import { promises } from "node:fs";
import { EventEmitter } from "node:events";
import path from "node:path";
import * as frida from "frida";
import WebSocket, { WebSocketServer } from "ws";

import { platform } from "./platform";
import { parse_cli_options, CliOptions } from "./cli";
import { create_logger, Logger } from "./logger";

const codex = require("./third-party/RemoteDebugCodex.js");
const messageProto = require("./third-party/WARemoteDebugProtobuf.js");

class DebugMessageEmitter extends EventEmitter {}

type StructOffsetConfig = {
    LaunchConfigOffsets: number[];
    RemoteDebugConfigOffsets: number[];
    SceneOffset: number;
    WebSocketURLStringOffset: number;
    RemoteDebugModeOffset: number;
}

type HookConfig = {
    Version: number;
    LoadStartHookOffset: string;
    CDPFilterHookOffset: string;
    CastToJsonHookOffset?: string;
    SceneOffsets?: number[];
    MiniAppConfigStructOffsets?: StructOffsetConfig;
    AppIdStringOffset?: number;
};

type MiniappLoadStartEvent = {
    type: "miniappLoadStart";
    appid: string | null;
    scene?: number;
};

type DebugClientState = {
    appid: string | null;
    messageCount: number;
    probed: boolean;
};

const HOOK_MATCH_TIMEOUT_MS = 60 * 1000;

const debugMessageEmitter = new DebugMessageEmitter();
const hookEvents = new EventEmitter();
let pendingHookAppId: { appid: string; at: number } | null = null;

const bufferToHexString = (buffer: ArrayBuffer) => {
    return Array.from(new Uint8Array(buffer))
        .map((byte) => byte.toString(16).padStart(2, "0"))
        .join("");
};

// surface console output of the injected hook script in the terminal
const logCdpConsoleEvent = (
    logger: Logger,
    payload: unknown,
    contextId?: string,
) => {
    if (typeof payload !== "string") {
        return;
    }
    if (
        !payload.includes("consoleAPICalled") &&
        !payload.includes("Log.entryAdded")
    ) {
        return;
    }
    const ctx = contextId ? `[ctx=${contextId}]` : "";
    try {
        const parsed = JSON.parse(payload);
        if (parsed.method === "Runtime.consoleAPICalled") {
            const args = (parsed.params?.args ?? []).map((arg: any) => {
                if (arg.value !== undefined) {
                    return typeof arg.value === "string"
                        ? arg.value
                        : JSON.stringify(arg.value);
                }
                return String(arg.description ?? arg.type ?? "");
            });
            // logger.info(`[miniapp console]${ctx} ${args.join(" ")}`);
        } else if (parsed.method === "Log.entryAdded") {
            const entry = parsed.params?.entry ?? {};
            // logger.info(`[miniapp log]${ctx} ${entry.text ?? ""}`);
        }
    } catch (_) {
        // not a JSON payload, ignore
    }
};

// one line per (jscontext, cdp event) to discover how contexts are exposed
const logCdpEventOnce = (
    seen: Set<string>,
    logger: Logger,
    payload: unknown,
    contextId?: string,
) => {
    if (typeof payload !== "string") {
        return;
    }
    try {
        const parsed = JSON.parse(payload);
        if (typeof parsed.method !== "string") {
            return;
        }
        const ctx = contextId ?? "";
        const key = `${ctx}:${parsed.method}`;
        if (seen.has(key)) {
            return;
        }
        seen.add(key);
        if (parsed.method === "Runtime.executionContextCreated") {
            const context = parsed.params?.context ?? {};
            logger.info(
                `[hook] cdp ${parsed.method} ctx=${ctx} id=${context.id} ` +
                    `name=${context.name} origin=${context.origin} ` +
                    `aux=${JSON.stringify(context.auxData)}`,
            );
        } else if (parsed.method.startsWith("Target.")) {
            logger.info(
                `[hook] cdp event ${parsed.method} ctx=${ctx} ` +
                    `params=${JSON.stringify(parsed.params).slice(0, 400)}`,
            );
        } else {
            // logger.info(`[hook] cdp event ${parsed.method} ctx=${ctx}`);
        }
    } catch (_) {
        // not a JSON payload, ignore
    }
};

// installed with Runtime.addBinding so the injected hook can push events
// back to this process without relying on console forwarding
const HOOK_BINDING_NAME = "__wmpfHookBridge";

const debugServer = (
    options: CliOptions,
    logger: Logger,
    hookScript: string | null,
): WebSocketServer => {
    const wss = new WebSocketServer({ port: options.debugPort });
    logger.info(
        `[server] debug server running on ws://localhost:${options.debugPort}`,
    );
    logger.info(`[server] debug server waiting for miniapp to connect...`);

    let messageCounter = 0;
    let miniappConnectionCounter = 0;
    const clientStates = new Map<WebSocket, DebugClientState>();
    const seenCdpEvents = new Set<string>();

    const sendChromeDevtoolsMessage = (
        client: WebSocket,
        message: string,
        jscontextId: string,
    ) => {
        if (client.readyState !== WebSocket.OPEN) {
            return;
        }
        // encode CDP and send to miniapp
        // wrapDebugMessageData(data, category, compressAlgo)
        const rawPayload = {
            jscontext_id: jscontextId,
            op_id: Math.round(100 * Math.random()),
            payload: message.toString(),
        };
        logger.main_debug(rawPayload);
        const wrappedData = codex.wrapDebugMessageData(
            rawPayload,
            "chromeDevtools",
            0,
        );
        const outData = {
            seq: ++messageCounter,
            category: "chromeDevtools",
            data: wrappedData.buffer,
            compressAlgo: 0,
            originalSize: wrappedData.originalSize,
        };
        const encodedData =
            messageProto.mmbizwxadevremote.WARemoteDebug_DebugMessage.encode(
                outData,
            ).finish();
        client.send(encodedData, { binary: true });
    };

    // --- hook injection through the CDP proxy ---------------------------
    // `Runtime.enable` re-announces every live JS context, so each context is
    // probed for the target appid and the hook is evaluated in the context
    // that actually carries `wx.request` (the AppService logic layer)
    const PROBE_RETRY_INTERVAL_MS = 300;
    const PROBE_MAX_ATTEMPTS = 30;
    let cdpRequestCounter = 0;
    let hookEvaluationCounter = 100000;

    type PendingEvaluation = {
        contextId: number;
        kind: "probe" | "inject";
        attempts: number;
    };

    const pendingEvaluations = new Map<number, PendingEvaluation>();
    const injectedContexts = new Set<number>();
    const reprobeCount = new Map<number, number>();
    const probeTimers = new Map<number, NodeJS.Timeout>();

    const clearProbeTimer = (contextId: number) => {
        const timer = probeTimers.get(contextId);
        if (timer) {
            clearTimeout(timer);
            probeTimers.delete(contextId);
        }
    };

    const clearAllProbeTimers = () => {
        for (const timer of probeTimers.values()) {
            clearTimeout(timer);
        }
        probeTimers.clear();
    };

    const buildProbeExpression = () =>
        "(function () {" +
        "try {" +
        'if (typeof wx === "undefined" || !wx) { return "no-wx"; }' +
        'if (typeof wx.request !== "function") { return "no-api"; }' +
        'var appid = "";' +
        "try {" +
        "if (wx.getAccountInfoSync) {" +
        "appid = wx.getAccountInfoSync().miniProgram.appId;" +
        "}" +
        "} catch (e) {}" +
        'if (!appid && typeof __wxConfig !== "undefined" && __wxConfig.accountInfo) {' +
        "appid = __wxConfig.accountInfo.appId;" +
        "}" +
        'return "ready:" + appid;' +
        '} catch (e) { return "probe-error:" + e; }' +
        "})()";

    // built by concatenation so the hook source can contain backticks and
    // `${` without breaking the generated expression
    const buildInjectionExpression = (appid: string, source: string) =>
        "(function () {" +
        'try { var appid = "";' +
        "try {" +
        'if (typeof wx !== "undefined" && wx.getAccountInfoSync) {' +
        "appid = wx.getAccountInfoSync().miniProgram.appId;" +
        "}" +
        "} catch (e) {}" +
        'if (!appid && typeof __wxConfig !== "undefined" && __wxConfig.accountInfo) {' +
        "appid = __wxConfig.accountInfo.appId;" +
        "}" +
        "if (appid !== " +
        JSON.stringify(appid) +
        ') { return "appid-mismatch:" + appid; }' +
        "var beforeRequest = null;" +
        "try { beforeRequest = wx.request || null; } catch (e) {}" +
        "var __hookEmit = function (payload) {" +
        "var text = typeof payload === 'string' ? payload : JSON.stringify(payload);" +
        "try {" +
        "if (typeof " +
        HOOK_BINDING_NAME +
        " === 'function') { " +
        HOOK_BINDING_NAME +
        "(text); }" +
        "} catch (e) {}" +
        "try { console.log(text); } catch (e) {}" +
        "};" +
        "try {" +
        source +
        '\n} catch (e) { return "hook-error:" + e; }' +
        "try {" +
        "var afterRequest = wx.request || null;" +
        "var patched = beforeRequest !== null && " +
        "(afterRequest !== beforeRequest || wx.__hooked === true || " +
        "(afterRequest && afterRequest.__hookWrapped === true));" +
        "var frozen = Object.isFrozen(wx);" +
        "var diag = \"\";" +
        "try {" +
        "var own = Object.getOwnPropertyDescriptor(wx, 'request');" +
        "diag += \":own=\" + (own ? (own.get ? 'accessor' : 'value') + ',w=' + own.writable + ',c=' + own.configurable : 'none');" +
        "} catch (e) { diag += ':own-err'; }" +
        "try {" +
        "var proto = Object.getPrototypeOf(wx);" +
        "var protoDesc = proto ? Object.getOwnPropertyDescriptor(proto, 'request') : null;" +
        "diag += \":proto=\" + (protoDesc ? 'has' : 'none');" +
        "} catch (e) { diag += ':proto-err'; }" +
        'diag += ":type=" + (typeof wx.request);' +
        'return "injected:" + appid + ":patched=" + patched + ":frozen=" + frozen + diag;' +
        '} catch (e) { return "injected:" + appid + ":verify-error:" + e; }' +
        '} catch (e) { return "probe-error:" + e; }' +
        "})()";

    const sendEvaluation = (
        contextId: number,
        kind: PendingEvaluation["kind"],
        expression: string,
        attempts: number,
    ) => {
        if (!hookCdpClient || hookCdpClient.readyState !== WebSocket.OPEN) {
            return;
        }
        const id = ++hookEvaluationCounter;
        pendingEvaluations.set(id, { contextId, kind, attempts });
        hookCdpClient.send(
            JSON.stringify({
                id,
                method: "Runtime.evaluate",
                params: { expression, contextId, returnByValue: true },
            }),
        );
    };

    const probeContext = (contextId: number, attempts: number) => {
        if (!options.hookAppId || !hookScript) {
            return;
        }
        if (injectedContexts.has(contextId)) {
            return;
        }
        clearProbeTimer(contextId);
        sendEvaluation(contextId, "probe", buildProbeExpression(), attempts);
    };

    const scheduleProbe = (contextId: number, attempts: number) => {
        if (injectedContexts.has(contextId) || attempts >= PROBE_MAX_ATTEMPTS) {
            return;
        }
        clearProbeTimer(contextId);
        probeTimers.set(
            contextId,
            setTimeout(() => {
                probeTimers.delete(contextId);
                probeContext(contextId, attempts);
            }, PROBE_RETRY_INTERVAL_MS),
        );
    };

    // the runtime may rebuild the API object right after the context appears,
    // so re-check the patch a few times during startup and re-apply it if the
    // hook was lost
    const REPROBE_DELAYS_MS = [1500, 5000, 12000];
    const scheduleReprobe = (contextId: number) => {
        const count = reprobeCount.get(contextId) ?? 0;
        if (count >= REPROBE_DELAYS_MS.length) {
            return;
        }
        reprobeCount.set(contextId, count + 1);
        const delay = REPROBE_DELAYS_MS[count];
        clearProbeTimer(contextId);
        logger.info(
            `[hook] re-checking context ${contextId} in ${delay}ms (pass ${count + 1})`,
        );
        probeTimers.set(
            contextId,
            setTimeout(() => {
                probeTimers.delete(contextId);
                injectedContexts.delete(contextId);
                probeContext(contextId, 1);
            }, delay),
        );
    };

    const injectIntoContext = (contextId: number) => {
        if (!options.hookAppId || !hookScript) {
            return;
        }
        clearProbeTimer(contextId);
        logger.info(`[hook] injecting hook into context ${contextId}`);
        sendEvaluation(
            contextId,
            "inject",
            buildInjectionExpression(options.hookAppId, hookScript),
            1,
        );
    };

    const handleProbeResult = (value: string, pending: PendingEvaluation) => {
        if (value === `ready:${options.hookAppId}`) {
            injectIntoContext(pending.contextId);
            return;
        }
        if (value === "no-wx" || value === "no-api" || value === "ready:") {
            scheduleProbe(pending.contextId, pending.attempts + 1);
            return;
        }
        if (value.startsWith("probe-error:")) {
            logger.info(
                `[hook] probe failed in context ${pending.contextId}: ${value}`,
            );
        }
    };

    const handleInjectionResult = (value: string, pending: PendingEvaluation) => {
        if (value.startsWith("injected:")) {
            injectedContexts.add(pending.contextId);
            logger.info(
                `[hook] hook injected into context ${pending.contextId} (${value})`,
            );
            if (!value.includes(":patched=true")) {
                logger.info(
                    "[hook] warning: wx.request was not replaced by the hook " +
                        "(the API object may be frozen or the hook source does not patch it)",
                );
            }
            scheduleReprobe(pending.contextId);
            return;
        }
        if (value.startsWith("appid-mismatch:")) {
            const appid = value.slice("appid-mismatch:".length);
            if (appid === "") {
                // the context exists but the miniapp has not exposed its
                // account info yet; probe again shortly
                scheduleProbe(pending.contextId, 1);
                return;
            }
            logger.info(
                `[hook] not injecting, context ${pending.contextId} belongs to ` +
                    `appid ${appid}`,
            );
            return;
        }
        logger.info(
            `[hook] injection result in context ${pending.contextId}: ${value}`,
        );
    };

    const handleEvaluationResult = (
        parsed: any,
        pending: PendingEvaluation,
    ) => {
        const details = parsed.result ?? {};
        if (details.exceptionDetails || parsed.error) {
            logger.info(
                `[hook] evaluation failed in context ${pending.contextId}: ` +
                    `${details.exceptionDetails?.text ?? parsed.error?.message ?? ""}`,
            );
            return;
        }
        const value = details.result?.value;
        if (typeof value !== "string") {
            logger.info(
                `[hook] unexpected result in context ${pending.contextId}: ` +
                    `${JSON.stringify(details.result ?? null)}`,
            );
            return;
        }
        if (pending.kind === "probe") {
            handleProbeResult(value, pending);
            return;
        }
        handleInjectionResult(value, pending);
    };

    const handleHookCdpMessage = (payload: string) => {
        let parsed: any = null;
        try {
            parsed = JSON.parse(payload);
        } catch (_) {
            return;
        }
        if (parsed.method === "Runtime.consoleAPICalled") {
            // console output produced by the evaluated hook only reaches this
            // session, so mirror it here as well
            const args = (parsed.params?.args ?? []).map((arg: any) => {
                if (arg.value !== undefined) {
                    return typeof arg.value === "string"
                        ? arg.value
                        : JSON.stringify(arg.value);
                }
                return String(arg.description ?? arg.type ?? "");
            });
            // logger.info(`[hook console] ${args.join(" ")}`);
            return;
        }
        if (parsed.method === "Runtime.bindingCalled") {
            const params = parsed.params ?? {};
            if (params.name === HOOK_BINDING_NAME) {
                logger.info(`[hook appservice] ${params.payload ?? ""}`);
            }
            return;
        }
        if (parsed.method === "Runtime.executionContextCreated") {
            const contextId = parsed.params?.context?.id;
            if (typeof contextId === "number") {
                probeContext(contextId, 1);
            }
            return;
        }
        if (parsed.method === "Runtime.executionContextDestroyed") {
            const contextId = parsed.params?.executionContextId;
            if (typeof contextId === "number") {
                clearProbeTimer(contextId);
                injectedContexts.delete(contextId);
                reprobeCount.delete(contextId);
            }
            return;
        }
        if (parsed.method === "Debugger.scriptParsed") {
            const params = parsed.params ?? {};
            const url = String(params.url ?? "");
            const contextId = params.executionContextId;
            if (
                typeof contextId === "number" &&
                /(^|\/)appservice\.app\.js$/.test(url)
            ) {
                // the service entry script is a strong hint, probe right away
                // instead of waiting for the next retry
                probeContext(contextId, 1);
            }
            return;
        }
        if (typeof parsed.id === "number") {
            const pending = pendingEvaluations.get(parsed.id);
            if (pending) {
                pendingEvaluations.delete(parsed.id);
                handleEvaluationResult(parsed, pending);
            }
        }
    };

    // the runtime closes the debug socket when no IDE is attached, so hook a
    // lightweight CDP client to the proxy as soon as the target miniapp shows
    // up; the same client probes and evaluates the hook in every JS context
    let hookCdpClient: WebSocket | null = null;
    const armHookCdpClient = () => {
        if (!hookCdpClient || hookCdpClient.readyState !== WebSocket.OPEN) {
            return;
        }
        // a new debug session (or a restarted miniapp) re-announces its
        // contexts; drop in-flight work and probe them again
        pendingEvaluations.clear();
        clearAllProbeTimers();
        injectedContexts.clear();
        reprobeCount.clear();
        hookCdpClient.send(
            JSON.stringify({ id: ++cdpRequestCounter, method: "Runtime.enable" }),
        );
        hookCdpClient.send(
            JSON.stringify({
                id: ++cdpRequestCounter,
                method: "Runtime.addBinding",
                params: { name: HOOK_BINDING_NAME },
            }),
        );
        hookCdpClient.send(
            JSON.stringify({ id: ++cdpRequestCounter, method: "Debugger.enable" }),
        );
    };

    const startHookCdpClient = () => {
        if (hookCdpClient) {
            armHookCdpClient();
            return;
        }
        const client = new WebSocket(`ws://127.0.0.1:${options.cdpPort}`);
        hookCdpClient = client;
        client.on("open", () => {
            logger.info("[hook] cdp probe client connected");
            armHookCdpClient();
        });
        client.on("message", (data: Buffer) => {
            handleHookCdpMessage(data.toString());
        });
        client.on("error", (e) => {
            logger.error(`[hook] cdp probe client error: ${e}`);
        });
        client.on("close", () => {
            hookCdpClient = null;
        });
    };

    const maybeProbe = (client: WebSocket) => {
        const state = clientStates.get(client);
        if (!state || state.probed) {
            return;
        }
        state.probed = true;
        startHookCdpClient();
    };

    const onMessage = (ws: WebSocket, message: ArrayBuffer) => {
        const clientState = clientStates.get(ws);
        if (clientState) {
            clientState.messageCount += 1;
        }
        logger.main_debug(
            `[miniapp] client received raw message (hex): ${bufferToHexString(message)}`,
        );
        let unwrappedData: any = null;
        try {
            const decodedData =
                messageProto.mmbizwxadevremote.WARemoteDebug_DebugMessage.decode(
                    message,
                );
            unwrappedData = codex.unwrapDebugMessageData(decodedData);
            logger.main_debug(`[miniapp] [DEBUG] decoded data:`);
            logger.main_debug(unwrappedData);
        } catch (e) {
            // logger.error(`[miniapp] miniapp client err: ${e}`);
        }

        if (unwrappedData === null) {
            return;
        }

        if (clientState && clientState.messageCount === 1) {
            logger.info(
                `[hook] miniapp first message category=${unwrappedData.category} ` +
                    `data=${JSON.stringify(unwrappedData.data).slice(0, 200)}`,
            );
        }

        const state = clientStates.get(ws);
        const isTargetClient =
            state !== undefined &&
            options.hookAppId !== undefined &&
            state.appid === options.hookAppId;
        if (isTargetClient) {
            // the client talks as soon as it is ready, probe then
            maybeProbe(ws);
        }

        if (
            unwrappedData.category === "chromeDevtoolsResult" ||
            unwrappedData.category === "chromeDevtools"
        ) {
            const payload = unwrappedData.data.payload;
            const jscontextId = unwrappedData.data.jscontext_id;
            if (isTargetClient) {
                logCdpConsoleEvent(logger, payload, jscontextId);
                logCdpEventOnce(seenCdpEvents, logger, payload, jscontextId);
            }
            if (unwrappedData.category === "chromeDevtoolsResult") {
                // need to proxy to CDP client
                debugMessageEmitter.emit("cdpmessage", payload);
            }
            return;
        }

        if (!state) {
            return;
        }

        if (unwrappedData.category === "addJsContext") {
            // the miniapp connects right after OnLoadStart; fall back to the
            // pending appid in case the connection was established before the
            // frida event reached us
            if (
                state.appid === null &&
                pendingHookAppId &&
                Date.now() - pendingHookAppId.at <= HOOK_MATCH_TIMEOUT_MS
            ) {
                state.appid = pendingHookAppId.appid;
                logger.info(
                    `[hook] miniapp client matched appid ${state.appid}`,
                );
                maybeProbe(ws);
            }
            const contextId = String(unwrappedData.data.jscontext_id ?? "");
            const contextName = String(unwrappedData.data.jscontext_name ?? "");
            if (options.hookAppId) {
                logger.info(
                    `[hook] js context added: id=${contextId} name=${contextName}`,
                );
            } else {
                logger.main_debug(
                    `[miniapp] js context added: id=${contextId} name=${contextName}`,
                );
            }
        }
    };

    wss.on("connection", (ws: WebSocket, request: any) => {
        const clientId = ++miniappConnectionCounter;
        // logger.info(
        //     `[miniapp] miniapp client #${clientId} connected url=${JSON.stringify(request?.url ?? "")} ` +
        //         `headers=${JSON.stringify(request?.headers ?? {})}`,
        // );
        const state: DebugClientState = {
            appid: null,
            messageCount: 0,
            probed: false,
        };
        clientStates.set(ws, state);
        if (
            options.hookAppId &&
            pendingHookAppId &&
            pendingHookAppId.appid === options.hookAppId &&
            Date.now() - pendingHookAppId.at <= HOOK_MATCH_TIMEOUT_MS
        ) {
            state.appid = pendingHookAppId.appid;
            logger.info(
                `[hook] miniapp client matched appid ${state.appid}`,
            );
        }
        ws.on("message", (message: ArrayBuffer) => onMessage(ws, message));
        ws.on("error", (err) => {
            logger.error("[miniapp] miniapp client err:", err);
        });
        ws.on("close", (code: number, reason: Buffer) => {
            clientStates.delete(ws);
            logger.info(
                `[miniapp] miniapp client #${clientId} disconnected code=${code} ` +
                    `reason=${JSON.stringify(reason?.toString() ?? "")} ` +
                    `messages=${state.messageCount}`,
            );
        });
    });

    // Harness state across the OnLoadStart hook and the debug connection.
    hookEvents.on("loadStart", (event: MiniappLoadStartEvent) => {
        if (!options.hookAppId) {
            return;
        }
        if (!event.appid) {
            logger.info(
                `[hook] OnLoadStart without appid (scene: ${event.scene}), ignored`,
            );
            return;
        }
        logger.info(
            `[hook] OnLoadStart: appid=${event.appid}, scene=${event.scene}`,
        );
        if (event.appid !== options.hookAppId) {
            logger.info(
                `[hook] appid mismatch: got ${event.appid}, target ${options.hookAppId}`,
            );
            return;
        }

        pendingHookAppId = { appid: event.appid, at: Date.now() };
    });

    debugMessageEmitter.on(
        "proxymessage",
        (data: { message: string; jscontext_id?: string }) => {
            wss.clients.forEach((client) => {
                sendChromeDevtoolsMessage(
                    client,
                    data.message,
                    data.jscontext_id ?? "",
                );
            });
        },
    );
    return wss;
};

const proxyServer = (options: CliOptions, logger: Logger): WebSocketServer => {
    const wss = new WebSocketServer({ port: options.cdpPort });
    logger.info(
        `[server] proxy server running on ws://localhost:${options.cdpPort}`,
    );
    logger.info(
        `[server] link: devtools://devtools/bundled/inspector.html?ws=127.0.0.1:${options.cdpPort}`,
    );

    const onMessage = (message: string) => {
        debugMessageEmitter.emit("proxymessage", { message });
    };

    wss.on("connection", (ws: WebSocket) => {
        logger.info("[cdp] CDP client connected");
        ws.on("message", onMessage);
        ws.on("error", (err) => {
            logger.error("[cdp] CDP client err:", err);
        });
        ws.on("close", () => {
            logger.info("[cdp] CDP client disconnected");
        });
    });

    debugMessageEmitter.on("cdpmessage", (message: string) => {
        wss &&
            wss.clients.forEach((client) => {
                if (client.readyState === WebSocket.OPEN) {
                    // send CDP message to devtools
                    client.send(message);
                }
            });
    });
    return wss;
};

const autoDetectConfig = async (
    session: frida.Session,
    projectRoot: string,
    wmpfVersion: number,
): Promise<HookConfig> => {
    let detectorContent: string;
    try {
        detectorContent = (
            await promises.readFile(
                path.join(
                    projectRoot,
                    "frida/autodetect",
                    `${process.platform}.js`,
                ),
            )
        ).toString();
    } catch (e) {
        throw new Error("[frida] auto-detect script not found");
    }

    const detector = await session.createScript(detectorContent);
    const detectedConfig = new Promise<Omit<HookConfig, "Version">>(
        (resolve, reject) => {
            detector.message.connect((message: frida.Message) => {
                if (message.type === "error") {
                    reject(
                        new Error(
                            `[frida] auto-detect failed: ${message.description}`,
                        ),
                    );
                    return;
                }

                const payload = message.payload as {
                    type?: string;
                    config?: Omit<HookConfig, "Version">;
                    error?: string;
                };
                if (payload.type === "wmpf-offsets" && payload.config) {
                    resolve(payload.config);
                } else if (payload.type === "wmpf-offsets-error") {
                    reject(
                        new Error(
                            `[frida] auto-detect failed: ${payload.error ?? "unknown error"}`,
                        ),
                    );
                }
            });
        },
    );

    try {
        await detector.load();
        return { Version: wmpfVersion, ...(await detectedConfig) };
    } finally {
        await detector.unload();
    }
};

const fridaServer = async (
    options: CliOptions,
    logger: Logger,
): Promise<frida.Session> => {
    const localDevice = await frida.getLocalDevice();
    const { pid: wmpfPid, version: wmpfVersion } = await platform.findWmpfProcess()

    // attach to process
    const session = await localDevice.attach(wmpfPid);

    // find hook script
    const projectRoot = path.join(
        path.dirname(
            (require.main && require.main.filename) ||
                (process.mainModule && process.mainModule.filename) ||
                process.cwd(),
        ),
        "..",
    );
    let scriptContent: string | null = null;
    try {
        scriptContent = (
            await promises.readFile(path.join(projectRoot, "frida/hook.js"))
        ).toString();
    } catch (e) {
        throw new Error("[frida] hook script not found");
    }

    let configContent: string | null = null;
    if (options.autoDetect) {
        logger.info(`[frida] auto-detecting hook offsets...`);
        const config = await autoDetectConfig(session, projectRoot, wmpfVersion);
        configContent = JSON.stringify(config);
        logger.info(`[frida] detected hook offsets: ${configContent}`);
    } else {
        try {
            configContent = (
                await promises.readFile(
                    path.join(
                        projectRoot,
                        `frida/config/${process.platform}`,
                        `addresses.${wmpfVersion}.json`,
                    ),
                )
            ).toString();
            configContent = JSON.stringify(JSON.parse(configContent));
        } catch (e) {
            throw new Error(`[frida] version config not found: ${wmpfVersion}`);
        }
    }

    if (scriptContent === null || configContent === null) {
        throw new Error("[frida] unable to find hook script");
    }
    const fridaSource = scriptContent;

    const configObject = JSON.parse(configContent) as Record<string, unknown>;

    // frida/hook.js keeps the config inside a template literal, so the JSON
    // has to be escaped for that context: every `\n` produced by stringify
    // would otherwise turn into a real newline and break JSON.parse
    const buildScript = (config: Record<string, unknown>) => {
        const escapedConfig = JSON.stringify(config)
            .replace(/\\/g, "\\\\")
            .replace(/`/g, "\\`")
            .replace(/\$\{/g, "\\${");
        // use a replacer function so `$` in the config is literal
        return fridaSource.replace("@@CONFIG@@", () => escapedConfig);
    };

    const bindMessages = (script: frida.Script) => {
        script.message.connect((message: frida.Message) => {
            if (message.type === "error") {
                logger.error("[frida client]", message);
                return;
            }

            const payload = message.payload as any;
            if (payload && payload.type === "miniappLoadStart") {
                hookEvents.emit("loadStart", payload as MiniappLoadStartEvent);
                return;
            }

            logger.frida_debug("[frida client]", message.payload);
        });
    };

    const script = await session.createScript(buildScript(configObject));
    bindMessages(script);
    await script.load();
    logger.info(
        `[frida] script loaded, WMPF version: ${wmpfVersion}, pid: ${wmpfPid}`,
    );
    logger.info(`[frida] you can now open any miniapps`);
    return session;
};

const main = async () => {
    const options = parse_cli_options();
    const logger = create_logger(options);

    let hookScript: string | null = null;
    if (options.hookScript) {
        try {
            hookScript = await promises.readFile(
                path.resolve(options.hookScript),
                "utf8",
            );
        } catch (e) {
            throw new Error(`[main] unable to read hook script: ${e}`);
        }
        if (hookScript.trim().length === 0) {
            throw new Error("[main] hook script is empty");
        }
        logger.info(
            `[hook] will inject ${options.hookScript} into appid ${options.hookAppId}`,
        );
    }

    const debugWss = debugServer(options, logger, hookScript);
    const proxyWss = proxyServer(options, logger);
    const fridaSession = await fridaServer(options, logger);

    process.on("SIGINT", async () => {
        logger.info("[server] shutting down...");
        debugWss.close();
        proxyWss.close();
        await fridaSession.detach();
        process.exit(0);
    });
};

(async () => {
    await main();
})();
