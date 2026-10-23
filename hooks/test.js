(function () {
    console.log("[user script] start");
    // __hookEmit is provided by the injector: it pushes the message back to
    // the debugger process through a CDP binding (and console.log as fallback)
    var emit =
        typeof __hookEmit === "function"
            ? __hookEmit
            : function (text) {
                  try {
                      console.log(text);
                  } catch (e) {}
              };

    var target = wx;
    if (!target) {
        emit("[hook] skip: wx is missing");
        return;
    }
    if (target.__hooked) {
        return;
    }
    var raw = target.request;
    if (typeof raw !== "function") {
        emit("[hook] skip: wx.request is " + typeof raw);
        return;
    }
    if (raw.__hookWrapped) {
        return;
    }

    var wrapped = function (opts) {
        emit("[hook] request " + (opts && opts.url));
        return raw.apply(this, arguments);
    };
    wrapped.__hookWrapped = true;

    // the runtime freezes the wx object, so try the plain assignment first
    // and fall back to defineProperty on the instance and its prototypes
    try {
        target.request = wrapped;
    } catch (e) {}
    if (target.request !== wrapped) {
        try {
            Object.defineProperty(target, "request", {
                value: wrapped,
                configurable: true,
                writable: true,
                enumerable: true,
            });
        } catch (e) {}
    }
    if (target.request !== wrapped) {
        var proto = Object.getPrototypeOf(target);
        for (var i = 0; i < 3 && proto; i++) {
            try {
                Object.defineProperty(proto, "request", {
                    value: wrapped,
                    configurable: true,
                    writable: true,
                    enumerable: true,
                });
            } catch (e) {}
            if (target.request === wrapped) {
                break;
            }
            proto = Object.getPrototypeOf(proto);
        }
    }

    try {
        Object.defineProperty(target, "__hooked", {
            value: true,
            configurable: true,
        });
    } catch (e) {
        try {
            target.__hooked = true;
        } catch (e2) {}
    }

    emit(
        "[hook] installed " +
            (target.request === wrapped) +
            " frozen: " +
            Object.isFrozen(target),
    );
    console.log("[user script] end");
})();
"hooked";
