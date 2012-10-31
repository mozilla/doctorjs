// quick-n-dirty parser of Dimitris's original type format
function parseType(src) {
    function match(str) {
        var n = str.length;
        if (src.length && src.substring(0, n) === str) {
            src = src.substring(n).trim();
            return true;
        }
        return false;
    }

    function mustMatch(str, msg) {
        if (!match(str))
            throw new Error(msg + " (" + src + ")");
    }

    function Type() {
        var root;
        if (match("any")) {
            root = "any";
        } else if (match("string")) {
            root = "string";
        } else if (match("number")) {
            root = "number";
        } else if (match("Array")) {
            if (match("[")) {
                root = { kind: "array", elementType: Type() };
                mustMatch("]", "invalid array type");
            } else {
                root = { kind: "array", elementType: "any" };
            }
        } else if (src.length && src[0] === "<") {
            root = UnionType();
        } else {
            var re = /^([a-zA-Z_$][a-zA-Z_$0-9]*)/;
            var result = re.exec(src);
            if (!result)
                throw new Error("unrecognized type: " + src);
            root = result[0];
            src = src.substring(root.length).trim();
        }

        while (match("function")) {
            mustMatch("(", "invalid function type");
            var args = [];
            if (!match(")")) {
                do {
                    args.push(Type());
                } while (match(","));
                mustMatch(")", "invalid function type");
            }
            root = { kind: "function", returnType: root, argTypes: args };
        }

        return root;
    }

    function UnionType() {
        mustMatch("<", "invalid union type");
        var variants = [];
        if (!match(">")) {
            do {
                variants.push(Type());
            } while (match("|"));
            mustMatch(">", "invalid union type");
        }
        return { kind: "union", variants: variants };
    }

    return Type();
}

// formatType : JSON type -> HTML source
// render the JSON type as pretty HTML
function formatType(type) {
    if (typeof type === "string")
        return type;

    if (type.kind === "function") {
        return "function (" +
               type.argTypes.map(formatType).join(", ") +
               ") &rarr; " +
               formatType(type.returnType);
    } else if (type.kind === "array") {
        return "Array[" + formatType(type.elementType) + "]";
    } else if (type.kind === "union") {
        return "&lt;" + type.variants.map(formatType).join(" | ") + "&gt;";
    }

    throw new Error("unrecognized type");
}
