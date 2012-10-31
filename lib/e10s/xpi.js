/* ***** BEGIN LICENSE BLOCK *****
 * Version: MPL 1.1/GPL 2.0/LGPL 2.1
 *
 * The contents of this file are subject to the Mozilla Public License Version
 * 1.1 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 * http://www.mozilla.org/MPL/
 *
 * Software distributed under the License is distributed on an 'AS IS' basis,
 * WITHOUT WARRANTY OF ANY KIND, either express or implied. See the License
 * for the specific language governing rights and limitations under the
 * License.
 *
 * The Original Code is DoctorJS.
 *
 * The Initial Developer of the Original Code is
 * Dave Herman <dherman@mozilla.com>
 * Portions created by the Initial Developer are Copyright (C) 2010
 * the Initial Developer. All Rights Reserved.
 *
 * Contributor(s):
 *   Dave Herman <dherman@mozilla.com>
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either the GNU General Public License Version 2 or later (the "GPL"), or
 * the GNU Lesser General Public License Version 2.1 or later (the "LGPL"),
 * in which case the provisions of the GPL or the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of either the GPL or the LGPL, and not to allow others to
 * use your version of this file under the terms of the MPL, indicate your
 * decision by deleting the provisions above and replace them with the notice
 * and other provisions required by the GPL or the LGPL. If you do not delete
 * the provisions above, a recipient may use your version of this file under
 * the terms of any one of the MPL, the GPL or the LGPL.
 *
 * ***** END LICENSE BLOCK ***** */

// https://developer.mozilla.org/en/chrome_registration
// http://mxr.mozilla.org/mozilla2.0/source/xpcom/components/ManifestParser.cpp

var path = require("path");
var fs = require("fs");
var Memo = require("./memo").Memo;

function XPI(root, warn) {
    this.root = path.normalize(root);
    this.manifests = new Memo();
    this.warn = warn || function() {};
    this.content = Object.create(null, {});
}

XPI.prototype = {
    readManifest: function readManifest(localPath) {
        var self = this;
        return this.manifests.memoSync(localPath, function() {
            var src = fs.readFileSync(path.join(self.root, localPath), "utf8");
            var instrs = parseInstrs(self, localPath, src.split(/\n/));
            registerContent(self, localPath, instrs);
            // FIXME: handle sub-manifests
            return new Manifest(self, localPath, src, instrs);
        });
    },
    readChromeManifest: function readChromeManifest() {
        return this.readManifest("chrome.manifest");
    },
    lookupURI: function lookupURI(uri, referer) {
        return uri.match(/^chrome:\/\//)
             ? this.lookupChromeURI(uri)
             : this.lookupRelativeURI(uri, referer);
    },
    lookupChromeURI: function lookupChromeURI(uri) {
        var match = uri.match(/^chrome:\/\/([^\/]+)\/([^\/]+)\/(.*)$/);
        if (!match)
            throw new Error("invalid chrome URI: " + uri);

        switch (match[2]) {
          case "content":
            return this.lookupContentURI(match[1], match[3], uri);

          // FIXME: implement others
          default:
            throw new Error("unhandled chrome URI type: " + uri);
        }
    },
    lookupContentURI: function lookupContentURI(alias, relativePath, uri) {
        var local = this.content[alias];
        if (!local)
            throw new Error("unrecognized content alias: " + uri);
        return path.join(local, relativePath);
    },
    lookupRelativeURI: function lookupRelativeURI(relativePath, referer) {
        return path.join(path.dirname(referer), relativePath);
    }
};

function Manifest(xpi, local, src, instrs) {
    this.xpi = xpi;
    this.localPath = local;
    this.src = src;
    this.instrs = instrs;
}

Manifest.prototype = {
    lookupRelativeURI: function lookupRelativeURI(relativePath) {
        return this.xpi.lookupRelativeURI(relativePath, this.localPath);
    }
};

function manifestParser(name, tokens, i) {
    return { manifest: tokens[0] };
}

function overlayParser(name, tokens, i) {
    return { target: tokens[0], overlay: tokens[1] };
}

function contentParser(name, tokens, i) {
    return { package: tokens[0], uri: tokens[1] };
}

var instrParsers = {
    "manifest": manifestParser,
    "content":  contentParser,
    "overlay":  overlayParser
};

// FIXME: not yet implemented:
//   - binary-component
//   - interfaces
//   - component
//   - contract
//   - category
//   - locale
//   - skin
//   - style
//   - override
//   - resource

function parseInstrs(xpi, local, lines) {
    var instrs = Object.create(null, {});

    function add(name, instr) {
        var a = instrs[name] || (instrs[name] = []);
        a.push(instr);
    }

    for (var i = 0, n = lines.length; i < n; i++) {
        var line = lines[i].trim();
        if (line === '' || line[0] === '#')
            continue;

        var tokens = line.split(/[ \t]+/);
        var name = tokens.shift();
        if (!instrParsers.hasOwnProperty(name)) {
            xpi.warn(local + ":" + (i+1) + ": unhandled instruction: " + name);
            continue;
        }

        var parser = instrParsers[name];
        var flags = popFlags(tokens, i);
        var instr = parser(name, tokens, i);
        if (instr) {
            instr.flags = flags;
            add(name, instr);
        }
    }

    return instrs;
}

var flagParsers = {
    "application":       equalityParser,
    "appversion":        inequalityParser,
    "contentaccessible": equalityParser,
    "os":                equalityParser,
    "osversion":         inequalityParser,
    "abi":               equalityParser
};

function equalityParser(token) {
    var i = token.indexOf("=");
    return {
        flag: token.substring(0, i).trim(),
        value: token.substring(i + 1).trim()
    };
}

function inequalityParser(token) {
    var keys = ["<=", ">=", "<", ">", "="];
    for (var i = 0, n = keys.length; i < n; i++) {
        var relation = keys[i];
        var idx = token.indexOf(relation);
        if (idx >= 0) {
            return {
                flag: token.substring(0, idx).trim(),
                relation: relation,
                value: token.substring(idx + relation.length).trim()
            };
        }
    }
}

// array[string] nat -> array[object]
function popFlags(tokens, i) {
    var flags = [];

    // keep popping until a token doesn't parse as a flag
  parseNext:
    for (var j = tokens.length - 1; j >= 0; j--) {
        var token = tokens[j];

        // find a parser for this flag
        for (var flag in flagParsers) {
            if (token.substring(0, flag.length) === flag) {
                var parsed = flagParsers[flag](token);
                if (parsed) {
                    flags.unshift(parsed);
                    continue parseNext;
                }
            }
        }

        // we couldn't find a parser, so bail
        break;
    }

    return flags.length > 0 ? flags : null;
}

function registerContent(xpi, local, instrs) {
    var a = instrs.content || [];
    for (var i = 0, n = a.length; i < n; i++) {
        var pkg = a[i]["package"];
        var uri = a[i].uri;
        if (uri.match(/^jar:/))
            uri = uri.replace(/^jar:/, "").replace(/!/g, "");
        xpi.content[pkg] = uri;
    }
}

exports.XPI = XPI;

// var xpi = new XPI(process.argv[2]);
// xpi.readChromeManifest();
// console.log(xpi.lookupURI("chrome://dta/content/dta/manager.xul"));
