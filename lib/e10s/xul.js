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

var sax = require("sax");
var fs = require("fs");
var async = require("async");
var jsconf = require("./json-config");

var config = jsconf.readFileSync("xul.jsconf");

function extractScripts(path, cb) {
    var stream = fs.createReadStream(path);
    var saxStream = sax.createStream(false, { lowercasetags: true, noscript: true });

    var context = null;

    var scripts = [];

    saxStream.on("opentag", function(tag) {
        var name = tag.name;
        var attributes = tag.attributes;

        if (name === "script") {
            context = { tag: "script", type: attributes.type, previous: context, line: saxStream._parser.line + 1 };
            if (attributes.src)
                scripts.push({ type: attributes.type, href: attributes.src });
        } else if (config.inlineEventHandlers.hasOwnProperty(name)) { // FIXME: just include any events?
            var eventTypes = config.inlineEventHandlers[name];
            for (var i = 0, n = eventTypes.length; i < n; i++) {
                var eventType = eventTypes[i];
                if (eventType in attributes) {
                    scripts.push({
                        tag: name,
                        eventType: eventType.replace(/^on/, ""),
                        contents: attributes[eventType],
                        file: path,
                        line: saxStream._parser.line + 1
                    });
                }
            }
        }
    });

    saxStream.on("closetag", function(tag) {
        if (tag === "script")
            context = context.previous;
    });

    function onText(text) {
        if (context && context.tag === "script")
            scripts.push({ type: context.type, contents: text, file: path, line: context.line });
    }

    saxStream.on("text", onText);

    var cdata;

    saxStream.on("opencdata", function() {
        cdata = "";
    });

    saxStream.on("cdata", function(text) {
        cdata += text;
    });

    saxStream.on("closecdata", function() {
        onText(cdata);
    });

    saxStream.on("error", function(err) {
        cb(err, null);
    });

    saxStream.on("end", function() {
        cb(null, scripts);
    });

    stream.pipe(saxStream);
}

exports.extractScripts = extractScripts;
