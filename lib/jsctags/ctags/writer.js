/* ***** BEGIN LICENSE BLOCK *****
 * Version: MPL 1.1/GPL 2.0/LGPL 2.1
 *
 * The contents of this file are subject to the Mozilla Public License Version
 * 1.1 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 * http://www.mozilla.org/MPL/
 *
 * Software distributed under the License is distributed on an "AS IS" basis,
 * WITHOUT WARRANTY OF ANY KIND, either express or implied. See the License
 * for the specific language governing rights and limitations under the
 * License.
 *
 * The Original Code is Bespin.
 *
 * The Initial Developer of the Original Code is
 * Mozilla.
 * Portions created by the Initial Developer are Copyright (C) 2009
 * the Initial Developer. All Rights Reserved.
 *
 * Contributor(s):
 *   Bespin Team (bespin@mozilla.com)
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

var Trait = require('../traits').Trait;
var _ = require('../underscore')._;

const ESCAPES = { "\\": "\\\\", "\n": "\\n", "\r": "\\r", "\t": "\\t" };

var METATAGS = [
    { name: '!_TAG_FILE_FORMAT', tagfile: 2, addr: "/extended format/" },
    {
        name:       '!_TAG_FILE_SORTED',
        tagfile:    0,
        addr:       "/0=unsorted, 1=sorted, 2=foldcase/"
    },
    {
        name:       '!_TAG_PROGRAM_AUTHOR',
        tagfile:    "Patrick Walton",
        addr:       "/pwalton@mozilla.com/"
    },
    { name: '!_TAG_PROGRAM_NAME', tagfile: "jsctags" },
    {
        name:       '!_TAG_PROGRAM_URL',
        tagfile:    "http://github.com/pcwalton/jsctags",
        addr:       "/GitHub repository/"
    },
    { name: '!_TAG_PROGRAM_VERSION', tagfile: "0.1" }
];

const SPECIAL_FIELDS = { addr: true, kind: true, name: true, tagfile: true };

exports.TagWriter = Trait({
    tags: Trait.required,

    init: function() { },

    write: function(stream, opts) {
        if (!opts.hasOwnProperty('sort') || opts.sort === 'no') {
            var sortfunc = function(a, b) { return parseInt(a.sortno, 10) - parseInt(b.sortno, 10); };
        } else if (opts.sort === 'yes') {
            var sortfunc = function(a, b) {
                if (a.name === b.name) return 0;
                else if (a.name < b.name) return -1;
                else return 1;
            };
            for (var i in METATAGS) {
                if (METATAGS[i].name == '!_TAG_FILE_SORTED') {
                    METATAGS[i].tagfile = 1;
                    break;
                }
            }
        } else {
            throw new Error("Invalid value for --sort flag.");
        }
        this.tags = this.tags.sort(sortfunc);
        this.tags = METATAGS.concat(this.tags);

        var lines = this.tags.map(function(tag) {
            delete tag.sortno;
            var buf = [ tag.name, "\t", tag.tagfile, "\t" ];

            var addr = tag.addr;
            buf.push(addr !== undefined ? addr : "//");

            var tagfields = [];
            for (var key in tag) {
                if (!(key in SPECIAL_FIELDS)) {
                    tagfields.push(key);
                }
            }
            tagfields.sort();

            var kind = tag.kind;
            if (kind === undefined && tagfields.length === 0) {
                buf.push("\n");
                return buf.join("");
            }

            buf.push(";\"");

            if (kind !== undefined) {
                buf.push("\t", kind);
            }

            tagfields.forEach(function(tagfield) {
                buf.push("\t", tagfield, ":");

                var escape = function(str) { return ESCAPES[str]; };
                buf.push(tag[tagfield].replace("[\\\n\r\t]", escape));
            });

            buf.push("\n");
            return buf.join("");
        });

        lines.forEach(function(line) { stream.write(line); });
    },

    writeJSONP: function(stream, func) {
        this.tags.map(function(tag) { delete tag.sortno; });
        var json = JSON.stringify(this.tags);
        _([ func, "(", json, ");" ]).each(function(str) {
            stream.write(str);
        });
    },
});

