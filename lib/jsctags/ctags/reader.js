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

var _ = require('../underscore')._;
var Trait = require('../traits').Trait;

exports.TagReader = Trait({
    readLines: function(lines) {
        var tags = [];

        _(lines).each(function(line) {
            var parts = line.split("\t");
            if (parts.length < 3) {
                return;
            }

            var name = parts[0];
            if (/^!_TAG_/.test(name)) {
                return;
            }

            // TODO: cope with tab characters in the addr
            var tag = { name: name, tagfile: parts[1], addr: parts[2] };

            var fieldIndex;
            if (parts.length > 3 && parts[3].indexOf(":") === -1) {
                tag.kind = parts[3];
                fieldIndex = 4;
            } else {
                fieldIndex = 3;
            }

            var fields = {};
            _(parts.slice(fieldIndex)).each(function(field) {
                var match = /^([^:]+):(.*)/.exec(field);
                fields[match[1]] = match[2];
            });
            tag.fields = fields;

            tags.push(tag);
        });

        this.add(tags);
    },

    readString: function(str) {
        this.readLines(str.split("\n"));
    }
});

