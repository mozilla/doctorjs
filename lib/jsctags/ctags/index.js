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

var parse = require('../../../narcissus/lib/parser').parse;
var _ = require('underscore')._;
var Interpreter = require('./interp').Interpreter;
var TagReader = require('./reader').TagReader;
var TagWriter = require('./writer').TagWriter;
var Trait = require('../traits').Trait;

exports.Tags = function(initialTags) {
    this.tags = initialTags != null ? initialTags : [];
    this.init();
};

exports.Tags.prototype = Object.create(Object.prototype, Trait.compose(Trait({
    _search: function(id, pred) {
        var shadowTag = { name: id };
        var tags = this.tags;
        var index = _(tags).sortedIndex(shadowTag, function(tag) {
            return tag.name;
        });

        var start = index, end = index;
        while (start >= 0 && start < tags.length && pred(tags[start])) {
            start--;
        }
        while (end >= 0 && end < tags.length && pred(tags[end])) {
            end++;
        }

        return tags.slice(start + 1, end);
    },

    add: function(newTags) {
        var tags = this.tags;
        Array.prototype.push.apply(tags, newTags);

        tags.sort(function(a, b) {
            var nameA = a.name, nameB = b.name;
            if (nameA < nameB) {
                return -1;
            }
            if (nameA === nameB) {
                return 0;
            }
            return 1;
        });
    },

    /** Returns all the tags that match the given identifier. */
    get: function(id) {
        return this._search(id, function(tag) { return tag.name === id; });
    },

    /**
     * Adds the tags from the supplied JavaScript file to the internal store of
     * tags.
     */
    //dimvar: string (file contents), path to file, options
    scan: function(src, file, opts) {
        if (opts === null || opts === undefined) {
            opts = {};
        }

        var lines = src.split("\n");
        var ast = parse(src, file, 1);

        var interp = new Interpreter(ast, file, lines, opts);
        interp.interpret();
        this.add(interp.tags);
    },

    /** Returns all the tags that begin with the given prefix. */
    stem: function(prefix) {
        var len = prefix.length;
        return this._search(prefix, function(tag) {
            return tag.name.substring(0, len) === prefix;
        });
    }
}), TagReader, TagWriter));

