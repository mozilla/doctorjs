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

const CHILDREN_KEYS =
  ['funDecls', 'setup', 'varDecl', 'object', 'condition', 'iterator',
   'discriminant', 'cases', 'update', 'tryBlock', 'body', 'expression',
   'statement', 'value', 'thenPart', 'elsePart', 'catchClauses', 'finallyBlock'
   ];

var myast;

function parse() {
    tiki.ensurePackage('::narcissus', function() {
        var require = tiki.require;
        var parse = require('narcissus').parse;
        var jsdefs = require('narcissus:jsdefs');
        var tokenIds = jsdefs.tokenIds;

        var astToJSON = function(ast) {
            var desc;
            if (ast.type in jsdefs.tokens) {
                desc = jsdefs.tokens[ast.type];
            } else {
                desc = "?";
            }

            if ('lineno' in ast) {
                desc += " @ " + ast.lineno;
            }
            var nameField;
            switch (ast.type) {
            case tokenIds.IDENTIFIER:
            case tokenIds.NUMBER:
            case tokenIds.STRING:
            case tokenIds.REGEXP:
                nameField = 'value';
                break;
            case tokenIds.BREAK:
            case tokenIds.CONTINUE:
            default:
                nameField = 'name';
            }
            if (nameField in ast) {
                desc += " " + ast[nameField];
            }
            var json = { data: desc };

            var children = [];
            for (var i=0, len=ast.length; i<len; i++) children.push(ast[i]);
            CHILDREN_KEYS.forEach(function(childKey) {
                if (!(childKey in ast)) {
                    return;
                }

                var value = ast[childKey];
                if (typeof(value) !== 'object' || value === null) {
                    return;
                }

                if ('tokenizer' in value) {
                    children.push(value);
                } else if (value[0] !== undefined) {
                    children.push.apply(children, value);
                }
            });

            if (children.length > 0) {
                json.children = children.map(astToJSON);
            }

            return json;
        };

        var ast = parse($('#js').val(), 'js', 1);

        $('#tree').tree({
            data: {
                type:   'json',
                opts:   { static: astToJSON(ast) }
            }
        });
    });
}

