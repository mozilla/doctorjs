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

var graphNodeTypes = {
    graphExpression: 3,
    graphIndexExpression: 2
};

var xmlNodeTypes = {
    xmlAnyName: 1,
    xmlAttributeSelector: 2,
    xmlFilterExpression: 3,
    xmlQualifiedIdentifier: 4,
    xmlFunctionQualifiedIdentifier: 3,
    xmlElement: 2,
    xmlList: 2,
    xmlEscape: 2,
    xmlText: 2,
    xmlStartTag: 2,
    xmlEndTag: 2,
    xmlPointTag: 2,
    xmlName: 2,
    xmlAttribute: 2,
    xmlCdata: 2,
    xmlComment: 2,
    xmlProcessingInstruction: 3
};

function bogus(msg, key, index) {
    return function bogosityBuilderMethod() {
        var loc = arguments[index];
        this.stats[key] = (this.stats[key] || 0) + 1;
        this.bogosity++;
        return null;
    }
}

function BogosityBuilder() {
    this.stats = {};
    this.bogosity = 0;
}

BogosityBuilder.prototype = {};
for (var key in graphNodeTypes)
    BogosityBuilder.prototype[key] = bogus("sharp-literals", key, graphNodeTypes[key] - 1);
for (var key in xmlNodeTypes)
    BogosityBuilder.prototype[key] = bogus("E4X", key, xmlNodeTypes[key] - 1);
BogosityBuilder.prototype.binaryExpression = function(op, left, right) {
    if (op === "..") {
        this.stats.xmlDotDot = (this.stats.xmlDotDot || 0) + 1;
        this.bogosity++;
    }
    return null;
};

var builder = new BogosityBuilder();

void (Reflect.parse(source, { loc: true, builder: builder }));

if (builder.bogosity > 0) {
    print(JSON.stringify(builder.stats));
}
