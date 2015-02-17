#!/usr/bin/env node
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

var argv = process.argv;
var path = require('path');


var cwd = path.dirname(argv[1]);
var libdir = path.join(cwd, "..", "lib");
var jscdir = path.join(libdir, "jsctags");

function requireJsc(mod) {
	return require(path.join(jscdir, mod));
}

var util = require('util');
var _ = requireJsc('underscore')._;
var getTags = require('../lib/cfa2/jscfa').getTags;
var parse = require('../narcissus/lib/parser').parse;

// prints a value and exits
function returnVal(val) {
  // we're only allowed to return one value
  if(returnVal.returned) return false;
  returnVal.returned = true;

  // wait for the value to be written
  process.stdout.once('drain', function () {
	process.exit();
  });

  util.print(val);
  return true;
}
// static variable
returnVal.returned = false;

// prints an object as json string and exits
function returnJson(obj) {
  return returnVal(JSON.stringify(obj));
}

var stdin = process.openStdin();
stdin.setEncoding("utf8");

var buf = [];
stdin.on("data", _(buf.push).bind(buf));
stdin.on("end", function () {
  var src = buf.join("");
  var lines, ast;
  try {
    lines = src.split("\n");
    ast = parse(src, "js", 1);
  } catch (e) {
    returnJson({ error: e.message, stage: "parse" });
    return;
  }

  var json;
  try {
    json = getTags(ast, "js", lines, {});
  } catch (e) {
    json = { error: e.message, stage: "analysis" };
  }

  returnJson(json);
  return;
});
