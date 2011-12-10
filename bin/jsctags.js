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

var _ = require('underscore')._;
var fs = require('fs');
var util = require('util');
var ctags = require('ctags');
var getopt = require('getopt').getopt;
var log = require('log');
var Tags = ctags.Tags;

function usage() {
    util.puts("usage: jsctags [options] path0 [.. pathN]");
    util.puts("options:");
    util.puts("    -f, --output file     place output in the given file (-f " +
             "- for stdout)");
    util.puts("    -h, --help            display this usage info");
    util.puts("    -j, --jsonp function  use JSONP with a function name");
    util.puts("    -o, --output file     synonym for -f");
    util.puts("        --oneprog         combine all inputs into one program");
    util.puts("    -L, --libroot dir     add a CommonJS module root (like " +
             "require.paths)")
    util.puts("    -W, --warning level   set log level (debug/info/warn/" +
             "error, default error)");
    process.exit(1);
}

var opts;
try {
    opts = getopt("help|h", "jsonp|j=s", "libroot|L=s@", "oneprog", "output|o|f=s",
                  "sort|=s", "warning|W=s");
} catch (e) {
    util.puts(e);
    usage();
}

var pathCount = argv.length - 2;
if (opts.help || pathCount === 0) {
    usage();
}

if (opts.warning) {
    var level = opts.warning.toUpperCase();
    if (!log.levels.hasOwnProperty(level)) {
        util.puts("no such logging level: \"" + opts.warning + "\"");
        usage();
    }
    log.level = log.levels[level];
}

function idFor(st) {
    return st.dev + "," + st.ino;
}

var librootIds = {};
if ('libroot' in opts) {
    opts.libroot.forEach(function(libroot) {
        var st = fs.statSync(libroot);
        librootIds[idFor(st)] = true;
    });
}

var tags = new Tags();

// Ascend the directory hierarchy to find the CommonJS package this module is
// in, if any.
function getModuleInfo(fullPath) {
    function commonJS(modulePath, packageId) {
        var ext = path.extname(modulePath), len = modulePath.length;
        var modulePart = modulePath.substring(0, len - ext.length);
        var moduleId = (packageId != null)
                       ? packageId + ":" + modulePart
                       : modulePart;
        return { commonJS: true, module: moduleId };
    }

    var dir = path.dirname(fullPath);
    var i = 0, lastPath = null, libPath = null;
    while (true) {
        var p, st;
        try {
            p = dir;
            _(i).times(function() { p = path.dirname(p); });
            st = fs.statSync(p);
        } catch (e) {
            break;
        }

        if (p === lastPath) {
            break;
        }
        lastPath = p;

        var metadataPath = path.join(p, "package.json");
        try {
            var metadata = fs.readFileSync(metadataPath);
            var packageId = JSON.parse(metadata).name;
            if (typeof(packageId) !== 'string') {
                // Fall back to the directory name in case we're in a package
                // that doesn't conform to the CommonJS spec, such as a Bespin
                // plugin.
                packageId = path.basename(p);
            }

            if (libPath == null) {
                // We're in a nonconformant (Bespin-style) package lacking a
                // "lib" directory. Assume that the module files are rooted
                // alongside the package.json file.
                libPath = p;
            }

            return commonJS(fullPath.substring(libPath.length + 1), packageId);
        } catch (e) {}

        if (path.basename(p) === "lib") {
            libPath = p;
        }

        if (librootIds.hasOwnProperty(idFor(st))) {
            return commonJS(fullPath.substring(p.length + 1));
        }

        if (p.lastIndexOf("/") < 1) {
            // For some reason path.dirname() returns "." once it's done.
            break;
        }

        i++;
    }

    return { commonJS: false };
}

var idsSeen = {};
function processPath(p) {
    var st = fs.statSync(p);
    var id = idFor(st);
    if (id in idsSeen) {
        return; // avoid loops
    }
    idsSeen[id] = true;

    var ext = path.extname(p).toLowerCase();
    if (st.isDirectory()) {
        fs.readdirSync(p).forEach(function(filename) {
            processPath(path.join(p, filename));
        });
    } else if (ext === ".js" || ext === ".jsm") {
        try {
            var data = fs.readFileSync(p, "utf8");
            tags.scan(data, p, getModuleInfo(p));
        } catch (e) {
            if ('lineNumber' in e) {
                util.puts("error:" + p + ":" + e.lineNumber + ": " + e);
            } else {
                util.puts(e.message);
                throw e;
            }
        }
    }
}

if (opts.oneprog)
  processMany();
else
  for (var i = 0; i < pathCount; i++) {
    //processPath(argv[i + 2], false, "", "");
    //dimvar: processPath seems to use its first arg only
    processPath(argv[i + 2]);
  }

function processMany() {
  var i, fileinfo = new Array(pathCount), f, linecount = 0, l, data,
  readf = fs.readFileSync, pcm1 = pathCount - 1;

  for (i = 0; i <= pcm1; i++) {
    f = argv[i + 2];
    data = readf(argv[i + 2], "utf8");
    if (data.charAt(data.length - 1) === "\n")
      l = data.split("\n").length - 1;
    else {
      l = data.split("\n").length;
      data += "\n";
    }
    fileinfo[i] = {path: f, lines: l, data: data,
                   start: linecount + 1, end: linecount + l};
    linecount += l;
  }

  for (data = "", i = pcm1; i >= 0; --i) data = fileinfo[i].data + data;
  // the decision to pass argv[2] here is arbitrary
  tags.scan(data, argv[2], getModuleInfo(argv[2]));

  function getFileInfo(ln) {
    var i = 0, f, s = 0, e = pcm1, floor = Math.floor;
    while (true) {
      i = floor((s + e) / 2);
      f = fileinfo[i];
      if (ln < f.start)
        e = i;
      else if (ln >= f.start && ln <= f.end)
        return {tagfile: f.path, lineno: ln - f.start + 1};
      else
        s = i + 1;
    }
  }

  for (l = tags.tags.length, i = 0; i < l; i++) {
    var t= tags.tags[i];
    var fi = getFileInfo(t.lineno);
    t.tagfile = fi.tagfile;
    t.lineno = fi.lineno.toString();
  }
}

var out;
if (opts.hasOwnProperty('output')) {
    if (opts.output === '-') {
        out = process.stdout;
    } else {
        out = fs.createWriteStream(opts.output);
    }
} else if (opts.hasOwnProperty('jsonp')) {
    out = fs.createWriteStream("tags.jsonp");
} else {
    out = fs.createWriteStream("tags");
}

if (opts.hasOwnProperty('jsonp')) {
    tags.writeJSONP(out, opts.jsonp);
} else {
    tags.write(out, opts);
}

if (out != process.stdout) {
    out.end();
}
