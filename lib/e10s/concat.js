#!/usr/bin/env node

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

var path = require("path");
var fs = require("fs");
var async = require("async");

var xul = require("./xul");

var spawn = require("child_process").spawn;

function concat(root, jses, jsms, xuls, pureJSOut, wrappedJSOut, coordsOut, skippedOut, tempOut) {
    var currentLine = 1;
    var coords = {};
    var skipped = {};
    var skippedAny = false;

    var pureJSStream = fs.createWriteStream(pureJSOut, { encoding: 'utf8' });
    var wrappedJSStream = fs.createWriteStream(wrappedJSOut, { encoding: 'utf8' });

    function countLines(str) {
        var matches = str.match(/\n/g);
        if (matches)
            currentLine += matches.length;
    }

    function puts(str, cb, wrappedStr) {
        var toDrain = [];
        if (!pureJSStream.write(str))
            toDrain.push(pureJSStream);
        if (!wrappedJSStream.write(wrappedStr || str))
            toDrain.push(wrappedJSStream);

        if (toDrain.length === 0) {
            process.nextTick(cb);
        } else {
            async.forEachSeries(toDrain, function(stream, cb) {
                stream.once("drain", cb);
            }, cb);
        }
    }

    function tryCat(file, cb) {
        var fullPath = path.join(root, file);
        checkFileSyntax(fullPath, function(passed) {
            if (!passed) {
                skippedAny = true;
                skipped[file] = true;
                cb();
            } else {
                cat(file, fullPath, cb);
            }
        });
    }

    function checkFileSyntax(fullPath, cb) {
        var rs = fs.createReadStream(fullPath, { encoding: 'utf8' });
        var ws = fs.createWriteStream(tempOut, { flags: 'w+', encoding: 'utf8' });
        ws.write("(function(){");
        rs.pipe(ws, { end: false });
        rs.on("error", function(err) {
            console.log(err.toString());
            cb(false);
        });
        rs.on("end", function(err) {
            if (err) {
                cb(false);
                return;
            }
            ws.write("\n})();\n");
            ws.end();
            ws.on('close', function(err) {
                if (err)
                    cb(false);
                else
                    checkTempSyntax(function(exitCode) { cb(exitCode === 0) });
            });
        });
    }

    function cat(file, fullPath, cb) {
        wrappedJSStream.write("(function(){");
        coords[file] = currentLine;
        var rs = fs.createReadStream(fullPath, { encoding: 'utf8' });
        rs.on("data", countLines);
        handleErrors(rs, cb, false);
        rs.pipe(pureJSStream, { end: false });
        rs.pipe(wrappedJSStream, { end: false });
        rs.on("end", function() {
            currentLine++;
            puts("\n", cb, "\n})();\n");
        });
    }

    function wrapHandler(filename, lineno, contents) {
        // munge the handler name
        var munged = filename.replace(/[.\/]/g, "_").replace(/[^a-z0-9_$]*/g, "");
        var handler = "$handler_" + munged + "_" + lineno;

        return "function " + handler + "(event) { " + contents + "\n}\n";
    }

    function handleErrors(x, cb, result) {
        x.on('error', function(err) {
            console.log(String(err));
            cb(result);
        });
    }

    function checkTempSyntax(cb) {
        var src =
            "try { " +
            "Reflect.parse(snarf('" + tempOut + "')); " +
            "} catch (e) { quit(1) }";
        var sm = spawn("js", ["-e", src], { customFds: [-1, 1, 2] });
        handleErrors(sm, cb, 1);
        sm.on('exit', cb);
    }

    function checkSourceSyntax(src, cb) {
        var tempStream = fs.createWriteStream(tempOut, { flags: 'w+', encoding: 'utf8' });
        tempStream.write("(function(){" + src + "\n})();\n");
        tempStream.end();
        handleErrors(tempStream, cb, 1);
        tempStream.on('close', function() {
            checkTempSyntax(cb);
        });
    }

    function expandXMLEntities(s) {
        // FIXME: handle &nnnn; and &xhhhh; entities
        return s.replace(/&lt;/g, "<")
                .replace(/&gt;/g, ">")
                .replace(/&amp;/g, "&")
                .replace(/&apos;/g, "'")
                .replace(/&quot;/g, '"');
    }

    function printerFor(file) {
        return function printScript(script, cb) {
            if (script.contents) {
                var contents =
                    expandXMLEntities(script.eventType
                                      ? wrapHandler(file, script.line, script.contents)
                                      : script.contents + "\n");
                checkSourceSyntax(contents, function(exitCode) {
                    if (exitCode === 0) {
                        if (!coords[file])
                            coords[file] = {};
                        coords[file][script.line] = currentLine;
                        countLines(contents);
                        puts(contents, cb);
                    } else {
                        skippedAny = true;
                        if (!skipped[file])
                            skipped[file] = {};
                        skipped[file][script.line] = contents;
                        process.nextTick(cb);
                    }
                });
            } else {
                process.nextTick(cb);
            }
        };
    }

    function extract(file, cb) {
        xul.extractScripts(path.join(root, file), function(err, scripts) {
            if (!err)
                async.forEachSeries(scripts, printerFor(file), cb);
            else
                process.nextTick(function() { cb(err) });
        });
    }

    async.series([
        function(next) { async.forEachSeries(jses, tryCat, next) },
        function(next) { async.forEachSeries(jsms, tryCat, next) },
        function(next) { async.forEachSeries(xuls, extract, next) },
        function(next) {
            pureJSStream.end();
            wrappedJSStream.end();
            var coordsStream = fs.createWriteStream(coordsOut, { encoding: 'utf8' });
            handleErrors(coordsStream, next, undefined);
            coordsStream.write(JSON.stringify(coords));
            coordsStream.end();
            coordsStream.on('close', next);
        },
        function(next) {
            if (skippedAny) {
                var skippedStream = fs.createWriteStream(skippedOut, { encoding: 'utf8' });
                handleErrors(skippedStream, next, undefined);
                skippedStream.write(JSON.stringify(skipped));
                skippedStream.end();
            }
        }
    ], function(err) {
        if (err) {
            console.log(err.stack || String(err));
            process.exit(1);
        }
    });
}

function main(args) {
    var root = args[0];
    var jses = JSON.parse(args[1]);
    var jsms = JSON.parse(args[2]);
    var xuls = JSON.parse(args[3]);
    var pureJS = args[4];
    var wrappedJS = args[5];
    var coords = args[6];
    var skipped = args[7];
    var temp = args[8];
    process.addListener('exit', function() {
        if (path.existsSync(temp)) {
            try { fs.unlinkSync(temp); }
            catch (rmErr) {
                console.log("failed to unlink temp file: " + temp);
                console.log(rmErr);
            }
        }
    });
    concat(root, jses, jsms, xuls, pureJS, wrappedJS, coords, skipped, temp);
}

main(process.argv.slice(2));
