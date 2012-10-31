#!/usr/bin/env node
;

var path = require('path');
var fs = require("fs");
var print = console.log,
    readFileSync = require('fs').readFileSync,
    parse = require('../../narcissus/lib/parser').parse,
    desugar = require('../../narcissus/lib/desugaring').desugar,
    analyze_addon = require('./jscfa').analyze_addon;

Narcissus.options.allowHTMLComments = true;

function printf(fd,s) { fs.writeSync(fd, s, null, 'utf8'); }

var addon = process.argv[2];
var coordsFile = process.argv[3];
var xpiFile = process.argv[4];
var resultsDir = process.argv[5] || ".";

try {
  var ast = desugar(parse(readFileSync(addon), addon, 1));
  var lines = ast.tokenizer.source.split("\n");
  var startTime = process.uptime();
  var timeout = 300; // 5 minutes
  var results = analyze_addon(ast, timeout);
  var evts = [], contentObjs = [], safe_evts = [];

  results.forEach(function(r) {
    if (r.kind === "Touch content")
      contentObjs.push(r);
    else if ("status" in r)
      (r.status[3] === "unsafe" ? evts : safe_evts).push(r);
  });

  // To use the script for debugging (i.e., call it directly on all.js), 
  // the next call should succeed even when argv[3] and up are missing.
  humanReadableResults(evts, safe_evts, contentObjs);
  print("done with humanreadableresults");
  var fhandle = readFileSync(coordsFile);
  var coords = parseCoords(fhandle);
  var entries = [];

  evts.forEach(function(evt) {
    var st = evt.status;
    var lineno = evt.lineno;
    var realPath = getRealPath(lineno, coords);
    entries.push({
      code: lines[lineno - 1],
      path: realPath.path,
      line: realPath.line,
      kind: "Attach listener",
      event: st[0].slice(0, -1),
      target: st[1],
      source: st[2],
      flagged: st[3]
    });
  });

  contentObjs.forEach(function(con) {
    var lineno = con.lineno;
    var realPath = getRealPath(lineno, coords);
    entries.push({
      code: lines[lineno - 1],
      path: realPath.path,
      line: realPath.line,
      kind: "Touch content"
    });    
  });

  var fd = fs.openSync(path.join(resultsDir, "evts"), "w", 0777);
  printf(fd, JSON.stringify({
    addon: xpiFile,
    results: entries,
  }));
  fs.closeSync(fd);

  var completed, astSize, loc, runtime, memused;
  if (results.timedout) {
    completed = "timeout";
    runtime = (timeout * 1000) + " ms";
  }
  else {
    completed = "done";
    runtime = ((process.uptime() - startTime) * 1000) + " ms";
  }
  astSize = results.astSize + " AST nodes";
  loc = lines.length + " LOC";
  memused = (process.memoryUsage().heapUsed / 1000000) + " MB";
  printResult(completed + "\n" + astSize + "\n" + loc + "\n" + runtime + "\n" +
              memused + "\n" + entries.length + " e10s violations\n" +
              safe_evts.length + " safe listeners\n");
}
catch (e) {
  printResult("failed", e && (e.message + "\n" + e.stack));
  process.exit(1);
}

function humanReadableResults(evts, safe_evts, contentObjs) {
  var fd = fs.openSync(path.join(resultsDir, "hrevts"), "w", 0777);

  function printEvt(evt) {
    var st = evt.status;
    printf(fd,
           normStr(lines[evt.lineno - 1].replace(/^\s+/,""), 75) + "     " + 
           normStr(st[0].slice(0, -1), 20) + normStr(st[1], 14) + 
           normStr(st[2], 12) + st[3] + "\n");
  }
  printf(fd,
         normStr("*Source code*", 80) + normStr("*Event name*", 20) +
         normStr("*Attached on*", 14) + normStr("*Came from*", 12) +
         "*Status*\n\n");
  safe_evts.forEach(printEvt);
  printf(fd, "\n");
  evts.forEach(printEvt);
  printf(fd, "\n");

  contentObjs.forEach(function(con) {
    printf(fd, normStr(lines[con.lineno - 1].replace(/^\s+/,""), 75) + "\n");
  });
  printf(fd, "\n");
  fs.closeSync(fd);
}

function parseCoords(src) {
  var obj = JSON.parse(src);
  var result = [];
  for (var key in obj) {
    var val = obj[key];
    if (typeof val === "number") {
      result.push({ line: val, realPath: key, realLine: 1 });
      continue;
    }
    for (var realLine in val)
      result.push({ line: val[realLine], realPath: key, realLine: realLine });
  }
  function compareLines(entry1, entry2) {
      return entry1.line < entry2.line
           ? -1
           : entry1.line > entry2.line
           ? 1
           : 0;
  }
  result.sort(compareLines);
  return result;
}

// line: 1-indexed
function getRealPath(line, coords) {
  var entry;
  for (var i = coords.length - 1; i >= 0; i--) {
    entry = coords[i];
    if (entry.line <= line)
      break;
  }
  var scriptOffset = line - entry.line;
  var scriptStart = entry.realLine;
  return {
    path: entry.realPath,
    line: scriptStart + scriptOffset
  };
}

function printResult(result, extras) {
  try {
    var fd = fs.openSync(path.join(resultsDir, "result"), "w", 0777);
    printf(fd, result + "\n");
    if (extras)
        printf(fd, extras);
    fs.closeSync(fd);
  } catch (e) { }
}

function normStr(s, l) {
  var diff = l - s.length;

  if (diff > 0)
    for (var i = 0; i < diff; i++) s += " ";
  else
    s = s.slice(0, s.length + diff);
  return s;
}
