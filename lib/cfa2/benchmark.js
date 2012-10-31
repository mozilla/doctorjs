#!/usr/bin/env node
;

var print = console.log,
readFileSync = require('fs').readFileSync,
spawn = require('child_process').spawn,
parse = require('../../narcissus/lib/parser').parse,
getTags = require('./jscfa').getTags;

var arg = process.argv[2], files = [], done = false;

if ((arg === "sunspider") || (arg === "v8/v6")) {
  var ls = spawn('ls', [arg]);
  ls.stdout.on('data', function(data) {
    var fs = (""+data).split("\n");
    for (var i = 0, len = fs.length; i < len; i++)
      /js$/.test(fs[i]) && files.push(arg + "/" + fs[i]);
  });
  ls.on('exit', function() {
    for (var i = 0, len = files.length; i < len; i++) run(files[i]);
  });
}
else 
  run(arg);

function run(file) {
  getTags(parse(readFileSync(file), file, 1), file, [], {});
  print(file + ": " + (process.memoryUsage().heapUsed / 1000000) + " MB");
}
