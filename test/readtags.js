//#!/usr/bin/env node
var tags = require('../lib/jsctags/ctags').Tags,
    fs = require('fs'),
    util = require('util'),
    path = require('path'),
    argv = process.argv;

tags = new tags();

fs.readFile(argv[2], 'utf-8', function (e, data) {
  if (e) throw e;
  //tags.readString(data);
  tags.scan(data, argv[2]);
  
  var result = (argv.length >= 4) ? tags.stem(argv[3]) : tags.tags;
  util.puts(util.inspect(result));
});