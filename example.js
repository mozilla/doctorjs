var tags = require('lib/jsctags/ctags').Tags,
    fs = require('fs');
    
tags = new tags();

fs.readFile('./example.js', 'utf-8', function (e, data) {
  tags.scan(data, __dirname + '/example.js', {commonJS: false});
  console.log(tags);
});