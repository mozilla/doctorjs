var path = require('path');

var parse = require('../../narcissus/lib/parser').parse;
var getTags = require('../cfa2/jscfa').getTags;
var formidable = require('../formidable');

function analyze(cwd, req, resp) {
  // FIXME: extra field for header message (instead of "Not Found")
  function error(code, msg) {
    resp.writeHead(code, "Not Found", { 'Content-type': 'text/plain' });  
    resp.end(code + " " + msg);
  }

  if (req.method !== 'POST') {
    resp.writeHead(405, "Invalid Method", { 'Content-type': 'text/plain' });
    resp.end("405 Only POST method allowed");
    return;                                        
  }

  var form = new formidable.IncomingForm();
  var src;

  // prevent formidable from saving files
  form.onPart = function (part) {
	if(!part.filename)
	  this.handlePart(part);
  };
  form
    .addListener('error', function (err) {
      error(400, err);
    })
    .addListener('field', function (field, value) {
      if (field === 'src')
        src = value;
    })
    .addListener('end', function () {
      if (!src) {
        error(400, 'No "src" field in POST');
        return;
      }

      // farm the work out to rn.js
      var spawn = require('child_process').spawn;
      var rn = spawn('node', [path.join(cwd, 'rn.js')]);

      // on timeout, kill the process and send an error
      var timeout = setTimeout(function () {
        if (rn) {
          rn.kill(); // ooh, ulträa brutal ;)
          error(500, "Service timed out");
        }
      }, 10000);

      // forward the output ctags to the response
      var buf = [];
      rn.stdout.on("data", _(buf.push).bind(buf));
      rn.stdout.on("end", function () {
        clearTimeout(timeout);
        rn = null;
        resp.writeHead(200, "OK", { "Content-type": "application/json" });
        resp.end(buf.join(""));
      });
	  
      // send the input program to rn.js
      rn.stdin.end(src);
    });

  form.parse(req);
}

exports.analyze = analyze;
