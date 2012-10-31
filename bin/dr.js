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
var http = require('http');
var url = require('url');
var servetypes = requireJsc('servetypes');

function usage(msg) {
  util.print("usage: " + path.basename(argv[1]) + " [options]\n");
  util.print("  -h/--help        Print usage information\n");
  util.print("  -s/--static      Directory containing static web content\n");
  util.print("  -n/--no-service  Disable the JSON service");
  util.print("  -p/--port        Server port to listen on\n");
  if (msg) {
    util.print("\n" + msg + "\n");
    process.exit(1);
  }

  process.exit(0);
}

function parseOpts(argv, callback) {
  var dir = null;
  var port = 8080;
  var service = true;

  for (var i = 0; i < argv.length; i++) {
    switch (argv[i]) {
    case "--help":
    case "-h":
      callback(null, { help: true, dir: null, port: null, service: null });
      break;

    case "--no-service":
    case "-n":
      service = false;
      break;

    case "--port":
    case "-p":
      i++;
      if (i >= argv.length) {
        callback("port not specified", null);
        return;
      }
      port = parseInt(argv[i]);
      if (isNaN(port)) {
        callback("invalid port", null);
        return;
      }
      break;

    case "--static":
    case "-s":
      i++;
      if (i >= argv.length) {
        callback("static source directory not specified", null);
        return;
      }
      dir = argv[i];
      break;
    }
  }

  if (!service && !dir) {
    callback("service disabled without static directory", null);
    return;
  }

  if (!dir) {
    callback(null, { help: false, dir: null, port: port, service: service });
    return;
  }

  require('fs').stat(path.normalize(dir), function(err, stats) {
    if (!stats || !stats.isDirectory())
      callback("bad directory", null);
    else
      callback(null, { help: false, dir: dir, port: port, service: service });
  });
}

// construct a request handler for the entire web site
function makeSiteHandler(dir, service) {
  var mimeTypes = {
    jpg: "image/jpeg",
    png: "image/png",
    gif: "image/gif",
    html: "text/html",
    txt: "text/plain"
  };

  return function (req, resp) {
    var query = url.parse(req.url).pathname;

    if (service && query === '/analyze') {
      servetypes.analyze(cwd, req, resp);
      return;
    }

    if (query === '/')
        query = '/index.html';

    var file = path.join(dir, query);
    var ext = path.extname(file);

    var fs = require('fs');
    fs.stat(file, function (err, stats) {
      if (!stats || !stats.isFile()) {
        util.debug("404: " + file);
        resp.writeHead(404, "Not Found", { 'Content-type': 'text/plain' });
        resp.end("404 Not Found");
        return;
      }

      resp.writeHead(200, "OK", { "Content-type": mimeTypes[ext] });

      var stream = fs.createReadStream(file);
      stream.on("data", _.bind(resp.write, resp));
      stream.on("end", _.bind(resp.end, resp));
    });
  };
}

// request handler for just the JSON service
function service(req, resp) {
  var query = url.parse(req.url).pathname;

  if (query !== '/analyze') {
    resp.writeHead(404, "Not Found", { 'Content-type': 'text/plain' });
    resp.end("404 Not Found");
    return;
  }

  servetypes.analyze(cwd, req, resp);
}

parseOpts(argv.slice(2), function(err, opts) {
  if (err)
    usage(err);

  if (opts.help)
    usage();

  var handler;
  if (opts.dir) {
    util.log("staging site from " + opts.dir);
    handler = makeSiteHandler(opts.dir, opts.service);
  } else {
    util.log("running JSON service only");
    handler = service;
  }

  util.log("listening on port " + opts.port + "...");
  http.createServer(handler).listen(opts.port, "127.0.0.1");
});
