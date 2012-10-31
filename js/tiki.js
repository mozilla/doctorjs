/*! @license
==========================================================================
Tiki 1.0 - CommonJS Runtime
copyright 2009-2010, Apple Inc., Sprout Systems Inc., and contributors.

Permission is hereby granted, free of charge, to any person obtaining a 
copy of this software and associated documentation files (the "Software"), 
to deal in the Software without restriction, including without limitation 
the rights to use, copy, modify, merge, publish, distribute, sublicense, 
and/or sell copies of the Software, and to permit persons to whom the 
Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in 
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR 
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, 
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE 
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER 
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING 
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER 
DEALINGS IN THE SOFTWARE.

Tiki is part of the SproutCore project.

SproutCore and the SproutCore logo are trademarks of Sprout Systems, Inc.

For more information visit http://www.sproutcore.com/tiki

==========================================================================
@license */

/*globals tiki ENV ARGV ARGS */

"use modules false";
"use loader false";

/**
  Implements a very simple handler for the loader registration API so that
  additional scripts can load without throwing exceptions.  This loader can
  also return module instances for modules registered with an actual factory
  function.
  
  Note that this stub loader cannot be used on its own.  You must load the 
  regular tiki package as well, which will replace this loader as soon as it
  is fetched.
*/
if ("undefined" === typeof tiki) { var tiki = function() {
  
  var T_UNDEFINED = 'undefined',
      queue = [];
        
  // save a registration method in a queue to be replayed later once the 
  // real loader is available.
  function _record(method, args) {
    queue.push({ m: method, a: args });
  }
  
  var tiki = {
    
    // used to detect when real loader should replace this one
    isBootstrap: true,
    
    // log of actions to be replayed later
    queue: queue, 
    
    // helpers just record into queue
    register: function(packageId, opts) { 
      
      // this hack will make unit tests work for tiki by adding core_test to
      // the list of dependencies.
      if (packageId.match(/^tiki/) && this.ENV) {
        if ((this.ENV.app === 'tiki') && (this.ENV.mode === 'test')) {
          if (!opts.dependencies) opts.dependencies = {};
          opts.dependencies['core_test'] = '~';
        }
      }
      
      _record('register', arguments);
       return this;  
    },
    
    // Keep these around just in case we need them in the end...
    // script:   function() { 
    //   _record('script', arguments); 
    //   return this; 
    // },
    // 
    // stylesheet: function() { 
    //   _record('stylesheet', arguments); 
    //   return this; 
    // },

    // modules actually get saved as well a recorded so you can use them.
    module: function(moduleId, factory) {
      if (moduleId.match(/\:tiki$/)) this.tikiFactory = factory;
      _record('module', arguments);
      return this ;
    },

    // load the tikiFactory 
    start: function() {
      var exp = {}, ret;
      this.tikiFactory(null, exp, null); // no require or module!
      ret = exp.Browser.start(this.ENV, this.ARGS, queue);
      queue = null;
      return ret ;
    }
    
  };
  
  if (T_UNDEFINED !== typeof ENV) tiki.ENV = ENV;
  if (T_UNDEFINED !== typeof ARGV) tiki.ARGS = ARGV; // for older versions
  if (T_UNDEFINED !== typeof ARGS) tiki.ARGS = ARGS;
  
  return tiki;
  
}(); }


tiki.register('::tiki/1.0.0', { 
  "name": "tiki",
  "version": "1.0.0",
});

tiki.module('::tiki/1.0.0:tiki', function(require, exports, module) {
// ==========================================================================
// Project:   Tiki - CommonJS Runtime
// Copyright: ©2009-2010 Apple Inc. All rights reserved.
// License:   Licened under MIT license (see __preamble__.js)
// ==========================================================================
/*jslint evil:true */

/**
  @file 
  
  This file implements the core building blocks needed to implement the 
  tiki runtime in an environment.  If you can require this one module, you can
  setup a runtime that will load additional packages.
  
  It is important that this module NOT require() any other modules since a
  functioning require() statement may not be available.  The module can 
  populate, but not replace, the exports object.

  To configure a Tiki runtime, you need to create a Sandbox and Loader 
  instance from this API with one or more loader Sources.  The BrowserSource
  object implements the basic source you need to work in the browser.  The
  Repository object implemented in the server-side only 'file' API can be 
  used to load from a local repository of packages.
*/

// used for type checking.  This allows the type strings to be minified.
var T_FUNCTION = 'function',
    T_STRING   = 'string',
    T_UNDEFINED = 'undefined';
    
    
var IS_CANONICAL = /^::/; // must begin with ::
var isCanonicalId = function(id) {
  return !!IS_CANONICAL.exec(id);
};  

var DEBUG = function() {
  exports.debug.apply(this, arguments);
};

exports.debug = function() {
  var msg = Array.prototype.join.call(arguments, '');
  require('util').debug(msg);
};

// ..........................................................
// CORE UTILITIES
// 

var TMP_ARY = [];

/**
  Tests whether the passed object is an array or not.
*/
var isArray;

if (Array.isArray) {
  isArray = Array.isArray;
} else {
  isArray = function(obj) {
    if ('object' !== typeof obj) return false;
    if (obj instanceof Array) return true;
    return obj.constructor && (obj.constructor.name==='Array');
  };
}
exports.isArray = isArray;

/**
  Create a new object with the passed object as the prototype.
*/
var createObject;
if (Object.create) {
  createObject = Object.create;
} else {
  var K = function() {},
      Kproto = K.prototype;
  createObject = function(obj) {
    if (!obj) obj = Object.prototype;
    K.prototype = obj;
    
    var ret = new K();
    ret.prototype = obj;
    K.prototype = Kproto;
    
    return ret ;
  };
}
exports.createObject = createObject;

var _constructor, _extend, extend;

// returns a new constructor function with clean closure...
_constructor = function() {
  return function() {
    if (this.init) return this.init.apply(this, arguments);
    else return this;
  };
};

_extend = function() {
  return extend(this);
};

/**
  Creates a "subclass" of the passed constructor.  The default constructor
  will call look for a local "init" method and call it.
  
  If you don't pass an initial constructor, this will create a new based 
  object.
*/
extend = function(Constructor) {
  var Ret = _constructor();
  Ret.prototype = createObject(Constructor.prototype);
  Ret.prototype.constructor = Ret;
  Ret.super_ = Constructor;
  Ret.extend = _extend;
  return Ret;
};
exports.extend = extend;

/**
  Invokes the passed fn on each item in the array in parallel.  Invokes
  done when finished.
  
  # Example
  
      parallel([1,2,3], function(item, done) {
        // do something with item
        done();
      })(function(err) {
        // invoked when done, err if there was an error
      });
      
  @param {Array} array 
    items to iterate
    
  @param {Function} fn
    callback to invoke
    
  @returns {void}
*/
var parallel = function(array, fn) {
  if (fn && !fn.displayName) fn.displayName = 'parallel#fn';
  
  return function(done) {
    if (array.length === 0) return done(null, []);
    
    var len = array.length,
        cnt = len,
        cancelled = false,
        idx;

    var tail = function(err) {
      if (cancelled) return; // nothing to do

      if (err) {
        cancelled = true;
        return done(err);
      }

      if (--cnt <= 0) done(); 
    };
    tail.displayName = 'parallel#tail';

    for(idx=0;idx<len;idx++) fn(array[idx], tail);
  };
};
parallel.displayName = 'parallel';

/**
  @private
  
  Implements the sync map() on all platforms
*/
var map;
if (Array.prototype.map) {
  map = function(array, fn) {
    return array.map(fn);
  };

} else {
  map = function(array, fn) {
    var idx, len = array.length, ret = [];
    for(idx=0;idx<len;idx++) {
      ret[idx] = fn(array[idx], idx);
    }
    return ret ;
  };
}
map.displayName = 'map';


var PENDING = 'pending',
    READY   = 'ready',
    RUNNING = 'running';
    
/**
  Returns a function that will execute the continuable exactly once and 
  then cache the result.  Invoking the same return function more than once
  will simply return the old result. 
  
  This is a good replacement for promises in many cases.
  
  h3. Example
  
  {{{
    // load a file only once
    var loadit = Co.once(Co.fs.loadFile(pathToFile));

    loadit(function(content) { 
      // loads the file
    });
    
    loadit(function(content) {
      // if already loaded, just invokes with past content
    });
    
  }}}
  
  @param {Function} cont
    Continuable to invoke 
    
  @returns {Function} 
    A new continuable that will only execute once then returns the cached
    result.
*/
var once = function(action, context) {
  var state = PENDING,
      queue = [],
      makePending = false,
      args  = null;

  var ret = function(callback) {
    if (!context) context = this;
    
    // cont has already finished, just invoke callback based on result
    switch(state) {
      
      // already resolved, invoke callback immediately
      case READY:
        callback.apply(null, args);
        break;

      // action has started running but hasn't finished yet
      case RUNNING:
        queue.push(callback);
        break;
        
      // action has not started yet
      case PENDING:
        queue.push(callback);
        state = RUNNING;

        action.call(context, function(err) {
          args  = Array.prototype.slice.call(arguments);
          
          var oldQueue = queue, oldArgs = args;

          if (makePending) {
            state = PENDING;
            queue = [];
            args  = null; 
            makePending = false;

          } else {
            state = READY;
            queue = null;
          }
          
          if (oldQueue) {
            oldQueue.forEach(function(q) { q.apply(null, oldArgs); });
          }
        });
        break;
    }
    return this;
  };
  ret.displayName = 'once#handler';

  // allow the action to be reset so it is called again
  ret.reset = function() {
    switch(state) {
      
      // already run, need to reset
      case READY: 
        state = PENDING;
        queue = [];
        args  = null;
        break;
        
      // in process - set makePending so that resolving will reset to pending
      case RUNNING:
        makePending = true;
        break;
        
      // otherwise ignore pending since there is nothing to reset
    }
  };
  ret.reset.displayName = 'once#handler.reset';
  
  return ret ;
};
exports.once = once;


/**
  Iterate over a property, setting display names on functions as needed.
  Call this on your own exports to setup display names for debugging.
*/
var displayNames = function(obj, root) {
  var k,v;
  for(k in obj) {
    if (!obj.hasOwnProperty(k)) continue ;
    v = obj[k];
    if ('function' === typeof v) {
      if (!v.displayName) {
        v.displayName = root ? (root+'.'+k) : k;
        displayNames(v.prototype, v.displayName);
      }
      
    }
  }
  return obj;
};

// ..........................................................
// ERRORS
// 

var NotFound = extend(Error);
NotFound.prototype.init = function(canonicalId, pkgId) {
  var msg = canonicalId+' not found';
  if (pkgId) {
    if (T_STRING === typeof pkgId) msg = msg+' '+pkgId;
    else msg = msg+' in package '+(pkgId.id || '(unknown)');
  }
  this.message = msg;
  return this;
};
exports.NotFound = NotFound;

var InvalidPackageDef = extend(Error);
InvalidPackageDef.prototype.init = function(def, reason) {
  if ('undefined' !== typeof JSON) def = JSON.stringify(def);
  this.message = "Invalid package definition. "+reason+" "+def;
};
exports.InvalidPackageDef = InvalidPackageDef;

// ..........................................................
// semver
// 

// ..........................................................
// NATCOMPARE
// 
// Used with thanks to Kristof Coomans 
// Find online at http://sourcefrog.net/projects/natsort/natcompare.js
// Cleaned up JSLint errors

/*
natcompare.js -- Perform 'natural order' comparisons of strings in JavaScript.
Copyright (C) 2005 by SCK-CEN (Belgian Nucleair Research Centre)
Written by Kristof Coomans <kristof[dot]coomans[at]sckcen[dot]be>

Based on the Java version by Pierre-Luc Paour, of which this is more or less a straight conversion.
Copyright (C) 2003 by Pierre-Luc Paour <natorder@paour.com>

The Java version was based on the C version by Martin Pool.
Copyright (C) 2000 by Martin Pool <mbp@humbug.org.au>

This software is provided 'as-is', without any express or implied
warranty.  In no event will the authors be held liable for any damages
arising from the use of this software.

Permission is granted to anyone to use this software for any purpose,
including commercial applications, and to alter it and redistribute it
freely, subject to the following restrictions:

1. The origin of this software must not be misrepresented; you must not
claim that you wrote the original software. If you use this software
in a product, an acknowledgment in the product documentation would be
appreciated but is not required.
2. Altered source versions must be plainly marked as such, and must not be
misrepresented as being the original software.
3. This notice may not be removed or altered from any source distribution.
*/
var natcompare = function() {
  
  var isWhitespaceChar = function(a) {
    var charCode = a.charCodeAt(0);
    return charCode <= 32;
  };

  var isDigitChar = function(a) {
    var charCode = a.charCodeAt(0);
    return ( charCode >= 48  && charCode <= 57 );
  };

  var compareRight = function(a,b) {
    var bias = 0,
        ia   = 0,
        ib   = 0,
        ca, cb;

    // The longest run of digits wins.  That aside, the greatest
    // value wins, but we can't know that it will until we've scanned
    // both numbers to know that they have the same magnitude, so we
    // remember it in BIAS.
    for (;; ia++, ib++) {
      ca = a.charAt(ia);
      cb = b.charAt(ib);

      if (!isDigitChar(ca) && !isDigitChar(cb)) return bias;
      else if (!isDigitChar(ca)) return -1;
      else if (!isDigitChar(cb)) return +1;
      else if (ca < cb) if (bias === 0) bias = -1;
      else if (ca > cb) if (bias === 0) bias = +1;
      else if (ca === 0 && cb === 0) return bias;
    }
  };

  var natcompare = function(a,b) {

    var ia  = 0, 
    ib  = 0,
    nza = 0, 
    nzb = 0,
    ca, cb, result;

    while (true) {
      // only count the number of zeroes leading the last number compared
      nza = nzb = 0;

      ca = a.charAt(ia);
      cb = b.charAt(ib);

      // skip over leading spaces or zeros
      while ( isWhitespaceChar( ca ) || ca =='0' ) {
        if (ca == '0') nza++;
        else nza = 0; // only count consecutive zeroes
        ca = a.charAt(++ia);
      }

      while ( isWhitespaceChar( cb ) || cb == '0') {
        if (cb == '0') nzb++;
        else nzb = 0; // only count consecutive zeroes
        cb = b.charAt(++ib);
      }

      // process run of digits
      if (isDigitChar(ca) && isDigitChar(cb)) {
        if ((result = compareRight(a.substring(ia), b.substring(ib))) !== 0) {
          return result;
        }
      }

      // The strings compare the same.  Perhaps the caller
      // will want to call strcmp to break the tie.
      if (ca === 0 && cb === 0) return nza - nzb;

      if (ca < cb) return -1;
      else if (ca > cb) return +1;

      ++ia; ++ib;
    }
  };

  return natcompare;
}();
exports.natcompare = natcompare;

// ..........................................................
// PUBLIC API
// 

// Support Methods
var invalidVers = function(vers) {
  return new Error('' + vers + ' is an invalid version string');
};
invalidVers.displayName = 'invalidVers';

var compareNum = function(vers1, vers2, num1, num2) {
  num1 = Number(num1);
  num2 = Number(num2);
  if (isNaN(num1)) throw invalidVers(vers1);
  if (isNaN(num2)) throw invalidVers(vers2);
  return num1 - num2 ;
};
compareNum.displayName = 'compareNum';


var vparse;
var semver = {
  
  /**
    Parse the version number into its components.  Returns result of a regex.
  */
  parse: function(vers) {
    var ret = vers.match(/^(=|~)?([\d]+?)(\.([\d]+?)(\.(.+))?)?$/);
    if (!ret) return null; // no match
    return [ret, ret[2], ret[4] || '0', ret[6] || '0', ret[1]];
  },


  /**
    Returns the major version number of a version string. 

    @param {String} vers
      version string

    @returns {Number} version number or null if could not be parsed
  */
  major: function(vers) {
    return Number(vparse(vers)[1]);
  },

  /**
    Returns the minor version number of a version string


    @param {String} vers
      version string

    @returns {Number} version number or null if could not be parsed
  */
  minor: function(vers) {
    return Number(vparse(vers)[2]);
  },

  /**
    Returns the patch of a version string.  The patch value is always a string
    not a number
  */
  patch: function(vers) {
    var ret = vparse(vers)[3];
    return isNaN(Number(ret)) ? ret : Number(ret);
  },

  STRICT: 'strict',
  NORMAL: 'normal',

  /**
    Returns the comparison mode.  Will be one of NORMAL or STRICT
  */
  mode: function(vers) {
    var ret = vparse(vers)[4];
    return ret === '=' ? semver.STRICT : semver.NORMAL;
  },

  /**
    Compares two patch strings using the proper matching formula defined by
    semver.org.  Returns:
    
    @param {String} patch1 first patch to compare
    @param {String} patch2 second patch to compare
    @returns {Number} -1 if patch1 < patch2, 1 if patch1 > patch2, 0 if equal 
  */
  comparePatch: function(patch1, patch2) {
    var num1, num2;

    if (patch1 === patch2) return 0; // equal

    num1   = Number(patch1);
    num2   = Number(patch2);

    if (isNaN(num1)) {
      if (isNaN(num2)) {
        // do lexigraphic comparison
        return natcompare(patch1, patch2);

      } else return -1; // num2 is a number therefore num1 < num2

    // num1 is a number but num2 is not so num1 > num2
    } else if (isNaN(num2)) {
      return 1 ;
    } else {
      return num1<num2 ? -1 : (num1>num2 ? 1 : 0) ;
    }
  },

  /**
    Compares two version strings, using natural sorting for the patch.
  */
  compare: function(vers1, vers2) {
    var ret ;

    if (vers1 === vers2) return 0;
    if (vers1) vers1 = vparse(vers1);
    if (vers2) vers2 = vparse(vers2);

    if (!vers1 && !vers2) return 0;
    if (!vers1) return -1; 
    if (!vers2) return 1; 


    ret = compareNum(vers1[0], vers2[0], vers1[1], vers2[1]);
    if (ret === 0) {
      ret = compareNum(vers1[0], vers2[0], vers1[2], vers2[2]);
      if (ret === 0) ret = semver.comparePatch(vers1[3], vers2[3]);
    }

    return (ret < 0) ? -1 : (ret>0 ? 1 : 0);
  },

  /**
    Returns true if the second version string represents a version compatible 
    with the first version.  In general this means the second version must be
    greater than or equal to the first version but its major version must not 
    be different.
  */
  compatible: function(reqVers, curVers) {
    if (!reqVers) return true; // always compatible with no version
    if (reqVers === curVers) return true; // fast path

    // make sure these parse - or else treat them like null
    if (reqVers && !vparse(reqVers)) reqVers = null;
    if (curVers && !vparse(curVers)) curVers = null;

    // try fast paths again in case they changed state
    if (!reqVers) return true; // always compatible with no version
    if (reqVers === curVers) return true; // fast path
    
    // strict mode, must be an exact (semantic) match
    if (semver.mode(reqVers) === semver.STRICT) {
      return curVers && (semver.compare(reqVers, curVers)===0);

    } else {
      if (!curVers) return true; // if no vers, always assume compat

      // major vers
      if (semver.major(reqVers) !== semver.major(curVers)) return false; 
      return semver.compare(reqVers, curVers) <= 0;
    }
  },

  /**
    Normalizes version numbers so that semantically equivalent will be treated 
    the same.
  */
  normalize: function(vers) {
    var patch;

    if (!vers || vers.length===0) return null;
    vers = semver.parse(vers);
    if (!vers) return null;

    patch = Number(vers[3]);
    if (isNaN(patch)) patch = vers[3];

    return [Number(vers[1]), Number(vers[2]), patch].join('.');
  }
  
};
exports.semver = semver;
vparse = semver.parse;


// ..........................................................
// FACTORY
// 

/**
  @constructor
  
  A factory knows how to instantiate a new module for a sandbox, including 
  generating the require() method used by the module itself.  You can return
  custom factories when you install a plugin.  Your module should export
  loadFactory().
  
  The default factory here actually expects to receive a module descriptor
  as generated by the build tools.
*/
var Factory = exports.extend(Object);
exports.Factory = Factory;

Factory.prototype.init = function(moduleId, pkg, factory) {
  this.id  = moduleId;
  this.pkg = pkg;
  this.factory = factory;
};

/**
  Actually generates a new set of exports for the named sandbox.  The sandbox
  must return a module object that can be used to generate the factory.
  
  If the current value of the local factory is a string, then we will actually
  eval/compile the factory as well.
  
  @param sandbox {Sandbox}
    The sandbox the will own the module instance
    
  @param module {Module}
    The module object the exports will belong to
    
  @returns {Hash} exports from instantiated module
*/
Factory.prototype.call = function(sandbox, module) {

  // get the factory function, evaluate if needed
  var func = this.factory,
      filename = this.__filename,
      dirname  = this.__dirname;
      
  if (T_STRING === typeof(func)) {
    func = this.factory = Factory.compile(func, this.pkg.id+':'+this.id);
  }

  // generate a nested require for this puppy
  var req = sandbox.createRequire(module),
      exp = module.exports;
  func.call(exp, req, exp, module, filename, dirname);
  return module.exports;
};


// standard wrapper around a module.  replace item[1] with a string and join.
var MODULE_WRAPPER = [
  '(function(require, exports, module) {',
  null,
  '\n});\n//@ sourceURL=',
  null,
  '\n'];

/**
  Evaluates the passed string.  Returns a function.
  
  @param moduleText {String}
    The module text to compile
    
  @param moduleId {String}
    Optional moduleId.  If provided will be used for debug
    
  @returns {Function} compiled factory
*/
Factory.compile = function(moduleText, moduleId) {
  var ret;
  
  MODULE_WRAPPER[1] = moduleText;
  MODULE_WRAPPER[3] = moduleId || '(unknown module)';
  
  ret = MODULE_WRAPPER.join('');
  ret = eval(ret);
  
  MODULE_WRAPPER[1] = MODULE_WRAPPER[3] = null;
  return ret;
};

exports.Factory = Factory;

// ..........................................................
// MODULE
// 

/**
  A Module describes a single module, including its id, ownerPackage, and
  the actual module exports once the module has been instantiated.  It also
  implements the resource() method which can lookup a resource on the module's
  package.
*/
var Module = exports.extend(Object);
exports.Module = Module;

Module.prototype.init = function(id, ownerPackage, sandbox) {
  this.id           = id;
  this.ownerPackage = ownerPackage;
  this.exports      = {};
  var module        = this;
  
  /**
    Lookup a resource on the module's ownerPackage.  Returns a URL or path 
    for the discovered resource.  The method used to detect the module or 
    package is implemented in the package.
    
    Note that this method is generated for each module we create because some
    code will try to pluck this method off of the module and call it in a
    different context.
    
    @param resourceId {String}
      Full or partial name of resource to retrieve
      
    @param done {Function}
      Optional.  Makes the resource discovery asyncronous
      
    @returns {String} url or path if not called async
  */
  this.resource = function(id) {
    return sandbox.resource(id, module.id, ownerPackage);
  };
};

// ..........................................................
// PACKAGE
// 

/**
  Package expects you to register the package with a config having the 
  following keys:
  
    {
      "name": "name-of-package" (vs canonical id)
      "version": current version of package (if known)
      
      // these are dependencies you require to run.  If the package is 
      // async loaded, these will be the ones loaded
      "dependencies": {
         "package-name": "version"
      },
      
      // these map a specific package-name/version to a canonicalId that must
      // be registered for the package to be loaded.  You may include 
      // additional packages here that may be referenced but are not required
      // to run (for example - lazy loaded packages)
      //
      // This also forms the universe of packages this particular package can
      // reference.
      //
      "tiki:packages": {
        "package-name": [
          { "version": "1.0.0", "id": "canonicalId", "url": "url" }
        ]
      },

      // ids mapped to urls.  all of these scripts must be loaded for this 
      // package to be considered ready 
      "tiki:scripts": {
        "id": "url"
      },
      
      // stylesheets that must be loaded for this package to be considered
      // ready.  The id is used so that the URL can load from a relative path
      // that may move around and still be accurate.
      "tiki:stylesheets": {
        "id": "url",
        "id": "url"
      },
      
      // maps asset paths for non-JS and non-CSS assets to URLs.  Used to 
      // progrmatically load images, etc.
      "tiki:resources": {
        "asset/path": "url",
        "asset/path": "url"
      }
    }

  This registration ensures that the package and it's related assets are 
  loaded.
*/
     
var Package = exports.extend(Object);
exports.Package = Package;

Package.prototype.init = function(id, config) {
  if (!isCanonicalId(id)) id = '::'+id; // normalize
  this.id = id;
  this.config = config;
  this.isReady = true;
};

// ..........................................................
// Package Configs
// 

/**
  Retrieves the named config property.  This method can be overidden by 
  subclasses to perform more advanced processing on the key data
  
  @param {String} key
    The key to retrieve
    
  @returns {Object} the key value or undefined
*/
Package.prototype.get = function(key) {
  return this.config ? this.config[key] : undefined;
};

/**
  Updates the named config property.

  @param {String} key
    The key to update
    
  @param {Object} value
    The object value to change
    
  @returns {Package} receiver
*/
Package.prototype.set = function(key, value) {
  if (!this.config) this.config = {};
  this.config[key] = value;
  return this;
};

/**
  Determines the required version of the named packageId, if any, specified
  in this package.
  
  @param {String} packageId
    The packageId to lookup
    
  @returns {String} The required version or null (meaning any)
*/
Package.prototype.requiredVersion = function(packageId) { 
  var deps = this.get('dependencies');
  return deps ? deps[packageId] : null;
};

// ..........................................................
// Nested Packages
// 

/**
  Attempts to match the passed packageId and version to the receiver or a 
  nested package inside the receiver.  If a match is found, returns the 
  packages canonicalId.  Otherwise returns null.  
  
  This does not search remote sources for the package.  It only looks at 
  what packages are available locally.
  
  This method is called after a package version has been checked for 
  compatibility with the package dependencies.  It is not necessary to 
  validate the requested version against any dependencies.
  
  @param {String} packageId
    The package id to look up

  @param {String} vers
    The expected version.  If null, then return the newest version for the 
    package.
    
  @param {String} Canonical packageId or null
*/
Package.prototype.canonicalPackageId = function(packageId, vers) {
  if ((packageId === this.get('name')) && 
      semver.compatible(vers, this.get('version'))) {
      return this.id;
  }
  return null;
};

/**
  Returns the receiver or an instance of a nested package if it matches the
  canonicalId passed here.  This method will only be called with a canonicalId
  returned from a previous call to Package#canonicalPackageId.
  
  If the package identified by the canonicalId is not available locally for
  some reason, return null.
  
  @param {String} canonicalId 
    The canonical packageId.
    
  @returns {Package} a package instance or null
*/
Package.prototype.packageFor = function(canonicalId) {
  if (canonicalId === this.id) return this;
  return null;
};

/**
  Verifies that the package identified by the passed canonical id is available
  locally and ready for use.  If it is not available, this method should 
  attempt to download the package from a remote source.
  
  Invokes the `done` callback when complete.
  
  If for some reason you cannot download and install the package you should
  invoke the callback with an error object describing the reason.  There are
  a number of standard errors defined on Package such as NotFound.
  
  @param {String} canonicalId
    The canonical packageId
    
  @param {Function} done
    Callback to invoke with result.  Pass an error object if the package 
    could not be loaded for some reason.  Otherwise invoke with no params
    
  @returns {void}
*/
Package.prototype.ensurePackage = function(canonicalId, done) {
  if (canonicalId === this.id) return done();
  else return done(new NotFound(canonicalId, this));
};

/**
  Returns all packages in the package including the package itself and any 
  nested packages.  Default just returns self.
*/
Package.prototype.catalogPackages = function() {
  return [this];
};

// ..........................................................
// Package Module Loading
// 

/**
  Detects whether the moduleId exists in the current package.
  
  @param {String} moduleId
    The moduleId to check
    
  @returns {Boolean} true if the module exists
*/
Package.prototype.exists = function(moduleId) {
  return !!(this.factories && this.factories[moduleId]);
};

/**
  Returns a Factory object for the passed moduleId or null if no matching
  factory could be found.
  
  @param {String} moduleId
    The moduleId to check
    
  @returns {Factory} factory object
*/
Package.prototype.load = function(moduleId) {
  return this.factories ? this.factories[moduleId] : null;
};

// ..........................................................
// LOADER
// 

// potentially optimize to avoid memory churn.
var joinPackageId = function joinPackageId(packageId, moduleId) {
  return packageId+':'+moduleId;
};

/**
  A loader is responsible for finding and loading factory functions.  The 
  primary purpose of the loader is to find packages and modules in those 
  packages.  The loader typically relies on one or more sources to actually
  find a particular package.
*/
var Loader = exports.extend(Object);
exports.Loader = Loader;

Loader.prototype.init = function(sources) {
  this.sources = sources || [];
  this.clear();
};

/**
  Clear caches in the loader causing future requests to go back to the 
  sources.
*/
Loader.prototype.clear = function() {
  this.factories = {};
  this.canonicalIds = {};
  this.packages ={};
  this.packageSources = {};
  this.canonicalPackageIds = {};
};

/**
  The default package.  This can be replaced but normally it is empty, meaning
  it will never match a module.
  
  @property {Package}
*/
Loader.prototype.defaultPackage = new Package('default', { 
  name: "default" 
});

/**
  The anonymous package.  This can be used when loading files outside of a 
  package.
  
  @property {Package}
*/
Loader.prototype.anonymousPackage = new Package('(anonymous)', { 
  name: "(anonymous)"
});


/**

  Discovers the canonical id for a module.  A canonicalId is a valid URN that
  can be used to uniquely identify a module.
  that looks like:
  
    ::packageId:moduleId
    
  For example:
  
    ::sproutcore-runtime/1.2.0:mixins/enumerable
  
  Canonical Ids are discovered according to the following algorithm:
  
  1.  If you pass in an already canonicalId, return it
  2.  If you pass in a relative moduleId, it will be expanded and attached
      to the workingPackage.
  3.  If you pass in a moduleId with a packageId embedded, lookup the latest
      version of the package that is compatible with the passed workingPackage
  4.  If you pass a moduleId with no packageId embedded, then first look
      for the module on the workingPackage.  
  5.  If not found there, look for a packageId with the same name.  If that is 
      found, return either packageId:index or packageId:packageId as module.  
  6.  Otherwise, assume it is part of the default package. 

  @param {String} moduleId
    The moduleId to lookup.  May be a canonicalId, packageId:moduleId, 
    absolute moduleId or relative moduleId
    
  @param {String} curModuleId
    Optional.  moduleId of the module requesting the lookup.  Only needed if
    the moduleId param might be relative.
    
  @param {Package} workingPackage
    The working package making the request.  When searching for a package,
    only use packages that are compatible with the workingPackage.
    
    This parameter is also optional, though if you omit it, this method 
    assumes the anonymousPackage.
    
  @returns {void}
*/
Loader.prototype.canonical = function(moduleId, curModuleId, workingPackage) {
  
  var cache, cacheId, idx, packageId, canonicalId, pkg, ret; 
  
  // NORMALIZE PARAMS
  // normalize params - curModuleId can be omitted (though relative ids won't)
  // work
  if (curModuleId && (T_STRING !== typeof curModuleId)) {
    workingPackage = curModuleId;
    curModuleId = null;
  }
  
  // return immediately if already canonical
  if (isCanonicalId(moduleId)) return moduleId;
  
  // if no workingPackage, assume anonymous
  if (!workingPackage) workingPackage = this.anonymousPackage;
  
  // Resolve moduleId - may return canonical
  moduleId = this._resolve(moduleId, curModuleId, workingPackage);
  if (isCanonicalId(moduleId)) return moduleId;
  
  // then lookup in cache
  cacheId = workingPackage ? workingPackage.id : '(null)';
  cache = this.canonicalIds;
  if (!cache) cache = this.canonicalIds = {};
  if (!cache[cacheId]) cache[cacheId] = {};
  cache = cache[cacheId];
  if (cache[moduleId]) return cache[moduleId];
  cacheId = moduleId; // save for later

  // Not Found in Cache.  Do a lookup
  idx = moduleId.indexOf(':');
  if (idx>=0) {
    packageId = moduleId.slice(0,idx);
    moduleId  = moduleId.slice(idx+1);
    if (moduleId[0]==='/') {
      throw new Error('Absolute path not allowed with packageId');
    }
  }

  // if packageId is provided, just resolve packageId to a canonicalId
  ret = null;
  if (packageId && (packageId.length>0)) {
    canonicalId = this._canonicalPackageId(packageId, null, workingPackage);
    if (canonicalId) ret = joinPackageId(canonicalId, moduleId);

  // no packageId is provided, we'll need to do a little more searching
  } else {

    // first look in workingPackage for match...
    if (workingPackage && workingPackage.exists(moduleId)) {
      ret = joinPackageId(workingPackage.id, moduleId);
      
    // not in working package, look for packageId:index or
    // packageId:packageId
    } else {
      canonicalId = this._canonicalPackageId(moduleId, null, workingPackage);
      if (canonicalId) pkg = this._packageFor(canonicalId, workingPackage);
      if (pkg) {
        if (pkg.exists('index')) ret = joinPackageId(pkg.id, 'index');
        else if (pkg.exists(moduleId)) ret = joinPackageId(pkg.id,moduleId);
      }
    }
    
    // not in working package and isn't a package itself, assume default
    // package.  If there is no defaultPackage, return with the working
    // package.  This will fail but at least the error will be more 
    // helpful
    if (!ret) {
      if (this.defaultPackage) packageId = this.defaultPackage.id;
      else if (this.workingPackage) packageId = this.workingPackage.id;
      else if (this.anonymousPackage) packageId = this.anonymousPackage.id;
      else return packageId = null;
      
      if (packageId) ret = joinPackageId(packageId, moduleId);
    }
  }

  // save to cache and return
  cache[cacheId] = ret;
  return ret ;
};
  
/**

  Loads a factory for the named canonical module Id.  If you did not obtain
  the canonical module id through the loader's canonical() method, then you
  must also pass a workingPackage property so that the loader can locate the
  package that owns the module.
  
  The returns factory function can be used to actually generate a module.
  
  @param {String} canonicalId
    A canonical module id
    
  @param {Package} workingPackage
    Optional working package.  Only required if you pass in a canonical id
    that you did not obtain from the loader's canonical() method.
    
  @returns {void}
  
*/
Loader.prototype.load = function(canonicalId, workingPackage, sandbox) {

  var cache, ret, idx, packageId, moduleId, pkg;
  
  if (!workingPackage) workingPackage = this.anonymousPackage;
  
  cache = this.factories;
  if (!cache) cache = this.factories = {};
  if (cache[canonicalId]) return cache[canonicalId];

  // not in cache - load from package
  idx       = canonicalId.indexOf(':',2);
  packageId = canonicalId.slice(0,idx);
  moduleId  = canonicalId.slice(idx+1);

  pkg = this._packageFor(packageId, workingPackage);
  
//@if(debug)
  if (!pkg) DEBUG('Loader#load - '+packageId+' not found for '+moduleId);
//@endif

  if (!pkg) return null; // not found
  
  ret = pkg.load(moduleId, sandbox);
  cache[canonicalId] = ret;
  return ret ;
};

/**
  Returns a catalog of all known packages visible to the workingPackage.
  The catalog is simply an array of package objects in no particular order
*/
Loader.prototype.catalogPackages = function(workingPackage) {
  if (!workingPackage) workingPackage = this.anonymousPackage;
  var catalog = [], sources, idx, len, seen = {};
  if (this.defaultPackage) catalog.push(this.defaultPackage);
  
  // anonymous package is never visible unless it is working..
  //if (this.anonymousPackage) ret.push(this.anonymousPackage);

  // append any packages with versions that haven't been seen already
  var append = function(packages) {
    var idx, len, check, cur;
    
    if (!packages) return; // nothing to do
    len = packages.length;
    for(idx=0;idx<len;idx++) {
      cur = packages[idx];
      check = seen[cur.get('name')];
      if (!check) check = seen[cur.get('name')] = {};      
      if (!check[cur.get('version')]) {
        catalog.push(cur);
        check[cur.get('version')] = cur;
      }
    }
  };
  
  if (workingPackage) append(workingPackage.catalogPackages());

  sources = this.sources;
  len = sources.length;
  for(idx=0;idx<len;idx++) append(sources[idx].catalogPackages());
  
  seen = null; // no longer needed.
  return catalog;
};

/**
  Discovers the canonical id for a package.  A cnaonicalID is a URN that can
  be used to uniquely identify a package.  It looks like: 
  
    ::packageId
  
  for example:
  
    ::sproutcore-datastore/1.2.0/1ef3ab23ce23ff938

  If you need to perform some low-level operation on a package, this method
  is the best way to identify the package you want to work with specifically.
  
  ## Examples
  
  Find a compatible package named 'foo' in the current owner module:
  
      loader.canonicalPackage('foo', ownerPackage, function(err, pkg) {
        // process response
      });
      
  Find the package named 'foo', exactly version '1.0.0'.  This may return a
  packes nested in the ownerPackage:
  
      loader.canonicalPackage('foo', '=1.0.0', ownerPackage, function(err, pkg) {
        // process response
      });
  
  Find the latest version of 'foo' installed in the system - not specific to 
  any particular package
  
      loader.canonicalPackage('foo', loader.anonymousPackage, function(err, pkg) {
        // process result
      });
      
  @param {String|Package} packageId
    The packageId to load.  If you pass a package, the package itself will
    be returned.
    
  @param {String} vers 
    The required version.  Pass null or omit this parameter to use the latest
    version (compatible with the workingPackage).
    
  @param {Package} workingPackage
    The working package.  This method will search in this package first for
    nested packages.  It will also consult the workingPackage to determine 
    the required version if you don't name a version explicitly.
    
    You may pass null or omit this parameter, in which case the anonymous
    package will be used for context.
    
  @param {Function} done 
    Callback.  Invoked with an error and the loaded package.  If no matching
    package can be found, invoked with null for the package.

  @returns {void}
*/
Loader.prototype.canonicalPackageId = function(packageId, vers, workingPackage) {

  var idx;

  // fast path in case you pass in a package already
  if (packageId instanceof Package) return packageId.id;

  // fast path packageId is already canonical - slice of moduleId first
  if (isCanonicalId(packageId)) {
    idx = packageId.indexOf(':', 2);
    if (idx>=0) packageId = packageId.slice(0,idx);
    return packageId;
  }
  
  // normalize the params.  vers may be omitted
  if (vers && (T_STRING !== typeof vers)) {
    workingPackage = vers;
    vers = null;
  }  

  // must always have a package
  if (!workingPackage) workingPackage = this.anonymousPackage;
  
  // if packageId includes a moduleId, slice it off
  idx = packageId.indexOf(':');
  if (idx>=0) packageId = packageId.slice(0, idx);
  
  // now we can just pass onto internal primitive
  return this._canonicalPackageId(packageId, vers, workingPackage);
};


/**
  Primitive returns the package instance for the named canonicalId.  You can
  pass in a canonicalId for a package only or a package and module.  In either
  case, this method will only return the package instance itself.
  
  Note that to load a canonicalId that was not resolved through the 
  canonicalPackageId() or canonical() method, you will need to also pass in
  a workingPackage so the loader can find the package.
  
  @param {String} canonicalId
    The canonicalId to load a package for.  May contain only the packageId or
    a moduleId as well.
    
  @param {Package} workingPackage
    Optional workingPackage used to locate the package.  This is only needed
    if you request a canonicalId that you did not obtain through the 
    canonical*() methods on the loader.

  @returns {void}
*/
Loader.prototype.packageFor = function(canonicalId, workingPackage){

  if (!workingPackage) workingPackage = this.anonymousPackage;
  
  // remove moduleId
  var idx = canonicalId.indexOf(':', 2);
  if (idx>=0) canonicalId = canonicalId.slice(0, idx);

  return this._packageFor(canonicalId, workingPackage);
};

/**
  Verifies that the named canonicalId is ready for use, including any of its
  dependencies.  You can pass in either a canonical packageId only or a 
  moduleId.   In either case, this method will actually only check the package
  properties for dependency resolution since dependencies are not tracked for
  individual modules.
  
  @param {String} canonicalId
    The canonicalId to use for lookup
    
  @param 
*/
Loader.prototype.ready = function(canonicalId, workingPackage) {

  if (!workingPackage) workingPackage = this.anonymousPackage;
  
  // strip out moduleId
  var idx = canonicalId.indexOf(':', 2), 
      moduleId, pkg;
  
  if (idx >= 0) {
    moduleId    = canonicalId.slice(idx+1);
    canonicalId = canonicalId.slice(0, idx);
  }
  
  if (this._packageReady(canonicalId, workingPackage, {})) {
    pkg = this._packageFor(canonicalId, workingPackage);
    if (!pkg) return false;
    return !!pkg.exists(moduleId);
  } else return false;
  
};

/**
  Ensures the package that maps to the passed packageId/vers combo and all
  of its known dependencies are loaded and ready for use.  If anything is not
  loaded, it will load them also.  
  
  Invokes the passed callback when loading is complete.
  
  This method ends up calling ensurePackage() on one or more of its sources
  to get the actual packages to load.
  
  @param {String} packageId
    The packageID to load.  May be a packageId name or a canonical packageId
    
  @param {String} vers
    Optional version used to constrain the compatible package
    
  @param {Package} workingPackage
    Optional working package used to match the packageId.  If the package 
    might be nested you should always pass a workingPackage.  Default assumes
    anonymousPackage.
    
  @param {Function} done
    Callback invoked when package is loaded.  Passes an error if there was an
    error.  Otherwise no params.
    
  @returns {void}
*/
Loader.prototype.ensurePackage = function(packageId, vers, workingPackage, done) {

  // normalize params
  if (vers && (T_STRING !== typeof vers)) {
    done = workingPackage ;
    workingPackage = vers;
    vers = null;
  }

  if (workingPackage && (T_FUNCTION === typeof workingPackage)) {
    done = workingPackage;
    workingPackage = null;
  }
  
  if (!workingPackage) workingPackage = this.anonymousPackage;

  this._ensurePackage(packageId, vers, workingPackage, {}, done);
};

/**
  @private
  
  Primitive for ensurePackage().  Does no param normalization.  Called 
  recursively for dependencies.
*/
Loader.prototype._ensurePackage = function(packageId, vers, workingPackage, seen, done) {

  var loader = this, canonicalId, source;
  
  // find the canonicalId and source to ask to ensure...
  canonicalId = this._canonicalPackageId(packageId, vers, workingPackage);
  if (!canonicalId) {
    return done(new NotFound(packageId, workingPackage));
  }

  if (seen[canonicalId]) return done(); // success
  seen[canonicalId] = true;

  source = this._sourceForCanonicalPackageId(canonicalId, workingPackage);
  if (!source) {
    return done(new NotFound(canonicalId, workingPackage));
  }

  source.ensurePackage(canonicalId, function(err) {
    var pkg, deps, packageId, packageIds;

    if (err) return done(err);
    pkg = loader.packageFor(canonicalId, workingPackage);
    if (!pkg) {
      return done(new NotFound(canonicalId, workingPackage));
    }

    deps = pkg.get('dependencies');
    if (!deps) return done(); // nothing to do
    
    // map deps to array to we can process in parallel
    packageIds = [];
    for(packageId in deps) {
      if (!deps.hasOwnProperty(packageId)) continue;
      packageIds.push({ packageId: packageId, vers: deps[packageId] });
    }
    
    parallel(packageIds, function(info, done) {
      loader._ensurePackage(info.packageId, info.vers, pkg, seen, done);
    })(done);

  });
  
};

/**
  @private
  
  Discovers the canonical packageId for the named packageId, version and 
  working package.  This will also store in cache the source where you can
  locare and load the associated package, if needed.
  
  This primitive is used by all other package methods to resolve a package
  into a canonicalId that can be used to reference a specific package instance
  
  It does not perform any error checking on passed in parameters which is why
  it should never be called directly outside of the Loader itself.
  
  @param {String|Package} packageId
    The packageId to load.  If you pass a package, the package itself will
    be returned.
    
  @param {String} vers 
    The required version.  Pass null or omit this parameter to use the latest
    version (compatible with the workingPackage).
    
  @param {Package} workingPackage
    The working package.  This method will search in this package first for
    nested packages.  It will also consult the workingPackage to determine 
    the required version if you don't name a version explicitly.
    
  @returns {String}
*/
Loader.prototype._canonicalPackageId = function(packageId, vers, workingPackage) {

  // fast paths
  if (packageId instanceof Package) return packageId.id;
  if (isCanonicalId(packageId)) return packageId;
  if ((packageId === 'default') && this.defaultPackage) {
    return this.defaultPackage.id;
  }
  
  var cache = this.canonicalPackageIds,
      cacheId, sources, ret, idx, len, source;

  // use anonymousPackage if no workingPackage is provided
  if (!workingPackage) workingPackage = this.anonymousPackage;
  if (!workingPackage) throw new Error('working package is required');

  // if packageId is already canonical, vers must be null, otherwise lookup
  // vers in working package
  if (!vers) vers = workingPackage.requiredVersion(packageId);
  
  // look in cache...
  cacheId = workingPackage.id;
  if (!cache) cache = this.canonicalPackageIds = {};
  if (!cache[cacheId]) cache[cacheId] = {};
  cache = cache[cacheId];
  if (!cache[packageId]) cache[packageId] = {};
  cache = cache[packageId];
  if (cache[vers]) return cache[vers];

  sources = this.sources;

  // first, ask the workingPackage  
  ret = workingPackage.canonicalPackageId(packageId, vers);
  source = workingPackage;
  

  // not found - make sure there isn't another incompatible version in 
  // workingPackage.  nested packages superceed all other packages so if there
  // is an incompatible nested version we need to throw an error.
  if (!ret) {
    ret = workingPackage.canonicalPackageId(packageId, null);
    if (ret) {
      throw new Error(
        workingPackage.get('name')+" contains an incompatible nested"+
        " package "+packageId+" (expected: "+vers+")");
    }
  }
  
    
  // next, if not found in the workingPackage, then ask each of our 
  // sources in turn until a match is found.  When found, return
  if (!ret && sources) {
    len = sources.length;
    for(idx=0;!ret && (idx<len);idx++) {
      source = sources[idx];
      ret = source.canonicalPackageId(packageId, vers);
    }
  }
  
  if (ret) this._cachePackageSource(ret, workingPackage, source);
  cache[vers] = ret;
  return ret ;
};

// add a function to the cache that will immediately return the source
Loader.prototype._cachePackageSource = function(id, workingPackage, source) {
  var scache = this.packageSources, pkgId = workingPackage.id;
  
  if (!scache) scache = this.packageSources = {};
  if (!scache[pkgId]) scache[pkgId] = {};
  scache = scache[pkgId];
  scache[id] = source;
};

/**
  Looks up the source for the named canonicalId in the cache.  Returns null
  if no match is found.
*/
Loader.prototype._sourceForCanonicalPackageId = function(canonicalId, workingPackage) {
  var scache = this.packageSources, 
      wpackageId = workingPackage.id, 
      pkg, sources, len, idx, ret;

  if (!scache) scache = this.packageSources = {};
  if (!scache[wpackageId]) scache[wpackageId] = {};
  scache = scache[wpackageId];
  if (scache[canonicalId]) return scache[canonicalId];
  
  sources = this.sources;
    
  // first, ask the workingPackage to find any matching package (since it 
  // can only have one version).  Then check the returned version against 
  // the expected version.  
  if (workingPackage) {
    pkg = workingPackage.packageFor(canonicalId);
    if (pkg) ret = workingPackage; 
  }
  
  if (!ret && sources) {
    len = sources.length;
    for(idx=0;!ret && (idx<len); idx++) {
      ret = sources[idx];
      if (!ret.packageFor(canonicalId)) ret = null;
    }
  }
  
  scache[canonicalId] = ret;
  return ret ;
};

/**
  Primitive actually loads a package from a canonicalId.  Throws an exception
  if source for package is not already in cache.  Also caches loaded package.
*/
Loader.prototype._packageFor = function(canonicalId, workingPackage) {
  var cache, source, ret;

  // special case - if default packageId just get the default package.
  if (this.defaultPackage && (canonicalId === this.defaultPackage.id)) {
    return this.defaultPackage;
  }
  
  // try to resolve out of cache
  cache = this.packages;
  if (!cache) cache = this.packages = {};
  if (cache[canonicalId]) return cache[canonicalId];

  source = this._sourceForCanonicalPackageId(canonicalId, workingPackage);
  if (source) ret = source.packageFor(canonicalId);
  cache[canonicalId] = ret;
  return ret ;
};

/**
  Primitive simply checks to see if the named canonicalId is ready or not
  along with any dependencies
*/
Loader.prototype._packageReady = function(canonicalId, workingPackage, seen) {
  var cache = this.packages, pkg, deps, packageId, vers;

  // if we've already seen this package, exit immediately
  if (seen[canonicalId]) return true;
  seen[canonicalId] = true;
  
  // first try to find the package for the receiver
  pkg = this._packageFor(canonicalId, workingPackage);
  if (!pkg) return false; // nothing to do.

  // look at dependencies. make sure they are also loaded
  deps = pkg.get('dependencies');
  for(packageId in deps) {
    if (!deps.hasOwnProperty(packageId)) continue;
    vers = deps[packageId];
    canonicalId = this._canonicalPackageId(packageId, vers, pkg);
    if (!canonicalId) return false;
    return this._packageReady(canonicalId, pkg, seen);
  }
  
  return true;
};

/**
  Take a relative or fully qualified module name as well as an optional
  base module Id name and returns a fully qualified module name.  If you 
  pass a relative module name and no baseId, throws an exception.

  Any embedded package name will remain in-tact.

  resolve('foo', 'bar', 'my_package') => 'foo'
  resolve('./foo', 'bar/baz', 'my_package') => 'my_package:bar/foo'
  resolve('/foo/bar/baz', 'bar/baz', 'my_package') => 'default:/foo/bar/baz'
  resolve('foo/../bar', 'baz', 'my_package') => 'foo/bar'
  resolve('your_package:foo', 'baz', 'my_package') => 'your_package:foo'

  If the returned id does not include a packageId then the canonical() 
  method will attempt to resolve the ID by searching the default package, 
  then the current package, then looking for a package by the same name.

  @param {String} moduleId relative or fully qualified module id
  @param {String} baseId fully qualified base id
  @returns {String} fully qualified name
*/
Loader.prototype._resolve = function(moduleId, curModuleId, pkg){
  var path, len, idx, part, parts, packageId, err;

  // if id does not contain a packageId and it starts with a / then 
  // return with anonymous package id.
  if (moduleId[0]==='/' && moduleId.indexOf(':')<0) {
    return this.anonymousPackage.id + ':' + moduleId;
  }

  // contains relative components?
  if (moduleId.match(/(^\.\.?\/)|(\/\.\.?\/)|(\/\.\.?\/?$)/)) {

    // if we have a packageId embedded, get that first
    if ((idx=moduleId.indexOf(':'))>=0) {
      packageId = moduleId.slice(0,idx);
      moduleId  = moduleId.slice(idx+1);
      path      = []; // path must always be absolute.

    // if no package ID, then use baseId if first component is . or ..
    } else if (moduleId.match(/^\.\.?\//)) {
      if (!curModuleId) {
        throw new Error("id required to resolve relative id: "+moduleId);
      }

      // if base moduleId contains a packageId return an error
      if (curModuleId.indexOf(':')>=0) {
        throw new Error("current moduleId cannot contain packageId");
      }
        
      // use the pkg.id (which will be canonical)
      if (pkg) packageId = pkg.id;

      // work from current moduleId as base.  Ignore current module name
      path = curModuleId.split('/');
      path.pop(); 

    } else path = [];

    // iterate through path components and update path
    parts = moduleId.split('/');
    len   = parts.length;
    for(idx=0;idx<len;idx++) {
      part = parts[idx];
      if (part === '..') {
        if (path.length<1) throw new Error("invalid path: "+moduleId);
        path.pop();

      } else if (part !== '.') path.push(part);
    }

    moduleId = path.join('/');
    if (packageId) moduleId = joinPackageId(packageId, moduleId);
  }

  return moduleId ;
};


// ..........................................................
// SANDBOX
// 

/**
  A Sandbox maintains a cache of instantiated modules.  Whenever a modules 
  is instantiated, it will always be owned by a single sandbox.  This way
  when you required the same module more than once, you will always get the
  same module.
  
  Each sandbox is owned by a single loader, which is responsible for providing
  the sandbox with Factory objects to instantiate new modules.
  
  A sandbox can also have a 'main' module which can be used as a primary
  entry point for finding other related modules.
  
*/
var Sandbox = exports.extend(Object);
exports.Sandbox = Sandbox;

Sandbox.prototype.init = function(loader, env, args, mainModuleId) {
  this.loader = loader;
  this.env    = env;
  this.args   = args;
  if (mainModuleId) this.main(mainModuleId);

  this.clear();
};

Sandbox.prototype.catalogPackages = function(workingPackage) {
  return this.loader.catalogPackages(workingPackage);
};

Sandbox.prototype.createRequire = function(module) {
  
  var sandbox = this,
      curId   = module.id,
      curPkg  = module.ownerPackage,
      reqd;
      
  // basic synchronous require
  var req = function(moduleId, packageId) {
    if (packageId && moduleId.indexOf(':')<0) {
      if (packageId.isPackage) packageId = packageId.id;
      moduleId = packageId+':'+moduleId;
    }
    return sandbox.require(moduleId, curId, curPkg);
  };
  reqd = req.displayName = (curId||'(unknown)')+'#require';

  // expose any native require.  Mostly used by seed
  req.nativeRequire = sandbox.nativeRequire;
  
  // async version - packageId is optional
  req.ensure = function(moduleIds, done) {
    // always normalize moduleId to an array
    if (!isArray(moduleIds)) {
      moduleIds = Array.prototype.slice.call(arguments);
      done = moduleIds.pop();
    }

    // ensure each module is loaded 
    parallel(moduleIds, function(moduleId, done) {
      sandbox.ensure(moduleId, curId, curPkg, done);

    })(function(err) { 
      if (err) return done(err);
      if (done.length<=1) return done(); // don't lookup modules themselves
      
      done(null, map(moduleIds, function(moduleId) {
        return sandbox.require(moduleId, curId, curPkg);
      }));
    });
  };
  req.ensure.displayName = reqd+'.ensure';
  
  // return true if the passed module or modules are ready for use right now
  // this is like calling ensure() but it won't load anything that isn't 
  // actually ready
  req.ready = function(moduleIds) {
    var idx, len ;
    
    // always normalize moduleId to an array
    if (!isArray(moduleIds)) {
      moduleIds = Array.prototype.slice.call(arguments);
    }

    len = moduleIds.length;
    for(idx=0;idx<len;idx++) {
      if (!sandbox.ready(moduleIds[idx], curId, curPkg)) return false;
    }
    return true;
  };
  req.ready.displayName = reqd+'.ready';

  /**
    Returns the package for the named packageId and optional version from
    the perspective of the current package.  This invokes a similar method 
    on the sandbox, which will pass it along to the loader, though a secure
    sandbox may actually wrap the responses as well.
    
    This method only acts on packages available locally.  To get possibly
    remote packages, you must first call require.ensurePackage() to ensure
    the package and its dependencies have been loaded.
    
    @param {String} packageId
      The packageId to load
      
    @param {String} vers
      Optional version
      
    @returns {Package} the package or null
  */
  req.packageFor = function(packageId, vers) {
    return sandbox.packageFor(packageId, vers, curPkg);
  };
  req.packageFor.displayName = reqd+'.packageFor';
  
  /**
    Asynchronously loads the named package and any dependencies if needed.
    This is only required if you suspect your package may not be available 
    locally.  If your callback accepts only one parameter, then the packages
    will be loaded but not instantiated. The first parameter is always an 
    error object or null.
    
    If your callback accepts more than one parameter, then the packages will
    be instantiated and passed to your callback as well.
  
    If a package cannot be loaded for some reason, your callback will be 
    invoked with an error of type NotFound.
    
    @param {String} packageId
      The packageId to load
    
    @param {String} vers
      Optional version

    @param {Function} done
      Callback invoked once packages have loaded.
    
    @returns {Package} the package or null
  */
  req.ensurePackage = function(packageId, vers, done) {
    sandbox.ensurePackage(packageId, vers, curPkg, function(err) {
      if (err) return done(err);
      if (done.length <= 1) return done();
      done(null, sandbox.packageFor(packageId, vers, curPkg));
    });
  };
  req.ensurePackage.displayName = reqd+'.ensurePackage.displayName';
  
  /**
    Returns a catalog of all packages visible to the current module without
    any additional loading.  This may be an expensive operation; you should
    only use it when necessary to detect plugins, etc.
  */
  req.catalogPackages = function() {
    return sandbox.catalogPackages(curPkg);
  };
  
  // mark main module in sandbox
  req.main = sandbox.main();
  req.env  = sandbox.env;
  req.args = sandbox.args;
  req.sandbox = sandbox;
  req.loader  = sandbox.loader;
  
  req.isTiki = true; // walk like a duck
  
  return req;
};

// ..........................................................
// RESOLVING MODULE IDS
// 

Sandbox.prototype.Module = Module;

/**
  Retrieves a module object for the passed moduleId.  You can also pass 
  optional package information, including an optional curModuleId and a
  workingPackage.  You MUST pass at least a workingPackage.
  
  The returned module object represents the module but the module exports may
  not yet be instantiated.  Use require() to retrieve the module exports.
  
  @param {String} moduleId
    The module id to lookup.  Should include a nested packageId
    
  @param {String} curModuleId
    Optional current module id to resolve relative modules.
    
  @param {Package} workingPackage
    The working package making the request
    
  @returns {void}
*/
Sandbox.prototype.module = function(moduleId, curModuleId, workingPackage) {

  var ret, canonicalId, cache, packageId, idx, pkg;
  
  // assume canonicalId will normalize params
  canonicalId = this.loader.canonical(moduleId, curModuleId, workingPackage);
  if (!canonicalId) throw(new NotFound(moduleId, workingPackage));

  // get out of cache first
  cache = this.modules;
  if (!cache) cache = this.modules = {};
  if (ret = cache[canonicalId]) return ret;
  
  // not in cache...add it
  idx       = canonicalId.indexOf(':', 2);
  moduleId  = canonicalId.slice(idx+1);
  packageId = canonicalId.slice(0, idx);
  pkg = this.loader.packageFor(packageId, workingPackage);
  if (!pkg) throw(new NotFound(packageId, workingPackage));
  ret = cache[canonicalId] = new this.Module(moduleId, pkg, this);
  
  return ret ;
};

/**
  Returns the main module for the sandbox.  This should only be called 
  from the factory when it is setting main on itself.  Otherwise the main
  module may not exist yet.
  
  Note that the mainModule will be resolved using the anonymousPackage so
  the named module must be visible from there.
*/
Sandbox.prototype.main = function(newMainModuleId, workingPackage) {
  if (newMainModuleId !== undefined) {
    this._mainModule = null;
    this._mainModuleId = newMainModuleId;
    this._mainModuleWorkingPackage = workingPackage;
    return this;
    
  } else {
    if (!this._mainModule && this._mainModuleId) {
      workingPackage = this._mainModuleWorkingPackage;
      this._mainModule = this.module(this._mainModuleId, workingPackage);
    }
    return this._mainModule;
  }
};

/**
  Returns the exports for the named module.

  @param {String} moduleId
    The module id to lookup.  Should include a nested packageId
  
  @param {String} curModuleId
    Optional current module id to resolve relative modules.
  
  @param {Package} workingPackage
    The working package making the request
  
  @param {Function} done
    Callback to invoke when the module has been retrieved.
  
  @returns {void}
*/
Sandbox.prototype.require = function(moduleId, curModuleId, workingPackage) {

  var ret, canonicalId, cache, used, factory, module, exp;
  
  // assume canonical() will normalize params
  canonicalId = this.loader.canonical(moduleId, curModuleId, workingPackage);
  if (!canonicalId) throw new NotFound(moduleId, workingPackage);

  // return out of cache
  cache = this.exports; used  = this.usedExports;
  if (!cache) cache = this.exports = {};
  if (!used)  used  = this.usedExports = {};
  if (ret = cache[canonicalId]) {
    ret = ret.exports;
    if (!used[canonicalId]) used[canonicalId] = ret;
    return ret;
  }

  // not in cache, get factory, module, and run function...
  factory = this.loader.load(canonicalId, workingPackage, this);
  if (!factory) throw(new NotFound(canonicalId, workingPackage));

  module  = this.module(canonicalId, workingPackage);
  cache[canonicalId] = module;

  exp = factory.call(this, module);
  module.exports = exp;
  
  // check for cyclical refs
  if (used[canonicalId] && (used[canonicalId] !== exp)) {
    throw new Error("cyclical requires() in "+canonicalId);
  }

  return exp;
};

/**
  Returns true if the given module is ready. This checks the local cache 
  first then hands this off to the loader.
*/
Sandbox.prototype.ready = function(moduleId, curModuleId, workingPackage) {
  // assume canonicalPackageId() will normalize params
  var id = this.loader.canonical(moduleId, curModuleId, workingPackage);
  return id ? this.loader.ready(id) : false;
};

/**
  Ensures the passed moduleId and all of its dependencies are available in
  the local domain.  If any dependencies are not available locally, attempts
  to retrieve them from a remote server.
  
  You don't usually call this method directly.  Instead you should call the 
  require.ensure() method defined on a module's local require() method.
  
*/
Sandbox.prototype.ensure = function(moduleId, curModuleId, workingPackage, done) {

  var id, loader, packageId, idx;
  
  // normalize params so that done is in right place
  if (curModuleId && (T_STRING !== typeof curModuleId)) {
    done = workingPackage;
    workingPackage = curModuleId;
    curModuleId = null;
  }
  
  if (workingPackage && (T_FUNCTION === typeof workingPackage)) {
    done = workingPackage ;
    workingPackage = null;
  }
  
  id = this.loader.canonical(moduleId, curModuleId, workingPackage);
  if (!id) return done(new NotFound(moduleId, workingPackage));
  
  idx       = id.indexOf(':', 2);
  moduleId  = id.slice(idx+1);
  packageId = id.slice(0, idx);
  loader    = this.loader;

  loader.ensurePackage(packageId, workingPackage, function(err) {
    if (err) return done(err);
    var pkg = loader.packageFor(packageId, workingPackage);
    if (!pkg.exists(moduleId)) done(new NotFound(moduleId, pkg));
    else done(); // all clear
  });
};

/**
  TODO: document
*/
Sandbox.prototype.packageFor = function(packageId, vers, workingPackage) {

  // assume canonicalPackageId() will normalize params
  var id = this.loader.canonicalPackageId(packageId, vers, workingPackage);
  if (!id) return null;
  return this.loader.packageFor(id);
};

/** 
  TODO: document
*/
Sandbox.prototype.ensurePackage = function(packageId, vers, workingPackage, done) {

  // normalize params so that done is in right place
  if (vers && (T_STRING !== typeof vers)) {
    done = workingPackage;
    workingPackage = vers;
    vers = null;
  }
  
  if (workingPackage && (T_FUNCTION === typeof workingPackage)) {
    done = workingPackage ;
    workingPackage = null;
  }
  
  var id = this.loader.canonicalPackageId(packageId, vers, workingPackage);
  if (!id) return done(new NotFound(packageId, workingPackage));
  this.loader.ensurePackage(id, done);
};


/**
  Returns the path or URL to a resource in the named package. 
*/
Sandbox.prototype.resource = function(resourceId, moduleId, ownerPackage) {
  if (!ownerPackage.resource) return null;
  return ownerPackage.resource(resourceId, moduleId);
};

/**
  Clears the sandbox.  requiring modules will cause them to be reinstantied
*/
Sandbox.prototype.clear = function() {
  this.exports = {};
  this.modules = {};
  this.usedExports = {};
  return this;
};

// ..........................................................
// BROWSER
// 

// Implements a default loader source for use in the browser.  This object
// should also be set as the "require" global on the browser to allow for
// module registrations

var Browser = exports.extend(Object);
exports.Browser = Browser;

Browser.prototype.init = function() {
  this._ready  = {};
  this._unload = {};
  
  this.clear();
};

/**
  Reset the browser caches.  This would require all packages and modules 
  to register themselves.  You should also clear the associated loader and
  sandbox if you use this.
*/
Browser.prototype.clear = function() {
  this.packageInfoByName = {}; // stores package info sorted by name/version
  this.packageInfoById   = {}; // stores package info sorted by id
  this.packages    = {}; // instantiated packages
  this.factories   = {}; // registered module factories by id

  this.stylesheetActions = {}; // resolvable stylesheet load actions
  this.scriptActions     = {}; // resolvable script actions
  this.ensureActions     = {}; // resolvable package actions
};

/**
  Configures a basic sandbox environment based on the browser.  Now you can
  register and require from it.
  
  @returns {Browser} new instance
*/
Browser.start = function(env, args, queue) {
  // build new chain of objects and setup require.
  var browser, len, idx, action;
  
  browser         = new Browser();
  browser.loader  = new Loader([browser]);
  browser.sandbox = new Sandbox(browser.loader, env, args);
  browser.queue   = queue;

  var mod = { 
    id: 'index', 
    ownerPackage: browser.loader.anonymousPackage 
  };

  browser.require = browser.sandbox.createRequire(mod);
  // TODO: amend standard CommonJS methods for loading modules when they
  // are standardized
  
  return browser;
};

Browser.prototype.replay = function() {
  var queue = this.queue,
      len   = queue ? queue.length : 0,
      idx, action;
      
  this.queue = null;
  for(idx=0;idx<len;idx++) {
    action = queue[idx];
    this[action.m].apply(this, action.a);
  }
  
  return this;
};

// safe - in place of preamble start()
Browser.prototype.start = function() {
  return this;
};

/**
  Makes all dependencies of the passed canonical packageId global.  Used
  for backwards compatibility with non-CommonJS libraries.
*/
Browser.prototype.global = function(canonicalId) {
  if (!domAvailable && !xhrAvailable) return this;  // don't work out of brsr
  var GLOBAL = (function() { return this; })();
  
  var globals, pkg, deps, packageId, exports, keys, key, idx, len;
  
  globals = this.globals;
  if (!globals) globals = this.globals = {};

  pkg = this.packageFor(canonicalId);
  if (!pkg) throw new Error(canonicalId+' package not found');
  
  deps = pkg.get('dependencies');
  if (!deps) return this; // nothing to do
  
  for(packageId in deps) {
    if (!deps.hasOwnProperty(packageId)) continue;
    canonicalId  = this.loader.canonical(packageId, pkg);
    if (globals[canonicalId]) continue;
    globals[canonicalId] = true;
    
    // some cases a dependency refers to a package that is itself not 
    // using modules.  In this case just ignore
    if (!this.sandbox.ready(packageId, pkg)) continue;
    
    exports = this.sandbox.require(packageId, pkg);
    if (keys = exports.__globals__) {
      len = keys.length;
      for(idx=0;idx<len;idx++) {
        key = keys[idx];
        GLOBAL[key] = exports[key];
      }

    // no __globals__ key is defined so just iterate through any exported
    // properties. this should actually be the more common case
    } else {
      for(key in exports) {
        if (!exports.hasOwnProperty(key)) continue;
        GLOBAL[key] = exports[key];
      }
    }
    
  }

  return this;
};

// ..........................................................
// Ready & Unload Handlers
// 

var buildInvocation = function(args) {
  var context, method;
  
  if (args.length === 1) {
    context = null;
    method  = args[0];
    args = Array.prototype.slice.call(args, 1);
  } else {
    context = args[0];
    method  = args[1];
    args    = Array.prototype.slice.call(args, 2);
  }

  return { target: context, method: method, args: args };
};

var queueListener = function(base, queueName, args) {
  if (!base[queueName]) base[queueName] = [];
  base[queueName].push(buildInvocation(args));
};

/**
  Invoke the passed callback when the document is ready.  You can pass 
  either an object/function or a moduleId and property name plus additional
  arguments.
*/
Browser.prototype.addReadyListener = function(context, method) {
  if (this._ready && this._ready.isReady) {
    this._invoke(buildInvocation(arguments));
  } else {
    this._setupReadyListener();
    queueListener(this._ready, 'queue', arguments);
  }
};

/**
  Invoke the passed callback just after any ready listeners have fired but
  just before the main moduleId is required.  This is primarily provided as 
  a way for legacy environments to hook in their own main function.
*/
Browser.prototype.addMainListener = function(context, method) {
  if (this._ready && this._ready.isReady) {
    this._invoke(buildInvocation(arguments));
  } else {
    this._setupReadyListener();
    queueListener(this._ready, 'mqueue', arguments);
  }
};

/**
  Invoke the passed callback when the browser is about to unload.
*/
Browser.prototype.addUnloadListener = function(context, method) {
  if (this._unload && this._unload.isUnloading) {
    this._invoke(buildInvocation(arguments));
  } else {
    this._setupUnloadListener();
    queueListener(this._unload, 'queue', arguments);
  }
};


Browser.prototype._invoke = function(inv) {
  var target = inv.target, method = inv.method;
  if (T_STRING === typeof target) target = this.require(target);
  if (T_STRING === typeof method) method = target[method];
  if (method) method.apply(target, inv.args);
  inv.target = inv.method = inv.args = null;
};

Browser.prototype._setupReadyListener = function() {
  if (this._ready.setup) return this;
  this._ready.setup =true;
  
  var ready = this._ready, source = this, fire;
  
  fire = function() {
    if (ready.isReady) return;
    ready.isReady = true;
    
    // first cleanup any listeners so they don't fire again
    if (ready.cleanup) ready.cleanup();
    ready.cleanup = null;
    
    var q, len, idx;
    
    q = ready.queue;
    len = q ? q.length : 0;
    ready.queue = null;
    for(idx=0;idx<len;idx++) source._invoke(q[idx]);
    
    q = ready.mqueue;
    len = q ? q.length : 0 ;
    ready.mqueue = null;
    for(idx=0;idx<len;idx++) source._invoke(q[idx]);

    source._runMain(); // get main module.
  };
      
  // always listen for onready event - detect based on platform
  // those code is derived from jquery 1.3.1
  // server-side JS
  if (T_UNDEFINED === typeof document) {
    // TODO: handler server-side JS cases here

  // Mozilla, Opera, webkit nightlies
  } else if (document.addEventListener) {

    // cleanup handler to be called whenever any registered listener fires
    // should prevent additional listeners from firing
    ready.cleanup = function() {
      document.removeEventListener('DOMContentLoaded', fire, false);
      document.removeEventListener('load', fire, false);
    };

    // register listeners
    document.addEventListener('DOMContentLoaded', fire, false);
    document.addEventListener('load', fire, false);

  // IE
  } else if (document.attachEvent) {

    // cleanup handler - should cleanup all registered listeners
    ready.cleanup = function() {
      document.detachEvent('onreadystatechange', fire);
      document.detachEvent('onload', fire);
      ready.ieHandler = null; // will stop the ieHandler from firing again
    };

    // listen for readystate and load events
    document.attachEvent('onreadystatechange', fire);
    document.attachEvent('onload', fire);

    // also if IE and no an iframe, continually check to see if the document 
    // is ready
    // NOTE: DO NOT CHANGE TO ===, FAILS IN IE.
    if ( document.documentElement.doScroll && window == window.top ) {
      ready.ieHandler = function() {

        // If IE is used, use the trick by Diego Perini
        // http://javascript.nwbox.com/IEContentLoaded/
        if (ready.ieHandler && !ready.isReady) {
          try {
            document.documentElement.doScroll("left");
          } catch( error ) {
            setTimeout( ready.ieHandler, 0 );
            return;
          }
        }

        // and execute any waiting functions
        fire();
      };

      ready.ieHandler();
    }

  }  
};

Browser._scheduleUnloadListener = function() {
  if (this._unload.setup) return this;
  this._unload.setup =true;
  
  var unload = this._unload, source = this, fire;

  unload.isUnloading = false;
  fire = function() { 
    if (unload.isUnloading) return;
    unload.isUnloading = true;
    
    if (unload.cleanup) unload.cleanup();
    unload.cleanup = null;
    
    var q = unload.queue,
        len = q ? q.length : 0,
        idx, inv;
        
    unload.queue = null;
    for(idx=0;idx<len;idx++) source._invoke(q[idx]);
  };

  if (T_UNDEFINED === typeof document) {
    // TODO: Handle server-side JS mode
    
  } else if (document.addEventListener) {
    unload.cleanup = function() {
      document.removeEventListener('unload', fire);
    };
    document.addEventListener('unload', fire, false);
    
  } else if (document.attachEvent) {
    unload.cleanup = function() {
      document.detachEvent('onunload', fire);
    };
    document.attachEvent('unload', fire);
  }
  
};

// ..........................................................
// Registration API
// 

/**
  Sets the main moduleId on the sandbox.  This module will be automatically
  required after all other ready and main handlers have run when the document
  is ready.
  
  @param {String} moduleId
    A moduleId with packageId included ideally.  Can be canonicalId.
    
  @returns {void}
*/
Browser.prototype.main = function(moduleId, method) {
  if (this.sandbox) this.sandbox.main(moduleId);
  this._setupReadyListener(); // make sure we listen for ready event
  this._main = { id: moduleId, method: method };
};

Browser.prototype._runMain = function() {
  if (!this._main) return ;
  
  var moduleId = this._main.id,
      method   = this._main.method,
      req      = this.require;
  
  if (!moduleId || !req) return ;
  this._main = null;

  // async load any main module dependencies if needed then require
  req.ensure(moduleId, function(err) {
    if (err) throw err;
    var exp = req(moduleId);
    if (T_STRING === typeof method) method = exp[method];
    if (method) method.call(exp);
  });
};


// creates a new action that will invoke the passed value then setup the
// resolve() method to wait on response
Browser.prototype._action  = function(action) {
  var ret;
  
  ret = once(function(done) {
    ret.resolve = function(err, val) {
      ret.resolve = null; // no more...
      done(err, val);
    };
    action(); 
  });
  return ret;
  
};

Browser.prototype._resolve = function(dict, key, value) {
  
  // for pushed content, just create the action function
  if (!dict[key]) dict[key] = function(done) { done(null, value); };
  
  // if a value already exists, call resolve if still valid
  else if (dict[key].resolve) dict[key].resolve(null, value);
  return this;
};

Browser.prototype._fail = function(dict, key, err) {
  if (dict[key].resolve) dict[key].resolve(err);
};

var T_SCRIPT     = 'script',
    T_STYLESHEET = 'stylesheet',
    T_RESOURCE   = 'resource';
    
/**
  Normalizes package info, expanding some compacted items out to full 
  info needed.
*/
Browser.prototype._normalize = function(def, packageId) {
  if (!isCanonicalId(packageId)) packageId = '::'+packageId;
  def.id = packageId;
  def.version = semver.normalize(def.version);
  def['tiki:external'] = !!def['tiki:external']; 
  def['tiki:private']  = !!def['tiki:private'];  // ditto

  // expand list of resources
  var base = def['tiki:base']; 
  if (def['tiki:resources']) {

    def['tiki:resources'] = map(def['tiki:resources'], function(item) {
      
      // expand a simple string into a default entry
      if (T_STRING === typeof item) {
        item = { 
          id: packageId+':'+item,
          name: item 
        };
      }

      // must have an item name or you can't lookup the resource
      if (!item.name) {
        throw new InvalidPackageDef(def, 'resources must have a name');
      }

      if (!item.id) {
        item.id = packageId+':'+item.name;
      }
      if (!isCanonicalId(item.id)) item.id = '::'+item.id;
      
      // assume type from ext if one is provided
      if (!item.type) {
        if (item.name.match(/\.js$/)) item.type = T_SCRIPT;
        else if (item.name.match(/\.css$/)) item.type = T_STYLESHEET;
        else item.type = T_RESOURCE;
      }
      
      if (!item.url) {
        if (base) item.url = base+'/'+item.name;
        else item.url = item.id+item.name;
      }
      
      return item;
    });
  }
   
  // always have a nested and dependencies hash, even if it is empty
  if (!def.dependencies) def.dependencies = {};

  var nested = def['tiki:nested'], key;
  if (nested) {
    for(key in nested) {
      if (!nested.hasOwnProperty(key)) continue;
      if (!isCanonicalId(nested[key])) nested[key] = '::'+nested[key];
    }
    
  } else def['tiki:nested'] = {};
  
  return def;
};

/**
  Register new package information.
*/
Browser.prototype.register = function(packageId, def) {
  var reg, replace, name, vers, idx = -1;
  
  // normalize some basics...
  def = this._normalize(def, packageId);
  packageId = def.id; // make sure to get normalized packageId

  // see if a pkg with same id is registered.  if so, replace it only if 
  // the new one is not external and the old one is
  reg = this.packageInfoById;
  if (!reg) reg = this.packageInfoById = {};
  if (reg[packageId]) {
    if (!reg[packageId]['tiki:external']) return this;
    replace = reg[packageId];
  }
  reg[packageId] = def;
  
  if (def.name) {
    name = def.name;
    vers = def.version;
    
    reg = this.packageInfoByName;
    if (!reg) reg = this.packageInfoByName = {};
    if (!reg[name]) reg[name] = {};
    reg = reg[name];
    
    // update list of packageIds matching version...
    if (!reg[vers] || (reg[vers].length<=1)) {
      reg[vers] = [def];
    } else {
      if (replace) idx = reg[vers].indexOf(replace);
      if (idx>=0) {
        reg[vers] = reg[vers].slice(0, idx).concat(reg[vers].slice(idx+1));
      }
      reg[vers].push(def);
    }
    
  }
  
  return this;
};

/**
  Main registration API for all modules.  Simply registers a module for later
  use by a package.
*/
Browser.prototype.module = function(key, def) {
  if (!isCanonicalId(key)) key = '::'+key;
  this.factories[key] = def;
  return this; 
};

/**
  Register a script that has loaded
*/
Browser.prototype.script = function(scriptId) {
  if (!isCanonicalId(scriptId)) scriptId = '::'+scriptId;
  this._resolve(this.scriptActions, scriptId, true);
};

/**
  Register a stylesheet that has loaded.
*/
Browser.prototype.stylesheet = function(stylesheetId) {
  if (!isCanonicalId(stylesheetId)) stylesheetId = '::'+stylesheetId;
  this._resolve(this.stylesheetActions, stylesheetId, true);
};

// ..........................................................
// Called by Loader
//

var domAvailable = T_UNDEFINED !== typeof document && document.createElement;
var xhrAvailable = T_UNDEFINED !== typeof XMLHttpRequest;

/**
  Whether to use XHR by default. If true, XHR is tried first to fetch script
  resources; script tag injection is only used as a fallback if XHR fails. If
  false (the default if the DOM is available), script tag injection is tried
  first, and XHR is used as the fallback.
*/
Browser.prototype.xhr = !domAvailable;

/**
  Whether to automatically wrap the fetched JavaScript in tiki.module() and
  tiki.script() calls. With this on, CommonJS modules will "just work" without
  preprocessing. Setting this to true requires, and implies, that XHR will be
  used to fetch the files.
*/
Browser.prototype.autowrap = false;

var findPublicPackageInfo = function(infos) {
  if (!infos) return null;
  
  var loc = infos.length;
  while(--loc>=0) {
    if (!infos[loc]['tiki:private']) return infos[loc];
  }
  return null;
};

/**
  Find the canonical package ID for the passed package ID and optional 
  version.  This will look through all the registered package infos, only
  searching those that are not private, but including external references.
*/
Browser.prototype.canonicalPackageId = function(packageId, vers) {
  var info = this.packageInfoByName[packageId],
      ret, cur, cvers, rvers;
  
  if (vers) vers = semver.normalize(vers);
  if (!info) return null; // not found
  
  // see if we have caught a lucky break
  if (info[vers] && (info[vers].length===1)) return info[vers][0].id;

  // need to search...
  for(cvers in info) {
    if (!info.hasOwnProperty(cvers)) continue;
    if (!semver.compatible(vers, cvers)) continue;
    if (!ret || (semver.compare(rvers, cvers)<0)) {
      ret = findPublicPackageInfo(info[cvers]);
      if (ret) rvers = cvers; 
    }
  }
  
  return ret ? ret.id : null;
};

// get package for canonicalId, instantiate if needed
Browser.prototype.packageFor = function(canonicalId) {
  var ret = this.packages[canonicalId];
  if (ret) return ret ;

  // instantiate if needed
  ret = this.packageInfoById[canonicalId];
  if (ret && !ret['tiki:external']) { // external refs can't be instantiated
    ret = new this.Package(canonicalId, ret, this);
    this.packages[canonicalId] = ret;
    return ret ;
  }

  return null ; // not found
};

/**
  Ensures the named canonical packageId and all of its dependent scripts are
  loaded.
*/
Browser.prototype.ensurePackage = function(canonicalId, done) {
  var action = this.ensureActions[canonicalId];
  if (action) return action(done); // add another listener
  
  // no action get - get the package info and start one.
  var info = this.packageInfoById[canonicalId];
  if (!info) {
    return done(new NotFound(canonicalId, 'browser package info'));
  }
  
  var source = this;
  
  action = once(function(done) {
    var cnt = 1, ready = false, cancelled;
    
    // invoked when an action finishes.  Will resolve this action
    // when all of them finish.
    var cleanup = function(err) {
      if (cancelled) return;
      if (err) {
        cancelled = true;
        return done(err);
      }
      
      cnt = cnt-1;
      if (cnt<=0 && ready) return done(null, info);
    };

    // proactively kick off any known packages.  If a dependent package
    // is not known here just skip it for now.  This is just an optimization
    // anyway.  The Loader will take care of ensuring all dependencies are
    // really met.
    var dependencies = info.dependencies,
        nested       = info['tiki:nested'],
        packageId, vers, depInfo, curId;

    for(packageId in dependencies) {
      if (!dependencies.hasOwnProperty(packageId)) continue;
      curId = nested[packageId];
      if (!curId) {
        vers = dependencies[packageId];
        curId = source.canonicalPackageId(packageId, vers);
      }
      
      if (curId && source.packageInfoById[canonicalId]) {
        cnt++;
        source.ensurePackage(curId, cleanup);
      }
    }
    
    // step through resources and kick off each script and stylesheet
    var resources = info['tiki:resources'], 
        lim = resources ? resources.length : 0,
        loc, rsrc;
    for(loc=0;loc<lim;loc++) {
      rsrc = resources[loc];
      if (rsrc.type === T_RESOURCE) continue;
      if (rsrc.type === T_SCRIPT) {
        cnt++;
        source.ensureScript(rsrc.id, rsrc.url, cleanup);
      } else if (rsrc.type === T_STYLESHEET) {
        cnt++;
        source.ensureStylesheet(rsrc.id, rsrc.url, cleanup);
      }
    }
      
    // done, set ready to true so that the final handler can fire
    ready = true;
    cleanup(); 
    
  });
  
  this.ensureActions[canonicalId] = action;
  action(done); // kick off
};

Browser.prototype.ensureScript = function(id, url, done) {
  var action = this.scriptActions[id];
  if (action) return action(done);
  
  var source = this;
  action = this._action(function() {
    source._loadScript(id, url);
  });
  
  this.scriptActions[id] = action;
  return action(done);
};

Browser.prototype.ensureStylesheet = function(id, url, done) {
  var action = this.stylesheetActions[id];
  if (action) return action(done);
  
  var source = this;
  action = this._action(function() {
    source._loadStylesheet(id, url);
  });

  this.stylesheetActions[id] = action;
  return action(done);
};

Browser.prototype._injectScript = function(id, url) {
  var body, el;

  body = document.body;
  el = document.createElement('script');
  el.src = url;
  body.appendChild(el);
  body = el = null;
};

Browser.prototype._xhrScript = function(id, url) {
  var autowrap = this.autowrap;

  var req = new XMLHttpRequest();
  req.open('GET', url, true);
  req.onreadystatechange = function(evt) {
    // Accept 200 or 0 for local file requests.
    if (req.readyState !== 4 || (req.status !== 200 && req.status !== 0)) {
      return;
    }

    var src = req.responseText;
    if (autowrap) {
      src = "tiki.module('" + id + "', function(require, exports, module) {" +
        src + "});" + "tiki.script('" + id + "');";
    }

    // Add a Firebug-style sourceURL parameter to help debugging.
    eval(src + "\n//@ sourceURL=" + url);

    // Immediately return after the eval. The script may have stomped all over
    // our local state.
  };

  req.send(null);
};

Browser.prototype._loadScript = function(id, url) {
    if (this.autowrap) {
        this.xhr = true;
        if (!xhrAvailable) {
            DEBUG('Autowrap is on but XHR is not available. Danger ahead.');
        }
    }

    if (xhrAvailable && domAvailable) {
        if (this.xhr) {
            try {
                return this._xhrScript(id, url);
            } catch (e) {
                return this._injectScript(id, url);
            }
        } else {
            try {
                return this._injectScript(id, url);
            } catch (e) {
                return this._xhrScript(id, url);
            }
        }
    } else if (xhrAvailable) {
        return this._xhrScript(id, url);
    } else if (domAvailable) {
        return this._injectScript(id, url);
    }

    DEBUG('Browser#_loadScript() not supported on this platform.');
    this.script(id);
};

if (domAvailable) {
  // actually loads the stylesheet.  separated out to ease unit testing
  Browser.prototype._loadStylesheet = function(id, url) {
    var body, el;
    
    body = document.getElementsByTagName('head')[0] || document.body;
    el   = document.createElement('link');
    el.rel = 'stylesheet';
    el.href = url;
    el.type = 'text/css';
    body.appendChild(el);
    el = body = null;

    this.stylesheet(id); // no onload support - just notify now.
  };
} else {
  // actually loads the stylesheet.  separated out to ease unit testing
  Browser.prototype._loadStylesheet = function(id, url) {
    DEBUG('Browser#_loadStylesheet() not supported on this platform.');
    this.stylesheet(id);
  };
}



// ..........................................................
// BROWSER PACKAGE
// 

/**
  Special edition of Package designed to work with the Browser source.  This
  kind of package knows how to get its data out of the Browser source on 
  demand.
*/
var BrowserPackage = Package.extend();
Browser.prototype.Package = BrowserPackage;

BrowserPackage.prototype.init = function(id, config, source) {
  Package.prototype.init.call(this, id, config);
  this.source = source;
};

// if not self, look for nested packages
BrowserPackage.prototype.canonicalPackageId = function(packageId, vers) {
  var ret, nested, info;
  
  ret = Package.prototype.canonicalPackageId.call(this, packageId, vers);
  if (ret) return ret ;
  
  nested = this.get('tiki:nested') || {}; 
  ret = nested[packageId];
  if (!ret) return null;

  info = this.source.packageInfoById[ret];
  return info && semver.compatible(vers,info.version) ? ret : null;
};

BrowserPackage.prototype.packageFor = function(canonicalId) {
  var ret = Package.prototype.packageFor.call(this, canonicalId);
  return ret ? ret : this.source.packageFor(canonicalId);
};

BrowserPackage.prototype.ensurePackage = function(canonicalId, done) {
  if (canonicalId === this.id) return done(); 
  this.source.ensurePackage(canonicalId, done);
};

BrowserPackage.prototype.catalogPackages = function() {
  var ret = [this], nested, key;

  nested = this.get('tiki:nested') || {};
  for(key in nested) {
    if (!nested.hasOwnProperty(key)) continue;
    ret.push(this.source.packageFor(nested[key]));
  }
  
  return ret ;
};

BrowserPackage.prototype.exists = function(moduleId) {
  var canonicalId = this.id+':'+moduleId;
  return !!this.source.factories[canonicalId];
};

BrowserPackage.prototype.load = function(moduleId) {
  var canonicalId, factory;
  
  canonicalId = this.id+':'+moduleId;
  factory  = this.source.factories[canonicalId];
  return factory ? new this.Factory(moduleId, this, factory) : null;
};

BrowserPackage.prototype.Factory = Factory;


displayNames(exports, 'tiki');

});
// ==========================================================================
// Project:   Tiki - CommonJS Runtime
// Copyright: ©2009-2010 Apple Inc. All rights reserved.
// License:   Licened under MIT license (see __preamble__.js)
// ==========================================================================
/*globals tiki ENV ARGS */

// This postamble runs when the loader and supporting modules are all 
// registered, allowing the real loader to replace the bootstrap version.
// it is not wrapped as a module so that it can run immediately.
"use modules false";
"use loader false";

// note that the loader.start method is safe so that calling this more than
// once will only setup the default loader once.
tiki = tiki.start();
tiki.replay(); // replay queue
