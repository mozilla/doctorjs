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
 * The Original Code is Bespin.
 *
 * The Initial Developer of the Original Code is
 * Dimitris Vardoulakis <dimvar@gmail.com>
 * Portions created by the Initial Developer are Copyright (C) 2010
 * the Initial Developer. All Rights Reserved.
 *
 * Contributor(s):
 *   Dimitris Vardoulakis <dimvar@gmail.com>
 *   Patrick Walton <pcwalton@mozilla.com>
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

/*
 * Narcissus - JS implemented in JS.
 *
 * Control-flow analysis to infer types. The output is in ctags format.
 */


/* (Possible) TODOs:
 * - now all objs are in heap. If it's too imprecise, treat them as heap vars.
 *   Create on stack & heap, and if heap changes when u need the obj then join.
 * - representation of Aobj: in the common case, an abstract obj has one proto 
 *   and one constructor. Specialize for this case.
 */

/*
 * Semantics of: function foo (args) body:
 * It's not the same as: var foo = function foo (args) body
 * If it appears in a script then it's hoisted at the top, so it's in funDecls
 * If it appears in a block then it's visible after it's appearance, in the
 * whole rest of the script!!
 * {foo(); {function foo() {print("foo");}}; foo();}
 * The 1st call to foo throws, but if you remove it the 2nd call succeeds.
 */

/* (POSSIBLY) UNSOUND ASSUMPTIONS:
 * - Won't iterate loops to fixpt.
 * - Return undefined not tracked, eg (if sth return 12;) always returns number.
 * - If the prototype property of a function object foo is accessed in a weird
 *   way, eg foo["proto" + "type"] the analysis won't figure it out.
 * - when popping from an array, I do nothing. This is hard to make sound.
 */

////////////////////////////////////////////////////////////////////////////////
/////////////////////////////   UTILITIES  /////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

if (!Array.prototype.forEach) 
  Array.prototype.forEach = function(fun) {
    for (var i = 0, len = this.length; i < len; i++) 
      /* if (i in this) */ fun(this[i], i, this);
  };

// search for an elm in the array that satisfies pred
Array.prototype.member = function(pred) {
  for (var i = 0, len = this.length; i < len; i++)
    /* if (i in this) */ if (pred(this[i])) return this[i];
  return false;
};

Array.prototype.memq = function(sth) {
  for (var i = 0, len = this.length; i < len; i++)
    /* if (i in this) */ if (sth === this[i]) return this[i];
  return false;
};

// starting at index, remove all elms that satisfy the pred in linear time.
Array.prototype.rmElmAfterIndex = function(pred, index) {
  if (index >= this.length) return;
  for (var i = index, j = index, len = this.length; i < len; i++)
    if (!pred(this[i])) this[j++] = this[i];
  this.length = j;
};

// remove all duplicates from array (keep first occurence of each elm)
// pred determines the equality of elms
Array.prototype.rmDups = function(pred) {
  var i = 0, self = this;
  while (i < (this.length - 1)) {
    this.rmElmAfterIndex(function(elm) { return pred(elm, self[i]); }, i+1);
    i++;
  }
};

// compare two arrays for structural equality
function arrayeq(eq, a1, a2) {
  var len = a1.length, i;
  if (len !== a2.length) return false;
  for (i=0; i<len; i++) if (!eq(a1[i], a2[i])) return false;
  return true;
}

function buildArray(size, elm) {
  var a = new Array(size);
  for (var i=0; i<size; i++) a[i] = elm;
  return a;
}

function buildString(size, elm) {
  return buildArray(size, elm).join("");
}

// merge two sorted arrays of numbers into a sorted new array, remove dups!
function arraymerge(a1, a2) {
  var i=0, j=0, len1 = a1.length, len2 = a2.length, a = new Array();
  while (true) {
    if (i === len1) {
      for (; j < len2; j++) a.push(a2[j]);
      return a;
    }
    if (j === len2) {
      for (; i<len1; i++) a.push(a1[i]);
      return a;
    }
    var diff = a1[i] - a2[j];
    if (diff < 0)
      a.push(a1[i++]);
    else if (diff > 0)
      a.push(a2[j++]);
    else
      i++;
  }
}

const UNHANDLED_CONSTRUCT = 0;
const CFA_ERROR = 1;
// number, string -> Error
// returns an Error w/ a "code" property, so that DrJS can classify errors
function errorWithCode(code, msg) {
  var e = new Error(msg);
  e.code = code;
  return e;
}

////////////////////////////////////////////////////////////////////////////////
////////////////////    PREPARE AST FOR FLOW ANALYSIS    ///////////////////////
////////////////////////////////////////////////////////////////////////////////

var jsparse = require('../../narcissus/lib/parser');
var Node = jsparse.Node;
const DECLARED_FORM = jsparse.DECLARED_FORM;
const STATEMENT_FORM = jsparse.STATEMENT_FORM;

eval(require('../../narcissus/lib/definitions').consts);

var print = console.log;
var fs = require('fs');
function printf(fd, s) { fs.writeSync(fd, s, null, encoding='utf8'); }

// count is used to generate a unique ID for each node in the AST.
var count;

function newCount() { return ++count; }

// Use token_count to get fresh IDs for new non-terminals
var token_count = (require('../../narcissus/lib/definitions').tokens).length;
const DOT_PROTO = token_count++;
const ARGUMENTS = token_count++;
const PLUS_ASSIGN = token_count++;

// Instead of a flat long case dispatch, arities create a tree-like dispatch.
// Nodes are grouped in arities by how we recur down their structure.
const NULLARY = [NULL, THIS, TRUE, FALSE, IDENTIFIER, NUMBER, STRING, REGEXP];
const UNARY = [DELETE, VOID, TYPEOF, NOT, BITWISE_NOT, UNARY_PLUS, UNARY_MINUS,
               NEW, INCREMENT, DECREMENT, DOT_PROTO, ARGUMENTS];
const BINARY = [BITWISE_OR, BITWISE_XOR, BITWISE_AND, EQ, NE, STRICT_EQ, 
                STRICT_NE, LT, LE, GE, GT, INSTANCEOF, LSH, RSH, URSH, PLUS, 
                MINUS, MUL, DIV, MOD, AND, OR, ASSIGN, INDEX, IN, DOT, 
                PLUS_ASSIGN];
const N_ARY = [COMMA, ARRAY_INIT];

// expr node -> stm node
function semiNode(n) {
  var sn = new Node(n.tokenizer, {type:SEMICOLON});
  sn.expression = n;
  return sn;
}

// tokenizer, string -> identifier node
function idNode(t, name) {
  var n = new Node(t, {type:IDENTIFIER});
  n.name = n.value = name;
  return n;
}

var astSize; // calculated for statistics

// node, optional string -> node
// Does some cleanup on the input expression node in-place.
// funName is used to name some anonymous funs using heuristics from the context
function fixExp(n, funName) {
  var nt = n.type, ch = n.children;
  astSize++;

  function fixe(n, i, ch) { ch[i] = fixExp(n); }

  if (NULLARY.memq(nt)) {
    if (nt === IDENTIFIER) n.name = n.value;
    else if (nt === STRING) n.value += "-";
  }
  else if (UNARY.memq(nt)) {
    if (nt === UNARY_MINUS && ch[0].type === NUMBER) {
      n.type = NUMBER;
      n.value = -ch[0].value;
      n.children = [];
      return n;
    }
    if (nt === NEW) { // unify NEW and NEW_WITH_ARGS
      n.type = NEW_WITH_ARGS;
      ch.push(new Node(n.tokenizer, {type:LIST, children:[]}));
    }
    ch[0] = fixExp(ch[0]);
  }
  else if (BINARY.memq(nt)) {
    if (nt === INDEX) {
      ch.forEach(fixe);
      if (ch[1].type === NUMBER) {
        ch[1].type = STRING;
        ch[1].value += "-";
      }
      return n;
    }
    else if (nt === DOT) {
      var ch1 = ch[1];
      // jsparse makes the 1st child of DOTs an ID b/c that's what is parsed.
      // For an evaluator it makes more sense to make the 1st child a string,
      // b/c functions that recur on DOTs won't try to look it up as a name.
      ch1.type = STRING;
      delete ch1.name;
      // DOT_PROTO has no new semantic meaning, it's an optimization so that we
      // dont check at every property access if the property name is "prototype"
      if (ch1.value === "prototype") n.type = DOT_PROTO;
    }
    else if (nt === ASSIGN && ch[0].assignOp === PLUS)
      n.type = PLUS_ASSIGN;
    else if (nt === ASSIGN && !ch[0].assignOp) {
      var n0 = ch[0];
      ch[0] = fixExp(n0);
      if (n0.type === IDENTIFIER)
        funName = n0.name;
      else if (n0.type === DOT) {
        var fname = n0.children[1].value;
        funName = fname.substring(0, fname.length - 1);
      }
      ch[1] = fixExp(ch[1], funName);
      return n;
    }
    ch.forEach(fixe);
  }
  else if (nt === HOOK || N_ARY.memq(nt)) {
    // Uncomment this if Narcissus produces empty COMMA nodes.
    if (nt === COMMA && ch.length === 0)
      ch.push(new Node(n.tokenizer, {type:TRUE}));
    if (nt === ARRAY_INIT) {
      ch.forEach(function(kid, i, ch) {
        if (kid === null) ch[i] = idNode(n.tokenizer, "undefined");
      });
    }
    ch.forEach(fixe);
  }
  else if (nt === CALL || nt === NEW_WITH_ARGS) {
    ch[0] = fixExp(ch[0]);
    ch[1].children.forEach(fixe);
  }
  else if (nt === FUNCTION) {
    fixFun(n, funName);
  }
  else if (nt === OBJECT_INIT) {
    ch.forEach(function(prop) {
      if (prop.type === GETTER || prop.type === SETTER) {
        // FIXME: for now, just don't crash on getters/setters
        prop.children = [new Node(n.tokenizer,
                                  { type : STRING, value : prop.name + "-" }),
                         new Node(n.tokenizer, {type:TRUE})];
      }
      else {
        var pch = prop.children, pch0 = pch[0], pname = pch0.value;
        pch0.type = STRING;
        delete pch0.name;
        pch0.value += "-";
        pch[1] = fixExp(pch[1], pname);
      }
    });
  }
  else if (nt === LET_BLOCK) {
    n.varDecls.forEach(function(vd, i, vds) {
      vd.name = vd.value;
      vd.initializer && (vd.initializer = fixExp(vd.initializer, vd.value));
    });
    n.expression = fixExp(n.expression);
  }
  else if (nt === YIELD) { // FIXME: for now, just don't crash on yield
    n.type = TRUE;
    delete n.value
  }
  return n;
}

// node, optional string -> void
function fixFun(n, funName) {
  var t = n.tokenizer;
  // replace name w/ a property fname which is an IDENTIFIER node.
  n.fname = idNode(t, n.name || funName);
  delete n.name;
  // turn the formals to nodes, I'll want to attach stuff to them later.
  n.params.forEach(function(p, i, ps) { ps[i] = idNode(t, p); });
  // don't tag builtin funs, they never have RETURN when used as constructors.
  n.hasReturn = fixStm(n.body);
}

// Array of id nodes, tokenizer -> comma node
// Convert variable initializations (coming from VAR,CONST,LET) to assignments.
function initsToAssigns(inits, t) {
  var n, vdecl, a, i, len, ch;  
  n = new Node(t, {type:COMMA});
  ch = n.children;
  for (i = 0, len = inits.length; i < len; i++) {
    vdecl = inits[i];
    if (vdecl.initializer) {
      a = new Node(vdecl.tokenizer, {type:ASSIGN});
      a.children = [idNode(vdecl.tokenizer, vdecl.name), vdecl.initializer];
      ch.push(a);
    }
  }
  // if no initialization values, push dummy node to avoid empty comma node.
  ch.length || ch.push(new Node(t, {type:TRUE}));
  return n;
}

// node, optional script node -> boolean
// returns true iff n contains RETURN directly (not RETURNs of inner functions).
function fixStm(n, parentScript) {
  var i, j, n2, ans1, ans2, ch = n.children;
  astSize++;
  
  switch (n.type) {
  case SCRIPT:
  case BLOCK:
    var ans1 = false, parscr = (n.type === SCRIPT) ? n : parentScript;
    i=0;
    while (i < ch.length) {
      n2 = ch[i];
      switch (n2.type) {
      case VAR:
      case CONST:
        ch.splice(i++, 1,
                  semiNode(fixExp(initsToAssigns(n2.children, n2.tokenizer))));
        break;

      case SWITCH:
        if (n2.cases.length === 0) {// switch w/out branches becomes semi node
          n2.discriminant = fixExp(n2.discriminant);
          ch[i] = semiNode(n2.discriminant);
        }
        else
          ans1 = fixStm(n2, parscr) || ans1;
        i++;
        break;

      case FUNCTION: //rm functions from Script bodies, they're in funDecls
        fixFun(n2);
        // To handle funs in blocks, unsoundly add them to funDecls
        if (n2.functionForm === STATEMENT_FORM) parscr.funDecls.push(n2);
        ch.splice(i, 1);
        // The code below is for when we don't handle funs in blocks.
        // if (n2.functionForm === DECLARED_FORM)
        //   ch.splice(i, 1);
        // else
        //   ++i;
        break;

      case SEMICOLON: // remove empty SEMICOLON nodes
        if (n2.expression == null) {
          ch.splice(i, 1);
          break;
        } // o/w fall thru to fix the node

      default:
        ans1 = fixStm(n2, parscr) || ans1;
        i++;
        break;
      }
    }
    return ans1;

  case LET: // let definitions
    n.children.forEach(function(vd) {
      vd.name = vd.value;
      vd.initializer && (vd.initializer = fixExp(vd.initializer));
    });
    return false;

  case LET_BLOCK:
    n.varDecls.forEach(function(vd) {
      vd.name = vd.value;
      vd.initializer && (vd.initializer = fixExp(vd.initializer));
    });
    if (n.expression) { // let-exp in stm context
      n.expression = fixExp(n.expression);
      n.block = semiNode(n.expression);
      delete n.expression;
      return false;
    }
    else // let-stm
      return fixStm(n.block, parentScript);

  case BREAK: case CONTINUE: case DEBUGGER:
    n.type = BLOCK;
    n.varDecls = [];
    n.children = [];
    return false;

  case SEMICOLON:
    if (!n.expression)
      n.expression = new Node(n.tokenizer, {type:TRUE});
    else
      n.expression = fixExp(n.expression); //n.expression can't be null
    return false;

  case IF:
    n.condition = fixExp(n.condition);
    ans1 = fixStm(n.thenPart, parentScript);
    return (n.elsePart && fixStm(n.elsePart, parentScript)) || ans1;

  case SWITCH:
    n.discriminant = fixExp(n.discriminant);
    ans1 = false;
    n.cases.forEach( function(branch) {
      branch.caseLabel && (branch.caseLabel = fixExp(branch.caseLabel));
      ans2 = fixStm(branch.statements, parentScript);
      ans1 = ans1 || ans2;
    });
    return ans1;

  case FOR:
    n2 = n.setup;
    if (n2) {
      if (n2.type === VAR || n2.type === CONST)
        n.setup = fixExp(initsToAssigns(n2.children, n2.tokenizer));
      else
        n.setup = fixExp(n2);
    }
    n.condition && (n.condition = fixExp(n.condition));
    n.update && (n.update = fixExp(n.update));
    return fixStm(n.body, parentScript);

  case FOR_IN:
    n.iterator = fixExp(n.iterator);
    n.object = fixExp(n.object);
    if (n.body.type !== BLOCK) {
      var fibody = new Node(n.tokenizer, {type:BLOCK});
      fibody.children = [n.body];
      n.body = fibody;
    }
    return fixStm(n.body, parentScript);
    
  case WHILE:
  case DO:
    n.condition = fixExp(n.condition);
    return fixStm(n.body, parentScript);

  case TRY: // turn the varName of each catch-clause to a node called exvar
    ans1 = fixStm(n.tryBlock, parentScript);
    n.catchClauses.forEach(function(clause) {
      clause.exvar = idNode(clause.tokenizer, clause.varName);
      clause.guard && (clause.guard = fixExp(clause.guard));
      ans2 = fixStm(clause.block, parentScript);
      ans1 = ans1 || ans2;
    });
    return (n.finallyBlock && fixStm(n.finallyBlock, parentScript)) || ans1;

  case THROW: 
    n.exception = fixExp(n.exception);
    return false;

  case RETURN:
    if (n.value === undefined)
      n.value = idNode(n.tokenizer, "undefined");
    else
      n.value = fixExp(n.value);
    return true;
     
  case VAR: case CONST: // very rare to not appear in a block or script.
    n.type = SEMICOLON;
    n.expression = fixExp(initsToAssigns(n.children, n.tokenizer));
    ch = [];
    return false;

  case FUNCTION:
    n2 = new Node(n.tokenizer, {type:FUNCTION});
    n2.name = n.name; delete n.name;
    n2.params = n.params; delete n.params;
    n2.functionForm = n.functionForm; delete n.functionForm;
    n2.body = n.body; delete n.body;
    fixFun(n2);
    // To handle funs not in scripts, unsoundly add them to funDecls
    parentScript.funDecls.push(n2);
    n.type = SEMICOLON;
    n.expression = new Node(n.tokenizer, {type:TRUE});
    return false;

  case WITH:
    n.object = fixExp(n.object);
    return fixStm(n.body, parentScript);

  case LABEL: //replace LABEL nodes by their statement (forget labels)
    n.type = BLOCK;
    n.varDecls = [];
    n.children = [n.statement];
    delete n.statement;
    return fixStm(n.children[0], parentScript);
    
  default:
    throw errorWithCode(UNHANDLED_CONSTRUCT,
                        "fixStm: " + n.type + ", line " + n.lineno);
  }
}

// Invariants of the AST after fixStm:
// - no NEW nodes, they became NEW_WITH_ARGS
// - the formals of functions are nodes, not strings
// - functions have a property fname which is an IDENTIFIER node, name deleted
// - no VAR and CONST nodes, they've become semicolon comma nodes.
// - no BREAK and CONTINUE nodes.
//   Unfortunately, this isn't independent of exceptions.
//   If a finally-block breaks or continues, the exception isn't propagated.
//   I will falsely propagate it (still sound, just more approximate).
// - no LABEL nodes
// - function nodes only in blocks, not in scripts
// - no empty SEMICOLON nodes
// - no switches w/out branches
// - each catch clause has a property exvar which is an IDENTIFIER node
// - all returns have .value (the ones that didn't, got an undefined)
// - the lhs of a property initializer of an OBJECT_INIT is always a string
// - the property names in DOT and OBJECT_INIT end with a dash.
// - there is no DOT whose 2nd arg is "prototype", they've become NODE_PROTOs.
// - the second kid of DOT is always a STRING, not an IDENTIFIER.
// - value of a NUMBER can be negative (UNARY_MINUS of constant became NUMBER).
// - the operator += has its own non-terminal, PLUS_ASSIGN.
// - each function node has a property hasReturn to show if it uses RETURN.
// - there is no INDEX whose 2nd arg has type NUMBER, they've become STRINGs.
// - The body of a LET_BLOCK in statement context is always a statement.
// - FUNCTIONs in BLOCKs are added to funDecls of enclosing SCRIPT.
// - Array literals don't have holes (null children) in them.
// - The body of FOR_IN is always a BLOCK.

function walkASTgenerator() {
  var jt = new Array(token_count); // jump table
  var o = {}; // dummy object for the calls to apply
  
  function recur(n) { return jt[n.type].apply(o, arguments); }
  function override(tt, fun) { jt[tt] = fun; }

  function _nokids() {}
  NULLARY.forEach(function(tt) { jt[tt] = _nokids; });

  function _haskids() {
    var args = arguments, ch = args[0].children;
    ch.forEach(function(kid) {
      args[0] = kid;
      recur.apply(o, args);
    });
  }
  [HOOK].concat(N_ARY, UNARY, BINARY).forEach(function(tt) {jt[tt]=_haskids;});

  jt[CALL] = jt[NEW_WITH_ARGS] = function() {
    var args = arguments, n = args[0], ch = n.children;
    args[0] = ch[0];
    recur.apply(o, args);
    ch[1].children.forEach(function(kid) {
      args[0] = kid;
      recur.apply(o, args);
    });
  };

  jt[OBJECT_INIT] = function() {
    var args = arguments;
    args[0].children.forEach(function(kid) {
      var ch = kid.children;
      args[0] = ch[0];
      recur.apply(o, args);
      args[0] = ch[1];
      recur.apply(o, args);
    });
  };

  jt[FUNCTION] = function() {
    arguments[0] = arguments[0].body;
    recur.apply(o, arguments);
  };

  jt[SCRIPT] = function() {
    var args = arguments, n = args[0];
    n.funDecls.forEach(function(fd) {
      args[0] = fd;
      recur.apply(o, args);
    });
    n.children.forEach(function(kid) {
      args[0] = kid;
      recur.apply(o, args);
    });
  };

  jt[BLOCK] = function() {
    var args = arguments;
    args[0].children.forEach(function(kid) {
      args[0] = kid;
      recur.apply(o, args);
    });
  };

  jt[SEMICOLON] = function() {
    arguments[0] = arguments[0].expression;
    recur.apply(o, arguments);
  };

  jt[IF] = function() {
    var n = arguments[0];
    arguments[0] = n.condition;
    recur.apply(o, arguments);
    arguments[0] = n.thenPart;
    recur.apply(o, arguments);
    if (n.elsePart) {
      arguments[0] = n.elsePart;
      recur.apply(o, arguments);
    }
  };

  jt[SWITCH] = function() {
    var args = arguments, n = args[0];
    args[0] = n.discriminant;
    recur.apply(o, args);
    n.cases.forEach(function(branch) {
      if (branch.caseLabel) {
        args[0] = branch.caseLabel;
        recur.apply(o, args);
      }
      args[0] = branch.statements;
      recur.apply(o, args);
    });
  };

  jt[FOR] = function() {
    var n = arguments[0];
    if (n.setup) {
      arguments[0] = n.setup;
      recur.apply(o, arguments);
    }
    if (n.condition) {
      arguments[0] = n.condition;
      recur.apply(o, arguments);
    }
    if (n.update) {
      arguments[0] = n.update;
      recur.apply(o, arguments);
    }
    arguments[0] = n.body;
    recur.apply(o, arguments);
  };

  jt[FOR_IN] = function() {
    var n = arguments[0];
    arguments[0] = n.iterator;
    recur.apply(o, arguments);
    arguments[0] = n.object;
    recur.apply(o, arguments);
    arguments[0] = n.body;
    recur.apply(o, arguments);
  };

  jt[WHILE] = jt[DO] = function() {
    var n = arguments[0];
    arguments[0] = n.condition;
    recur.apply(o, arguments);
    arguments[0] = n.body;
    recur.apply(o, arguments);
  };

  jt[TRY] = function() {
    var args = arguments, n = args[0];
    args[0] = n.tryBlock;
    recur.apply(o, args);
    n.catchClauses.forEach(function(clause) {
      if (clause.guard) {
        args[0] = clause.guard;
        recur.apply(o, args);
      }
      args[0] = clause.block;
      recur.apply(o, args);
    });
    if (n.finallyBlock) {
      args[0] = n.finallyBlock;
      recur.apply(o, args);
    }
  };

  jt[THROW] = function() {
    arguments[0] = arguments[0].exception;
    recur.apply(o, arguments);
  };

  jt[RETURN] = function() {
    var n = arguments[0];
    if (n.value) {
      arguments[0] = n.value;
      recur.apply(o, arguments);
    }
  };

  jt[WITH] = function() {
    var n = arguments[0];
    arguments[0] = n.object;
    recur.apply(o, arguments);
    arguments[0] = n.body;
    recur.apply(o, arguments);
  };

  jt[LET_BLOCK] = function() {
    var args = arguments, n = args[0];
    n.varDecls.forEach(function(vd) {
      (args[0] = vd.initializer) && recur.apply(o, args);
    });
    (args[0] = n.expression) || (args[0] = n.block); 
    recur.apply(o, args);
  };

  jt[LET] = function() {
    var args = arguments;
    args[0].children.forEach(function(vd) {
      (args[0] = vd.initializer) && recur.apply(o, args);
    });
  };

  return { walkAST: recur, override: override};
}

// node -> void
// Adds an "addr" property to nodes, which is a number unique for each node.
var labelAST, labelAST_override;

(function() {
  var walkerobj = walkASTgenerator(), override = walkerobj.override;
  labelAST = walkerobj.walkAST;
  labelAST_override = override;

  override(ARRAY_INIT, function(n) {
    n.addr = newCount();
    n.children.forEach(labelAST);
  });

  override(NEW_WITH_ARGS, function(n) {
    n.addr = newCount();
    labelAST(n.children[0]);
    n.children[1].children.forEach(labelAST);
  });

  override(REGEXP, function(n) { n.addr = newCount(); });

  override(OBJECT_INIT, function(n) {
    n.addr = newCount();
    n.children.forEach(function(prop) {
      labelAST(prop.children[0]); 
      labelAST(prop.children[1]);
    });
  });

  override(TRY, function(n) {
    labelAST(n.tryBlock);
    n.catchClauses.forEach(function(c) {
      c.exvar.addr = newCount();
      c.guard && labelAST(c.guard);
      labelAST(c.block);
    });
    n.finallyBlock && labelAST(n.finallyBlock);
  });

  override(SCRIPT, function(n) {
    n.varDecls.forEach(function(vd) {vd.addr = newCount();});
    n.funDecls.forEach(labelAST);
    n.children.forEach(labelAST);
  });

  override(FUNCTION, function _function(n) {
    n.addr = newCount();
    n.defaultProtoAddr = newCount();
    n.fname.addr = newCount();
    n.params.forEach(function(p) { p.addr = newCount(); });
    labelAST(n.body);
  });
})();

// Node, number, Array of id nodes -> void
// WITH node, address of the fresh variable, bound variables
// After desugarWith is executed, there are no WITHs in the AST.
var desugarWith;
// FIXME: the desugaring handles nested WITHs incorrectly.

(function () {
  var walkerobj = walkASTgenerator(), override = walkerobj.override;
  desugarWith = walkerobj.walkAST;

  function withIdNode(t, addr) {
    var n = idNode(t, "internalVar: with");
    n.addr = addr;
    return n;
  }

  override(SCRIPT, function(n, withAddr, boundvars) {
    n.funDecls.forEach(function(fd) { desugarWith(fd, withAddr, boundvars); });
    var blen = boundvars.length;
    Array.prototype.push.apply(boundvars, n.varDecls);
    n.children.forEach(function(stm) {
      desugarWith(stm, withAddr, boundvars, n.varDecls);
    });
    boundvars.splice(blen, boundvars.length);
  });

  override(FUNCTION, function(n, withAddr, boundvars) {
    var blen = boundvars.length;
    Array.prototype.push.apply(boundvars, n.params);
    desugarWith(n.body, withAddr, boundvars);
    boundvars.splice(blen, boundvars.length);
  });

  // Turn to a block with two statements.
  // The 4th argument is the varDecls of the innermost enclosing SCRIPT, so that
  // the fresh variable of the WITH can be added there.
  override(WITH, function(n, withAddr, boundvars, vardecls) {
    var newaddr = newCount(), t = n.tokenizer;
    var freshvar = withIdNode(t, newaddr), assgn;
    vardecls.push(freshvar);
    assgn = new Node(t, {type:ASSIGN});
    assgn.children = [freshvar, n.object];
    desugarWith(n.body, newaddr, [], vardecls);
    n.type = BLOCK;
    n.varDecls = [];
    n.children = [semiNode(assgn), n.body];
    delete n.object;
    delete n.body;
  });

  // Add the CATCH variable to the bound variables
  override(TRY, function(n, withAddr, boundvars, vardecls) {
    desugarWith(n.tryBlock, withAddr, boundvars, vardecls);
    n.catchClauses.forEach(function(clause) {
      boundvars.push(clause.exvar);
      clause.guard && desugarWith(clause.guard, withAddr, boundvars);
      desugarWith(clause.block, withAddr, boundvars, vardecls);
      boundvars.pop();
    });
    n.finallyBlock && desugarWith(n.finallyBlock,withAddr,boundvars,vardecls);
  });

  // May change n to an IF node
  override(FOR_IN, function(n, withAddr, boundvars, vardecls) {    
    var it = n.iterator, it, obj = n.object, b = n.body;
    if (it.type === IDENTIFIER)
      // (Temporary) Copy to avoid sharing introduced by desugaring.
      n.iterator = it = idNode(it.tokenizer, it.value);
    desugarWith(obj, withAddr, boundvars);
    desugarWith(b, withAddr, boundvars, vardecls);
    if (it.type !== IDENTIFIER) {
      desugarWith(it, withAddr, boundvars);
      return;
    }
    if (_makeHook(n, it, withAddr, boundvars)) {
      var t = n.tokenizer, ch = n.children;
      n.type = IF;
      n.children = [];
      n.condition = ch[0];
      var forinn = new Node(t, {type:FOR_IN});
      forinn.iterator = ch[1];
      forinn.object = obj;
      forinn.body = b;
      n.thenPart = forinn;
      forinn = new Node(t, {type:FOR_IN});
      forinn.iterator = ch[2];
      forinn.object = obj;
      // The body b must be cloned o/w markConts will overwrite the conts of the
      // true branch when it processes the false branch.
      forinn.body = b;
      n.elsePart = forinn;
    }
  });

  // Change the 1st arg to a HOOK node.
  // n may be an ID node, but it doesn't appear in varDecls b/c it's an rvalue,
  // it doesn't come from a VAR, so it can be mutated safely. 
  // Returns true iff it edits the node.
  function _makeHook(n, idn, withAddr, boundvars) {
    var t = idn.tokenizer, name = idn.name;
    if (!withAddr) return;
    if (boundvars.member(function(bv) { return bv.name === name; })) return;
    var inn = new Node(t, {type : IN});
    inn.children = [new Node(t, {type : STRING, value : name + "-"}),
                    withIdNode(t, withAddr)];
    var dotn = new Node(t, {type: DOT});
    dotn.children = [withIdNode(t, withAddr), 
                     new Node(t, {type:STRING, value : name + "-"})];
    n.type = HOOK;
    n.children = [inn, dotn, idNode(t, name)];
    return true;
  }

  override(IDENTIFIER, function(n, withAddr, boundvars) {
    _makeHook(n, n, withAddr, boundvars);
  });

  // May change n to a HOOK node
  function _assign(n, withAddr, boundvars) {
    var t = n.tokenizer, type = n.type, lval = n.children[0], 
    aop = lval.assignOp, rval = n.children[1];
    desugarWith(rval, withAddr, boundvars);
    if (lval.type !== IDENTIFIER) {
      desugarWith(lval, withAddr, boundvars);
      return;
    }
    if (_makeHook(n, lval, withAddr, boundvars)) {
      var branch = n.children[1], assgn = new Node(t, {type:type});
      branch.assignOp = aop;
      assgn.children = [branch, rval];
      n.children[1] = assgn;
      branch = n.children[2], assgn = new Node(t, {type:type});
      branch.assignOp = aop;
      assgn.children = [branch, rval];
      n.children[2] = assgn;
    }
  }

  override(ASSIGN, _assign);
  override(PLUS_ASSIGN, _assign);
})();

// Node, Map from strings to id nodes, Array of id nodes -> void
// Rename variables according to the input substitution map
var subst;

(function () {
  var walkerobj = walkASTgenerator(), override = walkerobj.override;
  subst = walkerobj.walkAST;

  // The only substitution happens here. All other cases are binders, so they
  // update boundvars to prevent erroneous substitutions.
  override(IDENTIFIER, function(n, smap, boundvars) {
    var vname = n.value;
    if (boundvars.member(function(bv) { return bv.value === vname; })) return;
    var newvar = smap[vname];
    if (newvar) {
      n.name = n.value = newvar.value; 
      n.addr = newvar.addr;
    }
  });

  override(FUNCTION, function(n, smap, boundvars) {
    var blen = boundvars.length;
    boundvars.push(n.fname);
    Array.prototype.push.apply(boundvars, n.params);
    subst(n.body, smap, boundvars);
    boundvars.splice(blen, boundvars.length);
  });

  function _block(vds, fds, stms, smap, boundvars) {
    var blen = boundvars.length;
    Array.prototype.push.apply(boundvars, vds);
    if (fds) {
      fds.forEach(function(fd) { boundvars.push(fd.fname); });
      fds.forEach(function(fd) { subst(fd, smap, boundvars); });
    }
    stms.forEach(function(stm) { subst(stm, smap, boundvars); });
    boundvars.splice(blen, boundvars.length);
  }

  override(SCRIPT, function(n, smap, boundvars) {
    _block(n.varDecls, n.funDecls, n.children, smap, boundvars);
  });

  override(BLOCK, function(n, smap, boundvars) {
    _block(n.varDecls, undefined, n.children, smap, boundvars);
  });

  override(FOR, function(n, smap, boundvars) {
    var blen = boundvars.length;
    n.varDecls && Array.prototype.push.apply(boundvars, n.varDecls);
    n.setup && subst(n.setup, smap, boundvars);
    n.condition && subst(n.condition, smap, boundvars);
    n.update && subst(n.update, smap, boundvars);
    subst(n.body, smap, boundvars);
    boundvars.splice(blen, boundvars.length);
  });

  override(LET_BLOCK, function(n, smap, boundvars) {
    var vds = n.varDecls, stms;
    if (n.expression)
      stms = [semiNode(n.expression)];
    else {
      vds.concat(n.block.varDecls);
      stms = n.block.children;
    }
    _block(vds, undefined, stms, smap, boundvars);
  });

  override(TRY, function(n, smap, boundvars) {
    subst(n.tryBlock, smap, boundvars);
    n.catchClauses.forEach(function(clause) {
      boundvars.push(clause.exvar);
      clause.guard && subst(clause.guard, smap, boundvars);
      subst(clause.block, smap, boundvars);
      boundvars.pop();
    });
    n.finallyBlock && subst(n.finallyBlock, smap, boundvars);
  });
})();

// Must happen after desugaring of WITH, o/w when I create fresh vars for LETs,
// I may subst erroneously in the body of a WITH.
// After desugarLet is executed, there are no LETs or LET_BLOCKs in the AST.
var desugarLet;

(function () {
  var walkerobj = walkASTgenerator(), override = walkerobj.override;
  desugarLet = walkerobj.walkAST;

  // Array of id nodes, Array of id nodes, tokenizer -> 
  // { smap : Substitution map, comman : comma node }
  function letInitsToAssigns(vds, scriptVds, t) {
    var smap = {}, newaddr, freshvar, comman;
    for (var i = 0, len = vds.length; i < len; i++) {
      newaddr = newCount();
      // New vars must have different names for tagVarRefs to work.
      freshvar = idNode(t, "internalVar: let" + newaddr);
      freshvar.addr = newaddr;
      smap[vds[i].value] = freshvar;
      scriptVds.push(freshvar);
    }
    comman = initsToAssigns(vds, t);
    subst(comman, smap, []);
    desugarLet(comman, scriptVds);
    return {smap : smap, comman : comman};
  }

  override(LET_BLOCK, function(n, scriptVds) {
    var tmp = letInitsToAssigns(n.varDecls, scriptVds, n.tokenizer),
    smap = tmp.smap,
    comman = tmp.comman;
    delete n.variables;
    var body;
    if (body = n.expression) {
      subst(body, smap, []);
      desugarLet(body, scriptVds);
      n.type = COMMA;
      n.children = comman.children;
      n.children.push(body);
      delete n.expression;
    }
    else if (body = n.block) {
      subst(body, smap, []);
      desugarLet(body, scriptVds, body);
      n.type = BLOCK;
      n.children = body.children;
      n.children.unshift(semiNode(comman));
      delete n.block;
      n.varDecls = [];
    }
  });

  override(BLOCK, function(n, scriptVds) {
    n.children.forEach(function(stm) { desugarLet(stm, scriptVds, n); });
  });

  override(FOR, function(n, scriptVds) {
    n.setup && desugarLet(n.setup, scriptVds, n); // LET can appear in setup
    n.condition && desugarLet(n.condition, scriptVds);
    n.update && desugarLet(n.update, scriptVds);
    desugarLet(n.body, scriptVds);
  });

  // LET definitions can appear in SCRIPTs or BLOCKs
  override(LET, function(n, scriptVds, innerBlock) {
    var tmp = letInitsToAssigns(n.children, scriptVds, n.tokenizer),
    smap = tmp.smap,
    comman = tmp.comman;
    // Call subst on the sub-nodes of innerBlock directly, to avoid binding vars
    // that must be substituted.
    if (innerBlock.type === FOR) {
      subst(innerBlock.setup, smap, []);
      innerBlock.condition && subst(innerBlock.condition, smap, []);
      innerBlock.update && subst(innerBlock.update, smap, []);
      subst(innerBlock.body, smap, []);
      n.type = COMMA;
      n.children = comman.children;
    }
    else {
      innerBlock.children.forEach(function(stm) { subst(stm, smap, []); });
      n.type = SEMICOLON;
      n.expression = comman;
      delete n.children;
    }
  });

  override(SCRIPT, function(n) {
    var vds = n.varDecls;
    n.funDecls.forEach(desugarLet);
    n.children.forEach(function(stm) { desugarLet(stm, vds, n); });
  });
})();

const STACK = 0, HEAP = 1;

// helper function for the IDENTIFIER case of tagVarRefs
function tagVarRefsId(classifyEvents) {
  return function(n, innerscope, otherscopes) {
    var boundvar, varname = n.name;
    // search var in innermost scope
    for (var i = innerscope.length - 1; i >= 0; i--) {
      boundvar = innerscope[i];
      if (boundvar.name === varname) {
        //print("stack ref: " + varname);
        n.kind = STACK;
        // if boundvar is a heap var and some of its heap refs get mutated,
        // we may need to update bindings in frames during the cfa.
        n.addr = boundvar.addr; 
        return;
      }
    }
    // search var in other scopes
    for (var i = otherscopes.length - 1; i >= 0; i--) {
      boundvar = otherscopes[i];
      if (boundvar.name === varname) {
        // print("heap ref: " + varname);
        n.kind = boundvar.kind = HEAP;
        n.addr = boundvar.addr;
        flags[boundvar.addr] = true;
        return;
      }
    }
    // var has no binder in the program
    if (commonJSmode && varname === "exports") {
      n.kind = HEAP;
      n.addr = exports_object_av_addr;
      var p = arguments[3]; // exported property name passed as extra arg
      if (p && p.type === STRING)
        exports_object.lines[p.value.slice(0, -1)] = p.lineno;
      return;
    }
    //print("global: " + varname + " :: " + n.lineno);
    n.type = DOT;
    var nthis = idNode({lineno: n.lineno}, "internalVar: global object");
    nthis.kind = HEAP;
    if (classifyEvents && varname === "addEventListener")
      nthis.addr = chrome_obj_av_addr;
    else
      nthis.addr = global_object_av_addr;
    n.children = [nthis, new Node({}, {type:STRING, value:n.name + "-"})];
  };
}

// node, array of id nodes, array of id nodes -> void
// Classify variable references as either stack or heap references.
var tagVarRefs, tagVarRefs_override;

(function() {
  var walkerobj = walkASTgenerator(), override = walkerobj.override;
  tagVarRefs = walkerobj.walkAST;
  tagVarRefs_override = override;

  override(DOT, function(n, innerscope, otherscopes) {
    var ch = n.children;
    var n0 = ch[0];
    // don't classify property names
    if (commonJSmode && n0.type === IDENTIFIER && n0.name === "exports")
      tagVarRefs(n0, innerscope, otherscopes, ch[1]);
    else 
      tagVarRefs(n0, innerscope, otherscopes);
  });

  override(INDEX, function(n, innerscope, otherscopes) {
    var ch = n.children, n0 = ch[0], shadowed = false;
    // use new non-terminal only  if "arguments" refers to the arguments array
    if (n0.type === IDENTIFIER && n0.name === "arguments") {
      for (var i = innerscope.length - 1; i >= 0; i--) 
        if (innerscope[i].name === "arguments") {
          shadowed = true;
          break;
        }
      if (!shadowed) {
        n.type = ARGUMENTS;
        n.arguments = innerscope; //hack: innerscope is params (maybe extended)
        ch[0] = ch[1];
        ch.splice(1, 1);
        // undo the changes made for INDEX nodes only in fixExp
        if (ch[0].type === STRING && propIsNumeric(ch[0].value)) {
          ch[0].type = NUMBER;
          ch[0].value = ch[0].value.slice(0, -1) - 0;
        }
      }
    }
    ch.forEach(function(kid) { tagVarRefs(kid, innerscope, otherscopes); });
  });

  override(IDENTIFIER, tagVarRefsId(false));

  override(FUNCTION, function(n, innerscope, otherscopes) {
    var fn = n.fname, len, params = n.params;
    len = otherscopes.length;
    // extend otherscopes
    Array.prototype.push.apply(otherscopes, innerscope); 
    // fun name is visible in the body & not a heap ref, add it to scope
    params.push(fn);
    tagVarRefs(n.body, params, otherscopes);
    params.pop();
    if (fn.kind !== HEAP) fn.kind = STACK;    
    params.forEach(function(p) {if (p.kind !== HEAP) p.kind=STACK;});
    // trim otherscopes
    otherscopes.splice(len, innerscope.length);
  });

  override(SCRIPT, function(n, innerscope, otherscopes) {
    var i, j, len, vdecl, vdecls = n.varDecls, fdecl, fdecls = n.funDecls;
    // extend inner scope
    j = innerscope.length;
    Array.prototype.push.apply(innerscope, vdecls);
    fdecls.forEach(function(fd) { innerscope.push(fd.fname); });
    // tag refs in fun decls
    fdecls.forEach(function(fd) { tagVarRefs(fd, innerscope, otherscopes); });
    // tag the var refs in the body
    var as = arguments;
    n.children.forEach(function(stm) {tagVarRefs(stm,innerscope,otherscopes);});
    // tag formals
    vdecls.forEach(function(vd) {
      // for toplevel vars, assigning flags causes the Aval`s to be recorded
      // in the heap. After the analysis, we use that for ctags.
      if (as[3] === "toplevel") flags[vd.addr] = true;
      if (vd.kind !== HEAP) vd.kind = STACK;
    });
    fdecls.forEach(function(fd) { if (fd.kind !== HEAP) fd.kind = STACK; });    
    //trim inner scope 
    innerscope.splice(j, vdecls.length + fdecls.length);
  });

  override(TRY, function(n, innerscope, otherscopes) {
    tagVarRefs(n.tryBlock, innerscope, otherscopes);
    n.catchClauses.forEach(function(clause) {
      var xv = clause.exvar;
      innerscope.push(xv);
      clause.guard && 
        tagVarRefs(clause.guard, innerscope, otherscopes);
      tagVarRefs(clause.block, innerscope, otherscopes);
      innerscope.pop();
      if (xv.kind !== HEAP) xv.kind = STACK;
    });
    n.finallyBlock && tagVarRefs(n.finallyBlock, innerscope, otherscopes);
  });
})();

// node, node, node -> void
// For every node N in the AST, add refs from N to the node that is normally 
// exec'd after N and to the node that is exec'd if N throws an exception.
var markConts;

(function() {
  var walkerobj = walkASTgenerator(), override = walkerobj.override;
  markConts = walkerobj.walkAST;

  function _fun(n) { markConts(n.body, undefined, undefined); }
  override(FUNCTION, _fun);

  function _block(n, kreg, kexc) {
    var ch = n.children, i, len;
    n.kexc = kexc;
    len = ch.length;
    if (len === 0) 
      n.kreg = kreg;
    else {
      n.kreg = ch[0];
      len--;
      for (i=0; i < len; i++) markConts(ch[i], ch[i+1], kexc);
      markConts(ch[len], kreg, kexc);
    }
  }
  override(BLOCK, _block);

  override(SCRIPT, function(n, kreg, kexc) { 
    n.funDecls.forEach(_fun); 
    _block(n, kreg, kexc);
  });

  override(SEMICOLON, function(n, kreg, kexc) {
    n.kreg = kreg;
    n.kexc = kexc;
    markConts(n.expression);
  });

  // normally, return & throw don't use their kreg. But this analysis allows 
  // more permissive control flow, to be faster.
  override(THROW, function(n, kreg, kexc) {
    n.kreg = kreg;
    n.kexc = kexc;
    markConts(n.exception);
  });

  override(RETURN, function(n, kreg, kexc) {
    n.kreg = kreg;
    n.kexc = kexc;
    markConts(n.value);
  });

  override(IF, function(n, kreg, kexc) {
    var thenp = n.thenPart, elsep = n.elsePart, condStm;
    condStm = semiNode(n.condition);
    n.kreg = condStm; // first run the test
    n.kexc = kexc;
    markConts(condStm, thenp, kexc); // ignore result & run the true branch
    markConts(thenp, elsep || kreg, kexc); // then run the false branch
    elsep && markConts(elsep, kreg, kexc);
  });

  function markContsCase(n, kreg, kexc) {
    var clabel = n.caseLabel, clabelStm, stms = n.statements;
    n.kexc = kexc;
    if (clabel) {
      clabelStm = semiNode(clabel);
      n.kreg = clabelStm;
      markConts(clabelStm, stms, kexc);
    }
    else n.kreg = stms;
    markConts(stms, kreg, kexc);
  }

  override(SWITCH, function(n, kreg, kexc) {
    var cases = n.cases, discStm, i, len;
    discStm = semiNode(n.discriminant);
    n.kreg = discStm; // first run the discriminant, then all branches in order
    n.kexc = kexc;
    markConts(discStm, cases[0], kexc);
    for (i = 0, len = cases.length - 1; i < len; i++) //no empty switch, len >=0
      markContsCase(cases[i], cases[i+1], kexc);
    markContsCase(cases[len], kreg, kexc);
  });

  override(FOR, function(n, kreg, kexc) {
    var body = n.body;
    n.kexc = kexc;
    // Do setup, condition, body & update once.
    var setup = n.setup, setupStm, condition = n.condition, condStm;
    var update = n.update, updStm;
    n.kexc = kexc;
    if (!setup && !condition)
      n.kreg = body;
    else if (setup && !condition) {
      setupStm = semiNode(setup);
      n.kreg = setupStm;
      markConts(setupStm, body, kexc);
    }
    else {// condition exists
      condStm = semiNode(condition);
      markConts(condStm, body, kexc);
      if (setup) {
        setupStm = semiNode(setup);
        n.kreg = setupStm;
        markConts(setupStm, condStm, kexc);  
      }
      else n.kreg = condStm;
    }
    if (update) {
      updStm = semiNode(update);
      markConts(body, updStm, kexc);
      markConts(updStm, kreg, kexc);
    }
    else markConts(body, kreg, kexc);
  });

  override(FOR_IN, function(n, kreg, kexc) {
    var body = n.body;
    n.kexc = kexc;
    n.kreg = body;
    markConts(body, kreg, kexc);
  });

  override(WHILE, function(n, kreg, kexc) {
    var condStm = semiNode(n.condition), body = n.body;
    n.kreg = condStm;
    n.kexc = kexc;
    markConts(condStm, body, kexc);
    markConts(body, kreg, kexc);
  });

  override(DO, function(n, kreg, kexc) {
    var condStm = semiNode(n.condition), body = n.body;
    n.kreg = body;
    n.kexc = kexc;
    markConts(body, condStm, kexc);
    markConts(condStm, kreg, kexc);
  });

  function markContsCatch(n, knocatch, kreg, kexc) {
    var guard = n.guard, guardStm, block = n.block;
    if (guard) {// Mozilla catch
      // The guard is of the form (var if expr).
      // If expr is truthy, the catch body is run w/ var bound to the exception.
      // If expr is falsy, we go to the next block (another catch or finally).
      // If the guard or the body throw, the next catches (if any) can't handle
      // the exception, we go to the finally block (if any) directly.      
      markConts(guard);
      guardStm = semiNode(guard);
      n.kreg = guardStm;
      guardStm.kcatch = block; // this catch handles the exception
      guardStm.knocatch = knocatch; // this catch doesn't handle the exception
      guardStm.kexc = kexc; // the guard throws a new exception
    }
    markConts(block, kreg, kexc);
  }

  override(TRY, function(n, kreg, kexc) {
    var fin = n.finallyBlock, clause, clauses=n.catchClauses, knocatch, i, len;
    // process back-to-front to avoid if-madness
    if (fin) {
      markConts(fin, kreg, kexc);
      knocatch = kexc = kreg = fin; // TRY & CATCHes go to fin no matter what
    }
    for (len = clauses.length, i = len-1; i>=0; i--) {
      clause = clauses[i];
      markContsCatch(clause, knocatch, kreg, kexc);
      knocatch = clause;
    }
    markConts(n.tryBlock, kreg, knocatch || kexc);
    n.kreg = n.tryBlock;
  });
})();


////////////////////////////////////////////////////////////////////////////////
////////////////////////////   CFA2  code  /////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// abstract objects and abstract values are different!!!

var heap;
// modified[addr] is a timestamp that shows the last time heap[addr] was updated
var modified; 
var timestamp;
// If i is the addr of a var, flags[i] is true if the var is a heap var.
var flags;
var exports_object;
var exports_object_av_addr;
var commonJSmode;
var timedout = false, timeout = 120; // stop after 2 minutes if you're not done

// A summary contains a function node (fn), an array of abstract values (args),
// a timestamp (ts) and abstract values (res) and (err). It means: when we call
// fn w/ args and the heap's timestamp is ts, the result is res and if fn can
// throw an exception, the value thrown is err.

// summaries: a map from addresses of fun nodes to triples {ts, insouts, type},
// where ts is a timestamp, insouts is an array of args-result pairs,
// and type is the join of all args-result pairs.
var summaries;

// pending contains info that exists in the runtime stack. For each pending call
// to evalFun, pending contains an object {args, ts} where args is the arguments
// of the call and ts is the timestamp at the time of the call.
var pending;
// core JS functions also use pending but differently.

// when initGlobals is called, count has its final value (core objs are in heap)
// FIXME, I'm violating the invariant in "function cfa2". Change it?
function initGlobals() {
  big_ts = 1000; // used only when debugging
  timestamp = 0;
  heap = new Array(count); // reserve heap space, don't grow it gradually
  modified = buildArray(count, timestamp);
  summaries = {}; // We use {} instead of an Array b/c it's sparse.
  pending = {};
  flags = {};
  exports_object = {lines : {}};
}

// string -> void
// works only in NodeJS 
function dumpHeap(filename) {
  var fd = fs.openSync(filename, "w", mode=0777);
  for (var i = 0, l = heap.length; i < l; i++)
    printf(fd, "[" + i + "]\n" + (heap[i] ? heap[i].toString(2) : "") + "\n");
  fs.closeSync(fd);
}

// non-empty array of strings -> void
function normalizeUnionType(types) {
  // any is a supertype of all types
  if (types.memq("any")) {
    types[0] = "any";
    types.length = 1;
  }
  else
    types.rmDups(function(e1, e2) {return e1 === e2;});
}

// Constructor for abstract properties
// Takes an object w/ the property's attributes
// Don't call from outside the abstract-values module, use addProp instead.
function Aprop(attribs){
  this.aval = attribs.aval;
  // writable, enumerable and configurable default to true
  this.write = ("write" in attribs) ? attribs.write : true;
  this.enum = ("enum" in attribs) ? attribs.enum : true;
  this.config = ("config" in attribs) ? attribs.config : true;
}

// optional number -> string
Aprop.prototype.toString = function(indent) {
  return this.aval.toString(indent);
};

// An abstract object o1 is represented as a JS object o2. 
// A property of o1 named p has the name p- in o2.
// A special property p of o1 has the name -p in o2.
// Special properties: -number, -string, -proto, -fun, -addr
// -addr: the address of o1 in the heap
// -proto: the address of o1's prototype in the heap
// -fun: may point to a function node
// -number: may contain an Aval (join of properties w/ "numeric" names)
// -string: may contain an Aval (join of all properties)
function Aobj(specialProps) {
  for (var p in specialProps) this["-" + p] = specialProps[p];
  heap[specialProps.addr] = this; // put new object in heap
}

Aobj.prototype = new Array();

// Takes an optional array for cycle detection.
Aobj.prototype.toType = function(seenObjs) {
  var self = this;
  if (seenObjs) {
    if (seenObjs.memq(self))
      return "any";
    else
      seenObjs.push(self);
  }
  else
    seenObjs = [self];

  if (this["-fun"]) return funToType(this["-fun"], seenObjs);
  var c = this.getProp("constructor-");
  var types = [];
  if (c === undefined) return "Global Object";
  c.forEachObj(function(o) {if (o["-fun"]) types.push(o["-fun"].fname.name);});
  if (types.length === 0)
    throw errorWithCode(CFA_ERROR, "Didn't find a name for constructor");
  normalizeUnionType(types);
  if (types.length === 1) {
    if (types[0] === "Array") return this.toArrayType(seenObjs);
    return types[0];
  }
  return ("<" + types.join(" | ") + ">");
};

// void -> boolean
Aobj.prototype.isArray = function() {
  var c = this.getProp("constructor-"), cobj;
  if (c === undefined) return false;
  if (c.objs.length !== 1) return false;
  cobj = heap[c.objs[0]];
  return cobj["-fun"] && cobj["-fun"].fname.name === "Array";
}

// For homogeneous arrays, include the type of their elms.
// Takes an optional array for cycle detection.
Aobj.prototype.toArrayType = function(seenObjs) {
  var elmtype = BOTTOM, self = this;
  this.forEachOwnProp(function(p) {
    if (propIsNumeric(p)) elmtype = avjoin(elmtype, self.getOwnExactProp(p));
  });
  elmtype = elmtype.toType(seenObjs);
  if (/\|/.test(elmtype) || elmtype === "any")
    return "Array";
  else
    return "Array[" + elmtype + "]";
};

// void -> function node
Aobj.prototype.getFun = function() { return this["-fun"]; };

// Aval -> void
Aobj.prototype.updateProto = function(av) {
  if (this["-proto"]) {
    if (!avlt(av, this["-proto"])) {
      this["-proto"] = avjoin(this["-proto"], av);
      //print("++ts: 1");
      ++timestamp;
    }
    return;
  }
  this["-proto"] = av;
  //print("++ts: 2");
  ++timestamp;
};

// string -> boolean
function propIsNumeric(p) {
  return p === "-number" || (/-$/.test(p) && !isNaN(p.slice(0, -1)));
}

// act: Aobj, optional Array[string] -> {val : A, stop : boolean}
// combine: Array[A] -> A
function foldProtoChain(o, act, combine) {
  function recur(o, seenObjs, seenProps) {
    var v = act(o, seenProps), val = v.val;
    if (v.stop) return val; // stop going up the chain
    if (!o["-proto"]) return val; // reached the end of the prototype chain
    if (seenObjs.memq(o))
      return val;
    else
      seenObjs.push(o);
    var a = [], solen = seenObjs.length, splen = seenProps.length;
    o["-proto"].forEachObj(function(proto) {
      a.push(recur(proto, seenObjs, seenProps));
      seenObjs.splice(solen, seenObjs.length);
      seenProps.splice(splen, seenProps.length);
    });
    a.push(val); // The current level's result is last, 'combine' pops to get it
    return combine(a);
  }

  return recur(o, [], []);
}

// string -> Aval or undefined
// doesn't look in prototype chain
Aobj.prototype.getOwnExactProp = function(pname) {
  return this[pname] && this[pname].aval;
};

// string -> Aval or undefined
// doesn't look in prototype chain
// pname is not "-number" or "-string"
Aobj.prototype.getOwnProp = function(pname) {
  if (this.hasOwnProperty(pname)) 
    return this[pname].aval;
  if (this.numPropsMerged && propIsNumeric(pname))
    return this["-number"].aval;
  if (this.strPropsMerged) 
    return this["-string"].aval;
};

// string -> Aval or undefined
// May include "-number" and "-string" in its result
Aobj.prototype.getProp = function(pname) {
  return getProp(this, pname, true);
};

// Aobj, string, boolean -> Aval or undefined
// pname is not "-number" or "-string"
// Looks in prototype chain. Returns undefined iff the property doesn't exist in
// *all* paths up the prototype chain o/w it returns an Aval.
// function getProp(o, pname, lax) {
//   function act(o) {
//     if (o.hasOwnProperty(pname))
//       return {val : o[pname].aval, stop : true};
//     if (lax && o.numPropsMerged) {
//       if (propIsNumeric(pname))
//         return {val : o["-number"].aval, stop : true};
//       if (o.strPropsMerged)
//         return {val : o["-string"].aval, stop : false};
//     }
//     return { stop : false };
//   }

//   function combine(avs) {
//     var notfoundinsomechain = false, val = avs.pop();
//     avs.forEach(function(av) {
//       if (!av)
//         notfoundinsomechain = true;
//       else
//         val = maybeavjoin(val, av);
//     });
//     return val && (notfoundinsomechain ? avjoin(AUNDEF, val) : val);
//   }
//   return foldProtoChain(o, act, combine);
// }

function getProp(o, pname, lax) {
  var levels = 0, av;

  while (o !== undefined && levels <= 2) {
    if (o.hasOwnProperty(pname))
      return o[pname].aval;
    if (lax && o.numPropsMerged) {
      if (propIsNumeric(pname))
        return o["-number"].aval;
      if (o.strPropsMerged)
        av = maybeavjoin(av, o["-string"].aval);
    }
    levels++;
    o = o["-proto"] && heap[o["-proto"].objs[0]];
  }
  return av;
}

Aobj.prototype.getNumProps = function() {
  this.mergeNumProps();
  return this["-number"].aval;
};

// Aobj.prototype.getStrProps = function() {
//   function act(o, seenProps) {
//     if (o.strPropsMerged)
//       return {val : o["-string"].aval, stop : false};
//     var val = BOTTOM;
//     o.forEachOwnProp(function(pname, pval) {
//       if (pval.enum && !seenProps.memq(pname)) {
//         val = avjoin(val, o[pname].aval);
//         (pname !== "-number") && seenProps.push(pname);
//       }
//     });
//     return {val : val, stop : false};
//   }

//   function combine(avs) {
//     var val = BOTTOM;
//     avs.forEach(function(av) { val = avjoin(val, av); });
//     return val;
//   }
//   return foldProtoChain(this, act, combine);
// };

Aobj.prototype.getStrProps = function() {
  var levels = 0, av = BOTTOM, seenProps = [], o = this;

  while (o !== undefined && levels <= 2) {
    if (o.strPropsMerged)
      av = avjoin(av, o["-string"].aval);
    else
      o.forEachOwnProp(function(pname, pval) {
        if (pval.enum && !seenProps.memq(pname)) {
          av = avjoin(av, o[pname].aval);
          (pname !== "-number") && seenProps.push(pname);
        }
      });
    levels++;
    o = o["-proto"] && heap[o["-proto"].objs[0]];
  }
  return av;
};

// string, Object -> void
// attribs.aval is the property's value
// The property shouldn't be already present, it'll be overwritten
Aobj.prototype.addProp = function(prop, attribs) {
  this[prop] = new Aprop(attribs);
};

// string, Aval -> void
Aobj.prototype.updateExactProp = function(pname, newv) {
  if (this.hasOwnProperty(pname)) {
    var p = this[pname];
    if (!avlt(newv, p.aval)) {
      p.aval = avjoin(p.aval, newv);
      //print("++ts: 3");
      ++timestamp;
    }
    return;
  }
  this[pname] = new Aprop({aval : newv});
  //print("++ts: 4");
  ++timestamp;
};

// string, Aval -> void
// pname is not "-number" or "-string"
Aobj.prototype.updateProp = function(pname, newv) {
  function upd(pname, pval, newv) {
    if (!avlt(newv, pval.aval)) {
      pval.aval = avjoin(pval.aval, newv);
      //print("++ts: 5");
      ++timestamp;
    }
  }

  if (this.hasOwnProperty(pname))
    // either it's not enumerable, or it doesn't interfere with "-number"
    upd(pname, this[pname], newv);
  else {// the new property is enumerable
    if (this.strPropsMerged)
      upd("-string", this["-string"], newv);
    if (this.numPropsMerged && propIsNumeric(pname))
      upd("-number", this["-number"], newv);
    else if (!this.strPropsMerged) {
      this[pname] = new Aprop({aval : newv});
      //print("++ts: 6 " + pname);
      ++timestamp;
    }
  }
};

// Aval -> void
Aobj.prototype.updateNumProps = function(newv) {
  this.mergeNumProps();
  this.updateExactProp("-number", newv);
};

// Aval -> void
Aobj.prototype.updateStrProps = function(newv) {
  this.mergeStrProps();
  this.updateExactProp("-number", newv);
  this.updateExactProp("-string", newv);
};

// merge all numeric properties of the object to one generic number property
Aobj.prototype.mergeNumProps = function() {
  if (this.numPropsMerged) return;
  var av = BOTTOM, self = this;
  this.forEachOwnProp(function(p) {
    if (propIsNumeric(p)) {
      av = avjoin(av, self[p].aval);
      delete self[p]; // don't keep a mix of merged and unmerged properties.
    }
  });
  this.updateExactProp("-number", av); // this bumps timestamp, don't bump again
  this.numPropsMerged = true;
};

Aobj.prototype.mergeStrProps = function() {
  if (this.strPropsMerged) return;
  if (!this.numPropsMerged) this.mergeNumProps();
  var av = BOTTOM, self = this;
  this.forEachOwnProp(function(pname, pval) {
    if (pval.enum) {
      av = avjoin(av, pval.aval);
      if (pname !== "-number") delete self[pname];
    }
  });
  this.updateExactProp("-string", av); // this bumps timestamp, don't bump again
  this.strPropsMerged = true;
};

Aobj.prototype.forEachOwnProp = function(f) {
  for (var p in this)
    if (this[p] instanceof Aprop) 
      f(p, this[p]); // f may ignore its second argument
};

// Aobj.prototype.forEachEnumProp = function(f) {
//   function act(o, seenProps) {
//     for (var p in o) {
//       var pval = o[p];
//       if ((pval instanceof Aprop) && pval.enum
//           && !seenProps.memq(p)) {
//         f(p, pval.aval); // f may ignore its second argument
//         seenProps.push(p);
//       }
//     }
//     return { stop : false };
//   }
//   foldProtoChain(this, act, function() {});
// };

Aobj.prototype.forEachEnumProp = function(f) {
  var levels = 0, av = BOTTOM, seenProps = [], o = this;

  while (o !== undefined && levels <= 2) {
    for (var p in o) {
      var pval = o[p];
      if ((pval instanceof Aprop) && pval.enum && !seenProps.memq(p)) {
        f(p, pval.aval); // f may ignore its second argument
        seenProps.push(p);
      }
    }
    levels++;
    o = o["-proto"] && heap[o["-proto"].objs[0]];
  }
  return av;
};

// optional number -> string
// Returns a multiline string, each line starts with indent (or more) spaces
Aobj.prototype.toString = function(indent) {
  indent = indent || 0;
  var i1 = buildString(indent, " "), i2 = i1 + "  ";

  var s = i1 + "<proto>:\n";
  s += (this["-proto"] ? this["-proto"].toString(indent + 2) : (i2 + "??\n"));
  
  if (this["-fun"]) {
    s += i1 + "<function>:\n" + i2 + this["-fun"].fname.name +
      (this["-fun"].lineno ? ("@" + this["-fun"].lineno) : "") + "\n";
  }

  var self = this;
  this.forEachOwnProp(function(p) {
    var pname = p;
    if (p !== "-number" && p !== "-string")
      pname = p.slice(0, -1);
    s += i1 + pname + ":\n" + self[p].toString(indent + 2);
  });

  return s;
};


// An abstract value is an obj w/ 2 properties: base is a number whose bits
// encode the base values, objs is an array of sorted heap addresses that 
// denotes a set of objects.
const BOTTOM = makeBaseAval(0), ANUM = makeBaseAval(1), ASTR = makeBaseAval(2);
const ATRU = makeBaseAval(4), AFALS = makeBaseAval(8), ABOOL = makeBaseAval(12);
const AUNDEF = makeBaseAval(16), ANULL = makeBaseAval(32);
const RESTARGS = -1;
const INVALID_TIMESTAMP = -1;

// constructor for abstract values. Should only be called from the wrappers.
function Aval() {}

// number -> Aval
function makeBaseAval(base) {
  var v = new Aval();
  v.base = base;
  v.objs = [];
  return v;
}

// number -> Aval
// When creating an abs. value, it can contain at most one object
function makeObjAval(objaddr) {
  var v = new Aval();
  v.base = 0;
  v.objs = [objaddr];
  return v;
}

// string -> Aval
function makeStrLitAval(s) {
  var v = new Aval();
  v.base = 2;
  v.objs = [];
  v.str = s;
  return v;
}

// used by parts of the code that don't know the representation of Aval
Aval.prototype.getBase = function() { return makeBaseAval(this.base); };

// void -> string or undefined
Aval.prototype.getStrLit = function() { return this.str; };

// Merge ATRU and AFALS to one generic boolean in the base b
function mergeBoolsInBase(b) {
  if (b & 8) b |= 4;
  b = ((b & 48) >> 1) | (b & 7);
  return b;
}

// Takes an optional array for cycle detection.
Aval.prototype.toType = function(seenObjs) {
  var i = 1, base = mergeBoolsInBase(this.base), types = [];
  var basetypes = {1 : "number", 2 : "string", 4 : "boolean",
                   8 : "undefined", 16 : "null"};
  while (i <= 16) {
    if ((base & i) === i) types.push(basetypes[i]);
    i *= 2;
  }
  // If uncommented, tags show string constants where possible.
  // if ((base & 2) && (this.str !== undefined)) {
  //   types.rmElmAfterIndex(function(s) {return s === "string";}, 0);
  //   types.push("\"" + this.str + "\"");
  // }
  seenObjs || (seenObjs = []);
  var slen = seenObjs.length;
  this.forEachObj(function (o) {
    types.push(o.toType(seenObjs));
    seenObjs.splice(slen, seenObjs.length);
  });
  if (types.length === 0) return "any";
  normalizeUnionType(types);
  if (types.length === 1) return types[0];
  return ("<" + types.join(" | ") + ">");
};

// void -> Aval
// Used when scalars need to be converted to objects
Aval.prototype.baseToObj = function() {
  var base = this.base;
  if (base & 15 === 0) return this;
  var av = makeBaseAval(0);
  av.objs = this.objs;
  if (base & 2) av = avjoin(av, generic_string_av);
  if (base & 1) av = avjoin(av, generic_number_av);
  if (base & 12) av = avjoin(av, generic_boolean_av);
  return av;
};

// fun takes an Aobj
Aval.prototype.forEachObj = function(fun) {
  var objaddrs = this.objs;
  if (objaddrs.length === 1) // make common case faster
    fun(heap[objaddrs[0]]);
  else
    objaddrs.forEach(function(addr) { fun(heap[addr]); });
};

// Like forEachObj but fun returns a boolean; if it's true, we stop.
Aval.prototype.forEachObjWhile = function(fun) {
  var objaddrs = this.objs, len = objaddrs.length;
  if (len === 1) // make common case faster
    fun(heap[objaddrs[0]]);
  else {
    var i = 0, cont = false;
    while (!cont && i < len)
      cont = fun(heap[objaddrs[i++]]);
  }
};

// string -> Aval
Aval.prototype.getProp = function(pname) {
  var av = BOTTOM;
  this.forEachObj(function(o) { av = avjoin(av, o.getProp(pname) || AUNDEF); });
  return av;
};

// string, Aval -> void
Aval.prototype.updateProp = function(pname, av) {
  this.forEachObj(function(o) { o.updateProp(pname, av); });
};

// array of Aval, node -> Ans
// Call each function with args. args[0] is what THIS is bound to.
// FIXME: record error if rator contains base vals and non-functions
Aval.prototype.callFun = function(args, callNode) {
  var retval = BOTTOM, errval, ans, debugCalls = 0;
  this.baseToObj().forEachObj(function(o) {
    var clos = o.getFun();
    if (!clos) return;
    debugCalls++;
    ans = evalFun(clos, args, false, callNode);
    retval = avjoin(retval, ans.v);
    errval = maybeavjoin(errval, ans.err);
  });

  // var ratorNode = callNode && callNode.children[0];
  // if (!debugCalls) {
  //   var funName, ln = ratorNode.lineno;
  //   switch (ratorNode.type) {
  //   case IDENTIFIER:
  //     funName = ratorNode.name;
  //     break;
  //   case FUNCTION:
  //     funName = ratorNode.fname.name;
  //     break;
  //   case DOT:
  //     if (ratorNode.children[1].type === STRING) {
  //       funName = ratorNode.children[1].value.slice(0, -1);
  //       break;
  //     }
  //     // fall thru
  //   default:
  //     funName = "??";
  //     break;
  //   }
  //   if (args[0] === global_object_av)
  //     print("unknown function: " + funName + ", line " + (ln || "??"));
  //   else
  //     print("unknown method: " + funName + ", line " + (ln || "??"));
  // }
  
  return new Ans(retval, undefined, errval);
};

Aval.prototype.hasNum = function() { return this.base & 1; };

Aval.prototype.hasStr = function() { return this.base & 2; };

Aval.prototype.hasObjs = function() { return this.objs.length > 0; };

// returns true if it can guarantee that the Aval is falsy.
Aval.prototype.isFalsy = function() {
  var base = this.base;
  return this.objs.length === 0 && base !== 0 && 
    (base % 8 === 0 || (base === 2 && this.str === "-"));
};

// returns true if it can guarantee that the Aval is truthy.
Aval.prototype.isTruthy = function() {
  var base = this.base;
  return (this.objs.length === 0 && ((base === 2 && this.str !== "-") ||
                                     base === 4));
};

// optional number -> string
Aval.prototype.toString = function(indent) {
  var i1 = buildString(indent || 0, " ");
  var i = 1, base = mergeBoolsInBase(this.base), types = [];
  var basetypes = {1 : "number", 2 : "string", 4 : "boolean",
                   8 : "undefined", 16 : "null"};
  while (i <= 16) {
    if ((base & i) === i) types.push(basetypes[i]);
    i *= 2;
  }
  return (i1 + "Base: " + types.join(", ") + "\n" +
          i1 + "Objects: " + this.objs.join(", ") + "\n");
};

// Aval, Aval -> Aval
function avjoin(v1, v2) {
  var os1 = v1.objs, os1l = os1.length, os2 = v2.objs, os2l = os2.length;
  var b1 = v1.base, b2 = v2.base, av = makeBaseAval(b1 | b2);

  if (av.base & 2) {
    if (b1 & 2) {
      if (!(b2 & 2) || v1.str === v2.str)
        av.str = v1.str;
    }
    else // (b2 & 2) is truthy
      av.str = v2.str;
  }

  if (os1l === 0)
    av.objs = os2; // need a copy of os2 here? I think not.
  else if (os2l === 0)
    av.objs = os1; // need a copy of os1 here? I think not.
  else if (os1 === os2)
    av.objs = os1;
  else if (os1l === os2l) {
    for (var i = 0; i < os1l; i++) if (os1[i] !== os2[i]) break;
    if (i === os1l) {
      av.objs = v2.objs = os1;
      return av;
    }
    else
      av.objs = arraymerge(os1, os2);
  }
  else // merge the two arrays
    av.objs = arraymerge(os1, os2);
  return av;
}

// Aval or undefined, Aval or undefined -> Aval or undefined
function maybeavjoin(v1, v2) {
  if (!v1) return v2;
  if (!v2) return v1;
  return avjoin(v1, v2);
}

// Aval, Aval -> boolean
// compares abstract values for equality
function aveq(v1, v2) {
  if (v1.base !== v2.base) return false;
  if (v1.str !== v2.str) return false;
  var os1 = v1.objs, os2 = v2.objs, len = os1.length, i; 
  if (len !== os2.length) return false;
  if (os1 === os2) return true;
  for (i=0; i<len; i++) if (os1[i] !== os2[i]) return false;
  // os2 = os1; // Some extra sharing is possible.
  return true;
}

// Aval, Aval -> boolean
// returns true if v1 is less than v2
function avlt(v1, v2) {
  var b1 = v1.base, b2 = v2.base;
  if (b1 > (b1 & b2)) return false;
  if ((b1 & 2) && ("str" in v2) && v2.str !== v1.str)
    return false;
  var os1 = v1.objs, os1l = os1.length, os2 = v2.objs, os2l = os2.length;
  if (os1l === 0 || os1 === os2) return true;
  if (os1l > os2l) return false;
  for (var i = 0, j = 0; i < os1l; i++) {
    while (os2[j] < os1[i]) j++;
    if (j === os2l || os1[i] !== os2[j])
      return false; // there's an elm is os1 that's not in os2
  }
  return true;
}

// function node -> Aval
// If the program doesn't set a function's prototype property, create default.
function makeDefaultProto(n) {
  var paddr = n.defaultProtoAddr;
  var o = new Aobj({ addr: paddr, proto: object_prototype_av });
  o["constructor-"] = new Aprop({aval: makeObjAval(n.addr), enum: false});
  return makeObjAval(paddr);
}

// heap address, Aval -> void
function updateHeapAv(addr, newv) {
  var oldv = heap[addr]; //oldv shouldn't be undefined
  if (!avlt(newv, oldv)) {
    heap[addr] = avjoin(oldv, newv);
    //print("++ts: 7");
    modified[addr] = ++timestamp;
  }
}

// abstract plus
function aplus(v1, v2) {
  if (v1.objs.length !== 0 || v2.objs.length !== 0)
    return makeBaseAval(3);
  var base = ((v1.base | v2.base) & 2); // base is 0 or 2
  if ((v1.base & 61) !== 0 && (v2.base & 61) !== 0) base |= 1;
  return makeBaseAval(base);
}

// Invariant: the following code should know nothing about the representation 
// of abstract values.

////////////////////////////////////////////////////////////////////////////////
/////////////////////  CORE AND CLIENT-SIDE OBJECTS   //////////////////////////
////////////////////////////////////////////////////////////////////////////////

var global_object_av;
var global_object_av_addr;
var object_prototype_av;
var function_prototype_av;
var array_constructor;
var regexp_constructor;
// Used to automatically convert base values to objs and call methods on them
var generic_number_av;
var generic_string_av;
var generic_boolean_av;

// string, function, number -> function node
function funToNode(name, code, arity) {
  var n = new Node({}, {type:FUNCTION});
  n.fname = idNode({}, name);
  n.builtin = true;
  n.addr = newCount();
  pending[count] = 0;
  // built-in funs have no params property but they have an arity property
  // instead. It's only used by the apply method.
  n.arity = arity;
  n.body = code;
  return n;
}

// Aobj, string, function, number -> void
function attachMethod(o, mname, mcode, arity) {
  var n = funToNode(mname, mcode, arity), addr = n.addr;
  var fobj = new Aobj({ addr: addr,
                        proto: function_prototype_av,
                        fun: n });
  o.addProp(mname + "-",  { aval: makeObjAval(addr), enum : false });
  return fobj;
}

// create the JS core objects in heap & fill in core
function initCoreObjs() {

  function toStr(args) { return new Ans(ASTR); }
  function toNum(args) { return new Ans(ANUM); }
  function toBool(args) { return new Ans(ABOOL); }
  function toThis(args) { return new Ans(args[0]); }

  // Global object
  var go = new Aobj({ addr: newCount() }), goav = makeObjAval(count);
  global_object_av = heap[newCount()] = goav;
  global_object_av_addr = count;
  
  // global identifiers and methods
  go.addProp("Infinity-", {aval:ANUM, write:false, enum:false, config:false});
  go.addProp("NaN-", {aval:ANUM, write:false, enum:false, config:false});
  go.addProp("undefined-",{aval:AUNDEF, write:false, enum:false, config:false});

  // Object.prototype
  var op = new Aobj({ addr: newCount() }), opav = makeObjAval(count);
  object_prototype_av = opav;

  // Object.__proto__ (same as Function.prototype)
  var o_p = new Aobj({ addr: newCount(), proto: opav });
  var o_pav = makeObjAval(count);
  function_prototype_av = o_pav;

  // Function.prototype.prototype
  var fpp = new Aobj({ addr: newCount(), proto: opav });
  o_p.addProp("prototype-",{aval:makeObjAval(count), enum:false, config:false});
  fpp.addProp("constructor-", {aval : o_pav, enum : false});

  // Object
  var _Object = (function () {
    // This object is used when Object is called w/out new.
    // In reality the behavior doesn't change. In CFA, when there is no new, 
    // it's better to bind THIS to nonewav instead of the global object.
    new Aobj({ addr: newCount(), proto: opav });
    var nonewav = makeObjAval(count);

    return function (args, withNew) {
      var retval = withNew ? args[0] : nonewav;
      var arg = args[1];
      if (!arg) {
        retval.forEachObj(function (o) { o.updateProto(opav); });
        return new Ans(retval);
      }
      else {
        // throw errorWithCode(CFA_ERROR, "call a suitable constructor, " +
        //                     "hasn't been defined yet. FIXME");
        retval.forEachObj(function (o) { o.updateProto(opav); });
        return new Ans(retval);
      }
    };
  })();
  // Object is a heap var that will contain an Aval that points to o
  var o = attachMethod(go, "Object", _Object, 0), oav = makeObjAval(count);
  o.addProp("prototype-", {aval:opav, write:false, enum:false, config:false});
  op.addProp("constructor-", {aval: oav, enum: false});

  // Function
  var f = new Aobj({addr: newCount(), proto: o_pav}), fav = makeObjAval(count);
  go.addProp("Function-",{aval : fav, enum : false});
  f.addProp("prototype-", {aval:o_pav, write:false, enum:false, config:false});
  o_p.addProp("constructor-", {aval : fav, enum : false});

  // Methods are attached here because o_pav must be defined already.
  attachMethod(go, "isFinite", toBool, 1);
  attachMethod(go, "isNaN", toBool, 1);
  attachMethod(go, "parseInt", toNum, 1);
  attachMethod(op, "hasOwnProperty", toBool, 1);
  attachMethod(op, "toString", toStr, 0);
  attachMethod(op, "valueOf", toThis, 0);
  attachMethod(o_p, "toString", toStr, 0);
  attachMethod(o_p, "call",
               function(args, withNew, cn) {
                 var f = args.shift();
                 args[0] || args.unshift(global_object_av);
                 return f.callFun(args, cn);
               }, 0);
  attachMethod(o_p, "apply",
               function(args, withNew, cn) {
                 var recv = args[1] || global_object_av, a2 = args[2], rands,
                 av, maxArity = 0, restargs, i, ans, retval = BOTTOM, errval;
                 // We can't compute the arguments once for all functions that
                 // may be applied. The functions may have different arity which
                 // impacts what goes to the restargs for each function.
                 args[0].forEachObj(function(o) {
                   var clos = o.getFun(), pslen, i;
                   if (!clos) return;
                   if (clos.builtin)
                     pslen = clos.arity;
                   else
                     pslen = clos.params.length;
                   // compute arguments
                   restargs = BOTTOM;
                   rands = buildArray(pslen, BOTTOM);
                   if (a2) { // a2 is the array passed at the call to apply.
                     a2.forEachObj(function(o) {
                       if (o.numPropsMerged) {
                         av = o.getNumProps();
                         restargs = avjoin(restargs, av);
                         for (i = 0; i < pslen; i++)
                           rands[i] = avjoin(rands[i], av);
                       }
                       else {
                         for (i = 0; i < pslen; i++) {
                           av = o.getOwnExactProp(i + "-") || AUNDEF;
                           rands[i] = avjoin(rands[i], av);
                         }
                         while (true) { // search for extra arguments
                           av = o.getOwnExactProp(i++ + "-");
                           // to find the end of the array, we must see that
                           // an elm *definitely* doesn't exist, different
                           // from AUNDEF
                           if (!av) break;
                           restargs = avjoin(restargs, av);
                         }
                       }
                     });
                   }
                   else {
                     rands = buildArray(pslen, BOTTOM);
                   }
                   // do function call
                   rands.unshift(recv);
                   rands.push(restargs);
                   ans = evalFun(clos, rands, false, cn);
                   retval = avjoin(retval, ans.v);
                   errval = maybeavjoin(errval, ans.err);
                 });
                 return new Ans(retval, undefined, errval);
               }, 2);  

  (function () {
    // Array.prototype
    var ap = new Aobj({ addr: newCount(), proto: opav });
    var apav = makeObjAval(count);

    function putelms(args) {
      var i, len = args.length;
      args[0].forEachObj(function (o) {
        for (i = 1; i < len; i++) o.updateNumProps(args[i]);
      });
      return new Ans(ANUM);
    }

    function getelms(args) {
      var av = BOTTOM;
      args[0].forEachObj(function (o) { av = avjoin(av, o.getNumProps()); });
      return new Ans(av);
    }
    
    attachMethod(ap, "concat",
                 // lose precision by not creating a new array
                 function(args) {
                   var thisarr = args[0], av = BOTTOM;
                   // if arg is base, join it, if it's array join its elms
                   for (var i = 1, l = args.length; i < l; i++) {
                     var avarg = args[i];
                     av = avjoin(av, avarg.getBase());
                     avarg.forEachObj(function(o) {
                       if (o.isArray()) av = avjoin(av, o.getNumProps());
                     });
                     thisarr.forEachObj(function(o) { o.updateNumProps(av); });
                   }
                   return new Ans(thisarr);
                 }, 0);
    attachMethod(ap, "join", toStr, 1);
    attachMethod(ap, "pop", getelms, 0);
    attachMethod(ap, "push", putelms, 0);
    attachMethod(ap, "slice", toThis, 2);
    attachMethod(ap, "sort", toThis, 1);
    attachMethod(ap, "splice", toThis, 0);
    attachMethod(ap, "shift", getelms, 0);
    attachMethod(ap, "toString", toStr, 0);
    attachMethod(ap, "unshift", putelms, 0);

    // Array
    var _Array = (function () {
      // This object is used when Array is called w/out new 
      new Aobj({ addr: newCount(), proto: apav });
      var nonewav = makeObjAval(count);

      return function(args, withNew) {
        var retval = withNew ? args[0] : nonewav;
        var arglen = args.length;
        retval.forEachObj(function (o) {
          o.updateProto(apav);
          if (o.getOwnExactProp("length-"))
            o.updateProp("length-", ANUM);
          else
            o.addProp("length-", {aval : ANUM, enum : false});
        });
        if (arglen <= 2) // new Array(), new Array(size)
          ;
        else { // new Array(elm1, ... , elmN)
          retval.forEachObj(function (o) {
            for (var i = 1; i < arglen; i++)
              o.updateProp((i - 1) + "-", args[i]);
          });
        }
        return new Ans(retval);
      };
    })();
    array_constructor = _Array;
    var a = attachMethod(go, "Array", _Array, 0), aav = makeObjAval(count);
    a.addProp("prototype-", {aval:apav, write:false, enum:false, config:false});
    ap.addProp("constructor-", {aval : aav, enum : false});
  })();

  (function () {
    // Number.prototype
    var np = new Aobj({ addr: newCount(), proto: opav });
    var npav = makeObjAval(count);
    attachMethod(np, "toString", toStr, 0);
    attachMethod(np, "valueOf", toNum, 0);
    // create generic number object
    new Aobj({ addr: newCount(), proto: npav});
    generic_number_av = makeObjAval(count);

    // Number
    function _Number(args, withNew) {
      if (withNew) {
        args[0].forEachObj(function (o) { o.updateProto(npav); });
        return new Ans(args[0]);
      }
      return new Ans(ANUM);
    }
    var n = attachMethod(go, "Number", _Number, 0), nav = makeObjAval(count);
    n.addProp("prototype-", {aval:npav, write:false, enum:false, config:false});
    np.addProp("constructor-", {aval : nav, enum : false});
  })();

  (function () {
    // String.prototype
    var sp = new Aobj({ addr: newCount(), proto: opav });
    var spav = makeObjAval(count);
    attachMethod(sp, "charAt", toStr, 1);
    attachMethod(sp, "charCodeAt", toNum, 1);
    attachMethod(sp, "indexOf", toNum, 2);
    attachMethod(sp, "lastIndexOf", toNum, 2);
    // all Arrays returned by calls to match are merged in one
    var omatch = new Aobj({ addr: newCount() });
    var omatchav = avjoin(ANULL, makeObjAval(count));
    array_constructor([omatchav], true);
    omatch.updateNumProps(ASTR);
    omatch.addProp("index-", {aval : ANUM});
    omatch.addProp("input-", {aval : ASTR});
    attachMethod(sp, "match", function(args) { return new Ans(omatchav); }, 1);
    attachMethod(sp, "replace", toStr, 2);
    attachMethod(sp, "slice", toStr, 2);
    attachMethod(sp, "substr", toStr, 2);
    attachMethod(sp, "substring", toStr, 2);
    attachMethod(sp, "toLowerCase", toStr, 0);
    attachMethod(sp, "toString", toStr, 0);
    attachMethod(sp, "toUpperCase", toStr, 0);
    // all Arrays returned by calls to split are merged in one
    var osplit = new Aobj({ addr: newCount() });
    var osplitav = makeObjAval(count);
    array_constructor([osplitav], true);
    osplit.updateNumProps(ASTR);
    attachMethod(sp, "split", function(args) {
      return new Ans(osplitav);
    }, 2);
    attachMethod(sp, "valueOf", toStr, 0);
    // create generic string object
    new Aobj({ addr: newCount(), proto: spav });
    generic_string_av = makeObjAval(count);

    // String
    function _String(args, withNew) {
      if (withNew) {
        args[0].forEachObj(function (o) { o.updateProto(spav); });
        return new Ans(args[0]);
      }
      return new Ans(ASTR);
    }
    var s = attachMethod(go, "String", _String, 1), sav = makeObjAval(count);
    s.addProp("prototype-", {aval:spav, write:false, enum:false, config:false});
    sp.addProp("constructor-", {aval : sav, enum : false});
    attachMethod(s, "fromCharCode", toStr, 0);
  })();

  (function () {
    // Error.prototype
    var ep = new Aobj({ addr: newCount(), proto: opav });
    var epav = makeObjAval(count);
    attachMethod(ep, "toString", toStr, 0);

    // Error
    function _Error(args) {
      args[0].forEachObj(function (o) {
        o.updateProto(epav);
        o.updateProp("message-", args[1] || ASTR);
      });
      return new Ans(args[0]);
    }
    var e = attachMethod(go, "Error", _Error, 1), eav = makeObjAval(count);
    e.addProp("prototype-", {aval:epav, write:false, enum:false, config:false});
    ep.addProp("constructor-", {aval : eav, enum : false});
    ep.addProp("name-", {aval : ASTR, enum : false});

    // SyntaxError.prototype
    var sep = new Aobj({ addr: newCount(), proto: epav });
    var sepav = makeObjAval(count);

    // SyntaxError
    function _SyntaxError(args) {
      args[0].forEachObj(function (o) { 
        o.updateProto(sepav); 
        o.addProp("message-", {aval : ASTR});
      });
      return new Ans(args[0]);
    }
    var se = attachMethod(go, "SyntaxError", _SyntaxError, 1);
    var seav = makeObjAval(count);
    se.addProp("prototype-",{aval:sepav, write:false, enum:false,config:false});
    sep.addProp("constructor-", {aval : seav, enum : false});
    sep.addProp("name-", {aval : ASTR});
  })();

  (function () {
    // RegExp.prototype
    var rp = new Aobj({ addr: newCount(), proto: opav });
    var rpav = makeObjAval(count);
    // all Arrays returned by calls to exec are merged in one
    var oexec = new Aobj({ addr: newCount() });
    var oexecav = avjoin(ANULL, makeObjAval(count));
    array_constructor([oexecav], true);
    oexec.updateNumProps(ASTR);
    oexec.addProp("index-", {aval : ANUM});
    oexec.addProp("input-", {aval : ASTR});
    attachMethod(rp, "exec", function(args) { return new Ans(oexecav); }, 1);
    attachMethod(rp, "test", toBool, 1);

    // RegExp
    function _RegExp(args) {
      args[0].forEachObj(function (o) {
        o.updateProto(rpav);
        o.addProp("global-",{aval:ABOOL, write:false, enum:false,config:false});
        o.addProp("ignoreCase-", 
                  {aval:ABOOL, write:false, enum:false, config:false});
        o.addProp("lastIndex-", {aval : ANUM, enum : false, config : false});
        o.addProp("multiline-", 
                  {aval:ABOOL, write:false, enum:false, config:false});
        o.addProp("source-",{aval:ASTR, write:false, enum:false, config:false});
      });
      return new Ans(args[0]);
    }
    regexp_constructor = _RegExp;
    var r = attachMethod(go, "RegExp", _RegExp, 2), rav = makeObjAval(count);
    r.addProp("prototype-", {aval:rpav, write:false, enum:false, config:false});
    rp.addProp("constructor-", {aval : rav, enum : false});
  })();

  (function () {
    // Date.prototype
    var dp = new Aobj({ addr: newCount(), proto: opav });
    var dpav = makeObjAval(count);
    attachMethod(dp, "getDate", toNum, 0);
    attachMethod(dp, "getDay", toNum, 0);
    attachMethod(dp, "getFullYear", toNum, 0);
    attachMethod(dp, "getHours", toNum, 0);
    attachMethod(dp, "getMilliseconds", toNum, 0);
    attachMethod(dp, "getMinutes", toNum, 0);
    attachMethod(dp, "getMonth", toNum, 0);
    attachMethod(dp, "getSeconds", toNum, 0);
    attachMethod(dp, "getTime", toNum, 0);
    attachMethod(dp, "getTimezoneOffset", toNum, 0);
    attachMethod(dp, "getYear", toNum, 0);
    attachMethod(dp, "setTime", toNum, 1);
    attachMethod(dp, "toString", toStr, 0);
    attachMethod(dp, "valueOf", toNum, 0);

    // Date
    function _Date(args, withNew) {
      if (withNew) {
        args[0].forEachObj(function (o) { o.updateProto(dpav); });
        return new Ans(args[0]);
      }
      return new Ans(ASTR);
    }
    var d = attachMethod(go, "Date", _Date, 0), dav = makeObjAval(count);
    d.addProp("prototype-", {aval:dpav, write:false, enum:false, config:false});
    dp.addProp("constructor-", {aval : dav, enum : false});
  })();

  (function () {
    // Math
    var m = new Aobj({ addr: newCount(), proto: opav });
    var mav = makeObjAval(count);
    go.addProp("Math-", {aval : mav, enum : false});
    m.addProp("constructor-", {aval : oav, enum : false});
    m.addProp("E-", {aval : ANUM, write : false, enum : false, config : false});
    m.addProp("LN10-",{aval : ANUM, write : false, enum : false, config:false});
    m.addProp("LN2-", {aval : ANUM, write : false, enum : false, config:false});
    m.addProp("LOG10E-", {aval : ANUM, write:false, enum:false, config:false});
    m.addProp("LOG2E-", {aval : ANUM, write:false, enum:false, config:false});
    m.addProp("PI-", {aval : ANUM, write : false, enum : false, config :false});
    m.addProp("SQRT1_2-", {aval : ANUM, write:false, enum:false, config:false});
    m.addProp("SQRT2-",{aval:ANUM, write:false, enum:false, config:false});
    attachMethod(m, "abs", toNum, 1);
    attachMethod(m, "acos", toNum, 1);
    attachMethod(m, "asin", toNum, 1);
    attachMethod(m, "atan", toNum, 1);
    attachMethod(m, "atan2", toNum, 1);
    attachMethod(m, "ceil", toNum, 1);
    attachMethod(m, "cos", toNum, 1);
    attachMethod(m, "exp", toNum, 1);
    attachMethod(m, "floor", toNum, 1);
    attachMethod(m, "log", toNum, 1);
    attachMethod(m, "max", toNum, 0);
    attachMethod(m, "min", toNum, 0);
    attachMethod(m, "pow", toNum, 2);
    attachMethod(m, "random", toNum, 0);
    attachMethod(m, "round", toNum, 1);
    attachMethod(m, "sin", toNum, 1);
    attachMethod(m, "sqrt", toNum, 1);
    attachMethod(m, "tan", toNum, 1);
  })();

  (function () {
    // Boolean.prototype
    var bp = new Aobj({ addr: newCount(), proto: opav });
    var bpav = makeObjAval(count);
    attachMethod(bp, "toString", toStr, 0);
    attachMethod(bp, "valueOf", toBool, 0);
    // create generic boolean object
    new Aobj({ addr: newCount(), proto: bpav });
    generic_boolean_av = makeObjAval(count);

    // Boolean
    function _Boolean(args, withNew) {
      if (withNew) {
        args[0].forEachObj(function (o) { o.updateProto(bpav); });
        return new Ans(args[0]);
      }
      return new Ans(ABOOL);
    }
    var b = attachMethod(go, "Boolean", _Boolean, 1), bav = makeObjAval(count);
    b.addProp("prototype-", {aval:bpav, write:false, enum:false, config:false});
    bp.addProp("constructor-", {aval : bav, enum : false});
  })();
}


////////////////////////////////////////////////////////////////////////////////
//////////////////////////   EVALUATION PREAMBLE   /////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// frame, identifier node, Aval -> void
function frameSet(fr, param, val) {
  fr[param.addr] = [val, timestamp]; // record when param was bound to val
}

// frame, identifier node -> Aval
function frameGet(fr, param) {
  var pa = param.addr, binding = fr[pa];
  if (binding[1] < modified[pa]) {
    // if binding changed in heap, change it in frame to be sound
    binding[0] = avjoin(binding[0], heap[pa]);
    binding[1] = timestamp;
  }
  return binding[0];
}

// fun. node, array of Aval, timestamp  -> [Aval, Aval] or false
function searchSummary(n, args, ts) {
  var n_summaries = summaries[n.addr], insouts, summary;
  if (n_summaries.ts < ts) return false;
  insouts = n_summaries.insouts;
  // Start from the end to find the elm that was pushed last
  for (var i = insouts.length - 1; i >= 0; i--) {
    summary = insouts[i];
    // If no widening, turn avlt to aveq in the next line.
    if (arrayeq(avlt, args, summary[0])) return summary.slice(-2);
  }
  return false;
}

// function node -> boolean
// check if any summary exists for this function node
function existsSummary(n) {
  return summaries[n.addr].ts !== INVALID_TIMESTAMP;
}

// fun. node, array of Aval, Aval, Aval or undefined, timestamp  -> void
function addSummary(n, args, retval, errval, ts) {
  var addr = n.addr, summary = summaries[addr];
  if (summary.ts === ts)
    summary.insouts.push([args, retval, errval]);
  else if (summary.ts < ts) { // discard summaries for old timestamps.
    summary.ts = ts;
    summary.insouts = [[args, retval, errval]];
  }
  // join new summary w/ earlier ones.
  var insjoin = summary.type[0];
  for (var i = 0, len = insjoin.length; i < len; i++)
    insjoin[i] = avjoin(insjoin[i], args[i] || AUNDEF/*arg mismatch*/);
  summary.type[1] = avjoin(summary.type[1], retval);
  summary.type[2] = maybeavjoin(summary.type[2], errval);
}

function showSummaries() {
  for (var addr in summaries) {
    var f = heap[addr].getFun();
    //print(f.fname.name + ": " + funToType(f));
  }
}

// function node, array of Aval -> number or undefined
// How evalFun interprets the return value of searchPending
// Zero: new frame on the stack
// Positive number: throw to clear the stack b/c of timestamp increase
// Negative number: throw to clear the stack during recursion
// undefined: return w/out throwing during recursion
function searchPending(n, args) {
  var bucket = pending[n.addr], len = bucket.length, i;
  // We use the number of pending calls to n to clear the stack.
  if (len === 0) return 0;
  if (bucket[0].ts < timestamp) return len;
  // Invariant: no two sets of args are related in \sqsubseteq.
  for (i = 0; i < len; i++) {
    // No need to keep going, a more general frame is pending.
    if (arrayeq(avlt, args, bucket[i].args))
      return;
    // The deeper frame can be widened, throw to it.
    else if (arrayeq(avlt, bucket[i].args, args)) 
      return i - len;
  }
  return 0;
}

// function node, {args, timestamp} -> void
function addPending(n, elm) { pending[n.addr].push(elm); }

// function node -> {args, timestamp}
function rmPending(n) {
  // // Uncomment when debugging
  // var elm = pending[n.addr].pop();
  // if (!elm) throw errorWithCode(CFA_ERROR, "Remove from empty pending.");
  // return elm;
  return pending[n.addr].pop();
}

// evalExp & friends use Ans to return tuples
function Ans(v, fr, err) {
  this.v = v; // evalExp puts abstract values here, evalStm puts statements
  this.fr = fr; // frame
  err && (this.err = err); // Aval for exceptions thrown
}

// Initialize the heap for each fun decl, var decl and heap var.
// Because of this function, we never get undefined by reading from heap.
// Must be run after initGlobals and after initCoreObjs.
// Most Aobj`s that aren't core are created here.
var initDeclsInHeap, initDeclsInHeap_override;

(function() {
  var walkerobj = walkASTgenerator(), override = walkerobj.override;
  initDeclsInHeap = walkerobj.walkAST;
  initDeclsInHeap_override = override;

  override(REGEXP, function(n) {
    new Aobj({ addr: n.addr });
    regexp_constructor([makeObjAval(n.addr)]);
  });

  // FIXME?: when array elms have the same type, they can be prematurely merged
  // to help the speed of the algo e.g. in 3d-cube
  override(ARRAY_INIT, function(n) {
    new Aobj({ addr: n.addr });
    array_constructor([makeObjAval(n.addr)], true);
    n.children.forEach(initDeclsInHeap);
  });

  override(OBJECT_INIT, function(n) {
    new Aobj({ addr: n.addr, proto: object_prototype_av });
    n.children.forEach(function(prop) {
      initDeclsInHeap(prop.children[0]);
      initDeclsInHeap(prop.children[1]);
    });
  });

  override(NEW_WITH_ARGS, function(n) {
    new Aobj({ addr: n.addr });
    initDeclsInHeap(n.children[0]);
    n.children[1].children.forEach(initDeclsInHeap);
  });

  override(TRY, function(n) {
    initDeclsInHeap(n.tryBlock);
    n.catchClauses.forEach(function(c) {
      if (c.exvar.kind === HEAP) heap[c.exvar.addr] = BOTTOM;
      c.guard && initDeclsInHeap(c.guard);
      initDeclsInHeap(c.block);
    });
    n.finallyBlock && initDeclsInHeap(n.finallyBlock);
  });

  function _function(n) {
    var objaddr = n.addr, fn = n.fname, 
    obj = new Aobj({ addr: objaddr, fun: n, proto: function_prototype_av });
    obj.addProp("prototype-", {aval:BOTTOM, enum:false});
    if (fn.kind === HEAP)
      heap[fn.addr] = makeObjAval(objaddr);
    n.params.forEach(function(p) {if (p.kind === HEAP) heap[p.addr] = BOTTOM;});
    flags[objaddr] = n;
    // initialize summaries and pending
    summaries[objaddr] = {
      ts: INVALID_TIMESTAMP,
      insouts: [],
      type: [buildArray(n.params.length + 1, BOTTOM), BOTTOM]//arg 0 is for THIS
    };
    pending[objaddr] = [];
    initDeclsInHeap(n.body);
  }

  override(FUNCTION, _function);

  override(SCRIPT, function(n) {
    n.funDecls.forEach(_function);
    n.varDecls.forEach(function(vd){if (flags[vd.addr]) heap[vd.addr]=BOTTOM;});
    n.children.forEach(initDeclsInHeap);
  });
})();

// void -> Aval
// Used to analyze functions that aren't called
function makeGenericObj() {
  new Aobj({ addr: newCount(), proto: object_prototype_av });
  return makeObjAval(count);
}


////////////////////////////////////////////////////////////////////////////////
//////////////////////////   EVALUATION FUNCTIONS   ////////////////////////////
////////////////////////////////////////////////////////////////////////////////

// function for evaluating lvalues
// node, Ans, optional Aval -> Ans
// use n to get an lvalue, do the assignment and return the rvalue
var evalLval;

(function() {
  var walkerobj = walkASTgenerator(), override = walkerobj.override;
  evalLval = walkerobj.walkAST;

  function _stackref(n, ans, oldlval) {
    if (n.assignOp) {
      if (n.assignOp === PLUS)
        ans.v = aplus(ans.v, oldlval);
      else
        ans.v = ANUM;
    }
    var newav = avjoin(frameGet(ans.fr, n), ans.v);
    frameSet(ans.fr, n, newav);
    // if n is a heap var, update heap so its heap refs get the correct Aval.
    if (flags[n.addr]) updateHeapAv(n.addr, newav);
    return ans;
  }

  function _heapref(n, ans, oldlval) {
    if (n.assignOp) {
      if (n.assignOp === PLUS)
        ans.v = aplus(ans.v, oldlval);
      else
        ans.v = ANUM;
    }
    updateHeapAv(n.addr, ans.v);
    return ans;
  }

  override(IDENTIFIER, function(n, ans, oldlval) {
    if (n.kind === STACK)
      return _stackref(n, ans, oldlval);
    else
      return _heapref(n, ans, oldlval);
  });

  override(INDEX, function(n, ans, oldlval) {
    var rval = ans.v, fr = ans.fr, errval, ch = n.children;
    if (n.assignOp) {
      if (n.assignOp === PLUS)
        rval = aplus(rval, oldlval);
      else
        rval = ANUM;
    }
    var prop = ch[1];
    var ansobj = evalExp(ch[0], fr), avobj = ansobj.v;
    fr = ansobj.fr;
    errval = ansobj.err;
    // Unsound: ignore everything the index can eval to except numbers & strings
    if (prop.type === STRING)
      avobj.updateProp(prop.value, rval);
    else {
      var ansprop = evalExp(prop, fr), avprop = ansprop.v;
      fr = ansprop.fr;
      errval = maybeavjoin(errval, ansprop.err);
      if (avprop.hasNum()) 
        avobj.forEachObj(function(o) { o.updateNumProps(rval); });
      if (avprop.hasStr()) {
        var slit = avprop.getStrLit();
        if (slit)
          avobj.updateProp(slit, rval);
        else
          avobj.forEachObj(function(o) { o.updateStrProps(rval); });
      }
    }
    return new Ans(rval, fr, maybeavjoin(errval, ans.err));
  });

  function _dot(n, ans, oldlval) {
    if (n.assignOp) {
      if (n.assignOp === PLUS)
        ans.v = aplus(ans.v, oldlval);
      else
        ans.v = ANUM;
    }
    var ch = n.children, ans2 = evalExp(ch[0], ans.fr);
    ans2.v.updateProp(ch[1].value, ans.v);
    ans.fr = ans2.fr;
    ans.err = maybeavjoin(ans.err, ans2.err);
    return ans;
  }

  override(DOT, _dot);
  override(DOT_PROTO, _dot);

  override(ARGUMENTS, function(n, ans, oldlval) {
    // FIXME: handle assignment to the arguments array
    return ans;
  });

  // in extremely rare cases, you can see a CALL as the lhs of an assignment.
  override(CALL, function(n, ans, oldlval) {
    return ans;
  });
})();

// function for evaluating expressions
// node, frame -> Ans
var evalExp, evalExp_override;

(function() {
  var walkerobj = walkASTgenerator(), override = walkerobj.override;
  evalExp = walkerobj.walkAST;
  evalExp_override = override;

  function _stackref(n, fr) { return new Ans(frameGet(fr, n), fr); }

  function _heapref(n, fr) { return new Ans(heap[n.addr], fr); }

  override(IDENTIFIER, function(n, fr) {
    if (n.kind === STACK)
      return _stackref(n, fr);
    else
      return _heapref(n, fr);
  });

  override(NUMBER, function(n, fr) { return new Ans(ANUM, fr); });

  override(STRING, 
           function(n, fr) { return new Ans(makeStrLitAval(n.value), fr); });

  override(TRUE, function(n, fr) { return new Ans(ATRU, fr); });

  override(FALSE, function(n, fr) { return new Ans(AFALS, fr); });

  override(NULL, function(n, fr) { return new Ans(ANULL, fr); });

  override(REGEXP, function(n, fr){ return new Ans(makeObjAval(n.addr), fr); });

  override(THIS, function(n, fr) { return new Ans(fr.thisav, fr); });

  function _unary2num(n, fr) {
    var ans = evalExp(n.children[0], fr);
    ans.v = ANUM;
    return ans;
  }

  [UNARY_PLUS, UNARY_MINUS, INCREMENT, DECREMENT, BITWISE_NOT].forEach(
    function(tt) { override(tt, _unary2num); });

  override(NOT, function(n, fr) {
    var ans = evalExp(n.children[0], fr), av = ans.v;
    if (av.isTruthy())
      ans.v = AFALS;
    else if (av.isFalsy())
      ans.v = ATRU;
    else
      ans.v = ABOOL;
    return ans;
  });

  override(TYPEOF, function(n, fr) {
    var ans = evalExp(n.children[0], fr);
    ans.v = ASTR;
    return ans;
  });

  override(VOID, function(n, fr) {
    var ans = evalExp(n.children[0], fr);
    ans.v = AUNDEF;
    return ans;
  });

  override(DELETE, function(n, fr) { // unsound: I'm not deleting anything
    var ans = evalExp(n.children[0], fr);
    ans.v = ABOOL;
    return ans;
  });

  override(IN, function(n, fr) {
    var ans1 = evalExp(n.children[0], fr);
    var ans2 = evalExp(n.children[1], ans1.fr);
    ans2.err = maybeavjoin(ans1.err, ans2.err);
    var pname = ans1.v.getStrLit(), ans2v = ans2.v;
    if (!ans2v.hasObjs())
      ans2.v = AFALS;
    else if (!pname)
      ans2.v = ABOOL;
    else {
      var av = BOTTOM;
      ans2v.forEachObj(function(o) {
        if (!o.getProp(pname))
          av = avjoin(av, AFALS);
        else
          av = avjoin(av, ATRU);
      });
      ans2.v = av;
    }
    return ans2;
  });

  function _binary2bool(n, fr) {
    var ans1 = evalExp(n.children[0], fr);
    var ans2 = evalExp(n.children[1], ans1.fr);
    ans2.v = ABOOL;
    ans2.err = maybeavjoin(ans1.err, ans2.err);
    return ans2;
  }

  [EQ, NE, STRICT_EQ, STRICT_NE, LT, LE, GE, GT, INSTANCEOF].forEach(
    function(tt) { override(tt, _binary2bool); });

  function _andor(pred1, pred2) {
    return function(n, fr) {
      var ans1 = evalExp(n.children[0], fr), av = ans1.v;
      if (pred1.call(av)) return ans1;
      var ans2 = evalExp(n.children[1], ans1.fr);
      ans2.err = maybeavjoin(ans1.err, ans2.err);
      if (!pred2.call(av)) ans2.v = avjoin(av, ans2.v);
      return ans2;
    }
  }

  override(AND, _andor(Aval.prototype.isFalsy, Aval.prototype.isTruthy));
  override(OR, _andor(Aval.prototype.isTruthy, Aval.prototype.isFalsy));

  override(PLUS, function(n, fr) {
    var ans1 = evalExp(n.children[0], fr);
    var ans2 = evalExp(n.children[1], ans1.fr);
    ans2.v = aplus(ans1.v, ans2.v);
    ans2.err = maybeavjoin(ans1.err, ans2.err);
    return ans2;
  });

  function _binary2num(n, fr) {
    var ans1 = evalExp(n.children[0], fr);
    var ans2 = evalExp(n.children[1], ans1.fr);
    ans2.v = ANUM;
    ans2.err = maybeavjoin(ans1.err, ans2.err);
    return ans2;
  }

  [MINUS, MUL, DIV, MOD, BITWISE_OR, BITWISE_XOR, BITWISE_AND, 
   LSH, RSH, URSH].forEach(function(tt) { override(tt, _binary2num); });

  override(PLUS_ASSIGN, function(n, fr) {
    var ch = n.children;
    // recomputing ch[0] for += is better than checking every lhs in evalLval
    var ans = evalExp(ch[0], fr);
    return evalLval(ch[0], evalExp(ch[1], fr), ans.v);
  });

  override(ASSIGN, function(n, fr) { 
    return evalLval(n.children[0], evalExp(n.children[1], fr));
  });

  override(HOOK, function(n, fr) {
    var ch = n.children;
    var ans = evalExp(ch[0], fr), test = ans.v, av = BOTTOM, err = ans.err;
    if (!test.isFalsy()) {
      ans = evalExp(ch[1], ans.fr);
      av = avjoin(av, ans.v);
      err = maybeavjoin(err, ans.err);
    }
    if (!test.isTruthy()) {
      ans = evalExp(ch[2], ans.fr);
      av = avjoin(av, ans.v);
      err = maybeavjoin(err, ans.err);
    }
    return new Ans(av, ans.fr, err);
  });

  override(FUNCTION, 
           function(n, fr) { return new Ans(makeObjAval(n.addr), fr); });

  override(COMMA, function(n, fr) {
    var ans, av, errval;
    n.children.forEach(function(exp) {
      ans = evalExp(exp, fr);
      av = ans.v; // keep last one
      fr = ans.fr;
      errval = maybeavjoin(errval, ans.err);
    });
    ans.v = av;
    ans.err = errval;
    return ans;
  });

  override(OBJECT_INIT, function(n, fr) {
    var ans, errval, objaddr = n.addr, newobj = heap[objaddr];
    n.children.forEach(function(pinit) {
      ans = evalExp(pinit.children[1], fr);
      fr = ans.fr;
      newobj.updateProp(pinit.children[0].value, ans.v);
      errval = maybeavjoin(errval, ans.err);
    });
    return new Ans(makeObjAval(objaddr), fr, errval);
  });

  override(ARRAY_INIT, function(n, fr) {
    var ans, errval, arrayaddr = n.addr, newarray = heap[arrayaddr];
    n.children.forEach(function(elm, i) {
      ans = evalExp(elm, fr);
      fr = ans.fr;
      newarray.updateProp(i + "-", ans.v);
      errval = maybeavjoin(errval, ans.err);
    });
    return new Ans(makeObjAval(arrayaddr), fr, errval);
  });

  override(DOT_PROTO, function(n, fr) {
    var ans = evalExp(n.children[0], fr), ans2, av = BOTTOM, 
    av2, errval = ans.err;
    // FIXME: record error if ans.v contains base values
    ans.v.forEachObj(function(o) {
      var clos = o.getFun(), proto;
      if (!clos) { // if o isn't a function, this is just a property access
        av2 = o.getProp("prototype-");
        av = avjoin(av, av2 || AUNDEF);
      }
      else {
        proto = o.getProp("prototype-");
        if (!aveq(BOTTOM, proto))
          av = avjoin(av, proto);
        else {// create default prototype and return it
          proto = makeDefaultProto(clos);
          o.updateProp("prototype-", proto);
          av = avjoin(av, proto);
        }
      }
    });
    ans2 = new Ans(av, ans.fr, errval);
    ans2.thisav = ans.v; // used by method calls
    return ans2;
  });

  override(INDEX, function(n, fr) {
    var ansobj = evalExp(n.children[0], fr), avobj = ansobj.v.baseToObj(),
    prop = n.children[1], errval = ansobj.err, av , ans;
    fr = ansobj.fr;
    // If [] notation is used with a constant, try to be precise.
    // Unsound: ignore everything the index can eval to except numbers & strings
    if (prop.type === STRING)
      av = avobj.getProp(prop.value);
    else {
      var ansprop = evalExp(prop, fr), avprop = ansprop.v;
      fr = ansprop.fr;
      errval = maybeavjoin(errval, ansprop.err);
      av = BOTTOM;
      if (avprop.hasNum())
        avobj.forEachObj(function(o) { av = avjoin(av, o.getNumProps()); });
      if (avprop.hasStr()) {
        var slit = avprop.getStrLit();
        if (slit)
          av = avjoin(av, avobj.getProp(slit));
        else
          avobj.forEachObj(function(o) { av = avjoin(av, o.getStrProps()); });
      }
    }
    ans = new Ans(av, fr, errval);
    ans.thisav = avobj;
    return ans;
  });

  override(DOT, function(n, fr) {
    var ans = evalExp(n.children[0], fr), avobj = ans.v.baseToObj();
    ans.thisav = avobj; // used by method calls
    ans.v = avobj.getProp(n.children[1].value);
    return ans;
  });

  override(CALL, function(n, fr) {
    // To see if the analysis reaches some program point in all.js, add some 
    // call: e10sDebug(some_msg) and uncomment the following code.
    // if (n.children[0].value === "e10sDebug") {
    //   print(n.children[1].children[0].value);
    // }

    var ans = evalExp(n.children[0], fr), ans1, errval, rands = [];
    rands.push(ans.thisav ? ans.thisav : global_object_av);
    fr = ans.fr;
    errval = ans.err;
    // evaluate arguments
    n.children[1].children.forEach(function(rand) {
      ans1 = evalExp(rand, fr);
      rands.push(ans1.v);
      fr = ans1.fr;
      errval = maybeavjoin(errval, ans1.err);
    });
    // call each function that can flow to the operator position
    ans = ans.v.callFun(rands, n);
    ans.fr = fr;
    ans.err = maybeavjoin(errval, ans.err);
    return ans;
  });

  override(NEW_WITH_ARGS, function(n, fr) {
    var ch = n.children, rands = [], retval = BOTTOM;
    var ans = evalExp(ch[0], fr), ans1, errval;
    var objaddr = n.addr, thisobj = heap[objaddr];
    rands.push(makeObjAval(objaddr));
    fr = ans.fr;
    errval = ans.err;
    // evaluate arguments
    ch[1].children.forEach(function(rand) {
      ans1 = evalExp(rand, fr);
      rands.push(ans1.v);
      fr = ans1.fr;
      errval = maybeavjoin(errval, ans1.err);
    });
    // FIXME: record error if rator contains base vals and non-functions
    ans.v.baseToObj().forEachObj(function(o) {
      var clos = o.getFun(), proto;
      if (!clos) return;
      proto = o.getProp("prototype-");
      if (aveq(BOTTOM, proto)) {
        // create default prototype & use it
        proto = makeDefaultProto(clos);
        o.updateProp("prototype-", proto);
      }
      thisobj.updateProto(proto);
      // if a fun is called both w/ and w/out new, assume it's a constructor
      clos.withNew = true;
      ans = evalFun(clos, rands, true, n);
      if (clos.hasReturn) // constructor uses return
        retval = avjoin(retval, ans.v);
      else // constructor doesn't use return
        retval = avjoin(retval, rands[0]);
      errval = maybeavjoin(errval, ans.err);
    });
    return new Ans(retval, fr, errval);
  });

  override(ARGUMENTS, function(n, fr) {
    var index = n.children[0], ps = n.arguments;
    var restargs = fr[RESTARGS] || BOTTOM, ans, av, errval;
    if (index.type === NUMBER) {
      var iv = index.value;
      if (iv < 0)
        av = AUNDEF;
      else if (iv < ps.length)
        av = frameGet(fr, ps[iv]);
      else
        av = restargs; // unsound: not checking if iv > #args
    }
    else {
      ans = evalExp(index, fr);
      fr = ans.fr;
      errval = ans.err;
      av = BOTTOM;
      // when we don't know the index, we return the join of all args
      ps.forEach(function(p) { av = avjoin(av, frameGet(fr, p)); });
      av = avjoin(av, restargs);
    }
    return new Ans(av, fr, errval);
  });
})();

// function for evaluating statements
// node, frame -> Ans
// Evaluate the statement and find which statement should be executed next.
var evalStm;

(function() {
  var walkerobj = walkASTgenerator(), override = walkerobj.override;
  evalStm = walkerobj.walkAST;

  override(SEMICOLON, function(n, fr) {
    var ans = evalExp(n.expression, fr);
    ans.v = n.kreg;
    return ans;
  });

  function _next(n, fr) { return new Ans(n.kreg, fr); }

  [BLOCK, CASE, DEFAULT, DO, FINALLY, FOR, IF, SWITCH, TRY, WHILE].forEach(
    function(tt) { override(tt, _next); });

  override(FOR_IN, function(n, fr) {
    // For most kinds of iterators at FOR/IN we have to be conservative 
    // (e.g. DOTs or INDEXes). Without flow sensitivity, we even have to be
    // conservative for stack refs that have been initialized, we can't forget
    // their current value. We can only be precise when the iterator is a stack
    // reference and the variable is BOTTOM in the frame.
    var ans = evalExp(n.object, fr), errval, av;
    var it = n.iterator, b = n.body;
    if (it.type === IDENTIFIER && 
        it.kind === STACK && 
        aveq(BOTTOM, frameGet(fr, it))) {

      av = ans.v;
      errval = ans.err;
      av.forEachObj(function(o) {
        o.forEachEnumProp(function(p) {
          // wipe the value of it from the previous iteration
          frameSet(fr, it, makeStrLitAval(p));
          if (flags[it.addr]) updateHeapAv(it.addr, makeStrLitAval(p));
          ans = evalStm(b, fr);
          errval = maybeavjoin(errval, ans.err);
        });
      });
      ans.v = b.kreg;
      ans.err = errval;
    }
    else {
      av = BOTTOM;
      ans.v.forEachObj(function(o) {
        o.forEachEnumProp(function(p) {
          if (propIsNumeric(p)) 
            av = avjoin(av, ANUM);
          else
            av = avjoin(av, ASTR);
        });
      });
      ans.v = av;
      ans = evalLval(n.iterator, ans);
      ans.v = b;
    }
    return ans;
  });

  override(CATCH, function(n, fr) { return new Ans(n.block, fr); });

  override(THROW, function(n, fr) {
    var ans = evalExp(n.exception, fr);
    ans.err = maybeavjoin(ans.err, ans.v);
    ans.v = n.kreg;
    return ans;
  });
})();

var big_ts;

// StackCleaner inherits from Error and is not used to signal errors, but to
// manage the size of the runtime stack.

// function node, number, optional array of Aval
function StackCleaner(fn, howmany, args) {
  this.fn = fn;
  this.howmany = howmany;
  if (args) this.args = args;
}

StackCleaner.prototype = new Error();

// function node, array of Aval, boolean, optional call node -> Ans w/out fr
// Arg 4 is the node that caused the function call (if there is one).
function evalFun(fn, args, withNew, cn) {
  var ans, n, params, fr, w, script = fn.body, pelm1;
  var retval = BOTTOM, errval = BOTTOM;

  // stm node (exception continuation), av (exception value) -> void
  function stmThrows(n, errav) {
    if (n) {
      if (n.type === CATCH) {
        var exvar = n.exvar;
        if (exvar.kind === HEAP)
          heap[exvar.addr] = avjoin(errav, heap[exvar.addr]);
        if (fr[exvar.addr]) // revealing the representation of frame here.
          frameSet(fr, exvar, avjoin(errav, frameGet(fr, exvar)));
        else
          frameSet(fr, exvar, errav);
      }
      w.push(n);
    }
    else
      errval = avjoin(errval, errav);
  }

  if (process.uptime() > timeout) throw new Error("timeout");
  
  // if (timestamp > big_ts) {
  //   print("big ts: " + timestamp);
  //   dumpHeap("heapdump" + timestamp + ".txt");
  //   big_ts += 1000;
  //   if (big_ts > 100000) throw new Error("foobar");
  // }

  // treat built-in functions specially
  if (fn.builtin) {
    // return fn.body(args, withNew, cn);
    // If there's an input for which built-ins cause stack overflow, uncomment.
    var addr = fn.addr;
    if (pending[addr] > 1) {
      return new Ans(BOTTOM, undefined, BOTTOM);
    }
    ++pending[addr];
    try {
      ans = fn.body(args, withNew, cn);
      --pending[addr];
      return ans;
    }
    catch (e) {
      if (e instanceof StackCleaner) --pending[addr];
      throw e;
    }
  }

  var tsAtStart;
  var result = searchSummary(fn, args, timestamp);
  if (result) return new Ans(result[0], undefined, result[1]);

  while(true) {
    try {
      tsAtStart = timestamp;
      // pending & exceptions prevent the runtime stack from growing too much.
      var pelm2 = searchPending(fn, args);
      if (pelm2 === 0) {
        pelm1 = {args : args, ts : timestamp};
        addPending(fn, pelm1);
      }
      else if (pelm2 === undefined) {
        // If a call eventually leads to itself, stop analyzing & return BOTTOM.
        // Add a summary that describes the least solution.
        addSummary(fn, args, BOTTOM, BOTTOM, tsAtStart);
        return new Ans(BOTTOM, undefined, BOTTOM);
      }
      else if (pelm2 > 0) {
        // There are pending calls that are obsolete because their timestamp is
        // old. Discard frames to not grow the stack too much.
        throw new StackCleaner(fn, pelm2);
      }
      else /* if (pelm2 < 0) */ {
        throw new StackCleaner(fn, -pelm2, args);
      }
      w = [];
      fr = {};
      params = fn.params;
      frameSet(fr, fn.fname, makeObjAval(fn.addr));
      // args[0] is always the obj that THIS is bound to.
      // THIS never has a heap ref, so its entry in the frame is special.
      fr.thisav = args[0];
      // Bind formals to actuals
      for (var i = 0, len = params.length; i < len; i++) {
        var param = params[i], arg = args[i+1] || AUNDEF;//maybe #args < #params
        if (param.kind === HEAP) updateHeapAv(param.addr, arg);
        frameSet(fr, param, arg);
      }
      var argslen = args.length;
      if ((++i) < argslen) { // handling of extra arguments
        var restargs = BOTTOM;
        for (; i<argslen; i++) restargs = avjoin(restargs, args[i]);
        fr[RESTARGS] = restargs; // special entry in the frame.
      }
      // bind a non-init`d var to bottom, not undefined.
      script.varDecls.forEach(function(vd) { frameSet(fr, vd, BOTTOM); });
      // bind the fun names in the frame.
      script.funDecls.forEach(function(fd) {
        frameSet(fr, fd.fname, makeObjAval(fd.addr));
      });

      w.push(script.kreg);
      while (w.length !== 0) {
        n = w.pop();
        if (n === undefined) continue;
        if (n.type === RETURN) {
          ans = evalExp(n.value, fr);
          // fr is passed to exprs/stms & mutated, no need to join(fr, ans.fr)
          fr = ans.fr;
          retval = avjoin(retval, ans.v);
          w.push(n.kreg);
          if (ans.err) stmThrows(n.kexc, ans.err);
        }
        else {
          ans = evalStm(n, fr);
          fr = ans.fr;
          w.push(ans.v);
          if (ans.err) stmThrows(n.kexc, ans.err);
        }
      }
      rmPending(fn);
      if (!fn.hasReturn) retval = AUNDEF;
      // Find if a summary has been added during recursion.
      result = searchSummary(fn, args, tsAtStart);
      if (!result || (avlt(retval, result[0]) && avlt(errval, result[1]))) {
        // Either fn isn't recursive, or the fixpt computation has finished.
        if (!result) addSummary(fn, args, retval, errval, tsAtStart);
        return new Ans(retval, undefined, errval);
      }
      else {
        retval = avjoin(result[0], retval);
        errval = avjoin(result[1], errval);
        // The result changed the last summary; update summary and keep going.
        addSummary(fn, args, retval, errval, tsAtStart);
      }
    }
    catch (e) {
      if (!(e instanceof StackCleaner)) {
        // analysis error, irrelevant to the stack-handling code
        throw e;
      }
      if (!pelm1) throw e;
      rmPending(fn);
      if (e.fn !== fn) throw e;
      if (e.howmany !== 1) {
        e.howmany--;
        throw e;
      }
      if (e.args) args = e.args;
    }
  }
}

// maybe merge with evalFun at some point
function evalToplevel(tl) {
  var w /* workset */, fr, n, ans;
  w = [];
  fr = {};
  initDeclsInHeap(tl);

  fr.thisav = global_object_av;
  // bind a non-init`d var to bottom, different from assigning undefined to it.
  tl.varDecls.forEach(function(vd) { frameSet(fr, vd, BOTTOM); });
  // bind the fun names in the frame.
  tl.funDecls.forEach(function(fd) { 
    frameSet(fr, fd.fname, makeObjAval(fd.addr));
  });

  // evaluate the stms of the toplevel in order
  w.push(tl.kreg);
  while (w.length !== 0) {
    n = w.pop();
    if (n === undefined) continue; // end of toplevel reached
    if (n.type === RETURN)
      ; // record error, return in toplevel
    else {
      ans = evalStm(n, fr);
      fr = ans.fr;
      w.push(ans.v);
      // FIXME: handle toplevel uncaught exception
    }
  }

  //print("call uncalled functions");
  
  // each function w/out a summary is called with unknown arguments
  for (var addr in summaries) {
    var f = heap[addr].getFun();
    if (!existsSummary(f)) {
      var any_args = buildArray(f.params.length, BOTTOM);
      any_args.unshift(makeGenericObj());
      evalFun(f, any_args, false);
    }
  }

  //showSummaries();
}

// initGlobals and initCoreObjs are difficult to override. The next 2 vars help
// clients of the analysis add stuff to happen during initialization
var initOtherGlobals, initOtherObjs;

// consumes the ast returned by jsparse.parse
function cfa2(ast) {
  count = 0;
  astSize = 0;
  initGlobals();
  initOtherGlobals && initOtherGlobals();
  //print("fixStm start");
  fixStm(ast);
  //print("fixStm succeeded");
  initCoreObjs();
  initOtherObjs && initOtherObjs();
  //print("initObjs done");
  if (commonJSmode) { // create the exports object
    var e = new Aobj({ addr: newCount() }), eav = makeObjAval(count);
    heap[newCount()] = eav;
    exports_object_av_addr = count;
    exports_object.obj = e;
  }
  labelAST(ast);
  //print("labelStm done");
  desugarWith(ast, undefined, []);
  //print("desugarWith done");
  desugarLet(ast);
  tagVarRefs(ast, [], [], "toplevel");
  //print("tagrefsStm done");
  markConts(ast, undefined, undefined);
  //print("markconts done");
  try {
    //print("Done with preamble. Analysis starting.");
    evalToplevel(ast);    
    //print("after cfa2");
    // print("AST size: " + astSize);
    // print("ts: " + timestamp);
    // dumpHeap("heapdump.txt");
  }
  catch (e) {
    if (e.message !== "timeout") {
      print(e.message);
      console.trace();
      if (! ("code" in e)) e.code = CFA_ERROR;
      throw e;
    }
    else
      timedout = true;
  }
}

// function node -> string
function funToType(n, seenObjs) {
  if (n.builtin)
    return "function"; // FIXME: tag built-in nodes w/ their types
  if (seenObjs) {
    if (seenObjs.memq(n))
      return "any";
    else
      seenObjs.push(n);
  }
  else {
    seenObjs = [n];
  }
  
  var addr = n.addr, summary = summaries[addr];
  if (summary.ts === INVALID_TIMESTAMP) // the function was never called
    return "function";
  var insjoin = summary.type[0], instypes = [], outtype, slen = seenObjs.length;
  for (var i = 1, len = insjoin.length; i < len; i++) {
    instypes[i - 1] = insjoin[i].toType(seenObjs);
    // each argument must see the same seenObjs, the initial one.
    seenObjs.splice(slen, seenObjs.length);
  }

  if (n.withNew && !n.hasReturn) {
    outtype = n.fname.name;
    // If a fun is called both w/ and w/out new, assume it's a constructor.
    // If a constructor is called w/out new, THIS is bound to the global obj.
    // In this case, the result type must contain void.
    var thisObjType = insjoin[0].toType(seenObjs);
    if (/Global Object/.test(thisObjType))
      outtype = "<void | " + outtype + ">";
  }
  else
    outtype = summary.type[1].toType(seenObjs);
  
  if (outtype === "undefined") outtype = "void";
  return (outtype + " function(" + instypes.join(", ") +")");
}

// node, string, Array of string, cmd-line options -> Array of ctags
function getTags(ast, pathtofile, lines, options) {
  const REGEX_ESCAPES = { "\n": "\\n", "\r": "\\r", "\t": "\\t" };
  var tags = [];

  function regexify(str) {
    function subst(ch) {
      return (ch in REGEX_ESCAPES) ? REGEX_ESCAPES[ch] : "\\" + ch;
    }
    str || (str = "");
    return "/^" + str.replace(/[\\/$\n\r\t]/g, subst) + "$/";
  }

  if (options.commonJS) commonJSmode = true;
  // print(pathtofile);
  cfa2(ast);
  // print("Flow analysis done. Generating tags");

  if (exports_object.obj) {
    var eo = exports_object.obj;
    eo.forEachOwnProp(function (p) {
      var av = eo.getOwnExactProp(p);
      var tag = {};
      tag.name = /-$/.test(p) ? p.slice(0, -1) : p.slice(1);
      tag.tagfile = pathtofile;
      tag.addr = regexify(lines[exports_object.lines[p] - 1]);
      var type = av.toType();
      if (/(^<.*> function)|(^[^<>\|]*function)/.test(type))
        tag.kind = "f";
      else
        tag.kind = "v";
      tag.type = type;
      tag.module = options.module;
      tag.lineno = exports_object.lines[p];
      tags.push(tag);
    });
  }

  for (var addr in summaries) {
    var f = heap[addr].getFun();
    tags.push({ name : f.fname.name || "%anonymous_function",
                tagfile : pathtofile,
                addr : regexify(lines[f.lineno - 1]),
                kind : "f",
                type : funToType(f),
                lineno : f.lineno.toString(),
                sortno : f.lineno.toString()
              });
  }
  ast.varDecls.forEach(function(vd) {
    tags.push({ name : vd.name,
                tagfile : pathtofile,
                addr : regexify(lines[vd.lineno - 1]),
                kind : "v",
                type : heap[vd.addr].toType(),
                lineno : vd.lineno.toString(),
                sortno : vd.lineno.toString()
              });
  });
  return tags;
}

// node -> boolean
// hacky test suite. Look in run-tests.js
function runtest(ast) {
  cfa2(ast);
  // find test's addr at the toplevel
  var testaddr, fds = ast.funDecls;
  for (var i = 0, len = fds.length; i < len; i++) 
    if (fds[i].fname.name === "test") {
      testaddr = fds[i].addr;
      break;
    }
  if (testaddr === undefined) throw errorWithCode(CFA_ERROR, "Malformed test");
  var type = summaries[testaddr].type;
  // print(type[0][1]);
  // print(type[1]);
  return aveq(type[0][1], type[1]);
}

exports.cfa2 = cfa2;
exports.runtest = runtest;
exports.getTags = getTags;

////////////////////////////////////////////////////////////////////////////////
//////////////    DATA DEFINITIONS FOR THE AST RETURNED BY JSPARSE  ////////////
////////////////////////////////////////////////////////////////////////////////

function walkExp(n) {

  switch (n.type){

    //nullary
  case NULL:
  case THIS:
  case TRUE:
  case FALSE:
    break;

  case IDENTIFIER:
  case NUMBER:
  case STRING:
  case REGEXP:
    // n.value
    break;

    //unary
  case DELETE:
  case VOID:
  case TYPEOF:
  case NOT:
  case BITWISE_NOT:
  case UNARY_PLUS: case UNARY_MINUS:
  case NEW:
    walkExp(n.children[0]); 
    break;

  case INCREMENT: case DECREMENT:
    // n.postfix is true or undefined
    walkExp(n.children[0]);
    break;

    //binary
  case CALL:
  case NEW_WITH_ARGS:
    walkExp(n.children[0]); 
    //n[1].type === LIST
    n.children[1].children.forEach(walkExp);
    break;

  case IN:
    walkExp(n.children[0]); // an exp which must eval to string
    walkExp(n.children[1]); // an exp which must eval to obj
    break;

  case DOT:
    walkExp(n.children[0]);
    walkExp(n.children[1]); // must be IDENTIFIER
    break;

  case BITWISE_OR: case BITWISE_XOR: case BITWISE_AND:
  case EQ: case NE: case STRICT_EQ: case STRICT_NE:
  case LT: case LE: case GE: case GT:
  case INSTANCEOF:
  case LSH: case RSH: case URSH:
  case PLUS: case MINUS: case MUL: case DIV: case MOD:
  case AND: case OR:
  case ASSIGN: // n[0].assignOp shows which op-and-assign operator we have here
  case INDEX: // property indexing  
    walkExp(n.children[0]);
    walkExp(n.children[1]);
    break;

    //ternary
  case HOOK:
    walkExp(n.children[0]);
    walkExp(n.children[1]);
    walkExp(n.children[2]);
    break;

    //variable arity
  case COMMA:
  case ARRAY_INIT: // array literal
    n.children.forEach(walkExp);
    break;

  case OBJECT_INIT:
    n.children.forEach(function(prop) { // prop.type === PROPERTY_INIT
      walkExp(prop.children[0]); // identifier, number or string
      walkExp(prop.children[1]);
    });
    break;

    //other
  case FUNCTION:
    // n.name is a string
    // n.params is an array of strings
    // n.functionForm === EXPRESSED_FORM
    walkStm(n.body);
    break;
  }
}

function walkStm(n) {
  switch (n.type) {

  case SCRIPT: 
  case BLOCK:
    n.children.forEach(walkStm);
    break;

  case FUNCTION:
    // n.name is a string
    // n.params is an array of strings
    // n.functionForm === DECLARED_FORM or STATEMENT_FORM
    // STATEMENT_FORM is for funs declared in inner blocks, like IF branches
    // It doesn't extend the funDecls of the script, bad!
    walkStm(n.body);
    break;

  case SEMICOLON:
    n.expression && walkExp(n.expression); 
    break;

  case IF:
    walkExp(n.condition);
    walkStm(n.thenPart);
    n.elsePart && walkStm(n.elsePart);
    break;
    
  case SWITCH:
    walkExp(n.discriminant);
    // a switch w/out branches is legal, n.cases is []
    n.cases.forEach(function(branch) {
      branch.caseLabel && walkExp(branch.caseLabel);
      // if the branch has no stms, branch.statements is an empty block
      walkStm(branch.statements);
    });
    break;

  case FOR: 
    if (n.setup) {
      if (n.setup.type === VAR || n.setup.type === CONST)
        walkStm(n.setup);
      else walkExp(n.setup);
    }
    n.condition && walkExp(n.condition);
    n.update && walkExp(n.update);
    walkStm(n.body);
    break;

  case FOR_IN:
    // n.varDecl may be used when there is a LET at the head of the for/in loop.
    walkExp(n.iterator);
    walkExp(n.object);
    walkStm(n.body);
    break;

  case WHILE:
  case DO:
    walkExp(n.condition);
    walkStm(n.body);
    break;

  case BREAK:
  case CONTINUE:
    // do nothing: n.label is just a name, n.target points back to ancestor
    break;

  case TRY:
    walkStm(n.tryBlock);
    n.catchClauses.forEach(function(clause) { // clause.varName is a string
      clause.guard && walkExp(clause.guard);
      walkStm(clause.block);
    });
    n.finallyBlock && walkStm(n.finallyBlock);
    break;

  case THROW: 
    walkExp(n.exception);
    break;

  case RETURN:
    n.value && walkExp(n.value);
    break;
    
  case WITH:
    walkExp(n.object);
    walkStm(n.body);
    break;

  case LABEL:
    // n.label is a string
    walkStm(n.statement);
    break;

  case VAR: 
  case CONST: // variable or constant declaration
    // vd.name is a string
    // vd.readOnly is true for constants, false for variables
    n.children.forEach(function(vd) { walkExp(vd.initializer); });
    break;
  }
  return n;
}

////////////////////////////////////////////////////////////////////////////////
////////////    EVENT CLASSIFICATION FOR FIREFOX ADDONS    /////////////////////
////////////////////////////////////////////////////////////////////////////////

var e10sResults, chrome_obj_av_addr, Chrome, Content;

(function() {
  // Initializing functions are overriden here
  initOtherGlobals = function() {
    // make separate constructors for chrome and content objs, so that we can 
    // distinguish them w/ instanceof
    Chrome = function(specialProps) { Aobj.call(this, specialProps); }
    Chrome.prototype = new Aobj({ addr: newCount() });
    Content = function(specialProps) { Aobj.call(this, specialProps); }
    Content.prototype = new Aobj({ addr: newCount() });
    e10sResults = {};
  };
  initOtherObjs = initDOMObjs;
  tagVarRefs_override(IDENTIFIER, tagVarRefsId(true));

  // Must be called *after* the desugarings.
  function initDeclsInHeap_e10s(n) {
    // "Attach listener" have one more property called status:
    // status is an Array of four strings, describing the listener:
    // event name: some specific name or unknown
    // attached on: chrome, content or any
    // originates from: chrome, content or any
    // flagged: safe or unsafe
    n.addr = newCount();
    e10sResults[count] = {
      lineno : n.lineno,
      analyzed : false,
      kind : (n.type === DOT && n.children[1].value === "addEventListener-") ?
        "Attach listener" : "Touch content"
    };
    n.children.forEach(initDeclsInHeap);
  }
  initDeclsInHeap_override(DOT, initDeclsInHeap_e10s);
  initDeclsInHeap_override(INDEX, initDeclsInHeap_e10s);
})();

function initDOMObjs() {

  function toThis(args) { return new Ans(args[0]); }

  // the whole DOM tree is modeled by 2 chrome and 1 content object
  var chr = new Chrome({ addr: newCount() }), chrav = makeObjAval(count);
  chrome_obj_av_addr = newCount();
  heap[chrome_obj_av_addr] = chrav;
  var chr2 = new Chrome({ addr: newCount() }), chr2av = makeObjAval(count);
  var con = new Content({ addr: newCount() }), conav = makeObjAval(count);

  chr.addProp("content-", { aval: chr2av, enum: false });
  chr.addProp("contentDocument-", { aval: conav, enum: false });
  chr.addProp("contentWindow-", { aval: chr2av, enum: false });
  chr.addProp("defaultView-", { aval: conav, enum: false });
  chr2.addProp("document-", { aval: conav, enum: false });
  con.addProp("documentElement-", { aval: conav, enum: false });
  chr.addProp("opener-", { aval: chrav, enum: false });
  con.addProp("opener-", { aval: conav, enum: false });
  chr.addProp("selectedBrowser-", { aval: chrav, enum: false });

  ["firstChild-", "lastChild-", "nextSibling-", "top-"].forEach(
    function(pname) {
      chr.addProp(pname, { aval: chrav, enum: false });
      chr2.addProp(pname, { aval: chr2av, enum: false });
      con.addProp(pname, { aval: conav, enum: false });
    }
  );
  chr.addProp("parentNode-", { aval: chrav, enum: false });
  chr2.addProp("parentNode-", { aval: chrav, enum: false });
  con.addProp("parentNode-", { aval: conav, enum: false });

  attachMethod(chr, "getBrowser", toThis, 0);
  ["getElementById", "appendChild", "removeChild", "createElement"].forEach(
    function(fname) {
      attachMethod(chr, fname, toThis, 1);
      attachMethod(con, fname, toThis, 1);
    }
  );

  // chrarr is for functions that normally return a Node list of chrome elms
  var chrarr = new Aobj({ addr: newCount() }), chrarrav = makeObjAval(count);
  array_constructor([chrarrav], true);
  chrarr.updateNumProps(chrav);

  // conarr is for functions that normally return a Node list of content elms
  var conarr = new Aobj({ addr: newCount() }), conarrav = makeObjAval(count);
  array_constructor([conarrav], true);
  conarr.updateNumProps(conav);

  function toNodeList(args) {
    var av = BOTTOM, both = 0;
    args[0].forEachObjWhile(function(o) {
      if (o instanceof Chrome) {
        av = avjoin(av, chrarrav);
        both |= 1;
      }
      if (o instanceof Content) {
        av = avjoin(av, conarrav);
        both |= 2;
      }
      return both === 3;
    });
    return new Ans(av);
  }

  chr.addProp("childNodes-", { aval: chrarrav, enum: false });
  chr2.addProp("childNodes-", { aval: chrarrav, enum: false });
  con.addProp("childNodes-", { aval: conarrav, enum: false });  

  [["querySelectorAll", 1], ["getElementsByClassName", 1],
   ["getElementsByAttribute", 2], ["getElementsByTagName", 1]].forEach(
     function(pair) {
       var p0 = pair[0], p1 = pair[1];
       attachMethod(chr, p0, toNodeList, p1);
       attachMethod(chr2, p0, toNodeList, p1);
       attachMethod(con, p0, toNodeList, p1);
     }
   );

  global_object_av.forEachObj(function(go) {
    go.addProp("content-", { aval: chr2av, enum: false });
    go.addProp("contentWindow-", { aval: chr2av, enum: false });
    go.addProp("document-", { aval: chrav, enum: false });
    go.addProp("gBrowser-", { aval: chrav, enum: false });
    go.addProp("opener-", { aval: chrav, enum: false });
    go.addProp("window-", { aval: chrav, enum: false });
  });

  function aEL(args, withNew, callNode) {
    // oldst can be undefined
    function evtjoin(oldst, newst) {
      if (oldst) {
        if (oldst[0] !== newst[0]) newst[0] = "unknown-";
        if (oldst[1] !== newst[1]) newst[1] = "any";
        if (oldst[2] !== newst[2]) newst[2] = "any";
        if (oldst[3] !== newst[3]) newst[3] = "unsafe";
      }
      return newst;
    }

    var evt = (args[1] && args[1].getStrLit()) || "unknown-";
    var ratorNode = callNode.children[0], raddr=ratorNode.addr, ec, evtkind, st;

    if (!ratorNode) return new Ans(BOTTOM);
    ec = e10sResults[raddr];
    if (ec)
      ec.analyzed = true;
    else {
      if (!raddr) raddr = ratorNode.addr = newCount();
      ec = e10sResults[raddr] = {lineno : ratorNode.lineno,
                                 analyzed : true,
                                 kind : "Attach listener",
                                 status : undefined};
    }

    evtkind = eventKinds[evt.slice(0,-1)];
    if (evtkind === XUL)
      st = [evt, "chrome", "chrome", "safe"];
    else if (evtkind === undefined && !args[4] && evt !== "unknown-") {
      // listener for custom event that can't come from content
      st = [evt, "chrome", "chrome", "safe"];
    }
    else {
      var numobjs = 0;
      args[0].forEachObj(function(o) {
        ++numobjs;
        if (o instanceof Chrome) {
          var st2 = [evt, "chrome", undefined, undefined];
          if (evtkind === NO_BUBBLE) {
            st2[2] = "chrome";
            st2[3] = "safe";
          }
          else {
            st2[2] = "any";
            st2[3] = "unsafe"
          }
          st = evtjoin(st, st2);
        }
        else if (o instanceof Content) {
          st = evtjoin(st, [evt, "content", "content", "unsafe"]);
        }
        else 
          st = evtjoin(st, [evt, "any", "any", "unsafe"]);
      });
      if (numobjs === 0) st = [evt, "any", "any", "unsafe"];
    }
    ec.status = evtjoin(ec.status, st);
    return new Ans(BOTTOM);
  }

  var aEL_node = funToNode("addEventListener-", aEL, 3);
  new Aobj({ addr: count,
             proto : function_prototype_av,
             fun : aEL_node });
  var aELav = makeObjAval(count);

  // Node, Aval, Aval -> Aval
  function evalExp_e10s(n, recv, av) {
    var recvchrome = false, recvcon = false;
    recv.forEachObjWhile(function(o) {
      if (o instanceof Chrome)
        recvchrome = true;
      else if (o instanceof Content)
        recvcon = true;
      return recvchrome && recvcon;
    });
    if (recvchrome && !recvcon)
      av.forEachObjWhile(function(o) {
        if (o instanceof Content) {
          var ec = e10sResults[n.addr];
          ec.analyzed = true;
          ec.kind = "Touch content";
          return true;
        }
      });
    //hideous hack for properties of chrome & content elms we don't know about
    if (aveq(av, AUNDEF) && (recvchrome || recvcon))
      return recv;
    else
      return av;
  }

  // replace evalExp/DOT with the following function
  evalExp_override(DOT, function(n, fr) {
    var ch = n.children;
    var ans = evalExp(ch[0], fr), avobj = ans.v.baseToObj();
    ans.thisav = avobj; // used by method calls
    if (ch[1].value === "addEventListener-")
      ans.v = aELav;
    else
      ans.v = avobj.getProp(ch[1].value);
    ans.v = evalExp_e10s(n, avobj, ans.v);
    return ans;
  });

  evalExp_override(INDEX, function(n, fr) {
    var ansobj = evalExp(n.children[0], fr), avobj = ansobj.v.baseToObj();
    var prop = n.children[1], errval = ansobj.err, av , ans;
    fr = ansobj.fr;
    if (prop.type === STRING)
      av = avobj.getProp(prop.value);
    else {
      var ansprop = evalExp(prop, fr), avprop = ansprop.v;
      fr = ansprop.fr;
      errval = maybeavjoin(errval, ansprop.err);
      av = BOTTOM;
      if (avprop.hasNum())
        avobj.forEachObj(function(o) { av = avjoin(av, o.getNumProps()); });
      if (avprop.hasStr()) {
        var slit = avprop.getStrLit();
        if (slit)
          av = avjoin(av, avobj.getProp(slit));
        else
          avobj.forEachObj(function(o) { av = avjoin(av, o.getStrProps()); });
      }
    }
    ans = new Ans(evalExp_e10s(n, avobj, av), fr, errval);
    ans.thisav = avobj;
    return ans;
  });
}

const XUL = 0, BUBBLE = 1, NO_BUBBLE = 2;
var eventKinds = {
  abort : BUBBLE,
  blur : NO_BUBBLE,
  broadcast : XUL,
  change : BUBBLE,
  CheckboxStateChange : XUL,
  click : BUBBLE,
  close : XUL,
  command : XUL,
  commandupdate : XUL,
  contextmenu : XUL,
  dblclick : BUBBLE,
  DOMActivate : BUBBLE,
  DOMAttrModified : BUBBLE,
  DOMCharacterDataModified : BUBBLE,
  DOMContentLoaded : BUBBLE,
  DOMFocusIn : BUBBLE,
  DOMFocusOut : BUBBLE,
  DOMMenuItemActive : XUL,
  DOMMenuItemInactive : XUL,
  DOMMouseScroll : XUL,
  DOMNodeInserted : BUBBLE,
  DOMNodeInsertedIntoDocument : NO_BUBBLE,
  DOMNodeRemoved : BUBBLE,
  DOMNodeRemovedFromDocument : NO_BUBBLE,
  DOMSubtreeModified : BUBBLE,
  dragdrop : XUL,
  dragenter : XUL,
  dragexit : XUL,
  draggesture : XUL,
  dragover : XUL,
  error : BUBBLE,
  focus : NO_BUBBLE,
  input : XUL,
  keydown : BUBBLE,
  keypress : BUBBLE,
  keyup : BUBBLE,
  load : NO_BUBBLE,
  mousedown : BUBBLE,
  mousemove : BUBBLE,
  mouseout : BUBBLE,
  mouseover : BUBBLE,
  mouseup : BUBBLE,
  overflow : XUL,
  overflowchanged : XUL,
  pagehide: BUBBLE,
  pageshow: BUBBLE,
  popuphidden : XUL,
  popuphiding : XUL,
  popupshowing : XUL,
  popupshown : XUL,
  RadioStateChange : XUL,
  reset : BUBBLE,
  resize : BUBBLE,
  scroll : BUBBLE,
  select : BUBBLE,
  submit : BUBBLE,
  TabClose : XUL,
  TabOpen : XUL,
  TabSelect : XUL,
  underflow : XUL,
  unload : NO_BUBBLE
  // ViewChanged event from greasemonkey?
};

function analyze_addon(ast, tmout) {
  print("Doing CFA");
  timeout = tmout;
  cfa2(ast);
  // Addresses are irrelevant outside jscfa, convert results to array.
  var rs = [];
  for (var addr in e10sResults) {
    var r = e10sResults[addr];
    if (r.analyzed) rs.push(r);
  }
  rs.astSize = astSize;
  rs.timedout = timedout;
  print("Done with CFA: " + timestamp);
  return rs;
}

exports.analyze_addon = analyze_addon;
