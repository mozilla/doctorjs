// LET: substitutions do the right thing
function test(expected) {
  var n1, n2, n3;
  let (x = "asdf") {
    (function(x) { n1 = x; })(0);
  }
  let (y = "qwer") {
    let (y = 123) {
      n2 = y;
    }
  }
  let (z = "asdf") {
    (function(num) { 
      var z = num;
      n3 = z; 
    })(0);
  }
  return n1 + n2 + n3;
}

test(0);
