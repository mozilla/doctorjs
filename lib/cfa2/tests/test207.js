// unsound.
// The two x`s are the same variable, the result should be number or string.
function test(expected) {
  return (function(x) {var x = 3; return x;})("asdf");
}

test(0);
