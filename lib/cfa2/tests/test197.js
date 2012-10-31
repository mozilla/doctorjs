// WITH: shadowed by function
function test(expected) {
  var o = {x:1};
  with (o) {
    return (function(x) { return x; })("asdf");
  }
}

test("asdf");
