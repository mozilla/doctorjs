// shadow by var
function test(expected) {
  var o = {x:1};
  with (o) {
    return (function() { var x = "asdf"; return x; })();
  }
}

test("asdf");
