// CATCH variable is heap
function test(expected) {
  try {
    throw new Error("foo");
  }
  catch (e) {
    return (function(){ return e.message; })();
  }
}

test("foo");
