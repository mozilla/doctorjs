// evalExp/DOT_PROTO: n[0] throws
function test(expected) {
  function t() {throw new Error("");}

  function Foo() {}
  
  try {
    (function(){
      if (123) t(); else return new Foo();
    }()).prototype;
  }
  catch (e) {
    return e.message;
  }
}

test("");
