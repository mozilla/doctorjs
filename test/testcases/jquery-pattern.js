(function (wnd) {
    var myQuery = {
        foo: function () {
            window.alert("foo");
        },

        bar: function () {
            return 1;
        },

        baz: 3
    };

    myQuery.boo = function () {
        return 42;
    };

    myQuery.boo.foo = 12;

    wnd.$ = wnd.myQuery = myQuery;
})(window);

