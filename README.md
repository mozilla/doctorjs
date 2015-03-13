Overview
--------
jsctags is a [ctags] [1]-compatible code indexing solution for JavaScript. Its
interface and output are essentially identical to [Exuberant Ctags] [2], but,
instead of simply parsing the JavaScript, jsctags uses a simple form of
abstract interpretation to determine which symbols are exported. This allows
jsctags to achieve much better results than Exuberant Ctags. Popular libraries
such as jQuery and CommonJS modules can now be meaningfully indexed.

You can use jsctags to create `tags` files that are usable in many editors,
from Vim to TextMate (via the [CodeBrowser] [3] plugin). jsctags is slated to
become a key component of the [Bespin] [4] IDE, where it will be used to
provide code completion.

jsctags is written entirely in JavaScript, using CommonJS modules, the
[node.js] [5] framework, and the [Narcissus] [6] engine.

License
-------
jsctags is tri-licensed under the Mozilla Public License 1.1, the GNU General
Public License 2.0, and the GNU Lesser General Public License 2.1.

Requirements
------------
* node.js
* `make`

Building
--------
To install:

* `git submodule update --init --recursive`
* `make install`

To uninstall:

* `make uninstall`

To play with Narcissus' parser:

* `make serve`
* Navigate to [`http://localhost:8080/html/parser.html`] [parser].

Usage
-----
Simply go to your project root and invoke `jsctags lib` (replacing `lib` with
the directory in which your JavaScript source files are stored). The `tags`
file will be placed in the current directory.

For more options, try `jsctags -h`.

Directory structure
-------------------
The directory structure mostly follows the CommonJS packaging scheme:

* `bin/`: tools runnable from node.js (should be directly executable in Unix)
* `html/`: in-browser demo files
* `js/`: support files for the HTML demos
* `lib/`: CommonJS-compliant library files
* `lib/ctags/`: the core jsctags code
* `narcissus/`: the Narcissus engine
* `test/`: test cases for the indexer

[1]: http://en.wikipedia.org/wiki/Ctags
[2]: http://ctags.sourceforge.net/
[3]: http://www.cocoabits.com/TmCodeBrowser/
[4]: http://mozillalabs.com/bespin/
[5]: http://nodejs.org/
[6]: http://mxr.mozilla.org/mozilla/source/js/narcissus/

[parser]: http://localhost:8080/html/parser.html

