/* ***** BEGIN LICENSE BLOCK *****
 * Version: MPL 1.1/GPL 2.0/LGPL 2.1
 *
 * The contents of this file are subject to the Mozilla Public License Version
 * 1.1 (the "License"); you may not use this file except in compliance with
 * the License. You may obtain a copy of the License at
 * http://www.mozilla.org/MPL/
 *
 * Software distributed under the License is distributed on an "AS IS" basis,
 * WITHOUT WARRANTY OF ANY KIND, either express or implied. See the License
 * for the specific language governing rights and limitations under the
 * License.
 *
 * The Original Code is Bespin.
 *
 * The Initial Developer of the Original Code is
 * Mozilla.
 * Portions created by the Initial Developer are Copyright (C) 2009
 * the Initial Developer. All Rights Reserved.
 *
 * Contributor(s):
 *   Bespin Team (bespin@mozilla.com)
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

/**
 * Simple option parsing library, vaguely influenced by the venerable Perl
 * Getopt::Long.
 */

exports.getopt = exports.GetOptions = function() {
    var table = {};
    for (var i = 0; i < arguments.length; i++) {
        var spec = arguments[i];
        var match = /^([A-Za-z0-9_|-]+)(?:=(s)(@)?)?$/.exec(spec);
        var aliases = match[1].split("|");
        var info = { id: aliases[0], type: match[2], multi: match[3] };
        aliases.forEach(function(alias) { table[alias] = info; });
    }

    var result = {};
    var argv = process.argv;
    var i = 2;
    while (i < argv.length) {
        var arg = argv[i];
        if (arg === "--") {
            argv.splice(i, 1);
            break;
        }
        if (arg.charAt(0) !== "-") {
            i++;
            continue;
        }

        argv.splice(i, 1);

        var info, param;
        if (arg.charAt(1) === "-") {
            var match = /^--([A-Za-z0-9_|-]+)(?:=(.*))?$/.exec(arg);
            if (match == null) {
                throw new Error("malformed option \"" + arg + "\"");
            }

            var optname = match[1];
            if (!(optname in table)) {
                throw new Error("unknown option \"--" + optname + "\"");
            }

            info = table[optname];
            if (info.type != null) {
                if (match[2] != null) {
                    param = match[2];
                } else if (i < argv.length) {
                    param = argv[i];
                    argv.splice(i, 1);
                } else {
                    throw new Error("option \"--" + optname + "\" requires " +
                        "an argument");
                }
            } else {
                param = true;
            }
        } else {
            var optname = arg.charAt(1);

            if (!(optname in table)) {
                throw new Error("unknown option \"-" + optname + "\"");
            }

            info = table[optname];
            if (info.type != null) {
                if (arg.length > 2) {
                    param = arg.substr(2);
                } else if (i < argv.length) {
                    param = argv[i];
                    argv.splice(i, 1);
                } else {
                    throw new Error("option \"-" + optname + "\" requires " +
                        "an argument");
                }
            } else if (arg.length == 2) {
                param = true;
            } else {
                throw new Error("option \"-" + optname + "\" doesn't take " +
                    "an argument");
            }
        }

        var optid = info.id;
        if (info.multi != null) {
            if (!(optid in result)) {
                result[optid] = [ param ];
            } else {
                result[optid].push(param);
            }
        } else {
            result[optid] = param;
        }
    }

    return result;
}

