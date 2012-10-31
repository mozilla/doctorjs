/*
    Spinner provides a simple approach for adding and removing a preloader
    for your web applications. Usage is as simple as calling $('elem').spinner() and
    subsequently $('elem').spinner.remove(). You may create your own preloader
    at http://www.ajaxload.info. Please note that if you use a custom preloader,
    you must pass in the new height and width as options.
    
    Copyright (C) 2010 Corey Ballou
    Website: http://www.jqueryin.com
    Documentation: http://www.jqueryin.com/projects/spinner-jquery-preloader-plugin/

    This program is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License along
    with this program; if not, write to the Free Software Foundation, Inc.,
    51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 */
(function($) {
    $.fn.spinner = function(options) {
        var opts = $.extend({}, $.fn.spinner.defaults, options);

        return this.each(function() {
            var l=0, t=0, w=0, h=0, shim=0, $s;
            var $this = $(this);
            
            // removal handling
            if (options == 'remove' || options == 'close') {
                var $s = $this.data('spinner');
                var o = $this.data('opts');
                if (typeof $s != 'undefined') {
                    $s.remove();
                    $this.removeData('spinner').removeData('opts');
                    if (o.hide) $this.css('visibility', 'visible');
                    o.onFinish.call(this);
                    return;
                }
            }
            
            // retrieve element positioning
            var pos = $this.offset();
            w = $this.outerWidth();
            h = $this.outerHeight();
            
            // calculate vertical centering
            if (h > opts.height) shim = Math.round((h - opts.height)/ 2);
            else if (h < opts.height) shim = 0 - Math.round((opts.height - h) / 2);
            t = pos.top + shim + 'px';
            
            // calculate horizontal positioning
            if (opts.position == 'right') {
                l = pos.left + w + 10 + 'px';
            } else if (opts.position == 'left') {
                l = pos.left - opts.width - 10 + 'px';
            } else {
                l = pos.left + Math.round(.5 * w) - Math.round(.5 * opts.width) + 'px';
            }
            
            // call start callback
            opts.onStart.call(this);
            
            // hide element?
            if (opts.hide) $this.css('visibility', 'hidden');
            
            // create the spinner and attach
            $s = $('<img src="' + opts.img + '" style="position: absolute; left: ' + l +'; top: ' + t + '; width: ' + opts.width + 'px; height: ' + opts.height + 'px; z-index: ' + opts.zIndex + ';" />').appendTo('body');
            
            // removal handling
            $this.data('spinner', $s).data('opts', opts);
        });
    };
    
    // default spinner options
    $.fn.spinner.defaults = {
        position    : 'right'       // left, right, center
        , img       : 'spinner.gif' // path to spinner img
        , height    : 16            // height of spinner img
        , width     : 16            // width of spinner img
        , zIndex    : 1001          // z-index of spinner
        , hide      : false         // whether to hide the elem
        , onStart   : function(){ } // start callback
        , onFinish  : function(){ } // end callback
    };
})(jQuery);
