
window._ = require('lodash');

try {
    window.$ = window.jQuery = require('jquery');
} catch (e) {}

window.axios = require('axios');

window.axios.defaults.headers.common['X-Requested-With'] = 'XMLHttpRequest';

let token = document.head.querySelector('meta[name="csrf-token"]');

if (token) {
    window.axios.defaults.headers.common['X-CSRF-TOKEN'] = token.content;
} else {
    console.error('CSRF token not found: https://laravel.com/docs/csrf#csrf-x-csrf-token');
}

require('./lib/ujs');
$(document).on('ajax:success', function (event, data) {
    setTimeout(function () {
        if (data.redirect) {
            window.location = data.redirect;
        } else {
            var $target = $(event.target);
            if ($target.data('redirect')) {
                window.location = $target.data('redirect');
            } else {
                window.location.reload();
            }
        }
    }, 500);
});
$(document).on('ajax:error', function (event, data) {
    alert(data);
});


require('./lib/bootstrap-4.0.0-beta.2.bundle');
require('./lib/bootstrap-editable-1.5.1');

$.fn.editable.defaults.mode = 'inline';
$.fn.editableform.buttons =
    '<button type="submit" class="btn btn-primary btn editable-submit">' +
    '儲存' +
    '</button>' +
    '<button type="button" class="btn btn-default btn editable-cancel">' +
    '取消' +
    '</button>';
$.fn.editable.defaults.send = "always";
$.fn.editable.defaults.ajaxOptions = { type: "PUT" };
$(document).ready(function () {
    $('[data-editable]').editable();
});


