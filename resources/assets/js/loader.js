
window._ = require('lodash');

try {
    window.$ = window.jQuery = require('jquery');
} catch (e) {}

window.joint = require('jointjs');

window.axios = require('axios');

window.React = require('react');
window.ReactDOM = require('react-dom');
window.PreviewForm = require("./components/PreviewForm").default;
window.InspectDetail = require("./components/InspectDetail").default;

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
    if (data.responseJSON) {
        let response = data.responseJSON;
        if (response.error) {
            alert(response.error);
        } else if (response.message) {
            alert(response.message);
        } else if (response.msg) {
            alert(response.msg);
        } else if (response.result) {
            alert(response.result);
        }

        if (response.refresh) {
            window.location.reload();
        }
    } else {
        alert(data.responseText);
    }
});


require('./lib/bootstrap-3.3.7');
require('./lib/bootstrap-editable-1.5.1');

$.fn.editable.defaults.mode = 'inline';
$.fn.editable.defaults.send = "always";
$.fn.editable.defaults.ajaxOptions = { type: "PUT" };
$(document).ready(function () {
    $('[data-editable]').editable();
});


