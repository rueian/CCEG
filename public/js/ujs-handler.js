(function ($, undefined) {
  'use strict';

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


})(jQuery);
