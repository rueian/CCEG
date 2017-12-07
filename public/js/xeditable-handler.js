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

