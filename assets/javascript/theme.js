/* Theme switcher: System / Light / Dark. */
(function () {
  'use strict';
  var select = document.getElementById('theme-select');
  if (!select) return;
  select.value = document.documentElement.getAttribute('data-theme') || 'system';
  select.addEventListener('change', function () {
    var v = select.value;
    if (v === 'light' || v === 'dark') document.documentElement.setAttribute('data-theme', v);
    else document.documentElement.removeAttribute('data-theme');
    try {
      if (v === 'system') localStorage.removeItem('localvault-theme');
      else localStorage.setItem('localvault-theme', v);
    } catch (e) { /* the choice still applies for this visit */ }
  });
})();
