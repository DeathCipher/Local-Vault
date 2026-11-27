/* Loaded in <head> so the saved theme applies before first paint (no flash).
   No saved choice means "system": the CSS follows the operating system. */
(function () {
  document.documentElement.classList.remove('no-js');
  try {
    var t = localStorage.getItem('localvault-theme');
    if (t === 'light' || t === 'dark') document.documentElement.setAttribute('data-theme', t);
  } catch (e) { /* storage blocked: stay on the system theme */ }
})();
