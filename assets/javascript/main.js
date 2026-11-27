/* LocalVault download site: release details, copy buttons, download feedback.
   Everything here is an enhancement; the pages work without JavaScript. */
(function () {
  'use strict';

  var root = document.body.getAttribute('data-root') || '';
  var installerUrl = root + 'assets/downloads/localvault.msi';
  var status = document.getElementById('dl-status');
  var downloads = Array.prototype.slice.call(document.querySelectorAll('a[data-download]'));
  var served = /^https?:$/.test(location.protocol);
  var unavailable = false;

  /* Release details come from release.json; the HTML holds the same values as a fallback. */
  function fmtSize(bytes) { return (bytes / 1048576).toFixed(1) + ' MB'; }
  function fmtDate(iso) {
    var d = new Date(iso + 'T12:00:00');
    return isNaN(d) ? iso : d.toLocaleDateString('en-GB', { day: 'numeric', month: 'long', year: 'numeric' });
  }
  function setAll(key, text) {
    Array.prototype.forEach.call(document.querySelectorAll('[data-release="' + key + '"]'), function (n) { n.textContent = text; });
  }
  if (served && window.fetch) {
    fetch(root + 'assets/downloads/release.json', { cache: 'no-store' })
      .then(function (r) { return r.ok ? r.json() : Promise.reject(); })
      .then(function (rel) {
        if (rel.version) setAll('version', rel.version);
        if (rel.size) setAll('size', fmtSize(rel.size));
        if (rel.date) setAll('date', fmtDate(rel.date));
        if (rel.sha256) setAll('sha256', rel.sha256);
      })
      .catch(function () { /* keep the built-in values */ });

    /* If the installer file is missing, say so instead of letting the browser save a 404 page. */
    fetch(installerUrl, { method: 'HEAD' })
      .then(function (r) { if (!r.ok) throw new Error('missing'); })
      .catch(function () {
        unavailable = true;
        downloads.forEach(function (a) { a.setAttribute('aria-disabled', 'true'); });
        if (status) {
          status.textContent = 'The installer isn\u2019t available on this server right now. Ask whoever runs this site to check that localvault.msi is in assets/downloads.';
          status.classList.add('error');
        }
      });
  }

  /* Screen-reader announcement for the copy buttons. */
  var live = document.createElement('div');
  live.className = 'visually-hidden';
  live.setAttribute('role', 'status');
  live.setAttribute('aria-live', 'polite');
  document.body.appendChild(live);

  /* navigator.clipboard only exists on https or localhost, so a plain
     http://192.168.x.x address needs the older execCommand route. */
  function copyText(text) {
    if (navigator.clipboard && window.isSecureContext) return navigator.clipboard.writeText(text);
    return new Promise(function (resolve, reject) {
      var ta = document.createElement('textarea');
      ta.value = text;
      ta.setAttribute('readonly', '');
      ta.style.cssText = 'position:fixed;top:0;left:0;opacity:0';
      document.body.appendChild(ta);
      ta.select();
      var ok = false;
      try { ok = document.execCommand('copy'); } catch (e) {}
      document.body.removeChild(ta);
      ok ? resolve() : reject();
    });
  }
  Array.prototype.forEach.call(document.querySelectorAll('[data-copy-target]'), function (btn) {
    btn.addEventListener('click', function () {
      var target = document.getElementById(btn.getAttribute('data-copy-target'));
      if (!target) return;
      copyText(target.textContent.trim()).then(function () {
        btn.textContent = 'Copied';
        btn.classList.add('copied');
        live.textContent = 'Checksum copied to the clipboard.';
      }, function () {
        btn.textContent = 'Press Ctrl+C';
        live.textContent = 'Copy failed. The checksum is selected; press Ctrl+C.';
        var range = document.createRange();
        range.selectNodeContents(target);
        var sel = window.getSelection();
        sel.removeAllRanges();
        sel.addRange(range);
      });
      setTimeout(function () { btn.textContent = 'Copy'; btn.classList.remove('copied'); }, 2200);
    });
  });

  /* Download links: the padlock opens and a short message says what to do next. */
  var padlock = document.querySelector('.padlock');
  downloads.forEach(function (a) {
    a.addEventListener('click', function (e) {
      if (unavailable) { e.preventDefault(); return; }
      if (padlock) padlock.classList.add('open');
      if (status) {
        status.classList.remove('error');
        status.classList.add('done');
        status.textContent = 'Download started. When it finishes, open the file to install.';
      }
    });
  });

  /* The installer is for Windows only. */
  var note = document.getElementById('platform-note');
  if (note && !/Windows/i.test(navigator.userAgent)) note.hidden = false;
})();
