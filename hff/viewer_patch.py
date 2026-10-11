"""Layout fixes for the HFF map viewer (viewer_template.html), applied by build.py.

1. The page can never be wider than the window: the progress strip has one cell per block, and
   with ~100 blocks its fixed-width cells made the page about 1780px wide, pushing the reading
   panel off the right edge of the screen. The cells now shrink (and wrap if needed).
2. The reading panel is wider by default (34% of the window, between 400px and 760px) and can be
   resized by dragging its left edge (or with the arrow keys on the focused edge; double-click
   resets). The chosen width is remembered in this browser.
3. Formulas wider than the panel are scaled down to fit (to at most 70%); a formula that is still
   too wide gets its own horizontally scrollable line, instead of running off the panel.
4. (Lean-friendly version) The reading panel shows, directly under the statement of a block, the
   names of its Lean declarations (field "lean" of the block in the map JSON) and, if the build
   found hff/lean_status.json, the Lean status of the block (field "lean_status": "proved",
   "sorry" or "definition"), e.g. "Lean: rev_involution · proved in Lean". The search box also
   matches Lean names.
"""

CSS_SUBS = [
    ('.app{display:grid;grid-template-rows:auto minmax(0,1fr);height:100%}',
     '.app{display:grid;grid-template-rows:auto minmax(0,1fr);grid-template-columns:minmax(0,1fr);height:100%}'),
    ('.tools{display:flex;flex-wrap:wrap;align-items:center;gap:8px}',
     '.tools{display:flex;flex-wrap:wrap;align-items:center;gap:8px;min-width:0}'),
    ('.progress{display:flex;align-items:center;gap:8px;',
     '.progress{display:flex;align-items:center;gap:8px;min-width:0;'),
    ('.cells{display:flex;gap:3px}',
     '.cells{display:flex;flex-wrap:wrap;gap:3px;flex:0 1 auto;min-width:0;'
     'width:min(calc(var(--n, 10) * 17px), 520px, 34vw)}'),
    ('.cell{width:14px;height:10px;border-radius:2px;background:var(--band)}',
     '.cell{flex:1 1 0;min-width:2px;max-width:14px;height:10px;border-radius:2px;background:var(--band)}'),
    ('.main{display:grid;grid-template-columns:minmax(0,1fr) 400px;min-height:0;position:relative}',
     '.main{--panel-w:clamp(400px,34vw,760px);display:grid;grid-template-columns:minmax(0,1fr) var(--panel-w);'
     'min-height:0;position:relative}'),
    ('mjx-container[jax="SVG"][display="true"]{margin:.5em 0 !important;overflow-x:auto;overflow-y:hidden}',
     'mjx-container[jax="SVG"][display="true"]{margin:.5em 0 !important;overflow-x:auto;overflow-y:hidden}\n'
     '.panel mjx-container[jax="SVG"][display="true"]{max-width:100%}\n'
     '.panel mjx-container.mjx-wide{display:block;max-width:100%;overflow-x:auto;overflow-y:hidden;'
     'margin:.35em 0;padding-bottom:2px}\n'
     '.panel .m.m-wrap{white-space:normal;overflow-wrap:anywhere}\n'
     '.nobr{white-space:nowrap}\n'
     '.splitter{position:absolute;top:0;bottom:0;right:var(--panel-w);width:12px;margin-right:-6px;'
     'cursor:col-resize;z-index:7;touch-action:none;outline:none}\n'
     '.splitter::after{content:"";position:absolute;top:0;bottom:0;left:5px;width:2px;background:transparent;'
     'transition:background .15s}\n'
     '.splitter:hover::after,.splitter.active::after,.splitter:focus-visible::after{background:var(--accent)}\n'
     'body.resizing,body.resizing *{cursor:col-resize !important;user-select:none !important}'),
    ('#panelToggle{display:inline-flex}',
     '#panelToggle{display:inline-flex}\n  .splitter{display:none}'),
]

HTML_SUBS = [
    ('<aside class="panel" id="panel" aria-live="polite"></aside>',
     '<div class="splitter" id="splitter" role="separator" aria-orientation="vertical" tabindex="0" '
     'aria-label="Resize the panel" title="Drag to resize the panel (double-click to reset)"></div>\n'
     '    <aside class="panel" id="panel" aria-live="polite"></aside>'),
]

JS_SUBS = [
    ("      return textHTML(p, links);\n    }).join('');",
     "      return textHTML(p, links);\n    }).join('')\n"
     "      // keep punctuation that follows an inline formula on the formula's line\n"
     "      .replace(/(<span class=\"(?:mjx-ph\" data-d=\"0|m)\">(?:(?!<\\/span>)[\\s\\S])*<\\/span>)([,.;:)]+)/g,\n"
     "               '<span class=\"nobr\">$1$2</span>');"),
    ("c.className = 'cell'; cellsEl.appendChild(c); });",
     "c.className = 'cell'; cellsEl.appendChild(c); });\n"
     "  cellsEl.style.setProperty('--n', blocks.length);\n"
     "  if (blocks.length > 40) cellsEl.style.gap = '1px';"),
    ('  /* ---------------- start ---------------- */',
     r"""  /* ---------------- resizable panel and wide formulas (layout patch) ---------------- */
  var mainEl = document.querySelector('.main'), splitter = $('#splitter');
  var PANEL_KEY = 'hff-map:' + DATA.slug + ':panel-width';
  function panelLimits() {
    var w = mainEl.getBoundingClientRect().width;
    return { min: 320, max: Math.max(320, w - 260) };
  }
  function setPanelWidth(px, save) {
    if (px == null) mainEl.style.removeProperty('--panel-w');
    else {
      var l = panelLimits();
      px = Math.round(Math.min(l.max, Math.max(l.min, px)));
      mainEl.style.setProperty('--panel-w', px + 'px');
    }
    if (save) {
      try { if (px == null) localStorage.removeItem(PANEL_KEY); else localStorage.setItem(PANEL_KEY, String(px)); } catch (e) {}
    }
    cam = clampCam(cam); apply();
  }
  try { var savedW = parseFloat(localStorage.getItem(PANEL_KEY)); if (savedW > 0) setPanelWidth(savedW, false); } catch (e) {}
  var dragging = false;
  splitter.addEventListener('pointerdown', function (e) {
    if (e.button !== 0) return;
    dragging = true;
    try { splitter.setPointerCapture(e.pointerId); } catch (err) {}
    splitter.classList.add('active'); document.body.classList.add('resizing');
    e.preventDefault();
  });
  splitter.addEventListener('pointermove', function (e) {
    if (dragging) setPanelWidth(mainEl.getBoundingClientRect().right - e.clientX, false);
  });
  function endDrag() {
    if (!dragging) return;
    dragging = false;
    splitter.classList.remove('active'); document.body.classList.remove('resizing');
    setPanelWidth(panel.getBoundingClientRect().width, true);
  }
  splitter.addEventListener('pointerup', endDrag);
  splitter.addEventListener('pointercancel', endDrag);
  splitter.addEventListener('lostpointercapture', endDrag);
  splitter.addEventListener('dblclick', function () { setPanelWidth(null, true); });
  splitter.addEventListener('keydown', function (e) {
    var step = e.shiftKey ? 80 : 24, w = panel.getBoundingClientRect().width;
    if (e.key === 'ArrowLeft') setPanelWidth(w + step, true);
    else if (e.key === 'ArrowRight') setPanelWidth(w - step, true);
    else if (e.key === 'Home' || e.key === 'Enter') setPanelWidth(null, true);
    else return;
    e.preventDefault(); e.stopPropagation();
  });
  window.addEventListener('resize', function () {
    var v = parseFloat(mainEl.style.getPropertyValue('--panel-w'));
    if (v > 0) setPanelWidth(v, false);
  });

  // Formulas wider than the panel: scale down to fit (to at most MIN_SCALE); if still too wide,
  // the formula gets its own horizontally scrollable line.
  var MIN_SCALE = 0.7, MIN_INLINE = 0.85;
  function scaleUnit(v, k) {
    var m = /^\s*(-?[\d.]+)([a-z%]*)\s*$/.exec(v || '');
    return m ? (parseFloat(m[1]) * k).toFixed(3) + m[2] : v;
  }
  function fitFormula(c, avail) {
    var svg = c.firstElementChild;
    if (!svg || svg.tagName.toLowerCase() !== 'svg') return;
    if (svg.getAttribute('data-w0') == null) {
      svg.setAttribute('data-w0', svg.getAttribute('width') || '');
      svg.setAttribute('data-h0', svg.getAttribute('height') || '');
      svg.setAttribute('data-va0', svg.style.verticalAlign || '');
    }
    var w0 = svg.getAttribute('data-w0'), h0 = svg.getAttribute('data-h0'), va0 = svg.getAttribute('data-va0');
    if (w0) svg.setAttribute('width', w0);
    if (h0) svg.setAttribute('height', h0);
    svg.style.verticalAlign = va0;
    c.classList.remove('mjx-wide');
    var w = svg.getBoundingClientRect().width;
    if (!w || w <= avail + 0.5 || !w0 || !h0) return;
    var display = c.getAttribute('display') === 'true', s = avail / w;
    if (!display && s < MIN_INLINE) c.classList.add('mjx-wide');
    var k = Math.max(s, (display || s < MIN_INLINE) ? MIN_SCALE : MIN_INLINE);
    svg.setAttribute('width', scaleUnit(w0, k));
    svg.setAttribute('height', scaleUnit(h0, k));
    if (va0) svg.style.verticalAlign = scaleUnit(va0, k);
  }
  function fitFallback(sp, avail) {
    sp.classList.remove('m-wrap');
    if (!sp.classList.contains('disp') && sp.getBoundingClientRect().width > avail + 0.5) sp.classList.add('m-wrap');
  }
  var fitQueued = false;
  function fitPanelMath() {
    fitQueued = false;
    if (panel.classList.contains('collapsed')) return;
    var items = panel.querySelectorAll('mjx-container, .m');
    for (var i = 0; i < items.length; i++) {
      var c = items[i], host = c.parentElement && c.parentElement.closest('.rich, h2, .h, li, p, section, div');
      if (!host || host === c) continue;
      var cs = getComputedStyle(host);
      var avail = host.clientWidth - (parseFloat(cs.paddingLeft) || 0) - (parseFloat(cs.paddingRight) || 0);
      if (avail <= 0) continue;
      if (c.tagName.toLowerCase() === 'mjx-container') fitFormula(c, avail); else fitFallback(c, avail);
    }
  }
  function queueFit() { if (!fitQueued) { fitQueued = true; requestAnimationFrame(fitPanelMath); } }
  if (window.ResizeObserver) new ResizeObserver(queueFit).observe(panel);
  new MutationObserver(queueFit).observe(panel, { childList: true, subtree: true });
  if (document.fonts && document.fonts.ready) document.fonts.ready.then(queueFit);

  /* ---------------- start ---------------- */"""),
]


LEAN_CSS_SUBS = [
    ('.none{font:400 13.5px/1.5 var(--font-body);color:var(--muted);margin:0}',
     '.none{font:400 13.5px/1.5 var(--font-body);color:var(--muted);margin:0}\n'
     '.leanline{font:400 12.5px/1.5 var(--font-body);color:var(--muted);margin:2px 0 0;overflow-wrap:anywhere}\n'
     '.leanline code{font:500 12px/1.4 var(--font-mono);color:var(--muted)}\n'
     '.leanline .leanst{white-space:nowrap}\n'
     '.leanline .leanst-proved{color:var(--accent)}'),
]

LEAN_JS_SUBS = [
    ('  function renderBlock(id) {',
     r"""  // Lean declarations of a block (and their status, if lean_status.json was found by the build)
  var LEAN_STATUS = { proved: 'proved in Lean', complete: 'proved in Lean', sorry: 'not yet proved in Lean (sorry)',
                      definition: 'definition in Lean' };
  function leanLine(b) {
    var p = document.createElement('p');
    p.className = 'leanline';
    p.appendChild(document.createTextNode('Lean: '));
    b.lean.forEach(function (n, i) {
      if (i) p.appendChild(document.createTextNode(', '));
      var c = document.createElement('code'); c.textContent = n; p.appendChild(c);
    });
    if (b.lean_status) {
      var st = document.createElement('span');
      st.className = 'leanst leanst-' + String(b.lean_status).replace(/[^A-Za-z]/g, '');
      st.textContent = '\u00b7 ' + (LEAN_STATUS[b.lean_status] || String(b.lean_status));
      p.appendChild(document.createTextNode(' '));
      p.appendChild(st);
    }
    return p;
  }

  function renderBlock(id) {"""),
    ('    s1.appendChild(richDiv(b.statement)); panel.appendChild(s1);',
     '    s1.appendChild(richDiv(b.statement));\n'
     '    if (b.lean && b.lean.length) s1.appendChild(leanLine(b));\n'
     '    panel.appendChild(s1);'),
    ("(label(b) + ' ' + plain(b.header) + ' ' + plain(b.statement)).toLowerCase().indexOf(q) >= 0;",
     "(label(b) + ' ' + plain(b.header) + ' ' + plain(b.statement) + ' ' + (b.lean || []).join(' ')).toLowerCase().indexOf(q) >= 0;"),
]


def patch(html):
    for old, new in CSS_SUBS + HTML_SUBS + JS_SUBS + LEAN_CSS_SUBS + LEAN_JS_SUBS:
        if html.count(old) != 1:
            raise SystemExit('viewer layout patch failed: ' + old[:70])
        html = html.replace(old, new)
    return html
