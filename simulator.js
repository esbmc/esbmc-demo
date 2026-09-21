'use strict';
var NEED = 10;         // body passes the loop needs
var K_OK  = 11;        // first bound that fully unrolls the loop (bound K cuts at K-1 passes)
var MODEL_X = 7;       // the solver's chosen model for the nondet input

var SRC = [
  '#include <assert.h>',
  'unsigned nondet_uint(void);',
  '',
  'int main(void) {',
  '  unsigned x = nondet_uint();',
  '  if (x > 10) return 0;      /* bounds x to 0..10 */',
  '  unsigned i = 0;',
  '  while (i < 10) {           /* the loop: exactly 10 passes */',
  '    i = i + 1;',
  '    if (x > 0) x = x - 1;',
  '  }',
  '  assert(x == 0);',
  '  return 0;',
  '}'
];

function $(id){ return document.getElementById(id); }
function esc(s){ return s.replace(/&/g,'&amp;').replace(/</g,'&lt;'); }
function bin32(v){ var s=(v>>>0).toString(2); while(s.length<32)s='0'+s;
  return '(' + s.slice(0,8)+' '+s.slice(8,16)+' '+s.slice(16,24)+' '+s.slice(24,32) + ')'; }

/* symex events for one pass-sequence at bound k; mode decides the cut handling */
function symexEvents(ev, k, mode, stRef){
  var passes = k === 0 ? NEED : Math.min(k - 1, NEED);
  var x = MODEL_X;
  for (var j = 1; j <= passes; j++) {
    ev.push({ line:8, kind:'guard',
      txt:'Unwinding loop 3 iteration ' + j + '   file main.c line 8 column 3 function main' });
    stRef.n++;
    ev.push({ line:9, kind:'assign', txt:'i = i + 1  →  i = ' + j,
      st:{ n:stRef.n, txt:'i = ' + j + ' ' + bin32(j) } });
    if (x > 0) {
      ev.push({ line:10, kind:'guard', txt:'guard x > 0: true, decrement taken' });
      x = x - 1;
      stRef.n++;
      ev.push({ line:10, kind:'assign', txt:'x = x - 1  →  x = ' + x,
        st:{ n:stRef.n, txt:'x = ' + x + ' ' + bin32(x) } });
    } else {
      ev.push({ line:10, kind:'guard', txt:'guard x > 0: false, x already 0' });
    }
  }
  var cut = k > 0 && passes < NEED;
  if (cut) {
    ev.push({ line:8, kind:'cut',
      txt:'Not unwinding loop 3 iteration ' + k + ': bound ' + k + ' reached at the back-edge' });
    if (mode === 'assert') {
      stRef.n++;
      ev.push({ line:8, kind:'prop', violated:true,
        txt:'unwinding assertion ¬(i < 10) fails here (i = ' + passes + ' < 10)',
        st:{ n:stRef.n, txt:'i = ' + passes + ' ' + bin32(passes) } });
    } else if (mode === 'assume') {
      ev.push({ line:8, kind:'guard', txt:'assume ¬(i < 10) with i = ' + passes + ': infeasible, path assumed away' });
    }
  } else if (k > 0 && passes === NEED) {
    ev.push({ line:8, kind:'guard', txt:'guard i < 10: false (i = ' + NEED + '), natural exit, no cut' });
  }
  return { x:x, cut:cut, passes:passes };
}

/* ---------- plain runs: (no flags) and --unwind K ---------- */
function buildPlain(cfg){
  var ev = []; var stRef = { n:0 };
  var bound = cfg.strat === 'plain' ? 0 : cfg.unwind;
  var mode = cfg.pl ? 'partial' : (cfg.noua ? 'assume' : 'assert');
  ev.push({ line:null, kind:'note',
    txt: bound === 0
      ? 'no --unwind: max_unwind = 0, symex unrolls until the loop condition stops it'
      : 'single BMC run with --unwind ' + bound + ' (no k loop)' });
  ev.push({ line:null, kind:'header', txt:'Starting Bounded Model Checking' });
  var r = symexEvents(ev, bound, mode, stRef);
  if (bound === 0 || !r.cut) {
    ev.push({ line:12, kind:'phase', sat:false,
      txt:'assert(x == 0) with x = ' + r.x + ': UNSAT' });
    ev.push({ line:null, kind:'end',
      verdict:{ cls:'ok', label:'VERIFICATION SUCCESSFUL' + (bound === 0 ? '' : ' (sound)') },
      txt: bound === 0
        ? 'no bound: the loop unrolled its natural 10 passes'
        : 'bound ' + bound + ' was never reached; the formula is UNSAT' });
  } else if (mode === 'assert') {
    ev.push({ line:null, kind:'end', violated:true,
      verdict:{ cls:'bad', label:'VERIFICATION FAILED: unwinding assertion loop' },
      txt:'the failing property is the CUT, not your assert' });
  } else if (mode === 'assume') {
    ev.push({ line:null, kind:'end',
      verdict:{ cls:'ok', label:'VERIFICATION SUCCESSFUL (bounded)' },
      txt:'paths past ' + bound + ' unwindings were assumed away; result holds only up to the bound' });
  } else {
    ev.push({ line:12, kind:'phase', sat:r.x > 0,
      txt:'truncated path reached the assert with i = ' + r.passes + ', x = ' + r.x +
          (r.x > 0 ? ': spurious violation' : ': holds by luck; pass ' + NEED + ' unchecked') });
    ev.push({ line:null, kind:'end', violated:r.x > 0,
      verdict: r.x > 0 ? { cls:'bad', label:'VERIFICATION FAILED: assertion (spurious)' }
                       : { cls:'ok', label:'VERIFICATION SUCCESSFUL (silently unsound)' },
      txt:'--partial-loops leaves the cut unguarded' });
  }
  return ev;
}

/* ---------- iterative strategies ---------- */
function buildIter(cfg){
  var ev = []; var stRef = { n:0 };
  var isKind = cfg.strat === 'kind' || cfg.strat === 'kindp';
  var stratFlag = { falsi:'--falsification', incr:'--incremental-bmc',
                    kind:'--k-induction', kindp:'--k-induction-parallel' }[cfg.strat];

  /* CLI validation, mirroring command_line_options.cpp */
  if (cfg.bks === 0) {
    ev.push({ line:null, kind:'end',
      verdict:{ cls:'bad', label:'CLI error' },
      txt:'error: Please specify --base-k-step >= 1: a base case of k = 0 sets --unwind 0, which ESBMC treats as unlimited unwinding.' });
    return ev;
  }
  if (!cfg.unl && cfg.ksi >= cfg.mks) {
    ev.push({ line:null, kind:'end', verdict:{ cls:'bad', label:'CLI error' },
      txt:'error: --k-step (' + cfg.ksi + ') must be smaller than --max-k-step (' + cfg.mks + ').' });
    return ev;
  }
  if (!cfg.unl && cfg.bks >= cfg.mks) {
    ev.push({ line:null, kind:'end', verdict:{ cls:'bad', label:'CLI error' },
      txt:'error: --base-k-step (' + cfg.bks + ') must be smaller than --max-k-step (' + cfg.mks + ').' });
    return ev;
  }

  ev.push({ line:null, kind:'note',
    txt:stratFlag + ': loops k from ' + cfg.bks + ' to ' + (cfg.unl ? '∞' : cfg.mks) +
        ' in steps of ' + cfg.ksi + '; round k re-runs symex with --unwind k' });

  var max = cfg.unl ? 999 : cfg.mks;
  var CAP_ROUNDS = 24;               /* demo build cap: stop building further rounds */
  var closed = null, built = 0;

  for (var k = cfg.bks; k <= max && !closed && built < CAP_ROUNDS; k += cfg.ksi) {
    built++;
    /* ---- base case B(k): no-unwinding-assertions, partial-loops=false ---- */
    ev.push({ line:null, kind:'header', round:'k=' + k + ' · B',
      txt:'Checking base case, k = ' + k });
    var rb = symexEvents(ev, k, 'assume', stRef);
    ev.push({ line:null, kind:'phase', sat:false,
      txt:'Base case: UNSAT, no violation up to k = ' + k });

    if (cfg.strat === 'falsi') continue;

    /* ---- forward condition F(k): only unwinding assertions checked ---- */
    ev.push({ line:null, kind:'header', round:'k=' + k + ' · F',
      txt:'Checking forward condition, k = ' + k });
    var fSat = k < K_OK;
    symexEvents(ev, k, 'assert', stRef);
    if (!fSat) {
      ev.push({ line:null, kind:'phase', sat:false,
        txt:'Forward condition holds at k = ' + k + ': every loop fully unrolled' });
      ev.push({ line:null, kind:'end',
        verdict:{ cls:'ok', label:'VERIFICATION SUCCESSFUL' },
        txt:'Solution found by the forward condition (k = ' + k + '): all loops fully unrolled, result not bounded' });
      closed = k;
      break;
    }
    ev.push({ line:null, kind:'phase', sat:true,
      txt:'Forward condition: SAT, a loop needed more than ' + k + ' unwindings' });

    /* ---- inductive step I(k) ---- */
    if (!isKind) continue;
    if (k === 1) {
      ev.push({ line:null, kind:'note', txt:'inductive step is not run at k = 1: a one-iteration hypothesis proves nothing' });
      continue;
    }
    if (cfg.mis >= 0 && k > cfg.mis) {
      ev.push({ line:null, kind:'note', txt:'inductive step skipped: k = ' + k + ' > --max-inductive-step ' + cfg.mis });
      continue;
    }
    ev.push({ line:null, kind:'header', round:'k=' + k + ' · I', txt:'Checking inductive step, k = ' + k });
    ev.push({ line:8, kind:'havoc', txt:'havoc at loop head: i ← nondet_uint(), x ← nondet_uint()' });
    ev.push({ line:8, kind:'guard', txt:'assume(i < 10): entry condition pins the havoced state' });
    ev.push({ line:12, kind:'phase', sat:true,
      txt:'Inductive step: SAT, spurious counterexample (havoc decoupled i from x: e.g. i = 9, x = 10)' });
    if (cfg.cex)
      ev.push({ line:null, kind:'note', txt:'--show-cex: cex states printed, i = 9, x = 10 … no real execution reaches this state' });
    if (cfg.bidir)
      ev.push({ line:null, kind:'note', txt:'--bidirectional: searching the spurious cex for assignable invariants' });
  }

  if (!closed) {
    if (built >= CAP_ROUNDS) {
      ev.push({ line:null, kind:'end', verdict:{ cls:'unk', label:'… (demo cap)' },
        txt:'further rounds omitted here; the run continues at k = ' + (cfg.bks + built * cfg.ksi) +
            (cfg.unl ? ' until --timeout/--memlimit' : ' up to --max-k-step ' + cfg.mks) });
    } else {
      ev.push({ line:null, kind:'end', verdict:{ cls:'unk', label:'VERIFICATION UNKNOWN' },
        txt:'Unable to prove or falsify the program, giving up. Exhausted k ≤ ' +
            (cfg.unl ? '∞' : cfg.mks) + ' without closing F(k)' + (isKind ? ' or I(k)' : '') });
    }
  }
  return ev;
}

function buildTimeline(cfg){
  if (cfg.strat === 'plain' || cfg.strat === 'unwind') return buildPlain(cfg);
  return buildIter(cfg);
}

/* ---------- rendering ---------- */
var step = 0, events = [], timer = null, oldHRef = null;

function readCfg(){
  return { strat: (document.querySelector('input[name=strat]:checked') || {}).value || 'plain',
           unwind: parseInt($('unwind').value,10) || 0,
           noua: $('noua').checked, pl: $('pl').checked,
           bks: parseInt($('bks').value,10), ksi: parseInt($('ksi').value,10),
           mks: parseInt($('mks').value,10), unl: $('unl').checked,
           mis: parseInt($('mis').value,10),
           cex: $('cex').checked, bidir: $('bidir').checked,
           limit: parseInt($('limit').value,10) || 40 };
}

function cmdline(cfg){
  var f = ['main.c'];
  if (cfg.strat === 'plain') { /* nothing */ }
  else if (cfg.strat === 'unwind') {
    f.push('--unwind ' + cfg.unwind);
    if (cfg.noua) f.push('--no-unwinding-assertions');
    if (cfg.pl) f.push('--partial-loops');
  } else {
    f.push({ falsi:'--falsification', incr:'--incremental-bmc',
             kind:'--k-induction', kindp:'--k-induction-parallel' }[cfg.strat]);
    f.push('--base-k-step ' + cfg.bks);
    f.push('--k-step ' + cfg.ksi);
    if (cfg.unl) f.push('--unlimited-k-steps'); else f.push('--max-k-step ' + cfg.mks);
    if (cfg.strat === 'kind' || cfg.strat === 'kindp') {
      if (cfg.mis >= 0) f.push('--max-inductive-step ' + cfg.mis);
      if (cfg.cex) f.push('--show-cex');
      if (cfg.bidir) f.push('--bidirectional');
    }
  }
  return 'esbmc ' + f.join(' ');
}

function visibility(cfg){
  var iterative = !(cfg.strat === 'plain' || cfg.strat === 'unwind');
  var kindish = cfg.strat === 'kind' || cfg.strat === 'kindp';
  $('grpGeneral').style.display = iterative ? 'none' : '';
  $('grpIter').style.display = iterative ? '' : 'none';
  $('grpKind').style.display = kindish ? '' : 'none';
}

function render(){
  var cfg = readCfg();
  visibility(cfg);
  $('cmdline').textContent = cmdline(cfg);
  events = buildTimeline(cfg);
  var truncated = events.length > cfg.limit;
  var shown = truncated ? cfg.limit : events.length;
  if (step >= shown) step = shown - 1;
  if (step < 0) step = 0;
  var cur = events[step];

  /* source */
  var seen = {};
  for (var i = 0; i <= step; i++) if (events[i].line) seen[events[i].line] = true;
  $('src').innerHTML = SRC.map(function(text, idx){
    var ln = idx + 1;
    var cls = 'ln' + (seen[ln] ? ' seen' : '') + (cur && cur.line === ln ? ' cur' : '');
    return '<span class="' + cls + '"><span class="no">' + ln + '</span>' + esc(text || ' ') + '</span>';
  }).join('');
  var visited = Object.keys(seen).length;
  $('coverage').textContent = 'source scan: ' + visited + ' of ' + SRC.length + ' lines visited' +
    (cur && cur.kind === 'havoc' ? ': havoc re-enters the loop head with fresh nondet values' : '') +
    (truncated ? ' (event limit ' + cfg.limit + ' reached; the real run continues)' : '');

  /* run output up to current step */
  var out = [];
  for (var i = 0; i <= step; i++) {
    var e = events[i];
    var cls = e.kind === 'prop' || e.violated ? 'bad'
            : e.kind === 'phase' ? (e.sat ? 'cut' : 'ok')
            : e.kind === 'cut' ? 'cut'
            : e.kind === 'note' ? 'note'
            : e.kind === 'header' || e.kind === 'end' ? 'sep' : '';
    if (e.st)
      out.push('<span class="st">State ' + e.st.n + ' file main.c line ' + e.line + ' column 3 function main thread 0</span>' +
               '<span class="st">----------------------------------------------------</span>' +
               '<span class="st' + (i === step ? ' cur' : '') + '">' + esc(e.st.txt) + '</span>');
    out.push('<span class="st' + (cls ? ' ' + cls : '') + (i === step && !e.st ? ' cur' : '') + '">' +
             esc(e.kind === 'end' ? '' : e.txt || '') + (e.kind === 'end' && e.verdict ? 'VERIFICATION ' + (e.verdict.cls === 'bad' ? 'FAILED' : e.verdict.cls === 'ok' ? 'SUCCESSFUL' : 'UNKNOWN') : '') + '</span>');
  }

  /* verdict line: last verdict at or before current step */
  var vd = $('verdict'); vd.textContent = ''; vd.className = 'verdict';
  for (var i = Math.min(step, shown - 1); i >= 0; i--) {
    if (events[i].verdict) {
      vd.textContent = events[i].verdict.label + '   (at event ' + (i + 1) + ')';
      vd.className = 'verdict ' + events[i].verdict.cls;
      break;
    }
  }

  /* timeline dots, grouped by round chips */
  var html = '';
  events.slice(0, shown).forEach(function(e, i){
    if (e.round) html += '<span class="dot header future-off" style="opacity:1">' + esc(e.round) + '</span>';
    var cls = 'dot ' + e.kind + (i === step ? ' cur' : '') + (i > step ? ' future' : '');
    html += '<span class="' + cls + '" data-i="' + i + '" title="' + esc(e.txt || '') + '">' +
            (e.kind === 'header' || e.kind === 'end' ? '' : (i + 1)) + '</span>';
  });
  $('dots').innerHTML = html;

  /* slide the run-output pane to its newest content: 0.5s ease-in-out both ways.
     The pane is bottom-pinned (justify-content:flex-end), so offsetHeight is the
     visible height and constant; measure scrollTop-free overflow instead. */
  var inner = $('termInner');
  var oldH = oldHRef === null ? inner.scrollHeight : oldHRef;
  inner.classList.remove('anim');
  inner.innerHTML = out.join('\n');
  var delta = inner.scrollHeight - oldH;
  if (delta !== 0) {
    inner.style.transform = 'translateY(' + Math.min(delta, 10000) + 'px)';
    void inner.offsetHeight;
    inner.classList.add('anim');
    inner.style.transform = 'translateY(0)';
  }
  oldHRef = inner.scrollHeight;
  /* a click must not yank the page to the focused element */
  if (document.activeElement && document.activeElement.blur)
    document.activeElement.blur();

  $('nowline').textContent = cur ? (cur.line ? 'line ' + cur.line + ': ' : '') + (cur.txt || cur.verdict && cur.verdict.label || '') : '';
  $('stepinfo').textContent = 'event ' + (step + 1) + ' / ' + shown + (truncated ? ' (limit)' : ' (end)');
  $('prev').disabled = step === 0;
  $('next').disabled = step >= shown - 1;
}

function stopAuto(){ if (timer) { clearInterval(timer); timer = null; $('auto').textContent = '⏵ auto'; } }

/* click handlers: preventDefault + blur so a click never scrolls the page */
$('dots').addEventListener('click', function(ev){
  var d = ev.target.closest ? ev.target.closest('.dot[data-i]') : null;
  if (!d) return;
  ev.preventDefault();
  stopAuto();
  step = parseInt(d.getAttribute('data-i'), 10);
  render();
  if (document.activeElement && document.activeElement.blur) document.activeElement.blur();
});
function pressed(id, fn){
  $(id).addEventListener('click', function(ev){
    ev.preventDefault();
    fn();
    if (document.activeElement && document.activeElement.blur) document.activeElement.blur();
  });
}
pressed('next', function(){ if (step < Math.min(readCfg().limit, events.length) - 1) { step++; render(); } });
pressed('prev', function(){ if (step > 0) { step--; render(); } });
pressed('auto', function(){
  if (timer) { stopAuto(); return; }
  $('auto').textContent = '⏸ pause';
  timer = setInterval(function(){
    var shown = Math.min(readCfg().limit, events.length);
    if (step >= shown - 1) { stopAuto(); return; }
    step++; render();
  }, 2000);
});
pressed('reset', function(){ step = 0; render(); });

/* param changes rebuild */
['unwind','noua','pl','bks','ksi','mks','unl','mis','cex','bidir','limit'].forEach(function(id){
  $(id).addEventListener('change', function(){ stopAuto(); step = 0; render(); });
});
document.querySelectorAll('#strategyPicker input').forEach(function(el){
  el.addEventListener('change', function(){ stopAuto(); step = 0; render(); });
});
document.addEventListener('keydown', function(e){
  if (e.key === 'ArrowRight') { stopAuto(); if (step < Math.min(readCfg().limit, events.length) - 1) { step++; render(); } }
  if (e.key === 'ArrowLeft')  { stopAuto(); if (step > 0) { step--; render(); } }
});

/* no scroll anchoring: growing panes must not pull the viewport */
if ('scrollRestoration' in history) history.scrollRestoration = 'manual';
try { document.documentElement.style.overflowAnchor = 'none'; } catch (e) {}

step = 0;
render();
