/* Faultline — UI layer (rendering, state, events). Depends on engine.js */
/* =====================================================================
   FAULTLINE UI
   ===================================================================== */
const $ = s => document.querySelector(s);
const esc = s => String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const DOMAINS = { w: 'Wi‑Fi', d: 'Display', p: 'Power', a: 'Audio', s: 'Performance', g: 'General', c: 'Custom' };
const domOf = r => r.custom ? 'c' : (DOMAINS[r.id[0]] ? r.id[0] : 'c');

/* ---------- notation ---------- */
function vH(n) { const m = n.match(/^([A-Za-z]+)_(\d+)$/); return `<span class="v">${m ? `${m[1]}<sub>${m[2]}</sub>` : esc(n)}</span>`; }
function tH(t) { if (t.t === 'v') return vH(t.n); if (t.t === 'c') return `<span class="k">${esc(t.n)}</span>`; return `<span class="fn">${esc(t.n)}</span>(${t.a.map(tH).join(', ')})`; }
function lH(l) { return `${l.neg ? '<span class="neg">¬</span>' : ''}<span class="p">${esc(l.p)}</span>${l.a.length ? `(${l.a.map(tH).join(', ')})` : ''}`; }
const AND = '<span class="op">∧</span>', OR = '<span class="op">∨</span>', IMP = '<span class="op">⇒</span>';
function ruleH(r) {
  const vs = varsOf([...r.body, r.head]);
  return `${vs.length ? `<span class="op">∀</span>${vs.map(vH).join(',')} ` : ''}${r.body.map(lH).join(` ${AND} `)} ${IMP} ${lH(r.head)}`;
}
function clauseH(lits) {
  if (!lits.length) return '<b>□</b> <span class="muted">(empty clause)</span>';
  return lits.map(l => l.p === 'Ans' ? `<span class="p" style="color:var(--accent)">Ans</span>(${l.a.map(tH).join(', ')})` : lH(l)).join(` ${OR} `);
}
function thH(th, only) {
  const ks = Object.keys(th).filter(k => !only || only.has(k));
  if (!ks.length) return '{ }';
  return '{' + ks.map(k => `${vH(k)}/${tH(subst(th, V(k)))}`).join(', ') + '}';
}
const pct = x => Math.round(x * 100) + '%';
const humanize = s => s.replace(/_/g, ' ').replace(/^./, c => c.toUpperCase());
const sevOf = f => { const x = KB.facts.find(l => l.p === 'severity' && l.a[0].n === f); return x ? x.a[1].n : 'medium'; };
const valClass = v => v === true ? 'yes' : v === false ? 'no' : 'unk';
const valText = v => v === true ? 'Yes' : v === false ? 'No' : 'Don’t know';

/* ---------- state ---------- */
const S = {
  tab: 'diagnose',
  describe: 'My laptop isn’t connecting to Wi‑Fi.',
  intakeMsg: null,
  sym: null, answers: {}, asked: [], pending: null, result: null,
  kbFilter: 'all', kbMsg: null, kbDraft: '',
  lab: { scenario: 'wifi-brief', mode: 'forward', fcShown: null, query: 'fault(wifi, X)', bc: null, sel: 0, err: null },
  uni: { a: 'knows(john, X)', b: 'knows(Y, mother(Y))' },
  res: { scenario: 'wifi-brief', query: 'fault(wifi, X)', out: null, err: null },
};
function loadCustom() { try { return JSON.parse(localStorage.getItem('faultline.custom') || '[]'); } catch (e) { return []; } }
function saveCustom() { try { localStorage.setItem('faultline.custom', JSON.stringify(KB.rules.filter(r => r.custom).map(r => r.src).concat(KB.facts.filter(f => f.custom).map(f => f.src)))); } catch (e) { } }
const scenAnswers = k => k === 'session' ? S.answers : PRESETS[k].answers;
const scenGoal = k => k === 'session' ? (S.sym ? `fault(${S.sym}, X)` : 'fault(wifi, X)') : PRESETS[k].goal;

/* =====================================================================
   DIAGNOSE
   ===================================================================== */
function startSymptom(id) {
  S.sym = id; S.answers = {}; S.asked = []; S.result = null; S.pending = null;
  runInterview();
}
function runInterview() {
  GEN = 0;
  const goal = parseQuery(`fault(${S.sym}, X)`)[0];
  const P = makeProver(S.answers, { ask: true });
  try {
    const r = P.prove(goal, {}, 0, []).next();
    S.pending = null;
    if (r.done) S.result = { none: true };
    else {
      const node = finalize(r.value.node, r.value.th);
      const fault = subst(r.value.th, V('X')).n;
      const others = solveAll(`fault(${S.sym}, X)`, S.answers).sols.map(s => ({ f: s.binding[0][1].n, cf: s.cf })).filter(s => s.f !== fault);
      S.result = { node, fault, cf: node.cf, others, fc: forwardChain(S.answers) };
    }
  } catch (e) {
    if (e instanceof AskNeeded) { S.pending = e; S.result = null; } else throw e;
  }
  renderDiagnose();
}
function answer(v) {
  const e = S.pending; if (!e) return;
  const key = atomKey(e.lit);
  S.answers[key] = v; S.asked.push({ key, lit: e.lit, v });
  runInterview();
}
function changeAnswer(i) {
  S.asked.slice(i).forEach(a => delete S.answers[a.key]);
  S.asked = S.asked.slice(0, i);
  runInterview();
}

function renderDiagnose() {
  const sym = SYMPTOMS.find(s => s.id === S.sym);
  let main;
  if (!S.sym) main = intakeH();
  else main = (S.result ? resultH(sym) : questionH(sym)) + logH();
  $('#p-diagnose').innerHTML = `
    <div class="head"><div>
      <h1>${S.sym ? esc(sym.t) : 'Diagnose'}</h1>
    </div>${S.sym ? '<button class="btn" data-act="restart">New problem</button>' : ''}</div>
    <div class="dx"><div class="stack fade">${main}</div><aside class="wm">${wmH()}</aside></div>`;
}

function intakeH() {
  return `
  <div class="card intake">
    <label class="eyebrow" for="desc">Problem</label>
    <textarea id="desc" rows="2">${esc(S.describe)}</textarea>
    <div class="row"><button class="btn primary" data-act="analyze">Start diagnosis</button>
      ${S.intakeMsg ? `<span class="msg err">${esc(S.intakeMsg)}</span>` : ''}</div>
  </div>
  <div><h3 style="margin-top:6px">Symptoms</h3>
  <div class="sym-grid">${SYMPTOMS.map(s => `<button class="sym" data-act="pick" data-sym="${s.id}"><b>${esc(s.t)}</b><code>?- fault(${s.id}, X)</code></button>`).join('')}</div></div>`;
}

function questionH(sym) {
  const e = S.pending, q = ASK[e.lit.p];
  const chain = e.chain.slice().reverse();
  const why = chain.length ? `<ol class="chain">
      
      ${chain.map((c, i) => `<li><span class="rid">${c.rule.id}</span> · ${i === 0 ? 'Proving' : 'for'} <code class="fol">${lH(substLit(e.th, c.goal))}</code><div class="fol" style="margin-top:4px">${ruleH(c.rule)}</div></li>`).join('')}
      <li>Goal <code class="fol">${lH(parseQuery(`fault(${S.sym}, X)`)[0])}</code>.</li></ol>` : '';
  return `
  <div class="card qcard" aria-live="polite">
    <div class="qtop"><span class="eyebrow">Question ${S.asked.length + 1}</span><span class="goal" style="padding:4px 10px">?- ${lH(parseQuery(`fault(${S.sym}, X)`)[0])}</span></div>
    <code class="qlit fol">${lH(e.lit)} ?</code>
    <p class="qtext">${esc(q.q)}</p>
    <p class="qhint">${esc(q.h)}</p>
    <div class="answers">
      <button class="ans yes" data-act="answer" data-v="yes">Yes <kbd>Y</kbd></button>
      <button class="ans no" data-act="answer" data-v="no">No <kbd>N</kbd></button>
      <button class="ans unk" data-act="answer" data-v="unk">Don’t know <kbd>U</kbd></button>
    </div>
    <details class="why"><summary>Why?</summary>${why}</details>
  </div>`;
}

function treeH(n) {
  const badge = n.kind === 'rule' ? `<span class="b rule">rule ${n.rule.id} · cf ${n.cf.toFixed(2)}</span>`
    : n.kind === 'fact' ? '<span class="b fact">fact</span>'
      : n.kind === 'yes' ? '<span class="b yes">you: yes</span>'
        : n.kind === 'no' ? '<span class="b no">you: no</span>' : '<span class="b naf">not provable</span>';
  return `<li><span class="node">${lH(n.lit)} ${badge}</span>${n.children && n.children.length ? `<ul>${n.children.map(treeH).join('')}</ul>` : ''}</li>`;
}

function resultH(sym) {
  if (S.result.none) return `
  <div class="card result">
    <span class="eyebrow">Inconclusive</span>
    <h2 style="margin-top:6px">No diagnosis</h2>
    <p class="muted"><code>fault(${S.sym}, X)</code> is not provable.</p>
    <div class="row" style="margin-top:16px"><button class="btn" data-act="to-lab">Trace</button></div>
  </div>`;
  const r = S.result, info = FAULTS[r.fault] || { t: humanize(r.fault), s: 'Concluded by a custom rule.', steps: [] }, sev = sevOf(r.fault);
  const esc8 = r.fc.wm.some(w => w.lit.p === 'escalate' && w.lit.a[0].n === r.fault);
  return `
  <div class="card result">
    <span class="eyebrow">Diagnosis · X = ${esc(r.fault)}</span>
    <h2>${esc(info.t)}</h2>
    <div class="meta">
      <code class="fol">${lH({ p: 'fault', a: [C(S.sym), C(r.fault)], neg: false })}</code>
      <span class="sev ${sev}">${sev} severity</span>
      <span class="cfm">Certainty <b>${pct(r.cf)}</b><span class="bar"><i style="width:${pct(r.cf)}"></i></span></span>
    </div>
    <p style="max-width:66ch">${esc(info.s)}</p>
    ${esc8 ? `<p class="alert"><code>escalate(${esc(r.fault)})</code>: needs a technician.</p>` : ''}
    ${info.steps.length ? `<h3>Fix</h3><ol class="steps">${info.steps.map(s => `<li>${esc(s)}</li>`).join('')}</ol>` : ''}
    <h3>Proof</h3>
    <div class="scroll"><ul class="tree">${treeH(r.node)}</ul></div>
    ${r.others.length ? `<h3>Other matches</h3><ul style="margin:0;padding-left:20px">${r.others.map(o => `<li>${esc((FAULTS[o.f] || { t: humanize(o.f) }).t)} <span class="muted">(${pct(o.cf)})</span></li>`).join('')}</ul>` : ''}
    <div class="row" style="margin-top:20px">
      <button class="btn primary" data-act="to-lab">Inference lab</button>
      <button class="btn" data-act="to-res">Resolution</button>
    </div>
  </div>`;
}

function logH() {
  if (!S.asked.length) return '';
  return `<div class="log"><h3>Answers</h3><ol>${S.asked.map((a, i) => `
    <li><span class="n">${String(i + 1).padStart(2, '0')}</span>
      <span class="q">${esc(ASK[a.lit.p].q)}<code>${esc(atomKey(a.lit))} = ${a.v === 'unknown' ? 'unknown' : a.v}</code></span>
      <span class="row" style="gap:4px;flex-wrap:nowrap"><span class="val ${valClass(a.v)}">${valText(a.v)}</span><button data-act="change" data-i="${i}" aria-label="Change answer ${i + 1}">Change</button></span></li>`).join('')}</ol></div>`;
}

function wmH() {
  const kbF = KB.facts.filter(f => f.p === 'device' || f.p === 'router');
  const hidden = KB.facts.length - kbF.length;
  const der = S.result && !S.result.none ? S.result.fc.wm.filter(w => w.how.src === 'rule') : [];
  const nAsk = Object.keys(ASK).length;
  return `
  <div class="card">
    <h4>Goal</h4>
    <div class="goal">?- ${S.sym ? lH(parseQuery(`fault(${S.sym}, X)`)[0]) : '<span class="muted">—</span>'}</div>
  </div>
  <div class="card">
    <h4>Working memory <span>${kbF.length + S.asked.length + der.length} facts</span></h4>
    <ul>
      ${kbF.map(f => `<li><span class="dot kb"></span>${lH(f)}<span class="tag">kb</span></li>`).join('')}
      ${S.asked.map(a => `<li><span class="dot ${valClass(a.v)}"></span>${a.v === false ? lH({ ...a.lit, neg: true }) : a.v === 'unknown' ? lH(a.lit) + ' <span class="muted">= ?</span>' : lH(a.lit)}<span class="tag">you</span></li>`).join('')}
      ${der.map(w => `<li><span class="dot der"></span>${lH(w.lit)}<span class="tag">${w.how.rule.id}</span></li>`).join('')}
    </ul>
  </div>
  <div class="card stats">
    <div><b>${KB.rules.length}</b><span>rules</span></div>
    <div><b>${nAsk}</b><span>askables</span></div>
    <div><b>${S.asked.length}</b><span>asked</span></div>
  </div>`;
}

/* =====================================================================
   KNOWLEDGE BASE
   ===================================================================== */
function renderKB() {
  const doms = ['all', ...Object.keys(DOMAINS).filter(d => KB.rules.some(r => domOf(r) === d))];
  const rules = KB.rules.filter(r => S.kbFilter === 'all' || domOf(r) === S.kbFilter);
  const groups = {}; rules.forEach(r => (groups[domOf(r)] = groups[domOf(r)] || []).push(r));
  const preds = {};
  const note = (l, kind) => { const k = l.p + '/' + l.a.length; preds[k] = preds[k] || { p: l.p, n: l.a.length, kind, uses: 0 }; if (kind === 'derived') preds[k].kind = 'derived'; };
  KB.facts.forEach(f => note(f, 'fact'));
  KB.rules.forEach(r => { note(r.head, 'derived'); r.body.forEach(l => { note(l, ASK[l.p] ? 'askable' : 'fact'); preds[l.p + '/' + l.a.length].uses++; }); });
  const order = { askable: 0, derived: 1, fact: 2 };
  const plist = Object.values(preds).sort((a, b) => order[a.kind] - order[b.kind] || a.p.localeCompare(b.p));
  const ex = 'c1 [0.8]: device(D), wifi_on(D), vpn_active(D) => fault(wifi, vpn_conflict).\nvpn_active(lap).';
  $('#p-kb').innerHTML = `
  <div class="head"><div><h1>Knowledge base</h1></div>
    <div class="kpis"><div><b>${KB.rules.length}</b><span>rules</span></div><div><b>${KB.facts.length}</b><span>facts</span></div><div><b>${plist.length}</b><span>predicates</span></div></div></div>
  <div class="kb-grid">
    <div>
      <div class="filters">${doms.map(d => `<button class="chip" data-act="kbf" data-d="${d}" aria-pressed="${S.kbFilter === d}">${d === 'all' ? 'All rules' : DOMAINS[d]} <span class="muted">${d === 'all' ? KB.rules.length : KB.rules.filter(r => domOf(r) === d).length}</span></button>`).join('')}</div>
      <div class="rules">${Object.entries(groups).map(([d, rs]) => `<div class="dom">${DOMAINS[d]}</div>` + rs.map(r => {
        const npos = 1 + r.body.filter(l => l.neg).length;
        const clause = [...r.body.map(l => ({ ...l, neg: !l.neg })), r.head];
        return `<div class="rule"><div class="id">${esc(r.id)}<small>cf ${r.cf.toFixed(2)}</small></div>
          <div style="min-width:0"><div class="fol">${ruleH(r)}</div>
            <details><summary>CNF</summary><div class="forms fol">
              <div><span>Implication-free</span><div>${varsOf(clause).length ? '∀' + varsOf(clause).map(vH).join(',') + ' ' : ''}<span class="neg">¬</span>(${r.body.map(lH).join(` ${AND} `)}) ${OR} ${lH(r.head)}</div></div>
              <div><span>CNF clause</span><div>${clauseH(clause)}</div></div>
              <div><span>Horn?</span><div style="font-family:var(--body)">${npos === 1 ? 'Yes' : `No (${npos} positive literals)`}</div></div>
            </div></details></div>
          ${r.custom ? `<button class="btn small" data-act="delrule" data-id="${esc(r.id)}">Remove</button>` : '<span></span>'}</div>`;
      }).join('')).join('')}</div>
    </div>
    <div class="stack">
      <div class="card">
        <h2 style="font-size:18px">Add rule / fact</h2>
        <p class="syntax"><code>id [cf]: p(X), not q(X) => r(X).</code></p>
        <textarea id="kbin" class="mono" rows="4" style="margin-top:10px" placeholder="${esc(ex)}">${esc(S.kbDraft)}</textarea>
        <div class="row" style="margin-top:10px"><button class="btn primary" data-act="kbadd">Add</button><button class="btn" data-act="kbex">Example</button></div>
        ${S.kbMsg ? `<p class="msg ${S.kbMsg.ok ? 'ok' : 'err'}" style="margin:10px 0 0">${S.kbMsg.html}</p>` : ''}
        ${KB.facts.some(f => f.custom) ? `<h3>Custom facts</h3><ul style="margin:0;padding:0;list-style:none;display:grid;gap:6px">${KB.facts.filter(f => f.custom).map(f => `<li class="row" style="justify-content:space-between"><code class="fol">${lH(f)}</code><button class="btn small" data-act="delfact" data-k="${esc(atomKey(f))}">Remove</button></li>`).join('')}</ul>` : ''}
      </div>
      <div>
        <h3 style="margin-top:0">Predicates</h3>
        <div class="tablebox"><table><thead><tr><th>Predicate</th><th>Type</th><th>Question / source</th></tr></thead><tbody>
        ${plist.map(p => `<tr><td><code class="p">${esc(p.p)}</code><span class="muted">/${p.n}</span></td><td><span class="kind ${p.kind}">${p.kind}</span></td><td>${p.kind === 'askable' ? esc(ASK[p.p].q) : p.kind === 'derived' ? `<span class="muted">${KB.rules.filter(r => r.head.p === p.p).map(r => r.id).join(', ')}</span>` : `<span class="muted">${KB.facts.filter(f => f.p === p.p).length} facts</span>`}</td></tr>`).join('')}
        </tbody></table></div>
      </div>
    </div>
  </div>`;
}

/* =====================================================================
   INFERENCE LAB
   ===================================================================== */
function scenSelect(id, sel) {
  const opts = [['session', S.asked.length ? `Current session (${S.asked.length})` : 'Current session (empty)'], ...Object.entries(PRESETS).map(([k, p]) => [k, p.label])];
  return `<label class="eyebrow lbl" for="${id}">Scenario</label><select id="${id}">${opts.map(([k, l]) => `<option value="${k}" ${k === sel ? 'selected' : ''}>${esc(l)}</option>`).join('')}</select>`;
}
function answerChips(ans) {
  const es = Object.entries(ans);
  if (!es.length) return '<span class="muted" style="font-size:13px">No answers</span>';
  return es.map(([k, v]) => `<span class="lit-chip ${valClass(v)}">${v === false ? '¬' : ''}${esc(k)}${v === 'unknown' ? ' = ?' : ''}</span>`).join('');
}
function runBackward() {
  const L = S.lab;
  try { const trace = []; const out = solveAll(L.query, scenAnswers(L.scenario), { trace, html: lH }); L.bc = { ...out, trace }; L.err = null; L.sel = 0; }
  catch (e) { L.bc = null; L.err = e.message; }
}
function renderLab() {
  const L = S.lab, ans = scenAnswers(L.scenario);
  let body;
  if (L.mode === 'forward') {
    const fc = forwardChain(ans);
    const shown = L.fcShown === null ? fc.cycles.length : Math.min(L.fcShown, fc.cycles.length);
    const init = fc.wm.slice(0, fc.initial);
    const goals = fc.wm.filter(w => w.how.src === 'rule' && (w.lit.p === 'fault' || w.lit.p === 'escalate') && w.how.cycle <= shown);
    body = `
    <div class="row" style="margin-bottom:16px">
      <button class="btn primary" data-act="fc-next" ${shown >= fc.cycles.length ? 'disabled' : ''}>Next cycle</button>
      <button class="btn" data-act="fc-all" ${shown >= fc.cycles.length ? 'disabled' : ''}>Run all</button>
      <button class="btn" data-act="fc-reset" ${shown === 0 ? 'disabled' : ''}>Reset</button>
      <span class="muted" style="font-size:13px">Cycle ${shown} of ${fc.cycles.length}</span>
    </div>
    <div class="lab-grid">
      <div class="stack">
        ${fc.cycles.slice(0, shown).map(c => `<div class="cycle fade"><header>Cycle ${c.n}<span>conflict set: ${c.conflict.length}</span></header>
          ${c.conflict.map(x => `<div class="fire"><div class="top-l"><span class="rid">${x.rule.id}</span><span class="th">θ = ${thH(x.th)}</span></div>
            <div class="fol">${x.premises.map(lH).join(` ${AND} `)}</div>
            <div class="new ${x.head.p === 'fault' || x.head.p === 'escalate' ? 'goal-fact' : ''}">${IMP} ${lH(x.head)}</div></div>`).join('')}</div>`).join('')}
        ${shown >= fc.cycles.length ? `<div class="conc"><b>Fixpoint · ${fc.cycles.length} cycle${fc.cycles.length === 1 ? '' : 's'}</b><div class="fol" style="margin-top:6px">${goals.length ? goals.map(g => lH(g.lit)).join(', ') : 'No conclusion'}</div></div>` : ''}
      </div>
      <div class="card">
        <h4 class="eyebrow" style="margin:0 0 10px">Working memory</h4>
        <ul style="list-style:none;padding:0;margin:0;display:grid;gap:4px;font:13px var(--mono)">
          ${init.filter(w => w.how.src === 'answer' || w.lit.p === 'device' || w.lit.p === 'router').map(w => `<li><span class="dot ${w.how.src === 'answer' ? 'yes' : 'kb'}" style="display:inline-block;margin-right:8px"></span>${lH(w.lit)}</li>`).join('')}
          ${fc.negKnown.map(k => `<li><span class="dot no" style="display:inline-block;margin-right:8px"></span>${lH({ ...keyToLit(k), neg: true })}</li>`).join('')}
          ${fc.wm.filter(w => w.how.src === 'rule' && w.how.cycle <= shown).map(w => `<li><span class="dot der" style="display:inline-block;margin-right:8px"></span>${lH(w.lit)} <span class="muted" style="font-family:var(--body);font-size:11px">cycle ${w.how.cycle} · ${w.how.rule.id}</span></li>`).join('')}
        </ul>
      </div>
    </div>`;
  } else {
    if (!L.bc && !L.err) runBackward();
    const bc = L.bc, sol = bc && bc.sols[L.sel];
    const exs = ['fault(wifi, X)', 'suspect(lap, W)', 'fault(S, X), severity(X, Sev)', 'fault(S, X), escalate(X)', 'router_ok(R)'];
    body = `
    <div class="row" style="margin-bottom:8px;align-items:end">
      <div style="flex:1 1 280px;min-width:0"><label class="eyebrow lbl" for="bq">Query</label><input id="bq" class="mono" type="text" value="${esc(L.query)}" spellcheck="false"></div>
      <button class="btn primary" data-act="bc-run">Prove</button>
    </div>
    <div class="row" style="gap:6px;margin-bottom:16px">${exs.map(q => `<button class="chip" data-act="bc-ex" data-q="${esc(q)}"><code>${esc(q)}</code></button>`).join('')}</div>
    ${L.err ? `<p class="msg err">${esc(L.err)}</p>` : `
    <div class="lab-grid">
      <div class="stack">
        <div><h3 style="margin-top:0">${bc.sols.length ? `${bc.sols.length} solution${bc.sols.length > 1 ? 's' : ''}` : 'No solutions'}</h3>
          ${bc.sols.length ? `<div class="sols">${bc.sols.map((s, i) => `<button class="sol" data-act="bc-sel" data-i="${i}" aria-pressed="${i === L.sel}"><span>${s.binding.length ? s.binding.map(([v, t]) => `${vH(v)} = ${tH(t)}`).join(', ') : 'true'}</span><small>cf ${s.cf.toFixed(2)}</small></button>`).join('')}</div>` : '<p class="muted">Not provable.</p>'}</div>
        ${sol ? `<div><h3>Proof tree</h3><div class="scroll card" style="padding:14px"><ul class="tree">${sol.nodes.map(treeH).join('')}</ul></div></div>` : ''}
      </div>
      <div><h3 style="margin-top:0">Trace${bc.trace.length >= 1500 ? ' (truncated)' : ''}</h3>
        <div class="trace">${bc.trace.map(t => `<div class="${t.k}-l">${'<span class="ind">│ </span>'.repeat(t.d)}${t.k === 'goal' ? '?- ' : t.k === 'ok' ? '✓ ' : t.k === 'fail' ? '✗ ' : t.k === 'unk' ? '? ' : '↳ '}${t.html}</div>`).join('')}</div>
      </div>
    </div>`}`;
  }
  $('#p-lab').innerHTML = `
  <div class="head"><div><h1>Inference lab</h1></div></div>
  <div class="toolbar">
    <div style="flex:1 1 280px">${scenSelect('labscen', L.scenario)}</div>
    <div class="seg" role="group" aria-label="Reasoning mode"><button data-act="mode" data-m="forward" aria-pressed="${L.mode === 'forward'}">Forward</button><button data-act="mode" data-m="backward" aria-pressed="${L.mode === 'backward'}">Backward</button></div>
  </div>
  <div class="answers-row">${answerChips(ans)}</div>
  ${body}`;
}

/* =====================================================================
   UNIFICATION
   ===================================================================== */
const UNI_PRESETS = [
  ['fault(wifi, X)', 'fault(S, adapter_driver)', 'Goal vs rule head'],
  ['associated(lap, R)', 'associated(D, rtr)', 'Variables on both sides'],
  ['knows(john, X)', 'knows(Y, mother(Y))', 'Through a function'],
  ['q(X, g(X, Z))', 'q(f(Y), g(f(a), Y))', 'Chained bindings'],
  ['p(X, X)', 'p(Y, f(Y))', 'Occurs check'],
  ['router_ok(rtr)', 'router_ok(lap)', 'Constant clash'],
];
function renderUnify() {
  const U = S.uni; let out;
  try {
    const a = parseTermStr(U.a), b = parseTermStr(U.b), tr = [];
    const th = unify(a, b, {}, tr);
    const vars = termVars(a, termVars(b, []));
    out = `
    <div class="banner ${th ? 'ok' : 'bad'}">
      <span class="eyebrow">${th ? 'Unifiable' : 'Not unifiable'}</span>
      ${th ? `<b>MGU</b><div class="mgu">θ = ${thH(th, new Set(vars))}</div><div class="fol">Result: ${tH(subst(th, a))}</div>`
        : `<b>${esc(tr[tr.length - 1].msg)}</b>`}
    </div>
    <h3>Steps</h3>
    <div class="tablebox" style="max-height:none"><table class="steps-t"><thead><tr><th>#</th><th>Pair</th><th>Action</th><th>θ</th></tr></thead><tbody>
      ${tr.map((s, i) => `<tr><td>${i + 1}</td><td class="fol">${tH(s.a)} <span class="op">≐</span> ${tH(s.b)}</td><td><span class="act ${s.kind}">${s.kind === 'dec' ? 'decompose' : s.kind}</span> <span style="font-size:13px">${esc(s.msg)}</span></td><td class="fol">${s.th ? thH(s.th) : '<span class="neg">fail</span>'}</td></tr>`).join('')}
    </tbody></table></div>`;
  } catch (e) { out = `<p class="msg err">${esc(e.message)}</p>`; }
  $('#p-unify').innerHTML = `
  <div class="head"><div><h1>Unification</h1></div></div>
  <div class="card">
    <div class="uni-in">
      <div><label class="eyebrow lbl" for="ua">Term 1</label><input id="ua" class="mono" type="text" value="${esc(U.a)}" spellcheck="false"></div>
      <span class="eq">≐</span>
      <div><label class="eyebrow lbl" for="ub">Term 2</label><input id="ub" class="mono" type="text" value="${esc(U.b)}" spellcheck="false"></div>
      <button class="btn primary" data-act="uni-run">Unify</button>
    </div>
    <div class="row" style="gap:6px;margin-top:14px">${UNI_PRESETS.map((p, i) => `<button class="chip" data-act="uni-ex" data-i="${i}" aria-pressed="${U.a === p[0] && U.b === p[1]}">${esc(p[2])}</button>`).join('')}</div>
  </div>
  <div class="stack" style="margin-top:20px">${out}</div>`;
}

/* =====================================================================
   RESOLUTION
   ===================================================================== */
function runRes() {
  const R = S.res;
  try { R.out = refute(R.query, scenAnswers(R.scenario)); R.err = null; } catch (e) { R.out = null; R.err = e.message; }
}
function renderRes() {
  const R = S.res; if (!R.out && !R.err) runRes();
  const o = R.out;
  let body = '';
  if (R.err) body = `<p class="msg err">${esc(R.err)}</p>`;
  else {
    const kp = `<div class="kpis"><div><b>${o.base.length + 1}</b><span>clauses</span></div><div><b>${o.gen.toLocaleString()}</b><span>resolvents</span></div><div><b>${o.picks.toLocaleString()}</b><span>expanded</span></div>${o.ok ? `<div><b>${proofLedger(o.final).order.filter(c => c.kind === 'derived').length}</b><span>proof steps</span></div>` : ''}</div>`;
    if (o.ok) {
      const { order, idx } = proofLedger(o.final);
      const ansL = o.final.lits[0];
      const bindings = o.qv.map((v, i) => `${vH(v)} = ${tH(ansL.a[i])}`).join(', ');
      body = `
      <div class="banner ok"><span class="eyebrow">Refutation found</span><b>${o.qv.length ? 'Answer: ' : 'Proved: '}<span class="fol" style="font-weight:500">${o.qv.length ? bindings : o.goals.map(lH).join(` ${AND} `)}</span></b></div>
      ${kp}
      <h3>Proof</h3>
      <div class="ledger">${order.map(c => {
        const n = idx.get(c); const fin = c === o.final;
        if (c.kind === 'input') return `<div class="lg input"><span class="n">${n}</span><div class="fol">${clauseH(c.lits)}</div><div class="src">given · <b>${esc(c.src)}</b></div></div>`;
        const [p1, p2] = c.parents; const shown = new Set([...varsOf(p1.lits), ...varsOf(c.dRen)]);
        return `<div class="lg ${fin ? 'final' : ''}"><span class="n">${n}</span><div class="fol">${clauseH(c.lits)}<span class="th">θ = ${thH(c.th, shown)} · resolved ${lH(c.on[0])} with ${lH(c.on[1])}</span></div><div class="src">resolve <b>${idx.get(p1)}</b> + <b>${idx.get(p2)}</b>${fin ? '<br>only Ans remains' : ''}</div></div>`;
      }).join('')}</div>`;
    } else {
      body = `<div class="banner bad"><span class="eyebrow">No refutation</span><b>${o.exhausted ? 'Goal does not follow' : 'Search limit reached'}</b></div>${kp}`;
    }
  }
  const clauses = o ? [o.goalC, ...o.base] : [];
  $('#p-res').innerHTML = `
  <div class="head"><div><h1>Resolution</h1></div></div>
  <div class="toolbar">
    <div style="flex:1 1 260px">${scenSelect('resscen', R.scenario)}</div>
    <div style="flex:2 1 300px"><label class="eyebrow lbl" for="rq">Goal</label><input id="rq" class="mono" type="text" value="${esc(R.query)}" spellcheck="false"></div>
    <button class="btn primary" data-act="res-run">Prove</button>
  </div>
  <div class="answers-row">${answerChips(scenAnswers(R.scenario))}</div>
  <div class="stack">${body}
  ${clauses.length ? `<details><summary>Clauses (${clauses.length})</summary><div class="box" style="margin-top:10px">${clauses.map((c, i) => `<div><span class="o">${i === 0 ? 'negated goal' : esc(c.src)}</span><span class="fol">${clauseH(c.lits)}</span></div>`).join('')}</div></details>` : ''}
  </div>`;
}

/* =====================================================================
   ROUTING & EVENTS
   ===================================================================== */
const RENDER = { diagnose: renderDiagnose, kb: renderKB, lab: renderLab, unify: renderUnify, res: renderRes };
function show(tab) {
  S.tab = tab;
  document.querySelectorAll('.tab').forEach(b => b.setAttribute('aria-selected', b.dataset.tab === tab));
  document.querySelectorAll('.panel').forEach(p => p.hidden = p.id !== 'p-' + tab);
  RENDER[tab]();
  try { localStorage.setItem('faultline.tab', tab); } catch (e) { }
}

document.addEventListener('click', ev => {
  const t = ev.target.closest('[data-act],[data-tab]'); if (!t) return;
  if (t.dataset.tab) { show(t.dataset.tab); window.scrollTo(0, 0); return; }
  const a = t.dataset.act;
  switch (a) {
    case 'analyze': {
      S.describe = $('#desc').value;
      const s = classify(S.describe);
      if (!s) { S.intakeMsg = 'No symptom matched those words. Choose one of the symptoms below.'; renderDiagnose(); }
      else { S.intakeMsg = null; startSymptom(s.id); }
      break;
    }
    case 'pick': S.describe = ($('#desc') || {}).value || S.describe; startSymptom(t.dataset.sym); break;
    case 'answer': answer(t.dataset.v === 'yes' ? true : t.dataset.v === 'no' ? false : 'unknown'); break;
    case 'change': changeAnswer(+t.dataset.i); break;
    case 'restart': S.sym = null; S.answers = {}; S.asked = []; S.result = null; S.pending = null; renderDiagnose(); break;
    case 'to-lab': S.lab.scenario = 'session'; S.lab.query = scenGoal('session'); S.lab.bc = null; S.lab.fcShown = 0; S.lab.mode = 'forward'; show('lab'); window.scrollTo(0, 0); break;
    case 'to-res': S.res.scenario = 'session'; S.res.query = scenGoal('session'); S.res.out = null; show('res'); window.scrollTo(0, 0); break;
    case 'kbf': S.kbFilter = t.dataset.d; renderKB(); break;
    case 'kbex': S.kbDraft = 'c1 [0.8]: device(D), wifi_on(D), vpn_active(D) => fault(wifi, vpn_conflict).\nvpn_active(lap).'; S.kbMsg = null; renderKB(); break;
    case 'kbadd': {
      S.kbDraft = $('#kbin').value;
      try {
        const added = addCustom(S.kbDraft); saveCustom(); S.kbDraft = '';
        S.kbMsg = { ok: true, html: 'Added ' + added.map(x => x.head ? `rule <code>${esc(x.id)}</code>` : `fact <code>${esc(atomKey(x))}</code>`).join(', ') };
        S.lab.bc = null; S.res.out = null;
      } catch (e) { S.kbMsg = { ok: false, html: esc(e.message) }; }
      renderKB(); break;
    }
    case 'delrule': KB.rules = KB.rules.filter(r => !(r.custom && r.id === t.dataset.id)); saveCustom(); S.kbMsg = null; S.lab.bc = null; S.res.out = null; renderKB(); break;
    case 'delfact': KB.facts = KB.facts.filter(f => !(f.custom && atomKey(f) === t.dataset.k)); saveCustom(); S.kbMsg = null; S.lab.bc = null; S.res.out = null; renderKB(); break;
    case 'mode': S.lab.mode = t.dataset.m; renderLab(); break;
    case 'fc-next': S.lab.fcShown = (S.lab.fcShown === null ? 0 : S.lab.fcShown) + 1; renderLab(); break;
    case 'fc-all': S.lab.fcShown = null; renderLab(); break;
    case 'fc-reset': S.lab.fcShown = 0; renderLab(); break;
    case 'bc-run': S.lab.query = $('#bq').value; runBackward(); renderLab(); break;
    case 'bc-ex': S.lab.query = t.dataset.q; runBackward(); renderLab(); break;
    case 'bc-sel': S.lab.sel = +t.dataset.i; renderLab(); break;
    case 'uni-run': S.uni.a = $('#ua').value; S.uni.b = $('#ub').value; renderUnify(); break;
    case 'uni-ex': { const p = UNI_PRESETS[+t.dataset.i]; S.uni.a = p[0]; S.uni.b = p[1]; renderUnify(); break; }
    case 'res-run': S.res.query = $('#rq').value; runRes(); renderRes(); break;
  }
});
document.addEventListener('change', ev => {
  if (ev.target.id === 'labscen') { S.lab.scenario = ev.target.value; S.lab.query = scenGoal(S.lab.scenario); S.lab.bc = null; S.lab.fcShown = null; renderLab(); }
  if (ev.target.id === 'resscen') { S.res.scenario = ev.target.value; S.res.query = scenGoal(S.res.scenario); S.res.out = null; renderRes(); }
});
document.addEventListener('keydown', ev => {
  const id = ev.target.id;
  if (ev.key === 'Enter' && !ev.shiftKey) {
    const map = { bq: 'bc-run', ua: 'uni-run', ub: 'uni-run', rq: 'res-run', desc: 'analyze' };
    if (map[id]) { ev.preventDefault(); document.querySelector(`[data-act="${map[id]}"]`).click(); return; }
  }
  if (S.tab === 'diagnose' && S.pending && !/INPUT|TEXTAREA|SELECT/.test(ev.target.tagName) && !ev.metaKey && !ev.ctrlKey) {
    const k = ev.key.toLowerCase();
    if (k === 'y') answer(true); else if (k === 'n') answer(false); else if (k === 'u') answer('unknown');
  }
});

/* ---------- boot ---------- */
buildKB(loadCustom());
let startTab = 'diagnose';
const h = (location.hash || '').slice(1);
if (RENDER[h]) startTab = h; else { try { const s = localStorage.getItem('faultline.tab'); if (RENDER[s]) startTab = s; } catch (e) { } }
show(startTab);
