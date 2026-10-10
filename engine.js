"use strict";
/* =====================================================================
   FAULTLINE ENGINE — first-order logic for troubleshooting
   Terms · Parser · Unification (MGU + occurs check) · Backward chaining
   (SLD, goal-driven questioning, certainty factors) · Forward chaining
   (data-driven, conflict sets) · Resolution refutation (CNF, set of
   support, unit preference, answer extraction)
   ===================================================================== */

/* ---------- Terms & literals ---------- */
const V = n => ({ t: 'v', n });
const C = n => ({ t: 'c', n });
const F = (n, a) => ({ t: 'f', n, a });

function walk(t, th) { while (t.t === 'v' && th[t.n] !== undefined) t = th[t.n]; return t; }
function subst(th, t) { t = walk(t, th); return t.t === 'f' ? F(t.n, t.a.map(x => subst(th, x))) : t; }
function substLit(th, l) { return { p: l.p, a: l.a.map(x => subst(th, x)), neg: l.neg }; }
function occurs(v, t, th) { t = walk(t, th); if (t.t === 'v') return t.n === v; if (t.t === 'f') return t.a.some(x => occurs(v, x, th)); return false; }
function termStr(t) { return t.t === 'f' ? `${t.n}(${t.a.map(termStr).join(', ')})` : t.n; }
function litStr(l) { return (l.neg ? '¬' : '') + l.p + (l.a.length ? `(${l.a.map(termStr).join(', ')})` : ''); }
function atomKey(l) { return l.p + (l.a.length ? `(${l.a.map(termStr).join(',')})` : ''); }
function termVars(t, acc) { if (t.t === 'v') { if (!acc.includes(t.n)) acc.push(t.n); } else if (t.t === 'f') t.a.forEach(x => termVars(x, acc)); return acc; }
function varsOf(lits) { const acc = []; lits.forEach(l => l.a.forEach(t => termVars(t, acc))); return acc; }
function isGround(l) { return varsOf([l]).length === 0; }

/* ---------- Unification (Robinson / AIMA, with optional trace) ---------- */
function unify(x, y, th, tr) {
  if (th === null) return null;
  const a = walk(x, th), b = walk(y, th);
  const rec = (kind, msg, out) => { if (tr) tr.push({ a, b, kind, msg, th: out }); return out; };
  if (a.t === 'v' && b.t === 'v' && a.n === b.n) return rec('same', 'Same variable, already equal', th);
  if (a.t === 'v') return bindVar(a, b, th, rec);
  if (b.t === 'v') return bindVar(b, a, th, rec);
  if (a.t === 'c' && b.t === 'c') return a.n === b.n ? rec('same', 'Identical constants', th) : rec('fail', `Constant clash: ${a.n} ≠ ${b.n}`, null);
  if (a.t === 'f' && b.t === 'f') {
    if (a.n !== b.n || a.a.length !== b.a.length) return rec('fail', `Functor clash: ${a.n}/${a.a.length} vs ${b.n}/${b.a.length}`, null);
    rec('dec', `Same functor ${a.n}/${a.a.length}: unify the arguments pairwise`, th);
    for (let i = 0; i < a.a.length; i++) { th = unify(a.a[i], b.a[i], th, tr); if (!th) return null; }
    return th;
  }
  return rec('fail', 'A constant cannot match a compound term', null);
}
function bindVar(v, t, th, rec) {
  if (occurs(v.n, t, th)) return rec('fail', `Occurs check: ${v.n} occurs inside ${termStr(subst(th, t))}`, null);
  return rec('bind', `Bind ${v.n} ↦ ${termStr(t)}`, { ...th, [v.n]: t });
}
function unifyLits(a, b, th) {
  if (a.p !== b.p || a.a.length !== b.a.length) return null;
  for (let i = 0; i < a.a.length; i++) { th = unify(a.a[i], b.a[i], th); if (!th) return null; }
  return th;
}

/* ---------- Parser ---------- */
const TOK = /\s+|%[^\n]*|=>|⇒|->|:-|←|∧|&|¬|~|\d+(?:\.\d+)?|[A-Za-z_][A-Za-z0-9_]*|[(),.\[\]:]/y;
function tokenize(src) {
  const out = []; let i = 0;
  while (i < src.length) {
    TOK.lastIndex = i; const m = TOK.exec(src);
    if (!m) throw new Error(`Unexpected character “${src[i]}” (line ${lineOf(src, i)})`);
    i = TOK.lastIndex;
    if (/^\s/.test(m[0]) || m[0][0] === '%') continue;
    out.push({ s: m[0], pos: m.index });
  }
  return out;
}
function lineOf(src, pos) { return src.slice(0, pos).split('\n').length; }

function mkParser(src) {
  const toks = tokenize(src); let k = 0;
  const peek = (o = 0) => toks[k + o] ? toks[k + o].s : undefined;
  const next = () => toks[k++];
  const fail = msg => { const t = toks[Math.min(k, toks.length - 1)]; throw new Error(msg + (t && src.includes('\n') ? ` (line ${lineOf(src, t.pos)})` : '')); };
  const expect = s => { if (peek() !== s) fail(`Expected “${s}”` + (peek() ? ` but found “${peek()}”` : ' at the end')); return next(); };
  function args() { const a = [term()]; while (peek() === ',') { next(); a.push(term()); } expect(')'); return a; }
  function term() {
    const t = next(); if (!t) fail('Expected a term');
    const s = t.s;
    if (/^\d/.test(s)) return C(s);
    if (!/^[A-Za-z_]/.test(s)) fail(`Unexpected “${s}”`);
    if (peek() === '(') { next(); if (/^[A-Z_]/.test(s)) fail(`Function name “${s}” must start with a lowercase letter`); return F(s, args()); }
    return /^[A-Z_]/.test(s) ? V(s) : C(s);
  }
  function atom() {
    const t = next();
    if (!t || !/^[a-z]/.test(t.s)) fail(`Expected a predicate name starting lowercase` + (t ? `, found “${t.s}”` : ''));
    let a = []; if (peek() === '(') { next(); a = args(); }
    return { p: t.s, a, neg: false };
  }
  function isNeg() { const s = peek(), n = peek(1); return s === '¬' || s === '~' || (s === 'not' && n !== undefined && /^[a-z]/.test(n)); }
  function literal() { let neg = false; while (isNeg()) { next(); neg = !neg; } const l = atom(); l.neg = neg; return l; }
  function conj() { const ls = [literal()]; while (peek() === ',' || peek() === '∧' || peek() === '&') { next(); ls.push(literal()); } return ls; }
  function checkRule(r) {
    if (r.head.neg) fail('A rule must conclude a positive literal (Horn head)');
    const pos = varsOf(r.body.filter(l => !l.neg));
    const hv = varsOf([r.head]).filter(v => !pos.includes(v));
    if (hv.length) fail(`Variable ${hv[0]} in the conclusion must also appear in a positive premise`);
    const nv = varsOf(r.body.filter(l => l.neg)).filter(v => !pos.includes(v));
    if (nv.length) fail(`Unsafe negation: ${nv[0]} must be bound by a positive premise first`);
    return r;
  }
  function statement() {
    let id = null, cf = 1;
    if (/^[A-Za-z_]/.test(peek() || '') && (peek(1) === ':' || peek(1) === '[')) {
      id = next().s;
      if (peek() === '[') { next(); const n = next(); if (!n || isNaN(+n.s)) fail('Expected a certainty factor between 0 and 1'); cf = +n.s; if (cf < 0 || cf > 1) fail('Certainty must be between 0 and 1'); expect(']'); }
      expect(':');
    }
    const first = conj();
    if (['=>', '⇒', '->'].includes(peek())) { next(); const head = literal(); expect('.'); return { kind: 'rule', rule: checkRule({ id, cf, body: first, head }) }; }
    if (peek() === ':-' || peek() === '←') {
      if (first.length !== 1) fail('Left of “:-” must be a single literal');
      next(); const body = conj(); expect('.');
      return { kind: 'rule', rule: checkRule({ id, cf, body, head: first[0] }) };
    }
    expect('.');
    if (first.length !== 1) fail('A fact is a single literal. Use “=>” to write a rule');
    if (first[0].neg) fail('Facts must be positive literals');
    if (!isGround(first[0])) fail('Facts must be ground (no variables)');
    return { kind: 'fact', lit: first[0] };
  }
  return { term, conj, statement, peek, fail, done: () => k >= toks.length };
}
function parseProgram(src) {
  const P = mkParser(src); const rules = [], facts = [];
  while (!P.done()) { const st = P.statement(); if (st.kind === 'rule') rules.push(st.rule); else facts.push(st.lit); }
  return { rules, facts };
}
function parseQuery(src) {
  const P = mkParser(src.trim().replace(/\.\s*$/, ''));
  const ls = P.conj(); if (!P.done()) P.fail(`Unexpected “${P.peek()}”`);
  return ls;
}
function parseTermStr(src) {
  const P = mkParser(src.trim()); const t = P.term(); if (!P.done()) P.fail(`Unexpected “${P.peek()}”`); return t;
}

/* ---------- Knowledge base source ---------- */
const KB_SRC = `% Entities in the world being diagnosed
device(lap).
router(rtr).

% Wi-Fi: radio and router state
w1 [1.0]:  device(D), not wifi_on(D) => radio_blocked(D).
w2 [1.0]:  device(D), airplane_mode(D) => radio_blocked(D).
w3 [1.0]:  router(R), others_connect(R) => router_ok(R).
w4 [0.9]:  router(R), not others_connect(R), not router_lights_ok(R) => router_down(R).
w5 [0.85]: router(R), not others_connect(R), router_lights_ok(R) => upstream_down(R).
% The brief's rule: enabled + router working + not connected => check the adapter
w6 [0.9]:  device(D), router(R), wifi_on(D), router_ok(R), not associated(D, R) => suspect(D, adapter).
w7 [1.0]:  device(D), router(R), router_ok(R), associated(D, R) => linked(D, R).
% Wi-Fi: faults
w8 [0.97]:  radio_blocked(D) => fault(wifi, radio_disabled).
w9 [0.92]:  router_down(R) => fault(wifi, router_failure).
w10 [0.85]: upstream_down(R) => fault(wifi, isp_outage).
w11 [0.88]: suspect(D, adapter), not adapter_healthy(D) => fault(wifi, adapter_driver).
w12 [0.8]:  suspect(D, adapter), router(R), not sees_ssid(D, R) => fault(wifi, band_or_range).
w13 [0.9]:  suspect(D, adapter), router(R), sees_ssid(D, R), password_rejected(D) => fault(wifi, wrong_credentials).
w14 [0.7]:  suspect(D, adapter), router(R), sees_ssid(D, R), not password_rejected(D) => fault(wifi, stale_profile).
w15 [0.85]: linked(D, R), self_assigned_ip(D) => fault(wifi, dhcp_failure).
w16 [0.8]:  linked(D, R), not self_assigned_ip(D), dns_only_fail(D) => fault(wifi, dns_failure).

% Display: screen stays black
d1 [1.0]:  device(D), power_led_on(D) => powered(D).
d2 [0.9]:  device(D), not power_led_on(D), not charger_led(D) => fault(display, no_power_input).
d3 [0.75]: device(D), not power_led_on(D), charger_led(D) => fault(display, board_or_battery).
d4 [0.85]: powered(D), beep_or_blink(D) => fault(display, memory_post).
d5 [0.88]: powered(D), not beep_or_blink(D), backlight_faint(D) => fault(display, backlight).
d6 [0.8]:  powered(D), not beep_or_blink(D), not backlight_faint(D), external_works(D) => fault(display, panel_or_cable).
d7 [0.75]: powered(D), not beep_or_blink(D), not external_works(D) => fault(display, gpu).

% Power: battery not charging
p1 [1.0]:  device(D), charger_led(D) => adapter_live(D).
p2 [0.95]: device(D), battery_swollen(D) => fault(power, swollen_battery).
p3 [0.9]:  device(D), not charger_led(D), not outlet_works(D) => fault(power, dead_outlet).
p4 [0.85]: device(D), not charger_led(D), outlet_works(D) => fault(power, faulty_charger).
p5 [0.9]:  adapter_live(D), stuck_percent(D) => fault(power, charge_limit).
p6 [0.8]:  adapter_live(D), not stuck_percent(D), not charging_icon(D), other_charger(D) => fault(power, underpowered_charger).
p7 [0.8]:  adapter_live(D), not stuck_percent(D), not charging_icon(D), not other_charger(D) => fault(power, dc_jack).
p8 [0.75]: adapter_live(D), not stuck_percent(D), charging_icon(D), fast_drain(D) => fault(power, worn_battery).

% Audio: no sound
a1 [0.97]: device(D), muted(D) => fault(audio, muted).
a2 [1.0]:  device(D), not muted(D), all_apps_silent(D), correct_output(D) => system_silent(D).
a3 [0.85]: device(D), not muted(D), not all_apps_silent(D) => fault(audio, app_setting).
a4 [0.9]:  device(D), not muted(D), all_apps_silent(D), not correct_output(D) => fault(audio, wrong_output).
a5 [0.88]: system_silent(D), driver_warning(D) => fault(audio, driver).
a6 [0.8]:  system_silent(D), not driver_warning(D), headphones_work(D) => fault(audio, speakers).
a7 [0.75]: system_silent(D), not driver_warning(D), not headphones_work(D) => fault(audio, audio_codec).

% Performance: running slowly
s1 [1.0]:  device(D), not high_cpu(D), not hot_fan_loud(D) => cpu_ok(D).
s2 [0.85]: device(D), high_cpu(D), slow_since_update(D) => fault(perf, post_update_tasks).
s3 [0.8]:  device(D), high_cpu(D), not slow_since_update(D) => fault(perf, runaway_process).
s4 [0.85]: device(D), not high_cpu(D), hot_fan_loud(D) => fault(perf, thermal_throttling).
s5 [0.8]:  cpu_ok(D), ram_high(D) => fault(perf, memory_pressure).
s6 [0.85]: cpu_ok(D), not ram_high(D), disk_full(D) => fault(perf, disk_full).
s7 [0.7]:  cpu_ok(D), not ram_high(D), not disk_full(D), hdd(D) => fault(perf, hdd_bottleneck).

% General: escalation policy
g1 [1.0]: fault(S, F), severity(F, high) => escalate(F).
g2 [1.0]: fault(S, F), needs_service(F) => escalate(F).

% Severity of each fault
severity(radio_disabled, low).  severity(router_failure, medium).  severity(isp_outage, medium).
severity(adapter_driver, medium). severity(band_or_range, low).  severity(wrong_credentials, low).
severity(stale_profile, low).   severity(dhcp_failure, medium).  severity(dns_failure, low).
severity(no_power_input, medium). severity(board_or_battery, high). severity(memory_post, medium).
severity(backlight, medium).    severity(panel_or_cable, medium). severity(gpu, high).
severity(swollen_battery, high). severity(dead_outlet, low).     severity(faulty_charger, medium).
severity(charge_limit, low).    severity(underpowered_charger, low). severity(dc_jack, high).
severity(worn_battery, medium). severity(muted, low).            severity(app_setting, low).
severity(wrong_output, low).    severity(driver, medium).        severity(speakers, medium).
severity(audio_codec, high).    severity(post_update_tasks, low). severity(runaway_process, medium).
severity(thermal_throttling, medium). severity(memory_pressure, medium). severity(disk_full, low).
severity(hdd_bottleneck, low).

% Faults that need a technician
needs_service(board_or_battery). needs_service(gpu). needs_service(panel_or_cable).
needs_service(dc_jack). needs_service(audio_codec).
`;

/* ---------- Askable predicates: knowledge acquired from the user ---------- */
const ASK = {
  wifi_on: { q: 'Is Wi‑Fi turned on?', h: 'The Wi‑Fi icon in the taskbar or menu bar is not crossed out or greyed.' },
  airplane_mode: { q: 'Is Airplane mode switched on?', h: 'Look for the plane icon in quick settings or the notification area.' },
  others_connect: { q: 'Can other devices connect to the same Wi‑Fi?', h: 'Try a phone or tablet on the same network name.' },
  router_lights_ok: { q: "Are the router's power and internet lights steady?", h: 'Answer No if a light is off, red, or blinking orange.' },
  associated: { q: 'Is your laptop connected to the router?', h: 'Your network name shows “Connected” under it in the Wi‑Fi list.' },
  adapter_healthy: { q: 'Is the wireless adapter listed in Device Manager without a warning sign?', h: 'Windows: Device Manager → Network adapters. macOS: System Information → Network → Wi‑Fi.' },
  sees_ssid: { q: "Does your network's name appear in the list of available networks?", h: 'Refresh the list once and wait a few seconds.' },
  password_rejected: { q: 'When you try to join, does it report a wrong password or authentication failure?', h: 'Messages like “Can’t connect to this network” right after entering the key count as Yes.' },
  self_assigned_ip: { q: 'Does your IP address start with 169.254?', h: 'Windows: run ipconfig. macOS: Wi‑Fi → Details → TCP/IP.' },
  dns_only_fail: { q: 'Does “ping 1.1.1.1” work while websites still fail to load?', h: 'This separates a DNS fault from a full loss of connectivity.' },
  power_led_on: { q: 'When you press the power button, does a power light come on?', h: 'Many laptops light the power button itself or a small LED near the hinge.' },
  charger_led: { q: 'Is the charger plugged in with its light on?', h: 'Check the brick, the plug end, or the laptop’s charging LED.' },
  beep_or_blink: { q: 'Does the laptop beep or flash a light in a repeating pattern at startup?', h: 'Repeating patterns are hardware self-test (POST) error codes.' },
  backlight_faint: { q: 'Shine a flashlight at the screen at an angle. Can you faintly see an image?', h: 'A faint image means the panel draws but the backlight is off.' },
  external_works: { q: 'With an external monitor connected, does it show a picture?', h: 'Use HDMI or USB‑C. Press Win + P or Fn + the display key if needed.' },
  battery_swollen: { q: 'Is the case bulging, the trackpad lifted, or the battery flagged “replace soon”?', h: 'Asked first because a swollen battery is a safety risk.' },
  outlet_works: { q: 'Does another device work from the same wall outlet?', h: 'A lamp or phone charger is a quick test.' },
  stuck_percent: { q: 'Is the battery holding at a fixed level with “plugged in, not charging”?', h: 'Often exactly 60% or 80%.' },
  charging_icon: { q: 'Does the battery icon show a charging symbol when the charger is connected?', h: 'A lightning bolt or plug over the battery icon.' },
  other_charger: { q: 'Does a different charger of the correct wattage charge it?', h: 'Borrow a compatible charger with the same or higher wattage.' },
  fast_drain: { q: 'Does a full charge last less than half as long as it used to?', h: 'Compare with how long it lasted when new.' },
  muted: { q: 'Is the volume muted or set to zero?', h: 'Check the speaker icon and the Fn mute key.' },
  all_apps_silent: { q: 'Is sound missing in every app, not just one?', h: 'Try a system sound, a video in the browser, and a music app.' },
  correct_output: { q: 'In sound settings, is the output set to the device you expect?', h: 'Bluetooth headsets and monitors often take over the output.' },
  driver_warning: { q: 'Does Device Manager show a warning on the audio device, or no audio device at all?', h: 'Device Manager → Sound, video and game controllers.' },
  headphones_work: { q: 'Do wired headphones produce sound when plugged in?', h: 'This separates the speakers from the audio chip.' },
  high_cpu: { q: 'Is CPU usage above 80% while you are not doing anything?', h: 'Task Manager (Ctrl + Shift + Esc) or Activity Monitor.' },
  slow_since_update: { q: 'Did the slowness start right after an update or a new install?', h: 'Think about the last few days.' },
  hot_fan_loud: { q: 'Is the laptop hot with the fan running loudly?', h: 'Feel near the vents on the side or underneath.' },
  ram_high: { q: 'Is memory usage above 85%?', h: 'Task Manager → Performance → Memory.' },
  disk_full: { q: 'Is the system drive more than 90% full?', h: 'Settings → System → Storage, or About This Mac → Storage.' },
  hdd: { q: 'Does it use a spinning hard disk (HDD) rather than an SSD?', h: 'Task Manager → Performance → Disk shows the drive type.' },
};

/* ---------- Fault catalogue: what each conclusion means and how to fix it ---------- */
const FAULTS = {
  radio_disabled: { t: 'Wireless radio is switched off', s: "The laptop's Wi‑Fi radio is disabled, so it never tries to join a network.", steps: ['Open quick settings and turn Wi‑Fi on.', 'Turn Airplane mode off.', 'Toggle the Fn key or side switch with the antenna icon, if your laptop has one.', 'Choose your network and reconnect.'] },
  router_failure: { t: 'Router is down', s: 'No device can join and the router shows fault lights, so the router itself has stopped serving the network.', steps: ['Unplug the router for 30 seconds, then power it back on.', 'Wait two minutes for the lights to settle.', 'Check that the WAN or internet cable is seated at both ends.', 'If lights stay red, factory-reset the router or call your provider.'] },
  isp_outage: { t: 'Internet service outage', s: 'The router looks healthy but no device gets online, so the connection beyond the router is down.', steps: ['Check your provider’s outage page or support line from mobile data.', 'Restart the modem if it is separate from the router.', 'Use a phone hotspot until service returns.'] },
  adapter_driver: { t: 'Network adapter or driver fault', s: 'Wi‑Fi is on and the router works for other devices, yet this laptop cannot associate, and the adapter reports a problem.', steps: ['Device Manager → Network adapters → right-click the wireless adapter → Uninstall device, then restart.', 'Install the latest Wi‑Fi driver from the laptop maker’s support site.', 'Run “netsh winsock reset” and “netsh int ip reset” in an admin terminal, then restart.', 'If the adapter is missing entirely, check that wireless is enabled in BIOS/UEFI.'] },
  band_or_range: { t: 'Network not visible: band or range', s: 'The adapter works but cannot see your network, which points to signal range or a 2.4/5 GHz band mismatch.', steps: ['Move closer to the router and refresh the network list.', 'Enable the 2.4 GHz band on the router if it broadcasts 5 GHz only.', 'Check that the network name is not hidden.', 'Change the router’s channel to 1, 6 or 11 to avoid interference.'] },
  wrong_credentials: { t: 'Authentication failure', s: 'The laptop sees the network but the router rejects its key.', steps: ['Re-enter the password carefully; it is case-sensitive.', 'Confirm the key on the router label or admin page.', 'Set the router to WPA2/WPA3 mixed mode if the laptop is older.', 'Forget the network and join again.'] },
  stale_profile: { t: 'Corrupted saved network profile', s: 'The network is visible and the key is accepted elsewhere, but the saved profile on this laptop fails.', steps: ['Forget the network in Wi‑Fi settings.', 'Restart the laptop.', 'Join the network again and re-enter the password.'] },
  dhcp_failure: { t: 'No IP address from the router (DHCP)', s: 'The laptop joins the network but gives itself a 169.254 address because the router never assigned one.', steps: ['Run “ipconfig /release” then “ipconfig /renew”.', 'Restart the router to reset its DHCP service.', 'Check the router for MAC filtering or a full address pool.', 'As a stopgap, set a static IP in the router’s range.'] },
  dns_failure: { t: 'DNS resolution failure', s: 'The connection works by IP address, but names do not resolve to addresses.', steps: ['Run “ipconfig /flushdns”.', 'Set DNS to 1.1.1.1 and 8.8.8.8 in adapter settings.', 'Turn off any VPN or proxy and test again.'] },
  no_power_input: { t: 'No power reaching the laptop', s: 'Neither the laptop nor the charger shows power.', steps: ['Try a different wall outlet.', 'Reseat the charger at the wall, the brick and the laptop.', 'Hold the power button for 30 seconds with the charger connected, then press it normally.'] },
  board_or_battery: { t: 'Power circuit or battery failure', s: 'The charger is live but the laptop shows no sign of power, which points to the battery or the board’s power circuit.', steps: ['Unplug everything and hold power for 30 seconds to drain residual charge.', 'If the battery is removable, try starting on the charger alone.', 'Book a hardware service; the power circuit likely needs repair.'] },
  memory_post: { t: 'Startup self-test failure (often memory)', s: 'Beep or blink codes mean the hardware self-test failed before the screen came on.', steps: ['Count the pattern and look it up in your laptop’s manual.', 'Reseat the RAM modules if the panel is accessible.', 'Try one memory stick at a time to find a bad one.'] },
  backlight: { t: 'Backlight failure', s: 'The panel is drawing an image but the light behind it is off.', steps: ['Press the brightness-up keys a few times.', 'Close and reopen the lid to rule out the lid sensor.', 'Use an external monitor as a workaround; the backlight or panel needs service.'] },
  panel_or_cable: { t: 'Internal display panel or cable', s: 'The graphics output works on an external screen, so the fault is in the built-in panel or its hinge cable.', steps: ['Open the lid to different angles; flicker points to the hinge cable.', 'Keep using an external monitor for now.', 'Book a repair for the panel or display cable.'] },
  gpu: { t: 'Graphics or board failure', s: 'The laptop has power but no image reaches any screen.', steps: ['Disconnect all accessories and try again.', 'Reset the BIOS/CMOS following the maker’s instructions.', 'Book a hardware service for the graphics circuit.'] },
  swollen_battery: { t: 'Swollen battery: stop using it', s: 'A swelling lithium battery can catch fire. This outranks every other diagnosis.', steps: ['Shut down and unplug the laptop now.', 'Do not charge, press on, or puncture the battery.', 'Have the battery replaced by a service centre and recycled properly.'] },
  dead_outlet: { t: 'Dead wall outlet', s: 'The charger shows no light and other devices fail on the same outlet.', steps: ['Use another outlet.', 'Check the power strip switch and the circuit breaker.'] },
  faulty_charger: { t: 'Faulty charger', s: 'The outlet is live but the charger shows no light.', steps: ['Inspect the cable for kinks or frayed sections.', 'Replace the charger with one of the correct wattage and connector.'] },
  charge_limit: { t: 'Battery protection limit is on', s: 'The laptop deliberately stops charging at a set level to extend battery life.', steps: ['Open the maker’s utility: Lenovo Vantage, MyASUS, Dell Power Manager, or macOS Battery settings.', 'Turn off conservation or optimised charging if you need a full charge today.', 'Leave the limit on for desk use; it is good for the battery.'] },
  underpowered_charger: { t: 'Charger wattage too low', s: 'Your usual charger delivers power but not enough to charge; a stronger one works.', steps: ['Use the original charger wattage or higher.', 'For USB‑C, use a Power Delivery charger rated for your laptop.'] },
  dc_jack: { t: 'Charging port or circuit fault', s: 'The charger is live but no charger can charge the laptop.', steps: ['Inspect the port for lint or bent pins and clean gently.', 'Book a repair for the DC jack or charging circuit.'] },
  worn_battery: { t: 'Worn battery', s: 'The battery charges but holds far less than it did.', steps: ['Run “powercfg /batteryreport” and compare design vs full-charge capacity.', 'Replace the battery if it is below about 60% of design capacity.'] },
  muted: { t: 'Audio is muted', s: 'The output is muted or at zero volume.', steps: ['Unmute and raise the volume.', 'Check the Fn mute key and the per-app volume mixer.'] },
  app_setting: { t: 'One app is silent', s: 'Sound works elsewhere, so the fault is in that app’s own settings.', steps: ['Check the app’s output device and volume.', 'Unmute the browser tab if it is a website.', 'Restart the app.'] },
  wrong_output: { t: 'Wrong output device', s: 'Sound is routed to a device you are not listening to.', steps: ['Sound settings → Output → choose your speakers or headphones.', 'Disconnect unused Bluetooth audio devices.'] },
  driver: { t: 'Audio driver fault', s: 'The operating system reports a problem with the audio device.', steps: ['Device Manager → audio device → Roll back or Uninstall, then restart.', 'Install the audio driver from the laptop maker.', 'Restart the Windows Audio service.'] },
  speakers: { t: 'Internal speakers fault', s: 'Headphones work, so the audio chip is fine and the speakers or their cable have failed.', steps: ['Turn off audio enhancements and test again.', 'Use headphones or a USB speaker meanwhile.', 'Book a repair for the speakers.'] },
  audio_codec: { t: 'Audio chip failure', s: 'No output works and the driver reports no error, which points to the audio hardware.', steps: ['Use a USB audio adapter as a workaround.', 'Book a hardware service.'] },
  post_update_tasks: { t: 'Post-update background work', s: 'Updates trigger indexing and optimisation that use the CPU for a while.', steps: ['Leave the laptop plugged in and idle for one to two hours.', 'If it is still slow after a day, roll back the update.'] },
  runaway_process: { t: 'Runaway process or malware', s: 'Something is using the CPU heavily while you are idle.', steps: ['Task Manager → sort by CPU → end or uninstall the culprit.', 'Run a full antivirus scan.', 'Disable unneeded startup apps.'] },
  thermal_throttling: { t: 'Thermal throttling', s: 'The CPU is not busy but the laptop is hot, so it slows itself to cool down.', steps: ['Use it on a hard, flat surface.', 'Clean the vents with compressed air.', 'Have the thermal paste and fan serviced if it persists.'] },
  memory_pressure: { t: 'Memory pressure', s: 'RAM is nearly full, so the system swaps to disk.', steps: ['Close unused apps and browser tabs.', 'Disable startup items you do not need.', 'Consider a RAM upgrade.'] },
  disk_full: { t: 'System drive nearly full', s: 'Less than 10% free space slows updates, caching and virtual memory.', steps: ['Run Storage Sense or Disk Cleanup.', 'Uninstall unused apps and move large files off the drive.', 'Keep at least 15% free.'] },
  hdd_bottleneck: { t: 'Hard disk bottleneck', s: 'Nothing else is overloaded; the spinning hard disk is the slowest part.', steps: ['Upgrade to an SSD; it is the largest single speed-up for older laptops.'] },
};

const SYMPTOMS = [
  { id: 'wifi', t: 'Won’t connect to Wi‑Fi', d: 'No network, or connected without internet', kw: ['wifi', 'wi-fi', 'wi‑fi', 'wireless', 'internet', 'network', 'connect', 'router', 'ssid', 'online', 'dns', 'ip address'] },
  { id: 'display', t: 'Screen stays black', d: 'Nothing on the display after power on', kw: ['screen', 'display', 'black', 'blank', 'monitor', 'nothing on', 'no picture', 'boot', 'turn on', 'won\'t start', 'dead'] },
  { id: 'power', t: 'Battery not charging', d: 'Plugged in, but the charge does not rise', kw: ['charg', 'battery', 'plug', 'adapter', 'power cord', 'drain'] },
  { id: 'audio', t: 'No sound', d: 'Speakers or headphones are silent', kw: ['sound', 'audio', 'speaker', 'volume', 'mute', 'hear', 'headphone'] },
  { id: 'perf', t: 'Running very slowly', d: 'Lag, freezing, fans, long load times', kw: ['slow', 'lag', 'freez', 'hang', 'sluggish', 'performance', 'hot', 'fan', 'takes forever', 'stuck'] },
];

function classify(text) {
  const t = text.toLowerCase(); let best = null, bs = 0;
  for (const s of SYMPTOMS) { const sc = s.kw.reduce((n, k) => n + (t.includes(k) ? 1 : 0), 0); if (sc > bs) { bs = sc; best = s; } }
  return best;
}

const PRESETS = {
  'wifi-brief': { label: 'Wi‑Fi: the brief’s example', goal: 'fault(wifi, X)', answers: { 'wifi_on(lap)': true, 'airplane_mode(lap)': false, 'others_connect(rtr)': true, 'associated(lap,rtr)': false, 'adapter_healthy(lap)': false } },
  'wifi-pass': { label: 'Wi‑Fi: rejected password', goal: 'fault(wifi, X)', answers: { 'wifi_on(lap)': true, 'airplane_mode(lap)': false, 'others_connect(rtr)': true, 'associated(lap,rtr)': false, 'adapter_healthy(lap)': true, 'sees_ssid(lap,rtr)': true, 'password_rejected(lap)': true } },
  'wifi-router': { label: 'Wi‑Fi: router down', goal: 'fault(wifi, X)', answers: { 'wifi_on(lap)': true, 'airplane_mode(lap)': false, 'others_connect(rtr)': false, 'router_lights_ok(rtr)': false } },
  'display-backlight': { label: 'Display: dead backlight', goal: 'fault(display, X)', answers: { 'power_led_on(lap)': true, 'beep_or_blink(lap)': false, 'backlight_faint(lap)': true, 'external_works(lap)': true } },
  'power-limit': { label: 'Power: stuck at 80%', goal: 'fault(power, X)', answers: { 'battery_swollen(lap)': false, 'charger_led(lap)': true, 'stuck_percent(lap)': true } },
  'audio-codec': { label: 'Audio: dead audio chip', goal: 'fault(S, X), escalate(X)', answers: { 'muted(lap)': false, 'all_apps_silent(lap)': true, 'correct_output(lap)': true, 'driver_warning(lap)': false, 'headphones_work(lap)': false } },
};

/* ---------- Knowledge base assembly ---------- */
const KB = { rules: [], facts: [] };
function buildKB(customSrcs) {
  const base = parseProgram(KB_SRC);
  KB.rules = base.rules.map(r => ({ ...r, custom: false }));
  KB.facts = base.facts.slice();
  const bad = [];
  (customSrcs || []).forEach(src => {
    try { addCustom(src); } catch (e) { bad.push(src); }
  });
  return bad;
}
function addCustom(src) {
  const prog = parseProgram(src);
  const added = [];
  prog.rules.forEach(r => {
    if (!r.id) { let n = 1; while (KB.rules.some(x => x.id === 'c' + n)) n++; r.id = 'c' + n; }
    if (KB.rules.some(x => x.id === r.id)) throw new Error(`Rule id “${r.id}” is already used`);
    r.custom = true; r.src = `${r.id} [${r.cf}]: ${r.body.map(litStr).join(', ').replace(/¬/g, 'not ')} => ${litStr(r.head)}.`;
    KB.rules.push(r); added.push(r);
  });
  prog.facts.forEach(f => {
    if (KB.facts.some(x => atomKey(x) === atomKey(f))) throw new Error(`Fact ${litStr(f)} is already in the knowledge base`);
    f.custom = true; f.src = atomKey(f) + '.'; KB.facts.push(f); added.push(f);
  });
  if (!added.length) throw new Error('Nothing to add');
  return added;
}

/* ---------- Backward chaining (SLD resolution with question asking) ---------- */
class AskNeeded { constructor(lit, chain, th) { this.lit = lit; this.chain = chain; this.th = th; } }
let GEN = 0;
function renTerm(t, m, s) { if (t.t === 'v') return m[t.n] || (m[t.n] = V(t.n + '_' + s)); if (t.t === 'f') return F(t.n, t.a.map(x => renTerm(x, m, s))); return t; }
function renameRule(r) { const s = ++GEN, m = {}; const rl = l => ({ p: l.p, a: l.a.map(x => renTerm(x, m, s)), neg: l.neg }); return { head: rl(r.head), body: r.body.map(rl) }; }

const keyCache = new Map();
function keyToLit(k) { if (!keyCache.has(k)) keyCache.set(k, parseQuery(k)[0]); return keyCache.get(k); }

function makeProver(answers, opts = {}) {
  const trace = opts.trace, MAXD = 40, MAXT = 1500;
  const T = (d, k, html) => { if (trace && trace.length < MAXT) trace.push({ d, k, html }); };
  const H = opts.html || (l => litStr(l));

  function* prove(goal, th, d, chain) {
    if (d > MAXD) { T(d, 'fail', 'depth limit reached'); return; }
    const g = substLit(th, goal);
    T(d, 'goal', H(g));
    let any = false;
    if (g.neg) {
      const pos = { ...g, neg: false };
      if (!isGround(pos)) { T(d, 'fail', 'cannot test a non-ground negation'); return; }
      if (ASK[pos.p]) {
        const v = answers[atomKey(pos)];
        if (v === undefined) { if (opts.ask) throw new AskNeeded(pos, chain, th); T(d, 'unk', `${H(pos)} not answered`); return; }
        if (v === false) { T(d, 'ok', `answered no, so ${H(g)} holds`); yield { th, node: { lit: g, kind: 'no', cf: 1 } }; }
        else T(d, 'fail', v === 'unknown' ? `${H(pos)} unknown` : `answered yes, so ${H(g)} fails`);
        return;
      }
      for (const _ of prove(pos, th, d + 1, chain)) { T(d, 'fail', `${H(pos)} is provable, so the negation fails`); return; }
      T(d, 'ok', `${H(pos)} not provable (negation as failure)`);
      yield { th, node: { lit: g, kind: 'naf', cf: 1 } };
      return;
    }
    if (ASK[g.p]) {
      if (isGround(g)) {
        const v = answers[atomKey(g)];
        if (v === undefined) { if (opts.ask) throw new AskNeeded(g, chain, th); T(d, 'unk', `${H(g)} not answered`); return; }
        if (v === true) { T(d, 'ok', 'answered yes'); yield { th, node: { lit: g, kind: 'yes', cf: 1 } }; }
        else T(d, 'fail', v === false ? 'answered no' : 'answer unknown');
        return;
      }
      for (const [k, v] of Object.entries(answers)) {
        if (v !== true) continue; const th2 = unifyLits(g, keyToLit(k), th);
        if (th2) { any = true; T(d, 'ok', `matches answer ${H(keyToLit(k))}`); yield { th: th2, node: { lit: substLit(th2, g), kind: 'yes', cf: 1 } }; }
      }
      if (!any) T(d, 'fail', 'no matching answer');
      return;
    }
    for (const f of KB.facts) {
      const th2 = unifyLits(g, f, th);
      if (th2) { any = true; T(d, 'ok', `fact ${H(f)}`); yield { th: th2, node: { lit: substLit(th2, g), kind: 'fact', cf: 1 } }; }
    }
    for (const r of KB.rules) {
      if (r.head.p !== g.p || r.head.a.length !== g.a.length) continue;
      const rr = renameRule(r);
      const th2 = unifyLits(rr.head, g, th);
      if (!th2) continue;
      T(d, 'rule', `try rule <b>${r.id}</b>: ${rr.body.map(l => H(substLit(th2, l))).join(' ∧ ')} ⇒ ${H(substLit(th2, rr.head))}`);
      const ch = chain.concat([{ rule: r, goal: g }]);
      for (const res of proveAll(rr.body, th2, d + 1, ch)) {
        any = true;
        const cf = +(r.cf * Math.min(1, ...res.nodes.map(n => n.cf))).toFixed(4);
        T(d, 'ok', `rule ${r.id} proves ${H(substLit(res.th, g))}`);
        yield { th: res.th, node: { lit: substLit(res.th, g), kind: 'rule', rule: r, children: res.nodes, cf } };
      }
    }
    if (!any) T(d, 'fail', `no proof for ${H(g)}`);
  }
  function* proveAll(goals, th, d, chain) {
    if (!goals.length) { yield { th, nodes: [] }; return; }
    for (const r1 of prove(goals[0], th, d, chain))
      for (const r2 of proveAll(goals.slice(1), r1.th, d, chain))
        yield { th: r2.th, nodes: [r1.node, ...r2.nodes] };
  }
  return { prove, proveAll };
}
function finalize(n, th) { return { ...n, lit: substLit(th, n.lit), children: n.children ? n.children.map(c => finalize(c, th)) : undefined }; }

function solveAll(query, answers, opts = {}) {
  GEN = 0;
  const goals = typeof query === 'string' ? parseQuery(query) : query;
  const qv = varsOf(goals);
  const P = makeProver(answers, opts);
  const sols = [], seen = new Set();
  for (const r of P.proveAll(goals, {}, 0, [])) {
    const binding = qv.map(v => [v, subst(r.th, V(v))]);
    const key = binding.map(([v, t]) => v + '=' + termStr(t)).join(';');
    if (seen.has(key)) continue; seen.add(key);
    const nodes = r.nodes.map(n => finalize(n, r.th));
    sols.push({ binding, nodes, cf: Math.min(1, ...nodes.map(n => n.cf)) });
    if (sols.length >= (opts.max || 25)) break;
  }
  return { goals, qv, sols };
}

/* ---------- Forward chaining (data-driven, cycle by cycle) ---------- */
function forwardChain(answers) {
  const wm = [], keys = new Set(), negKnown = new Set();
  const add = (l, how) => { const k = atomKey(l); if (!keys.has(k)) { keys.add(k); wm.push({ lit: l, how }); return true; } return false; };
  KB.facts.forEach(f => add(f, { src: 'kb' }));
  for (const [k, v] of Object.entries(answers)) { if (v === true) add(keyToLit(k), { src: 'answer' }); else if (v === false) negKnown.add(k); }
  const initial = wm.length;
  function* match(lits, th) {
    if (!lits.length) { yield th; return; }
    const [l, ...rest] = lits;
    if (l.neg) { const g = substLit(th, { ...l, neg: false }); if (isGround(g) && negKnown.has(atomKey(g))) yield* match(rest, th); return; }
    for (const w of wm.slice()) { const th2 = unifyLits(l, w.lit, th); if (th2) yield* match(rest, th2); }
  }
  const cycles = [];
  for (let c = 1; c <= 30; c++) {
    const conflict = [], pending = new Set();
    for (const r of KB.rules) {
      const ordered = [...r.body.filter(l => !l.neg), ...r.body.filter(l => l.neg)];
      for (const th of match(ordered, {})) {
        const head = substLit(th, r.head);
        if (!isGround(head)) continue;
        const k = atomKey(head);
        if (keys.has(k) || pending.has(k)) continue;
        pending.add(k);
        conflict.push({ rule: r, th, head, premises: r.body.map(l => substLit(th, l)) });
      }
    }
    if (!conflict.length) break;
    conflict.forEach(x => add(x.head, { src: 'rule', rule: x.rule, cycle: c }));
    cycles.push({ n: c, conflict });
  }
  return { wm, initial, cycles, negKnown: [...negKnown] };
}

/* ---------- Resolution refutation ---------- */
function toClauses(answers) {
  const cl = [];
  KB.facts.forEach(f => cl.push({ lits: [f], src: 'fact' }));
  KB.rules.forEach(r => cl.push({ lits: [...r.body.map(l => ({ ...l, neg: !l.neg })), r.head], src: 'rule ' + r.id }));
  for (const [k, v] of Object.entries(answers)) {
    if (v === true || v === false) cl.push({ lits: [{ ...keyToLit(k), neg: !v }], src: v ? 'answer: yes' : 'answer: no' });
  }
  return cl;
}
function mapVars(lits, m) { const rt = t => t.t === 'v' ? (m[t.n] || t) : t.t === 'f' ? F(t.n, t.a.map(rt)) : t; return lits.map(l => ({ p: l.p, a: l.a.map(rt), neg: l.neg })); }
function renameApart(lits, avoid) {
  const names = varsOf(lits), taken = new Set([...avoid, ...names]), m = {};
  for (const n of names) if (avoid.has(n)) { let c = n + '′'; while (taken.has(c)) c += '′'; taken.add(c); m[n] = V(c); }
  return mapVars(lits, m);
}
function prettyVars(lits) {
  const used = new Set(), m = {};
  for (const n of varsOf(lits)) { let c = n.replace(/′+$/, ''); while (used.has(c)) c += '′'; used.add(c); m[n] = V(c); }
  return mapVars(lits, m);
}
function skel(t) { return t.t === 'v' ? '_' : t.t === 'f' ? t.n + '(' + t.a.map(skel).join(',') + ')' : t.n; }
function ckey(lits) {
  const sk = l => (l.neg ? '~' : '') + l.p + '(' + l.a.map(skel).join(',') + ')';
  const sorted = [...lits].sort((a, b) => sk(a) < sk(b) ? -1 : sk(a) > sk(b) ? 1 : 0);
  const m = {}; let i = 0;
  const ct = t => t.t === 'v' ? (m[t.n] || (m[t.n] = 'V' + (i++))) : t.t === 'f' ? t.n + '(' + t.a.map(ct).join(',') + ')' : t.n;
  return sorted.map(l => (l.neg ? '~' : '') + l.p + '(' + l.a.map(ct).join(',') + ')').join('|');
}
function resolvePair(c, d) {
  const cv = new Set(varsOf(c.lits));
  const dl = renameApart(d.lits, cv);
  const out = [];
  c.lits.forEach((a, i) => dl.forEach((b, j) => {
    if (a.neg === b.neg || a.p !== b.p || a.a.length !== b.a.length || a.p === 'Ans') return;
    const th = unifyLits(a, b, {}); if (!th) return;
    let lits = [...c.lits.filter((_, x) => x !== i), ...dl.filter((_, y) => y !== j)].map(l => substLit(th, l));
    const seen = new Set(); lits = lits.filter(l => { const s = litStr(l); if (seen.has(s)) return false; seen.add(s); return true; });
    const strs = new Set(lits.map(litStr));
    if (lits.some(l => !l.neg && strs.has('¬' + litStr(l)))) return;
    out.push({ lits: prettyVars(lits), th, on: [a, b], dRen: dl });
  }));
  return out;
}
function refute(query, answers, limit = 3000) {
  const goals = parseQuery(query); const qv = varsOf(goals);
  const ans = qv.length ? [{ p: 'Ans', a: qv.map(V), neg: false }] : [];
  const base = toClauses(answers).map(c => ({ ...c, kind: 'input' }));
  const goalC = { lits: [...goals.map(l => ({ ...l, neg: !l.neg })), ...ans], src: 'negated goal', kind: 'input', n: 0 };
  const seen = new Set(base.map(c => ckey(c.lits))); seen.add(ckey(goalC.lits));
  const w = c => c.lits.filter(l => l.p !== 'Ans').length;
  const sos = [goalC], usable = []; let gen = 0, picks = 0;
  while (sos.length && gen < limit) {
    let bi = 0; for (let i = 1; i < sos.length; i++) if (w(sos[i]) < w(sos[bi]) || (w(sos[i]) === w(sos[bi]) && sos[i].n < sos[bi].n)) bi = i;
    const c = sos.splice(bi, 1)[0]; picks++; usable.push(c);
    for (const d of base) {
      for (const r of resolvePair(c, d)) {
        if (r.lits.filter(l => l.p === 'Ans').length > 1) continue;
        const k = ckey(r.lits); if (seen.has(k)) continue; seen.add(k); gen++;
        const nc = { lits: r.lits, parents: [c, d], th: r.th, on: r.on, dRen: r.dRen, kind: 'derived', n: gen };
        if (nc.lits.every(l => l.p === 'Ans')) return { ok: true, final: nc, gen, picks, base, goalC, qv, goals };
        sos.push(nc);
      }
    }
  }
  return { ok: false, gen, picks, base, goalC, qv, goals, exhausted: !sos.length };
}
function proofLedger(final) {
  const order = [], idx = new Map();
  (function visit(c) { if (idx.has(c)) return; if (c.parents) c.parents.forEach(visit); order.push(c); idx.set(c, order.length); })(final);
  return { order, idx };
}

if (typeof module !== 'undefined') module.exports = { buildKB, KB, solveAll, forwardChain, refute, proofLedger, unify, parseTermStr, parseQuery, makeProver, AskNeeded, PRESETS, FAULTS, ASK, classify, addCustom, litStr, termStr, subst, V };
