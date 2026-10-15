// NRS³ · Cristales — interfaz y dibujo de la página.
"use strict";
const C = window.Cristales;
const $ = id => document.getElementById(id);
const css = n => getComputedStyle(document.documentElement).getPropertyValue(n).trim();
const st = { lat: C.LATTICES[0], estado: "onda", yaw: 0.7, pitch: 0.42, seed: 7, tour: null };

// tema
$("theme").onclick = () => {
  const r = document.documentElement, dark = r.dataset.theme ? r.dataset.theme === "dark"
    : matchMedia("(prefers-color-scheme: dark)").matches;
  r.dataset.theme = dark ? "light" : "dark"; draw();
};

// chips de redes, agrupadas por familia
(function () {
  const box = $("lats"); let fam = "";
  for (const lat of C.LATTICES) {
    if (lat.familia !== fam) { fam = lat.familia; const s = document.createElement("span"); s.className = "fam"; s.textContent = fam; box.appendChild(s); }
    const b = document.createElement("button"); b.className = "chip"; b.type = "button"; b.textContent = lat.nombre;
    b.dataset.id = lat.id; b.onclick = () => { stopTour(); pick(lat); }; box.appendChild(b);
  }
  const s = document.createElement("span"); s.className = "fam"; s.textContent = "pendientes"; box.appendChild(s);
  for (const p of C.PENDIENTES) { const b = document.createElement("button"); b.className = "chip"; b.disabled = true; b.textContent = p; b.title = "todavía no está en Lean"; box.appendChild(b); }
})();

function pick(lat, keep) {
  st.lat = lat;
  if (!keep) { $("a").value = lat.def[0]; $("b").value = lat.def[1]; $("c").value = lat.def[2]; }
  for (const b of $("lats").querySelectorAll("button[data-id]")) b.setAttribute("aria-pressed", b.dataset.id === lat.id);
  update();
}

function lengths() {
  let a = +$("a").value, b = +$("b").value, c = +$("c").value;
  const f = st.lat.forma;
  if (f === "a") { b = a; c = a; } else if (f === "ac") { b = a; }
  $("lb").classList.toggle("off", f !== "abc"); $("lc").classList.toggle("off", f === "a");
  $("b").disabled = f !== "abc"; $("c").disabled = f === "a";
  return [a, b, c];
}

let R = null;
function update() {
  const [a, b, c] = lengths();
  const kappa = [+$("kx").value, +$("ky").value, +$("kz").value], t = +$("t").value, L = +$("L").value;
  $("va").textContent = a.toFixed(2); $("vb").textContent = b.toFixed(2); $("vc").textContent = c.toFixed(2);
  $("vL").textContent = L + " (" + (2 * L + 1) ** 3 + ")"; $("vt").textContent = t.toFixed(2);
  $("vkx").textContent = kappa[0].toFixed(2); $("vky").textContent = kappa[1].toFixed(2); $("vkz").textContent = kappa[2].toFixed(2);
  const msg = st.lat.valid(a, b, c);
  $("alert").hidden = !msg;
  if (msg) $("alert").textContent = "Con estas longitudes los enlaces de Lean ya no son las capas más cercanas (" + msg +
    "). El grafo no cambia y los lemas siguen valiendo; cambia solo la geometría.";
  R = C.compute({ lat: st.lat, a, b, c, L, kappa, estado: st.estado, t, seed: st.seed });
  R.a = a; R.b = b; R.c = c; R.kappa = kappa; R.t = t;
  $("onda").setAttribute("aria-pressed", st.estado === "onda"); $("alea").setAttribute("aria-pressed", st.estado !== "onda");
  badges(); pairs(); draw();
}

const fmt = (x, d = 4) => (Math.abs(x) < 5e-13 ? "0" : x.toFixed(d));
function badge(k, v, cls) { return `<div class="badge ${cls || ""}"><span class="k">${k}</span>${v}</div>`; }
function badges() {
  const S = R.Sig, O = R.Om, onda = st.estado === "onda";
  const cov = [1, 2, 3].map(j => S[0][j]), cero = cov.every(x => Math.abs(x) < 1e-10);
  const dS = C.det(S), dO = Math.abs(C.det(O));
  $("badges").innerHTML =
    badge("grupo puntual (" + st.lat.lema + ")", "orden " + st.lat.orden) +
    badge("vecinos (grafo de Lean)", C.bondVectors(st.lat).length) +
    badge("sitios en la región", R.N) +
    badge("cov(H, X), cov(H, Y), cov(H, Z)", cov.map(x => fmt(x, 3)).join(" · "), cero ? "ok" : "no") +
    badge("Ω_HX · Ω_HY · Ω_HZ", [1, 2, 3].map(j => fmt(O[0][j], 3)).join(" · ")) +
    (onda ? badge("fórmula exacta del lema", R.exact.map(x => fmt(x, 3)).join(" · "), "ok") : "") +
    badge("límite −½ v", R.vel.map(x => fmt(-x / 2, 3)).join(" · ")) +
    badge("Robertson 1934: |det Ω| ≤ det Σ", fmt(dO, 3) + " ≤ " + fmt(dS, 3), dO <= dS + 1e-12 ? "ok" : "no");
}

function bar(label, val, max, color) {
  const w = max > 0 ? Math.min(100, 100 * Math.abs(val) / max) : 0;
  return `<div class="barrow"><span>${label}</span><div class="bartrack"><div class="barfill" style="width:${w}%;background:${color}"></div></div></div>`;
}
function pairs() {
  const S = R.Sig, O = R.Om, blue = css("--blue"), orange = css("--orange"), green = css("--green"), violet = css("--violet");
  const prod = S[0][0] * S[1][1], cov2 = S[0][1] ** 2, om2 = O[0][1] ** 2;
  const onda = st.estado === "onda";
  $("pairHX").innerHTML =
    `<div class="row"><span>Var H · Var X</span><b>${fmt(prod, 4)}</b></div>` +
    `<div class="row"><span>Cov(H, X)²</span><b>${fmt(cov2, 4)}</b></div>` +
    `<div class="row"><span>⟨⁅H, X⁆⟩²</span><b>${fmt(om2, 4)}</b></div>` +
    `<div class="bars">${bar("Var H · Var X", prod, prod, blue)}${bar("Cov² + ⟨⁅H,X⁆⟩²", cov2 + om2, prod, orange)}${bar("  de eso, Cov²", cov2, prod, onda ? green : violet)}</div>` +
    `<p class="sub">Robertson–Schrödinger: <code>Cov² + ⟨⁅H,X⁆⟩² ≤ Var H · Var X</code> (<code>robertson_schrodinger</code>). ` +
    (onda ? `En la onda plana <code>Cov = 0</code> por la simetría (<code>covariance_hopping_position_unitPlaneWave</code>): todo el peso está en el corchete.`
      : `Sin simetría la covarianza reaparece y se reparte el peso con el corchete.`) + `</p>`;
  const p2 = S[1][1] * S[2][2], c2 = S[1][2] ** 2;
  $("pairXY").innerHTML =
    `<div class="row"><span>Var X · Var Y</span><b>${fmt(p2, 4)}</b></div>` +
    `<div class="row"><span>Cov(X, Y)²</span><b>${fmt(c2, 4)}</b></div>` +
    `<div class="row"><span>⟨⁅X, Y⁆⟩</span><b>${fmt(O[1][2], 4)}</b></div>` +
    `<div class="bars">${bar("Var X · Var Y", p2, p2, blue)}${bar("Cov(X, Y)²", c2, p2, orange)}</div>` +
    `<p class="sub">Las posiciones conmutan, así que <code>Ω<sub>XY</sub> = 0</code> en todo estado y la cota es solo la positividad de la matriz de Gram (lo fundamental, como dice Tom). En las redes primitivas de ejes ortogonales (cúbica, tetragonal y ortorrómbica simples) la región es una caja alineada con los ejes y, como <code>|ψ|²</code> es uniforme en la onda plana, también <code>Cov(X, Y) = 0</code>; en las demás la caja está inclinada y la covarianza no tiene por qué anularse.</p>`;
}

// ---- dibujo ----
function rot(p) {
  const cy = Math.cos(st.yaw), sy = Math.sin(st.yaw), cp = Math.cos(st.pitch), sp = Math.sin(st.pitch);
  const x = cy * p[0] - sy * p[1], y = sy * p[0] + cy * p[1];
  return [x, cp * p[2] - sp * y, sp * p[2] + cp * y];
}
function setup(cv) {
  const r = cv.getBoundingClientRect(), dpr = devicePixelRatio || 1;
  cv.width = Math.max(10, r.width * dpr); cv.height = Math.max(10, r.height * dpr);
  const g = cv.getContext("2d"); g.setTransform(dpr, 0, 0, dpr, 0, 0); return [g, r.width, r.height];
}
function arrow(g, x0, y0, x1, y1, color, dash) {
  g.strokeStyle = color; g.fillStyle = color; g.lineWidth = dash ? 3.4 : 2.2;
  g.setLineDash(dash ? [6, 4] : []);
  g.beginPath(); g.moveTo(x0, y0); g.lineTo(x1, y1); g.stroke(); g.setLineDash([]);
  const an = Math.atan2(y1 - y0, x1 - x0), h = 9;
  g.beginPath(); g.moveTo(x1, y1); g.lineTo(x1 - h * Math.cos(an - 0.4), y1 - h * Math.sin(an - 0.4));
  g.lineTo(x1 - h * Math.cos(an + 0.4), y1 - h * Math.sin(an + 0.4)); g.closePath(); g.fill();
}
function drawRed() {
  const [g, W, H] = setup($("red"));
  g.clearRect(0, 0, W, H);
  const show = []; const Ls = Math.min(2, +$("L").value);
  R.cells.forEach((n, i) => { if (Math.abs(n[0]) <= Ls && Math.abs(n[1]) <= Ls && Math.abs(n[2]) <= Ls) show.push(i); });
  let ext = 1e-9; for (const i of show) for (const x of R.pos[i]) ext = Math.max(ext, Math.abs(x));
  const sc = 0.36 * Math.min(W, H) / ext, cx = W / 2, cy = H / 2;
  const P = p => { const q = rot(p); return [cx + sc * q[0], cy - sc * q[1], q[2]]; };
  // enlaces del sitio central
  const o = P([0, 0, 0]);
  g.strokeStyle = css("--orange"); g.lineWidth = 2;
  for (const d of R.bvc) { const q = P(d); g.beginPath(); g.moveTo(o[0], o[1]); g.lineTo(q[0], q[1]); g.stroke(); }
  // sitios, del fondo al frente
  const pts = show.map(i => { const q = P(R.pos[i]); return [q, i]; }).sort((u, v) => u[0][2] - v[0][2]);
  for (const [q, i] of pts) {
    const amp = (R.re[i] ** 2 + R.im[i] ** 2) * R.N, ph = Math.atan2(R.im[i], R.re[i]);
    const r = Math.max(1.6, Math.min(9, 3.2 * Math.sqrt(amp)));
    g.fillStyle = `hsl(${(ph * 180 / Math.PI + 360) % 360}, 70%, 52%)`;
    g.globalAlpha = 0.35 + 0.65 * (0.5 + 0.5 * Math.tanh(q[2] / (sc * ext)));
    g.beginPath(); g.arc(q[0], q[1], r, 0, 2 * Math.PI); g.fill();
  }
  g.globalAlpha = 1;
  // flechas: velocidad de grupo y (Ω_HX, Ω_HY, Ω_HZ)
  const vm = Math.hypot(...R.vel), om = [R.Om[0][1], R.Om[0][2], R.Om[0][3]], omm = Math.hypot(...om);
  const s2 = 0.75 * ext;
  if (omm > 1e-9 && vm > 1e-9) { const q = P(om.map(x => -x / vm * s2 * 2)); arrow(g, o[0], o[1], q[0], q[1], css("--green"), true); }
  if (vm > 1e-9) { const q = P(R.vel.map(x => x / vm * s2)); arrow(g, o[0], o[1], q[0], q[1], css("--violet")); }
  g.fillStyle = css("--muted"); g.font = "12px system-ui";
  g.fillText(st.lat.nombre + " · " + C.bondVectors(st.lat).length + " vecinos", 10, H - 10);
}
function drawMats() {
  const [g, W, H] = setup($("mats"));
  g.clearRect(0, 0, W, H);
  const lab = ["H", "X", "Y", "Z"], pad = 22, gap = 18, size = Math.min((W - 2 * pad - gap) / 2, H - 48), cell = size / 4;
  const mats = [["Σ (covarianzas)", R.Sig, true], ["Ω (corchetes)", R.Om, false]];
  const onda = st.estado === "onda";
  mats.forEach(([name, M, sym], m) => {
    const x0 = pad + m * (size + gap) + 14, y0 = 30;
    let mx = 1e-12; for (const r of M) for (const v of r) mx = Math.max(mx, Math.abs(v));
    g.fillStyle = css("--ink2"); g.font = "600 13px system-ui"; g.fillText(name, x0, 18);
    g.font = "11px system-ui";
    for (let i = 0; i < 4; i++) {
      g.fillStyle = css("--muted"); g.fillText(lab[i], x0 - 12, y0 + cell * (i + 0.6)); g.fillText(lab[i], x0 + cell * (i + 0.4), y0 + size + 13);
      for (let j = 0; j < 4; j++) {
        const v = M[i][j], z = Math.abs(v) < 1e-10;
        // ceros forzados: Ω diagonal (siempre), Ω entre posiciones (conmutan), Σ_HX en la onda plana (lema)
        const forced = z && ((!sym && (i === j || (i > 0 && j > 0))) || (sym && onda && (i === 0) !== (j === 0)));
        const col = v >= 0 ? css("--blue") : css("--orange");
        g.globalAlpha = forced ? 0.22 : 0.12 + 0.85 * Math.abs(v) / mx;
        g.fillStyle = forced ? css("--green") : col;
        g.fillRect(x0 + j * cell + 1, y0 + i * cell + 1, cell - 2, cell - 2);
        g.globalAlpha = 1; g.fillStyle = forced ? css("--green") : css("--ink");
        g.font = (forced ? "600 " : "") + Math.max(9, Math.min(12, cell / 4.6)) + "px system-ui";
        const txt = z ? "0" : (Math.abs(v) >= 100 ? v.toFixed(0) : v.toFixed(2));
        g.fillText(txt, x0 + j * cell + cell / 2 - g.measureText(txt).width / 2, y0 + i * cell + cell / 2 + 4);
      }
    }
  });
}
function drawBanda() {
  const [g, W, H] = setup($("banda"));
  g.clearRect(0, 0, W, H);
  const line = C.bandLine(st.lat, R.a, R.b, R.c, R.kappa, R.t);
  let lo = Infinity, hi = -Infinity; for (const [, e] of line) { lo = Math.min(lo, e); hi = Math.max(hi, e); }
  if (hi - lo < 1e-9) { hi += 1; lo -= 1; }
  const px = 44, py = 18, w = W - px - 14, h = H - 2 * py - 10;
  const X = s => px + (s + 1) / 2 * w, Y = e => py + (hi - e) / (hi - lo) * h;
  g.strokeStyle = css("--grid"); g.lineWidth = 1; g.strokeRect(px, py, w, h);
  g.fillStyle = css("--muted"); g.font = "11px system-ui";
  g.fillText(hi.toFixed(2), 4, py + 8); g.fillText(lo.toFixed(2), 4, py + h);
  g.fillText("−k", px, H - 6); g.fillText("0", X(0) - 3, H - 6); g.fillText("k", px + w - 8, H - 6);
  g.strokeStyle = css("--blue"); g.lineWidth = 2; g.beginPath();
  line.forEach(([s, e], i) => i ? g.lineTo(X(s), Y(e)) : g.moveTo(X(s), Y(e))); g.stroke();
  // pendiente en s = 1 (el k elegido)
  const kh = Math.hypot(...R.kappa.map((x, j) => x * Math.PI / [R.a, R.b, R.c][j]));
  const e1 = R.band, x1 = X(1), y1 = Y(e1);
  const slope = kh > 1e-9 ? R.vel.reduce((s, v, j) => s + v * R.kappa[j] * Math.PI / [R.a, R.b, R.c][j], 0) / kh : 0;
  const ds = 0.35, de = slope * kh * ds;
  g.strokeStyle = css("--violet"); g.lineWidth = 2;
  g.beginPath(); g.moveTo(X(1 - ds), Y(e1 - de)); g.lineTo(x1, y1); g.stroke();
  g.fillStyle = css("--violet"); g.beginPath(); g.arc(x1, y1, 4.5, 0, 2 * Math.PI); g.fill();
  g.font = "12px system-ui";
  g.fillText("pendiente = velocidad de grupo a lo largo de k: " + slope.toFixed(3), px + 8, py + 16);
}
function draw() { if (R) { drawRed(); drawMats(); drawBanda(); } }

// arrastrar para girar
(function () {
  const cv = $("red"); let drag = null;
  cv.addEventListener("pointerdown", e => { drag = [e.clientX, e.clientY]; cv.setPointerCapture(e.pointerId); stopSpin(); });
  cv.addEventListener("pointermove", e => { if (!drag) return; st.yaw += (e.clientX - drag[0]) * 0.01; st.pitch = Math.max(-1.4, Math.min(1.4, st.pitch + (e.clientY - drag[1]) * 0.01)); drag = [e.clientX, e.clientY]; drawRed(); });
  cv.addEventListener("pointerup", () => { drag = null; });
})();
let spin = setInterval(() => { st.yaw += 0.006; if (R) drawRed(); }, 40);
function stopSpin() { if (spin) { clearInterval(spin); spin = null; } }

for (const id of ["a", "b", "c", "L", "kx", "ky", "kz", "t"]) $(id).addEventListener("input", () => { stopTour(); update(); });
$("onda").onclick = () => { st.estado = "onda"; update(); };
$("alea").onclick = () => { st.estado = "aleatorio"; st.seed = (st.seed * 7919 + 13) % 100003; update(); };

function randomize() {
  const lat = C.LATTICES[Math.floor(Math.random() * C.LATTICES.length)];
  st.lat = lat;
  const jit = x => +(x * (0.9 + 0.2 * Math.random())).toFixed(2);
  let [a, b, c] = lat.def.map(jit);
  if (lat.valid(a, b, c)) [a, b, c] = lat.def;
  $("a").value = a; $("b").value = b; $("c").value = c;
  for (const id of ["kx", "ky", "kz"]) $(id).value = (Math.random() * 1.6 - 0.8).toFixed(2);
  st.estado = Math.random() < 0.7 ? "onda" : "aleatorio"; st.seed = Math.floor(Math.random() * 1e5);
  pick(lat, true);
}
$("random").onclick = () => { stopTour(); randomize(); };
function stopTour() { if (st.tour) { clearInterval(st.tour); st.tour = null; $("tour").setAttribute("aria-pressed", "false"); } }
$("tour").onclick = () => {
  if (st.tour) { stopTour(); return; }
  $("tour").setAttribute("aria-pressed", "true"); randomize(); st.tour = setInterval(randomize, 5000);
};

// tabla de lemas
(function () {
  const F = "https://github.com/naype888-cloud/physlib/blob/mosaic-cristales/PhyslibAlpha/";
  const rows = [
    ["Las redes y sus grupos puntuales: cúbicas 48, tetragonales 16, hexagonal 24, ortorrómbicas 8 (con las 8 operaciones explícitas)",
      "card_pointGroup_hypercubic, bcc_/fcc_card_pointGroup, tetragonal_…, hexagonal_…, orthorhombic_… (4)", "CondensedMatter/Crystal/PointGroup/"],
    ["Toda red con un sitio por celda es centrosimétrica", "PeriodicGraph.inversion_mem_symmetries", "CondensedMatter/Crystal/Inversion.lean"],
    ["Inversión × inversión temporal: f H f = H, f X f = −X", "inversionReversal_hopping, inversionReversal_position", "CondensedMatter/Crystal/Inversion.lean"],
    ["En toda onda plana, Σ_HX = 0 en todas las direcciones", "covariance_hopping_position_unitPlaneWave", "CondensedMatter/Crystal/Inversion.lean"],
    ["Ω_HX exacto en una región finita: suma sobre los enlaces internos", "expectation_bracket_unitPlaneWave", "CondensedMatter/Crystal/GroupVelocity.lean"],
    ["La banda y su velocidad de grupo", "band, hasDerivAt_band", "CondensedMatter/Crystal/GroupVelocity.lean"],
    ["En cajas grandes, Ω_HX → −½ v (Følner)", "tendsto_expectation_bracket_box", "CondensedMatter/Crystal/GroupVelocity.lean"],
    ["Grupo pequeño de k: si fija k e invierte r, Σ_HX = Ω_HX = 0 en la onda plana (la velocidad de grupo a lo largo de r se anula)", "covariance_/expectation_bracket_hopping_position_littleGroup", "CondensedMatter/Crystal/LittleGroup.lean"],
    ["En Γ y en las esquinas de la zona (χ(−n) = χ(n)) la inversión está en el grupo pequeño: Ω_HX = 0 en toda dirección", "expectation_bracket_hopping_position_of_neg", "CondensedMatter/Crystal/LittleGroup.lean"],
    ["Estado simétrico ⇒ Σ_AB = Ω_AB = 0 (par/impar); con inversión temporal, Σ entre paridades, Ω dentro de una", "covariance_eq_zero_of_symm, …_of_reverse", "ProbabilisticTheory/CStarAlgebra/SymmetricState.lean"],
    ["Antiunitario f con f∘f = id: estado fijo ⇒ par e impar sin correlación", "covariance_ofVec_eq_zero_of_antiunitary", "ProbabilisticTheory/HilbertSpace/State/Antiunitary.lean"],
    ["Robertson 1934 para los estados de cristal (sin norma): |det Ω| ≤ det Σ", "AlgState.robertson_det, AlgState.robertson_schrodinger", "ProbabilisticTheory/StarAlgebra/StateUncertainty.lean"],
    ["En el estado térmico invariante por traslación; traslación que fija A e invierte B ⇒ Σ_AB = Ω_AB = 0", "robertson_det_translationInvariantState, covariance_translationInvariantState_eq_zero", "CondensedMatter/Crystal/InvariantStateUncertainty.lean"],
    ["Cadena: cov(H, X) = 0 en el estado de corriente máxima, por la simetría partícula–hueco", "covariance_maxCurrentState", "CondensedMatter/TightBindingChain/MaxCurrentState/ParticleHole.lean"],
  ];
  $("ledger").querySelector("tbody").innerHTML = rows.map(([q, l, f]) =>
    `<tr><td>${q}</td><td><code>${l}</code></td><td><a href="${F + f}">${f.split("/").pop() || f}</a></td></tr>`).join("");
})();

addEventListener("resize", draw);
matchMedia("(prefers-color-scheme: dark)").addEventListener("change", draw);
pick(C.LATTICES[0]);
