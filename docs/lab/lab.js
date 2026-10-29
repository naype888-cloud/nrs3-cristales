// RS^N³ · Cristales — the laboratory: every lattice with its own parameters.
(() => {
  "use strict";
  const C = window.Cristales, F = window.Fig, LAT = C.LATTICES;
  const $ = (id) => document.getElementById(id);
  const st = { i: LAT.findIndex((l) => l.id === "cF"), estado: "onda", seed: 7, yaw: 0.7, pitch: 0.42, spin: !matchMedia("(prefers-reduced-motion: reduce)").matches, p: {}, tour: null };
  const fmt = (x, d = 3) => (Math.abs(x) < 5e-12 ? "0" : x.toFixed(d));
  const lat = () => LAT[st.i];
  let R = null, conv = null;

  LAT.forEach((l, i) => { const o = document.createElement("option"); o.value = i; o.textContent = `${l.nombre} (${l.id})`; $("lat").appendChild(o); });
  $("lat").addEventListener("change", () => { stopTour(); pick(+$("lat").value); });

  function pick(i, keep) {
    st.i = i; $("lat").value = i;
    if (!keep) st.p = Object.assign({}, lat().def);
    const box = $("lens"); box.innerHTML = "";
    for (const s of lat().sliders) {
      const l = document.createElement("label"); l.className = "slide";
      l.innerHTML = `<span>${s.label}</span><input type="range" min="${s.min}" max="${s.max}" step="${s.step}" value="${st.p[s.key]}"><output></output>`;
      const inp = l.querySelector("input");
      inp.addEventListener("input", () => { stopTour(); st.p[s.key] = +inp.value; update(); });
      box.appendChild(l);
    }
    update();
  }
  const kappa = () => [+$("kx").value, +$("ky").value, +$("kz").value];
  function update() {
    const l = lat(), kp = kappa(), t = +$("t").value, Lr = +$("L").value;
    lat().sliders.forEach((s, j) => { $("lens").querySelectorAll("output")[j].textContent = (+st.p[s.key]).toFixed(2); });
    $("vkx").textContent = kp[0].toFixed(2); $("vky").textContent = kp[1].toFixed(2); $("vkz").textContent = kp[2].toFixed(2);
    $("vL").textContent = `${Lr} (${(2 * Lr + 1) ** 3})`; $("vt").textContent = t.toFixed(2);
    $("onda").setAttribute("aria-pressed", st.estado === "onda"); $("alea").setAttribute("aria-pressed", st.estado !== "onda");
    const p = C.complete(l, st.p), msg = l.valid(p);
    $("alert").hidden = !msg;
    if (msg) $("alert").textContent = `Con estas longitudes los enlaces de Lean ya no son las capas más cercanas (${msg}). El grafo no cambia y los lemas siguen valiendo; cambia solo la geometría.`;
    R = C.compute({ lat: l, p: st.p, L: Lr, kappa: kp, estado: st.estado, t, seed: st.seed });
    conv = C.convergence(l, st.p, kp, t, 12);
    $("meta").innerHTML = `${l.sistema} · ${l.holo} · <code>${l.lema}</code>`;
    badges(); bars(); draw();
  }
  const badge = (k, v, c) => `<div class="badge ${c || ""}"><span class="k">${k}</span>${v}</div>`;
  function badges() {
    const l = lat(), S = R.Sig, O = R.Om, onda = st.estado === "onda";
    const cov = [1, 2, 3].map((j) => S[0][j]), cero = cov.every((x) => Math.abs(x) < 1e-10);
    const lim = C.limitOmega(l, st.p, kappa(), +$("t").value);
    $("badges").innerHTML = badge("grupo puntual", `|G| = ${l.orden} · ${l.holo}`) + badge("vecinos (grafo de Lean)", l.vecinos) +
      badge("sitios en la región", R.N) +
      badge("Σ_HX · Σ_HY · Σ_HZ", cov.map((x) => fmt(x)).join(" · "), onda ? (cero ? "ok" : "no") : "") +
      badge("Ω_HX · Ω_HY · Ω_HZ", [1, 2, 3].map((j) => fmt(O[0][j])).join(" · ")) +
      (onda ? badge("fórmula exacta (5.1)", R.exact.map((x) => fmt(x)).join(" · "), "ok") : "") +
      badge("límite −½ v (5.2)", lim.map((x) => fmt(x)).join(" · "));
  }
  function bars() {
    const S = R.Sig, O = R.Om, P = F.pal(), names = ["X", "Y", "Z"];
    const row = (n, v, m, c) => { const w = m > 1e-300 ? Math.min(100, 100 * v / m) : 0; return `<div class="brow"><span>${n}</span><div class="tr"><div class="fl" style="width:${w}%;background:${c}"></div></div><output>${w < 0.05 ? "0" : w.toFixed(1)} %</output></div>`; };
    let h = "", ok = true;
    for (let j = 1; j <= 3; j++) {
      const rhs = S[0][0] * S[j][j], c2 = S[0][j] ** 2, o2 = O[0][j] ** 2;
      if (c2 + o2 > rhs * (1 + 1e-9) + 1e-12) ok = false;
      h += `<div class="pairb"><h4>par (H, ${names[j - 1]})</h4>${row("Var H · Var " + names[j - 1], rhs, rhs, P.muted)}${row("Cov² + Ω²", c2 + o2, rhs, P.ink2)}${row("· Cov²", c2, rhs, P.blue)}${row("· Ω²", o2, rhs, P.orange)}</div>`;
    }
    $("bars").innerHTML = h + `<p class="verdict ${ok ? "ok" : ""}">${ok ? "<b>✓</b> la cota se cumple en los tres pares" : "la cota falla"} · con (H, X, Y, Z) a la vez det Ω = 0: las posiciones conmutan</p>`;
  }
  function cube() {
    const Ns = [+$("nx").value, +$("ny").value, +$("nz").value], I = C.cubeInfo(Ns);
    ["x", "y", "z"].forEach((a, j) => ($("vn" + a).textContent = Ns[j]));
    $("rc").innerHTML = ["x", "y", "z"].map((a, j) => `${a}: N = <b>${Ns[j]}</b> · C = <b>${I.C[j].toFixed(6)}</b> · ` + (I.sat[j] ? `<b class="ok">satura</b>` : `<b class="hot">δ = ${I.delta[j].toExponential(2)} &gt; 0</b>`)).join("<br>") +
      `<br>δδδ = <b>${I.vol === 0 ? "0" : I.vol.toExponential(3)}</b> · C<sub>N</sub><sup>∞</sup> = ${C.CINF.toFixed(6)} (no se alcanza)`;
    const P = F.pal();
    F.drawBox($("cubo"), Ns, { pal: P, yaw: st.yaw, pitch: st.pitch }); F.drawCN($("cn"), Ns, { pal: P, Nmax: 60 });
  }
  function draw() {
    if (!R) return;
    const P = F.pal(), l = lat();
    F.drawLattice($("red"), { lat: l, p: st.p, Rc: +$("L").value, yaw: st.yaw, pitch: st.pitch, pal: P, bonds: "all", phase: R, fit: 0.44 });
    F.drawMats($("mats"), R, { pal: P, estado: st.estado });
    F.drawBand($("banda"), R, { pal: P, lat: l, kappa: kappa(), t: +$("t").value });
    F.drawConv($("conv"), conv, C.limitOmega(l, st.p, kappa(), +$("t").value), { pal: P });
    cube();
  }
  // phase colouring needs the same cell order as the scene: only when the scene covers the whole region
  const origDraw = draw;

  // ---- interaction --------------------------------------------------------------------------------------------
  for (const id of ["red", "cubo"]) {
    const cv = $(id); let d = null;
    cv.addEventListener("pointerdown", (e) => { d = [e.clientX, e.clientY]; st.spin = false; cv.setPointerCapture(e.pointerId); });
    cv.addEventListener("pointermove", (e) => { if (!d) return; st.yaw += (e.clientX - d[0]) * 0.01; st.pitch = Math.max(-1.35, Math.min(1.35, st.pitch + (e.clientY - d[1]) * 0.008)); d = [e.clientX, e.clientY]; origDraw(); });
    cv.addEventListener("pointerup", () => (d = null)); cv.addEventListener("pointercancel", () => (d = null));
  }
  for (const id of ["kx", "ky", "kz", "L", "t"]) $(id).addEventListener("input", () => { stopTour(); update(); });
  for (const id of ["nx", "ny", "nz"]) $(id).addEventListener("input", cube);
  $("onda").addEventListener("click", () => { st.estado = "onda"; update(); });
  $("alea").addEventListener("click", () => { st.estado = "aleatorio"; st.seed = (st.seed * 7919 + 13) % 100003; update(); });
  function randomize() {
    const i = Math.floor(Math.random() * LAT.length), l = LAT[i];
    st.p = Object.assign({}, l.def);
    for (const s of l.sliders) { const v = +(l.def[s.key] * (0.92 + 0.16 * Math.random())).toFixed(2); st.p[s.key] = Math.min(s.max, Math.max(s.min, v)); }
    if (l.valid(C.complete(l, st.p))) st.p = Object.assign({}, l.def);
    for (const id of ["kx", "ky", "kz"]) $(id).value = (Math.random() * 1.6 - 0.8).toFixed(2);
    st.estado = Math.random() < 0.7 ? "onda" : "aleatorio"; pick(i, true);
  }
  function stopTour() { if (st.tour) { clearInterval(st.tour); st.tour = null; $("tour").setAttribute("aria-pressed", "false"); } }
  $("rand").addEventListener("click", () => { stopTour(); randomize(); });
  $("tour").addEventListener("click", () => { if (st.tour) return stopTour(); $("tour").setAttribute("aria-pressed", "true"); randomize(); st.tour = setInterval(randomize, 5000); });
  setInterval(() => { if (st.spin && !document.hidden && R) { st.yaw += 0.01; origDraw(); } }, 40);
  new MutationObserver(origDraw).observe(document.documentElement, { attributes: true, attributeFilter: ["data-theme"] });
  matchMedia("(prefers-color-scheme: dark)").addEventListener("change", origDraw);
  addEventListener("resize", origDraw);
  pick(st.i);
})();
