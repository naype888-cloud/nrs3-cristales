// RS^N³ · Cristales — the didactic page. One lattice chosen by the reader drives every figure.
(() => {
  "use strict";
  const C = window.Cristales, F = window.Fig, LAT = C.LATTICES;
  const $ = (id) => document.getElementById(id);
  const still = matchMedia("(prefers-reduced-motion: reduce)");
  const st = { i: LAT.findIndex((l) => l.id === "cF"), estado: "onda", seed: 7, inv: 0, yaw: 0.7, pitch: 0.42, spin: !still.matches };
  const fmt = (x, d = 3) => (Math.abs(x) < 5e-12 ? "0" : x.toFixed(d));
  const lat = () => LAT[st.i];

  try {
    const q = new URLSearchParams(location.search).get("red"), j = LAT.findIndex((l) => l.id === q);
    if (j >= 0) st.i = j;
  } catch (e) {}

  // ---- the chooser: chips by system, a select, the gallery --------------------------------------------------
  const chips = $("chips"), sel = $("latSel"), gal = $("gallery");
  let sys = "";
  LAT.forEach((l, i) => {
    if (l.sistema !== sys) { sys = l.sistema; const s = document.createElement("span"); s.className = "sys"; s.textContent = sys.toLowerCase(); chips.appendChild(s); }
    const b = document.createElement("button");
    b.type = "button"; b.textContent = l.id; b.title = l.nombre; b.setAttribute("aria-label", l.nombre); b.dataset.i = i;
    b.addEventListener("click", () => pick(i)); chips.appendChild(b);
    const o = document.createElement("option"); o.value = i; o.textContent = `${l.nombre} (${l.id})`; sel.appendChild(o);
    const c = document.createElement("button");
    c.type = "button"; c.className = "card-l"; c.dataset.i = i; c.setAttribute("role", "listitem");
    c.innerHTML = `<canvas aria-hidden="true"></canvas><span class="tag">${l.id}</span><span class="n">${l.nombre}</span><span class="m">|G| = ${l.orden} · ${l.vecinos} vec.</span>`;
    c.addEventListener("click", () => { pick(i); document.getElementById("p2").scrollIntoView({ behavior: still.matches ? "auto" : "smooth", block: "start" }); });
    gal.appendChild(c);
  });
  sel.addEventListener("change", () => pick(+sel.value));
  $("rand").addEventListener("click", () => {
    pick(Math.floor(Math.random() * LAT.length));
    for (const id of ["kx", "ky", "kz"]) $(id).value = (Math.random() * 1.6 - 0.8).toFixed(2);
    update();
  });

  // ---- state and update -----------------------------------------------------------------------------------------
  let R = null, conv = null, lim = null;
  function pick(i) {
    st.i = i; sel.value = i; pickTracers();
    for (const b of chips.querySelectorAll("button")) b.setAttribute("aria-pressed", +b.dataset.i === i);
    for (const b of gal.querySelectorAll(".card-l")) b.setAttribute("aria-pressed", +b.dataset.i === i);
    try { const u = new URL(location.href); u.searchParams.set("red", lat().id); history.replaceState(null, "", u); } catch (e) {}
    update();
  }
  const kappa = () => [+$("kx").value, +$("ky").value, +$("kz").value];
  function update() {
    const l = lat(), kp = kappa(), t = +$("t").value;
    $("vkx").textContent = kp[0].toFixed(2); $("vky").textContent = kp[1].toFixed(2); $("vkz").textContent = kp[2].toFixed(2); $("vt").textContent = t.toFixed(2);
    $("onda").setAttribute("aria-pressed", st.estado === "onda"); $("alea").setAttribute("aria-pressed", st.estado !== "onda");
    R = C.compute({ lat: l, p: {}, L: 2, kappa: kp, estado: st.estado, t, seed: st.seed });
    conv = C.convergence(l, {}, kp, t, 10); lim = C.limitOmega(l, {}, kp, t);
    text(); draw();
  }

  function text() {
    const l = lat(), S = R.Sig, O = R.Om, onda = st.estado === "onda";
    const b = l.bonds.map((d) => "(" + d.join(",") + ")").join(" ");
    $("r2").innerHTML = `<b>${l.nombre}</b> · <b>${l.vecinos}</b> vecinos<br>enlaces (±), en coordenadas de la red:<br>${b}`;
    $("l2").textContent = `${l.grafo}: ${l.vecinos} vecinos por sitio`;
    $("r3").innerHTML = `<b>|G| = ${l.orden}</b> · ${l.holo} · sistema ${l.sistema.toLowerCase()}<br>Lean: <code>${l.lema}</code>`;
    const cov = [1, 2, 3].map((j) => S[0][j]);
    $("r5").innerHTML = (onda
      ? `Σ<sub>HX</sub> · Σ<sub>HY</sub> · Σ<sub>HZ</sub> = <b class="ok">${cov.map((x) => fmt(x)).join(" · ")}</b> (forzados)`
      : `Σ<sub>HX</sub> · Σ<sub>HY</sub> · Σ<sub>HZ</sub> = <b class="hot">${cov.map((x) => fmt(x)).join(" · ")}</b> (reaparecen)`) +
      `<br>Ω<sub>HX</sub> · Ω<sub>HY</sub> · Ω<sub>HZ</sub> = <b>${[1, 2, 3].map((j) => fmt(O[0][j])).join(" · ")}</b>` +
      `<br>Ω entre X, Y, Z = <b class="ok">0</b> siempre (conmutan)`;
    const kh = Math.hypot(...R.k), slope = kh > 1e-9 ? (R.vel[0] * R.k[0] + R.vel[1] * R.k[1] + R.vel[2] * R.k[2]) / kh : 0;
    $("r6").innerHTML = `velocidad de grupo a lo largo de k = <b>${fmt(slope)}</b><br>límite −½ v = <b>${lim.map((x) => fmt(x)).join(" · ")}</b>` +
      `<br>caja L = 2 (onda plana, fórmula exacta) = <b>${R.exact.map((x) => fmt(x)).join(" · ")}</b>` +
      `<br>caja L = 10 = <b>${conv[9][1].map((x) => fmt(x)).join(" · ")}</b>`;
    bars();
  }

  const row = (name, v, max, col) => {
    const w = max > 1e-300 ? Math.min(100, 100 * v / max) : 0;
    return `<div class="brow"><span>${name}</span><div class="tr"><div class="fl" style="width:${w}%;background:${col}"></div></div><output>${w < 0.05 ? "0" : w.toFixed(w < 1 ? 2 : 1)} %</output></div>`;
  };
  function bars() {
    const S = R.Sig, O = R.Om, P = F.pal(), names = ["X", "Y", "Z"];
    let html = "", allOk = true;
    for (let j = 1; j <= 3; j++) {
      const rhs = S[0][0] * S[j][j], c2 = S[0][j] ** 2, o2 = O[0][j] ** 2, lhs = c2 + o2;
      if (lhs > rhs * (1 + 1e-9) + 1e-12) allOk = false;
      html += `<div class="pairb"><h4>par (H, ${names[j - 1]})</h4>` +
        row("Var H · Var " + names[j - 1], rhs, rhs, P.muted) +
        row("Cov² + Ω²", lhs, rhs, P.ink2) + row("· Cov²", c2, rhs, P.blue) + row("· Ω²", o2, rhs, P.orange) + `</div>`;
    }
    $("c7").innerHTML = html + `<p class="verdict ${allOk ? "ok" : ""}">${allOk ? "<b>✓</b> Cov² + Ω² ≤ Var H · Var X en los tres pares" : "la cota no se cumple: revisa el estado"}</p>`;
    const S0 = S[0][1], hx = S[0][0] * S[1][1];
    $("r7").innerHTML = `par (H, X): lado izquierdo = <b>${fmt(S0 * S0 + O[0][1] ** 2, 4)}</b> ≤ lado derecho = <b>${fmt(hx, 4)}</b>`;
  }

  // ---- drawing ------------------------------------------------------------------------------------------------------
  const vis = new Set();
  const STEPS = ["p1", "p2", "p3", "p4", "p5", "p6", "p7", "p8"];
  STEPS.forEach((id) => vis.add(id));
  const io = "IntersectionObserver" in window ? new IntersectionObserver((es) => {
    es.forEach((e) => (e.isIntersecting ? vis.add(e.target.id) : vis.delete(e.target.id)));
    draw(); drawGallery();
  }, { rootMargin: "80px" }) : null;
  if (io) STEPS.forEach((id) => io.observe($(id)));

  let tracers = [];
  function pickTracers() {
    const S = F.scene(lat(), {}, 2), c = [];
    S.cells.forEach((n, i) => { if (i !== S.centre && n[0] + 2 * n[1] + 3 * n[2] > 0 && Math.abs(n[0]) + Math.abs(n[1]) + Math.abs(n[2]) <= 3) c.push(i); });
    let s = 11; const r = () => ((s = (s * 1103515245 + 12345) & 0x7fffffff) / 0x7fffffff);
    c.sort(() => r() - 0.5); tracers = c.slice(0, 7);
  }

  function draw() {
    if (!R) return;
    const P = F.pal(), l = lat();
    if (vis.has("p2")) F.drawLattice($("c2"), { lat: l, p: {}, Rc: 2, yaw: st.yaw, pitch: st.pitch, pal: P, bonds: "all", fit: 0.4 });
    if (vis.has("p3")) F.drawLattice($("c3"), { lat: l, p: {}, Rc: 2, yaw: st.yaw, pitch: st.pitch, pal: P, bonds: "none", tracers, inv: st.inv, fit: 0.4 });
    if (vis.has("p4")) F.drawLattice($("c4"), { lat: l, p: {}, Rc: 2, yaw: st.yaw, pitch: st.pitch, pal: P, bonds: "none", phase: R, fit: 0.4 });
    if (vis.has("p5")) F.drawMats($("c5"), R, { pal: P, estado: st.estado });
    if (vis.has("p8")) {
      const Ns = [+$("nx").value, +$("ny").value, +$("nz").value];
      F.drawBox($("c8a"), Ns, { pal: P, yaw: st.yaw, pitch: st.pitch }); F.drawCN($("c8b"), Ns, { pal: P, Nmax: 60 });
    }
    if (vis.has("p6")) { F.drawBand($("c6a"), R, { pal: P, lat: l, kappa: kappa(), t: +$("t").value }); F.drawConv($("c6b"), conv, lim, { pal: P }); }
  }
  function drawGallery() {
    if (!vis.has("p1")) return;
    const P = F.pal();
    gal.querySelectorAll(".card-l").forEach((c) => {
      const i = +c.dataset.i;
      F.drawLattice(c.querySelector("canvas"), { lat: LAT[i], p: {}, Rc: 1, yaw: st.yaw * 0.7 + i * 0.35, pitch: 0.42, pal: P, bonds: "all", fit: 0.42 });
    });
  }

  // ---- interaction ------------------------------------------------------------------------------------------------------
  for (const id of ["c2", "c3", "c4"]) {
    const cv = $(id); let drag = null;
    cv.addEventListener("pointerdown", (e) => { drag = [e.clientX, e.clientY]; st.spin = false; cv.setPointerCapture(e.pointerId); });
    cv.addEventListener("pointermove", (e) => {
      if (!drag) return;
      st.yaw += (e.clientX - drag[0]) * 0.01; st.pitch = Math.max(-1.35, Math.min(1.35, st.pitch + (e.clientY - drag[1]) * 0.008));
      drag = [e.clientX, e.clientY]; draw();
    });
    cv.addEventListener("pointerup", () => (drag = null)); cv.addEventListener("pointercancel", () => (drag = null));
  }
  $("inv").addEventListener("input", () => { st.inv = +$("inv").value; $("invo").textContent = Math.round(st.inv * 100) + " %"; draw(); });
  for (const id of ["kx", "ky", "kz", "t"]) $(id).addEventListener("input", update);
  function cube() {
    const Ns = [+$("nx").value, +$("ny").value, +$("nz").value], I = C.cubeInfo(Ns);
    ["x", "y", "z"].forEach((a, j) => ($("vn" + a).textContent = Ns[j]));
    $("r8").innerHTML = ["x", "y", "z"].map((a, j) => `eje ${a}: N = <b>${Ns[j]}</b> · C = <b>${I.C[j].toFixed(6)}</b> · δ = ` +
      (I.sat[j] ? `<b class="ok">0 (satura)</b>` : `<b class="hot">${I.delta[j].toExponential(3)} &gt; 0 (estricto)</b>`)).join("<br>") +
      `<br>cuanto volumétrico δδδ = <b>${I.vol === 0 ? "0" : I.vol.toExponential(3)}</b> · C<sub>N</sub><sup>∞</sup> = ${C.CINF.toFixed(6)} (no se alcanza)`;
    draw();
  }
  for (const id of ["nx", "ny", "nz"]) $(id).addEventListener("input", cube);
  $("onda").addEventListener("click", () => { st.estado = "onda"; update(); });
  $("alea").addEventListener("click", () => { st.estado = "aleatorio"; st.seed = (st.seed * 7919 + 13) % 100003; update(); });

  let last = 0;
  function loop(now) {
    if (st.spin && !document.hidden && now - last > 33) {
      st.yaw += 0.006; last = now; draw();
    }
    if (!document.hidden && now - (loop.g || 0) > 50) { loop.g = now; drawGallery(); }
    requestAnimationFrame(loop);
  }
  new MutationObserver(() => { draw(); drawGallery(); }).observe(document.documentElement, { attributes: true, attributeFilter: ["data-theme"] });
  matchMedia("(prefers-color-scheme: dark)").addEventListener("change", () => { draw(); drawGallery(); });
  addEventListener("resize", () => { draw(); drawGallery(); });

  pick(st.i); cube();
  requestAnimationFrame(loop);
})();
