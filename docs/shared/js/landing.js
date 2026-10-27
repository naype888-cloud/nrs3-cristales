// The living lattice of the landing. One Bravais lattice at a time (the fourteen in turn): the central
// site and its neighbours in orange, a few tracer sites carried through the origin by the inversion
// n ↦ −n. The lattice stays the same, because every Bravais lattice with one site per cell is
// centrosymmetric (PeriodicGraph.inversion_mem_symmetries). Click: next lattice. Drag: turn.
// Keys: ← → change the lattice. No dependencies beyond cristales-core.js and figures.js.
(() => {
  "use strict";
  const C = window.Cristales, F = window.Fig, P = F.DARK;
  const canvas = document.getElementById("crystal");
  if (!canvas || !canvas.getContext) return;
  const out = document.getElementById("readout"), cap = document.getElementById("cap"), dots = document.getElementById("dots");
  const still = matchMedia("(prefers-reduced-motion: reduce)");
  const LAT = C.LATTICES, STAY = 7000;

  let k = LAT.findIndex((l) => l.id === "cF"), t0 = performance.now(), yaw = 0.7, pitch = 0.42, spin = 0.00028;
  let dragging = false, moved = 0, lastX = 0, lastY = 0, running = false, tracers = [];

  function pickTracers() {
    // six sites on one side of the origin: the inversion carries them to the other side
    const S = F.scene(LAT[k], {}, 2), c = [];
    S.cells.forEach((n, i) => { if (i !== S.centre && n[0] + 2 * n[1] + 3 * n[2] > 0 && Math.abs(n[0]) + Math.abs(n[1]) + Math.abs(n[2]) <= 3) c.push(i); });
    c.sort(() => Math.random() - 0.5); tracers = c.slice(0, 6);
  }
  function label() {
    const l = LAT[k];
    out.innerHTML = `<b>${l.nombre}</b> · ${l.vecinos} vecinos · |G| = <b>${l.orden}</b> · ${l.holo}`;
    dots.querySelectorAll("button").forEach((b, i) => b.setAttribute("aria-current", i === k ? "true" : "false"));
  }
  function go(i) { k = (i + LAT.length) % LAT.length; t0 = performance.now(); pickTracers(); label(); if (!running) frame(performance.now()); }

  LAT.forEach((l, i) => {
    const b = document.createElement("button");
    b.type = "button"; b.title = l.nombre; b.setAttribute("aria-label", l.nombre); b.textContent = l.id;
    b.addEventListener("click", () => go(i)); dots.appendChild(b);
  });

  function frame(now) {
    const dt = (now - t0) / 1000;
    // fade in, inversion there, hold, inversion back, fade out
    const fadeIn = F.ease(dt / 0.7), fadeOut = 1 - F.ease((dt - (STAY / 1000 - 0.7)) / 0.7);
    const a0 = still.matches ? 1 : Math.max(0, Math.min(fadeIn, fadeOut));
    const go1 = F.ease((dt - 1.2) / 1.6), back = F.ease((dt - 4.0) / 1.6), inv = still.matches ? 0 : go1 - back;
    if (cap) cap.textContent = inv > 0.04 && inv < 0.96 ? "n ↦ −n · los sitios naranja cruzan el origen" : "n ↦ −n · la red no cambia";
    if (!dragging && !still.matches) yaw += spin * 16;
    F.drawLattice(canvas, { lat: LAT[k], p: {}, Rc: 2, yaw, pitch, pal: P, bonds: "all", tracers, inv, alpha: a0, fit: 0.4 });
    if (!still.matches && dt > STAY / 1000) go(k + 1);
  }
  function loop(now) { if (!running) return; frame(now); requestAnimationFrame(loop); }
  const start = () => { if (!running) { running = true; requestAnimationFrame(loop); } };
  const stop = () => { running = false; };

  canvas.addEventListener("pointerdown", (e) => { dragging = true; moved = 0; lastX = e.clientX; lastY = e.clientY; canvas.setPointerCapture(e.pointerId); });
  canvas.addEventListener("pointermove", (e) => {
    if (!dragging) return;
    yaw += (e.clientX - lastX) * 0.008; pitch = Math.max(-1.3, Math.min(1.3, pitch + (e.clientY - lastY) * 0.006));
    moved += Math.abs(e.clientX - lastX) + Math.abs(e.clientY - lastY); lastX = e.clientX; lastY = e.clientY;
    if (!running) frame(performance.now());
  });
  canvas.addEventListener("pointerup", () => { dragging = false; if (moved < 6) go(k + 1); });
  canvas.addEventListener("pointercancel", () => (dragging = false));
  canvas.addEventListener("keydown", (e) => {
    if (e.key === "ArrowRight") { go(k + 1); e.preventDefault(); } else if (e.key === "ArrowLeft") { go(k - 1); e.preventDefault(); }
  });
  document.addEventListener("visibilitychange", () => (document.hidden ? stop() : start()));
  new ResizeObserver(() => { if (!running) frame(performance.now()); }).observe(canvas);

  pickTracers(); label(); frame(performance.now());
  requestAnimationFrame(() => canvas.classList.add("ready"));
  if (!still.matches) start();

  // ---- the ticker of the results ------------------------------------------------------------------------
  const items = [...document.querySelectorAll(".ticker li")], bar = document.querySelector(".progress");
  if (!items.length) return;
  const TICK = 3800;
  let idx = 0, paused = false;
  function show(i) {
    items.forEach((li, n) => {
      li.classList.toggle("on", n === i); li.classList.toggle("off", n === idx && n !== i);
      li.querySelector("a").tabIndex = n === i ? 0 : -1; li.setAttribute("aria-hidden", n === i ? "false" : "true");
    });
    idx = i;
    if (bar) { bar.style.setProperty("--tick", TICK / 1000 + "s"); bar.classList.remove("run"); void bar.offsetWidth; bar.classList.add("run"); }
  }
  function tick() { if (!paused && !document.hidden) show((idx + 1) % items.length); setTimeout(tick, TICK); }
  const list = document.querySelector(".ticker");
  list.addEventListener("pointerenter", () => (paused = true));
  list.addEventListener("pointerleave", () => (paused = false));
  list.addEventListener("focusin", () => (paused = true));
  list.addEventListener("focusout", () => (paused = false));
  show(0);
  if (!still.matches) setTimeout(tick, TICK);
})();
