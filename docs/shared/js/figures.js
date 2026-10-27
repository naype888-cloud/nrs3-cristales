// NRS³ · Cristales — figures. Canvas drawings shared by the landing, the didactic page, the formal note
// and the laboratory. Colour carries one meaning on every page:
//   blue = structure and covariance Σ · orange = the bracket Ω (flow) · green = a zero forced by symmetry
//   violet = group velocity · hue of a site = phase of the wave.
(function (root) {
  "use strict";
  const C = root.Cristales;
  const MONO = '"JetBrains Mono", ui-monospace, Menlo, Consolas, monospace';
  const SANS = 'system-ui, -apple-system, "Segoe UI", sans-serif';

  // the palette of the page the canvas lives in (read again after a theme change)
  function pal() {
    const s = getComputedStyle(document.documentElement), v = (n) => s.getPropertyValue(n).trim();
    return { bg: v("--bg"), panel: v("--panel"), ink: v("--ink"), ink2: v("--ink2"), muted: v("--muted"), grid: v("--grid"),
      blue: v("--blue"), orange: v("--orange"), green: v("--green"), violet: v("--violet"), red: v("--red") };
  }
  const DARK = { bg: "#06080b", panel: "#0d1520", ink: "#f2f1ee", ink2: "#c4c3bf", muted: "#8a8985", grid: "#1e2631",
    blue: "#5b9be6", orange: "#f08a5d", green: "#4fb37d", violet: "#a48bf0", red: "#f0605f" };

  function setup(cv) {
    const r = cv.getBoundingClientRect(), dpr = Math.min(window.devicePixelRatio || 1, 2);
    const w = Math.max(10, Math.round(r.width * dpr)), h = Math.max(10, Math.round(r.height * dpr));
    if (cv.width !== w) cv.width = w;
    if (cv.height !== h) cv.height = h;
    const g = cv.getContext("2d"); g.setTransform(dpr, 0, 0, dpr, 0, 0); g.clearRect(0, 0, r.width, r.height);
    return [g, r.width, r.height];
  }
  const rgba = (hex, a) => {
    const n = parseInt(hex.slice(1), 16);
    return `rgba(${n >> 16 & 255},${n >> 8 & 255},${n & 255},${a})`;
  };
  const ease = (x) => (x <= 0 ? 0 : x >= 1 ? 1 : x * x * (3 - 2 * x));
  const isDark = (P) => { const n = parseInt(P.bg.slice(1), 16); return 0.299 * (n >> 16 & 255) + 0.587 * (n >> 8 & 255) + 0.114 * (n & 255) < 128; };

  // ---- the scene of a lattice: the cells {−Rc…Rc}³, their positions and the bonds between them --------
  const cache = new Map();
  function scene(lat, p0, Rc) {
    const p = C.complete(lat, p0), key = lat.id + JSON.stringify(p) + Rc;
    if (cache.has(key)) return cache.get(key);
    const vec = lat.vec(p), n = 2 * Rc + 1, cells = [], idx = new Map();
    for (let i = -Rc; i <= Rc; i++) for (let j = -Rc; j <= Rc; j++) for (let k = -Rc; k <= Rc; k++) {
      idx.set(i + "," + j + "," + k, cells.length); cells.push([i, j, k]);
    }
    const pos = cells.map((c) => C.cart(vec, c));
    const edges = [];
    cells.forEach((c, a) => {
      for (const d of lat.bonds) {
        const b = idx.get((c[0] + d[0]) + "," + (c[1] + d[1]) + "," + (c[2] + d[2]));
        if (b !== undefined) edges.push([a, b]);
      }
    });
    const centre = idx.get("0,0,0"), cb = C.bondVectors(lat).map((d) => C.cart(vec, d));
    let ext = 1e-9; for (const q of pos) ext = Math.max(ext, Math.hypot(q[0], q[1], q[2]));
    const s = { cells, pos, edges, centre, cb, ext, n, p };
    if (cache.size > 40) cache.clear();
    cache.set(key, s); return s;
  }

  function rot(q, yaw, pitch) {
    const cy = Math.cos(yaw), sy = Math.sin(yaw), cp = Math.cos(pitch), sp = Math.sin(pitch);
    const x = cy * q[0] - sy * q[1], y = sy * q[0] + cy * q[1];
    return [x, cp * q[2] - sp * y, sp * q[2] + cp * y];
  }

  // o: {lat, p, Rc, yaw, pitch, pal, tracers:[cell index], inv:0…1, phase: R (compute result), bonds: "centre"|"all"|"none",
  //     fit: scale, alpha}
  function drawLattice(cv, o) {
    const [g, W, H] = setup(cv), P = o.pal || pal();
    const S = scene(o.lat, o.p || {}, o.Rc || 2);
    const sc = (o.fit || 0.42) * Math.min(W, H) / S.ext, cx = W / 2, cy = H / 2;
    const yaw = o.yaw || 0, pitch = o.pitch == null ? 0.4 : o.pitch;
    const proj = (q) => { const r = rot(q, yaw, pitch); return [cx + sc * r[0], cy - sc * r[1], r[2]]; };
    const depth = (z) => 0.32 + 0.68 * (0.5 + 0.5 * Math.tanh(z / (S.ext * 0.9)));
    const bonds = o.bonds || "centre", a0 = o.alpha == null ? 1 : o.alpha;
    const tr = new Set(o.tracers || []), s = ease(o.inv || 0);
    const at = (i) => {
      const q = S.pos[i];
      return tr.has(i) ? [q[0] * (1 - 2 * s), q[1] * (1 - 2 * s), q[2] * (1 - 2 * s)] : q;
    };
    const pts = S.pos.map((_, i) => proj(at(i)));
    if (bonds === "all") {
      g.lineWidth = 1; g.lineCap = "round";
      for (const [a, b] of S.edges) {
        const z = (pts[a][2] + pts[b][2]) / 2;
        g.strokeStyle = rgba(P.blue, 0.10 + 0.26 * depth(z) * a0);
        g.beginPath(); g.moveTo(pts[a][0], pts[a][1]); g.lineTo(pts[b][0], pts[b][1]); g.stroke();
      }
    }
    const o0 = proj([0, 0, 0]);
    if (bonds !== "none") {
      g.lineWidth = 2; g.strokeStyle = rgba(P.orange, 0.92 * a0); g.lineCap = "round";
      for (const d of S.cb) { const q = proj(d); g.beginPath(); g.moveTo(o0[0], o0[1]); g.lineTo(q[0], q[1]); g.stroke(); }
    }
    const order = pts.map((q, i) => [q[2], i]).sort((u, v) => u[0] - v[0]);
    const centreNb = new Set();
    if (bonds !== "none") for (const d of S.cb) centreNb.add(d.map((x) => x.toFixed(6)).join());
    for (const [z, i] of order) {
      const q = pts[i], d = depth(z), isC = i === S.centre;
      const isN = centreNb.has(S.pos[i].map((x) => x.toFixed(6)).join());
      let r = Math.max(1.5, Math.min(7, 0.012 * Math.min(W, H) * (0.7 + 0.5 * d))), col = P.blue, al = (0.25 + 0.65 * d) * a0;
      if (o.phase) {
        const ph = Math.atan2(o.phase.im[i], o.phase.re[i]), amp = (o.phase.re[i] ** 2 + o.phase.im[i] ** 2) * o.phase.N;
        r = Math.max(1.5, Math.min(8, 0.0075 * Math.min(W, H) * (1.5 + 0.9 * Math.sqrt(amp))));
        col = null; g.fillStyle = `hsla(${(ph * 180 / Math.PI + 360) % 360}, 68%, ${isDark(P) ? 62 : 46}%, ${al})`;
      }
      if (tr.has(i)) { col = P.orange; al = a0; r *= 1.5; }
      if (isN && bonds !== "none") { col = P.orange; al = a0; r *= 1.25; }
      if (isC) { col = P.ink; al = a0; r *= 1.7; }
      if (col) g.fillStyle = rgba(col, al);
      g.beginPath(); g.arc(q[0], q[1], r, 0, 2 * Math.PI); g.fill();
    }
    return { W, H, S };
  }

  // ---- the matrices Σ and Ω of (H, X, Y, Z) ---------------------------------------------------------
  function drawMats(cv, R, o) {
    const [g, W, H] = setup(cv), P = o.pal || pal(), onda = o.estado === "onda";
    const lab = ["H", "X", "Y", "Z"], gap = Math.max(18, W * 0.05), size = Math.min((W - gap - 44) / 2, H - 56), cell = size / 4;
    const x00 = (W - (2 * size + gap)) / 2;
    [["Σ · covarianzas", R.Sig, true], ["Ω · corchetes", R.Om, false]].forEach(([name, M, sym], m) => {
      const x0 = x00 + m * (size + gap), y0 = 34;
      let mx = 1e-12; for (const r of M) for (const v of r) mx = Math.max(mx, Math.abs(v));
      g.fillStyle = P.ink2; g.font = `600 12px ${MONO}`; g.textAlign = "left"; g.fillText(name, x0, 18);
      g.font = `11px ${MONO}`;
      for (let i = 0; i < 4; i++) {
        g.fillStyle = P.muted; g.textAlign = "right"; g.fillText(lab[i], x0 - 6, y0 + cell * (i + 0.6));
        g.textAlign = "center"; g.fillText(lab[i], x0 + cell * (i + 0.5), y0 + size + 15);
        for (let j = 0; j < 4; j++) {
          const v = M[i][j], z = Math.abs(v) < 1e-10;
          // forced zeros: Ω on the diagonal and between positions (they commute); Σ_HX on a symmetric state
          const forced = z && ((!sym && (i === j || (i > 0 && j > 0))) || (sym && onda && (i === 0) !== (j === 0)));
          const col = v >= 0 ? P.blue : P.orange, w = forced ? 0.16 : 0.1 + 0.8 * Math.abs(v) / mx;
          g.fillStyle = rgba(forced ? P.green : col, w);
          g.beginPath(); g.roundRect(x0 + j * cell + 1.5, y0 + i * cell + 1.5, cell - 3, cell - 3, 4); g.fill();
          if (forced) { g.strokeStyle = rgba(P.green, 0.7); g.lineWidth = 1; g.stroke(); }
          g.fillStyle = forced ? P.green : P.ink; g.textAlign = "center";
          g.font = `${forced ? "600 " : ""}${Math.max(9, Math.min(12, cell / 4.2))}px ${MONO}`;
          const txt = z ? "0" : (Math.abs(v) >= 100 ? v.toFixed(0) : Math.abs(v) >= 10 ? v.toFixed(1) : v.toFixed(2));
          g.fillText(txt, x0 + j * cell + cell / 2, y0 + i * cell + cell / 2 + 4);
        }
      }
    });
    g.textAlign = "left";
  }

  // ---- the band along the direction of κ, with the group velocity as its slope --------------------------
  function drawBand(cv, R, o) {
    const [g, W, H] = setup(cv), P = o.pal || pal(), lat = o.lat;
    const line = C.bandLine(lat, R.p, o.kappa, o.t);
    let lo = Infinity, hi = -Infinity; for (const [, e] of line) { lo = Math.min(lo, e); hi = Math.max(hi, e); }
    if (hi - lo < 1e-9) { hi += 1; lo -= 1; }
    const px = 46, py = 22, w = W - px - 16, h = H - py - 30;
    const X = (s) => px + (s + 1) / 2 * w, Y = (e) => py + (hi - e) / (hi - lo) * h;
    g.strokeStyle = P.grid; g.lineWidth = 1; g.strokeRect(px, py, w, h);
    g.beginPath(); g.moveTo(X(0), py); g.lineTo(X(0), py + h); g.stroke();
    g.fillStyle = P.muted; g.font = `11px ${MONO}`; g.textAlign = "right";
    g.fillText(hi.toFixed(1), px - 6, py + 9); g.fillText(lo.toFixed(1), px - 6, py + h);
    g.textAlign = "center"; g.fillText("−κ", px, H - 10); g.fillText("0", X(0), H - 10); g.fillText("+κ", px + w, H - 10);
    g.textAlign = "left"; g.fillText("ε(k)", px + 6, py + 14);
    g.strokeStyle = P.blue; g.lineWidth = 2; g.beginPath();
    line.forEach(([s, e], i) => i ? g.lineTo(X(s), Y(e)) : g.moveTo(X(s), Y(e))); g.stroke();
    const k = R.k, kh = Math.hypot(k[0], k[1], k[2]);
    if (kh > 1e-9) {
      const slope = (R.vel[0] * k[0] + R.vel[1] * k[1] + R.vel[2] * k[2]) / kh;   // v along k
      const e1 = R.band, ds = 0.4, de = slope * kh * ds;
      g.strokeStyle = P.violet; g.lineWidth = 2; g.beginPath(); g.moveTo(X(1 - ds), Y(e1 - de)); g.lineTo(X(1), Y(e1)); g.stroke();
      g.fillStyle = P.violet; g.beginPath(); g.arc(X(1), Y(e1), 4.5, 0, 2 * Math.PI); g.fill();
      return slope;
    }
    g.fillStyle = P.violet; g.beginPath(); g.arc(X(1), Y(R.band), 4.5, 0, 2 * Math.PI); g.fill();
    return 0;
  }

  // ---- Ω_HX(L) of the box and its limit −½ v ------------------------------------------------------------
  function drawConv(cv, series, limit, o) {
    const [g, W, H] = setup(cv), P = o.pal || pal();
    const cols = [P.blue, P.orange, P.violet], names = ["Ω_HX", "Ω_HY", "Ω_HZ"];
    let lo = Infinity, hi = -Infinity;
    for (const [, v] of series) for (const x of v) { lo = Math.min(lo, x); hi = Math.max(hi, x); }
    for (const x of limit) { lo = Math.min(lo, x); hi = Math.max(hi, x); }
    lo = Math.min(lo, 0); hi = Math.max(hi, 0);
    const padv = (hi - lo) * 0.08 || 1; lo -= padv; hi += padv;
    const px = 46, py = 18, w = W - px - 56, h = H - py - 30, n = series.length;
    const X = (L) => px + (L - 1) / (n - 1) * w, Y = (e) => py + (hi - e) / (hi - lo) * h;
    g.strokeStyle = P.grid; g.lineWidth = 1; g.strokeRect(px, py, w, h);
    g.beginPath(); g.moveTo(px, Y(0)); g.lineTo(px + w, Y(0)); g.stroke();
    g.fillStyle = P.muted; g.font = `11px ${MONO}`; g.textAlign = "right";
    g.fillText(hi.toFixed(2), px - 6, py + 9); g.fillText(lo.toFixed(2), px - 6, py + h);
    g.textAlign = "center";
    for (let L = 1; L <= n; L += n > 8 ? 2 : 1) g.fillText(String(L), X(L), H - 10);
    g.textAlign = "left"; g.fillText("L", px + w + 6, H - 10);
    const live = [0, 1, 2].filter((j) => series.some(([, v]) => Math.abs(v[j]) > 1e-9) || Math.abs(limit[j]) > 1e-9);
    for (const j of live) {
      g.strokeStyle = rgba(cols[j], 0.55); g.setLineDash([5, 4]); g.lineWidth = 1.5;
      g.beginPath(); g.moveTo(px, Y(limit[j])); g.lineTo(px + w, Y(limit[j])); g.stroke(); g.setLineDash([]);
      g.strokeStyle = cols[j]; g.lineWidth = 2; g.beginPath();
      series.forEach(([L, v], i) => i ? g.lineTo(X(L), Y(v[j])) : g.moveTo(X(L), Y(v[j]))); g.stroke();
      g.fillStyle = cols[j];
      series.forEach(([L, v]) => { g.beginPath(); g.arc(X(L), Y(v[j]), 2.6, 0, 2 * Math.PI); g.fill(); });
      g.font = `11px ${MONO}`; g.fillText(names[j], px + w + 6, Y(limit[j]) + 4);
    }
    if (!live.length) { g.fillStyle = P.green; g.fillText("Ω_H· = 0 en toda caja: k fija la inversión", px + 10, Y(0) - 8); }
  }


  // ---- C_Nava(N): 1 at N = 2, 3, strictly above 1 from N = 4, rising to C∞ without reaching it --------------
  function drawCN(cv, Ns, o) {
    const [g, W, H] = setup(cv), P = o.pal || pal(), Nmax = o.Nmax || 40, CI = C.CINF;
    const px = 52, py = 20, w = W - px - 64, h = H - py - 32, lo = 0.98, hi = CI + 0.02;
    const X = (n) => px + (n - 2) / (Nmax - 2) * w, Y = (c) => py + (hi - c) / (hi - lo) * h;
    g.strokeStyle = P.grid; g.lineWidth = 1; g.strokeRect(px, py, w, h);
    g.beginPath(); g.moveTo(px, Y(1)); g.lineTo(px + w, Y(1)); g.stroke();
    g.fillStyle = P.muted; g.font = `11px ${MONO}`; g.textAlign = "right";
    g.fillText("1", px - 6, Y(1) + 4); g.fillText(CI.toFixed(4), px - 6, Y(CI) + 4);
    g.textAlign = "center";
    for (let n = 2; n <= Nmax; n += n < 10 ? 2 : 10) g.fillText(String(n), X(n), H - 12);
    g.textAlign = "left"; g.fillText("N", px + w + 6, H - 12);
    g.strokeStyle = rgba(P.violet, 0.6); g.setLineDash([5, 4]); g.beginPath(); g.moveTo(px, Y(CI)); g.lineTo(px + w, Y(CI)); g.stroke(); g.setLineDash([]);
    g.fillStyle = P.violet; g.fillText("C∞ (no se alcanza)", px + w - 118, Y(CI) - 6);
    g.strokeStyle = P.blue; g.lineWidth = 2; g.beginPath();
    for (let n = 2; n <= Nmax; n++) { const x = X(n), y = Y(C.cNava(n)); n === 2 ? g.moveTo(x, y) : g.lineTo(x, y); }
    g.stroke();
    g.fillStyle = P.green; g.fillRect(X(2) - 3, Y(1) - 3, 6, 6); g.fillRect(X(3) - 3, Y(1) - 3, 6, 6);
    g.fillText("N = 2, 3: C = 1 (satura)", X(2) + 8, Y(1) - 8);
    const cols = [P.blue, P.orange, P.violet], names = ["x", "y", "z"];
    Ns.forEach((n, j) => {
      const nn = Math.min(n, Nmax), x = X(nn), y = Y(C.cNava(n));
      g.strokeStyle = cols[j]; g.lineWidth = 1.5; g.beginPath(); g.moveTo(x, y); g.lineTo(x, py + h); g.stroke();
      g.fillStyle = cols[j]; g.beginPath(); g.arc(x, y, 5, 0, 2 * Math.PI); g.fill();
      g.fillText(names[j], x + 7, y - 7 - 11 * j);
    });
  }

  // ---- the open cube of Nx × Ny × Nz sites: an axis that saturates (N ≤ 3) in green, a strict one (N ≥ 4) in violet --
  function drawBox(cv, Ns, o) {
    const [g, W, H] = setup(cv), P = o.pal || pal(), M = Ns.map((n) => Math.min(n, 12));
    const pts = [], idx = (i, j, k) => (i * M[1] + j) * M[2] + k;
    const q = (i, j, k) => [(i - (M[0] - 1) / 2), (j - (M[1] - 1) / 2), (k - (M[2] - 1) / 2)];
    const ext = Math.max(M[0], M[1], M[2]) * 0.9, sc = 0.42 * Math.min(W, H) / ext, cx = W / 2, cy = H / 2;
    const proj = (p) => { const r = rot(p, o.yaw || 0.6, o.pitch == null ? 0.45 : o.pitch); return [cx + sc * r[0], cy - sc * r[1], r[2]]; };
    for (let i = 0; i < M[0]; i++) for (let j = 0; j < M[1]; j++) for (let k = 0; k < M[2]; k++) pts[idx(i, j, k)] = proj(q(i, j, k));
    const col = (a) => (Ns[a] <= 3 ? P.green : P.violet);
    g.lineWidth = 1.1;
    for (let i = 0; i < M[0]; i++) for (let j = 0; j < M[1]; j++) for (let k = 0; k < M[2]; k++) {
      const a = pts[idx(i, j, k)], nb = [[i + 1, j, k, 0], [i, j + 1, k, 1], [i, j, k + 1, 2]];
      for (const [ii, jj, kk, ax] of nb) {
        if (ii >= M[0] || jj >= M[1] || kk >= M[2]) continue;
        const b = pts[idx(ii, jj, kk)];
        g.strokeStyle = rgba(col(ax), 0.45); g.beginPath(); g.moveTo(a[0], a[1]); g.lineTo(b[0], b[1]); g.stroke();
      }
    }
    const ord = pts.map((p, n) => [p[2], n]).sort((u, v) => u[0] - v[0]);
    for (const [, n] of ord) { const p = pts[n]; g.fillStyle = rgba(P.ink, 0.7); g.beginPath(); g.arc(p[0], p[1], 2.4, 0, 2 * Math.PI); g.fill(); }
    if (Ns.some((n) => n > 12)) { g.fillStyle = P.muted; g.font = `11px ${MONO}`; g.fillText("se dibujan a lo más 12 sitios por eje", 10, H - 10); }
  }

  root.Fig = { pal, DARK, setup, scene, rot, drawLattice, drawMats, drawBand, drawConv, drawCN, drawBox, rgba, ease, MONO, SANS };
})(window);
