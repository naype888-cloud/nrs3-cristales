// NRS³ · Cristales — numerical core, no dependencies.
// The lattices, their bonds and the orders of their point groups are those of the Lean statements
// (PhyslibAlpha). Everything else in this file is a numerical model of those statements.
(function (root) {
  "use strict";
  const S3 = Math.sqrt(3);

  // Primitive vectors (Cartesian) of each Lean embedding. p = {a, b, c, u, v, w}.
  const V = {
    cub: (p) => [[p.a, 0, 0], [0, p.b, 0], [0, 0, p.c]],                                  // orthorhombicVectors
    bcc: (p) => [[-p.a / 2, p.b / 2, p.c / 2], [p.a / 2, -p.b / 2, p.c / 2], [p.a / 2, p.b / 2, -p.c / 2]],
    fcc: (p) => [[0, p.b / 2, p.c / 2], [p.a / 2, 0, p.c / 2], [p.a / 2, p.b / 2, 0]],
    hex: (p) => [[p.a, 0, 0], [-p.a / 2, p.a * S3 / 2, 0], [0, 0, p.c]],                  // hcpVectors
    base: (p) => [[p.a / 2, -p.b / 2, 0], [p.a / 2, p.b / 2, 0], [0, 0, p.c]],            // baseCentredVectors
    rho: (p) => [[p.a, p.b, p.b], [p.b, p.a, p.b], [p.b, p.b, p.a]],                      // rhombohedralVectors p q
    mon: (p) => [[p.a, 0, 0], [0, p.b, 0], [p.w, 0, p.c]],                                // monoclinicVectors
    monC: (p) => [[p.a / 2, -p.b / 2, 0], [p.a / 2, p.b / 2, 0], [p.w, 0, p.c]],          // baseCentredMonoclinicVectors
    tri: (p) => [[p.a, 0, 0], [p.u, p.b, 0], [p.w, p.v, p.c]],                            // triclinicVectors
  };

  const PR = (n) => "https://github.com/leanprover-community/physlib/pull/" + n;
  const sl = (key, label, min, max, step) => ({ key, label, min, max, step });
  const A = sl("a", "a", 0.6, 2, 0.01), B = sl("b", "b", 0.6, 2, 0.01), C = sl("c", "c", 0.6, 2.4, 0.01);

  // sliders: the free lengths of the family. fill(p) completes the dependent ones.
  // valid(p): null, or the reason the Lean bonds stop being the nearest shells
  // (the graph does not change, and neither do the lemmas; only the geometry).
  const L = (o) => Object.assign({ valid: () => null, ell: (p) => [p.a, p.b, p.c] }, o);
  const eqAll = (p) => Object.assign({}, p, { b: p.a, c: p.a });
  const eqAB = (p) => Object.assign({}, p, { b: p.a });

  const LATTICES = [
    L({ id: "aP", nombre: "Triclínica", sistema: "Triclínico", holo: "Ci = −1", orden: 2,
      vec: V.tri, bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [2, 0, 0], [1, 1, 0], [1, -1, 0], [1, 0, -1], [0, 1, -1]],
      sliders: [sl("a", "a", 2, 4, 0.01), sl("b", "b₂", 2, 5, 0.01), sl("c", "c₃", 2, 6, 0.01),
        sl("u", "b₁", -1.5, 2.5, 0.01), sl("v", "c₂", -1.5, 2.5, 0.01), sl("w", "c₁", -1.5, 2.5, 0.01)],
      def: { a: 3, b: 4, c: 5, u: 1, v: 1, w: 1 }, fill: (p) => p,
      lema: "triclinic_card_pointGroup", grafo: "triclinic_neighbors_card", st: { k: "alpha", pr: 1825 } }),
    L({ id: "mP", nombre: "Monoclínica simple", sistema: "Monoclínico", holo: "C₂h = 2/m", orden: 4,
      vec: V.mon, bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 0, 1], [1, 0, -1], [2, 0, -1], [1, 1, 0], [1, -1, 0],
        [0, 1, 1], [0, 1, -1]],
      sliders: [sl("a", "a", 2, 4, 0.01), sl("b", "b", 2, 6, 0.01), sl("c", "c₃", 2, 5, 0.01), sl("w", "c₁", -2, 2, 0.01)],
      def: { a: 3, b: 5, c: 3, u: 0, v: 0, w: 1 }, fill: (p) => p,
      lema: "monoclinic_card_pointGroup", grafo: "monoclinic_neighbors_card", st: { k: "alpha", pr: 1825 } }),
    L({ id: "mC", nombre: "Monoclínica centrada en la base", sistema: "Monoclínico", holo: "C₂h = 2/m", orden: 4,
      vec: V.monC, bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, -1, 0], [2, -1, 0], [1, -2, 0], [1, 0, -1], [0, 1, -1]],
      sliders: [sl("a", "a", 2, 6, 0.01), sl("b", "b", 1, 4, 0.01), sl("c", "c₃", 2, 5, 0.01), sl("w", "c₁", -2, 2, 0.01)],
      def: { a: 4, b: 2, c: 3, u: 0, v: 0, w: 1 }, fill: (p) => p,
      lema: "baseCentredMonoclinic_card_pointGroup", grafo: "baseCentredMonoclinic_neighbors_card",
      st: { k: "alpha", pr: 1825 } }),
    L({ id: "oP", nombre: "Ortorrómbica simple", sistema: "Ortorrómbico", holo: "D₂h = mmm", orden: 8,
      vec: V.cub, bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 0], [1, -1, 0], [2, 0, 0]],
      sliders: [sl("a", "a", 2, 5, 0.01), sl("b", "b", 2, 6, 0.01), sl("c", "c", 3, 8, 0.01)],
      def: { a: 3, b: 4, c: 7, u: 0, v: 0, w: 0 }, fill: (p) => p,
      lema: "orthorhombic_card_pointGroup", grafo: "orthorhombic_neighbors_card", st: { k: "alpha", pr: 1802 } }),
    L({ id: "oC", nombre: "Ortorrómbica centrada en la base", sistema: "Ortorrómbico", holo: "D₂h = mmm", orden: 8,
      vec: V.base, bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 0], [1, 2, 0], [2, 1, 0]],
      sliders: [sl("a", "a", 2, 7, 0.01), sl("b", "b", 3, 8, 0.01), sl("c", "c", 2, 7, 0.01)],
      def: { a: 3, b: 6, c: 5, u: 0, v: 0, w: 0 }, fill: (p) => p,
      lema: "baseCentredOrthorhombic_card_pointGroup", grafo: "baseCentredOrthorhombic_neighbors_card",
      st: { k: "alpha", pr: 1802 } }),
    L({ id: "oI", nombre: "Ortorrómbica centrada en el cuerpo", sistema: "Ortorrómbico", holo: "D₂h = mmm", orden: 8,
      vec: V.bcc, bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 1], [0, 1, 1], [0, 2, 2], [1, 1, 0]],
      sliders: [sl("a", "a", 1.5, 4, 0.01), sl("b", "b", 4, 9, 0.01), sl("c", "c", 3, 8, 0.01)],
      def: { a: 2, b: 7, c: 5, u: 0, v: 0, w: 0 }, fill: (p) => p,
      lema: "bodyCentredOrthorhombic_card_pointGroup", grafo: "bodyCentredOrthorhombic_neighbors_card",
      st: { k: "alpha", pr: 1802 } }),
    L({ id: "oF", nombre: "Ortorrómbica centrada en las caras", sistema: "Ortorrómbico", holo: "D₂h = mmm", orden: 8,
      vec: V.fcc, bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [0, 1, -1], [1, -1, 0], [1, 0, -1], [1, -1, -1], [1, -1, -2],
        [2, -2, -1]],
      sliders: [sl("a", "a", 1.5, 4, 0.01), sl("b", "b", 3, 6, 0.01), sl("c", "c", 3, 7, 0.01)],
      def: { a: 2, b: 4, c: 5, u: 0, v: 0, w: 0 }, fill: (p) => p,
      lema: "faceCentredOrthorhombic_card_pointGroup", grafo: "faceCentredOrthorhombic_neighbors_card",
      st: { k: "alpha", pr: 1802 } }),
    L({ id: "tP", nombre: "Tetragonal simple", sistema: "Tetragonal", holo: "D₄h = 4/mmm", orden: 16,
      vec: V.cub, bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 0], [1, -1, 0]],
      sliders: [sl("a", "a", 0.6, 1.6, 0.01), sl("c", "c", 0.6, 2.4, 0.01)],
      def: { a: 1, b: 1, c: 1.2, u: 0, v: 0, w: 0 }, fill: eqAB,
      valid: (p) => (p.a < p.c && p.c < p.a * Math.SQRT2) ? null : "se pide a < c < a√2",
      lema: "tetragonal_card_pointGroup", grafo: "tetragonal_neighbors_card", st: { k: "alpha", pr: 1798 } }),
    L({ id: "tI", nombre: "Tetragonal centrada en el cuerpo", sistema: "Tetragonal", holo: "D₄h = 4/mmm", orden: 16,
      vec: V.bcc, bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 1], [0, 1, 1], [1, 0, 1], [1, 1, 2], [-1, 1, 0]],
      sliders: [sl("a", "a", 0.6, 1.6, 0.01), sl("c", "c", 0.6, 3, 0.01)],
      def: { a: 1, b: 1, c: 2, u: 0, v: 0, w: 0 }, fill: eqAB,
      valid: (p) => (p.a * Math.SQRT2 < p.c && p.c < p.a * Math.sqrt(6)) ? null : "se pide a√2 < c < a√6",
      lema: "bodyCentredTetragonal_card_pointGroup", grafo: "bodyCentredTetragonal_neighbors_card",
      st: { k: "alpha", pr: 1798 } }),
    L({ id: "hR", nombre: "Romboédrica", sistema: "Trigonal", holo: "D₃d = −3m", orden: 12,
      vec: V.rho, bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 0], [0, 1, 1], [1, 0, 1]],
      sliders: [sl("a", "p", 0.6, 1.6, 0.01), sl("b", "q", -0.3, 0.1, 0.005)],
      def: { a: 1, b: -0.1, c: 1, u: 0, v: 0, w: 0 }, fill: (p) => Object.assign({}, p, { c: p.a }),
      ell: (p) => [p.a, p.a, p.a],
      valid: (p) => {
        const r = p.b / p.a, cos = (2 * r + r * r) / (1 + 2 * r * r);
        if (p.a === p.b || p.a + 2 * p.b === 0) return "los vectores no son independientes";
        return (cos > -0.25 && cos < 0) ? null : "se pide −1/4 < cos α < 0 (aquí cos α = " + cos.toFixed(3) + ")";
      },
      lema: "rhombohedral_card_pointGroup", grafo: "rhombohedral_neighbors_card", st: { k: "alpha", pr: 1823 } }),
    L({ id: "hP", nombre: "Hexagonal", sistema: "Hexagonal", holo: "D₆h = 6/mmm", orden: 24,
      vec: V.hex, bonds: [[1, 0, 0], [0, 1, 0], [1, 1, 0], [0, 0, 1]],
      sliders: [sl("a", "a", 0.6, 1.6, 0.01), sl("c", "c", 0.6, 2.4, 0.01)],
      def: { a: 1, b: 1, c: 1.5, u: 0, v: 0, w: 0 }, fill: eqAB,
      valid: (p) => (p.c < p.a * S3) ? null : "se pide c < a√3",
      lema: "hexagonal_card_pointGroup", grafo: "hexagonal_neighbors_card", st: { k: "alpha", pr: 1798 } }),
    L({ id: "cP", nombre: "Cúbica simple", sistema: "Cúbico", holo: "Oh = m3m", orden: 48,
      vec: V.cub, bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1]],
      sliders: [sl("a", "a", 0.6, 1.6, 0.01)], def: { a: 1, b: 1, c: 1, u: 0, v: 0, w: 0 }, fill: eqAll,
      lema: "card_pointGroup_hypercubic", grafo: "hypercubicGraph", st: { k: "alpha", pr: null } }),
    L({ id: "cI", nombre: "Cúbica centrada en el cuerpo", sistema: "Cúbico", holo: "Oh = m3m", orden: 48,
      vec: V.bcc, bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 1]],
      sliders: [sl("a", "a", 0.6, 1.6, 0.01)], def: { a: 1, b: 1, c: 1, u: 0, v: 0, w: 0 }, fill: eqAll,
      lema: "bcc_card_pointGroup", grafo: "bccGraph", st: { k: "alpha", pr: null } }),
    L({ id: "cF", nombre: "Cúbica centrada en las caras", sistema: "Cúbico", holo: "Oh = m3m", orden: 48,
      vec: V.fcc, bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, -1, 0], [0, 1, -1], [-1, 0, 1]],
      sliders: [sl("a", "a", 0.6, 1.6, 0.01)], def: { a: 1, b: 1, c: 1, u: 0, v: 0, w: 0 }, fill: eqAll,
      lema: "fcc_card_pointGroup", grafo: "fccGraph", st: { k: "alpha", pr: null } }),
  ];
  for (const l of LATTICES) l.vecinos = 2 * l.bonds.length;

  const SISTEMAS = ["Triclínico", "Monoclínico", "Ortorrómbico", "Tetragonal", "Trigonal", "Hexagonal", "Cúbico"];

  const complete = (lat, p) => lat.fill(Object.assign({}, lat.def, p));
  const cart = (vec, n) => [0, 1, 2].map((j) => n[0] * vec[0][j] + n[1] * vec[1][j] + n[2] * vec[2][j]);
  const dot = (u, v) => u[0] * v[0] + u[1] * v[1] + u[2] * v[2];
  const bondVectors = (lat) => { const o = []; for (const b of lat.bonds) { o.push(b); o.push(b.map((x) => -x)); } return o; };

  // seeded generator: reproducible random states
  function rng(seed) {
    let s = seed >>> 0 || 1;
    return () => { s ^= s << 13; s ^= s >>> 17; s ^= s << 5; return (s >>> 0) / 4294967296; };
  }

  // the region Λ = {−L, …, L}³ in lattice coordinates: symmetric, −Λ = Λ
  function region(Lr) {
    const cells = [], index = new Map();
    for (let i = -Lr; i <= Lr; i++) for (let j = -Lr; j <= Lr; j++) for (let k = -Lr; k <= Lr; k++) {
      index.set(i + "," + j + "," + k, cells.length); cells.push([i, j, k]);
    }
    return { cells, index };
  }

  // the wave vector in Cartesian components: κ_j π / ℓ_j
  const kvec = (lat, p, kappa) => { const ell = lat.ell(p); return kappa.map((x, j) => x * Math.PI / ell[j]); };

  // the whole computation of a state: Σ and Ω of (H, X, Y, Z), the exact formula and the limit
  function compute(o) {
    const { lat, L: Lr, kappa, estado, t = 1, seed = 7 } = o;
    const p = complete(lat, o.p), vec = lat.vec(p);
    const { cells, index } = region(Lr);
    const N = cells.length, pos = cells.map((n) => cart(vec, n));
    const bv = bondVectors(lat), bvc = bv.map((d) => cart(vec, d));
    const nb = cells.map((n) => {
      const out = [];
      for (const d of bv) {
        const m = index.get((n[0] + d[0]) + "," + (n[1] + d[1]) + "," + (n[2] + d[2]));
        if (m !== undefined) out.push(m);
      }
      return out;
    });
    const k = kvec(lat, p, kappa);
    const re = new Float64Array(N), im = new Float64Array(N);
    if (estado === "onda") {
      const s = 1 / Math.sqrt(N);
      for (let n = 0; n < N; n++) { const ph = dot(k, pos[n]); re[n] = s * Math.cos(ph); im[n] = s * Math.sin(ph); }
    } else {
      const r = rng(seed); let nn = 0;
      for (let n = 0; n < N; n++) {
        const ph = dot(k, pos[n]), amp = 0.4 + r(), ex = (r() - 0.5) * 2.4;
        re[n] = amp * Math.cos(ph + ex); im[n] = amp * Math.sin(ph + ex); nn += re[n] * re[n] + im[n] * im[n];
      }
      const s = 1 / Math.sqrt(nn);
      for (let n = 0; n < N; n++) { re[n] *= s; im[n] *= s; }
    }
    const apply = (op) => {
      const or = new Float64Array(N), oi = new Float64Array(N);
      for (let n = 0; n < N; n++) {
        if (op === 0) { let sr = 0, si = 0; for (const m of nb[n]) { sr += re[m]; si += im[m]; } or[n] = -t * sr; oi[n] = -t * si; }
        else { const x = pos[n][op - 1]; or[n] = x * re[n]; oi[n] = x * im[n]; }
      }
      return [or, oi];
    };
    const ops = [0, 1, 2, 3].map(apply);
    const mean = ops.map(([or, oi]) => { let s = 0; for (let n = 0; n < N; n++) s += re[n] * or[n] + im[n] * oi[n]; return s; });
    const u = ops.map(([or, oi], A_) => [or.map((v, n) => v - mean[A_] * re[n]), oi.map((v, n) => v - mean[A_] * im[n])]);
    const Sig = [[], [], [], []], Om = [[], [], [], []];
    for (let a = 0; a < 4; a++) for (let b = 0; b < 4; b++) {
      let gr = 0, gi = 0;
      const [ar, ai] = u[a], [br, bi] = u[b];
      for (let n = 0; n < N; n++) { gr += ar[n] * br[n] + ai[n] * bi[n]; gi += ar[n] * bi[n] - ai[n] * br[n]; }
      Sig[a][b] = gr; Om[a][b] = gi;
    }
    const exact = exactOmega(lat, p, kappa, t, Lr);
    const vel = [0, 1, 2].map((j) => t * bvc.reduce((s, d) => s + d[j] * Math.sin(dot(k, d)), 0));
    const band = -t * bvc.reduce((s, d) => s + Math.cos(dot(k, d)), 0);
    return { N, pos, re, im, Sig, Om, exact, vel, band, k, bvc, vec, cells, p };
  }

  // exact Ω_HX for the plane wave on Λ: −(t / 2|Λ|) Σ_bonds r(δ) sin(k·δ)  (expectation_bracket_unitPlaneWave)
  function exactOmega(lat, p0, kappa, t, Lr) {
    const p = complete(lat, p0), vec = lat.vec(p), k = kvec(lat, p, kappa), bv = bondVectors(lat);
    const n = 2 * Lr + 1, N = n * n * n, s = [0, 0, 0];
    for (const d of bv) {
      // number of cells n in Λ with n + d in Λ, and the Cartesian bond vector
      let cnt = 1;
      for (let j = 0; j < 3; j++) cnt *= Math.max(0, n - Math.abs(d[j]));
      const dc = cart(vec, d), sn = Math.sin(dot(k, dc));
      for (let j = 0; j < 3; j++) s[j] += cnt * dc[j] * sn;
    }
    return s.map((x) => -(t / (2 * N)) * x);
  }

  // the group velocity −½ v: the limit of the box Ω_HX  (tendsto_expectation_bracket_box)
  function limitOmega(lat, p0, kappa, t) {
    const p = complete(lat, p0), vec = lat.vec(p), k = kvec(lat, p, kappa);
    const bvc = bondVectors(lat).map((d) => cart(vec, d));
    return [0, 1, 2].map((j) => -0.5 * t * bvc.reduce((s, d) => s + d[j] * Math.sin(dot(k, d)), 0));
  }

  function det(M) {
    const n = M.length, A_ = M.map((r) => r.slice()); let d = 1;
    for (let i = 0; i < n; i++) {
      let p = i; for (let r = i + 1; r < n; r++) if (Math.abs(A_[r][i]) > Math.abs(A_[p][i])) p = r;
      if (Math.abs(A_[p][i]) < 1e-300) return 0;
      if (p !== i) { [A_[p], A_[i]] = [A_[i], A_[p]]; d = -d; }
      d *= A_[i][i];
      for (let r = i + 1; r < n; r++) { const f = A_[r][i] / A_[i][i]; for (let cc = i; cc < n; cc++) A_[r][cc] -= f * A_[i][cc]; }
    }
    return d;
  }

  // the band ε(k) = −t Σ_δ cos(k·δ) along the direction of κ, s ∈ [−1, 1]
  function bandLine(lat, p0, kappa, t = 1, n = 161) {
    const p = complete(lat, p0), vec = lat.vec(p), bvc = bondVectors(lat).map((d) => cart(vec, d));
    const ell = lat.ell(p), out = [];
    for (let i = 0; i < n; i++) {
      const s = -1 + 2 * i / (n - 1), k = kappa.map((x, j) => s * x * Math.PI / ell[j]);
      out.push([s, -t * bvc.reduce((acc, d) => acc + Math.cos(dot(k, d)), 0)]);
    }
    return out;
  }

  // Ω_HX(L) for L = 1 … Lmax: the box approaches −½ v
  function convergence(lat, p, kappa, t, Lmax) {
    const out = [];
    for (let Lr = 1; Lr <= Lmax; Lr++) out.push([Lr, exactOmega(lat, p, kappa, t, Lr)]);
    return out;
  }

  // ---- the cube of N sites per axis: C_Nava(N), the excess δ and the volumetric quantum ------------------
  // C² has the closed form of uncertaintyRatio_sq_eq with θ = π/(N+1); C(N) = 1 exactly for N = 2, 3 (Robertson saturates)
  // and C(N) > 1 strictly for every N ≥ 4, increasing to C∞ = √(π²/3 − 2) without reaching it.
  const CINF = Math.sqrt(Math.PI * Math.PI / 3 - 2);
  function cNava(N) {
    if (N <= 3) return 1;
    const th = Math.PI / (N + 1), c2 = 2 * (N - 1) / ((N + 1) * Math.cos(th) ** 2) *
      (((N + 1) ** 2 + 2) / 6 * Math.sin(th) ** 2 - 1);
    return Math.sqrt(c2);
  }
  const cubeInfo = (Ns) => {
    const C_ = Ns.map(cNava), d = C_.map((c) => c - 1);
    return { C: C_, delta: d, vol: d[0] * d[1] * d[2], sat: Ns.map((n) => n <= 3) };
  };

  const api = { LATTICES, SISTEMAS, PR, complete, compute, exactOmega, limitOmega, convergence, det, bandLine,
    bondVectors, cart, kvec, dot, cNava, CINF, cubeInfo };
  if (typeof module !== "undefined" && module.exports) module.exports = api; else root.Cristales = api;
})(typeof window !== "undefined" ? window : globalThis);
