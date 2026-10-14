// NRS³ · Cristales — núcleo numérico, sin dependencias.
// Las redes, sus enlaces y los órdenes de sus grupos puntuales son los de Lean
// (rama mosaic-cristales del fork de Physlib). Lo demás es un modelo numérico.
(function (root) {
  "use strict";
  const S3 = Math.sqrt(3);

  // Vectores primitivos (cartesianos) de cada embebimiento de Lean.
  const V = {
    cub: (a, b, c) => [[a, 0, 0], [0, b, 0], [0, 0, c]],                    // orthorhombicVectors
    bcc: (a, b, c) => [[-a / 2, b / 2, c / 2], [a / 2, -b / 2, c / 2], [a / 2, b / 2, -c / 2]],
    fcc: (a, b, c) => [[0, b / 2, c / 2], [a / 2, 0, c / 2], [a / 2, b / 2, 0]],
    hex: (a, b, c) => [[a, 0, 0], [-a / 2, a * S3 / 2, 0], [0, 0, c]],      // hcpVectors
    base: (a, b, c) => [[a / 2, -b / 2, 0], [a / 2, b / 2, 0], [0, 0, c]],  // baseCentredVectors
  };

  // forma: qué longitudes son libres. valid: rango en que los enlaces son las primeras capas.
  const LATTICES = [
    { id: "cP", nombre: "Cúbica simple", familia: "cúbica", forma: "a", vec: V.cub,
      bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1]], orden: 48, def: [1, 1, 1],
      lema: "card_pointGroup_hypercubic 3", valid: () => null },
    { id: "cI", nombre: "Cúbica centrada en el cuerpo", familia: "cúbica", forma: "a", vec: V.bcc,
      bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 1]], orden: 48, def: [1, 1, 1],
      lema: "bcc_card_pointGroup", valid: () => null },
    { id: "cF", nombre: "Cúbica centrada en las caras", familia: "cúbica", forma: "a", vec: V.fcc,
      bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, -1, 0], [0, 1, -1], [-1, 0, 1]], orden: 48,
      def: [1, 1, 1], lema: "fcc_card_pointGroup", valid: () => null },
    { id: "tP", nombre: "Tetragonal simple", familia: "tetragonal", forma: "ac", vec: V.cub,
      bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 0], [1, -1, 0]], orden: 16, def: [1, 1, 1.2],
      lema: "tetragonal_card_pointGroup",
      valid: (a, b, c) => (a < c && c < a * Math.SQRT2) ? null : "se pide a < c < a√2" },
    { id: "tI", nombre: "Tetragonal centrada en el cuerpo", familia: "tetragonal", forma: "ac",
      vec: V.bcc, bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 1], [0, 1, 1], [1, 0, 1],
        [1, 1, 2], [-1, 1, 0]], orden: 16, def: [1, 1, 2],
      lema: "bodyCentredTetragonal_card_pointGroup",
      valid: (a, b, c) => (a * Math.SQRT2 < c && c < a * Math.sqrt(6)) ? null : "se pide a√2 < c < a√6" },
    { id: "hP", nombre: "Hexagonal", familia: "hexagonal", forma: "ac", vec: V.hex,
      bonds: [[1, 0, 0], [0, 1, 0], [1, 1, 0], [0, 0, 1]], orden: 24, def: [1, 1, 1.5],
      lema: "hexagonal_card_pointGroup",
      valid: (a, b, c) => (c < a * S3) ? null : "se pide c < a√3" },
    { id: "oP", nombre: "Ortorrómbica simple", familia: "ortorrómbica", forma: "abc", vec: V.cub,
      bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 0], [1, -1, 0], [2, 0, 0]], orden: 8,
      def: [3, 4, 7], lema: "orthorhombic_card_pointGroup", valid: () => null },
    { id: "oC", nombre: "Ortorrómbica centrada en la base", familia: "ortorrómbica", forma: "abc",
      vec: V.base, bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 0], [1, 2, 0], [2, 1, 0]],
      orden: 8, def: [3, 6, 5], lema: "baseCentredOrthorhombic_card_pointGroup", valid: () => null },
    { id: "oI", nombre: "Ortorrómbica centrada en el cuerpo", familia: "ortorrómbica", forma: "abc",
      vec: V.bcc, bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 1], [0, 1, 1], [0, 2, 2],
        [1, 1, 0]], orden: 8, def: [2, 7, 5], lema: "bodyCentredOrthorhombic_card_pointGroup",
      valid: () => null },
    { id: "oF", nombre: "Ortorrómbica centrada en las caras", familia: "ortorrómbica", forma: "abc",
      vec: V.fcc, bonds: [[1, 0, 0], [0, 1, 0], [0, 0, 1], [0, 1, -1], [1, -1, 0], [1, 0, -1],
        [1, -1, -1], [1, -1, -2], [2, -2, -1]], orden: 8, def: [2, 4, 5],
      lema: "faceCentredOrthorhombic_card_pointGroup", valid: () => null },
  ];
  // Pendientes (sin Lean todavía): se muestran apagadas.
  const PENDIENTES = ["Romboédrica", "Monoclínica simple", "Monoclínica centrada", "Triclínica"];

  function cart(vec, n) {
    return [0, 1, 2].map(j => n[0] * vec[0][j] + n[1] * vec[1][j] + n[2] * vec[2][j]);
  }
  function dot(u, v) { return u[0] * v[0] + u[1] * v[1] + u[2] * v[2]; }

  // Vectores de enlace con los dos signos, como `bondVectors` en Lean.
  function bondVectors(lat) {
    const out = [];
    for (const b of lat.bonds) { out.push(b); out.push(b.map(x => -x)); }
    return out;
  }

  // Generador pseudoaleatorio con semilla, para estados aleatorios reproducibles.
  function rng(seed) {
    let s = seed >>> 0 || 1;
    return () => { s ^= s << 13; s ^= s >>> 17; s ^= s << 5; return ((s >>> 0) / 4294967296); };
  }

  // La región Λ = {-L, …, L}³ en coordenadas de red: es simétrica, -Λ = Λ.
  function region(L) {
    const cells = [], index = new Map();
    for (let i = -L; i <= L; i++) for (let j = -L; j <= L; j++) for (let k = -L; k <= L; k++) {
      index.set(i + "," + j + "," + k, cells.length); cells.push([i, j, k]);
    }
    return { cells, index };
  }

  // Todo el cálculo de un estado: Σ, Ω de (H, X, Y, Z), la fórmula exacta y el límite.
  function compute(opts) {
    const { lat, a, b, c, L, kappa, estado, t = 1, seed = 7 } = opts;
    const vec = lat.vec(a, b, c);
    const { cells, index } = region(L);
    const N = cells.length;
    const pos = cells.map(n => cart(vec, n));
    const bv = bondVectors(lat);
    const bvc = bv.map(d => cart(vec, d));
    // vecinos dentro de la región
    const nb = cells.map(n => {
      const out = [];
      for (const d of bv) {
        const m = index.get((n[0] + d[0]) + "," + (n[1] + d[1]) + "," + (n[2] + d[2]));
        if (m !== undefined) out.push(m);
      }
      return out;
    });
    // k cartesiano: κ_j π / ℓ_j
    const ell = [a, b, c];
    const k = kappa.map((x, j) => x * Math.PI / ell[j]);
    // el estado
    const re = new Float64Array(N), im = new Float64Array(N);
    if (estado === "onda") {
      const s = 1 / Math.sqrt(N);
      for (let n = 0; n < N; n++) { const ph = dot(k, pos[n]); re[n] = s * Math.cos(ph); im[n] = s * Math.sin(ph); }
    } else {
      const r = rng(seed); let nn = 0;
      for (let n = 0; n < N; n++) {
        const ph = dot(k, pos[n]);
        const amp = 0.4 + r(); const ex = (r() - 0.5) * 2.4;
        re[n] = amp * Math.cos(ph + ex); im[n] = amp * Math.sin(ph + ex);
        nn += re[n] * re[n] + im[n] * im[n];
      }
      const s = 1 / Math.sqrt(nn);
      for (let n = 0; n < N; n++) { re[n] *= s; im[n] *= s; }
    }
    // operadores: H (salto -t) y X_j
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
    const u = ops.map(([or, oi], A) => [or.map((v, n) => v - mean[A] * re[n]), oi.map((v, n) => v - mean[A] * im[n])]);
    const Sig = [[], [], [], []], Om = [[], [], [], []];
    for (let A = 0; A < 4; A++) for (let B = 0; B < 4; B++) {
      // ⟪u_A, u_B⟫ = Σ conj(u_A) u_B
      let gr = 0, gi = 0;
      const [ar, ai] = u[A], [br, bi] = u[B];
      for (let n = 0; n < N; n++) { gr += ar[n] * br[n] + ai[n] * bi[n]; gi += ar[n] * bi[n] - ai[n] * br[n]; }
      Sig[A][B] = gr; Om[A][B] = gi;
    }
    // Fórmula exacta del lema (onda plana): -(t / 2|Λ|) Σ_enlaces r(δ) sin(k·δ)
    const exact = [0, 1, 2].map(j => {
      let s = 0;
      for (let n = 0; n < N; n++) for (const m of nb[n]) {
        const d = [pos[m][0] - pos[n][0], pos[m][1] - pos[n][1], pos[m][2] - pos[n][2]];
        s += d[j] * Math.sin(dot(k, d));
      }
      return -(t / (2 * N)) * s;
    });
    // Límite de cajas grandes: -½ velocidad de grupo, v_j = t Σ_δ δ_j sin(k·δ)
    const vel = [0, 1, 2].map(j => t * bvc.reduce((s, d) => s + d[j] * Math.sin(dot(k, d)), 0));
    const band = -t * bvc.reduce((s, d) => s + Math.cos(dot(k, d)), 0);
    return { N, pos, re, im, Sig, Om, exact, vel, band, k, bvc, vec, cells };
  }

  function det(M) {
    const n = M.length, A = M.map(r => r.slice()); let d = 1;
    for (let i = 0; i < n; i++) {
      let p = i; for (let r = i + 1; r < n; r++) if (Math.abs(A[r][i]) > Math.abs(A[p][i])) p = r;
      if (Math.abs(A[p][i]) < 1e-300) return 0;
      if (p !== i) { [A[p], A[i]] = [A[i], A[p]]; d = -d; }
      d *= A[i][i];
      for (let r = i + 1; r < n; r++) { const f = A[r][i] / A[i][i]; for (let cc = i; cc < n; cc++) A[r][cc] -= f * A[i][cc]; }
    }
    return d;
  }

  // Banda a lo largo de la dirección de k, s ∈ [-1, 1].
  function bandLine(lat, a, b, c, kappa, t = 1, n = 161) {
    const vec = lat.vec(a, b, c), bvc = bondVectors(lat).map(d => cart(vec, d)), ell = [a, b, c];
    const out = [];
    for (let i = 0; i < n; i++) {
      const s = -1 + 2 * i / (n - 1);
      const k = kappa.map((x, j) => s * x * Math.PI / ell[j]);
      out.push([s, -t * bvc.reduce((acc, d) => acc + Math.cos(dot(k, d)), 0)]);
    }
    return out;
  }

  const api = { LATTICES, PENDIENTES, compute, det, bandLine, bondVectors, cart };
  if (typeof module !== "undefined" && module.exports) module.exports = api; else root.Cristales = api;
})(typeof window !== "undefined" ? window : globalThis);
