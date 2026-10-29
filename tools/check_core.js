// Checks the numerical model of the site against the formulas of the Lean statements, for the fourteen lattices:
//   Σ_HX = 0 on every plane wave of a symmetric region (covariance_hopping_position_unitPlaneWave),
//   Ω_HX = the exact sum (expectation_bracket_unitPlaneWave), Robertson–Schrödinger, the box limit −½ v,
//   and C_N: = 1 for N = 2, 3; > 1 and increasing from N = 4; below C_N^∞.  Run: node tools/check_core.js
const C = require("../docs/shared/js/cristales-core.js");
let bad = 0;
const fail = (m) => { bad++; console.log("FAIL", m); };
for (const lat of C.LATTICES) {
  for (const kappa of [[0.37, -0.52, 0.61], [0.9, 0.1, -0.3], [0, 0, 0]]) {
    const R = C.compute({ lat, p: {}, L: 2, kappa, estado: "onda", t: 1 });
    for (let j = 1; j <= 3; j++) {
      if (Math.abs(R.Sig[0][j]) > 1e-10) fail(`${lat.id} Σ_H${j} ≠ 0`);
      if (Math.abs(R.Om[0][j] - R.exact[j - 1]) > 1e-10) fail(`${lat.id} Ω ≠ exact`);
      if (R.Sig[0][j] ** 2 + R.Om[0][j] ** 2 > R.Sig[0][0] * R.Sig[j][j] * (1 + 1e-9) + 1e-12) fail(`${lat.id} Robertson`);
      if (Math.abs(R.Om[j][1 + (j % 3)]) > 1e-10) fail(`${lat.id} positions do not commute`);
    }
    const conv = C.convergence(lat, {}, kappa, 1, 12), lim = C.limitOmega(lat, {}, kappa, 1);
    const err = (v) => Math.max(...v.map((x, j) => Math.abs(x - lim[j])));
    if (!(err(conv[11][1]) <= err(conv[0][1]) + 1e-12)) fail(`${lat.id} box does not approach the limit`);
  }
  if (lat.vecinos !== 2 * lat.bonds.length) fail(`${lat.id} neighbours`);
}
for (const N of [2, 3]) if (Math.abs(C.cNava(N) - 1) > 1e-12) fail(`C(${N}) ≠ 1`);
let prev = 1;
for (let N = 4; N <= 1e6; N = N < 60 ? N + 1 : N * 2) {
  const c = C.cNava(N);
  if (!(c > 1 && c < C.CINF && c >= prev)) fail(`C(${N}) = ${c}`);
  prev = c;
}
console.log(bad ? `${bad} failures` : `ok: ${C.LATTICES.length} lattices, C_N strictly in (1, C_N^∞) for N ≥ 4`);
process.exit(bad ? 1 : 0);
