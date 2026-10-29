// Fills the two tables of docs/formal/index.html (the fourteen lattices, the ledger) from the numerical core,
// so that the page and the model cannot drift apart. Run: node tools/gen_formal_tables.js
const fs = require("fs"), path = require("path");
const C = require("../docs/shared/js/cristales-core.js");
const file = path.join(__dirname, "../docs/formal/index.html");
let html = fs.readFileSync(file, "utf8");

const PH = "https://github.com/leanprover-community/physlib/";
const FORK = "https://github.com/naype888-cloud/physlib/blob/";
const CORPUS = "https://github.com/naype888-cloud/nava-robertson-schrodinger/blob/main/";
const REPO = "https://github.com/naype888-cloud/nrs3-cristales/blob/main/";
const chip = (k, t, href) => `<span class="chip ${k}">${href ? `<a href="${href}">${t}</a>` : t}</span>`;
const st = {
  phys: (n) => chip("phys", "Physlib #" + n, PH + "pull/" + n),
  alpha: (...ns) => ns.map((n) => chip("alpha", "PhyslibAlpha #" + n, PH + "pull/" + n)).join(" "),
  alphaNoPr: () => chip("alpha", "PhyslibAlpha"),
  fork: (b) => chip("fork", "rama del fork", FORK.replace("/blob/", "/tree/") + b),
  repo: () => chip("pr", "este repo"),
};

const VEC = {
  aP: "(a,0,0) · (b₁,b₂,0) · (c₁,c₂,c₃)", mP: "(a,0,0) · (0,b,0) · (c₁,0,c₃)",
  mC: "(a/2,−b/2,0) · (a/2,b/2,0) · (c₁,0,c₃)", oP: "(a,0,0) · (0,b,0) · (0,0,c)",
  oC: "(a/2,−b/2,0) · (a/2,b/2,0) · (0,0,c)", oI: "(−a/2,b/2,c/2) · (a/2,−b/2,c/2) · (a/2,b/2,−c/2)",
  oF: "(0,b/2,c/2) · (a/2,0,c/2) · (a/2,b/2,0)", tP: "como oP con a = b", tI: "como oI con a = b",
  hR: "(p,q,q) · (q,p,q) · (q,q,p)", hP: "(a,0,0) · (−a/2,a√3/2,0) · (0,0,c)",
  cP: "como oP con a = b = c", cI: "como oI con a = b = c", cF: "como oF con a = b = c",
};
const stat = (l) => (l.st.pr ? st.alpha(l.st.pr) + (l.id === "mP" || l.id === "mC" || l.id === "aP" ? " " + chip("alpha", "#1896", PH + "pull/1896") : "") : st.alphaNoPr());

let rows = `<tr><th>sistema</th><th>red</th><th>vectores primitivos</th><th>enlaces ±, coord. de la red</th><th class="num">vec.</th><th class="num">|G|</th><th>holoedría</th><th>Lean</th><th>estado</th></tr>\n`;
for (const l of C.LATTICES) {
  rows += `<tr><td class="sys">${l.sistema}</td><td>${l.nombre} <code>${l.id}</code></td><td class="vec">${VEC[l.id]}</td>` +
    `<td class="vec">${l.bonds.map((b) => "(" + b.join(",") + ")").join(" ")}</td><td class="num">${l.vecinos}</td><td class="num">${l.orden}</td>` +
    `<td>${l.holo}</td><td><code>${l.lema}</code></td><td>${stat(l)}</td></tr>\n`;
}

const P = "PhyslibAlpha/";
const lg = [
  ["Bravais general: <code>Crystal.bravais d</code>, <code>Embedding.ofVectors</code>, llena el espacio ⇔ los vectores lo generan", "isSpaceFilling_ofVectors_iff, position_ofVectors", "Physlib/CondensedMatter/Crystal/Bravais/Basic.lean", PH + "blob/master/", st.phys(1961)],
  ["Las catorce redes: grafo, vecinos y orden del grupo puntual", "<code>*_neighbors_card</code>, <code>*_card_pointGroup</code> (§2)", P + "CondensedMatter/Crystal/PointGroup/", PH + "tree/master/", st.alpha(1798, 1802, 1823, 1825)],
  ["Grupos puntuales de cristales con varios sitios por celda (subredes)", "<code>pointGroupMulEquivOfLift</code>, <code>linear_mem_bondDifferences_iff</code>", P + "CondensedMatter/Crystal/PointGroup/", PH + "tree/master/", st.alpha(1826)],
  ["Diamante (orden 48) y panal (orden 12)", "diamond_card_pointGroup, honeycomb_card_pointGroup", P + "CondensedMatter/Crystal/PointGroup/DiamondHoneycomb.lean", FORK + "feat-physlibalpha-crystal-diamond-honeycomb/", st.fork("feat-physlibalpha-crystal-diamond-honeycomb")],
  ["Toda red con un sitio por celda es centrosimétrica", "PeriodicGraph.inversion_mem_symmetries", P + "CondensedMatter/Crystal/Inversion.lean", FORK + "mosaic-cristales/", st.fork("mosaic-cristales")],
  ["Inversión por inversión temporal: <i>f H f = H</i>, <i>f X f = −X</i>", "inversionReversal_hopping, inversionReversal_position", P + "CondensedMatter/Crystal/Inversion.lean", FORK + "mosaic-cristales/", st.fork("mosaic-cristales")],
  ["En toda onda plana, Σ<sub>HX</sub> = 0 en todas las direcciones", "covariance_hopping_position_unitPlaneWave", P + "CondensedMatter/Crystal/Inversion.lean", FORK + "mosaic-cristales/", st.fork("mosaic-cristales")],
  ["Estado simétrico ⇒ Σ<sub>AB</sub> = Ω<sub>AB</sub> = 0; con inversión temporal, Σ entre paridades, Ω dentro de una", "covariance_eq_zero_of_symm, expectation_bracket_eq_zero_of_symm, …_of_reverse", P + "ProbabilisticTheory/CStarAlgebra/SymmetricState.lean", FORK + "mosaic-cristales/", st.fork("mosaic-cristales")],
  ["Antiunitario <i>f∘f = id</i> que fija el estado: par e impar sin correlación", "covariance_ofVec_eq_zero_of_antiunitary", P + "ProbabilisticTheory/HilbertSpace/State/Antiunitary.lean", FORK + "mosaic-cristales/", st.fork("mosaic-cristales")],
  ["Grupo pequeño de <i>k</i>: ceros, esquinas de la zona e invariancia de Ω", "covariance_hopping_position_littleGroup, expectation_bracket_hopping_position_of_neg, …_comp_littleGroup", P + "CondensedMatter/Crystal/LittleGroup.lean", FORK + "mosaic-cristales/", st.fork("mosaic-cristales")],
  ["Red cuadrada, <i>k</i> en la diagonal: Ω<sub>HX</sub> = Ω<sub>HY</sub>", "NRS3Cristales.omega_diagonal", "NRS3Cristales/Diagonal.lean", REPO, st.repo()],
  ["Forma de covarianza, positividad, <i>R<sup>H</sup> M R = M</i>, Schur", "covarianceForm, posSemidef_covarianceMatrixForm, covarianceMatrixForm_eq_zero_of_irreducible", P + "ProbabilisticTheory/StarAlgebra/CovarianceForm.lean", PH + "blob/master/", st.alpha(1822)],
  ["Forma de <i>M</i> por sistema cristalino", "covarianceMatrixForm_monoclinic / _orthorhombic / _rhombohedral / _cubic / _rotation", P + "CondensedMatter/Crystal/CovarianceShape.lean", FORK + "feat-physlibalpha-crystal-covariance-shape/", st.fork("feat-physlibalpha-crystal-covariance-shape")],
  ["Ω exacta de la onda plana, la banda y el límite −½ ∂ε", "expectation_bracket_unitPlaneWave, band, hasDerivAt_band, tendsto_expectation_bracket_box", P + "CondensedMatter/Crystal/GroupVelocity.lean", FORK + "mosaic-cristales/", st.fork("mosaic-cristales")],
  ["Ehrenfest y deriva en cajas grandes", "hasDerivAt_expectation_heisenberg, tendsto_drift_box", P + "ProbabilisticTheory/HilbertSpace/Dynamics/Ehrenfest.lean", FORK + "mosaic-cristales/", st.fork("mosaic-cristales")],
  ["Robertson–Schrödinger y |det Ω| ≤ det Σ para estados de <i>⋆</i>-álgebras", "AlgState.robertson_schrodinger, AlgState.robertson_det", P + "ProbabilisticTheory/StarAlgebra/StateUncertainty.lean", PH + "blob/master/", st.alpha(1803)],
  ["Estado térmico invariante por traslación; traslación que fija <i>A</i> e invierte <i>B</i>", "robertson_det_translationInvariantState, covariance_translationInvariantState_eq_zero", P + "CondensedMatter/Crystal/InvariantStateUncertainty.lean", PH + "blob/master/", st.alpha(1803)],
  ["Cadena: cov(H, X) = 0 en el estado de corriente máxima (la prueba por simetría partícula–hueco está en la rama del fork)", "TightBindingChain.covariance_maxCurrentState", P + "CondensedMatter/TightBindingChain/MaxCurrentState/UncertaintyRatio.lean", PH + "blob/master/", st.alphaNoPr()],
  ["FCC y BCC como palabras de pasos de eje; complemento de Schur; tensión nula en la parte par", "det_sub_bipartita, schur_bipartita, palabras2_diagonalCara, palabras3_cuerpo, tension_parteFCC_eq_zero", "NRS3Cristales/Schur.lean · SchurCubo.lean", REPO, st.repo()],
  ["Forma cerrada de <i>C²</i> en el estado de corriente máxima, <i>θ = π/(N+1)</i>", "uncertaintyRatio_sq_eq", P + "CondensedMatter/TightBindingChain/MaxCurrentState/Variances.lean", PH + "blob/master/", st.alpha(1732)],
  ["<i>C = 1</i> ⇔ N = 2, 3; <i>C &gt; 1</i> estrictamente desde N = 4", "uncertaintyRatio_eq_one_iff, one_lt_uncertaintyRatio", P + "CondensedMatter/TightBindingChain/MaxCurrentState/UncertaintyRatio.lean", PH + "blob/master/", st.alpha(1723)],
  ["Saturación de Robertson–Schrödinger solo en N = 2, 3; estricta desde N = 4 (eje)", "centeredGramDefect_maxCurrentState_eq_zero_iff, robertson_schrodinger_maxCurrentState_lt", P + "CondensedMatter/TightBindingChain/MaxCurrentState/Saturation.lean", PH + "blob/master/", st.alpha(1718)],
  ["Cubo: cada eje con su <i>C</i>, ejes que conmutan, estricto desde 4 × 4 × 4, <i>det Σ = (C<sub>x</sub>C<sub>y</sub>C<sub>z</sub>)² |det Ω|</i>", "robertson_schrodinger_cube, bracketMatrix_cubePairs, det_covarianceMatrix_maxCurrentCubeState, robertson_det_maxCurrentCubeState_strict", P + "CondensedMatter/TightBindingChain/Cube/Basic.lean", PH + "blob/master/", st.alpha(1725, 1742)],
  ["Cuanto volumétrico <i>δ(Nx)δ(Ny)δ(Nz)</i>: nulo si algún eje tiene 2 o 3 sitios, positivo desde 4 × 4 × 4", "volQuantum_eq_zero_iff, volQuantum_pos", P + "CondensedMatter/TightBindingChain/Cube/VolumetricQuantum.lean", PH + "blob/master/", st.alpha(1756)],
  ["<i>C</i> estrictamente creciente desde N = 4 y por debajo de <i>C<sub>N</sub><sup>∞</sup></i> (Taylor y Bernstein)", "uncertaintyRatio_lt_uncertaintyRatio, uncertaintyRatioSqForm_strictMonoOn", P + "CondensedMatter/TightBindingChain/MaxCurrentState/LongChainMonotonicity.lean", PH + "blob/master/", st.alpha(1735)],
  ["Límite <i>C → C<sub>N</sub><sup>∞</sup> = √(π²/3 − 2)</i> (Szegő)", "tendsto_uncertaintyRatio, tendsto_uncertaintyRatioSqForm", P + "CondensedMatter/TightBindingChain/MaxCurrentState/LongChainLimit.lean", PH + "blob/master/", st.alpha(1734)],
  ["El paso de eje es estrictamente el más corto: 1 &lt; √2 &lt; √3; con un solo eje no hay diagonal", "OrthogonalStep.minimal_adjacency_is_orthogonal, DiagonalNeedsTwoAxes.no_diagonal_of_one_axis", "NavaRobertsonIndependent/Mathematics/D4_WhyNotDiagonal.lean", CORPUS, chip("pr", "corpus RS^N", "https://github.com/naype888-cloud/nava-robertson-schrodinger")],
  ["Banda del ángulo RS^N: <i>θ<sub>RS^N</sub>(4) ≤ θ<sub>RS^N</sub>(d) &lt; arccos(1/C<sub>N</sub><sup>∞</sup>)</i> para d ≥ 4", "SpectrumBounds.angleNRS_spectrum_bounds", "NavaRobertsonIndependent/Mathematics/D48_SpectrumBounds.lean", CORPUS, chip("pr", "corpus RS^N", "https://github.com/naype888-cloud/nava-robertson-schrodinger")],
];
let led = `<tr><th>enunciado</th><th>Lean</th><th>archivo</th><th>estado</th></tr>\n`;
for (const [q, l, f, base, s] of lg) {
  const fl = f.includes("/") && /\.lean$/.test(f) ? `<a href="${base}${f}">${f.split("/").pop()}</a>` : f.endsWith("/") ? `<a href="${base}${f}">${f}</a>` : f;
  led += `<tr><td>${q}</td><td><code>${l}</code></td><td>${fl}</td><td>${s}</td></tr>\n`;
}
const put = (tag, body) => { html = html.replace(new RegExp(`<!--${tag}:begin-->[\\s\\S]*?<!--${tag}:end-->`), `<!--${tag}:begin-->\n${body}<!--${tag}:end-->`); };
put("LT", rows); put("LG", led);
fs.writeFileSync(file, html);
console.log("tables written:", C.LATTICES.length, "lattices,", lg.length, "ledger rows");
