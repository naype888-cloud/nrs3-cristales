// The "Try it" of §5: Ω_HX of the box against its limit −½ v, for any of the fourteen lattices.
(() => {
  "use strict";
  const C = window.Cristales, F = window.Fig, $ = (id) => document.getElementById(id);
  const sel = $("tl");
  C.LATTICES.forEach((l, i) => { const o = document.createElement("option"); o.value = i; o.textContent = `${l.nombre} (${l.id})`; sel.appendChild(o); });
  sel.value = C.LATTICES.findIndex((l) => l.id === "cF");
  const fmt = (x) => (Math.abs(x) < 5e-12 ? "0" : x.toFixed(4));
  function update() {
    const l = C.LATTICES[+sel.value], kp = ["tkx", "tky", "tkz"].map((id) => +$(id).value);
    ["x", "y", "z"].forEach((a, j) => ($("tvk" + a).textContent = kp[j].toFixed(2)));
    const series = C.convergence(l, {}, kp, 1, 20), lim = C.limitOmega(l, {}, kp, 1);
    F.drawConv($("tc"), series, lim, { pal: F.pal() });
    const Ls = [1, 2, 3, 5, 10, 20];
    $("tt").innerHTML = `<tr><th>L</th><th class="num">Ω_HX</th><th class="num">Ω_HY</th><th class="num">Ω_HZ</th></tr>` +
      Ls.map((L) => `<tr><td>${L}</td>${series[L - 1][1].map((x) => `<td class="num">${fmt(x)}</td>`).join("")}</tr>`).join("") +
      `<tr><td><b>límite −½ v</b></td>${lim.map((x) => `<td class="num"><b>${fmt(x)}</b></td>`).join("")}</tr>`;
    $("tr").innerHTML = `Σ<sub>HX</sub> = Σ<sub>HY</sub> = Σ<sub>HZ</sub> = <b>0</b> en la onda plana de toda región simétrica (Teorema 3.3); |G| = ${l.orden}, ${l.vecinos} vecinos.`;
  }
  ["tl", "tkx", "tky", "tkz"].forEach((id) => $(id).addEventListener("input", update));
  new MutationObserver(update).observe(document.documentElement, { attributes: true, attributeFilter: ["data-theme"] });
  addEventListener("resize", update);
  update();
})();
