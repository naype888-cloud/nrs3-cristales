/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube.Basic

/-!
# Una palabra o dos, en el cubo

En el cubo `Tx × Ty × Tz` hay dos clases de pares `(A, B)`:

* **ejes distintos** (`A` en `x`, `B` en `y`): conmutan. `AB = BA` es un solo operador; sus dos
  caminos (`x` luego `y`, `y` luego `x`) llegan a la diagonal de cara. Una palabra, un enunciado.
* **el mismo eje** (`H` y `X` de una cadena, el par `T_d : P_d`): no conmutan. `HX` y `XH` son dos
  operadores distintos, el estado de corriente máxima los distingue, y la desigualdad elemental
  da incertidumbre positiva. Dos palabras, dos enunciados.

## Resultados principales

* `bracket_pares_ejes_distintos` : ejes distintos ⇒ conmutador `0`.
* `axisBracket_ne_zero` : en el estado de corriente máxima, `⟨⁅H, X⁆⟩ ≠ 0` en cada eje.
* `bracket_mismo_eje_ne_zero` : el conmutador de un eje no es cero.
* `bracket_eq_zero_iff_ejes_distintos` : para observables distintos, conmutan ⟺ ejes distintos.
* `uno_o_dos_palabras` : las tres afirmaciones juntas, más `0 < Var H · Var X` por eje.
-/

namespace NRS3Cristales

open ProbabilisticTheory ProbabilisticTheory.UnitalPositiveLinearMap CondensedMatter
open CondensedMatter.TightBindingChain
open scoped selfAdjoint

variable (Tx Ty Tz : CondensedMatter.TightBindingChain)

/-- **Una palabra**: observables de ejes distintos conmutan. -/
lemma bracket_pares_ejes_distintos {p q : Fin 2 × Fin 3} (h : p.2 ≠ q.2) :
    ⁅Tx.cubePairs Ty Tz p, Tx.cubePairs Ty Tz q⁆ = 0 :=
  Tx.bracket_cubePairs_of_ne Ty Tz h

variable {Tx Ty Tz}

/-- En el estado de corriente máxima del cubo, el valor esperado del conmutador de cada eje no
es cero. -/
lemma axisBracket_ne_zero (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 2 ≤ Tx.N) (hNy : 2 ≤ Ty.N) (hNz : 2 ≤ Tz.N) (k : Fin 3) :
    Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) k ≠ 0 := by
  have hP := Tx.sq_axisBracket_maxCurrentCubeState Ty Tz
  have hne : (Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 0 *
      Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 1 *
      Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 2) ≠ 0 := by
    intro h0
    rw [h0] at hP
    exact pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (Tx.bound_ne_zero hx hNx)
      (Ty.bound_ne_zero hy hNy)) (Tz.bound_ne_zero hz hNz)) (by simpa using hP.symm)
  intro hk
  fin_cases k <;> simp_all

/-- **Dos palabras**: los dos observables de un eje no conmutan. -/
lemma bracket_mismo_eje_ne_zero (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 2 ≤ Tx.N) (hNy : 2 ≤ Ty.N) (hNz : 2 ≤ Tz.N) (k : Fin 3) :
    ⁅Tx.cubePairs Ty Tz (0, k), Tx.cubePairs Ty Tz (1, k)⁆ ≠ 0 := by
  intro h
  apply axisBracket_ne_zero hx hy hz hNx hNy hNz k
  simp [axisBracket, h]

/-- **Una palabra o dos** en el cubo: ejes distintos conmutan; el par de un mismo eje no
conmuta, y por la desigualdad elemental su incertidumbre es positiva en el estado de corriente
máxima. -/
theorem uno_o_dos_palabras (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 2 ≤ Tx.N) (hNy : 2 ≤ Ty.N) (hNz : 2 ≤ Tz.N) :
    (∀ p q : Fin 2 × Fin 3, p.2 ≠ q.2 → ⁅Tx.cubePairs Ty Tz p, Tx.cubePairs Ty Tz q⁆ = 0) ∧
    (∀ k : Fin 3, ⁅Tx.cubePairs Ty Tz (0, k), Tx.cubePairs Ty Tz (1, k)⁆ ≠ 0) ∧
    (∀ k : Fin 3, 0 < variance (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.cubePairs Ty Tz (0, k)) *
      variance (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.cubePairs Ty Tz (1, k))) := by
  refine ⟨fun p q h => bracket_pares_ejes_distintos Tx Ty Tz h,
    bracket_mismo_eje_ne_zero hx hy hz hNx hNy hNz, fun k => ?_⟩
  have hb := axisBracket_ne_zero hx hy hz hNx hNy hNz k
  have hr := robertson (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.cubePairs Ty Tz (0, k))
    (Tx.cubePairs Ty Tz (1, k))
  exact lt_of_lt_of_le (by positivity) hr

/-- Intercambiar un conmutador cambia su signo. -/
private lemma bracket_swap {A : Type*} [CStarAlgebra A] (a b : Observable A) :
    ⁅b, a⁆ = -⁅a, b⁆ := by
  rw [selfAdjoint.bracket_def, selfAdjoint.lieMul_swap, ← selfAdjoint.bracket_def]

/-- **El iff sobre el cubo**: dos observables distintos del par de cada eje conmutan, es decir
`AB` y `BA` son una sola palabra, si y solo si están en ejes distintos. En el mismo eje son dos
palabras distintas. -/
theorem bracket_eq_zero_iff_ejes_distintos (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 2 ≤ Tx.N) (hNy : 2 ≤ Ty.N) (hNz : 2 ≤ Tz.N) {p q : Fin 2 × Fin 3} (h : p ≠ q) :
    ⁅Tx.cubePairs Ty Tz p, Tx.cubePairs Ty Tz q⁆ = 0 ↔ p.2 ≠ q.2 := by
  refine ⟨fun h0 hk => ?_, fun hk => bracket_pares_ejes_distintos Tx Ty Tz hk⟩
  obtain ⟨j, k⟩ := p
  obtain ⟨j', k'⟩ := q
  simp only at hk
  subst hk
  have hj : j ≠ j' := fun e => h (by rw [e])
  have hne := bracket_mismo_eje_ne_zero hx hy hz hNx hNy hNz k
  fin_cases j <;> fin_cases j' <;> simp at hj ⊢
  · exact hne h0
  · rw [bracket_swap] at h0; exact hne (neg_eq_zero.mp h0)

end NRS3Cristales
