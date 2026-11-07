/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import NRS3Cristales.Schur
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# La banda de FCC refinada: el cuadrado de la banda cúbica

`Schur` prueba que, sobre la subred par de `ℤ³` (FCC), la dinámica efectiva es exacta,
`H_eff(E) = H_PQ H_QP / E`, y que la entrada `(p, q)` de `H_PQ H_QP` cuenta palabras de dos
pasos de eje (`palabras2`): `6` de regreso, `2` hacia cada diagonal de cara, `1` hacia cada
`±2eᵢ`. El grafo de `12` vecinos con salto uniforme es el truncamiento de eso a primeros
vecinos: tira el regreso y la segunda capa, y pone `1` donde el peso es `2`.

Aquí se calcula el símbolo de Bloch de la versión refinada. El símbolo de un transporte es la
suma de las fases `e^{i k·v}` sobre sus desplazamientos `v`; el de dos pasos es la suma sobre
las palabras. Como las palabras de dos pasos son pares de palabras de un paso, el símbolo se
multiplica:

  `símbolo(H²)(k) = (símbolo(H)(k))² = (2 cos k₁ + 2 cos k₂ + 2 cos k₃)²`.

La banda de FCC refinada es `t₀² / E` por el cuadrado de la banda cúbica. Con los pesos del
censo,

  `(2 Σ cos kᵢ)² = 6 + 8 Σ_{i<j} cos kᵢ cos kⱼ + 2 Σ cos 2kᵢ`,

donde `6` es el regreso, `8 cos kᵢ cos kⱼ = 2 · (4 cos kᵢ cos kⱼ)` son las doce diagonales de
cara con peso `2`, y `2 cos 2kᵢ` son los seis dobles pasos con peso `1`.

El peso `2` de la diagonal de cara es el de `card_twoStepWords_fiber`
(PhyslibAlpha #1987, abierto): cada vecino de FCC se alcanza con exactamente dos palabras de dos
pasos. Aquí no se importa ese PR; el peso entra por `palabras2`, de `Schur`.

La diferencia con el truncamiento no es de detalle: la banda refinada es `≥ 0` en todo `k`
(es un cuadrado, `H_PQ H_QP` es semidefinida positiva), y la del grafo de `12` vecinos con
salto uniforme cambia de signo.

## Resultados principales

* `simbolo_vecinos` : el símbolo del paso de eje es `2 cos k₁ + 2 cos k₂ + 2 cos k₃`.
* `simbolo_dospasos` : el símbolo de las palabras de dos pasos es el cuadrado del de un paso.
* `simbolo_palabras2` : lo mismo, escrito con los pesos `palabras2` del censo.
* `banda_fcc_refinada` : el símbolo de `H_PQ H_QP` es `(2 Σ cos kᵢ)²`.
* `banda_fcc_refinada_eq_pesos` : con los pesos `6`, `2`, `1` del censo.
* `banda_fcc_refinada_nonneg`, `banda_fcc_refinada_le` : está en `[0, 36]`; `36` en `k = 0`.
* `banda_truncada_negativa` : el grafo de `12` vecinos con salto uniforme es negativo en
  `k = (π, 0, 0)`; la refinada vale ahí `4`.
-/

namespace NRS3Cristales

open Finset

/-! ## A. El símbolo de Bloch de un conjunto de desplazamientos -/

/-- La fase de Bloch `e^{i k·v}` del desplazamiento `v` con momento `k`. -/
noncomputable def fase (k : Fin 3 → ℝ) (v : Fin 3 → ℤ) : ℂ :=
  Complex.exp (((∑ i, k i * (v i : ℝ) : ℝ) : ℂ) * Complex.I)

/-- **La fase es multiplicativa**: componer desplazamientos multiplica las fases. -/
lemma fase_add (k : Fin 3 → ℝ) (v w : Fin 3 → ℤ) : fase k (v + w) = fase k v * fase k w := by
  have h : ∑ i, k i * (((v + w) i : ℤ) : ℝ) = ∑ i, k i * (v i : ℝ) + ∑ i, k i * (w i : ℝ) := by
    simp [mul_add, Finset.sum_add_distrib]
  rw [fase, h, Complex.ofReal_add, add_mul, Complex.exp_add]
  rfl

/-- El paso de eje `±eᵢ` determina `(i, signo)`. -/
lemma paso_inj :
    Function.Injective fun is : Fin 3 × Bool =>
      (Pi.single is.1 (if is.2 then (1 : ℤ) else -1) : Fin 3 → ℤ) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have h1 := congrFun h i
  by_cases hij : i = j
  · subst hij
    cases a <;> cases b <;> simp_all
  · simp [hij] at h1
    cases a <;> simp_all

/-- Una suma sobre los seis vecinos de `0` es una suma sobre `(i, signo)`. -/
lemma sum_vecinos_zero {M : Type*} [AddCommMonoid M] (f : (Fin 3 → ℤ) → M) :
    ∑ s ∈ vecinos 0, f s =
      ∑ i : Fin 3, (f (Pi.single i 1) + f (Pi.single i (-1))) := by
  rw [vecinos, Finset.sum_image (fun x _ y _ h => paso_inj (by simpa using h)),
    Fintype.sum_prod_type]
  simp

/-- **El símbolo del paso de eje**: la banda cúbica `2 cos k₁ + 2 cos k₂ + 2 cos k₃`. -/
lemma simbolo_vecinos (k : Fin 3 → ℝ) :
    ∑ s ∈ vecinos 0, fase k s = ((∑ i, 2 * Real.cos (k i) : ℝ) : ℂ) := by
  rw [sum_vecinos_zero]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : (∑ j, k j * (((Pi.single i (1 : ℤ) : Fin 3 → ℤ) j : ℤ) : ℝ)) = k i := by
    simp [Pi.single_apply]
  have e2 : (∑ j, k j * (((Pi.single i (-1 : ℤ) : Fin 3 → ℤ) j : ℤ) : ℝ)) = -k i := by
    simp [Pi.single_apply]
  rw [fase, fase, e1, e2, ← Complex.ofReal_cos]
  push_cast
  exact (Complex.two_cos _).symm

/-! ## B. Las palabras de dos pasos -/

/-- Los vecinos de `w` son `w` más los vecinos de `0`. -/
lemma vecinos_eq_image (w : Fin 3 → ℤ) : vecinos w = (vecinos 0).image (w + ·) := by
  simpa using vecinos_add w 0

/-- **El símbolo de las palabras de dos pasos es el cuadrado del de un paso.** -/
lemma simbolo_dospasos (k : Fin 3 → ℝ) :
    ∑ w ∈ vecinos 0, ∑ u ∈ vecinos w, fase k u = (∑ s ∈ vecinos 0, fase k s) ^ 2 := by
  have h : ∀ w, ∑ u ∈ vecinos w, fase k u = fase k w * ∑ s ∈ vecinos 0, fase k s := by
    intro w
    rw [vecinos_eq_image, Finset.sum_image (fun x _ y _ h => add_left_cancel h),
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => fase_add k w s
  rw [Finset.sum_congr rfl fun w _ => h w, ← Finset.sum_mul, sq]

/-- Regrupar las palabras de dos pasos por su extremo: cada desplazamiento `v` cuenta
`palabras2 0 v` veces. -/
lemma sum_dospasos_eq_palabras2 (f : (Fin 3 → ℤ) → ℂ) :
    ∑ w ∈ vecinos 0, ∑ u ∈ vecinos w, f u =
      ∑ v ∈ (vecinos 0).biUnion vecinos, (palabras2 0 v : ℂ) * f v := by
  rw [Finset.sum_comm' (t' := (vecinos 0).biUnion vecinos)
    (s' := fun v => (vecinos 0).filter fun w => v ∈ vecinos w)]
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    rfl
  · intro w v
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨hw, hv⟩
      exact ⟨⟨hw, hv⟩, w, hw, hv⟩
    · rintro ⟨⟨hw, hv⟩, -⟩
      exact ⟨hw, hv⟩

/-- **El símbolo de `H_PQ H_QP`, con los pesos del censo, es el cuadrado de la banda cúbica.** -/
lemma simbolo_palabras2 (k : Fin 3 → ℝ) :
    ∑ v ∈ (vecinos 0).biUnion vecinos, (palabras2 0 v : ℂ) * fase k v =
      (((∑ i, 2 * Real.cos (k i)) ^ 2 : ℝ) : ℂ) := by
  rw [← sum_dospasos_eq_palabras2, simbolo_dospasos, simbolo_vecinos]
  push_cast
  rfl

/-! ## C. La banda de FCC refinada -/

/-- La banda cúbica de un paso de eje. -/
noncomputable def bandaCubica (k : Fin 3 → ℝ) : ℝ := ∑ i, 2 * Real.cos (k i)

/-- **La banda de FCC refinada**: el símbolo de `H_PQ H_QP` (y por tanto de
`H_eff(E) = H_PQ H_QP / E`, salvo el factor `t₀² / E`) es el cuadrado de la banda cúbica. -/
theorem banda_fcc_refinada (k : Fin 3 → ℝ) :
    ∑ v ∈ (vecinos 0).biUnion vecinos, (palabras2 0 v : ℂ) * fase k v =
      ((bandaCubica k ^ 2 : ℝ) : ℂ) :=
  simbolo_palabras2 k

/-- **Con los pesos del censo**: `6` de regreso, `8 cos kᵢ cos kⱼ` por las doce diagonales de
cara (peso `2`), `2 cos 2kᵢ` por los seis dobles pasos (peso `1`). -/
theorem banda_fcc_refinada_eq_pesos (k : Fin 3 → ℝ) :
    bandaCubica k ^ 2 =
      6 + 8 * (Real.cos (k 0) * Real.cos (k 1) + Real.cos (k 0) * Real.cos (k 2) +
          Real.cos (k 1) * Real.cos (k 2)) +
        2 * (Real.cos (2 * k 0) + Real.cos (2 * k 1) + Real.cos (2 * k 2)) := by
  simp only [bandaCubica, Fin.sum_univ_three, Real.cos_two_mul]
  ring

/-- La banda refinada es `≥ 0` en todo `k`: `H_PQ H_QP` es semidefinida positiva. -/
lemma banda_fcc_refinada_nonneg (k : Fin 3 → ℝ) : 0 ≤ bandaCubica k ^ 2 := sq_nonneg _

/-- La banda cúbica está en `[−6, 6]`. -/
lemma abs_bandaCubica_le (k : Fin 3 → ℝ) : |bandaCubica k| ≤ 6 := by
  have h : ∀ i, |2 * Real.cos (k i)| ≤ 2 := fun i => by
    rw [abs_mul, abs_two]
    nlinarith [Real.abs_cos_le_one (k i)]
  calc |bandaCubica k| ≤ ∑ i, |2 * Real.cos (k i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, (2 : ℝ) := Finset.sum_le_sum fun i _ => h i
    _ = 6 := by simp; norm_num

/-- **La banda refinada está en `[0, 36]`**, y `36 = 6 + 12·2 + 6·1` es el censo completo,
alcanzado en `k = 0`. -/
lemma banda_fcc_refinada_le (k : Fin 3 → ℝ) : bandaCubica k ^ 2 ≤ 36 := by
  have := abs_bandaCubica_le k
  nlinarith [abs_nonneg (bandaCubica k), sq_abs (bandaCubica k)]

lemma banda_fcc_refinada_zero : bandaCubica 0 ^ 2 = 36 := by
  simp [bandaCubica]; norm_num

/-- El símbolo del grafo de `12` vecinos con salto uniforme (el truncamiento a primeros
vecinos): `4 Σ_{i<j} cos kᵢ cos kⱼ`. -/
noncomputable def bandaTruncada (k : Fin 3 → ℝ) : ℝ :=
  4 * (Real.cos (k 0) * Real.cos (k 1) + Real.cos (k 0) * Real.cos (k 2) +
    Real.cos (k 1) * Real.cos (k 2))

/-- **El truncamiento cambia de signo; la banda refinada no**: en `k = (π, 0, 0)` el grafo de
`12` vecinos vale `−4` y la banda refinada vale `4`. -/
theorem banda_truncada_negativa :
    bandaTruncada ![Real.pi, 0, 0] = -4 ∧ bandaCubica ![Real.pi, 0, 0] ^ 2 = 4 := by
  refine ⟨?_, ?_⟩
  · simp [bandaTruncada]
  · simp [bandaCubica, Fin.sum_univ_three]; norm_num

end NRS3Cristales
