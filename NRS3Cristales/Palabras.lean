/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Una palabra o dos: conmutar es lo mismo que no tener estado que distinga `AB` de `BA`

Para dos observables hermitianos `A, B` la palabra de segundo orden que los mezcla es `AB`
(o `BA`). Hay dos casos y se excluyen:

* `A, B` conmutan: `AB = BA` es **una** sola palabra (la diagonal del cubo, `x·y = y·x`,
  `palabras2_diagonalCara` cuenta los dos caminos pero es un solo operador). El término de
  conmutador de Robertson–Schrödinger vale `0` en todo estado.
* `A, B` no conmutan: `AB` y `BA` son **dos** palabras distintas, y hay un estado unitario
  que las distingue: `⟨[A, B]⟩ ≠ 0`. Para ese estado la cota de incertidumbre es estrictamente
  positiva. Es el caso de `T_d : P_d`.

## Resultados principales

* `commute_iff_forall_commutator` : `A, B` conmutan ⟺ `⟨ψ, [A, B] ψ⟩ = 0` para todo `ψ`.
* `not_commute_iff_exists_unit` : no conmutan ⟺ existe un estado unitario con
  `⟨ψ, [A, B] ψ⟩ ≠ 0`.
* `commutator_sq_le` : en un estado unitario,
  `|⟨[A, B]⟩|² ≤ 4 · Var A · Var B` (la desigualdad elemental, sin covarianza).
* `exists_pos_bound_of_not_commute` : si no conmutan, existe un estado unitario con
  `0 < Var A · Var B` (la varianza es `‖fluct A ψ‖²`).
-/

open scoped ComplexConjugate InnerProductSpace

namespace NRS3Cristales

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- La palabra de diferencia: `AB − BA`. -/
abbrev commutator (A B : E →ₗ[ℂ] E) : E →ₗ[ℂ] E := A * B - B * A

/-- **Una palabra**: `A, B` conmutan si y solo si el valor esperado de `[A, B]` es cero en
todo estado. -/
lemma commute_iff_forall_commutator (A B : E →ₗ[ℂ] E) :
    Commute A B ↔ ∀ ψ : E, ⟪commutator A B ψ, ψ⟫_ℂ = 0 := by
  rw [inner_map_self_eq_zero, sub_eq_zero]
  exact ⟨fun h => h, fun h => h⟩

/-- **Dos palabras**: `A, B` no conmutan si y solo si algún estado unitario distingue `AB`
de `BA`. -/
lemma not_commute_iff_exists_unit [FiniteDimensional ℂ E] [Nontrivial E] (A B : E →ₗ[ℂ] E) :
    ¬ Commute A B ↔ ∃ ψ : E, ‖ψ‖ = 1 ∧ ⟪commutator A B ψ, ψ⟫_ℂ ≠ 0 := by
  rw [commute_iff_forall_commutator]
  push Not
  constructor
  · rintro ⟨ψ, hψ⟩
    have hne : ψ ≠ 0 := by
      rintro rfl; simp at hψ
    refine ⟨(‖ψ‖⁻¹ : ℂ) • ψ, ?_, ?_⟩
    · rw [norm_smul]; simp [hne]
    · rw [map_smul, inner_smul_left, inner_smul_right]
      exact mul_ne_zero (by simp [hne]) (mul_ne_zero (by simp [hne]) hψ)
  · rintro ⟨ψ, -, h⟩; exact ⟨ψ, h⟩

/-- La media de un observable hermitiano en un estado es real. -/
lemma conj_inner_self_eq {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (ψ : E) :
    conj ⟪A ψ, ψ⟫_ℂ = ⟪A ψ, ψ⟫_ℂ := by
  rw [inner_conj_symm]; exact (hA ψ ψ).symm

/-- La fluctuación `A ψ − ⟨A⟩ ψ`. -/
noncomputable def fluct (A : E →ₗ[ℂ] E) (ψ : E) : E := A ψ - ⟪A ψ, ψ⟫_ℂ • ψ

/-- La desigualdad elemental sin covarianza: en un estado unitario,
`|⟨[A, B]⟩|² ≤ 4 ‖(A − ⟨A⟩)ψ‖² ‖(B − ⟨B⟩)ψ‖²`. -/
lemma commutator_sq_le {A B : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) {ψ : E}
    (hψ : ‖ψ‖ = 1) :
    ‖⟪commutator A B ψ, ψ⟫_ℂ‖ ^ 2 ≤ 4 * (‖fluct A ψ‖ ^ 2 * ‖fluct B ψ‖ ^ 2) := by
  set m := ⟪A ψ, ψ⟫_ℂ with hm
  set n := ⟪B ψ, ψ⟫_ℂ with hn
  have key : ⟪commutator A B ψ, ψ⟫_ℂ = ⟪fluct B ψ, fluct A ψ⟫_ℂ - ⟪fluct A ψ, fluct B ψ⟫_ℂ := by
    have hAB : ⟪A (B ψ), ψ⟫_ℂ = ⟪B ψ, A ψ⟫_ℂ := hA (B ψ) ψ
    have hBA : ⟪B (A ψ), ψ⟫_ℂ = ⟪A ψ, B ψ⟫_ℂ := hB (A ψ) ψ
    have h1 : ⟪ψ, ψ⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hψ]; simp
    have hcm : conj m = m := conj_inner_self_eq hA ψ
    have hcn : conj n = n := conj_inner_self_eq hB ψ
    have e1 : ⟪B ψ, ψ⟫_ℂ = n := rfl
    have e2 : ⟪A ψ, ψ⟫_ℂ = m := rfl
    have e3 : ⟪ψ, A ψ⟫_ℂ = m := by rw [← inner_conj_symm, hcm]
    have e4 : ⟪ψ, B ψ⟫_ℂ = n := by rw [← inner_conj_symm, hcn]
    have c1 : ⟪commutator A B ψ, ψ⟫_ℂ = ⟪B ψ, A ψ⟫_ℂ - ⟪A ψ, B ψ⟫_ℂ := by
      rw [commutator, LinearMap.sub_apply, inner_sub_left]
      exact congrArg₂ (· - ·) hAB hBA
    have c2 : ⟪fluct B ψ, fluct A ψ⟫_ℂ = ⟪B ψ, A ψ⟫_ℂ - n * m := by
      simp only [fluct, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, e1, e2,
        e3, h1, hcn]
      ring
    have c3 : ⟪fluct A ψ, fluct B ψ⟫_ℂ = ⟪A ψ, B ψ⟫_ℂ - m * n := by
      simp only [fluct, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, e1, e2,
        e4, h1, hcm]
      ring
    rw [c1, c2, c3]; ring
  rw [key]
  set a := fluct A ψ
  set b := fluct B ψ
  have h1 : ‖⟪b, a⟫_ℂ‖ ≤ ‖b‖ * ‖a‖ := norm_inner_le_norm b a
  have h2 : ‖⟪a, b⟫_ℂ‖ ≤ ‖a‖ * ‖b‖ := norm_inner_le_norm a b
  have h3 : ‖⟪b, a⟫_ℂ - ⟪a, b⟫_ℂ‖ ≤ 2 * (‖a‖ * ‖b‖) :=
    (norm_sub_le _ _).trans (by nlinarith)
  calc ‖⟪b, a⟫_ℂ - ⟪a, b⟫_ℂ‖ ^ 2 ≤ (2 * (‖a‖ * ‖b‖)) ^ 2 := by gcongr
    _ = 4 * (‖a‖ ^ 2 * ‖b‖ ^ 2) := by ring

/-- **Dos palabras distintas dan incertidumbre positiva**: si `A, B` no conmutan hay un estado
unitario en el que el producto de las varianzas es estrictamente positivo. -/
lemma exists_pos_bound_of_not_commute [FiniteDimensional ℂ E] [Nontrivial E]
    {A B : E →ₗ[ℂ] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) (h : ¬ Commute A B) :
    ∃ ψ : E, ‖ψ‖ = 1 ∧ 0 < ‖fluct A ψ‖ ^ 2 * ‖fluct B ψ‖ ^ 2 := by
  obtain ⟨ψ, hψ, hne⟩ := (not_commute_iff_exists_unit A B).1 h
  refine ⟨ψ, hψ, ?_⟩
  have := commutator_sq_le hA hB hψ
  have hpos : 0 < ‖⟪commutator A B ψ, ψ⟫_ℂ‖ ^ 2 := by positivity
  linarith

end NRS3Cristales
