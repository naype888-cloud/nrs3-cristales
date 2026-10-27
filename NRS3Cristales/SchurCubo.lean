/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube.Basic
import NRS3Cristales.Schur

/-!
# La parte FCC del estado de corriente máxima no carga tensión

El estado de corriente máxima del cubo (`maxCurrentCubeState`) tiene en la posición
`(x, y, z)` la amplitud `r · i^(x + y + z)` con `r` real. En las posiciones de suma par (la
partición de FCC de `Schur`) la fase es `±1`: las amplitudes son reales. Con cualquier
transporte efectivo de entradas reales sobre esas posiciones, en particular `H_PQ H_QP` (las
palabras de dos pasos de eje), la tensión es `0` (`tension_eq_zero_of_real`).

Sobre el cubo completo el mismo estado satura la relación de cada eje con `2` o `3`
posiciones y es estricto desde `4` (`centeredGramDefect_alongX_eq_zero_iff`,
`robertson_schrodinger_cube`): en `3³` satura y en `4³` rompe. Ninguna de las dos cosas se ve
en la descripción efectiva por diagonales: la tensión vive en el paso de eje `P ↔ Q`.

## Resultados principales

* `val_maxCurrentState` : la amplitud de la cadena es `√(2/(N+1)) · i^m · sin((m+1)π/(N+1))`.
* `val_maxCurrentCubeState` : la amplitud del cubo es el producto de las tres.
* `im_val_maxCurrentCubeState_of_even` : en las posiciones de suma par la amplitud es real.
* `tension_parteFCC_eq_zero` : la parte FCC del estado tiene tensión `0` con todo transporte
  efectivo real.
-/

namespace NRS3Cristales

open CondensedMatter TightBindingChain QuantumMechanics FiniteHilbertSpace
open scoped InnerProductSpace

variable (T Tx Ty Tz : TightBindingChain)

/-- La amplitud de un estado en la posición `m` es `⟪|m⟩, ψ⟫`. -/
lemma inner_localizedState (ψ : T.HilbertSpace) (m : Fin T.N) :
    ⟪(localizedState m : T.HilbertSpace), ψ⟫_ℂ = ψ.val m := by
  rw [localizedState, basisFun_apply, inner_eq_val, EuclideanSpace.inner_single_left]
  simp

/-- La amplitud del estado de corriente máxima de la cadena. -/
lemma val_maxCurrentState (m : Fin T.N) :
    T.maxCurrentState.val m = (((√(2 / (T.N + 1)) *
      Real.sin (((m : ℕ) + 1) * (Real.pi / (T.N + 1)))) : ℝ) : ℂ) * Complex.I ^ (m : ℕ) := by
  rw [← inner_localizedState, inner_maxCurrentState]
  push_cast
  ring

/-- La amplitud del estado de corriente máxima del cubo es el producto de las tres. -/
lemma val_maxCurrentCubeState (x : Fin Tx.N) (y : Fin Ty.N) (z : Fin Tz.N) :
    (Tx.maxCurrentCubeState Ty Tz).val (x, y, z) =
      Tx.maxCurrentState.val x * (Ty.maxCurrentState.val y * Tz.maxCurrentState.val z) := by
  rw [maxCurrentCubeState, prodVec_val, prodVec_val]

/-- **En las posiciones de suma par la amplitud del estado de corriente máxima es real**: la
fase `i^(x + y + z)` es `±1`. -/
lemma im_val_maxCurrentCubeState_of_even {x : Fin Tx.N} {y : Fin Ty.N} {z : Fin Tz.N}
    (h : Even ((x : ℕ) + y + z)) : ((Tx.maxCurrentCubeState Ty Tz).val (x, y, z)).im = 0 := by
  obtain ⟨k, hk⟩ := h
  rw [val_maxCurrentCubeState, val_maxCurrentState, val_maxCurrentState, val_maxCurrentState]
  set a := √(2 / (Tx.N + 1)) * Real.sin (((x : ℕ) + 1) * (Real.pi / (Tx.N + 1)))
  set b := √(2 / (Ty.N + 1)) * Real.sin (((y : ℕ) + 1) * (Real.pi / (Ty.N + 1)))
  set c := √(2 / (Tz.N + 1)) * Real.sin (((z : ℕ) + 1) * (Real.pi / (Tz.N + 1)))
  have hI : Complex.I ^ (x : ℕ) * (Complex.I ^ (y : ℕ) * Complex.I ^ (z : ℕ)) =
      (((-1) ^ k : ℝ) : ℂ) := by
    rw [← pow_add, ← pow_add, ← add_assoc, hk, ← two_mul, pow_mul, Complex.I_sq]
    push_cast
    rfl
  rw [show (a : ℂ) * Complex.I ^ (x : ℕ) * ((b : ℂ) * Complex.I ^ (y : ℕ) *
      ((c : ℂ) * Complex.I ^ (z : ℕ))) =
      (a : ℂ) * b * c * (Complex.I ^ (x : ℕ) * (Complex.I ^ (y : ℕ) * Complex.I ^ (z : ℕ)))
      by ring, hI]
  norm_cast

/-- Las posiciones de suma par del cubo: la partición de FCC. -/
abbrev ParFCC := {p : Fin Tx.N × Fin Ty.N × Fin Tz.N // Even ((p.1 : ℕ) + p.2.1 + p.2.2)}

/-- La parte FCC del estado de corriente máxima del cubo. -/
noncomputable def parteFCC : ParFCC Tx Ty Tz → ℂ :=
  fun p => (Tx.maxCurrentCubeState Ty Tz).val p.1

/-- **La parte FCC del estado de corriente máxima no carga tensión**: con cualquier transporte
efectivo `T` y posición `X` de entradas reales sobre las posiciones de suma par, en particular
las palabras de dos pasos de eje `H_PQ H_QP`, `⟨i[T, X]⟩ = 0`. -/
lemma tension_parteFCC_eq_zero {T X : Matrix (ParFCC Tx Ty Tz) (ParFCC Tx Ty Tz) ℂ}
    (hT : ∀ i j, (T i j).im = 0) (hX : ∀ i j, (X i j).im = 0) :
    tension T X (parteFCC Tx Ty Tz) = 0 :=
  tension_eq_zero_of_real hT hX fun p => im_val_maxCurrentCubeState_of_even Tx Ty Tz p.2

end NRS3Cristales
