/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import PhyslibAlpha.CondensedMatter.Crystal.LittleGroup
import PhyslibAlpha.CondensedMatter.Crystal.PointGroup.Hypercubic
import PhyslibAlpha.CondensedMatter.Crystal.GroupVelocity

/-!
# El grupo pequeño en la diagonal de la red cuadrada

En la red cuadrada, el intercambio de ejes `(x, y) ↦ (y, x)` es una simetría. Si el momento `χ`
no cambia al intercambiar los ejes (la diagonal `k = (k₀, k₀)` de la zona de Brillouin), el
intercambio está en el grupo pequeño de `χ`. Entonces, en la onda plana de `χ` sobre el cuadrado
`{0, …, N}²`, `Ω_{H, X} = Ω_{H, Y}`: la velocidad de grupo apunta a lo largo de la diagonal.

Es la instancia concreta de `expectation_bracket_hopping_position_comp_littleGroup`.
-/

namespace NRS3Cristales

open CondensedMatter Crystal ProbabilisticTheory
open scoped selfAdjoint

/-- El intercambio de los ejes de la red cuadrada. -/
def intercambio : (Fin 2 → ℤ) ≃+ (Fin 2 → ℤ) := signedPerm (Equiv.swap 0 1) fun _ => true

lemma intercambio_apply (n : Fin 2 → ℤ) : intercambio n 0 = n 1 ∧ intercambio n 1 = n 0 := by
  simp [intercambio, signedPerm_apply, signOf]

lemma intercambio_symm (n : Fin 2 → ℤ) : intercambio.symm n = intercambio n := by
  rw [AddEquiv.symm_apply_eq]
  funext i
  fin_cases i <;> simp [(intercambio_apply _).1, (intercambio_apply _).2]

/-- El intercambio como simetría de la red cuadrada. -/
def intercambioSim : (hypercubicGraph 2).symmetries :=
  ⟨⟨intercambio, 1, fun _ => 0⟩, by
    rw [PeriodicGraph.mem_symmetries_iff]
    rintro ⟨⟩ ⟨⟩ d
    simpa [intercambio] using
      ((signedPerm_mem_pointStabilizer (Equiv.swap 0 1) fun _ => true) d).symm⟩

/-- La coordenada `x`. -/
def coordX : (Fin 2 → ℤ) →+ ℝ := (Int.castAddHom ℝ).comp (Pi.evalAddMonoidHom _ 0)

/-- La coordenada `y`. -/
def coordY : (Fin 2 → ℤ) →+ ℝ := (Int.castAddHom ℝ).comp (Pi.evalAddMonoidHom _ 1)

lemma coordX_comp : coordX.comp (intercambio.symm : (Fin 2 → ℤ) →+ (Fin 2 → ℤ)) = coordY := by
  ext n
  simp [coordX, coordY, intercambio_symm, (intercambio_apply _).1]

/-- El cuadrado `{0, …, N}²` no cambia al intercambiar los ejes. -/
lemma intercambio_mem_box (N : ℕ) (n : Fin 2 → ℤ) :
    intercambio n ∈ box 2 (N + 1) ↔ n ∈ box 2 (N + 1) := by
  simp only [box, Fintype.mem_piFinset, Fin.forall_fin_two, (intercambio_apply _).1,
    (intercambio_apply _).2]
  exact and_comm

/-- **En la diagonal de la zona de Brillouin, `Ω_{H, X} = Ω_{H, Y}`** en la onda plana sobre el
cuadrado `{0, …, N}²`. -/
lemma omega_diagonal {χ : BrillouinZone (Fin 2 → ℤ)}
    (hχ : ∀ n, χ (Multiplicative.ofAdd (intercambio n)) = χ (Multiplicative.ofAdd n))
    (N : ℕ) (t : ℝ) :
    UnitalPositiveLinearMap.expectation
      (UnitalPositiveLinearMap.ofVec (norm_unitCharacterWave (box_succ_nonempty 2 N) χ))
      ⁅hoppingObservable (Λ := box 2 (N + 1)) (hypercubicGraph 2) t, positionObservable coordY⁆ =
    UnitalPositiveLinearMap.expectation
      (UnitalPositiveLinearMap.ofVec (norm_unitCharacterWave (box_succ_nonempty 2 N) χ))
      ⁅hoppingObservable (Λ := box 2 (N + 1)) (hypercubicGraph 2) t,
        positionObservable coordX⁆ := by
  have hs : intercambioSim ∈ (hypercubicGraph 2).littleGroup χ := by
    have hχ' : ∀ m, χ (Multiplicative.ofAdd (intercambio.symm m)) = χ (Multiplicative.ofAdd m) :=
      fun m => by rw [intercambio_symm, hχ]
    rw [PeriodicGraph.mem_littleGroup]
    ext n
    exact congrArg Subtype.val (hχ' (Multiplicative.toAdd n))
  have h := expectation_bracket_hopping_position_comp_littleGroup hs (intercambio_mem_box N)
    (box_succ_nonempty 2 N) t coordX
  rwa [show coordX.comp ((intercambioSim : CellSymmetry (Fin 2 → ℤ) Unit).linear.symm :
    (Fin 2 → ℤ) →+ (Fin 2 → ℤ)) = coordY from coordX_comp] at h

end NRS3Cristales
