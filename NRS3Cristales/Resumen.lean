/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import PhyslibAlpha.CondensedMatter.Crystal.PointGroup.Cubic
import PhyslibAlpha.CondensedMatter.Crystal.PointGroup.Hypercubic
import PhyslibAlpha.CondensedMatter.Crystal.PointGroup.TetragonalHexagonal
import PhyslibAlpha.CondensedMatter.Crystal.PointGroup.Orthorhombic
import PhyslibAlpha.CondensedMatter.Crystal.Inversion
import PhyslibAlpha.CondensedMatter.Crystal.GroupVelocity
import PhyslibAlpha.CondensedMatter.Crystal.InvariantStateUncertainty
import PhyslibAlpha.CondensedMatter.Crystal.LittleGroup
import PhyslibAlpha.CondensedMatter.TightBindingChain.MaxCurrentState.UncertaintyRatio

/-!
# Cristales: la simetría da la forma de `Σ` y `Ω`, el espectro da el tamaño

Resumen de lo probado en la rama `mosaic-cristales` del fork de Physlib. Cada `example` repite el
enunciado y lo prueba con el lema de la biblioteca, así que este archivo compila solo si los
lemas dicen exactamente esto.
-/

namespace NRS3Cristales

open CondensedMatter Crystal ProbabilisticTheory Filter Topology
open scoped selfAdjoint

/-! ## 1. Las redes y sus grupos puntuales -/

example : Nat.card (hypercubicGraph 3).pointGroup = 2 ^ 3 * Nat.factorial 3 :=
  card_pointGroup_hypercubic 3
example : Nat.card bccGraph.pointGroup = 48 := bcc_card_pointGroup
example : Nat.card fccGraph.pointGroup = 48 := fcc_card_pointGroup
example : Nat.card tetragonalGraph.pointGroup = 16 := tetragonal_card_pointGroup
example : Nat.card bodyCentredTetragonalGraph.pointGroup = 16 :=
  bodyCentredTetragonal_card_pointGroup
example : Nat.card hexagonalGraph.pointGroup = 24 := hexagonal_card_pointGroup
example : Nat.card orthorhombicGraph.pointGroup = 8 := orthorhombic_card_pointGroup
example : Nat.card baseCentredOrthorhombicGraph.pointGroup = 8 :=
  baseCentredOrthorhombic_card_pointGroup
example : Nat.card bodyCentredOrthorhombicGraph.pointGroup = 8 :=
  bodyCentredOrthorhombic_card_pointGroup
example : Nat.card faceCentredOrthorhombicGraph.pointGroup = 8 :=
  faceCentredOrthorhombic_card_pointGroup

/-! ## 2. La forma: toda red de Bravais es centrosimétrica, y `Σ_HX = 0` -/

example {G : Type*} [AddCommGroup G] (g : PeriodicGraph (Crystal.ofUnitCell G Unit)) :
    PeriodicGraph.inversion ∈ g.symmetries :=
  PeriodicGraph.inversion_mem_symmetries g

example {G : Type*} [AddCommGroup G] [DecidableEq G]
    (g : PeriodicGraph (Crystal.ofUnitCell G Unit)) {Λ : Finset G} (hΛ : ∀ n ∈ Λ, -n ∈ Λ)
    (hne : Λ.Nonempty) (t : ℝ) (k r : G →+ ℝ) :
    UnitalPositiveLinearMap.covariance
      (UnitalPositiveLinearMap.ofVec (norm_unitPlaneWave hne k))
      (hoppingObservable g t) (positionObservable r) = 0 :=
  covariance_hopping_position_unitPlaneWave g hΛ hne t k r

/-! ## 3. El tamaño: lo que sobrevive es la velocidad de grupo de la banda -/

example {d : ℕ} (g : PeriodicGraph (Crystal.ofUnitCell (Fin d → ℤ) Unit)) (t : ℝ)
    (k r : (Fin d → ℤ) →+ ℝ) :
    Tendsto (fun N : ℕ => UnitalPositiveLinearMap.expectation
      (UnitalPositiveLinearMap.ofVec (norm_unitPlaneWave (box_succ_nonempty d N) k))
      ⁅hoppingObservable (Λ := box d (N + 1)) g t, positionObservable r⁆) atTop
      (𝓝 (-(t / 2) * ∑ δ ∈ bondVectors g, r δ * Real.sin (k δ))) :=
  tendsto_expectation_bracket_box g t k r

example {G : Type*} [AddCommGroup G] [DecidableEq G]
    (g : PeriodicGraph (Crystal.ofUnitCell G Unit)) (t : ℝ) (k r : G →+ ℝ) :
    HasDerivAt (fun s : ℝ => band g t (k + s • r))
      (t * ∑ δ ∈ bondVectors g, r δ * Real.sin (k δ)) 0 :=
  hasDerivAt_band g t k r

/-! ## 4. El puente: Robertson 1934 para los estados de cristal -/

example {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A] (ω : AlgState A)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → selfAdjoint A) :
    |(ω.bracketMatrix a).det| ≤ (ω.covarianceMatrix a).det :=
  ω.robertson_det a

/-! ## 5. La cadena: `cov(H, X) = 0` en el estado de corriente máxima, por simetría -/

example (T : TightBindingChain) :
    UnitalPositiveLinearMap.covariance T.maxCurrentVectorState T.openHamiltonianObservable
      T.positionObservable = 0 :=
  T.covariance_maxCurrentState

/-! ## 6. El grupo pequeño de cada momento: qué entradas de `Σ` y `Ω` se anulan en cada `k` -/

/-- Si `s` está en el grupo pequeño de `χ`, fija la región e invierte la dirección `r`, entonces
en la onda plana de momento `χ` la energía y la posición a lo largo de `r` no se correlacionan. -/
example {G : Type*} [AddCommGroup G] [DecidableEq G] [TopologicalSpace G] [DiscreteTopology G]
    {g : PeriodicGraph (Crystal.ofUnitCell G Unit)} {s : g.symmetries} {χ : BrillouinZone G}
    (hs : s ∈ g.littleGroup χ) {Λ : Finset G}
    (hΛ : ∀ n, (s : CellSymmetry G Unit).linear n ∈ Λ ↔ n ∈ Λ) (hne : Λ.Nonempty) (t : ℝ)
    {r : G →+ ℝ} (hr : ∀ n, r ((s : CellSymmetry G Unit).linear n) = -r n) :
    UnitalPositiveLinearMap.covariance
        (UnitalPositiveLinearMap.ofVec (norm_unitCharacterWave hne χ))
        (hoppingObservable g t) (positionObservable r) = 0 ∧
      UnitalPositiveLinearMap.expectation
        (UnitalPositiveLinearMap.ofVec (norm_unitCharacterWave hne χ))
        ⁅hoppingObservable (Λ := Λ) g t, positionObservable r⁆ = 0 :=
  ⟨covariance_hopping_position_littleGroup hs hΛ hne t hr,
    expectation_bracket_hopping_position_littleGroup hs hΛ hne t hr⟩

/-- En los momentos con `χ(-n) = χ(n)` (el centro y las esquinas de la zona) la inversión está en
el grupo pequeño, así que `Ω_HX = 0` en todas las direcciones. -/
example {G : Type*} [AddCommGroup G] [DecidableEq G] [TopologicalSpace G] [DiscreteTopology G]
    (g : PeriodicGraph (Crystal.ofUnitCell G Unit)) {χ : BrillouinZone G}
    (hχ : ∀ n, χ (Multiplicative.ofAdd (-n)) = χ (Multiplicative.ofAdd n)) {Λ : Finset G}
    (hΛ : ∀ n, -n ∈ Λ ↔ n ∈ Λ) (hne : Λ.Nonempty) (t : ℝ) (r : G →+ ℝ) :
    UnitalPositiveLinearMap.expectation
      (UnitalPositiveLinearMap.ofVec (norm_unitCharacterWave hne χ))
      ⁅hoppingObservable (Λ := Λ) g t, positionObservable r⁆ = 0 :=
  expectation_bracket_hopping_position_of_neg g hχ hΛ hne t r

end NRS3Cristales
