/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube.Basic
import NRS3Cristales.Schur
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Hasse

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
* `cubo`, `cubo_adj_iff` : el cubo abierto es el producto caja de tres `pathGraph` de Mathlib,
  y sus aristas son las de `redCubica` (el grafo de Cayley de los pasos de eje) en la caja.
* `paridad_cubo`, `adyacencia_particion` : cada arista cambia la paridad, así que
  `H_PP = H_QQ = 0` en el cubo abierto real.
* `det_cubo_schur` : el complemento de Schur exacto con la adyacencia del producto caja.
* `dosPasos_eq` : `H_PQ H_QP = A²` sobre las posiciones pares (caminos de dos pasos).
* `tension_parteFCC_dosPasos` : la parte FCC no carga tensión con ese transporte.
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

/-! ## El cubo abierto como grafo de Mathlib

El transporte del cubo abierto es la adyacencia del producto caja de tres caminos,
`pathGraph Nx □ (pathGraph Ny □ pathGraph Nz)`: en cada eje es el salto de la cadena abierta
(`inner_openHamiltonian_eq_adjMatrix`, Physlib #2096). Sus aristas son las del grafo de Cayley
de los pasos de eje vistas en la caja, cada arista cambia la paridad, y por eso `H_PP = H_QQ = 0`
es un teorema del cubo, no una hipótesis: el complemento de Schur es exacto. -/

open SimpleGraph Matrix

/-- Copia local de la instancia de la rama `feat-cube-adjacency` (Mathlib aún no la tiene). -/
instance {α β : Type*} [DecidableEq α] [DecidableEq β] {G : SimpleGraph α} {H : SimpleGraph β}
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (G □ H).Adj :=
  fun _ _ => decidable_of_iff' _ boxProd_adj

/-- El cubo abierto: el producto caja de los tres caminos de Mathlib. -/
abbrev cubo : SimpleGraph (Fin Tx.N × Fin Ty.N × Fin Tz.N) :=
  pathGraph Tx.N □ (pathGraph Ty.N □ pathGraph Tz.N)

/-- Las coordenadas enteras de una posición de la caja. -/
def coord (p : Fin Tx.N × Fin Ty.N × Fin Tz.N) : Fin 3 → ℤ :=
  ![((p.1 : ℕ) : ℤ), ((p.2.1 : ℕ) : ℤ), ((p.2.2 : ℕ) : ℤ)]

/-- **El cubo abierto es la red cúbica vista en la caja**: dos posiciones son vecinas en el
producto caja de los caminos si y solo si sus coordenadas son vecinas en el grafo de Cayley de
los pasos de eje. -/
lemma cubo_adj_iff (p q : Fin Tx.N × Fin Ty.N × Fin Tz.N) :
    (cubo Tx Ty Tz).Adj p q ↔ redCubica.Adj (coord Tx Ty Tz p) (coord Tx Ty Tz q) := by
  rw [← mem_vecinos_iff_adj]
  obtain ⟨x, y, z⟩ := p
  obtain ⟨x', y', z'⟩ := q
  simp only [vecinos, Finset.mem_image, Finset.mem_univ, true_and, cubo, boxProd_adj,
    pathGraph_adj, Prod.mk.injEq, Fin.ext_iff]
  constructor
  · rintro (⟨hx | hx, hy, hz⟩ | ⟨(⟨hy | hy, hz⟩ | ⟨hz | hz, hy⟩), hx⟩)
    all_goals first
      | (refine ⟨(0, true), ?_⟩; funext i; fin_cases i <;>
          simp [coord, CondensedMatter.Crystal.axisStep] <;> omega)
      | (refine ⟨(0, false), ?_⟩; funext i; fin_cases i <;>
          simp [coord, CondensedMatter.Crystal.axisStep] <;> omega)
      | (refine ⟨(1, true), ?_⟩; funext i; fin_cases i <;>
          simp [coord, CondensedMatter.Crystal.axisStep] <;> omega)
      | (refine ⟨(1, false), ?_⟩; funext i; fin_cases i <;>
          simp [coord, CondensedMatter.Crystal.axisStep] <;> omega)
      | (refine ⟨(2, true), ?_⟩; funext i; fin_cases i <;>
          simp [coord, CondensedMatter.Crystal.axisStep] <;> omega)
      | (refine ⟨(2, false), ?_⟩; funext i; fin_cases i <;>
          simp [coord, CondensedMatter.Crystal.axisStep] <;> omega)
  · rintro ⟨⟨i, s⟩, h⟩
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    fin_cases i <;> cases s <;> simp [coord, CondensedMatter.Crystal.axisStep] at h0 h1 h2 <;>
      omega

/-- **Cada arista del cubo cambia la paridad** de `x + y + z`. -/
lemma paridad_cubo {p q : Fin Tx.N × Fin Ty.N × Fin Tz.N} (h : (cubo Tx Ty Tz).Adj p q) :
    ¬ (Even ((p.1 : ℕ) + p.2.1 + p.2.2) ↔ Even ((q.1 : ℕ) + q.2.1 + q.2.2)) := by
  obtain ⟨x, y, z⟩ := p
  obtain ⟨x', y', z'⟩ := q
  simp only [cubo, boxProd_adj, pathGraph_adj, Prod.mk.injEq] at h
  simp only [Nat.even_iff]
  rcases h with ⟨hx, rfl, rfl⟩ | ⟨⟨hy, rfl⟩ | ⟨hz, rfl⟩, rfl⟩ <;> omega

/-- Las posiciones de suma impar: `Q` en la partición de FCC. -/
abbrev ImparFCC :=
  {p : Fin Tx.N × Fin Ty.N × Fin Tz.N // ¬ Even ((p.1 : ℕ) + p.2.1 + p.2.2)}

/-- La partición par/impar de la caja. -/
def particion : ParFCC Tx Ty Tz ⊕ ImparFCC Tx Ty Tz ≃ Fin Tx.N × Fin Ty.N × Fin Tz.N :=
  Equiv.sumCompl _

/-- La adyacencia del cubo abierto. -/
noncomputable abbrev adyacencia : Matrix (Fin Tx.N × Fin Ty.N × Fin Tz.N)
    (Fin Tx.N × Fin Ty.N × Fin Tz.N) ℂ :=
  (cubo Tx Ty Tz).adjMatrix ℂ

/-- El bloque `H_PQ`: de las posiciones pares a las impares. -/
noncomputable abbrev bloquePQ : Matrix (ParFCC Tx Ty Tz) (ImparFCC Tx Ty Tz) ℂ :=
  (adyacencia Tx Ty Tz).submatrix Subtype.val Subtype.val

/-- El bloque `H_QP`: de las posiciones impares a las pares. -/
noncomputable abbrev bloqueQP : Matrix (ImparFCC Tx Ty Tz) (ParFCC Tx Ty Tz) ℂ :=
  (adyacencia Tx Ty Tz).submatrix Subtype.val Subtype.val

lemma adyacencia_eq_zero {p q : Fin Tx.N × Fin Ty.N × Fin Tz.N}
    (h : Even ((p.1 : ℕ) + p.2.1 + p.2.2) ↔ Even ((q.1 : ℕ) + q.2.1 + q.2.2)) :
    adyacencia Tx Ty Tz p q = 0 := by
  rw [adyacencia, adjMatrix_apply, ite_eq_right_iff]
  exact fun hpq => (paridad_cubo Tx Ty Tz hpq h).elim

/-- **`H_PP = H_QQ = 0` en el cubo abierto**: en la partición par/impar la adyacencia es
`fromBlocks 0 H_PQ H_QP 0`. -/
lemma adyacencia_particion :
    (adyacencia Tx Ty Tz).submatrix (particion Tx Ty Tz) (particion Tx Ty Tz) =
      fromBlocks 0 (bloquePQ Tx Ty Tz) (bloqueQP Tx Ty Tz) 0 := by
  ext (i | i) (j | j)
  · exact adyacencia_eq_zero Tx Ty Tz (iff_of_true i.2 j.2)
  · rfl
  · rfl
  · exact adyacencia_eq_zero Tx Ty Tz (iff_of_false i.2 j.2)

/-- **El complemento de Schur del cubo abierto es exacto**:
`det (E − A) = E^|Q| · det (E − H_PQ H_QP / E)` con `A` la adyacencia del producto caja. -/
theorem det_cubo_schur {E : ℂ} (hE : E ≠ 0) :
    (E • (1 : Matrix (Fin Tx.N × Fin Ty.N × Fin Tz.N) _ ℂ) - adyacencia Tx Ty Tz).det =
      E ^ Fintype.card (ImparFCC Tx Ty Tz) *
        (E • (1 : Matrix (ParFCC Tx Ty Tz) (ParFCC Tx Ty Tz) ℂ) -
          E⁻¹ • (bloquePQ Tx Ty Tz * bloqueQP Tx Ty Tz)).det := by
  have h : (E • (1 : Matrix (Fin Tx.N × Fin Ty.N × Fin Tz.N) _ ℂ) -
      adyacencia Tx Ty Tz).submatrix (particion Tx Ty Tz) (particion Tx Ty Tz) =
      E • (1 : Matrix (ParFCC Tx Ty Tz ⊕ ImparFCC Tx Ty Tz) _ ℂ) -
        fromBlocks 0 (bloquePQ Tx Ty Tz) (bloqueQP Tx Ty Tz) 0 := by
    rw [← adyacencia_particion]
    ext i j
    simp [one_apply, (particion Tx Ty Tz).injective.eq_iff]
  rw [← det_submatrix_equiv_self (particion Tx Ty Tz), h]
  exact det_sub_bipartita _ _ hE

/-- **`H_PQ H_QP` es `A²` sobre las posiciones pares**: los pasos intermedios pares no cuentan
porque la adyacencia entre dos pares es `0`. Por `SimpleGraph.adjMatrix_pow_apply_eq_card_walk`
(Mathlib), la entrada `(p, q)` de `A²` es el número de caminos de largo `2` de `p` a `q` en el
cubo abierto: las palabras de dos pasos de eje. -/
lemma dosPasos_eq (p q : ParFCC Tx Ty Tz) :
    (bloquePQ Tx Ty Tz * bloqueQP Tx Ty Tz) p q = (adyacencia Tx Ty Tz ^ 2) p.1 q.1 := by
  have hpar : ∑ w : ParFCC Tx Ty Tz,
      adyacencia Tx Ty Tz p.1 w.1 * adyacencia Tx Ty Tz w.1 q.1 = 0 :=
    Finset.sum_eq_zero fun w _ => by
      rw [adyacencia_eq_zero Tx Ty Tz (iff_of_true p.2 w.2), zero_mul]
  conv_rhs => rw [sq, mul_apply, ← Fintype.sum_subtype_add_sum_subtype
    (fun w : Fin Tx.N × Fin Ty.N × Fin Tz.N => Even ((w.1 : ℕ) + w.2.1 + w.2.2))]
  rw [hpar, zero_add, mul_apply]
  rfl

lemma im_adyacencia (p q : Fin Tx.N × Fin Ty.N × Fin Tz.N) : (adyacencia Tx Ty Tz p q).im = 0 := by
  rw [adyacencia, adjMatrix_apply]
  split_ifs <;> simp

/-- **La parte FCC no carga tensión con el transporte de dos pasos del cubo abierto**
`H_PQ H_QP`, para toda posición real. -/
lemma tension_parteFCC_dosPasos {X : Matrix (ParFCC Tx Ty Tz) (ParFCC Tx Ty Tz) ℂ}
    (hX : ∀ i j, (X i j).im = 0) :
    tension (bloquePQ Tx Ty Tz * bloqueQP Tx Ty Tz) X (parteFCC Tx Ty Tz) = 0 := by
  refine tension_parteFCC_eq_zero Tx Ty Tz (fun i j => ?_) hX
  simp only [mul_apply, submatrix_apply, Complex.im_sum, Complex.mul_im, im_adyacencia,
    mul_zero, zero_mul, add_zero, Finset.sum_const_zero]

end NRS3Cristales
