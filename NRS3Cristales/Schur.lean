/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under the NRS Noncommercial License as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Algebra.Order.Ring.Star

/-!
# El complemento de Schur del cubo: los vecinos de FCC y BCC son palabras de pasos de eje

El transporte del cubo es el paso de eje: `p ↦ p ± eᵢ`. Se separan las posiciones en dos
conjuntos, `P` (donde hay átomo) y `Q` (el resto del espacio), y el transporte en bloques
`H_PP, H_PQ, H_QP, H_QQ`. La dinámica efectiva sobre `P` es el complemento de Schur (Schur 1917)

  `H_eff(E) = H_PP + H_PQ (E − H_QQ)⁻¹ H_QP`.

* **FCC** (`P` = suma de coordenadas par). Cada paso de eje cambia la paridad, así que
  `H_PP = H_QQ = 0`, y el complemento es exacto, sin serie: `H_eff(E) = H_PQ H_QP / E`.
  Las entradas de `H_PQ H_QP` cuentan palabras de dos pasos de eje: `6` de regreso,
  `2` hacia cada `±eᵢ ± eⱼ` (la "diagonal de cara": `x` luego `y`, o `y` luego `x`) y `1` hacia
  cada `±2eᵢ`. No hay otra: `6 + 12·2 + 6·1 = 36 = 6²`.
* **BCC** (`P` = coordenadas de igual paridad). Hay pasos de eje dentro de `Q`, así que el
  complemento es una serie. A dos pasos solo se llega a `±2eᵢ`; la diagonal de cuerpo
  `(1, 1, 1)` no se alcanza en dos pasos y se alcanza en tres por `6` palabras. El orden por
  número de pasos invierte el orden euclídeo (`√3/2 < 1`).

Ningún vecino diagonal es primitivo: todos son palabras del único movimiento elemental, el paso
de eje (`D4_WhyNotDiagonal.minimal_adjacency_is_orthogonal`, `D22`).

Además, con transporte de entradas reales, un estado de amplitudes reales tiene tensión
`⟨i[T, X]⟩ = 0`. En `SchurCubo` se aplica a la parte par del estado de corriente máxima.

## Resultados principales

* `det_sub_bipartita` : `det (E − H) = E^|Q| · det (E − H_PQ H_QP / E)` si `H_PP = H_QQ = 0`.
* `schur_bipartita` : `H ψ = E ψ ⟺ ψ_Q = H_QP ψ_P / E ∧ H_PQ H_QP ψ_P = E² ψ_P`.
* `tension_eq_zero_of_real` : entradas reales y amplitudes reales ⇒ tensión `0`.
* `not_even_iff_of_mem_vecinos` : el paso de eje cambia la paridad (`H_PP = H_QQ = 0` en FCC).
* `palabras2_add` : el número de palabras solo depende del desplazamiento.
* `palabras2_regreso`, `palabras2_diagonalCara`, `palabras2_dobleEje`, `suma_palabras2` :
  los pesos `6`, `2`, `1` de FCC, y que no hay más.
* `palabras2_cuerpo`, `palabras3_cuerpo`, `palabras2_adyacentes_Q` : BCC.
* `card_pares_caja_tres`, `card_igualParidad_caja_tres` : la caja `3³` contiene la celda FCC
  (`14`) y la celda BCC (`9`); en `4³` son `32` y `16`.
-/

namespace NRS3Cristales

open Matrix

/-! ## A. El complemento de Schur de un transporte bipartito -/

section Bipartito

variable {K : Type*} [Field K] {m n : Type*} [DecidableEq m] [DecidableEq n]

/-- Un transporte sin bloques diagonales: `E − H` en bloques. -/
lemma smul_one_sub_bipartita (B : Matrix m n K) (C : Matrix n m K) (E : K) :
    E • (1 : Matrix (m ⊕ n) (m ⊕ n) K) - fromBlocks 0 B C 0 =
      fromBlocks (E • 1) (-B) (-C) (E • 1) := by
  ext (i | i) (j | j) <;> simp [one_apply]

/-- **El complemento de Schur de un transporte bipartito es exacto**:
`det (E − H) = E^|Q| · det (E − H_PQ H_QP / E)`. -/
lemma det_sub_bipartita [Fintype m] [Fintype n] (B : Matrix m n K) (C : Matrix n m K) {E : K} (hE : E ≠ 0) :
    (E • (1 : Matrix (m ⊕ n) (m ⊕ n) K) - fromBlocks 0 B C 0).det =
      E ^ Fintype.card n * (E • (1 : Matrix m m K) - E⁻¹ • (B * C)).det := by
  let _ : Invertible (E • (1 : Matrix n n K)) :=
    ⟨E⁻¹ • 1, by simp [smul_smul, hE], by simp [smul_smul, hE]⟩
  have hinv : ⅟(E • (1 : Matrix n n K)) = E⁻¹ • 1 := rfl
  rw [smul_one_sub_bipartita, det_fromBlocks₂₂, det_smul, det_one, mul_one, hinv]
  simp [Matrix.mul_smul, Matrix.smul_mul]

omit [DecidableEq m] [DecidableEq n] in
/-- Un autovector de un transporte bipartito, bloque por bloque. -/
lemma mulVec_bipartita_iff [Fintype m] [Fintype n] (B : Matrix m n K) (C : Matrix n m K) (u : m → K) (w : n → K)
    (E : K) :
    fromBlocks 0 B C 0 *ᵥ Sum.elim u w = E • Sum.elim u w ↔
      B *ᵥ w = E • u ∧ C *ᵥ u = E • w := by
  rw [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]
  simp only [zero_mulVec, zero_add, add_zero]
  constructor
  · intro h
    exact ⟨funext fun i => by simpa using congrFun h (Sum.inl i),
      funext fun j => by simpa using congrFun h (Sum.inr j)⟩
  · rintro ⟨h₁, h₂⟩
    funext i
    rcases i with i | j <;> simp [h₁, h₂]

omit [DecidableEq m] [DecidableEq n] in
/-- **Schur bipartito**: `H ψ = E ψ` si y solo si la parte en `Q` está fijada por la de `P`,
`ψ_Q = H_QP ψ_P / E`, y la parte en `P` es autovector de `H_PQ H_QP` con valor `E²`. -/
lemma schur_bipartita [Fintype m] [Fintype n] (B : Matrix m n K) (C : Matrix n m K) (u : m → K) (w : n → K)
    {E : K} (hE : E ≠ 0) :
    fromBlocks 0 B C 0 *ᵥ Sum.elim u w = E • Sum.elim u w ↔
      w = E⁻¹ • C *ᵥ u ∧ (B * C) *ᵥ u = E ^ 2 • u := by
  rw [mulVec_bipartita_iff, ← mulVec_mulVec]
  constructor
  · rintro ⟨hB, hC⟩
    refine ⟨by rw [hC, smul_smul, inv_mul_cancel₀ hE, one_smul], ?_⟩
    rw [hC, mulVec_smul, hB, smul_smul, sq]
  · rintro ⟨rfl, hBC⟩
    refine ⟨?_, by rw [smul_smul, mul_inv_cancel₀ hE, one_smul]⟩
    rw [mulVec_smul, hBC, smul_smul, sq, ← mul_assoc, inv_mul_cancel₀ hE, one_mul]

end Bipartito

/-! ## B. Con todo real, la tensión es cero -/

section Real

variable {ι : Type*} [Fintype ι]

/-- La tensión `⟨i[T, X]⟩ = Re ⟪v, i(TX − XT) v⟫` de un vector de amplitudes. -/
noncomputable def tension (T X : Matrix ι ι ℂ) (v : ι → ℂ) : ℝ :=
  (star v ⬝ᵥ ((Complex.I • (T * X - X * T)) *ᵥ v)).re

/-- Una matriz de entradas reales y un vector de amplitudes reales dan `⟪v, M v⟫` real. -/
lemma im_dotProduct_mulVec_eq_zero {M : Matrix ι ι ℂ} (hM : ∀ i j, (M i j).im = 0)
    {v : ι → ℂ} (hv : ∀ i, (v i).im = 0) : (star v ⬝ᵥ M *ᵥ v).im = 0 := by
  simp [dotProduct, mulVec, Complex.im_sum, Complex.mul_im, hM, hv]

/-- El producto de matrices de entradas reales tiene entradas reales. -/
lemma im_mul_eq_zero {T X : Matrix ι ι ℂ} (hT : ∀ i j, (T i j).im = 0)
    (hX : ∀ i j, (X i j).im = 0) (i j : ι) : ((T * X) i j).im = 0 := by
  simp [mul_apply, Complex.im_sum, Complex.mul_im, hT, hX]

/-- **Con transporte y posición reales, un estado de amplitudes reales tiene tensión `0`**:
la tensión vive en las fases relativas. Es la forma matricial de
`NearMaxTension.tension_eq_zero_of_real` (`D23b`). -/
lemma tension_eq_zero_of_real {T X : Matrix ι ι ℂ} (hT : ∀ i j, (T i j).im = 0)
    (hX : ∀ i j, (X i j).im = 0) {v : ι → ℂ} (hv : ∀ i, (v i).im = 0) :
    tension T X v = 0 := by
  have h := im_dotProduct_mulVec_eq_zero (M := T * X - X * T)
    (fun i j => by simp [Matrix.sub_apply, im_mul_eq_zero hT hX, im_mul_eq_zero hX hT]) hv
  rw [tension, smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re]
  simp [h]

end Real

/-! ## C. Palabras de pasos de eje en `ℤ³` -/

/-- Los seis vecinos de eje `v ± eᵢ`. -/
def vecinos (v : Fin 3 → ℤ) : Finset (Fin 3 → ℤ) :=
  (Finset.univ : Finset (Fin 3 × Bool)).image fun is => v + Pi.single is.1 (if is.2 then 1 else -1)

/-- El número de palabras de dos pasos de eje de `p` a `q`: la entrada `(p, q)` de `H²`. -/
def palabras2 (p q : Fin 3 → ℤ) : ℕ := ((vecinos p).filter fun w => q ∈ vecinos w).card

/-- El número de palabras de tres pasos de eje de `p` a `q`: la entrada `(p, q)` de `H³`. -/
def palabras3 (p q : Fin 3 → ℤ) : ℕ := ∑ w ∈ vecinos p, palabras2 w q

lemma vecinos_add (p v : Fin 3 → ℤ) : vecinos (p + v) = (vecinos v).image (p + ·) := by
  simp only [vecinos, Finset.image_image]
  congr 1
  funext is
  simp [add_assoc]

lemma add_mem_vecinos_add (p v q : Fin 3 → ℤ) : p + q ∈ vecinos (p + v) ↔ q ∈ vecinos v := by
  rw [vecinos_add, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, h⟩
    rwa [← add_left_cancel h]
  · exact fun h => ⟨q, h, rfl⟩

/-- **El número de palabras solo depende del desplazamiento.** -/
lemma palabras2_add (p v q : Fin 3 → ℤ) : palabras2 (p + v) (p + q) = palabras2 v q := by
  rw [palabras2, vecinos_add, Finset.filter_image, Finset.card_image_of_injective _
    (add_right_injective p)]
  simp only [add_mem_vecinos_add]
  rfl

/-- **El paso de eje cambia la paridad**: en la partición de FCC, `H_PP = H_QQ = 0`. -/
lemma not_even_iff_of_mem_vecinos {p q : Fin 3 → ℤ} (h : q ∈ vecinos p) :
    ¬ (Even (∑ i, p i) ↔ Even (∑ i, q i)) := by
  obtain ⟨⟨i, s⟩, -, rfl⟩ := Finset.mem_image.mp h
  simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ,
    ite_true]
  cases s <;> simp [Int.even_add, parity_simps] <;> rw [← Int.not_even_iff_odd] <;>
    exact iff_not_self

/-- Seis palabras de regreso: la coordinación del cubo, la diagonal de `H²`. -/
lemma palabras2_regreso : palabras2 0 0 = 6 := by decide

/-- **La "diagonal de cara" de FCC son dos palabras de eje**: `x` luego `y`, o `y` luego `x`. -/
lemma palabras2_diagonalCara :
    ∀ i j : Fin 3, i ≠ j → ∀ s t : Bool,
      palabras2 0 (Pi.single i (if s then 1 else -1) + Pi.single j (if t then 1 else -1)) = 2 := by
  decide

/-- **El doble paso por un eje es una sola palabra.** -/
lemma palabras2_dobleEje :
    ∀ i : Fin 3, ∀ s : Bool, palabras2 0 (Pi.single i (if s then 2 else -2)) = 1 := by
  decide

/-- Todas las palabras de dos pasos son `36 = 6 + 12·2 + 6·1`: no hay otro acoplamiento en
`H_PQ H_QP` que el regreso, las doce diagonales de cara y los seis dobles pasos. -/
lemma suma_palabras2 : ∑ w ∈ vecinos 0, (vecinos w).card = 6 + 12 * 2 + 6 * 1 := by decide

/-- BCC: la diagonal de cuerpo no se alcanza en dos pasos de eje. -/
lemma palabras2_cuerpo : palabras2 0 ![1, 1, 1] = 0 := by decide

/-- BCC: la diagonal de cuerpo se alcanza en tres pasos de eje, por `3! = 6` palabras. -/
lemma palabras3_cuerpo : palabras3 0 ![1, 1, 1] = 6 := by decide

/-- BCC: hay pasos de eje entre dos posiciones de `Q` (sin la misma paridad en sus tres
coordenadas), así que su complemento de Schur no es finito. -/
lemma palabras2_adyacentes_Q : ![1, 1, 0] ∈ vecinos ![1, 0, 0] := by decide

/-! ## D. Las cajas `3³` y `4³` -/

/-- Las posiciones de suma par de la caja `n³`. -/
def pares (n : ℕ) : Finset (Fin n × Fin n × Fin n) :=
  Finset.univ.filter fun p => Even ((p.1 : ℕ) + p.2.1 + p.2.2)

/-- Las posiciones de la caja `n³` con sus tres coordenadas de igual paridad. -/
def igualParidad (n : ℕ) : Finset (Fin n × Fin n × Fin n) :=
  Finset.univ.filter fun p =>
    (Even (p.1 : ℕ) ↔ Even (p.2.1 : ℕ)) ∧ (Even (p.2.1 : ℕ) ↔ Even (p.2.2 : ℕ))

/-- **La caja `3³` contiene la celda convencional FCC**: `8` esquinas y `6` centros de cara. -/
lemma card_pares_caja_tres : (pares 3).card = 14 := by decide

/-- **La caja `3³` contiene la celda convencional BCC**: `8` esquinas y el centro. -/
lemma card_igualParidad_caja_tres : (igualParidad 3).card = 9 := by decide

lemma card_pares_caja_cuatro : (pares 4).card = 32 := by decide

lemma card_igualParidad_caja_cuatro : (igualParidad 4).card = 16 := by decide

end NRS3Cristales
