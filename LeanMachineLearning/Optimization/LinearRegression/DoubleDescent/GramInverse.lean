/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.RandomFeatures
public import LeanMachineLearning.ForMathlib.LinearAlgebra.Matrix.GramProjector

/-!
# Deterministic reductions for Gaussian random-feature regression

The purely linear-algebraic half of the random-matrix input to double descent (Milestone 7b of
the plan; [Bach, 2024]; [Hastie et al., 2022]; [Belkin et al., 2019]). Nothing here is
probabilistic: these lemmas reduce the random quantities `Tr ((Zᵀ Z)⁻¹ Sᵀ S)` and
`‖(M X - 1) θ⋆‖²` of the random-feature estimator `θ̂ = M y`, `M = S (Zᵀ Z)⁻¹ Zᵀ`, `Z = X S`, to
statements about a standard Gaussian matrix `G = X Q` that Gaussian invariance can then handle.

* `exists_orthonormal_factor`: `S = Q R` with `Qᵀ Q = 1` and `R` invertible and symmetric, from
  `Sᵀ S` invertible
  (`R = √(Sᵀ S)`, `Q = S R⁻¹`; no Gram-Schmidt, no triangularity);
* `trace_inv_gram_mul_gram_of_factor`: `Tr ((Zᵀ Z)⁻¹ Sᵀ S) = Tr ((Gᵀ G)⁻¹)`: the feature covariance
  cancels, so only identity-covariance Wishart matrices are ever needed;
* `bias_eq_omitted_add_fit_error`: `‖(M X - 1) θ‖² = ‖θ⊥‖² + ‖(Gᵀ G)⁻¹ Gᵀ X θ⊥‖²`, with
  `θ⊥ = θ - Q Qᵀ θ` the part of `θ` outside `range S`
  (`operator_eq_orthonormal_frame`: `M = Q (Gᵀ G)⁻¹ Gᵀ`);
* `isUnit_det_gram_iff_injective`, `isUnit_det_gram_submatrix_ne`: full column rank, and its
  inheritance by a submatrix with one column deleted;
* `inv_gram_apply_self`, `inv_gram_apply_ne`: **dual-vector formula**
  `((Zᵀ Z)⁻¹)ⱼⱼ = ‖(1 - P_{Zⱼ}) zⱼ‖⁻²` and `((Zᵀ Z)⁻¹)ᵢⱼ = - βᵢ ((Zᵀ Z)⁻¹)ⱼⱼ` with `P_{Zⱼ}` the
  `Matrix.gramProjector` of `Z` without column `j` and `β` the regression of `zⱼ` on the other columns;
* `trace_inv_gram_mul_self`: `Tr ((Zᵀ Z)⁻²) = ∑ⱼ ((Zᵀ Z)⁻¹)ⱼⱼ² (1 + ‖βⱼ‖²)`.

For a Gaussian `G`, the dual-vector formula makes `((Gᵀ G)⁻¹)ⱼⱼ` an exact inverse `χ²_{p-q+1}`
variable, which is the engine of Milestone 7c-7e.
-/

@[expose]
public section

namespace LinearRegression.DoubleDescent

open Matrix
open scoped MatrixOrder

variable {m n n₀ : Type*} [Fintype m] [Fintype n] [Fintype n₀] [DecidableEq n]

/-- **Orthonormal frame of a full-column-rank matrix.** If `Sᵀ S` is invertible, then `S = Q R`
with `Qᵀ Q = 1` and `R` invertible and symmetric (`R = √(Sᵀ S)`, so `Rᵀ R = R R = Sᵀ S`).

Proof: take `R = √(Sᵀ S)` (`CFC.sqrt`, symmetric with `R R = Sᵀ S`) and `Q = S R⁻¹`; then
`Qᵀ Q = R⁻¹ (Sᵀ S) R⁻¹ = 1`. No Gram-Schmidt and no triangularity are needed, since only
`Rᵀ R = Sᵀ S` is ever used downstream. -/
theorem exists_orthonormal_factor (S : Matrix n₀ n ℝ) (hS : IsUnit (Sᵀ * S).det) :
    ∃ (Q : Matrix n₀ n ℝ) (R : Matrix n n ℝ), Qᵀ * Q = 1 ∧ IsUnit R.det ∧ Rᵀ = R ∧
      S = Q * R := by
  have hpsd : 0 ≤ Sᵀ * S := by
    rw [Matrix.nonneg_iff_posSemidef]
    simpa using Matrix.posSemidef_conjTranspose_mul_self S
  set R : Matrix n n ℝ := CFC.sqrt (Sᵀ * S) with hR
  have hRR : R * R = Sᵀ * S := CFC.sqrt_mul_sqrt_self _ hpsd
  have hRT : Rᵀ = R := by
    have := (CFC.sqrt_nonneg (Sᵀ * S)).isSelfAdjoint
    simpa [IsSelfAdjoint, Matrix.star_eq_conjTranspose] using this
  have hdet : IsUnit R.det := by
    have : IsUnit (R.det * R.det) := by rw [← det_mul, hRR]; exact hS
    exact (isUnit_mul_self_iff.mp this)
  refine ⟨S * R⁻¹, R, ?_, hdet, hRT, ?_⟩
  · have hRinvT : (R⁻¹)ᵀ = R⁻¹ := by rw [transpose_nonsing_inv, hRT]
    have hinv : R⁻¹ * R = 1 := nonsing_inv_mul _ hdet
    calc (S * R⁻¹)ᵀ * (S * R⁻¹) = R⁻¹ * (Sᵀ * S) * R⁻¹ := by
          rw [transpose_mul, hRinvT, Matrix.mul_assoc, ← Matrix.mul_assoc Sᵀ, ← Matrix.mul_assoc,
            Matrix.mul_assoc R⁻¹, Matrix.mul_assoc]
      _ = 1 := by rw [← hRR, ← Matrix.mul_assoc, hinv, Matrix.one_mul, mul_nonsing_inv _ hdet]
  · rw [Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.mul_one]

/-- **QR trace reduction.** Let `S = Q R` with orthonormal columns `Qᵀ Q = 1` and `R` invertible,
and put `G = X Q`, `Z = X S = G R`. Then `Tr ((Zᵀ Z)⁻¹ Sᵀ S) = Tr ((Gᵀ G)⁻¹)`: the feature
covariance `Sᵀ S = Rᵀ R` cancels exactly against `Zᵀ Z = Rᵀ (Gᵀ G) R`. No invertibility of `Gᵀ G`
is needed (both sides use Mathlib's `⁻¹`, which obeys `(A B)⁻¹ = B⁻¹ A⁻¹` unconditionally). -/
theorem trace_inv_gram_mul_gram_of_factor {m n n₀ : Type*} [Fintype m] [Fintype n] [Fintype n₀]
    [DecidableEq n] (X : Matrix m n₀ ℝ) (Q : Matrix n₀ n ℝ) (R : Matrix n n ℝ)
    (hQ : Qᵀ * Q = 1) (hR : IsUnit R.det) :
    trace (((X * (Q * R))ᵀ * (X * (Q * R)))⁻¹ * ((Q * R)ᵀ * (Q * R))) =
      trace (((X * Q)ᵀ * (X * Q))⁻¹) := by
  have hRT : IsUnit Rᵀ.det := isUnit_det_transpose _ hR
  have hS : (Q * R)ᵀ * (Q * R) = Rᵀ * R := by
    rw [transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Qᵀ, hQ, Matrix.one_mul]
  have hZ : (X * (Q * R))ᵀ * (X * (Q * R)) = Rᵀ * ((X * Q)ᵀ * (X * Q)) * R := by
    simp only [← Matrix.mul_assoc, transpose_mul]
  rw [hS, hZ, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Rᵀ⁻¹, nonsing_inv_mul _ hRT, Matrix.one_mul, trace_mul_comm,
    Matrix.mul_assoc, mul_nonsing_inv _ hR, Matrix.mul_one]


/-- `Z` has trivial kernel iff its Gram matrix is invertible (`Zᵀ Z v = 0 → ‖Z v‖² = 0`). -/
theorem isUnit_det_gram_iff_injective {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (Z : Matrix m n ℝ) : IsUnit (Zᵀ * Z).det ↔ Function.Injective Z.mulVec := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
  constructor
  · intro h v w hvw
    apply h
    simp only [← Matrix.mulVec_mulVec, hvw]
  · intro h v w hvw
    have hd : (Zᵀ * Z) *ᵥ (v - w) = 0 := by rw [mulVec_sub, hvw, sub_self]
    have h0 : Z *ᵥ (v - w) ⬝ᵥ Z *ᵥ (v - w) = 0 := by
      have : (v - w) ⬝ᵥ (Zᵀ *ᵥ (Z *ᵥ (v - w))) = Z *ᵥ (v - w) ⬝ᵥ Z *ᵥ (v - w) := by
        rw [dotProduct_mulVec, vecMul_transpose]
      rw [← this, Matrix.mulVec_mulVec, hd, dotProduct_zero]
    have h1 : Z *ᵥ (v - w) = Z *ᵥ 0 := by rw [dotProduct_self_eq_zero.mp h0, mulVec_zero]
    exact sub_eq_zero.mp (h h1)


section DeleteColumn

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

private lemma sum_eq_apply_add_sum_ne (f : n → ℝ) (j : n) :
    ∑ i, f i = f j + ∑ i : {k // k ≠ j}, f i := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  congr 1
  exact Finset.sum_subtype _ (by simp) f

/-- Extension by zero of a vector indexed by `{k // k ≠ j}` to a vector indexed by `n`. -/
private def extendNe (j : n) (v : {k // k ≠ j} → ℝ) : n → ℝ :=
  fun i => if h : i = j then 0 else v ⟨i, h⟩

omit [Fintype m] in
private lemma mulVec_extendNe (Z : Matrix m n ℝ) (j : n) (v : {k // k ≠ j} → ℝ) :
    Z *ᵥ extendNe j v = (Z.submatrix id (Subtype.val : {k // k ≠ j} → n)) *ᵥ v := by
  ext a
  simp only [mulVec, dotProduct, submatrix_apply, id]
  rw [sum_eq_apply_add_sum_ne _ j]
  have h0 : extendNe j v j = 0 := by simp [extendNe]
  have h1 : ∀ x : {k // k ≠ j}, extendNe j v x = v x := fun x => by simp [extendNe, x.2]
  simp only [h0, h1, mul_zero, zero_add]

/-- Deleting a column of a full-column-rank matrix keeps it of full column rank. -/
theorem isUnit_det_gram_submatrix_ne (Z : Matrix m n ℝ) (hZ : IsUnit (Zᵀ * Z).det) (j : n) :
    IsUnit ((Z.submatrix id (Subtype.val : {k // k ≠ j} → n))ᵀ *
      (Z.submatrix id (Subtype.val : {k // k ≠ j} → n))).det := by
  rw [isUnit_det_gram_iff_injective] at hZ ⊢
  intro v w hvw
  have := hZ (a₁ := extendNe j v) (a₂ := extendNe j w)
    (by simpa only [mulVec_extendNe] using hvw)
  funext i
  have := congrFun this i.1
  simpa [extendNe, i.2] using this

/-- **Dual-vector formula (core).** Let `Zⱼ` be `Z` without column `j`, `β = (Zⱼᵀ Zⱼ)⁻¹ Zⱼᵀ zⱼ` the
least-squares coefficients of column `zⱼ` on the others, and `r = zⱼ - Zⱼ β = (1 - P_{Zⱼ}) zⱼ` the
residual. Then `r` solves the normal equations for the vector `e_j`: `Zᵀ r = ‖r‖² e_j`, and
`r = Z c` with `c = e_j - extendNe β`. Applying `(Zᵀ Z)⁻¹` gives `c = ‖r‖² (Zᵀ Z)⁻¹ e_j`. -/
private theorem dual_core (Z : Matrix m n ℝ) (hZ : IsUnit (Zᵀ * Z).det) (j : n) :
    let Zj := Z.submatrix id (Subtype.val : {k // k ≠ j} → n)
    let β := ((Zjᵀ * Zj)⁻¹ * Zjᵀ) *ᵥ Z.col j
    let r := Z.col j - Zj *ᵥ β
    Pi.single j 1 - extendNe j β = (r ⬝ᵥ r) • ((Zᵀ * Z)⁻¹ *ᵥ Pi.single j 1) := by
  intro Zj β r
  have hZj : IsUnit (Zjᵀ * Zj).det := isUnit_det_gram_submatrix_ne Z hZ j
  have F1 : Zjᵀ *ᵥ r = 0 := by
    have := transpose_mulVec_residual_leftInverse Zj hZj (Z.col j)
    have hr : r = -(Zj *ᵥ β - Z.col j) := by simp [r]
    rw [hr, mulVec_neg, this, neg_zero]
  have F2 : Zᵀ *ᵥ r = (r ⬝ᵥ r) • Pi.single j 1 := by
    funext i
    by_cases hi : i = j
    · subst hi
      have h0 : (Zj *ᵥ β) ⬝ᵥ r = 0 := by
        rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, F1, zero_dotProduct]
      have hc : Z.col i = r + Zj *ᵥ β := by simp [r]
      have : (Zᵀ *ᵥ r) i = Z.col i ⬝ᵥ r := rfl
      rw [this, hc, add_dotProduct, h0, add_zero]
      simp
    · have : (Zᵀ *ᵥ r) i = (Zjᵀ *ᵥ r) ⟨i, hi⟩ := rfl
      rw [this, F1]
      simp [hi]
  have F3 : Z *ᵥ (Pi.single j 1 - extendNe j β) = r := by
    rw [mulVec_sub, mulVec_single_one, mulVec_extendNe]
  have key : (Zᵀ * Z) *ᵥ (Pi.single j 1 - extendNe j β) = (r ⬝ᵥ r) • Pi.single j 1 := by
    rw [← mulVec_mulVec, F3, F2]
  calc Pi.single j 1 - extendNe j β
      = (Zᵀ * Z)⁻¹ *ᵥ ((Zᵀ * Z) *ᵥ (Pi.single j 1 - extendNe j β)) := by
        rw [mulVec_mulVec, nonsing_inv_mul _ hZ, one_mulVec]
    _ = _ := by rw [key, mulVec_smul]

/-- **Diagonal of the inverse Gram matrix (dual-vector formula).** If `Zᵀ Z` is invertible and
`Zⱼ` is `Z` without column `j`, then
`((Zᵀ Z)⁻¹)ⱼⱼ = 1 / ‖(1 - P_{Zⱼ}) zⱼ‖²`, the reciprocal squared distance from column `zⱼ` to the
span of the other columns (Lemma 3.3 of the plan's notes; no block reindexing). -/
theorem inv_gram_apply_self [DecidableEq m] (Z : Matrix m n ℝ) (hZ : IsUnit (Zᵀ * Z).det) (j : n) :
    (Zᵀ * Z)⁻¹ j j =
      (((1 - Matrix.gramProjector (Z.submatrix id (Subtype.val : {k // k ≠ j} → n))) *ᵥ Z.col j) ⬝ᵥ
        ((1 - Matrix.gramProjector (Z.submatrix id (Subtype.val : {k // k ≠ j} → n))) *ᵥ
          Z.col j))⁻¹ := by
  have h := congrFun (dual_core Z hZ j) j
  rw [Matrix.one_sub_gramProjector_mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply, mulVec_single_one, col_apply, smul_eq_mul,
    extendNe, Pi.single_eq_same, dite_true, sub_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- **Off-diagonal entries of the inverse Gram matrix.** With `β = (Zⱼᵀ Zⱼ)⁻¹ Zⱼᵀ zⱼ` the
least-squares coefficients of column `j` on the others, for `i ≠ j`,
`((Zᵀ Z)⁻¹)ᵢⱼ = - βᵢ · ((Zᵀ Z)⁻¹)ⱼⱼ`. -/
theorem inv_gram_apply_ne (Z : Matrix m n ℝ) (hZ : IsUnit (Zᵀ * Z).det) {i j : n}
    (hij : i ≠ j) :
    (Zᵀ * Z)⁻¹ i j =
      -((((Z.submatrix id (Subtype.val : {k // k ≠ j} → n))ᵀ *
          (Z.submatrix id (Subtype.val : {k // k ≠ j} → n)))⁻¹ *
          (Z.submatrix id (Subtype.val : {k // k ≠ j} → n))ᵀ) *ᵥ Z.col j) ⟨i, hij⟩ *
        (Zᵀ * Z)⁻¹ j j := by
  have h := congrFun (dual_core Z hZ j) i
  have hj := congrFun (dual_core Z hZ j) j
  simp only [Pi.sub_apply, Pi.smul_apply, mulVec_single_one, col_apply, smul_eq_mul, extendNe,
    Pi.single_eq_same, dite_true, sub_zero, Pi.single_eq_of_ne hij, hij, dite_false,
    zero_sub] at h hj
  linear_combination (Zᵀ * Z)⁻¹ i j * hj - (Zᵀ * Z)⁻¹ j j * h

/-- **`Tr (Zᵀ Z)⁻²` through the column regressions.** If `Zᵀ Z` is invertible, then
`Tr ((Zᵀ Z)⁻¹)² = ∑ⱼ ((Zᵀ Z)⁻¹)ⱼⱼ² (1 + ‖βⱼ‖²)`, where `βⱼ = (Zⱼᵀ Zⱼ)⁻¹ Zⱼᵀ zⱼ` are the
least-squares coefficients of column `j` on the others. By `inv_gram_apply_self`, the factor
`((Zᵀ Z)⁻¹)ⱼⱼ = ‖(1 - P_{Zⱼ}) zⱼ‖⁻²` depends on `zⱼ` only through the residual, while `βⱼ` depends
on `P_{Zⱼ} zⱼ`; this is the decomposition used for `E Tr (Gᵀ G)⁻²`. -/
theorem trace_inv_gram_mul_self (Z : Matrix m n ℝ) (hZ : IsUnit (Zᵀ * Z).det) :
    trace ((Zᵀ * Z)⁻¹ * (Zᵀ * Z)⁻¹) =
      ∑ j, (Zᵀ * Z)⁻¹ j j ^ 2 *
        (1 + (let Zj := Z.submatrix id (Subtype.val : {k // k ≠ j} → n)
          (((Zjᵀ * Zj)⁻¹ * Zjᵀ) *ᵥ Z.col j) ⬝ᵥ (((Zjᵀ * Zj)⁻¹ * Zjᵀ) *ᵥ Z.col j))) := by
  have hsymm : ((Zᵀ * Z)⁻¹)ᵀ = (Zᵀ * Z)⁻¹ := by
    rw [transpose_nonsing_inv, transpose_mul, transpose_transpose]
  have hcol : ∀ i j, (Zᵀ * Z)⁻¹ j i = (Zᵀ * Z)⁻¹ i j := fun i j => by
    conv_lhs => rw [← hsymm]
    rfl
  simp only [trace, diag_apply, mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hcol _ j, ← sq]
  rw [sum_eq_apply_add_sum_ne _ j]
  have hne : ∀ i : {k // k ≠ j}, (Zᵀ * Z)⁻¹ i j ^ 2 = (Zᵀ * Z)⁻¹ j j ^ 2 *
      (((((Z.submatrix id (Subtype.val : {k // k ≠ j} → n))ᵀ *
        (Z.submatrix id (Subtype.val : {k // k ≠ j} → n)))⁻¹ *
        (Z.submatrix id (Subtype.val : {k // k ≠ j} → n))ᵀ) *ᵥ Z.col j) i) ^ 2 := fun i => by
    rw [inv_gram_apply_ne Z hZ i.2]
    ring
  simp only [hne, ← Finset.mul_sum, dotProduct, sq]
  ring

end DeleteColumn

section Bias

variable {m n n₀ : Type*} [Fintype m] [Fintype n] [Fintype n₀] [DecidableEq n] [DecidableEq n₀]

omit [DecidableEq n₀] in
/-- **The random-feature operator in an orthonormal frame.** For `S = Q R` with `R` invertible,
`G = X Q` and `Z = X S = G R`, the operator `M = S (Zᵀ Z)⁻¹ Zᵀ` equals `Q (Gᵀ G)⁻¹ Gᵀ`: the
triangular factor `R` cancels. Only `R` must be invertible. -/
theorem operator_eq_orthonormal_frame (X : Matrix m n₀ ℝ) (Q : Matrix n₀ n ℝ) (R : Matrix n n ℝ)
    (hR : IsUnit R.det) :
    (Q * R) * (((X * (Q * R))ᵀ * (X * (Q * R)))⁻¹ * (X * (Q * R))ᵀ) =
      Q * (((X * Q)ᵀ * (X * Q))⁻¹ * (X * Q)ᵀ) := by
  have hRT : IsUnit Rᵀ.det := isUnit_det_transpose _ hR
  have hZ : (X * (Q * R))ᵀ * (X * (Q * R)) = Rᵀ * ((X * Q)ᵀ * (X * Q)) * R := by
    simp only [← Matrix.mul_assoc, transpose_mul]
  have hZt : (X * (Q * R))ᵀ = Rᵀ * (X * Q)ᵀ := by
    simp only [← Matrix.mul_assoc, transpose_mul]
  rw [hZ, hZt, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Rᵀ⁻¹, nonsing_inv_mul _ hRT, Matrix.one_mul, ← Matrix.mul_assoc R,
    mul_nonsing_inv _ hR, Matrix.one_mul]

/-- **Bias reduction (Pythagoras).** Let `S = Q R` with `Qᵀ Q = 1`, `R` invertible, `G = X Q` with
`H = Gᵀ G` invertible, and `M = S (Zᵀ Z)⁻¹ Zᵀ`, `Z = X S`, the random-feature operator. For
`θ⊥ = θ - Q Qᵀ θ`, the component of `θ` outside `range S`, put `w = H⁻¹ Gᵀ (X θ⊥)`. Then
`‖(M X - 1) θ‖² = ‖θ⊥‖² + ‖w‖²`.

The first term is the omitted signal and the second the error from fitting the noise-like
`X θ⊥`, which for Gaussian `X` is independent of `G`. Proof: `M = Q H⁻¹ Gᵀ`
(`operator_eq_orthonormal_frame`) gives `M G = Q`, so `(M X - 1) θ = Q w - θ⊥`, and `Q w ⟂ θ⊥`. -/
theorem bias_eq_omitted_add_fit_error (X : Matrix m n₀ ℝ) (Q : Matrix n₀ n ℝ) (R : Matrix n n ℝ)
    (hQ : Qᵀ * Q = 1) (hR : IsUnit R.det) (hG : IsUnit ((X * Q)ᵀ * (X * Q)).det)
    (M : Matrix n₀ m ℝ)
    (hM : M = (Q * R) * (((X * (Q * R))ᵀ * (X * (Q * R)))⁻¹ * (X * (Q * R))ᵀ))
    (θ θp : n₀ → ℝ) (hθp : θp = θ - Q *ᵥ (Qᵀ *ᵥ θ)) :
    (M * X - 1) *ᵥ θ ⬝ᵥ (M * X - 1) *ᵥ θ =
      θp ⬝ᵥ θp + (((X * Q)ᵀ * (X * Q))⁻¹ * (X * Q)ᵀ) *ᵥ (X *ᵥ θp) ⬝ᵥ
        (((X * Q)ᵀ * (X * Q))⁻¹ * (X * Q)ᵀ) *ᵥ (X *ᵥ θp) := by
  set w := (((X * Q)ᵀ * (X * Q))⁻¹ * (X * Q)ᵀ) *ᵥ (X *ᵥ θp) with hw
  have hM' : M = Q * (((X * Q)ᵀ * (X * Q))⁻¹ * (X * Q)ᵀ) := by
    rw [hM, operator_eq_orthonormal_frame X Q R hR]
  have hMG : M * (X * Q) = Q := by
    rw [hM', Matrix.mul_assoc, leftInverse_mul_self _ hG, Matrix.mul_one]
  have hQθp : Qᵀ *ᵥ θp = 0 := by
    rw [hθp, mulVec_sub, mulVec_mulVec, hQ, one_mulVec, sub_self]
  have hθ : θ = Q *ᵥ (Qᵀ *ᵥ θ) + θp := by rw [hθp]; abel
  have hu : (M * X - 1) *ᵥ θ = Q *ᵥ w - θp := by
    have hA : M *ᵥ (X *ᵥ (Q *ᵥ (Qᵀ *ᵥ θ))) = Q *ᵥ (Qᵀ *ᵥ θ) := by
      rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, hMG]
    have hB : M *ᵥ (X *ᵥ θp) = Q *ᵥ w := by
      rw [hM', hw]
      exact (mulVec_mulVec (X *ᵥ θp) Q (((X * Q)ᵀ * (X * Q))⁻¹ * (X * Q)ᵀ)).symm
    have h1 : M *ᵥ (X *ᵥ θ) = Q *ᵥ (Qᵀ *ᵥ θ) + Q *ᵥ w := by
      conv_lhs => rw [hθ]
      rw [mulVec_add, mulVec_add, hA, hB]
    rw [sub_mulVec, ← mulVec_mulVec, h1, one_mulVec]
    conv_lhs => rw [show Q *ᵥ (Qᵀ *ᵥ θ) + Q *ᵥ w - θ = Q *ᵥ w - θp from by rw [hθp]; abel]
  have hdot : ∀ (v : n → ℝ) (x : n₀ → ℝ), (Q *ᵥ v) ⬝ᵥ x = v ⬝ᵥ (Qᵀ *ᵥ x) := fun v x => by
    have : x ᵥ* Q = Qᵀ *ᵥ x := by simpa using vecMul_transpose Qᵀ x
    rw [dotProduct_comm, dotProduct_mulVec, this, dotProduct_comm]
  have h1 : (Q *ᵥ w) ⬝ᵥ (Q *ᵥ w) = w ⬝ᵥ w := by
    rw [hdot, mulVec_mulVec, hQ, one_mulVec]
  have h2 : (Q *ᵥ w) ⬝ᵥ θp = 0 := by rw [hdot, hQθp, dotProduct_zero]
  rw [hu, sub_dotProduct, dotProduct_sub, dotProduct_sub, h1, h2, dotProduct_comm θp (Q *ᵥ w), h2]
  ring

end Bias

end LinearRegression.DoubleDescent

end
