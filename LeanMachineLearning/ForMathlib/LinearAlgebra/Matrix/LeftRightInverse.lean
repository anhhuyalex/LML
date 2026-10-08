/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Left and right inverses of full-rank matrices, and the minimum-norm interpolator

For `Z : Matrix m n ℝ` with invertible Gram matrix, `(Zᵀ Z)⁻¹ Zᵀ` is a left inverse (full column
rank), and with `Z Zᵀ` invertible, `Zᵀ (Z Zᵀ)⁻¹` is a right inverse (full row rank). Stated for
arbitrary finite index types.

* `Matrix.leftInverse_mul_self`, `Matrix.leftInverse_mul_transpose`;
* `Matrix.self_mul_rightInverse`, `Matrix.rightInverse_interpolates`;
* `Matrix.rightInverse_norm_sq_decomp`, `Matrix.eq_rightInverse_of_norm_le`: Pythagoras for the
  right-inverse interpolator `η̂ = Zᵀ (Z Zᵀ)⁻¹ y`, so `η̂` is the unique minimum-norm solution of
  `Z η = y`.
-/

@[expose] public section

open scoped Matrix RealInnerProductSpace

namespace Matrix

/-- **Left inverse.** If the Gram matrix `Zᵀ Z` is invertible (full column rank, `n ≤ m`), then
`(Zᵀ Z)⁻¹ Zᵀ` is a left inverse of `Z`. -/
theorem leftInverse_mul_self {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (Z : Matrix m n ℝ) (h : IsUnit (Zᵀ * Z).det) : ((Zᵀ * Z)⁻¹ * Zᵀ) * Z = 1 := by
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h]

/-- The left-inverse operator `(Zᵀ Z)⁻¹ Zᵀ` has "covariance" `(Zᵀ Z)⁻¹`: with `A = (Zᵀ Z)⁻¹ Zᵀ`,
`A Aᵀ = (Zᵀ Z)⁻¹` (the inverse is symmetric). This is the matrix behind the OLS variance
`σ² Tr ((Zᵀ Z)⁻¹ Σ)`. -/
theorem leftInverse_mul_transpose {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (Z : Matrix m n ℝ) (h : IsUnit (Zᵀ * Z).det) :
    ((Zᵀ * Z)⁻¹ * Zᵀ) * ((Zᵀ * Z)⁻¹ * Zᵀ)ᵀ = (Zᵀ * Z)⁻¹ := by
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Zᵀ, Matrix.mul_nonsing_inv _ h,
    Matrix.mul_one]

/-- **Right inverse.** If `Z Zᵀ` is invertible (full row rank, `m ≤ n`), then `Zᵀ (Z Zᵀ)⁻¹` is a
right inverse of `Z`. -/
theorem self_mul_rightInverse {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (Z : Matrix m n ℝ) (h : IsUnit (Z * Zᵀ).det) : Z * (Zᵀ * (Z * Zᵀ)⁻¹) = 1 := by
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h]

/-- The right inverse `Z† = Zᵀ (Z Zᵀ)⁻¹` has Gram matrix `Z†ᵀ Z† = (Z Zᵀ)⁻¹`. -/
theorem rightInverse_transpose_mul_self {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (Z : Matrix m n ℝ) (h : IsUnit (Z * Zᵀ).det) :
    (Zᵀ * (Z * Zᵀ)⁻¹)ᵀ * (Zᵀ * (Z * Zᵀ)⁻¹) = (Z * Zᵀ)⁻¹ := by
  have hsymm : ((Z * Zᵀ)⁻¹)ᵀ = (Z * Zᵀ)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.transpose_mul, hsymm, Matrix.transpose_transpose]
  calc (Z * Zᵀ)⁻¹ * Z * (Zᵀ * (Z * Zᵀ)⁻¹)
      = (Z * Zᵀ)⁻¹ * ((Z * Zᵀ) * (Z * Zᵀ)⁻¹) := by simp only [Matrix.mul_assoc]
    _ = (Z * Zᵀ)⁻¹ := by rw [Matrix.mul_nonsing_inv _ h, Matrix.mul_one]

/-- **Right-inverse coefficients interpolate.** If `Z Zᵀ` is invertible, the coefficients
`Zᵀ (Z Zᵀ)⁻¹ y` fit any target exactly: `Z (Zᵀ (Z Zᵀ)⁻¹ y) = y`. Stated for arbitrary index types
and plain vectors, so that it also serves as the surjectivity of a full-row-rank `S`. -/
theorem rightInverse_interpolates {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (Z : Matrix m n ℝ) (hZ : IsUnit (Z * Zᵀ).det) (y : m → ℝ) :
    Z *ᵥ ((Zᵀ * (Z * Zᵀ)⁻¹) *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, self_mul_rightInverse Z hZ, Matrix.one_mulVec]

/-- **Pythagoras for the right-inverse interpolator.** If `Z Zᵀ` is invertible, every interpolator
`Z η = y` satisfies `‖η‖² = ‖η̂‖² + ‖η - η̂‖²` with `η̂ = Zᵀ (Z Zᵀ)⁻¹ y`: the difference
`η - η̂` lies in `ker Z`, which is orthogonal to `range Zᵀ ∋ η̂`. (`NTK.affine_minNorm_pythagoras`
is the case `J = Z`, `r₀ = -y`.) -/
theorem rightInverse_norm_sq_decomp {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (Z : Matrix m n ℝ) (hZ : IsUnit (Z * Zᵀ).det) (y : m → ℝ) {η : EuclideanSpace ℝ n}
    (h : Z *ᵥ η.ofLp = y) :
    ‖η‖ ^ 2 = ‖(WithLp.toLp 2 ((Zᵀ * (Z * Zᵀ)⁻¹) *ᵥ y) : EuclideanSpace ℝ n)‖ ^ 2 +
      ‖η - WithLp.toLp 2 ((Zᵀ * (Z * Zᵀ)⁻¹) *ᵥ y)‖ ^ 2 := by
  set ηh : EuclideanSpace ℝ n := WithLp.toLp 2 ((Zᵀ * (Z * Zᵀ)⁻¹) *ᵥ y) with hηh
  have hd : Z *ᵥ (η - ηh).ofLp = 0 := by
    simp [hηh, Matrix.mulVec_sub, h, rightInverse_interpolates Z hZ]
  have horth : ⟪ηh, η - ηh⟫ = 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    simp only [star_trivial]
    rw [hηh, WithLp.ofLp_toLp, dotProduct_comm, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
      Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mulVec_mulVec, hd,
      Matrix.mulVec_zero, zero_dotProduct]
  have hsplit : η = ηh + (η - ηh) := by abel
  conv_lhs => rw [hsplit]
  rw [norm_add_sq_real, horth]
  ring

/-- **The right-inverse fit is the unique minimum-norm interpolator.** If `Z Zᵀ` is invertible, an
interpolator `Z η = y` of norm at most `‖Zᵀ (Z Zᵀ)⁻¹ y‖` equals `Zᵀ (Z Zᵀ)⁻¹ y`. -/
theorem eq_rightInverse_of_norm_le {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (Z : Matrix m n ℝ) (hZ : IsUnit (Z * Zᵀ).det) (y : m → ℝ) {η : EuclideanSpace ℝ n}
    (h : Z *ᵥ η.ofLp = y)
    (hle : ‖η‖ ≤ ‖(WithLp.toLp 2 ((Zᵀ * (Z * Zᵀ)⁻¹) *ᵥ y) : EuclideanSpace ℝ n)‖) :
    η = WithLp.toLp 2 ((Zᵀ * (Z * Zᵀ)⁻¹) *ᵥ y) := by
  have h2 := rightInverse_norm_sq_decomp Z hZ y h
  have h3 : ‖η - WithLp.toLp 2 ((Zᵀ * (Z * Zᵀ)⁻¹) *ᵥ y)‖ ^ 2 ≤ 0 := by
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hle 2]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm h3 (sq_nonneg _))))

end Matrix

end
