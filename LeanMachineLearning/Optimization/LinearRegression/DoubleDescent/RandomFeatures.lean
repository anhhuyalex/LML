/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Foundations.GramProjector
public import LeanMachineLearning.Optimization.NTK.Shallow.DatasetNTK
public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.AffineDynamics

/-!
# Least-squares estimators on a projected design

For the random-feature design `Z = X S ∈ ℝ^{m × n}` (`m` samples, `n` random features) the fitted
feature coefficients are the least-squares solution of `Z η = y`, which is available in closed
form in the two full-rank regimes ([Bach, 2024]; [Hastie et al., 2022]; [Belkin et al., 2019]):

* **`m > n`, `Zᵀ Z` invertible** (feature bottleneck): the left inverse `(Zᵀ Z)⁻¹ Zᵀ y` is the
  *unique* minimizer of the empirical squared loss;
* **`m < n`, `Z Zᵀ` invertible** (sample bottleneck): the right inverse `Zᵀ (Z Zᵀ)⁻¹ y` is the
  *unique minimum-norm interpolator*.

No Moore–Penrose pseudoinverse is defined and no new loss or optimality predicate is introduced:
optimality is stated for the residual norm `‖Z η - y‖` and the interpolation constraint
`Z η = y`, by reusing `NTK.gramProjector` and `NTK.minNorm_pythagoras` (through
`NTK.affine_minNorm_pythagoras` / `NTK.eq_affine_limit_of_norm_le`). `mseLoss_linear` identifies
this residual with the NTK development's `NTK.mseLoss` of the linear model `z ↦ z ⬝ η`.

* `leftInverse_mul_self`, `self_mul_rightInverse`: the algebraic left/right inverse identities;
* `mseLoss_linear`: `NTK.mseLoss` of a linear model is `(2m)⁻¹ ‖Z η - y‖²`;
* `norm_sq_residual_eq_leftInverse_add`, `norm_sq_residual_leftInverse`, `leftInverse_isMinOn`,
  `eq_leftInverse_of_norm_residual_le`: the feature-bottleneck estimator is the unique minimizer,
  with minimum residual `‖(I - P_Z) y‖`;
* `rightInverse_interpolates`, `rightInverse_norm_sq_decomp`, `eq_rightInverse_of_norm_le`: the
  sample-bottleneck estimator interpolates and is the unique minimum-norm interpolator.
-/

@[expose]
public section

namespace LinearRegression.DoubleDescent

open Matrix NTK
open scoped Matrix RealInnerProductSpace

/-- **Left inverse.** If the Gram matrix `Zᵀ Z` is invertible (full column rank, `n ≤ m`), then
`(Zᵀ Z)⁻¹ Zᵀ` is a left inverse of `Z`. -/
theorem leftInverse_mul_self {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (Z : Matrix m n ℝ) (h : IsUnit (Zᵀ * Z).det) : ((Zᵀ * Z)⁻¹ * Zᵀ) * Z = 1 := by
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h]

/-- **Right inverse.** If `Z Zᵀ` is invertible (full row rank, `m ≤ n`), then `Zᵀ (Z Zᵀ)⁻¹` is a
right inverse of `Z`. -/
theorem self_mul_rightInverse {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (Z : Matrix m n ℝ) (h : IsUnit (Z * Zᵀ).det) : Z * (Zᵀ * (Z * Zᵀ)⁻¹) = 1 := by
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ h]

variable {m n : ℕ}

/-- **`NTK.mseLoss` of a linear model.** For the linear predictor `z ↦ z ⬝ η` on the rows of `Z`,
`L(η) = (2m)⁻¹ ‖Z η - y‖²`; so minimizers of `NTK.mseLoss` are exactly the minimizers of the
residual norm `‖Z η - y‖` studied below. -/
theorem mseLoss_linear (Z : Matrix (Fin m) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin m))
    (η : EuclideanSpace ℝ (Fin n)) :
    mseLoss (fun (z : Fin n → ℝ) (η : EuclideanSpace ℝ (Fin n)) => z ⬝ᵥ η.ofLp) Z y η =
      (2 * (m : ℝ))⁻¹ * ‖WithLp.toLp 2 (Z *ᵥ η.ofLp) - y‖ ^ 2 := rfl

section FeatureBottleneck

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

variable (Z : Matrix m n ℝ) (hZ : IsUnit (Zᵀ * Z).det)
  (y : EuclideanSpace ℝ m)

include hZ

/-- Normal equations: the residual of the left-inverse fit is orthogonal to the columns of `Z`,
`Zᵀ (Z η̂ - y) = 0` for `η̂ = (Zᵀ Z)⁻¹ Zᵀ y`. -/
private theorem transpose_mulVec_residual_leftInverse :
    Zᵀ *ᵥ (Z *ᵥ (((Zᵀ * Z)⁻¹ * Zᵀ) *ᵥ y.ofLp) - y.ofLp) = 0 := by
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hZ, Matrix.one_mul, sub_self]

/-- **Pythagoras for the left-inverse fit.** For the left-inverse coefficients
`η̂ = (Zᵀ Z)⁻¹ Zᵀ y`, every `η` has `‖Z η - y‖² = ‖Z η̂ - y‖² + ‖Z (η - η̂)‖²`, since the residual
`Z η̂ - y` is orthogonal to the range of `Z`. -/
theorem norm_sq_residual_eq_leftInverse_add (η : EuclideanSpace ℝ n) :
    ‖WithLp.toLp 2 (Z *ᵥ η.ofLp) - y‖ ^ 2 =
      ‖WithLp.toLp 2 (Z *ᵥ (((Zᵀ * Z)⁻¹ * Zᵀ) *ᵥ y.ofLp)) - y‖ ^ 2 +
        ‖(WithLp.toLp 2 (Z *ᵥ (η.ofLp - (((Zᵀ * Z)⁻¹ * Zᵀ) *ᵥ y.ofLp))) :
          EuclideanSpace ℝ m)‖ ^ 2 := by
  set a : EuclideanSpace ℝ m :=
    WithLp.toLp 2 (Z *ᵥ (((Zᵀ * Z)⁻¹ * Zᵀ) *ᵥ y.ofLp)) - y with ha
  set b : EuclideanSpace ℝ m :=
    WithLp.toLp 2 (Z *ᵥ (η.ofLp - (((Zᵀ * Z)⁻¹ * Zᵀ) *ᵥ y.ofLp))) with hb
  have hsplit : (WithLp.toLp 2 (Z *ᵥ η.ofLp) : EuclideanSpace ℝ m) - y = a + b := by
    ext i
    simp [ha, hb, Matrix.mulVec_sub]
  have horth : ⟪a, b⟫ = 0 := by
    have ha' : a.ofLp = Z *ᵥ (((Zᵀ * Z)⁻¹ * Zᵀ) *ᵥ y.ofLp) - y.ofLp := by simp [ha]
    rw [real_inner_eq_dotProduct, ha', hb, WithLp.ofLp_toLp, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, transpose_mulVec_residual_leftInverse Z hZ y, zero_dotProduct]
  rw [hsplit, norm_add_sq_real, horth]
  ring

omit hZ in
variable [DecidableEq m] in
/-- **The residual of the left-inverse fit is the orthogonal-projection residual:**
`‖Z η̂ - y‖ = ‖(I - P_Z) y‖` with `P_Z = Z (Zᵀ Z)⁻¹ Zᵀ` the Gram projector. -/
theorem norm_sq_residual_leftInverse :
    ‖WithLp.toLp 2 (Z *ᵥ (((Zᵀ * Z)⁻¹ * Zᵀ) *ᵥ y.ofLp)) - y‖ =
      ‖(WithLp.toLp 2 ((1 - gramProjector Z) *ᵥ y.ofLp) : EuclideanSpace ℝ m)‖ := by
  rw [← norm_neg (WithLp.toLp 2 ((1 - gramProjector Z) *ᵥ y.ofLp))]
  congr 1
  ext i
  simp [gramProjector, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]

/-- **Feature-bottleneck estimator is a global minimizer.** If `Zᵀ Z` is invertible, the
left-inverse coefficients `(Zᵀ Z)⁻¹ Zᵀ y` minimize the residual norm `‖Z η - y‖`, equivalently
`NTK.mseLoss` of the linear model (`mseLoss_linear`). -/
theorem leftInverse_isMinOn :
    IsMinOn (fun η : EuclideanSpace ℝ n => ‖WithLp.toLp 2 (Z *ᵥ η.ofLp) - y‖) Set.univ
      (WithLp.toLp 2 (((Zᵀ * Z)⁻¹ * Zᵀ) *ᵥ y.ofLp)) := isMinOn_iff.mpr fun η _ => by
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  rw [norm_sq_residual_eq_leftInverse_add Z hZ y η]
  exact le_add_of_nonneg_right (sq_nonneg _)

/-- **Feature-bottleneck estimator is the unique minimizer.** If `Zᵀ Z` is invertible, any
coefficient vector whose residual norm is at most that of `(Zᵀ Z)⁻¹ Zᵀ y` equals it, because `Z` is
injective. -/
theorem eq_leftInverse_of_norm_residual_le (η : EuclideanSpace ℝ n)
    (h : ‖WithLp.toLp 2 (Z *ᵥ η.ofLp) - y‖ ≤
      ‖WithLp.toLp 2 (Z *ᵥ (((Zᵀ * Z)⁻¹ * Zᵀ) *ᵥ y.ofLp)) - y‖) :
    η = WithLp.toLp 2 (((Zᵀ * Z)⁻¹ * Zᵀ) *ᵥ y.ofLp) := by
  have h2 := norm_sq_residual_eq_leftInverse_add Z hZ y η
  set v : n → ℝ := η.ofLp - ((Zᵀ * Z)⁻¹ * Zᵀ) *ᵥ y.ofLp with hv
  have hN : ‖(WithLp.toLp 2 (Z *ᵥ v) : EuclideanSpace ℝ m)‖ ^ 2 ≤ 0 := by
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) h 2]
  have hZv : Z *ᵥ v = 0 := by
    have := norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hN (sq_nonneg _)))
    simpa using congrArg WithLp.ofLp this
  have hv0 : v = 0 := by
    rw [← Matrix.one_mulVec v, ← leftInverse_mul_self Z hZ, ← Matrix.mulVec_mulVec, hZv,
      Matrix.mulVec_zero]
  ext i
  simpa [hv, sub_eq_zero] using congrFun hv0 i

end FeatureBottleneck

section SampleBottleneck

variable (Z : Matrix (Fin m) (Fin n) ℝ) (hZ : IsUnit (Z * Zᵀ).det)
  (y : EuclideanSpace ℝ (Fin m))

omit hZ in
/-- The right-inverse coefficients are `matrixCLM` applied to the target (the form used by the NTK
minimum-norm lemmas, with `r₀ = -y`). -/
private theorem matrixCLM_rightInverse :
    matrixCLM (-(Zᵀ * (Z * Zᵀ)⁻¹)) (-y) =
      WithLp.toLp 2 ((Zᵀ * (Z * Zᵀ)⁻¹) *ᵥ y.ofLp) := by
  ext i
  simp [matrixCLM_apply, Matrix.neg_mulVec, Matrix.mulVec_neg]

include hZ

/-- **Sample-bottleneck estimator interpolates.** If `Z Zᵀ` is invertible, the right-inverse
coefficients `Zᵀ (Z Zᵀ)⁻¹ y` fit the targets exactly: `Z (Zᵀ (Z Zᵀ)⁻¹ y) = y`. -/
theorem rightInverse_interpolates :
    Z *ᵥ ((Zᵀ * (Z * Zᵀ)⁻¹) *ᵥ y.ofLp) = y.ofLp := by
  rw [Matrix.mulVec_mulVec, self_mul_rightInverse Z hZ, Matrix.one_mulVec]

/-- **Pythagoras for the right-inverse interpolator.** If `Z Zᵀ` is invertible, every interpolator
`Z η = y` satisfies `‖η‖² = ‖η̂‖² + ‖η - η̂‖²` with `η̂ = Zᵀ (Z Zᵀ)⁻¹ y`. This is
`NTK.affine_minNorm_pythagoras` for `J = Z`, `r₀ = -y`. -/
theorem rightInverse_norm_sq_decomp {η : EuclideanSpace ℝ (Fin n)} (h : Z *ᵥ η.ofLp = y.ofLp) :
    ‖η‖ ^ 2 = ‖(WithLp.toLp 2 ((Zᵀ * (Z * Zᵀ)⁻¹) *ᵥ y.ofLp) : EuclideanSpace ℝ (Fin n))‖ ^ 2 +
      ‖η - WithLp.toLp 2 ((Zᵀ * (Z * Zᵀ)⁻¹) *ᵥ y.ofLp)‖ ^ 2 := by
  have h' := (affine_minNorm_pythagoras Z ((Matrix.isUnit_iff_isUnit_det _).2 hZ) (-y)
    (w' := η) (by simpa using h)).2
  rwa [matrixCLM_rightInverse Z y] at h'

/-- **Sample-bottleneck estimator is the unique minimum-norm interpolator.** If `Z Zᵀ` is
invertible, an interpolator `Z η = y` of norm at most `‖Zᵀ (Z Zᵀ)⁻¹ y‖` equals `Zᵀ (Z Zᵀ)⁻¹ y`.
This is `NTK.eq_affine_limit_of_norm_le`. -/
theorem eq_rightInverse_of_norm_le {η : EuclideanSpace ℝ (Fin n)} (h : Z *ᵥ η.ofLp = y.ofLp)
    (hle : ‖η‖ ≤ ‖(WithLp.toLp 2 ((Zᵀ * (Z * Zᵀ)⁻¹) *ᵥ y.ofLp) : EuclideanSpace ℝ (Fin n))‖) :
    η = WithLp.toLp 2 ((Zᵀ * (Z * Zᵀ)⁻¹) *ᵥ y.ofLp) := by
  rw [← matrixCLM_rightInverse Z y] at hle ⊢
  exact eq_affine_limit_of_norm_le Z ((Matrix.isUnit_iff_isUnit_det _).2 hZ) (-y)
    (by simpa using h) hle

end SampleBottleneck

end LinearRegression.DoubleDescent

end
