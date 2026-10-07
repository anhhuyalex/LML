/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.LinearAlgebra.Matrix.LeftRightInverse
public import LeanMachineLearning.Optimization.LinearRegression.HMRT
public import LeanMachineLearning.Optimization.NTK.Foundations.GramProjector
public import LeanMachineLearning.Optimization.NTK.Shallow.DatasetNTK

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
`Z η = y`, by reusing `NTK.gramProjector` and `NTK.mseLoss`. `mseLoss_linear` identifies this
residual with the NTK development's `NTK.mseLoss` of the linear model `z ↦ z ⬝ η`.

* `leftInverse_mul_self`, `self_mul_rightInverse`: the algebraic left/right inverse identities;
* `mseLoss_linear`: `NTK.mseLoss` of a linear model is `(2m)⁻¹ ‖Z η - y‖²`;
* `norm_sq_residual_eq_leftInverse_add`, `norm_sq_residual_leftInverse`, `leftInverse_isMinOn`,
  `eq_leftInverse_of_norm_residual_le`: the feature-bottleneck estimator is the unique minimizer,
  with minimum residual `‖(I - P_Z) y‖`;
* `rightInverse_interpolates`, `rightInverse_norm_sq_decomp`, `eq_rightInverse_of_norm_le`: the
  sample-bottleneck estimator interpolates and is the unique minimum-norm interpolator (stated for
  arbitrary index types and plain target vectors).
-/

@[expose]
public section

namespace LinearRegression.DoubleDescent

open Matrix NTK
open scoped Matrix RealInnerProductSpace

variable {m n : ℕ}

/-- **`NTK.mseLoss` of a linear model.** For the linear predictor `z ↦ z ⬝ η` on the rows of `Z`,
`L(η) = (2m)⁻¹ ‖Z η - y‖²`; so minimizers of `NTK.mseLoss` are exactly the minimizers of the
residual norm `‖Z η - y‖` studied below. -/
theorem mseLoss_linear (Z : Matrix (Fin m) (Fin n) ℝ) (y : EuclideanSpace ℝ (Fin m))
    (η : EuclideanSpace ℝ (Fin n)) :
    mseLoss (fun (z : Fin n → ℝ) (η : EuclideanSpace ℝ (Fin n)) => z ⬝ᵥ η.ofLp) Z y η =
      (2 * (m : ℝ))⁻¹ * ‖WithLp.toLp 2 (Z *ᵥ η.ofLp) - y‖ ^ 2 := rfl

/-- **Bridge to `LinearRegression.leastSquaresLoss`.** For `m > 0` samples,
`‖y - Z η‖² = 2 m · NTK.mseLoss` of the linear model. Hence the minimizers of the two losses
coincide, which unifies the minimizer theorems of this file (stated for the residual norm) with
`LinearRegression.IsMinNormLeastSquares`. -/
theorem leastSquaresLoss_eq_two_mul_card_mul_mseLoss (hm : 0 < m) (Z : Matrix (Fin m) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin m)) (η : EuclideanSpace ℝ (Fin n)) :
    LinearRegression.leastSquaresLoss Z y η =
      2 * (m : ℝ) * mseLoss (fun (z : Fin n → ℝ) (η : EuclideanSpace ℝ (Fin n)) => z ⬝ᵥ η.ofLp)
        Z y η := by
  rw [mseLoss_linear, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul,
    LinearRegression.leastSquaresLoss, norm_sub_rev]
  rfl

section FeatureBottleneck

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

variable (Z : Matrix m n ℝ) (hZ : IsUnit (Zᵀ * Z).det)
  (y : EuclideanSpace ℝ m)

include hZ

/-- Normal equations: the residual of the left-inverse fit is orthogonal to the columns of `Z`,
`Zᵀ (Z η̂ - y) = 0` for `η̂ = (Zᵀ Z)⁻¹ Zᵀ y`, for a plain vector `y : m → ℝ`. -/
theorem transpose_mulVec_residual_leftInverse (y : m → ℝ) :
    Zᵀ *ᵥ (Z *ᵥ (((Zᵀ * Z)⁻¹ * Zᵀ) *ᵥ y) - y) = 0 := by
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
      ← Matrix.mulVec_transpose, transpose_mulVec_residual_leftInverse Z hZ y.ofLp, zero_dotProduct]
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
  simp [NTK.one_sub_gramProjector_mulVec]

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

section MinNormLeastSquares

variable {m n : Type*} [Fintype m] [Fintype n]

/-- `LinearRegression.leastSquaresLoss` is the square of the residual norm, so it has the same
minimizers as `η ↦ ‖Z η - y‖` (the form used throughout this file). -/
theorem isMinOn_leastSquaresLoss_iff (Z : Matrix m n ℝ) (y : EuclideanSpace ℝ m)
    (η : EuclideanSpace ℝ n) :
    IsMinOn (LinearRegression.leastSquaresLoss Z y) Set.univ η ↔
      IsMinOn (fun η' : EuclideanSpace ℝ n => ‖WithLp.toLp 2 (Z *ᵥ η'.ofLp) - y‖) Set.univ η := by
  have h : ∀ η' : EuclideanSpace ℝ n, LinearRegression.leastSquaresLoss Z y η' =
      ‖WithLp.toLp 2 (Z *ᵥ η'.ofLp) - y‖ ^ 2 := fun η' => by
    rw [LinearRegression.leastSquaresLoss, norm_sub_rev]
    rfl
  simp only [isMinOn_iff, Set.mem_univ, forall_const, h]
  exact forall_congr' fun η' => sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)

/-- **Minimum-norm least squares from the norm form.** If `η` has norm at most that of every
minimizer of the residual norm, it is a `LinearRegression.IsMinNormLeastSquares` estimator. -/
theorem isMinNormLeastSquares_of_norm_le (Z : Matrix m n ℝ) (y : EuclideanSpace ℝ m)
    (η : EuclideanSpace ℝ n)
    (hnorm : ∀ η' : EuclideanSpace ℝ n,
      IsMinOn (fun η'' : EuclideanSpace ℝ n => ‖WithLp.toLp 2 (Z *ᵥ η''.ofLp) - y‖)
        Set.univ η' → ‖η‖ ≤ ‖η'‖) :
    LinearRegression.IsMinNormLeastSquares Z y η :=
  isMinOn_iff.mpr fun η' hη' => hnorm η' ((isMinOn_leastSquaresLoss_iff Z y η').mp hη')

variable [DecidableEq n] in
/-- **The feature-bottleneck estimator is the ridgeless least-squares solution.** If `Zᵀ Z` is
invertible, `(Zᵀ Z)⁻¹ Zᵀ y` minimizes `LinearRegression.leastSquaresLoss` and is
`LinearRegression.IsMinNormLeastSquares`: it is the unique minimizer of the residual
(`eq_leftInverse_of_norm_residual_le`), hence trivially of minimum norm. -/
theorem leftInverse_isMinNormLeastSquares (Z : Matrix m n ℝ) (hZ : IsUnit (Zᵀ * Z).det)
    (y : EuclideanSpace ℝ m) :
    IsMinOn (LinearRegression.leastSquaresLoss Z y) Set.univ
        (WithLp.toLp 2 (((Zᵀ * Z)⁻¹ * Zᵀ) *ᵥ y.ofLp)) ∧
      LinearRegression.IsMinNormLeastSquares Z y
        (WithLp.toLp 2 (((Zᵀ * Z)⁻¹ * Zᵀ) *ᵥ y.ofLp)) := by
  refine ⟨(isMinOn_leastSquaresLoss_iff Z y _).mpr (leftInverse_isMinOn Z hZ y), ?_⟩
  refine isMinNormLeastSquares_of_norm_le Z y _ fun η' hη' => ?_
  have h := eq_leftInverse_of_norm_residual_le Z hZ y η'
    (isMinOn_iff.mp hη' (WithLp.toLp 2 (((Zᵀ * Z)⁻¹ * Zᵀ) *ᵥ y.ofLp)) (Set.mem_univ _))
  exact le_of_eq (congrArg norm h.symm)

variable [DecidableEq m] in
/-- **The sample-bottleneck estimator is the ridgeless least-squares solution.** If `Z Zᵀ` is
invertible, the minimum-norm interpolator `Zᵀ (Z Zᵀ)⁻¹ y` minimizes
`LinearRegression.leastSquaresLoss` (with value `0`) and is
`LinearRegression.IsMinNormLeastSquares`: every minimizer is an interpolator, whose norm is at
least that of `Zᵀ (Z Zᵀ)⁻¹ y` (`rightInverse_norm_sq_decomp`). -/
theorem rightInverse_isMinNormLeastSquares (Z : Matrix m n ℝ) (hZ : IsUnit (Z * Zᵀ).det)
    (y : EuclideanSpace ℝ m) :
    IsMinOn (LinearRegression.leastSquaresLoss Z y) Set.univ
        (WithLp.toLp 2 ((Zᵀ * (Z * Zᵀ)⁻¹) *ᵥ y.ofLp)) ∧
      LinearRegression.IsMinNormLeastSquares Z y
        (WithLp.toLp 2 ((Zᵀ * (Z * Zᵀ)⁻¹) *ᵥ y.ofLp)) := by
  set ηh : EuclideanSpace ℝ n := WithLp.toLp 2 ((Zᵀ * (Z * Zᵀ)⁻¹) *ᵥ y.ofLp) with hηh
  have h0 : ‖(WithLp.toLp 2 (Z *ᵥ ηh.ofLp) : EuclideanSpace ℝ m) - y‖ = 0 := by
    rw [hηh, WithLp.ofLp_toLp, rightInverse_interpolates Z hZ y.ofLp]
    simp
  refine ⟨(isMinOn_leastSquaresLoss_iff Z y _).mpr (isMinOn_iff.mpr fun η' _ => ?_), ?_⟩
  · change ‖(WithLp.toLp 2 (Z *ᵥ ηh.ofLp) : EuclideanSpace ℝ m) - y‖ ≤ _
    rw [h0]
    exact norm_nonneg _
  refine isMinNormLeastSquares_of_norm_le Z y _ fun η' hη' => ?_
  have hle := isMinOn_iff.mp hη' ηh (Set.mem_univ _)
  have hint : Z *ᵥ η'.ofLp = y.ofLp := by
    have h1 : ‖(WithLp.toLp 2 (Z *ᵥ η'.ofLp) : EuclideanSpace ℝ m) - y‖ = 0 :=
      le_antisymm (le_trans hle (le_of_eq h0)) (norm_nonneg _)
    have := sub_eq_zero.mp (norm_eq_zero.mp h1)
    simpa using congrArg WithLp.ofLp this
  have h2 := rightInverse_norm_sq_decomp Z hZ y.ofLp hint
  have h3 : ‖ηh‖ ^ 2 ≤ ‖η'‖ ^ 2 := by
    rw [h2]
    exact le_add_of_nonneg_right (sq_nonneg _)
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h3

end MinNormLeastSquares

end LinearRegression.DoubleDescent

end
