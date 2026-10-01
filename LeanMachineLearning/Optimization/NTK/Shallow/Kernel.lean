/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Basic
public import LeanMachineLearning.Optimization.NTK.Foundations.IIDAverage
public import LeanMachineLearning.Optimization.NTK.Foundations.MatrixUtil
public import LeanMachineLearning.Optimization.NTK.Shallow.DatasetNTK
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import LeanMachineLearning.Optimization.ConvexOpt.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# The neural tangent kernel (NTK)

This file formalizes the neural tangent kernel (NTK) corresponding to Section 4.3 of the
deep learning theory notes (Telgarsky 2021).

The NTK arises naturally from the gradient-feature view of the linearization `f₀`.
Because `f₀(x; W) = ⟨∇_W f(x; W₀), W⟩_F` is a linear predictor in the feature space
`{∇_W f(x; W₀) : x ∈ ℝᵈ}`, the corresponding kernel is the inner product between
feature maps:
  `kₘ(x, x') = ⟨∇_W f(x; W₀), ∇_W f(x'; W₀)⟩_F`.

As `m → ∞`, the rows `wⱼ₀` are i.i.d. Gaussian and the empirical average converges
almost surely to the **limiting NTK**:
  `k(x, x') = xᵀx' · 𝔼_w[σ'(wᵀx)σ'(wᵀx')]`.

For the ReLU, this expectation has the elegant closed form
  `k(x, x') = xᵀx' · (π − arccos(xᵀx')) / (2π)`
derived via a geometric argument on the sphere; it is proved in `NTK.ReluClosedForm`, which
needs the two-dimensional Gaussian computation from `NTK.Initialization`.

## Main definitions

* `NTK.empiricalNTKWithOuter` : the empirical NTK with arbitrary fixed outer coefficients.
* `NTK.empiricalNTK` : the simplified empirical NTK when `aⱼ² = 1`.
* `NTK.limitingNTK` : the limiting NTK `k(x, x')`.
* `NTK.gaussianRow_average_tendsto_integral` : reusable SLLN for empirical averages of
  measurable integrable functions of iid Gaussian rows.
* `NTK.variance_average_pi`, `NTK.chebyshev_average_pi`,
  `NTK.chebyshev_average_pi_le_second_moment` (in `NTK.IIDAverage`) : variance and Chebyshev
  bounds for empirical averages of an `ℒ²` observable under an i.i.d. product measure.
* `NTK.ntk_convergence` : almost sure convergence `kₘ(x,x') → k(x,x')` (SLLN).
* `NTK.reluNTK_closedForm` (in `NTK.ReluClosedForm`) : closed form
  `k(x,x') = xᵀx'·(π−arccos(xᵀx'))/(2π)` for ReLU.
* `NTK.trainingOutputs` (and the rest of this list, in `NTK.DatasetNTK`) : the vector
  `f(θ) = [f(x¹; θ), …, f(xᵐ; θ)]ᵀ` of predictions on the training dataset.
* `NTK.trainingResidual` : the residual error vector `r(θ) = f(θ) - y`.
* `NTK.mseLoss` : the empirical MSE loss objective `L(θ) = (1 / 2m) ‖r(θ)‖²`.
* `NTK.tangentFeature` : the sensitivity vector `x ↦ ∇_θ f(x; θ) ∈ ℝ^P`.
* `NTK.outputJacobian` : the network output Jacobian matrix `J(θ) ∈ ℝ^{m × P}`.
* `NTK.empiricalNTKMatrix` : the empirical NTK Gram matrix `K_t = J(θ) J(θ)ᵀ ∈ ℝ^{m × m}`.

The finite-width gradient-flow function-space dynamics (the residual ODE
`∂_t r(t) = - (1/m) K_t r(t)` and its supporting step-by-step derivation) have moved to
`LeanMachineLearning.Optimization.NTK.Training.GradientFlow`, alongside the infinite-width
specialization and closed-form dynamics that build on it.

-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory Filter ConvexOpt
open scoped RealInnerProductSpace Matrix

namespace NTK

variable {d m : ℕ}

/-! ### Dot product and norm helpers -/

/-- `x ⬝ᵥ x` is the sum of the coordinate squares. -/
lemma dotProduct_self_eq_sum_sq (x : Fin d → ℝ) : x ⬝ᵥ x = ∑ k : Fin d, x k ^ 2 := by
  simp [dotProduct, pow_two]

/-- For the Euclidean `L²` norm on `EuclideanSpace ℝ (Fin d)`, `‖x‖² = x ⬝ᵥ x`.

The default norm on `Fin d → ℝ` is the sup norm, so the analogous statement is false for the raw
Pi type. -/
lemma norm_sq_eq_dotProduct (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ^ 2 = x.ofLp ⬝ᵥ x.ofLp := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa using (dotProduct_self_eq_sum_sq x.ofLp).symm

lemma dotProduct_mul_right (c : ℝ) (x y : Fin d → ℝ) :
    x ⬝ᵥ (fun k => c * y k) = c * (x ⬝ᵥ y) :=
  dotProduct_smul c x y

lemma dotProduct_mul_mul (c₁ c₂ : ℝ) (x y : Fin d → ℝ) :
    (fun k => c₁ * x k) ⬝ᵥ (fun k => c₂ * y k) = (c₁ * c₂) * (x ⬝ᵥ y) := by
  rw [show (fun k => c₁ * x k) = c₁ • x from rfl, smul_dotProduct, dotProduct_mul_right,
    smul_eq_mul, mul_assoc]

/-- Cauchy–Schwarz for the dot product, in sum-of-squares form. -/
lemma sq_dotProduct_le (w x : Fin d → ℝ) :
    (w ⬝ᵥ x) ^ 2 ≤ (∑ j : Fin d, w j ^ 2) * ∑ j : Fin d, x j ^ 2 := by
  unfold dotProduct
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- The dot product of a weight vector with a scaled input `(1 / √d) * x` has the scaling
factor `1 / √d` factored out. -/
lemma dotProduct_scaled_input (d : ℕ) (w x : Fin d → ℝ) :
    w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * x k) = (Real.sqrt (d : ℝ))⁻¹ * (w ⬝ᵥ x) :=
  dotProduct_mul_right _ _ _

/-- Preactivation form: `w ⬝ᵥ (x / √d) = (w ⬝ᵥ x) / √d`. -/
lemma dotProduct_scaled_input_div (d : ℕ) (w x : Fin d → ℝ) :
    w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * x k) = (w ⬝ᵥ x) / Real.sqrt (d : ℝ) := by
  rw [dotProduct_scaled_input, div_eq_inv_mul]

/-- Inner product of two scaled inputs factors out `(1 / √d)² = 1 / d`. -/
lemma dotProduct_scaled_dataset (d : ℕ) (hd : 0 < d) (x y : Fin d → ℝ) :
    (fun k => (Real.sqrt (d : ℝ))⁻¹ * x k) ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * y k) =
      (d : ℝ)⁻¹ * (x ⬝ᵥ y) := by
  rw [dotProduct_mul_mul]
  have h_sqrt : (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ))⁻¹ = (d : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  rw [h_sqrt]

/-! ### Empirical NTK (Definition 4.5) -/

/-- The empirical NTK with arbitrary fixed outer coefficients:
  `kₘ,a(x,x') = (xᵀx') · (1/m)∑ⱼ aⱼ² σ'(wⱼ₀ᵀx)σ'(wⱼ₀ᵀx')`.

The lecture notes immediately simplify this expression using `aⱼ ∈ {±1}`. Keeping this
general form around makes the connection to `gradientMatrix` explicit. -/
noncomputable def empiricalNTKWithOuter
    (σ' : ℝ → ℝ)
    (outerCoeffs : Fin m → ℝ)
    (W₀ : Fin m → Fin d → ℝ)
    (x x' : Fin d → ℝ) : ℝ :=
  (x ⬝ᵥ x') *
    ((m : ℝ)⁻¹ * ∑ j : Fin m,
      outerCoeffs j ^ 2 *
      σ' (∑ k : Fin d, W₀ j k * x k) *
      σ' (∑ k : Fin d, W₀ j k * x' k))

/-- **Definition 4.5** (Empirical neural tangent kernel, `aⱼ² = 1` case).
Given initialization `W₀ : Fin m → Fin d → ℝ` and outer coefficients satisfying
`aⱼ² = 1`, the empirical NTK is the kernel obtained as the Frobenius inner product
of gradients:
  `kₘ(x, x') = ⟨∇_W f(x; W₀), ∇_W f(x'; W₀)⟩_F
              = (xᵀx') · (1/m) ∑ⱼ σ'(wⱼ₀ᵀx) σ'(wⱼ₀ᵀx')`.

The second equality uses `aⱼ² = 1` and `⟨xσ'(·), x'σ'(·)⟩ = (xᵀx')σ'(·)σ'(·)`. -/
noncomputable def empiricalNTK
    (σ' : ℝ → ℝ)
    (W₀ : Fin m → Fin d → ℝ)
    (x x' : Fin d → ℝ) : ℝ :=
  (x ⬝ᵥ x') *
    ((m : ℝ)⁻¹ * ∑ j : Fin m,
      σ' (∑ k : Fin d, W₀ j k * x k) *
      σ' (∑ k : Fin d, W₀ j k * x' k))

-- Term-level algebraic identity for the Frobenius inner product of gradients.
private lemma gradient_matrix_term_eq (m : ℕ) (outerCoeffs_j : ℝ) (val_x val_x' : ℝ)
    (x_k x'_k : ℝ) :
    ((m : ℝ)⁻¹.sqrt * outerCoeffs_j * val_x * x_k) *
    ((m : ℝ)⁻¹.sqrt * outerCoeffs_j * val_x' * x'_k) =
    (x_k * x'_k) * ((m : ℝ)⁻¹ * outerCoeffs_j ^ 2 * val_x * val_x') := by
  calc
    _ = ((m : ℝ)⁻¹.sqrt * (m : ℝ)⁻¹.sqrt) *
          (outerCoeffs_j * outerCoeffs_j) * val_x * val_x' * (x_k * x'_k) := by
      ring
    _ = (m : ℝ)⁻¹ * outerCoeffs_j ^ 2 * val_x * val_x' * (x_k * x'_k) := by
      rw [Real.mul_self_sqrt (inv_nonneg.2 (Nat.cast_nonneg m)), ← sq]
    _ = _ := by ring

/-- The entrywise product sum of gradient features is the empirical NTK with the
outer-coefficient squares included. -/
lemma sum_gradientMatrix_mul_eq_empiricalNTKWithOuter
    (σ' : ℝ → ℝ) (outerCoeffs : Fin m → ℝ)
    (W₀ : Fin m → Fin d → ℝ) (x x' : Fin d → ℝ) :
    (∑ i : Fin m, ∑ j : Fin d,
      gradientMatrix (σ' := σ') outerCoeffs x W₀ i j *
        gradientMatrix (σ' := σ') outerCoeffs x' W₀ i j) =
    empiricalNTKWithOuter σ' outerCoeffs W₀ x x' := by
  unfold gradientMatrix empiricalNTKWithOuter dotProduct
  simp_rw [gradient_matrix_term_eq]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  congr 1
  rw [Finset.mul_sum]
  congr 1; ext i
  ring

/-- If all fixed outer coefficients satisfy `aⱼ² = 1`, the general empirical NTK
reduces to the simplified expression used in the notes. -/
lemma empiricalNTKWithOuter_eq_empiricalNTK_of_sq_one
    (σ' : ℝ → ℝ) (outerCoeffs : Fin m → ℝ)
    (W₀ : Fin m → Fin d → ℝ) (x x' : Fin d → ℝ)
    (houter : ∀ j : Fin m, outerCoeffs j ^ 2 = 1) :
    empiricalNTKWithOuter σ' outerCoeffs W₀ x x' =
    empiricalNTK σ' W₀ x x' := by
  simp [empiricalNTKWithOuter, empiricalNTK, houter]

/-- The empirical NTK is symmetric: `kₘ(x, x') = kₘ(x', x)`. -/
lemma empiricalNTK_symm
    (σ' : ℝ → ℝ) (W₀ : Fin m → Fin d → ℝ) (x x' : Fin d → ℝ) :
    empiricalNTK σ' W₀ x x' = empiricalNTK σ' W₀ x' x := by
  simp only [empiricalNTK, dotProduct_comm x x', mul_comm (σ' _) (σ' _)]

/-- The dataset empirical NTK matrix with arbitrary outer coefficients is positive semidefinite. -/
theorem empiricalNTKWithOuter_dataset_posSemidef
    (σ' : ℝ → ℝ) (outerCoeffs : Fin m → ℝ)
    (W₀ : Fin m → Fin d → ℝ) {N : ℕ} (X : Fin N → Fin d → ℝ) :
    (Matrix.of (fun α β => empiricalNTKWithOuter σ' outerCoeffs W₀ (X α) (X β))).PosSemidef := by
  have h_eq : (Matrix.of fun α β => empiricalNTKWithOuter σ' outerCoeffs W₀ (X α) (X β)) =
      (Matrix.of fun α (j, k) => gradientMatrix (σ' := σ') outerCoeffs (X α) W₀ j k) *
      (Matrix.of fun α (j, k) => gradientMatrix (σ' := σ') outerCoeffs (X α) W₀ j k)ᵀ := by
    ext α β
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    rw [Fintype.sum_prod_type]
    exact (sum_gradientMatrix_mul_eq_empiricalNTKWithOuter
      σ' outerCoeffs W₀ (X α) (X β)).symm
  rw [h_eq]
  have h1 : (1 : Matrix (Fin m × Fin d) (Fin m × Fin d) ℝ).PosSemidef := Matrix.PosSemidef.one
  have h := h1.mul_mul_conjTranspose_same
    (Matrix.of fun α (j, k) => gradientMatrix (σ' := σ') outerCoeffs (X α) W₀ j k)
  simp only [Matrix.mul_one] at h
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The dataset empirical NTK matrix (`aⱼ² = 1` case) is positive semidefinite. -/
theorem empiricalNTK_dataset_posSemidef
    (σ' : ℝ → ℝ) (outerCoeffs : Fin m → ℝ)
    (W₀ : Fin m → Fin d → ℝ) {N : ℕ} (X : Fin N → Fin d → ℝ)
    (houter : ∀ j : Fin m, outerCoeffs j ^ 2 = 1) :
    (Matrix.of (fun α β => empiricalNTK σ' W₀ (X α) (X β))).PosSemidef := by
  have h_eq : (Matrix.of fun α β => empiricalNTK σ' W₀ (X α) (X β)) =
      Matrix.of fun α β => empiricalNTKWithOuter σ' outerCoeffs W₀ (X α) (X β) := by
    ext α β
    simp only [Matrix.of_apply]
    exact (empiricalNTKWithOuter_eq_empiricalNTK_of_sq_one
      σ' outerCoeffs W₀ (X α) (X β) houter).symm
  rw [h_eq]
  exact empiricalNTKWithOuter_dataset_posSemidef σ' outerCoeffs W₀ X

/-- The empirical NTK is positive semidefinite: for any finite set of points
and coefficients `(αᵢ, xᵢ)`, `∑ᵢⱼ αᵢαⱼ kₘ(xᵢ, xⱼ) ≥ 0`.
This follows from being the Gram matrix of the gradient features. -/
lemma empiricalNTK_posSemidef
    (σ' : ℝ → ℝ) (W₀ : Fin m → Fin d → ℝ)
    {n : ℕ} (α : Fin n → ℝ) (pts : Fin n → Fin d → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      α i * α j * empiricalNTK σ' W₀ (pts i) (pts j) :=
  posSemidef_sum_nonneg
    (M := Matrix.of fun a b => empiricalNTK σ' W₀ (pts a) (pts b))
    (empiricalNTK_dataset_posSemidef σ' (fun _ => 1) W₀ pts (fun _ => one_pow 2)) α

/-! ### Limiting NTK (Definition 4.6) -/

/-- **Definition 4.6** (Limiting neural tangent kernel).
The limiting NTK is the expectation of the gradient-feature inner product
as `m → ∞`:
  `k(x, x') = (xᵀx') · 𝔼_{w ~ 𝒩(0,Iᵈ)}[σ'(wᵀx) σ'(wᵀx')]`.

This is positive semidefinite and symmetric. For the ReLU, it has the closed form
given in `reluNTK_closedForm`. -/
noncomputable def limitingNTK (σ' : ℝ → ℝ) (x x' : Fin d → ℝ) : ℝ :=
  (x ⬝ᵥ x') *
    ∫ w : Fin d → ℝ,
      σ' (w ⬝ᵥ x) * σ' (w ⬝ᵥ x') ∂(gaussianRowMeasure d)

/-- The limiting NTK is symmetric. -/
lemma limitingNTK_symm (σ' : ℝ → ℝ) (x x' : Fin d → ℝ) :
    limitingNTK σ' x x' = limitingNTK σ' x' x := by
  simp only [limitingNTK, dotProduct_comm x x', mul_comm (σ' _) (σ' _)]

/-! ### Measurability and integrability of the NTK summand -/

/-- The standard Gaussian row measure `𝒩(0, Iᵈ)` is a probability measure. -/
instance : IsProbabilityMeasure (gaussianRowMeasure d) := by
  unfold gaussianRowMeasure
  infer_instance

/-- The dot product `w ↦ wᵀx` with a fixed vector is measurable. -/
lemma measurable_dotProduct_left (x : Fin d → ℝ) :
    Measurable fun w : Fin d → ℝ => w ⬝ᵥ x :=
  Finset.measurable_sum _ fun k _ => (measurable_pi_apply k).mul measurable_const

/-- The product `w ↦ σ'(wᵀx) · σ'(wᵀx')` is measurable whenever `σ'` is. -/
lemma measurable_ntkSummand {σ' : ℝ → ℝ} (hσ' : Measurable σ') (x x' : Fin d → ℝ) :
    Measurable (fun w : Fin d → ℝ => σ' (w ⬝ᵥ x) * σ' (w ⬝ᵥ x')) :=
  (hσ'.comp (measurable_dotProduct_left x)).mul (hσ'.comp (measurable_dotProduct_left x'))

/-- If `σ'` is bounded by `C`, then
`|σ'(wᵀx) · σ'(wᵀx')| ≤ C²`. -/
lemma abs_ntkSummand_le {σ' : ℝ → ℝ} {C : ℝ} (hC : ∀ z, |σ' z| ≤ C)
    (x x' : Fin d → ℝ) (w : Fin d → ℝ) :
    |σ' (w ⬝ᵥ x) * σ' (w ⬝ᵥ x')| ≤ C * C := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (σ' 0)) (hC 0)
  rw [abs_mul]
  exact mul_le_mul (hC _) (hC _) (abs_nonneg _) hC0

/-- The product `w ↦ σ'(wᵀx) · σ'(wᵀx')` is integrable against the Gaussian
row measure when `σ'` is measurable and bounded. -/
lemma integrable_ntkSummand {σ' : ℝ → ℝ} (hσ'm : Measurable σ') {C : ℝ}
    (hC : ∀ z, |σ' z| ≤ C) (x x' : Fin d → ℝ) :
    Integrable (fun w : Fin d → ℝ => σ' (w ⬝ᵥ x) * σ' (w ⬝ᵥ x')) (gaussianRowMeasure d) :=
  Integrable.of_bound (measurable_ntkSummand hσ'm x x').aestronglyMeasurable (C * C)
    (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs]
      exact abs_ntkSummand_le hC x x' w)

/-! ### Almost sure convergence of the empirical NTK (Lemma 4.3) -/

/-- The width-`m` empirical NTK built from the first `m` rows of an infinite iid
initialization. This is the right object for the notes' `m → ∞` limit. -/
noncomputable def empiricalNTKFromRows
    (σ' : ℝ → ℝ)
    (rows : ℕ → Fin d → ℝ)
    (width : ℕ)
    (x x' : Fin d → ℝ) : ℝ :=
  (x ⬝ᵥ x') *
    ((width : ℝ)⁻¹ * ∑ j : Fin width,
      σ' (rows j.val ⬝ᵥ x) * σ' (rows j.val ⬝ᵥ x'))

/-- The strong law for empirical averages of a measurable integrable function of
i.i.d. Gaussian rows. Specializes `iid_average_tendsto_integral` to Gaussian row measures. -/
lemma gaussianRow_average_tendsto_integral
    (g : (Fin d → ℝ) → ℝ)
    (hg_meas : Measurable g)
    (hg_int : Integrable g (gaussianRowMeasure d)) :
    ∀ᵐ rows : ℕ → Fin d → ℝ
      ∂(Measure.infinitePi fun _ : ℕ => gaussianRowMeasure d),
      Filter.Tendsto
        (fun width : ℕ => (width : ℝ)⁻¹ * ∑ j : Fin width, g (rows j))
        Filter.atTop
        (nhds (∫ w, g w ∂(gaussianRowMeasure d))) :=
  iid_average_tendsto_integral (gaussianRowMeasure d) g hg_meas hg_int

/-- **Lemma 4.3** (Almost sure convergence of the empirical NTK).
For fixed `x, x' ∈ ℝᵈ`, a measurable bounded `σ'`, and an infinite sequence of iid
rows `w₀, w₁, ... ~ 𝒩(0,Iᵈ)`:
  `kₘ(x, x') →_as k(x, x')  as  m → ∞`.

**Proof:** The summands `Yⱼ = σ'(wⱼ₀ᵀx)σ'(wⱼ₀ᵀx')` are measurable functions of the
independent rows `wⱼ₀`, hence pairwise independent; they are identically distributed
(each row has law `𝒩(0,Iᵈ)`) and integrable (bounded by `C²` on a probability space).
The strong law of large numbers (Etemadi's version, `ProbabilityTheory.strong_law_ae`,
which only needs pairwise independence) gives `(1/m)∑ⱼ Yⱼ →_as 𝔼[Y₀]`, and multiplying
by the constant `xᵀx'` yields the claim, since
`𝔼[Y₀] = 𝔼_{w ~ 𝒩(0,Iᵈ)}[σ'(wᵀx)σ'(wᵀx')]`.

The measurability hypothesis `hσ'_meas` is implicit in the informal notes (their `σ'`
is the ReLU derivative `1[· ≥ 0]`, which is measurable: `measurable_reluIndicator`);
it is needed for the integrability required by the strong law. -/
theorem ntk_convergence
    (σ' : ℝ → ℝ)
    (hσ'_meas : Measurable σ')
    (hσ'_bounded : ∃ C : ℝ, ∀ z : ℝ, |σ' z| ≤ C)
    (x x' : Fin d → ℝ) :
    ∀ᵐ rows : ℕ → Fin d → ℝ
      ∂(MeasureTheory.Measure.infinitePi (fun _ : ℕ => gaussianRowMeasure d)),
      Filter.Tendsto
        (fun width => empiricalNTKFromRows σ' rows width x x')
        Filter.atTop
        (nhds (limitingNTK σ' x x')) := by
  obtain ⟨C, hC⟩ := hσ'_bounded
  have hg_meas : Measurable (fun w : Fin d → ℝ => σ' (w ⬝ᵥ x) * σ' (w ⬝ᵥ x')) :=
    measurable_ntkSummand hσ'_meas x x'
  have hg_int : Integrable (fun w : Fin d → ℝ => σ' (w ⬝ᵥ x) * σ' (w ⬝ᵥ x'))
      (gaussianRowMeasure d) :=
    integrable_ntkSummand hσ'_meas hC x x'
  filter_upwards [gaussianRow_average_tendsto_integral
    (fun w : Fin d → ℝ => σ' (w ⬝ᵥ x) * σ' (w ⬝ᵥ x')) hg_meas hg_int]
    with rows hrows
  exact hrows.const_mul (x ⬝ᵥ x')

/-! ### ReLU NTK closed form (Proposition 4.2) -/

/-- The ReLU derivative: `1[z ≥ 0]` (a.e. equal to the actual derivative). -/
noncomputable def reluIndicator : ℝ → ℝ := fun z => if 0 ≤ z then 1 else 0

/-- The ReLU derivative is measurable: it is the indicator of the closed
measurable set `[0, ∞)`. Together with `abs_reluIndicator_le` this shows that
`reluIndicator` satisfies the hypotheses of `ntk_convergence`. -/
lemma measurable_reluIndicator : Measurable reluIndicator := by
  have h : reluIndicator = Set.indicator (Set.Ici 0) fun _ => (1 : ℝ) := by
    ext z
    simp [reluIndicator, Set.indicator]
  rw [h]
  exact Measurable.indicator measurable_const measurableSet_Ici

/-- The ReLU derivative is bounded by `1`. -/
lemma abs_reluIndicator_le (z : ℝ) : |reluIndicator z| ≤ 1 := by
  simp only [reluIndicator]
  split_ifs <;> simp

/-! ### Auxiliary lemmas for the ReLU NTK closed form -/

/-- The row inner product agrees with the Euclidean inner product of the `L²` lifts. -/
lemma dotProduct_eq_inner_toLp (x y : Fin d → ℝ) :
    x ⬝ᵥ y = ⟪WithLp.toLp 2 y, WithLp.toLp 2 x⟫ := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct]

/-- Pushforward of `gaussianRowMeasure` by the linear functional `w ↦ wᵀx` is a 1D Gaussian
with mean `0` and variance `xᵀx`. -/
lemma map_gaussianRowMeasure_dotProduct (x : Fin d → ℝ) :
    Measure.map (fun w => w ⬝ᵥ x) (gaussianRowMeasure d) =
      gaussianReal 0 (Real.toNNReal (x ⬝ᵥ x)) := by
  have h_eq : (fun w : Fin d → ℝ => w ⬝ᵥ x) =
      (fun (v : EuclideanSpace ℝ (Fin d)) => innerSL ℝ (WithLp.toLp 2 x) v) ∘ (WithLp.toLp 2) := by
    ext w
    dsimp
    rw [← dotProduct_eq_inner_toLp w x]
  rw [h_eq, ← Measure.map_map]
  · have h_toLp : Measure.map (WithLp.toLp 2) (gaussianRowMeasure d) =
        stdGaussian (EuclideanSpace ℝ (Fin d)) := map_pi_eq_stdGaussian
    rw [h_toLp]
    have h_map := IsGaussian.map_eq_gaussianReal
      (μ := stdGaussian (EuclideanSpace ℝ (Fin d))) (innerSL ℝ (WithLp.toLp 2 x))
    rw [h_map]
    have h_mean : ∫ (v : EuclideanSpace ℝ (Fin d)),
        (innerSL ℝ (WithLp.toLp 2 x)) v ∂stdGaussian (EuclideanSpace ℝ (Fin d)) = 0 := by
      rw [(innerSL ℝ (WithLp.toLp 2 x)).integral_comp_id_comm IsGaussian.integrable_id]
      rw [integral_id_stdGaussian]
      exact map_zero (innerSL ℝ (WithLp.toLp 2 x))
    have h_var : Var[innerSL ℝ (WithLp.toLp 2 x); stdGaussian (EuclideanSpace ℝ (Fin d))] =
        x ⬝ᵥ x := by
      rw [variance_dual_stdGaussian]
      rw [innerSL_apply_norm]
      rw [norm_sq_eq_dotProduct (WithLp.toLp 2 x)]
    rw [h_mean, h_var]
  all_goals fun_prop

end NTK

end
