/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Basic
public import LeanMachineLearning.Optimization.NTK.MatrixUtil
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
# The empirical NTK matrix on a finite dataset, and the MSE gradient

The training-output and residual vectors, the empirical MSE loss, the tangent features and output
Jacobian, the empirical NTK Gram matrix `K = J Jᵀ` and its positive semidefiniteness, the gradient
of the MSE loss, and the discrete gradient-descent step.
-/
@[expose] public section

open Real MeasureTheory ProbabilityTheory Filter ConvexOpt
open scoped RealInnerProductSpace Matrix

namespace NTK

variable {d m : ℕ}

/-! ### Finite-Dataset Empirical NTK, Optimization, and Function-Space Dynamics

This section formalizes the empirical Neural Tangent Kernel (NTK) on finite datasets,
the discrete gradient descent and continuous gradient flow optimization regimes,
the Gram factorization and positive semidefiniteness of the empirical NTK matrix,
and the exact induced function-space training dynamics.
-/

variable {ι : Type*} {P : ℕ}

/-- The vector of network outputs on the training dataset:
  `f(θ) = [f(x¹; θ), …, f(xᵐ; θ)]ᵀ ∈ ℝᵐ`. -/
noncomputable def trainingOutputs (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ : EuclideanSpace ℝ (Fin P)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun α => f (X α) θ)

/-- The residual error vector function:
  `r(θ) = f(θ) - y ∈ ℝᵐ`. -/
noncomputable def trainingResidual (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m)) (θ : EuclideanSpace ℝ (Fin P)) : EuclideanSpace ℝ (Fin m) :=
  trainingOutputs f X θ - y

/-- The empirical Mean-Squared Error (MSE) loss objective:
  `L(θ) = (1 / 2m) ∑_α (f(x^α; θ) - y^α)² = (1 / 2m) ‖f(θ) - y‖² = (1 / 2m) ‖r(θ)‖²`. -/
noncomputable def mseLoss (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m)) (θ : EuclideanSpace ℝ (Fin P)) : ℝ :=
  (2 * (m : ℝ))⁻¹ * ‖trainingResidual f X y θ‖ ^ 2

lemma mseLoss_eq_sum (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m)) (θ : EuclideanSpace ℝ (Fin P)) :
    mseLoss f X y θ = (2 * (m : ℝ))⁻¹ * ∑ α : Fin m, (f (X α) θ - y α) ^ 2 := by
  simp [mseLoss, EuclideanSpace.real_norm_sq_eq, trainingResidual, trainingOutputs]

/-- The tangent feature map `x ↦ ∇_θ f(x; θ) ∈ ℝ^P`, representing the sensitivity
of the scalar output with respect to parameters. -/
noncomputable def tangentFeature (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (x : ι)
    (θ : EuclideanSpace ℝ (Fin P)) : EuclideanSpace ℝ (Fin P) :=
  gradient (fun θ' => f x θ') θ

/-- The network output Jacobian matrix evaluated on the training dataset `J(θ) ∈ ℝ^{m × P}`,
whose `α`-th row is the transposed tangent feature vector `∇_θ f(x^α; θ)ᵀ`. -/
noncomputable def outputJacobian (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ : EuclideanSpace ℝ (Fin P)) : Matrix (Fin m) (Fin P) ℝ :=
  Matrix.of fun α j => tangentFeature f (X α) θ j

/-- The empirical Neural Tangent Kernel (NTK) Gram matrix `K_t = J(θ) J(θ)ᵀ ∈ ℝ^{m × m}`. -/
noncomputable def empiricalNTKMatrix (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ : EuclideanSpace ℝ (Fin P)) : Matrix (Fin m) (Fin m) ℝ :=
  outputJacobian f X θ * (outputJacobian f X θ)ᵀ

/-- The entries of the empirical NTK matrix are the inner products of tangent features:
  `K_t^{α β} = ⟨∇_θ f(x^α; θ(t)), ∇_θ f(x^β; θ(t))⟩`. -/
lemma empiricalNTKMatrix_apply (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ : EuclideanSpace ℝ (Fin P)) (α β : Fin m) :
    empiricalNTKMatrix f X θ α β = ⟪tangentFeature f (X α) θ, tangentFeature f (X β) θ⟫ := by
  simp [empiricalNTKMatrix, Matrix.mul_apply, outputJacobian, PiLp.inner_apply, mul_comm]

/-- The last row of the empirical NTK of the extended dataset `(X, x)` at `θ`: the train-test
cross-kernel `⟪∇f(x; θ), ∇f(X α; θ)⟫` and the test norm `‖∇f(x; θ)‖²`. -/
lemma empiricalNTKMatrix_snoc_last {ι : Type*} {m P : ℕ}
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (x : ι)
    (θ : EuclideanSpace ℝ (Fin P)) (α : Fin m) :
    empiricalNTKMatrix f (Fin.snoc (α := fun _ => ι) X x : Fin (m + 1) → ι) θ (Fin.last m)
        (Fin.castSucc α) = ⟪tangentFeature f x θ, tangentFeature f (X α) θ⟫ ∧
      empiricalNTKMatrix f (Fin.snoc (α := fun _ => ι) X x : Fin (m + 1) → ι) θ (Fin.last m)
        (Fin.last m) = ⟪tangentFeature f x θ, tangentFeature f x θ⟫ := by
  simp [empiricalNTKMatrix_apply]

/-- The cross-kernel vector is `J(θ) ∇f(x; θ)`. -/
lemma outputJacobian_mulVec_tangentFeature {ι : Type*} {m P : ℕ}
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (x : ι)
    (θ : EuclideanSpace ℝ (Fin P)) (α : Fin m) :
    (outputJacobian f X θ *ᵥ (tangentFeature f x θ).ofLp) α =
      ⟪tangentFeature f x θ, tangentFeature f (X α) θ⟫ := by
  simp [outputJacobian, Matrix.mulVec, dotProduct, PiLp.inner_apply, mul_comm]

/-! ### Positive Semidefiniteness and Gram Factorization -/

/-- The empirical NTK Gram matrix is positive semidefinite (`PosSemidef`) for any parameter
state. -/
theorem empiricalNTKMatrix_posSemidef (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ : EuclideanSpace ℝ (Fin P)) :
    (empiricalNTKMatrix f X θ).PosSemidef := by
  have h1 : (1 : Matrix (Fin P) (Fin P) ℝ).PosSemidef := Matrix.PosSemidef.one
  have h := h1.mul_mul_conjTranspose_same (outputJacobian f X θ)
  simp only [Matrix.mul_one] at h
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- Quadratic form evaluation: `vᵀ K v = ‖Jᵀ v‖²`. -/
theorem empiricalNTKMatrix_quad_form (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ : EuclideanSpace ℝ (Fin P)) (v : Fin m → ℝ) :
    v ⬝ᵥ ((empiricalNTKMatrix f X θ) *ᵥ v) =
      ‖(WithLp.toLp 2 ((outputJacobian f X θ)ᵀ *ᵥ v) : EuclideanSpace ℝ (Fin P))‖ ^ 2 := by
  have h_eq : v ⬝ᵥ ((empiricalNTKMatrix f X θ) *ᵥ v) =
      ((outputJacobian f X θ)ᵀ *ᵥ v) ⬝ᵥ ((outputJacobian f X θ)ᵀ *ᵥ v) := by
    dsimp [empiricalNTKMatrix]
    rw [← Matrix.mulVec_mulVec v (outputJacobian f X θ) (outputJacobian f X θ)ᵀ]
    rw [Matrix.dotProduct_mulVec]
    rw [← Matrix.mulVec_transpose]
  rw [h_eq, EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, pow_two]

/-- The quadratic form of the empirical NTK matrix is non-negative: `vᵀ K v ≥ 0`. -/
theorem empiricalNTKMatrix_quad_form_nonneg (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ : EuclideanSpace ℝ (Fin P)) (v : Fin m → ℝ) :
    0 ≤ v ⬝ᵥ ((empiricalNTKMatrix f X θ) *ᵥ v) := by
  rw [empiricalNTKMatrix_quad_form]
  exact sq_nonneg _

/-! ### Gradient of the MSE Loss -/

/-- Chain rule for a differentiable scalar function of a differentiable scalar-valued map: the
map `θ ↦ ℓ' (g θ)` has gradient `r • ∇g` when `ℓ'` has derivative `r` at `g θ`. This is the basic
step for any pointwise loss; `hasFDerivAt_sq_diff` is the squared-loss case. -/
lemma hasFDerivAt_generalizedLoss_term (θ : EuclideanSpace ℝ (Fin P))
    {g : EuclideanSpace ℝ (Fin P) → ℝ} (hg : DifferentiableAt ℝ g θ)
    {ℓ' : ℝ → ℝ} {r : ℝ} (hℓ : HasDerivAt ℓ' r (g θ)) :
    HasFDerivAt (fun θ' => ℓ' (g θ'))
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin P)) (r • gradient g θ)) θ := by
  have h := hℓ.comp_hasFDerivAt θ hg.hasFDerivAt
  have h_eq : InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin P)) (r • gradient g θ) =
      r • fderiv ℝ g θ := by
    apply ContinuousLinearMap.ext
    intro v
    rw [InnerProductSpace.toDual_apply_apply, smul_apply, smul_eq_mul,
      ← toDual_gradient, InnerProductSpace.toDual_apply_apply, inner_smul_left,
      starRingEnd_apply, star_trivial]
  rw [h_eq]
  exact h

/-- The squared-loss case of `hasFDerivAt_generalizedLoss_term`. -/
lemma hasFDerivAt_sq_diff (θ : EuclideanSpace ℝ (Fin P)) {g : EuclideanSpace ℝ (Fin P) → ℝ}
    (hg : DifferentiableAt ℝ g θ) (c : ℝ) :
    HasFDerivAt (fun θ' => (g θ' - c) ^ 2)
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin P))
        ((2 * (g θ - c)) • gradient g θ)) θ := by
  have hℓ : HasDerivAt (fun u : ℝ => (u - c) ^ 2) (2 * (g θ - c)) (g θ) := by
    have h := (hasDerivAt_pow 2 (g θ - c)).comp (g θ) ((hasDerivAt_id (g θ)).sub_const c)
    simpa [Function.comp_def] using h
  exact hasFDerivAt_generalizedLoss_term θ hg hℓ

/-- The empirical MSE loss has gradient
  `(1 / m) ∑_α (f(x^α; θ) - y^α) ∇_θ f(x^α; θ)`
at `θ`, in the `HasGradientAt` form needed for chain rules along curves. -/
theorem hasGradientAt_mseLoss (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m)) (θ : EuclideanSpace ℝ (Fin P))
    (hdiff : ∀ α : Fin m, DifferentiableAt ℝ (fun θ' => f (X α) θ') θ) :
    HasGradientAt (mseLoss f X y)
      ((m : ℝ)⁻¹ • ∑ α : Fin m, (trainingResidual f X y θ α) • tangentFeature f (X α) θ) θ := by
  have h_term : ∀ α ∈ (Finset.univ : Finset (Fin m)),
      HasFDerivAt (fun θ' => (f (X α) θ' - y α) ^ 2)
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin P))
          ((2 * (trainingResidual f X y θ α)) • tangentFeature f (X α) θ)) θ := by
    intro α _
    exact hasFDerivAt_sq_diff θ (hdiff α) (y α)
  have h_sum := HasFDerivAt.sum (u := Finset.univ) (A := fun α θ' => (f (X α) θ' - y α) ^ 2) h_term
  have h_sum_eq : (∑ α ∈ (Finset.univ : Finset (Fin m)), fun θ' => (f (X α) θ' - y α) ^ 2) =
      (fun θ' => ∑ α : Fin m, (f (X α) θ' - y α) ^ 2) := by
    ext θ'
    simp only [Finset.sum_apply]
  rw [h_sum_eq] at h_sum
  have h_scaled := h_sum.const_smul (2 * (m : ℝ))⁻¹
  have h_loss_eq : mseLoss f X y =
      fun θ' => (2 * (m : ℝ))⁻¹ * ∑ α : Fin m, (f (X α) θ' - y α) ^ 2 :=
    funext (mseLoss_eq_sum f X y)
  rw [h_loss_eq]
  have h_grad : HasGradientAt (fun θ' => (2 * (m : ℝ))⁻¹ * ∑ α : Fin m, (f (X α) θ' - y α) ^ 2)
      ((m : ℝ)⁻¹ • ∑ α : Fin m, (trainingResidual f X y θ α) • tangentFeature f (X α) θ) θ := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h_scaled using 1
    ext v
    simp only [smul_apply, sum_apply,
      InnerProductSpace.toDual_apply_apply, smul_eq_mul]
    rw [inner_smul_left]
    simp only [starRingEnd_apply, star_trivial]
    rw [sum_inner]
    simp only [inner_smul_left, starRingEnd_apply, star_trivial]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    ring
  exact h_grad

/-- The gradient of the empirical MSE loss with respect to parameters:
  `∇_θ L(θ) = (1 / m) ∑_α (f(x^α; θ) - y^α) ∇_θ f(x^α; θ)`. -/
theorem gradient_mseLoss (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m)) (θ : EuclideanSpace ℝ (Fin P))
    (hdiff : ∀ α : Fin m, DifferentiableAt ℝ (fun θ' => f (X α) θ') θ) :
    gradient (mseLoss f X y) θ =
      (m : ℝ)⁻¹ • ∑ α : Fin m, (trainingResidual f X y θ α) • tangentFeature f (X α) θ :=
  (hasGradientAt_mseLoss f X y θ hdiff).gradient

/-- Coordinate-wise formulation matching the Jacobian-residual product:
  `[∇_θ L(θ)]_j = (1 / m) [J(θ)ᵀ r(θ)]_j = (1 / m) ∑_α (f(x^α; θ) - y^α) [∇_θ f(x^α; θ)]_j`. -/
lemma gradient_mseLoss_apply_j (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m)) (θ : EuclideanSpace ℝ (Fin P))
    (hdiff : ∀ α : Fin m, DifferentiableAt ℝ (fun θ' => f (X α) θ') θ) (j : Fin P) :
    gradient (mseLoss f X y) θ j =
      (m : ℝ)⁻¹ * ((outputJacobian f X θ)ᵀ *ᵥ (trainingResidual f X y θ).ofLp) j := by
  rw [gradient_mseLoss f X y θ hdiff]
  have h_eval :
      ((m : ℝ)⁻¹ • ∑ α : Fin m, (trainingResidual f X y θ α) • tangentFeature f (X α) θ) j =
      (m : ℝ)⁻¹ * ∑ α : Fin m, (trainingResidual f X y θ α) * tangentFeature f (X α) θ j := by
    change (m : ℝ)⁻¹ *
      (∑ α : Fin m, (trainingResidual f X y θ α) • tangentFeature f (X α) θ).ofLp j = _
    rw [show (∑ α : Fin m, (trainingResidual f X y θ α) • tangentFeature f (X α) θ).ofLp =
        ∑ α : Fin m, ((trainingResidual f X y θ α) • tangentFeature f (X α) θ).ofLp from
        map_sum (WithLp.linearEquiv 2 ℝ (Fin P → ℝ)) _ Finset.univ]
    rw [Finset.sum_apply]
    rfl
  rw [h_eval]
  congr 1
  rw [Matrix.mulVec_apply]
  rw [dotProduct]
  simp only [Matrix.row_apply, Matrix.transpose_apply, outputJacobian, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro α _
  ring

/-- Vectorized formulation of the MSE gradient:
  `∇_θ L(θ) = (1 / m) J(θ)ᵀ r(θ)`. -/
lemma gradient_mseLoss_eq_mulVec (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m)) (θ : EuclideanSpace ℝ (Fin P))
    (hdiff : ∀ α : Fin m, DifferentiableAt ℝ (fun θ' => f (X α) θ') θ) :
    (gradient (mseLoss f X y) θ).ofLp =
      (m : ℝ)⁻¹ • ((outputJacobian f X θ)ᵀ *ᵥ (trainingResidual f X y θ).ofLp) := by
  ext j
  exact gradient_mseLoss_apply_j f X y θ hdiff j

/-! ### Discrete Gradient Descent Dynamics -/

/-- Discrete gradient descent step equation starting at `θ₀` with constant learning rate `η`
for the empirical MSE loss:
  `θ_{k+1} = θ_k - η ∇_θ L(θ_k)`. -/
lemma gdIterate_mseLoss_succ
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m)) (η : ℝ) (θ₀ : EuclideanSpace ℝ (Fin P)) (k : ℕ) :
    gdIterate (mseLoss f X y) (fun _ => η) θ₀ (k + 1) =
      gdIterate (mseLoss f X y) (fun _ => η) θ₀ k -
        η • gradient (mseLoss f X y) (gdIterate (mseLoss f X y) (fun _ => η) θ₀ k) := rfl


open scoped Matrix.Norms.Frobenius

attribute [local instance]
  Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace

/-- Gradient speed bound: the norm of the MSE gradient is controlled by the output Jacobian's
Frobenius norm and the residual norm: `‖∇_θ L(θ)‖ ≤ (1/m) ‖J(θ)‖_F ‖r(θ)‖`. This is Step 1 of
the Gap 5 displacement-integral bound (`InfiniteNTK.lean`): it bounds the instantaneous "speed"
`‖∂_t θ(t)‖ = ‖∇_θ L(θ(t))‖` of gradient flow. -/
theorem gradient_mseLoss_norm_le (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m)) (θ : EuclideanSpace ℝ (Fin P))
    (hdiff : ∀ α : Fin m, DifferentiableAt ℝ (fun θ' => f (X α) θ') θ) :
    ‖gradient (mseLoss f X y) θ‖ ≤
      (m : ℝ)⁻¹ * ‖outputJacobian f X θ‖ * ‖trainingResidual f X y θ‖ := by
  have heq : gradient (mseLoss f X y) θ =
      (m : ℝ)⁻¹ • (WithLp.toLp 2 ((outputJacobian f X θ)ᵀ *ᵥ (trainingResidual f X y θ).ofLp) :
        EuclideanSpace ℝ (Fin P)) := by
    rw [show gradient (mseLoss f X y) θ =
        WithLp.toLp 2 (gradient (mseLoss f X y) θ).ofLp from rfl]
    rw [gradient_mseLoss_eq_mulVec f X y θ hdiff]
    rfl
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (m : ℝ)⁻¹),
    mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ‖(WithLp.toLp 2 ((outputJacobian f X θ)ᵀ *ᵥ (trainingResidual f X y θ).ofLp) :
        EuclideanSpace ℝ (Fin P))‖ ≤
        ‖(outputJacobian f X θ)ᵀ‖ * ‖trainingResidual f X y θ‖ :=
      mulVec_frobenius_norm_le _ _
    _ = ‖outputJacobian f X θ‖ * ‖trainingResidual f X y θ‖ := by
      rw [Matrix.frobenius_norm_transpose]

end NTK

end
