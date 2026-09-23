/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Probability.StrongLaw
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
derived via a geometric argument on the sphere.

## Main definitions

* `NTK.empiricalNTKWithOuter` : the empirical NTK with arbitrary fixed outer coefficients.
* `NTK.empiricalNTK` : the simplified empirical NTK when `aⱼ² = 1`.
* `NTK.limitingNTK` : the limiting NTK `k(x, x')`.
* `NTK.ntkSummand` : the iid summand `σ'(wᵀx)σ'(wᵀx')` of the empirical average,
  with measurability/boundedness/integrability API (`measurable_ntkSummand`,
  `abs_ntkSummand_le`, `integrable_ntkSummand`).
* `NTK.gaussianRow_average_tendsto_integral` : reusable SLLN for empirical averages of
  measurable integrable functions of iid Gaussian rows.
* `NTK.ntk_convergence` : almost sure convergence `kₘ(x,x') → k(x,x')` (SLLN).
* `NTK.reluNTK_closedForm` : closed form `k(x,x') = xᵀx'·(π−arccos(xᵀx'))/(2π)` for ReLU.
* `NTK.trainingOutputs` : the vector `f(θ) = [f(x¹; θ), …, f(xᵐ; θ)]ᵀ` of predictions on the training dataset.
* `NTK.trainingResidual` : the residual error vector `r(θ) = f(θ) - y`.
* `NTK.mseLoss` : the empirical MSE loss objective `L(θ) = (1 / 2m) ‖r(θ)‖²`.
* `NTK.tangentFeature` : the sensitivity vector `x ↦ ∇_θ f(x; θ) ∈ ℝ^P`.
* `NTK.outputJacobian` : the network output Jacobian matrix `J(θ) ∈ ℝ^{m × P}`.
* `NTK.empiricalNTKMatrix` : the empirical NTK Gram matrix `K_t = J(θ) J(θ)ᵀ ∈ ℝ^{m × m}`.
* `NTK.gradient_flow_output_coord_ode` : coordinate ODE `∂_t f^α(t) = - (1/m) ∑_β K_t^{α β} r^β(t)` under gradient flow.
* `NTK.gradient_flow_output_vector_ode` : vector output ODE `∂_t f(t) = - (1/m) K_t r(t)`.
* `NTK.gradient_flow_residual_vector_ode` : vector residual ODE `∂_t r(t) = - (1/m) K_t r(t)`.

-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory Filter ConvexOpt
open scoped RealInnerProductSpace Matrix

namespace NTK

variable {d m : ℕ}

/-! ### Inner product and norm helpers -/

/-- The standard inner product on `Fin d → ℝ`. -/
noncomputable def innerProduct (x y : Fin d → ℝ) : ℝ :=
  ∑ k : Fin d, x k * y k

/-- Notation `x ⊙ y` for the standard inner product `innerProduct x y`. -/
infixl:73 " ⊙ " => innerProduct

lemma innerProduct_comm (x y : Fin d → ℝ) : x ⊙ y = y ⊙ x := by
  simp [innerProduct, mul_comm]

lemma innerProduct_self_nonneg (x : Fin d → ℝ) : 0 ≤ x ⊙ x :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

/-- `x ⊙ x` is the sum of the coordinate squares. -/
lemma innerProduct_self_eq_sum_sq (x : Fin d → ℝ) : x ⊙ x = ∑ k : Fin d, x k ^ 2 := by
  simp [innerProduct, pow_two]

/-- For the Euclidean `L²` norm on `EuclideanSpace ℝ (Fin d)`, `‖x‖² = x ⊙ x`.

The default norm on `Fin d → ℝ` is the sup norm, so the analogous statement is false for the raw
Pi type. -/
lemma norm_sq_eq_innerProduct (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ^ 2 = x.ofLp ⊙ x.ofLp := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa using (innerProduct_self_eq_sum_sq x.ofLp).symm

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
  (x ⊙ x') *
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
  (x ⊙ x') *
    ((m : ℝ)⁻¹ * ∑ j : Fin m,
      σ' (∑ k : Fin d, W₀ j k * x k) *
      σ' (∑ k : Fin d, W₀ j k * x' k))

-- The square of the square root of the inverse of m (cast to real) is the inverse of m.
private lemma sq_sqrt_inv_cast_nat (m : ℕ) :
    ((m : ℝ)⁻¹.sqrt) * ((m : ℝ)⁻¹.sqrt) = (m : ℝ)⁻¹ := by
  rw [← sq, Real.sq_sqrt]
  exact inv_nonneg.mpr (Nat.cast_nonneg m)

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
      rw [sq_sqrt_inv_cast_nat m, ← sq]
    _ = _ := by ring

/-- The Frobenius inner product of gradient features is the empirical NTK with the
outer-coefficient squares included. -/
lemma frobeniusInner_gradientMatrix_eq_empiricalNTKWithOuter
    (σ' : ℝ → ℝ) (outerCoeffs : Fin m → ℝ)
    (W₀ : Fin m → Fin d → ℝ) (x x' : Fin d → ℝ) :
    frobeniusInner
      (gradientMatrix (σ' := σ') outerCoeffs x W₀)
      (gradientMatrix (σ' := σ') outerCoeffs x' W₀) =
    empiricalNTKWithOuter σ' outerCoeffs W₀ x x' := by
  unfold frobeniusInner gradientMatrix empiricalNTKWithOuter innerProduct
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
  simp only [empiricalNTK, innerProduct_comm x x', mul_comm (σ' _) (σ' _)]

-- Helper 1: Reorder
private lemma quadruple_sum_comm {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ) :
    ∑ i : α, ∑ i' : β, ∑ j : γ, ∑ k : δ, f i i' j k =
      ∑ j : γ, ∑ k : δ, ∑ i : α, ∑ i' : β, f i i' j k := by
  calc
    ∑ i : α, ∑ i' : β, ∑ j : γ, ∑ k : δ, f i i' j k
        = ∑ x : α × β, ∑ j : γ, ∑ k : δ, f x.1 x.2 j k := by
            rw [← Fintype.sum_prod_type']
    _ = ∑ x : α × β, ∑ y : γ × δ, f x.1 x.2 y.1 y.2 := by
          congr 1
          ext x
          rw [← Fintype.sum_prod_type']
    _ = ∑ z : (α × β) × (γ × δ), f z.1.1 z.1.2 z.2.1 z.2.2 := by
          rw [← Fintype.sum_prod_type']
    _ = ∑ y : γ × δ, ∑ x : α × β, f x.1 x.2 y.1 y.2 := by
          simpa using
            (Fintype.sum_prod_type_right'
              (f := fun (x : α × β) (y : γ × δ) =>
                f x.1 x.2 y.1 y.2))
    _ = ∑ j : γ, ∑ k : δ, ∑ x : α × β, f x.1 x.2 j k := by
          simpa using
            (Fintype.sum_prod_type' (f := fun j k => ∑ x : α × β, f x.1 x.2 j k))
    _ = ∑ j : γ, ∑ k : δ, ∑ i : α, ∑ i' : β, f i i' j k := by
          congr 1
          ext j
          congr 1
          ext k
          simpa using (Fintype.sum_prod_type' (f := fun i i' => f i i' j k))

-- Helper 2: Expand
private lemma empiricalNTK_term_expand
    (σ' : ℝ → ℝ) (W₀ : Fin m → Fin d → ℝ) {n : ℕ} (α : Fin n → ℝ) (pts : Fin n → Fin d → ℝ)
    (i i' : Fin n) :
    α i * α i' * empiricalNTK σ' W₀ (pts i) (pts i') =
      ∑ j : Fin m, ∑ k : Fin d,
        (m : ℝ)⁻¹ *
          (α i * α i' * (pts i k * pts i' k) *
            (σ' (∑ l : Fin d, W₀ j l * pts i l) *
              σ' (∑ l : Fin d, W₀ j l * pts i' l))) := by
  unfold empiricalNTK innerProduct
  calc
    α i * α i' *
        ((∑ k : Fin d, pts i k * pts i' k) *
          ((m : ℝ)⁻¹ *
            ∑ j : Fin m, σ' (∑ k : Fin d, W₀ j k * pts i k) * σ' (∑ k : Fin d, W₀ j k * pts i' k)))
        =
          (α i * α i' * ∑ k : Fin d, pts i k * pts i' k) * (m : ℝ)⁻¹ *
            ∑ j : Fin m,
              σ' (∑ k : Fin d, W₀ j k * pts i k) *
                σ' (∑ k : Fin d, W₀ j k * pts i' k) := by
            ring
    _ =
      (α i * α i' * ∑ k : Fin d, pts i k * pts i' k) * (m : ℝ)⁻¹ *
        ∑ j : Fin m, σ' (∑ k : Fin d, W₀ j k * pts i k) * σ' (∑ k : Fin d, W₀ j k * pts i' k)
        := by rfl
    _ =
        ((m : ℝ)⁻¹ * α i * α i') *
            ((∑ k : Fin d, pts i k * pts i' k) *
              ∑ j : Fin m, σ' (∑ k : Fin d, W₀ j k * pts i k) *
                σ' (∑ k : Fin d, W₀ j k * pts i' k)) := by
            ring
    _ =
        ((m : ℝ)⁻¹ * α i * α i') *
          ∑ k : Fin d,
            ∑ j : Fin m,
              (pts i k * pts i' k) *
                (σ' (∑ k : Fin d, W₀ j k * pts i k) *
                  σ' (∑ k : Fin d, W₀ j k * pts i' k)) := by
            rw [Fintype.sum_mul_sum]
    _ =
        ((m : ℝ)⁻¹ * α i * α i') *
          ∑ j : Fin m,
            ∑ k : Fin d,
              (pts i k * pts i' k) *
                (σ' (∑ k : Fin d, W₀ j k * pts i k) *
                  σ' (∑ k : Fin d, W₀ j k * pts i' k)) := by
            rw [Finset.sum_comm]
    _ = ∑ j : Fin m, ∑ k : Fin d,
          (m : ℝ)⁻¹ *
            (α i * α i' * (pts i k * pts i' k) *
              (σ' (∑ l : Fin d, W₀ j l * pts i l) *
                σ' (∑ l : Fin d, W₀ j l * pts i' l))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring

-- Helper 3: Square
private lemma empiricalNTK_term_square
    (σ' : ℝ → ℝ) (W₀ : Fin m → Fin d → ℝ) {n : ℕ} (α : Fin n → ℝ) (pts : Fin n → Fin d → ℝ)
    (j : Fin m) (k : Fin d) :
    ∑ i : Fin n, ∑ i' : Fin n,
      (m : ℝ)⁻¹ *
        (α i * α i' * (pts i k * pts i' k) *
          (σ' (∑ l : Fin d, W₀ j l * pts i l) *
            σ' (∑ l : Fin d, W₀ j l * pts i' l))) =
      (m : ℝ)⁻¹ *
        (∑ i : Fin n, α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
  calc
    ∑ i : Fin n, ∑ i' : Fin n,
      (m : ℝ)⁻¹ *
        (α i * α i' * (pts i k * pts i' k) *
          (σ' (∑ l : Fin d, W₀ j l * pts i l) *
            σ' (∑ l : Fin d, W₀ j l * pts i' l)))
        = ∑ i : Fin n, ∑ i' : Fin n,
            (m : ℝ)⁻¹ *
              ((α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) *
                (α i' * pts i' k * σ' (∑ l : Fin d, W₀ j l * pts i' l))) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro i' _
            ring
    _ = (m : ℝ)⁻¹ *
          ∑ i : Fin n, ∑ i' : Fin n,
            (α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) *
              (α i' * pts i' k * σ' (∑ l : Fin d, W₀ j l * pts i' l)) := by
            calc
              ∑ i : Fin n, ∑ i' : Fin n,
                  (m : ℝ)⁻¹ *
                    ((α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) *
                      (α i' * pts i' k * σ' (∑ l : Fin d, W₀ j l * pts i' l)))
                  =
                    ∑ i : Fin n,
                      (m : ℝ)⁻¹ *
                        ∑ i' : Fin n,
                          (α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) *
                            (α i' * pts i' k * σ' (∑ l : Fin d, W₀ j l * pts i' l)) := by
                      apply Finset.sum_congr rfl
                      intro i _
                      rw [← Finset.mul_sum]
              _ = (m : ℝ)⁻¹ *
                    ∑ i : Fin n, ∑ i' : Fin n,
                      (α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) *
                        (α i' * pts i' k * σ' (∑ l : Fin d, W₀ j l * pts i' l)) := by
                      rw [← Finset.mul_sum]
    _ = (m : ℝ)⁻¹ *
          (∑ i : Fin n, α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
            rw [pow_two, Fintype.sum_mul_sum]

/-- The empirical NTK is positive semidefinite: for any finite set of points
and coefficients `(αᵢ, xᵢ)`, `∑ᵢⱼ αᵢαⱼ kₘ(xᵢ, xⱼ) ≥ 0`.
This follows from being the Gram matrix of the gradient features. -/
lemma empiricalNTK_posSemidef
    (σ' : ℝ → ℝ) (W₀ : Fin m → Fin d → ℝ)
    {n : ℕ} (α : Fin n → ℝ) (pts : Fin n → Fin d → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      α i * α j * empiricalNTK σ' W₀ (pts i) (pts j) := by
  have h_eq : ∑ i : Fin n, ∑ j : Fin n, α i * α j * empiricalNTK σ' W₀ (pts i) (pts j) =
      (m : ℝ)⁻¹ * ∑ j : Fin m, ∑ k : Fin d,
        (∑ i : Fin n, α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
    calc
      ∑ i : Fin n, ∑ j : Fin n, α i * α j * empiricalNTK σ' W₀ (pts i) (pts j)
          = ∑ i : Fin n, ∑ i' : Fin n, ∑ j : Fin m, ∑ k : Fin d,
              (m : ℝ)⁻¹ *
                (α i * α i' * (pts i k * pts i' k) *
                  (σ' (∑ l : Fin d, W₀ j l * pts i l) *
                    σ' (∑ l : Fin d, W₀ j l * pts i' l))) := by
              -- Step 1: Expand the kernel into a quadruple sum.
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro i' _
              exact empiricalNTK_term_expand σ' W₀ α pts i i'
      _ = ∑ j : Fin m, ∑ k : Fin d, ∑ i : Fin n, ∑ i' : Fin n,
            (m : ℝ)⁻¹ *
              (α i * α i' * (pts i k * pts i' k) *
                (σ' (∑ l : Fin d, W₀ j l * pts i l) *
                  σ' (∑ l : Fin d, W₀ j l * pts i' l))) := quadruple_sum_comm _
      _ = (m : ℝ)⁻¹ * ∑ j : Fin m, ∑ k : Fin d,
            (∑ i : Fin n,
              α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
              -- Step 2: Repackage the quadruple sum as a sum of squares.
              calc
                ∑ j : Fin m, ∑ k : Fin d, ∑ i : Fin n, ∑ i' : Fin n,
                    (m : ℝ)⁻¹ *
                      (α i * α i' * (pts i k * pts i' k) *
                        (σ' (∑ l : Fin d, W₀ j l * pts i l) *
                          σ' (∑ l : Fin d, W₀ j l * pts i' l)))
                    = ∑ j : Fin m, ∑ k : Fin d,
                        (m : ℝ)⁻¹ *
                          (∑ i : Fin n,
                            α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
                            apply Finset.sum_congr rfl
                            intro j _
                            apply Finset.sum_congr rfl
                            intro k _
                            exact empiricalNTK_term_square σ' W₀ α pts j k
                _ = (m : ℝ)⁻¹ * ∑ j : Fin m, ∑ k : Fin d,
                      (∑ i : Fin n, α i * pts i k * σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
                            calc
                              ∑ j : Fin m, ∑ k : Fin d,
                                  (m : ℝ)⁻¹ *
                                    (∑ i : Fin n,
                                      α i * pts i k *
                                        σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2
                                  =
                                    ∑ j : Fin m,
                                      (m : ℝ)⁻¹ *
                                        ∑ k : Fin d,
                                          (∑ i : Fin n,
                                            α i * pts i k *
                                              σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
                                      apply Finset.sum_congr rfl
                                      intro j _
                                      rw [← Finset.mul_sum]
                              _ = (m : ℝ)⁻¹ * ∑ j : Fin m, ∑ k : Fin d,
                                    (∑ i : Fin n,
                                      α i * pts i k *
                                        σ' (∑ l : Fin d, W₀ j l * pts i l)) ^ 2 := by
                                      rw [← Finset.mul_sum]
  rw [h_eq]
  apply mul_nonneg
  · exact inv_nonneg.mpr (Nat.cast_nonneg m)
  · apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro k _
    exact sq_nonneg _

/-! ### Limiting NTK (Definition 4.6) -/

/-- **Definition 4.6** (Limiting neural tangent kernel).
The limiting NTK is the expectation of the gradient-feature inner product
as `m → ∞`:
  `k(x, x') = (xᵀx') · 𝔼_{w ~ 𝒩(0,Iᵈ)}[σ'(wᵀx) σ'(wᵀx')]`.

This is positive semidefinite and symmetric. For the ReLU, it has the closed form
given in `reluNTK_closedForm`. -/
noncomputable def limitingNTK (σ' : ℝ → ℝ) (x x' : Fin d → ℝ) : ℝ :=
  (x ⊙ x') *
    ∫ w : Fin d → ℝ,
      σ' (w ⊙ x) * σ' (w ⊙ x') ∂(gaussianRowMeasure d)

/-- The limiting NTK is symmetric. -/
lemma limitingNTK_symm (σ' : ℝ → ℝ) (x x' : Fin d → ℝ) :
    limitingNTK σ' x x' = limitingNTK σ' x' x := by
  simp only [limitingNTK, innerProduct_comm x x', mul_comm (σ' _) (σ' _)]

/-! ### Measurability and integrability of the NTK summand -/

/-- The standard Gaussian row measure `𝒩(0, Iᵈ)` is a probability measure. -/
instance : IsProbabilityMeasure (gaussianRowMeasure d) := by
  unfold gaussianRowMeasure
  infer_instance

/-- The dot product `w ↦ wᵀx` with a fixed vector is measurable. -/
lemma measurable_innerProduct_left (x : Fin d → ℝ) :
    Measurable fun w : Fin d → ℝ => w ⊙ x :=
  Finset.measurable_sum _ fun k _ => (measurable_pi_apply k).mul measurable_const

/-- The iid summand appearing in the empirical NTK average:
  `Y(w) = σ'(wᵀx) · σ'(wᵀx')`.
The empirical NTK is `xᵀx'` times the empirical mean of `Y` over the rows, and the
limiting NTK is `xᵀx'` times the expectation of `Y`. -/
noncomputable def ntkSummand (σ' : ℝ → ℝ) (x x' : Fin d → ℝ) (w : Fin d → ℝ) : ℝ :=
  σ' (w ⊙ x) * σ' (w ⊙ x')

/-- The NTK summand is measurable whenever `σ'` is. -/
lemma measurable_ntkSummand {σ' : ℝ → ℝ} (hσ' : Measurable σ') (x x' : Fin d → ℝ) :
    Measurable (ntkSummand σ' x x') :=
  (hσ'.comp (measurable_innerProduct_left x)).mul (hσ'.comp (measurable_innerProduct_left x'))

/-- If `σ'` is bounded by `C`, the NTK summand is bounded by `C²`. -/
lemma abs_ntkSummand_le {σ' : ℝ → ℝ} {C : ℝ} (hC : ∀ z, |σ' z| ≤ C)
    (x x' : Fin d → ℝ) (w : Fin d → ℝ) :
    |ntkSummand σ' x x' w| ≤ C * C := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (σ' 0)) (hC 0)
  rw [ntkSummand, abs_mul]
  exact mul_le_mul (hC _) (hC _) (abs_nonneg _) hC0

/-- A bounded measurable NTK summand is integrable against the Gaussian row measure. -/
lemma integrable_ntkSummand {σ' : ℝ → ℝ} (hσ'm : Measurable σ') {C : ℝ}
    (hC : ∀ z, |σ' z| ≤ C) (x x' : Fin d → ℝ) :
    Integrable (ntkSummand σ' x x') (gaussianRowMeasure d) :=
  Integrable.of_bound (measurable_ntkSummand hσ'm x x').aestronglyMeasurable (C * C)
    (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs]; exact abs_ntkSummand_le hC x x' w)

/-! ### Almost sure convergence of the empirical NTK (Lemma 4.3) -/

/-- The width-`m` empirical NTK built from the first `m` rows of an infinite iid
initialization. This is the right object for the notes' `m → ∞` limit. -/
noncomputable def empiricalNTKFromRows
    (σ' : ℝ → ℝ)
    (rows : ℕ → Fin d → ℝ)
    (width : ℕ)
    (x x' : Fin d → ℝ) : ℝ :=
  (x ⊙ x') *
    ((width : ℝ)⁻¹ * ∑ j : Fin width,
      σ' (rows j.val ⊙ x) * σ' (rows j.val ⊙ x'))

/-- The strong law for empirical averages of a measurable integrable function of
i.i.d. Gaussian rows. This packages the product-measure independence, identical-distribution,
expectation-transport, and `Finset.range`/`Fin` conversion used by kernel limit proofs. -/
lemma gaussianRow_average_tendsto_integral
    (g : (Fin d → ℝ) → ℝ)
    (hg_meas : Measurable g)
    (hg_int : Integrable g (gaussianRowMeasure d)) :
    ∀ᵐ rows : ℕ → Fin d → ℝ
      ∂(Measure.infinitePi fun _ : ℕ => gaussianRowMeasure d),
      Filter.Tendsto
        (fun width : ℕ => (width : ℝ)⁻¹ * ∑ j : Fin width, g (rows j))
        Filter.atTop
        (nhds (∫ w, g w ∂(gaussianRowMeasure d))) := by
  set μ := Measure.infinitePi (fun _ : ℕ => gaussianRowMeasure d)
  have hmap_eval : ∀ i : ℕ, μ.map (fun rows => rows i) = gaussianRowMeasure d :=
    fun i => Measure.infinitePi_map_eval _ i
  have hmp : MeasurePreserving (fun rows : ℕ → Fin d → ℝ => rows 0) μ
      (gaussianRowMeasure d) :=
    measurePreserving_eval_infinitePi (fun _ : ℕ => gaussianRowMeasure d) 0
  have hint : Integrable (fun rows : ℕ → Fin d → ℝ => g (rows 0)) μ :=
    (hmp.integrable_comp hg_meas.aestronglyMeasurable).2 hg_int
  have hindep : Pairwise (Function.onFun (· ⟂ᵢ[μ] ·) fun j rows => g (rows j)) := by
    have h := iIndepFun_infinitePi (P := fun _ : ℕ => gaussianRowMeasure d)
      (X := fun _ : ℕ => g) (fun _ => hg_meas)
    intro i j hij
    exact h.indepFun hij
  have hident : ∀ i : ℕ,
      IdentDistrib (fun rows : ℕ → Fin d → ℝ => g (rows i))
        (fun rows : ℕ → Fin d → ℝ => g (rows 0)) μ μ := by
    intro i
    have hcoord : IdentDistrib (fun rows : ℕ → Fin d → ℝ => rows i)
        (fun rows : ℕ → Fin d → ℝ => rows 0) μ μ := by
      refine ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable, ?_⟩
      rw [hmap_eval i, hmap_eval 0]
    exact hcoord.comp hg_meas
  have hslln : ∀ᵐ rows ∂μ, Filter.Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, g (rows i))
      Filter.atTop (nhds (∫ rows, g (rows 0) ∂μ)) :=
    strong_law_ae _ hint hindep hident
  have hexp : ∫ rows, g (rows 0) ∂μ = ∫ w, g w ∂(gaussianRowMeasure d) := by
    rw [← hmap_eval 0]
    exact (MeasureTheory.integral_map (measurable_pi_apply 0).aemeasurable
      hg_meas.stronglyMeasurable.aestronglyMeasurable).symm
  filter_upwards [hslln] with rows hrows
  rw [← hexp]
  convert hrows using 1
  ext width
  rw [smul_eq_mul, Fin.sum_univ_eq_sum_range (fun i => g (rows i)) width]

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
  have hg_meas : Measurable (ntkSummand σ' x x') := measurable_ntkSummand hσ'_meas x x'
  have hg_int : Integrable (ntkSummand σ' x x') (gaussianRowMeasure d) :=
    integrable_ntkSummand hσ'_meas hC x x'
  filter_upwards [gaussianRow_average_tendsto_integral (ntkSummand σ' x x') hg_meas hg_int]
    with rows hrows
  exact hrows.const_mul (x ⊙ x')

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
lemma innerProduct_eq_inner_toLp (x y : Fin d → ℝ) :
    x ⊙ y = ⟪WithLp.toLp 2 y, WithLp.toLp 2 x⟫ := by
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [innerProduct, dotProduct]

/-- Pushforward of `gaussianRowMeasure` by the linear functional `w ↦ wᵀx` is a 1D Gaussian
with mean `0` and variance `xᵀx`. -/
lemma map_gaussianRowMeasure_innerProduct (x : Fin d → ℝ) :
    Measure.map (fun w => w ⊙ x) (gaussianRowMeasure d) =
      gaussianReal 0 (Real.toNNReal (x ⊙ x)) := by
  have h_eq : (fun w : Fin d → ℝ => w ⊙ x) =
      (fun (v : EuclideanSpace ℝ (Fin d)) => innerSL ℝ (WithLp.toLp 2 x) v) ∘ (WithLp.toLp 2) := by
    ext w
    dsimp
    rw [← innerProduct_eq_inner_toLp w x]
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
        x ⊙ x := by
      rw [variance_dual_stdGaussian]
      rw [innerSL_apply_norm]
      rw [norm_sq_eq_innerProduct (WithLp.toLp 2 x)]
    rw [h_mean, h_var]
  all_goals fun_prop

/--
Informal proof:
The standard Gaussian measure on ℝ is absolutely continuous with respect to Lebesgue measure.
Since the Lebesgue measure of any singleton is zero and the Gaussian measure is the integral of a
density with respect to Lebesgue measure, the Gaussian measure of every singleton is also zero.
Specifically, `gaussianReal 0 1 {x} = ∫_ {x} p(x) dλ = 0`.
See Kallenberg, *Foundations of Modern Probability*:
<https://link.springer.com/book/10.1007/978-1-4757-4015-8>.
-/
lemma gaussianReal_singleton_eq_zero (x : ℝ) : (gaussianReal 0 1).real {x} = 0 := by
  have h_ac : gaussianReal 0 1 ≪ volume := gaussianReal_absolutelyContinuous 0 (by norm_num)
  have h_vol : volume {x} = 0 := by simp
  have h : (gaussianReal 0 1) {x} = 0 := h_ac h_vol
  simp [measureReal_def, h]

/-- The standard Gaussian gives mass `1/2` to `[0, ∞)`. -/
lemma gaussianReal_Ici_one_half : (gaussianReal 0 1).real (Set.Ici 0) = 1 / 2 := by
  have hneg : (gaussianReal 0 1).map (fun y => -y) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg]
    simp
  have h_symm : (gaussianReal 0 1).real (Set.Ici 0) = (gaussianReal 0 1).real (Set.Iic 0) := by
    have hpre : (fun y : ℝ => -y) ⁻¹' Set.Ici 0 = Set.Iic 0 := by ext y; simp
    have h1 : ((gaussianReal 0 1).map (fun y => -y)).real (Set.Ici 0) =
        (gaussianReal 0 1).real (Set.Iic 0) := by
      rw [measureReal_def, Measure.map_apply (by fun_prop) measurableSet_Ici, hpre]
      rfl
    rw [hneg] at h1
    exact h1
  have h_add : (gaussianReal 0 1).real (Set.Ici 0) + (gaussianReal 0 1).real (Set.Iic 0) = 1 := by
    have h := measureReal_union_add_inter (μ := gaussianReal 0 1) (s := Set.Ici 0)
      (t := Set.Iic 0) measurableSet_Iic (measure_ne_top _ _) (measure_ne_top _ _)
    have h_union : (Set.Ici 0 : Set ℝ) ∪ Set.Iic 0 = Set.univ := by ext y; simp
    have h_inter : (Set.Ici 0 : Set ℝ) ∩ Set.Iic 0 = {0} := by
      ext y
      have h_iff : 0 ≤ y ∧ y ≤ 0 ↔ y = 0 := by
        constructor
        · intro h_le; exact le_antisymm h_le.2 h_le.1
        · intro h_eq; rw [h_eq]; exact ⟨le_refl 0, le_refl 0⟩
      exact h_iff
    have h_univ : (gaussianReal 0 1).real Set.univ = 1 := by simp [measureReal_def]
    rw [h_union, h_inter, h_univ] at h
    have h_zero : (gaussianReal 0 1).real {0} = 0 := gaussianReal_singleton_eq_zero 0
    linarith
  linarith [h_symm, h_add]

/-- For unit vectors, inner product `1` forces equality. -/
lemma innerProduct_eq_one_iff_eq (x x' : Fin d → ℝ) (hx : x ⊙ x = 1) (hx' : x' ⊙ x' = 1) :
    x ⊙ x' = 1 ↔ x = x' := by
  constructor
  · intro h
    funext i
    have hsum_eq : (x - x') ⊙ (x - x') = (x ⊙ x) - 2 * (x ⊙ x') + (x' ⊙ x') := by
      unfold innerProduct
      simp only [Pi.sub_apply]
      have step1 : (fun (i : Fin d) => (x i - x' i) * (x i - x' i)) =
                   fun (i : Fin d) => x i * x i - 2 * (x i * x' i) + x' i * x' i := by
        funext j; ring
      rw [step1]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hzero : (x - x') ⊙ (x - x') = 0 := by
      calc (x - x') ⊙ (x - x') = (x ⊙ x) - 2 * (x ⊙ x') + (x' ⊙ x') := hsum_eq
        _ = 1 - 2 * 1 + 1 := by rw [hx, hx', h]
        _ = 0 := by ring
    have h_i : (x i - x' i) ^ 2 = 0 := by
      have hsum_sq : (x - x') ⊙ (x - x') = ∑ k : Fin d, (x k - x' k) ^ 2 := by
        unfold innerProduct
        simp only [Pi.sub_apply]
        have : (fun (j : Fin d) => (x j - x' j) * (x j - x' j)) = fun j => (x j - x' j) ^ 2 := by
          funext j; ring
        rw [this]
      rw [hsum_sq] at hzero
      have := Finset.sum_eq_zero_iff_of_nonneg
        (fun (k : Fin d) _ => sq_nonneg (x k - x' k)) |>.mp hzero i (Finset.mem_univ _)
      exact this
    have : x i - x' i = 0 := by simpa using h_i
    linarith
  · rintro rfl
    exact hx

/-- For unit vectors, inner product `-1` forces `x' = -x`. -/
lemma innerProduct_eq_neg_one_iff_eq_neg (x x' : Fin d → ℝ)
    (hx : x ⊙ x = 1) (hx' : x' ⊙ x' = 1) :
    x ⊙ x' = -1 ↔ x' = -x := by
  constructor
  · intro h
    funext i
    have hsum_eq : (x + x') ⊙ (x + x') = (x ⊙ x) + 2 * (x ⊙ x') + (x' ⊙ x') := by
      unfold innerProduct
      simp only [Pi.add_apply]
      have step1 : (fun (i : Fin d) => (x i + x' i) * (x i + x' i)) =
                   fun (i : Fin d) => x i * x i + 2 * (x i * x' i) + x' i * x' i := by
        funext j; ring
      rw [step1]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hzero : (x + x') ⊙ (x + x') = 0 := by
      calc (x + x') ⊙ (x + x') = (x ⊙ x) + 2 * (x ⊙ x') + (x' ⊙ x') := hsum_eq
        _ = 1 + 2 * (-1) + 1 := by rw [hx, hx', h]
        _ = 0 := by ring
    have h_i : (x i + x' i) ^ 2 = 0 := by
      have hsum_sq : (x + x') ⊙ (x + x') = ∑ k : Fin d, (x k + x' k) ^ 2 := by
        unfold innerProduct
        simp only [Pi.add_apply]
        have : (fun (j : Fin d) => (x j + x' j) * (x j + x' j)) = fun j => (x j + x' j) ^ 2 := by
          funext j; ring
        rw [this]
      rw [hsum_sq] at hzero
      have := Finset.sum_eq_zero_iff_of_nonneg
        (fun (k : Fin d) _ => sq_nonneg (x k + x' k)) |>.mp hzero i (Finset.mem_univ _)
      exact this
    have : x i + x' i = 0 := by simpa using h_i
    rw [Pi.neg_apply]
    linarith
  · intro h
    unfold innerProduct
    simp only [h, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    have : ∑ i : Fin d, x i * x i = x ⊙ x := rfl
    rw [this, hx]

open scoped RealInnerProductSpace

/-- The row inner product `y.ofLp ⊙ x` agrees with the `EuclideanSpace` inner product
`⟪y, WithLp.toLp 2 x⟫` for `y` already in `EuclideanSpace` form. -/
lemma ofLp_innerProduct_eq_inner (x : Fin d → ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    y.ofLp ⊙ x = ⟪y, WithLp.toLp 2 x⟫ := by
  rw [show y = WithLp.toLp 2 (y.ofLp) by rfl]
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [innerProduct, dotProduct, star_trivial]
  simp_rw [mul_comm]

/-- Pushing the integral over the row-wise Gaussian forward to `EuclideanSpace` via `toLp 2`. -/
lemma integral_gaussianRowMeasure_eq_integral_stdGaussian
    {d : ℕ} (f : (Fin d → ℝ) → ℝ) :
    ∫ w, f w ∂(gaussianRowMeasure d) =
    ∫ y, f y.ofLp ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  rw [← map_pi_eq_stdGaussian (ι := Fin d)]
  rw [show Measure.map (WithLp.toLp 2) (Measure.pi fun x => gaussianReal 0 1) =
        Measure.map ⇑(MeasurableEquiv.toLp 2 (Fin d → ℝ)) (Measure.pi fun x => gaussianReal 0 1)
      by rw [MeasurableEquiv.coe_toLp]]
  rw [integral_map_equiv (MeasurableEquiv.toLp 2 (Fin d → ℝ))]
  simp [WithLp.ofLp_toLp, gaussianRowMeasure]

/-- `reluIndicator (w ⊙ x)` is the indicator of the closed halfspace `{w | w ⊙ x ≥ 0}`. -/
lemma reluIndicator_eq_indicator_Ici (x : Fin d → ℝ) :
    (fun w => reluIndicator (w ⊙ x)) = Set.indicator {w | w ⊙ x ≥ 0} (fun _ => 1) := by
  ext w
  simp [reluIndicator, Set.indicator]

/-- The product of two `reluIndicator`s is the indicator of the intersection of halfspaces. -/
lemma integral_reluIndicator_mul_eq_measure (x x' : Fin d → ℝ) :
    ∫ w, reluIndicator (w ⊙ x) * reluIndicator (w ⊙ x') ∂(gaussianRowMeasure d) =
      (gaussianRowMeasure d).real ({w | w ⊙ x ≥ 0} ∩ {w | w ⊙ x' ≥ 0}) := by
  have h_eq : (fun w => reluIndicator (w ⊙ x) * reluIndicator (w ⊙ x')) =
      Set.indicator ({w | w ⊙ x ≥ 0} ∩ {w | w ⊙ x' ≥ 0}) (fun _ => 1) := by
    ext w
    simp [reluIndicator, Set.indicator]
    split_ifs <;> tauto
  have h_meas : MeasurableSet ({w | w ⊙ x ≥ 0} ∩ {w | w ⊙ x' ≥ 0}) := by
    apply MeasurableSet.inter
    · exact measurableSet_Ici.preimage (measurable_innerProduct_left x)
    · exact measurableSet_Ici.preimage (measurable_innerProduct_left x')
  rw [h_eq]
  rw [integral_indicator h_meas]
  simp [measureReal_def]

/-- The joint law of the first two coordinate projections under a product probability measure
is the product of the first two marginals. -/
lemma map_pi_eval_two {d : ℕ} (hd : 2 ≤ d) {μ : Fin d → Measure ℝ}
    [∀ i, IsProbabilityMeasure (μ i)] :
    Measure.map (fun t : Fin d → ℝ => (t ⟨0, by linarith⟩, t ⟨1, by linarith⟩)) (Measure.pi μ) =
      (μ ⟨0, by linarith⟩).prod (μ ⟨1, by linarith⟩) := by
  have h_indep : iIndepFun (fun i (t : Fin d → ℝ) => t i) (Measure.pi μ) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have h01 : (fun (t : Fin d → ℝ) => t ⟨0, by linarith⟩) ⟂ᵢ[Measure.pi μ]
      (fun t => t ⟨1, by linarith⟩) := by
    refine h_indep.indepFun ?_
    intro h_eq
    have h_val : (⟨0, by linarith⟩ : Fin d).val = (⟨1, by linarith⟩ : Fin d).val := by rw [h_eq]
    simp at h_val
  have h_map := IndepFun.map_prod_eq_prod_map_map
    ((measurable_pi_apply (⟨0, by linarith⟩ : Fin d)).aemeasurable)
    ((measurable_pi_apply (⟨1, by linarith⟩ : Fin d)).aemeasurable) h01
  simpa only [Measure.pi_map_eval, measure_univ, Finset.prod_const_one, one_smul] using h_map

/-- The angle between two unit vectors in ℝᵈ:
  `angle x x' = arccos(xᵀx')` for `x ⊙ x = x' ⊙ x' = 1`. -/
noncomputable def vectorAngle (x x' : Fin d → ℝ) : ℝ :=
  Real.arccos (x ⊙ x')

/--
Informal proof:
Let $x$ and $x'$ be unit vectors in $\mathbb{R}^d$.
The integral $\int \mathbf{1}[w^\top x \ge 0] \mathbf{1}[w^\top x' \ge 0] d\mu(w)$
where $\mu$ is the standard normal distribution
is the probability that a standard normal vector $w$ has non-negative inner products
with both $x$ and $x'$.
Because the standard normal distribution is rotationally symmetric, we can project
$w$ onto the 2D subspace spanned by $x$ and $x'$.
The projection is a standard 2D normal vector.
In 2D, the region $w^\top x \ge 0$ and $w^\top x' \ge 0$ is a sector.
The angle between $x$ and $x'$ is $\theta = \arccos(x^\top x')$.
The boundary of the region $w^\top x \ge 0$ is orthogonal to $x$.
Thus, the angle of the sector where both are non-negative is $\pi - \theta$.
Since the 2D standard normal distribution is rotationally symmetric, the probability
of falling in this sector is the angle divided by $2\pi$,
which is $(\pi - \theta) / (2\pi)$.
See Section 4.3 (Proposition 4.2) of Telgarsky's Deep Learning Theory lecture notes
(https://mjt.cs.illinois.edu/dlt/two.pdf) or Cho & Saul (2009)
"Kernel Methods for Deep Learning"
(https://papers.nips.cc/paper_files/paper/2009/file/5751ec3e9a4feab575962e78e006250d-Paper.pdf)
for this standard geometric argument.
-/
lemma prob_halfspace_intersect
    (x x' : Fin d → ℝ)
    (hx : x ⊙ x = 1)
    (hx' : x' ⊙ x' = 1) :
    ∫ w : Fin d → ℝ, reluIndicator (w ⊙ x) * reluIndicator (w ⊙ x') ∂(gaussianRowMeasure d) =
      (Real.pi - Real.arccos (x ⊙ x')) / (2 * Real.pi) := by
  sorry

/-- **Proposition 4.2** (ReLU NTK closed form, Telgarsky 2021).
For `σ' = 1[· ≥ 0]` (the ReLU derivative) and `x, x' ∈ ℝᵈ` with
`x ⊙ x = x' ⊙ x' = 1`:
  `k(x, x') = (xᵀx') · (π − arccos(xᵀx')) / (2π)`.

**Proof sketch:**
- By rotational invariance of `𝒩(0, Iᵈ)`, we may project `w` onto `span(x, x')`.
- In the 2D plane, `w` is effectively uniform on the unit circle.
- The event `{wᵀx ≥ 0} ∩ {wᵀx' ≥ 0}` is a sector of angle `π − θ` where `θ = arccos(xᵀx')`.
- The probability of this sector is `(π − θ)/(2π)`.
- Multiplying by `xᵀx'` gives the result. -/
theorem reluNTK_closedForm
    (x x' : Fin d → ℝ)
    (hx : x ⊙ x = 1)
    (hx' : x' ⊙ x' = 1) :
    limitingNTK reluIndicator x x' =
      (x ⊙ x') * (Real.pi - Real.arccos (x ⊙ x')) / (2 * Real.pi) := by
  unfold limitingNTK
  rw [prob_halfspace_intersect x x' hx hx']
  ring

/-- The ReLU NTK is nonneg when `xᵀx' ≥ 0`. -/
lemma reluNTK_nonneg_of_nonneg_inner
    (x x' : Fin d → ℝ)
    (hx : x ⊙ x = 1) (hx' : x' ⊙ x' = 1)
    (hinn : 0 ≤ x ⊙ x') :
    0 ≤ limitingNTK reluIndicator x x' := by
  rw [reluNTK_closedForm x x' hx hx']
  apply div_nonneg
  · apply mul_nonneg hinn
    linarith [Real.arccos_le_pi (x ⊙ x'), Real.pi_pos]
  · linarith [Real.pi_pos]

/-- The ReLU NTK at equal inputs normalized by the local inner product. -/
lemma reluNTK_self
    (x : Fin d → ℝ) (hx : x ⊙ x = 1) :
    limitingNTK reluIndicator x x = 1 / 2 := by
  rw [reluNTK_closedForm x x hx hx]
  rw [hx]
  simp [Real.arccos_one]
  ring_nf
  simp [Real.pi_pos.ne']

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
  unfold mseLoss
  rw [EuclideanSpace.real_norm_sq_eq]
  rfl

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
  simp only [empiricalNTKMatrix, Matrix.mul_apply, Matrix.transpose_apply, outputJacobian, Matrix.of_apply]
  rw [show tangentFeature f (X α) θ = WithLp.toLp 2 (tangentFeature f (X α) θ).ofLp by rfl]
  rw [show tangentFeature f (X β) θ = WithLp.toLp 2 (tangentFeature f (X β) θ).ofLp by rfl]
  rw [EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, mul_comm]

/-! ### Positive Semidefiniteness and Gram Factorization -/

/-- The empirical NTK Gram matrix is positive semidefinite (`PosSemidef`) for any parameter state. -/
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

/-! ### Compatibility with Existing Shallow Network and Gradient Matrices -/

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
    exact (frobeniusInner_gradientMatrix_eq_empiricalNTKWithOuter σ' outerCoeffs W₀ (X α) (X β)).symm
  rw [h_eq]
  have h1 : (1 : Matrix (Fin m × Fin d) (Fin m × Fin d) ℝ).PosSemidef := Matrix.PosSemidef.one
  have h := h1.mul_mul_conjTranspose_same (Matrix.of fun α (j, k) => gradientMatrix (σ' := σ') outerCoeffs (X α) W₀ j k)
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
    exact (empiricalNTKWithOuter_eq_empiricalNTK_of_sq_one σ' outerCoeffs W₀ (X α) (X β) houter).symm
  rw [h_eq]
  exact empiricalNTKWithOuter_dataset_posSemidef σ' outerCoeffs W₀ X

/-! ### Gradient of the MSE Loss -/

lemma hasFDerivAt_sq_diff (θ : EuclideanSpace ℝ (Fin P)) {g : EuclideanSpace ℝ (Fin P) → ℝ}
    (hg : DifferentiableAt ℝ g θ) (c : ℝ) :
    HasFDerivAt (fun θ' => (g θ' - c) ^ 2)
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin P)) ((2 * (g θ - c)) • gradient g θ)) θ := by
  have h1 : HasFDerivAt (fun θ' => g θ' - c) (fderiv ℝ g θ) θ := by
    have h := hg.hasFDerivAt.sub (hasFDerivAt_const c θ)
    rw [sub_zero] at h
    exact h
  have h2 := h1.mul h1
  have h_eq : (fun θ' => (g θ' - c) ^ 2) = (fun θ' => (g θ' - c) * (g θ' - c)) := by
    ext; ring
  rw [h_eq]
  convert h2 using 1
  ext v
  have h_grad : fderiv ℝ g θ v = ⟪gradient g θ, v⟫ := by
    rw [← toDual_gradient, InnerProductSpace.toDual_apply_apply]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [h_grad]
  simp only [InnerProductSpace.toDual_apply_apply, inner_smul_left, starRingEnd_apply, star_trivial]
  ring

/-- The gradient of the empirical MSE loss with respect to parameters:
  `∇_θ L(θ) = (1 / m) ∑_α (f(x^α; θ) - y^α) ∇_θ f(x^α; θ)`. -/
theorem gradient_mseLoss (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m)) (θ : EuclideanSpace ℝ (Fin P))
    (hdiff : ∀ α : Fin m, DifferentiableAt ℝ (fun θ' => f (X α) θ') θ) :
    gradient (mseLoss f X y) θ = (m : ℝ)⁻¹ • ∑ α : Fin m, (trainingResidual f X y θ α) • tangentFeature f (X α) θ := by
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
  have h_loss_eq : mseLoss f X y = fun θ' => (2 * (m : ℝ))⁻¹ * ∑ α : Fin m, (f (X α) θ' - y α) ^ 2 := by
    ext θ'
    unfold mseLoss trainingResidual trainingOutputs
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
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
  exact h_grad.gradient

/-- Coordinate-wise formulation matching the Jacobian-residual product:
  `[∇_θ L(θ)]_j = (1 / m) [J(θ)ᵀ r(θ)]_j = (1 / m) ∑_α (f(x^α; θ) - y^α) [∇_θ f(x^α; θ)]_j`. -/
lemma gradient_mseLoss_apply_j (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (y : EuclideanSpace ℝ (Fin m)) (θ : EuclideanSpace ℝ (Fin P))
    (hdiff : ∀ α : Fin m, DifferentiableAt ℝ (fun θ' => f (X α) θ') θ) (j : Fin P) :
    gradient (mseLoss f X y) θ j = (m : ℝ)⁻¹ * ((outputJacobian f X θ)ᵀ *ᵥ (trainingResidual f X y θ).ofLp) j := by
  rw [gradient_mseLoss f X y θ hdiff]
  have h_eval : ((m : ℝ)⁻¹ • ∑ α : Fin m, (trainingResidual f X y θ α) • tangentFeature f (X α) θ) j =
      (m : ℝ)⁻¹ * ∑ α : Fin m, (trainingResidual f X y θ α) * tangentFeature f (X α) θ j := by
    change (m : ℝ)⁻¹ * (∑ α : Fin m, (trainingResidual f X y θ α) • tangentFeature f (X α) θ).ofLp j = _
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
    (gradient (mseLoss f X y) θ).ofLp = (m : ℝ)⁻¹ • ((outputJacobian f X θ)ᵀ *ᵥ (trainingResidual f X y θ).ofLp) := by
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
      gdIterate (mseLoss f X y) (fun _ => η) θ₀ k - η • gradient (mseLoss f X y) (gdIterate (mseLoss f X y) (fun _ => η) θ₀ k) := rfl

/-! ### Continuous Gradient Flow and Function-Space Dynamics -/

/-- Step 1 (Multivariate Chain Rule):
  `∂_t f^α(t) = ⟨∇_θ f(x^α; θ(t)), ∂_t θ(t)⟩`. -/
theorem hasDerivAt_trainingOutputs_coord
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ_traj : ℝ → EuclideanSpace ℝ (Fin P))
    (θ' : ℝ → EuclideanSpace ℝ (Fin P)) (t : ℝ) (α : Fin m)
    (hdiff : DifferentiableAt ℝ (fun θ' => f (X α) θ') (θ_traj t))
    (hθ : HasDerivAt θ_traj (θ' t) t) :
    HasDerivAt (fun s => (trainingOutputs f X (θ_traj s)) α)
      ⟪tangentFeature f (X α) (θ_traj t), θ' t⟫ t := by
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt t hθ
  have hgrad : fderiv ℝ (fun θ' => f (X α) θ') (θ_traj t) (θ' t) =
      ⟪tangentFeature f (X α) (θ_traj t), θ' t⟫ := by
    rw [← toDual_gradient, InnerProductSpace.toDual_apply_apply]
    rfl
  rw [hgrad] at hcomp
  exact hcomp

/-- Steps 2–4 (Assembly with Empirical NTK):
Along the gradient flow trajectory `∂_t θ(t) = -∇_θ L(θ(t))`, the output coordinates satisfy:
  `∂_t f^α(t) = - (1 / m) ∑_β K_t^{α β} (f^β(t) - y^β) = - (1 / m) ∑_β K_t^{α β} r^β(t)`. -/
theorem gradient_flow_output_coord_ode
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : GFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (t : ℝ) (α : Fin m)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => (trainingOutputs f X (θ_traj s)) α)
      (- (m : ℝ)⁻¹ * ∑ β : Fin m, empiricalNTKMatrix f X (θ_traj t) α β * (trainingResidual f X y (θ_traj t)) β) t := by
  have h_chain := hasDerivAt_trainingOutputs_coord f X θ_traj
    (fun s => -gradient (mseLoss f X y) (θ_traj s)) t α (hdiff α) (hflow.ode t)
  rw [gradient_mseLoss f X y (θ_traj t) hdiff] at h_chain
  have h_inner : ⟪tangentFeature f (X α) (θ_traj t),
      -((m : ℝ)⁻¹ • ∑ β : Fin m, (trainingResidual f X y (θ_traj t)) β • tangentFeature f (X β) (θ_traj t))⟫ =
      - (m : ℝ)⁻¹ * ∑ β : Fin m, empiricalNTKMatrix f X (θ_traj t) α β * (trainingResidual f X y (θ_traj t)) β := by
    rw [inner_neg_right, inner_smul_right, inner_sum]
    simp only [inner_smul_right]
    rw [neg_mul]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro β _
    have hK := (empiricalNTKMatrix_apply f X (θ_traj t) α β).symm
    rw [hK]
    ring
  rw [h_inner] at h_chain
  exact h_chain

lemma hasDerivAt_euclideanSpace (v : ℝ → EuclideanSpace ℝ (Fin m))
    (v' : EuclideanSpace ℝ (Fin m)) (t : ℝ) :
    HasDerivAt v v' t ↔ ∀ i : Fin m, HasDerivAt (fun s => v s i) (v' i) t := by
  let e := (EuclideanSpace.equiv (Fin m) ℝ).toContinuousLinearEquiv
  have h := hasDerivAt_pi (φ := fun s => e (v s)) (φ' := e v') (x := t)
  constructor
  · intro hv i
    have he := (e : EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → ℝ)).hasFDerivAt.comp_hasDerivAt t hv
    exact (h.mp he) i
  · intro hi
    have he : HasDerivAt (fun s => e (v s)) (e v') t := h.mpr hi
    have h_orig := (e.symm : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)).hasFDerivAt.comp_hasDerivAt t he
    convert h_orig
    · ext s; simp [e]
    · simp [e]

/-- Step 5 (Vector Matrix-Vector Formulation):
Along continuous gradient flow, the training output vector satisfies:
  `∂_t f(t) = - (1 / m) K_t r(t)`. -/
theorem gradient_flow_output_vector_ode
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : GFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (t : ℝ)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => trainingOutputs f X (θ_traj s))
      (WithLp.toLp 2 (- (m : ℝ)⁻¹ • ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ (trainingResidual f X y (θ_traj t)).ofLp))) t := by
  rw [hasDerivAt_euclideanSpace]
  intro α
  have h_coord := gradient_flow_output_coord_ode f X y hflow t α hdiff
  have h_eq : - (m : ℝ)⁻¹ * ∑ β : Fin m, empiricalNTKMatrix f X (θ_traj t) α β * (trainingResidual f X y (θ_traj t)) β =
      (WithLp.toLp 2 (- (m : ℝ)⁻¹ • ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ (trainingResidual f X y (θ_traj t)).ofLp)) : EuclideanSpace ℝ (Fin m)) α := by
    change - (m : ℝ)⁻¹ * ∑ β : Fin m, empiricalNTKMatrix f X (θ_traj t) α β * (trainingResidual f X y (θ_traj t)) β =
      (- (m : ℝ)⁻¹ • ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ (trainingResidual f X y (θ_traj t)).ofLp)) α
    have h_row : (empiricalNTKMatrix f X (θ_traj t)).row α =
      empiricalNTKMatrix f X (θ_traj t) α := rfl
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_apply, dotProduct, h_row]
  rw [h_eq] at h_coord
  exact h_coord

/-- Function-space residual ODE under gradient flow:
  `∂_t r(t) = - (1 / m) K_t r(t)`. -/
theorem gradient_flow_residual_vector_ode
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (y : EuclideanSpace ℝ (Fin m))
    {θ₀ : EuclideanSpace ℝ (Fin P)} {θ_traj : ℝ → EuclideanSpace ℝ (Fin P)}
    (hflow : GFTrajectory (mseLoss f X y) θ₀ θ_traj)
    (t : ℝ)
    (hdiff : ∀ β : Fin m, DifferentiableAt ℝ (fun θ' => f (X β) θ') (θ_traj t)) :
    HasDerivAt (fun s => trainingResidual f X y (θ_traj s))
      (WithLp.toLp 2 (- (m : ℝ)⁻¹ • ((empiricalNTKMatrix f X (θ_traj t)) *ᵥ (trainingResidual f X y (θ_traj t)).ofLp))) t := by
  have h_out := gradient_flow_output_vector_ode f X y hflow t hdiff
  have h_sub := h_out.sub_const y
  convert h_sub using 1
  ext s
  rfl

end NTK

end
