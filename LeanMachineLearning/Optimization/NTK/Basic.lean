/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Approximation.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Scaled shallow networks and Taylor linearization near initialization

This file defines the core objects for Chapter 4 of the deep learning theory notes
(Telgarsky 2021), which studies neural networks near their random initialization.

The central objects are:
- A **scaled shallow network** `f(x; W) = (1/√m) ∑ⱼ aⱼ σ(wⱼᵀx)` with fixed outer layer
  `a` and variable inner weight matrix `W`.
- The **standard Gaussian initialization**: rows of `W₀` drawn i.i.d. from `𝒩(0, Iᵈ)`.
- The **first-order Taylor linearization** `f₀(x; W) = f(x; W₀) + ⟨∇_W f(x; W₀), W − W₀⟩_F`.

The key insight is that `f₀` is affine in `W` while remaining nonlinear in `x`,
making it much easier to analyze than `f` itself.

## Main definitions

* `NTK.ShallowNetwork σ d m` : a scaled shallow network with activation `σ`,
  input dimension `d`, and width `m`.
* `NTK.ShallowNetwork.eval` : evaluate `f(x; W) = (1/√m) ∑ⱼ aⱼ σ(wⱼᵀx)`.
* `NTK.linearization` : the first-order Taylor linearization `f₀(x; W)`.

-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory

namespace NTK

variable {d m : ℕ}

/-! ### Scaled shallow network (Definition 4.1 / Section 4.1) -/

/-- **Definition 4.1** (Telgarsky 2021, eq. (2)).
A scaled shallow network with activation `σ`, input dimension `d`, and width `m`.

The network computes
  `f(x; W) = (1/√m) ∑ⱼ aⱼ σ(wⱼᵀx)`
where `W : Fin m → Fin d → ℝ` has rows `wⱼ` and `a : Fin m → ℝ` is a fixed
outer layer satisfying `|aⱼ| ≤ 1`.

The `1/√m` normalization ensures the associated NTK has a finite limit as `m → ∞`. -/
structure ShallowNetwork (σ : ℝ → ℝ) (d m : ℕ) where
  /-- The fixed outer-layer coefficients satisfying `|outerCoeffs j| ≤ 1`. -/
  outerCoeffs : Fin m → ℝ
  /-- Outer coefficients are bounded in absolute value by 1. -/
  outerCoeffs_bound : ∀ j : Fin m, |outerCoeffs j| ≤ 1

/-- Evaluate a scaled shallow network at input `x` and weight matrix `W`:
  `f(x; W) = (1/√m) ∑ⱼ aⱼ σ(wⱼᵀx)`.

Here `W : Fin m → Fin d → ℝ` represents the weight matrix with rows `W i : Fin d → ℝ`,
and the inner product `wⱼᵀx = ∑ₖ W j k * x k`. -/
noncomputable def ShallowNetwork.eval
    {σ : ℝ → ℝ} {d m : ℕ}
    (net : ShallowNetwork σ d m)
    (x : Fin d → ℝ)
    (W : Fin m → Fin d → ℝ) : ℝ :=
  (m : ℝ)⁻¹.sqrt * ∑ j : Fin m, net.outerCoeffs j * σ (∑ k : Fin d, W j k * x k)

/-! ### The weight gradient `∇_W f(x; W₀)`

The gradient of `f(x; W)` with respect to `W`, evaluated at `W₀`, is the matrix in `ℝ^{m×d}` with
entry `(j, k)` equal to `aⱼ · σ'(wⱼ₀ᵀx) · xₖ / √m`, written out explicitly as
`(m : ℝ)⁻¹.sqrt * outerCoeffs j * σ' (∑ l, W₀ j l * x l) * x k`. For the ReLU, `σ'(z) = 1[z ≥ 0]`
(a.e.), so the gradient is sparse at signs. -/

/-! ### Gaussian initialization (Definition 4.2)

**Definition 4.2** (Standard Gaussian initialization). The standard Gaussian initialization of
a weight matrix `W₀ : Fin m → Fin d → ℝ` is the product measure under which the rows
`W₀ 0, …, W₀ (m-1)` are i.i.d. `𝒩(0, Iᵈ)`, each row itself having i.i.d. `𝒩(0, 1)` coordinates. It
is written out explicitly throughout as
`Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin d => gaussianReal 0 1`. -/

/-! ### Taylor linearization (Definition 4.3) -/

/-- **Definition 4.3** (First-order Taylor linearization).
For a scaled shallow network with differentiable activation `σ` and a fixed
initialization `W₀ : Fin m → Fin d → ℝ`, the first-order Taylor linearization
of `f(x; ·)` at `W₀` is:
  `f₀(x; W) = f(x; W₀) + ⟨∇_W f(x; W₀), W − W₀⟩_F`
  `         = (1/√m) ∑ⱼ aⱼ [σ(wⱼ₀ᵀx) + σ'(wⱼ₀ᵀx)(wⱼ − wⱼ₀)ᵀx]`.

This is affine in `W` and nonlinear in `x` (when `σ` is nonlinear). -/
noncomputable def linearization
    {σ σ' : ℝ → ℝ} -- σ and its derivative
    {d m : ℕ}
    (outerCoeffs : Fin m → ℝ)
    (x : Fin d → ℝ)
    (W₀ W : Fin m → Fin d → ℝ) : ℝ :=
  let eval₀ : ℝ :=
    (m : ℝ)⁻¹.sqrt *
    ∑ j : Fin m, outerCoeffs j * σ (∑ k : Fin d, W₀ j k * x k)
  let grad_inner : ℝ :=
    (m : ℝ)⁻¹.sqrt *
    ∑ j : Fin m, outerCoeffs j *
      σ' (∑ k : Fin d, W₀ j k * x k) *
      ∑ k : Fin d, (W j k - W₀ j k) * x k
  eval₀ + grad_inner

/-- For the ReLU activation `σ(z) = max(0, z)`, the linearization simplifies to
  `f₀(x; W) = (1/√m) ∑ⱼ aⱼ σ'(wⱼ₀ᵀx) wⱼᵀx = ⟨∇_W f(x; W₀), W⟩_F`
because `σ(z) = z · σ'(z)` a.e., which cancels the constant term at `W₀`. -/
lemma linearization_relu_eq
    {d m : ℕ}
    (outerCoeffs : Fin m → ℝ)
    (x : Fin d → ℝ)
    (W₀ W : Fin m → Fin d → ℝ)
    (σ' : ℝ → ℝ) :
    linearization (σ := fun z => z * σ' z) (σ' := σ') outerCoeffs x W₀ W =
    (m : ℝ)⁻¹.sqrt *
    ∑ j : Fin m, outerCoeffs j * σ' (∑ k : Fin d, W₀ j k * x k) *
      ∑ k : Fin d, W j k * x k := by
  simp only [linearization]
  have h_inner_sum (j : Fin m) :
      ∑ k : Fin d, (W j k - W₀ j k) * x k =
        ∑ k : Fin d, W j k * x k - ∑ k : Fin d, W₀ j k * x k := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [h_inner_sum j]
  ring

end NTK

end
