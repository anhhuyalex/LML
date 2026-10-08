/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Approximation.Basic

/-!
# Scaled shallow networks and Taylor linearization near initialization

This file defines the core objects for Chapter 4 of the deep learning theory notes
(Telgarsky 2021), which studies neural networks near their random initialization.

The central objects are:
- The **scaled shallow network** `f(x; W) = (1/√m) ∑ⱼ aⱼ σ(wⱼᵀx)` with fixed outer layer
  `a` (`|aⱼ| ≤ 1` where the bound is needed) and variable inner weight matrix `W`.
- The **standard Gaussian initialization**: rows of `W₀` drawn i.i.d. from `𝒩(0, Iᵈ)`.
- The **first-order Taylor linearization** `f₀(x; W) = f(x; W₀) + ⟨∇_W f(x; W₀), W − W₀⟩_F`.

The key insight is that `f₀` is affine in `W` while remaining nonlinear in `x`,
making it much easier to analyze than `f` itself.

## Main definitions

* `NTK.evalSingle σ W a x` : evaluate `f(x; W, a) = (1/√m) ∑ⱼ aⱼ σ(wⱼᵀx)`.
* `NTK.linearization` : the first-order Taylor linearization `f₀(x; W)`.

-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory

namespace NTK

variable {d m : ℕ}

/-! ### Scaled shallow network (Definition 4.1 / Section 4.1) -/

/-- **Definition 4.1** (Telgarsky 2021, eq. (2)). Single-output evaluation of a scaled shallow
network with activation `φ`, input weights `W : Fin n → Fin d → ℝ` (rows `Wᵢ`) and readout weights
`a : Fin n → ℝ`:
  `f(x; W, a) = (1/√n) ∑ᵢ aᵢ φ(Wᵢ ⬝ᵥ x)`.

Chapter 4 fixes the outer layer with `|aᵢ| ≤ 1` and varies only `W`; this is stated as the
hypothesis `∀ i, |a i| ≤ 1` where it is needed. The `1/√n` normalization ensures the associated NTK
has a finite limit as `n → ∞`. -/
noncomputable def evalSingle {d n : ℕ}
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (x : Fin d → ℝ) : ℝ :=
  (n : ℝ)⁻¹.sqrt * ∑ i : Fin n, a i * φ (W i ⬝ᵥ x)

/-- The normalized-sum formula for a scalar network evaluation. This is the public
equation lemma for `evalSingle`, so proofs need not unfold its implementation. -/
lemma evalSingle_eq_normalized_sum {d n : ℕ}
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (x : Fin d → ℝ) :
    evalSingle φ W a x = (n : ℝ)⁻¹.sqrt * ∑ i : Fin n, a i * φ (W i ⬝ᵥ x) := rfl

/-! ### The weight gradient `∇_W f(x; W₀)`

The gradient of `f(x; W)` with respect to `W`, evaluated at `W₀`, is the matrix in `ℝ^{m×d}` with
entry `(j, k)` equal to `aⱼ · σ'(wⱼ₀ᵀx) · xₖ / √m`, written out explicitly as
`(m : ℝ)⁻¹.sqrt * a j * σ' (∑ l, W₀ j l * x l) * x k`. For the ReLU, `σ'(z) = 1[z ≥ 0]`
(a.e.), so the gradient is sparse at signs. -/

/-! ### Gaussian initialization (Definition 4.2)

**Definition 4.2** (Standard Gaussian initialization). The standard Gaussian initialization of
a weight matrix `W₀ : Fin m → Fin d → ℝ` is the product measure under which the rows
`W₀ 0, …, W₀ (m-1)` are i.i.d. `𝒩(0, Iᵈ)`, each row itself having i.i.d. `𝒩(0, 1)` coordinates. It
is written out explicitly throughout as
`Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin d => gaussianReal 0 1`. -/

/-! ### Taylor linearization (Definition 4.3) -/

/-- **Definition 4.3** (First-order Taylor linearization).
For a scaled shallow network with outer layer `a`, an activation `σ` with (sub)derivative `σ'`, and
a fixed initialization `W₀ : Fin m → Fin d → ℝ`, the first-order Taylor linearization
of `f(x; ·)` at `W₀` is:
  `f₀(x; W) = f(x; W₀) + ⟨∇_W f(x; W₀), W − W₀⟩_F`
  `         = (1/√m) ∑ⱼ aⱼ [σ(wⱼ₀ᵀx) + σ'(wⱼ₀ᵀx)(wⱼ − wⱼ₀)ᵀx]`,
with `f = evalSingle σ · a`. The derivative `σ'` is a parameter so that the ReLU can use its
a.e.-derivative `1[z ≥ 0]` at the kink. For differentiable `σ` and `σ' = deriv σ` this is the
Taylor model `f(x; θ₀) + ⟪∇f(x; θ₀), θ - θ₀⟫` of the packed network (`linearization_eq_taylor`).

This is affine in `W` and nonlinear in `x` (when `σ` is nonlinear). -/
noncomputable def linearization
    {σ σ' : ℝ → ℝ} -- σ and its derivative
    {d m : ℕ}
    (a : Fin m → ℝ)
    (x : Fin d → ℝ)
    (W₀ W : Fin m → Fin d → ℝ) : ℝ :=
  evalSingle σ W₀ a x +
    (m : ℝ)⁻¹.sqrt * ∑ j : Fin m, a j * σ' (W₀ j ⬝ᵥ x) * ((W j - W₀ j) ⬝ᵥ x)

/-- For the ReLU activation `σ(z) = max(0, z)`, the linearization simplifies to
  `f₀(x; W) = (1/√m) ∑ⱼ aⱼ σ'(wⱼ₀ᵀx) wⱼᵀx = ⟨∇_W f(x; W₀), W⟩_F`
because `σ(z) = z · σ'(z)` a.e., which cancels the constant term at `W₀`. -/
lemma linearization_relu_eq
    {d m : ℕ}
    (a : Fin m → ℝ)
    (x : Fin d → ℝ)
    (W₀ W : Fin m → Fin d → ℝ)
    (σ' : ℝ → ℝ) :
    linearization (σ := fun z => z * σ' z) (σ' := σ') a x W₀ W =
    (m : ℝ)⁻¹.sqrt * ∑ j : Fin m, a j * σ' (W₀ j ⬝ᵥ x) * (W j ⬝ᵥ x) := by
  simp only [linearization, evalSingle, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sub_dotProduct]
  ring

end NTK

end
