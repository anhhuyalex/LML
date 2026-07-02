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

* `NTK.empiricalNTK` : the empirical NTK `kₘ(x, x')` at initialization `W₀`.
* `NTK.limitingNTK` : the limiting NTK `k(x, x')`.
* `NTK.ntk_convergence` : almost sure convergence `kₘ(x,x') → k(x,x')` (SLLN).
* `NTK.reluNTK_closedForm` : closed form `k(x,x') = xᵀx'·(π−arccos(xᵀx'))/(2π)` for ReLU.

-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory Filter

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

/-- `‖x‖² = x ⊙ x`. -/
lemma norm_sq_eq_innerProduct (x : Fin d → ℝ) : ‖x‖ ^ 2 = x ⊙ x := by
  sorry

/-! ### Empirical NTK (Definition 4.5) -/

/-- **Definition 4.5** (Empirical neural tangent kernel).
Given initialization `W₀ : Fin m → Fin d → ℝ` and outer coefficients `a` with `aⱼ² = 1`,
the empirical NTK is the kernel obtained as the Frobenius inner product of gradients:
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

/-- The empirical NTK is symmetric: `kₘ(x, x') = kₘ(x', x)`. -/
lemma empiricalNTK_symm
    (σ' : ℝ → ℝ) (W₀ : Fin m → Fin d → ℝ) (x x' : Fin d → ℝ) :
    empiricalNTK σ' W₀ x x' = empiricalNTK σ' W₀ x' x := by
  simp only [empiricalNTK, innerProduct_comm x x', mul_comm (σ' _) (σ' _)]

/-- The empirical NTK is positive semidefinite: for any finite set of points
and coefficients `(αᵢ, xᵢ)`, `∑ᵢⱼ αᵢαⱼ kₘ(xᵢ, xⱼ) ≥ 0`.
This follows from being the Gram matrix of the gradient features. -/
lemma empiricalNTK_posSemidef
    (σ' : ℝ → ℝ) (W₀ : Fin m → Fin d → ℝ)
    {n : ℕ} (α : Fin n → ℝ) (pts : Fin n → Fin d → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      α i * α j * empiricalNTK σ' W₀ (pts i) (pts j) := by
  sorry

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

/-! ### Almost sure convergence of the empirical NTK (Lemma 4.3) -/

/-- **Lemma 4.3** (Almost sure convergence of the empirical NTK).
For fixed `x, x' ∈ ℝᵈ` and `W₀ ~ 𝒩(0,Iᵈ)^{⊗m}` (in `m`):
  `kₘ(x, x') →_as k(x, x')  as  m → ∞`.

**Proof:** The summands `σ'(wⱼ₀ᵀx)σ'(wⱼ₀ᵀx')` are i.i.d. with mean
`𝔼[σ'(wᵀx)σ'(wᵀx')]`; apply the strong law of large numbers. -/
theorem ntk_convergence
    (σ' : ℝ → ℝ)
    (hσ'_bounded : ∃ C : ℝ, ∀ z : ℝ, |σ' z| ≤ C)
    (x x' : Fin d → ℝ) :
    ∀ᵐ W₀_seq : ℕ → Fin m → Fin d → ℝ
      ∂(MeasureTheory.Measure.infinitePi (fun _ : ℕ => gaussianInit m d)),
      Filter.Tendsto
        (fun n => empiricalNTK σ' (W₀_seq n) x x')
        Filter.atTop
        (nhds (limitingNTK σ' x x')) := by
  sorry

/-! ### ReLU NTK closed form (Proposition 4.2) -/

/-- The ReLU derivative: `𝟏[z ≥ 0]` (a.e. equal to the actual derivative). -/
noncomputable def reluIndicator : ℝ → ℝ := fun z => if 0 ≤ z then 1 else 0

/-- The angle between two unit vectors in ℝᵈ:
  `angle x x' = arccos(xᵀx')` for `‖x‖ = ‖x'‖ = 1`. -/
noncomputable def vectorAngle (x x' : Fin d → ℝ) : ℝ :=
  Real.arccos (x ⊙ x')

/-- **Proposition 4.2** (ReLU NTK closed form, Telgarsky 2021).
For `σ' = 𝟏[· ≥ 0]` (the ReLU derivative) and `x, x' ∈ ℝᵈ` with `‖x‖ = ‖x'‖ = 1`:
  `k(x, x') = (xᵀx') · (π − arccos(xᵀx')) / (2π)`.

**Proof sketch:**
- By rotational invariance of `𝒩(0, Iᵈ)`, we may project `w` onto `span(x, x')`.
- In the 2D plane, `w` is effectively uniform on the unit circle.
- The event `{wᵀx ≥ 0} ∩ {wᵀx' ≥ 0}` is a sector of angle `π − θ` where `θ = arccos(xᵀx')`.
- The probability of this sector is `(π − θ)/(2π)`.
- Multiplying by `xᵀx'` gives the result. -/
theorem reluNTK_closedForm
    (x x' : Fin d → ℝ)
    (hx : ‖x‖ = 1)
    (hx' : ‖x'‖ = 1) :
    limitingNTK reluIndicator x x' =
      (x ⊙ x') * (Real.pi - Real.arccos (x ⊙ x')) / (2 * Real.pi) := by
  sorry

/-- The ReLU NTK is nonneg when `xᵀx' ≥ 0`. -/
lemma reluNTK_nonneg_of_nonneg_inner
    (x x' : Fin d → ℝ)
    (hx : ‖x‖ = 1) (hx' : ‖x'‖ = 1)
    (hinn : 0 ≤ x ⊙ x') :
    0 ≤ limitingNTK reluIndicator x x' := by
  rw [reluNTK_closedForm x x' hx hx']
  apply div_nonneg
  · apply mul_nonneg hinn
    linarith [Real.arccos_le_pi (x ⊙ x'), Real.pi_pos]
  · linarith [Real.pi_pos]

/-- The ReLU NTK at equal inputs: `k(x, x) = ‖x‖² / 2`. -/
lemma reluNTK_self
    (x : Fin d → ℝ) (hx : ‖x‖ = 1) :
    limitingNTK reluIndicator x x = 1 / 2 := by
  rw [reluNTK_closedForm x x hx hx]
  have h_inner : x ⊙ x = 1 := by rw [← norm_sq_eq_innerProduct, hx, one_pow]
  rw [h_inner]
  simp [Real.arccos_one]
  ring_nf
  simp [Real.pi_pos.ne']

end NTK

end
