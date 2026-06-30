/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Linearization bounds: smooth activations and ReLU

This file proves that the first-order Taylor linearization `f₀` is a good approximation
to the network `f` when the width `m` is large, corresponding to Section 4.2 of the
deep learning theory notes (Telgarsky 2021).

Two regimes are handled separately:

1. **Smooth activations** (Proposition 4.1 / `smoothLinearizationBound`):
   If `σ` is `β`-smooth (i.e. `|σ''| ≤ β`), then
   `|f(x; W) − f₀(x; V)| ≤ β/(2√m) · ‖W − V‖_F²`
   for any `x` with `‖x‖ ≤ 1`.  This does not require any probabilistic argument.

2. **ReLU activation** (Lemma 4.1 / `reluLinearizationBound`):
   Because the ReLU is not smooth, we instead exploit Gaussian initialization `W₀`.
   A concentration lemma (`reluSignConcentration`) bounds the number of neurons
   whose sign changes under a bounded perturbation, and Cauchy-Schwarz then gives
   `|f(x; W) − f₀(x; W)| ≤ (2B^{4/3} + B·ln(1/δ)^{1/4}) / m^{1/6}`
   with probability at least `1 − δ`, uniformly over `‖W − W₀‖_F ≤ B`.

## Main results

* `NTK.BetaSmooth` : predicate for `β`-smooth activations.
* `NTK.smoothLinearizationBound` : Proposition 4.1 (smooth case).
* `NTK.reluSignConcentration` : Lemma 4.2 (Gaussian sign-concentration).
* `NTK.reluLinearizationBound` : Lemma 4.1 (ReLU linearization bound).

-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory NNReal Filter

namespace NTK

variable {d m : ℕ}

/-! ### β-smooth activations (Definition 4.4) -/

/-- **Definition 4.4**.
An activation `σ : ℝ → ℝ` is *`β`-smooth* if `σ` is twice differentiable everywhere
and `|σ''(z)| ≤ β` for all `z ∈ ℝ`. -/
structure BetaSmooth (σ : ℝ → ℝ) (β : ℝ) : Prop where
  /-- `σ` is differentiable everywhere. -/
  differentiable : Differentiable ℝ σ
  /-- The derivative `σ'` is also differentiable everywhere. -/
  differentiable' : Differentiable ℝ (deriv σ)
  /-- Second derivative is bounded: `|σ''(z)| ≤ β`. -/
  hessian_bound   : ∀ z : ℝ, |deriv (deriv σ) z| ≤ β

lemma BetaSmooth.β_nonneg {σ : ℝ → ℝ} {β : ℝ} (h : BetaSmooth σ β) : 0 ≤ β := by
  have := h.hessian_bound 0
  linarith [abs_nonneg (deriv (deriv σ) 0)]

/-- Taylor's theorem for `β`-smooth activations:
  `|σ(r) − σ(s) − σ'(s)·(r − s)| ≤ β(r − s)²/2`. -/
lemma BetaSmooth.taylor_bound
    {σ : ℝ → ℝ} {β : ℝ} (hσ : BetaSmooth σ β) (r s : ℝ) :
    |σ r - σ s - deriv σ s * (r - s)| ≤ β * (r - s) ^ 2 / 2 := by
  sorry

/-! ### Smooth linearization bound (Proposition 4.1) -/

/-- **Proposition 4.1** (Telgarsky 2021).
For a `β`-smooth activation `σ` and outer coefficients `|aⱼ| ≤ 1`,
and for any `x` with `‖x‖ ≤ 1` and any weight matrices `W, V`:
  `|f(x; W) − f₀(x; V)| ≤ β/(2√m) · ‖W − V‖_F²`.

**Proof sketch:** Apply the Taylor bound to each neuron and sum using Cauchy-Schwarz.
No probabilistic argument is needed; the bound holds for any `W, V ∈ ℝ^{m×d}`. -/
theorem smoothLinearizationBound
    {σ : ℝ → ℝ} {β : ℝ}
    (hσ : BetaSmooth σ β)
    (net : ShallowNetwork σ d m)
    (x : Fin d → ℝ)
    (hx : ‖x‖ ≤ 1)
    (W V : Fin m → Fin d → ℝ) :
    |net.eval x W - linearization (σ := σ) (σ' := deriv σ) net.outerCoeffs x V V|
    ≤ β / (2 * Real.sqrt m) * frobeniusNorm (fun i j => W i j - V i j) ^ 2 := by
  sorry

/-! ### Sign concentration under Gaussian initialization (Lemma 4.2) -/

/-- The set of neuron indices whose inner product with `x` is small in absolute value.
  `signAmbiguous τ x W₀ = {j : |wⱼ₀ᵀx| ≤ τ‖x‖}`. -/
def signAmbiguous (τ : ℝ) (x : Fin d → ℝ) (W₀ : Fin m → Fin d → ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun j =>
    |∑ k : Fin d, W₀ j k * x k| ≤ τ * ‖x‖)

/-- **Lemma 4.2** (Telgarsky 2021 / Hoeffding concentration).
Let `x ∈ ℝᵈ` with `‖x‖ > 0` and let `W₀ ~ 𝒩(0, Iᵈ)^{⊗m}`.
For any `τ > 0` and `δ ∈ (0,1)`, with probability at least `1 − δ` over `W₀`,
  `|{j : |wⱼ₀ᵀx| ≤ τ‖x�|}| ≤ mτ + √(m/2 · ln(1/δ))`.

**Proof:** Each indicator is Bernoulli with mean `≤ τ` (Gaussian density bound);
apply Hoeffding's inequality to the i.i.d. sum. -/
theorem reluSignConcentration
    (x : Fin d → ℝ) (hx : 0 < ‖x‖)
    (τ : ℝ) (hτ : 0 < τ)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᵐ W₀ ∂(gaussianInit m d),
      (signAmbiguous τ x W₀).card ≤
        (m : ℝ) * τ + Real.sqrt ((m : ℝ) / 2 * Real.log (1 / δ)) := by
  sorry

/-! ### Bad index sets for the ReLU proof -/

/-- Neurons with a large perturbation from initialization:
  `largePerturb B W W₀ = {j : ‖wⱼ − wⱼ₀‖ ≥ B}`. -/
def largePerturb (B : ℝ) (W W₀ : Fin m → Fin d → ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun j =>
    B ≤ ‖fun k => W j k - W₀ j k‖)

/-- The union of the sign-ambiguous and large-perturbation index sets. -/
def badSet (τ B : ℝ) (x : Fin d → ℝ) (W W₀ : Fin m → Fin d → ℝ) : Finset (Fin m) :=
  signAmbiguous τ x W₀ ∪ largePerturb B W W₀

/-- For neurons outside `badSet`, the sign of `wⱼᵀx` agrees with `wⱼ₀ᵀx`.
This is the key geometric observation: if `|wⱼ₀ᵀx| > τ‖x‖` and `‖wⱼ − wⱼ₀‖ < τ`,
then the sign cannot have flipped. -/
lemma sign_preserved_outside_badSet
    (τ B : ℝ) (hτ : 0 < τ) (hB : 0 < B)
    (x : Fin d → ℝ)
    (W W₀ : Fin m → Fin d → ℝ)
    (hW : frobeniusNorm (fun i k => W i k - W₀ i k) ≤ B)
    (j : Fin m) (hj : j ∉ badSet τ B x W W₀) :
    (0 ≤ ∑ k : Fin d, W j k * x k) ↔
    (0 ≤ ∑ k : Fin d, W₀ j k * x k) := by
  sorry

/-! ### ReLU linearization bound (Lemma 4.1) -/

/-- The ReLU activation. Bundled here for convenience. -/
noncomputable def relu : ℝ → ℝ := fun z => max z 0

/-- The subgradient / derivative of ReLU (a.e. equal to the indicator): `σ'(z) = 𝟏[z ≥ 0]`. -/
noncomputable def reluDeriv : ℝ → ℝ := fun z => if 0 ≤ z then 1 else 0

/-- Scaled shallow network with ReLU activation. -/
abbrev ReLUNetwork (d m : ℕ) := ShallowNetwork relu d m

/-- **Lemma 4.1** (Telgarsky 2021, main ReLU linearization bound).
Let `net` be a ReLU network, `W₀ ~ 𝒩(0, Iᵈ)^{⊗m}`, `B ≥ 0`, and `‖x‖ ≤ 1`.
With probability at least `1 − δ` over `W₀`, for every `W` with `‖W − W₀‖_F ≤ B`:
  `|f(x; W) − f₀(x; W)| ≤ (2B^{4/3} + B·(ln(1/δ))^{1/4}) / m^{1/6}`.

**Proof sketch:**
1. Choose the balancing radius `r = B^{2/3}/m^{1/3}`.
2. Define `S = S₁ ∪ S₂` where `S₁ = signAmbiguous r x W₀` and `S₂ = largePerturb r W W₀`.
3. By `reluSignConcentration`, `|S₁| ≤ rm + √(m ln(1/δ)/2)` w.p. ≥ 1−δ.
4. By Frobenius bound, `|S₂| ≤ B²/r²`.
5. The choice of `r` gives `|S| ≤ m^{2/3}(2B^{2/3} + √(ln(1/δ)))`.
6. Outside `S`, signs are preserved, so the linearization error sums only over `j ∈ S`;
   Cauchy-Schwarz gives the stated bound. -/
theorem reluLinearizationBound
    (net : ReLUNetwork d m)
    (x : Fin d → ℝ) (hx : ‖x‖ ≤ 1)
    (B : ℝ) (hB : 0 ≤ B)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᵐ W₀ ∂(gaussianInit m d),
      ∀ W : Fin m → Fin d → ℝ,
        frobeniusNorm (fun i k => W i k - W₀ i k) ≤ B →
          |net.eval x W -
           linearization (σ := relu) (σ' := reluDeriv) net.outerCoeffs x W₀ W|
          ≤ (2 * B ^ (4 / 3 : ℝ) + B * Real.log (1 / δ) ^ (1 / 4 : ℝ)) /
            (m : ℝ) ^ (1 / 6 : ℝ) := by
  sorry

/-- **Corollary** (second part of Lemma 4.1): second-order Taylor error for ReLU.
For any additional `V` with `‖V − W₀‖_F ≤ B`:
  `|f(x; V) − (f(x; W) + ⟨∇_W f(x; W), V − W⟩_F)| ≤ (6B^{4/3} + 2B·(ln(1/δ))^{1/4}) / m^{1/6}`. -/
theorem reluLinearizationBound_secondOrder
    (net : ReLUNetwork d m)
    (x : Fin d → ℝ) (hx : ‖x‖ ≤ 1)
    (B : ℝ) (hB : 0 ≤ B)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∀ᵐ W₀ ∂(gaussianInit m d),
      ∀ W V : Fin m → Fin d → ℝ,
        frobeniusNorm (fun i k => W i k - W₀ i k) ≤ B →
        frobeniusNorm (fun i k => V i k - W₀ i k) ≤ B →
          |net.eval x V -
           (net.eval x W +
            linearization (σ := relu) (σ' := reluDeriv) net.outerCoeffs x W V -
            net.eval x W)|
          ≤ (6 * B ^ (4 / 3 : ℝ) + 2 * B * Real.log (1 / δ) ^ (1 / 4 : ℝ)) /
            (m : ℝ) ^ (1 / 6 : ℝ) := by
  sorry

end NTK

end
