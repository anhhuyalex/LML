/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.RGFlow.DepthInduction

/-!
# Subleading corrections: the kernel and the NLO metric

This file formalizes `docs/Renormalization.md`'s `eq:definition-of-kernel-first`/`eq:K-recursion`
(the infinite-width kernel, defined as the width-independent leading term of the mean metric
recursion) and `eq:NLO-metric-recursion` (the next-to-leading-order correction). This is, by a
wide margin, the most algebraically intricate derivation in the chapter (book lines 3130-3211,
a five-equation chain of substitutions) and is the chapter's lowest-priority milestone
(Phase NGP6): every declaration below is either a direct recursive definition or a `sorry`'d
theorem with its informal proof and source cited in the docstring.

See `LML/blueprint/src/chapters/renormalization.tex`, Chapter "RG flow of preactivations",
Section "Subleading corrections: the kernel and the NLO metric".
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter NeuralNetwork Renormalization
open scoped ENNReal NNReal

namespace RGFlow

universe uA

variable {A : Type uA} [Fintype A] [DecidableEq A]

/-- **The kernel.** The width-independent ("infinite-width") recursion for the mean metric,
obtained from `meanMetric_eq_gaussianExpectation_add` by dropping its `O(1/n_{ℓ-1})` remainder:
`K 0` is the first layer's exact (fixed-dataset) metric, and each subsequent layer's kernel is the
Gaussian expectation of the activation product under the previous layer's kernel.

Source: `eq:definition-of-kernel-first` and `eq:K-recursion`. -/
def kernel (K0 : Matrix A A ℝ) (p : ℕ → InitHyperparams) (σ : ℝ → ℝ) : ℕ → Matrix A A ℝ
  | 0 => K0
  | ℓ + 1 => fun a₁ a₂ =>
      (p (ℓ + 1)).biasVariance +
        scaledWeightVariance (p (ℓ + 1)) A *
          gaussianExpectation (kernel K0 p σ ℓ) (fun z => σ (z.ofLp a₁) * σ (z.ofLp a₂))

omit [DecidableEq A] in
@[simp] theorem kernel_zero (K0 : Matrix A A ℝ) (p : ℕ → InitHyperparams) (σ : ℝ → ℝ) :
    kernel K0 p σ 0 = K0 := rfl

omit [DecidableEq A] in
theorem kernel_succ (K0 : Matrix A A ℝ) (p : ℕ → InitHyperparams) (σ : ℝ → ℝ) (ℓ : ℕ) (a₁ a₂ : A) :
    kernel K0 p σ (ℓ + 1) a₁ a₂ =
      (p (ℓ + 1)).biasVariance +
        scaledWeightVariance (p (ℓ + 1)) A *
          gaussianExpectation (kernel K0 p σ ℓ) (fun z => σ (z.ofLp a₁) * σ (z.ofLp a₂)) := rfl

/-- **The NLO metric.** A layer-`ℓ` correction matrix `Σ ℓ` such that the mean metric equals the
kernel plus `Σ ℓ / n_{ℓ-1}` up to `O(1/n_{ℓ-1}²)`; recorded here as an unconstrained sequence of
matrices, since pinning down its value is exactly the content of `nloMetric_succ_eq` below.

Source: `eq:self-energy-decomposition`. -/
def NloMetric (A : Type uA) : Type uA := ℕ → Matrix A A ℝ

/-- **NLO metric recursion.**

Writing `G^{(ℓ)} = K^{(ℓ)} + Σ^{(ℓ)}/n_{ℓ-1} + O(1/n_{ℓ-1}²)`, the NLO metric `Σ^{(ℓ)}` satisfies
the recursion displayed at `eq:NLO-metric-recursion`, an explicit bilinear expression in
`Σ^{(ℓ)}`, the four-point vertex `V^{(ℓ)}`, and Gaussian brackets under the kernel `K^{(ℓ)}`.

**This theorem is deferred and recorded with `sorry`.** Informal proof: substitute the
`1/n_{ℓ-1}`-expansions `eq:self-energy-decomposition`/`eq:vertex-decomposition` into the exact
two-point matching identity `eq:second-moment-from-action-reprinted` (an instance of
`Renormalization.QuarticCoupling.twoPoint_isBigO` at one further order), invert to isolate
`g^{(ℓ)} - K^{(ℓ)}` (`eq:inverse-difference`), substitute the quartic-coupling correction into the
leading two-activation Gaussian bracket via a first-order tilted-measure expansion
(`eq:subleading-sigma-sigma`, an instance of
`Renormalization.hasDerivWithinAt_integral_deform_zero`), and collect terms order by order in
`1/n_{ℓ-1}`. Source: Yaida, "Non-Gaussian processes and neural networks at finite widths"
<https://arxiv.org/abs/1910.00019>, and book lines 3147-3211 for the full manual computation. -/
theorem nloMetric_succ_eq
    (K0 : Matrix A A ℝ) (p : ℕ → InitHyperparams) (σ : ℝ → ℝ) (nlo : NloMetric A)
    (V : ℕ → A → A → A → A → ℝ) (nPrev : ℕ) (ℓ : ℕ) (a₁ a₂ : A) :
    nlo (ℓ + 1) a₁ a₂ =
      scaledWeightVariance (p (ℓ + 1)) A / (nPrev : ℝ) *
        ∑ β₁, ∑ β₂, ∑ β₃, ∑ β₄,
          (((kernel K0 p σ ℓ)⁻¹ β₁ β₃ * (kernel K0 p σ ℓ)⁻¹ β₂ β₄ * nlo ℓ β₃ β₄ / 2 *
                covarianceWith (multivariateGaussian 0 (kernel K0 p σ ℓ))
                  (fun z => z.ofLp a₁ * z.ofLp a₂)
                  (fun z => z.ofLp β₁ * z.ofLp β₂ - kernel K0 p σ ℓ β₁ β₂))
            + (V ℓ β₁ β₂ β₃ β₄ / 8 *
                covarianceWith (multivariateGaussian 0 (kernel K0 p σ ℓ))
                  (fun z => z.ofLp a₁ * z.ofLp a₂)
                  (fun z => (z.ofLp β₁ * z.ofLp β₂ - kernel K0 p σ ℓ β₁ β₂) *
                    (z.ofLp β₃ * z.ofLp β₄ - kernel K0 p σ ℓ β₃ β₄)))
            + (V ℓ β₁ β₃ β₂ β₄ * kernel K0 p σ ℓ β₃ β₄ / 4 *
                covarianceWith (multivariateGaussian 0 (kernel K0 p σ ℓ))
                  (fun z => z.ofLp a₁ * z.ofLp a₂)
                  (fun z => -2 * (z.ofLp β₁ * z.ofLp β₂) + kernel K0 p σ ℓ β₁ β₂))) := by
  sorry

end RGFlow
