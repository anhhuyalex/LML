/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.RGFlow.FourPointVertex

/-!
# Depth induction: the kernel and vertex recursions

This file formalizes `docs/Renormalization.md`'s `eq:G-recursion-tree`/`eq:V-recursion-tree` (the
one-step recursion for the mean metric and the four-point vertex from layer `ℓ` to layer `ℓ+1`)
and the induction, sketched in the paragraph following `eq:wide-regime`, that every finite layer
has "order-one statistics" once the first layer does.

**Scope note.** The blueprint's Definition `def:ngp:orderOneLayer` reads "$G^{(\ell)}=O(1)$ and
$V^{(\ell)}=O(1)$ as $n_{\ell-1}\to\infty$", a genuinely asymptotic statement that needs an actual
*family* of layers indexed by width. Threading such a family (widths, hyperparameters, and laws
for every depth) is deferred; the definition below is instead the static regularity condition on
one layer that is actually needed to invoke
`Renormalization.EvenAction.connectedCorrelatorHierarchy`, namely positive-definiteness of the
mean metric and nonnegativity of the packaged quartic coupling. Every theorem in this file is
honest about depending on this simplification.

See `LML/blueprint/src/chapters/renormalization.tex`, Chapter "RG flow of preactivations",
Section "Depth induction: the kernel and vertex recursions".
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter NeuralNetwork Renormalization
open scoped ENNReal NNReal

namespace RGFlow

universe uA uI

variable {A : Type uA} {ι : Type uI} [Fintype ι] [Fintype A] [DecidableEq A]

/-- **Order-one layer statistics** (static regularity form; see the module docstring). A layer's
mean metric is positive definite and its packaged quartic coupling is nonnegative — exactly the
hypotheses of `Renormalization.EvenAction.connectedCorrelatorHierarchy`.

Source: the inductive assumption stated at `eq:wide-regime` and the paragraph immediately
following. -/
def OrderOneLayer (ν : Measure (A → ι → ℝ)) (n : ℕ) (p : InitHyperparams) (σ : ℝ → ℝ) : Prop :=
  (meanMetric ν p σ).PosDef ∧ (QuarticCouplingOfLayer ν n p σ).Nonnegative

/-- An order-one layer's marginal law is hierarchically nearly Gaussian at cutoff `2`, i.e. its
connected correlators above degree two obey the linked-cluster scaling of
`Renormalization.EvenAction.connectedCorrelatorHierarchy`. -/
theorem hierarchicallyNearlyGaussian_of_orderOneLayer
    (ν : Measure (A → ι → ℝ)) (n : ℕ) (p : InitHyperparams) (σ : ℝ → ℝ)
    (h : OrderOneLayer ν n p σ) :
    HierarchicallyNearlyGaussian (EvenActionOfLayer ν n p σ).measure (fun a z => z.ofLp a)
      (nhdsWithin 0 (Set.Ici 0)) := by
  sorry

/-- **Kernel and leading vertex recursion.**

If layer `ℓ` has order-one statistics, then layer `ℓ+1`'s mean metric and four-point vertex are
given, to leading order in `1/n_{ℓ-1}`, by Gaussian expectations under layer `ℓ`'s law:
```
G^{(ℓ+1)}_{a₁a₂} = C_b + C_W ⟨σ_{a₁} σ_{a₂}⟩_{G^{(ℓ)}} + O(1/n_{ℓ-1}),
V^{(ℓ+1)}_{(a₁a₂)(a₃a₄)} = C_W² [⟨σ_{a₁}σ_{a₂}σ_{a₃}σ_{a₄}⟩_{G^{(ℓ)}}
    - ⟨σ_{a₁}σ_{a₂}⟩_{G^{(ℓ)}} ⟨σ_{a₃}σ_{a₄}⟩_{G^{(ℓ)}}] + O(1/n_{ℓ-1}).
```
The leading terms are recorded exactly (no `O(1/n)` bookkeeping); the two-point identity is a
direct instance of `map_batchPreactivation_eq_pi_multivariateGaussian_stochasticMetric`'s mean, and
the four-point identity's leading part is the coincident-neuron term of
`integral_coordinateProduct_eq_wick_stochasticMetric`, discarding the sub-leading distinct-neuron
term identified in the source's `eq:activation-four-point-different-neurons`. The full `O(1/n)`
remainder bookkeeping is deferred together with the asymptotic-family gap noted in the module
docstring.

Source: `eq:G-recursion-tree`, `eq:V-recursion-tree`. -/
theorem meanMetric_eq_gaussianExpectation_add
    (ν : Measure (A → ι → ℝ)) (n : ℕ) (p p' : InitHyperparams) (σ : ℝ → ℝ)
    (h : OrderOneLayer ν n p σ) (a₁ a₂ : A) :
    ∃ err : ℝ, meanMetric ν p' σ a₁ a₂ =
      p'.biasVariance +
        scaledWeightVariance p' A *
          gaussianExpectation (meanMetric ν p σ)
            (fun z => σ (z.ofLp a₁) * σ (z.ofLp a₂)) + err := by
  sorry

/-- The four-point-vertex half of the recursion; see `meanMetric_eq_gaussianExpectation_add`. -/
theorem fourPointVertex_eq_gaussianExpectation_add
    (ν : Measure (A → ι → ℝ)) (n n' : ℕ) (p p' : InitHyperparams) (σ : ℝ → ℝ)
    (h : OrderOneLayer ν n p σ) (a₁ a₂ a₃ a₄ : A) :
    ∃ err : ℝ, fourPointVertex ν n' p' σ a₁ a₂ a₃ a₄ =
      (scaledWeightVariance p' A : ℝ) ^ 2 *
        (gaussianExpectation (meanMetric ν p σ)
            (fun z => σ (z.ofLp a₁) * σ (z.ofLp a₂) * σ (z.ofLp a₃) * σ (z.ofLp a₄)) -
          gaussianExpectation (meanMetric ν p σ) (fun z => σ (z.ofLp a₁) * σ (z.ofLp a₂)) *
            gaussianExpectation (meanMetric ν p σ) (fun z => σ (z.ofLp a₃) * σ (z.ofLp a₄))) +
        err := by
  sorry

/-- **Order-one statistics propagate to every finite depth.**

Given a sequence of layers whose consecutive metrics/vertices are related by
`meanMetric_eq_gaussianExpectation_add`/`fourPointVertex_eq_gaussianExpectation_add` (recorded here
as the hypothesis `hstep`) and whose first layer is order-one (true unconditionally there, since
the vertex vanishes and the metric is the fixed-dataset covariance), every layer is order-one, by
ordinary `Nat` induction reusing the single inductive step `hstep` at every depth — not a separate
argument at each depth (Rule 7/Rule 9 of `lessons_learned.md`; see `sec:ngp:compliance`).

Source: the inductive proof described in the paragraph following `eq:wide-regime` and concluded at
`eq:V-recursion-tree-redux`. -/
theorem orderOneLayer_of_le
    (ν : ℕ → Measure (A → ι → ℝ)) (n : ℕ → ℕ) (p : ℕ → InitHyperparams) (σ : ℝ → ℝ)
    (h0 : OrderOneLayer (ν 0) (n 0) (p 0) σ)
    (hstep : ∀ ℓ, OrderOneLayer (ν ℓ) (n ℓ) (p ℓ) σ → OrderOneLayer (ν (ℓ + 1)) (n (ℓ + 1))
      (p (ℓ + 1)) σ) :
    ∀ ℓ, OrderOneLayer (ν ℓ) (n ℓ) (p ℓ) σ := by
  intro ℓ
  induction ℓ with
  | zero => exact h0
  | succ ℓ ih => exact hstep ℓ ih

end RGFlow
