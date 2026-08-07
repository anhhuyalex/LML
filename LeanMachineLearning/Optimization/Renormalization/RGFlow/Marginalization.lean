/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.RGFlow.DepthInduction

/-!
# Marginalization rules

This file formalizes `docs/Renormalization.md`'s `eq:marginalization-rule`/`eq:sum-rule-mlp`: the
statistics of finitely many samples and neurons of a layer depend on the rest of the layer only
through a restriction, not a re-derivation. The metric-level half of this fact is definitional
(`NeuralNetwork.layerCovariance`'s defining sum ranges over the *neuron* index `ι`, not the sample
index `A`, so it is already well-defined on any sub-collection of samples without restriction); the
measure-level half — that the *law* of a subsample is the marginal of the full law, not merely a
formula that happens to agree — is the genuinely new content, and is recorded with `sorry`.

See `LML/blueprint/src/chapters/renormalization.tex`, Chapter "RG flow of preactivations",
Section "Marginalization rules".
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter NeuralNetwork Renormalization
open scoped ENNReal NNReal

namespace RGFlow

universe uA uI

variable {A : Type uA} {ι : Type uI} [Fintype ι] [Fintype A] [DecidableEq A]

omit [Fintype A] [DecidableEq A] in
/-- The stochastic metric restricted to two samples in a subset `B` is already computed by the
same formula applied to `B`'s own realization: no restriction operation is needed, since
`layerCovariance`'s sum ranges over neurons, not samples. This is the metric-level content of
`eq:marginalization-rule`, and needs no measure theory. -/
theorem stochasticMetric_eq_of_mem (p : InitHyperparams) (σ : ℝ → ℝ) (z : A → ι → ℝ)
    (B : Finset A) {a₁ a₂ : A} (h₁ : a₁ ∈ B) (h₂ : a₂ ∈ B) :
    stochasticMetric p σ z a₁ a₂ =
      stochasticMetric p σ (fun (b : {a // a ∈ B}) i => z b i) ⟨a₁, h₁⟩ ⟨a₂, h₂⟩ := rfl

/-- **Restriction to a subsample and a subset of neurons.**

Let `B ⊆ A` and `I ⊆ κ` be finite. The pushforward of layer `ℓ`'s marginal law under the
coordinate-restriction map to `I`-indexed neurons and `B`-indexed samples equals the marginal law
of layer `ℓ` computed with the dataset restricted to `B` and the neuron set restricted to `I`.

Informal proof: this is the general fact that a pushforward measure's expectation of a function of
finitely many coordinates depends only on the pushforward under projection to those coordinates.
Use `MeasureTheory.integral_map`, the coordinate-projection measurability of `batchPreactivation`,
and the projection of a finite `Measure.pi` product onto a sub-product of its factors (standard
Mathlib API for `Measure.pi`, whose exact name must still be verified in a scratch file per
Rule 1/Rule 8 of `lessons_learned.md` before this proof is filled in).
Source: `eq:marginalization-rule` and `eq:sum-rule-mlp`. -/
theorem map_restrict_eq_outputLaw_restrict
    {κ : Type*} [Fintype κ] [DecidableEq κ] (p : InitHyperparams) (σ : ℝ → ℝ) (z : A → ι → ℝ)
    (B : Finset A) (I : Finset κ) :
    Measure.map
      (fun w : κ → EuclideanSpace ℝ A =>
        fun (j : I) => (EuclideanSpace.equiv B ℝ).symm (fun a : B => (w j).ofLp (a : A)))
      (Measure.pi (fun _ : κ => multivariateGaussian 0 (stochasticMetric p σ z))) =
    Measure.pi (fun _ : I =>
      multivariateGaussian 0 (fun a₁ a₂ : B => stochasticMetric p σ z (a₁ : A) (a₂ : A))) := by
  sorry

/-- **Vertex and kernel recursions need only finitely many samples.**

Immediate corollary of `stochasticMetric_eq_of_mem`: the right-hand sides of
`meanMetric_eq_gaussianExpectation_add`/`fourPointVertex_eq_gaussianExpectation_add`, evaluated at
a fixed finite tuple of samples, depend on the previous layer's metric only through its
restriction to those samples.

Source: subsubsection "Marginalization over samples," book lines 3023-3036. -/
theorem fourPointVertex_eq_of_mem (ν : Measure (A → ι → ℝ)) (n : ℕ) (p : InitHyperparams)
    (σ : ℝ → ℝ) (B : Finset A) {a₁ a₂ a₃ a₄ : A}
    (h₁ : a₁ ∈ B) (h₂ : a₂ ∈ B) (h₃ : a₃ ∈ B) (h₄ : a₄ ∈ B) :
    fourPointVertex ν n p σ a₁ a₂ a₃ a₄ =
      (n : ℝ) * jointCumulant (ν.map (fun z (b : {a // a ∈ B}) i => z (b : A) i))
        ![fun z => stochasticMetric p σ z ⟨a₁, h₁⟩ ⟨a₂, h₂⟩,
          fun z => stochasticMetric p σ z ⟨a₃, h₃⟩ ⟨a₄, h₄⟩] := by
  sorry

end RGFlow
