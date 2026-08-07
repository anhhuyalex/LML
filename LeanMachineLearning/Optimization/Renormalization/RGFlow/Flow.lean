/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.RGFlow.Subleading

/-!
# RG flow: vocabulary

This file formalizes the "relevant"/"irrelevant" coupling vocabulary of
`docs/Renormalization.md`'s `sec:marginalization-group-flow` (book lines 3356-3361). As the
blueprint's Remark "Representation group flow is exactly kernel composition" explains, the
"RG flow" slogan itself needs no new probability-theory declaration: it is exactly
`NeuralNetwork.MLPEnsemble.outputKernel`'s sequential kernel composition, already proved in
Chapter "Renormalization foundations and neural-network ensembles". This file adds only the two
ordinary monotonicity predicates the source's vocabulary names.

See `LML/blueprint/src/chapters/renormalization.tex`, Chapter "RG flow of preactivations",
Section "RG flow: vocabulary".
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter NeuralNetwork Renormalization
open scoped ENNReal NNReal

namespace RGFlow

universe uA

variable {A : Type uA} [Fintype A]

/-- A scalar summary of a four-point vertex at one layer: the sum of squares of its entries. Any
other norm on the finite-dimensional space of such tensors would serve equally well for the
monotonicity predicates below; this one needs no extra structure beyond `Fintype A`. -/
def vertexNormSq (V : A → A → A → A → ℝ) : ℝ :=
  ∑ a₁, ∑ a₂, ∑ a₃, ∑ a₄, V a₁ a₂ a₃ a₄ ^ 2

theorem vertexNormSq_nonneg (V : A → A → A → A → ℝ) : 0 ≤ vertexNormSq V := by
  unfold vertexNormSq
  positivity

/-- **A coupling is relevant along the (representation-group) flow** if its size is eventually
increasing with depth.

Source: the paragraph defining relevant/irrelevant couplings, book lines 3356-3361. -/
def RelevantCoupling (V : ℕ → A → A → A → A → ℝ) : Prop :=
  Monotone fun ℓ => vertexNormSq (V ℓ)

/-- **A coupling is irrelevant along the flow** if its size is eventually decreasing with depth.

A coupling that is both relevant and irrelevant is, in the source's terminology, *marginal*. -/
def IrrelevantCoupling (V : ℕ → A → A → A → A → ℝ) : Prop :=
  Antitone fun ℓ => vertexNormSq (V ℓ)

/-- A coupling that is both relevant and irrelevant is constant in depth (the "marginal" case
mentioned in the source's footnote). -/
theorem vertexNormSq_const_of_relevant_of_irrelevant (V : ℕ → A → A → A → A → ℝ)
    (hrel : RelevantCoupling V) (hirr : IrrelevantCoupling V) :
    ∀ ℓ₁ ℓ₂, vertexNormSq (V ℓ₁) = vertexNormSq (V ℓ₂) := by
  intro ℓ₁ ℓ₂
  rcases le_total ℓ₁ ℓ₂ with h | h
  · exact le_antisymm (hrel h) (hirr h)
  · exact (le_antisymm (hrel h) (hirr h)).symm

/-!
**Representation group flow is exactly kernel composition.**

The source's Equations `eq:full-distribution-factorization` and `eq:full-action-decomposition`
describe the joint law of all layers as a Markov chain and its marginals as sequential
integration — precisely what `NeuralNetwork.MLPEnsemble.outputKernel` already computes by `Kernel`
composition (Theorem `thm:renorm:deepKernelLaw` in Chapter "Renormalization foundations and
neural-network ensembles"). No further Lean declaration is added for those two equations, nor for
the physics-history footnote or field-theory analogy (book lines 3280-3348), which are
expository.
-/

end RGFlow
