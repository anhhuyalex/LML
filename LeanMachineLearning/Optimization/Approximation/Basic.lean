/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Neural network function classes and activations

This file defines the basic building blocks for neural network approximation theory,
corresponding to Section 2 of the deep learning theory notes.

## Main definitions

* `thresholdActivation` : the Heaviside threshold function σ(z) = 1[z ≥ 0]
* `reluActivation` : the ReLU function σ(z) = max(z, 0)
* `Sigmoidal` : predicate for sigmoidal activations (continuous, limits 0 and 1)
* `OneHiddenLayer.FunctionClass σ d m` : class of single-hidden-layer networks
  with activation σ, input dimension d, and width m
* `OneHiddenLayer.UnboundedClass σ d` : union over all widths m

-/

@[expose] public section

open Real

namespace Approximation

/-! ### Activation functions -/

/-- The threshold (Heaviside) activation: σ(z) = 1 if z ≥ 0, else 0. -/
noncomputable def thresholdActivation : ℝ → ℝ := fun z => if z ≥ 0 then 1 else 0

/-- The ReLU activation: σ(z) = max(z, 0). -/
noncomputable def reluActivation : ℝ → ℝ := fun z => max z 0

/-- A sigmoidal activation is continuous with limits 0 at -∞ and 1 at +∞. -/
structure Sigmoidal (σ : ℝ → ℝ) : Prop where
  continuous : Continuous σ
  tendsto_atBot : Filter.Tendsto σ Filter.atBot (nhds 0)
  tendsto_atTop : Filter.Tendsto σ Filter.atTop (nhds 1)

lemma thresholdActivation_sigmoidal : Sigmoidal thresholdActivation := by
  refine ⟨?_, ?_, ?_⟩
  · sorry
  · sorry
  · sorry

/-! ### Single-hidden-layer networks -/

namespace OneHiddenLayer

/-- A single-hidden-layer network with activation σ, input dimension d, width m.
  f(x) = ∑ᵢ aᵢ · σ(wᵢᵀx + bᵢ), with a ∈ ℝ^m, W ∈ ℝ^(m×d), b ∈ ℝ^m. -/
structure Network (σ : ℝ → ℝ) (d m : ℕ) where
  /-- Weight matrix: `weights i j` is the weight from input `j` to neuron `i`. -/
  weights : Fin m → EuclideanSpace ℝ (Fin d)
  /-- Bias vector: `biases i` is the bias of neuron `i`. -/
  biases  : Fin m → ℝ
  /-- Output coefficients: `coeffs i` is the coefficient of neuron `i`. -/
  coeffs  : Fin m → ℝ

/-- Evaluate a single-hidden-layer network at a point. -/
noncomputable def affineMap {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) (b : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  inner ℝ w x + b

lemma affineMap_add {d : ℕ} (w₁ w₂ : EuclideanSpace ℝ (Fin d)) (b₁ b₂ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    affineMap (w₁ + w₂) (b₁ + b₂) x = affineMap w₁ b₁ x + affineMap w₂ b₂ x := by
  simp [affineMap, inner_add_left, add_assoc, add_left_comm, add_comm]

lemma affineMap_sub {d : ℕ} (w₁ w₂ : EuclideanSpace ℝ (Fin d)) (b₁ b₂ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    affineMap (w₁ - w₂) (b₁ - b₂) x = affineMap w₁ b₁ x - affineMap w₂ b₂ x := by
  simp [affineMap, inner_add_left, inner_neg_left, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]

/-- Recenter an affine functional to the translated inner product `z ↦ c⟪z - v, u⟫`. -/
lemma affineMap_smul_sub_inner {d : ℕ} (c : ℝ)
    (u v z : EuclideanSpace ℝ (Fin d)) :
    affineMap (c • u) (-c * inner ℝ v u) z = c * inner ℝ (z - v) u := by
  calc
    affineMap (c • u) (-c * inner ℝ v u) z
        = c * inner ℝ u z - c * inner ℝ v u := by
            simp [affineMap, real_inner_smul_left, sub_eq_add_neg]
    _ = c * inner ℝ z u - c * inner ℝ v u := by rw [real_inner_comm u z]
    _ = c * (inner ℝ z u - inner ℝ v u) := by ring
    _ = c * inner ℝ (z - v) u := by rw [inner_sub_left]

/-- Evaluate a single-hidden-layer network at a point. -/
noncomputable def Network.eval (σ : ℝ → ℝ) {d m : ℕ} (net : Network σ d m)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ i : Fin m, net.coeffs i * σ (affineMap (net.weights i) (net.biases i) x)

/-- The set of functions realized by single-hidden-layer networks of width m. -/
def FunctionClass (σ : ℝ → ℝ) (d m : ℕ) : Set ((EuclideanSpace ℝ (Fin d)) → ℝ) :=
  { f | ∃ net : Network σ d m, f = net.eval σ }

/-- The unbounded-width class: union over all widths. -/
def UnboundedClass (σ : ℝ → ℝ) (d : ℕ) : Set ((EuclideanSpace ℝ (Fin d)) → ℝ) :=
  ⋃ m : ℕ, FunctionClass σ d m

lemma mem_FunctionClass_iff {σ : ℝ → ℝ} {d m : ℕ}
    {f : (EuclideanSpace ℝ (Fin d)) → ℝ} :
    f ∈ FunctionClass σ d m ↔ ∃ net : Network σ d m, f = net.eval σ :=
  Iff.rfl

lemma mem_UnboundedClass_iff {σ : ℝ → ℝ} {d : ℕ}
    {f : (EuclideanSpace ℝ (Fin d)) → ℝ} :
    f ∈ UnboundedClass σ d ↔ ∃ m : ℕ, ∃ net : Network σ d m, f = net.eval σ := by
  simp [UnboundedClass, FunctionClass]

end OneHiddenLayer

/-! ### Two-hidden-layer networks -/

namespace TwoHiddenLayer

/-- A two-hidden-layer network with activation σ, input dimension d, widths m₁, m₂. -/
structure Network (σ : ℝ → ℝ) (d m₁ m₂ : ℕ) where
  /-- First-layer weight matrix. -/
  weights₁ : Fin m₁ → EuclideanSpace ℝ (Fin d)
  /-- First-layer bias vector. -/
  biases₁  : Fin m₁ → ℝ
  /-- Second-layer weight matrix. -/
  weights₂ : Fin m₂ → Fin m₁ → ℝ
  /-- Second-layer bias vector. -/
  biases₂  : Fin m₂ → ℝ
  /-- Output coefficients. -/
  coeffs   : Fin m₂ → ℝ

/-- Evaluate a two-hidden-layer network at a point. -/
noncomputable def Network.eval (σ : ℝ → ℝ) {d m₁ m₂ : ℕ} (net : Network σ d m₁ m₂)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ j : Fin m₂,
    net.coeffs j * σ (∑ i : Fin m₁,
      net.weights₂ j i * σ (∑ k : Fin d, net.weights₁ i k * x k + net.biases₁ i)
      + net.biases₂ j)

/-- The set of functions realized by two-hidden-layer networks of widths m₁, m₂. -/
def FunctionClass (σ : ℝ → ℝ) (d m₁ m₂ : ℕ) : Set ((EuclideanSpace ℝ (Fin d)) → ℝ) :=
  { f | ∃ net : Network σ d m₁ m₂, f = net.eval σ }

end TwoHiddenLayer

end Approximation

end
