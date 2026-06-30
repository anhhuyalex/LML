/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Approximation.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Multivariate approximation (folklore construction, Theorem 2.1)

This file formalizes Theorem 2.1 and its supporting lemmas from Chapter 2 of the
deep learning theory notes:

1. Piecewise constant approximation of continuous functions (Lemma 2.1).
2. Rectangle indicator network construction (the gγ network).
3. The curse-of-dimension upper bound: a 3-layer ReLU network with Ω(1/δᵈ) nodes
   achieves L¹-error ≤ 2ε on [0,1]ᵈ.

## Main definitions

* `RectanglePartition d` : a δ-fine rectangle partition of a subset of ℝᵈ
* `piecewiseConstApprox` : piecewise constant function from Lemma 2.1
* `rectIndicatorNet` : the rectangle indicator network gγ
* `folkloreBound` : the main approximation theorem

-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Real Finset

namespace Approximation.Multivariate

/-! ### Uniform modulus of continuity -/

/-- The uniform modulus of continuity: ω_g(δ) = sup{|g(x)-g(x')| : ‖x-x'‖_∞ ≤ δ}. -/
noncomputable def uniformModulus {d : ℕ} (g : (Fin d → ℝ) → ℝ) (δ : ℝ) : ℝ :=
  ⨆ x : { p : (Fin d → ℝ) × (Fin d → ℝ) //
    ∀ j, |p.1 j - p.2 j| ≤ δ }, |g x.val.1 - g x.val.2|

/-! ### Rectangle partitions -/

/-- A half-open rectangle in ℝᵈ, given by its left endpoints and widths. -/
structure Rectangle (d : ℕ) where
  /-- Left endpoints of the rectangle in each coordinate. -/
  left : Fin d → ℝ
  /-- Side lengths of the rectangle in each coordinate. -/
  width : Fin d → ℝ
  width_pos : ∀ j, 0 < width j

/-- The set of points in a rectangle. -/
def Rectangle.toSet {d : ℕ} (R : Rectangle d) : Set (Fin d → ℝ) :=
  { x | ∀ j, R.left j ≤ x j ∧ x j < R.left j + R.width j }

/-- A rectangle is δ-fine if all side lengths are ≤ δ. -/
def Rectangle.isFine {d : ℕ} (R : Rectangle d) (δ : ℝ) : Prop :=
  ∀ j, R.width j ≤ δ

/-- A δ-fine rectangle partition of a set U: a finite collection of pairwise disjoint,
    δ-fine rectangles whose union is U. -/
structure RectanglePartition (d : ℕ) (U : Set (Fin d → ℝ)) (δ : ℝ) where
  /-- The finite collection of rectangles forming the partition. -/
  rectangles : Finset (Rectangle d)
  cover      : ∀ x ∈ U, ∃ R ∈ rectangles, x ∈ R.toSet
  disjoint   : ∀ R₁ ∈ rectangles, ∀ R₂ ∈ rectangles, R₁ ≠ R₂ →
    R₁.toSet ∩ R₂.toSet = ∅
  fine       : ∀ R ∈ rectangles, R.isFine δ

/-! ### Piecewise constant approximation (Lemma 2.1) -/

/-- Choose a representative point from each rectangle. -/
noncomputable def representative {d : ℕ} (R : Rectangle d) : Fin d → ℝ :=
  fun j => R.left j

/-- Piecewise constant approximation h = ∑ᵢ g(xᵢ) · 1_{Rᵢ}. -/
noncomputable def piecewiseConstApprox {d : ℕ} {U : Set (Fin d → ℝ)} {δ : ℝ}
    (g : (Fin d → ℝ) → ℝ) (P : RectanglePartition d U δ) (x : Fin d → ℝ) : ℝ :=
  ∑ R ∈ P.rectangles, g (representative R) * R.toSet.indicator 1 x

/-- Lemma 2.1: piecewise constant approximation error ≤ modulus at scale δ. -/
theorem piecewiseConstApprox_error {d : ℕ} {U : Set (Fin d → ℝ)} {δ ε : ℝ}
    (g : (Fin d → ℝ) → ℝ) (P : RectanglePartition d U δ)
    (hω : uniformModulus g δ ≤ ε) :
    ∀ x ∈ U, |piecewiseConstApprox g P x - g x| ≤ ε := by
  sorry

/-! ### Rectangle indicator network (gγ construction) -/

/-- The soft indicator for a single coordinate interval [a, b) at smoothing scale γ. -/
noncomputable def softStep (a b γ : ℝ) (z : ℝ) : ℝ :=
  reluActivation ((z - (a - γ)) / γ)
  - reluActivation ((z - a) / γ)
  - reluActivation ((z - b) / γ)
  + reluActivation ((z - (b + γ)) / γ)

/-- The rectangle indicator network gγ for rectangle R at smoothing scale γ. -/
noncomputable def rectIndicatorNet {d : ℕ} (R : Rectangle d) (γ : ℝ) (x : Fin d → ℝ) : ℝ :=
  reluActivation (∑ j : Fin d, softStep (R.left j) (R.left j + R.width j) γ (x j) - (d - 1 : ℝ))

/-- gγ = 1 inside R. -/
lemma rectIndicatorNet_one {d : ℕ} {R : Rectangle d} {γ : ℝ} (hγ : 0 < γ)
    {x : Fin d → ℝ} (hx : x ∈ R.toSet) :
    rectIndicatorNet R γ x = 1 := by
  sorry

/-- gγ = 0 outside the γ-padded rectangle. -/
lemma rectIndicatorNet_zero {d : ℕ} {R : Rectangle d} {γ : ℝ} (hγ : 0 < γ)
    {x : Fin d → ℝ}
    (hx : ∃ j, x j < R.left j - γ ∨ x j ≥ R.left j + R.width j + γ) :
    rectIndicatorNet R γ x = 0 := by
  sorry

/-- L¹ error between gγ and the indicator of R is O(γ). -/
lemma rectIndicatorNet_L1_error {d : ℕ} {R : Rectangle d} {γ : ℝ} (hγ : 0 < γ)
    (μ : MeasureTheory.Measure (Fin d → ℝ)) :
    ∫ x, |rectIndicatorNet R γ x - R.toSet.indicator 1 x| ∂μ ≤
    (∏ j : Fin d, (R.width j + 2 * γ)) - ∏ j : Fin d, R.width j := by
  sorry

/-! ### Main theorem: multivariate folklore bound (Theorem 2.1) -/

/-- Theorem 2.1: for continuous g with modulus ε at scale δ, there is a 3-layer ReLU network
    with Ω(1/δᵈ) nodes achieving L¹-error ≤ 2ε on [0,1]ᵈ.

    The network is constructed as f = ∑ᵢ αᵢ · gγ(·; Rᵢ) where the Rᵢ partition [0,2)ᵈ. -/
theorem folkloreBound {d : ℕ} {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (g : (Fin d → ℝ) → ℝ) (hg : Continuous g)
    (hω : uniformModulus g δ ≤ ε)
    (μ : MeasureTheory.Measure (Fin d → ℝ)) :
    ∃ (f : (Fin d → ℝ) → ℝ),
      (∃ m₁ : ℕ, f ∈ TwoHiddenLayer.FunctionClass reluActivation d m₁ 1) ∧
      ∫ x : Fin d → ℝ, |f x - g x| ∂μ ≤ 2 * ε := by
  sorry

end Approximation.Multivariate

end
