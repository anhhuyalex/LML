/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Approximation.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

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

variable {d : ℕ}



@[expose] public section

open MeasureTheory MeasureTheory.Measure Real Finset

noncomputable instance euclideanSpaceMeasureSpace : MeasureSpace (EuclideanSpace ℝ (Fin d)) where
  volume := volume

namespace Approximation.Multivariate

/-! ### Uniform modulus of continuity -/

/-- The uniform modulus of continuity: ω_g(δ) = sup{|g(x)-g(x')| : ‖x-x'‖_∞ ≤ δ}.

We define this in `WithTop ℝ` so the admissible values are automatically bounded above by `⊤`,
avoiding the nontrivial `BddAbove` witness that would be required for an `ℝ`-valued supremum. -/
noncomputable def uniformModulus (g : (EuclideanSpace ℝ (Fin d)) → ℝ) (δ : ℝ) : WithTop ℝ :=
  sSup (Set.range fun x : { p : (EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d)) //
    ∀ j, |p.1 j - p.2 j| ≤ δ } => ((|g x.val.1 - g x.val.2| : ℝ) : WithTop ℝ))

lemma le_uniformModulus {g : (EuclideanSpace ℝ (Fin d)) → ℝ} {δ : ℝ}
    (p : { q : (EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d)) //
      ∀ j, |q.1 j - q.2 j| ≤ δ }) :
    ((|g p.val.1 - g p.val.2| : ℝ) : WithTop ℝ) ≤ uniformModulus g δ := by
  exact le_csSup (OrderTop.bddAbove _) (Set.mem_range_self p)

/-! ### Rectangle partitions -/

/-- A half-open rectangle in ℝᵈ, given by its left endpoints and widths. -/
structure Rectangle (d : ℕ) where
  /-- Left endpoints of the rectangle in each coordinate. -/
  left : EuclideanSpace ℝ (Fin d)
  /-- Side lengths of the rectangle in each coordinate. -/
  width : EuclideanSpace ℝ (Fin d)
  width_pos : ∀ j, 0 < width j

/-- The set of points in a rectangle. -/
def Rectangle.toSet {d : ℕ} (R : Rectangle d) : Set (EuclideanSpace ℝ (Fin d)) :=
  { x | ∀ j, R.left j ≤ x j ∧ x j < R.left j + R.width j }

/-- A rectangle is δ-fine if all side lengths are ≤ δ. -/
def Rectangle.isFine (R : Rectangle d) (δ : ℝ) : Prop :=
  ∀ j, R.width j ≤ δ

/-- A δ-fine rectangle partition of a set U: a finite collection of pairwise disjoint,
    δ-fine rectangles whose union is U. -/
structure RectanglePartition (d : ℕ) (U : Set (EuclideanSpace ℝ (Fin d))) (δ : ℝ) where
  /-- The finite collection of rectangles forming the partition. -/
  rectangles : Finset (Rectangle d)
  cover      : ∀ x ∈ U, ∃ R ∈ rectangles, x ∈ R.toSet
  disjoint   : ∀ R₁ ∈ rectangles, ∀ R₂ ∈ rectangles, R₁ ≠ R₂ →
    R₁.toSet ∩ R₂.toSet = ∅
  fine       : ∀ R ∈ rectangles, R.isFine δ

/-! ### Piecewise constant approximation (Lemma 2.1) -/

/-- Choose a representative point from each rectangle. -/
noncomputable def representative (R : Rectangle d) : EuclideanSpace ℝ (Fin d) :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm R.left

/-- Piecewise constant approximation h = ∑ᵢ g(xᵢ) · 1_{Rᵢ}. -/
noncomputable def piecewiseConstApprox {U : Set (EuclideanSpace ℝ (Fin d))} {δ : ℝ}
    (g : (EuclideanSpace ℝ (Fin d)) → ℝ) (P : RectanglePartition d U δ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ R ∈ P.rectangles, g (representative R) * R.toSet.indicator (fun _ => (1 : ℝ)) x

/-- Lemma 2.1: piecewise constant approximation error ≤ modulus at scale δ. -/
theorem piecewiseConstApprox_error {U : Set (EuclideanSpace ℝ (Fin d))} {δ ε : ℝ}
    (g : (EuclideanSpace ℝ (Fin d)) → ℝ) (P : RectanglePartition d U δ)
    (hω : uniformModulus g δ ≤ (ε : WithTop ℝ)) :
    ∀ x ∈ U, |piecewiseConstApprox g P x - g x| ≤ ε := by
  intro x hx
  -- Step 1: Obtain the (unique) rectangle R in the partition that contains x
  rcases P.cover x hx with ⟨R, hR, hxR⟩
  -- Step 2: Show that the piecewise constant approximant simplifies to g(representative R) at x
  have h_piecewise : piecewiseConstApprox g P x = g (representative R) := by
    dsimp [piecewiseConstApprox]
    calc
      ∑ R' ∈ P.rectangles, g (representative R') * R'.toSet.indicator (fun _ => (1 : ℝ)) x
        = g (representative R) * R.toSet.indicator (fun _ => (1 : ℝ)) x := by
          refine Finset.sum_eq_single_of_mem R hR ?_
          intro R' hR' h_ne
          have h_disjoint := P.disjoint R hR R' hR' h_ne.symm
          have hx_not_mem : x ∉ R'.toSet := by
            intro hxR'
            have hx_inter : x ∈ R.toSet ∩ R'.toSet := ⟨hxR, hxR'⟩
            rw [h_disjoint] at hx_inter
            exact hx_inter
          simp [hx_not_mem]
      _ = g (representative R) * 1 := by
          rw [Set.indicator_of_mem hxR]
      _ = g (representative R) := by ring
  rw [h_piecewise]
  -- Step 3: For each coordinate j, show |(representative R) j - x j| ≤ δ
  have h_dist : ∀ j, |(representative R) j - x j| ≤ δ := by
    intro j
    have hxRj := hxR j
    rcases hxRj with ⟨h_left, h_right⟩
    -- From P.fine, the width of R in coordinate j is ≤ δ
    have h_fine := P.fine R hR j
    -- representative R equals R.left coordinate-wise
    have h_rep : (representative R) j = R.left j := by
      simp [representative]
    rw [h_rep]
    -- Now we need |R.left j - x j| ≤ δ. Since R.left j ≤ x j, the absolute value is x j - R.left j
    have h_nonneg : 0 ≤ x j - R.left j := by linarith
    have h_lt_width : x j - R.left j < R.width j := by linarith
    -- Chain: x j - R.left j < R.width j ≤ δ, so it's ≤ δ
    have h_le : x j - R.left j ≤ δ := by linarith
    -- |R.left j - x j| = |x j - R.left j| by abs_sub_comm
    rw [abs_sub_comm, abs_of_nonneg h_nonneg]
    exact h_le
  -- Step 4: Use the definition of uniformModulus to bound |g(representative R) - g x|
  have h_abs : ((|g (representative R) - g x| : ℝ) : WithTop ℝ) ≤ uniformModulus g δ := by
    exact le_uniformModulus ⟨(representative R, x), h_dist⟩
  -- Step 5: Transitivity with hω
  simpa using le_trans h_abs hω

/-! ### Rectangle indicator network (gγ construction) -/

/-- The soft indicator for a single coordinate interval [a, b) at smoothing scale γ. -/
noncomputable def softStep (a b γ : ℝ) (z : ℝ) : ℝ :=
  reluActivation ((z - (a - γ)) / γ)
  - reluActivation ((z - a) / γ)
  - reluActivation ((z - b) / γ)
  + reluActivation ((z - (b + γ)) / γ)

/-- The rectangle indicator network gγ for rectangle R at smoothing scale γ. -/
noncomputable def rectIndicatorNet (R : Rectangle d) (γ : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  reluActivation (∑ j : Fin d, softStep (R.left j) (R.left j + R.width j) γ (x j) - (d - 1 : ℝ))

/-- If γ > 0 and a ≤ z < b, then the soft step function equals 1. -/
lemma softStep_eq_one {a b γ z : ℝ} (hγ : 0 < γ) (hz : a ≤ z ∧ z < b) : softStep a b γ z = 1 := by
  rcases hz with ⟨hle, hlt⟩
  dsimp [softStep, reluActivation]
  -- The four ReLU terms: analyze sign of each argument
  have hz_minus_a_nonneg : 0 ≤ z - a := by linarith
  have hz_minus_b_neg : z - b < 0 := by linarith
  have hz_minus_b_plus_γ_neg : z - (b + γ) < 0 := by linarith
  -- Nonnegativity/negativity of the divided terms
  have h_div1 : 0 ≤ (z - (a - γ)) / γ := div_nonneg (by linarith) hγ.le
  have h_div2 : 0 ≤ (z - a) / γ := div_nonneg hz_minus_a_nonneg hγ.le
  have h_div3 : (z - b) / γ < 0 := div_neg_of_neg_of_pos hz_minus_b_neg hγ
  have h_div4 : (z - (b + γ)) / γ < 0 := div_neg_of_neg_of_pos hz_minus_b_plus_γ_neg hγ
  -- Replace each max(z,0) by either z (when nonneg) or 0 (when negative)
  rw [max_eq_left h_div1, max_eq_left h_div2, max_eq_right h_div3.le, max_eq_right h_div4.le]
  -- Now it's a rational expression: (z-(a-γ))/γ - (z-a)/γ = 1
  field_simp [hγ.ne.symm]
  ring

/-- gγ = 1 inside R. -/
lemma rectIndicatorNet_one {R : Rectangle d} {γ : ℝ} (hγ : 0 < γ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ R.toSet) :
    rectIndicatorNet R γ x = 1 := by
  -- hx gives: for all j, R.left j ≤ x j < R.left j + R.width j
  dsimp [rectIndicatorNet]
  have h_softstep : ∀ j : Fin d, softStep (R.left j) (R.left j + R.width j) γ (x j) = 1 := by
    intro j
    -- hx j : R.left j ≤ x j ∧ x j < R.left j + R.width j
    exact softStep_eq_one hγ (hx j)
  -- Sum of softStep over all coordinates equals d
  have h_sum : (∑ j : Fin d, softStep (R.left j) (R.left j + R.width j) γ (x j)) = (d : ℝ) := by
    calc
      (∑ j : Fin d, softStep (R.left j) (R.left j + R.width j) γ (x j))
          = (∑ j : Fin d, (1 : ℝ)) := by
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [h_softstep j]
      _ = (d : ℝ) := by simp
  rw [h_sum]
  -- Now: reluActivation ((d : ℝ) - (d - 1 : ℝ)) = 1
  dsimp [reluActivation]
  have h_sub : (d : ℝ) - (d - 1 : ℝ) = 1 := by
    ring
  rw [h_sub]
  norm_num

/-- If γ > 0, a ≤ b, and z is to the left of the γ-padded interval (z < a - γ)
    or to the right (z ≥ b + γ), then the soft step function equals 0. -/
lemma softStep_eq_zero {a b γ z : ℝ} (hγ : 0 < γ) (h_ab : a ≤ b) (hz : z < a - γ ∨ z ≥ b + γ) :
    softStep a b γ z = 0 := by
  rcases hz with (hz_lt | hz_ge)
  · -- Case: z < a - γ  (all four ReLU arguments are negative → all max = 0)
    dsimp [softStep, reluActivation]
    have h_div1 : (z - (a - γ)) / γ < 0 := div_neg_of_neg_of_pos (by linarith) hγ
    have h_div2 : (z - a) / γ < 0 := div_neg_of_neg_of_pos (by linarith) hγ
    have h_div3 : (z - b) / γ < 0 := div_neg_of_neg_of_pos (by linarith) hγ
    have h_div4 : (z - (b + γ)) / γ < 0 := div_neg_of_neg_of_pos (by linarith) hγ
    rw [max_eq_right h_div1.le, max_eq_right h_div2.le, max_eq_right h_div3.le,
      max_eq_right h_div4.le]
    norm_num
  · -- Case: z ≥ b + γ  (all four ReLU arguments are nonnegative → all max = argument)
    dsimp [softStep, reluActivation]
    have h_div1 : 0 ≤ (z - (a - γ)) / γ := div_nonneg (by linarith) hγ.le
    have h_div2 : 0 ≤ (z - a) / γ := div_nonneg (by linarith) hγ.le
    have h_div3 : 0 ≤ (z - b) / γ := div_nonneg (by linarith) hγ.le
    have h_div4 : 0 ≤ (z - (b + γ)) / γ := div_nonneg (by linarith) hγ.le
    rw [max_eq_left h_div1, max_eq_left h_div2, max_eq_left h_div3, max_eq_left h_div4]
    field_simp [hγ.ne.symm]
    ring_nf

/-- If γ > 0 and a ≤ b, the soft step function is bounded above by 1 for all z. -/
lemma softStep_le_one {a b γ z : ℝ} (hγ : 0 < γ) (h_ab : a ≤ b) : softStep a b γ z ≤ 1 := by
  dsimp [softStep, reluActivation]
  by_cases hz1 : z ≤ a - γ
  · -- Region I: z ≤ a-γ  → all terms ≤ 0 → softStep = 0 ≤ 1
    have h1 : (z - (a - γ)) / γ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hγ.le
    have h2 : (z - a) / γ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hγ.le
    have h3 : (z - b) / γ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hγ.le
    have h4 : (z - (b + γ)) / γ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hγ.le
    rw [max_eq_right h1, max_eq_right h2, max_eq_right h3, max_eq_right h4]
    norm_num
  · -- z > a-γ
    by_cases hz2 : z ≤ a
    · -- Region II: a-γ ≤ z ≤ a  → only first ReLU fires: softStep = (z-(a-γ))/γ ≤ 1
      have h1 : 0 ≤ (z - (a - γ)) / γ := div_nonneg (by linarith) hγ.le
      have h2 : (z - a) / γ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hγ.le
      have h3 : (z - b) / γ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hγ.le
      have h4 : (z - (b + γ)) / γ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hγ.le
      rw [max_eq_left h1, max_eq_right h2, max_eq_right h3, max_eq_right h4]
      field_simp [hγ.ne.symm]
      linarith
    · -- z > a
      by_cases hz3 : z ≤ b
      · -- Region III: a ≤ z ≤ b  → first two ReLUs fire: softStep = 1
        have h1 : 0 ≤ (z - (a - γ)) / γ := div_nonneg (by linarith) hγ.le
        have h2 : 0 ≤ (z - a) / γ := div_nonneg (by linarith) hγ.le
        have h3 : (z - b) / γ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hγ.le
        have h4 : (z - (b + γ)) / γ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hγ.le
        rw [max_eq_left h1, max_eq_left h2, max_eq_right h3, max_eq_right h4]
        field_simp [hγ.ne.symm]
        ring_nf
        exact le_refl γ
      · -- z > b
        by_cases hz4 : z ≤ b + γ
        · -- Region IV: b ≤ z ≤ b+γ  → first three ReLUs fire: softStep = 1 - (z-b)/γ ≤ 1
          have h1 : 0 ≤ (z - (a - γ)) / γ := div_nonneg (by linarith) hγ.le
          have h2 : 0 ≤ (z - a) / γ := div_nonneg (by linarith) hγ.le
          have h3 : 0 ≤ (z - b) / γ := div_nonneg (by linarith) hγ.le
          have h4 : (z - (b + γ)) / γ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hγ.le
          rw [max_eq_left h1, max_eq_left h2, max_eq_left h3, max_eq_right h4]
          field_simp [hγ.ne.symm]
          linarith
        · -- Region V: z ≥ b+γ  → all four ReLUs fire: softStep = 0 ≤ 1
          have h1 : 0 ≤ (z - (a - γ)) / γ := div_nonneg (by linarith) hγ.le
          have h2 : 0 ≤ (z - a) / γ := div_nonneg (by linarith) hγ.le
          have h3 : 0 ≤ (z - b) / γ := div_nonneg (by linarith) hγ.le
          have h4 : 0 ≤ (z - (b + γ)) / γ := div_nonneg (by linarith) hγ.le
          rw [max_eq_left h1, max_eq_left h2, max_eq_left h3, max_eq_left h4]
          field_simp [hγ.ne.symm]
          ring_nf
          exact hγ.le

/-- gγ = 0 outside the γ-padded rectangle. -/
lemma rectIndicatorNet_zero {R : Rectangle d} {γ : ℝ} (hγ : 0 < γ)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : ∃ j, x j < R.left j - γ ∨ x j ≥ R.left j + R.width j + γ) :
    rectIndicatorNet R γ x = 0 := by
  rcases hx with ⟨j, hx_j⟩
  dsimp [rectIndicatorNet]
  -- For each coordinate k, the soft step is ≤ 1 (by softStep_le_one).
  have h_softstep_le_one : ∀ k : Fin d,
      softStep (R.left k) (R.left k + R.width k) γ (x k) ≤ 1 := by
    intro k
    have h_ab_k : R.left k ≤ R.left k + R.width k := by
      have := R.width_pos k
      linarith
    exact softStep_le_one hγ h_ab_k (z := x k)
  -- For the distinguished coordinate j, the soft step is exactly 0.
  have h_ab_j : R.left j ≤ R.left j + R.width j := by
    have := R.width_pos j
    linarith
  have h_softstep_zero : softStep (R.left j) (R.left j + R.width j) γ (x j) = 0 :=
    softStep_eq_zero hγ h_ab_j hx_j
  -- Split the sum into the term at j and the rest.
  have h_sum_split : (∑ k : Fin d, softStep (R.left k) (R.left k + R.width k) γ (x k))
      = softStep (R.left j) (R.left j + R.width j) γ (x j)
        + (∑ k ∈ (Finset.univ.erase j),
            softStep (R.left k) (R.left k + R.width k) γ (x k)) := by
    calc
      (∑ k : Fin d, softStep (R.left k) (R.left k + R.width k) γ (x k))
          = (∑ k ∈ (Finset.univ.erase j),
              softStep (R.left k) (R.left k + R.width k) γ (x k))
            + softStep (R.left j) (R.left j + R.width j) γ (x j) :=
        (Finset.sum_erase_add (Finset.univ : Finset (Fin d))
          (fun k => softStep (R.left k) (R.left k + R.width k) γ (x k))
          (Finset.mem_univ j)).symm
      _ = softStep (R.left j) (R.left j + R.width j) γ (x j)
            + (∑ k ∈ (Finset.univ.erase j),
                softStep (R.left k) (R.left k + R.width k) γ (x k)) := by
        ring
  -- The sum over all k is ≤ d-1 (since one term is 0 and all others ≤ 1).
  have h_total_le :
      (∑ k : Fin d, softStep (R.left k) (R.left k + R.width k) γ (x k)) ≤
        (d : ℝ) - 1 := by
    rw [h_sum_split, h_softstep_zero, zero_add]
    calc
      (∑ k ∈ (Finset.univ.erase j),
          softStep (R.left k) (R.left k + R.width k) γ (x k))
          ≤ (∑ k ∈ (Finset.univ.erase j), (1 : ℝ)) :=
        Finset.sum_le_sum fun k hk => h_softstep_le_one k
      _ = (d : ℝ) - 1 := by
        have h_erase := Finset.sum_erase_add (Finset.univ : Finset (Fin d))
          (fun _ => (1 : ℝ)) (Finset.mem_univ j)
        have h_total : (∑ k : Fin d, (1 : ℝ)) = (d : ℝ) := by simp
        linarith
  -- Therefore the argument to the outer ReLU is ≤ 0.
  have h_arg_nonpos : (∑ k : Fin d, softStep (R.left k) (R.left k + R.width k) γ (x k))
      - (d - 1 : ℝ) ≤ 0 := by
    linarith
  -- ReLU of a non-positive argument is 0.
  dsimp [reluActivation]
  exact max_eq_right h_arg_nonpos

lemma rectIndicatorNet_nonneg {R : Rectangle d} {γ : ℝ} (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ rectIndicatorNet R γ x := by
  dsimp [rectIndicatorNet, reluActivation]
  exact le_max_right _ _

lemma rectIndicatorNet_le_one {R : Rectangle d} {γ : ℝ} (hγ : 0 < γ)
    (x : EuclideanSpace ℝ (Fin d)) :
    rectIndicatorNet R γ x ≤ 1 := by
  dsimp [rectIndicatorNet, reluActivation]
  have h_sum :
      (∑ j : Fin d, softStep (R.left j) (R.left j + R.width j) γ (x j)) ≤
        (d : ℝ) := by
    calc
      (∑ j : Fin d, softStep (R.left j) (R.left j + R.width j) γ (x j))
          ≤ (∑ j : Fin d, (1 : ℝ)) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have h_ab : R.left j ≤ R.left j + R.width j := by
              have := R.width_pos j
              linarith
            exact softStep_le_one hγ h_ab
      _ = (d : ℝ) := by simp
  have h_arg :
      (∑ j : Fin d, softStep (R.left j) (R.left j + R.width j) γ (x j))
        - (d - 1 : ℝ) ≤ 1 := by
    linarith
  exact max_le h_arg zero_le_one

/-- L¹ error between gγ and the indicator of R is O(γ). -/
-- If s ⊆ t, then 1_s ≤ 1_t pointwise (as ℝ-valued indicators)
private lemma indicator_mono {α : Type*} {s t : Set α} (h : s ⊆ t) (x : α) :
    (s.indicator (fun _ => (1 : ℝ)) x : ℝ) ≤ (t.indicator (fun _ => (1 : ℝ)) x : ℝ) := by
  by_cases hx : x ∈ s
  · have hx_t : x ∈ t := h hx
    simp [hx, hx_t]
  · by_cases hx_t : x ∈ t
    · simp [hx, hx_t]
    · simp [hx, hx_t]

-- A half-open rectangle in ℝᵈ is measurable (finite intersection of half-open intervals)
private lemma measurableSet_half_open_rectangle (l w : Fin d → ℝ) :
    MeasurableSet {x : EuclideanSpace ℝ (Fin d) | ∀ j, l j ≤ x j ∧ x j < l j + w j} := by
  have h_proj_measurable (j : Fin d) : Measurable (fun x : EuclideanSpace ℝ (Fin d) => x j) := by
    have : (fun x : EuclideanSpace ℝ (Fin d) => x j) =
        (fun f : Fin d → ℝ => f j) ∘ (@WithLp.ofLp 2 (Fin d → ℝ)) := rfl
    rw [this]
    exact (measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 _)
  have : {x | ∀ j, l j ≤ x j ∧ x j < l j + w j} = ⋂ j : Fin d,
      {x : EuclideanSpace ℝ (Fin d) | l j ≤ x j} ∩
      {x : EuclideanSpace ℝ (Fin d) | x j < l j + w j} := by
    ext x; simp
  rw [this]
  refine MeasurableSet.iInter fun j => ?_
  refine (measurableSet_le (measurable_const) (h_proj_measurable j)).inter ?_
  exact measurableSet_lt (h_proj_measurable j) measurable_const

-- Volume of a half-open rectangle in ℝᵈ: {x | ∀ j, l j ≤ x j < l j + w j}
private lemma volume_half_open_rectangle_eq_prod (l w : Fin d → ℝ) (hw_pos : ∀ j, 0 < w j) :
    volume.real {x : EuclideanSpace ℝ (Fin d) | ∀ j, l j ≤ x j ∧ x j < l j + w j} = ∏ j, w j := by
  have h_eq : {x | ∀ j, l j ≤ x j ∧ x j < l j + w j} =
      (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' (Set.pi Set.univ (fun j => Set.Ico (l j) (l j + w j))) := by
    ext x; simp
  have h_meas : MeasurableSet (Set.pi Set.univ (fun j => Set.Ico (l j) (l j + w j))) :=
    MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Ico)
  rw [h_eq]
  change (volume ((@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹'
      (Set.pi Set.univ (fun j => Set.Ico (l j) (l j + w j))))).toReal = ∏ j, w j
  rw [(PiLp.volume_preserving_ofLp (ι := Fin d)).measure_preimage h_meas.nullMeasurableSet]
  have h_le : ∀ j, l j ≤ l j + w j := by
    intro j; linarith [hw_pos j]
  rw [volume_pi_Ico_toReal h_le]
  apply Finset.prod_congr rfl
  intro j _
  ring

-- rectIndicatorNet is continuous (as a composition of ReLU with continuous affine maps)
private lemma rectIndicatorNet_continuous {R : Rectangle d} {γ : ℝ} :
    Continuous (rectIndicatorNet R γ) := by
  have h_cont_relu : Continuous reluActivation := by
    unfold reluActivation
    exact continuous_id.max continuous_const
  -- softStep a b γ is continuous as a function ℝ → ℝ
  have h_cont_softStep_fn (a b : ℝ) : Continuous (fun (z : ℝ) => softStep a b γ z) := by
    dsimp [softStep]
    have h_term (c : ℝ) : Continuous (fun (z : ℝ) => reluActivation ((z - c) / γ)) :=
      h_cont_relu.comp ((continuous_id.sub continuous_const).div_const γ)
    -- softStep = term(a-γ) - term(a) - term(b) + term(b+γ)
    exact Continuous.add
      (Continuous.sub
        (Continuous.sub (h_term (a - γ)) (h_term a))
        (h_term b))
      (h_term (b + γ))
  -- For each coordinate j, x ↦ softStep(...)(x j) is continuous on EuclideanSpace
  have h_cont_coord (j : Fin d) : Continuous (fun (x : EuclideanSpace ℝ (Fin d)) =>
      softStep (R.left j) (R.left j + R.width j) γ (x j)) :=
    (h_cont_softStep_fn (R.left j) (R.left j + R.width j)).comp
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) j)
  -- The sum over all coordinates is continuous
  have h_cont_sum : Continuous (fun (x : EuclideanSpace ℝ (Fin d)) =>
      ∑ j : Fin d, softStep (R.left j) (R.left j + R.width j) γ (x j)) :=
    continuous_finsetSum (Finset.univ : Finset (Fin d)) fun j _ => h_cont_coord j
  -- rectIndicatorNet = reluActivation ∘ (sum - (d-1)), hence continuous
  unfold rectIndicatorNet
  refine h_cont_relu.comp ?_
  exact h_cont_sum.sub continuous_const

-- Pointwise bound: |gγ - 1_R| ≤ 1_S - 1_R when R ⊆ S and gγ = 0 outside S
private lemma rectIndicatorNet_pointwise_bound {R : Rectangle d} {γ : ℝ} (hγ : 0 < γ)
    (S : Set (EuclideanSpace ℝ (Fin d))) (h_sub : R.toSet ⊆ S)
    (h_zero_outside : ∀ x, x ∉ S → rectIndicatorNet R γ x = 0) (x : EuclideanSpace ℝ (Fin d)) :
    |rectIndicatorNet R γ x - R.toSet.indicator (fun _ => (1 : ℝ)) x| ≤
    (S.indicator (fun _ => (1 : ℝ)) x : ℝ) - (R.toSet.indicator (fun _ => (1 : ℝ)) x : ℝ) := by
  by_cases hxS : x ∈ S
  · by_cases hxR : x ∈ R.toSet
    · -- x ∈ R ⊆ S: both sides = 0
      have h_rect_eq_one : rectIndicatorNet R γ x = 1 := rectIndicatorNet_one hγ hxR
      have h_ind_R : R.toSet.indicator (fun _ => (1 : ℝ)) x = (1 : ℝ) :=
        Set.indicator_of_mem hxR _
      have h_ind_S : S.indicator (fun _ => (1 : ℝ)) x = (1 : ℝ) :=
        Set.indicator_of_mem (h_sub hxR) _
      rw [h_rect_eq_one, h_ind_R, h_ind_S]
      simp
    · -- x ∈ S \ R: 0 ≤ gγ ≤ 1, so |gγ| ≤ 1 = 1_S - 1_R
      have h_ind_R : R.toSet.indicator (fun _ => (1 : ℝ)) x = (0 : ℝ) :=
        Set.indicator_of_notMem hxR _
      have h_ind_S : S.indicator (fun _ => (1 : ℝ)) x = (1 : ℝ) := Set.indicator_of_mem hxS _
      have h_nonneg : 0 ≤ rectIndicatorNet R γ x := rectIndicatorNet_nonneg x
      have h_le_one : rectIndicatorNet R γ x ≤ 1 := rectIndicatorNet_le_one hγ x
      rw [h_ind_R, h_ind_S]
      simp only [sub_zero, ge_iff_le]
      rw [abs_of_nonneg h_nonneg]
      exact h_le_one
  · -- x ∉ S: both sides = 0
    have h_rect_eq_zero : rectIndicatorNet R γ x = 0 := h_zero_outside x hxS
    have h_ind_R : R.toSet.indicator (fun _ => (1 : ℝ)) x = (0 : ℝ) :=
      Set.indicator_of_notMem (fun hxR => hxS (h_sub hxR)) _
    have h_ind_S : S.indicator (fun _ => (1 : ℝ)) x = (0 : ℝ) := Set.indicator_of_notMem hxS _
    rw [h_rect_eq_zero, h_ind_R, h_ind_S]
    simp

-- Volume of a half-open rectangle in ℝᵈ is finite
private lemma volume_half_open_rectangle_ne_top (l w : Fin d → ℝ) :
    volume {x : EuclideanSpace ℝ (Fin d) | ∀ j, l j ≤ x j ∧ x j < l j + w j} ≠ ⊤ := by
  have h_eq : {x | ∀ j, l j ≤ x j ∧ x j < l j + w j} =
      (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' (Set.pi Set.univ (fun j => Set.Ico (l j) (l j + w j))) := by
    ext x; simp
  have h_meas : MeasurableSet (Set.pi Set.univ (fun j => Set.Ico (l j) (l j + w j))) :=
    MeasurableSet.pi Set.countable_univ (fun i _ => measurableSet_Ico)
  rw [h_eq, (PiLp.volume_preserving_ofLp (ι := Fin d)).measure_preimage h_meas.nullMeasurableSet]
  have h_bdd : Bornology.IsBounded (Set.pi Set.univ (fun j => Set.Ico (l j) (l j + w j))) := by
    rw [Bornology.isBounded_pi]
    right; intro j; exact Metric.isBounded_Ico (l j) (l j + w j)
  exact h_bdd.measure_lt_top.ne

lemma rectIndicatorNet_L1_error {R : Rectangle d} {γ : ℝ} (hγ : 0 < γ) :
    ∫ x, |rectIndicatorNet R γ x - R.toSet.indicator (fun _ => (1 : ℝ)) x| ≤
    (∏ j : Fin d, (R.width j + 2 * γ)) - ∏ j : Fin d, R.width j := by
  /- We bound the integrand pointwise by the indicator of the expanded rectangle
     minus the indicator of R, then use the volume formula for half-open rectangles. -/
  -- 1. Define the γ-expanded rectangle
  set S : Set (EuclideanSpace ℝ (Fin d)) :=
    {x | ∀ j : Fin d, R.left j - γ ≤ x j ∧ x j < R.left j + R.width j + γ}
  -- 2. Basic inclusion: R ⊆ S
  have h_sub : R.toSet ⊆ S := fun x hx j => by
    rcases hx j with ⟨h_left, h_right⟩; exact ⟨by linarith, by linarith⟩
  -- 3. rectIndicatorNet = 0 outside S
  have h_zero_outside (x : EuclideanSpace ℝ (Fin d)) (hx : x ∉ S) : rectIndicatorNet R γ x = 0 := by
    rw [Set.mem_ofPred_eq] at hx
    have h_exists : ∃ j : Fin d, x j < R.left j - γ ∨ x j ≥ R.left j + R.width j + γ := by
      by_contra! h
      apply hx
      intro j
      have h_not_or := h j
      constructor
      · linarith
      · linarith
    rcases h_exists with ⟨j, hj_left | hj_right⟩
    · exact rectIndicatorNet_zero hγ ⟨j, Or.inl hj_left⟩
    · exact rectIndicatorNet_zero hγ ⟨j, Or.inr hj_right⟩
  -- 4. Pointwise inequality
  have h_pointwise (x : EuclideanSpace ℝ (Fin d)) :
      |rectIndicatorNet R γ x - R.toSet.indicator (fun _ => (1 : ℝ)) x| ≤
      (S.indicator (fun _ => (1 : ℝ)) x : ℝ) -
        (R.toSet.indicator (fun _ => (1 : ℝ)) x : ℝ) :=
    rectIndicatorNet_pointwise_bound hγ S h_sub h_zero_outside x
  -- Represent R.toSet and S as half-open rectangles (used for measurability, volume)
  have hR_eq : R.toSet = {x | ∀ j, R.left j ≤ x j ∧ x j < R.left j + R.width j} := by
    ext x; simp [Rectangle.toSet]
  have hS_eq :
      S =
        {x | ∀ j, (R.left j - γ) ≤ x j ∧
          x j < (R.left j - γ) + (R.width j + 2 * γ)} := by
    ext x; constructor
    · intro h j; rcases h j with ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    · intro h j; rcases h j with ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  -- 5. Measurability: R.toSet and S are half-open rectangles, hence measurable
  have hR_meas : MeasurableSet R.toSet := by
    rw [hR_eq]
    exact measurableSet_half_open_rectangle R.left R.width
  have hS_meas : MeasurableSet S := by
    rw [hS_eq]
    exact measurableSet_half_open_rectangle
      (fun j => R.left j - γ) (fun j => R.width j + 2 * γ)
  have h_vol_S_fin : volume S ≠ ⊤ := by
    rw [hS_eq]
    exact volume_half_open_rectangle_ne_top
      (fun j => R.left j - γ) (fun j => R.width j + 2 * γ)
  have h_vol_R_fin : volume R.toSet ≠ ⊤ := by
    rw [hR_eq]
    exact volume_half_open_rectangle_ne_top R.left R.width
  --    Indicator functions of sets with finite measure are integrable.
  have h_int_S_ind : Integrable (S.indicator (fun _ => (1 : ℝ))) volume := by
    rw [integrable_indicator_iff hS_meas]
    exact integrableOn_const (C := (1 : ℝ)) (by simpa using h_vol_S_fin)
  have h_int_R_ind : Integrable (R.toSet.indicator (fun _ => (1 : ℝ))) volume := by
    rw [integrable_indicator_iff hR_meas]
    exact integrableOn_const (C := (1 : ℝ)) (by simpa using h_vol_R_fin)
  -- Difference of integrable indicators is integrable
  have h_int_right :
      Integrable
        (fun x => (S.indicator (fun _ => (1 : ℝ)) x : ℝ) -
          (R.toSet.indicator (fun _ => (1 : ℝ)) x : ℝ)) volume :=
    Integrable.sub h_int_S_ind h_int_R_ind
  -- Indicator difference is nonnegative (since R ⊆ S)
  have h_nonneg_diff (x : EuclideanSpace ℝ (Fin d)) :
      0 ≤ (S.indicator (fun _ => (1 : ℝ)) x : ℝ) -
        (R.toSet.indicator (fun _ => (1 : ℝ)) x : ℝ) := by
    have h := indicator_mono h_sub x
    linarith
  -- The absolute error function is integrable:
  -- it is measurable, nonnegative, and bounded pointwise by the integrable function above.
  have h_int_left :
      Integrable
        (fun x => |rectIndicatorNet R γ x - R.toSet.indicator (fun _ => (1 : ℝ)) x|)
        volume := by
    have h_meas :
        AEStronglyMeasurable
          (fun x => |rectIndicatorNet R γ x - R.toSet.indicator (fun _ => (1 : ℝ)) x|)
          volume :=
      continuous_abs.comp_aestronglyMeasurable
        (AEStronglyMeasurable.sub
          (rectIndicatorNet_continuous.aestronglyMeasurable)
          ((aestronglyMeasurable_const (β := ℝ)).indicator hR_meas))
    have h_bound_norm : ∀ᵐ x ∂volume,
        ‖|rectIndicatorNet R γ x - R.toSet.indicator (fun _ => (1 : ℝ)) x|‖ ≤
        ‖(S.indicator (fun _ => (1 : ℝ)) x : ℝ) -
          (R.toSet.indicator (fun _ => (1 : ℝ)) x : ℝ)‖ := by
      filter_upwards with x
      have h_nonneg_d := h_nonneg_diff x
      rw [Real.norm_of_nonneg (abs_nonneg _), Real.norm_of_nonneg h_nonneg_d]
      exact h_pointwise x
    exact ⟨h_meas, h_int_right.hasFiniteIntegral.mono h_bound_norm⟩
  have h_vol_S : volume.real S = ∏ j, (R.width j + 2 * γ) := by
    have hw_pos : ∀ j, 0 < R.width j + 2 * γ := by
      intro j; have := R.width_pos j; linarith
    rw [hS_eq]
    apply volume_half_open_rectangle_eq_prod
      (fun j => R.left j - γ) (fun j => R.width j + 2 * γ) hw_pos
  have h_vol_R : volume.real R.toSet = ∏ j, R.width j := by
    rw [hR_eq]
    apply volume_half_open_rectangle_eq_prod R.left R.width R.width_pos
  calc
    ∫ x, |rectIndicatorNet R γ x - R.toSet.indicator (fun _ => (1 : ℝ)) x| ≤
        ∫ x, ((S.indicator (fun _ => (1 : ℝ)) x : ℝ) -
          (R.toSet.indicator (fun _ => (1 : ℝ)) x : ℝ)) :=
        integral_mono h_int_left h_int_right h_pointwise
    _ = (∫ x, S.indicator (fun _ => (1 : ℝ)) x) - (∫ x, R.toSet.indicator (fun _ => (1 : ℝ)) x) :=
        integral_sub h_int_S_ind h_int_R_ind
    _ = volume.real S - volume.real R.toSet := by
        change (∫ x, S.indicator 1 x) - (∫ x, R.toSet.indicator 1 x) = _
        rw [integral_indicator_one hS_meas, integral_indicator_one hR_meas]
    _ = (∏ j : Fin d, (R.width j + 2 * γ)) - (∏ j : Fin d, R.width j) := by rw [h_vol_S, h_vol_R]

/-! ### Unit cube and partition construction -/

/-- The half-open unit cube [0,1)ᵈ in ℝᵈ. -/
def unitCube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ j, (0 : ℝ) ≤ x j ∧ x j < 1}

/-- The unit cube is measurable. -/
lemma measurableSet_unitCube : MeasurableSet (unitCube d) := by
  dsimp [unitCube]
  have h_proj (j : Fin d) : Measurable (fun x : EuclideanSpace ℝ (Fin d) => x j) := by
    have : (fun x : EuclideanSpace ℝ (Fin d) => x j) =
        (fun f : Fin d → ℝ => f j) ∘ (@WithLp.ofLp 2 (Fin d → ℝ)) := rfl
    rw [this]
    exact (measurable_pi_apply j).comp (WithLp.measurable_ofLp 2 _)
  have : {x | ∀ j, (0 : ℝ) ≤ x j ∧ x j < 1} = ⋂ j : Fin d,
      {x : EuclideanSpace ℝ (Fin d) | (0 : ℝ) ≤ x j} ∩
      {x : EuclideanSpace ℝ (Fin d) | x j < 1} := by
    ext x; simp
  rw [this]
  refine MeasurableSet.iInter fun j => ?_
  refine (measurableSet_le measurable_const (h_proj j)).inter ?_
  exact measurableSet_lt (h_proj j) measurable_const

/-- Volume of the unit cube is 1: it is the half-open rectangle with left `0`, width `1`. -/
lemma volume_unitCube : volume.real (unitCube d) = 1 := by
  have key := volume_half_open_rectangle_eq_prod (d := d)
    (fun _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun _ => zero_lt_one)
  have h_eq : {x : EuclideanSpace ℝ (Fin d) |
      ∀ j, (fun _ => (0 : ℝ)) j ≤ x j ∧ x j < (fun _ => (0 : ℝ)) j + (fun _ => (1 : ℝ)) j}
      = unitCube d := by
    ext x; simp only [unitCube, Set.mem_ofPred_eq, zero_add]
  rw [h_eq] at key
  rw [key]; simp

-- For w ≥ 0 and natural numbers a < b, we have (a+1)*w ≤ b*w.
-- This is used to show adjacent grid intervals are disjoint.
private lemma nat_succ_mul_le_of_lt {w : ℝ} (hw_nonneg : 0 ≤ w) {a b : ℕ} (h_lt : a < b) :
    ((a : ℝ) + 1) * w ≤ (b : ℝ) * w := by
  have h_succ_le : (a : ℕ) + 1 ≤ b := Nat.succ_le_of_lt h_lt
  have h_cast : ((a : ℕ) + 1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast h_succ_le
  nlinarith

-- For w > 0 and a ≠ b, the half-open intervals [a*w, (a+1)*w) and [b*w, (b+1)*w) are disjoint.
-- This is the key geometric fact behind the grid rectangle disjointness.
private lemma grid_interval_disjoint {w : ℝ} (hw_pos : 0 < w) (a b : ℕ) (h_ne : a ≠ b) (x : ℝ) :
    ¬(((a : ℝ) * w ≤ x ∧ x < (a : ℝ) * w + w) ∧ ((b : ℝ) * w ≤ x ∧ x < (b : ℝ) * w + w)) := by
  have h_order : a < b ∨ b < a := Nat.lt_or_gt_of_ne h_ne
  rintro ⟨⟨hxl₁, hxr₁⟩, ⟨hxl₂, hxr₂⟩⟩
  rcases h_order with (h_lt | h_lt)
  · have h_ineq : (a : ℝ) * w + w ≤ (b : ℝ) * w := by
      calc
        (a : ℝ) * w + w = ((a : ℝ) + 1) * w := by ring
        _ ≤ (b : ℝ) * w := nat_succ_mul_le_of_lt (le_of_lt hw_pos) h_lt
    nlinarith
  · have h_ineq : (b : ℝ) * w + w ≤ (a : ℝ) * w := by
      calc
        (b : ℝ) * w + w = ((b : ℝ) + 1) * w := by ring
        _ ≤ (a : ℝ) * w := nat_succ_mul_le_of_lt (le_of_lt hw_pos) h_lt
    nlinarith

/-- There exists a δ-fine rectangle partition of the unit cube.
    This is the standard grid construction: subdivide each coordinate
    into intervals of length ≤ δ. -/
lemma exists_unitCube_partition {δ : ℝ} (hδ : 0 < δ) :
    ∃ _P : RectanglePartition d (unitCube d) δ, True := by
  rcases exists_nat_one_div_lt hδ with ⟨n, hn⟩
  have h_denom_ne_zero : (n : ℝ) + 1 ≠ 0 := by nlinarith
  set w := 1 / ((n : ℝ) + 1) with hw_def
  have hw_pos' : 0 < w := by
    rw [hw_def]
    exact div_pos (by norm_num)
      (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (by norm_num))
  have hw_le_δ : w ≤ δ := le_of_lt hn
  classical
    let rect (k : Fin d → Fin (n+1)) : Rectangle d := {
      left := (EuclideanSpace.equiv (Fin d) ℝ).symm (fun j => ((k j : ℕ) : ℝ) * w)
      width := (EuclideanSpace.equiv (Fin d) ℝ).symm (fun _ => w)
      width_pos := by
        intro j; dsimp; exact hw_pos'
    }
    let idx : Finset (Fin d → Fin (n+1)) :=
      Fintype.piFinset fun (_ : Fin d) => Finset.univ
    let rects : Finset (Rectangle d) := idx.image rect
    have h_cover : ∀ x ∈ unitCube d, ∃ R ∈ rects, x ∈ R.toSet := by
      intro x hx
      let k (j : Fin d) : Fin (n+1) :=
        have h_mul_nonneg : 0 ≤ ((n : ℝ) + 1) * x j := by nlinarith [(hx j).1]
        have h_mul_lt : ((n : ℝ) + 1) * x j < (n : ℝ) + 1 := by
          nlinarith [(hx j).2]
        have h_mul_lt' : ((n : ℝ) + 1) * x j < ((n + 1 : ℕ) : ℝ) := by
          simpa [Nat.cast_add] using h_mul_lt
        have h_floor_lt : ⌊((n : ℝ) + 1) * x j⌋₊ < n + 1 :=
          ((Nat.floor_lt h_mul_nonneg).mpr h_mul_lt')
        ⟨⌊((n : ℝ) + 1) * x j⌋₊, h_floor_lt⟩
      have h_mem_toSet : x ∈ (rect k).toSet := by
        dsimp [Rectangle.toSet, rect]
        intro j
        have h_floor_val_le : (⌊((n : ℝ) + 1) * x j⌋₊ : ℝ) ≤ ((n : ℝ) + 1) * x j :=
          Nat.floor_le (by nlinarith [(hx j).1])
        have h_lt_floor_add_one : ((n : ℝ) + 1) * x j < (⌊((n : ℝ) + 1) * x j⌋₊ : ℝ) + 1 :=
          Nat.lt_floor_add_one _
        have h_left : ((⌊((n : ℝ) + 1) * x j⌋₊ : ℕ) : ℝ) * w ≤ x j := by
          calc
            ((⌊((n : ℝ) + 1) * x j⌋₊ : ℕ) : ℝ) * w =
                ((⌊((n : ℝ) + 1) * x j⌋₊ : ℕ) : ℝ) / ((n : ℝ) + 1) := by dsimp [w]; ring
            _ ≤ (((n : ℝ) + 1) * x j) / ((n : ℝ) + 1) := by gcongr
            _ = x j := by field_simp [h_denom_ne_zero]
        have h_right : x j < (((⌊((n : ℝ) + 1) * x j⌋₊ : ℕ) : ℝ) + 1) * w := by
          calc
            x j = (((n : ℝ) + 1) * x j) / ((n : ℝ) + 1) := by field_simp [h_denom_ne_zero]
            _ < ((⌊((n : ℝ) + 1) * x j⌋₊ : ℝ) + 1) / ((n : ℝ) + 1) := by gcongr
            _ = (((⌊((n : ℝ) + 1) * x j⌋₊ : ℕ) : ℝ) + 1) * w := by dsimp [w]; ring
        -- Goal is: ((k j : ℕ) : ℝ) * w ≤ x j ∧ x j < ((k j : ℕ) : ℝ) * w + w
        -- We have h_left/h_right in terms of ⌊...⌋₊; unfold k to rewrite
        constructor
        · dsimp [k]; exact h_left
        · dsimp [k]
          calc
            x j < (((⌊((n : ℝ) + 1) * x j⌋₊ : ℕ) : ℝ) + 1) * w := h_right
            _ = ((⌊((n : ℝ) + 1) * x j⌋₊ : ℕ) : ℝ) * w + w := by ring
      have h_rect_mem : rect k ∈ rects := by
        dsimp [rects]; exact Finset.mem_image.mpr ⟨k, by simp [idx], rfl⟩
      exact ⟨rect k, h_rect_mem, h_mem_toSet⟩
    have h_disjoint : ∀ R₁ ∈ rects, ∀ R₂ ∈ rects, R₁ ≠ R₂ → R₁.toSet ∩ R₂.toSet = ∅ := by
      intro R₁ hR₁ R₂ hR₂ h_ne
      dsimp [rects] at hR₁ hR₂
      rcases Finset.mem_image.mp hR₁ with ⟨k₁, hk₁, rfl⟩
      rcases Finset.mem_image.mp hR₂ with ⟨k₂, hk₂, rfl⟩
      have hk_ne : k₁ ≠ k₂ := by
        intro h_eq; apply h_ne; rw [h_eq]
      have h_exists_j : ∃ j, (k₁ j : ℕ) ≠ (k₂ j : ℕ) := by
        by_contra! h_all_eq
        apply hk_ne
        funext j; exact Fin.ext (h_all_eq j)
      rcases h_exists_j with ⟨j, hj⟩
      ext x; constructor
      · intro hx
        rcases hx with ⟨hx₁, hx₂⟩
        rcases hx₁ j with ⟨hxl₁, hxr₁⟩; rcases hx₂ j with ⟨hxl₂, hxr₂⟩
        exfalso
        exact grid_interval_disjoint hw_pos' (k₁ j) (k₂ j) hj (x j) ⟨⟨hxl₁, hxr₁⟩, ⟨hxl₂, hxr₂⟩⟩
      · simp
    have h_fine : ∀ R ∈ rects, R.isFine δ := by
      intro R hR
      dsimp [rects] at hR
      rcases Finset.mem_image.mp hR with ⟨k, hk, rfl⟩
      dsimp [Rectangle.isFine]
      intro j
      simpa [rect] using hw_le_δ
    refine ⟨{
      rectangles := rects
      cover := h_cover
      disjoint := h_disjoint
      fine := h_fine
    }, trivial⟩

/-! ### Representability of rectIndicatorNet as a two-hidden-layer network -/

/-- A single rectIndicatorNet is representable as a two-hidden-layer ReLU network
    with hidden widths m₁ = 4*d (the inner softStep components) and m₂ = 1. -/
lemma rectIndicatorNet_mem_FunctionClass {R : Rectangle d} {γ : ℝ} :
    ∃ m₁ : ℕ, rectIndicatorNet R γ ∈ TwoHiddenLayer.FunctionClass reluActivation d m₁ 1 := by
  -- Construct a TwoHiddenLayer.Network that computes rectIndicatorNet.
  -- The first layer has 4*d neurons: for each coordinate j, four neurons
  -- computing relu((x_j - c)/γ) for c = a-γ, a, b, b+γ.
  -- The second layer has 1 neuron computing relu(sum - (d-1)).
  sorry

/-- A finite linear combination of rectIndicatorNet functions is representable
    as a two-hidden-layer ReLU network. The hidden widths are m₁ = sum of individual
    first-layer widths, m₂ = number of rectangles. -/
lemma sum_rectIndicatorNet_mem_FunctionClass {ι : Type*} [Fintype ι]
    (R : ι → Rectangle d) (γ : ℝ) (α : ι → ℝ) :
    ∃ m₁ m₂ : ℕ, (fun x => ∑ i : ι, α i * rectIndicatorNet (R i) γ x) ∈
      TwoHiddenLayer.FunctionClass reluActivation d m₁ m₂ := by
  -- Concatenate the networks for each rectIndicatorNet.
  -- First layer: take disjoint union of first layers (size = sum of individual m₁'s).
  -- Second layer: one neuron per rectangle, each computing its own rectIndicatorNet.
  -- Output coefficients: α i.
  sorry

/-! ### Main theorem: multivariate folklore bound (Theorem 2.1) -/
/-- Theorem 2.1: for continuous g with modulus ε at scale δ, there is a 3-layer ReLU network
    with Ω(1/δᵈ) nodes achieving L¹-error ≤ 2ε on [0,1]ᵈ.

    The network is constructed as f = ∑ᵢ αᵢ · gγ(·; Rᵢ) where the Rᵢ partition [0,1)ᵈ. -/
theorem folkloreBound {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (g : (EuclideanSpace ℝ (Fin d)) → ℝ) (hg : Continuous g)
    (hω : uniformModulus g δ ≤ (ε : WithTop ℝ)) :
    ∃ (f : (EuclideanSpace ℝ (Fin d)) → ℝ) (m₁ m₂ : ℕ),
      f ∈ TwoHiddenLayer.FunctionClass reluActivation d m₁ m₂ ∧
      ∫ x in unitCube d, |f x - g x| ≤ 2 * ε := by
  -- Step 1: Obtain a δ-fine partition of the unit cube
  rcases exists_unitCube_partition hδ with ⟨P, _⟩
  -- Step 2: Let h be the piecewise constant approximation of g on this partition.
  -- By piecewiseConstApprox_error, |h(x) - g(x)| ≤ ε pointwise on the unit cube.
  set h := piecewiseConstApprox g P with hh_def
  have h_error : ∀ x ∈ unitCube d, |h x - g x| ≤ ε :=
    piecewiseConstApprox_error g P hω
  -- Step 3: Choose γ > 0 small enough so that the total L¹ error from approximating
  -- each rectangle indicator by its rectIndicatorNet is at most ε.
  -- For each rectangle R, rectIndicatorNet_L1_error bounds the L¹ error by
  -- (∏(w_j + 2γ)) - (∏ w_j). Since w_j ≤ δ, we can make this arbitrarily small.
  -- Standard argument: take γ small enough; the polynomial ∏(w_j + 2γ) - ∏ w_j
  -- has no constant term, so it → 0 as γ → 0.
  have h_exists_γ : ∃ γ, 0 < γ ∧
      (∑ R ∈ P.rectangles, |g (representative R)| *
        ((∏ j : Fin d, (R.width j + 2 * γ)) - ∏ j : Fin d, R.width j)) ≤ ε := by
    -- Because g is continuous on the compact closure of the unit cube, it attains a maximum M.
    -- Let M := sup_{x ∈ unitCube d} |g(x)| (finite by compactness).
    -- For each rectangle R, width_j ≤ δ, so the product gap is ≤ C * γ
    -- for some C depending on δ and d.
    -- Choose γ ≤ ε / (|P| · M · C).
    sorry
  rcases h_exists_γ with ⟨γ, hγ, hγ_sum⟩
  -- Step 4: Define f as the linear combination of rectIndicatorNet functions.
  -- f(x) = Σ_R g(representative R) · gγ_R(x)
  set f := (fun x => ∑ R ∈ P.rectangles, g (representative R) * rectIndicatorNet R γ x) with hf_def
  -- Step 5: Show f is in TwoHiddenLayer.FunctionClass
  have h_f_mem : ∃ m₁ m₂ : ℕ, f ∈ TwoHiddenLayer.FunctionClass reluActivation d m₁ m₂ := by
    -- Use the lemma sum_rectIndicatorNet_mem_FunctionClass,
    -- converting the Finset sum to a sum over a Fintype.
    -- Let ι := P.rectangles (which is a Finset).
    -- Use: ∑_{R ∈ s} φ(R) = ∑_{i : s} φ(i)
    sorry
  rcases h_f_mem with ⟨m₁, m₂, h_f_mem'⟩
  -- Step 6: Bound the L¹ error ∫_{unitCube} |f - g| ≤ 2ε.
  -- Triangle inequality: |f - g| ≤ |f - h| + |h - g|, then split the integral.
  have h_integral : ∫ x in unitCube d, |f x - g x| ≤ 2 * ε := by
    -- Pointwise triangle inequality through the intermediate piecewise-constant h.
    have h_tri : ∀ x, |f x - g x| ≤ |f x - h x| + |h x - g x| := by
      intro x
      exact abs_sub_le (f x) (h x) (g x)
    -- Integrability witnesses: on the finite-measure cube, each integrand is bounded/measurable.
    -- (These use finiteness of `volume (unitCube d)`; they FAIL over all of ℝᵈ — see docs.)
    have hInt_fg : IntegrableOn (fun x => |f x - g x|) (unitCube d) volume := by
      sorry
    have hInt_fh : IntegrableOn (fun x => |f x - h x|) (unitCube d) volume := by
      sorry
    have hInt_hg : IntegrableOn (fun x => |h x - g x|) (unitCube d) volume := by
      sorry
    calc
      ∫ x in unitCube d, |f x - g x|
          ≤ ∫ x in unitCube d, (|f x - h x| + |h x - g x|) :=
            setIntegral_mono_on hInt_fg (hInt_fh.add hInt_hg) measurableSet_unitCube
              (fun x _ => h_tri x)
      _ = (∫ x in unitCube d, |f x - h x|) + (∫ x in unitCube d, |h x - g x|) :=
            integral_add hInt_fh hInt_hg
      _ ≤ ε + ε := by
            apply add_le_add
            · -- ∫ |f - h| ≤ ε: expand f - h as a rectangle sum and use hγ_sum.
              sorry
            · -- ∫ |h - g| ≤ ε : |h - g| ≤ ε on the cube (h_error) and volume (unitCube) = 1
              sorry
      _ = 2 * ε := by ring
  exact ⟨f, m₁, m₂, h_f_mem', h_integral⟩

end Approximation.Multivariate

end
