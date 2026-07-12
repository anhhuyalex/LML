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

noncomputable instance : MeasureSpace (EuclideanSpace ℝ (Fin d)) where
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
    (g : (EuclideanSpace ℝ (Fin d)) → ℝ) (P : RectanglePartition d U δ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∑ R ∈ P.rectangles, g (representative R) * R.toSet.indicator 1 x

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
      ∑ R' ∈ P.rectangles, g (representative R') * R'.toSet.indicator 1 x 
        = g (representative R) * R.toSet.indicator 1 x := by
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
          rfl
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
    rw [max_eq_right h_div1.le, max_eq_right h_div2.le, max_eq_right h_div3.le, max_eq_right h_div4.le]
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
    simpa using (Finset.sum_erase_add (Finset.univ : Finset (Fin d))
      (fun k => softStep (R.left k) (R.left k + R.width k) γ (x k)) (Finset.mem_univ j)).symm
  -- The sum over all k is ≤ d-1 (since one term is 0 and all others ≤ 1).
  have h_total_le : (∑ k : Fin d, softStep (R.left k) (R.left k + R.width k) γ (x k)) ≤ (d : ℝ) - 1 := by
    rw [h_sum_split, h_softstep_zero, zero_add]
    calc
      (∑ k ∈ (Finset.univ.erase j),
          softStep (R.left k) (R.left k + R.width k) γ (x k))
          ≤ (∑ k ∈ (Finset.univ.erase j), (1 : ℝ)) :=
        Finset.sum_le_sum fun k hk => h_softstep_le_one k
      _ = (d : ℝ) - 1 := by
        have h_erase := Finset.sum_erase_add (Finset.univ : Finset (Fin d)) (fun _ => (1 : ℝ))
          (Finset.mem_univ j)
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
  have h_sum : (∑ j : Fin d, softStep (R.left j) (R.left j + R.width j) γ (x j)) ≤ (d : ℝ) := by
    calc
      (∑ j : Fin d, softStep (R.left j) (R.left j + R.width j) γ (x j))
          ≤ (∑ j : Fin d, (1 : ℝ)) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have h_ab : R.left j ≤ R.left j + R.width j := by
              have := R.width_pos j
              linarith
            exact softStep_le_one hγ h_ab
      _ = (d : ℝ) := by simp
  have h_arg : (∑ j : Fin d, softStep (R.left j) (R.left j + R.width j) γ (x j)) - (d - 1 : ℝ) ≤ 1 := by linarith
  exact max_le h_arg zero_le_one

/-- L¹ error between gγ and the indicator of R is O(γ). -/
lemma rectIndicatorNet_L1_error {R : Rectangle d} {γ : ℝ} (hγ : 0 < γ) :
    ∫ x, |rectIndicatorNet R γ x - R.toSet.indicator 1 x| ≤
    (∏ j : Fin d, (R.width j + 2 * γ)) - ∏ j : Fin d, R.width j := by
  /- We bound the integrand pointwise by the indicator of the expanded rectangle
     minus the indicator of R, then use the volume formula for half-open rectangles. -/
  -- 1. Define the γ-expanded rectangle
  set S : Set (EuclideanSpace ℝ (Fin d)) :=
    {x | ∀ j : Fin d, R.left j - γ ≤ x j ∧ x j < R.left j + R.width j + γ}
  
  -- 2. Basic inclusion: R ⊆ S
  have h_sub : R.toSet ⊆ S := by
    intro x hx
    rintro j
    rcases hx j with ⟨h_left, h_right⟩
    refine ⟨by linarith, by linarith⟩
  
  -- 3. rectIndicatorNet = 0 outside S
  have h_zero_outside (x : EuclideanSpace ℝ (Fin d)) (hx : x ∉ S) : rectIndicatorNet R γ x = 0 := by
    rw [Set.mem_setOf_eq] at hx
    -- hx: ¬ (∀ j, R.left j - γ ≤ x j ∧ x j < R.left j + R.width j + γ)
    -- Equivalent to: ∃ j, ¬ (R.left j - γ ≤ x j) ∨ ¬ (x j < R.left j + R.width j + γ)
    -- i.e., ∃ j, x j < R.left j - γ ∨ x j ≥ R.left j + R.width j + γ
    have h_exists : ∃ j : Fin d, x j < R.left j - γ ∨ x j ≥ R.left j + R.width j + γ := by
      by_contra! h  -- h: ∀ j, ¬ (x j < R.left j - γ ∨ x j ≥ R.left j + R.width j + γ)
      apply hx
      intro j
      have h_not_or := h j  -- ¬ (x j < R.left j - γ ∨ x j ≥ R.left j + R.width j + γ)
      -- From ¬ (A ∨ B) we get ¬ A ∧ ¬ B
      -- i.e., ¬ (x j < R.left j - γ) and ¬ (x j ≥ R.left j + R.width j + γ)
      -- So R.left j - γ ≤ x j and x j < R.left j + R.width j + γ
      constructor
      · -- R.left j - γ ≤ x j
        linarith
      · -- x j < R.left j + R.width j + γ
        linarith
    rcases h_exists with ⟨j, hj_left | hj_right⟩
    · -- x j < R.left j - γ
      exact rectIndicatorNet_zero hγ ⟨j, Or.inl hj_left⟩
    · -- x j ≥ R.left j + R.width j + γ
      exact rectIndicatorNet_zero hγ ⟨j, Or.inr hj_right⟩
  
  -- 4. Pointwise inequality
  have h_pointwise (x : EuclideanSpace ℝ (Fin d)) :
      |rectIndicatorNet R γ x - R.toSet.indicator 1 x| ≤
      (S.indicator 1 x : ℝ) - (R.toSet.indicator 1 x : ℝ) := by
    by_cases hxS : x ∈ S
    · by_cases hxR : x ∈ R.toSet
      · -- x ∈ R ⊆ S
        have h_rect_eq_one : rectIndicatorNet R γ x = 1 := rectIndicatorNet_one hγ hxR
        have h_ind_R : R.toSet.indicator 1 x = (1 : ℝ) := Set.indicator_of_mem hxR _
        have h_ind_S : S.indicator 1 x = (1 : ℝ) := Set.indicator_of_mem (h_sub hxR) _
        rw [h_rect_eq_one, h_ind_R, h_ind_S]
        simp
      · -- x ∈ S \ R
        have h_ind_R : R.toSet.indicator 1 x = (0 : ℝ) := Set.indicator_of_notMem hxR _
        have h_ind_S : S.indicator 1 x = (1 : ℝ) := Set.indicator_of_mem hxS _
        have h_nonneg : 0 ≤ rectIndicatorNet R γ x := rectIndicatorNet_nonneg x
        have h_le_one : rectIndicatorNet R γ x ≤ 1 := rectIndicatorNet_le_one hγ x
        rw [h_ind_R, h_ind_S]
        -- Goal: |rectIndicatorNet R γ x - 0| ≤ (1 : ℝ) - 0
        simp
        -- Goal: |rectIndicatorNet R γ x| ≤ 1
        rw [abs_of_nonneg h_nonneg]
        exact h_le_one
    · -- x ∉ S, so rectIndicatorNet = 0 and both indicators = 0
      have h_rect_eq_zero : rectIndicatorNet R γ x = 0 := h_zero_outside x hxS
      have h_ind_R : R.toSet.indicator 1 x = (0 : ℝ) :=
        Set.indicator_of_notMem (fun hxR => hxS (h_sub hxR)) _
      have h_ind_S : S.indicator 1 x = (0 : ℝ) := Set.indicator_of_notMem hxS _
      rw [h_rect_eq_zero, h_ind_R, h_ind_S]
      simp

  -- The remainder of the proof uses measure theory:
  -- 5. Measurability of R.toSet and S (finite intersection of half-open intervals).
  -- 6. Finiteness of volume(S) (bounded rectangle → finite Lebesgue measure).
  -- 7. Integrability of the absolute difference and the indicator difference.
  -- 8. Apply integral_mono to the pointwise inequality.
  -- 9. Split integral of difference via integral_sub.
  -- 10. Integral of indicator = volume.real via integral_indicator_one.
  -- 11. Volume of half-open rectangle = product of side lengths:
  --     use PiLp.volume_preserving_ofLp to transfer to (Fin d → ℝ),
  --     then Real.volume_pi_Ico_toReal.
  sorry

/-! ### Main theorem: multivariate folklore bound (Theorem 2.1) -/

/-- Theorem 2.1: for continuous g with modulus ε at scale δ, there is a 3-layer ReLU network
    with Ω(1/δᵈ) nodes achieving L¹-error ≤ 2ε on [0,1]ᵈ.

    The network is constructed as f = ∑ᵢ αᵢ · gγ(·; Rᵢ) where the Rᵢ partition [0,2)ᵈ. -/
theorem folkloreBound {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (g : (EuclideanSpace ℝ (Fin d)) → ℝ) (hg : Continuous g)
    (hω : uniformModulus g δ ≤ (ε : WithTop ℝ)) :
    ∃ (f : (EuclideanSpace ℝ (Fin d)) → ℝ),
      (∃ m₁ : ℕ, f ∈ TwoHiddenLayer.FunctionClass reluActivation d m₁ 1) ∧
      ∫ x : EuclideanSpace ℝ (Fin d), |f x - g x| ≤ 2 * ε := by
  sorry

end Approximation.Multivariate

end
