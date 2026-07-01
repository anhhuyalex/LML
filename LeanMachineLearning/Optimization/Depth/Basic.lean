/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Approximation.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Real.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# The Δ mapping and its iterated composition (Section 5.1)

This file defines the fundamental building block `Δ` for depth-separation results
(Chapter 5, Telgarsky 2021).

`Δ : ℝ → ℝ` is the piecewise-affine "tent" function:
```
Δ(x) = 2σ(x) − 4σ(x − 1/2) + 2σ(x − 1)
      = 2x        if x ∈ [0, 1/2)
        2 − 2x    if x ∈ [1/2, 1)
        0         otherwise
```
where σ is the ReLU activation.

The key property (Proposition 5.1) is that the L-fold composition Δ^L satisfies
```
Δ^L(x) = Δ(⟨2^{L-1} x⟩)
```
where ⟨·⟩ denotes the fractional part. This means Δ^L has exactly 2^{L-1} uniformly
spaced copies of Δ on [0,1], so its complexity grows *exponentially* in L while the
network size is only O(L).

## Main definitions

* `deltaTent` : the tent function Δ
* `deltaTentIter L` : the L-fold composition Δ^L
* `fractionalPart` : x ↦ x − ⌊x⌋

## Main results

* `deltaTent_eq` : pointwise formula for Δ on the three regions
* `deltaTentIter_eq` : Proposition 5.1 — Δ^L(x) = Δ(⟨2^{L-1} x⟩)
* `deltaTent_reflection` : Δ(z) = Δ(1 − z) for z ∈ [0, 1]

-/

@[expose] public section

open Real Int Finset Approximation

namespace Depth

/-! ### Basic building block: the Δ tent function -/

/-- The tent function Δ, defined via ReLU:
  Δ(x) = 2σ(x) − 4σ(x − 1/2) + 2σ(x − 1). -/
noncomputable def deltaTent (x : ℝ) : ℝ :=
  2 * reluActivation x - 4 * reluActivation (x - 1/2) + 2 * reluActivation (x - 1)

/-- The fractional part of a real number: ⟨x⟩ = x − ⌊x⌋. -/
noncomputable def fractionalPart (x : ℝ) : ℝ := x - ⌊x⌋

/-! ### Pointwise characterization of Δ -/

lemma deltaTent_of_Ico_left (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) (1/2)) :
    deltaTent x = 2 * x := by
  simp only [deltaTent, reluActivation]
  rcases Set.mem_Ico.mp hx with ⟨hx0, hx1⟩
  have h1 : max x 0 = x := max_eq_left hx0
  have h2 : max (x - 1/2) 0 = 0 := by
    apply max_eq_right
    linarith
  have h3 : max (x - 1) 0 = 0 := by
    apply max_eq_right
    linarith
  rw [h1, h2, h3]; ring

lemma deltaTent_of_Ico_right (x : ℝ) (hx : x ∈ Set.Ico (1/2 : ℝ) 1) :
    deltaTent x = 2 - 2 * x := by
  simp only [deltaTent, reluActivation]
  rcases Set.mem_Ico.mp hx with ⟨hx1, hx2⟩
  have h1 : max x 0 = x := max_eq_left (le_trans (by norm_num : (0 : ℝ) ≤ 1/2) hx1)
  have h2 : max (x - 1/2) 0 = x - 1/2 := by
    apply max_eq_left; linarith
  have h3 : max (x - 1) 0 = 0 := by
    apply max_eq_right; linarith
  rw [h1, h2, h3]; ring

lemma deltaTent_of_outside (x : ℝ) (hx : x ∉ Set.Ico (0 : ℝ) 1) :
    deltaTent x = 0 := by
  simp only [deltaTent, reluActivation]
  rw [Set.mem_Ico, not_and_or] at hx
  by_cases h : x < 0
  · have h1 : max x 0 = 0 := max_eq_right (le_of_lt h)
    have h2 : max (x - 1/2) 0 = 0 := max_eq_right (by linarith)
    have h3 : max (x - 1) 0 = 0 := max_eq_right (by linarith)
    rw [h1, h2, h3]; ring
  · have hge : x ≥ 1 := by
      rcases hx with (hx0 | hx1)
      · exact absurd (le_of_not_gt h) hx0
      · exact by linarith
    have h1 : max x 0 = x := max_eq_left (le_of_not_gt h)
    have h2 : max (x - 1/2) 0 = x - 1/2 := max_eq_left (by linarith)
    have h3 : max (x - 1) 0 = x - 1 := max_eq_left (by linarith)
    rw [h1, h2, h3]; ring

/-- Δ takes values in [0, 1] on [0, 1]. -/
lemma deltaTent_nonneg (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ deltaTent x := by
  rcases Set.mem_Icc.mp hx with ⟨hx0, hx1⟩
  by_cases hx_lt_half : x < 1/2
  · rw [deltaTent_of_Ico_left x ⟨hx0, hx_lt_half⟩]
    nlinarith
  · by_cases hx_eq_one : x = 1
    · rw [hx_eq_one]
      simp [deltaTent, reluActivation]
      norm_num
    · have hx_lt_one : x < 1 := by
        by_contra! H
        exact hx_eq_one (by linarith)
      rw [deltaTent_of_Ico_right x ⟨by linarith, hx_lt_one⟩]
      nlinarith

/-- Δ(z) = Δ(1 − z) for z ∈ [0, 1] (reflection symmetry). -/
lemma deltaTent_reflection (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    deltaTent z = deltaTent (1 - z) := by
  rcases Set.mem_Icc.mp hz with ⟨hz0, hz1⟩
  by_cases hz_lt_half : z < 1/2
  · by_cases hz_eq_zero : z = 0
    · rw [hz_eq_zero]
      simp [deltaTent, reluActivation]
      norm_num
    · have hz_pos : 0 < z := by
        by_contra! H
        exact hz_eq_zero (by linarith)
      have hz_Ico : z ∈ Set.Ico (0 : ℝ) (1/2) := ⟨hz0, hz_lt_half⟩
      have h1z_Ico : (1 - z) ∈ Set.Ico (1/2 : ℝ) 1 := by
        constructor
        · linarith
        · have : 1 - z < 1 := by linarith
          exact this
      rw [deltaTent_of_Ico_left z hz_Ico, deltaTent_of_Ico_right (1 - z) h1z_Ico]
      ring
  · by_cases hz_eq_half : z = 1/2
    · rw [hz_eq_half]
      simp [deltaTent, reluActivation]
      norm_num
    · have hz_gt_half : 1/2 < z := by
        by_contra! H
        exact hz_eq_half (by linarith)
      by_cases hz_eq_one : z = 1
      · rw [hz_eq_one]
        simp [deltaTent, reluActivation]
        norm_num
      · have hz_lt_one : z < 1 := by
          by_contra! H
          exact hz_eq_one (by linarith)
        have hz_Ico : z ∈ Set.Ico (1/2 : ℝ) 1 := ⟨by linarith, hz_lt_one⟩
        have h1z_lt_half : 1 - z < 1/2 := by linarith
        have h1z_nonneg : 0 ≤ 1 - z := by linarith
        have h1z_Ico : (1 - z) ∈ Set.Ico (0 : ℝ) (1/2) := ⟨h1z_nonneg, h1z_lt_half⟩
        rw [deltaTent_of_Ico_right z hz_Ico, deltaTent_of_Ico_left (1 - z) h1z_Ico]
        ring

/-! ### Iterated composition Δ^L -/

/-- The L-fold composition of Δ with itself. -/
noncomputable def deltaTentIter : ℕ → ℝ → ℝ
  | 0     => id
  | (L+1) => deltaTent ∘ deltaTentIter L

lemma deltaTentIter_zero : deltaTentIter 0 = id := rfl

lemma deltaTentIter_succ (L : ℕ) (x : ℝ) :
    deltaTentIter (L + 1) x = deltaTent (deltaTentIter L x) := rfl

/-- Helper lemma: compute deltaTent for any x ∈ [0,1] with a case split on x = 1. -/
lemma deltaTent_of_Icc (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : deltaTent x = if x < 1/2 then 2*x else 2 - 2*x := by
  rcases Set.mem_Icc.mp hx with ⟨hx0, hx1⟩
  by_cases hx_lt_half : x < 1/2
  · rw [deltaTent_of_Ico_left x ⟨hx0, hx_lt_half⟩]
    rw [if_pos hx_lt_half]
  · have hx_ge_half : 1/2 ≤ x := by linarith
    by_cases hx_eq_one : x = 1
    · rw [hx_eq_one]
      simp [deltaTent, reluActivation]
      norm_num
    · have hx_lt_one : x < 1 := by
        by_contra! H; exact hx_eq_one (by linarith)
      rw [deltaTent_of_Ico_right x ⟨hx_ge_half, hx_lt_one⟩]
      rw [if_neg (by linarith : ¬ (x < 1/2))]

/-- Key identity: Δ(Δ(t)) = Δ(⟨2t⟩) for t ∈ [0,1). -/
lemma deltaTent_twice_eq (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    deltaTent (deltaTent t) = deltaTent (fractionalPart (2 * t)) := by
  rcases Set.mem_Ico.mp ht with ⟨ht0, ht1⟩
  by_cases ht_half : t < 1/2
  · -- t ∈ [0, 1/2): Δ(t) = 2t
    have h_dt : deltaTent t = 2 * t := deltaTent_of_Ico_left t ⟨ht0, ht_half⟩
    rw [h_dt]
    have h2t_nonneg : 0 ≤ 2*t := by nlinarith
    have h2t_lt_one : 2*t < 1 := by nlinarith
    have h_floor : ⌊2*t⌋ = (0 : ℤ) := by
      rw [Int.floor_eq_zero_iff]
      exact ⟨h2t_nonneg, h2t_lt_one⟩
    simp [fractionalPart, h_floor]
  · -- t ∈ [1/2, 1): Δ(t) = 2-2t
    have hge_half : 1/2 ≤ t := by linarith
    have h_dt : deltaTent t = 2 - 2*t :=
      deltaTent_of_Ico_right t ⟨hge_half, ht1⟩
    rw [h_dt]
    have h_floor : ⌊2*t⌋ = (1 : ℤ) := by
      rw [Int.floor_eq_iff]
      constructor
      · push_cast; nlinarith
      · push_cast; nlinarith
    -- Now need δ(2-2t) = δ(2t-1) for t ∈ [1/2, 1)
    -- Both 2-2t and 2t-1 are in [0,1]
    have h_2t_d : (2-2*t) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> nlinarith
    have h_fp : (2*t - 1) ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> nlinarith
    have h_fp_val : fractionalPart (2*t) = 2*t - 1 := by
      unfold fractionalPart
      simp [h_floor]
    rw [h_fp_val]
    rw [deltaTent_of_Icc (2-2*t) h_2t_d, deltaTent_of_Icc (2*t - 1) h_fp]
    by_cases h_t_three_fourths : 2*t - 1 = 1/2
    · -- t = 3/4: direct computation
      have h_t_val : t = 3/4 := by linarith
      rw [h_t_val]; norm_num
    · by_cases h2t_sub_one_half : 2*t - 1 < 1/2
      · -- 2t-1 ∈ [0, 1/2): δ(2t-1) = 2(2t-1) = 4t-2
        -- 2-2t ∈ (1/2, 1]: δ(2-2t) = 2-2(2-2t) = 4t-2
        have h2t_d_cond : ¬ (2-2*t < 1/2) := by nlinarith
        rw [if_pos h2t_sub_one_half, if_neg h2t_d_cond]
        ring
      · -- 2t-1 ≥ 1/2 and 2t-1 ≠ 1/2, so 2t-1 > 1/2
        have h2t_sub_one_gt_half : 2*t - 1 > 1/2 := by
          by_contra! H; exact h_t_three_fourths (by linarith)
        -- 2-2t ∈ [0, 1/2): δ(2-2t) = 2(2-2t) = 4-4t
        -- 2t-1 ∈ (1/2, 1): δ(2t-1) = 2-2(2t-1) = 4-4t
        have h2t_d_cond : (2-2*t) < 1/2 := by nlinarith
        rw [if_neg (by linarith : ¬ (2*t - 1 < 1/2)), if_pos h2t_d_cond]
        ring

/-- Proposition 5.1: Δ^L(x) = Δ(⟨2^{L-1} x⟩) for all x ∈ [0,1].
  Here we state the version for L ≥ 1, so that 2^{L-1} makes sense. -/
theorem deltaTentIter_eq (L : ℕ) (hL : 1 ≤ L) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    deltaTentIter L x = deltaTent (fractionalPart (2^(L-1 : ℕ) * x)) := by
  rcases Set.mem_Icc.mp hx with ⟨hx0, hx1⟩
  induction L with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      -- L = 1 case: need Δ(x) = Δ(⟨x⟩) for x ∈ [0,1]
      -- Since x ∈ [0,1], ⌊x⌋ = 0 for x < 1, and ⌊1⌋ = 1 but Δ(1) = 0 = Δ(0) = Δ(⟨1⟩)
      -- so the equality holds in both cases.
      by_cases hx_lt_one : x < 1
      · have h_floor : ⌊x⌋ = (0 : ℤ) := by
          rw [Int.floor_eq_zero_iff]
          exact ⟨hx0, hx_lt_one⟩
        simp [deltaTentIter, fractionalPart, h_floor]
      · have hx_eq_one : x = 1 := by linarith
        rw [hx_eq_one]
        simp [deltaTentIter, fractionalPart, deltaTent, reluActivation]
        norm_num
    | succ m =>
      rw [deltaTentIter_succ]
      have hx' : deltaTentIter (m + 1) x = deltaTent (fractionalPart (2^(m : ℕ) * x)) :=
        ih (by omega)
      rw [hx']
      -- Need to show Δ(Δ(t)) = Δ(⟨2t⟩) where t = fractionalPart (2^m * x) ∈ [0,1)
      -- key identity: ⟨2*y⟩ = ⟨2*⟨y⟩⟩
      have h_fp_mul_two (y : ℝ) : fractionalPart (2 * y) = fractionalPart (2 * fractionalPart y) := by
        have h_fract_eq : ∀ (x : ℝ), fractionalPart x = Int.fract x := λ x => rfl
        calc
          fractionalPart (2 * y) = Int.fract (2 * y) := rfl
          _ = Int.fract (2 * (Int.fract y + (⌊y⌋ : ℝ))) := by
            simp [Int.fract_add_floor]
          _ = Int.fract (2 * Int.fract y + (2 * ⌊y⌋ : ℝ)) := by ring
          _ = Int.fract (2 * Int.fract y + (2 * ⌊y⌋ : ℤ)) := by push_cast; rfl
          _ = Int.fract (2 * Int.fract y) := by
            rw [Int.fract_add_intCast (2 * Int.fract y) (2 * ⌊y⌋)]
          _ = fractionalPart (2 * fractionalPart y) := rfl

      have ht : fractionalPart (2^(m : ℕ) * x) ∈ Set.Ico (0 : ℝ) 1 := by
        have h_nonneg : 0 ≤ fractionalPart (2^(m : ℕ) * x) := sub_nonneg.mpr (Int.floor_le _)
        have h_lt_one : fractionalPart (2^(m : ℕ) * x) < 1 := by
          have := Int.lt_floor_add_one (2^(m : ℕ) * x)
          calc
            fractionalPart (2^(m : ℕ) * x) = (2^(m : ℕ) * x) - (⌊2^(m : ℕ) * x⌋ : ℝ) := rfl
            _ < ((⌊2^(m : ℕ) * x⌋ : ℝ) + 1) - (⌊2^(m : ℕ) * x⌋ : ℝ) := by nlinarith
            _ = 1 := by ring
        exact ⟨h_nonneg, h_lt_one⟩
      have h_comp : deltaTent (deltaTent (fractionalPart (2^(m : ℕ) * x))) =
          deltaTent (fractionalPart (2 ^ (m + 1) * x)) := by
        calc
          deltaTent (deltaTent (fractionalPart (2^(m : ℕ) * x)))
              = deltaTent (fractionalPart (2 * fractionalPart (2^(m : ℕ) * x))) := by
                apply deltaTent_twice_eq (fractionalPart (2^(m : ℕ) * x)) ht
          _ = deltaTent (fractionalPart (2 * (2^(m : ℕ) * x))) := by
            rw [h_fp_mul_two (2^(m : ℕ) * x)]
          _ = deltaTent (fractionalPart (2^(m+1 : ℕ) * x)) := by
            simp [pow_succ, mul_comm, mul_left_comm]
      rw [h_comp]
      -- (succ (succ m) - 1 : ℕ) = m+1 as Nat exponents
      have h_exp : (Nat.succ (Nat.succ m) - 1 : ℕ) = m+1 := by omega
      simp [h_exp]

/-- Δ^L has exactly 2^{L-1} uniformly-spaced copies of Δ on [0,1].
  (Informal consequence of Proposition 5.1.) -/
lemma deltaTentIter_copies (L : ℕ) (hL : 1 ≤ L) :
    ∀ k : Fin (2^(L-1 : ℕ)), ∀ x : ℝ,
      x ∈ Set.Icc ((k : ℝ) / 2^(L-1 : ℕ)) (((k : ℝ) + 1) / 2^(L-1 : ℕ)) →
      deltaTentIter L x = deltaTent (2^(L-1 : ℕ) * x - k) := by
  sorry

/-! ### ReLU network model -/

/-- A univariate ReLU network specified by layer widths (m₁, …, mL).
  Each node in layer i computes σ(aᵀh + b) where h is the output of layer i-1. -/
structure ReLUNetwork (L : ℕ) where
  /-- The network has at least one layer (L ≥ 1). -/
  hLpos : 0 < L
  /-- Width of each layer. -/
  widths : Fin L → ℕ
  /-- Weight parameters: weights[i][j][k] is the weight from node k of layer i-1 to node j of layer i. -/
  weights : ∀ (i : Fin L), Fin (widths i) → (Fin (if i.val = 0 then 1 else widths ⟨i.val - 1, by
    have hi : i.val < L := i.2
    exact Nat.lt_of_le_of_lt (Nat.sub_le i.val 1) hi
    ⟩)) → ℝ
  /-- Bias parameters. -/
  biases : ∀ (i : Fin L), Fin (widths i) → ℝ
  /-- Output layer: a linear combination of the last layer's outputs. -/
  outWeights : Fin (widths ⟨L - 1, Nat.sub_lt hLpos (by decide)⟩) → ℝ
  outBias : ℝ

/-- Total number of nodes in a ReLU network. -/
noncomputable def ReLUNetwork.totalNodes {L : ℕ} (net : ReLUNetwork L) : ℕ :=
  ∑ i, net.widths i

end Depth

end
