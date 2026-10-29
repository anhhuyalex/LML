/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-!
# Ratio comparison lemma

This file formalizes the elementary ratio bound (Talagrand, Lemma 1.7.14):
if `|A'| ≤ B'`, `0 < B'` and `1 ≤ B`, then `|A' / B' - A / B| ≤ |A - A'| + |B - B'|`.
-/

@[expose] public section

/-- A numerator bound and a positive lower bound on the absolute denominator bound a
quotient. The denominator itself may be negative. -/
theorem abs_div_le_div_of_le_abs {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {x D b δ : K}
    (hδ : 0 < δ) (hD : δ ≤ |D|) (hx : |x| ≤ b) : |x / D| ≤ b / δ := by
  rw [abs_div]
  exact div_le_div₀ ((abs_nonneg _).trans hx) hx hδ hD

/-- Dividing by a coefficient bounded below by `3/4` costs at most a factor `4/3`. -/
theorem abs_div_le_four_thirds {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {x D b : K} (hD : 3 / 4 ≤ D) (hx : |x| ≤ b) :
    |x / D| ≤ 4 / 3 * b :=
  (abs_div_le_div_of_le_abs (by norm_num) (hD.trans (le_abs_self D)) hx).trans_eq (by ring)

/-- A contraction coefficient in `[0,r]`, with `r<1`, gives a positive denominator
and a uniform bound for `a/(1-κ*a)` whenever `a` belongs to `[0,1]`. -/
theorem one_sub_mul_div_bounds {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {κ a r : K} (hκ0 : 0 ≤ κ) (hκr : κ ≤ r)
    (ha : a ∈ Set.Icc (0 : K) 1) (hr : r < 1) :
    1 - r ≤ 1 - κ * a ∧ 0 ≤ a / (1 - κ * a) ∧ a / (1 - κ * a) ≤ 1 / (1 - r) := by
  have hd : 1 - r ≤ 1 - κ * a := by
    nlinarith [mul_le_mul_of_nonneg_left ha.2 hκ0]
  have hp : 0 < 1 - r := by linarith
  have hD : 0 < 1 - κ * a := hp.trans_le hd
  refine ⟨hd, div_nonneg ha.1 hD.le, ?_⟩
  exact (div_le_div_of_nonneg_left ha.1 hp hd).trans
    (div_le_div_of_nonneg_right ha.2 hp.le)

/-- **Talagrand Lemma 1.7.14 (Ratio comparison lemma).**
If `|A'| ≤ B'`, `0 < B'` and `1 ≤ B`, then `|A' / B' - A / B| ≤ |A - A'| + |B - B'|`. -/
theorem abs_div_sub_div_le {A A' B B' : ℝ} (hA' : |A'| ≤ B') (hB' : 0 < B') (hB : 1 ≤ B) :
    |A' / B' - A / B| ≤ |A - A'| + |B - B'| := by
  have hB_pos : 0 < B := by linarith
  have hB_ne : B ≠ 0 := hB_pos.ne'
  have hB'_ne : B' ≠ 0 := hB'.ne'
  have h_id : A' / B' - A / B = (A' / B') * ((B - B') / B) + (A' - A) / B := by
    field_simp
    ring
  rw [h_id]
  refine (abs_add_le _ _).trans ?_
  have h_id2 : |(A' / B') * ((B - B') / B)| = (|A'| / B') * (|B - B'| / B) := by
    rw [abs_mul, abs_div, abs_div, abs_of_pos hB', abs_of_pos hB_pos]
  have h_id3 : |(A' - A) / B| = |A' - A| / B := by
    rw [abs_div, abs_of_pos hB_pos]
  rw [h_id2, h_id3]
  have h_ratio : |A'| / B' ≤ 1 := (div_le_one₀ hB').mpr hA'
  have h_term1 : (|A'| / B') * (|B - B'| / B) ≤ |B - B'| := by
    calc (|A'| / B') * (|B - B'| / B)
      _ ≤ 1 * (|B - B'| / B) := mul_le_mul_of_nonneg_right h_ratio (by positivity)
      _ = |B - B'| / B := one_mul _
      _ ≤ |B - B'| := div_le_self (abs_nonneg _) hB
  have h_term2 : |A' - A| / B ≤ |A - A'| := by
    rw [abs_sub_comm A' A]
    exact div_le_self (abs_nonneg _) hB
  linarith

/-- A generalized ratio comparison bound:
if `0 < B'`, `0 < B` and `|A / B| ≤ C`, then
`|A' / B' - A / B| ≤ (B')⁻¹ * (|A' - A| + C * |B' - B|)`. -/
theorem abs_div_sub_div_le_of_denom_ge {A A' B B' C : ℝ}
    (hB' : 0 < B') (hB : 0 < B) (hAB : |A / B| ≤ C) :
    |A' / B' - A / B| ≤ (B')⁻¹ * (|A' - A| + C * |B' - B|) := by
  have hB_ne : B ≠ 0 := hB.ne'
  have hB'_ne : B' ≠ 0 := hB'.ne'
  have h_id : A' / B' - A / B = (A' - A) / B' - (A / B) * ((B' - B) / B') := by
    field_simp
    ring
  rw [h_id]
  refine (abs_sub _ _).trans ?_
  simp only [abs_div, abs_mul, abs_of_pos hB']
  have h1 : |A| / |B| * (|B' - B| / B') ≤ C * (|B' - B| / B') := by
    rw [← abs_div]
    exact mul_le_mul_of_nonneg_right hAB (by positivity)
  calc |A' - A| / B' + |A| / |B| * (|B' - B| / B')
    _ ≤ |A' - A| / B' + C * (|B' - B| / B') := add_le_add_right h1 (|A' - A| / B')
    _ = (B')⁻¹ * (|A' - A| + C * |B' - B|) := by
      have : |A' - A| / B' + C * (|B' - B| / B') = (|A' - A| + C * |B' - B|) / B' := by ring
      rw [this, div_eq_inv_mul]
