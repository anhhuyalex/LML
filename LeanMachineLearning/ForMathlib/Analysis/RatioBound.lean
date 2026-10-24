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
  have h_div_le_self : ∀ x : ℝ, 0 ≤ x → x / B ≤ x := fun x hx => by
    rw [div_le_iff₀ hB_pos]
    calc x = x * 1 := (mul_one x).symm
      _ ≤ x * B := mul_le_mul_of_nonneg_left hB hx
  have h_term1 : (|A'| / B') * (|B - B'| / B) ≤ |B - B'| := by
    calc (|A'| / B') * (|B - B'| / B)
      _ ≤ 1 * (|B - B'| / B) := mul_le_mul_of_nonneg_right h_ratio (by positivity)
      _ = |B - B'| / B := one_mul _
      _ ≤ |B - B'| := h_div_le_self _ (abs_nonneg _)
  have h_term2 : |A' - A| / B ≤ |A - A'| := by
    rw [abs_sub_comm A' A]
    exact h_div_le_self _ (abs_nonneg _)
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
