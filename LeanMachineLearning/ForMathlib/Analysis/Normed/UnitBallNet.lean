/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
# Finite nets of the unit ball and operator norms

The unit ball of a `d`-dimensional real normed space has a `1 / 2`-net of cardinality at most
`5 ^ d`, and the norm of a linear map into an inner product space is at most four times the largest
value of `|⟪b, T a⟫|` over two such nets (Talagrand, *Spin Glasses*, Vol. I, Appendix A.8).

## Main declarations

* `exists_finset_unitBall_net`: the net.
* `ContinuousLinearMap.opNorm_le_four_mul_of_net`: the operator norm bound.
-/

@[expose] public section

open Module Finset
open scoped RealInnerProductSpace

/-- **A `1 / 2`-net of the closed unit ball** of a `d`-dimensional real normed space with at most
`5 ^ d` points: a separated set of maximal cardinality. -/
theorem exists_finset_unitBall_net (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] :
    ∃ A : Finset V, (∀ a ∈ A, ‖a‖ ≤ 1) ∧ A.card ≤ 5 ^ finrank ℝ V ∧
      ∀ x : V, ‖x‖ ≤ 1 → ∃ a ∈ A, ‖x - a‖ ≤ 1 / 2 := by
  classical
  let sep : Finset V → Prop := fun A =>
    (∀ a ∈ A, ‖a‖ ≤ 1) ∧ ∀ a ∈ A, ∀ b ∈ A, a ≠ b → 1 / 2 ≤ ‖a - b‖
  have hcard : ∀ A, sep A → A.card ≤ 5 ^ finrank ℝ V := fun A hA => by
    have hinj : Function.Injective fun a : V => (2 : ℝ) • a :=
      smul_right_injective V two_ne_zero
    rw [← card_image_of_injective A hinj]
    refine Besicovitch.card_le_of_separated _ (fun c hc => ?_) fun c hc d hd hcd => ?_
    · obtain ⟨a, ha, rfl⟩ := mem_image.1 hc
      rw [norm_smul, Real.norm_two]
      linarith [hA.1 a ha]
    · obtain ⟨a, ha, rfl⟩ := mem_image.1 hc
      obtain ⟨b, hb, rfl⟩ := mem_image.1 hd
      rw [← smul_sub, norm_smul, Real.norm_two]
      linarith [hA.2 a ha b hb fun h => hcd (by rw [h])]
  set S : Finset ℕ := (range (5 ^ finrank ℝ V + 1)).filter fun n => ∃ A, sep A ∧ A.card = n
    with hS
  have hmem : ∀ A, sep A → A.card ∈ S := fun A hA =>
    mem_filter.2 ⟨mem_range.2 (Nat.lt_succ_of_le (hcard A hA)), A, hA, rfl⟩
  have hne : S.Nonempty := ⟨_, hmem ∅ ⟨by simp, by simp⟩⟩
  obtain ⟨-, A, hA, hAc⟩ := mem_filter.1 (S.max'_mem hne)
  refine ⟨A, hA.1, hcard A hA, fun x hx => ?_⟩
  by_contra h
  push Not at h
  replace h : ∀ a ∈ A, 1 / 2 < ‖x - a‖ := h
  have hxA : x ∉ A := fun hxA => by
    have := h x hxA
    rw [sub_self, norm_zero] at this
    norm_num at this
  have hins : sep (insert x A) := by
    refine ⟨fun a ha => ?_, fun a ha b hb hab => ?_⟩
    · rcases mem_insert.1 ha with rfl | ha
      exacts [hx, hA.1 a ha]
    · rcases mem_insert.1 ha with h1 | h1 <;> rcases mem_insert.1 hb with h2 | h2
      · exact absurd (h1.trans h2.symm) hab
      · rw [h1]; exact (h b h2).le
      · rw [h2, norm_sub_rev]; exact (h a h1).le
      · exact hA.2 a h1 b h2 hab
  have hle : (insert x A).card ≤ A.card := (S.le_max' _ (hmem _ hins)).trans_eq hAc.symm
  rw [card_insert_of_notMem hxA] at hle
  exact Nat.not_succ_le_self _ hle

/-- **Operator norm from two nets:** if every point of each unit ball is within `1 / 2` of the
set `A`, respectively `B`, and `|⟪b, T a⟫| ≤ S` for all `a ∈ A`, `b ∈ B`, then `‖T‖ ≤ 4 S`. -/
theorem ContinuousLinearMap.opNorm_le_four_mul_of_net {V W : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W] (T : V →L[ℝ] W)
    {A : Set V} {B : Set W} (hA : ∀ x : V, ‖x‖ ≤ 1 → ∃ a ∈ A, ‖x - a‖ ≤ 1 / 2)
    (hB : ∀ y : W, ‖y‖ ≤ 1 → ∃ b ∈ B, ‖y - b‖ ≤ 1 / 2) {S : ℝ} (hS : 0 ≤ S)
    (h : ∀ a ∈ A, ∀ b ∈ B, |⟪b, T a⟫| ≤ S) : ‖T‖ ≤ 4 * S := by
  have h1 : ∀ a ∈ A, ‖T a‖ ≤ 2 * S := fun a ha => by
    rcases eq_or_ne (T a) 0 with h0 | h0
    · rw [h0, norm_zero]; linarith
    have hn : 0 < ‖T a‖ := norm_pos_iff.2 h0
    set u : W := ‖T a‖⁻¹ • T a with hu
    have hun : ‖u‖ ≤ 1 := by
      rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    obtain ⟨b, hb, hub⟩ := hB u hun
    have hval : ⟪u, T a⟫ = ‖T a‖ := by
      rw [hu, real_inner_smul_left, real_inner_self_eq_norm_sq, sq, ← mul_assoc,
        inv_mul_cancel₀ hn.ne', one_mul]
    have hsplit : ⟪u, T a⟫ = ⟪b, T a⟫ + ⟪u - b, T a⟫ := by
      rw [inner_sub_left]; ring
    have hrest : ⟪u - b, T a⟫ ≤ 1 / 2 * ‖T a‖ :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hub (norm_nonneg _))
    have := (le_abs_self _).trans (h a ha b hb)
    linarith
  have h2 : ‖T‖ ≤ 2 * S + ‖T‖ / 2 := by
    have hC : 0 ≤ 2 * S + ‖T‖ / 2 := by positivity
    refine T.opNorm_le_of_unit_norm hC fun x hx => ?_
    obtain ⟨a, ha, hxa⟩ := hA x hx.le
    calc ‖T x‖ = ‖T a + T (x - a)‖ := by rw [← map_add, add_sub_cancel]
      _ ≤ ‖T a‖ + ‖T (x - a)‖ := norm_add_le _ _
      _ ≤ 2 * S + ‖T‖ * (1 / 2) :=
          add_le_add (h1 a ha) ((T.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left hxa (norm_nonneg _)))
      _ = 2 * S + ‖T‖ / 2 := by ring
  linarith
