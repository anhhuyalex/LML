/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# One small tolerance for a two-sided estimate

If two functions `F`, `G` are continuous at `0` with `F 0 = G 0 = L`, then for every `ε > 0` and
every `δ₀ > 0` there is a single `t ∈ (0, δ₀)` with `L - ε < F t` and `G t < L + ε`. This is the
bookkeeping step that turns a non-asymptotic sandwich `F t ≤ X ≤ G t` (with a tolerance `t`) into a
convergence-in-probability statement.
-/

@[expose] public section

open Filter Topology

/-- **A single small tolerance works for both sides.** -/
theorem exists_pos_lt_sandwich {F G : ℝ → ℝ} {L ε δ₀ : ℝ} (hF : ContinuousAt F 0)
    (hG : ContinuousAt G 0) (hF0 : F 0 = L) (hG0 : G 0 = L) (hε : 0 < ε) (hδ₀ : 0 < δ₀) :
    ∃ t : ℝ, 0 < t ∧ t < δ₀ ∧ L - ε < F t ∧ G t < L + ε := by
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (0 < t ∧ t < δ₀) ∧ L - ε < F t ∧ G t < L + ε := by
    have hI : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioo (0 : ℝ) δ₀ :=
      Ioo_mem_nhdsGT hδ₀
    have g1 := (hF.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))).eventually
      (lt_mem_nhds (show L - ε < F 0 by rw [hF0]; linarith))
    have g2 := (hG.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))).eventually
      (gt_mem_nhds (show G 0 < L + ε by rw [hG0]; linarith))
    filter_upwards [hI, g1, g2] with t ht h1 h2
    exact ⟨ht, h1, h2⟩
  obtain ⟨t, ⟨ht0, ht1⟩, h1, h2⟩ := hev.exists
  exact ⟨t, ht0, ht1, h1, h2⟩

end
