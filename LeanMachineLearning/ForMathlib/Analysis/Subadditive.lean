/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Subadditive

/-!
# Fekete's lemma for superadditive sequences

Mathlib proves Fekete's lemma for subadditive sequences (`Subadditive.tendsto_lim`).  The
superadditive version, used for the Guerra–Toninelli thermodynamic limit
([Panchenko, 2013, Lemma 1.3]), follows by negation.  No definition of "superadditive" is
introduced: the hypothesis `∀ m n, u m + u n ≤ u (m + n)` is written out.

## Main declarations

* `tendsto_div_atTop_sSup_of_superadditive`: if `u (m + n) ≥ u m + u n` and `u n / n` is bounded
  above, then `u n / n → sup_{n ≥ 1} u n / n`.
-/

@[expose] public section

open Set Filter
open scoped Topology

/-- **Fekete's lemma for superadditive sequences** ([Panchenko, 2013, Lemma 1.3, Eq. (1.37)]):
if `u m + u n ≤ u (m + n)` for all `m n` and `u n / n` is bounded above, then
`u n / n` converges to `sup_{n ≥ 1} u n / n`. -/
theorem tendsto_div_atTop_sSup_of_superadditive {u : ℕ → ℝ}
    (h : ∀ m n, u m + u n ≤ u (m + n)) (hbdd : BddAbove (range fun n => u n / n)) :
    Tendsto (fun n => u n / n) atTop (𝓝 (sSup ((fun n : ℕ => u n / n) '' Ici 1))) := by
  have hs : Subadditive fun n => -u n := fun m n => by
    have := h m n
    simp only
    linarith
  have hb : BddBelow (range fun n : ℕ => -u n / n) := by
    obtain ⟨C, hC⟩ := hbdd
    refine ⟨-C, ?_⟩
    rintro _ ⟨n, rfl⟩
    have := hC ⟨n, rfl⟩
    simp only [neg_div]
    linarith
  have hlim : hs.lim = -sSup ((fun n : ℕ => u n / n) '' Ici 1) := by
    rw [Subadditive.lim, Real.sInf_def]
    congr 2
    ext x
    simp only [Set.mem_neg, mem_image, mem_Ici, neg_div]
    constructor
    · rintro ⟨n, hn, hx⟩
      exact ⟨n, hn, by linarith⟩
    · rintro ⟨n, hn, hx⟩
      exact ⟨n, hn, by linarith⟩
  have := (hs.tendsto_lim hb).neg
  rw [hlim, neg_neg] at this
  simpa [neg_div] using this
