/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# The decreasing enumeration of the atoms of a counting measure on `ℝ`

For a measure `M` on `ℝ`, `nthLargestAtom n M` is the `(n+1)`-st largest *positive* point of `M`,
counted with multiplicity: the supremum of the rationals `q` with `M (Ioi q) ≥ n + 1`
(and `0` if there is none). It needs no choice of an ordering of the points, and it is a
measurable function of `M` for the Giry σ-algebra, because it is a countable supremum of
simple functions.

If `M` takes values in `ℕ ∪ {∞}` on the half-lines `Ioi s`, `s > 0`, then
`M (Ioi t) = #{n | t < nthLargestAtom n M}` (`lt_nthLargestAtom_iff`), and the layer-cake formula
gives `∑ₙ nthLargestAtom n M = ∫ x in Ioi 0, x ∂M` (`tsum_nthLargestAtom`), whatever the
multiplicities of the points are.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory

open scoped Classical in
/-- The `(n+1)`-st largest positive point of a counting measure `M` on `ℝ`, counted with
multiplicity: `sup {q ∈ ℚ | n + 1 ≤ M (Ioi q)}` (with value `0` when the set is empty, and `∞`
when it is unbounded). -/
noncomputable def nthLargestAtom (n : ℕ) (M : Measure ℝ) : ℝ≥0∞ :=
  ⨆ q : ℚ, if (n + 1 : ℝ≥0∞) ≤ M (Ioi (q : ℝ)) then ENNReal.ofReal q else 0

/-- `M ↦ nthLargestAtom n M` is measurable for the Giry σ-algebra. -/
theorem measurable_nthLargestAtom (n : ℕ) : Measurable (nthLargestAtom n) :=
  Measurable.iSup fun _ => Measurable.ite
    (measurableSet_le measurable_const (Measure.measurable_coe measurableSet_Ioi))
    measurable_const measurable_const

/-- The enumeration is decreasing: `u₀ ≥ u₁ ≥ …`. -/
theorem antitone_nthLargestAtom (M : Measure ℝ) : Antitone fun n => nthLargestAtom n M := by
  intro m n hmn
  refine iSup_mono fun q => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (le_trans (by exact_mod_cast Nat.succ_le_succ hmn) h1) h2
  · exact bot_le
  · exact le_rfl

/-- The mass of an open half-line is the increasing limit of the masses of the half-lines
`(t + 1/(j+1), ∞)`. -/
theorem measure_Ioi_eq_iSup_add_one_div (M : Measure ℝ) (t : ℝ) :
    M (Ioi t) = ⨆ j : ℕ, M (Ioi (t + 1 / ((j : ℝ) + 1))) := by
  rw [← Monotone.measure_iUnion]
  · congr 1
    ext x
    simp only [mem_Ioi, mem_iUnion]
    refine ⟨fun hx => ?_, fun ⟨j, hj⟩ => ?_⟩
    · obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
      exact ⟨j, by linarith⟩
    · have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith
  · intro j k hjk
    refine Ioi_subset_Ioi ?_
    have : 1 / ((k : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
    linarith

/-- If `M` is `ℕ ∪ {∞}`-valued on the half-lines `Ioi s`, `s > 0`, then for `t ≥ 0` the `(n+1)`-st
largest atom exceeds `t` iff at least `n + 1` atoms lie above `t`. -/
theorem ofReal_lt_nthLargestAtom_iff {M : Measure ℝ} (n : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hint : ∀ s : ℝ, 0 < s → M (Ioi s) = ⊤ ∨ ∃ m : ℕ, M (Ioi s) = m) :
    ENNReal.ofReal t < nthLargestAtom n M ↔ (n + 1 : ℝ≥0∞) ≤ M (Ioi t) := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := lt_iSup_iff.1 h
    by_cases hM : (n + 1 : ℝ≥0∞) ≤ M (Ioi (q : ℝ))
    · simp only [hM, ↓reduceIte, ENNReal.ofReal_lt_ofReal_iff'] at hq
      exact hM.trans (measure_mono (Ioi_subset_Ioi hq.1.le))
    · simp only [hM, ↓reduceIte] at hq
      exact absurd hq (not_lt_of_ge bot_le)
  · intro h
    have hcont := measure_Ioi_eq_iSup_add_one_div M t
    have hj : ∃ j : ℕ, (n + 1 : ℝ≥0∞) ≤ M (Ioi (t + 1 / ((j : ℝ) + 1))) := by
      by_contra hcon
      push Not at hcon
      have hle : ⨆ j : ℕ, M (Ioi (t + 1 / ((j : ℝ) + 1))) ≤ n := by
        refine iSup_le fun j => ?_
        rcases hint (t + 1 / ((j : ℝ) + 1)) (by positivity) with htop | ⟨m, hm⟩
        · exact absurd (htop ▸ hcon j) (not_lt_of_ge le_top)
        · have := hcon j
          rw [hm] at this ⊢
          exact_mod_cast Nat.lt_succ_iff.1 (by exact_mod_cast this)
      rw [← hcont] at hle
      exact absurd (h.trans hle) (by exact_mod_cast Nat.not_succ_le_self n)
    obtain ⟨j, hj⟩ := hj
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < t + 1 / ((j : ℝ) + 1) by
      have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith)
    have hMq : (n + 1 : ℝ≥0∞) ≤ M (Ioi (q : ℝ)) :=
      hj.trans (measure_mono (Ioi_subset_Ioi hq2.le))
    calc ENNReal.ofReal t < ENNReal.ofReal q :=
          ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hq1, by linarith⟩
      _ = if (n + 1 : ℝ≥0∞) ≤ M (Ioi (q : ℝ)) then ENNReal.ofReal q else 0 := by simp [hMq]
      _ ≤ nthLargestAtom n M := le_iSup (fun q : ℚ =>
          if (n + 1 : ℝ≥0∞) ≤ M (Ioi (q : ℝ)) then ENNReal.ofReal q else 0) q

/-- Counting the `n` with `n + 1 ≤ c` recovers a value `c ∈ ℕ ∪ {∞}`. -/
theorem tsum_ite_add_one_le {c : ℝ≥0∞} (hc : c = ⊤ ∨ ∃ m : ℕ, c = m) :
    ∑' n : ℕ, (if (n + 1 : ℝ≥0∞) ≤ c then (1 : ℝ≥0∞) else 0) = c := by
  rcases hc with rfl | ⟨m, rfl⟩
  · simp
  · rw [tsum_eq_sum (s := Finset.range m)]
    · rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ≥0∞))]
      · simp
      · intro n hn
        simp only [Finset.mem_range] at hn
        simp [show (n + 1 : ℝ≥0∞) ≤ m by exact_mod_cast hn]
    · intro n hn
      simp only [Finset.mem_range, not_lt] at hn
      simp [show ¬ ((n : ℝ≥0∞) + 1 ≤ m) by exact_mod_cast (by omega : ¬ n + 1 ≤ m)]

/-- The set of `t > 0` below the `n`-th atom has Lebesgue measure equal to that atom. -/
theorem volume_ofReal_lt_inter_Ioi (u : ℝ≥0∞) :
    volume ({t : ℝ | ENNReal.ofReal t < u} ∩ Ioi 0) = u := by
  by_cases hu : u = ⊤
  · have : {t : ℝ | ENNReal.ofReal t < u} ∩ Ioi 0 = Ioi 0 := by
      ext t; simp [hu]
    rw [this, Real.volume_Ioi, hu]
  · have : {t : ℝ | ENNReal.ofReal t < u} ∩ Ioi 0 = Ioo 0 u.toReal := by
      ext t
      simp only [mem_inter_iff, Set.mem_ofPred_eq, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, (ENNReal.ofReal_lt_iff_lt_toReal h2.le hu).1 h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨(ENNReal.ofReal_lt_iff_lt_toReal h2.le hu).2 h1, h2⟩
    rw [this, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal hu]

/-- **The sum of the atoms is the first moment.** If `M` is `ℕ ∪ {∞}`-valued on the half-lines
`Ioi s`, `s > 0`, then `∑ₙ nthLargestAtom n M = ∫ x in Ioi 0, x ∂M` (in `ℝ≥0∞`), whatever the
multiplicities of the atoms. -/
theorem tsum_nthLargestAtom {M : Measure ℝ}
    (hint : ∀ s : ℝ, 0 < s → M (Ioi s) = ⊤ ∨ ∃ m : ℕ, M (Ioi s) = m) :
    ∑' n, nthLargestAtom n M = ∫⁻ x in Ioi 0, ENNReal.ofReal x ∂M := by
  let S : ℕ → Set ℝ := fun n => {t | ENNReal.ofReal t < nthLargestAtom n M}
  have hS : ∀ n, MeasurableSet (S n) := fun n =>
    measurableSet_lt ENNReal.measurable_ofReal measurable_const
  have hcount : ∀ t : ℝ, 0 < t → M (Ioi t) = ∑' n, (S n).indicator (fun _ => (1 : ℝ≥0∞)) t := by
    intro t ht
    rw [← tsum_ite_add_one_le (hint t ht)]
    refine tsum_congr fun n => ?_
    simp only [S, indicator, Set.mem_ofPred_eq, ofReal_lt_nthLargestAtom_iff n ht.le hint]
  calc ∑' n, nthLargestAtom n M
      = ∑' n, ∫⁻ t in Ioi 0, (S n).indicator (fun _ => (1 : ℝ≥0∞)) t := by
        refine tsum_congr fun n => ?_
        rw [lintegral_indicator (hS n), setLIntegral_const, one_mul, Measure.restrict_apply (hS n),
          volume_ofReal_lt_inter_Ioi]
    _ = ∫⁻ t in Ioi 0, ∑' n, (S n).indicator (fun _ => (1 : ℝ≥0∞)) t :=
        (lintegral_tsum fun n => ((measurable_const.indicator (hS n)).aemeasurable)).symm
    _ = ∫⁻ t in Ioi 0, M (Ioi t) :=
        setLIntegral_congr_fun measurableSet_Ioi fun t ht => (hcount t ht).symm
    _ = ∫⁻ t in Ioi 0, (M.restrict (Ioi 0)) {a | t < a} := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        rw [Measure.restrict_apply' measurableSet_Ioi]
        congr 1
        ext a
        simp only [mem_inter_iff, Set.mem_ofPred_eq, mem_Ioi]
        exact ⟨fun h => ⟨h, ht.trans h⟩, fun h => h.1⟩
    _ = ∫⁻ x in Ioi 0, ENNReal.ofReal x ∂M := by
        refine (lintegral_eq_lintegral_meas_lt (M.restrict (Ioi 0)) (f := id) ?_
          aemeasurable_id).symm
        exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => hx.le)

end MeasureTheory
