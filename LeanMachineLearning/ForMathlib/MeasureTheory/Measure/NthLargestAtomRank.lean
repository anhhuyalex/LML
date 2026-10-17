/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.NthLargestAtom
public import Mathlib.Basic.Denumerable
public import Mathlib.Order.Interval.Set.Nat

/-!
# Ranking distinct positive atoms

A countably infinite family of distinct positive masses with finitely many masses above
any positive threshold is enumerated by `nthLargestAtom`. The rank is the number of
strictly larger masses. This deterministic bridge avoids choosing a ranking of random
points measurably.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory

/-- A family of positive masses that is summable has only finitely many masses
above any fixed positive threshold. -/
theorem finite_superlevel_of_summable {α : Type*} {u : α → ℝ}
    (hs : Summable u) {t : ℝ} (ht : 0 < t) :
    {a | t ≤ u a}.Finite := by
  by_contra hfin
  have hi : Set.Infinite {a | t ≤ u a} := Set.not_finite.1 hfin
  let e : ℕ ↪ α := hi.natEmbedding.trans (Function.Embedding.subtype _)
  have he (n : ℕ) : t ≤ u (e n) := (hi.natEmbedding.toFun n).property
  have hsum : Summable (fun n => u (e n)) := hs.comp_injective e.injective
  have hzero := hsum.tendsto_atTop_zero
  have hlim : Filter.Tendsto (fun n => u (e n)) Filter.atTop (nhds 0) := hzero
  have hclosed : t ≤ (0 : ℝ) := ge_of_tendsto hlim (Filter.Eventually.of_forall he)
  exact (not_le_of_gt ht) hclosed

/-- For a positive injective family with finite superlevels, counting the larger
values gives each point a unique natural-number rank. -/
noncomputable def positiveMassRank {α : Type*} (u : α → ℝ) (a : α) : ℕ :=
  Set.ncard {b | u a < u b}

/-- A point with smaller mass has strictly larger rank. -/
theorem positiveMassRank_strictAnti {α : Type*} {u : α → ℝ}
    (hfin : ∀ a, {b | u a ≤ u b}.Finite) {a b : α} (hab : u a < u b) :
    positiveMassRank u b < positiveMassRank u a := by
  classical
  have hsubset : {c | u b < u c} ⊂ {c | u a < u c} := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨fun c hc => hab.trans hc, ?_⟩
    intro heq
    have hb : b ∈ {c | u b < u c} := heq ▸ (show b ∈ {c | u a < u c} from hab)
    exact (lt_irrefl (u b) hb)
  have hf : {c | u a < u c}.Finite := (hfin a).subset (fun c hc => show u a ≤ u c from le_of_lt hc)
  let _ : Finite {c | u a < u c} := hf.to_subtype
  exact Set.ncard_lt_ncard hsubset

/-- Distinct masses are distinguished by their number of larger masses. -/
theorem positiveMassRank_injective {α : Type*} {u : α → ℝ}
    (hu : Function.Injective u)
    (hfin : ∀ a, {b | u a ≤ u b}.Finite) :
    Function.Injective (positiveMassRank u) := by
  intro a b h
  rcases lt_trichotomy (u a) (u b) with hab | hab | hab
  · exact False.elim ((positiveMassRank_strictAnti hfin hab).ne h.symm)
  · exact hu hab
  · exact False.elim ((positiveMassRank_strictAnti hfin hab).ne h)

/-- Every natural rank occurs when there are infinitely many distinct masses:
otherwise the finitely many masses above a fixed one would exhaust the family. -/
theorem positiveMassRank_surjective {α : Type*} [Infinite α] {u : α → ℝ}
    (hu : Function.Injective u)
    (hfin : ∀ a, {b | u a ≤ u b}.Finite) :
    Function.Surjective (positiveMassRank u) := by
  classical
  let rank := positiveMassRank u
  have hrank : Function.Injective rank := positiveMassRank_injective hu hfin
  have hdown : ∀ a : α, ∀ k < rank a, ∃ b, rank b = k := by
    intro a k hk
    let s : Set α := {b | u a < u b}
    have hs : s.Finite := (hfin a).subset
      (fun b hb => show u a ≤ u b from le_of_lt hb)
    have hstep : ∀ b ∈ s, rank b < rank a := fun b hb =>
      positiveMassRank_strictAnti hfin hb
    let _ : Finite s := hs.to_subtype
    have hcount : (Set.Iio (rank a)).ncard = rank a := Set.ncard_Iio_nat _
    have himage : (rank '' s).ncard = s.ncard :=
      Set.ncard_image_of_injective s hrank
    have heq : rank '' s = Set.Iio (rank a) := by
      apply Set.eq_of_subset_of_ncard_le (ht := Set.finite_Iio _)
      · rintro j ⟨b, hb, rfl⟩
        exact hstep b hb
      · rw [hcount, himage]
        rfl
    have hmem : k ∈ rank '' s := heq.symm ▸ (show k ∈ Set.Iio (rank a) from hk)
    obtain ⟨b, _, hb'⟩ := hmem
    exact ⟨b, hb'⟩
  intro k
  by_contra hn
  have hlarge : ∀ a, rank a < k := by
    intro a
    by_contra hle
    have hka : k ≤ rank a := Nat.le_of_not_gt hle
    rcases eq_or_lt_of_le hka with heq | hlt
    · exact hn ⟨a, heq.symm⟩
    · obtain ⟨b, hb⟩ := hdown a k hlt
      exact hn ⟨b, hb⟩
  have hfinite : (Set.range rank).Finite := by
    have hsub : Set.range rank ⊆ Set.Iio k := by
      rintro j ⟨b, rfl⟩
      exact hlarge b
    exact (Set.finite_Iio k).subset hsub
  exact (Set.infinite_range_of_injective hrank) hfinite

/-- The ranking equivalence of an infinite family of distinct positive masses. -/
noncomputable def positiveMassRankEquiv {α : Type*} [Infinite α] (u : α → ℝ)
    (hu : Function.Injective u) (hfin : ∀ a, {b | u a ≤ u b}.Finite) : α ≃ ℕ :=
  Equiv.ofBijective (positiveMassRank u)
    ⟨positiveMassRank_injective hu hfin, positiveMassRank_surjective hu hfin⟩

/-- The level count for a Dirac sum of positive distinct masses is the number
of masses above the level. -/
theorem count_Ioi_sum_dirac {α : Type*} (u : α → ℝ) (t : ℝ) :
    (Measure.sum fun a : α => Measure.dirac (u a)) (Ioi t) =
      (Set.encard {a | t < u a} : ℝ≥0∞) := by
  rw [Measure.sum_apply _ measurableSet_Ioi]
  simp only [Measure.dirac_apply' _ measurableSet_Ioi]
  rw [← ENNReal.tsum_set_one,
    tsum_subtype {a : α | t < u a} (fun _ => (1 : ℝ≥0∞))]
  apply tsum_congr
  intro a
  simp [Set.indicator]

/-- In a positive, summable, injective family, the point of rank `n` is exactly
the `n`-th largest atom of its counting measure. -/
theorem nthLargestAtom_sum_dirac_rank {α : Type*} (u : α → ℝ)
    (hpos : ∀ a, 0 < u a) (hs : Summable u)
    (a : α) :
    nthLargestAtom (positiveMassRank u a)
      (Measure.sum fun b : α => Measure.dirac (u b)) = ENNReal.ofReal (u a) := by
  classical
  let M : Measure ℝ := Measure.sum fun b : α => Measure.dirac (u b)
  let n := positiveMassRank u a
  have hfin (b : α) : {c | u b ≤ u c}.Finite :=
    finite_superlevel_of_summable hs (hpos b)
  have hint : ∀ s : ℝ, 0 < s → M (Ioi s) = ⊤ ∨ ∃ k : ℕ, M (Ioi s) = k := by
    intro s _
    rw [count_Ioi_sum_dirac]
    generalize Set.encard {a | s < u a} = e
    induction e using ENat.recTopCoe with
    | top => exact Or.inl rfl
    | coe k => exact Or.inr ⟨k, rfl⟩
  have hlevel : M (Ioi (u a)) = (n : ℝ≥0∞) := by
    rw [count_Ioi_sum_dirac]
    have hf : {b | u a < u b}.Finite := (hfin a).subset
      (fun b hb => show u a ≤ u b from le_of_lt hb)
    rw [← hf.cast_ncard_eq]
    rfl
  have hstrict : ∀ t : ℝ, 0 ≤ t → t < u a →
      (n + 1 : ℝ≥0∞) ≤ M (Ioi t) := by
    intro t ht hta
    rw [count_Ioi_sum_dirac]
    have hsub : insert a {b | u a < u b} ⊆ {b | t < u b} := by
      intro b hb
      rcases Set.mem_insert_iff.mp hb with rfl | hb
      · exact hta
      · exact hta.trans hb
    have hnot : a ∉ {b | u a < u b} := fun ha => (lt_irrefl (u a)) ha
    have hf : {b | u a < u b}.Finite := (hfin a).subset
      (fun b hb => show u a ≤ u b from le_of_lt hb)
    have hcard : (n + 1 : ℝ≥0∞) =
        ((insert a {b | u a < u b}).encard : ℝ≥0∞) := by
      rw [Set.encard_insert_of_notMem hnot, ← hf.cast_ncard_eq]
      simp only [ENat.toENNReal_add, ENat.toENNReal_one]
      rfl
    exact hcard.le.trans (ENat.toENNReal_mono (Set.encard_mono hsub))
  apply le_antisymm
  · by_contra h
    have hlt : ENNReal.ofReal (u a) < nthLargestAtom n M := lt_of_not_ge h
    have hge := (ofReal_lt_nthLargestAtom_iff (M := M) n (hpos a).le hint).1 hlt
    rw [hlevel] at hge
    exact (not_le_of_gt (by exact_mod_cast Nat.lt_succ_self n)) hge
  · have hle : ∀ q : ℚ, (q : ℝ) < u a →
        ENNReal.ofReal q ≤ nthLargestAtom n M := by
      intro q hq
      by_cases hq0 : 0 ≤ (q : ℝ)
      · have hqM : (n + 1 : ℝ≥0∞) ≤ M (Ioi (q : ℝ)) := hstrict q hq0 hq
        exact (show ENNReal.ofReal q ≤ nthLargestAtom n M from by
          exact le_iSup_of_le q (by simp [hqM]))
      · simp only [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hq0)]
        exact bot_le
    apply le_of_forall_lt
    intro v hv
    have hvfin : v ≠ ⊤ := ne_top_of_lt (hv.trans_le le_top)
    have hvreal : v.toReal < u a := by
      have hv' := (ENNReal.toReal_lt_toReal hvfin ENNReal.ofReal_ne_top).2 hv
      simpa [ENNReal.toReal_ofReal (hpos a).le] using hv'
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hvreal
    have hq0 : 0 < (q : ℝ) := lt_of_le_of_lt (ENNReal.toReal_nonneg) hq1
    have hqstrict : v < ENNReal.ofReal q := by
      rw [← ENNReal.ofReal_toReal hvfin]
      exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hq1, hq0⟩
    exact hqstrict.trans_le (hle q hq2)

/-- The entire ranked sequence is the original family reindexed by its rank
bijection; no measurable selection of the bijection is needed. -/
theorem nthLargestAtom_sum_dirac_rankEquiv {α : Type*} [Infinite α] (u : α → ℝ)
    (hu : Function.Injective u) (hpos : ∀ a, 0 < u a) (hs : Summable u)
    (k : ℕ) :
    nthLargestAtom k (Measure.sum fun a : α => Measure.dirac (u a)) =
      ENNReal.ofReal (u ((positiveMassRankEquiv u hu
        (fun a => finite_superlevel_of_summable hs (hpos a))).symm k)) := by
  let e := positiveMassRankEquiv u hu
    (fun a => finite_superlevel_of_summable hs (hpos a))
  have hk : positiveMassRank u (e.symm k) = k := e.apply_symm_apply k
  change nthLargestAtom k (Measure.sum fun a : α => Measure.dirac (u a)) =
    ENNReal.ofReal (u (e.symm k))
  simpa only [hk] using nthLargestAtom_sum_dirac_rank u hpos hs (e.symm k)

/-- The sum of ranked masses equals the sum over the original atom indices. -/
theorem tsum_nthLargestAtom_sum_dirac {α : Type*} [Infinite α] (u : α → ℝ)
    (hu : Function.Injective u) (hpos : ∀ a, 0 < u a) (hs : Summable u) :
    (∑' k, nthLargestAtom k (Measure.sum fun a : α => Measure.dirac (u a))) =
      ENNReal.ofReal (∑' a, u a) := by
  let e := positiveMassRankEquiv u hu
    (fun a => finite_superlevel_of_summable hs (hpos a))
  simp_rw [nthLargestAtom_sum_dirac_rankEquiv u hu hpos hs]
  change (∑' k, ENNReal.ofReal (u (e.symm k))) = ENNReal.ofReal (∑' a, u a)
  rw [ENNReal.ofReal_tsum_of_nonneg (fun a => (hpos a).le) hs]
  exact Equiv.tsum_eq e.symm (fun a => ENNReal.ofReal (u a))

end MeasureTheory
