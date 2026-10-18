/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.NthLargestAtomRank

/-!
# The mark of the `l`-th largest point of a marked counting measure

For a counting measure `μ` on `ℝ × Γ` (positions and marks, `Γ` countable) the mark of the
`l`-th largest point is read from the counts of points above rational thresholds: the mark `b` is
the one for which, between two rational thresholds `q < q'`, `μ` has `l + 1` points above `q`, `l`
points above `q'` and exactly one more point with mark `b` above `q` than above `q'`. This is a
measurable function of `μ`, and for a family of positive, distinct, summable positions it is the
mark of the point of rank `l` (`isRankedMark_sum_dirac_iff`).
-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {Γ : Type*} [MeasurableSpace Γ]

/-- Between the rational thresholds `q < q'` the counting measure `μ` has `l + 1` points above
`q`, `l` points above `q'`, and exactly one more point with mark `b` above `q` than above `q'`. -/
def IsRankedMark (l : ℕ) (b : Γ) (μ : Measure (ℝ × Γ)) : Prop :=
  ∃ q q' : ℚ, (q : ℝ) < q' ∧ μ (Ioi (q : ℝ) ×ˢ univ) = l + 1 ∧ μ (Ioi (q' : ℝ) ×ˢ univ) = l ∧
    μ (Ioi (q : ℝ) ×ˢ {b}) = μ (Ioi (q' : ℝ) ×ˢ {b}) + 1

/-- `IsRankedMark l b` is a measurable condition on the counting measure. -/
theorem measurableSet_isRankedMark [MeasurableSingletonClass Γ] (l : ℕ) (b : Γ) :
    MeasurableSet {μ : Measure (ℝ × Γ) | IsRankedMark l b μ} := by
  have hset : ∀ (q : ℚ) (B : Set Γ), MeasurableSet B →
      Measurable fun μ : Measure (ℝ × Γ) => μ (Ioi (q : ℝ) ×ˢ B) := fun q B hB =>
    Measure.measurable_coe (measurableSet_Ioi.prod hB)
  have hc : {μ : Measure (ℝ × Γ) | IsRankedMark l b μ} = ⋃ q : ℚ, ⋃ q' : ℚ, ⋃ _ : (q : ℝ) < q',
      {μ : Measure (ℝ × Γ) | μ (Ioi (q : ℝ) ×ˢ univ) = l + 1} ∩
        {μ : Measure (ℝ × Γ) | μ (Ioi (q' : ℝ) ×ˢ univ) = l} ∩
        {μ : Measure (ℝ × Γ) | μ (Ioi (q : ℝ) ×ˢ {b}) = μ (Ioi (q' : ℝ) ×ˢ {b}) + 1} := by
    ext μ
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, IsRankedMark]
    constructor
    · rintro ⟨q, q', h1, h2, h3, h4⟩
      exact ⟨q, q', h1, ⟨h2, h3⟩, h4⟩
    · rintro ⟨q, q', h1, ⟨h2, h3⟩, h4⟩
      exact ⟨q, q', h1, h2, h3, h4⟩
  rw [hc]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun q' => MeasurableSet.iUnion
    fun _ => ?_
  refine ((measurableSet_eq_fun (hset q univ MeasurableSet.univ) measurable_const).inter
    (measurableSet_eq_fun (hset q' univ MeasurableSet.univ) measurable_const)).inter
    (measurableSet_eq_fun (hset q {b} (measurableSet_singleton b))
      ((hset q' {b} (measurableSet_singleton b)).add_const 1))

/-- Characterization of the least element of a set of natural numbers. -/
theorem sInf_nat_eq_iff (S : Set ℕ) (n : ℕ) :
    sInf S = n ↔ (n ∈ S ∧ ∀ m, m < n → m ∉ S) ∨ ((∀ m, m ∉ S) ∧ n = 0) := by
  by_cases hne : S.Nonempty
  · constructor
    · rintro rfl
      exact Or.inl ⟨Nat.sInf_mem hne, fun m hm => notMem_of_lt_csInf' hm⟩
    · rintro (⟨hn, hlt⟩ | ⟨h, _⟩)
      · refine le_antisymm (Nat.sInf_le hn) (not_lt.1 fun hlt' => ?_)
        exact hlt _ hlt' (Nat.sInf_mem hne)
      · exact absurd (Nat.sInf_mem hne) (h _)
  · have hS0 : S = ∅ := not_nonempty_iff_eq_empty.1 hne
    subst hS0
    simp [Nat.sInf_empty, eq_comm]

section Mark

variable [Encodable Γ] [Inhabited Γ]

/-- The mark of the `l`-th largest point of a counting measure on `ℝ × Γ`: the mark `b` of least
code with `IsRankedMark l b μ` (an arbitrary mark if there is none). -/
noncomputable def rankedMark (l : ℕ) (μ : Measure (ℝ × Γ)) : Γ :=
  (Encodable.decode (sInf {n | ∃ b : Γ, Encodable.encode b = n ∧ IsRankedMark l b μ})).getD
    default

/-- If exactly one mark satisfies `IsRankedMark l`, it is the ranked mark. -/
theorem rankedMark_eq_of_unique {l : ℕ} {μ : Measure (ℝ × Γ)} {b : Γ}
    (hb : IsRankedMark l b μ) (hu : ∀ b', IsRankedMark l b' μ → b' = b) :
    rankedMark l μ = b := by
  have hS : {n | ∃ b' : Γ, Encodable.encode b' = n ∧ IsRankedMark l b' μ} =
      {Encodable.encode b} := by
    ext n
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨b', rfl, hb'⟩
      rw [hu b' hb']
    · rintro rfl
      exact ⟨b, rfl, hb⟩
  unfold rankedMark
  rw [hS, csInf_singleton, Encodable.encodek]
  rfl

/-- The ranked mark is a measurable function of the counting measure. -/
theorem measurable_rankedMark [MeasurableSingletonClass Γ] (l : ℕ) :
    Measurable (rankedMark (Γ := Γ) l) := by
  classical
  have hmem : ∀ n : ℕ, MeasurableSet {μ : Measure (ℝ × Γ) |
      n ∈ {n | ∃ b : Γ, Encodable.encode b = n ∧ IsRankedMark l b μ}} := fun n => by
    have : {μ : Measure (ℝ × Γ) | n ∈ {n | ∃ b : Γ, Encodable.encode b = n ∧
        IsRankedMark l b μ}} = ⋃ b : {b : Γ // Encodable.encode b = n},
          {μ | IsRankedMark l b.1 μ} := by
      ext μ
      simp only [mem_ofPred_eq, mem_iUnion, Subtype.exists]
      exact ⟨fun ⟨b, hb, h⟩ => ⟨b, hb, h⟩, fun ⟨b, hb, h⟩ => ⟨b, hb, h⟩⟩
    rw [this]
    exact MeasurableSet.iUnion fun b => measurableSet_isRankedMark l b.1
  have hinf : Measurable fun μ : Measure (ℝ × Γ) =>
      sInf {n | ∃ b : Γ, Encodable.encode b = n ∧ IsRankedMark l b μ} := by
    refine measurable_to_countable' fun n => ?_
    have : (fun μ : Measure (ℝ × Γ) => sInf {n | ∃ b : Γ, Encodable.encode b = n ∧
        IsRankedMark l b μ}) ⁻¹' {n} =
        ({μ | n ∈ {n | ∃ b : Γ, Encodable.encode b = n ∧ IsRankedMark l b μ}} ∩
          ⋂ m ∈ Finset.range n, {μ | m ∉ {n | ∃ b : Γ, Encodable.encode b = n ∧
            IsRankedMark l b μ}}) ∪
        ({μ | ∀ m, m ∉ {n | ∃ b : Γ, Encodable.encode b = n ∧ IsRankedMark l b μ}} ∩
          {_μ | n = 0}) := by
      ext μ
      simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_ofPred_eq,
        mem_iInter, Finset.mem_range]
      exact sInf_nat_eq_iff _ n
    rw [this]
    refine ((hmem n).inter (Finset.measurableSet_biInter _ fun m _ => (hmem m).compl)).union ?_
    refine MeasurableSet.inter ?_ (MeasurableSet.const _)
    have : {μ : Measure (ℝ × Γ) | ∀ m, m ∉ {n | ∃ b : Γ, Encodable.encode b = n ∧
        IsRankedMark l b μ}} = ⋂ m : ℕ, {μ | m ∉ {n | ∃ b : Γ, Encodable.encode b = n ∧
        IsRankedMark l b μ}} := by ext; simp
    rw [this]
    exact MeasurableSet.iInter fun m => (hmem m).compl
  have hdec : Measurable fun n : ℕ => (Encodable.decode n : Option Γ).getD default :=
    measurable_from_nat
  exact hdec.comp hinf

end Mark

section Det

variable [MeasurableSingletonClass Γ] {Q : Type*} {x : Q → ℝ} {a : Q → Γ}

omit [MeasurableSingletonClass Γ] in
/-- The mass of `Ioi s ×ˢ B` under the counting measure of the marked points `(x q, a q)`. -/
theorem sum_dirac_Ioi_prod_apply (x : Q → ℝ) (a : Q → Γ) (s : ℝ) {B : Set Γ}
    (hB : MeasurableSet B) :
    (Measure.sum fun q => Measure.dirac (x q, a q)) (Ioi s ×ˢ B) =
      (({q | s < x q ∧ a q ∈ B}.encard : ℕ∞) : ℝ≥0∞) := by
  rw [sum_dirac_apply (fun q => (x q, a q)) (measurableSet_Ioi.prod hB)]
  congr 2

/-- `IsRankedMark` for a counting measure of marked points, in terms of cardinalities. -/
theorem isRankedMark_sum_dirac_iff_encard (l : ℕ) (b : Γ) :
    IsRankedMark l b (Measure.sum fun q => Measure.dirac (x q, a q)) ↔
      ∃ q q' : ℚ, (q : ℝ) < q' ∧ {r | (q : ℝ) < x r}.encard = l + 1 ∧
        {r | (q' : ℝ) < x r}.encard = l ∧
        {r | (q : ℝ) < x r ∧ a r = b}.encard = {r | (q' : ℝ) < x r ∧ a r = b}.encard + 1 := by
  have h1 : ∀ s : ℝ, (Measure.sum fun q => Measure.dirac (x q, a q)) (Ioi s ×ˢ univ) =
      (({q | s < x q}.encard : ℕ∞) : ℝ≥0∞) := fun s => by
    rw [sum_dirac_Ioi_prod_apply x a s MeasurableSet.univ]
    simp
  have h2 : ∀ s : ℝ, (Measure.sum fun q => Measure.dirac (x q, a q)) (Ioi s ×ˢ {b}) =
      (({q | s < x q ∧ a q = b}.encard : ℕ∞) : ℝ≥0∞) := fun s => by
    rw [sum_dirac_Ioi_prod_apply x a s (measurableSet_singleton b)]
    simp
  unfold IsRankedMark
  simp_rw [h1, h2]
  refine exists_congr fun q => exists_congr fun q' => and_congr_right fun _ => ?_
  have c1 : ∀ (e : ℕ∞) (n : ℕ), (e : ℝ≥0∞) = n + 1 ↔ e = n + 1 := fun e n => by
    rw [← ENat.toENNReal_inj]; simp
  have c2 : ∀ (e : ℕ∞) (n : ℕ), (e : ℝ≥0∞) = n ↔ e = n := fun e n => by
    rw [← ENat.toENNReal_inj]; simp
  have c3 : ∀ e₁ e₂ : ℕ∞, (e₁ : ℝ≥0∞) = e₂ + 1 ↔ e₁ = e₂ + 1 := fun e₁ e₂ => by
    rw [← ENat.toENNReal_inj]; simp
  rw [c1, c2, c3]

/-- A finite set of points above `t` stays at a positive distance above `t`. -/
theorem exists_gap_above {t : ℝ} {L : Set Q} (hL : L.Finite) (h : ∀ r ∈ L, t < x r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ L, t + ε ≤ x r := by
  classical
  by_cases hne : L.Nonempty
  · obtain ⟨r₀, hr₀, hmin⟩ := Finset.exists_min_image hL.toFinset x (by simpa using hne)
    refine ⟨x r₀ - t, sub_pos.2 (h r₀ (by simpa using hr₀)), fun r hr => ?_⟩
    have := hmin r (by simpa using hr)
    linarith
  · exact ⟨1, one_pos, fun r hr => absurd ⟨r, hr⟩ hne⟩

/-- The points below `t` stay at a positive distance below `t`. -/
theorem exists_gap_below {t : ℝ} (ht : 0 < t) (hfin : ∀ s, 0 < s → {r | s ≤ x r}.Finite) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r, x r < t → x r ≤ t - δ := by
  classical
  set M := {r | t / 2 ≤ x r ∧ x r < t} with hMdef
  have hM : M.Finite := (hfin (t / 2) (by linarith)).subset fun r hr => hr.1
  by_cases hne : M.Nonempty
  · obtain ⟨r₀, hr₀, hmax⟩ := Finset.exists_max_image hM.toFinset x (by simpa using hne)
    have hr₀M : r₀ ∈ M := by simpa using hr₀
    refine ⟨min (t / 2) (t - x r₀), lt_min (by linarith) (sub_pos.2 hr₀M.2), fun r hr => ?_⟩
    by_cases hr2 : t / 2 ≤ x r
    · have := hmax r (by simpa [hMdef] using ⟨hr2, hr⟩)
      have := min_le_right (t / 2) (t - x r₀)
      linarith
    · have := min_le_left (t / 2) (t - x r₀)
      linarith [not_le.1 hr2]
  · refine ⟨t / 2, by linarith, fun r hr => ?_⟩
    by_contra hcon
    exact hne ⟨r, by linarith [not_le.1 hcon], hr⟩

/-- **The ranked mark of a marked counting measure.** For positive, distinct positions `x q` with
finitely many above every positive threshold, the mark `b` satisfies `IsRankedMark l b` for the
counting measure of the points `(x q, a q)` exactly when `l` is the rank of a point `q₀` and
`b = a q₀`. -/
theorem isRankedMark_sum_dirac_iff (hpos : ∀ q, 0 < x q) (hinj : Function.Injective x)
    (hfin : ∀ s, 0 < s → {r | s ≤ x r}.Finite) (q₀ : Q) (b : Γ) :
    IsRankedMark {r | x q₀ < x r}.ncard b (Measure.sum fun q => Measure.dirac (x q, a q)) ↔
      b = a q₀ := by
  classical
  rw [isRankedMark_sum_dirac_iff_encard]
  set t := x q₀ with ht
  set L := {r | t < x r} with hLdef
  have hL : L.Finite := (hfin t (hpos q₀)).subset fun r hr => show t ≤ x r from le_of_lt hr
  have hq₀L : q₀ ∉ L := by simp [hLdef, ht]
  constructor
  · rintro ⟨q, q', hqq', h1, h2, h3⟩
    set A := {r | (q : ℝ) < x r} with hA
    set B := {r | (q' : ℝ) < x r} with hB
    have hBA : B ⊆ A := fun r hr => show (q : ℝ) < x r from lt_trans hqq' hr
    have hAfin : A.Finite := Set.finite_of_encard_eq_coe h1
    have hBfin : B.Finite := hAfin.subset hBA
    have hAc : A.ncard = L.ncard + 1 := by
      have h := hAfin.cast_ncard_eq
      rw [h1] at h
      exact_mod_cast h
    have hBc : B.ncard = L.ncard := by
      have h := hBfin.cast_ncard_eq
      rw [h2] at h
      exact_mod_cast h
    have hD : (A \ B).ncard = 1 := by
      rw [Set.ncard_sdiff hBA hBfin, hAc, hBc]
      omega
    obtain ⟨p, hp⟩ := Set.ncard_eq_one.1 hD
    have hpD : p ∈ A \ B := by rw [hp]; exact mem_singleton p
    have hrank : {r | x p < x r} = B := by
      ext r
      simp only [mem_ofPred_eq]
      constructor
      · intro hr
        have hrA : r ∈ A := lt_trans hpD.1 hr
        by_contra hrB
        have : r ∈ A \ B := ⟨hrA, hrB⟩
        rw [hp] at this
        have : r = p := this
        subst this
        exact lt_irrefl _ hr
      · intro hr
        exact lt_of_le_of_lt (not_lt.1 hpD.2) hr
    have hpq : p = q₀ := by
      have hfin' : ∀ r, {s | x r ≤ x s}.Finite := fun r => hfin (x r) (hpos r)
      refine injective_ncard_superlevel_lt hinj hfin' ?_
      show {r | x p < x r}.ncard = {r | x q₀ < x r}.ncard
      rw [hrank, hBc]
    subst hpq
    by_contra hne
    have heq : {r | (q : ℝ) < x r ∧ a r = b} = {r | (q' : ℝ) < x r ∧ a r = b} := by
      ext r
      simp only [mem_ofPred_eq]
      constructor
      · rintro ⟨hr, hra⟩
        refine ⟨?_, hra⟩
        by_contra hrB
        have : r ∈ A \ B := ⟨hr, hrB⟩
        rw [hp] at this
        have : r = p := this
        subst this
        exact hne hra.symm
      · rintro ⟨hr, hra⟩
        exact ⟨lt_trans hqq' hr, hra⟩
    rw [heq] at h3
    have hfinT : {r | (q' : ℝ) < x r ∧ a r = b}.Finite := hBfin.subset fun r hr => hr.1
    rw [← hfinT.cast_ncard_eq] at h3
    norm_cast at h3
    omega
  · rintro rfl
    obtain ⟨ε, hε, hε'⟩ := exists_gap_above hL (fun r hr => hr)
    obtain ⟨δ, hδ, hδ'⟩ := exists_gap_below (hpos q₀) hfin
    obtain ⟨q', hq'1, hq'2⟩ := exists_rat_btwn (show t < t + ε by linarith)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t - δ < t by linarith)
    have hSq : {r | (q : ℝ) < x r} = insert q₀ L := by
      ext r
      simp only [mem_ofPred_eq, mem_insert_iff, hLdef]
      constructor
      · intro hr
        by_cases hlt : x r < t
        · exact absurd (lt_of_le_of_lt (hδ' r hlt) hq1) (not_lt.2 hr.le)
        · rcases (not_lt.1 hlt).eq_or_lt with h | h
          · exact Or.inl (hinj h.symm)
          · exact Or.inr h
      · rintro (rfl | hr)
        · exact hq2
        · exact lt_trans hq2 hr
    have hSq' : {r | (q' : ℝ) < x r} = L := by
      ext r
      simp only [mem_ofPred_eq, hLdef]
      constructor
      · exact fun hr => lt_trans hq'1 hr
      · intro hr
        exact lt_of_lt_of_le hq'2 (hε' r hr)
    have hq : (q : ℝ) < q' := by linarith
    refine ⟨q, q', hq, ?_, ?_, ?_⟩
    · rw [hSq, encard_insert_of_notMem hq₀L, hL.cast_ncard_eq]
    · rw [hSq', hL.cast_ncard_eq]
    · have hTq : {r | (q : ℝ) < x r ∧ a r = a q₀} =
          insert q₀ {r | (q' : ℝ) < x r ∧ a r = a q₀} := by
        ext r
        simp only [mem_ofPred_eq, mem_insert_iff]
        constructor
        · rintro ⟨hr, hra⟩
          have : r ∈ {r | (q : ℝ) < x r} := hr
          rw [hSq] at this
          rcases this with rfl | hrL
          · exact Or.inl rfl
          · right
            have : r ∈ {r | (q' : ℝ) < x r} := by rw [hSq']; exact hrL
            exact ⟨this, hra⟩
        · rintro (rfl | ⟨hr, hra⟩)
          · exact ⟨hq2, rfl⟩
          · exact ⟨lt_trans (by exact_mod_cast hq) hr, hra⟩
      rw [hTq, encard_insert_of_notMem]
      intro hmem
      have : (q' : ℝ) < t := hmem.1
      linarith

/-- **The ranked mark is the mark of the point of that rank.** -/
theorem rankedMark_sum_dirac [Encodable Γ] [Inhabited Γ] (hpos : ∀ q, 0 < x q)
    (hinj : Function.Injective x) (hfin : ∀ s, 0 < s → {r | s ≤ x r}.Finite) (q₀ : Q) :
    rankedMark {r | x q₀ < x r}.ncard (Measure.sum fun q => Measure.dirac (x q, a q)) =
      a q₀ :=
  rankedMark_eq_of_unique ((isRankedMark_sum_dirac_iff hpos hinj hfin q₀ (a q₀)).2 rfl)
    fun _ hb' => (isRankedMark_sum_dirac_iff hpos hinj hfin q₀ _).1 hb'

end Det

end MeasureTheory
