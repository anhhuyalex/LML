/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Distributions.Poisson.Thinning
public import LeanMachineLearning.ForMathlib.Probability.Distributions.Poisson.SumCountable
public import LeanMachineLearning.ForMathlib.Probability.Independence.Nonatomic
public import LeanMachineLearning.ForMathlib.Probability.Independence.IndepInfinitePi
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Poisson point processes: existence theorem (Panchenko, Theorem 2.5)

Following Panchenko, a Poisson process with mean measure `μ = ∑ₙ rₙ νₙ` is built from independent
blocks `Bₙ = (Nₙ, (Xₙₗ)ₗ)`: `Nₙ ~ Po(rₙ)` points sampled i.i.d. from the probability measure
`νₙ`. The point configuration is represented by its counting measure
`poissonCountingMeasure`, so overlapping atoms are counted with multiplicity.

The theorems are stated for an arbitrary probability space carrying independent blocks with the
prescribed laws, rather than for one canonical product space; `exists_poissonBlocks` shows that
such blocks exist.

## Main declarations

* `SpinGlasses.poissonCountingMeasure`: the counting measure of the first `N n` points of each
  block.
* `SpinGlasses.iIndepFun_hasLaw_poissonCountingMeasure_apply`: the counts of disjoint measurable
  sets of finite mean measure are independent, and `M(A)` is `Po(μ A)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpinGlasses

variable {S : Type*} [MeasurableSpace S]

/-- The counting measure of the first `N n` points of each block. This definition is deterministic:
probability is imposed by a law on the block coordinates. -/
noncomputable def poissonCountingMeasure (N : ℕ → ℕ) (X : ℕ → ℕ → S) : Measure S :=
  Measure.sum fun n => ∑ l ∈ Finset.range (N n), Measure.dirac (X n l)

/-- The counting measure is measurable as a function of all the block coordinates, for the
Giry measurable structure on measures. -/
theorem measurable_poissonCountingMeasure :
    Measurable fun q : (n : ℕ) → ℕ × (ℕ → S) =>
      poissonCountingMeasure (fun n => (q n).1) (fun n l => (q n).2 l) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [poissonCountingMeasure, Measure.sum_apply _ hs]
  apply Measurable.tsum
  intro n
  have hblock : Measurable fun q : ℕ × (ℕ → S) =>
      (∑ l ∈ Finset.range q.1, Measure.dirac (q.2 l)) s := by
    apply measurable_from_prod_countable_right
    intro k
    change Measurable fun y : ℕ → S =>
      (∑ l ∈ Finset.range k, Measure.dirac (y l)) s
    rw [show (fun y : ℕ → S => (∑ l ∈ Finset.range k, Measure.dirac (y l)) s) =
      (fun y => ∑ l ∈ Finset.range k, (Measure.dirac (y l)) s) by
        funext y; simp only [Measure.coe_finsetSum, Finset.sum_apply]]
    exact Finset.measurable_sum _ fun l _ =>
      ((Measure.measurable_coe hs).comp Measure.measurable_dirac).comp
        (measurable_pi_apply l)
  exact hblock.comp (measurable_pi_apply n)

/-- Evaluation of the counting measure on a measurable set is the sum of the numbers of
sampled points in that set, counted with multiplicity. -/
theorem poissonCountingMeasure_apply (N : ℕ → ℕ) (X : ℕ → ℕ → S)
    {A : Set S} (hA : MeasurableSet A) :
    poissonCountingMeasure N X A =
      ∑' n, ∑ l ∈ Finset.range (N n), A.indicator 1 (X n l) := by
  simp only [poissonCountingMeasure, Measure.sum_apply _ hA, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.dirac_apply' _ hA]

/-- If the points `X n l`, `l < N n`, are pairwise distinct, the counting measure of a measurable
set is the cardinality of the set of these points lying in it. -/
theorem poissonCountingMeasure_apply_eq_encard (N : ℕ → ℕ) (X : ℕ → ℕ → S)
    (hinj : ∀ a b : ℕ × ℕ, a ≠ b → a.2 < N a.1 → b.2 < N b.1 → X a.1 a.2 ≠ X b.1 b.2)
    {A : Set S}
    (hA : MeasurableSet A) :
    poissonCountingMeasure N X A =
      (A ∩ {x | ∃ n, ∃ l < N n, X n l = x}).encard := by
  classical
  set T : Set (ℕ × ℕ) := {q | q.2 < N q.1 ∧ X q.1 q.2 ∈ A} with hT
  have h1 : ∑' n, ∑ l ∈ Finset.range (N n), A.indicator (1 : S → ℝ≥0∞) (X n l) =
      ∑' q : ℕ × ℕ, T.indicator (1 : ℕ × ℕ → ℝ≥0∞) q := by
    refine Eq.trans ?_
      (ENNReal.tsum_prod (f := fun n l => T.indicator (1 : ℕ × ℕ → ℝ≥0∞) (n, l))).symm
    refine tsum_congr fun n => ?_
    rw [tsum_eq_sum (s := Finset.range (N n))]
    · refine Finset.sum_congr rfl fun l hl => ?_
      have hl' : l < N n := Finset.mem_range.1 hl
      by_cases h : X n l ∈ A <;> simp [Set.indicator, hT, h, hl']
    · intro l hl
      have : ¬ l < N n := fun h => hl (Finset.mem_range.2 h)
      simp [Set.indicator, hT, this]
  have h2 : (fun q : ℕ × ℕ => X q.1 q.2) '' T = A ∩ {x | ∃ n, ∃ l < N n, X n l = x} := by
    ext x
    constructor
    · rintro ⟨⟨n, l⟩, ⟨hl, hx⟩, rfl⟩
      exact ⟨hx, n, l, hl, rfl⟩
    · rintro ⟨hx, n, l, hl, rfl⟩
      exact ⟨⟨n, l⟩, ⟨hl, hx⟩, rfl⟩
  have hinj' : Set.InjOn (fun q : ℕ × ℕ => X q.1 q.2) T := fun a ha b hb hab =>
    by_contra fun hne => hinj a b hne ha.1 hb.1 hab
  rw [poissonCountingMeasure_apply _ _ hA, h1, ← tsum_subtype T (1 : ℕ × ℕ → ℝ≥0∞)]
  simp only [Pi.one_apply]
  rw [ENNReal.tsum_set_one, ← h2, hinj'.encard_image]

omit [MeasurableSpace S] in
/-- Sorting the points of `S` into the disjoint sets `A i`, with one extra category for the
complement. -/
private noncomputable def cellOf {κ : Type*} (A : κ → Set S) (x : S) : Option κ :=
  open Classical in if h : ∃ i, x ∈ A i then some h.choose else none

omit [MeasurableSpace S] in
private lemma cellOf_eq_some_iff {κ : Type*} {A : κ → Set S}
    (hdisj : Pairwise (Function.onFun Disjoint A)) (x : S) (i : κ) :
    cellOf A x = some i ↔ x ∈ A i := by
  classical
  unfold cellOf
  constructor
  · intro h
    by_cases hx : ∃ j, x ∈ A j
    · simp only [hx, ↓reduceDIte, Option.some.injEq] at h
      exact h ▸ hx.choose_spec
    · simp [hx] at h
  · intro hi
    have hx : ∃ j, x ∈ A j := ⟨i, hi⟩
    simp only [hx, ↓reduceDIte, Option.some.injEq]
    by_contra hne
    exact Set.disjoint_left.1 (hdisj hne) hx.choose_spec hi

private lemma measurable_cellOf {κ : Type*} [Finite κ] {A : κ → Set S}
    (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Function.onFun Disjoint A)) :
    @Measurable S (Option κ) _ ⊤ (cellOf A) := by
  have := Fintype.ofFinite κ
  let _ : MeasurableSpace (Option κ) := ⊤
  have : MeasurableSingletonClass (Option κ) := ⟨fun _ => trivial⟩
  refine measurable_to_countable' fun o => ?_
  rcases o with _ | i
  · have : cellOf A ⁻¹' {none} = (⋃ i, A i)ᶜ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
        not_exists]
      constructor
      · intro h i hi
        have := (cellOf_eq_some_iff hdisj x i).2 hi
        simp_all
      · intro h
        by_contra hne
        obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 hne
        exact h i ((cellOf_eq_some_iff hdisj x i).1 hi)
    rw [this]
    exact (MeasurableSet.iUnion hA).compl
  · have : cellOf A ⁻¹' {some i} = A i := by
      ext x; simpa using cellOf_eq_some_iff hdisj x i
    rw [this]; exact hA i

open Classical in
omit [MeasurableSpace S] in
/-- The number of the first `N` points that fall in the cell `o`. -/
private lemma indicator_cell_count {κ : Type*} {A : κ → Set S}
    (hdisj : Pairwise (Function.onFun Disjoint A)) (N : ℕ) (X : ℕ → S) (i : κ) :
    (∑ l ∈ Finset.range N, (A i).indicator (1 : S → ℝ≥0∞) (X l)) =
      ((∑ l ∈ Finset.range N, if cellOf A (X l) = some i then 1 else 0 : ℕ) : ℝ≥0∞) := by
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h : X l ∈ A i
  · simp [h, (cellOf_eq_some_iff hdisj _ i).2 h]
  · simp [h, mt (cellOf_eq_some_iff hdisj _ i).1 h]

/-- **Existence theorem for Poisson processes (Panchenko, Theorem 2.5).** Let `B n = (Nₙ, (Xₙₗ)ₗ)`
be independent random blocks with `Nₙ ~ Po(rₙ)` independent of the i.i.d. sequence
`Xₙₗ ~ νₙ`, and let `M` be the counting measure of all the points `Xₙₗ`, `l < Nₙ`. Let
`μ = ∑ₙ rₙ νₙ`. For pairwise disjoint measurable sets `A i` of finite `μ`-measure, the counts
`M (A i)` are mutually independent and `M (A i) ~ Po(μ (A i))`. -/
theorem iIndepFun_hasLaw_poissonCountingMeasure_apply {Ω κ : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] [Finite κ] (ν : ℕ → Measure S)
    [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0) {B : ℕ → Ω → ℕ × (ℕ → S)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    {μ : Measure S} (hμ : μ = Measure.sum fun n => (r n : ℝ≥0∞) • ν n)
    {M : Ω → Measure S}
    (hM : ∀ ω, M ω = poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l))
    {A : κ → Set S} (hA : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Function.onFun Disjoint A))
    (hfin : ∀ i, μ (A i) ≠ ∞) :
    (∀ i, HasLaw (fun ω => M ω (A i)) (Po((μ (A i)).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)) P) ∧
      iIndepFun (fun i ω => M ω (A i)) P := by
  classical
  have := Fintype.ofFinite κ
  let _ : MeasurableSpace (Option κ) := ⊤
  have : MeasurableSingletonClass (Option κ) := ⟨fun _ => trivial⟩
  set c : S → Option κ := cellOf A with hcdef
  have hc : Measurable c := measurable_cellOf hA hdisj
  -- cell probabilities of the blocks
  set p : ℕ → Option κ → ℝ≥0 := fun n o => (ν n (c ⁻¹' {o})).toNNReal with hp
  have hν : ∀ n o, ν n (c ⁻¹' {o}) = ENNReal.ofNNReal (p n o) := fun n o => by
    simp [hp, ENNReal.coe_toNNReal (measure_ne_top _ _)]
  have hpsum : ∀ n, ∑ o, p n o = 1 := fun n => by
    have h1 : ∑ o, ν n (c ⁻¹' {o}) = 1 := by
      rw [sum_measure_preimage_singleton _ (fun o _ => hc (measurableSet_singleton o))]
      simp
    simp only [hν] at h1
    exact_mod_cast h1
  -- category counts of each block
  set Y : ℕ → Option κ → Ω → ℕ := fun n o ω =>
    ∑ l ∈ Finset.range (B n ω).1, if c ((B n ω).2 l) = o then 1 else 0 with hY
  have hYlaw : ∀ n, HasLaw (fun ω o => Y n o ω) (Measure.pi fun o => Po(r n * p n o)) P :=
    fun n => hasLaw_counts_poisson_thinning_of_hasLaw_prod (ν n) (r n) hc (p n) (hpsum n)
      (hν n) (hlaw n)
  have hYo : ∀ n o, HasLaw (Y n o) Po(r n * p n o) P := fun n o =>
    (measurePreserving_eval (fun o => Po(r n * p n o)) o).hasLaw.comp (hYlaw n)
  have h2 : ∀ n, iIndepFun (Y n) P := fun n => (iIndepFun_iff_hasLaw_pi_pi (hYo n)).2 (hYlaw n)
  have hG : Measurable fun b : ℕ × (ℕ → S) => fun o : Option κ =>
      ∑ l ∈ Finset.range b.1, if c (b.2 l) = o then 1 else 0 :=
    measurable_categoryCounts.comp (by fun_prop : Measurable fun b : ℕ × (ℕ → S) =>
      (b.1, fun l => c (b.2 l)))
  have hmeasY : ∀ n o, Measurable (Y n o) := fun n o =>
    (measurable_pi_apply o).comp (hG.comp (hBm n))
  have h1 : iIndepFun (fun n ω => (Y n · ω)) P :=
    hB.comp (fun _ b => fun o : Option κ => ∑ l ∈ Finset.range b.1, if c (b.2 l) = o then 1 else 0)
      fun _ => hG
  have hall : iIndepFun (fun (q : ℕ × Option κ) ω => Y q.1 q.2 ω) P :=
    iIndepFun_uncurry' hmeasY h1 h2
  -- the series over blocks, one cell at a time
  have hrows : iIndepFun (fun o ω => (fun n => Y n o ω)) P :=
    iIndepFun.curry' (X := fun o n ω => Y n o ω) (fun o n => hmeasY n o)
      (hall.precomp (g := Prod.swap) Prod.swap_injective)
  have hK : iIndepFun (fun (i : κ) ω => ∑' n, (Y n (some i) ω : ℝ≥0∞)) P :=
    (hrows.precomp (g := some) (Option.some_injective κ)).comp
      (fun _ v => ∑' n, (v n : ℝ≥0∞))
      (fun _ => Measurable.tsum fun n =>
        (measurable_of_countable (Nat.cast : ℕ → ℝ≥0∞)).comp (measurable_pi_apply n))
  have hMeq : ∀ i ω, M ω (A i) = ∑' n, (Y n (some i) ω : ℝ≥0∞) := fun i ω => by
    rw [hM, poissonCountingMeasure_apply _ _ (hA i)]
    refine tsum_congr fun n => ?_
    exact indicator_cell_count hdisj _ _ i
  -- the laws
  have hμA : ∀ i, μ (A i) = ∑' n, (r n : ℝ≥0∞) * ν n (A i) := fun i => by
    simp [hμ, Measure.sum_apply _ (hA i)]
  have hterm : ∀ n i, ((r n : ℝ≥0∞) * ν n (A i)) ≠ ∞ := fun n i =>
    ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)
  have hpA : ∀ n i, p n (some i) = (ν n (A i)).toNNReal := fun n i => by
    simp only [hp, hcdef]
    congr 2
    ext x; simpa using cellOf_eq_some_iff hdisj x i
  have hrate : ∀ i, (fun n => r n * p n (some i)) = fun n =>
      ((r n : ℝ≥0∞) * ν n (A i)).toNNReal := fun i => by
    ext n; simp [hpA, ENNReal.toNNReal_mul]
  have hsum : ∀ i, Summable fun n => r n * p n (some i) := fun i => by
    rw [hrate]
    exact ENNReal.summable_toNNReal_of_tsum_ne_top (by rw [← hμA]; exact hfin i)
  have htsum : ∀ i, ∑' n, r n * p n (some i) = (μ (A i)).toNNReal := fun i => by
    rw [hrate, hμA, ENNReal.tsum_toNNReal_eq (hterm · i)]
  have hKnat : ∀ i, HasLaw (fun ω => ∑' n, Y n (some i) ω) Po((μ (A i)).toNNReal) P :=
    fun i => by
      rw [← htsum]
      exact (hall.precomp (g := fun n => (n, some i))
        (fun a b hab => by simpa using hab)).hasLaw_tsum_poissonMeasure
        (fun n => hYo n (some i)) (hsum i)
  have hae : ∀ i, (fun ω => M ω (A i)) =ᵐ[P]
      fun ω => (((∑' n, Y n (some i) ω : ℕ)) : ℝ≥0∞) := fun i => by
    filter_upwards [ae_summable_natCast_of_hasLaw_poissonMeasure
      (fun n => hYo n (some i)) (hsum i)] with ω hω
    rw [hMeq]
    have hs : Summable fun n => Y n (some i) ω := summable_of_summable_natCast hω
    have := hs.hasSum.map (Nat.castAddMonoidHom ℝ≥0∞) continuous_of_discreteTopology
    simpa [Function.comp_def] using this.tsum_eq
  refine ⟨fun i => ?_,
    iIndepFun.congr (fun i => ae_of_all P fun ω => (hMeq i ω).symm) hK⟩
  have hcast : HasLaw (fun ω => ((∑' n, Y n (some i) ω : ℕ) : ℝ≥0∞))
      (Po((μ (A i)).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞)) P :=
    (⟨(measurable_of_countable (Nat.cast : ℕ → ℝ≥0∞)).aemeasurable, rfl⟩ : HasLaw
      (Nat.cast : ℕ → ℝ≥0∞) (Po((μ (A i)).toNNReal).map (Nat.cast : ℕ → ℝ≥0∞))
      Po((μ (A i)).toNNReal)).comp (hKnat i)
  exact hcast.congr (hae i)

/-- Independent Poisson blocks exist: on the product space `ℕ → ℕ × (ℕ → S)` with the product of
the laws `Po(rₙ) ⊗ νₙ^{⊗ℕ}`, the coordinate maps are measurable, independent, and have these
laws. -/
theorem exists_poissonBlocks (ν : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ν n)]
    (r : ℕ → ℝ≥0) :
    ∃ P : Measure (ℕ → ℕ × (ℕ → S)), IsProbabilityMeasure P ∧
      (∀ n, Measurable fun ω : ℕ → ℕ × (ℕ → S) => ω n) ∧
      iIndepFun (fun n (ω : ℕ → ℕ × (ℕ → S)) => ω n) P ∧
      ∀ n, HasLaw (fun ω : ℕ → ℕ × (ℕ → S) => ω n)
        (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P :=
  ⟨Measure.infinitePi fun n => Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n),
    inferInstance, fun n => measurable_pi_apply n,
    iIndepFun_infinitePi (X := fun _ x => x) fun _ => measurable_id,
    fun n => hasLaw_eval_infinitePi
      (fun n => Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) n⟩

/-- **Simplicity.** If the laws `νₙ` of the blocks that actually carry mass (`rₙ ≠ 0`) have no
atoms, then almost surely all the sampled points `Xₙₗ`, `l < Nₙ`, are pairwise distinct, so the
counting measure counts each point of the random set only once. Blocks of zero intensity are
a.s. empty and may have arbitrary law. -/
theorem ae_pairwise_ne_poissonBlocks [MeasurableEq S] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ν : ℕ → Measure S)
    [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0) {B : ℕ → Ω → ℕ × (ℕ → S)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hnull : ∀ n, r n ≠ 0 → NullSingletonClass (ν n)) :
    ∀ᵐ ω ∂P, ∀ a b : ℕ × ℕ, a ≠ b → a.2 < (B a.1 ω).1 → b.2 < (B b.1 ω).1 →
      (B a.1 ω).2 a.2 ≠ (B b.1 ω).2 b.2 := by
  have hsamp : ∀ n, HasLaw (fun ω => (B n ω).2) (Measure.infinitePi fun _ : ℕ => ν n) P :=
    fun n => measurePreserving_snd.hasLaw.comp (hlaw n)
  have hpoint : ∀ n l, HasLaw (fun ω => (B n ω).2 l) (ν n) P := fun n l =>
    (hasLaw_eval_infinitePi (fun _ : ℕ => ν n) l).comp (hsamp n)
  have hmeas : ∀ n l, Measurable fun ω => (B n ω).2 l := fun n l =>
    (measurable_pi_apply l).comp (measurable_snd.comp (hBm n))
  have h2 : ∀ n, iIndepFun (fun l ω => (B n ω).2 l) P := fun n =>
    (iIndepFun_iff_hasLaw_Pi_infinitePi (hpoint n) (hsamp n).aemeasurable).2 (hsamp n)
  have h1 : iIndepFun (fun n ω => fun l => (B n ω).2 l) P :=
    hB.comp (fun _ b => b.2) fun _ => measurable_snd
  have hall := iIndepFun_uncurry' (X := fun n l ω => (B n ω).2 l) hmeas h1 h2
  -- blocks of zero intensity are empty
  have hempty : ∀ᵐ ω ∂P, ∀ n, r n = 0 → (B n ω).1 = 0 := by
    refine ae_all_iff.2 fun n => ?_
    by_cases hn : r n = 0
    · have hN : HasLaw (fun ω => (B n ω).1) Po(r n) P :=
        measurePreserving_fst.hasLaw.comp (hlaw n)
      have hnull0 : P {ω | (B n ω).1 ≠ 0} = 0 := by
        rw [hN.measure_eq (p := fun k => k ≠ 0) (measurableSet_singleton 0).compl, hn,
          poissonMeasure_zero]
        simp
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull0] with ω hω _
      simpa using hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hn
  -- distinctness among the blocks that carry mass
  let I := {q : ℕ × ℕ // r q.1 ≠ 0}
  have hsub := (hall.precomp (g := fun q : I => q.1) Subtype.val_injective).ae_pairwise_ne
    (fun q => (hmeas q.1.1 q.1.2).aemeasurable) fun q => by
      have := hnull q.1.1 q.2
      rw [(hpoint q.1.1 q.1.2).map_eq]; exact this
  filter_upwards [hsub, hempty] with ω hω hz a b hab ha hb
  have hra : r a.1 ≠ 0 := fun h => by simp [hz _ h] at ha
  have hrb : r b.1 ≠ 0 := fun h => by simp [hz _ h] at hb
  exact hω (i := ⟨a, hra⟩) (j := ⟨b, hrb⟩) (fun h => hab (congrArg Subtype.val h))

/-- Almost surely, the counting measure of every measurable set is the number of points of the
random set `Π = {Xₙₗ : l < Nₙ}` lying in it. -/
theorem ae_poissonCountingMeasure_eq_encard [MeasurableEq S] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (ν : ℕ → Measure S)
    [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0) {B : ℕ → Ω → ℕ × (ℕ → S)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hnull : ∀ n, r n ≠ 0 → NullSingletonClass (ν n)) :
    ∀ᵐ ω ∂P, ∀ A : Set S, MeasurableSet A →
      poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l) A =
        (A ∩ {x | ∃ n, ∃ l < (B n ω).1, (B n ω).2 l = x}).encard := by
  filter_upwards [ae_pairwise_ne_poissonBlocks ν r hBm hB hlaw hnull] with ω hω A hA
  exact poissonCountingMeasure_apply_eq_encard _ _ hω hA

end SpinGlasses
