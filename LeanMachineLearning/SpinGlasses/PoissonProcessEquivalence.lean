/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonProcess
public import LeanMachineLearning.ForMathlib.Probability.HasCondDistrib
public import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Poisson blocks: conditional sampling, Campbell's formula and Giry-law uniqueness

The conditional i.i.d. law is expressed on the block coordinates, without attempting to
canonically enumerate the points of an arbitrary counting measure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpinGlasses

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

/-- Conditionally on a Poisson block's count, its entire sample sequence is i.i.d.
This is stronger than the assertion concerning only the first `N` points. -/
theorem hasCondDistrib_poissonBlockSamples {P : Measure Ω} [IsProbabilityMeasure P]
    (ν : Measure S) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {B : Ω → ℕ × (ℕ → S)}
    (hB : HasLaw B (Po(r).prod (Measure.infinitePi fun _ : ℕ => ν)) P) :
    HasCondDistrib (fun ω => (B ω).2) (fun ω => (B ω).1)
      (ProbabilityTheory.Kernel.const ℕ (Measure.infinitePi fun _ : ℕ => ν)) P := by
  have hN : HasLaw (fun ω => (B ω).1) Po(r) P :=
    measurePreserving_fst.hasLaw.comp hB
  have hX : HasLaw (fun ω => (B ω).2) (Measure.infinitePi fun _ : ℕ => ν) P :=
    measurePreserving_snd.hasLaw.comp hB
  exact ((indepFun_iff_hasLaw_prodMk_prod hN hX).2 hB).hasCondDistrib_const hN.aemeasurable hX

/-- Campbell's formula for a family of independent Poisson blocks. No atomlessness or
independence is needed for this expectation identity once each block law is known. -/
theorem lintegral_poissonCountingMeasure {P : Measure Ω}
    (ν : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → S)}
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    {f : S → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, ∫⁻ s, f s ∂poissonCountingMeasure
      (fun n => (B n ω).1) (fun n l => (B n ω).2 l) ∂P =
      ∫⁻ s, f s ∂Measure.sum (fun n => (r n : ℝ≥0∞) • ν n) := by
  have hg : Measurable fun q : ℕ × (ℕ → S) =>
      ∑ l ∈ Finset.range q.1, f (q.2 l) := by
    apply measurable_from_prod_countable_right
    intro k
    change Measurable fun y : ℕ → S => ∑ l ∈ Finset.range k, f (y l)
    exact Finset.measurable_sum _ fun l _ => hf.comp (measurable_pi_apply l)
  have hm : ∀ n, AEMeasurable (fun ω =>
      ∑ l ∈ Finset.range (B n ω).1, f ((B n ω).2 l)) P := fun n =>
    hg.comp_aemeasurable (hlaw n).aemeasurable
  simp only [poissonCountingMeasure, lintegral_sum_measure, lintegral_finsetSum_measure,
    lintegral_dirac' _ hf]
  rw [lintegral_tsum (fun n => hm n)]
  congr 1
  ext n
  rw [lintegral_smul_measure, (hlaw n).lintegral_comp hg.aemeasurable]
  rw [lintegral_prod _ hg.aemeasurable]
  have hinner (k : ℕ) :
      (∫⁻ x : ℕ → S, ∑ l ∈ Finset.range k, f (x l) ∂
        Measure.infinitePi fun _ : ℕ => ν n) =
        ∑ l ∈ Finset.range k, ∫⁻ s, f s ∂ν n := by
    rw [lintegral_finsetSum (Finset.range k)
      (f := fun l (x : ℕ → S) => f (x l))
      (fun l _ => hf.comp (measurable_pi_apply l))]
    congr 1
    ext l
    exact (hasLaw_eval_infinitePi (fun _ : ℕ => ν n) l).lintegral_comp
      hf.aemeasurable
  simp_rw [hinner, Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul]
  rw [lintegral_mul_const (∫⁻ s, f s ∂ν n)
    (measurable_of_countable _ : Measurable fun k : ℕ => (k : ℝ≥0∞))]
  rw [lintegral_natCast_poissonMeasure]
  rfl

/-- If the points of block `n` lie in the cell `A n` of a pairwise disjoint family, the counting
measure restricted to that cell is exactly the counting measure of block `n`. -/
theorem poissonCountingMeasure_restrict_partition
    (N : ℕ → ℕ) (X : ℕ → ℕ → S) (A : ℕ → Set S)
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (hX : ∀ n l, l < N n → X n l ∈ A n)
    (hA : ∀ n, MeasurableSet (A n)) (n : ℕ) :
    (poissonCountingMeasure N X).restrict (A n) =
      ∑ l ∈ Finset.range (N n), Measure.dirac (X n l) := by
  classical
  ext t ht
  rw [Measure.restrict_apply ht, poissonCountingMeasure_apply N X (ht.inter (hA n)),
    tsum_eq_single n, Measure.finsetSum_apply]
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hmem := hX n l (Finset.mem_range.mp hl)
    by_cases h : X n l ∈ t <;> simp [Measure.dirac_apply' _ ht, Set.indicator, h, hmem]
  · intro m hmn
    refine Finset.sum_eq_zero fun l hl => ?_
    have hnot : X m l ∉ t ∩ A n := fun h =>
      Set.disjoint_left.mp (hdisj hmn) (hX m l (Finset.mem_range.mp hl)) h.2
    simp [Set.indicator, hnot]

/-- A block construction supported on pairwise disjoint partition cells has exactly its
block horizon as the counting measure of each cell. This deterministic identity is valid
without atomlessness: repeated points are counted with multiplicity. -/
theorem poissonCountingMeasure_partition_apply
    (N : ℕ → ℕ) (X : ℕ → ℕ → S) (A : ℕ → Set S)
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (hX : ∀ n l, l < N n → X n l ∈ A n)
    (hA : ∀ n, MeasurableSet (A n)) (n : ℕ) :
    (poissonCountingMeasure N X) (A n) = (N n : ℝ≥0∞) := by
  rw [← Measure.restrict_apply_univ,
    poissonCountingMeasure_restrict_partition N X A hdisj hX hA n, Measure.finsetSum_apply]
  simp

/-- In the independent-block representation, the counts on partition cells have the
prescribed joint Poisson law. The full configuration law is the pushforward of these blocks;
this avoids choosing an enumeration of the atoms of a general random counting measure. -/
theorem hasLaw_partitionBlockCounts {P : Measure Ω}
    (ν : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → S)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P) :
    HasLaw (fun ω n => (B n ω).1) (Measure.infinitePi fun n => Po(r n)) P := by
  have hi : iIndepFun (fun n ω => (B n ω).1) P :=
    hB.comp (fun _ b => b.1) fun _ => measurable_fst
  have hcount : ∀ n, HasLaw (fun ω => (B n ω).1) (Po(r n)) P :=
    fun n => measurePreserving_fst.hasLaw.comp (hlaw n)
  refine ⟨(measurable_pi_iff.2 fun n => measurable_fst.comp (hBm n)).aemeasurable, ?_⟩
  simpa only [Function.comp_def,
    show (fun n => P.map (fun ω => (B n ω).1)) =
      (fun n => Po(r n)) from funext fun n => (hcount n).map_eq] using
    hi.map_fun_eq_infinitePi_map (fun n => measurable_fst.comp (hBm n))

/-- Counts of partition cells have the joint product-Poisson law when the block samples
are supported in their respective cells. This packages the deterministic evaluation
identity with the independent-block count theorem. -/
theorem hasLaw_poissonCountingMeasure_partition_apply {P : Measure Ω}
    (ν : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → S)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (A : ℕ → Set S) (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (hsupport : ∀ ω n l, l < (B n ω).1 → (B n ω).2 l ∈ A n) :
    HasLaw (fun ω n => (poissonCountingMeasure (fun m => (B m ω).1)
      (fun m l => (B m ω).2 l)) (A n))
      (Measure.infinitePi fun n => (Po(r n)).map (Nat.cast : ℕ → ℝ≥0∞)) P := by
  have heq : (fun ω n => (poissonCountingMeasure (fun m => (B m ω).1)
      (fun m l => (B m ω).2 l)) (A n)) =
      (fun ω n => ((B n ω).1 : ℝ≥0∞)) := by
    funext ω n
    exact poissonCountingMeasure_partition_apply _ _ A hdisj (hsupport ω) hA n
  rw [heq]
  have hcast : HasLaw (fun x : ℕ → ℕ => fun n => (x n : ℝ≥0∞))
      (Measure.infinitePi fun n => (Po(r n)).map (Nat.cast : ℕ → ℝ≥0∞))
      (Measure.infinitePi fun n => Po(r n)) := by
    have hc : Measurable (Nat.cast : ℕ → ℝ≥0∞) := measurable_of_countable _
    exact ⟨(measurable_pi_iff.2 fun n => hc.comp (measurable_pi_apply n)).aemeasurable,
      Measure.infinitePi_map_pi (μ := fun n => Po(r n)) (fun _ => hc)⟩
  exact hcast.fun_comp (hasLaw_partitionBlockCounts ν r hBm hB hlaw)

/-- Joint law of the evaluations on finitely many disjoint measurable sets: independent
Poisson counts, where a set of infinite intensity carries the point mass at `∞`. The law depends
on the construction only through the intensity `μ = ∑ₙ rₙ νₙ`. -/
theorem hasLaw_poissonCountingMeasure_disjoint {κ : Type*} [Fintype κ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ν : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → S)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    {μ : Measure S} (hμ : μ = Measure.sum fun n => (r n : ℝ≥0∞) • ν n)
    {A : κ → Set S} (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) :
    HasLaw (fun ω i => (poissonCountingMeasure (fun n => (B n ω).1)
      (fun n l => (B n ω).2 l)) (A i))
      (Measure.pi fun i => if μ (A i) = ∞ then Measure.dirac ∞ else
        (Po((μ (A i)).toNNReal)).map (Nat.cast : ℕ → ℝ≥0∞)) P := by
  obtain ⟨hlaws, hind⟩ := iIndepFun_hasLaw_poissonCountingMeasure_apply
    ν r hBm hB hlaw hμ (M := fun ω => poissonCountingMeasure
      (fun n => (B n ω).1) (fun n l => (B n ω).2 l)) (fun _ => rfl) hA hdisj
  exact (iIndepFun_iff_hasLaw_pi_pi hlaws).1 hind

end SpinGlasses

namespace MeasureTheory

/-- To compare finite-dimensional laws of random measures, it suffices to compare their
joint evaluations on finite disjoint measurable families. No finiteness of the values of
the random measures is required. -/
theorem Measure.map_finset_eval_eq_of_disjoint {α Ω Ω' : Type*}
    [MeasurableSpace α] [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {X : Ω → Measure α} {Y : Ω' → Measure α}
    (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ (κ : Type (max u_1 0)) [Fintype κ] (A : κ → Set α),
      (∀ i, MeasurableSet (A i)) → Pairwise (Function.onFun Disjoint A) →
      P.map (fun ω i => X ω (A i)) = Q.map (fun ω i => Y ω (A i)))
    (t : Finset {s : Set α // MeasurableSet s}) :
    P.map (fun ω (s : t) => X ω s.1) = Q.map (fun ω (s : t) => Y ω s.1) := by
  classical
  let κ := t → Bool
  let A : κ → Set α := fun v =>
    ⋂ s : t, if v s then s.1.1 else s.1.1ᶜ
  have hA : ∀ v, MeasurableSet (A v) := by
    intro v
    exact MeasurableSet.iInter fun s => by
      split
      · exact s.1.2
      · exact s.1.2.compl
  have hd : Pairwise (Function.onFun Disjoint A) := by
    intro v w hvw
    have ⟨s, hs⟩ : ∃ s, v s ≠ w s := by
      by_contra hn
      apply hvw
      funext s
      by_contra hne
      exact hn ⟨s, hne⟩
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hx' := Set.mem_iInter.mp hx s
    have hy' := Set.mem_iInter.mp hy s
    by_cases hv : v s = true <;> cases hw : w s <;> simp_all
  have hpartition : ∀ s : t, s.1.1 = ⋃ v : {v : κ // v s}, A v := by
    intro s
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      let v : κ := fun u => decide (x ∈ u.1.1)
      refine ⟨⟨v, by exact decide_eq_true hx⟩, Set.mem_iInter.mpr fun u => ?_⟩
      change x ∈ if v u then u.1.1 else u.1.1ᶜ
      by_cases hu : x ∈ u.1.1
      · simpa only [show v u = true from decide_eq_true hu, ite_true] using hu
      · simpa only [show v u = false from decide_eq_false hu, Bool.false_eq_true, ite_false,
          Set.mem_compl_iff] using hu
    · rintro ⟨v, hv⟩
      have hs := Set.mem_iInter.mp hv s
      change x ∈ if v.1 s then s.1.1 else s.1.1ᶜ at hs
      simpa [v.2] using hs
  let F : (κ → ℝ≥0∞) → t → ℝ≥0∞ := fun z s =>
    ∑ v : {v : κ // v s}, z v.1
  have hF (m : Measure α) (s : t) : m s.1.1 = F (fun v => m (A v)) s := by
    rw [hpartition s]
    have hh := measure_iUnion (μ := m) (f := fun v : {v : κ // v s} => A v.1)
      (fun v w hv => hd (Subtype.val_injective.ne hv)) (fun v => hA v.1)
    simpa only [tsum_fintype] using hh
  have hFX : (fun ω (s : t) => X ω s.1) = fun ω => F (fun v => X ω (A v)) :=
    funext fun ω => funext fun s => hF (X ω) s
  have hFY : (fun ω (s : t) => Y ω s.1) = fun ω => F (fun v => Y ω (A v)) :=
    funext fun ω => funext fun s => hF (Y ω) s
  have hFm : Measurable F := measurable_pi_iff.mpr fun s =>
    Finset.measurable_sum _ fun v _ => measurable_pi_apply v.1
  rw [hFX, hFY]
  have he := h κ A hA hd
  have hXe : Measurable (fun ω : Ω => fun v => X ω (A v)) :=
    measurable_pi_iff.mpr fun v => (Measure.measurable_coe (hA v)).comp hX
  have hYe : Measurable (fun ω : Ω' => fun v => Y ω (A v)) :=
    measurable_pi_iff.mpr fun v => (Measure.measurable_coe (hA v)).comp hY
  calc
    P.map (fun ω => F (fun v => X ω (A v))) =
        (P.map (fun ω v => X ω (A v))).map F := by
      rw [Measure.map_map hFm hXe]
      rfl
    _ = (Q.map (fun ω v => Y ω (A v))).map F := by rw [he]
    _ = Q.map (fun ω => F (fun v => Y ω (A v))) := by
      rw [Measure.map_map hFm hYe]
      rfl

/-- Finite-dimensional distributions of evaluations on measurable sets determine the law
of a random measure. This does not require a countable generating class on the base space. -/
theorem Measure.map_eq_of_finset_eval_eq {α Ω Ω' : Type*}
    [MeasurableSpace α] [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsFiniteMeasure P]
    {X : Ω → Measure α} {Y : Ω' → Measure α}
    (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ (t : Finset {s : Set α // MeasurableSet s}),
      P.map (fun ω (s : t) => X ω s.1) =
        Q.map (fun ω (s : t) => Y ω s.1)) :
    P.map X = Q.map Y := by
  let e : {s : Set α // MeasurableSet s} → Measure α → ℝ≥0∞ := fun s μ => μ s.1
  have he : ∀ s, Measurable (e s) := fun s => Measure.measurable_coe s.2
  have hm : P.map (fun ω s => e s (X ω)) =
      Q.map (fun ω s => e s (Y ω)) := by
    let R := P.map (fun ω s => e s (X ω))
    let T := Q.map (fun ω s => e s (Y ω))
    have hr : IsProjectiveLimit R (fun t =>
        P.map (fun ω (s : t) => X ω s.1)) := by
      intro t
      dsimp only [R]
      rw [show (P.map (fun ω s => e s (X ω))).map t.restrict =
        P.map (fun ω => t.restrict (fun s => e s (X ω))) from by
        simpa only [Function.comp_def] using
          (Measure.map_map (Finset.measurable_restrict t)
            (measurable_pi_iff.2 (fun s => (he s).comp hX)))]
      rfl
    have ht : IsProjectiveLimit T (fun t =>
        P.map (fun ω (s : t) => X ω s.1)) := by
      intro t
      dsimp only [T]
      rw [show (Q.map (fun ω s => e s (Y ω))).map t.restrict =
        Q.map (fun ω => t.restrict (fun s => e s (Y ω))) from by
        simpa only [Function.comp_def] using
          (Measure.map_map (Finset.measurable_restrict t)
            (measurable_pi_iff.2 (fun s => (he s).comp hY)))]
      exact (h t).symm
    have (t : Finset {s : Set α // MeasurableSet s}) :
        IsFiniteMeasure (P.map (fun ω (s : t) => X ω s.1)) :=
      Measure.isFiniteMeasure_map P _
    exact hr.unique ht
  have hspace : (inferInstance : MeasurableSpace (Measure α)) =
      MeasurableSpace.comap (fun μ => fun s => e s μ) inferInstance := by
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    change (⨆ (s : Set α) (_ : MeasurableSet s),
      (borel ℝ≥0∞).comap (fun μ : Measure α => μ s)) = _
    rw [iSup_subtype']
    simp only [MeasurableSpace.comap_comp]
    rfl
  have : IsFiniteMeasure (P.map X) := Measure.isFiniteMeasure_map P X
  apply ext_of_generate_finite
    {t : Set (Measure α) | ∃ (I : Finset {s : Set α // MeasurableSet s})
      (U : Set (I → ℝ≥0∞)), MeasurableSet U ∧
        t = (fun μ (s : I) => e s μ) ⁻¹' U} ?_ ?_ ?_ ?_
  · change (inferInstance : MeasurableSpace (Measure α)) = _
    rw [hspace, ← generateFrom_measurableCylinders,
      MeasurableSpace.comap_generateFrom]
    congr 1
    ext t
    simp only [Set.mem_image, mem_measurableCylinders, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, ⟨I, U, hU, rfl⟩, rfl⟩
      exact ⟨I, U, hU, rfl⟩
    · rintro ⟨I, U, hU, rfl⟩
      exact ⟨cylinder I U, ⟨I, U, hU, rfl⟩, rfl⟩
  · have hc : {t : Set (Measure α) | ∃ (I : Finset {s : Set α // MeasurableSet s})
        (U : Set (I → ℝ≥0∞)), MeasurableSet U ∧
          t = (fun μ (s : I) => e s μ) ⁻¹' U} =
        {t | ∃ u ∈ measurableCylinders (fun _ : {s : Set α // MeasurableSet s} =>
          ℝ≥0∞), (fun μ : Measure α => fun s => e s μ) ⁻¹' u = t} := by
      ext t
      simp only [Set.mem_ofPred_eq, mem_measurableCylinders]
      constructor
      · rintro ⟨I, U, hU, rfl⟩
        exact ⟨cylinder I U, ⟨I, U, hU, rfl⟩, rfl⟩
      · rintro ⟨u, ⟨I, U, hU, rfl⟩, rfl⟩
        exact ⟨I, U, hU, rfl⟩
    rw [hc]
    exact (isPiSystem_measurableCylinders).comap _
  · rintro t ⟨I, U, hU, rfl⟩
    have hI : Measurable (fun μ : Measure α => fun s : I => e s μ) :=
      measurable_pi_iff.2 (fun s => he s.1)
    rw [Measure.map_apply hX (hI hU), Measure.map_apply hY (hI hU)]
    have hc := h I
    have hc' : P.map (fun ω (s : I) => e s (X ω)) =
        Q.map (fun ω (s : I) => e s (Y ω)) := hc
    have heval := congrArg (fun m : Measure (I → ℝ≥0∞) => m U) hc'
    have hmI : Measurable (fun ω : Ω => fun s : I => e s.1 (X ω)) :=
      measurable_pi_iff.2 (fun s => (he s.1).comp hX)
    have hmJ : Measurable (fun ω : Ω' => fun s : I => e s.1 (Y ω)) :=
      measurable_pi_iff.2 (fun s => (he s.1).comp hY)
    rw [Measure.map_apply hmI hU, Measure.map_apply hmJ hU] at heval
    exact heval
  · rw [Measure.map_apply hX MeasurableSet.univ,
      Measure.map_apply hY MeasurableSet.univ]
    simp only [Set.preimage_univ]
    have hh := congrArg (fun m : Measure ({s : Set α // MeasurableSet s} → ℝ≥0∞) =>
      m Set.univ) hm
    have hmX : Measurable (fun ω s => e s (X ω)) :=
      measurable_pi_iff.2 (fun s => (he s).comp hX)
    have hmY : Measurable (fun ω s => e s (Y ω)) :=
      measurable_pi_iff.2 (fun s => (he s).comp hY)
    rw [Measure.map_apply hmX MeasurableSet.univ,
      Measure.map_apply hmY MeasurableSet.univ] at hh
    simpa only [Set.preimage_univ] using hh

/-- Equality of joint evaluation laws on disjoint measurable families determines the Giry law.
No countable generating class on the base space is required. -/
theorem Measure.map_eq_of_disjoint_eval_eq {α Ω Ω' : Type*}
    [MeasurableSpace α] [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsFiniteMeasure P]
    {X : Ω → Measure α} {Y : Ω' → Measure α}
    (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ (κ : Type (max u_1 0)) [Fintype κ] (A : κ → Set α),
      (∀ i, MeasurableSet (A i)) → Pairwise (Function.onFun Disjoint A) →
      P.map (fun ω i => X ω (A i)) = Q.map (fun ω i => Y ω (A i))) :
    P.map X = Q.map Y :=
  Measure.map_eq_of_finset_eval_eq hX hY
    (Measure.map_finset_eval_eq_of_disjoint hX hY h)

end MeasureTheory

namespace SpinGlasses

variable {S : Type*} [MeasurableSpace S]

/-- **Equivalence of constructions (Panchenko, Theorem 2.4).** Two independent-block
constructions with the same intensity `∑ₙ rₙ νₙ = ∑ₘ r'ₘ ν'ₘ` produce counting measures with
the same law on the space of measures, even if the decompositions into blocks differ. -/
theorem identDistrib_poissonCountingMeasure_of_intensity_eq {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (ν : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    (ν' : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ν' n)] (r' : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → S)} (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    {B' : ℕ → Ω' → ℕ × (ℕ → S)} (hBm' : ∀ n, Measurable (B' n)) (hB' : iIndepFun B' Q)
    (hlaw' : ∀ n, HasLaw (B' n) (Po(r' n).prod (Measure.infinitePi fun _ : ℕ => ν' n)) Q)
    (hμ : (Measure.sum fun n => (r n : ℝ≥0∞) • ν n) =
      Measure.sum fun n => (r' n : ℝ≥0∞) • ν' n) :
    IdentDistrib (fun ω => poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l))
      (fun ω => poissonCountingMeasure (fun n => (B' n ω).1) (fun n l => (B' n ω).2 l))
      P Q := by
  have hM := measurable_poissonCountingMeasure_comp hBm
  have hM' := measurable_poissonCountingMeasure_comp hBm'
  refine ⟨hM.aemeasurable, hM'.aemeasurable, ?_⟩
  refine Measure.map_eq_of_disjoint_eval_eq hM hM' fun κ _ A hA hdisj => ?_
  rw [(hasLaw_poissonCountingMeasure_disjoint ν r hBm hB hlaw rfl hA hdisj).map_eq,
    (hasLaw_poissonCountingMeasure_disjoint ν' r' hBm' hB' hlaw' hμ hA hdisj).map_eq]

end SpinGlasses
