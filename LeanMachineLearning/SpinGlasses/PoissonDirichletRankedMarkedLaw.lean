/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeMarked
public import LeanMachineLearning.SpinGlasses.PoissonDirichletMarkedLaw
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.InfinitePiCurryRestrict
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.MapPairInfinitePi
public import LeanMachineLearning.ForMathlib.Probability.InfinitePiZip

/-!
# Ranked atoms with i.i.d. marks attached by rank

For the ranked atoms `uₙ` of a ζ-Poisson process and marks `Yₙ` that are i.i.d. and independent of
the process, the law of `∑ uₙ X(Yₙ)` is that of the same sum when the marks are attached to the
sampled *points* of the Poisson blocks. The two differ by a rank bijection that depends only on the
blocks; for each fixed block configuration an i.i.d. array is invariant under such a bijection,
so no measurability of the bijection is required.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SpinGlasses

variable {T : Type*} [MeasurableSpace T]

/-- For a fixed block configuration with positive distinct summable active masses, the sum of
the masses times marks attached to the *points* has the same law as the sum of the *ranked* masses
times marks attached by rank, when the marks are i.i.d. -/
theorem map_tsum_active_mul_eq_map_tsum_ranked_mul
    (b : ℕ → ℕ × (ℕ → ℝ)) [Infinite {q : ℕ × ℕ // q.2 < (b q.1).1}]
    (hpos : ∀ q : {q : ℕ × ℕ // q.2 < (b q.1).1}, 0 < (b q.1.1).2 q.1.2)
    (hinj : Function.Injective fun q : {q : ℕ × ℕ // q.2 < (b q.1).1} => (b q.1.1).2 q.1.2)
    (hs : Summable fun q : {q : ℕ × ℕ // q.2 < (b q.1).1} => (b q.1.1).2 q.1.2)
    (τ : Measure T) [IsProbabilityMeasure τ] {X : T → ℝ} (hX : Measurable X) :
    (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => τ).map
        (fun y' => ∑' q : {q : ℕ × ℕ // q.2 < (b q.1).1},
          ENNReal.ofReal ((b q.1.1).2 q.1.2 * X (y' q.1.1 q.1.2))) =
      (Measure.infinitePi fun _ : ℕ => τ).map
        (fun y => ∑' n, nthLargestAtom n (poissonCountingMeasure
          (fun k => (b k).1) (fun k l => (b k).2 l)) * ENNReal.ofReal (X (y n))) := by
  obtain ⟨e, he⟩ := exists_equiv_nthLargestAtom_sum_dirac
    (fun q : {q : ℕ × ℕ // q.2 < (b q.1).1} => (b q.1.1).2 q.1.2) hinj hpos hs
  have hM := poissonCountingMeasure_eq_sum_dirac (fun k => (b k).1) (fun k l => (b k).2 l)
  have hsum : ∀ y' : ℕ → ℕ → T,
      (∑' q : {q : ℕ × ℕ // q.2 < (b q.1).1},
        ENNReal.ofReal ((b q.1.1).2 q.1.2 * X (y' q.1.1 q.1.2))) =
      ∑' n, nthLargestAtom n (poissonCountingMeasure
          (fun k => (b k).1) (fun k l => (b k).2 l)) *
        ENNReal.ofReal (X (y' (e.symm n).1.1 (e.symm n).1.2)) := by
    intro y'
    rw [← e.symm.tsum_eq]
    refine tsum_congr fun n => ?_
    rw [hM, ENNReal.ofReal_mul (hpos _).le]
    have := he (e.symm n)
    rw [Equiv.apply_symm_apply] at this
    rw [this]
  have hm : Measurable fun y' : ℕ → ℕ → T => fun n : ℕ => y' (e.symm n).1.1 (e.symm n).1.2 :=
    measurable_pi_iff.2 fun n => (measurable_pi_apply _).comp (measurable_pi_apply _)
  have hF : Measurable fun y : ℕ → T => ∑' n, nthLargestAtom n (poissonCountingMeasure
      (fun k => (b k).1) (fun k l => (b k).2 l)) * ENNReal.ofReal (X (y n)) :=
    Measurable.tsum fun n =>
      measurable_const.mul (ENNReal.measurable_ofReal.comp (hX.comp (measurable_pi_apply n)))
  have h1 := Measure.map_infinitePi_infinitePi_restrict_equiv τ
    {q : ℕ × ℕ | q.2 < (b q.1).1} e
  rw [show (fun y' : ℕ → ℕ → T => ∑' q : {q : ℕ × ℕ // q.2 < (b q.1).1},
        ENNReal.ofReal ((b q.1.1).2 q.1.2 * X (y' q.1.1 q.1.2))) =
      (fun y : ℕ → T => ∑' n, nthLargestAtom n (poissonCountingMeasure
          (fun k => (b k).1) (fun k l => (b k).2 l)) * ENNReal.ofReal (X (y n))) ∘
        (fun y' : ℕ → ℕ → T => fun n : ℕ => y' (e.symm n).1.1 (e.symm n).1.2)
    from funext hsum, ← Measure.map_map hF hm, h1]

/-- Marking the points of one Poisson block by an independent i.i.d. array of marks. -/
theorem map_prod_infinitePi_blockMarks {X : Type*} [MeasurableSpace X] (π : Measure ℕ)
    (ν : Measure X) [IsProbabilityMeasure ν] (τ : Measure T)
    [IsProbabilityMeasure τ] :
    (((π.prod (Measure.infinitePi fun _ : ℕ => ν)).prod
        (Measure.infinitePi fun _ : ℕ => τ)).map
      (fun p => (p.1.1, fun l => (p.1.2 l, p.2 l)))) =
      π.prod (Measure.infinitePi fun _ : ℕ => ν.prod τ) := by
  have hz : Measurable fun p : (ℕ → X) × (ℕ → T) => fun l => (p.1 l, p.2 l) :=
    measurable_pi_iff.2 fun l => ((measurable_pi_apply l).comp measurable_fst).prodMk
      ((measurable_pi_apply l).comp measurable_snd)
  have hassoc := (measurePreserving_prodAssoc π (Measure.infinitePi fun _ : ℕ => ν)
    (Measure.infinitePi fun _ : ℕ => τ))
  have hmap := Measure.map_prod_map π ((Measure.infinitePi fun _ : ℕ => ν).prod
    (Measure.infinitePi fun _ : ℕ => τ)) (f := id) (g := fun p : (ℕ → X) × (ℕ → T) =>
      fun l => (p.1 l, p.2 l)) measurable_id hz
  rw [Measure.infinitePi_prod_map_zip (fun _ : ℕ => ν) (fun _ : ℕ => τ), Measure.map_id]
    at hmap
  rw [hmap, ← hassoc.map_eq, Measure.map_map (measurable_id.prodMap hz)
    MeasurableEquiv.prodAssoc.measurable]
  rfl

/-- Marking the points of all blocks of an independent family of Poisson blocks by an
independent i.i.d. array of marks. -/
theorem map_prod_infinitePi_allBlockMarks {X : Type*} [MeasurableSpace X]
    (π : ℕ → Measure ℕ) [∀ k, IsProbabilityMeasure (π k)] (ν : ℕ → Measure X)
    [∀ k, IsProbabilityMeasure (ν k)] (τ : Measure T) [IsProbabilityMeasure τ] :
    ((Measure.infinitePi fun k => (π k).prod (Measure.infinitePi fun _ : ℕ => ν k)).prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => τ)).map
      (fun p k => ((p.1 k).1, fun l => ((p.1 k).2 l, p.2 k l))) =
      Measure.infinitePi fun k => (π k).prod (Measure.infinitePi fun _ : ℕ => (ν k).prod τ) := by
  have hzip := Measure.infinitePi_prod_map_zip
    (fun k => (π k).prod (Measure.infinitePi fun _ : ℕ => ν k))
    (fun _ : ℕ => Measure.infinitePi fun _ : ℕ => τ)
  have hblock : Measurable fun w : (ℕ × (ℕ → X)) × (ℕ → T) =>
      ((w.1.1, fun l => (w.1.2 l, w.2 l)) : ℕ × (ℕ → X × T)) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun l =>
      (((measurable_pi_apply l).comp (measurable_snd.comp measurable_fst)).prodMk
        ((measurable_pi_apply l).comp measurable_snd)))
  have hpi := Measure.infinitePi_map_pi
    (fun k => ((π k).prod (Measure.infinitePi fun _ : ℕ => ν k)).prod
      (Measure.infinitePi fun _ : ℕ => τ))
    (f := fun _ w => ((w.1.1, fun l => (w.1.2 l, w.2 l)) : ℕ × (ℕ → X × T)))
    (fun _ => hblock)
  simp only [map_prod_infinitePi_blockMarks] at hpi
  rw [← hpi, ← hzip, Measure.map_map]
  · rfl
  · exact measurable_pi_iff.2 fun k => hblock.comp (measurable_pi_apply k)
  · exact measurable_pi_iff.2 fun k => ((measurable_pi_apply k).comp measurable_fst).prodMk
      ((measurable_pi_apply k).comp measurable_snd)

/-- The total of the positive points of a marked counting measure, after multiplying each point
by a function of its mark, is the sum over the active points. -/
theorem lintegral_marked_blocks_eq_tsum (N : ℕ → ℕ) (Z : ℕ → ℕ → ℝ × T) {X : T → ℝ}
    (hX : Measurable X) :
    (∫⁻ y in Ioi 0, ENNReal.ofReal y ∂((poissonCountingMeasure N Z).map
        (fun p : ℝ × T => p.1 * X p.2))) =
      ∑' q : {q : ℕ × ℕ // q.2 < N q.1},
        ENNReal.ofReal ((Z q.1.1 q.1.2).1 * X (Z q.1.1 q.1.2).2) := by
  have hmap : Measurable fun p : ℝ × T => p.1 * X p.2 := by fun_prop
  rw [setLIntegral_eq_of_support_subset, poissonCountingMeasure_map _ _ hmap,
    lintegral_poissonCountingMeasure_eq_tsum _ _ ENNReal.measurable_ofReal]
  intro y hy
  simpa using hy

/-- The sum over the active points, as a measurable function of the block configuration and
of an array of marks attached to the points. -/
theorem measurable_tsum_active_mul {X : T → ℝ} (hX : Measurable X) :
    Measurable fun p : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → T) =>
      ∑' q : {q : ℕ × ℕ // q.2 < (p.1 q.1).1},
        ENNReal.ofReal ((p.1 q.1.1).2 q.1.2 * X (p.2 q.1.1 q.1.2)) := by
  have h : (fun p : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → T) =>
      ∑' q : {q : ℕ × ℕ // q.2 < (p.1 q.1).1},
        ENNReal.ofReal ((p.1 q.1.1).2 q.1.2 * X (p.2 q.1.1 q.1.2))) =
      fun p => ∑' q : ℕ × ℕ, {q : ℕ × ℕ | q.2 < (p.1 q.1).1}.indicator
        (fun q => ENNReal.ofReal ((p.1 q.1).2 q.2 * X (p.2 q.1 q.2))) q := by
    funext p
    exact tsum_subtype {q : ℕ × ℕ | q.2 < (p.1 q.1).1}
      (fun q => ENNReal.ofReal ((p.1 q.1).2 q.2 * X (p.2 q.1 q.2)))
  rw [h]
  refine Measurable.tsum fun q => ?_
  simp only [Set.indicator, Set.mem_ofPred_eq]
  have hN : Measurable fun p : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → T) => (p.1 q.1).1 :=
    measurable_fst.comp ((measurable_pi_apply q.1).comp measurable_fst)
  have hx : Measurable fun p : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → T) => (p.1 q.1).2 q.2 :=
    (measurable_pi_apply q.2).comp (measurable_snd.comp ((measurable_pi_apply q.1).comp
      measurable_fst))
  have hy : Measurable fun p : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → T) => p.2 q.1 q.2 :=
    (measurable_pi_apply q.2).comp ((measurable_pi_apply q.1).comp measurable_snd)
  exact Measurable.ite (hN (MeasurableSet.of_discrete : MeasurableSet {n : ℕ | q.2 < n}))
    (ENNReal.measurable_ofReal.comp (hx.mul (hX.comp hy))) measurable_const

/-- The ranked sum is a measurable function of the block configuration and the rank-indexed
marks. -/
theorem measurable_tsum_ranked_mul {X : T → ℝ} (hX : Measurable X) :
    Measurable fun p : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → T) =>
      ∑' n, nthLargestAtom n (poissonCountingMeasure
        (fun k => (p.1 k).1) (fun k l => (p.1 k).2 l)) * ENNReal.ofReal (X (p.2 n)) :=
  Measurable.tsum fun n =>
    ((measurable_nthLargestAtom n).comp (measurable_poissonCountingMeasure.comp
      measurable_fst)).mul (ENNReal.measurable_ofReal.comp
        (hX.comp ((measurable_pi_apply n).comp measurable_snd)))

/-- Almost surely, the active masses of independent ζ-Poisson blocks are infinite in number,
positive, summable and pairwise distinct. -/
theorem ae_infinitePi_blocks_good {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)] (rate : ℕ → ℝ≥0)
    (hmu : zetaPoissonMeasure ζ = Measure.sum fun k => (rate k : ℝ≥0∞) • nu k) :
    ∀ᵐ b ∂(Measure.infinitePi fun k =>
        Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)),
      Infinite {q : ℕ × ℕ // q.2 < (b q.1).1} ∧
      (∀ q : {q : ℕ × ℕ // q.2 < (b q.1).1}, 0 < (b q.1.1).2 q.1.2) ∧
      Summable (fun q : {q : ℕ × ℕ // q.2 < (b q.1).1} => (b q.1.1).2 q.1.2) ∧
      Function.Injective (fun q : {q : ℕ × ℕ // q.2 < (b q.1).1} => (b q.1.1).2 q.1.2) := by
  have hBm : ∀ k, Measurable fun b : ℕ → ℕ × (ℕ → ℝ) => b k := fun k => measurable_pi_apply k
  have hB : iIndepFun (fun k (b : ℕ → ℕ × (ℕ → ℝ)) => b k)
      (Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)) :=
    iIndepFun_infinitePi (X := fun _ x => x) fun _ => measurable_id
  have hlaw : ∀ k, HasLaw (fun b : ℕ → ℕ × (ℕ → ℝ) => b k)
      (Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k))
      (Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)) :=
    fun k => hasLaw_eval_infinitePi
      (fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)) k
  have h1 := ae_cascadeRoot_active_infinite hζ0 nu rate
    (fun k (b : ℕ → ℕ × (ℕ → ℝ)) => b k) hBm hB hlaw hmu
  have h2 := ae_cascadeRoot_active_pos nu rate (fun k (b : ℕ → ℕ × (ℕ → ℝ)) => b k) hlaw hmu
  have h3 := ae_cascadeRoot_active_summable hζ0 hζ1 nu rate
    (fun k (b : ℕ → ℕ × (ℕ → ℝ)) => b k) hBm hlaw hmu
  have h4 := ae_cascadeRoot_active_injective nu rate (fun k (b : ℕ → ℕ × (ℕ → ℝ)) => b k)
    hBm hB hlaw hmu
  filter_upwards [h1, h2, h3, h4] with b a1 a2 a3 a4
  exact ⟨a1, a2, a3, a4⟩

/-- **Marks by point or by rank give the same law.** Under independent Poisson blocks (of
the ζ-Poisson process) and an independent i.i.d. mark array, the sum of the masses times marks
attached to the sampled points has the law of the sum of the ranked masses times marks attached
by rank. -/
theorem map_prod_tsum_active_eq_map_prod_tsum_ranked {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)] (rate : ℕ → ℝ≥0)
    (hmu : zetaPoissonMeasure ζ = Measure.sum fun k => (rate k : ℝ≥0∞) • nu k)
    (τ : Measure T) [IsProbabilityMeasure τ] {X : T → ℝ} (hX : Measurable X) :
    ((Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => τ)).map
      (fun p => ∑' q : {q : ℕ × ℕ // q.2 < (p.1 q.1).1},
        ENNReal.ofReal ((p.1 q.1.1).2 q.1.2 * X (p.2 q.1.1 q.1.2))) =
    ((Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).prod
        (Measure.infinitePi fun _ : ℕ => τ)).map
      (fun p => ∑' n, nthLargestAtom n (poissonCountingMeasure
        (fun k => (p.1 k).1) (fun k l => (p.1 k).2 l)) * ENNReal.ofReal (X (p.2 n))) := by
  have hgood := ae_infinitePi_blocks_good hζ0 hζ1 nu rate hmu
  refine Measure.map_prod_eq_of_ae_map_fiber_eq _ _ _ (measurable_tsum_active_mul hX)
    (measurable_tsum_ranked_mul hX) ?_
  filter_upwards [hgood] with b hb
  obtain ⟨hinf, hpos, hsum, hinj⟩ := hb
  exact map_tsum_active_mul_eq_map_tsum_ranked_mul b hpos hinj hsum τ hX

/-- **Theorem 2.6 for ranked atoms with i.i.d. marks, on the canonical space.** Under independent
Poisson blocks (of the ζ-Poisson process) and an independent i.i.d. mark array with
`0 < E X(Y)^ζ < ∞`, the law of `∑ uₙ X(Yₙ)` (ranked masses `uₙ`) is that of `c ∑ uₙ`,
`c = (E X(Y)^ζ)^(1/ζ)`. -/
theorem map_prod_tsum_ranked_marked_eq {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)] (rate : ℕ → ℝ≥0)
    (hmu : zetaPoissonMeasure ζ = Measure.sum fun k => (rate k : ℝ≥0∞) • nu k)
    (τ : Measure T) [IsProbabilityMeasure τ] {X : T → ℝ} (hX : Measurable X)
    (hXpos : ∀ᵐ t ∂τ, 0 < X t) (hpos : 0 < ∫⁻ t, ENNReal.ofReal (X t) ^ ζ ∂τ)
    (hfin : ∫⁻ t, ENNReal.ofReal (X t) ^ ζ ∂τ < ∞) :
    ((Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).prod
        (Measure.infinitePi fun _ : ℕ => τ)).map
      (fun p => ∑' n, nthLargestAtom n (poissonCountingMeasure
        (fun k => (p.1 k).1) (fun k l => (p.1 k).2 l)) * ENNReal.ofReal (X (p.2 n))) =
    (Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).map
      (fun b => ENNReal.ofReal ((∫⁻ t, ENNReal.ofReal (X t) ^ ζ ∂τ).toReal ^ ζ⁻¹) *
        ∑' n, nthLargestAtom n (poissonCountingMeasure
          (fun k => (b k).1) (fun k l => (b k).2 l))) := by
  have hBm : ∀ k, Measurable fun b : ℕ → ℕ × (ℕ → ℝ) => b k := fun k => measurable_pi_apply k
  have hB : iIndepFun (fun k (b : ℕ → ℕ × (ℕ → ℝ)) => b k)
      (Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)) :=
    iIndepFun_infinitePi (X := fun _ x => x) fun _ => measurable_id
  have hlaw : ∀ k, HasLaw (fun b : ℕ → ℕ × (ℕ → ℝ) => b k)
      (Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k))
      (Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)) :=
    fun k => hasLaw_eval_infinitePi
      (fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)) k
  have hμ1 : (zetaPoissonMeasure ζ).prod τ =
      Measure.sum fun k => (rate k : ℝ≥0∞) • (nu k).prod τ := by
    rw [hmu, Measure.prod_sum_left]
    simp only [Measure.prod_smul_left]
  have hmarked := identDistrib_marked_sum (P := Measure.infinitePi fun k =>
      Po(rate k).prod (Measure.infinitePi fun _ : ℕ => (nu k).prod τ)) hζ0 τ hX hXpos
    hpos hfin (fun k => (nu k).prod τ) rate
    (B := fun k (b : ℕ → ℕ × (ℕ → ℝ × T)) => b k) (fun k => measurable_pi_apply k)
    (iIndepFun_infinitePi (X := fun _ x => x) fun _ => measurable_id)
    (fun k => hasLaw_eval_infinitePi
      (fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => (nu k).prod τ)) k)
    hμ1 nu rate hBm hB hlaw hmu
  have hzip := map_prod_infinitePi_allBlockMarks (fun k => Po(rate k)) nu τ
  have hS : ∀ b : ℕ → ℕ × (ℕ → ℝ × T),
      (∫⁻ y in Ioi 0, ENNReal.ofReal y ∂((poissonCountingMeasure
        (fun n => (b n).1) (fun n l => (b n).2 l)).map (fun p : ℝ × T => p.1 * X p.2))) =
      ∑' q : {q : ℕ × ℕ // q.2 < (b q.1).1},
        ENNReal.ofReal (((b q.1.1).2 q.1.2).1 * X ((b q.1.1).2 q.1.2).2) :=
    fun b => lintegral_marked_blocks_eq_tsum _ _ hX
  have hzipm : Measurable fun p : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → T) =>
      fun k => ((p.1 k).1, fun l => ((p.1 k).2 l, p.2 k l)) :=
    measurable_pi_iff.2 fun k =>
      (measurable_fst.comp ((measurable_pi_apply k).comp measurable_fst)).prodMk
        (measurable_pi_iff.2 fun l =>
          ((measurable_pi_apply l).comp (measurable_snd.comp
            ((measurable_pi_apply k).comp measurable_fst))).prodMk
            ((measurable_pi_apply l).comp ((measurable_pi_apply k).comp measurable_snd)))
  have hlawS : (Measure.infinitePi fun k => Po(rate k).prod
        (Measure.infinitePi fun _ : ℕ => (nu k).prod τ)).map
      (fun b => ∫⁻ y in Ioi 0, ENNReal.ofReal y ∂((poissonCountingMeasure
        (fun n => (b n).1) (fun n l => (b n).2 l)).map (fun p : ℝ × T => p.1 * X p.2))) =
      ((Measure.infinitePi fun k => Po(rate k).prod
          (Measure.infinitePi fun _ : ℕ => nu k)).prod
        (Measure.infinitePi fun _ : ℕ => τ)).map
      (fun p => ∑' n, nthLargestAtom n (poissonCountingMeasure
        (fun k => (p.1 k).1) (fun k l => (p.1 k).2 l)) * ENNReal.ofReal (X (p.2 n))) := by
    have hSae := hmarked.aemeasurable_fst
    rw [← hzip] at hSae ⊢
    rw [AEMeasurable.map_map_of_aemeasurable hSae hzipm.aemeasurable]
    have hcomp : (fun b : ℕ → ℕ × (ℕ → ℝ × T) => ∫⁻ y in Ioi 0, ENNReal.ofReal y ∂(
        (poissonCountingMeasure (fun n => (b n).1) (fun n l => (b n).2 l)).map
          (fun p : ℝ × T => p.1 * X p.2))) ∘
        (fun p : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → T) =>
          fun k => ((p.1 k).1, fun l => ((p.1 k).2 l, p.2 k l))) =
        fun p => ∑' q : {q : ℕ × ℕ // q.2 < (p.1 q.1).1},
          ENNReal.ofReal ((p.1 q.1.1).2 q.1.2 * X (p.2 q.1.1 q.1.2)) :=
      funext fun p => hS _
    rw [hcomp]
    exact map_prod_tsum_active_eq_map_prod_tsum_ranked hζ0 hζ1 nu rate hmu τ hX
  have hae : ∀ᵐ b ∂(Measure.infinitePi fun k =>
      Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)),
      (∫⁻ y in Ioi 0, ENNReal.ofReal y ∂(poissonCountingMeasure
        (fun n => (b n).1) (fun n l => (b n).2 l))) =
      ∑' n, nthLargestAtom n (poissonCountingMeasure
        (fun k => (b k).1) (fun k l => (b k).2 l)) := by
    filter_upwards [ae_tsum_rankedRoot_eq_lintegral hζ0 hζ1 nu rate
      (fun k (b : ℕ → ℕ × (ℕ → ℝ)) => b k) hBm hB hlaw hmu (fun x => x) measurable_id]
      with b hb
    rw [hb, setLIntegral_eq_of_support_subset]
    intro y hy
    simpa using hy
  rw [← hlawS, hmarked.map_eq]
  refine Measure.map_congr ?_
  filter_upwards [hae] with b hb
  rw [hb]

/-- **Theorem 2.6 for ranked atoms with i.i.d. marks.** Let `uₙ` be the ranked atoms of
independent ζ-Poisson blocks and `Yₙ` i.i.d. marks, independent of the blocks, with
`0 < E X(Y)^ζ < ∞`. Then `∑ uₙ X(Yₙ)` has the law of `c ∑ uₙ`, `c = (E X(Y)^ζ)^(1/ζ)`. -/
theorem identDistrib_ranked_marked_sum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)] (rate : ℕ → ℝ≥0)
    (B : ℕ → Ω → ℕ × (ℕ → ℝ)) (hBm : ∀ k, Measurable (B k)) (hB : iIndepFun B P)
    (hlaw : ∀ k, HasLaw (B k) (Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)) P)
    (hmu : zetaPoissonMeasure ζ = Measure.sum fun k => (rate k : ℝ≥0∞) • nu k)
    (τ : Measure T) [IsProbabilityMeasure τ] (Y : ℕ → Ω → T) (hYm : ∀ n, Measurable (Y n))
    (hY : iIndepFun Y P) (hYlaw : ∀ n, HasLaw (Y n) τ P)
    (hBY : IndepFun (fun ω k => B k ω) (fun ω n => Y n ω) P)
    {X : T → ℝ} (hX : Measurable X) (hXpos : ∀ᵐ t ∂τ, 0 < X t)
    (hpos : 0 < ∫⁻ t, ENNReal.ofReal (X t) ^ ζ ∂τ)
    (hfin : ∫⁻ t, ENNReal.ofReal (X t) ^ ζ ∂τ < ∞) :
    IdentDistrib
      (fun ω => ∑' n, nthLargestAtom n (poissonCountingMeasure
        (fun k => (B k ω).1) (fun k l => (B k ω).2 l)) * ENNReal.ofReal (X (Y n ω)))
      (fun ω => ENNReal.ofReal ((∫⁻ t, ENNReal.ofReal (X t) ^ ζ ∂τ).toReal ^ ζ⁻¹) *
        ∑' n, nthLargestAtom n (poissonCountingMeasure
          (fun k => (B k ω).1) (fun k l => (B k ω).2 l))) P P := by
  have hBhm : Measurable fun ω k => B k ω := measurable_pi_iff.2 hBm
  have hYhm : Measurable fun ω n => Y n ω := measurable_pi_iff.2 hYm
  have hBhat := HasLaw.infinitePi hBm hB hlaw
  have hYhat := HasLaw.infinitePi hYm hY hYlaw
  have hpair : P.map (fun ω => ((fun k => B k ω), (fun n => Y n ω))) =
      (Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).prod
        (Measure.infinitePi fun _ : ℕ => τ) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hBhm.aemeasurable hYhm.aemeasurable).1 hBY,
      hBhat.map_eq, hYhat.map_eq]
  have hcan := map_prod_tsum_ranked_marked_eq hζ0 hζ1 nu rate hmu τ hX hXpos hpos hfin
  have hS0m : Measurable fun ω => ENNReal.ofReal
      ((∫⁻ t, ENNReal.ofReal (X t) ^ ζ ∂τ).toReal ^ ζ⁻¹) *
        ∑' n, nthLargestAtom n (poissonCountingMeasure
          (fun k => (B k ω).1) (fun k l => (B k ω).2 l)) :=
    (Measurable.tsum fun n => (measurable_nthLargestAtom n).comp
      (measurable_poissonCountingMeasure_comp hBm)).const_mul _
  refine ⟨((measurable_tsum_ranked_mul hX).comp (hBhm.prodMk hYhm)).aemeasurable,
    hS0m.aemeasurable, ?_⟩
  have hRm : Measurable fun b : ℕ → ℕ × (ℕ → ℝ) => ENNReal.ofReal
      ((∫⁻ t, ENNReal.ofReal (X t) ^ ζ ∂τ).toReal ^ ζ⁻¹) *
        ∑' n, nthLargestAtom n (poissonCountingMeasure
          (fun k => (b k).1) (fun k l => (b k).2 l)) :=
    (Measurable.tsum fun n => (measurable_nthLargestAtom n).comp
      measurable_poissonCountingMeasure).const_mul _
  have h2 := Measure.map_map (μ := P) hRm hBhm
  rw [hBhat.map_eq] at h2
  have h1 := Measure.map_map (μ := P) (measurable_tsum_ranked_mul hX) (hBhm.prodMk hYhm)
  rw [hpair, hcan] at h1
  exact h1.symm.trans h2

end SpinGlasses
