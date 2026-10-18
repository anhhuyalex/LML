/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletRankedMarkedLaw

/-!
# Replica sums over ranked atoms with rank-indexed marks

For ranked atoms `uₘ` of ζ-Poisson blocks and i.i.d. marks `yₘ` indexed by *rank*, every finite
family of replica sums `∑_{m⃗ ∈ ℕⁿ} Θᵢ ((u_{mₗ}, y_{mₗ})ₗ)` has the joint law of the same family
computed with marks attached to the sampled *points* of the blocks. This is the family version of
`map_prod_tsum_active_eq_map_prod_tsum_ranked`, for replica sums instead of single sums.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SpinGlasses

variable {T : Type*} [MeasurableSpace T]

/-- For a fixed block configuration with positive distinct summable active masses: the replica
sums over active points with i.i.d. point marks, and over ranks with i.i.d. rank marks, have the
same law. -/
theorem map_replica_active_eq_map_replica_ranked
    (b : ℕ → ℕ × (ℕ → ℝ)) [Infinite {q : ℕ × ℕ // q.2 < (b q.1).1}]
    (hpos : ∀ q : {q : ℕ × ℕ // q.2 < (b q.1).1}, 0 < (b q.1.1).2 q.1.2)
    (hinj : Function.Injective fun q : {q : ℕ × ℕ // q.2 < (b q.1).1} => (b q.1.1).2 q.1.2)
    (hs : Summable fun q : {q : ℕ × ℕ // q.2 < (b q.1).1} => (b q.1.1).2 q.1.2)
    (τ : Measure T) [IsProbabilityMeasure τ] {ι : Type*} (n : ι → ℕ)
    (Θ : (i : ι) → (Fin (n i) → ℝ≥0∞ × T) → ℝ≥0∞) (hΘ : ∀ i, Measurable (Θ i)) :
    (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => τ).map
        (fun y' i => ∑' q : Fin (n i) → {q : ℕ × ℕ // q.2 < (b q.1).1},
          Θ i (fun l => (ENNReal.ofReal ((b (q l).1.1).2 (q l).1.2), y' (q l).1.1 (q l).1.2))) =
      (Measure.infinitePi fun _ : ℕ => τ).map
        (fun y i => ∑' m : Fin (n i) → ℕ, Θ i (fun l => (nthLargestAtom (m l)
          (poissonCountingMeasure (fun k => (b k).1) (fun k l => (b k).2 l)), y (m l)))) := by
  obtain ⟨e, he⟩ := exists_equiv_nthLargestAtom_sum_dirac
    (fun q : {q : ℕ × ℕ // q.2 < (b q.1).1} => (b q.1.1).2 q.1.2) hinj hpos hs
  have hM := poissonCountingMeasure_eq_sum_dirac (fun k => (b k).1) (fun k l => (b k).2 l)
  have hsum : ∀ (y' : ℕ → ℕ → T) (i : ι),
      (∑' q : Fin (n i) → {q : ℕ × ℕ // q.2 < (b q.1).1},
        Θ i (fun l => (ENNReal.ofReal ((b (q l).1.1).2 (q l).1.2), y' (q l).1.1 (q l).1.2))) =
      ∑' m : Fin (n i) → ℕ, Θ i (fun l => (nthLargestAtom (m l)
          (poissonCountingMeasure (fun k => (b k).1) (fun k l => (b k).2 l)),
        y' (e.symm (m l)).1.1 (e.symm (m l)).1.2)) := by
    intro y' i
    rw [← (Equiv.arrowCongr (Equiv.refl (Fin (n i))) e.symm).tsum_eq]
    refine tsum_congr fun m => ?_
    congr 1
    funext l
    simp only [Equiv.arrowCongr_apply, Equiv.refl_symm, Equiv.refl_apply, Function.comp_apply]
    refine Prod.ext ?_ rfl
    simp only
    rw [hM, ← he (e.symm (m l)), Equiv.apply_symm_apply]
  have hRk : Measurable fun (y : ℕ → T) (i : ι) => ∑' m : Fin (n i) → ℕ, Θ i (fun l =>
      (nthLargestAtom (m l) (poissonCountingMeasure (fun k => (b k).1) (fun k l => (b k).2 l)),
        y (m l))) :=
    measurable_pi_iff.2 fun i => Measurable.tsum fun m => (hΘ i).comp
      (measurable_pi_iff.2 fun l => measurable_const.prodMk (measurable_pi_apply (m l)))
  have hg : Measurable fun y' : ℕ → ℕ → T => fun m : ℕ => y' (e.symm m).1.1 (e.symm m).1.2 :=
    measurable_pi_iff.2 fun m => (measurable_pi_apply _).comp (measurable_pi_apply _)
  have h1 := Measure.map_infinitePi_infinitePi_restrict_equiv τ {q : ℕ × ℕ | q.2 < (b q.1).1} e
  have e1 : (fun (y' : ℕ → ℕ → T) (i : ι) => ∑' q : Fin (n i) → {q : ℕ × ℕ // q.2 < (b q.1).1},
      Θ i (fun l => (ENNReal.ofReal ((b (q l).1.1).2 (q l).1.2), y' (q l).1.1 (q l).1.2))) =
      (fun (y : ℕ → T) (i : ι) => ∑' m : Fin (n i) → ℕ, Θ i (fun l => (nthLargestAtom (m l)
          (poissonCountingMeasure (fun k => (b k).1) (fun k l => (b k).2 l)), y (m l)))) ∘
        (fun y' : ℕ → ℕ → T => fun m : ℕ => y' (e.symm m).1.1 (e.symm m).1.2) :=
    funext fun y' => funext fun i => hsum y' i
  rw [e1, ← Measure.map_map hRk hg, h1]

open scoped Classical in
/-- A sum over tuples of elements of a subtype is a sum over all tuples with an indicator. -/
theorem tsum_fin_pi_subtype {α : Type*} {n : ℕ} (P : α → Prop)
    (f : (Fin n → {x // P x}) → ℝ≥0∞) :
    ∑' q, f q = ∑' q : Fin n → α, if h : ∀ l, P (q l) then f (fun l => ⟨q l, h l⟩) else 0 := by
  have h := tsum_subtype {q : Fin n → α | ∀ l, P (q l)} (fun q =>
    if h : ∀ l, P (q l) then f (fun l => ⟨q l, h l⟩) else 0)
  have h1 : ∑' q, f q = ∑' x : {q : Fin n → α | ∀ l, P (q l)},
      (if h : ∀ l, P (x.1 l) then f (fun l => ⟨x.1 l, h l⟩) else 0) := by
    rw [← (Equiv.subtypePiEquivPi (p := fun _ x => P x)).tsum_eq f]
    refine tsum_congr fun c => ?_
    have hc : (∀ l, P (c.1 l)) = True := eq_true c.2
    simp only [hc, dite_true]
    rfl
  rw [h1, h]
  refine tsum_congr fun q => ?_
  by_cases hq : ∀ l, P (q l)
  · simp [Set.indicator, hq]
  · simp [Set.indicator, hq]

/-- **Marks by rank or by point give the same replica sums in law.** -/
theorem map_prod_replica_active_eq_ranked {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)] (rate : ℕ → ℝ≥0)
    (hmu : zetaPoissonMeasure ζ = Measure.sum fun k => (rate k : ℝ≥0∞) • nu k)
    (τ : Measure T) [IsProbabilityMeasure τ] {ι : Type*} (n : ι → ℕ)
    (Θ : (i : ι) → (Fin (n i) → ℝ≥0∞ × T) → ℝ≥0∞) (hΘ : ∀ i, Measurable (Θ i)) :
    ((Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => τ)).map
      (fun p i => ∑' q : Fin (n i) → {q : ℕ × ℕ // q.2 < (p.1 q.1).1},
        Θ i (fun l => (ENNReal.ofReal ((p.1 (q l).1.1).2 (q l).1.2), p.2 (q l).1.1 (q l).1.2))) =
    ((Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).prod
        (Measure.infinitePi fun _ : ℕ => τ)).map
      (fun p i => ∑' m : Fin (n i) → ℕ, Θ i (fun l => (nthLargestAtom (m l)
        (poissonCountingMeasure (fun k => (p.1 k).1) (fun k l => (p.1 k).2 l)), p.2 (m l)))) := by
  classical
  have hgood := ae_infinitePi_blocks_good hζ0 hζ1 nu rate hmu
  have hL : Measurable fun p : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → T) => fun i : ι =>
      ∑' q : Fin (n i) → {q : ℕ × ℕ // q.2 < (p.1 q.1).1}, Θ i (fun l =>
        (ENNReal.ofReal ((p.1 (q l).1.1).2 (q l).1.2), p.2 (q l).1.1 (q l).1.2)) := by
    refine measurable_pi_iff.2 fun i => ?_
    simp_rw [tsum_fin_pi_subtype (fun x : ℕ × ℕ => x.2 < _)]
    refine Measurable.tsum fun q => ?_
    simp only [dite_eq_ite]
    refine Measurable.ite ?_ ((hΘ i).comp (measurable_pi_iff.2 fun l => ?_)) measurable_const
    · have : {p : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → T) | ∀ l, (q l).2 < (p.1 (q l).1).1} =
          ⋂ l, {p | (q l).2 < (p.1 (q l).1).1} := by ext; simp
      rw [this]
      refine MeasurableSet.iInter fun l => ?_
      exact (measurable_from_top (f := fun n : ℕ => decide ((q l).2 < n)) |>.comp
        (measurable_fst.comp ((measurable_pi_apply (q l).1).comp measurable_fst)))
        (measurableSet_singleton true) |>.congr (by ext; simp)
    · exact (ENNReal.measurable_ofReal.comp ((measurable_pi_apply (q l).2).comp
        (measurable_snd.comp ((measurable_pi_apply (q l).1).comp measurable_fst)))).prodMk
        ((measurable_pi_apply (q l).2).comp ((measurable_pi_apply (q l).1).comp
          measurable_snd))
  have hR : Measurable fun p : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → T) => fun i : ι =>
      ∑' m : Fin (n i) → ℕ, Θ i (fun l => (nthLargestAtom (m l)
        (poissonCountingMeasure (fun k => (p.1 k).1) (fun k l => (p.1 k).2 l)), p.2 (m l))) :=
    measurable_pi_iff.2 fun i => Measurable.tsum fun m => (hΘ i).comp
      (measurable_pi_iff.2 fun l => (((measurable_nthLargestAtom (m l)).comp
        (measurable_poissonCountingMeasure.comp measurable_fst))).prodMk
        ((measurable_pi_apply (m l)).comp measurable_snd))
  refine Measure.map_prod_eq_of_ae_map_fiber_eq _ _ _ hL hR ?_
  filter_upwards [hgood] with b hb
  obtain ⟨hinf, hpos, hsum, hinj⟩ := hb
  exact map_replica_active_eq_map_replica_ranked b hpos hinj hsum τ n Θ hΘ

end SpinGlasses
