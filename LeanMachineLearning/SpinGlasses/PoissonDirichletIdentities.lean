/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletInvariance
public import LeanMachineLearning.SpinGlasses.GaussianIBPCountable

/-!
# Block-indexed replicas of Poisson counting measures

The order-free integrals used in Lemma 2.3 are series over the actual block indices,
without introducing a ranking of the marked atoms. This deterministic bridge is the
first step toward applying countable Gaussian integration by parts.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SpinGlasses

/-- An overlap observable on finitely many replicas is bounded without any global
boundedness assumption on the function of real matrices: overlap entries are in `{0, 1}`.
The witness is reusable for both the unperturbed and tilted Gaussian IBP formulas. -/
theorem exists_bound_index_overlap_observable
    {R α : Type*} [Fintype R] [DecidableEq α] (f : (R → R → ℝ) → ℝ) :
    ∃ M : ℝ, ∀ σ : R → α,
      |f (fun i j => if σ i = σ j then 1 else 0)| ≤ M := by
  classical
  let s : Finset (R → R → ℝ) :=
    Finset.univ.image (fun a : R → R → Bool => fun i j => if a i j then 1 else 0)
  refine ⟨∑ a ∈ s, |f a|, fun σ => ?_⟩
  have hmem : (fun i j => if σ i = σ j then (1 : ℝ) else 0) ∈ s := by
    apply Finset.mem_image.mpr
    refine ⟨fun i j => decide (σ i = σ j), Finset.mem_univ _, ?_⟩
    funext i j
    simp
  exact Finset.single_le_sum (fun a _ => abs_nonneg (f a)) hmem

/-- The covariance correction in the countable Gaussian IBP formula is uniformly
bounded. In particular, it needs no additional hypothesis on the test function. -/
theorem exists_bound_index_overlap_ibp_observable
    {R α : Type*} [Fintype R] [DecidableEq α] (r₀ : R)
    (f : (R → R → ℝ) → ℝ) :
    ∃ M : ℝ, ∀ τ : Option R → α,
      |f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
        ((∑ r : R, if τ (some r₀) = τ (some r) then (1 : ℝ) else 0) -
          (Fintype.card R : ℝ) *
            (if τ (some r₀) = τ none then 1 else 0))| ≤ M := by
  classical
  obtain ⟨M, hM⟩ := exists_bound_index_overlap_observable (α := α) f
  refine ⟨(2 * Fintype.card R : ℝ) * M, fun τ => ?_⟩
  have hM' := hM (fun r => τ (some r))
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM'
  have hsum : 0 ≤ (∑ r : R, if τ (some r₀) = τ (some r) then (1 : ℝ) else 0) ∧
      (∑ r : R, if τ (some r₀) = τ (some r) then (1 : ℝ) else 0) ≤ Fintype.card R := by
    constructor
    · exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    · simpa using (Finset.sum_le_sum (s := Finset.univ) (fun r _ =>
        show (if τ (some r₀) = τ (some r) then (1 : ℝ) else 0) ≤ 1 by
          split_ifs <;> norm_num))
  have hlast : 0 ≤ (Fintype.card R : ℝ) *
      (if τ (some r₀) = τ none then 1 else 0) ∧
      (Fintype.card R : ℝ) * (if τ (some r₀) = τ none then 1 else 0) ≤
        Fintype.card R := by
    constructor
    · positivity
    · split_ifs <;> simp
  rw [abs_mul]
  have hcorr : |(∑ r : R, if τ (some r₀) = τ (some r) then (1 : ℝ) else 0) -
      (Fintype.card R : ℝ) * (if τ (some r₀) = τ none then 1 else 0)| ≤
        (2 * Fintype.card R : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [hsum.1, hsum.2, hlast.1, hlast.2]
  exact (mul_le_mul hM' hcorr (abs_nonneg _) hM0).trans_eq (by ring)

/-- Integrating against the restriction of a block counting measure sums exactly the
indices whose sampled point lies in the restriction set. No sigma-finiteness of the
unrestricted measure is needed. -/
theorem lintegral_poissonCountingMeasure_restrict_eq_tsum
    {S : Type*} [MeasurableSpace S] (N : ℕ → ℕ) (X : ℕ → ℕ → S)
    {A : Set S} [DecidablePred (· ∈ A)] (hA : MeasurableSet A)
    {f : S → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂(poissonCountingMeasure N X).restrict A) =
      ∑' q : {p : ℕ × ℕ // p.2 < N p.1},
        (if X q.1.1 q.1.2 ∈ A then f (X q.1.1 q.1.2) else 0) := by
  classical
  simp only [poissonCountingMeasure_eq_sum_dirac]
  rw [← lintegral_indicator hA, lintegral_sum_measure]
  exact tsum_congr fun q => by
    rw [lintegral_dirac' _ (hf.indicator hA)]
    simp [Set.indicator]

/-- Replica integrals against a restricted block counting measure are sums over
block-index tuples. This applies even if the unrestricted measure is not sigma-finite.
The one-point restricted formula above is the induction step. -/
theorem lintegral_pi_poissonCountingMeasure_restrict_eq_tsum
    {S : Type*} [MeasurableSpace S] (N : ℕ → ℕ) (X : ℕ → ℕ → S)
    {A : Set S} [DecidablePred (· ∈ A)] (hA : MeasurableSet A)
    [SigmaFinite ((poissonCountingMeasure N X).restrict A)]
    (n : ℕ) {Φ : (Fin n → S) → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ q, Φ q ∂Measure.pi fun _ : Fin n =>
      (poissonCountingMeasure N X).restrict A) =
      ∑' q : Fin n → {p : ℕ × ℕ // p.2 < N p.1},
        (if ∀ i, X (q i).1.1 (q i).1.2 ∈ A then
          Φ (fun i => X (q i).1.1 (q i).1.2) else 0) := by
  classical
  induction n with
  | zero =>
    rw [lintegral_pi_fin_zero _ hΦ, tsum_fin_zero]
    simp only [IsEmpty.forall_iff, ↓reduceIte]
    exact congrArg Φ (funext fun i => isEmptyElim i)
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S) (Fin.last n)
    have hmp := measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => (poissonCountingMeasure N X).restrict A) (Fin.last n)
    have h := hmp.lintegral_comp_emb e.measurableEmbedding
      (fun z => Φ (e.symm z))
    simp only [MeasurableEquiv.symm_apply_apply, e] at h
    change (∫⁻ q, Φ q ∂Measure.pi fun _ : Fin (n + 1) =>
      (poissonCountingMeasure N X).restrict A) =
      (∫⁻ z, Φ (e.symm z) ∂((poissonCountingMeasure N X).restrict A).prod
        (Measure.pi fun _ : Fin n => (poissonCountingMeasure N X).restrict A)) at h
    rw [h, lintegral_prod_symm]
    · have hmeas : Measurable fun y : Fin n → S =>
          ∫⁻ x, Φ (e.symm (x, y)) ∂(poissonCountingMeasure N X).restrict A :=
        (hΦ.comp e.symm.measurable).lintegral_prod_left'
      rw [ih hmeas]
      have hx (y : Fin n → S) : Measurable fun x : S => Φ (e.symm (x, y)) :=
        (hΦ.comp e.symm.measurable).comp
          (measurable_id.prodMk measurable_const)
      simp_rw [lintegral_poissonCountingMeasure_restrict_eq_tsum N X hA (hx _)]
      have hsplit (q : Fin n → {p : ℕ × ℕ // p.2 < N p.1}) :
          (if ∀ i, X (q i).1.1 (q i).1.2 ∈ A then
            ∑' p : {p : ℕ × ℕ // p.2 < N p.1},
              if X p.1.1 p.1.2 ∈ A then
                Φ (e.symm (X p.1.1 p.1.2,
                  fun i => X (q i).1.1 (q i).1.2)) else 0 else 0) =
          ∑' p : {p : ℕ × ℕ // p.2 < N p.1},
            if (∀ i, X (q i).1.1 (q i).1.2 ∈ A) then
              (if X p.1.1 p.1.2 ∈ A then
                Φ (e.symm (X p.1.1 p.1.2,
                  fun i => X (q i).1.1 (q i).1.2)) else 0) else 0 := by
        split_ifs <;> simp_all
      simp_rw [hsplit]
      rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod]
      let eI := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) =>
        {p : ℕ × ℕ // p.2 < N p.1}) (Fin.last n)
      refine (Equiv.tsum_eq eI.toEquiv
        (fun z => if (∀ i, X (z.2 i).1.1 (z.2 i).1.2 ∈ A) then
          (if X z.1.1.1 z.1.1.2 ∈ A then
            Φ (e.symm (X z.1.1.1 z.1.1.2,
              fun i => X (z.2 i).1.1 (z.2 i).1.2)) else 0) else 0)).symm.trans ?_
      congr 1
      funext q
      have hc : (fun i => X (q i).1.1 (q i).1.2) =
          e.symm (X (eI q).1.1.1 (eI q).1.1.2,
            fun i => X ((eI q).2 i).1.1 ((eI q).2 i).1.2) := by
        apply e.injective
        ext i <;> simp [e, eI, MeasurableEquiv.piFinSuccAbove_apply, Fin.init_def]
      have hp : (∀ i, X (q i).1.1 (q i).1.2 ∈ A) ↔
          (∀ i, X ((eI q).2 i).1.1 ((eI q).2 i).1.2 ∈ A) ∧
            X (eI q).1.1.1 (eI q).1.1.2 ∈ A := by
        constructor
        · intro hq
          exact ⟨fun i => by simpa [eI, MeasurableEquiv.piFinSuccAbove_apply,
            Fin.init_def] using hq i.castSucc, by simpa [eI,
            MeasurableEquiv.piFinSuccAbove_apply] using hq (Fin.last n)⟩
        · rintro ⟨hq, hlast⟩ i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa [eI, MeasurableEquiv.piFinSuccAbove_apply] using hlast
          · simpa [eI, MeasurableEquiv.piFinSuccAbove_apply,
              Fin.init_def] using hq j
      rw [hc]
      by_cases hlast : X (eI q).1.1.1 (eI q).1.1.2 ∈ A <;>
        by_cases hrest : ∀ i, X ((eI q).2 i).1.1 ((eI q).2 i).1.2 ∈ A <;>
        simp [hp, hlast, hrest]
    · exact (hΦ.comp e.symm.measurable).aemeasurable

/-- Expand an `n`-fold integral against a block counting measure into a series over
replica choices of actual block indices. This identity counts repeated atoms with
multiplicity, and does not require atomlessness. The sigma-finiteness assumption is
necessary for Mathlib's finite product measure construction; it is not automatic for
counting measures with infinitely many coincident atoms. It is the case `A = univ` of
`lintegral_pi_poissonCountingMeasure_restrict_eq_tsum`. -/
theorem lintegral_pi_poissonCountingMeasure_eq_tsum
    {S : Type*} [MeasurableSpace S] (N : ℕ → ℕ) (X : ℕ → ℕ → S)
    [SigmaFinite (poissonCountingMeasure N X)]
    (n : ℕ) {Φ : (Fin n → S) → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ q, Φ q ∂Measure.pi fun _ : Fin n => poissonCountingMeasure N X) =
      ∑' q : Fin n → {p : ℕ × ℕ // p.2 < N p.1},
        Φ (fun i => X (q i).1.1 (q i).1.2) := by
  have _ : SigmaFinite ((poissonCountingMeasure N X).restrict Set.univ) := by
    rwa [Measure.restrict_univ]
  simpa only [Measure.restrict_univ, Set.mem_univ, implies_true, ite_true] using
    lintegral_pi_poissonCountingMeasure_restrict_eq_tsum N X MeasurableSet.univ n hΦ

/-- Finite counts on every positive shell make the counting measure restricted to
positive masses sigma-finite, regardless of what happens at nonpositive points. -/
theorem sigmaFinite_poissonCountingMeasure_restrict_pos_of_shells
    {S : Type*} [MeasurableSpace S] (N : ℕ → ℕ) (X : ℕ → ℕ → ℝ × S)
    (hfin : ∀ k : ℕ, poissonCountingMeasure N X
      (Set.Ioi (1 / ((k : ℝ) + 1)) ×ˢ Set.univ) < ∞) :
    SigmaFinite ((poissonCountingMeasure N X).restrict
      (Set.Ioi 0 ×ˢ (Set.univ : Set S))) := by
  rw [← iUnion_Ioi_inv_succ_prod_univ]
  exact sigmaFinite_restrict_iUnion (fun k => measurableSet_Ioi.prod MeasurableSet.univ) hfin

/-- The Gaussian-marked reference process has sigma-finite positive-mass restriction
almost surely. This supplies the instance required by the block-index replica bridge. -/
theorem ae_sigmaFinite_poissonDirichlet_gaussian_restrict_pos
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ζ : ℝ} (hζ : 0 < ζ)
    (ν : ℕ → Measure (ℝ × ℝ)) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → NNReal)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • ν n) :
    ∀ᵐ ω ∂P, SigmaFinite ((poissonCountingMeasure (fun n => (B n ω).1)
      (fun n l => (B n ω).2 l)).restrict (Set.Ioi 0 ×ˢ Set.univ)) := by
  have hshell := ae_poissonCountingMeasure_Ioi_inv_succ_prod_univ_lt_top hζ (gaussianReal 0 1)
    ν r hBm hB hlaw hμ
  filter_upwards [hshell] with ω hω
  exact sigmaFinite_poissonCountingMeasure_restrict_pos_of_shells
    (fun n => (B n ω).1) (fun n l => (B n ω).2 l) hω

/-- Almost surely the order-free finite-replica integral of the Gaussian-marked
reference process has an explicit block-index expansion, with the positivity guard.
This is the stochastic specialization of the deterministic restricted bridge. -/
theorem ae_lintegral_pi_poissonDirichlet_gaussian_eq_tsum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ζ : ℝ} (hζ : 0 < ζ)
    (ν : ℕ → Measure (ℝ × ℝ)) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → NNReal)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ k, Measurable (B k)) (hB : iIndepFun B P)
    (hlaw : ∀ k, HasLaw (B k)
      (Po(r k).prod (Measure.infinitePi fun _ : ℕ => ν k)) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun k => (r k : ℝ≥0∞) • ν k)
    (n : ℕ) {Φ : (Fin n → ℝ × ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∀ᵐ ω ∂P,
      (∫⁻ q, Φ q ∂Measure.pi fun _ : Fin n =>
        (poissonCountingMeasure (fun k => (B k ω).1)
          (fun k l => (B k ω).2 l)).restrict (Set.Ioi 0 ×ˢ Set.univ)) =
        ∑' q : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          (if ∀ i, 0 < ((B (q i).1.1 ω).2 (q i).1.2).1 then
            Φ (fun i => (B (q i).1.1 ω).2 (q i).1.2) else 0) := by
  filter_upwards [ae_sigmaFinite_poissonDirichlet_gaussian_restrict_pos
    hζ ν r hBm hB hlaw hμ] with ω hσ
  let _ : SigmaFinite ((poissonCountingMeasure (fun k => (B k ω).1)
      (fun k l => (B k ω).2 l)).restrict (Set.Ioi 0 ×ˢ Set.univ)) := hσ
  simpa only [Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true] using
    (lintegral_pi_poissonCountingMeasure_restrict_eq_tsum
      (fun k => (B k ω).1) (fun k l => (B k ω).2 l)
      (measurableSet_Ioi.prod MeasurableSet.univ) n hΦ)

/-- On the almost-sure distinctness event, equality of two sampled points is exactly
index equality. This is the overlap `R = 1` versus replica-index coincidence bridge. -/
theorem ae_poissonBlocks_point_eq_iff_index_eq
    {S Ω : Type*} [MeasurableSpace S] [MeasurableEq S] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (ν : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → NNReal)
    {B : ℕ → Ω → ℕ × (ℕ → S)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hnull : ∀ n, r n ≠ 0 → NullSingletonClass (ν n)) :
    ∀ᵐ ω ∂P, ∀ a b : {q : ℕ × ℕ // q.2 < (B q.1 ω).1},
      (B a.1.1 ω).2 a.1.2 = (B b.1.1 ω).2 b.1.2 ↔ a = b := by
  filter_upwards [ae_pairwise_ne_poissonBlocks ν r hBm hB hlaw hnull]
    with ω hω a b
  constructor
  · intro heq
    by_contra hne
    exact hω a.1 b.1 (fun hab => hne (Subtype.ext hab)) a.2 b.2 heq
  · exact fun hab => by rw [hab]

end SpinGlasses
