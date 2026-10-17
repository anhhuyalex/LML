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

/-- Expand an `n`-fold integral against a block counting measure into a series over
replica choices of actual block indices. This identity counts repeated atoms with
multiplicity, and does not require atomlessness. The sigma-finiteness assumption is
necessary for Mathlib's finite product measure construction; it is not automatic for
counting measures with infinitely many coincident atoms. -/
theorem lintegral_pi_poissonCountingMeasure_eq_tsum
    {S : Type*} [MeasurableSpace S] (N : ℕ → ℕ) (X : ℕ → ℕ → S)
    [SigmaFinite (poissonCountingMeasure N X)]
    (n : ℕ) {Φ : (Fin n → S) → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ q, Φ q ∂Measure.pi fun _ : Fin n => poissonCountingMeasure N X) =
      ∑' q : Fin n → {p : ℕ × ℕ // p.2 < N p.1},
        Φ (fun i => X (q i).1.1 (q i).1.2) := by
  classical
  induction n with
  | zero =>
    rw [Measure.pi_of_empty]
    rw [lintegral_dirac' _ hΦ]
    have hzero : ∀ q : Fin 0 → {p : ℕ × ℕ // p.2 < N p.1},
        q = (isEmptyElim : Fin 0 → {p : ℕ × ℕ // p.2 < N p.1}) :=
      fun _ => Subsingleton.elim _ _
    simp_rw [hzero]
    rw [tsum_fintype]
    let _ : Unique (Fin 0 → {p : ℕ × ℕ // p.2 < N p.1}) :=
      uniqueOfSubsingleton (fun i : Fin 0 => i.elim0)
    simp only [Finset.univ_unique, Finset.sum_const, Finset.card_singleton, one_smul]
    congr 1
    funext i
    exact isEmptyElim i
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S) (Fin.last n)
    have hmp := measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => poissonCountingMeasure N X) (Fin.last n)
    have h := hmp.lintegral_comp_emb e.measurableEmbedding
      (fun z => Φ (e.symm z))
    simp only [MeasurableEquiv.symm_apply_apply, e] at h
    change (∫⁻ q, Φ q ∂Measure.pi fun _ : Fin (n + 1) =>
      poissonCountingMeasure N X) =
      (∫⁻ z, Φ (e.symm z) ∂(poissonCountingMeasure N X).prod
        (Measure.pi fun _ : Fin n => poissonCountingMeasure N X)) at h
    rw [h, lintegral_prod_symm]
    · have hmeas : Measurable fun y : Fin n → S =>
          ∫⁻ x, Φ (e.symm (x, y)) ∂poissonCountingMeasure N X :=
        (hΦ.comp e.symm.measurable).lintegral_prod_left'
      rw [ih hmeas]
      have hx (y : Fin n → S) : Measurable fun x : S => Φ (e.symm (x, y)) :=
        (hΦ.comp e.symm.measurable).comp
          (measurable_id.prodMk measurable_const)
      simp_rw [lintegral_poissonCountingMeasure_eq_tsum N X (hx _)]
      rw [ENNReal.tsum_comm]
      rw [← ENNReal.tsum_prod]
      let eI := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) =>
        {p : ℕ × ℕ // p.2 < N p.1}) (Fin.last n)
      refine (Equiv.tsum_eq eI.toEquiv
        (fun z => Φ (e.symm (X z.1.1.1 z.1.1.2,
          fun i => X (z.2 i).1.1 (z.2 i).1.2)))).symm.trans ?_
      congr 1
      funext q
      congr 1
      funext i
      have hc (q : Fin (n + 1) → {p : ℕ × ℕ // p.2 < N p.1}) :
          (fun j => X (q j).1.1 (q j).1.2) =
            e.symm (X (eI q).1.1.1 (eI q).1.1.2,
              fun j => X ((eI q).2 j).1.1 ((eI q).2 j).1.2) := by
        apply e.injective
        ext j <;> simp [e, eI, MeasurableEquiv.piFinSuccAbove_apply,
          Fin.init_def]
      exact congrArg (fun f : Fin (n + 1) → S => f i) (hc q).symm
    · exact (hΦ.comp e.symm.measurable).aemeasurable

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
