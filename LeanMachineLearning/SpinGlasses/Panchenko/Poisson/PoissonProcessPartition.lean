/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonProcessEquivalence
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.RestrictPartition

/-!
# Poisson processes: conditional i.i.d. structure on a partition (Panchenko, Theorem 2.4)

For a measurable partition `S = ⊔ₘ Aₘ` with `0 < μ(Aₘ) < ∞`, the book states that, given the
counts `(M(Aₘ))ₘ`, the points of `M` in `Aₘ` form an i.i.d. sample of that size from
`μ[|Aₘ] = μ(· ∩ Aₘ)/μ(Aₘ)`, independently over `m`. We state this without ordering the atoms
of `M`, as an equality in law for the pair (counts, restrictions `M|Aₘ`) with an explicit model:
independent blocks `(Nₘ, (Zₘₗ)ₗ) ~ Po(μ(Aₘ)) ⊗ μ[|Aₘ]^{⊗ℕ}`, the counts being `Nₘ` and the
restrictions being the sample counting measures `∑_{l<Nₘ} δ_{Zₘₗ}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpinGlasses

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

/-- **Equivalence Theorem 2.4, conditional i.i.d. form.** Let `M` be the counting measure of
independent Poisson blocks with intensity `μ`, and let `(Aₘ)` be a measurable partition of `S`
into sets of finite `μ`-mass. Then there are independent blocks `(Nₘ, (Zₘₗ)ₗ)` with law
`Po(μ(Aₘ)) ⊗ νₘ^{⊗ℕ}`, where `νₘ = μ[|Aₘ] = μ(· ∩ Aₘ)/μ(Aₘ)` whenever `μ(Aₘ) ≠ 0` (a cell of
mass zero has an empty block almost surely, so its sample law is an arbitrary probability measure),
such that the pair `((M(Aₘ))ₘ, (M|Aₘ)ₘ)` has the same law as `((Nₘ)ₘ, (∑_{l<Nₘ} δ_{Zₘₗ})ₘ)`.
In particular, conditionally on the counts, the restriction of `M` to `Aₘ` is the counting measure
of an i.i.d. sample of size `M(Aₘ)` from `μ[|Aₘ]`, independently over `m`. -/
theorem exists_identDistrib_restrict_poissonCountingMeasure {P : Measure Ω}
    [IsProbabilityMeasure P] (ν : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ν n)]
    (r : ℕ → ℝ≥0) {B : ℕ → Ω → ℕ × (ℕ → S)} (hBm : ∀ n, Measurable (B n))
    (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    {μ : Measure S} (hμ : μ = Measure.sum fun n => (r n : ℝ≥0∞) • ν n)
    {M : Ω → Measure S}
    (hM : ∀ ω, M ω = poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l))
    {A : ℕ → Set S} (hA : ∀ m, MeasurableSet (A m))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (hcover : ⋃ m, A m = Set.univ)
    (hfin : ∀ m, μ (A m) ≠ ∞) :
    ∃ (ν' : ℕ → Measure S) (P' : Measure (ℕ → ℕ × (ℕ → S))),
      (∀ m, IsProbabilityMeasure (ν' m)) ∧ (∀ m, μ (A m) ≠ 0 → ν' m = μ[|A m]) ∧
      IsProbabilityMeasure P' ∧ iIndepFun (fun m (q : ℕ → ℕ × (ℕ → S)) => q m) P' ∧
      (∀ m, HasLaw (fun q : ℕ → ℕ × (ℕ → S) => q m)
        (Po((μ (A m)).toNNReal).prod (Measure.infinitePi fun _ : ℕ => ν' m)) P') ∧
      IdentDistrib (fun ω => (fun m => M ω (A m), fun m => (M ω).restrict (A m)))
        (fun q : ℕ → ℕ × (ℕ → S) => (fun m => (((q m).1 : ℕ) : ℝ≥0∞),
          fun m => ∑ l ∈ Finset.range (q m).1, Measure.dirac ((q m).2 l))) P P' := by
  obtain rfl : M = fun ω => poissonCountingMeasure
    (fun n => (B n ω).1) (fun n l => (B n ω).2 l) := funext hM
  obtain ⟨ν', hprob, hcond, hint⟩ :=
    exists_probabilityMeasure_family_sum_smul_eq μ hA hdisj hcover hfin (ν 0)
  obtain ⟨P', hP', hm', hi', hl'⟩ := exists_poissonBlocks ν' (fun m => (μ (A m)).toNNReal)
  have hid := identDistrib_poissonCountingMeasure_of_intensity_eq ν r ν'
    (fun m => (μ (A m)).toNNReal) hBm hB hlaw hm' hi' hl' (hμ.symm.trans hint.symm)
  let Φ : Measure S → (ℕ → ℝ≥0∞) × (ℕ → Measure S) := fun m =>
    (fun k => m (A k), fun k => m.restrict (A k))
  have hΦ : Measurable Φ := Measurable.prodMk
    (measurable_pi_iff.2 fun k => Measure.measurable_coe (hA k))
    (measurable_pi_iff.2 fun k => Measure.measurable_restrict (hA k))
  have hsupp : ∀ᵐ q ∂P', ∀ m l, l < (q m).1 → (q m).2 l ∈ A m := by
    rw [ae_all_iff]
    intro m
    by_cases h0 : μ (A m) = 0
    · have hr0 : (μ (A m)).toNNReal = 0 := by simp [h0]
      have hN : HasLaw (fun q : ℕ → ℕ × (ℕ → S) => (q m).1) Po(0) P' := by
        have h := measurePreserving_fst.hasLaw.comp (hl' m)
        rwa [hr0] at h
      filter_upwards [hN.ae_eq_zero_of_poisson_zero] with q hq l hl
      omega
    · have hpm : IsProbabilityMeasure μ[|A m] := hcond m h0 ▸ hprob m
      have hl : HasLaw (fun q : ℕ → ℕ × (ℕ → S) => (q m).2)
          (Measure.infinitePi fun _ : ℕ => μ[|A m]) P' := by
        rw [← hcond m h0]
        exact measurePreserving_snd.hasLaw.comp (hl' m)
      filter_upwards [ae_all_mem_of_hasLaw_infinitePi hl (hA m) (ae_cond_mem (hA m))] with q hq l _
      exact hq l
  refine ⟨ν', P', hprob, hcond, hP', hi', hl', ?_⟩
  refine (hid.comp hΦ).trans (IdentDistrib.of_ae_eq
    ((hΦ.comp (measurable_poissonCountingMeasure_comp hm')).aemeasurable) ?_)
  filter_upwards [hsupp] with q hq
  refine Prod.ext (funext fun m => ?_) (funext fun m => ?_)
  · exact poissonCountingMeasure_partition_apply _ _ A hdisj (fun n l hl => hq n l hl) hA m
  · exact poissonCountingMeasure_restrict_partition _ _ A hdisj (fun n l hl => hq n l hl) hA m

/-- **Poisson blocks with a prescribed σ-finite intensity.** Every σ-finite measure `μ` on a
nonempty space is `∑ₙ rₙ νₙ` for probability measures `νₙ` and weights `rₙ ∈ ℝ≥0`; with
`exists_poissonBlocks` this gives a Poisson process with intensity `μ`. -/
theorem exists_probabilityMeasure_sum_smul_eq_of_sigmaFinite [Nonempty S] (μ : Measure S)
    [SigmaFinite μ] :
    ∃ (ν : ℕ → Measure S) (r : ℕ → ℝ≥0), (∀ n, IsProbabilityMeasure (ν n)) ∧
      μ = Measure.sum fun n => (r n : ℝ≥0∞) • ν n := by
  obtain ⟨A, hA, hdisj, hcover, hfin⟩ := exists_measurable_partition_of_sigmaFinite μ
  obtain ⟨ν, hν, -, hsum⟩ := exists_probabilityMeasure_family_sum_smul_eq μ hA hdisj hcover
    (fun i => (hfin i).ne) (Measure.dirac (Classical.arbitrary S))
  exact ⟨ν, fun m => (μ (A m)).toNNReal, hν, hsum.symm⟩

end SpinGlasses
