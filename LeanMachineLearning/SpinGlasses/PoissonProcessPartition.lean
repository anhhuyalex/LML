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
with `0 < μ(Aₘ) < ∞`. Then the pair `((M(Aₘ))ₘ, (M|Aₘ)ₘ)` has the same law as
`((Nₘ)ₘ, (∑_{l<Nₘ} δ_{Zₘₗ})ₘ)` for independent blocks `(Nₘ, (Zₘₗ)ₗ)` with law
`Po(μ(Aₘ)) ⊗ μ[|Aₘ]^{⊗ℕ}`. In particular, conditionally on the counts, the restriction of `M`
to `Aₘ` is the counting measure of an i.i.d. sample of size `M(Aₘ)` from `μ[|Aₘ]`, independently
over `m`. -/
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
    (hpos : ∀ m, μ (A m) ≠ 0) (hfin : ∀ m, μ (A m) ≠ ∞) :
    ∃ P' : Measure (ℕ → ℕ × (ℕ → S)), IsProbabilityMeasure P' ∧
      iIndepFun (fun m (q : ℕ → ℕ × (ℕ → S)) => q m) P' ∧
      (∀ m, HasLaw (fun q : ℕ → ℕ × (ℕ → S) => q m)
        (Po((μ (A m)).toNNReal).prod (Measure.infinitePi fun _ : ℕ => μ[|A m])) P') ∧
      IdentDistrib (fun ω => (fun m => M ω (A m), fun m => (M ω).restrict (A m)))
        (fun q : ℕ → ℕ × (ℕ → S) => (fun m => (((q m).1 : ℕ) : ℝ≥0∞),
          fun m => ∑ l ∈ Finset.range (q m).1, Measure.dirac ((q m).2 l))) P P' := by
  obtain rfl : M = fun ω => poissonCountingMeasure
    (fun n => (B n ω).1) (fun n l => (B n ω).2 l) := funext hM
  have hprob : ∀ m, IsProbabilityMeasure (μ[|A m]) := fun m =>
    cond_isProbabilityMeasure_of_finite (hpos m) (hfin m)
  obtain ⟨P', hP', hm', hi', hl'⟩ := exists_poissonBlocks (fun m => μ[|A m])
    (fun m => (μ (A m)).toNNReal)
  have hint : (Measure.sum fun m => ((μ (A m)).toNNReal : ℝ≥0∞) • μ[|A m]) = μ := by
    simpa only [ENNReal.coe_toNNReal (hfin _)] using
      sum_meas_smul_cond_of_iUnion_eq_univ hA hdisj hcover hfin
  have hid := identDistrib_poissonCountingMeasure_of_intensity_eq ν r (fun m => μ[|A m])
    (fun m => (μ (A m)).toNNReal) hBm hB hlaw hm' hi' hl' (hμ.symm.trans hint.symm)
  let Φ : Measure S → (ℕ → ℝ≥0∞) × (ℕ → Measure S) := fun m =>
    (fun k => m (A k), fun k => m.restrict (A k))
  have hΦ : Measurable Φ := Measurable.prodMk
    (measurable_pi_iff.2 fun k => Measure.measurable_coe (hA k))
    (measurable_pi_iff.2 fun k => Measure.measurable_restrict (hA k))
  have hsupp : ∀ᵐ q ∂P', ∀ m l, (q m).2 l ∈ A m := by
    rw [ae_all_iff]
    intro m
    rw [ae_all_iff]
    intro l
    have hl : HasLaw (fun q : ℕ → ℕ × (ℕ → S) => (q m).2 l) (μ[|A m]) P' :=
      (hasLaw_eval_infinitePi (fun _ : ℕ => μ[|A m]) l).comp
        (measurePreserving_snd.hasLaw.comp (hl' m))
    refine (ae_map_iff hl.aemeasurable (hA m)).1 ?_
    rw [hl.map_eq]
    exact ae_cond_mem (hA m)
  refine ⟨P', hP', hi', hl', ?_⟩
  refine (hid.comp hΦ).trans (IdentDistrib.of_ae_eq
    ((hΦ.comp (measurable_poissonCountingMeasure_comp hm')).aemeasurable) ?_)
  filter_upwards [hsupp] with q hq
  refine Prod.ext (funext fun m => ?_) (funext fun m => ?_)
  · exact poissonCountingMeasure_partition_apply _ _ A hdisj (fun n l _ => hq n l) hA m
  · exact poissonCountingMeasure_restrict_partition _ _ A hdisj (fun n l _ => hq n l) hA m

end SpinGlasses
