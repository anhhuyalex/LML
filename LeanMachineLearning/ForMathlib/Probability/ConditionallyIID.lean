/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.ExchangeableMixture
public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Conditionally i.i.d. sequences are mixtures of i.i.d. sequences

Let `Y : ℕ → Ω → E` be a sequence with values in a standard Borel space and `X : Ω → β` a random
element such that, conditionally on `σ(X)`,

* the coordinates are independent: `P[∏ i ∈ t, f i (Y i) | σ(X)] = ∏ i ∈ t, P[f i (Y i) | σ(X)]`
  for finite `t` and bounded measurable `f i`, and
* the coordinates are identically distributed: `P[f (Y i) | σ(X)] = P[f (Y 0) | σ(X)]`.

Then the law of the whole sequence is the mixture of i.i.d. sequences
`(P.map X).bind (x ↦ (condDistrib (Y 0) X P x)^{⊗ℕ})`.  Only the values on indicator functions are
used, which is what the box measures of the product σ-algebra require.

This is the last step in the proof of de Finetti's theorem [Panchenko, 2013, Thm. 1.6]; the two
hypotheses are Eq. (1.88) and the identical-distribution remark following it.

## Main declarations

* `ProbabilityTheory.map_eq_bind_infinitePi_condDistrib`
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityTheory

variable {Ω β E : Type*} {mΩ : MeasurableSpace Ω} {mβ : MeasurableSpace β} [MeasurableSpace E]
  [StandardBorelSpace E] [Nonempty E] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → β} {Y : ℕ → Ω → E}

/-- **Conditionally i.i.d. sequences are mixtures of i.i.d. sequences.** If the coordinates of `Y`
are conditionally independent and identically distributed given `σ(X)` (in the sense of bounded
measurable test functions), then the law of `Y` is the mixture, over the law of `X`, of the product
measures `(condDistrib (Y 0) X P x)^{⊗ℕ}`. -/
theorem map_eq_bind_infinitePi_condDistrib (hX : Measurable X) (hY : ∀ i, Measurable (Y i))
    (hid : ∀ (i : ℕ) (f : E → ℝ), Measurable f → (∃ C, ∀ x, |f x| ≤ C) →
      P[fun ω => f (Y i ω) | mβ.comap X] =ᵐ[P] P[fun ω => f (Y 0 ω) | mβ.comap X])
    (hprod : ∀ (t : Finset ℕ) (f : ℕ → E → ℝ), (∀ i, Measurable (f i)) →
      (∀ i, ∃ C, ∀ x, |f i x| ≤ C) →
      P[fun ω => ∏ i ∈ t, f i (Y i ω) | mβ.comap X] =ᵐ[P]
        fun ω => ∏ i ∈ t, P[fun ω => f i (Y i ω) | mβ.comap X] ω) :
    P.map (fun ω i => Y i ω) =
      (P.map X).bind fun x => Measure.infinitePi fun _ : ℕ => condDistrib (Y 0) X P x := by
  set κ := condDistrib (Y 0) X P with hκdef
  have hν : Measurable fun x => Measure.infinitePi fun _ : ℕ => κ x :=
    Measure.measurable_infinitePi_const κ.measurable
  have hmeasY : Measurable fun ω i => Y i ω := measurable_pi_iff.2 hY
  have : IsProbabilityMeasure ((P.map X).bind fun x => Measure.infinitePi fun _ : ℕ => κ x) :=
    isProbabilityMeasure_bind hν.aemeasurable (ae_of_all _ fun x => inferInstance)
  refine ext_of_generate_finite _ generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => MeasurableSpace.isPiSystem_measurableSet)
      fun _ => MeasurableSet.univ) ?_ (by simp)
  rintro _ ⟨t, u, hu, rfl⟩
  have hu' : ∀ i, MeasurableSet (u i) := fun i => hu i (mem_univ i)
  have hbox : MeasurableSet ((t : Set ℕ).pi u) := .pi t.countable_toSet fun i _ => hu' i
  rw [Measure.map_apply hmeasY hbox]
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 ?_
  rw [Measure.bind_apply hbox hν.aemeasurable]
  simp_rw [Measure.infinitePi_pi (μ := fun _ : ℕ => κ _) (fun i _ => hu' i)]
  -- reduce to real numbers
  set f : ℕ → E → ℝ := fun i => (u i).indicator 1 with hf
  have hfm : ∀ i, Measurable (f i) := fun i => measurable_one.indicator (hu' i)
  have hfb : ∀ i, ∃ C, ∀ x, |f i x| ≤ C := fun i =>
    ⟨1, fun x => by by_cases hx : x ∈ u i <;> simp [hf, hx]⟩
  have hlhs : (P ((fun ω i => Y i ω) ⁻¹' (t : Set ℕ).pi u)).toReal =
      ∫ ω, ∏ i ∈ t, f i (Y i ω) ∂P := by
    classical
    have : ∀ ω, ∏ i ∈ t, f i (Y i ω) =
        ((fun ω i => Y i ω) ⁻¹' (t : Set ℕ).pi u).indicator 1 ω := by
      intro ω
      simp only [hf, Set.indicator_apply, Pi.one_apply, mem_preimage, Set.mem_pi,
        Finset.mem_coe]
      rw [Finset.prod_boole]
    simp_rw [this]
    rw [integral_indicator_one (hmeasY hbox)]
    rfl
  have hrhs : (∫⁻ x, ∏ i ∈ t, κ x (u i) ∂P.map X).toReal =
      ∫ x, ∏ i ∈ t, ∫ y, f i y ∂κ x ∂P.map X := by
    rw [← integral_toReal]
    · refine integral_congr_ae (ae_of_all _ fun x => ?_)
      dsimp only
      rw [ENNReal.toReal_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [hf]
      rw [integral_indicator_one (hu' i)]
      rfl
    · exact (Finset.measurable_prod _ fun i _ => κ.measurable_coe (hu' i)).aemeasurable
    · exact ae_of_all _ fun x => ENNReal.prod_lt_top fun i _ => measure_lt_top _ _
  have hψ : ∀ i, StronglyMeasurable fun x => ∫ y, f i y ∂κ x := fun i =>
    (hfm i).stronglyMeasurable.integral_kernel
  have hψP : StronglyMeasurable fun x => ∏ i ∈ t, ∫ y, f i y ∂κ x :=
    Finset.stronglyMeasurable_fun_prod _ fun i _ => hψ i
  have hall : ∀ᵐ ω ∂P, ∀ i, P[fun ω => f i (Y i ω) | mβ.comap X] ω = ∫ y, f i y ∂κ (X ω) := by
    rw [ae_all_iff]
    intro i
    obtain ⟨C, hC⟩ := hfb i
    have hint : Integrable (fun ω => f i (Y 0 ω)) P :=
      Integrable.of_bound ((hfm i).comp (hY 0)).aestronglyMeasurable C
        (.of_forall fun ω => by simpa using hC (Y 0 ω))
    filter_upwards [hid i (f i) (hfm i) (hfb i), condExp_ae_eq_integral_condDistrib hX
      (hY 0).aemeasurable (hfm i).stronglyMeasurable hint] with ω h1 h2
    rw [h1, h2]
  rw [hlhs, hrhs, integral_map hX.aemeasurable hψP.aestronglyMeasurable]
  calc ∫ ω, ∏ i ∈ t, f i (Y i ω) ∂P
      = ∫ ω, P[fun ω => ∏ i ∈ t, f i (Y i ω) | mβ.comap X] ω ∂P :=
        (integral_condExp hX.comap_le).symm
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [hprod t f hfm hfb, hall] with ω h1 h2
        rw [h1]
        exact Finset.prod_congr rfl fun i _ => h2 i

end ProbabilityTheory
