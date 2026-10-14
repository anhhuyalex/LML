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
# Conditionally independent sequences are mixtures of product measures

Let `Y : ι → Ω → E` be a family of random variables and `X : Ω → β` a random element such that,
conditionally on `σ(X)`,

* the coordinates are independent: `P[∏ i ∈ t, f i (Y i) | σ(X)] = ∏ i ∈ t, P[f i (Y i) | σ(X)]`
  for finite `t` and bounded measurable `f i`, and
* the coordinate `Y i` has law `κ i (X ω)`: `P[f (Y i) | σ(X)] = ∫ f d(κ i (X ·))`.

Then the joint law of `(X, Y)` is `P.map X ⊗ₘ K` where `K x = ⊗ᵢ κ i x`
(`map_prodMk_eq_compProd_infinitePi`).  Only the values on indicator functions are used, which is
what the box measures of the product σ-algebra require.  If the coordinates are moreover identically
distributed, the law of `Y` alone is the mixture
`(P.map X).bind (x ↦ (condDistrib (Y 0) X P x)^{⊗ℕ})` of i.i.d. sequences
(`map_eq_bind_infinitePi_condDistrib`).

The first statement is the last step in the proof of the Aldous–Hoover theorem (Theorem 1.5, where
the kernels `κ i` differ from coordinate to coordinate), the second one in the proof of de Finetti's
theorem [Panchenko, 2013, Thm. 1.6]; the hypotheses are Eqs. (1.88)/(1.94).

## Main declarations

* `ProbabilityTheory.map_prodMk_eq_compProd_infinitePi`
* `ProbabilityTheory.map_eq_bind_infinitePi_condDistrib`
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω β E ι : Type*} {mΩ : MeasurableSpace Ω} {mβ : MeasurableSpace β} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → β}

/-- **Conditionally independent coordinates form a mixture of product measures.**  If, given
`σ(X)`, the coordinates `Y i` are independent (`hprod`) with laws `κ i (X ω)` (`hcond`), then
`(X, Y)` has the law `P.map X ⊗ₘ K`, where `K x = ⊗ᵢ κ i x`. -/
theorem map_prodMk_eq_compProd_infinitePi {Y : ι → Ω → E} (κ : ι → Kernel β E)
    [∀ i, IsMarkovKernel (κ i)] (K : Kernel β (ι → E)) [IsMarkovKernel K]
    (hK : ∀ x, K x = Measure.infinitePi fun i => κ i x) (hX : Measurable X)
    (hY : ∀ i, Measurable (Y i))
    (hcond : ∀ (i : ι) (f : E → ℝ), Measurable f → (∃ C, ∀ x, |f x| ≤ C) →
      P[fun ω => f (Y i ω) | mβ.comap X] =ᵐ[P] fun ω => ∫ y, f y ∂κ i (X ω))
    (hprod : ∀ (t : Finset ι) (f : ι → E → ℝ), (∀ i, Measurable (f i)) →
      (∀ i, ∃ C, ∀ x, |f i x| ≤ C) →
      P[fun ω => ∏ i ∈ t, f i (Y i ω) | mβ.comap X] =ᵐ[P]
        fun ω => ∏ i ∈ t, P[fun ω => f i (Y i ω) | mβ.comap X] ω) :
    P.map (fun ω => (X ω, fun i => Y i ω)) = (P.map X) ⊗ₘ K := by
  have hmeasY : Measurable fun ω i => Y i ω := measurable_pi_iff.2 hY
  have hmeasXY : Measurable fun ω => (X ω, fun i => Y i ω) := hX.prodMk hmeasY
  refine ext_of_generate_finite _ (generateFrom_eq_prod MeasurableSpace.generateFrom_measurableSet
      generateFrom_squareCylinders isCountablySpanning_measurableSet ?_).symm
    (IsPiSystem.prod MeasurableSpace.isPiSystem_measurableSet
      (isPiSystem_squareCylinders (fun _ => MeasurableSpace.isPiSystem_measurableSet)
        fun _ => MeasurableSet.univ)) ?_ (by simp)
  · exact ⟨fun _ => univ, fun _ => ⟨∅, fun _ => univ, by simp, by simp⟩, iUnion_const _⟩
  rintro _ ⟨A, hA, _, ⟨t, u, hu, rfl⟩, rfl⟩
  have hu' : ∀ i, MeasurableSet (u i) := fun i => hu i (mem_univ i)
  have hbox : MeasurableSet ((t : Set ι).pi u) := .pi t.countable_toSet fun i _ => hu' i
  rw [Measure.map_apply hmeasXY (hA.prod hbox)]
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 ?_
  rw [Measure.compProd_apply_prod hA hbox]
  simp_rw [hK, Measure.infinitePi_pi (μ := fun i => κ i _) (fun i _ => hu' i)]
  -- reduce to real numbers
  set f : ι → E → ℝ := fun i => (u i).indicator 1 with hf
  have hfm : ∀ i, Measurable (f i) := fun i => measurable_one.indicator (hu' i)
  have hfb : ∀ i, ∃ C, ∀ x, |f i x| ≤ C := fun i =>
    ⟨1, fun x => by by_cases hx : x ∈ u i <;> simp [hf, hx]⟩
  have hXA : MeasurableSet (X ⁻¹' A) := hX hA
  have hlhs : (P ((fun ω => (X ω, fun i => Y i ω)) ⁻¹' (A ×ˢ (t : Set ι).pi u))).toReal =
      ∫ ω in X ⁻¹' A, ∏ i ∈ t, f i (Y i ω) ∂P := by
    classical
    have : ∀ ω, (X ⁻¹' A).indicator (fun ω => ∏ i ∈ t, f i (Y i ω)) ω =
        ((fun ω => (X ω, fun i => Y i ω)) ⁻¹' (A ×ˢ (t : Set ι).pi u)).indicator 1 ω := by
      intro ω
      by_cases hω : X ω ∈ A
      · simp only [hf, Set.indicator_apply, Pi.one_apply, mem_preimage, Set.mem_pi,
          Finset.mem_coe, hω, Set.mem_prod, true_and]
        rw [Finset.prod_boole]
        simp
      · simp [hω]
    rw [← integral_indicator hXA]
    simp_rw [this]
    rw [integral_indicator_one (hmeasXY (hA.prod hbox))]
    rfl
  have hrhs : (∫⁻ x in A, ∏ i ∈ t, κ i x (u i) ∂P.map X).toReal =
      ∫ x in A, ∏ i ∈ t, ∫ y, f i y ∂κ i x ∂P.map X := by
    rw [← integral_toReal]
    · refine setIntegral_congr_fun hA fun x _ => ?_
      rw [ENNReal.toReal_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [hf]
      rw [integral_indicator_one (hu' i)]
      rfl
    · exact (Finset.measurable_prod _ fun i _ => (κ i).measurable_coe (hu' i)).aemeasurable
    · exact ae_of_all _ fun x => ENNReal.prod_lt_top fun i _ => measure_lt_top _ _
  have hψ : ∀ i, StronglyMeasurable fun x => ∫ y, f i y ∂κ i x := fun i =>
    (hfm i).stronglyMeasurable.integral_kernel
  have hψP : StronglyMeasurable fun x => ∏ i ∈ t, ∫ y, f i y ∂κ i x :=
    Finset.stronglyMeasurable_fun_prod _ fun i _ => hψ i
  have hall : ∀ᵐ ω ∂P, ∀ i ∈ t,
      P[fun ω => f i (Y i ω) | mβ.comap X] ω = ∫ y, f i y ∂κ i (X ω) :=
    (Finset.eventually_all t).2 fun i _ => hcond i (f i) (hfm i) (hfb i)
  have hgint : Integrable (fun ω => ∏ i ∈ t, f i (Y i ω)) P := by
    obtain ⟨C, hC⟩ : ∃ C, ∀ ω, ‖∏ i ∈ t, f i (Y i ω)‖ ≤ C := by
      refine ⟨∏ i ∈ t, (hfb i).choose, fun ω => ?_⟩
      rw [norm_prod]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ =>
        (hfb i).choose_spec _
    exact Integrable.of_bound
      (Finset.measurable_prod _ fun i _ => (hfm i).comp (hY i)).aestronglyMeasurable C
      (.of_forall hC)
  rw [hlhs, hrhs, setIntegral_map hA hψP.aestronglyMeasurable hX.aemeasurable,
    ← setIntegral_condExp hX.comap_le hgint ⟨A, hA, rfl⟩]
  refine setIntegral_congr_ae hXA ?_
  filter_upwards [hprod t f hfm hfb, hall] with ω h1 h2 _
  rw [h1]
  exact Finset.prod_congr rfl h2

/-- **Conditionally i.i.d. sequences are mixtures of i.i.d. sequences.** If the coordinates of `Y`
are conditionally independent and identically distributed given `σ(X)` (in the sense of bounded
measurable test functions), then the law of `Y` is the mixture, over the law of `X`, of the product
measures `(condDistrib (Y 0) X P x)^{⊗ℕ}`. -/
theorem map_eq_bind_infinitePi_condDistrib [StandardBorelSpace E] [Nonempty E] {Y : ℕ → Ω → E}
    (hX : Measurable X) (hY : ∀ i, Measurable (Y i))
    (hid : ∀ (i : ℕ) (f : E → ℝ), Measurable f → (∃ C, ∀ x, |f x| ≤ C) →
      P[fun ω => f (Y i ω) | mβ.comap X] =ᵐ[P] P[fun ω => f (Y 0 ω) | mβ.comap X])
    (hprod : ∀ (t : Finset ℕ) (f : ℕ → E → ℝ), (∀ i, Measurable (f i)) →
      (∀ i, ∃ C, ∀ x, |f i x| ≤ C) →
      P[fun ω => ∏ i ∈ t, f i (Y i ω) | mβ.comap X] =ᵐ[P]
        fun ω => ∏ i ∈ t, P[fun ω => f i (Y i ω) | mβ.comap X] ω) :
    P.map (fun ω i => Y i ω) =
      (P.map X).bind fun x => Measure.infinitePi fun _ : ℕ => condDistrib (Y 0) X P x := by
  set κ := condDistrib (Y 0) X P with hκdef
  let K : Kernel β (ℕ → E) :=
    ⟨fun x => Measure.infinitePi fun _ : ℕ => κ x,
      Measure.measurable_infinitePi_const κ.measurable⟩
  have : IsMarkovKernel K :=
    ⟨fun x => inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi _))⟩
  have hmeasY : Measurable fun ω i => Y i ω := measurable_pi_iff.2 hY
  have hjoint := map_prodMk_eq_compProd_infinitePi (P := P) (Y := Y) (fun _ => κ) K (fun _ => rfl)
    hX hY (fun i f hf hfb => ?_) hprod
  · calc P.map (fun ω i => Y i ω)
        = (P.map (fun ω => (X ω, fun i => Y i ω))).snd := by
          rw [Measure.snd, Measure.map_map measurable_snd (hX.prodMk hmeasY)]
          rfl
      _ = (P.map X).bind K := by rw [hjoint, Measure.snd_compProd]
  · obtain ⟨C, hC⟩ := hfb
    have hint : Integrable (fun ω => f (Y 0 ω)) P :=
      Integrable.of_bound (hf.comp (hY 0)).aestronglyMeasurable C
        (.of_forall fun ω => by simpa using hC (Y 0 ω))
    filter_upwards [hid i f hf ⟨C, hC⟩, condExp_ae_eq_integral_condDistrib hX
      (hY 0).aemeasurable hf.stronglyMeasurable hint] with ω h1 h2
    rw [h1, h2]

end ProbabilityTheory
