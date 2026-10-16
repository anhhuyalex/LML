/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletTransform
public import Mathlib.Probability.Distributions.Gaussian.Real
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.RestrictPartition
public import LeanMachineLearning.ForMathlib.Probability.IdentDistribReplica
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.SignedToReal
public import LeanMachineLearning.SpinGlasses.PoissonDirichletLogSum

/-!
# Gaussian marks for Poisson–Dirichlet invariance

The power-law Poisson-process transformation becomes stationary when Gaussian marks are
exponentially tilted and shifted by the corresponding Cameron–Martin drift.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SpinGlasses

/-- Exponential tilting of a standard Gaussian, before normalizing: the resulting
measure has mean `a` and total mass `exp (a²/2)`. -/
theorem gaussianReal_withDensity_exp_mul (a : ℝ) :
    (gaussianReal 0 1).withDensity (fun g => ENNReal.ofReal (Real.exp (a * g))) =
      ENNReal.ofReal (Real.exp (a ^ 2 / 2)) • gaussianReal a 1 := by
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) (one_ne_zero : (1 : NNReal) ≠ 0),
    gaussianReal_of_var_ne_zero a (one_ne_zero : (1 : NNReal) ≠ 0)]
  · apply Measure.ext
    intro s hs
    rw [withDensity_apply _ hs, Measure.smul_apply, withDensity_apply _ hs,
      setLIntegral_withDensity_eq_setLIntegral_mul _ (by fun_prop) (by fun_prop)]
    · simp only [smul_eq_mul]
      rw [← lintegral_const_mul _ (by fun_prop : Measurable (gaussianPDF a 1))]
      apply setLIntegral_congr_fun hs
      intro x _
      change gaussianPDF 0 1 x * ENNReal.ofReal (Real.exp (a * x)) =
        ENNReal.ofReal (Real.exp (a ^ 2 / 2)) * gaussianPDF a 1 x
      simp only [gaussianPDF, gaussianPDFReal]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have he : a * x + (-(x - 0) ^ 2 / (2 * (1 : ℝ))) =
          a ^ 2 / 2 + (-(x - a) ^ 2 / (2 * (1 : ℝ))) := by ring
      simp only [NNReal.coe_one, mul_one] at *
      calc
        _ = (√(2 * Real.pi))⁻¹ * Real.exp
            (a * x + (-(x - 0) ^ 2 / 2)) := by rw [Real.exp_add]; ring
        _ = (√(2 * Real.pi))⁻¹ * Real.exp
            (a ^ 2 / 2 + (-(x - a) ^ 2 / 2)) := by rw [he]
        _ = _ := by rw [Real.exp_add]; ring
    · exact hs

/-- The `ζ`-th power of the Cameron–Martin multiplier `exp (t (g - tζ/2))` is a constant times
the density `exp (tζ g)` of the exponential tilting. -/
theorem ofReal_exp_cameronMartin_rpow (ζ t g : ℝ) :
    ENNReal.ofReal (Real.exp (t * (g - t * ζ / 2))) ^ ζ =
      ENNReal.ofReal (Real.exp (-(t * ζ) ^ 2 / 2)) *
        ENNReal.ofReal (Real.exp ((t * ζ) * g)) := by
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 1
  ring_nf

/-- The ζ-power Gaussian multiplier has expectation one. -/
theorem lintegral_gaussian_multiplier (ζ t : ℝ) :
    ∫⁻ g, ENNReal.ofReal (Real.exp (t * (g - t * ζ / 2))) ^ ζ
      ∂gaussianReal 0 1 = 1 := by
  simp_rw [ofReal_exp_cameronMartin_rpow]
  rw [lintegral_const_mul]
  · have hm : (∫⁻ g, ENNReal.ofReal (Real.exp ((t * ζ) * g)) ∂gaussianReal 0 1) =
      ENNReal.ofReal (Real.exp ((t * ζ) ^ 2 / 2)) := by
      calc
        _ = ((gaussianReal 0 1).withDensity
          (fun g => ENNReal.ofReal (Real.exp ((t * ζ) * g)))) Set.univ := by
            rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
        _ = _ := by rw [gaussianReal_withDensity_exp_mul, Measure.smul_apply]; simp
    rw [hm]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    simp [show -(t * ζ) ^ 2 / 2 + (t * ζ) ^ 2 / 2 = 0 by ring]
  · fun_prop

/-- The size-biased law of a Gaussian mark shifted by the Cameron–Martin drift
is again standard Gaussian. This is the mark-law calculation in Lemma 2.3. -/
theorem poissonMarkTilt_gaussian (ζ t : ℝ) :
    poissonMarkTilt ζ ((gaussianReal 0 1).map
      (fun g => (Real.exp (t * (g - t * ζ / 2)), g - t * ζ))) =
        gaussianReal 0 1 := by
  let f : ℝ → ℝ × ℝ := fun g => (Real.exp (t * (g - t * ζ / 2)), g - t * ζ)
  have hf : Measurable f := by fun_prop
  have hm : (∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂(gaussianReal 0 1).map f) = 1 := by
    rw [lintegral_map (by fun_prop) hf]
    exact lintegral_gaussian_multiplier ζ t
  rw [poissonMarkTilt, hm, inv_one, one_smul]
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (by fun_prop) hs,
    withDensity_apply _ (hs.preimage (by fun_prop))]
  rw [← lintegral_indicator (hs.preimage (by fun_prop))]
  rw [lintegral_map
    ((by fun_prop : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 ^ ζ)).indicator
      (hs.preimage (by fun_prop))) hf]
  change (∫⁻ g, ((fun g : ℝ => g - t * ζ) ⁻¹' s).indicator
    (fun g => ENNReal.ofReal (Real.exp (t * (g - t * ζ / 2))) ^ ζ) g
    ∂gaussianReal 0 1) = _
  simp_rw [ofReal_exp_cameronMartin_rpow]
  simp_rw [Set.indicator_const_mul]
  rw [lintegral_const_mul _ ((by fun_prop : Measurable
    (fun g : ℝ => ENNReal.ofReal (Real.exp (t * ζ * g)))).indicator
      (hs.preimage (by fun_prop)))]
  have ht := gaussianReal_withDensity_exp_mul (t * ζ)
  have heq : ∫⁻ g in (fun g : ℝ => g - t * ζ) ⁻¹' s,
      ENNReal.ofReal (Real.exp (t * ζ * g)) ∂gaussianReal 0 1 =
      ENNReal.ofReal (Real.exp ((t * ζ) ^ 2 / 2)) *
        gaussianReal (t * ζ) 1 ((fun g : ℝ => g - t * ζ) ⁻¹' s) := by
    rw [← withDensity_apply _ (hs.preimage (by fun_prop)), ht, Measure.smul_apply]
    rfl
  rw [lintegral_indicator (hs.preimage (by fun_prop)), heq]
  rw [← Measure.map_apply (by fun_prop : Measurable (fun g : ℝ => g - t * ζ)) hs]
  rw [gaussianReal_map_sub_const]
  have hc : ENNReal.ofReal (Real.exp (-(t * ζ) ^ 2 / 2)) *
      ENNReal.ofReal (Real.exp ((t * ζ) ^ 2 / 2)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add,
      show -(t * ζ) ^ 2 / 2 + (t * ζ) ^ 2 / 2 = 0 by ring]
    simp
  rw [← mul_assoc, hc, one_mul, sub_self]

/-- Gaussian specialization of Theorem 2.6: the *marked counting measures* are identically
 distributed after exponential rescaling and Cameron–Martin translation. The two constructions
 may use different independent Poisson block decompositions. -/
theorem identDistrib_poissonDirichlet_gaussian_transform
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ζ : ℝ} (hζ : 0 < ζ) (t : ℝ)
    (ν : ℕ → Measure (ℝ × (ℝ × ℝ))) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → NNReal)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × (ℝ × ℝ))}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod ((gaussianReal 0 1).map
        (fun g => (Real.exp (t * (g - t * ζ / 2)), g - t * ζ))) =
      Measure.sum (fun n => (r n : ENNReal) • ν n))
    (ν' : ℕ → Measure (ℝ × ℝ)) [∀ n, IsProbabilityMeasure (ν' n)] (r' : ℕ → NNReal)
    {B' : ℕ → Ω' → ℕ × (ℕ → ℝ × ℝ)}
    (hBm' : ∀ n, Measurable (B' n)) (hB' : iIndepFun B' Q)
    (hlaw' : ∀ n, HasLaw (B' n) (Po(r' n).prod
      (Measure.infinitePi fun _ : ℕ => ν' n)) Q)
    (hμ' : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum (fun n => (r' n : ENNReal) • ν' n)) :
    IdentDistrib
      (fun ω => (poissonCountingMeasure (fun n => (B n ω).1)
        (fun n l => (B n ω).2 l)).map
          (fun p : ℝ × (ℝ × ℝ) => (p.1 * p.2.1, p.2.2)))
      (fun ω => poissonCountingMeasure (fun n => (B' n ω).1)
        (fun n l => (B' n ω).2 l)) P Q := by
  let τ : Measure (ℝ × ℝ) := (gaussianReal 0 1).map
    (fun g => (Real.exp (t * (g - t * ζ / 2)), g - t * ζ))
  have hτprob : IsProbabilityMeasure τ := inferInstance
  have hτ : ∀ᵐ p ∂τ, 0 < p.1 := by
    apply (ae_map_iff (by fun_prop : AEMeasurable
      (fun g : ℝ => (Real.exp (t * (g - t * ζ / 2)), g - t * ζ))
      (gaussianReal 0 1)) (measurableSet_lt measurable_const measurable_fst)).2
    exact Filter.Eventually.of_forall (fun g => Real.exp_pos _)
  have hm : (∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂τ) = 1 := by
    rw [lintegral_map (by fun_prop) (by fun_prop)]
    exact lintegral_gaussian_multiplier ζ t
  have htilt : poissonMarkTilt ζ τ = gaussianReal 0 1 :=
    poissonMarkTilt_gaussian ζ t
  have hid := identDistrib_poissonDirichlet_marked_transform hζ τ hτ
    (hm ▸ zero_lt_one) (hm ▸ ENNReal.one_lt_top) ν r hBm hB hlaw hμ
    ν' r' hBm' hB' hlaw' (htilt ▸ hμ')
  have hscale : (1 : ℝ) ^ ζ⁻¹ = 1 := by simp
  simp only [hm, ENNReal.toReal_one, hscale, mul_one] at hid
  convert hid using 1
  funext ω
  simp

/-- The Gaussian transformation preserves the law of the *unmarked* mass process: forgetting
the marks, the transformed and the reference counting measures are identically distributed. -/
theorem identDistrib_poissonDirichlet_gaussian_masses
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ζ : ℝ} (hζ : 0 < ζ) (t : ℝ)
    (ν : ℕ → Measure (ℝ × (ℝ × ℝ))) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → NNReal)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × (ℝ × ℝ))}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod ((gaussianReal 0 1).map
        (fun g => (Real.exp (t * (g - t * ζ / 2)), g - t * ζ))) =
      Measure.sum (fun n => (r n : ENNReal) • ν n))
    (ν' : ℕ → Measure (ℝ × ℝ)) [∀ n, IsProbabilityMeasure (ν' n)] (r' : ℕ → NNReal)
    {B' : ℕ → Ω' → ℕ × (ℕ → ℝ × ℝ)}
    (hBm' : ∀ n, Measurable (B' n)) (hB' : iIndepFun B' Q)
    (hlaw' : ∀ n, HasLaw (B' n) (Po(r' n).prod
      (Measure.infinitePi fun _ : ℕ => ν' n)) Q)
    (hμ' : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum (fun n => (r' n : ENNReal) • ν' n)) :
    IdentDistrib
      (fun ω => (poissonCountingMeasure (fun k => (B k ω).1) (fun k l => (B k ω).2 l)).map
        (fun p : ℝ × (ℝ × ℝ) => p.1 * p.2.1))
      (fun ω => poissonCountingMeasure (fun k => (B' k ω).1)
        (fun k l => ((B' k ω).2 l).1)) P Q := by
  have hid := (identDistrib_poissonDirichlet_gaussian_transform hζ t ν r
    hBm hB hlaw hμ ν' r' hBm' hB' hlaw' hμ').comp (Measure.measurable_map Prod.fst measurable_fst)
  simpa only [Function.comp_def, Measure.map_map measurable_fst (by fun_prop : Measurable
    fun p : ℝ × (ℝ × ℝ) => (p.1 * p.2.1, p.2.2)), poissonCountingMeasure_map_fst] using hid

/-- The ranked masses of a counting measure are measurable in the Giry sigma algebra. -/
theorem measurable_rankedMasses :
    Measurable (fun M : Measure ℝ => fun n : ℕ => nthLargestAtom n M) :=
  measurable_pi_iff.2 measurable_nthLargestAtom

/-- Gaussian rescaling preserves the joint law of *all ranked masses*. -/
theorem identDistrib_poissonDirichlet_gaussian_rankedMasses
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ζ : ℝ} (hζ : 0 < ζ) (t : ℝ)
    (ν : ℕ → Measure (ℝ × (ℝ × ℝ))) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → NNReal)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × (ℝ × ℝ))}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod ((gaussianReal 0 1).map
        (fun g => (Real.exp (t * (g - t * ζ / 2)), g - t * ζ))) =
      Measure.sum (fun n => (r n : ENNReal) • ν n))
    (ν' : ℕ → Measure (ℝ × ℝ)) [∀ n, IsProbabilityMeasure (ν' n)] (r' : ℕ → NNReal)
    {B' : ℕ → Ω' → ℕ × (ℕ → ℝ × ℝ)}
    (hBm' : ∀ n, Measurable (B' n)) (hB' : iIndepFun B' Q)
    (hlaw' : ∀ n, HasLaw (B' n) (Po(r' n).prod
      (Measure.infinitePi fun _ : ℕ => ν' n)) Q)
    (hμ' : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum (fun n => (r' n : ENNReal) • ν' n)) :
    IdentDistrib
      (fun ω n => nthLargestAtom n
        ((poissonCountingMeasure (fun k => (B k ω).1) (fun k l => (B k ω).2 l)).map
          (fun p : ℝ × (ℝ × ℝ) => p.1 * p.2.1)))
      (fun ω n => nthLargestAtom n
        (poissonCountingMeasure (fun k => (B' k ω).1) (fun k l => ((B' k ω).2 l).1))) P Q :=
  (identDistrib_poissonDirichlet_gaussian_masses hζ t ν r hBm hB hlaw hμ ν' r' hBm' hB' hlaw'
    hμ').comp measurable_rankedMasses

/-- Gaussian rescaling also preserves the law of the entire sequence of normalized ranked
weights. The normalization is the existing Poisson–Dirichlet weight observable. -/
theorem identDistrib_poissonDirichlet_gaussian_weights
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ζ : ℝ} (hζ : 0 < ζ) (t : ℝ)
    (ν : ℕ → Measure (ℝ × (ℝ × ℝ))) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → NNReal)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × (ℝ × ℝ))}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod ((gaussianReal 0 1).map
        (fun g => (Real.exp (t * (g - t * ζ / 2)), g - t * ζ))) =
      Measure.sum (fun n => (r n : ENNReal) • ν n))
    (ν' : ℕ → Measure (ℝ × ℝ)) [∀ n, IsProbabilityMeasure (ν' n)] (r' : ℕ → NNReal)
    {B' : ℕ → Ω' → ℕ × (ℕ → ℝ × ℝ)}
    (hBm' : ∀ n, Measurable (B' n)) (hB' : iIndepFun B' Q)
    (hlaw' : ∀ n, HasLaw (B' n) (Po(r' n).prod
      (Measure.infinitePi fun _ : ℕ => ν' n)) Q)
    (hμ' : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum (fun n => (r' n : ENNReal) • ν' n)) :
    IdentDistrib
      (fun ω n => poissonDirichletWeight n
        ((poissonCountingMeasure (fun k => (B k ω).1) (fun k l => (B k ω).2 l)).map
          (fun p : ℝ × (ℝ × ℝ) => p.1 * p.2.1)))
      (fun ω n => poissonDirichletWeight n
        (poissonCountingMeasure (fun k => (B' k ω).1) (fun k l => ((B' k ω).2 l).1))) P Q :=
  (identDistrib_poissonDirichlet_gaussian_masses hζ t ν r hBm hB hlaw hμ ν' r' hBm' hB' hlaw'
    hμ').comp (measurable_pi_iff.2 measurable_poissonDirichletWeight)

/-- The open quadrant `{x > 0}` is exhausted by the sets `{x > 1/(k+1)}`. -/
theorem iUnion_Ioi_inv_succ_prod_univ {S : Type*} :
    (⋃ k : ℕ, Set.Ioi (1 / ((k : ℝ) + 1)) ×ˢ (Set.univ : Set S)) =
      Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set S) := by
  ext ⟨x, y⟩
  simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true]
  refine ⟨fun ⟨k, hk⟩ => lt_trans (by positivity) hk, fun hx => ?_⟩
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hx
  exact ⟨k, hk⟩

/-- **Lemma 2.3, order-free form (Panchenko, Eq. (2.33)).** Replica integrals of the Gaussian
marked process are invariant: for every finite or infinite family of measurable
`Φᵢ : (ℝ × ℝ)ⁿ → [0, ∞]`, the family `(∫ Φᵢ d(M ↾ {x > 0})^{⊗n})ᵢ` has the same joint law for the
transformed counting measure `M_t` (points `(u x, g - tζ)`) and for the reference counting measure
`M_0` (points `(u, g)`). Taking `Φ` to be `∏ₗ xₗ` times an observable `f(R) ∏ₗ yₗ^{kₗ}` of the
overlaps `Rₗₗ' = 1{pₗ = pₗ'}` and the marks gives, after dividing by the total mass to the power
`n`, the statement of the book, with no enumeration of the atoms. -/
theorem identDistrib_lintegral_pi_poissonDirichlet_gaussian
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ζ : ℝ} (hζ : 0 < ζ) (t : ℝ)
    (ν : ℕ → Measure (ℝ × (ℝ × ℝ))) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → NNReal)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × (ℝ × ℝ))}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod ((gaussianReal 0 1).map
        (fun g => (Real.exp (t * (g - t * ζ / 2)), g - t * ζ))) =
      Measure.sum (fun n => (r n : ENNReal) • ν n))
    (ν' : ℕ → Measure (ℝ × ℝ)) [∀ n, IsProbabilityMeasure (ν' n)] (r' : ℕ → NNReal)
    {B' : ℕ → Ω' → ℕ × (ℕ → ℝ × ℝ)}
    (hBm' : ∀ n, Measurable (B' n)) (hB' : iIndepFun B' Q)
    (hlaw' : ∀ n, HasLaw (B' n) (Po(r' n).prod
      (Measure.infinitePi fun _ : ℕ => ν' n)) Q)
    (hμ' : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum (fun n => (r' n : ENNReal) • ν' n))
    (n : ℕ) {ι : Type*} {Φ : ι → (Fin n → ℝ × ℝ) → ℝ≥0∞} (hΦ : ∀ i, Measurable (Φ i)) :
    IdentDistrib
      (fun ω i => ∫⁻ q, Φ i q ∂Measure.pi fun _ : Fin n =>
        ((poissonCountingMeasure (fun k => (B k ω).1) (fun k l => (B k ω).2 l)).map
          (fun p : ℝ × (ℝ × ℝ) => (p.1 * p.2.1, p.2.2))).restrict (Set.Ioi 0 ×ˢ Set.univ))
      (fun ω i => ∫⁻ q, Φ i q ∂Measure.pi fun _ : Fin n =>
        (poissonCountingMeasure (fun k => (B' k ω).1) (fun k l => (B' k ω).2 l)).restrict
          (Set.Ioi 0 ×ˢ Set.univ)) P Q := by
  have hid := identDistrib_poissonDirichlet_gaussian_transform hζ t ν r hBm hB hlaw hμ ν' r' hBm'
    hB' hlaw' hμ'
  let C : ℕ → Set (ℝ × ℝ) := fun k => Set.Ioi (1 / ((k : ℝ) + 1)) ×ˢ Set.univ
  have hC : ∀ k, MeasurableSet (C k) := fun k => measurableSet_Ioi.prod MeasurableSet.univ
  have hY : ∀ᵐ ω ∂Q, ∀ k, poissonCountingMeasure (fun n => (B' n ω).1)
      (fun n l => (B' n ω).2 l) (C k) < ∞ := by
    rw [ae_all_iff]
    intro k
    exact ae_poissonCountingMeasure_Ioi_prod_univ_lt_top hζ (gaussianReal 0 1) ν' r' hBm' hB'
      hlaw' hμ' (by positivity)
  have hX := hid.symm.ae_snd (measurableSet_forall_measure_lt_top hC) hY
  have h := hid.lintegral_pi_restrict hC hX hY n hΦ
  simpa only [C, iUnion_Ioi_inv_succ_prod_univ] using h

/-- **Lemma 2.3 (Panchenko, Eq. (2.33)) for the Gaussian marked process, as an equality in law.**
For `n` replicas, exponents `kₗ`, and a measurable `f` of the overlap matrix
`Rₗₗ' = 1{pₗ = pₗ'}`, the replica average
`⟨f(R) ∏ₗ yₗ^{kₗ}⟩_M = ∫ (∏ₗ xₗ) f(R) ∏ₗ yₗ^{kₗ} dM^{⊗n} / ∫ ∏ₗ xₗ dM^{⊗n}`
(integrals against `M` restricted to `{x > 0}`; the Gibbs weight of an atom is `x / ∫ x dM`) has
the same law for `M_t` (points `(u x, g - tζ)`) and for `M_0` (points `(u, g)`).
No integrability is assumed: both sides use the same junk value where an integral diverges. -/
theorem identDistrib_replica_average_poissonDirichlet_gaussian
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ζ : ℝ} (hζ : 0 < ζ) (t : ℝ)
    (ν : ℕ → Measure (ℝ × (ℝ × ℝ))) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → NNReal)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × (ℝ × ℝ))}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod ((gaussianReal 0 1).map
        (fun g => (Real.exp (t * (g - t * ζ / 2)), g - t * ζ))) =
      Measure.sum (fun n => (r n : ENNReal) • ν n))
    (ν' : ℕ → Measure (ℝ × ℝ)) [∀ n, IsProbabilityMeasure (ν' n)] (r' : ℕ → NNReal)
    {B' : ℕ → Ω' → ℕ × (ℕ → ℝ × ℝ)}
    (hBm' : ∀ n, Measurable (B' n)) (hB' : iIndepFun B' Q)
    (hlaw' : ∀ n, HasLaw (B' n) (Po(r' n).prod
      (Measure.infinitePi fun _ : ℕ => ν' n)) Q)
    (hμ' : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum (fun n => (r' n : ENNReal) • ν' n))
    (n : ℕ) (k : Fin n → ℕ) {f : (Fin n → Fin n → ℝ) → ℝ} (hf : Measurable f) :
    IdentDistrib
      (fun ω =>
        (∫ q, (∏ l, (q l).1) * (f (fun l l' => if q l = q l' then 1 else 0) *
            ∏ l, (q l).2 ^ k l) ∂Measure.pi fun _ : Fin n =>
          ((poissonCountingMeasure (fun j => (B j ω).1) (fun j l => (B j ω).2 l)).map
            (fun p : ℝ × (ℝ × ℝ) => (p.1 * p.2.1, p.2.2))).restrict (Set.Ioi 0 ×ˢ Set.univ)) /
        ∫ q, ∏ l, (q l).1 ∂Measure.pi fun _ : Fin n =>
          ((poissonCountingMeasure (fun j => (B j ω).1) (fun j l => (B j ω).2 l)).map
            (fun p : ℝ × (ℝ × ℝ) => (p.1 * p.2.1, p.2.2))).restrict (Set.Ioi 0 ×ˢ Set.univ))
      (fun ω =>
        (∫ q, (∏ l, (q l).1) * (f (fun l l' => if q l = q l' then 1 else 0) *
            ∏ l, (q l).2 ^ k l) ∂Measure.pi fun _ : Fin n =>
          (poissonCountingMeasure (fun j => (B' j ω).1) (fun j l => (B' j ω).2 l)).restrict
            (Set.Ioi 0 ×ˢ Set.univ)) /
        ∫ q, ∏ l, (q l).1 ∂Measure.pi fun _ : Fin n =>
          (poissonCountingMeasure (fun j => (B' j ω).1) (fun j l => (B' j ω).2 l)).restrict
            (Set.Ioi 0 ×ˢ Set.univ)) P Q := by
  let R : (Fin n → ℝ × ℝ) → Fin n → Fin n → ℝ := fun q l l' => if q l = q l' then 1 else 0
  have hR : Measurable R := by
    refine measurable_pi_iff.2 fun l => measurable_pi_iff.2 fun l' => ?_
    exact Measurable.ite (measurableSet_eq_fun (measurable_pi_apply l) (measurable_pi_apply l'))
      measurable_const measurable_const
  let G : Fin 2 → (Fin n → ℝ × ℝ) → ℝ := ![fun q => (∏ l, (q l).1) * (f (R q) *
      ∏ l, (q l).2 ^ k l), fun q => ∏ l, (q l).1]
  have hW : Measurable fun q : Fin n → ℝ × ℝ => ∏ l, (q l).1 :=
    Finset.measurable_prod _ fun l _ => measurable_fst.comp (measurable_pi_apply l)
  have hY : Measurable fun q : Fin n → ℝ × ℝ => ∏ l, (q l).2 ^ k l :=
    Finset.measurable_prod _ fun l _ => (measurable_snd.comp (measurable_pi_apply l)).pow_const _
  have hG : ∀ j, Measurable (G j) := by
    intro j
    fin_cases j
    · exact hW.mul ((hf.comp hR).mul hY)
    · exact hW
  let Φ : Fin 2 × Bool → (Fin n → ℝ × ℝ) → ℝ≥0∞ := fun i q =>
    ENNReal.ofReal ((if i.2 then 1 else -1) * G i.1 q)
  have hΦ : ∀ i, Measurable (Φ i) := fun i =>
    ENNReal.measurable_ofReal.comp (measurable_const.mul (hG i.1))
  have hid := identDistrib_lintegral_pi_poissonDirichlet_gaussian hζ t ν r hBm hB hlaw hμ ν' r'
    hBm' hB' hlaw' hμ' n hΦ
  let A : (Fin 2 × Bool → ℝ≥0∞) → ℝ := fun v =>
    signedToReal (v (0, true)) (v (0, false)) / signedToReal (v (1, true)) (v (1, false))
  have hA : Measurable A := by
    refine Measurable.div ?_ ?_
    · have h0 : Measurable fun v : Fin 2 × Bool → ℝ≥0∞ => (v (0, true), v (0, false)) := by
        fun_prop
      exact measurable_signedToReal.comp h0
    · have h1 : Measurable fun v : Fin 2 × Bool → ℝ≥0∞ => (v (1, true), v (1, false)) := by
        fun_prop
      exact measurable_signedToReal.comp h1
  have hint : ∀ (μ : Measure (Fin n → ℝ × ℝ)) (j : Fin 2), ∫ q, G j q ∂μ =
      signedToReal (∫⁻ q, Φ (j, true) q ∂μ) (∫⁻ q, Φ (j, false) q ∂μ) := by
    intro μ j
    rw [integral_eq_signedToReal_lintegral μ (hG j)]
    simp [Φ]
  have hpt : ∀ μ : Measure (Fin n → ℝ × ℝ),
      (∫ q, (∏ l, (q l).1) * (f (fun l l' => if q l = q l' then 1 else 0) *
        ∏ l, (q l).2 ^ k l) ∂μ) / ∫ q, ∏ l, (q l).1 ∂μ = A fun i => ∫⁻ q, Φ i q ∂μ := by
    intro μ
    simp only [A]
    rw [← hint μ 0, ← hint μ 1]
    rfl
  convert hid.comp hA using 1 <;> exact funext fun ω => hpt _

end SpinGlasses
