/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletTransform
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian marks for Poisson–Dirichlet invariance

The power-law Poisson-process transformation becomes stationary when Gaussian marks are
exponentially tilted and shifted by the corresponding Cameron–Martin drift.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

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

/-- The ζ-power Gaussian multiplier has expectation one. -/
theorem lintegral_gaussian_multiplier (ζ t : ℝ) :
    ∫⁻ g, ENNReal.ofReal (Real.exp (t * (g - t * ζ / 2))) ^ ζ
      ∂gaussianReal 0 1 = 1 := by
  have hpow : ∀ g : ℝ,
      ENNReal.ofReal (Real.exp (t * (g - t * ζ / 2))) ^ ζ =
        ENNReal.ofReal (Real.exp (-(t * ζ) ^ 2 / 2)) *
          ENNReal.ofReal (Real.exp ((t * ζ) * g)) := by
    intro g
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 1
    ring_nf
  simp_rw [hpow]
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
  have hshift : ∀ g : ℝ, ENNReal.ofReal (Real.exp (t * (g - t * ζ / 2))) ^ ζ =
      ENNReal.ofReal (Real.exp (-(t * ζ) ^ 2 / 2)) *
        ENNReal.ofReal (Real.exp ((t * ζ) * g)) := by
    intro g
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 1
    ring_nf
  rw [← lintegral_indicator (hs.preimage (by fun_prop))]
  rw [lintegral_map
    ((by fun_prop : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 ^ ζ)).indicator
      (hs.preimage (by fun_prop))) hf]
  change (∫⁻ g, ((fun g : ℝ => g - t * ζ) ⁻¹' s).indicator
    (fun g => ENNReal.ofReal (Real.exp (t * (g - t * ζ / 2))) ^ ζ) g
    ∂gaussianReal 0 1) = _
  simp_rw [hshift]
  have hmul : ∀ g : ℝ,
      (s.preimage (fun g => g - t * ζ)).indicator
        (fun g => ENNReal.ofReal (Real.exp (-(t * ζ) ^ 2 / 2)) *
          ENNReal.ofReal (Real.exp ((t * ζ) * g))) g =
      ENNReal.ofReal (Real.exp (-(t * ζ) ^ 2 / 2)) *
        ((s.preimage (fun g => g - t * ζ)).indicator
          (fun g => ENNReal.ofReal (Real.exp ((t * ζ) * g)))) g := by
    intro g
    by_cases hg : g - t * ζ ∈ s <;> simp [Set.indicator, hg]
  simp_rw [hmul]
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
  have heq : (fun p : ℝ × ℝ => (p.1, p.2)) = id := by
    funext ⟨x, y⟩
    rfl
  simp [heq]

end SpinGlasses
