/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import LeanMachineLearning.SpinGlasses.PoissonProcessEquivalence

/-!
# The Poisson–Dirichlet intensity

The intensity of the Poisson point process used to construct `PD(ζ)` is
`ζ x ^ (-1 - ζ) dx` on the positive half-line. The counting measure itself is represented by
the existing `SpinGlasses.poissonCountingMeasure`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace SpinGlasses

/-- The intensity `ζ x ^ (-1 - ζ) dx` on the positive half-line. -/
noncomputable def zetaPoissonMeasure (ζ : ℝ) : Measure ℝ :=
  volume.withDensity fun x =>
    if 0 < x then ENNReal.ofReal (ζ * x ^ (-1 - ζ)) else 0

instance nullSingletonClass_zetaPoissonMeasure (ζ : ℝ) :
    NullSingletonClass (zetaPoissonMeasure ζ) := by
  unfold zetaPoissonMeasure
  infer_instance

instance sigmaFinite_zetaPoissonMeasure (ζ : ℝ) :
    SigmaFinite (zetaPoissonMeasure ζ) := by
  unfold zetaPoissonMeasure
  exact SigmaFinite.withDensity_of_ne_top' (fun x => by
    split_ifs <;> simp)

/-- The power-law density has unit mass above one. -/
theorem integral_Ioi_zeta_rpow {ζ : ℝ} (hζ : 0 < ζ) :
    ∫ x in Ioi (1 : ℝ), ζ * x ^ (-1 - ζ) = 1 := by
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : -1 - ζ < -1)
    (by norm_num : (0 : ℝ) < 1)]
  have hn : -1 - ζ + 1 = -ζ := by ring
  rw [hn, Real.one_rpow]
  have hne : ζ ≠ 0 := ne_of_gt hζ
  field_simp

/-- The first moment of points below one, evaluated at the intensity measure. -/
theorem integral_Ioo_zeta_rpow {ζ : ℝ} (hζ1 : ζ < 1) :
    ∫ x in Ioo (0 : ℝ) 1, ζ * x ^ (-ζ) = ζ / (1 - ζ) := by
  rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [integral_rpow (Or.inl (by linarith : -1 < -ζ))]
  simp only [Real.one_rpow, Real.zero_rpow (by linarith : -ζ + 1 ≠ 0)]
  ring

/-- The mass of the intensity above one is exactly one. -/
theorem zetaPoissonMeasure_Ioi_one {ζ : ℝ} (hζ : 0 < ζ) :
    zetaPoissonMeasure ζ (Ioi 1) = 1 := by
  rw [zetaPoissonMeasure, withDensity_apply _ measurableSet_Ioi]
  have heq : (∫⁻ x in Ioi (1 : ℝ),
      if 0 < x then ENNReal.ofReal (ζ * x ^ (-1 - ζ)) else 0) =
      ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (ζ * x ^ (-1 - ζ)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp [lt_trans zero_lt_one (mem_Ioi.mp hx)]
  rw [heq]
  have hf : IntegrableOn (fun x : ℝ => ζ * x ^ (-1 - ζ)) (Ioi 1) := by
    exact (integrableOn_Ioi_rpow_of_lt (by linarith : -1 - ζ < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul ζ
  rw [← ofReal_integral_eq_lintegral_ofReal hf]
  · rw [integral_Ioi_zeta_rpow hζ, ENNReal.ofReal_one]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg hζ.le
      (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one (mem_Ioi.mp hx))) _)

/-- Expected small-point mass from Campbell's identity. The result assumes only Campbell's
formula, so it applies to any construction of the Poisson counting measure. -/
theorem expected_poisson_sum_lt_one {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    {M : Ω → Measure ℝ}
    (hCamp : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ ω, ∫⁻ x, f x ∂(M ω) ∂P = ∫⁻ x, f x ∂(zetaPoissonMeasure ζ)) :
    ∫⁻ ω, ∫⁻ x in Ioo 0 1, ENNReal.ofReal x ∂(M ω) ∂P =
      ENNReal.ofReal (ζ / (1 - ζ)) := by
  let f : ℝ → ℝ≥0∞ := (Ioo (0 : ℝ) 1).indicator ENNReal.ofReal
  have hf : Measurable f := (ENNReal.measurable_ofReal).indicator measurableSet_Ioo
  have hc := hCamp f hf
  have hleft : ∀ ω, (∫⁻ x, f x ∂(M ω)) =
      ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal x ∂(M ω) := by
    intro ω
    exact lintegral_indicator measurableSet_Ioo _
  simp_rw [hleft] at hc
  calc
    _ = ∫⁻ x, f x ∂(zetaPoissonMeasure ζ) := hc
    _ = ENNReal.ofReal (ζ / (1 - ζ)) := by
      rw [zetaPoissonMeasure]
      have hd : Measurable (fun x : ℝ =>
          if 0 < x then ENNReal.ofReal (ζ * x ^ (-1 - ζ)) else 0) := by
        have hm : Measurable (fun x : ℝ => ζ * x ^ (-1 - ζ)) := by fun_prop
        exact (ENNReal.measurable_ofReal.comp hm).ite measurableSet_Ioi measurable_const
      rw [lintegral_withDensity_eq_lintegral_mul volume hd hf]
      · have heq : ∀ x : ℝ,
            (if 0 < x then ENNReal.ofReal (ζ * x ^ (-1 - ζ)) else 0) * f x =
              (Ioo (0 : ℝ) 1).indicator
                (fun x => ENNReal.ofReal (ζ * x ^ (-ζ))) x := by
          intro x
          by_cases hx : x ∈ Ioo (0 : ℝ) 1
          · have hp : 0 < x := hx.1
            simp only [f, Set.indicator_of_mem hx]
            simp only [hp, ↓reduceIte]
            rw [← ENNReal.ofReal_mul (mul_nonneg hζ0.le (Real.rpow_nonneg hp.le _))]
            congr 1
            have he : x ^ (-1 - ζ) * x = x ^ (-ζ) := by
              conv_lhs => rhs; rw [← Real.rpow_one x]
              rw [← Real.rpow_add hp]
              congr 1; ring
            rw [mul_assoc, he]
          · simp only [f, Set.indicator, hx, ↓reduceIte, mul_zero]
        change (∫⁻ x : ℝ,
          (if 0 < x then ENNReal.ofReal (ζ * x ^ (-1 - ζ)) else 0) * f x) = _
        simp_rw [heq]
        rw [lintegral_indicator measurableSet_Ioo]
        have hi : IntegrableOn (fun x : ℝ => ζ * x ^ (-ζ)) (Ioo 0 1) := by
          exact (intervalIntegral.integrableOn_Ioo_rpow_iff
            (by norm_num : (0 : ℝ) < 1)).2
            (by linarith : -1 < -ζ) |>.const_mul ζ
        rw [← ofReal_integral_eq_lintegral_ofReal hi]
        · exact congrArg ENNReal.ofReal (integral_Ioo_zeta_rpow hζ1)
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
          exact mul_nonneg hζ0.le (Real.rpow_nonneg hx.1.le _)
/-- Finite expected mass below one implies finite small-point mass almost surely. -/
theorem ae_poisson_sum_lt_one_finite {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    {M : Ω → Measure ℝ} (hM : Measurable M)
    (hCamp : ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ ω, ∫⁻ x, f x ∂(M ω) ∂P = ∫⁻ x, f x ∂(zetaPoissonMeasure ζ)) :
    ∀ᵐ ω ∂P, (∫⁻ x in Ioo 0 1, ENNReal.ofReal x ∂(M ω)) < ∞ := by
  have hf : Measurable (fun ω => ∫⁻ x in Ioo (0 : ℝ) 1,
      ENNReal.ofReal x ∂(M ω)) := by
    convert (Measure.measurable_lintegral
      ((ENNReal.measurable_ofReal).indicator
        (measurableSet_Ioo (a := (0 : ℝ)) (b := 1)))).comp hM using 1
    ext ω
    exact (lintegral_indicator
      (measurableSet_Ioo (a := (0 : ℝ)) (b := 1)) _).symm
  apply ae_lt_top hf
  rw [expected_poisson_sum_lt_one hζ0 hζ1 hCamp]
  exact ENNReal.ofReal_ne_top

end SpinGlasses
