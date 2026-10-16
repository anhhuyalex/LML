/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichlet
public import LeanMachineLearning.SpinGlasses.PoissonProcessTransform
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Transformations of the Poisson–Dirichlet intensity

The power-law intensity is homogeneous under positive dilations. This is the analytic input
for the marked Poisson-process transformation in Theorem 2.6.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace SpinGlasses

/-- Multiplying all points of the `ζ`-Poisson intensity by a positive constant multiplies
its mass by the `ζ`-th power of that constant. -/
theorem zetaPoissonMeasure_map_mul {ζ c : ℝ} (hζ : 0 < ζ) (hc : 0 < c) :
    (zetaPoissonMeasure ζ).map (fun u => u * c) =
      ENNReal.ofReal (c ^ ζ) • zetaPoissonMeasure ζ := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  let d : ℝ → ℝ≥0∞ := fun u =>
    if 0 < u then ENNReal.ofReal (ζ * u ^ (-1 - ζ)) else 0
  have hd : Measurable d :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).ite measurableSet_Ioi measurable_const
  have hdi : ∀ u : ℝ, d (u * c⁻¹) * ENNReal.ofReal c⁻¹ =
      ENNReal.ofReal (c ^ ζ) * d u := by
    intro u
    by_cases hu : 0 < u
    · have hui : 0 < u * c⁻¹ := mul_pos hu (inv_pos.mpr hc)
      simp only [d, if_pos hu, if_pos hui]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ ζ * (u * c⁻¹) ^ (-1 - ζ)),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ c ^ ζ)]
      congr 1
      rw [Real.mul_rpow hu.le (inv_pos.mpr hc).le]
      have hp : (c⁻¹) ^ (-1 - ζ) * c⁻¹ = c ^ ζ := by
        calc
          _ = (c⁻¹) ^ (-ζ) := by
            conv_lhs => rhs; rw [← Real.rpow_one (c⁻¹)]
            rw [← Real.rpow_add (inv_pos.mpr hc)]
            congr 1
            ring
          _ = c ^ ζ := by
            rw [Real.inv_rpow hc.le, ← Real.rpow_neg hc.le]
            congr 1
            ring
      calc
        _ = ζ * u ^ (-1 - ζ) * ((c⁻¹) ^ (-1 - ζ) * c⁻¹) := by ring
        _ = _ := by rw [hp]; ring
    · have hui : ¬ 0 < u * c⁻¹ := not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg
        (le_of_not_gt hu) (inv_pos.mpr hc).le)
      simp [d, hu, hui]
  ext A hA
  have hmeas : Measurable fun u : ℝ => u * c := by fun_prop
  rw [Measure.map_apply hmeas hA, Measure.smul_apply, zetaPoissonMeasure,
    withDensity_apply _ (hA.preimage hmeas), withDensity_apply _ hA]
  have heq : ∀ u : ℝ, (A.preimage (fun v => v * c)).indicator d u =
      A.indicator (fun v => d (v * c⁻¹)) (u * c) := by
    intro u
    have hi : u * c * c⁻¹ = u := by field_simp
    by_cases h : u * c ∈ A <;> simp [indicator, h, hi]
  have hmap := Real.map_volume_mul_right hc0
  have hf : Measurable (A.indicator (fun v => d (v * c⁻¹))) :=
    (hd.comp (by fun_prop)).indicator hA
  have hchange : (∫⁻ u, (A.preimage (fun v => v * c)).indicator d u ∂volume) =
      ∫⁻ v, A.indicator (fun w => d (w * c⁻¹)) v
        ∂(Measure.map (fun u : ℝ => u * c) volume) := by
    rw [lintegral_map hf hmeas]
    exact lintegral_congr heq
  rw [← lintegral_indicator (hA.preimage hmeas), ← lintegral_indicator hA]
  change (∫⁻ u, (A.preimage (fun v => v * c)).indicator d u ∂volume) =
    ENNReal.ofReal (c ^ ζ) * ∫⁻ u, A.indicator d u ∂volume
  rw [hchange, hmap, lintegral_smul_measure]
  simp only [abs_inv, abs_of_pos hc]
  change ENNReal.ofReal c⁻¹ * (∫⁻ u, A.indicator (fun v => d (v * c⁻¹)) u ∂volume) = _
  rw [← lintegral_const_mul _ (hd.indicator hA), ← lintegral_const_mul _ hf]
  apply lintegral_congr
  intro u
  by_cases hu : u ∈ A
  · simp only [indicator_of_mem hu]
    rw [mul_comm]
    exact hdi u
  · simp [indicator_of_notMem hu]

/-- The ζ-power size bias of a pair of marks `(X,Y)`, normalized to a probability
measure on the mark space. The normalizing constant is required to be positive and finite. -/
noncomputable def poissonMarkTilt {S : Type*} [MeasurableSpace S] (ζ : ℝ)
    (ν : Measure (ℝ × S)) : Measure S :=
  (ENNReal.ofReal (∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂ν).toReal)⁻¹ •
    ((ν.withDensity fun p => ENNReal.ofReal p.1 ^ ζ).map Prod.snd)

/-- The normalized ζ-power tilt is a probability measure. -/
theorem poissonMarkTilt_isProbability {S : Type*} [MeasurableSpace S]
    {ζ : ℝ} {ν : Measure (ℝ × S)}
    (hpos : 0 < ∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂ν)
    (hfin : ∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂ν < ∞) :
    IsProbabilityMeasure (poissonMarkTilt ζ ν) := by
  constructor
  simp only [poissonMarkTilt]
  rw [Measure.smul_apply, Measure.map_apply (by fun_prop : Measurable (Prod.snd : ℝ × S → S))
    MeasurableSet.univ, Set.preimage_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  have hne : (∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂ν) ≠ ∞ := hfin.ne
  change (ENNReal.ofReal (∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂ν).toReal)⁻¹ *
    (∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂ν) = 1
  rw [ENNReal.ofReal_toReal hne, ENNReal.inv_mul_cancel hpos.ne' hne]

/-- The tilted law evaluates a measurable set by its ζ-weighted mark mass. -/
theorem poissonMarkTilt_apply {S : Type*} [MeasurableSpace S] (ζ : ℝ)
    (ν : Measure (ℝ × S)) {A : Set S} (hA : MeasurableSet A) :
    poissonMarkTilt ζ ν A =
      (ENNReal.ofReal (∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂ν).toReal)⁻¹ *
        ∫⁻ p in Prod.snd ⁻¹' A, ENNReal.ofReal p.1 ^ ζ ∂ν := by
  rw [poissonMarkTilt, Measure.smul_apply, Measure.map_apply (by fun_prop) hA,
    withDensity_apply _ (hA.preimage (by fun_prop))]
  rfl

end SpinGlasses
