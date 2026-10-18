/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletTransform
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Power maps of the `ζ`-Poisson intensity

The map `x ↦ x ^ e` carries the intensity `ζ x ^ (-1 - ζ) dx` on `(0, ∞)` to the intensity
`(ζ / e) y ^ (-1 - ζ / e) dy` (Panchenko, Eq. (2.98)); this is the computation behind Lemma 2.6.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace SpinGlasses

/-- **Power maps of the `ζ`-Poisson intensity.** -/
theorem zetaPoissonMeasure_map_rpow {ζ e : ℝ} (hζ : 0 < ζ) (he : 0 < e) :
    (zetaPoissonMeasure ζ).map (fun x : ℝ => x ^ e) = zetaPoissonMeasure (ζ / e) := by
  have hmeas : Measurable fun x : ℝ => x ^ e := measurable_id.pow_const e
  ext A hA
  rw [Measure.map_apply hmeas hA, zetaPoissonMeasure, zetaPoissonMeasure,
    withDensity_apply _ (hA.preimage hmeas), withDensity_apply _ hA]
  set d1 : ℝ → ℝ≥0∞ := fun x => if 0 < x then ENNReal.ofReal (ζ * x ^ (-1 - ζ)) else 0 with hd1
  set d2 : ℝ → ℝ≥0∞ := fun y =>
    if 0 < y then ENNReal.ofReal (ζ / e * y ^ (-1 - ζ / e)) else 0 with hd2
  have himg : (fun x : ℝ => x ^ e) '' Ioi 0 = Ioi 0 := by
    ext y
    refine ⟨fun ⟨x, hx, hxy⟩ => hxy ▸ Real.rpow_pos_of_pos hx e, fun hy => ⟨y ^ e⁻¹,
      Real.rpow_pos_of_pos hy _, ?_⟩⟩
    change (y ^ e⁻¹) ^ e = y
    rw [← Real.rpow_mul hy.le, inv_mul_cancel₀ he.ne', Real.rpow_one]
  have hinj : InjOn (fun x : ℝ => x ^ e) (Ioi 0) := fun x hx y hy hxy => by
    have := congrArg (fun z => z ^ e⁻¹) hxy
    simpa [← Real.rpow_mul (le_of_lt hx), ← Real.rpow_mul (le_of_lt hy), he.ne'] using this
  have hder : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun x : ℝ => x ^ e) (e * x ^ (e - 1))
      (Ioi 0) x := fun x hx => (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))).hasDerivWithinAt
  have hsupp2 : ∀ y, y ∉ Ioi (0 : ℝ) → d2 y = 0 := fun y hy => by simp [hd2, mem_Ioi.not.1 hy]
  have hsupp1 : ∀ x, x ∉ Ioi (0 : ℝ) → d1 x = 0 := fun x hx => by simp [hd1, mem_Ioi.not.1 hx]
  have hR : ∫⁻ y in A, d2 y = ∫⁻ y in Ioi 0, A.indicator d2 y := by
    rw [← lintegral_indicator hA, ← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ Ioi (0 : ℝ)
    · simp [indicator_of_mem hy]
    · simp [indicator_of_notMem hy, hsupp2 y hy]
  have hL : ∫⁻ x in (fun x : ℝ => x ^ e) ⁻¹' A, d1 x =
      ∫⁻ x in Ioi 0, ((fun x : ℝ => x ^ e) ⁻¹' A).indicator d1 x := by
    rw [← lintegral_indicator (hA.preimage hmeas), ← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · simp [indicator_of_mem hx]
    · simp [indicator_of_notMem hx, hsupp1 x hx]
  have key := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hder hinj
    (A.indicator d2)
  rw [himg] at key
  rw [hR, hL, key]
  refine (setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_).symm
  have hx0 : 0 < x := hx
  by_cases hxA : x ^ e ∈ A
  · have hxA' : x ∈ (fun x : ℝ => x ^ e) ⁻¹' A := hxA
    rw [indicator_of_mem hxA', indicator_of_mem hxA]
    have hxe : 0 < x ^ e := Real.rpow_pos_of_pos hx0 e
    simp only [hd1, hd2, hx0, hxe, ite_true]
    rw [abs_of_pos (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h1 : (x ^ e) ^ (-1 - ζ / e) = x ^ (-e - ζ) := by
      rw [← Real.rpow_mul hx0.le]
      congr 1
      field_simp
    rw [h1]
    calc e * x ^ (e - 1) * (ζ / e * x ^ (-e - ζ)) = ζ * (x ^ (e - 1) * x ^ (-e - ζ)) := by
          field_simp
      _ = ζ * x ^ (-1 - ζ) := by rw [← Real.rpow_add hx0]; congr 2; ring
  · have hxA' : x ∉ (fun x : ℝ => x ^ e) ⁻¹' A := hxA
    rw [indicator_of_notMem hxA', indicator_of_notMem hxA]
    simp

end SpinGlasses
