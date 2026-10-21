/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Reparameterizing trigonometric interpolation by a square

The substitution `s = arccos √t` turns the ubiquitous factor
`sin s * cos s` into the constant `-1 / 2` after the chain rule.
-/

@[expose] public section

/-- Compose an angle derivative carrying `sin s * cos s` with
`t ↦ arccos √t`. On the open unit interval, the two square-root factors in
the chain rule cancel, leaving `-D / 2`. -/
theorem HasDerivAt.comp_arccos_sqrt_of_sin_cos {φ : ℝ → ℝ} {D t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1)
    (hφ : HasDerivAt φ
      (Real.sin (Real.arccos (Real.sqrt t)) *
        Real.cos (Real.arccos (Real.sqrt t)) * D)
      (Real.arccos (Real.sqrt t))) :
    HasDerivAt (fun u => φ (Real.arccos (Real.sqrt u))) (-D / 2) t := by
  have hsqrt_lt_one : Real.sqrt t < 1 := (Real.sqrt_lt' one_pos).2 (by simpa using ht1)
  have hsqrt_sq : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht0.le
  have hsqrt_ne_neg_one : Real.sqrt t ≠ -1 := (neg_one_lt_zero.trans_le (Real.sqrt_nonneg t)).ne'
  have hinner : HasDerivAt (fun u => Real.arccos (Real.sqrt u))
      (-(1 / Real.sqrt (1 - (Real.sqrt t) ^ 2)) * (1 / (2 * Real.sqrt t))) t := by
    exact (Real.hasDerivAt_arccos hsqrt_ne_neg_one hsqrt_lt_one.ne).comp t
      (Real.hasDerivAt_sqrt ht0.ne')
  refine hφ.comp t hinner |>.congr_deriv ?_
  rw [Real.cos_arccos (by linarith [Real.sqrt_nonneg t]) hsqrt_lt_one.le, Real.sin_arccos, hsqrt_sq]
  have hpos : 0 < 1 - t := sub_pos.mpr ht1
  have hsqrtprod : Real.sqrt (1 - t) * Real.sqrt t ≠ 0 := mul_ne_zero
    (Real.sqrt_ne_zero'.mpr hpos) (Real.sqrt_ne_zero'.mpr ht0)
  field_simp
