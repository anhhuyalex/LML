/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.Hyperbolic

/-!
# Continuity and derivatives of `Real.tanh`

This file provides continuity and derivative identities for `Real.tanh` and `Real.tanh ^ 2`,
together with second derivative bounds for the fixed-point analysis of the Sherrington-Kirkpatrick
model (Talagrand Section 1.7).
-/

@[expose] public section

namespace Real

/-- `Real.tanh` is continuous. -/
@[fun_prop]
theorem continuous_tanh : Continuous Real.tanh := by
  rw [show Real.tanh = fun x => Real.sinh x / Real.cosh x from
    funext Real.tanh_eq_sinh_div_cosh]
  exact Real.continuous_sinh.div Real.continuous_cosh fun x => (Real.cosh_pos x).ne'

/-- The derivative of `Real.tanh` is `1 - tanh² x`. -/
theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  have heq : Real.tanh = Real.sinh / Real.cosh := by
    ext y; exact Real.tanh_eq_sinh_div_cosh y
  rw [heq]
  have h_id : (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2 =
      1 - (Real.sinh x / Real.cosh x) ^ 2 := by
    have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
    have hcs : Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x = 1 := by
      calc Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x
        _ = Real.cosh x ^ 2 - Real.sinh x ^ 2 := by ring
        _ = 1 := Real.cosh_sq_sub_sinh_sq x
    rw [hcs, div_pow]
    field_simp
    rw [(Real.cosh_sq_sub_sinh_sq x).symm]
  rwa [h_id] at h

/-- The derivative of `x ↦ tanh² x` is `2 tanh x (1 - tanh² x)`. -/
theorem hasDerivAt_tanh_sq (x : ℝ) :
    HasDerivAt (fun y => Real.tanh y ^ 2) (2 * Real.tanh x * (1 - Real.tanh x ^ 2)) x := by
  have h : HasDerivAt (fun y => (Real.tanh y) ^ 2)
      (2 * Real.tanh x ^ (2 - 1) * (1 - Real.tanh x ^ 2)) x :=
    (hasDerivAt_tanh x).pow 2
  have h_eq : 2 * Real.tanh x ^ (2 - 1) * (1 - Real.tanh x ^ 2) =
      2 * Real.tanh x * (1 - Real.tanh x ^ 2) := by
    simp only [Nat.reduceSub, pow_one]
  exact h_eq ▸ h

/-- The derivative of `x ↦ 2 tanh x (1 - tanh² x)` is `2 (1 - tanh² x) (1 - 3 tanh² x)`. -/
theorem hasDerivAt_tanh_sq_deriv (x : ℝ) :
    HasDerivAt (fun y => 2 * Real.tanh y * (1 - Real.tanh y ^ 2))
      (2 * (1 - Real.tanh x ^ 2) * (1 - 3 * Real.tanh x ^ 2)) x := by
  have h1 : HasDerivAt (fun y => 2 * Real.tanh y) (2 * (1 - Real.tanh x ^ 2)) x :=
    (hasDerivAt_tanh x).const_mul 2
  have h2 : HasDerivAt (fun y => 1 - Real.tanh y ^ 2)
      (- (2 * Real.tanh x * (1 - Real.tanh x ^ 2))) x := by
    have hsub := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_tanh_sq x)
    rw [zero_sub] at hsub
    exact hsub
  have hprod := h1.mul h2
  have hid : 2 * (1 - Real.tanh x ^ 2) * (1 - Real.tanh x ^ 2) +
      2 * Real.tanh x * (- (2 * Real.tanh x * (1 - Real.tanh x ^ 2))) =
      2 * (1 - Real.tanh x ^ 2) * (1 - 3 * Real.tanh x ^ 2) := by
    ring
  exact hid ▸ hprod

/-- The second derivative of `tanh²` is bounded by 2 in absolute value. -/
theorem abs_tanh_sq_second_deriv_le (x : ℝ) :
    |2 * (1 - Real.tanh x ^ 2) * (1 - 3 * Real.tanh x ^ 2)| ≤ 2 := by
  set u := Real.tanh x ^ 2
  have hu0 : 0 ≤ u := sq_nonneg _
  have hu1 : u < 1 := Real.tanh_sq_lt_one x
  have hu1_le : u ≤ 1 := hu1.le
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- The first derivative of `tanh²` is bounded by 2 in absolute value. -/
theorem abs_deriv_tanh_sq_le (x : ℝ) : |2 * Real.tanh x * (1 - Real.tanh x ^ 2)| ≤ 2 := by
  have ht : |Real.tanh x| ≤ 1 := (Real.abs_tanh_lt_one x).le
  have hu0 : 0 ≤ Real.tanh x ^ 2 := sq_nonneg _
  have hu1 : Real.tanh x ^ 2 ≤ 1 := (Real.tanh_sq_lt_one x).le
  have hpos : 0 ≤ 1 - Real.tanh x ^ 2 := by linarith
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg hpos]
  nlinarith

/-- **`tanh` is 1-Lipschitz:** `|tanh x - tanh y| ≤ |x - y|`. -/
theorem abs_tanh_sub_tanh_le (x y : ℝ) : |Real.tanh x - Real.tanh y| ≤ |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Real.tanh)
    (f' := fun t => 1 - Real.tanh t ^ 2) (s := Set.univ) (C := 1)
    (fun t _ => (hasDerivAt_tanh t).hasDerivWithinAt)
    (fun t _ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [Real.tanh_sq_lt_one t])]
      nlinarith [sq_nonneg (Real.tanh t)])
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs, abs_sub_comm] using h

/-- `|tanh x| ≤ |x|`. -/
theorem abs_tanh_le_abs (x : ℝ) : |Real.tanh x| ≤ |x| := by
  simpa using abs_tanh_sub_tanh_le x 0

/-- `tanh (h + x) + tanh (h - x) = 2 sinh (2 h) / (cosh (2 h) + cosh (2 x))`. -/
theorem tanh_add_tanh_sub (h x : ℝ) :
    Real.tanh (h + x) + Real.tanh (h - x) =
      2 * Real.sinh (2 * h) / (Real.cosh (2 * h) + Real.cosh (2 * x)) := by
  have h1 := Real.cosh_pos (h + x)
  have h2 := Real.cosh_pos (h - x)
  have hsum : Real.sinh (h + x) * Real.cosh (h - x) + Real.cosh (h + x) * Real.sinh (h - x) =
      Real.sinh (2 * h) := by
    rw [← Real.sinh_add]; ring_nf
  have hprod : Real.cosh (h + x) * Real.cosh (h - x) =
      (Real.cosh (2 * h) + Real.cosh (2 * x)) / 2 := by
    rw [Real.cosh_mul_cosh]; ring_nf
  have hc : 0 < Real.cosh (2 * h) + Real.cosh (2 * x) := by
    have := Real.cosh_pos (2 * h); have := Real.cosh_pos (2 * x); linarith
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, div_add_div _ _ h1.ne' h2.ne',
    show Real.sinh (h + x) * Real.cosh (h - x) + Real.cosh (h + x) * Real.sinh (h - x) =
      Real.sinh (2 * h) from hsum, hprod]
  field_simp

end Real
