/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Matching the T-basis covariance and Gaussian variance formulas

Talagrand's Section 1.8 quantities `A²`, `B²`, `C²` include the inverse system size.
The Section 1.10 recurrence uses size-independent coefficients before dividing by the
size. These identities identify the two written-out expressions without introducing
another definition of a variance or a model. The scale may be any real number.
-/

@[expose] public section

namespace SpinGlasses

/-- The pair variance in Section 1.8 is the pair recurrence coefficient divided by size. -/
theorem sk_T_pair_variance_eq (β q qhat m : ℝ) :
    (1 - 2 * q + qhat) / (m * (1 - β ^ 2 * (1 - 2 * q + qhat))) =
      ((1 - 2 * q + qhat) / (1 - β ^ 2 * (1 - 2 * q + qhat))) / m := by
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The single variance agrees with the coefficient obtained from the single recurrence.
Only the pair denominator must be nonzero; no nonzero scale or second denominator is needed. -/
theorem sk_T_single_variance_eq (β q qhat m : ℝ)
    (hD : 1 - β ^ 2 * (1 - 2 * q + qhat) ≠ 0) :
    (q - qhat) / (m * (1 - β ^ 2 * (1 - 2 * q + qhat)) *
      (1 - β ^ 2 * (1 - 4 * q + 3 * qhat))) =
      ((q - qhat) * (1 + β ^ 2 * ((1 - 2 * q + qhat) /
        (1 - β ^ 2 * (1 - 2 * q + qhat)))) /
          (1 - β ^ 2 * (1 - 4 * q + 3 * qhat))) / m := by
  have he : 1 + β ^ 2 * ((1 - 2 * q + qhat) /
      (1 - β ^ 2 * (1 - 2 * q + qhat))) =
        (1 - β ^ 2 * (1 - 2 * q + qhat))⁻¹ := by
    generalize ha : 1 - 2 * q + qhat = a at *
    generalize hd : 1 - β ^ 2 * a = d at *
    field_simp
    rw [← hd]
    ring
  rw [he]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The global variance agrees with the recurrence coefficient, with the same size factor. -/
theorem sk_T_global_variance_eq (β q qhat m : ℝ)
    (hD : 1 - β ^ 2 * (1 - 2 * q + qhat) ≠ 0) :
    ((qhat - q ^ 2) / m + β ^ 2 * (qhat - q ^ 2) *
        ((1 - 2 * q + qhat) / (m * (1 - β ^ 2 * (1 - 2 * q + qhat)))) +
      2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qhat) *
        ((q - qhat) / (m * (1 - β ^ 2 * (1 - 2 * q + qhat)) *
          (1 - β ^ 2 * (1 - 4 * q + 3 * qhat))))) /
            (1 - β ^ 2 * (1 - 4 * q + 3 * qhat)) =
      ((qhat - q ^ 2) + β ^ 2 * (qhat - q ^ 2) *
          ((1 - 2 * q + qhat) / (1 - β ^ 2 * (1 - 2 * q + qhat))) +
        2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qhat) *
          ((q - qhat) * (1 + β ^ 2 * ((1 - 2 * q + qhat) /
            (1 - β ^ 2 * (1 - 2 * q + qhat)))) /
              (1 - β ^ 2 * (1 - 4 * q + 3 * qhat)))) /
                (1 - β ^ 2 * (1 - 4 * q + 3 * qhat)) / m := by
  rw [sk_T_pair_variance_eq, sk_T_single_variance_eq β q qhat m hD]
  ring

end SpinGlasses
