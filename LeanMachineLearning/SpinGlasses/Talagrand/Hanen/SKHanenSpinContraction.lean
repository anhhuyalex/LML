/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenVanishing
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.CoordinatePair

/-!
# Exact spin contractions for surviving Hanen terms

A spin-difference pair with one selected endpoint contracts to a signed inverse cosh square.
The remaining observable may be arbitrary provided it is invariant under updates at that pair.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real
namespace SpinGlasses

/-- The mean of a single spin with energy `s*Y` is `tanh Y`. -/
theorem integral_count_tilted_spin_eq_tanh (Y : ℝ) :
    (∫ s : ℤˣ, (s : ℝ) ∂Measure.count.tilted (fun s : ℤˣ => (s : ℝ) * Y)) =
      Real.tanh Y := by
  rw [integral_count_tilted, sum_units_int, sum_units_int]
  simp only [Units.val_one, Units.val_neg, Int.cast_neg, Int.cast_one, one_mul, neg_one_mul,
    mul_one, mul_neg_one]
  rw [Real.tanh_eq]
  ring

/-- A spin difference times its first endpoint contracts to the spin variance. -/
theorem integral_spin_diff_mul_left_of_invariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : ℝ) (x y : ι) (hxy : x ≠ y) (G : (ι → ℤˣ) → ℝ)
    (hx : ∀ ε t, G (Function.update ε x t) = G ε)
    (hy : ∀ ε t, G (Function.update ε y t) = G ε) :
    (∫ ε : ι → ℤˣ, ((ε x : ℝ) - (ε y : ℝ)) * (ε x : ℝ) * G ε
      ∂(Measure.pi fun _ : ι => Measure.count.tilted fun s : ℤˣ => (s : ℝ) * Y)) =
      ((Real.cosh Y)⁻¹) ^ 2 *
        ∫ ε : ι → ℤˣ, G ε
          ∂(Measure.pi fun _ : ι => Measure.count.tilted fun s : ℤˣ => (s : ℝ) * Y) := by
  rw [integral_pi_mul_pair_of_invariant _ x y hxy
    (fun a b : ℤˣ => ((a : ℝ) - (b : ℝ)) * (a : ℝ)) G hx hy]
  congr 1
  have hin (a : ℤˣ) :
      (∫ b : ℤˣ, ((a : ℝ) - (b : ℝ)) * (a : ℝ)
        ∂Measure.count.tilted (fun s : ℤˣ => (s : ℝ) * Y)) =
      1 - Real.tanh Y * (a : ℝ) := by
    simp_rw [sub_mul, ← pow_two, units_cast_sq, integral_sub Integrable.of_finite Integrable.of_finite,
      integral_const, probReal_univ, one_smul, integral_mul_const,
      integral_count_tilted_spin_eq_tanh]
  simp_rw [hin]
  rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_const,
    probReal_univ, one_smul, integral_const_mul, integral_count_tilted_spin_eq_tanh,
    ← pow_two, Real.one_sub_tanh_sq_eq_inv_cosh_sq]

/-- Selecting the second endpoint reverses the sign of the contraction. -/
theorem integral_spin_diff_mul_selected_of_invariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : ℝ) (x y : ι) (hxy : x ≠ y) (b : Bool) (G : (ι → ℤˣ) → ℝ)
    (hx : ∀ ε t, G (Function.update ε x t) = G ε)
    (hy : ∀ ε t, G (Function.update ε y t) = G ε) :
    (∫ ε : ι → ℤˣ, ((ε x : ℝ) - (ε y : ℝ)) *
        (ε (if b then x else y) : ℝ) * G ε
      ∂(Measure.pi fun _ : ι => Measure.count.tilted fun s : ℤˣ => (s : ℝ) * Y)) =
      (if b then (1 : ℝ) else -1) * ((Real.cosh Y)⁻¹) ^ 2 *
        ∫ ε : ι → ℤˣ, G ε
          ∂(Measure.pi fun _ : ι => Measure.count.tilted fun s : ℤˣ => (s : ℝ) * Y) := by
  cases b with
  | true => simpa using integral_spin_diff_mul_left_of_invariant Y x y hxy G hx hy
  | false =>
    simp only [Bool.false_eq_true, ite_false, neg_one_mul]
    have he (ε : ι → ℤˣ) : ((ε x : ℝ) - (ε y : ℝ)) * (ε y : ℝ) * G ε =
        -(((ε y : ℝ) - (ε x : ℝ)) * (ε y : ℝ) * G ε) := by ring
    simp_rw [he, integral_neg]
    rw [integral_spin_diff_mul_left_of_invariant Y y x hxy.symm G hy hx]
    ring

end SpinGlasses
