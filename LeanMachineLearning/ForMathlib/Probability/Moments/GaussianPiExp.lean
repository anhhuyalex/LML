/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Exponential and hyperbolic moments of linear forms in independent standard Gaussians

For independent standard Gaussians `g : E → ℝ` (law `Measure.pi fun _ => gaussianReal 0 1`) and
coefficients `c : E → ℝ`, `m : ℝ`:

* `integral_exp_sum_mul_gaussianReal`: `𝔼 exp (∑ cₑ gₑ) = exp (∑ cₑ² / 2)`;
* `integral_cosh_sum_mul_gaussianReal`: `𝔼 cosh (∑ cₑ gₑ + m) = cosh m * exp (∑ cₑ² / 2)`.

Both come with their integrability statements.  The one-dimensional case is
`integral_exp_mul_gaussianReal_zero_one`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Moment generating function of a standard Gaussian `𝒩(0, 1)`. -/
theorem integral_exp_mul_gaussianReal_zero_one (t : ℝ) :
    ∫ x, Real.exp (t * x) ∂(gaussianReal 0 1) = Real.exp (t ^ 2 / 2) := by
  have h := congr_fun (ProbabilityTheory.mgf_fun_id_gaussianReal (μ := 0) (v := 1)) t
  dsimp [ProbabilityTheory.mgf] at h
  rw [h]
  ring_nf

/-- Integrability of the exponential of a linear combination of independent standard Gaussians. -/
theorem integrable_exp_sum_mul_gaussianReal {E : Type*} [Fintype E] (c : E → ℝ) :
    Integrable (fun g : E → ℝ => Real.exp (∑ e, c e * g e))
      (Measure.pi fun _ : E => gaussianReal 0 1) := by
  have e : (fun g : E → ℝ => Real.exp (∑ e, c e * g e)) =
      fun g => ∏ e, Real.exp (c e * g e) := by
    ext g
    rw [Real.exp_sum]
  rw [e]
  exact MeasureTheory.Integrable.fintype_prod (fun e => integrable_exp_mul_gaussianReal (c e))

/-- Integral of the exponential of a linear combination of independent standard Gaussians. -/
theorem integral_exp_sum_mul_gaussianReal {E : Type*} [Fintype E] (c : E → ℝ) :
    ∫ g : E → ℝ, Real.exp (∑ e, c e * g e)
      ∂(Measure.pi fun _ : E => gaussianReal 0 1) =
    Real.exp (∑ e, c e ^ 2 / 2) := by
  simp_rw [Real.exp_sum]
  have h_int := MeasureTheory.integral_fintype_prod_eq_prod
    (E := fun _ : E => ℝ) (μ := fun _ : E => gaussianReal 0 1)
    (fun e (x : ℝ) => Real.exp (c e * x))
  rw [h_int]
  have h (e : E) : ∫ x, Real.exp (c e * x) ∂(gaussianReal 0 1) = Real.exp (c e ^ 2 / 2) :=
    integral_exp_mul_gaussianReal_zero_one (c e)
  rw [Finset.prod_congr rfl fun e _ => h e, ← Real.exp_sum]

/-- `cosh` of an affine form is the average of the exponentials of `±` the form. -/
theorem cosh_sum_mul_add_eq {E : Type*} [Fintype E] (c : E → ℝ) (m : ℝ) (g : E → ℝ) :
    Real.cosh (∑ e, c e * g e + m) =
      (Real.exp m * Real.exp (∑ e, c e * g e) +
        Real.exp (-m) * Real.exp (∑ e, (-c) e * g e)) / 2 := by
  have hneg : ∑ e, (-c) e * g e = -∑ e, c e * g e := by
    simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  rw [Real.cosh_eq, hneg, neg_add, Real.exp_add, Real.exp_add]
  ring

/-- Integrability of the hyperbolic cosine of an affine combination of independent Gaussians. -/
theorem integrable_cosh_sum_mul_gaussianReal {E : Type*} [Fintype E] (c : E → ℝ) (m : ℝ) :
    Integrable (fun g : E → ℝ => Real.cosh (∑ e, c e * g e + m))
      (Measure.pi fun _ : E => gaussianReal 0 1) := by
  simp_rw [cosh_sum_mul_add_eq]
  exact (((integrable_exp_sum_mul_gaussianReal c).const_mul _).add
    ((integrable_exp_sum_mul_gaussianReal (-c)).const_mul _)).div_const 2

/-- Integral of the hyperbolic cosine of an affine combination of independent Gaussians. -/
theorem integral_cosh_sum_mul_gaussianReal {E : Type*} [Fintype E] (c : E → ℝ) (m : ℝ) :
    ∫ g : E → ℝ, Real.cosh (∑ e, c e * g e + m)
      ∂(Measure.pi fun _ : E => gaussianReal 0 1) =
    Real.cosh m * Real.exp (∑ e, c e ^ 2 / 2) := by
  simp_rw [cosh_sum_mul_add_eq]
  rw [integral_div, integral_add ((integrable_exp_sum_mul_gaussianReal c).const_mul _)
    ((integrable_exp_sum_mul_gaussianReal (-c)).const_mul _), integral_const_mul,
    integral_const_mul, integral_exp_sum_mul_gaussianReal c,
    integral_exp_sum_mul_gaussianReal (-c)]
  have hsq : (∑ e, (-c) e ^ 2 / 2) = ∑ e, c e ^ 2 / 2 := by
    simp only [Pi.neg_apply, neg_sq]
  rw [hsq, Real.cosh_eq]
  ring
