/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.Hyperbolic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Exponential and hyperbolic moments of linear forms in independent standard Gaussians

For independent standard Gaussians `g : E → ℝ` (law `Measure.pi fun _ => gaussianReal 0 1`) and
coefficients `c : E → ℝ`, `m : ℝ`:

* `integral_exp_sum_mul_gaussianReal`: `𝔼 exp (∑ cₑ gₑ) = exp (∑ cₑ² / 2)`;
* `integral_cosh_sum_mul_gaussianReal`: `𝔼 cosh (∑ cₑ gₑ + m) = cosh m * exp (∑ cₑ² / 2)`.
* `integral_cosh_two_sum_mul_gaussianReal`: the corresponding formula for two independent
  finite Gaussian blocks;
* `integral_cosh_sum_mul_add_mul_gaussianReal`: the product-space formula for a finite block
  and one independent scalar Gaussian.

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

/-- Integrability of a product of exponential linear forms in two independent finite Gaussian
blocks. -/
theorem integrable_exp_prod_mul_gaussianReal {K L : Type*} [Fintype K] [Fintype L]
    (c : K → ℝ) (d : L → ℝ) :
    Integrable (fun ω : (K → ℝ) × (L → ℝ) =>
      Real.exp (∑ i, c i * ω.1 i) * Real.exp (∑ j, d j * ω.2 j))
      ((Measure.pi fun _ : K => gaussianReal 0 1).prod
        (Measure.pi fun _ : L => gaussianReal 0 1)) :=
  (integrable_exp_sum_mul_gaussianReal c).mul_prod
    (integrable_exp_sum_mul_gaussianReal d)

/-- Integrability of a product of an exponential linear form in a finite Gaussian block and an
exponential multiple of an independent scalar Gaussian. -/
theorem integrable_exp_mul_prod_gaussianReal {K : Type*} [Fintype K]
    (c : K → ℝ) (d : ℝ) :
    Integrable (fun ω : (K → ℝ) × ℝ =>
      Real.exp (∑ i, c i * ω.1 i) * Real.exp (d * ω.2))
      ((Measure.pi fun _ : K => gaussianReal 0 1).prod (gaussianReal 0 1)) :=
  (integrable_exp_sum_mul_gaussianReal c).mul_prod
    (integrable_exp_mul_gaussianReal d)

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


/-- `cosh` of affine forms in two independent finite Gaussian blocks is the average of the
corresponding positive and negative exponential products. -/
theorem cosh_two_sum_mul_add_eq {K L : Type*} [Fintype K] [Fintype L]
    (c : K → ℝ) (d : L → ℝ) (m : ℝ) (ω : (K → ℝ) × (L → ℝ)) :
    Real.cosh (∑ i, c i * ω.1 i + ∑ j, d j * ω.2 j + m) =
      (Real.exp m *
            (Real.exp (∑ i, c i * ω.1 i) * Real.exp (∑ j, d j * ω.2 j)) +
          Real.exp (-m) *
            (Real.exp (∑ i, (-c) i * ω.1 i) *
              Real.exp (∑ j, (-d) j * ω.2 j))) /
        2 := by
  simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] using
    Real.cosh_add_add_eq (∑ i, c i * ω.1 i) (∑ j, d j * ω.2 j) m

/-- Integrability of `cosh` of an affine combination of two independent finite Gaussian
blocks. -/
theorem integrable_cosh_two_sum_mul_gaussianReal {K L : Type*} [Fintype K] [Fintype L]
    (c : K → ℝ) (d : L → ℝ) (m : ℝ) :
    Integrable (fun ω : (K → ℝ) × (L → ℝ) =>
      Real.cosh (∑ i, c i * ω.1 i + ∑ j, d j * ω.2 j + m))
      ((Measure.pi fun _ : K => gaussianReal 0 1).prod
        (Measure.pi fun _ : L => gaussianReal 0 1)) := by
  simp_rw [cosh_two_sum_mul_add_eq c d m]
  have h1 := integrable_exp_prod_mul_gaussianReal c d
  have h2 := integrable_exp_prod_mul_gaussianReal (-c) (-d)
  exact ((h1.const_mul _).add (h2.const_mul _)).div_const 2

/-- Integral of `cosh` of an affine combination of two independent finite Gaussian blocks. -/
theorem integral_cosh_two_sum_mul_gaussianReal {K L : Type*} [Fintype K] [Fintype L]
    (c : K → ℝ) (d : L → ℝ) (m : ℝ) :
    ∫ ω : (K → ℝ) × (L → ℝ),
      Real.cosh (∑ i, c i * ω.1 i + ∑ j, d j * ω.2 j + m)
      ∂((Measure.pi fun _ : K => gaussianReal 0 1).prod
        (Measure.pi fun _ : L => gaussianReal 0 1)) =
    Real.cosh m * Real.exp ((∑ i, c i ^ 2 + ∑ j, d j ^ 2) / 2) := by
  simp_rw [cosh_two_sum_mul_add_eq c d m]
  have h1 := integrable_exp_prod_mul_gaussianReal c d
  have h2 := integrable_exp_prod_mul_gaussianReal (-c) (-d)
  rw [integral_div, integral_add (h1.const_mul _) (h2.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_prod_mul (fun g : K → ℝ => Real.exp (∑ i, c i * g i))
      (fun z : L → ℝ => Real.exp (∑ j, d j * z j)),
    integral_prod_mul (fun g : K → ℝ => Real.exp (∑ i, (-c) i * g i))
      (fun z : L → ℝ => Real.exp (∑ j, (-d) j * z j)),
    integral_exp_sum_mul_gaussianReal c, integral_exp_sum_mul_gaussianReal d,
    integral_exp_sum_mul_gaussianReal (-c), integral_exp_sum_mul_gaussianReal (-d)]
  have hc : ∑ i, (-c) i ^ 2 / 2 = ∑ i, c i ^ 2 / 2 := by
    simp only [Pi.neg_apply, neg_sq]
  have hd : ∑ j, (-d) j ^ 2 / 2 = ∑ j, d j ^ 2 / 2 := by
    simp only [Pi.neg_apply, neg_sq]
  rw [hc, hd]
  have hsum : ∑ i, c i ^ 2 / 2 + ∑ j, d j ^ 2 / 2 =
      (∑ i, c i ^ 2 + ∑ j, d j ^ 2) / 2 := by
    rw [← Finset.sum_div, ← Finset.sum_div, ← add_div]
  have hv : Real.exp (∑ i, c i ^ 2 / 2) * Real.exp (∑ j, d j ^ 2 / 2) =
      Real.exp ((∑ i, c i ^ 2 + ∑ j, d j ^ 2) / 2) := by
    rw [← Real.exp_add, hsum]
  rw [hv, Real.cosh_eq]
  ring


/-- `cosh` of an affine form in a finite Gaussian block and one scalar Gaussian is the average
of the corresponding positive and negative exponential products. -/
theorem cosh_sum_mul_add_mul_eq {K : Type*} [Fintype K] (c : K → ℝ) (d m : ℝ)
    (ω : (K → ℝ) × ℝ) :
    Real.cosh (∑ i, c i * ω.1 i + d * ω.2 + m) =
      (Real.exp m * (Real.exp (∑ i, c i * ω.1 i) * Real.exp (d * ω.2)) +
        Real.exp (-m) *
          (Real.exp (∑ i, (-c) i * ω.1 i) * Real.exp (-d * ω.2))) / 2 := by
  simpa only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] using
    Real.cosh_add_add_eq (∑ i, c i * ω.1 i) (d * ω.2) m

/-- Integrability of `cosh` of an affine combination of a finite Gaussian block and one
independent scalar Gaussian. -/
theorem integrable_cosh_sum_mul_add_mul_gaussianReal {K : Type*} [Fintype K]
    (c : K → ℝ) (d m : ℝ) :
    Integrable (fun ω : (K → ℝ) × ℝ =>
      Real.cosh (∑ i, c i * ω.1 i + d * ω.2 + m))
      ((Measure.pi fun _ : K => gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  simp_rw [cosh_sum_mul_add_mul_eq c d m]
  have h1 := integrable_exp_mul_prod_gaussianReal c d
  have h2 := integrable_exp_mul_prod_gaussianReal (-c) (-d)
  exact ((h1.const_mul _).add (h2.const_mul _)).div_const 2

/-- Integral of `cosh` of an affine combination of a finite Gaussian block and one independent
scalar Gaussian. -/
theorem integral_cosh_sum_mul_add_mul_gaussianReal {K : Type*} [Fintype K]
    (c : K → ℝ) (d m : ℝ) :
    ∫ ω : (K → ℝ) × ℝ, Real.cosh (∑ i, c i * ω.1 i + d * ω.2 + m)
      ∂((Measure.pi fun _ : K => gaussianReal 0 1).prod (gaussianReal 0 1)) =
    Real.cosh m * Real.exp ((∑ i, c i ^ 2 + d ^ 2) / 2) := by
  simp_rw [cosh_sum_mul_add_mul_eq c d m]
  have h1 := integrable_exp_mul_prod_gaussianReal c d
  have h2 := integrable_exp_mul_prod_gaussianReal (-c) (-d)
  rw [integral_div, integral_add (h1.const_mul _) (h2.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_prod_mul (fun g : K → ℝ => Real.exp (∑ i, c i * g i))
      (fun z : ℝ => Real.exp (d * z)),
    integral_prod_mul (fun g : K → ℝ => Real.exp (∑ i, (-c) i * g i))
      (fun z : ℝ => Real.exp (-d * z)),
    integral_exp_sum_mul_gaussianReal c, integral_exp_sum_mul_gaussianReal (-c),
    integral_exp_mul_gaussianReal_zero_one d,
    integral_exp_mul_gaussianReal_zero_one (-d)]
  have hc : ∑ i, (-c) i ^ 2 / 2 = ∑ i, c i ^ 2 / 2 := by
    simp only [Pi.neg_apply, neg_sq]
  have hd : (-d) ^ 2 / 2 = d ^ 2 / 2 := by ring
  rw [hc, hd]
  have hsum : ∑ i, c i ^ 2 / 2 + d ^ 2 / 2 =
      (∑ i, c i ^ 2 + d ^ 2) / 2 := by
    rw [← Finset.sum_div, ← add_div]
  have hv : Real.exp (∑ i, c i ^ 2 / 2) * Real.exp (d ^ 2 / 2) =
      Real.exp ((∑ i, c i ^ 2 + d ^ 2) / 2) := by
    rw [← Real.exp_add, hsum]
  rw [hv, Real.cosh_eq]
  ring
