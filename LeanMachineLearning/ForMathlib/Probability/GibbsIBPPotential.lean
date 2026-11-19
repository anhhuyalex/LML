/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.BoundedTilted

/-!
# Gaussian integration by parts for Gibbs measures with potential energy

This module provides the core Gaussian integration by parts (Stein identity) for
Hamiltonians with potential terms `u(S)`, where `S` depends affinely on a Gaussian
random variable `z ~ 𝒩(0, v)`.

Differentiating `u'(S) e^{u(S)}` produces the characteristic `(u''(S) + (u'(S))²) e^{u(S)}`
combination that appears in:
1. Auxiliary Gaussian spin integration (Talagrand Section 2.2, Term IV);
2. Quenched disorder integration (Talagrand Section 2.2, Term III diagonal);
3. Cavity in $M$ (Talagrand Section 2.3, Lemma 2.3.2 and Exercise 2.3.3).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace MeasureTheory

/-- Pointwise derivative of `z ↦ u'(S₀ + c * z) * exp (u (S₀ + c * z))`. -/
theorem hasDerivAt_deriv_u_mul_exp_affine {u : ℝ → ℝ} {u' u'' : ℝ → ℝ}
    (hu' : ∀ x, HasDerivAt u (u' x) x) (hu'' : ∀ x, HasDerivAt u' (u'' x) x)
    (S₀ c z : ℝ) :
    HasDerivAt (fun t => u' (S₀ + c * t) * Real.exp (u (S₀ + c * t)))
      (c * (u'' (S₀ + c * z) + (u' (S₀ + c * z)) ^ 2) * Real.exp (u (S₀ + c * z))) z := by
  have hS : HasDerivAt (fun t => S₀ + c * t) c z := by
    simpa using (hasDerivAt_id z).const_mul c |>.const_add S₀
  have h1 : HasDerivAt (fun t => u' (S₀ + c * t)) (u'' (S₀ + c * z) * c) z :=
    (hu'' (S₀ + c * z)).comp z hS
  have h2 : HasDerivAt (fun t => Real.exp (u (S₀ + c * t)))
      (Real.exp (u (S₀ + c * z)) * (u' (S₀ + c * z) * c)) z := by
    simpa only [Function.comp_def] using ((hu' (S₀ + c * z)).comp z hS).exp
  have hprod := h1.mul h2
  convert hprod using 1
  ring

/-- **Gaussian integration by parts for a 1D potential (integrable form):**
`𝔼 [g u'(S₀ + c g) e^{u(S₀ + c g)}] = v c 𝔼 [(u''(S₀ + c g) + (u'(S₀ + c g))²) e^{u(S₀ + c g)}]`
for `g ~ 𝒩(0, v)`. -/
theorem integral_id_mul_deriv_u_mul_exp_affine_gaussianReal_of_integrable (v : NNReal)
    {u u' u'' : ℝ → ℝ}
    (hu' : ∀ x, HasDerivAt u (u' x) x) (hu'' : ∀ x, HasDerivAt u' (u'' x) x)
    (S₀ c : ℝ)
    (hxF : Integrable (fun z => z * (u' (S₀ + c * z) * Real.exp (u (S₀ + c * z))))
      (gaussianReal 0 v))
    (hiF' : Integrable (fun z => (u'' (S₀ + c * z) + (u' (S₀ + c * z)) ^ 2) *
      Real.exp (u (S₀ + c * z))) (gaussianReal 0 v)) :
    ∫ z, z * (u' (S₀ + c * z) * Real.exp (u (S₀ + c * z))) ∂gaussianReal 0 v =
      (v : ℝ) * c * ∫ z, (u'' (S₀ + c * z) + (u' (S₀ + c * z)) ^ 2) *
        Real.exp (u (S₀ + c * z)) ∂gaussianReal 0 v := by
  have hd (x : ℝ) : HasDerivAt (fun t => u' t * Real.exp (u t))
      ((u'' x + (u' x) ^ 2) * Real.exp (u x)) x := by
    have h1 : HasDerivAt u' (u'' x) x := hu'' x
    have h2 : HasDerivAt (fun t => Real.exp (u t)) (Real.exp (u x) * u' x) x := (hu' x).exp
    have hp := h1.mul h2
    convert hp using 1
    ring
  exact integral_id_mul_comp_affine_gaussianReal v hd S₀ c hxF hiF'

/-- **Gaussian integration by parts for a 1D potential (bounded form):**
`𝔼 [g u'(S₀ + c g) e^{u(S₀ + c g)}] = v c 𝔼 [(u''(S₀ + c g) + (u'(S₀ + c g))²) e^{u(S₀ + c g)}]`
for `g ~ 𝒩(0, v)`. -/
theorem integral_id_mul_deriv_u_mul_exp_affine_gaussianReal (v : NNReal)
    {u u' u'' : ℝ → ℝ}
    (hu' : ∀ x, HasDerivAt u (u' x) x) (hu'' : ∀ x, HasDerivAt u' (u'' x) x)
    {B D D₂ : ℝ} (hB : ∀ x, u x ≤ B) (hD : ∀ x, |u' x| ≤ D) (hD₂ : ∀ x, |u'' x| ≤ D₂)
    (S₀ c : ℝ) :
    ∫ z, z * (u' (S₀ + c * z) * Real.exp (u (S₀ + c * z))) ∂gaussianReal 0 v =
      (v : ℝ) * c * ∫ z, (u'' (S₀ + c * z) + (u' (S₀ + c * z)) ^ 2) *
        Real.exp (u (S₀ + c * z)) ∂gaussianReal 0 v := by
  have hmF : Continuous (fun t => u' (S₀ + c * t) * Real.exp (u (S₀ + c * t))) := by
    have hF' : ∀ z, HasDerivAt (fun t => u' (S₀ + c * t) * Real.exp (u (S₀ + c * t)))
        (c * (u'' (S₀ + c * z) + (u' (S₀ + c * z)) ^ 2) * Real.exp (u (S₀ + c * z))) z :=
      fun z => hasDerivAt_deriv_u_mul_exp_affine hu' hu'' S₀ c z
    exact continuous_iff_continuousAt.2 fun x => (hF' x).continuousAt
  have hmF' : Measurable (fun t => (u'' (S₀ + c * t) + (u' (S₀ + c * t)) ^ 2) *
      Real.exp (u (S₀ + c * t))) := by
    have hcu : Continuous u := continuous_iff_continuousAt.2 fun x => (hu' x).continuousAt
    have hmu : Measurable u := hcu.measurable
    have hdu : Measurable u' := by
      have heq : u' = deriv u := funext fun x => (hu' x).deriv.symm
      rw [heq]
      exact measurable_deriv u
    have hdu' : Measurable u'' := by
      have heq : u'' = deriv u' := funext fun x => (hu'' x).deriv.symm
      rw [heq]
      exact measurable_deriv u'
    fun_prop
  have hbF (z : ℝ) : |u' (S₀ + c * z) * Real.exp (u (S₀ + c * z))| ≤ |D| * Real.exp B :=
    abs_mul_exp_le ((hD _).trans (le_abs_self _)) (hB _)
  have hbF' (z : ℝ) : |(u'' (S₀ + c * z) + (u' (S₀ + c * z)) ^ 2) *
      Real.exp (u (S₀ + c * z))| ≤ (|D₂| + D ^ 2) * Real.exp B := by
    have hsum : |u'' (S₀ + c * z) + (u' (S₀ + c * z)) ^ 2| ≤ |D₂| + D ^ 2 := by
      refine (abs_add_le _ _).trans (add_le_add ((hD₂ _).trans (le_abs_self _)) ?_)
      rw [sq, abs_mul]
      have hD0 : 0 ≤ D := (abs_nonneg (u' 0)).trans (hD 0)
      calc |u' (S₀ + c * z)| * |u' (S₀ + c * z)|
        _ ≤ D * D := mul_le_mul (hD _) (hD _) (abs_nonneg _) hD0
        _ = D ^ 2 := (sq D).symm
    exact abs_mul_exp_le hsum (hB _)
  have hG1 : Integrable (id : ℝ → ℝ) (gaussianReal 0 v) :=
    integrable_id_gaussianReal
  have hxF : Integrable (fun z => z * (u' (S₀ + c * z) * Real.exp (u (S₀ + c * z))))
      (gaussianReal 0 v) := by
    have heq : (fun z => z * (u' (S₀ + c * z) * Real.exp (u (S₀ + c * z)))) =
        (fun z => (u' (S₀ + c * z) * Real.exp (u (S₀ + c * z))) * z) := by ext z; ring
    rw [heq]
    exact hG1.bdd_mul hmF.measurable.aestronglyMeasurable (ae_of_all _ hbF)
  have hiF' : Integrable (fun z => (u'' (S₀ + c * z) + (u' (S₀ + c * z)) ^ 2) *
      Real.exp (u (S₀ + c * z))) (gaussianReal 0 v) :=
    integrable_of_measurable_bound hmF' (M := (|D₂| + D ^ 2) * Real.exp B)
      (fun z => hbF' z)
  exact integral_id_mul_deriv_u_mul_exp_affine_gaussianReal_of_integrable
    v hu' hu'' S₀ c hxF hiF'

end MeasureTheory
