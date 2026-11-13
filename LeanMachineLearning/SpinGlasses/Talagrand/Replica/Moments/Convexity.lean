/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.CGFConvex
public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.Moments.RealPowers

/-!
# Convexity of the real-moment pressure of the SK model (Talagrand, Section 1.13)

At fixed finite size `N`, the map `t ↦ N⁻¹ log 𝔼 Z_N^t` is convex on all of `ℝ`: it is the
cumulant-generating function of `log Z_N`, which has exponential moments of every order
(`integrable_exp_mul_log_skPartition`).  This is the convexity used in the book to pass from
convergence of the functions `N⁻¹ log 𝔼 Z_N^t` to convergence of their derivatives at `t = 0`
(see `tendsto_deriv_of_convexOn_tendsto`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

/-- **Convexity of the real-moment pressure at fixed `N`:** `t ↦ log 𝔼 Z_N^t` is convex on `ℝ`. -/
theorem convexOn_log_integral_rpow_skPartition (N : ℕ) (β h : ℝ) :
    ConvexOn ℝ Set.univ (fun t : ℝ => Real.log (∫ g : FinPairs N → ℝ,
      (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ t
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))) := by
  have hZ : ∀ᵐ g ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1),
      0 < ∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ) :=
    Filter.Eventually.of_forall (skPartition_pos N β h)
  have hm : AEMeasurable (fun g : FinPairs N → ℝ => ∑ σ : Fin N → ℤˣ,
      Real.exp (skGibbsEnergy N β h g σ)) (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) :=
    (Finset.measurable_sum _ fun σ _ => (measurable_skGibbsEnergy N β h σ).exp).aemeasurable
  have huniv : integrableExpSet (fun g : FinPairs N → ℝ => Real.log (∑ σ : Fin N → ℤˣ,
      Real.exp (skGibbsEnergy N β h g σ))) (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) =
      Set.univ :=
    Set.eq_univ_of_forall fun t => integrable_exp_mul_log_skPartition N β h t
  simpa only [huniv] using convexOn_log_integral_rpow hZ hm

/-- The rescaled real-moment pressure `t ↦ N⁻¹ log 𝔼 Z_N^t` is convex on `ℝ`. -/
theorem convexOn_inv_mul_log_integral_rpow_skPartition (N : ℕ) (β h : ℝ) :
    ConvexOn ℝ Set.univ (fun t : ℝ => (N : ℝ)⁻¹ * Real.log (∫ g : FinPairs N → ℝ,
      (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ t
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))) :=
  (convexOn_log_integral_rpow_skPartition N β h).smul (inv_nonneg.2 (Nat.cast_nonneg N))

end SpinGlasses
