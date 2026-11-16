/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ProductTiltedMarginal
public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Units
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Integrating the auxiliary Gaussian spins of the perceptron smart path

Talagrand, Section 2.2, Exercise 2.2.1 and (2.20). The full system has `N + 1` spins;
the spin coordinates are the first `N` spins and the last spin separately. The auxiliary
Gaussian coordinates are part of the configuration, independently for each replica, while
the old disorder `g`, last disorder `a` and field `y` are held fixed.

Integrating the auxiliary coordinates replaces each potential by its log exponential integral.
Only measurability and an upper bound on the potential are needed; the three-derivative
assumptions of the chapter are unnecessary for this identity. It also allows no constraints,
one full spin and an empty replica type. No model or effective-potential definition is added.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SpinGlasses

/-- **Exercise 2.2.1.** A spin-only replica observable has the same average after integrating
out the auxiliary Gaussian spins. The direct logarithmic expression is the book's `u_t`.
The identity holds for every real coefficient parameter `t`; the smart path uses `0 ≤ t ≤ 1`.
The energy is written with its last-field term first, by commutativity of addition. -/
theorem integral_pi_perceptron_smart_path_auxiliary {N M : ℕ} {R : Type*} [Fintype R]
    {u : ℝ → ℝ} (hu : Measurable u) {D : ℝ} (hD : ∀ x, u x ≤ D)
    (g : Fin M → Fin N → ℝ) (a : Fin M → ℝ) (y t : ℝ)
    (F : (R → (Fin N → ℤˣ) × ℤˣ) → ℝ) :
    let S : ((Fin N → ℤˣ) × ℤˣ) → Fin M → ℝ := fun σ k =>
      (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, g k i * ((σ.1 i : ℤ) : ℝ)) +
        Real.sqrt (t / (N + 1)) * a k * ((σ.2 : ℤ) : ℝ)
    (∫ x : R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ), F (fun r => (x r).1)
      ∂(Measure.pi fun _ : R =>
        ((Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ)).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)).tilted
        (fun p => ((p.1.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * y +
          ∑ k, u (S p.1 k + Real.sqrt ((1 - t) / (N + 1)) * p.2 k)))) =
      ∫ σ, F σ ∂(Measure.pi fun _ : R => Measure.count.tilted
        (fun σ : (Fin N → ℤˣ) × ℤˣ => ((σ.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * y +
          ∑ k, Real.log (∫ z, Real.exp (u (S σ k +
            Real.sqrt ((1 - t) / (N + 1)) * z)) ∂gaussianReal 0 1))) := by
  intro S
  exact integral_pi_tilted_count_prod_sum (fun _ : Fin M => gaussianReal 0 1)
    (fun σ : (Fin N → ℤˣ) × ℤˣ => ((σ.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * y)
    (fun σ k z => u (S σ k + Real.sqrt ((1 - t) / (N + 1)) * z))
    (fun σ k => hu.comp (by fun_prop)) (fun _ => D) (fun _ _ z => hD _) F

end SpinGlasses
