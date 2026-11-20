/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ProductTiltedMarginal
public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Units
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathModel
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Integrating the auxiliary Gaussian spins of the perceptron smart path

Talagrand, Section 2.2, Exercise 2.2.1 and (2.20). The full system has `N + 1` spins;
the spin coordinates are the first `N` spins and the last spin separately. The auxiliary
Gaussian coordinates are part of the configuration, independently for each replica, while
the disorder `ω = ((g, a), y)` is held fixed.

Integrating the auxiliary coordinates replaces each potential by its log exponential integral.
Only measurability and an upper bound on the potential are needed; the three-derivative
assumptions of the chapter are unnecessary for this identity. It also allows no constraints,
one full spin and an empty replica type. The model objects are those of `SmartPathModel`; no
effective-potential definition is added.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SpinGlasses

/-- **Exercise 2.2.1.** A spin-only replica observable has the same average after integrating
out the auxiliary Gaussian spins. The direct logarithmic expression is the book's `u_t`; the field
`smartPathFieldNoAux t ω (σ, 0) k` is the field of (2.14), which does not depend on the auxiliary
coordinates. The identity holds for every real coefficient parameter `t`; the smart path uses
`0 ≤ t ≤ 1`. The effective energy is written with its last-field term first, by commutativity of
addition. -/
theorem integral_pi_perceptron_smart_path_auxiliary {N M : ℕ} {R : Type*} [Fintype R]
    {u : ℝ → ℝ} (hu : Measurable u) {D : ℝ} (hD : ∀ x, u x ≤ D)
    (ω : SmartPathDisorder N M) (t : ℝ) (F : (R → PerceptronSpin N) → ℝ) :
    ∫ x : R → SmartPathState N M, F (fun r => (x r).1)
      ∂(Measure.pi fun _ : R => (smartPathBase N M).tilted (smartPathEnergy u t ω)) =
      ∫ σ, F σ ∂(Measure.pi fun _ : R => Measure.count.tilted
        (fun σ : PerceptronSpin N => ((σ.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * ω.2 +
          ∑ k, Real.log (∫ z, Real.exp (u (smartPathFieldNoAux t ω (σ, 0) k +
            Real.sqrt ((1 - t) / (N + 1)) * z)) ∂gaussianReal 0 1))) := by
  exact integral_pi_tilted_count_prod_sum (fun _ : Fin M => gaussianReal 0 1)
    (fun σ : PerceptronSpin N => ((σ.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * ω.2)
    (fun σ k z => u (smartPathFieldNoAux t ω (σ, 0) k + Real.sqrt ((1 - t) / (N + 1)) * z))
    (fun σ k => hu.comp (by fun_prop)) (fun _ => D) (fun _ _ z => hD _) F

end SpinGlasses
