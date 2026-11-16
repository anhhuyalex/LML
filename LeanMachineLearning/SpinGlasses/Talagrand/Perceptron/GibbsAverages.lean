/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.BoundedPotential
public import LeanMachineLearning.ForMathlib.Analysis.Calculus.IteratedDerivBounds
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FiniteReplicaTilted
public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Units
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Bounded replica averages for the Gaussian binary perceptron

The replicas share the disorder `g` and are independent under the product of the tilted counting
measures conditional on `g`. No model or Gibbs-law wrapper is needed. The observable may depend
on this disorder, as does the derivative product in Talagrand's (2.10).

The regularity hypothesis (2.7) is written directly as
`∀ j < 3, Differentiable ℝ (iteratedDeriv j u)` and
`∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D`.
The shared `lipschitzWith_iteratedDeriv_of_forall_abs_le` makes `u`, `u'` and `u''` Lipschitz.
In particular they are measurable. No continuity of `u'''` is imposed. The finite-state
integrability below needs only measurability of `u`; no uniform energy bound is necessary.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SpinGlasses

variable {N M : ℕ} {R : Type*} [Fintype R]

/-- A bounded measurable replica observable has an integrable Gibbs average under the
Gaussian disorder. Zero spins, zero constraints and an empty replica type are allowed. -/
theorem integrable_integral_pi_count_tilted_sum_potential {u : ℝ → ℝ} (hu : Measurable u)
    (Φ : (Fin M → Fin N → ℝ) → (R → Fin N → ℤˣ) → ℝ)
    (hΦ : ∀ σ, Measurable fun g => Φ g σ) {C : ℝ} (hC : ∀ g σ, |Φ g σ| ≤ C) :
    Integrable (fun g : Fin M → Fin N → ℝ => ∫ σ, Φ g σ
      ∂(Measure.pi fun _ : R => Measure.count.tilted (fun τ : Fin N → ℤˣ =>
        ∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))))
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  refine integrable_integral_pi_count_tilted_of_bound _ (fun τ => ?_) Φ hΦ C hC
  exact Finset.measurable_sum _ fun k _ => hu.comp (by fun_prop)

/-- Taking replica and disorder averages preserves a uniform bound. The energy and the
observable use the same disorder; no Gaussian-law claim for Gibbs-sampled fields is made. -/
theorem abs_integral_integral_pi_count_tilted_sum_potential_le (u : ℝ → ℝ)
    (Φ : (Fin M → Fin N → ℝ) → (R → Fin N → ℤˣ) → ℝ)
    {C : ℝ} (hC : ∀ g σ, |Φ g σ| ≤ C) :
    |∫ g : Fin M → Fin N → ℝ, ∫ σ, Φ g σ
      ∂(Measure.pi fun _ : R => Measure.count.tilted (fun τ : Fin N → ℤˣ =>
        ∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ))))
      ∂(Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1)| ≤ C :=
  abs_integral_integral_pi_tilted_le (fun _ => inferInstance) hC

/-- The derivative-product observable (2.10) has an integrable two-replica Gibbs average.
The uniform derivative bound suffices; no differentiability of `u'` is needed here. -/
theorem integrable_integral_pi_count_tilted_deriv_mul_deriv {u : ℝ → ℝ} {D : ℝ}
    (hu : Measurable u) (hD : ∀ x, |deriv u x| ≤ D) :
    Integrable (fun g : Fin M → Fin N → ℝ => ∫ σ : Fin 2 → Fin N → ℤˣ,
      (N : ℝ)⁻¹ * ∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ 0 i : ℤ) : ℝ)) *
        deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ 1 i : ℤ) : ℝ))
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (fun τ : Fin N → ℤˣ =>
        ∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ)))))
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  refine integrable_integral_pi_count_tilted_sum_potential hu _ (fun σ => ?_)
    (fun g σ => abs_inv_mul_sum_deriv_mul_deriv_le hD g (σ 0) (σ 1))
  exact measurable_const.mul (Finset.measurable_sum _ fun k _ =>
    ((measurable_deriv u).comp (by fun_prop)).mul ((measurable_deriv u).comp (by fun_prop)))

/-- The disorder-averaged derivative product retains the bound `(M / N) D²`. This bounds the
observable of (2.10); it does not prove concentration around a number `r`. -/
theorem abs_integral_integral_pi_count_tilted_deriv_mul_deriv_le {u : ℝ → ℝ} {D : ℝ}
    (hD : ∀ x, |deriv u x| ≤ D) :
    |∫ g : Fin M → Fin N → ℝ, ∫ σ : Fin 2 → Fin N → ℤˣ,
      (N : ℝ)⁻¹ * ∑ k, deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ 0 i : ℤ) : ℝ)) *
        deriv u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ 1 i : ℤ) : ℝ))
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (fun τ : Fin N → ℤˣ =>
        ∑ k, u ((Real.sqrt N)⁻¹ * ∑ i, g k i * ((τ i : ℤ) : ℝ))))
      ∂(Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1)| ≤
        M / N * D ^ 2 :=
  abs_integral_integral_pi_count_tilted_sum_potential_le u _
    (fun g σ => abs_inv_mul_sum_deriv_mul_deriv_le hD g (σ 0) (σ 1))

end SpinGlasses
