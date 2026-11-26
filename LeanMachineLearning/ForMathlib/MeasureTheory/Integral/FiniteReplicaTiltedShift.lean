/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FiniteReplicaTilted
public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# A constant shift of the energy does not change the Gibbs measure

`μ.tilted (fun a => f a + c) = μ.tilted f`, so the replica averages of both are equal. This is
the reason why an additive Gaussian that does not depend on the configuration (such as the
diagonal part of the SK Hamiltonian) drops out of every Gibbs average.
-/

@[expose] public section

open Finset

namespace MeasureTheory

variable {α R : Type*} [MeasurableSpace α]

/-- Adding a constant to the exponent does not change a tilted measure. -/
theorem tilted_add_const_exponent (μ : Measure α) (f : α → ℝ) (c : ℝ) :
    μ.tilted (fun a => f a + c) = μ.tilted f := by
  have h : (fun a => Real.exp (f a + c) / ∫ x, Real.exp (f x + c) ∂μ) =
      fun a => Real.exp (f a) / ∫ x, Real.exp (f x) ∂μ := by
    ext a
    simp only [Real.exp_add, integral_mul_const]
    exact mul_div_mul_right _ _ (Real.exp_pos c).ne'
  exact congrArg μ.withDensity (funext fun x => congrArg ENNReal.ofReal (congrFun h x))

/-- **Constant shifts cancel in replica Gibbs averages.** -/
theorem integral_pi_count_tilted_add_const [Fintype R] (f : α → ℝ) (c : ℝ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ψ : (R → α) → E) :
    ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted fun a => f a + c) =
      ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted f) := by
  rw [tilted_add_const_exponent]

end MeasureTheory
