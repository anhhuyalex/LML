/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FiniteReplicaTilted

/-!
# A constant shift of the energy does not change the Gibbs measure

`Measure.count.tilted (fun a => f a + c)` and `Measure.count.tilted f` have the same replica
averages. This is the reason why an additive Gaussian that does not depend on the configuration
(such as the diagonal part of the SK Hamiltonian) drops out of every Gibbs average.
-/

@[expose] public section

open Finset

namespace MeasureTheory

variable {α R : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **Constant shifts cancel in replica Gibbs averages.** -/
theorem integral_pi_count_tilted_add_const [Fintype α] [Fintype R] (f : α → ℝ) (c : ℝ)
    (Ψ : (R → α) → ℝ) :
    ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted fun a => f a + c) =
      ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted f) := by
  classical
  rw [integral_pi_count_tilted, integral_pi_count_tilted]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun r _ => ?_
  simp only [Real.exp_add, ← Finset.sum_mul]
  have hc : Real.exp c ≠ 0 := (Real.exp_pos c).ne'
  field_simp

end MeasureTheory
