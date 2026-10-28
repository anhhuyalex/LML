/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The mean of a Gram kernel

For a finite family `f i` of integrable functions, the double average of the kernel
`∑ i, f i a * f i b` against two independent copies of a probability measure is the sum of the
squared means.
-/

@[expose] public section

open MeasureTheory

/-- **The mean of a Gram kernel:**
`∬ ∑_{i ∈ s} f_i(a) f_i(b) dμ(b) dμ(a) = ∑_{i ∈ s} (∫ f_i dμ)²`. -/
theorem integral_integral_finset_sum_mul {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Finset ι) (f : ι → α → ℝ) (hf : ∀ i ∈ s, Integrable (f i) μ) :
    ∫ a, ∫ b, ∑ i ∈ s, f i a * f i b ∂μ ∂μ = ∑ i ∈ s, (∫ a, f i a ∂μ) ^ 2 := by
  have hin : ∀ a, ∫ b, ∑ i ∈ s, f i a * f i b ∂μ = ∑ i ∈ s, f i a * ∫ b, f i b ∂μ := fun a => by
    rw [integral_finsetSum _ fun i hi => (hf i hi).const_mul _]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  simp_rw [hin]
  rw [integral_finsetSum _ fun i hi => (hf i hi).mul_const _]
  exact Finset.sum_congr rfl fun i _ => by rw [integral_mul_const, sq]
