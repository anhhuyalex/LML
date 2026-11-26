/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The mean of a Gram kernel

The double average of the Gram kernel `⟪f a, f b⟫` of an integrable function with values in a
Hilbert space is `‖∫ f‖²`; for a finite family of real functions, the double average of
`∑ i, f i a * f i b` is the sum of the squared means.
-/

@[expose] public section

open MeasureTheory

/-- **The mean of a Gram kernel** in a Hilbert space: `∬ ⟪f a, f b⟫ = ‖∫ f‖²`. -/
theorem integral_integral_inner_eq_norm_integral_sq {α 𝕜 E : Type*} [MeasurableSpace α]
    [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} {f : α → E} (hf : Integrable f μ) :
    ∫ a, ∫ b, inner 𝕜 (f a) (f b) ∂μ ∂μ = (‖∫ a, f a ∂μ‖ : 𝕜) ^ 2 := by
  have h : ∀ v : E, ∫ a, inner 𝕜 (f a) v ∂μ = inner 𝕜 (∫ a, f a ∂μ) v := fun v => by
    simp_rw [← inner_conj_symm (𝕜 := 𝕜) _ v]
    rw [integral_conj, integral_inner hf, inner_conj_symm]
  simp_rw [integral_inner hf]
  rw [h, inner_self_eq_norm_sq_to_K]

/-- **The mean of a Gram kernel:**
`∬ ∑_{i ∈ s} f_i(a) f_i(b) dμ(b) dμ(a) = ∑_{i ∈ s} (∫ f_i dμ)²`. -/
theorem integral_integral_finset_sum_mul {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Finset ι) (f : ι → α → ℝ) (hf : ∀ i ∈ s, Integrable (f i) μ) :
    ∫ a, ∫ b, ∑ i ∈ s, f i a * f i b ∂μ ∂μ = ∑ i ∈ s, (∫ a, f i a ∂μ) ^ 2 := by
  have h : ∀ i ∈ s, ∫ a, ∫ b, f i a * f i b ∂μ ∂μ = (∫ a, f i a ∂μ) ^ 2 := fun i hi => by
    have h := integral_integral_inner_eq_norm_integral_sq (𝕜 := ℝ) (hf i hi)
    simpa [mul_comm] using h
  have hin : ∀ a, ∫ b, ∑ i ∈ s, f i a * f i b ∂μ = ∑ i ∈ s, ∫ b, f i a * f i b ∂μ := fun a =>
    integral_finsetSum _ fun i hi => (hf i hi).const_mul _
  simp_rw [hin]
  rw [integral_finsetSum _ fun i hi => by
    simp_rw [integral_const_mul]
    exact (hf i hi).mul_const _]
  exact Finset.sum_congr rfl h
