/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GibbsMeasure

/-!
# The coupled free energy (Talagrand, Eqs. (1.283)--(1.286))

Two copies of a system with energy `f` that interact through `λ Θ(σ¹, σ²)` have partition function
`Z_λ = ∑_{σ¹,σ²} exp(f σ¹ + f σ² + λ Θ(σ¹, σ²))`.  Since `Z_0 = (∑_σ exp (f σ))²`, one has
`log Z_λ - log Z_0 = log ⟨exp(λ Θ)⟩`, the average being over two independent replicas of the
Gibbs measure of `f`.  For `Θ = R₁₂ · M` this is the identity (1.286).

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Eqs. (1.283)--(1.286).
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace SpinGlasses

/-- **Eq. (1.286), finite form.**  For a finite nonempty configuration space `α`, an energy
`f` and a pair interaction `Θ`,
`log ∑_{x,y} exp(f x + f y + Θ x y) - log ∑_{x,y} exp(f x + f y)
  = log 𝔼_{σ¹,σ² ∼ Gibbs(f)} exp(Θ(σ¹, σ²))`. -/
theorem log_sum_sum_exp_coupled_sub {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (f : α → ℝ) (Θ : α → α → ℝ) :
    Real.log (∑ x, ∑ y, Real.exp (f x + f y + Θ x y)) -
        Real.log (∑ x, ∑ y, Real.exp (f x + f y)) =
      Real.log (∫ σ : Fin 2 → α, Real.exp (Θ (σ 0) (σ 1))
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted f)) := by
  have hZ : 0 < ∑ b, Real.exp (f b) := Finset.sum_pos (fun b _ => Real.exp_pos _)
    Finset.univ_nonempty
  have hA : 0 < ∑ x, ∑ y, Real.exp (f x + f y + Θ x y) :=
    Finset.sum_pos (fun x _ => Finset.sum_pos (fun y _ => Real.exp_pos _) Finset.univ_nonempty)
      Finset.univ_nonempty
  have hZ2 : ∑ x, ∑ y, Real.exp (f x + f y) = (∑ b, Real.exp (f b)) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    simp only [Real.exp_add]
  have hint : ∫ σ : Fin 2 → α, Real.exp (Θ (σ 0) (σ 1))
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted f) =
      (∑ x, ∑ y, Real.exp (f x + f y + Θ x y)) / (∑ b, Real.exp (f b)) ^ 2 := by
    rw [integral_pi_fin_two_count_tilted f (fun x y => Real.exp (Θ x y)), Finset.sum_div]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Real.exp_add]
    field_simp
  rw [hint, hZ2, Real.log_div hA.ne' (pow_pos hZ 2).ne']

end SpinGlasses
