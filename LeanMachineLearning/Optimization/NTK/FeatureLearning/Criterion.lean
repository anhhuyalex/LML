/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Asymptotics.Theta
public import LeanMachineLearning.Optimization.NTK.FeatureLearning.Basic

/-!
# Feature learning: the quantitative criterion and the learning-rate condition

**Definition 4.1** ([Yang & Hu, 2021]).  The hidden layer *learns features* at a gradient step on a
sample `α` when the normalized squared displacement of its preactivations is of order one,
`(1/n) ‖Δh^α‖² = Θ(1)` as `n → ∞`.

No new definition is needed: the criterion is Mathlib's `Asymptotics.IsTheta` applied to
`n ↦ n⁻¹ ∑ᵢ (Δhᵢ^α)²`, and the displacement is the explicit expression of
`one_step_preactivation_update` (Milestone 1).  The generic reductions `f ^ 2 =Θ 1 ↔ f =Θ 1` and
`f / g =Θ 1 ↔ f =Θ g` are in `ForMathlib/Analysis/Asymptotics/Theta.lean`.

## Main results and proof outline

* `normalized_sq_displacement_isTheta`: if `Δhᵢ = c · Sᵢ` with the neuron average of `Sᵢ²` of order
  one, then `(1/n) ∑ᵢ Δhᵢ² = Θ(c²)`.  This is `n⁻¹ ∑ (c Sᵢ)² = c² · n⁻¹ ∑ Sᵢ²` and `IsTheta.mul`.
* `featureLearning_criterion_iff_learningRate`: `(η / (γ √n))² = Θ(1) ↔ η = Θ(γ √n)`.
* `featureLearning_iff_learningRate_of_oneStep`: for the actual one-step update of the width-`n`
  network with scaling knob `γ` and learning rate `η`, the criterion holds if and only if
  `η = Θ(γ √n)`.  The coefficient `-(η / (m γ √n))` is `one_step_preactivation_update`.

## References

* [Yang, Hu 2021], [Mei, Montanari, Nguyen 2018], [Chizat, Bach 2018].
-/

@[expose] public section

open Asymptotics Filter
open scoped Matrix

namespace NTK

/-- **Exact scaling of the normalized squared displacement.** If every coordinate of the
displacement factors as `Δh n i = c n * S n i` and the neuron average of `(S n i)²` is of order one
("typical coordinates are order one"), then `(1/n) ∑ᵢ (Δh n i)² = Θ((c n)²)`. -/
theorem normalized_sq_displacement_isTheta (c : ℕ → ℝ) (S Δh : (n : ℕ) → Fin n → ℝ)
    (hΔh : ∀ n i, Δh n i = c n * S n i)
    (hS : (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, S n i ^ 2) =Θ[atTop] fun _ => (1 : ℝ)) :
    (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, Δh n i ^ 2) =Θ[atTop] fun n => c n ^ 2 := by
  have h : ∀ n : ℕ, (n : ℝ)⁻¹ * ∑ i : Fin n, Δh n i ^ 2 =
      c n ^ 2 * ((n : ℝ)⁻¹ * ∑ i : Fin n, S n i ^ 2) := by
    intro n
    simp_rw [hΔh, mul_pow]
    rw [← Finset.mul_sum]
    ring
  simp_rw [h]
  simpa using (isTheta_refl (fun n => c n ^ 2) atTop).mul hS

/-- **Fundamental learning-rate condition.** The feature-learning scale `(η / (γ √n))²` is of order
one if and only if `η = Θ(γ √n)`. -/
theorem featureLearning_criterion_iff_learningRate (η γ : ℕ → ℝ) (hγ : ∀ n, 0 < γ n) :
    (fun n : ℕ => (η n / (γ n * Real.sqrt n)) ^ 2) =Θ[atTop] (fun _ => (1 : ℝ)) ↔
      η =Θ[atTop] fun n => γ n * Real.sqrt n := by
  refine isTheta_sq_div_one_iff ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (mul_pos (hγ n) (Real.sqrt_pos.2 (by exact_mod_cast hn))).ne'

variable {φ : ℝ → ℝ} {m d : ℕ}

/-- **Feature learning holds exactly when `η = Θ(γ √n)`.** Let `(W n, a n)` be the parameters of the
width-`n` network `featureLearningNetwork (γ n) φ n d` on a fixed dataset `(X, y)`, and
`(W' n, a' n)` the parameters after one gradient step of size `η n`.  Write `S n i` for the sum in
`one_step_preactivation_update`, so that the preactivation displacement of neuron `i` on sample `α`
is `-(η n / (m γ n √n)) * S n i`.  If the neuron average of `(S n i)²` is of order one, then
`(1/n) ∑ᵢ (Δhᵢ^α)² = Θ(1)` (Definition 4.1) if and only if `η = Θ(γ √n)`. -/
theorem featureLearning_iff_learningRate_of_oneStep (hm : 0 < m) (hφ : Differentiable ℝ φ)
    (γ η : ℕ → ℝ) (hγ : ∀ n, 0 < γ n) (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m))
    (W W' : (n : ℕ) → Fin n → Fin d → ℝ) (a a' : (n : ℕ) → Fin n → ℝ)
    (hstep : ∀ n, packParams (W' n) (a' n) = packParams (W n) (a n) -
      η n • gradient (mseLoss (featureLearningNetwork (γ n) φ n d) X y) (packParams (W n) (a n)))
    (α : Fin m) (S : (n : ℕ) → Fin n → ℝ)
    (hS_def : ∀ n i, S n i = ∑ β : Fin m,
      (featureLearningNetwork (γ n) φ n d (X β) (packParams (W n) (a n)) - y β) * a n i *
        deriv φ ((Real.sqrt (d : ℝ))⁻¹ * (W n i ⬝ᵥ X β)) * ((d : ℝ)⁻¹ * (X β ⬝ᵥ X α)))
    (hS : (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n, S n i ^ 2) =Θ[atTop] fun _ => (1 : ℝ)) :
    (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i : Fin n,
        ((Real.sqrt (d : ℝ))⁻¹ * (W' n i ⬝ᵥ X α) - (Real.sqrt (d : ℝ))⁻¹ * (W n i ⬝ᵥ X α)) ^ 2)
      =Θ[atTop] (fun _ => (1 : ℝ)) ↔
    η =Θ[atTop] fun n => γ n * Real.sqrt n := by
  rw [← featureLearning_criterion_iff_learningRate η γ hγ]
  have hΔh := normalized_sq_displacement_isTheta
    (fun n => -(η n / ((m : ℝ) * γ n * Real.sqrt n))) S
    (fun n i => (Real.sqrt (d : ℝ))⁻¹ * (W' n i ⬝ᵥ X α) - (Real.sqrt (d : ℝ))⁻¹ * (W n i ⬝ᵥ X α))
    (fun n i => by
      rw [one_step_preactivation_update (γ n) (η n) hφ X y (W n) (W' n) (a n) (a' n) (hstep n),
        hS_def])
    hS
  have hc : (fun n : ℕ => (-(η n / ((m : ℝ) * γ n * Real.sqrt n))) ^ 2) =Θ[atTop]
      fun n => (η n / (γ n * Real.sqrt n)) ^ 2 := by
    have hm' : ((m : ℝ)⁻¹ ^ 2) ≠ 0 := by positivity
    refine (EventuallyEq.isTheta (Eventually.of_forall fun n => ?_)).trans
      ((isTheta_const_mul_left (l := atTop) (g := fun n : ℕ => (η n / (γ n * Real.sqrt n)) ^ 2)
        (f := fun n : ℕ => (η n / (γ n * Real.sqrt n)) ^ 2) hm').2 (isTheta_refl _ _))
    show (-(η n / ((m : ℝ) * γ n * Real.sqrt n))) ^ 2 =
      (m : ℝ)⁻¹ ^ 2 * (η n / (γ n * Real.sqrt n)) ^ 2
    rw [neg_sq]
    ring
  have key := hΔh.trans hc
  exact ⟨fun h => (key.symm.trans h), fun h => key.trans h⟩

end NTK
