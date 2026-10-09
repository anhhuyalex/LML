/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.FeatureLearning.MeanField
public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.Dynamics

/-!
# Accelerated gradient flow as an interacting particle system

In the mean-field regime `γ = √n`, gradient flow at the accelerated rate `η = η₀ n`,
`∂ₜ θ = -η₀ n ∇L(θ)`, moves each neuron `pᵢ = (aᵢ, wᵢ) ∈ ℝ × ℝᵈ` by an order-one velocity: the
width factor `n⁻¹` in the single-neuron gradient `∇_{pᵢ} L` is cancelled by `η₀ n`, and what
remains depends on the other neurons only through the empirical measure `ρₜ⁽ⁿ⁾` of the particles
(via the predictions `f_ρ(xᵝ)`).  So the `n` neurons form an autonomous interacting particle system
`d/dt pᵢ = b(pᵢ, ρₜ⁽ⁿ⁾)` ([Mei, Montanari, Nguyen 2018], [Chizat, Bach 2018]).

## Main declarations

* `NTK.meanFieldVelocityField η₀ φ X y p ρ`: the velocity field `b = (b_a, b_w)`, the only new
  definition.  The mean-field predictor `f_ρ(xᵝ) = ∫ q, q.1 * φ(…) ∂ρ` is spelled out in it.
* `NTK.width_factor_cancellation`: `-η₀ n ∇_{pᵢ} L = b(pᵢ, ρ⁽ⁿ⁾)`, for the single-neuron
  coordinates `∂_{aᵢ} L` and `∇_{wᵢ} L` of the loss of `featureLearningNetwork (√n)`.  It follows
  from `gradient_readout_mseLoss` / `gradient_inputWeight_mseLoss` (the `γ`-general single-neuron
  gradients), `integral_empiricalMeasure_neuron_eq_featureLearningNetwork` (the network *is*
  `f_{ρ⁽ⁿ⁾}`) and the cancellation `√n √n = n`.
* `NTK.interacting_particle_system_ode`: along the accelerated flow, each particle
  `s ↦ (aᵢ(s), wᵢ(s))` has derivative `b((aᵢ(t), wᵢ(t)), ρₜ⁽ⁿ⁾)`.  The flow hypothesis is that of
  `gradient_flow_output_vector_ode`, with `η = η₀ n`.
* `NTK.meanFieldVelocityField_congr`: `b(p, ρ)` depends on `ρ` only through its predictions
  `f_ρ(xᵝ)`.
* `NTK.mean_field_coupling_structure`: `b(p, ρ⁽ⁿ⁾)` is invariant under permuting the particles, a
  one-line consequence of `MeasureTheory.empiricalMeasure_comp_equiv`.

## References

* [Mei, Montanari, Nguyen 2018], [Chizat, Bach 2018].
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NTK

variable {φ : ℝ → ℝ} {n d m : ℕ}

/-- The velocity field `b = (b_a, b_w)` of the mean-field particle system, as a function of a
particle `p = (a, w) ∈ ℝ × ℝᵈ` and the neuron distribution `ρ`:
`b_a(p, ρ) = -(η₀/m) ∑_β (f_ρ(xᵝ) - yᵝ) φ(hᵝ)` and
`b_w(p, ρ) = -(η₀/(m √d)) ∑_β (f_ρ(xᵝ) - yᵝ) a φ'(hᵝ) xᵝ`, with `hᵝ = (√d)⁻¹ ⟨w, xᵝ⟩` and
`f_ρ(x) = ∫ q, q.1 * φ((√d)⁻¹ ⟨q.2, x⟩) ∂ρ`. -/
noncomputable def meanFieldVelocityField (η₀ : ℝ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (y : EuclideanSpace ℝ (Fin m)) (p : ℝ × (Fin d → ℝ)) (ρ : Measure (ℝ × (Fin d → ℝ))) :
    ℝ × (Fin d → ℝ) :=
  (-(η₀ / (m : ℝ)) * ∑ β : Fin m,
      ((∫ q, q.1 * φ ((Real.sqrt (d : ℝ))⁻¹ * (q.2 ⬝ᵥ X β)) ∂ρ) - y β) *
        φ ((Real.sqrt (d : ℝ))⁻¹ * (p.2 ⬝ᵥ X β)),
    fun j => -(η₀ / ((m : ℝ) * Real.sqrt (d : ℝ))) * ∑ β : Fin m,
      ((∫ q, q.1 * φ ((Real.sqrt (d : ℝ))⁻¹ * (q.2 ⬝ᵥ X β)) ∂ρ) - y β) * p.1 *
        deriv φ ((Real.sqrt (d : ℝ))⁻¹ * (p.2 ⬝ᵥ X β)) * X β j)

/-- **Cancellation of the width factor.** For the mean-field network `featureLearningNetwork (√n)`,
multiplying the single-neuron loss gradients (the `aᵢ` and `wᵢ` coordinates of the gradient of
`mseLoss` at `packParams W a`) by `-η₀ n` gives the order-one velocity
`b((aᵢ, wᵢ), ρ⁽ⁿ⁾)` of the empirical measure `ρ⁽ⁿ⁾ = n⁻¹ ∑ⱼ δ_{(aⱼ, wⱼ)}`.
No `0 < n` is needed: a neuron `i : Fin n` exists only when `n > 0`. -/
theorem width_factor_cancellation (η₀ : ℝ) (hφ : Differentiable ℝ φ) (a : Fin n → ℝ)
    (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) (i : Fin n) :
    meanFieldVelocityField η₀ φ X y (a i, W i) (empiricalMeasure fun j => (a j, W j)) =
      (-(η₀ * n) * gradient (mseLoss (featureLearningNetwork (Real.sqrt n) φ n d) X y)
          (packParams W a) (paramIndexEquiv n d (Sum.inr i)),
        fun j => -(η₀ * n) * gradient (mseLoss (featureLearningNetwork (Real.sqrt n) φ n d) X y)
          (packParams W a) (paramIndexEquiv n d (Sum.inl (i, j)))) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 i.pos.ne'
  have hsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  simp only [meanFieldVelocityField, gradient_readout_mseLoss _ hφ,
    gradient_inputWeight_mseLoss _ hφ,
    integral_empiricalMeasure_neuron_eq_featureLearningNetwork, hsq]
  refine Prod.ext ?_ (funext fun j => ?_)
  · field_simp
  · field_simp
    congr 3
    exact Finset.sum_congr rfl fun β _ => by ring

/-- **The velocity field depends on `ρ` only through the predictions `f_ρ(xᵝ)`:** two neuron
distributions with the same predictions on the data induce the same velocity at every particle. -/
theorem meanFieldVelocityField_congr (η₀ : ℝ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (y : EuclideanSpace ℝ (Fin m)) (p : ℝ × (Fin d → ℝ)) {ρ ρ' : Measure (ℝ × (Fin d → ℝ))}
    (h : ∀ β, ∫ q, q.1 * φ ((Real.sqrt (d : ℝ))⁻¹ * (q.2 ⬝ᵥ X β)) ∂ρ =
      ∫ q, q.1 * φ ((Real.sqrt (d : ℝ))⁻¹ * (q.2 ⬝ᵥ X β)) ∂ρ') :
    meanFieldVelocityField η₀ φ X y p ρ = meanFieldVelocityField η₀ φ X y p ρ' := by
  simp only [meanFieldVelocityField, h]

/-- **The coupling is all-to-all and permutation symmetric:** the velocity of a particle in the
presence of the particles `(aⱼ, wⱼ)` does not change when the other particles are relabelled by a
permutation `σ`. -/
theorem mean_field_coupling_structure (η₀ : ℝ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (y : EuclideanSpace ℝ (Fin m)) (p : ℝ × (Fin d → ℝ)) (σ : Equiv.Perm (Fin n))
    (a : Fin n → ℝ) (W : Fin n → Fin d → ℝ) :
    meanFieldVelocityField η₀ φ X y p (empiricalMeasure fun j => (a (σ j), W (σ j))) =
      meanFieldVelocityField η₀ φ X y p (empiricalMeasure fun j => (a j, W j)) := by
  exact congrArg (meanFieldVelocityField η₀ φ X y p)
    (empiricalMeasure_comp_equiv σ fun j => (a j, W j))

/-- **The accelerated gradient flow is an autonomous interacting particle system.** If the packed
parameters follow gradient flow at rate `η₀ n` for the loss of `featureLearningNetwork (√n)`,
`∂ₜ θ = -(η₀ n) ∇L(θ)`, then every particle `s ↦ (aᵢ(s), wᵢ(s))` satisfies
`d/dt (aᵢ, wᵢ) = b((aᵢ(t), wᵢ(t)), ρₜ⁽ⁿ⁾)` with `ρₜ⁽ⁿ⁾ = n⁻¹ ∑ⱼ δ_{(aⱼ(t), wⱼ(t))}`. -/
theorem interacting_particle_system_ode (η₀ : ℝ) (hφ : Differentiable ℝ φ)
    (a : ℝ → Fin n → ℝ) (W : ℝ → Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (y : EuclideanSpace ℝ (Fin m)) (t : ℝ)
    (hflow : HasDerivAt (fun s => packParams (W s) (a s))
      (-((η₀ * n) • gradient (mseLoss (featureLearningNetwork (Real.sqrt n) φ n d) X y)
        (packParams (W t) (a t)))) t) (i : Fin n) :
    HasDerivAt (fun s => (a s i, W s i))
      (meanFieldVelocityField η₀ φ X y (a t i, W t i)
        (empiricalMeasure fun j => (a t j, W t j))) t := by
  rw [width_factor_cancellation η₀ hφ (a t) (W t) X y i]
  have hcoord := (hasDerivAt_euclideanSpace _ _ _).1 hflow
  refine HasDerivAt.prodMk ?_ ((hasDerivAt_pi).2 fun j => ?_)
  · simpa [packParams_apply_idxA] using hcoord (paramIndexEquiv n d (Sum.inr i))
  · simpa [packParams_apply_idxW] using hcoord (paramIndexEquiv n d (Sum.inl (i, j)))

end NTK
