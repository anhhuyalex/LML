/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.Empirical
public import LeanMachineLearning.Optimization.NTK.FeatureLearning.Basic

/-!
# Mean-field description of the two-layer network: the neuron integral

In the mean-field regime `γ = √n` the width-`n` network is an average over its neurons,
`f(x; θ) = n⁻¹ ∑ᵢ aᵢ φ((√d)⁻¹ ⟨wᵢ, x⟩)`, which depends on the neurons `(aᵢ, wᵢ) ∈ ℝ × ℝᵈ` only
through their empirical measure `ρ⁽ⁿ⁾ = n⁻¹ ∑ᵢ δ_{(aᵢ, wᵢ)}`.  This file reads that average as an
integral `f_ρ(x) = ∫ p, p.1 * φ((√d)⁻¹ ⟨p.2, x⟩) ∂ρ` against a measure `ρ` on the single-neuron
parameter space `ℝ × (Fin d → ℝ)` ([Mei, Montanari, Nguyen 2018], [Chizat, Bach 2018]).

No definition is introduced.  The single-neuron parameter space is the product `ℝ × (Fin d → ℝ)`
itself, the neuron measure is `MeasureTheory.empiricalMeasure`
(`ForMathlib/MeasureTheory/Measure/Empirical.lean`), the predictor is the integral written out,
and the mean-field loss `L(ρ)` is `NTK.mseLoss` applied to the function
`fun x ρ => ∫ p, p.1 * φ((√d)⁻¹ * (p.2 ⬝ᵥ x)) ∂ρ`, because `mseLoss` and `trainingResidual` are
polymorphic in the parameter space `Θ = Measure (ℝ × (Fin d → ℝ))`.

## Main declarations

* `NTK.integral_empiricalMeasure_neuron`: for the empirical measure of the neurons the integral is
  the explicit width-`n` average.
* `NTK.integral_empiricalMeasure_neuron_eq_featureLearningNetwork`: it is exactly
  `featureLearningNetwork (√n)` on the packed parameters.
* `NTK.trainingResidual_integral_empiricalMeasure`, `NTK.mseLoss_integral_empiricalMeasure`:
  consequently the residual and the empirical MSE loss of the measure predictor at `ρ⁽ⁿ⁾` are those
  of the discrete network.

## Implementation notes

The predictor is a Bochner integral, so it is `0` where the integrand fails to be integrable.
Integrability is not needed for the empirical measures treated here: a finite sum of Dirac masses
integrates every function, and no `0 < n` is needed either, since both sides vanish for `n = 0`.

## References

* [Mei, Montanari, Nguyen 2018], [Chizat, Bach 2018].
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace Matrix

namespace NTK

variable {φ : ℝ → ℝ} {n d m : ℕ}

/-- **Integral representation of the width-`n` network:** for the empirical measure of the
neurons `(aᵢ, wᵢ)`, the prediction `f_ρ(x) = ∫ a φ((√d)⁻¹ ⟨w, x⟩) dρ(a, w)` of the two-layer
network with neuron distribution `ρ` is the average
`f_{ρ⁽ⁿ⁾}(x) = n⁻¹ ∑ᵢ aᵢ φ((√d)⁻¹ ⟨wᵢ, x⟩)`. -/
theorem integral_empiricalMeasure_neuron (φ : ℝ → ℝ) (a : Fin n → ℝ)
    (W : Fin n → Fin d → ℝ) (x : Fin d → ℝ) :
    ∫ p, p.1 * φ ((Real.sqrt (d : ℝ))⁻¹ * (p.2 ⬝ᵥ x)) ∂(empiricalMeasure fun i => (a i, W i)) =
      (n : ℝ)⁻¹ * ∑ i : Fin n, a i * φ ((Real.sqrt (d : ℝ))⁻¹ * (W i ⬝ᵥ x)) := by
  rw [integral_empiricalMeasure, Fintype.card_fin, smul_eq_mul]

/-- **The neuron integral at the empirical measure is the mean-field network:** it equals
`featureLearningNetwork (√n)` on the packed parameters `packParams W a`. -/
theorem integral_empiricalMeasure_neuron_eq_featureLearningNetwork (φ : ℝ → ℝ)
    (a : Fin n → ℝ) (W : Fin n → Fin d → ℝ) (x : Fin d → ℝ) :
    ∫ p, p.1 * φ ((Real.sqrt (d : ℝ))⁻¹ * (p.2 ⬝ᵥ x)) ∂(empiricalMeasure fun i => (a i, W i)) =
      featureLearningNetwork (Real.sqrt n) φ n d x (packParams W a) := by
  rw [integral_empiricalMeasure_neuron, featureLearningNetwork_sqrt_packParams]

/-- The training residual of the measure predictor at the empirical measure of the neurons is the
residual of the mean-field network `featureLearningNetwork (√n)`. -/
theorem trainingResidual_integral_empiricalMeasure (φ : ℝ → ℝ)
    (a : Fin n → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (y : EuclideanSpace ℝ (Fin m)) :
    trainingResidual (fun (x : Fin d → ℝ) (ρ : Measure (ℝ × (Fin d → ℝ))) =>
        ∫ p, p.1 * φ ((Real.sqrt (d : ℝ))⁻¹ * (p.2 ⬝ᵥ x)) ∂ρ) X y
      (empiricalMeasure fun i => (a i, W i)) =
      trainingResidual (featureLearningNetwork (Real.sqrt n) φ n d) X y (packParams W a) := by
  simp only [trainingResidual, integral_empiricalMeasure_neuron_eq_featureLearningNetwork]

/-- **The mean-field loss `L(ρ)` at the empirical measure is the loss of the network:** the
empirical MSE loss of the measure predictor at `ρ⁽ⁿ⁾` equals that of
`featureLearningNetwork (√n)` at the packed parameters.  No loss functional on measures needs to
be defined: it is `mseLoss` of the neuron integral. -/
theorem mseLoss_integral_empiricalMeasure (φ : ℝ → ℝ) (a : Fin n → ℝ)
    (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    mseLoss (fun (x : Fin d → ℝ) (ρ : Measure (ℝ × (Fin d → ℝ))) =>
        ∫ p, p.1 * φ ((Real.sqrt (d : ℝ))⁻¹ * (p.2 ⬝ᵥ x)) ∂ρ) X y
      (empiricalMeasure fun i => (a i, W i)) =
      mseLoss (featureLearningNetwork (Real.sqrt n) φ n d) X y (packParams W a) := by
  rw [mseLoss, mseLoss, trainingResidual_integral_empiricalMeasure]

end NTK
