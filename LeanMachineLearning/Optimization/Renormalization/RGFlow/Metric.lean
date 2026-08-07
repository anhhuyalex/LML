/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.InducedLaw
public import LeanMachineLearning.Optimization.Renormalization.Gaussian

/-!
# The stochastic metric at an arbitrary layer

This file formalizes `docs/Renormalization.md`'s `eq:general-stochastic-metric`,
`eq:mean-metric-any-layer`, and `eq:metric-fluctuation-general-layer`: the covariance matrix of a
Gaussian-initialized layer, applied to a *random* batch of inputs (namely, the previous layer's
activations) rather than a fixed dataset. `NeuralNetwork.layerCovariance` already computes this
covariance for one fixed input batch `s : A → ι → ℝ`; this file only adds randomness by
integrating over the law of `s`, and hence needs no new probability-theory infrastructure beyond
what `InducedLaw.lean` and `Gaussian.lean` already provide.

See `LML/blueprint/src/chapters/renormalization.tex`, Chapter "RG flow of preactivations",
Section "The stochastic metric at an arbitrary layer".
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter NeuralNetwork Renormalization
open scoped ENNReal NNReal

namespace RGFlow

universe uA uI

variable {A : Type uA} {ι : Type uI} [Fintype ι] [Fintype A] [DecidableEq A]

/-- The stochastic metric `Ĝ^{(ℓ+1)}` of one realization `z : A → ι → ℝ` of the previous layer's
preactivations: apply the activation `σ` coordinatewise and then take the layer covariance.

Source: `eq:general-stochastic-metric`, specialized from `eq:second-layer-metric-mean`. -/
def stochasticMetric (p : InitHyperparams) (σ : ℝ → ℝ) (z : A → ι → ℝ) : Matrix A A ℝ :=
  layerCovariance p (batchActivate σ z)

omit [Fintype A] [DecidableEq A] in
@[simp] theorem stochasticMetric_apply (p : InitHyperparams) (σ : ℝ → ℝ) (z : A → ι → ℝ)
    (a a' : A) :
    stochasticMetric p σ z a a' =
      p.biasVariance + scaledWeightVariance p ι * ∑ i, σ (z a i) * σ (z a' i) := by
  simp [stochasticMetric, layerCovariance, batchActivate]

omit [DecidableEq A] in
/-- The stochastic metric is positive semidefinite, entrywise-pointwise in `z`; a direct corollary
of `NeuralNetwork.layerCovariance_posSemidef`. -/
theorem stochasticMetric_posSemidef (p : InitHyperparams) (σ : ℝ → ℝ) (z : A → ι → ℝ) :
    (stochasticMetric p σ z).PosSemidef :=
  layerCovariance_posSemidef p (batchActivate σ z)

/-- The mean metric `G^{(ℓ+1)}`: the entrywise expectation of the stochastic metric under the law
`ν` of the previous layer's preactivations `z : A → ι → ℝ`.

Source: `eq:mean-metric-any-layer`. -/
def meanMetric (ν : Measure (A → ι → ℝ)) (p : InitHyperparams) (σ : ℝ → ℝ) : Matrix A A ℝ :=
  fun a a' => ∫ z, stochasticMetric p σ z a a' ∂ν

/-- The metric fluctuation `ΔG^{(ℓ+1)}` at one realization `z`: the stochastic metric minus its
mean.

Source: `eq:metric-fluctuation-general-layer`. -/
def metricFluctuation (ν : Measure (A → ι → ℝ)) (p : InitHyperparams) (σ : ℝ → ℝ)
    (z : A → ι → ℝ) : Matrix A A ℝ :=
  stochasticMetric p σ z - meanMetric ν p σ

omit [Fintype A] [DecidableEq A] in
@[simp] theorem metricFluctuation_apply (ν : Measure (A → ι → ℝ)) (p : InitHyperparams)
    (σ : ℝ → ℝ) (z : A → ι → ℝ) (a a' : A) :
    metricFluctuation ν p σ z a a' = stochasticMetric p σ z a a' - meanMetric ν p σ a a' := rfl

omit [Fintype A] [DecidableEq A] in
/-- The metric fluctuation is centered: its `ν`-expectation vanishes entrywise.

Source: the sentence immediately following `eq:metric-fluctuation-general-layer`. -/
theorem integral_metricFluctuation_eq_zero (ν : Measure (A → ι → ℝ)) [IsProbabilityMeasure ν]
    (p : InitHyperparams) (σ : ℝ → ℝ) (a a' : A)
    (hint : Integrable (fun z => stochasticMetric p σ z a a') ν) :
    ∫ z, metricFluctuation ν p σ z a a' ∂ν = 0 := by
  simp only [metricFluctuation_apply]
  rw [integral_sub hint (integrable_const _), integral_const]
  simp [meanMetric]

/-- **Conditional law of an arbitrary layer given the previous one.**

Push forward the Gaussian layer-parameter law through batched preactivation on a *fixed*
realization `z` of the previous layer's activations: this is a direct instance of
`NeuralNetwork.map_evalBatch_layerGaussianInit` with the input batch `s := batchActivate σ z`, and
needs no new proof. Randomizing `z` according to its own (previous-layer) law and applying the
tower property recovers the source's `eq:general-layer-conditional`; see
`RGFlow.integral_coordinateProduct_eq_wick_stochasticMetric` below for the resulting even-moment
formula.

Source: `eq:general-layer-conditional`. -/
theorem map_batchPreactivation_eq_pi_multivariateGaussian_stochasticMetric
    {κ : Type*} [Fintype κ] (p : InitHyperparams) (σ : ℝ → ℝ) (z : A → ι → ℝ) :
    Measure.map (fun q : LayerParams ι κ => fun j => batchToEuclidean (batchPreactivation q
        (batchActivate σ z)) j)
        (layerGaussianInit p ι κ) =
      Measure.pi (fun _ : κ => multivariateGaussian 0 (stochasticMetric p σ z)) :=
  map_evalBatch_layerGaussianInit p (batchActivate σ z)

/-- The marginal law of the next layer's *entire* batch of preactivations (all neurons, all
samples), obtained by mixing the conditional Gaussian law
(`map_batchPreactivation_eq_pi_multivariateGaussian_stochasticMetric`) over the previous layer's
law `ν`. This is the rigorous meaning of `eq:marginal-integrated-out-ell-layer`:
`p(z^{(ℓ+1)} | 𝒟) = ∫ dz^{(ℓ)} p(z^{(ℓ+1)} | z^{(ℓ)}) p(z^{(ℓ)} | 𝒟)`. -/
def nextLayerLaw (ν : Measure (A → ι → ℝ)) (p : InitHyperparams) (σ : ℝ → ℝ)
    (κ : Type*) [Fintype κ] : Measure (κ → EuclideanSpace ℝ A) :=
  ν.bind fun z => Measure.map
    (fun q : LayerParams ι κ => fun j => batchToEuclidean (batchPreactivation q
      (batchActivate σ z)) j) (layerGaussianInit p ι κ)

/-- The next-layer law is exactly the `ν`-mixture of the conditional Gaussian laws: a direct
consequence of `map_batchPreactivation_eq_pi_multivariateGaussian_stochasticMetric`, with no
further proof needed beyond congruence of `Measure.bind` in its kernel argument. -/
theorem nextLayerLaw_eq_bind_pi_multivariateGaussian
    (ν : Measure (A → ι → ℝ)) (p : InitHyperparams) (σ : ℝ → ℝ)
    (κ : Type*) [Fintype κ] :
    nextLayerLaw ν p σ κ =
      ν.bind fun z =>
        Measure.pi (fun _ : κ => multivariateGaussian 0 (stochasticMetric p σ z)) := by
  unfold nextLayerLaw
  refine congrArg (Measure.bind ν) (funext fun z => ?_)
  exact map_batchPreactivation_eq_pi_multivariateGaussian_stochasticMetric p σ z

/-- **General even-moment Wick formula at an arbitrary layer.**

Fix one neuron `j₀`. The `2m`-point correlator of that neuron's preactivations across the sample
tuple `index`, computed under the full mixture law `nextLayerLaw`, equals the `ν`-average of the
Wick sum in the *stochastic* metric `stochasticMetric p σ z`. This is
`eq:general-even-moment` specialized to a single neuron; the general statement with several
neurons and Kronecker-delta bookkeeping follows from this one together with the
neuron-independence already recorded in
`map_batchPreactivation_eq_pi_multivariateGaussian_stochasticMetric` (different neurons are a
`Measure.pi` product, hence independent, conditionally on `z`).

This is the one place in the chapter that needs a genuinely new proof-engineering pattern: "apply
a fixed-covariance Gaussian theorem to a random covariance, then integrate out the randomness."
The blueprint (`sec:ngp:refactors`, item 1) proposes extracting the general form of this pattern
as a reusable lemma in `Gaussian.lean` rather than inlining it here; until that lemma exists this
theorem is recorded with `sorry`.

Informal proof: by `nextLayerLaw_eq_bind_pi_multivariateGaussian`, the neuron-`j₀` marginal of
`nextLayerLaw` is `ν.bind (fun z => multivariateGaussian 0 (stochasticMetric p σ z))` (project the
product measure `Measure.pi` onto coordinate `j₀`, which is standard Mathlib API for
`Measure.pi`). The Bochner integral of a product of coordinate functions against a `Measure.bind`
mixture is the `ν`-integral of the same product's expectation under each mixture component (a
Fubini/tower-property argument), which for each fixed `z` is exactly
`integral_prod_multivariateGaussian_centered_eq_wick` (already proved in `Gaussian.lean`, applied
with mean `0`) evaluated at covariance `stochasticMetric p σ z`.
Source: `eq:general-even-moment` and `eq:general-layer-conditional`, book lines 2840-2854. -/
theorem integral_coordinateProduct_eq_wick_stochasticMetric
    (ν : Measure (A → ι → ℝ)) (p : InitHyperparams) (σ : ℝ → ℝ)
    (κ : Type*) [Fintype κ] [DecidableEq κ]
    (j₀ : κ) (m : ℕ) (index : Fin (2 * m) → A) :
    jointMoment (Measure.map (fun w : κ → EuclideanSpace ℝ A => w j₀) (nextLayerLaw ν p σ κ))
        (fun r w => w.ofLp (index r)) =
      ∫ z, wick (fun r q => stochasticMetric p σ z (index r) (index q)) Finset.univ ∂ν := by
  sorry

end RGFlow
