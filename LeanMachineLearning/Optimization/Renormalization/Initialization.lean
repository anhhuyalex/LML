/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Network
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Covariance

/-!
# Independent Gaussian initialization of a dense layer

This file constructs the law, rather than merely postulating coordinate moments.  Its two nested
finite `Measure.pi` products encode independence of weight coordinates, and an outer product keeps
weights independent from biases.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace NeuralNetwork

universe u v

/-- Bias and unscaled weight variances.  Nonnegativity is represented in the type. -/
structure InitHyperparams where
  /-- Variance shared by the independent bias coordinates. -/
  biasVariance : ℝ≥0
  /-- Weight variance before division by the layer's fan-in. -/
  weightVariance : ℝ≥0

/-- Fan-in-scaled variance of one weight coordinate. -/
def scaledWeightVariance (p : InitHyperparams) (ι : Type u) [Fintype ι] : ℝ≥0 :=
  p.weightVariance / (Fintype.card ι : ℝ≥0)

/-- Independent centered Gaussian weight coordinates. -/
def gaussianWeightLaw (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] : Measure (κ → ι → ℝ) :=
  Measure.pi fun _ : κ => Measure.pi fun _ : ι => gaussianReal 0 (scaledWeightVariance p ι)

/-- Independent centered Gaussian bias coordinates. -/
def gaussianBiasLaw (p : InitHyperparams) (κ : Type v) [Fintype κ] : Measure (κ → ℝ) :=
  Measure.pi fun _ : κ => gaussianReal 0 p.biasVariance

/-- Product law of all weight and bias coordinates of a dense layer. -/
def layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] : Measure (LayerParams ι κ) :=
  (gaussianWeightLaw p ι κ).prod (gaussianBiasLaw p κ)

instance instIsProbabilityMeasureLayerGaussianInit (p : InitHyperparams)
    (ι : Type u) (κ : Type v) [Fintype ι] [Fintype κ] :
    IsProbabilityMeasure (layerGaussianInit p ι κ) := by
  unfold layerGaussianInit gaussianWeightLaw gaussianBiasLaw
  infer_instance

/-- Named theorem form of the probability-measure instance. -/
theorem isProbabilityMeasure_layerGaussianInit (p : InitHyperparams)
    (ι : Type u) (κ : Type v) [Fintype ι] [Fintype κ] :
    IsProbabilityMeasure (layerGaussianInit p ι κ) := by
  infer_instance

/-- A bias coordinate has the requested centered Gaussian law.

Informal proof: map the outer product by `Prod.snd`, then map the finite product by evaluation at
`j`.  `Measure.map_snd_prod` and `Measure.pi_map_eval` reduce the result to the corresponding
factor.  See Mathlib's finite product construction:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/Pi.html>. -/
theorem map_bias_layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] (j : κ) :
    Measure.map (fun q : LayerParams ι κ => q.2 j) (layerGaussianInit p ι κ) =
      gaussianReal 0 p.biasVariance := by
  classical
  haveI : IsProbabilityMeasure (gaussianWeightLaw p ι κ) := by
    unfold gaussianWeightLaw
    infer_instance
  rw [show (fun q : LayerParams ι κ => q.2 j) = Function.eval j ∘ Prod.snd from rfl,
    ← Measure.map_map (measurable_pi_apply j) measurable_snd]
  simp only [layerGaussianInit, Measure.map_snd_prod, measure_univ, one_smul, gaussianBiasLaw]
  rw [Measure.pi_map_eval]
  simp

/-- A weight coordinate has the fan-in-scaled centered Gaussian law.

Informal proof: map the outer product by `Prod.fst`, then apply `Measure.pi_map_eval` first at `j`
and then at `i`.  Probability normalization removes the scalar factors introduced by projection.
See <https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/Pi.html>. -/
theorem map_weight_layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] (j : κ) (i : ι) :
    Measure.map (fun q : LayerParams ι κ => q.1 j i) (layerGaussianInit p ι κ) =
      gaussianReal 0 (scaledWeightVariance p ι) := by
  classical
  haveI : IsProbabilityMeasure (gaussianBiasLaw p κ) := by
    unfold gaussianBiasLaw
    infer_instance
  rw [show (fun q : LayerParams ι κ => q.1 j i) =
      Function.eval i ∘ (fun q : LayerParams ι κ => q.1 j) from rfl,
    ← Measure.map_map (measurable_pi_apply i)
      ((measurable_pi_apply j).comp measurable_fst)]
  rw [show (fun q : LayerParams ι κ => q.1 j) = Function.eval j ∘ Prod.fst from rfl,
    ← Measure.map_map (measurable_pi_apply j) measurable_fst]
  simp only [layerGaussianInit, Measure.map_fst_prod, measure_univ, one_smul,
    gaussianWeightLaw]
  rw [Measure.pi_map_eval]
  simp only [measure_univ, Finset.prod_const_one, one_smul]
  rw [Measure.pi_map_eval]
  simp only [measure_univ, Finset.prod_const_one, one_smul]

/-- Bias coordinates are mutually independent.

Informal proof: `iIndepFun_pi` gives independence of evaluations under `gaussianBiasLaw`; composing
with the second projection preserves it under the independent outer product.  See Mathlib's
`ProbabilityTheory.iIndepFun_pi`:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html>. -/
theorem iIndepFun_bias_layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] :
    iIndepFun (fun j (q : LayerParams ι κ) => q.2 j) (layerGaussianInit p ι κ) := by
  sorry

/-- All flattened weight coordinates are mutually independent.

Informal proof: apply `iIndepFun_pi` at the outer weight-row product and within every row, or use
its `HasLaw` characterization to flatten the two finite products into a product indexed by
`κ × ι`.  See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html>. -/
theorem iIndepFun_weight_layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] :
    iIndepFun (fun ji : κ × ι => fun q : LayerParams ι κ => q.1 ji.1 ji.2)
      (layerGaussianInit p ι κ) := by
  sorry

/-- The complete weight vector is independent of the complete bias vector.

Informal proof: these are the two coordinate projections of the product measure
`gaussianWeightLaw.prod gaussianBiasLaw`; independence of product projections is the defining
product-measure theorem.  See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html>. -/
theorem indepFun_weight_bias_layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] :
    IndepFun (fun q : LayerParams ι κ => q.1) (fun q => q.2) (layerGaussianInit p ι κ) := by
  sorry

/-- Every initialized bias is centered.

Informal proof: transfer the integral through `map_bias_layerGaussianInit` and use Mathlib's
`integral_id_gaussianReal`.  See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Gaussian/Real.html>. -/
theorem integral_bias_layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] (j : κ) :
    ∫ q, q.2 j ∂layerGaussianInit p ι κ = 0 := by
  let X : LayerParams ι κ → ℝ := fun q => q.2 j
  have hX : Measurable X := (measurable_pi_apply j).comp measurable_snd
  calc
    ∫ q, q.2 j ∂layerGaussianInit p ι κ =
        ∫ x, x ∂Measure.map X (layerGaussianInit p ι κ) := by
      symm
      exact integral_map hX.aemeasurable continuous_id.aestronglyMeasurable
    _ = ∫ x, x ∂gaussianReal 0 p.biasVariance := by rw [map_bias_layerGaussianInit]
    _ = 0 := integral_id_gaussianReal

/-- Every initialized weight is centered.

Informal proof: transfer the integral through `map_weight_layerGaussianInit` and apply
`integral_id_gaussianReal`.  See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Gaussian/Real.html>. -/
theorem integral_weight_layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] (j : κ) (i : ι) :
    ∫ q, q.1 j i ∂layerGaussianInit p ι κ = 0 := by
  let X : LayerParams ι κ → ℝ := fun q => q.1 j i
  have hX : Measurable X :=
    (measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_fst)
  calc
    ∫ q, q.1 j i ∂layerGaussianInit p ι κ =
        ∫ x, x ∂Measure.map X (layerGaussianInit p ι κ) := by
      symm
      exact integral_map hX.aemeasurable continuous_id.aestronglyMeasurable
    _ = ∫ x, x ∂gaussianReal 0 (scaledWeightVariance p ι) := by
      rw [map_weight_layerGaussianInit]
    _ = 0 := integral_id_gaussianReal

/-- Bias covariance is the expected Kronecker-delta formula.

Informal proof: for equal indices this is `variance_id_gaussianReal` transported through the
coordinate-law theorem; for unequal indices, mutual independence and centeredness give zero
covariance.  See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/Covariance.html>. -/
theorem covariance_bias_layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] [DecidableEq κ] (j j' : κ) :
    cov[fun q : LayerParams ι κ => q.2 j, fun q => q.2 j'; layerGaussianInit p ι κ] =
      if j = j' then p.biasVariance else 0 := by
  sorry

/-- Weight covariance is diagonal in both neuron and input coordinates.

Informal proof: equality of the pairs reduces to the transported Gaussian variance theorem;
distinct pairs are independent by `iIndepFun_weight_layerGaussianInit`, hence have covariance zero.
See <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/Covariance.html>. -/
theorem covariance_weight_layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (j j' : κ) (i i' : ι) :
    cov[fun q : LayerParams ι κ => q.1 j i, fun q => q.1 j' i'; layerGaussianInit p ι κ] =
      if j = j' ∧ i = i' then scaledWeightVariance p ι else 0 := by
  sorry

end NeuralNetwork

end

end
