/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Initialization
public import LeanMachineLearning.Optimization.Renormalization.ParameterizedMLP

/-!
# Independent Gaussian initialization of a fixed MLP shape

This file upgrades the single-layer initialization law to an explicit joint law on
`MLPShape.Params`. It is the rigorous meaning of the Chapter 2 density `p(θ)`: parameters in
different layers, as well as scalar coordinates within each layer, are independent.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace NeuralNetwork

universe u v

namespace MLPShape

/-- One pair of Gaussian initialization hyperparameters for every affine layer of a fixed shape. -/
def Hyperparams {m n : ℕ} : MLPShape m n → Type
  | .output => InitHyperparams
  | .hidden tail => InitHyperparams × tail.Hyperparams

/-- The joint independent Gaussian law of every parameter in a fixed MLP.

The outer product at a hidden constructor makes the first layer independent of all later layers;
`layerGaussianInit` supplies the independent scalar coordinates inside that layer. -/
def gaussianInit {m n : ℕ} : (S : MLPShape m n) → S.Hyperparams → Measure S.Params
  | .output, p => layerGaussianInit p (Fin m) (Fin n)
  | .hidden (k := k) tail, p =>
      (layerGaussianInit p.1 (Fin m) (Fin k)).prod (tail.gaussianInit p.2)

-- The law at a hidden constructor is the product of the first-layer Gaussian law with the tail
-- law.  The first factor is a probability measure by `isProbabilityMeasure_layerGaussianInit`,
-- so the product is a probability measure exactly when the tail law is one; that hypothesis is
-- supplied by the induction hypothesis in `isProbabilityMeasure_gaussianInit`.
private lemma isProbabilityMeasure_gaussianInit_hidden {k n m : ℕ} (p₁ : InitHyperparams)
    (tail : MLPShape k n) (p₂ : tail.Hyperparams)
    (htail : IsProbabilityMeasure (tail.gaussianInit p₂)) :
    IsProbabilityMeasure ((layerGaussianInit p₁ (Fin m) (Fin k)).prod (tail.gaussianInit p₂)) :=
  inferInstance

/-- Every full-network Gaussian initialization is a probability measure.

Informal proof: induct on the architecture. The output case is
`isProbabilityMeasure_layerGaussianInit`. At a hidden constructor, the first-layer law and the
induction-hypothesis law for the tail are probability measures, and their product is again a
probability measure. See Mathlib's product-measure API:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/Prod/Basic.html>. -/
theorem isProbabilityMeasure_gaussianInit {m n : ℕ} (S : MLPShape m n)
    (p : S.Hyperparams) : IsProbabilityMeasure (S.gaussianInit p) := by
  induction S with
  | output => exact isProbabilityMeasure_layerGaussianInit p _ _
  | hidden tail ih => exact isProbabilityMeasure_gaussianInit_hidden p.1 tail p.2 (ih p.2)

noncomputable instance instIsProbabilityMeasureGaussianInit {m n : ℕ} (S : MLPShape m n)
    (p : S.Hyperparams) : IsProbabilityMeasure (S.gaussianInit p) :=
  S.isProbabilityMeasure_gaussianInit p

/-- A single index type for every scalar weight and bias in every layer of a fixed MLP. -/
def Coordinate {m n : ℕ} : MLPShape m n → Type
  | .output => LayerCoordinate (Fin m) (Fin n)
  | .hidden (k := k) tail => LayerCoordinate (Fin m) (Fin k) ⊕ tail.Coordinate

/-- Read one scalar parameter from the structured parameter space of a fixed MLP. -/
def coordinate {m n : ℕ} (S : MLPShape m n) (c : S.Coordinate) (θ : S.Params) : ℝ :=
  match S with
  | .output => layerCoordinate c θ
  | .hidden tail =>
      match c with
      | Sum.inl c => layerCoordinate c θ.1
      | Sum.inr c => tail.coordinate c θ.2

/-- Variance assigned to a scalar coordinate by a full-network initialization. -/
def coordinateVariance {m n : ℕ} (S : MLPShape m n)
    (p : S.Hyperparams) (c : S.Coordinate) : ℝ≥0 :=
  match S with
  | .output =>
      match c with
      | Sum.inl _ => scaledWeightVariance p (Fin m)
      | Sum.inr _ => p.biasVariance
  | .hidden tail =>
      match c with
      | Sum.inl (Sum.inl _) => scaledWeightVariance p.1 (Fin m)
      | Sum.inl (Sum.inr _) => p.1.biasVariance
      | Sum.inr c => tail.coordinateVariance p.2 c

/-- A flattened scalar coordinate of one layer has the corresponding single-layer Gaussian law. -/
private theorem map_layerCoordinate_layerGaussianInit (p : InitHyperparams)
    (ι : Type u) (κ : Type v) [Fintype ι] [Fintype κ]
    (c : LayerCoordinate ι κ) :
    Measure.map (fun q : LayerParams ι κ => layerCoordinate c q) (layerGaussianInit p ι κ) =
      gaussianReal 0 (match c with
        | Sum.inl _ => scaledWeightVariance p ι
        | Sum.inr _ => p.biasVariance) := by
  cases c with
  | inl ji =>
      simpa [layerCoordinate] using map_weight_layerGaussianInit p ι κ ji.1 ji.2
  | inr j =>
      simpa [layerCoordinate] using map_bias_layerGaussianInit p ι κ j

/-- Layer-coordinate evaluation is measurable. -/
private theorem measurable_layerCoordinate' {ι : Type u} {κ : Type v}
    (c : LayerCoordinate ι κ) :
    Measurable (fun q : LayerParams ι κ => layerCoordinate c q) := by
  cases c with
  | inl ji => exact (measurable_pi_apply ji.2).comp ((measurable_pi_apply ji.1).comp measurable_fst)
  | inr j => exact (measurable_pi_apply j).comp measurable_snd

/-- Reading any scalar coordinate of an MLP parameter tuple is measurable. -/
private theorem measurable_coordinate {m n : ℕ} (S : MLPShape m n) (c : S.Coordinate) :
    Measurable (S.coordinate c) := by
  induction S with
  | output =>
      rename_i m₀ n₀
      exact measurable_layerCoordinate' c
  | hidden tail ih =>
      rename_i m₀ n₀ k
      cases c with
      | inl c =>
          exact (measurable_layerCoordinate' c).comp measurable_fst
      | inr c =>
          exact (ih c).comp measurable_snd

/-- Output-layer case of `map_coordinate_gaussianInit`.

Informal proof: after unfolding `coordinate`, `gaussianInit`, and `coordinateVariance`, this is
exactly `map_layerCoordinate_layerGaussianInit`, hence ultimately the single-layer marginal
lemmas `map_weight_layerGaussianInit` and `map_bias_layerGaussianInit`. -/
private theorem map_coordinate_gaussianInit_output {m n : ℕ}
    (p : (MLPShape.output : MLPShape m n).Hyperparams)
    (c : (MLPShape.output : MLPShape m n).Coordinate) :
    Measure.map ((MLPShape.output : MLPShape m n).coordinate c)
        ((MLPShape.output : MLPShape m n).gaussianInit p) =
      gaussianReal 0 ((MLPShape.output : MLPShape m n).coordinateVariance p c) := by
  sorry

/-- Hidden-layer induction step for `map_coordinate_gaussianInit`.

Informal proof: split `c`. If `c` is in the first layer, rewrite the coordinate as a layer
coordinate composed with `Prod.fst`; `Measure.map_map` and `Measure.map_fst_prod` reduce the
marginal to the first-layer law because the tail law is a probability measure, then
`map_weight_layerGaussianInit`/`map_bias_layerGaussianInit` finish. If `c` is in the tail, use
`Prod.snd`, `Measure.map_snd_prod`, the probability-measure instance for the first-layer law, and
the induction hypothesis. This is the standard product-measure marginal argument documented at
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/Prod/Basic.html>. -/
private theorem map_coordinate_gaussianInit_hidden {m n k : ℕ} (tail : MLPShape k n)
    (ih : ∀ (p : tail.Hyperparams) (c : tail.Coordinate),
      Measure.map (tail.coordinate c) (tail.gaussianInit p) =
        gaussianReal 0 (tail.coordinateVariance p c))
    (p : (MLPShape.hidden tail : MLPShape m n).Hyperparams)
    (c : (MLPShape.hidden tail : MLPShape m n).Coordinate) :
    Measure.map ((MLPShape.hidden tail : MLPShape m n).coordinate c)
        ((MLPShape.hidden tail : MLPShape m n).gaussianInit p) =
      gaussianReal 0 ((MLPShape.hidden tail : MLPShape m n).coordinateVariance p c) := by
  sorry

/-- Every scalar parameter of a fixed MLP has its prescribed centered Gaussian marginal law.

Informal proof: induct on the shape and on whether the coordinate belongs to the first layer or
the tail. In the first case, project the first factor of the product and apply
`map_weight_layerGaussianInit` or `map_bias_layerGaussianInit`; in the second case, project the
tail factor and use the induction hypothesis. See Mathlib's product projection theorems:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/Prod/Basic.html>. -/
theorem map_coordinate_gaussianInit {m n : ℕ} (S : MLPShape m n)
    (p : S.Hyperparams) (c : S.Coordinate) :
    Measure.map (S.coordinate c) (S.gaussianInit p) =
      gaussianReal 0 (S.coordinateVariance p c) := by
  induction S with
  | output => exact map_coordinate_gaussianInit_output p c
  | hidden tail ih => exact map_coordinate_gaussianInit_hidden tail ih p c

/-- All scalar weights and biases in all layers of a fixed MLP are jointly independent.

Informal proof: `iIndepFun_layerCoordinate_layerGaussianInit` gives joint independence in the first
layer, and the induction hypothesis gives it in the tail. The two families are independent because
the full law is their product; combining them along the sum index `S.Coordinate` proves the result.
See Mathlib's independence API:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html>. -/
theorem iIndepFun_coordinate_gaussianInit {m n : ℕ} (S : MLPShape m n)
    (p : S.Hyperparams) :
    iIndepFun (fun c : S.Coordinate => S.coordinate c) (S.gaussianInit p) := by
  sorry

end MLPShape

end NeuralNetwork

end

end
