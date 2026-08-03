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

/-- Every full-network Gaussian initialization is a probability measure.

Informal proof: induct on the architecture. The output case is
`isProbabilityMeasure_layerGaussianInit`. At a hidden constructor, the first-layer law and the
induction-hypothesis law for the tail are probability measures, and their product is again a
probability measure. See Mathlib's product-measure API:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/Prod/Basic.html>. -/
theorem isProbabilityMeasure_gaussianInit {m n : ℕ} (S : MLPShape m n)
    (p : S.Hyperparams) : IsProbabilityMeasure (S.gaussianInit p) := by
  sorry

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
  sorry

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
