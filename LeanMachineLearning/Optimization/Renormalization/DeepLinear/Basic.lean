/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.InducedLaw
public import Mathlib.Probability.Moments.Variance

/-!
# Deep linear networks at initialization

This file specializes LML's shape-safe MLP and Gaussian-initialization APIs to bias-free deep
linear networks.  It also defines the normalized Gram matrix and normalized energy used throughout
the finite-width theory.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace NeuralNetwork

universe uA uI

/-- The Gram matrix of a finite batch, normalized by the number of input coordinates. -/
def normalizedGram {A : Type uA} {ι : Type uI} [Fintype ι]
    (x : A → ι → ℝ) : Matrix A A ℝ :=
  fun a b => (Fintype.card ι : ℝ)⁻¹ * ∑ i, x a i * x b i

/-- Mean squared coordinate magnitude of a finite vector. -/
def normalizedEnergy {ι : Type uI} [Fintype ι] (x : ι → ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ i, x i ^ 2

/-- The normalized Gram matrix is symmetric. -/
theorem normalizedGram_symm {A : Type uA} {ι : Type uI} [Fintype ι]
    (x : A → ι → ℝ) : (normalizedGram x).IsSymm := by
  ext a b
  simp only [normalizedGram, Matrix.transpose_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The normalized Gram matrix is positive semidefinite.

Informal proof: expand the quadratic form and interchange the two finite sums.  It becomes
`|ι|⁻¹ * ∑ i, (∑ a, v a * x a i)^2`, a nonnegative scalar times a sum of squares.  This is the
standard Gram-matrix proof; see <https://en.wikipedia.org/wiki/Gram_matrix#Positive-semidefiniteness>.
-/
theorem normalizedGram_posSemidef {A : Type uA} {ι : Type uI} [Fintype ι]
    (x : A → ι → ℝ) : (normalizedGram x).PosSemidef := by
  sorry

/-- A singleton batch recovers normalized energy on the diagonal. -/
@[simp] theorem normalizedGram_singleton {ι : Type uI} [Fintype ι] (x : ι → ℝ) :
    normalizedGram (fun _ : PUnit => x) PUnit.unit PUnit.unit = normalizedEnergy x := by
  simp only [normalizedGram, normalizedEnergy]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Normalized energy is nonnegative. -/
theorem normalizedEnergy_nonneg {ι : Type uI} [Fintype ι] (x : ι → ℝ) :
    0 ≤ normalizedEnergy x := by
  unfold normalizedEnergy
  positivity

/-- Normalized energy bundled as a nonnegative real. -/
def normalizedEnergyNNReal {ι : Type uI} [Fintype ι] (x : ι → ℝ) : ℝ≥0 :=
  ⟨normalizedEnergy x, normalizedEnergy_nonneg x⟩

/-- Rewrite the existing layer covariance in terms of the normalized Gram matrix.

Informal proof: unfold `layerCovariance`, `scaledWeightVariance`, and `normalizedGram`; move the
coercion from `NNReal` through division, and use `div_eq_inv_mul`.  This is exactly the fan-in
cancellation in equation `eq:two-point-function-deep-linear-layer-ell` of
`docs/Renormalization.md`.
-/
theorem layerCovariance_eq_bias_add_weight_mul_normalizedGram
    {A : Type uA} {ι : Type uI} [Fintype ι]
    (p : InitHyperparams) (x : A → ι → ℝ) :
    layerCovariance p x = fun a b =>
      (p.biasVariance : ℝ) + (p.weightVariance : ℝ) * normalizedGram x a b := by
  sorry

namespace DeepLinear

/-- Bias-free Gaussian initialization with unscaled weight variance `Cw`. -/
def hyperparams (Cw : ℝ≥0) : InitHyperparams where
  biasVariance := 0
  weightVariance := Cw

@[simp] theorem hyperparams_biasVariance (Cw : ℝ≥0) : (hyperparams Cw).biasVariance = 0 := rfl

@[simp] theorem hyperparams_weightVariance (Cw : ℝ≥0) :
    (hyperparams Cw).weightVariance = Cw := rfl

end DeepLinear

namespace MLPShape

/-- Put bias-free deep-linear hyperparameters on every layer of a fixed shape. -/
def deepLinearHyperparams {m n : ℕ} : (S : MLPShape m n) → ℝ≥0 → S.Hyperparams
  | .output, Cw => DeepLinear.hyperparams Cw
  | .hidden tail, Cw => (DeepLinear.hyperparams Cw, tail.deepLinearHyperparams Cw)

/-- View a fixed shape as a recursively initialized deep-linear ensemble. -/
def deepLinearEnsemble {m n : ℕ} :
    (S : MLPShape m n) → ℝ≥0 → MLPEnsemble (linear 1) m n
  | .output, Cw => .output (DeepLinear.hyperparams Cw)
  | .hidden tail, Cw => .hidden (DeepLinear.hyperparams Cw) (tail.deepLinearEnsemble Cw)

@[simp] theorem shape_deepLinearEnsemble {m n : ℕ} (S : MLPShape m n) (Cw : ℝ≥0) :
    (S.deepLinearEnsemble Cw).shape = S := by
  induction S with
  | output => rfl
  | hidden tail ih => simp [deepLinearEnsemble, MLPEnsemble.shape, ih]

/-- The hidden widths of a shape, excluding its input and output widths. -/
def hiddenWidths {m n : ℕ} (S : MLPShape m n) : List ℕ :=
  S.widths.tail.dropLast

/-- A shape with `h` equal-width hidden layers. -/
def constantHiddenShape (m n width : ℕ) : (h : ℕ) → MLPShape m n
  | 0 => .output
  | h + 1 => .hidden (constantHiddenShape width n width h)

@[simp] theorem depth_constantHiddenShape (m n width h : ℕ) :
    (constantHiddenShape m n width h).depth = h + 1 := by
  induction h generalizing m with
  | zero => rfl
  | succ h ih => simp [constantHiddenShape, depth, ih, Nat.add_assoc]

/-- The output law on one deterministic input. -/
def deepLinearOutputLaw {m n : ℕ} (S : MLPShape m n) (Cw : ℝ≥0)
    (x : Fin m → ℝ) : Measure (Fin n → ℝ) :=
  Measure.map (fun θ : S.Params => S.eval (linear 1) θ x)
    (S.gaussianInit (S.deepLinearHyperparams Cw))

/-- The output law on a finite or indexed deterministic batch. -/
def deepLinearBatchLaw {A : Type uA} {m n : ℕ} (S : MLPShape m n) (Cw : ℝ≥0)
    (D : A → Fin m → ℝ) : Measure (A → Fin n → ℝ) :=
  (S.paramModel (linear 1) (measurable_linear 1)).outputLaw D
    (S.gaussianInit (S.deepLinearHyperparams Cw))

/-- The one-input output law bundled with its probability certificate. -/
def deepLinearOutputProbabilityMeasure {m n : ℕ} (S : MLPShape m n) (Cw : ℝ≥0)
    (x : Fin m → ℝ) : ProbabilityMeasure (Fin n → ℝ) := by
  refine ⟨S.deepLinearOutputLaw Cw x, ?_⟩
  unfold deepLinearOutputLaw
  apply Measure.isProbabilityMeasure_map
  exact ((S.measurable_eval (measurable_linear 1)).comp
    (measurable_id.prodMk measurable_const)).aemeasurable

/-- Recursive kernel semantics agrees with the explicit batch pushforward.

Informal proof: specialize `MLPEnsemble.outputKernel_apply_eq_outputLaw`, rewrite the recursively
computed shape using `shape_deepLinearEnsemble`, and prove by induction that its hyperparameter
tuple is `deepLinearHyperparams`.  See the kernel composition API documented at
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/Comp.html>.
-/
theorem deepLinearOutputKernel_apply {A : Type uA} {m n : ℕ} (S : MLPShape m n)
    (Cw : ℝ≥0) (D : A → Fin m → ℝ) :
    (S.deepLinearEnsemble Cw).outputKernel (measurable_linear 1) A D =
      S.deepLinearBatchLaw Cw D := by
  sorry

end MLPShape

end NeuralNetwork

end

end
