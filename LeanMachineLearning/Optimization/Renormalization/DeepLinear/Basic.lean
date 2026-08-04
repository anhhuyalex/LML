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

/-- A rank-one Gram kernel `a, b ↦ y a * y b`. -/
private def rankOneGram {A : Type uA} (y : A → ℝ) : Matrix A A ℝ :=
  fun a b => y a * y b

/-- A rank-one Gram kernel is positive semidefinite. -/
private theorem rankOneGram_posSemidef {A : Type uA} (y : A → ℝ) :
    Matrix.PosSemidef (rankOneGram y) := by
  refine ⟨?_, ?_⟩
  · ext a b
    simp [rankOneGram, mul_comm]
  · intro v
    simpa [rankOneGram, Finsupp.sum, Finset.sum_mul, Finset.mul_sum, star_trivial] using
      mul_self_nonneg (v.sum fun a va => va * y a)

-- A sum of rank-one Gram kernels `a, b ↦ y i a * y i b` is positive semidefinite:
-- each summand is by `rankOneGram_posSemidef`, and positivity survives finite sums.
private theorem sum_rankOneGram_posSemidef {A : Type uA} {ι : Type uI} [Fintype ι]
    (y : ι → A → ℝ) : Matrix.PosSemidef (∑ i, rankOneGram (y i)) :=
  Matrix.posSemidef_sum Finset.univ (fun i _ => rankOneGram_posSemidef (y i))

-- The normalized Gram matrix is exactly the sum of rank-one Gram kernels, scaled by the
-- reciprocal of the input dimension `|ι|`.
private theorem normalizedGram_eq_sum_rankOneGram {A : Type uA} {ι : Type uI} [Fintype ι]
    (x : A → ι → ℝ) :
    normalizedGram x = (Fintype.card ι : ℝ)⁻¹ • (∑ i, rankOneGram (fun a => x a i)) := by
  ext a b
  simp [normalizedGram, rankOneGram, Matrix.sum_apply]

/-- The normalized Gram matrix is positive semidefinite.

Informal proof: expand the quadratic form and interchange the two finite sums.  It becomes
`|ι|⁻¹ * ∑ i, (∑ a, v a * x a i)^2`, a nonnegative scalar times a sum of squares.  This is the
standard Gram-matrix proof; see <https://en.wikipedia.org/wiki/Gram_matrix#Positive-semidefiniteness>.
-/
theorem normalizedGram_posSemidef {A : Type uA} {ι : Type uI} [Fintype ι]
    (x : A → ι → ℝ) : (normalizedGram x).PosSemidef :=
  (normalizedGram_eq_sum_rankOneGram x) ▸
    (sum_rankOneGram_posSemidef (fun i a => x a i)).smul (inv_nonneg.mpr (Nat.cast_nonneg _))

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
  ext a b
  simp only [layerCovariance, normalizedGram, scaledWeightVariance, NNReal.coe_div,
    NNReal.coe_natCast]
  ring

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

/-- Casting a pair along a type equality in its second coordinate preserves the first
coordinate. -/
private lemma cast_congrArg_prod {A : Type*} {B C : Type uA} (h : B = C) (a : A) (b : B) :
    cast (congrArg (fun T : Type uA => A × T) h) (a, b) = (a, cast h b) := by
  cases h
  rfl

/-- The recursively accumulated hyperparameter tuple agrees with the shape-wise one.

The two sides live in the dependent types `(S.deepLinearEnsemble Cw).shape.Hyperparams` and
`S.Hyperparams`, which are equal only along `shape_deepLinearEnsemble`, so the statement uses
heterogeneous equality. -/
@[simp] theorem deepLinearEnsemble_hyperparams {m n : ℕ} (S : MLPShape m n) (Cw : ℝ≥0) :
    HEq (S.deepLinearEnsemble Cw).hyperparams (S.deepLinearHyperparams Cw) := by
  induction S with
  | output => rfl
  | hidden tail ih =>
      -- Both tuples start with `DeepLinear.hyperparams Cw`; the recursive `HEq` in `ih`
      -- transports the tail hyperparameters back and rebuilds the pair.
      rcases heq_iff_exists_eq_cast.mp ih with ⟨hT, hx⟩
      refine heq_of_eq_cast ?e ?h
      · exact congrArg (fun T : Type => InitHyperparams × T) hT
      · exact (congrArg (fun z => (DeepLinear.hyperparams Cw, z)) hx).trans
          (cast_congrArg_prod hT (DeepLinear.hyperparams Cw)
            (tail.deepLinearHyperparams Cw)).symm

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
  unfold deepLinearBatchLaw
  rw [MLPEnsemble.outputKernel_apply_eq_outputLaw]
  conv_rhs => rw [← shape_deepLinearEnsemble S Cw]
  -- Both sides now evaluate the same shape `(S.deepLinearEnsemble Cw).shape`; the only
  -- remaining differences are the measurability proof and the hyperparameter tuple.
  congr 1
  · -- the Gaussian measures agree: the ensemble hyperparameters equal `deepLinearHyperparams`
    congr 1
    exact heq_iff_eq.mp
      (HEq.trans (deepLinearEnsemble_hyperparams S Cw)
        (HEq.symm (Mathlib.Tactic.DepRewrite.hdcongrArg (shape_deepLinearEnsemble S Cw)
          (fun T _ => deepLinearHyperparams T Cw))))

end MLPShape

end NeuralNetwork

end

end
