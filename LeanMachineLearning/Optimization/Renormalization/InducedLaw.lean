/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Initialization
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Moments.Variance

/-!
# Induced laws and randomized neural-network layers

The primary semantics is a pushforward measure.  Kernel-valued randomized maps then make
independently initialized layers compositional without using formal products of Dirac deltas.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory ComplexConjugate

namespace NeuralNetwork

universe uΘ uX uY uA uB

variable {A : Type uA} {E S : Type uB} {ι : Type uX} {κ : Type uY}

/-- An architecture-independent model whose evaluator is jointly measurable in parameters and
input. -/
structure ParamModel (Θ : Type uΘ) (X : Type uX) (Y : Type uY)
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Y] where
  /-- Evaluate parameters `θ : Θ` at an input `x : X`. -/
  eval : Θ → X → Y
  /-- Joint measurability of evaluation in the parameter and input variables. -/
  measurable_eval : Measurable fun p : Θ × X => eval p.1 p.2

namespace ParamModel

variable {Θ : Type uΘ} {X : Type uX} {Y : Type uY}
  [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Y]

/-- Evaluate one parameter value on every entry of a dataset. -/
def evalBatch (F : ParamModel Θ X Y) (D : A → X) (θ : Θ) : A → Y :=
  fun a => F.eval θ (D a)

theorem measurable_eval_fixed (F : ParamModel Θ X Y) (x : X) :
    Measurable fun θ => F.eval θ x := by
  exact F.measurable_eval.comp (measurable_id.prodMk measurable_const)

theorem measurable_evalBatch (F : ParamModel Θ X Y) (D : A → X) :
    Measurable (F.evalBatch D) := by
  exact measurable_pi_lambda _ fun a => F.measurable_eval_fixed (D a)

/-- Distribution of the finite-dataset outputs induced by a parameter law. -/
def outputLaw (F : ParamModel Θ X Y) (D : A → X) (μ : Measure Θ) : Measure (A → Y) :=
  μ.map (F.evalBatch D)

/-- A measurable pushforward of a probability measure is a probability measure.

Informal proof: evaluate `μ.map (F.evalBatch D)` on the whole space; measurability of the batched
evaluator turns the preimage of `univ` into `univ`, whose mass is one. See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Map.html>. -/
instance instIsProbabilityMeasureOutputLaw (F : ParamModel Θ X Y) (D : A → X)
    (μ : Measure Θ) [IsProbabilityMeasure μ] : IsProbabilityMeasure (F.outputLaw D μ) := by
  unfold outputLaw
  exact μ.isProbabilityMeasure_map (F.measurable_evalBatch D).aemeasurable

/-- Observable formula for the induced output law.

Informal proof: unfold `outputLaw` and apply `MeasureTheory.integral_map` using
`measurable_evalBatch`; the strong-measurability hypothesis is exactly the remaining premise.
See <https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner/Basic.html>. -/
theorem integral_outputLaw [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ParamModel Θ X Y) (D : A → X) (μ : Measure Θ) (G : (A → Y) → E)
    (hG : AEStronglyMeasurable G (F.outputLaw D μ)) :
    ∫ y, G y ∂F.outputLaw D μ = ∫ θ, G (F.evalBatch D θ) ∂μ := by
  unfold outputLaw at hG ⊢
  exact integral_map (F.measurable_evalBatch D).aemeasurable hG

/-- Conditional output kernel at fixed parameters, with datasets as inputs. -/
def deterministicOutputKernel (F : ParamModel Θ X Y) (θ : Θ) : Kernel (A → X) (A → Y) :=
  Kernel.deterministic (fun D a => F.eval θ (D a)) <| by
    exact measurable_pi_lambda _ fun a =>
      F.measurable_eval.comp (measurable_const.prodMk (measurable_pi_apply a))

/-- Deterministic conditional-output kernel with the parameter as kernel input and the dataset
fixed.  This orientation is the one composed with a parameter measure. -/
def parameterOutputKernel (F : ParamModel Θ X Y) (D : A → X) : Kernel Θ (A → Y) :=
  Kernel.deterministic (F.evalBatch D) (F.measurable_evalBatch D)

/-- Integrating deterministic conditional outputs against the parameter law is the output
pushforward. -/
theorem parameterOutputKernel_comp_eq_outputLaw (F : ParamModel Θ X Y) (D : A → X)
    (μ : Measure Θ) : F.parameterOutputKernel D ∘ₘ μ = F.outputLaw D μ := by
  unfold parameterOutputKernel outputLaw
  exact Measure.deterministic_comp_eq_map (F.measurable_evalBatch D)

@[simp] theorem deterministicOutputKernel_apply (F : ParamModel Θ X Y) (θ : Θ)
    (D : A → X) : F.deterministicOutputKernel θ D = Measure.dirac (F.evalBatch D θ) := by
  rw [deterministicOutputKernel, Kernel.deterministic_apply]
  rfl

end ParamModel

/-- Discoverability wrapper for Bochner integration against a Dirac measure. -/
theorem integral_dirac_apply [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace S] [MeasurableSingletonClass S] (f : S → E) (s : S) :
    ∫ x, f x ∂Measure.dirac s = f s := by
  exact integral_dirac f s

/-- The identity random variable has zero variance under a point mass. -/
theorem variance_id_dirac (s : ℝ) : Var[id; Measure.dirac s] = 0 := by
  exact variance_dirac s

/-- Characteristic function of a deterministic real law. -/
theorem charFun_dirac (s t : ℝ) :
    charFun (Measure.dirac s) t = Complex.exp ((t * s : ℂ) * Complex.I) := by
  rw [MeasureTheory.charFun_dirac]
  congr 2
  simp [mul_comm]

/-- A randomized measurable map, represented as a Markov kernel.  The same random parameter is
used throughout one evaluation. -/
def randomMapKernel {Θ : Type uΘ} {X : Type uX} {Y : Type uY}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure Θ) (F : Θ → X → Y)
    (_hF : Measurable fun p : Θ × X => F p.1 p.2) : Kernel X Y :=
  (Kernel.id ×ₖ Kernel.const X ν).map fun p : X × Θ => F p.2 p.1

/-- Pointwise description of `randomMapKernel`.

Informal proof: `Kernel.prod_apply` turns `Kernel.id ×ₖ Kernel.const` into
`dirac x × ν`; mapping `(x,θ) ↦ F θ x` and integrating out the Dirac coordinate leaves
`ν.map (fun θ ↦ F θ x)`.  See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/Prod.html>. -/
theorem randomMapKernel_apply {Θ : Type uΘ} {X : Type uX} {Y : Type uY}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (F : Θ → X → Y)
    (hF : Measurable fun p : Θ × X => F p.1 p.2) (x : X) :
    randomMapKernel ν F hF x = ν.map fun θ => F θ x := by
  have hswap : Measurable (fun p : X × Θ => F p.2 p.1) := hF.comp measurable_swap
  rw [randomMapKernel, Kernel.map_apply _ hswap, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map hswap measurable_prodMk_left]
  rfl

/-- Batched affine preactivation, with sample and neuron indices kept separate. -/
def batchPreactivation [Fintype ι] (q : LayerParams ι κ)
    (s : A → ι → ℝ) : A → κ → ℝ :=
  fun a => (DenseLayer.ofParams q).preactivation (s a)

/-- Batched affine evaluation is jointly measurable in parameters and inputs.

Informal proof: each output coordinate is a bias projection plus a finite sum of products of
measurable coordinate projections. Measurability of a function into a finite product is equivalent
to measurability of every coordinate. See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Constructions.html>. -/
theorem measurable_batchPreactivation [Fintype ι] [Finite κ] :
    Measurable (fun p : LayerParams ι κ × (A → ι → ℝ) =>
      batchPreactivation p.1 p.2) := by
  letI := Fintype.ofFinite κ
  exact measurable_pi_lambda _ fun a => DenseLayer.measurable_preactivation.comp
    (measurable_fst.prodMk ((measurable_pi_apply a).comp measurable_snd))

/-- Covariance across samples for one initialized output neuron. -/
def layerCovariance (p : InitHyperparams) (s : A → ι → ℝ) [Fintype ι] : Matrix A A ℝ :=
  fun a a' => p.biasVariance + scaledWeightVariance p ι * ∑ i, s a i * s a' i

/-- The layer covariance is positive semidefinite.

Informal proof: for a coefficient vector `v`, expand its quadratic form as
`C_b (∑ a, v a)^2 + (C_W / |ι|) ∑ i, (∑ a, v a * s a i)^2`.  Both coefficients are nonnegative
and every square is nonnegative.  The covariance is symmetric by commutativity.  This is the Gram
matrix argument described at <https://en.wikipedia.org/wiki/Gram_matrix#Positive-semidefiniteness>. -/
theorem layerCovariance_posSemidef [Fintype ι]
    (p : InitHyperparams) (s : A → ι → ℝ) : (layerCovariance p s).PosSemidef := by
  sorry

/-- Convert one neuron's raw sample vector to Mathlib's Euclidean representation. -/
def batchToEuclidean (z : A → κ → ℝ) (j : κ) : EuclideanSpace ℝ A :=
  (EuclideanSpace.equiv A ℝ).symm fun a => z a j

/-- Exact joint law of all batched preactivations in one initialized layer.

Informal proof: for fixed `j`, the batch is an affine linear image of the centered jointly Gaussian
bias and weight row.  Its mean is zero and its covariance is `layerCovariance p s` by the coordinate
moment lemmas.  Different `j` use disjoint independent parameter rows, so
`iIndepFun.map_fun_eq_pi_map` identifies the joint law with the finite product shown below.  See
Mathlib's multivariate Gaussian construction:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Gaussian/Multivariate.html>. -/
theorem map_evalBatch_layerGaussianInit [Fintype ι] [Fintype κ] [Fintype A] [DecidableEq A]
    (p : InitHyperparams) (s : A → ι → ℝ) :
    Measure.map (fun q : LayerParams ι κ => fun j => batchToEuclidean (batchPreactivation q s) j)
        (layerGaussianInit p ι κ) =
      Measure.pi (fun _ : κ => multivariateGaussian 0 (layerCovariance p s)) := by
  sorry

/-- Randomized dense-layer kernel under independent Gaussian initialization. -/
def randomLayerKernel [Fintype ι] [Fintype κ] (p : InitHyperparams) :
    Kernel (A → ι → ℝ) (A → κ → ℝ) :=
  randomMapKernel (layerGaussianInit p ι κ) batchPreactivation measurable_batchPreactivation

/-- A shape-safe list of independently initialized layer laws. -/
inductive MLPEnsemble (σ : ℝ → ℝ) : ℕ → ℕ → Type where
  | output {m n : ℕ} : InitHyperparams → MLPEnsemble σ m n
  | hidden {m n k : ℕ} : InitHyperparams → MLPEnsemble σ k n → MLPEnsemble σ m n

namespace MLPEnsemble

/-- Kernel semantics of an independently initialized MLP on a shared finite batch.

Informal construction: an output node is `randomLayerKernel`.  At a hidden node, compose its
random affine kernel, the deterministic coordinatewise activation kernel, and the recursively
constructed tail.  Kernel composition integrates over the fresh parameter law at each layer,
which is exactly independent initialization.  See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/Comp.html>. -/
def outputKernel {σ : ℝ → ℝ} (hσ : Measurable σ) {m n : ℕ} (N : MLPEnsemble σ m n)
    (A : Type uA) : Kernel (A → Fin m → ℝ) (A → Fin n → ℝ) := by
  sorry

end MLPEnsemble

end NeuralNetwork

end

end
