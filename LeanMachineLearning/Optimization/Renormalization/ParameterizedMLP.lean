/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Network

/-!
# Parameter spaces for fixed MLP architectures

`MLP` is the executable network value.  This file separates a network's shape from its parameters,
making the source's notation `f(x; θ)` literal: `MLPShape.Params S` is the type of `θ` for shape
`S`, and `MLPShape.eval S σ θ x` is the parameterized evaluator.
-/

@[expose] public section

noncomputable section

namespace NeuralNetwork

/-- The shape of a nonempty MLP, without parameter values. -/
inductive MLPShape : ℕ → ℕ → Type where
  | output {m n : ℕ} : MLPShape m n
  | hidden {m n k : ℕ} : MLPShape k n → MLPShape m n

namespace MLPShape

/-- Structured parameter space of a fixed MLP architecture. -/
def Params {m n : ℕ} : MLPShape m n → Type
  | .output => LayerParams (Fin m) (Fin n)
  | .hidden (k := k) tail => LayerParams (Fin m) (Fin k) × tail.Params

/-- Canonical product measurable space on the structured parameters. -/
noncomputable instance instMeasurableSpaceParams {m n : ℕ} (S : MLPShape m n) :
    MeasurableSpace S.Params := by
  induction S with
  | output =>
      simp only [Params]
      infer_instance
  | hidden tail ih =>
      simp only [Params]
      letI : MeasurableSpace tail.Params := ih
      infer_instance

/-- Canonical product topology on the structured parameters. -/
instance instTopologicalSpaceParams {m n : ℕ} (S : MLPShape m n) :
    TopologicalSpace S.Params := by
  induction S with
  | output =>
      simp only [Params]
      infer_instance
  | hidden tail ih =>
      simp only [Params]
      letI : TopologicalSpace tail.Params := ih
      infer_instance

/-- Instantiate executable dense layers from structured parameters. -/
def instantiate {σ : ℝ → ℝ} {m n : ℕ} :
    (S : MLPShape m n) → S.Params → MLP σ m n
  | .output, p => .output (DenseLayer.ofParams p)
  | .hidden tail, p => .hidden (DenseLayer.ofParams p.1) (tail.instantiate p.2)

/-- The parameterized MLP evaluator `f(x; θ)`. -/
def eval {m n : ℕ} (S : MLPShape m n) (σ : ℝ → ℝ)
    (θ : S.Params) (x : Fin m → ℝ) : Fin n → ℝ :=
  (S.instantiate θ : MLP σ m n).eval x

@[simp] theorem eval_output {m n : ℕ} (σ : ℝ → ℝ)
    (θ : (MLPShape.output : MLPShape m n).Params) (x : Fin m → ℝ) :
    eval .output σ θ x = (DenseLayer.ofParams θ).preactivation x := rfl

@[simp] theorem eval_hidden {m n k : ℕ} (tail : MLPShape k n) (σ : ℝ → ℝ)
    (θ : (MLPShape.hidden tail : MLPShape m n).Params) (x : Fin m → ℝ) :
    eval (.hidden tail) σ θ x =
      eval tail σ θ.2 ((DenseLayer.ofParams θ.1).activate σ x) := rfl

/-- Number of independent scalar parameters in the architecture. -/
def paramCount {m n : ℕ} : MLPShape m n → ℕ
  | .output => n * m + n
  | .hidden (m := m) (k := k) tail => k * m + k + tail.paramCount

/-- Input width followed by every layer width. -/
def widths {m n : ℕ} : MLPShape m n → List ℕ
  | .output => [m, n]
  | .hidden (m := m) tail => m :: tail.widths

/-- Depth of the architecture. -/
def depth {m n : ℕ} : MLPShape m n → ℕ
  | .output => 1
  | .hidden tail => tail.depth + 1

-- Measurability of a single affine layer in (parameters, input) form.  The expression
-- `(DenseLayer.ofParams p.1).preactivation p.2` is definitionally `preactivationFromParams`,
-- so this is just `DenseLayer.measurable_preactivation` restated for `Fin m`/`Fin n`.
-- Used as the base case of `measurable_eval`.
private lemma measurable_ofParams_preactivation (m n : ℕ) :
    Measurable
      (fun p : LayerParams (Fin m) (Fin n) × (Fin m → ℝ) =>
        (DenseLayer.ofParams p.1).preactivation p.2) :=
  DenseLayer.measurable_preactivation

-- Measurability of the hidden-layer transition map: pairing the tail parameters with the
-- activated output of the head affine layer is jointly measurable whenever `σ` is.  `A` is
-- any measurable tail parameter type (here `tail.Params`).  Used in the hidden case of
-- `measurable_eval` to thread the induction hypothesis through the first affine layer.
private lemma measurable_activateFromParams_prod (m k : ℕ) {A : Type*} [MeasurableSpace A]
    {σ : ℝ → ℝ} (hσ : Measurable σ) :
    Measurable
      (fun p : (LayerParams (Fin m) (Fin k) × A) × (Fin m → ℝ) =>
        (p.1.2, DenseLayer.activateFromParams σ (p.1.1, p.2))) :=
  (measurable_snd.comp measurable_fst).prodMk
    ((DenseLayer.measurable_activate hσ).comp
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd))

-- Continuity of a single affine layer in (parameters, input) form.  This is the topological
-- analogue of `measurable_ofParams_preactivation`, and is used as the base case of
-- `continuous_eval`.
private lemma continuous_ofParams_preactivation (m n : ℕ) :
    Continuous
      (fun p : LayerParams (Fin m) (Fin n) × (Fin m → ℝ) =>
        (DenseLayer.ofParams p.1).preactivation p.2) :=
  DenseLayer.continuous_preactivation

-- Continuity of the hidden-layer transition map: keep the tail parameters and replace the input by
-- the activated output of the head layer.  This is the topological analogue of
-- `measurable_activateFromParams_prod`.
private lemma continuous_activateFromParams_prod (m k : ℕ) {A : Type*} [TopologicalSpace A]
    {σ : ℝ → ℝ} (hσ : Continuous σ) :
    Continuous
      (fun p : (LayerParams (Fin m) (Fin k) × A) × (Fin m → ℝ) =>
        (p.1.2, DenseLayer.activateFromParams σ (p.1.1, p.2))) :=
  (continuous_snd.comp continuous_fst).prodMk
    ((DenseLayer.continuous_activate hσ).comp
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd))

/-- Joint measurability in all parameters and the input.

Informal proof: induction over the shape.  A single affine layer is jointly measurable by
`DenseLayer.measurable_preactivation`.  At a hidden constructor, jointly evaluate the first affine
layer, compose coordinatewise with measurable `σ`, and apply the induction hypothesis to the tail
parameters and resulting activation.  This is exactly the recursion in Chapter 2.  See Mathlib's
finite-product measurable-space API:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/Pi.html>. -/
theorem measurable_eval {m n : ℕ} (S : MLPShape m n) {σ : ℝ → ℝ} (hσ : Measurable σ) :
    Measurable (fun p : S.Params × (Fin m → ℝ) => S.eval σ p.1 p.2) := by
  induction S with
  | output =>
      rename_i m₀ n₀
      exact measurable_ofParams_preactivation m₀ n₀
  | hidden tail ih =>
      rename_i m₀ n₀ k
      exact ih.comp (measurable_activateFromParams_prod m₀ k hσ)

/-- Joint continuity in all parameters and the input.

Informal proof: the same structural induction as `measurable_eval`, using the continuous affine
and activation composition lemmas instead.  See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/ContinuousMap/Basic.html>. -/
theorem continuous_eval {m n : ℕ} (S : MLPShape m n) {σ : ℝ → ℝ} (hσ : Continuous σ) :
    Continuous (fun p : S.Params × (Fin m → ℝ) => S.eval σ p.1 p.2) := by
  induction S with
  | output =>
      rename_i m₀ n₀
      exact continuous_ofParams_preactivation m₀ n₀
  | hidden tail ih =>
      rename_i m₀ n₀ k
      exact ih.comp (continuous_activateFromParams_prod m₀ k hσ)

end MLPShape

end NeuralNetwork

end

end
