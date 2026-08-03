/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Activation
public import Mathlib.Data.Matrix.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Finite dense layers and typed multilayer perceptrons

The core representation uses arbitrary finite index types.  Consequently, layer shapes are checked
by Lean's type system, while `Fin n` remains available for the usual width-based presentation.
The output layer is affine; the activation is applied only after hidden layers.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace NeuralNetwork

universe u v

/-- A finite or indexed dataset whose samples have coordinates indexed by `ι`.  Keeping the sample
index type explicit prevents the sample and feature axes from being transposed accidentally. -/
abbrev Dataset (A : Type v) (ι : Type u) := A → ι → ℝ

/-- Parameters of an affine map from coordinates `ι` to coordinates `κ`. -/
structure DenseLayer (ι κ : Type*) where
  /-- Matrix of affine weights, indexed by output and then input coordinates. -/
  weight : Matrix κ ι ℝ
  /-- Additive bias at each output coordinate. -/
  bias : κ → ℝ

/-- The raw product representation is useful for product measures and joint regularity statements.
Writing the weight array as an iterated function, rather than through the opaque `Matrix` synonym,
lets Lean use the canonical finite-product measurable space without a competing instance. -/
abbrev LayerParams (ι κ : Type*) := (κ → ι → ℝ) × (κ → ℝ)

namespace DenseLayer

variable {ι κ : Type*}

/-- Convert product-form parameters to a dense layer. -/
def ofParams (p : LayerParams ι κ) : DenseLayer ι κ := ⟨p.1, p.2⟩

/-- Convert a dense layer to its product-form parameters. -/
def toParams (L : DenseLayer ι κ) : LayerParams ι κ := (L.weight, L.bias)

@[simp] theorem ofParams_toParams (L : DenseLayer ι κ) : ofParams L.toParams = L := by
  cases L
  rfl

@[simp] theorem toParams_ofParams (p : LayerParams ι κ) : (ofParams p).toParams = p := rfl

/-- Affine preactivation `W x + b`. -/
def preactivation [Fintype ι] (L : DenseLayer ι κ) (x : ι → ℝ) : κ → ℝ :=
  L.weight.mulVec x + L.bias

/-- Apply a scalar activation coordinatewise after the affine map. -/
def activate [Fintype ι] (σ : ℝ → ℝ) (L : DenseLayer ι κ) (x : ι → ℝ) : κ → ℝ :=
  σ ∘ L.preactivation x

@[simp] theorem preactivation_apply [Fintype ι] (L : DenseLayer ι κ) (x : ι → ℝ)
    (j : κ) : L.preactivation x j = L.bias j + ∑ i, L.weight j i * x i := by
  change (∑ i, L.weight j i * x i) + L.bias j = _
  rw [add_comm]

@[simp] theorem activate_apply [Fintype ι] (σ : ℝ → ℝ) (L : DenseLayer ι κ)
    (x : ι → ℝ) (j : κ) : L.activate σ x j = σ (L.preactivation x j) := rfl

/-- Joint affine evaluation in product-form parameters and inputs. -/
def preactivationFromParams [Fintype ι] (p : LayerParams ι κ × (ι → ℝ)) : κ → ℝ :=
  (ofParams p.1).preactivation p.2

theorem continuous_preactivation [Fintype ι] :
    Continuous (preactivationFromParams : LayerParams ι κ × (ι → ℝ) → κ → ℝ) := by
  unfold preactivationFromParams preactivation ofParams Matrix.mulVec
  fun_prop

theorem measurable_preactivation [Fintype ι] [Finite κ] :
    Measurable (preactivationFromParams : LayerParams ι κ × (ι → ℝ) → κ → ℝ) :=
  let _ := Fintype.ofFinite κ
  continuous_preactivation.measurable

/-- Joint activated evaluation in product-form parameters and inputs. -/
def activateFromParams [Fintype ι] (σ : ℝ → ℝ)
    (p : LayerParams ι κ × (ι → ℝ)) : κ → ℝ :=
  σ ∘ preactivationFromParams p

theorem continuous_activate [Fintype ι] {σ : ℝ → ℝ} (hσ : Continuous σ) :
    Continuous (activateFromParams σ : LayerParams ι κ × (ι → ℝ) → κ → ℝ) := by
  change Continuous (fun p j => σ (preactivationFromParams p j))
  exact continuous_pi fun j => hσ.comp ((continuous_apply j).comp continuous_preactivation)

theorem measurable_activate [Fintype ι] [Finite κ] {σ : ℝ → ℝ} (hσ : Measurable σ) :
    Measurable (activateFromParams σ : LayerParams ι κ × (ι → ℝ) → κ → ℝ) := by
  let _ := Fintype.ofFinite κ
  change Measurable (fun p j => σ (preactivationFromParams p j))
  exact measurable_pi_lambda _ fun j =>
    hσ.comp ((measurable_pi_apply j).comp measurable_preactivation)

theorem continuous_preactivation_fixed [Fintype ι] (L : DenseLayer ι κ) :
    Continuous L.preactivation := by
  unfold preactivation Matrix.mulVec
  fun_prop

theorem measurable_preactivation_fixed [Fintype ι] [Finite κ] (L : DenseLayer ι κ) :
    Measurable L.preactivation := by
  let _ := Fintype.ofFinite κ
  exact L.continuous_preactivation_fixed.measurable

theorem continuous_activate_fixed [Fintype ι] (L : DenseLayer ι κ)
    {σ : ℝ → ℝ} (hσ : Continuous σ) : Continuous (L.activate σ) := by
  change Continuous (fun x j => σ (L.preactivation x j))
  exact continuous_pi fun j => hσ.comp ((continuous_apply j).comp L.continuous_preactivation_fixed)

theorem measurable_activate_fixed [Fintype ι] [Finite κ] (L : DenseLayer ι κ)
    {σ : ℝ → ℝ} (hσ : Measurable σ) : Measurable (L.activate σ) := by
  let _ := Fintype.ofFinite κ
  change Measurable (fun x j => σ (L.preactivation x j))
  exact measurable_pi_lambda _ fun j =>
    hσ.comp ((measurable_pi_apply j).comp L.measurable_preactivation_fixed)

/-- Number of scalar weights and biases in a dense layer. -/
def paramCount [Fintype ι] [Fintype κ] (_L : DenseLayer ι κ) : ℕ :=
  Fintype.card κ * Fintype.card ι + Fintype.card κ

theorem preactivation_eq_of_row_eq [Fintype ι] (L : DenseLayer ι κ) {j j' : κ}
    (hW : L.weight j = L.weight j') (hb : L.bias j = L.bias j') (x : ι → ℝ) :
    L.preactivation x j = L.preactivation x j' := by
  simp only [preactivation_apply, hb]
  rw [hW]

theorem preactivation_zero_eq [Fintype ι] (x : ι → ℝ) (j j' : κ) :
    (DenseLayer.mk (0 : Matrix κ ι ℝ) 0).preactivation x j =
      (DenseLayer.mk (0 : Matrix κ ι ℝ) 0).preactivation x j' := by
  simp

/-- A threshold neuron fires exactly when its weighted evidence exceeds the negative bias, as
stated in the source. -/
theorem activate_threshold_eq_one_iff [Fintype ι] (L : DenseLayer ι κ)
    (x : ι → ℝ) (j : κ) :
    L.activate threshold x j = 1 ↔ -L.bias j ≤ ∑ i, L.weight j i * x i := by
  simp only [activate_apply, threshold, preactivation_apply]
  by_cases h : 0 ≤ L.bias j + ∑ i, L.weight j i * x i <;> simp [h] <;> linarith

/-- The complementary non-firing criterion for a threshold neuron. -/
theorem activate_threshold_eq_zero_iff [Fintype ι] (L : DenseLayer ι κ)
    (x : ι → ℝ) (j : κ) :
    L.activate threshold x j = 0 ↔ ∑ i, L.weight j i * x i < -L.bias j := by
  simp only [activate_apply, threshold]
  split_ifs with h
  · simp only [one_ne_zero, false_iff]
    rw [preactivation_apply] at h
    linarith
  · simp only [true_iff]
    rw [preactivation_apply] at h
    linarith

end DenseLayer

/-- A nonempty, shape-safe sequence of dense layers with numerical widths.
`DenseLayer` itself remains polymorphic over arbitrary finite index types; this
specialization gives MLPs a concise width-indexed public interface. -/
inductive MLP (σ : ℝ → ℝ) : ℕ → ℕ → Type where
  | output {m n : ℕ} : DenseLayer (Fin m) (Fin n) → MLP σ m n
  | hidden {m n k : ℕ} : DenseLayer (Fin m) (Fin k) → MLP σ k n → MLP σ m n

namespace MLP

/-- Evaluate a typed MLP. -/
def eval {σ : ℝ → ℝ} {m n : ℕ} : MLP σ m n → (Fin m → ℝ) → (Fin n → ℝ)
  | .output L => L.preactivation
  | .hidden L N => fun x => N.eval (L.activate σ x)

@[simp] theorem eval_output {σ : ℝ → ℝ} {m n : ℕ} (L : DenseLayer (Fin m) (Fin n)) :
    (MLP.output L : MLP σ m n).eval = L.preactivation := rfl

@[simp] theorem eval_hidden {σ : ℝ → ℝ} {m n k : ℕ}
    (L : DenseLayer (Fin m) (Fin k)) (N : MLP σ k n) (x : Fin m → ℝ) :
    (MLP.hidden L N).eval x = N.eval (L.activate σ x) := rfl

theorem continuous_eval {σ : ℝ → ℝ} {m n : ℕ} (N : MLP σ m n) (hσ : Continuous σ) :
    Continuous N.eval := by
  induction N with
  | output L => exact L.continuous_preactivation_fixed
  | hidden L N ih => exact ih.comp (L.continuous_activate_fixed hσ)

theorem measurable_eval {σ : ℝ → ℝ} {m n : ℕ} (N : MLP σ m n) (hσ : Measurable σ) :
    Measurable N.eval := by
  induction N with
  | output L => exact L.measurable_preactivation_fixed
  | hidden L N ih => exact ih.comp (L.measurable_activate_fixed hσ)

/-- Total number of scalar parameters in an MLP. -/
def paramCount {σ : ℝ → ℝ} {m n : ℕ} : MLP σ m n → ℕ
  | .output L => L.paramCount
  | .hidden L N => L.paramCount + N.paramCount

/-- Number of affine layers in an MLP. -/
def depth {σ : ℝ → ℝ} {m n : ℕ} : MLP σ m n → ℕ
  | .output _ => 1
  | .hidden _ N => N.depth + 1

/-- The input width followed by every successive layer width. -/
def widths {σ : ℝ → ℝ} {m n : ℕ} : MLP σ m n → List ℕ
  | .output _ => [m, n]
  | .hidden _ N => m :: N.widths

@[simp] theorem widths_length {σ : ℝ → ℝ} {m n : ℕ} (N : MLP σ m n) :
    N.widths.length = N.depth + 1 := by
  induction N with
  | output L => simp [widths, depth]
  | hidden L N ih => simp [widths, depth, ih, Nat.add_comm]

/-- The source's convention that depth is one less than the number of listed widths. -/
theorem depth_eq_widths_length_sub_one {σ : ℝ → ℝ} {m n : ℕ} (N : MLP σ m n) :
    N.depth = N.widths.length - 1 := by
  rw [N.widths_length]
  omega

/-- Parameter count computed directly from a nonempty list of widths. -/
def paramCountFromWidths : List ℕ → ℕ
  | a :: b :: rest => b * a + b + paramCountFromWidths (b :: rest)
  | _ => 0
termination_by widths => widths.length

theorem paramCount_eq_paramCountFromWidths {σ : ℝ → ℝ} {m n : ℕ} (N : MLP σ m n) :
    N.paramCount = paramCountFromWidths N.widths := by
  induction N with
  | output L => simp [paramCount, widths, paramCountFromWidths, DenseLayer.paramCount]
  | hidden L N ih =>
      cases N with
      | output L' =>
          simp [paramCount, widths, paramCountFromWidths, DenseLayer.paramCount]
      | hidden L' N' =>
          simp [paramCount, widths, paramCountFromWidths, DenseLayer.paramCount] at ih ⊢
          omega

/-- Evaluate on a finite collection of inputs while keeping sample and neuron indices separate. -/
def evalBatch {σ : ℝ → ℝ} {m n : ℕ} {A : Type v}
    (N : MLP σ m n) (D : Dataset A (Fin m)) : A → Fin n → ℝ :=
  fun a => N.eval (D a)

@[simp] theorem evalBatch_apply {σ : ℝ → ℝ} {m n : ℕ} {A : Type v}
    (N : MLP σ m n) (D : A → Fin m → ℝ) (a : A) :
    N.evalBatch D a = N.eval (D a) := rfl

end MLP

/-- The source's `(4,5,5,5,1)` architecture, used as a checked parameter-count example. -/
def exampleMLP45551 (σ : ℝ → ℝ) : MLP σ 4 1 :=
  .hidden (⟨0, 0⟩ : DenseLayer (Fin 4) (Fin 5)) <|
    .hidden (⟨0, 0⟩ : DenseLayer (Fin 5) (Fin 5)) <|
      .hidden (⟨0, 0⟩ : DenseLayer (Fin 5) (Fin 5)) <|
        .output (⟨0, 0⟩ : DenseLayer (Fin 5) (Fin 1))

example (σ : ℝ → ℝ) : (exampleMLP45551 σ).paramCount = 91 := by
  norm_num [exampleMLP45551, MLP.paramCount, DenseLayer.paramCount]

end NeuralNetwork

end

end
