/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.ParameterizedMLP
public import LeanMachineLearning.Optimization.Renormalization.Learning

/-!
# Neuron-permutation symmetry and zero-initialization collapse

This file separates three claims that are often conflated:

1. relabeling a hidden layer and inversely relabeling the following layer does not change the
   represented function;
2. identical neurons produce an all-equal hidden representation; and
3. an equivariant update preserves parameters fixed by the symmetry.

The third statement is deliberately optimizer-agnostic.  Applying it to gradient descent requires
an invariant loss and a proof that the resulting update is equivariant.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace NeuralNetwork

universe u

/-- A coordinate vector is collapsed when every pair of coordinates agrees. -/
def AllCoordinatesEqual {ι : Type u} (x : ι → ℝ) : Prop := ∀ i j, x i = x j

/-- Relabel coordinates by an equivalence. -/
def permuteCoordinates {ι κ : Type*} (e : ι ≃ κ) (x : ι → ℝ) : κ → ℝ :=
  fun j => x (e.symm j)

namespace DenseLayer

variable {ι κ κ' : Type*}

/-- Relabel the output neurons of a dense layer. -/
def permuteOutput (e : κ ≃ κ') (L : DenseLayer ι κ) : DenseLayer ι κ' where
  weight j i := L.weight (e.symm j) i
  bias j := L.bias (e.symm j)

/-- Relabel the input coordinates of a dense layer. -/
def permuteInput (e : ι ≃ κ) (L : DenseLayer ι κ') : DenseLayer κ κ' where
  weight j i := L.weight j (e.symm i)
  bias := L.bias

@[simp] theorem preactivation_permuteOutput [Fintype ι] (e : κ ≃ κ')
    (L : DenseLayer ι κ) (x : ι → ℝ) :
    (L.permuteOutput e).preactivation x = permuteCoordinates e (L.preactivation x) := by
  funext j
  rfl

/-- Inversely relabeling the inputs of a dense layer cancels a coordinate relabeling.

Informal proof: expand the matrix-vector product and reindex the finite sum by `e`; bijectivity
ensures that every old input coordinate occurs exactly once.  This is the standard change-of-index
identity for a finite sum; see Mathlib's `Equiv.sum_comp` documentation at
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Group/Finset/Basic.html>.
-/
theorem preactivation_permuteInput [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (L : DenseLayer ι κ') (x : ι → ℝ) :
    (L.permuteInput e).preactivation (permuteCoordinates e x) = L.preactivation x := by
  funext j
  simp only [preactivation_apply, permuteInput, permuteCoordinates]
  congr 1
  exact Equiv.sum_comp e.symm (fun i => L.weight j i * x i)

/-- All output neurons of a layer have the same affine parameters. -/
def IdenticalNeurons (L : DenseLayer ι κ) : Prop :=
  ∀ j j', L.weight j = L.weight j' ∧ L.bias j = L.bias j'

theorem IdenticalNeurons.preactivation [Fintype ι] {L : DenseLayer ι κ}
    (hL : L.IdenticalNeurons) (x : ι → ℝ) : AllCoordinatesEqual (L.preactivation x) := by
  intro j j'
  exact L.preactivation_eq_of_row_eq (hL j j').1 (hL j j').2 x

theorem IdenticalNeurons.activate [Fintype ι] {L : DenseLayer ι κ}
    (hL : L.IdenticalNeurons) (σ : ℝ → ℝ) (x : ι → ℝ) :
    AllCoordinatesEqual (L.activate σ x) := by
  intro j j'
  simp only [activate_apply]
  rw [hL.preactivation x j j']

/-- Collapse a layer's input axis to one coordinate by summing every weight row. -/
def collapseInputToOne [Fintype ι] (L : DenseLayer ι κ) : DenseLayer (Fin 1) κ where
  weight j _ := ∑ i, L.weight j i
  bias := L.bias

/-- If all input coordinates agree, a dense layer is exactly equivalent to a one-input layer.
Thus a collapsed width supplies no independent hidden features; its only remaining effect is the
sum of the outgoing weights. -/
theorem preactivation_eq_collapseInputToOne [Fintype ι] [Nonempty ι]
    (L : DenseLayer ι κ) (x : ι → ℝ) (hx : AllCoordinatesEqual x) :
    L.preactivation x =
      (L.collapseInputToOne).preactivation (fun _ : Fin 1 => x (Classical.choice inferInstance)) := by
  let i₀ : ι := Classical.choice inferInstance
  funext j
  simp only [preactivation_apply, collapseInputToOne]
  have hxi : ∀ i, x i = x i₀ := fun i => hx i i₀
  simp_rw [hxi]
  simp [Finset.sum_mul]

theorem identicalNeurons_zero [Fintype ι] [Fintype κ] :
    (DenseLayer.mk (0 : Matrix κ ι ℝ) 0).IdenticalNeurons := by
  intro j j'
  constructor
  · funext i
    simp
  · simp

end DenseLayer

namespace MLP

/-- Relabel only the input coordinates of the first affine layer. -/
def permuteInput {σ : ℝ → ℝ} {m m' n : ℕ} (e : Fin m ≃ Fin m') :
    MLP σ m n → MLP σ m' n
  | .output L => .output (L.permuteInput e)
  | .hidden L N => .hidden (L.permuteInput e) N

theorem eval_permuteInput {σ : ℝ → ℝ} {m m' n : ℕ} (e : Fin m ≃ Fin m')
    (N : MLP σ m n) (x : Fin m → ℝ) :
    (N.permuteInput e).eval (permuteCoordinates e x) = N.eval x := by
  cases N with
  | output L => exact L.preactivation_permuteInput e x
  | hidden L N =>
      simp only [permuteInput, eval_hidden]
      apply congrArg N.eval
      funext j
      simp only [DenseLayer.activate_apply]
      rw [L.preactivation_permuteInput e x]

/-- Relabel one hidden layer and inversely relabel the input of its tail. -/
def relabelFirstHidden {σ : ℝ → ℝ} {m k n : ℕ} (e : Equiv.Perm (Fin k))
    (L : DenseLayer (Fin m) (Fin k)) (N : MLP σ k n) : MLP σ m n :=
  .hidden (L.permuteOutput e) (N.permuteInput e)

/-- A neuron permutation is a parameter relabeling, not a change of represented function. -/
theorem eval_relabelFirstHidden {σ : ℝ → ℝ} {m k n : ℕ} (e : Equiv.Perm (Fin k))
    (L : DenseLayer (Fin m) (Fin k)) (N : MLP σ k n) (x : Fin m → ℝ) :
    (relabelFirstHidden e L N).eval x = (MLP.hidden L N).eval x := by
  simp only [relabelFirstHidden, eval_hidden, DenseLayer.preactivation_permuteOutput,
    DenseLayer.activate, Function.comp_def]
  exact N.eval_permuteInput e (L.activate σ x)

/-- Every hidden affine layer has identical output neurons. -/
def HiddenLayersIdentical {σ : ℝ → ℝ} {m n : ℕ} : MLP σ m n → Prop
  | .output _ => True
  | .hidden L N => L.IdenticalNeurons ∧ N.HiddenLayersIdentical

/-- Every width-tagged state in a trace is collapsed. -/
def TraceCollapsed (trace : List HiddenRepresentation) : Prop :=
  ∀ state ∈ trace, AllCoordinatesEqual state.2

theorem HiddenLayersIdentical.traceCollapsed {σ : ℝ → ℝ} {m n : ℕ}
    {N : MLP σ m n} (hN : N.HiddenLayersIdentical) (x : Fin m → ℝ) :
    TraceCollapsed (N.hiddenTrace x) := by
  induction N with
  | output L => simp [hiddenTrace, TraceCollapsed]
  | hidden L N ih =>
      intro state hstate
      simp only [hiddenTrace, List.mem_cons] at hstate
      rcases hstate with rfl | htail
      · exact hN.1.activate σ x
      · exact ih hN.2 (L.activate σ x) state htail

/-- Replace every affine layer by zero parameters while preserving the architecture. -/
def zeroLike {σ : ℝ → ℝ} {m n : ℕ} : MLP σ m n → MLP σ m n
  | .output _ => .output ⟨0, 0⟩
  | .hidden _ N => .hidden ⟨0, 0⟩ N.zeroLike

theorem hiddenLayersIdentical_zeroLike {σ : ℝ → ℝ} {m n : ℕ} (N : MLP σ m n) :
    N.zeroLike.HiddenLayersIdentical := by
  induction N with
  | output L => simp [zeroLike, HiddenLayersIdentical]
  | hidden L N ih =>
      simp only [zeroLike, HiddenLayersIdentical]
      exact ⟨DenseLayer.identicalNeurons_zero, ih⟩

/-- Zero initialization makes every hidden representation constant across its neuron axis. -/
theorem zeroLike_traceCollapsed {σ : ℝ → ℝ} {m n : ℕ}
    (N : MLP σ m n) (x : Fin m → ℝ) : TraceCollapsed (N.zeroLike.hiddenTrace x) :=
  (hiddenLayersIdentical_zeroLike N).traceCollapsed x

end MLP

/-- Parameters fixed by every transformation in a family. -/
def FixedBy {G Θ : Type*} (act : G → Θ → Θ) (θ : Θ) : Prop :=
  ∀ g, act g θ = θ

/-- An update commutes with a family of symmetry transformations. -/
def EquivariantUpdate {G Θ : Type*} (act : G → Θ → Θ) (step : UpdateRule Θ) : Prop :=
  ∀ g θ, step (act g θ) = act g (step θ)

/-- An equivariant update preserves the fixed-point locus of the symmetry. -/
theorem EquivariantUpdate.fixedBy {G Θ : Type*} {act : G → Θ → Θ}
    {step : UpdateRule Θ} (hstep : EquivariantUpdate act step) {θ : Θ}
    (hθ : FixedBy act θ) : FixedBy act (step θ) := by
  intro g
  rw [← hstep, hθ]

/-- Every iterate of an equivariant update preserves symmetric initialization. -/
theorem EquivariantUpdate.trajectory_fixedBy {G Θ : Type*} {act : G → Θ → Θ}
    {step : UpdateRule Θ} (hstep : EquivariantUpdate act step) {θ : Θ}
    (hθ : FixedBy act θ) (n : ℕ) : FixedBy act (step.trajectory θ n) := by
  induction n with
  | zero => exact hθ
  | succ n ih => exact hstep.fixedBy ih

/-- Formal optimizer-independent content of zero-initialization collapse: if zero/identical
parameters are fixed by all neuron permutations and the learning update is equivariant, every
training iterate remains in that fixed-point locus.  Concluding equality of particular weight rows
then uses the concrete permutation action; concluding poor task loss needs an additional problem.
-/
theorem permutationSymmetricTraining_preservesCollapse {G Θ : Type*}
    (act : G → Θ → Θ) (step : UpdateRule Θ) (θ₀ : Θ)
    (hzero : FixedBy act θ₀) (hequiv : EquivariantUpdate act step) (n : ℕ) :
    FixedBy act (step.trajectory θ₀ n) :=
  hequiv.trajectory_fixedBy hzero n

end NeuralNetwork

end

end
