/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.InducedLaw

/-!
# Approximation and learning vocabulary for parameterized models

This file makes the source's distinction between a target, a parameterized family, approximation,
and a learning algorithm explicit.  It intentionally asserts no universal-approximation or
optimizer-convergence theorem: those require hypotheses absent from the source chapter.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace NeuralNetwork

universe uΘ uX uY uA

namespace ParamModel

variable {Θ : Type uΘ} {X : Type uX} {Y : Type uY}
  [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Y]

/-- The set of functions represented exactly by a parameterized model. -/
def functionClass (F : ParamModel Θ X Y) : Set (X → Y) := Set.range F.eval

/-- A model realizes a target exactly when some parameter evaluates to that target. -/
def Realizes (F : ParamModel Θ X Y) (target : X → Y) : Prop :=
  ∃ θ, F.eval θ = target

theorem realizes_iff_mem_functionClass (F : ParamModel Θ X Y) (target : X → Y) :
    F.Realizes target ↔ target ∈ F.functionClass := Iff.rfl

/-- Pointwise approximation on a specified domain.  This formulation avoids assuming compactness
or the existence of a supremum norm. -/
def ApproximatesOn [PseudoMetricSpace Y] (F : ParamModel Θ X Y) (target : X → Y)
    (s : Set X) (ε : ℝ) : Prop :=
  ∃ θ, ∀ x ∈ s, dist (F.eval θ x) (target x) ≤ ε

/-- Approximation to arbitrary positive accuracy on a domain. -/
def IsDenseOn [PseudoMetricSpace Y] (F : ParamModel Θ X Y) (target : X → Y)
    (s : Set X) : Prop :=
  ∀ ε, 0 < ε → F.ApproximatesOn target s ε

/-- An exact realization gives every nonnegative approximation tolerance. -/
theorem Realizes.approximatesOn [PseudoMetricSpace Y] {F : ParamModel Θ X Y}
    {target : X → Y} (h : F.Realizes target) (s : Set X) {ε : ℝ} (hε : 0 ≤ ε) :
    F.ApproximatesOn target s ε := by
  obtain ⟨θ, hθ⟩ := h
  refine ⟨θ, fun x _ => ?_⟩
  rw [hθ]
  simpa using hε

/-- An embedding of one parameter space into another that preserves evaluation. -/
structure EmbedsInto {Θ' : Type*} [MeasurableSpace Θ']
    (F : ParamModel Θ X Y) (G : ParamModel Θ' X Y) where
  /-- Embed source parameters into target parameters. -/
  param : Θ → Θ'
  /-- Embedded parameters compute the same function. -/
  eval_eq : ∀ θ x, G.eval (param θ) x = F.eval θ x

/-- Expressivity is monotone under a parameter embedding. -/
theorem EmbedsInto.realizes {Θ' : Type*} [MeasurableSpace Θ']
    {F : ParamModel Θ X Y} {G : ParamModel Θ' X Y} (h : F.EmbedsInto G)
    {target : X → Y} (ht : F.Realizes target) : G.Realizes target := by
  obtain ⟨θ, rfl⟩ := ht
  exact ⟨h.param θ, funext (h.eval_eq θ)⟩

/-- Approximation is monotone under a parameter embedding. -/
theorem EmbedsInto.approximatesOn {Θ' : Type*} [MeasurableSpace Θ'] [PseudoMetricSpace Y]
    {F : ParamModel Θ X Y} {G : ParamModel Θ' X Y} (h : F.EmbedsInto G)
    {target : X → Y} {s : Set X} {ε : ℝ} (ht : F.ApproximatesOn target s ε) :
    G.ApproximatesOn target s ε := by
  obtain ⟨θ, hθ⟩ := ht
  exact ⟨h.param θ, fun x hx => by rw [h.eval_eq]; exact hθ x hx⟩

end ParamModel

/-- A supervised learning problem separates the target from the model and records the loss used to
compare predictions with target values. -/
structure SupervisedProblem (X : Type uX) (Y : Type uY) where
  /-- The function to be learned or approximated. -/
  target : X → Y
  /-- Pointwise discrepancy between a prediction and a target value. -/
  loss : Y → Y → ℝ

namespace SupervisedProblem

variable {X : Type uX} {Y : Type uY} {A : Type uA} {Θ : Type uΘ}

/-- Average empirical risk on a finite indexed dataset.  For an empty index type the conventional
Lean value is zero because both the sum and natural-cardinality denominator are zero. -/
def empiricalRisk [Fintype A] (P : SupervisedProblem X Y) (eval : Θ → X → Y)
    (D : A → X) (θ : Θ) : ℝ :=
  (∑ a, P.loss (eval θ (D a)) (P.target (D a))) / Fintype.card A

@[simp] theorem empiricalRisk_apply [Fintype A] (P : SupervisedProblem X Y)
    (eval : Θ → X → Y) (D : A → X) (θ : Θ) :
    P.empiricalRisk eval D θ =
      (∑ a, P.loss (eval θ (D a)) (P.target (D a))) / Fintype.card A := rfl

end SupervisedProblem

/-- A deterministic one-step learning rule on a parameter space. -/
abbrev UpdateRule (Θ : Type uΘ) := Θ → Θ

namespace UpdateRule

variable {Θ : Type uΘ}

/-- Parameter value after `n` updates. -/
def trajectory (step : UpdateRule Θ) (θ₀ : Θ) : ℕ → Θ
  | 0 => θ₀
  | n + 1 => step (trajectory step θ₀ n)

@[simp] theorem trajectory_zero (step : UpdateRule Θ) (θ₀ : Θ) :
    step.trajectory θ₀ 0 = θ₀ := rfl

@[simp] theorem trajectory_succ (step : UpdateRule Θ) (θ₀ : Θ) (n : ℕ) :
    step.trajectory θ₀ (n + 1) = step (step.trajectory θ₀ n) := rfl

/-- A learning rule is risk-nonincreasing for a specified risk functional. -/
def NonincreasingFor (step : UpdateRule Θ) (risk : Θ → ℝ) : Prop :=
  ∀ θ, risk (step θ) ≤ risk θ

theorem NonincreasingFor.trajectory (step : UpdateRule Θ) (risk : Θ → ℝ)
    (h : step.NonincreasingFor risk) (θ₀ : Θ) :
    Antitone fun n => risk (step.trajectory θ₀ n) := by
  apply antitone_nat_of_succ_le
  intro n
  exact h _

end UpdateRule

end NeuralNetwork

end

end
