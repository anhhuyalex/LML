/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Approximation.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Algebra.Polynomial.Basic

/-!
# Universal approximation theorem (Hornik-Stinchcombe-White 1989)

This file formalizes the universal approximation results of Chapter 2, Section 2.2.
The key steps are:

1. Show that the cosine and exponential function classes are closed under multiplication,
   making them subalgebras of C(S, ℝ).
2. Apply the Stone-Weierstrass theorem (from Mathlib) to conclude density.
3. Approximate the cosine activation by the sigmoidal activation to transfer universality.

## Main results

* `IsUniversal` : predicate for universal approximation over compact sets
* `cos_mul_mem` : F_{cos,d} is closed under pointwise multiplication
* `exp_mul_mem` : F_{exp,d} is closed under pointwise multiplication
* `cos_isUniversal` : F_{cos,d} is a universal approximator
* `exp_isUniversal` : F_{exp,d} is a universal approximator
* `sigmoidal_isUniversal` : F_{σ,d} is universal for any sigmoidal σ
* `relu_isUniversal` : F_{ReLU,d} is a universal approximator

-/

@[expose] public section

open Real Filter Topology ContinuousMap

namespace Approximation.Universal

variable {d : ℕ}

/-! ### Universal approximation predicate -/

/-- A function class ℱ is a universal approximator over compact sets if for every
    compact S ⊆ ℝᵈ, every continuous g : S → ℝ, and every ε > 0, there is f ∈ ℱ
    with sup_{x ∈ S} |f(x) - g(x)| ≤ ε. -/
def IsUniversal (ℱ : Set ((EuclideanSpace ℝ (Fin d)) → ℝ)) : Prop :=
  ∀ (S : Set (EuclideanSpace ℝ (Fin d))), IsCompact S →
  ∀ (g : (EuclideanSpace ℝ (Fin d)) → ℝ), ContinuousOn g S →
  ∀ ε > 0, ∃ f ∈ ℱ, ∀ x ∈ S, |f x - g x| ≤ ε

/-! ### Closure under multiplication -/

/-- F_{cos,d} is closed under pointwise multiplication.
    Proof uses 2cos(y)cos(z) = cos(y+z) + cos(y-z). -/
theorem cos_mul_mem (f₁ f₂ : (EuclideanSpace ℝ (Fin d)) → ℝ)
    (hf₁ : f₁ ∈ OneHiddenLayer.UnboundedClass (fun z => Real.cos z) d)
    (hf₂ : f₂ ∈ OneHiddenLayer.UnboundedClass (fun z => Real.cos z) d) :
    (fun x => f₁ x * f₂ x) ∈ OneHiddenLayer.UnboundedClass (fun z => Real.cos z) d := by
  sorry

/-- F_{exp,d} is closed under pointwise multiplication.
    Proof uses exp(aᵀx) · exp(bᵀx) = exp((a+b)ᵀx). -/
theorem exp_mul_mem (f₁ f₂ : (EuclideanSpace ℝ (Fin d)) → ℝ)
    (hf₁ : f₁ ∈ OneHiddenLayer.UnboundedClass Real.exp d)
    (hf₂ : f₂ ∈ OneHiddenLayer.UnboundedClass Real.exp d) :
    (fun x => f₁ x * f₂ x) ∈ OneHiddenLayer.UnboundedClass Real.exp d := by
  sorry

/-! ### Stone-Weierstrass via Mathlib -/

/-- F_{cos,d} satisfies the Stone-Weierstrass separation condition:
    for x ≠ x', the function z ↦ cos((z-x')ᵀ(x-x')/‖x-x'‖²) separates them. -/
lemma cos_separates_points (x x' : EuclideanSpace ℝ (Fin d)) (h : x ≠ x') :
    ∃ f ∈ OneHiddenLayer.UnboundedClass (fun z => Real.cos z) d, f x ≠ f x' := by
  sorry

/-- F_{cos,d} does not vanish: cos(0ᵀx) = 1 for all x. -/
lemma cos_nonvanishing (x : EuclideanSpace ℝ (Fin d)) :
    ∃ f ∈ OneHiddenLayer.UnboundedClass (fun z => Real.cos z) d, f x ≠ 0 := by
  refine ⟨fun _ => 1, ?_, one_ne_zero⟩
  simp only [OneHiddenLayer.UnboundedClass, OneHiddenLayer.FunctionClass,
    Set.mem_iUnion, Set.mem_setOf_eq]
  -- Use one neuron: weight 0, bias 0, coefficient 1 → eval = 1 * cos(0) = 1
  exact ⟨1, { weights := fun _ => 0, biases := fun _ => 0, coeffs := fun _ => 1 }, by
    funext y
    simp [OneHiddenLayer.Network.eval]⟩

/-! ### Main universality theorems -/

/-- Lemma 2.2: F_{cos,d} is a universal approximator (Hornik-Stinchcombe-White 1989). -/
theorem cos_isUniversal : IsUniversal (OneHiddenLayer.UnboundedClass (fun z => Real.cos z) d) := by
  sorry

/-- F_{exp,d} is a universal approximator. -/
theorem exp_isUniversal : IsUniversal (OneHiddenLayer.UnboundedClass Real.exp d) := by
  sorry

/-- Theorem 2.3: for any sigmoidal σ, F_{σ,d} is a universal approximator. -/
theorem sigmoidal_isUniversal (σ : ℝ → ℝ) (hσ : Sigmoidal σ) :
    IsUniversal (OneHiddenLayer.UnboundedClass σ d) := by
  sorry

/-- Corollary: F_{ReLU,d} is a universal approximator.
    Uses the fact that z ↦ σ_ReLU(z) - σ_ReLU(z-1) exhibits sigmoidal-type behavior. -/
theorem relu_isUniversal : IsUniversal (OneHiddenLayer.UnboundedClass reluActivation d) := by
  sorry

/-! ### Alternative Universal Approximation Conditions -/

/-- Cybenko (1989) approach via duality: if ℱ_σ is not dense in C(S, ℝ),
then by duality there exists a signed measure μ such that ∫ σ(wᵀx - b) dμ(x) = 0
for all w, b. One can then show this implies μ = 0, a contradiction. -/
theorem cybenko_duality (σ : ℝ → ℝ) (hσ : Sigmoidal σ) :
    IsUniversal (OneHiddenLayer.UnboundedClass σ d) := by
  sorry

/-- Leshno et al (1993): A continuous activation function σ is a universal approximator
if and only if it is not a polynomial. -/
theorem leshno_isUniversal_iff_not_polynomial (σ : ℝ → ℝ) (h_cont : Continuous σ) :
    IsUniversal (OneHiddenLayer.UnboundedClass σ d) ↔
    ¬ ∃ (p : Polynomial ℝ), ∀ x, σ x = Polynomial.eval x p := by
  sorry

end Approximation.Universal

end
