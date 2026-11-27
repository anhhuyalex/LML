/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Tactic.ByContra

/-!
# Saddle points

## Main statements

* `eq_of_strict_saddle`: a function of two variables has at most one point of `S × T` at which
  it has a strict minimum in the first variable and a strict maximum in the second.
* `notMem_segment_of_saddle`: a point `y₁` at which some partial value is below the partial
  minimum at `y₀` is not between `y₀` and the second coordinate of a saddle point. This confines
  saddle points of perturbed functions.
-/

@[expose] public section

/-- A function of two variables has at most one strict saddle point: if `(a, b)` and `(c, d)`
are both strict minima in the first variable (over `S`) and strict maxima in the second (over
`T`), then they coincide. -/
theorem eq_of_strict_saddle {X Y β : Type*} [Preorder β] {G : X → Y → β} {S : Set X}
    {T : Set Y} {a c : X} {b d : Y} (ha : a ∈ S) (hb : b ∈ T) (hc : c ∈ S) (hd : d ∈ T)
    (hmin : ∀ x ∈ S, x ≠ a → G a b < G x b) (hmax : ∀ y ∈ T, y ≠ b → G a y < G a b)
    (hmin' : ∀ x ∈ S, x ≠ c → G c d < G x d) (hmax' : ∀ y ∈ T, y ≠ d → G c y < G c d) :
    a = c ∧ b = d := by
  by_contra hne
  have lt : ∀ {a c : X} {b d : Y}, a ∈ S → b ∈ T → c ∈ S →
      (∀ x ∈ S, x ≠ a → G a b < G x b) → (∀ y ∈ T, y ≠ d → G c y < G c d) →
      ¬(a = c ∧ b = d) → G a b < G c d := by
    intro a c b d _ hb hc hmin hmax hne
    by_cases hca : c = a
    · subst hca
      exact hmax b hb fun h => hne ⟨rfl, h⟩
    by_cases hbd : b = d
    · subst hbd
      exact hmin c hc hca
    exact (hmin c hc hca).trans (hmax b hb hbd)
  exact lt_asymm (lt ha hb hc hmin hmax' hne)
    (lt hc hd ha hmin' hmax fun h => hne ⟨h.1.symm, h.2.symm⟩)

/-- Let `x` minimize `f · y` over `S` and let `f x y₀ ≤ f x y`, and suppose every `f x' y₀`,
`x' ∈ S`, is at least `m`. If `f x₁ ·` is quasiconcave on `Y` and `f x₁ y₁` is not at least `m`,
then `y₁` is not on the segment from `y₀` to `y`. -/
theorem notMem_segment_of_saddle {𝕜 X E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
    [AddCommMonoid E] [SMul 𝕜 E] [Preorder β] {f : X → E → β} {S : Set X} {Y : Set E}
    {x x₁ : X} {y y₀ y₁ : E} {m : β} (hx : x ∈ S) (hx₁ : x₁ ∈ S)
    (hq : QuasiconcaveOn 𝕜 Y (f x₁)) (hy : y ∈ Y) (hy₀ : y₀ ∈ Y)
    (hmin : ∀ x' ∈ S, f x y ≤ f x' y) (hmax : f x y₀ ≤ f x y) (hm : ∀ x' ∈ S, m ≤ f x' y₀)
    (h₁ : ¬m ≤ f x₁ y₁) : y₁ ∉ segment 𝕜 y₀ y := fun hseg =>
  h₁ ((hq m).segment_subset ⟨hy₀, hm x₁ hx₁⟩
    ⟨hy, ((hm x hx).trans hmax).trans (hmin x₁ hx₁)⟩ hseg).2
