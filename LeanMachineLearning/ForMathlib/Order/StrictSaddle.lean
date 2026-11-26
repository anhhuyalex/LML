/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Tactic.ByContra

/-!
# Uniqueness of strict saddle points

## Main statements

* `eq_of_strict_saddle`: a function of two variables has at most one point of `S × T` at which
  it has a strict minimum in the first variable and a strict maximum in the second.
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
