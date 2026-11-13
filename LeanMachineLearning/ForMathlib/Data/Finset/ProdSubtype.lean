/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Products over a subtype with one factor erased

A product over the subtype `↥s` of a finset with the factor at `u : ↥s` erased is the product over
`s.erase u`.
-/

@[expose] public section

namespace Finset

/-- A product over `↥s` with the factor at `u` erased is the product over `s.erase ↑u`. -/
theorem prod_univ_erase_subtype {J M : Type*} [CommMonoid M] [DecidableEq J]
    (s : Finset J) (u : s) (H : J → M) :
    (∏ j ∈ (Finset.univ : Finset s).erase u, H j) = ∏ j ∈ s.erase (u : J), H j := by
  apply Finset.prod_bij (fun (j : s) _ => (j : J))
  · intro j hj
    exact Finset.mem_erase.mpr
      ⟨fun heq => (Finset.ne_of_mem_erase hj) (Subtype.ext heq), j.2⟩
  · intro j _ k _ hjk
    exact Subtype.ext hjk
  · intro j hj
    refine ⟨⟨j, (Finset.mem_erase.mp hj).2⟩, ?_, rfl⟩
    simpa only [Finset.mem_erase, Finset.mem_univ, and_true] using
      (show (⟨j, (Finset.mem_erase.mp hj).2⟩ : s) ≠ u from
        fun h => (Finset.ne_of_mem_erase hj) (congrArg Subtype.val h))
  · intro _ _
    rfl

end Finset
