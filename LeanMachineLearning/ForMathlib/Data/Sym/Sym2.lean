/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Data.Sym.Sym2.Order
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Unordered pairs, equivalences and sorted representatives

`Sym2.map` is functorial; for an equivalence `e : α ≃ β` it is an equivalence
`Equiv.sym2Congr e : Sym2 α ≃ Sym2 β`, the unordered-pair analogue of `Equiv.prodCongr`
(and of `Sym.equivCongr` for symmetric powers).

Sorted representatives agree exactly up to swapping. Sorting is injective on cross pairs
from two disjoint sets, so endpoint enumerations can reuse these facts without analytic imports.
-/

@[expose] public section

namespace Equiv

variable {α β : Type*}

/-- An equivalence `α ≃ β` induces an equivalence of unordered pairs `Sym2 α ≃ Sym2 β`. -/
def sym2Congr (e : α ≃ β) : Sym2 α ≃ Sym2 β where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv c := Sym2.ind (fun x y => by simp [Sym2.map_mk]) c
  right_inv c := Sym2.ind (fun x y => by simp [Sym2.map_mk]) c

@[simp]
theorem sym2Congr_apply (e : α ≃ β) (c : Sym2 α) : sym2Congr e c = Sym2.map e c := rfl

@[simp]
theorem sym2Congr_symm (e : α ≃ β) : (sym2Congr e).symm = sym2Congr e.symm := rfl

end Equiv

/-- Unordered pairs given by `(min, max)` are equal iff they agree up to swapping. -/
theorem minmax_pair_eq_iff {α : Type*} [LinearOrder α] {x y x' y' : α} :
    (min x y, max x y) = (min x' y', max x' y') ↔ (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  rw [Prod.mk.injEq]
  exact (Sym2.inf_eq_inf_and_sup_eq_sup
    (s := s(x, y)) (t := s(x', y'))).trans Sym2.eq_iff

/-- Sorting retains the two endpoint choices when they come from disjoint sets. -/
theorem minmax_pair_injOn_prod {α : Type*} [LinearOrder α] {S T : Set α}
    (hd : Disjoint S T) :
    Set.InjOn (fun p : α × α => (min p.1 p.2, max p.1 p.2)) (S ×ˢ T) := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd he
  rcases minmax_pair_eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact False.elim (Set.disjoint_left.mp hd hab.1 hcd.2)

namespace Finset

open scoped BigOperators

/-- Sum weights over sorted cross choices between disjoint finite sets. The weight need
not be symmetric, and may take values in any additive commutative monoid. -/
theorem sum_orderedPairs_sorted_product {α M : Type*} [Fintype α] [LinearOrder α]
    [AddCommMonoid M] (A B : Finset α) (hd : Disjoint A B) (f : α × α → M) :
    (∑ p ∈ (univ : Finset {p : α × α // p.1 < p.2}).filter (fun p =>
      p.val ∈ (A.product B).image (fun ab => (min ab.1 ab.2, max ab.1 ab.2))), f p.val) =
      ∑ ab ∈ A.product B, f (min ab.1 ab.2, max ab.1 ab.2) := by
  let C := (A.product B).image (fun ab => (min ab.1 ab.2, max ab.1 ab.2))
  let D := (univ : Finset ({p : α × α // p.1 < p.2})).filter fun p => p.val ∈ C
  have hD : D.image Subtype.val = C := by
    ext ab
    constructor
    · intro hab
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hab
      exact (mem_filter.mp hp).2
    · intro hab
      obtain ⟨⟨a, b⟩, hP, he⟩ := mem_image.mp hab
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hP
      have hne : a ≠ b := fun h => disjoint_left.mp hd ha (h ▸ hb)
      have hlt : ab.1 < ab.2 := by
        rw [← he]
        exact min_lt_max.mpr hne
      exact mem_image.mpr ⟨⟨ab, hlt⟩, mem_filter.mpr ⟨mem_univ _, hab⟩, rfl⟩
  have hi : Set.InjOn (fun ab : α × α => (min ab.1 ab.2, max ab.1 ab.2))
      (A.product B : Set (α × α)) := by
    intro ab hab cd hcd he
    exact minmax_pair_injOn_prod (disjoint_coe.mpr hd)
      (Finset.mem_product.mp hab) (Finset.mem_product.mp hcd) he
  calc
    (∑ p ∈ D, f p.val) = ∑ ab ∈ D.image Subtype.val, f ab :=
      (sum_image (fun _ _ _ _ h => Subtype.val_injective h)).symm
    _ = ∑ ab ∈ C, f ab := by rw [hD]
    _ = ∑ ab ∈ A.product B, f (min ab.1 ab.2, max ab.1 ab.2) := sum_image hi

/-- Sorting cross choices from two disjoint finite sets gives one strictly ordered pair
per choice. The finite ambient type may be any linear order. -/
theorem card_orderedPairs_sorted_product {α : Type*} [Fintype α] [LinearOrder α]
    (A B : Finset α) (hd : Disjoint A B) :
    ((univ : Finset ({p : α × α // p.1 < p.2})).filter fun p =>
      p.val ∈ (A.product B).image (fun ab => (min ab.1 ab.2, max ab.1 ab.2))).card =
      A.card * B.card := by
  simpa using sum_orderedPairs_sorted_product A B hd (fun _ => (1 : ℕ))

end Finset
