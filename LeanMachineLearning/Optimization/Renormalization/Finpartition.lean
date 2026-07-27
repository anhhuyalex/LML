/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.Order.Partition.Finpartition

/-!
# Finite-partition algebra for renormalization

This file defines the combinatorial transforms used for moments, cumulants, and Wick expansions.
It has no probability or measure-theory imports.

## Main definitions

* `Finpartition.blockProduct`: product of a block weight over the parts of a partition.
* `Finpartition.partitionTransform`: sum of block products over all partitions.
* `Finpartition.cumulantTransform`: the signed Möbius transform on set partitions.
* `Finpartition.Pairing`: a finite partition whose blocks all have cardinality two.
* `Finpartition.pairingSum`: sum of block products over pairings.

## Verified external API

The declarations used from the pinned Mathlib revision were checked in
`RenormalizationAPIAudit.lean`: `Finpartition.map`, `Finpartition.bind`,
`Finpartition.bind_parts`, `Finpartition.mem_bind`, `Finpartition.card_bind`,
`Finpartition.sum_card_parts`, `Equiv.finsetCongr`, `Finset.prod_biUnion`,
`Finset.prod_sum`, `Fintype.prod_sum`, and
`IncidenceAlgebra.moebius_inversion_bot`.

## Deferred proofs

The theorem statements in this first skeleton intentionally use `sorry`.  The structural map and
bind results follow by transporting partitions with `Finpartition.map`, expanding
`Finpartition.bind_parts`, and applying the standard finite product reindexing lemmas.  The pairing
cardinality result follows from `Finpartition.sum_card_parts`, since every block contributes two.
The two inversion theorems are Möbius inversion on the lattice of set partitions, whose interval
coefficient is `(-1)^(k-1) * (k-1)!` for a partition with `k` blocks.

References:

* Mathlib's finite-partition implementation:
  <https://github.com/leanprover-community/mathlib4/blob/abb22825db7e020c94f38a007ae3fffe6c3a7532/Mathlib/Order/Partition/Finpartition.lean>
* G.-C. Rota, *On the foundations of combinatorial theory I. Theory of Möbius functions*:
  <https://doi.org/10.1007/BF00531932>
-/

@[expose] public section

open scoped BigOperators

namespace Finpartition

variable {α β R : Type*} [DecidableEq α]

/-- The product of `f` over all blocks of a finite partition. -/
def blockProduct [CommMonoid R] {s : Finset α} (P : Finpartition s)
    (f : Finset α → R) : R :=
  ∏ B ∈ P.parts, f B

/-- The partition transform: sum over partitions of the product of their block weights. -/
def partitionTransform [CommSemiring R] (f : Finset α → R) (s : Finset α) : R :=
  ∑ P : Finpartition s, P.blockProduct f

/-- The Möbius coefficient of a partition in the interval ending at the indiscrete partition. -/
def cumulantCoefficient [CommRing R] {s : Finset α} (P : Finpartition s) : R :=
  (-1 : R) ^ (P.parts.card - 1) * (P.parts.card - 1).factorial

/-- The cumulant transform, with conventional value zero on the empty set. -/
def cumulantTransform [CommRing R] (f : Finset α → R) (s : Finset α) : R :=
  if s = ∅ then 0 else
    ∑ P : Finpartition s, cumulantCoefficient P * P.blockProduct f

/-- A finite partition is a pairing when each of its blocks has cardinality two. -/
def IsPairing {s : Finset α} (P : Finpartition s) : Prop :=
  ∀ B ∈ P.parts, B.card = 2

/-- A pairing of `s` is a finite partition of `s` into two-element blocks. -/
def Pairing (s : Finset α) :=
  {P : Finpartition s // ∀ B ∈ P.parts, B.card = 2}

noncomputable instance {s : Finset α} : Fintype (Pairing s) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun P : Finpartition s ↦ ∀ B ∈ P.parts, B.card = 2) (by
    intro P
    simp)

/-- The product of `f` over the two-element blocks of a pairing. -/
def Pairing.blockProduct [CommMonoid R] {s : Finset α} (P : Pairing s)
    (f : Finset α → R) : R :=
  P.1.blockProduct f

/-- The sum of block products over all pairings of a finite set. -/
noncomputable def pairingSum [CommSemiring R] (f : Finset α → R) (s : Finset α) : R :=
  ∑ P : Pairing s, P.blockProduct f

/-- Every pairing has half as many blocks as elements.

Informal proof: sum the cardinalities of the blocks using `Finpartition.sum_card_parts` and replace
each summand by two using `P.2`.  The source is the Mathlib finite-partition file linked in the
module docstring. -/
theorem Pairing.two_mul_card_parts {s : Finset α} (P : Pairing s) :
    2 * P.1.parts.card = s.card := by
  sorry

/-- A finite set of odd cardinality has no pairing.

Informal proof: a pairing would make its cardinality twice the number of blocks by
`Pairing.two_mul_card_parts`, contradicting oddness. -/
theorem Pairing.isEmpty_of_odd_card {s : Finset α} (hs : Odd s.card) : IsEmpty (Pairing s) := by
  sorry

/-- In a pairing, an element has a unique distinct partner in its block.

Informal proof: the block `P.1.part a` exists and contains `a`; its cardinality is two, so it has
exactly one other member.  Uniqueness follows because `Finpartition.part` is the unique block
containing `a`. -/
theorem Pairing.existsUnique_partner {s : Finset α} (P : Pairing s) {a : α} (ha : a ∈ s) :
    ∃! b : α, b ∈ s ∧ b ≠ a ∧ P.1.part a = {a, b} := by
  sorry

/-- Add a fresh two-element block to a pairing.

Informal construction: extend the underlying finpartition by the disjoint block `{a, b}`.  The old
blocks remain pairs, and the new block has cardinality two because `a ≠ b`. -/
def Pairing.insertPair {s : Finset α} (P : Pairing s) {a b : α} (hab : a ≠ b)
    (ha : a ∉ s) (hb : b ∉ s) : Pairing (insert a (insert b s)) := by
  sorry

/-- The blocks of `insertPair` are the new pair together with the original blocks.

Informal proof: unfold the construction and use the `parts` theorem for
`Finpartition.extend`; freshness makes the union disjoint. -/
theorem Pairing.insertPair_parts {s : Finset α} (P : Pairing s) {a b : α} (hab : a ≠ b)
    (ha : a ∉ s) (hb : b ∉ s) :
    (P.insertPair hab ha hb).1.parts = insert {a, b} P.1.parts := by
  sorry

/-- The order isomorphism on finite sets induced by an equivalence of element types. -/
def _root_.Equiv.finsetOrderIso (e : α ≃ β) : Finset α ≃o Finset β where
  toEquiv := e.finsetCongr
  map_rel_iff' := by
    intro s t
    simp [Equiv.finsetCongr_apply]

/-- Reindex a finite partition along an equivalence. -/
def mapEquiv [DecidableEq β] (e : α ≃ β) {s : Finset α} (P : Finpartition s) :
    Finpartition (s.map e.toEmbedding) :=
  P.map e.finsetOrderIso

/-- Reindexing maps every block along the same equivalence.

Informal proof: this is `Finpartition.parts_map` followed by
`Equiv.finsetCongr_apply`. -/
theorem parts_mapEquiv [DecidableEq β] (e : α ≃ β) {s : Finset α}
    (P : Finpartition s) :
    (P.mapEquiv e).parts = P.parts.map e.finsetOrderIso.toEmbedding := by
  sorry

/-- Block products are natural under reindexing.

Informal proof: rewrite the parts with `parts_mapEquiv` and apply `Finset.prod_map`. -/
theorem blockProduct_mapEquiv [DecidableEq β] [CommMonoid R] (e : α ≃ β)
    {s : Finset α} (P : Finpartition s) (f : Finset β → R) :
    (P.mapEquiv e).blockProduct f = P.blockProduct (fun B ↦ f (B.map e.toEmbedding)) := by
  sorry

/-- The partition transform commutes with reindexing by an equivalence.

Informal proof: `mapEquiv e` is a bijection on partitions, and
`blockProduct_mapEquiv` identifies corresponding summands. -/
theorem partitionTransform_map [DecidableEq β] [CommSemiring R] (e : α ≃ β)
    (f : Finset β → R) (s : Finset α) :
    partitionTransform f (s.map e.toEmbedding) =
      partitionTransform (fun B ↦ f (B.map e.toEmbedding)) s := by
  sorry

/-- The cumulant transform commutes with reindexing by an equivalence.

Informal proof: use the same partition bijection as `partitionTransform_map`; it preserves the
number of blocks, hence also `cumulantCoefficient`. -/
theorem cumulantTransform_map [DecidableEq β] [CommRing R] (e : α ≃ β)
    (f : Finset β → R) (s : Finset α) :
    cumulantTransform f (s.map e.toEmbedding) =
      cumulantTransform (fun B ↦ f (B.map e.toEmbedding)) s := by
  sorry

/-- The block product of a bound partition factors over the outer partition.

Informal proof: expand `Finpartition.bind_parts` as a disjoint bi-union and use
`Finset.prod_biUnion`; disjointness is supplied by the outer partition. -/
theorem blockProduct_bind [CommMonoid R] {s : Finset α} (P : Finpartition s)
    (Q : ∀ B ∈ P.parts, Finpartition B) (f : Finset α → R) :
    (P.bind Q).blockProduct f = ∏ B : P.parts, (Q B.1 B.2).blockProduct f := by
  sorry

/-- Summing over refinements of every block factors as a product of partition transforms.

Informal proof: apply `blockProduct_bind`, then distribute the finite product over the independent
finite sums with `Fintype.prod_sum`. -/
theorem partitionTransform_bind [CommSemiring R] {s : Finset α} (P : Finpartition s)
    (f : Finset α → R) :
    (∑ Q : ∀ B : P.parts, Finpartition B.1,
      (P.bind (fun B hB ↦ Q ⟨B, hB⟩)).blockProduct f) =
      ∏ B : P.parts, partitionTransform f B.1 := by
  sorry

/-- The partition transform inverts the cumulant transform for functions normalized at the empty
set.

Informal proof: expand both transforms, regroup nested partitions by `Finpartition.bind`, and apply
Möbius inversion on the partition lattice.  Rota's paper linked in the module docstring proves the
general inversion theorem and the coefficient `(-1)^(k-1)(k-1)!`. -/
theorem partitionTransform_cumulantTransform [CommRing R] (f : Finset α → R)
    (hf : f ∅ = 1) :
    partitionTransform (cumulantTransform f) = f := by
  sorry

/-- The cumulant transform inverts the partition transform for functions vanishing at the empty
set.

Informal proof: this is the converse direction of the same Möbius inversion.  The special value of
`cumulantTransform` at the empty set agrees with the hypothesis `f ∅ = 0`. -/
theorem cumulantTransform_partitionTransform [CommRing R] (f : Finset α → R)
    (hf : f ∅ = 0) :
    cumulantTransform (partitionTransform f) = f := by
  sorry

end Finpartition

end
