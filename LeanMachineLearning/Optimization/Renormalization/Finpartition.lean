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
`Renormalization/APIAudit.lean`: `Finpartition.map`, `Finpartition.bind`,
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

-- The recursive decomposition of `pairingSum` (`pairingSum_erase_aux` and
-- `pairingSum_erase`) is defined after `Pairing.insertPair_parts` below, since the proof
-- needs `Pairing.insertPair` and `Pairing.existsUnique_partner`.

/-- Every pairing has half as many blocks as elements.

Informal proof: sum the cardinalities of the blocks using `Finpartition.sum_card_parts` and replace
each summand by two using `P.2`.  The source is the Mathlib finite-partition file linked in the
module docstring. -/
theorem Pairing.two_mul_card_parts {s : Finset α} (P : Pairing s) :
    2 * P.1.parts.card = s.card := by
  have h : ∑ B ∈ P.1.parts, B.card = s.card := P.1.sum_card_parts
  have h' : ∑ B ∈ P.1.parts, B.card = ∑ B ∈ P.1.parts, 2 := by
    apply Finset.sum_congr rfl
    intro B hB
    exact P.2 B hB
  rw [h'] at h
  rw [Finset.sum_const, Nat.nsmul_eq_mul] at h
  rw [← h, mul_comm]

/-- A finite set of odd cardinality has no pairing.

Informal proof: a pairing would make its cardinality twice the number of blocks by
`Pairing.two_mul_card_parts`, contradicting oddness. -/
theorem Pairing.isEmpty_of_odd_card {s : Finset α} (hs : Odd s.card) : IsEmpty (Pairing s) := by
  by_contra h
  simp only [not_isEmpty_iff] at h
  obtain ⟨P⟩ := h
  have h_eq : s.card = 2 * P.1.parts.card := (P.two_mul_card_parts).symm
  have h_even : Even s.card := ⟨P.1.parts.card, by rw [h_eq, two_mul]⟩
  exact Nat.not_odd_iff_even.mpr h_even hs

/-- In a pairing, an element has a unique distinct partner in its block.

Informal proof: the block `P.1.part a` exists and contains `a`; its cardinality is two, so it has
exactly one other member.  Uniqueness follows because `Finpartition.part` is the unique block
containing `a`. -/
theorem Pairing.existsUnique_partner {s : Finset α} (P : Pairing s) {a : α} (ha : a ∈ s) :
    ∃! b : α, b ∈ s ∧ b ≠ a ∧ P.1.part a = {a, b} := by
  have h_mem : P.1.part a ∈ P.1.parts := P.1.part_mem.2 ha
  have h_card : (P.1.part a).card = 2 := P.2 (P.1.part a) h_mem
  have ha_in : a ∈ P.1.part a := P.1.mem_part ha
  set t := P.1.part a \ {a} with ht
  have ht_card : t.card = 1 := by
    rw [ht]
    rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.2 ha_in)]
    simp [h_card]
  obtain ⟨b, hb_eq⟩ := Finset.card_eq_one.1 ht_card
  have hb_in : b ∈ P.1.part a := by
    have hbt : b ∈ t := by rw [hb_eq]; simp
    exact (Finset.mem_sdiff.1 hbt).1
  have hb_ne : b ≠ a := by
    have hbt : b ∈ t := by rw [hb_eq]; simp
    intro h
    have : b ∈ ({a} : Finset α) := by rw [h]; simp
    exact (Finset.mem_sdiff.1 hbt).2 this
  use b
  have h_card_ab : ({a, b} : Finset α).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hb_ne.symm)]
    simp
  have h_eq_ab : P.1.part a = {a, b} := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      by_cases h : x = a
      · rw [h]
        simp
      · have hx_t : x ∈ t := by
          rw [ht]
          exact Finset.mem_sdiff.2 ⟨hx, by simpa using h⟩
        rw [hb_eq] at hx_t
        simp [hx_t]
    · rw [h_card, h_card_ab]
  constructor
  · exact ⟨P.1.subset h_mem hb_in, hb_ne, h_eq_ab⟩
  · intro c hc
    rcases hc with ⟨hc_s, hc_ne, hc_eq⟩
    have hc_in : c ∈ P.1.part a := by
      rw [hc_eq]
      simp
    have : c ∈ t := by
      rw [ht]
      exact Finset.mem_sdiff.2 ⟨hc_in, by simpa using hc_ne⟩
    rw [hb_eq] at this
    rw [Finset.mem_singleton] at this
    exact this

/-- Add a fresh two-element block to a pairing.

Informal construction: extend the underlying finpartition by the disjoint block `{a, b}`.  The old
blocks remain pairs, and the new block has cardinality two because `a ≠ b`. -/
def Pairing.insertPair {s : Finset α} (P : Pairing s) {a b : α} (hab : a ≠ b)
    (ha : a ∉ s) (hb : b ∉ s) : Pairing (insert a (insert b s)) := by
  have h_disj : Disjoint s {a, b} := by
    simp [Finset.disjoint_iff_inter_eq_empty, ha, hb]
  have h_sup : s ∪ {a, b} = insert a (insert b s) := by
    ext x
    simp
  refine ⟨P.1.extend (show ({a, b} : Finset α) ≠ ∅ by simp) h_disj h_sup, ?_⟩
  intro B hB
  rw [Finpartition.extend_parts] at hB
  simp only [Finset.mem_insert] at hB
  rcases hB with (rfl | hB)
  · rw [Finset.card_pair hab]
  · exact P.2 B hB

/-- The blocks of `insertPair` are the new pair together with the original blocks.

Informal proof: unfold the construction and use the `parts` theorem for
`Finpartition.extend`; freshness makes the union disjoint. -/
theorem Pairing.insertPair_parts {s : Finset α} (P : Pairing s) {a b : α} (hab : a ≠ b)
    (ha : a ∉ s) (hb : b ∉ s) :
    (P.insertPair hab ha hb).1.parts = insert {a, b} P.1.parts := by
  simp [insertPair, Finpartition.extend_parts]

/-- The order isomorphism on finite sets induced by an equivalence of element types. -/
def _root_.Equiv.finsetOrderIso (e : α ≃ β) : Finset α ≃o Finset β where
  toEquiv := e.finsetCongr
  map_rel_iff' := by
    intro s t
    simp [Equiv.finsetCongr_apply]

/-- Decompose the pairing sum by choosing the partner of a distinguished element.

Informal proof: Every perfect matching of `s` pairs a distinguished element `a ∈ s` with a unique
element `b ∈ s \ {a}`. Thus, the sum over all pairings of `s` equals the sum over all `b ∈ s \ {a}`
of the block weight `f {a, b}` multiplied by the sum over all pairings of `s \ {a, b}`.
This formalizes the recursive structure of perfect matchings. (Source: Perfect matching, Wikipedia, https://en.wikipedia.org/wiki/Perfect_matching) -/
theorem pairingSum_erase {R : Type*} [CommSemiring R] (f : Finset α → R)
    (s : Finset α) {a : α} (ha : a ∈ s) :
    pairingSum f s =
      ∑ b ∈ s.erase a, f {a, b} * pairingSum f ((s.erase a).erase b) := by
  sorry


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
  simp [mapEquiv, Finpartition.parts_map]
  rfl

omit [DecidableEq α] in
/-- `mapEquiv e` is an equivalence of finpartition types, with inverse `mapEquiv e.symm`. -/
@[simp]
lemma finsetOrderIso_symm_apply (e : α ≃ β) (B : Finset α) :
    e.symm.finsetOrderIso (e.finsetOrderIso B) = B := by
  classical
  change e.symm.finsetCongr (e.finsetCongr B) = B
  simp [Equiv.finsetCongr_apply, Finset.map_map]

omit [DecidableEq α] in
@[simp]
lemma finsetOrderIso_apply_symm (e : α ≃ β) (B : Finset β) :
    e.finsetOrderIso (e.symm.finsetOrderIso B) = B := by
  classical
  change e.finsetCongr (e.symm.finsetCongr B) = B
  simp [Equiv.finsetCongr_apply, Finset.map_map]

lemma mapEquivEquiv_parts_eq [DecidableEq β] (e : α ≃ β) {s : Finset α} (P : Finpartition s) :
    (mapEquiv e.symm (mapEquiv e P)).parts = P.parts := by
  ext B
  simp only [parts_mapEquiv, Finset.mem_map, Equiv.finsetOrderIso]
  constructor
  · rintro ⟨B', ⟨B'', h1, h2⟩, h3⟩
    subst h2 h3
    have H : e.symm.finsetCongr.toEmbedding (e.finsetCongr.toEmbedding B'') = B'' := by
      ext b
      simp
    rwa [H]
  · intro h
    exact ⟨e.finsetCongr B, ⟨B, h, rfl⟩, Equiv.symm_apply_apply e.finsetCongr B⟩

lemma mapEquivEquiv_parts_eq' [DecidableEq β] (e : α ≃ β) {s : Finset α}
    (Q : Finpartition (s.map e.toEmbedding)) :
    (mapEquiv e (mapEquiv e.symm Q)).parts = Q.parts := by
  ext B
  simp only [parts_mapEquiv, Finset.mem_map, Equiv.finsetOrderIso]
  constructor
  · rintro ⟨B', ⟨B'', h1, h2⟩, h3⟩
    subst h2 h3
    have H : e.finsetCongr.toEmbedding (e.symm.finsetCongr.toEmbedding B'') = B'' := by
      ext b
      simp
    rwa [H]
  · intro h
    exact ⟨e.symm.finsetCongr B, ⟨B, h, rfl⟩, Equiv.apply_symm_apply e.finsetCongr B⟩

omit [DecidableEq α] in
lemma mapEquivEquiv_finset_eq (e : α ≃ β) (s : Finset α) :
    (s.map e.toEmbedding).map e.symm.toEmbedding = s := by
  rw [Finset.map_map]
  simp

@[simp]
lemma parts_mapEquiv_copy [DecidableEq β] (e : α ≃ β) {s s' : Finset α}
    (P : Finpartition s) (h : s = s') :
    (mapEquiv e (P.copy h)).parts = (mapEquiv e P).parts := by
  subst h
  rfl

/-- Reindexing a finite partition along `e` as an equivalence of partition types. -/
def mapEquivEquiv [DecidableEq β] (e : α ≃ β) (s : Finset α) :
    Finpartition s ≃ Finpartition (s.map e.toEmbedding) where
  toFun P := mapEquiv e P
  invFun Q := (mapEquiv e.symm Q).copy (mapEquivEquiv_finset_eq e s)
  left_inv P := by
    ext B
    simp only [Finpartition.copy_parts, mapEquivEquiv_parts_eq]
  right_inv Q := by
    ext B
    simp only [mapEquivEquiv_parts_eq' e Q, parts_mapEquiv_copy]

/-- Block products are natural under reindexing.

Informal proof: rewrite the parts with `parts_mapEquiv` and apply `Finset.prod_map`. -/
theorem blockProduct_mapEquiv [DecidableEq β] [CommMonoid R] (e : α ≃ β)
    {s : Finset α} (P : Finpartition s) (f : Finset β → R) :
    (P.mapEquiv e).blockProduct f = P.blockProduct (fun B ↦ f (B.map e.toEmbedding)) := by
  simp_rw [blockProduct, parts_mapEquiv]
  rw [Finset.prod_map]
  apply Finset.prod_congr rfl
  intro B _
  rfl

/-- The partition transform commutes with reindexing by an equivalence.

Informal proof: `mapEquiv e` is a bijection on partitions, and
`blockProduct_mapEquiv` identifies corresponding summands. -/
theorem partitionTransform_map [DecidableEq β] [CommSemiring R] (e : α ≃ β)
    (f : Finset β → R) (s : Finset α) :
    partitionTransform f (s.map e.toEmbedding) =
      partitionTransform (fun B ↦ f (B.map e.toEmbedding)) s := by
  simp_rw [partitionTransform]
  exact (mapEquivEquiv e s).sum_comp (fun Q ↦ Q.blockProduct f) ▸ (by
    apply Finset.sum_congr rfl
    intro P _
    exact blockProduct_mapEquiv e P f)

/-- The cumulant transform commutes with reindexing by an equivalence.

Informal proof: use the same partition bijection as `partitionTransform_map`; it preserves the
number of blocks, hence also `cumulantCoefficient`. -/
theorem cumulantTransform_map [DecidableEq β] [CommRing R] (e : α ≃ β)
    (f : Finset β → R) (s : Finset α) :
    cumulantTransform f (s.map e.toEmbedding) =
      cumulantTransform (fun B ↦ f (B.map e.toEmbedding)) s := by
  by_cases h : s = ∅
  · simp [cumulantTransform, h]
  · have h' : s.map e.toEmbedding ≠ ∅ := by simp [h]
    simp only [cumulantTransform, h, h', ↓reduceIte]
    exact (mapEquivEquiv e s).sum_comp (fun Q ↦ cumulantCoefficient Q * Q.blockProduct f) ▸ (by
      apply Finset.sum_congr rfl
      intro P _
      have card_eq : ((mapEquivEquiv e s) P).parts.card = P.parts.card := by
        change (mapEquiv e P).parts.card = P.parts.card
        rw [parts_mapEquiv, Finset.card_map]
      congr 1
      · change (-1 : R) ^ (((mapEquivEquiv e s) P).parts.card - 1) *
          (((mapEquivEquiv e s) P).parts.card - 1).factorial = _
        rw [card_eq]
        rfl
      · exact blockProduct_mapEquiv e P f)

/-- The block product of a bound partition factors over the outer partition.

Informal proof: expand `Finpartition.bind_parts` as a disjoint bi-union and use
`Finset.prod_biUnion`; disjointness is supplied by the outer partition.
(Source: Partition of a set, Wikipedia, https://en.wikipedia.org/wiki/Partition_of_a_set) -/
theorem blockProduct_bind [CommMonoid R] {s : Finset α} (P : Finpartition s)
    (Q : ∀ B ∈ P.parts, Finpartition B) (f : Finset α → R) :
    (P.bind Q).blockProduct f = ∏ B : P.parts, (Q B.1 B.2).blockProduct f := by
  simp_rw [blockProduct]
  rw [bind_parts, Finset.prod_biUnion]
  · apply Finset.prod_congr rfl
    intro B hB
    rfl
  · intro B _ C _ hBC
    dsimp [Function.onFun]
    apply Finset.disjoint_left.mpr
    intro X hXB hXC
    have h1 : X ⊆ B.1 := (Q B.1 B.2).subset hXB
    have h2 : X ⊆ C.1 := (Q C.1 C.2).subset hXC
    have h3 : X ⊆ B.1 ∩ C.1 := Finset.subset_inter h1 h2
    have hBC_ne : B.1 ≠ C.1 := Subtype.coe_ne_coe.mpr hBC
    have h4 : Disjoint B.1 C.1 := P.disjoint B.2 C.2 hBC_ne
    have h5 : B.1 ∩ C.1 = ∅ := Finset.disjoint_iff_inter_eq_empty.mp h4
    rw [h5] at h3
    have h6 : X = ∅ := Finset.subset_empty.mp h3
    subst h6
    have h7 : ∅ ∉ (Q B.1 B.2).parts := (Q B.1 B.2).bot_notMem
    exact h7 hXB

/-- Summing over refinements of every block factors as a product of partition transforms.

Informal proof: apply `blockProduct_bind`, then distribute the finite product over the independent
finite sums with `Fintype.prod_sum`.
(Source: Partition of a set, Wikipedia, https://en.wikipedia.org/wiki/Partition_of_a_set) -/
theorem partitionTransform_bind [CommSemiring R] {s : Finset α} (P : Finpartition s)
    (f : Finset α → R) :
    (∑ Q : ∀ B : P.parts, Finpartition B.1,
      (P.bind (fun B hB ↦ Q ⟨B, hB⟩)).blockProduct f) =
      ∏ B : P.parts, partitionTransform f B.1 := by
  simp_rw [blockProduct_bind, partitionTransform]
  exact Fintype.prod_sum (fun (B : P.parts) (q : Finpartition B.1) ↦ q.blockProduct f) |>.symm

/-- The partition transform inverts the cumulant transform for functions normalized at the empty
set.

Informal proof: expand both transforms, regroup nested partitions by `Finpartition.bind`, and apply
Möbius inversion on the partition lattice. The Möbius function of the partition lattice on
intervals of partitions is `(-1)^(k-1)(k-1)!`, which perfectly cancels the
factorial terms in the definition of the cumulant transform.
(Source: Theory of Möbius Functions, Rota (1964),
https://link.springer.com/article/10.1007/BF01899123) -/
theorem partitionTransform_cumulantTransform [CommRing R] (f : Finset α → R)
    (hf : f ∅ = 1) :
    partitionTransform (cumulantTransform f) = f := by
  sorry

/-- The cumulant transform inverts the partition transform for functions vanishing at the empty
set.

Informal proof: this is the converse direction of the same Möbius inversion on the partition
lattice.
The special value of `cumulantTransform` at the empty set agrees with the hypothesis `f ∅ = 0`.
(Source: Theory of Möbius Functions, Rota (1964),
https://link.springer.com/article/10.1007/BF01899123) -/
theorem cumulantTransform_partitionTransform [CommRing R] (f : Finset α → R)
    (hf : f ∅ = 0) :
    cumulantTransform (partitionTransform f) = f := by
  sorry

end Finpartition

end
