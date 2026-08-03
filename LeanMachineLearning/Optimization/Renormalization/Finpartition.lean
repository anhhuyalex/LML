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
    rw [ht, Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.2 ha_in)]
    simp [h_card]
  obtain ⟨b, hb_eq⟩ := Finset.card_eq_one.1 ht_card
  have hbt : b ∈ t := by rw [hb_eq]; simp
  have hb_in : b ∈ P.1.part a := (Finset.mem_sdiff.1 hbt).1
  have hb_ne : b ≠ a := by
    intro h
    exact (Finset.mem_sdiff.1 hbt).2 (by rw [h]; simp)
  use b
  have h_card_ab : ({a, b} : Finset α).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hb_ne.symm)]
    simp
  have h_eq_ab : P.1.part a = {a, b} := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      by_cases h : x = a
      · simp [h]
      · have hx_t : x ∈ t := by
          rw [ht]
          exact Finset.mem_sdiff.2 ⟨hx, by simpa using h⟩
        rw [hb_eq] at hx_t
        simp [hx_t]
    · rw [h_card, h_card_ab]
  constructor
  · exact ⟨P.1.subset h_mem hb_in, hb_ne, h_eq_ab⟩
  · intro c hc
    rcases hc with ⟨_, hc_ne, hc_eq⟩
    have : c ∈ t := by
      rw [ht]
      exact Finset.mem_sdiff.2 ⟨by rw [hc_eq]; simp, by simpa using hc_ne⟩
    rwa [hb_eq, Finset.mem_singleton] at this

/-- Add a fresh two-element block to a pairing.

Informal construction: extend the underlying finpartition by the disjoint block `{a, b}`.  The old
blocks remain pairs, and the new block has cardinality two because `a ≠ b`. -/
def Pairing.insertPair {s : Finset α} (P : Pairing s) {a b : α} (hab : a ≠ b)
    (ha : a ∉ s) (hb : b ∉ s) : Pairing (insert a (insert b s)) := by
  have h_disj : Disjoint s {a, b} := by
    simp [Finset.disjoint_iff_inter_eq_empty, ha, hb]
  have h_sup : s ∪ {a, b} = insert a (insert b s) := by
    simp
  refine ⟨P.1.extend (show ({a, b} : Finset α) ≠ ∅ by simp) h_disj h_sup, ?_⟩
  intro B hB
  simp only [Finpartition.extend_parts, Finset.mem_insert] at hB
  rcases hB with (rfl | hB)
  · simp [hab]
  · exact P.2 B hB

/-- The blocks of `insertPair` are the new pair together with the original blocks.

Informal proof: unfold the construction and use the `parts` theorem for
`Finpartition.extend`; freshness makes the union disjoint. -/
theorem Pairing.insertPair_parts {s : Finset α} (P : Pairing s) {a b : α} (hab : a ≠ b)
    (ha : a ∉ s) (hb : b ∉ s) :
    (P.insertPair hab ha hb).1.parts = insert {a, b} P.1.parts := by
  simp [insertPair, Finpartition.extend_parts]

/-- Change the carrier of a pairing to an equal finset. -/
noncomputable abbrev Pairing.copy {s t : Finset α} (P : Pairing s) (h : s = t) : Pairing t :=
  ⟨P.1.copy h, P.2⟩

/-- The data of the partner of `a` in `P`: the partner itself, its membership in `s.erase a`,
and the identity of the block containing `a`.  Bundling these as a subtype keeps the proof data
out of the signature of `Pairing.erasePair`, so equality of residual pairings does not require
proof irrelevance. -/
abbrev Pairing.PartnerData {s : Finset α} (P : Pairing s) (a : α) :=
  {b : α // b ∈ s.erase a ∧ P.1.part a = {a, b}}

/-- The residual pairing obtained by deleting the block `{a, b}` containing `a`.

The argument `pd : P.PartnerData a` identifies the partner `b = pd.1` of `a` together with the
identity of the block `P.1.part a = {a, b}`.  The parts of the result are exactly
`P.1.parts.erase {a, pd.1}` (see `Pairing.erasePair_parts`), so all blocks remain two-element
sets. -/
noncomputable abbrev Pairing.erasePair {s : Finset α} {a : α} (P : Pairing s) (ha : a ∈ s)
    (pd : P.PartnerData a) : Pairing ((s.erase a).erase pd.1) := by
  refine ⟨Finpartition.ofExistsUnique (P.1.parts.erase {a, pd.1}) ?_ ?_ ?_, ?_⟩
  · -- every remaining part avoids both `a` and `pd.1`, hence stays inside the residual carrier
    intro p hp
    rcases Finset.mem_erase.mp hp with ⟨hp_ne, hp_mem⟩
    intro x hx
    have hx_s : x ∈ s := P.1.subset hp_mem hx
    have hx_ne_a : x ≠ a := by
      intro hxa
      subst x
      exact hp_ne ((P.1.part_eq_of_mem hp_mem hx).symm.trans pd.2.2)
    have hx_ne_b : x ≠ pd.1 := by
      intro hxb
      subst x
      have hb_mem_part : pd.1 ∈ P.1.part a := by
        simp [pd.2.2]
      exact hp_ne ((P.1.eq_of_mem_parts hp_mem (P.1.part_mem.2 ha) hx hb_mem_part).trans pd.2.2)
    exact Finset.mem_erase.mpr ⟨hx_ne_b, Finset.mem_erase.mpr ⟨hx_ne_a, hx_s⟩⟩
  · -- every element of the residual carrier lies in exactly one remaining part
    intro x hx
    rcases Finset.mem_erase.mp hx with ⟨hx_ne_b, hx_sa⟩
    rcases Finset.mem_erase.mp hx_sa with ⟨hx_ne_a, hx_s⟩
    obtain ⟨t, ht1, ht_uniq⟩ := P.1.existsUnique_mem hx_s
    rcases ht1 with ⟨ht_mem, ht_x⟩
    have ht_ne : t ≠ {a, pd.1} := by
      intro ht
      have : x ∈ ({a, pd.1} : Finset α) := by
        rw [← ht]
        exact ht_x
      rcases Finset.mem_insert.mp this with (hxa | hxb)
      · exact hx_ne_a hxa
      · exact hx_ne_b (Finset.mem_singleton.mp hxb)
    refine ⟨t, ⟨Finset.mem_erase.mpr ⟨ht_ne, ht_mem⟩, ht_x⟩, ?_⟩
    intro u hu
    exact ht_uniq u ⟨(Finset.mem_erase.mp hu.1).2, hu.2⟩
  · -- the empty set is not a remaining part
    intro h
    exact P.1.bot_notMem (Finset.mem_erase.mp h).2
  · -- deleting a two-element block preserves the pairing property
    intro B hB
    exact P.2 B (Finset.mem_erase.mp hB).2

@[simp]
lemma Pairing.erasePair_parts {s : Finset α} {a : α} (P : Pairing s) (ha : a ∈ s)
    (pd : P.PartnerData a) :
    (P.erasePair ha pd).1.parts = P.1.parts.erase {a, pd.1} := rfl

/-- Reconstruct a pairing of `s` from the partner `b` of `a` and a pairing of the residual set.

This is the inverse of `Pairing.erasePair`: it inserts the fresh block `{a, b}` into `Q` using
`Pairing.insertPair` and then changes the carrier from `insert a (insert b ((s.erase a).erase b))`
back to `s`. -/
noncomputable abbrev Pairing.insertErasedPair (s : Finset α) (a : α) (ha : a ∈ s)
    (b : {b : α // b ∈ s.erase a}) (Q : Pairing ((s.erase a).erase b.1)) : Pairing s :=
  (Q.insertPair (Finset.mem_erase.mp b.2).1.symm (by simp) (by simp)).copy (by
    -- inserting `b` recovers `s.erase a`, and inserting `a` recovers `s`
    rw [Finset.insert_erase b.2, Finset.insert_erase ha])

@[simp]
lemma Pairing.insertErasedPair_parts (s : Finset α) (a : α) (ha : a ∈ s)
    (b : {b : α // b ∈ s.erase a}) (Q : Pairing ((s.erase a).erase b.1)) :
    (insertErasedPair s a ha b Q).1.parts = insert {a, b.1} Q.1.parts := by
  simp [insertPair_parts]

/-- The block product of a reconstructed pairing factors into the new pair and the residual. -/
lemma Pairing.blockProduct_insertErasedPair [CommMonoid R] (s : Finset α) (a : α) (ha : a ∈ s)
    (b : {b : α // b ∈ s.erase a}) (Q : Pairing ((s.erase a).erase b.1)) (f : Finset α → R) :
    (insertErasedPair s a ha b Q).blockProduct f = f {a, b.1} * Q.blockProduct f := by
  -- the new block `{a, b.1}` is not among the old parts, so `Finset.prod_insert` applies
  have hnot : {a, b.1} ∉ Q.1.parts := by
    intro h
    have : a ∈ (s.erase a).erase b.1 := Q.1.subset h (by simp)
    simp at this
  unfold Pairing.blockProduct Finpartition.blockProduct
  rw [insertErasedPair_parts, Finset.prod_insert hnot]

/-- The partner data of `a` in `P`, obtained from `Pairing.existsUnique_partner`. -/
noncomputable def Pairing.partnerData {s : Finset α} {a : α} (P : Pairing s) (ha : a ∈ s) :
    P.PartnerData a := by
  refine ⟨Classical.choose (P.existsUnique_partner ha), ?_⟩
  rcases Classical.choose_spec (P.existsUnique_partner ha) with ⟨⟨hb, hne, hpart⟩, _⟩
  exact ⟨Finset.mem_erase.mpr ⟨hne, hb⟩, hpart⟩

/-- The partner of `a` in `P`, as an element of `s.erase a` (the projection of `partnerData`). -/
noncomputable abbrev Pairing.partner {s : Finset α} {a : α} (P : Pairing s) (ha : a ∈ s) :
    {b : α // b ∈ s.erase a} :=
  ⟨(P.partnerData ha).1, (P.partnerData ha).2.1⟩

/-- The partner of `a` is the unique element satisfying the given partner data. -/
lemma Pairing.partnerData_eq {s : Finset α} {a : α} (P : Pairing s) (ha : a ∈ s) {b : α}
    (hb : b ∈ s) (hne : b ≠ a) (hpart : P.1.part a = {a, b}) :
    P.partnerData ha = ⟨b, Finset.mem_erase.mpr ⟨hne, hb⟩, hpart⟩ := by
  rcases Classical.choose_spec (P.existsUnique_partner ha) with ⟨_, huniq⟩
  exact Subtype.ext (huniq b ⟨hb, hne, hpart⟩).symm

/-- A pairing of `s` is determined by the partner `b` of `a` and the residual pairing.

`toFun` deletes the block containing `a` (via `Pairing.erasePair`), and `invFun` reconstructs it
(via `Pairing.insertErasedPair`).  The two maps are inverse because the block containing `a` is
unique. -/
noncomputable def Pairing.eraseEquiv (s : Finset α) (a : α) (ha : a ∈ s) :
    Pairing s ≃ Σ b : {b : α // b ∈ s.erase a}, Pairing ((s.erase a).erase b) where
  toFun P := ⟨P.partner ha, P.erasePair ha (P.partnerData ha)⟩
  invFun x := Pairing.insertErasedPair s a ha x.1 x.2
  left_inv P := by
    -- deleting the block containing `a` and reinserting it recovers the original parts
    change (Pairing.insertErasedPair s a ha
      (⟨(P.partnerData ha).1, (P.partnerData ha).2.1⟩ : {b : α // b ∈ s.erase a})
      (P.erasePair ha (P.partnerData ha))) = P
    apply Subtype.ext
    ext B
    have hmem : {a, (P.partnerData ha).1} ∈ P.1.parts := by
      rw [← (P.partnerData ha).2.2]
      exact P.1.part_mem.2 ha
    rw [insertErasedPair_parts, erasePair_parts, Finset.insert_erase hmem]
  right_inv x := by
    -- the partner of `a` in the reconstructed pairing is `b`, and the residual is `Q`
    rcases x with ⟨b, Q⟩
    have hb_ne_a : b.1 ≠ a := (Finset.mem_erase.mp b.2).1
    have hb_mem_s : b.1 ∈ s := (Finset.mem_erase.mp b.2).2
    have hR_part : (insertErasedPair s a ha b Q).1.part a = {a, b.1} := by
      -- the block of `a` in the reconstructed pairing is the freshly inserted pair
      apply Finpartition.part_eq_of_mem
      · rw [insertErasedPair_parts]
        simp
      · simp
    have hpd : (insertErasedPair s a ha b Q).partnerData ha =
        ⟨b.1, Finset.mem_erase.mpr ⟨hb_ne_a, hb_mem_s⟩, hR_part⟩ :=
      Pairing.partnerData_eq (insertErasedPair s a ha b Q) ha hb_mem_s hb_ne_a hR_part
    have hQ_eq : (insertErasedPair s a ha b Q).erasePair ha
        ⟨b.1, Finset.mem_erase.mpr ⟨hb_ne_a, hb_mem_s⟩, hR_part⟩ = Q := by
      -- the residual parts are `(insertErasedPair ...).1.parts.erase {a, b.1}` = `Q.1.parts`
      apply Subtype.ext
      ext B
      have hnot : {a, b.1} ∉ Q.1.parts := by
        intro h
        have : a ∈ (s.erase a).erase b.1 := Q.1.subset h (by simp)
        simp at this
      simp [insertPair_parts, Finset.erase_insert hnot]
    have hb_val :
        (⟨b.1, Finset.mem_erase.mpr ⟨hb_ne_a, hb_mem_s⟩⟩ : {x : α // x ∈ s.erase a}) = b :=
      Subtype.ext rfl
    -- unfold the forward map: the partner of `a` is `b.1` and the residual is `Q`
    change (⟨(insertErasedPair s a ha b Q).partner ha,
      (insertErasedPair s a ha b Q).erasePair ha ((insertErasedPair s a ha b Q).partnerData ha)⟩ :
        Σ b : {b : α // b ∈ s.erase a}, Pairing ((s.erase a).erase b)) = ⟨b, Q⟩
    apply Sigma.ext
    · -- the partner of `a` in the reconstructed pairing is `b.1`
      simp [Pairing.partner, hpd, hb_val]
    · -- the residual pairing is `Q`
      change (insertErasedPair s a ha b Q).erasePair ha
        ((insertErasedPair s a ha b Q).partnerData ha) ≍ Q
      rw [hpd, hQ_eq]

/-- Auxiliary form of the recursive decomposition of pairings by a distinguished element.

Informal proof: send a pairing `P` of `s` to the unique partner `b` of `a` in `P`
(together with `b ∈ s.erase a`) and to the residual pairing obtained by deleting the block
`{a, b}`.  The inverse sends a partner `b ∈ s.erase a` and a residual pairing of
`(s.erase a).erase b` to the pairing obtained by adjoining the fresh block `{a, b}`; the
freshness hypotheses required by `Pairing.insertPair` are immediate from membership in the erased
set.  Under the resulting equivalence `Pairing.eraseEquiv`, `Pairing.insertErasedPair_parts`
identifies the parts as `insert {a, b} Q.1.parts`, so the block product factors as
`f {a, b} * Q.blockProduct f`.  Reindexing the finite sum over the equivalence and using
`Finset.mul_sum` gives the displayed identity.

This is the standard "choose the partner of a fixed vertex" recursion for perfect matchings;
see the proof of the recurrence for perfect matchings of a complete graph at
<https://en.wikipedia.org/wiki/Perfect_matching>. -/
theorem pairingSum_erase_aux {R : Type*} [CommSemiring R] (f : Finset α → R)
    (s : Finset α) {a : α} (ha : a ∈ s) :
    pairingSum f s =
      ∑ b ∈ s.erase a, f {a, b} * pairingSum f ((s.erase a).erase b) := by
  -- Step 1: reindex the pairing sum along the erase equivalence
  calc
    pairingSum f s = ∑ P : Pairing s, P.blockProduct f := rfl
    _ = ∑ x : Σ b : {b : α // b ∈ s.erase a}, Pairing ((s.erase a).erase b),
          ((Pairing.eraseEquiv s a ha).symm x).blockProduct f :=
      ((Pairing.eraseEquiv s a ha).symm.sum_comp (fun P : Pairing s ↦ P.blockProduct f)).symm
    _ = ∑ b : {b : α // b ∈ s.erase a},
          ∑ Q : Pairing ((s.erase a).erase b), f {a, b.1} * Q.blockProduct f := by
      -- the block product of the reconstructed pairing splits over the fresh block
      have hsummand :
          ∀ x : Σ b : {b : α // b ∈ s.erase a}, Pairing ((s.erase a).erase b),
            ((Pairing.eraseEquiv s a ha).symm x).blockProduct f =
              f {a, x.1.1} * x.2.blockProduct f := fun x =>
        Pairing.blockProduct_insertErasedPair s a ha x.1 x.2 f
      simp only [hsummand]
      exact Fintype.sum_sigma
        (fun x : Σ b : {b : α // b ∈ s.erase a}, Pairing ((s.erase a).erase b) ↦
          f {a, x.1.1} * x.2.blockProduct f)
    _ = ∑ b ∈ s.erase a, f {a, b} * pairingSum f ((s.erase a).erase b) := by
      -- reindex the subtype-indexed sum as a bounded sum over `s.erase a`
      rw [Finset.sum_coe_sort (s.erase a) (fun b : α ↦ (∑ Q : Pairing ((s.erase a).erase b),
        f {a, b} * Q.blockProduct f))]
      -- unfold `pairingSum` on the right and factor `f {a, b}` out of each inner sum
      simp [pairingSum, Finset.mul_sum]

/-- Decompose the pairing sum by choosing the partner of a distinguished element.

Informal proof: Every perfect matching of `s` pairs a distinguished element `a ∈ s` with a unique
element `b ∈ s \ {a}`. Thus, the sum over all pairings of `s` equals the sum over all `b ∈ s \ {a}`
of the block weight `f {a, b}` multiplied by the sum over all pairings of `s \ {a, b}`.
This formalizes the recursive structure of perfect matchings. (Source: Perfect matching, Wikipedia, https://en.wikipedia.org/wiki/Perfect_matching) -/
theorem pairingSum_erase {R : Type*} [CommSemiring R] (f : Finset α → R)
    (s : Finset α) {a : α} (ha : a ∈ s) :
    pairingSum f s =
      ∑ b ∈ s.erase a, f {a, b} * pairingSum f ((s.erase a).erase b) :=
  pairingSum_erase_aux f s ha

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

/-- Delete the block `B` from a partition of `s`, leaving a partition of `s \ B`.

This is the inverse of `insertBlock`: the remaining parts are the original parts with `B` removed,
and they cover exactly `s \ B` because `B` is a part. -/
private def deleteBlock {s : Finset α} (P : Finpartition s) (B : Finset α)
    (hB : B ∈ P.parts) : Finpartition (s \ B) := by
  refine ofExistsUnique (P.parts.erase B) ?_ ?_ ?_
  · -- every remaining part stays inside `s \ B`: a point of it cannot lie in `B`
    intro C hC
    rw [Finset.mem_erase] at hC
    intro x hx
    exact Finset.mem_sdiff.mpr ⟨P.subset hC.2 hx, by
      intro hxB
      exact hC.1 (P.eq_of_mem_parts hC.2 hB hx hxB)⟩
  · -- each element of `s \ B` lies in the unique remaining part that contained it
    intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hx_s, hx_nB⟩
    obtain ⟨C, hC, hxC⟩ := P.existsUnique_mem hx_s
    refine ⟨C, ⟨Finset.mem_erase.mpr ⟨?_, hC.1⟩, hC.2⟩, ?_⟩
    · intro hC_eq
      exact hx_nB (by simpa [hC_eq] using hC.2)
    · -- any other remaining part containing `x` equals `C` by uniqueness in `P`
      intro D hD
      rcases hD with ⟨hD_mem, hxD⟩
      exact hxC D ⟨(Finset.mem_erase.mp hD_mem).2, hxD⟩
  · -- `∅` is not a remaining part
    intro h
    exact P.empty_notMem_parts (Finset.mem_erase.mp h).2

/-- Insert a new block `B` into a partition of `s \ B`, giving a partition of `s`.

This is the inverse of `deleteBlock`: the new part `B` is added to the parts of `Q`, and the
resulting parts cover `s = B ∪ (s \ B)`. -/
private def insertBlock {s : Finset α} (B : Finset α) (hBne : B ≠ ∅)
    (hBsub : B ⊆ s) (Q : Finpartition (s \ B)) : Finpartition s := by
  refine ofExistsUnique (insert B Q.parts) ?_ ?_ ?_
  · -- every part (the new block or an old block) is contained in `s`
    intro C hC
    rcases Finset.mem_insert.mp hC with (rfl | hC)
    · exact hBsub
    · intro x hx
      exact (Finset.mem_sdiff.mp (Q.subset hC hx)).1
  · -- each element of `s` lies in the new block or in the unique old block containing it
    intro x hx
    by_cases hx_B : x ∈ B
    · refine ⟨B, ⟨by simp, hx_B⟩, ?_⟩
      intro C hC
      rcases hC with ⟨hC_mem, hxC⟩
      rcases Finset.mem_insert.mp hC_mem with (rfl | hC_mem)
      · rfl
      · exfalso
        exact (Finset.mem_sdiff.mp (Q.subset hC_mem hxC)).2 hx_B
    · have hx_sB : x ∈ s \ B := Finset.mem_sdiff.mpr ⟨hx, hx_B⟩
      obtain ⟨C, hC, hxC⟩ := Q.existsUnique_mem hx_sB
      refine ⟨C, ⟨by simp [hC.1], hC.2⟩, ?_⟩
      intro D hD
      rcases hD with ⟨hD_mem, hxD⟩
      rcases Finset.mem_insert.mp hD_mem with (rfl | hD_mem)
      · exfalso
        exact hx_B (by simpa using hxD)
      · exact hxC D ⟨hD_mem, hxD⟩
  · -- `∅` is not a part: neither the new block (nonempty) nor an old part
    intro h
    rcases Finset.mem_insert.mp h with (hB | hbot)
    · exact hBne hB.symm
    · exact Q.empty_notMem_parts hbot

/-- The parts of `insertBlock` are the new block together with the old parts. -/
private lemma insertBlock_parts {s : Finset α} (B : Finset α) (hBne : B ≠ ∅)
    (hBsub : B ⊆ s) (Q : Finpartition (s \ B)) :
    (Q.insertBlock B hBne hBsub).parts = insert B Q.parts := rfl

/-- The parts of `deleteBlock` are the original parts with `B` removed. -/
private lemma deleteBlock_parts {s : Finset α} (P : Finpartition s) (B : Finset α)
    (hB : B ∈ P.parts) :
    (P.deleteBlock B hB).parts = P.parts.erase B := rfl

/-- Deleting the block containing `a` and then reinserting it recovers the partition. -/
private lemma insertBlock_deleteBlock {s : Finset α} (P : Finpartition s)
    (a : α) (ha : a ∈ s) :
    (P.deleteBlock (P.part a) (P.part_mem.2 ha)).insertBlock (P.part a)
      (by exact P.ne_empty (P.part_mem.2 ha)) (P.part_subset a) = P := by
  apply Finpartition.ext
  ext B
  change B ∈ insert (P.part a) (P.parts.erase (P.part a)) ↔ B ∈ P.parts
  by_cases h : B = P.part a
  · -- `B` is the distinguished block: present on both sides
    simp [h]
    exact ha
  · -- any other part of the rebuilt partition is an original part and conversely
    simp [h]

/-- In a reinserted partition, the block containing `a` is the new block `B`. -/
private lemma insertBlock_part_of_mem {s : Finset α} (B : Finset α) (hBne : B ≠ ∅)
    (hBsub : B ⊆ s) (Q : Finpartition (s \ B)) (a : α) (hBa : a ∈ B) :
    (Q.insertBlock B hBne hBsub).part a = B := by
  apply part_eq_of_mem
  · change B ∈ insert B Q.parts
    simp
  · exact hBa

/-- Casting a partition along a carrier equality preserves its parts. -/
private lemma cast_congrArg_parts (t u : Finset α) (h : t = u) (Q : Finpartition t) :
    (cast (congrArg Finpartition h) Q).parts = Q.parts := by
  cases h
  rfl

/-- Reinserting a block and deleting the block containing `a` recovers the original partition.

The residual carriers (`s \ B` versus `s \ (insertBlock ...).part a`) differ only by the equality
`(insertBlock ...).part a = B`, so the two residual partitions are heterogeneously equal. -/
private lemma deleteBlock_insertBlock {s : Finset α} (B : Finset α) (hBne : B ≠ ∅)
    (hBsub : B ⊆ s) (Q : Finpartition (s \ B)) (a : α) (ha : a ∈ s) (hBa : a ∈ B) :
    (Q.insertBlock B hBne hBsub).deleteBlock ((Q.insertBlock B hBne hBsub).part a)
      ((Q.insertBlock B hBne hBsub).part_mem.2 ha) ≍ Q := by
  have hX1 : (Q.insertBlock B hBne hBsub).part a = B :=
    insertBlock_part_of_mem B hBne hBsub Q a hBa
  -- cast `Q` to the residual carrier and compare parts (the membership proof is not rewritten)
  refine heq_of_eq_cast ?e ?h
  · exact congrArg Finpartition (congrArg (fun t : Finset α => s \ t) hX1).symm
  · apply Finpartition.ext
    ext C
    rw [cast_congrArg_parts (s \ B) (s \ (Q.insertBlock B hBne hBsub).part a)
      (congrArg (fun t : Finset α => s \ t) hX1).symm]
    simp [deleteBlock_parts, insertBlock_parts]
    rw [hX1]
    by_cases h : C = B
    · -- the new block is deleted, so it is absent from the residual parts
      simp [h]
      intro hBQ
      -- `B ∈ Q.parts` would force `B ⊆ s \ B`, hence `B = ∅`, contradicting nonemptiness
      have hBempty : B = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro x hx
        exact (Finset.mem_sdiff.mp (Q.subset hBQ hx)).2 hx
      exact hBne hBempty
    · -- old blocks are kept exactly
      simp [h]

/-- The block product factors over the block containing `a` and the remaining blocks. -/
private lemma blockProduct_deleteBlock [CommMonoid R] {s : Finset α} (P : Finpartition s)
    (g : Finset α → R) (a : α) (ha : a ∈ s) :
    P.blockProduct g = g (P.part a) * (P.deleteBlock (P.part a) (P.part_mem.2 ha)).blockProduct g := by
  rw [blockProduct, blockProduct, deleteBlock_parts]
  rw [← Finset.insert_erase (P.part_mem.2 ha)]
  rw [Finset.prod_insert]
  · simp
  · simp

/-- Add a new block `D` to a partition of `B`, giving a partition of `B ∪ D`.

This is `Finpartition.extend` specialised to finsets: the carrier becomes `s` via `B ∪ D = s`. -/
private def Finpartition.extendBlock {s B D : Finset α} (Q : Finpartition B) (hDne : D ≠ ∅)
    (hdisj : Disjoint B D) (hsup : B ∪ D = s) : Finpartition s :=
  Q.extend hDne hdisj hsup

/-- The parts of `extendBlock` are the new block together with the old parts. -/
private lemma Finpartition.extendBlock_parts {s B D : Finset α} (Q : Finpartition B)
    (hDne : D ≠ ∅) (hdisj : Disjoint B D) (hsup : B ∪ D = s) :
    (Q.extendBlock hDne hdisj hsup).parts = insert D Q.parts := rfl

/-- The block product of an extended partition factors over the new block. -/
private lemma blockProduct_extendBlock [CommMonoid R] {s B D : Finset α} (Q : Finpartition B)
    (hDne : D ≠ ∅) (hdisj : Disjoint B D) (hsup : B ∪ D = s) (f : Finset α → R) :
    (Q.extendBlock hDne hdisj hsup).blockProduct f = f D * Q.blockProduct f := by
  rw [blockProduct, blockProduct, extendBlock_parts]
  rw [Finset.prod_insert]
  · rfl
  · -- `D ∉ Q.parts`: `D ⊆ B` would contradict `Disjoint B D` unless `D = ∅`
    intro hD
    apply hDne
    apply Finset.eq_empty_iff_forall_notMem.2
    intro x hx
    exact (Finset.disjoint_left.mp hdisj (Q.subset hD hx)) hx

/-- Restricting a partition to `s \ D`, for a block `D`, deletes exactly that block. -/
private lemma Finpartition.restrict_parts_of_mem {s : Finset α} (T : Finpartition s) {D : Finset α}
    (hD : D ∈ T.parts) :
    (T.restrict (show s \ D ⊆ s by exact Finset.sdiff_subset)).parts = T.parts.erase D := by
  ext C
  constructor
  · intro hC
    rw [restrict, Finset.mem_erase, Finset.mem_image] at hC
    rcases hC with ⟨hC_ne, ⟨E, hE, hE_eq⟩⟩
    by_cases hED : E = D
    · -- `E = D` would make `E ∩ (s \ D) = ∅`, contradicting `C ≠ ∅`
      exfalso
      apply hC_ne
      rw [← hE_eq, hED]
      ext x
      simp
    · rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · -- `C ≠ D`, since `C = E` and `E ≠ D`
        intro hC_D
        apply hED
        symm
        -- `E ∩ (s \ D) = E`, so `C = E`
        rw [← hE_eq]
        apply Finset.inter_eq_left.2
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨T.subset hE hx, by
          intro hxD
          have : x ∈ E ∩ D := Finset.mem_inter.mpr ⟨hx, hxD⟩
          exact (Finset.disjoint_iff_inter_eq_empty.mp (T.disjoint hE hD hED)) ▸ (by simp at this)⟩
      · -- `C = E ∩ (s \ D)` is the image of `E ∈ T.parts`
        rw [← hE_eq]
        exact hE
  · intro hC
    rw [Finset.mem_erase] at hC
    rw [restrict, Finset.mem_erase]
    refine ⟨T.ne_empty hC.2, ?_⟩
    -- `C ∩ (s \ D) = C`, since `C` and `D` are distinct disjoint blocks
    exact Finset.mem_image.mpr ⟨C, hC.2, by
      apply Finset.inter_eq_left.2
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨T.subset hC.2 hx, by
        intro hxD
        have : x ∈ C ∩ D := Finset.mem_inter.mpr ⟨hx, hxD⟩
        exact (Finset.disjoint_iff_inter_eq_empty.mp (T.disjoint hC.2 hD hC.1)) ▸ (by simp at this)⟩⟩

/-- Extending and then restricting back to the original block recovers the partition. -/
private lemma restrict_extendBlock {s B D : Finset α} (Q : Finpartition B) (hDne : D ≠ ∅)
    (hdisj : Disjoint B D) (hsup : B ∪ D = s) (hBs : B ⊆ s) :
    ((Q.extendBlock hDne hdisj hsup).restrict (show B ⊆ s by exact hBs)) = Q := by
  apply Finpartition.ext
  ext C
  change C ∈ ((insert D Q.parts).image (fun E : Finset α => E ∩ B)).erase ∅ ↔ C ∈ Q.parts
  constructor
  · intro hC
    rw [Finset.mem_erase, Finset.mem_image] at hC
    rcases hC with ⟨hC_ne, ⟨E, hE, hE_eq⟩⟩
    rcases Finset.mem_insert.mp hE with (rfl | hE)
    · -- `E = D`: `D ∩ B = ∅` contradicts `C ≠ ∅`
      exfalso
      apply hC_ne
      rw [← hE_eq, Finset.inter_comm]
      exact Finset.disjoint_iff_inter_eq_empty.mp hdisj
    · -- `E ∈ Q.parts`: `E ∩ B = E`
      rw [← hE_eq]
      rw [Finset.inter_eq_left.2 (Q.subset hE)]
      exact hE
  · intro hC
    rw [Finset.mem_erase]
    refine ⟨Q.ne_empty hC, Finset.mem_image.mpr ⟨C, Finset.mem_insert_of_mem hC, ?_⟩⟩
    rw [Finset.inter_eq_left.2 (Q.subset hC)]

/-- The partition transform of the empty set is the empty product `1`. -/
private lemma partitionTransform_empty [CommSemiring R] (g : Finset α → R) :
    partitionTransform g ∅ = 1 := by
  classical
  have hbot : (∅ : Finset α) = ⊥ := by rfl
  rw [hbot]
  have hparts : (default : Finpartition (⊥ : Finset α)).parts = ∅ := by simp
  simpa [partitionTransform, blockProduct, hparts] using
    (Fintype.sum_unique (fun P : Finpartition (⊥ : Finset α) ↦ P.blockProduct g))

/-- The partition transform of the cumulant transform decomposes by the block containing `a`.

This is the induction step of the Möbius-inversion proof: a partition of `s` is determined by the
block `B` containing `a` and the induced partition of the complement `s \ B`, so the transform on
`s` splits into the `a`-block contribution times the transform on the complement.  Splitting off
the full block `B = s` (whose complement transform is `1`) yields the recursion used by
`partitionTransform_cumulantTransform_of_nonempty_mobius`. -/
private lemma partitionTransform_cumulantTransform_rec [CommRing R] (f : Finset α → R)
    (s : Finset α) (_hs : s ≠ ∅) (a : α) (ha : a ∈ s) :
    partitionTransform (cumulantTransform f) s =
      cumulantTransform f s +
        ∑ B ∈ s.powerset.filter (fun B => a ∈ B ∧ B ≠ s),
          cumulantTransform f B * partitionTransform (cumulantTransform f) (s \ B) := by
  classical
  let t : Finset (Finset α) := s.powerset.filter (fun B => a ∈ B)
  have hstep1 :
      partitionTransform (cumulantTransform f) s =
        ∑ B ∈ t, cumulantTransform f B * partitionTransform (cumulantTransform f) (s \ B) := by
    calc
      partitionTransform (cumulantTransform f) s
          = ∑ P : Finpartition s, P.blockProduct (cumulantTransform f) := rfl
      _ = ∑ x ∈ t.sigma (fun B => (Finset.univ : Finset (Finpartition (s \ B)))),
            cumulantTransform f x.1 * x.2.blockProduct (cumulantTransform f) := by
        -- reindex along the bijection `P ↦ (P.part a, deleteBlock ...)`
        rw [← Finset.sum_bij' (s := Finset.univ) (t := t.sigma (fun B => Finset.univ))
          (i := fun P _ => ⟨P.part a, P.deleteBlock (P.part a) (P.part_mem.2 ha)⟩)
          (j := fun x hx => x.2.insertBlock x.1
            (Finset.nonempty_iff_ne_empty.1 ⟨a, (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).2⟩)
            (Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).1))]
        · -- membership of the forward image in the sigma finset
          intro P hP
          exact Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_powerset.mpr (P.part_subset a), P.mem_part ha⟩, Finset.mem_univ _⟩
        · -- membership of the backward image in the partition finset
          intro x hx
          exact Finset.mem_univ _
        · -- deleting then reinserting the block containing `a` recovers `P`
          intro P hP
          exact insertBlock_deleteBlock P a ha
        · -- inserting then deleting recovers `⟨B, Q⟩`
          intro x hx
          rcases x with ⟨B, Q⟩
          have hBne : B ≠ ∅ := Finset.nonempty_iff_ne_empty.1
            ⟨a, (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).2⟩
          have hBsub : B ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).1
          have hBa : a ∈ B := (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).2
          apply Sigma.ext
          · exact insertBlock_part_of_mem B hBne hBsub Q a hBa
          · -- the residual partition after deleting the new block is `Q`
            exact deleteBlock_insertBlock B hBne hBsub Q a (hBsub hBa) hBa
        · -- the block products match: `P.blockProduct = K f (P.part a) * residual product`
          intro P hP
          exact blockProduct_deleteBlock P (cumulantTransform f) a ha
      _ = ∑ B ∈ t, cumulantTransform f B * partitionTransform (cumulantTransform f) (s \ B) := by
        -- convert the sigma sum over `B ∈ t` into the double sum
        rw [Finset.sum_sigma]
        apply Finset.sum_congr rfl
        intro B hB
        simp [partitionTransform, Finset.mul_sum]
  -- Step 2: split off the `B = s` summand, whose complement transform is `1`
  have hs_mem : s ∈ t := by
    simp [t, ha]
  calc
    partitionTransform (cumulantTransform f) s
        = ∑ B ∈ t, cumulantTransform f B * partitionTransform (cumulantTransform f) (s \ B) := hstep1
    _ = cumulantTransform f s + ∑ B ∈ t.erase s,
          cumulantTransform f B * partitionTransform (cumulantTransform f) (s \ B) := by
      -- `t = insert s (t.erase s)`, and the `B = s` summand is `K f s * S ∅ = K f s`
      nth_rw 1 [← Finset.insert_erase hs_mem]
      rw [Finset.sum_insert (Finset.notMem_erase _ _)]
      congr 1
      simp [partitionTransform_empty]
    _ = cumulantTransform f s +
          ∑ B ∈ s.powerset.filter (fun B => a ∈ B ∧ B ≠ s),
            cumulantTransform f B * partitionTransform (cumulantTransform f) (s \ B) := by
      congr 1
      -- `t.erase s` is exactly the filter with the extra condition `B ≠ s`
      rw [show t.erase s = s.powerset.filter (fun B => a ∈ B ∧ B ≠ s) by
        ext B
        by_cases hBs : B = s
        · simp [t, hBs, ha]
        · simp [t, hBs]]

/-- Möbius inversion kernel for the partition transform on nonempty carriers.

This lemma packages the only substantial combinatorial fact needed for moment--cumulant
inversion.  Expanding the left hand side produces a double sum over an outer partition and an
inner partition of each outer block.  The already-proved lemma `partitionTransform_bind` is the
formal API for this distribution/rebinding step: the choices of inner partitions glue to a single
refinement via `Finpartition.bind`, and `blockProduct_bind` identifies the corresponding block
products.  After regrouping by the glued partition `T`, the remaining scalar coefficient is the
classical partition-lattice Möbius interval sum
`∑ ρ, ∏ C ∈ ρ, (-1)^(|C|-1)(|C|-1)!`.  This sum is `1` when `T` is the one-block partition and
`0` otherwise; equivalently, it is the signed count of permutations by their cycle-support
partition, so for at least two cycles/elements cancellation is given by sign reversal under a
transposition.

References for the informal proof and the Möbius value: Rota, *On the foundations of
combinatorial theory I. Theory of Möbius functions*, Z. Wahrscheinlichkeitstheorie verw. Gebiete 2
(1964), and Stanley, *Enumerative Combinatorics I*, 2nd ed., Example 3.10.4.  The project
blueprint records this as the partition-inversion theorem in
`blueprint/src/chapters/renormalization.tex`, `thm:renorm:partitionInversion`. -/
private theorem partitionTransform_cumulantTransform_of_nonempty_mobius [CommRing R]
    (f : Finset α → R) {s : Finset α} (hs : s ≠ ∅) :
    partitionTransform (cumulantTransform f) s = f s := by
  classical
  -- Step 1: unfold the outer transform.  Because every block of a `Finpartition` is nonempty
  -- (`Finpartition.bot_notMem`), every inner `cumulantTransform f B` uses its nonempty branch.
  -- Step 2: distribute products of inner sums over the outer blocks and glue the chosen inner
  -- partitions with `Finpartition.bind`; the local API lemmas `partitionTransform_bind` and
  -- `blockProduct_bind` are designed for exactly this reindexing.
  -- Step 3: apply the classical Möbius cancellation on the interval above each glued partition.
  -- Only the indiscrete partition of the nonempty set `s` survives, and its block product is `f s`.
  sorry

/-- Nonempty-set part of moment-cumulant inversion for finite partitions.

Informal proof: for `s ≠ ∅`, expand `partitionTransform (cumulantTransform f) s`.  Since every
block of a `Finpartition` is nonempty (`Finpartition.bot_notMem`), every occurrence of
`cumulantTransform f B` unfolds to the signed sum defining the Möbius transform.  Distributing the
product of these sums over the blocks of an outer partition and using `Finpartition.bind` identifies
such data with a refinement of the outer partition.  Regrouping by the resulting bound partition
leaves, for each partition `T`, the standard interval Möbius sum in the partition lattice.  The
coefficient `(-1)^(k-1)(k-1)!` is the classical Möbius value of the interval from a `k`-block
partition to the indiscrete partition; hence all partitions cancel except the indiscrete partition,
whose remaining block product is `f s`.

References: Rota, *On the foundations of combinatorial theory I. Theory of Möbius functions*,
Z. Wahrscheinlichkeitstheorie verw. Gebiete 2 (1964), and Stanley, *Enumerative Combinatorics I*,
Prop. 3.10.1 for the Möbius value of the partition lattice. -/
theorem partitionTransform_cumulantTransform_of_nonempty [CommRing R] (f : Finset α → R)
    {s : Finset α} (hs : s ≠ ∅) :
    partitionTransform (cumulantTransform f) s = f s := by
  exact partitionTransform_cumulantTransform_of_nonempty_mobius f hs

-- The empty carrier is a self-contained edge case: the only partition is the empty one, whose
-- block product is the empty product `1`, equal to `f ∅` by the normalization hypothesis `hf`.
-- Used as the `s = ∅` branch of `partitionTransform_cumulantTransform`.
private lemma partitionTransform_cumulantTransform_empty [CommRing R] (f : Finset α → R)
    (hf : f ∅ = 1) :
    partitionTransform (cumulantTransform f) ⊥ = f ⊥ := by
  have hparts : (default : Finpartition (⊥ : Finset α)).parts = ∅ := by simp
  simpa [partitionTransform, blockProduct, hf, hparts] using Fintype.sum_unique
    (fun P : Finpartition (⊥ : Finset α) ↦ P.blockProduct (cumulantTransform f))

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
  funext s
  rcases eq_or_ne s ∅ with rfl | hs
  · -- empty carrier: both transforms collapse to the single empty product, equal to `f ∅ = 1`
    exact partitionTransform_cumulantTransform_empty f hf
  · -- nonempty carrier: deferred to the Möbius-inversion identity for nonempty sets
    exact partitionTransform_cumulantTransform_of_nonempty f hs

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
