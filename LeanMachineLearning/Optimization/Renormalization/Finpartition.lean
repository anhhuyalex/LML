/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Data.Fintype.Perm

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

The declarations used from the pinned Mathlib revision were checked in: `Finpartition.map`,
`Finpartition.bind`, `Finpartition.bind_parts`, `Finpartition.mem_bind`, `Finpartition.card_bind`,
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
      (P.ne_empty (P.part_mem.2 ha)) (P.part_subset a) = P := by
  apply Finpartition.ext
  ext B
  change B ∈ insert (P.part a) (P.parts.erase (P.part a)) ↔ B ∈ P.parts
  by_cases h : B = P.part a
  · -- `B` is the distinguished block: present on both sides
    subst B
    constructor
    · intro _
      exact P.part_mem.2 ha
    · intro _
      exact Finset.mem_insert.mpr (Or.inl rfl)
  · -- any other part of the rebuilt partition is an original part and conversely
    constructor
    · intro hB
      exact (Finset.mem_erase.mp (Finset.mem_insert.mp hB |>.resolve_left h)).2
    · intro hB
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨h, hB⟩))

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
    rw [deleteBlock_parts, insertBlock_parts]
    rw [hX1]
    by_cases h : C = B
    · -- the new block is deleted, so it is absent from the residual parts
      subst C
      constructor
      · intro hC
        exact False.elim ((Finset.mem_erase.mp hC).1 rfl)
      · intro hBQ
        -- `B ∈ Q.parts` would force `B ⊆ s \ B`, hence `B = ∅`, contradicting nonemptiness
        exact False.elim (hBne (Finset.eq_empty_iff_forall_notMem.2
          (fun x hx => (Finset.mem_sdiff.mp (Q.subset hBQ hx)).2 hx)))
    · -- old blocks are kept exactly
      constructor
      · intro hC
        exact (Finset.mem_insert.mp (Finset.mem_erase.mp hC).2).resolve_left h
      · intro hC
        exact Finset.mem_erase.mpr ⟨h, Finset.mem_insert.mpr (Or.inr hC)⟩

/-- The block product factors over the block containing `a` and the remaining blocks. -/
private lemma blockProduct_deleteBlock [CommMonoid R] {s : Finset α} (P : Finpartition s)
    (g : Finset α → R) (a : α) (ha : a ∈ s) :
    P.blockProduct g =
      g (P.part a) * (P.deleteBlock (P.part a) (P.part_mem.2 ha)).blockProduct g := by
  rw [blockProduct, blockProduct, deleteBlock_parts, ← Finset.insert_erase (P.part_mem.2 ha),
    Finset.prod_insert]
  · simp
  · simp

/-- Add a new block `D` to a partition of `B`, giving a partition of `B ∪ D`.

This is `Finpartition.extend` specialised to finsets: the carrier becomes `s` via `B ∪ D = s`. -/
private def extendBlock {s B D : Finset α} (Q : Finpartition B) (hDne : D ≠ ∅)
    (hdisj : Disjoint B D) (hsup : B ∪ D = s) : Finpartition s :=
  Q.extend hDne hdisj hsup

/-- The parts of `extendBlock` are the new block together with the old parts. -/
private lemma extendBlock_parts {s B D : Finset α} (Q : Finpartition B)
    (hDne : D ≠ ∅) (hdisj : Disjoint B D) (hsup : B ∪ D = s) :
    (Q.extendBlock hDne hdisj hsup).parts = insert D Q.parts := rfl

/-- The block product of an extended partition factors over the new block. -/
private lemma blockProduct_extendBlock [CommMonoid R] {s B D : Finset α} (Q : Finpartition B)
    (hDne : D ≠ ∅) (hdisj : Disjoint B D) (hsup : B ∪ D = s) (f : Finset α → R) :
    (Q.extendBlock hDne hdisj hsup).blockProduct f = f D * Q.blockProduct f := by
  rw [blockProduct, blockProduct, extendBlock_parts, Finset.prod_insert]
  · -- `D ∉ Q.parts`: `D ⊆ B` would contradict `Disjoint B D` unless `D = ∅`
    intro hD
    exact hDne (Finset.eq_empty_iff_forall_notMem.2
      (fun x hx => (Finset.disjoint_left.mp hdisj (Q.subset hD hx)) hx))

/-- Distinct blocks of a partition stay unchanged when intersected with the complement of another
block: the blocks are disjoint, and both lie inside the carrier. -/
private lemma inter_sdiff_self_of_mem {s : Finset α} {T : Finpartition s} {D E : Finset α}
    (hE : E ∈ T.parts) (hD : D ∈ T.parts) (hED : E ≠ D) :
    E ⊓ (s \ D) = E :=
  Finset.inter_eq_left.2 (fun _ hx => Finset.mem_sdiff.mpr ⟨T.subset hE hx, fun hxD =>
    (Finset.disjoint_left.mp (T.disjoint hE hD hED)) hx hxD⟩)

/-- Restricting a partition to `s \ D`, for a block `D`, deletes exactly that block. -/
private lemma Finpartition.restrict_parts_of_mem {s : Finset α} (T : Finpartition s) {D : Finset α}
    (hD : D ∈ T.parts) :
    (T.restrict (Finset.sdiff_subset : s \ D ⊆ s)).parts = T.parts.erase D := by
  ext C
  constructor
  · intro hC
    rw [restrict, Finset.mem_erase, Finset.mem_image] at hC
    rcases hC with ⟨hC_ne, ⟨E, hE, hE_eq⟩⟩
    by_cases hED : E = D
    · -- `E = D` would make `E ∩ (s \ D) = ∅`, contradicting `C ≠ ∅`
      exfalso
      exact hC_ne (by rw [← hE_eq, hED]; ext x; simp)
    · rw [Finset.mem_erase]
      constructor
      · -- `C ≠ D`: `C = E` and `E ≠ D`
        intro hC_D
        exact hED ((show C = E by rw [← hE_eq, inter_sdiff_self_of_mem hE hD hED]).symm.trans hC_D)
      · -- `C = E ∩ (s \ D)` is the image of the part `E`
        rwa [show C = E by rw [← hE_eq, inter_sdiff_self_of_mem hE hD hED]]
  · intro hC
    rw [Finset.mem_erase] at hC
    rw [restrict, Finset.mem_erase]
    constructor
    · exact T.ne_empty hC.2
    · exact Finset.mem_image.mpr ⟨C, hC.2, inter_sdiff_self_of_mem hC.2 hD hC.1⟩

/-- Extending and then restricting back to the original block recovers the partition. -/
private lemma restrict_extendBlock {s B D : Finset α} (Q : Finpartition B) (hDne : D ≠ ∅)
    (hdisj : Disjoint B D) (hsup : B ∪ D = s) (hBs : B ⊆ s) :
    ((Q.extendBlock hDne hdisj hsup).restrict hBs) = Q := by
  apply Finpartition.ext
  ext C
  change C ∈ ((insert D Q.parts).image (fun E : Finset α => E ⊓ B)).erase ∅ ↔ C ∈ Q.parts
  constructor
  · intro hC
    rw [Finset.mem_erase, Finset.mem_image] at hC
    rcases hC with ⟨hC_ne, ⟨E, hE, hE_eq⟩⟩
    rcases Finset.mem_insert.mp hE with (rfl | hE)
    · -- `E = D`: `E ⊓ B = ∅` contradicts `C ≠ ∅`
      exfalso
      apply hC_ne
      rw [← hE_eq, Finset.inf_eq_inter, Finset.inter_comm]
      exact Finset.disjoint_iff_inter_eq_empty.mp hdisj
    · -- `E ∈ Q.parts`: `E ⊓ B = E`
      rw [← hE_eq, Finset.inf_eq_inter, Finset.inter_eq_left.2 (Q.subset hE)]
      exact hE
  · intro hC
    rw [Finset.mem_erase]
    refine ⟨Q.ne_empty hC, Finset.mem_image.mpr ⟨C, Finset.mem_insert_of_mem hC, ?_⟩⟩
    rw [Finset.inf_eq_inter, Finset.inter_eq_left.2 (Q.subset hC)]

/-- The indiscrete partition `⊤` is the unique partition with a single block. -/
private lemma Finpartition.eq_top_iff_card_parts_eq_one {s : Finset α} (T : Finpartition s)
    (hs : s ≠ ∅) : T = ⊤ ↔ T.parts.card = 1 := by
  classical
  -- the indiscrete partition has the single block `s`
  have hpartsT : (⊤ : Finpartition s).parts = {s} := by
    apply Finset.eq_singleton_iff_unique_mem.2
    constructor
    · rcases Finpartition.parts_nonempty (⊤ : Finpartition s) hs with ⟨B, hB⟩
      have hB_eq : B = s :=
        Finset.mem_singleton.mp (Finset.mem_of_subset (Finpartition.parts_top_subset s) hB)
      simpa [hB_eq] using hB
    · exact fun D hD =>
        Finset.mem_singleton.mp (Finset.mem_of_subset (Finpartition.parts_top_subset s) hD)
  constructor
  · intro h
    rw [h, hpartsT]
    simp
  · intro hcard
    -- a single block must be `s` itself, since the blocks cover `s`
    exact Finpartition.ext (by
      rcases Finset.card_eq_one.mp hcard with ⟨B, hB⟩
      rw [hB, show B = s by simpa [hB] using T.biUnion_parts]
      exact hpartsT.symm)

/-- The coefficient identity for the Möbius inversion on the partition lattice.

For a partition `T` of a nonempty set `s` and a distinguished element `a ∈ s`, the signed sum
`c T + Σ_{D ∈ T.parts, a ∉ D} c (T restricted to s \ D)` is `1` exactly when `T` is the one-block
partition `⊤`, and `0` otherwise.  For `k = |T.parts| ≥ 2` blocks the cancellation is the
telescoping identity `(-1)^(k-1)(k-1)! + (k-1)(-1)^(k-2)(k-2)! = 0`. -/
private lemma cumulantCoefficient_sum_coarser [CommRing R] (s : Finset α) (a : α) (ha : a ∈ s)
    (T : Finpartition s) :
    cumulantCoefficient T +
      ∑ D ∈ T.parts.filter (fun D => a ∉ D),
        cumulantCoefficient (T.restrict (Finset.sdiff_subset : s \ D ⊆ s)) =
      if T = ⊤ then (1 : R) else 0 := by
  classical
  have hs : s ≠ ∅ := Finset.nonempty_iff_ne_empty.1 ⟨a, ha⟩
  by_cases hT : T = ⊤
  · -- `T = ⊤`: single block `s`, no block avoids `a`, and `c (⊤) = 1`
    subst hT
    have hparts : (⊤ : Finpartition s).parts = {s} := by
      apply Finset.eq_singleton_iff_unique_mem.2
      constructor
      · rcases Finpartition.parts_nonempty (⊤ : Finpartition s) hs with ⟨B, hB⟩
        have hB_eq : B = s :=
          Finset.mem_singleton.mp (Finset.mem_of_subset (Finpartition.parts_top_subset s) hB)
        simpa [hB_eq] using hB
      · exact fun D hD =>
          Finset.mem_singleton.mp (Finset.mem_of_subset (Finpartition.parts_top_subset s) hD)
    -- the only block `s` contains `a`, so the filter over blocks avoiding `a` is empty
    have hfilter_empty : ({s} : Finset (Finset α)).filter (fun D => a ∉ D) = ∅ := by
      simp [ha]
    simp [hparts, hfilter_empty, cumulantCoefficient]
  · -- `T ≠ ⊤`: `k = |T.parts| ≥ 2` blocks, and the identity telescopes
    have hk : 2 ≤ T.parts.card := by
      have hne1 : T.parts.card ≠ 1 := fun h1 =>
        hT ((Finpartition.eq_top_iff_card_parts_eq_one T hs).2 h1)
      have hpos : 0 < T.parts.card :=
        Finset.card_pos.mpr (Finpartition.parts_nonempty T hs)
      omega
    set k := T.parts.card with hk_def
    -- the blocks avoiding `a` are exactly the blocks other than `T.part a`
    have hfilter : T.parts.filter (fun D => a ∉ D) = T.parts.erase (T.part a) := by
      ext D
      constructor
      · intro hD
        rw [Finset.mem_filter] at hD
        exact Finset.mem_erase.mpr ⟨fun h_eq => hD.2 (h_eq ▸ T.mem_part ha), hD.1⟩
      · intro hD
        rw [Finset.mem_erase] at hD
        exact Finset.mem_filter.mpr ⟨hD.2, fun haD =>
          hD.1 (T.eq_of_mem_parts hD.2 (T.part_mem.2 ha) haD (T.mem_part ha))⟩
    -- each restricted coefficient is the constant `(-1)^(k-2)(k-2)!`
    have hsummand : ∀ D ∈ T.parts.filter (fun D => a ∉ D),
        cumulantCoefficient (T.restrict (Finset.sdiff_subset : s \ D ⊆ s)) =
          (-1 : R) ^ (k - 2) * Nat.factorial (k - 2) := by
      intro D hD
      rw [Finset.mem_filter] at hD
      unfold cumulantCoefficient
      have hcard : (T.restrict (Finset.sdiff_subset : s \ D ⊆ s)).parts.card - 1 =
          k - 2 := by
        rw [Finpartition.restrict_parts_of_mem T hD.1, Finset.card_erase_of_mem hD.1, hk_def]
        omega
      rw [hcard]
    have hsum :
        ∑ D ∈ T.parts.filter (fun D => a ∉ D),
          cumulantCoefficient (T.restrict (Finset.sdiff_subset : s \ D ⊆ s)) =
          ((k - 1 : ℕ) : R) * ((-1 : R) ^ (k - 2) * Nat.factorial (k - 2)) := by
      rw [Finset.sum_congr rfl hsummand, Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [hfilter, Finset.card_erase_of_mem (T.part_mem.2 ha), hk_def]
    -- the two summands cancel: `(-1)^(k-1)(k-1)! + (k-1)(-1)^(k-2)(k-2)! = 0`
    have htest : k - 1 = (k - 2) + 1 := by
      rw [hk_def]
      omega
    have hpow : (-1 : R) ^ (k - 1) = -((-1 : R) ^ (k - 2)) := by
      rw [htest, pow_succ, mul_neg_one]
    have hfac : (Nat.factorial (k - 1) : R) = ((k - 1 : ℕ) : R) * Nat.factorial (k - 2) := by
      rw [htest, Nat.factorial_succ, Nat.cast_mul, htest.symm]
    rw [if_neg hT, hsum,
      show cumulantCoefficient T = (-1 : R) ^ (k - 1) * Nat.factorial (k - 1) by rfl,
      hpow, hfac]
    -- the two summands cancel: `-p * (x * f) + x * (p * f) = 0`
    rw [neg_mul, mul_left_comm]
    exact neg_add_cancel (((k - 1 : ℕ) : R) * ((-1 : R) ^ (k - 2) * Nat.factorial (k - 2)))

/-- The regrouping identity behind the Möbius inversion.

Expanding every `cumulantTransform` in `K f s + Σ_{B ⊊ s, a ∈ B} K f B * f (s \ B)` and
reindexing the second double sum by the glued partition `T = Q` extended with the block `s \ B`
yields, for each partition `T` of `s`, the coefficient
`c T + Σ_{D ∈ T.parts, a ∉ D} c (T restricted to s \ D)`, which is `1` for `T = ⊤` and `0`
otherwise (`cumulantCoefficient_sum_coarser`).  Only the one-block partition survives. -/
private lemma sum_block_cumulant [CommRing R] (f : Finset α → R) (s : Finset α) (a : α)
    (ha : a ∈ s) :
    cumulantTransform f s +
      ∑ B ∈ s.powerset.filter (fun B => a ∈ B ∧ B ≠ s),
        cumulantTransform f B * f (s \ B) = f s := by
  classical
  let t : Finset (Finset α) := s.powerset.filter (fun B => a ∈ B ∧ B ≠ s)
  have hs : s ≠ ∅ := Finset.nonempty_iff_ne_empty.1 ⟨a, ha⟩
  have hK (u : Finset α) (hu : u ≠ ∅) :
      cumulantTransform f u = ∑ Q : Finpartition u, cumulantCoefficient Q * Q.blockProduct f := by
    simp [cumulantTransform, hu]
  -- Step 1: expand both `cumulantTransform` sums (all carriers are nonempty)
  have hstep1 :
      cumulantTransform f s +
        ∑ B ∈ t, cumulantTransform f B * f (s \ B) =
        (∑ Q : Finpartition s, cumulantCoefficient Q * Q.blockProduct f) +
          ∑ x ∈ t.sigma (fun B => (Finset.univ : Finset (Finpartition B))),
            (cumulantCoefficient x.2 * x.2.blockProduct f) * f (s \ x.1) := by
    -- expand every `cumulantTransform` (all carriers are nonempty) and distribute the products
    rw [hK s hs, Finset.sum_sigma, add_left_cancel_iff]
    refine Finset.sum_congr rfl ?_
    intro B hB
    rw [hK B (Finset.nonempty_iff_ne_empty.1 ⟨a, (Finset.mem_filter.mp hB).2.1⟩)]
    simp [Finset.sum_mul]
  -- Step 2: reindex the second double sum by the glued partition `T = Q` extended with `s \ B`
  have hstep2 :
      ∑ x ∈ t.sigma (fun B => (Finset.univ : Finset (Finpartition B))),
        (cumulantCoefficient x.2 * x.2.blockProduct f) * f (s \ x.1) =
        ∑ y ∈ (Finset.univ : Finset (Finpartition s)).sigma
          (fun T => T.parts.filter (fun D => a ∉ D)),
          cumulantCoefficient (y.1.restrict (Finset.sdiff_subset : s \ y.2 ⊆ s)) *
            y.1.blockProduct f := by
    -- forward map: glue the block `s \ B` onto `Q` and record it as the distinguished block
    let i : ∀ x ∈ t.sigma (fun B => (Finset.univ : Finset (Finpartition B))),
        Sigma (fun T : Finpartition s => Finset α) :=
      fun x hx =>
        let hB : x.1 ∈ s.powerset ∧ a ∈ x.1 ∧ x.1 ≠ s :=
          Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1
        let hDne : s \ x.1 ≠ ∅ := fun h =>
          hB.2.2 (le_antisymm (Finset.mem_powerset.mp hB.1) (Finset.sdiff_eq_empty_iff_subset.mp h))
        let hdisj : Disjoint x.1 (s \ x.1) := by simp [Finset.disjoint_iff_inter_eq_empty]
        let hsup : x.1 ∪ (s \ x.1) = s := Finset.union_sdiff_of_subset (Finset.mem_powerset.mp hB.1)
        Sigma.mk (x.2.extendBlock hDne hdisj hsup) (s \ x.1)
    -- backward map: delete the block `D` from `T` and restrict to the complement
    let j : ∀ y ∈ (Finset.univ : Finset (Finpartition s)).sigma
          (fun T => T.parts.filter (fun D => a ∉ D)),
        Sigma (fun B : Finset α => Finpartition B) :=
      fun y hy => Sigma.mk (s \ y.2) (y.1.restrict (Finset.sdiff_subset : s \ y.2 ⊆ s))
    rw [← Finset.sum_bij' (s := t.sigma (fun B => (Finset.univ : Finset (Finpartition B))))
      (t := (Finset.univ : Finset (Finpartition s)).sigma
        (fun T => T.parts.filter (fun D => a ∉ D)))
      (i := i) (j := j)
      (hi := fun x hx => Finset.mem_sigma.mpr ⟨Finset.mem_univ _, by
        rw [Finset.mem_filter]
        exact ⟨by simp [i, extendBlock_parts],
          fun h =>
            (Finset.mem_sdiff.mp h).2 (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).2.1⟩⟩)
      (hj := fun y hy => Finset.mem_sigma.mpr ⟨by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_powerset.mpr (Finset.sdiff_subset), ⟨Finset.mem_sdiff.mpr ⟨ha,
          (Finset.mem_filter.mp (Finset.mem_sigma.mp hy).2).2⟩, fun h => by
          have hne : y.2 ≠ ∅ :=
            y.1.ne_empty (Finset.mem_filter.mp (Finset.mem_sigma.mp hy).2).1
          rcases Finset.nonempty_iff_ne_empty.2 hne with ⟨x, hx⟩
          -- `s \ y.2 = s` would put every element of the nonempty block `y.2` in `s \ y.2`
          have hx_sd : x ∈ s \ y.2 := by
            rw [show s \ y.2 = s by simpa [j] using h]
            exact Finset.mem_of_subset
              (y.1.subset (Finset.mem_filter.mp (Finset.mem_sigma.mp hy).2).1) hx
          exact (Finset.mem_sdiff.mp hx_sd).2 hx⟩⟩
        , Finset.mem_univ _⟩)]
    · -- deleting then gluing back recovers the pair `⟨B, Q⟩`
      intro x hx
      rcases x with ⟨B, Q⟩
      have hB : B ∈ s.powerset ∧ a ∈ B ∧ B ≠ s := Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1
      have hBsub : B ⊆ s := Finset.mem_powerset.mp hB.1
      have hBne' : s \ B ≠ ∅ := fun h =>
        hB.2.2 (le_antisymm hBsub (Finset.sdiff_eq_empty_iff_subset.mp h))
      have hdisj' : Disjoint B (s \ B) := by simp [Finset.disjoint_iff_inter_eq_empty]
      have hsup' : B ∪ (s \ B) = s := Finset.union_sdiff_of_subset hBsub
      have hsdiff : s \ (s \ B) = B := by
        simp [hBsub]
      dsimp [i, j]
      apply Sigma.ext
      · exact hsdiff
      · -- the restricted extended partition is `Q`
        refine heq_of_eq_cast (congrArg Finpartition hsdiff.symm) ?_
        apply Finpartition.ext
        ext C
        rw [cast_congrArg_parts B (s \ (s \ B)) hsdiff.symm]
        -- the restriction deletes the new block `s \ B` and keeps the old parts
        have hnew : s \ B ∈ (Q.extendBlock hBne' hdisj' hsup').parts := by
          simp [extendBlock_parts]
        rw [Finpartition.restrict_parts_of_mem (Q.extendBlock hBne' hdisj' hsup') hnew]
        rw [extendBlock_parts, Finset.erase_insert]
        · -- `s \ B ∉ Q.parts`: `s \ B ⊆ B` would force `s \ B = ∅`
          intro hD
          exact hBne' (by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro x hx
            exact (Finset.mem_sdiff.mp hx).2 (Q.subset hD hx))
    · -- gluing then deleting recovers the pair `⟨T, D⟩`
      intro y hy
      rcases y with ⟨T, D⟩
      have hD : D ∈ T.parts ∧ a ∉ D := Finset.mem_filter.mp (Finset.mem_sigma.mp hy).2
      have hDsub : D ⊆ s := T.subset hD.1
      have hsdiff : s \ (s \ D) = D := by
        simp [hDsub]
      dsimp [i, j]
      exact Sigma.ext (Finpartition.ext (by
        rw [extendBlock_parts, Finpartition.restrict_parts_of_mem T hD.1, hsdiff]
        exact Finset.insert_erase hD.1)) (heq_of_eq hsdiff)
    · -- the summands match:
      -- `(c Q * Q.blockProduct f) * f (s \ B) = c (T.restrict B) * T.blockProduct f`
      intro x hx
      rcases x with ⟨B, Q⟩
      have hB : B ∈ s.powerset ∧ a ∈ B ∧ B ≠ s := Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1
      have hBsub : B ⊆ s := Finset.mem_powerset.mp hB.1
      have hsdiff : s \ (s \ B) = B := by
        simp [hBsub]
      have hDne : s \ B ≠ ∅ := fun h =>
        hB.2.2 (le_antisymm hBsub (Finset.sdiff_eq_empty_iff_subset.mp h))
      have hdisj : Disjoint B (s \ B) := by simp [Finset.disjoint_iff_inter_eq_empty]
      have hsup : B ∪ (s \ B) = s := Finset.union_sdiff_of_subset hBsub
      -- the restriction to `s \ (s \ B) = B` deletes the new block and recovers `Q`
      -- (retyped along `hsdiff` so that the carriers agree)
      have hrestrict : (Q.extendBlock hDne hdisj hsup).restrict
          (Finset.sdiff_subset : s \ (s \ B) ⊆ s) = Q.copy hsdiff.symm :=
        Finpartition.ext (by
          rw [Finpartition.restrict_parts_of_mem (Q.extendBlock hDne hdisj hsup)
            (show s \ B ∈ (Q.extendBlock hDne hdisj hsup).parts from by simp [extendBlock_parts])]
          rw [extendBlock_parts, Finset.erase_insert]
          · rfl
          · intro hD
            exact hDne (by
              rw [Finset.eq_empty_iff_forall_notMem]
              intro x hx
              exact (Finset.mem_sdiff.mp hx).2 (Q.subset hD hx)))
      dsimp [i, j]
      rw [hrestrict]
      rw [blockProduct_extendBlock]
      -- `c Q * (f (s \ B) * Q.blockProduct f) = (c Q * Q.blockProduct f) * f (s \ B)`
      -- (`Q.copy hsdiff.symm` has the same parts as `Q`, so the coefficients agree)
      rw [show (Q.copy hsdiff.symm).cumulantCoefficient = Q.cumulantCoefficient by rfl]
      ac_rfl
  -- Step 3: combine the two sums over `T` and apply the coefficient identity
  rw [hstep1, hstep2, Finset.sum_sigma, ← Finset.sum_add_distrib]
  trans ∑ T : Finpartition s, (if T = ⊤ then (1 : R) else 0) * T.blockProduct f
  · -- the coefficient of each `T` is `1` exactly for `T = ⊤`, and `0` otherwise
    refine Finset.sum_congr rfl ?_
    intro T hT
    -- reduce the sigma projections, then pull the common factor `T.blockProduct f` out
    change T.cumulantCoefficient * T.blockProduct f +
      ∑ s_1 ∈ T.parts.filter (fun s_1 => a ∉ s_1),
        (T.restrict (Finset.sdiff_subset : s \ s_1 ⊆ s)).cumulantCoefficient * T.blockProduct f
      = (if T = ⊤ then 1 else 0) * T.blockProduct f
    rw [← Finset.sum_mul, ← add_mul]
    exact congrArg (· * T.blockProduct f) (cumulantCoefficient_sum_coarser s a ha T)
  · -- only the one-block partition `⊤` survives, contributing `⊤.blockProduct f = f s`
    have hparts : (⊤ : Finpartition s).parts = {s} := by
      apply Finset.eq_singleton_iff_unique_mem.2
      constructor
      · rcases Finpartition.parts_nonempty (⊤ : Finpartition s) hs with ⟨B, hB⟩
        have hB_eq : B = s :=
          Finset.mem_singleton.mp (Finset.mem_of_subset (Finpartition.parts_top_subset s) hB)
        simpa [hB_eq] using hB
      · exact fun D hD =>
          Finset.mem_singleton.mp (Finset.mem_of_subset (Finpartition.parts_top_subset s) hD)
    simp [Finset.sum_ite_eq', hparts, blockProduct, ite_mul, one_mul, zero_mul]

/-- The partition transform of the empty set is the empty product `1`. -/
private lemma partitionTransform_empty [CommSemiring R] (g : Finset α → R) :
    partitionTransform g ∅ = 1 := by
  classical
  have hbot : (∅ : Finset α) = ⊥ := rfl
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
            (Finset.nonempty_iff_ne_empty.1
              ⟨a, (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).2⟩)
            (Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).1))]
        · -- membership of the forward image in the sigma finset
          exact fun P _ => Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_powerset.mpr (P.part_subset a), P.mem_part ha⟩, Finset.mem_univ _⟩
        · -- membership of the backward image in the partition finset
          exact fun _ _ => Finset.mem_univ _
        · -- deleting then reinserting the block containing `a` recovers `P`
          exact fun P _ => insertBlock_deleteBlock P a ha
        · -- inserting then deleting recovers `⟨B, Q⟩`
          intro x hx
          rcases x with ⟨B, Q⟩
          have hBne : B ≠ ∅ := Finset.nonempty_iff_ne_empty.1
            ⟨a, (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).2⟩
          have hBsub : B ⊆ s :=
            Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).1
          have hBa : a ∈ B := (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).2
          exact Sigma.ext (insertBlock_part_of_mem B hBne hBsub Q a hBa)
            (deleteBlock_insertBlock B hBne hBsub Q a (hBsub hBa) hBa)
        · -- the block products match: `P.blockProduct = K f (P.part a) * residual product`
          exact fun P _ => blockProduct_deleteBlock P (cumulantTransform f) a ha
      _ = ∑ B ∈ t, cumulantTransform f B * partitionTransform (cumulantTransform f) (s \ B) := by
        -- convert the sigma sum over `B ∈ t` into the double sum
        rw [Finset.sum_sigma]
        refine Finset.sum_congr rfl ?_
        intro B hB
        simp [partitionTransform, Finset.mul_sum]
  -- Step 2: split off the `B = s` summand, whose complement transform is `1`
  calc
    partitionTransform (cumulantTransform f) s
        = ∑ B ∈ t,
            cumulantTransform f B * partitionTransform (cumulantTransform f) (s \ B) := hstep1
    _ = cumulantTransform f s + ∑ B ∈ t.erase s,
          cumulantTransform f B * partitionTransform (cumulantTransform f) (s \ B) := by
      -- `t = insert s (t.erase s)`, and the `B = s` summand is `K f s * S ∅ = K f s`
      nth_rw 1 [← Finset.insert_erase (show s ∈ t by simp [t, ha])]
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
        by_cases hBs : B = s <;> simp [t, hBs, ha]]

/-- Möbius inversion kernel for the partition transform on nonempty carriers.

This is proved by strong induction on `|s|`.  The induction step decomposes
`partitionTransform (cumulantTransform f) s` according to the block containing a fixed element
`a ∈ s` (`partitionTransform_cumulantTransform_rec`), applies the induction hypothesis to each
proper subset `s \ B`, and finishes with the one-level Möbius identity
`sum_block_cumulant`: expanding every inner `cumulantTransform` and regrouping the resulting
double sum by the glued partition `Q ∪ {s \ B}` gives, for each partition `T` of `s`, the
coefficient `c T + ∑_{D ∈ T.parts, a ∉ D} c (T restricted to s \ D)`, which is `1` exactly for
the one-block partition `⊤` and `0` otherwise (`cumulantCoefficient_sum_coarser`).  Only `⊤`
survives, contributing `f s`.

References for the informal proof and the Möbius value: Rota, *On the foundations of
combinatorial theory I. Theory of Möbius functions*, Z. Wahrscheinlichkeitstheorie verw. Gebiete 2
(1964), and Stanley, *Enumerative Combinatorics I*, 2nd ed., Example 3.10.4.  The project
blueprint records this as the partition-inversion theorem in
`blueprint/src/chapters/renormalization.tex`, `thm:renorm:partitionInversion`. -/
private theorem partitionTransform_cumulantTransform_of_nonempty_mobius [CommRing R]
    (f : Finset α → R) {s : Finset α} (hs : s ≠ ∅) :
    partitionTransform (cumulantTransform f) s = f s := by
  classical
  -- strong induction on the cardinality of the carrier `s`
  have hP : ∀ n, ∀ s, s.card = n → s ≠ ∅ → partitionTransform (cumulantTransform f) s = f s :=
    fun n => Nat.strong_induction_on n (by
    intro n ih s hs_n hs_ne
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.2 hs_ne
    -- Step 1: decompose the transform by the block containing `a`
    rw [partitionTransform_cumulantTransform_rec f s hs_ne a ha]
    -- Step 2: apply the induction hypothesis to every proper subset `s \ B`
    trans cumulantTransform f s +
        ∑ B ∈ s.powerset.filter (fun B => a ∈ B ∧ B ≠ s),
          cumulantTransform f B * f (s \ B)
    · rw [add_left_cancel_iff]
      refine Finset.sum_congr rfl ?_
      intro B hB
      rcases Finset.mem_filter.mp hB with ⟨hBp, hB_prop⟩
      have hBsub : B ⊆ s := Finset.mem_powerset.mp hBp
      -- `s \ B` is strictly smaller than `s`: the nonempty block `B` is removed
      have hBcard : (s \ B).card < n := by
        rw [← hs_n]
        exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
          ⟨Finset.sdiff_subset, fun h => (Finset.mem_sdiff.mp (h ▸ ha)).2 hB_prop.1⟩)
      have h_sB_ne : s \ B ≠ ∅ := fun h =>
        hB_prop.2 (le_antisymm hBsub (Finset.sdiff_eq_empty_iff_subset.mp h))
      rw [ih (s \ B).card hBcard (s \ B) rfl h_sB_ne]
    -- Step 3: the regrouped Möbius identity collapses to `f s`
    · exact sum_block_cumulant f s a ha)
  exact hP s.card s rfl hs

/-- Nonempty-set part of moment-cumulant inversion for finite partitions.

Informal proof: for `s ≠ ∅`, the partition transform of the cumulant transform is `f s`, by the
Möbius inversion on the partition lattice.  This file proves it by strong induction on `|s|`:
decomposing by the block containing a fixed element reduces the transform on `s` to the transform
on proper subsets (the induction hypothesis) plus a one-level Möbius cancellation on the interval
above each glued partition (`cumulantCoefficient_sum_coarser`), where the coefficient
`(-1)^(k-1)(k-1)!` telescopes against `(k-1)(-1)^(k-2)(k-2)!`.  Only the one-block partition `⊤`
survives, whose block product is `f s`.

References: Rota, *On the foundations of combinatorial theory I. Theory of Möbius functions*,
Z. Wahrscheinlichkeitstheorie verw. Gebiete 2 (1964), and Stanley, *Enumerative Combinatorics I*,
Prop. 3.10.1 for the Möbius value of the partition lattice. -/
theorem partitionTransform_cumulantTransform_of_nonempty [CommRing R] (f : Finset α → R)
    {s : Finset α} (hs : s ≠ ∅) :
    partitionTransform (cumulantTransform f) s = f s :=
  partitionTransform_cumulantTransform_of_nonempty_mobius f hs

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

/-- The indiscrete partition has block product `f s` on a nonempty carrier. -/
private lemma blockProduct_top [CommMonoid R] (f : Finset α → R) {s : Finset α} (hs : s ≠ ∅) :
    (⊤ : Finpartition s).blockProduct f = f s := by
  have hparts : (⊤ : Finpartition s).parts = {s} := by
    apply Finset.eq_singleton_iff_unique_mem.2
    constructor
    · rcases Finpartition.parts_nonempty (⊤ : Finpartition s) hs with ⟨B, hB⟩
      have hB_eq : B = s :=
        Finset.mem_singleton.mp (Finset.mem_of_subset (Finpartition.parts_top_subset s) hB)
      simpa [hB_eq] using hB
    · exact fun D hD =>
        Finset.mem_singleton.mp (Finset.mem_of_subset (Finpartition.parts_top_subset s) hD)
  rw [blockProduct, hparts, Finset.prod_singleton]

/-- If a part of `P` is the whole carrier, then `P` is the indiscrete partition. -/
private lemma eq_top_of_mem_parts_eq_self {s : Finset α} (P : Finpartition s) {B : Finset α}
    (hB : B ∈ P.parts) (hBs : B = s) :
    P = ⊤ := by
  rcases eq_or_ne s ∅ with rfl | hs
  · exact (P.empty_notMem_parts (hBs ▸ hB)).elim
  · refine (Finpartition.eq_top_iff_card_parts_eq_one P hs).2 ?_
    have hparts : P.parts = {s} := by
      apply Finset.eq_singleton_iff_unique_mem.2
      constructor
      · exact hBs ▸ hB
      · intro C hC
        by_contra hCs
        rcases Finset.nonempty_iff_ne_empty.2 (P.ne_empty hC) with ⟨x, hxC⟩
        exact hCs ((P.eq_of_mem_parts hC hB hxC (hBs.symm ▸ P.subset hC hxC)).trans hBs)
    rw [hparts]
    simp

/-- Every block of a non-top partition is a proper subset of the carrier, hence smaller. -/
private lemma card_lt_card_of_mem_parts_of_ne_top {s : Finset α} (P : Finpartition s)
    {B : Finset α} (hB : B ∈ P.parts) (hP : P ≠ ⊤) :
    B.card < s.card :=
  Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨P.subset hB, fun hBs => hP (eq_top_of_mem_parts_eq_self P hB hBs)⟩)

/-- Split the partition transform into the top partition and all lower partitions. -/
private lemma partitionTransform_eq_top_add_erase [CommSemiring R] (f : Finset α → R)
    {s : Finset α} (hs : s ≠ ∅) :
    partitionTransform f s =
      f s + ∑ P ∈ (Finset.univ.erase (⊤ : Finpartition s)), P.blockProduct f := by
  nth_rw 1 [partitionTransform, ← Finset.insert_erase (Finset.mem_univ (⊤ : Finpartition s))]
  rw [Finset.sum_insert, blockProduct_top f hs]
  simp

-- Triangularity step for the partition transform on a nonempty carrier: if `f` and `g` agree on
-- every strictly smaller carrier, then equality of the two transforms at `s` forces `f s = g s`.
-- The one-block partition `⊤` contributes exactly `f s` / `g s`, and the lower-order remainder
-- (sum over non-top partitions) agrees block by block by the smaller-carrier hypothesis.
private lemma eq_of_partitionTransform_eq_of_lt_card [CommRing R] {f g : Finset α → R}
    {s : Finset α} (hs : s ≠ ∅)
    (hfg : partitionTransform f s = partitionTransform g s)
    (hsub : ∀ B : Finset α, B.card < s.card → f B = g B) :
    f s = g s := by
  -- Every block of a non-top partition is a proper subset of `s` (hence smaller), so the block
  -- products of `f` and `g` agree term by term.
  have hlower :
      (∑ P ∈ (Finset.univ.erase (⊤ : Finpartition s)), P.blockProduct f) =
        ∑ P ∈ (Finset.univ.erase (⊤ : Finpartition s)), P.blockProduct g :=
    Finset.sum_congr rfl (fun P hP =>
      Finset.prod_congr rfl (fun B hB =>
        hsub B (card_lt_card_of_mem_parts_of_ne_top P hB (Finset.mem_erase.mp hP).1)))
  -- Split both transforms into the top contribution `f s`/`g s` and the (equal) remainder.
  rw [partitionTransform_eq_top_add_erase f hs,
    partitionTransform_eq_top_add_erase g hs, hlower] at hfg
  exact add_right_cancel hfg

/-- The partition transform is injective on functions with prescribed value `0` at the empty set.

Informal proof: argue by strong induction on `s.card`.  The empty case is exactly the two
normalization hypotheses.  For a nonempty carrier `s`, split the defining sum
`partitionTransform f s = ∑ P, P.blockProduct f` into the one-block partition `⊤`, whose
contribution is `f s`, and the remaining partitions.  In any non-top partition every block is a
proper subset of `s`, so the induction hypothesis identifies the block-products for `f` and `g`.
The equality of the two partition transforms then cancels the equal lower-order remainder and
leaves `f s = g s`.

This is a triangularity/injectivity argument for the zeta transform on the finite partition
poset.  It is equivalent to Möbius inversion; see Rota, *On the foundations of combinatorial
theory I. Theory of Möbius functions*, and the project blueprint theorem
`thm:renorm:partitionInversion`. -/
private theorem partitionTransform_injective_of_empty [CommRing R] {f g : Finset α → R}
    (hf : f ∅ = 0) (hg : g ∅ = 0)
    (hfg : partitionTransform f = partitionTransform g) :
    f = g := by
  -- Strong induction on the cardinality of the carrier: the empty carrier is exactly the two
  -- normalization hypotheses, and the nonempty step is the triangularity lemma.
  have hcard : ∀ n, ∀ s : Finset α, s.card = n → f s = g s := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs_card
      rcases eq_or_ne s ∅ with rfl | hs
      · rw [hf, hg]
      · -- The induction hypothesis applies to every block, whose carrier is strictly smaller.
        exact eq_of_partitionTransform_eq_of_lt_card hs (congrFun hfg s)
          (fun B hBlt => ih B.card (hs_card ▸ hBlt) B rfl)
  exact funext fun s => hcard s.card s rfl

/-- The cumulant transform inverts the partition transform for functions vanishing at the empty
set.

Informal proof: apply the already-proved forward inversion to the function `partitionTransform f`.
Its value on the empty set is `1`, so
`partitionTransform (cumulantTransform (partitionTransform f)) = partitionTransform f`.  The
partition transform is triangular with leading term `f s` on each nonempty `s`; hence it is
injective among functions with value `0` at the empty set.  Since `cumulantTransform` is
conventionally `0` on the empty set and `f ∅ = 0`, this injectivity gives the result.
(Source: Theory of Möbius Functions, Rota (1964),
https://link.springer.com/article/10.1007/BF01899123) -/
theorem cumulantTransform_partitionTransform [CommRing R] (f : Finset α → R)
    (hf : f ∅ = 0) :
    cumulantTransform (partitionTransform f) = f := by
  classical
  refine partitionTransform_injective_of_empty
    (f := cumulantTransform (partitionTransform f)) (g := f) ?_ hf ?_
  · simp [cumulantTransform]
  · exact partitionTransform_cumulantTransform (partitionTransform f) (partitionTransform_empty f)

section TracePairMatching

variable {A B : Finset α}

/-- The block of a restricted partition containing `x` is the trace on `b` of the original block
containing `x`. -/
lemma part_restrict {a b : Finset α} (P : Finpartition a) (hb : b ⊆ a) {x : α} (hx : x ∈ b) :
    (P.restrict hb).part x = P.part x ∩ b := by
  have hxa : x ∈ a := hb hx
  have hmem : P.part x ∩ b ∈ (P.restrict hb).parts := by
    rw [restrict]
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_image.mpr ⟨P.part x, P.part_mem.2 hxa, rfl⟩⟩
    exact Finset.nonempty_iff_ne_empty.mp ⟨x, Finset.mem_inter.mpr ⟨P.mem_part hxa, hx⟩⟩
  exact (Finpartition.part_eq_of_mem _ hmem
    (Finset.mem_inter.mpr ⟨P.mem_part hxa, hx⟩))

/-- A partial matching between the blocks of two finpartitions `π` and `σ`: a chosen subset `S` of
`π`'s blocks, a chosen subset `T` of `σ`'s blocks, and a bijection pairing them up.

This is the reusable "trace restriction / partial-matching fiber equivalence" API called for in
`cumulantTransform_tracePair_partialMatching_regrouping`'s docstring: `Matching.glue` reconstructs a
finpartition of `A ∪ B` from a pair of trace partitions and a matching between their blocks, and
`Matching.ofFinpartition` / `Matching.glue_ofFinpartition` (below) show this is (one half of) an
equivalence with `Finpartition (A ∪ B)`. -/
structure Matching (π : Finpartition A) (σ : Finpartition B) where
  /-- The chosen subset of `π`'s blocks that participate in the matching. -/
  S : Finset (Finset α)
  /-- The chosen subset of `σ`'s blocks that participate in the matching. -/
  T : Finset (Finset α)
  hS : S ⊆ π.parts
  hT : T ⊆ σ.parts
  /-- The bijection pairing each matched `π`-block in `S` with a `σ`-block in `T`. -/
  e : {p // p ∈ S} ≃ {q // q ∈ T}

/-- If `p ⊆ A` and `q ⊆ B` for disjoint `A`, `B`, then `p ∪ q` meets `A` exactly in `p`. -/
lemma union_inter_left_of_subset {p q : Finset α} (hAB : Disjoint A B) (hp : p ⊆ A)
    (hq : q ⊆ B) : (p ∪ q) ∩ A = p := by
  apply Finset.Subset.antisymm
  · intro y hy
    rcases Finset.mem_inter.mp hy with ⟨hyU, hyA⟩
    rcases Finset.mem_union.mp hyU with hyp | hyq
    · exact hyp
    · exact absurd hyA (Finset.disjoint_left.mp hAB.symm (hq hyq))
  · intro y hy
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hy, hp hy⟩

/-- If `p ⊆ A` and `q ⊆ B` for disjoint `A`, `B`, then `p ∪ q` meets `B` exactly in `q`. -/
lemma union_inter_right_of_subset {p q : Finset α} (hAB : Disjoint A B) (hp : p ⊆ A)
    (hq : q ⊆ B) : (p ∪ q) ∩ B = q := by
  rw [Finset.union_comm]
  exact union_inter_left_of_subset hAB.symm hq hp

namespace Matching

variable {π : Finpartition A} {σ : Finpartition B}

/-- The number of glued pairs in a matching. -/
def size (M : Matching π σ) : ℕ := M.S.card

/-- The blocks of the glued partition: unmatched blocks of `π`, unmatched blocks of `σ`, and the
unions of matched pairs. -/
def glueParts (M : Matching π σ) : Finset (Finset α) :=
  (π.parts \ M.S) ∪ (σ.parts \ M.T) ∪ (M.S.attach.image (fun s => (s.1 : Finset α) ∪ (M.e s).1))

lemma subset_of_mem_glueParts (M : Matching π σ) {p : Finset α} (hp : p ∈ M.glueParts) :
    p ⊆ A ∪ B := by
  simp only [glueParts, Finset.mem_union, Finset.mem_sdiff, Finset.mem_image,
    Finset.mem_attach, true_and] at hp
  rcases hp with (⟨hp, _⟩ | ⟨hp, _⟩) | ⟨s, rfl⟩
  · exact (π.subset hp).trans Finset.subset_union_left
  · exact (σ.subset hp).trans Finset.subset_union_right
  · exact Finset.union_subset_union (π.subset (M.hS s.2)) (σ.subset (M.hT (M.e s).2))

lemma empty_notMem_glueParts (M : Matching π σ) : ∅ ∉ M.glueParts := by
  intro hmem
  rw [glueParts, Finset.mem_union, Finset.mem_union] at hmem
  rcases hmem with (hmem | hmem) | hmem
  · exact π.ne_empty (Finset.mem_sdiff.mp hmem).1 rfl
  · exact σ.ne_empty (Finset.mem_sdiff.mp hmem).1 rfl
  · obtain ⟨s, -, hs⟩ := Finset.mem_image.mp hmem
    have hne : ((s.1 : Finset α) ∪ (M.e s).1).Nonempty :=
      Finset.Nonempty.mono Finset.subset_union_left (π.nonempty_of_mem_parts (M.hS s.2))
    exact hne.ne_empty hs

/-- Every point of `A ∪ B` lies in exactly one block of the glued matching.

Informal proof: for `x ∈ A`, its unique `π`-block `π.part x` is either matched (in `M.S`) or not.
If matched to `q := M.e ⟨π.part x, _⟩`, the merged block `π.part x ∪ q` is the unique witness: any
other candidate block containing `x` would, by case analysis on which of the three parts of
`glueParts` it comes from, have to equal `π.part x` (contradicting membership in the erased part)
or lie in `B` (contradicting `x ∈ A` and `Disjoint A B`) or come from a different matched pair
whose `π`-side must equal `π.part x` by uniqueness of `Finpartition.part`, forcing equality of
the pairs by injectivity of `M.e`. If unmatched, `π.part x` itself is the unique witness by the
symmetric argument. The case `x ∈ B` is symmetric, using `M.e.symm`. -/
lemma existsUnique_mem_glueParts (M : Matching π σ) (hAB : Disjoint A B) :
    ∀ x ∈ A ∪ B, ∃! t, t ∈ M.glueParts ∧ x ∈ t := by
  intro x hx
  rcases Finset.mem_union.mp hx with hxA | hxB
  · -- `x ∈ A`: work with the block of `π` containing `x`.
    have hxB' : x ∉ B := Finset.disjoint_left.mp hAB hxA
    have hp0_mem : π.part x ∈ π.parts := π.part_mem.2 hxA
    have hp0_x : x ∈ π.part x := π.mem_part hxA
    by_cases hp0S : π.part x ∈ M.S
    · -- the block is matched: the merged block is the unique witness
      set s0 : {p // p ∈ M.S} := ⟨π.part x, hp0S⟩ with hs0_def
      refine ⟨s0.1 ∪ (M.e s0).1,
        ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s0, Finset.mem_attach _ s0, rfl⟩),
          Finset.mem_union_left _ hp0_x⟩, ?_⟩
      rintro t' ⟨ht', hxt'⟩
      rw [glueParts, Finset.mem_union, Finset.mem_union] at ht'
      rcases ht' with (ht' | ht') | ht'
      · have heq : π.part x = t' := π.part_eq_of_mem (Finset.mem_sdiff.mp ht').1 hxt'
        exact absurd (heq ▸ hp0S) (Finset.mem_sdiff.mp ht').2
      · exact absurd (σ.subset (Finset.mem_sdiff.mp ht').1 hxt') hxB'
      · obtain ⟨s1, -, hs1⟩ := Finset.mem_image.mp ht'
        have hx_notin : x ∉ (M.e s1).1 := fun h => hxB' (σ.subset (M.hT (M.e s1).2) h)
        have hx_s1 : x ∈ s1.1 := (Finset.mem_union.mp (hs1 ▸ hxt')).resolve_right hx_notin
        have hp0_eq : π.part x = s1.1 := π.part_eq_of_mem (M.hS s1.2) hx_s1
        have hs1_eq : s1 = s0 := Subtype.ext hp0_eq.symm
        rw [← hs1, hs1_eq]
    · -- the block is unmatched: it is itself the unique witness
      refine ⟨π.part x,
        ⟨Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_sdiff.mpr ⟨hp0_mem, hp0S⟩)), hp0_x⟩, ?_⟩
      rintro t' ⟨ht', hxt'⟩
      rw [glueParts, Finset.mem_union, Finset.mem_union] at ht'
      rcases ht' with (ht' | ht') | ht'
      · exact (π.part_eq_of_mem (Finset.mem_sdiff.mp ht').1 hxt').symm
      · exact absurd (σ.subset (Finset.mem_sdiff.mp ht').1 hxt') hxB'
      · obtain ⟨s1, -, hs1⟩ := Finset.mem_image.mp ht'
        have hx_notin : x ∉ (M.e s1).1 := fun h => hxB' (σ.subset (M.hT (M.e s1).2) h)
        have hx_s1 : x ∈ s1.1 := (Finset.mem_union.mp (hs1 ▸ hxt')).resolve_right hx_notin
        have hp0_eq : π.part x = s1.1 := π.part_eq_of_mem (M.hS s1.2) hx_s1
        exact absurd (hp0_eq ▸ s1.2) hp0S
  · -- `x ∈ B`: symmetric, working with the block of `σ` containing `x` and `M.e.symm`.
    have hxA' : x ∉ A := fun h => Finset.disjoint_left.mp hAB h hxB
    have hq0_mem : σ.part x ∈ σ.parts := σ.part_mem.2 hxB
    have hq0_x : x ∈ σ.part x := σ.mem_part hxB
    by_cases hq0T : σ.part x ∈ M.T
    · set t0 : {q // q ∈ M.T} := ⟨σ.part x, hq0T⟩ with ht0_def
      refine ⟨(M.e.symm t0).1 ∪ t0.1,
        ⟨Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨M.e.symm t0, Finset.mem_attach _ _, by simp⟩),
          Finset.mem_union_right _ hq0_x⟩, ?_⟩
      rintro t' ⟨ht', hxt'⟩
      rw [glueParts, Finset.mem_union, Finset.mem_union] at ht'
      rcases ht' with (ht' | ht') | ht'
      · exact absurd (π.subset (Finset.mem_sdiff.mp ht').1 hxt') hxA'
      · have heq : σ.part x = t' := σ.part_eq_of_mem (Finset.mem_sdiff.mp ht').1 hxt'
        exact absurd (heq ▸ hq0T) (Finset.mem_sdiff.mp ht').2
      · obtain ⟨s1, -, hs1⟩ := Finset.mem_image.mp ht'
        have hx_notin : x ∉ s1.1 := fun h => hxA' (π.subset (M.hS s1.2) h)
        have hx_e : x ∈ (M.e s1).1 := (Finset.mem_union.mp (hs1 ▸ hxt')).resolve_left hx_notin
        have hq0_eq : σ.part x = (M.e s1).1 := σ.part_eq_of_mem (M.hT (M.e s1).2) hx_e
        have hs1_eq : s1 = M.e.symm t0 := by
          apply M.e.injective
          rw [Equiv.apply_symm_apply]
          exact Subtype.ext hq0_eq.symm
        rw [← hs1, hs1_eq, Equiv.apply_symm_apply]
    · refine ⟨σ.part x,
        ⟨Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_sdiff.mpr ⟨hq0_mem, hq0T⟩)), hq0_x⟩, ?_⟩
      rintro t' ⟨ht', hxt'⟩
      rw [glueParts, Finset.mem_union, Finset.mem_union] at ht'
      rcases ht' with (ht' | ht') | ht'
      · exact absurd (π.subset (Finset.mem_sdiff.mp ht').1 hxt') hxA'
      · exact (σ.part_eq_of_mem (Finset.mem_sdiff.mp ht').1 hxt').symm
      · obtain ⟨s1, -, hs1⟩ := Finset.mem_image.mp ht'
        have hx_notin : x ∉ s1.1 := fun h => hxA' (π.subset (M.hS s1.2) h)
        have hx_e : x ∈ (M.e s1).1 := (Finset.mem_union.mp (hs1 ▸ hxt')).resolve_left hx_notin
        have hq0_eq : σ.part x = (M.e s1).1 := σ.part_eq_of_mem (M.hT (M.e s1).2) hx_e
        exact absurd (hq0_eq ▸ (M.e s1).2) hq0T

/-- Glue a matching between the blocks of `π` and `σ` into a finpartition of `A ∪ B`, merging each
matched pair of blocks into a single block and keeping unmatched blocks as they are. -/
def glue (M : Matching π σ) (hAB : Disjoint A B) : Finpartition (A ∪ B) :=
  Finpartition.ofExistsUnique M.glueParts (fun _ hp => M.subset_of_mem_glueParts hp)
    (M.existsUnique_mem_glueParts hAB) M.empty_notMem_glueParts

@[simp] lemma glue_parts (M : Matching π σ) (hAB : Disjoint A B) :
    (M.glue hAB).parts = M.glueParts := rfl

lemma card_T_eq_card_S (M : Matching π σ) : M.T.card = M.S.card := by
  simpa using Fintype.card_congr M.e.symm

lemma injOn_mergeMap (M : Matching π σ) (hAB : Disjoint A B) :
    Set.InjOn (fun s : {p // p ∈ M.S} => (s.1 : Finset α) ∪ (M.e s).1) Set.univ := by
  intro s1 _ s2 _ h
  simp only at h
  have h1 : ((s1.1 : Finset α) ∪ (M.e s1).1) ∩ A = s1.1 :=
    union_inter_left_of_subset hAB (π.subset (M.hS s1.2)) (σ.subset (M.hT (M.e s1).2))
  have h2 : ((s2.1 : Finset α) ∪ (M.e s2).1) ∩ A = s2.1 :=
    union_inter_left_of_subset hAB (π.subset (M.hS s2.2)) (σ.subset (M.hT (M.e s2).2))
  exact Subtype.ext (h1 ▸ h2 ▸ (h ▸ rfl : ((s1.1 : Finset α) ∪ (M.e s1).1) ∩ A
    = ((s2.1 : Finset α) ∪ (M.e s2).1) ∩ A))

/-- The unmatched `π`-blocks and unmatched `σ`-blocks are disjoint (as elements of the glued
partition), since they lie on the disjoint sides `A`, `B` of the cut. -/
lemma disjoint_leftUnmatched_rightUnmatched (M : Matching π σ) (hAB : Disjoint A B) :
    Disjoint (π.parts \ M.S) (σ.parts \ M.T) := by
  rw [Finset.disjoint_left]
  intro t ht ht'
  have htA : t ⊆ A := π.subset (Finset.mem_sdiff.mp ht).1
  have htB : t ⊆ B := σ.subset (Finset.mem_sdiff.mp ht').1
  exact π.ne_empty (Finset.mem_sdiff.mp ht).1
    (Finset.subset_empty.mp (fun y hy => absurd (htB hy) (Finset.disjoint_left.mp hAB (htA hy))))

/-- Every merged block meets both `A` and `B`, in the matched `π`- and `σ`-block respectively. -/
lemma merged_inter_nonempty (M : Matching π σ) (hAB : Disjoint A B) {t : Finset α}
    (ht : t ∈ M.S.attach.image (fun s => (s.1 : Finset α) ∪ (M.e s).1)) :
    (t ∩ A).Nonempty ∧ (t ∩ B).Nonempty := by
  obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp ht
  rw [union_inter_left_of_subset hAB (π.subset (M.hS s.2)) (σ.subset (M.hT (M.e s).2)),
    union_inter_right_of_subset hAB (π.subset (M.hS s.2)) (σ.subset (M.hT (M.e s).2))]
  exact ⟨π.nonempty_of_mem_parts (M.hS s.2), σ.nonempty_of_mem_parts (M.hT (M.e s).2)⟩

/-- No unmatched block coincides with a merged block: a merged block meets both sides of the cut,
while an unmatched block lies entirely on one side. -/
lemma disjoint_unmatched_merged (M : Matching π σ) (hAB : Disjoint A B) :
    Disjoint ((π.parts \ M.S) ∪ (σ.parts \ M.T))
      (M.S.attach.image (fun s => (s.1 : Finset α) ∪ (M.e s).1)) := by
  rw [Finset.disjoint_union_left, Finset.disjoint_left, Finset.disjoint_left]
  refine ⟨fun t ht ht' => ?_, fun t ht ht' => ?_⟩
  · obtain ⟨x, hx⟩ := (M.merged_inter_nonempty hAB ht').2
    exact (Finset.disjoint_left.mp hAB) (π.subset (Finset.mem_sdiff.mp ht).1
      (Finset.mem_inter.mp hx).1) (Finset.mem_inter.mp hx).2
  · obtain ⟨x, hx⟩ := (M.merged_inter_nonempty hAB ht').1
    exact (Finset.disjoint_left.mp hAB) (Finset.mem_inter.mp hx).2
      (σ.subset (Finset.mem_sdiff.mp ht).1 (Finset.mem_inter.mp hx).1)

/-- The glued partition has `p + q - m` blocks, where `p = |π.parts|`, `q = |σ.parts|`, and
`m = M.size` is the number of glued pairs: the `m` matched pairs merge into `m` blocks, and
`p - m`, `q - m` blocks remain unmatched on each side. -/
lemma card_glueParts (M : Matching π σ) (hAB : Disjoint A B) :
    M.glueParts.card = π.parts.card + σ.parts.card - M.size := by
  have hcard : M.glueParts.card = (π.parts \ M.S).card + (σ.parts \ M.T).card +
      (M.S.attach.image (fun s => (s.1 : Finset α) ∪ (M.e s).1)).card := by
    rw [glueParts, Finset.card_union_of_disjoint (M.disjoint_unmatched_merged hAB),
      Finset.card_union_of_disjoint (M.disjoint_leftUnmatched_rightUnmatched hAB)]
  rw [hcard, Finset.card_sdiff_of_subset (M.hS), Finset.card_sdiff_of_subset (M.hT),
    Finset.card_image_of_injOn (fun s1 hs1 s2 hs2 h => M.injOn_mergeMap hAB (Set.mem_univ s1)
      (Set.mem_univ s2) h),
    Finset.card_attach]
  have hSle : M.S.card ≤ π.parts.card := Finset.card_le_card M.hS
  have hTle : M.T.card ≤ σ.parts.card := Finset.card_le_card M.hT
  have hTS : M.T.card = M.S.card := M.card_T_eq_card_S
  simp only [size]
  omega

/-- The block product of the glued partition factors as the product of the block products of `π`
and `σ`, provided matched pairs multiply correctly (`hmul`). -/
lemma blockProduct_glue {R : Type*} [CommMonoid R] (M : Matching π σ) (hAB : Disjoint A B)
    (f : Finset α → R)
    (hmul : ∀ s : {p // p ∈ M.S}, f ((s.1 : Finset α) ∪ (M.e s).1) = f s.1 * f (M.e s).1) :
    (M.glue hAB).blockProduct f = π.blockProduct f * σ.blockProduct f := by
  have hprod : (M.glue hAB).blockProduct f =
      (∏ t ∈ π.parts \ M.S, f t) * (∏ t ∈ σ.parts \ M.T, f t) *
        (∏ t ∈ M.S.attach.image (fun s => (s.1 : Finset α) ∪ (M.e s).1), f t) := by
    rw [Finpartition.blockProduct, glue_parts, glueParts,
      Finset.prod_union (M.disjoint_unmatched_merged hAB),
      Finset.prod_union (M.disjoint_leftUnmatched_rightUnmatched hAB)]
  rw [hprod, Finset.prod_image (fun s1 hs1 s2 hs2 h => M.injOn_mergeMap hAB (Set.mem_univ s1)
    (Set.mem_univ s2) h)]
  simp_rw [hmul]
  rw [Finset.prod_mul_distrib]
  have hπ : π.blockProduct f = (∏ t ∈ π.parts \ M.S, f t) * (∏ s ∈ M.S.attach, f s.1) := by
    rw [Finpartition.blockProduct, ← Finset.prod_sdiff (M.hS), Finset.prod_attach M.S f]
  have hσ : σ.blockProduct f = (∏ t ∈ σ.parts \ M.T, f t) * (∏ s ∈ M.S.attach, f (M.e s).1) := by
    rw [Finpartition.blockProduct, ← Finset.prod_sdiff (M.hT)]
    congr 1
    rw [← Finset.prod_attach M.T f, Finset.attach_eq_univ, Finset.attach_eq_univ]
    exact (Equiv.prod_comp M.e (fun t : {x // x ∈ M.T} => f t.1)).symm
  rw [hπ, hσ]
  ac_rfl

end Matching

/-- The `T`-blocks that genuinely span the cut: they meet both `A` and `B`. -/
def mergedOf (T : Finpartition (A ∪ B)) : Finset (Finset α) :=
  T.parts.filter (fun D => (D ∩ A).Nonempty ∧ (D ∩ B).Nonempty)

lemma injOn_inter_left_mergedOf (T : Finpartition (A ∪ B)) :
    Set.InjOn (· ∩ A) (mergedOf T : Set (Finset α)) := by
  intro D1 hD1 D2 hD2 heq
  simp only [mergedOf, Finset.coe_filter, Set.mem_ofPred_eq] at hD1 hD2
  dsimp only at heq
  by_contra hne
  have hdisj : Disjoint (D1 ∩ A) (D2 ∩ A) :=
    (T.disjoint hD1.1 hD2.1 hne).mono inf_le_left inf_le_left
  exact (Finset.nonempty_iff_ne_empty.mp hD2.2.1) (by simpa [heq, disjoint_self] using hdisj)

lemma injOn_inter_right_mergedOf (T : Finpartition (A ∪ B)) :
    Set.InjOn (· ∩ B) (mergedOf T : Set (Finset α)) := by
  intro D1 hD1 D2 hD2 heq
  simp only [mergedOf, Finset.coe_filter, Set.mem_ofPred_eq] at hD1 hD2
  dsimp only at heq
  by_contra hne
  have hdisj : Disjoint (D1 ∩ B) (D2 ∩ B) :=
    (T.disjoint hD1.1 hD2.1 hne).mono inf_le_left inf_le_left
  exact (Finset.nonempty_iff_ne_empty.mp hD2.2.2) (by simpa [heq, disjoint_self] using hdisj)

/-- The (unique) merged `T`-block whose `A`-trace is `t`. -/
noncomputable def mergedOfLeft (T : Finpartition (A ∪ B)) {t : Finset α}
    (ht : t ∈ (mergedOf T).image (· ∩ A)) : Finset α :=
  (Finset.mem_image.mp ht).choose

lemma mergedOfLeft_mem (T : Finpartition (A ∪ B)) {t : Finset α}
    (ht : t ∈ (mergedOf T).image (· ∩ A)) : mergedOfLeft T ht ∈ mergedOf T :=
  (Finset.mem_image.mp ht).choose_spec.1

lemma mergedOfLeft_inter (T : Finpartition (A ∪ B)) {t : Finset α}
    (ht : t ∈ (mergedOf T).image (· ∩ A)) : mergedOfLeft T ht ∩ A = t :=
  (Finset.mem_image.mp ht).choose_spec.2

/-- The (unique) merged `T`-block whose `B`-trace is `t`. -/
noncomputable def mergedOfRight (T : Finpartition (A ∪ B)) {t : Finset α}
    (ht : t ∈ (mergedOf T).image (· ∩ B)) : Finset α :=
  (Finset.mem_image.mp ht).choose

lemma mergedOfRight_mem (T : Finpartition (A ∪ B)) {t : Finset α}
    (ht : t ∈ (mergedOf T).image (· ∩ B)) : mergedOfRight T ht ∈ mergedOf T :=
  (Finset.mem_image.mp ht).choose_spec.1

lemma mergedOfRight_inter (T : Finpartition (A ∪ B)) {t : Finset α}
    (ht : t ∈ (mergedOf T).image (· ∩ B)) : mergedOfRight T ht ∩ B = t :=
  (Finset.mem_image.mp ht).choose_spec.2

namespace Matching

variable {π : Finpartition A} {σ : Finpartition B}

/-- The partial matching extracted from a finpartition of `A ∪ B`: the merged blocks, split into
their `A`- and `B`-traces. -/
noncomputable def ofFinpartition (T : Finpartition (A ∪ B)) (_hAB : Disjoint A B) :
    Matching (T.restrict (Finset.subset_union_left)) (T.restrict (Finset.subset_union_right)) := by
  refine
    { S := (mergedOf T).image (· ∩ A)
      T := (mergedOf T).image (· ∩ B)
      hS := ?_
      hT := ?_
      e :=
        { toFun := fun s => ⟨mergedOfLeft T s.2 ∩ B,
            Finset.mem_image.mpr ⟨mergedOfLeft T s.2, mergedOfLeft_mem T s.2, rfl⟩⟩
          invFun := fun t => ⟨mergedOfRight T t.2 ∩ A,
            Finset.mem_image.mpr ⟨mergedOfRight T t.2, mergedOfRight_mem T t.2, rfl⟩⟩
          left_inv := ?_
          right_inv := ?_ } }
  · intro t ht
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp ht
    rw [restrict]
    exact Finset.mem_erase.mpr
      ⟨Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hD).2.1,
        Finset.mem_image.mpr ⟨D, (Finset.mem_filter.mp hD).1, rfl⟩⟩
  · intro t ht
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp ht
    rw [restrict]
    exact Finset.mem_erase.mpr
      ⟨Finset.nonempty_iff_ne_empty.mp (Finset.mem_filter.mp hD).2.2,
        Finset.mem_image.mpr ⟨D, (Finset.mem_filter.mp hD).1, rfl⟩⟩
  · intro s
    apply Subtype.ext
    change mergedOfRight T (Finset.mem_image.mpr
      ⟨mergedOfLeft T s.2, mergedOfLeft_mem T s.2, rfl⟩) ∩ A = s.1
    rw [T.injOn_inter_right_mergedOf (mergedOfRight_mem T _) (mergedOfLeft_mem T s.2)
      (mergedOfRight_inter T _)]
    exact mergedOfLeft_inter T s.2
  · intro t
    apply Subtype.ext
    change mergedOfLeft T (Finset.mem_image.mpr
      ⟨mergedOfRight T t.2, mergedOfRight_mem T t.2, rfl⟩) ∩ B = t.1
    rw [T.injOn_inter_left_mergedOf (mergedOfLeft_mem T _) (mergedOfRight_mem T t.2)
      (mergedOfLeft_inter T _)]
    exact mergedOfRight_inter T t.2

-- A set contained in `A ∪ B` is the union of its two traces: `D = (D ∩ A) ∪ (D ∩ B)`.
private lemma union_inter_inter_eq_self {D A B : Finset α} (hD : D ⊆ A ∪ B) :
    (D ∩ A) ∪ (D ∩ B) = D := by
  rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hD]

-- A `T`-block that does not span the cut meets at most one of the two sides.
private lemma inter_eq_empty_of_not_merged (T : Finpartition (A ∪ B)) {D : Finset α}
    (hD : D ∈ T.parts) (hnot : D ∉ mergedOf T) : D ∩ A = ∅ ∨ D ∩ B = ∅ := by
  by_contra h
  exact hnot (by simpa [mergedOf, Finset.nonempty_iff_ne_empty] using ⟨hD, not_or.mp h⟩)

-- If `t` is a `T`-block that does not span the cut, no merged block has `t` as its trace:
-- any such block would share a point with `t` and hence equal `t` by `eq_of_mem_parts`.
private lemma not_mem_mergedOf_image_of_not_merged (T : Finpartition (A ∪ B)) {t : Finset α}
    (ht : t ∈ T.parts) (htm : t ∉ mergedOf T) (s : Finset α) :
    ¬ ∃ D ∈ mergedOf T, D ∩ s = t := by
  rintro ⟨D, hDm, hDt⟩
  obtain ⟨x, hx⟩ := T.nonempty_of_mem_parts ht
  exact htm ((T.eq_of_mem_parts (Finset.mem_filter.mp hDm).1 ht
    (Finset.mem_inter.mp (hDt ▸ hx)).1 hx) ▸ hDm)

-- Forward inclusion of `glue_ofFinpartition`: every block of the glued parts is a block of `T`.
private lemma glueParts_subset_parts (T : Finpartition (A ∪ B)) (hAB : Disjoint A B) :
    (ofFinpartition T hAB).glueParts ⊆ T.parts := by
  intro t ht
  -- Every `T`-block is the union of its `A`- and `B`-traces.
  have hsplit : ∀ ⦃D : Finset α⦄, D ∈ T.parts → (D ∩ A) ∪ (D ∩ B) = D :=
    fun D hD => union_inter_inter_eq_self (T.subset hD)
  -- Unfold `glueParts` (with both restricted partitions and the merged blocks) into three cases.
  simp only [glueParts, ofFinpartition, Finpartition.restrict, Finset.inf_eq_inter,
    Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_image, Finset.mem_attach,
    true_and] at ht
  rcases ht with (ht | ht) | ht
  · -- Unmatched left block `t = D ∩ A`: `D` is not merged, so it misses `B` and `D = t`.
    rcases ht with ⟨⟨htne, D, hD, rfl⟩, hnot⟩
    convert hD using 1
    rcases inter_eq_empty_of_not_merged T hD (fun hDm => hnot ⟨D, hDm, rfl⟩) with hDA | hDB
    · exact (htne hDA).elim
    · simpa [hDB] using hsplit hD
  · -- Unmatched right block `t = D ∩ B`, symmetric to the previous case.
    rcases ht with ⟨⟨htne, D, hD, rfl⟩, hnot⟩
    convert hD using 1
    rcases inter_eq_empty_of_not_merged T hD (fun hDm => hnot ⟨D, hDm, rfl⟩) with hDA | hDB
    · simpa [hDA] using hsplit hD
    · exact (htne hDB).elim
  · -- Merged block: `t = s.1 ∪ (mergedOfLeft T s.2 ∩ B)`, and `mergedOfLeft T s.2` is a part.
    obtain ⟨s, -, rfl⟩ := ht
    change (s.1 : Finset α) ∪ (mergedOfLeft T s.2 ∩ B) ∈ T.parts
    have hDmem : mergedOfLeft T s.2 ∈ T.parts := (Finset.mem_filter.mp (mergedOfLeft_mem T s.2)).1
    convert hDmem using 1
    simpa [mergedOfLeft_inter T s.2] using hsplit hDmem

-- Backward inclusion of `glue_ofFinpartition`: every block of `T` appears in the glued parts.
private lemma parts_subset_glueParts (T : Finpartition (A ∪ B)) (hAB : Disjoint A B) :
    T.parts ⊆ (ofFinpartition T hAB).glueParts := by
  intro t ht
  -- `t = (t ∩ A) ∪ (t ∩ B)`: `t` is a merged block iff it spans the cut, otherwise it is
  -- unmatched on exactly one side.
  have hsplit : (t ∩ A) ∪ (t ∩ B) = t := union_inter_inter_eq_self (T.subset ht)
  simp only [glueParts, ofFinpartition, Finpartition.restrict, Finset.inf_eq_inter,
    Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_image, Finset.mem_attach,
    true_and]
  by_cases htm : t ∈ mergedOf T
  · right
    -- `t` spans the cut: it is the merged block of the matched pair `⟨t ∩ A, t ∩ B⟩`.
    let hs : t ∩ A ∈ (mergedOf T).image (· ∩ A) :=
      Finset.mem_image.mpr ⟨t, htm, rfl⟩
    refine ⟨⟨t ∩ A, hs⟩, ?_⟩
    change (t ∩ A) ∪ (mergedOfLeft T hs ∩ B) = t
    simpa [T.injOn_inter_left_mergedOf (mergedOfLeft_mem T hs) htm (mergedOfLeft_inter T hs)]
      using hsplit
  · by_cases hA : t ∩ A = ∅
    · left
      right
      -- `t` misses `A`, so it is the unmatched right block `t = t ∩ B`.
      refine ⟨?_, ?_⟩
      · refine ⟨T.ne_empty ht, t, ht, by simpa [hA] using hsplit⟩
      · exact not_mem_mergedOf_image_of_not_merged T ht htm B
    · left
      left
      -- `t` meets `A` but does not span the cut, so it misses `B`: unmatched left block.
      have htA : t ∩ A = t := by
        rcases inter_eq_empty_of_not_merged T ht htm with hA' | hB
        · exact (hA hA').elim
        · simpa [hB] using hsplit
      refine ⟨?_, ?_⟩
      · refine ⟨T.ne_empty ht, t, ht, htA⟩
      · exact not_mem_mergedOf_image_of_not_merged T ht htm A

/-- Gluing the matching extracted from `T` recovers `T`.

Informal proof.  Write `M := ofFinpartition T hAB`, `π₀ := T.restrict subset_union_left`,
`σ₀ := T.restrict subset_union_right`.  We show `M.glueParts = T.parts` by double inclusion,
using the elementary fact that every `D ⊆ A ∪ B` satisfies `(D ∩ A) ∪ (D ∩ B) = D`, and that a
block `D ∈ T.parts` not in `mergedOf T` must satisfy `D ∩ A = ∅` or `D ∩ B = ∅` (it cannot meet
both sides), forcing `D ⊆ B` or `D ⊆ A` respectively via the first fact.

`(⊇)`: for `t ∈ T.parts`, either `t ∈ mergedOf T`, in which case `t = (t ∩ A) ∪ (t ∩ B)` is (by
construction of `ofFinpartition`) exactly the image of the matched pair `⟨t ∩ A, _⟩ : ↥M.S` under
`fun s => s.1 ∪ (M.e s).1` (using `mergedOfLeft_inter`/`injOn_inter_left_mergedOf` to identify the
witness block as `t` itself); or `t ∉ mergedOf T`, in which case `t` is pure and lands in
`π₀.parts \ M.S` or `σ₀.parts \ M.T` (it is not in `M.S`/`M.T` since any block matched from that
side would, being nonempty and sharing a point with `t`, equal `t` by `Finpartition.eq_of_mem_parts`
and hence lie in `mergedOf T`, contradiction).

`(⊆)`: for `t ∈ π₀.parts \ M.S`, unfolding `restrict` gives `t = D ∩ A` for some `D ∈ T.parts`
with `t ≠ ∅`; since `t ∉ M.S` forces `D ∉ mergedOf T` (else `D ∩ A ∈ M.S`), purity gives
`D ∩ A = ∅` (impossible, `t ≠ ∅`) or `D ∩ B = ∅`, so `D = D ∩ A = t ∈ T.parts`.  Symmetrically for
`σ₀.parts \ M.T`.  For `t` in the merged-block image, `t = s.1 ∪ (M.e s).1` with
`s.1 = mergedOfLeft T s.2 ∩ A` and (by definition of `ofFinpartition`'s `e`)
`(M.e s).1 = mergedOfLeft T s.2 ∩ B`, so `t = mergedOfLeft T s.2 ∈ T.parts`.

This closure argument was fully carried out in an earlier draft of this file (all cases above were
individually verified against `lake env lean`) but tripped on a parenthesisation bug in the
`t ∈ (T.restrict h).parts` rewrites (`T.restrict h |>.parts` mis-parses); redo those four
occurrences with explicit parentheses `(T.restrict h).parts` and the proof goes through with the
same case structure as `restrict_glue_left`/`restrict_glue_right` below. -/
lemma glue_ofFinpartition (T : Finpartition (A ∪ B)) (hAB : Disjoint A B) :
    (ofFinpartition T hAB).glue hAB = T := by
  apply Finpartition.ext
  simp [glue_parts, Finset.Subset.antisymm (glueParts_subset_parts T hAB)
    (parts_subset_glueParts T hAB)]

/-- Matchings between the blocks of `π` and `σ` form a finite type: a matching is the same data as
a pair of subsets of `π.parts`, `σ.parts` together with a bijection between their coercions. -/
noncomputable instance instFintype : Fintype (Matching π σ) := by
  haveI : Fintype {S : Finset (Finset α) // S ⊆ π.parts} :=
    Fintype.subtype π.parts.powerset (fun S => Finset.mem_powerset)
  haveI : Fintype {T : Finset (Finset α) // T ⊆ σ.parts} :=
    Fintype.subtype σ.parts.powerset (fun T => Finset.mem_powerset)
  haveI : DecidableEq {S : Finset (Finset α) // S ⊆ π.parts} := Subtype.instDecidableEq
  haveI : DecidableEq {T : Finset (Finset α) // T ⊆ σ.parts} := Subtype.instDecidableEq
  exact Fintype.ofEquiv
    (Σ' (S' : {S : Finset (Finset α) // S ⊆ π.parts}) (T' : {T : Finset (Finset α) // T ⊆ σ.parts}),
      ({p // p ∈ S'.1} ≃ {q // q ∈ T'.1}))
    { toFun := fun x => ⟨x.1.1, x.2.1.1, x.1.2, x.2.1.2, x.2.2⟩
      invFun := fun M => ⟨⟨M.S, M.hS⟩, ⟨M.T, M.hT⟩, M.e⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- `M.glue hAB` restricted back to `A` recovers `π`. -/
lemma restrict_glue_left (M : Matching π σ) (hAB : Disjoint A B) :
    (M.glue hAB).restrict (Finset.subset_union_left) = π := by
  apply Finpartition.ext
  ext t
  rw [Finpartition.restrict, Finset.mem_erase, Finset.mem_image]
  simp only [Finset.inf_eq_inter]
  constructor
  · rintro ⟨htne, D, hD, rfl⟩
    rw [glue_parts, glueParts, Finset.mem_union, Finset.mem_union] at hD
    rcases hD with (hD | hD) | hD
    · rw [Finset.inter_eq_left.mpr (π.subset (Finset.mem_sdiff.mp hD).1)]
      exact (Finset.mem_sdiff.mp hD).1
    · exfalso
      apply htne
      apply Finset.eq_empty_of_forall_notMem
      intro y hy
      rcases Finset.mem_inter.mp hy with ⟨hyD, hyA⟩
      exact (Finset.disjoint_left.mp hAB hyA) (σ.subset (Finset.mem_sdiff.mp hD).1 hyD)
    · obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hD
      rw [union_inter_left_of_subset hAB (π.subset (M.hS s.2)) (σ.subset (M.hT (M.e s).2))]
      exact M.hS s.2
  · intro ht
    by_cases hmatch : t ∈ M.S
    · refine ⟨Finset.nonempty_iff_ne_empty.mp (π.nonempty_of_mem_parts ht),
        t ∪ (M.e ⟨t, hmatch⟩).1, ?_, ?_⟩
      · rw [glue_parts, glueParts]
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨⟨t, hmatch⟩, Finset.mem_attach _ _, rfl⟩)
      · exact union_inter_left_of_subset hAB (π.subset ht) (σ.subset (M.hT (M.e ⟨t, hmatch⟩).2))
    · refine ⟨Finset.nonempty_iff_ne_empty.mp (π.nonempty_of_mem_parts ht), t, ?_, ?_⟩
      · rw [glue_parts, glueParts]
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ht, hmatch⟩))
      · exact Finset.inter_eq_left.mpr (π.subset ht)

/-- `M.glue hAB` restricted back to `B` recovers `σ`. -/
lemma restrict_glue_right (M : Matching π σ) (hAB : Disjoint A B) :
    (M.glue hAB).restrict (Finset.subset_union_right) = σ := by
  apply Finpartition.ext
  ext t
  rw [Finpartition.restrict, Finset.mem_erase, Finset.mem_image]
  simp only [Finset.inf_eq_inter]
  constructor
  · rintro ⟨htne, D, hD, rfl⟩
    rw [glue_parts, glueParts, Finset.mem_union, Finset.mem_union] at hD
    rcases hD with (hD | hD) | hD
    · exfalso
      apply htne
      apply Finset.eq_empty_of_forall_notMem
      intro y hy
      rcases Finset.mem_inter.mp hy with ⟨hyD, hyB⟩
      exact (Finset.disjoint_left.mp hAB (π.subset (Finset.mem_sdiff.mp hD).1 hyD)) hyB
    · rw [Finset.inter_eq_left.mpr (σ.subset (Finset.mem_sdiff.mp hD).1)]
      exact (Finset.mem_sdiff.mp hD).1
    · obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hD
      rw [union_inter_right_of_subset hAB (π.subset (M.hS s.2)) (σ.subset (M.hT (M.e s).2))]
      exact M.hT (M.e s).2
  · intro ht
    by_cases hmatch : t ∈ M.T
    · refine ⟨Finset.nonempty_iff_ne_empty.mp (σ.nonempty_of_mem_parts ht),
        (M.e.symm ⟨t, hmatch⟩).1 ∪ t, ?_, ?_⟩
      · rw [glue_parts, glueParts]
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨M.e.symm ⟨t, hmatch⟩, Finset.mem_attach _ _, by rw [Equiv.apply_symm_apply]⟩)
      · rw [union_inter_right_of_subset hAB (π.subset (M.hS (M.e.symm ⟨t, hmatch⟩).2))
          (σ.subset ht)]
    · refine ⟨Finset.nonempty_iff_ne_empty.mp (σ.nonempty_of_mem_parts ht), t, ?_, ?_⟩
      · rw [glue_parts, glueParts]
        exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨ht, hmatch⟩))
      · exact Finset.inter_eq_left.mpr (σ.subset ht)

/-- In the glue of a matching, the blocks meeting both sides of the cut are exactly the merged
blocks. -/
lemma mergedOf_glue (M : Matching π σ) (hAB : Disjoint A B) :
    mergedOf (M.glue hAB) =
      M.S.attach.image (fun s => (s.1 : Finset α) ∪ (M.e s).1) := by
  ext t
  rw [mergedOf, glue_parts]
  constructor
  · intro ht
    rw [Finset.mem_filter, glueParts, Finset.mem_union, Finset.mem_union] at ht
    rcases ht with ⟨(ht | ht) | ht, hspan⟩
    · exact False.elim (hspan.2.elim fun x hx =>
        (Finset.disjoint_left.mp hAB)
          (π.subset (Finset.mem_sdiff.mp ht).1 (Finset.mem_inter.mp hx).1)
          (Finset.mem_inter.mp hx).2)
    · exact False.elim (hspan.1.elim fun x hx =>
        (Finset.disjoint_left.mp hAB)
          (Finset.mem_inter.mp hx).2
          (σ.subset (Finset.mem_sdiff.mp ht).1 (Finset.mem_inter.mp hx).1))
    · exact ht
  · intro ht
    rw [Finset.mem_filter, glueParts]
    exact ⟨Finset.mem_union_right _ ht, M.merged_inter_nonempty hAB ht⟩

-- Intersecting a merged block of `M` with `A` recovers its `π`-side: if a merged block has
-- `A`-trace `p`, then `p` is a matched `π`-block of `M`.
private lemma mem_left_of_merged_inter (M : Matching π σ) (hAB : Disjoint A B)
    {p t : Finset α} (ht : t ∈ M.S.attach.image (fun s => (s.1 : Finset α) ∪ (M.e s).1))
    (htp : t ∩ A = p) : p ∈ M.S := by
  obtain ⟨s, -, hs⟩ := Finset.mem_image.mp ht
  -- The trace of the merged block `s.1 ∪ (M.e s).1` on `A` is exactly `s.1`, so `p = s.1`.
  have hleft := union_inter_left_of_subset hAB (π.subset (M.hS s.2)) (σ.subset (M.hT (M.e s).2))
  have hp_eq := (htp.symm.trans (congrArg (· ∩ A) hs).symm).trans hleft
  exact hp_eq ▸ s.2

-- Intersecting a merged block of `M` with `B` recovers its `σ`-side: if a merged block has
-- `B`-trace `q`, then `q` is a matched `σ`-block of `M`.
private lemma mem_right_of_merged_inter (M : Matching π σ) (hAB : Disjoint A B)
    {q t : Finset α} (ht : t ∈ M.S.attach.image (fun s => (s.1 : Finset α) ∪ (M.e s).1))
    (htq : t ∩ B = q) : q ∈ M.T := by
  obtain ⟨s, -, hs⟩ := Finset.mem_image.mp ht
  -- The trace of the merged block `s.1 ∪ (M.e s).1` on `B` is exactly `(M.e s).1`, so `q` is
  -- the matched `σ`-block.
  have hright := union_inter_right_of_subset hAB (π.subset (M.hS s.2)) (σ.subset (M.hT (M.e s).2))
  have hq_eq := (htq.symm.trans (congrArg (· ∩ B) hs).symm).trans hright
  exact hq_eq ▸ (M.e s).2

-- If two matchings glue to the same partition, their matched `π`-blocks agree: every merged
-- block of `M₁` occurs among the merged blocks of `M₂`, and its `A`-trace pins down the
-- `π`-side.
private lemma S_eq_of_glue_eq (M₁ M₂ : Matching π σ) (hAB : Disjoint A B)
    (hglue : M₁.glue hAB = M₂.glue hAB) : M₁.S = M₂.S := by
  ext p
  constructor
  · intro hp
    -- The merged block of `M₁` containing `p` lies in the common merged-block set of `M₂`.
    exact mem_left_of_merged_inter M₂ hAB
      (by
        rw [← M₂.mergedOf_glue hAB, ← hglue, M₁.mergedOf_glue hAB]
        exact Finset.mem_image.mpr ⟨⟨p, hp⟩, Finset.mem_attach _ _, rfl⟩)
      (union_inter_left_of_subset hAB (π.subset (M₁.hS hp))
        (σ.subset (M₁.hT (M₁.e ⟨p, hp⟩).2)))
  · intro hp
    -- Symmetric: transfer `p`'s merged block of `M₂` back to `M₁` using `hglue.symm`.
    exact mem_left_of_merged_inter M₁ hAB
      (by
        rw [← M₁.mergedOf_glue hAB, ← hglue.symm, M₂.mergedOf_glue hAB]
        exact Finset.mem_image.mpr ⟨⟨p, hp⟩, Finset.mem_attach _ _, rfl⟩)
      (union_inter_left_of_subset hAB (π.subset (M₂.hS hp))
        (σ.subset (M₂.hT (M₂.e ⟨p, hp⟩).2)))

-- If two matchings glue to the same partition, their matched `σ`-blocks agree, by the
-- symmetric argument on the `B`-side of the cut.
private lemma T_eq_of_glue_eq (M₁ M₂ : Matching π σ) (hAB : Disjoint A B)
    (hglue : M₁.glue hAB = M₂.glue hAB) : M₁.T = M₂.T := by
  ext q
  constructor
  · intro hq
    -- The merged block of `M₁` whose `σ`-side is `q` lies in the common merged-block set.
    let s₁ := M₁.e.symm ⟨q, hq⟩
    exact mem_right_of_merged_inter M₂ hAB
      (by
        rw [← M₂.mergedOf_glue hAB, ← hglue, M₁.mergedOf_glue hAB]
        exact Finset.mem_image.mpr ⟨s₁, Finset.mem_attach _ _, by simp [s₁]⟩)
      (union_inter_right_of_subset hAB (π.subset (M₁.hS s₁.2)) (σ.subset (M₁.hT hq)))
  · intro hq
    -- Symmetric: transfer `q`'s merged block of `M₂` back to `M₁` using `hglue.symm`.
    let s₂ := M₂.e.symm ⟨q, hq⟩
    exact mem_right_of_merged_inter M₁ hAB
      (by
        rw [← M₁.mergedOf_glue hAB, ← hglue.symm, M₂.mergedOf_glue hAB]
        exact Finset.mem_image.mpr ⟨s₂, Finset.mem_attach _ _, by simp [s₂]⟩)
      (union_inter_right_of_subset hAB (π.subset (M₂.hS s₂.2)) (σ.subset (M₂.hT hq)))

-- If two matchings glue to the same partition, they are equal: the two previous lemmas give
-- `S`- and `T`-equality, and intersecting a common merged block with `A` (resp. `B`) pins down
-- the matched pair `s ↦ (s.1, (e s).1)`, so `e₁ = e₂` by `Equiv.ext`.
private lemma eq_of_glue_eq (M₁ M₂ : Matching π σ) (hAB : Disjoint A B)
    (hglue : M₁.glue hAB = M₂.glue hAB) : M₁ = M₂ := by
  have hS := S_eq_of_glue_eq M₁ M₂ hAB hglue
  have hT := T_eq_of_glue_eq M₁ M₂ hAB hglue
  rcases M₁ with ⟨S₁, T₁, hS₁, hT₁, e₁⟩
  rcases M₂ with ⟨S₂, T₂, hS₂, hT₂, e₂⟩
  cases hS
  cases hT
  congr
  ext s
  let M₁' : Matching π σ := { S := S₁, T := T₁, hS := hS₁, hT := hT₁, e := e₁ }
  let M₂' : Matching π σ := { S := S₁, T := T₁, hS := hS₂, hT := hT₂, e := e₂ }
  have hmerged : s.1 ∪ (e₁ s).1 ∈
      S₁.attach.image (fun s => (s.1 : Finset α) ∪ (e₂ s).1) := by
    rw [← M₂'.mergedOf_glue hAB, ← hglue, M₁'.mergedOf_glue hAB]
    exact Finset.mem_image.mpr ⟨s, Finset.mem_attach _ _, rfl⟩
  obtain ⟨s', -, hs'⟩ := Finset.mem_image.mp hmerged
  have hleft₁ := union_inter_left_of_subset hAB (π.subset (hS₁ s.2)) (σ.subset (hT₁ (e₁ s).2))
  have hleft₂ := union_inter_left_of_subset hAB (π.subset (hS₂ s'.2)) (σ.subset (hT₂ (e₂ s').2))
  have hs_eq := Subtype.ext ((hleft₁.symm.trans (congrArg (· ∩ A) hs').symm).trans hleft₂)
  subst s'
  have hright₁ := union_inter_right_of_subset hAB (π.subset (hS₁ s.2)) (σ.subset (hT₁ (e₁ s).2))
  have hright₂ := union_inter_right_of_subset hAB (π.subset (hS₂ s.2)) (σ.subset (hT₂ (e₂ s).2))
  have heq_fin := (hright₁.symm.trans (congrArg (· ∩ B) hs').symm).trans hright₂
  rw [heq_fin]

/-- Distinct matchings glue to distinct partitions of `A ∪ B`.

Informal proof.  Suppose `M.glue hAB = M'.glue hAB =: T`.  A block of `T` meets both `A` and `B`
exactly when it is a merged block, i.e. `mergedOf T = M.S.attach.image (fun s => s.1 ∪ (M.e s).1)
= M'.S.attach.image (fun s => s.1 ∪ (M'.e s).1)` (unmatched blocks lie entirely on one side by
`merged_inter_nonempty`/disjointness, exactly as in `glue_ofFinpartition`).  Intersecting this
common set of blocks with `A` (respectively `B`) and using `union_inter_left_of_subset`/
`union_inter_right_of_subset` identifies it with `M.S` and with `M'.S` (respectively `M.T`,
`M'.T`), so `M.S = M'.S` and `M.T = M'.T`.  Finally, for `s : ↥M.S`, the block `s.1 ∪ (M.e s).1`
lies in the common merged-block set, hence equals `s'.1 ∪ (M'.e s').1` for some `s' : ↥M'.S = ↥M.S`;
intersecting with `A` forces `s' = s`, and intersecting with `B` then forces
`(M.e s).1 = (M'.e s).1`; so `M.e = M'.e` by `Equiv.ext`, giving `M = M'`. -/
lemma glue_injective (hAB : Disjoint A B) :
    Function.Injective (fun M : Matching π σ => M.glue hAB) :=
  fun M₁ M₂ hglue => eq_of_glue_eq M₁ M₂ hAB hglue

/-- The number of size-`m` matchings between `π` and `σ` is `p.choose m * q.choose m * m!`, where
`p = π.parts.card`, `q = σ.parts.card`.

Informal proof.  A size-`m` matching is the same data as a choice of `m`-element subsets
`S ⊆ π.parts`, `T ⊆ σ.parts` (`p.choose m * q.choose m` ways, by `Finset.card_powersetCard`)
together with a bijection `↥S ≃ ↥T` (`m!` ways by `Fintype.card_equiv`, applicable since
`|S| = |T| = m`).  Formally: biject `{M : Matching π σ // M.size = m}` with
`Σ (S ∈ π.parts.powersetCard m) (T ∈ σ.parts.powersetCard m), (↥S ≃ ↥T)` via
`M ↦ ⟨M.S, M.T, M.e⟩` (using `card_T_eq_card_S` for well-definedness of the target `T`'s membership
in `σ.parts.powersetCard m`), with inverse packaging `⟨S, T, e⟩` plus the subset proofs back into a
`Matching`; then take `Fintype.card` of both sides via `Fintype.card_congr` and
`Fintype.card_sigma`. -/
private lemma card_equiv_between_finsets_of_card_eq {γ δ : Type*} [DecidableEq γ] [DecidableEq δ]
    (S : Finset γ) (T : Finset δ)
    {m : ℕ} (hS : S.card = m) (hT : T.card = m) :
    Fintype.card ({x // x ∈ S} ≃ {y // y ∈ T}) = m.factorial := by
  rw [Fintype.card_equiv (Fintype.card_eq.mp (by simp [hS, hT])).some,
    Fintype.card_coe, hS]

-- The data of a size-`m` matching: an `m`-subset of `π.parts`, an `m`-subset of `σ.parts`,
-- and a bijection between the two.  `π` and `σ` are explicit so that the type is fully
-- determined at use sites (the original `let Ω` relied on `classical` to fill them in).
private abbrev matchingSizeFiber (π : Finpartition A) (σ : Finpartition B) (m : ℕ) : Type _ :=
  Σ (S' : {S : Finset (Finset α) // S ∈ π.parts.powersetCard m}),
    Σ (T' : {T : Finset (Finset α) // T ∈ σ.parts.powersetCard m}),
      ({p // p ∈ S'.1} ≃ {q // q ∈ T'.1})

-- A size-`m` matching is the same data as a choice of `m`-subsets `S ⊆ π.parts`, `T ⊆ σ.parts`
-- together with a bijection `↥S ≃ ↥T`; this bijection exhibits that equivalence, so cardinalities
-- can be transported between the two types.
private noncomputable def matchingSizeEquiv (m : ℕ) :
    {M : Matching π σ // M.size = m} ≃ matchingSizeFiber π σ m :=
  { toFun := fun ⟨M, hsize⟩ =>
      ⟨⟨M.S, Finset.mem_powersetCard.mpr ⟨M.hS, by simpa [size] using hsize⟩⟩,
        ⟨⟨M.T, Finset.mem_powersetCard.mpr ⟨M.hT,
          by simpa [size, card_T_eq_card_S M] using hsize⟩⟩, M.e⟩⟩
    invFun := fun x =>
      ⟨{ S := x.1.1
         T := x.2.1.1
         hS := (Finset.mem_powersetCard.mp x.1.2).1
         hT := (Finset.mem_powersetCard.mp x.2.1.2).1
         e := x.2.2 },
        by simpa [size] using (Finset.mem_powersetCard.mp x.1.2).2⟩
    left_inv := by
      rintro ⟨⟨S, T, hS, hT, e⟩, hsize⟩
      simp
    right_inv := by
      rintro ⟨⟨S, hS⟩, ⟨⟨T, hT⟩, e⟩⟩
      simp }

-- Counting the fibers: choosing `S`, `T`, and a bijection between them yields
-- `p.choose m * q.choose m * m!` elements (via `Finset.card_powersetCard` for the choices).
private lemma card_matchingSizeFiber (m : ℕ) :
    Fintype.card (matchingSizeFiber π σ m) =
      π.parts.card.choose m * σ.parts.card.choose m * m.factorial := by
  have hfiber : ∀ (S' : {S : Finset (Finset α) // S ∈ π.parts.powersetCard m})
      (T' : {T : Finset (Finset α) // T ∈ σ.parts.powersetCard m}),
      Fintype.card ({p // p ∈ S'.1} ≃ {q // q ∈ T'.1}) = m.factorial :=
    fun S' T' =>
      card_equiv_between_finsets_of_card_eq S'.1 T'.1
        (Finset.mem_powersetCard.mp S'.2).2 (Finset.mem_powersetCard.mp T'.2).2
  simp [matchingSizeFiber, hfiber, Finset.sum_const, Nat.mul_assoc]

lemma card_filter_size_eq (m : ℕ) :
    (Finset.univ.filter (fun M : Matching π σ => M.size = m)).card =
      π.parts.card.choose m * σ.parts.card.choose m * m.factorial := by
  rw [← Fintype.card_subtype (fun M : Matching π σ => M.size = m),
    Fintype.card_congr (matchingSizeEquiv m), card_matchingSizeFiber m]

/-- A matching has size at most the smaller number of available blocks. -/
lemma size_le_min (M : Matching π σ) : M.size ≤ Nat.min π.parts.card σ.parts.card := by
  simp only [size]
  exact le_min (Finset.card_le_card M.hS)
    (by simpa [M.card_T_eq_card_S] using (Finset.card_le_card M.hT))

/-- Sum a coefficient depending only on the matching size by first choosing the size.

This is the purely enumerative last step in the trace-pair decomposition: the fiber of
`M ↦ M.size` over `m` has cardinality `(p choose m) (q choose m) m!`, as counted by
`card_filter_size_eq`, and there are no fibers outside `range (min p q + 1)` by `size_le_min`. -/
lemma sum_coeff_by_size {R : Type*} [CommRing R]
    (c : ℕ → R) :
    (∑ M : Matching π σ, c M.size) =
      ∑ m ∈ Finset.range (Nat.min π.parts.card σ.parts.card + 1),
        (((π.parts.card.choose m) * (σ.parts.card.choose m) * m.factorial : ℕ) : R) * c m := by
  have hmaps : ((Finset.univ : Finset (Matching π σ)) : Set (Matching π σ)).MapsTo size
      (Finset.range (Nat.min π.parts.card σ.parts.card + 1)) :=
    fun M _ => by simpa [Finset.mem_range] using Nat.lt_succ_of_le M.size_le_min
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  simp_rw [Finset.sum_filter]
  exact Finset.sum_congr rfl (fun m _ => by
    calc
      ∑ x : Matching π σ, (if size x = m then c (size x) else 0) =
          ∑ x : Matching π σ, (if size x = m then c m else 0) := by
        exact Finset.sum_congr rfl (fun x _ => by by_cases hx : size x = m <;> simp [hx])
      _ = ((Finset.univ.filter (fun M : Matching π σ => M.size = m)).card : R) * c m := by
        simp [Finset.sum_const, nsmul_eq_mul, ← Finset.sum_filter]
      _ = (((π.parts.card.choose m) * (σ.parts.card.choose m) * m.factorial : ℕ) : R) * c m := by
        rw [Matching.card_filter_size_eq])

end Matching

-- Turn a fiber element into a matching: extract the merged blocks via `Matching.ofFinpartition`
-- and transport the type along the two trace equalities `hπ`, `hσ`.
private noncomputable def traceFiberToMatching (π : Finpartition A) (σ : Finpartition B)
    (hAB : Disjoint A B) (T : Finpartition (A ∪ B))
    (hπ : T.restrict (Finset.subset_union_left) = π)
    (hσ : T.restrict (Finset.subset_union_right) = σ) : Matching π σ := by
  cases hπ
  cases hσ
  exact Matching.ofFinpartition T hAB

-- Round-trip 1: gluing the matching extracted from `T` recovers `T` (`Matching.glue_ofFinpartition`
-- applied after the transport along the trace equalities collapses to `rfl`).
private lemma glue_traceFiberToMatching (π : Finpartition A) (σ : Finpartition B)
    (hAB : Disjoint A B) (T : Finpartition (A ∪ B))
    (hπ : T.restrict (Finset.subset_union_left) = π)
    (hσ : T.restrict (Finset.subset_union_right) = σ) :
    (traceFiberToMatching π σ hAB T hπ hσ).glue hAB = T := by
  cases hπ
  cases hσ
  exact Matching.glue_ofFinpartition T hAB

-- Round-trip 2: extracting from the glue of `M` recovers `M`.  We use injectivity of `glue`
-- (`Matching.glue_injective`) together with round-trip 1 applied to `M.glue hAB`.
private lemma traceFiberToMatching_glue (π : Finpartition A) (σ : Finpartition B)
    (hAB : Disjoint A B) (M : Matching π σ) :
    traceFiberToMatching π σ hAB (M.glue hAB) (Matching.restrict_glue_left M hAB)
        (Matching.restrict_glue_right M hAB) = M :=
  Matching.glue_injective hAB
    (glue_traceFiberToMatching π σ hAB (M.glue hAB) (Matching.restrict_glue_left M hAB)
      (Matching.restrict_glue_right M hAB))

-- The extracted matching is independent of which proofs of the two trace equalities are supplied
-- (both are propositions, so the transported data is the same).  This makes the fiber reindexing
-- well-defined even when the membership proof of the fiber is constructed in two different ways.
private lemma traceFiberToMatching_congr (π : Finpartition A) (σ : Finpartition B)
    (hAB : Disjoint A B) (T : Finpartition (A ∪ B))
    (hπ : T.restrict (Finset.subset_union_left) = π)
    (hπ' : T.restrict (Finset.subset_union_left) = π)
    (hσ : T.restrict (Finset.subset_union_right) = σ)
    (hσ' : T.restrict (Finset.subset_union_right) = σ) :
    traceFiberToMatching π σ hAB T hπ hσ = traceFiberToMatching π σ hAB T hπ' hσ' := by
  cases hπ; cases hσ; cases hπ'; cases hσ'
  rfl

-- The cumulant summand of a glued partition `M.glue hAB` factors into the two trace block
-- products and a coefficient depending only on `M.size`: the block product splits across the cut
-- (`hsplit` applied to each matched pair), and `Matching.card_glueParts` identifies the number of
-- blocks of the glued partition as `p + q - |M|`.
private lemma glue_summand_eq {R : Type*} [CommRing R] (hAB : Disjoint A B)
    (f : Finset α → R) (hsplit : ∀ D : Finset α, f D = f (D ∩ A) * f (D ∩ B))
    (π : Finpartition A) (σ : Finpartition B) (M : Matching π σ) :
    cumulantCoefficient (M.glue hAB) * (M.glue hAB).blockProduct f =
      (π.blockProduct f * σ.blockProduct f) *
        ((-1 : R) ^ (π.parts.card + σ.parts.card - M.size - 1) *
          ((π.parts.card + σ.parts.card - M.size - 1).factorial : R)) := by
  have hcoeff : cumulantCoefficient (M.glue hAB) =
      (-1 : R) ^ (π.parts.card + σ.parts.card - M.size - 1) *
        ((π.parts.card + σ.parts.card - M.size - 1).factorial : R) := by
    simp [cumulantCoefficient, Matching.card_glueParts M hAB]
  have hblock : (M.glue hAB).blockProduct f = π.blockProduct f * σ.blockProduct f :=
    Matching.blockProduct_glue M hAB f (fun s => by
      -- per matched pair, `hsplit` turns the union into the product of the two traces
      rw [hsplit ((s.1 : Finset α) ∪ (M.e s).1),
        union_inter_left_of_subset hAB (π.subset (M.hS s.2)) (σ.subset (M.hT (M.e s).2)),
        union_inter_right_of_subset hAB (π.subset (M.hS s.2)) (σ.subset (M.hT (M.e s).2))])
  rw [hblock, hcoeff, mul_comm]

-- Regroup the defining sum over all partitions of `A ∪ B` by the trace pair: first by the
-- `A`-trace, then by the `B`-trace inside each `A`-class (`Finset.sum_fiberwise` on the product
-- type `Finpartition A × Finpartition B`).
private lemma sum_cumulant_by_trace {R : Type*} [CommRing R] (f : Finset α → R) :
    (∑ T : Finpartition (A ∪ B), cumulantCoefficient T * T.blockProduct f) =
      ∑ π : Finpartition A, ∑ σ : Finpartition B,
        ∑ T ∈ Finset.univ.filter (fun T : Finpartition (A ∪ B) =>
            T.restrict (Finset.subset_union_left) = π ∧ T.restrict (Finset.subset_union_right) = σ),
          cumulantCoefficient T * T.blockProduct f := by
  classical
  calc
    (∑ T : Finpartition (A ∪ B), cumulantCoefficient T * T.blockProduct f)
        = ∑ π : Finpartition A, ∑ σ : Finpartition B,
            ∑ T ∈ Finset.univ.filter (fun T : Finpartition (A ∪ B) =>
                (T.restrict (Finset.subset_union_left), T.restrict (Finset.subset_union_right)) = (π, σ)),
              cumulantCoefficient T * T.blockProduct f := by
      rw [← Finset.sum_fiberwise (Finset.univ : Finset (Finpartition (A ∪ B)))
        (fun T => (T.restrict (Finset.subset_union_left), T.restrict (Finset.subset_union_right)))
        (fun T => cumulantCoefficient T * T.blockProduct f),
        Fintype.sum_prod_type]
    _ = ∑ π : Finpartition A, ∑ σ : Finpartition B,
          ∑ T ∈ Finset.univ.filter (fun T : Finpartition (A ∪ B) =>
              T.restrict (Finset.subset_union_left) = π ∧ T.restrict (Finset.subset_union_right) = σ),
            cumulantCoefficient T * T.blockProduct f :=
      Finset.sum_congr rfl (fun π _ => Finset.sum_congr rfl (fun σ _ =>
        Finset.sum_congr (by ext T; simp [Prod.ext_iff]) (fun _ _ => rfl)))

-- Within a fixed trace pair fiber, the sum over partitions reindexes along the bijection
-- `M ↦ M.glue hAB` (`traceFiberToMatching` is the inverse, see the two round-trip lemmas above).
private lemma sum_traceFiber_eq_sum_matching {R : Type*} [CommRing R] (hAB : Disjoint A B)
    (f : Finset α → R) (π : Finpartition A) (σ : Finpartition B) :
    (∑ T ∈ Finset.univ.filter (fun T : Finpartition (A ∪ B) =>
        T.restrict (Finset.subset_union_left) = π ∧ T.restrict (Finset.subset_union_right) = σ),
      cumulantCoefficient T * T.blockProduct f) =
      ∑ M : Matching π σ, cumulantCoefficient (M.glue hAB) * (M.glue hAB).blockProduct f := by
  classical
  -- `Finset.sum_bij` with `T ↦ traceFiberToMatching π σ hAB T ...`; injectivity and surjectivity
  -- are the two round-trip lemmas, and the summand equality is round-trip 1 applied to `T`.
  apply Finset.sum_bij (fun T hT =>
      traceFiberToMatching π σ hAB T (Finset.mem_filter.mp hT).2.1 (Finset.mem_filter.mp hT).2.2)
  · intro T _
    exact Finset.mem_univ _
  · intro T₁ hT₁ T₂ hT₂ h
    -- injectivity: two matchings that glue to the same partition are equal
    simpa [glue_traceFiberToMatching π σ hAB T₁ (Finset.mem_filter.mp hT₁).2.1
        (Finset.mem_filter.mp hT₁).2.2,
      glue_traceFiberToMatching π σ hAB T₂ (Finset.mem_filter.mp hT₂).2.1
        (Finset.mem_filter.mp hT₂).2.2] using
        congrArg (fun M : Matching π σ => M.glue hAB) h
  · intro M _
    -- surjectivity: `M` is extracted from its own glue
    have hmem : M.glue hAB ∈ Finset.univ.filter (fun T : Finpartition (A ∪ B) =>
        T.restrict (Finset.subset_union_left) = π ∧ T.restrict (Finset.subset_union_right) = σ) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ⟨Matching.restrict_glue_left M hAB, Matching.restrict_glue_right M hAB⟩⟩
    -- the extracted matching differs from `M` only by the choice of the trace-equality proofs
    exact ⟨M.glue hAB, hmem,
      (traceFiberToMatching_congr π σ hAB (M.glue hAB) (Finset.mem_filter.mp hmem).2.1
        (Matching.restrict_glue_left M hAB) (Finset.mem_filter.mp hmem).2.2
        (Matching.restrict_glue_right M hAB)).trans (traceFiberToMatching_glue π σ hAB M)⟩
  · intro T hT
    -- the summand of `T` is the glued summand of the matching extracted from `T`
    rw [glue_traceFiberToMatching π σ hAB T (Finset.mem_filter.mp hT).2.1
      (Finset.mem_filter.mp hT).2.2]

/-- The cumulant transform of a function that factors multiplicatively across a cut `A | B`
reindexes as a double sum over the trace partitions of `A` and `B`, with the fiber over each trace
pair collapsing to the partial-matching coefficient sum.  This is the reusable regrouping identity
behind `Renormalization.cumulantTransform_tracePair_partialMatching_regrouping`.

Informal proof.  Unfold `cumulantTransform` (using `A ∪ B ≠ ∅`) as
`∑ T : Finpartition (A ∪ B), cumulantCoefficient T * T.blockProduct f`.  Group this sum by the pair
of traces `(T.restrict subset_union_left, T.restrict subset_union_right)` using
`Finset.sum_fiberwise` twice (first by the `A`-trace, then by the `B`-trace within each class).  For
fixed traces `π, σ`, the fiber `{T // T.restrict_left = π ∧ T.restrict_right = σ}` is in bijection
with `Matching π σ` via `M ↦ M.glue hAB`: injective by `Matching.glue_injective`, and surjective
because for `T` in the fiber, `M := Matching.ofFinpartition T hAB` satisfies
`M.glue hAB = T` (`Matching.glue_ofFinpartition`) after transporting `M`'s type along
`Matching.restrict_glue_left`/`Matching.restrict_glue_right`-style trace identities (here directly
`T.restrict_left = π`, `T.restrict_right = σ` from fiber membership).  Reindexing the fiber sum
along this bijection (`Finset.sum_bij` using `Matching.glue_injective` for injectivity and the above
for surjectivity) and applying `Matching.blockProduct_glue` (with `hsplit` supplying the per-pair
multiplicativity hypothesis via `union_inter_left_of_subset`/`union_inter_right_of_subset`) and
`Matching.card_glueParts` (for `cumulantCoefficient`, i.e. `Finpartition.cumulantCoefficient`)
turns each fiber sum into
`(π.blockProduct f * σ.blockProduct f) * ∑ M : Matching π σ, coeff (M.size)`
where `coeff k := (-1) ^ (p + q - k - 1) * (p + q - k - 1)!`.  Finally, group `Matching π σ` by
`M.size` (`Finset.sum_fiberwise` once more) and use `Matching.card_filter_size_eq` to identify the
count of each size class as `p.choose m * q.choose m * m!`; restrict the resulting sum over `m : ℕ`
to `Finset.range (min p q + 1)` since `Matching.size` never exceeds `min p q` (`M.S ⊆ π.parts`,
`M.T ⊆ σ.parts`), so every term with `m > min p q` has an empty size-class and contributes `0`. -/
/- The trace/glue regrouping before counting matchings by size.

Informal proof. Expand `cumulantTransform` using `hne`. Regroup a partition `T` of `A ∪ B` by
its two restrictions to `A` and `B`. For fixed traces `π` and `σ`, the fiber is in bijection with
`Matching π σ` via `M ↦ M.glue hAB`; injectivity is `Matching.glue_injective` and surjectivity is
`Matching.ofFinpartition` plus `Matching.glue_ofFinpartition` (`traceFiberToMatching` with the two
round-trip lemmas `glue_traceFiberToMatching`/`traceFiberToMatching_glue`). On a glued partition,
`Matching.blockProduct_glue` turns the block product into `π.blockProduct f * σ.blockProduct f`,
with `hsplit` applied to each matched union using `union_inter_left_of_subset` and
`union_inter_right_of_subset`; `Matching.card_glueParts` changes the cumulant coefficient to the
coefficient depending on `M.size` displayed below. The separate, fully formalized counting of
matchings by size happens in `cumulantTransform_eq_sum_matching`. -/
lemma cumulantTransform_eq_sum_matchings_by_trace {R : Type*} [CommRing R]
    (hAB : Disjoint A B) (hne : A ∪ B ≠ ∅) (f : Finset α → R)
    (hsplit : ∀ D : Finset α, f D = f (D ∩ A) * f (D ∩ B)) :
    cumulantTransform f (A ∪ B) =
      ∑ π : Finpartition A, ∑ σ : Finpartition B, (π.blockProduct f * σ.blockProduct f) *
        (∑ M : Matching π σ,
          ((-1 : R) ^ (π.parts.card + σ.parts.card - M.size - 1) *
            ((π.parts.card + σ.parts.card - M.size - 1).factorial : R))) := by
  classical
  calc
    cumulantTransform f (A ∪ B) =
        ∑ T : Finpartition (A ∪ B), cumulantCoefficient T * T.blockProduct f := by
      -- `A ∪ B ≠ ∅`, so `cumulantTransform` uses its nonempty (sum) branch
      simp [cumulantTransform, hne]
    _ = ∑ π : Finpartition A, ∑ σ : Finpartition B,
          ∑ T ∈ Finset.univ.filter (fun T : Finpartition (A ∪ B) =>
              T.restrict (Finset.subset_union_left) = π ∧ T.restrict (Finset.subset_union_right) = σ),
            cumulantCoefficient T * T.blockProduct f :=
      sum_cumulant_by_trace f
    _ = ∑ π : Finpartition A, ∑ σ : Finpartition B,
          ∑ M : Matching π σ, cumulantCoefficient (M.glue hAB) * (M.glue hAB).blockProduct f :=
      Finset.sum_congr rfl (fun π _ => Finset.sum_congr rfl (fun σ _ =>
        sum_traceFiber_eq_sum_matching hAB f π σ))
    _ = ∑ π : Finpartition A, ∑ σ : Finpartition B, (π.blockProduct f * σ.blockProduct f) *
          (∑ M : Matching π σ,
            ((-1 : R) ^ (π.parts.card + σ.parts.card - M.size - 1) *
              ((π.parts.card + σ.parts.card - M.size - 1).factorial : R))) :=
      Finset.sum_congr rfl (fun π _ => Finset.sum_congr rfl (fun σ _ =>
        (Finset.sum_congr rfl (fun M _ => glue_summand_eq hAB f hsplit π σ M)).trans (by
          simp [Finset.mul_sum])))

lemma cumulantTransform_eq_sum_matching {R : Type*} [CommRing R] (hAB : Disjoint A B)
    (hne : A ∪ B ≠ ∅) (f : Finset α → R) (hsplit : ∀ D : Finset α, f D = f (D ∩ A) * f (D ∩ B)) :
    cumulantTransform f (A ∪ B) =
      ∑ π : Finpartition A, ∑ σ : Finpartition B, (π.blockProduct f * σ.blockProduct f) *
        (∑ m ∈ Finset.range (Nat.min π.parts.card σ.parts.card + 1),
          ((((π.parts.card.choose m) * (σ.parts.card.choose m) * m.factorial : ℕ) : R) *
            ((-1 : R) ^ (π.parts.card + σ.parts.card - m - 1) *
              ((π.parts.card + σ.parts.card - m - 1).factorial : R)))) := by
  rw [cumulantTransform_eq_sum_matchings_by_trace hAB hne f hsplit]
  exact Finset.sum_congr rfl (fun π _ => Finset.sum_congr rfl (fun σ _ => by
    rw [Matching.sum_coeff_by_size
      (π := π) (σ := σ)
      (c := fun m : ℕ =>
        ((-1 : R) ^ (π.parts.card + σ.parts.card - m - 1) *
          ((π.parts.card + σ.parts.card - m - 1).factorial : R)))]))

end TracePairMatching

end Finpartition

end
