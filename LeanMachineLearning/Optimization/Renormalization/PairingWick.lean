/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.PairingCardinality
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Aesop

/-!
# Weighted Wick sums as finite pairing algebra

These definitions, recursions, and relabelling identities are purely algebraic.
The Gaussian moment theorems using them are in `Gaussian.lean`.
-/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Renormalization

variable {ι : Type*} [DecidableEq ι]

/-- The canonical weight of an unordered two-element block for a covariance kernel.  Averaging the
two orientations avoids choosing an order on the index type. -/
def pairWeight (C : ι → ι → ℝ) (B : Finset ι) : ℝ :=
  (∑ i ∈ B, ∑ j ∈ B.erase i, C i j) / 2

/-- The Wick sum of a covariance kernel over all pairings of `s`. -/
def wick (C : ι → ι → ℝ) (s : Finset ι) : ℝ :=
  Finpartition.pairingSum (pairWeight C) s

/-- A Wick sum on an odd-cardinality set vanishes.

Informal proof: `Finpartition.Pairing.isEmpty_of_odd_card` says the indexing type of the sum is
empty, so the finite sum is zero. -/
theorem wick_eq_zero_of_odd_card (C : ι → ι → ℝ) (s : Finset ι) (hs : Odd s.card) :
    wick C s = 0 := by
  have h : IsEmpty (Finpartition.Pairing s) := Finpartition.Pairing.isEmpty_of_odd_card hs
  unfold wick Finpartition.pairingSum
  apply Fintype.sum_empty

/-- The canonical block weight of a two-element set is the covariance of its elements.

Informal proof:
By definition, `pairWeight C {a, b} = (∑ i ∈ {a, b}, ∑ j ∈ {a, b} \ {i}, C i j) / 2`.
When `a ≠ b`, the outer sum has two terms: `i = a` and `i = b`.
For `i = a`, the inner sum is over `{b}`, yielding `C a b`.
For `i = b`, the inner sum is over `{a}`, yielding `C b a`.
Summing these gives `(C a b + C b a) / 2`. Since `C` is symmetric (`hC`), this is `C a b`.
(Source: Covariance matrix, Wikipedia, https://en.wikipedia.org/wiki/Covariance_matrix) -/
theorem pairWeight_pair (C : ι → ι → ℝ) (hC : ∀ i j, C i j = C j i) {a b : ι} (hab : a ≠ b) :
    pairWeight C {a, b} = C a b := by
  unfold pairWeight
  rw [Finset.sum_pair hab]
  have h1 : ({a, b} : Finset ι).erase a = {b} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxa, h | h⟩; exacts [False.elim (hxa h), h]
    · rintro rfl; exact ⟨hab.symm, Or.inr rfl⟩
  have h2 : ({a, b} : Finset ι).erase b = {a} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxb, h | h⟩; exacts [h, False.elim (hxb h)]
    · rintro rfl; exact ⟨hab, Or.inl rfl⟩
  rw [h1, h2]
  rw [Finset.sum_singleton, Finset.sum_singleton]
  rw [hC b a]
  ring

/-- The blocks of a pairing of a `2m`-element set can be written as `m` labelled pairs of distinct
elements: for every symmetric kernel `C`, the product of `C` over the labelled pairs is the product
of the block weights `pairWeight C`. -/
theorem exists_labels_prod_pairWeight {s : Finset ι} {m : ℕ} (P : Finpartition.Pairing s)
    (hs : s.card = 2 * m) :
    ∃ u v : Fin m → ι, (∀ j, u j ≠ v j) ∧ ∀ C : ι → ι → ℝ, (∀ i j, C i j = C j i) →
      ∏ j : Fin m, C (u j) (v j) = P.blockProduct (pairWeight C) := by
  have hparts : P.val.parts.card = m := P.card_parts_of_card_eq hs
  let e : Fin m ≃ P.val.parts := Fintype.equivOfCardEq (by simp [hparts])
  choose u v huv hB using fun j : Fin m =>
    Finset.card_eq_two.mp (P.property (e j).val (e j).property)
  refine ⟨u, v, huv, fun C hC => ?_⟩
  calc
    _ = ∏ j : Fin m, pairWeight C (e j).val := by
      apply Finset.prod_congr rfl
      intro j _
      rw [hB, pairWeight_pair C hC (huv j)]
    _ = _ := P.prod_equiv_eq_blockProduct e (pairWeight C)

/-- Pairing recurrence obtained by choosing the partner of a distinguished element.

Informal proof:
For a non-empty set `s` containing a distinguished element `a`, any perfect matching (pairing)
of `s` must pair `a` with a unique partner `b ∈ s \ {a}`. Thus, the set of pairings of `s` is
partitioned by the choice of `b`. For a fixed `b`, the remaining pairings are exactly the pairings
of `s \ {a, b}`. Since the weight of a pairing is the product of covariances and the covariance
`C(a, b)` is symmetric (by `hC`), we can factor out `C a b` and sum over all choices of `b`.
This yields the recurrence relation.
This is the standard recursive proof of Isserlis' theorem.
(Source: Wick's Theorem, nLab) -/
theorem wick_erase (C : ι → ι → ℝ) (hC : ∀ i j, C i j = C j i)
    (s : Finset ι) {a : ι} (ha : a ∈ s) :
    wick C s = ∑ b ∈ s.erase a, C a b * wick C ((s.erase a).erase b) := by
  unfold wick
  rw [Finpartition.pairingSum_erase (pairWeight C) s ha]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mem_erase] at hb
  have h_pair := pairWeight_pair C hC hb.1.symm
  rw [h_pair]

/-- The Wick sum on the empty set is the empty product, hence one. -/
theorem wick_empty (C : ι → ι → ℝ) : wick C (∅ : Finset ι) = 1 := by
  let _ : Unique (Finpartition.Pairing (∅ : Finset ι)) :=
    { default := ⟨⊥, by simp⟩
      uniq := fun P ↦ by
        apply Subtype.ext
        ext a
        have hparts : P.1.parts = ∅ := (Finpartition.parts_eq_empty_iff).mpr (by simp)
        rw [hparts]
        simp }
  unfold wick Finpartition.pairingSum
  rw [Fintype.sum_unique]
  change (∏ B ∈ (∅ : Finset (Finset ι)), pairWeight C B) = 1
  simp

/-- The Wick sum on two distinct positions is their covariance. -/
theorem wick_pair (C : ι → ι → ℝ) (hC : ∀ i j, C i j = C j i)
    {a b : ι} (hab : a ≠ b) : wick C ({a, b} : Finset ι) = C a b := by
  rw [wick_erase C hC ({a, b} : Finset ι) (Finset.mem_insert_self a {b})]
  simp [hab, wick_empty]

/-- The fourth-order Wick sum is the sum of its three pairings. -/
theorem wick_four (C : ι → ι → ℝ) (hC : ∀ i j, C i j = C j i)
    {a b c d : ι} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    wick C ({a, b, c, d} : Finset ι) =
      C a b * C c d + C a c * C b d + C a d * C b c := by
  have hea : ({a, b, c, d} : Finset ι).erase a = {b, c, d} := by
    ext x
    simp [eq_comm, hab, hac, had]
  have heb : ({b, c, d} : Finset ι).erase b = {c, d} := by
    ext x
    simp [eq_comm, hbc, hbd]
  have hec : ({b, c, d} : Finset ι).erase c = {b, d} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hed : ({b, c, d} : Finset ι).erase d = {b, c} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  rw [wick_erase C hC ({a, b, c, d} : Finset ι) (Finset.mem_insert_self a _), hea,
    Finset.sum_insert (by simp [hbc, hbd]), Finset.sum_insert (by simp [hcd]),
    Finset.sum_singleton, heb, wick_pair C hC hcd, hec, wick_pair C hC hbd,
    hed, wick_pair C hC hbc]
  ring

/-! ### Transporting Wick sums along equivalences -/

/-- Mapping a finite partition along an equivalence preserves the property of being a pairing. -/
theorem mapEquiv_isPairing_iff {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) {s : Finset α} (P : Finpartition s) :
    (∀ B ∈ P.parts, B.card = 2) ↔
      (∀ B ∈ (Finpartition.mapEquiv e P).parts, B.card = 2) := by
  rw [Finpartition.parts_mapEquiv]
  constructor
  · intro hP B hB
    rcases Finset.mem_map.mp hB with ⟨C, hC, rfl⟩
    exact (Finset.card_map e.toEmbedding).trans (hP C hC)
  · intro hQ B hB
    simpa [Finset.card_map] using
      hQ (B.map e.toEmbedding) (Finset.mem_map.mpr ⟨B, hB, rfl⟩)

/-- Equivalence between pairings of a finite set and pairings of its image. -/
def pairingMapEquivEquiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (s : Finset α) :
    Finpartition.Pairing s ≃ Finpartition.Pairing (s.map e.toEmbedding) :=
  (Finpartition.mapEquivEquiv e s).subtypeEquiv (mapEquiv_isPairing_iff e)

/-- A pairing sum over an image is the pairing sum of the pulled-back block weight. -/
theorem pairingSum_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    {R : Type*} [CommSemiring R] (e : α ≃ β) (f : Finset β → R) (s : Finset α) :
    Finpartition.pairingSum f (s.map e.toEmbedding) =
      Finpartition.pairingSum (fun B : Finset α ↦ f (B.map e.toEmbedding)) s := by
  unfold Finpartition.pairingSum
  exact (((pairingMapEquivEquiv e s).sum_comp
    (fun Q : Finpartition.Pairing (s.map e.toEmbedding) ↦ Q.blockProduct f)).symm.trans
    (Finset.sum_congr rfl (fun P _hP ↦ Finpartition.blockProduct_mapEquiv e P.1 f)))

/-- The weight of a pair is natural under relabelling of its two positions. -/
theorem pairWeight_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (C : β → β → ℝ) (B : Finset α) :
    pairWeight C (B.map e.toEmbedding) =
      pairWeight (fun a b : α ↦ C (e a) (e b)) B := by
  unfold pairWeight
  congr 1
  rw [Finset.sum_map]
  exact Finset.sum_congr rfl (fun a _ha ↦ by
    rw [← Finset.map_erase e.toEmbedding B a, Finset.sum_map]
    simp [Equiv.toEmbedding_apply])

/-- Transport a Wick sum and its covariance kernel along an equivalence. -/
theorem wick_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (C : β → β → ℝ) (s : Finset α) :
    wick (fun a b : α ↦ C (e a) (e b)) s = wick C (s.map e.toEmbedding) := by
  unfold wick
  rw [pairingSum_map]
  unfold Finpartition.pairingSum
  apply Finset.sum_congr rfl
  intro P hP
  simp only [Finpartition.Pairing.blockProduct, Finpartition.blockProduct]
  apply Finset.prod_congr rfl
  intro B hB
  exact (pairWeight_map e C B).symm

/-- Wick sums over finite universal sets are invariant under an equivalence of positions. -/
theorem wick_univ_equiv {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (C : β → β → ℝ) :
    wick (fun a b : α ↦ C (e a) (e b)) (Finset.univ : Finset α) =
      wick C (Finset.univ : Finset β) := by
  rw [wick_map, Finset.map_univ_equiv]

end Renormalization
