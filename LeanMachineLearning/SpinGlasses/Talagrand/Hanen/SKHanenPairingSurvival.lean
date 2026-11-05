/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPathVanishing
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenSpinContraction
public import LeanMachineLearning.ForMathlib.Data.Fintype.DisjointTransversal
public import LeanMachineLearning.Optimization.Renormalization.PairingBlocks

/-!
# Exact support of the surviving critical cavity terms

At derivative order `m`, the `2m` endpoints must hit all `2m` disjoint spin-difference
pairs. There is then exactly one endpoint in each pair, no endpoint outside the pairs,
and no repeated endpoint. This is the support argument of Talagrand Eq. (1.339).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix
namespace SpinGlasses

/-- A nonzero critical endpoint term gives a bijection from spin-difference pairs to the
individual derivative endpoints. The endpoints are distinct, even if no such assumption
was imposed on the derivative pairs. -/
theorem skCavityPathMean_zero_critical_survival (N m n : ℕ) (β q h : ℝ)
    (pairMap : Fin (2 * m) → Fin n × Fin n)
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (p : Fin m → Fin n × Fin n)
    (F : (Fin n → Fin N → ℤˣ) → ℝ) (fhat : (Fin n → ℤˣ) → ℝ)
    (hfhat : ∀ (ε : Fin n → ℤˣ) (i : Fin n) (t : ℤˣ),
      i ∈ (univ : Finset (Fin (2 * m))).biUnion
        (fun v => {(pairMap v).1, (pairMap v).2}) →
      fhat (Function.update ε i t) = fhat ε) :
    let endpoint : Fin m × Bool → Fin n :=
      fun j => if j.2 then (p j.1).1 else (p j.1).2
    skCavityPathMean N n β q h 0 (fun σ => F (fun r i => σ r i.castSucc) *
      (∏ w : Fin (2 * m), ((σ (pairMap w).1 (Fin.last N) : ℝ) -
        (σ (pairMap w).2 (Fin.last N) : ℝ))) *
      (∏ j : Fin m, (σ (p j).1 (Fin.last N) : ℝ) * (σ (p j).2 (Fin.last N) : ℝ)) *
      fhat (fun r => σ r (Fin.last N))) ≠ 0 →
    ∃ e : Fin (2 * m) ≃ Fin m × Bool,
      (∀ v j, endpoint j ∈ ({(pairMap v).1, (pairMap v).2} : Finset (Fin n)) ↔ e v = j) ∧
      Function.Injective endpoint := by
  intro endpoint hnonzero
  let S : Fin (2 * m) → Set (Fin n) :=
    fun v => {(pairMap v).1, (pairMap v).2}
  have hd : Pairwise fun u v => Disjoint (S u) (S v) := by
    intro u v huv
    simpa only [S, Set.disjoint_insert_left, Set.disjoint_singleton_left,
      Set.mem_insert_iff, Set.mem_singleton_iff, not_or, and_assoc] using hdisj u v huv
  have hhit (v : Fin (2 * m)) : ∃ j, endpoint j ∈ S v := by
    by_contra hmiss
    have hp1 : (pairMap v).1 ∉ (∅ : Finset (Fin n)) ∪
        univ.biUnion (fun j : Fin m => {(p j).1, (p j).2}) := by
      intro hm
      rw [empty_union, mem_biUnion] at hm
      obtain ⟨j, _, hj⟩ := hm
      simp only [mem_insert, mem_singleton] at hj
      rcases hj with hj | hj
      · exact hmiss ⟨(j, true), by simp [endpoint, S, hj]⟩
      · exact hmiss ⟨(j, false), by simp [endpoint, S, hj]⟩
    have hp2 : (pairMap v).2 ∉ (∅ : Finset (Fin n)) ∪
        univ.biUnion (fun j : Fin m => {(p j).1, (p j).2}) := by
      intro hm
      rw [empty_union, mem_biUnion] at hm
      obtain ⟨j, _, hj⟩ := hm
      simp only [mem_insert, mem_singleton] at hj
      rcases hj with hj | hj
      · exact hmiss ⟨(j, true), by simp [endpoint, S, hj]⟩
      · exact hmiss ⟨(j, false), by simp [endpoint, S, hj]⟩
    have hz := skCavityPathMean_zero_vanishing_of_missing_pair N n β q h
      (univ : Finset (Fin (2 * m))) pairMap (fun u _ v _ huv => hdisj u v huv)
      ∅ p v (mem_univ _) ⟨hp1, hp2⟩ F fhat hfhat
    exact hnonzero (by simpa only [prod_empty, mul_one] using hz)
  simpa only [S, Set.mem_insert_iff, Set.mem_singleton_iff, mem_insert, mem_singleton] using
    exists_equiv_of_pairwiseDisjoint_of_hits S endpoint (by simp [mul_comm]) hd hhit

/-- A nonzero critical term recovers a unique generic pairing and derivative ordering.
Its blocks are characterized by incidence with the two endpoints of each derivative pair,
so the recovered data do not depend on a choice of survival witness. -/
theorem skCavityPathMean_zero_critical_pairing (N m n : ℕ) (β q h : ℝ)
    (pairMap : Fin (2 * m) → Fin n × Fin n)
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (p : Fin m → Fin n × Fin n)
    (F : (Fin n → Fin N → ℤˣ) → ℝ) (fhat : (Fin n → ℤˣ) → ℝ)
    (hfhat : ∀ (ε : Fin n → ℤˣ) (i : Fin n) (t : ℤˣ),
      i ∈ (univ : Finset (Fin (2 * m))).biUnion
        (fun v => {(pairMap v).1, (pairMap v).2}) →
      fhat (Function.update ε i t) = fhat ε) :
    skCavityPathMean N n β q h 0 (fun σ => F (fun r i => σ r i.castSucc) *
      (∏ w : Fin (2 * m), ((σ (pairMap w).1 (Fin.last N) : ℝ) -
        (σ (pairMap w).2 (Fin.last N) : ℝ))) *
      (∏ j : Fin m, (σ (p j).1 (Fin.last N) : ℝ) * (σ (p j).2 (Fin.last N) : ℝ)) *
      fhat (fun r => σ r (Fin.last N))) ≠ 0 →
    ∃! Pe : Σ P : Finpartition.Pairing (univ : Finset (Fin (2 * m))),
        Fin m ≃ P.val.parts, ∀ i v,
      v ∈ (Pe.2 i).val ↔
        (p i).1 ∈ ({(pairMap v).1, (pairMap v).2} : Finset (Fin n)) ∨
        (p i).2 ∈ ({(pairMap v).1, (pairMap v).2} : Finset (Fin n)) := by
  intro hn
  obtain ⟨e, he, _⟩ := skCavityPathMean_zero_critical_survival N m n β q h
    pairMap hdisj p F fhat hfhat hn
  obtain ⟨Pe, hPe, hu⟩ := Finpartition.existsUnique_pairing_ordering_of_equiv e
  have hi (i : Fin m) (v : Fin (2 * m)) : (e v).1 = i ↔
      (p i).1 ∈ ({(pairMap v).1, (pairMap v).2} : Finset (Fin n)) ∨
      (p i).2 ∈ ({(pairMap v).1, (pairMap v).2} : Finset (Fin n)) := by
    have ht : (p i).1 ∈ ({(pairMap v).1, (pairMap v).2} : Finset (Fin n)) ↔
        e v = (i, true) := he v (i, true)
    have hf : (p i).2 ∈ ({(pairMap v).1, (pairMap v).2} : Finset (Fin n)) ↔
        e v = (i, false) := he v (i, false)
    rw [ht, hf]
    constructor
    · intro hvi
      cases hb : (e v).2
      · exact Or.inr (Prod.ext hvi hb)
      · exact Or.inl (Prod.ext hvi hb)
    · rintro (hvi | hvi) <;> exact congrArg Prod.fst hvi
  refine ⟨Pe, (fun i v => (hPe i v).trans (hi i v)), ?_⟩
  intro Q hQ
  exact hu Q (fun i v => (hQ i v).trans (hi i v).symm)

/-- Evaluate an admissible surviving endpoint term, including the old-spin observable.
The old replicas continue to share one disorder. No fixed-point or temperature hypothesis
is needed for this exact identity at the decoupled endpoint. -/
theorem skCavityPathMean_zero_tuple_eval (N m n : ℕ) (β q h : ℝ)
    (pairMap : Fin (2 * m) → Fin n × Fin n)
    (hxy : ∀ v, (pairMap v).1 ≠ (pairMap v).2)
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (p : Fin m → Fin n × Fin n) (e : Fin (2 * m) ≃ Fin m × Bool)
    (b : Fin (2 * m) → Bool)
    (he : ∀ v, (if (e v).2 then (p (e v).1).1 else (p (e v).1).2) =
      if b v then (pairMap v).1 else (pairMap v).2)
    (F : (Fin n → Fin N → ℤˣ) → ℝ) (fhat : (Fin n → ℤˣ) → ℝ)
    (hfhat : ∀ (ε : Fin n → ℤˣ) (i : Fin n) (t : ℤˣ),
      i ∈ (univ : Finset (Fin (2 * m))).biUnion
        (fun v => {(pairMap v).1, (pairMap v).2}) →
      fhat (Function.update ε i t) = fhat ε) :
    skCavityPathMean N n β q h 0 (fun σ => F (fun r i => σ r i.castSucc) *
      (∏ w : Fin (2 * m), ((σ (pairMap w).1 (Fin.last N) : ℝ) -
        (σ (pairMap w).2 (Fin.last N) : ℝ))) *
      (∏ j : Fin m, (σ (p j).1 (Fin.last N) : ℝ) * (σ (p j).2 (Fin.last N) : ℝ)) *
      fhat (fun r => σ r (Fin.last N))) =
      (∏ v : Fin (2 * m), if b v then (1 : ℝ) else -1) *
      (∫ z : ℝ, (∫ ε : Fin n → ℤˣ, fhat ε
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
            fun s : ℤˣ => (s : ℝ) * (β * z * Real.sqrt q + h))) *
        ((Real.cosh (β * z * Real.sqrt q + h))⁻¹) ^ (4 * m) ∂gaussianReal 0 1) *
      (∫ g' : FinPairs N → ℝ, ∫ ρ : Fin n → Fin N → ℤˣ, F ρ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (skCavityOldEnergy N β h g'))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) := by
  let H : (Fin n → ℤˣ) → ℝ := fun ε =>
    (∏ w : Fin (2 * m), ((ε (pairMap w).1 : ℝ) - (ε (pairMap w).2 : ℝ))) *
      (∏ j : Fin m, (ε (p j).1 : ℝ) * (ε (p j).2 : ℝ)) * fhat ε
  have hfun : (fun σ : Fin n → Fin (N + 1) → ℤˣ => F (fun r i => σ r i.castSucc) *
      (∏ w : Fin (2 * m), ((σ (pairMap w).1 (Fin.last N) : ℝ) -
        (σ (pairMap w).2 (Fin.last N) : ℝ))) *
      (∏ j : Fin m, (σ (p j).1 (Fin.last N) : ℝ) * (σ (p j).2 (Fin.last N) : ℝ)) *
      fhat (fun r => σ r (Fin.last N))) =
      fun σ => F (fun r i => σ r i.castSucc) * H (fun r => σ r (Fin.last N)) := by
    funext σ
    dsimp only [H]
    ring
  rw [hfun, skCavityPathMean_zero_mul]
  dsimp only [H]
  have hsp (Y : ℝ) := integral_spin_diff_prod_endpoint Y m pairMap hxy hdisj p e b he
    fhat hfhat
  simp_rw [hsp]
  have hcomm (z : ℝ) :
      (∏ v : Fin (2 * m), if b v then (1 : ℝ) else -1) *
        ((Real.cosh (β * z * Real.sqrt q + h))⁻¹) ^ (4 * m) *
        (∫ ε : Fin n → ℤˣ, fhat ε ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
          fun s : ℤˣ => (s : ℝ) * (β * z * Real.sqrt q + h))) =
      (∏ v : Fin (2 * m), if b v then (1 : ℝ) else -1) *
        ((∫ ε : Fin n → ℤˣ, fhat ε ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
          fun s : ℤˣ => (s : ℝ) * (β * z * Real.sqrt q + h))) *
        ((Real.cosh (β * z * Real.sqrt q + h))⁻¹) ^ (4 * m)) := by ring
  simp_rw [hcomm, integral_const_mul]

end SpinGlasses
