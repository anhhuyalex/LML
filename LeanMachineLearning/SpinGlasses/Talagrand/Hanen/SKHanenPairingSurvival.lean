/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPathVanishing
public import LeanMachineLearning.ForMathlib.Data.Fintype.DisjointTransversal

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
    fun v => ↑({(pairMap v).1, (pairMap v).2} : Finset (Fin n))
  have hd : Pairwise fun u v => Disjoint (S u) (S v) := by
    intro u v huv
    rw [Set.disjoint_left]
    intro a ha hb
    simp only [S, mem_coe, mem_insert, mem_singleton] at ha hb
    obtain ⟨h1, h2, h3, h4⟩ := hdisj u v huv
    rcases ha with rfl | rfl <;> rcases hb with hb | hb
    · exact h1 hb
    · exact h2 hb
    · exact h3 hb
    · exact h4 hb
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
  exact exists_equiv_of_pairwiseDisjoint_of_hits S endpoint (by simp [mul_comm]) hd hhit

end SpinGlasses
