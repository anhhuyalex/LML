/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenOldChoices
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPairingSurvival
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.RelationFibers

/-!
# Removing fresh replicas from the critical derivative sum

Critical survival forces every derivative endpoint into an original spin-difference pair.
The exact canonical weights are therefore one, and the recursive choice sum reduces to
the sum over ordered tuples of original replica pairs. The old-spin observable can depend
on the choice, as it does for products of truncated overlaps.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

/-- A nonzero critical term whose spin-difference pairs are original has only original
derivative endpoints. No assumptions on the old-spin observable or on the parameters are needed. -/
theorem skCavityPathMean_zero_choice_support (N m n : ℕ) (β q h : ℝ)
    (pairMap : Fin (2 * m) →
      Fin (skCavityIterReplicaCount m n) × Fin (skCavityIterReplicaCount m n))
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (hold : ∀ v, 2 * m ≤ (pairMap v).1.val ∧ 2 * m ≤ (pairMap v).2.val)
    (c : SKCavityDerivativeChoices m n)
    (F : (Fin (skCavityIterReplicaCount m n) → Fin N → ℤˣ) → ℝ)
    (fhat : (Fin (skCavityIterReplicaCount m n) → ℤˣ) → ℝ)
    (hfhat : ∀ ε i t,
      i ∈ (univ : Finset (Fin (2 * m))).biUnion
        (fun v => {(pairMap v).1, (pairMap v).2}) →
      fhat (Function.update ε i t) = fhat ε)
    (hnonzero : skCavityPathMean N (skCavityIterReplicaCount m n) β q h 0 (fun σ =>
      F (fun r i => σ r i.castSucc) *
        (∏ v : Fin (2 * m), ((σ (pairMap v).1 (Fin.last N) : ℝ) -
          (σ (pairMap v).2 (Fin.last N) : ℝ))) *
        (∏ r : Fin m,
          (σ (skCavityChoiceEndpoints m n c r).1 (Fin.last N) : ℝ) *
          (σ (skCavityChoiceEndpoints m n c r).2 (Fin.last N) : ℝ)) *
        fhat (fun r => σ r (Fin.last N))) ≠ 0) :
    ∀ r : Fin m,
      2 * m ≤ (skCavityChoiceEndpoints m n c r).1.val ∧
      2 * m ≤ (skCavityChoiceEndpoints m n c r).2.val := by
  obtain ⟨e, he, _⟩ := skCavityPathMean_zero_critical_survival N m
    (skCavityIterReplicaCount m n) β q h pairMap hdisj
    (skCavityChoiceEndpoints m n c) F fhat hfhat hnonzero
  have hpos (j : Fin m × Bool) :
      2 * m ≤ (if j.2 then (skCavityChoiceEndpoints m n c j.1).1
        else (skCavityChoiceEndpoints m n c j.1).2).val := by
    have hm := (he (e.symm j) j).2 (e.apply_symm_apply j)
    simp only [mem_insert, mem_singleton] at hm
    rcases hm with hm | hm
    · rw [hm]
      exact (hold _).1
    · rw [hm]
      exact (hold _).2
  exact fun r => ⟨hpos (r, true), hpos (r, false)⟩

/-- Exact removal of fresh-replica choices and their signed coefficients at the critical
order. Products of overlaps may be included in the choice-dependent old-spin observable. -/
theorem skCavityPathMean_zero_choice_sum (N m n : ℕ) (β q h : ℝ)
    (pairMap : Fin (2 * m) →
      Fin (skCavityIterReplicaCount m n) × Fin (skCavityIterReplicaCount m n))
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (hold : ∀ v, 2 * m ≤ (pairMap v).1.val ∧ 2 * m ≤ (pairMap v).2.val)
    (F : SKCavityDerivativeChoices m n →
      (Fin (skCavityIterReplicaCount m n) → Fin N → ℤˣ) → ℝ)
    (fhat : (Fin (skCavityIterReplicaCount m n) → ℤˣ) → ℝ)
    (hfhat : ∀ ε i t,
      i ∈ (univ : Finset (Fin (2 * m))).biUnion
        (fun v => {(pairMap v).1, (pairMap v).2}) →
      fhat (Function.update ε i t) = fhat ε) :
    let G := fun c => skCavityPathMean N (skCavityIterReplicaCount m n) β q h 0 (fun σ =>
      F c (fun r i => σ r i.castSucc) *
        (∏ v : Fin (2 * m), ((σ (pairMap v).1 (Fin.last N) : ℝ) -
          (σ (pairMap v).2 (Fin.last N) : ℝ))) *
        (∏ r : Fin m,
          (σ (skCavityChoiceEndpoints m n c r).1 (Fin.last N) : ℝ) *
          (σ (skCavityChoiceEndpoints m n c r).2 (Fin.last N) : ℝ)) *
        fhat (fun r => σ r (Fin.last N)))
    ∑ c, skCavityChoiceWeight m n c * G c =
      ∑ p : Fin m → FinPairs n, G (skCavityOldChoices m n p) := by
  intro G
  have hs (c) (hc : G c ≠ 0) :=
    skCavityPathMean_zero_choice_support N m n β q h pairMap hdisj hold c (F c) fhat hfhat hc
  calc
    _ = ∑ c, G c := by
      apply sum_congr rfl
      intro c _
      by_cases hc : G c = 0
      · simp only [hc, mul_zero]
      · rw [skCavityChoiceWeight_eq_one_of_old m n c (hs c hc), one_mul]
    _ = _ := sum_skCavityOldChoices m n G hs

/-- At the critical order, the derivative is a sum over ordered original-replica pairs.
Fresh replicas, their negative coefficients, and the growing replica count have all disappeared.
The remaining task for Theorem 1.11.9 is grouping these tuples into pairings of the differences. -/
theorem iteratedDerivWithin_skCavityPathMean_zero_old_pairs (N m n : ℕ) (β q h : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (pairMap : Fin (2 * m) → Fin n × Fin n)
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (F : (Fin n → Fin N → ℤˣ) → ℝ) (fhat : (Fin n → ℤˣ) → ℝ)
    (hfhat : ∀ ε i t,
      i ∈ (univ : Finset (Fin (2 * m))).biUnion
        (fun v => {(pairMap v).1, (pairMap v).2}) →
      fhat (Function.update ε i t) = fhat ε) :
    iteratedDerivWithin m (fun t => skCavityPathMean N n β q h t (fun σ =>
      F (fun r i => σ r i.castSucc) *
        (∏ v : Fin (2 * m), ((σ (pairMap v).1 (Fin.last N) : ℝ) -
          (σ (pairMap v).2 (Fin.last N) : ℝ))) *
        fhat (fun r => σ r (Fin.last N)))) (Set.Icc 0 1) 0 =
      (β ^ 2) ^ m * ∑ p : Fin m → FinPairs n, skCavityPathMean N n β q h 0 (fun σ =>
        F (fun r i => σ r i.castSucc) *
          (∏ v : Fin (2 * m), ((σ (pairMap v).1 (Fin.last N) : ℝ) -
            (σ (pairMap v).2 (Fin.last N) : ℝ))) *
          (∏ r : Fin m, (σ (p r).val.1 (Fin.last N) : ℝ) *
            (σ (p r).val.2 (Fin.last N) : ℝ)) * fhat (fun r => σ r (Fin.last N)) *
          ∏ r : Fin m, ((N + 1 : ℝ)⁻¹ *
            (∑ i : Fin N, (σ (p r).val.1 i.castSucc : ℝ) *
              (σ (p r).val.2 i.castSucc : ℝ)) - q)) := by
  let R := skCavityIterReplicaCount m n
  let ι := skCavityIterOldEmbedding m n
  let pm := fun v => (ι (pairMap v).1, ι (pairMap v).2)
  let Fc := fun c (ρ : Fin R → Fin N → ℤˣ) => F (fun r => ρ (ι r)) *
    ∏ r : Fin m, ((N + 1 : ℝ)⁻¹ *
      (∑ i : Fin N, (ρ (skCavityChoiceEndpoints m n c r).1 i : ℝ) *
        (ρ (skCavityChoiceEndpoints m n c r).2 i : ℝ)) - q)
  let G := fun c (σ : Fin R → Fin (N + 1) → ℤˣ) => Fc c (fun r i => σ r i.castSucc) *
    (∏ v : Fin (2 * m), ((σ (pm v).1 (Fin.last N) : ℝ) -
      (σ (pm v).2 (Fin.last N) : ℝ))) *
    (∏ r : Fin m, (σ (skCavityChoiceEndpoints m n c r).1 (Fin.last N) : ℝ) *
      (σ (skCavityChoiceEndpoints m n c r).2 (Fin.last N) : ℝ)) *
    fhat (fun r => σ (ι r) (Fin.last N))
  rw [iteratedDerivWithin_skCavityPathMean N m β q h hq n _ 0 ⟨le_rfl, zero_le_one⟩]
  have hkernel : skCavityIterKernel N β q m n (fun σ =>
      F (fun r i => σ r i.castSucc) *
        (∏ v : Fin (2 * m), ((σ (pairMap v).1 (Fin.last N) : ℝ) -
          (σ (pairMap v).2 (Fin.last N) : ℝ))) * fhat (fun r => σ r (Fin.last N))) =
      fun σ => ∑ c, ((β ^ 2) ^ m * skCavityChoiceWeight m n c) * G c σ := by
    funext σ
    rw [skCavityIterKernel_eq_choice_sum, mul_sum]
    apply sum_congr rfl
    intro c _
    simp only [G, Fc, pm, ι, skCavityPathKernel, dotProduct,
      prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
    ring
  rw [hkernel, skCavityPathMean_finset_sum]
  simp_rw [mul_assoc]
  rw [← mul_sum]
  congr 1
  have hd : ∀ u v, u ≠ v → (pm u).1 ≠ (pm v).1 ∧ (pm u).1 ≠ (pm v).2 ∧
      (pm u).2 ≠ (pm v).1 ∧ (pm u).2 ≠ (pm v).2 := by
    intro u v huv
    obtain ⟨h1, h2, h3, h4⟩ := hdisj u v huv
    exact ⟨ι.injective.ne h1, ι.injective.ne h2, ι.injective.ne h3, ι.injective.ne h4⟩
  have ho (v) : 2 * m ≤ (pm v).1.val ∧ 2 * m ≤ (pm v).2.val := by
    simp only [pm, ι, skCavityIterOldEmbedding_val]
    omega
  have hf : ∀ (ε : Fin R → ℤˣ) i t,
      i ∈ (univ : Finset (Fin (2 * m))).biUnion (fun v => {(pm v).1, (pm v).2}) →
      fhat (fun r => Function.update ε i t (ι r)) = fhat (fun r => ε (ι r)) := by
    intro ε i t hi
    simp only [mem_biUnion, mem_insert, mem_singleton] at hi
    obtain ⟨v, _, hi | hi⟩ := hi
    all_goals
      subst i
      change fhat ((Function.update ε (ι _) t) ∘ ι) = _
      rw [Function.update_comp_eq_of_injective ε ι.injective]
      apply hfhat
      exact mem_biUnion.mpr ⟨v, mem_univ _, by simp⟩
  rw [show (∑ c, skCavityChoiceWeight m n c *
      skCavityPathMean N R β q h 0 (G c)) = _ from
    skCavityPathMean_zero_choice_sum N m n β q h pm hd ho Fc
      (fun ε => fhat (fun r => ε (ι r))) hf]
  apply sum_congr rfl
  intro p _
  dsimp only [G, Fc, pm]
  simp only [skCavityChoiceEndpoints_old]
  let H : (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun τ =>
    F (fun r i => τ r i.castSucc) *
      (∏ v : Fin (2 * m), ((τ (pairMap v).1 (Fin.last N) : ℝ) -
        (τ (pairMap v).2 (Fin.last N) : ℝ))) *
      (∏ r : Fin m, (τ (p r).val.1 (Fin.last N) : ℝ) *
        (τ (p r).val.2 (Fin.last N) : ℝ)) * fhat (fun r => τ r (Fin.last N)) *
      ∏ r : Fin m, ((N + 1 : ℝ)⁻¹ *
        (∑ i : Fin N, (τ (p r).val.1 i.castSucc : ℝ) *
          (τ (p r).val.2 i.castSucc : ℝ)) - q)
  calc
    _ = skCavityPathMean N R β q h 0 (fun σ => H (fun r => σ (ι r))) := by
      congr 1
      funext σ
      dsimp only [H, ι]
      ring
    _ = _ := by
      simpa only [H, mul_assoc] using skCavityPathMean_comp_injective N β q h 0 ι.injective H

/-- Group the original-pair sum by its unique pairing and derivative ordering. Membership
in a group is an explicit incidence relation; zero terms require no arbitrary classification. -/
theorem skCavityPathMean_zero_old_pairs_sum_fibers (N m n : ℕ) (β q h : ℝ)
    (pairMap : Fin (2 * m) → Fin n × Fin n)
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (F : (Fin n → Fin N → ℤˣ) → ℝ) (fhat : (Fin n → ℤˣ) → ℝ)
    (hfhat : ∀ ε i t,
      i ∈ (univ : Finset (Fin (2 * m))).biUnion
        (fun v => {(pairMap v).1, (pairMap v).2}) →
      fhat (Function.update ε i t) = fhat ε) :
    let A := fun p : Fin m → FinPairs n => skCavityPathMean N n β q h 0 (fun σ =>
      F (fun r i => σ r i.castSucc) *
        (∏ v : Fin (2 * m), ((σ (pairMap v).1 (Fin.last N) : ℝ) -
          (σ (pairMap v).2 (Fin.last N) : ℝ))) *
        (∏ r : Fin m, (σ (p r).val.1 (Fin.last N) : ℝ) *
          (σ (p r).val.2 (Fin.last N) : ℝ)) * fhat (fun r => σ r (Fin.last N)) *
        ∏ r : Fin m, ((N + 1 : ℝ)⁻¹ *
          (∑ i : Fin N, (σ (p r).val.1 i.castSucc : ℝ) *
            (σ (p r).val.2 i.castSucc : ℝ)) - q))
    (∑ p, A p) =
      ∑ Pe : (Σ P : Finpartition.Pairing (univ : Finset (Fin (2 * m))),
          Fin m ≃ P.val.parts),
        ∑ p with (∀ i v, v ∈ (Pe.2 i).val ↔
          (p i).val.1 ∈ ({(pairMap v).1, (pairMap v).2} : Finset (Fin n)) ∨
          (p i).val.2 ∈ ({(pairMap v).1, (pairMap v).2} : Finset (Fin n))), A p := by
  intro A
  apply sum_eq_sum_filter_of_existsUnique
  intro p _ hp
  let Fp : (Fin n → Fin N → ℤˣ) → ℝ := fun ρ => F ρ *
    ∏ r : Fin m, ((N + 1 : ℝ)⁻¹ *
      (∑ i : Fin N, (ρ (p r).val.1 i : ℝ) * (ρ (p r).val.2 i : ℝ)) - q)
  have he : A p = skCavityPathMean N n β q h 0 (fun σ =>
      Fp (fun r i => σ r i.castSucc) *
        (∏ v : Fin (2 * m), ((σ (pairMap v).1 (Fin.last N) : ℝ) -
          (σ (pairMap v).2 (Fin.last N) : ℝ))) *
        (∏ r : Fin m, (σ (p r).val.1 (Fin.last N) : ℝ) *
          (σ (p r).val.2 (Fin.last N) : ℝ)) * fhat (fun r => σ r (Fin.last N))) := by
    dsimp only [A]
    congr 1
    funext σ
    dsimp only [Fp]
    ring
  rw [he] at hp
  simpa only [mem_univ, true_and] using skCavityPathMean_zero_critical_pairing N m n β q h
    pairMap hdisj (fun r => (p r).val) Fp fhat hfhat hp

end SpinGlasses
