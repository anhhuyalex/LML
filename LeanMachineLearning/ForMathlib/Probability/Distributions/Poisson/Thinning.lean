/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Poisson thinning

This file isolates the algebraic law underlying finite Poisson thinning. Rather than introducing a
categorical-distribution wrapper, the main theorem states the probability mass calculation directly.
-/

@[expose] public section

open MeasureTheory Real
open scoped NNReal Nat

namespace ProbabilityTheory

private abbrev WordFiber {ι : Type*} [DecidableEq ι] (n : ℕ) (m : ι → ℕ) :=
  {x : Fin n → ι // ∀ i, (List.ofFn x).count i = m i}

private noncomputable def consWordEquiv {ι : Type*} [DecidableEq ι]
    (n : ℕ) (m : ι → ℕ) (a : ι) (ha : 0 < m a) :
    WordFiber n (Function.update m a (m a - 1)) ≃
      {x : WordFiber (n + 1) m // x.1 0 = a} := by
  refine Equiv.ofBijective (fun y => ⟨⟨Fin.cons a y.1, ?_⟩, by simp⟩) ?_
  · intro i
    rw [List.ofFn_cons, List.count_cons]
    by_cases hia : i = a
    · subst i
      simp only [beq_self_eq_true, ite_true]
      have h := congrArg (fun k => k + 1) (y.2 a)
      simp only [Function.update_self] at h
      omega
    · simpa [hia, Ne.symm hia] using y.2 i
  constructor
  · rintro ⟨y, hy⟩ ⟨z, hz⟩ heq
    apply Subtype.ext
    funext j
    have hfun := congrArg (fun q => q.1.1 (Fin.succ j)) heq
    simpa using hfun
  · rintro ⟨⟨x, hx⟩, hxa⟩
    let y : Fin n → ι := fun j => x (Fin.succ j)
    have hxy : Fin.cons a y = x := by
      funext j
      refine Fin.cases ?_ (fun k => ?_) j
      · simpa using hxa.symm
      · simp [y]
    have hy : ∀ i, (List.ofFn y).count i = Function.update m a (m a - 1) i := by
      intro i
      have hi := hx i
      rw [← hxy, List.ofFn_cons, List.count_cons] at hi
      by_cases hia : i = a
      · subst i
        simp only [Function.update_self]
        simp only [beq_self_eq_true, ite_true] at hi
        omega
      · simpa [hia, Ne.symm hia] using hi
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hxy

private noncomputable def wordFiberFirstEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (m : ι → ℕ) :
    WordFiber (n + 1) m ≃ Σ a : {a : ι // 0 < m a},
      WordFiber n (Function.update m a.1 (m a.1 - 1)) := by
  let e : WordFiber (n + 1) m ≃ Σ a : ι, {x : WordFiber (n + 1) m // x.1 0 = a} :=
    { toFun := fun x => ⟨x.1 0, x, rfl⟩
      invFun := fun x => x.2.1
      left_inv := by intro x; rfl
      right_inv := by rintro ⟨a, x, hx⟩; subst a; rfl }
  let ep : (Σ a : {a : ι // 0 < m a},
      {x : WordFiber (n + 1) m // x.1 0 = a.1}) ≃
      Σ a : {a : ι // 0 < m a},
        WordFiber n (Function.update m a.1 (m a.1 - 1)) :=
    Equiv.sigmaCongrRight fun a => (consWordEquiv n m a.1 a.2).symm
  let er : (Σ a : ι, {x : WordFiber (n + 1) m // x.1 0 = a}) ≃
      Σ a : {a : ι // 0 < m a}, {x : WordFiber (n + 1) m // x.1 0 = a.1} := by
    refine Equiv.ofBijective (fun z => ⟨⟨z.1, ?_⟩, z.2⟩) ?_
    · have hx := z.2.1.2 z.1
      have hzero : (List.ofFn z.2.1.1).count z.1 ≠ 0 := by
        exact Nat.ne_of_gt (List.count_pos_iff.mpr (List.mem_ofFn.mpr ⟨0, z.2.2⟩))
      omega
    constructor
    · intro x y h
      cases x with
      | mk a x =>
        cases y with
        | mk b y =>
          simp only [Sigma.mk.injEq] at h ⊢
          exact ⟨congrArg Subtype.val h.1, h.2⟩
    · rintro ⟨⟨a, ha⟩, x⟩
      exact ⟨⟨a, x⟩, rfl⟩
  exact e.trans (er.trans ep)

/-- If prescribed multiplicities have total zero, there is exactly one word with those
multiplicities. This is the base case for the finite categorical count law. -/
theorem multinomial_eq_card_words_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
    (hm : ∑ i, m i = 0) :
    Nat.multinomial Finset.univ m =
      Fintype.card {x : Fin 0 → ι // ∀ i, (List.ofFn x).count i = m i} := by
  have hm0 : m = 0 := by
    funext i
    apply Nat.eq_zero_of_le_zero
    have hi : m i ≤ ∑ j, m j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simpa [hm] using hi
  subst m
  rw [Nat.multinomial]
  simp

private theorem multinomial_decrement {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (a : ι) (ha : 0 < m a) :
    Nat.multinomial Finset.univ (Function.update m a (m a - 1)) * (∑ i, m i) =
      m a * Nat.multinomial Finset.univ m := by
  let ma := Function.update m a (m a - 1)
  have hsum : ∑ i, ma i + 1 = ∑ i, m i := by
    dsimp [ma]
    rw [Finset.sum_update_of_mem (Finset.mem_univ a),
      Finset.sdiff_singleton_eq_erase,
      ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    omega
  have hprod : (∏ i, (ma i).factorial) * m a = ∏ i, (m i).factorial := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ a)]
    dsimp [ma]
    simp only [Function.update_self]
    have hp : ∏ x ∈ Finset.univ.erase a,
        (Function.update m a (m a - 1) x).factorial =
          ∏ x ∈ Finset.univ.erase a, (m x).factorial := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [hp]
    rw [mul_assoc, mul_comm (m a - 1).factorial (m a),
      Nat.mul_factorial_pred (Nat.ne_of_gt ha)]
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ =>
    Nat.factorial_ne_zero (ma i)))
  calc
    (∏ i, (ma i).factorial) *
        (Nat.multinomial Finset.univ ma * ∑ i, m i) =
      ((∏ i, (ma i).factorial) * Nat.multinomial Finset.univ ma) * ∑ i, m i := by
        ac_rfl
    _ = (∑ i, ma i).factorial * ∑ i, m i := by rw [Nat.multinomial_spec]
    _ = (∑ i, ma i).factorial * (∑ i, ma i + 1) := by rw [hsum]
    _ = (∑ i, m i).factorial := by
      rw [mul_comm, ← Nat.factorial_succ, hsum]
    _ = (∏ i, (m i).factorial) * Nat.multinomial Finset.univ m := by
      rw [Nat.multinomial_spec]
    _ = ((∏ i, (ma i).factorial) * m a) * Nat.multinomial Finset.univ m := by
      rw [hprod]
    _ = (∏ i, (ma i).factorial) * (m a * Nat.multinomial Finset.univ m) := by
      ac_rfl

private theorem card_wordFiber {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (m : ι → ℕ) (hsum : ∑ i, m i = n) :
    Fintype.card (WordFiber n m) = Nat.multinomial Finset.univ m := by
  induction n using Nat.strong_induction_on generalizing m with
  | h n ih =>
    cases n with
    | zero =>
      simpa [WordFiber] using (multinomial_eq_card_words_zero m hsum).symm
    | succ n =>
      rw [Fintype.card_congr (wordFiberFirstEquiv n m), Fintype.card_sigma]
      apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos n)
      rw [Finset.sum_mul]
      have hma (a : {a : ι // 0 < m a}) :
          Fintype.card (WordFiber n (Function.update m a.1 (m a.1 - 1))) =
            Nat.multinomial Finset.univ (Function.update m a.1 (m a.1 - 1)) := by
        apply ih n (Nat.lt_succ_self n)
        rw [Finset.sum_update_of_mem (Finset.mem_univ a.1),
          Finset.sdiff_singleton_eq_erase]
        have ht := hsum
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a.1)] at ht
        omega
      simp_rw [hma]
      have hterm (a : {a : ι // 0 < m a}) :
          Nat.multinomial Finset.univ (Function.update m a.1 (m a.1 - 1)) * (n + 1) =
            m a.1 * Nat.multinomial Finset.univ m := by
        rw [← hsum]
        exact multinomial_decrement m a.1 a.2
      simp_rw [hterm]
      rw [Nat.mul_comm (Nat.multinomial Finset.univ m) (n + 1)]
      change ∑ x : {a : ι // 0 < m a}, m x.1 * Nat.multinomial Finset.univ m =
        (n + 1) * Nat.multinomial Finset.univ m
      rw [← hsum, Finset.sum_mul]
      change (∑ x : {a : ι // 0 < m a}, m x.1 * Nat.multinomial Finset.univ m) =
        ∑ a, m a * Nat.multinomial Finset.univ m
      have hsub :
          (∑ a : {a : ι // 0 < m a}, m a.1 * Nat.multinomial Finset.univ m) =
            ∑ a ∈ Finset.univ.filter (fun a => 0 < m a),
              m a * Nat.multinomial Finset.univ m := by
        classical
        rw [Finset.sum_subtype (s := Finset.univ.filter fun a => 0 < m a)
          (p := fun a => 0 < m a)
          (f := fun a => m a * Nat.multinomial Finset.univ m) (by simp)]
      rw [hsub]
      exact Finset.sum_filter_of_ne (s := Finset.univ) (p := fun a : ι => 0 < m a)
        (f := fun a => m a * Nat.multinomial Finset.univ m)
        (fun _ _ hne => Nat.pos_of_ne_zero (mul_ne_zero_iff.mp hne).1)

/-- The number of finite words with prescribed letter multiplicities is the corresponding
multinomial coefficient. -/
theorem multinomial_eq_card_words {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ) :
    Nat.multinomial Finset.univ m =
      Fintype.card {x : Fin (∑ i, m i) → ι // ∀ i, (List.ofFn x).count i = m i} := by
  symm
  exact card_wordFiber _ _ rfl

/-- The multinomial coefficient is the factorial quotient attached to prescribed category counts.
This formulation is useful when a finite categorical law is obtained by grouping words into count
fibers: it avoids unfolding `Nat.multinomial` at every probabilistic consumer. -/
theorem multinomial_eq_factorial_div {ι : Type*} [Fintype ι] (m : ι → ℕ) :
    Nat.multinomial Finset.univ m =
      (Finset.univ.sum m)! / Finset.univ.prod (fun i => (m i)!) := by
  rfl

/-- Multiplying the multinomial coefficient by the category factorials recovers the factorial of
the total count. This is the cancellation boundary used by multinomial counting arguments. -/
theorem prod_factorial_mul_multinomial {ι : Type*} [Fintype ι] (m : ι → ℕ) :
    Finset.univ.prod (fun i => (m i)!) * Nat.multinomial Finset.univ m =
      (Finset.univ.sum m)! := Nat.multinomial_spec Finset.univ m

/-- The Poisson-weighted multinomial mass factors into independent Poisson masses. This is the
algebraic core of finite Poisson thinning. -/
theorem poisson_mul_multinomial_eq_prod_poisson {ι : Type*} [Fintype ι]
    (r : ℝ≥0) (p : ι → ℝ≥0) (hp : ∑ i, p i = 1) (m : ι → ℕ) :
    Po(r) ({Finset.univ.sum m} : Set ℕ) *
        ENNReal.ofNNReal (Nat.multinomial Finset.univ m) *
        Finset.univ.prod (fun i => ENNReal.ofNNReal (p i) ^ m i) =
      Finset.univ.prod (fun i => Po(r * p i) ({m i} : Set ℕ)) := by
  classical
  simp only [poissonMeasure_singleton]
  push_cast
  rw [← ENNReal.ofReal_natCast]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity)]
  rw [show Finset.univ.prod (fun i => ENNReal.ofNNReal (p i) ^ m i) =
    ENNReal.ofReal (Finset.univ.prod fun i => (p i : ℝ) ^ m i) by
      rw [ENNReal.ofReal_prod_of_nonneg]
      · apply Finset.prod_congr rfl
        intro i hi
        rw [ENNReal.ofReal_pow (NNReal.zero_le_coe)]
        simp
      · intro i hi
        positivity]
  rw [← ENNReal.ofReal_mul (by positivity)]
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).2
  have hp' : ∑ i, (p i : ℝ) = 1 := by exact_mod_cast hp
  rw [Finset.prod_div_distrib]
  rw [Finset.prod_mul_distrib]
  rw [← Real.exp_sum]
  rw [show (∑ x, -(↑r * (p x : ℝ))) = -(↑r * ∑ x, (p x : ℝ)) by
    rw [Finset.mul_sum, Finset.sum_neg_distrib]]
  rw [hp', mul_one]
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib]
  rw [← Finset.prod_pow_eq_pow_sum]
  rw [← Nat.cast_prod]
  have hmult : ((∏ i, (m i)!) : ℝ) * Nat.multinomial Finset.univ m =
      (Finset.univ.sum m)! := by
    exact_mod_cast prod_factorial_mul_multinomial m
  rw [← hmult]
  have hmn : (Nat.multinomial Finset.univ m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ m))
  field_simp [hmn]
  push_cast
  ring

end ProbabilityTheory
