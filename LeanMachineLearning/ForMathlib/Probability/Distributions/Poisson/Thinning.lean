/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.MeasureTheory.Constructions.Pi
public import LeanMachineLearning.ForMathlib.Probability.Distributions.Poisson.SumCountable
public import LeanMachineLearning.ForMathlib.Probability.ExchangeableMixture
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Poisson thinning

This file isolates the algebraic law underlying finite Poisson thinning. Rather than introducing a
categorical-distribution wrapper, the main theorem states the probability mass calculation directly.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal Nat ENNReal

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

private noncomputable def wordFiberFirstEquiv {ι : Type*} [DecidableEq ι]
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
      rw [← Finset.sum_mul, Nat.mul_comm (Nat.multinomial Finset.univ m) (n + 1)]
      congr 1
      rw [← hsum, ← Finset.sum_filter_of_ne (s := Finset.univ) (p := fun a : ι => 0 < m a)
        (fun _ _ h => Nat.pos_of_ne_zero h)]
      exact (Finset.sum_subtype (p := fun a => 0 < m a) _ (by simp) m).symm

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

/-- The count of a letter in `List.ofFn x` is the number of positions carrying it. -/
theorem count_ofFn_eq_sum {ι : Type*} [DecidableEq ι] (n : ℕ) (x : Fin n → ι) (i : ι) :
    (List.ofFn x).count i = ∑ j, if x j = i then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih (fun j => x j.succ)]
    simp [add_comm]

/-- **Fixed-horizon multinomial law.** Under an i.i.d. product measure with singleton masses
`p i`, the set of words of length `∑ m i` with letter multiplicities `m` has mass
`multinomial m * ∏ (p i)^(m i)`. -/
theorem measure_pi_counts_eq {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (ν : Measure ι) [IsProbabilityMeasure ν] (p : ι → ℝ≥0)
    (hν : ∀ i, ν {i} = ENNReal.ofNNReal (p i)) (m : ι → ℕ) :
    Measure.pi (fun _ : Fin (∑ i, m i) => ν)
        {x | ∀ i, (∑ j, if x j = i then 1 else 0) = m i} =
      ENNReal.ofNNReal (Nat.multinomial Finset.univ m) *
        ∏ i, ENNReal.ofNNReal (p i) ^ m i := by
  have hset : {x : Fin (∑ i, m i) → ι | ∀ i, (∑ j, if x j = i then 1 else 0) = m i} =
      ↑(Finset.univ.filter fun x : Fin (∑ i, m i) → ι =>
        ∀ i, (∑ j, if x j = i then 1 else 0) = m i) := by
    ext x; simp
  rw [hset, measure_finset_eq_sum_singleton]
  have hterm : ∀ x ∈ Finset.univ.filter
      (fun x : Fin (∑ i, m i) → ι => ∀ i, (∑ j, if x j = i then 1 else 0) = m i),
      Measure.pi (fun _ : Fin (∑ i, m i) => ν) {x} = ∏ i, ENNReal.ofNNReal (p i) ^ m i := by
    intro x hx
    have hx' := (Finset.mem_filter.1 hx).2
    rw [Measure.pi_singleton]
    simp only [hν]
    rw [← Finset.prod_fiberwise' Finset.univ x (fun i => ENNReal.ofNNReal (p i))]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_const, ← hx' i, Finset.card_filter]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [multinomial_eq_card_words m, Fintype.card_subtype]
  simp_rw [count_ofFn_eq_sum]

/-- The category counts of the first `N` letters of a sequence depend measurably on `(N, x)`. -/
theorem measurable_categoryCounts {ι : Type*} [Countable ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] :
    Measurable fun q : ℕ × (ℕ → ι) => fun i : ι =>
      ∑ l ∈ Finset.range q.1, if q.2 l = i then 1 else 0 := by
  refine measurable_from_prod_countable_right fun n => ?_
  refine measurable_pi_iff.2 fun i => ?_
  change Measurable fun x : ℕ → ι => ∑ l ∈ Finset.range n, if x l = i then 1 else 0
  refine Finset.measurable_sum _ fun l _ => ?_
  exact Measurable.ite (measurableSet_eq_fun (measurable_pi_apply l) measurable_const)
    measurable_const measurable_const

/-- **Thinning in canonical form.** If `N ~ Po(r)` is independent of an i.i.d. sequence with
finite law `ν`, the category counts of the first `N` letters have law `⊗ i, Po(r * p i)`. -/
theorem map_counts_prod_infinitePi {ι : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (ν : Measure ι) [IsProbabilityMeasure ν] (r : ℝ≥0)
    (p : ι → ℝ≥0) (hp : ∑ i, p i = 1) (hν : ∀ i, ν {i} = ENNReal.ofNNReal (p i)) :
    (Po(r).prod (Measure.infinitePi fun _ : ℕ => ν)).map
        (fun q : ℕ × (ℕ → ι) => fun i : ι =>
          ∑ l ∈ Finset.range q.1, if q.2 l = i then 1 else 0) =
      Measure.pi fun i => Po(r * p i) := by
  refine Measure.ext_of_singleton fun m => ?_
  rw [Measure.map_apply measurable_categoryCounts (measurableSet_singleton m), Measure.prod_apply
    (measurable_categoryCounts (measurableSet_singleton m)), Measure.pi_singleton,
    ← poisson_mul_multinomial_eq_prod_poisson r p hp m]
  rw [lintegral_countable', tsum_eq_single (∑ i, m i)]
  · have hsec : (Prod.mk (∑ i, m i) ⁻¹' ((fun q : ℕ × (ℕ → ι) => fun i : ι =>
        ∑ l ∈ Finset.range q.1, if q.2 l = i then 1 else 0) ⁻¹' {m})) =
        (fun σ : ℕ → ι => fun j : Fin (∑ i, m i) => σ j) ⁻¹'
          {x | ∀ i, (∑ j, if x j = i then 1 else 0) = m i} := by
      ext σ
      simp only [Set.mem_preimage, Set.mem_singleton_iff, funext_iff]
      refine forall_congr' fun i => ?_
      rw [← Fin.sum_univ_eq_sum_range (fun l => if σ l = i then 1 else 0)]
    rw [hsec, ← Measure.map_apply (by fun_prop) (Set.toFinite _).measurableSet,
      (Measure.measurePreserving_restrict_infinitePi ν (f := fun j : Fin (∑ i, m i) => (j : ℕ))
        Fin.val_injective).map_eq, measure_pi_counts_eq ν p hν m]
    ring
  · intro n hn
    have hempty : Prod.mk n ⁻¹' ((fun q : ℕ × (ℕ → ι) => fun i : ι =>
        ∑ l ∈ Finset.range q.1, if q.2 l = i then 1 else 0) ⁻¹' {m}) = ∅ := by
      ext σ
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      apply hn
      have : ∑ i, ∑ l ∈ Finset.range n, (if σ l = i then 1 else 0) = n := by
        rw [Finset.sum_comm]; simp
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => congrFun h i
    rw [hempty, measure_empty, zero_mul]


/-- **Multinomial Poisson thinning.** Let `N ~ Po(r)` be independent of an i.i.d. sequence
`X l` with finite law `ν`, `ν {i} = p i`. Then the category counts
`N_i = ∑_{l < N} 1_{X l = i}` have joint law `⊗ i, Po(r * p i)`; in particular they are mutually
independent Poisson variables. -/
theorem hasLaw_counts_poisson_thinning {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (ν : Measure ι) [IsProbabilityMeasure ν] (r : ℝ≥0)
    (p : ι → ℝ≥0) (hp : ∑ i, p i = 1) (hν : ∀ i, ν {i} = ENNReal.ofNNReal (p i))
    {N : Ω → ℕ} {X : ℕ → Ω → ι} (hN : HasLaw N Po(r) P) (hX : ∀ l, HasLaw (X l) ν P)
    (hXi : iIndepFun X P) (hNX : IndepFun N (fun ω l => X l ω) P) :
    HasLaw (fun ω i => ∑ l ∈ Finset.range (N ω), if X l ω = i then 1 else 0)
      (Measure.pi fun i => Po(r * p i)) P := by
  have hXm : AEMeasurable (fun ω l => X l ω) P :=
    aemeasurable_pi_iff.2 fun l => (hX l).aemeasurable
  have hseq : P.map (fun ω l => X l ω) = Measure.infinitePi fun _ : ℕ => ν := by
    rw [hXi.map_fun_eq_infinitePi_map₀' fun l => (hX l).aemeasurable]
    congr 1; funext l; exact (hX l).map_eq
  have hpair : HasLaw (fun ω => (N ω, fun l => X l ω))
      (Po(r).prod (Measure.infinitePi fun _ : ℕ => ν)) P :=
    hNX.hasLaw_prod hN ⟨hXm, hseq⟩
  refine ⟨?_, ?_⟩
  · exact measurable_categoryCounts.comp_aemeasurable hpair.aemeasurable
  · rw [← map_counts_prod_infinitePi ν r p hp hν, ← hpair.map_eq,
      AEMeasurable.map_map_of_aemeasurable measurable_categoryCounts.aemeasurable
        hpair.aemeasurable]
    rfl

/-- **Poisson thinning, coordinatewise form.** The category counts of the first `N` letters are
mutually independent, and the `i`-th one is `Po(r * p i)`. -/
theorem iIndepFun_hasLaw_counts_poisson_thinning {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (ν : Measure ι) [IsProbabilityMeasure ν] (r : ℝ≥0)
    (p : ι → ℝ≥0) (hp : ∑ i, p i = 1) (hν : ∀ i, ν {i} = ENNReal.ofNNReal (p i))
    {N : Ω → ℕ} {X : ℕ → Ω → ι} (hN : HasLaw N Po(r) P) (hX : ∀ l, HasLaw (X l) ν P)
    (hXi : iIndepFun X P) (hNX : IndepFun N (fun ω l => X l ω) P) :
    (∀ i, HasLaw (fun ω => ∑ l ∈ Finset.range (N ω), if X l ω = i then 1 else 0)
        Po(r * p i) P) ∧
      iIndepFun (fun (i : ι) ω => ∑ l ∈ Finset.range (N ω), if X l ω = i then 1 else 0) P := by
  have h := hasLaw_counts_poisson_thinning ν r p hp hν hN hX hXi hNX
  have hi : ∀ i, HasLaw (fun ω => ∑ l ∈ Finset.range (N ω), if X l ω = i then 1 else 0)
      Po(r * p i) P := fun i =>
    (measurePreserving_eval (fun i => Po(r * p i)) i).hasLaw.comp h
  exact ⟨hi, (iIndepFun_iff_hasLaw_pi_pi hi).2 h⟩

/-- Applying a measurable map to every sample of a block `Po(r) ⊗ ν^{⊗ℕ}` gives a block with
sample law `ν.map f`. -/
theorem hasLaw_map_prod_infinitePi {Ω S T : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [MeasurableSpace S] [MeasurableSpace T] {r : ℝ≥0} {ν : Measure S} [IsProbabilityMeasure ν]
    {B : Ω → ℕ × (ℕ → S)} (hB : HasLaw B (Po(r).prod (Measure.infinitePi fun _ : ℕ => ν)) P)
    {f : S → T} (hf : Measurable f) :
    HasLaw (fun ω => ((B ω).1, fun l => f ((B ω).2 l)))
      (Po(r).prod (Measure.infinitePi fun _ : ℕ => ν.map f)) P := by
  have hm : Measurable (fun b : ℕ × (ℕ → S) => (b.1, fun l => f (b.2 l))) := by fun_prop
  have hmap : (Po(r).prod (Measure.infinitePi fun _ : ℕ => ν)).map
      (fun b : ℕ × (ℕ → S) => (b.1, fun l => f (b.2 l))) =
      Po(r).prod (Measure.infinitePi fun _ : ℕ => ν.map f) := by
    rw [show (fun b : ℕ × (ℕ → S) => (b.1, fun l => f (b.2 l))) =
      Prod.map id (fun x => fun l => f (x l)) from rfl,
      ← Measure.map_prod_map _ _ measurable_id (by fun_prop :
        Measurable fun x : ℕ → S => fun l => f (x l))]
    simp only [Measure.map_id]
    exact congrArg (Measure.prod (Po(r)))
      (Measure.infinitePi_map_pi (μ := fun _ : ℕ => ν) (fun _ => hf))
  exact ⟨hm.aemeasurable.comp_aemeasurable hB.aemeasurable, by
    rw [← hmap, ← hB.map_eq,
      AEMeasurable.map_map_of_aemeasurable hm.aemeasurable hB.aemeasurable]
    rfl⟩

/-- **Thinning of a canonical Poisson block, with a category map.** If a random block
`B = (N, X)` has law `Po(r) ⊗ ν^{⊗ℕ}`, and `c` sorts the sample space into finitely many categories
with `ν (c ⁻¹' {i}) = p i`, then the category counts of the first `N` points have law
`⊗ i, Po(r * p i)`. -/
theorem hasLaw_counts_poisson_thinning_of_hasLaw_prod {Ω S ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [MeasurableSpace S] [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (ν : Measure S) [IsProbabilityMeasure ν] (r : ℝ≥0) {c : S → ι}
    (hc : Measurable c) (p : ι → ℝ≥0) (hp : ∑ i, p i = 1)
    (hν : ∀ i, ν (c ⁻¹' {i}) = ENNReal.ofNNReal (p i)) {B : Ω → ℕ × (ℕ → S)}
    (hB : HasLaw B (Po(r).prod (Measure.infinitePi fun _ : ℕ => ν)) P) :
    HasLaw (fun ω i => ∑ l ∈ Finset.range (B ω).1, if c ((B ω).2 l) = i then 1 else 0)
      (Measure.pi fun i => Po(r * p i)) P := by
  have : IsProbabilityMeasure (ν.map c) := ⟨by simp [Measure.map_apply hc MeasurableSet.univ]⟩
  have hν' : ∀ i, ν.map c {i} = ENNReal.ofNNReal (p i) := fun i => by
    rw [Measure.map_apply hc (measurableSet_singleton i), hν]
  have hT : Measurable fun q : ℕ × (ℕ → S) => (q.1, fun l => c (q.2 l)) := by fun_prop
  have hcount := hasLaw_map_prod_infinitePi hB hc
  refine ⟨?_, ?_⟩
  · exact (measurable_categoryCounts.comp hT).comp_aemeasurable hB.aemeasurable
  · rw [← map_counts_prod_infinitePi (ν.map c) r p hp hν', ← hcount.map_eq,
      AEMeasurable.map_map_of_aemeasurable measurable_categoryCounts.aemeasurable
        hcount.aemeasurable]
    rfl

end ProbabilityTheory
