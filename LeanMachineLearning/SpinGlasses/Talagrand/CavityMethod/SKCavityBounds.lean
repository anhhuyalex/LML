/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityDerivative
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.OffDiag

/-!
# Uniform covariance bounds for the cavity replica derivative

These bounds are independent of the old-pair disorder. They make the conditional
Gaussian derivative eligible for dominated differentiation over that disorder.
-/

@[expose] public section

open MeasureTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- Each normalized truncated Ising overlap is bounded by one, including when `N = 0`. -/
theorem abs_sk_cavity_overlap_le_one (N : ℕ)
    (a b : Fin (N + 1) → ℤˣ) :
    |(N + 1 : ℝ)⁻¹ *
      ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ
        fun i : Fin N => (b i.castSucc : ℝ))| ≤ 1 := by
  have hs : ∀ i : Fin N, |(a i.castSucc : ℝ) * (b i.castSucc : ℝ)| = 1 := by
    intro i
    rw [abs_mul]
    have ha : |(a i.castSucc : ℝ)| = 1 := abs_units_cast_eq_one (a i.castSucc)
    have hb : |(b i.castSucc : ℝ)| = 1 := abs_units_cast_eq_one (b i.castSucc)
    rw [ha, hb, one_mul]
  have hn : (0 : ℝ) ≤ (N + 1 : ℝ)⁻¹ := by positivity
  calc
    _ = (N + 1 : ℝ)⁻¹ *
        |∑ i : Fin N, (a i.castSucc : ℝ) * (b i.castSucc : ℝ)| := by
          rw [dotProduct, abs_mul, abs_of_nonneg hn]
    _ ≤ (N + 1 : ℝ)⁻¹ *
        ∑ i : Fin N, |(a i.castSucc : ℝ) * (b i.castSucc : ℝ)| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hn
    _ = (N : ℝ) / (N + 1 : ℝ) := by
          simp only [hs, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
          ring
    _ ≤ 1 := by
          have hp : (N : ℝ) ≤ (N + 1 : ℝ) := by exact_mod_cast Nat.le_succ N
          exact (div_le_one (by positivity)).2 hp

/-- The covariance kernel appearing in the cavity derivative has a uniform
bound when the scalar variance parameter belongs to `[0,1]`. -/
theorem abs_sk_cavity_covariance_le (N : ℕ) (β q : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (a b : Fin (N + 1) → ℤˣ) :
    |β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
      (q - (N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (b i.castSucc : ℝ)))| ≤ 2 * β ^ 2 := by
  have ha : |(a (Fin.last N) : ℝ)| = 1 := abs_units_cast_eq_one (a (Fin.last N))
  have hb : |(b (Fin.last N) : ℝ)| = 1 := abs_units_cast_eq_one (b (Fin.last N))
  have hqabs : |q| ≤ 1 := by simpa [abs_of_nonneg hq.1] using hq.2
  have hdiff : |q - (N + 1 : ℝ)⁻¹ *
      ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ
        fun i : Fin N => (b i.castSucc : ℝ))| ≤ 2 := by
    calc
      _ ≤ |q| + |(N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (b i.castSucc : ℝ))| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add hqabs (abs_sk_cavity_overlap_le_one N a b)
      _ = 2 := by ring
  rw [abs_mul, abs_mul, abs_mul, abs_pow, ha, hb, mul_one, mul_one]
  simpa only [abs_abs, sq_abs] using
    (mul_le_mul_of_nonneg_left hdiff (sq_nonneg β)).trans_eq (mul_comm _ _)

/-- Uniform bound on the complete four-term replica covariance combination.
This is the domination needed after conditioning on the old-pair disorder;
it works for any finite replica type and any uniformly bounded kernel. -/
theorem abs_replica_covariance_combination_le {R α : Type*} [Fintype R]
    (U : α → α → ℝ) (C : ℝ)
    (hU : ∀ a b, |U a b| ≤ C) (τ : Option (Option R) → α) :
    |(∑ r : R, ∑ r' : R, U (τ (some (some r))) (τ (some (some r')))) -
        2 * (Fintype.card R : ℝ) *
          (∑ r : R, U (τ (some (some r))) (τ (some none))) -
        (Fintype.card R : ℝ) * U (τ (some none)) (τ (some none)) +
        (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
          U (τ (some none)) (τ none)| ≤
      2 * (Fintype.card R : ℝ) * (2 * (Fintype.card R : ℝ) + 1) * C := by
  let n : ℝ := Fintype.card R
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hsum : ∀ r : R,
      |∑ r' : R, U (τ (some (some r))) (τ (some (some r')))| ≤ n * C := by
    intro r
    calc
      _ ≤ ∑ r' : R, |U (τ (some (some r))) (τ (some (some r')))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r' : R, C := Finset.sum_le_sum fun r' _ => hU _ _
      _ = n * C := by simp [n]
  have hdouble :
      |∑ r : R, ∑ r' : R, U (τ (some (some r))) (τ (some (some r')))| ≤
        n * (n * C) := by
    calc
      _ ≤ ∑ r : R, |∑ r' : R, U (τ (some (some r))) (τ (some (some r')))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : R, n * C := Finset.sum_le_sum fun r _ => hsum r
      _ = n * (n * C) := by simp [n]
  have hsingle : |∑ r : R, U (τ (some (some r))) (τ (some none))| ≤ n * C := by
    calc
      _ ≤ ∑ r : R, |U (τ (some (some r))) (τ (some none))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _r : R, C := Finset.sum_le_sum fun r _ => hU _ _
      _ = n * C := by simp [n]
  calc
    _ ≤ |∑ r : R, ∑ r' : R, U (τ (some (some r))) (τ (some (some r')))| +
        |2 * n * ∑ r : R, U (τ (some (some r))) (τ (some none))| +
        |n * U (τ (some none)) (τ (some none))| +
        |n * (n + 1) * U (τ (some none)) (τ none)| := by
          have h1 := abs_add_le
            ((∑ r : R, ∑ r' : R,
                U (τ (some (some r))) (τ (some (some r')))) -
              2 * n * ∑ r : R, U (τ (some (some r))) (τ (some none)) -
              n * U (τ (some none)) (τ (some none)))
            (n * (n + 1) * U (τ (some none)) (τ none))
          have h2 := abs_sub
            ((∑ r : R, ∑ r' : R,
                U (τ (some (some r))) (τ (some (some r')))) -
              2 * n * ∑ r : R, U (τ (some (some r))) (τ (some none)))
            (n * U (τ (some none)) (τ (some none)))
          have h3 := abs_sub
            (∑ r : R, ∑ r' : R, U (τ (some (some r))) (τ (some (some r'))))
            (2 * n * ∑ r : R, U (τ (some (some r))) (τ (some none)))
          dsimp [n] at h1 h2 h3 ⊢
          linarith
    _ ≤ n * (n * C) + (2 * n) * (n * C) + n * C + (n * (n + 1)) * C := by
          simp only [abs_mul, abs_of_nonneg hn,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * n),
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ n + 1)]
          gcongr
          · exact hU _ _
          · exact hU _ _
    _ = _ := by dsimp [n]; ring

/-- The diagonal terms of the replica covariance combination cancel whenever the
covariance has a constant diagonal. This is the algebraic step from the general
Gaussian replica derivative to its cavity form; it does not assume symmetry of `U`. -/
theorem replica_covariance_combination_cancel_diagonal
    {R α : Type*} [Fintype R] [DecidableEq R] (U : α → α → ℝ) (C : ℝ)
    (hdiag : ∀ a, U a a = C) (τ : Option (Option R) → α) :
    (∑ r : R, ∑ r' : R, U (τ (some (some r))) (τ (some (some r')))) -
        2 * (Fintype.card R : ℝ) *
          (∑ r : R, U (τ (some (some r))) (τ (some none))) -
        (Fintype.card R : ℝ) * U (τ (some none)) (τ (some none)) +
        (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
          U (τ (some none)) (τ none) =
      (∑ r : R, ∑ r' : R, if r = r' then 0 else
          U (τ (some (some r))) (τ (some (some r')))) -
        2 * (Fintype.card R : ℝ) *
          (∑ r : R, U (τ (some (some r))) (τ (some none))) +
        (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
          U (τ (some none)) (τ none) := by
  have hs (r : R) :
      (∑ r' : R, U (τ (some (some r))) (τ (some (some r')))) =
        C + ∑ r' : R, if r = r' then 0 else
          U (τ (some (some r))) (τ (some (some r'))) := by
    have hh (r' : R) : U (τ (some (some r))) (τ (some (some r'))) =
        (if r = r' then C else 0) +
          (if r = r' then 0 else U (τ (some (some r))) (τ (some (some r')))) := by
      split_ifs with hr
      · subst r'; simp [hdiag]
      · simp
    rw [Finset.sum_congr rfl fun r' _ => hh r', Finset.sum_add_distrib]
    simp
  simp_rw [hs, Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [hdiag (τ (some none))]
  ring

/-- For a symmetric covariance kernel, the surviving ordered off-diagonal
terms are twice the strictly ordered replica pairs. This combines diagonal
cancellation with the generic finite-sum reindexing, while remaining
independent of the cavity model. -/
theorem replica_covariance_combination_eq_two_sum_lt
    {R α : Type*} [Fintype R] [LinearOrder R] (U : α → α → ℝ) (C : ℝ)
    (hdiag : ∀ a, U a a = C) (hsym : ∀ a b, U a b = U b a)
    (τ : Option (Option R) → α) :
    (∑ r : R, ∑ r' : R, U (τ (some (some r))) (τ (some (some r')))) -
        2 * (Fintype.card R : ℝ) *
          (∑ r : R, U (τ (some (some r))) (τ (some none))) -
        (Fintype.card R : ℝ) * U (τ (some none)) (τ (some none)) +
        (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
          U (τ (some none)) (τ none) =
      2 * ∑ p : R × R with p.1 < p.2,
          U (τ (some (some p.1))) (τ (some (some p.2))) -
        2 * (Fintype.card R : ℝ) *
          (∑ r : R, U (τ (some (some r))) (τ (some none))) +
        (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
          U (τ (some none)) (τ none) := by
  rw [replica_covariance_combination_cancel_diagonal U C hdiag τ,
    sum_sum_offDiag_eq_two_sum_lt
      (fun r r' => U (τ (some (some r))) (τ (some (some r'))))
      (fun r r' => hsym _ _)]

/-- The square-parameter chain rule multiplies the clean angle bracket by
`-1 / 2`. This algebraic form reverses the covariance kernel and gives the
three coefficients used by Talagrand's cavity derivative. -/
theorem neg_half_replica_covariance_offDiag
    {R α : Type*} [Fintype R] [LinearOrder R] (U : α → α → ℝ)
    (τ : Option (Option R) → α) :
    -(2 * ∑ p : R × R with p.1 < p.2,
        U (τ (some (some p.1))) (τ (some (some p.2))) -
      2 * (Fintype.card R : ℝ) * ∑ r : R,
        U (τ (some (some r))) (τ (some none)) +
      (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
        U (τ (some none)) (τ none)) / 2 =
    (∑ p : R × R with p.1 < p.2,
        -U (τ (some (some p.1))) (τ (some (some p.2)))) -
      (Fintype.card R : ℝ) * ∑ r : R,
        -U (τ (some (some r))) (τ (some none)) +
      (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) / 2 *
        (-U (τ (some none)) (τ none)) := by
  simp only [Finset.sum_neg_distrib]
  ring

/-- The number of strictly ordered pairs of replicas is `n.choose 2`. -/
theorem card_filter_lt_fin_prod (n : ℕ) :
    ((Finset.univ : Finset (Fin n × Fin n)).filter fun p => p.1 < p.2).card = n.choose 2 := by
  rw [← card_finPairs n, Fintype.card_subtype]

/-- The book's three families of replica pairs (`ℓ < ℓ' ≤ n`, `ℓ ≤ n` against `n + 1`, and
`n + 1` against `n + 2`), weighted `1`, `-n`, `n (n + 1) / 2`, carry in total
`n (n - 1) / 2 + n² + n (n + 1) / 2 = 2 n²` terms. Hence a uniform bound `c` on the kernel
bounds the combination by `2 n² c`. -/
theorem abs_book_replica_combination_le {α : Type*} (n : ℕ) (K : α → α → ℝ) (c : ℝ)
    (hK : ∀ a b, |K a b| ≤ c) (τ : Option (Option (Fin n)) → α) :
    |(∑ p : Fin n × Fin n with p.1 < p.2, K (τ (some (some p.1))) (τ (some (some p.2)))) -
        (n : ℝ) * ∑ r : Fin n, K (τ (some (some r))) (τ (some none)) +
        (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none)| ≤ 2 * (n : ℝ) ^ 2 * c := by
  have hc : 0 ≤ c := (abs_nonneg _).trans (hK (τ none) (τ none))
  have h1 : |∑ p : Fin n × Fin n with p.1 < p.2, K (τ (some (some p.1))) (τ (some (some p.2)))| ≤
      (n : ℝ) * ((n : ℝ) - 1) / 2 * c := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ c fun p _ => hK _ _).trans ?_
    rw [card_filter_lt_fin_prod, nsmul_eq_mul, Nat.cast_choose_two]
  have h2 : |∑ r : Fin n, K (τ (some (some r))) (τ (some none))| ≤ n * c := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ c fun r _ => hK _ _).trans ?_
    simp
  have h3 := hK (τ (some none)) (τ none)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc _ ≤ |∑ p : Fin n × Fin n with p.1 < p.2, K (τ (some (some p.1))) (τ (some (some p.2)))| +
        (n : ℝ) * |∑ r : Fin n, K (τ (some (some r))) (τ (some none))| +
        (n : ℝ) * ((n : ℝ) + 1) / 2 * |K (τ (some none)) (τ none)| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans ?_) ?_)
        · rw [abs_mul, abs_of_nonneg hn]
        · rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 * c + (n : ℝ) * (n * c) +
        (n : ℝ) * ((n : ℝ) + 1) / 2 * c := by
        gcongr
    _ = 2 * (n : ℝ) ^ 2 * c := by ring

/-- The book's combination of the three replica families is unchanged when the kernel is shifted
by a constant, because the weights `C(n,2)`, `-n²` and `C(n+1,2)` add up to zero. -/
theorem book_replica_combination_add_const {α : Type*} (n : ℕ) (K : α → α → ℝ) (κ : ℝ)
    (τ : Option (Option (Fin n)) → α) :
    (∑ p : Fin n × Fin n with p.1 < p.2,
        (K (τ (some (some p.1))) (τ (some (some p.2))) + κ)) -
      (n : ℝ) * ∑ r : Fin n, (K (τ (some (some r))) (τ (some none)) + κ) +
      (n : ℝ) * ((n : ℝ) + 1) / 2 * (K (τ (some none)) (τ none) + κ) =
    (∑ p : Fin n × Fin n with p.1 < p.2, K (τ (some (some p.1))) (τ (some (some p.2)))) -
      (n : ℝ) * ∑ r : Fin n, K (τ (some (some r))) (τ (some none)) +
      (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none) := by
  simp only [Finset.sum_add_distrib, Finset.sum_const, card_filter_lt_fin_prod, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_choose_two]
  ring

/-- **Absolute value of the angle combination.** If a kernel `U` is minus a kernel `Kf` plus a
constant, the angle form `2 ∑_{ℓ<ℓ'} U - 2n ∑_ℓ U + n (n + 1) U` of the replica combination is
bounded by twice the same combination of `|Kf|`. -/
theorem abs_two_sum_lt_combination_le {α : Type*} (n : ℕ) (U Kf : α → α → ℝ) (κ : ℝ)
    (hU : ∀ a b, U a b = -Kf a b + κ) (τ : Option (Option (Fin n)) → α) :
    |2 * (∑ p : Fin n × Fin n with p.1 < p.2, U (τ (some (some p.1))) (τ (some (some p.2)))) -
        2 * (n : ℝ) * ∑ r : Fin n, U (τ (some (some r))) (τ (some none)) +
        (n : ℝ) * ((n : ℝ) + 1) * U (τ (some none)) (τ none)| ≤
      2 * ((∑ p : Fin n × Fin n with p.1 < p.2,
            |Kf (τ (some (some p.1))) (τ (some (some p.2)))|) +
        (n : ℝ) * ∑ r : Fin n, |Kf (τ (some (some r))) (τ (some none))| +
        (n : ℝ) * ((n : ℝ) + 1) / 2 * |Kf (τ (some none)) (τ none)|) := by
  have hshift := book_replica_combination_add_const n (fun a b => -Kf a b) κ τ
  have heq : 2 * (∑ p : Fin n × Fin n with p.1 < p.2,
          U (τ (some (some p.1))) (τ (some (some p.2)))) -
        2 * (n : ℝ) * ∑ r : Fin n, U (τ (some (some r))) (τ (some none)) +
        (n : ℝ) * ((n : ℝ) + 1) * U (τ (some none)) (τ none) =
      2 * ((∑ p : Fin n × Fin n with p.1 < p.2, -Kf (τ (some (some p.1))) (τ (some (some p.2)))) -
        (n : ℝ) * ∑ r : Fin n, -Kf (τ (some (some r))) (τ (some none)) +
        (n : ℝ) * ((n : ℝ) + 1) / 2 * -Kf (τ (some none)) (τ none)) := by
    rw [← hshift]
    simp only [hU]
    ring
  rw [heq, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2)]
  refine mul_le_mul_of_nonneg_left ?_ two_pos.le
  simp only [Finset.sum_neg_distrib, mul_neg]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc _ ≤ |-(∑ p : Fin n × Fin n with p.1 < p.2, Kf (τ (some (some p.1))) (τ (some (some p.2))))| +
        |(n : ℝ) * ∑ r : Fin n, Kf (τ (some (some r))) (τ (some none))| +
        |(n : ℝ) * ((n : ℝ) + 1) / 2 * Kf (τ (some none)) (τ none)| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans ?_) ?_)
        · simp only [abs_neg, abs_mul, abs_of_nonneg hn]
          exact le_rfl
        · rw [abs_neg]
    _ ≤ _ := by
        have hc : |(n : ℝ) * ((n : ℝ) + 1) / 2| = (n : ℝ) * ((n : ℝ) + 1) / 2 :=
          abs_of_nonneg (by positivity)
        rw [abs_neg, abs_mul, abs_of_nonneg hn, abs_mul, hc]
        exact add_le_add (add_le_add (Finset.abs_sum_le_sum_abs _ _)
          (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hn)) le_rfl

/-- The cavity covariance has a constant diagonal, including at `N = 0`.
This is the exact hypothesis for `replica_covariance_combination_cancel_diagonal`. -/
theorem sk_cavity_covariance_diagonal (N : ℕ) (β q : ℝ)
    (a : Fin (N + 1) → ℤˣ) :
    β ^ 2 * (a (Fin.last N) : ℝ) * (a (Fin.last N) : ℝ) *
      (q - (N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (a i.castSucc : ℝ))) =
    β ^ 2 * (q - (N : ℝ) / (N + 1 : ℝ)) := by
  rw [sk_cavity_self_overlap]
  have hs : (a (Fin.last N) : ℝ) ^ 2 = 1 := units_cast_sq _
  calc
    _ = β ^ 2 * (a (Fin.last N) : ℝ) ^ 2 *
        (q - (N : ℝ) / (N + 1 : ℝ)) := by ring
    _ = _ := by rw [hs, mul_one]

/-- The cavity covariance is symmetric in its two spin configurations. -/
theorem sk_cavity_covariance_symmetric (N : ℕ) (β q : ℝ)
    (a b : Fin (N + 1) → ℤˣ) :
    β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
      (q - (N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (b i.castSucc : ℝ))) =
    β ^ 2 * (b (Fin.last N) : ℝ) * (a (Fin.last N) : ℝ) *
      (q - (N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (b i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (a i.castSucc : ℝ))) := by
  rw [dotProduct_comm]
  ring

/-- Reversing the cavity covariance puts the overlap in Talagrand's
`R⁻ - q` convention. -/
theorem neg_sk_cavity_covariance (N : ℕ) (β q : ℝ)
    (a b : Fin (N + 1) → ℤˣ) :
    -(β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
      (q - (N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (b i.castSucc : ℝ)))) =
    β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
      ((N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (b i.castSucc : ℝ)) - q) := by
  ring

/-- The cavity kernel `β² ε ε' (R⁻ - q)` in the book's orientation is uniformly bounded. -/
theorem abs_sk_cavity_kernel_le (N : ℕ) (β q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (a b : Fin (N + 1) → ℤˣ) :
    |β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ
        fun i : Fin N => (b i.castSucc : ℝ)) - q)| ≤ 2 * β ^ 2 := by
  have h := abs_sk_cavity_covariance_le N β q hq a b
  rwa [← abs_neg, neg_sk_cavity_covariance] at h

/-- The kernel with the full overlap `R` differs from the one with the truncated overlap `R⁻` by
the constant `β² / (N + 1)`, since `ε² = 1`. -/
theorem sk_cavity_kernel_full_eq (N : ℕ) (β q : ℝ) (a b : Fin (N + 1) → ℤˣ) :
    β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (a i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (b i : ℝ)) - q) =
    β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ
        fun i : Fin N => (b i.castSucc : ℝ)) - q) + β ^ 2 / (N + 1 : ℝ) := by
  rw [sk_overlap_succ_eq_cavity]
  have ha : (a (Fin.last N) : ℝ) ^ 2 = 1 := units_cast_sq _
  have hb : (b (Fin.last N) : ℝ) ^ 2 = 1 := units_cast_sq _
  have : β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
      ((N + 1 : ℝ)⁻¹ * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ)) =
      β ^ 2 / (N + 1 : ℝ) := by
    field_simp
    rw [ha, hb]; ring
  linear_combination this

/-- The absolute value of the full-overlap kernel is `β²` times the overlap deviation, since the
last spins have absolute value one. -/
theorem abs_sk_cavity_kernel_full (N : ℕ) (β q : ℝ) (a b : Fin (N + 1) → ℤˣ) :
    |β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (a i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (b i : ℝ)) - q)| =
    β ^ 2 * |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (a i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (b i : ℝ)) - q| := by
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg β), abs_units_cast_eq_one,
    abs_units_cast_eq_one]
  ring

end SpinGlasses
