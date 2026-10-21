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
  classical
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
    calc
      _ = ∑ r' : R, ((if r = r' then C else 0) +
          (if r = r' then 0 else U (τ (some (some r))) (τ (some (some r'))))) :=
        Finset.sum_congr rfl (fun r' _ => hh r')
      _ = _ := by simp [Finset.sum_add_distrib]
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
      2 * ∑ p ∈ (Finset.univ : Finset R).offDiag with p.1 < p.2,
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
    -(2 * ∑ p ∈ (Finset.univ : Finset R).offDiag with p.1 < p.2,
        U (τ (some (some p.1))) (τ (some (some p.2))) -
      2 * (Fintype.card R : ℝ) * ∑ r : R,
        U (τ (some (some r))) (τ (some none)) +
      (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
        U (τ (some none)) (τ none)) / 2 =
    (∑ p ∈ (Finset.univ : Finset R).offDiag with p.1 < p.2,
        -U (τ (some (some p.1))) (τ (some (some p.2)))) -
      (Fintype.card R : ℝ) * ∑ r : R,
        -U (τ (some (some r))) (τ (some none)) +
      (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) / 2 *
        (-U (τ (some none)) (τ none)) := by
  simp only [Finset.sum_neg_distrib]
  ring

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
  have hs : (a (Fin.last N) : ℝ) ^ 2 = 1 := by
    simpa using units_cast_sq (a (Fin.last N))
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

end SpinGlasses
