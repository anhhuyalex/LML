/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Data.Nat.Choose.Cast

public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.AddPowEstimates
public import LeanMachineLearning.ForMathlib.Data.Nat.Recurrence
public import LeanMachineLearning.ForMathlib.Probability.Moments.IidSumMoments
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Elementary estimates for the moment expansion of an i.i.d. sum

Analytic ingredients of the proof that the `k`-th moment of a centered i.i.d. sum is the Gaussian
one up to a relative error `n^{-1/2}` (the second order Taylor remainder of `u ↦ u^p`,
`pow_succ_sub_pow_sub_mul_le`, is in `AddPowEstimates`):

* `Nat.eq_zero_of_odd_of_two_step_mul`: a sequence `a` with `a 1 = 0` and
  `a (k + 2) = (k + 1) a k` (the Gaussian moments) vanishes at odd indices;
* `ProbabilityTheory.abs_le_of_abs_sub_le_sqrt_pow`: if `e 0 = 0` and the increments of `e` are at
  most `c (√(n + 1))^p`, then `|e n| ≤ c (√(n + 1))^{p+2}`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, after Eq. (1.122).
-/

@[expose] public section

open MeasureTheory Finset

namespace ProbabilityTheory

/-- `1 ≤ √(n + 1)`. -/
theorem one_le_sqrt_natCast_add_one (n : ℕ) : 1 ≤ Real.sqrt ((n : ℝ) + 1) :=
  Real.one_le_sqrt.2 (by linarith [Nat.cast_nonneg (α := ℝ) n])

/-- **Summation of increments of order `√(n+1)^p`:** if `e 0 = 0` and
`|e (n + 1) - e n| ≤ c (√(n + 1))^p` for all `n`, then `|e n| ≤ c (√(n + 1))^{p+2}`. -/
theorem abs_le_of_abs_sub_le_sqrt_pow {e : ℕ → ℝ} (he0 : e 0 = 0) {c : ℝ} (hc : 0 ≤ c) {p : ℕ}
    (h : ∀ n : ℕ, |e (n + 1) - e n| ≤ c * Real.sqrt ((n : ℝ) + 1) ^ p) (n : ℕ) :
    |e n| ≤ c * Real.sqrt ((n : ℝ) + 1) ^ (p + 2) := by
  have key : |e n| ≤ (n : ℝ) * (c * Real.sqrt ((n : ℝ) + 1) ^ p) := by
    have hstep : ∀ {k : ℕ}, k < n → dist (e k) (e (k + 1)) ≤
        c * Real.sqrt ((n : ℝ) + 1) ^ p := fun {k} hk => by
      have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk.le
      have hb : |e (k + 1) - e k| ≤ c * Real.sqrt ((n : ℝ) + 1) ^ p :=
        (h k).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (by linarith)) p) hc)
      simpa only [Real.dist_eq, abs_sub_comm] using hb
    simpa only [he0, dist_zero_left, Real.norm_eq_abs, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul] using
      dist_le_range_sum_of_dist_le
        (d := fun _ => c * Real.sqrt ((n : ℝ) + 1) ^ p) n hstep
  refine key.trans ?_
  have hs : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by positivity)
  rw [pow_add, hs]
  have : (n : ℝ) * (c * Real.sqrt ((n : ℝ) + 1) ^ p) ≤ ((n : ℝ) + 1) *
      (c * Real.sqrt ((n : ℝ) + 1) ^ p) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  nlinarith

private theorem abs_gaussian_moment_increment_sub_le
    {a : ℕ → ℝ} (ha1 : a 1 = 0) (ha : ∀ k, a (k + 2) = (k + 1) * a k)
    {σ2 : ℝ} (hσ : 0 ≤ σ2) {k : ℕ} (hk : 3 ≤ k) (n : ℕ) :
    |(k.choose 2 : ℝ) * σ2 * (a (k - 2) * σ2 ^ ((k - 2) / 2) * (n : ℝ) ^ ((k - 2) / 2)) -
      (a k * σ2 ^ (k / 2) * (((n + 1 : ℕ) : ℝ)) ^ (k / 2) -
        a k * σ2 ^ (k / 2) * (n : ℝ) ^ (k / 2))|
        ≤ ((k : ℝ) * (k - 1) * |a k| * σ2 ^ (k / 2)) *
          Real.sqrt ((n : ℝ) + 1) ^ (k - 3) := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · obtain ⟨p, rfl⟩ : ∃ p, m = p + 2 := ⟨m - 2, by omega⟩
    have e1 : 2 * (p + 2) - 2 = 2 * p + 2 := by omega
    have e2 : 2 * (p + 2) / 2 = p + 2 := by omega
    have e3 : (2 * p + 2) / 2 = p + 1 := by omega
    have e4 : 2 * (p + 2) - 3 = 2 * p + 1 := by omega
    have hch : ((2 * (p + 2)).choose 2 : ℝ) = (p + 2 : ℝ) * (2 * (p : ℝ) + 3) := by
      rw [Nat.cast_choose_two]
      push_cast
      ring
    have hak : a (2 * (p + 2)) = (2 * (p : ℝ) + 3) * a (2 * p + 2) := by
      rw [show 2 * (p + 2) = (2 * p + 2) + 2 by ring, ha]
      push_cast
      ring
    rw [e1, e2, e3, e4, hch, hak]
    obtain ⟨hg0, hg1⟩ := pow_succ_sub_pow_sub_mul_le (Nat.cast_nonneg (α := ℝ) n) p
    set g := ((n : ℝ) + 1) ^ (p + 2) - (n : ℝ) ^ (p + 2) - (p + 2 : ℝ) * (n : ℝ) ^ (p + 1)
      with hg_def
    have hΘ : (p + 2 : ℝ) * (2 * (p : ℝ) + 3) * σ2 * (a (2 * p + 2) * σ2 ^ (p + 1) *
        (n : ℝ) ^ (p + 1)) - ((2 * (p : ℝ) + 3) * a (2 * p + 2) * σ2 ^ (p + 2) *
          (((n + 1 : ℕ) : ℝ)) ^ (p + 2) - (2 * (p : ℝ) + 3) * a (2 * p + 2) * σ2 ^ (p + 2) *
            (n : ℝ) ^ (p + 2)) = -((2 * (p : ℝ) + 3) * a (2 * p + 2) * σ2 ^ (p + 2) * g) := by
      rw [hg_def]
      push_cast
      ring
    rw [hΘ, abs_neg, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ σ2 ^ (p + 2)),
      abs_of_nonneg hg0]
    have hs : Real.sqrt ((n : ℝ) + 1) ^ (2 * p + 1) ≥ ((n : ℝ) + 1) ^ p := by
      have h1 : Real.sqrt ((n : ℝ) + 1) ^ (2 * p) = ((n : ℝ) + 1) ^ p := by
        rw [pow_mul, Real.sq_sqrt (by positivity)]
      have h2 := one_le_sqrt_natCast_add_one n
      calc ((n : ℝ) + 1) ^ p = Real.sqrt ((n : ℝ) + 1) ^ (2 * p) := h1.symm
        _ ≤ Real.sqrt ((n : ℝ) + 1) ^ (2 * p) * Real.sqrt ((n : ℝ) + 1) :=
            le_mul_of_one_le_right (by positivity) h2
        _ = _ := by ring
    calc |(2 * (p : ℝ) + 3) * a (2 * p + 2)| * σ2 ^ (p + 2) * g
        ≤ |(2 * (p : ℝ) + 3) * a (2 * p + 2)| * σ2 ^ (p + 2) *
            ((p + 2 : ℝ) * (p + 1 : ℝ) * ((n : ℝ) + 1) ^ p) :=
          mul_le_mul_of_nonneg_left hg1 (by positivity)
      _ ≤ |(2 * (p : ℝ) + 3) * a (2 * p + 2)| * σ2 ^ (p + 2) * ((p + 2 : ℝ) * (p + 1 : ℝ)) *
            Real.sqrt ((n : ℝ) + 1) ^ (2 * p + 1) := by
          have := mul_le_mul_of_nonneg_left hs
            (by positivity : 0 ≤ |(2 * (p : ℝ) + 3) * a (2 * p + 2)| * σ2 ^ (p + 2) *
              ((p + 2 : ℝ) * (p + 1 : ℝ)))
          nlinarith [this]
      _ ≤ _ := by
          have hcoeff : (p + 2 : ℝ) * (p + 1 : ℝ) ≤
              ((2 * (p + 2) : ℕ) : ℝ) * (((2 * (p + 2) : ℕ) : ℝ) - 1) := by
            push_cast; nlinarith
          calc _ = (((p + 2 : ℝ) * (p + 1 : ℝ)) *
              (|(2 * (p : ℝ) + 3) * a (2 * p + 2)| * σ2 ^ (p + 2))) *
                Real.sqrt ((n : ℝ) + 1) ^ (2 * p + 1) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hcoeff (by positivity)) (by positivity)
  · have h1 : a (2 * m + 1) = 0 := Nat.eq_zero_of_odd_of_two_step_mul ha1 ha ⟨m, rfl⟩
    have h2 : a (2 * m + 1 - 2) = 0 := Nat.eq_zero_of_odd_of_two_step_mul ha1 ha ⟨m - 1, by omega⟩
    simp [h1, h2]

/-- **The leading terms cancel in the increment of the Gaussian reference.**  For a sequence `a`
with `a 1 = 0` and `a (k + 2) = (k + 1) a k` and `σ2 ≥ 0`, the quantity
`Θ = C(k, 2) σ2 · ref_{k-2}(n) - (ref_k(n + 1) - ref_k(n))`, where
`ref_j(n) = a j σ2^{j/2} n^{j/2}`, satisfies `|Θ| ≤ c (√(n + 1))^{k-3}` for some `c ≥ 0` and all
`n`, for each `k ≥ 3`.  (For odd `k` it vanishes; for even `k` the leading terms cancel because
`C(2m, 2) a_{2m-2} = m a_{2m}` and the remainder is the Taylor remainder of `n ↦ n^m`.) -/
theorem exists_abs_cancellation_le {a : ℕ → ℝ} (ha1 : a 1 = 0) (ha : ∀ k, a (k + 2) = (k + 1) * a k)
    {σ2 : ℝ} (hσ : 0 ≤ σ2) {k : ℕ} (hk : 3 ≤ k) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ n : ℕ,
      |(k.choose 2 : ℝ) * σ2 * (a (k - 2) * σ2 ^ ((k - 2) / 2) * (n : ℝ) ^ ((k - 2) / 2)) -
        (a k * σ2 ^ (k / 2) * (((n + 1 : ℕ) : ℝ)) ^ (k / 2) -
          a k * σ2 ^ (k / 2) * (n : ℝ) ^ (k / 2))|
        ≤ c * Real.sqrt ((n : ℝ) + 1) ^ (k - 3) := by
  have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr (by omega)
  exact ⟨(k : ℝ) * (k - 1) * |a k| * σ2 ^ (k / 2),
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) (sub_nonneg.mpr hk1))
      (abs_nonneg _)) (pow_nonneg hσ _),
    abs_gaussian_moment_increment_sub_le ha1 ha hσ hk⟩

/-- `n^{⌊j/2⌋} ≤ (√(n + 1))^j`. -/
theorem natCast_pow_div_two_le_sqrt_pow (n j : ℕ) :
    (n : ℝ) ^ (j / 2) ≤ Real.sqrt ((n : ℝ) + 1) ^ j := by
  have hs1 := one_le_sqrt_natCast_add_one n
  calc (n : ℝ) ^ (j / 2) ≤ ((n : ℝ) + 1) ^ (j / 2) :=
        pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) _
    _ = Real.sqrt ((n : ℝ) + 1) ^ (2 * (j / 2)) := by
        rw [pow_mul, Real.sq_sqrt (by positivity)]
    _ ≤ Real.sqrt ((n : ℝ) + 1) ^ j := pow_le_pow_right₀ hs1 (Nat.mul_div_le j 2)

/-- **Uniform moment bound for a centered i.i.d. sum under moment bounds `B`:** for any sequence
`B : ℕ → ℝ` (`B j ≥ 0`) and exponent `k : ℕ`, there exists `C ≥ 0` depending only on `B` and `k`
such that for every probability space `(Ω, ν)`, every centered `g : Ω → ℝ` with all powers
integrable and `|∫ g^j dν| ≤ B j`, and every `n : ℕ`,
`|𝔼 (∑_{i < n} g(y_i))^k| ≤ C (√(n + 1))^k`. -/
theorem exists_abs_integral_pow_sum_pi_le (B : ℕ → ℝ) (hB0 : ∀ j, 0 ≤ B j) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] {g : Ω → ℝ},
        (∀ j, Integrable (fun x => g x ^ j) ν) →
        ∫ x, g x ∂ν = 0 →
        (∀ j, |∫ x, g x ^ j ∂ν| ≤ B j) →
        ∀ n : ℕ,
          |∫ y : Fin n → Ω, (∑ i, g (y i)) ^ k ∂(Measure.pi fun _ : Fin n => ν)| ≤
            C * Real.sqrt ((n : ℝ) + 1) ^ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | _ | k'
    · refine ⟨1, zero_le_one, fun ν _ _ _ _ n => ?_⟩
      simp
    · refine ⟨0, le_rfl, fun {Ω} _ ν _ {g} hint h0 _ n => ?_⟩
      have hM1 : ∀ m : ℕ, ∫ y : Fin m → Ω, (∑ i, g (y i)) ^ 1 ∂(Measure.pi fun _ => ν) = 0 := by
        intro m
        induction m with
        | zero => simp
        | succ m ihm =>
          rw [integral_pow_sum_pi_succ hint m 1]
          simp only [pow_one] at ihm
          simp [Finset.sum_range_succ, h0, ihm]
      rw [hM1 n]; simp
    · choose! C hC0 hC using ih
      let c : ℝ := ∑ j ∈ Ico 2 (k' + 3), ((k' + 2).choose j : ℝ) * B j * C (k' + 2 - j)
      have hc0 : 0 ≤ c := Finset.sum_nonneg fun j hj => by
        have hlt : k' + 2 - j < k' + 2 := by
          have hj2 := (Finset.mem_Ico.1 hj).1
          omega
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB0 j)) (hC0 _ hlt)
      refine ⟨c, hc0, fun {Ω} _ ν _ {g} hint h0 hBg n => ?_⟩
      let M_n (m : ℕ) : ℝ := ∫ y : Fin m → Ω, (∑ i, g (y i)) ^ (k' + 2) ∂(Measure.pi fun _ => ν)
      have hM0 : M_n 0 = 0 := by simp [M_n]
      have hstep (m : ℕ) : |M_n (m + 1) - M_n m| ≤ c * Real.sqrt ((m : ℝ) + 1) ^ k' := by
        have hrec := integral_pow_sum_pi_succ hint m (k' + 2)
        have hsplit : M_n (m + 1) - M_n m =
            ∑ j ∈ Ico 2 (k' + 3),
              ((k' + 2).choose j : ℝ) * (∫ x, g x ^ j ∂ν) *
                ∫ y : Fin m → Ω, (∑ i, g (y i)) ^ (k' + 2 - j) ∂(Measure.pi fun _ => ν) := by
          dsimp only [M_n]
          rw [hrec, ← Finset.sum_range_add_sum_Ico _ (show 2 ≤ k' + 2 + 1 by omega)]
          simp [Finset.sum_range_succ, h0]
        rw [hsplit, Finset.sum_mul]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
        have hj2 : 2 ≤ j := (Finset.mem_Ico.1 hj).1
        have hlt : k' + 2 - j < k' + 2 := by omega
        have h1 := hC (k' + 2 - j) hlt ν hint h0 hBg m
        have hpow : Real.sqrt ((m : ℝ) + 1) ^ (k' + 2 - j) ≤ Real.sqrt ((m : ℝ) + 1) ^ k' :=
          pow_le_pow_right₀ (one_le_sqrt_natCast_add_one m) (by omega)
        rw [abs_mul, abs_mul, Nat.abs_cast]
        calc ((k' + 2).choose j : ℝ) * |∫ x, g x ^ j ∂ν| *
              |∫ y : Fin m → Ω, (∑ i, g (y i)) ^ (k' + 2 - j) ∂(Measure.pi fun _ => ν)|
            ≤ ((k' + 2).choose j : ℝ) * B j *
                (C (k' + 2 - j) * Real.sqrt ((m : ℝ) + 1) ^ k') :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hBg j) (Nat.cast_nonneg _))
                (h1.trans (mul_le_mul_of_nonneg_left hpow (hC0 _ hlt)))
                (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB0 j))
          _ = ((k' + 2).choose j : ℝ) * B j * C (k' + 2 - j) * Real.sqrt ((m : ℝ) + 1) ^ k' := by
              ring
      exact abs_le_of_abs_sub_le_sqrt_pow hM0 hc0 hstep n

/-- **Binomial identity for Gaussian-scaled variance powers:**
`∑_{j ≤ k} C(k, j) (a(j) v₁^{j/2}) (a(k - j) v₂^{(k - j)/2}) = a(k) (v₁ + v₂)^{k/2}`
for any sequence `a` with `a 0 = 1`, `a 1 = 0`, `a (n + 2) = (n + 1) a n`, and any `v₁, v₂ : ℝ`
(no sign assumption on `v₁` or `v₂`). -/
theorem sum_choose_mul_gaussian_moments_eq {a : ℕ → ℝ}
    (ha0 : a 0 = 1) (ha1 : a 1 = 0) (ha : ∀ n, a (n + 2) = (n + 1) * a n)
    (v₁ v₂ : ℝ) (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * (a j * v₁ ^ (j / 2)) * (a (k - j) * v₂ ^ ((k - j) / 2))) =
      a k * (v₁ + v₂) ^ (k / 2) := by
  have hodd_zero : ∀ n, Odd n → a n = 0 := fun n hn =>
    Nat.eq_zero_of_odd_of_two_step_mul ha1 ha hn
  have heven_fact : ∀ m : ℕ, (2 ^ m : ℝ) * (m.factorial : ℝ) * a (2 * m) =
      ((2 * m).factorial : ℝ) := by
    intro m
    induction m with
    | zero => simp [ha0]
    | succ m ihm =>
      have h1 : 2 * (m + 1) = 2 * m + 2 := by ring
      have hf2 : ((2 * m + 2).factorial : ℝ) =
          (2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 1) * ((2 * m).factorial : ℝ) := by
        rw [Nat.factorial_succ (2 * m + 1), Nat.factorial_succ (2 * m)]
        push_cast; ring
      have hf1 : ((m + 1).factorial : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
        rw [Nat.factorial_succ m]; push_cast; ring
      rw [h1, ha (2 * m), hf2, hf1, pow_succ, ← ihm]
      push_cast; ring
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | hodd
  · rw [show m + m = 2 * m by ring]
    have hdiv : (2 * m) / 2 = m := by omega
    rw [hdiv]
    have hsum_even :
        (∑ j ∈ Finset.range (2 * m + 1),
          ((2 * m).choose j : ℝ) * (a j * v₁ ^ (j / 2)) *
            (a (2 * m - j) * v₂ ^ ((2 * m - j) / 2))) =
        ∑ l ∈ Finset.range (m + 1),
          ((2 * m).choose (2 * l) : ℝ) * (a (2 * l) * v₁ ^ l) *
            (a (2 * (m - l)) * v₂ ^ (m - l)) := by
      have hsub : ∀ m' : ℕ, ∀ f : ℕ → ℝ, (∀ j, Odd j → f j = 0) →
          ∑ j ∈ Finset.range (2 * m' + 1), f j = ∑ l ∈ Finset.range (m' + 1), f (2 * l) := by
        intro m' f hf
        induction m' with
        | zero => simp
        | succ m' ih =>
          rw [show 2 * (m' + 1) + 1 = (2 * m' + 1) + 2 by ring,
            Finset.sum_range_succ, Finset.sum_range_succ, ih,
            hf (2 * m' + 1) ⟨m', rfl⟩, add_zero,
            Finset.sum_range_succ _ (m' + 1), show 2 * m' + 2 = 2 * (m' + 1) by ring]
      rw [hsub m _ (fun j hj => by rw [hodd_zero j hj, zero_mul, mul_zero, zero_mul])]
      refine Finset.sum_congr rfl fun l hl => ?_
      have hl_le : l ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
      have e1 : 2 * l / 2 = l := by omega
      have e2 : 2 * m - 2 * l = 2 * (m - l) := by omega
      have e3 : 2 * (m - l) / 2 = m - l := by omega
      rw [e1, e2, e3]
    rw [hsum_even]
    have hterm_eq : ∀ l ∈ Finset.range (m + 1),
        ((2 * m).choose (2 * l) : ℝ) * (a (2 * l) * v₁ ^ l) *
          (a (2 * (m - l)) * v₂ ^ (m - l)) =
        a (2 * m) * ((m.choose l : ℝ) * v₁ ^ l * v₂ ^ (m - l)) := by
      intro l hl
      have hl_le : l ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
      have h2l_le : 2 * l ≤ 2 * m := by omega
      have hc_pos : (0 : ℝ) < (2 ^ m : ℝ) * (l.factorial : ℝ) * ((m - l).factorial : ℝ) := by
        positivity
      apply mul_left_cancel₀ hc_pos.ne'
      have hchoose1 := Nat.choose_mul_factorial_mul_factorial h2l_le
      have hchoose2 := Nat.choose_mul_factorial_mul_factorial hl_le
      have hsub2 : 2 * m - 2 * l = 2 * (m - l) := by omega
      have hcast1 : ((2 * m).choose (2 * l) : ℝ) * ((2 * l).factorial : ℝ) *
          ((2 * (m - l)).factorial : ℝ) = ((2 * m).factorial : ℝ) := by
        rw [← hsub2]; exact_mod_cast hchoose1
      have hcast2 : (m.choose l : ℝ) * (l.factorial : ℝ) * ((m - l).factorial : ℝ) =
          (m.factorial : ℝ) := by
        exact_mod_cast hchoose2
      have hpow2 : (2 ^ m : ℝ) = (2 ^ l : ℝ) * (2 ^ (m - l) : ℝ) := by
        rw [← pow_add, Nat.add_sub_of_le hl_le]
      calc (2 ^ m * ↑l.factorial * ↑(m - l).factorial) *
            (↑((2 * m).choose (2 * l)) * (a (2 * l) * v₁ ^ l) *
              (a (2 * (m - l)) * v₂ ^ (m - l)))
          = (↑((2 * m).choose (2 * l)) * (2 ^ l * ↑l.factorial * a (2 * l)) *
              (2 ^ (m - l) * ↑(m - l).factorial * a (2 * (m - l)))) *
              (v₁ ^ l * v₂ ^ (m - l)) := by
            rw [hpow2]; ring
        _ = (↑((2 * m).choose (2 * l)) * ↑(2 * l).factorial * ↑(2 * (m - l)).factorial) *
              (v₁ ^ l * v₂ ^ (m - l)) := by
            rw [heven_fact l, heven_fact (m - l)]
        _ = ↑(2 * m).factorial * (v₁ ^ l * v₂ ^ (m - l)) := by rw [hcast1]
        _ = (2 ^ m * ↑m.factorial * a (2 * m)) * (v₁ ^ l * v₂ ^ (m - l)) := by
            rw [← heven_fact m]
        _ = (2 ^ m * (↑(m.choose l) * ↑l.factorial * ↑(m - l).factorial) * a (2 * m)) *
              (v₁ ^ l * v₂ ^ (m - l)) := by
            rw [← hcast2]
        _ = (2 ^ m * ↑l.factorial * ↑(m - l).factorial) *
              (a (2 * m) * (↑(m.choose l) * v₁ ^ l * v₂ ^ (m - l))) := by
            ring
    rw [Finset.sum_congr rfl hterm_eq, ← Finset.mul_sum, add_pow]
    congr 1
    refine Finset.sum_congr rfl fun l _ => by ring
  · rw [hodd_zero k hodd, zero_mul]
    refine Finset.sum_eq_zero fun j hj => ?_
    rcases Nat.even_or_odd j with ⟨l, rfl⟩ | hj_odd
    · have hk_sub_odd : Odd (k - (l + l)) := by
        rcases hodd with ⟨m, rfl⟩
        have hj_le : l + l ≤ 2 * m + 1 := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        exact ⟨m - l, by omega⟩
      rw [hodd_zero _ hk_sub_odd, zero_mul, mul_zero]
    · rw [hodd_zero j hj_odd, zero_mul, mul_zero, zero_mul]

/-- **Uniform quantitative moment expansion of a centered i.i.d. sum under moment bounds `B`:**
Given `B : ℕ → ℝ` (`B j ≥ 0`), a sequence `a` with `a 0 = 1`, `a 1 = 0`, `a (n + 2) = (n + 1) a n`,
and `k : ℕ`, there exists `C ≥ 0` depending only on `B, a, k` such that for every probability space
`(Ω, ν)`, every centered `g : Ω → ℝ` with all powers integrable and `|∫ g^j dν| ≤ B j`, and every
`n : ℕ`,
`|𝔼 (∑_{i < n} g(y_i))^k - a(k) (∫ g² dν)^{k/2} n^{k/2}| ≤ C (√(n + 1))^{k - 1}`. -/
theorem exists_abs_integral_pow_sum_pi_sub_le (B : ℕ → ℝ) (hB0 : ∀ j, 0 ≤ B j)
    {a : ℕ → ℝ} (ha0 : a 0 = 1) (ha1 : a 1 = 0) (ha : ∀ n, a (n + 2) = (n + 1) * a n)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] {g : Ω → ℝ},
        (∀ j, Integrable (fun x => g x ^ j) ν) →
        ∫ x, g x ∂ν = 0 →
        (∀ j, |∫ x, g x ^ j ∂ν| ≤ B j) →
        ∀ n : ℕ,
          |∫ y : Fin n → Ω, (∑ i, g (y i)) ^ k ∂(Measure.pi fun _ : Fin n => ν) -
              a k * (∫ x, g x ^ 2 ∂ν) ^ (k / 2) * (n : ℝ) ^ (k / 2)| ≤
            C * Real.sqrt ((n : ℝ) + 1) ^ (k - 1) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases lt_or_ge k 3 with hk3 | hk3
    · interval_cases k
      · refine ⟨0, le_rfl, fun ν _ _ _ _ n => ?_⟩
        simp [ha0]
      · refine ⟨0, le_rfl, fun {Ω} _ ν _ {g} hint h0 _ n => ?_⟩
        have hM1 : ∀ m : ℕ, ∫ y : Fin m → Ω, (∑ i, g (y i)) ^ 1 ∂(Measure.pi fun _ => ν) = 0 := by
          intro m
          induction m with
          | zero => simp
          | succ m ihm =>
            rw [integral_pow_sum_pi_succ hint m 1]
            simp only [pow_one] at ihm
            simp [Finset.sum_range_succ, h0, ihm]
        rw [hM1 n]; simp [ha1]
      · refine ⟨0, le_rfl, fun {Ω} _ ν _ {g} hint h0 _ n => ?_⟩
        have ha2 : a 2 = 1 := by rw [show (2 : ℕ) = 0 + 2 from rfl, ha, ha0]; simp
        have hM2 : ∀ m : ℕ, ∫ y : Fin m → Ω, (∑ i, g (y i)) ^ 2 ∂(Measure.pi fun _ => ν) =
            (m : ℝ) * ∫ x, g x ^ 2 ∂ν := by
          intro m
          induction m with
          | zero => simp
          | succ m ihm =>
            rw [integral_pow_sum_pi_succ hint m 2,
              ← Finset.sum_range_add_sum_Ico _ (show 2 ≤ 3 by omega)]
            simp [Finset.sum_range_succ, h0, ihm]
            ring
        rw [hM2 n, ha2]; simp; ring_nf
    · choose! C hC0 hC using ih
      choose! C_pri hCpri0 hCpri using fun j => exists_abs_integral_pow_sum_pi_le B hB0 j
      let c_T : ℝ := (k : ℝ) * (k - 1) * |a k| * B 2 ^ (k / 2)
      let c_R : ℝ := ∑ i ∈ Finset.Ico 3 (k + 1), (k.choose i : ℝ) * B i * C_pri (k - i)
      let c : ℝ := (k.choose 2 : ℝ) * B 2 * C (k - 2) + c_R + c_T
      have hCk2 : 0 ≤ C (k - 2) := hC0 _ (by omega)
      have hcR0 : 0 ≤ c_R := Finset.sum_nonneg fun i _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB0 i)) (hCpri0 _)
      have hB2_0 : 0 ≤ B 2 := hB0 2
      have hcT0 : 0 ≤ c_T := by
        dsimp only [c_T]
        have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
        have hsub0 : 0 ≤ (k : ℝ) - 1 := sub_nonneg.2 hk1
        exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hsub0) (abs_nonneg _))
          (pow_nonneg hB2_0 _)
      have hc0 : 0 ≤ c :=
        add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hB2_0) hCk2) hcR0) hcT0
      refine ⟨c, hc0, fun {Ω} _ ν _ {g} hint h0 hBg n => ?_⟩
      let M_fn (m : ℕ) (j : ℕ) : ℝ :=
        ∫ y : Fin m → Ω, (∑ i, g (y i)) ^ j ∂(Measure.pi fun _ => ν)
      let μ2 : ℝ := ∫ x, g x ^ 2 ∂ν
      have hμ2_0 : 0 ≤ μ2 := integral_nonneg fun _ => sq_nonneg _
      have hμ2_le : μ2 ≤ B 2 := (le_abs_self _).trans (hBg 2)
      have hrec2 (m : ℕ) : M_fn (m + 1) k = M_fn m k + (k.choose 2 : ℝ) * μ2 * M_fn m (k - 2) +
          ∑ i ∈ Finset.Ico 3 (k + 1), (k.choose i : ℝ) * (∫ x, g x ^ i ∂ν) * M_fn m (k - i) := by
        dsimp only [M_fn]
        rw [integral_pow_sum_pi_succ hint m k,
          ← Finset.sum_range_add_sum_Ico _ (show 3 ≤ k + 1 by omega)]
        simp [Finset.sum_range_succ, h0, μ2, add_assoc]
      have hT_unif (m : ℕ) :
          |(k.choose 2 : ℝ) * μ2 * (a (k - 2) * μ2 ^ ((k - 2) / 2) * (m : ℝ) ^ ((k - 2) / 2)) -
            (a k * μ2 ^ (k / 2) * (((m + 1 : ℕ) : ℝ)) ^ (k / 2) -
              a k * μ2 ^ (k / 2) * (m : ℝ) ^ (k / 2))| ≤
            c_T * Real.sqrt ((m : ℝ) + 1) ^ (k - 3) := by
        refine (abs_gaussian_moment_increment_sub_le ha1 ha hμ2_0 hk3 m).trans ?_
        dsimp only [c_T]
        gcongr
        exact pow_le_pow_left₀ hμ2_0 hμ2_le _
      have hΔ (m : ℕ) :
          |(M_fn (m + 1) k - a k * μ2 ^ (k / 2) * (((m + 1 : ℕ) : ℝ)) ^ (k / 2)) -
            (M_fn m k - a k * μ2 ^ (k / 2) * (m : ℝ) ^ (k / 2))| ≤
            c * Real.sqrt ((m : ℝ) + 1) ^ (k - 3) := by
        have hs1 := one_le_sqrt_natCast_add_one m
        let R_m := ∑ i ∈ Finset.Ico 3 (k + 1),
          (k.choose i : ℝ) * (∫ x, g x ^ i ∂ν) * M_fn m (k - i)
        have hRb : |R_m| ≤ c_R * Real.sqrt ((m : ℝ) + 1) ^ (k - 3) := by
          dsimp only [R_m, c_R]
          rw [Finset.sum_mul]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
          have hi3 : 3 ≤ i := (Finset.mem_Ico.1 hi).1
          have h1 := hCpri (k - i) ν hint h0 hBg m
          have h2 : Real.sqrt ((m : ℝ) + 1) ^ (k - i) ≤ Real.sqrt ((m : ℝ) + 1) ^ (k - 3) :=
            pow_le_pow_right₀ hs1 (by omega)
          rw [abs_mul, abs_mul, Nat.abs_cast]
          calc (k.choose i : ℝ) * |∫ x, g x ^ i ∂ν| * |M_fn m (k - i)|
              ≤ (k.choose i : ℝ) * B i *
                  (C_pri (k - i) * Real.sqrt ((m : ℝ) + 1) ^ (k - 3)) :=
                mul_le_mul (mul_le_mul_of_nonneg_left (hBg i) (Nat.cast_nonneg _))
                  (h1.trans (mul_le_mul_of_nonneg_left h2 (hCpri0 _)))
                  (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB0 i))
            _ = _ := by ring
        have hEb : (k.choose 2 : ℝ) * μ2 *
            |M_fn m (k - 2) - a (k - 2) * μ2 ^ ((k - 2) / 2) * (m : ℝ) ^ ((k - 2) / 2)| ≤
            (k.choose 2 : ℝ) * B 2 * C (k - 2) * Real.sqrt ((m : ℝ) + 1) ^ (k - 3) := by
          have h1 := hC (k - 2) (by omega) ν hint h0 hBg m
          rw [show k - 2 - 1 = k - 3 by omega] at h1
          calc (k.choose 2 : ℝ) * μ2 * |M_fn m (k - 2) - _|
              ≤ (k.choose 2 : ℝ) * B 2 *
                  (C (k - 2) * Real.sqrt ((m : ℝ) + 1) ^ (k - 3)) :=
                mul_le_mul (mul_le_mul_of_nonneg_left hμ2_le (Nat.cast_nonneg _))
                  h1 (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB0 2))
            _ = _ := by ring
        have hid : (M_fn (m + 1) k - a k * μ2 ^ (k / 2) * (((m + 1 : ℕ) : ℝ)) ^ (k / 2)) -
            (M_fn m k - a k * μ2 ^ (k / 2) * (m : ℝ) ^ (k / 2)) =
            (k.choose 2 : ℝ) * μ2 *
              (M_fn m (k - 2) - a (k - 2) * μ2 ^ ((k - 2) / 2) * (m : ℝ) ^ ((k - 2) / 2)) +
              R_m +
            ((k.choose 2 : ℝ) * μ2 *
                (a (k - 2) * μ2 ^ ((k - 2) / 2) * (m : ℝ) ^ ((k - 2) / 2)) -
              (a k * μ2 ^ (k / 2) * (((m + 1 : ℕ) : ℝ)) ^ (k / 2) -
                a k * μ2 ^ (k / 2) * (m : ℝ) ^ (k / 2))) := by
          rw [hrec2 m]; dsimp only [R_m]; ring
        rw [hid]
        calc _ ≤ |(k.choose 2 : ℝ) * μ2 *
                (M_fn m (k - 2) - a (k - 2) * μ2 ^ ((k - 2) / 2) * (m : ℝ) ^ ((k - 2) / 2)) +
                R_m| +
              |(k.choose 2 : ℝ) * μ2 *
                  (a (k - 2) * μ2 ^ ((k - 2) / 2) * (m : ℝ) ^ ((k - 2) / 2)) -
                (a k * μ2 ^ (k / 2) * (((m + 1 : ℕ) : ℝ)) ^ (k / 2) -
                  a k * μ2 ^ (k / 2) * (m : ℝ) ^ (k / 2))| := abs_add_le _ _
          _ ≤ (|(k.choose 2 : ℝ) * μ2 *
                (M_fn m (k - 2) - a (k - 2) * μ2 ^ ((k - 2) / 2) * (m : ℝ) ^ ((k - 2) / 2))| +
                |R_m|) +
              c_T * Real.sqrt ((m : ℝ) + 1) ^ (k - 3) :=
            add_le_add (abs_add_le _ _) (hT_unif m)
          _ ≤ c * Real.sqrt ((m : ℝ) + 1) ^ (k - 3) := by
            rw [abs_mul, abs_mul, Nat.abs_cast, abs_of_nonneg hμ2_0]
            dsimp only [c]; linarith [hEb, hRb]
      have he0 : M_fn 0 k - a k * μ2 ^ (k / 2) * ((0 : ℕ) : ℝ) ^ (k / 2) = 0 := by
        dsimp only [M_fn]
        simp [zero_pow (by omega : k ≠ 0), zero_pow (by omega : k / 2 ≠ 0)]
      have hres := abs_le_of_abs_sub_le_sqrt_pow
        (e := fun m => M_fn m k - a k * μ2 ^ (k / 2) * (m : ℝ) ^ (k / 2)) he0 hc0 hΔ n
      rwa [show k - 3 + 2 = k - 1 by omega] at hres


/-- **Uniform moment expansion of the sum of two independent centered i.i.d. sums:**
If `X` is a sum of `L` i.i.d. variables under `ν₁` (`L ≥ 1`, moments bounded by `B₁`) and `Y` is an
independent sum of `M` i.i.d. variables under `ν₂` (`M ≤ L`, moments bounded by `B₂`), then
`|𝔼[(L⁻¹ X + L⁻¹ Y)^m] - (√L)⁻¹^m a(m) (v₁ + (M / L) v₂)^{m/2}| ≤ C (√L)⁻¹^{m+1}` uniformly in
`L ≥ 1` and `M ≤ L`. -/
theorem exists_abs_integral_add_pow_avg_two_pi_sub_le_all_orders
    (B₁ B₂ : ℕ → ℝ) (hB₁ : ∀ j, 0 ≤ B₁ j) (hB₂ : ∀ j, 0 ≤ B₂ j)
    {a : ℕ → ℝ} (ha0 : a 0 = 1) (ha1 : a 1 = 0) (ha : ∀ n, a (n + 2) = (n + 1) * a n)
    (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
        (ν₁ : Measure Ω₁) [IsProbabilityMeasure ν₁]
        (ν₂ : Measure Ω₂) [IsProbabilityMeasure ν₂]
        {f₁ : Ω₁ → ℝ} {f₂ : Ω₂ → ℝ},
        (∀ j, Integrable (fun x => f₁ x ^ j) ν₁) →
        ∫ x, f₁ x ∂ν₁ = 0 →
        (∀ j, |∫ x, f₁ x ^ j ∂ν₁| ≤ B₁ j) →
        (∀ j, Integrable (fun x => f₂ x ^ j) ν₂) →
        ∫ x, f₂ x ∂ν₂ = 0 →
        (∀ j, |∫ x, f₂ x ^ j ∂ν₂| ≤ B₂ j) →
        ∀ (L M : ℕ), 1 ≤ L → (M : ℝ) ≤ L →
          |∫ p : (Fin L → Ω₁) × (Fin M → Ω₂),
              ((L : ℝ)⁻¹ * ∑ i, f₁ (p.1 i) + (L : ℝ)⁻¹ * ∑ j, f₂ (p.2 j)) ^ m
              ∂((Measure.pi fun _ : Fin L => ν₁).prod (Measure.pi fun _ : Fin M => ν₂)) -
            ((Real.sqrt L)⁻¹) ^ m * a m *
              ((∫ x, f₁ x ^ 2 ∂ν₁) + ((M : ℝ) / L) * (∫ x, f₂ x ^ 2 ∂ν₂)) ^ (m / 2)| ≤
            C * ((Real.sqrt L)⁻¹) ^ (m + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨0, le_rfl, ?_⟩
    intros
    simp [ha0]
  choose! C₁ hC₁0 hC₁ using fun j => exists_abs_integral_pow_sum_pi_sub_le B₁ hB₁ ha0 ha1 ha j
  choose! C₂ hC₂0 hC₂ using fun j => exists_abs_integral_pow_sum_pi_sub_le B₂ hB₂ ha0 ha1 ha j
  choose! K₂ hK₂0 hK₂ using fun j => exists_abs_integral_pow_sum_pi_le B₂ hB₂ j
  let c_term (j : ℕ) : ℝ :=
    (m.choose j : ℝ) *
      (C₁ j * Real.sqrt 2 ^ (j - 1) * K₂ (m - j) * Real.sqrt 2 ^ (m - j) +
        |a j| * B₁ 2 ^ (j / 2) * C₂ (m - j) * Real.sqrt 2 ^ (m - j - 1))
  let C : ℝ := ∑ j ∈ Finset.range (m + 1), c_term j
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => by
    dsimp only [c_term]
    have := hC₁0 j; have := hK₂0 (m - j); have := hC₂0 (m - j); have := hB₁ 2
    positivity
  refine ⟨C, hC0, ?_⟩
  intro Ω₁ Ω₂ _ _ ν₁ _ ν₂ _ f₁ f₂ hint₁ h0₁ hB₁f hint₂ h0₂ hB₂f L M hL1 hML
  let P₁ := Measure.pi fun _ : Fin L => ν₁
  let P₂ := Measure.pi fun _ : Fin M => ν₂
  have hL_pos : (0 : ℝ) < L := Nat.cast_pos.2 hL1
  have hL_ge1 : (1 : ℝ) ≤ L := Nat.one_le_cast.2 hL1
  have hsL_pos : 0 < Real.sqrt L := Real.sqrt_pos.2 hL_pos
  have hsL_ge1 : 1 ≤ Real.sqrt L := by simpa using Real.sqrt_le_sqrt hL_ge1
  let ε : ℝ := (Real.sqrt L)⁻¹
  have hε_pos : 0 < ε := inv_pos.2 hsL_pos
  have hε2 : ε ^ 2 = (L : ℝ)⁻¹ := by dsimp only [ε]; rw [inv_pow, Real.sq_sqrt hL_pos.le]
  let v₁ : ℝ := ∫ x, f₁ x ^ 2 ∂ν₁
  let v₂ : ℝ := ∫ x, f₂ x ^ 2 ∂ν₂
  have hv₁0 : 0 ≤ v₁ := integral_nonneg fun _ => sq_nonneg _
  have hv₂0 : 0 ≤ v₂ := integral_nonneg fun _ => sq_nonneg _
  have hv₁_le : v₁ ≤ B₁ 2 := (le_abs_self _).trans (hB₁f 2)
  let S₁ (x : Fin L → Ω₁) : ℝ := ∑ i, f₁ (x i)
  let S₂ (y : Fin M → Ω₂) : ℝ := ∑ j, f₂ (y j)
  have hexp_int :
      ∫ p : (Fin L → Ω₁) × (Fin M → Ω₂),
        ((L : ℝ)⁻¹ * S₁ p.1 + (L : ℝ)⁻¹ * S₂ p.2) ^ m ∂(P₁.prod P₂) =
      ((L : ℝ)⁻¹) ^ m * ∑ j ∈ Finset.range (m + 1),
        (m.choose j : ℝ) * (∫ x, S₁ x ^ j ∂P₁) * (∫ y, S₂ y ^ (m - j) ∂P₂) := by
    have hpt (p : (Fin L → Ω₁) × (Fin M → Ω₂)) :
        ((L : ℝ)⁻¹ * S₁ p.1 + (L : ℝ)⁻¹ * S₂ p.2) ^ m =
          ((L : ℝ)⁻¹) ^ m * ∑ j ∈ Finset.range (m + 1),
            (m.choose j : ℝ) * (S₁ p.1 ^ j * S₂ p.2 ^ (m - j)) := by
      rw [← mul_add, mul_pow, add_pow]
      congr 1
      refine Finset.sum_congr rfl fun j _ => by ring
    simp_rw [hpt]
    rw [integral_const_mul, integral_finsetSum]
    · congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
      have hprod := integral_prod_mul (μ := P₁) (ν := P₂)
        (fun x => S₁ x ^ j) (fun y => S₂ y ^ (m - j))
      rw [hprod]; ring
    · intro j _
      have hi1 : Integrable (fun x => S₁ x ^ j) P₁ := integrable_pow_sum_pi hint₁ L j
      have hi2 : Integrable (fun y => S₂ y ^ (m - j)) P₂ := integrable_pow_sum_pi hint₂ M (m - j)
      exact (hi1.mul_prod hi2).const_mul _
  have href_eq :
      ε ^ m * a m * (v₁ + ((M : ℝ) / L) * v₂) ^ (m / 2) =
        ((L : ℝ)⁻¹) ^ m * ∑ j ∈ Finset.range (m + 1),
          (m.choose j : ℝ) * (a j * v₁ ^ (j / 2) * (L : ℝ) ^ (j / 2)) *
            (a (m - j) * v₂ ^ ((m - j) / 2) * (M : ℝ) ^ ((m - j) / 2)) := by
    have hbin := sum_choose_mul_gaussian_moments_eq ha0 ha1 ha v₁ (((M : ℝ) / L) * v₂) m
    rw [mul_assoc, ← hbin, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_le : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    rcases Nat.even_or_odd j with ⟨l, rfl⟩ | hj_odd
    · rcases Nat.even_or_odd (m - (l + l)) with ⟨r_idx, hr_eq⟩ | hmj_odd
      · have hm_eq : m = 2 * (l + r_idx) := by omega
        have hj_div : (l + l) / 2 = l := by omega
        have hmj_div : (m - (l + l)) / 2 = r_idx := by omega
        rw [hj_div, hmj_div, hm_eq]
        have hε_pow : ε ^ (2 * (l + r_idx)) = ((L : ℝ)⁻¹) ^ l * ((L : ℝ)⁻¹) ^ r_idx := by
          rw [pow_mul, hε2, pow_add]
        have hL_2pow : ((L : ℝ)⁻¹) ^ (2 * (l + r_idx)) =
            (((L : ℝ)⁻¹) ^ l * ((L : ℝ)⁻¹) ^ r_idx) *
              (((L : ℝ)⁻¹) ^ l * ((L : ℝ)⁻¹) ^ r_idx) := by
          rw [show 2 * (l + r_idx) = (l + r_idx) + (l + r_idx) by ring, pow_add, pow_add]
        have hLl : ((L : ℝ)⁻¹) ^ l * (L : ℝ) ^ l = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ hL_pos.ne', one_pow]
        have hMr : ((M : ℝ) ^ r_idx / (L : ℝ) ^ r_idx) = ((L : ℝ)⁻¹) ^ r_idx * (M : ℝ) ^ r_idx := by
          rw [div_eq_mul_inv, inv_pow, mul_comm]
        rw [hε_pow, hL_2pow, mul_pow, div_pow, hMr]
        calc (((L : ℝ)⁻¹) ^ l * ((L : ℝ)⁻¹) ^ r_idx) *
              (((2 * (l + r_idx)).choose (l + l) : ℝ) * (a (l + l) * v₁ ^ l) *
                (a (2 * (l + r_idx) - (l + l)) * ((((L : ℝ)⁻¹) ^ r_idx * (M : ℝ) ^ r_idx) *
                  v₂ ^ r_idx)))
            = (((L : ℝ)⁻¹) ^ l * ((L : ℝ)⁻¹) ^ r_idx) *
                (((L : ℝ)⁻¹) ^ l * (L : ℝ) ^ l) *
                (((L : ℝ)⁻¹) ^ r_idx) *
                (((2 * (l + r_idx)).choose (l + l) : ℝ) * (a (l + l) * v₁ ^ l) *
                  (a (2 * (l + r_idx) - (l + l)) * ((M : ℝ) ^ r_idx * v₂ ^ r_idx))) := by
              rw [hLl, mul_one]; ring
          _ = (((L : ℝ)⁻¹) ^ l * ((L : ℝ)⁻¹) ^ r_idx * (((L : ℝ)⁻¹) ^ l * ((L : ℝ)⁻¹) ^ r_idx)) *
                (((2 * (l + r_idx)).choose (l + l) : ℝ) * (a (l + l) * v₁ ^ l * (L : ℝ) ^ l) *
                  (a (2 * (l + r_idx) - (l + l)) * v₂ ^ r_idx * (M : ℝ) ^ r_idx)) := by
              ring
      · have hzero := Nat.eq_zero_of_odd_of_two_step_mul ha1 ha hmj_odd
        rw [hzero]; ring
    · have hzero := Nat.eq_zero_of_odd_of_two_step_mul ha1 ha hj_odd
      rw [hzero]; ring
  rw [hexp_int, href_eq, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ ((L : ℝ)⁻¹) ^ m)]
  have hsL2 : Real.sqrt ((L : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt L := by
    rw [← Real.sqrt_mul zero_le_two]; exact Real.sqrt_le_sqrt (by linarith)
  have hsM2 : Real.sqrt ((M : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt L := by
    rw [← Real.sqrt_mul zero_le_two]; exact Real.sqrt_le_sqrt (by linarith)
  have hscale_m1 : ((L : ℝ)⁻¹) ^ m * Real.sqrt L ^ (m - 1) = ε ^ (m + 1) := by
    rw [← hε2, ← pow_mul, show 2 * m = (m + 1) + (m - 1) by omega, pow_add]
    have h1 : ε ^ (m - 1) * Real.sqrt L ^ (m - 1) = 1 := by
      rw [← mul_pow]; dsimp only [ε]; rw [inv_mul_cancel₀ hsL_pos.ne', one_pow]
    calc ε ^ (m + 1) * ε ^ (m - 1) * Real.sqrt L ^ (m - 1)
        = ε ^ (m + 1) * (ε ^ (m - 1) * Real.sqrt L ^ (m - 1)) := by ring
      _ = ε ^ (m + 1) := by rw [h1, mul_one]
  have hterm_bd : ∀ j ∈ Finset.range (m + 1),
      |(m.choose j : ℝ) * (∫ x, S₁ x ^ j ∂P₁) * (∫ y, S₂ y ^ (m - j) ∂P₂) -
        (m.choose j : ℝ) * (a j * v₁ ^ (j / 2) * (L : ℝ) ^ (j / 2)) *
          (a (m - j) * v₂ ^ ((m - j) / 2) * (M : ℝ) ^ ((m - j) / 2))| ≤
      c_term j * Real.sqrt L ^ (m - 1) := by
    intro j hj
    have hj_le : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    let A₁ := ∫ x, S₁ x ^ j ∂P₁
    let R₁ := a j * v₁ ^ (j / 2) * (L : ℝ) ^ (j / 2)
    let A₂ := ∫ y, S₂ y ^ (m - j) ∂P₂
    let R₂ := a (m - j) * v₂ ^ ((m - j) / 2) * (M : ℝ) ^ ((m - j) / 2)
    have hdecomp : (m.choose j : ℝ) * A₁ * A₂ - (m.choose j : ℝ) * R₁ * R₂ =
        (m.choose j : ℝ) * ((A₁ - R₁) * A₂ + R₁ * (A₂ - R₂)) := by ring
    rw [hdecomp, abs_mul, Nat.abs_cast]
    have hpart1 : |(A₁ - R₁) * A₂| ≤
        (C₁ j * Real.sqrt 2 ^ (j - 1) * K₂ (m - j) * Real.sqrt 2 ^ (m - j)) *
          Real.sqrt L ^ (m - 1) := by
      rcases Nat.eq_zero_or_pos j with rfl | hj_pos
      · have hA1R1 : A₁ - R₁ = 0 := by simp [A₁, R₁, P₁, ha0]
        rw [hA1R1, zero_mul, abs_zero]
        have := hC₁0 0; have := hK₂0 (m - 0); positivity
      · rw [abs_mul]
        have hb1 : |A₁ - R₁| ≤ C₁ j * Real.sqrt 2 ^ (j - 1) * Real.sqrt L ^ (j - 1) := by
          have hraw := hC₁ j ν₁ hint₁ h0₁ hB₁f L
          have hp : Real.sqrt ((L : ℝ) + 1) ^ (j - 1) ≤
              Real.sqrt 2 ^ (j - 1) * Real.sqrt L ^ (j - 1) := by
            rw [← mul_pow]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsL2 _
          exact hraw.trans ((mul_le_mul_of_nonneg_left hp (hC₁0 j)).trans_eq (by ring))
        have hb2 : |A₂| ≤ K₂ (m - j) * Real.sqrt 2 ^ (m - j) * Real.sqrt L ^ (m - j) := by
          have hraw := hK₂ (m - j) ν₂ hint₂ h0₂ hB₂f M
          have hp : Real.sqrt ((M : ℝ) + 1) ^ (m - j) ≤
              Real.sqrt 2 ^ (m - j) * Real.sqrt L ^ (m - j) := by
            rw [← mul_pow]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsM2 _
          exact hraw.trans ((mul_le_mul_of_nonneg_left hp (hK₂0 (m - j))).trans_eq (by ring))
        have hexp : (j - 1) + (m - j) = m - 1 := by omega
        calc |A₁ - R₁| * |A₂|
            ≤ (C₁ j * Real.sqrt 2 ^ (j - 1) * Real.sqrt L ^ (j - 1)) *
                (K₂ (m - j) * Real.sqrt 2 ^ (m - j) * Real.sqrt L ^ (m - j)) :=
              mul_le_mul hb1 hb2 (abs_nonneg _)
                (by have := hC₁0 j; positivity)
          _ = (C₁ j * Real.sqrt 2 ^ (j - 1) * K₂ (m - j) * Real.sqrt 2 ^ (m - j)) *
                (Real.sqrt L ^ (j - 1) * Real.sqrt L ^ (m - j)) := by ring
          _ = (C₁ j * Real.sqrt 2 ^ (j - 1) * K₂ (m - j) * Real.sqrt 2 ^ (m - j)) *
                Real.sqrt L ^ (m - 1) := by rw [← pow_add, hexp]
    have hpart2 : |R₁ * (A₂ - R₂)| ≤
        (|a j| * B₁ 2 ^ (j / 2) * C₂ (m - j) * Real.sqrt 2 ^ (m - j - 1)) *
          Real.sqrt L ^ (m - 1) := by
      rcases Nat.eq_zero_or_pos (m - j) with hmj0 | hmj_pos
      · have hjm : j = m := by omega
        subst hjm
        have hA2R2 : A₂ - R₂ = 0 := by simp [A₂, R₂, P₂, ha0]
        rw [hA2R2, mul_zero, abs_zero]
        have := hC₂0 (j - j); have := hB₁ 2; positivity
      · rw [abs_mul]
        have hR1_bd : |R₁| ≤ |a j| * B₁ 2 ^ (j / 2) * Real.sqrt L ^ j := by
          dsimp only [R₁]
          rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hv₁0 _),
            abs_of_nonneg (pow_nonneg hL_pos.le _)]
          have hLj : (L : ℝ) ^ (j / 2) ≤ Real.sqrt L ^ j := by
            have h1 : (L : ℝ) ^ (j / 2) = Real.sqrt L ^ (2 * (j / 2)) := by
              rw [pow_mul, Real.sq_sqrt hL_pos.le]
            rw [h1]
            exact pow_le_pow_right₀ hsL_ge1 (Nat.mul_div_le j 2)
          exact mul_le_mul (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hv₁0 hv₁_le _) (abs_nonneg _)) hLj
            (pow_nonneg hL_pos.le _)
            (mul_nonneg (abs_nonneg _) (pow_nonneg (hB₁ 2) _))
        have hb2 : |A₂ - R₂| ≤
            C₂ (m - j) * Real.sqrt 2 ^ (m - j - 1) * Real.sqrt L ^ (m - j - 1) := by
          have hraw := hC₂ (m - j) ν₂ hint₂ h0₂ hB₂f M
          have hp : Real.sqrt ((M : ℝ) + 1) ^ (m - j - 1) ≤
              Real.sqrt 2 ^ (m - j - 1) * Real.sqrt L ^ (m - j - 1) := by
            rw [← mul_pow]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsM2 _
          exact hraw.trans ((mul_le_mul_of_nonneg_left hp (hC₂0 (m - j))).trans_eq (by ring))
        have hexp : j + (m - j - 1) = m - 1 := by omega
        calc |R₁| * |A₂ - R₂|
            ≤ (|a j| * B₁ 2 ^ (j / 2) * Real.sqrt L ^ j) *
                (C₂ (m - j) * Real.sqrt 2 ^ (m - j - 1) * Real.sqrt L ^ (m - j - 1)) :=
              mul_le_mul hR1_bd hb2 (abs_nonneg _)
                (by have := hB₁ 2; positivity)
          _ = (|a j| * B₁ 2 ^ (j / 2) * C₂ (m - j) * Real.sqrt 2 ^ (m - j - 1)) *
                (Real.sqrt L ^ j * Real.sqrt L ^ (m - j - 1)) := by ring
          _ = (|a j| * B₁ 2 ^ (j / 2) * C₂ (m - j) * Real.sqrt 2 ^ (m - j - 1)) *
                Real.sqrt L ^ (m - 1) := by rw [← pow_add, hexp]
    dsimp only [c_term]
    calc (m.choose j : ℝ) * |(A₁ - R₁) * A₂ + R₁ * (A₂ - R₂)|
        ≤ (m.choose j : ℝ) * (|(A₁ - R₁) * A₂| + |R₁ * (A₂ - R₂)|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) (Nat.cast_nonneg _)
      _ ≤ (m.choose j : ℝ) *
            ((C₁ j * Real.sqrt 2 ^ (j - 1) * K₂ (m - j) * Real.sqrt 2 ^ (m - j)) *
                Real.sqrt L ^ (m - 1) +
              (|a j| * B₁ 2 ^ (j / 2) * C₂ (m - j) * Real.sqrt 2 ^ (m - j - 1)) *
                Real.sqrt L ^ (m - 1)) :=
          mul_le_mul_of_nonneg_left (add_le_add hpart1 hpart2) (Nat.cast_nonneg _)
      _ = _ := by ring
  calc ((L : ℝ)⁻¹) ^ m *
        |∑ j ∈ Finset.range (m + 1),
          ((m.choose j : ℝ) * (∫ x, S₁ x ^ j ∂P₁) * (∫ y, S₂ y ^ (m - j) ∂P₂) -
            (m.choose j : ℝ) * (a j * v₁ ^ (j / 2) * (L : ℝ) ^ (j / 2)) *
              (a (m - j) * v₂ ^ ((m - j) / 2) * (M : ℝ) ^ ((m - j) / 2)))|
      ≤ ((L : ℝ)⁻¹) ^ m *
          ∑ j ∈ Finset.range (m + 1), c_term j * Real.sqrt L ^ (m - 1) :=
        mul_le_mul_of_nonneg_left
          ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm_bd))
          (by positivity)
    _ = C * (((L : ℝ)⁻¹) ^ m * Real.sqrt L ^ (m - 1)) := by
        dsimp only [C]; rw [← Finset.sum_mul]; ring
    _ = C * ε ^ (m + 1) := by rw [hscale_m1]


/-- The positive-order form of the two-sum moment expansion. -/
theorem exists_abs_integral_add_pow_avg_two_pi_sub_le
    (B₁ B₂ : ℕ → ℝ) (hB₁ : ∀ j, 0 ≤ B₁ j) (hB₂ : ∀ j, 0 ≤ B₂ j)
    {a : ℕ → ℝ} (ha0 : a 0 = 1) (ha1 : a 1 = 0) (ha : ∀ n, a (n + 2) = (n + 1) * a n)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
        (ν₁ : Measure Ω₁) [IsProbabilityMeasure ν₁]
        (ν₂ : Measure Ω₂) [IsProbabilityMeasure ν₂]
        {f₁ : Ω₁ → ℝ} {f₂ : Ω₂ → ℝ},
        (∀ j, Integrable (fun x => f₁ x ^ j) ν₁) →
        ∫ x, f₁ x ∂ν₁ = 0 →
        (∀ j, |∫ x, f₁ x ^ j ∂ν₁| ≤ B₁ j) →
        (∀ j, Integrable (fun x => f₂ x ^ j) ν₂) →
        ∫ x, f₂ x ∂ν₂ = 0 →
        (∀ j, |∫ x, f₂ x ^ j ∂ν₂| ≤ B₂ j) →
        ∀ (L M : ℕ), 1 ≤ L → (M : ℝ) ≤ L →
          |∫ p : (Fin L → Ω₁) × (Fin M → Ω₂),
              ((L : ℝ)⁻¹ * ∑ i, f₁ (p.1 i) + (L : ℝ)⁻¹ * ∑ j, f₂ (p.2 j)) ^ m
              ∂((Measure.pi fun _ : Fin L => ν₁).prod (Measure.pi fun _ : Fin M => ν₂)) -
            ((Real.sqrt L)⁻¹) ^ m * a m *
              ((∫ x, f₁ x ^ 2 ∂ν₁) + ((M : ℝ) / L) * (∫ x, f₂ x ^ 2 ∂ν₂)) ^ (m / 2)| ≤
            C * ((Real.sqrt L)⁻¹) ^ (m + 1) :=
  exists_abs_integral_add_pow_avg_two_pi_sub_le_all_orders B₁ B₂ hB₁ hB₂ ha0 ha1 ha m

section Main

variable {Ω : Type*} [MeasurableSpace Ω]
  {ν : Measure Ω} [IsProbabilityMeasure ν] {f : Ω → ℝ}

/-- **Moment expansion of an i.i.d. centered sum** (Talagrand, Eq. (1.122)).  Let `f` be centered
under `ν` with all powers integrable, and let `a` satisfy `a 0 = 1`, `a 1 = 0`,
`a (k + 2) = (k + 1) a k` (the moments of a standard Gaussian).  Then for every `k` there is `C`
with `|𝔼 (∑_{i<n} f (yᵢ))^k - a k σ2^{⌊k/2⌋} n^{⌊k/2⌋}| ≤ C (√(n + 1))^{k-1}` for all `n`, where
`σ2 = ∫ f² dν`. -/
theorem iid_sum_moment_expansion (hint : ∀ j, Integrable (fun x => f x ^ j) ν)
    (h0 : ∫ x, f x ∂ν = 0) {a : ℕ → ℝ} (ha0 : a 0 = 1) (ha1 : a 1 = 0)
    (ha : ∀ k, a (k + 2) = (k + 1) * a k) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |∫ y : Fin n → Ω, (∑ i, f (y i)) ^ k ∂(Measure.pi fun _ : Fin n => ν) -
        a k * (∫ x, f x ^ 2 ∂ν) ^ (k / 2) * (n : ℝ) ^ (k / 2)| ≤
      C * Real.sqrt ((n : ℝ) + 1) ^ (k - 1) := by
  obtain ⟨C, hC, hbound⟩ := exists_abs_integral_pow_sum_pi_sub_le
    (fun j => |∫ x, f x ^ j ∂ν|) (fun _ => abs_nonneg _) ha0 ha1 ha k
  exact ⟨C, hC, hbound ν hint h0 (fun _ => le_rfl)⟩

/-- **The moments of the normalized i.i.d. sum** (Talagrand, Eq. (1.122)).  Under the hypotheses
of `iid_sum_moment_expansion`, for every `m ≥ 1` there is `C` such that for all `N > 0`,
`|𝔼 (N⁻¹ ∑_{i<N} f (yᵢ))^m - N^{-m/2} a m σ2^{⌊m/2⌋}| ≤ C N^{-(m+1)/2}`, where
`N^{-1/2}` is written `(√N)⁻¹`. -/
theorem abs_integral_pow_avg_sub_le (hint : ∀ j, Integrable (fun x => f x ^ j) ν)
    (h0 : ∫ x, f x ∂ν = 0) {a : ℕ → ℝ} (ha0 : a 0 = 1) (ha1 : a 1 = 0)
    (ha : ∀ k, a (k + 2) = (k + 1) * a k) {m : ℕ} (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
      |∫ y : Fin N → Ω, ((N : ℝ)⁻¹ * ∑ i, f (y i)) ^ m ∂(Measure.pi fun _ : Fin N => ν) -
        ((Real.sqrt N)⁻¹) ^ m * a m * (∫ x, f x ^ 2 ∂ν) ^ (m / 2)| ≤
      C * ((Real.sqrt N)⁻¹) ^ (m + 1) := by
  obtain ⟨C, hC0, hC⟩ := iid_sum_moment_expansion hint h0 ha0 ha1 ha m
  refine ⟨C * Real.sqrt 2 ^ (m - 1), by positivity, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  set ε : ℝ := (Real.sqrt N)⁻¹ with hε
  have hε2 : ε ^ 2 = (N : ℝ)⁻¹ := by rw [hε, inv_pow, Real.sq_sqrt hNpos.le]
  -- pull the scalar out of the integral
  have e1 : ∫ y : Fin N → Ω, ((N : ℝ)⁻¹ * ∑ i, f (y i)) ^ m ∂(Measure.pi fun _ : Fin N => ν) =
      ((N : ℝ)⁻¹) ^ m * ∫ y : Fin N → Ω, (∑ i, f (y i)) ^ m ∂(Measure.pi fun _ : Fin N => ν) := by
    simp_rw [mul_pow]
    exact integral_const_mul _ _
  -- the reference term, parity by parity
  have e2 : ε ^ m * a m * (∫ x, f x ^ 2 ∂ν) ^ (m / 2) = ((N : ℝ)⁻¹) ^ m *
      (a m * (∫ x, f x ^ 2 ∂ν) ^ (m / 2) * (N : ℝ) ^ (m / 2)) := by
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' m
    · have hj : 2 * j / 2 = j := by omega
      rw [hj, pow_mul, hε2, pow_mul]
      have : ((N : ℝ)⁻¹ ^ 2) ^ j * (N : ℝ) ^ j = ((N : ℝ)⁻¹) ^ j := by
        rw [sq, ← mul_pow, show (N : ℝ)⁻¹ * (N : ℝ)⁻¹ * N = (N : ℝ)⁻¹ by field_simp]
      calc ((N : ℝ)⁻¹) ^ j * a (2 * j) * (∫ x, f x ^ 2 ∂ν) ^ j = a (2 * j) *
            (∫ x, f x ^ 2 ∂ν) ^ j * ((N : ℝ)⁻¹) ^ j := by ring
        _ = _ := by rw [← this]; ring
    · rw [Nat.eq_zero_of_odd_of_two_step_mul ha1 ha ⟨j, rfl⟩]
      simp
  rw [e1, e2, ← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((N : ℝ)⁻¹) ^ m)]
  have hs : Real.sqrt ((N : ℝ) + 1) ≤ Real.sqrt 2 * Real.sqrt N := by
    have h1N : (1 : ℝ) ≤ N := Nat.one_le_cast.2 hN
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hpow : Real.sqrt ((N : ℝ) + 1) ^ (m - 1) ≤
      Real.sqrt 2 ^ (m - 1) * Real.sqrt N ^ (m - 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hs _
  have hfin : ((N : ℝ)⁻¹) ^ m * Real.sqrt N ^ (m - 1) = ε ^ (m + 1) := by
    rw [← hε2, ← pow_mul, show 2 * m = (m + 1) + (m - 1) by omega, pow_add]
    have : ε ^ (m - 1) * Real.sqrt N ^ (m - 1) = 1 := by
      rw [← mul_pow, hε, inv_mul_cancel₀ hsN.ne', one_pow]
    calc ε ^ (m + 1) * ε ^ (m - 1) * Real.sqrt N ^ (m - 1)
        = ε ^ (m + 1) * (ε ^ (m - 1) * Real.sqrt N ^ (m - 1)) := by ring
      _ = _ := by rw [this, mul_one]
  calc ((N : ℝ)⁻¹) ^ m * |∫ y : Fin N → Ω, (∑ i, f (y i)) ^ m ∂(Measure.pi fun _ : Fin N => ν) -
        a m * (∫ x, f x ^ 2 ∂ν) ^ (m / 2) * (N : ℝ) ^ (m / 2)|
      ≤ ((N : ℝ)⁻¹) ^ m * (C * Real.sqrt ((N : ℝ) + 1) ^ (m - 1)) :=
        mul_le_mul_of_nonneg_left (hC N) (by positivity)
    _ ≤ ((N : ℝ)⁻¹) ^ m * (C * (Real.sqrt 2 ^ (m - 1) * Real.sqrt N ^ (m - 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow hC0) (by positivity)
    _ = C * Real.sqrt 2 ^ (m - 1) * (((N : ℝ)⁻¹) ^ m * Real.sqrt N ^ (m - 1)) := by ring
    _ = _ := by rw [hfin]

end Main

end ProbabilityTheory
