/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Data.Nat.Recurrence
public import LeanMachineLearning.ForMathlib.Probability.Moments.IidSumMoments
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.Positivity

/-!
# Elementary estimates for the moment expansion of an i.i.d. sum

Three analytic ingredients of the proof that the `k`-th moment of a centered i.i.d. sum is the
Gaussian one up to a relative error `n^{-1/2}`:

* `Nat.eq_zero_of_odd_of_two_step_mul`: a sequence `a` with `a 1 = 0` and
  `a (k + 2) = (k + 1) a k` (the Gaussian moments) vanishes at odd indices;
* `ProbabilityTheory.pow_succ_sub_pow_sub_mul_le`: `0 ≤ (u + 1)^p - u^p - p u^{p-1} ≤
  p (p - 1) (u + 1)^{p-2}` for `u ≥ 0` (second order Taylor remainder of `u ↦ u^p`);
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

/-- **Second order Taylor remainder of a power:** for `u ≥ 0` and `p ≥ 0`,
`0 ≤ (u + 1)^{p+2} - u^{p+2} - (p + 2) u^{p+1} ≤ (p + 2) (p + 1) (u + 1)^p`. -/
theorem pow_succ_sub_pow_sub_mul_le {u : ℝ} (hu : 0 ≤ u) (p : ℕ) :
    0 ≤ (u + 1) ^ (p + 2) - u ^ (p + 2) - (p + 2 : ℝ) * u ^ (p + 1) ∧
      (u + 1) ^ (p + 2) - u ^ (p + 2) - (p + 2 : ℝ) * u ^ (p + 1) ≤
        (p + 2 : ℝ) * (p + 1 : ℝ) * (u + 1) ^ p := by
  induction p with
  | zero => constructor <;> simp <;> nlinarith
  | succ p ih =>
    obtain ⟨h0, h1⟩ := ih
    have e : (u + 1) ^ (p + 1 + 2) - u ^ (p + 1 + 2) - ((p + 1 : ℕ) + 2 : ℝ) * u ^ (p + 1 + 1) =
        (u + 1) * ((u + 1) ^ (p + 2) - u ^ (p + 2) - (p + 2 : ℝ) * u ^ (p + 1)) +
          (p + 2 : ℝ) * u ^ (p + 1) := by
      push_cast
      ring
    rw [e]
    have hu1 : 0 ≤ u + 1 := by linarith
    have hup : u ^ (p + 1) ≤ (u + 1) ^ (p + 1) := pow_le_pow_left₀ hu (by linarith) _
    refine ⟨by positivity, ?_⟩
    calc (u + 1) * ((u + 1) ^ (p + 2) - u ^ (p + 2) - (p + 2 : ℝ) * u ^ (p + 1)) +
          (p + 2 : ℝ) * u ^ (p + 1)
        ≤ (u + 1) * ((p + 2 : ℝ) * (p + 1 : ℝ) * (u + 1) ^ p) + (p + 2 : ℝ) * (u + 1) ^ (p + 1) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 hu1)
            (mul_le_mul_of_nonneg_left hup (by positivity))
      _ ≤ ((p + 1 : ℕ) + 2 : ℝ) * ((p + 1 : ℕ) + 1 : ℝ) * (u + 1) ^ (p + 1) := by
          push_cast
          have key : (u + 1) * ((p + 2 : ℝ) * (p + 1 : ℝ) * (u + 1) ^ p) =
              (p + 2 : ℝ) * (p + 1 : ℝ) * (u + 1) ^ (p + 1) := by ring
          rw [key]
          nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ p + 2) (pow_nonneg hu1 (p + 1))]

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
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' k
  · obtain ⟨p, rfl⟩ : ∃ p, m = p + 2 := ⟨m - 2, by omega⟩
    refine ⟨|(2 * (p : ℝ) + 3) * a (2 * p + 2)| * σ2 ^ (p + 2) * ((p + 2 : ℝ) * (p + 1 : ℝ)), by
      positivity, fun n => ?_⟩
    have e1 : 2 * (p + 2) - 2 = 2 * p + 2 := by omega
    have e2 : 2 * (p + 2) / 2 = p + 2 := by omega
    have e3 : (2 * p + 2) / 2 = p + 1 := by omega
    have e4 : 2 * (p + 2) - 3 = 2 * p + 1 := by omega
    have hch : ((2 * (p + 2)).choose 2 : ℝ) = (p + 2 : ℝ) * (2 * (p : ℝ) + 3) := by
      have : (2 * (p + 2)).choose 2 = (p + 2) * (2 * p + 3) := by
        rw [Nat.choose_two_right, show 2 * (p + 2) - 1 = 2 * p + 3 by omega]
        exact Nat.div_eq_of_eq_mul_left (by norm_num) (by ring)
      rw [this]
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
  · refine ⟨0, le_rfl, fun n => ?_⟩
    have h1 : a (2 * m + 1) = 0 := Nat.eq_zero_of_odd_of_two_step_mul ha1 ha ⟨m, rfl⟩
    have h2 : a (2 * m + 1 - 2) = 0 := Nat.eq_zero_of_odd_of_two_step_mul ha1 ha ⟨m - 1, by omega⟩
    rw [h1, h2]
    simp

/-- `n^{⌊j/2⌋} ≤ (√(n + 1))^j`. -/
theorem natCast_pow_div_two_le_sqrt_pow (n j : ℕ) :
    (n : ℝ) ^ (j / 2) ≤ Real.sqrt ((n : ℝ) + 1) ^ j := by
  have hs1 := one_le_sqrt_natCast_add_one n
  calc (n : ℝ) ^ (j / 2) ≤ ((n : ℝ) + 1) ^ (j / 2) :=
        pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) _
    _ = Real.sqrt ((n : ℝ) + 1) ^ (2 * (j / 2)) := by
        rw [pow_mul, Real.sq_sqrt (by positivity)]
    _ ≤ Real.sqrt ((n : ℝ) + 1) ^ j := pow_le_pow_right₀ hs1 (Nat.mul_div_le j 2)

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
  obtain ⟨M, hM⟩ : ∃ M : ℕ → ℕ → ℝ, ∀ n j, M n j =
      ∫ y : Fin n → Ω, (∑ i, f (y i)) ^ j ∂(Measure.pi fun _ : Fin n => ν) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : ℕ → ℝ, ∀ j, μ j = ∫ x, f x ^ j ∂ν := ⟨_, fun _ => rfl⟩
  simp only [← hM, ← hμ]
  have hμ0 : μ 0 = 1 := by simp [hμ]
  have hμ1 : μ 1 = 0 := by simpa [hμ] using h0
  have hσ : 0 ≤ μ 2 := by rw [hμ]; exact integral_nonneg fun x => sq_nonneg _
  have hrec : ∀ n j, M (n + 1) j = ∑ i ∈ range (j + 1), (j.choose i : ℝ) * μ i * M n (j - i) :=
    fun n j => by
      rw [hM, integral_pow_sum_pi_succ hint]
      simp only [hM, hμ]
  have hM0 : ∀ n, M n 0 = 1 := fun n => by simp [hM]
  have hMz : ∀ j, 1 ≤ j → M 0 j = 0 := fun j hj => by
    simp [hM, zero_pow (by omega : j ≠ 0)]
  have hM1 : ∀ n, M n 1 = 0 := fun n => by
    induction n with
    | zero => exact hMz 1 le_rfl
    | succ n ih => rw [hrec]; simp [Finset.sum_range_succ, hμ0, hμ1, ih]
  have hrec2 : ∀ n k, 2 ≤ k → M (n + 1) k = M n k + (k.choose 2 : ℝ) * μ 2 * M n (k - 2) +
      ∑ i ∈ Ico 3 (k + 1), (k.choose i : ℝ) * μ i * M n (k - i) := fun n k hk => by
    rw [hrec, ← Finset.sum_range_add_sum_Ico _ (show 3 ≤ k + 1 by omega)]
    simp [Finset.sum_range_succ, hμ0, hμ1, add_assoc]
  have hM2 : ∀ n, M n 2 = n * μ 2 := fun n => by
    induction n with
    | zero => simpa using hMz 2 (by norm_num)
    | succ n ih =>
      rw [hrec2 n 2 le_rfl]
      simp [hM0, ih]
      ring
  have main : ∀ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |M n k - a k * μ 2 ^ (k / 2) * (n : ℝ) ^ (k / 2)| ≤
        C * Real.sqrt ((n : ℝ) + 1) ^ (k - 1) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases lt_or_ge k 3 with hk3 | hk3
      · interval_cases k
        · exact ⟨0, le_rfl, fun n => by simp [hM0, ha0]⟩
        · exact ⟨0, le_rfl, fun n => by simp [hM1, ha1]⟩
        · have h2 : a 2 = 1 := by
            rw [show (2 : ℕ) = 0 + 2 from rfl, ha, ha0]; simp
          exact ⟨0, le_rfl, fun n => by simp [hM2, h2]; ring⟩
      · have hk2 : 2 ≤ k := by omega
        choose! C hC0 hC using ih
        set B : ℝ := ∑ i ∈ range k, (C i + |a i| * |μ 2| ^ (i / 2)) with hB
        have hB0 : 0 ≤ B := Finset.sum_nonneg fun i hi =>
          add_nonneg (hC0 i (Finset.mem_range.1 hi)) (by positivity)
        have hpri : ∀ i < k, ∀ n : ℕ, |M n i| ≤ B * Real.sqrt ((n : ℝ) + 1) ^ i := by
          intro i hi n
          have hs1 := one_le_sqrt_natCast_add_one n
          have h1 := hC i hi n
          have h2 : Real.sqrt ((n : ℝ) + 1) ^ (i - 1) ≤ Real.sqrt ((n : ℝ) + 1) ^ i :=
            pow_le_pow_right₀ hs1 (Nat.sub_le i 1)
          have h3 := natCast_pow_div_two_le_sqrt_pow n i
          have hle : C i + |a i| * |μ 2| ^ (i / 2) ≤ B :=
            Finset.single_le_sum (f := fun i => C i + |a i| * |μ 2| ^ (i / 2))
              (fun j hj => add_nonneg (hC0 j (Finset.mem_range.1 hj)) (by positivity))
              (Finset.mem_range.2 hi)
          calc |M n i| = |(M n i - a i * μ 2 ^ (i / 2) * (n : ℝ) ^ (i / 2)) +
                a i * μ 2 ^ (i / 2) * (n : ℝ) ^ (i / 2)| := by ring_nf
            _ ≤ |M n i - a i * μ 2 ^ (i / 2) * (n : ℝ) ^ (i / 2)| +
                |a i * μ 2 ^ (i / 2) * (n : ℝ) ^ (i / 2)| := abs_add_le _ _
            _ ≤ C i * Real.sqrt ((n : ℝ) + 1) ^ i + |a i| * |μ 2| ^ (i / 2) *
                Real.sqrt ((n : ℝ) + 1) ^ i := by
                refine add_le_add (h1.trans (mul_le_mul_of_nonneg_left h2 (hC0 i hi))) ?_
                rw [abs_mul, abs_mul, abs_pow, abs_pow, Nat.abs_cast]
                exact mul_le_mul_of_nonneg_left h3 (by positivity)
            _ = (C i + |a i| * |μ 2| ^ (i / 2)) * Real.sqrt ((n : ℝ) + 1) ^ i := by ring
            _ ≤ B * Real.sqrt ((n : ℝ) + 1) ^ i :=
                mul_le_mul_of_nonneg_right hle (by positivity)
        obtain ⟨cT, hcT0, hT⟩ := exists_abs_cancellation_le ha1 ha hσ hk3
        set cR : ℝ := ∑ i ∈ Ico 3 (k + 1), (k.choose i : ℝ) * |μ i| * B with hcR
        have hcR0 : 0 ≤ cR := Finset.sum_nonneg fun i _ => by positivity
        set c : ℝ := (k.choose 2 : ℝ) * |μ 2| * C (k - 2) + cR + cT with hc
        have hCk2 : 0 ≤ C (k - 2) := hC0 _ (by omega)
        have hc0 : 0 ≤ c := by positivity
        have hΔ : ∀ n : ℕ, |(M (n + 1) k - a k * μ 2 ^ (k / 2) * (((n + 1 : ℕ) : ℝ)) ^ (k / 2)) -
            (M n k - a k * μ 2 ^ (k / 2) * (n : ℝ) ^ (k / 2))| ≤
            c * Real.sqrt ((n : ℝ) + 1) ^ (k - 3) := by
          intro n
          have hs1 := one_le_sqrt_natCast_add_one n
          set R := ∑ i ∈ Ico 3 (k + 1), (k.choose i : ℝ) * μ i * M n (k - i) with hR
          have hRb : |R| ≤ cR * Real.sqrt ((n : ℝ) + 1) ^ (k - 3) := by
            rw [hR, hcR, Finset.sum_mul]
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
            have hi3 : 3 ≤ i := (Finset.mem_Ico.1 hi).1
            have hik : i < k + 1 := (Finset.mem_Ico.1 hi).2
            have h1 := hpri (k - i) (by omega) n
            have h2 : Real.sqrt ((n : ℝ) + 1) ^ (k - i) ≤ Real.sqrt ((n : ℝ) + 1) ^ (k - 3) :=
              pow_le_pow_right₀ hs1 (by omega)
            rw [abs_mul, abs_mul, Nat.abs_cast]
            calc (k.choose i : ℝ) * |μ i| * |M n (k - i)|
                ≤ (k.choose i : ℝ) * |μ i| * (B * Real.sqrt ((n : ℝ) + 1) ^ (k - 3)) :=
                  mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left h2 hB0))
                    (by positivity)
              _ = _ := by ring
          have hEb : (k.choose 2 : ℝ) * |μ 2| * |M n (k - 2) - a (k - 2) * μ 2 ^ ((k - 2) / 2) *
              (n : ℝ) ^ ((k - 2) / 2)| ≤ (k.choose 2 : ℝ) * |μ 2| * C (k - 2) *
                Real.sqrt ((n : ℝ) + 1) ^ (k - 3) := by
            have := hC (k - 2) (by omega) n
            rw [show k - 2 - 1 = k - 3 by omega] at this
            calc _ ≤ (k.choose 2 : ℝ) * |μ 2| * (C (k - 2) * Real.sqrt ((n : ℝ) + 1) ^ (k - 3)) :=
                  mul_le_mul_of_nonneg_left this (by positivity)
              _ = _ := by ring
          have hid : (M (n + 1) k - a k * μ 2 ^ (k / 2) * (((n + 1 : ℕ) : ℝ)) ^ (k / 2)) -
              (M n k - a k * μ 2 ^ (k / 2) * (n : ℝ) ^ (k / 2)) =
              (k.choose 2 : ℝ) * μ 2 * (M n (k - 2) - a (k - 2) * μ 2 ^ ((k - 2) / 2) *
                (n : ℝ) ^ ((k - 2) / 2)) + R +
              ((k.choose 2 : ℝ) * μ 2 * (a (k - 2) * μ 2 ^ ((k - 2) / 2) *
                (n : ℝ) ^ ((k - 2) / 2)) -
                (a k * μ 2 ^ (k / 2) * (((n + 1 : ℕ) : ℝ)) ^ (k / 2) -
                  a k * μ 2 ^ (k / 2) * (n : ℝ) ^ (k / 2))) := by
            rw [hrec2 n k hk2]
            ring
          rw [hid]
          have hT' := hT n
          calc _ ≤ |(k.choose 2 : ℝ) * μ 2 * (M n (k - 2) - a (k - 2) * μ 2 ^ ((k - 2) / 2) *
                (n : ℝ) ^ ((k - 2) / 2)) + R| + |(k.choose 2 : ℝ) * μ 2 * (a (k - 2) *
                  μ 2 ^ ((k - 2) / 2) * (n : ℝ) ^ ((k - 2) / 2)) -
                    (a k * μ 2 ^ (k / 2) * (((n + 1 : ℕ) : ℝ)) ^ (k / 2) -
                      a k * μ 2 ^ (k / 2) * (n : ℝ) ^ (k / 2))| := abs_add_le _ _
            _ ≤ (|(k.choose 2 : ℝ) * μ 2 * (M n (k - 2) - a (k - 2) * μ 2 ^ ((k - 2) / 2) *
                (n : ℝ) ^ ((k - 2) / 2))| + |R|) + cT * Real.sqrt ((n : ℝ) + 1) ^ (k - 3) :=
                add_le_add (abs_add_le _ _) hT'
            _ ≤ _ := by
                rw [abs_mul, abs_mul, Nat.abs_cast] at *
                nlinarith [hEb, hRb]
        have he0 : M 0 k - a k * μ 2 ^ (k / 2) * ((0 : ℕ) : ℝ) ^ (k / 2) = 0 := by
          rw [hMz k (by omega), Nat.cast_zero, zero_pow (by omega : k / 2 ≠ 0)]
          ring
        refine ⟨c, hc0, fun n => ?_⟩
        have := abs_le_of_abs_sub_le_sqrt_pow (e := fun n : ℕ => M n k - a k * μ 2 ^ (k / 2) *
          (n : ℝ) ^ (k / 2)) he0 hc0 hΔ n
        rwa [show k - 3 + 2 = k - 1 by omega] at this
  simpa only [hM, hμ] using main k

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
