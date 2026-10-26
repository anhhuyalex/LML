/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.ConjExponents
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Elementary estimates for powers of a sum

* `add_pow_le_mul_pow_add_mul_pow`: a weighted (Young type) form of `add_pow_le`,
  `(a + b)^n ≤ (1 + θ)^(n-1) a^n + (1 + θ⁻¹)^(n-1) b^n`.
* `pow_add_sub_pow_sub_le`: for an odd exponent the symmetric difference of `a ± x` is controlled
  by `n x (|a| + x)^(n-1)`.
* `prod_abs_le_sum_pow`: the crude arithmetic-geometric inequality `∏ |a_j| ≤ ∑ |a_j|^n` for `n`
  numbers.
-/

@[expose] public section

/-- **Weighted power inequality.** For `a, b ≥ 0`, `θ > 0` and `n ≥ 1`,
`(a + b)^n ≤ (1 + θ)^(n-1) a^n + (1 + θ⁻¹)^(n-1) b^n`. Convexity of `t ↦ t^n` applied with the
weights `1/(1+θ)` and `θ/(1+θ)`; `θ = 1` recovers `add_pow_le`. -/
theorem add_pow_le_mul_pow_add_mul_pow {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hθ : 0 < θ)
    {n : ℕ} (hn : 1 ≤ n) :
    (a + b) ^ n ≤ (1 + θ) ^ (n - 1) * a ^ n + (1 + θ⁻¹) ^ (n - 1) * b ^ n := by
  have h1 : (0 : ℝ) < 1 + θ := by linarith
  have hw1 : 0 ≤ 1 / (1 + θ) := by positivity
  have hw2 : 0 ≤ θ / (1 + θ) := by positivity
  have hw : 1 / (1 + θ) + θ / (1 + θ) = 1 := by field_simp
  have hconv := (convexOn_pow n).2 (x := (1 + θ) * a) (y := (1 + θ) / θ * b)
    (Set.mem_Ici.2 (by positivity)) (Set.mem_Ici.2 (by positivity)) hw1 hw2 hw
  simp only [smul_eq_mul] at hconv
  have hsum : 1 / (1 + θ) * ((1 + θ) * a) + θ / (1 + θ) * ((1 + θ) / θ * b) = a + b := by
    field_simp
  rw [hsum] at hconv
  refine hconv.trans (le_of_eq ?_)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel, mul_pow, div_pow, one_div]
  have hθ' : θ ≠ 0 := hθ.ne'
  have h1' : (1 + θ) ≠ 0 := h1.ne'
  have e : (1 + θ⁻¹) = (1 + θ) / θ := by
    field_simp
    ring
  rw [e, div_pow]
  field_simp
  ring_nf

/-- For an odd exponent `n` and `x ≥ 0`, half the difference `(a + x)^n - (a - x)^n` is
nonnegative and at most `n x (|a| + x)^(n-1)`. -/
theorem pow_add_sub_pow_sub_le {n : ℕ} (hn : Odd n) (a : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ ((a + x) ^ n - (a - x) ^ n) / 2 ∧
      ((a + x) ^ n - (a - x) ^ n) / 2 ≤ n * x * (|a| + x) ^ (n - 1) := by
  refine ⟨?_, ?_⟩
  · have : (a - x) ^ n ≤ (a + x) ^ n := hn.pow_le_pow.2 (by linarith)
    linarith
  · have h := abs_pow_sub_pow_le (a + x) (a - x) n
    have hmax : max |a + x| |a - x| ≤ |a| + x := max_le
      ((abs_add_le _ _).trans (by rw [abs_of_nonneg hx]))
      ((abs_sub _ _).trans (by rw [abs_of_nonneg hx]))
    have hd : |a + x - (a - x)| = 2 * x := by
      rw [show a + x - (a - x) = 2 * x by ring, abs_of_nonneg (by linarith)]
    rw [hd] at h
    have h2 : ((a + x) ^ n - (a - x) ^ n) ≤ 2 * x * n * (|a| + x) ^ (n - 1) :=
      (le_abs_self _).trans (h.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hmax _) (by positivity)))
    linarith

/-- **Hölder absorption.** If `Z ≤ c^p V` for a Hölder conjugate pair `(p, r)` and `c, V, Z ≥ 0`,
then `Z^(1/p) V^(1/r) ≤ c V`: the powers of `V` recombine to `V^(1/p + 1/r) = V`. -/
theorem rpow_mul_rpow_le_mul_of_le_rpow_mul {p r : ℝ} (hpr : p.HolderConjugate r) {c V Z : ℝ}
    (hc : 0 ≤ c) (hV : 0 ≤ V) (hZ : 0 ≤ Z) (hZV : Z ≤ c ^ p * V) :
    Z ^ (1 / p) * V ^ (1 / r) ≤ c * V := by
  have h1 : Z ^ (1 / p) ≤ (c ^ p * V) ^ (1 / p) :=
    Real.rpow_le_rpow hZ hZV (by have := hpr.one_div_pos; linarith)
  have h2 : (c ^ p * V) ^ (1 / p) = c * V ^ (1 / p) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hc _) hV, ← Real.rpow_mul hc,
      mul_one_div_cancel hpr.ne_zero, Real.rpow_one]
  have h3 : V ^ (1 / p) * V ^ (1 / r) = V := by
    by_cases hV0 : V = 0
    · subst hV0
      rw [Real.zero_rpow hpr.one_div_ne_zero, zero_mul]
    · rw [← Real.rpow_add (lt_of_le_of_ne hV (Ne.symm hV0)),
        show 1 / p + 1 / r = 1 by simpa [one_div] using hpr.inv_add_inv_eq_one, Real.rpow_one]
  calc Z ^ (1 / p) * V ^ (1 / r) ≤ c * V ^ (1 / p) * V ^ (1 / r) :=
        mul_le_mul_of_nonneg_right (h1.trans_eq h2) (Real.rpow_nonneg hV _)
    _ = c * V := by rw [mul_assoc, h3]

/-- `exp (1/2) ≤ 2`. -/
theorem Real.exp_half_le_two : Real.exp (1 / 2) ≤ 2 := by
  have h : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h1 := Real.exp_one_lt_d9
  nlinarith [Real.exp_pos (1 / 2)]

/-- **Even power of a perturbed absolute value.** For `k ≥ 1` and `b ≥ 0`,
`(|a| + b)^(2k) ≤ 2 a^(2k) + (1 + 4k)^(2k-1) b^(2k)`, the case `θ = 1/(4k)` of
`add_pow_le_mul_pow_add_mul_pow`. -/
theorem abs_add_pow_two_mul_le {k : ℕ} (hk : 1 ≤ k) (a : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    (|a| + b) ^ (2 * k) ≤ 2 * a ^ (2 * k) + (1 + 4 * (k : ℝ)) ^ (2 * k - 1) * b ^ (2 * k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have h := add_pow_le_mul_pow_add_mul_pow (abs_nonneg a) hb
    (θ := 1 / (4 * (k : ℝ))) (by positivity) (n := 2 * k) (by omega)
  have hinv : (1 / (4 * (k : ℝ)))⁻¹ = 4 * k := by field_simp
  have hpow : 0 ≤ a ^ (2 * k) := Even.pow_nonneg ⟨k, by ring⟩ _
  rw [hinv, Even.pow_abs ⟨k, by ring⟩] at h
  refine h.trans ?_
  have hc : (1 + 1 / (4 * (k : ℝ))) ^ (2 * k - 1) ≤ 2 := by
    calc (1 + 1 / (4 * (k : ℝ))) ^ (2 * k - 1) ≤ Real.exp (1 / (4 * k)) ^ (2 * k - 1) :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (1 / (4 * (k : ℝ)))]) _
      _ = Real.exp (((2 * k - 1 : ℕ) : ℝ) * (1 / (4 * k))) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (1 / 2) := by
          refine Real.exp_le_exp.2 ?_
          rw [Nat.cast_sub (by omega)]
          push_cast
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
      _ ≤ 2 := Real.exp_half_le_two
  nlinarith [mul_le_mul_of_nonneg_right hc hpow]

/-- The pair `((m + 1) / m, m + 1)` is Hölder conjugate for `m > 0`. -/
theorem Real.HolderConjugate.succ_div_self {m : ℝ} (hm : 0 < m) :
    ((m + 1) / m).HolderConjugate (m + 1) := by
  rw [Real.holderConjugate_iff]
  refine ⟨by rw [lt_div_iff₀ hm]; linarith, ?_⟩
  field_simp

/-- Linear-to-exponential domination: `A + B ≤ (A + 1) * exp B` for `A, B ≥ 0`. -/
theorem Real.add_le_add_one_mul_exp {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    A + B ≤ (A + 1) * Real.exp B := by
  nlinarith [mul_le_mul_of_nonneg_left (Real.one_le_exp hB) hA, Real.add_one_le_exp B]

/-- Weighted AM-GM: `a * b ≤ (t a² + t⁻¹ b²) / 2` for `t > 0`. -/
theorem mul_le_half_mul_add_inv_mul {t a b : ℝ} (ht : 0 < t) :
    a * b ≤ (t * a ^ 2 + t⁻¹ * b ^ 2) / 2 := by
  have hsq : 0 ≤ (t * a - b) ^ 2 := sq_nonneg _
  have ht2 : 0 < 2 * t := by linarith
  have : 0 ≤ (t * a - b) ^ 2 / (2 * t) := div_nonneg hsq ht2.le
  calc a * b = (t * a ^ 2 + t⁻¹ * b ^ 2) / 2 - (t * a - b) ^ 2 / (2 * t) := by
        field_simp; ring
    _ ≤ (t * a ^ 2 + t⁻¹ * b ^ 2) / 2 := by linarith

/-- `(x + y)^(2k) ≤ 2^(2k-1) (x^(2k) + y^(2k))`. -/
theorem add_pow_two_mul_le {k : ℕ} (hk : 1 ≤ k) (x y : ℝ) :
    (x + y) ^ (2 * k) ≤ 2 ^ (2 * k - 1) * (x ^ (2 * k) + y ^ (2 * k)) := by
  have h_even : Even (2 * k) := ⟨k, by ring⟩
  rw [← Even.pow_abs h_even (x + y)]
  have h_le : |x + y| ≤ |x| + |y| := abs_add_le x y
  have h_pow := pow_le_pow_left₀ (abs_nonneg _) h_le (2 * k)
  refine h_pow.trans ?_
  have h_add := add_pow_le_mul_pow_add_mul_pow (abs_nonneg x) (abs_nonneg y)
    zero_lt_one (n := 2 * k) (by omega)
  have h1 : (1 : ℝ) + 1 = 2 := by norm_num
  have h2 : (1 : ℝ) + 1⁻¹ = 2 := by norm_num
  rw [h1, h2] at h_add
  rw [Even.pow_abs h_even x, Even.pow_abs h_even y] at h_add
  linarith

/-- `(x₁ + x₂ + x₃ + x₄)^(2k) ≤ 4^(2k-1) (x₁^(2k) + x₂^(2k) + x₃^(2k) + x₄^(2k))`. -/
theorem add_pow_four_two_mul_le {k : ℕ} (hk : 1 ≤ k) (x₁ x₂ x₃ x₄ : ℝ) :
    (x₁ + x₂ + x₃ + x₄) ^ (2 * k) ≤
      4 ^ (2 * k - 1) * (x₁ ^ (2 * k) + x₂ ^ (2 * k) + x₃ ^ (2 * k) + x₄ ^ (2 * k)) := by
  have h1 : (x₁ + x₂ + x₃ + x₄) = (x₁ + x₂) + (x₃ + x₄) := by ring
  rw [h1]
  refine (add_pow_two_mul_le hk (x₁ + x₂) (x₃ + x₄)).trans ?_
  have h2 := add_pow_two_mul_le hk x₁ x₂
  have h3 := add_pow_two_mul_le hk x₃ x₄
  have h22 : (2 : ℝ) ^ (2 * k - 1) * 2 ^ (2 * k - 1) = 4 ^ (2 * k - 1) := by
    rw [← mul_pow, show (2 : ℝ) * 2 = 4 by norm_num]
  calc 2 ^ (2 * k - 1) * ((x₁ + x₂) ^ (2 * k) + (x₃ + x₄) ^ (2 * k))
    _ ≤ 2 ^ (2 * k - 1) * (2 ^ (2 * k - 1) * (x₁ ^ (2 * k) + x₂ ^ (2 * k)) +
        2 ^ (2 * k - 1) * (x₃ ^ (2 * k) + x₄ ^ (2 * k))) :=
      mul_le_mul_of_nonneg_left (add_le_add h2 h3) (by positivity)
    _ = (2 ^ (2 * k - 1) * 2 ^ (2 * k - 1)) *
        (x₁ ^ (2 * k) + x₂ ^ (2 * k) + x₃ ^ (2 * k) + x₄ ^ (2 * k)) := by ring
    _ = 4 ^ (2 * k - 1) * (x₁ ^ (2 * k) + x₂ ^ (2 * k) + x₃ ^ (2 * k) + x₄ ^ (2 * k)) := by rw [h22]

/-- Passing from `N` to `N + 1` costs at most a factor `2 ^ k`:
`K / N ^ k ≤ 2 ^ k * K / (N + 1) ^ k` for `N ≥ 1` and `K ≥ 0`. -/
theorem div_pow_le_two_pow_mul_div_succ_pow {N : ℕ} (hN : 0 < N) (k : ℕ) {K : ℝ} (hK : 0 ≤ K) :
    K / (N : ℝ) ^ k ≤ 2 ^ k * K / ((N : ℝ) + 1) ^ k := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : ((N : ℝ) + 1) ^ k ≤ 2 ^ k * (N : ℝ) ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) k
  calc K * ((N : ℝ) + 1) ^ k ≤ K * (2 ^ k * (N : ℝ) ^ k) := mul_le_mul_of_nonneg_left h2 hK
    _ = 2 ^ k * K * (N : ℝ) ^ k := by ring

/-- Crude arithmetic-geometric mean inequality: the product of `n = |s|` absolute values is at most
the sum of their `n`-th powers (each factor is at most the largest one). -/
theorem prod_abs_le_sum_pow {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (a : ι → ℝ) :
    ∏ j ∈ s, |a j| ≤ ∑ j ∈ s, |a j| ^ s.card := by
  obtain ⟨j₀, hj₀s, hj₀⟩ := Finset.exists_max_image s (fun j => |a j|) hs
  calc ∏ j ∈ s, |a j| ≤ ∏ _j ∈ s, |a j₀| :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j hj => hj₀ j hj
    _ = |a j₀| ^ s.card := by simp
    _ ≤ ∑ j ∈ s, |a j| ^ s.card :=
        Finset.single_le_sum (f := fun j => |a j| ^ s.card) (fun j _ => by positivity) hj₀s
