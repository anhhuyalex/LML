/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.Taylor

/-!
# Taylor interpolation and remainder estimates

This file provides polynomial vanishing and remainder estimates for smooth functions on an interval
whose lower-order derivatives vanish at the basepoint.

## Main declarations

* `taylor_eval_zero_eq_remainder`: for a $C^{n+1}$ function $f$ on $\mathbb{R}$ with
  $f^{(k)}(0) = 0$ for $k \le n$, there exists $x' \in (0, 1)$ with $f(1) = f^{(n+1)}(x') / (n+1)!$.
* `abs_le_of_forall_deriv_zero_and_bound`: under the same condition, $|f(1)| \le M / (n+1)!$
  whenever $|f^{(n+1)}| \le M$ on $(0, 1)$.
-/

@[expose] public section

open Set

/-- If $f : \mathbb{R} \to \mathbb{R}$ is $C^{n+1}$ and all derivatives up to order $n$ vanish at $0$,
then $f(1) = f^{(n+1)}(x') / (n+1)!$ for some $x' \in (0, 1)$. -/
theorem taylor_eval_zero_eq_remainder {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiff ℝ (n + 1) f)
    (h_zero : ∀ k ≤ n, iteratedDeriv k f 0 = 0) :
    ∃ x' ∈ Ioo (0 : ℝ) 1, f 1 = iteratedDeriv (n + 1) f x' / (Nat.factorial (n + 1) : ℝ) := by
  have hne : (0 : ℝ) ≠ 1 := by norm_num
  have hu : uIcc (0 : ℝ) 1 = Icc 0 1 := by rw [uIcc_of_le zero_le_one]
  have hu_oo : uIoo (0 : ℝ) 1 = Ioo 0 1 := by rw [uIoo_of_le zero_le_one]
  have hf' : ContDiffOn ℝ (n + 1) f (uIcc 0 1) := hf.contDiffOn
  obtain ⟨x', hx', h_taylor⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hne hf'
  rw [hu_oo] at hx'
  have h_poly : taylorWithinEval f n (uIcc 0 1) 0 1 = 0 := by
    rw [taylor_within_apply]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_range] at hk
    have hu_diff : UniqueDiffOn ℝ (uIcc (0 : ℝ) 1) := uniqueDiffOn_uIcc hne
    have hkn_nat : k ≤ n + 1 := Nat.le_of_lt hk
    have hkn : (k : WithTop ℕ∞) ≤ (n + 1 : ℕ) := Nat.cast_le.mpr hkn_nat
    rw [iteratedDerivWithin_eq_iteratedDeriv hu_diff (hf.of_le hkn).contDiffAt]
    · rw [h_zero k (Nat.le_of_lt_succ hk), smul_zero]
    · rw [hu]; exact ⟨le_rfl, zero_le_one⟩
  rw [h_poly, sub_zero, sub_zero, one_pow, mul_one] at h_taylor
  exact ⟨x', hx', h_taylor⟩

/-- If $f : \mathbb{R} \to \mathbb{R}$ is $C^{n+1}$, all derivatives up to order $n$ vanish at $0$,
and $|f^{(n+1)}| \le M$ on $(0, 1)$, then $|f(1)| \le M / (n+1)!$. -/
theorem abs_le_of_forall_deriv_zero_and_bound {f : ℝ → ℝ} {n : ℕ} {M : ℝ}
    (hf : ContDiff ℝ (n + 1) f)
    (h_zero : ∀ k ≤ n, iteratedDeriv k f 0 = 0)
    (h_bound : ∀ x ∈ Ioo (0 : ℝ) 1, |iteratedDeriv (n + 1) f x| ≤ M) :
    |f 1| ≤ M / (Nat.factorial (n + 1) : ℝ) := by
  obtain ⟨x', hx', heq⟩ := taylor_eval_zero_eq_remainder hf h_zero
  rw [heq, abs_div, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (h_bound x' hx') (by positivity)
