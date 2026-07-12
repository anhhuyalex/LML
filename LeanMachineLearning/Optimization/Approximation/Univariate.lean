/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Approximation.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Univariate Lipschitz approximation (folklore construction)

This file formalizes Proposition 2.1 from the deep learning theory notes:
a ρ-Lipschitz function on [0,1] can be approximated to accuracy ε by a
single-hidden-layer threshold network with ⌈ρ/ε⌉ nodes.

## Main results

* `stepApprox` : the step-function approximant constructed from breakpoints bᵢ = iε/ρ
* `stepApprox_mem_FunctionClass` : the approximant lies in OneHiddenLayer.FunctionClass
* `stepApprox_error` : sup-norm error bound ≤ ε on [0,1]

-/

@[expose] public section

open Real Finset

namespace Approximation.Univariate

variable {g : ℝ → ℝ} {ρ ε : ℝ}

/-! ### Breakpoints and coefficients -/

/-- Number of steps: m = ⌈ρ/ε⌉. -/
noncomputable def numSteps (ρ ε : ℝ) : ℕ := ⌈ρ / ε⌉₊

/-- Breakpoints bᵢ = iε/ρ for i = 0, ..., m-1. -/
noncomputable def breakpoint (ρ ε : ℝ) (i : ℕ) : ℝ := i * ε / ρ

/-- Coefficients: a₀ = g(0), aᵢ = g(bᵢ) - g(bᵢ₋₁) for i ≥ 1. -/
noncomputable def coeff (g : ℝ → ℝ) (ρ ε : ℝ) : ℕ → ℝ
  | 0     => g 0
  | (i+1) => g (breakpoint ρ ε (i+1)) - g (breakpoint ρ ε i)

/-! ### The step-function approximant -/

/-- The step-function approximant:
  f_ε(x) = ∑_{i=0}^{m-1} aᵢ · 1[x ≥ bᵢ] -/
noncomputable def stepApprox (g : ℝ → ℝ) (ρ ε : ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ range (numSteps ρ ε),
    coeff g ρ ε i * thresholdActivation (x - breakpoint ρ ε i)

/-- The step-function approximant lies in the threshold network function class. -/
theorem stepApprox_mem_FunctionClass (_hρ : 0 < ρ) (_hε : 0 < ε) :
    (fun (x : EuclideanSpace ℝ (Fin 1))
      => stepApprox g ρ ε (x 0)) ∈
        OneHiddenLayer.FunctionClass thresholdActivation 1 (numSteps ρ ε) := by
  simp only [OneHiddenLayer.FunctionClass, Set.mem_setOf_eq]
  let net : OneHiddenLayer.Network thresholdActivation 1 (numSteps ρ ε) :=
    { weights := fun i => (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => 1)
      biases  := fun i => -(breakpoint ρ ε i.val)
      coeffs  := fun i => coeff g ρ ε i.val }
  exact ⟨net, by
    ext x
    simp only [OneHiddenLayer.Network.eval, stepApprox, thresholdActivation]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp only [net]
    have eq_sum : (∑ j : Fin 1, ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => 1) : Fin 1 → ℝ) j * (x : Fin 1 → ℝ) j) = (x : Fin 1 → ℝ) 0 := by
      change (∑ j : Fin 1, (1 : ℝ) * (x : Fin 1 → ℝ) j) = (x : Fin 1 → ℝ) 0
      rw [Fin.sum_univ_one]
      ring
    rw [eq_sum]
    have H2 : (x : Fin 1 → ℝ) 0 - breakpoint ρ ε ↑i = (x : Fin 1 → ℝ) 0 + -breakpoint ρ ε ↑i := by ring
    rw [H2]
  ⟩

/-! ### Error bound -/

/-- Telescoping: ∑_{i=0}^k aᵢ = g(b_k). -/
lemma sum_coeff_eq (g : ℝ → ℝ) (ρ ε : ℝ) (k : ℕ) :
    ∑ i ∈ range (k + 1), coeff g ρ ε i = g (breakpoint ρ ε k) := by
  induction k with
  | zero => simp [coeff, breakpoint]
  | succ k ih =>
    rw [sum_range_succ, ih, coeff]
    ring

/-! ### Helper lemmas for the error bound

The proof of `stepApprox_error` is broken into four independent pieces:

* `numSteps_pos` : the number of steps `m = ⌈ρ/ε⌉` is positive.
* `breakpoint_le_of_le` / `lt_breakpoint_of_lt` : clearing the denominator `ρ`
  translates the real bound `↑i ≤ xρ/ε` (resp. `xρ/ε < ↑i`) into `bᵢ ≤ x`
  (resp. `x < bᵢ`).  These place `x` relative to the grid.
* `stepApprox_collapse` : the purely combinatorial fact that, once `x` sits between
  `b_k` and the next occupied breakpoint, the network output telescopes to `g(b_k)`.
* `abs_g_breakpoint_sub_le` : the Lipschitz estimate `|g(b_k) - g(x)| ≤ ε`.
-/

/-- The number of steps `⌈ρ/ε⌉` is positive when `ρ, ε > 0`. -/
lemma numSteps_pos (hρ : 0 < ρ) (hε : 0 < ε) : 0 < numSteps ρ ε :=
  Nat.ceil_pos.mpr (div_pos hρ hε)

/-- If `↑i ≤ x·ρ/ε` then the `i`-th breakpoint lies weakly left of `x`. -/
lemma breakpoint_le_of_le (hρ : 0 < ρ) (hε : 0 < ε) {i : ℕ} {x : ℝ}
    (hi : (i : ℝ) ≤ x * ρ / ε) : breakpoint ρ ε i ≤ x := by
  rw [breakpoint, div_le_iff₀ hρ]
  rw [le_div_iff₀ hε] at hi
  linarith

/-- If `x·ρ/ε < ↑i` then `x` lies strictly left of the `i`-th breakpoint. -/
lemma lt_breakpoint_of_lt (hρ : 0 < ρ) (hε : 0 < ε) {i : ℕ} {x : ℝ}
    (hi : x * ρ / ε < (i : ℝ)) : x < breakpoint ρ ε i := by
  rw [breakpoint, lt_div_iff₀ hρ]
  rw [div_lt_iff₀ hε] at hi
  linarith

/-- **Telescoping collapse.**  If `k + 1 ≤ m`, every breakpoint `bᵢ` with `i ≤ k`
is `≤ x`, and every occupied breakpoint `bᵢ` with `k < i < m` is `> x`, then the
network output equals `g(b_k)`.  This is the "`f` is constant on `[b_k, x]`" step. -/
lemma stepApprox_collapse (g : ℝ → ℝ) (ρ ε x : ℝ) {k : ℕ}
    (hk : k + 1 ≤ numSteps ρ ε)
    (hle : ∀ i ≤ k, breakpoint ρ ε i ≤ x)
    (hgt : ∀ i, k < i → i < numSteps ρ ε → x < breakpoint ρ ε i) :
    stepApprox g ρ ε x = g (breakpoint ρ ε k) := by
  have hsub : Finset.range (k + 1) ⊆ Finset.range (numSteps ρ ε) :=
    Finset.range_subset_range.mpr hk
  -- Terms with index > k vanish because `x < bᵢ` forces the threshold to `0`.
  have hzero : ∀ i ∈ Finset.range (numSteps ρ ε), i ∉ Finset.range (k + 1) →
      coeff g ρ ε i * thresholdActivation (x - breakpoint ρ ε i) = 0 := by
    intro i hi hni
    rw [Finset.mem_range] at hi
    rw [Finset.mem_range, not_lt] at hni
    have hlt : x < breakpoint ρ ε i := hgt i (by omega) hi
    have hcond : ¬ (x - breakpoint ρ ε i ≥ 0) := by
      simp only [ge_iff_le, not_le]; linarith
    simp only [thresholdActivation]
    rw [if_neg hcond, mul_zero]
  -- Terms with index ≤ k keep coefficient `aᵢ` because `bᵢ ≤ x` forces threshold `1`.
  have hone : ∀ i ∈ Finset.range (k + 1),
      coeff g ρ ε i * thresholdActivation (x - breakpoint ρ ε i) = coeff g ρ ε i := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hbi : breakpoint ρ ε i ≤ x := hle i (by omega)
    have hcond : x - breakpoint ρ ε i ≥ 0 := by simp only [ge_iff_le]; linarith
    simp only [thresholdActivation]
    rw [if_pos hcond, mul_one]
  rw [stepApprox, ← sum_coeff_eq g ρ ε k, ← Finset.sum_subset hsub hzero]
  exact Finset.sum_congr rfl hone

/-- **Lipschitz estimate.**  If `b_k ≤ x` and `x·ρ ≤ (k+1)·ε` (i.e. `x` is within one
grid cell of `b_k`), then `|g(b_k) - g(x)| ≤ ε`. -/
lemma abs_g_breakpoint_sub_le (hg : LipschitzWith ρ.toNNReal g) (hρ : 0 < ρ)
    {k : ℕ} {x : ℝ} (hle : breakpoint ρ ε k ≤ x) (hub : x * ρ ≤ ((k : ℝ) + 1) * ε) :
    |g (breakpoint ρ ε k) - g x| ≤ ε := by
  have hdist := hg.dist_le_mul (breakpoint ρ ε k) x
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal ρ hρ.le] at hdist
  rw [abs_of_nonpos (by linarith : breakpoint ρ ε k - x ≤ 0)] at hdist
  have hcancel : ρ * breakpoint ρ ε k = (k : ℝ) * ε := by
    rw [breakpoint]; field_simp
  calc |g (breakpoint ρ ε k) - g x|
      ≤ ρ * -(breakpoint ρ ε k - x) := hdist
    _ = x * ρ - ρ * breakpoint ρ ε k := by ring
    _ = x * ρ - (k : ℝ) * ε := by rw [hcancel]
    _ ≤ ε := by nlinarith [hub]

/-- Main approximation error bound: sup_{x ∈ [0,1]} |f_ε(x) - g(x)| ≤ ε. -/
theorem stepApprox_error (hg : LipschitzWith ρ.toNNReal g) (hρ : 0 < ρ) (hε : 0 < ε)
    (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |stepApprox g ρ ε x - g x| ≤ ε := by
  obtain ⟨hx0, hx1⟩ := Set.mem_Icc.mp hx
  set m : ℕ := numSteps ρ ε with hm_def
  have hm_pos : 0 < m := numSteps_pos hρ hε
  -- The grid index containing `x`, capped so it stays in `range m`.
  set n : ℕ := ⌊x * ρ / ε⌋₊ with hn_def
  set k : ℕ := min n (m - 1) with hk_def
  have ht0 : 0 ≤ x * ρ / ε := div_nonneg (mul_nonneg hx0 hρ.le) hε.le
  -- `↑k ≤ xρ/ε`, so every breakpoint up to `k` is left of `x`.
  have hkreal : (k : ℝ) ≤ x * ρ / ε :=
    le_trans (by exact_mod_cast (by omega : k ≤ n)) (Nat.floor_le ht0)
  have hle : ∀ i ≤ k, breakpoint ρ ε i ≤ x := fun i hik =>
    breakpoint_le_of_le hρ hε (le_trans (by exact_mod_cast hik) hkreal)
  -- Every occupied breakpoint strictly past `k` is right of `x`.
  have hgt : ∀ i, k < i → i < m → x < breakpoint ρ ε i := by
    intro i hki him
    refine lt_breakpoint_of_lt hρ hε ?_
    -- `k < i < m` forces `k = n`, hence `xρ/ε < n + 1 ≤ i`.
    have hni : (n : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast (by omega : n + 1 ≤ i)
    have := Nat.lt_floor_add_one (x * ρ / ε)
    rw [← hn_def] at this
    linarith
  -- `x` is within one cell of `b_k`, i.e. `xρ ≤ (k+1)ε`.
  have hub : x * ρ ≤ ((k : ℝ) + 1) * ε := by
    rcases Nat.le_total n (m - 1) with h | h
    · -- capped index equals `⌊xρ/ε⌋`; use the floor upper bound.
      have hk : k = n := by omega
      have hlt := Nat.lt_floor_add_one (x * ρ / ε)
      rw [← hn_def, div_lt_iff₀ hε] at hlt
      rw [hk]; linarith
    · -- capped index equals `m - 1`; use `x ≤ 1 ≤ mε/ρ` via the ceiling bound.
      have hk1 : (k : ℝ) + 1 = (m : ℝ) := by
        have : k + 1 = m := by omega
        exact_mod_cast this
      have hxρ : x * ρ ≤ ρ := mul_le_of_le_one_left hρ.le hx1
      have hmc : m = ⌈ρ / ε⌉₊ := hm_def
      have hρm : ρ ≤ (m : ℝ) * ε := by
        have hle' : ρ / ε ≤ (m : ℝ) := by rw [hmc]; exact Nat.le_ceil _
        rw [div_le_iff₀ hε] at hle'; exact hle'
      rw [hk1]; linarith
  -- Assemble: collapse the network, then apply the Lipschitz estimate.
  have hstep : stepApprox g ρ ε x = g (breakpoint ρ ε k) :=
    stepApprox_collapse g ρ ε x (by omega) hle (fun i hki him => hgt i hki him)
  rw [hstep]
  exact abs_g_breakpoint_sub_le hg hρ (hle k le_rfl) hub

end Approximation.Univariate

end
