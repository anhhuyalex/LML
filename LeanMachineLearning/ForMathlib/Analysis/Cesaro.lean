/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Order.LiminfLimsup

/-!
# Cesàro averages and `liminf`

Mathlib proves that the Cesàro average of a convergent sequence converges to the same limit
(`Filter.Tendsto.cesaro`).  The Aizenman–Sims–Starr scheme
([Panchenko, 2013, §1.3, Eq. (1.49)]) needs only the one-sided statement for sequences that need
not converge: `liminf` of the averages is at least `liminf` of the sequence.

No definition of the Cesàro average is introduced: it is `(n : ℝ)⁻¹ * ∑ j ∈ range n, u j`.

## Main declarations

* `Filter.Eventually.sub_le_inv_mul_sum_range`: if `c ≤ u n` eventually, then for every `ε > 0` the
  averages are eventually at least `c - ε`; `Filter.Eventually.inv_mul_sum_range_le_add` is the
  upper-bound twin.
* `Filter.liminf_le_liminf_inv_mul_sum_range`: `liminf u ≤ liminf (n⁻¹ ∑_{j<n} u j)` for
  bounded `u`.
-/

@[expose] public section

open Filter Finset
open scoped Topology

namespace Filter

/-- **Cesàro averages inherit eventual lower bounds up to `ε`:** if `c ≤ u n` eventually, then for
every `ε > 0` eventually `c - ε ≤ n⁻¹ ∑_{j<n} u j`. -/
theorem Eventually.sub_le_inv_mul_sum_range {u : ℕ → ℝ} {c : ℝ} (h : ∀ᶠ n in atTop, c ≤ u n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, c - ε ≤ (n : ℝ)⁻¹ * ∑ j ∈ range n, u j := by
  -- the negative part `min (u n - c) 0` vanishes eventually, so its averages tend to `0`
  have hw : Tendsto (fun n => min (u n - c) 0) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (h.mono fun n hn => (min_eq_right (sub_nonneg.2 hn)).symm)
  filter_upwards [(hw.cesaro).eventually (lt_mem_nhds (show -ε < 0 by linarith)),
    eventually_ge_atTop 1] with n hn hn1
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hle : (n : ℝ)⁻¹ * ∑ j ∈ range n, min (u j - c) 0 ≤
      (n : ℝ)⁻¹ * ∑ j ∈ range n, u j - c := by
    have : (n : ℝ)⁻¹ * ∑ j ∈ range n, (u j - c) = (n : ℝ)⁻¹ * ∑ j ∈ range n, u j - c := by
      rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_sub, inv_mul_cancel_left₀ hn0]
    rw [← this]
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => min_le_left _ _)
      (inv_nonneg.2 (Nat.cast_nonneg _))
  linarith

/-- **Cesàro averages inherit eventual upper bounds up to `ε`:** if `u n ≤ c` eventually, then for
every `ε > 0` eventually `n⁻¹ ∑_{j<n} u j ≤ c + ε`. -/
theorem Eventually.inv_mul_sum_range_le_add {u : ℕ → ℝ} {c : ℝ} (h : ∀ᶠ n in atTop, u n ≤ c)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)⁻¹ * ∑ j ∈ range n, u j ≤ c + ε := by
  filter_upwards [Eventually.sub_le_inv_mul_sum_range (u := fun n => -u n) (c := -c)
    (h.mono fun n hn => neg_le_neg hn) hε] with n hn
  simp only [sum_neg_distrib, mul_neg] at hn
  linarith

/-- **`liminf` of Cesàro averages** ([Panchenko, 2013, §1.3]): for a bounded sequence,
`liminf u ≤ liminf (n⁻¹ ∑_{j<n} u j)`. -/
theorem liminf_le_liminf_inv_mul_sum_range {u : ℕ → ℝ} (hu : IsBoundedUnder (· ≤ ·) atTop u)
    (hu' : IsBoundedUnder (· ≥ ·) atTop u) :
    liminf u atTop ≤ liminf (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ range n, u j) atTop := by
  obtain ⟨C, hC⟩ := hu
  have hC' : ∀ᶠ n in atTop, u n ≤ C := hC
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j ∈ range n, u j) :=
    ⟨C + 1, (Eventually.inv_mul_sum_range_le_add hC' one_pos)⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have h1 : liminf u atTop - ε / 2 < liminf u atTop := by linarith
  have h2 := le_liminf_of_le hb.isCoboundedUnder_ge
    (Eventually.sub_le_inv_mul_sum_range (c := liminf u atTop - ε / 2)
      ((eventually_lt_of_lt_liminf h1 hu').mono fun n hn => hn.le) (half_pos hε))
  linarith

end Filter
