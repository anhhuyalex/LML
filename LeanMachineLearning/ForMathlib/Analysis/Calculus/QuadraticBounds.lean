/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Derivative at zero from a quadratic sandwich

If `t * a ≤ ψ t ≤ t * a + C * t ^ 2` for all `t` near `0`, then `ψ 0 = 0` and `ψ` has derivative `a`
at `0`: the difference quotient differs from `a` by at most `|C| * |t|`.

The same conclusion holds for a limit of functions `ψᵢ` along any nontrivial filter, if the
sandwich holds eventually along the filter for each `t` near `0` (with `C` fixed) and the
coefficients `aᵢ` converge: pass the two inequalities to the limit.

## Main declarations

* `abs_inv_mul_sub_le_of_quadratic_bounds`: the pointwise bound on the difference quotient.
* `hasDerivAt_zero_of_eventually_quadratic_bounds`: the derivative at `0`.
* `hasDerivAt_zero_of_tendsto_quadratic_bounds`: the same for a limit along a filter.
-/

@[expose] public section

open Filter
open scoped Topology

/-- **The difference quotient of a quadratically sandwiched value:** if `t * a ≤ x ≤ t * a + C * t²`
and `t ≠ 0`, then `|x / t - a| ≤ |C| * |t|`. -/
theorem abs_inv_mul_sub_le_of_quadratic_bounds {x a C t : ℝ}
    (hl : t * a ≤ x) (hu : x ≤ t * a + C * t ^ 2) (ht : t ≠ 0) :
    |t⁻¹ * x - a| ≤ |C| * |t| := by
  have heq : t⁻¹ * x - a = (x - t * a) / t := by field_simp
  rw [heq, abs_div, div_le_iff₀ (abs_pos.mpr ht), abs_of_nonneg (sub_nonneg.mpr hl)]
  calc x - t * a ≤ C * t ^ 2 := by linarith
    _ ≤ |C| * t ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg t)
    _ = |C| * |t| * |t| := by rw [mul_assoc, ← pow_two, sq_abs]

/-- **A function quadratically sandwiched near `0` is differentiable there:** if
`t * a ≤ ψ t ≤ t * a + C * t²` for all `t` near `0`, then `ψ' 0 = a`. -/
theorem hasDerivAt_zero_of_eventually_quadratic_bounds {ψ : ℝ → ℝ} {a C : ℝ}
    (h : ∀ᶠ t in 𝓝 0, t * a ≤ ψ t ∧ ψ t ≤ t * a + C * t ^ 2) :
    HasDerivAt ψ a 0 := by
  have h0 : ψ 0 = 0 := by
    have ht : 0 ≤ ψ 0 ∧ ψ 0 ≤ 0 := by simpa using h.self_of_nhds
    exact le_antisymm ht.2 ht.1
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hb : ∀ᶠ t in 𝓝[≠] 0, ‖t⁻¹ • (ψ t - ψ 0) - a‖ ≤ |C| * |t| := by
    filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with t ht hne
    simpa only [h0, sub_zero, smul_eq_mul, Real.norm_eq_abs] using
      abs_inv_mul_sub_le_of_quadratic_bounds ht.1 ht.2 hne
  have hlim : Tendsto (fun t : ℝ => |C| * |t|) (𝓝[≠] 0) (𝓝 0) := by
    simpa using ((continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds).const_mul |C|
  have ht := (squeeze_zero_norm' hb hlim).add_const a
  simpa only [sub_add_cancel, zero_add] using ht

/-- **Derivative at `0` of a limit of quadratically sandwiched functions.**  Let `ψᵢ → ψ`
pointwise near `0` along a nontrivial filter `l`, `aᵢ → a`, and suppose that for each `t` near `0`
eventually along `l` we have `t * aᵢ ≤ ψᵢ t ≤ t * aᵢ + C * t²` with a fixed `C`.  Then `ψ' 0 = a`.
The threshold in `i` may depend on `t`. -/
theorem hasDerivAt_zero_of_tendsto_quadratic_bounds
    {ι : Type*} {l : Filter ι} [l.NeBot] {ψs : ι → ℝ → ℝ} {as : ι → ℝ}
    {ψ : ℝ → ℝ} {a C : ℝ} (ha : Tendsto as l (𝓝 a))
    (hψ : ∀ᶠ t in 𝓝 0, Tendsto (fun i => ψs i t) l (𝓝 (ψ t)))
    (hb : ∀ᶠ t in 𝓝 0, ∀ᶠ i in l,
      t * as i ≤ ψs i t ∧ ψs i t ≤ t * as i + C * t ^ 2) : HasDerivAt ψ a 0 := by
  refine hasDerivAt_zero_of_eventually_quadratic_bounds (C := C) ?_
  filter_upwards [hψ, hb] with t ht hbound
  exact ⟨le_of_tendsto_of_tendsto (ha.const_mul t) ht (hbound.mono fun i hi => hi.1),
    le_of_tendsto_of_tendsto ht ((ha.const_mul t).add_const (C * t ^ 2))
      (hbound.mono fun i hi => hi.2)⟩
