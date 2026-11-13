/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# A derivative vanishes if the function vanishes on a one-sided neighbourhood

If `g` is differentiable at `0` with `g 0 = 0` and `g μ = 0` for all small `μ > 0`, then
`g' 0 = 0`: the slope `(g μ - g 0) / μ` is eventually `0` and tends to `g' 0`.
-/

@[expose] public section

open Filter
open scoped Topology

/-- **A one-sided eventually-zero function has zero derivative.** -/
theorem eq_zero_of_hasDerivAt_of_eventually_eq_zero_nhdsGT {g : ℝ → ℝ} {d : ℝ}
    (hg : HasDerivAt g d 0) (hg0 : g 0 = 0) (h : ∀ᶠ μ in 𝓝[>] (0 : ℝ), g μ = 0) : d = 0 := by
  have hslope : Tendsto (slope g 0) (𝓝[>] 0) (𝓝 d) :=
    hg.tendsto_slope.mono_left (nhdsWithin_mono 0 fun x hx => ne_of_gt hx)
  have hzero : Tendsto (slope g 0) (𝓝[>] 0) (𝓝 0) :=
    (EventuallyEq.tendsto (h.mono fun μ hμ => by simp [slope, hμ, hg0]))
  exact tendsto_nhds_unique hslope hzero
