/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The fundamental theorem of calculus for an integrand that is locally continuous

`intervalIntegral.integral_hasDerivAt_right` needs the integrand to be continuous at the endpoint
and strongly measurable near it.  Both follow if the integrand agrees near the endpoint with a
continuous function, which is how it is used when the integrand is locally constant or locally
affine.

## Main declarations

* `hasDerivAt_intervalIntegral_of_eventuallyEq`: the derivative of `μ ↦ ∫₀^μ g` at `τ` is `g τ`
  when `g` is interval integrable on `[0, τ]` and eventually equal to a continuous `h` near `τ`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

/-- **FTC for an integrand that is locally equal to a continuous function.**  If `g` is interval
integrable on `[0, τ]` and equals a continuous function `h` near `τ`, then `μ ↦ ∫₀^μ g` has
derivative `g τ` at `τ`. -/
theorem hasDerivAt_intervalIntegral_of_eventuallyEq {g h : ℝ → ℝ} {τ : ℝ}
    (hint : IntervalIntegrable g volume 0 τ) (hev : g =ᶠ[𝓝 τ] h) (hh : Continuous h) :
    HasDerivAt (fun μ => ∫ u in (0 : ℝ)..μ, g u) (g τ) τ := by
  have hcont : ContinuousAt g τ := (continuousAt_congr hev).mpr hh.continuousAt
  obtain ⟨s, hs, hsg⟩ := hev.exists_mem
  have hmeas : StronglyMeasurableAtFilter g (𝓝 τ) := by
    refine ⟨interior s, interior_mem_nhds.2 hs, ?_⟩
    exact hh.aestronglyMeasurable.congr (ae_restrict_of_forall_mem isOpen_interior.measurableSet
      fun x hx => (hsg (interior_subset hx)).symm)
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hcont
