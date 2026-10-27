/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Convex.Deriv

/-!
# Pointwise limits of convex functions with a derivative gap at the origin

A pointwise limit of differentiable convex functions can have a corner.  This file proves the
quantitative form used in [Talagrand, Spin Glasses I, Theorem 1.9.6]: if the convex functions
`f n` converge pointwise to `f` near `0`, and there is a fixed `c > 0` such that for every small
`λ > 0` the derivative gap `(f n)'(λ) - (f n)'(-λ)` exceeds `c` for all large `n` (the threshold may
depend on `λ`; no uniformity in `λ` and no convergence of the derivatives is assumed), then `f`
is not differentiable at `0`.

The proof compares derivatives with secant slopes on `[λ, 2λ]` and `[-2λ, -λ]`, which converge
to the corresponding secant slopes of `f`; differentiability of `f` at `0` forces both slopes to
be close to `f'(0)` for small `λ`.

## Main declarations

* `not_differentiableAt_of_convexOn_tendsto_of_derivative_gap`: the non-differentiability
  statement.
-/

@[expose] public section

open Set Filter
open scoped Topology

/-- **Pointwise limits of convex functions with a derivative gap are not differentiable.**
Let `f n` be convex and differentiable on `(-r, r)` with derivative `f' n`, and suppose `f n`
converges pointwise to `f` on `(-r, r)`.  If there is `c > 0` such that for every `λ ∈ (0, r)`
the gap `f' n λ - f' n (-λ)` is eventually (in `n`) larger than `c`, then `f` is not
differentiable at `0`. -/
theorem not_differentiableAt_of_convexOn_tendsto_of_derivative_gap
    {f : ℕ → ℝ → ℝ} {f' : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hconv : ∀ n, ConvexOn ℝ (Ioo (-r) r) (f n))
    (hderiv : ∀ n, ∀ x ∈ Ioo (-r) r, HasDerivAt (f n) (f' n x) x)
    (hlim : ∀ x ∈ Ioo (-r) r, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hgap : ∀ lam ∈ Ioo 0 r, ∀ᶠ n in atTop, c < f' n lam - f' n (-lam)) :
    ¬ DifferentiableAt ℝ g 0 := by
  intro hg
  have hd := hg.hasDerivAt
  have hlo := (hasDerivAt_iff_isLittleO.mp hd).def (show 0 < c / 8 by positivity)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hlo
  set lam : ℝ := min (δ / 2) (r / 2) / 2 with hlam
  have hl0 : 0 < lam := by positivity
  have hlδ : 2 * lam < δ := by
    have : min (δ / 2) (r / 2) ≤ δ / 2 := min_le_left _ _
    linarith
  have hlr : 2 * lam < r := by
    have : min (δ / 2) (r / 2) ≤ r / 2 := min_le_right _ _
    linarith
  have hmem : ∀ x : ℝ, |x| ≤ 2 * lam → x ∈ Ioo (-r) r := fun x hx =>
    ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  have hest : ∀ x : ℝ, |x| ≤ 2 * lam → |g x - g 0 - x * deriv g 0| ≤ c / 8 * |x| := by
    intro x hx
    have := hball (y := x) (by rw [Real.dist_eq, sub_zero]; linarith)
    simpa [Real.norm_eq_abs, smul_eq_mul, mul_comm] using this
  set d := deriv g 0
  have hA : ∀ n, f' n lam ≤ (f n (2 * lam) - f n lam) / lam := by
    intro n
    have := (hconv n).le_slope_of_hasDerivAt (x := lam) (y := 2 * lam)
      (hmem lam (by rw [abs_of_pos hl0]; linarith)) (hmem (2 * lam)
        (by rw [abs_of_pos (by positivity)])) (by linarith)
      (hderiv n lam (hmem lam (by rw [abs_of_pos hl0]; linarith)))
    rw [slope_def_field] at this
    have e : 2 * lam - lam = lam := by ring
    rwa [e] at this
  have hB : ∀ n, (f n (-lam) - f n (-(2 * lam))) / lam ≤ f' n (-lam) := by
    intro n
    have := (hconv n).slope_le_of_hasDerivAt (x := -(2 * lam)) (y := -lam)
      (hmem _ (by rw [abs_neg, abs_of_pos (by positivity)]))
      (hmem _ (by rw [abs_neg, abs_of_pos hl0]; linarith)) (by linarith)
      (hderiv n (-lam) (hmem _ (by rw [abs_neg, abs_of_pos hl0]; linarith)))
    rw [slope_def_field] at this
    have e : -lam - -(2 * lam) = lam := by ring
    rwa [e] at this
  have hT : Tendsto (fun n => (f n (2 * lam) - f n lam) / lam -
      (f n (-lam) - f n (-(2 * lam))) / lam) atTop
      (𝓝 ((g (2 * lam) - g lam) / lam - (g (-lam) - g (-(2 * lam))) / lam)) := by
    have h1 := hlim (2 * lam) (hmem _ (by rw [abs_of_pos (by positivity)]))
    have h2 := hlim lam (hmem _ (by rw [abs_of_pos hl0]; linarith))
    have h3 := hlim (-lam) (hmem _ (by rw [abs_neg, abs_of_pos hl0]; linarith))
    have h4 := hlim (-(2 * lam)) (hmem _ (by rw [abs_neg, abs_of_pos (by positivity)]))
    exact ((h1.sub h2).div_const lam).sub ((h3.sub h4).div_const lam)
  have hge : c ≤ (g (2 * lam) - g lam) / lam - (g (-lam) - g (-(2 * lam))) / lam := by
    refine ge_of_tendsto hT ?_
    filter_upwards [hgap lam ⟨hl0, by linarith⟩] with n hn
    linarith [hA n, hB n]
  have e1 := hest (2 * lam) (by rw [abs_of_pos (by positivity)])
  have e2 := hest lam (by rw [abs_of_pos hl0]; linarith)
  have e3 := hest (-lam) (by rw [abs_neg, abs_of_pos hl0]; linarith)
  have e4 := hest (-(2 * lam)) (by rw [abs_neg, abs_of_pos (by positivity)])
  rw [abs_of_pos (by positivity : 0 < 2 * lam)] at e1
  rw [abs_of_pos hl0] at e2
  rw [abs_neg, abs_of_pos hl0] at e3
  rw [abs_neg, abs_of_pos (by positivity : 0 < 2 * lam)] at e4
  rw [abs_le] at e1 e2 e3 e4
  have hgap' : (g (2 * lam) - g lam) / lam - (g (-lam) - g (-(2 * lam))) / lam ≤ 3 * c / 4 := by
    rw [← sub_div, div_le_iff₀ hl0]
    nlinarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2]
  linarith
