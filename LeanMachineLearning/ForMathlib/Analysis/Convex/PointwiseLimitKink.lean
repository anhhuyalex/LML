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
`f i` converge pointwise to `g` near `0` along a nontrivial filter (a sequence, a subsequence or a
net), and there is a fixed `c > 0` such that for every small `λ > 0` the derivative gap
`(f i)'(λ) - (f i)'(-λ)` is at least `c` eventually (the threshold may depend on `λ`; no
uniformity in `λ` and no convergence of the derivatives is assumed), then `g` is not
differentiable at `0`.

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
Let `f i` be convex and differentiable on `(-r, r)` with derivative `f' i`, and suppose `f i`
converges to `g` pointwise on `(-r, r)` along a nontrivial filter `l`.  If there is `c > 0` such
that for every `λ ∈ (0, r)` the gap `f' i λ - f' i (-λ)` is eventually (along `l`) at least `c`,
then `g` is not differentiable at `0`. -/
theorem not_differentiableAt_of_convexOn_tendsto_of_derivative_gap
    {ι : Type*} {l : Filter ι} [l.NeBot] {f f' : ι → ℝ → ℝ} {g : ℝ → ℝ} {r c : ℝ}
    (hr : 0 < r) (hc : 0 < c)
    (hconv : ∀ i, ConvexOn ℝ (Ioo (-r) r) (f i))
    (hderiv : ∀ i, ∀ x ∈ Ioo (-r) r, HasDerivAt (f i) (f' i x) x)
    (hlim : ∀ x ∈ Ioo (-r) r, Tendsto (fun i => f i x) l (𝓝 (g x)))
    (hgap : ∀ lam ∈ Ioo 0 r, ∀ᶠ i in l, c ≤ f' i lam - f' i (-lam)) :
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
  have hA : ∀ i, f' i lam ≤ (f i (2 * lam) - f i lam) / lam := by
    intro i
    have := (hconv i).le_slope_of_hasDerivAt (x := lam) (y := 2 * lam)
      (hmem lam (by rw [abs_of_pos hl0]; linarith)) (hmem (2 * lam)
        (by rw [abs_of_pos (by positivity)])) (by linarith)
      (hderiv i lam (hmem lam (by rw [abs_of_pos hl0]; linarith)))
    rw [slope_def_field] at this
    have e : 2 * lam - lam = lam := by ring
    rwa [e] at this
  have hB : ∀ i, (f i (-lam) - f i (-(2 * lam))) / lam ≤ f' i (-lam) := by
    intro i
    have := (hconv i).slope_le_of_hasDerivAt (x := -(2 * lam)) (y := -lam)
      (hmem _ (by rw [abs_neg, abs_of_pos (by positivity)]))
      (hmem _ (by rw [abs_neg, abs_of_pos hl0]; linarith)) (by linarith)
      (hderiv i (-lam) (hmem _ (by rw [abs_neg, abs_of_pos hl0]; linarith)))
    rw [slope_def_field] at this
    have e : -lam - -(2 * lam) = lam := by ring
    rwa [e] at this
  have hT : Tendsto (fun i => (f i (2 * lam) - f i lam) / lam -
      (f i (-lam) - f i (-(2 * lam))) / lam) l
      (𝓝 ((g (2 * lam) - g lam) / lam - (g (-lam) - g (-(2 * lam))) / lam)) := by
    have h1 := hlim (2 * lam) (hmem _ (by rw [abs_of_pos (by positivity)]))
    have h2 := hlim lam (hmem _ (by rw [abs_of_pos hl0]; linarith))
    have h3 := hlim (-lam) (hmem _ (by rw [abs_neg, abs_of_pos hl0]; linarith))
    have h4 := hlim (-(2 * lam)) (hmem _ (by rw [abs_neg, abs_of_pos (by positivity)]))
    exact ((h1.sub h2).div_const lam).sub ((h3.sub h4).div_const lam)
  have hge : c ≤ (g (2 * lam) - g lam) / lam - (g (-lam) - g (-(2 * lam))) / lam := by
    refine ge_of_tendsto hT ?_
    filter_upwards [hgap lam ⟨hl0, by linarith⟩] with i hi
    linarith [hA i, hB i]
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
