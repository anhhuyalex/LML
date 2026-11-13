/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Convex.Deriv

/-!
# Convergence of derivatives of convex functions at a point of differentiability

If convex functions `f i` converge pointwise to `g` on an open interval around `0` and `g` is
differentiable at `0`, then the derivatives `(f i)'(0)` converge to `g'(0)`.  The proof squeezes
`(f i)'(0)` between the secant slopes of `f i` on `[-λ, 0]` and `[0, λ]`; first the index filter
is passed to the limit, then `λ` is shrunk.  This is the positive counterpart of
`not_differentiableAt_of_convexOn_tendsto_of_derivative_gap`, where a derivative gap forces a
corner.

## Main declarations

* `tendsto_deriv_of_convexOn_tendsto`: the statement above, for any nontrivial filter `l`.
-/

@[expose] public section

open Set Filter
open scoped Topology

/-- **Derivatives of pointwise-convergent convex functions converge at a point where the limit is
differentiable.**  Let `f i` be convex on `(-r, r)` and differentiable at `0` with derivative
`f' i 0`, and suppose `f i` converges to `g` pointwise on `(-r, r)` along `l`.  If `g` is
differentiable at `0`, then `f' i 0 → deriv g 0`. -/
theorem tendsto_deriv_of_convexOn_tendsto
    {ι : Type*} {l : Filter ι} {f f' : ι → ℝ → ℝ} {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hconv : ∀ i, ConvexOn ℝ (Ioo (-r) r) (f i))
    (hderiv : ∀ i, HasDerivAt (f i) (f' i 0) 0)
    (hlim : ∀ x ∈ Ioo (-r) r, Tendsto (fun i => f i x) l (𝓝 (g x)))
    (hg : DifferentiableAt ℝ g 0) :
    Tendsto (fun i => f' i 0) l (𝓝 (deriv g 0)) := by
  have h0 : (0 : ℝ) ∈ Ioo (-r) r := ⟨by linarith, hr⟩
  have hd := hg.hasDerivAt
  set d := deriv g 0
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · -- lower bound: `a < f' i 0` eventually, from the left secant slope
    have hlo := (hasDerivAt_iff_isLittleO.mp hd).def (show 0 < (d - a) / 2 by linarith)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hlo
    set lam : ℝ := min (δ / 2) (r / 2) with hlam
    have hl0 : 0 < lam := by positivity
    have hlδ : lam < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hlr : lam < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hmem : -lam ∈ Ioo (-r) r := ⟨by linarith, by linarith⟩
    have hest := hball (y := -lam)
      (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hl0]; exact hlδ)
    simp only [Real.norm_eq_abs, smul_eq_mul, sub_zero, abs_neg, abs_of_pos hl0] at hest
    rw [abs_le] at hest
    have hT : Tendsto (fun i => (f i 0 - f i (-lam)) / lam) l
        (𝓝 ((g 0 - g (-lam)) / lam)) := ((hlim 0 h0).sub (hlim (-lam) hmem)).div_const lam
    have hgt : a < (g 0 - g (-lam)) / lam := by
      rw [lt_div_iff₀ hl0]
      nlinarith [hest.1, hest.2]
    filter_upwards [hT.eventually (lt_mem_nhds hgt)] with i hi
    have := (hconv i).slope_le_of_hasDerivAt (x := -lam) (y := 0) hmem h0 (by linarith)
      (hderiv i)
    rw [slope_def_field] at this
    have e : (0 : ℝ) - -lam = lam := by ring
    rw [e] at this
    exact hi.trans_le this
  · -- upper bound: `f' i 0 < a` eventually, from the right secant slope
    have hlo := (hasDerivAt_iff_isLittleO.mp hd).def (show 0 < (a - d) / 2 by linarith)
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hlo
    set lam : ℝ := min (δ / 2) (r / 2) with hlam
    have hl0 : 0 < lam := by positivity
    have hlδ : lam < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hlr : lam < r := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hmem : lam ∈ Ioo (-r) r := ⟨by linarith, hlr⟩
    have hest := hball (y := lam) (by rw [Real.dist_eq, sub_zero, abs_of_pos hl0]; exact hlδ)
    simp only [Real.norm_eq_abs, smul_eq_mul, sub_zero, abs_of_pos hl0] at hest
    rw [abs_le] at hest
    have hT : Tendsto (fun i => (f i lam - f i 0) / lam) l
        (𝓝 ((g lam - g 0) / lam)) := ((hlim lam hmem).sub (hlim 0 h0)).div_const lam
    have hlt : (g lam - g 0) / lam < a := by
      rw [div_lt_iff₀ hl0]
      nlinarith [hest.1, hest.2]
    filter_upwards [hT.eventually (gt_mem_nhds hlt)] with i hi
    have := (hconv i).le_slope_of_hasDerivAt (x := 0) (y := lam) h0 hmem (by linarith)
      (hderiv i)
    rw [slope_def_field] at this
    have e : lam - 0 = lam := by ring
    rw [e] at this
    exact this.trans_lt hi
