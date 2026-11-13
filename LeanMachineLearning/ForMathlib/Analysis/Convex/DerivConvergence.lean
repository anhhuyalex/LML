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
`(f i)'(x)` between secant slopes of `f i` on either side of `x`; the secant slopes of `g` converge
to `g'(x)`, so a secant point `y` close to `x` is chosen first, then the index filter is passed to
the limit.  This is the positive counterpart of
`not_differentiableAt_of_convexOn_tendsto_of_derivative_gap`, where a derivative gap forces a
corner.

## Main declarations

* `tendsto_deriv_of_convexOn_tendsto_of_mem_Ioo`: the statement at any point `x` of an open
  interval, for any filter `l` and scalar derivative values `d i`.
* `tendsto_deriv_of_convexOn_tendsto`: the case of a symmetric interval and `x = 0`.
-/

@[expose] public section

open Set Filter
open scoped Topology

/-- **Derivatives of pointwise-convergent convex functions converge at a point where the limit is
differentiable.**  Let `f i` be convex on `(a, b)` with derivative `d i` at `x ∈ (a, b)`, and
suppose `f i` converges to `g` pointwise on `(a, b)` along `l`.  If `g` is differentiable at `x`,
then `d i → deriv g x`. -/
theorem tendsto_deriv_of_convexOn_tendsto_of_mem_Ioo
    {ι : Type*} {l : Filter ι} {f : ι → ℝ → ℝ} {d : ι → ℝ}
    {g : ℝ → ℝ} {a b x : ℝ} (hx : x ∈ Ioo a b)
    (hconv : ∀ i, ConvexOn ℝ (Ioo a b) (f i))
    (hderiv : ∀ i, HasDerivAt (f i) (d i) x)
    (hlim : ∀ y ∈ Ioo a b, Tendsto (fun i => f i y) l (𝓝 (g y)))
    (hg : DifferentiableAt ℝ g x) :
    Tendsto d l (𝓝 (deriv g x)) := by
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · have hsec := hg.hasDerivAt.tendsto_slope.mono_left (nhdsLT_le_nhdsNE x)
    have hlo : ∀ᶠ y in 𝓝[<] x, a < y :=
      (show ∀ᶠ y in 𝓝 x, a < y from Ioi_mem_nhds hx.1).filter_mono inf_le_left
    have hneg : ∀ᶠ y in 𝓝[<] x, y < x := self_mem_nhdsWithin
    obtain ⟨y, hya, hyx, hcy⟩ :=
      (hlo.and (hneg.and (hsec.eventually (Ioi_mem_nhds hc)))).exists
    have hy : y ∈ Ioo a b := ⟨hya, hyx.trans hx.2⟩
    have hT : Tendsto (fun i => slope (f i) x y) l (𝓝 (slope g x y)) := by
      simp only [slope_def_field]
      exact ((hlim y hy).sub (hlim x hx)).div_const _
    filter_upwards [hT.eventually (Ioi_mem_nhds hcy)] with i hi
    have hb := (hconv i).slope_le_of_hasDerivAt hy hx hyx (hderiv i)
    rw [slope_comm] at hb
    exact hi.trans_le hb
  · have hsec := hg.hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)
    have hhi : ∀ᶠ y in 𝓝[>] x, y < b :=
      (show ∀ᶠ y in 𝓝 x, y < b from Iio_mem_nhds hx.2).filter_mono inf_le_left
    have hpos : ∀ᶠ y in 𝓝[>] x, x < y := self_mem_nhdsWithin
    obtain ⟨y, hyb, hxy, hyc⟩ :=
      (hhi.and (hpos.and (hsec.eventually (Iio_mem_nhds hc)))).exists
    have hy : y ∈ Ioo a b := ⟨hx.1.trans hxy, hyb⟩
    have hT : Tendsto (fun i => slope (f i) x y) l (𝓝 (slope g x y)) := by
      simp only [slope_def_field]
      exact ((hlim y hy).sub (hlim x hx)).div_const _
    filter_upwards [hT.eventually (Iio_mem_nhds hyc)] with i hi
    exact ((hconv i).le_slope_of_hasDerivAt hx hy hxy (hderiv i)).trans_lt hi

/-- The case `x = 0` on a symmetric interval `(-r, r)` of
`tendsto_deriv_of_convexOn_tendsto_of_mem_Ioo`. -/
theorem tendsto_deriv_of_convexOn_tendsto
    {ι : Type*} {l : Filter ι} {f f' : ι → ℝ → ℝ} {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (hconv : ∀ i, ConvexOn ℝ (Ioo (-r) r) (f i))
    (hderiv : ∀ i, HasDerivAt (f i) (f' i 0) 0)
    (hlim : ∀ x ∈ Ioo (-r) r, Tendsto (fun i => f i x) l (𝓝 (g x)))
    (hg : DifferentiableAt ℝ g 0) :
    Tendsto (fun i => f' i 0) l (𝓝 (deriv g 0)) :=
  tendsto_deriv_of_convexOn_tendsto_of_mem_Ioo ⟨by linarith, hr⟩ hconv hderiv hlim hg
