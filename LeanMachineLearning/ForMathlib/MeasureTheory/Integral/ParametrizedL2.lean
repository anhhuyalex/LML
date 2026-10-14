/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Moments.Variance

/-!
# Partial integrals of square-integrable functions

Let `f : V × X → ℝ` be square-integrable for a product of probability measures `μV ⊗ μX`, and
`m v = ∫ f (v, x) dμX(x)` its partial integral.  Then `m` is square-integrable, with
`‖m‖² ≤ ‖f‖²` (Jensen on each section), and the "two independent copies of the noise" integral
reduces to the inner product of the partial integrals:
`∫∫∫ f (v, x) f' (v, x') = ∫ m m'`.

## Main declarations

* `MeasureTheory.integrable_sq_integral_prod`: `v ↦ (∫ x, f (v, x))²` is integrable and
  `∫ v, (∫ x, f (v, x))² ≤ ∫ f²`.
* `MeasureTheory.integral_prod_mul_prod`: `∫ f (v, x) f' (v, x') d(μV ⊗ μX ⊗ μX) = ∫ m m'`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {V X : Type*} [MeasurableSpace V] [MeasurableSpace X] {μV : Measure V} {μX : Measure X}
  [IsProbabilityMeasure μV] [IsProbabilityMeasure μX]

/-- A function with square-integrable sections has integrable sections. -/
theorem integrable_section_of_integrable_sq {g : X → ℝ} (hg : Measurable g)
    (h : Integrable (fun x => g x ^ 2) μX) : Integrable g μX :=
  ((memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 h).integrable (by norm_num)

/-- **Jensen on a section:** `(∫ f)² ≤ ∫ f²` for a probability measure. -/
theorem sq_integral_le_integral_sq {g : X → ℝ} (hg : Measurable g)
    (h : Integrable (fun x => g x ^ 2) μX) : (∫ x, g x ∂μX) ^ 2 ≤ ∫ x, g x ^ 2 ∂μX := by
  have hm : MemLp g 2 μX := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 h
  have := variance_nonneg g μX
  rw [variance_eq_sub hm] at this
  simp only [Pi.pow_apply] at this
  linarith

variable {f f' : V × X → ℝ}

/-- **The partial integral of a square-integrable function is square-integrable**, and its norm
does not exceed that of the function. -/
theorem integrable_sq_integral_prod (hfm : Measurable f)
    (hf : Integrable (fun z => f z ^ 2) (μV.prod μX)) :
    Integrable (fun v => (∫ x, f (v, x) ∂μX) ^ 2) μV ∧
      ∫ v, (∫ x, f (v, x) ∂μX) ^ 2 ∂μV ≤ ∫ z, f z ^ 2 ∂(μV.prod μX) := by
  have hg : Integrable (fun v => ∫ x, f (v, x) ^ 2 ∂μX) μV := hf.integral_prod_left
  have hpt : ∀ᵐ v ∂μV, (∫ x, f (v, x) ∂μX) ^ 2 ≤ ∫ x, f (v, x) ^ 2 ∂μX := by
    filter_upwards [hf.prod_right_ae] with v hv
    exact sq_integral_le_integral_sq (hfm.comp measurable_prodMk_left) hv
  have hm : Measurable fun v => (∫ x, f (v, x) ∂μX) ^ 2 :=
    ((hfm.stronglyMeasurable.integral_prod_right').measurable).pow_const 2
  have hi : Integrable (fun v => (∫ x, f (v, x) ∂μX) ^ 2) μV :=
    Integrable.mono' hg hm.aestronglyMeasurable
      (hpt.mono fun v h => by rwa [Real.norm_of_nonneg (sq_nonneg _)])
  refine ⟨hi, ?_⟩
  calc ∫ v, (∫ x, f (v, x) ∂μX) ^ 2 ∂μV ≤ ∫ v, ∫ x, f (v, x) ^ 2 ∂μX ∂μV :=
        integral_mono_ae hi hg hpt
    _ = ∫ z, f z ^ 2 ∂(μV.prod μX) := (integral_prod _ hf).symm

/-- **Two independent copies of the noise:** for square-integrable `f, f'` on `V × X`,
`∫ f (v, x) f' (v, x') d(μV ⊗ (μX ⊗ μX)) = ∫ (∫ f (v, ·) dμX) (∫ f' (v, ·) dμX) dμV`, and the
integrand on the left is integrable. -/
theorem integral_prod_mul_prod (hfm : Measurable f) (hf : Integrable (fun z => f z ^ 2) (μV.prod μX))
    (hfm' : Measurable f') (hf' : Integrable (fun z => f' z ^ 2) (μV.prod μX)) :
    Integrable (fun z : V × (X × X) => f (z.1, z.2.1) * f' (z.1, z.2.2))
        (μV.prod (μX.prod μX)) ∧
      ∫ z : V × (X × X), f (z.1, z.2.1) * f' (z.1, z.2.2) ∂(μV.prod (μX.prod μX)) =
        ∫ v, (∫ x, f (v, x) ∂μX) * ∫ x, f' (v, x) ∂μX ∂μV := by
  have hF : Measurable fun z : V × (X × X) => f (z.1, z.2.1) * f' (z.1, z.2.2) :=
    (hfm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hfm'.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hs : ∀ {g : V × X → ℝ}, Measurable g → Integrable (fun z => g z ^ 2) (μV.prod μX) →
      ∀ᵐ v ∂μV, Integrable (fun x => g (v, x)) μX := fun hg hgi => by
    filter_upwards [hgi.prod_right_ae] with v hv
    exact integrable_section_of_integrable_sq (hg.comp measurable_prodMk_left) hv
  -- the absolute partial integrals are square-integrable
  have hA : ∀ {g : V × X → ℝ}, Measurable g → Integrable (fun z => g z ^ 2) (μV.prod μX) →
      MemLp (fun v => ∫ x, |g (v, x)| ∂μX) 2 μV := fun hg hgi => by
    have hg' : Measurable fun z => |g z| := hg.abs
    have h := (integrable_sq_integral_prod (μV := μV) (μX := μX) hg'
      (by simpa [sq_abs] using hgi)).1
    exact (memLp_two_iff_integrable_sq
      ((hg'.stronglyMeasurable.integral_prod_right').measurable.aestronglyMeasurable)).2 h
  refine ⟨?_, ?_⟩
  · refine (integrable_prod_iff hF.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · filter_upwards [hs hfm hf, hs hfm' hf'] with v h1 h2
      exact h1.mul_prod h2
    · have : (fun v => ∫ p : X × X, ‖f (v, p.1) * f' (v, p.2)‖ ∂(μX.prod μX)) =
          fun v => (∫ x, |f (v, x)| ∂μX) * ∫ x, |f' (v, x)| ∂μX := by
        funext v
        simp only [norm_mul, Real.norm_eq_abs]
        exact integral_prod_mul (fun x => |f (v, x)|) (fun x => |f' (v, x)|)
      simp only [this]
      exact (hA hfm hf).integrable_mul (hA hfm' hf')
  · sorry

end MeasureTheory
