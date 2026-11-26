/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Moments.Variance
public import LeanMachineLearning.ForMathlib.Analysis.Convex.Integral

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
* `MeasureTheory.ae_integrable_section_of_integrable_sq`,
  `MeasureTheory.memLp_integral_abs_of_integrable_sq`: the sections, and the absolute partial
  integral, of a square-integrable function are integrable, resp. in `L²`.
* `MeasureTheory.integral_prod_mul_prod`: `∫ f (v, x) f' (v, x') d(μV ⊗ μX ⊗ μX) = ∫ m m'`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

/-- The partial integral `x ↦ ∫ f (x, y) dν(y)` of a measurable function is measurable. -/
theorem _root_.Measurable.integral_prod_right' {α β E : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {ν : Measure β} [SFinite ν] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {f : α × β → E}
    (hf : Measurable f) : Measurable fun x => ∫ y, f (x, y) ∂ν :=
  hf.stronglyMeasurable.integral_prod_right'.measurable

namespace MeasureTheory

variable {V X E : Type*} [MeasurableSpace V] [MeasurableSpace X] {μV : Measure V}
  {μX : Measure X} [NormedAddCommGroup E]

/-- A function with square-integrable norm is integrable for a finite measure. -/
theorem integrable_of_integrable_sq_norm [IsFiniteMeasure μX] {g : X → E}
    (hg : AEStronglyMeasurable g μX) (h : Integrable (fun x => ‖g x‖ ^ 2) μX) :
    Integrable g μX :=
  ((memLp_two_iff_integrable_sq_norm hg).2 h).integrable (by norm_num)

/-- A function with square-integrable sections has integrable sections. -/
theorem integrable_section_of_integrable_sq [IsFiniteMeasure μX] {g : X → ℝ} (hg : Measurable g)
    (h : Integrable (fun x => g x ^ 2) μX) : Integrable g μX :=
  integrable_of_integrable_sq_norm hg.aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs, sq_abs] using h)

/-- **Jensen on a section:** `(∫ f)² ≤ ∫ f²` for a probability measure. -/
theorem sq_integral_le_integral_sq [IsProbabilityMeasure μX] {g : X → ℝ} (hg : Measurable g)
    (h : Integrable (fun x => g x ^ 2) μX) : (∫ x, g x ∂μX) ^ 2 ≤ ∫ x, g x ^ 2 ∂μX := by
  simpa only [Real.norm_eq_abs, sq_abs] using sq_norm_integral_le_integral_sq_norm
    ((memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2 h)

/-- **The partial integral of a square-integrable function is square-integrable**, vector-valued:
`v ↦ ‖∫ x, f (v, x)‖²` is integrable, and its integral is at most `∫ ‖f‖²`. -/
theorem integrable_sq_norm_integral_prod [NormedSpace ℝ E] [SFinite μV]
    [IsProbabilityMeasure μX] {f : V × X → E} (hfm : AEStronglyMeasurable f (μV.prod μX))
    (hf : Integrable (fun z => ‖f z‖ ^ 2) (μV.prod μX)) :
    Integrable (fun v => ‖∫ x, f (v, x) ∂μX‖ ^ 2) μV ∧
      ∫ v, ‖∫ x, f (v, x) ∂μX‖ ^ 2 ∂μV ≤ ∫ z, ‖f z‖ ^ 2 ∂(μV.prod μX) := by
  have hg : Integrable (fun v => ∫ x, ‖f (v, x)‖ ^ 2 ∂μX) μV := hf.integral_prod_left
  have hpt : ∀ᵐ v ∂μV, ‖∫ x, f (v, x) ∂μX‖ ^ 2 ≤ ∫ x, ‖f (v, x)‖ ^ 2 ∂μX := by
    filter_upwards [hf.prod_right_ae, hfm.prodMk_left] with v hv hm
    exact sq_norm_integral_le_integral_sq_norm ((memLp_two_iff_integrable_sq_norm hm).2 hv)
  have hm : AEStronglyMeasurable (fun v => ‖∫ x, f (v, x) ∂μX‖ ^ 2) μV :=
    hfm.integral_prod_right'.norm.pow 2
  have hi : Integrable (fun v => ‖∫ x, f (v, x) ∂μX‖ ^ 2) μV :=
    Integrable.mono' hg hm
      (hpt.mono fun v h => by rwa [Real.norm_of_nonneg (sq_nonneg _)])
  refine ⟨hi, ?_⟩
  calc ∫ v, ‖∫ x, f (v, x) ∂μX‖ ^ 2 ∂μV ≤ ∫ v, ∫ x, ‖f (v, x)‖ ^ 2 ∂μX ∂μV :=
        integral_mono_ae hi hg hpt
    _ = ∫ z, ‖f z‖ ^ 2 ∂(μV.prod μX) := (integral_prod _ hf).symm

/-- **The partial integral of a square-integrable function is square-integrable**, and its norm
does not exceed that of the function. -/
theorem integrable_sq_integral_prod [SFinite μV] [IsProbabilityMeasure μX] {f : V × X → ℝ}
    (hfm : Measurable f) (hf : Integrable (fun z => f z ^ 2) (μV.prod μX)) :
    Integrable (fun v => (∫ x, f (v, x) ∂μX) ^ 2) μV ∧
      ∫ v, (∫ x, f (v, x) ∂μX) ^ 2 ∂μV ≤ ∫ z, f z ^ 2 ∂(μV.prod μX) := by
  simpa only [Real.norm_eq_abs, sq_abs] using integrable_sq_norm_integral_prod (μV := μV)
    (μX := μX) hfm.aestronglyMeasurable (by simpa only [Real.norm_eq_abs, sq_abs] using hf)

/-- **Almost every section** of a function with square-integrable norm on `V × X` is
integrable. -/
theorem ae_integrable_section_of_integrable_sq_norm [SFinite μV] [IsFiniteMeasure μX]
    {g : V × X → E} (hg : AEStronglyMeasurable g (μV.prod μX))
    (h : Integrable (fun z => ‖g z‖ ^ 2) (μV.prod μX)) :
    ∀ᵐ v ∂μV, Integrable (fun x => g (v, x)) μX := by
  filter_upwards [h.prod_right_ae, hg.prodMk_left] with v hv hm
  exact integrable_of_integrable_sq_norm hm hv

/-- **Almost every section** of a square-integrable function on `V × X` is integrable. -/
theorem ae_integrable_section_of_integrable_sq [SFinite μV] [IsFiniteMeasure μX]
    {g : V × X → ℝ} (hg : Measurable g) (h : Integrable (fun z => g z ^ 2) (μV.prod μX)) :
    ∀ᵐ v ∂μV, Integrable (fun x => g (v, x)) μX :=
  ae_integrable_section_of_integrable_sq_norm hg.aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs, sq_abs] using h)

/-- **The partial integral of the norm** `v ↦ ∫ ‖g (v, x)‖ dμX` of a square-integrable function
is in `L²(μV)`. -/
theorem memLp_integral_norm_of_integrable_sq_norm [SFinite μV] [IsProbabilityMeasure μX]
    {g : V × X → E} (hg : AEStronglyMeasurable g (μV.prod μX))
    (h : Integrable (fun z => ‖g z‖ ^ 2) (μV.prod μX)) :
    MemLp (fun v => ∫ x, ‖g (v, x)‖ ∂μX) 2 μV := by
  have h' := (integrable_sq_norm_integral_prod (μV := μV) (μX := μX) hg.norm
    (by simpa only [norm_norm] using h)).1
  exact (memLp_two_iff_integrable_sq_norm hg.norm.integral_prod_right').2 h'

/-- **The absolute partial integral** `v ↦ ∫ |g (v, x)| dμX` of a square-integrable function is
in `L²(μV)`. -/
theorem memLp_integral_abs_of_integrable_sq [SFinite μV] [IsProbabilityMeasure μX]
    {g : V × X → ℝ} (hg : Measurable g) (h : Integrable (fun z => g z ^ 2) (μV.prod μX)) :
    MemLp (fun v => ∫ x, |g (v, x)| ∂μX) 2 μV := by
  simpa only [Real.norm_eq_abs] using memLp_integral_norm_of_integrable_sq_norm (μV := μV)
    (μX := μX) hg.aestronglyMeasurable (by simpa only [Real.norm_eq_abs, sq_abs] using h)

/-- **Two independent copies of the noise**, for a continuous bilinear map `B`: for
square-integrable `f, f'` on `V × X`,
`∫ B (f (v, x)) (f' (v, x')) = ∫ B (∫ f (v, ·)) (∫ f' (v, ·))`, and the integrand on the left is
integrable. -/
theorem integral_prod_bilin_prod {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [CompleteSpace E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [CompleteSpace E₂]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [SFinite μV]
    [IsProbabilityMeasure μX] (B : E₁ →L[ℝ] E₂ →L[ℝ] F) {f : V × X → E₁} {f' : V × X → E₂}
    (hfm : AEStronglyMeasurable f (μV.prod μX))
    (hf : Integrable (fun z => ‖f z‖ ^ 2) (μV.prod μX))
    (hfm' : AEStronglyMeasurable f' (μV.prod μX))
    (hf' : Integrable (fun z => ‖f' z‖ ^ 2) (μV.prod μX)) :
    Integrable (fun z : V × (X × X) => B (f (z.1, z.2.1)) (f' (z.1, z.2.2)))
        (μV.prod (μX.prod μX)) ∧
      ∫ z : V × (X × X), B (f (z.1, z.2.1)) (f' (z.1, z.2.2)) ∂(μV.prod (μX.prod μX)) =
        ∫ v, B (∫ x, f (v, x) ∂μX) (∫ x, f' (v, x) ∂μX) ∂μV := by
  have h1 : MeasureTheory.QuasiMeasurePreserving (fun z : V × (X × X) => (z.1, z.2.1))
      (μV.prod (μX.prod μX)) (μV.prod μX) :=
    ((MeasurePreserving.id μV).prod (measurePreserving_fst (μ := μX)
      (ν := μX))).quasiMeasurePreserving
  have h2 : MeasureTheory.QuasiMeasurePreserving (fun z : V × (X × X) => (z.1, z.2.2))
      (μV.prod (μX.prod μX)) (μV.prod μX) :=
    ((MeasurePreserving.id μV).prod (measurePreserving_snd (μ := μX)
      (ν := μX))).quasiMeasurePreserving
  have hF : AEStronglyMeasurable (fun z : V × (X × X) => B (f (z.1, z.2.1)) (f' (z.1, z.2.2)))
      (μV.prod (μX.prod μX)) :=
    B.aestronglyMeasurable_comp₂ (hfm.comp_quasiMeasurePreserving h1)
      (hfm'.comp_quasiMeasurePreserving h2)
  have hsec : ∀ᵐ v ∂μV, Integrable (fun x => f (v, x)) μX ∧ Integrable (fun x => f' (v, x)) μX := by
    filter_upwards [ae_integrable_section_of_integrable_sq_norm hfm hf,
      ae_integrable_section_of_integrable_sq_norm hfm' hf'] with v a b using ⟨a, b⟩
  have hbil : ∀ᵐ v ∂μV, Integrable (fun p : X × X => B (f (v, p.1)) (f' (v, p.2)))
      (μX.prod μX) := hsec.mono fun v h => by
    refine ((h.1.norm.mul_prod h.2.norm).const_mul ‖B‖).mono'
      (B.aestronglyMeasurable_comp₂ h.1.aestronglyMeasurable.comp_fst
        h.2.aestronglyMeasurable.comp_snd) (ae_of_all _ fun p => ?_)
    rw [← mul_assoc]
    exact B.le_opNorm₂ _ _
  have hI : Integrable (fun z : V × (X × X) => B (f (z.1, z.2.1)) (f' (z.1, z.2.2)))
      (μV.prod (μX.prod μX)) := by
    refine (integrable_prod_iff hF).2 ⟨hbil, ?_⟩
    refine (((memLp_integral_norm_of_integrable_sq_norm hfm hf).integrable_mul
      (memLp_integral_norm_of_integrable_sq_norm hfm' hf')).const_mul ‖B‖).mono'
      hF.norm.integral_prod_right' ?_
    filter_upwards [hsec, hbil] with v h hb
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    refine (integral_mono hb.norm ((h.1.norm.mul_prod h.2.norm).const_mul ‖B‖) fun p => by
      rw [← mul_assoc]; exact B.le_opNorm₂ _ _).trans_eq ?_
    rw [integral_const_mul, integral_prod_mul (fun x => ‖f (v, x)‖) (fun x => ‖f' (v, x)‖)]
    rfl
  refine ⟨hI, ?_⟩
  rw [integral_prod _ hI]
  refine integral_congr_ae ?_
  filter_upwards [hsec, hbil] with v h hb
  rw [integral_prod _ hb]
  have hin : ∀ x, ∫ x', B (f (v, x)) (f' (v, x')) ∂μX = B.flip (∫ x', f' (v, x') ∂μX) (f (v, x)) :=
    fun x => (B (f (v, x))).integral_comp_comm h.2
  simp only [hin]
  exact (B.flip (∫ x', f' (v, x') ∂μX)).integral_comp_comm h.1

/-- **Two independent copies of the noise:** for square-integrable `f, f'` on `V × X`,
`∫ f (v, x) f' (v, x') d(μV ⊗ (μX ⊗ μX)) = ∫ (∫ f (v, ·) dμX) (∫ f' (v, ·) dμX) dμV`, and the
integrand on the left is integrable. -/
theorem integral_prod_mul_prod [SFinite μV] [IsProbabilityMeasure μX] {f f' : V × X → ℝ}
    (hfm : Measurable f) (hf : Integrable (fun z => f z ^ 2) (μV.prod μX))
    (hfm' : Measurable f') (hf' : Integrable (fun z => f' z ^ 2) (μV.prod μX)) :
    Integrable (fun z : V × (X × X) => f (z.1, z.2.1) * f' (z.1, z.2.2))
        (μV.prod (μX.prod μX)) ∧
      ∫ z : V × (X × X), f (z.1, z.2.1) * f' (z.1, z.2.2) ∂(μV.prod (μX.prod μX)) =
        ∫ v, (∫ x, f (v, x) ∂μX) * ∫ x, f' (v, x) ∂μX ∂μV :=
  integral_prod_bilin_prod (ContinuousLinearMap.mul ℝ ℝ) hfm.aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs, sq_abs] using hf) hfm'.aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs, sq_abs] using hf')

/-- **Jensen for a family of square integrable vector-valued functions**:
`∑ᵢ ‖∫ hᵢ‖² ≤ ∫ ∑ᵢ ‖hᵢ‖²` for a probability measure. -/
theorem sum_sq_norm_integral_le {Ω ι : Type*} [MeasurableSpace Ω] [NormedSpace ℝ E] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P] (h : ι → Ω → E) (hm : ∀ i, MemLp (h i) 2 P) :
    ∑ i, ‖∫ ω, h i ω ∂P‖ ^ 2 ≤ ∫ ω, ∑ i, ‖h i ω‖ ^ 2 ∂P := by
  have hint2 (i : ι) : Integrable (fun ω => ‖h i ω‖ ^ 2) P :=
    (memLp_two_iff_integrable_sq_norm (hm i).aestronglyMeasurable).1 (hm i)
  rw [integral_finsetSum Finset.univ fun i _ => hint2 i]
  exact Finset.sum_le_sum fun i _ => sq_norm_integral_le_integral_sq_norm (hm i)

/-- **Jensen for a vector of bounded functions**: `∑ᵢ (∫ hᵢ)² ≤ ∫ ∑ᵢ hᵢ²` for a probability
measure. -/
theorem sum_sq_integral_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}
    [IsProbabilityMeasure P] (h : ι → Ω → ℝ) (hm : ∀ i, Measurable (h i)) {M : ℝ}
    (hb : ∀ i ω, |h i ω| ≤ M) :
    ∑ i, (∫ ω, h i ω ∂P) ^ 2 ≤ ∫ ω, ∑ i, h i ω ^ 2 ∂P := by
  simpa only [Real.norm_eq_abs, sq_abs] using sum_sq_norm_integral_le (P := P) h fun i =>
    MemLp.of_bound (hm i).aestronglyMeasurable M
      (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hb i ω)

end MeasureTheory
