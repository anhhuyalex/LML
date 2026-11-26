/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.RCLike.Basic

/-!
# Pointwise domination of a triple iterated integral

A pointwise bound `|G x y z| ≤ H x y z` passes through three nested integrals
`∫ x, ∫ y, ∫ z, G x y z ∂κ x y ∂ν ∂μ`, where the innermost measure may depend on the outer
variables, as soon as the dominating function has integrable partial integrals.
-/

@[expose] public section

open MeasureTheory

/-- Multiplying both copies of an integrand by a scalar whose square is one does not change its
second moment. -/
@[simp] theorem integral_mul_self_of_sq_eq_one {X K : Type*} [MeasurableSpace X]
    [NormedCommRing K] [NormedAlgebra ℝ K] (μ : Measure X) (u : K) (hu : u ^ 2 = 1) (f : X → K) :
    ∫ x, (u * f x) * (u * f x) ∂μ = ∫ x, f x * f x ∂μ := by
  congr 1
  funext x
  calc
    (u * f x) * (u * f x) = u ^ 2 * (f x * f x) := by ring
    _ = f x * f x := by rw [hu, one_mul]

/-- Two scalar factors may be collected outside an integral. -/
theorem integral_mul_mul_eq_mul_integral {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (u v : 𝕜) (f g : X → 𝕜) :
    ∫ x, (u * f x) * (v * g x) ∂μ = u * v * ∫ x, f x * g x ∂μ := by
  have hfun : (fun x => (u * f x) * (v * g x)) = fun x => (u * v) * (f x * g x) := by
    funext x
    ring
  rw [hfun, integral_const_mul]

/-- A pointwise bound `‖f‖ ≤ K g` almost everywhere passes through an integral. -/
theorem norm_integral_le_const_mul_integral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X) {f : X → E} {g : X → ℝ} {K : ℝ}
    (hg : Integrable g μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖ ≤ K * g x) :
    ‖∫ x, f x ∂μ‖ ≤ K * ∫ x, g x ∂μ := by
  simpa only [integral_const_mul] using norm_integral_le_of_norm_le (hg.const_mul K) hfg

/-- A pointwise bound `|f| ≤ K g` passes through an integral.  The domination hypothesis itself
forces `K g` to be nonnegative, so no separate sign assumptions on `K` or `g` are needed. -/
theorem abs_integral_le_const_mul_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f g : X → ℝ} {K : ℝ} (hg : Integrable g μ)
    (hfg : ∀ x, |f x| ≤ K * g x) :
    |∫ x, f x ∂μ| ≤ K * ∫ x, g x ∂μ := by
  simpa only [Real.norm_eq_abs] using norm_integral_le_const_mul_integral μ (f := f) hg
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hfg x)

/-- Integrating a constant plus an integrable function over a probability measure preserves the
constant. -/
@[simp] theorem integral_const_add_of_isProbabilityMeasure
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (μ : Measure X) [IsProbabilityMeasure μ] (c : E) (f : X → E)
    (hf : Integrable f μ) :
    ∫ x, c + f x ∂μ = c + ∫ x, f x ∂μ := by
  rw [integral_add (integrable_const c) hf, integral_const, probReal_univ, one_smul]

/-- Integrating an integrable function plus a constant over a probability measure preserves the
constant. -/
@[simp] theorem integral_add_const_of_isProbabilityMeasure
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (μ : Measure X) [IsProbabilityMeasure μ] (f : X → E) (c : E)
    (hf : Integrable f μ) :
    ∫ x, f x + c ∂μ = (∫ x, f x ∂μ) + c := by
  simpa only [add_comm] using integral_const_add_of_isProbabilityMeasure μ c f hf

/-- Integrating an integrable function minus a constant over a probability measure preserves
the constant. -/
@[simp] theorem integral_sub_const_of_isProbabilityMeasure
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (μ : Measure X) [IsProbabilityMeasure μ] (f : X → E) (c : E)
    (hf : Integrable f μ) :
    ∫ x, f x - c ∂μ = (∫ x, f x ∂μ) - c := by
  simpa only [sub_eq_add_neg] using integral_add_const_of_isProbabilityMeasure μ f (-c) hf

/-- Domination of a triple iterated integral of a vector-valued function by the iterated
integral of a dominating function, almost everywhere. -/
theorem norm_integral_integral_integral_le {X Y Z E : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) (ν : Measure Y) (κ : X → Y → Measure Z) {G : X → Y → Z → E}
    {H : X → Y → Z → ℝ} (hGH : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, ∀ᵐ z ∂κ x y, ‖G x y z‖ ≤ H x y z)
    (h1 : ∀ x y, Integrable (H x y) (κ x y))
    (h2 : ∀ x, Integrable (fun y => ∫ z, H x y z ∂κ x y) ν)
    (h3 : Integrable (fun x => ∫ y, ∫ z, H x y z ∂κ x y ∂ν) μ) :
    ‖∫ x, ∫ y, ∫ z, G x y z ∂κ x y ∂ν ∂μ‖ ≤ ∫ x, ∫ y, ∫ z, H x y z ∂κ x y ∂ν ∂μ :=
  norm_integral_le_of_norm_le h3 <| hGH.mono fun x hx =>
    norm_integral_le_of_norm_le (h2 x) <| hx.mono fun y hy =>
      norm_integral_le_of_norm_le (h1 x y) hy

/-- Domination of a triple iterated integral by the iterated integral of a dominating function. -/
theorem abs_integral_integral_integral_le {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] (μ : Measure X) (ν : Measure Y) (κ : X → Y → Measure Z)
    {G H : X → Y → Z → ℝ} (hGH : ∀ x y z, |G x y z| ≤ H x y z)
    (h1 : ∀ x y, Integrable (H x y) (κ x y))
    (h2 : ∀ x, Integrable (fun y => ∫ z, H x y z ∂κ x y) ν)
    (h3 : Integrable (fun x => ∫ y, ∫ z, H x y z ∂κ x y ∂ν) μ) :
    |∫ x, ∫ y, ∫ z, G x y z ∂κ x y ∂ν ∂μ| ≤ ∫ x, ∫ y, ∫ z, H x y z ∂κ x y ∂ν ∂μ := by
  simpa only [Real.norm_eq_abs] using norm_integral_integral_integral_le μ ν κ (G := G)
    (ae_of_all _ fun x => ae_of_all _ fun y => ae_of_all _ fun z => by
      simpa only [Real.norm_eq_abs] using hGH x y z) h1 h2 h3

/-- A nonnegative combination of iterated averages, each bounded by `X`, is bounded by the sum of
the coefficients times `X`. Only the terms of the sum need to be integrable. -/
theorem integral_integral_finset_sum_le_of_mem {Ω Z ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Z] (μ : Measure Ω) (κ : Ω → Measure Z) (s : Finset ι) (c : ι → ℝ)
    (G : ι → Z → ℝ) (X : ℝ) (hG : ∀ j ∈ s, ∀ g, Integrable (G j) (κ g))
    (hint : ∀ j ∈ s, Integrable (fun g => ∫ z, G j z ∂κ g) μ)
    (hc : ∀ j ∈ s, 0 ≤ c j) (hX : ∀ j ∈ s, ∫ g, ∫ z, G j z ∂κ g ∂μ ≤ X) :
    ∫ g, ∫ z, ∑ j ∈ s, c j * G j z ∂κ g ∂μ ≤ (∑ j ∈ s, c j) * X := by
  have h1 : ∀ g, ∫ z, ∑ j ∈ s, c j * G j z ∂κ g = ∑ j ∈ s, c j * ∫ z, G j z ∂κ g := fun g => by
    rw [integral_finsetSum _ fun j hj => (hG j hj g).const_mul (c j)]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  simp_rw [h1]
  rw [integral_finsetSum _ fun j hj => (hint j hj).const_mul (c j)]
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hX j hj) (hc j hj)

/-- A nonnegative combination of iterated averages, each bounded by `X`, is bounded by the sum of
the coefficients times `X`. The inner integrals are over finite measures and the outer integrand of
each term is integrable. -/
theorem integral_integral_finset_sum_le {Ω Z ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (μ : Measure Ω) (κ : Ω → Measure Z) (s : Finset ι) (c : ι → ℝ) (G : ι → Z → ℝ) (X : ℝ)
    (hG : ∀ j g, Integrable (G j) (κ g))
    (hint : ∀ j, Integrable (fun g => ∫ z, G j z ∂κ g) μ)
    (hc : ∀ j ∈ s, 0 ≤ c j) (hX : ∀ j ∈ s, ∫ g, ∫ z, G j z ∂κ g ∂μ ≤ X) :
    ∫ g, ∫ z, ∑ j ∈ s, c j * G j z ∂κ g ∂μ ≤ (∑ j ∈ s, c j) * X :=
  integral_integral_finset_sum_le_of_mem μ κ s c G X (fun j _ => hG j) (fun j _ => hint j) hc hX

/-- Integrating a function of the first coordinate over a product with a probability measure. -/
theorem integral_prod_fun_fst_of_isProbabilityMeasure {X Y E : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X) [SFinite μ]
    (ν : Measure Y) [IsProbabilityMeasure ν] (f : X → E) :
    ∫ x, f x.1 ∂(μ.prod ν) = ∫ y, f y ∂μ := by
  rw [integral_fun_fst, probReal_univ, one_smul]

/-- Integrating a function of the second coordinate over a product with a probability measure. -/
theorem integral_prod_fun_snd_of_isProbabilityMeasure {X Y E : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X)
    [IsProbabilityMeasure μ] (ν : Measure Y) [SFinite ν] (f : Y → E) :
    ∫ x, f x.2 ∂(μ.prod ν) = ∫ y, f y ∂ν := by
  rw [integral_fun_snd, probReal_univ, one_smul]

/-- A uniform bound on an observable bounds its average over a probability measure. No
measurability or integrability hypotheses are needed for this bound. -/
theorem abs_integral_le_of_forall_abs_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {f : X → ℝ} {M : ℝ} (hf : ∀ x, |f x| ≤ M) :
    |∫ x, f x ∂μ| ≤ M := by
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := M)
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hf x)

/-- An almost everywhere uniform bound on an environment-dependent vector-valued observable
bounds its iterated average over probability measures. -/
theorem norm_integral_integral_le_of_ae_norm_le {X Y E : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure X)
    [IsProbabilityMeasure μ] (κ : X → Measure Y) [∀ x, IsProbabilityMeasure (κ x)]
    (F : X → Y → E) {M : ℝ} (hF : ∀ᵐ x ∂μ, ∀ᵐ y ∂κ x, ‖F x y‖ ≤ M) :
    ‖∫ x, ∫ y, F x y ∂κ x ∂μ‖ ≤ M := by
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (C := M)
    (hF.mono fun x hx => by simpa using norm_integral_le_of_norm_le_const (μ := κ x) hx)

/-- A uniform bound on an environment-dependent observable bounds its iterated average over
probability measures. No measurability or integrability hypotheses are needed for this bound. -/
theorem abs_integral_integral_le_of_forall_abs_le {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (μ : Measure X) [IsProbabilityMeasure μ] (κ : X → Measure Y)
    [∀ x, IsProbabilityMeasure (κ x)] (F : X → Y → ℝ) {M : ℝ} (hF : ∀ x y, |F x y| ≤ M) :
    |∫ x, ∫ y, F x y ∂κ x ∂μ| ≤ M := by
  simpa only [Real.norm_eq_abs] using norm_integral_integral_le_of_ae_norm_le μ κ F
    (ae_of_all _ fun x => ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hF x y)

/-- A uniform bound on an observable bounds its iterated average over probability measures. -/
theorem abs_integral_integral_le_of_forall_le {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (μ : Measure X) [IsProbabilityMeasure μ] (κ : X → Measure Y)
    [∀ x, IsProbabilityMeasure (κ x)] (F : Y → ℝ) {M : ℝ} (hF : ∀ y, |F y| ≤ M) :
    |∫ x, ∫ y, F y ∂κ x ∂μ| ≤ M :=
  abs_integral_integral_le_of_forall_abs_le μ κ (fun _ => F) (fun _ => hF)

/-- An integrand `F ≥ 0` (a.e.) dominated by `Upper`, whose partial integrals are bounded by an
integrable `Bnd` with `∫ Bnd ≤ C`, has iterated integral at most `C`. -/
theorem double_integral_le_of_ae_dominated {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) {F Upper : α → β → ℝ} {Bnd : α → ℝ} {C : ℝ}
    (hF : ∀ᵐ x ∂μ, F x ≤ᵐ[ν] Upper x) (hF0 : ∀ᵐ x ∂μ, 0 ≤ᵐ[ν] F x)
    (hU : ∀ᵐ x ∂μ, Integrable (Upper x) ν) (hUB : ∀ᵐ x ∂μ, ∫ y, Upper x y ∂ν ≤ Bnd x)
    (hB : Integrable Bnd μ) (hBC : ∫ x, Bnd x ∂μ ≤ C) :
    ∫ x, ∫ y, F x y ∂ν ∂μ ≤ C := by
  have h_inner : ∀ᵐ x ∂μ, ∫ y, F x y ∂ν ≤ Bnd x := by
    filter_upwards [hF, hF0, hU, hUB] with x h1 h2 h3 h4 using
      (integral_mono_of_nonneg h2 h3 h1).trans h4
  exact (integral_mono_of_nonneg (hF0.mono fun x h => integral_nonneg_of_ae h) hB
    h_inner).trans hBC

/-- A nonnegative integrand `F` dominated pointwise by `Upper`, whose partial integrals are
bounded by an integrable `Bnd` with `∫ Bnd ≤ C`, has iterated integral at most `C`. -/
theorem double_integral_le_of_dominated {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) {F Upper : α → β → ℝ} {Bnd : α → ℝ} {C : ℝ}
    (hF : ∀ x y, F x y ≤ Upper x y) (hF0 : ∀ x y, 0 ≤ F x y)
    (hU : ∀ x, Integrable (Upper x) ν) (hUB : ∀ x, ∫ y, Upper x y ∂ν ≤ Bnd x)
    (hB : Integrable Bnd μ) (hBC : ∫ x, Bnd x ∂μ ≤ C) :
    ∫ x, ∫ y, F x y ∂ν ∂μ ≤ C :=
  double_integral_le_of_ae_dominated μ ν (ae_of_all _ fun x => ae_of_all _ (hF x))
    (ae_of_all _ fun x => ae_of_all _ (hF0 x)) (ae_of_all _ hU) (ae_of_all _ hUB) hB hBC

/-- The integral of an a.e. nonnegative function over a product of s-finite measures is at most
its iterated integral.  No integrability is needed: if the function is not integrable on the
product, the left side is the junk value `0`. -/
theorem integral_prod_le_integral_integral_of_ae_nonneg {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {F : α × β → ℝ} (hF0 : 0 ≤ᵐ[μ.prod ν] F) :
    ∫ w, F w ∂(μ.prod ν) ≤ ∫ x, ∫ y, F (x, y) ∂ν ∂μ := by
  by_cases hint : Integrable F (μ.prod ν)
  · exact (integral_prod F hint).le
  · rw [integral_undef hint]
    exact integral_nonneg_of_ae <| (Measure.ae_ae_of_ae_prod hF0).mono fun x hx =>
      integral_nonneg_of_ae hx

/-- The integral of a nonnegative function over a product of s-finite measures is at most its
iterated integral. -/
theorem integral_prod_le_integral_integral_of_nonneg {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {F : α × β → ℝ} (hF0 : ∀ w, 0 ≤ F w) :
    ∫ w, F w ∂(μ.prod ν) ≤ ∫ x, ∫ y, F (x, y) ∂ν ∂μ :=
  integral_prod_le_integral_integral_of_ae_nonneg (ae_of_all _ hF0)
