/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.ExpSqLinear
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.Hyperbolic
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiExp

/-!
# A Laplace principle for Gaussian integrals

Let `A` be a continuous function on `ℝ^ι` of at most linear growth, and let `x` be a standard
Gaussian vector. Then
`N⁻¹ log 𝔼 exp (N A (x / √N))` tends to `max_g (A g - ½ ‖g‖²)`.
This is the elementary Laplace principle used in the proof of Talagrand's Theorem 1.13.1. The
maximizer is a hypothesis (a witness), not a supremum.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- The scaling algebra behind the pointwise bound of the Laplace integral. -/
theorem laplace_scaling_aux (N s t B K S L : ℝ) (hs : s ≠ 0) (hsq : s ^ 2 = N) :
    N * (t * (B + S / N / 2) + (1 - t) * (K * (1 + L / s))) =
      N * (t * B + (1 - t) * K) + (t / 2 * S + s * ((1 - t) * K) * L) := by
  subst hsq
  have hs2 : s ^ 2 ≠ 0 := pow_ne_zero 2 hs
  field_simp
  ring

/-- The one-dimensional integrand `exp (t y²/2 + c |y|)` is Gaussian integrable for `t < 1`. -/
theorem integrable_exp_mul_sq_add_mul_abs {t : ℝ} (ht1 : t < 1) (c : ℝ) :
    Integrable (fun y : ℝ => Real.exp (t / 2 * y ^ 2 + c * |y|)) (gaussianReal 0 1) := by
  have hl : t / 2 < 1 / 2 := by linarith
  have hi1 := integrable_exp_mul_sq_add_mul_gaussianReal hl c
  have hi2 := integrable_exp_mul_sq_add_mul_gaussianReal hl (-c)
  refine Integrable.mono' (hi1.add hi2) (by fun_prop) (ae_of_all _ fun y => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  simpa only [sub_eq_add_neg, neg_mul, Pi.add_apply] using
    Real.exp_add_mul_abs_le_add (t / 2 * y ^ 2) c y

/-- The Gaussian integral of the one-dimensional integrand. -/
theorem integral_exp_mul_sq_add_mul_abs_le {t : ℝ} (ht1 : t < 1) (c : ℝ) :
    ∫ y : ℝ, Real.exp (t / 2 * y ^ 2 + c * |y|) ∂(gaussianReal 0 1) ≤
      2 * (Real.sqrt (1 - t))⁻¹ * Real.exp (c ^ 2 / (2 * (1 - t))) := by
  have hl : t / 2 < 1 / 2 := by linarith
  have hi1 := integrable_exp_mul_sq_add_mul_gaussianReal hl c
  have hi2 := integrable_exp_mul_sq_add_mul_gaussianReal hl (-c)
  have hle (y : ℝ) : Real.exp (t / 2 * y ^ 2 + c * |y|) ≤
      Real.exp (t / 2 * y ^ 2 + c * y) + Real.exp (t / 2 * y ^ 2 + -c * y) := by
    simpa only [sub_eq_add_neg, neg_mul] using
      Real.exp_add_mul_abs_le_add (t / 2 * y ^ 2) c y
  have hint : ∫ y : ℝ, Real.exp (t / 2 * y ^ 2 + c * |y|) ∂(gaussianReal 0 1) ≤
      ∫ y : ℝ, (Real.exp (t / 2 * y ^ 2 + c * y) + Real.exp (t / 2 * y ^ 2 + -c * y))
        ∂(gaussianReal 0 1) :=
    integral_mono_of_nonneg (ae_of_all _ fun y => (Real.exp_pos _).le) (hi1.add hi2)
      (ae_of_all _ hle)
  refine hint.trans (le_of_eq ?_)
  rw [integral_add hi1 hi2, integral_exp_mul_sq_add_mul_gaussianReal hl,
    integral_exp_mul_sq_add_mul_gaussianReal hl]
  have h1t : 1 - 2 * (t / 2) = 1 - t := by ring
  rw [h1t, neg_sq]
  ring

/-- **Pointwise bound** for the Laplace integrand. -/
theorem laplace_pointwise_bound (A : (ι → ℝ) → ℝ) (K : ℝ)
    (hA : ∀ g, |A g| ≤ K * (1 + ∑ i, |g i|)) (B : ℝ)
    (hB : ∀ g, A g - (∑ i, g i ^ 2) / 2 ≤ B) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {N : ℕ} (hN : 0 < N) (x : ι → ℝ) :
    N * A (fun i => x i / Real.sqrt N) ≤ N * (t * B + (1 - t) * K) +
      ∑ i, (t / 2 * x i ^ 2 + Real.sqrt N * ((1 - t) * K) * |x i|) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNpos.le
  set g : ι → ℝ := fun i => x i / Real.sqrt N with hg
  have hS : ∑ i, g i ^ 2 = (∑ i, x i ^ 2) / N := by
    simp only [hg, div_pow, hsq, Finset.sum_div]
  have hL : ∑ i, |g i| = (∑ i, |x i|) / Real.sqrt N := by
    simp only [hg, abs_div, abs_of_pos hsN, Finset.sum_div]
  have h1 : A g ≤ B + (∑ i, g i ^ 2) / 2 := by linarith [hB g]
  have h2 : A g ≤ K * (1 + ∑ i, |g i|) := (le_abs_self _).trans (hA g)
  have h3 : A g ≤ t * (B + (∑ i, g i ^ 2) / 2) + (1 - t) * (K * (1 + ∑ i, |g i|)) := by
    have := mul_le_mul_of_nonneg_left h1 ht0.le
    have := mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 ht1.le)
    nlinarith
  have h4 := mul_le_mul_of_nonneg_left h3 hNpos.le
  rw [hS, hL] at h4
  have e := laplace_scaling_aux N (Real.sqrt N) t B K (∑ i, x i ^ 2) (∑ i, |x i|) hsN.ne' hsq
  rw [e] at h4
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  exact h4

/-- **Upper bound for the Laplace integral.** If `A g - ‖g‖²/2 ≤ B` for all `g` and `A` has linear
growth, then for every `t ∈ (0, 1)` the Laplace integral is at most
`exp (N (t B + (1 - t) K)) (2 (1 - t)^{-1/2} exp (N (1 - t) K² / 2))^{card ι}`. -/
theorem integral_exp_laplace_le (A : (ι → ℝ) → ℝ) (K : ℝ)
    (hA : ∀ g, |A g| ≤ K * (1 + ∑ i, |g i|)) (B : ℝ)
    (hB : ∀ g, A g - (∑ i, g i ^ 2) / 2 ≤ B) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    {N : ℕ} (hN : 0 < N) :
    ∫ x : ι → ℝ, Real.exp (N * A (fun i => x i / Real.sqrt N))
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) ≤
      Real.exp (N * (t * B + (1 - t) * K)) *
        (2 * (Real.sqrt (1 - t))⁻¹ * Real.exp (N * (1 - t) * K ^ 2 / 2)) ^ Fintype.card ι := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNpos.le
  set c : ℝ := Real.sqrt N * ((1 - t) * K) with hc
  have hJint := integrable_exp_mul_sq_add_mul_abs ht1 c
  have hone : ∫ y : ℝ, Real.exp (t / 2 * y ^ 2 + c * |y|) ∂(gaussianReal 0 1) ≤
      2 * (Real.sqrt (1 - t))⁻¹ * Real.exp (N * (1 - t) * K ^ 2 / 2) := by
    refine (integral_exp_mul_sq_add_mul_abs_le ht1 c).trans (le_of_eq ?_)
    have : c ^ 2 / (2 * (1 - t)) = N * (1 - t) * K ^ 2 / 2 := by
      rw [hc, mul_pow, hsq]
      have : (1 - t) ≠ 0 := by linarith
      field_simp
    rw [this]
  have hprodint : Integrable (fun x : ι → ℝ =>
      ∏ i, Real.exp (t / 2 * x i ^ 2 + c * |x i|)) (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    Integrable.fintype_prod (f := fun _ => fun y : ℝ => Real.exp (t / 2 * y ^ 2 + c * |y|))
      fun _ => hJint
  calc ∫ x : ι → ℝ, Real.exp (N * A (fun i => x i / Real.sqrt N))
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1)
      ≤ ∫ x : ι → ℝ, Real.exp (N * (t * B + (1 - t) * K)) *
          ∏ i, Real.exp (t / 2 * x i ^ 2 + c * |x i|)
          ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun x => (Real.exp_pos _).le)
          (hprodint.const_mul _) (ae_of_all _ fun x => ?_)
        beta_reduce
        rw [← Real.exp_sum, ← Real.exp_add]
        exact Real.exp_le_exp.2 (laplace_pointwise_bound A K hA B hB ht0 ht1 hN x)
    _ = Real.exp (N * (t * B + (1 - t) * K)) *
          (∫ y : ℝ, Real.exp (t / 2 * y ^ 2 + c * |y|) ∂(gaussianReal 0 1)) ^ Fintype.card ι := by
        rw [integral_const_mul]
        congr 1
        have := MeasureTheory.integral_fintype_prod_eq_prod
          (E := fun _ : ι => ℝ) (μ := fun _ : ι => gaussianReal 0 1)
          (fun _ (y : ℝ) => Real.exp (t / 2 * y ^ 2 + c * |y|))
        rw [this, Finset.prod_const, Finset.card_univ]
    _ ≤ _ := by
        gcongr

/-- The Laplace integrand is integrable. -/
theorem integrable_exp_laplace (A : (ι → ℝ) → ℝ) (hAm : Measurable A) (K : ℝ)
    (hA : ∀ g, |A g| ≤ K * (1 + ∑ i, |g i|)) (B : ℝ)
    (hB : ∀ g, A g - (∑ i, g i ^ 2) / 2 ≤ B) {N : ℕ} (hN : 0 < N) :
    Integrable (fun x : ι → ℝ => Real.exp (N * A (fun i => x i / Real.sqrt N)))
      (Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have ht0 : (0 : ℝ) < 1 / 2 := by norm_num
  have ht1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hJint := integrable_exp_mul_sq_add_mul_abs ht1 (Real.sqrt N * ((1 - 1 / 2) * K))
  have hprodint : Integrable (fun x : ι → ℝ =>
      ∏ i, Real.exp (1 / 2 / 2 * x i ^ 2 + Real.sqrt N * ((1 - 1 / 2) * K) * |x i|))
      (Measure.pi fun _ : ι => gaussianReal 0 1) :=
    Integrable.fintype_prod (f := fun _ => fun y : ℝ =>
      Real.exp (1 / 2 / 2 * y ^ 2 + Real.sqrt N * ((1 - 1 / 2) * K) * |y|)) fun _ => hJint
  have hm : Measurable (fun x : ι → ℝ => Real.exp (N * A (fun i => x i / Real.sqrt N))) := by
    have : Measurable fun x : ι → ℝ => (fun i => x i / Real.sqrt N) := by fun_prop
    exact (measurable_const.mul (hAm.comp this)).exp
  refine Integrable.mono' (hprodint.const_mul (Real.exp (N * (1 / 2 * B + (1 - 1 / 2) * K))))
    hm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_sum, ← Real.exp_add]
  exact Real.exp_le_exp.2 (laplace_pointwise_bound A K hA B hB ht0 ht1 hN x)

/-- A standard Gaussian charges the interval `(a - r, a + r)` by at least
`2 r (2π)^{-1/2} exp (-(|a| + r)² / 2)`. -/
theorem gaussianReal_Ioo_ge (a : ℝ) {r : ℝ} (hr : 0 < r) :
    2 * r * (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(|a| + r) ^ 2 / 2) ≤
      (gaussianReal 0 1 (Set.Ioo (a - r) (a + r))).toReal := by
  rw [gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioo fun x _ =>
      gaussianPDFReal_nonneg _ _ _)]
  have hvol : (volume (Set.Ioo (a - r) (a + r))).toReal = 2 * r := by
    rw [Real.volume_Ioo]
    rw [ENNReal.toReal_ofReal (by linarith)]
    ring
  have hle := setIntegral_ge_of_const_le_real (μ := volume) (s := Set.Ioo (a - r) (a + r))
    (f := gaussianPDFReal 0 1)
    (c := (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(|a| + r) ^ 2 / 2)) measurableSet_Ioo
    (by simp) (fun x hx => ?_) ((integrable_gaussianPDFReal 0 1).integrableOn)
  · rw [Measure.real, hvol] at hle
    calc 2 * r * (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(|a| + r) ^ 2 / 2)
        = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(|a| + r) ^ 2 / 2) * (2 * r) := by ring
      _ ≤ _ := hle
  · rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have hx2 : x ^ 2 ≤ (|a| + r) ^ 2 := by
      have hxa : |x| ≤ |a| + r := by
        rw [abs_le]
        constructor <;> nlinarith [hx.1, hx.2, neg_abs_le a, le_abs_self a]
      calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
        _ ≤ (|a| + r) ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hxa 2
    linarith

/-- **Lower bound for the Laplace integral.** If `A g ≥ A gs - ε` whenever every coordinate of
`g` is within `δ` of the matching coordinate of `gs`, then the Laplace integral is at least
`exp (N (A gs - ε - ∑ (|gsᵢ| + δ)² / 2)) (2 √N δ (2π)^{-1/2})^{card ι}`. -/
theorem integral_exp_laplace_ge (A : (ι → ℝ) → ℝ) (hAm : Measurable A) (K : ℝ)
    (hA : ∀ g, |A g| ≤ K * (1 + ∑ i, |g i|)) (B : ℝ)
    (hB : ∀ g, A g - (∑ i, g i ^ 2) / 2 ≤ B) (gs : ι → ℝ) {δ ε : ℝ} (hδ : 0 < δ)
    (hcont : ∀ g : ι → ℝ, (∀ i, |g i - gs i| < δ) → A gs - ε ≤ A g) {N : ℕ} (hN : 0 < N) :
    Real.exp (N * (A gs - ε - (∑ i, (|gs i| + δ) ^ 2) / 2)) *
        (2 * Real.sqrt N * δ * (Real.sqrt (2 * Real.pi))⁻¹) ^ Fintype.card ι ≤
      ∫ x : ι → ℝ, Real.exp (N * A (fun i => x i / Real.sqrt N))
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNpos.le
  set S : Set (ι → ℝ) := Set.pi Set.univ (fun i =>
    Set.Ioo (Real.sqrt N * gs i - Real.sqrt N * δ) (Real.sqrt N * gs i + Real.sqrt N * δ)) with hS
  have hint := integrable_exp_laplace A hAm K hA B hB hN
  have hSmeas : MeasurableSet S := MeasurableSet.univ_pi fun i => measurableSet_Ioo
  have h1 : ∫ x in S, Real.exp (N * A (fun i => x i / Real.sqrt N))
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) ≤
      ∫ x : ι → ℝ, Real.exp (N * A (fun i => x i / Real.sqrt N))
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1) :=
    setIntegral_le_integral hint (ae_of_all _ fun x => (Real.exp_pos _).le)
  have h2 := setIntegral_ge_of_const_le_real (μ := Measure.pi fun _ : ι => gaussianReal 0 1)
    (s := S) (f := fun x : ι → ℝ => Real.exp (N * A (fun i => x i / Real.sqrt N)))
    (c := Real.exp (N * (A gs - ε))) hSmeas (measure_ne_top _ _)
    (fun x hx => ?_) hint.integrableOn
  · refine le_trans ?_ (h2.trans h1)
    have hmeasS : (Measure.pi fun _ : ι => gaussianReal 0 1).real S =
        ∏ i, (gaussianReal 0 1 (Set.Ioo (Real.sqrt N * gs i - Real.sqrt N * δ)
          (Real.sqrt N * gs i + Real.sqrt N * δ))).toReal := by
      rw [Measure.real, hS, Measure.pi_pi, ENNReal.toReal_prod]
    have hfac (i : ι) : 2 * Real.sqrt N * δ * (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-(N * (|gs i| + δ) ^ 2) / 2) ≤
        (gaussianReal 0 1 (Set.Ioo (Real.sqrt N * gs i - Real.sqrt N * δ)
          (Real.sqrt N * gs i + Real.sqrt N * δ))).toReal := by
      have hr : 0 < Real.sqrt N * δ := mul_pos hsN hδ
      have := gaussianReal_Ioo_ge (Real.sqrt N * gs i) hr
      have habs : |Real.sqrt N * gs i| + Real.sqrt N * δ = Real.sqrt N * (|gs i| + δ) := by
        rw [abs_mul, abs_of_pos hsN]
        ring
      rw [habs, mul_pow, hsq] at this
      calc 2 * Real.sqrt N * δ * (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.exp (-(N * (|gs i| + δ) ^ 2) / 2)
          = 2 * (Real.sqrt N * δ) * (Real.sqrt (2 * Real.pi))⁻¹ *
            Real.exp (-(N * (|gs i| + δ) ^ 2) / 2) := by ring
        _ ≤ _ := this
    have hprod : (2 * Real.sqrt N * δ * (Real.sqrt (2 * Real.pi))⁻¹) ^ Fintype.card ι *
        Real.exp (-(N * ∑ i, (|gs i| + δ) ^ 2) / 2) ≤
        ∏ i, (gaussianReal 0 1 (Set.Ioo (Real.sqrt N * gs i - Real.sqrt N * δ)
          (Real.sqrt N * gs i + Real.sqrt N * δ))).toReal := by
      refine le_trans (le_of_eq ?_) (Finset.prod_le_prod₀ (fun i _ => by positivity)
        (fun i _ => hfac i))
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
      congr 2
      rw [← Finset.sum_div, Finset.sum_neg_distrib, ← Finset.mul_sum]
    rw [hmeasS]
    calc Real.exp (N * (A gs - ε - (∑ i, (|gs i| + δ) ^ 2) / 2)) *
          (2 * Real.sqrt N * δ * (Real.sqrt (2 * Real.pi))⁻¹) ^ Fintype.card ι
        = Real.exp (N * (A gs - ε)) * ((2 * Real.sqrt N * δ * (Real.sqrt (2 * Real.pi))⁻¹) ^
            Fintype.card ι * Real.exp (-(N * ∑ i, (|gs i| + δ) ^ 2) / 2)) := by
          rw [show N * (A gs - ε - (∑ i, (|gs i| + δ) ^ 2) / 2) =
            N * (A gs - ε) + (-(N * ∑ i, (|gs i| + δ) ^ 2) / 2) by ring, Real.exp_add]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
  · have hx' : ∀ i, |x i / Real.sqrt N - gs i| < δ := by
      intro i
      have hxi := hx i (Set.mem_univ i)
      have e : x i / Real.sqrt N - gs i = (x i - Real.sqrt N * gs i) / Real.sqrt N := by
        field_simp
      rw [e, abs_lt]
      constructor
      · rw [lt_div_iff₀ hsN]
        linarith [hxi.1]
      · rw [div_lt_iff₀ hsN]
        linarith [hxi.2]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hcont _ hx') hNpos.le)

/-- Eventually the normalized logarithm of the Laplace integral is below any level above the
maximum `B`. -/
theorem eventually_log_integral_exp_laplace_lt (A : (ι → ℝ) → ℝ) (hAm : Measurable A) (K : ℝ)
    (hA : ∀ g, |A g| ≤ K * (1 + ∑ i, |g i|)) (B : ℝ)
    (hB : ∀ g, A g - (∑ i, g i ^ 2) / 2 ≤ B) {a : ℝ} (ha : B < a) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ)⁻¹ * Real.log (∫ x : ι → ℝ,
      Real.exp (N * A (fun i => x i / Real.sqrt N)) ∂(Measure.pi fun _ : ι => gaussianReal 0 1))
      < a := by
  set d : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hd
  set C : ℝ := K + d * K ^ 2 / 2 with hC
  set D : ℝ := max (C - B) 1 with hD
  have hDpos : 0 < D := lt_of_lt_of_le one_pos (le_max_right _ _)
  set s : ℝ := min (1 / 2) ((a - B) / (4 * D)) with hs
  have hspos : 0 < s := lt_min (by norm_num) (div_pos (by linarith) (by positivity))
  have hshalf : s ≤ 1 / 2 := min_le_left _ _
  set t : ℝ := 1 - s with ht
  have ht0 : 0 < t := by linarith
  have ht1 : t < 1 := by linarith
  have hsmall : s * (C - B) ≤ (a - B) / 4 := by
    have h1 : s * (C - B) ≤ s * D := mul_le_mul_of_nonneg_left (le_max_left _ _) hspos.le
    have h2 : s * D ≤ (a - B) / (4 * D) * D :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hDpos.le
    have h3 : (a - B) / (4 * D) * D = (a - B) / 4 := by field_simp
    linarith
  set L : ℝ := d * Real.log (2 * (Real.sqrt (1 - t))⁻¹) with hL
  have hlim : Tendsto (fun N : ℕ => L / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat L
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < (a - B) / 4 by linarith)),
    eventually_gt_atTop 0] with N hNL hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hI := integral_exp_laplace_le A K hA B hB ht0 ht1 hN
  have hpos : 0 < ∫ x : ι → ℝ, Real.exp (N * A (fun i => x i / Real.sqrt N))
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1) :=
    integral_exp_pos (integrable_exp_laplace A hAm K hA B hB hN)
  have h1t : 0 < 1 - t := by linarith
  have hsq1 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 h1t
  have hlog : Real.log (∫ x : ι → ℝ, Real.exp (N * A (fun i => x i / Real.sqrt N))
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) ≤
      N * (t * B + (1 - t) * K) + (L + N * (d * ((1 - t) * K ^ 2 / 2))) := by
    refine (Real.log_le_log hpos hI).trans (le_of_eq ?_)
    have hpos2 : 0 < 2 * (Real.sqrt (1 - t))⁻¹ * Real.exp (N * (1 - t) * K ^ 2 / 2) := by
      positivity
    rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos hpos2 _).ne', Real.log_exp, Real.log_pow,
      Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, hL, hd]
    ring
  have hdiv : (N : ℝ)⁻¹ * (N * (t * B + (1 - t) * K) + (L + N * (d * ((1 - t) * K ^ 2 / 2)))) =
      t * B + (1 - t) * C + L / N := by
    rw [hC]
    field_simp
    ring
  calc (N : ℝ)⁻¹ * Real.log _ ≤ (N : ℝ)⁻¹ * (N * (t * B + (1 - t) * K) +
        (L + N * (d * ((1 - t) * K ^ 2 / 2)))) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = t * B + (1 - t) * C + L / N := hdiv
    _ < a := by
        have : t * B + (1 - t) * C = B + s * (C - B) := by rw [ht]; ring
        linarith

/-- Eventually the normalized logarithm of the Laplace integral is above any level below the
value `B = A gs - ‖gs‖²/2` at a point `gs`, for continuous `A`. -/
theorem eventually_lt_log_integral_exp_laplace (A : (ι → ℝ) → ℝ) (hAc : Continuous A) (K : ℝ)
    (hA : ∀ g, |A g| ≤ K * (1 + ∑ i, |g i|)) (B : ℝ)
    (hB : ∀ g, A g - (∑ i, g i ^ 2) / 2 ≤ B) (gs : ι → ℝ) {a : ℝ}
    (ha : a < A gs - (∑ i, gs i ^ 2) / 2) :
    ∀ᶠ N : ℕ in atTop, a < (N : ℝ)⁻¹ * Real.log (∫ x : ι → ℝ,
      Real.exp (N * A (fun i => x i / Real.sqrt N))
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) := by
  set d : ℝ := ((Fintype.card ι : ℕ) : ℝ) with hd
  set η : ℝ := A gs - (∑ i, gs i ^ 2) / 2 - a with hη
  have hηpos : 0 < η := by linarith
  -- continuity radius
  obtain ⟨δ₁, hδ₁, hcont₁⟩ := Metric.continuousAt_iff.1 hAc.continuousAt (η / 4) (by linarith)
  set M : ℝ := ∑ i, |gs i| + d / 2 + 1 with hM
  have hMpos : 0 < M := by
    have : 0 ≤ ∑ i, |gs i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have : 0 ≤ d := Nat.cast_nonneg _
    linarith
  set δ : ℝ := min (min δ₁ 1) (η / (4 * M)) with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hδ₁ one_pos) (div_pos hηpos (by positivity))
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ2 : δ ≤ η / (4 * M) := min_le_right _ _
  have hδ3 : δ < δ₁ ∨ δ = δ₁ := lt_or_eq_of_le ((min_le_left _ _).trans (min_le_left _ _))
  have hcont : ∀ g : ι → ℝ, (∀ i, |g i - gs i| < δ) → A gs - η / 4 ≤ A g := by
    intro g hg
    have hdist : dist g gs < δ₁ := by
      rw [dist_pi_lt_iff hδ₁]
      intro i
      rw [Real.dist_eq]
      rcases hδ3 with h | h
      · exact (hg i).trans h
      · exact h ▸ hg i
    have := hcont₁ hdist
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  -- the shift of the quadratic term
  have hquad : (∑ i, (|gs i| + δ) ^ 2) / 2 ≤ (∑ i, gs i ^ 2) / 2 + η / 4 := by
    have h1 : ∑ i, (|gs i| + δ) ^ 2 = ∑ i, gs i ^ 2 + ∑ i, (2 * |gs i| * δ + δ ^ 2) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [add_sq, sq_abs]
      ring
    have h2 : ∑ i, (2 * |gs i| * δ + δ ^ 2) = 2 * δ * ∑ i, |gs i| + d * δ ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      ring
    have h3 : 2 * δ * ∑ i, |gs i| + d * δ ^ 2 ≤ 2 * δ * M := by
      have hdd : 0 ≤ d := Nat.cast_nonneg _
      have : d * δ ^ 2 ≤ d * δ := mul_le_mul_of_nonneg_left (by nlinarith) hdd
      rw [hM]
      nlinarith
    have h4 : 2 * δ * M ≤ η / 2 := by
      have : δ * M ≤ η / (4 * M) * M := mul_le_mul_of_nonneg_right hδ2 hMpos.le
      have h5 : η / (4 * M) * M = η / 4 := by field_simp
      linarith
    linarith
  set c : ℝ := 2 * δ * (Real.sqrt (2 * Real.pi))⁻¹ with hc
  have hcpos : 0 < c := by positivity
  have hlim : Tendsto (fun N : ℕ => d * Real.log c / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  filter_upwards [hlim.eventually (lt_mem_nhds (show (-(η / 4) : ℝ) < 0 by linarith)),
    eventually_gt_atTop 0] with N hNL hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 1 ≤ Real.sqrt N := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  have hlow := integral_exp_laplace_ge A hAc.measurable K hA B hB gs hδpos
    (ε := η / 4) hcont hN
  have hpos : 0 < ∫ x : ι → ℝ, Real.exp (N * A (fun i => x i / Real.sqrt N))
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1) :=
    integral_exp_pos (integrable_exp_laplace A hAc.measurable K hA B hB hN)
  have hbase : 0 < 2 * Real.sqrt N * δ * (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  have hlog := Real.log_le_log (by positivity) hlow
  rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos hbase _).ne', Real.log_exp, Real.log_pow] at hlog
  have hlogc : Real.log c ≤ Real.log (2 * Real.sqrt N * δ * (Real.sqrt (2 * Real.pi))⁻¹) := by
    refine Real.log_le_log hcpos ?_
    rw [hc]
    have : 2 * δ * (Real.sqrt (2 * Real.pi))⁻¹ * 1 ≤
        2 * δ * (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt N :=
      mul_le_mul_of_nonneg_left hsN (by positivity)
    nlinarith
  have hdnn : 0 ≤ d := Nat.cast_nonneg _
  have hlog2 : N * (A gs - η / 4 - (∑ i, (|gs i| + δ) ^ 2) / 2) + d * Real.log c ≤
      Real.log (∫ x : ι → ℝ, Real.exp (N * A (fun i => x i / Real.sqrt N))
        ∂(Measure.pi fun _ : ι => gaussianReal 0 1)) := by
    have := mul_le_mul_of_nonneg_left hlogc hdnn
    linarith
  have hfin : a < A gs - η / 4 - (∑ i, (|gs i| + δ) ^ 2) / 2 + d * Real.log c / N := by
    have : d * Real.log c / N > -(η / 4) := hNL
    linarith
  calc a < A gs - η / 4 - (∑ i, (|gs i| + δ) ^ 2) / 2 + d * Real.log c / N := hfin
    _ = (N : ℝ)⁻¹ * (N * (A gs - η / 4 - (∑ i, (|gs i| + δ) ^ 2) / 2) + d * Real.log c) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog2 (by positivity)

/-- **Laplace principle.** Let `A` be continuous with `|A g| ≤ K (1 + ∑ |gᵢ|)`, and let `gs` be a
maximizer of `A g - ‖g‖²/2`. For a standard Gaussian vector `x`,
`N⁻¹ log 𝔼 exp (N A (x / √N))` tends to `A gs - ‖gs‖²/2`. -/
theorem tendsto_log_integral_exp_laplace (A : (ι → ℝ) → ℝ) (hAc : Continuous A) (K : ℝ)
    (hA : ∀ g, |A g| ≤ K * (1 + ∑ i, |g i|)) (gs : ι → ℝ)
    (hmax : ∀ g, A g - (∑ i, g i ^ 2) / 2 ≤ A gs - (∑ i, gs i ^ 2) / 2) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * Real.log (∫ x : ι → ℝ,
      Real.exp (N * A (fun i => x i / Real.sqrt N)) ∂(Measure.pi fun _ : ι => gaussianReal 0 1)))
      atTop (𝓝 (A gs - (∑ i, gs i ^ 2) / 2)) := by
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · exact eventually_lt_log_integral_exp_laplace A hAc K hA _ hmax gs ha
  · exact eventually_log_integral_exp_laplace_lt A hAc.measurable K hA _ hmax ha

end ProbabilityTheory
