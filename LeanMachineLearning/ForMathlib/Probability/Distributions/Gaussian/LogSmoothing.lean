/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.LogConcaveMarginal
public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.MillsRatio

/-!
# The Gaussian log-Laplace smoothing of a potential

For a potential `u ≤ 0` with bounded first two derivatives, `x ↦ log 𝔼 exp u (x + c ξ)`, where `ξ`
is a standard Gaussian, is twice differentiable; its derivative is nonnegative when `u` is
nondecreasing, and its second derivative is nonpositive when `u` is concave (Talagrand,
*Spin Glasses*, Vol. I, Lemma 3.3.10 and Lemma 3.2.3).

## Main declarations

* `ProbabilityTheory.hasDerivAt_integral_mul_exp_comp_add_gaussianReal`: differentiation of
  `x ↦ ∫ f (x + c ξ) exp (u (x + c ξ))`.
* `ProbabilityTheory.hasDerivAt_log_integral_exp_comp_add_gaussianReal`: the first two
  derivatives of the smoothing.
* `ProbabilityTheory.integral_deriv_two_add_sq_div_le_integral_sq_div`: the averaged inequality
  behind `r̄ ≤ r` (Lemma 3.2.3).
* `ProbabilityTheory.measurable_integral_mul_exp_comp_add_gaussianReal`,
  `ProbabilityTheory.abs_integral_mul_exp_comp_add_div_le`: measurability and bounds for the
  ratios `A / Z`, `K / Z`.
* `ProbabilityTheory.exists_sq_mul_integral_deriv_mul_exp_div_le`: Lemma 3.3.8 for the smoothing,
  `(c A / Z)² ≤ (max ((τ - y) / c) 0)² + L`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology

namespace ProbabilityTheory

variable {u : ℝ → ℝ}

/-- For `u ≤ 0` and bounded `f`, `ξ ↦ f (y + c ξ) e^{u (y + c ξ)}` is integrable. -/
theorem integrable_mul_exp_comp_add_gaussianReal (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0)
    {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) (y c : ℝ) :
    Integrable (fun ξ => f (y + c * ξ) * Real.exp (u (y + c * ξ))) (gaussianReal 0 1) := by
  have haff : Measurable fun ξ : ℝ => y + c * ξ := by fun_prop
  refine Integrable.of_bound ((hf.comp haff).mul (hu.comp haff).exp).aestronglyMeasurable B
    (ae_of_all _ fun ξ => ?_)
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  exact (mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.2 (hu0 _))).trans (hB _)

/-- For `u ≤ 0`, the normalisation `𝔼 e^{u (y + c ξ)}` is positive. -/
theorem integral_exp_comp_add_gaussianReal_pos (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0)
    (y c : ℝ) : 0 < ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1) := by
  refine integral_exp_pos ?_
  simpa only [one_mul] using integrable_mul_exp_comp_add_gaussianReal hu hu0
    (f := fun _ => 1) measurable_const (B := 1) (fun _ => by simp) y c

/-- The ratio `𝔼 [f e^{u}] / 𝔼 e^{u}` at `y + c ξ` is bounded by any bound of `|f|`. -/
theorem abs_integral_mul_exp_comp_add_div_le (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0)
    {f : ℝ → ℝ} {B : ℝ} (hB : ∀ x, |f x| ≤ B) (y c : ℝ) :
    |(∫ ξ, f (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) /
      ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)| ≤ B := by
  have hZ := integral_exp_comp_add_gaussianReal_pos hu hu0 y c
  have hexpi : Integrable (fun ξ => Real.exp (u (y + c * ξ))) (gaussianReal 0 1) := by
    simpa only [one_mul] using integrable_mul_exp_comp_add_gaussianReal hu hu0
      (f := fun _ => 1) measurable_const (B := 1) (fun _ => by simp) y c
  rw [abs_div, abs_of_pos hZ, div_le_iff₀ hZ, ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hexpi.const_mul B) (ae_of_all _ fun ξ => ?_)
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hB _) (Real.exp_pos _).le

/-- Measurability in `ω` of `∫ f (a ω + c ξ) e^{u (a ω + c ξ)}`. -/
theorem measurable_integral_mul_exp_comp_add_gaussianReal {Ω : Type*} [MeasurableSpace Ω]
    (hu : Measurable u) {f : ℝ → ℝ} (hf : Measurable f) {a : Ω → ℝ} (ha : Measurable a)
    (c : ℝ) : Measurable fun ω =>
      ∫ ξ, f (a ω + c * ξ) * Real.exp (u (a ω + c * ξ)) ∂(gaussianReal 0 1) := by
  have hshift : Measurable fun p : Ω × ℝ => a p.1 + c * p.2 :=
    (ha.comp measurable_fst).add (measurable_snd.const_mul c)
  exact (((hf.comp hshift).mul (hu.comp hshift).exp).stronglyMeasurable.integral_prod_right'
    (ν := gaussianReal 0 1)).measurable

/-- Differentiation under the Gaussian integral: if `u ≤ 0` and `f` are differentiable with
`|u'| ≤ D`, `|f| ≤ B`, `|f'| ≤ B'`, then
`d/dx ∫ f (x + c ξ) e^{u (x + c ξ)} = ∫ (f' + f u') (x + c ξ) e^{u (x + c ξ)}`. -/
theorem hasDerivAt_integral_mul_exp_comp_add_gaussianReal (hu : Differentiable ℝ u)
    (hu0 : ∀ x, u x ≤ 0) {D : ℝ} (hD : ∀ x, |deriv u x| ≤ D) {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) {B B' : ℝ} (hB : ∀ x, |f x| ≤ B) (hB' : ∀ x, |deriv f x| ≤ B')
    (c x : ℝ) :
    HasDerivAt (fun x => ∫ ξ, f (x + c * ξ) * Real.exp (u (x + c * ξ)) ∂(gaussianReal 0 1))
      (∫ ξ, (deriv f (x + c * ξ) + f (x + c * ξ) * deriv u (x + c * ξ)) *
        Real.exp (u (x + c * ξ)) ∂(gaussianReal 0 1)) x := by
  have hum : Measurable u := hu.continuous.measurable
  have hfm : Measurable f := hf.continuous.measurable
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have haff : ∀ y : ℝ, Measurable fun ξ : ℝ => y + c * ξ := fun y => by fun_prop
  have hexp : ∀ y, Real.exp (u y) ≤ 1 := fun y => Real.exp_le_one_iff.2 (hu0 y)
  have hmeas : ∀ y, AEStronglyMeasurable (fun ξ => f (y + c * ξ) * Real.exp (u (y + c * ξ)))
      (gaussianReal 0 1) := fun y =>
    ((hfm.comp (haff y)).mul (hum.comp (haff y)).exp).aestronglyMeasurable
  have hint : Integrable (fun ξ => f (x + c * ξ) * Real.exp (u (x + c * ξ)))
      (gaussianReal 0 1) :=
    Integrable.of_bound (hmeas x) B (ae_of_all _ fun ξ => by
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hexp _)).trans (hB _))
  have hd : ∀ y ξ : ℝ, HasDerivAt (fun y => f (y + c * ξ) * Real.exp (u (y + c * ξ)))
      ((deriv f (y + c * ξ) + f (y + c * ξ) * deriv u (y + c * ξ)) *
        Real.exp (u (y + c * ξ))) y := fun y ξ => by
    have h1 := (hf (y + c * ξ)).hasDerivAt.comp_add_const y (c * ξ)
    have h2 := ((hu (y + c * ξ)).hasDerivAt.comp_add_const y (c * ξ)).exp
    refine (h1.mul h2).congr_deriv ?_
    ring
  have hdm : AEStronglyMeasurable (fun ξ => (deriv f (x + c * ξ) +
      f (x + c * ξ) * deriv u (x + c * ξ)) * Real.exp (u (x + c * ξ))) (gaussianReal 0 1) :=
    ((((measurable_deriv f).comp (haff x)).add ((hfm.comp (haff x)).mul
      ((measurable_deriv u).comp (haff x)))).mul
        (hum.comp (haff x)).exp).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal 0 1)
    (F := fun y ξ => f (y + c * ξ) * Real.exp (u (y + c * ξ)))
    (bound := fun _ => B' + B * D) Filter.univ_mem (Filter.Eventually.of_forall hmeas) hint hdm
    (ae_of_all _ fun ξ y _ => ?_) (integrable_const _) (ae_of_all _ fun ξ y _ => hd y ξ)).2
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_eq_abs]
  refine (mul_le_of_le_one_right (abs_nonneg _) (hexp _)).trans ((abs_add_le _ _).trans
    (add_le_add (hB' _) ?_))
  rw [abs_mul]
  exact mul_le_mul (hB _) (hD _) (abs_nonneg _) hB0

/-- **Talagrand, Lemma 3.3.10:** the first two derivatives of `v x = log 𝔼 e^{u (x + c ξ)}` are
`v' = A / Z` and `v'' = K / Z - (A / Z)²`, where `Z = 𝔼 e^{u}`, `A = 𝔼 u' e^{u}` and
`K = 𝔼 (u'' + u'²) e^{u}`. -/
theorem hasDerivAt_log_integral_exp_comp_add_gaussianReal (hu : Differentiable ℝ u)
    (hu' : Differentiable ℝ (deriv u)) (hu0 : ∀ x, u x ≤ 0) {D D₂ : ℝ}
    (hD : ∀ x, |deriv u x| ≤ D) (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) (c x : ℝ) :
    ∀ Z A K : ℝ → ℝ,
      (∀ y, Z y = ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) →
      (∀ y, A y = ∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) →
      (∀ y, K y = ∫ ξ, (deriv (deriv u) (y + c * ξ) + deriv u (y + c * ξ) ^ 2) *
        Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) →
      0 < Z x ∧ HasDerivAt (fun y => Real.log (Z y)) (A x / Z x) x ∧
        HasDerivAt (fun y => A y / Z y) (K x / Z x - (A x / Z x) ^ 2) x := by
  intro Z A K hZ hA hK
  have hum : Measurable u := hu.continuous.measurable
  have hZ0 : ∀ y, 0 < Z y := fun y => by
    rw [hZ]
    exact integral_exp_comp_add_gaussianReal_pos hum hu0 y c
  have hZd : HasDerivAt Z (A x) x := by
    have h := hasDerivAt_integral_mul_exp_comp_add_gaussianReal hu hu0 hD
      (f := fun _ => 1) (differentiable_const 1) (B := 1) (B' := 0) (fun _ => by simp)
      (fun _ => by simp) c x
    simp only [one_mul, deriv_const', zero_add] at h
    rw [show Z = _ from funext hZ, hA]
    exact h
  have hAd : HasDerivAt A (K x) x := by
    have h := hasDerivAt_integral_mul_exp_comp_add_gaussianReal hu hu0 hD
      (f := deriv u) hu' hD hD₂ c x
    simp only [← sq] at h
    rw [show A = _ from funext hA, hK]
    exact h
  refine ⟨hZ0 x, hZd.log (hZ0 x).ne', ?_⟩
  refine (hAd.div hZd (hZ0 x).ne').congr_deriv ?_
  have := (hZ0 x).ne'
  field_simp

/-- **The averaged form of `r̄ ≤ r`** (Talagrand, Lemma 3.2.3): for concave `u ≤ 0` with bounded
first two derivatives and any measurable shift `a` on a finite measure space,
`∫ K (a ω) / Z (a ω) ≤ ∫ (A (a ω) / Z (a ω))²`, in the notation of
`hasDerivAt_log_integral_exp_comp_add_gaussianReal`. Both integrands are integrable. -/
theorem integral_deriv_two_add_sq_div_le_integral_sq_div {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (hu : ConcaveOn ℝ univ u) (hu0 : ∀ x, u x ≤ 0)
    (hu1 : Differentiable ℝ u) (hu2 : Differentiable ℝ (deriv u)) {D D₂ : ℝ}
    (hD : ∀ x, |deriv u x| ≤ D) (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) {a : Ω → ℝ}
    (ha : Measurable a) (c : ℝ) :
    ∫ ω, (∫ ξ, (deriv (deriv u) (a ω + c * ξ) + deriv u (a ω + c * ξ) ^ 2) *
          Real.exp (u (a ω + c * ξ)) ∂(gaussianReal 0 1)) /
        (∫ ξ, Real.exp (u (a ω + c * ξ)) ∂(gaussianReal 0 1)) ∂μ ≤
      ∫ ω, ((∫ ξ, deriv u (a ω + c * ξ) * Real.exp (u (a ω + c * ξ)) ∂(gaussianReal 0 1)) /
        ∫ ξ, Real.exp (u (a ω + c * ξ)) ∂(gaussianReal 0 1)) ^ 2 ∂μ := by
  have hum : Measurable u := hu1.continuous.measurable
  have hmeas := fun (f : ℝ → ℝ) (hf : Measurable f) =>
    measurable_integral_mul_exp_comp_add_gaussianReal hum hf ha c
  have hZm : Measurable fun ω => ∫ ξ, Real.exp (u (a ω + c * ξ)) ∂(gaussianReal 0 1) := by
    simpa only [one_mul] using hmeas (fun _ => 1) measurable_const
  have hratio := fun (f : ℝ → ℝ) (B : ℝ) (hf : ∀ y, |f y| ≤ B) (y : ℝ) =>
    abs_integral_mul_exp_comp_add_div_le hum hu0 hf y c
  have hKb : ∀ y, |deriv (deriv u) y + deriv u y ^ 2| ≤ D₂ + D ^ 2 := fun y => by
    refine (abs_add_le _ _).trans (add_le_add (hD₂ _) ?_)
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hD _) 2
  refine integral_mono ?_ ?_ fun ω =>
    integral_deriv_two_add_sq_mul_exp_div_le_sq hu hu0 hu1 hu2 hD hD₂ (a ω) c
  · exact Integrable.of_bound ((hmeas _ ((measurable_deriv (deriv u)).add
      ((measurable_deriv u).pow_const 2))).div hZm).aestronglyMeasurable (D₂ + D ^ 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        exact hratio (fun y => deriv (deriv u) y + deriv u y ^ 2) _ hKb (a ω))
  · exact Integrable.of_bound (((hmeas _ (measurable_deriv u)).div hZm).pow_const 2
      ).aestronglyMeasurable (D ^ 2) (ae_of_all _ fun ω => by
        rw [norm_pow, Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hratio (deriv u) D hD (a ω)) 2)

/-- **Lemma 3.3.8 for the smoothing:** there is a universal `L` with
`(c A y / Z y)² ≤ (max ((τ - y) / c) 0)² + L` for every nondecreasing `u ≤ 0` vanishing on
`[τ, ∞)`, where `Z = 𝔼 e^{u}` and `A = 𝔼 u' e^{u}` at `y + c ξ`. -/
theorem exists_sq_mul_integral_deriv_mul_exp_div_le :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ u : ℝ → ℝ, Differentiable ℝ u → Monotone u → (∀ x, u x ≤ 0) →
      ∀ τ : ℝ, (∀ x, τ ≤ x → u x = 0) → ∀ D : ℝ, (∀ x, |deriv u x| ≤ D) → ∀ c : ℝ, 0 < c →
      ∀ y : ℝ,
        (c * (∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) /
            ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) ^ 2 ≤
          max ((τ - y) / c) 0 ^ 2 + L := by
  obtain ⟨L, hL0, hL⟩ := exists_sq_integral_id_mul_exp_div_le
  refine ⟨L, hL0, fun u hu hmono hu0 τ hτ D hD c hc y => ?_⟩
  have hum : Measurable u := hu.continuous.measurable
  have h := hL (fun ξ => u (y + c * ξ)) ((τ - y) / c)
    (fun x x' hx => hmono (add_le_add le_rfl (mul_le_mul_of_nonneg_left hx hc.le)))
    (fun ξ => hu0 _) (fun ξ hξ => hτ _ (by rw [div_le_iff₀ hc] at hξ; linarith))
  have hIBP : ∫ ξ, ξ * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1) =
      c * ∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1) := by
    have hd : ∀ ξ, HasDerivAt (fun ξ => Real.exp (u (y + c * ξ)))
        (c * (deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)))) ξ := fun ξ => by
      have h1 : HasDerivAt (fun ξ => y + c * ξ) c ξ := by
        simpa using ((hasDerivAt_id ξ).const_mul c).const_add y
      refine (((hu _).hasDerivAt.comp ξ h1).exp).congr_deriv ?_
      simp only [Function.comp_apply]
      ring
    have hid : Integrable (fun ξ : ℝ => ξ) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal 1).integrable le_rfl
    have hwi : Integrable (fun ξ => ξ * Real.exp (u (y + c * ξ))) (gaussianReal 0 1) := by
      refine hid.abs.mono' (measurable_id.mul
        (hum.comp (by fun_prop : Measurable fun ξ : ℝ => y + c * ξ)).exp).aestronglyMeasurable
        (ae_of_all _ fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.2 (hu0 _))
    rw [integral_id_mul_gaussianReal_eq 1 hd hwi
      ((integrable_mul_exp_comp_add_gaussianReal hum hu0 (measurable_deriv u) hD y c).const_mul c),
      NNReal.coe_one, one_mul, integral_const_mul]
  rwa [hIBP] at h

end ProbabilityTheory
