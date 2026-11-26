/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Variance derivative of a Gaussian average of a smooth function

For `f` with bounded first and second derivatives `f'`, `f''` and `γ = N(0,1)`, put
`G(w) = 𝔼 f(w z + h)`.  Stein's lemma gives `𝔼 [f'(w z + h) z] = w 𝔼 f''(w z + h)`, and
differentiation under the integral sign then gives `G'(w) = w 𝔼 f''(w z + h)`
(Talagrand, *Spin Glasses*, Eq. (1.75), after the substitution `w = β √x`).

## Main declarations

* `ProbabilityTheory.integral_deriv_comp_affine_mul_id_gaussianReal`: the Stein identity.
* `ProbabilityTheory.hasDerivAt_integral_comp_affine_gaussianReal`: the derivative in `w`.
* `ProbabilityTheory.integrable_gaussianReal_of_norm_le_pow`,
  `ProbabilityTheory.hasDerivAt_integral_comp_add_mul_gaussianReal`: integrability and
  differentiation of `t ↦ 𝔼 f (m t + σ t z)` for `f, f'` of polynomial growth.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

variable {f f' f'' : ℝ → ℝ} {C₁ C₂ : ℝ}

/-- **Derivative in the scale of an affine average:** if `f' ` is a bounded continuous derivative of
`f`, `|z|` is `μ`-integrable and `f(w z + h)` is integrable, then
`(d/dw) ∫ f(w z + h) dμ = ∫ f'(w z + h) z dμ`. -/
theorem hasDerivAt_integral_comp_mul_add {μ : Measure ℝ} (hf : ∀ y, HasDerivAt f (f' y) y)
    (hf'c : Continuous f') (hC₁ : ∀ y, |f' y| ≤ C₁) (hz : Integrable (fun z : ℝ => |z|) μ)
    (h w : ℝ) (hint : Integrable (fun z => f (w * z + h)) μ) :
    HasDerivAt (fun v => ∫ z, f (v * z + h) ∂μ) (∫ z, f' (w * z + h) * z ∂μ) w := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun y => (hf y).continuousAt
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ)
    (F := fun v z => f (v * z + h)) (F' := fun v z => f' (v * z + h) * z)
    univ_mem
    (Eventually.of_forall fun v =>
      (hfc.comp (by fun_prop : Continuous fun z : ℝ => v * z + h)).aestronglyMeasurable)
    hint
    ((hf'c.comp (by fun_prop : Continuous fun z : ℝ => w * z + h)).mul
      continuous_id').aestronglyMeasurable
    (bound := fun z => C₁ * |z|)
    (ae_of_all _ fun z v _ => ?_) (hz.const_mul C₁)
    (ae_of_all _ fun z v _ => ?_)).2
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hC₁ _) (abs_nonneg _)
  · have hl : HasDerivAt (fun v : ℝ => v * z + h) z v := by
      simpa using ((hasDerivAt_id' v).mul_const z).add_const h
    exact (hf (v * z + h)).comp v hl

/-- **Stein's lemma for an affine Gaussian argument:** if `f'` has a bounded continuous derivative
`f''` and is itself bounded, then `𝔼 [f'(w z + h) z] = w 𝔼 f''(w z + h)` for `z ~ N(0,1)`. -/
theorem integral_deriv_comp_affine_mul_id_gaussianReal (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hf''c : Continuous f'') (hC₁ : ∀ y, |f' y| ≤ C₁) (hC₂ : ∀ y, |f'' y| ≤ C₂) (h w : ℝ) :
    ∫ z, f' (w * z + h) * z ∂(gaussianReal 0 1) =
      w * ∫ z, f'' (w * z + h) ∂(gaussianReal 0 1) := by
  have hf'c : Continuous f' := continuous_iff_continuousAt.2 fun y => (hf' y).continuousAt
  have h1 : Integrable (fun z : ℝ => z * f' (h + w * z)) (gaussianReal 0 1) := by
    refine ((IsGaussian.integrable_id (μ := gaussianReal 0 1)).norm.const_mul C₁).mono'
      ((continuous_id'.mul (hf'c.comp (by fun_prop : Continuous fun z : ℝ => h + w * z)))
        |>.aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul, mul_comm, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC₁ _) (abs_nonneg _)
  have h2 : Integrable (fun z : ℝ => f'' (h + w * z)) (gaussianReal 0 1) :=
    (integrable_const C₂).mono'
      ((hf''c.comp (by fun_prop : Continuous fun z : ℝ => h + w * z)).aestronglyMeasurable)
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hC₂ _)
  have := integral_id_mul_comp_affine_gaussianReal 1 hf' h w h1 h2
  simp only [NNReal.coe_one, one_mul, add_comm h] at this ⊢
  simpa [mul_comm] using this

/-- **Derivative of the Gaussian average in the standard deviation:** under the assumptions of
`integral_deriv_comp_affine_mul_id_gaussianReal`, and if `f` is an antiderivative of `f'` with
`f(w z + h)` integrable, `(d/dw) 𝔼 f(w z + h) = w 𝔼 f''(w z + h)`. -/
theorem hasDerivAt_integral_comp_affine_gaussianReal (hf : ∀ y, HasDerivAt f (f' y) y)
    (hf' : ∀ y, HasDerivAt f' (f'' y) y) (hf''c : Continuous f'') (hC₁ : ∀ y, |f' y| ≤ C₁)
    (hC₂ : ∀ y, |f'' y| ≤ C₂) (h w : ℝ)
    (hint : Integrable (fun z => f (w * z + h)) (gaussianReal 0 1)) :
    HasDerivAt (fun v => ∫ z, f (v * z + h) ∂(gaussianReal 0 1))
      (w * ∫ z, f'' (w * z + h) ∂(gaussianReal 0 1)) w := by
  have hf'c : Continuous f' := continuous_iff_continuousAt.2 fun y => (hf' y).continuousAt
  have h_diff := hasDerivAt_integral_comp_mul_add hf hf'c hC₁
    (by simpa only [Real.norm_eq_abs, id] using
      (IsGaussian.integrable_id (μ := gaussianReal 0 1)).norm) h w hint
  rwa [integral_deriv_comp_affine_mul_id_gaussianReal hf' hf''c hC₁ hC₂ h w] at h_diff

/-- A function bounded by `C (1 + |z|) ^ k` is integrable against a standard Gaussian. -/
theorem integrable_gaussianReal_of_norm_le_pow {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (hg : AEStronglyMeasurable g (gaussianReal 0 1)) {C : ℝ} {k : ℕ}
    (h : ∀ z, ‖g z‖ ≤ C * (1 + |z|) ^ k) : Integrable g (gaussianReal 0 1) := by
  have hm : MemLp (fun z : ℝ => 1 + ‖z‖) k (gaussianReal 0 1) :=
    (memLp_const 1).add (memLp_id_gaussianReal (μ := 0) (v := 1) k).norm
  refine (hm.integrable_norm_pow'.const_mul C).mono' hg (ae_of_all _ fun z => (h z).trans_eq ?_)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]

/-- **Differentiation of a Gaussian average along a curve of affine maps:** if `f` has derivative
`f'` and both are of polynomial growth, then
`d/dt 𝔼 f (m t + σ t z) = 𝔼 [f' (m t + σ t z) (m' t + σ' t z)]`. -/
theorem hasDerivAt_integral_comp_add_mul_gaussianReal {f f' m σ m' σ' : ℝ → ℝ} {C t : ℝ}
    {k : ℕ} (hf : ∀ y, HasDerivAt f (f' y) y) (hf'm : Measurable f')
    (hC : ∀ y, |f y| ≤ C * (1 + |y|) ^ k) (hC' : ∀ y, |f' y| ≤ C * (1 + |y|) ^ k)
    (hm : ∀ᶠ s in 𝓝 t, HasDerivAt m (m' s) s) (hσ : ∀ᶠ s in 𝓝 t, HasDerivAt σ (σ' s) s)
    (hm' : ContinuousAt m' t) (hσ' : ContinuousAt σ' t) :
    HasDerivAt (fun s => ∫ z, f (m s + σ s * z) ∂(gaussianReal 0 1))
      (∫ z, f' (m t + σ t * z) * (m' t + σ' t * z) ∂(gaussianReal 0 1)) t := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun y => (hf y).continuousAt
  have hC0 : 0 ≤ C := by simpa using (abs_nonneg _).trans (hC 0)
  set B : ℝ := |m t| + |σ t| + |m' t| + |σ' t| + 1 with hB
  have hB0 : 0 ≤ B := by positivity
  have hnear : ∀ᶠ s in 𝓝 t, HasDerivAt m (m' s) s ∧ HasDerivAt σ (σ' s) s ∧ |m s| ≤ B ∧
      |σ s| ≤ B ∧ |m' s| ≤ B ∧ |σ' s| ≤ B := by
    have key : ∀ g : ℝ → ℝ, ContinuousAt g t → |g t| + 1 ≤ B → ∀ᶠ s in 𝓝 t, |g s| ≤ B :=
      fun g hg hle => (hg.abs.eventually_lt_const (lt_add_one _)).mono
        fun s hs => hs.le.trans hle
    have h1 := abs_nonneg (m t)
    have h2 := abs_nonneg (σ t)
    have h3 := abs_nonneg (m' t)
    have h4 := abs_nonneg (σ' t)
    filter_upwards [hm, hσ, key m hm.self_of_nhds.continuousAt (by linarith),
      key σ hσ.self_of_nhds.continuousAt (by linarith), key m' hm' (by linarith),
      key σ' hσ' (by linarith)] with s a b c d e g using ⟨a, b, c, d, e, g⟩
  have haff : ∀ a b : ℝ, Continuous fun z : ℝ => a + b * z := fun a b => by fun_prop
  have hpow : ∀ a b : ℝ, |a| ≤ B → |b| ≤ B → ∀ z : ℝ,
      C * (1 + |a + b * z|) ^ k ≤ C * (1 + B) ^ k * (1 + |z|) ^ k := fun a b ha hb z => by
    rw [mul_assoc, ← mul_pow]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ k) hC0
    have h1 : |a + b * z| ≤ B + B * |z| :=
      (abs_add_le _ _).trans (add_le_add ha (by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)))
    have h2 := abs_nonneg z
    nlinarith
  have ht := hnear.self_of_nhds
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal 0 1)
    (F := fun s z => f (m s + σ s * z))
    (F' := fun s z => f' (m s + σ s * z) * (m' s + σ' s * z))
    (bound := fun z => C * (1 + B) ^ k * B * (1 + |z|) ^ (k + 1)) hnear
    (Eventually.of_forall fun s => (hfc.comp (haff _ _)).aestronglyMeasurable)
    (integrable_gaussianReal_of_norm_le_pow (hfc.comp (haff _ _)).aestronglyMeasurable
      (C := C * (1 + B) ^ k) (k := k) fun z => (hC _).trans (hpow _ _ ht.2.2.1 ht.2.2.2.1 z))
    ((hf'm.comp (haff _ _).measurable).mul (haff _ _).measurable).aestronglyMeasurable
    (ae_of_all _ fun z s hs => ?_)
    (integrable_gaussianReal_of_norm_le_pow
      (by fun_prop : Continuous fun z : ℝ => C * (1 + B) ^ k * B * (1 + |z|) ^ (k + 1)
        ).aestronglyMeasurable (C := C * (1 + B) ^ k * B) (k := k + 1)
      fun z => (Real.norm_of_nonneg (by positivity)).le)
    (ae_of_all _ fun z s hs => ?_)).2
  · obtain ⟨-, -, h1, h2, h3, h4⟩ := hs
    have h5 : |m' s + σ' s * z| ≤ B * (1 + |z|) := by
      rw [mul_add, mul_one]
      exact (abs_add_le _ _).trans (add_le_add h3 (by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right h4 (abs_nonneg _)))
    rw [Real.norm_eq_abs, abs_mul]
    refine (mul_le_mul ((hC' _).trans (hpow _ _ h1 h2 z)) h5 (abs_nonneg _)
      (by positivity)).trans_eq ?_
    ring
  · exact (hf _).comp s (hs.1.add (hs.2.1.mul_const z))

end ProbabilityTheory
