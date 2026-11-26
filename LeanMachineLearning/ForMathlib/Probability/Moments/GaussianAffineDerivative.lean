/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import LeanMachineLearning.ForMathlib.MeasureTheory.Function.AEStronglyMeasurableDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Differentiation of averages along affine maps, and the Gaussian variance derivative

For `γ = N(0,1)` put `G(w) = 𝔼 f(w z + h)`.  Stein's lemma gives
`𝔼 [z f'(w z + h)] = w 𝔼 f''(w z + h)`, and differentiation under the integral sign then gives
`G'(w) = w 𝔼 f''(w z + h)` (Talagrand, *Spin Glasses*, Eq. (1.75), after the substitution
`w = β √x`).  The differentiation step is proved for any measure on `ℝ`, for vector-valued `f`
and along an arbitrary curve `t ↦ (m t, σ t)` of affine maps.

## Main declarations

* `ProbabilityTheory.hasDerivAt_integral_comp_add_mul_of_dominated`: differentiation of
  `t ↦ ∫ f (m t + σ t z) dμ` under an integrable domination.
* `ProbabilityTheory.hasDerivAt_integral_comp_mul_add_smul`,
  `ProbabilityTheory.hasDerivAt_integral_comp_add_mul`: its consequences for a bounded derivative
  and for polynomial growth against a finite measure with enough moments.
* `ProbabilityTheory.hasDerivAt_integral_comp_add_mul_gaussianReal_smul`: the Gaussian case.
* `ProbabilityTheory.integral_id_smul_deriv_comp_affine_gaussianReal`: the Stein identity.
* `ProbabilityTheory.hasDerivAt_integral_comp_affine_gaussianReal_smul`: the derivative in `w`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace ProbabilityTheory

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Differentiation of an average along a curve of affine maps, dominated form:** let `f`, with
values in a normed space, have derivative `f'`, let `m` and `σ` be differentiable on a
neighbourhood `S` of `t`, and let `bound` be a `μ`-integrable bound on the derivative integrand
over `S`. Then `d/dt ∫ f (m t + σ t z) dμ = ∫ (m' t + σ' t z) • f' (m t + σ t z) dμ`. -/
theorem hasDerivAt_integral_comp_add_mul_of_dominated {μ : Measure ℝ} {f f' : ℝ → F}
    {m σ m' σ' bound : ℝ → ℝ} {S : Set ℝ} {t : ℝ} (hf : ∀ y, HasDerivAt f (f' y) y)
    (hS : S ∈ 𝓝 t) (hm : ∀ s ∈ S, HasDerivAt m (m' s) s) (hσ : ∀ s ∈ S, HasDerivAt σ (σ' s) s)
    (hint : Integrable (fun z => f (m t + σ t * z)) μ)
    (hbound : ∀ᵐ z ∂μ, ∀ s ∈ S, ‖(m' s + σ' s * z) • f' (m s + σ s * z)‖ ≤ bound z)
    (hboundint : Integrable bound μ) :
    HasDerivAt (fun s => ∫ z, f (m s + σ s * z) ∂μ)
      (∫ z, (m' t + σ' t * z) • f' (m t + σ t * z) ∂μ) t := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun y => (hf y).continuousAt
  have hf'm : StronglyMeasurable f' := stronglyMeasurable_of_forall_hasDerivAt hf
  have haff : ∀ a b : ℝ, Continuous fun z : ℝ => a + b * z := fun a b => by fun_prop
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun s z => f (m s + σ s * z))
    (F' := fun s z => (m' s + σ' s * z) • f' (m s + σ s * z)) hS
    (Eventually.of_forall fun s => (hfc.comp (haff _ _)).aestronglyMeasurable) hint
    ((haff _ _).aestronglyMeasurable.smul
      (hf'm.comp_measurable (haff _ _).measurable).aestronglyMeasurable) hbound hboundint
    (ae_of_all _ fun z s hs => (hf _).scomp s ((hm s hs).add ((hσ s hs).mul_const z)))).2

/-- **Derivative in the scale of an affine average, vector-valued:** if `f'` is a bounded
derivative of `f`, `|z|` is `μ`-integrable and `f(w z + h)` is integrable, then
`(d/dw) ∫ f(w z + h) dμ = ∫ z • f'(w z + h) dμ`. -/
theorem hasDerivAt_integral_comp_mul_add_smul {μ : Measure ℝ} {f f' : ℝ → F} {C : ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hC : ∀ y, ‖f' y‖ ≤ C)
    (hz : Integrable (fun z : ℝ => |z|) μ) (h w : ℝ)
    (hint : Integrable (fun z => f (w * z + h)) μ) :
    HasDerivAt (fun v => ∫ z, f (v * z + h) ∂μ) (∫ z, z • f' (w * z + h) ∂μ) w := by
  have := hasDerivAt_integral_comp_add_mul_of_dominated (μ := μ) (m := fun _ => h) (σ := id)
    (m' := fun _ => 0) (σ' := fun _ => 1) (bound := fun z => |z| * C) (t := w) hf univ_mem
    (fun s _ => hasDerivAt_const s h) (fun s _ => hasDerivAt_id s)
    (by simpa only [id, add_comm h] using hint)
    (ae_of_all _ fun z s _ => by
      rw [zero_add, one_mul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _))
    (hz.mul_const C)
  simpa only [id, zero_add, one_mul, add_comm h] using this

/-- **Derivative in the scale of an affine average:** the real-valued case of
`hasDerivAt_integral_comp_mul_add_smul`. -/
theorem hasDerivAt_integral_comp_mul_add {μ : Measure ℝ} {f f' : ℝ → ℝ} {C₁ : ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hC₁ : ∀ y, |f' y| ≤ C₁)
    (hz : Integrable (fun z : ℝ => |z|) μ) (h w : ℝ)
    (hint : Integrable (fun z => f (w * z + h)) μ) :
    HasDerivAt (fun v => ∫ z, f (v * z + h) ∂μ) (∫ z, f' (w * z + h) * z ∂μ) w := by
  simpa only [smul_eq_mul, mul_comm] using
    hasDerivAt_integral_comp_mul_add_smul hf hC₁ hz h w hint

/-- A function bounded by `C (1 + |z|) ^ k` is integrable against a standard Gaussian. -/
theorem integrable_gaussianReal_of_norm_le_pow {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (hg : AEStronglyMeasurable g (gaussianReal 0 1)) {C : ℝ} {k : ℕ}
    (h : ∀ z, ‖g z‖ ≤ C * (1 + |z|) ^ k) : Integrable g (gaussianReal 0 1) := by
  have hm : MemLp (fun z : ℝ => 1 + ‖z‖) k (gaussianReal 0 1) :=
    (memLp_const 1).add (memLp_id_gaussianReal (μ := 0) (v := 1) k).norm
  refine (hm.integrable_norm_pow'.const_mul C).mono' hg (ae_of_all _ fun z => (h z).trans_eq ?_)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]

/-- A function whose derivative has growth at most `(1 + |y|) ^ k` has growth at most
`(1 + |y|) ^ (k + 1)`. -/
theorem norm_le_mul_one_add_abs_pow_of_hasDerivAt {f f' : ℝ → F}
    (hf : ∀ y, HasDerivAt f (f' y) y) {C : ℝ} {k : ℕ} (hC : ∀ y, ‖f' y‖ ≤ C * (1 + |y|) ^ k)
    (y : ℝ) : ‖f y‖ ≤ (‖f 0‖ + C) * (1 + |y|) ^ (k + 1) := by
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  have h := (convex_uIcc (0 : ℝ) y).norm_image_sub_le_of_norm_hasDerivWithin_le (f := f)
    (f' := f') (C := C * (1 + |y|) ^ k) (fun x _ => (hf x).hasDerivWithinAt)
    (fun x hx => (hC x).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (by simpa using Set.abs_sub_left_of_mem_uIcc hx) k) hC0))
    Set.left_mem_uIcc Set.right_mem_uIcc
  rw [sub_zero, Real.norm_eq_abs] at h
  have h1 : 1 ≤ (1 + |y|) ^ (k + 1) := one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg y))
  have h2 : C * (1 + |y|) ^ k * |y| ≤ C * (1 + |y|) ^ (k + 1) := by
    rw [pow_succ, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity)
  calc ‖f y‖ ≤ ‖f 0‖ + ‖f y - f 0‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ ‖f 0‖ * (1 + |y|) ^ (k + 1) + C * (1 + |y|) ^ (k + 1) :=
        add_le_add (le_mul_of_one_le_right (norm_nonneg _) h1) (h.trans h2)
    _ = (‖f 0‖ + C) * (1 + |y|) ^ (k + 1) := by ring

/-- A function of polynomial growth at an affine argument, times an affine factor, is integrable
against a standard Gaussian. -/
theorem integrable_add_mul_smul_comp_add_mul_gaussianReal {g : ℝ → F} (hg : StronglyMeasurable g)
    {C : ℝ} {k : ℕ} (hC : ∀ y, ‖g y‖ ≤ C * (1 + |y|) ^ k) (a b c d : ℝ) :
    Integrable (fun z => (c + d * z) • g (a + b * z)) (gaussianReal 0 1) := by
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  have haff : ∀ (a b z : ℝ), |a + b * z| ≤ |a| + |b| * |z| := fun a b z =>
    (abs_add_le _ _).trans_eq (by rw [abs_mul])
  have hm : AEStronglyMeasurable (fun z : ℝ => (c + d * z) • g (a + b * z)) (gaussianReal 0 1) :=
    (by fun_prop : Continuous fun z : ℝ => c + d * z).aestronglyMeasurable.smul
      (hg.comp_measurable (by fun_prop : Measurable fun z : ℝ => a + b * z)).aestronglyMeasurable
  refine integrable_gaussianReal_of_norm_le_pow hm
    (C := (|c| + |d|) * (C * (1 + |a| + |b|) ^ k)) (k := k + 1) fun z => ?_
  have h1 : 1 + |a + b * z| ≤ (1 + |a| + |b|) * (1 + |z|) := by
    nlinarith [haff a b z, abs_nonneg a, abs_nonneg b, abs_nonneg z,
      mul_nonneg (abs_nonneg a) (abs_nonneg z)]
  have h2 : |c + d * z| ≤ (|c| + |d|) * (1 + |z|) := by
    nlinarith [haff c d z, abs_nonneg c, abs_nonneg d, abs_nonneg z,
      mul_nonneg (abs_nonneg c) (abs_nonneg z)]
  rw [norm_smul, Real.norm_eq_abs]
  have h3 := (hC (a + b * z)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) h1 k) hC0)
  refine (mul_le_mul h2 h3 (norm_nonneg _) (by positivity)).trans_eq ?_
  rw [mul_pow (1 + |a| + |b|), pow_succ (1 + |z|)]
  ring

/-- A function of polynomial growth at an affine argument, times an affine factor, is integrable
against a standard Gaussian: the real-valued case. -/
theorem integrable_comp_add_mul_mul_add_mul_gaussianReal {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ}
    {k : ℕ} (hC : ∀ y, |g y| ≤ C * (1 + |y|) ^ k) (a b c d : ℝ) :
    Integrable (fun z => g (a + b * z) * (c + d * z)) (gaussianReal 0 1) := by
  simpa only [smul_eq_mul, mul_comm] using
    integrable_add_mul_smul_comp_add_mul_gaussianReal hg.stronglyMeasurable hC a b c d

/-- **Differentiation of an average along a curve of affine maps:** let `μ` be a finite measure
on `ℝ` with a finite moment of order `k + 1`, and let `f`, with values in a normed space, have
derivative `f'` of growth at most `(1 + |y|) ^ k`, with `f (m t + σ t z)` integrable. Then
`d/dt ∫ f (m t + σ t z) dμ = ∫ (m' t + σ' t z) • f' (m t + σ t z) dμ`. -/
theorem hasDerivAt_integral_comp_add_mul {μ : Measure ℝ} [IsFiniteMeasure μ] {f f' : ℝ → F}
    {m σ m' σ' : ℝ → ℝ} {C t : ℝ} {k : ℕ} (hμ : MemLp id ((k + 1 : ℕ) : ℝ≥0∞) μ)
    (hf : ∀ y, HasDerivAt f (f' y) y) (hint₀ : Integrable (fun z => f (m t + σ t * z)) μ)
    (hC' : ∀ y, ‖f' y‖ ≤ C * (1 + |y|) ^ k)
    (hm : ∀ᶠ s in 𝓝 t, HasDerivAt m (m' s) s) (hσ : ∀ᶠ s in 𝓝 t, HasDerivAt σ (σ' s) s)
    (hm' : ContinuousAt m' t) (hσ' : ContinuousAt σ' t) :
    HasDerivAt (fun s => ∫ z, f (m s + σ s * z) ∂μ)
      (∫ z, (m' t + σ' t * z) • f' (m t + σ t * z) ∂μ) t := by
  have hC0 : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC' 0)
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
  have hpow : ∀ a b : ℝ, |a| ≤ B → |b| ≤ B → ∀ z : ℝ,
      C * (1 + |a + b * z|) ^ k ≤ C * (1 + B) ^ k * (1 + |z|) ^ k := fun a b ha hb z => by
    rw [mul_assoc, ← mul_pow]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ k) hC0
    have h1 : |a + b * z| ≤ B + B * |z| :=
      (abs_add_le _ _).trans (add_le_add ha (by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)))
    have h2 := abs_nonneg z
    nlinarith
  have hint : ∀ n ≤ k + 1, Integrable (fun z : ℝ => (1 + |z|) ^ n) μ := fun n hn => by
    have h : MemLp (fun z : ℝ => 1 + ‖z‖) n μ :=
      (memLp_const 1).add (hμ.mono_exponent (by exact_mod_cast hn)).norm
    refine h.integrable_norm_pow'.congr (ae_of_all _ fun z => ?_)
    simp only
    rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
  refine hasDerivAt_integral_comp_add_mul_of_dominated (μ := μ)
    (bound := fun z => C * (1 + B) ^ k * B * (1 + |z|) ^ (k + 1)) hf hnear (fun s hs => hs.1)
    (fun s hs => hs.2.1) hint₀ (ae_of_all _ fun z s hs => ?_) ((hint (k + 1) le_rfl).const_mul _)
  obtain ⟨-, -, h1, h2, h3, h4⟩ := hs
  have h5 : |m' s + σ' s * z| ≤ B * (1 + |z|) := by
    rw [mul_add, mul_one]
    exact (abs_add_le _ _).trans (add_le_add h3 (by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right h4 (abs_nonneg _)))
  rw [norm_smul, Real.norm_eq_abs]
  refine (mul_le_mul h5 ((hC' _).trans (hpow _ _ h1 h2 z)) (norm_nonneg _)
    (by positivity)).trans_eq ?_
  ring

/-- **Differentiation of a Gaussian average along a curve of affine maps**, vector-valued: if the
derivative `f'` of `f` has polynomial growth, then
`d/dt 𝔼 f (m t + σ t z) = 𝔼 [(m' t + σ' t z) • f' (m t + σ t z)]`. -/
theorem hasDerivAt_integral_comp_add_mul_gaussianReal_smul {f f' : ℝ → F} {m σ m' σ' : ℝ → ℝ}
    {C t : ℝ} {k : ℕ} (hf : ∀ y, HasDerivAt f (f' y) y)
    (hC' : ∀ y, ‖f' y‖ ≤ C * (1 + |y|) ^ k) (hm : ∀ᶠ s in 𝓝 t, HasDerivAt m (m' s) s)
    (hσ : ∀ᶠ s in 𝓝 t, HasDerivAt σ (σ' s) s) (hm' : ContinuousAt m' t)
    (hσ' : ContinuousAt σ' t) :
    HasDerivAt (fun s => ∫ z, f (m s + σ s * z) ∂(gaussianReal 0 1))
      (∫ z, (m' t + σ' t * z) • f' (m t + σ t * z) ∂(gaussianReal 0 1)) t := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun y => (hf y).continuousAt
  refine hasDerivAt_integral_comp_add_mul (memLp_id_gaussianReal (μ := 0) (v := 1)
    ((k + 1 : ℕ) : ℝ≥0)) hf ?_ hC' hm hσ hm' hσ'
  have h := integrable_add_mul_smul_comp_add_mul_gaussianReal hfc.stronglyMeasurable
    (norm_le_mul_one_add_abs_pow_of_hasDerivAt hf hC') (m t) (σ t) 1 0
  simpa only [zero_mul, add_zero, one_smul] using h

/-- **Differentiation of a Gaussian average along a curve of affine maps:** if the derivative `f'`
of `f` has polynomial growth, then
`d/dt 𝔼 f (m t + σ t z) = 𝔼 [f' (m t + σ t z) (m' t + σ' t z)]`. -/
theorem hasDerivAt_integral_comp_add_mul_gaussianReal {f f' m σ m' σ' : ℝ → ℝ} {C t : ℝ}
    {k : ℕ} (hf : ∀ y, HasDerivAt f (f' y) y) (hC' : ∀ y, |f' y| ≤ C * (1 + |y|) ^ k)
    (hm : ∀ᶠ s in 𝓝 t, HasDerivAt m (m' s) s) (hσ : ∀ᶠ s in 𝓝 t, HasDerivAt σ (σ' s) s)
    (hm' : ContinuousAt m' t) (hσ' : ContinuousAt σ' t) :
    HasDerivAt (fun s => ∫ z, f (m s + σ s * z) ∂(gaussianReal 0 1))
      (∫ z, f' (m t + σ t * z) * (m' t + σ' t * z) ∂(gaussianReal 0 1)) t := by
  simpa only [smul_eq_mul, mul_comm] using
    hasDerivAt_integral_comp_add_mul_gaussianReal_smul hf hC' hm hσ hm' hσ'

/-- **Stein's lemma for an affine Gaussian argument**, vector-valued: if `f'` has derivative `f''`
of polynomial growth, then `𝔼 [z • f'(w z + h)] = w • 𝔼 f''(w z + h)` for `z ~ N(0,1)`. -/
theorem integral_id_smul_deriv_comp_affine_gaussianReal {f' f'' : ℝ → F}
    (hf' : ∀ y, HasDerivAt f' (f'' y) y) {C : ℝ} {k : ℕ}
    (hC : ∀ y, ‖f'' y‖ ≤ C * (1 + |y|) ^ k) (h w : ℝ) :
    ∫ z, z • f' (w * z + h) ∂(gaussianReal 0 1) =
      w • ∫ z, f'' (w * z + h) ∂(gaussianReal 0 1) := by
  have hf'c : Continuous f' := continuous_iff_continuousAt.2 fun y => (hf' y).continuousAt
  have hf''m : StronglyMeasurable f'' := stronglyMeasurable_of_forall_hasDerivAt hf'
  have h1 : Integrable (fun z : ℝ => z • f' (h + w * z)) (gaussianReal 0 1) := by
    simpa only [zero_add, one_mul] using integrable_add_mul_smul_comp_add_mul_gaussianReal
      hf'c.stronglyMeasurable (norm_le_mul_one_add_abs_pow_of_hasDerivAt hf' hC) h w 0 1
  have h2 : Integrable (fun z : ℝ => f'' (h + w * z)) (gaussianReal 0 1) := by
    simpa only [zero_mul, add_zero, one_smul] using
      integrable_add_mul_smul_comp_add_mul_gaussianReal hf''m hC h w 1 0
  have := integral_id_smul_comp_affine_gaussianReal 1 hf' h w h1 h2
  simpa only [NNReal.coe_one, one_mul, add_comm h] using this

/-- **Stein's lemma for an affine Gaussian argument:** if `f'` has a bounded derivative `f''`,
then `𝔼 [f'(w z + h) z] = w 𝔼 f''(w z + h)` for `z ~ N(0,1)`. -/
theorem integral_deriv_comp_affine_mul_id_gaussianReal_of_bounded {f' f'' : ℝ → ℝ} {C₂ : ℝ}
    (hf' : ∀ y, HasDerivAt f' (f'' y) y) (hC₂ : ∀ y, |f'' y| ≤ C₂) (h w : ℝ) :
    ∫ z, f' (w * z + h) * z ∂(gaussianReal 0 1) =
      w * ∫ z, f'' (w * z + h) ∂(gaussianReal 0 1) := by
  have := integral_id_smul_deriv_comp_affine_gaussianReal hf' (C := C₂) (k := 0)
    (by simpa using hC₂) h w
  simpa only [smul_eq_mul, mul_comm] using this

/-- **Derivative of the Gaussian average in the standard deviation**, vector-valued: if `f'` is a
derivative of `f`, and `f''` a derivative of `f'` with polynomial growth, then
`(d/dw) 𝔼 f(w z + h) = w • 𝔼 f''(w z + h)`. -/
theorem hasDerivAt_integral_comp_affine_gaussianReal_smul {f f' f'' : ℝ → F}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y) {C : ℝ} {k : ℕ}
    (hC : ∀ y, ‖f'' y‖ ≤ C * (1 + |y|) ^ k) (h w : ℝ) :
    HasDerivAt (fun v => ∫ z, f (v * z + h) ∂(gaussianReal 0 1))
      (w • ∫ z, f'' (w * z + h) ∂(gaussianReal 0 1)) w := by
  have := hasDerivAt_integral_comp_add_mul_gaussianReal_smul (m := fun _ => h) (σ := id)
    (m' := fun _ => 0) (σ' := fun _ => 1) (t := w) hf
    (norm_le_mul_one_add_abs_pow_of_hasDerivAt hf' hC)
    (Eventually.of_forall fun s => hasDerivAt_const s h)
    (Eventually.of_forall fun s => hasDerivAt_id s) continuousAt_const continuousAt_const
  rw [← integral_id_smul_deriv_comp_affine_gaussianReal hf' hC h w]
  simpa only [id, zero_add, one_mul, add_comm h] using this

/-- **Derivative of the Gaussian average in the standard deviation:** if `f` has derivative `f'`,
and `f'` has a bounded derivative `f''`, then `(d/dw) 𝔼 f(w z + h) = w 𝔼 f''(w z + h)`. -/
theorem hasDerivAt_integral_comp_affine_gaussianReal_of_bounded {f f' f'' : ℝ → ℝ} {C₂ : ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hC₂ : ∀ y, |f'' y| ≤ C₂) (h w : ℝ) :
    HasDerivAt (fun v => ∫ z, f (v * z + h) ∂(gaussianReal 0 1))
      (w * ∫ z, f'' (w * z + h) ∂(gaussianReal 0 1)) w :=
  hasDerivAt_integral_comp_affine_gaussianReal_smul hf hf' (C := C₂) (k := 0)
    (by simpa using hC₂) h w

end ProbabilityTheory
