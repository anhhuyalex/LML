/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianAffineDerivative

/-!
# Derivative of a two-Gaussian smoothing along a parameter path

For independent standard Gaussians `η₁, η₂` and a smooth `f`, the average
`𝔼 f (y + a η₁ + b η₂)` along a differentiable path `s ↦ (a s, b s)` has derivative
`(a a' + b b') 𝔼 f'' (y + a η₁ + b η₂)` (the heat equation). Differentiating under the product
Gaussian integral and applying Stein's lemma in each variable avoids any square root of
`a² + b²`, so the formula holds also where `a = b = 0`.

* `hasDerivAt_integral_gaussian_pair_path`.

This is the explicit term created by the `s`-dependent variance of `ξ*` in Talagrand's cavity
computation (Section 2.3, Eq. (2.49)).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace ProbabilityTheory

/-- **Heat equation along a path for a two-Gaussian smoothing.** -/
theorem hasDerivAt_integral_gaussian_pair_path {f f' f'' : ℝ → ℝ} {C₀ C₁ C₂ A B : ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hf''c : Continuous f'') (hC₀ : ∀ y, |f y| ≤ C₀) (hC₁ : ∀ y, |f' y| ≤ C₁)
    (hC₂ : ∀ y, |f'' y| ≤ C₂) {a b a' b' : ℝ → ℝ} (ha : ∀ s, HasDerivAt a (a' s) s)
    (hb : ∀ s, HasDerivAt b (b' s) s) (hA : ∀ s, |a' s| ≤ A) (hB : ∀ s, |b' s| ≤ B)
    (y s₀ : ℝ) :
    HasDerivAt (fun s => ∫ η, f (y + a s * η.1 + b s * η.2)
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))
      ((a s₀ * a' s₀ + b s₀ * b' s₀) *
        ∫ η, f'' (y + a s₀ * η.1 + b s₀ * η.2) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))
      s₀ := by
  set γ : Measure ℝ := gaussianReal 0 1 with hγ
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun y => (hf y).continuousAt
  have hf'c : Continuous f' := continuous_iff_continuousAt.2 fun y => (hf' y).continuousAt
  have hC₁0 : 0 ≤ C₁ := (abs_nonneg _).trans (hC₁ 0)
  have hz : Integrable (fun z : ℝ => |z|) γ := by
    simpa only [Real.norm_eq_abs, id] using (IsGaussian.integrable_id (μ := γ)).norm
  have hz1 : Integrable (fun η : ℝ × ℝ => |η.1|) (γ.prod γ) := hz.comp_fst γ
  have hz2 : Integrable (fun η : ℝ × ℝ => |η.2|) (γ.prod γ) := hz.comp_snd γ
  -- measurability of the path
  have hpm : ∀ s, Continuous fun η : ℝ × ℝ => y + a s * η.1 + b s * η.2 := fun s => by fun_prop
  have hint0 : Integrable (fun η : ℝ × ℝ => f (y + a s₀ * η.1 + b s₀ * η.2)) (γ.prod γ) :=
    (integrable_const C₀).mono' (hfc.comp (hpm s₀)).aestronglyMeasurable
      (ae_of_all _ fun η => by simpa only [Real.norm_eq_abs] using hC₀ _)
  have hder := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ.prod γ) (s := univ)
    (F := fun s η => f (y + a s * η.1 + b s * η.2))
    (F' := fun s η => f' (y + a s * η.1 + b s * η.2) * (a' s * η.1 + b' s * η.2))
    Filter.univ_mem (Filter.Eventually.of_forall fun s => (hfc.comp (hpm s)).aestronglyMeasurable)
    hint0
    (((hf'c.comp (hpm s₀)).mul (by fun_prop : Continuous fun η : ℝ × ℝ =>
      a' s₀ * η.1 + b' s₀ * η.2)).aestronglyMeasurable)
    (bound := fun η => C₁ * (A * |η.1| + B * |η.2|))
    (ae_of_all _ fun η s _ => by
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul (hC₁ _) ?_ (abs_nonneg _) hC₁0
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hA s) (abs_nonneg _)
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hB s) (abs_nonneg _))
    (((hz1.const_mul A).add (hz2.const_mul B)).const_mul C₁)
    (ae_of_all _ fun η s _ => by
      have hl : HasDerivAt (fun s => y + a s * η.1 + b s * η.2)
          (a' s * η.1 + b' s * η.2) s :=
        (((ha s).mul_const η.1).const_add y).add ((hb s).mul_const η.2)
      exact (hf _).comp s hl)).2
  refine hder.congr_deriv ?_
  -- Stein's lemma in each Gaussian variable
  have hi1 : Integrable (fun η : ℝ × ℝ => f' (y + a s₀ * η.1 + b s₀ * η.2) * η.1) (γ.prod γ) :=
    (hz1.const_mul C₁).mono' ((hf'c.comp (hpm s₀)).mul (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun η => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hC₁ _) (abs_nonneg _))
  have hi2 : Integrable (fun η : ℝ × ℝ => f' (y + a s₀ * η.1 + b s₀ * η.2) * η.2) (γ.prod γ) :=
    (hz2.const_mul C₁).mono' ((hf'c.comp (hpm s₀)).mul (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun η => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hC₁ _) (abs_nonneg _))
  have hi3 : Integrable (fun η : ℝ × ℝ => f'' (y + a s₀ * η.1 + b s₀ * η.2)) (γ.prod γ) :=
    (integrable_const C₂).mono' (hf''c.comp (hpm s₀)).aestronglyMeasurable
      (ae_of_all _ fun η => by simpa only [Real.norm_eq_abs] using hC₂ _)
  have st1 : ∫ η, f' (y + a s₀ * η.1 + b s₀ * η.2) * η.1 ∂(γ.prod γ) =
      a s₀ * ∫ η, f'' (y + a s₀ * η.1 + b s₀ * η.2) ∂(γ.prod γ) := by
    rw [integral_prod_symm _ hi1, integral_prod_symm _ hi3, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    have := integral_deriv_comp_affine_mul_id_gaussianReal hf' hf''c hC₁ hC₂ (y + b s₀ * w) (a s₀)
    simp only [show ∀ z : ℝ, y + a s₀ * z + b s₀ * w = a s₀ * z + (y + b s₀ * w) from
      fun z => by ring]
    exact this
  have st2 : ∫ η, f' (y + a s₀ * η.1 + b s₀ * η.2) * η.2 ∂(γ.prod γ) =
      b s₀ * ∫ η, f'' (y + a s₀ * η.1 + b s₀ * η.2) ∂(γ.prod γ) := by
    rw [integral_prod _ hi2, integral_prod _ hi3, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    have := integral_deriv_comp_affine_mul_id_gaussianReal hf' hf''c hC₁ hC₂ (y + a s₀ * w) (b s₀)
    simp only [show ∀ z : ℝ, y + a s₀ * w + b s₀ * z = b s₀ * z + (y + a s₀ * w) from
      fun z => by ring]
    exact this
  have hsplit : ∀ η : ℝ × ℝ, f' (y + a s₀ * η.1 + b s₀ * η.2) * (a' s₀ * η.1 + b' s₀ * η.2) =
      a' s₀ * (f' (y + a s₀ * η.1 + b s₀ * η.2) * η.1) +
        b' s₀ * (f' (y + a s₀ * η.1 + b s₀ * η.2) * η.2) := fun η => by ring
  simp_rw [hsplit]
  rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul,
    st1, st2]
  ring

end ProbabilityTheory
