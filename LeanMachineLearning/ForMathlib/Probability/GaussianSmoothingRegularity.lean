/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ContDiffParametric
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Regularity of the two-parameter Gaussian smoothing

For a `C²` function `g` with bounded `g, g', g''` and continuous linear forms `ℓ, A, B` on a
normed space `P`, the Gaussian smoothing `ψ(p) = ∬ g (ℓ p + b A p + ξ B p) dγ(b) dγ(ξ)` is `C²`
with bounded value, derivative and second derivative. For `P = ℝ² × ℝ` and `ℓ = y`, `A = τ₁`,
`B = τ₂` this is the regularity needed to apply the interpolation theorem with a parameter to the
cavity system (Talagrand Section 2.3), where `τ(s) = (cos s · a₀, sin s · √(1 − q))`.

* `ProbabilityTheory.boundedC2_integral_gaussian_smoothing`,
  `ProbabilityTheory.contDiff_two_integral_gaussian_smoothing`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

section

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] (ℓ A B : P →L[ℝ] ℝ) {g : ℝ → ℝ}

theorem norm_add_smul_add_smul_le (a b : ℝ) :
    ‖ℓ + a • A + b • B‖ ≤ (‖ℓ‖ + ‖A‖ + ‖B‖) * (1 + |a| + |b|) := by
  have h1 : ‖a • A‖ ≤ |a| * ‖A‖ := by rw [norm_smul, Real.norm_eq_abs]
  have h2 : ‖b • B‖ ≤ |b| * ‖B‖ := by rw [norm_smul, Real.norm_eq_abs]
  have h3 := norm_add_le (ℓ + a • A) (b • B)
  have h4 := norm_add_le ℓ (a • A)
  have hA := norm_nonneg A
  have hB := norm_nonneg B
  have hℓ := norm_nonneg ℓ
  nlinarith [abs_nonneg a, abs_nonneg b, mul_nonneg (abs_nonneg a) hA,
    mul_nonneg (abs_nonneg b) hB, mul_nonneg (abs_nonneg a) hB,
    mul_nonneg (abs_nonneg b) hA, mul_nonneg (abs_nonneg a) hℓ,
    mul_nonneg (abs_nonneg b) hℓ]

theorem hasFDerivAt_affine_forms (a b : ℝ) (p : P) :
    HasFDerivAt (fun p => ℓ p + a * A p + b * B p) (ℓ + a • A + b • B) p := by
  have h := (ℓ + a • A + b • B).hasFDerivAt (x := p)
  convert h using 1

theorem fderiv_comp_affine_forms (hg : Differentiable ℝ g) (a b : ℝ) (p : P) :
    fderiv ℝ (fun p => g (ℓ p + a * A p + b * B p)) p =
      deriv g (ℓ p + a * A p + b * B p) • (ℓ + a • A + b • B) :=
  ((hg _).hasDerivAt.comp_hasFDerivAt p (hasFDerivAt_affine_forms ℓ A B a b p)).fderiv

theorem norm_fderiv_fderiv_comp_affine_forms_le (hg : ContDiff ℝ 2 g) (a b : ℝ) (p : P) :
    ‖fderiv ℝ (fun p' => fderiv ℝ (fun p => g (ℓ p + a * A p + b * B p)) p') p‖ ≤
      |deriv (deriv g) (ℓ p + a * A p + b * B p)| * ‖ℓ + a • A + b • B‖ ^ 2 := by
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hfun : (fun p' => fderiv ℝ (fun p => g (ℓ p + a * A p + b * B p)) p') =
      fun p' => deriv g (ℓ p' + a * A p' + b * B p') • (ℓ + a • A + b • B) :=
    funext fun p' => fderiv_comp_affine_forms ℓ A B hg1 a b p'
  have hder : HasFDerivAt
      (fun p' => deriv g (ℓ p' + a * A p' + b * B p') • (ℓ + a • A + b • B))
      ((deriv (deriv g) (ℓ p + a * A p + b * B p) • (ℓ + a • A + b • B)).smulRight
        (ℓ + a • A + b • B)) p :=
    (((hg.differentiable_deriv_two _).hasDerivAt.comp_hasFDerivAt p
      (hasFDerivAt_affine_forms ℓ A B a b p)).smul_const (ℓ + a • A + b • B))
  rw [hfun, hder.fderiv, ContinuousLinearMap.norm_smulRight_apply, norm_smul, Real.norm_eq_abs]
  ring_nf
  exact le_rfl

/-- **The Gaussian smoothing is `C²` with bounded derivatives.** For a `C²` function `g` with
bounded `g, g', g''` and continuous linear forms `ℓ, A, B`, the map
`p ↦ ∬ g (ℓ p + b A p + ξ B p) dγ(b) dγ(ξ)` is `C²` with bounded value, derivative and second
derivative. -/
theorem boundedC2_integral_gaussian_smoothing (hg : ContDiff ℝ 2 g) {B₀ B₁ B₂ : ℝ}
    (h0 : ∀ x, |g x| ≤ B₀) (h1 : ∀ x, |deriv g x| ≤ B₁)
    (h2 : ∀ x, |deriv (deriv g) x| ≤ B₂) :
    BoundedC2 (fun p : P =>
      ∫ η, g (ℓ p + η.1 * A p + η.2 * B p) ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) := by
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hG : ContDiff ℝ 2 (fun q : P × (ℝ × ℝ) => g (ℓ q.1 + q.2.1 * A q.1 + q.2.2 * B q.1)) :=
    hg.comp (by fun_prop)
  have hB₁ : 0 ≤ B₁ := (abs_nonneg _).trans (h1 0)
  have hB₂ : 0 ≤ B₂ := (abs_nonneg _).trans (h2 0)
  set K : ℝ := ‖ℓ‖ + ‖A‖ + ‖B‖ with hK
  have hK0 : 0 ≤ K := by positivity
  have hγ1 : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal 1).integrable le_rfl).abs
  have hγ2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 2).integrable_sq
  set ν : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1) with hν
  have hi1 : Integrable (fun η : ℝ × ℝ => |η.1|) ν := hγ1.comp_fst _
  have hi2 : Integrable (fun η : ℝ × ℝ => |η.2|) ν := hγ1.comp_snd _
  have hq1 : Integrable (fun η : ℝ × ℝ => η.1 ^ 2) ν := hγ2.comp_fst _
  have hq2 : Integrable (fun η : ℝ × ℝ => η.2 ^ 2) ν := hγ2.comp_snd _
  have hb₁ : Integrable (fun η : ℝ × ℝ => B₁ * (K * (1 + |η.1| + |η.2|))) ν :=
    (((integrable_const (1 : ℝ)).add hi1 |>.add hi2).const_mul K).const_mul B₁
  have hb₂ : Integrable (fun η : ℝ × ℝ => B₂ * (K ^ 2 * (3 * (1 + η.1 ^ 2 + η.2 ^ 2)))) ν :=
    ((((integrable_const (1 : ℝ)).add hq1 |>.add hq2).const_mul 3).const_mul (K ^ 2)).const_mul B₂
  refine boundedC2_integral_of_bounds (ν := ν) (G := fun q : P × (ℝ × ℝ) =>
      g (ℓ q.1 + q.2.1 * A q.1 + q.2.2 * B q.1)) hG (fun p => ?_) (integrable_const B₀) hb₁ hb₂
    (fun p η => h0 _) (fun p η => ?_) (fun p η => ?_)
  · exact Integrable.of_bound (C := B₀)
      ((hG.continuous.comp (Continuous.prodMk_right p)).aestronglyMeasurable)
      (ae_of_all _ fun η => by simpa using h0 _)
  · show ‖fderiv ℝ (fun p => g (ℓ p + η.1 * A p + η.2 * B p)) p‖ ≤ _
    rw [fderiv_comp_affine_forms ℓ A B hg1, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (h1 _) (norm_add_smul_add_smul_le ℓ A B _ _) (norm_nonneg _) hB₁
  · show ‖fderiv ℝ (fun p' => fderiv ℝ (fun p => g (ℓ p + η.1 * A p + η.2 * B p)) p') p‖ ≤ _
    refine (norm_fderiv_fderiv_comp_affine_forms_le ℓ A B hg η.1 η.2 p).trans ?_
    have hn : ‖ℓ + η.1 • A + η.2 • B‖ ^ 2 ≤ K ^ 2 * (3 * (1 + η.1 ^ 2 + η.2 ^ 2)) := by
      have h := norm_add_smul_add_smul_le ℓ A B η.1 η.2
      have h0' := norm_nonneg (ℓ + η.1 • A + η.2 • B)
      have h3 : (1 + |η.1| + |η.2|) ^ 2 ≤ 3 * (1 + η.1 ^ 2 + η.2 ^ 2) := by
        nlinarith [sq_abs η.1, sq_abs η.2, abs_nonneg η.1, abs_nonneg η.2,
          sq_nonneg (|η.1| - |η.2|), sq_nonneg (|η.1| - 1), sq_nonneg (|η.2| - 1)]
      calc ‖ℓ + η.1 • A + η.2 • B‖ ^ 2
          ≤ (K * (1 + |η.1| + |η.2|)) ^ 2 := pow_le_pow_left₀ h0' h 2
        _ = K ^ 2 * (1 + |η.1| + |η.2|) ^ 2 := by ring
        _ ≤ K ^ 2 * (3 * (1 + η.1 ^ 2 + η.2 ^ 2)) :=
          mul_le_mul_of_nonneg_left h3 (sq_nonneg K)
    exact mul_le_mul (h2 _) hn (sq_nonneg _) hB₂

/-- **`C²` regularity of the Gaussian smoothing.** -/
theorem contDiff_two_integral_gaussian_smoothing (hg : ContDiff ℝ 2 g) {B₀ B₁ B₂ : ℝ}
    (h0 : ∀ x, |g x| ≤ B₀) (h1 : ∀ x, |deriv g x| ≤ B₁)
    (h2 : ∀ x, |deriv (deriv g) x| ≤ B₂) :
    ContDiff ℝ 2 (fun p : P =>
      ∫ η, g (ℓ p + η.1 * A p + η.2 * B p) ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) :=
  (boundedC2_integral_gaussian_smoothing ℓ A B hg h0 h1 h2).contDiff

end

end ProbabilityTheory
