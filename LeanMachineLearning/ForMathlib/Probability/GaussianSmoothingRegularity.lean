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

For a `C²` function `g` with bounded `g, g', g''`, the Gaussian smoothing
`ψ(τ₁, τ₂, y) = ∬ g (y + τ₁ b + τ₂ ξ) dγ(b) dγ(ξ)` is `C²` jointly in `(τ₁, τ₂, y)`. This is the
regularity needed to apply the interpolation theorem with a parameter to the cavity system
(Talagrand Section 2.3), where `τ(s) = (cos s · a₀, sin s · √(1 − q))`.

* `ProbabilityTheory.contDiff_two_integral_gaussian_smoothing`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/-- The linear form `(τ₁, τ₂, y) ↦ y + τ₁ b + τ₂ ξ`. -/
noncomputable def gaussSmoothForm (η : ℝ × ℝ) : ((ℝ × ℝ) × ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ +
    η.1 • (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ) +
    η.2 • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)

theorem gaussSmoothForm_apply (η : ℝ × ℝ) (p : (ℝ × ℝ) × ℝ) :
    gaussSmoothForm η p = p.2 + η.1 * p.1.1 + η.2 * p.1.2 := by
  simp [gaussSmoothForm]

theorem norm_gaussSmoothForm_le (η : ℝ × ℝ) : ‖gaussSmoothForm η‖ ≤ 1 + |η.1| + |η.2| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p => ?_
  rw [gaussSmoothForm_apply]
  have h1 : |p.2| ≤ ‖p‖ := by simpa using norm_snd_le p
  have h2 : |p.1.1| ≤ ‖p‖ := by
    simpa using (norm_fst_le p.1).trans (norm_fst_le p)
  have h3 : |p.1.2| ≤ ‖p‖ := by
    simpa using (norm_snd_le p.1).trans (norm_fst_le p)
  rw [Real.norm_eq_abs]
  calc |p.2 + η.1 * p.1.1 + η.2 * p.1.2|
      ≤ |p.2| + |η.1| * |p.1.1| + |η.2| * |p.1.2| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) ?_)
        · rw [abs_mul]
        · rw [abs_mul]
    _ ≤ (1 + |η.1| + |η.2|) * ‖p‖ := by
        nlinarith [abs_nonneg η.1, abs_nonneg η.2, mul_le_mul_of_nonneg_left h2 (abs_nonneg η.1),
          mul_le_mul_of_nonneg_left h3 (abs_nonneg η.2)]


section
variable {g : ℝ → ℝ}

/-- The integrand `G (p, η) = g (y + τ₁ b + τ₂ ξ)`. -/
noncomputable def gaussSmoothIntegrand (g : ℝ → ℝ) (q : ((ℝ × ℝ) × ℝ) × (ℝ × ℝ)) : ℝ :=
  g (gaussSmoothForm q.2 q.1)

theorem contDiff_gaussSmoothIntegrand {n : ℕ} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (gaussSmoothIntegrand g) := by
  have : ContDiff ℝ n (fun q : ((ℝ × ℝ) × ℝ) × (ℝ × ℝ) =>
      q.1.2 + q.2.1 * q.1.1.1 + q.2.2 * q.1.1.2) := by fun_prop
  have heq : gaussSmoothIntegrand g = g ∘ (fun q : ((ℝ × ℝ) × ℝ) × (ℝ × ℝ) =>
      q.1.2 + q.2.1 * q.1.1.1 + q.2.2 * q.1.1.2) := by
    funext q
    simp [gaussSmoothIntegrand, gaussSmoothForm_apply]
  rw [heq]
  exact hg.comp this

theorem fderivLeft_gaussSmoothIntegrand (hg : ContDiff ℝ 2 g)
    (q : ((ℝ × ℝ) × ℝ) × (ℝ × ℝ)) :
    fderivLeft (gaussSmoothIntegrand g) q =
      deriv g (gaussSmoothForm q.2 q.1) • gaussSmoothForm q.2 := by
  have hd : DifferentiableAt ℝ (gaussSmoothIntegrand g) q :=
    ((contDiff_gaussSmoothIntegrand (n := 2) hg).differentiable (by norm_num)) q
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  refine (hasFDerivAt_fderivLeft hd).unique ?_
  exact (hg1 _).hasDerivAt.comp_hasFDerivAt q.1 (gaussSmoothForm q.2).hasFDerivAt

theorem differentiable_deriv_of_contDiff_two (hg : ContDiff ℝ 2 g) :
    Differentiable ℝ (deriv g) := by
  have h : ContDiff ℝ (1 + 1) g := by simpa [one_add_one_eq_two] using hg
  rw [contDiff_succ_iff_deriv] at h
  exact (h.2.2.differentiable (by norm_num))

theorem norm_fderivLeft_fderivLeft_gaussSmoothIntegrand_le (hg : ContDiff ℝ 2 g)
    (q : ((ℝ × ℝ) × ℝ) × (ℝ × ℝ)) :
    ‖fderivLeft (fderivLeft (gaussSmoothIntegrand g)) q‖ ≤
      |deriv (deriv g) (gaussSmoothForm q.2 q.1)| * ‖gaussSmoothForm q.2‖ ^ 2 := by
  have hG2 : ContDiff ℝ (1 + 1 : ℕ) (gaussSmoothIntegrand g) := by
    simpa using contDiff_gaussSmoothIntegrand (n := 2) hg
  have hD1 : ContDiff ℝ 1 (fderivLeft (gaussSmoothIntegrand g)) :=
    contDiff_fderivLeft (n := 1) hG2
  have hd : DifferentiableAt ℝ (fderivLeft (gaussSmoothIntegrand g)) q :=
    (hD1.differentiable (by norm_num)) q
  have hdg := differentiable_deriv_of_contDiff_two hg
  have hfun : (fun p => fderivLeft (gaussSmoothIntegrand g) (p, q.2)) =
      fun p => deriv g (gaussSmoothForm q.2 p) • gaussSmoothForm q.2 :=
    funext fun p => fderivLeft_gaussSmoothIntegrand hg (p, q.2)
  have hder : HasFDerivAt (fun p => fderivLeft (gaussSmoothIntegrand g) (p, q.2))
      ((deriv (deriv g) (gaussSmoothForm q.2 q.1) • gaussSmoothForm q.2).smulRight
        (gaussSmoothForm q.2)) q.1 := by
    rw [hfun]
    exact ((hdg _).hasDerivAt.comp_hasFDerivAt q.1
      (gaussSmoothForm q.2).hasFDerivAt).smul_const (gaussSmoothForm q.2)
  rw [(hasFDerivAt_fderivLeft hd).unique hder, ContinuousLinearMap.norm_smulRight_apply,
    norm_smul, Real.norm_eq_abs]
  ring_nf
  exact le_rfl

/-- **`C²` regularity of the Gaussian smoothing in the smoothing parameters.** For a `C²` function
`g` with bounded `g, g', g''`, the map `(τ₁, τ₂, y) ↦ ∬ g (y + τ₁ b + τ₂ ξ) dγ(b) dγ(ξ)` is `C²`
on `ℝ² × ℝ`. -/
theorem contDiff_two_integral_gaussian_smoothing (hg : ContDiff ℝ 2 g) {B₀ B₁ B₂ : ℝ}
    (h0 : ∀ x, |g x| ≤ B₀) (h1 : ∀ x, |deriv g x| ≤ B₁)
    (h2 : ∀ x, |deriv (deriv g) x| ≤ B₂) :
    ContDiff ℝ 2 (fun p : (ℝ × ℝ) × ℝ =>
      ∫ η, g (p.2 + η.1 * p.1.1 + η.2 * p.1.2) ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) := by
  have hG := contDiff_gaussSmoothIntegrand (n := 2) hg
  have hB₁ : 0 ≤ B₁ := (abs_nonneg _).trans (h1 0)
  have hB₂ : 0 ≤ B₂ := (abs_nonneg _).trans (h2 0)
  have hγ1 : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal 1).integrable le_rfl).abs
  have hγ2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 2).integrable_sq
  set ν : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1) with hν
  have hi1 : Integrable (fun η : ℝ × ℝ => |η.1|) ν := hγ1.comp_fst _
  have hi2 : Integrable (fun η : ℝ × ℝ => |η.2|) ν := hγ1.comp_snd _
  have hq1 : Integrable (fun η : ℝ × ℝ => η.1 ^ 2) ν := hγ2.comp_fst _
  have hq2 : Integrable (fun η : ℝ × ℝ => η.2 ^ 2) ν := hγ2.comp_snd _
  have hb₁ : Integrable (fun η : ℝ × ℝ => B₁ * (1 + |η.1| + |η.2|)) ν :=
    ((integrable_const (1 : ℝ)).add hi1 |>.add hi2).const_mul B₁
  have hb₂ : Integrable (fun η : ℝ × ℝ => B₂ * (3 * (1 + η.1 ^ 2 + η.2 ^ 2))) ν :=
    (((integrable_const (1 : ℝ)).add hq1 |>.add hq2).const_mul 3).const_mul B₂
  have hint : ∀ p, Integrable (fun η => gaussSmoothIntegrand g (p, η)) ν := fun p =>
    Integrable.of_bound (C := B₀)
      ((hG.continuous.comp (Continuous.prodMk_right p)).aestronglyMeasurable)
      (ae_of_all _ fun η => by simpa [gaussSmoothIntegrand] using h0 _)
  have hfirst : ∀ q, ‖fderivLeft (gaussSmoothIntegrand g) q‖ ≤
      B₁ * (1 + |q.2.1| + |q.2.2|) := fun q => by
    rw [fderivLeft_gaussSmoothIntegrand hg, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (h1 _) (norm_gaussSmoothForm_le q.2) (norm_nonneg _) hB₁
  have hsecond : ∀ q, ‖fderivLeft (fderivLeft (gaussSmoothIntegrand g)) q‖ ≤
      B₂ * (3 * (1 + q.2.1 ^ 2 + q.2.2 ^ 2)) := fun q => by
    refine (norm_fderivLeft_fderivLeft_gaussSmoothIntegrand_le hg q).trans ?_
    have hn : ‖gaussSmoothForm q.2‖ ^ 2 ≤ 3 * (1 + q.2.1 ^ 2 + q.2.2 ^ 2) := by
      have := norm_gaussSmoothForm_le q.2
      have h0' := norm_nonneg (gaussSmoothForm q.2)
      nlinarith [sq_abs q.2.1, sq_abs q.2.2, abs_nonneg q.2.1, abs_nonneg q.2.2,
        sq_nonneg (|q.2.1| - |q.2.2|), sq_nonneg (|q.2.1| - 1), sq_nonneg (|q.2.2| - 1)]
    exact mul_le_mul (h2 _) hn (by positivity) hB₂
  have := contDiff_two_integral_of_bounds (ν := ν) hG hint hb₁ hb₂ hfirst hsecond
  simpa [gaussSmoothIntegrand, gaussSmoothForm_apply] using this

end

end ProbabilityTheory
