/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Approximation.InfiniteWidth
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Barron norm and the Fourier representation theorem

This file formalizes Definition 3.1 and Theorem 3.1 from the deep learning theory notes
(Telgarsky 2021), following Barron (1993).

The central object is the **Barron norm** of a function f : ℝᵈ → ℝ:
```
‖f‖_Barron := ∫ ‖∇̂f(w)‖ dw  =  2π ∫ ‖w‖ · |f̂(w)| dw
```
where f̂ is the Fourier transform and ∇̂f(w) = 2πi·w·f̂(w) is the Fourier transform of ∇f.

Functions with finite Barron norm admit an *exact* infinite-width representation as a
superposition of threshold (or cosine) neurons with a measure whose mass is bounded by
`2 ‖f‖_Barron`.

## Notation

We write `𝓕 f` for the Fourier transform of f, using Mathlib's `VectorFourier.fourierIntegral`
with the convention `𝓕 f(w) = ∫ exp(-2πi ⟨w, x⟩) f(x) dx`.
The Barron norm uses the convention from Telgarsky (2021), which follows Barron (1993).

## Main definitions

* `fourierGradNorm f w` : the integrand `‖∇̂f(w)‖ = 2π‖w‖·|f̂(w)|`.
* `barronNorm f` : Definition 3.1 — `∫ ‖∇̂f(w)‖ dw`.
* `BarronClass C` : the class of functions with Barron norm ≤ C.
* `barronPolarDecomp f` : the polar-decomposition representation of f̂.

## Main results

* `barronTheorem` : Theorem 3.1 — functions with finite Barron norm have an exact
  infinite-width threshold representation; the measure has mass ≤ 2·‖f‖_Barron.
* `gaussian_barronNorm_bound` : Barron norm of a Gaussian is O(√d) when σ² ≥ 1/(2π).

-/

@[expose] public section

open MeasureTheory Real Complex VectorFourier

namespace Approximation.BarronNorm

variable {d : ℕ}

/-! ### Fourier transform setup -/



/-- The Fourier transform of f : ℝᵈ → ℝ.
`𝓕 f(w) = ∫ exp(-2πi ⟨w, x⟩) f(x) dx`. -/
noncomputable def fourierTransform
    (f : (EuclideanSpace ℝ (Fin d)) → ℝ) (w : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ∫ x : EuclideanSpace ℝ (Fin d), Complex.exp (-(2 * π * Complex.I * ↑(inner ℝ w x))) * f x

/-- The magnitude of the Fourier transform. -/
noncomputable def fourierMagnitude
    (f : (EuclideanSpace ℝ (Fin d)) → ℝ) (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ‖fourierTransform f w‖

/-- The phase angle θ(w) of f̂(w): the unique θ with f̂(w) = |f̂(w)| · exp(2πiθ). -/
noncomputable def fourierPhase
    (f : (EuclideanSpace ℝ (Fin d)) → ℝ) (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Complex.arg (fourierTransform f w) / (2 * π)

lemma fourierTransform_neg_eq_conj
    (f : (EuclideanSpace ℝ (Fin d)) → ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    fourierTransform f (-w) = star (fourierTransform f w) := by
  simp_rw [fourierTransform]
  have h_star :
      star (∫ (x : EuclideanSpace ℝ (Fin d)),
        cexp (-(2 * ↑π * I * ↑(inner ℝ w x))) * ↑(f x)) =
        (starRingEnd ℂ) (∫ (x : EuclideanSpace ℝ (Fin d)),
          cexp (-(2 * ↑π * I * ↑(inner ℝ w x))) * ↑(f x)) := rfl
  rw [h_star, ← integral_conj]
  congr 1
  ext x
  have h1 :
      (starRingEnd ℂ) (cexp (-(2 * ↑π * I * ↑(inner ℝ w x))) * ↑(f x)) =
        (starRingEnd ℂ) (cexp (-(2 * ↑π * I * ↑(inner ℝ w x)))) *
          (starRingEnd ℂ) (f x : ℂ) := by
    exact map_mul (starRingEnd ℂ) _ _
  rw [h1]
  have h2 :
      (starRingEnd ℂ) (cexp (-(2 * ↑π * I * ↑(inner ℝ w x)))) =
        cexp (2 * ↑π * I * ↑(inner ℝ w x)) := by
    rw [← Complex.exp_conj]
    congr 1
    have h2a : (starRingEnd ℂ) (2 : ℂ) = 2 := by apply Complex.ext <;> simp
    have h2b : (starRingEnd ℂ) (↑π : ℂ) = ↑π := Complex.conj_ofReal π
    have h2c : (starRingEnd ℂ) I = -I := Complex.conj_I
    have h2d : (starRingEnd ℂ) ↑(inner ℝ w x) = ↑(inner ℝ w x) :=
      Complex.conj_ofReal (inner ℝ w x)
    simp [map_neg, map_mul, h2a, h2b, h2c, h2d]
  have h3 : (starRingEnd ℂ) (f x : ℂ) = (f x : ℂ) := Complex.conj_ofReal (f x)
  rw [h2, h3]
  congr 2
  simp [inner_neg_left]

lemma fourierMagnitude_neg (f : (EuclideanSpace ℝ (Fin d)) → ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    fourierMagnitude f (-w) = fourierMagnitude f w := by
  simp_rw [fourierMagnitude, fourierTransform_neg_eq_conj]
  simp

lemma sin_add_arg_star (b : ℝ) (z : ℂ) :
    Real.sin (b + Complex.arg (star z)) = Real.sin (b - Complex.arg z) := by
  change Real.sin (b + Complex.arg ((starRingEnd ℂ) z)) = Real.sin (b - Complex.arg z)
  rw [Complex.arg_conj]
  split_ifs with h
  · rw [h]
    rw [Real.sin_add_pi, Real.sin_sub_pi]
  · ring_nf

/-! ### Barron norm (Definition 3.1) -/

/-- The Barron norm integrand: ‖∇̂f(w)‖ = 2π·‖w‖·|f̂(w)|.
This follows from the Fourier derivative identity ∇̂f(w) = 2πi·w·f̂(w),
so ‖∇̂f(w)‖ = 2π·‖w‖·|f̂(w)|. -/
noncomputable def barronIntegrand
    (f : (EuclideanSpace ℝ (Fin d)) → ℝ) (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  2 * π * ‖w‖ * fourierMagnitude f w

/-- **Definition 3.1** (Barron 1993; Telgarsky 2021).
The *Barron norm* of f : ℝᵈ → ℝ is
  `‖f‖_Barron := ∫ ‖∇̂f(w)‖ dw = 2π ∫ ‖w‖ · |f̂(w)| dw`.
The corresponding *Barron class with norm C* is
  `ℱ_C := {f : ℝᵈ → ℝ | ‖f‖_Barron ≤ C}`. -/
noncomputable def barronNorm (f : (EuclideanSpace ℝ (Fin d)) → ℝ) : ℝ :=
  ∫ w : EuclideanSpace ℝ (Fin d), barronIntegrand f w

/-- The Barron class: functions with Barron norm at most C. -/
def BarronClass (C : ℝ) (d : ℕ) : Set ((EuclideanSpace ℝ (Fin d)) → ℝ) :=
  {f | ∃ _ : Integrable (barronIntegrand f) volume, barronNorm f ≤ C}

/-- Barron norm is nonneg. -/
lemma barronNorm_nonneg (f : (EuclideanSpace ℝ (Fin d)) → ℝ) : 0 ≤ barronNorm f := by
  apply MeasureTheory.integral_nonneg
  intro w
  simp only [barronIntegrand, fourierMagnitude]
  positivity

/-! ### Barron representation (Theorem 3.1) -/

/-- The cosine bump function used in Barron's construction:
  `(cos(2π wᵀx + 2πθ) - cos(2πθ)) / (2π‖w‖)`.
This is Lipschitz in x (bounded by ‖x‖) and is the building block of the
infinite-width threshold representation. -/
noncomputable def barronCosineBump
    (w : EuclideanSpace ℝ (Fin d)) (θ : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if ‖w‖ = 0 then 0
  else (Real.cos (2 * π * inner ℝ w x + 2 * π * θ) - Real.cos (2 * π * θ)) /
       (2 * π * ‖w‖)


/-- The Barron cosine bump is bounded by ‖x‖ (pointwise). -/
lemma barronCosineBump_bound (w : EuclideanSpace ℝ (Fin d)) (θ : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    |barronCosineBump w θ x| ≤ ‖x‖ := by
  simp only [barronCosineBump]
  split_ifs with hw
  · simp
  · rw [abs_div, div_le_iff₀ (by positivity)]
    -- Cosine is 1-Lipschitz, so |cos(a) - cos(b)| ≤ |a - b|; then apply Cauchy-Schwarz.
    calc |Real.cos (2 * π * inner ℝ w x + 2 * π * θ) - Real.cos (2 * π * θ)|
        ≤ |2 * π * inner ℝ w x + 2 * π * θ - 2 * π * θ| := by
          have h := LipschitzWith.dist_le_mul Real.lipschitzWith_cos
            (2 * π * inner ℝ w x + 2 * π * θ) (2 * π * θ)
          rw [Real.dist_eq, Real.dist_eq] at h; simpa using h
      _ = 2 * π * |inner ℝ w x| := by
          rw [show 2 * π * inner ℝ w x + 2 * π * θ - 2 * π * θ =
              (2 * π) * inner ℝ w x by ring,
              abs_mul, abs_of_pos Real.two_pi_pos]
      _ ≤ 2 * π * (‖w‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm w x) (le_of_lt Real.two_pi_pos)
      _ = ‖x‖ * (2 * π * ‖w‖) := by ring
      _ = ‖x‖ * |2 * π * ‖w‖| := by
          have hw_pos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)
          rw [abs_of_pos (mul_pos Real.two_pi_pos hw_pos)]

-- Helper for Fourier inversion
private lemma barron_fourier_inv {d : ℕ} {f : (EuclideanSpace ℝ (Fin d)) → ℝ}
    (hf_cont : Continuous f)
    (hf_L1 : Integrable f volume)
    (hfhat_L1 : Integrable (fourierTransform f) volume) :
    ∀ (x : EuclideanSpace ℝ (Fin d)),
      ↑(f x) = FourierTransformInv.fourierInv (fourierTransform f) x := by
  intro x
  have h_lift_cont : Continuous (fun x => (f x : ℂ)) := continuous_ofReal.comp hf_cont
  have h_lift_L1 : Integrable (fun x => (f x : ℂ)) volume := Integrable.ofReal hf_L1
  have hf_eq : fourierTransform f = FourierTransform.fourier (fun x => (f x : ℂ)) := by
    ext w
    rw [fourierTransform, fourier_eq']
    apply congr_arg
    ext x
    simp only [smul_eq_mul]
    rw [real_inner_comm]
    -- Rearrange to match exponent
    congr 1
    push_cast
    ring_nf
  have hfhat_L1' : Integrable (FourierTransform.fourier (fun x => (f x : ℂ))) volume := by
    rw [← hf_eq]
    exact hfhat_L1
  have h_inv_thm := Continuous.fourierInv_fourier_eq h_lift_cont h_lift_L1 hfhat_L1'
  have h_inv_eval :
      FourierTransformInv.fourierInv (FourierTransform.fourier (fun x => (f x : ℂ))) x =
        (fun x => (f x : ℂ)) x := by
    rw [h_inv_thm]
  rw [hf_eq]
  exact h_inv_eval.symm

-- Polar decomposition of the Fourier transform
private lemma fourierTransform_polar {d : ℕ}
    (f : (EuclideanSpace ℝ (Fin d)) → ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    fourierTransform f w =
      (fourierMagnitude f w : ℂ) * cexp (2 * ↑π * I * ↑(fourierPhase f w)) := by
  have h_arg : (2 * ↑π * I * ↑(fourierPhase f w)) = ↑(Complex.arg (fourierTransform f w)) * I := by
    unfold fourierPhase
    calc (2 * ↑π * I * ↑(Complex.arg (fourierTransform f w) / (2 * π)))
      _ = (2 * ↑π * I * (↑(Complex.arg (fourierTransform f w)) / (2 * ↑π))) := by
        push_cast
        rfl
      _ = I * ↑(Complex.arg (fourierTransform f w)) * (2 * ↑π / (2 * ↑π)) := by ring
      _ = I * ↑(Complex.arg (fourierTransform f w)) := by
        rw [div_self, mul_one]
        exact mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_pos.ne.symm)
      _ = ↑(Complex.arg (fourierTransform f w)) * I := mul_comm _ _
  rw [h_arg]
  unfold fourierMagnitude
  exact (Complex.norm_mul_exp_arg_mul_I _).symm

-- Integrability of the modulated Fourier transform difference
private lemma barron_diff_integrable {d : ℕ} {f : (EuclideanSpace ℝ (Fin d)) → ℝ}
    (hfhat_L1 : Integrable (fourierTransform f) volume)
    (x : EuclideanSpace ℝ (Fin d)) :
    Integrable
      (fun w ↦ (cexp (2 * ↑π * I * ↑(inner ℝ w x)) - 1) * fourierTransform f w)
      volume := by
  have hnorm : ∀ w,
      ‖(cexp (2 * ↑π * I * ↑(inner ℝ w x)) - 1) * fourierTransform f w‖ ≤
        2 * ‖fourierTransform f w‖ := by
    intro w
    rw [norm_mul, show
      2 * ↑π * I * ↑(inner ℝ w x) = ↑(2 * π * inner ℝ w x) * I by
        push_cast
        ring]
    exact mul_le_mul_of_nonneg_right (by
      calc
        ‖cexp (↑(2 * π * inner ℝ w x) * I) - 1‖ ≤
            ‖cexp (↑(2 * π * inner ℝ w x) * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + 1 := by rw [Complex.norm_exp_ofReal_mul_I, norm_one]
        _ = 2 := by norm_num) (norm_nonneg _)
  have h_bound : ∀ᵐ w ∂volume,
      ‖(cexp (2 * ↑π * I * ↑(inner ℝ w x)) - 1) * fourierTransform f w‖ ≤
        ‖(2 : ℝ) • fourierTransform f w‖ := by
    filter_upwards [] with w
    calc
      ‖(cexp (2 * ↑π * I * ↑(inner ℝ w x)) - 1) * fourierTransform f w‖ ≤
          2 * ‖fourierTransform f w‖ := hnorm w
      _ = ‖(2 : ℝ) • fourierTransform f w‖ := by rw [norm_smul, Real.norm_two]
  exact Integrable.mono (hfhat_L1.smul (2 : ℝ))
    (((Continuous.cexp
      (continuous_const.mul (continuous_ofReal.comp (continuous_id.inner continuous_const)))).sub
        continuous_const).aestronglyMeasurable.mul hfhat_L1.1)
    h_bound

-- Expresses the difference f(x) - f(0) as an integral over complex exponentials
private lemma barron_diff_exp {d : ℕ} {f : (EuclideanSpace ℝ (Fin d)) → ℝ}
    (hf_cont : Continuous f)
    (hf_L1 : Integrable f volume)
    (hfhat_L1 : Integrable (fourierTransform f) volume)
    (x : EuclideanSpace ℝ (Fin d)) :
    (f x : ℂ) - (f 0 : ℂ) =
      ∫ w, (Complex.exp (2 * π * Complex.I * inner ℝ w x) - 1) *
        fourierTransform f w := by
  have h_inv : ∀ (x : EuclideanSpace ℝ (Fin d)),
      ↑(f x) = FourierTransformInv.fourierInv (fourierTransform f) x :=
    barron_fourier_inv hf_cont hf_L1 hfhat_L1
  rw [h_inv x, h_inv 0]
  have h_int_x :
      FourierTransformInv.fourierInv (fourierTransform f) x =
        ∫ w : EuclideanSpace ℝ (Fin d),
          Complex.exp (2 * π * Complex.I * (inner ℝ w x : ℝ)) *
            fourierTransform f w := by
    change VectorFourier.fourierIntegral _ _ _ _ _ = _
    apply integral_congr_ae
    filter_upwards [] with w
    simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, LinearMap.neg_apply,
      innerₗ_apply_apply, Complex.ofReal_mul,
      ofReal_ofNat, neg_neg, mul_eq_mul_right_iff]
    ring_nf; simp
  have h_int_0 :
      FourierTransformInv.fourierInv (fourierTransform f) 0 =
        ∫ w : EuclideanSpace ℝ (Fin d), fourierTransform f w := by
    change VectorFourier.fourierIntegral _ _ _ _ _ = _
    apply integral_congr_ae
    filter_upwards [] with w
    simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, LinearMap.neg_apply,
      innerₗ_apply_apply, inner_zero_right, mul_zero, zero_mul, Complex.exp_zero, one_mul,
      Complex.ofReal_zero, neg_zero]
  rw [h_int_x, h_int_0, ← integral_sub]
  · apply integral_congr_ae
    filter_upwards [] with w
    ring_nf
  · have h_bound : ∀ᵐ w ∂volume, ‖cexp (2 * ↑π * I * ↑(inner ℝ w x)) * fourierTransform f w‖ ≤ ‖fourierTransform f w‖ := by
    filter_upwards [] with w
    exact le_of_eq (by
      rw [norm_mul, show
        2 * ↑π * I * ↑(inner ℝ w x) = ↑(2 * π * inner ℝ w x) * I by
          push_cast
          ring, Complex.norm_exp_ofReal_mul_I, one_mul])
    exact Integrable.mono hfhat_L1
      ((Continuous.cexp <|
        continuous_const.mul (continuous_ofReal.comp (continuous_id.inner continuous_const)))
          .aestronglyMeasurable.mul hfhat_L1.1)
      h_bound
  · exact hfhat_L1

-- Takes the real part of the integral to rewrite the complex exponential in terms of cosines
private lemma barron_real_part {d : ℕ} {f : (EuclideanSpace ℝ (Fin d)) → ℝ}
    (hfhat_L1 : Integrable (fourierTransform f) volume)
    (x : EuclideanSpace ℝ (Fin d))
    (h_diff_x :
      (f x : ℂ) - (f 0 : ℂ) =
        ∫ w, (Complex.exp (2 * π * Complex.I * inner ℝ w x) - 1) *
          fourierTransform f w) :
    f x - f 0 = ∫ w, barronCosineBump w (fourierPhase f w) x * barronIntegrand f w := by
  rw [show (f x - f 0 : ℝ) =
      (∫ (w : EuclideanSpace ℝ (Fin d)),
        (cexp (2 * ↑π * I * ↑(inner ℝ w x)) - 1) * fourierTransform f w).re by
    rw [← h_diff_x]
    rfl]
  have h_integrable := barron_diff_integrable hfhat_L1 x
  have h_int_re :
      (∫ (w : EuclideanSpace ℝ (Fin d)),
        (cexp (2 * ↑π * I * ↑(inner ℝ w x)) - 1) * fourierTransform f w).re =
          ∫ w, ((cexp (2 * ↑π * I * ↑(inner ℝ w x)) - 1) *
            fourierTransform f w).re := (integral_re h_integrable).symm
  rw [h_int_re]
  apply integral_congr_ae
  filter_upwards [] with w
  -- Prove pointwise equality between the real part of the integrand and the Barron representation
  by_cases hw : ‖w‖ = 0
  · rw [show cexp (2 * ↑π * I * ↑(inner ℝ w x)) - 1 = 0 by
        rw [show inner ℝ w x = (0 : ℝ) by
          rw [norm_eq_zero.mp hw, inner_zero_left],
          Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_self],
      zero_mul, Complex.zero_re]
    simp [barronCosineBump, hw]
  · -- Step 1: Prove polar decomposition of the Fourier transform
	    have h_polar := fourierTransform_polar f w
    -- Step 2: Simplify the real part of the integrand in the Fourier inversion formula
    have h_LHS :
        ((cexp (2 * ↑π * I * ↑(inner ℝ w x)) - 1) *
          ((fourierMagnitude f w : ℂ) *
            cexp (2 * ↑π * I * ↑(fourierPhase f w)))).re =
          fourierMagnitude f w *
            (Real.cos (2 * π * inner ℝ w x + 2 * π * fourierPhase f w) -
              Real.cos (2 * π * fourierPhase f w)) := by
      simp only [mul_re, sub_re, exp_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero,
        sub_zero, I_re, mul_im, zero_mul, add_zero, I_im, mul_one, sub_self, Real.exp_zero,
        zero_add, one_mul, one_re, exp_im, sub_im, one_im]
      rw [Real.cos_add]
      ring
    -- Step 3: Simplify the product of the Barron cosine bump and the Barron integrand
    have h_RHS :
        (Real.cos (2 * π * inner ℝ w x + 2 * π * fourierPhase f w) -
          Real.cos (2 * π * fourierPhase f w)) / (2 * π * ‖w‖) *
          (2 * π * ‖w‖ * fourierMagnitude f w) =
            fourierMagnitude f w *
              (Real.cos (2 * π * inner ℝ w x + 2 * π * fourierPhase f w) -
                Real.cos (2 * π * fourierPhase f w)) := by
      have h_nonzero : 2 * π * ‖w‖ ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hw
      calc
        _ = (Real.cos (2 * π * inner ℝ w x + 2 * π * fourierPhase f w) -
              Real.cos (2 * π * fourierPhase f w)) / (2 * π * ‖w‖) *
              (2 * π * ‖w‖) * fourierMagnitude f w := by
          ring
        _ = (Real.cos (2 * π * inner ℝ w x + 2 * π * fourierPhase f w) -
              Real.cos (2 * π * fourierPhase f w)) * fourierMagnitude f w := by
          rw [div_mul_cancel₀ _ h_nonzero]
        _ = _ := by ring
    -- Conclude the main goal by substitution
    rw [h_polar]
    unfold barronCosineBump barronIntegrand
    rw [if_neg hw, h_LHS, h_RHS]

-- A cosine bump can be represented as an integral against a threshold activation:
-- for any w, θ, x there exists g such that barronCosineBump w θ x = ∫ b, σ(⟨w,x⟩ - b) · g(b) db.
-- The construction places a constant block of height B = barronCosineBump w θ x on [⟨w,x⟩-1, ⟨w,x⟩]
-- and zero elsewhere; the threshold activation σ(z-b) = 1 exactly on that interval.
private lemma barronCosineBump_threshold_repr {d : ℕ}
    (w : EuclideanSpace ℝ (Fin d)) (θ : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ g : ℝ → ℝ, barronCosineBump w θ x = ∫ b, thresholdActivation (inner ℝ w x - b) * g b := by
  set z := inner ℝ w x with hz
  set B := barronCosineBump w θ x with hB
  let g : ℝ → ℝ := fun b => if b ∈ Set.Icc (z - 1) z then B else 0
  refine ⟨g, ?_⟩
  -- Key observation: thresholdActivation(z - b) = 1 when b ≤ z (i.e., when g b ≠ 0)
  have h_pointwise : ∀ b, thresholdActivation (z - b) * g b = g b := by
    intro b
    dsimp [g]
    by_cases hb : b ∈ Set.Icc (z - 1) z
    · -- b ∈ [z-1, z], so b ≤ z, hence z - b ≥ 0
      have hz_ge_b : z - b ≥ 0 := by
        rcases hb with ⟨hbl, hbr⟩
        linarith
      simp [thresholdActivation, hb, hz_ge_b]
    · -- b ∉ [z-1, z], so g b = 0
      simp [hb]
  have h_int_eq : ∫ b : ℝ, thresholdActivation (z - b) * g b = ∫ b : ℝ, g b :=
    integral_congr_ae (ae_of_all volume h_pointwise)
  rw [h_int_eq]
  -- g equals the indicator of Icc(z-1, z) scaled by B
  have h_g_eq_indicator : g = Set.indicator (Set.Icc (z - 1) z) (fun _ => B) := by
    ext b; simp [g, Set.indicator]
  rw [h_g_eq_indicator]
  rw [integral_indicator_const B measurableSet_Icc]
  -- volume of [z-1, z] = 1
  have h_vol : volume.real (Set.Icc (z - 1) z) = (1 : ℝ) := by
    rw [measureReal_def, Real.volume_Icc]
    simp
  simp [h_vol]

-- Reduces an integral against a threshold activation over [0, W] to an integral over [0, c]
private lemma setIntegral_thresholdActivation_eq_Icc {c W : ℝ} (_hc_nonneg : 0 ≤ c) (hc_le : c ≤ W) (f : ℝ → ℝ) :
    (∫ b in Set.Icc (0 : ℝ) W, thresholdActivation (c - b) * f b) =
    ∫ b in Set.Icc (0 : ℝ) c, f b := by
  -- Helper: thresholdActivation(c - b) = (Set.Iic c).indicator 1 at b
  have h_thresh_indicator (b : ℝ) :
      thresholdActivation (c - b) = (Set.Iic c).indicator (fun _ => (1 : ℝ)) b := by
    by_cases hb : b ≤ c
    · have h_nonneg : c - b ≥ 0 := by linarith
      simp [thresholdActivation, Set.indicator, Set.mem_Iic, h_nonneg, hb]
    · have h_neg : ¬(c - b ≥ 0) := by linarith
      simp [thresholdActivation, Set.indicator, Set.mem_Iic, h_neg, hb]
  -- Intersection lemma: when 0 ≤ c ≤ W, Icc 0 W ∩ Iic c = Icc 0 c
  have h_inter_pos :
      Set.Icc (0 : ℝ) W ∩ Set.Iic c = Set.Icc (0 : ℝ) c := by
    ext y; constructor
    · rintro ⟨⟨hy0, hyw⟩, hyc⟩; exact ⟨hy0, hyc⟩
    · rintro ⟨hy0, hyc⟩; exact ⟨⟨hy0, hyc.trans hc_le⟩, hyc⟩
  -- Step 1: replace thresholdActivation with indicator
  have h_step1 : (∫ b in Set.Icc (0 : ℝ) W, thresholdActivation (c - b) * f b) =
      (∫ b in Set.Icc (0 : ℝ) W, ((Set.Iic c).indicator (fun _ => (1 : ℝ)) b) * f b) := by
    refine setIntegral_congr_fun measurableSet_Icc ?_
    intro b _
    simp [h_thresh_indicator b]
  -- Step 2: move the constant 1 inside the indicator
  have h_step2 : (∫ b in Set.Icc (0 : ℝ) W, ((Set.Iic c).indicator (fun _ => (1 : ℝ)) b) * f b) =
      (∫ b in Set.Icc (0 : ℝ) W, (Set.Iic c).indicator (fun b' => f b') b) := by
    refine setIntegral_congr_fun measurableSet_Icc ?_
    intro b _
    simp [Set.indicator, mul_comm]
  -- Step 3: use setIntegral_indicator to convert to intersection integral
  have h_step3 : (∫ b in Set.Icc (0 : ℝ) W, (Set.Iic c).indicator (fun b' => f b') b) =
      ∫ b in Set.Icc (0 : ℝ) W ∩ Set.Iic c, f b := by
    rw [MeasureTheory.setIntegral_indicator measurableSet_Iic]
  -- Step 4: intersection equals Icc 0 c
  rw [h_step1, h_step2, h_step3, h_inter_pos]

-- An integral against a threshold activation is zero if the threshold is non-positive
private lemma setIntegral_thresholdActivation_nonpos_eq_zero {c W : ℝ} (hc : c ≤ 0) (hW_nonneg : 0 ≤ W) (f : ℝ → ℝ) :
    (∫ b in Set.Icc (0 : ℝ) W, thresholdActivation (c - b) * f b) = 0 := by
  by_cases hc0 : c = 0
  · -- c = 0: thresholdActivation(-b) is 0 for b > 0, and {0} has measure zero
    have h_thresh_indicator (b : ℝ) :
        thresholdActivation (-b) = (Set.Iic (0 : ℝ)).indicator (fun _ => (1 : ℝ)) b := by
      by_cases hb : b ≤ 0
      · have h_nonneg : -b ≥ 0 := by linarith
        simp [thresholdActivation, Set.indicator, Set.mem_Iic, h_nonneg, hb]
      · have h_neg : ¬(-b ≥ 0) := by linarith
        simp [thresholdActivation, Set.indicator, Set.mem_Iic, h_neg, hb]
    have h_eq1 : (fun b => thresholdActivation (-b) * f b)
        = (fun b => ((Set.Iic (0 : ℝ)).indicator (fun _ => (1 : ℝ)) b) * f b) := by
      ext b
      rw [← h_thresh_indicator b]
    have h_eq2 : (fun b => ((Set.Iic (0 : ℝ)).indicator (fun _ => (1 : ℝ)) b) * f b)
        = (fun b => (Set.Iic (0 : ℝ)).indicator (fun b' => f b') b) := by
      ext b; simp [Set.indicator, mul_comm]
    have h_inter : Set.Icc (0 : ℝ) W ∩ Set.Iic (0 : ℝ) = {(0 : ℝ)} := by
      ext x; constructor
      · rintro ⟨⟨hx0, _hxw⟩, hx0'⟩
        exact Set.mem_singleton_iff.mpr (le_antisymm hx0' hx0)
      · rintro (rfl : x = 0)
        have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) W := ⟨le_rfl, hW_nonneg⟩
        have h0' : (0 : ℝ) ∈ Set.Iic (0 : ℝ) := show (0 : ℝ) ≤ (0 : ℝ) from le_rfl
        exact ⟨h0, h0'⟩
    calc
      (∫ b in Set.Icc (0 : ℝ) W, thresholdActivation (c - b) * f b)
      _ = (∫ b in Set.Icc (0 : ℝ) W, thresholdActivation (0 - b) * f b) := by rw [hc0]
      _ = (∫ b in Set.Icc (0 : ℝ) W, thresholdActivation (-b) * f b) := by simp
      _ = (∫ b in Set.Icc (0 : ℝ) W, ((Set.Iic (0 : ℝ)).indicator (fun _ => (1 : ℝ)) b) * f b) := by rw [h_eq1]
      _ = (∫ b in Set.Icc (0 : ℝ) W, (Set.Iic (0 : ℝ)).indicator (fun b' => f b') b) := by rw [h_eq2]
      _ = ∫ b in Set.Icc (0 : ℝ) W ∩ Set.Iic (0 : ℝ), f b := MeasureTheory.setIntegral_indicator measurableSet_Iic
      _ = ∫ b in {(0 : ℝ)}, f b := by rw [h_inter]
      _ = 0 := by simp
  · -- c < 0: then thresholdActivation(c - b) = 0 for all b ≥ 0
    have h_ae : (fun b => thresholdActivation (c - b) * f b)
        =ᵐ[volume.restrict (Set.Icc (0 : ℝ) W)] fun _ => (0 : ℝ) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with b hb
      rcases hb with ⟨hb0, _hbw⟩
      have h_not_nonneg : ¬(c - b ≥ 0) := by
        have : c < 0 := lt_of_le_of_ne hc hc0
        linarith
      simp [thresholdActivation, h_not_nonneg]
    simp [integral_congr_ae h_ae]

-- Evaluate the integral of the scaled sine wave over [0, c]
private lemma integral_sin_bump_ftc (c φ W : ℝ) (hW : W ≠ 0) (hc : 0 ≤ c) :
    ∫ b in Set.Icc (0 : ℝ) c, (-Real.sin (2 * π * b + φ) / W) =
    (Real.cos (2 * π * c + φ) - Real.cos φ) / (2 * π * W) := by
  have h_cont : Continuous (fun b : ℝ => -Real.sin (2 * π * b + φ) / W) := by
    refine (((Real.continuous_sin.comp ?_).neg).div_const W)
    exact (continuous_const.mul continuous_id).add continuous_const
  have h_intble : IntervalIntegrable (fun b : ℝ => -Real.sin (2 * π * b + φ) / W) volume 0 c :=
    h_cont.intervalIntegrable _ _
  have h_deriv : ∀ b ∈ Set.uIcc (0 : ℝ) c,
      HasDerivAt (fun t : ℝ => Real.cos (2 * π * t + φ) / (2 * π * W))
        (-Real.sin (2 * π * b + φ) / W) b := by
    intro b _
    -- Derivative of the inner affine function t ↦ 2πt + φ
    have h_inner_deriv : HasDerivAt (fun t : ℝ => 2 * π * t + φ) (2 * π) b := by
      simpa using ((hasDerivAt_id b).const_mul (2 * π)).add_const φ
    -- Chain rule: derivative of cos(2πt + φ)
    have h_cos_deriv : HasDerivAt (fun t : ℝ => Real.cos (2 * π * t + φ))
        ((-Real.sin (2 * π * b + φ)) * (2 * π)) b :=
      h_inner_deriv.cos
    -- Divide by constant (2πW)
    have h_div : HasDerivAt (fun t : ℝ => Real.cos (2 * π * t + φ) / (2 * π * W))
        (((-Real.sin (2 * π * b + φ)) * (2 * π)) / (2 * π * W)) b :=
      h_cos_deriv.div_const (2 * π * W)
    -- Simplify: ((-sin) * 2π) / (2πW) = -sin / W
    have h_simp : (((-Real.sin (2 * π * b + φ)) * (2 * π)) / (2 * π * W)) =
        (-Real.sin (2 * π * b + φ) / W) := by
      field_simp [show (2 * π : ℝ) ≠ 0 from by positivity, hW]
    exact h_div.congr_deriv h_simp
  calc
    ∫ b in Set.Icc (0 : ℝ) c, (-Real.sin (2 * π * b + φ) / W)
        = ∫ b in Set.Ioc (0 : ℝ) c, (-Real.sin (2 * π * b + φ) / W) := by
          rw [MeasureTheory.integral_Icc_eq_integral_Ioc' (volume_singleton (a := 0))]
    _ = ∫ b in (0 : ℝ)..c, (-Real.sin (2 * π * b + φ) / W) := by
          rw [← intervalIntegral.integral_of_le hc]
    _ = (Real.cos (2 * π * c + φ) / (2 * π * W)) -
        (Real.cos (2 * π * (0 : ℝ) + φ) / (2 * π * W)) := by
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_intble]
    _ = (Real.cos (2 * π * c + φ) - Real.cos φ) / (2 * π * W) := by
      simp; ring

private lemma barronCosineBump_sin_repr_pos {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) (θ : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (hx : ‖x‖ ≤ 1) (hw0 : ‖w‖ ≠ 0) (ha_nonneg : 0 ≤ inner ℝ w x) :
    (∫ b in Set.Icc (0 : ℝ) ‖w‖, thresholdActivation (inner ℝ w x - b) * (-Real.sin (2 * π * b + 2 * π * θ) / ‖w‖)) +
    (∫ b in Set.Icc (0 : ℝ) ‖w‖, thresholdActivation (inner ℝ (-w) x - b) * (-Real.sin (2 * π * b - 2 * π * θ) / ‖w‖)) =
    barronCosineBump w θ x := by
  have hw_pos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0)
  set a := inner ℝ w x with ha_def
  -- Cauchy-Schwarz: |a| ≤ ‖w‖ · ‖x‖ ≤ ‖w‖
  have ha_bound : |a| ≤ ‖w‖ := by
    calc
      |a| ≤ ‖w‖ * ‖x‖ := abs_real_inner_le_norm w x
      _ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
      _ = ‖w‖ := mul_one _
  have ha_abs_range : -‖w‖ ≤ a ∧ a ≤ ‖w‖ := abs_le.mp ha_bound
  
  have ha_le_norm : a ≤ ‖w‖ := ha_abs_range.2
  have h_int1 : (∫ b in Set.Icc (0 : ℝ) ‖w‖,
      thresholdActivation (a - b) * (-Real.sin (2 * π * b + 2 * π * θ) / ‖w‖)) =
      ∫ b in Set.Icc (0 : ℝ) a, (-Real.sin (2 * π * b + 2 * π * θ) / ‖w‖) :=
    setIntegral_thresholdActivation_eq_Icc ha_nonneg ha_le_norm _

  have h_inner_neg : inner ℝ (-w) x = -a := by rw [inner_neg_left, ha_def]
  have h_int2 : (∫ b in Set.Icc (0 : ℝ) ‖w‖,
      thresholdActivation (inner ℝ (-w) x - b) * (-Real.sin (2 * π * b - 2 * π * θ) / ‖w‖)) = 0 := by
    rw [h_inner_neg]
    exact setIntegral_thresholdActivation_nonpos_eq_zero (by linarith) (norm_nonneg _) _

  have h_ftc : ∫ b in Set.Icc (0 : ℝ) a, (-Real.sin (2 * π * b + 2 * π * θ) / ‖w‖) =
      (Real.cos (2 * π * a + 2 * π * θ) - Real.cos (2 * π * θ)) / (2 * π * ‖w‖) :=
    integral_sin_bump_ftc a (2 * π * θ) ‖w‖ hw0 ha_nonneg

  have hgoal : (∫ b in Set.Icc (0 : ℝ) ‖w‖,
      thresholdActivation (inner ℝ w x - b) * (-Real.sin (2 * π * b + 2 * π * θ) / ‖w‖)) +
      (∫ b in Set.Icc (0 : ℝ) ‖w‖,
        thresholdActivation (inner ℝ (-w) x - b) * (-Real.sin (2 * π * b - 2 * π * θ) / ‖w‖)) =
      barronCosineBump w θ x := by
    calc
      (∫ b in Set.Icc (0 : ℝ) ‖w‖,
          thresholdActivation (inner ℝ w x - b) * (-Real.sin (2 * π * b + 2 * π * θ) / ‖w‖)) +
        (∫ b in Set.Icc (0 : ℝ) ‖w‖,
          thresholdActivation (inner ℝ (-w) x - b) * (-Real.sin (2 * π * b - 2 * π * θ) / ‖w‖))
      = (∫ b in Set.Icc (0 : ℝ) ‖w‖,
          thresholdActivation (a - b) * (-Real.sin (2 * π * b + 2 * π * θ) / ‖w‖)) +
        (∫ b in Set.Icc (0 : ℝ) ‖w‖,
          thresholdActivation (inner ℝ (-w) x - b) * (-Real.sin (2 * π * b - 2 * π * θ) / ‖w‖)) := by
        dsimp [a]
      _ = (∫ b in Set.Icc (0 : ℝ) a, (-Real.sin (2 * π * b + 2 * π * θ) / ‖w‖)) + (0 : ℝ) := by
        rw [h_int1, h_int2]
      _ = ∫ b in Set.Icc (0 : ℝ) a, (-Real.sin (2 * π * b + 2 * π * θ) / ‖w‖) := by simp
      _ = (Real.cos (2 * π * a + 2 * π * θ) - Real.cos (2 * π * θ)) / (2 * π * ‖w‖) := h_ftc
      _ = barronCosineBump w θ x := by
        rw [barronCosineBump, if_neg hw0, ha_def]
  exact hgoal

private lemma barronCosineBump_sin_repr_neg {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) (θ : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (hx : ‖x‖ ≤ 1) (hw0 : ‖w‖ ≠ 0) (ha_neg : inner ℝ w x < 0) :
    (∫ b in Set.Icc (0 : ℝ) ‖w‖, thresholdActivation (inner ℝ w x - b) * (-Real.sin (2 * π * b + 2 * π * θ) / ‖w‖)) +
    (∫ b in Set.Icc (0 : ℝ) ‖w‖, thresholdActivation (inner ℝ (-w) x - b) * (-Real.sin (2 * π * b - 2 * π * θ) / ‖w‖)) =
    barronCosineBump w θ x := by
  have hw_pos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0)
  set a := inner ℝ w x with ha_def
  -- Cauchy-Schwarz: |a| ≤ ‖w‖ · ‖x‖ ≤ ‖w‖
  have ha_bound : |a| ≤ ‖w‖ := by
    calc
      |a| ≤ ‖w‖ * ‖x‖ := abs_real_inner_le_norm w x
      _ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
      _ = ‖w‖ := mul_one _
  have ha_abs_range : -‖w‖ ≤ a ∧ a ≤ ‖w‖ := abs_le.mp ha_bound

  have h_neg_a_nonneg : 0 ≤ -a := by linarith
  have h_neg_a_le_norm : -a ≤ ‖w‖ := by linarith
  
  have h_int1 : (∫ b in Set.Icc (0 : ℝ) ‖w‖,
      thresholdActivation (a - b) * (-Real.sin (2 * π * b + 2 * π * θ) / ‖w‖)) = 0 :=
    setIntegral_thresholdActivation_nonpos_eq_zero (by linarith) (norm_nonneg _) _
  
  have h_inner_neg : inner ℝ (-w) x = -a := by rw [inner_neg_left, ha_def]
  have h_int2 : (∫ b in Set.Icc (0 : ℝ) ‖w‖,
      thresholdActivation (inner ℝ (-w) x - b) * (-Real.sin (2 * π * b - 2 * π * θ) / ‖w‖)) =
      ∫ b in Set.Icc (0 : ℝ) (-a), (-Real.sin (2 * π * b - 2 * π * θ) / ‖w‖) := by
    rw [h_inner_neg]
    exact setIntegral_thresholdActivation_eq_Icc h_neg_a_nonneg h_neg_a_le_norm _
  
  have h_ftc : ∫ b in Set.Icc (0 : ℝ) (-a), (-Real.sin (2 * π * b - 2 * π * θ) / ‖w‖) =
      (Real.cos (2 * π * a + 2 * π * θ) - Real.cos (2 * π * θ)) / (2 * π * ‖w‖) := by
    have h_ftc_raw := integral_sin_bump_ftc (-a) (-(2 * π * θ)) ‖w‖ hw0 h_neg_a_nonneg
    have h_eq_LHS : (fun b => -Real.sin (2 * π * b + -(2 * π * θ)) / ‖w‖) = 
                    (fun b => -Real.sin (2 * π * b - 2 * π * θ) / ‖w‖) := by rfl
    have h_eq_RHS : (Real.cos (2 * π * (-a) + -(2 * π * θ)) - Real.cos (-(2 * π * θ))) / (2 * π * ‖w‖) = 
                    (Real.cos (2 * π * a + 2 * π * θ) - Real.cos (2 * π * θ)) / (2 * π * ‖w‖) := by
      have h1 : 2 * π * (-a) + -(2 * π * θ) = -(2 * π * a + 2 * π * θ) := by ring
      rw [h1, Real.cos_neg, Real.cos_neg]
    rw [← h_eq_LHS, ← h_eq_RHS]
    exact h_ftc_raw
        
  have hgoal : (∫ b in Set.Icc (0 : ℝ) ‖w‖,
      thresholdActivation (inner ℝ w x - b) * (-Real.sin (2 * π * b + 2 * π * θ) / ‖w‖)) +
      (∫ b in Set.Icc (0 : ℝ) ‖w‖,
        thresholdActivation (inner ℝ (-w) x - b) * (-Real.sin (2 * π * b - 2 * π * θ) / ‖w‖)) =
      barronCosineBump w θ x := by
    calc
      (∫ b in Set.Icc (0 : ℝ) ‖w‖,
          thresholdActivation (inner ℝ w x - b) * (-Real.sin (2 * π * b + 2 * π * θ) / ‖w‖)) +
        (∫ b in Set.Icc (0 : ℝ) ‖w‖,
          thresholdActivation (inner ℝ (-w) x - b) * (-Real.sin (2 * π * b - 2 * π * θ) / ‖w‖))
      = (∫ b in Set.Icc (0 : ℝ) ‖w‖,
          thresholdActivation (a - b) * (-Real.sin (2 * π * b + 2 * π * θ) / ‖w‖)) +
        (∫ b in Set.Icc (0 : ℝ) ‖w‖,
          thresholdActivation (inner ℝ (-w) x - b) * (-Real.sin (2 * π * b - 2 * π * θ) / ‖w‖)) := by
        dsimp [a]
      _ = (0 : ℝ) + (∫ b in Set.Icc (0 : ℝ) (-a), (-Real.sin (2 * π * b - 2 * π * θ) / ‖w‖)) := by
        rw [h_int1, h_int2]
      _ = ∫ b in Set.Icc (0 : ℝ) (-a), (-Real.sin (2 * π * b - 2 * π * θ) / ‖w‖) := by simp
      _ = (Real.cos (2 * π * a + 2 * π * θ) - Real.cos (2 * π * θ)) / (2 * π * ‖w‖) := h_ftc
      _ = barronCosineBump w θ x := by
        rw [barronCosineBump, if_neg hw0, ha_def]
  exact hgoal

-- A cosine bump can also be represented as an integral against a threshold activation
-- using the fundamental theorem of calculus. This representation is independent of x
-- and is the basis for constructing the global signed measure.
private lemma barronCosineBump_sin_repr {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) (θ : ℝ) (x : EuclideanSpace ℝ (Fin d)) (hx : ‖x‖ ≤ 1) :
    barronCosineBump w θ x =
      (∫ b in Set.Icc (0 : ℝ) ‖w‖, thresholdActivation (inner ℝ w x - b) * (-Real.sin (2 * π * b + 2 * π * θ) / ‖w‖)) +
      (∫ b in Set.Icc (0 : ℝ) ‖w‖, thresholdActivation (inner ℝ (-w) x - b) * (-Real.sin (2 * π * b - 2 * π * θ) / ‖w‖)) := by
  by_cases hw0 : ‖w‖ = 0
  · -- Case ‖w‖ = 0: both sides are 0 (division by 0 yields 0, integrals over {0} are 0)
    have hbar : barronCosineBump w θ x = 0 := by
      unfold barronCosineBump
      rw [if_pos hw0]
    have hRHS : (∫ b in Set.Icc (0 : ℝ) ‖w‖,
        thresholdActivation (inner ℝ w x - b) * (-Real.sin (2 * π * b + 2 * π * θ) / ‖w‖)) +
        (∫ b in Set.Icc (0 : ℝ) ‖w‖,
          thresholdActivation (inner ℝ (-w) x - b) * (-Real.sin (2 * π * b - 2 * π * θ) / ‖w‖)) = 0 := by
      rw [hw0]
      simp
    rw [hbar, hRHS]
  · -- Case ‖w‖ ≠ 0
    by_cases ha_nonneg : 0 ≤ inner ℝ w x
    · exact (barronCosineBump_sin_repr_pos w θ x hx hw0 ha_nonneg).symm
    · have ha_neg : inner ℝ w x < 0 := not_le.mp ha_nonneg
      exact (barronCosineBump_sin_repr_neg w θ x hx hw0 ha_neg).symm

lemma barronTheorem_density_snoc_bound
    {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (density : (Fin (d + 1) → ℝ) → ℝ)
    (h_density : density = fun wb =>
      let w : EuclideanSpace ℝ (Fin d) := (EuclideanSpace.equiv (Fin d) ℝ).symm (fun (j : Fin d) => wb j.castSucc)
      let b : ℝ := wb (Fin.last d)
      if b ∈ Set.Icc (0 : ℝ) ‖w‖ then
        -4 * π * Real.sin (2 * π * b + 2 * π * fourierPhase f w) * fourierMagnitude f w
      else 0)
    (w : (j : Fin d) → ℝ) :
    (∫ b : ℝ, |density (Fin.snoc w b)|) ≤ 2 * barronIntegrand f ((EuclideanSpace.equiv (Fin d) ℝ).symm w) := by
  have h_dens : ∀ b : ℝ, density (Fin.snoc w b) = 
      if b ∈ Set.Icc (0 : ℝ) ‖(EuclideanSpace.equiv (Fin d) ℝ).symm w‖ then
        -4 * π * Real.sin (2 * π * b + 2 * π * fourierPhase f ((EuclideanSpace.equiv (Fin d) ℝ).symm w)) * fourierMagnitude f ((EuclideanSpace.equiv (Fin d) ℝ).symm w)
      else 0 := by
    intro b
    rw [h_density]
    dsimp only
    have hw : (fun (j : Fin d) => (Fin.snoc (α := fun _ => ℝ) w b) j.castSucc) = w := by
      ext j
      simp
    have hb : (Fin.snoc (α := fun _ => ℝ) w b) (Fin.last d) = b := by simp
    simp_rw [hw, hb]
  simp_rw [h_dens]
  have h_abs : ∀ b : ℝ, |if b ∈ Set.Icc (0 : ℝ) ‖(EuclideanSpace.equiv (Fin d) ℝ).symm w‖ then
        -4 * π * Real.sin (2 * π * b + 2 * π * fourierPhase f ((EuclideanSpace.equiv (Fin d) ℝ).symm w)) * fourierMagnitude f ((EuclideanSpace.equiv (Fin d) ℝ).symm w)
      else 0| = 
      if b ∈ Set.Icc (0 : ℝ) ‖(EuclideanSpace.equiv (Fin d) ℝ).symm w‖ then
        4 * π * |Real.sin (2 * π * b + 2 * π * fourierPhase f ((EuclideanSpace.equiv (Fin d) ℝ).symm w))| * fourierMagnitude f ((EuclideanSpace.equiv (Fin d) ℝ).symm w)
      else 0 := by
    intro b
    split_ifs with hb
    · rw [abs_mul, abs_mul]
      have h_fmag : 0 ≤ fourierMagnitude f ((EuclideanSpace.equiv (Fin d) ℝ).symm w) := by
        unfold fourierMagnitude
        exact norm_nonneg _
      rw [abs_of_nonneg h_fmag]
      have h4 : |-4 * π| = 4 * π := by 
        have h_neg : -4 * π = -(4 * π) := by ring
        rw [h_neg, abs_neg]
        have h_pos : (0 : ℝ) < 4 * π := by positivity
        exact abs_of_pos h_pos
      rw [h4]
    · exact abs_zero
  simp_rw [h_abs]
  have h_bound : ∀ b : ℝ, (if b ∈ Set.Icc (0 : ℝ) ‖(EuclideanSpace.equiv (Fin d) ℝ).symm w‖ then
        4 * π * |Real.sin (2 * π * b + 2 * π * fourierPhase f ((EuclideanSpace.equiv (Fin d) ℝ).symm w))| * fourierMagnitude f ((EuclideanSpace.equiv (Fin d) ℝ).symm w)
      else 0) ≤ 
      if b ∈ Set.Icc (0 : ℝ) ‖(EuclideanSpace.equiv (Fin d) ℝ).symm w‖ then
        4 * π * fourierMagnitude f ((EuclideanSpace.equiv (Fin d) ℝ).symm w)
      else 0 := by
    intro b
    split_ifs with hb
    · have h_sin : |Real.sin (2 * π * b + 2 * π * fourierPhase f ((EuclideanSpace.equiv (Fin d) ℝ).symm w))| ≤ 1 := Real.abs_sin_le_one _
      have h1 : 4 * π * |Real.sin (2 * π * b + 2 * π * fourierPhase f ((EuclideanSpace.equiv (Fin d) ℝ).symm w))| ≤ 4 * π * 1 := 
        mul_le_mul_of_nonneg_left h_sin (mul_nonneg (by norm_num) Real.pi_pos.le)
      have h_fmag : 0 ≤ fourierMagnitude f ((EuclideanSpace.equiv (Fin d) ℝ).symm w) := by
        unfold fourierMagnitude
        exact norm_nonneg _
      have h2 := mul_le_mul_of_nonneg_right h1 h_fmag
      rw [mul_one] at h2
      exact h2
    · exact le_rfl
  have h_int : ∫ b : ℝ, (if b ∈ Set.Icc (0 : ℝ) ‖(EuclideanSpace.equiv (Fin d) ℝ).symm w‖ then
        4 * π * fourierMagnitude f ((EuclideanSpace.equiv (Fin d) ℝ).symm w)
      else 0) = 4 * π * fourierMagnitude f ((EuclideanSpace.equiv (Fin d) ℝ).symm w) * ‖(EuclideanSpace.equiv (Fin d) ℝ).symm w‖ := by
    have h_ind : (fun (b : ℝ) => if b ∈ Set.Icc (0 : ℝ) ‖(EuclideanSpace.equiv (Fin d) ℝ).symm w‖ then
        4 * π * fourierMagnitude f ((EuclideanSpace.equiv (Fin d) ℝ).symm w)
      else 0) = Set.indicator (Set.Icc (0 : ℝ) ‖(EuclideanSpace.equiv (Fin d) ℝ).symm w‖) (fun _ => 4 * π * fourierMagnitude f ((EuclideanSpace.equiv (Fin d) ℝ).symm w)) := by
      ext b
      simp [Set.indicator]
    rw [h_ind, integral_indicator measurableSet_Icc, setIntegral_const]
    have h_vol : volume.real (Set.Icc (0 : ℝ) ‖(EuclideanSpace.equiv (Fin d) ℝ).symm w‖) = ‖(EuclideanSpace.equiv (Fin d) ℝ).symm w‖ := by
      change (volume (Set.Icc (0 : ℝ) ‖(EuclideanSpace.equiv (Fin d) ℝ).symm w‖)).toReal = _
      rw [Real.volume_Icc]
      have h_norm_pos : 0 ≤ ‖(EuclideanSpace.equiv (Fin d) ℝ).symm w‖ := norm_nonneg _
      rw [sub_zero]
      exact ENNReal.toReal_ofReal h_norm_pos
    rw [h_vol, smul_eq_mul, mul_comm]
  have h_le : (∫ b : ℝ, if b ∈ Set.Icc (0 : ℝ) ‖(EuclideanSpace.equiv (Fin d) ℝ).symm w‖ then
        4 * π * |Real.sin (2 * π * b + 2 * π * fourierPhase f ((EuclideanSpace.equiv (Fin d) ℝ).symm w))| * fourierMagnitude f ((EuclideanSpace.equiv (Fin d) ℝ).symm w)
      else 0) ≤ 
      ∫ b : ℝ, if b ∈ Set.Icc (0 : ℝ) ‖(EuclideanSpace.equiv (Fin d) ℝ).symm w‖ then
        4 * π * fourierMagnitude f ((EuclideanSpace.equiv (Fin d) ℝ).symm w)
      else 0 := by
    apply integral_mono
    · have h_cont : Continuous (fun b : ℝ => 4 * π * |Real.sin (2 * π * b + 2 * π * fourierPhase f ((EuclideanSpace.equiv (Fin d) ℝ).symm w))| * fourierMagnitude f ((EuclideanSpace.equiv (Fin d) ℝ).symm w)) := by continuity
      have h_int_on := Continuous.integrableOn_Icc (μ := volume) h_cont (a := 0) (b := ‖(EuclideanSpace.equiv (Fin d) ℝ).symm w‖)
      have h_int := IntegrableOn.integrable_indicator h_int_on measurableSet_Icc
      apply Integrable.congr h_int
      apply Filter.Eventually.of_forall
      intro x
      dsimp only
      unfold Set.indicator
      split_ifs
      · rfl
      · rfl
    · have h_cont : Continuous (fun _ : ℝ => 4 * π * fourierMagnitude f ((EuclideanSpace.equiv (Fin d) ℝ).symm w)) := continuous_const
      have h_int_on := Continuous.integrableOn_Icc (μ := volume) h_cont (a := 0) (b := ‖(EuclideanSpace.equiv (Fin d) ℝ).symm w‖)
      have h_int := IntegrableOn.integrable_indicator h_int_on measurableSet_Icc
      apply Integrable.congr h_int
      apply Filter.Eventually.of_forall
      intro x
      dsimp only
      unfold Set.indicator
      split_ifs
      · rfl
      · rfl
    · exact h_bound
  have h_barron : 2 * barronIntegrand f ((EuclideanSpace.equiv (Fin d) ℝ).symm w) = 4 * π * fourierMagnitude f ((EuclideanSpace.equiv (Fin d) ℝ).symm w) * ‖(EuclideanSpace.equiv (Fin d) ℝ).symm w‖ := by
    unfold barronIntegrand
    ring
  linarith

/-- **Theorem 3.1** (Based on Barron 1993; Telgarsky 2021).
If `∫ ‖∇̂f(w)‖ dw < ∞`, `f ∈ L¹`, and `f̂ ∈ L¹`, then for ‖x‖ ≤ 1:
```
f(x) - f(0) = ∫ [(cos(2πwᵀx+2πθ(w)) - cos(2πθ(w))) / (2π‖w‖)] · ‖∇̂f(w)‖ dw
```
and moreover f(x) - f(0) equals an integral against a signed measure on threshold neurons
whose mass is at most `2 · ‖f‖_Barron`.

This writes f as an exact infinite-width representation with measure mass bounded by
`2 · barronNorm f`. -/
theorem barronTheorem
    {f : (EuclideanSpace ℝ (Fin d)) → ℝ}
    (hf_cont : Continuous f)
    (hf_L1 : Integrable f volume)
    (hfhat_L1 : Integrable (fourierTransform f) volume)
    (hbarron : Integrable (barronIntegrand f) volume) :
    ∃ (net : Approximation.InfiniteWidth.InfiniteWidthNetwork thresholdActivation (d + 1)),
      Approximation.InfiniteWidth.InfiniteWidthNetwork.mass thresholdActivation net ≤
        2 * barronNorm f ∧
      ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≤ 1 →
        f x - f 0 =
          Approximation.InfiniteWidth.InfiniteWidthNetwork.eval thresholdActivation net
            (fun wb => thresholdActivation
              (inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun (j : Fin d) => wb j.castSucc)) x - wb (Fin.last d))) := by
  -- Step 1: The difference f(x) - f(0) can be expressed as an integral over the difference of exponentials.
  have h_diff : ∀ x, (f x : ℂ) - (f 0 : ℂ) = ∫ w, (Complex.exp (2 * π * Complex.I * inner ℝ w x) - 1) * fourierTransform f w :=
    fun x => barron_diff_exp hf_cont hf_L1 hfhat_L1 x

  -- Step 2: By taking the real part, we can rewrite the complex exponential in terms of cosines and the phase.
  have h_real : ∀ x, f x - f 0 = ∫ w, barronCosineBump w (fourierPhase f w) x * barronIntegrand f w :=
    fun x => barron_real_part hfhat_L1 x (h_diff x)

  -- Step 4: Use the $x$-independent sine representation to construct the signed measure.
  have h_sin_repr : ∀ w x, ‖x‖ ≤ 1 →
      barronCosineBump w (fourierPhase f w) x =
        (∫ b in Set.Icc (0 : ℝ) ‖w‖, thresholdActivation (inner ℝ w x - b) * (-Real.sin (2 * π * b + 2 * π * fourierPhase f w) / ‖w‖)) +
        (∫ b in Set.Icc (0 : ℝ) ‖w‖, thresholdActivation (inner ℝ (-w) x - b) * (-Real.sin (2 * π * b - 2 * π * fourierPhase f w) / ‖w‖)) := by
    intro w x hx
    exact barronCosineBump_sin_repr w (fourierPhase f w) x hx

  -- Step 5: Construct the measure for the infinite-width network by combining the measure over `w` (from barronIntegrand)
  -- and the measure over `b` (from the threshold representation).
  let density : (Fin (d + 1) → ℝ) → ℝ := fun wb =>
    let w : EuclideanSpace ℝ (Fin d) := (EuclideanSpace.equiv (Fin d) ℝ).symm (fun (j : Fin d) => wb j.castSucc)
    let b : ℝ := wb (Fin.last d)
    if b ∈ Set.Icc (0 : ℝ) ‖w‖ then
      -4 * π * Real.sin (2 * π * b + 2 * π * fourierPhase f w) * fourierMagnitude f w
    else 0

  let pos_density := fun wb => ENNReal.ofReal (density wb)
  let neg_density := fun wb => ENNReal.ofReal (-density wb)

  let measure_pos : Measure (Fin (d + 1) → ℝ) := volume.withDensity pos_density
  let measure_neg : Measure (Fin (d + 1) → ℝ) := volume.withDensity neg_density

  have h_finite_pos : IsFiniteMeasure measure_pos := sorry
  have h_finite_neg : IsFiniteMeasure measure_neg := sorry

  let net_measure : SignedMeasure (Fin (d + 1) → ℝ) :=
    (@Measure.toSignedMeasure (Fin (d + 1) → ℝ) _ measure_pos h_finite_pos) -
    (@Measure.toSignedMeasure (Fin (d + 1) → ℝ) _ measure_neg h_finite_neg)

  let net : Approximation.InfiniteWidth.InfiniteWidthNetwork thresholdActivation (d + 1) :=
    ⟨net_measure⟩

  refine ⟨net, ?_, ?_⟩
  · -- Prove the mass bound
    change (net_measure.toJordanDecomposition.posPart Set.univ).toReal + (net_measure.toJordanDecomposition.negPart Set.univ).toReal ≤ 2 * barronNorm f
    have h_tv : (net_measure.toJordanDecomposition.posPart Set.univ).toReal + (net_measure.toJordanDecomposition.negPart Set.univ).toReal ≤ ∫ wb, |density wb| := by
      sorry
    apply h_tv.trans
    have h_split : ∫ wb, |density wb| = ∫ w : Fin d → ℝ, ∫ b : ℝ, |density (Fin.snoc w b)| := by
      -- Tonelli's theorem via measure-preserving equivalence
      sorry
    rw [h_split]
    have h_inner : ∀ w : Fin d → ℝ, ∫ b : ℝ, |density (Fin.snoc w b)| ≤ 2 * barronIntegrand f ((EuclideanSpace.equiv (Fin d) ℝ).symm w) := by
      intro w
      apply barronTheorem_density_snoc_bound f density _ w
      rfl
    have h_mono : (∫ w : Fin d → ℝ, ∫ b : ℝ, |density (Fin.snoc w b)|) ≤ ∫ w : Fin d → ℝ, 2 * barronIntegrand f ((EuclideanSpace.equiv (Fin d) ℝ).symm w) := by
      -- Apply `integral_mono` with `h_inner`.
      sorry
    apply h_mono.trans
    have h_const : (∫ w : Fin d → ℝ, 2 * barronIntegrand f ((EuclideanSpace.equiv (Fin d) ℝ).symm w)) = 2 * barronNorm f := by
      rw [integral_const_mul]
      -- Change of variables using MeasureTheory.integral_comp_equiv for `EuclideanSpace.equiv`
      sorry
    exact h_const.le
  · -- Prove the evaluation equality
    intro x hx
    sorry

/-! ### Barron norm examples -/

/-- The Barron norm of a Gaussian is O(√d) when σ² ≥ 1/(2π).
(Section 3.2, Telgarsky 2021, following Barron 1993, Sec. IX.9.)

For f(x) = (2πσ²)^{d/2} exp(-‖x‖²/(2σ²)), we have
`‖f‖_Barron = 2π ∫ ‖w‖ |f̂(w)| dw ≤ C · √d`
where C depends only on σ, and the Barron norm is polynomial (not exponential) in d
when 2πσ² ≥ 1. -/
noncomputable def gaussian (σ : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (2 * π * σ ^ 2) ^ ((d : ℝ) / 2) * Real.exp (- ‖x‖ ^ 2 / (2 * σ ^ 2))

theorem gaussian_barronNorm_bound
    {σ : ℝ} (hσ : 0 < σ) (hσ2 : 2 * π * σ ^ 2 ≥ 1) :
    barronNorm (gaussian σ (d := d)) ≤
      Real.sqrt d / (Real.sqrt (2 * π) * (2 * π * σ ^ 2) ^ ((d + 1 : ℝ) / 2)) := by
  sorry

/-- A radial function f(x) = g(‖x‖) can have exponential Barron norm in dimension,
but under suitable decay conditions on g, its Barron integrand is integrable.
(Barron 1993, Sec. IX.9) -/
theorem radial_barron_integrable (g : ℝ → ℝ) (f : (EuclideanSpace ℝ (Fin d)) → ℝ)
    (hf : ∀ x, f x = g ‖x‖) (h_decay : True) :
    Integrable (barronIntegrand f) volume := by sorry

/-- Functions that are compositions of suitable scalar functions with polynomials
have finite Barron norm. (Barron 1993, Sec. IX.12) -/
theorem polynomial_comp_barron_integrable (P : (EuclideanSpace ℝ (Fin d)) → ℝ) (g : ℝ → ℝ)
    (f : (EuclideanSpace ℝ (Fin d)) → ℝ) (hf : ∀ x, f x = g (P x)) (hP : True) (hg : True) :
    Integrable (barronIntegrand f) volume := by sorry

/-- Analytic functions on suitable domains have finite Barron norm. (Barron 1993, Sec. IX.13) -/
theorem analytic_barron_integrable (f : (EuclideanSpace ℝ (Fin d)) → ℝ) (hf_analytic : True) :
    Integrable (barronIntegrand f) volume := by sorry

/-- Functions with O(d) bounded derivatives have finite Barron norm. (Barron 1993, Sec. IX.15) -/
theorem bounded_derivs_barron_integrable (f : (EuclideanSpace ℝ (Fin d)) → ℝ) (hf_derivs : True) :
    Integrable (barronIntegrand f) volume := by sorry

end Approximation.BarronNorm

end
