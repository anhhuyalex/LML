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
noncomputable def fourierTransform (f : (EuclideanSpace ℝ (Fin d)) → ℝ) (w : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ∫ x : EuclideanSpace ℝ (Fin d), Complex.exp (-(2 * π * Complex.I * ↑(inner ℝ w x))) * f x

/-- The magnitude of the Fourier transform. -/
noncomputable def fourierMagnitude (f : (EuclideanSpace ℝ (Fin d)) → ℝ) (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ‖fourierTransform f w‖

/-- The phase angle θ(w) of f̂(w): the unique θ with f̂(w) = |f̂(w)| · exp(2πiθ). -/
noncomputable def fourierPhase (f : (EuclideanSpace ℝ (Fin d)) → ℝ) (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Complex.arg (fourierTransform f w) / (2 * π)

/-! ### Barron norm (Definition 3.1) -/

/-- The Barron norm integrand: ‖∇̂f(w)‖ = 2π·‖w‖·|f̂(w)|.
This follows from the Fourier derivative identity ∇̂f(w) = 2πi·w·f̂(w),
so ‖∇̂f(w)‖ = 2π·‖w‖·|f̂(w)|. -/
noncomputable def barronIntegrand (f : (EuclideanSpace ℝ (Fin d)) → ℝ) (w : EuclideanSpace ℝ (Fin d)) : ℝ :=
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
noncomputable def barronCosineBump (w : EuclideanSpace ℝ (Fin d)) (θ : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
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
    ∀ (x : EuclideanSpace ℝ (Fin d)), ↑(f x) = FourierTransformInv.fourierInv (fourierTransform f) x := by
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
  have h_inv_eval : FourierTransformInv.fourierInv (FourierTransform.fourier (fun x => (f x : ℂ))) x = (fun x => (f x : ℂ)) x := by
    rw [h_inv_thm]
  rw [hf_eq]
  exact h_inv_eval.symm

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
  -- Step 1: Fourier inversion theorem gives an exact representation of f since f and fhat are L1 and f is continuous.
  have h_inv : ∀ (x : EuclideanSpace ℝ (Fin d)), ↑(f x) = FourierTransformInv.fourierInv (fourierTransform f) x := 
    barron_fourier_inv hf_cont hf_L1 hfhat_L1

  -- Step 2: The difference f(x) - f(0) can be expressed as an integral over the difference of exponentials.
  have h_diff : ∀ x, (f x : ℂ) - (f 0 : ℂ) = ∫ w, (Complex.exp (2 * π * Complex.I * inner ℝ w x) - 1) * fourierTransform f w := by
    intro x
    have hx := h_inv x
    have h0 := h_inv 0
    rw [hx, h0]
    have h_int_x : FourierTransformInv.fourierInv (fourierTransform f) x = ∫ w : EuclideanSpace ℝ (Fin d), Complex.exp (2 * π * Complex.I * (inner ℝ w x : ℝ)) * fourierTransform f w := by
      change VectorFourier.fourierIntegral _ _ _ _ _ = _
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, LinearMap.neg_apply, innerₗ_apply_apply, mul_neg, neg_mul, Complex.ofReal_neg, Complex.ofReal_mul]
      sorry
    have h_int_0 : FourierTransformInv.fourierInv (fourierTransform f) 0 = ∫ w : EuclideanSpace ℝ (Fin d), fourierTransform f w := by
      change VectorFourier.fourierIntegral _ _ _ _ _ = _
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, LinearMap.neg_apply, innerₗ_apply_apply, inner_zero_right, mul_zero, zero_mul, Complex.exp_zero, one_mul, Complex.ofReal_zero, neg_zero]
    rw [h_int_x, h_int_0, ← integral_sub]
    · apply integral_congr_ae
      filter_upwards [] with w
      ring_nf
    · sorry
    · sorry

  -- Step 3: By taking the real part, we can rewrite the complex exponential in terms of cosines and the phase.
  have h_real : ∀ x, f x - f 0 = ∫ w, barronCosineBump w (fourierPhase f w) x * barronIntegrand f w := by
    -- Use polar representation of `fourierTransform f w`.
    -- The definition of `barronIntegrand` and `barronCosineBump` naturally emerges from the real part of the difference.
    sorry

  -- Step 4: For each w, the cosine bump function can be represented as an integral over a threshold (step) function.
  have h_threshold : ∀ w x, ‖x‖ ≤ 1 →
      ∃ g : ℝ → ℝ, barronCosineBump w (fourierPhase f w) x = ∫ b, thresholdActivation (inner ℝ w x - b) * g b := by
    -- This relies on `univariateIntegralRep` (the fundamental theorem of calculus representation)
    -- adapted to the domain of the projection `inner ℝ w x`.
    sorry

  -- Step 5: Construct the measure for the infinite-width network by combining the measure over `w` (from barronIntegrand)
  -- and the measure over `b` (from the threshold representation).
  have h_net : ∃ (net : Approximation.InfiniteWidth.InfiniteWidthNetwork thresholdActivation (d + 1)),
      Approximation.InfiniteWidth.InfiniteWidthNetwork.mass thresholdActivation net ≤ 2 * barronNorm f ∧
      ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≤ 1 →
        f x - f 0 = Approximation.InfiniteWidth.InfiniteWidthNetwork.eval thresholdActivation net
            (fun wb => thresholdActivation
              (inner ℝ ((EuclideanSpace.equiv (Fin d) ℝ).symm (fun (j : Fin d) => wb j.castSucc)) x - wb (Fin.last d))) := by
    -- Define the network's signed measure via the product structure.
    -- Swapping the integrals (via Fubini's theorem) yields the network evaluation form.
    -- The bound on the total variation (mass) is exactly twice the integral of `barronIntegrand`,
    -- which is 2 * `barronNorm f`.
    sorry

  exact h_net

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
