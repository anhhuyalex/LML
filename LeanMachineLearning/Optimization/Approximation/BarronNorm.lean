/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Approximation.InfiniteWidth
public import Mathlib.Analysis.Fourier.FourierTransform
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

/-- The standard inner product on ℝᵈ (via Fin d → ℝ). -/
noncomputable def innerProd (w x : Fin d → ℝ) : ℝ :=
  ∑ j, w j * x j

/-- The Fourier transform of f : ℝᵈ → ℝ.
`𝓕 f(w) = ∫ exp(-2πi ⟨w, x⟩) f(x) dx`. -/
noncomputable def fourierTransform (f : (Fin d → ℝ) → ℝ) (w : Fin d → ℝ) : ℂ :=
  ∫ x : Fin d → ℝ, Complex.exp (-(2 * π * Complex.I * innerProd w x)) * f x

/-- The magnitude of the Fourier transform. -/
noncomputable def fourierMagnitude (f : (Fin d → ℝ) → ℝ) (w : Fin d → ℝ) : ℝ :=
  ‖fourierTransform f w‖

/-- The phase angle θ(w) of f̂(w): the unique θ with f̂(w) = |f̂(w)| · exp(2πiθ). -/
noncomputable def fourierPhase (f : (Fin d → ℝ) → ℝ) (w : Fin d → ℝ) : ℝ :=
  Complex.arg (fourierTransform f w) / (2 * π)

/-! ### Barron norm (Definition 3.1) -/

/-- The Barron norm integrand: ‖∇̂f(w)‖ = 2π·‖w‖·|f̂(w)|.
This follows from the Fourier derivative identity ∇̂f(w) = 2πi·w·f̂(w),
so ‖∇̂f(w)‖ = 2π·‖w‖·|f̂(w)|. -/
noncomputable def barronIntegrand (f : (Fin d → ℝ) → ℝ) (w : Fin d → ℝ) : ℝ :=
  2 * π * ‖w‖ * fourierMagnitude f w

/-- **Definition 3.1** (Barron 1993; Telgarsky 2021).
The *Barron norm* of f : ℝᵈ → ℝ is
  `‖f‖_Barron := ∫ ‖∇̂f(w)‖ dw = 2π ∫ ‖w‖ · |f̂(w)| dw`.
The corresponding *Barron class with norm C* is
  `ℱ_C := {f : ℝᵈ → ℝ | ‖f‖_Barron ≤ C}`. -/
noncomputable def barronNorm (f : (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ w : Fin d → ℝ, barronIntegrand f w

/-- The Barron class: functions with Barron norm at most C. -/
def BarronClass (C : ℝ) (d : ℕ) : Set ((Fin d → ℝ) → ℝ) :=
  {f | ∃ _ : Integrable (barronIntegrand f) volume, barronNorm f ≤ C}

/-- Barron norm is nonneg. -/
lemma barronNorm_nonneg (f : (Fin d → ℝ) → ℝ) : 0 ≤ barronNorm f := by
  apply MeasureTheory.integral_nonneg
  intro w
  simp only [barronIntegrand, fourierMagnitude]
  positivity

/-! ### Barron representation (Theorem 3.1) -/

/-- The cosine bump function used in Barron's construction:
  `(cos(2π wᵀx + 2πθ) - cos(2πθ)) / (2π‖w‖)`.
This is Lipschitz in x (bounded by ‖x‖) and is the building block of the
infinite-width threshold representation. -/
noncomputable def barronCosineBump (w : Fin d → ℝ) (θ : ℝ) (x : Fin d → ℝ) : ℝ :=
  if ‖w‖ = 0 then 0
  else (Real.cos (2 * π * innerProd w x + 2 * π * θ) - Real.cos (2 * π * θ)) /
       (2 * π * ‖w‖)

/-- The Barron cosine bump is bounded by ‖x‖ (pointwise). -/
lemma barronCosineBump_bound (w : Fin d → ℝ) (θ : ℝ) (x : Fin d → ℝ) :
    |barronCosineBump w θ x| ≤ ‖x‖ := by
  simp only [barronCosineBump]
  split_ifs with hw
  · simp
  · rw [abs_div]
    rw [div_le_iff₀ (by positivity)]
    calc |Real.cos (2 * π * innerProd w x + 2 * π * θ) - Real.cos (2 * π * θ)|
        ≤ |2 * π * innerProd w x + 2 * π * θ - 2 * π * θ| := by
          have h := LipschitzWith.dist_le_mul Real.lipschitzWith_cos (2 * π * innerProd w x + 2 * π * θ) (2 * π * θ)
          rw [Real.dist_eq, Real.dist_eq] at h
          simpa using h
      _ = |2 * π * innerProd w x| := by
          congr 1
          ring
      _ = 2 * π * |innerProd w x| := by
          have : (2 : ℝ) * π * innerProd w x = (2 * π) * innerProd w x := by ring
          rw [this, abs_mul, abs_of_pos Real.two_pi_pos]
      _ ≤ 2 * π * (‖w‖ * ‖x‖) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt Real.two_pi_pos)
          exact sorry
      _ = ‖x‖ * (2 * π * ‖w‖) := by
          ring
      _ = ‖x‖ * |2 * π * ‖w‖| := by
          have hw_pos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)
          have h_pos : 0 < 2 * π * ‖w‖ := mul_pos Real.two_pi_pos hw_pos
          rw [abs_of_pos h_pos]

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
    {f : (Fin d → ℝ) → ℝ}
    (hf_L1 : Integrable f volume)
    (hfhat_L1 : Integrable (fourierTransform f) volume)
    (hbarron : Integrable (barronIntegrand f) volume) :
    ∃ (net : Approximation.InfiniteWidth.InfiniteWidthNetwork thresholdActivation (d + 1)),
      Approximation.InfiniteWidth.InfiniteWidthNetwork.mass thresholdActivation net ≤
        2 * barronNorm f ∧
      ∀ x : Fin d → ℝ, ‖x‖ ≤ 1 →
        f x - f 0 =
          Approximation.InfiniteWidth.InfiniteWidthNetwork.eval thresholdActivation net
            (fun wb => thresholdActivation
              (innerProd (fun j => wb j.castSucc) x - wb (Fin.last d))) := by
  sorry

/-! ### Barron norm examples -/

/-- The Barron norm of a Gaussian is O(√d) when σ² ≥ 1/(2π).
(Section 3.2, Telgarsky 2021, following Barron 1993, Sec. IX.9.)

For f(x) = (2πσ²)^{d/2} exp(-‖x‖²/(2σ²)), we have
`‖f‖_Barron = 2π ∫ ‖w‖ |f̂(w)| dw ≤ C · √d`
where C depends only on σ, and the Barron norm is polynomial (not exponential) in d
when 2πσ² ≥ 1. -/
noncomputable def gaussian (σ : ℝ) (x : Fin d → ℝ) : ℝ :=
  (2 * π * σ ^ 2) ^ ((d : ℝ) / 2) * Real.exp (- ‖x‖ ^ 2 / (2 * σ ^ 2))

theorem gaussian_barronNorm_bound
    {σ : ℝ} (hσ : 0 < σ) (hσ2 : 2 * π * σ ^ 2 ≥ 1) :
    barronNorm (gaussian σ (d := d)) ≤
      Real.sqrt d / (Real.sqrt (2 * π) * (2 * π * σ ^ 2) ^ ((d + 1 : ℝ) / 2)) := by
  sorry

end Approximation.BarronNorm

end
