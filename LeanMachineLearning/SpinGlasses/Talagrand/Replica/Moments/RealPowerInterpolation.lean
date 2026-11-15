/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Gaussian.GaussianInterpolationNonlinear

/-!
# Interpolation derivative of a real moment of a partition function

Talagrand, *Spin Glasses* Vol. I, end of Section 1.13: the real moment `𝔼 Z_s^t` of the partition
function `Z_s = ∑ₐ exp (cos s X a + sin s Y a + h a)` along the trigonometric path.  This is the
case `W = exp` of `hasDerivAt_integral_comp_log_sum_exp_trig`, since `Z^t = exp (t log Z)`:
the Hessian of `u ↦ (∑ₐ exp (u a + h a))^t` is `t Z^t (δ_{ab} wₐ + (t - 1) wₐ w_b)` with the Gibbs
weights `w`, written below in the equivalent form `Z^t (t² wₗ wₖ + t wₗ (δ - wₖ))`.

## Main declarations

* `SpinGlasses.freeEnergyCompHessian_exp`: the Hessian entry for `W = exp`.
* `SpinGlasses.hasDerivAt_integral_exp_mul_log_sum_exp_trig_hessian`: the derivative of
  `s ↦ 𝔼 exp (n log Z_s)` for a real `n`, in covariance (Hessian) form; the first-derivative form
  for the normalized difference `log Z_s - log Z_{π/2}` is
  `SpinGlasses.hasDerivAt_integral_exp_mul_log_sum_exp_trig`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Real

namespace SpinGlasses

section

variable {κ Ω : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {X Y : κ → Ω → ℝ}

omit [Nonempty κ] in
/-- **The Hessian entry for `W = exp`:** `exp (n L) (n² wₗ wₖ + n wₗ (1[l = k] - wₖ))` with the
Gibbs weights `w` and `L = log ∑ₐ exp (y a + h a)`. -/
theorem freeEnergyCompHessian_exp (n : ℝ) (h y : κ → ℝ) (l k : κ) :
    freeEnergyCompHessian Real.exp n h y l k =
      Real.exp (n * Real.log (∑ a, Real.exp (y a + h a))) *
        (n ^ 2 * (Real.exp (y l + h l) / ∑ a, Real.exp (y a + h a)) *
            (Real.exp (y k + h k) / ∑ a, Real.exp (y a + h a)) +
          n * (Real.exp (y l + h l) / (∑ a, Real.exp (y a + h a)) *
            ((if l = k then 1 else 0) - Real.exp (y k + h k) / ∑ a, Real.exp (y a + h a)))) := by
  simp only [freeEnergyCompHessian, Real.deriv_exp]
  ring

/-- **Derivative of the real moment `𝔼 exp (n log Z_s)` along the trigonometric path**
`Z_s = ∑ₐ exp (cos s X a + sin s Y a + h a)`, for every real `n`: at `t` it is
`sin t cos t ∑_{l,k} (𝔼 Y_l Y_k - 𝔼 X_l X_k) 𝔼 [Z_t^n (n² wₗ wₖ + n wₗ (1[l = k] - wₖ))]`
with the Gibbs weights `w` of `Z_t`. -/
theorem hasDerivAt_integral_exp_mul_log_sum_exp_trig_hessian
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (hX : ∀ l, ∫ ω, X l ω ∂P = 0) (hY : ∀ l, ∫ ω, Y l ω ∂P = 0)
    (h0 : ∀ l k, ∫ ω, X l ω * Y k ω ∂P = 0) (n : ℝ) (h : κ → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ∫ ω, Real.exp (n * Real.log (∑ a, Real.exp (Real.cos s * X a ω +
        Real.sin s * Y a ω + h a))) ∂P)
      (Real.sin t * Real.cos t * ∑ l, ∑ k, ((∫ ω, Y l ω * Y k ω ∂P) - ∫ ω, X l ω * X k ω ∂P) *
        ∫ ω, freeEnergyCompHessian Real.exp n h
          (fun m => Real.cos t * X m ω + Real.sin t * Y m ω) l k ∂P) t := by
  have hb (x : ℝ) : |Real.exp x| ≤ 1 * Real.exp (1 * |x|) := by
    rw [one_mul, one_mul, abs_of_pos (Real.exp_pos x)]
    exact Real.exp_le_exp.2 (le_abs_self x)
  exact hasDerivAt_integral_comp_log_sum_exp_trig hXY hX hY h0 Real.contDiff_exp
    (C₀ := 1) (c₀ := 1) (C₁ := 1) (c₁ := 1) (C₂ := 1) (c₂ := 1) hb
    (fun x => by simpa only [Real.deriv_exp] using hb x)
    (fun x => by simpa only [Real.deriv_exp] using hb x) n h t

end

end SpinGlasses
