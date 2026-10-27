/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.LatalaGuerra
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.Tanh
public import LeanMachineLearning.SpinGlasses.SKFixedPoint

/-!
# Lemma 1.9.3: the secondary denominator `1 - β²(1 - 4q + 3q̂)` is positive (Talagrand, Section 1.9)

For a fixed point `q > 0` of `q = 𝔼 tanh²(β √q z + h)` and `q̂ = 𝔼 tanh⁴(β √q z + h)`,
`β² (1 - 4q + 3q̂) < 1`.  We follow the book: with `Φ(x) = 𝔼 tanh²(β √x z + h)`,
`x Φ'(x) - Φ(x) = x² (Φ(x)/x)' < 0` (the proof of Proposition A.14.1 for `φ = tanh`, which gives
the strict inequality), and Gaussian integration by parts gives `Φ'(q) = β²(1 - 4q + 3q̂)`; here
the derivative in `x` is not taken: the inequality is proved directly in terms of `w = β √q` as
`w · 𝔼[2 tanh Y (1 - tanh² Y) z] < 2 𝔼 tanh² Y` (`integral_tanh_core_lt`) and Stein's lemma
(`integral_tanh_sq_deriv_mul_id_eq`) is applied to the left-hand side.

`integral_tanh_core_lt` is the case `φ = tanh` of the general Latała–Guerra argument
(`integral_mul_deriv_mul_id_lt` in `LatalaGuerra.lean`): `w z = Y - h` splits the integral into
`𝔼 [φ(Y)(Y φ'(Y) - φ(Y))] < 0` and `h 𝔼 [φ(Y) φ'(Y)] ≥ 0`, the latter by the Gaussian
symmetrization of the book.  Here we only verify that `tanh` satisfies the hypotheses.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Lemma 1.9.3 and
  Proposition A.14.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

/-- `tanh' = 1 - tanh²`. -/
theorem deriv_tanh_eq : deriv Real.tanh = fun y => 1 - Real.tanh y ^ 2 :=
  funext fun y => (Real.hasDerivAt_tanh y).deriv

/-- `tanh` is globally `C¹`. -/
theorem contDiff_one_tanh : ContDiff ℝ 1 Real.tanh :=
  contDiff_one_iff_deriv.2 ⟨fun y => (Real.hasDerivAt_tanh y).differentiableAt, by
    rw [deriv_tanh_eq]; have := Real.continuous_tanh; fun_prop⟩

/-- `tanh` is increasing. -/
theorem monotone_tanh : Monotone Real.tanh :=
  monotone_of_deriv_nonneg (fun y => (Real.hasDerivAt_tanh y).differentiableAt) fun y => by
    rw [deriv_tanh_eq]; linarith [Real.tanh_sq_lt_one y]

/-- `tanh'' y = -2 tanh y (1 - tanh² y)`. -/
theorem hasDerivAt_deriv_tanh (y : ℝ) :
    HasDerivAt (deriv Real.tanh) (-(2 * Real.tanh y * (1 - Real.tanh y ^ 2))) y := by
  rw [deriv_tanh_eq]
  have hsub := (hasDerivAt_const y (1 : ℝ)).sub (Real.hasDerivAt_tanh_sq y)
  rw [zero_sub] at hsub
  exact hsub

/-- `tanh'' < 0` on `(0, ∞)`. -/
theorem neg_two_mul_tanh_mul_lt_zero {y : ℝ} (hy : 0 < y) :
    -(2 * Real.tanh y * (1 - Real.tanh y ^ 2)) < 0 := by
  have ht : 0 < Real.tanh y := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.2 hy) (Real.cosh_pos y)
  have := Real.tanh_sq_lt_one y
  nlinarith only [ht, this]

/-- **The key inequality of Proposition A.14.1 for `tanh`:**
`w · 𝔼[2 tanh Y (1 - tanh² Y) z] < 2 𝔼 tanh² Y` for `Y = w z + h`, `w ≠ 0`.
(This is `x² Ψ'(x) < 0` for `Ψ(x) = 𝔼 tanh²(√x z + h)/x`; it is the case `φ = tanh` of
`integral_mul_deriv_mul_id_lt`.) -/
theorem integral_tanh_core_lt {w : ℝ} (hw : w ≠ 0) (h : ℝ) :
    w * ∫ z : ℝ, 2 * Real.tanh (w * z + h) * (1 - Real.tanh (w * z + h) ^ 2) * z
        ∂(gaussianReal 0 1) < 2 * ∫ z : ℝ, Real.tanh (w * z + h) ^ 2 ∂(gaussianReal 0 1) := by
  have key := integral_mul_deriv_mul_id_lt contDiff_one_tanh Real.tanh_neg monotone_tanh
    (fun y => (Real.abs_tanh_lt_one y).le) (fun y _ => hasDerivAt_deriv_tanh y)
    (fun y hy => neg_two_mul_tanh_mul_lt_zero hy) hw h
  rw [deriv_tanh_eq] at key
  have e : ∫ z : ℝ, 2 * Real.tanh (w * z + h) * (1 - Real.tanh (w * z + h) ^ 2) * z
      ∂(gaussianReal 0 1) = 2 * ∫ z : ℝ, Real.tanh (w * z + h) *
        (1 - Real.tanh (w * z + h) ^ 2) * z ∂(gaussianReal 0 1) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
  rw [e]
  linarith

/-- `𝔼 [f''(wz+h)] = 2 - 8 𝔼 tanh² + 6 𝔼 tanh⁴` for `f = tanh²`, i.e.
`f'' = 2 (1 - tanh²)(1 - 3 tanh²)`. -/
theorem integral_tanh_sq_second_deriv_eq {w h a b : ℝ}
    (ha : ∫ z : ℝ, Real.tanh (w * z + h) ^ 2 ∂(gaussianReal 0 1) = a)
    (hb : ∫ z : ℝ, Real.tanh (w * z + h) ^ 4 ∂(gaussianReal 0 1) = b) :
    ∫ z : ℝ, 2 * (1 - Real.tanh (w * z + h) ^ 2) * (1 - 3 * Real.tanh (w * z + h) ^ 2)
      ∂(gaussianReal 0 1) = 2 - 8 * a + 6 * b := by
  have h2 := integrable_tanh_sq_affine w h
  have h4 : Integrable (fun z : ℝ => Real.tanh (w * z + h) ^ 4) (gaussianReal 0 1) :=
    (integrable_const (1 : ℝ)).mono' (by have := Real.continuous_tanh; fun_prop)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_one₀ (abs_nonneg _) (by
          rw [← sq_le_one_iff_abs_le_one]; exact (Real.tanh_sq_lt_one _).le))
  have e : ∀ z : ℝ, 2 * (1 - Real.tanh (w * z + h) ^ 2) * (1 - 3 * Real.tanh (w * z + h) ^ 2) =
      2 - 8 * Real.tanh (w * z + h) ^ 2 + 6 * Real.tanh (w * z + h) ^ 4 := fun z => by ring
  simp_rw [e]
  have hi1 : Integrable (fun z : ℝ => 2 - 8 * Real.tanh (w * z + h) ^ 2) (gaussianReal 0 1) :=
    (integrable_const (2 : ℝ)).sub (h2.const_mul 8)
  rw [integral_add hi1 (h4.const_mul 6), integral_sub (integrable_const (2 : ℝ))
    (h2.const_mul 8), integral_const_mul, integral_const_mul, ha, hb]
  simp

/-- **Lemma 1.9.3 (Talagrand), the fixed-point form.**  If `q > 0` is a solution of
`q = 𝔼 tanh²(β √q z + h)` and `q̂ = 𝔼 tanh⁴(β √q z + h)`, then `β² (1 - 4 q + 3 q̂) < 1`.
(For `h = 0` the fixed point `q = 0` is excluded by `0 < q`; for `h ≠ 0` every solution is
positive.) -/
theorem sk_beta_sq_mul_one_sub_four_add_three_lt_one {β h q qhat : ℝ} (hq : 0 < q)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat) :
    β ^ 2 * (1 - 4 * q + 3 * qhat) < 1 := by
  by_cases hβ : β = 0
  · subst hβ; norm_num
  have hw : β * Real.sqrt q ≠ 0 := mul_ne_zero hβ (Real.sqrt_pos.2 hq).ne'
  have hcore := integral_tanh_core_lt hw h
  rw [integral_tanh_sq_deriv_mul_id_eq h (β * Real.sqrt q), hfix] at hcore
  have hint := integral_tanh_sq_second_deriv_eq hfix hqhat
  rw [hint] at hcore
  have hsq : (β * Real.sqrt q) ^ 2 = β ^ 2 * q := by
    rw [mul_pow, Real.sq_sqrt hq.le]
  have e : β * Real.sqrt q * (β * Real.sqrt q * (2 - 8 * q + 6 * qhat)) =
      2 * (β ^ 2 * q * (1 - 4 * q + 3 * qhat)) := by
    linear_combination (2 - 8 * q + 6 * qhat) * hsq
  have : β ^ 2 * q * (1 - 4 * q + 3 * qhat) < q := by
    rw [e] at hcore; linarith
  by_contra hcon
  push Not at hcon
  nlinarith [mul_le_mul_of_nonneg_left hcon hq.le]

end SpinGlasses
