/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.Shift
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

The proof of `integral_tanh_core_lt` splits `w z = Y - h` into
`𝔼 [tanh Y (Y tanh' Y - tanh Y)] < 0` (`tanh_mul_sub_neg`) and `h 𝔼 [tanh Y tanh' Y] ≥ 0`
(`integral_odd_comp_affine_nonneg`, the symmetrization with `sinh` of the book, via the Gaussian
shift `integral_gaussianReal_add_const_eq`).

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Lemma 1.9.3 and
  Proposition A.14.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

/-- `c · sinh (c x)` has the sign of `x`. -/
theorem mul_sinh_mul_nonneg {c x : ℝ} (hx : 0 ≤ x) : 0 ≤ c * Real.sinh (c * x) := by
  rcases le_total 0 c with hc | hc
  · exact mul_nonneg hc (Real.sinh_nonneg_iff.2 (mul_nonneg hc hx))
  · exact mul_nonneg_of_nonpos_of_nonpos hc
      (Real.sinh_nonpos_iff.2 (mul_nonpos_of_nonpos_of_nonneg hc hx))

/-- **The symmetrization of Proposition A.14.1:** for a bounded continuous odd `g` with
`g ≥ 0` on `[0, ∞)`, `w ≠ 0` and every `h`, `h 𝔼 g(w z + h) ≥ 0`. -/
theorem integral_odd_comp_affine_nonneg {g : ℝ → ℝ} (hgc : Continuous g) {B : ℝ}
    (hB : ∀ y, |g y| ≤ B) (hodd : ∀ y, g (-y) = -g y) (hpos : ∀ y, 0 ≤ y → 0 ≤ g y)
    {w : ℝ} (hw : w ≠ 0) (h : ℝ) :
    0 ≤ h * ∫ z, g (w * z + h) ∂(gaussianReal 0 1) := by
  set a : ℝ := h / w with ha
  set G : ℝ → ℝ := fun u => g (w * u) with hG
  have e1 : ∀ z, g (w * z + h) = G (z + a) := fun z => by
    simp only [hG, ha]; congr 1; field_simp
  have hint : ∀ b : ℝ, Integrable (fun u => G u * Real.exp (b * u - b ^ 2 / 2))
      (gaussianReal 0 1) := fun b => by
    refine ((integrable_exp_mul_gaussianReal (μ := (0 : ℝ)) (v := 1) b).const_mul
      (B * Real.exp (-(b ^ 2 / 2)))).mono' ?_ ?_
    · exact ((hgc.comp (continuous_const.mul continuous_id)).mul
        (by fun_prop)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun u => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      have : Real.exp (b * u - b ^ 2 / 2) = Real.exp (-(b ^ 2 / 2)) * Real.exp (b * u) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]
      calc |G u| * (Real.exp (-(b ^ 2 / 2)) * Real.exp (b * u))
          ≤ B * (Real.exp (-(b ^ 2 / 2)) * Real.exp (b * u)) :=
            mul_le_mul_of_nonneg_right (hB _) (by positivity)
        _ = _ := by ring
  simp only [e1]
  rw [integral_gaussianReal_add_const_eq G a]
  set H : ℝ → ℝ := fun u => G u * Real.exp (a * u - a ^ 2 / 2) with hH
  have hneg : ∫ u, H (-u) ∂(gaussianReal 0 1) = ∫ u, H u ∂(gaussianReal 0 1) := by
    have := (Homeomorph.neg ℝ).measurableEmbedding.integral_map (μ := gaussianReal 0 1) H
    rw [show (Homeomorph.neg ℝ : ℝ → ℝ) = fun x => -x from rfl, gaussianReal_map_neg,
      neg_zero] at this
    exact this.symm
  have hHi : Integrable H (gaussianReal 0 1) := hint a
  have hHi' : Integrable (fun u => H (-u)) (gaussianReal 0 1) := by
    refine (hint (-a)).neg.congr (Filter.Eventually.of_forall fun u => ?_)
    simp only [hH, hG, mul_neg, hodd, Pi.neg_apply]
    ring_nf
  have key : ∫ u, H u ∂(gaussianReal 0 1) =
      ∫ u, G u * Real.sinh (a * u) * Real.exp (-(a ^ 2 / 2)) ∂(gaussianReal 0 1) := by
    have h2 : ∫ u, H u ∂(gaussianReal 0 1) =
        ∫ u, (H u + H (-u)) / 2 ∂(gaussianReal 0 1) := by
      rw [integral_div, integral_add hHi hHi', hneg]; ring
    rw [h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hH, hG, mul_neg, hodd, Real.sinh_eq]
    have e1 : Real.exp (a * u - a ^ 2 / 2) = Real.exp (a * u) * Real.exp (-(a ^ 2 / 2)) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(a * u) - a ^ 2 / 2) = Real.exp (-(a * u)) * Real.exp (-(a ^ 2 / 2)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1, e2]
    ring
  rw [key, ← integral_const_mul]
  refine integral_nonneg fun u => ?_
  have hw2 : 0 < w ^ 2 := by positivity
  have hc : h = h / w ^ 2 * w ^ 2 := by field_simp
  have hau : a * u = h / w ^ 2 * (w * u) := by simp only [ha]; field_simp
  have hE := (Real.exp_pos (-(a ^ 2 / 2))).le
  have hmain : 0 ≤ G u * (h / w ^ 2 * Real.sinh (h / w ^ 2 * (w * u))) := by
    rcases le_total 0 (w * u) with hx | hx
    · exact mul_nonneg (hpos _ hx) (mul_sinh_mul_nonneg hx)
    · have h1 : G u ≤ 0 := by
        have := hpos (-(w * u)) (by linarith)
        simp only [hG]; rw [hodd] at this; linarith
      have h2 : h / w ^ 2 * Real.sinh (h / w ^ 2 * (w * u)) ≤ 0 := by
        have := mul_sinh_mul_nonneg (c := h / w ^ 2) (x := -(w * u)) (by linarith)
        rw [mul_neg, Real.sinh_neg] at this
        linarith
      exact mul_nonneg_of_nonpos_of_nonpos h1 h2
  rw [hau]
  calc 0 ≤ w ^ 2 * Real.exp (-(a ^ 2 / 2)) *
        (G u * (h / w ^ 2 * Real.sinh (h / w ^ 2 * (w * u)))) :=
        mul_nonneg (by positivity) hmain
    _ = h * (G u * Real.sinh (h / w ^ 2 * (w * u)) * Real.exp (-(a ^ 2 / 2))) := by
        field_simp

/-- `tanh y (y (1 - tanh² y) - tanh y) < 0` for `y ≠ 0`: the sign computation of
Proposition A.14.1 (`ψ(y) = y φ'(y) - φ(y)` has the sign opposite to `y`). -/
theorem tanh_mul_sub_neg {y : ℝ} (hy : y ≠ 0) :
    Real.tanh y * (y * (1 - Real.tanh y ^ 2) - Real.tanh y) < 0 := by
  have hpos : ∀ y : ℝ, 0 < y → Real.tanh y * (y * (1 - Real.tanh y ^ 2) - Real.tanh y) < 0 := by
    intro y hy
    have hc := Real.cosh_pos y
    have ht : 0 < Real.tanh y := by
      rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos (Real.sinh_pos_iff.2 hy) hc
    have hs : y < Real.sinh y * Real.cosh y := by
      have := Real.self_lt_sinh_iff.2 (by linarith : 0 < 2 * y)
      rw [Real.sinh_two_mul] at this
      linarith
    have e : y * (1 - Real.tanh y ^ 2) - Real.tanh y =
        (y - Real.sinh y * Real.cosh y) / Real.cosh y ^ 2 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      have := Real.cosh_sq y
      field_simp
      nlinarith [this]
    rw [e]
    exact mul_neg_of_pos_of_neg ht (div_neg_of_neg_of_pos (by linarith) (by positivity))
  rcases lt_or_gt_of_ne hy with hneg | hposy
  · have := hpos (-y) (by linarith)
    rw [Real.tanh_neg] at this
    nlinarith [this]
  · exact hpos y hposy

/-- The integrand of `tanh y (y (1 - tanh² y) - tanh y)` grows at most linearly. -/
theorem abs_tanh_mul_sub_le (y : ℝ) :
    |Real.tanh y * (y * (1 - Real.tanh y ^ 2) - Real.tanh y)| ≤ |y| + 1 := by
  have ht := Real.tanh_sq_lt_one y
  have ht1 : |Real.tanh y| ≤ 1 := by
    rw [← sq_le_one_iff_abs_le_one]; exact ht.le
  have h0 : 0 ≤ 1 - Real.tanh y ^ 2 := by linarith
  have e : Real.tanh y * (y * (1 - Real.tanh y ^ 2) - Real.tanh y) =
      Real.tanh y * y * (1 - Real.tanh y ^ 2) - Real.tanh y ^ 2 := by ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  have h1 : |Real.tanh y * y * (1 - Real.tanh y ^ 2)| ≤ |y| := by
    rw [abs_mul, abs_mul, abs_of_nonneg h0]
    calc |Real.tanh y| * |y| * (1 - Real.tanh y ^ 2) ≤ 1 * |y| * 1 := by
          gcongr
          · linarith [sq_nonneg (Real.tanh y)]
      _ = |y| := by ring
  have h2 : |Real.tanh y ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]; exact ht.le
  linarith

/-- **The key inequality of Proposition A.14.1 for `tanh`:**
`w · 𝔼[2 tanh Y (1 - tanh² Y) z] < 2 𝔼 tanh² Y` for `Y = w z + h`, `w ≠ 0`.
(This is `x² Ψ'(x) < 0` for `Ψ(x) = 𝔼 tanh²(√x z + h)/x`.) -/
theorem integral_tanh_core_lt {w : ℝ} (hw : w ≠ 0) (h : ℝ) :
    w * ∫ z : ℝ, 2 * Real.tanh (w * z + h) * (1 - Real.tanh (w * z + h) ^ 2) * z
        ∂(gaussianReal 0 1) < 2 * ∫ z : ℝ, Real.tanh (w * z + h) ^ 2 ∂(gaussianReal 0 1) := by
  set f₁ : ℝ → ℝ := fun y => Real.tanh y * (y * (1 - Real.tanh y ^ 2) - Real.tanh y) with hf₁
  set g : ℝ → ℝ := fun y => Real.tanh y * (1 - Real.tanh y ^ 2) with hg
  have hlin : Integrable (fun z : ℝ => |w| * |z| + (|h| + 1)) (gaussianReal 0 1) :=
    (integrable_abs_id_gaussianReal.const_mul |w|).add (integrable_const _)
  have hYc : Continuous fun z : ℝ => w * z + h := by fun_prop
  have hf₁c : Continuous f₁ := by
    simp only [hf₁]; have := Real.continuous_tanh; fun_prop
  have hgc : Continuous g := by simp only [hg]; have := Real.continuous_tanh; fun_prop
  have hgb : ∀ y, |g y| ≤ 1 := fun y => by
    have ht := Real.tanh_sq_lt_one y
    have ht1 : |Real.tanh y| ≤ 1 := by
      rw [← sq_le_one_iff_abs_le_one]; exact ht.le
    have h0 : 0 ≤ 1 - Real.tanh y ^ 2 := by linarith
    simp only [hg]
    rw [abs_mul, abs_of_nonneg h0]
    calc |Real.tanh y| * (1 - Real.tanh y ^ 2) ≤ 1 * 1 := by
          gcongr
          linarith [sq_nonneg (Real.tanh y)]
      _ = 1 := by ring
  have hodd : ∀ y, g (-y) = -g y := fun y => by simp [hg, Real.tanh_neg]
  have hgpos : ∀ y, 0 ≤ y → 0 ≤ g y := fun y hy => by
    simp only [hg]
    have h0 : 0 ≤ 1 - Real.tanh y ^ 2 := by linarith [Real.tanh_sq_lt_one y]
    have ht : 0 ≤ Real.tanh y := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.2 hy) (Real.cosh_pos y).le
    exact mul_nonneg ht h0
  have hIf : Integrable (fun z : ℝ => f₁ (w * z + h)) (gaussianReal 0 1) := by
    refine hlin.mono' (hf₁c.comp hYc).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_tanh_mul_sub_le _).trans ?_
    have : |w * z + h| ≤ |w| * |z| + |h| := by
      rw [← abs_mul]; exact abs_add_le _ _
    linarith
  have hIg : Integrable (fun z : ℝ => g (w * z + h)) (gaussianReal 0 1) :=
    (integrable_const (1 : ℝ)).mono' (hgc.comp hYc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hgb _)
  have hIt : Integrable (fun z : ℝ => Real.tanh (w * z + h) ^ 2) (gaussianReal 0 1) :=
    integrable_tanh_sq_affine w h
  have hIa : Integrable (fun z : ℝ => 2 * Real.tanh (w * z + h) *
      (1 - Real.tanh (w * z + h) ^ 2) * z) (gaussianReal 0 1) := by
    refine (integrable_abs_id_gaussianReal.const_mul 2).mono'
      (continuous_tanh_deriv_affine w h |>.mul continuous_id').aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (Real.abs_deriv_tanh_sq_le _) (abs_nonneg _)
  -- the integral of `f₁ ∘ Y` is negative
  have hneg : ∫ z : ℝ, f₁ (w * z + h) ∂(gaussianReal 0 1) < 0 := by
    have hpos : 0 < ∫ z : ℝ, -f₁ (w * z + h) ∂(gaussianReal 0 1) := by
      refine integral_pos_of_integrable_nonneg_nonzero (x := if h = 0 then 1 else 0)
        (hf₁c.comp hYc).neg hIf.neg (fun z => ?_) ?_
      · by_cases hz : w * z + h = 0
        · simp [hf₁, hz]
        · exact (neg_nonneg.2 (tanh_mul_sub_neg hz).le)
      · have hx : w * (if h = 0 then (1 : ℝ) else 0) + h ≠ 0 := by
          split_ifs with hh
          · simpa [hh] using hw
          · simpa using hh
        exact (neg_ne_zero.2 (tanh_mul_sub_neg hx).ne)
    rw [integral_neg] at hpos
    linarith
  -- the symmetrization term
  have hsym := integral_odd_comp_affine_nonneg hgc hgb hodd hgpos hw h
  have hpt : ∀ z : ℝ, w * (2 * Real.tanh (w * z + h) * (1 - Real.tanh (w * z + h) ^ 2) * z) -
      2 * Real.tanh (w * z + h) ^ 2 = 2 * f₁ (w * z + h) - 2 * (h * g (w * z + h)) := fun z => by
    simp only [hf₁, hg]; ring
  have hmain : w * ∫ z : ℝ, 2 * Real.tanh (w * z + h) * (1 - Real.tanh (w * z + h) ^ 2) * z
        ∂(gaussianReal 0 1) - 2 * ∫ z : ℝ, Real.tanh (w * z + h) ^ 2 ∂(gaussianReal 0 1) =
      2 * ∫ z : ℝ, f₁ (w * z + h) ∂(gaussianReal 0 1) -
        2 * (h * ∫ z : ℝ, g (w * z + h) ∂(gaussianReal 0 1)) := by
    have e1 : ∫ z : ℝ, (w * (2 * Real.tanh (w * z + h) * (1 - Real.tanh (w * z + h) ^ 2) * z) -
        2 * Real.tanh (w * z + h) ^ 2) ∂(gaussianReal 0 1) =
        w * ∫ z : ℝ, 2 * Real.tanh (w * z + h) * (1 - Real.tanh (w * z + h) ^ 2) * z
          ∂(gaussianReal 0 1) - 2 * ∫ z : ℝ, Real.tanh (w * z + h) ^ 2 ∂(gaussianReal 0 1) := by
      rw [integral_sub (hIa.const_mul w) (hIt.const_mul 2), integral_const_mul,
        integral_const_mul]
    have e2 : ∫ z : ℝ, (2 * f₁ (w * z + h) - 2 * (h * g (w * z + h))) ∂(gaussianReal 0 1) =
        2 * ∫ z : ℝ, f₁ (w * z + h) ∂(gaussianReal 0 1) -
          2 * (h * ∫ z : ℝ, g (w * z + h) ∂(gaussianReal 0 1)) := by
      rw [integral_sub (hIf.const_mul 2) ((hIg.const_mul h).const_mul 2), integral_const_mul,
        integral_const_mul, integral_const_mul]
    rw [← e1, ← e2]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
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
