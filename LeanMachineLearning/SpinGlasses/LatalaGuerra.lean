/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.Shift
public import LeanMachineLearning.SpinGlasses.SKFixedPoint

/-!
# The Latała–Guerra lemma (Talagrand, Appendix A.14, Proposition A.14.1)

Let `φ` be a bounded increasing odd function with `φ'' < 0` on `(0, ∞)`.  Then for every `h` the
function `Ψ(x) = 𝔼 φ(s √x z + h)² / x` is strictly decreasing on `(0, ∞)` and tends to `0` at
infinity (`s = 1` in the book; `s = 0` needs `h ≠ 0`).

Regularity at zero is not automatic from the book's hypotheses (the odd extension of
`√y / (1 + √y)` is bounded, increasing and concave on `(0, ∞)` but has no derivative at `0`), so
we assume `φ` is globally `C¹` and `φ'` has a derivative `φ₂ y < 0` at every `y > 0`.  The proof
follows the book: `x² Ψ'(x) = 𝔼 φ(Y)(Y φ'(Y) - φ(Y)) - h 𝔼 φ(Y) φ'(Y)` with `Y = √x z + h`; the
first term is negative because `y φ'(y) - φ(y)` has the sign opposite to `y`, and the second is
nonpositive by the symmetrization `integral_odd_comp_affine_nonneg`.  Differentiation under the
integral uses `0 ≤ φ' ≤ φ'(0)`, derived from concavity.

## Main declarations

* `SpinGlasses.integral_odd_comp_affine_nonneg`: the Gaussian symmetrization with `sinh`.
* `SpinGlasses.integral_mul_deriv_mul_id_lt`: the key inequality
  `w 𝔼[φ(Y) φ'(Y) z] < 𝔼 φ(Y)²` for `Y = w z + h`, `w ≠ 0`.
* `SpinGlasses.strictAntiOn_integral_sq_comp_sqrt_div`: strict decrease of `Ψ`.
* `SpinGlasses.tendsto_integral_sq_comp_sqrt_div_atTop`: `Ψ(x) → 0`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Appendix A.14.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter

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

section Deterministic

variable {φ φ₂ : ℝ → ℝ}

/-- The derivative of an odd function is even. -/
theorem deriv_neg_eq_of_odd (hodd : ∀ y, φ (-y) = -φ y) (y : ℝ) :
    deriv φ (-y) = deriv φ y := by
  have h : deriv φ y = deriv (fun x => -φ (-x)) y := by
    congr 1; funext x; rw [hodd, neg_neg]
  rw [h]
  change deriv φ (-y) = deriv (-(fun x => φ (-x))) y
  rw [deriv.neg, deriv_comp_neg, neg_neg]

/-- Concavity on `[0, ∞)`: `φ'` is strictly decreasing there when `φ'' < 0` on `(0, ∞)`. -/
theorem strictAntiOn_deriv_Ici (hc1 : ContDiff ℝ 1 φ)
    (hφ₂ : ∀ y, 0 < y → HasDerivAt (deriv φ) (φ₂ y) y) (hneg : ∀ y, 0 < y → φ₂ y < 0) :
    StrictAntiOn (deriv φ) (Ici 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici 0) (hc1.continuous_deriv le_rfl).continuousOn
    fun y hy => ?_
  rw [interior_Ici] at hy
  rw [(hφ₂ y hy).deriv]
  exact hneg y hy

/-- `φ' > 0` on `[0, ∞)` for an increasing `φ` with `φ'' < 0` on `(0, ∞)`. -/
theorem deriv_pos_of_nonneg (hc1 : ContDiff ℝ 1 φ) (hm : Monotone φ)
    (hφ₂ : ∀ y, 0 < y → HasDerivAt (deriv φ) (φ₂ y) y) (hneg : ∀ y, 0 < y → φ₂ y < 0) {y : ℝ}
    (hy : 0 ≤ y) : 0 < deriv φ y := by
  have h1 := strictAntiOn_deriv_Ici hc1 hφ₂ hneg (show y ∈ Ici (0 : ℝ) from hy)
    (show y + 1 ∈ Ici (0 : ℝ) from by simp only [mem_Ici]; linarith) (by linarith)
  have h2 : 0 ≤ deriv φ (y + 1) :=
    ((hc1.differentiable one_ne_zero) (y + 1)).hasDerivAt.nonneg_of_monotone hm
  linarith

/-- For an increasing odd `φ`, `0 ≤ φ' ≤ φ'(0)` everywhere. -/
theorem deriv_mem_Icc (hc1 : ContDiff ℝ 1 φ) (hodd : ∀ y, φ (-y) = -φ y) (hm : Monotone φ)
    (hφ₂ : ∀ y, 0 < y → HasDerivAt (deriv φ) (φ₂ y) y) (hneg : ∀ y, 0 < y → φ₂ y < 0)
    (y : ℝ) : deriv φ y ∈ Icc 0 (deriv φ 0) := by
  refine ⟨((hc1.differentiable one_ne_zero) y).hasDerivAt.nonneg_of_monotone hm, ?_⟩
  rcases le_total 0 y with hy | hy
  · exact (strictAntiOn_deriv_Ici hc1 hφ₂ hneg).antitoneOn self_mem_Ici
      (show y ∈ Ici (0 : ℝ) from hy) hy
  · rw [← deriv_neg_eq_of_odd hodd y]
    exact (strictAntiOn_deriv_Ici hc1 hφ₂ hneg).antitoneOn self_mem_Ici
      (show -y ∈ Ici (0 : ℝ) from by simp only [mem_Ici]; linarith) (by linarith)

/-- `φ(0) = 0` for an odd function. -/
theorem apply_zero_of_odd (hodd : ∀ y, φ (-y) = -φ y) : φ 0 = 0 := by
  have := hodd 0
  rw [neg_zero] at this
  linarith

/-- `φ > 0` on `(0, ∞)` for an increasing odd `φ` with `φ'' < 0` on `(0, ∞)`. -/
theorem apply_pos_of_pos (hc1 : ContDiff ℝ 1 φ) (hodd : ∀ y, φ (-y) = -φ y) (hm : Monotone φ)
    (hφ₂ : ∀ y, 0 < y → HasDerivAt (deriv φ) (φ₂ y) y) (hneg : ∀ y, 0 < y → φ₂ y < 0) {y : ℝ}
    (hy : 0 < y) : 0 < φ y := by
  have h := strictMonoOn_of_deriv_pos (convex_Ici 0) hc1.continuous.continuousOn
    (f := φ) fun x hx => by
      rw [interior_Ici] at hx
      exact deriv_pos_of_nonneg hc1 hm hφ₂ hneg (le_of_lt hx)
  have := h self_mem_Ici (show y ∈ Ici (0 : ℝ) from hy.le) hy
  rwa [apply_zero_of_odd hodd] at this

/-- `φ ≠ 0` away from zero. -/
theorem apply_ne_zero (hc1 : ContDiff ℝ 1 φ) (hodd : ∀ y, φ (-y) = -φ y) (hm : Monotone φ)
    (hφ₂ : ∀ y, 0 < y → HasDerivAt (deriv φ) (φ₂ y) y) (hneg : ∀ y, 0 < y → φ₂ y < 0) {y : ℝ}
    (hy : y ≠ 0) : φ y ≠ 0 := by
  rcases lt_or_gt_of_ne hy with h | h
  · have := apply_pos_of_pos hc1 hodd hm hφ₂ hneg (neg_pos.2 h)
    rw [hodd] at this
    linarith
  · exact (apply_pos_of_pos hc1 hodd hm hφ₂ hneg h).ne'

/-- `y φ'(y) - φ(y) < 0` for `y > 0`: `ψ(y) = y φ'(y) - φ(y)` has `ψ(0) = 0`, `ψ' = y φ''`. -/
theorem mul_deriv_sub_self_neg (hc1 : ContDiff ℝ 1 φ) (hodd : ∀ y, φ (-y) = -φ y)
    (hφ₂ : ∀ y, 0 < y → HasDerivAt (deriv φ) (φ₂ y) y) (hneg : ∀ y, 0 < y → φ₂ y < 0) {y : ℝ}
    (hy : 0 < y) : y * deriv φ y - φ y < 0 := by
  have hd : ∀ x, 0 < x → HasDerivAt (fun t => t * deriv φ t - φ t) (x * φ₂ x) x := fun x hx => by
    have := (((hasDerivAt_id x).mul (hφ₂ x hx)).sub
      (((hc1.differentiable one_ne_zero) x).hasDerivAt))
    refine this.congr_deriv ?_
    simp only [id]
    ring
  have hcont : ContinuousOn (fun t => t * deriv φ t - φ t) (Ici 0) :=
    ((continuous_id.mul (hc1.continuous_deriv le_rfl)).sub hc1.continuous).continuousOn
  have h := strictAntiOn_of_deriv_neg (convex_Ici 0) hcont fun x hx => by
    rw [interior_Ici] at hx
    rw [(hd x hx).deriv]
    exact mul_neg_of_pos_of_neg hx (hneg x hx)
  have := h self_mem_Ici (show y ∈ Ici (0 : ℝ) from hy.le) hy
  simpa [apply_zero_of_odd hodd] using this

/-- **The sign computation of Proposition A.14.1:** `φ(y) (y φ'(y) - φ(y)) < 0` for `y ≠ 0`. -/
theorem mul_mul_deriv_sub_self_neg (hc1 : ContDiff ℝ 1 φ) (hodd : ∀ y, φ (-y) = -φ y)
    (hm : Monotone φ) (hφ₂ : ∀ y, 0 < y → HasDerivAt (deriv φ) (φ₂ y) y)
    (hneg : ∀ y, 0 < y → φ₂ y < 0) {y : ℝ} (hy : y ≠ 0) :
    φ y * (y * deriv φ y - φ y) < 0 := by
  rcases lt_or_gt_of_ne hy with h | h
  · have h1 := apply_pos_of_pos hc1 hodd hm hφ₂ hneg (neg_pos.2 h)
    have h2 := mul_deriv_sub_self_neg hc1 hodd hφ₂ hneg (neg_pos.2 h)
    rw [hodd] at h1
    rw [hodd, deriv_neg_eq_of_odd hodd] at h2
    nlinarith only [h1, h2]
  · exact mul_neg_of_pos_of_neg (apply_pos_of_pos hc1 hodd hm hφ₂ hneg h)
      (mul_deriv_sub_self_neg hc1 hodd hφ₂ hneg h)

end Deterministic

section Gaussian

variable {φ φ₂ : ℝ → ℝ} {B : ℝ}

/-- `φ φ'` is continuous, bounded by `B φ'(0)`, odd and nonnegative on `[0, ∞)`: the hypotheses of
the symmetrization `integral_odd_comp_affine_nonneg`. -/
theorem integral_mul_deriv_nonneg_aux (hc1 : ContDiff ℝ 1 φ) (hodd : ∀ y, φ (-y) = -φ y)
    (hm : Monotone φ) (hB : ∀ y, |φ y| ≤ B)
    (hφ₂ : ∀ y, 0 < y → HasDerivAt (deriv φ) (φ₂ y) y) (hneg : ∀ y, 0 < y → φ₂ y < 0)
    {w : ℝ} (hw : w ≠ 0) (h : ℝ) :
    0 ≤ h * ∫ z, φ (w * z + h) * deriv φ (w * z + h) ∂(gaussianReal 0 1) := by
  refine integral_odd_comp_affine_nonneg (g := fun y => φ y * deriv φ y)
    (hc1.continuous.mul (hc1.continuous_deriv le_rfl)) (B := B * deriv φ 0) (fun y => ?_)
    (fun y => ?_) (fun y hy => ?_) hw h
  · have h1 := deriv_mem_Icc hc1 hodd hm hφ₂ hneg y
    rw [abs_mul, abs_of_nonneg h1.1]
    exact mul_le_mul (hB y) h1.2 h1.1 ((abs_nonneg _).trans (hB y))
  · simp only [hodd, deriv_neg_eq_of_odd hodd]; ring
  · have h0 : 0 ≤ φ y := by
      have := hm hy
      rwa [apply_zero_of_odd hodd] at this
    exact mul_nonneg h0 (deriv_mem_Icc hc1 hodd hm hφ₂ hneg y).1

/-- **The key inequality of Proposition A.14.1:** for `w ≠ 0` and `Y = w z + h`,
`w 𝔼[φ(Y) φ'(Y) z] < 𝔼 φ(Y)²`.  (This is `x² Ψ'(x) < 0` for `Ψ(x) = 𝔼 φ(√x z + h)²/x`.) -/
theorem integral_mul_deriv_mul_id_lt (hc1 : ContDiff ℝ 1 φ) (hodd : ∀ y, φ (-y) = -φ y)
    (hm : Monotone φ) (hB : ∀ y, |φ y| ≤ B)
    (hφ₂ : ∀ y, 0 < y → HasDerivAt (deriv φ) (φ₂ y) y) (hneg : ∀ y, 0 < y → φ₂ y < 0)
    {w : ℝ} (hw : w ≠ 0) (h : ℝ) :
    w * ∫ z, φ (w * z + h) * deriv φ (w * z + h) * z ∂(gaussianReal 0 1) <
      ∫ z, φ (w * z + h) ^ 2 ∂(gaussianReal 0 1) := by
  set D : ℝ := deriv φ 0 with hD
  set f₁ : ℝ → ℝ := fun y => φ y * (y * deriv φ y - φ y) with hf₁
  set g : ℝ → ℝ := fun y => φ y * deriv φ y with hg
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hD0 : 0 ≤ D := (deriv_mem_Icc hc1 hodd hm hφ₂ hneg 0).1
  have hφc : Continuous φ := hc1.continuous
  have hφ'c : Continuous (deriv φ) := hc1.continuous_deriv le_rfl
  have hYc : Continuous fun z : ℝ => w * z + h := by fun_prop
  have hf₁c : Continuous f₁ := by simp only [hf₁]; fun_prop
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hgb : ∀ y, |g y| ≤ B * D := fun y => by
    have h1 := deriv_mem_Icc hc1 hodd hm hφ₂ hneg y
    simp only [hg]
    rw [abs_mul, abs_of_nonneg h1.1]
    exact mul_le_mul (hB y) h1.2 h1.1 hB0
  have hf₁b : ∀ y, |f₁ y| ≤ B * (D * |y| + B) := fun y => by
    have h1 := deriv_mem_Icc hc1 hodd hm hφ₂ hneg y
    simp only [hf₁]
    rw [abs_mul]
    refine mul_le_mul (hB y) ((abs_sub _ _).trans ?_) (abs_nonneg _) hB0
    rw [abs_mul, abs_of_nonneg h1.1, mul_comm |y|]
    exact add_le_add (mul_le_mul_of_nonneg_right h1.2 (abs_nonneg _)) (hB y)
  have hlin : Integrable (fun z : ℝ => B * D * |w| * |z| + B * (D * |h| + B)) (gaussianReal 0 1) :=
    (integrable_abs_id_gaussianReal.const_mul (B * D * |w|)).add (integrable_const _)
  have hIf : Integrable (fun z : ℝ => f₁ (w * z + h)) (gaussianReal 0 1) := by
    refine hlin.mono' (hf₁c.comp hYc).aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]
    refine (hf₁b _).trans ?_
    have : |w * z + h| ≤ |w| * |z| + |h| := by
      rw [← abs_mul]; exact abs_add_le _ _
    nlinarith only [this, mul_nonneg hB0 hD0, hB0, hD0]
  have hIg : Integrable (fun z : ℝ => g (w * z + h)) (gaussianReal 0 1) :=
    (integrable_const (B * D)).mono' (hgc.comp hYc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hgb _)
  have hIsq : Integrable (fun z : ℝ => φ (w * z + h) ^ 2) (gaussianReal 0 1) :=
    (integrable_const (B ^ 2)).mono' ((hφc.comp hYc).pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2)
  have hIa : Integrable (fun z : ℝ => g (w * z + h) * z) (gaussianReal 0 1) := by
    refine (integrable_abs_id_gaussianReal.const_mul (B * D)).mono'
      ((hgc.comp hYc).mul continuous_id).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hgb _) (abs_nonneg _)
  -- the integral of `f₁ ∘ Y` is negative
  have hneg' : ∫ z : ℝ, f₁ (w * z + h) ∂(gaussianReal 0 1) < 0 := by
    have hpos : 0 < ∫ z : ℝ, -f₁ (w * z + h) ∂(gaussianReal 0 1) := by
      refine integral_pos_of_integrable_nonneg_nonzero (x := if h = 0 then 1 else 0)
        (hf₁c.comp hYc).neg hIf.neg (fun z => ?_) ?_
      · by_cases hz : w * z + h = 0
        · simp only [hf₁, hz, Pi.zero_apply]
          nlinarith only [mul_self_nonneg (φ 0)]
        · exact neg_nonneg.2 (mul_mul_deriv_sub_self_neg hc1 hodd hm hφ₂ hneg hz).le
      · have hx : w * (if h = 0 then (1 : ℝ) else 0) + h ≠ 0 := by
          split_ifs with hh
          · simpa [hh] using hw
          · simpa using hh
        exact neg_ne_zero.2 (mul_mul_deriv_sub_self_neg hc1 hodd hm hφ₂ hneg hx).ne
    rw [integral_neg] at hpos
    linarith
  have hsym := integral_mul_deriv_nonneg_aux hc1 hodd hm hB hφ₂ hneg hw h
  have hpt : ∀ z : ℝ, w * (g (w * z + h) * z) - φ (w * z + h) ^ 2 =
      f₁ (w * z + h) - h * g (w * z + h) := fun z => by
    simp only [hf₁, hg]; ring
  have hmain : w * ∫ z : ℝ, g (w * z + h) * z ∂(gaussianReal 0 1) -
      ∫ z : ℝ, φ (w * z + h) ^ 2 ∂(gaussianReal 0 1) =
      ∫ z : ℝ, f₁ (w * z + h) ∂(gaussianReal 0 1) -
        h * ∫ z : ℝ, g (w * z + h) ∂(gaussianReal 0 1) := by
    rw [← integral_const_mul, ← integral_sub (hIa.const_mul w) hIsq, ← integral_const_mul,
      ← integral_sub hIf (hIg.const_mul h)]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  change w * ∫ z : ℝ, g (w * z + h) * z ∂(gaussianReal 0 1) < _
  change 0 ≤ h * ∫ z, g (w * z + h) ∂(gaussianReal 0 1) at hsym
  linarith

/-- **Parameter derivative of the Gaussian mean of `φ²`** (differentiation under the integral,
dominated by `2 B φ'(0) |z|`): `(d/dw) 𝔼 φ(w z + h)² = 𝔼[2 φ(Y) φ'(Y) z]`. -/
theorem hasDerivAt_integral_sq_comp_affine (hc1 : ContDiff ℝ 1 φ) (hodd : ∀ y, φ (-y) = -φ y)
    (hm : Monotone φ) (hB : ∀ y, |φ y| ≤ B)
    (hφ₂ : ∀ y, 0 < y → HasDerivAt (deriv φ) (φ₂ y) y) (hneg : ∀ y, 0 < y → φ₂ y < 0)
    (h w : ℝ) :
    HasDerivAt (fun v => ∫ z, φ (v * z + h) ^ 2 ∂(gaussianReal 0 1))
      (∫ z, 2 * (φ (w * z + h) * deriv φ (w * z + h)) * z ∂(gaussianReal 0 1)) w := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hφc : Continuous φ := hc1.continuous
  have hφ'c : Continuous (deriv φ) := hc1.continuous_deriv le_rfl
  have hsq : ∀ v : ℝ, Continuous fun z : ℝ => φ (v * z + h) ^ 2 := fun v => by fun_prop
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := univ)
    (F := fun v z => φ (v * z + h) ^ 2)
    (F' := fun v z => 2 * (φ (v * z + h) * deriv φ (v * z + h)) * z)
    univ_mem (Filter.Eventually.of_forall fun v => (hsq v).aestronglyMeasurable)
    ((integrable_const (B ^ 2)).mono' (hsq w).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2))
    (by fun_prop : Continuous fun z : ℝ =>
      2 * (φ (w * z + h) * deriv φ (w * z + h)) * z).aestronglyMeasurable
    (bound := fun z => 2 * (B * deriv φ 0) * |z|) (ae_of_all _ fun z v _ => ?_)
    (integrable_abs_id_gaussianReal.const_mul (2 * (B * deriv φ 0)))
    (ae_of_all _ fun z v _ => ?_)).2
  · have h1 := deriv_mem_Icc hc1 hodd hm hφ₂ hneg (v * z + h)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg h1.1,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := mul_le_mul (hB (v * z + h)) h1.2 h1.1 hB0
    nlinarith only [this, abs_nonneg z]
  · have h_lin : HasDerivAt (fun v => v * z + h) z v := by
      simpa using ((hasDerivAt_id' v).mul_const z).add_const h
    have h1 : HasDerivAt (fun v => φ (v * z + h)) (deriv φ (v * z + h) * z) v :=
      ((hc1.differentiable one_ne_zero) (v * z + h)).hasDerivAt.comp v h_lin
    refine (h1.pow 2).congr_deriv ?_
    push_cast
    ring

/-- **Proposition A.14.1 (Latała–Guerra lemma).** Let `φ` be globally `C¹`, bounded, increasing
and odd, with `φ'' < 0` on `(0, ∞)`.  If `s ≠ 0` or `h ≠ 0`, then
`x ↦ 𝔼 φ(s √x z + h)² / x` is strictly decreasing on `(0, ∞)`. -/
theorem strictAntiOn_integral_sq_comp_sqrt_div (hc1 : ContDiff ℝ 1 φ)
    (hodd : ∀ y, φ (-y) = -φ y) (hm : Monotone φ) (hB : ∀ y, |φ y| ≤ B)
    (hφ₂ : ∀ y, 0 < y → HasDerivAt (deriv φ) (φ₂ y) y) (hneg : ∀ y, 0 < y → φ₂ y < 0)
    (s h : ℝ) (hsh : s ≠ 0 ∨ h ≠ 0) :
    StrictAntiOn (fun x : ℝ => (∫ z, φ (s * Real.sqrt x * z + h) ^ 2 ∂(gaussianReal 0 1)) / x)
      (Ioi 0) := by
  have hkey : ∀ x : ℝ, 0 < x →
      x * ((∫ z, 2 * (φ (s * Real.sqrt x * z + h) * deriv φ (s * Real.sqrt x * z + h)) * z
        ∂(gaussianReal 0 1)) * (s * (1 / (2 * Real.sqrt x)))) <
      ∫ z, φ (s * Real.sqrt x * z + h) ^ 2 ∂(gaussianReal 0 1) := fun x hx => by
    have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
    have e : ∫ z, 2 * (φ (s * Real.sqrt x * z + h) * deriv φ (s * Real.sqrt x * z + h)) * z
        ∂(gaussianReal 0 1) =
        2 * ∫ z, φ (s * Real.sqrt x * z + h) * deriv φ (s * Real.sqrt x * z + h) * z
          ∂(gaussianReal 0 1) := by
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun z => by ring)
    rw [e]
    by_cases hs : s = 0
    · subst hs
      have hh : h ≠ 0 := hsh.resolve_left (by simp)
      have hpos : 0 < ∫ z, φ (0 * Real.sqrt x * z + h) ^ 2 ∂(gaussianReal 0 1) := by
        simp only [zero_mul, zero_add, integral_const, smul_eq_mul]
        simpa using pow_pos (abs_pos.2 (apply_ne_zero hc1 hodd hm hφ₂ hneg hh)) 2
      simpa using hpos
    · have hw : s * Real.sqrt x ≠ 0 := mul_ne_zero hs hsx.ne'
      have hlt := integral_mul_deriv_mul_id_lt hc1 hodd hm hB hφ₂ hneg hw h
      generalize (∫ z, φ (s * Real.sqrt x * z + h) * deriv φ (s * Real.sqrt x * z + h) * z
        ∂(gaussianReal 0 1)) = J at hlt ⊢
      have e2 : x * (2 * J * (s * (1 / (2 * Real.sqrt x)))) = s * Real.sqrt x * J := by
        have hne : Real.sqrt x ≠ 0 := hsx.ne'
        calc x * (2 * J * (s * (1 / (2 * Real.sqrt x))))
            = (Real.sqrt x * Real.sqrt x) * (2 * J * (s * (1 / (2 * Real.sqrt x)))) := by
              rw [hxx]
          _ = s * Real.sqrt x * J := by field_simp
      rw [e2]
      exact hlt
  have hd : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt (fun y : ℝ =>
      (∫ z, φ (s * Real.sqrt y * z + h) ^ 2 ∂(gaussianReal 0 1)) / y)
      ((((∫ z, 2 * (φ (s * Real.sqrt y * z + h) * deriv φ (s * Real.sqrt y * z + h)) * z
        ∂(gaussianReal 0 1)) * (s * (1 / (2 * Real.sqrt y)))) * y -
        (∫ z, φ (s * Real.sqrt y * z + h) ^ 2 ∂(gaussianReal 0 1)) * 1) / y ^ 2) y := by
    intro y hy
    have h2 : HasDerivAt (fun y : ℝ => s * Real.sqrt y) (s * (1 / (2 * Real.sqrt y))) y :=
      (Real.hasDerivAt_sqrt (ne_of_gt hy)).const_mul s
    have h3 := (hasDerivAt_integral_sq_comp_affine hc1 hodd hm hB hφ₂ hneg h
      (s * Real.sqrt y)).comp y h2
    exact h3.div (hasDerivAt_id y) (ne_of_gt hy)
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun y hy => (hd y hy).continuousAt.continuousWithinAt) fun y hy => ?_
  rw [interior_Ioi] at hy
  rw [(hd y hy).deriv]
  have hy2 : 0 < y ^ 2 := by have : (0 : ℝ) < y := hy; positivity
  apply div_neg_of_neg_of_pos _ hy2
  nlinarith only [hkey y hy]

/-- **Proposition A.14.1, vanishing at infinity:** for bounded `φ`,
`𝔼 φ(s √x z + h)² / x → 0` as `x → ∞`. -/
theorem tendsto_integral_sq_comp_sqrt_div_atTop (hB : ∀ y, |φ y| ≤ B) (s h : ℝ) :
    Tendsto (fun x : ℝ => (∫ z, φ (s * Real.sqrt x * z + h) ^ 2 ∂(gaussianReal 0 1)) / x)
      atTop (nhds 0) := by
  have hup : Tendsto (fun x : ℝ => B ^ 2 / x) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact div_nonneg (integral_nonneg fun z => sq_nonneg _) hx.le
  · filter_upwards [eventually_gt_atTop 0] with x hx
    refine div_le_div_of_nonneg_right ?_ hx.le
    have := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1)
      (f := fun z => φ (s * Real.sqrt x * z + h) ^ 2) (C := B ^ 2)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2)
    simpa using (le_abs_self _).trans this

end Gaussian

end SpinGlasses
