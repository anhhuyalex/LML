/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapSecondMoments.SKSecondMoment
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.Tanh

/-!
# Lipschitz estimates for the Gaussian averages in Hanen's leading term

Step E5 of the proof of the even case of Theorem 1.11.1 (the book's "very simple matter").
The leading term of Proposition 1.11.11 for the reduced system differs from the one for the
full system by `O((N+2)^{-1/2})` in the bracket. The bracket is a Gaussian average of a bounded
Lipschitz function of `r z + h` with `r = β √q`; this module collects the Lipschitz bounds in `r`
and the comparison `|r - rm| ≲ (N+2)^{-1/2}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real
namespace SpinGlasses

/-- The first absolute moment of the standard Gaussian is at most one. -/
theorem integral_abs_gaussianReal_le_one : ∫ z : ℝ, |z| ∂gaussianReal 0 1 ≤ 1 := by
  have hm : MemLp id 2 (gaussianReal 0 1) := memLp_id_gaussianReal 2
  have hsq : Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 1) := hm.integrable_sq
  have habs : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) :=
    (hm.integrable (by norm_num)).abs
  have hvar : ∫ z : ℝ, z ^ 2 ∂gaussianReal 0 1 = 1 := by
    have h0 : ∫ z : ℝ, id z ∂gaussianReal 0 1 = 0 := integral_id_gaussianReal
    have := variance_of_integral_eq_zero (μ := gaussianReal 0 1) (X := id) aemeasurable_id h0
    rw [variance_id_gaussianReal] at this
    simpa using this.symm
  calc ∫ z : ℝ, |z| ∂gaussianReal 0 1 ≤ ∫ z : ℝ, (1 + z ^ 2) / 2 ∂gaussianReal 0 1 :=
        integral_mono habs ((integrable_const (1 : ℝ)).add hsq |>.div_const 2) fun z => by
          nlinarith [sq_abs z, sq_nonneg (|z| - 1)]
    _ = 1 := by
        rw [integral_div, integral_add (integrable_const _) hsq, hvar]
        simp

/-- **Integral form of a Lipschitz bound.** If `f` is bounded, continuous and `L`-Lipschitz, then
the Gaussian average of `f (r z + h)` is `L`-Lipschitz in `r`. -/
theorem abs_integral_gaussianReal_comp_sub_le (f : ℝ → ℝ) (L B : ℝ) (hL : 0 ≤ L)
    (hcont : Continuous f) (hf : ∀ u v, |f u - f v| ≤ L * |u - v|) (hB : ∀ u, |f u| ≤ B)
    (r r' h : ℝ) :
    |(∫ z : ℝ, f (r * z + h) ∂gaussianReal 0 1) - ∫ z : ℝ, f (r' * z + h) ∂gaussianReal 0 1| ≤
      L * |r - r'| := by
  have hint (c : ℝ) : Integrable (fun z : ℝ => f (c * z + h)) (gaussianReal 0 1) :=
    Integrable.of_bound (hcont.comp (by fun_prop)).aestronglyMeasurable B
      (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using hB _)
  have habs : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal 2).integrable (by norm_num)).abs
  rw [← integral_sub (hint r) (hint r')]
  refine abs_integral_le_integral_abs.trans ?_
  calc ∫ z : ℝ, |f (r * z + h) - f (r' * z + h)| ∂gaussianReal 0 1
      ≤ ∫ z : ℝ, L * |r - r'| * |z| ∂gaussianReal 0 1 := by
        refine integral_mono ((hint r).sub (hint r')).abs (habs.const_mul _) fun z => ?_
        have := hf (r * z + h) (r' * z + h)
        calc _ ≤ L * |r * z + h - (r' * z + h)| := this
          _ = L * |r - r'| * |z| := by
              rw [show r * z + h - (r' * z + h) = (r - r') * z by ring, abs_mul]
              ring
    _ = L * |r - r'| * ∫ z : ℝ, |z| ∂gaussianReal 0 1 := integral_const_mul _ _
    _ ≤ L * |r - r'| * 1 :=
        mul_le_mul_of_nonneg_left integral_abs_gaussianReal_le_one (by positivity)
    _ = _ := mul_one _

/-- `x ↦ x^n` is `n`-Lipschitz on `[0, 1]`. -/
theorem abs_pow_sub_pow_le_of_mem_Icc (n : ℕ) {a b : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) : |a ^ n - b ^ n| ≤ n * |a - b| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hbn : b ^ n ∈ Set.Icc (0 : ℝ) 1 := ⟨pow_nonneg hb.1 n, pow_le_one₀ hb.1 hb.2⟩
    have h1 : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + (a - b) * b ^ n := by ring
    rw [h1]
    calc _ ≤ |a * (a ^ n - b ^ n)| + |(a - b) * b ^ n| := abs_add_le _ _
      _ = a * |a ^ n - b ^ n| + |a - b| * b ^ n := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha.1, abs_of_nonneg hbn.1]
      _ ≤ 1 * (n * |a - b|) + |a - b| * 1 := by
          gcongr
          · exact ha.2
          · exact hbn.2
      _ = _ := by push_cast; ring

/-- The hyperbolic secant is 1-Lipschitz. -/
theorem abs_inv_cosh_sub_le (u v : ℝ) : |(Real.cosh u)⁻¹ - (Real.cosh v)⁻¹| ≤ |u - v| := by
  have hd : ∀ x : ℝ, HasDerivAt (fun u => (Real.cosh u)⁻¹)
      (-(Real.sinh x) / (Real.cosh x) ^ 2) x := by
    intro x
    simpa using (Real.hasDerivAt_cosh x).inv (Real.cosh_pos x).ne'
  have hb : ∀ x ∈ (Set.univ : Set ℝ), ‖deriv (fun u => (Real.cosh u)⁻¹) x‖ ≤ 1 := by
    intro x _
    rw [(hd x).deriv, Real.norm_eq_abs, abs_div, abs_neg, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ Real.cosh x ^ 2)]
    have hc := Real.one_le_cosh x
    have hs := Real.abs_sinh_le_cosh x
    rw [div_le_one (by positivity)]
    nlinarith
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun u => (Real.cosh u)⁻¹)
    (fun x _ => (hd x).differentiableAt) hb convex_univ (Set.mem_univ v) (Set.mem_univ u)
  simpa [Real.norm_eq_abs] using this

/-- `u ↦ (cosh u ^ n)⁻¹` is `n`-Lipschitz. -/
theorem abs_inv_cosh_pow_sub_le (n : ℕ) (u v : ℝ) :
    |(Real.cosh u ^ n)⁻¹ - (Real.cosh v ^ n)⁻¹| ≤ n * |u - v| := by
  have hm (x : ℝ) : (Real.cosh x)⁻¹ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, inv_le_one_of_one_le₀ (Real.one_le_cosh x)⟩
  rw [← inv_pow, ← inv_pow]
  exact (abs_pow_sub_pow_le_of_mem_Icc n (hm u) (hm v)).trans
    (mul_le_mul_of_nonneg_left (abs_inv_cosh_sub_le u v) (Nat.cast_nonneg n))

/-- `tanh ^ 4` is 4-Lipschitz. -/
theorem abs_tanh_pow_four_sub_le (u v : ℝ) :
    |Real.tanh u ^ 4 - Real.tanh v ^ 4| ≤ 4 * |u - v| := by
  have ha := Real.abs_tanh_lt_one u
  have hb := Real.abs_tanh_lt_one v
  have h1 : Real.tanh u ^ 4 - Real.tanh v ^ 4 = (Real.tanh u - Real.tanh v) *
      ((Real.tanh u + Real.tanh v) * (Real.tanh u ^ 2 + Real.tanh v ^ 2)) := by ring
  rw [h1, abs_mul]
  have h2 : |(Real.tanh u + Real.tanh v) * (Real.tanh u ^ 2 + Real.tanh v ^ 2)| ≤ 4 := by
    rw [abs_mul]
    have hs : |Real.tanh u + Real.tanh v| ≤ 2 := by
      have := abs_add_le (Real.tanh u) (Real.tanh v); linarith
    have hq : |Real.tanh u ^ 2 + Real.tanh v ^ 2| ≤ 2 := by
      rw [abs_of_nonneg (by positivity)]
      nlinarith [abs_nonneg (Real.tanh u), abs_nonneg (Real.tanh v), sq_abs (Real.tanh u),
        sq_abs (Real.tanh v)]
    nlinarith [abs_nonneg (Real.tanh u + Real.tanh v),
      abs_nonneg (Real.tanh u ^ 2 + Real.tanh v ^ 2)]
  calc _ ≤ |u - v| * 4 := by
        refine mul_le_mul (Real.abs_tanh_sub_tanh_le u v) h2 (abs_nonneg _) (abs_nonneg _)
    _ = _ := by ring

/-- The Gaussian average of `(cosh (r z + h) ^ (4p))⁻¹` is `4p`-Lipschitz in `r`. -/
theorem abs_integral_inv_cosh_pow_sub_le (p : ℕ) (r r' h : ℝ) :
    |(∫ z : ℝ, (Real.cosh (r * z + h) ^ (4 * p))⁻¹ ∂gaussianReal 0 1) -
      ∫ z : ℝ, (Real.cosh (r' * z + h) ^ (4 * p))⁻¹ ∂gaussianReal 0 1| ≤
      ((4 * p : ℕ) : ℝ) * |r - r'| :=
  abs_integral_gaussianReal_comp_sub_le (fun u => (Real.cosh u ^ (4 * p))⁻¹) (4 * p) 1
    (Nat.cast_nonneg _) (by fun_prop (disch := intro; positivity))
    (fun u v => abs_inv_cosh_pow_sub_le (4 * p) u v) (fun u => by
      rw [abs_of_nonneg (by positivity)]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (Real.one_le_cosh u))) r r' h

/-- The Gaussian average of `tanh (r z + h) ^ 4` is 4-Lipschitz in `r`. -/
theorem abs_integral_tanh_pow_four_sub_le (r r' h : ℝ) :
    |(∫ z : ℝ, Real.tanh (r * z + h) ^ 4 ∂gaussianReal 0 1) -
      ∫ z : ℝ, Real.tanh (r' * z + h) ^ 4 ∂gaussianReal 0 1| ≤ 4 * |r - r'| :=
  abs_integral_gaussianReal_comp_sub_le (fun u => Real.tanh u ^ 4) 4 1 (by norm_num)
    (by fun_prop) abs_tanh_pow_four_sub_le (fun u => by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (Real.abs_tanh_lt_one u).le) r r' h

end SpinGlasses
