/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GaussianCovarianceInterpolation

/-!
# Gaussian interpolation for a smooth function of the free energy

Let `L(y) = log ∑ₐ exp (y a + h a)` and `W : ℝ → ℝ` be `C²`.  The functional
`F_W(y) = W (n L(y))` has
* `∂_l F_W = n W'(n L) w_l`,
* `∂_k ∂_l F_W = n² W''(n L) w_l w_k + n W'(n L) w_l (1[l = k] - w_k)`,

where `w_l = exp (y l + h l) / ∑ₐ exp (y a + h a)` are the Gibbs weights.  Together with the
generic `hasDerivAt_integral_comp_trig` this gives the derivative along the trigonometric path of
`s ↦ 𝔼 W (n L(cos s X + sin s Y))`, which is the missing second-order term in Talagrand's
Eq. (1.125) (the case `W(x) = (x - a)^k` in the proof of Theorem 1.4.11).

## Main declarations

* `SpinGlasses.fderiv_comp_log_sum_exp_single`, `SpinGlasses.fderiv_fderiv_comp_log_sum_exp_single`:
  gradient and Hessian of `F_W`.
* `SpinGlasses.hasDerivAt_integral_comp_log_sum_exp_trig`: the derivative along the path.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped Real

namespace SpinGlasses

section Derivatives

variable {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] (h : κ → ℝ)

omit [DecidableEq κ] in
/-- `y ↦ log ∑ₐ exp (y a + h a)` has `fderiv` as its Fréchet derivative. -/
lemma hasFDerivAt_log_sum_exp_fderiv (y : κ → ℝ) :
    HasFDerivAt (fun y : κ → ℝ => Real.log (∑ a, Real.exp (y a + h a)))
      (fderiv ℝ (fun y : κ → ℝ => Real.log (∑ a, Real.exp (y a + h a))) y) y :=
  (((hasFDerivAt_sum_exp_add h y).log (sum_exp_add_pos h y).ne').differentiableAt).hasFDerivAt

omit [DecidableEq κ] in
lemma contDiff_log_sum_exp :
    ContDiff ℝ 2 (fun y : κ → ℝ => Real.log (∑ a, Real.exp (y a + h a))) :=
  ContDiff.log (ContDiff.sum fun a _ => ((contDiff_apply ℝ ℝ a).add contDiff_const).exp)
    fun y => (sum_exp_add_pos h y).ne'

lemma differentiable_fderiv_log_sum_exp_single (l : κ) :
    Differentiable ℝ (fun y : κ → ℝ =>
      fderiv ℝ (fun y : κ → ℝ => Real.log (∑ a, Real.exp (y a + h a))) y (Pi.single l 1)) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ (fun y : κ → ℝ => Real.log (∑ a, Real.exp (y a + h a)))) :=
    (contDiff_log_sum_exp h).fderiv_right (by norm_num)
  exact (h1.clm_apply contDiff_const).differentiable one_ne_zero

/-- **Gradient of a smooth function of the free energy:**
`∂_l W (n L(y)) = n W'(n L(y)) w_l(y)`. -/
theorem fderiv_comp_log_sum_exp_single {W : ℝ → ℝ} (hW : Differentiable ℝ W) (n : ℝ)
    (y : κ → ℝ) (l : κ) :
    fderiv ℝ (fun y : κ → ℝ => W (n * Real.log (∑ a, Real.exp (y a + h a)))) y (Pi.single l 1) =
      deriv W (n * Real.log (∑ a, Real.exp (y a + h a))) *
        (n * (Real.exp (y l + h l) / ∑ a, Real.exp (y a + h a))) := by
  have h2 : HasFDerivAt (fun y : κ → ℝ => W (n * Real.log (∑ a, Real.exp (y a + h a))))
      (deriv W (n * Real.log (∑ a, Real.exp (y a + h a))) •
        (n • fderiv ℝ (fun y : κ → ℝ => Real.log (∑ a, Real.exp (y a + h a))) y)) y :=
    (hW (n * Real.log (∑ a, Real.exp (y a + h a)))).hasDerivAt.comp_hasFDerivAt y
      ((hasFDerivAt_log_sum_exp_fderiv h y).const_mul n)
  rw [h2.fderiv]
  simp [fderiv_log_sum_exp_single]

/-- **Hessian of a smooth function of the free energy:**
`∂_k ∂_l W (n L) = n² W''(n L) w_l w_k + n W'(n L) w_l (1[l = k] - w_k)`. -/
theorem fderiv_fderiv_comp_log_sum_exp_single {W : ℝ → ℝ} (hW : ContDiff ℝ 2 W) (n : ℝ)
    (y : κ → ℝ) (l k : κ) :
    fderiv ℝ (fun y : κ → ℝ => fderiv ℝ (fun y : κ → ℝ =>
        W (n * Real.log (∑ a, Real.exp (y a + h a)))) y (Pi.single l 1)) y (Pi.single k 1) =
      n ^ 2 * deriv (deriv W) (n * Real.log (∑ a, Real.exp (y a + h a))) *
        (Real.exp (y l + h l) / ∑ a, Real.exp (y a + h a)) *
        (Real.exp (y k + h k) / ∑ a, Real.exp (y a + h a)) +
      n * deriv W (n * Real.log (∑ a, Real.exp (y a + h a))) *
        (Real.exp (y l + h l) / (∑ a, Real.exp (y a + h a)) *
          ((if l = k then 1 else 0) - Real.exp (y k + h k) / ∑ a, Real.exp (y a + h a))) := by
  have hW1 : Differentiable ℝ W := hW.differentiable (by norm_num)
  have hW2 : Differentiable ℝ (deriv W) := hW.differentiable_deriv_two
  have hfun : (fun y : κ → ℝ => fderiv ℝ (fun y : κ → ℝ =>
      W (n * Real.log (∑ a, Real.exp (y a + h a)))) y (Pi.single l 1)) = fun y =>
      deriv W (n * Real.log (∑ a, Real.exp (y a + h a))) *
        (n * fderiv ℝ (fun y : κ → ℝ => Real.log (∑ a, Real.exp (y a + h a))) y
          (Pi.single l 1)) := by
    ext y
    rw [fderiv_comp_log_sum_exp_single h hW1, fderiv_log_sum_exp_single]
  have hA : HasFDerivAt (fun y : κ → ℝ => deriv W (n * Real.log (∑ a, Real.exp (y a + h a))))
      (deriv (deriv W) (n * Real.log (∑ a, Real.exp (y a + h a))) •
        (n • fderiv ℝ (fun y : κ → ℝ => Real.log (∑ a, Real.exp (y a + h a))) y)) y :=
    HasDerivAt.comp_hasFDerivAt (h₂ := deriv W) y
      (hW2 (n * Real.log (∑ a, Real.exp (y a + h a)))).hasDerivAt
      ((hasFDerivAt_log_sum_exp_fderiv h y).const_mul n)
  have hB : HasFDerivAt (fun y : κ → ℝ => n * fderiv ℝ (fun y : κ → ℝ =>
      Real.log (∑ a, Real.exp (y a + h a))) y (Pi.single l 1))
      (n • fderiv ℝ (fun y : κ → ℝ => fderiv ℝ (fun y : κ → ℝ =>
        Real.log (∑ a, Real.exp (y a + h a))) y (Pi.single l 1)) y) y :=
    ((differentiable_fderiv_log_sum_exp_single h l y).hasFDerivAt).const_mul n
  rw [hfun, (hA.fun_mul hB).fderiv]
  have hdd := fderiv_fderiv_log_sum_exp_single h y l k
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [hdd]
  simp only [fderiv_log_sum_exp_single]
  ring

omit [DecidableEq κ] in
/-- The scaled free energy grows at most linearly: for every `c`,
`exp (c |n L(y)|) ≤ exp (|c| |n| |L(0)|) exp (|c| |n| ∑ₐ |y a|)`. -/
lemma exp_mul_abs_mul_log_sum_exp_le (n c : ℝ) (y : κ → ℝ) :
    Real.exp (c * |n * Real.log (∑ a, Real.exp (y a + h a))|) ≤
      Real.exp (|c| * |n| * |Real.log (∑ a, Real.exp (h a))|) *
        Real.exp (|c| * |n| * ∑ a, |y a|) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 := abs_log_sum_exp_le h y
  calc c * |n * Real.log (∑ a, Real.exp (y a + h a))|
      ≤ |c| * |n * Real.log (∑ a, Real.exp (y a + h a))| :=
        mul_le_mul_of_nonneg_right (le_abs_self c) (abs_nonneg _)
    _ = |c| * (|n| * |Real.log (∑ a, Real.exp (y a + h a))|) := by rw [abs_mul]
    _ ≤ |c| * (|n| * (|Real.log (∑ a, Real.exp (h a))| + ∑ a, |y a|)) := by gcongr
    _ = _ := by ring

omit [DecidableEq κ] in
/-- A function with exponential growth, composed with the scaled free energy, has exponential
growth in `‖y‖₁`. -/
lemma abs_comp_log_sum_exp_le {f : ℝ → ℝ} {C c : ℝ} (hf : ∀ x, |f x| ≤ C * Real.exp (c * |x|))
    (n : ℝ) (y : κ → ℝ) :
    |f (n * Real.log (∑ a, Real.exp (y a + h a)))| ≤
      C * Real.exp (|c| * |n| * |Real.log (∑ a, Real.exp (h a))|) *
        Real.exp (|c| * |n| * ∑ a, |y a|) := by
  have hC : 0 ≤ C := by simpa using (abs_nonneg _).trans (hf 0)
  calc _ ≤ C * Real.exp (c * |n * Real.log (∑ a, Real.exp (y a + h a))|) := hf _
    _ ≤ C * (Real.exp (|c| * |n| * |Real.log (∑ a, Real.exp (h a))|) *
          Real.exp (|c| * |n| * ∑ a, |y a|)) :=
        mul_le_mul_of_nonneg_left (exp_mul_abs_mul_log_sum_exp_le h n c y) hC
    _ = _ := by ring

end Derivatives

/-- Real-number core of the Hessian bound: with `0 ≤ w_l, w_k ≤ 1`, `|1[l = k] - w_k| ≤ 1`,
`|W'| ≤ M₁` and `|W''| ≤ M₂`, the entry `n² W'' w_l w_k + n W' w_l (1[l = k] - w_k)` is at most
`n² M₂ + |n| M₁` in absolute value. -/
lemma abs_hessian_term_le {n a₁ a₂ wl wk d M₁ M₂ : ℝ} (hwl : wl ∈ Set.Icc (0 : ℝ) 1)
    (hwk : wk ∈ Set.Icc (0 : ℝ) 1) (hd : |d - wk| ≤ 1) (ha₁ : |a₁| ≤ M₁) (ha₂ : |a₂| ≤ M₂) :
    |n ^ 2 * a₂ * wl * wk + n * a₁ * (wl * (d - wk))| ≤ n ^ 2 * M₂ + |n| * M₁ := by
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · have hp : wl * wk ≤ 1 := by nlinarith [hwl.1, hwl.2, hwk.1, hwk.2]
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg n), abs_of_nonneg hwl.1,
      abs_of_nonneg hwk.1]
    calc n ^ 2 * |a₂| * wl * wk = n ^ 2 * |a₂| * (wl * wk) := by ring
      _ ≤ n ^ 2 * |a₂| * 1 := mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ n ^ 2 * M₂ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left ha₂ (sq_nonneg n)
  · rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hwl.1]
    have hp : wl * |d - wk| ≤ 1 := by nlinarith [hwl.1, hwl.2, abs_nonneg (d - wk)]
    calc |n| * |a₁| * (wl * |d - wk|) ≤ |n| * |a₁| * 1 :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ |n| * M₁ := by rw [mul_one]; exact mul_le_mul_of_nonneg_left ha₁ (abs_nonneg n)

section Hessian

variable {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] (h : κ → ℝ)

/-- **Exponential bound on the Hessian entries of `F_W`.** -/
lemma abs_hessian_comp_log_sum_exp_le {W : ℝ → ℝ} (hW : ContDiff ℝ 2 W)
    {C₁ c₁ C₂ c₂ : ℝ} (hW1 : ∀ x, |deriv W x| ≤ C₁ * Real.exp (c₁ * |x|))
    (hW2 : ∀ x, |deriv (deriv W) x| ≤ C₂ * Real.exp (c₂ * |x|)) (n : ℝ) (y : κ → ℝ)
    (l k : κ) :
    |fderiv ℝ (fun y : κ → ℝ => fderiv ℝ (fun y : κ → ℝ =>
        W (n * Real.log (∑ a, Real.exp (y a + h a)))) y (Pi.single l 1)) y (Pi.single k 1)| ≤
      (n ^ 2 * (C₂ * Real.exp (|c₂| * |n| * |Real.log (∑ a, Real.exp (h a))|)) +
        |n| * (C₁ * Real.exp (|c₁| * |n| * |Real.log (∑ a, Real.exp (h a))|))) *
        Real.exp ((|c₁| * |n| + |c₂| * |n|) * ∑ a, |y a|) := by
  have hS : 0 ≤ ∑ a, |y a| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hC₁ : 0 ≤ C₁ := by simpa using (abs_nonneg _).trans (hW1 0)
  have hC₂ : 0 ≤ C₂ := by simpa using (abs_nonneg _).trans (hW2 0)
  rw [fderiv_fderiv_comp_log_sum_exp_single h hW n y l k]
  have hl := gibbsWeight_mem_Icc y h l
  have hk := gibbsWeight_mem_Icc y h k
  have hn1 : 0 ≤ |c₁| * |n| := by positivity
  have hn2 : 0 ≤ |c₂| * |n| := by positivity
  have e1 : Real.exp (|c₁| * |n| * ∑ a, |y a|) ≤
      Real.exp ((|c₁| * |n| + |c₂| * |n|) * ∑ a, |y a|) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) hS)
  have e2 : Real.exp (|c₂| * |n| * ∑ a, |y a|) ≤
      Real.exp ((|c₁| * |n| + |c₂| * |n|) * ∑ a, |y a|) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) hS)
  have b2 : |deriv (deriv W) (n * Real.log (∑ a, Real.exp (y a + h a)))| ≤
      C₂ * Real.exp (|c₂| * |n| * |Real.log (∑ a, Real.exp (h a))|) *
        Real.exp ((|c₁| * |n| + |c₂| * |n|) * ∑ a, |y a|) :=
    (abs_comp_log_sum_exp_le h hW2 n y).trans
      (mul_le_mul_of_nonneg_left e2 (by positivity))
  have b1 : |deriv W (n * Real.log (∑ a, Real.exp (y a + h a)))| ≤
      C₁ * Real.exp (|c₁| * |n| * |Real.log (∑ a, Real.exp (h a))|) *
        Real.exp ((|c₁| * |n| + |c₂| * |n|) * ∑ a, |y a|) :=
    (abs_comp_log_sum_exp_le h hW1 n y).trans
      (mul_le_mul_of_nonneg_left e1 (by positivity))
  have hhess := abs_hessian_term_le (n := n) hl hk (abs_ite_one_sub_le_one (p := l = k) hk) b1 b2
  calc _ ≤ _ := hhess
    _ = _ := by ring

end Hessian

section Trig

variable {κ Ω : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {X Y : κ → Ω → ℝ}

/-- **The Hessian entry of `F_W(y) = W (n log ∑ₐ exp (y a + h a))`:**
`n² W''(n L) w_l w_k + n W'(n L) w_l (1[l = k] - w_k)` with the Gibbs weights `w`.  It is a
definition because it is the integrand of Eq. (1.125) and is used in the statements of the
derivative, of its integrability and of the smart-path profile. -/
noncomputable def freeEnergyCompHessian (W : ℝ → ℝ) (n : ℝ) (h y : κ → ℝ) (l k : κ) : ℝ :=
  n ^ 2 * deriv (deriv W) (n * Real.log (∑ a, Real.exp (y a + h a))) *
      (Real.exp (y l + h l) / ∑ a, Real.exp (y a + h a)) *
      (Real.exp (y k + h k) / ∑ a, Real.exp (y a + h a)) +
    n * deriv W (n * Real.log (∑ a, Real.exp (y a + h a))) *
      (Real.exp (y l + h l) / (∑ a, Real.exp (y a + h a)) *
        ((if l = k then 1 else 0) - Real.exp (y k + h k) / ∑ a, Real.exp (y a + h a)))

/-- The Hessian entries of `F_W` along the path are integrable (exponential growth against a
Gaussian). -/
theorem integrable_freeEnergyCompHessian
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (hX : ∀ l, ∫ ω, X l ω ∂P = 0) (hY : ∀ l, ∫ ω, Y l ω ∂P = 0) {W : ℝ → ℝ}
    (hW : ContDiff ℝ 2 W) {C₁ c₁ C₂ c₂ : ℝ} (hW1 : ∀ x, |deriv W x| ≤ C₁ * Real.exp (c₁ * |x|))
    (hW2 : ∀ x, |deriv (deriv W) x| ≤ C₂ * Real.exp (c₂ * |x|)) (n : ℝ) (h : κ → ℝ) (t : ℝ)
    (l k : κ) :
    Integrable (fun ω => freeEnergyCompHessian W n h
      (fun m => Real.cos t * X m ω + Real.sin t * Y m ω) l k) P := by
  have hmean : ∀ k, ∫ ω, Sum.elim X Y k ω ∂P = 0 := by
    rintro (k | k)
    exacts [hX k, hY k]
  have hF : ContDiff ℝ 2 (fun y : κ → ℝ => W (n * Real.log (∑ a, Real.exp (y a + h a)))) :=
    hW.comp (contDiff_const.mul (contDiff_log_sum_exp h))
  have hG : Continuous (fun y : κ → ℝ => fderiv ℝ (fun y : κ → ℝ => fderiv ℝ (fun y : κ → ℝ =>
      W (n * Real.log (∑ a, Real.exp (y a + h a)))) y (Pi.single l 1)) y (Pi.single k 1)) := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ (fun y : κ → ℝ =>
        W (n * Real.log (∑ a, Real.exp (y a + h a))))) := hF.fderiv_right (by norm_num)
    have h2 : ContDiff ℝ 1 (fun y : κ → ℝ => fderiv ℝ (fun y : κ → ℝ =>
        W (n * Real.log (∑ a, Real.exp (y a + h a)))) y (Pi.single l 1)) :=
      h1.clm_apply contDiff_const
    exact (h2.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hC₁ : 0 ≤ C₁ := by simpa using (abs_nonneg _).trans (hW1 0)
  have hC₂ : 0 ≤ C₂ := by simpa using (abs_nonneg _).trans (hW2 0)
  have hD : 0 ≤ n ^ 2 * (C₂ * Real.exp (|c₂| * |n| * |Real.log (∑ a, Real.exp (h a))|)) +
      |n| * (C₁ * Real.exp (|c₁| * |n| * |Real.log (∑ a, Real.exp (h a))|)) := by positivity
  have hcc : 0 ≤ |c₁| * |n| + |c₂| * |n| := by positivity
  refine integrable_comp_of_exp_growth (X := Sum.elim X Y) hXY hmean
    (F := fun v : κ ⊕ κ → ℝ => freeEnergyCompHessian W n h
      (fun m => Real.cos t * v (Sum.inl m) + Real.sin t * v (Sum.inr m)) l k)
    ?_ (C := n ^ 2 * (C₂ * Real.exp (|c₂| * |n| * |Real.log (∑ a, Real.exp (h a))|)) +
      |n| * (C₁ * Real.exp (|c₁| * |n| * |Real.log (∑ a, Real.exp (h a))|)))
    (c := |c₁| * |n| + |c₂| * |n|) fun v => ?_
  · have : (fun v : κ ⊕ κ → ℝ => freeEnergyCompHessian W n h
        (fun m => Real.cos t * v (Sum.inl m) + Real.sin t * v (Sum.inr m)) l k) =
        fun v => fderiv ℝ (fun y : κ → ℝ => fderiv ℝ (fun y : κ → ℝ =>
          W (n * Real.log (∑ a, Real.exp (y a + h a)))) y (Pi.single l 1))
          (fun m => Real.cos t * v (Sum.inl m) + Real.sin t * v (Sum.inr m)) (Pi.single k 1) :=
      funext fun v => (fderiv_fderiv_comp_log_sum_exp_single h hW n _ l k).symm
    rw [this]
    exact (hG.comp (by fun_prop)).measurable
  · have key := abs_hessian_comp_log_sum_exp_le h hW hW1 hW2 n
      (fun m => Real.cos t * v (Sum.inl m) + Real.sin t * v (Sum.inr m)) l k
    rw [fderiv_fderiv_comp_log_sum_exp_single h hW n _ l k] at key
    refine key.trans ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
      (sum_abs_cos_mul_add_sin_mul_le t v) hcc)) hD

/-- **Derivative of `𝔼 W (n log ∑ₐ exp (Z_s(a) + h a))` along the trigonometric path
`Z_s = cos s X + sin s Y`** (the second-order term of Talagrand's Eq. (1.125)).  Let `W` be `C²`
with `W`, `W'`, `W''` of exponential growth and let `w_l = exp (Z_t l + h l) / ∑ₐ exp (Z_t a + h a)`
be the Gibbs weights.  Then the derivative at `t` is
`sin t cos t ∑_{l,k} (𝔼 Y_l Y_k - 𝔼 X_l X_k) 𝔼 H_{lk}` where `H_{lk}` is
`freeEnergyCompHessian`, `n² W''(n L) w_l w_k + n W'(n L) w_l (1[l = k] - w_k)`
with `L = log ∑ₐ exp (Z_t a + h a)`. -/
theorem hasDerivAt_integral_comp_log_sum_exp_trig
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (hX : ∀ l, ∫ ω, X l ω ∂P = 0) (hY : ∀ l, ∫ ω, Y l ω ∂P = 0)
    (h0 : ∀ l k, ∫ ω, X l ω * Y k ω ∂P = 0) {W : ℝ → ℝ} (hW : ContDiff ℝ 2 W)
    {C₀ c₀ C₁ c₁ C₂ c₂ : ℝ} (hW0 : ∀ x, |W x| ≤ C₀ * Real.exp (c₀ * |x|))
    (hW1 : ∀ x, |deriv W x| ≤ C₁ * Real.exp (c₁ * |x|))
    (hW2 : ∀ x, |deriv (deriv W) x| ≤ C₂ * Real.exp (c₂ * |x|)) (n : ℝ) (h : κ → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ∫ ω, W (n * Real.log (∑ a, Real.exp (Real.cos s * X a ω +
        Real.sin s * Y a ω + h a))) ∂P)
      (Real.sin t * Real.cos t * ∑ l, ∑ k, ((∫ ω, Y l ω * Y k ω ∂P) - ∫ ω, X l ω * X k ω ∂P) *
        ∫ ω, freeEnergyCompHessian W n h (fun m => Real.cos t * X m ω + Real.sin t * Y m ω) l k
          ∂P) t := by
  have hW1d : Differentiable ℝ W := hW.differentiable (by norm_num)
  have hF : ContDiff ℝ 2 (fun y : κ → ℝ => W (n * Real.log (∑ a, Real.exp (y a + h a)))) :=
    hW.comp (contDiff_const.mul (contDiff_log_sum_exp h))
  have hC₀ : 0 ≤ C₀ := by simpa using (abs_nonneg _).trans (hW0 0)
  have hC₁ : 0 ≤ C₁ := by simpa using (abs_nonneg _).trans (hW1 0)
  have hC₂ : 0 ≤ C₂ := by simpa using (abs_nonneg _).trans (hW2 0)
  have hS : ∀ y : κ → ℝ, 0 ≤ ∑ a, |y a| := fun y => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have key := hasDerivAt_integral_comp_trig hXY hX hY h0 hF
    (C₀ := C₀ * Real.exp (|c₀| * |n| * |Real.log (∑ a, Real.exp (h a))|))
    (c₀ := |c₀| * |n|) (fun y => abs_comp_log_sum_exp_le h hW0 n y)
    (D := fun _ => C₁ * Real.exp (|c₁| * |n| * |Real.log (∑ a, Real.exp (h a))|) * |n|)
    (c₁ := |c₁| * |n|) (fun l y => by
      rw [fderiv_comp_log_sum_exp_single h hW1d, abs_mul, abs_mul]
      have hw := gibbsWeight_mem_Icc y h l
      calc |deriv W (n * Real.log (∑ a, Real.exp (y a + h a)))| *
            (|n| * |Real.exp (y l + h l) / ∑ a, Real.exp (y a + h a)|)
          ≤ (C₁ * Real.exp (|c₁| * |n| * |Real.log (∑ a, Real.exp (h a))|) *
              Real.exp (|c₁| * |n| * ∑ a, |y a|)) * (|n| * 1) := by
            refine mul_le_mul (abs_comp_log_sum_exp_le h hW1 n y)
              (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) (by positivity)
              (by positivity)
            rw [abs_of_nonneg hw.1]; exact hw.2
        _ = _ := by ring)
    (D2 := fun _ _ => n ^ 2 * (C₂ * Real.exp (|c₂| * |n| * |Real.log (∑ a, Real.exp (h a))|)) +
      |n| * (C₁ * Real.exp (|c₁| * |n| * |Real.log (∑ a, Real.exp (h a))|)))
    (c₂ := |c₁| * |n| + |c₂| * |n|)
    (fun k l y => abs_hessian_comp_log_sum_exp_le h hW hW1 hW2 n y l k) t
  refine key.congr_deriv ?_
  congr 1
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  congr 1
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  exact fderiv_fderiv_comp_log_sum_exp_single h hW n _ l k

/-- **Eq. (1.125), pathwise form:** the derivative of `s ↦ 𝔼 W (n L_s)` at `t` is
`sin t cos t · 𝔼 ∑_{l,k} (𝔼 Y_l Y_k - 𝔼 X_l X_k) F_W''_{lk}(Z_t)`, with the expectation outside
the double sum. -/
theorem hasDerivAt_integral_comp_log_sum_exp_trig_integral
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (hX : ∀ l, ∫ ω, X l ω ∂P = 0) (hY : ∀ l, ∫ ω, Y l ω ∂P = 0)
    (h0 : ∀ l k, ∫ ω, X l ω * Y k ω ∂P = 0) {W : ℝ → ℝ} (hW : ContDiff ℝ 2 W)
    {C₀ c₀ C₁ c₁ C₂ c₂ : ℝ} (hW0 : ∀ x, |W x| ≤ C₀ * Real.exp (c₀ * |x|))
    (hW1 : ∀ x, |deriv W x| ≤ C₁ * Real.exp (c₁ * |x|))
    (hW2 : ∀ x, |deriv (deriv W) x| ≤ C₂ * Real.exp (c₂ * |x|)) (n : ℝ) (h : κ → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ∫ ω, W (n * Real.log (∑ a, Real.exp (Real.cos s * X a ω +
        Real.sin s * Y a ω + h a))) ∂P)
      (Real.sin t * Real.cos t * ∫ ω, ∑ l, ∑ k, ((∫ ω', Y l ω' * Y k ω' ∂P) -
        ∫ ω', X l ω' * X k ω' ∂P) * freeEnergyCompHessian W n h
          (fun m => Real.cos t * X m ω + Real.sin t * Y m ω) l k ∂P) t := by
  refine (hasDerivAt_integral_comp_log_sum_exp_trig hXY hX hY h0 hW hW0 hW1 hW2 n h
    t).congr_deriv ?_
  congr 1
  have hint := integrable_freeEnergyCompHessian hXY hX hY hW hW1 hW2 n h t
  rw [integral_finsetSum _ fun l _ => integrable_finsetSum _ fun k _ => (hint l k).const_mul _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_finsetSum _ fun k _ => (hint l k).const_mul _]
  exact Finset.sum_congr rfl fun k _ => (integral_const_mul _ _).symm

end Trig

end SpinGlasses
