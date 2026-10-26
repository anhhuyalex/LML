/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.AddPowEstimates
public import LeanMachineLearning.SpinGlasses.Concentration
public import LeanMachineLearning.SpinGlasses.GaussianComparison
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianVector
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianGram
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.SinCosEndpoint

/-!
# Gaussian interpolation for smooth functionals

Let `X` and `Y` be independent centered Gaussian vectors on a finite index set `κ` with covariance
matrices `A` and `B`.  Along the trigonometric path `Z_s = cos s X + sin s Y` the expectation of a
smooth bounded functional `F` has derivative
`(d/ds) 𝔼 F (Z_s) = sin s cos s ∑_{l,k} (B_{lk} - A_{lk}) 𝔼 ∂_k ∂_l F (Z_s)`,
by Gaussian integration by parts (the smooth counterpart of
`SpinGlasses.hasDerivAt_integral_log_sum_exp_trig`, which treats `F = log ∑ exp`).  Integrating
over `s ∈ [0, π/2]` gives the Lipschitz dependence of Gaussian expectations on the covariance,
`|𝔼 F (Y) - 𝔼 F (X)| ≤ ½ ∑_{l,k} |B_{lk} - A_{lk}| ‖∂_k ∂_l F‖_∞`.

## Main declarations

* `SpinGlasses.hasDerivAt_integral_comp_trig`: the derivative along the path.
* `SpinGlasses.abs_integral_comp_sub_le`: the covariance comparison.
* `SpinGlasses.integral_comp_le_of_covariance_le`: **Slepian's lemma** for a general `C²` test
  function `F` with `∂_k ∂_l F ≥ 0` for `l ≠ k` and exponentially bounded value, gradient and
  Hessian ([Talagrand, Prop. 1.3.3]).
* `SpinGlasses.integral_log_sum_exp_le_of_covariance_le`: the instance `F = - log ∑ₐ exp (· + h)`,
  the Gaussian comparison for the free energy used by the Guerra–Toninelli theorem.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.2.
* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, §1.3 and §1.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped Real

namespace SpinGlasses

variable {κ Ω : Type*} [Fintype κ] [DecidableEq κ] {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The derivative of a differentiable `F` in a direction `w` is the sum of the partial
derivatives weighted by the coordinates of `w`. -/
theorem fderiv_apply_eq_sum_mul {F : (κ → ℝ) → ℝ} (y w : κ → ℝ) :
    fderiv ℝ F y w = ∑ l, w l * fderiv ℝ F y (Pi.single l 1) := by
  have h := ((fderiv ℝ F y : (κ → ℝ) →L[ℝ] ℝ) : (κ → ℝ) →ₗ[ℝ] ℝ).pi_apply_eq_sum_univ w
  simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 2
  ext m
  simp [Pi.single_apply, eq_comm]

variable {X Y : κ → Ω → ℝ}

omit [DecidableEq κ] in
/-- The `ℓ¹` norm of the rotated vector `cos s a + sin s b` is at most that of `(a, b)`. -/
lemma sum_abs_cos_mul_add_sin_mul_le (s : ℝ) (v : κ ⊕ κ → ℝ) :
    ∑ l, |Real.cos s * v (Sum.inl l) + Real.sin s * v (Sum.inr l)| ≤ ∑ p, |v p| := by
  rw [Fintype.sum_sum_type]
  calc ∑ l, |Real.cos s * v (Sum.inl l) + Real.sin s * v (Sum.inr l)|
      ≤ ∑ l, (|v (Sum.inl l)| + |v (Sum.inr l)|) :=
        Finset.sum_le_sum fun l _ => (abs_add_le _ _).trans (add_le_add
          (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one s))
          (by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one s)))
    _ = _ := Finset.sum_add_distrib

/-- **Derivative of a smooth Gaussian functional along the trigonometric path.**  For independent
centered Gaussian vectors `X`, `Y` (jointly Gaussian with `𝔼 X Y = 0`) and a `C²` functional `F`
whose value, gradient and Hessian grow at most exponentially in `‖y‖₁`, the derivative of
`s ↦ 𝔼 F (cos s X + sin s Y)` at `t` is
`sin t cos t ∑_{l,k} (𝔼 Y_l Y_k - 𝔼 X_l X_k) 𝔼 ∂_k ∂_l F (Z_t)` for `Z_t = cos t X + sin t Y`. -/
theorem hasDerivAt_integral_comp_trig
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (hX : ∀ l, ∫ ω, X l ω ∂P = 0) (hY : ∀ l, ∫ ω, Y l ω ∂P = 0)
    (h0 : ∀ l k, ∫ ω, X l ω * Y k ω ∂P = 0) {F : (κ → ℝ) → ℝ} (hF : ContDiff ℝ 2 F)
    {C₀ c₀ : ℝ} (hF0 : ∀ y, |F y| ≤ C₀ * Real.exp (c₀ * ∑ l, |y l|)) {D : κ → ℝ} {c₁ : ℝ}
    (hF1 : ∀ l y, |fderiv ℝ F y (Pi.single l 1)| ≤ D l * Real.exp (c₁ * ∑ l, |y l|))
    {D2 : κ → κ → ℝ} {c₂ : ℝ}
    (hF2 : ∀ k l y, |fderiv ℝ (fun y => fderiv ℝ F y (Pi.single l 1)) y (Pi.single k 1)| ≤
      D2 k l * Real.exp (c₂ * ∑ l, |y l|)) (t : ℝ) :
    HasDerivAt (fun s => ∫ ω, F (fun l => Real.cos s * X l ω + Real.sin s * Y l ω) ∂P)
      (Real.sin t * Real.cos t * ∑ l, ∑ k, ((∫ ω, Y l ω * Y k ω ∂P) - ∫ ω, X l ω * X k ω ∂P) *
        ∫ ω, fderiv ℝ (fun y => fderiv ℝ F y (Pi.single l 1))
          (fun m => Real.cos t * X m ω + Real.sin t * Y m ω) (Pi.single k 1) ∂P) t := by
  classical
  have hP := hXY.isProbabilityMeasure
  have hFd : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hFc : Continuous F := hFd.continuous
  have hFl : ∀ l, Differentiable ℝ (fun y => fderiv ℝ F y (Pi.single l 1)) := fun l => by
    have h1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
    exact (h1.clm_apply contDiff_const).differentiable one_ne_zero
  have hXi : ∀ l, Integrable (X l) P := fun l => (hXY.eval (Sum.inl l)).integrable
  have hYi : ∀ l, Integrable (Y l) P := fun l => (hXY.eval (Sum.inr l)).integrable
  have hmean : ∀ k, ∫ ω, Sum.elim X Y k ω ∂P = 0 := by
    rintro (k | k)
    exacts [hX k, hY k]
  have hD0 : ∀ l, 0 ≤ D l := fun l => by simpa using (abs_nonneg _).trans (hF1 l 0)
  have hC₀ : 0 ≤ C₀ := by simpa using (abs_nonneg _).trans (hF0 0)
  -- the exponential bound on the integrand of the derivative
  have hbd : ∀ (s : ℝ) (l : κ) (v : κ ⊕ κ → ℝ),
      |(-Real.sin s * v (Sum.inl l) + Real.cos s * v (Sum.inr l)) *
        fderiv ℝ F (fun m => Real.cos s * v (Sum.inl m) + Real.sin s * v (Sum.inr m))
          (Pi.single l 1)| ≤ D l * Real.exp ((|c₁| + 1) * ∑ p, |v p|) := fun s l v => by
    have hS : (0 : ℝ) ≤ ∑ p, |v p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hlr : |v (Sum.inl l)| + |v (Sum.inr l)| ≤ ∑ p, |v p| := by
      rw [Fintype.sum_sum_type]
      exact add_le_add (Finset.single_le_sum (f := fun m => |v (Sum.inl m)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ l)) (Finset.single_le_sum
        (f := fun m => |v (Sum.inr m)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ l))
    have hZ := sum_abs_cos_mul_add_sin_mul_le s v
    have hexp : Real.exp (c₁ * ∑ m, |Real.cos s * v (Sum.inl m) + Real.sin s * v (Sum.inr m)|) ≤
        Real.exp (|c₁| * ∑ p, |v p|) := Real.exp_le_exp.2 ((mul_le_mul_of_nonneg_right
          (le_abs_self c₁) (Finset.sum_nonneg fun _ _ => abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hZ (abs_nonneg _)))
    rw [abs_mul]
    calc _ ≤ (∑ p, |v p|) * (D l * Real.exp (|c₁| * ∑ p, |v p|)) :=
          mul_le_mul ((abs_neg_sin_mul_add_cos_mul_le _ _ s).trans hlr)
            ((hF1 l _).trans (mul_le_mul_of_nonneg_left hexp (hD0 l))) (abs_nonneg _) hS
      _ = D l * ((∑ p, |v p|) * Real.exp (|c₁| * ∑ p, |v p|)) := by ring
      _ ≤ D l * (Real.exp (∑ p, |v p|) * Real.exp (|c₁| * ∑ p, |v p|)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (by linarith [Real.add_one_le_exp (∑ p, |v p|)]) (Real.exp_pos _).le) (hD0 l)
      _ = D l * Real.exp ((|c₁| + 1) * ∑ p, |v p|) := by
          rw [← Real.exp_add]; congr 2; ring
  have hder := hasDerivAt_integral_comp_of_exp_growth (X := Sum.elim X Y) hXY hmean
    (G := fun s v => F fun l => Real.cos s * v (Sum.inl l) + Real.sin s * v (Sum.inr l))
    (G' := fun s v => ∑ l, (-Real.sin s * v (Sum.inl l) + Real.cos s * v (Sum.inr l)) *
      fderiv ℝ F (fun m => Real.cos s * v (Sum.inl m) + Real.sin s * v (Sum.inr m))
        (Pi.single l 1)) t
    (fun s => (hFc.comp (by fun_prop)).measurable)
    (Finset.measurable_sum _ fun l _ => (by fun_prop : Measurable _).mul
      ((((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const).measurable).comp
        (by fun_prop)))
    (fun s v => by
      have hpath : HasDerivAt (fun s => fun l => Real.cos s * v (Sum.inl l) +
          Real.sin s * v (Sum.inr l)) (fun l => -Real.sin s * v (Sum.inl l) +
          Real.cos s * v (Sum.inr l)) s :=
        hasDerivAt_pi.2 fun l => ((Real.hasDerivAt_cos s).mul_const _).add
          ((Real.hasDerivAt_sin s).mul_const _)
      refine ((hFd _).hasFDerivAt.comp_hasDerivAt s hpath).congr_deriv ?_
      rw [fderiv_apply_eq_sum_mul])
    (C := ∑ l, D l) (c := |c₁| + 1) (fun s v => by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun l _ => hbd s l v)
    (C₀ := C₀) (c₀ := |c₀|) (fun v => by
      refine (hF0 _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC₀)
      exact (mul_le_mul_of_nonneg_right (le_abs_self c₀)
        (Finset.sum_nonneg fun _ _ => abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_left (sum_abs_cos_mul_add_sin_mul_le t v) (abs_nonneg _)))
  refine hder.congr_deriv ?_
  -- Gaussian integration by parts
  have hlin := hasGaussianLaw_sumElim_lincomb hXY (-Real.sin t) (Real.cos t) (Real.cos t)
    (Real.sin t)
  have hWmean : ∀ l, ∫ ω, (-Real.sin t * X l ω + Real.cos t * Y l ω) ∂P = 0 :=
    integral_lincomb_eq_zero hX hY hXi hYi _ _
  have hZmean : ∀ l, ∫ ω, (Real.cos t * X l ω + Real.sin t * Y l ω) ∂P = 0 :=
    integral_lincomb_eq_zero hX hY hXi hYi _ _
  have hstein : ∀ l, ∫ ω, (-Real.sin t * X l ω + Real.cos t * Y l ω) *
      fderiv ℝ F (fun m => Real.cos t * X m ω + Real.sin t * Y m ω) (Pi.single l 1) ∂P =
      Real.sin t * Real.cos t * ∑ k, ((∫ ω, Y l ω * Y k ω ∂P) - ∫ ω, X l ω * X k ω ∂P) *
        ∫ ω, fderiv ℝ (fun y => fderiv ℝ F y (Pi.single l 1))
          (fun m => Real.cos t * X m ω + Real.sin t * Y m ω) (Pi.single k 1) ∂P := fun l => by
    have h := integral_mul_comp_eq_sum_integral_mul_of_sum
      (W := fun a ω => -Real.sin t * X a ω + Real.cos t * Y a ω)
      (X := fun a ω => Real.cos t * X a ω + Real.sin t * Y a ω) hlin hWmean hZmean l
      (F := fun y => fderiv ℝ F y (Pi.single l 1)) (hFl l) (C := D l) (c := c₁)
      (fun y => hF1 l y) (D := fun k => D2 k l) (d := fun _ => c₂)
      (fun k y => hF2 k l y)
    rw [h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_lincomb_mul_lincomb hXY h0 (-Real.sin t) (Real.cos t) (Real.cos t)
      (Real.sin t) l k]
    ring
  have hint : ∀ l, Integrable (fun ω => (-Real.sin t * X l ω + Real.cos t * Y l ω) *
      fderiv ℝ F (fun m => Real.cos t * X m ω + Real.sin t * Y m ω) (Pi.single l 1)) P :=
    fun l => integrable_comp_of_exp_growth (X := Sum.elim X Y) hXY hmean
      (F := fun v => (-Real.sin t * v (Sum.inl l) + Real.cos t * v (Sum.inr l)) *
        fderiv ℝ F (fun m => Real.cos t * v (Sum.inl m) + Real.sin t * v (Sum.inr m))
          (Pi.single l 1))
      ((by fun_prop : Measurable _).mul
        ((((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const).measurable).comp
          (by fun_prop)))
      (C := D l) (c := |c₁| + 1) (fun v => hbd t l v)
  change ∫ ω, ∑ l, (-Real.sin t * X l ω + Real.cos t * Y l ω) *
      fderiv ℝ F (fun m => Real.cos t * X m ω + Real.sin t * Y m ω) (Pi.single l 1) ∂P = _
  rw [integral_finsetSum _ fun l _ => hint l]
  simp_rw [hstein]
  rw [Finset.mul_sum]

/-- **Lipschitz dependence of Gaussian expectations on the covariance.**  For independent centered
Gaussian vectors `X`, `Y` and a `C²` functional `F` with bounded value, gradient and Hessian,
`|𝔼 F (Y) - 𝔼 F (X)| ≤ ½ ∑_{l,k} |𝔼 Y_l Y_k - 𝔼 X_l X_k| ‖∂_k ∂_l F‖_∞`. -/
theorem abs_integral_comp_sub_le
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (hX : ∀ l, ∫ ω, X l ω ∂P = 0) (hY : ∀ l, ∫ ω, Y l ω ∂P = 0)
    (h0 : ∀ l k, ∫ ω, X l ω * Y k ω ∂P = 0) {F : (κ → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) {B : ℝ}
    (hF0 : ∀ y, |F y| ≤ B) {D : κ → ℝ} (hF1 : ∀ l y, |fderiv ℝ F y (Pi.single l 1)| ≤ D l)
    {D2 : κ → κ → ℝ}
    (hF2 : ∀ k l y, |fderiv ℝ (fun y => fderiv ℝ F y (Pi.single l 1)) y (Pi.single k 1)| ≤
      D2 k l) :
    |∫ ω, F (fun l => Y l ω) ∂P - ∫ ω, F (fun l => X l ω) ∂P| ≤
      (1 / 2) * ∑ l, ∑ k, |(∫ ω, Y l ω * Y k ω ∂P) - ∫ ω, X l ω * X k ω ∂P| * D2 k l := by
  classical
  have hP := hXY.isProbabilityMeasure
  have hd := fun s => hasDerivAt_integral_comp_trig hXY hX hY h0 hF
    (C₀ := B) (c₀ := 0) (fun y => by simpa using hF0 y) (D := D) (c₁ := 0)
    (fun l y => by simpa using hF1 l y) (D2 := D2) (c₂ := 0)
    (fun k l y => by simpa using hF2 k l y) s
  have h := Real.abs_sub_le_half_of_abs_deriv_le
    (φ := fun s => ∫ ω, F (fun l => Real.cos s * X l ω + Real.sin s * Y l ω) ∂P)
    (K := ∑ l, ∑ k, |(∫ ω, Y l ω * Y k ω ∂P) - ∫ ω, X l ω * X k ω ∂P| * D2 k l) hd
    (fun s hs => by
      have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs.1
        (hs.2.trans (by linarith [Real.pi_pos]))
      have hcos : 0 ≤ Real.cos s := Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩
      rw [abs_mul, abs_of_nonneg (mul_nonneg hsin hcos), mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hsin hcos)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have := norm_integral_le_of_norm_le_const (μ := P) (C := D2 k l)
        (f := fun ω => fderiv ℝ (fun y => fderiv ℝ F y (Pi.single l 1))
          (fun m => Real.cos s * X m ω + Real.sin s * Y m ω) (Pi.single k 1))
        (ae_of_all _ fun ω => by simpa using hF2 k l _)
      simpa using this)
  simp only [Real.cos_zero, Real.sin_zero, Real.sin_pi_div_two, Real.cos_pi_div_two] at h
  simpa [mul_comm, div_eq_inv_mul] using h

/-- **Slepian's lemma for a general test function** ([Talagrand, Prop. 1.3.3]).  Let `X`, `Y` be
independent centered Gaussian vectors (jointly Gaussian with `𝔼 X Y = 0`; this is no restriction,
as only the two laws matter) with the same variances, `𝔼 X_l² = 𝔼 Y_l²`, and
`𝔼 X_l X_k ≤ 𝔼 Y_l Y_k` for `l ≠ k`.  If `F` is `C²` with `∂_k ∂_l F ≥ 0` for `l ≠ k` and its value,
gradient and Hessian grow at most exponentially in `‖y‖₁`, then `𝔼 F(X) ≤ 𝔼 F(Y)`.  (With the
book's notation `u = Y`, `v = X`.)  Indeed `s ↦ 𝔼 F (cos s X + sin s Y)` has derivative
`sin s cos s ∑_{l,k} (𝔼 Y_l Y_k - 𝔼 X_l X_k) 𝔼 ∂_k ∂_l F (Z_s) ≥ 0` on `[0, π/2]`
(`hasDerivAt_integral_comp_trig`): the diagonal terms vanish and the others are products of
nonnegative factors. -/
theorem integral_comp_le_of_covariance_le
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (hX : ∀ l, ∫ ω, X l ω ∂P = 0) (hY : ∀ l, ∫ ω, Y l ω ∂P = 0)
    (h0 : ∀ l k, ∫ ω, X l ω * Y k ω ∂P = 0)
    (hdiag : ∀ l, ∫ ω, Y l ω * Y l ω ∂P = ∫ ω, X l ω * X l ω ∂P)
    (hle : ∀ l k, l ≠ k → ∫ ω, X l ω * X k ω ∂P ≤ ∫ ω, Y l ω * Y k ω ∂P)
    {F : (κ → ℝ) → ℝ} (hF : ContDiff ℝ 2 F)
    (hmix : ∀ l k y, l ≠ k →
      0 ≤ fderiv ℝ (fun y => fderiv ℝ F y (Pi.single l 1)) y (Pi.single k 1))
    {C₀ c₀ : ℝ} (hF0 : ∀ y, |F y| ≤ C₀ * Real.exp (c₀ * ∑ l, |y l|)) {D : κ → ℝ} {c₁ : ℝ}
    (hF1 : ∀ l y, |fderiv ℝ F y (Pi.single l 1)| ≤ D l * Real.exp (c₁ * ∑ l, |y l|))
    {D2 : κ → κ → ℝ} {c₂ : ℝ}
    (hF2 : ∀ k l y, |fderiv ℝ (fun y => fderiv ℝ F y (Pi.single l 1)) y (Pi.single k 1)| ≤
      D2 k l * Real.exp (c₂ * ∑ l, |y l|)) :
    ∫ ω, F (fun l => X l ω) ∂P ≤ ∫ ω, F (fun l => Y l ω) ∂P := by
  have hd := fun s => hasDerivAt_integral_comp_trig hXY hX hY h0 hF hF0 hF1 hF2 s
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc 0 (π / 2))
    (fun s _ => (hd s).differentiableAt.continuousAt.continuousWithinAt)
    (fun s _ => (hd s).differentiableAt.differentiableWithinAt) (fun s hs => by
      rw [interior_Icc] at hs
      rw [(hd s).deriv]
      have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs.1.le
        (hs.2.le.trans (by linarith [Real.pi_pos]))
      have hcos : 0 ≤ Real.cos s := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs.1, Real.pi_pos],
        hs.2.le⟩
      refine mul_nonneg (mul_nonneg hsin hcos) (Finset.sum_nonneg fun l _ =>
        Finset.sum_nonneg fun k _ => ?_)
      by_cases hlk : l = k
      · subst hlk
        simp [hdiag]
      · exact mul_nonneg (sub_nonneg.2 (hle l k hlk)) (integral_nonneg fun ω => hmix l k _ hlk))
  have := hmono ⟨le_rfl, by linarith [Real.pi_pos]⟩ ⟨by linarith [Real.pi_pos], le_rfl⟩
    (by linarith [Real.pi_pos])
  simpa using this

section Gram

open scoped Matrix

variable {K K' : Type*} [Fintype K] [Fintype K']

/-- **Gaussian expectations depend Lipschitz-continuously on the Gram matrix.**  For families of
vectors `a l ∈ ℝ^K` and `a' l ∈ ℝ^K'` and a `C²` functional `F` with bounded value, gradient and
Hessian, with `ξ`, `ξ'` standard Gaussian vectors,
`|𝔼 F ((a' l ⬝ᵥ ξ')_l) - 𝔼 F ((a l ⬝ᵥ ξ)_l)| ≤ ½ ∑_{l,k} |a' l ⬝ᵥ a' k - a l ⬝ᵥ a k| ‖∂_k ∂_l F‖_∞`.
-/
theorem abs_integral_dotProduct_sub_le (a : κ → K → ℝ) (a' : κ → K' → ℝ) {F : (κ → ℝ) → ℝ}
    (hF : ContDiff ℝ 2 F) {B : ℝ} (hF0 : ∀ y, |F y| ≤ B) {D : κ → ℝ}
    (hF1 : ∀ l y, |fderiv ℝ F y (Pi.single l 1)| ≤ D l) {D2 : κ → κ → ℝ}
    (hF2 : ∀ k l y, |fderiv ℝ (fun y => fderiv ℝ F y (Pi.single l 1)) y (Pi.single k 1)| ≤
      D2 k l) :
    |∫ ξ', F (fun l => a' l ⬝ᵥ ξ') ∂(Measure.pi fun _ : K' => gaussianReal 0 1) -
        ∫ ξ, F (fun l => a l ⬝ᵥ ξ) ∂(Measure.pi fun _ : K => gaussianReal 0 1)| ≤
      (1 / 2) * ∑ l, ∑ k, |a' l ⬝ᵥ a' k - a l ⬝ᵥ a k| * D2 k l := by
  classical
  -- both vectors are linear forms of one standard Gaussian vector on `K ⊕ K'`
  set P : Measure (K ⊕ K' → ℝ) := Measure.pi fun _ => gaussianReal 0 1 with hP
  obtain ⟨a1, ha1⟩ : ∃ a1 : κ → K ⊕ K' → ℝ, ∀ l, a1 l = Sum.elim (a l) fun _ => 0 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a2 : κ → K ⊕ K' → ℝ, ∀ l, a2 l = Sum.elim (fun _ => 0) (a' l) :=
    ⟨_, fun _ => rfl⟩
  have hdot1 : ∀ l k, a1 l ⬝ᵥ a1 k = a l ⬝ᵥ a k := fun l k => by
    simp [ha1, dotProduct, Fintype.sum_sum_type]
  have hdot2 : ∀ l k, a2 l ⬝ᵥ a2 k = a' l ⬝ᵥ a' k := fun l k => by
    simp [ha2, dotProduct, Fintype.sum_sum_type]
  have hdot12 : ∀ l k, a1 l ⬝ᵥ a2 k = 0 := fun l k => by
    simp [ha1, ha2, dotProduct, Fintype.sum_sum_type]
  have hfam : HasGaussianLaw (fun (ξ : K ⊕ K' → ℝ) (s : κ ⊕ κ) =>
      (Sum.elim a1 a2 s) ⬝ᵥ ξ) P := hasGaussianLaw_dotProduct_family (Sum.elim a1 a2)
  have hXY : HasGaussianLaw (fun ξ s => Sum.elim (fun l (ξ : K ⊕ K' → ℝ) => a1 l ⬝ᵥ ξ)
      (fun l ξ => a2 l ⬝ᵥ ξ) s ξ) P := by
    have e : (fun (ξ : K ⊕ K' → ℝ) (s : κ ⊕ κ) => Sum.elim (fun l (ξ : K ⊕ K' → ℝ) =>
        a1 l ⬝ᵥ ξ) (fun l ξ => a2 l ⬝ᵥ ξ) s ξ) = fun ξ s => (Sum.elim a1 a2 s) ⬝ᵥ ξ := by
      funext ξ s
      rcases s with l | l <;> rfl
    rw [e]
    exact hfam
  have hX : ∀ l, ∫ ξ, a1 l ⬝ᵥ ξ ∂P = 0 := fun l => integral_dotProduct_pi_gaussianReal _
  have hY : ∀ l, ∫ ξ, a2 l ⬝ᵥ ξ ∂P = 0 := fun l => integral_dotProduct_pi_gaussianReal _
  have h0 : ∀ l k, ∫ ξ, a1 l ⬝ᵥ ξ * (a2 k ⬝ᵥ ξ) ∂P = 0 := fun l k => by
    rw [integral_dotProduct_mul_dotProduct_pi_gaussianReal, hdot12]
  have key := abs_integral_comp_sub_le (X := fun l (ξ : K ⊕ K' → ℝ) => a1 l ⬝ᵥ ξ)
    (Y := fun l ξ => a2 l ⬝ᵥ ξ) hXY hX hY h0 hF hF0 hF1 hF2
  beta_reduce at key
  simp only [hP, integral_dotProduct_mul_dotProduct_pi_gaussianReal, hdot1, hdot2] at key
  have hFm : Measurable F := (hF.continuous).measurable
  have hcov1 : ∀ r s, ∫ ξ, a1 r ⬝ᵥ ξ * (a1 s ⬝ᵥ ξ) ∂P = a r ⬝ᵥ a s := fun r s => by
    rw [integral_dotProduct_mul_dotProduct_pi_gaussianReal, hdot1]
  have hcov2 : ∀ r s, ∫ ξ, a2 r ⬝ᵥ ξ * (a2 s ⬝ᵥ ξ) ∂P = a' r ⬝ᵥ a' s := fun r s => by
    rw [integral_dotProduct_mul_dotProduct_pi_gaussianReal, hdot2]
  have hEX := integral_comp_eq_integral_dotProduct (K := K) (P := P)
    (X := fun l (ξ : K ⊕ K' → ℝ) => a1 l ⬝ᵥ ξ) a (hasGaussianLaw_dotProduct_family a1) hX hcov1
    hFm
  have hEY := integral_comp_eq_integral_dotProduct (K := K') (P := P)
    (X := fun l (ξ : K ⊕ K' → ℝ) => a2 l ⬝ᵥ ξ) a' (hasGaussianLaw_dotProduct_family a2) hY hcov2
    hFm
  rw [← hEX, ← hEY]
  exact key

omit [Fintype κ] [DecidableEq κ] in
/-- **Two independent Gaussian blocks as an iterated integral.**  For linear forms of a pair of
independent blocks `(g, ξ)` of i.i.d. standard Gaussians, the iterated integral over `ξ` and then
`g` of a bounded measurable functional is its integral over the combined standard Gaussian vector
on `K ⊕ K'` through the combined linear forms. -/
theorem integral_integral_dotProduct_add [Finite κ] (a₁ : κ → K → ℝ) (a₂ : κ → K' → ℝ)
    {F : (κ → ℝ) → ℝ} (hFm : Measurable F) {B : ℝ} (hFb : ∀ y, |F y| ≤ B) :
    ∫ g, ∫ ξ, F (fun r => a₁ r ⬝ᵥ g + a₂ r ⬝ᵥ ξ) ∂(Measure.pi fun _ : K' => gaussianReal 0 1)
        ∂(Measure.pi fun _ : K => gaussianReal 0 1) =
      ∫ ζ, F (fun r => Sum.elim (a₁ r) (a₂ r) ⬝ᵥ ζ)
        ∂(Measure.pi fun _ : K ⊕ K' => gaussianReal 0 1) := by
  have hfam : HasGaussianLaw (fun (ζ : K ⊕ K' → ℝ) (r : κ) => Sum.elim (a₁ r) (a₂ r) ⬝ᵥ ζ)
      (Measure.pi fun _ : K ⊕ K' => gaussianReal 0 1) :=
    hasGaussianLaw_dotProduct_family fun r => Sum.elim (a₁ r) (a₂ r)
  have h := integral_comp_eq_integral_dotProduct_prod (A := κ)
    (X := fun r (ζ : K ⊕ K' → ℝ) => Sum.elim (a₁ r) (a₂ r) ⬝ᵥ ζ) a₁ a₂ hfam
    (fun r => integral_dotProduct_pi_gaussianReal _)
    (fun r s => by
      rw [integral_dotProduct_mul_dotProduct_pi_gaussianReal]
      simp [dotProduct, Fintype.sum_sum_type]) hFm
  have hint : Integrable (fun q : (K → ℝ) × (K' → ℝ) => F fun r => a₁ r ⬝ᵥ q.1 + a₂ r ⬝ᵥ q.2)
      ((Measure.pi fun _ : K => gaussianReal 0 1).prod
        (Measure.pi fun _ : K' => gaussianReal 0 1)) :=
    Integrable.of_bound ((hFm.comp (measurable_dotProduct_prod a₁ a₂)).aestronglyMeasurable) B
      (ae_of_all _ fun q => by rw [Real.norm_eq_abs]; exact hFb _)
  rw [h]
  exact (integral_prod _ hint).symm

end Gram

section Pair

/-- The product functional `y ↦ f (y 0) * g (y 1)` on `ℝ²` is `C²` when `f` and `g` are. -/
theorem contDiff_pair_mul {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 fun y : Fin 2 → ℝ => f (y 0) * g (y 1) :=
  (hf.comp (contDiff_apply ℝ ℝ 0)).mul (hg.comp (contDiff_apply ℝ ℝ 1))

/-- The partial derivatives of `y ↦ f (y 0) * g (y 1)`. -/
theorem fderiv_pair_mul {f g : ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (y : Fin 2 → ℝ) (l : Fin 2) :
    fderiv ℝ (fun y : Fin 2 → ℝ => f (y 0) * g (y 1)) y (Pi.single l 1) =
      if l = 0 then deriv f (y 0) * g (y 1) else f (y 0) * deriv g (y 1) := by
  have h0 : HasFDerivAt (fun y : Fin 2 → ℝ => f (y 0))
      (deriv f (y 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) y :=
    (hf (y 0)).hasDerivAt.comp_hasFDerivAt y (hasFDerivAt_apply 0 y)
  have h1 : HasFDerivAt (fun y : Fin 2 → ℝ => g (y 1))
      (deriv g (y 1) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) y :=
    (hg (y 1)).hasDerivAt.comp_hasFDerivAt y (hasFDerivAt_apply 1 y)
  rw [(h0.fun_mul h1).fderiv]
  fin_cases l <;> simp [mul_comm]

/-- The second partial derivatives of `y ↦ f (y 0) * g (y 1)`. -/
theorem fderiv_fderiv_pair_mul {f g : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (y : Fin 2 → ℝ) (k l : Fin 2) :
    fderiv ℝ (fun y => fderiv ℝ (fun y : Fin 2 → ℝ => f (y 0) * g (y 1)) y (Pi.single l 1)) y
        (Pi.single k 1) =
      if l = 0 then
        (if k = 0 then deriv (deriv f) (y 0) * g (y 1) else deriv f (y 0) * deriv g (y 1))
      else (if k = 0 then deriv f (y 0) * deriv g (y 1) else f (y 0) * deriv (deriv g) (y 1)) := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hg1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hf2 : Differentiable ℝ (deriv f) :=
    ((contDiff_succ_iff_deriv (n := 1)).1 hf).2.2.differentiable one_ne_zero
  have hg2 : Differentiable ℝ (deriv g) :=
    ((contDiff_succ_iff_deriv (n := 1)).1 hg).2.2.differentiable one_ne_zero
  have e : (fun y : Fin 2 → ℝ => fderiv ℝ (fun y : Fin 2 → ℝ => f (y 0) * g (y 1)) y
      (Pi.single l 1)) = fun y => if l = 0 then deriv f (y 0) * g (y 1) else
        f (y 0) * deriv g (y 1) := funext fun y => fderiv_pair_mul hf1 hg1 y l
  rw [e]
  fin_cases l
  · simp only [Fin.zero_eta, ite_true]
    rw [fderiv_pair_mul hf2 hg1 y k]
  · simp only [Fin.mk_one, one_ne_zero, ite_false]
    rw [fderiv_pair_mul hf1 hg2 y k]

variable {K K' : Type*} [Fintype K] [Fintype K']

/-- **Two linear forms of a Gaussian vector (Talagrand, §1.5).**  For `f ∈ C²` with bounds
`|f| ≤ M₀`, `|f'| ≤ M₁`, `|f''| ≤ M₂` and standard Gaussian vectors `ξ`, `ξ'`,
`|𝔼 f (u' ⬝ᵥ ξ') f (v' ⬝ᵥ ξ') - 𝔼 f (u ⬝ᵥ ξ) f (v ⬝ᵥ ξ)| ≤
  M₁² |u' ⬝ᵥ v' - u ⬝ᵥ v| + ½ M₀ M₂ (|u' ⬝ᵥ u' - u ⬝ᵥ u| + |v' ⬝ᵥ v' - v ⬝ᵥ v|)`. -/
theorem abs_integral_mul_sub_le (u v : K → ℝ) (u' v' : K' → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {M0 M1 M2 : ℝ} (h0 : ∀ x, |f x| ≤ M0) (h1 : ∀ x, |deriv f x| ≤ M1)
    (h2 : ∀ x, |deriv (deriv f) x| ≤ M2) :
    |∫ ξ', f (u' ⬝ᵥ ξ') * f (v' ⬝ᵥ ξ') ∂(Measure.pi fun _ : K' => gaussianReal 0 1) -
        ∫ ξ, f (u ⬝ᵥ ξ) * f (v ⬝ᵥ ξ) ∂(Measure.pi fun _ : K => gaussianReal 0 1)| ≤
      M1 ^ 2 * |u' ⬝ᵥ v' - u ⬝ᵥ v| +
        M0 * M2 / 2 * (|u' ⬝ᵥ u' - u ⬝ᵥ u| + |v' ⬝ᵥ v' - v ⬝ᵥ v|) := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hM0 : 0 ≤ M0 := (abs_nonneg _).trans (h0 0)
  have hM1 : 0 ≤ M1 := (abs_nonneg _).trans (h1 0)
  have hM2 : 0 ≤ M2 := (abs_nonneg _).trans (h2 0)
  have key := abs_integral_dotProduct_sub_le (κ := Fin 2) ![u, v] ![u', v']
    (F := fun y : Fin 2 → ℝ => f (y 0) * f (y 1)) (contDiff_pair_mul hf hf)
    (B := M0 * M0) (fun y => by
      rw [abs_mul]; exact mul_le_mul (h0 _) (h0 _) (abs_nonneg _) hM0)
    (D := fun l => M1 * M0) (fun l y => by
      rw [fderiv_pair_mul hf1 hf1]
      split_ifs
      · rw [abs_mul]; exact mul_le_mul (h1 _) (h0 _) (abs_nonneg _) hM1
      · rw [abs_mul, mul_comm]; exact mul_le_mul (h1 _) (h0 _) (abs_nonneg _) hM1)
    (D2 := fun k l => if k = l then M2 * M0 else M1 * M1) (fun k l y => by
      rw [fderiv_fderiv_pair_mul hf hf]
      fin_cases l <;> fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, one_ne_zero, ite_true,
        ite_false, abs_mul, zero_ne_one, Fin.isValue]
      · exact mul_le_mul (h2 _) (h0 _) (abs_nonneg _) hM2
      · exact mul_le_mul (h1 _) (h1 _) (abs_nonneg _) hM1
      · exact mul_le_mul (h1 _) (h1 _) (abs_nonneg _) hM1
      · rw [mul_comm]; exact mul_le_mul (h2 _) (h0 _) (abs_nonneg _) hM2)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, ite_true, ite_false,
    one_ne_zero, zero_ne_one, dotProduct_comm v u, dotProduct_comm v' u', Fin.isValue] at key
  refine key.trans (le_of_eq ?_)
  ring

end Pair

section LogSumExp

variable {α : Type*} [Fintype α] (h : α → ℝ)

/-- A partition function is positive. -/
lemma sum_exp_add_pos [Nonempty α] (y : α → ℝ) : 0 < ∑ a, Real.exp (y a + h a) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

lemma hasFDerivAt_sum_exp_add (y : α → ℝ) :
    HasFDerivAt (fun y : α → ℝ => ∑ a, Real.exp (y a + h a))
      (∑ a, Real.exp (y a + h a) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : α => ℝ) a) y :=
  HasFDerivAt.fun_sum fun a _ => ((hasFDerivAt_apply a y).add_const (h a)).exp

variable [DecidableEq α] [Nonempty α]

/-- **The partial derivatives of the free energy are the Gibbs weights:**
`∂_l log ∑ₐ exp (y a + h a) = exp (y l + h l) / ∑ₐ exp (y a + h a)`. -/
lemma fderiv_log_sum_exp_single (y : α → ℝ) (l : α) :
    fderiv ℝ (fun y : α → ℝ => Real.log (∑ a, Real.exp (y a + h a))) y (Pi.single l 1) =
      Real.exp (y l + h l) / ∑ a, Real.exp (y a + h a) := by
  rw [((hasFDerivAt_sum_exp_add h y).log (sum_exp_add_pos h y).ne').fderiv]
  simp [Pi.single_apply, div_eq_inv_mul]

/-- **The Hessian of the free energy is `diag w - w wᵀ`:** with the Gibbs weights
`w_l = exp (y l + h l) / ∑ₐ exp (y a + h a)`,
`∂_k ∂_l log ∑ₐ exp (y a + h a) = w_l (1[l = k] - w_k)`. -/
lemma fderiv_fderiv_log_sum_exp_single (y : α → ℝ) (l k : α) :
    fderiv ℝ (fun y : α → ℝ =>
      fderiv ℝ (fun y : α → ℝ => Real.log (∑ a, Real.exp (y a + h a))) y (Pi.single l 1)) y
      (Pi.single k 1) =
    Real.exp (y l + h l) / (∑ a, Real.exp (y a + h a)) *
      ((if l = k then 1 else 0) - Real.exp (y k + h k) / ∑ a, Real.exp (y a + h a)) := by
  have hZ := (sum_exp_add_pos h y).ne'
  have hfun : (fun y : α → ℝ =>
      fderiv ℝ (fun y : α → ℝ => Real.log (∑ a, Real.exp (y a + h a))) y (Pi.single l 1)) =
      fun y => Real.exp (y l + h l) * (∑ a, Real.exp (y a + h a))⁻¹ := by
    ext y
    rw [fderiv_log_sum_exp_single, div_eq_mul_inv]
  have hinv : HasFDerivAt (fun y : α → ℝ => (∑ a, Real.exp (y a + h a))⁻¹) _ y :=
    (hasDerivAt_inv hZ).comp_hasFDerivAt y (hasFDerivAt_sum_exp_add h y)
  have hexp : HasFDerivAt (fun y : α → ℝ => Real.exp (y l + h l))
      (Real.exp (y l + h l) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : α => ℝ) l) y :=
    ((hasFDerivAt_apply l y).add_const (h l)).exp
  rw [hfun, (hexp.fun_mul hinv).fderiv]
  simp [Pi.single_apply]
  split_ifs <;> field_simp <;> ring

/-- A `0/1` indicator minus a weight in `[0, 1]` has absolute value at most `1`. -/
theorem abs_ite_one_sub_le_one {p : Prop} [Decidable p] {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1) :
    |(if p then (1 : ℝ) else 0) - w| ≤ 1 := by
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [hw.1, hw.2]

omit [DecidableEq κ] in
/-- **Gaussian comparison for the free energy** (the smooth form of Slepian's inequality).
Let `(X, Y)` be a centered jointly Gaussian pair of fields on a finite set with `𝔼 X(a) Y(b) = 0`,
equal variances `𝔼 X(a)² = 𝔼 Y(a)²` and `𝔼 X(a) X(b) ≤ 𝔼 Y(a) Y(b)`.  Then for every bias `h`,
`𝔼 log ∑ₐ exp (Y(a) + h(a)) ≤ 𝔼 log ∑ₐ exp (X(a) + h(a))`.
This is `integral_comp_le_of_covariance_le` for `F = - log ∑ₐ exp (· + h)`, whose gradient is
`-w` and whose Hessian is `-(diag w - w wᵀ)` for the Gibbs weights `w`, so `∂_k ∂_l F = w_l w_k ≥ 0`
for `l ≠ k` (`fderiv_fderiv_log_sum_exp_single`). -/
theorem integral_log_sum_exp_le_of_covariance_le [Nonempty κ]
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (hX : ∀ a, ∫ ω, X a ω ∂P = 0) (hY : ∀ a, ∫ ω, Y a ω ∂P = 0)
    (h0 : ∀ a b, ∫ ω, X a ω * Y b ω ∂P = 0)
    (hdiag : ∀ a, ∫ ω, Y a ω * Y a ω ∂P = ∫ ω, X a ω * X a ω ∂P)
    (hle : ∀ a b, ∫ ω, X a ω * X b ω ∂P ≤ ∫ ω, Y a ω * Y b ω ∂P) (h : κ → ℝ) :
    ∫ ω, Real.log (∑ a, Real.exp (Y a ω + h a)) ∂P ≤
      ∫ ω, Real.log (∑ a, Real.exp (X a ω + h a)) ∂P := by
  classical
  have hF : ContDiff ℝ 2 (fun y : κ → ℝ => -Real.log (∑ a, Real.exp (y a + h a))) :=
    (ContDiff.log (ContDiff.sum fun a _ => ((contDiff_apply ℝ ℝ a).add contDiff_const).exp)
      fun y => (sum_exp_add_pos h y).ne').neg
  have hF1 : ∀ l y, fderiv ℝ (fun y : κ → ℝ => -Real.log (∑ a, Real.exp (y a + h a))) y
      (Pi.single l 1) = -(Real.exp (y l + h l) / ∑ a, Real.exp (y a + h a)) := fun l y => by
    rw [fderiv_fun_neg, neg_apply, fderiv_log_sum_exp_single]
  have hF2 : ∀ k l y, fderiv ℝ (fun y => fderiv ℝ (fun y : κ → ℝ =>
      -Real.log (∑ a, Real.exp (y a + h a))) y (Pi.single l 1)) y (Pi.single k 1) =
      -(Real.exp (y l + h l) / (∑ a, Real.exp (y a + h a)) *
        ((if l = k then 1 else 0) - Real.exp (y k + h k) / ∑ a, Real.exp (y a + h a))) :=
    fun k l y => by
    simp_rw [fderiv_fun_neg, neg_apply]
    rw [fderiv_fun_neg, neg_apply, fderiv_fderiv_log_sum_exp_single]
  have key := integral_comp_le_of_covariance_le hXY hX hY h0 hdiag
    (fun l k hlk => hle l k) (F := fun y : κ → ℝ => -Real.log (∑ a, Real.exp (y a + h a))) hF
    (fun l k y hlk => by
      rw [hF2]
      have hl := gibbsWeight_mem_Icc y h l
      have hk := gibbsWeight_mem_Icc y h k
      simp only [hlk, ite_false, zero_sub, mul_neg, neg_neg]
      exact mul_nonneg hl.1 hk.1)
    (C₀ := |Real.log (∑ a, Real.exp (h a))| + 1) (c₀ := 1) (fun y => by
      rw [abs_neg]
      refine (abs_log_sum_exp_le h y).trans ?_
      simpa only [one_mul] using Real.add_le_add_one_mul_exp (abs_nonneg _)
        (Finset.sum_nonneg fun a _ => abs_nonneg (y a)))
    (D := fun _ => 1) (c₁ := 0) (fun l y => by
      rw [hF1, abs_neg, abs_of_nonneg (gibbsWeight_mem_Icc y h l).1]
      simpa using (gibbsWeight_mem_Icc y h l).2)
    (D2 := fun _ _ => 1) (c₂ := 0) (fun k l y => by
      rw [hF2, abs_neg, abs_mul]
      have hl := gibbsWeight_mem_Icc y h l
      have hk := gibbsWeight_mem_Icc y h k
      rw [abs_of_nonneg hl.1]
      simpa using mul_le_mul hl.2 (abs_ite_one_sub_le_one hk) (abs_nonneg _) zero_le_one)
  simp only [integral_neg] at key
  exact neg_le_neg_iff.1 key

end LogSumExp

end SpinGlasses
