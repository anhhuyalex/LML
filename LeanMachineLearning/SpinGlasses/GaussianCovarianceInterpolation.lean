/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

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

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.2.
* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, §1.5.
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

/-- **Derivative of a smooth Gaussian functional along the trigonometric path.**  For independent
centered Gaussian vectors `X`, `Y` (jointly Gaussian with `𝔼 X Y = 0`) and a `C²` functional `F`
with bounded value, gradient and Hessian, the derivative of `s ↦ 𝔼 F (cos s X + sin s Y)` at `t` is
`sin t cos t ∑_{l,k} (𝔼 Y_l Y_k - 𝔼 X_l X_k) 𝔼 ∂_k ∂_l F (Z_t)` for `Z_t = cos t X + sin t Y`. -/
theorem hasDerivAt_integral_comp_trig
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (hX : ∀ l, ∫ ω, X l ω ∂P = 0) (hY : ∀ l, ∫ ω, Y l ω ∂P = 0)
    (h0 : ∀ l k, ∫ ω, X l ω * Y k ω ∂P = 0) {F : (κ → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) {B : ℝ}
    (hF0 : ∀ y, |F y| ≤ B) {D : κ → ℝ} (hF1 : ∀ l y, |fderiv ℝ F y (Pi.single l 1)| ≤ D l)
    {D2 : κ → κ → ℝ}
    (hF2 : ∀ k l y, |fderiv ℝ (fun y => fderiv ℝ F y (Pi.single l 1)) y (Pi.single k 1)| ≤
      D2 k l) (t : ℝ) :
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
  have hD0 : ∀ l, 0 ≤ D l := fun l => (abs_nonneg _).trans (hF1 l 0)
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
    (C := ∑ l, D l) (c := 1) (fun s v => by
      have hS : (0 : ℝ) ≤ ∑ p, |v p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hlr : ∀ l, |v (Sum.inl l)| + |v (Sum.inr l)| ≤ ∑ p, |v p| := fun l => by
        rw [Fintype.sum_sum_type]
        exact add_le_add (Finset.single_le_sum (f := fun m => |v (Sum.inl m)|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ l)) (Finset.single_le_sum
          (f := fun m => |v (Sum.inr m)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ l))
      calc _ ≤ ∑ l, |(-Real.sin s * v (Sum.inl l) + Real.cos s * v (Sum.inr l)) *
              fderiv ℝ F (fun m => Real.cos s * v (Sum.inl m) + Real.sin s * v (Sum.inr m))
                (Pi.single l 1)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ l, (∑ p, |v p|) * D l := Finset.sum_le_sum fun l _ => by
            rw [abs_mul]
            exact mul_le_mul ((abs_neg_sin_mul_add_cos_mul_le _ _ s).trans (hlr l)) (hF1 l _)
              (abs_nonneg _) hS
        _ = (∑ l, D l) * ∑ p, |v p| := by rw [← Finset.mul_sum, mul_comm]
        _ ≤ (∑ l, D l) * Real.exp (1 * ∑ p, |v p|) :=
            mul_le_mul_of_nonneg_left (by
              rw [one_mul]; linarith [Real.add_one_le_exp (∑ p, |v p|)])
              (Finset.sum_nonneg fun l _ => hD0 l))
    (C₀ := B) (c₀ := 0) (fun v => by simpa using hF0 _)
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
      (F := fun y => fderiv ℝ F y (Pi.single l 1)) (hFl l) (C := D l) (c := 0)
      (fun y => by simpa using hF1 l y) (D := fun k => D2 k l) (d := fun _ => 0)
      (fun k y => by simpa using hF2 k l y)
    rw [h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_lincomb_mul_lincomb hXY h0 (-Real.sin t) (Real.cos t) (Real.cos t)
      (Real.sin t) l k]
    ring
  have hZm : AEMeasurable (fun ω m => Real.cos t * X m ω + Real.sin t * Y m ω) P :=
    aemeasurable_pi_iff.2 fun m => (((hXY.eval (Sum.inl m)).aemeasurable).const_mul _).add
      (((hXY.eval (Sum.inr m)).aemeasurable).const_mul _)
  have hint : ∀ l, Integrable (fun ω => (-Real.sin t * X l ω + Real.cos t * Y l ω) *
      fderiv ℝ F (fun m => Real.cos t * X m ω + Real.sin t * Y m ω) (Pi.single l 1)) P :=
    fun l => (((hXi l).const_mul _).add ((hYi l).const_mul _)).mul_bdd (c := D l)
      (((hF.continuous_fderiv (by norm_num)).clm_apply
        continuous_const).measurable.comp_aemeasurable hZm).aestronglyMeasurable
      (ae_of_all _ fun ω => by simpa using hF1 l _)
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
  have hd := fun s => hasDerivAt_integral_comp_trig hXY hX hY h0 hF hF0 hF1 hF2 s
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

end SpinGlasses
