/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiExp
public import LeanMachineLearning.SpinGlasses.Talagrand.GuerraReplicaSymmetric.SKFixedPoint
public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.SKReplicaConstant

/-!
# Hyperbolic moments of the replica fixed-point problem

Talagrand, *Spin Glasses* Vol. I, Section 1.13, Eq. (1.408): integrability, positivity and
continuity in `q` of the Gaussian integrals `𝔼 ch^n(β z √q + h)` and
`𝔼 ch^n(β z √q + h) th²(β z √q + h)`, and the bounds `0 ≤ R_n ≤ 1` for their ratio.
-/

@[expose] public section

open Finset Real MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators

namespace SpinGlasses

/-- For any `n, w, h`, `z ↦ ch^n(w z + h)` is integrable against the standard Gaussian measure. -/
theorem integrable_cosh_pow (n : ℕ) (w h : ℝ) :
    Integrable (fun z : ℝ => cosh (w * z + h) ^ n) (gaussianReal 0 1) := by
  have hz (ε : Fin n → ℤˣ) (z : ℝ) :
      Real.exp ((w * z + h) * ∑ l, ((ε l : ℤ) : ℝ)) =
        Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ)) *
          Real.exp ((w * ∑ l, ((ε l : ℤ) : ℝ)) * z) := by
    rw [← Real.exp_add]; congr 1; ring
  have hint_term (ε : Fin n → ℤˣ) :
      Integrable (fun z : ℝ => Real.exp ((w * z + h) * ∑ l, ((ε l : ℤ) : ℝ)))
        (gaussianReal 0 1) := by
    simp_rw [hz ε]
    exact (integrable_exp_mul_gaussianReal _).const_mul _
  have hint_sum : Integrable (fun z : ℝ => ∑ ε : Fin n → ℤˣ,
      Real.exp ((w * z + h) * ∑ l, ((ε l : ℤ) : ℝ))) (gaussianReal 0 1) :=
    integrable_finsetSum _ fun ε _ => hint_term ε
  have heq (z : ℝ) : (∑ ε : Fin n → ℤˣ,
      Real.exp ((w * z + h) * ∑ l, ((ε l : ℤ) : ℝ))) =
        (2 : ℝ) ^ n * cosh (w * z + h) ^ n := by
    rw [sum_exp_h_mul_spin (w * z + h), mul_pow]
  simp_rw [heq] at hint_sum
  have h2n : (2 : ℝ) ^ n ≠ 0 := (pow_pos two_pos n).ne'
  have := hint_sum.const_mul ((2 : ℝ) ^ n)⁻¹
  simp_rw [← mul_assoc, inv_mul_cancel₀ h2n, one_mul] at this
  exact this

/-- `ch^n x · th² x ≤ ch^n x`, since `th² ≤ 1`. -/
lemma cosh_pow_mul_tanh_sq_le (n : ℕ) (x : ℝ) : cosh x ^ n * tanh x ^ 2 ≤ cosh x ^ n := by
  calc cosh x ^ n * tanh x ^ 2
    _ ≤ cosh x ^ n * 1 :=
      mul_le_mul_of_nonneg_left ((Real.tanh_sq_lt_one _).le) (pow_nonneg (Real.cosh_pos _).le _)
    _ = cosh x ^ n := mul_one _

/-- For any `n, w, h`, `z ↦ ch^n(w z + h) th²(w z + h)` is integrable against the standard
Gaussian. -/
theorem integrable_cosh_pow_mul_tanh_sq (n : ℕ) (w h : ℝ) :
    Integrable (fun z : ℝ => cosh (w * z + h) ^ n * tanh (w * z + h) ^ 2)
      (gaussianReal 0 1) := by
  refine (integrable_cosh_pow n w h).mono' ?_ (Eventually.of_forall fun z => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    exact (Real.continuous_cosh.comp (by fun_prop)).pow n |>.mul
      ((Real.continuous_tanh.comp (by fun_prop)).pow 2)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (Real.cosh_pos _).le _),
      abs_of_nonneg (sq_nonneg _)]
    exact cosh_pow_mul_tanh_sq_le n _

/-- Positivity of the replicated cosh expectation: `0 < 𝔼 ch^n(w z + h)`. -/
theorem integral_cosh_pow_pos (n : ℕ) (w h : ℝ) :
    0 < ∫ z : ℝ, cosh (w * z + h) ^ n ∂(gaussianReal 0 1) := by
  have hone : (1 : ℝ) ≤ ∫ z : ℝ, cosh (w * z + h) ^ n ∂(gaussianReal 0 1) := by
    have h1 : (1 : ℝ) = ∫ _ : ℝ, (1 : ℝ) ∂(gaussianReal 0 1) := by
      rw [integral_const, probReal_univ, smul_eq_mul, mul_one]
    rw [h1]
    refine integral_mono (integrable_const 1) (integrable_cosh_pow n w h) fun z => ?_
    exact one_le_pow₀ (Real.one_le_cosh _)
  linarith

/-- Reordered integrability for `z ↦ ch^n(β z √q + h)`. -/
theorem integrable_cosh_pow_sk (n : ℕ) (β h q : ℝ) :
    Integrable (fun z : ℝ => cosh (β * z * Real.sqrt q + h) ^ n) (gaussianReal 0 1) := by
  have heq : (fun z : ℝ => cosh (β * z * Real.sqrt q + h) ^ n) =
      (fun z => cosh ((β * Real.sqrt q) * z + h) ^ n) := by
    ext z; congr 2; ring
  rw [heq]
  exact integrable_cosh_pow n (β * Real.sqrt q) h

/-- Reordered integrability for `z ↦ ch^n(β z √q + h) th²(β z √q + h)`. -/
theorem integrable_cosh_pow_mul_tanh_sq_sk (n : ℕ) (β h q : ℝ) :
    Integrable (fun z : ℝ => cosh (β * z * Real.sqrt q + h) ^ n *
      tanh (β * z * Real.sqrt q + h) ^ 2) (gaussianReal 0 1) := by
  have heq : (fun z : ℝ => cosh (β * z * Real.sqrt q + h) ^ n *
        tanh (β * z * Real.sqrt q + h) ^ 2) =
      (fun z => cosh ((β * Real.sqrt q) * z + h) ^ n *
        tanh ((β * Real.sqrt q) * z + h) ^ 2) := by
    ext z; congr 3 <;> ring
  rw [heq]
  exact integrable_cosh_pow_mul_tanh_sq n (β * Real.sqrt q) h

/-- Positivity of the replicated cosh expectation for `β z √q + h`. -/
theorem integral_cosh_pow_sk_pos (n : ℕ) (β h q : ℝ) :
    0 < ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1) := by
  have heq : (fun z : ℝ => cosh (β * z * Real.sqrt q + h) ^ n) =
      (fun z => cosh ((β * Real.sqrt q) * z + h) ^ n) := by
    ext z; congr 2; ring
  rw [heq]
  exact integral_cosh_pow_pos n (β * Real.sqrt q) h

/-- The replica fixed-point ratio is nonnegative. -/
theorem skReplica_ratio_nonneg (n : ℕ) (β h q : ℝ) :
    0 ≤ (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
          tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
        (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) := by
  have hnum : 0 ≤ ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
      tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) :=
    integral_nonneg fun z => mul_nonneg (pow_nonneg (Real.cosh_pos _).le _) (sq_nonneg _)
  have hden := integral_cosh_pow_sk_pos n β h q
  exact div_nonneg hnum hden.le

/-- The replica fixed-point ratio is at most 1. -/
theorem skReplica_ratio_le_one (n : ℕ) (β h q : ℝ) :
    (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
          tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
        (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) ≤ 1 := by
  have hden := integral_cosh_pow_sk_pos n β h q
  rw [div_le_one hden]
  refine integral_mono (integrable_cosh_pow_mul_tanh_sq_sk n β h q)
    (integrable_cosh_pow_sk n β h q) fun z => cosh_pow_mul_tanh_sq_le n _

/-- Domination of `ch^n(β z √q + h)` for `q ∈ [0, 1]` by an exponentially integrable function of
`z` that does not depend on `q`. Only `q ≤ 1` is needed. -/
lemma cosh_pow_le_exp_bound (n : ℕ) (β h z q : ℝ) (hq1 : q ≤ 1) :
    cosh (β * z * Real.sqrt q + h) ^ n ≤
      Real.exp (n * |h|) * (Real.exp (n * |β| * z) + Real.exp (-(n * |β|) * z)) := by
  have hsq : Real.sqrt q ≤ 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hq1
  have hx : |β * z * Real.sqrt q + h| ≤ |β| * |z| + |h| := by
    calc |β * z * Real.sqrt q + h|
      _ ≤ |β * z * Real.sqrt q| + |h| := abs_add_le _ _
      _ = |β| * |z| * Real.sqrt q + |h| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg q)]
      _ ≤ |β| * |z| * 1 + |h| := by gcongr
      _ = |β| * |z| + |h| := by rw [mul_one]
  have hch : cosh (β * z * Real.sqrt q + h) ≤ Real.exp (|β| * |z| + |h|) :=
    (Real.cosh_le_exp_abs _).trans (Real.exp_le_exp.2 hx)
  have hexp : Real.exp (n * |β| * |z|) ≤ Real.exp (n * |β| * z) + Real.exp (-(n * |β|) * z) := by
    have := Real.exp_add_mul_abs_le_add 0 (n * |β|) z
    rwa [zero_add, zero_add, zero_sub, ← neg_mul] at this
  calc cosh (β * z * Real.sqrt q + h) ^ n
    _ ≤ (Real.exp (|β| * |z| + |h|)) ^ n := pow_le_pow_left₀ (Real.cosh_pos _).le hch n
    _ = Real.exp (n * (|β| * |z| + |h|)) := by rw [← Real.exp_nat_mul]
    _ = Real.exp (n * |h|) * Real.exp (n * |β| * |z|) := by
      rw [show (n : ℝ) * (|β| * |z| + |h|) = (n : ℝ) * |h| + n * |β| * |z| by ring,
        Real.exp_add]
    _ ≤ Real.exp (n * |h|) * (Real.exp (n * |β| * z) + Real.exp (-(n * |β|) * z)) :=
      mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le

/-- The `q`-independent dominating function of `cosh_pow_le_exp_bound` is Gaussian integrable. -/
lemma integrable_cosh_pow_bound (n : ℕ) (β h : ℝ) :
    Integrable (fun z : ℝ => Real.exp (n * |h|) *
      (Real.exp (n * |β| * z) + Real.exp (-(n * |β|) * z))) (gaussianReal 0 1) :=
  ((integrable_exp_mul_gaussianReal (n * |β|)).add
    (integrable_exp_mul_gaussianReal (-(n * |β|)))).const_mul _

/-- Continuity on `[0, 1]` of the Gaussian integral of any continuous function of
`β z √q + h` that is dominated by `cosh ^ n`. -/
private lemma continuousOn_integral_comp_of_abs_le_cosh_pow (n : ℕ) (β h : ℝ) {F : ℝ → ℝ}
    (hF : Continuous F) (hb : ∀ x, |F x| ≤ cosh x ^ n) :
    ContinuousOn (fun q : ℝ => ∫ z : ℝ, F (β * z * Real.sqrt q + h) ∂(gaussianReal 0 1))
      (Set.Icc (0 : ℝ) 1) := by
  refine continuousOn_of_dominated (bound := fun z : ℝ => Real.exp (n * |h|) *
      (Real.exp (n * |β| * z) + Real.exp (-(n * |β|) * z))) (fun q _ => ?_)
    (fun q hq => ae_of_all _ fun z => ?_) (integrable_cosh_pow_bound n β h)
    (ae_of_all _ fun z => ?_)
  · exact (hF.comp (by fun_prop : Continuous fun z : ℝ =>
      β * z * Real.sqrt q + h)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact (hb _).trans (cosh_pow_le_exp_bound n β h z q hq.2)
  · exact (hF.comp (by fun_prop)).continuousOn

/-- Continuity of the denominator on `[0, 1]`. -/
lemma continuousOn_integral_cosh_pow (n : ℕ) (β h : ℝ) :
    ContinuousOn (fun q : ℝ => ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n
      ∂(gaussianReal 0 1)) (Set.Icc (0 : ℝ) 1) :=
  continuousOn_integral_comp_of_abs_le_cosh_pow n β h (F := fun x => cosh x ^ n)
    (Real.continuous_cosh.pow n) fun _ => (abs_of_nonneg (pow_nonneg (Real.cosh_pos _).le _)).le

/-- Continuity of the numerator on `[0, 1]`. -/
lemma continuousOn_integral_cosh_pow_mul_tanh_sq (n : ℕ) (β h : ℝ) :
    ContinuousOn (fun q : ℝ => ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
      tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) (Set.Icc (0 : ℝ) 1) :=
  continuousOn_integral_comp_of_abs_le_cosh_pow n β h (F := fun x => cosh x ^ n * tanh x ^ 2)
    ((Real.continuous_cosh.pow n).mul (Real.continuous_tanh.pow 2)) fun x => by
      rw [abs_mul, abs_of_nonneg (pow_nonneg (Real.cosh_pos _).le _),
        abs_of_nonneg (sq_nonneg _)]
      exact cosh_pow_mul_tanh_sq_le n x

/-- Continuity of the replica ratio map on `[0, 1]`. -/
lemma continuousOn_skReplica_ratio (n : ℕ) (β h : ℝ) :
    ContinuousOn (fun q : ℝ =>
      (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
            tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)))
      (Set.Icc (0 : ℝ) 1) := by
  refine ContinuousOn.div (continuousOn_integral_cosh_pow_mul_tanh_sq n β h)
    (continuousOn_integral_cosh_pow n β h) fun q _ => ?_
  exact (integral_cosh_pow_sk_pos n β h q).ne'

end SpinGlasses
