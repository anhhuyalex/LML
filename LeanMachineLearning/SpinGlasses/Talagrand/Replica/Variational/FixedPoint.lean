/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.SKReplicaTheorem
public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.SKReplicaConstant
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiExp
public import LeanMachineLearning.SpinGlasses.Talagrand.GuerraReplicaSymmetric.SKFixedPoint
public import LeanMachineLearning.SpinGlasses.Talagrand.GuerraReplicaSymmetric.SKFixedPointRS
public import LeanMachineLearning.SpinGlasses.Talagrand.GuerraReplicaSymmetric.SKFixedPointResidual
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.HypercubeProduct
public import LeanMachineLearning.SpinGlasses.Talagrand.DecoupledSystems.SKFirstMoment
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Fixed point of the replica-symmetric variational problem

Talagrand, *Spin Glasses* Vol. I, Section 1.13, Eq. (1.408).
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
    (integrable_cosh_pow_sk n β h q) fun z => ?_
  calc cosh (β * z * Real.sqrt q + h) ^ n * tanh (β * z * Real.sqrt q + h) ^ 2
    _ ≤ cosh (β * z * Real.sqrt q + h) ^ n * 1 :=
      mul_le_mul_of_nonneg_left ((Real.tanh_sq_lt_one _).le)
        (pow_nonneg (Real.cosh_pos _).le _)
    _ = cosh (β * z * Real.sqrt q + h) ^ n := mul_one _

/-- At `β = 0`, `Φ_n(q)` is constant and equals `n * log (cosh h)`. -/
theorem replica_phi_zero (n : ℕ) (h q : ℝ) :
    n * (0 : ℝ) ^ 2 * (1 - q) ^ 2 / 4 - (n : ℝ) ^ 2 * 0 ^ 2 * q ^ 2 / 4 +
        Real.log (∫ z : ℝ, cosh (0 * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) =
      n * Real.log (cosh h) := by
  have heq : (fun z : ℝ => cosh (0 * z * Real.sqrt q + h) ^ n) =
      (fun _ => cosh h ^ n) := by
    ext z; congr 2; ring
  simp_rw [heq]
  rw [integral_const, probReal_univ, smul_eq_mul, one_mul, Real.log_pow]
  ring

/-- At `β = 0`, the replica ratio is identically `th² h`. -/
theorem skReplica_ratio_zero (n : ℕ) (h q : ℝ) :
    (∫ z : ℝ, cosh (0 * z * Real.sqrt q + h) ^ n *
          tanh (0 * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
        (∫ z : ℝ, cosh (0 * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) =
      tanh h ^ 2 := by
  have heq1 : (fun z : ℝ => cosh (0 * z * Real.sqrt q + h) ^ n *
        tanh (0 * z * Real.sqrt q + h) ^ 2) =
      (fun _ => cosh h ^ n * tanh h ^ 2) := by
    ext z; congr 3 <;> ring
  have heq2 : (fun z : ℝ => cosh (0 * z * Real.sqrt q + h) ^ n) =
      (fun _ => cosh h ^ n) := by
    ext z; congr 2; ring
  simp_rw [heq1, heq2]
  rw [integral_const, integral_const, probReal_univ, smul_eq_mul, one_mul,
    smul_eq_mul, one_mul]
  have hpos : cosh h ^ n ≠ 0 := (pow_pos (Real.cosh_pos h) n).ne'
  exact mul_div_cancel_left₀ _ hpos

/-- **Talagrand's Eq. (1.408) for `β = 0`:** `q = th² h` is a maximizing fixed point. -/
theorem exists_skReplica_maximizer_fixedPoint_zero (n : ℕ) (h : ℝ) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧
      (∀ q' : ℝ, 0 ≤ q' →
        n * (0 : ℝ) ^ 2 * (1 - q') ^ 2 / 4 - (n : ℝ) ^ 2 * 0 ^ 2 * q' ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (0 * z * Real.sqrt q' + h) ^ n ∂(gaussianReal 0 1)) ≤
          n * (0 : ℝ) ^ 2 * (1 - q) ^ 2 / 4 - (n : ℝ) ^ 2 * 0 ^ 2 * q ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (0 * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))) ∧
      q = (∫ z : ℝ, cosh (0 * z * Real.sqrt q + h) ^ n *
            tanh (0 * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (0 * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) ∧
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * Real.log (∫ g' : FinPairs N → ℝ,
          (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N 0 h g' σ)) ^ n
            ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))) atTop
        (𝓝 (n * Real.log 2 + (n * (0 : ℝ) ^ 2 * (1 - q) ^ 2 / 4 -
          (n : ℝ) ^ 2 * 0 ^ 2 * q ^ 2 / 4 +
          Real.log (∫ z : ℝ, cosh (0 * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))))) := by
  refine ⟨tanh h ^ 2, sq_nonneg _, (Real.tanh_sq_lt_one _).le, fun q' _ => ?_, ?_, ?_⟩
  · rw [replica_phi_zero, replica_phi_zero]
  · rw [skReplica_ratio_zero]
  · have hlim := sk_replica_theorem_zero (n := n) h
    rw [replica_phi_zero (q := 0)] at hlim
    rw [replica_phi_zero (q := tanh h ^ 2)]
    exact hlim

/-- 1D Gaussian expectation of `ch(w z + h)`. -/
theorem integral_cosh_affine_gaussianReal (w h : ℝ) :
    ∫ z : ℝ, cosh (w * z + h) ∂(gaussianReal 0 1) = Real.exp (w ^ 2 / 2) * cosh h := by
  have hch (z : ℝ) : cosh (w * z + h) =
      (Real.exp h * Real.exp (w * z) + Real.exp (-h) * Real.exp (-w * z)) / 2 := by
    rw [cosh_eq, ← Real.exp_add, ← Real.exp_add]
    congr 1; congr 1
    · congr 1; ring
    · congr 1; ring
  simp_rw [hch]
  rw [integral_div, integral_add, integral_const_mul, integral_const_mul,
    integral_exp_mul_gaussianReal_zero_one w,
    integral_exp_mul_gaussianReal_zero_one (-w)]
  · rw [neg_sq, Real.cosh_eq]
    ring
  · exact (integrable_exp_mul_gaussianReal w).const_mul _
  · exact (integrable_exp_mul_gaussianReal (-w)).const_mul _

/-- For `n = 1`, `Φ_1(q)` is constant on `q ≥ 0` and equals `β² / 4 + log (cosh h)`. -/
theorem replica_phi_one_const (β h q : ℝ) (hq : 0 ≤ q) :
    1 * β ^ 2 * (1 - q) ^ 2 / 4 - (1 : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
        Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ 1 ∂(gaussianReal 0 1)) =
      β ^ 2 / 4 + Real.log (cosh h) := by
  have heq : (fun z : ℝ => cosh (β * z * Real.sqrt q + h) ^ 1) =
      (fun z => cosh ((β * Real.sqrt q) * z + h)) := by
    ext z; rw [pow_one]; congr 1; ring
  rw [heq, integral_cosh_affine_gaussianReal]
  have hpos1 : 0 < Real.exp ((β * Real.sqrt q) ^ 2 / 2) := Real.exp_pos _
  have hpos2 : 0 < cosh h := Real.cosh_pos h
  rw [Real.log_mul hpos1.ne' hpos2.ne', Real.log_exp, mul_pow, Real.sq_sqrt hq]
  ring

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

/-- Existence of a fixed point in `[0, 1]` for the replica ratio map. -/
theorem exists_skReplica_ratio_fixedPoint (n : ℕ) (β h : ℝ) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧
      q = (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
            tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) := by
  set R : ℝ → ℝ := fun q =>
    (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
          tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
        (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))
  have hcont : ContinuousOn (fun x => R x - x) (Set.Icc (0 : ℝ) 1) :=
    ((continuousOn_skReplica_ratio n β h).sub continuous_id.continuousOn)
  have h0 : 0 ≤ R 0 - 0 := by
    rw [sub_zero]; exact skReplica_ratio_nonneg n β h 0
  have h1 : R 1 - 1 ≤ 0 := by
    linarith [skReplica_ratio_le_one n β h 1]
  obtain ⟨q, hq, hq0⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hcont ⟨h1, h0⟩
  refine ⟨q, hq.1, hq.2, ?_⟩
  dsimp [R] at hq0
  linarith

/-- **Talagrand's Eq. (1.408) for `n = 1`:** any fixed point in `[0, 1]` is a maximizer. -/
theorem exists_skReplica_maximizer_fixedPoint_one (β h : ℝ) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧
      (∀ q' : ℝ, 0 ≤ q' →
        1 * β ^ 2 * (1 - q') ^ 2 / 4 - (1 : ℝ) ^ 2 * β ^ 2 * q' ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q' + h) ^ 1 ∂(gaussianReal 0 1)) ≤
          1 * β ^ 2 * (1 - q) ^ 2 / 4 - (1 : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ 1 ∂(gaussianReal 0 1))) ∧
      q = (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ 1 *
            tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ 1 ∂(gaussianReal 0 1)) ∧
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * Real.log (∫ g' : FinPairs N → ℝ,
          (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g' σ)) ^ 1
            ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))) atTop
        (𝓝 (1 * Real.log 2 + (1 * β ^ 2 * (1 - q) ^ 2 / 4 -
          (1 : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
          Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ 1 ∂(gaussianReal 0 1))))) := by
  obtain ⟨q, hq0, hq1, hqfix⟩ := exists_skReplica_ratio_fixedPoint 1 β h
  refine ⟨q, hq0, hq1, fun q' hq' => ?_, hqfix, ?_⟩
  · rw [replica_phi_one_const β h q' hq', replica_phi_one_const β h q hq0]
  · obtain ⟨q0, hq0_ge, -, hlim⟩ := sk_replica_theorem (n := 1) β h
    push_cast at hlim ⊢
    rw [replica_phi_one_const β h q0 hq0_ge] at hlim
    rw [replica_phi_one_const β h q hq0]
    exact hlim

/-- Finite replica partition sum $\sum_{\varepsilon} \exp(h \sum_l \varepsilon_l +
\frac{\beta^2 q}{2} (\sum_l \varepsilon_l)^2)$. -/
noncomputable def skReplicaSum (n : ℕ) (β h q : ℝ) : ℝ :=
  ∑ ε : Fin n → ℤˣ, Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
    β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2)

theorem skReplicaSum_def (n : ℕ) (β h q : ℝ) :
    skReplicaSum n β h q =
      ∑ ε : Fin n → ℤˣ, Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
        β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) := rfl

theorem skReplicaSum_pos (n : ℕ) (β h q : ℝ) : 0 < skReplicaSum n β h q := by
  rw [skReplicaSum_def]
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem skReplicaSum_eq_integral (n : ℕ) (β h q : ℝ) (hq : 0 ≤ q) :
    skReplicaSum n β h q = (2 : ℝ) ^ n *
      ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1) := by
  have hz (ε : Fin n → ℤˣ) (z : ℝ) :
      Real.exp ((β * z * Real.sqrt q + h) * ∑ l, ((ε l : ℤ) : ℝ)) =
        Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ)) *
          Real.exp ((β * Real.sqrt q * ∑ l, ((ε l : ℤ) : ℝ)) * z) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsq : (β * Real.sqrt q) ^ 2 = β ^ 2 * q := by
    rw [mul_pow, Real.sq_sqrt hq]
  have hterm (ε : Fin n → ℤˣ) :
      Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
        β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) =
      ∫ z : ℝ, Real.exp ((β * z * Real.sqrt q + h) * ∑ l, ((ε l : ℤ) : ℝ))
        ∂(gaussianReal 0 1) := by
    simp_rw [hz ε]
    rw [integral_const_mul, integral_exp_mul_gaussianReal_zero_one, mul_pow, hsq,
      ← Real.exp_add]
    congr 1
    ring
  rw [skReplicaSum_def]
  simp_rw [hterm]
  rw [← integral_finsetSum]
  · have heq (z : ℝ) : (∑ ε : Fin n → ℤˣ,
        Real.exp ((β * z * Real.sqrt q + h) * ∑ l, ((ε l : ℤ) : ℝ))) =
          (2 : ℝ) ^ n * cosh (β * z * Real.sqrt q + h) ^ n := by
      have := sum_exp_h_mul_spin (N := n) (β * z * Real.sqrt q + h)
      rw [mul_pow] at this
      exact this
    simp_rw [heq]
    rw [integral_const_mul]
  · intro ε _
    simp_rw [hz ε]
    exact (integrable_exp_mul_gaussianReal _).const_mul _

theorem sum_spin_pair_exp_eq (n : ℕ) (Y : ℝ) (a b : Fin n) (hab : a ≠ b) :
    ∑ ε : Fin n → ℤˣ, ((ε a : ℤ) : ℝ) * ((ε b : ℤ) : ℝ) *
        Real.exp (Y * ∑ l, ((ε l : ℤ) : ℝ)) =
      (2 * cosh Y) ^ n * tanh Y ^ 2 := by
  let f : Fin n → ℤˣ → ℝ := fun i s =>
    if i = a then ((s : ℤ) : ℝ) * Real.exp (((s : ℤ) : ℝ) * Y)
    else if i = b then ((s : ℤ) : ℝ) * Real.exp (((s : ℤ) : ℝ) * Y)
    else Real.exp (((s : ℤ) : ℝ) * Y)
  have ha : a ∈ Finset.univ := Finset.mem_univ a
  have hb : b ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hab.symm, Finset.mem_univ b⟩
  have hprod (ε : Fin n → ℤˣ) : ((ε a : ℤ) : ℝ) * ((ε b : ℤ) : ℝ) *
      Real.exp (Y * ∑ l, ((ε l : ℤ) : ℝ)) = ∏ i, f i (ε i) := by
    have h1 : Real.exp (Y * ∑ l, ((ε l : ℤ) : ℝ)) = ∏ i, Real.exp (((ε i : ℤ) : ℝ) * Y) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hfa : f a (ε a) = ((ε a : ℤ) : ℝ) * Real.exp (((ε a : ℤ) : ℝ) * Y) := by simp [f]
    have hfb : f b (ε b) = ((ε b : ℤ) : ℝ) * Real.exp (((ε b : ℤ) : ℝ) * Y) := by
      simp [f, hab.symm]
    have hrest : ∏ i ∈ (Finset.univ.erase a).erase b, f i (ε i) =
        ∏ i ∈ (Finset.univ.erase a).erase b, Real.exp (((ε i : ℤ) : ℝ) * Y) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hia : i ≠ a := (Finset.mem_erase.1 (Finset.mem_of_mem_erase hi)).1
      have hib : i ≠ b := (Finset.mem_erase.1 hi).1
      simp [f, hia, hib]
    rw [← Finset.mul_prod_erase Finset.univ (fun i => f i (ε i)) ha]
    rw [← Finset.mul_prod_erase (Finset.univ.erase a) (fun i => f i (ε i)) hb]
    rw [hfa, hfb, hrest, h1]
    rw [← Finset.mul_prod_erase Finset.univ _ ha]
    rw [← Finset.mul_prod_erase (Finset.univ.erase a) _ hb]
    ring
  simp_rw [hprod]
  rw [hypercube_sum_prod_eq_prod_add f]
  rw [← Finset.mul_prod_erase Finset.univ _ ha]
  rw [← Finset.mul_prod_erase (Finset.univ.erase a) _ hb]
  have hfa : f a 1 + f a (-1) = 2 * Real.sinh Y := by
    simp [f, Real.sinh_eq]; ring
  have hfb : f b 1 + f b (-1) = 2 * Real.sinh Y := by
    simp [f, hab.symm, Real.sinh_eq]; ring
  have hrest : ∏ i ∈ (Finset.univ.erase a).erase b, (f i 1 + f i (-1)) =
      ∏ i ∈ (Finset.univ.erase a).erase b, (2 * Real.cosh Y) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have hia : i ≠ a := (Finset.mem_erase.1 (Finset.mem_of_mem_erase hi)).1
    have hib : i ≠ b := (Finset.mem_erase.1 hi).1
    simp [f, hia, hib, Real.cosh_eq]
    ring
  rw [hfa, hfb, hrest, Finset.prod_const]
  have hcard : ((Finset.univ.erase a).erase b).card = n - 2 := by
    rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha,
      Finset.card_univ, Fintype.card_fin]
    omega
  rw [hcard]
  have hn2 : 2 ≤ n := by
    have := Fintype.card_fin n
    by_contra! hlt
    interval_cases n
    · exact hab (Subsingleton.elim a b)
    · exact hab (Subsingleton.elim a b)
  have hpow : (2 * Real.cosh Y) ^ n =
      (2 * Real.cosh Y) ^ 2 * (2 * Real.cosh Y) ^ (n - 2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  have htanh : Real.tanh Y = Real.sinh Y / Real.cosh Y := Real.tanh_eq_sinh_div_cosh Y
  rw [htanh, div_pow]
  have hch : Real.cosh Y ≠ 0 := (Real.cosh_pos Y).ne'
  have hmul : (2 * Real.cosh Y) ^ 2 * (Real.sinh Y ^ 2 / Real.cosh Y ^ 2) =
      4 * Real.sinh Y ^ 2 := by
    calc (2 * Real.cosh Y) ^ 2 * (Real.sinh Y ^ 2 / Real.cosh Y ^ 2)
      _ = (4 * Real.cosh Y ^ 2) * (Real.sinh Y ^ 2 / Real.cosh Y ^ 2) := by ring
      _ = 4 * (Real.cosh Y ^ 2 * (Real.sinh Y ^ 2 / Real.cosh Y ^ 2)) := by ring
      _ = 4 * Real.sinh Y ^ 2 := by
        rw [mul_div_cancel₀ _ (pow_ne_zero 2 hch)]
  calc (2 * Real.sinh Y) * ((2 * Real.sinh Y) * (2 * Real.cosh Y) ^ (n - 2))
    _ = 4 * Real.sinh Y ^ 2 * (2 * Real.cosh Y) ^ (n - 2) := by ring
    _ = (2 * Real.cosh Y) ^ 2 * (Real.sinh Y ^ 2 / Real.cosh Y ^ 2) *
          (2 * Real.cosh Y) ^ (n - 2) := by rw [hmul]
    _ = (2 * Real.cosh Y) ^ 2 * (2 * Real.cosh Y) ^ (n - 2) *
          (Real.sinh Y ^ 2 / Real.cosh Y ^ 2) := by ring

theorem sum_spin_sq_sub_n_exp_eq (n : ℕ) (Y : ℝ) :
    ∑ ε : Fin n → ℤˣ, ((∑ l, ((ε l : ℤ) : ℝ)) ^ 2 - (n : ℝ)) *
        Real.exp (Y * ∑ l, ((ε l : ℤ) : ℝ)) =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * cosh Y) ^ n * tanh Y ^ 2 := by
  have h1 (ε : Fin n → ℤˣ) : (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 - (n : ℝ) =
      ∑ l, ∑ l', if l = l' then (0 : ℝ) else ((ε l : ℤ) : ℝ) * ((ε l' : ℤ) : ℝ) := by
    have hsum : ∑ l, ((ε l : ℤ) : ℝ) ^ 2 = (n : ℝ) := by
      simp [units_cast_sq]
    have := sum_const_coupling (n := n) 1 (fun l => ((ε l : ℤ) : ℝ))
    simp only [one_mul] at this
    rw [← hsum, ← this]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
    by_cases h : l = l' <;> simp [h]
  simp_rw [h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hswap : (∑ x : Fin n, ∑ ε : Fin n → ℤˣ, ∑ l' : Fin n,
        (if x = l' then (0 : ℝ) else ((ε x : ℤ) : ℝ) * ((ε l' : ℤ) : ℝ)) *
          Real.exp (Y * ∑ l, ((ε l : ℤ) : ℝ))) =
      ∑ x : Fin n, ∑ l' : Fin n, ∑ ε : Fin n → ℤˣ,
        (if x = l' then (0 : ℝ) else ((ε x : ℤ) : ℝ) * ((ε l' : ℤ) : ℝ)) *
          Real.exp (Y * ∑ l, ((ε l : ℤ) : ℝ)) := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_comm
  rw [hswap]
  have hterm (l l' : Fin n) : (∑ ε : Fin n → ℤˣ,
        (if l = l' then (0 : ℝ) else ((ε l : ℤ) : ℝ) * ((ε l' : ℤ) : ℝ)) *
          Real.exp (Y * ∑ k, ((ε k : ℤ) : ℝ))) =
      (if l = l' then (0 : ℝ) else 1) *
        ((2 * cosh Y) ^ n * tanh Y ^ 2) := by
    by_cases hll : l = l'
    · subst hll; simp
    · simp only [hll, ite_false, one_mul]
      exact sum_spin_pair_exp_eq n Y l l' hll
  simp_rw [hterm, ← Finset.sum_mul]
  have hcard : ∑ l : Fin n, ∑ l' : Fin n, (if l = l' then (0 : ℝ) else 1) =
      (n : ℝ) * ((n : ℝ) - 1) := by
    have := sum_sq_const_coupling (n := n) 1
    simpa using this
  rw [hcard]
  ring

theorem sum_spin_sq_exp_integral (n : ℕ) (β h q : ℝ) (hq : 0 ≤ q) :
    ∑ ε : Fin n → ℤˣ, ((∑ l, ((ε l : ℤ) : ℝ)) ^ 2 - (n : ℝ)) *
        Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
          β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) =
      (n : ℝ) * ((n : ℝ) - 1) * (2 : ℝ) ^ n *
        ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
          tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) := by
  have hz (ε : Fin n → ℤˣ) (z : ℝ) :
      Real.exp ((β * z * Real.sqrt q + h) * ∑ l, ((ε l : ℤ) : ℝ)) =
        Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ)) *
          Real.exp ((β * Real.sqrt q * ∑ l, ((ε l : ℤ) : ℝ)) * z) := by
    rw [← Real.exp_add]; congr 1; ring
  have hsq : (β * Real.sqrt q) ^ 2 = β ^ 2 * q := by
    rw [mul_pow, Real.sq_sqrt hq]
  have hterm (ε : Fin n → ℤˣ) :
      Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
        β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) =
      ∫ z : ℝ, Real.exp ((β * z * Real.sqrt q + h) * ∑ l, ((ε l : ℤ) : ℝ))
        ∂(gaussianReal 0 1) := by
    simp_rw [hz ε]
    rw [integral_const_mul, integral_exp_mul_gaussianReal_zero_one, mul_pow, hsq,
      ← Real.exp_add]
    congr 1
    ring
  simp_rw [hterm, ← integral_const_mul]
  rw [← integral_finsetSum]
  · have heq (z : ℝ) : (∑ ε : Fin n → ℤˣ,
        ((∑ l, ((ε l : ℤ) : ℝ)) ^ 2 - (n : ℝ)) *
          Real.exp ((β * z * Real.sqrt q + h) * ∑ l, ((ε l : ℤ) : ℝ))) =
        (n : ℝ) * ((n : ℝ) - 1) * (2 : ℝ) ^ n *
          (cosh (β * z * Real.sqrt q + h) ^ n *
            tanh (β * z * Real.sqrt q + h) ^ 2) := by
      have := sum_spin_sq_sub_n_exp_eq n (Y := β * z * Real.sqrt q + h)
      rw [this]
      rw [mul_pow]
      ring
    simp_rw [heq]
  · intro ε _
    simp_rw [hz ε]
    exact ((integrable_exp_mul_gaussianReal _).const_mul _).const_mul _

theorem hasDerivAt_skReplicaSum (n : ℕ) (β h q : ℝ) :
    HasDerivAt (fun x => skReplicaSum n β h x)
      (∑ ε : Fin n → ℤˣ, Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
        β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) *
        (β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 / 2)) q := by
  simp only [skReplicaSum_def]
  refine HasDerivAt.fun_sum fun ε _ => ?_
  have hlin : HasDerivAt (fun x : ℝ => h * ∑ l, ((ε l : ℤ) : ℝ) +
      β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * x / 2)
    (β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 / 2) q := by
    have h1 : (fun x : ℝ => h * ∑ l, ((ε l : ℤ) : ℝ) +
        β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * x / 2) =
      (fun x : ℝ => (β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 / 2) * x +
        h * ∑ l, ((ε l : ℤ) : ℝ)) := by
      ext x; ring
    rw [h1]
    have := ((hasDerivAt_id q).const_mul (β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 / 2)).add_const
      (h * ∑ l, ((ε l : ℤ) : ℝ))
    simpa using this
  exact hlin.exp

theorem skReplicaSum_deriv_eq (n : ℕ) (β h q : ℝ) (hq : 0 ≤ q) :
    (∑ ε : Fin n → ℤˣ, Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
      β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) *
      (β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 / 2)) =
    (n : ℝ) * β ^ 2 / 2 * skReplicaSum n β h q +
      (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 * (2 : ℝ) ^ n *
        ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
          tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) := by
  have hsplit (ε : Fin n → ℤˣ) :
      (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 =
        (n : ℝ) + ((∑ l, ((ε l : ℤ) : ℝ)) ^ 2 - (n : ℝ)) := by ring
  have hsum : (∑ ε : Fin n → ℤˣ, Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
        β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) *
        (β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 / 2)) =
      β ^ 2 / 2 * ∑ ε : Fin n → ℤˣ, (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 *
        Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
          β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ε _ => by ring
  rw [hsum]
  have hsum2 : (∑ ε : Fin n → ℤˣ, (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 *
        Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
          β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2)) =
      (n : ℝ) * skReplicaSum n β h q +
        ∑ ε : Fin n → ℤˣ, ((∑ l, ((ε l : ℤ) : ℝ)) ^ 2 - (n : ℝ)) *
          Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
            β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) := by
    rw [skReplicaSum_def]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [hsplit ε]
    ring
  rw [hsum2, sum_spin_sq_exp_integral n β h q hq]
  ring

theorem hasDerivAt_log_skReplicaSum (n : ℕ) (β h q : ℝ) :
    HasDerivAt (fun x => Real.log (skReplicaSum n β h x))
      ((∑ ε : Fin n → ℤˣ, Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
        β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) *
        (β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 / 2)) / skReplicaSum n β h q) q :=
  (hasDerivAt_skReplicaSum n β h q).log (skReplicaSum_pos n β h q).ne'

theorem hasDerivAt_log_skReplicaSum_of_nonneg (n : ℕ) (β h q : ℝ) (hq : 0 ≤ q) :
    HasDerivAt (fun x => Real.log (skReplicaSum n β h x))
      ((n : ℝ) * β ^ 2 / 2 +
        (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 *
          ((∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
            tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)))) q := by
  have hlog := hasDerivAt_log_skReplicaSum n β h q
  have hderiv_eq := skReplicaSum_deriv_eq n β h q hq
  have hS_eq := skReplicaSum_eq_integral n β h q hq
  have h2n_ne : (2 : ℝ) ^ n ≠ 0 := (pow_pos two_pos n).ne'
  have hint_ne : (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) ≠ 0 :=
    (integral_cosh_pow_sk_pos n β h q).ne'
  have h_eq : ((∑ ε : Fin n → ℤˣ, Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
        β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2) *
        (β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 / 2)) / skReplicaSum n β h q) =
      ((n : ℝ) * β ^ 2 / 2 +
        (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 *
          ((∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
            tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)))) := by
    rw [hderiv_eq, hS_eq]
    have hprod_ne : (2 : ℝ) ^ n *
        (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) ≠ 0 :=
      mul_ne_zero h2n_ne hint_ne
    rw [add_div]
    congr 1
    · exact mul_div_cancel_right₀ _ hprod_ne
    · rw [mul_assoc ((n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2), mul_div_assoc]
      congr 1
      exact mul_div_mul_left _ _ h2n_ne
  exact hlog.congr_deriv h_eq

theorem hasDerivAt_skReplicaPoly (n : ℕ) (β q : ℝ) :
    HasDerivAt (fun x => (n : ℝ) * β ^ 2 * (1 - x) ^ 2 / 4 -
      (n : ℝ) ^ 2 * β ^ 2 * x ^ 2 / 4)
      (-((n : ℝ) * β ^ 2 / 2) - (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 * q) q := by
  have h1 : (fun x => (n : ℝ) * β ^ 2 * (1 - x) ^ 2 / 4 -
      (n : ℝ) ^ 2 * β ^ 2 * x ^ 2 / 4) =
    (fun x => ((n : ℝ) * β ^ 2 / 4) +
      (-((n : ℝ) * β ^ 2 / 2)) * x +
      ((n : ℝ) * (1 - (n : ℝ)) * β ^ 2 / 4) * x ^ 2) := by
    ext x; ring
  rw [h1]
  have hd1 := ((hasDerivAt_id q).const_mul (-((n : ℝ) * β ^ 2 / 2))).const_add
    ((n : ℝ) * β ^ 2 / 4)
  have hd2 : HasDerivAt (fun x => ((n : ℝ) * (1 - (n : ℝ)) * β ^ 2 / 4) * x ^ 2)
      (((n : ℝ) * (1 - (n : ℝ)) * β ^ 2 / 4) * (2 * q)) q := by
    simpa using ((hasDerivAt_id q).pow 2).const_mul ((n : ℝ) * (1 - (n : ℝ)) * β ^ 2 / 4)
  have hd := hd1.add hd2
  have hval : (-((n : ℝ) * β ^ 2 / 2) * 1 + ((n : ℝ) * (1 - (n : ℝ)) * β ^ 2 / 4) * (2 * q)) =
      (-((n : ℝ) * β ^ 2 / 2) - (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 * q) := by ring
  exact hd.congr_deriv hval

/-- Replica free-energy function $F_n(q)$ expressed in terms of the finite configuration
sum `skReplicaSum`. -/
noncomputable def skReplicaF (n : ℕ) (β h q : ℝ) : ℝ :=
  (n : ℝ) * β ^ 2 * (1 - q) ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
    Real.log (skReplicaSum n β h q) - (n : ℝ) * Real.log 2

theorem skReplicaF_def (n : ℕ) (β h q : ℝ) :
    skReplicaF n β h q =
      (n : ℝ) * β ^ 2 * (1 - q) ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
        Real.log (skReplicaSum n β h q) - (n : ℝ) * Real.log 2 := rfl

theorem skReplicaF_eq_phi (n : ℕ) (β h q : ℝ) (hq : 0 ≤ q) :
    skReplicaF n β h q =
      (n : ℝ) * β ^ 2 * (1 - q) ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
        Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) := by
  have hS := skReplicaSum_eq_integral n β h q hq
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos two_pos n
  have hint_pos := integral_cosh_pow_sk_pos n β h q
  dsimp [skReplicaF]
  rw [hS, Real.log_mul h2n_pos.ne' hint_pos.ne', Real.log_pow]
  ring

theorem hasDerivAt_skReplicaF (n : ℕ) (β h q : ℝ) (hq : 0 ≤ q) :
    HasDerivAt (skReplicaF n β h)
      ((n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 *
        (((∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
          tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
        (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))) - q)) q := by
  have hp := hasDerivAt_skReplicaPoly n β q
  have hl := hasDerivAt_log_skReplicaSum_of_nonneg n β h q hq
  have htot := (hp.add hl).sub_const ((n : ℝ) * Real.log 2)
  have hval : -((n : ℝ) * β ^ 2 / 2) - (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 * q +
      ((n : ℝ) * β ^ 2 / 2 +
        (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 *
          ((∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
            tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)))) =
      (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 *
        (((∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
          tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
        (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))) - q) := by ring
  have htot' := htot.congr_deriv hval
  exact htot'

lemma isLocalMax_of_forall_le {f : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hmax : ∀ x : ℝ, 0 ≤ x → f x ≤ f a) : IsLocalMax f a := by
  filter_upwards [Ioi_mem_nhds ha] with x hx
  exact hmax x hx.le

lemma exists_gt_of_hasDerivAt_zero_pos {f : ℝ → ℝ} {c : ℝ} (hd : HasDerivAt f c 0) (hc : 0 < c) :
    ∃ x : ℝ, 0 < x ∧ f 0 < f x := by
  have ht := (hd.tendsto_slope_zero.mono_left (nhdsGT_le_nhdsNE 0)).eventually (Ioi_mem_nhds hc)
  have h_both := ht.and self_mem_nhdsWithin
  rcases h_both.exists with ⟨x, hx_slope, hx_pos⟩
  refine ⟨x, hx_pos, ?_⟩
  simp only [zero_add, smul_eq_mul] at hx_slope
  exact sub_pos.1 ((mul_pos_iff_of_pos_left (inv_pos.2 hx_pos)).1 hx_slope)

theorem skReplica_ratio_neg_beta (n : ℕ) (β h q : ℝ) :
    (∫ z : ℝ, cosh (-β * z * Real.sqrt q + h) ^ n *
          tanh (-β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
        (∫ z : ℝ, cosh (-β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) =
      (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
          tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
        (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) := by
  have hnum : ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
        tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) =
      ∫ z : ℝ, cosh (-β * z * Real.sqrt q + h) ^ n *
        tanh (-β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) := by
    rw [← integral_neg_gaussianReal (fun z : ℝ => cosh (-β * z * Real.sqrt q + h) ^ n *
      tanh (-β * z * Real.sqrt q + h) ^ 2)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    beta_reduce
    rw [show -β * -z * Real.sqrt q = β * z * Real.sqrt q by ring]
  have hden : ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1) =
      ∫ z : ℝ, cosh (-β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1) := by
    rw [← integral_neg_gaussianReal (fun z : ℝ => cosh (-β * z * Real.sqrt q + h) ^ n)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    beta_reduce
    rw [show -β * -z * Real.sqrt q = β * z * Real.sqrt q by ring]
  rw [hnum, hden]

theorem skReplica_ratio_q_zero (n : ℕ) (β h : ℝ) :
    (∫ z : ℝ, cosh (β * z * Real.sqrt 0 + h) ^ n *
          tanh (β * z * Real.sqrt 0 + h) ^ 2 ∂(gaussianReal 0 1)) /
        (∫ z : ℝ, cosh (β * z * Real.sqrt 0 + h) ^ n ∂(gaussianReal 0 1)) =
      tanh h ^ 2 := by
  have heq1 : (fun z : ℝ => cosh (β * z * Real.sqrt 0 + h) ^ n *
        tanh (β * z * Real.sqrt 0 + h) ^ 2) =
      (fun _ => cosh h ^ n * tanh h ^ 2) := by
    ext z
    rw [Real.sqrt_zero, mul_zero, zero_add]
  have heq2 : (fun z : ℝ => cosh (β * z * Real.sqrt 0 + h) ^ n) =
      (fun _ => cosh h ^ n) := by
    ext z
    rw [Real.sqrt_zero, mul_zero, zero_add]
  simp_rw [heq1, heq2]
  rw [integral_const, integral_const, probReal_univ, smul_eq_mul, one_mul,
    smul_eq_mul, one_mul]
  have hpos : cosh h ^ n ≠ 0 := (pow_pos (Real.cosh_pos h) n).ne'
  exact mul_div_cancel_left₀ _ hpos

lemma exists_skReplica_maximizer_fixedPoint_pos (n : ℕ) (hn : 2 ≤ n) (β h : ℝ) (hβ : 0 < β) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧
      (∀ q' : ℝ, 0 ≤ q' →
        n * β ^ 2 * (1 - q') ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q' ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q' + h) ^ n ∂(gaussianReal 0 1)) ≤
          n * β ^ 2 * (1 - q) ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))) ∧
      q = (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
            tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) ∧
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * Real.log (∫ g' : FinPairs N → ℝ,
          (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g' σ)) ^ n
            ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))) atTop
        (𝓝 (n * Real.log 2 + (n * β ^ 2 * (1 - q) ^ 2 / 4 -
          (n : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
          Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))))) := by
  obtain ⟨q0, hq0_nonneg, hq0_max, hlim⟩ := sk_replica_theorem_pos (n := n) β h hβ
  have hF_max : ∀ q : ℝ, 0 ≤ q → skReplicaF n β h q ≤ skReplicaF n β h q0 := by
    intro q hq
    rw [skReplicaF_eq_phi n β h q hq, skReplicaF_eq_phi n β h q0 hq0_nonneg]
    exact hq0_max q hq
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hn_sub_pos : 0 < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hC_pos : 0 < (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 := by positivity
  by_cases hq0_pos : 0 < q0
  · have hloc : IsLocalMax (skReplicaF n β h) q0 := isLocalMax_of_forall_le hq0_pos hF_max
    have hder := hloc.hasDerivAt_eq_zero (hasDerivAt_skReplicaF n β h q0 hq0_nonneg)
    have hd_eq : (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 *
        (((∫ z : ℝ, cosh (β * z * Real.sqrt q0 + h) ^ n *
            tanh (β * z * Real.sqrt q0 + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt q0 + h) ^ n ∂(gaussianReal 0 1))) - q0) = 0 := by
      exact hder
    have h_sub_zero : ((∫ z : ℝ, cosh (β * z * Real.sqrt q0 + h) ^ n *
          tanh (β * z * Real.sqrt q0 + h) ^ 2 ∂(gaussianReal 0 1)) /
        (∫ z : ℝ, cosh (β * z * Real.sqrt q0 + h) ^ n ∂(gaussianReal 0 1))) - q0 = 0 := by
      cases mul_eq_zero.mp hd_eq with
      | inl h1 => linarith
      | inr h2 => exact h2
    have h_fix : q0 = (∫ z : ℝ, cosh (β * z * Real.sqrt q0 + h) ^ n *
          tanh (β * z * Real.sqrt q0 + h) ^ 2 ∂(gaussianReal 0 1)) /
        (∫ z : ℝ, cosh (β * z * Real.sqrt q0 + h) ^ n ∂(gaussianReal 0 1)) := by linarith
    refine ⟨q0, hq0_nonneg, ?_, hq0_max, h_fix, hlim⟩
    rw [h_fix]
    exact skReplica_ratio_le_one n β h q0
  · have hq0_eq : q0 = 0 := by linarith
    by_cases hh : h = 0
    · subst hh
      have hR0 : (∫ z : ℝ, cosh (β * z * Real.sqrt 0 + 0) ^ n *
            tanh (β * z * Real.sqrt 0 + 0) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt 0 + 0) ^ n ∂(gaussianReal 0 1)) = 0 := by
        rw [skReplica_ratio_q_zero, Real.tanh_zero, sq, mul_zero]
      have h_fix : q0 = (∫ z : ℝ, cosh (β * z * Real.sqrt q0 + 0) ^ n *
            tanh (β * z * Real.sqrt q0 + 0) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt q0 + 0) ^ n ∂(gaussianReal 0 1)) := by
        rw [hq0_eq, hR0]
      refine ⟨q0, hq0_nonneg, ?_, hq0_max, h_fix, hlim⟩
      rw [hq0_eq]
      norm_num
    · have hR0_pos : 0 < (∫ z : ℝ, cosh (β * z * Real.sqrt 0 + h) ^ n *
            tanh (β * z * Real.sqrt 0 + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt 0 + h) ^ n ∂(gaussianReal 0 1)) := by
        rw [skReplica_ratio_q_zero]
        have ht : Real.tanh h ≠ 0 := by
          intro hth
          rw [Real.tanh_eq_sinh_div_cosh, div_eq_zero_iff] at hth
          cases hth with
          | inl h1 =>
            rw [Real.sinh_eq_zero] at h1
            exact hh h1
          | inr h2 =>
            exact (Real.cosh_pos h).ne' h2
        exact sq_pos_of_ne_zero ht
      have hd0 := hasDerivAt_skReplicaF n β h 0 le_rfl
      have hd0_val : 0 < (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 *
          (((∫ z : ℝ, cosh (β * z * Real.sqrt 0 + h) ^ n *
              tanh (β * z * Real.sqrt 0 + h) ^ 2 ∂(gaussianReal 0 1)) /
            (∫ z : ℝ, cosh (β * z * Real.sqrt 0 + h) ^ n ∂(gaussianReal 0 1))) - 0) := by
        rw [sub_zero]
        exact mul_pos hC_pos hR0_pos
      have hd0' : HasDerivAt (skReplicaF n β h)
          ((n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 *
            (((∫ z : ℝ, cosh (β * z * Real.sqrt 0 + h) ^ n *
                tanh (β * z * Real.sqrt 0 + h) ^ 2 ∂(gaussianReal 0 1)) /
              (∫ z : ℝ, cosh (β * z * Real.sqrt 0 + h) ^ n ∂(gaussianReal 0 1))) - 0)) 0 := by
        exact hd0
      rcases exists_gt_of_hasDerivAt_zero_pos hd0' hd0_val with ⟨x, hx_pos, hx_lt⟩
      have hx_le := hF_max x hx_pos.le
      rw [hq0_eq] at hx_le
      have hfalse : False := by linarith
      exact hfalse.elim
/-- **Talagrand's Eq. (1.408).** For every integer `n ≥ 1` and all `β, h ∈ ℝ`, there exists a
maximizer `q ∈ [0, 1]` of `Φ_n` over `[0, ∞)` that satisfies the tilted fixed-point equation
`q = 𝔼 [ch^n(β z √q + h) th²(β z √q + h)] / 𝔼 [ch^n(β z √q + h)]`, and `N⁻¹ log 𝔼 Z_N^n` tends to
`n log 2 + Φ_n(q)`. -/
theorem exists_skReplica_maximizer_fixedPoint (n : ℕ) [NeZero n] (β h : ℝ) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧
      (∀ q' : ℝ, 0 ≤ q' →
        n * β ^ 2 * (1 - q') ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q' ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q' + h) ^ n ∂(gaussianReal 0 1)) ≤
          n * β ^ 2 * (1 - q) ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))) ∧
      q = (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
            tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) ∧
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * Real.log (∫ g' : FinPairs N → ℝ,
          (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g' σ)) ^ n
            ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))) atTop
        (𝓝 (n * Real.log 2 + (n * β ^ 2 * (1 - q) ^ 2 / 4 -
          (n : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
          Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))))) := by
  rcases eq_or_ne n 1 with rfl | hn_ne
  · obtain ⟨q, hq0, hq1, hqmax, hqfix, hlim⟩ := exists_skReplica_maximizer_fixedPoint_one β h
    push_cast
    exact ⟨q, hq0, hq1, hqmax, hqfix, hlim⟩
  · have hn2 : 2 ≤ n := by
      have : 0 < n := NeZero.pos n
      omega
    rcases lt_trichotomy β 0 with hneg | hzero | hpos
    · obtain ⟨q, hq0, hq1, hqmax, hqfix, hlim⟩ :=
        exists_skReplica_maximizer_fixedPoint_pos n hn2 (-β) h (neg_pos.2 hneg)
      refine ⟨q, hq0, hq1, fun q' hq' => ?_, ?_, ?_⟩
      · have := hqmax q' hq'
        rwa [replica_phi_neg_beta, replica_phi_neg_beta] at this
      · rw [← skReplica_ratio_neg_beta]
        exact hqfix
      · rw [replica_phi_neg_beta] at hlim
        simpa only [integral_partition_pow_neg_beta] using hlim
    · subst hzero
      exact exists_skReplica_maximizer_fixedPoint_zero n h
    · exact exists_skReplica_maximizer_fixedPoint_pos n hn2 β h hpos


end SpinGlasses
