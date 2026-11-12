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

/-!
# Fixed point of the replica-symmetric variational problem

Talagrand, *Spin Glasses* Vol. I, Section 1.13, Eq. (1.408).
-/

@[expose] public section

open Finset Real MeasureTheory ProbabilityTheory Filter Topology
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
    calc cosh (w * z + h) ^ n * tanh (w * z + h) ^ 2
      _ ≤ cosh (w * z + h) ^ n * 1 :=
        mul_le_mul_of_nonneg_left ((Real.tanh_sq_lt_one _).le)
          (pow_nonneg (Real.cosh_pos _).le _)
      _ = cosh (w * z + h) ^ n := mul_one _

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

/-- Upper bound on `cosh x` by `exp |x|`. -/
lemma cosh_le_exp_abs (x : ℝ) : cosh x ≤ Real.exp |x| := by
  rw [cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.2 (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.2 (neg_le_abs x)
  linarith

/-- Bound `exp (c |z|)` by `exp (c z) + exp (-c z)` for `c ≥ 0`. -/
lemma exp_abs_le_exp_add_exp (c : ℝ) (z : ℝ) :
    Real.exp (c * |z|) ≤ Real.exp (c * z) + Real.exp (-c * z) := by
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    linarith [Real.exp_pos (-c * z)]
  · rw [abs_of_nonpos hz]
    have : c * -z = -c * z := by ring
    rw [this]
    linarith [Real.exp_pos (c * z)]

/-- Continuity of the denominator on `[0, 1]`. -/
lemma continuousOn_integral_cosh_pow (n : ℕ) (β h : ℝ) :
    ContinuousOn (fun q : ℝ => ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n
      ∂(gaussianReal 0 1)) (Set.Icc (0 : ℝ) 1) := by
  set B : ℝ → ℝ := fun z => Real.exp (n * |h|) *
    (Real.exp (n * |β| * z) + Real.exp (-(n * |β|) * z))
  have hB : Integrable B (gaussianReal 0 1) :=
    ((integrable_exp_mul_gaussianReal (n * |β|)).add
      (integrable_exp_mul_gaussianReal (-(n * |β|)))).const_mul _
  refine continuousOn_of_dominated (bound := B) (fun q _ => ?_)
    (fun q hq => ae_of_all _ fun z => ?_) hB (ae_of_all _ fun z => ?_)
  · exact (Real.continuous_cosh.comp (by fun_prop : Continuous fun z : ℝ =>
      β * z * Real.sqrt q + h)).pow n |>.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Real.cosh_pos _).le _)]
    have hq0 : 0 ≤ q := hq.1
    have hq1 : q ≤ 1 := hq.2
    have hsq : Real.sqrt q ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hq1
    have hsq0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
    have hx : |β * z * Real.sqrt q + h| ≤ |β| * |z| + |h| := by
      calc |β * z * Real.sqrt q + h|
        _ ≤ |β * z * Real.sqrt q| + |h| := abs_add_le _ _
        _ = |β| * |z| * Real.sqrt q + |h| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hsq0]
        _ ≤ |β| * |z| * 1 + |h| := by
          gcongr
        _ = |β| * |z| + |h| := by rw [mul_one]
    have hch : cosh (β * z * Real.sqrt q + h) ≤ Real.exp (|β| * |z| + |h|) :=
      (cosh_le_exp_abs _).trans (Real.exp_le_exp.2 hx)
    calc cosh (β * z * Real.sqrt q + h) ^ n
      _ ≤ (Real.exp (|β| * |z| + |h|)) ^ n :=
        pow_le_pow_left₀ (Real.cosh_pos _).le hch n
      _ = Real.exp (n * (|β| * |z| + |h|)) := by
        rw [← Real.exp_nat_mul]
      _ = Real.exp (n * |h|) * Real.exp ((n * |β|) * |z|) := by
        rw [show (n : ℝ) * (|β| * |z| + |h|) =
          (n : ℝ) * |h| + ((n : ℝ) * |β|) * |z| by ring, Real.exp_add]
      _ ≤ Real.exp (n * |h|) * (Real.exp (n * |β| * z) + Real.exp (-(n * |β|) * z)) :=
        mul_le_mul_of_nonneg_left (exp_abs_le_exp_add_exp _ _) (Real.exp_pos _).le
  · refine Continuous.continuousOn ?_
    exact (Real.continuous_cosh.comp (by fun_prop)).pow n

/-- Continuity of the numerator on `[0, 1]`. -/
lemma continuousOn_integral_cosh_pow_mul_tanh_sq (n : ℕ) (β h : ℝ) :
    ContinuousOn (fun q : ℝ => ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
      tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) (Set.Icc (0 : ℝ) 1) := by
  set B : ℝ → ℝ := fun z => Real.exp (n * |h|) *
    (Real.exp (n * |β| * z) + Real.exp (-(n * |β|) * z))
  have hB : Integrable B (gaussianReal 0 1) :=
    ((integrable_exp_mul_gaussianReal (n * |β|)).add
      (integrable_exp_mul_gaussianReal (-(n * |β|)))).const_mul _
  refine continuousOn_of_dominated (bound := B) (fun q _ => ?_)
    (fun q hq => ae_of_all _ fun z => ?_) hB (ae_of_all _ fun z => ?_)
  · exact ((Real.continuous_cosh.comp (by fun_prop : Continuous fun z : ℝ =>
      β * z * Real.sqrt q + h)).pow n |>.mul
      ((Real.continuous_tanh.comp (by fun_prop : Continuous fun z : ℝ =>
      β * z * Real.sqrt q + h)).pow 2)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (Real.cosh_pos _).le _),
      abs_of_nonneg (sq_nonneg _)]
    have hq0 : 0 ≤ q := hq.1
    have hq1 : q ≤ 1 := hq.2
    have hsq : Real.sqrt q ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hq1
    have hsq0 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
    have hx : |β * z * Real.sqrt q + h| ≤ |β| * |z| + |h| := by
      calc |β * z * Real.sqrt q + h|
        _ ≤ |β * z * Real.sqrt q| + |h| := abs_add_le _ _
        _ = |β| * |z| * Real.sqrt q + |h| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hsq0]
        _ ≤ |β| * |z| * 1 + |h| := by
          gcongr
        _ = |β| * |z| + |h| := by rw [mul_one]
    have hch : cosh (β * z * Real.sqrt q + h) ≤ Real.exp (|β| * |z| + |h|) :=
      (cosh_le_exp_abs _).trans (Real.exp_le_exp.2 hx)
    have hpow : cosh (β * z * Real.sqrt q + h) ^ n ≤ B z := by
      calc cosh (β * z * Real.sqrt q + h) ^ n
        _ ≤ (Real.exp (|β| * |z| + |h|)) ^ n :=
          pow_le_pow_left₀ (Real.cosh_pos _).le hch n
        _ = Real.exp (n * (|β| * |z| + |h|)) := by
          rw [← Real.exp_nat_mul]
        _ = Real.exp (n * |h|) * Real.exp ((n * |β|) * |z|) := by
          rw [show (n : ℝ) * (|β| * |z| + |h|) =
            (n : ℝ) * |h| + ((n : ℝ) * |β|) * |z| by ring, Real.exp_add]
        _ ≤ Real.exp (n * |h|) * (Real.exp (n * |β| * z) + Real.exp (-(n * |β|) * z)) :=
          mul_le_mul_of_nonneg_left (exp_abs_le_exp_add_exp _ _) (Real.exp_pos _).le
    calc cosh (β * z * Real.sqrt q + h) ^ n * tanh (β * z * Real.sqrt q + h) ^ 2
      _ ≤ cosh (β * z * Real.sqrt q + h) ^ n * 1 :=
        mul_le_mul_of_nonneg_left ((Real.tanh_sq_lt_one _).le)
          (pow_nonneg (Real.cosh_pos _).le _)
      _ = cosh (β * z * Real.sqrt q + h) ^ n := mul_one _
      _ ≤ B z := hpow
  · refine Continuous.continuousOn ?_
    exact (Real.continuous_cosh.comp (by fun_prop)).pow n |>.mul
      ((Real.continuous_tanh.comp (by fun_prop)).pow 2)

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
    rw [replica_phi_one_const β h q0 hq0_ge] at hlim
    rw [replica_phi_one_const β h q hq0]
    exact hlim

end SpinGlasses
