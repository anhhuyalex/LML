/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Field
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.HypercubeProduct
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.JensenLog
public import LeanMachineLearning.SpinGlasses.Basic
public import LeanMachineLearning.SpinGlasses.GibbsMeasure
public import LeanMachineLearning.SpinGlasses.SKModel
public import LeanMachineLearning.SpinGlasses.SKDecoupled
public import LeanMachineLearning.SpinGlasses.GaussianIBP

/-!
# First Moment of the Partition Function & Temperature Derivative in the SK Model

This file formalizes the first-moment computation and the temperature derivative of the free
energy in the Sherrington–Kirkpatrick model
(Michel Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, 2010, Sections 1.2–1.3,
Eqs. (1.24)–(1.26) and (1.84)).

## Main Results

* `SpinGlasses.integral_exp_mul_gaussianReal_zero_one`: MGF of a standard Gaussian `𝒩(0, 1)`.
* `SpinGlasses.card_finPairs`: the number of pairs `i < j` in `Fin N` is `N.choose 2`.
* `SpinGlasses.integral_sk_partition_function_eq`: Exercise 1.2.3, Eq. (1.25),
  $$\frac{1}{N} \log \mathbb{E} Z_N = \frac{\beta^2}{4}\left(1 - \frac{1}{N}\right) +
    \log 2 + \log \cosh h.$$
* `SpinGlasses.sk_free_energy_le_first_moment`: Eq. (1.24) and (1.26), first-moment bound
  $$p_N(\beta, h) \le \frac{\beta^2}{4}\left(1 - \frac{1}{N}\right) + \log 2 + \log \cosh h.$$
* `SpinGlasses.hasDerivAt_sk_free_energy_beta`: Lemma 1.3.11, Eq. (1.84),
  temperature derivative of the expected free energy.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Springer, 2010, Chapter 1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Real Matrix

namespace SpinGlasses

/-- The type of ordered pairs `i < j` in `Fin N`. -/
abbrev FinPairs (N : ℕ) : Type :=
  {p : Fin N × Fin N // p.1 < p.2}

/-- The cardinality of `FinPairs N` is `N.choose 2`. -/
@[simp]
theorem card_finPairs (N : ℕ) : Fintype.card (FinPairs N) = N.choose 2 := by
  rw [Fintype.card_subtype]
  have h : (Finset.univ : Finset (Fin N × Fin N)) =
      (Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N)) :=
    Finset.univ_product_univ.symm
  rw [h]
  rw [Finset.card_product_filter_lt (α := Fin N) (s := Finset.univ)]
  simp only [Finset.card_univ, Fintype.card_fin]

/-- The real cardinality of `FinPairs N` is `N * (N - 1) / 2`. -/
theorem cast_card_finPairs (N : ℕ) :
    (Fintype.card (FinPairs N) : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
  rw [card_finPairs]
  exact Nat.cast_choose_two (K := ℝ) N

/-- Moment generating function of a standard Gaussian `𝒩(0, 1)`. -/
theorem integral_exp_mul_gaussianReal_zero_one (t : ℝ) :
    ∫ x, Real.exp (t * x) ∂(gaussianReal 0 1) = Real.exp (t ^ 2 / 2) := by
  have h := congr_fun (ProbabilityTheory.mgf_fun_id_gaussianReal (μ := 0) (v := 1)) t
  dsimp [ProbabilityTheory.mgf] at h
  rw [h]
  ring_nf

/-- Integrability of the exponential of a linear combination of independent standard Gaussians. -/
theorem integrable_exp_sum_mul_gaussianReal {E : Type*} [Fintype E] (c : E → ℝ) :
    Integrable (fun g : E → ℝ => Real.exp (∑ e, c e * g e))
      (Measure.pi fun _ : E => gaussianReal 0 1) := by
  have e : (fun g : E → ℝ => Real.exp (∑ e, c e * g e)) =
      fun g => ∏ e, Real.exp (c e * g e) := by
    ext g
    rw [Real.exp_sum]
  rw [e]
  exact MeasureTheory.Integrable.fintype_prod (fun e => integrable_exp_mul_gaussianReal (c e))

/-- Integral of the exponential of a linear combination of independent standard Gaussians. -/
theorem integral_exp_sum_mul_gaussianReal {E : Type*} [Fintype E] (c : E → ℝ) :
    ∫ g : E → ℝ, Real.exp (∑ e, c e * g e)
      ∂(Measure.pi fun _ : E => gaussianReal 0 1) =
    Real.exp (∑ e, c e ^ 2 / 2) := by
  simp_rw [Real.exp_sum]
  have h_int := MeasureTheory.integral_fintype_prod_eq_prod
    (E := fun _ : E => ℝ) (μ := fun _ : E => gaussianReal 0 1)
    (fun e (x : ℝ) => Real.exp (c e * x))
  rw [h_int]
  have h (e : E) : ∫ x, Real.exp (c e * x) ∂(gaussianReal 0 1) = Real.exp (c e ^ 2 / 2) :=
    integral_exp_mul_gaussianReal_zero_one (c e)
  rw [Finset.prod_congr rfl fun e _ => h e, ← Real.exp_sum]

/-- Integrability of the hyperbolic cosine of an affine combination of independent Gaussians. -/
theorem integrable_cosh_sum_mul_gaussianReal {E : Type*} [Fintype E] (c : E → ℝ) (m : ℝ) :
    Integrable (fun g : E → ℝ => Real.cosh (∑ e, c e * g e + m))
      (Measure.pi fun _ : E => gaussianReal 0 1) := by
  have heq : (fun g : E → ℝ => Real.cosh (∑ e, c e * g e + m)) =
      fun g => (Real.exp m * Real.exp (∑ e, c e * g e) +
        Real.exp (-m) * Real.exp (∑ e, (-c) e * g e)) / 2 := by
    ext g
    rw [Real.cosh_eq]
    have h1 : Real.exp (∑ e, c e * g e + m) = Real.exp m * Real.exp (∑ e, c e * g e) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-(∑ e, c e * g e + m)) = Real.exp (-m) * Real.exp (∑ e, (-c) e * g e) := by
      rw [← Real.exp_add]
      congr 1
      have : (∑ e, (-c) e * g e) = -∑ e, c e * g e := by
        simp only [Pi.neg_apply, neg_mul, ← Finset.sum_neg_distrib]
      linarith
    rw [h1, h2]
  rw [heq]
  exact (((integrable_exp_sum_mul_gaussianReal c).const_mul _).add
    ((integrable_exp_sum_mul_gaussianReal (-c)).const_mul _)).div_const 2

/-- Integral of the hyperbolic cosine of an affine combination of independent Gaussians. -/
theorem integral_cosh_sum_mul_gaussianReal {E : Type*} [Fintype E] (c : E → ℝ) (m : ℝ) :
    ∫ g : E → ℝ, Real.cosh (∑ e, c e * g e + m)
      ∂(Measure.pi fun _ : E => gaussianReal 0 1) =
    Real.cosh m * Real.exp (∑ e, c e ^ 2 / 2) := by
  have heq : (fun g : E → ℝ => Real.cosh (∑ e, c e * g e + m)) =
      fun g => (Real.exp m * Real.exp (∑ e, c e * g e) +
        Real.exp (-m) * Real.exp (∑ e, (-c) e * g e)) / 2 := by
    ext g
    rw [Real.cosh_eq]
    have h1 : Real.exp (∑ e, c e * g e + m) = Real.exp m * Real.exp (∑ e, c e * g e) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-(∑ e, c e * g e + m)) = Real.exp (-m) * Real.exp (∑ e, (-c) e * g e) := by
      rw [← Real.exp_add]
      congr 1
      have : (∑ e, (-c) e * g e) = -∑ e, c e * g e := by
        simp only [Pi.neg_apply, neg_mul, ← Finset.sum_neg_distrib]
      linarith
    rw [h1, h2]
  rw [heq, integral_div, integral_add]
  · rw [integral_const_mul, integral_const_mul,
        integral_exp_sum_mul_gaussianReal c, integral_exp_sum_mul_gaussianReal (-c)]
    have hsq : (∑ e, (-c) e ^ 2 / 2) = ∑ e, c e ^ 2 / 2 := by
      apply Finset.sum_congr rfl
      intro e _
      simp only [Pi.neg_apply, neg_sq]
    rw [hsq, Real.cosh_eq]
    ring
  · exact (integrable_exp_sum_mul_gaussianReal c).const_mul _
  · exact (integrable_exp_sum_mul_gaussianReal (-c)).const_mul _

theorem sk_first_moment_term_sq (N : ℕ) (β : ℝ) (σ : Fin N → ℤˣ) (p : FinPairs N) :
    ((Real.sqrt N)⁻¹ * β * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) ^ 2 / 2 =
      β ^ 2 / (2 * (N : ℝ)) := by
  have hsqrt : ((Real.sqrt N)⁻¹) ^ 2 = (N : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  calc ((Real.sqrt N)⁻¹ * β * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) ^ 2 / 2
    _ = (((Real.sqrt N)⁻¹) ^ 2 * β ^ 2 * (((σ p.val.1 : ℤ) : ℝ) ^ 2) *
          (((σ p.val.2 : ℤ) : ℝ) ^ 2)) / 2 := by ring
    _ = ((N : ℝ)⁻¹ * β ^ 2 * 1 * 1) / 2 := by rw [hsqrt, units_cast_sq, units_cast_sq]
    _ = β ^ 2 / (2 * (N : ℝ)) := by ring

theorem sum_sk_first_moment_term_sq {N : ℕ} (hN : 0 < N) (β : ℝ) (σ : Fin N → ℤˣ) :
    ∑ p : FinPairs N,
      ((Real.sqrt N)⁻¹ * β * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) ^ 2 / 2 =
    (N : ℝ) * (β ^ 2 / 4 * (1 - (N : ℝ)⁻¹)) := by
  simp_rw [sk_first_moment_term_sq]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, cast_card_finPairs]
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (ne_of_gt hN)
  field_simp
  ring

theorem sum_exp_h_mul_spin {N : ℕ} (h : ℝ) :
    ∑ σ : Fin N → ℤˣ, Real.exp (h * ∑ i, ((σ i : ℤ) : ℝ)) =
    (2 * Real.cosh h) ^ N := by
  have heq : (fun σ : Fin N → ℤˣ => Real.exp (h * ∑ i, ((σ i : ℤ) : ℝ))) =
      fun σ => Real.exp (∑ i, ((σ i : ℤ) : ℝ) * h) := by
    ext σ
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [heq, decoupled_partition_function_eq (fun _ => h)]
  rw [Fintype.card_fin, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow]

/-- The exact expectation of the SK partition function over Gaussian disorder `g` on pairs `i < j`
and constant external field `h`. -/
theorem integral_sk_partition_function {N : ℕ} (hN : 0 < N) (β h : ℝ) :
    ∫ g : FinPairs N → ℝ, ∑ σ : Fin N → ℤˣ,
      Real.exp ((Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((σ i : ℤ) : ℝ))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) =
    (2 * Real.cosh h) ^ N * Real.exp ((N : ℝ) * (β ^ 2 / 4 * (1 - (N : ℝ)⁻¹))) := by
  set P : Measure (FinPairs N → ℝ) := Measure.pi fun _ : FinPairs N => gaussianReal 0 1
  have h_int_sum : ∫ g : FinPairs N → ℝ, ∑ σ : Fin N → ℤˣ,
      Real.exp ((Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((σ i : ℤ) : ℝ)) ∂P =
      ∑ σ : Fin N → ℤˣ, Real.exp (h * ∑ i, ((σ i : ℤ) : ℝ)) *
        ∫ g : FinPairs N → ℝ, Real.exp (∑ p : FinPairs N,
          ((Real.sqrt N)⁻¹ * β * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) * g p) ∂P := by
    have h_swap : (fun (g : FinPairs N → ℝ) => ∑ σ : Fin N → ℤˣ,
        Real.exp ((Real.sqrt N)⁻¹ * β *
          (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
          h * ∑ i, ((σ i : ℤ) : ℝ))) =
        fun (g : FinPairs N → ℝ) => ∑ σ : Fin N → ℤˣ, Real.exp (h * ∑ i, ((σ i : ℤ) : ℝ)) *
          Real.exp (∑ p : FinPairs N,
            ((Real.sqrt N)⁻¹ * β * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) * g p) := by
      ext g
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [add_comm, Real.exp_add]
      congr 2
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [h_swap, integral_finsetSum Finset.univ]
    · refine Finset.sum_congr rfl fun σ _ => ?_
      rw [integral_const_mul]
    · intro σ _
      exact (integrable_exp_sum_mul_gaussianReal _).const_mul _
  rw [h_int_sum]
  have h_g_int (σ : Fin N → ℤˣ) : ∫ g : FinPairs N → ℝ, Real.exp (∑ p : FinPairs N,
      ((Real.sqrt N)⁻¹ * β * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) * g p) ∂P =
      Real.exp ((N : ℝ) * (β ^ 2 / 4 * (1 - (N : ℝ)⁻¹))) := by
    rw [integral_exp_sum_mul_gaussianReal]
    congr 1
    exact sum_sk_first_moment_term_sq hN β σ
  simp_rw [h_g_int, ← Finset.sum_mul, sum_exp_h_mul_spin]

/-- **First Moment of the SK Partition Function (Exercise 1.2.3, Eq. 1.25):**
The expectation of the SK partition function over Gaussian disorder `g` on pairs `i < j`
and constant external field `h`. -/
theorem integral_sk_partition_function_eq {N : ℕ} (hN : 0 < N) (β h : ℝ) :
    (N : ℝ)⁻¹ * Real.log (∫ g : FinPairs N → ℝ, ∑ σ : Fin N → ℤˣ,
      Real.exp ((Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((σ i : ℤ) : ℝ))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    β ^ 2 / 4 * (1 - (N : ℝ)⁻¹) + Real.log 2 + Real.log (Real.cosh h) := by
  rw [integral_sk_partition_function hN β h]
  have hcosh_pos : 0 < 2 * Real.cosh h := mul_pos two_pos (Real.cosh_pos h)
  have hpow_pos : 0 < (2 * Real.cosh h) ^ N := pow_pos hcosh_pos N
  rw [Real.log_mul hpow_pos.ne' (Real.exp_ne_zero _)]
  rw [Real.log_exp, Real.log_pow, Real.log_mul two_ne_zero (Real.cosh_pos _).ne']
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (ne_of_gt hN)
  field_simp
  ring

/-- **First-Moment Upper Bound on Expected Free Energy (Eqs. 1.24 & 1.26):**
By Jensen's inequality and the exact first moment computation,
$$p_N(\beta, h) \le \frac{\beta^2}{4}\left(1 - \frac{1}{N}\right) + \log 2 + \log \cosh h.$$ -/
theorem sk_free_energy_le_first_moment {N : ℕ} (hN : 0 < N) (β h : ℝ)
    (hlog_int : Integrable (fun g : FinPairs N → ℝ => Real.log (∑ σ : Fin N → ℤˣ,
      Real.exp ((Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((σ i : ℤ) : ℝ))))
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) :
    (N : ℝ)⁻¹ * ∫ g : FinPairs N → ℝ, Real.log (∑ σ : Fin N → ℤˣ,
      Real.exp ((Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((σ i : ℤ) : ℝ)))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
    β ^ 2 / 4 * (1 - (N : ℝ)⁻¹) + Real.log 2 + Real.log (Real.cosh h) := by
  set P : Measure (FinPairs N → ℝ) := Measure.pi fun _ : FinPairs N => gaussianReal 0 1
  set Z : (FinPairs N → ℝ) → ℝ := fun g => ∑ σ : Fin N → ℤˣ,
    Real.exp ((Real.sqrt N)⁻¹ * β *
      (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
      h * ∑ i, ((σ i : ℤ) : ℝ))
  have hZ_pos (g : FinPairs N → ℝ) : 0 < Z g := by
    dsimp [Z]
    exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hZ_int : Integrable Z P := by
    dsimp [Z]
    refine integrable_finsetSum Finset.univ fun σ _ => ?_
    have h_rw : (fun g : FinPairs N → ℝ => Real.exp ((Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((σ i : ℤ) : ℝ))) =
        fun g => Real.exp (h * ∑ i, ((σ i : ℤ) : ℝ)) * Real.exp (∑ p : FinPairs N,
          ((Real.sqrt N)⁻¹ * β * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) * g p) := by
      ext g
      rw [add_comm, Real.exp_add]
      congr 2
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [h_rw]
    exact (integrable_exp_sum_mul_gaussianReal _).const_mul _
  have h_jensen := integral_log_le_log_integral hZ_pos hZ_int hlog_int
  have hN_pos : 0 < (N : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 hN)
  have h_mul := mul_le_mul_of_nonneg_left h_jensen hN_pos.le
  rw [← integral_sk_partition_function_eq hN β h]
  exact h_mul

/-- **Derivative of the SK Log-Partition Function at Fixed Disorder:**
For any fixed disorder `g`, the derivative of `log Z_N(b)` with respect to `b` equals
the Gibbs average of the Hamiltonian `⟨u_σ⟩`. -/
theorem hasDerivAt_log_sum_exp_beta (N : ℕ) (g : FinPairs N → ℝ) (h : ℝ) (β : ℝ) :
    HasDerivAt (fun b => Real.log (∑ σ : Fin N → ℤˣ,
      Real.exp ((Real.sqrt N)⁻¹ * b *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((σ i : ℤ) : ℝ))))
      (∫ σ : Fin N → ℤˣ, ((Real.sqrt N)⁻¹ *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)))
        ∂(Measure.count.tilted fun σ => (Real.sqrt N)⁻¹ * β *
          (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
          h * ∑ i, ((σ i : ℤ) : ℝ))) β := by
  set u : (Fin N → ℤˣ) → ℝ := fun σ => (Real.sqrt N)⁻¹ *
    (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ))
  set C : (Fin N → ℤˣ) → ℝ := fun σ => h * ∑ i, ((σ i : ℤ) : ℝ)
  have hu (σ : Fin N → ℤˣ) : HasDerivAt (fun b => (Real.sqrt N)⁻¹ * b *
      (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) + C σ)
      (u σ) β := by
    have hlin : (fun b => (Real.sqrt N)⁻¹ * b *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) + C σ) =
        fun b => b * u σ + C σ := by
      ext b
      dsimp [u]
      ring
    rw [hlin]
    simpa using ((hasDerivAt_id β).mul_const (u σ)).add_const (C σ)
  have hexp (σ : Fin N → ℤˣ) : HasDerivAt (fun b => Real.exp ((Real.sqrt N)⁻¹ * b *
      (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) + C σ))
      (u σ * Real.exp (β * u σ + C σ)) β := by
    have h_eval : (Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) + C σ =
        β * u σ + C σ := by
      dsimp [u]
      ring
    have h_der := (hu σ).exp
    rw [h_eval] at h_der
    simpa [mul_comm] using h_der
  have hsum : HasDerivAt (fun b => ∑ σ : Fin N → ℤˣ, Real.exp ((Real.sqrt N)⁻¹ * b *
      (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) + C σ))
      (∑ σ : Fin N → ℤˣ, u σ * Real.exp (β * u σ + C σ)) β :=
    HasDerivAt.fun_sum fun σ _ => hexp σ
  have hZ_pos : 0 < ∑ σ : Fin N → ℤˣ, Real.exp ((Real.sqrt N)⁻¹ * β *
      (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) + C σ) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hlog := hsum.log hZ_pos.ne'
  have heq : (∑ σ : Fin N → ℤˣ, u σ * Real.exp (β * u σ + C σ)) /
      (∑ σ : Fin N → ℤˣ, Real.exp ((Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) + C σ)) =
      ∫ σ : Fin N → ℤˣ, u σ ∂(Measure.count.tilted fun σ => (Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) + C σ) := by
    have h_tilt := integral_count_tilted (fun σ => (Real.sqrt N)⁻¹ * β *
      (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) + C σ) u
    rw [h_tilt, Finset.sum_div]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have h_eq_w : Real.exp (β * u σ + C σ) =
        Real.exp ((Real.sqrt N)⁻¹ * β *
          (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) + C σ) := by
      congr 1
      dsimp [u]
      ring
    rw [h_eq_w]
    ring
  rw [heq] at hlog
  exact hlog

/-- The disorder Hamiltonian coordinate `u_σ` is measurable. -/
lemma measurable_disorder_u (N : ℕ) (σ : Fin N → ℤˣ) :
    Measurable (fun g : FinPairs N → ℝ => (Real.sqrt N)⁻¹ *
      (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ))) := by
  refine (Finset.measurable_sum Finset.univ fun p _ => ?_).const_mul _
  exact ((measurable_pi_apply p).mul_const _).mul_const _

/-- Each disorder coordinate `g p` is in `L²` under the product Gaussian measure. -/
lemma memLp_finPairs_entry (N : ℕ) (p : FinPairs N) :
    MemLp (fun g : FinPairs N → ℝ => g p) 2
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  have h_base : MemLp id (2 : ENNReal) (gaussianReal 0 1) := memLp_id_gaussianReal (2 : NNReal)
  exact h_base.comp_measurePreserving (measurePreserving_eval _ p)

/-- Absolute value of each disorder coordinate `|g p|` is integrable. -/
lemma integrable_finPairs_entry_abs (N : ℕ) (p : FinPairs N) :
    Integrable (fun g : FinPairs N → ℝ => |g p|)
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) :=
  (memLp_finPairs_entry N p).integrable (by norm_num) |>.abs

/-- **Temperature Derivative of the Expected Free Energy (Lemma 1.3.11, Eq. 1.84):**
The derivative of the expected free energy with respect to inverse temperature `β` equals
the expected Gibbs average of the normalized Hamiltonian:
`(d/dβ) p_N(β, h) = N⁻¹ 𝔼 ⟨u_σ⟩`. -/
theorem hasDerivAt_sk_free_energy_beta {N : ℕ} (hN : 0 < N) (h : ℝ) (β : ℝ)
    (hint : Integrable (fun g : FinPairs N → ℝ => Real.log (∑ σ : Fin N → ℤˣ,
      Real.exp ((Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((σ i : ℤ) : ℝ))))
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) :
    HasDerivAt (fun b => (N : ℝ)⁻¹ * ∫ g : FinPairs N → ℝ,
      Real.log (∑ σ : Fin N → ℤˣ, Real.exp ((Real.sqrt N)⁻¹ * b *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((σ i : ℤ) : ℝ)))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))
      ((N : ℝ)⁻¹ * ∫ g : FinPairs N → ℝ,
        ∫ σ : Fin N → ℤˣ, ((Real.sqrt N)⁻¹ *
          (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)))
        ∂(Measure.count.tilted fun σ => (Real.sqrt N)⁻¹ * β *
          (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
          h * ∑ i, ((σ i : ℤ) : ℝ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) β := by
  set P : Measure (FinPairs N → ℝ) := Measure.pi fun _ : FinPairs N => gaussianReal 0 1
  set u : (Fin N → ℤˣ) → (FinPairs N → ℝ) → ℝ := fun σ g => (Real.sqrt N)⁻¹ *
    (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ))
  set C : (Fin N → ℤˣ) → ℝ := fun σ => h * ∑ i, ((σ i : ℤ) : ℝ)
  set B : (FinPairs N → ℝ) → ℝ := fun g => (Real.sqrt N)⁻¹ * ∑ p : FinPairs N, |g p|
  have h_meas (σ : Fin N → ℤˣ) : Measurable (u σ) := measurable_disorder_u N σ
  have hB : Integrable B P := by
    dsimp [B]
    exact (integrable_finsetSum Finset.univ fun p _ =>
      integrable_finPairs_entry_abs N p).const_mul _
  have heq_b (g : FinPairs N → ℝ) :
      (Real.log (∑ σ : Fin N → ℤˣ, Real.exp ((Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((σ i : ℤ) : ℝ)))) =
      Real.log (∑ σ : Fin N → ℤˣ, Real.exp (β * u σ g + C σ)) := by
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    dsimp [u, C]
    ring
  have hint' : Integrable (fun g => Real.log (∑ σ, Real.exp (β * u σ g + C σ))) P :=
    hint.congr (ae_of_all _ fun g => heq_b g)
  have h_path := hasDerivAt_integral_log_sum_exp_path (μ := P) (t := β) (S := Set.univ)
    (f := fun b g σ => b * u σ g + C σ) (f' := fun _ g σ => u σ g) (B := B)
    Filter.univ_mem
    (fun s σ => (((h_meas σ).const_mul s).add_const (C σ)).aemeasurable)
    (fun σ => (h_meas σ).aemeasurable)
    hint'
    (fun g s _ σ => by simpa using ((hasDerivAt_id s).mul_const (u σ g)).add_const (C σ))
    hB
    (fun g s _ σ => by
      dsimp [u, B]
      have hpos : 0 ≤ (Real.sqrt N)⁻¹ := by positivity
      calc |(Real.sqrt N)⁻¹ * ∑ p : FinPairs N,
              g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)|
        _ = (Real.sqrt N)⁻¹ *
              |∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)| := by
          rw [abs_mul, abs_of_nonneg hpos]
        _ ≤ (Real.sqrt N)⁻¹ * ∑ p : FinPairs N, |g p| := by
          refine mul_le_mul_of_nonneg_left ?_ hpos
          calc |∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)|
            _ ≤ ∑ p : FinPairs N, |g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)| :=
              Finset.abs_sum_le_sum_abs _ _
            _ = ∑ p : FinPairs N, |g p| := by
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [abs_mul, abs_mul]
              rw [abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one, mul_one])
  have heq_f (b : ℝ) (g : FinPairs N → ℝ) (σ : Fin N → ℤˣ) :
      b * u σ g + C σ = (Real.sqrt N)⁻¹ * b *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((σ i : ℤ) : ℝ) := by
    dsimp [u, C]
    ring
  simp_rw [heq_f] at h_path
  exact h_path.const_mul (N : ℝ)⁻¹

end SpinGlasses
