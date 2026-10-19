/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiLinearForm
public import LeanMachineLearning.SpinGlasses.SKDecoupled
public import LeanMachineLearning.SpinGlasses.SKFirstMoment
import Mathlib.Algebra.BigOperators.Sym

/-!
# The Gaussian cavity field in Guerra's replica-symmetric interpolation

This module begins the smart-path calculation from Talagrand, *Spin Glasses*,
Section 1.3.  The independent cavity field has the explicit form
`β √q ∑ i, z i * σ i`, where the `z i` are independent standard Gaussians.
Its covariance is `β² q (σ ⬝ᵥ τ)`.  The result is deliberately stated for
arbitrary finite real vectors, rather than only hypercube configurations, so it
can be reused by spherical and relaxed spin models.

The remaining smart-path derivative and the replica-symmetric bound are not
formalized in this module yet.

## Main declaration

* `SpinGlasses.integral_decoupled_gaussian_field_mul`: covariance of Guerra's
  independent site-Gaussian field.
* `SpinGlasses.integral_sk_pair_field_mul`: covariance of the pair-indexed SK
  Gaussian field before its off-diagonal coefficient sum is simplified.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I,
  Section 1.3, Eq. (1.64).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real

namespace SpinGlasses

variable {ι : Type*} [Fintype ι]

/-- The covariance of two Gaussian linear forms, with the SK normalization made explicit.
This is stated for arbitrary coefficient vectors on any finite index type so that the same
calculation can be reused for pair, tensor, or cavity Gaussian fields. -/
theorem integral_normalized_gaussian_linear_form_mul {κ : Type*} [Fintype κ]
    (n β : ℝ) (hn : 0 ≤ n) (a b : κ → ℝ) :
    ∫ g : κ → ℝ,
      ((Real.sqrt n)⁻¹ * β * ∑ k, g k * a k) *
        ((Real.sqrt n)⁻¹ * β * ∑ k, g k * b k)
      ∂(Measure.pi fun _ : κ => gaussianReal 0 1) =
      n⁻¹ * β ^ 2 * (a ⬝ᵥ b) := by
  have ha (g : κ → ℝ) : ∑ k, g k * a k = a ⬝ᵥ g := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hb (g : κ → ℝ) : ∑ k, g k * b k = b ⬝ᵥ g := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  simp_rw [ha, hb]
  calc
    ∫ g : κ → ℝ, ((Real.sqrt n)⁻¹ * β * (a ⬝ᵥ g)) *
        ((Real.sqrt n)⁻¹ * β * (b ⬝ᵥ g))
        ∂(Measure.pi fun _ : κ => gaussianReal 0 1) =
        ((Real.sqrt n)⁻¹ * β) ^ 2 *
          ∫ g : κ → ℝ, (a ⬝ᵥ g) * (b ⬝ᵥ g)
            ∂(Measure.pi fun _ : κ => gaussianReal 0 1) := by
      have h_integrand :
          (fun g : κ → ℝ => ((Real.sqrt n)⁻¹ * β * (a ⬝ᵥ g)) *
            ((Real.sqrt n)⁻¹ * β * (b ⬝ᵥ g))) =
            fun g => ((Real.sqrt n)⁻¹ * β) ^ 2 * ((a ⬝ᵥ g) * (b ⬝ᵥ g)) := by
        ext g
        ring
      rw [h_integrand, integral_const_mul]
    _ = n⁻¹ * β ^ 2 * (a ⬝ᵥ b) := by
      rw [ProbabilityTheory.integral_dotProduct_mul_dotProduct_pi_gaussianReal]
      have hsquare : (Real.sqrt n)⁻¹ ^ 2 = n⁻¹ := by
        rw [inv_pow, Real.sq_sqrt hn]
      rw [mul_pow, hsquare]

/-- The covariance of the pair-indexed SK Gaussian field before the elementary off-diagonal
sum is rewritten in terms of the overlap. -/
theorem integral_sk_pair_field_mul {N : ℕ} (β : ℝ)
    (σ τ : Fin N → ℤˣ) :
    ∫ g : FinPairs N → ℝ,
      ((Real.sqrt N)⁻¹ * β *
        ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) *
        ((Real.sqrt N)⁻¹ * β *
          ∑ p : FinPairs N, g p * ((τ p.val.1 : ℤ) : ℝ) * ((τ p.val.2 : ℤ) : ℝ))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) =
      (N : ℝ)⁻¹ * β ^ 2 *
        ∑ p : FinPairs N,
          (((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) *
            ((τ p.val.1 : ℤ) : ℝ) * ((τ p.val.2 : ℤ) : ℝ) := by
  let a : FinPairs N → ℝ := fun p => ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)
  let b : FinPairs N → ℝ := fun p => ((τ p.val.1 : ℤ) : ℝ) * ((τ p.val.2 : ℤ) : ℝ)
  have hmain := integral_normalized_gaussian_linear_form_mul (N : ℝ) β
    (Nat.cast_nonneg N) a b
  simpa only [a, b, dotProduct, mul_assoc] using hmain

/-- The off-diagonal part of a quadratic sum is half the difference between the square of
the full sum and the sum of squares.  This purely finite identity is reusable independently
of the SK model. -/
theorem sum_finPairs_mul_eq_sub_sum_sq_div_two (N : ℕ) (x : Fin N → ℝ) :
    ∑ p : FinPairs N, x p.val.1 * x p.val.2 =
      ((∑ i, x i) ^ 2 - ∑ i, x i ^ 2) / 2 := by
  have hquadratic := QuadraticMap.map_sum (QuadraticMap.sq (R := ℝ))
    (Finset.univ : Finset (Fin N)) x
  rw [Finset.sum_sym2_filter_not_isDiag] at hquadratic
  have hpolar (p : Fin N × Fin N) :
      QuadraticMap.polarSym2 (QuadraticMap.sq (R := ℝ))
          (Sym2.map x (Sym2.mk p.1 p.2)) = 2 * x p.1 * x p.2 := by
    simp only [Sym2.map_mk, QuadraticMap.polarSym2_sym2Mk]
    change (x p.1 + x p.2) * (x p.1 + x p.2) -
      x p.1 * x p.1 - x p.2 * x p.2 = _
    ring
  simp_rw [hpolar] at hquadratic
  have hsubtype :
      ∑ p : FinPairs N, x p.val.1 * x p.val.2 =
        ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag with p.1 < p.2,
          x p.1 * x p.2 := by
    symm
    rw [Finset.sum_subtype]
    intro p
    constructor
    · exact fun hp => (Finset.mem_filter.mp hp).2
    · intro hp
      apply Finset.mem_filter.2
      refine ⟨Finset.mem_offDiag.2 ?_, hp⟩
      exact ⟨Finset.mem_univ _, Finset.mem_univ _, ne_of_lt hp⟩
  rw [hsubtype]
  have hquadratic' :
      (∑ i, x i) ^ 2 = ∑ i, x i ^ 2 +
        ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag with p.1 < p.2,
          2 * x p.1 * x p.2 := by
    simpa [QuadraticMap.sq, pow_two] using hquadratic
  have hdouble :
      ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag with p.1 < p.2,
        2 * x p.1 * x p.2 =
        2 * ∑ p ∈ (Finset.univ : Finset (Fin N)).offDiag with p.1 < p.2,
          x p.1 * x p.2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [hdouble] at hquadratic'
  linarith [hquadratic']

/-- For Ising configurations, the pair coefficient sum is the square of their overlap minus
the diagonal.  This is the finite combinatorial ingredient in the SK covariance formula. -/
theorem sum_sk_pair_coefficient_eq_overlap (N : ℕ) (σ τ : Fin N → ℤˣ) :
    ∑ p : FinPairs N,
      (((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) *
        ((τ p.val.1 : ℤ) : ℝ) * ((τ p.val.2 : ℤ) : ℝ) =
      (((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ)) ^ 2 - N) / 2 := by
  let x : Fin N → ℝ := fun i => ((σ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ)
  have hsum : ∑ i, x i =
      (fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ) := by
    rfl
  have hx_sq (i : Fin N) : x i ^ 2 = 1 := by
    dsimp [x]
    rw [mul_pow, units_cast_sq, units_cast_sq]
    norm_num
  have hsquares : ∑ i, x i ^ 2 = N := by
    simp_rw [hx_sq]
    simp
  have hbase := sum_finPairs_mul_eq_sub_sum_sq_div_two N x
  rw [hsum, hsquares] at hbase
  simpa only [x, Nat.cast_ofNat, mul_assoc, mul_left_comm, mul_comm] using hbase

/-- The covariance of the pair-indexed SK Gaussian field, expressed through the normalized
overlap of two Ising configurations. -/
theorem integral_sk_pair_field_mul_eq_overlap {N : ℕ} (hN : 0 < N) (β : ℝ)
    (σ τ : Fin N → ℤˣ) :
    ∫ g : FinPairs N → ℝ,
      ((Real.sqrt N)⁻¹ * β *
        ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) *
        ((Real.sqrt N)⁻¹ * β *
          ∑ p : FinPairs N, g p * ((τ p.val.1 : ℤ) : ℝ) * ((τ p.val.2 : ℤ) : ℝ))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) =
      (N : ℝ) * β ^ 2 / 2 *
        ((((N : ℝ)⁻¹ *
          ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ))) ^ 2 -
          (N : ℝ)⁻¹)) := by
  rw [integral_sk_pair_field_mul, sum_sk_pair_coefficient_eq_overlap]
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.ne_of_gt hN)
  field_simp

/-- The covariance of Guerra's independent site-Gaussian field.  This is the
decoupled contribution to the covariance difference in Eq. (1.64). -/
theorem integral_decoupled_gaussian_field_mul (β q : ℝ) (hq : 0 ≤ q)
    (σ τ : ι → ℝ) :
    ∫ z : ι → ℝ,
      (β * Real.sqrt q * ∑ i, z i * σ i) *
        (β * Real.sqrt q * ∑ i, z i * τ i)
      ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
      β ^ 2 * q * (σ ⬝ᵥ τ) := by
  have hσ (z : ι → ℝ) : ∑ i, z i * σ i = σ ⬝ᵥ z := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hτ (z : ι → ℝ) : ∑ i, z i * τ i = τ ⬝ᵥ z := by
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  simp_rw [hσ, hτ]
  calc
    ∫ z : ι → ℝ, (β * Real.sqrt q * (σ ⬝ᵥ z)) *
        (β * Real.sqrt q * (τ ⬝ᵥ z)) ∂(Measure.pi fun _ : ι => gaussianReal 0 1) =
        (β * Real.sqrt q) ^ 2 *
          ∫ z : ι → ℝ, (σ ⬝ᵥ z) * (τ ⬝ᵥ z)
            ∂(Measure.pi fun _ : ι => gaussianReal 0 1) := by
      have h_integrand :
          (fun z : ι → ℝ => (β * Real.sqrt q * (σ ⬝ᵥ z)) *
            (β * Real.sqrt q * (τ ⬝ᵥ z))) =
            fun z => (β * Real.sqrt q) ^ 2 * ((σ ⬝ᵥ z) * (τ ⬝ᵥ z)) := by
        ext z
        ring
      rw [h_integrand, integral_const_mul]
    _ = β ^ 2 * q * (σ ⬝ᵥ τ) := by
      rw [ProbabilityTheory.integral_dotProduct_mul_dotProduct_pi_gaussianReal,
        mul_pow, Real.sq_sqrt hq]

/-- The algebraic covariance difference used by Guerra's smart path.  The hypotheses are the
interacting and decoupled covariance computations; the conclusion is Eq. (1.64), written with
the conventional factor one half in the Gaussian interpolation covariance difference. -/
theorem smart_path_half_covariance_difference_eq [Nonempty ι] (β q : ℝ)
    (σ τ : ι → ℝ) (C D : ℝ)
    (hC : C = (Fintype.card ι : ℝ) * β ^ 2 / 2 *
      (((Fintype.card ι : ℝ)⁻¹ * (σ ⬝ᵥ τ)) ^ 2 - (Fintype.card ι : ℝ)⁻¹))
    (hD : D = β ^ 2 * q * (σ ⬝ᵥ τ)) :
    (Fintype.card ι : ℝ)⁻¹ * ((C - D) / 2) =
      β ^ 2 / 4 *
        (((Fintype.card ι : ℝ)⁻¹ * (σ ⬝ᵥ τ) - q) ^ 2 - q ^ 2 -
          (Fintype.card ι : ℝ)⁻¹) := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hdot : (σ ⬝ᵥ τ) = (Fintype.card ι : ℝ) *
      ((Fintype.card ι : ℝ)⁻¹ * (σ ⬝ᵥ τ)) := by
    calc
      σ ⬝ᵥ τ = 1 * (σ ⬝ᵥ τ) := by ring
      _ = ((Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)⁻¹) * (σ ⬝ᵥ τ) := by
        rw [mul_inv_cancel₀ hN]
      _ = (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ)⁻¹ * (σ ⬝ᵥ τ)) := by
        ring
  rw [hC, hD, hdot]
  field_simp
  ring

/-- Eq. (1.64) for the SK pair field and the independent Guerra cavity field.  The proof
reuses their separate Gaussian covariance calculations and leaves only the model-independent
algebraic assembly to `smart_path_half_covariance_difference_eq`. -/
theorem sk_smart_path_half_covariance_difference_eq {N : ℕ} (hN : 0 < N)
    (β q : ℝ) (hq : 0 ≤ q) (σ τ : Fin N → ℤˣ) :
    (N : ℝ)⁻¹ *
      (((∫ g : FinPairs N → ℝ,
          ((Real.sqrt N)⁻¹ * β *
            ∑ p : FinPairs N,
              g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) *
            ((Real.sqrt N)⁻¹ * β *
              ∑ p : FinPairs N,
                g p * ((τ p.val.1 : ℤ) : ℝ) * ((τ p.val.2 : ℤ) : ℝ))
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) -
        (∫ z : Fin N → ℝ,
          (β * Real.sqrt q * ∑ i, z i * ((σ i : ℤ) : ℝ)) *
            (β * Real.sqrt q * ∑ i, z i * ((τ i : ℤ) : ℝ))
          ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1))) / 2) =
      β ^ 2 / 4 *
        ((((N : ℝ)⁻¹ *
          ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ))) - q) ^ 2 -
          q ^ 2 - (N : ℝ)⁻¹) := by
  let _ : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [integral_sk_pair_field_mul_eq_overlap hN,
    integral_decoupled_gaussian_field_mul β q hq]
  simpa using smart_path_half_covariance_difference_eq β q
    (fun i => ((σ i : ℤ) : ℝ)) (fun i => ((τ i : ℤ) : ℝ)) _ _ rfl rfl

end SpinGlasses
