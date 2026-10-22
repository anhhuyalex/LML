/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityGaussian
public import LeanMachineLearning.SpinGlasses.SKReplicaSymmetricBound

/-!
# Gaussian inputs for the pair-perturbation interpolation (Talagrand Eq. 1.182)

On `(N+1)` spins the interpolation joins the independent pair block
`u_a = β (N (N+1))^{-1/2} ∑ g'_{ij} a_i a_j` (`s = 0`) to the scalar Gaussian
`v = (β / √2) q z` (`s = π / 2`).  Their joint law is Gaussian, they are centered and
uncorrelated, and the covariance difference is
`U(a, b) = (β² / 2) (q² - (S² - (N+1)) / (N (N+1)))`, `S = ∑ᵢ aᵢ bᵢ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- The pair block of the `(N+1)`-spin system and the scalar Gaussian form a jointly Gaussian
family under the product law. -/
theorem hasGaussianLaw_sk_pair_perturb_fields (N : ℕ) (β q : ℝ) :
    HasGaussianLaw
      (fun (ω : (FinPairs (N + 1) → ℝ) × ℝ)
        (s : (Fin (N + 1) → ℤˣ) ⊕ (Fin (N + 1) → ℤˣ)) =>
        Sum.elim
          (fun a => β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
            ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ))
          (fun _ => β * (Real.sqrt 2)⁻¹ * q * ω.2) s)
      ((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have h := hasGaussianLaw_linear_form_and_scalar_prod
    (c := fun (a : Fin (N + 1) → ℤˣ) (p : FinPairs (N + 1)) =>
      β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ * ((a p.val.1 : ℝ) * (a p.val.2 : ℝ)))
    (d := fun _ : Fin (N + 1) → ℤˣ => β * (Real.sqrt 2)⁻¹ * q)
  convert h using 1
  ext ω (σ | σ)
  · simp only [Sum.elim_inl, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp only [Sum.elim_inr]

/-- Centering of the pair block. -/
theorem integral_sk_pair_perturb_edge_field_eq_zero (N : ℕ) (β : ℝ) (a : Fin (N + 1) → ℤˣ) :
    (∫ ω : (FinPairs (N + 1) → ℝ) × ℝ,
      β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
        ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)
      ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod
        (gaussianReal 0 1))) = 0 :=
  integral_linear_form_prod_eq_zero (fun p : FinPairs (N + 1) =>
    β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ * ((a p.val.1 : ℝ) * (a p.val.2 : ℝ)))
    fun ω => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring

/-- Centering of the scalar Gaussian. -/
theorem integral_sk_pair_perturb_scalar_field_eq_zero (N : ℕ) (β q : ℝ) :
    (∫ ω : (FinPairs (N + 1) → ℝ) × ℝ, β * (Real.sqrt 2)⁻¹ * q * ω.2
      ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod
        (gaussianReal 0 1))) = 0 :=
  integral_scalar_prod_eq_zero (β * (Real.sqrt 2)⁻¹ * q) fun _ => rfl

/-- The pair block and the scalar Gaussian are uncorrelated. -/
theorem integral_sk_pair_perturb_edge_mul_scalar_eq_zero (N : ℕ) (β q : ℝ)
    (a : Fin (N + 1) → ℤˣ) :
    (∫ ω : (FinPairs (N + 1) → ℝ) × ℝ,
      (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
        ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) *
        (β * (Real.sqrt 2)⁻¹ * q * ω.2)
      ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod
        (gaussianReal 0 1))) = 0 :=
  integral_linear_form_mul_scalar_prod (fun p : FinPairs (N + 1) =>
    β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ * ((a p.val.1 : ℝ) * (a p.val.2 : ℝ)))
    (β * (Real.sqrt 2)⁻¹ * q)
    (fun ω => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    fun _ => rfl

/-- Covariance of the pair block at two configurations. -/
theorem integral_sk_pair_perturb_edge_field_mul (N : ℕ) (hN : 0 < N) (β : ℝ)
    (a b : Fin (N + 1) → ℤˣ) :
    (∫ ω : (FinPairs (N + 1) → ℝ) × ℝ,
      (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
        ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) *
      (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
        ∑ p : FinPairs (N + 1), ω.1 p * (b p.val.1 : ℝ) * (b p.val.2 : ℝ))
      ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod
        (gaussianReal 0 1))) =
      β ^ 2 * (((∑ i, (a i : ℝ) * (b i : ℝ)) ^ 2 - (N + 1 : ℝ)) /
        (2 * ((N : ℝ) * (N + 1)))) := by
  have hn : (0 : ℝ) < (N : ℝ) * (N + 1) := by positivity
  rw [integral_linear_form_mul_prod (fun p : FinPairs (N + 1) =>
      β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ * ((a p.val.1 : ℝ) * (a p.val.2 : ℝ)))
    (fun p : FinPairs (N + 1) =>
      β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ * ((b p.val.1 : ℝ) * (b p.val.2 : ℝ)))
    (fun ω => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun ω => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)]
  have hs : (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ =
      ((N : ℝ) * (N + 1))⁻¹ := inv_sqrt_mul_self _ hn.le
  have hsum := sum_sk_pair_coefficient_eq_overlap (N + 1) a b
  have hcoef : ∑ p : FinPairs (N + 1),
      β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ * ((a p.val.1 : ℝ) * (a p.val.2 : ℝ)) *
        (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ * ((b p.val.1 : ℝ) * (b p.val.2 : ℝ))) =
      β ^ 2 * ((N : ℝ) * (N + 1))⁻¹ * ∑ p : FinPairs (N + 1),
        (((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) * ((b p.val.1 : ℤ) : ℝ) *
          ((b p.val.2 : ℤ) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    linear_combination (β ^ 2 * ((a p.val.1 : ℝ) * (a p.val.2 : ℝ)) *
      ((b p.val.1 : ℝ) * (b p.val.2 : ℝ))) * hs
  rw [hcoef, hsum]
  simp only [dotProduct, Nat.cast_add, Nat.cast_one]
  field_simp

/-- Variance of the scalar Gaussian field. -/
theorem integral_sk_pair_perturb_scalar_field_mul (N : ℕ) (β q : ℝ) :
    (∫ ω : (FinPairs (N + 1) → ℝ) × ℝ,
      (β * (Real.sqrt 2)⁻¹ * q * ω.2) * (β * (Real.sqrt 2)⁻¹ * q * ω.2)
      ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod
        (gaussianReal 0 1))) = β ^ 2 * q ^ 2 / 2 := by
  rw [integral_scalar_mul_prod (β * (Real.sqrt 2)⁻¹ * q) (β * (Real.sqrt 2)⁻¹ * q)
    (fun _ => rfl) fun _ => rfl]
  have h2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 2⁻¹ := inv_sqrt_mul_self 2 (by norm_num)
  linear_combination (β * q) ^ 2 * h2

/-- **Covariance difference of the pair-perturbation fields.**  With
`Z(a, b) = ((∑ᵢ aᵢ bᵢ)² - (N+1)) / (N (N+1))`, the difference of the covariances of the
scalar and the pair field is `(β² / 2) (q² - Z(a, b))`. -/
theorem sk_pair_perturb_covariance_difference (N : ℕ) (hN : 0 < N) (β q : ℝ)
    (a b : Fin (N + 1) → ℤˣ) :
    β ^ 2 / 2 * (q ^ 2 - ((∑ i, (a i : ℝ) * (b i : ℝ)) ^ 2 - (N + 1 : ℝ)) /
        ((N : ℝ) * (N + 1))) =
      (∫ ω : (FinPairs (N + 1) → ℝ) × ℝ,
        (β * (Real.sqrt 2)⁻¹ * q * ω.2) * (β * (Real.sqrt 2)⁻¹ * q * ω.2)
        ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod
          (gaussianReal 0 1))) -
      ∫ ω : (FinPairs (N + 1) → ℝ) × ℝ,
        (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
          ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) *
        (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
          ∑ p : FinPairs (N + 1), ω.1 p * (b p.val.1 : ℝ) * (b p.val.2 : ℝ))
        ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod
          (gaussianReal 0 1)) := by
  rw [integral_sk_pair_perturb_scalar_field_mul, integral_sk_pair_perturb_edge_field_mul N hN]
  have hn : (N : ℝ) * (N + 1) ≠ 0 := by positivity
  field_simp

/-- Real-variable identity behind the overlap bound of Eq. (1.182): with the overlap `R` of the
first `N` coordinates and the last-spin product `ε`, the quantity
`Z = ((N R + ε)² - (N+1)) / (N (N+1))` equals `R² - (R - ε)² / (N+1)`. -/
theorem sk_pair_perturb_overlap_decomp (N : ℕ) (hN : 0 < N) (R ε : ℝ) (hε : ε ^ 2 = 1) :
    ((N * R + ε) ^ 2 - (N + 1 : ℝ)) / ((N : ℝ) * (N + 1)) =
      R ^ 2 - (R - ε) ^ 2 / (N + 1) := by
  have hn : (N : ℝ) ≠ 0 := by positivity
  field_simp
  linear_combination ((N : ℝ) + 1) * hε

/-- **Overlap bound of Eq. (1.182).**  `|Z - q²| ≤ 2 |R - q| + 4 / (N+1)`. -/
theorem abs_sk_pair_perturb_overlap_sub_le (N : ℕ) (hN : 0 < N) (R ε q : ℝ)
    (hε : ε ^ 2 = 1) (hR : |R| ≤ 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    |((N * R + ε) ^ 2 - (N + 1 : ℝ)) / ((N : ℝ) * (N + 1)) - q ^ 2| ≤
      2 * |R - q| + 4 / ((N : ℝ) + 1) := by
  rw [sk_pair_perturb_overlap_decomp N hN R ε hε]
  have hpos : (0 : ℝ) < N + 1 := by positivity
  have h1 : |R ^ 2 - q ^ 2| ≤ 2 * |R - q| := by
    rw [show R ^ 2 - q ^ 2 = (R - q) * (R + q) by ring, abs_mul]
    have : |R + q| ≤ 2 := by
      calc |R + q| ≤ |R| + |q| := abs_add_le _ _
        _ ≤ 1 + 1 := add_le_add hR (by rw [abs_of_nonneg hq.1]; exact hq.2)
        _ = 2 := by norm_num
    nlinarith [abs_nonneg (R - q)]
  have hεabs : |ε| = 1 :=
    (pow_eq_one_iff_of_nonneg (abs_nonneg ε) (two_ne_zero)).1 (by rw [sq_abs]; exact hε)
  have h2 : |(R - ε) ^ 2 / ((N : ℝ) + 1)| ≤ 4 / ((N : ℝ) + 1) := by
    rw [abs_div, abs_of_pos hpos, abs_pow]
    refine div_le_div_of_nonneg_right ?_ hpos.le
    have : |R - ε| ≤ 2 := by
      calc |R - ε| ≤ |R| + |ε| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add hR hεabs.le
        _ = 2 := by norm_num
    nlinarith [abs_nonneg (R - ε)]
  calc |R ^ 2 - (R - ε) ^ 2 / ((N : ℝ) + 1) - q ^ 2|
      = |(R ^ 2 - q ^ 2) - (R - ε) ^ 2 / ((N : ℝ) + 1)| := by ring_nf
    _ ≤ |R ^ 2 - q ^ 2| + |(R - ε) ^ 2 / ((N : ℝ) + 1)| := abs_sub _ _
    _ ≤ 2 * |R - q| + 4 / ((N : ℝ) + 1) := add_le_add h1 h2

end SpinGlasses
