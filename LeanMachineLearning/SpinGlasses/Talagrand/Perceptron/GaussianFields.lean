/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianGram
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiLinearForm
public import LeanMachineLearning.SpinGlasses.Basic

/-!
# Gaussian fields of fixed spins in the binary perceptron

Talagrand, *Spin Glasses* Vol. I, Section 2.1.  The disorder is a family of independent
standard Gaussians `g k i`, `k < M`, `i < N`, and a fixed spin `σ : Fin N → ℤˣ` produces in the
column `k` the *field* `(√N)⁻¹ ∑ i, g k i * σ i`.  The book says the field is "of order one"; here
this is made exact: for a **fixed** deterministic spin the field is standard normal, the fields of
two fixed spins in one column are centered with covariance the overlap
`N⁻¹ ∑ i, σ i * τ i`, any finite family of them is jointly Gaussian with that Gram matrix (also
when the matrix is singular), and fields in distinct columns are independent.  Nothing is said
about spins that depend on the disorder, such as samples of a Gibbs measure.

The index `k` of the independent column is the outer one, which reverses the book's `g_{i,k}`.

## Main declarations

* `SpinGlasses.map_normalized_constraint_field_eq_gaussianReal`: a fixed-spin field is `𝒩(0, 1)`.
* `SpinGlasses.integral_normalized_constraint_field_mul_eq`: its covariance is the overlap.
* `SpinGlasses.map_toLp_normalized_constraint_fields_eq_multivariateGaussian`: the joint law of
  finitely many fixed-spin fields.
* `SpinGlasses.map_normalized_constraint_fields_eq_pi_gaussianReal`: the fields of one fixed spin
  in the `M` columns are i.i.d. standard normal.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SpinGlasses

variable {N : ℕ}

/-- Normalizing a spin vector by `(√N)⁻¹` turns the sum `∑ i, σ i * τ i` into the overlap. -/
private lemma normalized_spin_dotProduct (σ τ : Fin N → ℤˣ) :
    (fun i => (Real.sqrt N)⁻¹ * ((σ i : ℤ) : ℝ)) ⬝ᵥ (fun i => (Real.sqrt N)⁻¹ * ((τ i : ℤ) : ℝ)) =
      (Fintype.card (Fin N) : ℝ)⁻¹ *
        ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ)) := by
  have h : (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ = (N : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg N)]
  simp only [dotProduct, Finset.mul_sum, Fintype.card_fin]
  exact Finset.sum_congr rfl fun i _ => by rw [← h]; ring

/-- The normalized field of a fixed spin is the linear form with coefficients `(√N)⁻¹ σ i`. -/
private lemma normalized_field_eq_dotProduct (σ : Fin N → ℤˣ) (x : Fin N → ℝ) :
    (Real.sqrt N)⁻¹ * ∑ i, x i * ((σ i : ℤ) : ℝ) =
      (fun i => (Real.sqrt N)⁻¹ * ((σ i : ℤ) : ℝ)) ⬝ᵥ x := by
  simp only [dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The normalized coefficient vector of a spin has square sum one. -/
private lemma normalized_spin_dotProduct_self (hN : 0 < N) (σ : Fin N → ℤˣ) :
    (fun i => (Real.sqrt N)⁻¹ * ((σ i : ℤ) : ℝ)) ⬝ᵥ (fun i => (Real.sqrt N)⁻¹ * ((σ i : ℤ) : ℝ))
      = 1 := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  rw [normalized_spin_dotProduct]
  exact card_inv_mul_dotProduct_self_eq_one _ fun i => units_cast_sq _

/-- **The field of a fixed spin is standard normal.**  For a deterministic spin `σ` and a vector
`x` of i.i.d. standard Gaussians, `(√N)⁻¹ ∑ i, x i * σ i ∼ 𝒩(0, 1)`.  This requires `N ≥ 1`: for
`N = 0` the field is identically zero. -/
theorem map_normalized_constraint_field_eq_gaussianReal (hN : 0 < N) (σ : Fin N → ℤˣ) :
    Measure.map (fun x : Fin N → ℝ => (Real.sqrt N)⁻¹ * ∑ i, x i * ((σ i : ℤ) : ℝ))
        (Measure.pi fun _ : Fin N => gaussianReal 0 1) = gaussianReal 0 1 := by
  simp only [normalized_field_eq_dotProduct]
  exact map_dotProduct_pi_gaussianReal_of_dotProduct_self (normalized_spin_dotProduct_self hN σ)

/-- A fixed-spin field is centered. -/
theorem integral_normalized_constraint_field_eq_zero (σ : Fin N → ℤˣ) :
    ∫ x : Fin N → ℝ, (Real.sqrt N)⁻¹ * ∑ i, x i * ((σ i : ℤ) : ℝ)
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) = 0 := by
  simp only [normalized_field_eq_dotProduct]
  exact integral_dotProduct_pi_gaussianReal _

/-- **Covariance of two fixed-spin fields in the same column is the overlap:**
`𝔼 [S(σ) S(τ)] = N⁻¹ ∑ i, σ i * τ i`.  It holds for every `N`. -/
theorem integral_normalized_constraint_field_mul_eq (σ τ : Fin N → ℤˣ) :
    ∫ x : Fin N → ℝ, ((Real.sqrt N)⁻¹ * ∑ i, x i * ((σ i : ℤ) : ℝ)) *
        ((Real.sqrt N)⁻¹ * ∑ i, x i * ((τ i : ℤ) : ℝ))
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      (Fintype.card (Fin N) : ℝ)⁻¹ *
        ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ)) := by
  simpa [Fintype.card_fin] using integral_normalized_gaussian_linear_form_mul (N : ℝ) 1
    (Nat.cast_nonneg N) (fun i => ((σ i : ℤ) : ℝ)) fun i => ((τ i : ℤ) : ℝ)

/-- The product of two fixed-spin fields of one column is integrable. -/
theorem integrable_normalized_constraint_field_mul (σ τ : Fin N → ℤˣ) :
    Integrable (fun x : Fin N → ℝ => ((Real.sqrt N)⁻¹ * ∑ i, x i * ((σ i : ℤ) : ℝ)) *
        ((Real.sqrt N)⁻¹ * ∑ i, x i * ((τ i : ℤ) : ℝ)))
      (Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  simp only [normalized_field_eq_dotProduct]
  exact integrable_dotProduct_mul_dotProduct_pi_gaussianReal _ _

/-- **Fields of finitely many fixed spins are jointly Gaussian.** -/
theorem hasGaussianLaw_normalized_constraint_fields {A : Type*} [Finite A] (σ : A → Fin N → ℤˣ) :
    HasGaussianLaw
      (fun (x : Fin N → ℝ) (a : A) => (Real.sqrt N)⁻¹ * ∑ i, x i * ((σ a i : ℤ) : ℝ))
      (Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  simp only [normalized_field_eq_dotProduct]
  exact hasGaussianLaw_dotProduct_family fun a i => (Real.sqrt N)⁻¹ * ((σ a i : ℤ) : ℝ)

/-- **Joint law of the fields of finitely many fixed spins** in one column: the centered
multivariate Gaussian whose covariance matrix is the overlap matrix
`N⁻¹ ∑ i, σ r i * σ s i` (the overlap of `SpinGlasses.Basic`).  The matrix may be singular,
e.g. for coincident spins. -/
theorem map_toLp_normalized_constraint_fields_eq_multivariateGaussian {A : Type*} [Fintype A]
    [DecidableEq A] (σ : A → Fin N → ℤˣ) :
    Measure.map
        (fun x : Fin N → ℝ => WithLp.toLp 2
          fun a : A => (Real.sqrt N)⁻¹ * ∑ i, x i * ((σ a i : ℤ) : ℝ))
        (Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      multivariateGaussian (0 : EuclideanSpace ℝ A)
        (Matrix.of fun r s => (Fintype.card (Fin N) : ℝ)⁻¹ *
          ((fun i => ((σ r i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ s i : ℤ) : ℝ))) := by
  simp only [normalized_field_eq_dotProduct]
  rw [map_toLp_dotProduct_pi_gaussianReal]
  simp only [normalized_spin_dotProduct]

/-- **Independence across columns.**  Choose a fixed spin `σ k` for each column `k`; the fields
`(√N)⁻¹ ∑ i, g k i * σ k i` of the different columns are independent. -/
theorem iIndepFun_normalized_constraint_fields {M : ℕ} (σ : Fin M → Fin N → ℤˣ) :
    iIndepFun (fun (k : Fin M) (g : Fin M → Fin N → ℝ) =>
        (Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ k i : ℤ) : ℝ))
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  simp only [normalized_field_eq_dotProduct]
  exact iIndepFun_dotProduct_pi_pi_gaussianReal fun k i => (Real.sqrt N)⁻¹ * ((σ k i : ℤ) : ℝ)

/-- **Law of the constraint fields of one fixed spin family.**  For `N ≥ 1` and fixed spins `σ k`,
the fields of the `M` columns are i.i.d. standard normal, i.e. the pushforward of the disorder law
is `Measure.pi fun _ => gaussianReal 0 1`. -/
theorem map_normalized_constraint_fields_eq_pi_gaussianReal {M : ℕ} (hN : 0 < N)
    (σ : Fin M → Fin N → ℤˣ) :
    Measure.map (fun (g : Fin M → Fin N → ℝ) (k : Fin M) =>
        (Real.sqrt N)⁻¹ * ∑ i, g k i * ((σ k i : ℤ) : ℝ))
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      Measure.pi fun _ : Fin M => gaussianReal 0 1 := by
  simp only [normalized_field_eq_dotProduct]
  exact map_dotProduct_pi_pi_gaussianReal_of_dotProduct_self fun k =>
    normalized_spin_dotProduct_self hN (σ k)

end SpinGlasses
