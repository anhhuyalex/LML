/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IteratedBound
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianGram
public import LeanMachineLearning.SpinGlasses.SKCavityOverlap
public import LeanMachineLearning.SpinGlasses.SKSmartPath
public import LeanMachineLearning.SpinGlasses.PoissonDirichletIdentities

/-!
# Gaussian inputs for the last-spin cavity interpolation

The new-edge disorder and the scalar cavity Gaussian are independent. This module establishes
joint Gaussianity of their fields without including the independent old-pair Hamiltonian in
either field. The latter belongs to the deterministic shift of the conditional replica theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- A family of linear forms in standard Gaussians and a family of multiples of an independent
standard Gaussian together form a jointly Gaussian vector on the product space. -/
theorem hasGaussianLaw_linear_form_and_scalar_prod
    {A K : Type*} [Finite A] [Fintype K] (c : A → K → ℝ) (d : A → ℝ) :
    HasGaussianLaw
      (fun (ω : (K → ℝ) × ℝ) (s : A ⊕ A) =>
        Sum.elim (fun a => ∑ i, c a i * ω.1 i) (fun a => d a * ω.2) s)
      ((Measure.pi fun _ : K => gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  let _ := Fintype.ofFinite A
  have hX : HasGaussianLaw (fun (g : K → ℝ) (a : A) => ∑ i, c a i * g i)
      (Measure.pi fun _ : K => gaussianReal 0 1) := by
    have h := hasGaussianLaw_dotProduct_family c
    convert h using 1
    rfl
  have hY : HasGaussianLaw (fun (z : ℝ) (a : A) => d a * z) (gaussianReal 0 1) := by
    have h : HasGaussianLaw (id : ℝ → ℝ) (gaussianReal 0 1) :=
      IsGaussian.hasGaussianLaw_id
    let L : ℝ →L[ℝ] (A → ℝ) := ContinuousLinearMap.pi fun a =>
      ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (d a)
    have hL : Measurable L := L.continuous.measurable
    have h' := h.map_of_measurable L hL
    convert h' using 1
    ext z a
    simp only [Function.comp_apply, L, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, id_eq]
    ring
  have hXm : Measurable (fun (g : K → ℝ) (a : A) => ∑ i, c a i * g i) := by
    refine measurable_pi_iff.2 fun a => ?_
    change Measurable (fun (g : K → ℝ) => ∑ i, c a i * g i)
    fun_prop
  have hYm : Measurable (fun (z : ℝ) (a : A) => d a * z) := by
    refine measurable_pi_iff.2 fun a => ?_
    change Measurable (fun z => d a * z)
    fun_prop
  exact HasGaussianLaw.sumElim_prod_of_independent hX hY hXm hYm

/-- The interacting last-spin field and the decoupled scalar field, considered together,
form a jointly Gaussian family under the product law of new-edge couplings and `z`.
The old-pair disorder is intentionally absent. -/
theorem hasGaussianLaw_sk_cavity_fields (N : ℕ) (β q : ℝ) :
    HasGaussianLaw
      (fun (ω : (Fin N → ℝ) × ℝ)
        (s : (Fin (N + 1) → ℤˣ) ⊕ (Fin (N + 1) → ℤˣ)) =>
        Sum.elim
          (fun σ => (Real.sqrt (N + 1))⁻¹ * β * (σ (Fin.last N) : ℝ) *
            ∑ i : Fin N, ω.1 i * (σ i.castSucc : ℝ))
          (fun σ => β * (σ (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) s)
      ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have h := hasGaussianLaw_linear_form_and_scalar_prod
    (c := fun σ : Fin (N + 1) → ℤˣ => fun i : Fin N =>
      (Real.sqrt (N + 1))⁻¹ * β * (σ (Fin.last N) : ℝ) * (σ i.castSucc : ℝ))
    (d := fun σ : Fin (N + 1) → ℤˣ => β * (σ (Fin.last N) : ℝ) * Real.sqrt q)
  convert h using 1
  ext ω (σ | σ)
  · simp only [Sum.elim_inl, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp only [Sum.elim_inr]
    ring

/-- The interacting N-spin cavity field and the decoupled scalar field, considered together,
form a jointly Gaussian family under the product law of new-edge couplings and `z`. -/
theorem hasGaussianLaw_sk_cavity_N_fields (N : ℕ) (β q : ℝ) :
    HasGaussianLaw
      (fun (ω : (Fin N → ℝ) × ℝ)
        (s : (Fin N → ℤˣ) ⊕ (Fin N → ℤˣ)) =>
        Sum.elim
          (fun σ => (Real.sqrt (N : ℝ))⁻¹ * β *
            ∑ i : Fin N, ω.1 i * (σ i : ℝ))
          (fun _ => β * ω.2 * Real.sqrt q) s)
      ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have h := hasGaussianLaw_linear_form_and_scalar_prod
    (c := fun σ : Fin N → ℤˣ => fun i : Fin N =>
      (Real.sqrt (N : ℝ))⁻¹ * β * (σ i : ℝ))
    (d := fun _ : Fin N → ℤˣ => β * Real.sqrt q)
  convert h using 1
  ext ω (σ | σ)
  · simp only [Sum.elim_inl, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp only [Sum.elim_inr]
    ring

/-- Centering of the interacting field under the independent new-edge and scalar laws. -/
theorem integral_sk_cavity_edge_field_eq_zero (N : ℕ) (β : ℝ)
    (σ : Fin (N + 1) → ℤˣ) :
    (∫ ω : (Fin N → ℝ) × ℝ,
      (Real.sqrt (N + 1))⁻¹ * β * (σ (Fin.last N) : ℝ) *
        ∑ i : Fin N, ω.1 i * (σ i.castSucc : ℝ)
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 := by
  rw [integral_prod_fun_fst_of_isProbabilityMeasure _ _ (fun g : Fin N → ℝ =>
    (Real.sqrt (N + 1))⁻¹ * β * (σ (Fin.last N) : ℝ) *
      ∑ i : Fin N, g i * (σ i.castSucc : ℝ))]
  rw [integral_const_mul]
  have he : (fun g : Fin N → ℝ => ∑ i : Fin N, g i * (σ i.castSucc : ℝ)) =
      (fun g => (fun i : Fin N => (σ i.castSucc : ℝ)) ⬝ᵥ g) := by
    funext g
    exact sum_mul_comm_eq_dotProduct _ _
  rw [he, integral_dotProduct_pi_gaussianReal, mul_zero]

/-- Centering of the decoupled scalar field under the product law. -/
theorem integral_sk_cavity_scalar_field_eq_zero (N : ℕ) (β q : ℝ)
    (σ : Fin (N + 1) → ℤˣ) :
    (∫ ω : (Fin N → ℝ) × ℝ,
      β * (σ (Fin.last N) : ℝ) * ω.2 * Real.sqrt q
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 := by
  rw [integral_prod_fun_snd_of_isProbabilityMeasure _ _
    (fun z : ℝ => β * (σ (Fin.last N) : ℝ) * z * Real.sqrt q)]
  have he : (fun z : ℝ => β * (σ (Fin.last N) : ℝ) * z * Real.sqrt q) =
      (fun z => (β * (σ (Fin.last N) : ℝ) * Real.sqrt q) * z) := by
    funext z
    ring
  rw [he, integral_const_mul]
  simp

/-- Covariance of two interacting cavity fields under the full new-disorder product law. -/
theorem integral_sk_cavity_edge_field_mul (N : ℕ) (β : ℝ)
    (σ τ : Fin (N + 1) → ℤˣ) :
    (∫ ω : (Fin N → ℝ) × ℝ,
      ((Real.sqrt (N + 1))⁻¹ * β * (σ (Fin.last N) : ℝ) *
        ∑ i : Fin N, ω.1 i * (σ i.castSucc : ℝ)) *
      ((Real.sqrt (N + 1))⁻¹ * β * (τ (Fin.last N) : ℝ) *
        ∑ i : Fin N, ω.1 i * (τ i.castSucc : ℝ))
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) =
      β ^ 2 * (σ (Fin.last N) : ℝ) * (τ (Fin.last N) : ℝ) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (σ i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (τ i.castSucc : ℝ))) := by
  rw [integral_prod_fun_fst_of_isProbabilityMeasure _ _ (fun g : Fin N → ℝ =>
    ((Real.sqrt (N + 1))⁻¹ * β * (σ (Fin.last N) : ℝ) *
      ∑ i : Fin N, g i * (σ i.castSucc : ℝ)) *
    ((Real.sqrt (N + 1))⁻¹ * β * (τ (Fin.last N) : ℝ) *
      ∑ i : Fin N, g i * (τ i.castSucc : ℝ)))]
  exact integral_last_spin_cavity_field_mul N (N + 1) β (by positivity) σ τ

/-- The cross-covariance is zero because the new edges and scalar field are independent. -/
theorem integral_sk_cavity_edge_mul_scalar_eq_zero (N : ℕ) (β q : ℝ)
    (σ τ : Fin (N + 1) → ℤˣ) :
    (∫ ω : (Fin N → ℝ) × ℝ,
      ((Real.sqrt (N + 1))⁻¹ * β * (σ (Fin.last N) : ℝ) *
        ∑ i : Fin N, ω.1 i * (σ i.castSucc : ℝ)) *
      (β * (τ (Fin.last N) : ℝ) * ω.2 * Real.sqrt q)
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 := by
  rw [integral_prod_mul
    (fun g : Fin N → ℝ =>
      (Real.sqrt (N + 1))⁻¹ * β * (σ (Fin.last N) : ℝ) *
        ∑ i : Fin N, g i * (σ i.castSucc : ℝ))
    (fun z : ℝ => β * (τ (Fin.last N) : ℝ) * z * Real.sqrt q)]
  have he : (∫ g : Fin N → ℝ,
      (Real.sqrt (N + 1))⁻¹ * β * (σ (Fin.last N) : ℝ) *
        ∑ i : Fin N, g i * (σ i.castSucc : ℝ)
      ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)) = 0 := by
    rw [integral_const_mul]
    have hs : (fun g : Fin N → ℝ => ∑ i : Fin N, g i * (σ i.castSucc : ℝ)) =
        (fun g => (fun i : Fin N => (σ i.castSucc : ℝ)) ⬝ᵥ g) := by
      funext g
      exact sum_mul_comm_eq_dotProduct _ _
    rw [hs, integral_dotProduct_pi_gaussianReal, mul_zero]
  rw [he, zero_mul]

/-- Scalar cavity covariance. The nonnegativity of `q` removes the square root. -/
theorem integral_sk_cavity_scalar_field_mul (N : ℕ) (β q : ℝ) (hq : 0 ≤ q)
    (σ τ : Fin (N + 1) → ℤˣ) :
    (∫ ω : (Fin N → ℝ) × ℝ,
      (β * (σ (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) *
      (β * (τ (Fin.last N) : ℝ) * ω.2 * Real.sqrt q)
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) =
      β ^ 2 * (σ (Fin.last N) : ℝ) * (τ (Fin.last N) : ℝ) * q := by
  rw [integral_prod_fun_snd_of_isProbabilityMeasure _ _ (fun z : ℝ =>
    (β * (σ (Fin.last N) : ℝ) * z * Real.sqrt q) *
      (β * (τ (Fin.last N) : ℝ) * z * Real.sqrt q))]
  have hc (z : ℝ) :
      (β * (σ (Fin.last N) : ℝ) * z * Real.sqrt q) *
        (β * (τ (Fin.last N) : ℝ) * z * Real.sqrt q) =
      (β ^ 2 * (σ (Fin.last N) : ℝ) * (τ (Fin.last N) : ℝ) * q) * z ^ 2 := by
    calc
      _ = (β ^ 2 * (σ (Fin.last N) : ℝ) *
          (τ (Fin.last N) : ℝ) * (Real.sqrt q ^ 2)) * z ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hq]
  simp_rw [hc]
  rw [integral_const_mul]
  rw [NTK.integral_sq_gaussianReal, mul_one]

/-- The covariance difference required by the trigonometric replica derivative.
The old-pair disorder does not enter either field. -/
theorem sk_cavity_covariance_difference (N : ℕ) (β q : ℝ) (hq : 0 ≤ q)
    (σ τ : Fin (N + 1) → ℤˣ) :
    β ^ 2 * (σ (Fin.last N) : ℝ) * (τ (Fin.last N) : ℝ) *
      (q - (N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (σ i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (τ i.castSucc : ℝ))) =
    (∫ ω : (Fin N → ℝ) × ℝ,
      (β * (σ (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) *
      (β * (τ (Fin.last N) : ℝ) * ω.2 * Real.sqrt q)
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) -
    (∫ ω : (Fin N → ℝ) × ℝ,
      ((Real.sqrt (N + 1))⁻¹ * β * (σ (Fin.last N) : ℝ) *
        ∑ i : Fin N, ω.1 i * (σ i.castSucc : ℝ)) *
      ((Real.sqrt (N + 1))⁻¹ * β * (τ (Fin.last N) : ℝ) *
        ∑ i : Fin N, ω.1 i * (τ i.castSucc : ℝ))
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) := by
  rw [integral_sk_cavity_scalar_field_mul N β q hq σ τ,
    integral_sk_cavity_edge_field_mul]
  ring

/-- Centering of the interacting N-spin field under the independent disorder laws. -/
theorem integral_sk_cavity_N_edge_field_eq_zero (N : ℕ) (β : ℝ)
    (σ : Fin N → ℤˣ) :
    (∫ ω : (Fin N → ℝ) × ℝ,
      (Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, ω.1 i * (σ i : ℝ)
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 := by
  rw [integral_prod_fun_fst_of_isProbabilityMeasure _ _ (fun g : Fin N → ℝ =>
    (Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, g i * (σ i : ℝ))]
  rw [integral_const_mul]
  have he : (fun g : Fin N → ℝ => ∑ i : Fin N, g i * (σ i : ℝ)) =
      (fun g => (fun i : Fin N => (σ i : ℝ)) ⬝ᵥ g) := by
    funext g
    exact sum_mul_comm_eq_dotProduct _ _
  rw [he, integral_dotProduct_pi_gaussianReal, mul_zero]

/-- Centering of the decoupled scalar field under the product law. -/
theorem integral_sk_cavity_N_scalar_field_eq_zero (N : ℕ) (β q : ℝ) :
    (∫ ω : (Fin N → ℝ) × ℝ,
      β * ω.2 * Real.sqrt q
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 := by
  rw [integral_prod_fun_snd_of_isProbabilityMeasure _ _
    (fun z : ℝ => β * z * Real.sqrt q)]
  have he : (fun z : ℝ => β * z * Real.sqrt q) = (fun z => (β * Real.sqrt q) * z) := by
    funext z; ring
  rw [he, integral_const_mul]
  simp

/-- Covariance of two interacting N-spin cavity fields under the product law. -/
theorem integral_sk_cavity_N_edge_field_mul (N : ℕ) (β : ℝ)
    (σ τ : Fin N → ℤˣ) :
    (∫ ω : (Fin N → ℝ) × ℝ,
      ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, ω.1 i * (σ i : ℝ)) *
      ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, ω.1 i * (τ i : ℝ))
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) =
      β ^ 2 * ((N : ℝ)⁻¹ * ∑ i : Fin N, (σ i : ℝ) * (τ i : ℝ)) := by
  rw [integral_prod_fun_fst_of_isProbabilityMeasure _ _ (fun g : Fin N → ℝ =>
    ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, g i * (σ i : ℝ)) *
    ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, g i * (τ i : ℝ)))]
  have h := integral_normalized_gaussian_linear_form_mul (N : ℝ) β (by positivity)
    (fun i => (σ i : ℝ)) (fun i => (τ i : ℝ))
  dsimp [dotProduct] at h
  rw [h]
  ring

/-- The cross-covariance is zero because the new edges and scalar field are independent. -/
theorem integral_sk_cavity_N_edge_mul_scalar_eq_zero (N : ℕ) (β q : ℝ)
    (σ _τ : Fin N → ℤˣ) :
    (∫ ω : (Fin N → ℝ) × ℝ,
      ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, ω.1 i * (σ i : ℝ)) *
      (β * ω.2 * Real.sqrt q)
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 := by
  rw [integral_prod_mul
    (fun g : Fin N → ℝ =>
      (Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, g i * (σ i : ℝ))
    (fun z : ℝ => β * z * Real.sqrt q)]
  have he : (∫ g : Fin N → ℝ,
      (Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, g i * (σ i : ℝ)
      ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)) = 0 := by
    rw [integral_const_mul]
    have hs : (fun g : Fin N → ℝ => ∑ i : Fin N, g i * (σ i : ℝ)) =
        (fun g => (fun i : Fin N => (σ i : ℝ)) ⬝ᵥ g) := by
      funext g
      exact sum_mul_comm_eq_dotProduct _ _
    rw [hs, integral_dotProduct_pi_gaussianReal, mul_zero]
  rw [he, zero_mul]

/-- Scalar N-spin cavity covariance. The nonnegativity of `q` removes the square root. -/
theorem integral_sk_cavity_N_scalar_field_mul (N : ℕ) (β q : ℝ) (hq : 0 ≤ q)
    (_σ _τ : Fin N → ℤˣ) :
    (∫ ω : (Fin N → ℝ) × ℝ,
      (β * ω.2 * Real.sqrt q) * (β * ω.2 * Real.sqrt q)
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) =
      β ^ 2 * q := by
  rw [integral_prod_fun_snd_of_isProbabilityMeasure _ _ (fun z : ℝ =>
    (β * z * Real.sqrt q) * (β * z * Real.sqrt q))]
  have hc (z : ℝ) :
      (β * z * Real.sqrt q) * (β * z * Real.sqrt q) = (β ^ 2 * q) * z ^ 2 := by
    calc
      _ = (β ^ 2 * (Real.sqrt q ^ 2)) * z ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hq]
  simp_rw [hc]
  rw [integral_const_mul]
  rw [NTK.integral_sq_gaussianReal, mul_one]

/-- The covariance difference for the N-spin cavity fields. -/
theorem sk_cavity_N_covariance_difference (N : ℕ) (β q : ℝ) (hq : 0 ≤ q)
    (σ τ : Fin N → ℤˣ) :
    β ^ 2 * (q - (N : ℝ)⁻¹ * ∑ i : Fin N, (σ i : ℝ) * (τ i : ℝ)) =
    (∫ ω : (Fin N → ℝ) × ℝ,
      (β * ω.2 * Real.sqrt q) * (β * ω.2 * Real.sqrt q)
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) -
    (∫ ω : (Fin N → ℝ) × ℝ,
      ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, ω.1 i * (σ i : ℝ)) *
      ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, ω.1 i * (τ i : ℝ))
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) := by
  rw [integral_sk_cavity_N_scalar_field_mul N β q hq σ τ,
    integral_sk_cavity_N_edge_field_mul]
  ring

/-- Sum of squares of coordinates of `σ¹ ± σ²` is at most `4 N`. -/
lemma sum_sq_units_add_or_sub_le (N : ℕ) (σ τ : Fin N → ℤˣ) (sign : ℝ)
    (hsign : sign = 1 ∨ sign = -1) :
    ∑ i : Fin N, ((σ i : ℝ) + sign * (τ i : ℝ)) ^ 2 ≤ 4 * (N : ℝ) := by
  have h_each (i : Fin N) : ((σ i : ℝ) + sign * (τ i : ℝ)) ^ 2 ≤ 4 := by
    have hs : |(σ i : ℝ)| = 1 := by simp [abs_units_cast_eq_one]
    have ht : |(τ i : ℝ)| = 1 := by simp [abs_units_cast_eq_one]
    have h_abs : |(σ i : ℝ) + sign * (τ i : ℝ)| ≤ 2 := by
      rcases hsign with rfl | rfl
      · calc |(σ i : ℝ) + 1 * (τ i : ℝ)| = |(σ i : ℝ) + (τ i : ℝ)| := by ring_nf
          _ ≤ |(σ i : ℝ)| + |(τ i : ℝ)| := abs_add_le _ _
          _ = 1 + 1 := by rw [hs, ht]
          _ = 2 := by norm_num
      · calc |(σ i : ℝ) + (-1) * (τ i : ℝ)| = |(σ i : ℝ) - (τ i : ℝ)| := by ring_nf
          _ ≤ |(σ i : ℝ)| + |-(τ i : ℝ)| := abs_add_le _ _
          _ = |(σ i : ℝ)| + |(τ i : ℝ)| := by rw [abs_neg]
          _ = 1 + 1 := by rw [hs, ht]
          _ = 2 := by norm_num
    have h1 := (abs_le.1 h_abs).1
    have h2 := (abs_le.1 h_abs).2
    nlinarith
  calc ∑ i : Fin N, ((σ i : ℝ) + sign * (τ i : ℝ)) ^ 2
    _ ≤ ∑ _i : Fin N, (4 : ℝ) := Finset.sum_le_sum fun i _ => h_each i
    _ = 4 * (N : ℝ) := by simp [nsmul_eq_mul, mul_comm]

/-- The total variance of the linear combination `cos s (X_σ ± X_τ) + sin s (Y_σ ± Y_τ)`
is at most `4 β²`. -/
lemma sum_sq_sk_cavity_linear_combo_le (N : ℕ) (hN : 0 < N) (β q s : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (σ τ : Fin N → ℤˣ) (sign : ℝ) (hsign : sign = 1 ∨ sign = -1) :
    let c_edge : Fin N → ℝ := fun i =>
      Real.cos s * ((Real.sqrt (N : ℝ))⁻¹ * β * ((σ i : ℝ) + sign * (τ i : ℝ)))
    let c_scalar : ℝ := Real.sin s * (β * Real.sqrt q * (1 + sign))
    (∑ i, (c_edge i) ^ 2) + c_scalar ^ 2 ≤ 4 * β ^ 2 := by
  intro c_edge c_scalar
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.2 hN
  have h_edge : ∑ i, (c_edge i) ^ 2 ≤ Real.cos s ^ 2 * (4 * β ^ 2) := by
    dsimp [c_edge]
    have h_rw : (∑ i : Fin N,
        (Real.cos s * ((Real.sqrt (N : ℝ))⁻¹ * β * ((σ i : ℝ) + sign * (τ i : ℝ)))) ^ 2) =
        (Real.cos s ^ 2 * ((Real.sqrt (N : ℝ))⁻¹ ^ 2 * β ^ 2)) *
          ∑ i, ((σ i : ℝ) + sign * (τ i : ℝ)) ^ 2 := by
      simp_rw [show ∀ i,
        (Real.cos s * ((Real.sqrt (N : ℝ))⁻¹ * β * ((σ i : ℝ) + sign * (τ i : ℝ)))) ^ 2 =
        (Real.cos s ^ 2 * ((Real.sqrt (N : ℝ))⁻¹ ^ 2 * β ^ 2)) *
          ((σ i : ℝ) + sign * (τ i : ℝ)) ^ 2 by intro i; ring]
      rw [← Finset.mul_sum]
    rw [h_rw]
    rw [inv_pow, Real.sq_sqrt hNpos.le]
    have hsum := sum_sq_units_add_or_sub_le N σ τ sign hsign
    have h_nonneg : 0 ≤ Real.cos s ^ 2 * ((N : ℝ)⁻¹ * β ^ 2) := by positivity
    calc (Real.cos s ^ 2 * ((N : ℝ)⁻¹ * β ^ 2)) * (∑ i, ((σ i : ℝ) + sign * (τ i : ℝ)) ^ 2)
      _ ≤ (Real.cos s ^ 2 * ((N : ℝ)⁻¹ * β ^ 2)) * (4 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum h_nonneg
      _ = Real.cos s ^ 2 * (4 * β ^ 2) := by
        have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
        field_simp
  have h_scalar : c_scalar ^ 2 ≤ Real.sin s ^ 2 * (4 * β ^ 2) := by
    dsimp [c_scalar]
    have h_sign_sq : (1 + sign) ^ 2 ≤ 4 := by
      rcases hsign with rfl | rfl <;> norm_num
    have h_prod : q * (1 + sign) ^ 2 ≤ 1 * 4 := by
      nlinarith [hq.1, hq.2]
    calc (Real.sin s * (β * Real.sqrt q * (1 + sign))) ^ 2
      _ = Real.sin s ^ 2 * β ^ 2 * (Real.sqrt q ^ 2 * (1 + sign) ^ 2) := by ring
      _ = Real.sin s ^ 2 * β ^ 2 * (q * (1 + sign) ^ 2) := by rw [Real.sq_sqrt hq.1]
      _ ≤ Real.sin s ^ 2 * β ^ 2 * (1 * 4) := by
        have : 0 ≤ Real.sin s ^ 2 * β ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_left h_prod this
      _ = Real.sin s ^ 2 * (4 * β ^ 2) := by ring
  calc (∑ i, (c_edge i) ^ 2) + c_scalar ^ 2
    _ ≤ Real.cos s ^ 2 * (4 * β ^ 2) + Real.sin s ^ 2 * (4 * β ^ 2) :=
      add_le_add h_edge h_scalar
    _ = (Real.cos s ^ 2 + Real.sin s ^ 2) * (4 * β ^ 2) := by ring
    _ = 4 * β ^ 2 := by rw [Real.cos_sq_add_sin_sq, one_mul]

end SpinGlasses
