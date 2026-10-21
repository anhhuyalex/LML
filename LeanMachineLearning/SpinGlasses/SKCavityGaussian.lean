/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IteratedBound
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
  let X : (Fin N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
    (Real.sqrt (N + 1))⁻¹ * β * (σ (Fin.last N) : ℝ) *
      ∑ i : Fin N, g i * (σ i.castSucc : ℝ)
  let Y : ℝ → (Fin (N + 1) → ℤˣ) → ℝ := fun z σ =>
    β * (σ (Fin.last N) : ℝ) * z * Real.sqrt q
  have hX : HasGaussianLaw X (Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
    have h := hasGaussianLaw_const_mul_sum_family ((Real.sqrt (N + 1))⁻¹ * β)
      (fun (σ : Fin (N + 1) → ℤˣ) (i : Fin N) =>
        (σ (Fin.last N) : ℝ) * (σ i.castSucc : ℝ))
    convert h using 1
    ext g σ
    simp only [X, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hY : HasGaussianLaw Y (gaussianReal 0 1) := by
    have h : HasGaussianLaw (id : ℝ → ℝ) (gaussianReal 0 1) :=
      IsGaussian.hasGaussianLaw_id
    let L : ℝ →L[ℝ] ((Fin (N + 1) → ℤˣ) → ℝ) :=
      ContinuousLinearMap.pi fun σ => ContinuousLinearMap.smulRight
        (ContinuousLinearMap.id ℝ ℝ) (β * (σ (Fin.last N) : ℝ) * Real.sqrt q)
    have hL : Measurable L := L.continuous.measurable
    have h' := h.map_of_measurable L hL
    convert h' using 1
    ext z σ
    simp only [Y, Function.comp_apply, L, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, id_eq]
    ring
  have hXm : Measurable X := measurable_pi_iff.2 fun σ => by
    change Measurable (fun g : Fin N → ℝ =>
      (Real.sqrt (N + 1))⁻¹ * β * (σ (Fin.last N) : ℝ) *
        ∑ i : Fin N, g i * (σ i.castSucc : ℝ))
    fun_prop
  have hYm : Measurable Y := measurable_pi_iff.2 fun σ => by
    change Measurable (fun z : ℝ => β * (σ (Fin.last N) : ℝ) * z * Real.sqrt q)
    fun_prop
  convert HasGaussianLaw.sumElim_prod_of_independent hX hY hXm hYm using 1

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
  rw [integral_sq_gaussianReal, mul_one]

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

end SpinGlasses
