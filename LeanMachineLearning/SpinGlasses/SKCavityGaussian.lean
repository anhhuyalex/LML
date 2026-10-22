/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IteratedBound
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianGram
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiExp
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.Hyperbolic
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

section GenericMoments

variable {K : Type*} [Fintype K] {f f' : (K → ℝ) × ℝ → ℝ}

/-- Centering of a linear form in the new-edge couplings under the product law. -/
theorem integral_linear_form_prod_eq_zero (c : K → ℝ)
    (hf : ∀ ω, f ω = ∑ i, c i * ω.1 i) :
    (∫ ω, f ω ∂((Measure.pi fun _ : K => gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 := by
  simp_rw [hf]
  rw [integral_prod_fun_fst_of_isProbabilityMeasure _ _ (fun g : K → ℝ => ∑ i, c i * g i)]
  exact integral_dotProduct_pi_gaussianReal c

/-- Centering of a multiple of the independent scalar Gaussian under the product law. -/
theorem integral_scalar_prod_eq_zero (d : ℝ) (hf : ∀ ω, f ω = d * ω.2) :
    (∫ ω, f ω ∂((Measure.pi fun _ : K => gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 := by
  simp_rw [hf]
  rw [integral_prod_fun_snd_of_isProbabilityMeasure _ _ (fun z : ℝ => d * z),
    integral_const_mul]
  simp

/-- Covariance of two linear forms in the new-edge couplings under the product law. -/
theorem integral_linear_form_mul_prod (c c' : K → ℝ)
    (hf : ∀ ω, f ω = ∑ i, c i * ω.1 i) (hf' : ∀ ω, f' ω = ∑ i, c' i * ω.1 i) :
    (∫ ω, f ω * f' ω
      ∂((Measure.pi fun _ : K => gaussianReal 0 1).prod (gaussianReal 0 1))) =
      ∑ i, c i * c' i := by
  simp_rw [hf, hf']
  rw [integral_prod_fun_fst_of_isProbabilityMeasure _ _
    (fun g : K → ℝ => (∑ i, c i * g i) * ∑ i, c' i * g i)]
  exact integral_dotProduct_mul_dotProduct_pi_gaussianReal c c'

/-- A linear form in the new edges is uncorrelated with the independent scalar field. -/
theorem integral_linear_form_mul_scalar_prod (c : K → ℝ) (d : ℝ)
    (hf : ∀ ω, f ω = ∑ i, c i * ω.1 i) (hf' : ∀ ω, f' ω = d * ω.2) :
    (∫ ω, f ω * f' ω
      ∂((Measure.pi fun _ : K => gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 := by
  simp_rw [hf, hf']
  rw [integral_prod_mul (fun g : K → ℝ => ∑ i, c i * g i) (fun z : ℝ => d * z)]
  have h : (∫ g : K → ℝ, ∑ i, c i * g i ∂(Measure.pi fun _ : K => gaussianReal 0 1)) = 0 :=
    integral_dotProduct_pi_gaussianReal c
  rw [h, zero_mul]

/-- Covariance of two multiples of the independent scalar Gaussian under the product law. -/
theorem integral_scalar_mul_prod (d d' : ℝ)
    (hf : ∀ ω, f ω = d * ω.2) (hf' : ∀ ω, f' ω = d' * ω.2) :
    (∫ ω, f ω * f' ω
      ∂((Measure.pi fun _ : K => gaussianReal 0 1).prod (gaussianReal 0 1))) = d * d' := by
  simp_rw [hf, hf']
  rw [integral_prod_fun_snd_of_isProbabilityMeasure _ _ (fun z : ℝ => (d * z) * (d' * z))]
  have hc : (fun z : ℝ => (d * z) * (d' * z)) = fun z => (d * d') * z ^ 2 := by
    funext z
    ring
  rw [hc, integral_const_mul, NTK.integral_sq_gaussianReal, mul_one]

end GenericMoments

/-- Centering of the interacting field under the independent new-edge and scalar laws. -/
theorem integral_sk_cavity_edge_field_eq_zero (N : ℕ) (β : ℝ)
    (σ : Fin (N + 1) → ℤˣ) :
    (∫ ω : (Fin N → ℝ) × ℝ,
      (Real.sqrt (N + 1))⁻¹ * β * (σ (Fin.last N) : ℝ) *
        ∑ i : Fin N, ω.1 i * (σ i.castSucc : ℝ)
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 :=
  integral_linear_form_prod_eq_zero
    (fun i => (Real.sqrt (N + 1))⁻¹ * β * (σ (Fin.last N) : ℝ) * (σ i.castSucc : ℝ))
    fun ω => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring

/-- Centering of the decoupled scalar field under the product law. -/
theorem integral_sk_cavity_scalar_field_eq_zero (N : ℕ) (β q : ℝ)
    (σ : Fin (N + 1) → ℤˣ) :
    (∫ ω : (Fin N → ℝ) × ℝ,
      β * (σ (Fin.last N) : ℝ) * ω.2 * Real.sqrt q
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 :=
  integral_scalar_prod_eq_zero (β * (σ (Fin.last N) : ℝ) * Real.sqrt q) fun ω => by ring

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
  rw [integral_linear_form_mul_prod
    (fun i => (Real.sqrt (N + 1))⁻¹ * β * (σ (Fin.last N) : ℝ) * (σ i.castSucc : ℝ))
    (fun i => (Real.sqrt (N + 1))⁻¹ * β * (τ (Fin.last N) : ℝ) * (τ i.castSucc : ℝ))
    (fun ω => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun ω => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)]
  have hs : (Real.sqrt (N + 1))⁻¹ ^ 2 = (N + 1 : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  simp only [dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  linear_combination (β ^ 2 * (σ (Fin.last N) : ℝ) * (τ (Fin.last N) : ℝ) *
    (σ i.castSucc : ℝ) * (τ i.castSucc : ℝ)) * hs

/-- The cross-covariance is zero because the new edges and scalar field are independent. -/
theorem integral_sk_cavity_edge_mul_scalar_eq_zero (N : ℕ) (β q : ℝ)
    (σ τ : Fin (N + 1) → ℤˣ) :
    (∫ ω : (Fin N → ℝ) × ℝ,
      ((Real.sqrt (N + 1))⁻¹ * β * (σ (Fin.last N) : ℝ) *
        ∑ i : Fin N, ω.1 i * (σ i.castSucc : ℝ)) *
      (β * (τ (Fin.last N) : ℝ) * ω.2 * Real.sqrt q)
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 :=
  integral_linear_form_mul_scalar_prod
    (fun i => (Real.sqrt (N + 1))⁻¹ * β * (σ (Fin.last N) : ℝ) * (σ i.castSucc : ℝ))
    (β * (τ (Fin.last N) : ℝ) * Real.sqrt q)
    (fun ω => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    fun ω => by ring

/-- Scalar cavity covariance. The nonnegativity of `q` removes the square root. -/
theorem integral_sk_cavity_scalar_field_mul (N : ℕ) (β q : ℝ) (hq : 0 ≤ q)
    (σ τ : Fin (N + 1) → ℤˣ) :
    (∫ ω : (Fin N → ℝ) × ℝ,
      (β * (σ (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) *
      (β * (τ (Fin.last N) : ℝ) * ω.2 * Real.sqrt q)
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) =
      β ^ 2 * (σ (Fin.last N) : ℝ) * (τ (Fin.last N) : ℝ) * q := by
  rw [integral_scalar_mul_prod (β * (σ (Fin.last N) : ℝ) * Real.sqrt q)
    (β * (τ (Fin.last N) : ℝ) * Real.sqrt q) (fun ω => by ring) (fun ω => by ring)]
  linear_combination (β ^ 2 * (σ (Fin.last N) : ℝ) * (τ (Fin.last N) : ℝ)) *
    Real.sq_sqrt hq

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
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 :=
  integral_linear_form_prod_eq_zero (fun i => (Real.sqrt (N : ℝ))⁻¹ * β * (σ i : ℝ))
    fun ω => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring

/-- Centering of the decoupled scalar field under the product law. -/
theorem integral_sk_cavity_N_scalar_field_eq_zero (N : ℕ) (β q : ℝ) :
    (∫ ω : (Fin N → ℝ) × ℝ,
      β * ω.2 * Real.sqrt q
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 :=
  integral_scalar_prod_eq_zero (β * Real.sqrt q) fun ω => by ring

/-- Covariance of two interacting N-spin cavity fields under the product law. -/
theorem integral_sk_cavity_N_edge_field_mul (N : ℕ) (β : ℝ)
    (σ τ : Fin N → ℤˣ) :
    (∫ ω : (Fin N → ℝ) × ℝ,
      ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, ω.1 i * (σ i : ℝ)) *
      ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, ω.1 i * (τ i : ℝ))
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) =
      β ^ 2 * ((N : ℝ)⁻¹ * ∑ i : Fin N, (σ i : ℝ) * (τ i : ℝ)) := by
  rw [integral_linear_form_mul_prod (fun i => (Real.sqrt (N : ℝ))⁻¹ * β * (σ i : ℝ))
    (fun i => (Real.sqrt (N : ℝ))⁻¹ * β * (τ i : ℝ))
    (fun ω => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun ω => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)]
  have hs : (Real.sqrt (N : ℝ))⁻¹ ^ 2 = (N : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  linear_combination (β ^ 2 * (σ i : ℝ) * (τ i : ℝ)) * hs

/-- The cross-covariance is zero because the new edges and scalar field are independent. -/
theorem integral_sk_cavity_N_edge_mul_scalar_eq_zero (N : ℕ) (β q : ℝ)
    (σ _τ : Fin N → ℤˣ) :
    (∫ ω : (Fin N → ℝ) × ℝ,
      ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, ω.1 i * (σ i : ℝ)) *
      (β * ω.2 * Real.sqrt q)
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 :=
  integral_linear_form_mul_scalar_prod (fun i => (Real.sqrt (N : ℝ))⁻¹ * β * (σ i : ℝ))
    (β * Real.sqrt q)
    (fun ω => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    fun ω => by ring

/-- Scalar N-spin cavity covariance. The nonnegativity of `q` removes the square root. -/
theorem integral_sk_cavity_N_scalar_field_mul (N : ℕ) (β q : ℝ) (hq : 0 ≤ q)
    (_σ _τ : Fin N → ℤˣ) :
    (∫ ω : (Fin N → ℝ) × ℝ,
      (β * ω.2 * Real.sqrt q) * (β * ω.2 * Real.sqrt q)
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) =
      β ^ 2 * q := by
  rw [integral_scalar_mul_prod (β * Real.sqrt q) (β * Real.sqrt q) (fun ω => by ring)
    (fun ω => by ring)]
  linear_combination β ^ 2 * Real.sq_sqrt hq

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

/-- The Gaussian `cosh` moment of either the sum or the difference of two interpolated
N-spin cavity fields is bounded uniformly in the interpolation angle. -/
theorem integral_cosh_sk_cavity_linear_combo_le (N : ℕ) (hN : 0 < N) (β q s m : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (σ τ : Fin N → ℤˣ) (sign : ℝ)
    (hsign : sign = 1 ∨ sign = -1) :
    (∫ ω : (Fin N → ℝ) × ℝ,
      Real.cosh
        (∑ i : Fin N,
            (Real.cos s * ((Real.sqrt (N : ℝ))⁻¹ * β *
              ((σ i : ℝ) + sign * (τ i : ℝ)))) * ω.1 i +
          (Real.sin s * (β * Real.sqrt q * (1 + sign))) * ω.2 + m)
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) ≤
      Real.cosh m * Real.exp (2 * β ^ 2) := by
  rw [integral_cosh_sum_mul_add_mul_gaussianReal]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.cosh_pos m).le
  have hvar := sum_sq_sk_cavity_linear_combo_le N hN β q s hq σ τ sign hsign
  dsimp only at hvar
  linarith

/-- The product of the two `sinh` cavity factors along the trigonometric path has Gaussian
expectation bounded by `cosh(2h) exp(2β²)`. -/
theorem integral_abs_sinh_mul_sinh_sk_cavity_le (N : ℕ) (hN : 0 < N) (β q s h : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (σ τ : Fin N → ℤˣ) :
    let L : (Fin N → ℤˣ) → (Fin N → ℝ) × ℝ → ℝ := fun ρ ω =>
      Real.cos s * ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, ω.1 i * (ρ i : ℝ)) +
      Real.sin s * (β * ω.2 * Real.sqrt q) + h
    (∫ ω : (Fin N → ℝ) × ℝ, |Real.sinh (L σ ω)| * |Real.sinh (L τ ω)|
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) ≤
      Real.cosh (2 * h) * Real.exp (2 * β ^ 2) := by
  intro L
  let c_add : Fin N → ℝ := fun i =>
    Real.cos s * ((Real.sqrt (N : ℝ))⁻¹ * β * ((σ i : ℝ) + 1 * (τ i : ℝ)))
  let d_add : ℝ := Real.sin s * (β * Real.sqrt q * (1 + 1))
  let c_sub : Fin N → ℝ := fun i =>
    Real.cos s * ((Real.sqrt (N : ℝ))⁻¹ * β * ((σ i : ℝ) + (-1) * (τ i : ℝ)))
  let d_sub : ℝ := Real.sin s * (β * Real.sqrt q * (1 + (-1)))
  have h_add_eq (ω : (Fin N → ℝ) × ℝ) :
      L σ ω + L τ ω = ∑ i, c_add i * ω.1 i + d_add * ω.2 + 2 * h := by
    have h1 : L σ ω + L τ ω =
        (Real.cos s * ((Real.sqrt (N : ℝ))⁻¹ * β)) *
          (∑ i : Fin N, ω.1 i * (σ i : ℝ) + ∑ i : Fin N, ω.1 i * (τ i : ℝ)) +
        d_add * ω.2 + 2 * h := by
      dsimp [L, d_add]
      ring
    rw [h1, ← Finset.sum_add_distrib, Finset.mul_sum]
    have h2 : (∑ i : Fin N, (Real.cos s * ((Real.sqrt (N : ℝ))⁻¹ * β)) *
        (ω.1 i * (σ i : ℝ) + ω.1 i * (τ i : ℝ))) = ∑ i, c_add i * ω.1 i := by
      dsimp [c_add]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [h2]
  have h_sub_eq (ω : (Fin N → ℝ) × ℝ) :
      L σ ω - L τ ω = ∑ i, c_sub i * ω.1 i + d_sub * ω.2 + 0 := by
    have h1 : L σ ω - L τ ω =
        (Real.cos s * ((Real.sqrt (N : ℝ))⁻¹ * β)) *
          (∑ i : Fin N, ω.1 i * (σ i : ℝ) - ∑ i : Fin N, ω.1 i * (τ i : ℝ)) +
        d_sub * ω.2 + 0 := by
      dsimp [L, d_sub]
      ring
    rw [h1, ← Finset.sum_sub_distrib, Finset.mul_sum]
    have h2 : (∑ i : Fin N, (Real.cos s * ((Real.sqrt (N : ℝ))⁻¹ * β)) *
        (ω.1 i * (σ i : ℝ) - ω.1 i * (τ i : ℝ))) = ∑ i, c_sub i * ω.1 i := by
      dsimp [c_sub]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [h2]
  have hint_add : Integrable (fun ω : (Fin N → ℝ) × ℝ => Real.cosh (L σ ω + L τ ω))
      ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    simp_rw [h_add_eq]
    exact integrable_cosh_sum_mul_add_mul_gaussianReal c_add d_add (2 * h)
  have hint_sub : Integrable (fun ω : (Fin N → ℝ) × ℝ => Real.cosh (L σ ω - L τ ω))
      ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    simp_rw [h_sub_eq]
    exact integrable_cosh_sum_mul_add_mul_gaussianReal c_sub d_sub 0
  have hint_dom : Integrable (fun ω : (Fin N → ℝ) × ℝ =>
      (Real.cosh (L σ ω + L τ ω) + Real.cosh (L σ ω - L τ ω)) / 2)
      ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    (hint_add.add hint_sub).div_const 2
  have h_le (ω : (Fin N → ℝ) × ℝ) :
      |Real.sinh (L σ ω)| * |Real.sinh (L τ ω)| ≤
      (Real.cosh (L σ ω + L τ ω) + Real.cosh (L σ ω - L τ ω)) / 2 := by
    calc |Real.sinh (L σ ω)| * |Real.sinh (L τ ω)|
      _ = |Real.sinh (L σ ω) * Real.sinh (L τ ω)| := (abs_mul _ _).symm
      _ ≤ Real.cosh (L σ ω) * Real.cosh (L τ ω) :=
        Real.abs_sinh_mul_sinh_le_cosh_mul_cosh _ _
      _ = (Real.cosh (L σ ω + L τ ω) + Real.cosh (L σ ω - L τ ω)) / 2 :=
        Real.cosh_mul_cosh _ _
  have h_meas : AEStronglyMeasurable
      (fun ω : (Fin N → ℝ) × ℝ => |Real.sinh (L σ ω)| * |Real.sinh (L τ ω)|)
      ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    dsimp [L]
    fun_prop
  have hint_lhs : Integrable (fun ω : (Fin N → ℝ) × ℝ =>
      |Real.sinh (L σ ω)| * |Real.sinh (L τ ω)|)
      ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    refine Integrable.mono' hint_dom h_meas (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_abs]
    exact h_le ω
  have h_int_mono := integral_mono hint_lhs hint_dom h_le
  refine h_int_mono.trans ?_
  rw [integral_div, integral_add hint_add hint_sub]
  have h_int_add : (∫ ω : (Fin N → ℝ) × ℝ, Real.cosh (L σ ω + L τ ω)
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) ≤
      Real.cosh (2 * h) * Real.exp (2 * β ^ 2) := by
    simp_rw [h_add_eq]
    exact integral_cosh_sk_cavity_linear_combo_le N hN β q s (2 * h) hq σ τ 1 (Or.inl rfl)
  have h_int_sub : (∫ ω : (Fin N → ℝ) × ℝ, Real.cosh (L σ ω - L τ ω)
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) ≤
      Real.cosh (2 * h) * Real.exp (2 * β ^ 2) := by
    simp_rw [h_sub_eq]
    have h0 := integral_cosh_sk_cavity_linear_combo_le N hN β q s 0 hq σ τ (-1) (Or.inr rfl)
    refine h0.trans ?_
    rw [Real.cosh_zero, one_mul]
    have h1le : 1 ≤ Real.cosh (2 * h) := Real.one_le_cosh (2 * h)
    have : 0 ≤ Real.exp (2 * β ^ 2) := (Real.exp_pos _).le
    nlinarith
  linarith

/-- **Covariance bracket identity for the cavity cosh derivative (Talagrand Eq. 1.178).**
For the signed Gaussian fields on `(Fin N → ℤˣ) × ℤˣ`, the bracket
`([E Y² - E X²]_diag - [E Y_a Y_b - E X_a X_b]_pair)` evaluates to
`-β² (1 - q) + ε¹ ε² β² (R(ρ¹, ρ²) - q)`. -/
theorem sk_cavity_covariance_bracket_eq (N : ℕ) (hN : 0 < N) (β q : ℝ) (hq : 0 ≤ q)
    (p : ((Fin N → ℤˣ) × ℤˣ) × ((Fin N → ℤˣ) × ℤˣ)) :
    let P := (Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)
    let X : (Fin N → ℤˣ) → (Fin N → ℝ) × ℝ → ℝ := fun σ ω =>
      (Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, ω.1 i * (σ i : ℝ)
    let Y : (Fin N → ℤˣ) → (Fin N → ℝ) × ℝ → ℝ := fun _ ω =>
      β * ω.2 * Real.sqrt q
    ((∫ ω', (p.1.2 : ℝ) * Y p.1.1 ω' * ((p.1.2 : ℝ) * Y p.1.1 ω') ∂P -
        ∫ ω', (p.1.2 : ℝ) * X p.1.1 ω' * ((p.1.2 : ℝ) * X p.1.1 ω') ∂P) -
      (∫ ω', (p.1.2 : ℝ) * Y p.1.1 ω' * ((p.2.2 : ℝ) * Y p.2.1 ω') ∂P -
        ∫ ω', (p.1.2 : ℝ) * X p.1.1 ω' * ((p.2.2 : ℝ) * X p.2.1 ω') ∂P)) =
    -β ^ 2 * (1 - q) +
      (p.1.2 : ℝ) * (p.2.2 : ℝ) *
        (β ^ 2 * ((N : ℝ)⁻¹ * ∑ i : Fin N, (p.1.1 i : ℝ) * (p.2.1 i : ℝ) - q)) := by
  intro P X Y
  have hu1 : (p.1.2 : ℝ) * (p.1.2 : ℝ) = 1 := by
    rw [← sq, units_cast_sq]
  have h1 : (∫ ω', (p.1.2 : ℝ) * Y p.1.1 ω' * ((p.1.2 : ℝ) * Y p.1.1 ω') ∂P) =
      ∫ ω', (Y p.1.1 ω') * (Y p.1.1 ω') ∂P := by
    have : (fun ω' => (p.1.2 : ℝ) * Y p.1.1 ω' * ((p.1.2 : ℝ) * Y p.1.1 ω')) =
        fun ω' => (Y p.1.1 ω') * (Y p.1.1 ω') := by
      funext ω'
      calc (p.1.2 : ℝ) * Y p.1.1 ω' * ((p.1.2 : ℝ) * Y p.1.1 ω')
        _ = ((p.1.2 : ℝ) * (p.1.2 : ℝ)) * ((Y p.1.1 ω') * (Y p.1.1 ω')) := by ring
        _ = (Y p.1.1 ω') * (Y p.1.1 ω') := by rw [hu1, one_mul]
    rw [this]
  have h2 : (∫ ω', (p.1.2 : ℝ) * X p.1.1 ω' * ((p.1.2 : ℝ) * X p.1.1 ω') ∂P) =
      ∫ ω', (X p.1.1 ω') * (X p.1.1 ω') ∂P := by
    have : (fun ω' => (p.1.2 : ℝ) * X p.1.1 ω' * ((p.1.2 : ℝ) * X p.1.1 ω')) =
        fun ω' => (X p.1.1 ω') * (X p.1.1 ω') := by
      funext ω'
      calc (p.1.2 : ℝ) * X p.1.1 ω' * ((p.1.2 : ℝ) * X p.1.1 ω')
        _ = ((p.1.2 : ℝ) * (p.1.2 : ℝ)) * ((X p.1.1 ω') * (X p.1.1 ω')) := by ring
        _ = (X p.1.1 ω') * (X p.1.1 ω') := by rw [hu1, one_mul]
    rw [this]
  have h3 : (∫ ω', (p.1.2 : ℝ) * Y p.1.1 ω' * ((p.2.2 : ℝ) * Y p.2.1 ω') ∂P) =
      (p.1.2 : ℝ) * (p.2.2 : ℝ) * ∫ ω', (Y p.1.1 ω') * (Y p.2.1 ω') ∂P := by
    have : (fun ω' => (p.1.2 : ℝ) * Y p.1.1 ω' * ((p.2.2 : ℝ) * Y p.2.1 ω')) =
        fun ω' => ((p.1.2 : ℝ) * (p.2.2 : ℝ)) * ((Y p.1.1 ω') * (Y p.2.1 ω')) := by
      funext ω'; ring
    rw [this, integral_const_mul]
  have h4 : (∫ ω', (p.1.2 : ℝ) * X p.1.1 ω' * ((p.2.2 : ℝ) * X p.2.1 ω') ∂P) =
      (p.1.2 : ℝ) * (p.2.2 : ℝ) * ∫ ω', (X p.1.1 ω') * (X p.2.1 ω') ∂P := by
    have : (fun ω' => (p.1.2 : ℝ) * X p.1.1 ω' * ((p.2.2 : ℝ) * X p.2.1 ω')) =
        fun ω' => ((p.1.2 : ℝ) * (p.2.2 : ℝ)) * ((X p.1.1 ω') * (X p.2.1 ω')) := by
      funext ω'; ring
    rw [this, integral_const_mul]
  rw [h1, h2, h3, h4, ← mul_sub]
  have hdiff1 := sk_cavity_N_covariance_difference N β q hq p.1.1 p.1.1
  have hdiff2 := sk_cavity_N_covariance_difference N β q hq p.1.1 p.2.1
  dsimp [P, X, Y] at hdiff1 hdiff2 ⊢
  rw [← hdiff1, ← hdiff2]
  have hdiag : (N : ℝ)⁻¹ * ∑ i : Fin N, (p.1.1 i : ℝ) * (p.1.1 i : ℝ) = 1 := by
    have hs : ∀ i : Fin N, (p.1.1 i : ℝ) * (p.1.1 i : ℝ) = 1 := fun i => by
      rw [← sq, units_cast_sq]
    simp_rw [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hNne : (N : ℝ) ≠ 0 := (Nat.cast_pos.2 hN).ne'
    rw [mul_one, inv_mul_cancel₀ hNne]
  rw [hdiag]
  ring

end SpinGlasses
