/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKReplicaSymmetricBound
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianGram

/-!
# The SK / Guerra smart path: Gaussian data

The trigonometric smart path `s ↦ cos s · X + sin s · Y + h` interpolates between the SK pair field
`X σ = N^{-1/2} β ∑_{i<j} g_{ij} σ_i σ_j` and Guerra's cavity field `Y σ = β √q ∑_i z_i σ_i`, on the
product space `(FinPairs N → ℝ) × (Fin N → ℝ)` of the two independent disorders.  This module
packages the Gaussian bookkeeping common to every use of this path (Theorem 1.3.7, Lemma 1.4.5
and its corollaries): measurability, joint Gaussianity, centering, independence of `X` and `Y`,
and the covariance difference of Eq. (1.64).

## Main declaration

* `SpinGlasses.exists_sk_smart_path_fields`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Sections 1.3-1.4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- A scalar multiple of the linear forms `g ↦ ∑ k, g k * a r k` of i.i.d. standard Gaussians is a
Gaussian vector (the form in which the SK and cavity fields are written). -/
theorem hasGaussianLaw_const_mul_sum_family {κ A : Type*} [Fintype κ] [Finite A] (c : ℝ)
    (a : A → κ → ℝ) :
    HasGaussianLaw (fun (g : κ → ℝ) (r : A) => c * ∑ k, g k * a r k)
      (Measure.pi fun _ : κ => gaussianReal 0 1) := by
  convert hasGaussianLaw_dotProduct_family (fun r k => c * a r k) using 1
  ext g r
  simp only [dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The SK pair sum is a dot product of the disorder with the coefficient vector `σᵢσⱼ`. -/
theorem sk_pair_sum_eq_dotProduct {N : ℕ} (σ : Fin N → ℤˣ) (g : FinPairs N → ℝ) :
    ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ) =
      (fun p : FinPairs N => ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) ⬝ᵥ g := by
  rw [← sum_mul_comm_eq_dotProduct]
  exact Finset.sum_congr rfl fun p _ => mul_assoc _ _ _

/-- **Gaussian data of the SK smart path.**  For `N > 0` and `q ≥ 0` there are measurable functions
`F` (the SK pair field of the pair disorder) and `G` (the cavity field of the site disorder) whose
joint law on the product of the two disorders is Gaussian, with centered, mutually uncorrelated
components and covariance difference
`𝔼 G_σ G_τ - 𝔼 F_σ F_τ = -(N β² / 2) ((R(σ, τ) - q)² - (q² + 1 / N))`, `R = N⁻¹ σ · τ`. -/
theorem exists_sk_smart_path_fields {N : ℕ} (hN : 0 < N) (β q : ℝ) (hq : 0 ≤ q)
    {P : Measure ((FinPairs N → ℝ) × (Fin N → ℝ))}
    (hP : P = (Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin N => gaussianReal 0 1)) :
    ∃ (F : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ) (G : (Fin N → ℝ) → (Fin N → ℤˣ) → ℝ),
      (∀ g σ, F g σ = (Real.sqrt N)⁻¹ * β *
        ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) ∧
      (∀ z σ, G z σ = β * Real.sqrt q * ∑ i, z i * ((σ i : ℤ) : ℝ)) ∧
      Measurable F ∧ Measurable G ∧
      HasGaussianLaw (fun (ω : (FinPairs N → ℝ) × (Fin N → ℝ))
        (s : (Fin N → ℤˣ) ⊕ (Fin N → ℤˣ)) =>
          Sum.elim (fun σ (ω : (FinPairs N → ℝ) × (Fin N → ℝ)) => F ω.1 σ)
            (fun σ ω => G ω.2 σ) s ω) P ∧
      (∀ σ, ∫ ω, F ω.1 σ ∂P = 0) ∧ (∀ σ, ∫ ω, G ω.2 σ ∂P = 0) ∧
      (∀ σ τ, ∫ ω, F ω.1 σ * G ω.2 τ ∂P = 0) ∧
      ∀ σ τ, ∫ ω, G ω.2 σ * G ω.2 τ ∂P - ∫ ω, F ω.1 σ * F ω.1 τ ∂P =
        -((N : ℝ) * β ^ 2 / 2) * ((((N : ℝ)⁻¹ *
          ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ))) - q) ^ 2 -
          (q ^ 2 + (N : ℝ)⁻¹)) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨Pg, hPg⟩ : ∃ Pg : Measure (FinPairs N → ℝ),
      Pg = Measure.pi fun _ : FinPairs N => gaussianReal 0 1 := ⟨_, rfl⟩
  obtain ⟨Pz, hPz⟩ : ∃ Pz : Measure (Fin N → ℝ),
      Pz = Measure.pi fun _ : Fin N => gaussianReal 0 1 := ⟨_, rfl⟩
  rw [← hPg, ← hPz] at hP
  subst hP
  have : IsProbabilityMeasure Pg := by rw [hPg]; infer_instance
  have : IsProbabilityMeasure Pz := by rw [hPz]; infer_instance
  -- the SK pair field and the cavity field as functions of their own disorder
  obtain ⟨F, hF⟩ : ∃ F : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ, ∀ g σ,
      F g σ = (Real.sqrt N)⁻¹ * β *
        ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : (Fin N → ℝ) → (Fin N → ℤˣ) → ℝ, ∀ z σ,
      G z σ = β * Real.sqrt q * ∑ i, z i * ((σ i : ℤ) : ℝ) := ⟨_, fun _ _ => rfl⟩
  have hFm : Measurable F := measurable_pi_iff.2 fun σ => by
    have e : (fun g => F g σ) = fun g => (Real.sqrt N)⁻¹ * β * ∑ p : FinPairs N, g p *
        ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ) := funext fun g => hF g σ
    rw [e]; fun_prop
  have hGm : Measurable G := measurable_pi_iff.2 fun σ => by
    have e : (fun z => G z σ) = fun z => β * Real.sqrt q * ∑ i, z i * ((σ i : ℤ) : ℝ) :=
      funext fun z => hG z σ
    rw [e]; fun_prop
  have hFG : HasGaussianLaw F Pg := by
    rw [hPg]
    convert hasGaussianLaw_const_mul_sum_family ((Real.sqrt N)⁻¹ * β)
      (fun (σ : Fin N → ℤˣ) (p : FinPairs N) =>
        ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) using 1
    ext g σ
    rw [hF]
    simp only [mul_assoc]
  have hGG : HasGaussianLaw G Pz := by
    rw [hPz]
    convert hasGaussianLaw_const_mul_sum_family (β * Real.sqrt q)
      (fun (σ : Fin N → ℤˣ) (i : Fin N) => ((σ i : ℤ) : ℝ)) using 1
    ext z σ
    rw [hG]
  have hF0 : ∀ σ, ∫ g, F g σ ∂Pg = 0 := fun σ => by
    simp only [hF, sk_pair_sum_eq_dotProduct]
    rw [hPg, integral_const_mul, integral_dotProduct_pi_gaussianReal, mul_zero]
  have hG0 : ∀ σ, ∫ z, G z σ ∂Pz = 0 := fun σ => by
    simp only [hG, sum_mul_comm_eq_dotProduct]
    rw [hPz, integral_const_mul, integral_dotProduct_pi_gaussianReal, mul_zero]
  -- Gaussian field on the product of the two disorders
  have hXG : HasGaussianLaw (fun (ω : (FinPairs N → ℝ) × (Fin N → ℝ)) (s : (Fin N → ℤˣ) ⊕
      (Fin N → ℤˣ)) => Sum.elim (fun σ => F ω.1 σ) (fun σ => G ω.2 σ) s)
      (Pg.prod Pz) := HasGaussianLaw.sumElim_prod_of_independent hFG hGG hFm hGm
  have hXG' : HasGaussianLaw (fun (ω : (FinPairs N → ℝ) × (Fin N → ℝ))
      (s : (Fin N → ℤˣ) ⊕ (Fin N → ℤˣ)) => Sum.elim (fun σ (ω : (FinPairs N → ℝ) × (Fin N → ℝ)) =>
        F ω.1 σ) (fun σ ω => G ω.2 σ) s ω) (Pg.prod Pz) := by
    have e : (fun (ω : (FinPairs N → ℝ) × (Fin N → ℝ)) (s : (Fin N → ℤˣ) ⊕ (Fin N → ℤˣ)) =>
        Sum.elim (fun σ (ω : (FinPairs N → ℝ) × (Fin N → ℝ)) => F ω.1 σ)
          (fun σ ω => G ω.2 σ) s ω) = fun ω s =>
        Sum.elim (fun σ => F ω.1 σ) (fun σ => G ω.2 σ) s := by
      funext ω s
      rcases s with σ | σ <;> rfl
    rw [e]
    exact hXG
  have hX0 : ∀ σ, ∫ ω, F ω.1 σ ∂(Pg.prod Pz) = 0 := fun σ => by
    rw [integral_fun_fst (fun g => F g σ), probReal_univ, one_smul, hF0]
  have hY0 : ∀ σ, ∫ ω, G ω.2 σ ∂(Pg.prod Pz) = 0 := fun σ => by
    rw [integral_fun_snd (fun z => G z σ), probReal_univ, one_smul, hG0]
  have h0 : ∀ σ τ, ∫ ω, F ω.1 σ * G ω.2 τ ∂(Pg.prod Pz) = 0 := fun σ τ => by
    rw [integral_prod_mul (fun g => F g σ) (fun z => G z τ), hF0, zero_mul]
  have hCov : ∀ σ τ, (N : ℝ)⁻¹ * ((∫ ω, F ω.1 σ * F ω.1 τ ∂(Pg.prod Pz) -
      ∫ ω, G ω.2 σ * G ω.2 τ ∂(Pg.prod Pz)) / 2) = β ^ 2 / 4 * ((((N : ℝ)⁻¹ *
        ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ))) - q) ^ 2 - q ^ 2 -
          (N : ℝ)⁻¹) := fun σ τ => by
    rw [integral_fun_fst (fun g => F g σ * F g τ), integral_fun_snd (fun z => G z σ * G z τ),
      probReal_univ, probReal_univ, one_smul, one_smul]
    simp only [hF, hG, hPg, hPz]
    exact sk_smart_path_half_covariance_difference_eq hN β q hq σ τ
  refine ⟨F, G, hF, hG, hFm, hGm, hXG', hX0, hY0, h0, fun σ τ => ?_⟩
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have := hCov σ τ
  field_simp at this ⊢
  linarith

end SpinGlasses
