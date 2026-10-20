/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKReplicaSymmetricBound
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianGram

/-!
# Guerra's replica-symmetric upper bound for the SK free energy

This module closes Talagrand's Theorem 1.3.7: for every `q ≥ 0`,
$$p_N(\beta, h) \le \log 2 + \mathbb{E}\log\cosh(\beta z\sqrt{q} + h) +
  \frac{\beta^2}{4}(1 - q)^2.$$
The proof interpolates, along the trigonometric smart path
`s ↦ cos s · X + sin s · Y + h`, between the SK field `X` (pair disorder) and Guerra's cavity
field `Y` (site disorder) on the product space of the two disorders, and combines
* the covariance difference of Eq. (1.64) (`sk_smart_path_half_covariance_difference_eq`),
* the derivative formula for the trigonometric path
  (`hasDerivAt_normalized_log_sum_exp_trig_of_covariance_difference`),
* the calculus endpoint estimate (`le_endpoint_of_trig_square_deriv`), and
* the exact decoupled free energy (`decoupled_free_energy_eq`).

## Main declaration

* `SpinGlasses.sk_replica_symmetric_upper_bound`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Theorem 1.3.7.
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

/-- `log cosh` of an affine function of a standard Gaussian is integrable
(`0 ≤ log cosh y ≤ |y|`). -/
theorem integrable_log_cosh_affine_gaussianReal (a b : ℝ) :
    Integrable (fun x : ℝ => Real.log (Real.cosh (a * x + b))) (gaussianReal 0 1) := by
  have hle (y : ℝ) : Real.log (Real.cosh y) ≤ |y| := by
    rw [← Real.cosh_abs y]
    refine (Real.log_le_log (Real.cosh_pos _) ?_).trans_eq (Real.log_exp _)
    rw [Real.cosh_eq]
    have := Real.exp_le_exp.2 (neg_le_self (abs_nonneg y))
    linarith
  have hid : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := IsGaussian.integrable_id
  refine Integrable.mono' ((hid.norm.const_mul |a|).add (integrable_const |b|))
    (Real.continuous_cosh.comp (by fun_prop : Continuous fun x : ℝ => a * x + b)
      |>.log (fun x => (Real.cosh_pos _).ne')).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (Real.one_le_cosh _))]
  refine (hle _).trans ?_
  calc |a * x + b| ≤ |a * x| + |b| := abs_add_le _ _
    _ = |a| * ‖x‖ + |b| := by rw [abs_mul, Real.norm_eq_abs]

/-- The SK pair sum is a dot product of the disorder with the coefficient vector `σᵢσⱼ`. -/
theorem sk_pair_sum_eq_dotProduct {N : ℕ} (σ : Fin N → ℤˣ) (g : FinPairs N → ℝ) :
    ∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ) =
      (fun p : FinPairs N => ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) ⬝ᵥ g := by
  rw [← sum_mul_comm_eq_dotProduct]
  exact Finset.sum_congr rfl fun p _ => mul_assoc _ _ _

/-- **Guerra's replica-symmetric upper bound (Talagrand, Theorem 1.3.7).** For every `q ≥ 0`,
`p_N(β, h) ≤ log 2 + 𝔼 log cosh (β √q z + h) + β²/4 (1 - q)²`, with `z ~ 𝒩(0, 1)`. -/
theorem sk_replica_symmetric_upper_bound {N : ℕ} (hN : 0 < N) (β h q : ℝ) (hq : 0 ≤ q) :
    (N : ℝ)⁻¹ * ∫ g : FinPairs N → ℝ, Real.log (∑ σ : Fin N → ℤˣ,
      Real.exp ((Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((σ i : ℤ) : ℝ)))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
    Real.log 2 + ∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ∂(gaussianReal 0 1) +
      β ^ 2 / 4 * (1 - q) ^ 2 := by
  classical
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨Pg, hPg⟩ : ∃ Pg : Measure (FinPairs N → ℝ),
      Pg = Measure.pi fun _ : FinPairs N => gaussianReal 0 1 := ⟨_, rfl⟩
  obtain ⟨Pz, hPz⟩ : ∃ Pz : Measure (Fin N → ℝ),
      Pz = Measure.pi fun _ : Fin N => gaussianReal 0 1 := ⟨_, rfl⟩
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
  -- the interpolation
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℝ, ∀ s, φ s = (N : ℝ)⁻¹ * ∫ ω, Real.log (∑ σ : Fin N → ℤˣ,
      Real.exp (Real.cos s * F ω.1 σ + Real.sin s * G ω.2 σ + h * ∑ i, ((σ i : ℤ) : ℝ)))
        ∂(Pg.prod Pz) := ⟨_, fun _ => rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : (Fin N → ℤˣ) → (Fin N → ℤˣ) → ℝ, ∀ σ τ,
      r σ τ = (N : ℝ)⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ)) :=
    ⟨_, fun _ _ => rfl⟩
  have hdiag : ∀ σ, r σ σ = 1 := fun σ => by
    rw [hr]
    simpa using card_inv_mul_dotProduct_self_eq_one (fun i => ((σ i : ℤ) : ℝ))
      (fun i => units_cast_sq (σ i))
  have hderiv : ∀ t, HasDerivAt φ (β ^ 2 / 2 * Real.sin t * Real.cos t *
      ∫ ω, ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ), ((r p.1 p.2 - q) ^ 2 - (1 - q) ^ 2)
        ∂((Measure.count.tilted fun a => Real.cos t * F ω.1 a + Real.sin t * G ω.2 a +
          h * ∑ i, ((a i : ℤ) : ℝ)).prod
          (Measure.count.tilted fun a => Real.cos t * F ω.1 a + Real.sin t * G ω.2 a +
            h * ∑ i, ((a i : ℤ) : ℝ))) ∂(Pg.prod Pz)) t := fun t => by
    have := hasDerivAt_normalized_log_sum_exp_trig_of_covariance_difference
      (X := fun σ ω => F ω.1 σ) (Y := fun σ ω => G ω.2 σ) (P := Pg.prod Pz) (N := N) β q t r
      (fun σ => (measurable_pi_apply σ |>.comp hFm).comp measurable_fst)
      (fun σ => (measurable_pi_apply σ |>.comp hGm).comp measurable_snd)
      hXG' hX0 hY0 h0
      (by simpa only [hr] using hCov) hdiag (fun a => h * ∑ i, ((a i : ℤ) : ℝ))
    rw [show φ = _ from funext hφ]
    exact this
  -- the remainder is nonnegative
  obtain ⟨A, hA⟩ : ∃ A : ℝ → ℝ, ∀ t, A t = (∫ ω, ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ),
      ((r p.1 p.2 - q) ^ 2 - (1 - q) ^ 2)
        ∂((Measure.count.tilted fun a => Real.cos t * F ω.1 a + Real.sin t * G ω.2 a +
          h * ∑ i, ((a i : ℤ) : ℝ)).prod
          (Measure.count.tilted fun a => Real.cos t * F ω.1 a + Real.sin t * G ω.2 a +
            h * ∑ i, ((a i : ℤ) : ℝ))) ∂(Pg.prod Pz)) + (1 - q) ^ 2 := ⟨_, fun _ => rfl⟩
  have hAnn : ∀ t, 0 ≤ A t := fun t => by
    rw [hA]
    set c : ℝ := (1 - q) ^ 2 with hc
    have hc0 : 0 ≤ c := sq_nonneg _
    have hpt : ∀ ω : (FinPairs N → ℝ) × (Fin N → ℝ), -c ≤
        ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ), ((r p.1 p.2 - q) ^ 2 - c)
        ∂((Measure.count.tilted fun a => Real.cos t * F ω.1 a + Real.sin t * G ω.2 a +
          h * ∑ i, ((a i : ℤ) : ℝ)).prod
          (Measure.count.tilted fun a => Real.cos t * F ω.1 a + Real.sin t * G ω.2 a +
            h * ∑ i, ((a i : ℤ) : ℝ))) := fun ω => by
      have := integral_mono (μ := (Measure.count.tilted fun a => Real.cos t * F ω.1 a +
          Real.sin t * G ω.2 a + h * ∑ i, ((a i : ℤ) : ℝ)).prod
          (Measure.count.tilted fun a => Real.cos t * F ω.1 a + Real.sin t * G ω.2 a +
            h * ∑ i, ((a i : ℤ) : ℝ)))
        (f := fun _ : (Fin N → ℤˣ) × (Fin N → ℤˣ) => -c)
        (g := fun p => (r p.1 p.2 - q) ^ 2 - c) Integrable.of_finite Integrable.of_finite
        (fun p => by simp only; linarith [sq_nonneg (r p.1 p.2 - q)])
      simpa using this
    by_cases hint : Integrable (fun ω : (FinPairs N → ℝ) × (Fin N → ℝ) =>
        ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ),
        ((r p.1 p.2 - q) ^ 2 - c)
        ∂((Measure.count.tilted fun a => Real.cos t * F ω.1 a + Real.sin t * G ω.2 a +
          h * ∑ i, ((a i : ℤ) : ℝ)).prod
          (Measure.count.tilted fun a => Real.cos t * F ω.1 a + Real.sin t * G ω.2 a +
            h * ∑ i, ((a i : ℤ) : ℝ)))) (Pg.prod Pz)
    · have := integral_mono (μ := Pg.prod Pz) (integrable_const (-c)) hint hpt
      simp at this
      linarith
    · rw [integral_undef hint]
      linarith
  have hderiv' : ∀ t, HasDerivAt φ (β ^ 2 / 2 * Real.sin t * Real.cos t * (A t - (1 - q) ^ 2)) t :=
    fun t => by
      rw [hA, add_sub_cancel_right]
      exact hderiv t
  have hmain := le_endpoint_of_trig_square_deriv φ A β q hderiv' hAnn
  -- the endpoint `s = 0`
  have h0e : φ 0 = (N : ℝ)⁻¹ * ∫ g : FinPairs N → ℝ, Real.log (∑ σ : Fin N → ℤˣ,
      Real.exp ((Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((σ i : ℤ) : ℝ))) ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
    rw [hφ]
    simp only [Real.cos_zero, Real.sin_zero, one_mul, zero_mul, add_zero]
    rw [integral_fun_fst (fun g : FinPairs N → ℝ => Real.log (∑ σ : Fin N → ℤˣ,
      Real.exp (F g σ + h * ∑ i, ((σ i : ℤ) : ℝ)))), probReal_univ, one_smul, hPg]
    simp only [hF]
  -- the endpoint `s = π / 2`
  have hpi : φ (Real.pi / 2) = Real.log 2 +
      ∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ∂(gaussianReal 0 1) := by
    rw [hφ]
    simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul, zero_add]
    rw [integral_fun_snd (fun z : Fin N → ℝ => Real.log (∑ σ : Fin N → ℤˣ,
      Real.exp (G z σ + h * ∑ i, ((σ i : ℤ) : ℝ)))), probReal_univ, one_smul]
    set j₀ : Fin N := ⟨0, hN⟩
    have hlaw : ∀ j, IdentDistrib (fun z : Fin N → ℝ => β * Real.sqrt q * z j + h)
        (fun z : Fin N → ℝ => β * Real.sqrt q * z j₀ + h) Pz Pz := fun j => by
      have hj := (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) j).map_eq
      have hj0 := (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) j₀).map_eq
      have hid : IdentDistrib (fun z : Fin N → ℝ => z j) (fun z : Fin N → ℝ => z j₀) Pz Pz :=
        ⟨(measurable_pi_apply j).aemeasurable, (measurable_pi_apply j₀).aemeasurable, by
          rw [hPz, hj, hj0]⟩
      exact hid.comp (by fun_prop : Measurable fun x : ℝ => β * Real.sqrt q * x + h)
    have hint : Integrable (fun z : Fin N → ℝ => Real.log (Real.cosh (β * Real.sqrt q * z j₀ + h)))
        Pz := by
      have := (integrable_log_cosh_affine_gaussianReal (β * Real.sqrt q) h)
      rw [← (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) j₀).map_eq] at this
      rw [hPz]
      exact (integrable_map_measure this.1 (measurable_pi_apply j₀).aemeasurable).1 this
    have hfe := decoupled_free_energy_eq (P := Pz) (fun j z => β * Real.sqrt q * z j + h) j₀
      hlaw hint
    simp only [Fintype.card_fin] at hfe
    have hrew : ∀ z : Fin N → ℝ, ∀ σ : Fin N → ℤˣ, G z σ + h * ∑ i, ((σ i : ℤ) : ℝ) =
        ∑ i, ((σ i : ℤ) : ℝ) * (β * Real.sqrt q * z i + h) := fun z σ => by
      rw [hG, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [hrew]
    rw [hfe, ← (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) j₀).map_eq, hPz]
    rw [integral_map (measurable_pi_apply j₀).aemeasurable]
    exact ((Real.continuous_cosh.comp (by fun_prop : Continuous fun x : ℝ =>
      β * Real.sqrt q * x + h)).log fun x => (Real.cosh_pos _).ne').aestronglyMeasurable
  rw [← h0e]
  linarith

end SpinGlasses
