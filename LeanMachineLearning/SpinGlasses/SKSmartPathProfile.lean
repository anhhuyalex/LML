/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKSmartPath
public import LeanMachineLearning.SpinGlasses.GaussianInterpolationReplica
public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.Pi

/-!
# The free energy along the SK smart path

Along the trigonometric smart path `s ↦ cos s · X + sin s · Y + h` between the SK pair field `X`
and Guerra's cavity field `Y`, the normalized free energy `φ(s) = N⁻¹ 𝔼 log Z_s` is differentiable
with derivative `(β² / 2) sin s cos s (A(s) - (1 - q)²)`, where
`A(s) = 𝔼⟨(R₁,₂ - q)²⟩_s ≥ 0` is the expected squared overlap of two replicas.  The endpoints are
the SK free energy (`s = 0`) and the decoupled free energy `log 2 + 𝔼 log cosh (β √q z + h)`
(`s = π / 2`).  This profile is shared by Guerra's bound (Theorem 1.3.7) and the
Aizenman–Lebowitz–Ruelle formula (Theorem 1.4.10).

## Main declarations

* `SpinGlasses.integrable_log_cosh_affine_gaussianReal`.
* `SpinGlasses.exists_sk_smart_path_profile`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Sections 1.3-1.4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- `log cosh` of an affine function of a standard Gaussian is integrable
(`0 ≤ log cosh y ≤ |y|`). -/
theorem integrable_log_cosh_affine_gaussianReal (a b : ℝ) :
    Integrable (fun x : ℝ => Real.log (Real.cosh (a * x + b))) (gaussianReal 0 1) := by
  have hid : Integrable (fun x : ℝ => x) (gaussianReal 0 1) := IsGaussian.integrable_id
  refine Integrable.mono' ((hid.norm.const_mul |a|).add (integrable_const |b|))
    (Real.continuous_cosh.comp (by fun_prop : Continuous fun x : ℝ => a * x + b)
      |>.log (fun x => (Real.cosh_pos _).ne')).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_cosh_nonneg _)]
  refine (Real.log_cosh_le_abs _).trans ?_
  calc |a * x + b| ≤ |a * x| + |b| := abs_add_le _ _
    _ = |a| * ‖x‖ + |b| := by rw [abs_mul, Real.norm_eq_abs]

/-- **The SK smart-path profile.**  For `N > 0`, `q ≥ 0` there are functions `φ` (the normalized
free energy along the smart path) and `A` (the expected squared overlap along the smart path)
with `φ 0` the SK free energy, `φ (π/2)` the decoupled free energy,
`φ' = (β²/2) sin cos (A - (1-q)²)` and `A ≥ 0`, where `A t` is the expectation over the two
disorders of the Gibbs average of `(R₁,₂ - q)²` for the smart-path energy at time `t`. -/
theorem exists_sk_smart_path_profile {N : ℕ} (hN : 0 < N) (β h q : ℝ) (hq : 0 ≤ q) :
    ∃ φ A : ℝ → ℝ,
      φ 0 = (N : ℝ)⁻¹ * ∫ g : FinPairs N → ℝ, Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp ((Real.sqrt N)⁻¹ * β *
          (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
          h * ∑ i, ((σ i : ℤ) : ℝ)))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ∧
      φ (Real.pi / 2) = Real.log 2 +
        ∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ∂(gaussianReal 0 1) ∧
      (∀ t, HasDerivAt φ (β ^ 2 / 2 * Real.sin t * Real.cos t * (A t - (1 - q) ^ 2)) t) ∧
      (∀ t, 0 ≤ A t) ∧
      ∀ t, A t = ∫ ω : (FinPairs N → ℝ) × (Fin N → ℝ), ∫ σ : Fin 2 → (Fin N → ℤˣ),
          (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
            Real.cos t * ((Real.sqrt N)⁻¹ * β *
              ∑ p : FinPairs N, ω.1 p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
            Real.sin t * (β * Real.sqrt q * ∑ i, ω.2 i * ((a i : ℤ) : ℝ)) +
            h * ∑ i, ((a i : ℤ) : ℝ))
          ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin N => gaussianReal 0 1)) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨Pg, hPg⟩ : ∃ Pg : Measure (FinPairs N → ℝ),
      Pg = Measure.pi fun _ : FinPairs N => gaussianReal 0 1 := ⟨_, rfl⟩
  obtain ⟨Pz, hPz⟩ : ∃ Pz : Measure (Fin N → ℝ),
      Pz = Measure.pi fun _ : Fin N => gaussianReal 0 1 := ⟨_, rfl⟩
  have : IsProbabilityMeasure Pg := by rw [hPg]; infer_instance
  have : IsProbabilityMeasure Pz := by rw [hPz]; infer_instance
  -- the SK pair field and the cavity field on the product of the two disorders
  obtain ⟨F, G, hF, hG, hFm, hGm, hXG', hX0, hY0, h0, hCov'⟩ :=
    exists_sk_smart_path_fields hN β q hq (P := Pg.prod Pz) (by rw [hPg, hPz])
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hCov : ∀ σ τ, (N : ℝ)⁻¹ * ((∫ ω, F ω.1 σ * F ω.1 τ ∂(Pg.prod Pz) -
      ∫ ω, G ω.2 σ * G ω.2 τ ∂(Pg.prod Pz)) / 2) = β ^ 2 / 4 * ((((N : ℝ)⁻¹ *
        ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ i : ℤ) : ℝ))) - q) ^ 2 - q ^ 2 -
          (N : ℝ)⁻¹) := fun σ τ => by
    have := hCov' σ τ
    field_simp at this ⊢
    linarith
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
  -- the remainder is the expected squared overlap
  obtain ⟨A, hA⟩ : ∃ A : ℝ → ℝ, ∀ t, A t = ∫ ω, ∫ σ : Fin 2 → (Fin N → ℤˣ),
      (r (σ 0) (σ 1) - q) ^ 2 ∂(Measure.pi fun _ : Fin 2 =>
        Measure.count.tilted fun a => Real.cos t * F ω.1 a + Real.sin t * G ω.2 a +
          h * ∑ i, ((a i : ℤ) : ℝ)) ∂(Pg.prod Pz) := ⟨_, fun _ => rfl⟩
  have hAnn : ∀ t, 0 ≤ A t := fun t => by
    rw [hA]
    exact integral_nonneg fun ω => integral_nonneg fun σ => sq_nonneg _
  have hderiv' : ∀ t, HasDerivAt φ (β ^ 2 / 2 * Real.sin t * Real.cos t * (A t - (1 - q) ^ 2)) t :=
    fun t => by
      have hg : ∀ a, AEMeasurable (fun ω : (FinPairs N → ℝ) × (Fin N → ℝ) =>
          Real.cos t * F ω.1 a + Real.sin t * G ω.2 a + h * ∑ i, ((a i : ℤ) : ℝ)) (Pg.prod Pz) :=
        fun a => ((((measurable_pi_apply a).comp hFm).comp measurable_fst).const_mul _ |>.add
          (((measurable_pi_apply a).comp hGm).comp measurable_snd |>.const_mul _)).add_const _
          |>.aemeasurable
      have hJint := integrable_integral_pi_count_tilted_det (R := Fin 2) (P := Pg.prod Pz)
        (g := fun a ω => Real.cos t * F ω.1 a + Real.sin t * G ω.2 a +
          h * ∑ i, ((a i : ℤ) : ℝ)) hg (fun σ : Fin 2 → (Fin N → ℤˣ) => (r (σ 0) (σ 1) - q) ^ 2)
      have hin : ∀ ω : (FinPairs N → ℝ) × (Fin N → ℝ),
          ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ), ((r p.1 p.2 - q) ^ 2 - (1 - q) ^ 2)
            ∂((Measure.count.tilted fun a => Real.cos t * F ω.1 a + Real.sin t * G ω.2 a +
              h * ∑ i, ((a i : ℤ) : ℝ)).prod
              (Measure.count.tilted fun a => Real.cos t * F ω.1 a + Real.sin t * G ω.2 a +
                h * ∑ i, ((a i : ℤ) : ℝ))) =
          (∫ σ : Fin 2 → (Fin N → ℤˣ), (r (σ 0) (σ 1) - q) ^ 2
            ∂(Measure.pi fun _ : Fin 2 =>
              Measure.count.tilted fun a => Real.cos t * F ω.1 a + Real.sin t * G ω.2 a +
                h * ∑ i, ((a i : ℤ) : ℝ))) - (1 - q) ^ 2 := fun ω => by
        rw [integral_sub Integrable.of_finite (integrable_const _), integral_const, probReal_univ,
          one_smul, integral_pi_fin_two _ (fun x y => (r x y - q) ^ 2),
          integral_prod _ Integrable.of_finite]
      have hA' : A t - (1 - q) ^ 2 = ∫ ω, ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ),
          ((r p.1 p.2 - q) ^ 2 - (1 - q) ^ 2)
          ∂((Measure.count.tilted fun a => Real.cos t * F ω.1 a + Real.sin t * G ω.2 a +
            h * ∑ i, ((a i : ℤ) : ℝ)).prod
            (Measure.count.tilted fun a => Real.cos t * F ω.1 a + Real.sin t * G ω.2 a +
              h * ∑ i, ((a i : ℤ) : ℝ))) ∂(Pg.prod Pz) := by
        simp_rw [hin]
        rw [integral_sub hJint (integrable_const _), integral_const, probReal_univ, one_smul, hA]
      rw [hA']
      exact hderiv t
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
    simp only [hG, decoupled_field_eq]
    rw [hfe, ← (measurePreserving_eval (fun _ : Fin N => gaussianReal 0 1) j₀).map_eq, hPz]
    rw [integral_map (measurable_pi_apply j₀).aemeasurable]
    exact ((Real.continuous_cosh.comp (by fun_prop : Continuous fun x : ℝ =>
      β * Real.sqrt q * x + h)).log fun x => (Real.cosh_pos _).ne').aestronglyMeasurable
  refine ⟨φ, A, ?_, hpi, hderiv', hAnn, fun t => ?_⟩
  · rw [← h0e]
  · rw [hA t]
    subst hPg hPz
    simp only [hF, hG, hr]

end SpinGlasses
