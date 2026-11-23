/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IteratedBound
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProdFactorization
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityPath

/-!
# The endpoint `v = 0` of the cavity path (Talagrand Lemma 2.3.1)

At `s = π/2` (`v = cos² s = 0`) the field is `S_0 = θ = √q z + √(1-q) ξ`, so the energy of the
interpolating system is a sum of the old energy, a function of the old configuration, and `u(θ)`,
a function of the new coordinate `ξ` and the shared Gaussian `z`. The Gibbs law of the extended
system is then a product, and:

* `integral_pi_tilted_cavityPath_pi_div_two` (2.37): for a function of the old configurations
  `(σ, ξ_{<M})` only, the extended average is the average `⟨f⟩_{t,∼}` of the old system;
* `integral_pi_tilted_cavityPath_pi_div_two_deriv_mul` (2.38): for two distinct replicas the
  average of `f u'(θ^1) u'(θ^2)` is `⟨f⟩_{t,∼}` times `ρ(z)`, where
  `ρ(z) = (E_ξ u'(θ) e^{u(θ)} / E_ξ e^{u(θ)})²`;
* `integral_integral_pi_tilted_cavityPath_pi_div_two_deriv_mul`: after averaging over the
  disorder and `z` (product law), the factor is `r̂ = E_z ρ(z)`, (2.36).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

/-- The squared, tilted Gaussian derivative averaged over the shared Gaussian, as in
Talagrand (2.36) and (2.68). -/
noncomputable def perceptronRhat (u : ℝ → ℝ) (q : ℝ) : ℝ :=
  ∫ z, ((∫ ξ, deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ) *
        Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1) /
      ∫ ξ, Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1) ^ 2
    ∂gaussianReal 0 1

theorem perceptronRhat_eq_integral_sq_integral_tilted (u : ℝ → ℝ) (q : ℝ) :
    perceptronRhat u q =
      ∫ z, (∫ ξ, deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)
          ∂((gaussianReal 0 1).tilted fun ξ => u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ))) ^ 2
        ∂gaussianReal 0 1 := by
  simp only [perceptronRhat, integral_tilted_eq_div]

variable {N M : ℕ} {μ : Measure (SmartPathState N (M + 1))} [IsFiniteMeasure μ] {u : ℝ → ℝ}
  {D : ℝ} (hu : Measurable u) (hD : ∀ x, u x ≤ D) (t q z : ℝ)
  (ω : SmartPathDisorder N (M + 1))

/-- At `s = π/2` the interpolating energy is a sum of the old energy and `u(θ)`. -/
theorem cavityPath_energy_pi_div_two :
    (fun p : SmartPathState N (M + 1) × ℝ =>
      smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
        u (Real.cos (Real.pi / 2) * smartPathField t ω p.1 (Fin.last M) +
          Real.sin (Real.pi / 2) * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2))) =
    fun p => smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2)
        (p.1.1, Fin.init p.1.2) + u (Real.sqrt q * z + Real.sqrt (1 - q) * p.2) := by
  funext p
  simp [Real.cos_pi_div_two, Real.sin_pi_div_two]

include hu hD in
/-- For a measurable potential bounded above, the Gibbs weight of the new coordinate is
integrable. -/
theorem integrable_exp_cavityPath_new :
    Integrable (fun ξ : ℝ => Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)))
      (gaussianReal 0 1) :=
  integrable_exp_of_ae_le (C := D)
    ((hu.comp (measurable_const.add (measurable_const.mul measurable_id))).aemeasurable)
    (Filter.Eventually.of_forall fun _ => hD _)

include hu hD in
/-- The Gibbs law of the new coordinate is a probability measure. -/
theorem isProbabilityMeasure_tilted_cavityPath_new :
    IsProbabilityMeasure ((gaussianReal 0 1).tilted
      fun ξ : ℝ => u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) :=
  isProbabilityMeasure_tilted (integrable_exp_cavityPath_new hu hD q z)

/-- **(2.37), at fixed disorder and `z`.** At `v = 0` the extended average of a function of the
old configurations is the average `⟨f⟩_{t,∼}` of the old system. -/
theorem integral_pi_tilted_cavityPath_pi_div_two {R : Type*} [Fintype R]
    (f : (R → SmartPathState N M) → ℝ)
    (hZ : Integrable (fun ξ : ℝ => Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)))
      (gaussianReal 0 1)) :
    ∫ σ : R → SmartPathState N (M + 1) × ℝ, f (fun r => ((σ r).1.1, Fin.init (σ r).1.2))
      ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted
        fun p : SmartPathState N (M + 1) × ℝ =>
          smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
            u (Real.cos (Real.pi / 2) * smartPathField t ω p.1 (Fin.last M) +
              Real.sin (Real.pi / 2) * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2))) =
      ∫ a : R → SmartPathState N (M + 1), f (fun r => ((a r).1, Fin.init (a r).2))
        ∂(Measure.pi fun _ : R => μ.tilted fun x : SmartPathState N (M + 1) =>
          smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2)) := by
  have := isProbabilityMeasure_tilted hZ
  rw [cavityPath_energy_pi_div_two t q z ω]
  have h := integral_pi_tilted_prod_add_mul (μ := μ) (ν := gaussianReal 0 1) (ι := R)
    (fun x : SmartPathState N (M + 1) =>
      smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2))
    (fun ξ : ℝ => u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ))
    (fun a => f (fun r => ((a r).1, Fin.init (a r).2))) (fun _ => 1)
  simpa using h

/-- **(2.38), at fixed disorder and `z`.** At `v = 0` and for two distinct replicas `i ≠ j`, the
extended average of `f u'(θ^i) u'(θ^j)` factorizes: it is `⟨f⟩_{t,∼}` times
`ρ(z) = (E_ξ u'(θ) e^{u(θ)} / E_ξ e^{u(θ)})²`, with `θ = √q z + √(1-q) ξ`. -/
theorem integral_pi_tilted_cavityPath_pi_div_two_deriv_mul {R : Type*} [Fintype R] {i j : R}
    (hij : i ≠ j) (f : (R → SmartPathState N M) → ℝ)
    (hZ : Integrable (fun ξ : ℝ => Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)))
      (gaussianReal 0 1)) :
    ∫ σ : R → SmartPathState N (M + 1) × ℝ, f (fun r => ((σ r).1.1, Fin.init (σ r).1.2)) *
        (deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * (σ i).2) *
          deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * (σ j).2))
      ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted
        fun p : SmartPathState N (M + 1) × ℝ =>
          smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
            u (Real.cos (Real.pi / 2) * smartPathField t ω p.1 (Fin.last M) +
              Real.sin (Real.pi / 2) * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2))) =
      (∫ a : R → SmartPathState N (M + 1), f (fun r => ((a r).1, Fin.init (a r).2))
        ∂(Measure.pi fun _ : R => μ.tilted fun x : SmartPathState N (M + 1) =>
          smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2))) *
      ((∫ ξ, deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ) *
          Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1) /
        ∫ ξ, Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1) ^ 2 := by
  have hprob := isProbabilityMeasure_tilted hZ
  rw [cavityPath_energy_pi_div_two t q z ω]
  have hθ : Measurable fun ξ : ℝ => deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ) :=
    (measurable_deriv u).comp (measurable_const.add (measurable_const.mul measurable_id))
  have h := integral_pi_tilted_prod_add_mul (μ := μ) (ν := gaussianReal 0 1) (ι := R)
    (fun x : SmartPathState N (M + 1) =>
      smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2))
    (fun ξ : ℝ => u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ))
    (fun a => f (fun r => ((a r).1, Fin.init (a r).2)))
    (fun τ => deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * τ i) *
      deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * τ j))
  rw [h, integral_pi_mul_of_ne _ hij hθ hθ, integral_tilted_eq_div, sq]

/-- **Lemma 2.3.1 (2.38), averaged over the disorder and `z`.** For the product law `P ⊗ 𝒩(0,1)` of
the disorder and the shared Gaussian `z`, the average of `f u'(θ^i) u'(θ^j)` under the extended
system at `v = 0` is `r̂` times the disorder average of `⟨f⟩_{t,∼}`, where
`r̂ = E_z (E_ξ u'(θ) e^{u(θ)} / E_ξ e^{u(θ)})²` is (2.36). -/
theorem integral_integral_pi_tilted_cavityPath_pi_div_two_deriv_mul {R : Type*} [Fintype R]
    {i j : R} (hij : i ≠ j) (f : SmartPathDisorder N (M + 1) → (R → SmartPathState N M) → ℝ)
    (P : Measure (SmartPathDisorder N (M + 1))) [SFinite P]
    (hZ : ∀ z : ℝ, Integrable (fun ξ : ℝ =>
      Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ))) (gaussianReal 0 1)) :
    ∫ p : SmartPathDisorder N (M + 1) × ℝ,
      (∫ σ : R → SmartPathState N (M + 1) × ℝ,
        f p.1 (fun r => ((σ r).1.1, Fin.init (σ r).1.2)) *
          (deriv u (Real.sqrt q * p.2 + Real.sqrt (1 - q) * (σ i).2) *
            deriv u (Real.sqrt q * p.2 + Real.sqrt (1 - q) * (σ j).2))
        ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted
          fun x : SmartPathState N (M + 1) × ℝ =>
            smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
              (x.1.1, Fin.init x.1.2) +
              u (Real.cos (Real.pi / 2) * smartPathField t p.1 x.1 (Fin.last M) +
                Real.sin (Real.pi / 2) * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2))))
      ∂(P.prod (gaussianReal 0 1)) =
    (perceptronRhat u q) *
      ∫ ω, (∫ a : R → SmartPathState N (M + 1), f ω (fun r => ((a r).1, Fin.init (a r).2))
        ∂(Measure.pi fun _ : R => μ.tilted fun x : SmartPathState N (M + 1) =>
          smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2))) ∂P := by
  simp_rw [integral_pi_tilted_cavityPath_pi_div_two_deriv_mul t q _ _ hij (f _) (hZ _)]
  exact (integral_prod_mul (μ := P) (ν := gaussianReal 0 1)
    (fun ω : SmartPathDisorder N (M + 1) =>
      ∫ a : R → SmartPathState N (M + 1), f ω (fun r => ((a r).1, Fin.init (a r).2))
        ∂(Measure.pi fun _ : R => μ.tilted fun x : SmartPathState N (M + 1) =>
          smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2)))
    (fun z : ℝ => ((∫ ξ, deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ) *
          Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1) /
        ∫ ξ, Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1) ^ 2)).trans
    (mul_comm _ _)

/-- **Lemma 2.3.1 (2.37), averaged over the disorder and `z`.** -/
theorem integral_integral_pi_tilted_cavityPath_pi_div_two {R : Type*} [Fintype R]
    (f : SmartPathDisorder N (M + 1) → (R → SmartPathState N M) → ℝ)
    (P : Measure (SmartPathDisorder N (M + 1))) [SFinite P]
    (hZ : ∀ z : ℝ, Integrable (fun ξ : ℝ =>
      Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ))) (gaussianReal 0 1)) :
    ∫ p : SmartPathDisorder N (M + 1) × ℝ,
      (∫ σ : R → SmartPathState N (M + 1) × ℝ, f p.1 (fun r => ((σ r).1.1, Fin.init (σ r).1.2))
        ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted
          fun x : SmartPathState N (M + 1) × ℝ =>
            smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
              (x.1.1, Fin.init x.1.2) +
              u (Real.cos (Real.pi / 2) * smartPathField t p.1 x.1 (Fin.last M) +
                Real.sin (Real.pi / 2) * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2))))
      ∂(P.prod (gaussianReal 0 1)) =
    ∫ ω, (∫ a : R → SmartPathState N (M + 1), f ω (fun r => ((a r).1, Fin.init (a r).2))
        ∂(Measure.pi fun _ : R => μ.tilted fun x : SmartPathState N (M + 1) =>
          smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2))) ∂P := by
  simp_rw [integral_pi_tilted_cavityPath_pi_div_two t q _ _ (f _) (hZ _)]
  exact integral_prod_fun_fst_of_isProbabilityMeasure (E := ℝ) P (gaussianReal 0 1)
    (fun ω : SmartPathDisorder N (M + 1) =>
      ∫ a : R → SmartPathState N (M + 1), f ω (fun r => ((a r).1, Fin.init (a r).2))
        ∂(Measure.pi fun _ : R => μ.tilted fun x : SmartPathState N (M + 1) =>
          smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2)))

/-- **The constant `r̂` of (2.36) lies in `[0, D²]`** when `|u'| ≤ D`: it is the average of a square
of a Gibbs average of `u'`. -/
theorem rhat_mem_Icc {D' : ℝ} (hD' : ∀ x, |deriv u x| ≤ D') (q : ℝ)
    (hZ : ∀ z : ℝ, Integrable (fun ξ : ℝ =>
      Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ))) (gaussianReal 0 1)) :
    0 ≤ perceptronRhat u q ∧ perceptronRhat u q ≤ D' ^ 2 := by
  rw [perceptronRhat_eq_integral_sq_integral_tilted]
  refine ⟨integral_nonneg fun z => sq_nonneg _, ?_⟩
  have hb (z : ℝ) : |(∫ ξ, deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)
        ∂((gaussianReal 0 1).tilted fun ξ => u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ))) ^ 2| ≤
      D' ^ 2 := by
    have hprob := isProbabilityMeasure_tilted (hZ z)
    have h := abs_integral_le_of_forall_abs_le
      ((gaussianReal 0 1).tilted fun ξ : ℝ => u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ))
      (f := fun ξ => deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) (M := D')
      fun ξ => hD' _
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  exact (le_abs_self _).trans (abs_integral_le_of_forall_abs_le (gaussianReal 0 1) hb)

end SpinGlasses
