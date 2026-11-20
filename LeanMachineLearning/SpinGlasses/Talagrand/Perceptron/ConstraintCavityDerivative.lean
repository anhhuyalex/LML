/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaRotation
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityPath
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathDifferentiation

/-!
# The pathwise `s`-derivative of the cavity average

Talagrand Section 2.3, the first step of Lemma 2.3.2 (the formula (2.41) for `B_v ≡ 1`). At fixed
disorder `ω` and fixed `z` the average `⟨f⟩_{t,s}` of the interpolating system is differentiable in
the path parameter `s`, with derivative the covariance of `f` with the sum over replicas of
`u'(S_s) z̃`, where `S_s = cos s S_{M,t} + sin s θ` and `z̃ = -sin s S_{M,t} + cos s θ`.

* `integrable_abs_smartPathField_smartPathBase`: the field is integrable under the smart-path base;
* `hasDerivAt_integral_pi_tilted_cavityPath`: the derivative, for a bounded measurable `f`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

variable {N M : ℕ}

/-- The absolute value of the smart-path field is integrable under the smart-path base law: the
quenched part depends only on the (finitely many) spins and the auxiliary part is Gaussian. -/
theorem integrable_abs_smartPathField_smartPathBase (t : ℝ) (ω : SmartPathDisorder N M)
    (k : Fin M) : Integrable (fun x : SmartPathState N M => |smartPathField t ω x k|)
      (smartPathBase N M) := by
  have h1 : Integrable (fun x : SmartPathState N M => |smartPathFieldNoAux t ω x k|)
      (smartPathBase N M) := by
    have : Integrable (fun a : PerceptronSpin N =>
        |smartPathFieldNoAux t ω (a, (0 : Fin M → ℝ)) k|)
        (Measure.count : Measure (PerceptronSpin N)) := Integrable.of_finite
    simpa [smartPathFieldNoAux_eq, smartPathBase_eq] using
      this.comp_fst (Measure.pi fun _ : Fin M => gaussianReal 0 1)
  refine (h1.add ((integrable_abs_snd_smartPathBase (N := N) (M := M) k).const_mul
    (Real.sqrt ((1 - t) / (N + 1))))).mono'
    (continuous_abs.measurable.comp (measurable_smartPathField_slice t ω k)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_abs, smartPathField_eq]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact le_rfl

section Derivative

variable {μ : Measure (SmartPathState N (M + 1))} [IsFiniteMeasure μ] [NeZero μ] {u : ℝ → ℝ}
  {D D₁ t : ℝ} (ω : SmartPathDisorder N (M + 1))

/-- **The pathwise `s`-derivative of the cavity average (the formula (2.41) for `B_v ≡ 1`).** At
fixed disorder `ω` and fixed `z`, for a bounded measurable observable `f` of `R` replicas of the
extended configuration `(x, ξ)`, the derivative at `s₀` of `⟨f⟩_{t,s}` is
`⟨f ∑ᵢ u'(S^i) z̃^i⟩ - ⟨f⟩ ⟨∑ᵢ u'(S^i) z̃^i⟩`, with `S = cos s₀ S_{M,t} + sin s₀ θ` and
`z̃ = -sin s₀ S_{M,t} + cos s₀ θ`, `θ = √q z + √(1-q) ξ`. The hypotheses are the upper bound
`u ≤ D`, `|u'| ≤ D₁`, and integrability of the field `S_{M,t}` under the base law; the Gaussian
factor `z̃` is unbounded and is dominated by `|S_{M,t}| + |θ|`. -/
theorem hasDerivAt_integral_pi_tilted_cavityPath (hu : Differentiable ℝ u) (hD : ∀ x, u x ≤ D)
    (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (hX : Integrable (fun x : SmartPathState N (M + 1) =>
      |smartPathField t ω x (Fin.last M)|) μ) (q z : ℝ)
    {R : Type*} [Fintype R] {f : (R → SmartPathState N (M + 1) × ℝ) → ℝ} (hf : Measurable f)
    {C : ℝ} (hfb : ∀ σ, |f σ| ≤ C) (s₀ : ℝ) :
    HasDerivAt (fun s => ∫ σ, f σ ∂(Measure.pi fun _ : R =>
        (μ.prod (gaussianReal 0 1)).tilted fun p : SmartPathState N (M + 1) × ℝ =>
          smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
            u (Real.cos s * smartPathField t ω p.1 (Fin.last M) +
              Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2))))
      ((∫ σ, f σ * ∑ i, (deriv u (Real.cos s₀ * smartPathField t ω (σ i).1 (Fin.last M) +
            Real.sin s₀ * (Real.sqrt q * z + Real.sqrt (1 - q) * (σ i).2)) *
          (-Real.sin s₀ * smartPathField t ω (σ i).1 (Fin.last M) +
            Real.cos s₀ * (Real.sqrt q * z + Real.sqrt (1 - q) * (σ i).2)))
          ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted
            fun p : SmartPathState N (M + 1) × ℝ =>
              smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
                u (Real.cos s₀ * smartPathField t ω p.1 (Fin.last M) +
                  Real.sin s₀ * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2)))) -
        (∫ σ, f σ ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted
            fun p : SmartPathState N (M + 1) × ℝ =>
              smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
                u (Real.cos s₀ * smartPathField t ω p.1 (Fin.last M) +
                  Real.sin s₀ * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2)))) *
          ∫ σ, ∑ i, (deriv u (Real.cos s₀ * smartPathField t ω (σ i).1 (Fin.last M) +
              Real.sin s₀ * (Real.sqrt q * z + Real.sqrt (1 - q) * (σ i).2)) *
            (-Real.sin s₀ * smartPathField t ω (σ i).1 (Fin.last M) +
              Real.cos s₀ * (Real.sqrt q * z + Real.sqrt (1 - q) * (σ i).2)))
            ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted
              fun p : SmartPathState N (M + 1) × ℝ =>
                smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2)
                  (p.1.1, Fin.init p.1.2) +
                  u (Real.cos s₀ * smartPathField t ω p.1 (Fin.last M) +
                    Real.sin s₀ * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2)))) s₀ := by
  have hum : Measurable u := hu.continuous.measurable
  have hθ : Integrable (fun ξ : ℝ => |Real.sqrt q * z + Real.sqrt (1 - q) * ξ|)
      (gaussianReal 0 1) := by
    have h1 : Integrable (fun ξ : ℝ => |ξ|) (gaussianReal 0 1) :=
      integrable_abs_id_gaussianReal (m := 0) (v := 1)
    refine ((integrable_const |Real.sqrt q * z|).add (h1.const_mul (Real.sqrt (1 - q)))).mono'
      (by fun_prop) (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    refine (abs_add_le _ _).trans ?_
    simp only [Pi.add_apply, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), le_refl]
  have hint : Integrable (fun p : SmartPathState N (M + 1) × ℝ =>
      |smartPathField t ω p.1 (Fin.last M)| +
        |Real.sqrt q * z + Real.sqrt (1 - q) * p.2|) (μ.prod (gaussianReal 0 1)) :=
    (hX.comp_fst (gaussianReal 0 1)).add (hθ.comp_snd μ)
  exact hasDerivAt_integral_pi_tilted_rotation (ρ := μ.prod (gaussianReal 0 1))
    (E₀ := fun p : SmartPathState N (M + 1) × ℝ =>
      smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2))
    (X := fun p => smartPathField t ω p.1 (Fin.last M))
    (Y := fun p => Real.sqrt q * z + Real.sqrt (1 - q) * p.2)
    ((measurable_smartPathEnergy_init hum t ω).comp measurable_fst)
    ((measurable_smartPathField_slice t ω (Fin.last M)).comp measurable_fst)
    (by fun_prop) hu (B₀ := M * D + Real.sqrt (1 - t) * |ω.2|) (B₁ := D)
    (fun p => smartPathEnergy_init_le hD t ω p.1) hD hD₁ hint hf hfb s₀

end Derivative

section DerivativeMul

variable {μ : Measure (SmartPathState N (M + 1))} [IsFiniteMeasure μ] [NeZero μ] {u : ℝ → ℝ}
  {D D₁ D₂ t : ℝ} (ω : SmartPathDisorder N (M + 1))

/-- **The pathwise derivative with the moving factor `u'(S_s^i) u'(S_s^j)`** (the formula (2.41) for
`B_v = u'(S_v^1) u'(S_v^2)`). The observable moves with `s` and its derivative contains the
unbounded Gaussian factor `z̃`; it is dominated by `C D₁ D₂ (w(σ_i) + w(σ_j))` with
`w = |S_{M,t}| + |θ|`, so only `|u''| ≤ D₂` is needed in addition to the hypotheses of
`hasDerivAt_integral_pi_tilted_cavityPath`. -/
theorem hasDerivAt_integral_pi_tilted_cavityPath_deriv_mul (hu : Differentiable ℝ u)
    (hu₂ : Differentiable ℝ (deriv u)) (hD : ∀ x, u x ≤ D) (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂)
    (hX : Integrable (fun x : SmartPathState N (M + 1) =>
      |smartPathField t ω x (Fin.last M)|) μ) (q z : ℝ)
    {R : Type*} [Fintype R] (i j : R) {f : (R → SmartPathState N (M + 1) × ℝ) → ℝ}
    (hf : Measurable f) {C : ℝ} (hfb : ∀ σ, |f σ| ≤ C) (s₀ : ℝ) :
    HasDerivAt (fun s => ∫ σ, f σ * (deriv u (Real.cos s * smartPathField t ω (σ i).1
      (Fin.last M) + Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * (σ i).2)) *
        deriv u (Real.cos s * smartPathField t ω (σ j).1 (Fin.last M) + Real.sin s *
          (Real.sqrt q * z + Real.sqrt (1 - q) * (σ j).2))) ∂(Measure.pi fun _ : R =>
        (μ.prod (gaussianReal 0 1)).tilted fun p : SmartPathState N (M + 1) × ℝ =>
            smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
              u (Real.cos s * smartPathField t ω p.1 (Fin.last M) +
                Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2))))
      ((∫ σ, f σ * (deriv (deriv u) (Real.cos s₀ * smartPathField t ω (σ i).1 (Fin.last M) +
        Real.sin s₀ * (Real.sqrt q * z + Real.sqrt (1 - q) * (σ i).2)) *
          (-Real.sin s₀ * smartPathField t ω (σ i).1 (Fin.last M) + Real.cos s₀ * (Real.sqrt q *
            z + Real.sqrt (1 - q) * (σ i).2)) *
          deriv u (Real.cos s₀ * smartPathField t ω (σ j).1 (Fin.last M) + Real.sin s₀ *
            (Real.sqrt q * z + Real.sqrt (1 - q) * (σ j).2)) +
        deriv u (Real.cos s₀ * smartPathField t ω (σ i).1 (Fin.last M) + Real.sin s₀ *
          (Real.sqrt q * z + Real.sqrt (1 - q) * (σ i).2)) *
          (deriv (deriv u) (Real.cos s₀ * smartPathField t ω (σ j).1 (Fin.last M) + Real.sin s₀ *
            (Real.sqrt q * z + Real.sqrt (1 - q) * (σ j).2)) *
            (-Real.sin s₀ * smartPathField t ω (σ j).1 (Fin.last M) + Real.cos s₀ * (Real.sqrt q *
              z + Real.sqrt (1 - q) * (σ j).2))))
          ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted fun p : SmartPathState N
            (M + 1) × ℝ =>
            smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
              u (Real.cos s₀ * smartPathField t ω p.1 (Fin.last M) +
                Real.sin s₀ * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2)))) +
      ((∫ σ, f σ * (deriv u (Real.cos s₀ * smartPathField t ω (σ i).1 (Fin.last M) + Real.sin s₀ *
        (Real.sqrt q * z + Real.sqrt (1 - q) * (σ i).2)) *
          deriv u (Real.cos s₀ * smartPathField t ω (σ j).1 (Fin.last M) + Real.sin s₀ *
            (Real.sqrt q * z + Real.sqrt (1 - q) * (σ j).2))) *
          ∑ k, (deriv u (Real.cos s₀ * smartPathField t ω (σ k).1 (Fin.last M) + Real.sin s₀ *
            (Real.sqrt q * z + Real.sqrt (1 - q) * (σ k).2)) *
            (-Real.sin s₀ * smartPathField t ω (σ k).1 (Fin.last M) + Real.cos s₀ * (Real.sqrt q *
              z + Real.sqrt (1 - q) * (σ k).2)))
          ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted fun p : SmartPathState N
            (M + 1) × ℝ =>
            smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
              u (Real.cos s₀ * smartPathField t ω p.1 (Fin.last M) +
                Real.sin s₀ * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2)))) -
        (∫ σ, f σ * (deriv u (Real.cos s₀ * smartPathField t ω (σ i).1 (Fin.last M) +
          Real.sin s₀ * (Real.sqrt q * z + Real.sqrt (1 - q) * (σ i).2)) *
          deriv u (Real.cos s₀ * smartPathField t ω (σ j).1 (Fin.last M) + Real.sin s₀ *
            (Real.sqrt q * z + Real.sqrt (1 - q) * (σ j).2)))
          ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted fun p : SmartPathState N
            (M + 1) × ℝ =>
            smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
              u (Real.cos s₀ * smartPathField t ω p.1 (Fin.last M) +
                Real.sin s₀ * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2)))) *
          ∫ σ, ∑ k, (deriv u (Real.cos s₀ * smartPathField t ω (σ k).1 (Fin.last M) +
            Real.sin s₀ * (Real.sqrt q * z + Real.sqrt (1 - q) * (σ k).2)) *
            (-Real.sin s₀ * smartPathField t ω (σ k).1 (Fin.last M) + Real.cos s₀ * (Real.sqrt q *
              z + Real.sqrt (1 - q) * (σ k).2)))
            ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted fun p : SmartPathState N
              (M + 1) × ℝ =>
            smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
              u (Real.cos s₀ * smartPathField t ω p.1 (Fin.last M) +
                Real.sin s₀ * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2))))) s₀ := by
  have hum : Measurable u := hu.continuous.measurable
  have hθ : Integrable (fun ξ : ℝ => |Real.sqrt q * z + Real.sqrt (1 - q) * ξ|)
      (gaussianReal 0 1) := by
    have h1 : Integrable (fun ξ : ℝ => |ξ|) (gaussianReal 0 1) :=
      integrable_abs_id_gaussianReal (m := 0) (v := 1)
    refine ((integrable_const |Real.sqrt q * z|).add (h1.const_mul (Real.sqrt (1 - q)))).mono'
      (by fun_prop) (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    refine (abs_add_le _ _).trans ?_
    simp only [Pi.add_apply, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), le_refl]
  have hint : Integrable (fun p : SmartPathState N (M + 1) × ℝ =>
      |smartPathField t ω p.1 (Fin.last M)| +
        |Real.sqrt q * z + Real.sqrt (1 - q) * p.2|) (μ.prod (gaussianReal 0 1)) :=
    (hX.comp_fst (gaussianReal 0 1)).add (hθ.comp_snd μ)
  exact hasDerivAt_integral_pi_tilted_rotation_deriv_mul (ρ := μ.prod (gaussianReal 0 1))
    (E₀ := fun p : SmartPathState N (M + 1) × ℝ =>
      smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2))
    (X := fun p => smartPathField t ω p.1 (Fin.last M))
    (Y := fun p => Real.sqrt q * z + Real.sqrt (1 - q) * p.2)
    ((measurable_smartPathEnergy_init hum t ω).comp measurable_fst)
    ((measurable_smartPathField_slice t ω (Fin.last M)).comp measurable_fst)
    (by fun_prop) hu hu₂ (B₀ := M * D + Real.sqrt (1 - t) * |ω.2|) (B₁ := D)
    (fun p => smartPathEnergy_init_le hD t ω p.1) hD hD₁ hD₂ hint hf hfb i j s₀

end DerivativeMul

end SpinGlasses
