/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaComparison
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityPath

/-!
# Lemma 2.3.4: comparison of the interpolating systems

Talagrand Section 2.3, (2.61). For a nonnegative observable `f` of `n` replicas of the spins, the
average under the interpolating system at any angle `s₁` is at most `exp (4 n D)` times the average
at any other angle `s₂`, where `|u| ≤ D`: the two energies differ only by `u (S_{s₁}) - u (S_{s₂})`,
bounded by `2 D`. This is a pointwise comparison of Gibbs weights, so no derivative estimate is
needed.

* `SpinGlasses.integral_pi_tilted_cavityPath_le_exp_mul`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

variable {N M : ℕ} {u : ℝ → ℝ} {D : ℝ}

/-- **Lemma 2.3.4, Eq. (2.61).** For `f ≥ 0` a function of the spins of `R` replicas, the replica
average at angle `s₁` is at most `exp (4 |R| D)` times the one at angle `s₂`. -/
theorem integral_pi_tilted_cavityPath_le_exp_mul (hu : Measurable u) (hD : ∀ x, |u x| ≤ D)
    (t q z s₁ s₂ : ℝ) (ω : SmartPathDisorder N (M + 1)) {R : Type*} [Fintype R] [DecidableEq R]
    (f : (R → PerceptronSpin N) → ℝ) (hf0 : ∀ σ, 0 ≤ f σ) :
    ∫ σ : R → SmartPathState N (M + 1) × ℝ, f (fun r => (σ r).1.1)
      ∂(Measure.pi fun _ : R => ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
        fun p : SmartPathState N (M + 1) × ℝ =>
          smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
            u (Real.cos s₁ * smartPathField t ω p.1 (Fin.last M) +
              Real.sin s₁ * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2))) ≤
      Real.exp (4 * Fintype.card R * D) *
      ∫ σ : R → SmartPathState N (M + 1) × ℝ, f (fun r => (σ r).1.1)
        ∂(Measure.pi fun _ : R => ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
          fun p : SmartPathState N (M + 1) × ℝ =>
            smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
              u (Real.cos s₂ * smartPathField t ω p.1 (Fin.last M) +
                Real.sin s₂ * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2))) := by
  have hD' : ∀ x, u x ≤ D := fun x => le_of_abs_le (hD x)
  have hE : ∀ s : ℝ, Measurable fun p : SmartPathState N (M + 1) × ℝ =>
      smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
        u (Real.cos s * smartPathField t ω p.1 (Fin.last M) +
          Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2)) := fun s =>
    ((measurable_smartPathEnergy_init hu t ω).comp measurable_fst).add
      (hu.comp ((measurable_const.mul ((measurable_smartPathField_slice t ω (Fin.last M)).comp
        measurable_fst)).add (measurable_const.mul (by fun_prop))))
  have hexp : Integrable (fun p : SmartPathState N (M + 1) × ℝ => Real.exp
      (smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
        u (Real.cos s₂ * smartPathField t ω p.1 (Fin.last M) +
          Real.sin s₂ * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2))))
      ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)) :=
    integrable_exp_of_ae_le (C := (M * D + Real.sqrt (1 - t) * |ω.2|) + D) (hE s₂).aemeasurable
      (ae_of_all _ fun p => add_le_add (smartPathEnergy_init_le hD' t ω p.1) (hD' _))
  have hfm : Measurable fun σ : R → SmartPathState N (M + 1) × ℝ => f (fun r => (σ r).1.1) :=
    (measurable_of_finite f).comp (by fun_prop)
  have hfi : Integrable (fun σ : R → SmartPathState N (M + 1) × ℝ => f (fun r => (σ r).1.1))
      (Measure.pi fun _ : R => ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
        fun p : SmartPathState N (M + 1) × ℝ =>
          smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
            u (Real.cos s₂ * smartPathField t ω p.1 (Fin.last M) +
              Real.sin s₂ * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2))) :=
    Integrable.of_bound (C := ∑ σ, |f σ|) hfm.aestronglyMeasurable (ae_of_all _ fun σ => by
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun σ => |f σ|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ _))
  have hCb : ∀ p : SmartPathState N (M + 1) × ℝ,
      |(smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
        u (Real.cos s₁ * smartPathField t ω p.1 (Fin.last M) +
          Real.sin s₁ * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2))) -
      (smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
        u (Real.cos s₂ * smartPathField t ω p.1 (Fin.last M) +
          Real.sin s₂ * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2)))| ≤ 2 * D := fun p => by
    rw [add_sub_add_left_eq_sub]
    refine (abs_sub _ _).trans ?_
    linarith [hD (Real.cos s₁ * smartPathField t ω p.1 (Fin.last M) +
        Real.sin s₁ * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2)),
      hD (Real.cos s₂ * smartPathField t ω p.1 (Fin.last M) +
        Real.sin s₂ * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2))]
  have key := integral_pi_tilted_le_exp_mul_of_abs_sub_le (ι := R)
    (μ := (smartPathBase N (M + 1)).prod (gaussianReal 0 1)) hexp
    (E₁ := fun p : SmartPathState N (M + 1) × ℝ =>
      smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
        u (Real.cos s₁ * smartPathField t ω p.1 (Fin.last M) +
          Real.sin s₁ * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2)))
    (((hE s₁).sub (hE s₂))) hCb (Y := fun σ : R → SmartPathState N (M + 1) × ℝ =>
      f (fun r => (σ r).1.1)) (fun σ => hf0 _) hfi
  convert key using 3
  ring

/-- **Lemma 2.3.4, Eq. (2.61), integrated over the disorder.** For a probability law `P` of the
disorder `ω` and the common Gaussian `z`, and a bounded nonnegative observable `F ω z f` of the
spins of `R` replicas (which may depend on the disorder and on `z`), the disorder average at angle
`s₁` of the replica Gibbs average is at most `exp (4 |R| D)` times the one at angle `s₂`. -/
theorem integral_integral_pi_tilted_cavityPath_le_exp_mul (hu : Measurable u)
    (hD : ∀ x, |u x| ≤ D) (t q s₁ s₂ : ℝ)
    {P : Measure (SmartPathDisorder N (M + 1) × ℝ)} [IsProbabilityMeasure P]
    {R : Type*} [Fintype R]
    {F : SmartPathDisorder N (M + 1) × ℝ → (R → PerceptronSpin N) → ℝ}
    (hF : Measurable fun p : (SmartPathDisorder N (M + 1) × ℝ) × (R → PerceptronSpin N) =>
      F p.1 p.2) {K : ℝ} (hF0 : ∀ p f, 0 ≤ F p f) (hFb : ∀ p f, F p f ≤ K) :
    ∫ p, ∫ σ : R → SmartPathState N (M + 1) × ℝ, F p (fun r => (σ r).1.1)
      ∂(Measure.pi fun _ : R => ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
        fun x : SmartPathState N (M + 1) × ℝ =>
          smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
            (x.1.1, Fin.init x.1.2) +
            u (Real.cos s₁ * smartPathField t p.1 x.1 (Fin.last M) +
              Real.sin s₁ * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2))) ∂P ≤
      Real.exp (4 * Fintype.card R * D) *
      ∫ p, ∫ σ : R → SmartPathState N (M + 1) × ℝ, F p (fun r => (σ r).1.1)
        ∂(Measure.pi fun _ : R => ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
          fun x : SmartPathState N (M + 1) × ℝ =>
            smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
              (x.1.1, Fin.init x.1.2) +
              u (Real.cos s₂ * smartPathField t p.1 x.1 (Fin.last M) +
                Real.sin s₂ * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2))) ∂P := by
  have hD' : ∀ x, u x ≤ D := fun x => le_of_abs_le (hD x)
  have hE : ∀ s : ℝ, Measurable fun r : (SmartPathDisorder N (M + 1) × ℝ) ×
      (SmartPathState N (M + 1) × ℝ) =>
      smartPathEnergy u t ((Fin.init r.1.1.1.1, Fin.init r.1.1.1.2), r.1.1.2)
        (r.2.1.1, Fin.init r.2.1.2) +
        u (Real.cos s * smartPathField t r.1.1 r.2.1 (Fin.last M) +
          Real.sin s * (Real.sqrt q * r.1.2 + Real.sqrt (1 - q) * r.2.2)) := fun s => by
    have hr : Measurable fun r : (SmartPathDisorder N (M + 1) × ℝ) ×
        (SmartPathState N (M + 1) × ℝ) =>
        ((r.1.1, r.2.1) : SmartPathDisorder N (M + 1) × SmartPathState N (M + 1)) :=
      (measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)
    have h1 := (measurable_smartPathEnergy_init_joint (N := N) (M := M) hu t).comp hr
    have h2 := (measurable_smartPathField (N := N) (M := M + 1) t (Fin.last M)).comp hr
    exact h1.add (hu.comp ((measurable_const.mul h2).add (measurable_const.mul (by fun_prop))))
  have hB : ∀ (s : ℝ) (p : SmartPathDisorder N (M + 1) × ℝ) (x : SmartPathState N (M + 1) × ℝ),
      smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2) (x.1.1, Fin.init x.1.2) +
        u (Real.cos s * smartPathField t p.1 x.1 (Fin.last M) +
          Real.sin s * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2)) ≤
      (M * D + Real.sqrt (1 - t) * |p.1.2|) + D := fun s p x =>
    add_le_add (smartPathEnergy_init_le hD' t p.1 x.1) (hD' _)
  have hC : ∀ (p : SmartPathDisorder N (M + 1) × ℝ) (x : SmartPathState N (M + 1) × ℝ),
      |(smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
          (x.1.1, Fin.init x.1.2) +
        u (Real.cos s₁ * smartPathField t p.1 x.1 (Fin.last M) +
          Real.sin s₁ * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2))) -
      (smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
          (x.1.1, Fin.init x.1.2) +
        u (Real.cos s₂ * smartPathField t p.1 x.1 (Fin.last M) +
          Real.sin s₂ * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2)))| ≤ 2 * D := fun p x => by
    rw [add_sub_add_left_eq_sub]
    refine (abs_sub _ _).trans ?_
    linarith [hD (Real.cos s₁ * smartPathField t p.1 x.1 (Fin.last M) +
        Real.sin s₁ * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2)),
      hD (Real.cos s₂ * smartPathField t p.1 x.1 (Fin.last M) +
        Real.sin s₂ * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2))]
  have hG : Measurable fun r : (SmartPathDisorder N (M + 1) × ℝ) ×
      (R → SmartPathState N (M + 1) × ℝ) => F r.1 (fun i => (r.2 i).1.1) := by
    have hmap : Measurable fun r : (SmartPathDisorder N (M + 1) × ℝ) ×
        (R → SmartPathState N (M + 1) × ℝ) =>
        ((r.1, fun i => (r.2 i).1.1) : (SmartPathDisorder N (M + 1) × ℝ) ×
          (R → PerceptronSpin N)) :=
      measurable_fst.prodMk (measurable_pi_iff.2 fun i =>
        (measurable_fst.comp measurable_fst).comp ((measurable_pi_apply i).comp measurable_snd))
    exact (hF.comp hmap : _)
  have key := integral_integral_pi_tilted_le_exp_mul_of_abs_sub_le (ι := R)
    (μ := (smartPathBase N (M + 1)).prod (gaussianReal 0 1)) (P := P)
    (E₁ := fun p x => smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
        (x.1.1, Fin.init x.1.2) +
        u (Real.cos s₁ * smartPathField t p.1 x.1 (Fin.last M) +
          Real.sin s₁ * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2)))
    (E₀ := fun p x => smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
        (x.1.1, Fin.init x.1.2) +
        u (Real.cos s₂ * smartPathField t p.1 x.1 (Fin.last M) +
          Real.sin s₂ * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2)))
    (hE s₂) (hE s₁) (B := fun p => (M * D + Real.sqrt (1 - t) * |p.1.2|) + D)
    (hB s₂) (hB s₁) (C := 2 * D) hC (G := fun p σ => F p (fun i => (σ i).1.1)) hG (M := K)
    (fun p σ => hF0 _ _) (fun p σ => hFb _ _)
  have e : 2 * (Fintype.card R : ℝ) * (2 * D) = 4 * Fintype.card R * D := by ring
  rw [e] at key
  exact key

end SpinGlasses
