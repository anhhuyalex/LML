/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaComparison
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityPath
public import
  LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityInterpolationBound

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
open scoped BigOperators NNReal ENNReal

universe uR

namespace SpinGlasses

section Comparison

variable {N M : ℕ} {u : ℝ → ℝ} {D : ℝ}

/-- **Lemma 2.3.4, Eq. (2.61).** For `f ≥ 0` a function of the spins of `R` replicas, the replica
average at angle `s₁` is at most `exp (4 |R| D)` times the one at angle `s₂`. -/
theorem integral_pi_tilted_cavityPath_le_exp_mul (hu : Measurable u) (hD : ∀ x, |u x| ≤ D)
    (t q z s₁ s₂ : ℝ) (ω : SmartPathDisorder N (M + 1)) {R : Type*} [Fintype R]
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
  classical
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

end Comparison

theorem integral_pi_cavity_rotation_nonneg_le_exp_mul
    {N M : ℕ} {R : Type uR} [Fintype R]
    {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    (t q s₁ s₂ : ℝ) (variance : ℝ≥0)
    {g : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
    (hg : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => g p.1 p.2)
    (hg0 : ∀ ω a, 0 ≤ g ω a) :
    let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
    let μ₀ (ω : SmartPathDisorder N M) :=
      (smartPathBase N M).tilted (smartPathEnergy u t ω)
    let γ_sh := Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : Fin 2 => gaussianReal 0 1
    let X : PerceptronSpin N → (Fin N ⊕ Unit) ⊕ Unit → ℝ :=
      fun σ => Sum.elim (cavityCoef N t σ) 0
    let Y : (Fin N ⊕ Unit) ⊕ Unit → ℝ := Sum.elim 0 (fun _ => Real.sqrt q)
    let A : Fin 2 → ℝ := Pi.single 0 (Real.sqrt ((1 - t) / (N + 1)))
    let E : Fin 2 → ℝ := Pi.single 1 (Real.sqrt (1 - q))
    let S (s : ℝ) (w : (Fin N ⊕ Unit) ⊕ Unit → ℝ)
        (x : SmartPathState N M × (Fin 2 → ℝ)) : ℝ :=
      Real.cos s * (X x.1.1 ⬝ᵥ w + A ⬝ᵥ x.2) +
        Real.sin s * (Y ⬝ᵥ w + E ⬝ᵥ x.2)
    let ν (s : ℝ) (p : SmartPathDisorder N M × ((Fin N ⊕ Unit) ⊕ Unit → ℝ)) :=
      ((μ₀ p.1).prod γ_aux).tilted fun x => u (S s p.2 x)
    (∀ᵐ ω ∂P₀, Integrable (g ω) (Measure.pi fun _ : R => μ₀ ω)) →
    Integrable (fun ω => ∫ a, g ω a ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ →
    ∫ p, ∫ a : R → SmartPathState N M × (Fin 2 → ℝ),
        g p.1 (fun r => (a r).1) ∂(Measure.pi fun _ : R => ν s₁ p) ∂(P₀.prod γ_sh) ≤
      Real.exp (4 * Fintype.card R * B) *
      ∫ p, ∫ a : R → SmartPathState N M × (Fin 2 → ℝ),
        g p.1 (fun r => (a r).1) ∂(Measure.pi fun _ : R => ν s₂ p) ∂(P₀.prod γ_sh) := by
  intro P₀ μ₀ γ_sh γ_aux X Y A E S ν hgi hgi₁
  have hB' : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  let Ω := SmartPathDisorder N M
  let W := (Fin N ⊕ Unit) ⊕ Unit → ℝ
  let T := SmartPathState N M × (Fin 2 → ℝ)
  let G (p : Ω × W) (a : R → T) := g p.1 (fun r => (a r).1)
  have hGm : Measurable fun p : (Ω × W) × (R → T) => G p.1 p.2 := by
    have hp : Measurable fun p : (Ω × W) × (R → T) =>
        ((p.1.1, fun r => (p.2 r).1) : Ω × (R → SmartPathState N M)) :=
      (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
    have h := hg.comp hp
    exact h
  have hV (s : ℝ) (p : Ω × W) : Measurable fun x : T => u (S s p.2 x) := by
    have hs := measurable_cavity_rotation_field (N := N) (M := M) t q s
    have hp : Measurable fun x : T => (p.2, x) := measurable_const.prodMk measurable_id
    have h := hu.comp (hs.comp hp)
    exact h
  have hμ (ω : Ω) : IsProbabilityMeasure (μ₀ ω) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy (μ := smartPathBase N M)
      hu hB' ω t
  have hgi_abs : Integrable (fun ω => ∫ a, |g ω a| ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ := by
    simpa only [abs_of_nonneg (hg0 _ _)] using hgi₁
  have hint_s (s : ℝ) :
      (∀ᵐ p ∂P₀.prod γ_sh, Integrable (G p) (Measure.pi fun _ : R => ν s p)) ∧
      Integrable (fun p => ∫ a, G p a ∂(Measure.pi fun _ : R => ν s p)) (P₀.prod γ_sh) := by
    have : ∀ p, IsProbabilityMeasure (ν s p) := fun p =>
      isProbabilityMeasure_tilted_of_ae_le (hV s p).aemeasurable (ae_of_all _ fun _ => hB' _)
    have hlift : ∀ᵐ p ∂P₀.prod γ_sh,
        Integrable (fun a => |G p a|) (Measure.pi fun _ : R => ν s p) ∧
          (∫ a, |G p a| ∂(Measure.pi fun _ : R => ν s p)) ≤
            Real.exp (2 * (Fintype.card R : ℝ) * B) *
              ∫ a, |g p.1 a| ∂(Measure.pi fun _ : R => μ₀ p.1) :=
      (Measure.quasiMeasurePreserving_fst (μ := P₀) (ν := γ_sh)).ae hgi |>.mono fun p hp =>
        integrable_pi_tilted_prod_fst_abs_and_le (μ₀ p.1) γ_aux (hV s p) (fun _ => hB _)
          Function.injective_id hp
    have h1 : ∀ᵐ p ∂P₀.prod γ_sh, Integrable (G p) (Measure.pi fun _ : R => ν s p) :=
      hlift.mono fun p hp => by
        simpa only [G, abs_of_nonneg (hg0 _ _)] using hp.1
    have hJm := measurable_integral_pi_cavity_rotation t q s hu hB' (F := G) hGm
    have hI := (hgi_abs.comp_fst γ_sh).const_mul (Real.exp (2 * (Fintype.card R : ℝ) * B))
    have h2 : Integrable (fun p => ∫ a, G p a ∂(Measure.pi fun _ : R => ν s p)) (P₀.prod γ_sh) := by
      refine hI.mono' hJm.aestronglyMeasurable (hlift.mono fun p hp => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun a => hg0 _ _)]
      simpa only [G, abs_of_nonneg (hg0 _ _)] using hp.2
    exact ⟨h1, h2⟩
  obtain ⟨_, hI1⟩ := hint_s s₁
  obtain ⟨h2_ae, hI2⟩ := hint_s s₂
  rw [← integral_const_mul]
  refine integral_mono_ae hI1 (hI2.const_mul _) (h2_ae.mono fun p hp2 => ?_)
  have hexp0 : Integrable (fun x : T => Real.exp (u (S s₂ p.2 x))) ((μ₀ p.1).prod γ_aux) :=
    integrable_exp_of_ae_le (C := B) (hV s₂ p).aemeasurable (ae_of_all _ fun _ => hB' _)
  have hsub : ∀ x : T, |u (S s₁ p.2 x) - u (S s₂ p.2 x)| ≤ 2 * B := fun x =>
    (abs_sub _ _).trans (by linarith [hB (S s₁ p.2 x), hB (S s₂ p.2 x)])
  have hcomp := integral_pi_tilted_le_exp_mul_of_abs_sub_le (ι := R)
    (μ := (μ₀ p.1).prod γ_aux) hexp0 ((hV s₁ p).sub (hV s₂ p)) hsub
    (Y := G p) (fun _ => hg0 _ _) hp2
  have heq : 2 * (Fintype.card R : ℝ) * (2 * B) = 4 * Fintype.card R * B := by ring
  rw [heq] at hcomp
  exact hcomp

theorem integral_integral_pi_cavity_rotation_zero_eq_smartPath
    {N M : ℕ} {R : Type uR} [Fintype R]
    {u : ℝ → ℝ} {B D : ℝ} (hu : SmartPathPotential u B D)
    (t q : ℝ) (variance : ℝ≥0)
    (ψ : R → ℝ → ℝ) (hψm : ∀ r, Measurable (ψ r))
    {M₀ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀)
    {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
    (hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2) :
    let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
    let μ₀ (ω : SmartPathDisorder N M) :=
      (smartPathBase N M).tilted (smartPathEnergy u t ω)
    let γ_sh := Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : Fin 2 => gaussianReal 0 1
    let X : PerceptronSpin N → (Fin N ⊕ Unit) ⊕ Unit → ℝ :=
      fun σ => Sum.elim (cavityCoef N t σ) 0
    let Y : (Fin N ⊕ Unit) ⊕ Unit → ℝ := Sum.elim 0 (fun _ => Real.sqrt q)
    let A : Fin 2 → ℝ := Pi.single 0 (Real.sqrt ((1 - t) / (N + 1)))
    let E : Fin 2 → ℝ := Pi.single 1 (Real.sqrt (1 - q))
    let S₀ (w : (Fin N ⊕ Unit) ⊕ Unit → ℝ)
        (x : SmartPathState N M × (Fin 2 → ℝ)) : ℝ :=
      Real.cos 0 * (X x.1.1 ⬝ᵥ w + A ⬝ᵥ x.2) +
        Real.sin 0 * (Y ⬝ᵥ w + E ⬝ᵥ x.2)
    let P₁ := smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
    (∀ᵐ ω ∂P₀, Integrable (f ω) (Measure.pi fun _ : R => μ₀ ω)) →
    Integrable (fun ω => ∫ a, |f ω a| ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ →
    ∫ ω₀, ∫ w, ∫ σ : R → SmartPathState N M × (Fin 2 → ℝ),
        f ω₀ (fun r => (σ r).1) * ∏ r, ψ r (S₀ w (σ r))
        ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun x => u (S₀ w x)))
        ∂γ_sh ∂P₀ =
      ∫ ω, ∫ a : R → SmartPathState N (M + 1),
        f ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (fun r => ((a r).1, Fin.init (a r).2)) *
          ∏ r, ψ r (smartPathField t ω (a r) (Fin.last M))
        ∂(Measure.pi fun _ : R => (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω))
        ∂P₁ := by
  intro P₀ μ₀ γ_sh γ_aux X Y A E S₀ P₁ hfi hfi₁
  rw [integral_integral_pi_cavity_rotation_eq_extended hu t q 0 variance ψ hψm hM₀ hf hfi hfi₁]
  have hpt (p : SmartPathDisorder N (M + 1) × ℝ) :
      (∫ a : R → SmartPathState N (M + 1) × ℝ,
        f ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
          (fun r => ((a r).1.1, Fin.init (a r).1.2)) *
          ∏ r, ψ r (Real.cos 0 * smartPathField t p.1 (a r).1 (Fin.last M) +
            Real.sin 0 * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * (a r).2))
        ∂(Measure.pi fun _ : R => ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
          fun x : SmartPathState N (M + 1) × ℝ =>
            smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
              (x.1.1, Fin.init x.1.2) +
              u (Real.cos 0 * smartPathField t p.1 x.1 (Fin.last M) +
                Real.sin 0 * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2)))) =
      ∫ a : R → SmartPathState N (M + 1),
        f ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2) (fun r => ((a r).1, Fin.init (a r).2)) *
          ∏ r, ψ r (smartPathField t p.1 (a r) (Fin.last M))
        ∂(Measure.pi fun _ : R => (smartPathBase N (M + 1)).tilted (smartPathEnergy u t p.1)) := by
    have h := integral_pi_tilted_cavityPath_zero (μ := smartPathBase N (M + 1)) (u := u)
      t q p.2 p.1 (fun a : R → SmartPathState N (M + 1) =>
        f ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2) (fun r => ((a r).1, Fin.init (a r).2)) *
          ∏ r, ψ r (smartPathField t p.1 (a r) (Fin.last M)))
    simpa [Real.cos_zero, Real.sin_zero] using h
  simp_rw [hpt]
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : SmartPathDisorder N (M + 1) → ℝ, ∀ ω, Ψ ω =
      ∫ a : R → SmartPathState N (M + 1),
        f ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (fun r => ((a r).1, Fin.init (a r).2)) *
          ∏ r, ψ r (smartPathField t ω (a r) (Fin.last M))
        ∂(Measure.pi fun _ : R => (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)) :=
    ⟨_, fun _ => rfl⟩
  simp_rw [← hΨ]
  exact integral_prod_fun_fst_of_isProbabilityMeasure (E := ℝ) P₁ (gaussianReal 0 1) Ψ

theorem integral_integral_pi_cavity_rotation_pi_div_two_unweighted_eq
    {N M : ℕ} {R : Type uR} [Fintype R]
    {u : ℝ → ℝ} {B D : ℝ} (hu : SmartPathPotential u B D)
    (t q : ℝ) (variance : ℝ≥0)
    {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
    (hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2) :
    let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
    let μ₀ (ω : SmartPathDisorder N M) :=
      (smartPathBase N M).tilted (smartPathEnergy u t ω)
    let γ_sh := Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : Fin 2 => gaussianReal 0 1
    let X : PerceptronSpin N → (Fin N ⊕ Unit) ⊕ Unit → ℝ :=
      fun σ => Sum.elim (cavityCoef N t σ) 0
    let Y : (Fin N ⊕ Unit) ⊕ Unit → ℝ := Sum.elim 0 (fun _ => Real.sqrt q)
    let A : Fin 2 → ℝ := Pi.single 0 (Real.sqrt ((1 - t) / (N + 1)))
    let E : Fin 2 → ℝ := Pi.single 1 (Real.sqrt (1 - q))
    let S (w : (Fin N ⊕ Unit) ⊕ Unit → ℝ)
        (x : SmartPathState N M × (Fin 2 → ℝ)) : ℝ :=
      Real.cos (Real.pi / 2) * (X x.1.1 ⬝ᵥ w + A ⬝ᵥ x.2) +
        Real.sin (Real.pi / 2) * (Y ⬝ᵥ w + E ⬝ᵥ x.2)
    let P₁ := smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
    (∀ᵐ ω ∂P₀, Integrable (f ω) (Measure.pi fun _ : R => μ₀ ω)) →
    Integrable (fun ω => ∫ a, |f ω a| ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ →
    ∫ ω₀, ∫ w, ∫ σ : R → SmartPathState N M × (Fin 2 → ℝ),
        f ω₀ (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun x => u (S w x)))
        ∂γ_sh ∂P₀ =
      ∫ ω, ∫ a : R → SmartPathState N (M + 1),
        f ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (fun r => ((a r).1, Fin.init (a r).2))
        ∂(Measure.pi fun _ : R => (smartPathBase N (M + 1)).tilted
          fun x : SmartPathState N (M + 1) =>
            smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2))
        ∂P₁ := by
  intro P₀ μ₀ γ_sh γ_aux X Y A E S P₁ hfi hfi₁
  have h1 := integral_integral_pi_cavity_rotation_eq_extended hu t q (Real.pi / 2) variance
    (fun _ _ => 1) (fun _ => measurable_const) (M₀ := 1) (fun _ _ => by simp) hf hfi hfi₁
  dsimp only at h1
  simp only [Finset.prod_const_one, mul_one] at h1
  have : SFinite P₁ := by
    have : IsProbabilityMeasure P₁ := by dsimp [P₁]; rw [smartPathDisorder_eq]; infer_instance
    infer_instance
  rw [h1]
  exact integral_integral_pi_tilted_cavityPath_pi_div_two t q
    (fun ω a => f ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) a) P₁
    (fun z => integrable_exp_cavityPath_new hu.measurable (fun x => hu.le x) q z)

theorem integral_integral_pi_cavity_rotation_pi_div_two_deriv_mul_eq
    {N M : ℕ} {R : Type uR} [Fintype R] {r₁ r₂ : R} (hr : r₁ ≠ r₂)
    {u : ℝ → ℝ} {B D : ℝ} (hu : SmartPathPotential u B D)
    (t q : ℝ) (variance : ℝ≥0)
    {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
    (hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2) :
    let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
    let μ₀ (ω : SmartPathDisorder N M) :=
      (smartPathBase N M).tilted (smartPathEnergy u t ω)
    let γ_sh := Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : Fin 2 => gaussianReal 0 1
    let X : PerceptronSpin N → (Fin N ⊕ Unit) ⊕ Unit → ℝ :=
      fun σ => Sum.elim (cavityCoef N t σ) 0
    let Y : (Fin N ⊕ Unit) ⊕ Unit → ℝ := Sum.elim 0 (fun _ => Real.sqrt q)
    let A : Fin 2 → ℝ := Pi.single 0 (Real.sqrt ((1 - t) / (N + 1)))
    let E : Fin 2 → ℝ := Pi.single 1 (Real.sqrt (1 - q))
    let S (w : (Fin N ⊕ Unit) ⊕ Unit → ℝ)
        (x : SmartPathState N M × (Fin 2 → ℝ)) : ℝ :=
      Real.cos (Real.pi / 2) * (X x.1.1 ⬝ᵥ w + A ⬝ᵥ x.2) +
        Real.sin (Real.pi / 2) * (Y ⬝ᵥ w + E ⬝ᵥ x.2)
    let P₁ := smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
    let rhat := perceptronRhat u q
    (∀ᵐ ω ∂P₀, Integrable (f ω) (Measure.pi fun _ : R => μ₀ ω)) →
    Integrable (fun ω => ∫ a, |f ω a| ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ →
    ∫ ω₀, ∫ w, ∫ σ : R → SmartPathState N M × (Fin 2 → ℝ),
        f ω₀ (fun r => (σ r).1) * (deriv u (S w (σ r₁)) * deriv u (S w (σ r₂)))
        ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun x => u (S w x)))
        ∂γ_sh ∂P₀ =
      rhat * ∫ ω, ∫ a : R → SmartPathState N (M + 1),
        f ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (fun r => ((a r).1, Fin.init (a r).2))
        ∂(Measure.pi fun _ : R => (smartPathBase N (M + 1)).tilted
          fun x : SmartPathState N (M + 1) =>
            smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2))
        ∂P₁ := by
  classical
  intro P₀ μ₀ γ_sh γ_aux X Y A E S P₁ rhat hfi hfi₁
  let ψ (r : R) (x : ℝ) : ℝ := if r = r₁ ∨ r = r₂ then deriv u x else 1
  have hψm (r : R) : Measurable (ψ r) := by
    dsimp only [ψ]; split_ifs; exacts [measurable_deriv u, measurable_const]
  have hM₀ (r : R) (x : ℝ) : |ψ r x| ≤ 1 + |D| := by
    dsimp only [ψ]; split_ifs
    · linarith [hu.abs_deriv_le x, le_abs_self D, abs_nonneg D]
    · rw [abs_one]; linarith [abs_nonneg D]
  have hprod_eq (x : R → ℝ) :
      (∏ r : R, ψ r (x r)) = deriv u (x r₁) * deriv u (x r₂) := by
    simpa only [ψ, apply_ite, Finset.mem_insert, Finset.mem_singleton, Finset.prod_pair hr] using
      (Fintype.prod_ite_mem ({r₁, r₂} : Finset R) (fun r => deriv u (x r)))
  have h1 := integral_integral_pi_cavity_rotation_eq_extended hu t q (Real.pi / 2) variance
    ψ hψm hM₀ hf hfi hfi₁
  dsimp only at h1
  have hlhs :
      (∫ ω₀, ∫ w, ∫ σ : R → SmartPathState N M × (Fin 2 → ℝ),
        f ω₀ (fun r => (σ r).1) * (deriv u (S w (σ r₁)) * deriv u (S w (σ r₂)))
        ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun x => u (S w x)))
        ∂γ_sh ∂P₀) =
      ∫ ω₀, ∫ w, ∫ σ : R → SmartPathState N M × (Fin 2 → ℝ),
        f ω₀ (fun r => (σ r).1) * ∏ r, ψ r (S w (σ r))
        ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun x => u (S w x)))
        ∂γ_sh ∂P₀ := by
    refine integral_congr_ae (ae_of_all _ fun ω₀ => integral_congr_ae (ae_of_all _ fun w =>
      integral_congr_ae (ae_of_all _ fun σ => ?_)))
    dsimp only
    rw [hprod_eq (fun r => S w (σ r))]
  rw [hlhs, h1]
  have : SFinite P₁ := by
    have : IsProbabilityMeasure P₁ := by dsimp [P₁]; rw [smartPathDisorder_eq]; infer_instance
    infer_instance
  have hrhs_eq :
      (∫ p : SmartPathDisorder N (M + 1) × ℝ,
        ∫ a : R → SmartPathState N (M + 1) × ℝ,
          f ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
            (fun r => ((a r).1.1, Fin.init (a r).1.2)) *
            ∏ r, ψ r (Real.cos (Real.pi / 2) * smartPathField t p.1 (a r).1 (Fin.last M) +
              Real.sin (Real.pi / 2) * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * (a r).2))
        ∂(Measure.pi fun _ : R => ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
          fun x : SmartPathState N (M + 1) × ℝ =>
            smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
              (x.1.1, Fin.init x.1.2) +
              u (Real.cos (Real.pi / 2) * smartPathField t p.1 x.1 (Fin.last M) +
                Real.sin (Real.pi / 2) * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2)))
        ∂(P₁.prod (gaussianReal 0 1))) =
      ∫ p : SmartPathDisorder N (M + 1) × ℝ,
        ∫ a : R → SmartPathState N (M + 1) × ℝ,
          f ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
            (fun r => ((a r).1.1, Fin.init (a r).1.2)) *
            (deriv u (Real.sqrt q * p.2 + Real.sqrt (1 - q) * (a r₁).2) *
              deriv u (Real.sqrt q * p.2 + Real.sqrt (1 - q) * (a r₂).2))
        ∂(Measure.pi fun _ : R => ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
          fun x : SmartPathState N (M + 1) × ℝ =>
            smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
              (x.1.1, Fin.init x.1.2) +
              u (Real.cos (Real.pi / 2) * smartPathField t p.1 x.1 (Fin.last M) +
                Real.sin (Real.pi / 2) * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2)))
        ∂(P₁.prod (gaussianReal 0 1)) := by
    refine integral_congr_ae (ae_of_all _ fun p => integral_congr_ae (ae_of_all _ fun a => ?_))
    dsimp only
    rw [hprod_eq]
    simp [Real.cos_pi_div_two, Real.sin_pi_div_two]
  rw [hrhs_eq]
  exact integral_integral_pi_tilted_cavityPath_pi_div_two_deriv_mul t q hr
    (fun ω a => f ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) a) P₁
    (fun z => integrable_exp_cavityPath_new hu.measurable (fun x => hu.le x) q z)

/-- **Abstract master bound behind Proposition 2.3.5, Eq. (2.62).** -/
theorem abs_integral_smartPath_deriv_mul_sub_rhat_le_of_split_pair_bound
    {N M : ℕ} {R : Type uR} [Fintype R]
    {r₁ r₂ : R} (hr : r₁ ≠ r₂)
    {t q : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (variance : ℝ≥0)
    {u : ℝ → ℝ} {D : ℝ}
    (hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
    (hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
    {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
    (hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2)
    {m : ℝ} (hm0 : 0 ≤ m) :
    let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
    let μ₀ (ω : SmartPathDisorder N M) :=
      (smartPathBase N M).tilted (smartPathEnergy u t ω)
    let γ_sh := Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : Fin 2 => gaussianReal 0 1
    let X : PerceptronSpin N → (Fin N ⊕ Unit) ⊕ Unit → ℝ :=
      fun σ => Sum.elim (cavityCoef N t σ) 0
    let Y : (Fin N ⊕ Unit) ⊕ Unit → ℝ := Sum.elim 0 (fun _ => Real.sqrt q)
    let A : Fin 2 → ℝ := Pi.single 0 (Real.sqrt ((1 - t) / (N + 1)))
    let E : Fin 2 → ℝ := Pi.single 1 (Real.sqrt (1 - q))
    let S (s : ℝ) (w : (Fin N ⊕ Unit) ⊕ Unit → ℝ)
        (x : SmartPathState N M × (Fin 2 → ℝ)) : ℝ :=
      Real.cos s * (X x.1.1 ⬝ᵥ w + A ⬝ᵥ x.2) +
        Real.sin s * (Y ⬝ᵥ w + E ⬝ᵥ x.2)
    let ν (s : ℝ) (p : SmartPathDisorder N M × ((Fin N ⊕ Unit) ⊕ Unit → ℝ)) :=
      ((μ₀ p.1).prod γ_aux).tilted fun x => u (S s p.2 x)
    let P₁ := smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
    let μ₁ (ω : SmartPathDisorder N (M + 1)) :=
      (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)
    let f_ext (ω : SmartPathDisorder N (M + 1)) (a : R → SmartPathState N (M + 1)) : ℝ :=
      f ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (fun r => ((a r).1, Fin.init (a r).2))
    let d_spin (σ τ : PerceptronSpin N) : ℝ :=
      |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
        ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
    let rhat := perceptronRhat u q
    let n : ℝ := Fintype.card R
    let M₀w : ℝ := 1 + |D|
    let M₁w : ℝ := |D|
    let L_u : ℝ := 1 + |D| + |(1 : ℝ)| + |(0 : ℝ)| + |(1 : ℝ)| * |D|
    let L_w : ℝ := 1 + |D| + |M₀w| + |M₁w| + |M₀w| * |D|
    let K_u : ℝ := (4 * n ^ 2 + n) * L_u ^ (Fintype.card R + 2)
    let K_w : ℝ := (4 * n ^ 2 + n) * L_w ^ (Fintype.card R + 2)
    (∀ᵐ ω ∂P₀, Integrable (f ω) (Measure.pi fun _ : R => μ₀ ω)) →
    Integrable (fun ω => ∫ a, |f ω a| ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ →
    (∀ (s : ℝ) (ι : Type uR) [Fintype ι] (e : R → ι), Function.Injective e → ∀ i j, i ≠ j →
      ∫ p, ∫ a : ι → SmartPathState N M × (Fin 2 → ℝ),
        |f p.1 (fun r => (a (e r)).1)| * d_spin (a i).1.1 (a j).1.1
        ∂(Measure.pi fun _ : ι => ν s p) ∂(P₀.prod γ_sh) ≤ m) →
    |(∫ ω, ∫ a : R → SmartPathState N (M + 1),
        f_ext ω a *
          (deriv u (smartPathField t ω (a r₁) (Fin.last M)) *
            deriv u (smartPathField t ω (a r₂) (Fin.last M)))
        ∂(Measure.pi fun _ : R => μ₁ ω) ∂P₁) -
      rhat * (∫ ω, ∫ a : R → SmartPathState N (M + 1), f_ext ω a
        ∂(Measure.pi fun _ : R => μ₁ ω) ∂P₁)| ≤
      (K_w / 2 + |D| ^ 2 * (K_u / 2)) *
        (m + 1 / (N + 1) * Real.exp (4 * n * |D|) *
          ∫ ω, ∫ a : R → SmartPathState N (M + 1),
            |f_ext ω a| ∂(Measure.pi fun _ : R => μ₁ ω) ∂P₁) := by
  classical
  intro P₀ μ₀ γ_sh γ_aux X Y A E S ν P₁ μ₁ f_ext d_spin rhat n M₀w M₁w L_u L_w K_u K_w
    hfi hfi₁ hpair
  obtain ⟨hu, h2d, hb3⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hD_abs : ∀ x, |u x| ≤ |D| := fun x => (hu.abs_le x).trans (le_abs_self D)
  have hf_abs_m : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) =>
      |f p.1 p.2| := by simpa only [Real.norm_eq_abs] using hf.norm
  let I₁ : ℝ := ∫ ω, ∫ a : R → SmartPathState N (M + 1),
    |f_ext ω a| ∂(Measure.pi fun _ : R => μ₁ ω) ∂P₁
  have hI₁_0 : 0 ≤ I₁ := integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _
  have hm1_0 : ∫ p, ∫ a : R → SmartPathState N M × (Fin 2 → ℝ),
      |f p.1 (fun r => (a r).1)| ∂(Measure.pi fun _ : R => ν 0 p) ∂(P₀.prod γ_sh) = I₁ := by
    obtain ⟨_, hF₁⟩ :=
      integrable_integral_pi_cavity_rotation_abs t q 0 variance hu.toSmartPathPotential hf hfi hfi₁
    have h0 := integral_integral_pi_cavity_rotation_zero_eq_smartPath hu.toSmartPathPotential
      t q variance (fun _ _ => 1) (fun _ => measurable_const) (M₀ := 1) (fun _ _ => by simp)
      hf_abs_m (hfi.mono fun ω hω => hω.abs) (by simpa only [abs_abs] using hfi₁)
    dsimp only at h0
    simp only [Finset.prod_const_one, mul_one] at h0
    have hfub := integral_prod
      (fun p => ∫ a : R → SmartPathState N M × (Fin 2 → ℝ),
        |f p.1 (fun r => (a r).1)| ∂(Measure.pi fun _ : R => ν 0 p)) hF₁
    exact hfub.trans h0
  have hm1_le (s : ℝ) :
      ∫ p, ∫ a : R → SmartPathState N M × (Fin 2 → ℝ),
        |f p.1 (fun r => (a r).1)| ∂(Measure.pi fun _ : R => ν s p) ∂(P₀.prod γ_sh) ≤
      Real.exp (4 * n * |D|) * I₁ := by
    have h := integral_pi_cavity_rotation_nonneg_le_exp_mul hu.measurable hD_abs t q s 0 variance
      hf_abs_m (fun _ _ => abs_nonneg _) (hfi.mono fun _ hω => hω.abs) hfi₁
    dsimp only at h
    rw [hm1_0] at h
    exact h
  let B_err : ℝ := m + 1 / (N + 1) * Real.exp (4 * n * |D|) * I₁
  -- Unweighted path φ_u(s)
  let φ_u (s : ℝ) : ℝ :=
    ∫ ω₀, ∫ w, ∫ σ : R → SmartPathState N M × (Fin 2 → ℝ),
      f ω₀ (fun r => (σ r).1)
      ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun x => u (S s w x)))
      ∂γ_sh ∂P₀
  have hderiv_u (s : ℝ) : ∃ z, HasDerivAt φ_u (Real.sin s * Real.cos s * z) s ∧
      (s ∈ Set.Icc 0 (Real.pi / 2) → |z| ≤ K_u * B_err) := by
    obtain ⟨z, hz, hzb⟩ := exists_hasDerivAt_cavity_rotation_abs_le_of_pair_bound ht hq variance hu
      (fun _ _ => 1) (fun _ => differentiable_const 1) (fun _ => by simp)
      (M₀ := 1) (M₁ := 0) (M₂ := 0)
      (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp)
      hf s hm0 hfi hfi₁ (fun ι _ e he i j hij => hpair s ι e he i j hij)
    simp only [Finset.prod_const_one, mul_one] at hz
    refine ⟨z, hz, fun _ => hzb.trans ?_⟩
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hm1_le s) (by positivity)
  -- Weighted path φ_w(s)
  let ψ_w (r : R) (x : ℝ) : ℝ := if r = r₁ ∨ r = r₂ then deriv u x else 1
  obtain ⟨hψd, hψ₂d, hM₀w, hM₁w, hM₂w⟩ :=
    differentiable_and_abs_deriv_le_ite_one (p := fun i : R => i = r₁ ∨ i = r₂)
      (B₀ := M₀w) (B₁ := M₁w) (B₂ := |D|) hu.differentiable_deriv h2d
      (fun x => by dsimp [M₀w]; linarith [hu.abs_deriv_le x, le_abs_self D])
      (fun x => (hu.abs_deriv₂_le x).trans (le_abs_self D))
      (fun x => (hb3 x).trans (le_abs_self D))
      (by dsimp [M₀w]; linarith only [abs_nonneg D]) (abs_nonneg _) (abs_nonneg _)
  let φ_w (s : ℝ) : ℝ :=
    ∫ ω₀, ∫ w, ∫ σ : R → SmartPathState N M × (Fin 2 → ℝ),
      f ω₀ (fun r => (σ r).1) * ∏ r, ψ_w r (S s w (σ r))
      ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun x => u (S s w x)))
      ∂γ_sh ∂P₀
  have hderiv_w (s : ℝ) : ∃ z, HasDerivAt φ_w (Real.sin s * Real.cos s * z) s ∧
      (s ∈ Set.Icc 0 (Real.pi / 2) → |z| ≤ K_w * B_err) := by
    obtain ⟨z, hz, hzb⟩ := exists_hasDerivAt_cavity_rotation_abs_le_of_pair_bound ht hq variance hu
      ψ_w hψd hψ₂d hM₀w hM₁w hM₂w
      hf s hm0 hfi hfi₁ (fun ι _ e he i j hij => hpair s ι e he i j hij)
    refine ⟨z, hz, fun _ => hzb.trans ?_⟩
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hm1_le s) (by positivity)
  -- Identify endpoints of φ_u and φ_w!
  have hprod_w (x : R → ℝ) :
      (∏ r : R, ψ_w r (x r)) = deriv u (x r₁) * deriv u (x r₂) := by
    simpa only [ψ_w, apply_ite, Finset.mem_insert, Finset.mem_singleton, Finset.prod_pair hr] using
      (Fintype.prod_ite_mem ({r₁, r₂} : Finset R) (fun r => deriv u (x r)))
  have hφ_u_0 : φ_u 0 = ∫ ω, ∫ a : R → SmartPathState N (M + 1), f_ext ω a
      ∂(Measure.pi fun _ : R => μ₁ ω) ∂P₁ := by
    have h := integral_integral_pi_cavity_rotation_zero_eq_smartPath hu.toSmartPathPotential
      t q variance (fun _ _ => 1) (fun _ => measurable_const) (M₀ := 1) (fun _ _ => by simp)
      hf hfi hfi₁
    dsimp only [φ_u] at h ⊢
    simpa only [Finset.prod_const_one, mul_one] using h
  have hφ_u_pi : φ_u (Real.pi / 2) =
      ∫ ω, ∫ a : R → SmartPathState N (M + 1), f_ext ω a
        ∂(Measure.pi fun _ : R => (smartPathBase N (M + 1)).tilted
          fun x : SmartPathState N (M + 1) =>
            smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2))
        ∂P₁ :=
    integral_integral_pi_cavity_rotation_pi_div_two_unweighted_eq hu.toSmartPathPotential
      t q variance hf hfi hfi₁
  have hφ_w_0 : φ_w 0 = ∫ ω, ∫ a : R → SmartPathState N (M + 1),
      f_ext ω a *
        (deriv u (smartPathField t ω (a r₁) (Fin.last M)) *
          deriv u (smartPathField t ω (a r₂) (Fin.last M)))
      ∂(Measure.pi fun _ : R => μ₁ ω) ∂P₁ := by
    have h := integral_integral_pi_cavity_rotation_zero_eq_smartPath hu.toSmartPathPotential
      t q variance ψ_w (fun r => (hψd r).continuous.measurable) hM₀w hf hfi hfi₁
    dsimp only [φ_w] at h ⊢
    rw [h]
    refine integral_congr_ae (ae_of_all _ fun ω => integral_congr_ae (ae_of_all _ fun a => ?_))
    dsimp only [f_ext]
    rw [hprod_w]
  have hφ_w_pi : φ_w (Real.pi / 2) = rhat * φ_u (Real.pi / 2) := by
    have h := integral_integral_pi_cavity_rotation_pi_div_two_deriv_mul_eq hr
      hu.toSmartPathPotential t q variance hf hfi hfi₁
    dsimp only at h
    have hl : φ_w (Real.pi / 2) =
        ∫ ω₀, ∫ w, ∫ σ : R → SmartPathState N M × (Fin 2 → ℝ),
          f ω₀ (fun r => (σ r).1) * (deriv u (S (Real.pi / 2) w (σ r₁)) *
            deriv u (S (Real.pi / 2) w (σ r₂)))
          ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun x => u (S (Real.pi / 2) w x)))
          ∂γ_sh ∂P₀ := by
      dsimp only [φ_w]
      refine integral_congr_ae (ae_of_all _ fun ω₀ => integral_congr_ae (ae_of_all _ fun w =>
        integral_congr_ae (ae_of_all _ fun σ => ?_)))
      dsimp only
      rw [hprod_w]
    rw [hl, hφ_u_pi]
    exact h
  have hrhat_b := rhat_mem_Icc (u := u) (D' := |D|)
    (fun x => (hu.abs_deriv_le x).trans (le_abs_self D)) q
    (fun z => integrable_exp_cavityPath_new hu.measurable (fun x => hu.le x) q z)
  rw [← hφ_w_0, ← hφ_u_0]
  calc |φ_w 0 - rhat * φ_u 0| ≤ K_w * B_err / 2 + |D| ^ 2 * (K_u * B_err / 2) :=
        Real.abs_sub_mul_le_half_of_exists_hasDerivAt hφ_w_pi
          (by rw [abs_of_nonneg hrhat_b.1]; exact hrhat_b.2) hderiv_w hderiv_u
    _ = (K_w / 2 + |D| ^ 2 * (K_u / 2)) * B_err := by ring

/-- **Proposition 2.3.5, Eq. (2.62), `(1, ∞)` endpoint.** -/
theorem abs_integral_smartPath_deriv_mul_sub_rhat_le_first_moment
    (R : Type uR) [Fintype R] (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N M : ℕ) {r₁ r₂ : R} (_hr : r₁ ≠ r₂)
        {t q : ℝ} (_ht : t ∈ Set.Icc (0 : ℝ) 1) (_hq : q ∈ Set.Icc (0 : ℝ) 1)
        (variance : ℝ≥0)
        {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
        (_hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2),
        let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
        let μ₀ (ω : SmartPathDisorder N M) :=
          (smartPathBase N M).tilted (smartPathEnergy u t ω)
        let P₁ := smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
        let μ₁ (ω : SmartPathDisorder N (M + 1)) :=
          (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)
        let f_ext (ω : SmartPathDisorder N (M + 1)) (a : R → SmartPathState N (M + 1)) : ℝ :=
          f ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (fun r => ((a r).1, Fin.init (a r).2))
        let average (g : SmartPathDisorder N (M + 1) → (R → SmartPathState N (M + 1)) → ℝ) :=
          ∫ ω, ∫ a, g ω a ∂(Measure.pi fun _ : R => μ₁ ω) ∂P₁
        let weighted := average fun ω a =>
          f_ext ω a * (deriv u (smartPathField t ω (a r₁) (Fin.last M)) *
            deriv u (smartPathField t ω (a r₂) (Fin.last M)))
        let unweighted := average f_ext
        let firstMoment := average fun ω a => |f_ext ω a|
        (∀ᵐ ω ∂P₀, Integrable (f ω) (Measure.pi fun _ : R => μ₀ ω)) →
        Integrable (fun ω => ∫ a, |f ω a| ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ →
        |weighted - perceptronRhat u q * unweighted| ≤ K * ((2 + 1 / (N + 1)) * firstMoment) := by
  let n : ℝ := Fintype.card R
  let M₀w : ℝ := 1 + |D|
  let M₁w : ℝ := |D|
  let L_u : ℝ := 1 + |D| + |(1 : ℝ)| + |(0 : ℝ)| + |(1 : ℝ)| * |D|
  let L_w : ℝ := 1 + |D| + |M₀w| + |M₁w| + |M₀w| * |D|
  let K_u : ℝ := (4 * n ^ 2 + n) * L_u ^ (Fintype.card R + 2)
  let K_w : ℝ := (4 * n ^ 2 + n) * L_w ^ (Fintype.card R + 2)
  let K : ℝ := (K_w / 2 + |D| ^ 2 * (K_u / 2)) * Real.exp (4 * n * |D|)
  refine ⟨K, by positivity, ?_⟩
  intro N M r₁ r₂ hr t q ht hq variance u hd hb f hf P₀ μ₀ P₁ μ₁ f_ext
    average weighted unweighted I₁ hfi hfi₁
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hD_abs : ∀ x, |u x| ≤ |D| := fun x => (hu.abs_le x).trans (le_abs_self D)
  have hf_abs_m : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) =>
      |f p.1 p.2| := by simpa only [Real.norm_eq_abs] using hf.norm
  have hI₁_0 : 0 ≤ I₁ := integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _
  let m : ℝ := 2 * Real.exp (4 * n * |D|) * I₁
  have hm0 : 0 ≤ m := by positivity
  let d_spin (σ τ : PerceptronSpin N) : ℝ :=
    |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
      ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
  let T := SmartPathState N M × (Fin 2 → ℝ)
  have hdm : Measurable fun p : T × T => d_spin p.1.1.1 p.2.1.1 := by
    let b : PerceptronSpin N × PerceptronSpin N → ℝ := fun p => d_spin p.1 p.2
    have hproj : Measurable fun p : T × T => (p.1.1.1, p.2.1.1) :=
      (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_fst.comp (measurable_fst.comp measurable_snd))
    have h := (measurable_of_finite b).comp hproj
    exact h
  have hm1_0 : ∫ p, ∫ a : R → T,
      |f p.1 (fun r => (a r).1)| ∂(Measure.pi fun _ : R =>
        ((μ₀ p.1).prod (Measure.pi fun _ : Fin 2 => gaussianReal 0 1)).tilted
          fun x => u (Real.cos 0 *
            (Sum.elim (cavityCoef N t x.1.1) 0 ⬝ᵥ p.2 +
              Pi.single 0 (Real.sqrt ((1 - t) / (N + 1))) ⬝ᵥ x.2) +
            Real.sin 0 * (Sum.elim 0 (fun _ => Real.sqrt q) ⬝ᵥ p.2 +
              Pi.single 1 (Real.sqrt (1 - q)) ⬝ᵥ x.2)))
      ∂(P₀.prod (Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)) = I₁ := by
    obtain ⟨_, hF₁⟩ :=
      integrable_integral_pi_cavity_rotation_abs t q 0 variance hu.toSmartPathPotential hf hfi hfi₁
    have h0 := integral_integral_pi_cavity_rotation_zero_eq_smartPath hu.toSmartPathPotential
      t q variance (fun _ _ => 1) (fun _ => measurable_const) (M₀ := 1) (fun _ _ => by simp)
      hf_abs_m (hfi.mono fun _ hω => hω.abs) (by simpa only [abs_abs] using hfi₁)
    dsimp only at h0
    simp only [Finset.prod_const_one, mul_one] at h0
    exact (integral_prod _ hF₁).trans h0
  have hpair (s : ℝ) (ι : Type uR) [Fintype ι] (e : R → ι) (he : Function.Injective e)
      (i j : ι) (hij : i ≠ j) :
      ∫ p, ∫ a : ι → T,
        |f p.1 (fun r => (a (e r)).1)| * d_spin (a i).1.1 (a j).1.1
        ∂(Measure.pi fun _ : ι =>
          ((μ₀ p.1).prod (Measure.pi fun _ : Fin 2 => gaussianReal 0 1)).tilted
            fun x => u (Real.cos s *
              (Sum.elim (cavityCoef N t x.1.1) 0 ⬝ᵥ p.2 +
                Pi.single 0 (Real.sqrt ((1 - t) / (N + 1))) ⬝ᵥ x.2) +
              Real.sin s * (Sum.elim 0 (fun _ => Real.sqrt q) ⬝ᵥ p.2 +
                Pi.single 1 (Real.sqrt (1 - q)) ⬝ᵥ x.2)))
        ∂(P₀.prod (Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)) ≤ m := by
    have hS := measurable_cavity_rotation_field (N := N) (M := M) t q s
    have hμ₀ (ω : SmartPathDisorder N M) : IsProbabilityMeasure (μ₀ ω) :=
      isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.measurable (fun x => hu.le x) ω t
    let νs (p : SmartPathDisorder N M × ((Fin N ⊕ Unit) ⊕ Unit → ℝ)) :=
      ((μ₀ p.1).prod (Measure.pi fun _ : Fin 2 => gaussianReal 0 1)).tilted
        fun x : T => u (Real.cos s *
          (Sum.elim (cavityCoef N t x.1.1) 0 ⬝ᵥ p.2 +
            Pi.single 0 (Real.sqrt ((1 - t) / (N + 1))) ⬝ᵥ x.2) +
          Real.sin s * (Sum.elim 0 (fun _ => Real.sqrt q) ⬝ᵥ p.2 +
            Pi.single 1 (Real.sqrt (1 - q)) ⬝ᵥ x.2))
    have : ∀ p, IsProbabilityMeasure (νs p) := fun p => by
      have hp : Measurable fun x : T => (p.2, x) := measurable_const.prodMk measurable_id
      have hs := hS.comp hp
      exact isProbabilityMeasure_tilted_of_ae_le (hu.measurable.comp hs).aemeasurable
        (ae_of_all _ fun _ => hu.le _)
    obtain ⟨hFI, hF₁⟩ :=
      integrable_integral_pi_cavity_rotation_abs t q s variance hu.toSmartPathPotential hf hfi hfi₁
    have hh := integral_integral_pair_holder_one_top _ νs he hij
      (f := fun p a => f p.1 (fun r => (a r).1))
      (d := fun a b => d_spin a.1.1 b.1.1)
      (fun _ _ => abs_nonneg _) hdm (Md := 2)
      (ae_of_all _ fun _ => ae_of_all _ fun a => abs_perceptron_overlap_sub_le_two hq _ _)
      hFI hF₁
    have hdom := integral_pi_cavity_rotation_nonneg_le_exp_mul hu.measurable hD_abs t q s 0 variance
      hf_abs_m (fun _ _ => abs_nonneg _) (hfi.mono fun _ hω => hω.abs) hfi₁
    dsimp only at hdom
    rw [hm1_0] at hdom
    calc _ ≤ (∫ p, ∫ a : R → T, |f p.1 (fun r => (a r).1)|
            ∂(Measure.pi fun _ : R => νs p)
            ∂(P₀.prod (Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1))) * 2 := hh
      _ ≤ (Real.exp (4 * n * |D|) * I₁) * 2 := mul_le_mul_of_nonneg_right hdom zero_le_two
      _ = m := by dsimp only [m]; ring
  have hmain := abs_integral_smartPath_deriv_mul_sub_rhat_le_of_split_pair_bound hr ht hq variance
    hd hb hf hm0 hfi hfi₁ hpair
  refine hmain.trans_eq ?_
  dsimp only [K, m, I₁]
  ring

/-- **Proposition 2.3.5, Eq. (2.62), interior Hölder exponents.** -/
theorem abs_integral_smartPath_deriv_mul_sub_rhat_le_holder
    (R : Type uR) [Fintype R] (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N M : ℕ) {r₁ r₂ : R} (_hr : r₁ ≠ r₂)
        {t q : ℝ} (_ht : t ∈ Set.Icc (0 : ℝ) 1) (_hq : q ∈ Set.Icc (0 : ℝ) 1)
        (variance : ℝ≥0)
        {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
        (_hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2)
        {p₁ p₂ : ℝ} (_hp : p₁.HolderConjugate p₂),
        let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
        let μ₀ (ω : SmartPathDisorder N M) :=
          (smartPathBase N M).tilted (smartPathEnergy u t ω)
        let P₁ := smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
        let μ₁ (ω : SmartPathDisorder N (M + 1)) :=
          (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)
        let f_ext (ω : SmartPathDisorder N (M + 1)) (a : R → SmartPathState N (M + 1)) : ℝ :=
          f ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (fun r => ((a r).1, Fin.init (a r).2))
        let d_spin (σ τ : PerceptronSpin N) : ℝ :=
          |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
            ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
        let average (g : SmartPathDisorder N (M + 1) → (R → SmartPathState N (M + 1)) → ℝ) :=
          ∫ ω, ∫ a, g ω a ∂(Measure.pi fun _ : R => μ₁ ω) ∂P₁
        let weighted := average fun ω a =>
          f_ext ω a * (deriv u (smartPathField t ω (a r₁) (Fin.last M)) *
            deriv u (smartPathField t ω (a r₂) (Fin.last M)))
        let unweighted := average f_ext
        let firstMoment := average fun ω a => |f_ext ω a|
        let observableMoment := average fun ω a => |f_ext ω a| ^ p₁
        let overlapMoment : ℝ :=
          ∫ ω, ∫ a : Fin 2 → SmartPathState N (M + 1),
            d_spin (a 0).1 (a 1).1 ^ p₂ ∂(Measure.pi fun _ : Fin 2 => μ₁ ω) ∂P₁
        (∀ᵐ ω ∂P₀, Integrable (fun a => |f ω a| ^ p₁) (Measure.pi fun _ : R => μ₀ ω)) →
        Integrable (fun ω => ∫ a, |f ω a| ^ p₁ ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ →
        |weighted - perceptronRhat u q * unweighted| ≤
          K * (observableMoment ^ (1 / p₁) * overlapMoment ^ (1 / p₂) +
            1 / (N + 1) * firstMoment) := by
  let n : ℝ := Fintype.card R
  let M₀w : ℝ := 1 + |D|
  let M₁w : ℝ := |D|
  let L_u : ℝ := 1 + |D| + |(1 : ℝ)| + |(0 : ℝ)| + |(1 : ℝ)| * |D|
  let L_w : ℝ := 1 + |D| + |M₀w| + |M₁w| + |M₀w| * |D|
  let K_u : ℝ := (4 * n ^ 2 + n) * L_u ^ (Fintype.card R + 2)
  let K_w : ℝ := (4 * n ^ 2 + n) * L_w ^ (Fintype.card R + 2)
  let E_dom : ℝ := Real.exp ((4 * n + 8) * |D|)
  let K : ℝ := (K_w / 2 + |D| ^ 2 * (K_u / 2)) * E_dom
  refine ⟨K, by positivity, ?_⟩
  intro N M r₁ r₂ hr t q ht hq variance u hd hb f hf p₁ p₂ hp P₀ μ₀ P₁ μ₁ f_ext d_spin
    average weighted unweighted I₁ A₀ B₀ hfp hfp₁
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hP₀ : IsProbabilityMeasure P₀ := by dsimp [P₀]; rw [smartPathDisorder_eq]; infer_instance
  have hμ₀ (ω : SmartPathDisorder N M) : IsProbabilityMeasure (μ₀ ω) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.measurable (fun x => hu.le x) ω t
  obtain ⟨hfi, hfi₁⟩ := integrable_pi_tilted_and_integrable_integral_abs_of_rpow P₀
    (μ := smartPathBase N M) (measurable_smartPathEnergy hu.measurable t) hf hp.lt.le hfp hfp₁
  have hD_abs : ∀ x, |u x| ≤ |D| := fun x => (hu.abs_le x).trans (le_abs_self D)
  have hhp1 : 0 ≤ 1 / p₁ := div_nonneg zero_le_one hp.pos.le
  have hhp2 : 0 ≤ 1 / p₂ := div_nonneg zero_le_one hp.symm.pos.le
  have hf_abs_m : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) =>
      |f p.1 p.2| := by simpa only [Real.norm_eq_abs] using hf.norm
  have hf_pow_m : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) =>
      |f p.1 p.2| ^ p₁ := hf_abs_m.pow_const p₁
  have hdo_m : Measurable fun p : SmartPathDisorder N M × (Fin 2 → SmartPathState N M) =>
      d_spin (p.2 0).1 (p.2 1).1 ^ p₂ := by
    let b : PerceptronSpin N × PerceptronSpin N → ℝ := fun p => d_spin p.1 p.2 ^ p₂
    have hproj : Measurable fun p : SmartPathDisorder N M × (Fin 2 → SmartPathState N M) =>
        ((p.2 0).1, (p.2 1).1) :=
      (measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)).prodMk
        (measurable_fst.comp ((measurable_pi_apply 1).comp measurable_snd))
    have hb' := (measurable_of_finite b).comp hproj
    exact hb'
  have hA₀ : 0 ≤ A₀ := integral_nonneg fun _ => integral_nonneg fun _ =>
    Real.rpow_nonneg (abs_nonneg _) _
  have hB₀ : 0 ≤ B₀ := integral_nonneg fun _ => integral_nonneg fun _ =>
    Real.rpow_nonneg (abs_nonneg _) _
  have hI₁ : 0 ≤ I₁ := integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _
  let m : ℝ := E_dom * (A₀ ^ (1 / p₁) * B₀ ^ (1 / p₂))
  have hm0 : 0 ≤ m := by positivity
  let T := SmartPathState N M × (Fin 2 → ℝ)
  let W := (Fin N ⊕ Unit) ⊕ Unit → ℝ
  let γ_sh : Measure W := Measure.pi fun _ => gaussianReal 0 1
  let γ_aux : Measure (Fin 2 → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  let νs (s : ℝ) (p : SmartPathDisorder N M × W) :=
    ((μ₀ p.1).prod γ_aux).tilted fun x : T => u (Real.cos s *
      (Sum.elim (cavityCoef N t x.1.1) 0 ⬝ᵥ p.2 +
        Pi.single 0 (Real.sqrt ((1 - t) / (N + 1))) ⬝ᵥ x.2) +
      Real.sin s * (Sum.elim 0 (fun _ => Real.sqrt q) ⬝ᵥ p.2 +
        Pi.single 1 (Real.sqrt (1 - q)) ⬝ᵥ x.2))
  have habs_p (ω : SmartPathDisorder N M) (a : R → SmartPathState N M) :
      |(|f ω a| ^ p₁)| = |f ω a| ^ p₁ :=
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
  have hfp₁_abs :
      Integrable (fun ω => ∫ a, |(|f ω a| ^ p₁)| ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ := by
    simpa only [habs_p] using hfp₁
  have hmp_0 : ∫ p, ∫ a : R → T, |f p.1 (fun r => (a r).1)| ^ p₁
      ∂(Measure.pi fun _ : R => νs 0 p) ∂(P₀.prod γ_sh) = A₀ := by
    obtain ⟨_, hFp₁⟩ :=
      integrable_integral_pi_cavity_rotation_abs t q 0 variance hu.toSmartPathPotential
        hf_pow_m hfp hfp₁_abs
    simp only [habs_p] at hFp₁
    have h0 := integral_integral_pi_cavity_rotation_zero_eq_smartPath hu.toSmartPathPotential
      t q variance (fun _ _ => 1) (fun _ => measurable_const) (M₀ := 1) (fun _ _ => by simp)
      hf_pow_m hfp hfp₁_abs
    dsimp only at h0
    simp only [Finset.prod_const_one, mul_one] at h0
    exact (integral_prod _ hFp₁).trans h0
  have hdo_b (a : Fin 2 → SmartPathState N M) : |d_spin (a 0).1 (a 1).1 ^ p₂| ≤ 2 ^ p₂ := by
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (abs_perceptron_overlap_sub_le_two hq _ _)
      hp.symm.pos.le
  have hdo_i : ∀ᵐ ω ∂P₀, Integrable (fun a : Fin 2 → SmartPathState N M =>
      d_spin (a 0).1 (a 1).1 ^ p₂) (Measure.pi fun _ : Fin 2 => μ₀ ω) :=
    ae_of_all _ fun ω => by
      have hpω : Measurable fun a : Fin 2 → SmartPathState N M => (ω, a) :=
        measurable_const.prodMk measurable_id
      have hmω := hdo_m.comp hpω
      exact Integrable.of_bound hmω.aestronglyMeasurable
        (2 ^ p₂) (ae_of_all _ fun a => by simpa using hdo_b a)
  have hdo_m1 := measurable_integral_pi_tilted (μ := smartPathBase N M)
    (E := fun ω => smartPathEnergy u t ω)
    (G := fun _ (a : Fin 2 → SmartPathState N M) => |d_spin (a 0).1 (a 1).1 ^ p₂|)
    (measurable_smartPathEnergy hu.measurable t)
    (by simpa only [Real.norm_eq_abs] using hdo_m.norm)
  have hdo_i1 : Integrable (fun ω => ∫ a : Fin 2 → SmartPathState N M,
      |d_spin (a 0).1 (a 1).1 ^ p₂| ∂(Measure.pi fun _ : Fin 2 => μ₀ ω)) P₀ :=
    Integrable.of_bound hdo_m1.aestronglyMeasurable (2 ^ p₂) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      exact abs_integral_le_of_forall_abs_le _ fun a => by simpa [abs_abs] using hdo_b a)
  have habs_o (a : Fin 2 → SmartPathState N M) :
      |d_spin (a 0).1 (a 1).1 ^ p₂| = d_spin (a 0).1 (a 1).1 ^ p₂ :=
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
  have hmo_0 : ∫ p, ∫ a : Fin 2 → T, d_spin (a 0).1.1 (a 1).1.1 ^ p₂
      ∂(Measure.pi fun _ : Fin 2 => νs 0 p) ∂(P₀.prod γ_sh) = B₀ := by
    obtain ⟨_, hFo₁⟩ :=
      integrable_integral_pi_cavity_rotation_abs t q 0 variance hu.toSmartPathPotential
        hdo_m hdo_i hdo_i1
    have habs_o' (a : Fin 2 → T) :
        |d_spin (a 0).1.1 (a 1).1.1 ^ p₂| = d_spin (a 0).1.1 (a 1).1.1 ^ p₂ :=
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
    simp only [habs_o'] at hFo₁
    have h0 := integral_integral_pi_cavity_rotation_zero_eq_smartPath hu.toSmartPathPotential
      t q variance (fun _ _ => 1) (fun _ => measurable_const) (M₀ := 1) (fun _ _ => by simp)
      hdo_m hdo_i hdo_i1
    dsimp only at h0
    simp only [Finset.prod_const_one, mul_one] at h0
    exact (integral_prod _ hFo₁).trans h0
  have hdm : Measurable fun p : T × T => d_spin p.1.1.1 p.2.1.1 := by
    let b : PerceptronSpin N × PerceptronSpin N → ℝ := fun p => d_spin p.1 p.2
    have hproj : Measurable fun p : T × T => (p.1.1.1, p.2.1.1) :=
      (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_fst.comp (measurable_fst.comp measurable_snd))
    have h := (measurable_of_finite b).comp hproj
    exact h
  have hd₂m : Measurable fun a : Fin 2 → T => d_spin (a 0).1.1 (a 1).1.1 := by
    have hpair0 : Measurable fun a : Fin 2 → T => (a 0, a 1) :=
      (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
    have h := hdm.comp hpair0
    exact h
  have hpair (s : ℝ) (ι : Type uR) [Fintype ι] (e : R → ι) (he : Function.Injective e)
      (i j : ι) (hij : i ≠ j) :
      ∫ p, ∫ a : ι → T, |f p.1 (fun r => (a (e r)).1)| * d_spin (a i).1.1 (a j).1.1
        ∂(Measure.pi fun _ : ι => νs s p) ∂(P₀.prod γ_sh) ≤ m := by
    have hS := measurable_cavity_rotation_field (N := N) (M := M) t q s
    have : ∀ p, IsProbabilityMeasure (νs s p) := fun p => by
      have hp' : Measurable fun x : T => (p.2, x) := measurable_const.prodMk measurable_id
      have hs := hS.comp hp'
      have hv := hu.measurable.comp hs
      exact isProbabilityMeasure_tilted_of_ae_le hv.aemeasurable
        (ae_of_all _ fun _ => hu.le _)
    obtain ⟨hFI, _⟩ :=
      integrable_integral_pi_cavity_rotation_abs t q s variance hu.toSmartPathPotential hf hfi hfi₁
    obtain ⟨hFn, hFnI⟩ :=
      integrable_integral_pi_cavity_rotation_abs t q s variance hu.toSmartPathPotential
        hf_pow_m hfp hfp₁_abs
    have hfp_mem : ∀ᵐ z ∂(P₀.prod γ_sh),
        MemLp (fun a : R → T => f z.1 (fun r => (a r).1))
          (ENNReal.ofReal p₁) (Measure.pi fun _ : R => νs s z) := by
      filter_upwards [hFI, hFn] with z hzi hzn
      refine (integrable_norm_rpow_iff hzi.aestronglyMeasurable
        (by simp [hp.pos]) ENNReal.ofReal_ne_top).mp ?_
      rw [ENNReal.toReal_ofReal hp.pos.le]
      change Integrable (fun a : R → T => |f z.1 (fun r => (a r).1)| ^ p₁)
        (Measure.pi fun _ : R => νs s z) at hzn
      simpa only [Real.norm_eq_abs] using hzn
    have hfp_int : Integrable
        (fun z => ∫ a : R → T, |f z.1 (fun r => (a r).1)| ^ p₁ ∂(Measure.pi fun _ : R => νs s z))
        (P₀.prod γ_sh) := by
      change Integrable (fun z => ∫ a : R → T, |(|f z.1 (fun r => (a r).1)| ^ p₁)|
        ∂(Measure.pi fun _ : R => νs s z)) (P₀.prod γ_sh) at hFnI
      simpa only [habs_p] using hFnI
    have hdq_mem : ∀ᵐ z ∂(P₀.prod γ_sh), MemLp (fun a : Fin 2 → T => d_spin (a 0).1.1 (a 1).1.1)
        (ENNReal.ofReal p₂) (Measure.pi fun _ : Fin 2 => νs s z) :=
      ae_of_all _ fun z => MemLp.of_bound hd₂m.aestronglyMeasurable 2
        (ae_of_all _ fun a => by
          rw [Real.norm_of_nonneg (abs_nonneg _)]
          exact abs_perceptron_overlap_sub_le_two hq _ _)
    obtain ⟨_, hFo₁⟩ :=
      integrable_integral_pi_cavity_rotation_abs t q s variance hu.toSmartPathPotential
        hdo_m hdo_i hdo_i1
    have habs_o' (a : Fin 2 → T) :
        |d_spin (a 0).1.1 (a 1).1.1 ^ p₂| = d_spin (a 0).1.1 (a 1).1.1 ^ p₂ :=
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)
    have hdq_int : Integrable (fun z => ∫ a : Fin 2 → T, d_spin (a 0).1.1 (a 1).1.1 ^ p₂
        ∂(Measure.pi fun _ : Fin 2 => νs s z)) (P₀.prod γ_sh) := by
      simpa only [habs_o'] using hFo₁
    have hh := integral_integral_pair_holder_prob (P₀.prod γ_sh) (νs s) he hij
      (f := fun p a => f p.1 (fun r => (a r).1))
      (d := fun a b => d_spin a.1.1 b.1.1) (fun _ _ => abs_nonneg _) hp
      hfp_mem hfp_int hdq_mem hdq_int
    -- Now dominate Aₚ ≤ exp(4n|D|) A₀ and Bₚ ≤ exp(8|D|) B₀!
    have hdom_A : ∫ p, ∫ a : R → T, |f p.1 (fun r => (a r).1)| ^ p₁
        ∂(Measure.pi fun _ : R => νs s p) ∂(P₀.prod γ_sh) ≤
        Real.exp (4 * n * |D|) * A₀ := by
      have h := integral_pi_cavity_rotation_nonneg_le_exp_mul hu.measurable hD_abs t q s 0 variance
        hf_pow_m (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) hfp hfp₁
      dsimp only at h
      rw [hmp_0] at h
      exact h
    have hdo_i1_raw : Integrable (fun ω => ∫ a : Fin 2 → SmartPathState N M,
        d_spin (a 0).1 (a 1).1 ^ p₂ ∂(Measure.pi fun _ : Fin 2 => μ₀ ω)) P₀ := by
      simpa only [habs_o] using hdo_i1
    have hdom_B : ∫ p, ∫ a : Fin 2 → T, d_spin (a 0).1.1 (a 1).1.1 ^ p₂
        ∂(Measure.pi fun _ : Fin 2 => νs s p) ∂(P₀.prod γ_sh) ≤
        Real.exp (8 * |D|) * B₀ := by
      have h := integral_pi_cavity_rotation_nonneg_le_exp_mul hu.measurable hD_abs t q s 0 variance
        hdo_m (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _) hdo_i hdo_i1_raw
      dsimp only at h
      rw [hmo_0, Fintype.card_fin] at h
      have hexp : Real.exp (4 * ((2 : ℕ) : ℝ) * |D|) = Real.exp (8 * |D|) := by
        congr 1; push_cast; ring
      rwa [hexp] at h
    have hA_pow : (∫ p, ∫ a : R → T, |f p.1 (fun r => (a r).1)| ^ p₁
        ∂(Measure.pi fun _ : R => νs s p) ∂(P₀.prod γ_sh)) ^ (1 / p₁) ≤
        E_dom ^ (1 / p₁) * A₀ ^ (1 / p₁) := by
      have hle_E : Real.exp (4 * n * |D|) ≤ E_dom :=
        Real.exp_le_exp.2 (by linarith [abs_nonneg D])
      have h1 := Real.rpow_le_rpow
        (integral_nonneg fun _ => integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _)
        (hdom_A.trans (mul_le_mul_of_nonneg_right hle_E hA₀)) hhp1
      rwa [Real.mul_rpow (Real.exp_pos _).le hA₀] at h1
    have hB_pow : (∫ p, ∫ a : Fin 2 → T, d_spin (a 0).1.1 (a 1).1.1 ^ p₂
        ∂(Measure.pi fun _ : Fin 2 => νs s p) ∂(P₀.prod γ_sh)) ^ (1 / p₂) ≤
        E_dom ^ (1 / p₂) * B₀ ^ (1 / p₂) := by
      have hle_E : Real.exp (8 * |D|) ≤ E_dom :=
        Real.exp_le_exp.2 (by
          dsimp only [n]
          nlinarith [abs_nonneg D, (Nat.cast_nonneg (Fintype.card R) : (0 : ℝ) ≤ Fintype.card R)])
      have h1 := Real.rpow_le_rpow
        (integral_nonneg fun _ => integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _)
        (hdom_B.trans (mul_le_mul_of_nonneg_right hle_E hB₀)) hhp2
      rwa [Real.mul_rpow (Real.exp_pos _).le hB₀] at h1
    have hE_sum : E_dom ^ (1 / p₁) * E_dom ^ (1 / p₂) = E_dom := by
      rw [← Real.rpow_add (Real.exp_pos _)]
      have hsum : 1 / p₁ + 1 / p₂ = 1 := by simpa [one_div] using hp.inv_add_inv_eq_one
      rw [hsum, Real.rpow_one]
    calc _ ≤ (E_dom ^ (1 / p₁) * A₀ ^ (1 / p₁)) * (E_dom ^ (1 / p₂) * B₀ ^ (1 / p₂)) :=
          hh.trans (mul_le_mul hA_pow hB_pow
            (Real.rpow_nonneg (integral_nonneg fun _ => integral_nonneg fun _ =>
              Real.rpow_nonneg (abs_nonneg _) _) _)
            (mul_nonneg (Real.rpow_nonneg (Real.exp_pos _).le _) (Real.rpow_nonneg hA₀ _)))
      _ = E_dom ^ (1 / p₁) * E_dom ^ (1 / p₂) * (A₀ ^ (1 / p₁) * B₀ ^ (1 / p₂)) := by ring
      _ = m := by rw [hE_sum]
  have hmain := abs_integral_smartPath_deriv_mul_sub_rhat_le_of_split_pair_bound hr ht hq variance
    hd hb hf hm0 hfi hfi₁ hpair
  refine hmain.trans ?_
  have hle_E1 : Real.exp (4 * n * |D|) ≤ E_dom :=
    Real.exp_le_exp.2 (by linarith [abs_nonneg D])
  have h1 : m + 1 / (N + 1) * Real.exp (4 * n * |D|) * I₁ ≤
      E_dom * (A₀ ^ (1 / p₁) * B₀ ^ (1 / p₂) + 1 / (N + 1) * I₁) := by
    dsimp only [m]
    have h2 : 1 / ((N : ℝ) + 1) * Real.exp (4 * n * |D|) * I₁ ≤
        1 / ((N : ℝ) + 1) * E_dom * I₁ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hle_E1 (by positivity)) hI₁
    linarith
  calc _ ≤ (K_w / 2 + |D| ^ 2 * (K_u / 2)) *
          (E_dom * (A₀ ^ (1 / p₁) * B₀ ^ (1 / p₂) + 1 / (N + 1) * I₁)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = K * (A₀ ^ (1 / p₁) * B₀ ^ (1 / p₂) + 1 / (N + 1) * I₁) := by
        dsimp only [K]; ring

/-- **Proposition 2.3.5, Eq. (2.62), `(∞, 1)` endpoint.** -/
theorem abs_integral_smartPath_deriv_mul_sub_rhat_le_of_ae_abs_le
    (R : Type uR) [Fintype R] (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N M : ℕ) {r₁ r₂ : R} (_hr : r₁ ≠ r₂)
        {t q : ℝ} (_ht : t ∈ Set.Icc (0 : ℝ) 1) (_hq : q ∈ Set.Icc (0 : ℝ) 1)
        (variance : ℝ≥0)
        {u : ℝ → ℝ} (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        {f : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
        (_hf : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => f p.1 p.2)
        {M_f : ℝ} (_hMf : 0 ≤ M_f),
        let P₀ := smartPathDisorder (Measure.pi fun _ : Fin M =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
        let μ₀ (ω : SmartPathDisorder N M) :=
          (smartPathBase N M).tilted (smartPathEnergy u t ω)
        let P₁ := smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) variance
        let μ₁ (ω : SmartPathDisorder N (M + 1)) :=
          (smartPathBase N (M + 1)).tilted (smartPathEnergy u t ω)
        let f_ext (ω : SmartPathDisorder N (M + 1)) (a : R → SmartPathState N (M + 1)) : ℝ :=
          f ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (fun r => ((a r).1, Fin.init (a r).2))
        let d_spin (σ τ : PerceptronSpin N) : ℝ :=
          |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
            ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
        let average (g : SmartPathDisorder N (M + 1) → (R → SmartPathState N (M + 1)) → ℝ) :=
          ∫ ω, ∫ a, g ω a ∂(Measure.pi fun _ : R => μ₁ ω) ∂P₁
        let weighted := average fun ω a =>
          f_ext ω a * (deriv u (smartPathField t ω (a r₁) (Fin.last M)) *
            deriv u (smartPathField t ω (a r₂) (Fin.last M)))
        let unweighted := average f_ext
        let firstMoment := average fun ω a => |f_ext ω a|
        let overlapMoment : ℝ :=
          ∫ ω, ∫ a : Fin 2 → SmartPathState N (M + 1),
            d_spin (a 0).1 (a 1).1 ∂(Measure.pi fun _ : Fin 2 => μ₁ ω) ∂P₁
        (∀ᵐ ω ∂P₀, ∀ᵐ a ∂(Measure.pi fun _ : R => μ₀ ω), |f ω a| ≤ M_f) →
        |weighted - perceptronRhat u q * unweighted| ≤
          K * (M_f * overlapMoment + 1 / (N + 1) * firstMoment) := by
  let n : ℝ := Fintype.card R
  let M₀w : ℝ := 1 + |D|
  let M₁w : ℝ := |D|
  let L_u : ℝ := 1 + |D| + |(1 : ℝ)| + |(0 : ℝ)| + |(1 : ℝ)| * |D|
  let L_w : ℝ := 1 + |D| + |M₀w| + |M₁w| + |M₀w| * |D|
  let K_u : ℝ := (4 * n ^ 2 + n) * L_u ^ (Fintype.card R + 2)
  let K_w : ℝ := (4 * n ^ 2 + n) * L_w ^ (Fintype.card R + 2)
  let E_dom : ℝ := Real.exp ((4 * n + 8) * |D|)
  let K : ℝ := (K_w / 2 + |D| ^ 2 * (K_u / 2)) * E_dom
  refine ⟨K, by positivity, ?_⟩
  intro N M r₁ r₂ hr t q ht hq variance u hd hb f hf M_f hMf P₀ μ₀ P₁ μ₁ f_ext d_spin
    average weighted unweighted I₁ J₀ hOld
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hD_abs : ∀ x, |u x| ≤ |D| := fun x => (hu.abs_le x).trans (le_abs_self D)
  have hP₀ : IsProbabilityMeasure P₀ := by dsimp [P₀]; rw [smartPathDisorder_eq]; infer_instance
  have hμ₀ (ω : SmartPathDisorder N M) : IsProbabilityMeasure (μ₀ ω) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.measurable (fun x => hu.le x) ω t
  obtain ⟨hfi, hfi₁⟩ := integrable_pi_tilted_and_integrable_integral_abs_of_ae_abs_le
    (measurable_smartPathEnergy hu.measurable t) (ae_of_all P₀ hμ₀) hf hOld
  have hJ₀ : 0 ≤ J₀ := integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _
  have hI₁ : 0 ≤ I₁ := integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _
  let m : ℝ := Real.exp (8 * |D|) * (M_f * J₀)
  have hm0 : 0 ≤ m := by positivity
  let T := SmartPathState N M × (Fin 2 → ℝ)
  let W := (Fin N ⊕ Unit) ⊕ Unit → ℝ
  let γ_sh : Measure W := Measure.pi fun _ => gaussianReal 0 1
  let γ_aux : Measure (Fin 2 → ℝ) := Measure.pi fun _ => gaussianReal 0 1
  let V (s : ℝ) (p : SmartPathDisorder N M × W) (x : T) := u (Real.cos s *
    (Sum.elim (cavityCoef N t x.1.1) 0 ⬝ᵥ p.2 +
      Pi.single 0 (Real.sqrt ((1 - t) / (N + 1))) ⬝ᵥ x.2) +
    Real.sin s * (Sum.elim 0 (fun _ => Real.sqrt q) ⬝ᵥ p.2 +
      Pi.single 1 (Real.sqrt (1 - q)) ⬝ᵥ x.2))
  let νs (s : ℝ) (p : SmartPathDisorder N M × W) := ((μ₀ p.1).prod γ_aux).tilted (V s p)
  have hdo_m : Measurable fun p : SmartPathDisorder N M × (Fin 2 → SmartPathState N M) =>
      d_spin (p.2 0).1 (p.2 1).1 := by
    let b : PerceptronSpin N × PerceptronSpin N → ℝ := fun p => d_spin p.1 p.2
    have hproj : Measurable fun p : SmartPathDisorder N M × (Fin 2 → SmartPathState N M) =>
        ((p.2 0).1, (p.2 1).1) :=
      (measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)).prodMk
        (measurable_fst.comp ((measurable_pi_apply 1).comp measurable_snd))
    have hb' := (measurable_of_finite b).comp hproj
    exact hb'
  have hdo_i : ∀ᵐ ω ∂P₀, Integrable (fun a : Fin 2 → SmartPathState N M =>
      d_spin (a 0).1 (a 1).1) (Measure.pi fun _ : Fin 2 => μ₀ ω) :=
    ae_of_all _ fun ω => by
      have hpω : Measurable fun a : Fin 2 → SmartPathState N M => (ω, a) :=
        measurable_const.prodMk measurable_id
      have hmω := hdo_m.comp hpω
      exact Integrable.of_bound hmω.aestronglyMeasurable 2
        (ae_of_all _ fun a => by
          rw [Real.norm_of_nonneg (abs_nonneg _)]
          exact abs_perceptron_overlap_sub_le_two hq _ _)
  have hdo_m1 := measurable_integral_pi_tilted (μ := smartPathBase N M)
    (E := fun ω => smartPathEnergy u t ω)
    (G := fun _ (a : Fin 2 → SmartPathState N M) => |d_spin (a 0).1 (a 1).1|)
    (measurable_smartPathEnergy hu.measurable t)
    (by simpa only [Real.norm_eq_abs] using hdo_m.norm)
  have hdo_i1 : Integrable (fun ω => ∫ a : Fin 2 → SmartPathState N M,
      |d_spin (a 0).1 (a 1).1| ∂(Measure.pi fun _ : Fin 2 => μ₀ ω)) P₀ :=
    Integrable.of_bound hdo_m1.aestronglyMeasurable 2 (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      exact abs_integral_le_of_forall_abs_le _ fun a => by
        rw [abs_abs, abs_of_nonneg (abs_nonneg _)]
        exact abs_perceptron_overlap_sub_le_two hq _ _)
  have habs_o (a : Fin 2 → SmartPathState N M) :
      |d_spin (a 0).1 (a 1).1| = d_spin (a 0).1 (a 1).1 := abs_of_nonneg (abs_nonneg _)
  have hdo_i1_raw : Integrable (fun ω => ∫ a : Fin 2 → SmartPathState N M,
      d_spin (a 0).1 (a 1).1 ∂(Measure.pi fun _ : Fin 2 => μ₀ ω)) P₀ := by
    simpa only [habs_o] using hdo_i1
  have hmo_0 : ∫ p, ∫ a : Fin 2 → T, d_spin (a 0).1.1 (a 1).1.1
      ∂(Measure.pi fun _ : Fin 2 => νs 0 p) ∂(P₀.prod γ_sh) = J₀ := by
    obtain ⟨_, hFo₁⟩ :=
      integrable_integral_pi_cavity_rotation_abs t q 0 variance hu.toSmartPathPotential
        hdo_m hdo_i hdo_i1
    have habs_o' (a : Fin 2 → T) :
        |d_spin (a 0).1.1 (a 1).1.1| = d_spin (a 0).1.1 (a 1).1.1 :=
      abs_of_nonneg (abs_nonneg _)
    simp only [habs_o'] at hFo₁
    have h0 := integral_integral_pi_cavity_rotation_zero_eq_smartPath hu.toSmartPathPotential
      t q variance (fun _ _ => 1) (fun _ => measurable_const) (M₀ := 1) (fun _ _ => by simp)
      hdo_m hdo_i hdo_i1
    dsimp only at h0
    simp only [Finset.prod_const_one, mul_one] at h0
    exact (integral_prod _ hFo₁).trans h0
  have hdm : Measurable fun p : T × T => d_spin p.1.1.1 p.2.1.1 := by
    let b : PerceptronSpin N × PerceptronSpin N → ℝ := fun p => d_spin p.1 p.2
    have hproj : Measurable fun p : T × T => (p.1.1.1, p.2.1.1) :=
      (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_fst.comp (measurable_fst.comp measurable_snd))
    have h := (measurable_of_finite b).comp hproj
    exact h
  have hd₂m : Measurable fun a : Fin 2 → T => d_spin (a 0).1.1 (a 1).1.1 := by
    have hpair0 : Measurable fun a : Fin 2 → T => (a 0, a 1) :=
      (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
    have h := hdm.comp hpair0
    exact h
  have hpair (s : ℝ) (ι : Type uR) [Fintype ι] (e : R → ι) (he : Function.Injective e)
      (i j : ι) (hij : i ≠ j) :
      ∫ p, ∫ a : ι → T, |f p.1 (fun r => (a (e r)).1)| * d_spin (a i).1.1 (a j).1.1
        ∂(Measure.pi fun _ : ι => νs s p) ∂(P₀.prod γ_sh) ≤ m := by
    have hS := measurable_cavity_rotation_field (N := N) (M := M) t q s
    have : ∀ p, IsProbabilityMeasure (νs s p) := fun p => by
      have hp' : Measurable fun x : T => (p.2, x) := measurable_const.prodMk measurable_id
      have hs := hS.comp hp'
      have hv := hu.measurable.comp hs
      exact isProbabilityMeasure_tilted_of_ae_le hv.aemeasurable
        (ae_of_all _ fun _ => hu.le _)
    have : IsProbabilityMeasure (P₀.prod γ_sh) := inferInstance
    have hFa : ∀ᵐ p ∂(P₀.prod γ_sh), ∀ᵐ a ∂(Measure.pi fun _ : R => νs s p),
        |f p.1 (fun r => (a r).1)| ≤ M_f :=
      ae_pi_tilted_prod_fst P₀ γ_sh μ₀ γ_aux (V s) hOld
    have hFm (p : SmartPathDisorder N M × W) :
        AEStronglyMeasurable (fun a : R → T => f p.1 (fun r => (a r).1))
          (Measure.pi fun _ : R => νs s p) := by
      have ha : Measurable fun a : R → T => (p.1, fun r : R => (a r).1) :=
        measurable_const.prodMk (Measurable.of_eval fun r =>
          measurable_fst.comp (measurable_pi_apply r))
      exact (hf.comp ha).aestronglyMeasurable
    let G (_ : SmartPathDisorder N M × W) (a : Fin 2 → T) := d_spin (a 0).1.1 (a 1).1.1
    have hGm : Measurable fun z : (SmartPathDisorder N M × W) × (Fin 2 → T) => G z.1 z.2 :=
      hd₂m.comp measurable_snd
    have hZ := measurable_integral_pi_cavity_rotation t q s hu.measurable (fun x => hu.le x)
      (F := G) hGm
    have hd_bound (a : Fin 2 → T) : ‖d_spin (a 0).1.1 (a 1).1.1‖ ≤ 2 := by
      rw [Real.norm_of_nonneg (abs_nonneg _)]
      exact abs_perceptron_overlap_sub_le_two hq _ _
    have hd_mem : ∀ᵐ p ∂(P₀.prod γ_sh), Integrable
        (fun a : Fin 2 → T => d_spin (a 0).1.1 (a 1).1.1)
        (Measure.pi fun _ : Fin 2 => νs s p) :=
      ae_of_all _ fun _ => Integrable.of_bound hd₂m.aestronglyMeasurable 2 (ae_of_all _ hd_bound)
    have hd_int : Integrable (fun p => ∫ a : Fin 2 → T, d_spin (a 0).1.1 (a 1).1.1
        ∂(Measure.pi fun _ : Fin 2 => νs s p)) (P₀.prod γ_sh) := by
      refine Integrable.of_bound hZ.aestronglyMeasurable 2 (ae_of_all _ fun p => ?_)
      simpa only [probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const (ae_of_all (Measure.pi fun _ : Fin 2 => νs s p) hd_bound)
    have hh := integral_integral_pair_holder_top_one (P₀.prod γ_sh) (νs s) he hij
      (f := fun p a => f p.1 (fun r => (a r).1)) (ae_of_all _ hFm) hFa
      (d := fun a b => d_spin a.1.1 b.1.1) (fun _ _ => abs_nonneg _) hd_mem hd_int
    have hdom_B : ∫ p, ∫ a : Fin 2 → T, d_spin (a 0).1.1 (a 1).1.1
        ∂(Measure.pi fun _ : Fin 2 => νs s p) ∂(P₀.prod γ_sh) ≤
        Real.exp (8 * |D|) * J₀ := by
      have h := integral_pi_cavity_rotation_nonneg_le_exp_mul hu.measurable hD_abs t q s 0 variance
        hdo_m (fun _ _ => abs_nonneg _) hdo_i hdo_i1_raw
      dsimp only at h
      rw [hmo_0, Fintype.card_fin] at h
      have hexp : Real.exp (4 * ((2 : ℕ) : ℝ) * |D|) = Real.exp (8 * |D|) := by
        congr 1; push_cast; ring
      rwa [hexp] at h
    calc _ ≤ M_f * (∫ p, ∫ a : Fin 2 → T, d_spin (a 0).1.1 (a 1).1.1
            ∂(Measure.pi fun _ : Fin 2 => νs s p) ∂(P₀.prod γ_sh)) := hh
      _ ≤ M_f * (Real.exp (8 * |D|) * J₀) := mul_le_mul_of_nonneg_left hdom_B hMf
      _ = m := by dsimp only [m]; ring
  have hmain := abs_integral_smartPath_deriv_mul_sub_rhat_le_of_split_pair_bound hr ht hq variance
    hd hb hf hm0 hfi hfi₁ hpair
  refine hmain.trans ?_
  have hle_E8 : Real.exp (8 * |D|) ≤ E_dom := Real.exp_le_exp.2 (by
    dsimp only [n]
    nlinarith [abs_nonneg D, (Nat.cast_nonneg (Fintype.card R) : (0 : ℝ) ≤ Fintype.card R)])
  have hle_E1 : Real.exp (4 * n * |D|) ≤ E_dom :=
    Real.exp_le_exp.2 (by linarith [abs_nonneg D])
  have h1 : m + 1 / (N + 1) * Real.exp (4 * n * |D|) * I₁ ≤
      E_dom * (M_f * J₀ + 1 / (N + 1) * I₁) := by
    dsimp only [m]
    have h2 : Real.exp (8 * |D|) * (M_f * J₀) ≤ E_dom * (M_f * J₀) :=
      mul_le_mul_of_nonneg_right hle_E8 (mul_nonneg hMf hJ₀)
    have h3 : 1 / ((N : ℝ) + 1) * Real.exp (4 * n * |D|) * I₁ ≤
        1 / ((N : ℝ) + 1) * E_dom * I₁ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hle_E1 (by positivity)) hI₁
    linarith
  calc _ ≤ (K_w / 2 + |D| ^ 2 * (K_u / 2)) *
          (E_dom * (M_f * J₀ + 1 / (N + 1) * I₁)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = K * (M_f * J₀ + 1 / (N + 1) * I₁) := by dsimp only [K]; ring

end SpinGlasses
