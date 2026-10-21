/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GaussianIBP
public import LeanMachineLearning.SpinGlasses.GaussianComparison

/-!
# Derivative of replica averages along a Gaussian interpolation

Talagrand, Lemma 1.4.2: along an interpolation of two independent Gaussian energy fields the
derivative of the expected `n`-replica Gibbs average `𝔼⟨f⟩` is a combination of the replica
averages of the covariance difference `U`.  This module proves it for the (smooth) trigonometric
path `s ↦ cos s X + sin s Y + h` (see `GaussianComparison.lean`).

The proof has three steps:
1. `hasDerivAt_integral_pi_count_tilted_path`: at a fixed disorder the derivative of a replica
   average along a path of energies `f_s` is `⟨Ψ (∑ᵣ f'(σʳ) - n ⟨f'⟩)⟩`;
2. dominated differentiation under the expectation;
3. two applications of the replica Gaussian integration by parts
   (`integral_gibbs_replica_average_gaussian_option`), one for each of the two kinds of terms.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Lemma 1.4.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Function
open scoped Topology

namespace SpinGlasses

variable {α R : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **Derivative of a replica average along a path of energies.**  If the energies `f s a` have
derivatives `f' a` at `t`, the derivative of `s ↦ ⟨Ψ⟩_{f s}` is
`⟨Ψ (∑ᵣ f'(σʳ) - n ⟨f'⟩)⟩`, where the average `⟨f'⟩` is over an extra independent replica. -/
theorem hasDerivAt_integral_pi_count_tilted_path [Finite α] [Nonempty α] [Fintype R]
    (Ψ : (R → α) → ℝ) (f : ℝ → α → ℝ) (f' : α → ℝ) (t : ℝ)
    (hf : ∀ a, HasDerivAt (fun s => f s a) (f' a) t) :
    HasDerivAt (fun s => ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted (f s)))
      (∫ σ, Ψ σ * (∑ r, f' (σ r) - Fintype.card R * ∫ τ, f' τ ∂(Measure.count.tilted (f t)))
        ∂(Measure.pi fun _ : R => Measure.count.tilted (f t))) t := by
  have := Fintype.ofFinite α
  classical
  set G : (α → ℝ) → ℝ := fun v => ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted v)
    with hG
  have hGd : Differentiable ℝ G := by
    have hfun : G = fun v : α → ℝ => ∑ σ : R → α,
        (∏ r, Real.exp (v (σ r)) / ∑ b, Real.exp (v b)) * Ψ σ :=
      funext fun v => integral_pi_count_tilted v Ψ
    rw [hfun]
    exact differentiable_replicaAverage Ψ
  have hpath : HasDerivAt (fun s => f s) f' t := hasDerivAt_pi.2 hf
  have h1 := (hGd (f t)).hasFDerivAt.comp_hasDerivAt t hpath
  have hlin : f' = ∑ ρ, f' ρ • (Pi.single ρ (1 : ℝ) : α → ℝ) := by
    ext a
    simp [Finset.sum_apply, Pi.single_apply]
  have hval : (∫ σ, Ψ σ * (∑ r, f' (σ r) - Fintype.card R *
        ∫ τ, f' τ ∂(Measure.count.tilted (f t))) ∂(Measure.pi fun _ : R =>
          Measure.count.tilted (f t))) = fderiv ℝ G (f t) f' := by
    have hfd : fderiv ℝ G (f t) f' = ∑ ρ, f' ρ * fderiv ℝ G (f t) (Pi.single ρ 1) := by
      conv_lhs => rw [hlin]
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
    have hint : ∫ τ, f' τ ∂(Measure.count.tilted (f t)) =
        ∑ ρ, (Measure.count.tilted (f t)).real {ρ} * f' ρ := by
      rw [integral_fintype Integrable.of_finite]
      simp [smul_eq_mul]
    rw [hfd, hint]
    simp only [hG, fderiv_integral_pi_count_tilted]
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ fun _ _ => Integrable.of_finite]
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    have h1 : ∑ ρ, f' ρ * (∑ r, if σ r = ρ then (1 : ℝ) else 0) = ∑ r, f' (σ r) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp
    calc Ψ σ * (∑ r, f' (σ r) - Fintype.card R *
            ∑ ρ, (Measure.count.tilted (f t)).real {ρ} * f' ρ)
        = ∑ ρ, f' ρ * (((∑ r, if σ r = ρ then (1 : ℝ) else 0) -
            Fintype.card R * (Measure.count.tilted (f t)).real {ρ}) * Ψ σ) := by
          have : ∀ ρ, f' ρ * (((∑ r, if σ r = ρ then (1 : ℝ) else 0) -
              Fintype.card R * (Measure.count.tilted (f t)).real {ρ}) * Ψ σ) =
              Ψ σ * (f' ρ * (∑ r, if σ r = ρ then (1 : ℝ) else 0)) -
                Ψ σ * Fintype.card R * ((Measure.count.tilted (f t)).real {ρ} * f' ρ) :=
            fun ρ => by ring
          simp_rw [this]
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1]
          ring
      _ = _ := rfl
  rw [hval]
  exact h1

/-- **Derivative of a replica average of a moving observable along a path of energies.**
If, in addition, the observable `Ψ s σ` has derivative `Ψ' σ` at `t`, the derivative of
`s ↦ ⟨Ψ s⟩_{f s}` gains the term `⟨Ψ'⟩`. -/
theorem hasDerivAt_integral_pi_count_tilted_path_moving [Finite α] [Nonempty α] [Fintype R]
    (Ψ : ℝ → (R → α) → ℝ) (Ψ' : (R → α) → ℝ) (f : ℝ → α → ℝ) (f' : α → ℝ) (t : ℝ)
    (hΨ : ∀ σ, HasDerivAt (fun s => Ψ s σ) (Ψ' σ) t)
    (hf : ∀ a, HasDerivAt (fun s => f s a) (f' a) t) :
    HasDerivAt (fun s => ∫ σ, Ψ s σ ∂(Measure.pi fun _ : R => Measure.count.tilted (f s)))
      (∫ σ, Ψ t σ * (∑ r, f' (σ r) - Fintype.card R * ∫ τ, f' τ ∂(Measure.count.tilted (f t)))
        ∂(Measure.pi fun _ : R => Measure.count.tilted (f t)) +
        ∫ σ, Ψ' σ ∂(Measure.pi fun _ : R => Measure.count.tilted (f t))) t := by
  have := Fintype.ofFinite α
  classical
  have h1 := hasDerivAt_integral_pi_count_tilted_path (R := R) (Ψ t) f f' t hf
  have hpath : HasDerivAt (fun s => f s) f' t := hasDerivAt_pi.2 hf
  have hW : ∀ σ : R → α, HasDerivAt (fun s => ∏ r, Real.exp (f s (σ r)) / ∑ b, Real.exp (f s b))
      (fderiv ℝ (fun v : α → ℝ => ∏ r, Real.exp (v (σ r)) / ∑ b, Real.exp (v b)) (f t) f') t :=
    fun σ => by
      have hd : Differentiable ℝ fun v : α → ℝ =>
          ∏ r, Real.exp (v (σ r)) / ∑ b, Real.exp (v b) := by
        have := fun r : R => differentiable_gibbsWeight (σ r)
        fun_prop
      exact (hd (f t)).hasFDerivAt.comp_hasDerivAt t hpath
  have h2 : HasDerivAt (fun s => ∑ σ : R → α, (∏ r, Real.exp (f s (σ r)) / ∑ b, Real.exp (f s b)) *
      (Ψ s σ - Ψ t σ)) (∑ σ : R → α, (∏ r, Real.exp (f t (σ r)) / ∑ b, Real.exp (f t b)) *
        Ψ' σ) t := by
    have := HasDerivAt.fun_sum (u := (Finset.univ : Finset (R → α))) fun σ _ =>
      (hW σ).mul ((hΨ σ).sub_const (Ψ t σ))
    convert this using 1
    simp
  have e : ∀ s, ∫ σ, Ψ s σ ∂(Measure.pi fun _ : R => Measure.count.tilted (f s)) =
      ∫ σ, Ψ t σ ∂(Measure.pi fun _ : R => Measure.count.tilted (f s)) +
        ∑ σ : R → α, (∏ r, Real.exp (f s (σ r)) / ∑ b, Real.exp (f s b)) * (Ψ s σ - Ψ t σ) :=
    fun s => by
      rw [integral_pi_count_tilted, integral_pi_count_tilted, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun σ _ => by ring
  simp_rw [e]
  refine (h1.add h2).congr_deriv ?_
  rw [integral_pi_count_tilted (R := R) (f t) Ψ', integral_pi_count_tilted (R := R) (f t)
    (fun σ => Ψ t σ * (∑ r, f' (σ r) - Fintype.card R * ∫ τ, f' τ ∂(Measure.count.tilted (f t))))]

section Path

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The Gibbs weight of a state depends measurably on a random energy. -/
theorem aemeasurable_gibbsWeight [Fintype α] {g : Ω → α → ℝ}
    (hg : ∀ a, AEMeasurable (fun ω => g ω a) μ) (a : α) :
    AEMeasurable (fun ω => Real.exp (g ω a) / ∑ b, Real.exp (g ω b)) μ := by
  simp_rw [div_eq_mul_inv]
  exact (hg a).exp.mul (Finset.aemeasurable_fun_sum _ fun b _ => (hg b).exp).inv

/-- A replica average of a random observable against the Gibbs measure of a random energy is
measurable in the disorder. -/
theorem aemeasurable_integral_pi_count_tilted [Finite α] [Fintype R] {g : Ω → α → ℝ}
    (hg : ∀ a, AEMeasurable (fun ω => g ω a) μ) {Θ : Ω → (R → α) → ℝ}
    (hΘ : ∀ σ, AEMeasurable (fun ω => Θ ω σ) μ) :
    AEMeasurable (fun ω => ∫ σ, Θ ω σ ∂(Measure.pi fun _ : R => Measure.count.tilted (g ω))) μ := by
  have := Fintype.ofFinite α
  classical
  simp_rw [integral_pi_count_tilted]
  refine Finset.aemeasurable_fun_sum _ fun σ _ => ?_
  exact (Finset.aemeasurable_fun_prod _ fun r _ => aemeasurable_gibbsWeight hg (σ r)).mul (hΘ σ)

/-- The measurable version of `aemeasurable_integral_pi_count_tilted`. -/
theorem measurable_integral_pi_count_tilted [Finite α] [Fintype R] {g : Ω → α → ℝ}
    (hg : ∀ a, Measurable fun ω => g ω a) {Θ : Ω → (R → α) → ℝ}
    (hΘ : ∀ σ, Measurable fun ω => Θ ω σ) :
    Measurable fun ω => ∫ σ, Θ ω σ ∂(Measure.pi fun _ : R => Measure.count.tilted (g ω)) := by
  have := Fintype.ofFinite α
  classical
  simp_rw [integral_pi_count_tilted]
  exact Finset.measurable_fun_sum _ fun σ _ =>
    (Finset.measurable_fun_prod _ fun r _ =>
      (hg (σ r)).exp.div (Finset.measurable_fun_sum _ fun a _ => (hg a).exp)).mul (hΘ σ)

/-- **Differentiation of the expected replica average of a moving observable along a path of
random energies**, by dominated differentiation under the integral. -/
theorem hasDerivAt_integral_replica_path_moving [Finite α] [Nonempty α] [Fintype R]
    [IsFiniteMeasure μ]
    {Ψ Ψ' : ℝ → (R → α) → ℝ} {M M' : ℝ} {S : Set ℝ} {t : ℝ} (hS : S ∈ 𝓝 t)
    (hΨ : ∀ s ∈ S, ∀ σ, HasDerivAt (fun s => Ψ s σ) (Ψ' s σ) s)
    (hM : ∀ s ∈ S, ∀ σ, |Ψ s σ| ≤ M) (hM' : ∀ s ∈ S, ∀ σ, |Ψ' s σ| ≤ M')
    {f f' : ℝ → Ω → α → ℝ} (hmeas : ∀ s a, AEMeasurable (fun ω => f s ω a) μ)
    (hmeas' : ∀ a, AEMeasurable (fun ω => f' t ω a) μ)
    (hderiv : ∀ ω, ∀ s ∈ S, ∀ a, HasDerivAt (fun s => f s ω a) (f' s ω a) s)
    {B : Ω → ℝ} (hB : Integrable B μ) (hbound : ∀ ω, ∀ s ∈ S, ∀ a, |f' s ω a| ≤ B ω) :
    HasDerivAt (fun s => ∫ ω, ∫ σ, Ψ s σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (f s ω)) ∂μ)
      (∫ ω, (∫ σ, Ψ t σ * (∑ r, f' t ω (σ r) - Fintype.card R *
          ∫ τ, f' t ω τ ∂(Measure.count.tilted (f t ω)))
        ∂(Measure.pi fun _ : R => Measure.count.tilted (f t ω)) +
        ∫ σ, Ψ' t σ ∂(Measure.pi fun _ : R => Measure.count.tilted (f t ω))) ∂μ) t := by
  have := Fintype.ofFinite α
  classical
  have htS : t ∈ S := mem_of_mem_nhds hS
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM t htS (fun _ => Classical.arbitrary α))
  have hM'0 : 0 ≤ M' := (abs_nonneg _).trans (hM' t htS (fun _ => Classical.arbitrary α))
  have hF_meas : ∀ s, AEStronglyMeasurable (fun ω => ∫ σ, Ψ s σ
      ∂(Measure.pi fun _ : R => Measure.count.tilted (f s ω))) μ := fun s =>
    (aemeasurable_integral_pi_count_tilted (R := R) (hmeas s)
      (Θ := fun _ σ => Ψ s σ) fun σ => aemeasurable_const).aestronglyMeasurable
  have hF_int : Integrable (fun ω => ∫ σ, Ψ t σ
      ∂(Measure.pi fun _ : R => Measure.count.tilted (f t ω))) μ :=
    Integrable.of_bound (hF_meas t) M (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact abs_integral_pi_count_tilted_le _ (hM t htS))
  have hinner : ∀ ω s, s ∈ S → |∫ τ, f' s ω τ ∂(Measure.count.tilted (f s ω))| ≤ B ω :=
    fun ω s hs => by
      have := norm_integral_le_of_norm_le_const (μ := Measure.count.tilted (f s ω))
        (f := fun a => f' s ω a) (C := B ω)
        (ae_of_all _ fun a => by simpa [Real.norm_eq_abs] using hbound ω s hs a)
      simpa using this
  have hF'_bound : ∀ ω s, s ∈ S → ‖∫ σ, Ψ s σ * (∑ r, f' s ω (σ r) - Fintype.card R *
      ∫ τ, f' s ω τ ∂(Measure.count.tilted (f s ω)))
        ∂(Measure.pi fun _ : R => Measure.count.tilted (f s ω)) +
        ∫ σ, Ψ' s σ ∂(Measure.pi fun _ : R => Measure.count.tilted (f s ω))‖ ≤
      M * (Fintype.card R * B ω + Fintype.card R * B ω) + M' := fun ω s hs => by
    rw [Real.norm_eq_abs]
    have hb := hbound ω s hs
    have hB0 : 0 ≤ B ω := (abs_nonneg _).trans (hb (Classical.arbitrary α))
    refine (abs_add_le _ _).trans (add_le_add ?_ (abs_integral_pi_count_tilted_le _ (hM' s hs)))
    refine abs_integral_pi_count_tilted_le _ fun σ => ?_
    rw [abs_mul]
    refine mul_le_mul (hM s hs σ) ?_ (abs_nonneg _) hM0
    calc |∑ r, f' s ω (σ r) - Fintype.card R * ∫ τ, f' s ω τ ∂(Measure.count.tilted (f s ω))|
        ≤ |∑ r, f' s ω (σ r)| + |(Fintype.card R : ℝ) *
            ∫ τ, f' s ω τ ∂(Measure.count.tilted (f s ω))| := abs_sub _ _
      _ ≤ Fintype.card R * B ω + Fintype.card R * B ω := by
          refine add_le_add ?_ ?_
          · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            calc ∑ r, |f' s ω (σ r)| ≤ ∑ _r : R, B ω :=
                  Finset.sum_le_sum fun r _ => hb _
              _ = Fintype.card R * B ω := by simp
          · rw [abs_mul, Nat.abs_cast]
            exact mul_le_mul_of_nonneg_left (hinner ω s hs) (Nat.cast_nonneg _)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le hS (Eventually.of_forall hF_meas)
    hF_int (F' := fun s ω => ∫ σ, Ψ s σ * (∑ r, f' s ω (σ r) - Fintype.card R *
        ∫ τ, f' s ω τ ∂(Measure.count.tilted (f s ω)))
          ∂(Measure.pi fun _ : R => Measure.count.tilted (f s ω)) +
        ∫ σ, Ψ' s σ ∂(Measure.pi fun _ : R => Measure.count.tilted (f s ω)))
    ?_ (bound := fun ω => M * (Fintype.card R * B ω + Fintype.card R * B ω) + M')
    (ae_of_all _ fun ω s hs => hF'_bound ω s hs) ?_
    (ae_of_all _ fun ω s hs => ?_)).2
  · refine AEStronglyMeasurable.add ?_ ?_
    · refine aemeasurable_integral_pi_count_tilted (hmeas t) (fun σ => ?_) |>.aestronglyMeasurable
      refine aemeasurable_const.mul ?_
      refine (Finset.aemeasurable_fun_sum _ fun r _ => hmeas' (σ r)).sub ?_
      refine aemeasurable_const.mul ?_
      simp_rw [integral_count_tilted]
      exact Finset.aemeasurable_fun_sum _ fun a _ => (aemeasurable_gibbsWeight (hmeas t) a).mul
        (hmeas' a)
    · exact (aemeasurable_integral_pi_count_tilted (R := R) (hmeas t)
        (Θ := fun _ σ => Ψ' t σ) fun σ => aemeasurable_const).aestronglyMeasurable
  · exact ((((hB.const_mul (Fintype.card R : ℝ)).add (hB.const_mul (Fintype.card R : ℝ))).const_mul
      M).add (integrable_const M'))
  · exact hasDerivAt_integral_pi_count_tilted_path_moving (fun s' => Ψ s') (Ψ' s) (fun s => f s ω)
      (f' s ω) s (fun σ => hΨ s hs σ) (fun a => hderiv ω s hs a)

/-- **Differentiation of the expected replica average along a path of random energies**
(fixed observable). -/
theorem hasDerivAt_integral_replica_path [Finite α] [Nonempty α] [Fintype R] [IsFiniteMeasure μ]
    {Ψ : (R → α) → ℝ} {M : ℝ} (hΨ : ∀ σ, |Ψ σ| ≤ M) {S : Set ℝ} {t : ℝ} (hS : S ∈ 𝓝 t)
    {f f' : ℝ → Ω → α → ℝ} (hmeas : ∀ s a, AEMeasurable (fun ω => f s ω a) μ)
    (hmeas' : ∀ a, AEMeasurable (fun ω => f' t ω a) μ)
    (hderiv : ∀ ω, ∀ s ∈ S, ∀ a, HasDerivAt (fun s => f s ω a) (f' s ω a) s)
    {B : Ω → ℝ} (hB : Integrable B μ) (hbound : ∀ ω, ∀ s ∈ S, ∀ a, |f' s ω a| ≤ B ω) :
    HasDerivAt (fun s => ∫ ω, ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted (f s ω)) ∂μ)
      (∫ ω, ∫ σ, Ψ σ * (∑ r, f' t ω (σ r) - Fintype.card R *
          ∫ τ, f' t ω τ ∂(Measure.count.tilted (f t ω)))
        ∂(Measure.pi fun _ : R => Measure.count.tilted (f t ω)) ∂μ) t := by
  have h := hasDerivAt_integral_replica_path_moving (μ := μ) (Ψ := fun _ => Ψ)
    (Ψ' := fun _ _ => 0) (M := M) (M' := 0) hS (fun s _ σ => hasDerivAt_const s (Ψ σ))
    (fun _ _ σ => hΨ σ) (fun _ _ _ => by simp) hmeas hmeas' hderiv hB hbound
  simpa using h

end Path

section Trig

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : α → Ω → ℝ}

/-- The replica average of `Φ χ(σ^{r})` is integrable in the disorder when `χ` is, and `Φ` is
bounded. -/
theorem integrable_integral_pi_count_tilted_mul_eval [Finite α] [Nonempty α] [Fintype R]
    {g χ : α → Ω → ℝ} (hg : ∀ a, AEMeasurable (fun ω => g a ω) P)
    (hχm : ∀ a, AEMeasurable (χ a) P) (hχ : ∀ a, Integrable (χ a) P) {Φ : (R → α) → ℝ} {M : ℝ}
    (hΦ : ∀ σ, |Φ σ| ≤ M) (r : R) :
    Integrable (fun ω => ∫ σ, Φ σ * χ (σ r) ω
      ∂(Measure.pi fun _ : R => Measure.count.tilted fun a => g a ω)) P := by
  have := Fintype.ofFinite α
  have hmeas := aemeasurable_integral_pi_count_tilted (R := R) (g := fun ω a => g a ω)
    (Θ := fun ω σ => Φ σ * χ (σ r) ω) hg fun σ => aemeasurable_const.mul (hχm (σ r))
  refine Integrable.mono' ((integrable_finsetSum (Finset.univ : Finset α)
    fun a _ => (hχ a).abs).const_mul M) hmeas.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  have h := abs_integral_pi_count_tilted_mul_eval_le (fun a => g a ω) (fun a => χ a ω) r hΦ
  rw [Real.norm_eq_abs]
  refine h.trans (mul_le_mul_of_nonneg_left ?_ ((abs_nonneg _).trans (hΦ (fun _ =>
    Classical.arbitrary α))))
  have := norm_integral_count_tilted_le (fun a => g a ω) (fun a => |χ a ω|)
  simpa using (le_abs_self _).trans (by simpa using this)

/-- The replica average of `Φ ⟨χ⟩` (the extra replica integrated out) is integrable in the
disorder. -/
theorem integrable_integral_pi_count_tilted_mul_integral [Finite α] [Nonempty α] [Fintype R]
    {g χ : α → Ω → ℝ} (hg : ∀ a, AEMeasurable (fun ω => g a ω) P)
    (hχm : ∀ a, AEMeasurable (χ a) P) (hχ : ∀ a, Integrable (χ a) P) {Φ : (R → α) → ℝ} {M : ℝ}
    (hΦ : ∀ σ, |Φ σ| ≤ M) :
    Integrable (fun ω => ∫ σ, Φ σ * ∫ a, χ a ω ∂(Measure.count.tilted fun a => g a ω)
      ∂(Measure.pi fun _ : R => Measure.count.tilted fun a => g a ω)) P := by
  have := Fintype.ofFinite α
  have hmeas := aemeasurable_integral_pi_count_tilted (R := R) (g := fun ω a => g a ω)
    (Θ := fun ω σ => Φ σ * ∫ a, χ a ω ∂(Measure.count.tilted fun a => g a ω)) hg fun σ => by
      refine aemeasurable_const.mul ?_
      simp_rw [integral_count_tilted]
      exact Finset.aemeasurable_fun_sum _ fun a _ =>
        (aemeasurable_gibbsWeight (g := fun ω a => g a ω) hg a).mul (hχm a)
  refine Integrable.mono' ((integrable_finsetSum (Finset.univ : Finset α)
    fun a _ => (hχ a).abs).const_mul M) hmeas.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  have hM : 0 ≤ M := (abs_nonneg _).trans (hΦ (fun _ => Classical.arbitrary α))
  refine abs_integral_pi_count_tilted_le _ fun σ => ?_
  rw [abs_mul]
  refine mul_le_mul (hΦ σ) ?_ (abs_nonneg _) hM
  simpa using norm_integral_count_tilted_le (fun a => g a ω) (fun a => χ a ω)

/-- A replica average of a deterministic observable is integrable in the disorder. -/
theorem integrable_integral_pi_count_tilted_det [Finite α] [Nonempty α] [Fintype R]
    [IsFiniteMeasure P] {g : α → Ω → ℝ} (hg : ∀ a, AEMeasurable (fun ω => g a ω) P)
    (Θ : (R → α) → ℝ) :
    Integrable (fun ω => ∫ σ, Θ σ ∂(Measure.pi fun _ : R => Measure.count.tilted fun a => g a ω))
      P := by
  have := Fintype.ofFinite α
  obtain ⟨M, hM⟩ : ∃ M, ∀ σ, |Θ σ| ≤ M :=
    (Set.finite_range fun σ => |Θ σ|).bddAbove.imp fun M hM σ => hM ⟨σ, rfl⟩
  exact Integrable.of_bound (aemeasurable_integral_pi_count_tilted (R := R)
    (g := fun ω a => g a ω) (Θ := fun _ σ => Θ σ) hg (fun _ => aemeasurable_const)
    |>.aestronglyMeasurable) M (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact abs_integral_pi_count_tilted_le _ hM)

/-- **Marginalizing an extra replica.** A function of `n + 1` replicas that does not depend on the
last one has the same average as the `n`-replica function. -/
theorem integral_pi_option_count_tilted_marginal [Finite α] [Nonempty α] [Fintype R]
    (f : α → ℝ)
    (G : (R → α) → ℝ) :
    ∫ τ, G (fun r => τ (some r)) ∂(Measure.pi fun _ : Option R => Measure.count.tilted f) =
      ∫ σ, G σ ∂(Measure.pi fun _ : R => Measure.count.tilted f) := by
  have := Fintype.ofFinite α
  have h := integral_pi_option_count_tilted (R := R) f (fun σ _ => G σ)
  simpa [integral_const, probReal_univ] using h

/-- Marginalizing two extra replicas. -/
theorem integral_pi_option_option_count_tilted_marginal [Finite α] [Nonempty α] [Fintype R]
    (f : α → ℝ) (G : (R → α) → ℝ) :
    ∫ τ, G (fun r => τ (some (some r)))
        ∂(Measure.pi fun _ : Option (Option R) => Measure.count.tilted f) =
      ∫ σ, G σ ∂(Measure.pi fun _ : R => Measure.count.tilted f) :=
  (integral_pi_option_count_tilted_marginal (R := Option R) f fun ν => G fun r => ν (some r)).trans
    (integral_pi_option_count_tilted_marginal (R := R) f G)

variable [Finite α] [Nonempty α] [Fintype R]

/-- **Key identity of Lemma 1.4.2:** the two Gaussian integrations by parts turn the derivative
`𝔼⟨Φ (∑ᵣ u'(σʳ) - n ⟨u'⟩)⟩` of the replica average into the covariance combination. -/
theorem integral_replica_trig_key
    (hXm : ∀ a, Measurable (X a)) (hYm : ∀ a, Measurable (Y a))
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (hX : ∀ a, ∫ ω, X a ω ∂P = 0) (hY : ∀ a, ∫ ω, Y a ω ∂P = 0)
    (h0 : ∀ a b, ∫ ω, X a ω * Y b ω ∂P = 0) (U : α → α → ℝ)
    (hU : ∀ a b, U a b = ∫ ω, Y a ω * Y b ω ∂P - ∫ ω, X a ω * X b ω ∂P) (h : α → ℝ)
    {Φ : (R → α) → ℝ} {M : ℝ} (hM : ∀ σ, |Φ σ| ≤ M) (t : ℝ) :
    (∫ ω, ∫ σ, Φ σ * (∑ r, (-Real.sin t * X (σ r) ω + Real.cos t * Y (σ r) ω) -
        Fintype.card R * ∫ τ, (-Real.sin t * X τ ω + Real.cos t * Y τ ω)
          ∂(Measure.count.tilted fun a => Real.cos t * X a ω + Real.sin t * Y a ω + h a))
      ∂(Measure.pi fun _ : R =>
          Measure.count.tilted fun a => Real.cos t * X a ω + Real.sin t * Y a ω + h a) ∂P) =
      Real.sin t * Real.cos t * ∫ ω, ∫ τ : Option (Option R) → α,
        Φ (fun r => τ (some (some r))) *
          ((∑ r, ∑ r', U (τ (some (some r))) (τ (some (some r')))) -
            2 * Fintype.card R * ∑ r, U (τ (some (some r))) (τ (some none)) -
            Fintype.card R * U (τ (some none)) (τ (some none)) +
            Fintype.card R * (Fintype.card R + 1) * U (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option R) =>
          Measure.count.tilted fun a => Real.cos t * X a ω + Real.sin t * Y a ω + h a) ∂P := by
  have := Fintype.ofFinite α
  classical
  have hP := hXY.isProbabilityMeasure
  have hXi : ∀ a, Integrable (X a) P := fun a => (hXY.eval (Sum.inl a)).integrable
  have hYi : ∀ a, Integrable (Y a) P := fun a => (hXY.eval (Sum.inr a)).integrable
  -- the pair `(x, y) = (u', u)` of the Gaussian integration by parts
  obtain ⟨x, hx⟩ : ∃ x : α → Ω → ℝ, ∀ a ω, x a ω = -Real.sin t * X a ω + Real.cos t * Y a ω :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : α → Ω → ℝ, ∀ a ω, y a ω = Real.cos t * X a ω + Real.sin t * Y a ω :=
    ⟨_, fun _ _ => rfl⟩
  have hxyG : HasGaussianLaw (fun ω s => Sum.elim x y s ω) P := by
    have := hasGaussianLaw_sumElim_lincomb hXY (-Real.sin t) (Real.cos t) (Real.cos t)
      (Real.sin t)
    have e : (fun ω s => Sum.elim x y s ω) = fun ω c => Sum.elim
        (fun a ω => -Real.sin t * X a ω + Real.cos t * Y a ω)
        (fun a ω => Real.cos t * X a ω + Real.sin t * Y a ω) c ω := by
      funext ω c
      rcases c with a | a
      · exact hx a ω
      · exact hy a ω
    rw [e]
    exact this
  have hx0 : ∀ a, ∫ ω, x a ω ∂P = 0 := fun a => by
    simp only [hx]
    exact integral_lincomb_eq_zero hX hY hXi hYi _ _ a
  have hy0 : ∀ a, ∫ ω, y a ω ∂P = 0 := fun a => by
    simp only [hy]
    exact integral_lincomb_eq_zero hX hY hXi hYi _ _ a
  obtain ⟨C, hC⟩ : ∃ C : α → α → ℝ, ∀ a b, C a b = ∫ ω, x a ω * y b ω ∂P :=
    ⟨_, fun _ _ => rfl⟩
  have hCU : ∀ a b, C a b = Real.sin t * Real.cos t * U a b := fun a b => by
    rw [hC, hU]
    simp only [hx, hy]
    rw [integral_lincomb_mul_lincomb hXY h0]
    ring
  have hUsymm : ∀ a b, U a b = U b a := fun a b => by
    rw [hU, hU]
    simp_rw [mul_comm (Y a _), mul_comm (X a _)]
  obtain ⟨μt, hμt⟩ : ∃ μt : Ω → Measure α, ∀ ω,
      μt ω = Measure.count.tilted fun a => y a ω + h a := ⟨_, fun _ => rfl⟩
  have hxm : ∀ a, Measurable (x a) := fun a => by
    have e : x a = fun ω => -Real.sin t * X a ω + Real.cos t * Y a ω := funext (hx a)
    rw [e]; exact ((hXm a).const_mul _).add ((hYm a).const_mul _)
  have hym : ∀ a, Measurable (y a) := fun a => by
    have e : y a = fun ω => Real.cos t * X a ω + Real.sin t * Y a ω := funext (hy a)
    rw [e]; exact ((hXm a).const_mul _).add ((hYm a).const_mul _)
  have hxi : ∀ a, Integrable (x a) P := fun a => by
    have e : x a = fun ω => -Real.sin t * X a ω + Real.cos t * Y a ω := funext (hx a)
    rw [e]; exact ((hXi a).const_mul _).add ((hYi a).const_mul _)
  have hg : ∀ a, AEMeasurable (fun ω => y a ω + h a) P := fun a =>
    ((hym a).add_const _).aemeasurable
  -- Gaussian integration by parts, twice
  have IBP1 : ∀ r₀ : R, ∫ ω, ∫ σ, Φ σ * x (σ r₀) ω ∂(Measure.pi fun _ : R => μt ω) ∂P =
      ∫ ω, ∫ τ : Option R → α, Φ (fun r => τ (some r)) * (∑ r, C (τ (some r₀)) (τ (some r)) -
        Fintype.card R * C (τ (some r₀)) (τ none))
        ∂(Measure.pi fun _ : Option R => μt ω) ∂P := fun r₀ => by
    simpa only [hμt] using integral_gibbs_replica_average_gaussian_option x y hxyG hx0 hy0 C hC h
      r₀ Φ
  have IBP2 : ∫ ω, ∫ ρ : Option R → α, Φ (fun r => ρ (some r)) * x (ρ none) ω
      ∂(Measure.pi fun _ : Option R => μt ω) ∂P =
      ∫ ω, ∫ ν : Option (Option R) → α, Φ (fun r => ν (some (some r))) *
        (∑ r'' : Option R, C (ν (some none)) (ν (some r'')) -
          Fintype.card (Option R) * C (ν (some none)) (ν none))
        ∂(Measure.pi fun _ : Option (Option R) => μt ω) ∂P := by
    simpa only [hμt] using integral_gibbs_replica_average_gaussian_option (R := Option R) x y hxyG
      hx0 hy0 C hC h none (fun ρ => Φ (fun r => ρ (some r)))
  have IB : ∀ ω, ∫ σ, Φ σ * ∫ a, x a ω ∂(μt ω) ∂(Measure.pi fun _ : R => μt ω) =
      ∫ ρ : Option R → α, Φ (fun r => ρ (some r)) * x (ρ none) ω
        ∂(Measure.pi fun _ : Option R => μt ω) := fun ω => by
    have h1 := integral_pi_option_count_tilted (R := R) (fun a => y a ω + h a)
      (fun σ a => Φ σ * x a ω)
    simp only [integral_const_mul, ← hμt] at h1 ⊢
    exact h1.symm
  simp only [← hx, ← hy, ← hμt]
  -- split the derivative into the `∑ᵣ`-terms and the extra-replica term
  have hμprob : ∀ ω, IsProbabilityMeasure (μt ω) := fun ω => by rw [hμt]; infer_instance
  have hsplit : ∀ ω, ∫ σ, Φ σ * (∑ r, x (σ r) ω - Fintype.card R * ∫ a, x a ω ∂(μt ω))
        ∂(Measure.pi fun _ : R => μt ω) =
      ∑ r, ∫ σ, Φ σ * x (σ r) ω ∂(Measure.pi fun _ : R => μt ω) -
        Fintype.card R * ∫ σ, Φ σ * ∫ a, x a ω ∂(μt ω) ∂(Measure.pi fun _ : R => μt ω) :=
    fun ω => by
      have e : ∀ σ : R → α, Φ σ * (∑ r, x (σ r) ω - Fintype.card R * ∫ a, x a ω ∂(μt ω)) =
          ∑ r, Φ σ * x (σ r) ω - Fintype.card R * (Φ σ * ∫ a, x a ω ∂(μt ω)) := fun σ => by
        rw [mul_sub, Finset.mul_sum]
        ring
      simp_rw [e]
      rw [integral_sub
          (integrable_finsetSum _ fun _ _ => Integrable.of_finite) (Integrable.of_finite),
        integral_finsetSum _ fun _ _ => Integrable.of_finite, integral_const_mul]
  have ha : ∀ r, Integrable (fun ω => ∫ σ, Φ σ * x (σ r) ω
      ∂(Measure.pi fun _ : R => μt ω)) P := fun r => by
    simp only [hμt]
    exact integrable_integral_pi_count_tilted_mul_eval (g := fun a ω => y a ω + h a)
      (fun a => hg a) (fun a => (hxm a).aemeasurable) hxi hM r
  have hb : Integrable (fun ω => ∫ σ, Φ σ * ∫ a, x a ω ∂(μt ω)
      ∂(Measure.pi fun _ : R => μt ω)) P := by
    simp only [hμt]
    exact integrable_integral_pi_count_tilted_mul_integral (g := fun a ω => y a ω + h a)
      (fun a => hg a) (fun a => (hxm a).aemeasurable) hxi hM
  simp_rw [hsplit]
  rw [integral_sub (integrable_finsetSum _ fun r _ => ha r) (hb.const_mul _),
    integral_finsetSum _ fun r _ => ha r, integral_const_mul]
  simp_rw [IB]
  rw [IBP2]
  simp_rw [IBP1]
  -- put every term on the space of `n + 2` replicas
  have hmarg : ∀ (ω : Ω) (G : (Option R → α) → ℝ),
      ∫ τ, G τ ∂(Measure.pi fun _ : Option R => μt ω) =
        ∫ ν : Option (Option R) → α, G (fun o => ν (some o))
          ∂(Measure.pi fun _ : Option (Option R) => μt ω) := fun ω G => by
    rw [hμt]
    exact (integral_pi_option_count_tilted_marginal _ G).symm
  simp_rw [hmarg]
  have hdet : ∀ Θ : (Option (Option R) → α) → ℝ, Integrable (fun ω => ∫ ν, Θ ν
      ∂(Measure.pi fun _ : Option (Option R) => μt ω)) P := fun Θ => by
    simp only [hμt]
    exact integrable_integral_pi_count_tilted_det (g := fun a ω => y a ω + h a) hg Θ
  let G1 : R → (Option (Option R) → α) → ℝ := fun r₀ ν =>
    Φ (fun r => ν (some (some r))) * (∑ r, C (ν (some (some r₀))) (ν (some (some r))) -
      (Fintype.card R : ℝ) * C (ν (some (some r₀))) (ν (some none)))
  let G2 : (Option (Option R) → α) → ℝ := fun ν =>
    Φ (fun r => ν (some (some r))) * (∑ r'' : Option R, C (ν (some none)) (ν (some r'')) -
      (Fintype.card (Option R) : ℝ) * C (ν (some none)) (ν none))
  let G3 : (Option (Option R) → α) → ℝ := fun ν =>
    Φ (fun r => ν (some (some r))) *
      ((∑ r, ∑ r', U (ν (some (some r))) (ν (some (some r')))) -
        2 * Fintype.card R * ∑ r, U (ν (some (some r))) (ν (some none)) -
        Fintype.card R * U (ν (some none)) (ν (some none)) +
        Fintype.card R * (Fintype.card R + 1) * U (ν (some none)) (ν none))
  change ∑ r₀, ∫ ω, ∫ ν, G1 r₀ ν ∂(Measure.pi fun _ : Option (Option R) => μt ω) ∂P -
      Fintype.card R * ∫ ω, ∫ ν, G2 ν ∂(Measure.pi fun _ : Option (Option R) => μt ω) ∂P =
    Real.sin t * Real.cos t * ∫ ω, ∫ ν, G3 ν
      ∂(Measure.pi fun _ : Option (Option R) => μt ω) ∂P
  have hpt : ∀ ν, ∑ r₀, G1 r₀ ν - Fintype.card R * G2 ν = Real.sin t * Real.cos t * G3 ν :=
    fun ν => by
      simp only [G1, G2, G3, Fintype.sum_option, Fintype.card_option, hCU,
        hUsymm (ν (some none)) _]
      rw [hUsymm (ν none) (ν (some none))]
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
      push_cast
      ring
  have hinner : ∀ ω, ∑ r₀, ∫ ν, G1 r₀ ν ∂(Measure.pi fun _ : Option (Option R) => μt ω) -
      Fintype.card R * ∫ ν, G2 ν ∂(Measure.pi fun _ : Option (Option R) => μt ω) =
      ∫ ν, (∑ r₀, G1 r₀ ν - Fintype.card R * G2 ν)
        ∂(Measure.pi fun _ : Option (Option R) => μt ω) := fun ω => by
    rw [integral_sub (integrable_finsetSum _ fun _ _ => Integrable.of_finite)
      (Integrable.of_finite.const_mul _), integral_finsetSum _ fun _ _ => Integrable.of_finite,
      integral_const_mul]
  have hdet : ∀ Θ : (Option (Option R) → α) → ℝ, Integrable (fun ω => ∫ ν, Θ ν
      ∂(Measure.pi fun _ : Option (Option R) => μt ω)) P := fun Θ => by
    simp only [hμt]
    exact integrable_integral_pi_count_tilted_det (g := fun a ω => y a ω + h a) hg Θ
  calc ∑ r₀, ∫ ω, ∫ ν, G1 r₀ ν ∂(Measure.pi fun _ : Option (Option R) => μt ω) ∂P -
        Fintype.card R * ∫ ω, ∫ ν, G2 ν ∂(Measure.pi fun _ : Option (Option R) => μt ω) ∂P
      = ∫ ω, (∑ r₀, ∫ ν, G1 r₀ ν ∂(Measure.pi fun _ : Option (Option R) => μt ω) -
          Fintype.card R * ∫ ν, G2 ν ∂(Measure.pi fun _ : Option (Option R) => μt ω)) ∂P := by
        rw [integral_sub (integrable_finsetSum _ fun _ _ => hdet _) ((hdet _).const_mul _),
          integral_finsetSum _ fun _ _ => hdet _, integral_const_mul]
    _ = ∫ ω, ∫ ν, Real.sin t * Real.cos t * G3 ν
          ∂(Measure.pi fun _ : Option (Option R) => μt ω) ∂P := by
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        simp only
        rw [hinner]
        exact integral_congr_ae (ae_of_all _ fun ν => hpt ν)
    _ = _ := by
        simp_rw [integral_const_mul]


/-- **Lemma 1.4.2 (replica derivative along a Gaussian interpolation), trigonometric form.**
Let `(X, Y)` be a centered jointly Gaussian pair of fields with `𝔼 X Y = 0` and let
`U(a, b) = 𝔼 Y_a Y_b - 𝔼 X_a X_b`.  For a bounded observable `Φ` of `n = |R|` replicas, the
derivative of `s ↦ 𝔼⟨Φ⟩_s`, where `⟨·⟩_s` is the Gibbs average of `cos s X + sin s Y + h`, is
`sin t cos t · 𝔼⟨Φ (∑_{ℓ,ℓ'≤n} U(σˡ, σˡ') - 2n ∑_{ℓ≤n} U(σˡ, σ^{n+1}) - n U(σ^{n+1}, σ^{n+1})
  + n(n+1) U(σ^{n+1}, σ^{n+2}))⟩_t`
at `s = t`, the replicas `σ^{n+1}`, `σ^{n+2}` being the `some none` and `none` of
`Option (Option R)`. -/
theorem hasDerivAt_integral_replica_trig
    (hXm : ∀ a, Measurable (X a)) (hYm : ∀ a, Measurable (Y a))
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (hX : ∀ a, ∫ ω, X a ω ∂P = 0) (hY : ∀ a, ∫ ω, Y a ω ∂P = 0)
    (h0 : ∀ a b, ∫ ω, X a ω * Y b ω ∂P = 0) (U : α → α → ℝ)
    (hU : ∀ a b, U a b = ∫ ω, Y a ω * Y b ω ∂P - ∫ ω, X a ω * X b ω ∂P) (h : α → ℝ)
    (Φ : (R → α) → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ∫ ω, ∫ σ, Φ σ ∂(Measure.pi fun _ : R =>
        Measure.count.tilted fun a => Real.cos s * X a ω + Real.sin s * Y a ω + h a) ∂P)
      (Real.sin t * Real.cos t * ∫ ω, ∫ τ : Option (Option R) → α,
        Φ (fun r => τ (some (some r))) *
          ((∑ r, ∑ r', U (τ (some (some r))) (τ (some (some r')))) -
            2 * Fintype.card R * ∑ r, U (τ (some (some r))) (τ (some none)) -
            Fintype.card R * U (τ (some none)) (τ (some none)) +
            Fintype.card R * (Fintype.card R + 1) * U (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option R) =>
          Measure.count.tilted fun a => Real.cos t * X a ω + Real.sin t * Y a ω + h a) ∂P) t := by
  have := Fintype.ofFinite α
  have hP := hXY.isProbabilityMeasure
  have hXi : ∀ a, Integrable (X a) P := fun a => (hXY.eval (Sum.inl a)).integrable
  have hYi : ∀ a, Integrable (Y a) P := fun a => (hXY.eval (Sum.inr a)).integrable
  obtain ⟨M, hM⟩ : ∃ M, ∀ σ, |Φ σ| ≤ M :=
    (Set.finite_range fun σ => |Φ σ|).bddAbove.imp fun M hM σ => hM ⟨σ, rfl⟩
  have hpath := hasDerivAt_integral_replica_path (μ := P) (t := t) (S := Set.univ) (R := R)
    (Ψ := Φ) hM Filter.univ_mem
    (f := fun s ω a => Real.cos s * X a ω + Real.sin s * Y a ω + h a)
    (f' := fun s ω a => -Real.sin s * X a ω + Real.cos s * Y a ω)
    (fun s a => (((hXm a).const_mul _).add ((hYm a).const_mul _)).add_const _ |>.aemeasurable)
    (fun a => (((hXm a).const_mul _).add ((hYm a).const_mul _)).aemeasurable)
    (fun ω s _ a => hasDerivAt_cos_mul_add_sin_mul (X a ω) (Y a ω) (h a) s)
    (B := fun ω => ∑ a, (|X a ω| + |Y a ω|))
    (integrable_finsetSum _ fun a _ => (hXi a).abs.add (hYi a).abs)
    (fun ω s _ a => abs_neg_sin_mul_add_cos_mul_le_sum (fun b => X b ω) (fun b => Y b ω) s a)
  exact hpath.congr_deriv (integral_replica_trig_key hXm hYm hXY hX hY h0 U hU h hM t)

/-- Integrate a conditional derivative over independent base disorder. In a cavity
interpolation the covariance formula bounds this derivative independently of the old
couplings, so the domination is constant rather than Gaussian-dependent. -/
theorem hasDerivAt_integral_conditional_of_deriv_bound
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    [Nonempty Ω₀] (F D : ℝ → Ω₀ → ℝ) (t : ℝ)
    (hFm : ∀ s, AEStronglyMeasurable (F s) P₀)
    (hDm : AEStronglyMeasurable (D t) P₀)
    (hF : Integrable (F t) P₀)
    (hderiv : ∀ η s, HasDerivAt (fun u => F u η) (D s η) s)
    (M : ℝ) (hbound : ∀ η s, |D s η| ≤ M) :
    HasDerivAt (fun s => ∫ η, F s η ∂P₀) (∫ η, D t η ∂P₀) t := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbound (Classical.arbitrary Ω₀) t)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := P₀) (x₀ := t) (F := F) (F' := D)
    Filter.univ_mem (Eventually.of_forall hFm) hF hDm
    (bound := fun _ => M)
    (ae_of_all _ fun η s _ => by
      simpa only [Real.norm_eq_abs] using hbound η s)
    (integrable_const M) (ae_of_all _ fun η s _ => hderiv η s)).2

/-- The replica-derivative term `𝔼⟨Ψ (∑ᵣ f'(σʳ) - n ⟨f'⟩)⟩` is integrable in the disorder when
`f'` is dominated by an integrable function. -/
theorem integrable_replica_derivative_term {g χ : α → Ω → ℝ}
    (hg : ∀ a, AEMeasurable (fun ω => g a ω) P) (hχm : ∀ a, AEMeasurable (χ a) P)
    {B : Ω → ℝ} (hB : Integrable B P) (hχ : ∀ ω a, |χ a ω| ≤ B ω) {Ψ : (R → α) → ℝ} {M : ℝ}
    (hΨ : ∀ σ, |Ψ σ| ≤ M) :
    Integrable (fun ω => ∫ σ, Ψ σ * (∑ r, χ (σ r) ω - Fintype.card R *
        ∫ a, χ a ω ∂(Measure.count.tilted fun a => g a ω))
      ∂(Measure.pi fun _ : R => Measure.count.tilted fun a => g a ω)) P := by
  have := Fintype.ofFinite α
  classical
  have hM : 0 ≤ M := (abs_nonneg _).trans (hΨ (fun _ => Classical.arbitrary α))
  have hmeas := aemeasurable_integral_pi_count_tilted (R := R) (g := fun ω a => g a ω)
    (Θ := fun ω σ => Ψ σ * (∑ r, χ (σ r) ω - Fintype.card R *
      ∫ a, χ a ω ∂(Measure.count.tilted fun a => g a ω))) hg fun σ => by
      refine aemeasurable_const.mul ((Finset.aemeasurable_fun_sum _ fun r _ => hχm (σ r)).sub ?_)
      refine aemeasurable_const.mul ?_
      simp_rw [integral_count_tilted]
      exact Finset.aemeasurable_fun_sum _ fun a _ =>
        (aemeasurable_gibbsWeight (g := fun ω a => g a ω) hg a).mul (hχm a)
  refine Integrable.mono' ((hB.const_mul (Fintype.card R : ℝ)).add
    (hB.const_mul (Fintype.card R : ℝ)) |>.const_mul M) hmeas.aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  have hB0 : 0 ≤ B ω := (abs_nonneg _).trans (hχ ω (Classical.arbitrary α))
  refine abs_integral_pi_count_tilted_le _ fun σ => ?_
  rw [abs_mul]
  refine mul_le_mul (hΨ σ) ?_ (abs_nonneg _) hM
  have hin : |∫ a, χ a ω ∂(Measure.count.tilted fun a => g a ω)| ≤ B ω := by
    have := norm_integral_le_of_norm_le_const (μ := Measure.count.tilted fun a => g a ω)
      (f := fun a => χ a ω) (C := B ω)
      (ae_of_all _ fun a => by simpa [Real.norm_eq_abs] using hχ ω a)
    simpa using this
  calc |∑ r, χ (σ r) ω - Fintype.card R * ∫ a, χ a ω ∂(Measure.count.tilted fun a => g a ω)|
      ≤ |∑ r, χ (σ r) ω| + |(Fintype.card R : ℝ) *
          ∫ a, χ a ω ∂(Measure.count.tilted fun a => g a ω)| := abs_sub _ _
    _ ≤ Fintype.card R * B ω + Fintype.card R * B ω := by
        refine add_le_add ?_ ?_
        · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          calc ∑ r, |χ (σ r) ω| ≤ ∑ _r : R, B ω := Finset.sum_le_sum fun r _ => hχ ω _
            _ = Fintype.card R * B ω := by simp
        · rw [abs_mul, Nat.abs_cast]
          exact mul_le_mul_of_nonneg_left hin (Nat.cast_nonneg _)

/-- **Lemma 1.4.2 with a moving observable.**  If the observable `Φ s` of the `n` replicas also
depends smoothly on the interpolation parameter, the derivative of `s ↦ 𝔼⟨Φ s⟩_s` is the
derivative of Lemma 1.4.2 for `Φ t` plus `𝔼⟨Φ' t⟩_t`. -/
theorem hasDerivAt_integral_replica_trig_moving
    (hXm : ∀ a, Measurable (X a)) (hYm : ∀ a, Measurable (Y a))
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (hX : ∀ a, ∫ ω, X a ω ∂P = 0) (hY : ∀ a, ∫ ω, Y a ω ∂P = 0)
    (h0 : ∀ a b, ∫ ω, X a ω * Y b ω ∂P = 0) (U : α → α → ℝ)
    (hU : ∀ a b, U a b = ∫ ω, Y a ω * Y b ω ∂P - ∫ ω, X a ω * X b ω ∂P) (h : α → ℝ)
    {Φ Φ' : ℝ → (R → α) → ℝ} {M M' : ℝ}
    (hΦ : ∀ s σ, HasDerivAt (fun s => Φ s σ) (Φ' s σ) s) (hM : ∀ s σ, |Φ s σ| ≤ M)
    (hM' : ∀ s σ, |Φ' s σ| ≤ M') (t : ℝ) :
    HasDerivAt (fun s => ∫ ω, ∫ σ, Φ s σ ∂(Measure.pi fun _ : R =>
        Measure.count.tilted fun a => Real.cos s * X a ω + Real.sin s * Y a ω + h a) ∂P)
      (Real.sin t * Real.cos t * ∫ ω, ∫ τ : Option (Option R) → α,
        Φ t (fun r => τ (some (some r))) *
          ((∑ r, ∑ r', U (τ (some (some r))) (τ (some (some r')))) -
            2 * Fintype.card R * ∑ r, U (τ (some (some r))) (τ (some none)) -
            Fintype.card R * U (τ (some none)) (τ (some none)) +
            Fintype.card R * (Fintype.card R + 1) * U (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option R) =>
          Measure.count.tilted fun a => Real.cos t * X a ω + Real.sin t * Y a ω + h a) ∂P +
        ∫ ω, ∫ σ, Φ' t σ ∂(Measure.pi fun _ : R =>
          Measure.count.tilted fun a => Real.cos t * X a ω + Real.sin t * Y a ω + h a) ∂P) t := by
  have := Fintype.ofFinite α
  classical
  have hP := hXY.isProbabilityMeasure
  have hXi : ∀ a, Integrable (X a) P := fun a => (hXY.eval (Sum.inl a)).integrable
  have hYi : ∀ a, Integrable (Y a) P := fun a => (hXY.eval (Sum.inr a)).integrable
  have hpath := hasDerivAt_integral_replica_path_moving (μ := P) (t := t) (S := Set.univ) (R := R)
    (Ψ := Φ) (Ψ' := Φ') (M := M) (M' := M') Filter.univ_mem (fun s _ σ => hΦ s σ)
    (fun s _ σ => hM s σ) (fun s _ σ => hM' s σ)
    (f := fun s ω a => Real.cos s * X a ω + Real.sin s * Y a ω + h a)
    (f' := fun s ω a => -Real.sin s * X a ω + Real.cos s * Y a ω)
    (fun s a => (((hXm a).const_mul _).add ((hYm a).const_mul _)).add_const _ |>.aemeasurable)
    (fun a => (((hXm a).const_mul _).add ((hYm a).const_mul _)).aemeasurable)
    (fun ω s _ a => hasDerivAt_cos_mul_add_sin_mul (X a ω) (Y a ω) (h a) s)
    (B := fun ω => ∑ a, (|X a ω| + |Y a ω|))
    (integrable_finsetSum _ fun a _ => (hXi a).abs.add (hYi a).abs)
    (fun ω s _ a => abs_neg_sin_mul_add_cos_mul_le_sum (fun b => X b ω) (fun b => Y b ω) s a)
  refine hpath.congr_deriv ?_
  have hint1 := integrable_replica_derivative_term (R := R) (P := P)
    (g := fun a ω => Real.cos t * X a ω + Real.sin t * Y a ω + h a)
    (χ := fun a ω => -Real.sin t * X a ω + Real.cos t * Y a ω)
    (fun a => (((hXm a).const_mul _).add ((hYm a).const_mul _)).add_const _ |>.aemeasurable)
    (fun a => (((hXm a).const_mul _).add ((hYm a).const_mul _)).aemeasurable)
    (B := fun ω => ∑ a, (|X a ω| + |Y a ω|))
    (integrable_finsetSum _ fun a _ => (hXi a).abs.add (hYi a).abs)
    (fun ω a => abs_neg_sin_mul_add_cos_mul_le_sum (fun b => X b ω) (fun b => Y b ω) t a)
    (Ψ := Φ t) (hM t)
  have hint2 := integrable_integral_pi_count_tilted_det (R := R) (P := P)
    (g := fun a ω => Real.cos t * X a ω + Real.sin t * Y a ω + h a)
    (fun a => (((hXm a).const_mul _).add ((hYm a).const_mul _)).add_const _ |>.aemeasurable)
    (Φ' t)
  rw [integral_add hint1 hint2, integral_replica_trig_key hXm hYm hXY hX hY h0 U hU h (hM t) t]

end Trig

end SpinGlasses
