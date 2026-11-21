/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct

/-!
# Comparison of replica Gibbs averages for bounded energy perturbations

If two energies differ by at most `C` pointwise, the `ι`-replica Gibbs average of a nonnegative
observable under the second is at most `exp (2 |ι| C)` times that under the first. In Talagrand's
cavity in `M` (Section 2.3, Lemma 2.3.4) the perturbation is the new constraint's contribution,
bounded by `2 D` by (2.7), which gives (2.61).

* `MeasureTheory.integral_pi_tilted_le_exp_mul_of_abs_sub_le`.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] {μ : Measure α} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
/-- **Comparison of replica Gibbs averages.** If `|E₁ - E₀| ≤ C` pointwise then, for a nonnegative
`Y` integrable under the `E₀`-replica Gibbs law,
`∫ Y d(μ.tilted E₁)^{⊗ι} ≤ exp (2 |ι| C) ∫ Y d(μ.tilted E₀)^{⊗ι}`. -/
theorem integral_pi_tilted_le_exp_mul_of_abs_sub_le [NeZero μ] {E₀ E₁ : α → ℝ}
    (h0 : Integrable (fun a => Real.exp (E₀ a)) μ) (hm : Measurable fun a => E₁ a - E₀ a)
    {C : ℝ} (hC : ∀ a, |E₁ a - E₀ a| ≤ C) {Y : (ι → α) → ℝ} (hY0 : ∀ σ, 0 ≤ Y σ)
    (hY : Integrable Y (Measure.pi fun _ : ι => μ.tilted E₀)) :
    ∫ σ, Y σ ∂(Measure.pi fun _ : ι => μ.tilted E₁) ≤
      Real.exp (2 * Fintype.card ι * C) * ∫ σ, Y σ ∂(Measure.pi fun _ : ι => μ.tilted E₀) := by
  have : IsProbabilityMeasure (μ.tilted E₀) := isProbabilityMeasure_tilted h0
  have h1 : μ.tilted E₁ = (μ.tilted E₀).tilted fun a => E₁ a - E₀ a := by
    rw [tilted_tilted h0]
    congr 1
    funext a
    simp
  rw [h1, pi_tilted_eq_tilted_pi]
  set ν : Measure (ι → α) := Measure.pi fun _ : ι => μ.tilted E₀ with hν
  have hν1 : ν.real Set.univ = 1 := by simp [hν]
  have hem : Measurable fun σ : ι → α => ∑ i, (E₁ (σ i) - E₀ (σ i)) :=
    Finset.measurable_sum _ fun i _ => hm.comp (measurable_pi_apply i)
  have hbound : ∀ σ : ι → α, |∑ i, (E₁ (σ i) - E₀ (σ i))| ≤ Fintype.card ι * C := fun σ =>
    (Finset.abs_sum_le_sum_abs _ _).trans <| by
      calc ∑ i, |E₁ (σ i) - E₀ (σ i)| ≤ ∑ _i : ι, C := Finset.sum_le_sum fun i _ => hC _
        _ = Fintype.card ι * C := by simp
  have := abs_integral_tilted_le_exp_mul_integral_abs (μ := ν)
    (e := fun σ : ι → α => ∑ i, (E₁ (σ i) - E₀ (σ i))) (Y := Y) hem.aemeasurable
    (ae_of_all _ hbound) hY
  rw [hν1, div_one] at this
  calc ∫ σ, Y σ ∂ν.tilted (fun σ : ι → α => ∑ i, (E₁ (σ i) - E₀ (σ i)))
      ≤ |∫ σ, Y σ ∂ν.tilted (fun σ : ι → α => ∑ i, (E₁ (σ i) - E₀ (σ i)))| := le_abs_self _
    _ ≤ Real.exp (2 * (Fintype.card ι * C)) * ∫ σ, |Y σ| ∂ν := this
    _ = Real.exp (2 * Fintype.card ι * C) * ∫ σ, Y σ ∂ν := by
        rw [← mul_assoc, integral_congr_ae (ae_of_all _ fun σ => abs_of_nonneg (hY0 σ))]

section Environment

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Comparison of disorder-averaged replica Gibbs averages.** For jointly measurable random
energies `E₀, E₁` on a probability space of environments, bounded above and with
`|E₁ - E₀| ≤ C`, and a jointly measurable observable `0 ≤ G ≤ M` (which may depend on the
environment), the disorder average of the `ι`-replica Gibbs average under `E₁` is at most
`exp (2 |ι| C)` times that under `E₀`. -/
theorem integral_integral_pi_tilted_le_exp_mul_of_abs_sub_le [NeZero μ] {E₀ E₁ : Ω → α → ℝ}
    (hE₀ : Measurable fun p : Ω × α => E₀ p.1 p.2) (hE₁ : Measurable fun p : Ω × α => E₁ p.1 p.2)
    {B : Ω → ℝ} (hB₀ : ∀ ω a, E₀ ω a ≤ B ω) (hB₁ : ∀ ω a, E₁ ω a ≤ B ω) {C : ℝ}
    (hC : ∀ ω a, |E₁ ω a - E₀ ω a| ≤ C) {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → (ι → α) → ℝ} (hG : Measurable fun p : Ω × (ι → α) => G p.1 p.2)
    {M : ℝ} (hG0 : ∀ ω σ, 0 ≤ G ω σ) (hGb : ∀ ω σ, G ω σ ≤ M) :
    ∫ ω, ∫ σ, G ω σ ∂(Measure.pi fun _ : ι => μ.tilted (E₁ ω)) ∂P ≤
      Real.exp (2 * Fintype.card ι * C) *
        ∫ ω, ∫ σ, G ω σ ∂(Measure.pi fun _ : ι => μ.tilted (E₀ ω)) ∂P := by
  have hint : ∀ ω (E : Ω → α → ℝ), (∀ a, E ω a ≤ B ω) → (Measurable fun p : Ω × α => E p.1 p.2) →
      Integrable (fun a => Real.exp (E ω a)) μ := fun ω E hB hE =>
    integrable_exp_of_ae_le (C := B ω)
      (hE.comp (measurable_const.prodMk measurable_id)).aemeasurable (ae_of_all _ hB)
  have hprob : ∀ (E : Ω → α → ℝ), (∀ ω a, E ω a ≤ B ω) →
      (Measurable fun p : Ω × α => E p.1 p.2) →
      ∀ ω, IsProbabilityMeasure (μ.tilted (E ω)) := fun E hB hE ω =>
    isProbabilityMeasure_tilted (hint ω E (hB ω) hE)
  have hM : ∀ ω σ, |G ω σ| ≤ M := fun ω σ => by
    rw [abs_of_nonneg (hG0 ω σ)]; exact hGb ω σ
  have i₀ := integrable_integral_pi_tilted (μ := μ) (ι := ι) hE₀ (hprob E₀ hB₀ hE₀) (P := P) hG hM
  have i₁ := integrable_integral_pi_tilted (μ := μ) (ι := ι) hE₁ (hprob E₁ hB₁ hE₁) (P := P) hG hM
  rw [← integral_const_mul]
  refine integral_mono i₁ (i₀.const_mul _) fun ω => ?_
  have hm : Measurable fun a => E₁ ω a - E₀ ω a :=
    ((hE₁.comp (measurable_const.prodMk measurable_id)).sub
      (hE₀.comp (measurable_const.prodMk measurable_id)))
  have h0 := hint ω E₀ (hB₀ ω) hE₀
  have : IsProbabilityMeasure (μ.tilted (E₀ ω)) := hprob E₀ hB₀ hE₀ ω
  exact integral_pi_tilted_le_exp_mul_of_abs_sub_le h0 hm (hC ω) (hG0 ω)
    (Integrable.of_bound (C := M)
      (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (ae_of_all _ fun σ => by simpa using hM ω σ))

end Environment

end MeasureTheory
