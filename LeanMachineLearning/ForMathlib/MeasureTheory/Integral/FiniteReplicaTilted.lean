/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FiniteTilted

/-!
# Finite replica averages of a random tilted counting measure

Measurability, bounded Lp membership and finite-sum linearity for parameter-dependent
finite Gibbs expectations. Neither the energy nor the observable is required to
be Gaussian. Replica types may be empty. No model-specific definition is introduced.
-/

@[expose] public section

open Finset
open scoped ENNReal

namespace MeasureTheory

variable {α R : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **Replica average as an explicit sum:** under the `R`-fold product of the Gibbs measure
`count.tilted f`, `∫ Ψ = ∑_σ (∏_r exp (f (σ r)) / Z) Ψ(σ)`. -/
theorem integral_pi_count_tilted [Fintype α] [Fintype R] [DecidableEq R] (f : α → ℝ)
    (Ψ : (R → α) → ℝ) :
    ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted f) =
      ∑ σ : R → α, (∏ r, Real.exp (f (σ r)) / ∑ b, Real.exp (f b)) * Ψ σ := by
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Measure.real, Measure.pi_singleton, ENNReal.toReal_prod, smul_eq_mul]
  congr 1
  exact Finset.prod_congr rfl fun r _ => real_count_tilted_singleton f (σ r)

section Parameter

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

end Parameter

/-- An `L^p` envelope for a random finite Gibbs observable also dominates its replica
average. The disorder measure need not be finite and the envelope need not be constant. -/
theorem memLp_integral_pi_count_tilted_of_dominated {Ω α R : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [Finite α] [Nonempty α] [Fintype R]
    [MeasurableSpace α] [MeasurableSingletonClass α] {p : ℝ≥0∞}
    (f : Ω → α → ℝ) (hf : ∀ a, AEMeasurable (fun ω => f ω a) μ)
    (Φ : Ω → (R → α) → ℝ) (hΦ : ∀ σ, AEMeasurable (fun ω => Φ ω σ) μ)
    {B : Ω → ℝ} (hB : MemLp B p μ) (hbound : ∀ᵐ ω ∂μ, ∀ σ, |Φ ω σ| ≤ B ω) :
    MemLp (fun ω => ∫ σ, Φ ω σ
      ∂(Measure.pi fun _ : R => Measure.count.tilted (f ω))) p μ := by
  refine hB.mono' (aemeasurable_integral_pi_count_tilted hf hΦ).aestronglyMeasurable ?_
  filter_upwards [hbound] with ω hω
  have hi := norm_integral_le_of_norm_le_const
    (μ := Measure.pi fun _ : R => Measure.count.tilted (f ω)) (C := B ω)
    (f := Φ ω) (ae_of_all _ fun σ => by rw [Real.norm_eq_abs]; exact hω σ)
  simpa only [probReal_univ, mul_one] using hi

/-- A bounded random finite Gibbs observable has a replica average in every `L^p`
for a finite disorder measure. Energies and observables need only be a.e. measurable. -/
theorem memLp_integral_pi_count_tilted_of_bound {Ω α R : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] [Finite α] [Nonempty α] [Fintype R]
    [MeasurableSpace α] [MeasurableSingletonClass α] (p : ℝ≥0∞)
    (f : Ω → α → ℝ) (hf : ∀ a, AEMeasurable (fun ω => f ω a) μ)
    (Φ : Ω → (R → α) → ℝ) (hΦ : ∀ σ, AEMeasurable (fun ω => Φ ω σ) μ)
    (M : ℝ) (hM : ∀ᵐ ω ∂μ, ∀ σ, |Φ ω σ| ≤ M) :
    MemLp (fun ω => ∫ σ, Φ ω σ
      ∂(Measure.pi fun _ : R => Measure.count.tilted (f ω))) p μ :=
  memLp_integral_pi_count_tilted_of_dominated f hf Φ hΦ (memLp_const M) hM

/-- **A bounded replica average is integrable in the disorder.** If the energies and the
observable are measurable in the disorder `ω` and the observable is bounded, then
`ω ↦ ∫ Φ ω d(count.tilted (f ω))^{⊗R}` is integrable for a finite measure. -/
theorem integrable_integral_pi_count_tilted_of_bound {Ω α R : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] [Finite α] [Nonempty α] [Fintype R]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (f : Ω → α → ℝ) (hf : ∀ a, Measurable fun ω => f ω a)
    (Φ : Ω → (R → α) → ℝ) (hΦ : ∀ σ, Measurable fun ω => Φ ω σ) (M : ℝ)
    (hM : ∀ ω σ, |Φ ω σ| ≤ M) :
    Integrable (fun ω => ∫ σ, Φ ω σ ∂(Measure.pi fun _ : R => Measure.count.tilted (f ω))) μ := by
  exact (memLp_integral_pi_count_tilted_of_bound 1 f (fun a => (hf a).aemeasurable)
    Φ (fun σ => (hΦ σ).aemeasurable) M (ae_of_all _ hM)).integrable le_rfl

/-- **A finite sum of bounded replica averages can be integrated termwise in the disorder.** -/
theorem integral_integral_pi_count_tilted_finset_sum {Ω α R ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] [Finite α] [Nonempty α] [Fintype R]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (f : Ω → α → ℝ) (hf : ∀ a, Measurable fun ω => f ω a) (t : Finset ι)
    (Φ : ι → Ω → (R → α) → ℝ) (hΦ : ∀ i σ, Measurable fun ω => Φ i ω σ) (M : ℝ)
    (hM : ∀ i ω σ, |Φ i ω σ| ≤ M) :
    ∫ ω, ∫ σ, ∑ i ∈ t, Φ i ω σ ∂(Measure.pi fun _ : R => Measure.count.tilted (f ω)) ∂μ =
      ∑ i ∈ t, ∫ ω, ∫ σ, Φ i ω σ ∂(Measure.pi fun _ : R => Measure.count.tilted (f ω)) ∂μ := by
  have hint : ∀ ω, ∀ i ∈ t, Integrable (fun σ => Φ i ω σ)
      (Measure.pi fun _ : R => Measure.count.tilted (f ω)) := fun ω i _ => Integrable.of_finite
  simp_rw [integral_finsetSum t (hint _)]
  exact integral_finsetSum t fun i _ =>
    integrable_integral_pi_count_tilted_of_bound f hf (Φ i) (hΦ i) M (hM i)

/-- **Additivity of the bounded replica average in the disorder.** -/
theorem integral_integral_pi_count_tilted_add {Ω α R : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] [Finite α] [Nonempty α] [Fintype R]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (f : Ω → α → ℝ) (hf : ∀ a, Measurable fun ω => f ω a) (Φ Ψ : Ω → (R → α) → ℝ)
    (hΦ : ∀ σ, Measurable fun ω => Φ ω σ) (hΨ : ∀ σ, Measurable fun ω => Ψ ω σ)
    (M : ℝ) (hMΦ : ∀ ω σ, |Φ ω σ| ≤ M) (hMΨ : ∀ ω σ, |Ψ ω σ| ≤ M) :
    ∫ ω, ∫ σ, (Φ ω σ + Ψ ω σ) ∂(Measure.pi fun _ : R => Measure.count.tilted (f ω)) ∂μ =
      (∫ ω, ∫ σ, Φ ω σ ∂(Measure.pi fun _ : R => Measure.count.tilted (f ω)) ∂μ) +
      ∫ ω, ∫ σ, Ψ ω σ ∂(Measure.pi fun _ : R => Measure.count.tilted (f ω)) ∂μ := by
  simp_rw [integral_add (Integrable.of_finite (f := fun σ => Φ _ σ)) Integrable.of_finite]
  exact integral_add (integrable_integral_pi_count_tilted_of_bound f hf Φ hΦ M hMΦ)
    (integrable_integral_pi_count_tilted_of_bound f hf Ψ hΨ M hMΨ)

end MeasureTheory
