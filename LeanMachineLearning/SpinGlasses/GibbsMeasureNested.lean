/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GibbsMeasure
public import LeanMachineLearning.SpinGlasses.GaussianInterpolationReplica
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IteratedBound

/-!
# Nested two-replica Gibbs averages

For a random energy `E η ω` depending on two independent sources of disorder, the three-level
average `∫ η, ∫ ω, ∫ p, Θ p.1 p.2 ∂(tilted (E η ω) ⊗ tilted (E η ω))` of a deterministic
two-replica observable is monotone and affine in `Θ`.  These are the finite-measure
bookkeeping steps used by every interpolation estimate that compares two such averages.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

section Nested

variable {Ω₀ Ω α : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω] [Fintype α] [Nonempty α]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀] (P : Measure Ω) [IsProbabilityMeasure P]
  (E : Ω₀ → Ω → α → ℝ) (hE : ∀ a, Measurable (fun x : Ω₀ × Ω => E x.1 x.2 a))

include hE in
/-- Integrability of the inner levels of a nested two-replica average of a deterministic
observable. -/
theorem integrable_nested_prod_gibbs (Θ : α → α → ℝ) :
    (∀ η, Integrable (fun ω => ∫ p : α × α, Θ p.1 p.2
      ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω)))) P) ∧
    Integrable (fun η => ∫ ω, ∫ p : α × α, Θ p.1 p.2
      ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω))) ∂P) P₀ := by
  refine ⟨fun η => integrable_integral_prod_count_tilted_det (P := P)
    (A := fun ω a => E η ω a) (fun a => (hE a).comp measurable_prodMk_left) Θ, ?_⟩
  exact (integrable_integral_prod_count_tilted_det (P := P₀.prod P)
    (A := fun (x : Ω₀ × Ω) a => E x.1 x.2 a) hE Θ).integral_prod_left

include hE in
/-- **Domination of a nested two-replica average.** -/
theorem abs_integral_nested_prod_gibbs_le {G H : α → α → ℝ} (hGH : ∀ a b, |G a b| ≤ H a b) :
    |∫ η, ∫ ω, ∫ p : α × α, G p.1 p.2
        ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω))) ∂P ∂P₀| ≤
      ∫ η, ∫ ω, ∫ p : α × α, H p.1 p.2
        ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω))) ∂P ∂P₀ := by
  obtain ⟨h2, h3⟩ := integrable_nested_prod_gibbs P₀ P E hE H
  exact abs_integral_integral_integral_le P₀ P
    (fun η ω => (Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω)))
    (G := fun _ _ p => G p.1 p.2) (H := fun _ _ p => H p.1 p.2) (fun _ _ p => hGH p.1 p.2)
    (fun _ _ => Integrable.of_finite) h2 h3

include hE in
/-- **Affine maps pass through a nested two-replica average.** -/
theorem integral_nested_prod_gibbs_affine (f : α → α → ℝ) (c₁ c₂ : ℝ) :
    ∫ η, ∫ ω, ∫ p : α × α, (c₁ * f p.1 p.2 + c₂)
        ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω))) ∂P ∂P₀ =
      c₁ * (∫ η, ∫ ω, ∫ p : α × α, f p.1 p.2
        ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω))) ∂P ∂P₀) + c₂ := by
  obtain ⟨h2, h3⟩ := integrable_nested_prod_gibbs P₀ P E hE f
  have e1 (η : Ω₀) (ω : Ω) : (∫ p : α × α, (c₁ * f p.1 p.2 + c₂)
        ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω)))) =
      c₁ * (∫ p : α × α, f p.1 p.2
        ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω)))) + c₂ := by
    rw [integral_add (Integrable.of_finite.const_mul c₁) (integrable_const c₂),
      integral_const_mul, integral_const, probReal_univ, one_smul]
  have e2 (η : Ω₀) : (∫ ω, (c₁ * (∫ p : α × α, f p.1 p.2
        ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω)))) + c₂) ∂P) =
      c₁ * (∫ ω, ∫ p : α × α, f p.1 p.2
        ∂((Measure.count.tilted (E η ω)).prod (Measure.count.tilted (E η ω))) ∂P) + c₂ := by
    rw [integral_add ((h2 η).const_mul c₁) (integrable_const c₂), integral_const_mul,
      integral_const, probReal_univ, one_smul]
  simp_rw [e1, e2]
  rw [integral_add (h3.const_mul c₁) (integrable_const c₂), integral_const_mul, integral_const,
    probReal_univ, one_smul]

end Nested

end SpinGlasses
