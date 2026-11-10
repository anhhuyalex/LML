/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct

/-!
# Relabelling the sites of a replica Gibbs measure

Relabelling the sites of all replicas by a permutation `π` of the site set `M` moves the energy
by the same relabelling: the `R`-replica Gibbs average of `Θ ∘ (· ∘ π)` for the energy `E` is the
average of `Θ` for the energy `E ∘ (· ∘ π⁻¹)`.  This holds for an arbitrary spin law, with no
boundedness assumption.
-/

@[expose] public section

open MeasureTheory
namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- Permuting the sites of every replica preserves the product of the site laws. -/
theorem measurePreserving_replica_perm {R M : Type*} [Fintype R] [Fintype M] (μ : Measure α)
    [IsProbabilityMeasure μ] (π : Equiv.Perm M) :
    MeasurePreserving (MeasurableEquiv.arrowCongr' (Equiv.refl R)
      (MeasurableEquiv.arrowCongr' π (MeasurableEquiv.refl α)))
      (Measure.pi fun _ : R => Measure.pi fun _ : M => μ)
      (Measure.pi fun _ : R => Measure.pi fun _ : M => μ) :=
  measurePreserving_arrowCongr' (fun _ => Measure.pi fun _ : M => μ)
    (fun _ => Measure.pi fun _ : M => μ) (Equiv.refl R) _
    (fun _ => measurePreserving_arrowCongr' (fun _ => μ) (fun _ => μ) π _
      (fun _ => MeasurePreserving.id μ))

/-- **Site relabelling of a replica Gibbs average.**  Relabelling the sites of all `R` replicas by
`π` is the same as relabelling the energy by `π⁻¹`. -/
theorem integral_pi_tilted_comp_perm {R M : Type*} [Fintype R] [Fintype M] (μ : Measure α)
    [IsProbabilityMeasure μ] (π : Equiv.Perm M) (E : (M → α) → ℝ) (Θ : (R → M → α) → ℝ) :
    ∫ σ, Θ (fun r i => σ r (π i)) ∂(Measure.pi fun _ : R =>
        (Measure.pi fun _ : M => μ).tilted E) =
      ∫ σ, Θ σ ∂(Measure.pi fun _ : R => (Measure.pi fun _ : M => μ).tilted
        (fun a => E (fun i => a (π.symm i)))) := by
  have hF := fun G : (R → M → α) → ℝ =>
    (measurePreserving_replica_perm (R := R) μ π.symm).integral_comp' G
  have key : ∀ G : (R → M → α) → ℝ, ∫ σ : R → M → α, G (fun r i => σ r (π i)) ∂(Measure.pi
      fun _ : R => Measure.pi fun _ : M => μ) = ∫ τ, G τ ∂(Measure.pi
      fun _ : R => Measure.pi fun _ : M => μ) := fun G => by
    refine Eq.trans ?_ (hF G)
    rfl
  rw [integral_pi_tilted_eq_div, integral_pi_tilted_eq_div]
  congr 1
  · rw [← key fun τ => Θ τ * Real.exp (∑ r, E (fun i => τ r (π.symm i)))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    simp
  · rw [← key fun τ => Real.exp (∑ r, E (fun i => τ r (π.symm i)))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    simp

end MeasureTheory
