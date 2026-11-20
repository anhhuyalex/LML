/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.WithDensity

/-!
# Equivariance of Gibbs replica averages under a measurable equivalence

* `map_tilted_equiv`: the pushforward of `μ.tilted e` under a `μ`-preserving measurable
  equivalence `ψ` is `μ.tilted (e ∘ ψ.symm)`;
* `replicaDiff_map_equiv`, `replicaPairAverage_map_equiv`: the replica difference and the
  two-fresh-replica average against `ν.map ψ` are those against `ν` of the observable (and kernel)
  precomposed with `ψ`.

Together they transport a replica average along a symmetry of the base measure (the permutation of
constraints in the exchangeable form of Talagrand's Proposition 2.2.3).
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

/-- **Tilting commutes with a measure-preserving equivalence.** -/
theorem map_tilted_equiv {α : Type*} [MeasurableSpace α] {μ : Measure α} (ψ : α ≃ᵐ α)
    (hψ : MeasurePreserving ψ μ μ) {e : α → ℝ} (he : Measurable e) :
    (μ.tilted e).map ψ = μ.tilted (e ∘ ψ.symm) := by
  have hψ' : MeasurePreserving ψ.symm μ μ := hψ.symm ψ
  have hZ : ∫ x, Real.exp ((e ∘ ψ.symm) x) ∂μ = ∫ x, Real.exp (e x) ∂μ :=
    hψ'.integral_comp_of_aestronglyMeasurable (g := fun x => Real.exp (e x))
      he.exp.aestronglyMeasurable
  unfold Measure.tilted
  rw [map_equiv_withDensity (by fun_prop), hψ.map_eq, hZ]
  rfl

/-- **The pair average is equivariant under a measurable equivalence of the base space.** -/
theorem replicaPairAverage_map_equiv {α R : Type*} [MeasurableSpace α] [Fintype R]
    [LinearOrder R] (ν : Measure α) [IsProbabilityMeasure ν] (ψ : α ≃ᵐ α) (F : (R → α) → ℝ)
    (U : α → α → ℝ) :
    replicaPairAverage (ν.map ψ) F U =
      replicaPairAverage ν (fun ρ => F (fun r => ψ (ρ r))) (fun a b => U (ψ a) (ψ b)) := by
  unfold replicaPairAverage
  rw [← Measure.pi_map_pi (μ := fun _ : Option (Option R) => ν) (f := fun _ => ψ)
    (fun _ => ψ.measurable.aemeasurable)]
  rw [show (fun (x : Option (Option R) → α) i => ψ (x i)) =
    ⇑(MeasurableEquiv.piCongrRight fun _ : Option (Option R) => ψ) from rfl, integral_map_equiv]
  rfl

/-- **The replica difference is equivariant under a measurable equivalence of the base space.** -/
theorem replicaDiff_map_equiv {α R : Type*} [MeasurableSpace α] [Fintype R]
    (ν : Measure α) [IsProbabilityMeasure ν] (ψ : α ≃ᵐ α) (F : (R → α) → ℝ) (h : α → ℝ) :
    replicaDiff (ν.map ψ) F h =
      replicaDiff ν (fun ρ => F (fun r => ψ (ρ r))) (fun a => h (ψ a)) := by
  have hmap (G : (Option R → α) → ℝ) :
      ∫ σ, G σ ∂(Measure.pi fun _ : Option R => ν.map ψ) =
        ∫ σ, G (fun i => ψ (σ i)) ∂(Measure.pi fun _ : Option R => ν) := by
    rw [← Measure.pi_map_pi (μ := fun _ : Option R => ν) (f := fun _ => ψ)
      (fun _ => ψ.measurable.aemeasurable)]
    rw [show (fun (x : Option R → α) i => ψ (x i)) =
      ⇑(MeasurableEquiv.piCongrRight fun _ : Option R => ψ) from rfl, integral_map_equiv]
    rfl
  rw [replicaDiff_eq, replicaDiff_eq]
  simp only [hmap]

end MeasureTheory
