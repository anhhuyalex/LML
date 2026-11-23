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

* `map_tilted_measurableEquiv`: the pushforward of `μ.tilted e` under a `μ`-preserving measurable
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

/-- **Tilting commutes with a measure-preserving equivalence between arbitrary measurable
spaces.** With `β = α` and `ν = μ` this is the symmetry statement used for exchangeability. -/
theorem map_tilted_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} (ψ : α ≃ᵐ β) (hψ : MeasurePreserving ⇑ψ μ ν)
    {e : α → ℝ} (he : Measurable e) :
    (μ.tilted e).map ψ = ν.tilted (e ∘ ψ.symm) := by
  have hψ' : MeasurePreserving ⇑ψ.symm ν μ := hψ.symm ψ
  have hZ : ∫ y, Real.exp ((e ∘ ψ.symm) y) ∂ν = ∫ x, Real.exp (e x) ∂μ :=
    hψ'.integral_comp_of_aestronglyMeasurable (g := fun x => Real.exp (e x))
      he.exp.aestronglyMeasurable
  unfold Measure.tilted
  rw [map_equiv_withDensity (by fun_prop), hψ.map_eq, hZ]
  rfl

/-- **Change of variables for a finite product measure.** Integrating against the product of
`ν.map ψ` is integrating the coordinatewise `ψ`-image against the product of `ν`; the target type
may differ from the source. -/
theorem integral_pi_map_equiv {ι α β : Type*} [Fintype ι] [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure α) [IsFiniteMeasure ν] (ψ : α ≃ᵐ β) (G : (ι → β) → ℝ) :
    ∫ σ, G σ ∂(Measure.pi fun _ : ι => ν.map ψ) =
      ∫ σ, G (fun i => ψ (σ i)) ∂(Measure.pi fun _ => ν) := by
  rw [← Measure.pi_map_pi (μ := fun _ : ι => ν) (f := fun _ => ψ)
    (fun _ => ψ.measurable.aemeasurable)]
  exact integral_map_equiv (MeasurableEquiv.piCongrRight fun _ : ι => ψ) G

/-- **The pair average is equivariant under a measurable equivalence of the base space.** -/
theorem replicaPairAverage_map_equiv {α R : Type*} [MeasurableSpace α] [Fintype R]
    [LinearOrder R] (ν : Measure α) [IsProbabilityMeasure ν] (ψ : α ≃ᵐ α) (F : (R → α) → ℝ)
    (U : α → α → ℝ) :
    replicaPairAverage (ν.map ψ) F U =
      replicaPairAverage ν (fun ρ => F (fun r => ψ (ρ r))) (fun a b => U (ψ a) (ψ b)) :=
  integral_pi_map_equiv ν ψ _

/-- **The replica difference is equivariant under a measurable equivalence of the base space.** -/
theorem replicaDiff_map_equiv {α R : Type*} [MeasurableSpace α] [Fintype R]
    (ν : Measure α) [IsProbabilityMeasure ν] (ψ : α ≃ᵐ α) (F : (R → α) → ℝ) (h : α → ℝ) :
    replicaDiff (ν.map ψ) F h =
      replicaDiff ν (fun ρ => F (fun r => ψ (ρ r))) (fun a => h (ψ a)) := by
  rw [replicaDiff_eq, replicaDiff_eq]
  simp only [integral_pi_map_equiv ν ψ]

end MeasureTheory
