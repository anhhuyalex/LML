/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.FreeEnergy.Limit

/-!
# The ball model and the singular zero-spin model

The abstract spin space specializes directly to the radius-`sqrt d` ball from Section 1.12.
No separate spin-space type is needed. Zero coordinates give the singular fixed point `(0,0)`
and zero free energy at every temperature, for any underlying probability space.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Filter
open scoped BigOperators Topology

namespace SpinGlasses

/-- The book's ball model satisfies the same dimension-uniform high-temperature theorem.
The spin law is arbitrary, including point masses and laws supported on a proper subspace. -/
theorem existsUnique_skVectorFixedPoint_overlap_free_energy_ball (d : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (μ : Measure {a : Fin d → ℝ // ∑ u, a u ^ 2 ≤ (d : ℝ)})
        [IsProbabilityMeasure μ] (β : ℝ), 0 ≤ β → 15 * β * (d : ℝ) ≤ 1 →
        ∃! x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ),
          x ∈ skVectorFixedPointCone d ∧
          skVectorFixedPointMap μ (fun a => a.val) β x = x ∧
          (∀ N : ℕ,
            skVectorReplicaAverage μ (fun a => a.val) N β (fun σ => ∑ u, ∑ v,
              skVectorOverlapDeviation (fun a => a.val) N 0 1 x.1 u v σ ^ 2) +
            skVectorReplicaAverage μ (fun a => a.val) N β (fun σ => ∑ u, ∑ v,
              skVectorOverlapDeviation (fun a => a.val) N 0 0 x.2 u v σ ^ 2) ≤
                K / ((N : ℝ) + 1)) ∧
          (∀ N : ℕ,
            |skVectorFreeEnergy μ (fun a => a.val) (N + 1) β -
              skVectorPressure μ (fun a => a.val) β x| ≤ K / Real.sqrt ((N : ℝ) + 1)) ∧
          Tendsto (fun N : ℕ => skVectorFreeEnergy μ (fun a => a.val) N β) atTop
            (𝓝 (skVectorPressure μ (fun a => a.val) β x)) := by
  obtain ⟨K, hK, h⟩ := existsUnique_skVectorFixedPoint_overlap_free_energy d
  refine ⟨K, hK, ?_⟩
  intro μ _ β hβ hsmall
  exact h μ (fun a => a.val) (fun u => (measurable_pi_apply u).comp measurable_subtype_coe)
    (fun a => a.property) β hβ hsmall

/-- With identically zero spin coordinates the fixed-point map is identically zero,
including at singular covariance matrices and without a temperature restriction. -/
theorem skVectorFixedPointMap_zero_coordinates {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (d : ℕ) (β : ℝ)
    (x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)) :
    skVectorFixedPointMap μ (fun _ _ => 0) β x = 0 := by
  simp [skVectorFixedPointMap, skVectorFieldAverage]
  rfl

/-- The zero-spin model has the unique fixed point `(q,ρ)=(0,0)` at every temperature. -/
theorem existsUnique_skVectorFixedPoint_zero_coordinates {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (d : ℕ) (β : ℝ) :
    ∃! x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ),
      x ∈ skVectorFixedPointCone d ∧ skVectorFixedPointMap μ (fun _ _ => 0) β x = x := by
  refine ⟨0, ⟨?_, skVectorFixedPointMap_zero_coordinates μ d β 0⟩, ?_⟩
  · exact ⟨Matrix.PosSemidef.zero, by simpa using Matrix.PosSemidef.zero⟩
  · intro x hx
    exact hx.2.symm.trans (skVectorFixedPointMap_zero_coordinates μ d β x)

/-- Zero spin coordinates give partition function one and free energy zero for every size. -/
theorem skVectorFreeEnergy_zero_coordinates {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (d N : ℕ) (β : ℝ) :
    skVectorFreeEnergy μ (fun _ (_ : Fin d) => 0) N β = 0 := by
  simp [skVectorFreeEnergy, skVectorEnergy]

end SpinGlasses
