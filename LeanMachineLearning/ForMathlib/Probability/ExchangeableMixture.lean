/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.Probability.ProductMeasure

/-!
# Mixtures of i.i.d. sequences are exchangeable

If `ν ω` is a probability measure on `X` depending measurably on a parameter `ω`, then
`ω ↦ infinitePi (fun _ => ν ω)` is a measurable family of probability measures on `ι → X`
(`measurable_infinitePi_const`).  Each member is invariant under permutations of the coordinates
(`infinitePi_map_comp_equiv`), hence so is the mixture `P.bind (fun ω => infinitePi ...)`
(`bind_infinitePi_map_comp_equiv`): a mixture of i.i.d. sequences is exchangeable.

This is the easy half of de Finetti's theorem.  In spin glasses `ν ω` is the Gibbs measure of the
random Hamiltonian `H(ω)`, the sequence is the sequence of replicas, and the mixture is the
annealed law `𝔼 G^{⊗∞}`.

## Main declarations

* `MeasureTheory.Measure.measurable_pi_const`, `measurable_infinitePi_const`: measurability of
  the family of product measures in the parameter.
* `MeasureTheory.Measure.infinitePi_map_comp_equiv`: `infinitePi` of a constant family is
  invariant under `σ ↦ σ ∘ e`, `e : ι ≃ ι`.
* `MeasureTheory.Measure.map_bind_eq_self`: a mixture of `T`-invariant measures is `T`-invariant.
* `MeasureTheory.Measure.bind_infinitePi_map_comp_equiv`: exchangeability of the mixture.
-/

@[expose] public section

open Set

namespace MeasureTheory.Measure

variable {ι Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]

/-- The finite product of a measurable family of probability measures is measurable in the
parameter. -/
theorem measurable_pi_const [Fintype ι] {ν : Ω → Measure X} [∀ ω, IsProbabilityMeasure (ν ω)]
    (hν : Measurable ν) : Measurable fun ω => Measure.pi fun _ : ι => ν ω := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_pi.symm
    isPiSystem_pi ?_
  rintro _ ⟨t, ht, rfl⟩
  simp_rw [Measure.pi_pi]
  exact Finset.measurable_prod _ fun i _ => (measurable_coe (ht i (mem_univ i))).comp hν

/-- The infinite product of a measurable family of probability measures is measurable in the
parameter. -/
theorem measurable_infinitePi_const {ν : Ω → Measure X} [∀ ω, IsProbabilityMeasure (ν ω)]
    (hν : Measurable ν) : Measurable fun ω => Measure.infinitePi fun _ : ι => ν ω := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_
  intro A hA
  obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders _).1 hA
  have h : ∀ ω, Measure.infinitePi (fun _ : ι => ν ω) (cylinder s S) =
      Measure.pi (fun _ : s => ν ω) S := fun ω =>
    infinitePi_cylinder (X := fun _ : ι => X) (fun _ => ν ω) hS
  simp_rw [h]
  exact (measurable_coe hS).comp (measurable_pi_const hν)

/-- An i.i.d. sequence is invariant in law under any permutation of the indices. -/
theorem infinitePi_map_comp_equiv (ν : Measure X) [IsProbabilityMeasure ν] (e : ι ≃ ι) :
    (Measure.infinitePi fun _ : ι => ν).map (fun σ => σ ∘ e) = Measure.infinitePi fun _ => ν := by
  have h := infinitePi_map_piCongrLeft (X := fun _ : ι => X) (fun _ => ν) e.symm
  convert h using 2
  ext σ i
  rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  simp

/-- A mixture of measures that are invariant under a measurable map `T` is invariant under `T`. -/
theorem map_bind_eq_self {A : Type*} [MeasurableSpace A] {P : Measure Ω} {κ : Ω → Measure A}
    (hκ : Measurable κ) {T : A → A} (hT : Measurable T) (h : ∀ ω, (κ ω).map T = κ ω) :
    (P.bind κ).map T = P.bind κ := by
  ext s hs
  rw [Measure.map_apply hT hs, Measure.bind_apply (hT hs) hκ.aemeasurable,
    Measure.bind_apply hs hκ.aemeasurable]
  refine MeasureTheory.lintegral_congr fun ω => ?_
  rw [← Measure.map_apply hT hs, h]

/-- **A mixture of i.i.d. sequences is exchangeable:** if `ν : Ω → Measure X` is a measurable
family of probability measures and `P` a measure on `Ω`, the law `P.bind (ω ↦ ν ω ^ ⊗ι)` of the
sequence is invariant under every permutation `σ ↦ σ ∘ e` of the indices. -/
theorem bind_infinitePi_map_comp_equiv {P : Measure Ω} {ν : Ω → Measure X}
    [∀ ω, IsProbabilityMeasure (ν ω)] (hν : Measurable ν) (e : ι ≃ ι) :
    (P.bind fun ω => Measure.infinitePi fun _ : ι => ν ω).map (fun σ => σ ∘ e) =
      P.bind fun ω => Measure.infinitePi fun _ : ι => ν ω :=
  map_bind_eq_self (measurable_infinitePi_const hν)
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _)
    fun ω => infinitePi_map_comp_equiv (ν ω) e

end MeasureTheory.Measure
