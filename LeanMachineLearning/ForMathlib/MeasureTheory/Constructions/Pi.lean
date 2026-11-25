/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Count

/-! # Regrouping products and triples of coordinates -/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

/-- A finite product of counting measures is the counting measure on the product space. -/
theorem Measure.pi_count {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    [∀ i, Countable (X i)] :
    Measure.pi (fun i => (Measure.count : Measure (X i))) = Measure.count := by
  apply Measure.ext_of_singleton
  intro x
  simp [Measure.pi_singleton]

/-- **Coordinate marginal of a product law:** if `z` has the product law `Measure.pi μ`, then its
`i`-th coordinate has law `μ i`. -/
theorem Measure.map_apply_eq_of_map_eq_pi {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {X : ι → Type*} [∀ i, MeasurableSpace (X i)] {P : Measure Ω} {μ : ∀ i, Measure (X i)}
    [∀ i, IsProbabilityMeasure (μ i)] {z : Ω → ∀ i, X i} (hz : Measurable z)
    (hl : P.map z = Measure.pi μ) (i : ι) : P.map (fun ω => z ω i) = μ i := by
  rw [show (fun ω => z ω i) = (fun x : ∀ i, X i => x i) ∘ z from rfl,
    ← Measure.map_map (measurable_pi_apply i) hz, hl]
  exact (measurePreserving_eval μ i).map_eq

/-- A triple of coordinates of an i.i.d. vector `Fin 3 → α` is a product measure. -/
theorem measurePreserving_finThreeArrow {α : Type*} {m : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] :
    MeasurePreserving (fun y : Fin 3 → α => (y 0, y 1, y 2)) (Measure.pi fun _ => μ)
      (μ.prod (μ.prod μ)) := by
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => μ) 0
  have h2 := (MeasurePreserving.id μ).prod (measurePreserving_finTwoArrow μ)
  exact h2.comp h1

/-- Regrouping `((w, u), (v, x)) ↦ ((w, (u, v)), x)` preserves product measures. -/
theorem measurePreserving_prod_regroup {W U V X : Type*} {mW : MeasurableSpace W}
    {mU : MeasurableSpace U} {mV : MeasurableSpace V} {mX : MeasurableSpace X} (μW : Measure W)
    (μU : Measure U) (μV : Measure V) (μX : Measure X) [SFinite μW] [SFinite μU] [SFinite μV]
    [SFinite μX] :
    MeasurePreserving (fun p : (W × U) × (V × X) => ((p.1.1, (p.1.2, p.2.1)), p.2.2))
      ((μW.prod μU).prod (μV.prod μX)) ((μW.prod (μU.prod μV)).prod μX) := by
  have h1 := measurePreserving_prodAssoc μW μU (μV.prod μX)
  have h2 := (MeasurePreserving.id μW).prod
    (measurePreserving_prodAssoc μU μV μX).symm
  have h3 := (measurePreserving_prodAssoc μW (μU.prod μV) μX).symm
  exact h3.comp (h2.comp h1)

/-- Interchanging the middle factors `((a, b), (c, d)) ↦ ((a, c), (b, d))` preserves product
measures. -/
theorem measurePreserving_prodProdProdComm {A B C D : Type*} {mA : MeasurableSpace A}
    {mB : MeasurableSpace B} {mC : MeasurableSpace C} {mD : MeasurableSpace D}
    (μA : Measure A) (μB : Measure B) (μC : Measure C) (μD : Measure D)
    [SFinite μA] [SFinite μB] [SFinite μC] [SFinite μD] :
    MeasurePreserving (fun p : (A × B) × (C × D) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((μA.prod μB).prod (μC.prod μD)) ((μA.prod μC).prod (μB.prod μD)) := by
  have h1 := measurePreserving_prodAssoc μA μB (μC.prod μD)
  have h2 := (MeasurePreserving.id μA).prod ((measurePreserving_prodAssoc μB μC μD).symm)
  have h3 := (MeasurePreserving.id μA).prod
    ((Measure.measurePreserving_swap (μ := μB) (ν := μC)).prod (MeasurePreserving.id μD))
  have h4 := (MeasurePreserving.id μA).prod (measurePreserving_prodAssoc μC μB μD)
  have h5 := (measurePreserving_prodAssoc μA μC (μB.prod μD)).symm
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

/-- Uncurrying preserves product measures on finite index types: the iterated product of a
family `μ i k` is the product over index pairs. Taking `μ i k = ν` gives the i.i.d. statement. -/
theorem measurePreserving_curry_symm {ι κ X : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace X]
    (μ : ι → κ → Measure X) [∀ i k, SigmaFinite (μ i k)] :
    MeasurePreserving ⇑(MeasurableEquiv.curry ι κ X).symm
      (Measure.pi fun i : ι => Measure.pi (μ i))
      (Measure.pi fun x : ι × κ => μ x.1 x.2) := by
  refine ⟨(MeasurableEquiv.curry ι κ X).symm.measurable, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (MeasurableEquiv.curry ι κ X).symm.measurable (MeasurableSet.univ_pi hs)]
  have hpre : ⇑(MeasurableEquiv.curry ι κ X).symm ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun i : ι => Set.univ.pi fun k : κ => s (i, k)) := by
    ext W
    simp [Set.mem_pi]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/-- **Fubini for two i.i.d. coordinates:** an integrable function of the two coordinates of a point
of `Fin 2 → α` integrates against the product measure as an iterated integral. -/
theorem integral_pi_fin_two_of_integrable {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] {g : α → α → ℝ} (hg : Integrable (fun p : α × α => g p.1 p.2) (μ.prod μ)) :
    ∫ σ, g (σ 0) (σ 1) ∂(Measure.pi fun _ : Fin 2 => μ) = ∫ x, ∫ y, g x y ∂μ ∂μ := by
  have hmp := measurePreserving_piFinTwo (fun _ : Fin 2 => μ)
  have := hmp.integral_comp' (g := fun p : α × α => g p.1 p.2)
  simp only [MeasurableEquiv.piFinTwo_apply] at this
  rw [this]
  exact integral_prod (fun p : α × α => g p.1 p.2) hg

/-- **Fubini for two replicas:** a function of the two coordinates of a point of `Fin 2 → α`
integrates against the product measure as an iterated integral. -/
theorem integral_pi_fin_two {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Finite α] (μ : Measure α) [IsFiniteMeasure μ] (g : α → α → ℝ) :
    ∫ σ, g (σ 0) (σ 1) ∂(Measure.pi fun _ : Fin 2 => μ) = ∫ x, ∫ y, g x y ∂μ ∂μ :=
  integral_pi_fin_two_of_integrable μ Integrable.of_finite

/-- **Marginal of an i.i.d. vector along an injection of the index set:** restricting a vector
with the i.i.d. law `μ` indexed by `R'` to the coordinates `ρ r` (`ρ` injective) gives the i.i.d.
law indexed by `R`. -/
theorem measurePreserving_pi_comp_injective {R R' X : Type*} [Fintype R] [Fintype R']
    [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] {ρ : R → R'}
    (hρ : Function.Injective ρ) :
    MeasurePreserving (fun (τ : R' → X) (r : R) => τ (ρ r)) (Measure.pi fun _ : R' => μ)
      (Measure.pi fun _ : R => μ) := by
  classical
  refine ⟨by fun_prop, ?_⟩
  refine (Measure.pi_eq (μ := fun _ : R => μ)
    (μ' := Measure.map _ (Measure.pi fun _ : R' => μ)) fun s hs => ?_).symm
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have hpre : (fun (τ : R' → X) (r : R) => τ (ρ r)) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (Function.extend ρ s (fun _ => Set.univ)) := by
    ext τ
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h r'
      by_cases hr : ∃ r, ρ r = r'
      · obtain ⟨r, rfl⟩ := hr
        rw [hρ.extend_apply]
        exact h r
      · rw [Function.extend_apply' _ _ _ hr]
        trivial
    · intro h r
      have := h (ρ r)
      rwa [hρ.extend_apply] at this
  rw [hpre, Measure.pi_pi]
  have hone : ∀ r' ∉ Finset.univ.image ρ,
      μ (Function.extend ρ s (fun _ => Set.univ) r') = 1 := by
    intro r' hr
    rw [Function.extend_apply' _ _ _ (by simpa using hr)]
    simp
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.image ρ)) (fun x _ hx => hone x hx),
    Finset.prod_image (fun a _ b _ h => hρ h)]
  simp [hρ.extend_apply]

/-- **Permuting the inner index in every row of an iterated product measure preserves its law:**
each row `k : ι` may carry its own coordinate measure `μ k`. -/
theorem measurePreserving_pi_pi_comp_perm {ι κ X : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace X] (μ : ι → Measure X) [∀ k, SigmaFinite (μ k)] (π : Equiv.Perm κ) :
    MeasurePreserving (fun (g : ι → κ → X) (k : ι) (j : κ) => g k (π j))
      (Measure.pi fun k : ι => Measure.pi fun _ : κ => μ k)
      (Measure.pi fun k : ι => Measure.pi fun _ : κ => μ k) := by
  let e_col : (κ → X) ≃ᵐ (κ → X) := MeasurableEquiv.piCongrLeft (fun _ : κ => X) π.symm
  have hrow (k : ι) : MeasurePreserving ⇑e_col
      (Measure.pi fun _ : κ => μ k) (Measure.pi fun _ : κ => μ k) :=
    measurePreserving_piCongrLeft (fun _ : κ => μ k) π.symm
  let e_mat : (ι → κ → X) ≃ᵐ (ι → κ → X) := MeasurableEquiv.piCongrRight fun _ : ι => e_col
  have hmp : MeasurePreserving ⇑e_mat
      (Measure.pi fun k : ι => Measure.pi fun _ : κ => μ k)
      (Measure.pi fun k : ι => Measure.pi fun _ : κ => μ k) :=
    measurePreserving_pi _ _ hrow
  convert hmp using 1
  ext g k j
  change g k (π j) = (Equiv.piCongrLeft (fun _ : κ => X) π.symm (g k)) j
  rw [Equiv.piCongrLeft_apply]
  simp

end MeasureTheory
