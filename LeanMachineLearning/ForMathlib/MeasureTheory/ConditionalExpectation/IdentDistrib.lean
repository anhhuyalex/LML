/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Conditional expectations only depend on the joint law

If `A` takes values in a standard Borel space, the conditional expectation `P[F ∘ A | σ(B)]` is a
fixed function of `B`, namely `y ↦ ∫ F d(condDistrib A B P y)`, and `condDistrib A B P` is by
definition the disintegration of the joint law `P.map (B, A)`.  Hence everything computed from
`P[F ∘ A | σ(B)]` is determined by the law of the pair `(B, A)`:

* the conditional expectations of two pairs with the same law are the same function of `B`
  (`condExp_comp_ae_eq_of_map_eq`);
* their `L²` norms agree (`integral_sq_condExp_comp_eq_of_map_eq`), even on different probability
  spaces.

The second statement is how exchangeability enters the proofs of Lemmas 1.5 and 1.6 of
[Panchenko, 2013, §1.4]: exchangeability gives equality in law of pairs, and this file turns that
into equality of the `L²` norms of conditional expectations.

## Main declarations

* `ProbabilityTheory.condExp_comp_ae_eq_of_map_eq`
* `ProbabilityTheory.integral_sq_condExp_comp_eq_integral_condDistrib`
* `ProbabilityTheory.integral_sq_condExp_comp_eq_of_map_eq`
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω Ω' β E : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mβ : MeasurableSpace β} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
  {P : Measure Ω} {P' : Measure Ω'} {B : Ω → β} {A : Ω → E} {F : E → ℝ}

/-- `condDistrib` only depends on the joint law of `(B, A)`. -/
theorem condDistrib_eq_of_map_eq [IsFiniteMeasure P] [IsFiniteMeasure P'] {B' : Ω' → β}
    {A' : Ω' → E} (h : P.map (fun ω => (B ω, A ω)) = P'.map (fun ω => (B' ω, A' ω))) :
    condDistrib A B P = condDistrib A' B' P' := by
  have key : ∀ (ρ ρ' : Measure (β × E)) [IsFiniteMeasure ρ] [IsFiniteMeasure ρ'], ρ = ρ' →
      ρ.condKernel = ρ'.condKernel := by
    rintro ρ ρ' _ _ rfl
    rfl
  rw [condDistrib_def, condDistrib_def]
  exact key _ _ h

/-- The `L²` norm of `P[F ∘ A | σ(B)]` is the `L²(P.map B)` norm of
`y ↦ ∫ F d(condDistrib A B P y)`. -/
theorem integral_sq_condExp_comp_eq_integral_condDistrib [IsFiniteMeasure P] (hB : Measurable B)
    (hA : AEMeasurable A P) (hF : Measurable F) (hFb : ∃ C, ∀ x, |F x| ≤ C) :
    ∫ ω, P[fun ω => F (A ω) | mβ.comap B] ω ^ 2 ∂P =
      ∫ y, (∫ x, F x ∂condDistrib A B P y) ^ 2 ∂P.map B := by
  obtain ⟨C, hC⟩ := hFb
  have hint : Integrable (fun ω => F (A ω)) P :=
    Integrable.of_bound (hF.comp_aemeasurable hA).aestronglyMeasurable C
      (.of_forall fun ω => by simpa using hC (A ω))
  have hψ : StronglyMeasurable fun y => ∫ x, F x ∂condDistrib A B P y :=
    hF.stronglyMeasurable.integral_kernel
  have hψ2 : StronglyMeasurable fun y => (∫ x, F x ∂condDistrib A B P y) ^ 2 := hψ.pow 2
  rw [integral_map hB.aemeasurable hψ2.aestronglyMeasurable]
  refine integral_congr_ae ?_
  filter_upwards [condExp_ae_eq_integral_condDistrib hB hA hF.stronglyMeasurable hint] with ω hω
  rw [hω]

/-- If `(B, A)` and `(B', A')` have the same law, then `P[F ∘ A | σ(B)]` and `P'[F ∘ A' | σ(B')]`
have the same `L²` norm (even though they live on different probability spaces). -/
theorem integral_sq_condExp_comp_eq_of_map_eq [IsFiniteMeasure P] [IsFiniteMeasure P']
    {B' : Ω' → β} {A' : Ω' → E} (hB : Measurable B) (hA : AEMeasurable A P) (hB' : Measurable B')
    (hA' : AEMeasurable A' P') (hF : Measurable F) (hFb : ∃ C, ∀ x, |F x| ≤ C)
    (h : P.map (fun ω => (B ω, A ω)) = P'.map (fun ω => (B' ω, A' ω))) :
    ∫ ω, P[fun ω => F (A ω) | mβ.comap B] ω ^ 2 ∂P =
      ∫ ω, P'[fun ω => F (A' ω) | mβ.comap B'] ω ^ 2 ∂P' := by
  rw [integral_sq_condExp_comp_eq_integral_condDistrib hB hA hF hFb,
    integral_sq_condExp_comp_eq_integral_condDistrib hB' hA' hF hFb]
  have hm : P.map B = P'.map B' := by
    rw [← Measure.fst_map_prodMk₀ hB.aemeasurable hA,
      ← Measure.fst_map_prodMk₀ hB'.aemeasurable hA', h]
  rw [condDistrib_eq_of_map_eq h, hm]

/-- If `(B, A)` and `(B, A')` have the same law under `P`, then `P[F ∘ A | σ(B)]` and
`P[F ∘ A' | σ(B)]` coincide almost surely: the conditional expectation is the same function of
`B`. -/
theorem condExp_comp_ae_eq_of_map_eq [IsFiniteMeasure P] {A' : Ω → E} (hB : Measurable B)
    (hA : AEMeasurable A P) (hA' : AEMeasurable A' P) (hF : Measurable F)
    (hFb : ∃ C, ∀ x, |F x| ≤ C)
    (h : P.map (fun ω => (B ω, A ω)) = P.map (fun ω => (B ω, A' ω))) :
    P[fun ω => F (A ω) | mβ.comap B] =ᵐ[P] P[fun ω => F (A' ω) | mβ.comap B] := by
  obtain ⟨C, hC⟩ := hFb
  have hint : ∀ {A : Ω → E}, AEMeasurable A P → Integrable (fun ω => F (A ω)) P := fun hA =>
    Integrable.of_bound (hF.comp_aemeasurable hA).aestronglyMeasurable C
      (.of_forall fun ω => by simpa using hC _)
  filter_upwards [condExp_ae_eq_integral_condDistrib hB hA hF.stronglyMeasurable (hint hA),
    condExp_ae_eq_integral_condDistrib hB hA' hF.stronglyMeasurable (hint hA')] with ω h1 h2
  rw [h1, h2, condDistrib_eq_of_map_eq h]

end ProbabilityTheory
