/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.QuarticSignProd
public import LeanMachineLearning.SpinGlasses.SKCavityDecoupledEndpoint
public import LeanMachineLearning.SpinGlasses.GibbsReplicaMarginal

/-!
# Decoupled endpoint for an arbitrary set of replicas, and sign monomials

Talagrand's Lemma 1.6.2 (`sk_cavity_decoupled_endpoint`) for `Fin n` replicas, restated for any
finite set `R` of replicas, and its consequence for the products of four last spins that occur in
the algebra of Section 1.8: for `x ≠ y` and `a ≠ b`,
`ε_x ε_y ε_a ε_b` has decoupled average `𝔼 tanh^{4 - 2 c} Y`, where `c` counts the coincidences
among `x, y, a, b`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Lemma 1.6.2 for an arbitrary finite set of replicas.** -/
theorem sk_cavity_decoupled_endpoint_replicas (N : ℕ) (β q h : ℝ) {R : Type*} [Fintype R]
    (I : Finset R) (F : (R → Fin N → ℤˣ) → ℝ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) →
        (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ σ : R → Fin (N + 1) → ℤˣ,
          F (fun r i => σ r i.castSucc) * ∏ r ∈ I, ((σ r (Fin.last N) : ℤˣ) : ℝ)
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    (∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ I.card ∂(gaussianReal 0 1)) *
      ∫ g', ∫ ρ : R → Fin N → ℤˣ, F ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  intro B E
  let e : R ≃ Fin (Fintype.card R) := Fintype.equivFin R
  have key := sk_cavity_decoupled_endpoint N (Fintype.card R) β q h (I.map e.toEmbedding)
    (fun ρ => F fun r => ρ (e r))
  simp only [Finset.card_map] at key
  have hL : ∀ (g' : FinPairs N → ℝ) (ω : (Fin N → ℝ) × ℝ),
      ∫ σ : R → Fin (N + 1) → ℤˣ,
          F (fun r i => σ r i.castSucc) * ∏ r ∈ I, ((σ r (Fin.last N) : ℤˣ) : ℝ)
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω)) =
        ∫ σ : Fin (Fintype.card R) → Fin (N + 1) → ℤˣ,
          F (fun r i => σ (e r) i.castSucc) *
            ∏ r ∈ I.map e.toEmbedding, ((σ r (Fin.last N) : ℤˣ) : ℝ)
          ∂(Measure.pi fun _ : Fin (Fintype.card R) =>
            Measure.count.tilted (E (π / 2) g' ω)) := fun g' ω => by
    rw [integral_pi_count_tilted_reindex e (E (π / 2) g' ω)]
    simp only [Finset.prod_map, Equiv.coe_toEmbedding]
  have hR : ∀ g' : FinPairs N → ℝ,
      ∫ ρ : R → Fin N → ℤˣ, F ρ ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ))) =
        ∫ ρ : Fin (Fintype.card R) → Fin N → ℤˣ, F (fun r => ρ (e r))
          ∂(Measure.pi fun _ : Fin (Fintype.card R) => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ))) := fun g' =>
    integral_pi_count_tilted_reindex e _ F
  simp_rw [hL, hR]
  exact key

/-- **Decoupled average of a product of four last spins.**  For distinct `x ≠ y` and `a ≠ b`,
`ε_x ε_y ε_a ε_b` has the decoupled average `𝔼 tanh^{4 - 2 c} Y`, where `c` is the number of
coincidences among `x, y, a, b`, times the average of the old-spin observable. -/
theorem sk_cavity_decoupled_endpoint_quartic (N : ℕ) (β q h : ℝ) {R : Type*} [Fintype R]
    [DecidableEq R] {x y a b : R} (hxy : x ≠ y) (hab : a ≠ b)
    (F : (R → Fin N → ℤˣ) → ℝ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) →
        (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ σ : R → Fin (N + 1) → ℤˣ,
          F (fun r i => σ r i.castSucc) *
            (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) *
              ((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ))
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    (∫ z, Real.tanh (β * z * Real.sqrt q + h) ^
        (4 - 2 * ((if x = a then 1 else 0) + (if x = b then 1 else 0) +
          (if y = a then 1 else 0) + (if y = b then 1 else 0))) ∂(gaussianReal 0 1)) *
      ∫ g', ∫ ρ : R → Fin N → ℤˣ, F ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  intro B E
  obtain ⟨I, hcard, hprod⟩ := exists_finset_prod_eq_quartic (A := ℝ) hxy hab
  have hpt : ∀ σ : R → Fin (N + 1) → ℤˣ,
      F (fun r i => σ r i.castSucc) *
        (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) *
          ((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ)) =
      F (fun r i => σ r i.castSucc) * ∏ r ∈ I, ((σ r (Fin.last N) : ℤˣ) : ℝ) := fun σ => by
    rw [hprod (fun r => ((σ r (Fin.last N) : ℤˣ) : ℝ)) fun r => ?_]
    exact units_cast_sq _
  simp_rw [hpt]
  have hI : I.card = 4 - 2 * ((if x = a then 1 else 0) + (if x = b then 1 else 0) +
      (if y = a then 1 else 0) + (if y = b then 1 else 0)) := by omega
  rw [← hI]
  exact sk_cavity_decoupled_endpoint_replicas N β q h I F

end SpinGlasses
