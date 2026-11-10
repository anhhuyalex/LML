/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.FreeEnergy.Basic

/-!
# The two-replica average `ν` of the vector SK model with i.i.d. couplings

`ν(G) = 𝔼 ⟨G(σ¹, σ²)⟩` for the `N + 1` site system with i.i.d. standard Gaussian couplings, and its
link to the cavity average `ν₁` of the concrete model.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

variable {α : Type*} [MeasurableSpace α]

/-- `ν(G) = 𝔼 ⟨G(σ¹, σ²)⟩`: the disorder average of the two-replica Gibbs average for the
`N + 1` site vector SK model with i.i.d. standard Gaussian couplings. -/
noncomputable def skVectorReplicaAverage {d : ℕ} (μ : Measure α) (ξ : α → Fin d → ℝ) (N : ℕ) (β : ℝ)
    (G : (Fin 2 → Fin (N + 1) → α) → ℝ) : ℝ :=
  ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → α, G σ ∂(Measure.pi fun _ : Fin 2 =>
    (Measure.pi fun _ : Fin (N + 1) => μ).tilted
      (fun τ => skVectorEnergy (N + 1) β g (fun i => ξ (τ i)))) ∂(Measure.pi fun _ : FinPairs (N +
          1) =>
        gaussianReal 0 1)

section Lemmas

variable {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
  (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (N : ℕ) (β : ℝ)

include hξ hbound in
/-- The inner Gibbs average of a bounded measurable function is integrable in the couplings. -/
theorem integrable_skVectorReplicaAverage_inner (G : (Fin 2 → Fin (N + 1) → α) → ℝ) (hG :
  Measurable G)
    (hGb : ∃ M, ∀ x, |G x| ≤ M) :
    Integrable (fun g : FinPairs (N + 1) → ℝ => ∫ σ : Fin 2 → Fin (N + 1) → α, G σ
      ∂(Measure.pi fun _ : Fin 2 => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
        (fun τ => skVectorEnergy (N + 1) β g (fun i => ξ (τ i)))))
      (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
  integrable_integral_skVectorEnergy μ ξ hξ hbound β (gt := fun g => g) measurable_id G hG hGb

include hξ hbound in
/-- `ν` of a constant. -/
theorem skVectorReplicaAverage_const (c : ℝ) : skVectorReplicaAverage μ ξ N β (fun _ => c) = c := by
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  unfold skVectorReplicaAverage
  have : ∀ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → α, c
      ∂(Measure.pi fun _ : Fin 2 => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
        (fun τ => skVectorEnergy (N + 1) β g (fun i => ξ (τ i)))) = c := fun g => by
    have := isProbabilityMeasure_tilted_skVectorEnergy μ ξ hξ hr hbound N β g
    simp
  simp [this]

omit [IsProbabilityMeasure μ] in
/-- `ν` is linear: scaling. -/
theorem skVectorReplicaAverage_const_mul (c : ℝ) (G : (Fin 2 → Fin (N + 1) → α) → ℝ) :
    skVectorReplicaAverage μ ξ N β (fun σ => c * G σ) = c * skVectorReplicaAverage μ ξ N β G := by
  unfold skVectorReplicaAverage
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun g => integral_const_mul _ _)

include hξ hbound in
/-- `ν` is linear: sums. -/
theorem skVectorReplicaAverage_add (G H : (Fin 2 → Fin (N + 1) → α) → ℝ) (hG : Measurable G)
    (hH : Measurable H) (hGb : ∃ M, ∀ x, |G x| ≤ M) (hHb : ∃ M, ∀ x, |H x| ≤ M) :
    skVectorReplicaAverage μ ξ N β (fun σ => G σ + H σ) = skVectorReplicaAverage μ ξ N β G +
      skVectorReplicaAverage μ ξ N β H := by
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  unfold skVectorReplicaAverage
  rw [← integral_add (integrable_skVectorReplicaAverage_inner μ ξ hξ hbound N β G hG hGb)
    (integrable_skVectorReplicaAverage_inner μ ξ hξ hbound N β H hH hHb)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  have := isProbabilityMeasure_tilted_skVectorEnergy μ ξ hξ hr hbound N β g
  obtain ⟨M, hM⟩ := hGb
  obtain ⟨M', hM'⟩ := hHb
  exact integral_add (integrable_of_measurable_bound hG hM) (integrable_of_measurable_bound hH hM')

include hξ hbound in
/-- **Monotonicity of `ν`**: `|G| ≤ H` implies `|ν G| ≤ ν H`. -/
theorem abs_skVectorReplicaAverage_le (G H : (Fin 2 → Fin (N + 1) → α) → ℝ) (hH : Measurable H)
    (hHb : ∃ M, ∀ x, |H x| ≤ M) (hGH : ∀ σ, |G σ| ≤ H σ) :
    |skVectorReplicaAverage μ ξ N β G| ≤ skVectorReplicaAverage μ ξ N β H := by
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  unfold skVectorReplicaAverage
  rw [← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (integrable_skVectorReplicaAverage_inner μ ξ hξ hbound N β H
    hH hHb)
    (Filter.Eventually.of_forall fun g => ?_)
  have := isProbabilityMeasure_tilted_skVectorEnergy μ ξ hξ hr hbound N β g
  obtain ⟨M, hM⟩ := hHb
  exact norm_integral_le_of_norm_le (integrable_of_measurable_bound hH hM)
    (Filter.Eventually.of_forall fun σ => by simpa [Real.norm_eq_abs] using hGH σ)

include hξ hbound in
/-- **The cavity average `ν₁` of the concrete model is `ν`.** At `t = 1` the cavity energy does not
involve the Gaussian field, so the cavity average over the product space is the average over the
couplings alone. -/
theorem skVectorCavityAverage_disorderLaw_eq_replicaAverage (ρ q : Fin d → Fin d → ℝ)
    (G : (Fin 2 → Fin (N + 1) → α) → ℝ) (hG : Measurable G) :
    skVectorCavityAverage μ ξ N β ρ q (skVectorDisorderLaw N β q)
        (fun p ω => ω.1 (finPairsSplit N (Sum.inl p)))
        (fun i ω => ω.1 (finPairsSplit N (Sum.inr i))) (fun u ω => ω.2 u) 1
        (fun σ : Option (Option (Fin 2)) → Fin (N + 1) → α => G fun c => σ (some (some c))) =
      skVectorReplicaAverage μ ξ N β G := by
  have h := skVectorCavityAverage_one_eq μ ξ hξ hbound β ρ q
    (P := skVectorDisorderLaw N β q) (gt := fun p ω => ω.1 p)
    (g := fun p ω => ω.1 (finPairsSplit N (Sum.inl p)))
    (g' := fun i ω => ω.1 (finPairsSplit N (Sum.inr i))) (Y := fun u ω => ω.2 u)
    (fun _ _ => rfl) (fun _ _ => rfl) G hG
  rw [h]
  unfold skVectorReplicaAverage skVectorDisorderLaw
  have := integral_prod_mul (μ := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    (ν := skVectorGaussianLaw β q) (fun g : FinPairs (N + 1) → ℝ => ∫ x : Fin 2 → Fin (N + 1) → α,
      G x ∂(Measure.pi fun _ : Fin 2 => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
        (fun τ => skVectorEnergy (N + 1) β g (fun i => ξ (τ i))))) (fun _ => (1 : ℝ))
  simpa using this

end Lemmas

end SpinGlasses
