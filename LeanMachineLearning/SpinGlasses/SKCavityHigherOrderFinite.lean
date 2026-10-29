/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTStep

/-!
# Uniform cavity comparison over finite factor and replica sets

The mixed-moment induction deletes factors and adds fresh replicas. This version of
Eq. (1.298) accepts arbitrary finite replica types and products over a finite set, avoiding
repeated conversions to `Fin`. Its constant precedes the temperature, field and system size.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Uniform Eq. (1.298) for a finite subset of a linear-combination family.** Only
labels within factors actually used must be distinct. The replica index is arbitrary;
its finite cardinality is fixed before the constant. -/
theorem sk_cavity_lincomb_first_order_finset (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R κ : Type*} [Fintype R] (s : Finset κ) (M : ℝ)
    {ι : κ → Type*} [∀ j, Fintype (ι j)] (c : ∀ j, ι j → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (a b : ∀ j, ι j → R),
      (∀ j ∈ s, ∀ i, a j i ≠ b j i) →
      ∀ W : (R → Fin (N + 1) → ℤˣ) → ℝ, (∀ σ, |W σ| ≤ M) →
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
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let f : (R → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
      W σ * ∏ j ∈ s, ∑ i : ι j, c j i * ((N + 1 : ℝ)⁻¹ *
        ((fun v : Fin N => (σ (a j i) v.castSucc : ℝ)) ⬝ᵥ
          fun v : Fin N => (σ (b j i) v.castSucc : ℝ)) - q)
    |(∫ g, ∫ σ : R → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : R → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
  classical
  let e : R ≃ Fin (Fintype.card R) := Fintype.equivFin R
  obtain ⟨H, hH0, hH⟩ := sk_cavity_lincomb_sq_le_finset β₀ hβ₀ s M c
  obtain ⟨C, hC0, hC⟩ := sk_cavity_expansion_of_sq_le_uniform β₀ hβ₀
    (Fintype.card R) s.card H hH0.le
  refine ⟨C, hC0, ?_⟩
  intro β h q hfix hb N a b hab W hW B E Esk f
  let f' : (Fin (Fintype.card R) → Fin (N + 1) → ℤˣ) → ℝ :=
    fun σ => f (fun r => σ (e r))
  have hf := hH β h q hfix hb N (Fintype.card R)
    (fun j i => e (a j i)) (fun j i => e (b j i))
    (fun j hj i => e.injective.ne (hab j hj i))
    (fun σ => W (fun r => σ (e r))) (fun σ => hW _)
  have ht := (hC β h q hfix hb N f' (by simpa only [f', f] using hf)).1
  have hfull : (∫ g, ∫ σ : R → Fin (N + 1) → ℤˣ, f σ
      ∂(Measure.pi fun _ : R => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      ∫ g, ∫ σ : Fin (Fintype.card R) → Fin (N + 1) → ℤˣ, f' σ
        ∂(Measure.pi fun _ : Fin (Fintype.card R) => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    apply integral_congr_ae (ae_of_all _ fun g => ?_)
    exact integral_pi_count_tilted_reindex e (Esk g) f
  have hzero : (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : R → Fin (N + 1) → ℤˣ, f σ
      ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω))
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
      ∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ σ : Fin (Fintype.card R) → Fin (N + 1) → ℤˣ, f' σ
          ∂(Measure.pi fun _ : Fin (Fintype.card R) =>
            Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
    apply integral_congr_ae (ae_of_all _ fun g => ?_)
    apply integral_congr_ae (ae_of_all _ fun ω => ?_)
    exact integral_pi_count_tilted_reindex e (E (π / 2) g ω) f
  rw [hfull, hzero]
  exact ht

end SpinGlasses
