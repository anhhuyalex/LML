/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTStep

/-!
# Replacing truncated products by full products

The replacement before Talagrand's Eq. (1.313) is a sum over all nonempty sets of
last-site corrections. We reuse the same absolute-moment estimate that controls the
higher-order remainder of Eq. (1.310). The bounded factor may depend on every spin.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **The truncated-to-full product comparison before Eq. (1.313).**
For `k` overlap factors the absolute first moment of their product difference, times any
fixed uniformly bounded observable, is at most `C/(N+1)^((k+1)/2)`. Coefficients are fixed
before the constant; replica labels, the site count and the bounded observable may vary. -/
theorem sk_overlap_prod_sub_truncated_le (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) {κ : Type*} [Fintype κ]
    {ι : κ → Type*} [∀ j, Fintype (ι j)] (c : ∀ j, ι j → ℝ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N n : ℕ) (a b : ∀ j, ι j → Fin n), (∀ j i, a j i ≠ b j i) →
      ∀ (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
        (_ : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
        (Uf Um e : κ → (Fin n → Fin (N + 1) → ℤˣ) → ℝ),
      (∀ j σ, Uf j σ = ∑ i : ι j, c j i * ((N + 1 : ℝ)⁻¹ *
        ((fun v : Fin (N + 1) => (σ (a j i) v : ℝ)) ⬝ᵥ
          fun v : Fin (N + 1) => (σ (b j i) v : ℝ)) - q)) →
      (∀ j σ, Um j σ = ∑ i : ι j, c j i * ((N + 1 : ℝ)⁻¹ *
        ((fun v : Fin N => (σ (a j i) v.castSucc : ℝ)) ⬝ᵥ
          fun v : Fin N => (σ (b j i) v.castSucc : ℝ)) - q)) →
      (∀ j σ, e j σ = ∑ i : ι j, c j i *
        ((σ (a j i) (Fin.last N) : ℝ) * (σ (b j i) (Fin.last N) : ℝ))) →
      ∀ W : (Fin n → Fin (N + 1) → ℤˣ) → ℝ, (∀ σ, |W σ| ≤ M) →
      ν (fun σ => |W σ * ((∏ j, Uf j σ) - ∏ j, Um j σ)|) ≤
        C / ((N : ℝ) + 1) ^ (((Fintype.card κ + 1 : ℕ) : ℝ) / 2) := by
  classical
  obtain ⟨C, hC0, hC⟩ := sk_overlap_correction_sum_le β₀ hβ₀ c M 1
  refine ⟨C, hC0, ?_⟩
  intro β h q hfix hb N n a b hab ν hν Uf Um e hUf hUm he W hW
  obtain ⟨-, -, hmono, -⟩ := sk_replica_avg_calculus N n β h ν hν
  have hsplit (j : κ) (σ : Fin n → Fin (N + 1) → ℤˣ) :
      Uf j σ = Um j σ + (N + 1 : ℝ)⁻¹ * e j σ := by
    rw [hUf, hUm, he, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sk_overlap_succ_eq_cavity]
    ring
  have hpoint (σ : Fin n → Fin (N + 1) → ℤˣ) :
      |W σ * ((∏ j, Uf j σ) - ∏ j, Um j σ)| ≤
      ∑ t ∈ (Finset.univ : Finset κ).powerset with 1 ≤ t.card,
        ((N + 1 : ℝ)⁻¹) ^ t.card *
          |W σ * ((∏ i ∈ t, e i σ) * ∏ j ∈ Finset.univ \ t, Um j σ)| := by
    simp only [hsplit]
    rw [Finset.prod_add_sub_prod_eq_sum_nonempty, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun t _ => ?_)
    have ht : W σ * ((∏ i ∈ t, (N + 1 : ℝ)⁻¹ * e i σ) *
        ∏ j ∈ Finset.univ \ t, Um j σ) = ((N + 1 : ℝ)⁻¹) ^ t.card *
        (W σ * ((∏ i ∈ t, e i σ) * ∏ j ∈ Finset.univ \ t, Um j σ)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      ring
    rw [ht, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((N + 1 : ℝ)⁻¹) ^ t.card)]
  calc
    _ ≤ ν (fun σ => ∑ t ∈ (Finset.univ : Finset κ).powerset with 1 ≤ t.card,
        ((N + 1 : ℝ)⁻¹) ^ t.card *
          |W σ * ((∏ i ∈ t, e i σ) * ∏ j ∈ Finset.univ \ t, Um j σ)|) :=
      hmono _ _ hpoint
    _ = ∑ t ∈ (Finset.univ : Finset κ).powerset with 1 ≤ t.card,
        ((N + 1 : ℝ)⁻¹) ^ t.card * ν (fun σ =>
          |W σ * ((∏ i ∈ t, e i σ) * ∏ j ∈ Finset.univ \ t, Um j σ)|) :=
      sk_replica_avg_finset_sum N n β h ν hν _ _ _
    _ ≤ _ := hC β h q hfix hb N n a b hab ν hν Um e hUm he W hW

end SpinGlasses
