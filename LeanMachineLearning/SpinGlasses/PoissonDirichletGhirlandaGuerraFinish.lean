/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletGhirlandaGuerraBlocks

/-!
# Algebraic assembly of the Poisson-Dirichlet Ghirlanda--Guerra identity

The normalized old-replica overlap is separated into self-overlap and the
remaining replicas. This formulation applies to any countable Gibbs law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpinGlasses

/-- Separate the self-overlap in an old-replica Gibbs average. No probabilistic
hypotheses are required: positivity and summability of the weights suffice. -/
theorem gibbs_old_replica_self_overlap
    {J α : Type*} [Fintype J] [DecidableEq J] [DecidableEq α]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : Summable w)
    (r₀ : J) (Φ : (J → α) → ℝ) {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M) :
    (∑' σ : J → α, (∏ j, w (σ j)) *
      (Φ σ * ∑ j, if σ r₀ = σ j then 1 else 0)) =
    (∑' σ : J → α, (∏ j, w (σ j)) * Φ σ) +
      ∑ j ∈ (Finset.univ : Finset J).erase r₀,
        ∑' σ : J → α, (∏ k, w (σ k)) *
          (Φ σ * if σ r₀ = σ j then 1 else 0) := by
  classical
  have hbase := summable_prod_pi (J := J) (f := fun _ => w)
    (fun _ a => hw a) (fun _ => hs)
  have hbound (F : (J → α) → ℝ) (hF : ∀ σ, |F σ| ≤ M) :
      Summable (fun σ : J → α => (∏ j, w (σ j)) * F σ) := by
    apply (hbase.mul_right M).of_norm_bounded
    intro σ
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Finset.prod_nonneg fun j _ => hw (σ j))]
    exact mul_le_mul_of_nonneg_left (hF σ)
      (Finset.prod_nonneg fun j _ => hw (σ j))
  have hplain := hbound Φ hΦ
  have hterm (j : J) : Summable (fun σ : J → α =>
      (∏ k, w (σ k)) * (Φ σ * if σ r₀ = σ j then 1 else 0)) := by
    apply hbound (fun σ => Φ σ * if σ r₀ = σ j then 1 else 0)
    intro σ
    split_ifs
    · simpa using hΦ σ
    · simpa using (abs_nonneg (Φ σ)).trans (hΦ σ)
  have hpoint (σ : J → α) :
      (∏ j, w (σ j)) * (Φ σ * ∑ j, if σ r₀ = σ j then 1 else 0) =
      (∏ j, w (σ j)) * Φ σ +
        ∑ j ∈ (Finset.univ : Finset J).erase r₀,
          (∏ k, w (σ k)) * (Φ σ * if σ r₀ = σ j then 1 else 0) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r₀)]
    simp only [ite_true]
    rw [mul_add, mul_one, mul_add]
    rw [Finset.mul_sum, Finset.mul_sum]
  simp_rw [hpoint]
  have hfinite : Summable (fun σ : J → α =>
      ∑ j ∈ (Finset.univ : Finset J).erase r₀,
        (∏ k, w (σ k)) * (Φ σ * if σ r₀ = σ j then 1 else 0)) :=
    summable_sum (fun j _ => hterm j)
  rw [hplain.tsum_add hfinite]
  congr 1
  exact Summable.tsum_finsetSum (fun j _ => hterm j)

/-- The normalized Gaussian-IBP correction, with the diagonal term made explicit.
The identity holds for every bounded replica observable and normalized
nonnegative summable weights, independently of the Poisson construction. -/
theorem gaussian_ibp_overlap_correction_self_marginal
    {J α : Type*} [Fintype J] [DecidableEq J] [DecidableEq α]
    {w : α → ℝ} (hw0 : ∀ a, 0 ≤ w a) (hws : Summable w)
    (hw : ∑' a, w a = 1) (r₀ : J)
    (Φ : (J → α) → ℝ) {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M) (t : ℝ) :
    (∑' τ : Option J → α, (∏ o, w (τ o)) *
      (Φ (fun j => τ (some j)) *
        ((∑ j, t * (if τ (some r₀) = τ (some j) then 1 else 0)) -
          (Fintype.card J : ℝ) * t *
            (if τ (some r₀) = τ none then 1 else 0)))) =
      t * ((∑' σ : J → α, (∏ j, w (σ j)) * Φ σ) +
        (∑ j ∈ (Finset.univ : Finset J).erase r₀,
          ∑' σ : J → α, (∏ k, w (σ k)) *
            (Φ σ * if σ r₀ = σ j then 1 else 0)) -
        (Fintype.card J : ℝ) *
          (∑' τ : Option J → α, (∏ o, w (τ o)) *
            (Φ (fun j => τ (some j)) *
              (if τ (some r₀) = τ none then 1 else 0)))) := by
  rw [gaussian_ibp_overlap_correction_marginal hw0 hws hw r₀ Φ hΦ t]
  rw [gibbs_old_replica_self_overlap w hw0 hws r₀ Φ hΦ]

/-- Reindex a replica series from `Option (Fin n)` to `Fin (n+1)`.
The fresh replica `none` occupies the last coordinate. -/
theorem tsum_option_fin_replica_eq
    {α : Type*} (n : ℕ) (w : α → ℝ)
    (Φ : (Option (Fin n) → α) → ℝ) :
    (∑' τ : Option (Fin n) → α,
      (∏ o, w (τ o)) * Φ τ) =
      ∑' σ : Fin (n + 1) → α,
        (∏ j, w (σ j)) * Φ (σ ∘ finSuccEquivLast.symm) := by
  classical
  let e : (Option (Fin n) → α) ≃ (Fin (n + 1) → α) :=
    Equiv.arrowCongr finSuccEquivLast.symm (Equiv.refl α)
  have he (τ : Option (Fin n) → α) :
      e τ = τ ∘ finSuccEquivLast := rfl
  calc
    _ = ∑' σ : Fin (n + 1) → α,
          (∏ o, w ((e.symm σ) o)) * Φ (e.symm σ) := by
      exact (Equiv.tsum_eq e.symm
        (fun τ => (∏ o, w (τ o)) * Φ τ)).symm
    _ = _ := by
      apply tsum_congr
      intro σ
      have hs : e.symm σ = σ ∘ finSuccEquivLast.symm := rfl
      rw [hs]
      congr 1
      exact Fintype.prod_equiv finSuccEquivLast.symm
        (fun o => w (σ (finSuccEquivLast.symm o))) (fun j => w (σ j)) (fun _ => rfl)


end SpinGlasses
