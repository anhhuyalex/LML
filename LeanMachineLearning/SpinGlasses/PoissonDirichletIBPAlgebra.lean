/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletGibbs

/-!
# Algebra of the extra Gaussian-IBP replica

The `Option R` coordinate `none` represents the new replica. These deterministic identities
separate the extra-replica algebra from the random-environment Fubini argument.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

/-- The `Option R` Gaussian-IBP correction factors out its common covariance scalar.
This is useful even when the overlap observable is merely a function on the finite set of
zero-one overlap matrices, without a global boundedness assumption. -/
theorem gaussian_ibp_overlap_correction_factor
    {R α : Type*} [Fintype R] [DecidableEq α]
    (t : ℝ) (r₀ : R) (τ : Option R → α) :
    (∑ r, t * (if τ (some r₀) = τ (some r) then (1 : ℝ) else 0)) -
        (Fintype.card R : ℝ) * t * (if τ (some r₀) = τ none then 1 else 0) =
      t * ((∑ r, if τ (some r₀) = τ (some r) then (1 : ℝ) else 0) -
        (Fintype.card R : ℝ) * (if τ (some r₀) = τ none then 1 else 0)) := by
  rw [← Finset.mul_sum]
  ring

/-- An `Option R` Gibbs series has the expected marginal on its old replicas. The
extra coordinate has normalized weight one; bounded observables automatically satisfy
the absolute summability hypothesis. -/
theorem gaussian_ibp_option_replica_marginal
    {R α : Type*} [Fintype R]
    {w : α → ℝ} (hw0 : ∀ a, 0 ≤ w a) (hws : Summable w)
    (hw : ∑' a, w a = 1) (Φ : (R → α) → ℝ)
    {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M) :
    (∑' τ : Option R → α, (∏ o, w (τ o)) * Φ (fun r => τ (some r))) =
      ∑' σ : R → α, (∏ r, w (σ r)) * Φ σ := by
  have hbound : Summable (fun σ : R → α =>
      (∏ r, w (σ r)) * |Φ σ|) := by
    have hs := summable_prod_pi (J := R) (f := fun _ => w) (fun _ a => hw0 a)
      (fun _ => hws)
    exact (hs.mul_right M).of_nonneg_of_le
      (fun σ => mul_nonneg (Finset.prod_nonneg fun r _ => hw0 _) (abs_nonneg _))
      (fun σ => mul_le_mul_of_nonneg_left (hΦ σ)
        (Finset.prod_nonneg fun r _ => hw0 _))
  have hsum : Summable (fun σ : R → α => (∏ r, w (σ r)) * Φ σ) := by
    have hs : Summable (fun σ : R → α =>
        ‖(∏ r, w (σ r)) * Φ σ‖) := by
      convert hbound using 1
      funext σ
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Finset.prod_nonneg fun r _ => hw0 _)]
    exact hs.of_norm
  exact tsum_prod_option_some hw0 hws hw Φ hsum

/-- Inserting the self-overlap `R₀₀ = 1` into the covariance correction splits
its Gibbs expectation into a constant, the other old replicas, and the new replica.
The formula is pointwise and needs no summability or probability hypotheses. -/
theorem gaussian_ibp_overlap_correction_self
    {R α : Type*} [Fintype R] [DecidableEq R] [DecidableEq α]
    (r₀ : R) (τ : Option R → α) :
    (∑ r, if τ (some r₀) = τ (some r) then (1 : ℝ) else 0) -
        (Fintype.card R : ℝ) * (if τ (some r₀) = τ none then 1 else 0) =
      1 + (∑ r ∈ (Finset.univ : Finset R).erase r₀,
          if τ (some r₀) = τ (some r) then (1 : ℝ) else 0) -
        (Fintype.card R : ℝ) * (if τ (some r₀) = τ none then 1 else 0) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r₀)]
  simp

/-- The correction at zero Gaussian tilt vanishes pointwise, including the extra-replica
term; no interchange of expectations or derivatives is needed for this simplification. -/
theorem gaussian_ibp_overlap_correction_zero
    {R α : Type*} [Fintype R] [DecidableEq α]
    (r₀ : R) (τ : Option R → α) :
    (∑ r, (0 : ℝ) * (if τ (some r₀) = τ (some r) then 1 else 0)) -
      (Fintype.card R : ℝ) * 0 * (if τ (some r₀) = τ none then 1 else 0) = 0 := by
  simp

end SpinGlasses
