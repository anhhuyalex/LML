/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletGhirlandaGuerra

/-!
# Transferring marked Gaussian integration by parts to Poisson blocks

Separate the integrability of the uncentered Gaussian observable from conditional IBP.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

/-- In a positive summable environment, a bounded observable times a centered mark
is summable if and only if the corresponding uncentered observable is summable.
This is the pointwise series identity needed to add back the deterministic centering. -/
theorem gaussian_gibbs_mark_centering_identity
    {J α : Type*} [Fintype J]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : Summable w)
    (Φ : (J → α) → ℝ) {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M)
    (x : (J → α) → ℝ) (c : ℝ)
    (hx : Summable (fun σ : J → α => (∏ j, w (σ j)) * (Φ σ * (x σ - c)))) :
    Summable (fun σ : J → α => (∏ j, w (σ j)) * (Φ σ * x σ)) ∧
    (∑' σ : J → α, (∏ j, w (σ j)) * (Φ σ * x σ)) =
      (∑' σ : J → α, (∏ j, w (σ j)) * (Φ σ * (x σ - c))) +
        c * ∑' σ : J → α, (∏ j, w (σ j)) * Φ σ := by
  classical
  have hbase := summable_prod_pi (J := J) (f := fun _ => w) (fun _ a => hw a)
    (fun _ => hs)
  have hbound : Summable (fun σ : J → α => (∏ j, w (σ j)) * Φ σ) := by
    apply (hbase.mul_right M).of_norm_bounded
    intro σ
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Finset.prod_nonneg
      (fun j _ => hw (σ j)))]
    exact mul_le_mul_of_nonneg_left (hΦ σ) (Finset.prod_nonneg fun j _ => hw (σ j))
  have hadd : (fun σ : J → α => (∏ j, w (σ j)) * (Φ σ * x σ)) =
      (fun σ => (∏ j, w (σ j)) * (Φ σ * (x σ - c))) +
        (fun σ => c * ((∏ j, w (σ j)) * Φ σ)) := by
    funext σ
    simp only [Pi.add_apply]
    ring
  have hlast : Summable (fun σ : J → α => c * ((∏ j, w (σ j)) * Φ σ)) :=
    hbound.mul_left c
  constructor
  · rw [hadd]
    exact hx.add hlast
  · rw [hadd]
    rw [← tsum_mul_left]
    exact hx.tsum_add hlast

/-- The normalized overlap marginal is the extra-replica series with an unused
`none` coordinate removed. This is independent of the origin of the weights. -/
theorem gaussian_gibbs_mark_centering_option_marginal
    {J α : Type*} [Fintype J]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : Summable w)
    (hunit : ∑' a, w a = 1)
    (Φ : (J → α) → ℝ) {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M) :
    (∑' τ : Option J → α, (∏ o, w (τ o)) * Φ (fun j => τ (some j))) =
      ∑' σ : J → α, (∏ j, w (σ j)) * Φ σ :=
  gaussian_ibp_option_replica_marginal hw hs hunit Φ hΦ

/-- Centering a marked Gibbs series does not affect its convergence, and its
uncentered value is the centered value plus the bounded unmarked average. -/
theorem gaussian_gibbs_mark_centering_identity_of_masses
    {J α : Type*} [Fintype J] [Nonempty α]
    (u : α → ℝ) (hu : ∀ a, 0 < u a) (hs : Summable u)
    (Φ : (J → α) → ℝ) {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M)
    (x : (J → α) → ℝ) (c : ℝ)
    (hx : Summable (fun σ : J → α =>
      (∏ j, u (σ j) / ∑' a, u a) * (Φ σ * (x σ - c)))) :
    Summable (fun σ : J → α =>
      (∏ j, u (σ j) / ∑' a, u a) * (Φ σ * x σ)) ∧
    (∑' σ : J → α, (∏ j, u (σ j) / ∑' a, u a) * (Φ σ * x σ)) =
      (∑' σ : J → α,
        (∏ j, u (σ j) / ∑' a, u a) * (Φ σ * (x σ - c))) +
        c * ∑' σ : J → α,
          (∏ j, u (σ j) / ∑' a, u a) * Φ σ := by
  have hpos : 0 < ∑' a, u a :=
    hs.tsum_pos (fun a => (hu a).le) (Classical.choice inferInstance) (hu _)
  exact gaussian_gibbs_mark_centering_identity
    (fun a => u a / ∑' b, u b)
    (fun a => div_nonneg (hu a).le hpos.le) (hs.div_const _) Φ hΦ x c hx

end SpinGlasses
