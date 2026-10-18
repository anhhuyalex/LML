/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeInvariance
public import LeanMachineLearning.SpinGlasses.GaussianIBPCountable

/-!
# Real-valued Gibbs series for the Ruelle cascade

The Gibbs average of a real observable of `K` replicas for the weights `W(α) = w(α) exp (t g(α))`
is the series `∑_σ (∏_k W(σ_k) / ∑_α W(α)) Φ(σ)`; this is the form in which countable Gaussian
integration by parts is stated. For nonnegative finite observables it is the real part of the
quotient of `[0, ∞]`-valued sums used in the Bolthausen--Sznitman invariance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SpinGlasses

/-- The Gibbs series of a real observable `Φ` of `K` replicas for the real weights `W`. -/
noncomputable def gibbsSeries {α K : Type*} [Fintype K] (W : α → ℝ) (Φ : (K → α) → ℝ) : ℝ :=
  ∑' σ : K → α, (∏ k, W (σ k) / ∑' b, W b) * Φ σ

/-- **From quotients in `[0, ∞]` to Gibbs series.** For finite weights and a finite observable
the real part of the quotient `∑_σ ∏_k w(σ_k) F(σ) / (∑ w)^{|K|}` is the Gibbs series of the real
parts. -/
theorem toReal_tsum_prod_div_eq_gibbsSeries {α K : Type*} [Fintype K] (w : α → ℝ≥0∞)
    (hw : ∀ a, w a ≠ ∞) (F : (K → α) → ℝ≥0∞) (hF : ∀ σ, F σ ≠ ∞) :
    ((∑' σ : K → α, (∏ k, w (σ k)) * F σ) / (∑' a, w a) ^ Fintype.card K).toReal =
      gibbsSeries (fun a => (w a).toReal) (fun σ => (F σ).toReal) := by
  unfold gibbsSeries
  rw [ENNReal.toReal_div, ENNReal.tsum_toReal_eq (fun σ => ENNReal.mul_ne_top
    (ENNReal.prod_ne_top fun k _ => hw _) (hF σ)), ENNReal.toReal_pow,
    ENNReal.tsum_toReal_eq hw, ← tsum_div_const]
  refine tsum_congr fun σ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_prod, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ]
  ring

end SpinGlasses
