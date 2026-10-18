/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeInvariance
public import LeanMachineLearning.SpinGlasses.GaussianIBPCountable
public import LeanMachineLearning.SpinGlasses.PoissonDirichletIdentities

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

section GibbsSeries

variable {α K : Type*} [Fintype K] {W : α → ℝ}

/-- The Gibbs weights `∏_k W(σ_k) / ∑ W` of `K` replicas are a probability on `K → α`. -/
theorem hasSum_prod_div (hW : ∀ a, 0 ≤ W a) (hs : Summable W) (h0 : ∑' b, W b ≠ 0) :
    HasSum (fun σ : K → α => ∏ k, W (σ k) / ∑' b, W b) 1 := by
  have hZ : 0 < ∑' b, W b := lt_of_le_of_ne (tsum_nonneg hW) (Ne.symm h0)
  have hnn : ∀ σ : K → α, 0 ≤ ∏ k, W (σ k) / ∑' b, W b := fun σ =>
    Finset.prod_nonneg fun k _ => div_nonneg (hW _) hZ.le
  have hone : ∑' a, ENNReal.ofReal (W a / ∑' b, W b) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun a => div_nonneg (hW a) hZ.le)
      (hs.div_const _), tsum_div_const, div_self h0, ENNReal.ofReal_one]
  have hprod : ∑' σ : K → α, ENNReal.ofReal (∏ k, W (σ k) / ∑' b, W b) = 1 := by
    simp_rw [ENNReal.ofReal_prod_of_nonneg fun k _ => div_nonneg (hW _) hZ.le]
    rw [ENNReal.tsum_pi_prod fun _ a => ENNReal.ofReal (W a / ∑' b, W b)]
    simp [hone]
  have hsum : Summable fun σ : K → α => ∏ k, W (σ k) / ∑' b, W b :=
    summable_of_tsum_ofReal_lt_top hnn (by rw [hprod]; exact ENNReal.one_lt_top)
  refine hsum.hasSum_iff.2 ?_
  have h := ENNReal.ofReal_tsum_of_nonneg hnn hsum
  rw [hprod] at h
  exact ENNReal.ofReal_eq_one.1 h

/-- A bounded observable is summable against the Gibbs weights. -/
theorem summable_prod_div_mul (hW : ∀ a, 0 ≤ W a) (hs : Summable W) (h0 : ∑' b, W b ≠ 0)
    {Φ : (K → α) → ℝ} {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M) :
    Summable fun σ : K → α => (∏ k, W (σ k) / ∑' b, W b) * Φ σ := by
  have hZ : 0 < ∑' b, W b := lt_of_le_of_ne (tsum_nonneg hW) (Ne.symm h0)
  refine Summable.of_norm_bounded ((hasSum_prod_div hW hs h0).summable.mul_right M) fun σ => ?_
  rw [norm_mul, Real.norm_of_nonneg (Finset.prod_nonneg fun k _ => div_nonneg (hW _) hZ.le)]
  exact mul_le_mul_of_nonneg_left (hΦ σ) (Finset.prod_nonneg fun k _ => div_nonneg (hW _) hZ.le)

/-- The Gibbs series of a bounded observable is bounded by the same constant. -/
theorem abs_gibbsSeries_le (hW : ∀ a, 0 ≤ W a) (hs : Summable W) (h0 : ∑' b, W b ≠ 0)
    {Φ : (K → α) → ℝ} {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M) : |gibbsSeries W Φ| ≤ M := by
  have hZ : 0 < ∑' b, W b := lt_of_le_of_ne (tsum_nonneg hW) (Ne.symm h0)
  have hnn : ∀ σ : K → α, 0 ≤ ∏ k, W (σ k) / ∑' b, W b := fun σ =>
    Finset.prod_nonneg fun k _ => div_nonneg (hW _) hZ.le
  have h1 := (hasSum_prod_div (K := K) hW hs h0)
  calc |gibbsSeries W Φ| ≤ ∑' σ : K → α, ‖(∏ k, W (σ k) / ∑' b, W b) * Φ σ‖ :=
        norm_tsum_le_tsum_norm (summable_prod_div_mul hW hs h0 hΦ).norm
    _ ≤ ∑' σ : K → α, (∏ k, W (σ k) / ∑' b, W b) * M := by
        refine Summable.tsum_le_tsum (fun σ => ?_) (summable_prod_div_mul hW hs h0 hΦ).norm
          (h1.summable.mul_right M)
        rw [norm_mul, Real.norm_of_nonneg (hnn σ)]
        exact mul_le_mul_of_nonneg_left (hΦ σ) (hnn σ)
    _ = M := by rw [tsum_mul_right, h1.tsum_eq, one_mul]

/-- **Marginalizing the last replica.** The Gibbs series of an observable of the first `n`
replicas does not change when a further replica is added. -/
theorem gibbsSeries_castSucc {n : ℕ} (hW : ∀ a, 0 ≤ W a) (hs : Summable W)
    (h0 : ∑' b, W b ≠ 0) {Φ : (Fin n → α) → ℝ} {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M) :
    ∑' τ : Fin (n + 1) → α, (∏ k, W (τ k) / ∑' b, W b) * Φ (fun k => τ k.castSucc) =
      ∑' σ : Fin n → α, (∏ k, W (σ k) / ∑' b, W b) * Φ σ := by
  rw [← (Fin.snocEquiv fun _ : Fin (n + 1) => α).tsum_eq]
  have e : ∀ x : α × (Fin n → α),
      (∏ k, W (Fin.snocEquiv (fun _ : Fin (n + 1) => α) x k) / ∑' b, W b) *
        Φ (fun k => Fin.snocEquiv (fun _ : Fin (n + 1) => α) x k.castSucc) =
      (W x.1 / ∑' b, W b) * ((∏ k, W (x.2 k) / ∑' b, W b) * Φ x.2) := by
    intro x
    rw [Fin.prod_univ_castSucc]
    simp [Fin.snocEquiv, Fin.snoc_castSucc, Fin.snoc_last]
    ring
  simp_rw [e]
  have hg := summable_prod_div_mul (K := Fin n) hW hs h0 hΦ
  have hf : Summable fun a => W a / ∑' b, W b := hs.div_const _
  rw [← tsum_mul_tsum_of_summable_norm (hf.norm) (hg.norm), tsum_div_const, div_self h0,
    one_mul]

end GibbsSeries

end SpinGlasses
