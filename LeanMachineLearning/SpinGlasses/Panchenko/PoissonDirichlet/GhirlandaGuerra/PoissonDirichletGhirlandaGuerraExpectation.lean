/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletGhirlandaGuerraFinish

/-!
# Expected Gaussian overlap correction on Poisson-Dirichlet blocks

Combine the block-space Gaussian integration by parts with the almost-sure
extra-replica marginalization. This keeps the random active index type explicit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpinGlasses

/-- Add back a deterministic centering constant to a marked replica average.
The summability hypotheses are separate: neither equality of expectations nor
convergence of the unmarked series alone implies convergence of the marked one. -/
theorem integral_gibbs_centered_mark_add_constant
    {Ω α J : Type*} [MeasurableSpace Ω] [Fintype J]
    (P : Measure Ω) (w : Ω → α → ℝ)
    (Φ : (J → α) → ℝ) (x : Ω → (J → α) → ℝ) (c : ℝ)
    (hs : ∀ᵐ ω ∂P, Summable (fun σ : J → α =>
      (∏ j, w ω (σ j)) * (Φ σ * (x ω σ - c))) ∧
      Summable (fun σ : J → α => (∏ j, w ω (σ j)) * Φ σ))
    (hcenter : Integrable (fun ω => ∑' σ : J → α,
      (∏ j, w ω (σ j)) * (Φ σ * (x ω σ - c))) P)
    (hplain : Integrable (fun ω => ∑' σ : J → α,
      (∏ j, w ω (σ j)) * Φ σ) P) :
    (∫ ω, ∑' σ : J → α,
      (∏ j, w ω (σ j)) * (Φ σ * x ω σ) ∂P) =
      (∫ ω, ∑' σ : J → α,
        (∏ j, w ω (σ j)) * (Φ σ * (x ω σ - c)) ∂P) +
        c * ∫ ω, ∑' σ : J → α,
          (∏ j, w ω (σ j)) * Φ σ ∂P := by
  have hpoint : ∀ᵐ ω ∂P,
      (∑' σ : J → α, (∏ j, w ω (σ j)) * (Φ σ * x ω σ)) =
        (∑' σ : J → α,
          (∏ j, w ω (σ j)) * (Φ σ * (x ω σ - c))) +
          c * ∑' σ : J → α, (∏ j, w ω (σ j)) * Φ σ := by
    filter_upwards [hs] with ω ⟨hmark, hbase⟩
    have hterm (σ : J → α) :
        (∏ j, w ω (σ j)) * (Φ σ * x ω σ) =
          (∏ j, w ω (σ j)) * (Φ σ * (x ω σ - c)) +
            c * ((∏ j, w ω (σ j)) * Φ σ) := by ring
    simp_rw [hterm]
    rw [hmark.tsum_add (hbase.mul_left c), tsum_mul_left]
  rw [integral_congr_ae hpoint, integral_add hcenter (hplain.const_mul c),
    integral_const_mul]

/-- Gaussian integration by parts for the split Poisson blocks, with its extra
replica expressed as a difference of two expected overlap averages. -/
theorem integral_poissonDirichlet_gaussian_overlap_correction
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1) (t : ℝ)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ =>
        (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1))
    (n : ℕ) (r₀ : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ)
    (hf : Measurable f) :
    (∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 *
          Real.exp (t * ((B (σ j).1.1 ω).2 (σ j).1.2).2) /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1 *
            Real.exp (t * ((B a.1.1 ω).2 a.1.2).2)) *
        (f (fun i j => if σ i = σ j then 1 else 0) *
          ((B (σ r₀).1.1 ω).2 (σ r₀).1.2).2) ∂P) =
    ∫ ω, t *
      ((∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 *
            Real.exp (t * ((B (σ j).1.1 ω).2 (σ j).1.2).2) /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1 *
              Real.exp (t * ((B a.1.1 ω).2 a.1.2).2)) *
          (f (fun i j => if σ i = σ j then 1 else 0) *
            ∑ j : Fin n, if σ r₀ = σ j then 1 else 0)) -
        n * (∑' τ : Option (Fin n) → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          (∏ j, ((B (τ j).1.1 ω).2 (τ j).1.2).1 *
              Real.exp (t * ((B (τ j).1.1 ω).2 (τ j).1.2).2) /
            ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
              ((B a.1.1 ω).2 a.1.2).1 *
                Real.exp (t * ((B a.1.1 ω).2 a.1.2).2)) *
            (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
              (if τ (some r₀) = τ none then 1 else 0)))) ∂P := by
  rw [integral_poissonDirichlet_gaussian_tilt_ibp_blocks
    hζ hζ1 t ν r hBm hB hlaw hμ n r₀ f hf]
  exact integral_congr_ae
    (ae_poissonDirichlet_gaussian_overlap_correction
      hζ hζ1 t ν r hBm hB hlaw hμ n r₀ f)

end SpinGlasses
