/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Overlaps of random measures with exchangeable coordinates

For a random probability measure `G d` on `EuclideanSpace ℝ ι` whose coordinates play symmetric
roles after averaging over `d`, the mean normalized square norm and the mean normalized square of
the barycenter are given by any single coordinate.

## Main statements

* `MeasureTheory.integral_integral_inv_card_mul_sq_norm_of_exchangeable`.
-/

@[expose] public section

namespace MeasureTheory

/-- **The overlaps of a random measure with exchangeable coordinates** are given by one coordinate:
if the law of every quenched average of a function of `σ i` does not depend on `i`, and
`𝔼 ⟨‖σ‖²⟩` is finite, then `𝔼 ⟨‖σ‖² / |ι|⟩ = 𝔼 ⟨σ i₀²⟩` and
`𝔼 (∑ i, ⟨σ i⟩² / |ι|) = 𝔼 ⟨σ i₀⟩²`. -/
theorem integral_integral_inv_card_mul_sq_norm_of_exchangeable {Ω ι : Type*} [Fintype ι]
    [MeasurableSpace Ω] {P : Measure Ω} {G : Ω → Measure (EuclideanSpace ℝ ι)}
    [∀ d, IsProbabilityMeasure (G d)]
    (hGm : ∀ f : EuclideanSpace ℝ ι → ℝ, Measurable f → Measurable fun d => ∫ σ, f σ ∂(G d))
    (hsq : ∀ d, Integrable (fun σ => ‖σ‖ ^ 2) (G d))
    (hint : Integrable (fun d => ∫ σ, ‖σ‖ ^ 2 ∂(G d)) P) (i₀ : ι)
    (hsymm : ∀ (i : ι) (Φ F : ℝ → ℝ),
      ∫ d, F (∫ σ, Φ (σ i) ∂(G d)) ∂P = ∫ d, F (∫ σ, Φ (σ i₀) ∂(G d)) ∂P) :
    ∫ d, ∫ σ, (Fintype.card ι : ℝ)⁻¹ * ‖σ‖ ^ 2 ∂(G d) ∂P =
        ∫ d, ∫ σ, σ i₀ ^ 2 ∂(G d) ∂P ∧
      ∫ d, (Fintype.card ι : ℝ)⁻¹ * ∑ i, (∫ σ, σ i ∂(G d)) ^ 2 ∂P =
        ∫ d, (∫ σ, σ i₀ ∂(G d)) ^ 2 ∂P := by
  have hcoord : ∀ i : ι, Measurable fun σ : EuclideanSpace ℝ ι => σ i := fun i =>
    (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).measurable
  have hle : ∀ (i : ι) (σ : EuclideanSpace ℝ ι), σ i ^ 2 ≤ ‖σ‖ ^ 2 := fun i σ => by
    simpa only [Real.norm_eq_abs, sq_abs] using
      pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le σ i) 2
  have hcsq : ∀ d i, Integrable (fun σ : EuclideanSpace ℝ ι => σ i ^ 2) (G d) := fun d i =>
    (hsq d).mono' ((hcoord i).pow_const 2).aestronglyMeasurable (ae_of_all _ fun σ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hle i σ)
  have hL2 : ∀ d i, MemLp (fun σ : EuclideanSpace ℝ ι => σ i) 2 (G d) := fun d i =>
    (memLp_two_iff_integrable_sq (hcoord i).aestronglyMeasurable).2 (hcsq d i)
  have hi2 : ∀ i, Integrable (fun d => ∫ σ, σ i ^ 2 ∂(G d)) P := fun i =>
    hint.mono' (hGm _ ((hcoord i).pow_const 2)).aestronglyMeasurable (ae_of_all _ fun d => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
      exact integral_mono (hcsq d i) (hsq d) fun σ => hle i σ)
  have hi1 : ∀ i, Integrable (fun d => (∫ σ, σ i ∂(G d)) ^ 2) P := fun i =>
    (hi2 i).mono' ((hGm _ (hcoord i)).pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun d => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        simpa only [Real.norm_eq_abs, sq_abs] using
          sq_norm_integral_le_integral_sq_norm (hL2 d i))
  have hcard : (Fintype.card ι : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨i₀⟩).ne'
  constructor
  · have h1 : ∀ d, ∫ σ, (Fintype.card ι : ℝ)⁻¹ * ‖σ‖ ^ 2 ∂(G d) =
        (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∫ σ, σ i ^ 2 ∂(G d) := fun d => by
      rw [integral_const_mul, ← integral_finsetSum _ fun i _ => hcsq d i]
      simp only [EuclideanSpace.real_norm_sq_eq]
    simp only [h1]
    rw [integral_const_mul, integral_finsetSum _ fun i _ => hi2 i,
      Finset.sum_congr rfl fun i _ => hsymm i (fun x => x ^ 2) fun y => y,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ hcard]
  · rw [integral_const_mul, integral_finsetSum _ fun i _ => hi1 i,
      Finset.sum_congr rfl fun i _ => hsymm i (fun x => x) fun y => y ^ 2,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ hcard]

end MeasureTheory
