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

/-- **The overlaps of a random measure with exchangeable coordinates** in an orthonormal basis
`b` are given by one coordinate. For a.e. disorder, `G d` is a probability measure with finite
second moment. Exchangeability is only used for the two quenched quantities `⟨⟨b i, σ⟩²⟩` and
`⟨⟨b i, σ⟩⟩²`. -/
theorem integral_integral_inv_card_mul_sq_norm_of_exchangeable_orthonormalBasis {Ω ι E : Type*}
    [Fintype ι] [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b : OrthonormalBasis ι ℝ E) {P : Measure Ω}
    {G : Ω → Measure E} (hG : ∀ᵐ d ∂P, IsProbabilityMeasure (G d))
    (hm1 : ∀ i, AEStronglyMeasurable (fun d => ∫ σ, inner ℝ (b i) σ ∂(G d)) P)
    (hm2 : ∀ i, AEStronglyMeasurable (fun d => ∫ σ, inner ℝ (b i) σ ^ 2 ∂(G d)) P)
    (hsq : ∀ᵐ d ∂P, Integrable (fun σ => ‖σ‖ ^ 2) (G d))
    (hint : Integrable (fun d => ∫ σ, ‖σ‖ ^ 2 ∂(G d)) P) (i₀ : ι)
    (hs2 : ∀ i, ∫ d, ∫ σ, inner ℝ (b i) σ ^ 2 ∂(G d) ∂P =
      ∫ d, ∫ σ, inner ℝ (b i₀) σ ^ 2 ∂(G d) ∂P)
    (hs1 : ∀ i, ∫ d, (∫ σ, inner ℝ (b i) σ ∂(G d)) ^ 2 ∂P =
      ∫ d, (∫ σ, inner ℝ (b i₀) σ ∂(G d)) ^ 2 ∂P) :
    ∫ d, ∫ σ, (Fintype.card ι : ℝ)⁻¹ * ‖σ‖ ^ 2 ∂(G d) ∂P =
        ∫ d, ∫ σ, inner ℝ (b i₀) σ ^ 2 ∂(G d) ∂P ∧
      ∫ d, (Fintype.card ι : ℝ)⁻¹ * ∑ i, (∫ σ, inner ℝ (b i) σ ∂(G d)) ^ 2 ∂P =
        ∫ d, (∫ σ, inner ℝ (b i₀) σ ∂(G d)) ^ 2 ∂P := by
  have : FiniteDimensional ℝ E := b.toBasis.finiteDimensional_of_finite
  have hcoord : ∀ i : ι, Continuous fun σ : E => inner ℝ (b i) σ := fun i =>
    continuous_const.inner continuous_id
  have hle : ∀ (i : ι) (σ : E), inner ℝ (b i) σ ^ 2 ≤ ‖σ‖ ^ 2 := fun i σ => by
    have h := abs_real_inner_le_norm (b i) σ
    rw [b.orthonormal.1 i, one_mul] at h
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
  have hcsq : ∀ᵐ d ∂P, ∀ i, Integrable (fun σ : E => inner ℝ (b i) σ ^ 2) (G d) :=
    hsq.mono fun d h i => h.mono' ((hcoord i).pow 2).aestronglyMeasurable (ae_of_all _ fun σ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hle i σ)
  have hi2 : ∀ i, Integrable (fun d => ∫ σ, inner ℝ (b i) σ ^ 2 ∂(G d)) P := fun i =>
    hint.mono' (hm2 i) (by
      filter_upwards [hsq, hcsq] with d h1 h2
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
      exact integral_mono (h2 i) h1 fun σ => hle i σ)
  have hi1 : ∀ i, Integrable (fun d => (∫ σ, inner ℝ (b i) σ ∂(G d)) ^ 2) P := fun i =>
    (hi2 i).mono' ((hm1 i).pow 2) (by
      filter_upwards [hG, hcsq] with d _ h2
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      simpa only [Real.norm_eq_abs, sq_abs] using sq_norm_integral_le_integral_sq_norm
        ((memLp_two_iff_integrable_sq (hcoord i).aestronglyMeasurable).2 (h2 i)))
  have hcard : (Fintype.card ι : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Fintype.card_pos_iff.2 ⟨i₀⟩).ne'
  constructor
  · have h1 : ∀ᵐ d ∂P, ∫ σ, (Fintype.card ι : ℝ)⁻¹ * ‖σ‖ ^ 2 ∂(G d) =
        (Fintype.card ι : ℝ)⁻¹ * ∑ i, ∫ σ, inner ℝ (b i) σ ^ 2 ∂(G d) := hcsq.mono fun d h => by
      rw [integral_const_mul, ← integral_finsetSum _ fun i _ => h i]
      simp only [b.sum_sq_inner_right]
    rw [integral_congr_ae h1, integral_const_mul, integral_finsetSum _ fun i _ => hi2 i,
      Finset.sum_congr rfl fun i _ => hs2 i,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ hcard]
  · rw [integral_const_mul, integral_finsetSum _ fun i _ => hi1 i,
      Finset.sum_congr rfl fun i _ => hs1 i,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ hcard]

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
  classical
  have e : ∀ (i : ι) (σ : EuclideanSpace ℝ ι),
      inner ℝ (EuclideanSpace.basisFun ι ℝ i) σ = σ i := fun i σ => by
    simp [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  have hcoord : ∀ i : ι, Measurable fun σ : EuclideanSpace ℝ ι => σ i := fun i =>
    (PiLp.continuous_apply 2 (fun _ : ι => ℝ) i).measurable
  have h := integral_integral_inv_card_mul_sq_norm_of_exchangeable_orthonormalBasis
    (EuclideanSpace.basisFun ι ℝ) (P := P) (G := G) (ae_of_all _ fun _ => inferInstance)
    (fun i => by simpa only [e] using (hGm _ (hcoord i)).aestronglyMeasurable)
    (fun i => by simpa only [e] using (hGm _ ((hcoord i).pow_const 2)).aestronglyMeasurable)
    (ae_of_all _ hsq) hint i₀
    (fun i => by simpa only [e] using hsymm i (fun x => x ^ 2) fun y => y)
    (fun i => by simpa only [e] using hsymm i (fun x => x) fun y => y ^ 2)
  simpa only [e] using h

end MeasureTheory
