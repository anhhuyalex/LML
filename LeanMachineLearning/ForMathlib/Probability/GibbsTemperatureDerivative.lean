/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsLogPartition
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The inverse-temperature derivative of the expected free energy

For the energy `β ∑ₖ gₖ Xₖ` with i.i.d. standard Gaussian `gₖ`, the derivative of
`β ↦ 𝔼 log ∫ e^{β ∑ gₖ Xₖ} dμ` is `β ∑ₖ 𝔼 (⟨Xₖ²⟩ - ⟨Xₖ⟩²)`: differentiate the log-partition function
(`hasDerivAt_integral_log_partition_path`) and integrate by parts in each `gₖ`
(`integral_mul_gibbs_ratio_eq_sum`).  This is the computation of
`∂p_N/∂β` in the proof of Theorem 1.12.3 of Talagrand's book.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped BigOperators

namespace MeasureTheory

variable {α K : Type*} [MeasurableSpace α] [Fintype K] [DecidableEq K] {μ : Measure α}
  [IsFiniteMeasure μ] [NeZero μ] {X : K → α → ℝ} {B : ℝ}

/-- **Temperature derivative of the expected free energy.**  For a family `g` of i.i.d. standard
Gaussians and bounded measurable features `Xₖ`,
`d/db 𝔼 log ∫ e^{b ∑ gₖ Xₖ} dμ = b ∑ₖ 𝔼 (⟨Xₖ²⟩_b - ⟨Xₖ⟩_b²)`, where `⟨·⟩_b` is the Gibbs average
for the energy `b ∑ gₖ Xₖ`. -/
theorem hasDerivAt_integral_log_partition_temperature {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {g : K → Ω → ℝ}
    (hX : ∀ k, Measurable (X k)) (hB : 0 ≤ B) (hXb : ∀ k a, |X k a| ≤ B)
    (hg : HasGaussianLaw (fun ω k => g k ω) P) (hgm : ∀ k, Measurable (g k))
    (hmean : ∀ k, ∫ ω, g k ω ∂P = 0)
    (hcov : ∀ i l, ∫ ω, g i ω * g l ω ∂P = if i = l then 1 else 0) (b : ℝ) :
    HasDerivAt (fun s => ∫ ω, Real.log (∫ a, Real.exp (∑ k, g k ω * (s * X k a)) ∂μ) ∂P)
      (b * ∑ k, ∫ ω,
        ((∫ a, X k a ^ 2 * Real.exp (∑ l, g l ω * (b * X l a)) ∂μ) /
            ∫ a, Real.exp (∑ l, g l ω * (b * X l a)) ∂μ -
          ((∫ a, X k a * Real.exp (∑ l, g l ω * (b * X l a)) ∂μ) /
            ∫ a, Real.exp (∑ l, g l ω * (b * X l a)) ∂μ) ^ 2) ∂P) b := by
  classical
  have hXb' : ∀ k a, |b * X k a| ≤ |b| * B := fun k a => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hXb k a) (abs_nonneg _)
  have hXm' : ∀ k, Measurable fun a => b * X k a := fun k => (hX k).const_mul b
  -- the pointwise Gibbs ratio
  set R : (α → ℝ) → (K → ℝ) → ℝ := fun Y z =>
    (∫ a, Y a * Real.exp (0 + ∑ k, z k * (b * X k a)) ∂μ) /
      ∫ a, Real.exp (0 + ∑ k, z k * (b * X k a)) ∂μ with hR
  -- the derivative of the log-partition function along the path `s ↦ s g`
  have hgi : ∀ k, Integrable (g k) P := fun k => (hg.eval k).integrable
  have hd := hasDerivAt_integral_log_partition_path (μ := μ) (D := fun _ => (0 : ℝ)) (X := X)
    (B := B) (Eb := 0) (P := P) measurable_const hX hB (fun _ => by simp) hXb
    (z := fun s ω k => s * g k ω) (z' := fun _ ω k => g k ω) (t := b) (δ := 1) one_pos
    (fun ω s _ => hasDerivAt_pi.2 fun k => by simpa using (hasDerivAt_id s).mul_const (g k ω))
    (fun s => measurable_pi_iff.2 fun k => (hgm k).const_mul s) (measurable_pi_iff.2 hgm)
    (fun l => (hgi l).const_mul b) (g := fun ω => ∑ k, |g k ω|)
    (integrable_finsetSum _ fun k _ => (hgi k).abs)
    (fun ω s _ l => Finset.single_le_sum (f := fun k => |g k ω|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ l))
  have hRlin : ∀ (Y : α → ℝ) (z : K → ℝ), R (fun a => b * Y a) z = b * R Y z := fun Y z => by
    simp only [hR]
    rw [mul_div_assoc', ← integral_const_mul]
    congr 2
    funext a
    ring
  have hIBP : ∀ i, ∫ ω, g i ω * R (X i) (fun k => g k ω) ∂P =
      b * ∫ ω, (R (fun a => X i a ^ 2) (fun k => g k ω) - R (X i) (fun k => g k ω) ^ 2) ∂P := by
    intro i
    have := integral_mul_gibbs_ratio_eq_sum (μ := μ) (D := fun _ => (0 : ℝ))
      (X := fun k a => b * X k a) (Y := X i) (B := |b| * B) (M := B) (Eb := 0) (P := P) (Z := g) R
      (fun Y z => rfl) hg hmean i measurable_const hXm' (hX i) (by positivity) hB
      (fun _ => by simp) hXb' (hXb i)
    rw [this]
    simp only [hcov, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have e : (fun a => X i a * (b * X i a)) = fun a => b * (X i a ^ 2) := by
      funext a; ring
    simp only [e, hRlin]
    ring
  have hexp : ∀ (c : ℝ) (ω : Ω) (a : α),
      0 + ∑ k, (c * g k ω) * X k a = 0 + ∑ k, g k ω * (c * X k a) := fun c ω a => by
    congr 1; exact Finset.sum_congr rfl fun k _ => by ring
  have hpt : ∀ ω, ∑ l, g l ω * ((∫ a, X l a * Real.exp (0 + ∑ k, (b * g k ω) * X k a) ∂μ) /
      ∫ a, Real.exp (0 + ∑ k, (b * g k ω) * X k a) ∂μ) =
      ∑ l, g l ω * R (X l) (fun k => g k ω) := fun ω => by
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [hR, hexp]
  have hRb : ∀ (Y : α → ℝ) (M : ℝ), (∀ a, |Y a| ≤ M) → ∀ z, |R Y z| ≤ M := fun Y M hY z => by
    have := abs_gibbs_ratio_le (μ := μ) (D := fun _ => (0 : ℝ)) (X := fun k a => b * X k a)
      (Eb := 0) (B := |b| * B) measurable_const hXm' (fun _ => by simp) hXb' hY z
    simpa [hR] using this
  have hRc : ∀ (Y : α → ℝ) (M : ℝ), Measurable Y → 0 ≤ M → (∀ a, |Y a| ≤ M) →
      Continuous (R Y) := fun Y M hY hM hYb =>
    continuous_gibbs_ratio_linear (μ := μ) (D := fun _ => (0 : ℝ)) (X := fun k a => b * X k a)
      (Eb := 0) (B := |b| * B) R (fun Y z => rfl) measurable_const hXm' hY (by positivity) hM
      (fun _ => by simp) hXb' hYb
  have hint : ∀ i, Integrable (fun ω => g i ω * R (X i) (fun k => g k ω)) P := fun i => by
    refine ((hgi i).norm.mul_const B).mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact ((hgm i).mul ((hRc (X i) B (hX i) hB (hXb i)).measurable.comp
        (measurable_pi_iff.2 hgm))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hRb (X i) B (hXb i) _) (abs_nonneg _)
  have hR0 : ∀ (Y : α → ℝ) (ω : Ω), R Y (fun k => g k ω) =
      (∫ a, Y a * Real.exp (∑ l, g l ω * (b * X l a)) ∂μ) /
        ∫ a, Real.exp (∑ l, g l ω * (b * X l a)) ∂μ := fun Y ω => by
    simp only [hR, zero_add]
  have hfun : (fun s => ∫ ω, Real.log (∫ a, Real.exp (∑ k, g k ω * (s * X k a)) ∂μ) ∂P) =
      fun s => ∫ ω, Real.log (∫ a, Real.exp (0 + ∑ k, (s * g k ω) * X k a) ∂μ) ∂P := by
    funext s
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [zero_add]
    congr 2
    funext a
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hfun]
  refine hd.congr_deriv ?_
  simp only [hpt]
  rw [integral_finsetSum Finset.univ fun l _ => hint l]
  simp only [hIBP]
  rw [← Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [hR0]

end MeasureTheory
