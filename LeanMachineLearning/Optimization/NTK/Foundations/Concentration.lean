/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Generic Gaussian and probability-measure lemmas

Network-independent facts used by the NTK initialization development:

* moments of the standard real Gaussian `gaussianReal 0 1` (`x ↦ x²` and `x ↦ x⁴` integrable,
  `E[x²] = 1`, `x ↦ x²` in `MemLp 2`);
* sub-Gaussian moment-generating-function bounds for `gaussianReal 0 1` and the resulting
  two-sided Chernoff tail `P(|X| ≥ ε) ≤ 2 exp(-ε²/2)`;
* complement/union-bound algebra for `μ.real` on a probability measure
  (`measureReal_inter_ge_of_ge`, `measureReal_compl_inter_le`,
  `one_sub_le_measureReal_of_measureReal_compl_le`).

They were extracted from `NTK.Initialization.Setup`, which re-exports this module.
-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory

namespace NTK

/-- Hölder exponents `1/4 + 1/4 = 1/2`: bounds the `L²` norm of a product of two `L⁴` functions. -/
instance instHolderTripleFourFourTwo : ENNReal.HolderTriple 4 4 2 := ⟨by
  rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_inv_of_pos (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num⟩

/-- The square function is integrable with respect to the standard real Gaussian measure. -/
lemma integrable_sq_gaussianReal : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq
    (memLp_id_gaussianReal (2 : NNReal)).aestronglyMeasurable).1
  exact memLp_id_gaussianReal (2 : NNReal)

/-- The second moment of the standard real Gaussian measure is 1. -/
lemma integral_sq_gaussianReal : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := ProbabilityTheory.variance_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))
  rw [variance_eq_integral (X := id) measurable_id'.aemeasurable] at h
  simpa [id] using h

/-- The fourth power is integrable with respect to the standard real Gaussian measure. -/
lemma integrable_pow_four_gaussianReal :
    Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) := by
  have h := memLp_id_gaussianReal (4 : NNReal) (μ := 0) (v := 1)
  have hint := h.integrable_norm_rpow (by norm_num) (by norm_num)
  have heq : (fun x : ℝ => ‖id x‖ ^ (4 : ℝ)) = (fun x : ℝ => x ^ 4) := by
    ext x
    simp only [id, Real.norm_eq_abs]
    have h1 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
    rw [h1, Real.rpow_natCast]
    have h2 : |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
    have h3 : x ^ 4 = (x ^ 2) ^ 2 := by ring
    rw [h2, sq_abs, ← h3]
  have h_exp : ((4 : NNReal) : ENNReal).toReal = 4 := by rfl
  rw [h_exp] at hint
  rw [heq] at hint
  exact hint

/-- The square function is square-integrable (in `MemLp 2`) with respect to the standard
real Gaussian measure. -/
lemma memLp_sq_gaussianReal_two :
    MemLp (fun x : ℝ => x ^ 2) 2 (gaussianReal 0 1) := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  have heq : (fun x : ℝ => (x ^ 2) ^ 2) = (fun x : ℝ => x ^ 4) := by
    ext x; ring
  rw [heq]
  exact integrable_pow_four_gaussianReal

/-- The standard Gaussian has a sub-Gaussian moment-generating function with parameter `1`. -/
lemma hasSubgaussianMGF_id_gaussianReal_zero_one :
    ProbabilityTheory.HasSubgaussianMGF id (1 : NNReal) (gaussianReal 0 1) where
  integrable_exp_mul := integrable_exp_mul_gaussianReal
  mgf_le t := by rw [mgf_id_gaussianReal]; simp

/-- Negating a standard Gaussian is still sub-Gaussian with the same parameter (used for the
two-sided/absolute-value tail bound below). -/
lemma hasSubgaussianMGF_neg_id_gaussianReal_zero_one :
    ProbabilityTheory.HasSubgaussianMGF (fun x => -x) (1 : NNReal) (gaussianReal 0 1) :=
  hasSubgaussianMGF_id_gaussianReal_zero_one.neg

/-- Two-sided Chernoff tail bound for a standard Gaussian: `P(|X| ≥ ε) ≤ 2 exp(-ε²/2)`. -/
lemma prob_abs_gaussianReal_ge_le (ε : ℝ) (hε : 0 ≤ ε) :
    (gaussianReal 0 1).real {x : ℝ | ε ≤ |x|} ≤ 2 * Real.exp (-ε ^ 2 / 2) := by
  have hset : {x : ℝ | ε ≤ |x|} = {x : ℝ | ε ≤ x} ∪ {x : ℝ | ε ≤ -x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  rw [hset]
  have h1 := hasSubgaussianMGF_id_gaussianReal_zero_one.measure_ge_le hε
  have h2 := hasSubgaussianMGF_neg_id_gaussianReal_zero_one.measure_ge_le hε
  simp only [id] at h1
  have hle := measureReal_union_le (μ := gaussianReal 0 1) {x : ℝ | ε ≤ x} {x : ℝ | ε ≤ -x}
  have hcalc : Real.exp (-ε ^ 2 / (2 * (1:NNReal))) = Real.exp (-ε ^ 2 / 2) := by norm_num
  rw [hcalc] at h1 h2
  calc
    (gaussianReal 0 1).real ({x : ℝ | ε ≤ x} ∪ {x : ℝ | ε ≤ -x}) ≤
        (gaussianReal 0 1).real {x : ℝ | ε ≤ x} + (gaussianReal 0 1).real {x : ℝ | ε ≤ -x} := hle
    _ ≤ Real.exp (-ε ^ 2 / 2) + Real.exp (-ε ^ 2 / 2) := add_le_add h1 h2
    _ = 2 * Real.exp (-ε ^ 2 / 2) := by ring

/-- **Generic, reusable union-bound-for-complements.** Two events each of probability `≥ 1 - δ`
on the same probability measure intersect in an event of probability `≥ 1 - δ₁ - δ₂`. Used by
kernel-freeze (`NTK.Training.TwoLayer.KernelFreeze`) to combine the Jacobian-norm event with the
entrywise-readout event, but stated with no reference to the NTK setup so it can be reused for
any future combination of independent high-probability events. -/
theorem measureReal_inter_ge_of_ge {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {δ₁ δ₂ : ℝ} (hA' : μ.real A ≥ 1 - δ₁) (hB' : μ.real B ≥ 1 - δ₂) :
    μ.real (A ∩ B) ≥ 1 - δ₁ - δ₂ := by
  have hcompl : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := Set.compl_inter A B
  have h1 : μ.real ((A ∩ B)ᶜ) = 1 - μ.real (A ∩ B) := probReal_compl_eq_one_sub (hA.inter hB)
  have h2 : μ.real (Aᶜ ∪ Bᶜ) ≤ μ.real Aᶜ + μ.real Bᶜ := measureReal_union_le Aᶜ Bᶜ
  have h3 : μ.real Aᶜ = 1 - μ.real A := probReal_compl_eq_one_sub hA
  have h4 : μ.real Bᶜ = 1 - μ.real B := probReal_compl_eq_one_sub hB
  rw [hcompl] at h1
  linarith [h1, h2, h3, h4]

/-- The complement of an intersection has measure at most the sum of the complements' measures.
No measurability is needed. -/
theorem measureReal_compl_inter_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (A B : Set α) :
    μ.real (A ∩ B)ᶜ ≤ μ.real Aᶜ + μ.real Bᶜ := by
  rw [Set.compl_inter]
  exact measureReal_union_le _ _

/-- On a probability measure, `1 - μ Sᶜ ≤ μ S` for an arbitrary (possibly non-measurable) `S`. -/
theorem one_sub_le_measureReal_of_measureReal_compl_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {S : Set α} {c : ℝ} (h : μ.real Sᶜ ≤ c) :
    1 - c ≤ μ.real S := by
  have h1 := measureReal_union_le (μ := μ) S Sᶜ
  rw [Set.union_compl_self] at h1
  have h2 : μ.real Set.univ = 1 := by simp
  linarith

end NTK

end
