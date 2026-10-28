/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.AddPowEstimates

/-! # Lemmas about sub-Gaussian random variables
-/

@[expose] public section

open MeasureTheory Real
open scoped ENNReal NNReal

namespace ProbabilityTheory

namespace HasCondSubgaussianMGF

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {hm : m ≤ mΩ} [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}

lemma ae_trim_condExp_exp_sub_le_one (h : HasCondSubgaussianMGF m hm X c μ) (t : ℝ) :
    ∀ᵐ ω' ∂(μ.trim hm), (μ[fun ω ↦ exp (t * X ω - c * t ^ 2 / 2)|m]) ω' ≤ 1 := by
  have h_le : ∀ᵐ ω' ∂(μ.trim hm), μ[fun ω ↦ exp (t * X ω)|m] ω' ≤ exp (c * t ^ 2 / 2) :=
    h.ae_trim_condExp_le t
  have h_eq : μ[fun ω ↦ exp (t * X ω) / exp (c * t ^ 2 / 2)|m] =ᵐ[μ.trim hm]
      fun ω ↦ μ[fun ω ↦ exp (t * X ω)|m] ω / exp (c * t ^ 2 / 2) := by
    refine ae_eq_trim_of_measurable _ ?_ ?_ ?_
    · exact stronglyMeasurable_condExp.measurable
    · refine Measurable.div_const ?_ _
      exact stronglyMeasurable_condExp.measurable
    simp_rw [div_eq_inv_mul]
    refine condExp_mul_of_stronglyMeasurable_left ?_ ?_ ?_
    · fun_prop
    · refine Integrable.const_mul ?_ _
      exact h.integrable_exp_mul _
    · exact h.integrable_exp_mul _
  filter_upwards [h_le, h_eq] with ω hω_le hω_eq
  simp_rw [exp_sub, hω_eq]
  rwa [div_le_one (by positivity)]

lemma ae_condExp_exp_sub_le_one (h : HasCondSubgaussianMGF m hm X c μ) (t : ℝ) :
    ∀ᵐ ω' ∂μ, (μ[fun ω ↦ exp (t * X ω - c * t ^ 2 / 2)|m]) ω' ≤ 1 :=
  ae_of_ae_trim hm (h.ae_trim_condExp_exp_sub_le_one t)

lemma memLp_exp_mul_sub (h : HasCondSubgaussianMGF m hm X c μ) (t : ℝ) (p : ℝ≥0) :
    MemLp (fun ω ↦ exp (t * X ω - c * t ^ 2 / 2)) p μ := by
  have h_lp := h.memLp_exp_mul t p
  simp_rw [sub_eq_add_neg, exp_add]
  exact h_lp.mul_const _

lemma integrable_exp_mul_sub (h : HasCondSubgaussianMGF m hm X c μ) (t : ℝ) :
    Integrable (fun ω ↦ exp (t * X ω - c * t ^ 2 / 2)) μ := by
  have h_int := h.integrable_exp_mul t
  simp_rw [exp_sub]
  exact h_int.div_const _

end HasCondSubgaussianMGF

namespace HasSubgaussianMGF

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X Y : Ω → ℝ} {c cX cY : ℝ≥0}

/-- Chernoff bound on the left tail of a sub-Gaussian random variable. -/
lemma measure_le_le (h : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | X ω ≤ -ε} ≤ exp (-ε ^ 2 / (2 * c)) := by
  simp_rw [le_neg (b := ε), ← Pi.neg_apply]
  exact h.neg.measure_ge_le hε

/-- Two-sided Chernoff bound for a sub-Gaussian random variable:
`ℙ(ε ≤ |X|) ≤ 2 exp (-ε² / (2c))`. -/
lemma measureReal_abs_ge_le (h : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |X ω|} ≤ 2 * exp (-ε ^ 2 / (2 * c)) := by
  have : IsFiniteMeasure μ := by simpa [integrable_const_iff] using h.integrable_exp_mul 0
  have hset : {ω | ε ≤ |X ω|} ⊆ {ω | ε ≤ X ω} ∪ {ω | X ω ≤ -ε} := fun ω (hω : ε ≤ |X ω|) => by
    rcases le_abs.1 hω with h | h
    · exact Or.inl h
    · exact Or.inr (show X ω ≤ -ε by linarith)
  refine (measureReal_mono hset).trans ((measureReal_union_le _ _).trans ?_)
  linarith [h.measure_ge_le hε, h.measure_le_le hε]

/-- **Hoeffding inequality** for sub-Gaussian random variables. -/
lemma measure_sum_le_le_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {c : ι → ℝ≥0}
    {s : Finset ι} (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ -ε} ≤ exp (-ε ^ 2 / (2 * ∑ i ∈ s, c i)) := by
  simp_rw [le_neg (b := ε), ← Finset.sum_neg_distrib, ← Pi.neg_apply (f := X _),
    ← Pi.neg_apply (f := X)]
  refine measure_sum_ge_le_of_iIndepFun (X := -X) (μ := μ) ?_ ?_ hε
  · exact h_indep.comp _ (fun _ ↦ measurable_neg)
  · exact fun i hi ↦ (h_subG i hi).neg

/-- **Hoeffding inequality** for sub-Gaussian random variables. -/
lemma measure_sum_range_le_le_of_iIndepFun {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ℝ≥0}
    {n : ℕ} (h_subG : ∀ i < n, HasSubgaussianMGF (X i) c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ∑ i ∈ Finset.range n, X i ω ≤ -ε} ≤ exp (-ε ^ 2 / (2 * n * c)) := by
  simp_rw [le_neg (b := ε), ← Finset.sum_neg_distrib, ← Pi.neg_apply (f := X _),
    ← Pi.neg_apply (f := X)]
  refine measure_sum_range_ge_le_of_iIndepFun (X := -X) (μ := μ) ?_ ?_ hε
  · exact h_indep.comp _ (fun _ ↦ measurable_neg)
  · exact fun i hi ↦ (h_subG i hi).neg

section Sum

variable {ι ι' : Type*} {X : ι → Ω → ℝ} {cX : ι → ℝ≥0} {s : Finset ι}
  {Y : ι' → Ω → ℝ} {cY : ι' → ℝ≥0} {t : Finset ι'}

lemma measure_sum_le_sum_le [IsFiniteMeasure μ]
    (hX_indep : iIndepFun X μ) (hY_indep : iIndepFun Y μ)
    (hX_subG : ∀ i ∈ s, HasSubgaussianMGF (fun ω ↦ X i ω - μ[X i]) (cX i) μ)
    (hY_subG : ∀ j ∈ t, HasSubgaussianMGF (fun ω ↦ Y j ω - μ[Y j]) (cY j) μ)
    (h_indep_sum : IndepFun (fun ω ↦ ∑ i ∈ s, X i ω) (fun ω ↦ ∑ j ∈ t, Y j ω) μ)
    (h_le : ∑ j ∈ t, μ[Y j] ≤ ∑ i ∈ s, μ[X i]) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ ∑ j ∈ t, Y j ω}
      ≤ exp (- (∑ j ∈ t, μ[Y j] - ∑ i ∈ s, μ[X i]) ^ 2
        / (2 * (∑ i ∈ s, cX i + ∑ j ∈ t, cY j))) := by
  have hX_int i (his : i ∈ s) : Integrable (X i) μ := by
    have h_int := (hX_subG i his).integrable
    simp_rw [sub_eq_add_neg, integrable_add_const_iff] at h_int
    exact h_int
  have hY_int j (his : j ∈ t) : Integrable (Y j) μ := by
    have h_int := (hY_subG j his).integrable
    simp_rw [sub_eq_add_neg, integrable_add_const_iff] at h_int
    exact h_int
  refine (measureReal_le_le_exp
    (cX := ∑ i ∈ s, cX i) (cY := ∑ j ∈ t, cY j) ?_ ?_ h_indep_sum ?_).trans_eq ?_
  · suffices HasSubgaussianMGF (fun ω ↦ ∑ i ∈ s, (X i ω - μ[X i])) (∑ i ∈ s, cX i) μ by
      convert this
      rw [integral_finsetSum _ hX_int, Finset.sum_sub_distrib]
    refine sum_of_iIndepFun ?_ hX_subG
    exact hX_indep.comp (g := fun i x ↦ x - μ[X i]) (by fun_prop)
  · suffices HasSubgaussianMGF (fun ω ↦ ∑ j ∈ t, (Y j ω - μ[Y j])) (∑ j ∈ t, cY j) μ by
      convert this
      rw [integral_finsetSum _ hY_int, Finset.sum_sub_distrib]
    refine sum_of_iIndepFun ?_ hY_subG
    exact hY_indep.comp (g := fun i x ↦ x - μ[Y i]) (by fun_prop)
  · rwa [integral_finsetSum _ hX_int, integral_finsetSum _ hY_int]
  · congr
    · rw [integral_finsetSum _ hY_int]
    · rw [integral_finsetSum _ hX_int]

lemma measure_sum_le_sum_le' [IsFiniteMeasure μ]
    (hX_indep : iIndepFun X μ) (hY_indep : iIndepFun Y μ)
    (hX_subG : ∀ i ∈ s, HasSubgaussianMGF (fun ω ↦ X i ω - μ[X i]) (cX i) μ)
    (hY_subG : ∀ j ∈ t, HasSubgaussianMGF (fun ω ↦ Y j ω - μ[Y j]) (cY j) μ)
    (h_indep_sum : IndepFun (fun ω ↦ (X · ω)) (fun ω ↦ (Y · ω)) μ)
    (h_le : ∑ j ∈ t, μ[Y j] ≤ ∑ i ∈ s, μ[X i]) :
    μ.real {ω | ∑ i ∈ s, X i ω ≤ ∑ j ∈ t, Y j ω}
      ≤ Real.exp (- (∑ j ∈ t, μ[Y j] - ∑ i ∈ s, μ[X i]) ^ 2
        / (2 * (∑ i ∈ s, cX i + ∑ j ∈ t, cY j))) := by
  refine measure_sum_le_sum_le hX_indep hY_indep hX_subG hY_subG ?_ h_le
  exact h_indep_sum.comp (φ := fun p ↦ ∑ i ∈ s, p i) (ψ := fun p ↦ ∑ j ∈ t, p j)
    (by fun_prop) (by fun_prop)

end Sum

end HasSubgaussianMGF

section Moments

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Exponential moments of `|X|`.**  If `X` is measurable and sub-Gaussian with parameter `c`,
then `exp (t |X|)` is integrable and `𝔼 exp (t |X|) ≤ 2 exp (c t² / 2)`. -/
theorem HasSubgaussianMGF.integral_exp_abs_mul_le {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (hX : Measurable X) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * |X ω|)) μ ∧
      ∫ ω, Real.exp (t * |X ω|) ∂μ ≤ 2 * Real.exp (c * t ^ 2 / 2) := by
  have hle : ∀ ω, Real.exp (t * |X ω|) ≤ Real.exp (t * X ω) + Real.exp ((-t) * X ω) := fun ω => by
    rcases le_total 0 (X ω) with hx | hx
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · rw [abs_of_nonpos hx, show t * -X ω = (-t) * X ω by ring]
      exact le_add_of_nonneg_left (Real.exp_pos _).le
  have hint : Integrable (fun ω => Real.exp (t * X ω) + Real.exp ((-t) * X ω)) μ :=
    (h.integrable_exp_mul t).add (h.integrable_exp_mul (-t))
  have hI : Integrable (fun ω => Real.exp (t * |X ω|)) μ :=
    hint.mono' (by fun_prop) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hle ω)
  refine ⟨hI, (integral_mono hI hint hle).trans ?_⟩
  rw [integral_add (h.integrable_exp_mul t) (h.integrable_exp_mul (-t))]
  have h1 := h.mgf_le t
  have h2 := h.mgf_le (-t)
  rw [mgf] at h1 h2
  rw [neg_sq] at h2
  linarith

/-- A sub-Gaussian variable is integrable. -/
theorem HasSubgaussianMGF.integrable_of_measurable {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (hX : Measurable X) : Integrable X μ := by
  refine ((h.integral_exp_abs_mul_le hX 1).1).mono' hX.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, one_mul]
  linarith [Real.add_one_le_exp |X ω|, abs_nonneg (X ω)]

/-- `cosh X` is integrable for a sub-Gaussian `X`. -/
theorem HasSubgaussianMGF.integrable_two_cosh {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) :
    Integrable (fun ω => 2 * Real.cosh (X ω)) μ := by
  have := (h.integrable_exp_mul 1).add (h.integrable_exp_mul (-1))
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply, one_mul, neg_mul, Real.cosh_eq]
  ring

/-- `𝔼 2 cosh X ≤ 2 exp (c / 2)` for a sub-Gaussian `X` with parameter `c`. -/
theorem HasSubgaussianMGF.integral_two_cosh_le {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) :
    ∫ ω, 2 * Real.cosh (X ω) ∂μ ≤ 2 * Real.exp (c / 2) := by
  have h1 := h.mgf_le 1
  have h2 := h.mgf_le (-1)
  rw [mgf] at h1 h2
  have : ∫ ω, 2 * Real.cosh (X ω) ∂μ =
      (∫ ω, Real.exp (1 * X ω) ∂μ) + ∫ ω, Real.exp ((-1) * X ω) ∂μ := by
    rw [← integral_add (h.integrable_exp_mul 1) (h.integrable_exp_mul (-1))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [one_mul, neg_mul, Real.cosh_eq]
    ring
  rw [this]
  norm_num at h1 h2 ⊢
  linarith

/-- `𝔼 exp X ≤ exp (c / 2)` for a sub-Gaussian `X` with parameter `c`. -/
theorem HasSubgaussianMGF.integral_exp_le {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) :
    ∫ ω, Real.exp (X ω) ∂μ ≤ Real.exp (c / 2) := by
  have := h.mgf_le 1
  rw [mgf] at this
  simpa using this

/-- **Moment bounds for sub-Gaussian variables.** For `X` sub-Gaussian with parameter `c`,
any exponent `k` and any scale parameter `w > 0`: `w^k 𝔼 |X|^k ≤ 2 k! exp (c w² / 2)`. -/
theorem HasSubgaussianMGF.integral_pow_abs_le {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) (hX : Measurable X) (k : ℕ) {w : ℝ} (hw : 0 < w) :
    Integrable (fun ω => |X ω| ^ k) μ ∧
      w ^ k * ∫ ω, |X ω| ^ k ∂μ ≤ 2 * Nat.factorial k * Real.exp (c * w ^ 2 / 2) := by
  obtain ⟨hint, hexp⟩ := h.integral_exp_abs_mul_le hX w
  have hpt : ∀ ω, w ^ k * |X ω| ^ k ≤ (Nat.factorial k : ℝ) * Real.exp (w * |X ω|) := fun ω => by
    rw [← mul_pow]
    exact Real.pow_le_factorial_mul_exp (mul_nonneg hw.le (abs_nonneg _)) k
  have hmeas : Measurable fun ω => |X ω| ^ k :=
    (continuous_abs.measurable.comp hX).pow_const k
  have hint' : Integrable (fun ω => w ^ k * |X ω| ^ k) μ :=
    Integrable.mono' (hint.const_mul (Nat.factorial k : ℝ))
      (hmeas.const_mul _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hpt ω)
  refine ⟨by simpa [mul_assoc, hw.ne'] using hint'.const_mul ((w ^ k)⁻¹), ?_⟩
  rw [← integral_const_mul]
  refine (integral_mono hint' (hint.const_mul (Nat.factorial k : ℝ)) hpt).trans ?_
  rw [integral_const_mul]
  nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.factorial k)]

end Moments

end ProbabilityTheory
