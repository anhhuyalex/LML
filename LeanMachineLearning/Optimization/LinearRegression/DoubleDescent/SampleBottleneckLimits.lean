/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.ProdBound
public import LeanMachineLearning.ForMathlib.Topology.Instances.ENNReal.Lemmas
public import LeanMachineLearning.ForMathlib.Topology.Order.Sandwich
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.SampleBottleneckDecomposition
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.SampleBottleneckFixedDesign
public import LeanMachineLearning.Optimization.NTK.Initialization.ResidualConcentration

/-!
# Probabilistic limits in the sample-bottleneck regime (Milestone 7g)

Random-feature regression with `X ∈ ℝ^{m×n₀}` and `V ∈ ℝ^{n×n₀}` independent standard Gaussian
matrices (so `S = Vᵀ ∈ ℝ^{n₀×n}`), in the regime `m < min {n₀, n}`, `Z = X S`, `Z† = Zᵀ (Z Zᵀ)⁻¹`,
`M = S Z†` ([Bach, 2024]; [Hastie et al., 2022]; [Belkin et al., 2019]).

By `SampleBottleneckDecomposition.lean` the variance trace splits as
`Tr (Mᵀ M) = Tr ((X Xᵀ)⁻¹) + Tr ((Z† Z†ᵀ) (Sᵀ Pᗮ S))`, `Pᗮ = 1 - P_X`. The first term is the
inverse-Wishart trace of `Xᵀ` (`tendsto_measure_trace_inv_gram_deviation`). The second is a
Gaussian trace form in `V Pᗮ`, whose weight `Z† Z†ᵀ` depends on `V` only through `V P` and `X`;
the conditional Chebyshev bound `conditional_traceForm_chebyshev` (no basis of the null space and
no independence statement are needed) shows it is `(n₀ - m) Tr ((Z Zᵀ)⁻¹)` up to `ε₃`, and for a
fixed design `Tr ((Z Zᵀ)⁻¹)` is `Tr ((X Xᵀ)⁻¹) / ν` up to a factor `1 ± η`, `ν = n - m + 1`
(`measure_sampleTrace_mem_le`).

* `measure_sampleVariance_sandwich_le`: the non-asymptotic sandwich of the variance trace with
  an explicit failure probability.
* `tendsto_measure_sampleVariance_deviation`: **the variance trace converges in probability to
  `(γ - 1)⁻¹ + (δ - 1)⁻¹`** along `n₀ / m → γ > 1`, `n / m → δ > 1`.
-/

@[expose]
public section

namespace LinearRegression.DoubleDescent

open MeasureTheory ProbabilityTheory Matrix NTK Filter Topology
open scoped Matrix ENNReal

section Algebra

variable {m n n₀ : ℕ}

/-- Rotation of the row-space projector through `V P`: `X (V P)ᵀ = X Vᵀ`. -/
theorem mul_transpose_mul_gramProjector_transpose (X : Matrix (Fin m) (Fin n₀) ℝ)
    (V : Matrix (Fin n) (Fin n₀) ℝ) (hX : IsUnit (X * Xᵀ).det) :
    X * (V * gramProjector Xᵀ)ᵀ = X * Vᵀ := by
  rw [Matrix.transpose_mul, gramProjector_transpose, ← Matrix.mul_assoc,
    mul_gramProjector_transpose X hX]

/-- For a symmetric `N`, `Tr (B N) = ∑ᵢⱼ Bᵢⱼ Nᵢⱼ`. -/
theorem trace_mul_eq_sum_of_symm {ι : Type*} [Fintype ι] (B N : Matrix ι ι ℝ) (hN : Nᵀ = N) :
    (B * N).trace = ∑ i, ∑ j, B i j * N i j := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := congrFun (congrFun hN j) i
  rw [Matrix.transpose_apply] at this
  rw [this]

/-- The residual trace form:
`Tr ((Z† Z†ᵀ) (Sᵀ (1 - P) S)) = ∑ᵢⱼ (Z† Z†ᵀ)ᵢⱼ ((V (1-P)) (V (1-P))ᵀ)ᵢⱼ`
for `S = Vᵀ`. -/
theorem trace_mul_residual_eq_sum (B : Matrix (Fin n) (Fin n) ℝ) (V : Matrix (Fin n) (Fin n₀) ℝ)
    (P : Matrix (Fin n₀) (Fin n₀) ℝ) (hP : IsStarProjection P) :
    (B * ((Vᵀ)ᵀ * (1 - P) * Vᵀ)).trace =
      ∑ i, ∑ j, B i j * (((V * (1 - P)) * (1 : Matrix (Fin n₀) (Fin n₀) ℝ) *
        (V * (1 - P))ᵀ : Matrix (Fin n) (Fin n) ℝ) i j) := by
  have hD : IsStarProjection (1 - P) := hP.one_sub
  have hDD : (1 - P)ᵀ * (1 - P) = 1 - P := by
    rw [hD.transpose_eq]; exact ((isStarProjection_matrix_real_iff _).1 hD).2
  have hN : (V * (1 - P)) * (1 : Matrix (Fin n₀) (Fin n₀) ℝ) * (V * (1 - P))ᵀ =
      (Vᵀ)ᵀ * (1 - P) * Vᵀ := by
    rw [Matrix.mul_one, Matrix.transpose_mul, Matrix.transpose_transpose]
    calc V * (1 - P) * ((1 - P)ᵀ * Vᵀ) = V * ((1 - P) * (1 - P)ᵀ) * Vᵀ := by
          simp only [Matrix.mul_assoc]
      _ = V * (1 - P) * Vᵀ := by
          rw [hD.transpose_eq]
          rw [show (1 - P) * (1 - P) = 1 - P by rwa [hD.transpose_eq] at hDD]
  rw [← hN]
  exact trace_mul_eq_sum_of_symm B _ (by simp [Matrix.transpose_mul, Matrix.mul_assoc])

end Algebra


section Variance

variable {m n n₀ : ℕ}

/-- Real arithmetic of the variance sandwich: from the three sandwiches of `T₁`, `τ` and `T₂` to
the sandwich of `T₁ + T₂`. -/
theorem variance_sandwich_arith {T₁ c₁ ε₁ τ T₂ ν η N ε₃ : ℝ} (hν : 0 < ν) (hη : 0 < η)
    (hη1 : η < 1) (hN : 0 ≤ N) (hT₁ : |T₁ - c₁| < ε₁) (hτlo : T₁ / (ν * (1 + η)) ≤ τ)
    (hτhi : τ ≤ T₁ / (ν * (1 - η))) (hT₂ : |T₂ - N * τ| < ε₃) :
    (c₁ - ε₁) * (1 + (N / ν) / (1 + η)) - ε₃ < T₁ + T₂ ∧
      T₁ + T₂ < (c₁ + ε₁) * (1 + (N / ν) / (1 - η)) + ε₃ := by
  obtain ⟨h1, h2⟩ := abs_lt.1 hT₁
  obtain ⟨h3, h4⟩ := abs_lt.1 hT₂
  have h1η : 0 < 1 - η := by linarith
  have hfl : 0 < 1 + (N / ν) / (1 + η) := by positivity
  have hfh : 0 < 1 + (N / ν) / (1 - η) := by positivity
  constructor
  · have e : N * (T₁ / (ν * (1 + η))) = T₁ * ((N / ν) / (1 + η)) := by
      field_simp
    have h5 : N * (T₁ / (ν * (1 + η))) ≤ N * τ := mul_le_mul_of_nonneg_left hτlo hN
    have h6 : (c₁ - ε₁) * (1 + (N / ν) / (1 + η)) < T₁ * (1 + (N / ν) / (1 + η)) :=
      mul_lt_mul_of_pos_right (by linarith) hfl
    nlinarith
  · have e : N * (T₁ / (ν * (1 - η))) = T₁ * ((N / ν) / (1 - η)) := by
      field_simp
    have h5 : N * τ ≤ N * (T₁ / (ν * (1 - η))) := mul_le_mul_of_nonneg_left hτhi hN
    have h6 : T₁ * (1 + (N / ν) / (1 - η)) < (c₁ + ε₁) * (1 + (N / ν) / (1 - η)) :=
      mul_lt_mul_of_pos_right (by linarith) hfh
    nlinarith

/-- **Non-asymptotic variance sandwich in the sample-bottleneck regime.**
Let `X` be an `m × n₀` and `V` an independent `n × n₀` Gaussian matrix, `S = Vᵀ`, `Z = X S`,
`m ≤ min {n, n₀}`, `ν = n - m + 1`, and `Var = Tr ((Z Zᵀ)⁻¹ (Z Sᵀ S Zᵀ) (Z Zᵀ)⁻¹)` the variance
trace. For `0 < η < 1`, `0 < ε₁ ≤ c₁`, `ε₃ > 0`, outside an event of probability at most
`2 ℙ (|Tr ((X Xᵀ)⁻¹) - c₁| ≥ ε₁) + 2 · 60 m / (η⁴ ν²) + 2 n₀ ((c₁+ε₁) / (ν (1-η)))² / ε₃²`,
`(c₁ - ε₁)(1 + λ/(1+η)) - ε₃ < Var < (c₁ + ε₁)(1 + λ/(1-η)) + ε₃` with `λ = (n₀ - m) / ν`. -/
theorem measure_sampleVariance_sandwich_le (hm : 0 < m) (hmn : m ≤ n) (hmn₀ : m ≤ n₀)
    {η ε₁ ε₃ c₁ : ℝ} (hη : 0 < η) (hη1 : η < 1) (hε₁c : ε₁ ≤ c₁) (hε₃ : 0 < ε₃)
    (Var : (Fin m → Fin n₀ → ℝ) × (Fin n → Fin n₀ → ℝ) → ℝ)
    (hVar : ∀ x, Var x = Matrix.trace
      (((Matrix.of x.1 * (Matrix.of x.2)ᵀ) * (Matrix.of x.1 * (Matrix.of x.2)ᵀ)ᵀ)⁻¹ *
        ((Matrix.of x.1 * (Matrix.of x.2)ᵀ) * ((Matrix.of x.2)ᵀᵀ * (Matrix.of x.2)ᵀ) *
          (Matrix.of x.1 * (Matrix.of x.2)ᵀ)ᵀ) *
        ((Matrix.of x.1 * (Matrix.of x.2)ᵀ) * (Matrix.of x.1 * (Matrix.of x.2)ᵀ)ᵀ)⁻¹)) :
    ((Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n₀ => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n₀ => gaussianReal 0 1))
        {x | ¬ ((c₁ - ε₁) * (1 + (((n₀ : ℝ) - m) / ((n - m + 1 : ℕ) : ℝ)) / (1 + η)) - ε₃ <
              Var x ∧
            Var x < (c₁ + ε₁) * (1 + (((n₀ : ℝ) - m) / ((n - m + 1 : ℕ) : ℝ)) / (1 - η)) + ε₃)} ≤
      2 * (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n₀ => gaussianReal 0 1)
          {a | ε₁ ≤ |((Matrix.of a * (Matrix.of a)ᵀ)⁻¹).trace - c₁|} +
        2 * ENNReal.ofReal ((m : ℝ) * (60 / (η ^ 4 * ((n - m + 1 : ℕ) : ℝ) ^ 2))) +
        ENNReal.ofReal (2 * (n₀ : ℝ) * ((c₁ + ε₁) / (((n - m + 1 : ℕ) : ℝ) * (1 - η))) ^ 2 /
          ε₃ ^ 2) := by
  set ν : ℝ := ((n - m + 1 : ℕ) : ℝ) with hνdef
  have hν : 0 < ν := by rw [hνdef]; positivity
  set μX := Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n₀ => gaussianReal 0 1 with hμX
  set μV := Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n₀ => gaussianReal 0 1 with hμV
  have hX1 : IsProbabilityMeasure μX := by rw [hμX]; infer_instance
  have hV1 : IsProbabilityMeasure μV := by rw [hμV]; infer_instance
  set T₁ : (Fin m → Fin n₀ → ℝ) → ℝ := fun a => ((Matrix.of a * (Matrix.of a)ᵀ)⁻¹).trace with hT₁
  set τ : (Fin m → Fin n₀ → ℝ) × (Fin n → Fin n₀ → ℝ) → ℝ := fun x =>
    (((Matrix.of x.1 * (Matrix.of x.2)ᵀ) * (Matrix.of x.1 * (Matrix.of x.2)ᵀ)ᵀ)⁻¹).trace with hτ
  have hmT₁ : Measurable T₁ := by
    refine measurable_matrix_trace ?_
    fun_prop
  have hmτ : Measurable τ := by
    refine measurable_matrix_trace ?_
    fun_prop
  have hmT₁' : Measurable fun x : (Fin m → Fin n₀ → ℝ) × (Fin n → Fin n₀ → ℝ) => T₁ x.1 :=
    hmT₁.comp measurable_fst
  set B1 : Set ((Fin m → Fin n₀ → ℝ) × (Fin n → Fin n₀ → ℝ)) :=
    Prod.fst ⁻¹' {a | ε₁ ≤ |T₁ a - c₁|} with hB1
  set B2 : Set ((Fin m → Fin n₀ → ℝ) × (Fin n → Fin n₀ → ℝ)) :=
    {x | 0 < T₁ x.1 ∧ ¬ (T₁ x.1 / (ν * (1 + η)) ≤ τ x ∧ τ x ≤ T₁ x.1 / (ν * (1 - η)))}
    with hB2
  have hmB1 : MeasurableSet B1 :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp (hmT₁'.sub measurable_const))
  have hmB2 : MeasurableSet B2 := by
    refine (measurableSet_lt measurable_const hmT₁').inter ?_
    refine MeasurableSet.compl ?_
    exact (measurableSet_le (hmT₁'.div_const _) hmτ).inter
      (measurableSet_le hmτ (hmT₁'.div_const _))
  have hB1μ : (μX.prod μV) B1 = μX {a | ε₁ ≤ |T₁ a - c₁|} := by
    rw [hB1]
    exact (measurePreserving_fst (μ := μX) (ν := μV)).measure_preimage
      (measurableSet_le measurable_const
        (continuous_abs.measurable.comp (hmT₁.sub measurable_const))).nullMeasurableSet
  have hB2μ : (μX.prod μV) B2 ≤ ENNReal.ofReal ((m : ℝ) * (60 / (η ^ 4 * ν ^ 2))) := by
    refine measure_prod_le_of_ae_section_le μX μV hmB2 (Filter.Eventually.of_forall fun a => ?_)
    by_cases ha : 0 < T₁ a
    · have hX : IsUnit (Matrix.of a * (Matrix.of a)ᵀ).det :=
        isUnit_det_of_trace_inv_ne_zero _ ha.ne'
      refine le_trans (measure_mono ?_) (measure_sampleTrace_mem_le hm hmn _ hX hη hη1)
      intro V hV
      simp only [Set.mem_preimage, hB2, Set.mem_ofPred_eq] at hV ⊢
      exact hV.2
    · have : Prod.mk a ⁻¹' B2 = ∅ := by
        ext V; simp only [Set.mem_preimage, hB2, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false]; exact fun h => ha h.1
      rw [this, measure_empty]; exact zero_le
  -- the conditional Chebyshev bound for the residual trace form
  set P : (Fin m → Fin n₀ → ℝ) → Matrix (Fin n₀) (Fin n₀) ℝ :=
    fun a => gramProjector (Matrix.of a)ᵀ with hP
  have hPs : ∀ a, IsStarProjection (P a) := fun a => isOrthogonalProjection_gramProjector_all _
  have hPm : Measurable P := measurable_gramProjector (Φ := fun a => (Matrix.of a)ᵀ) (by fun_prop)
  set Bf : Matrix (Fin n) (Fin n₀) ℝ × (Fin m → Fin n₀ → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
    fun y => ((Matrix.of y.2 * y.1ᵀ)ᵀ * ((Matrix.of y.2 * y.1ᵀ) * (Matrix.of y.2 * y.1ᵀ)ᵀ)⁻¹) *
      ((Matrix.of y.2 * y.1ᵀ)ᵀ * ((Matrix.of y.2 * y.1ᵀ) * (Matrix.of y.2 * y.1ᵀ)ᵀ)⁻¹)ᵀ with hBf
  have hBm : Measurable Bf := by
    simp only [hBf]
    fun_prop
  have hcond := conditional_traceForm_chebyshev μX n n₀ P hPs hPm
    (fun _ => (1 : Matrix (Fin n₀) (Fin n₀) ℝ)) measurable_const Bf hBm hε₃
  set C3 : Set ((Fin m → Fin n₀ → ℝ) × (Fin n → Fin n₀ → ℝ)) :=
    {q | ε₃ ≤ |∑ i, ∑ j, Bf (Matrix.of q.2 * P q.1, q.1) i j *
        ((Matrix.of q.2 * (1 - P q.1) * (1 : Matrix (Fin n₀) (Fin n₀) ℝ) *
          (Matrix.of q.2 * (1 - P q.1))ᵀ : Matrix (Fin n) (Fin n) ℝ) i j) -
      (Bf (Matrix.of q.2 * P q.1, q.1)).trace *
        ((1 - P q.1) * (1 : Matrix (Fin n₀) (Fin n₀) ℝ) * (1 - P q.1)).trace|} with hC3
  have hcond' : (μX.prod μV) C3 ≤ ∫⁻ q, min 1 (ENNReal.ofReal
      (2 * (∑ i, ∑ j, Bf (Matrix.of q.2 * P q.1, q.1) i j ^ 2) *
        (∑ k, ∑ l, (1 : Matrix (Fin n₀) (Fin n₀) ℝ) k l ^ 2) / ε₃ ^ 2)) ∂(μX.prod μV) := hcond
  -- the key pointwise facts off `B1 ∪ B2`
  have key : ∀ x : (Fin m → Fin n₀ → ℝ) × (Fin n → Fin n₀ → ℝ), x ∉ B1 → x ∉ B2 →
      (|T₁ x.1 - c₁| < ε₁ ∧ 0 < T₁ x.1 ∧
        T₁ x.1 / (ν * (1 + η)) ≤ τ x ∧ τ x ≤ T₁ x.1 / (ν * (1 - η)) ∧ 0 < τ x) := by
    intro x hx1 hx2
    simp only [hB1, Set.mem_preimage, Set.mem_ofPred_eq, not_le] at hx1
    have hT : 0 < T₁ x.1 := by linarith [(abs_lt.1 hx1).1]
    have hx2' : T₁ x.1 / (ν * (1 + η)) ≤ τ x ∧ τ x ≤ T₁ x.1 / (ν * (1 - η)) := by
      by_contra h
      exact hx2 ⟨hT, h⟩
    obtain ⟨hlo, hhi⟩ := hx2'
    refine ⟨hx1, hT, hlo, hhi, lt_of_lt_of_le ?_ hlo⟩
    positivity
  -- the integrated bound is small off `B1 ∪ B2`
  have hint : ∫⁻ q, min 1 (ENNReal.ofReal
      (2 * (∑ i, ∑ j, Bf (Matrix.of q.2 * P q.1, q.1) i j ^ 2) *
        (∑ k, ∑ l, (1 : Matrix (Fin n₀) (Fin n₀) ℝ) k l ^ 2) / ε₃ ^ 2)) ∂(μX.prod μV) ≤
      (μX.prod μV) B1 + (μX.prod μV) B2 +
        ENNReal.ofReal (2 * (n₀ : ℝ) * ((c₁ + ε₁) / (ν * (1 - η))) ^ 2 / ε₃ ^ 2) := by
    refine (lintegral_min_one_ofReal_le (μX.prod μV) (hmB1.union hmB2) (fun q hq => ?_)).trans
      (add_le_add_left (measure_union_le _ _) _)
    have hq1 : q ∉ B1 := fun h => hq (Or.inl h)
    have hq2 : q ∉ B2 := fun h => hq (Or.inr h)
    obtain ⟨hT1, hTpos, hlo, hhi, hτpos⟩ := key q hq1 hq2
    have hX : IsUnit (Matrix.of q.1 * (Matrix.of q.1)ᵀ).det :=
      isUnit_det_of_trace_inv_ne_zero _ hTpos.ne'
    have hZ : IsUnit ((Matrix.of q.1 * (Matrix.of q.2)ᵀ) *
        (Matrix.of q.1 * (Matrix.of q.2)ᵀ)ᵀ).det :=
      isUnit_det_of_trace_inv_ne_zero _ hτpos.ne'
    have hBeq : Bf (Matrix.of q.2 * P q.1, q.1) =
        (((Matrix.of q.1 * (Matrix.of q.2)ᵀ)ᵀ * ((Matrix.of q.1 * (Matrix.of q.2)ᵀ) *
          (Matrix.of q.1 * (Matrix.of q.2)ᵀ)ᵀ)⁻¹) *
        ((Matrix.of q.1 * (Matrix.of q.2)ᵀ)ᵀ * ((Matrix.of q.1 * (Matrix.of q.2)ᵀ) *
          (Matrix.of q.1 * (Matrix.of q.2)ᵀ)ᵀ)⁻¹)ᵀ) := by
      simp only [hBf, hP]
      rw [mul_transpose_mul_gramProjector_transpose _ _ hX]
    set Z0 : Matrix (Fin m) (Fin n) ℝ := Matrix.of q.1 * (Matrix.of q.2)ᵀ with hZ0
    have hFrob := Matrix.sum_sq_mul_transpose_le_trace_sq (Z0ᵀ * (Z0 * Z0ᵀ)⁻¹)
    have htrB : ((Z0ᵀ * (Z0 * Z0ᵀ)⁻¹) * (Z0ᵀ * (Z0 * Z0ᵀ)⁻¹)ᵀ).trace = τ q := by
      rw [Matrix.trace_mul_comm, rightInverse_transpose_mul_self Z0 hZ]
    have hone : ∑ k : Fin n₀, ∑ l : Fin n₀, (1 : Matrix (Fin n₀) (Fin n₀) ℝ) k l ^ 2 = n₀ := by
      simp [Matrix.one_apply]
    have hτle : τ q ≤ (c₁ + ε₁) / (ν * (1 - η)) := by
      refine hhi.trans ?_
      rw [div_le_div_iff_of_pos_right (by have : 0 < 1 - η := by linarith
                                          positivity)]
      linarith [(abs_lt.1 hT1).2]
    rw [hBeq, hone]
    rw [htrB] at hFrob
    have hsq : (τ q) ^ 2 ≤ ((c₁ + ε₁) / (ν * (1 - η))) ^ 2 :=
      pow_le_pow_left₀ hτpos.le hτle 2
    have hn₀ : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
    have : 2 * (∑ i, ∑ j, ((Z0ᵀ * (Z0 * Z0ᵀ)⁻¹) * (Z0ᵀ * (Z0 * Z0ᵀ)⁻¹)ᵀ) i j ^ 2) * (n₀ : ℝ) ≤
        2 * (n₀ : ℝ) * ((c₁ + ε₁) / (ν * (1 - η))) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right (hFrob.trans hsq) hn₀]
    exact div_le_div_of_nonneg_right this (sq_nonneg ε₃)
  have hsub : {x : (Fin m → Fin n₀ → ℝ) × (Fin n → Fin n₀ → ℝ) |
      ¬ ((c₁ - ε₁) * (1 + (((n₀ : ℝ) - m) / ν) / (1 + η)) - ε₃ < Var x ∧
        Var x < (c₁ + ε₁) * (1 + (((n₀ : ℝ) - m) / ν) / (1 - η)) + ε₃)} ⊆ B1 ∪ B2 ∪ C3 := by
    intro x hx
    by_contra hnot
    simp only [Set.mem_union, not_or] at hnot
    obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hnot
    apply hx
    obtain ⟨hT1, hTpos, hlo, hhi, hτpos⟩ := key x hx1 hx2
    have hX : IsUnit (Matrix.of x.1 * (Matrix.of x.1)ᵀ).det :=
      isUnit_det_of_trace_inv_ne_zero _ hTpos.ne'
    have hZ : IsUnit ((Matrix.of x.1 * (Matrix.of x.2)ᵀ) *
        (Matrix.of x.1 * (Matrix.of x.2)ᵀ)ᵀ).det :=
      isUnit_det_of_trace_inv_ne_zero _ hτpos.ne'
    have hBeq : Bf (Matrix.of x.2 * P x.1, x.1) =
        (((Matrix.of x.1 * (Matrix.of x.2)ᵀ)ᵀ * ((Matrix.of x.1 * (Matrix.of x.2)ᵀ) *
          (Matrix.of x.1 * (Matrix.of x.2)ᵀ)ᵀ)⁻¹) *
        ((Matrix.of x.1 * (Matrix.of x.2)ᵀ)ᵀ * ((Matrix.of x.1 * (Matrix.of x.2)ᵀ) *
          (Matrix.of x.1 * (Matrix.of x.2)ᵀ)ᵀ)⁻¹)ᵀ) := by
      simp only [hBf, hP]
      rw [mul_transpose_mul_gramProjector_transpose _ _ hX]
    set Z0 : Matrix (Fin m) (Fin n) ℝ := Matrix.of x.1 * (Matrix.of x.2)ᵀ with hZ0
    have htrB : ((Z0ᵀ * (Z0 * Z0ᵀ)⁻¹) * (Z0ᵀ * (Z0 * Z0ᵀ)⁻¹)ᵀ).trace = τ x := by
      rw [Matrix.trace_mul_comm, rightInverse_transpose_mul_self Z0 hZ]
    have htrD : ((1 - P x.1) * (1 : Matrix (Fin n₀) (Fin n₀) ℝ) * (1 - P x.1)).trace =
        (n₀ : ℝ) - m := by
      have hPs' := hPs x.1
      have hD : IsStarProjection (1 - P x.1) := hPs'.one_sub
      have hDD : (1 - P x.1) * (1 - P x.1) = 1 - P x.1 := by
        exact ((isStarProjection_matrix_real_iff _).1 hD).2
      rw [Matrix.mul_one, hDD, Matrix.trace_sub, Matrix.trace_one, hP]
      simp only [Fintype.card_fin]
      rw [trace_gramProjector _ (by simpa using hX)]
      simp
    have hT2 : ∑ i, ∑ j, Bf (Matrix.of x.2 * P x.1, x.1) i j *
        ((Matrix.of x.2 * (1 - P x.1) * (1 : Matrix (Fin n₀) (Fin n₀) ℝ) *
          (Matrix.of x.2 * (1 - P x.1))ᵀ : Matrix (Fin n) (Fin n) ℝ) i j) =
        ((Z0ᵀ * (Z0 * Z0ᵀ)⁻¹ * (Z0ᵀ * (Z0 * Z0ᵀ)⁻¹)ᵀ) *
          ((Matrix.of x.2)ᵀᵀ * (1 - gramProjector (Matrix.of x.1)ᵀ) * (Matrix.of x.2)ᵀ)).trace := by
      rw [hBeq, ← trace_mul_residual_eq_sum _ _ _ (hPs x.1)]
    have hVarEq : Var x = ((Matrix.of x.1 * (Matrix.of x.1)ᵀ)⁻¹).trace +
        ((Z0ᵀ * (Z0 * Z0ᵀ)⁻¹ * (Z0ᵀ * (Z0 * Z0ᵀ)⁻¹)ᵀ) *
          ((Matrix.of x.2)ᵀᵀ * (1 - gramProjector (Matrix.of x.1)ᵀ) * (Matrix.of x.2)ᵀ)).trace := by
      rw [hVar x]
      exact sampleBottleneck_trace_eq_add (Matrix.of x.1) (Matrix.of x.2)ᵀ hX hZ
    simp only [hC3, Set.mem_ofPred_eq, not_le] at hx3
    rw [hT2, hBeq, htrB, htrD] at hx3
    rw [hVarEq]
    refine variance_sandwich_arith hν hη hη1 (sub_nonneg.2 (Nat.cast_le.2 hmn₀ : (m : ℝ) ≤ n₀))
      hT1 hlo hhi ?_
    rw [mul_comm]
    exact hx3
  calc (μX.prod μV) _ ≤ (μX.prod μV) (B1 ∪ B2 ∪ C3) := measure_mono hsub
    _ ≤ (μX.prod μV) (B1 ∪ B2) + (μX.prod μV) C3 := measure_union_le _ _
    _ ≤ ((μX.prod μV) B1 + (μX.prod μV) B2) + (μX.prod μV) C3 :=
        add_le_add_left (measure_union_le _ _) _
    _ ≤ ((μX.prod μV) B1 + (μX.prod μV) B2) + ((μX.prod μV) B1 + (μX.prod μV) B2 +
        ENNReal.ofReal (2 * (n₀ : ℝ) * ((c₁ + ε₁) / (ν * (1 - η))) ^ 2 / ε₃ ^ 2)) :=
        add_le_add_right (hcond'.trans hint) _
    _ ≤ 2 * μX {a | ε₁ ≤ |T₁ a - c₁|} +
        2 * ENNReal.ofReal ((m : ℝ) * (60 / (η ^ 4 * ν ^ 2))) +
        ENNReal.ofReal (2 * (n₀ : ℝ) * ((c₁ + ε₁) / (ν * (1 - η))) ^ 2 / ε₃ ^ 2) := by
        rw [hB1μ]
        have := hB2μ
        calc _ = 2 * μX {a | ε₁ ≤ |T₁ a - c₁|} + 2 * (μX.prod μV) B2 +
              ENNReal.ofReal (2 * (n₀ : ℝ) * ((c₁ + ε₁) / (ν * (1 - η))) ^ 2 / ε₃ ^ 2) := by
              rw [two_mul, two_mul]; ring
          _ ≤ _ := by gcongr


end Variance

/-- **Ratio limits in the sample-bottleneck regime.** If `m_k → ∞`, `n₀_k / m_k → γ` and
`n_k / m_k → δ > 1` with `m_k ≤ n_k`, then for `ν_k = n_k - m_k + 1`: `ν_k → ∞`,
`ν_k / m_k → δ - 1`, `m_k / ν_k² → 0`, `n₀_k / ν_k² → 0` and
`(n₀_k - m_k) / ν_k → (γ - 1) / (δ - 1)`. -/
theorem tendsto_sample_ratios {mm nn n0 : ℕ → ℕ} {γ δ : ℝ} (hδ : 1 < δ)
    (hm : ∀ k, 0 < mm k) (hmn : ∀ k, mm k ≤ nn k) (hmm : Tendsto mm atTop atTop)
    (hγ : Tendsto (fun k => (n0 k : ℝ) / (mm k : ℝ)) atTop (𝓝 γ))
    (hδ' : Tendsto (fun k => (nn k : ℝ) / (mm k : ℝ)) atTop (𝓝 δ)) :
    Tendsto (fun k => ((nn k - mm k + 1 : ℕ) : ℝ)) atTop atTop ∧
      Tendsto (fun k => ((nn k - mm k + 1 : ℕ) : ℝ) / (mm k : ℝ)) atTop (𝓝 (δ - 1)) ∧
      Tendsto (fun k => (mm k : ℝ) / ((nn k - mm k + 1 : ℕ) : ℝ) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun k => (n0 k : ℝ) / ((nn k - mm k + 1 : ℕ) : ℝ) ^ 2) atTop (𝓝 0) ∧
      Tendsto (fun k => ((n0 k : ℝ) - mm k) / ((nn k - mm k + 1 : ℕ) : ℝ)) atTop
        (𝓝 ((γ - 1) / (δ - 1))) := by
  have hmR : Tendsto (fun k => (mm k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hmm
  have hmpos : ∀ k, (0 : ℝ) < mm k := fun k => by exact_mod_cast hm k
  have hν : ∀ k, ((nn k - mm k + 1 : ℕ) : ℝ) = (nn k : ℝ) - mm k + 1 := fun k => by
    rw [Nat.cast_add, Nat.cast_sub (hmn k)]; simp
  have hδ1 : 0 < δ - 1 := by linarith
  have hrat : Tendsto (fun k => ((nn k - mm k + 1 : ℕ) : ℝ) / (mm k : ℝ)) atTop (𝓝 (δ - 1)) := by
    have h1 : Tendsto (fun k => (nn k : ℝ) / (mm k : ℝ) - 1 + 1 / (mm k : ℝ)) atTop
        (𝓝 (δ - 1 + 0)) :=
      (hδ'.sub_const 1).add (tendsto_const_nhds.div_atTop hmR)
    rw [add_zero] at h1
    refine h1.congr fun k => ?_
    rw [hν k]; field_simp [(hmpos k).ne']
  have hνtop : Tendsto (fun k => ((nn k - mm k + 1 : ℕ) : ℝ)) atTop atTop := by
    have := hrat.pos_mul_atTop hδ1 hmR
    refine this.congr fun k => ?_
    field_simp [(hmpos k).ne']
  have hνpos : ∀ k, (0 : ℝ) < ((nn k - mm k + 1 : ℕ) : ℝ) := fun k => by
    rw [hν k]; have : (mm k : ℝ) ≤ nn k := by exact_mod_cast hmn k
    linarith
  have hinv : Tendsto (fun k => ((nn k - mm k + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hνtop
  have hmν : Tendsto (fun k => (mm k : ℝ) / ((nn k - mm k + 1 : ℕ) : ℝ)) atTop
      (𝓝 ((δ - 1)⁻¹)) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).div hrat hδ1.ne'
    rw [one_div] at this
    refine this.congr fun k => ?_
    simp only [Pi.div_apply]
    field_simp [(hmpos k).ne', (hνpos k).ne']
  refine ⟨hνtop, hrat, ?_, ?_, ?_⟩
  · have := hmν.mul hinv
    simp only [mul_zero] at this
    refine this.congr fun k => ?_
    field_simp [(hνpos k).ne']
  · have := (hγ.mul hmν).mul hinv
    simp only [mul_zero] at this
    refine this.congr fun k => ?_
    field_simp [(hνpos k).ne', (hmpos k).ne']
  · have := (hγ.sub_const 1).div hrat hδ1.ne'
    refine this.congr fun k => ?_
    simp only [Pi.div_apply]
    field_simp [(hνpos k).ne', (hmpos k).ne']

/-- **The design trace `Tr ((X Xᵀ)⁻¹)` converges in probability to `(γ - 1)⁻¹`.** Along
`m_k ≤ n₀_k`, `m_k → ∞`, `n₀_k / m_k → γ > 1`, for `X_k` an `m_k × n₀_k` Gaussian matrix:
`ℙ (|Tr ((X_k X_kᵀ)⁻¹) - (γ - 1)⁻¹| ≥ ε) → 0`. This is Lemma 3.2 for the transpose `X_kᵀ`
(`tendsto_measure_trace_inv_gram_deviation`) together with `measure_preimage_transpose_le`. -/
theorem tendsto_measure_design_trace_inv_deviation {mm n0 : ℕ → ℕ} {γ : ℝ} (hγ : 1 < γ)
    (hm : ∀ k, 0 < mm k) (hmn0 : ∀ k, mm k ≤ n0 k) (hmm : Tendsto mm atTop atTop)
    (hγ' : Tendsto (fun k => (n0 k : ℝ) / (mm k : ℝ)) atTop (𝓝 γ)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k =>
      (Measure.pi fun _ : Fin (mm k) => Measure.pi fun _ : Fin (n0 k) => gaussianReal 0 1)
        {a | ε ≤ |((Matrix.of a * (Matrix.of a)ᵀ)⁻¹).trace - (γ - 1)⁻¹|}) atTop (𝓝 0) := by
  have hγ0 : 0 < γ := by linarith
  have hρ : Tendsto (fun k => (mm k : ℝ) / (n0 k : ℝ)) atTop (𝓝 γ⁻¹) := by
    have := hγ'.inv₀ hγ0.ne'
    refine this.congr fun k => ?_
    simp [inv_div]
  have hρ1 : γ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hγ
  have hn0 : Tendsto n0 atTop atTop := tendsto_atTop_mono hmn0 hmm
  have hc : γ⁻¹ / (1 - γ⁻¹) = (γ - 1)⁻¹ := by
    have : γ - 1 ≠ 0 := by linarith
    field_simp
  have h7d := tendsto_measure_trace_inv_gram_deviation hρ1 hm hmn0 hn0 hρ hε
  rw [hc] at h7d
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h7d
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun k => ?_)
  exact measure_preimage_transpose_le (mm k) (n0 k)
    {W | ε ≤ |((Matrix.of W)ᵀ * Matrix.of W)⁻¹.trace - (γ - 1)⁻¹|}


/-- **The variance of the sample-bottleneck estimator converges in probability (Milestone 7g,
variance half).** Let `X_k` be `m_k × n₀_k` and `V_k` independent `n_k × n₀_k` Gaussian matrices,
`S_k = V_kᵀ`, `Z_k = X_k S_k`, with `0 < m_k ≤ min {n_k, n₀_k}`, `m_k → ∞`, `n₀_k / m_k → γ > 1` and
`n_k / m_k → δ > 1`. Then the variance trace `Tr ((Z Zᵀ)⁻¹ (Z Sᵀ S Zᵀ) (Z Zᵀ)⁻¹)` of
`θ̂ = S Z† y` (`sampleBottleneck_variance_eq_trace`) converges in probability to
`(γ - 1)⁻¹ + (δ - 1)⁻¹`: for every `ε > 0` the probability that it differs from this by at least
`ε` tends to `0`. The variance of the estimator is `σ²` times this trace.

Proof: with `c₁ = (γ - 1)⁻¹`, `λ = (γ - 1) / (δ - 1)` the limit is `c₁ (1 + λ)`. One small
tolerance `t` (`exists_pos_lt_sandwich`) makes the sandwich of `measure_sampleVariance_sandwich_le`
lie inside `(L - ε, L + ε)` eventually, and its failure probability tends to `0` by
`tendsto_measure_design_trace_inv_deviation` and the ratio limits. -/
theorem tendsto_measure_sampleVariance_deviation {mm nn n0 : ℕ → ℕ} {γ δ : ℝ} (hγ : 1 < γ)
    (hδ : 1 < δ) (hm : ∀ k, 0 < mm k) (hmn : ∀ k, mm k ≤ nn k) (hmn0 : ∀ k, mm k ≤ n0 k)
    (hmm : Tendsto mm atTop atTop)
    (hγ' : Tendsto (fun k => (n0 k : ℝ) / (mm k : ℝ)) atTop (𝓝 γ))
    (hδ' : Tendsto (fun k => (nn k : ℝ) / (mm k : ℝ)) atTop (𝓝 δ))
    (Var : ∀ k, (Fin (mm k) → Fin (n0 k) → ℝ) × (Fin (nn k) → Fin (n0 k) → ℝ) → ℝ)
    (hVar : ∀ k x, Var k x = Matrix.trace
      (((Matrix.of x.1 * (Matrix.of x.2)ᵀ) * (Matrix.of x.1 * (Matrix.of x.2)ᵀ)ᵀ)⁻¹ *
        ((Matrix.of x.1 * (Matrix.of x.2)ᵀ) * ((Matrix.of x.2)ᵀᵀ * (Matrix.of x.2)ᵀ) *
          (Matrix.of x.1 * (Matrix.of x.2)ᵀ)ᵀ) *
        ((Matrix.of x.1 * (Matrix.of x.2)ᵀ) * (Matrix.of x.1 * (Matrix.of x.2)ᵀ)ᵀ)⁻¹))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k =>
      ((Measure.pi fun _ : Fin (mm k) => Measure.pi fun _ : Fin (n0 k) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (nn k) => Measure.pi fun _ : Fin (n0 k) => gaussianReal 0 1))
        {x | ε ≤ |Var k x - ((γ - 1)⁻¹ + (δ - 1)⁻¹)|}) atTop (𝓝 0) := by
  have hγ1 : 0 < γ - 1 := by linarith
  have hδ1 : 0 < δ - 1 := by linarith
  set c₁ : ℝ := (γ - 1)⁻¹ with hc₁
  have hc₁0 : 0 < c₁ := inv_pos.2 hγ1
  set lam : ℝ := (γ - 1) / (δ - 1) with hlam
  have hL : c₁ * (1 + lam) = (γ - 1)⁻¹ + (δ - 1)⁻¹ := by
    rw [hc₁, hlam]; field_simp
  set F : ℝ → ℝ := fun t => (c₁ - t) * (1 + lam / (1 + t)) - t with hF
  set G : ℝ → ℝ := fun t => (c₁ + t) * (1 + lam / (1 - t)) + t with hG
  have hFc : ContinuousAt F 0 := by
    refine ContinuousAt.sub (ContinuousAt.mul (by fun_prop) (ContinuousAt.add continuousAt_const
      (ContinuousAt.div continuousAt_const (by fun_prop) (by norm_num)))) (by fun_prop)
  have hGc : ContinuousAt G 0 := by
    refine ContinuousAt.add (ContinuousAt.mul (by fun_prop) (ContinuousAt.add continuousAt_const
      (ContinuousAt.div continuousAt_const (by fun_prop) (by norm_num)))) (by fun_prop)
  have hF0 : F 0 = (γ - 1)⁻¹ + (δ - 1)⁻¹ := by simp [hF, hL.symm]
  have hG0 : G 0 = (γ - 1)⁻¹ + (δ - 1)⁻¹ := by simp [hG, hL.symm]
  obtain ⟨t, ht0, ht1, hFt, hGt⟩ := exists_pos_lt_sandwich hFc hGc hF0 hG0 hε
    (lt_min one_pos hc₁0)
  have ht1' : t < 1 := lt_of_lt_of_le ht1 (min_le_left _ _)
  have htc : t ≤ c₁ := (lt_of_lt_of_le ht1 (min_le_right _ _)).le
  obtain ⟨hνtop, hrat, hmν2, hnν2, hlamk⟩ := tendsto_sample_ratios hδ hm hmn hmm hγ' hδ'
  have hXtail := tendsto_measure_design_trace_inv_deviation hγ hm hmn0 hmm hγ' ht0
  -- the failure probability of the non-asymptotic sandwich tends to `0`
  have hb2 : Tendsto (fun k => ENNReal.ofReal
      ((mm k : ℝ) * (60 / (t ^ 4 * ((nn k - mm k + 1 : ℕ) : ℝ) ^ 2)))) atTop (𝓝 0) := by
    have := (hmν2.const_mul (60 / t ^ 4))
    simp only [mul_zero] at this
    have h2 := ENNReal.tendsto_ofReal this
    rw [ENNReal.ofReal_zero] at h2
    refine h2.congr fun k => ?_
    congr 1
    have : (0 : ℝ) < ((nn k - mm k + 1 : ℕ) : ℝ) := by positivity
    field_simp
  have hb3 : Tendsto (fun k => ENNReal.ofReal (2 * (n0 k : ℝ) *
      ((c₁ + t) / (((nn k - mm k + 1 : ℕ) : ℝ) * (1 - t))) ^ 2 / t ^ 2)) atTop (𝓝 0) := by
    have h1t : 0 < 1 - t := by linarith
    have := hnν2.const_mul (2 * (c₁ + t) ^ 2 / ((1 - t) ^ 2 * t ^ 2))
    simp only [mul_zero] at this
    have h2 := ENNReal.tendsto_ofReal this
    rw [ENNReal.ofReal_zero] at h2
    refine h2.congr fun k => ?_
    congr 1
    have : (0 : ℝ) < ((nn k - mm k + 1 : ℕ) : ℝ) := by positivity
    field_simp
  have hbound : Tendsto (fun k =>
      2 * (Measure.pi fun _ : Fin (mm k) => Measure.pi fun _ : Fin (n0 k) => gaussianReal 0 1)
          {a | t ≤ |((Matrix.of a * (Matrix.of a)ᵀ)⁻¹).trace - c₁|} +
        2 * ENNReal.ofReal ((mm k : ℝ) * (60 / (t ^ 4 * ((nn k - mm k + 1 : ℕ) : ℝ) ^ 2))) +
        ENNReal.ofReal (2 * (n0 k : ℝ) *
          ((c₁ + t) / (((nn k - mm k + 1 : ℕ) : ℝ) * (1 - t))) ^ 2 / t ^ 2)) atTop (𝓝 0) := by
    have h := ((ENNReal.Tendsto.const_mul hXtail (Or.inr (by simp : (2 : ℝ≥0∞) ≠ ⊤))).add
      (ENNReal.Tendsto.const_mul hb2 (Or.inr (by simp : (2 : ℝ≥0∞) ≠ ⊤)))).add hb3
    simpa using h
  -- the sandwich endpoints converge to `F t` and `G t`
  have hlo : Tendsto (fun k => (c₁ - t) * (1 + (((n0 k : ℝ) - mm k) /
      ((nn k - mm k + 1 : ℕ) : ℝ)) / (1 + t)) - t) atTop (𝓝 (F t)) := by
    have h := (((tendsto_const_nhds (x := (1 : ℝ))).add (hlamk.div_const (1 + t))).const_mul
      (c₁ - t)).sub_const t
    refine h.congr fun k => ?_
    simp
  have hhi : Tendsto (fun k => (c₁ + t) * (1 + (((n0 k : ℝ) - mm k) /
      ((nn k - mm k + 1 : ℕ) : ℝ)) / (1 - t)) + t) atTop (𝓝 (G t)) := by
    have h := (((tendsto_const_nhds (x := (1 : ℝ))).add (hlamk.div_const (1 - t))).const_mul
      (c₁ + t)).add_const t
    refine h.congr fun k => ?_
    simp
  have hevlo := hlo.eventually (lt_mem_nhds hFt)
  have hevhi := hhi.eventually (gt_mem_nhds hGt)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hevlo, hevhi] with k h1 h2
  refine le_trans (measure_mono ?_) (measure_sampleVariance_sandwich_le (hm k) (hmn k) (hmn0 k)
    ht0 ht1' htc ht0 (Var k) (hVar k))
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  rintro ⟨h3, h4⟩
  have : |Var k x - ((γ - 1)⁻¹ + (δ - 1)⁻¹)| < ε := by
    rw [abs_lt]; constructor <;> linarith
  exact absurd hx (not_le.2 this)

end LinearRegression.DoubleDescent

end
