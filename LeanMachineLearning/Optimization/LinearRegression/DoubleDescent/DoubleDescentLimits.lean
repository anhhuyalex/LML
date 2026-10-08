/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.Deviation
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.AmbientBottleneck
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.DoubleDescentCurve
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.FeatureBottleneckLimits
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.SampleBottleneckLimits

/-!
# Global double descent of the risk (Milestone 7h, Theorem 3.1)

The three regimes of random-feature regression, with `m` samples, `n₀` ambient dimension and `n`
random features, are decided by the *smallest* of the three dimensions. `minNormOperator` is the
minimum-norm least-squares operator `M` (`θ̂ = M y`) with the formula valid in each regime, and
`conditionalRisk σ² θ X S = ‖(M X - 1) θ‖² + σ² Tr (Mᵀ M)` is the expected squared error of `θ̂`
over isotropic noise (`risk_eq_conditionalRisk`).

For independent Gaussian `X ∈ ℝ^{m×n₀}`, `S ∈ ℝ^{n₀×n}` the risk converges in probability to
`asymptoticTotalRisk σ² ρ⋆ γ δ` (`γ = lim n₀/m`, `δ = lim n/m`, `ρ⋆ = lim ‖θ‖²`):

* `tendsto_measure_featureRisk_deviation` (`n` smallest, Milestone 7f);
* `tendsto_measure_ambientRisk_deviation` (`n₀` smallest: OLS, unbiased, variance
  `σ² γ / (1 - γ)`);
* `tendsto_measure_sampleRisk_deviation` (`m` smallest, Milestone 7g);
* `double_descent_total_risk_convergence`: **Theorem 3.1**, the three regimes in one statement on
  the non-singular domain, with the structural hypotheses (`n ≤ min {m, n₀}`, ...) derived from the
  ratio limits (`..._of_eventually`).
-/

@[expose]
public section

namespace LinearRegression.DoubleDescent

open MeasureTheory ProbabilityTheory Matrix NTK Filter Topology
open scoped Matrix ENNReal

section Defs

variable {m n n₀ : ℕ}

/-- **The minimum-norm random-feature operator** `M` with `θ̂ = M y`, chosen by the smallest of the
three dimensions (`m` samples, `n₀` ambient, `n` features), which decides which Gram matrix of
`Z = X S` is invertible:
* `n ≤ min {m, n₀}` (feature bottleneck): `M = S (Zᵀ Z)⁻¹ Zᵀ`, the least-squares fit;
* `n₀ ≤ min {m, n}` (ambient bottleneck): `M = S (Sᵀ (S Sᵀ)⁻¹ ((Xᵀ X)⁻¹ Xᵀ))`, the minimum-norm
  least-squares fit, which is OLS `(Xᵀ X)⁻¹ Xᵀ` as soon as `S Sᵀ` is invertible;
* otherwise (`m` smallest, sample bottleneck): `M = S Zᵀ (Z Zᵀ)⁻¹`, the minimum-norm
  interpolator. -/
noncomputable def minNormOperator (X : Matrix (Fin m) (Fin n₀) ℝ) (S : Matrix (Fin n₀) (Fin n) ℝ) :
    Matrix (Fin n₀) (Fin m) ℝ :=
  if n ≤ min m n₀ then S * (((X * S)ᵀ * (X * S))⁻¹ * (X * S)ᵀ)
  else if n₀ ≤ min m n then S * ((Sᵀ * (S * Sᵀ)⁻¹) * ((Xᵀ * X)⁻¹ * Xᵀ))
  else S * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹)

/-- **The conditional prediction risk of the random-feature estimator.** With isotropic noise of
variance `σ²`, the risk `E_ε ‖θ̂ - θ‖²` of `θ̂ = M (X θ + ε)` is
`‖(M X - 1) θ‖² + σ² Tr (Mᵀ M)` (`linearEstimator_bias_variance_isotropic`). -/
noncomputable def conditionalRisk (σ_sq : ℝ) (θ : Fin n₀ → ℝ) (X : Matrix (Fin m) (Fin n₀) ℝ)
    (S : Matrix (Fin n₀) (Fin n) ℝ) : ℝ :=
  ((minNormOperator X S * X - 1) *ᵥ θ) ⬝ᵥ ((minNormOperator X S * X - 1) *ᵥ θ) +
    σ_sq * Matrix.trace ((minNormOperator X S)ᵀ * minNormOperator X S)

theorem minNormOperator_of_feature {X : Matrix (Fin m) (Fin n₀) ℝ} {S : Matrix (Fin n₀) (Fin n) ℝ}
    (h : n ≤ min m n₀) :
    minNormOperator X S = S * (((X * S)ᵀ * (X * S))⁻¹ * (X * S)ᵀ) := by
  simp [minNormOperator, h]

theorem minNormOperator_of_ambient {X : Matrix (Fin m) (Fin n₀) ℝ} {S : Matrix (Fin n₀) (Fin n) ℝ}
    (h : ¬ n ≤ min m n₀) (h' : n₀ ≤ min m n) :
    minNormOperator X S = S * ((Sᵀ * (S * Sᵀ)⁻¹) * ((Xᵀ * X)⁻¹ * Xᵀ)) := by
  simp [minNormOperator, h, h']

theorem minNormOperator_of_sample {X : Matrix (Fin m) (Fin n₀) ℝ} {S : Matrix (Fin n₀) (Fin n) ℝ}
    (h : ¬ n ≤ min m n₀) (h' : ¬ n₀ ≤ min m n) :
    minNormOperator X S = S * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹) := by
  simp [minNormOperator, h, h']

/-- **`conditionalRisk` is `LinearRegression.risk`, in closed form.** For the estimator
`θ̂ = M (X θ + ε)`, `M = minNormOperator X S`, and centered noise of covariance `σ² I`, the risk
`LinearRegression.risk 1 P θ̂ θ = E ‖θ̂ - θ‖²` equals `conditionalRisk σ² θ X S`: its bias is
`‖(M X - 1) θ‖²` and its variance `σ² Tr (Mᵀ M)` (`linearEstimator_bias_variance_isotropic`). -/
theorem risk_eq_conditionalRisk (σ_sq : ℝ) (θ : EuclideanSpace ℝ (Fin n₀))
    (X : Matrix (Fin m) (Fin n₀) ℝ) (S : Matrix (Fin n₀) (Fin n) ℝ)
    (P : Measure (Fin m → ℝ)) [IsProbabilityMeasure P]
    (hε : ∀ i, MemLp (fun ε : Fin m → ℝ => ε i) 2 P) (h_mean : ∀ i, ∫ ε, ε i ∂P = 0)
    (h_cov : ∀ i j, ∫ ε, ε i * ε j ∂P = if i = j then σ_sq else 0)
    (β_hat : (Fin m → ℝ) → EuclideanSpace ℝ (Fin n₀))
    (hβ : ∀ ε, (β_hat ε).ofLp = minNormOperator X S *ᵥ (X *ᵥ θ.ofLp + ε)) :
    LinearRegression.risk 1 P β_hat θ = conditionalRisk σ_sq θ.ofLp X S := by
  rw [(linearEstimator_bias_variance_isotropic (minNormOperator X S) X θ 1 σ_sq P hε h_mean
    h_cov β_hat hβ).2.2]
  unfold conditionalRisk
  rw [Matrix.one_mulVec, Matrix.mul_one, Matrix.trace_mul_comm]

/-- The feature-bottleneck variance trace identity holds without any invertibility hypothesis:
for singular `Zᵀ Z` both sides vanish (`0⁻¹`-convention). -/
theorem trace_featureOperator_eq (S : Matrix (Fin n₀) (Fin n) ℝ) (Z : Matrix (Fin m) (Fin n) ℝ) :
    Matrix.trace ((S * ((Zᵀ * Z)⁻¹ * Zᵀ))ᵀ * (S * ((Zᵀ * Z)⁻¹ * Zᵀ))) =
      Matrix.trace ((Zᵀ * Z)⁻¹ * (Sᵀ * S)) := by
  by_cases hZ : IsUnit (Zᵀ * Z).det
  · exact trace_operator_transpose_mul_self_eq_featureBottleneck S Z hZ
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hZ]
    simp only [Matrix.zero_mul, Matrix.mul_zero, Matrix.transpose_zero, Matrix.trace_zero]

/-- **Feature-bottleneck branch of the risk.** -/
theorem conditionalRisk_of_feature (σ_sq : ℝ) (θ : Fin n₀ → ℝ) (X : Matrix (Fin m) (Fin n₀) ℝ)
    (S : Matrix (Fin n₀) (Fin n) ℝ) (h : n ≤ min m n₀) :
    conditionalRisk σ_sq θ X S =
      (((S * (((X * S)ᵀ * (X * S))⁻¹ * (X * S)ᵀ)) * X - 1) *ᵥ θ) ⬝ᵥ
        (((S * (((X * S)ᵀ * (X * S))⁻¹ * (X * S)ᵀ)) * X - 1) *ᵥ θ) +
      σ_sq * Matrix.trace (((X * S)ᵀ * (X * S))⁻¹ * (Sᵀ * S)) := by
  unfold conditionalRisk
  rw [minNormOperator_of_feature h, trace_featureOperator_eq]

/-- **Sample-bottleneck branch of the risk.** -/
theorem conditionalRisk_of_sample (σ_sq : ℝ) (θ : Fin n₀ → ℝ) (X : Matrix (Fin m) (Fin n₀) ℝ)
    (S : Matrix (Fin n₀) (Fin n) ℝ) (h : ¬ n ≤ min m n₀) (h' : ¬ n₀ ≤ min m n) :
    conditionalRisk σ_sq θ X S =
      (((S * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹)) * X - 1) *ᵥ θ) ⬝ᵥ
        (((S * ((X * S)ᵀ * ((X * S) * (X * S)ᵀ)⁻¹)) * X - 1) *ᵥ θ) +
      σ_sq * Matrix.trace (((X * S) * (X * S)ᵀ)⁻¹ * ((X * S) * (Sᵀ * S) * (X * S)ᵀ) *
        ((X * S) * (X * S)ᵀ)⁻¹) := by
  unfold conditionalRisk
  rw [minNormOperator_of_sample h h', trace_operator_transpose_mul_self_eq_sampleBottleneck]

end Defs

section Ambient

variable {m n n₀ : ℕ}

/-- **The ambient-bottleneck risk is the OLS variance.** If `S Sᵀ` and `Xᵀ X` are invertible and the
branch of `minNormOperator` is the ambient one, then `conditionalRisk σ² θ X S = σ² Tr ((Xᵀ X)⁻¹)`:
the operator is OLS `(Xᵀ X)⁻¹ Xᵀ` (as `S (Sᵀ (S Sᵀ)⁻¹) = 1`), hence unbiased. -/
theorem conditionalRisk_of_ambient (σ_sq : ℝ) (θ : Fin n₀ → ℝ) (X : Matrix (Fin m) (Fin n₀) ℝ)
    (S : Matrix (Fin n₀) (Fin n) ℝ) (h : ¬ n ≤ min m n₀) (h' : n₀ ≤ min m n)
    (hX : IsUnit (Xᵀ * X).det) (hS : IsUnit (S * Sᵀ).det) :
    conditionalRisk σ_sq θ X S = σ_sq * ((Xᵀ * X)⁻¹).trace := by
  have hM : minNormOperator X S = (Xᵀ * X)⁻¹ * Xᵀ := by
    rw [minNormOperator_of_ambient h h', ← Matrix.mul_assoc S, self_mul_rightInverse S hS,
      Matrix.one_mul]
  have h1 : minNormOperator X S * X - 1 = 0 := by
    rw [hM, leftInverse_mul_self X hX, sub_self]
  have h2 : ((minNormOperator X S)ᵀ * minNormOperator X S).trace = ((Xᵀ * X)⁻¹).trace := by
    rw [Matrix.trace_mul_comm, hM, leftInverse_mul_transpose X hX]
  unfold conditionalRisk
  rw [h1, Matrix.zero_mulVec, dotProduct_zero, zero_add, h2]

end Ambient

section Regimes

/-- **Total risk in the feature-bottleneck regime, in probability.** Let `X_k` (`m_k × n₀_k`) and
`S_k` (`n₀_k × n_k`) be independent Gaussian matrices with `1 ≤ n_k ≤ min {m_k, n₀_k}`, `n_k → ∞`,
`n_k / m_k → δ < 1`, `n₀_k / m_k → γ > 0` and `‖θ_k‖² → r`. Then `conditionalRisk` converges in
probability to `(γ - δ) / (γ (1 - δ)) r + σ² δ / (1 - δ)`. -/
private theorem tendsto_measure_featureRisk_deviation_of_forall
    {mm nn n0 : ℕ → ℕ} {δ γ r : ℝ} (σ_sq : ℝ)
    (hδ1 : δ < 1) (hγ0 : 0 < γ) (hn : ∀ k, 0 < nn k) (hnm : ∀ k, nn k ≤ mm k)
    (hnn0 : ∀ k, nn k ≤ n0 k) (hnn : Tendsto nn atTop atTop)
    (hδ : Tendsto (fun k => (nn k : ℝ) / (mm k : ℝ)) atTop (𝓝 δ))
    (hγ : Tendsto (fun k => (n0 k : ℝ) / (mm k : ℝ)) atTop (𝓝 γ))
    (θ : ∀ k, Fin (n0 k) → ℝ) (hθ : Tendsto (fun k => θ k ⬝ᵥ θ k) atTop (𝓝 r)) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun k =>
      ((Measure.pi fun _ : Fin (mm k) => Measure.pi fun _ : Fin (n0 k) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (n0 k) => Measure.pi fun _ : Fin (nn k) => gaussianReal 0 1))
        {x | ε ≤ |conditionalRisk σ_sq (θ k) (Matrix.of x.1) (Matrix.of x.2) -
          ((γ - δ) / (γ * (1 - δ)) * r + σ_sq * (δ / (1 - δ)))|}) atTop (𝓝 0) := by
  have hfe : ∀ k, nn k ≤ min (mm k) (n0 k) := fun k => le_min (hnm k) (hnn0 k)
  have hmm : Tendsto mm atTop atTop := tendsto_atTop_mono hnm hnn
  obtain ⟨A, hA⟩ : ∃ A : ∀ k, (Fin (mm k) → Fin (n0 k) → ℝ) × (Fin (n0 k) → Fin (nn k) → ℝ) → ℝ,
      ∀ k x, A k x = (((Matrix.of x.2 * (((Matrix.of x.1 * Matrix.of x.2)ᵀ *
          (Matrix.of x.1 * Matrix.of x.2))⁻¹ * (Matrix.of x.1 * Matrix.of x.2)ᵀ)) *
            Matrix.of x.1 - 1) *ᵥ θ k) ⬝ᵥ (((Matrix.of x.2 * (((Matrix.of x.1 * Matrix.of x.2)ᵀ *
          (Matrix.of x.1 * Matrix.of x.2))⁻¹ * (Matrix.of x.1 * Matrix.of x.2)ᵀ)) *
            Matrix.of x.1 - 1) *ᵥ θ k) := ⟨fun k x => _, fun _ _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ∀ k, (Fin (mm k) → Fin (n0 k) → ℝ) × (Fin (n0 k) → Fin (nn k) → ℝ) → ℝ,
      ∀ k x, B k x = (((Matrix.of x.1 * Matrix.of x.2)ᵀ * (Matrix.of x.1 * Matrix.of x.2))⁻¹ *
          ((Matrix.of x.2)ᵀ * Matrix.of x.2)).trace := ⟨fun k x => _, fun _ _ => rfl⟩
  refine tendsto_measure_add_mul_deviation
    (fun k => (Measure.pi fun _ : Fin (mm k) =>
      Measure.pi fun _ : Fin (n0 k) => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin (n0 k) => Measure.pi fun _ : Fin (nn k) => gaussianReal 0 1))
    (fun k x => conditionalRisk σ_sq (θ k) (Matrix.of x.1) (Matrix.of x.2)) A B σ_sq
    ((γ - δ) / (γ * (1 - δ)) * r) (δ / (1 - δ))
    (fun k x => ?_) (fun ε hε => tendsto_measure_featureBias_deviation hδ1 hγ0 hn hnm hnn0 hnn hδ
      hγ θ hθ A hA hε) (fun ε hε => ?_) hε
  · rw [hA, hB]
    exact conditionalRisk_of_feature σ_sq (θ k) _ _ (hfe k)
  · simpa only [hB] using tendsto_measure_featureVariance_deviation hδ1 hn hnm hnn0 hmm hδ hε

/-- **Total risk in the sample-bottleneck regime, in probability.** Let `X_k` (`m_k × n₀_k`) and
`S_k` (`n₀_k × n_k`) be independent Gaussian matrices with `m_k < min {n₀_k, n_k}`, `m_k → ∞`,
`n₀_k / m_k → γ > 1`, `n_k / m_k → δ > 1` and `‖θ_k‖² → r`. Then `conditionalRisk` converges in
probability to `(1 - γ⁻¹) δ / (δ - 1) r + σ² ((γ - 1)⁻¹ + (δ - 1)⁻¹)`. -/
private theorem tendsto_measure_sampleRisk_deviation_of_forall
    {mm nn n0 : ℕ → ℕ} {γ δ r : ℝ} (σ_sq : ℝ)
    (hγ : 1 < γ) (hδ : 1 < δ) (hm : ∀ k, 0 < mm k) (hmn : ∀ k, mm k < nn k)
    (hmn0 : ∀ k, mm k < n0 k) (hmm : Tendsto mm atTop atTop)
    (hγ' : Tendsto (fun k => (n0 k : ℝ) / (mm k : ℝ)) atTop (𝓝 γ))
    (hδ' : Tendsto (fun k => (nn k : ℝ) / (mm k : ℝ)) atTop (𝓝 δ))
    (θ : ∀ k, Fin (n0 k) → ℝ) (hθ : Tendsto (fun k => θ k ⬝ᵥ θ k) atTop (𝓝 r)) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun k =>
      ((Measure.pi fun _ : Fin (mm k) => Measure.pi fun _ : Fin (n0 k) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (n0 k) => Measure.pi fun _ : Fin (nn k) => gaussianReal 0 1))
        {x | ε ≤ |conditionalRisk σ_sq (θ k) (Matrix.of x.1) (Matrix.of x.2) -
          ((1 - γ⁻¹) * (δ / (δ - 1)) * r + σ_sq * ((γ - 1)⁻¹ + (δ - 1)⁻¹))|}) atTop (𝓝 0) := by
  have hbr : ∀ k, ¬ nn k ≤ min (mm k) (n0 k) := fun k h =>
    absurd ((min_le_left _ _).trans' h) (not_le.2 (hmn k))
  have hbr' : ∀ k, ¬ n0 k ≤ min (mm k) (nn k) := fun k h =>
    absurd ((min_le_left _ _).trans' h) (not_le.2 (hmn0 k))
  obtain ⟨A, hA⟩ : ∃ A : ∀ k, (Fin (mm k) → Fin (n0 k) → ℝ) × (Fin (n0 k) → Fin (nn k) → ℝ) → ℝ,
      ∀ k x, A k x = ((Matrix.of x.2 * (((Matrix.of x.1 * Matrix.of x.2)ᵀ *
        (((Matrix.of x.1 * Matrix.of x.2) * (Matrix.of x.1 * Matrix.of x.2)ᵀ)⁻¹))) *
          Matrix.of x.1 - 1) *ᵥ θ k) ⬝ᵥ
      ((Matrix.of x.2 * (((Matrix.of x.1 * Matrix.of x.2)ᵀ *
        (((Matrix.of x.1 * Matrix.of x.2) * (Matrix.of x.1 * Matrix.of x.2)ᵀ)⁻¹))) *
          Matrix.of x.1 - 1) *ᵥ θ k) := ⟨fun k x => _, fun _ _ => rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ∀ k, (Fin (mm k) → Fin (n0 k) → ℝ) × (Fin (n0 k) → Fin (nn k) → ℝ) → ℝ,
      ∀ k x, B k x = Matrix.trace
      (((Matrix.of x.1 * Matrix.of x.2) * (Matrix.of x.1 * Matrix.of x.2)ᵀ)⁻¹ *
        ((Matrix.of x.1 * Matrix.of x.2) * ((Matrix.of x.2)ᵀ * Matrix.of x.2) *
          (Matrix.of x.1 * Matrix.of x.2)ᵀ) *
        ((Matrix.of x.1 * Matrix.of x.2) * (Matrix.of x.1 * Matrix.of x.2)ᵀ)⁻¹) :=
    ⟨fun k x => _, fun _ _ => rfl⟩
  refine tendsto_measure_add_mul_deviation
    (fun k => (Measure.pi fun _ : Fin (mm k) =>
      Measure.pi fun _ : Fin (n0 k) => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin (n0 k) => Measure.pi fun _ : Fin (nn k) => gaussianReal 0 1))
    (fun k x => conditionalRisk σ_sq (θ k) (Matrix.of x.1) (Matrix.of x.2)) A B σ_sq
    ((1 - γ⁻¹) * (δ / (δ - 1)) * r) ((γ - 1)⁻¹ + (δ - 1)⁻¹)
    (fun k x => ?_) (fun ε hε => tendsto_measure_sampleBias_deviation hγ hδ hm (fun k => (hmn k).le)
      (fun k => (hmn0 k).le) hmm hγ' hδ' θ hθ A hA hε) (fun ε hε =>
      tendsto_measure_sampleVariance_deviation hγ hδ hm (fun k => (hmn k).le)
        (fun k => (hmn0 k).le) hmm hγ' hδ' B hB hε) hε
  rw [hA, hB]
  exact conditionalRisk_of_sample σ_sq (θ k) _ _ (hbr k) (hbr' k)

/-- **Total risk in the ambient-bottleneck regime, in probability.** Let `X_k` (`m_k × n₀_k`) and
`S_k` (`n₀_k × n_k`) be independent Gaussian matrices with `n₀_k ≤ m_k`, `n₀_k < n_k`, `n₀_k → ∞`
and `n₀_k / m_k → γ ∈ (0, 1)`. Then `conditionalRisk` converges in probability to the OLS variance
`σ² γ / (1 - γ)`: the estimator is unbiased once `S Sᵀ` and `Xᵀ X` are invertible. -/
private theorem tendsto_measure_ambientRisk_deviation_of_forall
    {mm nn n0 : ℕ → ℕ} {γ : ℝ} (σ_sq : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hn0 : ∀ k, 0 < n0 k) (hn0m : ∀ k, n0 k ≤ mm k)
    (hn0n : ∀ k, n0 k < nn k) (hn0top : Tendsto n0 atTop atTop)
    (hγ : Tendsto (fun k => (n0 k : ℝ) / (mm k : ℝ)) atTop (𝓝 γ))
    (θ : ∀ k, Fin (n0 k) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k =>
      ((Measure.pi fun _ : Fin (mm k) => Measure.pi fun _ : Fin (n0 k) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (n0 k) => Measure.pi fun _ : Fin (nn k) => gaussianReal 0 1))
        {x | ε ≤ |conditionalRisk σ_sq (θ k) (Matrix.of x.1) (Matrix.of x.2) -
          σ_sq * (γ / (1 - γ))|}) atTop (𝓝 0) := by
  set c : ℝ := γ / (1 - γ) with hcdef
  have hc : 0 < c := div_pos hγ0 (by linarith)
  set η : ℝ := min (ε / (|σ_sq| + 1)) c with hηdef
  have hη : 0 < η := lt_min (by positivity) hc
  have hmtop : Tendsto mm atTop atTop := tendsto_atTop_mono hn0m hn0top
  have h7d := tendsto_measure_trace_inv_gram_deviation hγ1 hn0 hn0m hmtop hγ hη
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h7d
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun k => ?_)
  set μX := Measure.pi fun _ : Fin (mm k) => Measure.pi fun _ : Fin (n0 k) => gaussianReal 0 1
    with hμX
  set μS := Measure.pi fun _ : Fin (n0 k) => Measure.pi fun _ : Fin (nn k) => gaussianReal 0 1
    with hμS
  have hX1 : IsProbabilityMeasure μX := by rw [hμX]; infer_instance
  have hS1 : IsProbabilityMeasure μS := by rw [hμS]; infer_instance
  have hae : ∀ᵐ x ∂(μX.prod μS), IsUnit (Matrix.of x.2 * (Matrix.of x.2)ᵀ).det :=
    (measurePreserving_snd (μ := μX) (ν := μS)).quasiMeasurePreserving.ae
      (ae_isUnit_det_mul_transpose_gaussianMatrix (hn0n k).le)
  have hmT : Measurable fun a : Fin (mm k) → Fin (n0 k) → ℝ =>
      ((Matrix.of a)ᵀ * Matrix.of a)⁻¹.trace := measurable_matrix_trace (by fun_prop)
  calc (μX.prod μS) {x | ε ≤ |conditionalRisk σ_sq (θ k) (Matrix.of x.1) (Matrix.of x.2) -
          σ_sq * c|}
      ≤ (μX.prod μS) (Prod.fst ⁻¹' {a | η ≤ |((Matrix.of a)ᵀ * Matrix.of a)⁻¹.trace - c|}) := by
        refine measure_mono_ae ?_
        filter_upwards [hae] with x hx hbad
        simp only [Set.mem_ofPred_eq, Set.mem_preimage] at hbad ⊢
        by_contra hnot
        rw [not_le] at hnot
        have hTc : 0 < ((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹.trace := by
          have := (abs_lt.1 hnot).1
          have h2 : η ≤ c := min_le_right _ _
          linarith
        have hXu : IsUnit ((Matrix.of x.1)ᵀ * Matrix.of x.1).det :=
          isUnit_det_of_trace_inv_ne_zero _ hTc.ne'
        have hbr : ¬ nn k ≤ min (mm k) (n0 k) := fun h =>
          absurd ((min_le_right _ _).trans' h) (not_le.2 (hn0n k))
        rw [conditionalRisk_of_ambient σ_sq (θ k) _ _ hbr (le_min (hn0m k) (hn0n k).le) hXu hx]
          at hbad
        have e : σ_sq * ((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹.trace - σ_sq * c =
            σ_sq * (((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹.trace - c) := by ring
        rw [e, abs_mul] at hbad
        have hd := abs_nonneg (((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹.trace - c)
        have hηε : (|σ_sq| + 1) * η ≤ ε := by
          have := min_le_left (ε / (|σ_sq| + 1)) c
          calc (|σ_sq| + 1) * η ≤ (|σ_sq| + 1) * (ε / (|σ_sq| + 1)) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = ε := by field_simp
        nlinarith [abs_nonneg σ_sq, mul_lt_mul_of_pos_left hnot (by positivity :
          0 < |σ_sq| + 1)]
    _ = μX {a | η ≤ |((Matrix.of a)ᵀ * Matrix.of a)⁻¹.trace - c|} :=
        (measurePreserving_fst (μ := μX) (ν := μS)).measure_preimage
          (measurableSet_le measurable_const
            (continuous_abs.measurable.comp (hmT.sub measurable_const))).nullMeasurableSet

end Regimes

section Ratios

/-- If `a_k / c_k → α` and `b_k / c_k → β ≠ 0` with `c_k > 0` eventually, then
`a_k / b_k → α / β`. -/
theorem tendsto_ratio_of_ratios {a b c : ℕ → ℕ} {α β : ℝ} (hβ : β ≠ 0)
    (hc : ∀ᶠ k in atTop, 0 < c k)
    (ha : Tendsto (fun k => (a k : ℝ) / (c k : ℝ)) atTop (𝓝 α))
    (hb : Tendsto (fun k => (b k : ℝ) / (c k : ℝ)) atTop (𝓝 β)) :
    Tendsto (fun k => (a k : ℝ) / (b k : ℝ)) atTop (𝓝 (α / β)) := by
  refine (ha.div hb hβ).congr' ?_
  filter_upwards [hc] with k hk
  have : (0 : ℝ) < c k := by exact_mod_cast hk
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ this.ne']

/-- A sequence of natural numbers whose ratio to a diverging one tends to a positive limit
diverges. -/
theorem tendsto_atTop_of_ratio {a c : ℕ → ℕ} {α : ℝ} (hα : 0 < α) (hc : Tendsto c atTop atTop)
    (ha : Tendsto (fun k => (a k : ℝ) / (c k : ℝ)) atTop (𝓝 α)) : Tendsto a atTop atTop := by
  have hcR : Tendsto (fun k => (c k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hc
  have h := ha.pos_mul_atTop hα hcR
  have h' : Tendsto (fun k => (a k : ℝ)) atTop atTop := by
    refine h.congr' ?_
    filter_upwards [hc.eventually_gt_atTop 0] with k hk
    have : (0 : ℝ) < c k := by exact_mod_cast hk
    field_simp
  exact tendsto_natCast_atTop_iff.1 h'

/-- `a_k / b_k → α < 1` forces `a_k < b_k` eventually. -/
theorem eventually_lt_of_ratio {a b : ℕ → ℕ} {α : ℝ} (hα : α < 1)
    (h : Tendsto (fun k => (a k : ℝ) / (b k : ℝ)) atTop (𝓝 α)) (hb : ∀ᶠ k in atTop, 0 < b k) :
    ∀ᶠ k in atTop, a k < b k := by
  filter_upwards [h.eventually (gt_mem_nhds hα), hb] with k hk hbk
  have : (0 : ℝ) < b k := by exact_mod_cast hbk
  rw [div_lt_one this] at hk
  exact_mod_cast hk

/-- `a_k / b_k → α > 1` forces `b_k < a_k` eventually. -/
theorem eventually_gt_of_ratio {a b : ℕ → ℕ} {α : ℝ} (hα : 1 < α)
    (h : Tendsto (fun k => (a k : ℝ) / (b k : ℝ)) atTop (𝓝 α)) (hb : ∀ᶠ k in atTop, 0 < b k) :
    ∀ᶠ k in atTop, b k < a k := by
  filter_upwards [h.eventually (lt_mem_nhds hα), hb] with k hk hbk
  have : (0 : ℝ) < b k := by exact_mod_cast hbk
  rw [one_lt_div this] at hk
  exact_mod_cast hk

end Ratios

section Eventually

/-- **Total risk in the feature-bottleneck regime, in probability, with the structural
hypotheses only eventually.** This is `tendsto_measure_featureRisk_deviation_of_forall` applied
to the sequences shifted by the index from which the dimension inequalities hold. -/
theorem tendsto_measure_featureRisk_deviation {mm nn n0 : ℕ → ℕ} {δ γ r : ℝ}
    (σ_sq : ℝ) (hδ1 : δ < 1) (hγ0 : 0 < γ) (hn : ∀ᶠ k in atTop, 0 < nn k)
    (hnm : ∀ᶠ k in atTop, nn k ≤ mm k) (hnn0 : ∀ᶠ k in atTop, nn k ≤ n0 k)
    (hnn : Tendsto nn atTop atTop)
    (hδ : Tendsto (fun k => (nn k : ℝ) / (mm k : ℝ)) atTop (𝓝 δ))
    (hγ : Tendsto (fun k => (n0 k : ℝ) / (mm k : ℝ)) atTop (𝓝 γ))
    (θ : ∀ k, Fin (n0 k) → ℝ) (hθ : Tendsto (fun k => θ k ⬝ᵥ θ k) atTop (𝓝 r)) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun k =>
      ((Measure.pi fun _ : Fin (mm k) => Measure.pi fun _ : Fin (n0 k) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (n0 k) => Measure.pi fun _ : Fin (nn k) => gaussianReal 0 1))
        {x | ε ≤ |conditionalRisk σ_sq (θ k) (Matrix.of x.1) (Matrix.of x.2) -
          ((γ - δ) / (γ * (1 - δ)) * r + σ_sq * (δ / (1 - δ)))|}) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((hn.and hnm).and hnn0)
  refine (tendsto_add_atTop_iff_nat K).1 ?_
  exact tendsto_measure_featureRisk_deviation_of_forall (mm := fun k => mm (k + K))
    (nn := fun k => nn (k + K)) (n0 := fun k => n0 (k + K)) σ_sq hδ1 hγ0
    (fun k => (hK (k + K) (by omega)).1.1) (fun k => (hK (k + K) (by omega)).1.2)
    (fun k => (hK (k + K) (by omega)).2) (hnn.comp (tendsto_add_atTop_nat K))
    (hδ.comp (tendsto_add_atTop_nat K)) (hγ.comp (tendsto_add_atTop_nat K))
    (fun k => θ (k + K)) (hθ.comp (tendsto_add_atTop_nat K)) hε

/-- **Total risk in the sample-bottleneck regime, in probability, with the structural
hypotheses only eventually.** This is `tendsto_measure_sampleRisk_deviation_of_forall` applied
to the sequences shifted by the index from which the dimension inequalities hold. -/
theorem tendsto_measure_sampleRisk_deviation {mm nn n0 : ℕ → ℕ} {γ δ r : ℝ}
    (σ_sq : ℝ) (hγ : 1 < γ) (hδ : 1 < δ) (hm : ∀ᶠ k in atTop, 0 < mm k)
    (hmn : ∀ᶠ k in atTop, mm k < nn k) (hmn0 : ∀ᶠ k in atTop, mm k < n0 k)
    (hmm : Tendsto mm atTop atTop)
    (hγ' : Tendsto (fun k => (n0 k : ℝ) / (mm k : ℝ)) atTop (𝓝 γ))
    (hδ' : Tendsto (fun k => (nn k : ℝ) / (mm k : ℝ)) atTop (𝓝 δ))
    (θ : ∀ k, Fin (n0 k) → ℝ) (hθ : Tendsto (fun k => θ k ⬝ᵥ θ k) atTop (𝓝 r)) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun k =>
      ((Measure.pi fun _ : Fin (mm k) => Measure.pi fun _ : Fin (n0 k) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (n0 k) => Measure.pi fun _ : Fin (nn k) => gaussianReal 0 1))
        {x | ε ≤ |conditionalRisk σ_sq (θ k) (Matrix.of x.1) (Matrix.of x.2) -
          ((1 - γ⁻¹) * (δ / (δ - 1)) * r + σ_sq * ((γ - 1)⁻¹ + (δ - 1)⁻¹))|}) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((hm.and hmn).and hmn0)
  refine (tendsto_add_atTop_iff_nat K).1 ?_
  exact tendsto_measure_sampleRisk_deviation_of_forall (mm := fun k => mm (k + K))
    (nn := fun k => nn (k + K)) (n0 := fun k => n0 (k + K)) σ_sq hγ hδ
    (fun k => (hK (k + K) (by omega)).1.1) (fun k => (hK (k + K) (by omega)).1.2)
    (fun k => (hK (k + K) (by omega)).2) (hmm.comp (tendsto_add_atTop_nat K))
    (hγ'.comp (tendsto_add_atTop_nat K)) (hδ'.comp (tendsto_add_atTop_nat K))
    (fun k => θ (k + K)) (hθ.comp (tendsto_add_atTop_nat K)) hε

/-- **Total risk in the ambient-bottleneck regime, in probability, with the structural
hypotheses only eventually.** This is `tendsto_measure_ambientRisk_deviation_of_forall` applied
to the sequences shifted by the index from which the dimension inequalities hold. -/
theorem tendsto_measure_ambientRisk_deviation {mm nn n0 : ℕ → ℕ} {γ : ℝ}
    (σ_sq : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hn0 : ∀ᶠ k in atTop, 0 < n0 k)
    (hn0m : ∀ᶠ k in atTop, n0 k ≤ mm k) (hn0n : ∀ᶠ k in atTop, n0 k < nn k)
    (hn0top : Tendsto n0 atTop atTop)
    (hγ : Tendsto (fun k => (n0 k : ℝ) / (mm k : ℝ)) atTop (𝓝 γ))
    (θ : ∀ k, Fin (n0 k) → ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k =>
      ((Measure.pi fun _ : Fin (mm k) => Measure.pi fun _ : Fin (n0 k) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (n0 k) => Measure.pi fun _ : Fin (nn k) => gaussianReal 0 1))
        {x | ε ≤ |conditionalRisk σ_sq (θ k) (Matrix.of x.1) (Matrix.of x.2) -
          σ_sq * (γ / (1 - γ))|}) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 ((hn0.and hn0m).and hn0n)
  refine (tendsto_add_atTop_iff_nat K).1 ?_
  exact tendsto_measure_ambientRisk_deviation_of_forall (mm := fun k => mm (k + K))
    (nn := fun k => nn (k + K)) (n0 := fun k => n0 (k + K)) σ_sq hγ0 hγ1
    (fun k => (hK (k + K) (by omega)).1.1) (fun k => (hK (k + K) (by omega)).1.2)
    (fun k => (hK (k + K) (by omega)).2) (hn0top.comp (tendsto_add_atTop_nat K))
    (hγ.comp (tendsto_add_atTop_nat K)) (fun k => θ (k + K)) hε

end Eventually

section Global

/-- **Theorem 3.1 (global double descent of the risk, in probability).** Let `m_k → ∞` samples,
`n₀_k` ambient dimensions and `n_k` random features with `n₀_k / m_k → γ > 0`, `n_k / m_k → δ > 0`
and `‖θ_k‖² → ρ`, in the non-singular domain
`δ < min {1, γ}` (feature bottleneck), `γ < 1`, `γ ≤ δ` (ambient bottleneck) or `1 < γ`, `1 < δ`
(sample bottleneck). For independent Gaussian `X_k ∈ ℝ^{m_k × n₀_k}`, `S_k ∈ ℝ^{n₀_k × n_k}`, the
expected squared error `conditionalRisk σ² θ_k X_k S_k` of the minimum-norm random-feature estimator
converges in probability to `asymptoticTotalRisk σ² ρ γ δ`:
for every `ε > 0` the probability that they differ by `ε` or more tends to `0`.

On the diagonal `γ = δ < 1` the two formulas (feature and ambient) agree, and the proof applies one
of them; we assume that `n_k ≤ n₀_k` eventually or `n₀_k < n_k` eventually there (otherwise split
the index set). The excluded singular set is `{γ ≥ 1, δ ≥ 1, γ = 1 ∨ δ = 1}`, where the limit is
infinite (the interpolation peak). -/
theorem double_descent_total_risk_convergence {mm nn n0 : ℕ → ℕ} {γ δ ρ : ℝ} (σ_sq : ℝ)
    (hγ0 : 0 < γ) (hδ0 : 0 < δ)
    (hdom : δ < min 1 γ ∨ (γ < 1 ∧ γ ≤ δ) ∨ (1 < γ ∧ 1 < δ))
    (hord : γ = δ → γ < 1 → (∀ᶠ k in atTop, nn k ≤ n0 k) ∨ (∀ᶠ k in atTop, n0 k < nn k))
    (hmm : Tendsto mm atTop atTop)
    (hγ' : Tendsto (fun k => (n0 k : ℝ) / (mm k : ℝ)) atTop (𝓝 γ))
    (hδ' : Tendsto (fun k => (nn k : ℝ) / (mm k : ℝ)) atTop (𝓝 δ))
    (θ : ∀ k, Fin (n0 k) → ℝ) (hθ : Tendsto (fun k => θ k ⬝ᵥ θ k) atTop (𝓝 ρ)) {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto (fun k =>
      ((Measure.pi fun _ : Fin (mm k) => Measure.pi fun _ : Fin (n0 k) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (n0 k) => Measure.pi fun _ : Fin (nn k) => gaussianReal 0 1))
        {x | ε ≤ |conditionalRisk σ_sq (θ k) (Matrix.of x.1) (Matrix.of x.2) -
          asymptoticTotalRisk σ_sq ρ γ δ|}) atTop (𝓝 0) := by
  have hmpos : ∀ᶠ k in atTop, 0 < mm k := hmm.eventually_gt_atTop 0
  have hn0top : Tendsto n0 atTop atTop := tendsto_atTop_of_ratio hγ0 hmm hγ'
  have hnntop : Tendsto nn atTop atTop := tendsto_atTop_of_ratio hδ0 hmm hδ'
  have hn0pos : ∀ᶠ k in atTop, 0 < n0 k := hn0top.eventually_gt_atTop 0
  have hnnpos : ∀ᶠ k in atTop, 0 < nn k := hnntop.eventually_gt_atTop 0
  rcases hdom with h | ⟨hγ1, hγδ⟩ | ⟨hγ1, hδ1⟩
  · -- feature bottleneck
    have hδ1 : δ < 1 := lt_of_lt_of_le h (min_le_left _ _)
    have hδγ : δ < γ := lt_of_lt_of_le h (min_le_right _ _)
    have hnm : ∀ᶠ k in atTop, nn k ≤ mm k :=
      (eventually_lt_of_ratio hδ1 hδ' hmpos).mono fun k hk => hk.le
    have hnn0 : ∀ᶠ k in atTop, nn k ≤ n0 k :=
      (eventually_lt_of_ratio ((div_lt_one hγ0).2 hδγ)
        (tendsto_ratio_of_ratios hγ0.ne' hmpos hδ' hγ') hn0pos).mono fun k hk => hk.le
    have e : asymptoticTotalRisk σ_sq ρ γ δ =
        (γ - δ) / (γ * (1 - δ)) * ρ + σ_sq * (δ / (1 - δ)) := by
      unfold asymptoticTotalRisk
      rw [asymptoticBias_of_feature ρ h, asymptoticVariance_of_feature σ_sq h]
    rw [e]
    exact tendsto_measure_featureRisk_deviation σ_sq hδ1 hγ0 hnnpos hnm hnn0
      hnntop hδ' hγ' θ hθ hε
  · -- ambient bottleneck
    have e : asymptoticTotalRisk σ_sq ρ γ δ = σ_sq * (γ / (1 - γ)) := by
      unfold asymptoticTotalRisk
      rw [asymptoticBias_of_ambient ρ hγ1 hγδ, asymptoticVariance_of_ambient σ_sq hγ1 hγδ,
        zero_add]
    have hn0m : ∀ᶠ k in atTop, n0 k ≤ mm k :=
      (eventually_lt_of_ratio hγ1 hγ' hmpos).mono fun k hk => hk.le
    rcases hγδ.lt_or_eq with hlt | heq
    · have hn0n : ∀ᶠ k in atTop, n0 k < nn k :=
        eventually_lt_of_ratio ((div_lt_one hδ0).2 hlt)
          (tendsto_ratio_of_ratios hδ0.ne' hmpos hγ' hδ') hnnpos
      rw [e]
      exact tendsto_measure_ambientRisk_deviation σ_sq hγ0 hγ1 hn0pos hn0m hn0n
        hn0top hγ' θ hε
    · rcases hord heq hγ1 with hle | hlt'
      · -- diagonal, feature side
        have hδ1 : δ < 1 := heq ▸ hγ1
        have hnm : ∀ᶠ k in atTop, nn k ≤ mm k :=
          (eventually_lt_of_ratio hδ1 hδ' hmpos).mono fun k hk => hk.le
        have := tendsto_measure_featureRisk_deviation (r := ρ) σ_sq hδ1 hγ0
          hnnpos hnm hle hnntop hδ' hγ' θ hθ hε
        rw [e]
        simpa [heq] using this
      · rw [e]
        exact tendsto_measure_ambientRisk_deviation σ_sq hγ0 hγ1 hn0pos hn0m hlt'
          hn0top hγ' θ hε
  · -- sample bottleneck
    have e : asymptoticTotalRisk σ_sq ρ γ δ =
        (1 - γ⁻¹) * (δ / (δ - 1)) * ρ + σ_sq * ((γ - 1)⁻¹ + (δ - 1)⁻¹) := by
      unfold asymptoticTotalRisk
      rw [asymptoticBias_of_sample ρ hγ1.le hδ1.le, asymptoticVariance_of_sample σ_sq hγ1.le
        hδ1.le]
    rw [e]
    exact tendsto_measure_sampleRisk_deviation σ_sq hγ1 hδ1 hmpos
      (eventually_gt_of_ratio hδ1 hδ' hmpos) (eventually_gt_of_ratio hγ1 hγ' hmpos) hmm hγ' hδ'
      θ hθ hε

/-- **Theorem 3.1 for `LinearRegression.risk`.** The same convergence for the actual risk
`LinearRegression.risk 1 (P k) θ̂_k θ_k = E ‖θ̂_k - θ_k‖²` of `θ̂_k = M (X_k θ_k + ε)` under any
noise laws `P k` with mean `0` and covariance `σ² I`: by `risk_eq_conditionalRisk` the events
coincide with those of `double_descent_total_risk_convergence`, so the limit does not depend on
the noise law beyond `σ²`. -/
theorem double_descent_risk_convergence {mm nn n0 : ℕ → ℕ} {γ δ ρ : ℝ} (σ_sq : ℝ)
    (hγ0 : 0 < γ) (hδ0 : 0 < δ)
    (hdom : δ < min 1 γ ∨ (γ < 1 ∧ γ ≤ δ) ∨ (1 < γ ∧ 1 < δ))
    (hord : γ = δ → γ < 1 → (∀ᶠ k in atTop, nn k ≤ n0 k) ∨ (∀ᶠ k in atTop, n0 k < nn k))
    (hmm : Tendsto mm atTop atTop)
    (hγ' : Tendsto (fun k => (n0 k : ℝ) / (mm k : ℝ)) atTop (𝓝 γ))
    (hδ' : Tendsto (fun k => (nn k : ℝ) / (mm k : ℝ)) atTop (𝓝 δ))
    (θ : ∀ k, Fin (n0 k) → ℝ) (hθ : Tendsto (fun k => θ k ⬝ᵥ θ k) atTop (𝓝 ρ))
    (P : ∀ k, Measure (Fin (mm k) → ℝ)) [∀ k, IsProbabilityMeasure (P k)]
    (hmem : ∀ k i, MemLp (fun e : Fin (mm k) → ℝ => e i) 2 (P k))
    (hmean : ∀ k i, ∫ e, e i ∂P k = 0)
    (hcov : ∀ k i j, ∫ e, e i * e j ∂P k = if i = j then σ_sq else 0) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k =>
      ((Measure.pi fun _ : Fin (mm k) => Measure.pi fun _ : Fin (n0 k) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (n0 k) => Measure.pi fun _ : Fin (nn k) => gaussianReal 0 1))
        {x | ε ≤ |LinearRegression.risk 1 (P k) (fun e : Fin (mm k) → ℝ => (WithLp.toLp 2
          (minNormOperator (Matrix.of x.1) (Matrix.of x.2) *ᵥ (Matrix.of x.1 *ᵥ θ k + e)) :
            EuclideanSpace ℝ (Fin (n0 k)))) (WithLp.toLp 2 (θ k)) -
          asymptoticTotalRisk σ_sq ρ γ δ|}) atTop (𝓝 0) := by
  refine (double_descent_total_risk_convergence σ_sq hγ0 hδ0 hdom hord hmm hγ' hδ' θ hθ
    hε).congr fun k => ?_
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq]
  rw [risk_eq_conditionalRisk σ_sq (WithLp.toLp 2 (θ k)) (Matrix.of x.1) (Matrix.of x.2) (P k)
    (hmem k) (hmean k) (hcov k) _ (fun e => rfl)]

end Global

end LinearRegression.DoubleDescent

end
