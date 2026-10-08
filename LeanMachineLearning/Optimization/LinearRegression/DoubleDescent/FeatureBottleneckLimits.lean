/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.ProdBound
public import LeanMachineLearning.ForMathlib.Topology.Instances.ENNReal.Lemmas
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.FeatureBottleneck
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.FitErrorConcentration

/-!
# Probabilistic limits in the feature-bottleneck regime (Milestone 7f)

Random-feature regression with `X ∈ ℝ^{m×n₀}` and `S ∈ ℝ^{n₀×n}` independent Gaussian matrices,
`n ≤ min {m, n₀}` ([Bach, 2024]; [Hastie et al., 2022]; [Belkin et al., 2019]). With
`Z = X S`, `M = S (Zᵀ Z)⁻¹ Zᵀ`, the variance of `θ̂ = M y` is `σ² Tr ((Zᵀ Z)⁻¹ Sᵀ S)`
(`featureBottleneck_variance_eq_trace`) and its bias is `‖(M X - 1) θ‖²`. This file shows that
both converge in probability along `n / m → δ < 1`, `n₀ / m → γ > 0`, closing the probabilistic
inputs of Milestone 3b:

* `measure_trace_inv_gram_mul_gram_mem`, `tendsto_measure_featureTrace_deviation`: for *every* fixed
  `S` with `Sᵀ S` invertible, `Tr ((Zᵀ Z)⁻¹ Sᵀ S)` has the law of `Tr ((Gᵀ G)⁻¹)`, hence tends to
  `δ / (1 - δ)` in probability (Milestone 7d), so the variance tends to `σ² δ / (1 - δ)`;
* `measurePreserving_mulVec_mul_orthonormal`: `X u` and `X Q` are independent Gaussians when
  `Qᵀ Q = 1`, `Qᵀ u = 0`, `‖u‖ = 1`;
* `measure_featureBias_deviation_le`: for fixed `S`, the bias lies in
  `‖θ⊥‖² (1 + n (1 ∓ η) / (ν (1 ± η)))` except with the `X`-probability of
  `measure_fitError_deviation_le`, because `R_bias = ‖θ⊥‖² (1 + ‖(Gᵀ G)⁻¹ Gᵀ ζ‖²)`
  (`bias_eq_omitted_add_fit_error`) with `ζ = X θ⊥ / ‖θ⊥‖` independent of `G = X Q`;
* `measure_prod_sandwich_le`, `measure_featureBias_joint_le'`: the two-stage union bound over
  `(S, X)` with the `S`-event `‖(1 - P_S) θ‖² ≈ (1 - n/n₀) ‖θ‖²` of Milestone 7e;
* `tendsto_measure_featureBias_deviation`: the bias converges in probability to
  `(γ - δ) / (γ (1 - δ)) r` when `‖θ_k‖² → r`.

The ambient-bottleneck regime needs no new probability: its estimator is OLS, unbiased
(`ambientBottleneck_bias_variance`), with variance `σ² Tr ((Xᵀ X)⁻¹)`, and
`tendsto_measure_trace_inv_gram_deviation` with `p := m`, `m := n₀` gives `σ² γ / (1 - γ)`.
-/

@[expose]
public section

namespace LinearRegression.DoubleDescent

open MeasureTheory ProbabilityTheory Matrix NTK Filter Topology
open scoped Matrix

private theorem measurable_trace_inv_gram {p q : ℕ} :
    Measurable fun W : Fin p → Fin q → ℝ => ((Matrix.of W)ᵀ * Matrix.of W)⁻¹.trace := by
  have hW : Measurable fun W : Fin p → Fin q → ℝ => (Matrix.of W : Matrix (Fin p) (Fin q) ℝ) :=
    Measurable.of_eval_matrix _ fun i k => (measurable_pi_apply k).comp (measurable_pi_apply i)
  have h := measurable_matrix_nonsing_inv.comp
    (measurable_matrix_mul (measurable_matrix_transpose hW) hW)
  exact Finset.measurable_sum _ fun i _ => measurable_matrix_entry h i i

/-- **The variance trace of the feature-bottleneck estimator has the law of `Tr ((Gᵀ G)⁻¹)`.**
Let `S` be a fixed matrix with `Sᵀ S` invertible and `X` an `m × n₀` Gaussian matrix, `Z = X S`.
For every measurable set `B`, `ℙ (Tr ((Zᵀ Z)⁻¹ Sᵀ S) ∈ B) = ℙ (Tr ((Gᵀ G)⁻¹) ∈ B)` for `G` an
`m × n` Gaussian matrix. This is the QR trace reduction `trace_inv_gram_mul_gram_of_factor` for
`S = Q R` together with the orthogonal invariance `G = X Q` of `X`
(`map_gaussianMatrix_mul_orthonormal`); the feature covariance `Sᵀ S` drops out. -/
theorem measure_trace_inv_gram_mul_gram_mem {m n n₀ : ℕ} (S : Matrix (Fin n₀) (Fin n) ℝ)
    (hS : IsUnit (Sᵀ * S).det) {B : Set ℝ} (hB : MeasurableSet B) :
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n₀ => gaussianReal 0 1)
        {X | (((Matrix.of X * S)ᵀ * (Matrix.of X * S))⁻¹ * (Sᵀ * S)).trace ∈ B} =
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => gaussianReal 0 1)
        {G | ((Matrix.of G)ᵀ * Matrix.of G)⁻¹.trace ∈ B} := by
  obtain ⟨Q, R, hQ, hR, -, hSQR⟩ := exists_orthonormal_factor S hS
  have hmap := map_gaussianMatrix_mul_orthonormal (ρ := Fin m) Q hQ
  have hrot : Measurable fun X : Fin m → Fin n₀ → ℝ => fun i k => (Matrix.of X * Q) i k := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp (measurable_pi_apply i)).mul_const _
  have hset : MeasurableSet {G : Fin m → Fin n → ℝ |
      ((Matrix.of G)ᵀ * Matrix.of G)⁻¹.trace ∈ B} := measurable_trace_inv_gram hB
  conv_rhs => rw [← hmap, Measure.map_apply hrot hset]
  congr 1
  ext X
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [hSQR, trace_inv_gram_mul_gram_of_factor (Matrix.of X) Q R hQ hR]
  rfl

/-- **Variance in the feature-bottleneck regime, in probability (Milestone 3b, variance half).**
Let `X_k` be `m_k × n₀_k` Gaussian matrices and `S_k` any matrices with `S_kᵀ S_k` invertible and
`n_k` columns, `1 ≤ n_k ≤ m_k`, `m_k → ∞`, `n_k / m_k → δ < 1`. Then for `Z_k = X_k S_k` and every
`ε > 0`,
`ℙ (|Tr ((Z_kᵀ Z_k)⁻¹ S_kᵀ S_k) - δ / (1 - δ)| ≥ ε) → 0`.
The variance of the estimator is `σ²` times this trace (`featureBottleneck_variance_eq_trace`),
so it converges in probability to `σ² δ / (1 - δ)`. The matrices `S_k` are arbitrary: neither
the law of `S` nor its independence from `X` is used, only `Sᵀ S` invertible. -/
theorem tendsto_measure_featureTrace_deviation {mm nn n0 : ℕ → ℕ} {ρ : ℝ} (hρ1 : ρ < 1)
    (hn : ∀ k, 0 < nn k) (hnm : ∀ k, nn k ≤ mm k) (hm : Tendsto mm atTop atTop)
    (hr : Tendsto (fun k => (nn k : ℝ) / (mm k : ℝ)) atTop (𝓝 ρ))
    (S : ∀ k, Matrix (Fin (n0 k)) (Fin (nn k)) ℝ) (hS : ∀ k, IsUnit ((S k)ᵀ * S k).det)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k =>
      (Measure.pi fun _ : Fin (mm k) => Measure.pi fun _ : Fin (n0 k) => gaussianReal 0 1)
        {X | ε ≤ |(((Matrix.of X * S k)ᵀ * (Matrix.of X * S k))⁻¹ * ((S k)ᵀ * S k)).trace -
          ρ / (1 - ρ)|}) atTop (𝓝 0) := by
  refine (tendsto_measure_trace_inv_gram_deviation hρ1 hn hnm hm hr hε).congr fun k => ?_
  exact (measure_trace_inv_gram_mul_gram_mem (S k) (hS k)
    (B := {y : ℝ | ε ≤ |y - ρ / (1 - ρ)|}) (measurableSet_le measurable_const (by fun_prop))).symm

/-- **The Gram projector of an orthonormal factorization.** If `S = Q R` with `Qᵀ Q = 1` and `R`
invertible, then `P_S = Q Qᵀ`: the orthogonal projector onto `range S = range Q`. -/
theorem gramProjector_orthonormal_factor {n n₀ : ℕ} (Q : Matrix (Fin n₀) (Fin n) ℝ)
    (R : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ * Q = 1) (hR : IsUnit R.det) :
    gramProjector (Q * R) = Q * Qᵀ := by
  have hRT : IsUnit Rᵀ.det := isUnit_det_transpose _ hR
  have h1 : gramProjector R = 1 := by
    unfold gramProjector
    rw [Matrix.mul_inv_rev]
    rw [← Matrix.mul_assoc R R⁻¹, Matrix.mul_nonsing_inv _ hR, Matrix.one_mul,
      Matrix.nonsing_inv_mul _ hRT]
  rw [gramProjector_orthonormal_mul Q hQ R, h1, Matrix.mul_one]

/-- **Appending a unit vector to an orthonormal frame.** If `Qᵀ Q = 1` and `u` is a unit vector
orthogonal to the columns of `Q` (`Qᵀ u = 0`), then `[Q | u]` again has orthonormal columns. -/
theorem exists_orthonormal_snoc {ι : Type*} [Fintype ι] {n : ℕ} (Q : Matrix ι (Fin n) ℝ)
    (hQ : Qᵀ * Q = 1) (u : ι → ℝ) (hu : u ⬝ᵥ u = 1) (hQu : Qᵀ *ᵥ u = 0) :
    ∃ Qa : Matrix ι (Fin (n + 1)) ℝ, Qaᵀ * Qa = 1 ∧ (∀ i, Qa i (Fin.last n) = u i) ∧
      ∀ i k, Qa i k.castSucc = Q i k := by
  refine ⟨Matrix.of fun i c => Fin.lastCases (u i) (fun k => Q i k) c, ?_, fun i => by simp,
    fun i k => by simp⟩
  have hQe : ∀ k k' : Fin n, ∑ i, Q i k * Q i k' = if k = k' then 1 else 0 := fun k k' => by
    have := congrFun (congrFun hQ k) k'
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hue : ∀ k : Fin n, ∑ i, u i * Q i k = 0 := fun k => by
    have := congrFun hQu k
    simpa [Matrix.mulVec, dotProduct, mul_comm] using this
  ext c c'
  induction c using Fin.lastCases with
  | last =>
    induction c' using Fin.lastCases with
    | last => simpa [Matrix.mul_apply, Matrix.one_apply, dotProduct] using hu
    | cast k' => simp [Matrix.mul_apply, (Fin.castSucc_lt_last k').ne', hue]
  | cast k =>
    induction c' using Fin.lastCases with
    | last =>
      simp [Matrix.mul_apply, (Fin.castSucc_lt_last k).ne]
      simpa [mul_comm] using hue k
    | cast k' => simpa [Matrix.mul_apply, Matrix.one_apply] using hQe k k'

/-- **A Gaussian matrix against an orthonormal frame and one more direction.** If `X` has i.i.d.
standard normal entries, `Qᵀ Q = 1`, and `u` is a unit vector orthogonal to the columns of `Q`,
then `X u` and `X Q` are independent: `X u` is a standard Gaussian vector and `X Q` a Gaussian
matrix.

Proof: `[Q | u]` has orthonormal columns, so `X [Q | u]` is Gaussian
(`map_gaussianMatrix_mul_orthonormal`), and its last column is independent of the others
(`measurePreserving_columnSplit`). -/
theorem measurePreserving_mulVec_mul_orthonormal {m n₀ n : ℕ}
    (Q : Matrix (Fin n₀) (Fin n) ℝ) (hQ : Qᵀ * Q = 1) (u : Fin n₀ → ℝ) (hu : u ⬝ᵥ u = 1)
    (hQu : Qᵀ *ᵥ u = 0) :
    MeasurePreserving
      (fun X : Fin m → Fin n₀ → ℝ => (Matrix.of X *ᵥ u, fun i k => (Matrix.of X * Q) i k))
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n₀ => gaussianReal 0 1)
      ((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => gaussianReal 0 1)) := by
  obtain ⟨Qa, hQa, hlast, hcast⟩ := exists_orthonormal_snoc Q hQ u hu hQu
  have hrot : Measurable fun X : Fin m → Fin n₀ → ℝ => fun i k => (Matrix.of X * Qa) i k := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp (measurable_pi_apply i)).mul_const _
  have h1 : MeasurePreserving (fun X : Fin m → Fin n₀ → ℝ => fun i k => (Matrix.of X * Qa) i k)
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n₀ => gaussianReal 0 1)
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) :=
    ⟨hrot, map_gaussianMatrix_mul_orthonormal (ρ := Fin m) Qa hQa⟩
  have h2 := measurePreserving_columnSplit (p := m) (q := n) (Fin.last n)
  convert h2.comp h1 using 1
  funext X
  refine Prod.ext ?_ ?_
  · funext i
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hlast]
  · funext i k
    simp [Matrix.mul_apply, hcast, Fin.succAbove_last]

/-- **Fit error of the random-feature estimator in an orthonormal frame, `X`-probability.**
Let `S` (`n₀ × n`) have `Sᵀ S` invertible, `X` an `m × n₀` Gaussian matrix, `θ ∈ ℝ^{n₀}`, and put
`θ⊥ = (1 - P_S) θ`, `Z = X S`, `M = S (Zᵀ Z)⁻¹ Zᵀ`. Writing `R_bias = ‖(M X - 1) θ‖²`,
`ν = m - n + 1` and `0 < η < 1`, the bias lies in
`[‖θ⊥‖² (1 + n (1 - η) / (ν (1 + η))), ‖θ⊥‖² (1 + n (1 + η) / (ν (1 - η)))]` except on an event
of `X`-probability at most `60 / (η⁴ ν²) + 60 / (η⁴ n²)`, whatever `S` and `θ` are.

Proof: `bias_eq_omitted_add_fit_error` gives `R_bias = ‖θ⊥‖² + ‖(Gᵀ G)⁻¹ Gᵀ (X θ⊥)‖²` with
`G = X Q`, and `X θ⊥ = ‖θ⊥‖ · ζ` with `ζ = X u`, `u = θ⊥ / ‖θ⊥‖ ⟂ Q`. By
`measurePreserving_mulVec_mul_orthonormal`, `(G, ζ)` are independent Gaussians, and the fit error
`‖(Gᵀ G)⁻¹ Gᵀ ζ‖²` concentrates by `measure_fitError_deviation_le`. -/
theorem measure_featureBias_deviation_le {m q n₀ : ℕ} (hqm : q + 1 ≤ m)
    (S : Matrix (Fin n₀) (Fin (q + 1)) ℝ) (hS : IsUnit (Sᵀ * S).det) (θ : Fin n₀ → ℝ)
    (Rb : (Fin m → Fin n₀ → ℝ) → ℝ)
    (hRb : ∀ X, Rb X = ((S * (((Matrix.of X * S)ᵀ * (Matrix.of X * S))⁻¹ *
        (Matrix.of X * S)ᵀ)) * Matrix.of X - 1) *ᵥ θ ⬝ᵥ
          ((S * (((Matrix.of X * S)ᵀ * (Matrix.of X * S))⁻¹ * (Matrix.of X * S)ᵀ)) *
            Matrix.of X - 1) *ᵥ θ) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n₀ => gaussianReal 0 1)
        {X | ¬ (((1 - gramProjector S) *ᵥ θ) ⬝ᵥ ((1 - gramProjector S) *ᵥ θ) *
              (1 + ((q + 1 : ℕ) : ℝ) * (1 - η) / (((m - q : ℕ) : ℝ) * (1 + η))) ≤ Rb X ∧
            Rb X ≤ ((1 - gramProjector S) *ᵥ θ) ⬝ᵥ ((1 - gramProjector S) *ᵥ θ) *
              (1 + ((q + 1 : ℕ) : ℝ) * (1 + η) / (((m - q : ℕ) : ℝ) * (1 - η))))} ≤
      ENNReal.ofReal (60 / (η ^ 4 * ((m - q : ℕ) : ℝ) ^ 2)) +
        ENNReal.ofReal (60 / (η ^ 4 * ((q + 1 : ℕ) : ℝ) ^ 2)) := by
  obtain ⟨Q, R, hQ, hR, hRT, hSQR⟩ := exists_orthonormal_factor S hS
  subst hSQR
  set μX := Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n₀ => gaussianReal 0 1 with hμX
  have hP : gramProjector (Q * R) = Q * Qᵀ := gramProjector_orthonormal_factor Q R hQ hR
  set θp : Fin n₀ → ℝ := (1 - gramProjector (Q * R)) *ᵥ θ with hθpdef
  have hθp : θp = θ - Q *ᵥ (Qᵀ *ᵥ θ) := by
    rw [hθpdef, hP, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
  have hQθp : Qᵀ *ᵥ θp = 0 := by
    rw [hθp, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec, sub_self]
  -- almost surely the frame `G = X Q` has full column rank
  have hrot : Measurable fun X : Fin m → Fin n₀ → ℝ => fun i k => (Matrix.of X * Q) i k := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp (measurable_pi_apply i)).mul_const _
  have hunit : ∀ᵐ X ∂μX, IsUnit ((Matrix.of X * Q)ᵀ * (Matrix.of X * Q)).det := by
    refine ae_of_ae_map (p := fun G : Fin m → Fin (q + 1) → ℝ =>
      IsUnit ((Matrix.of G)ᵀ * Matrix.of G).det) hrot.aemeasurable ?_
    rw [map_gaussianMatrix_mul_orthonormal (ρ := Fin m) Q hQ]
    exact ae_isUnit_det_gram_gaussianMatrix (q + 1) m hqm
  have hbias : ∀ X, IsUnit ((Matrix.of X * Q)ᵀ * (Matrix.of X * Q)).det →
      Rb X = θp ⬝ᵥ θp + ((((Matrix.of X * Q)ᵀ * (Matrix.of X * Q))⁻¹ * (Matrix.of X * Q)ᵀ) *ᵥ
          (Matrix.of X *ᵥ θp)) ⬝ᵥ ((((Matrix.of X * Q)ᵀ * (Matrix.of X * Q))⁻¹ *
            (Matrix.of X * Q)ᵀ) *ᵥ (Matrix.of X *ᵥ θp)) := fun X hX => by
    rw [hRb X]
    exact bias_eq_omitted_add_fit_error (Matrix.of X) Q R hQ hR hX _ rfl θ θp hθp
  by_cases hθ0 : θp = 0
  · -- no omitted signal: the bias vanishes a.s. and the event is null
    have hnull : μX {X | ¬ IsUnit ((Matrix.of X * Q)ᵀ * (Matrix.of X * Q)).det} = 0 :=
      measure_eq_zero_iff_ae_notMem.2 (hunit.mono fun X hX hn => hn hX)
    refine le_of_eq_of_le (measure_mono_null (fun X hX => ?_) hnull) bot_le
    by_contra hU
    simp only [Set.mem_ofPred_eq, not_not] at hU
    apply hX
    have h0 := hbias X hU
    rw [hθ0, Matrix.mulVec_zero, Matrix.mulVec_zero, dotProduct_zero, dotProduct_zero,
      add_zero] at h0
    rw [hθ0] at *
    simp [h0]
  have hpos : 0 < θp ⬝ᵥ θp := lt_of_le_of_ne (by
    rw [← star_trivial θp]; exact dotProduct_star_self_nonneg θp)
    (fun h => hθ0 (dotProduct_self_eq_zero.1 h.symm))
  set s : ℝ := Real.sqrt (θp ⬝ᵥ θp) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hpos
  have hss : s * s = θp ⬝ᵥ θp := Real.mul_self_sqrt hpos.le
  set u : Fin n₀ → ℝ := s⁻¹ • θp with hu
  have huu : u ⬝ᵥ u = 1 := by
    rw [hu, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hss]
    field_simp
  have hQu : Qᵀ *ᵥ u = 0 := by rw [hu, Matrix.mulVec_smul, hQθp, smul_zero]
  have hθpu : θp = s • u := by rw [hu, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
  have hmp := measurePreserving_mulVec_mul_orthonormal (m := m) Q hQ u huu hQu
  have hmp' := (Measure.measurePreserving_swap (μ := Measure.pi fun _ : Fin m => gaussianReal 0 1)
    (ν := Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1)).comp hmp
  have hnull : μX {X | ¬ IsUnit ((Matrix.of X * Q)ᵀ * (Matrix.of X * Q)).det} = 0 :=
    measure_eq_zero_iff_ae_notMem.2 (hunit.mono fun X hX hn => hn hX)
  set c₁ : ℝ := ((q + 1 : ℕ) : ℝ) * (1 - η) / (((m - q : ℕ) : ℝ) * (1 + η)) with hc₁
  set c₂ : ℝ := ((q + 1 : ℕ) : ℝ) * (1 + η) / (((m - q : ℕ) : ℝ) * (1 - η)) with hc₂
  have hEm := measurableSet_not_le_le_fitError (m := m) (n := q + 1) c₁ c₂
  have hpre := hmp'.measure_preimage hEm.nullMeasurableSet
  have hbound := measure_fitError_deviation_le hqm hη hη1
  have hsub : {X | ¬ (θp ⬝ᵥ θp * (1 + c₁) ≤ Rb X ∧ Rb X ≤ θp ⬝ᵥ θp * (1 + c₂))} ⊆
      ((fun X : Fin m → Fin n₀ → ℝ => ((fun i k => (Matrix.of X * Q) i k, Matrix.of X *ᵥ u) :
        (Fin m → Fin (q + 1) → ℝ) × (Fin m → ℝ))) ⁻¹'
        {x : (Fin m → Fin (q + 1) → ℝ) × (Fin m → ℝ) |
          ¬ (c₁ ≤ ((((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ * (Matrix.of x.1)ᵀ) *ᵥ x.2) ⬝ᵥ
                ((((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ * (Matrix.of x.1)ᵀ) *ᵥ x.2) ∧
            ((((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ * (Matrix.of x.1)ᵀ) *ᵥ x.2) ⬝ᵥ
                ((((Matrix.of x.1)ᵀ * Matrix.of x.1)⁻¹ * (Matrix.of x.1)ᵀ) *ᵥ x.2) ≤ c₂)}) ∪
      {X | ¬ IsUnit ((Matrix.of X * Q)ᵀ * (Matrix.of X * Q)).det} := by
    intro X hX
    by_cases hU : IsUnit ((Matrix.of X * Q)ᵀ * (Matrix.of X * Q)).det
    · left
      simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hX ⊢
      intro ⟨h1, h2⟩
      apply hX
      set T := ((((Matrix.of X * Q)ᵀ * (Matrix.of X * Q))⁻¹ * (Matrix.of X * Q)ᵀ) *ᵥ
        (Matrix.of X *ᵥ u)) ⬝ᵥ ((((Matrix.of X * Q)ᵀ * (Matrix.of X * Q))⁻¹ *
          (Matrix.of X * Q)ᵀ) *ᵥ (Matrix.of X *ᵥ u)) with hT
      have hXu : Matrix.of X *ᵥ θp = s • (Matrix.of X *ᵥ u) := by
        conv_lhs => rw [hθpu]
        rw [Matrix.mulVec_smul]
      have hRbX : Rb X = θp ⬝ᵥ θp * (1 + T) := by
        rw [hbias X hU, hXu, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
          smul_eq_mul, ← hss]
        ring
      rw [hRbX]
      have h1' : c₁ ≤ T := h1
      have h2' : T ≤ c₂ := h2
      exact ⟨mul_le_mul_of_nonneg_left (by linarith) hpos.le,
        mul_le_mul_of_nonneg_left (by linarith) hpos.le⟩
    · right; exact hU
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hnull, add_zero]
  refine le_trans (le_of_eq ?_) hbound
  exact hpre

/-- Joint measurability of the bias `‖(M X - 1) θ‖²`, `M = S (Zᵀ Z)⁻¹ Zᵀ`, `Z = X S`, in
`(S, X)`. -/
theorem measurable_featureBias {m n n₀ : ℕ} (θ : Fin n₀ → ℝ) :
    Measurable fun x : (Fin n₀ → Fin n → ℝ) × (Fin m → Fin n₀ → ℝ) =>
      ((Matrix.of x.1 * (((Matrix.of x.2 * Matrix.of x.1)ᵀ *
        (Matrix.of x.2 * Matrix.of x.1))⁻¹ * (Matrix.of x.2 * Matrix.of x.1)ᵀ)) *
          Matrix.of x.2 - 1) *ᵥ θ ⬝ᵥ ((Matrix.of x.1 * (((Matrix.of x.2 * Matrix.of x.1)ᵀ *
            (Matrix.of x.2 * Matrix.of x.1))⁻¹ * (Matrix.of x.2 * Matrix.of x.1)ᵀ)) *
              Matrix.of x.2 - 1) *ᵥ θ := by
  have hS : Measurable fun x : (Fin n₀ → Fin n → ℝ) × (Fin m → Fin n₀ → ℝ) =>
      (Matrix.of x.1 : Matrix (Fin n₀) (Fin n) ℝ) :=
    Measurable.of_eval_matrix _ fun i k =>
      (measurable_pi_apply k).comp ((measurable_pi_apply i).comp measurable_fst)
  have hX : Measurable fun x : (Fin n₀ → Fin n → ℝ) × (Fin m → Fin n₀ → ℝ) =>
      (Matrix.of x.2 : Matrix (Fin m) (Fin n₀) ℝ) :=
    Measurable.of_eval_matrix _ fun i k =>
      (measurable_pi_apply k).comp ((measurable_pi_apply i).comp measurable_snd)
  have hZ := measurable_matrix_mul hX hS
  have hInv := measurable_matrix_nonsing_inv.comp
    (measurable_matrix_mul (measurable_matrix_transpose hZ) hZ)
  have hM := measurable_matrix_mul hS (measurable_matrix_mul hInv (measurable_matrix_transpose hZ))
  have hMX := measurable_matrix_mul hM hX
  have hD : Measurable fun x : (Fin n₀ → Fin n → ℝ) × (Fin m → Fin n₀ → ℝ) =>
      ((Matrix.of x.1 * (((Matrix.of x.2 * Matrix.of x.1)ᵀ * (Matrix.of x.2 * Matrix.of x.1))⁻¹ *
        (Matrix.of x.2 * Matrix.of x.1)ᵀ)) * Matrix.of x.2 - 1 : Matrix (Fin n₀) (Fin n₀) ℝ) :=
    Measurable.of_eval_matrix _ fun i j => by
      simp only [Matrix.sub_apply]
      exact (measurable_matrix_entry hMX i j).sub measurable_const
  have hv := measurable_mulVec hD (measurable_const (a := θ))
  exact measurable_dotProduct hv hv

/-- **Two-stage union bound for a product of probability spaces.** Let `s2` and `Rb` be measurable,
`c₁, c₂ ≥ 0`. If for `μS`-a.e. `S` the section `{X | ¬ (s2 S (1 + c₁) ≤ Rb (S, X) ≤ s2 S (1 + c₂))}`
has `μX`-measure at most `b`, then the product event
`¬ ((a - ε₁)(1 + c₁) ≤ Rb ≤ (a + ε₁)(1 + c₂))` has `μS ⊗ μX`-measure at most
`μS (ε₁ ≤ |s2 - a|) + b`: either `s2` is far from `a`, or `Rb` leaves its sandwich given `S`. -/
theorem measure_prod_sandwich_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μS : Measure α) [IsProbabilityMeasure μS] (μX : Measure β) [IsProbabilityMeasure μX]
    {s2 : α → ℝ} {Rb : α × β → ℝ} (hs2 : Measurable s2) (hRb : Measurable Rb)
    {a c₁ c₂ ε₁ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) {b : ENNReal}
    (hsec : ∀ᵐ S ∂μS, μX {X | ¬ (s2 S * (1 + c₁) ≤ Rb (S, X) ∧
      Rb (S, X) ≤ s2 S * (1 + c₂))} ≤ b) :
    (μS.prod μX) {x | ¬ ((a - ε₁) * (1 + c₁) ≤ Rb x ∧ Rb x ≤ (a + ε₁) * (1 + c₂))} ≤
      μS {S | ε₁ ≤ |s2 S - a|} + b := by
  have hSm : MeasurableSet {S : α | ε₁ ≤ |s2 S - a|} :=
    measurableSet_le measurable_const (by fun_prop)
  have hBm : MeasurableSet {x : α × β | ¬ (s2 x.1 * (1 + c₁) ≤ Rb x ∧
      Rb x ≤ s2 x.1 * (1 + c₂))} := by
    have h1 : Measurable fun x : α × β => s2 x.1 * (1 + c₁) :=
      (hs2.comp measurable_fst).mul_const _
    have h2 : Measurable fun x : α × β => s2 x.1 * (1 + c₂) :=
      (hs2.comp measurable_fst).mul_const _
    exact ((measurableSet_le h1 hRb).inter (measurableSet_le hRb h2)).compl
  have hsub : {x : α × β | ¬ ((a - ε₁) * (1 + c₁) ≤ Rb x ∧ Rb x ≤ (a + ε₁) * (1 + c₂))} ⊆
      Prod.fst ⁻¹' {S : α | ε₁ ≤ |s2 S - a|} ∪
        {x : α × β | ¬ (s2 x.1 * (1 + c₁) ≤ Rb x ∧ Rb x ≤ s2 x.1 * (1 + c₂))} := by
    intro x hx
    by_contra hnot
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq, not_or, not_le,
      not_not] at hnot
    obtain ⟨h1, h2, h3⟩ := hnot
    apply hx
    have hab := abs_lt.1 h1
    exact ⟨le_trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith)) h2,
      le_trans h3 (mul_le_mul_of_nonneg_right (by linarith) (by linarith))⟩
  have hAm : (μS.prod μX) (Prod.fst ⁻¹' {S : α | ε₁ ≤ |s2 S - a|}) =
      μS {S | ε₁ ≤ |s2 S - a|} :=
    (measurePreserving_fst (μ := μS) (ν := μX)).measure_preimage hSm.nullMeasurableSet
  have hBb : (μS.prod μX) {x : α × β | ¬ (s2 x.1 * (1 + c₁) ≤ Rb x ∧
      Rb x ≤ s2 x.1 * (1 + c₂))} ≤ b :=
    measure_prod_le_of_ae_section_le μS μX hBm hsec
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ _ := by rw [hAm]; exact add_le_add le_rfl hBb

/-- **Joint concentration of the feature-bottleneck bias over `(S, X)`.** Let `S` be an `n₀ × n`
and `X` an independent `m × n₀` Gaussian matrix, `n = q + 1 ≤ min {m, n₀}`, `R_bias =
‖(M X - 1) θ‖²` with `M = S (Zᵀ Z)⁻¹ Zᵀ`, `Z = X S`, `a = (1 - n/n₀) ‖θ‖²`, `ν = m - n + 1`,
`0 < η < 1` and `ε₁ > 0`. Then `R_bias` lies in `[(a - ε₁)(1 + c₁), (a + ε₁)(1 + c₂)]`,
`c₁ = n (1 - η) / (ν (1 + η))`, `c₂ = n (1 + η) / (ν (1 - η))`, except on an event of probability at
most `ℙ_S (|‖(1 - P_S) θ‖² - a| ≥ ε₁) + 60 / (η⁴ ν²) + 60 / (η⁴ n²)`. The first term is
controlled by `tendsto_measure_resid_deviation` (Milestone 7e), the others by the sandwich bound
for the fit error. -/
theorem measure_featureBias_joint_le {m q n₀ : ℕ} (hqm : q + 1 ≤ m) (hqn : q + 1 ≤ n₀)
    (θ : Fin n₀ → ℝ)
    (Rb : (Fin n₀ → Fin (q + 1) → ℝ) × (Fin m → Fin n₀ → ℝ) → ℝ)
    (hRb : ∀ x, Rb x = ((Matrix.of x.1 * (((Matrix.of x.2 * Matrix.of x.1)ᵀ *
        (Matrix.of x.2 * Matrix.of x.1))⁻¹ * (Matrix.of x.2 * Matrix.of x.1)ᵀ)) *
          Matrix.of x.2 - 1) *ᵥ θ ⬝ᵥ ((Matrix.of x.1 * (((Matrix.of x.2 * Matrix.of x.1)ᵀ *
            (Matrix.of x.2 * Matrix.of x.1))⁻¹ * (Matrix.of x.2 * Matrix.of x.1)ᵀ)) *
              Matrix.of x.2 - 1) *ᵥ θ)
    {η ε₁ : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ((Measure.pi fun _ : Fin n₀ => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n₀ => gaussianReal 0 1))
        {x | ¬ (((1 - (((q + 1 : ℕ) : ℝ)) / n₀) * (θ ⬝ᵥ θ) - ε₁) *
              (1 + ((q + 1 : ℕ) : ℝ) * (1 - η) / (((m - q : ℕ) : ℝ) * (1 + η))) ≤ Rb x ∧
            Rb x ≤ ((1 - (((q + 1 : ℕ) : ℝ)) / n₀) * (θ ⬝ᵥ θ) + ε₁) *
              (1 + ((q + 1 : ℕ) : ℝ) * (1 + η) / (((m - q : ℕ) : ℝ) * (1 - η))))} ≤
      (Measure.pi fun _ : Fin n₀ => Measure.pi fun _ : Fin (q + 1) => gaussianReal 0 1)
        {S | ε₁ ≤ |((1 - gramProjector (Matrix.of S)) *ᵥ θ) ⬝ᵥ
          ((1 - gramProjector (Matrix.of S)) *ᵥ θ) -
          (1 - (((q + 1 : ℕ) : ℝ)) / n₀) * (θ ⬝ᵥ θ)|} +
        (ENNReal.ofReal (60 / (η ^ 4 * ((m - q : ℕ) : ℝ) ^ 2)) +
          ENNReal.ofReal (60 / (η ^ 4 * ((q + 1 : ℕ) : ℝ) ^ 2))) := by
  have hν : 0 < ((m - q : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m - q)
  have hn : 0 < ((q + 1 : ℕ) : ℝ) := by positivity
  have h1η : 0 < 1 - η := by linarith
  refine measure_prod_sandwich_le _ _
    (s2 := fun S : Fin n₀ → Fin (q + 1) → ℝ =>
      ((1 - gramProjector (Matrix.of S)) *ᵥ θ) ⬝ᵥ ((1 - gramProjector (Matrix.of S)) *ᵥ θ))
    (Rb := Rb) (a := (1 - (((q + 1 : ℕ) : ℝ)) / n₀) * (θ ⬝ᵥ θ))
    (c₁ := ((q + 1 : ℕ) : ℝ) * (1 - η) / (((m - q : ℕ) : ℝ) * (1 + η)))
    (c₂ := ((q + 1 : ℕ) : ℝ) * (1 + η) / (((m - q : ℕ) : ℝ) * (1 - η))) (ε₁ := ε₁)
    ?_ ?_ (by positivity) (by positivity) ?_
  · have := (measurable_resid (n₀ := n₀) (n := q + 1)).comp
      (measurable_id.prodMk (measurable_const (a := θ)))
    exact this
  · rw [funext hRb]; exact measurable_featureBias θ
  · filter_upwards [ae_isUnit_det_gram_gaussianMatrix (q + 1) n₀ hqn] with S hS
    exact measure_featureBias_deviation_le hqm (Matrix.of S) hS θ (fun X => Rb (S, X))
      (fun X => hRb (S, X)) hη hη1

/-- `measure_featureBias_joint_le` for a general number `n ≥ 1` of features, with
`ν = m - n + 1`. -/
theorem measure_featureBias_joint_le' {m n n₀ : ℕ} (hn : 0 < n) (hnm : n ≤ m) (hnn₀ : n ≤ n₀)
    (θ : Fin n₀ → ℝ)
    (Rb : (Fin n₀ → Fin n → ℝ) × (Fin m → Fin n₀ → ℝ) → ℝ)
    (hRb : ∀ x, Rb x = ((Matrix.of x.1 * (((Matrix.of x.2 * Matrix.of x.1)ᵀ *
        (Matrix.of x.2 * Matrix.of x.1))⁻¹ * (Matrix.of x.2 * Matrix.of x.1)ᵀ)) *
          Matrix.of x.2 - 1) *ᵥ θ ⬝ᵥ ((Matrix.of x.1 * (((Matrix.of x.2 * Matrix.of x.1)ᵀ *
            (Matrix.of x.2 * Matrix.of x.1))⁻¹ * (Matrix.of x.2 * Matrix.of x.1)ᵀ)) *
              Matrix.of x.2 - 1) *ᵥ θ)
    {η ε₁ : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ((Measure.pi fun _ : Fin n₀ => Measure.pi fun _ : Fin n => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n₀ => gaussianReal 0 1))
        {x | ¬ (((1 - (n : ℝ) / n₀) * (θ ⬝ᵥ θ) - ε₁) *
              (1 + (n : ℝ) * (1 - η) / (((m - n + 1 : ℕ) : ℝ) * (1 + η))) ≤ Rb x ∧
            Rb x ≤ ((1 - (n : ℝ) / n₀) * (θ ⬝ᵥ θ) + ε₁) *
              (1 + (n : ℝ) * (1 + η) / (((m - n + 1 : ℕ) : ℝ) * (1 - η))))} ≤
      (Measure.pi fun _ : Fin n₀ => Measure.pi fun _ : Fin n => gaussianReal 0 1)
        {S | ε₁ ≤ |((1 - gramProjector (Matrix.of S)) *ᵥ θ) ⬝ᵥ
          ((1 - gramProjector (Matrix.of S)) *ᵥ θ) -
          (1 - (n : ℝ) / n₀) * (θ ⬝ᵥ θ)|} +
        (ENNReal.ofReal (60 / (η ^ 4 * ((m - n + 1 : ℕ) : ℝ) ^ 2)) +
          ENNReal.ofReal (60 / (η ^ 4 * (n : ℝ) ^ 2))) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have e : m - (q + 1) + 1 = m - q := by omega
  rw [e]
  exact measure_featureBias_joint_le hnm hnn₀ θ Rb hRb hη hη1

/-- **Choice of the tolerances.** If `L = a (1 + c)`, then for every `ε > 0` there is a single
`t ∈ (0, 1)` with `(a - t)(1 + c (1 - t)/(1 + t)) > L - ε` and
`(a + t)(1 + c (1 + t)/(1 - t)) < L + ε`: both sides are continuous in `t` and equal `L` at
`t = 0`. -/
theorem exists_tolerance_sandwich {a c L ε : ℝ} (hL : L = a * (1 + c)) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ L - ε < (a - t) * (1 + c * ((1 - t) / (1 + t))) ∧
      (a + t) * (1 + c * ((1 + t) / (1 - t))) < L + ε := by
  have h1 : ContinuousAt (fun t : ℝ => (a - t) * (1 + c * ((1 - t) / (1 + t)))) 0 := by
    refine ContinuousAt.mul (by fun_prop) (ContinuousAt.add continuousAt_const
      (ContinuousAt.mul continuousAt_const
        (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num))))
  have h2 : ContinuousAt (fun t : ℝ => (a + t) * (1 + c * ((1 + t) / (1 - t)))) 0 := by
    refine ContinuousAt.mul (by fun_prop) (ContinuousAt.add continuousAt_const
      (ContinuousAt.mul continuousAt_const
        (ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num))))
  have e1 : (fun t : ℝ => (a - t) * (1 + c * ((1 - t) / (1 + t)))) 0 = L := by simp [hL]
  have e2 : (fun t : ℝ => (a + t) * (1 + c * ((1 + t) / (1 - t)))) 0 = L := by simp [hL]
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < t ∧ t < 1 ∧
      L - ε < (a - t) * (1 + c * ((1 - t) / (1 + t))) ∧
        (a + t) * (1 + c * ((1 + t) / (1 - t))) < L + ε := by
    have hI : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), t ∈ Set.Ioo (0 : ℝ) 1 :=
      Ioo_mem_nhdsGT one_pos
    have g1 := (h1.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))).eventually
      (lt_mem_nhds (show L - ε < (fun t : ℝ => (a - t) * (1 + c * ((1 - t) / (1 + t)))) 0 by
        rw [e1]; linarith))
    have g2 := (h2.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))).eventually
      (gt_mem_nhds (show (fun t : ℝ => (a + t) * (1 + c * ((1 + t) / (1 - t)))) 0 < L + ε by
        rw [e2]; linarith))
    filter_upwards [hI, g1, g2] with t ht h1' h2'
    exact ⟨ht.1, ht.2, h1', h2'⟩
  obtain ⟨t, ht⟩ := hev.exists
  exact ⟨t, ht⟩

/-- **Ratio limits for the feature-bottleneck regime.** If `n_k ≤ m_k`, `n_k / m_k → δ < 1` and
`n₀_k / m_k → γ > 0`, with `m_k → ∞`, then for `ν_k = m_k - n_k + 1`:
`ν_k → ∞`, `n_k / ν_k → δ / (1 - δ)` and `n_k / n₀_k → δ / γ`. -/
theorem tendsto_feature_ratios {mm nn n0 : ℕ → ℕ} {δ γ : ℝ} (hδ1 : δ < 1) (hγ0 : 0 < γ)
    (hn : ∀ k, 0 < nn k) (hnm : ∀ k, nn k ≤ mm k) (hmm : Tendsto mm atTop atTop)
    (hδ : Tendsto (fun k => (nn k : ℝ) / (mm k : ℝ)) atTop (𝓝 δ))
    (hγ : Tendsto (fun k => (n0 k : ℝ) / (mm k : ℝ)) atTop (𝓝 γ)) :
    Tendsto (fun k => ((mm k - nn k + 1 : ℕ) : ℝ)) atTop atTop ∧
      Tendsto (fun k => (nn k : ℝ) / ((mm k - nn k + 1 : ℕ) : ℝ)) atTop (𝓝 (δ / (1 - δ))) ∧
      Tendsto (fun k => (nn k : ℝ) / (n0 k : ℝ)) atTop (𝓝 (δ / γ)) := by
  have hmR : Tendsto (fun k => (mm k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hmm
  have hmpos : ∀ k, (0 : ℝ) < mm k := fun k => by
    have := hn k; have := hnm k; exact_mod_cast (by omega : 0 < mm k)
  have hν : ∀ k, ((mm k - nn k + 1 : ℕ) : ℝ) = (mm k : ℝ) - nn k + 1 := fun k => by
    rw [Nat.cast_add, Nat.cast_sub (hnm k)]; simp
  have hrat : Tendsto (fun k => (((mm k - nn k + 1 : ℕ) : ℝ)) / (mm k : ℝ)) atTop
      (𝓝 (1 - δ)) := by
    have h1 : Tendsto (fun k => 1 - (nn k : ℝ) / (mm k : ℝ) + 1 / (mm k : ℝ)) atTop
        (𝓝 (1 - δ + 0)) :=
      (tendsto_const_nhds.sub hδ).add (tendsto_const_nhds.div_atTop hmR)
    rw [add_zero] at h1
    refine h1.congr fun k => ?_
    rw [hν k]; field_simp [(hmpos k).ne']
  have hδ1' : 0 < 1 - δ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have := hrat.pos_mul_atTop hδ1' hmR
    refine this.congr fun k => ?_
    field_simp [(hmpos k).ne']
  · have := hδ.div hrat hδ1'.ne'
    refine this.congr fun k => ?_
    simp only [Pi.div_apply]
    rw [div_div_div_cancel_right₀ (hmpos k).ne']
  · have := hδ.div hγ hγ0.ne'
    refine this.congr fun k => ?_
    simp only [Pi.div_apply]
    rw [div_div_div_cancel_right₀ (hmpos k).ne']

/-- **Bias of the feature-bottleneck estimator converges in probability (Milestone 3b, bias
half).** Let `S_k` be `n₀_k × n_k` and `X_k` independent `m_k × n₀_k` Gaussian matrices,
`1 ≤ n_k ≤ min {m_k, n₀_k}`, `n_k → ∞`, `n_k / m_k → δ < 1`, `n₀_k / m_k → γ > 0` and
`‖θ_k‖² → r`. Then the bias `R_bias = ‖(M X - 1) θ_k‖²` of `θ̂ = M y`, `M = S (Zᵀ Z)⁻¹ Zᵀ`,
`Z = X S`, converges in probability to `(γ - δ) / (γ (1 - δ)) r`: for every `ε > 0` the probability
that it differs from this by at least `ε` tends to `0`.

Proof: with `a = (1 - δ/γ) r` and `c = δ/(1-δ)`, the limit is `a (1 + c)`. A single small tolerance
`t` (`exists_tolerance_sandwich`) makes the sandwich `[(a_k - t)(1 + c₁), (a_k + t)(1 + c₂)]` of
`measure_featureBias_joint_le'` lie inside `(L - ε, L + ε)` eventually, and its failure
probability tends to `0` by `tendsto_measure_resid_deviation` (Milestone 7e) and `ν_k, n_k → ∞`. -/
theorem tendsto_measure_featureBias_deviation {mm nn n0 : ℕ → ℕ} {δ γ r : ℝ} (hδ1 : δ < 1)
    (hγ0 : 0 < γ) (hn : ∀ k, 0 < nn k) (hnm : ∀ k, nn k ≤ mm k) (hnn0 : ∀ k, nn k ≤ n0 k)
    (hnn : Tendsto nn atTop atTop)
    (hδ : Tendsto (fun k => (nn k : ℝ) / (mm k : ℝ)) atTop (𝓝 δ))
    (hγ : Tendsto (fun k => (n0 k : ℝ) / (mm k : ℝ)) atTop (𝓝 γ))
    (θ : ∀ k, Fin (n0 k) → ℝ) (hθ : Tendsto (fun k => θ k ⬝ᵥ θ k) atTop (𝓝 r))
    (Rb : ∀ k, (Fin (n0 k) → Fin (nn k) → ℝ) × (Fin (mm k) → Fin (n0 k) → ℝ) → ℝ)
    (hRb : ∀ k x, Rb k x = ((Matrix.of x.1 * (((Matrix.of x.2 * Matrix.of x.1)ᵀ *
        (Matrix.of x.2 * Matrix.of x.1))⁻¹ * (Matrix.of x.2 * Matrix.of x.1)ᵀ)) *
          Matrix.of x.2 - 1) *ᵥ θ k ⬝ᵥ ((Matrix.of x.1 * (((Matrix.of x.2 * Matrix.of x.1)ᵀ *
            (Matrix.of x.2 * Matrix.of x.1))⁻¹ * (Matrix.of x.2 * Matrix.of x.1)ᵀ)) *
              Matrix.of x.2 - 1) *ᵥ θ k)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k =>
      ((Measure.pi fun _ : Fin (n0 k) => Measure.pi fun _ : Fin (nn k) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (mm k) => Measure.pi fun _ : Fin (n0 k) => gaussianReal 0 1))
        {x | ε ≤ |Rb k x - (γ - δ) / (γ * (1 - δ)) * r|}) atTop (𝓝 0) := by
  have hmm : Tendsto mm atTop atTop := tendsto_atTop_mono hnm hnn
  obtain ⟨hνtop, hnν, hnn0r⟩ := tendsto_feature_ratios hδ1 hγ0 hn hnm hmm hδ hγ
  have hδ1' : 1 - δ ≠ 0 := by linarith
  have hL : (γ - δ) / (γ * (1 - δ)) * r = (1 - δ / γ) * r * (1 + δ / (1 - δ)) := by
    field_simp; ring
  obtain ⟨t, ht0, ht1, hlow, hhigh⟩ := exists_tolerance_sandwich hL hε
  have hak : Tendsto (fun k => (1 - (nn k : ℝ) / (n0 k : ℝ)) * (θ k ⬝ᵥ θ k)) atTop
      (𝓝 ((1 - δ / γ) * r)) := (tendsto_const_nhds.sub hnn0r).mul hθ
  have hc1 : Tendsto (fun k => (nn k : ℝ) * (1 - t) / (((mm k - nn k + 1 : ℕ) : ℝ) * (1 + t)))
      atTop (𝓝 (δ / (1 - δ) * ((1 - t) / (1 + t)))) := by
    refine ((hnν.mul_const ((1 - t) / (1 + t)))).congr fun k => ?_
    have : (0 : ℝ) < ((mm k - nn k + 1 : ℕ) : ℝ) := by positivity
    field_simp
  have hc2 : Tendsto (fun k => (nn k : ℝ) * (1 + t) / (((mm k - nn k + 1 : ℕ) : ℝ) * (1 - t)))
      atTop (𝓝 (δ / (1 - δ) * ((1 + t) / (1 - t)))) := by
    refine ((hnν.mul_const ((1 + t) / (1 - t)))).congr fun k => ?_
    have : (0 : ℝ) < ((mm k - nn k + 1 : ℕ) : ℝ) := by positivity
    have h1t : (1 - t) ≠ 0 := by linarith
    field_simp
  have hlowk := ((hak.sub_const t).mul (tendsto_const_nhds.add hc1)).eventually
    (lt_mem_nhds hlow)
  have hhighk := ((hak.add_const t).mul (tendsto_const_nhds.add hc2)).eventually
    (gt_mem_nhds hhigh)
  obtain ⟨M, hM⟩ := hθ.bddAbove_range
  have hM' : ∀ k, θ k ⬝ᵥ θ k ≤ max (M) 1 := fun k =>
    (hM ⟨k, rfl⟩).trans (le_max_left _ _)
  have h7e := tendsto_measure_resid_deviation n0 nn hnn0 hnn (M := max M 1)
    (lt_of_lt_of_le one_pos (le_max_right _ _)) ht0 θ hM'
  have hbound : Tendsto (fun k =>
      (Measure.pi fun _ : Fin (n0 k) => Measure.pi fun _ : Fin (nn k) => gaussianReal 0 1)
        {S | t ≤ |((1 - gramProjector (Matrix.of S)) *ᵥ θ k) ⬝ᵥ
          ((1 - gramProjector (Matrix.of S)) *ᵥ θ k) - (1 - (nn k : ℝ) / n0 k) * (θ k ⬝ᵥ θ k)|} +
        (ENNReal.ofReal (60 / (t ^ 4 * ((mm k - nn k + 1 : ℕ) : ℝ) ^ 2)) +
          ENNReal.ofReal (60 / (t ^ 4 * (nn k : ℝ) ^ 2)))) atTop (𝓝 0) := by
    have := h7e.add ((ENNReal.tendsto_ofReal_div_mul_sq hνtop 60 (by positivity : 0 < t ^ 4)).add
      (ENNReal.tendsto_ofReal_div_mul_sq (tendsto_natCast_atTop_atTop.comp hnn) 60
        (by positivity : 0 < t ^ 4)))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hlowk, hhighk] with k hk1 hk2
  refine le_trans (measure_mono ?_) (measure_featureBias_joint_le' (hn k) (hnm k) (hnn0 k) (θ k)
    (Rb k) (hRb k) (η := t) (ε₁ := t) ht0 ht1)
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  intro ⟨h1, h2⟩
  have : |Rb k x - (γ - δ) / (γ * (1 - δ)) * r| < ε := by
    rw [abs_lt]; constructor <;> linarith
  exact absurd hx (not_le.2 this)

end LinearRegression.DoubleDescent

end
