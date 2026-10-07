/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.FeatureBottleneck
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.FitErrorConcentration

/-!
# Probabilistic limits in the feature-bottleneck regime

TODO
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
then `X u` and `X Q` are independent: `X u` is a standard Gaussian vector and `X Q` a Gaussian matrix.

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
  sorry

end LinearRegression.DoubleDescent

end
