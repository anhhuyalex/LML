/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.FitErrorConcentration
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.GramInverse
public import LeanMachineLearning.Optimization.LinearRegression.DoubleDescent.InverseGramTrace

/-!
# The projected design of a fixed sample, with a Gaussian random-feature matrix

Sample-bottleneck regime of random-feature regression ([Bach, 2024]; [Hastie et al., 2022]):
`X ∈ ℝ^{m×n₀}` is a *fixed* design with `X Xᵀ` invertible and `V ∈ ℝ^{n×n₀}` has i.i.d. standard
normal entries (so `S = Vᵀ` is the random-feature matrix), `Z = X S = X Vᵀ ∈ ℝ^{m×n}`,
`m ≤ n`. Writing `X = R Qᵀ` with `Qᵀ Q = 1` and `R` symmetric invertible, the inverse Gram matrix
of `Z` factors as
`(Z Zᵀ)⁻¹ = R⁻¹ ((V Q)ᵀ (V Q))⁻¹ R⁻¹`
with `G = V Q ∈ ℝ^{n×m}` again Gaussian (orthogonal invariance), and `R⁻¹ R⁻¹ = (X Xᵀ)⁻¹`. This
reduces every statistic of `Z` that depends on the *design* only through `X Xᵀ` to the law of the
inverse Gram matrix of an identity-covariance Gaussian matrix:

* `exists_frame_inv_gram_sampleDesign`: the factorization above;
* `measure_sampleTrace_mem_le`: `Tr ((Z Zᵀ)⁻¹) = Tr (C (Gᵀ G)⁻¹)` with the PSD weight
  `C = (X Xᵀ)⁻¹` lies in `Tr ((X Xᵀ)⁻¹) / (ν (1 ± η))`, `ν = n - m + 1`, except with probability
  `60 m / (η⁴ ν²)` (`measure_trace_mul_inv_gram_deviation_le`);
* `measure_sampleQuad_mem_le`: for fixed `a ∈ ℝ^m`, `aᵀ (Z Zᵀ)⁻¹ a` lies in
  `aᵀ (X Xᵀ)⁻¹ a / (ν (1 ± η))` except with probability `60 / (η⁴ ν²)`
  (`measure_quadForm_inv_gram_fixed_mem_le`).
-/

@[expose]
public section

namespace LinearRegression.DoubleDescent

open MeasureTheory ProbabilityTheory Matrix NTK
open scoped Matrix

/-- **Orthonormal frame of the design.** If `X Xᵀ` is invertible, `Xᵀ = Q R` with `Qᵀ Q = 1` and
`R` symmetric invertible, `R⁻¹ R⁻¹ = (X Xᵀ)⁻¹`, and for every `V` the inverse Gram matrix of
`Z = X Vᵀ` factors as `(Z Zᵀ)⁻¹ = R⁻¹ ((V Q)ᵀ (V Q))⁻¹ R⁻¹`: only the Gaussian `G = V Q` is
random. -/
theorem exists_frame_inv_gram_sampleDesign {m n n₀ : ℕ} (X : Matrix (Fin m) (Fin n₀) ℝ)
    (hX : IsUnit (X * Xᵀ).det) :
    ∃ (Q : Matrix (Fin n₀) (Fin m) ℝ) (R : Matrix (Fin m) (Fin m) ℝ), Qᵀ * Q = 1 ∧
      IsUnit R.det ∧ Rᵀ = R ∧ R⁻¹ * R⁻¹ = (X * Xᵀ)⁻¹ ∧
      ∀ V : Matrix (Fin n) (Fin n₀) ℝ, ((X * Vᵀ) * (X * Vᵀ)ᵀ)⁻¹ =
        R⁻¹ * ((V * Q)ᵀ * (V * Q))⁻¹ * R⁻¹ := by
  obtain ⟨Q, R, hQ, hR, hRT, hΦ⟩ := exists_orthonormal_factor Xᵀ (by simpa using hX)
  have hXQR : X = R * Qᵀ := by
    have := congrArg Matrix.transpose hΦ
    rwa [Matrix.transpose_transpose, Matrix.transpose_mul, hRT] at this
  have hRR : R * R = X * Xᵀ := by
    rw [hXQR, Matrix.transpose_mul, Matrix.transpose_transpose, hRT, Matrix.mul_assoc,
      ← Matrix.mul_assoc Qᵀ, hQ, Matrix.one_mul]
  refine ⟨Q, R, hQ, hR, hRT, ?_, fun V => ?_⟩
  · rw [← hRR, Matrix.mul_inv_rev]
  · have : (X * Vᵀ) * (X * Vᵀ)ᵀ = R * ((V * Q)ᵀ * (V * Q)) * R := by
      rw [hXQR]
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hRT, Matrix.mul_assoc]
    rw [this, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]

/-- **The trace `Tr ((Z Zᵀ)⁻¹)` of the projected design concentrates, for a fixed design.** Let `X`
be a fixed `m × n₀` matrix with `X Xᵀ` invertible, `V` an `n × n₀` Gaussian matrix, `Z = X Vᵀ`,
`m ≤ n`, `ν = n - m + 1` and `0 < η < 1`. Then `Tr ((Z Zᵀ)⁻¹)` lies in
`[Tr ((X Xᵀ)⁻¹) / (ν (1+η)), Tr ((X Xᵀ)⁻¹) / (ν (1-η))]` except with probability at most
`60 m / (η⁴ ν²)`: through `X = R Qᵀ`, `(Z Zᵀ)⁻¹ = R⁻¹ ((V Q)ᵀ (V Q))⁻¹ R⁻¹`, so the trace is
`Tr (C (Gᵀ G)⁻¹)` with `G = V Q` Gaussian and the PSD weight `C = (X Xᵀ)⁻¹`. -/
theorem measure_sampleTrace_mem_le {m n n₀ : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (X : Matrix (Fin m) (Fin n₀) ℝ) (hX : IsUnit (X * Xᵀ).det) {η : ℝ} (hη : 0 < η)
    (hη1 : η < 1) :
    (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n₀ => gaussianReal 0 1)
        {V | ¬ (((X * Xᵀ)⁻¹).trace / (((n - m + 1 : ℕ) : ℝ) * (1 + η)) ≤
            (((X * (Matrix.of V)ᵀ) * (X * (Matrix.of V)ᵀ)ᵀ)⁻¹).trace ∧
          (((X * (Matrix.of V)ᵀ) * (X * (Matrix.of V)ᵀ)ᵀ)⁻¹).trace ≤
            ((X * Xᵀ)⁻¹).trace / (((n - m + 1 : ℕ) : ℝ) * (1 - η)))} ≤
      ENNReal.ofReal ((m : ℝ) * (60 / (η ^ 4 * ((n - m + 1 : ℕ) : ℝ) ^ 2))) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  obtain ⟨Q, R, hQ, hR, hRT, hRR, hZ⟩ := exists_frame_inv_gram_sampleDesign (n := n) X hX
  have hRinvT : (R⁻¹)ᵀ = R⁻¹ := by rw [Matrix.transpose_nonsing_inv, hRT]
  have hCpsd : (R⁻¹ * R⁻¹).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self R⁻¹
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hRinvT] using this
  have hmn' : q + 1 ≤ n := hmn
  have h := measure_trace_mul_inv_gram_deviation_le hmn' (R⁻¹ * R⁻¹) hCpsd hη hη1
  have e : n - (q + 1) + 1 = n - q := by omega
  rw [e]
  rw [hRR] at h
  refine le_trans (measure_mono ?_) (le_trans
    (measure_preimage_mul_orthonormal_le (ρ := Fin n) Q hQ _) h)
  intro V hV
  have hfW : (Matrix.of fun i k => (Matrix.of V * Q) i k : Matrix (Fin n) (Fin (q + 1)) ℝ) =
      Matrix.of V * Q := rfl
  simp only [Set.mem_ofPred_eq, hfW] at hV ⊢
  have htr : (((X * (Matrix.of V)ᵀ) * (X * (Matrix.of V)ᵀ)ᵀ)⁻¹).trace =
      ((X * Xᵀ)⁻¹ * ((Matrix.of V * Q)ᵀ * (Matrix.of V * Q))⁻¹).trace := by
    rw [hZ, ← hRR, Matrix.trace_mul_cycle]
  rw [htr] at hV
  exact hV

/-- **The fitted-signal energy `aᵀ (Z Zᵀ)⁻¹ a` concentrates, for a fixed design.** In the setting of
`measure_sampleTrace_mem_le`, for every fixed vector `a ∈ ℝ^m` the quadratic form
`aᵀ (Z Zᵀ)⁻¹ a` lies in `[aᵀ (X Xᵀ)⁻¹ a / (ν (1+η)), aᵀ (X Xᵀ)⁻¹ a / (ν (1-η))]` except with
probability at most `60 / (η⁴ ν²)`. (With `a = X θ` the left side is the squared norm of the
interpolating coefficients `Z† X θ`, and `aᵀ (X Xᵀ)⁻¹ a = ‖P_X θ‖²`.) -/
theorem measure_sampleQuad_mem_le {m n n₀ : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (X : Matrix (Fin m) (Fin n₀) ℝ) (hX : IsUnit (X * Xᵀ).det) (a : Fin m → ℝ) {η : ℝ}
    (hη : 0 < η) (hη1 : η < 1) :
    (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n₀ => gaussianReal 0 1)
        {V | ¬ ((a ⬝ᵥ (((X * Xᵀ)⁻¹) *ᵥ a)) / (((n - m + 1 : ℕ) : ℝ) * (1 + η)) ≤
            a ⬝ᵥ ((((X * (Matrix.of V)ᵀ) * (X * (Matrix.of V)ᵀ)ᵀ)⁻¹) *ᵥ a) ∧
          a ⬝ᵥ ((((X * (Matrix.of V)ᵀ) * (X * (Matrix.of V)ᵀ)ᵀ)⁻¹) *ᵥ a) ≤
            (a ⬝ᵥ (((X * Xᵀ)⁻¹) *ᵥ a)) / (((n - m + 1 : ℕ) : ℝ) * (1 - η)))} ≤
      ENNReal.ofReal (60 / (η ^ 4 * ((n - m + 1 : ℕ) : ℝ) ^ 2)) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  obtain ⟨Q, R, hQ, hR, hRT, hRR, hZ⟩ := exists_frame_inv_gram_sampleDesign (n := n) X hX
  have hRinvT : (R⁻¹)ᵀ = R⁻¹ := by rw [Matrix.transpose_nonsing_inv, hRT]
  have hmn' : q + 1 ≤ n := hmn
  have h := measure_quadForm_inv_gram_fixed_mem_le hmn' (R⁻¹ *ᵥ a) hη hη1
  have e : n - (q + 1) + 1 = n - q := by omega
  rw [e]
  have hnorm : (R⁻¹ *ᵥ a) ⬝ᵥ (R⁻¹ *ᵥ a) = a ⬝ᵥ (((X * Xᵀ)⁻¹) *ᵥ a) := by
    rw [← Matrix.dotProduct_transpose_mulVec, hRinvT, Matrix.mulVec_mulVec, hRR]
  rw [hnorm] at h
  refine le_trans (measure_mono ?_) (le_trans
    (measure_preimage_mul_orthonormal_le (ρ := Fin n) Q hQ _) h)
  intro V hV
  have hfW : (Matrix.of fun i k => (Matrix.of V * Q) i k : Matrix (Fin n) (Fin (q + 1)) ℝ) =
      Matrix.of V * Q := rfl
  simp only [Set.mem_ofPred_eq, hfW] at hV ⊢
  have hq : a ⬝ᵥ ((((X * (Matrix.of V)ᵀ) * (X * (Matrix.of V)ᵀ)ᵀ)⁻¹) *ᵥ a) =
      (R⁻¹ *ᵥ a) ⬝ᵥ (((Matrix.of V * Q)ᵀ * (Matrix.of V * Q))⁻¹ *ᵥ (R⁻¹ *ᵥ a)) := by
    rw [hZ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.dotProduct_transpose_mulVec,
      hRinvT]
    exact dotProduct_comm _ _
  rw [hq] at hV
  exact hV

end LinearRegression.DoubleDescent

end
