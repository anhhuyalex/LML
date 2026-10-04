/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.ReLU.ArcCosine

/-!
# The ReLU NTK in closed form

For unit vectors `x, x'` the limiting NTK of the ReLU network is
`k(x, x') = xᵀx' · (π − arccos(xᵀx')) / (2π)` (Proposition 4.2 of Telgarsky 2021).

The Gaussian input is reduced to two dimensions through the pushforward of the standard Gaussian
on `ℝᵈ` along the linear map `w ↦ (xᵀw, x'ᵀw)`, which is a centred Gaussian whose covariance is the
Gram matrix of the two rows (`map_matrixCLM_stdGaussian`). The two-dimensional orthant
computation is `expected_reluIndicator_mul_reluIndicator_eq_halfspace_sector`.
-/
@[expose] public section

open Real MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace Matrix

namespace NTK

variable {d : ℕ}

/-- **Pushforward of the standard Gaussian along a matrix.** The image of the standard Gaussian on
`ℝᵈ` under `v ↦ A v` is the centred Gaussian on `ℝᵏ` with covariance `A Aᵀ`. -/
lemma map_matrixCLM_stdGaussian {k : ℕ} (A : Matrix (Fin k) (Fin d) ℝ) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map (matrixCLM A) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) (A * Aᵀ) := by
  have hS : (A * Aᵀ).PosSemidef := by simpa using Matrix.posSemidef_self_mul_conjTranspose A
  refine IsGaussian.ext ?_ ?_
  · have h := (matrixCLM A).integral_id_map
      (μ := stdGaussian (EuclideanSpace ℝ (Fin d))) IsGaussian.integrable_id
    simp only [id] at h ⊢
    rw [h]
    simp [integral_id_stdGaussian, integral_id_multivariateGaussian]
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_stdGaussian,
      covarianceBilin_multivariateGaussian hS]
    rw [← matrixCLM_transpose_eq_adjoint, innerSL_apply_apply, matrixCLM_apply, matrixCLM_apply,
      EuclideanSpace.inner_toLp_toLp, star_trivial, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm,
      Matrix.transpose_transpose]

/-- The dot product of two unit vectors lies in `[-1, 1]` (Cauchy–Schwarz). -/
lemma dotProduct_mem_Icc_of_unit {x x' : Fin d → ℝ} (hx : x ⬝ᵥ x = 1) (hx' : x' ⬝ᵥ x' = 1) :
    x ⬝ᵥ x' ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := sq_dotProduct_le x x'
  rw [← dotProduct_self_eq_sum_sq, ← dotProduct_self_eq_sum_sq, hx, hx'] at h
  exact abs_le.mp (sq_le_one_iff_abs_le_one _ |>.mp (by simpa using h))

/--
**Orthant probability for two half-spaces.** For unit vectors `x, x'`, the standard Gaussian gives
the intersection of the half-spaces `{w | wᵀx ≥ 0}` and `{w | wᵀx' ≥ 0}` the mass
`(π − arccos(xᵀx')) / (2π)`.

The pair `(wᵀx, wᵀx')` is a centred Gaussian with covariance `!![1, ρ; ρ, 1]`, `ρ = xᵀx'`
(`map_matrixCLM_stdGaussian`); the two-dimensional computation is
`expected_reluIndicator_mul_reluIndicator_eq_halfspace_sector`. See Section 4.3 (Proposition 4.2)
of Telgarsky's Deep Learning Theory lecture notes or Cho & Saul (2009), "Kernel Methods for Deep
Learning".
-/
lemma prob_halfspace_intersect
    (x x' : Fin d → ℝ)
    (hx : x ⬝ᵥ x = 1)
    (hx' : x' ⬝ᵥ x' = 1) :
    ∫ w : Fin d → ℝ, reluIndicator (w ⬝ᵥ x) * reluIndicator (w ⬝ᵥ x') ∂(Measure.pi fun _ : Fin d =>
        gaussianReal 0 1) =
      (Real.pi - Real.arccos (x ⬝ᵥ x')) / (2 * Real.pi) := by
  have hρ := dotProduct_mem_Icc_of_unit hx hx'
  let A : Matrix (Fin 2) (Fin d) ℝ := Matrix.of ![x, x']
  have hAA : A * Aᵀ = !![1, x ⬝ᵥ x'; x ⬝ᵥ x', 1] := by
    have hxx : ∑ k, x k * x k = 1 := hx
    have hxx' : ∑ k, x' k * x' k = 1 := hx'
    have hcomm : ∑ k, x' k * x k = x ⬝ᵥ x' := by rw [dotProduct_comm]; rfl
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, Matrix.mul_apply, hxx, hxx', hcomm, dotProduct]
  have hmap := map_matrixCLM_stdGaussian A
  rw [hAA] at hmap
  rw [integral_gaussianRowMeasure_eq_integral_stdGaussian
    (f := fun w => reluIndicator (w ⬝ᵥ x) * reluIndicator (w ⬝ᵥ x'))]
  have hint : ∫ y : EuclideanSpace ℝ (Fin d),
        reluIndicator (y.ofLp ⬝ᵥ x) * reluIndicator (y.ofLp ⬝ᵥ x')
        ∂(stdGaussian (EuclideanSpace ℝ (Fin d))) =
      ∫ z : EuclideanSpace ℝ (Fin 2), reluIndicator (z.ofLp 0) * reluIndicator (z.ofLp 1)
        ∂(multivariateGaussian 0 !![1, x ⬝ᵥ x'; x ⬝ᵥ x', 1]) := by
    have hmeas : AEStronglyMeasurable
        (fun z : EuclideanSpace ℝ (Fin 2) => reluIndicator (z.ofLp 0) * reluIndicator (z.ofLp 1))
        (Measure.map (matrixCLM A) (stdGaussian (EuclideanSpace ℝ (Fin d)))) :=
      (((measurable_reluIndicator.comp (EuclideanSpace.proj (0 : Fin 2)).measurable).mul
        (measurable_reluIndicator.comp (EuclideanSpace.proj (1 : Fin 2)).measurable)
        ).stronglyMeasurable).aestronglyMeasurable
    rw [← hmap, integral_map (matrixCLM A).continuous.measurable.aemeasurable hmeas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp [matrixCLM_apply, A, dotProduct_comm y.ofLp]
  rw [hint]
  exact expected_reluIndicator_mul_reluIndicator_eq_halfspace_sector (x ⬝ᵥ x') hρ

/-- **Proposition 4.2** (ReLU NTK closed form, Telgarsky 2021).
For `σ' = 1[· ≥ 0]` (the ReLU derivative) and `x, x' ∈ ℝᵈ` with
`x ⬝ᵥ x = x' ⬝ᵥ x' = 1`:
  `k(x, x') = (xᵀx') · (π − arccos(xᵀx')) / (2π)`.

**Proof sketch:**
- By rotational invariance of `𝒩(0, Iᵈ)`, we may project `w` onto `span(x, x')`.
- In the 2D plane, `w` is effectively uniform on the unit circle.
- The event `{wᵀx ≥ 0} ∩ {wᵀx' ≥ 0}` is a sector of angle `π − θ` where `θ = arccos(xᵀx')`.
- The probability of this sector is `(π − θ)/(2π)`.
- Multiplying by `xᵀx'` gives the result. -/
theorem reluNTK_closedForm
    (x x' : Fin d → ℝ)
    (hx : x ⬝ᵥ x = 1)
    (hx' : x' ⬝ᵥ x' = 1) :
    shallowLimitingNTK reluIndicator x x' =
      (x ⬝ᵥ x') * (Real.pi - Real.arccos (x ⬝ᵥ x')) / (2 * Real.pi) := by
  unfold shallowLimitingNTK
  rw [prob_halfspace_intersect x x' hx hx']
  ring

/-- The ReLU NTK is nonneg when `xᵀx' ≥ 0`. -/
lemma reluNTK_nonneg_of_nonneg_inner
    (x x' : Fin d → ℝ)
    (hx : x ⬝ᵥ x = 1) (hx' : x' ⬝ᵥ x' = 1)
    (hinn : 0 ≤ x ⬝ᵥ x') :
    0 ≤ shallowLimitingNTK reluIndicator x x' := by
  rw [reluNTK_closedForm x x' hx hx']
  apply div_nonneg
  · apply mul_nonneg hinn
    linarith [Real.arccos_le_pi (x ⬝ᵥ x'), Real.pi_pos]
  · linarith [Real.pi_pos]

/-- The ReLU NTK at equal inputs normalized by the local inner product. -/
lemma reluNTK_self
    (x : Fin d → ℝ) (hx : x ⬝ᵥ x = 1) :
    shallowLimitingNTK reluIndicator x x = 1 / 2 := by
  rw [reluNTK_closedForm x x hx hx]
  rw [hx]
  simp [Real.arccos_one]
  ring_nf
  simp [Real.pi_pos.ne']

end NTK

end
