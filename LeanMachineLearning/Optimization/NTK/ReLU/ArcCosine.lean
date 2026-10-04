/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.ReLU.ChoSaul
public import Mathlib.MeasureTheory.Measure.TightNormed
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Cho-Saul / Arc-Cosine Kernel for ReLU (Proposition 2.5)

Bivariate Gaussian expectations of the ReLU and its weak derivative.  For a centred bivariate
Gaussian `(h^α, h^β)` with covariance `[[Φαα, Φαβ], [Φαβ, Φββ]]` and correlation `ρ`:

* `NTK.expected_reluIndicator_mul_reluIndicator_bivariate` :
  `E[1{h^α>0} 1{h^β>0}] = 1/4 + arcsin ρ / (2π)`.
* `NTK.expected_relu_mul_relu_bivariate` :
  `E[relu h^α · relu h^β] = (√(ΦααΦββ)/(2π)) (√(1-ρ²) + ρ(π/2 + arcsin ρ))`.
* `NTK.expected_reluIndicator_mul_reluIndicator_eq_halfspace_sector` : the same orthant probability
  in terms of the inner product of two unit vectors, used by `NTK.ReLU.ClosedForm`.

The reduction proceeds by positive homogeneity to standardized variables, a Cholesky reduction,
and polar-coordinate evaluation (`NTK.ReLU.ChoSaul`).
-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory Matrix Complex
open scoped BigOperators MatrixOrder RealInnerProductSpace Kronecker ENNReal

namespace NTK

variable {d n m : ℕ}

/-! ## Cho-Saul / Arc-Cosine Kernel for ReLU (Proposition 2.5) -/

/-- Equation lemma for `relu` (imported from `NTK.Shallow.Linearization`). -/
@[simp] lemma relu_apply (u : ℝ) : relu u = max u 0 := rfl

/-- Equivalence between `reluDeriv` and `reluIndicator` (which are definitionally equal). -/
lemma reluDeriv_eq_reluIndicator : reluDeriv = reluIndicator := rfl

/-! ### Structural API for ReLU -/

/-- Positive homogeneity of ReLU: `relu (c * u) = c * relu u` for `0 ≤ c`. -/
lemma relu_pos_mul (c u : ℝ) (hc : 0 ≤ c) : relu (c * u) = c * relu u := by
  dsimp [relu]
  rcases le_total 0 u with hu | hu
  · rw [max_eq_left hu, max_eq_left (mul_nonneg hc hu)]
  · rw [max_eq_right hu, mul_zero, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc hu)]

/-- Continuity of the ReLU activation function. -/
lemma continuous_relu : Continuous relu :=
  continuous_id.max continuous_const

/-- Scale invariance of the ReLU derivative for positive multipliers. -/
lemma reluIndicator_pos_mul (c u : ℝ) (hc : 0 < c) : reluIndicator (c * u) = reluIndicator u := by
  unfold reluIndicator
  have : 0 ≤ c * u ↔ 0 ≤ u := mul_nonneg_iff_of_pos_left hc
  rw [if_congr this rfl rfl]

/-! ### 2×2 Covariance and Correlation Geometry -/

/-- Positive semidefiniteness of the standardized 2×2 correlation matrix `!![1, ρ; ρ, 1]` for
`|ρ| ≤ 1`. -/
lemma corrMatrix2x2_posSemidef {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1) 1) :
    (show Matrix (Fin 2) (Fin 2) ℝ from !![1, ρ; ρ, 1]).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · rw [star_trivial]
    have h : x ⬝ᵥ !![1, ρ; ρ, 1] *ᵥ x = (x 0) ^ 2 + 2 * ρ * (x 0) * (x 1) + (x 1) ^ 2 := by
      simp [dotProduct, mulVec, Fin.sum_univ_two]
      ring
    rw [h]
    have h_sq : (x 0) ^ 2 + 2 * ρ * (x 0) * (x 1) + (x 1) ^ 2 =
        (x 0 + ρ * x 1) ^ 2 + (1 - ρ ^ 2) * (x 1) ^ 2 := by ring
    rw [h_sq]
    rcases hρ with ⟨h_ge, h_le⟩
    have h_diff : 0 ≤ 1 - ρ ^ 2 := by nlinarith
    positivity

/-- For any positive-semidefinite 2×2 covariance matrix with positive diagonal entries,
the Pearson correlation coefficient `ρ = Φαβ / √(Φαα * Φββ)` lies in `[-1, 1]`. -/
lemma pearsonRho_mem_Icc
    (Φαα Φββ Φαβ : ℝ) (hΦαα : 0 < Φαα) (hΦββ : 0 < Φββ)
    (hSigma : (show Matrix (Fin 2) (Fin 2) ℝ from !![Φαα, Φαβ; Φαβ, Φββ]).PosSemidef) :
    Φαβ / Real.sqrt (Φαα * Φββ) ∈ Set.Icc (-1) 1 := by
  have h_quad := hSigma.dotProduct_mulVec_nonneg (![-Φαβ, Φαα])
  simp only [star_trivial] at h_quad
  have h_eval : (![-Φαβ, Φαα] : Fin 2 → ℝ) ⬝ᵥ (!![Φαα, Φαβ; Φαβ,
      Φββ] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ (![-Φαβ, Φαα]) =
      Φαα * (Φαα * Φββ - Φαβ ^ 2) := by
    simp [dotProduct, mulVec, Fin.sum_univ_two]
    ring
  rw [h_eval] at h_quad
  have h_diff : 0 ≤ Φαα * Φββ - Φαβ ^ 2 :=
    nonneg_of_mul_nonneg_right h_quad hΦαα
  have h_sq : Φαβ ^ 2 ≤ Φαα * Φββ := by linarith
  have h_prod_pos : 0 < Φαα * Φββ := mul_pos hΦαα hΦββ
  have h_sqrt_pos : 0 < Real.sqrt (Φαα * Φββ) := Real.sqrt_pos.mpr h_prod_pos
  have h_abs : |Φαβ| ≤ Real.sqrt (Φαα * Φββ) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h_sq
  constructor
  · rw [le_div_iff₀ h_sqrt_pos]
    have := neg_le_of_abs_le h_abs
    linarith
  · rw [div_le_iff₀ h_sqrt_pos, one_mul]
    exact le_of_abs_le h_abs

-- Diagonal scaling recovers an off-diagonal covariance entry from its correlation coefficient.
private lemma diagonal_scale_offDiagonal_eq (a b x : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt a * (x / Real.sqrt (a * b)) * Real.sqrt b = x := by
  have hab : 0 < a * b := mul_pos ha hb
  have h_sqrt_ne : Real.sqrt (a * b) ≠ 0 := (Real.sqrt_pos.mpr hab).ne'
  have h_sqrt_mul : Real.sqrt a * Real.sqrt b = Real.sqrt (a * b) := by
    rw [← Real.sqrt_mul (le_of_lt ha)]
  calc
    Real.sqrt a * (x / Real.sqrt (a * b)) * Real.sqrt b =
        (Real.sqrt a * Real.sqrt b) * (x / Real.sqrt (a * b)) := by ring
    _ = Real.sqrt (a * b) * (x / Real.sqrt (a * b)) := by rw [h_sqrt_mul]
    _ = x := mul_div_cancel₀ x h_sqrt_ne

/-- Scaling identity: congruent transformation of the standardized correlation matrix by diagonal
standard deviations
recovers the unstandardized 2x2 covariance matrix `!![Φαα, Φαβ; Φαβ, Φββ]`. -/
lemma diagScale2x2_mul_corr_mul_diagScale
    (Φαα Φββ Φαβ : ℝ) (hΦαα : 0 < Φαα) (hΦββ : 0 < Φββ) :
    let ρ := Φαβ / Real.sqrt (Φαα * Φββ)
    let D := (!![Real.sqrt Φαα, 0; 0, Real.sqrt Φββ] : Matrix (Fin 2) (Fin 2) ℝ)
    D * !![1, ρ; ρ, 1] * Dᵀ = !![Φαα, Φαβ; Φαβ, Φββ] := by
  intro ρ D
  ext i j
  fin_cases i <;> fin_cases j
  · dsimp [D]
    simp only [cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, smul_cons,
      smul_eq_mul, mul_one, smul_empty, tail_cons, zero_smul, empty_vecMul, add_zero, zero_add,
      empty_mul, Equiv.symm_apply_apply, Fin.isValue, Matrix.mul_apply, of_apply, cons_val',
      cons_val_fin_one, cons_val_zero, transpose_apply, Fin.sum_univ_two, cons_val_one, mul_zero]
    exact Real.mul_self_sqrt (le_of_lt hΦαα)
  · dsimp [D, ρ]
    simp only [cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, smul_cons,
      smul_eq_mul, mul_one, smul_empty, tail_cons, zero_smul, empty_vecMul, add_zero, zero_add,
      empty_mul, Equiv.symm_apply_apply, Fin.isValue, Matrix.mul_apply, of_apply, cons_val',
      cons_val_fin_one, cons_val_zero, transpose_apply, cons_val_one, Fin.sum_univ_two, mul_zero]
    exact diagonal_scale_offDiagonal_eq Φαα Φββ Φαβ hΦαα hΦββ
  · dsimp [D, ρ]
    simp only [cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, smul_cons,
      smul_eq_mul, mul_one, smul_empty, tail_cons, zero_smul, empty_vecMul, add_zero, zero_add,
      empty_mul, Equiv.symm_apply_apply, Fin.isValue, Matrix.mul_apply, of_apply, cons_val',
      cons_val_fin_one, cons_val_one, transpose_apply, cons_val_zero, Fin.sum_univ_two, mul_zero]
    calc
      Real.sqrt Φββ * (Φαβ / Real.sqrt (Φαα * Φββ)) * Real.sqrt Φαα =
          Real.sqrt Φαα * (Φαβ / Real.sqrt (Φαα * Φββ)) * Real.sqrt Φββ := by ring
      _ = Φαβ := diagonal_scale_offDiagonal_eq Φαα Φββ Φαβ hΦαα hΦββ
  · dsimp [D]
    simp only [cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, smul_cons,
      smul_eq_mul, mul_one, smul_empty, tail_cons, zero_smul, empty_vecMul, add_zero, zero_add,
      empty_mul, Equiv.symm_apply_apply, Fin.isValue, Matrix.mul_apply, of_apply, cons_val',
      cons_val_fin_one, cons_val_one, transpose_apply, Fin.sum_univ_two, cons_val_zero, mul_zero]
    exact Real.mul_self_sqrt (le_of_lt hΦββ)

/-- Coordinate-wise action of the 2x2 diagonal scaling operator on `EuclideanSpace ℝ (Fin 2)`. -/
lemma toEuclideanCLM_diagScale_apply
    (s0 s1 : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    let D := (!![s0, 0; 0, s1] : Matrix (Fin 2) (Fin 2) ℝ)
    (toEuclideanCLM (𝕜 := ℝ) D z).ofLp 0 = s0 * z.ofLp 0 ∧
    (toEuclideanCLM (𝕜 := ℝ) D z).ofLp 1 = s1 * z.ofLp 1 := by
  intro D
  constructor
  · have h : (toEuclideanCLM (𝕜 := ℝ) D z).ofLp = D *ᵥ z.ofLp := ofLp_toEuclideanCLM D z
    have h0 : (toEuclideanCLM (𝕜 := ℝ) D z).ofLp 0 = (D *ᵥ z.ofLp) 0 := by rw [h]
    rw [h0]
    dsimp [D]
    simp [mulVec, dotProduct, Fin.sum_univ_two]
  · have h : (toEuclideanCLM (𝕜 := ℝ) D z).ofLp = D *ᵥ z.ofLp := ofLp_toEuclideanCLM D z
    have h1 : (toEuclideanCLM (𝕜 := ℝ) D z).ofLp 1 = (D *ᵥ z.ofLp) 1 := by rw [h]
    rw [h1]
    dsimp [D]
    simp [mulVec, dotProduct, Fin.sum_univ_two]

/-- Pullback of the ReLU product under diagonal scaling:
`relu (D z)₀ * relu (D z)₁ = √(Φαα * Φββ) * (relu z₀ * relu z₁)`. -/
lemma relu_mul_relu_toEuclideanCLM_diagScale
    (Φαα Φββ : ℝ) (hΦαα : 0 ≤ Φαα) (_hΦββ : 0 ≤ Φββ)
    (z : EuclideanSpace ℝ (Fin 2)) :
    relu ((toEuclideanCLM (𝕜 := ℝ) (!![Real.sqrt Φαα, 0; 0, Real.sqrt Φββ] : Matrix (Fin 2) (Fin 2)
        ℝ) z).ofLp 0) *
      relu ((toEuclideanCLM (𝕜 := ℝ) (!![Real.sqrt Φαα, 0; 0,
          Real.sqrt Φββ] : Matrix (Fin 2) (Fin 2) ℝ) z).ofLp 1) =
      Real.sqrt (Φαα * Φββ) * (relu (z.ofLp 0) * relu (z.ofLp 1)) := by
  obtain ⟨h0, h1⟩ := toEuclideanCLM_diagScale_apply (Real.sqrt Φαα) (Real.sqrt Φββ) z
  rw [h0, h1]
  have h_sqrt_α : 0 ≤ Real.sqrt Φαα := Real.sqrt_nonneg Φαα
  have h_sqrt_β : 0 ≤ Real.sqrt Φββ := Real.sqrt_nonneg Φββ
  rw [relu_pos_mul (Real.sqrt Φαα) (z.ofLp 0) h_sqrt_α]
  rw [relu_pos_mul (Real.sqrt Φββ) (z.ofLp 1) h_sqrt_β]
  calc
    Real.sqrt Φαα * relu (z.ofLp 0) * (Real.sqrt Φββ * relu (z.ofLp 1))
      = (Real.sqrt Φαα * Real.sqrt Φββ) * (relu (z.ofLp 0) * relu (z.ofLp 1)) := by ring
    _ = Real.sqrt (Φαα * Φββ) * (relu (z.ofLp 0) * relu (z.ofLp 1)) := by rw [Real.sqrt_mul hΦαα]

/-- Pullback of the ReLU indicator product under diagonal scaling:
positive multipliers leave signs invariant, so
`reluIndicator (D z)₀ * reluIndicator (D z)₁ = reluIndicator z₀ * reluIndicator z₁`. -/
lemma reluIndicator_mul_reluIndicator_toEuclideanCLM_diagScale
    (Φαα Φββ : ℝ) (hΦαα : 0 < Φαα) (hΦββ : 0 < Φββ)
    (z : EuclideanSpace ℝ (Fin 2)) :
    reluIndicator ((toEuclideanCLM (𝕜 := ℝ) (!![Real.sqrt Φαα, 0; 0,
        Real.sqrt Φββ] : Matrix (Fin 2) (Fin 2) ℝ) z).ofLp 0) *
      reluIndicator ((toEuclideanCLM (𝕜 := ℝ) (!![Real.sqrt Φαα, 0; 0,
          Real.sqrt Φββ] : Matrix (Fin 2) (Fin 2) ℝ) z).ofLp 1) =
      reluIndicator (z.ofLp 0) * reluIndicator (z.ofLp 1) := by
  obtain ⟨h0, h1⟩ := toEuclideanCLM_diagScale_apply (Real.sqrt Φαα) (Real.sqrt Φββ) z
  rw [h0, h1]
  have h_sqrt_α : 0 < Real.sqrt Φαα := Real.sqrt_pos.mpr hΦαα
  have h_sqrt_β : 0 < Real.sqrt Φββ := Real.sqrt_pos.mpr hΦββ
  rw [reluIndicator_pos_mul (Real.sqrt Φαα) (z.ofLp 0) h_sqrt_α]
  rw [reluIndicator_pos_mul (Real.sqrt Φββ) (z.ofLp 1) h_sqrt_β]

/-! ### Trigonometric Conversion -/

/-- Trigonometric bridge connecting the Cho-Saul derivative orthant probability to the
complementary arccosine form `(π - arccos ρ) / (2π)`. -/
lemma div_two_pi_pi_sub_arccos_eq_arcsin (ρ : ℝ) :
    (Real.pi - Real.arccos ρ) / (2 * Real.pi) = 1 / 4 + (1 / (2 * Real.pi)) * Real.arcsin ρ := by
  rw [Real.arccos_eq_pi_div_two_sub_arcsin]
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp
  ring

/-- Adjoint of the continuous linear map induced by a real 2x2 matrix on `EuclideanSpace ℝ (Fin 2)`.
-/
lemma toEuclideanCLM_adjoint (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (toEuclideanCLM (𝕜 := ℝ) A).adjoint = toEuclideanCLM (𝕜 := ℝ) Aᵀ := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [inner_toEuclideanCLM]
  rw [real_inner_comm]
  rw [inner_toEuclideanCLM]
  simp only [dotProduct, mulVec, Fin.sum_univ_two, transpose_apply]
  ring

/-- Self-adjointness of the 2x2 diagonal scaling operator. -/
lemma toEuclideanCLM_diagScale_adjoint (s0 s1 : ℝ) :
    let D := (!![s0, 0; 0, s1] : Matrix (Fin 2) (Fin 2) ℝ)
    (toEuclideanCLM (𝕜 := ℝ) D).adjoint = toEuclideanCLM (𝕜 := ℝ) D := by
  intro D
  rw [toEuclideanCLM_adjoint D]
  have hD : Dᵀ = D := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [D]
  rw [hD]

/-- Cholesky factorization of the 2x2 correlation matrix: `L * Lᵀ = !![1, ρ; ρ, 1]`. -/
lemma cholesky2x2_mul_transpose (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1) 1) :
    let L : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; ρ, Real.sqrt (1 - ρ ^ 2)]
    L * Lᵀ = !![1, ρ; ρ, 1] := by
  intro L
  ext i j
  fin_cases i <;> fin_cases j
  · dsimp [L]
    simp [Matrix.mul_apply, transpose_apply, Fin.sum_univ_two]
  · dsimp [L]
    simp [Matrix.mul_apply, transpose_apply, Fin.sum_univ_two]
  · dsimp [L]
    simp [Matrix.mul_apply, transpose_apply, Fin.sum_univ_two]
  · dsimp [L]
    have h_diff : 0 ≤ 1 - ρ ^ 2 := by
      rcases hρ with ⟨h_ge, h_le⟩
      nlinarith
    simp [Matrix.mul_apply, transpose_apply, Fin.sum_univ_two, Real.mul_self_sqrt h_diff]
    ring

/-- Pushforward of the standard bivariate normal distribution under the lower-triangular Cholesky
factor `L_ρ = !![1, 0; ρ, √(1 - ρ²)]` yields the standardized correlation normal `𝒩(0, R_ρ)`. -/
lemma map_cholesky2x2_stdGaussian (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1) 1) :
    let L : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; ρ, Real.sqrt (1 - ρ ^ 2)]
    Measure.map (toEuclideanCLM (𝕜 := ℝ) L) (stdGaussian (EuclideanSpace ℝ (Fin 2))) =
      multivariateGaussian 0 !![1, ρ; ρ, 1] := by
  intro L
  have hR_pos : (!![1, ρ; ρ, 1] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef :=
    corrMatrix2x2_posSemidef hρ
  set T := toEuclideanCLM (𝕜 := ℝ) L
  set μ_target := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) !![1, ρ; ρ, 1]
  have : IsGaussian (Measure.map T (stdGaussian (EuclideanSpace ℝ (Fin 2)))) := isGaussian_map T
  have : IsGaussian μ_target := isGaussian_multivariateGaussian
  apply ProbabilityTheory.IsGaussian.ext
  · simp only [id_eq]
    rw [integral_id_multivariateGaussian]
    rw [integral_map T.continuous.measurable.aemeasurable (by fun_prop)]
    have hT_int : ∫ x, T x ∂(stdGaussian (EuclideanSpace ℝ (Fin 2))) =
        T (∫ x, x ∂(stdGaussian (EuclideanSpace ℝ (Fin 2)))) :=
      ContinuousLinearMap.integral_comp_comm T IsGaussian.integrable_id
    rw [hT_int]
    rw [integral_id_stdGaussian]
    exact ContinuousLinearMap.map_zero T
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id T u v]
    rw [toEuclideanCLM_adjoint L]
    rw [covarianceBilin_stdGaussian]
    rw [innerSL_apply_apply]
    rw [inner_toEuclideanCLM]
    rw [covarianceBilin_multivariateGaussian hR_pos]
    have h_u : (toEuclideanCLM (𝕜 := ℝ) Lᵀ u : Fin 2 → ℝ) = Lᵀ *ᵥ u := ofLp_toEuclideanCLM Lᵀ u
    rw [h_u]
    have h_eval : (Lᵀ *ᵥ (u : Fin 2 → ℝ)) ⬝ᵥ (Lᵀ *ᵥ (v : Fin 2 → ℝ)) =
        (u : Fin 2 → ℝ) ⬝ᵥ (L * Lᵀ) *ᵥ (v : Fin 2 → ℝ) := by
      rw [← vecMul_transpose]
      rw [dotProduct_mulVec]
      rw [transpose_transpose]
      rw [vecMul_vecMul]
      rw [dotProduct_mulVec]
    rw [h_eval]
    have h_L := cholesky2x2_mul_transpose ρ hρ
    dsimp [L] at h_L
    rw [h_L]

/-! ### Step 1: Reduction to Standardized Variables via Positive Homogeneity -/

/-- Scaling of bivariate Gaussian distributions: pushforward of the standardized bivariate normal
under the diagonal standard deviation scaling yields the unstandardized bivariate normal (Step 1).
-/
lemma map_diagScale2x2_multivariateGaussian
    (Φαα Φββ Φαβ : ℝ) (hΦαα : 0 < Φαα) (hΦββ : 0 < Φββ)
    (hSigma : (show Matrix (Fin 2) (Fin 2) ℝ from !![Φαα, Φαβ; Φαβ, Φββ]).PosSemidef) :
    let ρ := Φαβ / Real.sqrt (Φαα * Φββ)
    let D := (!![Real.sqrt Φαα, 0; 0, Real.sqrt Φββ] : Matrix (Fin 2) (Fin 2) ℝ)
    Measure.map (toEuclideanCLM (𝕜 := ℝ) D) (multivariateGaussian 0 !![1, ρ; ρ, 1]) =
      multivariateGaussian 0 !![Φαα, Φαβ; Φαβ, Φββ] := by
  intro ρ D
  have hρ : ρ ∈ Set.Icc (-1) 1 := pearsonRho_mem_Icc Φαα Φββ Φαβ hΦαα hΦββ hSigma
  have hR_pos : (!![1, ρ; ρ, 1] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef :=
    corrMatrix2x2_posSemidef hρ
  set μ_R := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) !![1, ρ; ρ, 1]
  set μ_target := multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) !![Φαα, Φαβ; Φαβ, Φββ]
  set T := toEuclideanCLM (𝕜 := ℝ) D
  have : IsGaussian (Measure.map T μ_R) := isGaussian_map T
  have : IsGaussian μ_target := isGaussian_multivariateGaussian
  apply ProbabilityTheory.IsGaussian.ext
  · simp only [id_eq]
    rw [integral_id_multivariateGaussian]
    rw [integral_map T.continuous.measurable.aemeasurable (by fun_prop)]
    have hT_int : ∫ x, T x ∂μ_R = T (∫ x, x ∂μ_R) :=
        ContinuousLinearMap.integral_comp_comm T IsGaussian.integrable_id
    rw [hT_int]
    dsimp [μ_R]
    rw [integral_id_multivariateGaussian]
    exact ContinuousLinearMap.map_zero T
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id T u v]
    have hT_adj : T.adjoint = T := toEuclideanCLM_diagScale_adjoint (Real.sqrt Φαα) (Real.sqrt Φββ)
    rw [hT_adj]
    rw [covarianceBilin_multivariateGaussian hR_pos]
    rw [covarianceBilin_multivariateGaussian hSigma]
    have h_u : (T u : Fin 2 → ℝ) = D *ᵥ u := ofLp_toEuclideanCLM D u
    have h_v : (T v : Fin 2 → ℝ) = D *ᵥ v := ofLp_toEuclideanCLM D v
    rw [h_u, h_v]
    have h_scale := diagScale2x2_mul_corr_mul_diagScale Φαα Φββ Φαβ hΦαα hΦββ
    dsimp [D, ρ] at h_scale
    have h_eval : (D *ᵥ (u : Fin 2 → ℝ)) ⬝ᵥ !![1, ρ; ρ, 1] *ᵥ (D *ᵥ (v : Fin 2 → ℝ)) =
        (u : Fin 2 → ℝ) ⬝ᵥ (D * !![1, ρ; ρ, 1] * Dᵀ) *ᵥ (v : Fin 2 → ℝ) := by
      simp only [dotProduct, mulVec, Fin.sum_univ_two, D]
      simp only [cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons, head_cons, smul_cons,
        smul_eq_mul, mul_one, smul_empty, tail_cons, zero_smul, empty_vecMul, add_zero, zero_add,
        empty_mul, Equiv.symm_apply_apply, Fin.isValue, Matrix.mul_apply, of_apply, cons_val',
        cons_val_fin_one, cons_val_zero, transpose_apply, Fin.sum_univ_two, cons_val_one, mul_zero]
      ring
    rw [h_eval, h_scale]

/-- Change-of-variables skeleton shared by `expected_relu_mul_relu_eq_scale_mul_standardized` and
`expected_reluIndicator_mul_reluIndicator_eq_standardized`: both pull an integral against
`multivariateGaussian 0 !![Φαα,Φαβ;Φαβ,Φββ]` back, through the diagonal scaling map
`D = !![√Φαα, 0; 0, √Φββ]`, to the same integral against the standardized correlation measure
`multivariateGaussian 0 !![1,ρ;ρ,1]`. They differ only in the integrand `g` and how it transforms
under the pullback (`hpullback`) — a `√(ΦααΦββ)` factor for the ReLU product, none for the
sign-invariant indicator product — so that single difference is exposed as the `c` parameter. -/
private lemma integral_multivariateGaussian_eq_const_mul_integral_of_diagScale_pullback
    (Φαα Φββ Φαβ : ℝ) (hΦαα : 0 < Φαα) (hΦββ : 0 < Φββ)
    (hSigma : (show Matrix (Fin 2) (Fin 2) ℝ from !![Φαα, Φαβ; Φαβ, Φββ]).PosSemidef)
    (g : EuclideanSpace ℝ (Fin 2) → ℝ) (hg_meas : Measurable g) (c : ℝ)
    (hpullback : ∀ z : EuclideanSpace ℝ (Fin 2),
      g (toEuclideanCLM (𝕜 := ℝ)
        (!![Real.sqrt Φαα, 0; 0, Real.sqrt Φββ] : Matrix (Fin 2) (Fin 2) ℝ) z) = c * g z) :
    let ρ := Φαβ / Real.sqrt (Φαα * Φββ)
    ∫ z : EuclideanSpace ℝ (Fin 2), g z ∂(multivariateGaussian 0 !![Φαα, Φαβ; Φαβ, Φββ]) =
      c * ∫ z : EuclideanSpace ℝ (Fin 2), g z ∂(multivariateGaussian 0 !![1, ρ; ρ, 1]) := by
  intro ρ
  let D := (!![Real.sqrt Φαα, 0; 0, Real.sqrt Φββ] : Matrix (Fin 2) (Fin 2) ℝ)
  have hmap := map_diagScale2x2_multivariateGaussian Φαα Φββ Φαβ hΦαα hΦββ hSigma
  rw [← hmap]
  rw [integral_map (toEuclideanCLM (𝕜 := ℝ) D).continuous.measurable.aemeasurable
    hg_meas.aestronglyMeasurable]
  have h_comp : g ∘ (toEuclideanCLM (𝕜 := ℝ) D) = fun z => c * g z := funext hpullback
  change ∫ z, (g ∘ (toEuclideanCLM (𝕜 := ℝ) D)) z ∂(multivariateGaussian 0 !![1, ρ; ρ, 1]) = _
  rw [h_comp]
  exact integral_const_mul c g

/--
Informal proof of Step 1 for ReLU products:
By positive homogeneity `relu (c * u) = c * relu u` for `c ≥ 0`, scaling the centered Gaussian
vector `(h^α, h^β) ~ 𝒩(0, Σ)` by diagonal factors `1/√(Φαα)` and `1/√(Φββ)` produces a standard
bivariate normal vector `(z₁, z₂) ~ 𝒩(0, R_ρ)` where `R_ρ = !![1, ρ; ρ, 1]`.
Linearity of expectation pulls out the factor `√(Φαα * Φββ)`.
-/
lemma expected_relu_mul_relu_eq_scale_mul_standardized
    (Φαα Φββ Φαβ : ℝ) (hΦαα : 0 < Φαα) (hΦββ : 0 < Φββ)
    (hSigma : (show Matrix (Fin 2) (Fin 2) ℝ from !![Φαα, Φαβ; Φαβ, Φββ]).PosSemidef) :
    let ρ := Φαβ / Real.sqrt (Φαα * Φββ)
    ∫ z : EuclideanSpace ℝ (Fin 2), relu (z.ofLp 0) * relu (z.ofLp 1)
      ∂(multivariateGaussian 0 !![Φαα, Φαβ; Φαβ, Φββ]) =
      Real.sqrt (Φαα * Φββ) *
        ∫ z : EuclideanSpace ℝ (Fin 2), relu (z.ofLp 0) * relu (z.ofLp 1)
          ∂(multivariateGaussian 0 !![1, ρ; ρ, 1]) := by
  intro ρ
  exact integral_multivariateGaussian_eq_const_mul_integral_of_diagScale_pullback Φαα Φββ Φαβ
    hΦαα hΦββ hSigma (fun z => relu (z.ofLp 0) * relu (z.ofLp 1))
    ((continuous_relu.comp (EuclideanSpace.proj (0 : Fin 2)).continuous).mul
      (continuous_relu.comp (EuclideanSpace.proj (1 : Fin 2)).continuous)).measurable
    (Real.sqrt (Φαα * Φββ))
    (relu_mul_relu_toEuclideanCLM_diagScale Φαα Φββ (le_of_lt hΦαα) (le_of_lt hΦββ))

/--
Informal proof of Step 1 for derivative products:
Because scaling by positive constants `√(Φαα), √(Φββ) > 0` leaves signs invariant
(`reluIndicator (c * u) = reluIndicator u`), the expected derivative product reduces identically
to the standardized orthant probability `p(ρ) = 𝔼_{(z₁, z₂)}[1[z₁ ≥ 0] 1[z₂ ≥ 0]]`.
-/
lemma expected_reluIndicator_mul_reluIndicator_eq_standardized
    (Φαα Φββ Φαβ : ℝ) (hΦαα : 0 < Φαα) (hΦββ : 0 < Φββ)
    (hSigma : (show Matrix (Fin 2) (Fin 2) ℝ from !![Φαα, Φαβ; Φαβ, Φββ]).PosSemidef) :
    let ρ := Φαβ / Real.sqrt (Φαα * Φββ)
    ∫ z : EuclideanSpace ℝ (Fin 2), reluIndicator (z.ofLp 0) * reluIndicator (z.ofLp 1)
      ∂(multivariateGaussian 0 !![Φαα, Φαβ; Φαβ, Φββ]) =
      ∫ z : EuclideanSpace ℝ (Fin 2), reluIndicator (z.ofLp 0) * reluIndicator (z.ofLp 1)
        ∂(multivariateGaussian 0 !![1, ρ; ρ, 1]) := by
  intro ρ
  have h := integral_multivariateGaussian_eq_const_mul_integral_of_diagScale_pullback Φαα Φββ Φαβ
    hΦαα hΦββ hSigma (fun z => reluIndicator (z.ofLp 0) * reluIndicator (z.ofLp 1))
    ((measurable_reluIndicator.comp (EuclideanSpace.proj (0 : Fin 2)).measurable).mul
      (measurable_reluIndicator.comp (EuclideanSpace.proj (1 : Fin 2)).measurable)) 1
    (fun z => by
      simpa using reluIndicator_mul_reluIndicator_toEuclideanCLM_diagScale Φαα Φββ hΦαα hΦββ z)
  simpa using h

/-! ### Steps 2–3: Cholesky Reduction and Polar-Coordinate Evaluation -/

/-- Pull a correlated standard Gaussian integral back to independent Gaussian coordinates.
The Cholesky factor has rows `(1, 0)` and
`(cos (arccos ρ), sin (arccos ρ))`. -/
private lemma integral_corrGaussian_eq_angle
    (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1) 1) :
    ∫ z : EuclideanSpace ℝ (Fin 2), f (z.ofLp 0) * g (z.ofLp 1)
      ∂(multivariateGaussian 0 !![1, ρ; ρ, 1]) =
    ∫ z : EuclideanSpace ℝ (Fin 2), f (z.ofLp 0) *
        g (Real.cos (Real.arccos ρ) * z.ofLp 0 +
          Real.sin (Real.arccos ρ) * z.ofLp 1)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin 2))) := by
  let L : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; ρ, Real.sqrt (1 - ρ ^ 2)]
  have hmap := map_cholesky2x2_stdGaussian ρ hρ
  dsimp [L] at hmap
  rw [← hmap]
  have hint : AEStronglyMeasurable
      (fun z : EuclideanSpace ℝ (Fin 2) => f (z.ofLp 0) * g (z.ofLp 1))
      (Measure.map (toEuclideanCLM (𝕜 := ℝ) L)
        (stdGaussian (EuclideanSpace ℝ (Fin 2)))) :=
    (((hf.comp (EuclideanSpace.proj (0 : Fin 2)).measurable).mul
      (hg.comp (EuclideanSpace.proj (1 : Fin
          2)).measurable)).stronglyMeasurable).aestronglyMeasurable
  rw [integral_map (toEuclideanCLM (𝕜 := ℝ) L).continuous.measurable.aemeasurable hint]
  change ∫ z : EuclideanSpace ℝ (Fin 2),
      f ((toEuclideanCLM (𝕜 := ℝ) L z).ofLp 0) *
        g ((toEuclideanCLM (𝕜 := ℝ) L z).ofLp 1)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin 2))) = _
  congr 1 with z
  have hz := ofLp_toEuclideanCLM L z
  have hz0 : (toEuclideanCLM (𝕜 := ℝ) L z).ofLp 0 = z.ofLp 0 := by
    rw [hz]
    simp [L, mulVec, dotProduct, Fin.sum_univ_two]
  have hz1 : (toEuclideanCLM (𝕜 := ℝ) L z).ofLp 1 =
      ρ * z.ofLp 0 + Real.sqrt (1 - ρ ^ 2) * z.ofLp 1 := by
    rw [hz]
    simp [L, mulVec, dotProduct, Fin.sum_univ_two]
  have htheta0 : 0 ≤ Real.arccos ρ := Real.arccos_nonneg ρ
  have hthetapi : Real.arccos ρ ≤ Real.pi := Real.arccos_le_pi ρ
  have hcos : Real.cos (Real.arccos ρ) = ρ := Real.cos_arccos hρ.1 hρ.2
  have hsin : Real.sin (Real.arccos ρ) = Real.sqrt (1 - ρ ^ 2) :=
    Real.sin_eq_sqrt_one_sub_cos_sq htheta0 hthetapi |>.trans (by rw [hcos])
  rw [hz0, hz1, hcos, hsin]

/-- The derivative kernel is the angular size of the intersection of two half-planes. -/
lemma expected_reluIndicator_mul_reluIndicator_eq_halfspace_sector
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1) 1) :
    ∫ z : EuclideanSpace ℝ (Fin 2), reluIndicator (z.ofLp 0) * reluIndicator (z.ofLp 1)
      ∂(multivariateGaussian 0 !![1, ρ; ρ, 1]) =
      (Real.pi - Real.arccos ρ) / (2 * Real.pi) := by
  calc
    _ = ∫ z : EuclideanSpace ℝ (Fin 2), reluIndicator (z.ofLp 0) *
          reluIndicator (Real.cos (Real.arccos ρ) * z.ofLp 0 +
            Real.sin (Real.arccos ρ) * z.ofLp 1)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin 2))) :=
      integral_corrGaussian_eq_angle reluIndicator reluIndicator
        measurable_reluIndicator measurable_reluIndicator ρ hρ
    _ = _ := integral_stdGaussian_reluIndicator_angle (Real.arccos ρ)
      (Real.arccos_nonneg ρ) (Real.arccos_le_pi ρ)

/-- Standardized form of the Cho-Saul derivative kernel. -/
lemma expected_reluIndicator_mul_reluIndicator_standardized
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1) 1) :
    ∫ z : EuclideanSpace ℝ (Fin 2), reluIndicator (z.ofLp 0) * reluIndicator (z.ofLp 1)
      ∂(multivariateGaussian 0 !![1, ρ; ρ, 1]) =
      1 / 4 + (1 / (2 * Real.pi)) * Real.arcsin ρ := by
  rw [expected_reluIndicator_mul_reluIndicator_eq_halfspace_sector ρ hρ]
  exact div_two_pi_pi_sub_arccos_eq_arcsin ρ

/-- Standardized form of the Cho-Saul ReLU kernel, obtained by evaluating the same
two-dimensional Gaussian integral in polar coordinates. -/
lemma expected_relu_mul_relu_standardized
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1) 1) :
    ∫ z : EuclideanSpace ℝ (Fin 2), relu (z.ofLp 0) * relu (z.ofLp 1)
      ∂(multivariateGaussian 0 !![1, ρ; ρ, 1]) =
      (1 / (2 * Real.pi)) *
        (Real.sqrt (1 - ρ ^ 2) + ρ * (Real.pi / 2 + Real.arcsin ρ)) := by
  have htheta0 : 0 ≤ Real.arccos ρ := Real.arccos_nonneg ρ
  have hthetapi : Real.arccos ρ ≤ Real.pi := Real.arccos_le_pi ρ
  have hcos : Real.cos (Real.arccos ρ) = ρ := Real.cos_arccos hρ.1 hρ.2
  have hsin : Real.sin (Real.arccos ρ) = Real.sqrt (1 - ρ ^ 2) :=
    Real.sin_eq_sqrt_one_sub_cos_sq htheta0 hthetapi |>.trans (by rw [hcos])
  have hangle : Real.pi - Real.arccos ρ = Real.pi / 2 + Real.arcsin ρ := by
    rw [Real.arccos_eq_pi_div_two_sub_arcsin]
    ring
  calc
    _ = ∫ z : EuclideanSpace ℝ (Fin 2), relu (z.ofLp 0) *
          relu (Real.cos (Real.arccos ρ) * z.ofLp 0 +
            Real.sin (Real.arccos ρ) * z.ofLp 1)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin 2))) :=
      integral_corrGaussian_eq_angle relu relu
        continuous_relu.measurable continuous_relu.measurable ρ hρ
    _ = (Real.sin (Real.arccos ρ) +
          (Real.pi - Real.arccos ρ) * Real.cos (Real.arccos ρ)) /
          (2 * Real.pi) :=
      integral_stdGaussian_relu_angle (Real.arccos ρ) htheta0 hthetapi
    _ = _ := by
      rw [hcos, hsin, hangle]
      ring

/-! ### Step 4: Final Scaling Assembly -/

/-- **Proposition 2.5 (Cho-Saul / Arc-Cosine Kernel for ReLU Derivative - 1st order / Derivative
Kernel)**:
Under centered bivariate Gaussian preactivations `(h^α, h^β) ~ 𝒩(0, Σ)` with positive diagonal
variances `Φαα, Φββ > 0` and correlation `ρ = Φαβ / √(Φαα * Φββ) ∈ [-1, 1]`, the expected product of
ReLU weak derivatives equals the orthant probability: `1/4 + (1 / (2π)) * arcsin ρ`. -/
theorem expected_reluIndicator_mul_reluIndicator_bivariate
    (Φαα Φββ Φαβ : ℝ) (hΦαα : 0 < Φαα) (hΦββ : 0 < Φββ)
    (hSigma : (show Matrix (Fin 2) (Fin 2) ℝ from !![Φαα, Φαβ; Φαβ, Φββ]).PosSemidef) :
    let ρ := Φαβ / Real.sqrt (Φαα * Φββ)
    ∫ z : EuclideanSpace ℝ (Fin 2), reluIndicator (z.ofLp 0) * reluIndicator (z.ofLp 1)
      ∂(multivariateGaussian 0 !![Φαα, Φαβ; Φαβ, Φββ]) =
      1 / 4 + (1 / (2 * Real.pi)) * Real.arcsin ρ := by
  intro ρ
  have hρ : ρ ∈ Set.Icc (-1) 1 := pearsonRho_mem_Icc Φαα Φββ Φαβ hΦαα hΦββ hSigma
  rw [expected_reluIndicator_mul_reluIndicator_eq_standardized Φαα Φββ Φαβ hΦαα hΦββ hSigma]
  exact expected_reluIndicator_mul_reluIndicator_standardized ρ hρ

/-- Proposition 2.5 stated with the weak-derivative name used in the paper. -/
theorem expected_reluDeriv_mul_reluDeriv_bivariate
    (Φαα Φββ Φαβ : ℝ) (hΦαα : 0 < Φαα) (hΦββ : 0 < Φββ)
    (hSigma : (show Matrix (Fin 2) (Fin 2) ℝ from
      !![Φαα, Φαβ; Φαβ, Φββ]).PosSemidef) :
    let ρ := Φαβ / Real.sqrt (Φαα * Φββ)
    ∫ z : EuclideanSpace ℝ (Fin 2), reluDeriv (z.ofLp 0) * reluDeriv (z.ofLp 1)
      ∂(multivariateGaussian 0 !![Φαα, Φαβ; Φαβ, Φββ]) =
      1 / 4 + (1 / (2 * Real.pi)) * Real.arcsin ρ := by
  rw [reluDeriv_eq_reluIndicator]
  exact expected_reluIndicator_mul_reluIndicator_bivariate
    Φαα Φββ Φαβ hΦαα hΦββ hSigma

/-- **Proposition 2.5 (Cho-Saul / Arc-Cosine Kernel for ReLU - 0th order / NNGP Kernel)**:
Under centered bivariate Gaussian preactivations `(h^α, h^β) ~ 𝒩(0, Σ)` with positive diagonal
variances `Φαα, Φββ > 0` and correlation `ρ = Φαβ / √(Φαα * Φββ) ∈ [-1, 1]`, the expected product of
ReLU activations is `(√(Φαα * Φββ) / (2π)) * (√(1 - ρ²) + ρ * (π/2 + arcsin ρ))`. -/
theorem expected_relu_mul_relu_bivariate
    (Φαα Φββ Φαβ : ℝ) (hΦαα : 0 < Φαα) (hΦββ : 0 < Φββ)
    (hSigma : (show Matrix (Fin 2) (Fin 2) ℝ from !![Φαα, Φαβ; Φαβ, Φββ]).PosSemidef) :
    let ρ := Φαβ / Real.sqrt (Φαα * Φββ)
    ∫ z : EuclideanSpace ℝ (Fin 2), relu (z.ofLp 0) * relu (z.ofLp 1)
      ∂(multivariateGaussian 0 !![Φαα, Φαβ; Φαβ, Φββ]) =
      (Real.sqrt (Φαα * Φββ) / (2 * Real.pi)) *
        (Real.sqrt (1 - ρ ^ 2) + ρ * (Real.pi / 2 + Real.arcsin ρ)) := by
  intro ρ
  have hρ : ρ ∈ Set.Icc (-1) 1 := pearsonRho_mem_Icc Φαα Φββ Φαβ hΦαα hΦββ hSigma
  rw [expected_relu_mul_relu_eq_scale_mul_standardized Φαα Φββ Φαβ hΦαα hΦββ hSigma]
  rw [expected_relu_mul_relu_standardized ρ hρ]
  ring

/-- For ReLU activations, the off-diagonal bivariate limiting recurrence entry has closed form
given by the Cho-Saul / Arc-Cosine kernel (Proposition 2.5). -/
theorem limitingRecurrence_relu_bivariate
    (σw σb Φαα Φββ Φαβ : ℝ) (hΦαα : 0 < Φαα) (hΦββ : 0 < Φββ)
    (hSigma : (show Matrix (Fin 2) (Fin 2) ℝ from !![Φαα, Φαβ; Φαβ, Φββ]).PosSemidef) :
    let ρ := Φαβ / Real.sqrt (Φαα * Φββ)
    σb ^ 2 + σw ^ 2 * (∫ z : EuclideanSpace ℝ (Fin 2),
      relu (z.ofLp 0) * relu (z.ofLp 1) ∂(multivariateGaussian 0 !![Φαα, Φαβ; Φαβ, Φββ])) =
      σb ^ 2 + σw ^ 2 * ((Real.sqrt (Φαα * Φββ) / (2 * Real.pi)) *
        (Real.sqrt (1 - ρ ^ 2) + ρ * (Real.pi / 2 + Real.arcsin ρ))) := by
  intro ρ
  rw [expected_relu_mul_relu_bivariate Φαα Φββ Φαβ hΦαα hΦββ hSigma]

end NTK
