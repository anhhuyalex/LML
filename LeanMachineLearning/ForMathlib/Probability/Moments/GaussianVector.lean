/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.CovarianceBilin

/-!
# Gaussian vectors: representation and Stein's identity

A centered Gaussian vector `X : κ → Ω → ℝ` (`HasGaussianLaw`) has the law of a linear image
`A ξ` of i.i.d. standard Gaussians with `A Aᵀ` its covariance matrix
(`exists_matrix_map_eq_pi_gaussianReal`); this is `multivariateGaussian 0 S`
(`Mathlib/Probability/Distributions/Gaussian/Multivariate.lean`) written through
`Measure.pi fun _ => gaussianReal 0 1`.  Combined with Stein's identity for linear images
(`ForMathlib/Probability/Moments/GaussianStein.lean`), this gives the multivariate Gaussian
integration by parts of Panchenko, Eq. (1.25):
`𝔼[X i F(X)] = ∑ l, 𝔼[X i X l] 𝔼[∂ₗ F(X)]` (`integral_mul_comp_eq_sum_integral_mul`).
-/

@[expose] public section

open MeasureTheory Matrix
open scoped NNReal ENNReal MatrixOrder

namespace ProbabilityTheory

variable {κ Ω : Type*} [Fintype κ] [DecidableEq κ] {mΩ : MeasurableSpace Ω} {P : Measure Ω}

omit [Fintype κ] [DecidableEq κ] in
/-- The covariance matrix of a Gaussian vector is positive semidefinite. -/
theorem posSemidef_covariance_matrix [Finite κ] {X : κ → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω k => X k ω) P) :
    (Matrix.of fun i j => cov[X i, X j; P]).PosSemidef := by
  have := Fintype.ofFinite κ
  have hmem : ∀ i, MemLp (X i) 2 P := fun i => (hX.eval i).memLp_two
  have := hX.isProbabilityMeasure
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    simp [covariance_comm]
  · have h := (isPosSemidef_covarianceBilin (μ := P.map (fun ω => WithLp.toLp 2 (X · ω)))).nonneg
      (WithLp.toLp 2 x)
    have h2 := covarianceBilin_apply_pi hmem (WithLp.toLp 2 x) (WithLp.toLp 2 x)
    change 0 ≤ covarianceBilin _ _ _ at h
    rw [h2] at h
    simpa [mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using h


omit [DecidableEq κ] in
/-- **A centered Gaussian vector is a linear image of i.i.d. standard Gaussians.**  If
`X = (X k)_k` is centered with `HasGaussianLaw`, then its law is the image of
`Measure.pi (fun _ => gaussianReal 0 1)` under `ξ ↦ A ξ`, where `A Aᵀ` is the covariance matrix. -/
theorem exists_matrix_map_eq_pi_gaussianReal {X : κ → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω k => X k ω) P) (hmean : ∀ k, ∫ ω, X k ω ∂P = 0) :
    ∃ A : Matrix κ κ ℝ,
      P.map (fun ω k => X k ω) =
        (Measure.pi fun _ : κ => gaussianReal 0 1).map (fun ξ => A *ᵥ ξ) ∧
      A * Aᵀ = Matrix.of fun i j => cov[X i, X j; P] := by
  classical
  have hP := hX.isProbabilityMeasure
  have hmem : ∀ i, MemLp (X i) 2 P := fun i => (hX.eval i).memLp_two
  have hS := posSemidef_covariance_matrix hX
  set S : Matrix κ κ ℝ := Matrix.of fun i j => cov[X i, X j; P] with hSdef
  have hAsym : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
    have h := (CFC.sqrt_nonneg S).isSelfAdjoint
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact h.star_eq
  refine ⟨CFC.sqrt S, ?_, by rw [hAsym]; exact CFC.sqrt_mul_sqrt_self S hS.nonneg⟩
  have hY := hX.toLp_pi 2
  have hν : P.map (fun ω => WithLp.toLp 2 (X · ω)) = multivariateGaussian 0 S := by
    have := hY.isGaussian_map
    refine IsGaussian.ext ?_ ?_
    · rw [integral_id_multivariateGaussian']
      rw [integral_map hY.aemeasurable aestronglyMeasurable_id]
      ext k
      have hint : Integrable (fun ω => WithLp.toLp 2 (X · ω)) P := hY.integrable
      have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj k) hint
      simpa [hmean k] using this.symm
    · ext x y
      rw [covarianceBilin_apply_pi hmem, covarianceBilin_multivariateGaussian hS]
      simp only [hSdef, dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
  have hmap : P.map (fun ω k => X k ω) = (P.map (fun ω => WithLp.toLp 2 (X · ω))).map
      (fun z : EuclideanSpace ℝ κ => z.ofLp) := by
    rw [AEMeasurable.map_map_of_aemeasurable (g := fun z : EuclideanSpace ℝ κ => z.ofLp)
      (by exact (PiLp.continuous_ofLp 2 _).measurable.aemeasurable) hY.aemeasurable]
    rfl
  rw [hmap, hν, multivariateGaussian, ← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop)
    (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext ξ k
  simp [Matrix.toEuclideanCLM_toLp]


/-- **Gaussian integration by parts (Panchenko Eq. (1.25)).**  For a centered Gaussian vector
`X` and a differentiable `F` whose value and partial derivatives grow at most exponentially in
`‖y‖₁`, `𝔼[X i F(X)] = ∑ l, 𝔼[X i X l] 𝔼[∂ₗ F(X)]`, where
`∂ₗ F y = fderiv ℝ F y (Pi.single l 1)`. -/
theorem integral_mul_comp_eq_sum_integral_mul {X : κ → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω k => X k ω) P) (hmean : ∀ k, ∫ ω, X k ω ∂P = 0) (i : κ)
    {F : (κ → ℝ) → ℝ} (hF : Differentiable ℝ F) {C c : ℝ}
    (hFg : ∀ y, |F y| ≤ C * Real.exp (c * ∑ l, |y l|)) {D d : κ → ℝ}
    (hFg' : ∀ l y, |fderiv ℝ F y (Pi.single l 1)| ≤ D l * Real.exp (d l * ∑ l, |y l|)) :
    ∫ ω, X i ω * F (fun k => X k ω) ∂P =
      ∑ l, (∫ ω, X i ω * X l ω ∂P) * ∫ ω, fderiv ℝ F (fun k => X k ω) (Pi.single l 1) ∂P := by
  have hP := hX.isProbabilityMeasure
  obtain ⟨A, hlaw, hA⟩ := exists_matrix_map_eq_pi_gaussianReal hX hmean
  have hXm : AEMeasurable (fun ω k => X k ω) P := hX.aemeasurable
  have hAm : Measurable fun ξ : κ → ℝ => A *ᵥ ξ := by fun_prop
  have hint : ∀ {f : (κ → ℝ) → ℝ}, Measurable f →
      ∫ ω, f (fun k => X k ω) ∂P =
        ∫ ξ, f (A *ᵥ ξ) ∂(Measure.pi fun _ : κ => gaussianReal 0 1) := by
    intro f hf
    rw [← integral_map hXm hf.aestronglyMeasurable, hlaw,
      integral_map hAm.aemeasurable hf.aestronglyMeasurable]
  have hcov : ∀ l, ∫ ω, X i ω * X l ω ∂P = (A * Aᵀ) i l := by
    intro l
    have hmem : ∀ i, MemLp (X i) 2 P := fun i => (hX.eval i).memLp_two
    rw [hA]
    simp only [Matrix.of_apply]
    rw [covariance_eq_sub (hmem i) (hmem l), hmean, hmean]
    simp
  have h1 := hint (f := fun y => y i * F y)
    ((measurable_pi_apply i).mul hF.continuous.measurable)
  have h2 := fun l => hint (f := fun y => fderiv ℝ F y (Pi.single l 1))
    (measurable_fderiv_apply_const ℝ F _)
  simp only at h1 h2
  rw [h1, integral_mulVec_mul_comp_mulVec_eq_sum A i hF hFg hFg']
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hcov l, h2 l]

section Aux

variable {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]

/-- Exponential growth in `‖y‖₁` is inherited by restricting a vector to a sub-index set. -/
theorem abs_comp_inr_le_of_exp_growth {G : (κ₂ → ℝ) → ℝ} {C c : ℝ}
    (hG : ∀ y, |G y| ≤ C * Real.exp (c * ∑ l, |y l|)) (v : κ₁ ⊕ κ₂ → ℝ) :
    |G (fun l => v (Sum.inr l))| ≤ C * Real.exp (|c| * ∑ s, |v s|) := by
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hG 0)) (Real.exp_pos _)
  refine (hG _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC)
  calc c * ∑ l, |v (Sum.inr l)| ≤ |c| * ∑ l, |v (Sum.inr l)| :=
        mul_le_mul_of_nonneg_right (le_abs_self c) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    _ ≤ |c| * ∑ s, |v s| := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
        rw [Fintype.sum_sum_type]
        exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => abs_nonneg _)

variable [DecidableEq κ₂]

omit [Fintype κ₁] in
/-- **Gaussian integration by parts against a jointly Gaussian test variable.**
If the centered family `W ⊕ X` is jointly Gaussian and `F` is differentiable with exponentially
bounded value and partial derivatives, then `𝔼[W i F(X)] = ∑ l, 𝔼[W i X l] 𝔼[∂ₗ F(X)]`.
With `W = X` this is `integral_mul_comp_eq_sum_integral_mul`; in applications `W` is the part of
the Gaussian field that does not enter `F`. -/
theorem integral_mul_comp_eq_sum_integral_mul_of_sum [Finite κ₁] {W : κ₁ → Ω → ℝ} {X : κ₂ → Ω → ℝ}
    (hWX : HasGaussianLaw (fun ω s => Sum.elim W X s ω) P)
    (hW : ∀ k, ∫ ω, W k ω ∂P = 0) (hX : ∀ l, ∫ ω, X l ω ∂P = 0) (i : κ₁)
    {F : (κ₂ → ℝ) → ℝ} (hF : Differentiable ℝ F) {C c : ℝ}
    (hFg : ∀ y, |F y| ≤ C * Real.exp (c * ∑ l, |y l|)) {D d : κ₂ → ℝ}
    (hFg' : ∀ l y, |fderiv ℝ F y (Pi.single l 1)| ≤ D l * Real.exp (d l * ∑ l, |y l|)) :
    ∫ ω, W i ω * F (fun l => X l ω) ∂P =
      ∑ l, (∫ ω, W i ω * X l ω ∂P) * ∫ ω, fderiv ℝ F (fun k => X k ω) (Pi.single l 1) ∂P := by
  have := Fintype.ofFinite κ₁
  classical
  let R : (κ₁ ⊕ κ₂ → ℝ) →L[ℝ] (κ₂ → ℝ) :=
    ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (Sum.inr l)
  have hR : ∀ v, R v = fun l => v (Sum.inr l) := fun v => rfl
  have hF' : Differentiable ℝ (F ∘ R) := hF.comp R.differentiable
  have hfd : ∀ (v : κ₁ ⊕ κ₂ → ℝ) (s : κ₁ ⊕ κ₂),
      fderiv ℝ (F ∘ R) v (Pi.single s 1) = fderiv ℝ F (R v) (R (Pi.single s 1)) := by
    intro v s
    rw [fderiv_comp v (hF _) R.differentiableAt, R.fderiv]; rfl
  have hRs : ∀ l, R (Pi.single (Sum.inr l) (1 : ℝ)) = Pi.single l 1 := by
    intro l; ext m; simp [hR, Pi.single_apply]
  have hRl : ∀ k, R (Pi.single (Sum.inl k) (1 : ℝ)) = 0 := by
    intro k; ext m; simp [hR]
  have h := integral_mul_comp_eq_sum_integral_mul (X := Sum.elim W X) hWX
    (by rintro (k | l); exacts [hW k, hX l]) (Sum.inl i) hF' (C := C) (c := |c|)
    (fun v => abs_comp_inr_le_of_exp_growth hFg v)
    (D := Sum.elim (fun _ => 0) D) (d := Sum.elim (fun _ => 0) (fun l => |d l|))
    (by
      rintro (k | l) v
      · simp [hfd, hRl]
      · simp only [hfd, hRs, Sum.elim_inr]
        exact abs_comp_inr_le_of_exp_growth (G := fun y => fderiv ℝ F y (Pi.single l 1))
          (hFg' l) v)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hfd, hRl, hRs, map_zero,
    mul_zero, integral_zero, Finset.sum_const_zero, zero_add] at h
  simpa [hR] using h

end Aux

/-- A Gaussian process indexed by a finite type is a Gaussian vector: this passes from Mathlib's
`IsGaussianProcess` (finite-dimensional marginals) to the `HasGaussianLaw` hypothesis of
`integral_mul_comp_eq_sum_integral_mul`. -/
theorem IsGaussianProcess.hasGaussianLaw_pi {S : Type*} [Finite S] {X : S → Ω → ℝ}
    (hX : IsGaussianProcess X P) : HasGaussianLaw (fun ω s => X s ω) P := by
  have := Fintype.ofFinite S
  classical
  let L : (Finset.univ (α := S) → ℝ) →L[ℝ] (S → ℝ) :=
    ContinuousLinearMap.pi fun s => ContinuousLinearMap.proj ⟨s, Finset.mem_univ s⟩
  exact (hX.hasGaussianLaw Finset.univ).map_fun L


section Monomial

variable {κ' : Type*} [Fintype κ']

/-- A sub-product of coordinates is bounded by `exp (∑ |y l|)`. -/
theorem abs_prod_le_exp_sum (s : Finset κ') (y : κ' → ℝ) :
    |∏ i ∈ s, y i| ≤ Real.exp (∑ l, |y l|) := by
  rw [Finset.abs_prod]
  calc ∏ i ∈ s, |y i| ≤ ∏ i ∈ s, Real.exp |y i| :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
          fun i _ => by linarith [Real.add_one_le_exp (|y i|)]
    _ = Real.exp (∑ i ∈ s, |y i|) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑ l, |y l|) :=
        Real.exp_le_exp.2 (Finset.sum_le_sum_of_subset_of_nonneg s.subset_univ
          fun _ _ _ => abs_nonneg _)

variable [DecidableEq κ']

/-- The partial derivatives of the monomial `y ↦ ∏ i, y i` are the erased products. -/
theorem fderiv_prod_apply_pi_single (y : κ' → ℝ) (l : κ') :
    fderiv ℝ (fun y : κ' → ℝ => ∏ i, y i) y (Pi.single l 1) = ∏ i ∈ Finset.univ.erase l, y i := by
  rw [fderiv_finsetProd (fun i _ => differentiableAt_apply i y)]
  simp [(hasFDerivAt_apply _ y).fderiv, Pi.single_apply]

/-- **Multilinear Stein identity.**  For a centered Gaussian family `W ⊕ Y`,
`𝔼[W ∏ᵢ Yᵢ] = ∑ⱼ 𝔼[W Yⱼ] 𝔼[∏_{i ≠ j} Yᵢ]`.  This is
`integral_mul_comp_eq_sum_integral_mul_of_sum` for the monomial `F y = ∏ᵢ yᵢ`, whose value and
partial derivatives are bounded by `exp (∑ |yᵢ|)`; no integrability hypothesis is needed. -/
theorem integral_mul_prod_eq_sum_integral_prod_erase {W : Ω → ℝ} {Y : κ' → Ω → ℝ}
    (hWY : HasGaussianLaw (fun ω s => Sum.elim (fun _ : Unit => W) Y s ω) P)
    (hW : ∫ ω, W ω ∂P = 0) (hY : ∀ k, ∫ ω, Y k ω ∂P = 0) :
    ∫ ω, W ω * ∏ i, Y i ω ∂P =
      ∑ j, (∫ ω, W ω * Y j ω ∂P) * ∫ ω, ∏ i ∈ Finset.univ.erase j, Y i ω ∂P := by
  have h := integral_mul_comp_eq_sum_integral_mul_of_sum (W := fun _ : Unit => W) (X := Y) hWY
    (fun _ => hW) hY () (F := fun y => ∏ i, y i) (by fun_prop) (C := 1) (c := 1)
    (fun y => by simpa using abs_prod_le_exp_sum Finset.univ y) (D := fun _ => 1) (d := fun _ => 1)
    (fun l y => by
      rw [fderiv_prod_apply_pi_single]
      simpa using abs_prod_le_exp_sum _ y)
  simpa [fderiv_prod_apply_pi_single] using h

end Monomial

end ProbabilityTheory
