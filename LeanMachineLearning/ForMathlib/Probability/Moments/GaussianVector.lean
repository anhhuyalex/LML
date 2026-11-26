/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein
public import LeanMachineLearning.ForMathlib.MeasureTheory.Function.AEStronglyMeasurableDeriv
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.CovarianceBilin
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Pi

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
Both it and the version with a separate test variable are the coordinate form of the identity
`𝔼[W • F(X)] = 𝔼[DF(X) (𝔼[W • X])]` for vector-valued `X` and `F`
(`integral_smul_comp_eq_integral_fderiv_apply`).
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


/-- **The law of a centered Gaussian vector is `multivariateGaussian 0 S`**, `S` its covariance
matrix. -/
theorem map_toLp_eq_multivariateGaussian {X : κ → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω k => X k ω) P) (hmean : ∀ k, ∫ ω, X k ω ∂P = 0) :
    P.map (fun ω => WithLp.toLp 2 (X · ω)) =
      multivariateGaussian 0 (Matrix.of fun i j => cov[X i, X j; P]) := by
  have hP := hX.isProbabilityMeasure
  have hmem : ∀ i, MemLp (X i) 2 P := fun i => (hX.eval i).memLp_two
  have hS := posSemidef_covariance_matrix hX
  have hY := hX.toLp_pi 2
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
    simp only [dotProduct, mulVec, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-- The law of a centered Gaussian vector in `κ → ℝ` is the image of `multivariateGaussian 0 S`
under `ofLp`, `S` its covariance matrix. -/
theorem map_eq_map_multivariateGaussian {X : κ → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω k => X k ω) P) (hmean : ∀ k, ∫ ω, X k ω ∂P = 0) :
    P.map (fun ω k => X k ω) = (multivariateGaussian 0 (Matrix.of fun i j => cov[X i, X j; P])).map
      (fun z : EuclideanSpace ℝ κ => z.ofLp) := by
  classical
  rw [← map_toLp_eq_multivariateGaussian hX hmean,
    AEMeasurable.map_map_of_aemeasurable (g := fun z : EuclideanSpace ℝ κ => z.ofLp)
      (by exact (PiLp.continuous_ofLp 2 _).measurable.aemeasurable) (hX.toLp_pi 2).aemeasurable]
  rfl

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
  have hS := posSemidef_covariance_matrix hX
  set S : Matrix κ κ ℝ := Matrix.of fun i j => cov[X i, X j; P] with hSdef
  have hAsym : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
    have h := (CFC.sqrt_nonneg S).isSelfAdjoint
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact h.star_eq
  refine ⟨CFC.sqrt S, ?_, by rw [hAsym]; exact CFC.sqrt_mul_sqrt_self S hS.nonneg⟩
  rw [map_eq_map_multivariateGaussian hX hmean, multivariateGaussian, ← map_pi_eq_stdGaussian,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext ξ k
  simp [Matrix.toEuclideanCLM_toLp, hSdef]


omit [Fintype κ] [DecidableEq κ] in
/-- Every exponential of the norm of a Gaussian vector is integrable (a consequence of Fernique's
theorem). -/
theorem HasGaussianLaw.integrable_exp_mul_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] [MeasurableSpace E]
    [BorelSpace E] {X : Ω → E} (hX : HasGaussianLaw X P) (r : ℝ) :
    Integrable (fun ω => Real.exp (r * ‖X ω‖)) P := by
  have := hX.isGaussian_map
  obtain ⟨C, hC, hint⟩ := IsGaussian.exists_integrable_exp_sq (P.map X)
  have hm : Continuous fun x : E => Real.exp (r * ‖x‖) := by fun_prop
  have h : Integrable (fun x : E => Real.exp (r * ‖x‖)) (P.map X) := by
    refine (hint.const_mul (Real.exp (r ^ 2 / (4 * C)))).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add, Real.exp_le_exp]
    have key : r ^ 2 / (4 * C) + C * ‖x‖ ^ 2 - r * ‖x‖ =
        (2 * C * ‖x‖ - r) ^ 2 / (4 * C) := by
      field_simp
      ring
    have : 0 ≤ (2 * C * ‖x‖ - r) ^ 2 / (4 * C) := by positivity
    linarith
  exact (integrable_map_measure hm.aestronglyMeasurable hX.aemeasurable).1 h

omit [Fintype κ] [DecidableEq κ] in
/-- **Gaussian integration by parts for vectors.** Let `(W, X)` be a centered Gaussian vector,
`X` with values in a finite-dimensional normed space `E`, and let `F : E → V` be differentiable
with `F` and its derivative growing at most exponentially. Then
`𝔼[W • F(X)] = 𝔼[DF(X) (𝔼[W • X])]`. -/
theorem integral_smul_comp_eq_integral_fderiv_apply {E V : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {W : Ω → ℝ} {X : Ω → E}
    (hWX : HasGaussianLaw (fun ω => (W ω, X ω)) P) (hW : ∫ ω, W ω ∂P = 0)
    (hX : ∫ ω, X ω ∂P = 0) {F : E → V} (hF : Differentiable ℝ F) {C c D d : ℝ}
    (hFg : ∀ x, ‖F x‖ ≤ C * Real.exp (c * ‖x‖))
    (hFg' : ∀ x, ‖fderiv ℝ F x‖ ≤ D * Real.exp (d * ‖x‖)) :
    ∫ ω, W ω • F (X ω) ∂P = ∫ ω, fderiv ℝ F (X ω) (∫ ω', W ω' • X ω' ∂P) ∂P := by
  classical
  have hP := hWX.isProbabilityMeasure
  -- coordinates of `(W, X)` in a basis, and their representation by i.i.d. Gaussians
  set n := Module.finrank ℝ E
  set b := Module.finBasis ℝ E with hb
  set T : ℝ × E →L[ℝ] (Unit ⊕ Fin n → ℝ) := ContinuousLinearMap.pi
    (Sum.elim (fun _ => ContinuousLinearMap.fst ℝ ℝ E) fun l =>
      (LinearMap.toContinuousLinearMap (b.coord l)).comp (ContinuousLinearMap.snd ℝ ℝ E)) with hT
  set S : (Unit ⊕ Fin n → ℝ) →L[ℝ] ℝ × E :=
    (ContinuousLinearMap.proj (Sum.inl ())).prod
      (∑ l, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Unit ⊕ Fin n => ℝ)
        (Sum.inr l)).smulRight (b l)) with hS
  have hST : ∀ p, S (T p) = p := fun p => by
    refine Prod.ext (by simp [hS, hT]) ?_
    simp [hS, hT, sum_apply]
  have hY : HasGaussianLaw (fun ω s => T (W ω, X ω) s) P := hWX.map_fun T
  have hXint : Integrable X P := hWX.snd.integrable
  have hYmean : ∀ s, ∫ ω, T (W ω, X ω) s ∂P = 0 := by
    rintro (_ | l)
    · simpa [hT] using hW
    · have h := (LinearMap.toContinuousLinearMap (b.coord l)).integral_comp_comm hXint
      rw [hX, map_zero] at h
      simpa [hT] using h
  obtain ⟨A, hlaw, -⟩ := exists_matrix_map_eq_pi_gaussianReal
    (X := fun s ω => T (W ω, X ω) s) hY hYmean
  set π : Measure (Unit ⊕ Fin n → ℝ) := Measure.pi fun _ => gaussianReal 0 1 with hπ
  set M : (Unit ⊕ Fin n → ℝ) →L[ℝ] ℝ × E :=
    S.comp (LinearMap.toContinuousLinearMap A.mulVecLin) with hM
  have hlawM : P.map (fun ω => (W ω, X ω)) = π.map M := by
    have h := congrArg (Measure.map S) hlaw
    rw [AEMeasurable.map_map_of_aemeasurable S.continuous.aemeasurable hY.aemeasurable,
      Measure.map_map S.continuous.measurable (by fun_prop)] at h
    change P.map (fun ω => (W ω, X ω)) = π.map (fun x => S (A *ᵥ x))
    simpa only [Function.comp_def, hST] using h
  have htr : ∀ g : ℝ × E → V, StronglyMeasurable g →
      ∫ ω, g (W ω, X ω) ∂P = ∫ ξ, g (M ξ) ∂π := fun g hg => by
    rw [← integral_map hWX.aemeasurable hg.aestronglyMeasurable, hlawM,
      integral_map M.continuous.aemeasurable hg.aestronglyMeasurable]
  -- the representation `W = a ⬝ᵥ ξ`, `X = L ξ`
  set L : (Unit ⊕ Fin n → ℝ) →L[ℝ] E := (ContinuousLinearMap.snd ℝ ℝ E).comp M with hL
  set a : Unit ⊕ Fin n → ℝ := fun j => (M (Pi.single j 1)).1 with ha
  have hMa : ∀ ξ, (M ξ).1 = a ⬝ᵥ ξ := fun ξ => by
    have : ξ = ∑ j, ξ j • (Pi.single j (1 : ℝ) : Unit ⊕ Fin n → ℝ) := by
      ext m; simp [Pi.single_apply]
    conv_lhs => rw [this]
    simp only [map_sum, map_smul, Prod.fst_sum, Prod.smul_fst, smul_eq_mul, dotProduct, ha,
      mul_comm]
  have hnorm : ∀ ξ : Unit ⊕ Fin n → ℝ, ‖ξ‖ ≤ ∑ k, |ξ k| := fun ξ =>
    (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).2 fun k =>
      Finset.single_le_sum (f := fun k => |ξ k|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
  -- integrability against the Gaussians of anything of exponential growth along `L`
  have hint : ∀ (G : (Unit ⊕ Fin n → ℝ) → V), AEStronglyMeasurable G π → ∀ K r : ℝ,
      (∀ ξ, ‖G ξ‖ ≤ K * Real.exp (r * ∑ k, |ξ k|)) → Integrable G π := fun G hG K r h => by
    refine ((integrable_exp_sum_mul_abs_pi_stdGaussian fun _ => r).const_mul K).mono' hG
      (ae_of_all _ fun ξ => (h ξ).trans_eq ?_)
    rw [Finset.mul_sum]
  have hexp : ∀ (K r : ℝ) (ξ : Unit ⊕ Fin n → ℝ),
      K * Real.exp (r * ‖L ξ‖) ≤ |K| * Real.exp (|r| * ‖L‖ * ∑ k, |ξ k|) := fun K r ξ => by
    refine mul_le_mul (le_abs_self K) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (abs_nonneg K)
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_right (le_abs_self r) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left ((L.le_opNorm ξ).trans
        (mul_le_mul_of_nonneg_left (hnorm ξ) (norm_nonneg L))) (abs_nonneg r))
  have hdm : ∀ w : E, StronglyMeasurable fun x => fderiv ℝ F x w := fun w =>
    stronglyMeasurable_fderiv_apply_of_differentiable hF w
  have hcomp : ∀ ξ w, fderiv ℝ (F ∘ L) ξ w = fderiv ℝ F (L ξ) (L w) := fun ξ w => by
    rw [((hF (L ξ)).hasFDerivAt.comp ξ L.hasFDerivAt).fderiv]
    rfl
  have h1 : ∀ j : Unit ⊕ Fin n, Integrable (fun ξ => ξ j • F (L ξ)) π := fun j => by
    refine hint _ ((continuous_apply j).smul (hF.continuous.comp
      L.continuous)).aestronglyMeasurable |C| (1 + |c| * ‖L‖) fun ξ => ?_
    have hj : |ξ j| ≤ Real.exp (∑ k, |ξ k|) :=
      (Finset.single_le_sum (f := fun k => |ξ k|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)).trans (by linarith [Real.add_one_le_exp (∑ k, |ξ k|)])
    rw [norm_smul, Real.norm_eq_abs]
    refine (mul_le_mul hj ((hFg _).trans (hexp C c ξ)) (norm_nonneg _)
      (Real.exp_pos _).le).trans_eq ?_
    rw [add_mul, one_mul, Real.exp_add]
    ring
  have h2 : ∀ w : E, Integrable (fun ξ => fderiv ℝ F (L ξ) w) π := fun w => by
    refine hint _ ((hdm w).comp_measurable L.continuous.measurable).aestronglyMeasurable
      (|D| * ‖w‖) (|d| * ‖L‖) fun ξ => ?_
    refine ((fderiv ℝ F (L ξ)).le_opNorm w).trans ?_
    refine (mul_le_mul_of_nonneg_right ((hFg' _).trans (hexp D d ξ)) (norm_nonneg w)).trans_eq ?_
    ring
  -- Stein's identity along the direction `a`
  have hstein := integral_dotProduct_smul_pi_gaussianReal_eq (fun _ => (1 : ℝ≥0)) a
    (G := F ∘ L) (hF.comp L.differentiable) h1
    (fun j => by simpa only [hcomp] using h2 (L (Pi.single j 1)))
  simp only [NNReal.coe_one, one_mul, hcomp, Function.comp_apply] at hstein
  have hcov : ∫ ω, W ω • X ω ∂P = L a := by
    have htr' : ∫ ω, W ω • X ω ∂P = ∫ ξ, (M ξ).1 • (M ξ).2 ∂π := by
      have hg : Continuous fun p : ℝ × E => p.1 • p.2 := by fun_prop
      rw [← integral_map (f := fun p : ℝ × E => p.1 • p.2) hWX.aemeasurable
        hg.aestronglyMeasurable, hlawM,
        integral_map M.continuous.aemeasurable hg.aestronglyMeasurable]
    have h1L : ∀ j : Unit ⊕ Fin n, Integrable (fun ξ => ξ j • L ξ) π := fun j => by
      refine ((integrable_exp_sum_mul_abs_pi_stdGaussian fun _ => (2 : ℝ)).const_mul ‖L‖).mono'
        ((continuous_apply j).smul L.continuous).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
      have h0 : (0 : ℝ) ≤ ∑ k, |ξ k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hle : ∑ k, |ξ k| ≤ Real.exp (∑ k, |ξ k|) := by
        linarith [Real.add_one_le_exp (∑ k, |ξ k|)]
      have hj : |ξ j| ≤ Real.exp (∑ k, |ξ k|) :=
        (Finset.single_le_sum (f := fun k => |ξ k|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ j)).trans hle
      rw [norm_smul, Real.norm_eq_abs, ← Finset.mul_sum, two_mul, Real.exp_add]
      refine (mul_le_mul hj ((L.le_opNorm ξ).trans
        (mul_le_mul_of_nonneg_left ((hnorm ξ).trans hle) (norm_nonneg L))) (norm_nonneg _)
        (Real.exp_pos _).le).trans_eq ?_
      ring
    have h := integral_dotProduct_smul_pi_gaussianReal_eq (fun _ => (1 : ℝ≥0)) a
      (G := L) L.differentiable h1L (fun j => by
        simp only [ContinuousLinearMap.fderiv]; exact integrable_const _)
    simp only [NNReal.coe_one, one_mul, ContinuousLinearMap.fderiv] at h
    rw [htr']
    simp only [hMa]
    refine h.trans ?_
    rw [integral_const, probReal_univ, one_smul]
  have hg1 : StronglyMeasurable fun p : ℝ × E => p.1 • F p.2 :=
    (continuous_fst.smul (hF.continuous.comp continuous_snd)).stronglyMeasurable
  have hg2 : StronglyMeasurable fun p : ℝ × E => fderiv ℝ F p.2 (L a) :=
    (hdm (L a)).comp_measurable measurable_snd
  rw [hcov, htr _ hg1, htr _ hg2]
  simp only [hMa]
  exact hstein

omit [DecidableEq κ] in
/-- **Integrability of exponentially bounded functions of a Gaussian vector:** if `X` is a centered
Gaussian vector and `F` is measurable with `|F y| ≤ C exp (c ‖y‖₁)`, then `F(X)` is integrable. -/
theorem integrable_comp_of_exp_growth {X : κ → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω k => X k ω) P) (hmean : ∀ k, ∫ ω, X k ω ∂P = 0)
    {F : (κ → ℝ) → ℝ} (hFm : Measurable F) {C c : ℝ}
    (hF : ∀ y, |F y| ≤ C * Real.exp (c * ∑ l, |y l|)) :
    Integrable (fun ω => F fun k => X k ω) P := by
  obtain ⟨A, hlaw, -⟩ := exists_matrix_map_eq_pi_gaussianReal hX hmean
  have hAm : Measurable fun ξ : κ → ℝ => A *ᵥ ξ := by fun_prop
  have h2 : Integrable F (P.map fun ω k => X k ω) := by
    rw [hlaw, integrable_map_measure hFm.aestronglyMeasurable hAm.aemeasurable]
    exact integrable_comp_mulVec_of_exp_l1_growth A hFm hF
  exact (integrable_map_measure hFm.aestronglyMeasurable hX.aemeasurable).1 h2

omit [DecidableEq κ] in
/-- **Differentiation under the integral against a Gaussian vector**, locally in the parameter.
Let `X` be a centered Gaussian vector and `G s`, for `s` in a neighbourhood `U` of `s₀`, a family
of measurable functions, differentiable in `s` with `|∂ₛ G s y| ≤ C exp (c ‖y‖₁)`, and
`|G s₀ y| ≤ C₀ exp (c₀ ‖y‖₁)`.  Then `(d/ds) 𝔼 G s (X) = 𝔼 ∂ₛ G s (X)`. -/
theorem hasDerivAt_integral_comp_of_exp_growth_of_mem_nhds {X : κ → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω k => X k ω) P) (hmean : ∀ k, ∫ ω, X k ω ∂P = 0)
    {G G' : ℝ → (κ → ℝ) → ℝ} {s₀ : ℝ} {U : Set ℝ} (hU : U ∈ nhds s₀)
    (hGm : ∀ s ∈ U, Measurable (G s)) (hG'm : Measurable (G' s₀))
    (hG : ∀ s ∈ U, ∀ y, HasDerivAt (fun s => G s y) (G' s y) s) {C c : ℝ}
    (hG' : ∀ s ∈ U, ∀ y, |G' s y| ≤ C * Real.exp (c * ∑ l, |y l|)) {C₀ c₀ : ℝ}
    (hG₀ : ∀ y, |G s₀ y| ≤ C₀ * Real.exp (c₀ * ∑ l, |y l|)) :
    HasDerivAt (fun s => ∫ ω, G s (fun k => X k ω) ∂P)
      (∫ ω, G' s₀ (fun k => X k ω) ∂P) s₀ := by
  have hXm := hX.aemeasurable
  have hbd : Integrable (fun ω => |C| * Real.exp (|c| * ∑ l, |X l ω|)) P :=
    integrable_comp_of_exp_growth hX hmean (F := fun y => |C| * Real.exp (|c| * ∑ l, |y l|))
      (by fun_prop) (C := |C|) (c := |c|) fun y => le_of_eq (abs_of_nonneg (by positivity))
  have hle : ∀ y : κ → ℝ, C * Real.exp (c * ∑ l, |y l|) ≤ |C| * Real.exp (|c| * ∑ l, |y l|) :=
    fun y => mul_le_mul (le_abs_self C) (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
      (le_abs_self c) (Finset.sum_nonneg fun _ _ => abs_nonneg _))) (Real.exp_pos _).le
      (abs_nonneg C)
  have hint0 : Integrable (fun ω => G s₀ fun k => X k ω) P :=
    integrable_comp_of_exp_growth hX hmean (hGm s₀ (mem_of_mem_nhds hU)) hG₀
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P)
    (F := fun s ω => G s fun k => X k ω) (F' := fun s ω => G' s fun k => X k ω)
    (bound := fun ω => |C| * Real.exp (|c| * ∑ l, |X l ω|)) (s := U) hU
    (Filter.eventually_of_mem hU fun s hs =>
      ((hGm s hs).comp_aemeasurable hXm).aestronglyMeasurable)
    hint0 ((hG'm.comp_aemeasurable hXm).aestronglyMeasurable)
    (ae_of_all _ fun ω s hs => by
      rw [Real.norm_eq_abs]
      exact (hG' s hs _).trans (hle _))
    hbd (ae_of_all _ fun ω s hs => hG s hs _)).2

omit [DecidableEq κ] in
/-- **Differentiation under the integral against a Gaussian vector**, with hypotheses for all
values of the parameter.  Let `X` be a centered Gaussian vector and `G s` a family of measurable
functions, differentiable in `s` with `|∂ₛ G s y| ≤ C exp (c ‖y‖₁)` uniformly in `s`, and
`|G s₀ y| ≤ C₀ exp (c₀ ‖y‖₁)`.  Then `(d/ds) 𝔼 G s (X) = 𝔼 ∂ₛ G s (X)`. -/
theorem hasDerivAt_integral_comp_of_exp_growth {X : κ → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω k => X k ω) P) (hmean : ∀ k, ∫ ω, X k ω ∂P = 0)
    {G G' : ℝ → (κ → ℝ) → ℝ} (s₀ : ℝ) (hGm : ∀ s, Measurable (G s))
    (hG'm : Measurable (G' s₀)) (hG : ∀ s y, HasDerivAt (fun s => G s y) (G' s y) s) {C c : ℝ}
    (hG' : ∀ s y, |G' s y| ≤ C * Real.exp (c * ∑ l, |y l|)) {C₀ c₀ : ℝ}
    (hG₀ : ∀ y, |G s₀ y| ≤ C₀ * Real.exp (c₀ * ∑ l, |y l|)) :
    HasDerivAt (fun s => ∫ ω, G s (fun k => X k ω) ∂P)
      (∫ ω, G' s₀ (fun k => X k ω) ∂P) s₀ :=
  hasDerivAt_integral_comp_of_exp_growth_of_mem_nhds hX hmean Filter.univ_mem
    (fun s _ => hGm s) hG'm (fun s _ => hG s) (fun s _ => hG' s) hG₀

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

omit [Fintype κ₁] [DecidableEq κ₂] in
/-- The coordinates of `∫ w • V` for a square integrable weight `w` and a square integrable
vector `V = (V k)ₖ`. -/
theorem integral_smul_pi_apply_eq_integral_mul {w : Ω → ℝ} {V : κ₂ → Ω → ℝ} (hw : MemLp w 2 P)
    (hV : MemLp (fun ω k => V k ω) 2 P) (k : κ₂) :
    (∫ ω, w ω • (fun k => V k ω) ∂P) k = ∫ ω, w ω * V k ω ∂P := by
  have hint : Integrable (fun ω => w ω • fun k => V k ω) P :=
    memLp_one_iff_integrable.1 (hw.smul hV)
  rw [eval_integral fun l => Integrable.eval hint l]
  rfl

omit [Fintype κ₁] in
/-- A linear map on `κ → ℝ` evaluated through the coordinate directions. -/
theorem apply_eq_sum_smul_apply_pi_single {V : Type*} [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] (L : (κ₂ → ℝ) →L[ℝ] V) (w : κ₂ → ℝ) :
    L w = ∑ l, w l • L (Pi.single l 1) := by
  have : w = ∑ l, w l • (Pi.single l (1 : ℝ) : κ₂ → ℝ) := by
    ext m; simp [Pi.single_apply]
  conv_lhs => rw [this]
  simp only [map_sum, map_smul]

omit [Fintype κ₁] [DecidableEq κ₂] in
/-- Exponential growth in `‖y‖₁` implies exponential growth in the supremum norm. -/
theorem mul_exp_mul_sum_abs_le_mul_exp_norm (K r : ℝ) (y : κ₂ → ℝ) :
    K * Real.exp (r * ∑ l, |y l|) ≤ |K| * Real.exp (|r| * Fintype.card κ₂ * ‖y‖) := by
  have h1 : ∑ l, |y l| ≤ Fintype.card κ₂ * ‖y‖ := by
    have h := Finset.sum_le_card_nsmul Finset.univ (fun l => |y l|) ‖y‖
      fun l _ => norm_le_pi_norm y l
    rwa [Finset.card_univ, nsmul_eq_mul] at h
  refine mul_le_mul (le_abs_self K) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (abs_nonneg K)
  rw [mul_assoc]
  exact (mul_le_mul_of_nonneg_right (le_abs_self r)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left h1 (abs_nonneg r))

omit [Fintype κ₁] in
/-- Exponential bounds on the partial derivatives bound the derivative in operator norm. -/
theorem norm_fderiv_le_of_abs_fderiv_pi_single_le {F : (κ₂ → ℝ) → ℝ} {D d : κ₂ → ℝ}
    (hF : ∀ l y, |fderiv ℝ F y (Pi.single l 1)| ≤ D l * Real.exp (d l * ∑ l, |y l|))
    (y : κ₂ → ℝ) : ‖fderiv ℝ F y‖ ≤
      (∑ l, |D l|) * Real.exp ((∑ l, |d l|) * Fintype.card κ₂ * ‖y‖) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [apply_eq_sum_smul_apply_pi_single (fderiv ℝ F y) w, Real.norm_eq_abs, Finset.sum_mul,
    Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [smul_eq_mul, abs_mul, mul_comm]
  refine mul_le_mul ((hF l y).trans ((mul_exp_mul_sum_abs_le_mul_exp_norm (D l) (d l) y).trans ?_))
    (norm_le_pi_norm w l) (abs_nonneg _) (by positivity)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := fun l => |d l|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ l)) (Nat.cast_nonneg _))
    (norm_nonneg _))) (abs_nonneg _)

omit [Fintype κ₁] in
/-- **Gaussian integration by parts against a jointly Gaussian test variable.**
If the family `W ⊕ X` is jointly Gaussian, `X` and `W i` are centered, and `F` is differentiable
with exponentially bounded value and partial derivatives, then
`𝔼[W i F(X)] = ∑ l, 𝔼[W i X l] 𝔼[∂ₗ F(X)]`. This is the coordinate form of
`integral_smul_comp_eq_integral_fderiv_apply`; in applications `W` is the part of the Gaussian
field that does not enter `F`. -/
theorem integral_mul_comp_eq_sum_integral_mul_of_sum [Finite κ₁] {W : κ₁ → Ω → ℝ} {X : κ₂ → Ω → ℝ}
    (hWX : HasGaussianLaw (fun ω s => Sum.elim W X s ω) P) {i : κ₁}
    (hW : ∫ ω, W i ω ∂P = 0) (hX : ∀ l, ∫ ω, X l ω ∂P = 0)
    {F : (κ₂ → ℝ) → ℝ} (hF : Differentiable ℝ F) {C c : ℝ}
    (hFg : ∀ y, |F y| ≤ C * Real.exp (c * ∑ l, |y l|)) {D d : κ₂ → ℝ}
    (hFg' : ∀ l y, |fderiv ℝ F y (Pi.single l 1)| ≤ D l * Real.exp (d l * ∑ l, |y l|)) :
    ∫ ω, W i ω * F (fun l => X l ω) ∂P =
      ∑ l, (∫ ω, W i ω * X l ω ∂P) * ∫ ω, fderiv ℝ F (fun k => X k ω) (Pi.single l 1) ∂P := by
  have := Fintype.ofFinite κ₁
  have hP := hWX.isProbabilityMeasure
  set R : (κ₁ ⊕ κ₂ → ℝ) →L[ℝ] ℝ × (κ₂ → ℝ) :=
    (ContinuousLinearMap.proj (Sum.inl i)).prod
      (ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (Sum.inr l)) with hR
  have hpair : HasGaussianLaw (fun ω => (W i ω, fun l => X l ω)) P := hWX.map_fun R
  have hXG : HasGaussianLaw (fun ω l => X l ω) P := hpair.snd
  have hXmean : ∫ ω, (fun l => X l ω) ∂P = 0 := by
    funext l
    rw [eval_integral fun l => (hXG.eval l).integrable]
    exact hX l
  have hsum : ∀ (w y : κ₂ → ℝ),
      fderiv ℝ F y w = ∑ l, w l * fderiv ℝ F y (Pi.single l 1) := fun w y =>
    apply_eq_sum_smul_apply_pi_single (fderiv ℝ F y) w
  have h := integral_smul_comp_eq_integral_fderiv_apply hpair hW hXmean hF
    (C := |C|) (c := |c| * Fintype.card κ₂)
    (fun y => (hFg y).trans (mul_exp_mul_sum_abs_le_mul_exp_norm C c y))
    (norm_fderiv_le_of_abs_fderiv_pi_single_le hFg')
  have hcov : ∀ l, (∫ ω, W i ω • (fun l => X l ω) ∂P) l = ∫ ω, W i ω * X l ω ∂P :=
    integral_smul_pi_apply_eq_integral_mul hpair.fst.memLp_two hXG.memLp_two
  have hd : ∀ l, Integrable (fun ω => fderiv ℝ F (fun k => X k ω) (Pi.single l 1)) P :=
    fun l => integrable_comp_of_exp_growth hXG hX (measurable_fderiv_apply_const ℝ F _) (hFg' l)
  simp only [smul_eq_mul] at h
  simp only [h, hsum (∫ ω, W i ω • (fun l => X l ω) ∂P), hcov]
  rw [integral_finsetSum _ fun l _ => (hd l).const_mul _]
  simp only [integral_const_mul]

omit [Fintype κ₁] [DecidableEq κ₂] in
/-- **Integrability of `exp (A X)`** for a centered Gaussian family `W ⊕ X` and a measurable `A`
with `|A y| ≤ c₁ + c₂ ‖y‖₁`. -/
theorem integrable_exp_comp_of_sum [Finite κ₁] {W : κ₁ → Ω → ℝ} {X : κ₂ → Ω → ℝ}
    (hWX : HasGaussianLaw (fun ω s => Sum.elim W X s ω) P) (hX : ∀ l, ∫ ω, X l ω ∂P = 0)
    {A : (κ₂ → ℝ) → ℝ} (hAm : Measurable A) {c₁ c₂ : ℝ}
    (hAg : ∀ y, |A y| ≤ c₁ + c₂ * ∑ l, |y l|) :
    Integrable (fun ω => Real.exp (A fun l => X l ω)) P := by
  have := Fintype.ofFinite κ₁
  have hXG : HasGaussianLaw (fun ω l => X l ω) P :=
    hWX.map_fun (ContinuousLinearMap.pi fun l : κ₂ =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ₁ ⊕ κ₂ => ℝ) (Sum.inr l))
  refine integrable_comp_of_exp_growth hXG hX (F := fun y => Real.exp (A y)) hAm.exp
    (C := Real.exp c₁) (c := c₂) fun y => ?_
  rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  exact Real.exp_le_exp.2 ((le_abs_self _).trans (hAg y))

omit [Fintype κ₁] [DecidableEq κ₂] in
/-- **Integrability of `W i · exp (A X)`** for a Gaussian family `W ⊕ X` with `X` and `W i`
centered and a measurable `A` with `|A y| ≤ c₁ + c₂ ‖y‖₁`; this makes the integrals in
`integral_mul_exp_comp_eq_sum_integral_mul_of_sum` meaningful. -/
theorem integrable_mul_exp_comp_of_sum [Finite κ₁] {W : κ₁ → Ω → ℝ} {X : κ₂ → Ω → ℝ}
    (hWX : HasGaussianLaw (fun ω s => Sum.elim W X s ω) P) {i : κ₁}
    (hW : ∫ ω, W i ω ∂P = 0) (hX : ∀ l, ∫ ω, X l ω ∂P = 0)
    {A : (κ₂ → ℝ) → ℝ} (hAm : Measurable A) {c₁ c₂ : ℝ}
    (hAg : ∀ y, |A y| ≤ c₁ + c₂ * ∑ l, |y l|) :
    Integrable (fun ω => W i ω * Real.exp (A fun l => X l ω)) P := by
  have := Fintype.ofFinite κ₁
  have hZ : HasGaussianLaw (fun ω s => Sum.elim (fun _ : Unit => W i) X s ω) P := by
    have h := hWX.map_fun (ContinuousLinearMap.pi fun s : Unit ⊕ κ₂ =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ₁ ⊕ κ₂ => ℝ)
        (Sum.map (fun _ => i) id s))
    convert h using 1
    funext ω s
    rcases s with _ | l <;> rfl
  have hmean : ∀ s, ∫ ω, Sum.elim (fun _ : Unit => W i) X s ω ∂P = 0 := by
    rintro (_ | l)
    exacts [hW, hX l]
  have hexp : ∀ y, |Real.exp (A y)| ≤ Real.exp c₁ * Real.exp (c₂ * ∑ l, |y l|) := fun y => by
    rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (hAg y))
  refine integrable_comp_of_exp_growth (X := Sum.elim (fun _ : Unit => W i) X) hZ hmean
    (F := fun y => y (Sum.inl ()) * Real.exp (A fun l => y (Sum.inr l)))
    (by fun_prop) (C := Real.exp c₁) (c := |c₂| + 1) fun y => ?_
  have h1 := abs_comp_inr_le_of_exp_growth (G := fun y' => Real.exp (A y')) hexp y
  have h2 : |y (Sum.inl ())| ≤ ∑ s, |y s| :=
    Finset.single_le_sum (f := fun s => |y s|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  rw [abs_mul]
  calc |y (Sum.inl ())| * |Real.exp (A fun l => y (Sum.inr l))|
      ≤ Real.exp (∑ s, |y s|) * (Real.exp c₁ * Real.exp (|c₂| * ∑ s, |y s|)) :=
        mul_le_mul ((h2.trans (by linarith [Real.add_one_le_exp (∑ s, |y s|)]))) h1
          (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp c₁ * Real.exp ((|c₂| + 1) * ∑ s, |y s|) := by
        rw [add_mul, one_mul, Real.exp_add]; ring

omit [Fintype κ₁] in
/-- **Gaussian integration by parts for the exponential of a smooth functional.**  For a Gaussian
family `W ⊕ X` with `X` and `W i` centered and a differentiable `A` with `|A y| ≤ c₁ + c₂ ‖y‖₁`
and bounded partial derivatives `|∂ₗ A| ≤ c₃`,
`𝔼[W i exp (A X)] = ∑ l, 𝔼[W i X l] 𝔼[exp (A X) ∂ₗ A(X)]`.
This is `integral_mul_comp_eq_sum_integral_mul_of_sum` for `F = exp ∘ A`; it covers the Gibbs
weights and partition functions of the spin-glass models, where `A` is a combination of
`log ∑ exp`. -/
theorem integral_mul_exp_comp_eq_sum_integral_mul_of_sum [Finite κ₁] {W : κ₁ → Ω → ℝ}
    {X : κ₂ → Ω → ℝ} (hWX : HasGaussianLaw (fun ω s => Sum.elim W X s ω) P) {i : κ₁}
    (hW : ∫ ω, W i ω ∂P = 0) (hX : ∀ l, ∫ ω, X l ω ∂P = 0)
    {A : (κ₂ → ℝ) → ℝ} (hA : Differentiable ℝ A) {c₁ c₂ c₃ : ℝ}
    (hAg : ∀ y, |A y| ≤ c₁ + c₂ * ∑ l, |y l|)
    (hAg' : ∀ l y, |fderiv ℝ A y (Pi.single l 1)| ≤ c₃) :
    ∫ ω, W i ω * Real.exp (A fun l => X l ω) ∂P =
      ∑ l, (∫ ω, W i ω * X l ω ∂P) *
        ∫ ω, Real.exp (A fun k => X k ω) * fderiv ℝ A (fun k => X k ω) (Pi.single l 1) ∂P := by
  have hE : Differentiable ℝ fun y => Real.exp (A y) := Real.differentiable_exp.comp hA
  have hd : ∀ l y, fderiv ℝ (fun y => Real.exp (A y)) y (Pi.single l 1) =
      Real.exp (A y) * fderiv ℝ A y (Pi.single l 1) := by
    intro l y
    rw [fderiv_exp (hA y)]
    simp
  have hexp : ∀ y, Real.exp (A y) ≤ Real.exp c₁ * Real.exp (c₂ * ∑ l, |y l|) := fun y => by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (hAg y))
  have h := integral_mul_comp_eq_sum_integral_mul_of_sum hWX hW hX hE (C := Real.exp c₁)
    (c := c₂) (fun y => by rw [abs_of_pos (Real.exp_pos _)]; exact hexp y)
    (D := fun _ => c₃ * Real.exp c₁) (d := fun _ => c₂) (fun l y => by
      rw [hd, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (A y) * |fderiv ℝ A y (Pi.single l 1)|
          ≤ (Real.exp c₁ * Real.exp (c₂ * ∑ l, |y l|)) * c₃ :=
            mul_le_mul (hexp y) (hAg' l y) (abs_nonneg _) (by positivity)
        _ = c₃ * Real.exp c₁ * Real.exp (c₂ * ∑ l, |y l|) := by ring)
  simpa only [hd] using h

end Aux

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
  have hXX : HasGaussianLaw (fun ω s => Sum.elim X X s ω) P := by
    have h := hX.map_fun (ContinuousLinearMap.pi fun s : κ ⊕ κ =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) (Sum.elim id id s))
    convert h using 1
    funext ω s
    rcases s with k | k <;> rfl
  exact integral_mul_comp_eq_sum_integral_mul_of_sum hXX (hmean i) hmean hF hFg hFg'

/-- A Gaussian process indexed by a finite type is a Gaussian vector: this passes from Mathlib's
`IsGaussianProcess` (finite-dimensional marginals) to the `HasGaussianLaw` hypothesis of
`integral_mul_comp_eq_sum_integral_mul`. -/
theorem IsGaussianProcess.hasGaussianLaw_pi {S : Type*} [Finite S] {X : S → Ω → ℝ}
    (hX : IsGaussianProcess X P) : HasGaussianLaw (fun ω s => X s ω) P := by
  have := Fintype.ofFinite S
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
    (i := ()) hW hY (F := fun y => ∏ i, y i) (by fun_prop) (C := 1) (c := 1)
    (fun y => by simpa using abs_prod_le_exp_sum Finset.univ y) (D := fun _ => 1) (d := fun _ => 1)
    (fun l y => by
      rw [fderiv_prod_apply_pi_single]
      simpa using abs_prod_le_exp_sum _ y)
  simpa [fderiv_prod_apply_pi_single] using h

end Monomial

/-- **Gaussian laws on a product space with independent coordinates.**  If `f` and `g` have
Gaussian laws under `μ` and `ν`, then `z ↦ (f z.1, g z.2)` has a Gaussian law under `μ.prod ν`
(the product of two Gaussian measures is Gaussian). -/
theorem HasGaussianLaw.prodMk_prod {Ω₁ Ω₂ E F : Type*} {m₁ : MeasurableSpace Ω₁}
    {m₂ : MeasurableSpace Ω₂} {μ : Measure Ω₁} {ν : Measure Ω₂}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopologyEither E F] {f : Ω₁ → E} {g : Ω₂ → F}
    (hf : HasGaussianLaw f μ) (hg : HasGaussianLaw g ν) :
    HasGaussianLaw (fun z : Ω₁ × Ω₂ => (f z.1, g z.2)) (μ.prod ν) := by
  have := hf.isProbabilityMeasure
  have := hg.isProbabilityMeasure
  have hfm : AEMeasurable (fun z : Ω₁ × Ω₂ => f z.1) (μ.prod ν) :=
    hf.aemeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hgm : AEMeasurable (fun z : Ω₁ × Ω₂ => g z.2) (μ.prod ν) :=
    hg.aemeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have h : (μ.prod ν).map (fun z : Ω₁ × Ω₂ => (f z.1, g z.2)) = (μ.map f).prod (ν.map g) := by
    have hae : (fun z : Ω₁ × Ω₂ => (f z.1, g z.2)) =ᵐ[μ.prod ν]
        Prod.map (hf.aemeasurable.mk f) (hg.aemeasurable.mk g) :=
      (Measure.quasiMeasurePreserving_fst.ae_eq_comp hf.aemeasurable.ae_eq_mk).prodMk
        (Measure.quasiMeasurePreserving_snd.ae_eq_comp hg.aemeasurable.ae_eq_mk)
    rw [Measure.map_congr hae, Measure.map_congr hf.aemeasurable.ae_eq_mk,
      Measure.map_congr hg.aemeasurable.ae_eq_mk]
    exact (Measure.map_prod_map μ ν hf.aemeasurable.measurable_mk
      hg.aemeasurable.measurable_mk).symm
  refine ⟨hfm.prodMk hgm, ?_⟩
  have := hf.isGaussian_map
  have := hg.isGaussian_map
  rw [h]
  infer_instance

/-- **Two independent copies of a Gaussian vector are jointly Gaussian:** if `g` is a Gaussian
vector `(g a)ₐ` under `P`, then `z ↦ (g a z.1, g a z.2)` is a Gaussian vector indexed by `κ ⊕ κ`
under `P ⊗ P`. -/
theorem HasGaussianLaw.sumElim_prod {Ω' κ' : Type*} {m : MeasurableSpace Ω'} {P' : Measure Ω'}
    [Finite κ'] {g : κ' → Ω' → ℝ} (hg : HasGaussianLaw (fun ω a => g a ω) P') :
    HasGaussianLaw (fun (z : Ω' × Ω') (s : κ' ⊕ κ') =>
      Sum.elim (fun a (z : Ω' × Ω') => g a z.1) (fun a (z : Ω' × Ω') => g a z.2) s z)
      (P'.prod P') := by
  have := Fintype.ofFinite κ'
  have hpair := HasGaussianLaw.prodMk_prod hg hg
  let L : ((κ' → ℝ) × (κ' → ℝ)) →L[ℝ] (κ' ⊕ κ' → ℝ) := ContinuousLinearMap.pi
    (Sum.elim (fun a => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ' => ℝ) a).comp
        (ContinuousLinearMap.fst ℝ (κ' → ℝ) (κ' → ℝ)))
      (fun a => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ' => ℝ) a).comp
        (ContinuousLinearMap.snd ℝ (κ' → ℝ) (κ' → ℝ))))
  convert hpair.map_fun L using 1
  ext z (a | a) <;> simp [L]

/-- **Independent Gaussian vectors from different source spaces are jointly Gaussian.**  This is
the two-measure version of `HasGaussianLaw.sumElim_prod`, with two different (finite) index types
`κ₁`, `κ₂`; it is useful when Gaussian fields have different index types, such as pair disorder
and a site cavity field. -/
theorem HasGaussianLaw.sumElim_prod_of_independent {Ω₁ Ω₂ κ₁ κ₂ : Type*}
    {m₁ : MeasurableSpace Ω₁} {m₂ : MeasurableSpace Ω₂} {μ : Measure Ω₁} {ν : Measure Ω₂}
    [Finite κ₁] [Finite κ₂] {f : Ω₁ → κ₁ → ℝ} {g : Ω₂ → κ₂ → ℝ}
    (hf : HasGaussianLaw f μ) (hg : HasGaussianLaw g ν) :
    HasGaussianLaw (fun z : Ω₁ × Ω₂ => fun s : κ₁ ⊕ κ₂ =>
      Sum.elim (fun a => f z.1 a) (fun b => g z.2 b) s) (μ.prod ν) := by
  let _ := Fintype.ofFinite κ₁
  let _ := Fintype.ofFinite κ₂
  have hpair := HasGaussianLaw.prodMk_prod hf hg
  let L : ((κ₁ → ℝ) × (κ₂ → ℝ)) →L[ℝ] (κ₁ ⊕ κ₂ → ℝ) := ContinuousLinearMap.pi
    (Sum.elim
      (fun a => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ₁ => ℝ) a).comp
        (ContinuousLinearMap.fst ℝ (κ₁ → ℝ) (κ₂ → ℝ)))
      (fun b => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ₂ => ℝ) b).comp
        (ContinuousLinearMap.snd ℝ (κ₁ → ℝ) (κ₂ → ℝ))))
  convert hpair.map_fun L using 1
  ext z (a | b) <;> simp [L]

/-- Reindexing a finite Gaussian vector and multiplying each new coordinate by a deterministic
scalar preserves its joint Gaussian law.  The reindexing need not be injective, so this also
covers duplicated and signed coordinates. -/
theorem HasGaussianLaw.reindex_mul {Ω κ κ' : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [Finite κ] [Finite κ'] {X : κ → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω k => X k ω) P) (e : κ' → κ) (c : κ' → ℝ) :
    HasGaussianLaw (fun ω k => c k * X (e k) ω) P := by
  let _ := Fintype.ofFinite κ
  let _ := Fintype.ofFinite κ'
  let L : (κ → ℝ) →L[ℝ] (κ' → ℝ) := ContinuousLinearMap.pi fun k =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => ℝ) (e k)).smulRight (c k)
  convert hX.map_fun L using 1
  ext ω k
  simp [L, mul_comm]

/-- Reindexing a finite Gaussian vector preserves its joint Gaussian law. -/
theorem HasGaussianLaw.reindex {Ω κ κ' : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [Finite κ] [Finite κ'] {X : κ → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω k => X k ω) P) (e : κ' → κ) :
    HasGaussianLaw (fun ω k => X (e k) ω) P := by
  simpa using hX.reindex_mul e (fun _ => 1)

/-- Deterministic coordinate scaling preserves the joint Gaussian law. -/
theorem HasGaussianLaw.mul {Ω κ : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [Finite κ] {X : κ → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω k => X k ω) P) (c : κ → ℝ) :
    HasGaussianLaw (fun ω k => c k * X k ω) P :=
  hX.reindex_mul id c

/-- A linear combination `cos s · X + sin s · Y` of two jointly Gaussian blocks has Gaussian law. -/
theorem HasGaussianLaw.cos_sin_combination {Ω κ : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [Finite κ] {X Y : κ → Ω → ℝ}
    (hXY : HasGaussianLaw (fun ω s => Sum.elim (fun k (ω : Ω) => X k ω) (fun k ω => Y k ω) s ω) P)
    (s : ℝ) :
    HasGaussianLaw (fun ω k => Real.cos s * X k ω + Real.sin s * Y k ω) P := by
  let _ := Fintype.ofFinite κ
  let L : (κ ⊕ κ → ℝ) →L[ℝ] (κ → ℝ) := ContinuousLinearMap.pi fun k =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ ⊕ κ => ℝ) (Sum.inl k)).smulRight
      (Real.cos s)) +
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ ⊕ κ => ℝ) (Sum.inr k)).smulRight
      (Real.sin s))
  convert hXY.map_fun L using 1
  ext ω k
  simp [L, mul_comm]

/-- The coordinate evaluation of `multivariateGaussian 0 S` under `ofLp` has Gaussian law. -/
theorem hasGaussianLaw_ofLp_multivariateGaussian {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : Matrix κ κ ℝ) :
    HasGaussianLaw (fun z : EuclideanSpace ℝ κ => z.ofLp) (multivariateGaussian 0 S) :=
  (IsGaussian.hasGaussianLaw_id (μ := multivariateGaussian 0 S)).map_fun
    (ContinuousLinearEquiv.toContinuousLinearMap (PiLp.continuousLinearEquiv 2 ℝ fun _ : κ => ℝ))

/-- Coordinates of `multivariateGaussian 0 S` are centered. -/
theorem integral_eval_multivariateGaussian {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : Matrix κ κ ℝ) (x : κ) :
    ∫ z : EuclideanSpace ℝ κ, z x ∂(multivariateGaussian 0 S) = 0 := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) x).integral_comp_comm
    (IsGaussian.integrable_id (μ := multivariateGaussian 0 S))
  simpa [integral_id_multivariateGaussian'] using h

/-- Second moments of the coordinates of `multivariateGaussian 0 S`. -/
theorem integral_mul_eval_multivariateGaussian {κ : Type*} [Fintype κ] [DecidableEq κ]
    {S : Matrix κ κ ℝ} (hS : S.PosSemidef) (x y : κ) :
    ∫ z : EuclideanSpace ℝ κ, z x * z y ∂(multivariateGaussian 0 S) = S x y := by
  have h1 := hasGaussianLaw_ofLp_multivariateGaussian S
  have hx : MemLp (fun z : EuclideanSpace ℝ κ => z x) 2 (multivariateGaussian 0 S) :=
    (h1.eval x).memLp_two
  have hy : MemLp (fun z : EuclideanSpace ℝ κ => z y) 2 (multivariateGaussian 0 S) :=
    (h1.eval y).memLp_two
  have := covariance_eval_multivariateGaussian (μ := 0) hS x y
  rw [covariance_eq_sub hx hy, integral_eval_multivariateGaussian,
    integral_eval_multivariateGaussian] at this
  simpa using this

end ProbabilityTheory
