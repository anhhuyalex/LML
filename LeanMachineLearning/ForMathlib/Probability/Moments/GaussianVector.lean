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


/-- **The law of a centered Gaussian vector is `multivariateGaussian 0 S`**, `S` its covariance
matrix. -/
theorem map_toLp_eq_multivariateGaussian {X : κ → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω k => X k ω) P) (hmean : ∀ k, ∫ ω, X k ω ∂P = 0) :
    P.map (fun ω => WithLp.toLp 2 (X · ω)) =
      multivariateGaussian 0 (Matrix.of fun i j => cov[X i, X j; P]) := by
  classical
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
    exact integrable_comp_mulVec_of_exp_growth A hFm hF
  exact (integrable_map_measure hFm.aestronglyMeasurable hX.aemeasurable).1 h2

omit [DecidableEq κ] in
/-- **Differentiation under the integral against a Gaussian vector.**  Let `X` be a centered
Gaussian vector and `G s` a family of measurable functions, differentiable in `s` with
`|∂ₛ G s y| ≤ C exp (c ‖y‖₁)` uniformly in `s`, and `|G s₀ y| ≤ C₀ exp (c₀ ‖y‖₁)`.  Then
`(d/ds) 𝔼 G s (X) = 𝔼 ∂ₛ G s (X)`. -/
theorem hasDerivAt_integral_comp_of_exp_growth {X : κ → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω k => X k ω) P) (hmean : ∀ k, ∫ ω, X k ω ∂P = 0)
    {G G' : ℝ → (κ → ℝ) → ℝ} (s₀ : ℝ) (hGm : ∀ s, Measurable (G s))
    (hG'm : Measurable (G' s₀)) (hG : ∀ s y, HasDerivAt (fun s => G s y) (G' s y) s) {C c : ℝ}
    (hG' : ∀ s y, |G' s y| ≤ C * Real.exp (c * ∑ l, |y l|)) {C₀ c₀ : ℝ}
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
    integrable_comp_of_exp_growth hX hmean (hGm s₀) hG₀
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P)
    (F := fun s ω => G s fun k => X k ω) (F' := fun s ω => G' s fun k => X k ω)
    (bound := fun ω => |C| * Real.exp (|c| * ∑ l, |X l ω|)) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun s => ((hGm s).comp_aemeasurable hXm).aestronglyMeasurable)
    hint0 ((hG'm.comp_aemeasurable hXm).aestronglyMeasurable)
    (ae_of_all _ fun ω s _ => by
      rw [Real.norm_eq_abs]
      exact (hG' s _).trans (hle _))
    hbd (ae_of_all _ fun ω s _ => hG s _)).2

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

omit [Fintype κ₁] [DecidableEq κ₂] in
/-- **Integrability of `W i · exp (A X)`** for a centered Gaussian family `W ⊕ X` and a measurable
`A` with `|A y| ≤ c₁ + c₂ ‖y‖₁`; this makes the integrals in
`integral_mul_exp_comp_eq_sum_integral_mul_of_sum` meaningful. -/
theorem integrable_mul_exp_comp_of_sum [Finite κ₁] {W : κ₁ → Ω → ℝ} {X : κ₂ → Ω → ℝ}
    (hWX : HasGaussianLaw (fun ω s => Sum.elim W X s ω) P)
    (hW : ∀ k, ∫ ω, W k ω ∂P = 0) (hX : ∀ l, ∫ ω, X l ω ∂P = 0) (i : κ₁)
    {A : (κ₂ → ℝ) → ℝ} (hAm : Measurable A) {c₁ c₂ : ℝ}
    (hAg : ∀ y, |A y| ≤ c₁ + c₂ * ∑ l, |y l|) :
    Integrable (fun ω => W i ω * Real.exp (A fun l => X l ω)) P := by
  have := Fintype.ofFinite κ₁
  have hmean : ∀ s, ∫ ω, Sum.elim W X s ω ∂P = 0 := by
    rintro (k | l)
    exacts [hW k, hX l]
  have hexp : ∀ y, |Real.exp (A y)| ≤ Real.exp c₁ * Real.exp (c₂ * ∑ l, |y l|) := fun y => by
    rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (hAg y))
  refine integrable_comp_of_exp_growth (X := Sum.elim W X) hWX hmean
    (F := fun y => y (Sum.inl i) * Real.exp (A fun l => y (Sum.inr l)))
    (by fun_prop) (C := Real.exp c₁) (c := |c₂| + 1) fun y => ?_
  have h1 := abs_comp_inr_le_of_exp_growth (G := fun y' => Real.exp (A y')) hexp y
  have h2 : |y (Sum.inl i)| ≤ ∑ s, |y s| :=
    Finset.single_le_sum (f := fun s => |y s|) (fun _ _ => abs_nonneg _) (Finset.mem_univ _)
  rw [abs_mul]
  calc |y (Sum.inl i)| * |Real.exp (A fun l => y (Sum.inr l))|
      ≤ Real.exp (∑ s, |y s|) * (Real.exp c₁ * Real.exp (|c₂| * ∑ s, |y s|)) :=
        mul_le_mul ((h2.trans (by linarith [Real.add_one_le_exp (∑ s, |y s|)]))) h1
          (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp c₁ * Real.exp ((|c₂| + 1) * ∑ s, |y s|) := by
        rw [add_mul, one_mul, Real.exp_add]; ring

omit [Fintype κ₁] [DecidableEq κ₂] in
/-- **Integrability of `exp (A X)`** for a centered Gaussian family `W ⊕ X` and a measurable `A`
with `|A y| ≤ c₁ + c₂ ‖y‖₁`. -/
theorem integrable_exp_comp_of_sum [Finite κ₁] {W : κ₁ → Ω → ℝ} {X : κ₂ → Ω → ℝ}
    (hWX : HasGaussianLaw (fun ω s => Sum.elim W X s ω) P)
    (hW : ∀ k, ∫ ω, W k ω ∂P = 0) (hX : ∀ l, ∫ ω, X l ω ∂P = 0)
    {A : (κ₂ → ℝ) → ℝ} (hAm : Measurable A) {c₁ c₂ : ℝ}
    (hAg : ∀ y, |A y| ≤ c₁ + c₂ * ∑ l, |y l|) :
    Integrable (fun ω => Real.exp (A fun l => X l ω)) P := by
  have := Fintype.ofFinite κ₁
  have hmean : ∀ s, ∫ ω, Sum.elim W X s ω ∂P = 0 := by
    rintro (k | l)
    exacts [hW k, hX l]
  have hexp : ∀ y, |Real.exp (A y)| ≤ Real.exp c₁ * Real.exp (c₂ * ∑ l, |y l|) := fun y => by
    rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans (hAg y))
  exact integrable_comp_of_exp_growth (X := Sum.elim W X) hWX hmean
    (F := fun y => Real.exp (A fun l => y (Sum.inr l))) (by fun_prop) (C := Real.exp c₁)
    (c := |c₂|) fun y => abs_comp_inr_le_of_exp_growth (G := fun y' => Real.exp (A y')) hexp y

omit [Fintype κ₁] in
/-- **Gaussian integration by parts for the exponential of a smooth functional.**  For a centered
Gaussian family `W ⊕ X` and a differentiable `A` with `|A y| ≤ c₁ + c₂ ‖y‖₁` and bounded partial
derivatives `|∂ₗ A| ≤ c₃`,
`𝔼[W i exp (A X)] = ∑ l, 𝔼[W i X l] 𝔼[exp (A X) ∂ₗ A(X)]`.
This is `integral_mul_comp_eq_sum_integral_mul_of_sum` for `F = exp ∘ A`; it covers the Gibbs
weights and partition functions of the spin-glass models, where `A` is a combination of
`log ∑ exp`. -/
theorem integral_mul_exp_comp_eq_sum_integral_mul_of_sum [Finite κ₁] {W : κ₁ → Ω → ℝ}
    {X : κ₂ → Ω → ℝ} (hWX : HasGaussianLaw (fun ω s => Sum.elim W X s ω) P)
    (hW : ∀ k, ∫ ω, W k ω ∂P = 0) (hX : ∀ l, ∫ ω, X l ω ∂P = 0) (i : κ₁)
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
  have h := integral_mul_comp_eq_sum_integral_mul_of_sum hWX hW hX i hE (C := Real.exp c₁)
    (c := c₂) (fun y => by rw [abs_of_pos (Real.exp_pos _)]; exact hexp y)
    (D := fun _ => c₃ * Real.exp c₁) (d := fun _ => c₂) (fun l y => by
      rw [hd, abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (A y) * |fderiv ℝ A y (Pi.single l 1)|
          ≤ (Real.exp c₁ * Real.exp (c₂ * ∑ l, |y l|)) * c₃ :=
            mul_le_mul (hexp y) (hAg' l y) (abs_nonneg _) (by positivity)
        _ = c₃ * Real.exp c₁ * Real.exp (c₂ * ∑ l, |y l|) := by ring)
  simpa only [hd] using h

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

/-- **Gaussian laws on a product space with independent coordinates.**  If `f` and `g` have
Gaussian laws under `μ` and `ν`, then `z ↦ (f z.1, g z.2)` has a Gaussian law under `μ.prod ν`
(the product of two Gaussian measures is Gaussian). -/
theorem HasGaussianLaw.prodMk_prod {Ω₁ Ω₂ E F : Type*} {m₁ : MeasurableSpace Ω₁}
    {m₂ : MeasurableSpace Ω₂} {μ : Measure Ω₁} {ν : Measure Ω₂} [SFinite μ] [SFinite ν]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopologyEither E F] {f : Ω₁ → E} {g : Ω₂ → F}
    (hf : HasGaussianLaw f μ) (hg : HasGaussianLaw g ν) (hfm : Measurable f) (hgm : Measurable g) :
    HasGaussianLaw (fun z : Ω₁ × Ω₂ => (f z.1, g z.2)) (μ.prod ν) where
  aemeasurable := ((hfm.comp measurable_fst).prodMk (hgm.comp measurable_snd)).aemeasurable
  isGaussian_map := by
    have := hf.isGaussian_map
    have := hg.isGaussian_map
    have h : (μ.prod ν).map (fun z : Ω₁ × Ω₂ => (f z.1, g z.2)) = (μ.map f).prod (ν.map g) :=
      (Measure.map_prod_map μ ν hfm hgm).symm
    rw [h]
    infer_instance

/-- **Two independent copies of a Gaussian vector are jointly Gaussian:** if `g` is a Gaussian
vector `(g a)ₐ` under `P`, then `z ↦ (g a z.1, g a z.2)` is a Gaussian vector indexed by `κ ⊕ κ`
under `P ⊗ P`. -/
theorem HasGaussianLaw.sumElim_prod {Ω' κ' : Type*} {m : MeasurableSpace Ω'} {P' : Measure Ω'}
    [SFinite P'] [Finite κ'] {g : κ' → Ω' → ℝ} (hg : HasGaussianLaw (fun ω a => g a ω) P')
    (hm : ∀ a, Measurable (g a)) :
    HasGaussianLaw (fun (z : Ω' × Ω') (s : κ' ⊕ κ') =>
      Sum.elim (fun a (z : Ω' × Ω') => g a z.1) (fun a (z : Ω' × Ω') => g a z.2) s z)
      (P'.prod P') := by
  have := Fintype.ofFinite κ'
  have hmv : Measurable fun ω a => g a ω := Measurable.of_eval hm
  have hpair := HasGaussianLaw.prodMk_prod hg hg hmv hmv
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
    [SFinite μ] [SFinite ν] [Finite κ₁] [Finite κ₂] {f : Ω₁ → κ₁ → ℝ} {g : Ω₂ → κ₂ → ℝ}
    (hf : HasGaussianLaw f μ) (hg : HasGaussianLaw g ν) (hfm : Measurable f)
    (hgm : Measurable g) :
    HasGaussianLaw (fun z : Ω₁ × Ω₂ => fun s : κ₁ ⊕ κ₂ =>
      Sum.elim (fun a => f z.1 a) (fun b => g z.2 b) s) (μ.prod ν) := by
  let _ := Fintype.ofFinite κ₁
  let _ := Fintype.ofFinite κ₂
  have hpair := HasGaussianLaw.prodMk_prod hf hg hfm hgm
  let L : ((κ₁ → ℝ) × (κ₂ → ℝ)) →L[ℝ] (κ₁ ⊕ κ₂ → ℝ) := ContinuousLinearMap.pi
    (Sum.elim
      (fun a => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ₁ => ℝ) a).comp
        (ContinuousLinearMap.fst ℝ (κ₁ → ℝ) (κ₂ → ℝ)))
      (fun b => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ₂ => ℝ) b).comp
        (ContinuousLinearMap.snd ℝ (κ₁ → ℝ) (κ₂ → ℝ))))
  convert hpair.map_fun L using 1
  ext z (a | b) <;> simp [L]

end ProbabilityTheory
