/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiLinearForm
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianVector
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The law of a Gaussian family depends only on its Gram matrix

A centered Gaussian vector is determined in law by its covariance matrix
(`map_eq_of_integral_mul_eq`).  Linear forms `r ↦ a r ⬝ᵥ ξ` of i.i.d. standard Gaussians
`ξ ~ 𝒩(0,1)^K` are centered Gaussian with covariance `a r ⬝ᵥ a s`
(`hasGaussianLaw_dotProduct_family`), so any centered Gaussian family `X` with
`𝔼 X r X s = a r ⬝ᵥ a s` has the law of `r ↦ a r ⬝ᵥ ξ`:

* `ProbabilityTheory.map_toLp_dotProduct_pi_gaussianReal`: the law of `r ↦ a r ⬝ᵥ ξ` is
  `multivariateGaussian 0 (a r ⬝ᵥ a s)` (used by `NTK.stdGaussian_inner_family`);
* `ProbabilityTheory.integral_comp_comp_eq_integral_multivariateGaussian`: for a subfamily
  `(X (j l))_l` of a centered Gaussian family, expectations are Gaussian integrals against
  `multivariateGaussian 0 (𝔼 X (j l) X (j l'))`;
* `ProbabilityTheory.integral_comp_eq_integral_dotProduct`: for measurable `f`,
  `𝔼 f (X) = 𝔼 f (a ⬝ᵥ ξ)` (and the matching `integrable_comp_iff_dotProduct`);
* `ProbabilityTheory.integral_comp_eq_integral_dotProduct_prod`: the same for two independent
  blocks `(u, v) ~ 𝒩(0,1)^{K₁} ⊗ 𝒩(0,1)^{K₂}` and `r ↦ a₁ r ⬝ᵥ u + a₂ r ⬝ᵥ v`, with Gram matrix
  `a₁ r ⬝ᵥ a₁ s + a₂ r ⬝ᵥ a₂ s`.

This is how a Gaussian Hamiltonian is rewritten as a sum of independent Gaussian pieces *in law*
without any change of variables on the disorder (see `SpinGlasses/AizenmanSimsStarr.lean`).
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace ProbabilityTheory

section Law

variable {A Ω Ω' : Type*} [Finite A] {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {Q : Measure Ω'}

/-- **Centered Gaussian vectors with the same second moments have the same law.** -/
theorem map_eq_of_integral_mul_eq {X : A → Ω → ℝ} {Y : A → Ω' → ℝ}
    (hX : HasGaussianLaw (fun ω a => X a ω) P) (hY : HasGaussianLaw (fun ω a => Y a ω) Q)
    (hX0 : ∀ a, ∫ ω, X a ω ∂P = 0) (hY0 : ∀ a, ∫ ω, Y a ω ∂Q = 0)
    (hcov : ∀ a b, ∫ ω, X a ω * X b ω ∂P = ∫ ω, Y a ω * Y b ω ∂Q) :
    P.map (fun ω a => X a ω) = Q.map (fun ω a => Y a ω) := by
  have := Fintype.ofFinite A
  classical
  have hP := hX.isProbabilityMeasure
  have hQ := hY.isProbabilityMeasure
  rw [map_eq_map_multivariateGaussian hX hX0, map_eq_map_multivariateGaussian hY hY0]
  congr 2
  ext a b
  simp only [Matrix.of_apply]
  rw [covariance_eq_sub (hX.eval a).memLp_two (hX.eval b).memLp_two,
    covariance_eq_sub (hY.eval a).memLp_two (hY.eval b).memLp_two, hX0, hY0]
  simpa using hcov a b

end Law

section Restrict

variable {ι κ : Type*} [Finite ι] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **A subfamily of a Gaussian family is Gaussian:** `(X (j l))_l` for `j : κ → ι`. -/
theorem hasGaussianLaw_comp_index [Finite κ] {X : ι → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω i => X i ω) P) (j : κ → ι) :
    HasGaussianLaw (fun ω l => X (j l) ω) P := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  exact hX.map_fun (LinearMap.funLeft ℝ ℝ j).toContinuousLinearMap

/-- **Expectations of a subfamily of a centered Gaussian family are Gaussian integrals.**
For `j : κ → ι` and measurable `f`,
`𝔼 f ((X (j l))_l) = ∫ f d(multivariateGaussian 0 (𝔼 X (j l) X (j l')))`. -/
theorem integral_comp_comp_eq_integral_multivariateGaussian [Fintype κ] [DecidableEq κ]
    {X : ι → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω i => X i ω) P) (h0 : ∀ i, ∫ ω, X i ω ∂P = 0) (j : κ → ι)
    {f : (κ → ℝ) → ℝ} (hf : Measurable f) :
    ∫ ω, f (fun l => X (j l) ω) ∂P =
      ∫ x : EuclideanSpace ℝ κ, f x.ofLp ∂(multivariateGaussian 0
        (Matrix.of fun l l' => ∫ ω, X (j l) ω * X (j l') ω ∂P)) := by
  have hY := hasGaussianLaw_comp_index hX j
  have hP := hX.isProbabilityMeasure
  have hmem : ∀ l, MemLp (fun ω => X (j l) ω) 2 P := fun l => (hY.eval l).memLp_two
  have hS : (Matrix.of fun l l' => cov[fun ω => X (j l) ω, fun ω => X (j l') ω; P]) =
      Matrix.of fun l l' => ∫ ω, X (j l) ω * X (j l') ω ∂P := by
    ext l l'
    simp only [Matrix.of_apply]
    rw [covariance_eq_sub (hmem l) (hmem l'), h0, h0, mul_zero, sub_zero]
    rfl
  have h := map_eq_map_multivariateGaussian hY fun l => h0 (j l)
  rw [hS] at h
  rw [← integral_map hY.aemeasurable hf.aestronglyMeasurable, h,
    integral_map (PiLp.continuous_ofLp 2 _).aemeasurable hf.aestronglyMeasurable]

end Restrict

section DotProduct

variable {A K : Type*} [Finite A] [Fintype K]

/-- **Linear forms of i.i.d. standard Gaussians form a Gaussian vector.** -/
theorem hasGaussianLaw_dotProduct_family (a : A → K → ℝ) :
    HasGaussianLaw (fun (ξ : K → ℝ) (r : A) => a r ⬝ᵥ ξ)
      (Measure.pi fun _ : K => gaussianReal 0 1) := by
  have := Fintype.ofFinite A
  have := isGaussian_pi_gaussianReal (κ := K)
  exact IsGaussian.hasGaussianLaw_id.map_fun (Matrix.of a).mulVecLin.toContinuousLinearMap

/-- **The law of the linear forms `r ↦ a r ⬝ᵥ ξ` of a standard Gaussian vector** is the centered
multivariate Gaussian with Gram matrix `a r ⬝ᵥ a s`. -/
theorem map_toLp_dotProduct_pi_gaussianReal [Fintype A] [DecidableEq A] (a : A → K → ℝ) :
    (Measure.pi fun _ : K => gaussianReal 0 1).map
        (fun ξ : K → ℝ => WithLp.toLp 2 (fun r => a r ⬝ᵥ ξ)) =
      multivariateGaussian (0 : EuclideanSpace ℝ A) (Matrix.of fun r s => a r ⬝ᵥ a s) := by
  have h := map_toLp_eq_multivariateGaussian (hasGaussianLaw_dotProduct_family a)
    (fun r => integral_dotProduct_pi_gaussianReal (a r))
  convert h using 3
  ext r s
  rw [covariance_eq_sub ((hasGaussianLaw_dotProduct_family a).eval r).memLp_two
    ((hasGaussianLaw_dotProduct_family a).eval s).memLp_two]
  simp only [Pi.mul_apply, integral_dotProduct_mul_dotProduct_pi_gaussianReal,
    integral_dotProduct_pi_gaussianReal, mul_zero, sub_zero]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **Gram transfer.**  If `X` is a centered Gaussian family with `𝔼 X r X s = a r ⬝ᵥ a s`, then
it has the law of the linear forms `r ↦ a r ⬝ᵥ ξ` of i.i.d. standard Gaussians. -/
theorem map_eq_map_dotProduct_family {X : A → Ω → ℝ} (a : A → K → ℝ)
    (hX : HasGaussianLaw (fun ω r => X r ω) P) (hX0 : ∀ r, ∫ ω, X r ω ∂P = 0)
    (hcov : ∀ r s, ∫ ω, X r ω * X s ω ∂P = a r ⬝ᵥ a s) :
    P.map (fun ω r => X r ω) =
      (Measure.pi fun _ : K => gaussianReal 0 1).map (fun ξ r => a r ⬝ᵥ ξ) :=
  map_eq_of_integral_mul_eq (Y := fun r ξ => a r ⬝ᵥ ξ) hX (hasGaussianLaw_dotProduct_family a)
    hX0 (fun _ => integral_dotProduct_pi_gaussianReal _)
    fun r s => (hcov r s).trans (integral_dotProduct_mul_dotProduct_pi_gaussianReal _ _).symm

/-- **Gram transfer, integrals:** for measurable `f`, `𝔼 f (X) = 𝔼 f (r ↦ a r ⬝ᵥ ξ)` whenever `X`
is a centered Gaussian family with Gram matrix `a r ⬝ᵥ a s`. -/
theorem integral_comp_eq_integral_dotProduct {X : A → Ω → ℝ} (a : A → K → ℝ)
    (hX : HasGaussianLaw (fun ω r => X r ω) P) (hX0 : ∀ r, ∫ ω, X r ω ∂P = 0)
    (hcov : ∀ r s, ∫ ω, X r ω * X s ω ∂P = a r ⬝ᵥ a s) {f : (A → ℝ) → ℝ} (hf : Measurable f) :
    ∫ ω, f (fun r => X r ω) ∂P =
      ∫ ξ, f (fun r => a r ⬝ᵥ ξ) ∂(Measure.pi fun _ : K => gaussianReal 0 1) := by
  have h := map_eq_map_dotProduct_family a hX hX0 hcov
  have h1 := integral_map hX.aemeasurable hf.aestronglyMeasurable
  rw [← h1, h, integral_map (hasGaussianLaw_dotProduct_family a).aemeasurable
    hf.aestronglyMeasurable]

/-- **Gram transfer, integrability.** -/
theorem integrable_comp_iff_dotProduct {X : A → Ω → ℝ} (a : A → K → ℝ)
    (hX : HasGaussianLaw (fun ω r => X r ω) P) (hX0 : ∀ r, ∫ ω, X r ω ∂P = 0)
    (hcov : ∀ r s, ∫ ω, X r ω * X s ω ∂P = a r ⬝ᵥ a s) {f : (A → ℝ) → ℝ} (hf : Measurable f) :
    Integrable (fun ω => f (fun r => X r ω)) P ↔
      Integrable (fun ξ => f (fun r => a r ⬝ᵥ ξ)) (Measure.pi fun _ : K => gaussianReal 0 1) := by
  have h := map_eq_map_dotProduct_family a hX hX0 hcov
  have h1 := integrable_map_measure (g := f) hf.aestronglyMeasurable hX.aemeasurable
  have h2 := integrable_map_measure (g := f) hf.aestronglyMeasurable
    (hasGaussianLaw_dotProduct_family a).aemeasurable
  rw [h] at h1
  exact h1.symm.trans h2

end DotProduct

section Prod

variable {A K₁ K₂ : Type*} [Finite A] [Fintype K₁] [Fintype K₂] {Ω : Type*}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A linear form of a pair of independent blocks of i.i.d. standard Gaussians is the linear form
of the combined block. -/
private lemma sumElim_dotProduct_comp (a₁ : K₁ → ℝ) (a₂ : K₂ → ℝ) (ξ : K₁ ⊕ K₂ → ℝ) :
    Sum.elim a₁ a₂ ⬝ᵥ ξ = a₁ ⬝ᵥ (ξ ∘ Sum.inl) + a₂ ⬝ᵥ (ξ ∘ Sum.inr) := by
  simp [dotProduct, Fintype.sum_sum_type]

omit [Finite A] in
/-- Linear forms of a pair of blocks are measurable. -/
theorem measurable_dotProduct_prod (a₁ : A → K₁ → ℝ) (a₂ : A → K₂ → ℝ) :
    Measurable fun (q : (K₁ → ℝ) × (K₂ → ℝ)) (r : A) => a₁ r ⬝ᵥ q.1 + a₂ r ⬝ᵥ q.2 := by
  refine measurable_pi_iff.2 fun r => ?_
  simp only [dotProduct]
  fun_prop

/-- **Gram transfer, two independent blocks:** a centered Gaussian family `X` with
`𝔼 X r X s = a₁ r ⬝ᵥ a₁ s + a₂ r ⬝ᵥ a₂ s` has the law of
`r ↦ a₁ r ⬝ᵥ u + a₂ r ⬝ᵥ v` for independent `u ~ 𝒩(0,1)^{K₁}`, `v ~ 𝒩(0,1)^{K₂}`. -/
theorem map_eq_map_dotProduct_prod {X : A → Ω → ℝ} (a₁ : A → K₁ → ℝ) (a₂ : A → K₂ → ℝ)
    (hX : HasGaussianLaw (fun ω r => X r ω) P) (hX0 : ∀ r, ∫ ω, X r ω ∂P = 0)
    (hcov : ∀ r s, ∫ ω, X r ω * X s ω ∂P = a₁ r ⬝ᵥ a₁ s + a₂ r ⬝ᵥ a₂ s) :
    P.map (fun ω r => X r ω) =
      ((Measure.pi fun _ : K₁ => gaussianReal 0 1).prod
        (Measure.pi fun _ : K₂ => gaussianReal 0 1)).map
          (fun q r => a₁ r ⬝ᵥ q.1 + a₂ r ⬝ᵥ q.2) := by
  rw [map_eq_map_dotProduct_family (fun r => Sum.elim (a₁ r) (a₂ r)) hX hX0
    (fun r s => by
      rw [hcov r s]
      simp [dotProduct, Fintype.sum_sum_type])]
  have hmp := measurePreserving_sumPiEquivProdPi_symm
    (X := fun _ : K₁ ⊕ K₂ => ℝ) (fun _ => gaussianReal 0 1)
  have hg : Measurable fun (ξ : K₁ ⊕ K₂ → ℝ) (r : A) => Sum.elim (a₁ r) (a₂ r) ⬝ᵥ ξ := by
    refine measurable_pi_iff.2 fun r => ?_
    simp only [dotProduct]
    fun_prop
  rw [← hmp.map_eq, Measure.map_map hg (MeasurableEquiv.measurable _)]
  congr 1
  funext ξ r
  simp only [Function.comp_apply, sumElim_dotProduct_comp]
  rfl

/-- **Gram transfer, integrals, two independent blocks:** for measurable `f`,
`𝔼 f (X) = 𝔼 f (r ↦ a₁ r ⬝ᵥ u + a₂ r ⬝ᵥ v)`. -/
theorem integral_comp_eq_integral_dotProduct_prod {X : A → Ω → ℝ} (a₁ : A → K₁ → ℝ)
    (a₂ : A → K₂ → ℝ) (hX : HasGaussianLaw (fun ω r => X r ω) P)
    (hX0 : ∀ r, ∫ ω, X r ω ∂P = 0)
    (hcov : ∀ r s, ∫ ω, X r ω * X s ω ∂P = a₁ r ⬝ᵥ a₁ s + a₂ r ⬝ᵥ a₂ s) {f : (A → ℝ) → ℝ}
    (hf : Measurable f) :
    ∫ ω, f (fun r => X r ω) ∂P =
      ∫ q, f (fun r => a₁ r ⬝ᵥ q.1 + a₂ r ⬝ᵥ q.2)
        ∂((Measure.pi fun _ : K₁ => gaussianReal 0 1).prod
          (Measure.pi fun _ : K₂ => gaussianReal 0 1)) := by
  rw [← integral_map hX.aemeasurable hf.aestronglyMeasurable,
    map_eq_map_dotProduct_prod a₁ a₂ hX hX0 hcov,
    integral_map (measurable_dotProduct_prod a₁ a₂).aemeasurable hf.aestronglyMeasurable]

/-- **Gram transfer, integrability, two independent blocks.** -/
theorem integrable_comp_iff_dotProduct_prod {X : A → Ω → ℝ} (a₁ : A → K₁ → ℝ)
    (a₂ : A → K₂ → ℝ) (hX : HasGaussianLaw (fun ω r => X r ω) P)
    (hX0 : ∀ r, ∫ ω, X r ω ∂P = 0)
    (hcov : ∀ r s, ∫ ω, X r ω * X s ω ∂P = a₁ r ⬝ᵥ a₁ s + a₂ r ⬝ᵥ a₂ s) {f : (A → ℝ) → ℝ}
    (hf : Measurable f) :
    Integrable (fun ω => f (fun r => X r ω)) P ↔
      Integrable (fun q => f (fun r => a₁ r ⬝ᵥ q.1 + a₂ r ⬝ᵥ q.2))
        ((Measure.pi fun _ : K₁ => gaussianReal 0 1).prod
          (Measure.pi fun _ : K₂ => gaussianReal 0 1)) := by
  have h1 := integrable_map_measure (g := f) hf.aestronglyMeasurable hX.aemeasurable
  have h2 := integrable_map_measure (g := f)
    (μ := (Measure.pi fun _ : K₁ => gaussianReal 0 1).prod
      (Measure.pi fun _ : K₂ => gaussianReal 0 1)) hf.aestronglyMeasurable
    (measurable_dotProduct_prod a₁ a₂).aemeasurable
  rw [map_eq_map_dotProduct_prod a₁ a₂ hX hX0 hcov] at h1
  exact h1.symm.trans h2

end Prod

end ProbabilityTheory
