/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.SqrtSub
public import LeanMachineLearning.ForMathlib.Probability.StdGaussianRadial
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.CovarianceBilin

/-!
# Linear forms of an i.i.d. standard Gaussian vector

For `g` with i.i.d. `𝒩(0, 1)` coordinates indexed by a finite type `κ`
(`Measure.pi fun _ : κ => gaussianReal 0 1`), the linear forms `a ⬝ᵥ g` are centered with
covariance `𝔼[(a ⬝ᵥ g)(b ⬝ᵥ g)] = a ⬝ᵥ b`.  This is the covariance of `stdGaussian`
(`covarianceBilin_stdGaussian`) transported along
`pi_gaussianReal_eq_map_stdGaussian`.  It is the Gaussian-field covariance used for the pure
`p`-spin Hamiltonians of `SpinGlasses/Panchenko/Foundations/MixedPSpin.lean`,
with `κ = (Fin p → ι)`.

The coordinate-free statements, for `stdGaussian E` on a finite-dimensional real inner product
space and the linear forms `x ↦ ⟪a, x⟫`, include the exponential and `cosh` moments.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ENNReal NNReal

namespace ProbabilityTheory

variable {κ : Type*} [Fintype κ]

section StdGaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Linear forms of a standard Gaussian vector have finite moments of every finite order. -/
theorem memLp_inner_stdGaussian (a : E) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun x : E => inner ℝ a x) p (stdGaussian E) :=
  (innerSL ℝ a).comp_memLp' (IsGaussian.memLp_id (stdGaussian E) p hp)

/-- Linear forms of a standard Gaussian vector are centered. -/
theorem integral_inner_stdGaussian (a : E) : ∫ x, inner ℝ a x ∂(stdGaussian E) = 0 :=
  integral_strongDual_stdGaussian (innerSL ℝ a)

/-- **Covariance of linear forms of a standard Gaussian vector:**
`𝔼[⟪a, x⟫ ⟪b, x⟫] = ⟪a, b⟫`. -/
theorem integral_inner_mul_inner_stdGaussian (a b : E) :
    ∫ x, inner ℝ a x * inner ℝ b x ∂(stdGaussian E) = inner ℝ a b := by
  have hmem : MemLp id 2 (stdGaussian E) := IsGaussian.memLp_two_id
  have h := covarianceBilin_apply hmem a b
  have h0 : ∫ x, id x ∂(stdGaussian E) = 0 := integral_id_stdGaussian
  rw [h0, covarianceBilin_stdGaussian] at h
  simp only [sub_zero] at h
  rw [innerSL_apply_apply] at h
  exact h.symm

/-- The linear form `⟪a, x⟫` of a standard Gaussian vector has law `𝒩(0, ‖a‖²)`. -/
theorem map_inner_stdGaussian (a : E) :
    (stdGaussian E).map (fun x => inner ℝ a x) = gaussianReal 0 (‖a‖₊ ^ 2) := by
  have h := IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) (innerSL ℝ a)
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian, innerSL_apply_norm] at h
  have e : (‖a‖ ^ 2).toNNReal = ‖a‖₊ ^ 2 := by
    ext
    simp [Real.coe_toNNReal _ (sq_nonneg ‖a‖)]
  rwa [e] at h

/-- The exponential of a linear form of a standard Gaussian vector is integrable. -/
theorem integrable_exp_inner_stdGaussian (a : E) :
    Integrable (fun x : E => Real.exp (inner ℝ a x)) (stdGaussian E) := by
  have h := integrable_exp_mul_gaussianReal (μ := 0) (v := ‖a‖₊ ^ 2) 1
  rw [← map_inner_stdGaussian a] at h
  have h' := (integrable_map_measure (by fun_prop) (by fun_prop)).1 h
  simpa only [Function.comp_def, one_mul] using h'

/-- **Exponential moment of a linear form:** `𝔼 exp ⟪a, x⟫ = exp (‖a‖² / 2)`. -/
theorem integral_exp_inner_stdGaussian (a : E) :
    ∫ x, Real.exp (inner ℝ a x) ∂(stdGaussian E) = Real.exp (‖a‖ ^ 2 / 2) := by
  have h := congr_fun (mgf_fun_id_gaussianReal (μ := 0) (v := ‖a‖₊ ^ 2)) 1
  rw [mgf, ← map_inner_stdGaussian a, integral_map (by fun_prop) (by fun_prop)] at h
  simpa using h

/-- `cosh (⟪a, x⟫ + m)` is integrable for a standard Gaussian vector. -/
theorem integrable_cosh_inner_add_stdGaussian (a : E) (m : ℝ) :
    Integrable (fun x : E => Real.cosh (inner ℝ a x + m)) (stdGaussian E) := by
  have h := (((integrable_exp_inner_stdGaussian a).mul_const (Real.exp m)).add
    ((integrable_exp_inner_stdGaussian (-a)).mul_const (Real.exp (-m)))).div_const 2
  refine h.congr (ae_of_all _ fun x => ?_)
  simp only [Pi.add_apply, Real.cosh_eq, inner_neg_left, neg_add, Real.exp_add]

/-- `𝔼 cosh (⟪a, x⟫ + m) = cosh m · exp (‖a‖² / 2)` for a standard Gaussian vector. -/
theorem integral_cosh_inner_add_stdGaussian (a : E) (m : ℝ) :
    ∫ x, Real.cosh (inner ℝ a x + m) ∂(stdGaussian E) =
      Real.cosh m * Real.exp (‖a‖ ^ 2 / 2) := by
  have e : (fun x : E => Real.cosh (inner ℝ a x + m)) = fun x =>
      (Real.exp (inner ℝ a x) * Real.exp m + Real.exp (inner ℝ (-a) x) * Real.exp (-m)) / 2 := by
    funext x
    simp only [Real.cosh_eq, inner_neg_left, neg_add, Real.exp_add]
  rw [e, integral_div, integral_add ((integrable_exp_inner_stdGaussian a).mul_const _)
    ((integrable_exp_inner_stdGaussian (-a)).mul_const _), integral_mul_const,
    integral_mul_const, integral_exp_inner_stdGaussian, integral_exp_inner_stdGaussian,
    norm_neg, Real.cosh_eq]
  ring

end StdGaussian

/-- **The product of i.i.d. standard Gaussians is a Gaussian measure** on `κ → ℝ`
(`stdGaussian` pushed along the continuous linear equivalence `ofLp`). -/
theorem isGaussian_pi_gaussianReal : IsGaussian (Measure.pi fun _ : κ => gaussianReal 0 1) := by
  rw [pi_gaussianReal_eq_map_stdGaussian]
  exact isGaussian_map_equiv (μ := stdGaussian (EuclideanSpace ℝ κ))
    (PiLp.continuousLinearEquiv 2 ℝ fun _ : κ => ℝ)

/-- The linear form `g ↦ a ⬝ᵥ g` of i.i.d. standard Gaussians is the inner product with the
Euclidean vector `a`, after pushing the product measure to `stdGaussian`. -/
private lemma dotProduct_eq_inner (a g : κ → ℝ) :
    a ⬝ᵥ g = inner ℝ (WithLp.toLp 2 a) (WithLp.toLp 2 g) := by
  simp [dotProduct, PiLp.inner_apply, mul_comm]

/-- **Covariance of linear forms of i.i.d. standard Gaussians:**
`𝔼[(a ⬝ᵥ g)(b ⬝ᵥ g)] = a ⬝ᵥ b`. -/
theorem integral_dotProduct_mul_dotProduct_pi_gaussianReal (a b : κ → ℝ) :
    ∫ g : κ → ℝ, (a ⬝ᵥ g) * (b ⬝ᵥ g) ∂(Measure.pi fun _ : κ => gaussianReal 0 1) = a ⬝ᵥ b := by
  rw [pi_gaussianReal_eq_map_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  simp only [dotProduct_eq_inner a, dotProduct_eq_inner b, WithLp.toLp_ofLp]
  exact integral_inner_mul_inner_stdGaussian _ _

/-- Linear forms of i.i.d. standard Gaussians are centered. -/
theorem integral_dotProduct_pi_gaussianReal (a : κ → ℝ) :
    ∫ g : κ → ℝ, a ⬝ᵥ g ∂(Measure.pi fun _ : κ => gaussianReal 0 1) = 0 := by
  rw [pi_gaussianReal_eq_map_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  simp only [dotProduct_eq_inner a, WithLp.toLp_ofLp]
  exact integral_inner_stdGaussian _

/-- Linear forms of i.i.d. standard Gaussians are square-integrable. -/
theorem memLp_dotProduct_pi_gaussianReal (a : κ → ℝ) :
    MemLp (fun g : κ → ℝ => a ⬝ᵥ g) 2 (Measure.pi fun _ : κ => gaussianReal 0 1) := by
  rw [pi_gaussianReal_eq_map_stdGaussian]
  refine (memLp_map_measure_iff (by fun_prop) (by fun_prop)).2 ?_
  simp only [Function.comp_def, dotProduct_eq_inner a]
  exact memLp_inner_stdGaussian _ (by simp)

/-- A linear form `∑ k, g k * a k` is the dot product `a ⬝ᵥ g`. -/
theorem sum_mul_comm_eq_dotProduct (a g : κ → ℝ) : ∑ k, g k * a k = a ⬝ᵥ g :=
  dotProduct_comm g a

/-- **Covariance of two normalized Gaussian linear forms.**  For arbitrary coefficient vectors on
any finite index type and `n ≥ 0`,
`𝔼[(β/√n ∑ k, g k * a k)(β/√n ∑ k, g k * b k)] = n⁻¹ β² (a ⬝ᵥ b)`. -/
theorem integral_normalized_gaussian_linear_form_mul (n β : ℝ) (hn : 0 ≤ n) (a b : κ → ℝ) :
    ∫ g : κ → ℝ,
      ((Real.sqrt n)⁻¹ * β * ∑ k, g k * a k) *
        ((Real.sqrt n)⁻¹ * β * ∑ k, g k * b k)
      ∂(Measure.pi fun _ : κ => gaussianReal 0 1) =
      n⁻¹ * β ^ 2 * (a ⬝ᵥ b) := by
  have hc (u v : ℝ) : ((Real.sqrt n)⁻¹ * β * u) * ((Real.sqrt n)⁻¹ * β * v) =
      n⁻¹ * β ^ 2 * (u * v) := by
    rw [← Real.inv_sqrt_mul_self n hn]
    ring
  simp_rw [sum_mul_comm_eq_dotProduct, hc]
  rw [integral_const_mul, integral_dotProduct_mul_dotProduct_pi_gaussianReal]

/-- Product of two linear forms of i.i.d. standard Gaussians is integrable. -/
theorem integrable_dotProduct_mul_dotProduct_pi_gaussianReal (a b : κ → ℝ) :
    Integrable (fun g : κ → ℝ => (a ⬝ᵥ g) * (b ⬝ᵥ g))
      (Measure.pi fun _ : κ => gaussianReal 0 1) :=
  (memLp_dotProduct_pi_gaussianReal a).integrable_mul (memLp_dotProduct_pi_gaussianReal b)

/-- Covariance of individual coordinates of i.i.d. standard Gaussians: `1` if `p = p'`,
`0` otherwise. -/
theorem integral_pi_gaussianReal_coord_mul [DecidableEq κ] (p p' : κ) :
    ∫ g : κ → ℝ, g p * g p' ∂(Measure.pi fun _ : κ => gaussianReal 0 1) =
      if p = p' then 1 else 0 := by
  have := integral_dotProduct_mul_dotProduct_pi_gaussianReal (Pi.single p (1 : ℝ))
    (Pi.single p' (1 : ℝ))
  simpa [dotProduct_single, single_dotProduct, Pi.single_apply, eq_comm] using this

/-- Individual coordinates of i.i.d. standard Gaussians are centered. -/
theorem integral_pi_gaussianReal_coord (p : κ) :
    ∫ g : κ → ℝ, g p ∂(Measure.pi fun _ : κ => gaussianReal 0 1) = 0 := by
  classical
  have := integral_dotProduct_pi_gaussianReal (Pi.single p (1 : ℝ))
  simpa [single_dotProduct] using this

end ProbabilityTheory

