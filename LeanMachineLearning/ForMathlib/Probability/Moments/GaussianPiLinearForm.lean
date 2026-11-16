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
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace ProbabilityTheory

variable {κ : Type*} [Fintype κ]

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
  have hmem : MemLp id 2 (stdGaussian (EuclideanSpace ℝ κ)) := IsGaussian.memLp_two_id
  have h := covarianceBilin_apply hmem (WithLp.toLp 2 a) (WithLp.toLp 2 b)
  have h0 : ∫ x, id x ∂(stdGaussian (EuclideanSpace ℝ κ)) = 0 := integral_id_stdGaussian
  rw [h0, covarianceBilin_stdGaussian] at h
  simp only [sub_zero] at h
  rw [pi_gaussianReal_eq_map_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  simp only [dotProduct_eq_inner a, dotProduct_eq_inner b, WithLp.toLp_ofLp]
  rw [innerSL_apply_apply] at h
  exact h.symm

/-- Linear forms of i.i.d. standard Gaussians are centered. -/
theorem integral_dotProduct_pi_gaussianReal (a : κ → ℝ) :
    ∫ g : κ → ℝ, a ⬝ᵥ g ∂(Measure.pi fun _ : κ => gaussianReal 0 1) = 0 := by
  rw [pi_gaussianReal_eq_map_stdGaussian, integral_map (by fun_prop) (by fun_prop)]
  simp only [dotProduct_eq_inner a, WithLp.toLp_ofLp]
  have h := integral_inner (𝕜 := ℝ) (f := id) (IsGaussian.integrable_id (μ := stdGaussian
    (EuclideanSpace ℝ κ))) (WithLp.toLp 2 a)
  simpa [integral_id_stdGaussian] using h

/-- Linear forms of i.i.d. standard Gaussians are square-integrable. -/
theorem memLp_dotProduct_pi_gaussianReal (a : κ → ℝ) :
    MemLp (fun g : κ → ℝ => a ⬝ᵥ g) 2 (Measure.pi fun _ : κ => gaussianReal 0 1) := by
  rw [pi_gaussianReal_eq_map_stdGaussian]
  refine (memLp_map_measure_iff (by fun_prop) (by fun_prop)).2 ?_
  simp only [Function.comp_def, dotProduct_eq_inner a]
  exact (innerSL ℝ (WithLp.toLp 2 a)).comp_memLp' IsGaussian.memLp_two_id

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

