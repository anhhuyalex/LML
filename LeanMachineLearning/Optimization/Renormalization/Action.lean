/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Expectation
public import LeanMachineLearning.Optimization.Renormalization.Gaussian
public import LeanMachineLearning.Optimization.Renormalization.Perturbation
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Actions and Gaussian expectation

An action is represented relative to an explicit reference measure.  Its induced law is the
normalized exponential tilt by `exp (-S)`.  This makes the usual density presentation precise
without pretending that every measurable space carries a canonical Lebesgue measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal

namespace Renormalization

universe uΩ uI uE

/-- A real action on a configuration space. -/
abbrev Action (Ω : Type uΩ) := Ω → ℝ

namespace Action

/-- The unnormalized partition function of an action relative to `μ`. -/
def partitionFunction {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Action Ω) : ℝ :=
  ∫ x, Real.exp (-S x) ∂μ

/-- The exact integrability condition for an action to induce a probability law. -/
def Normalizable {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Action Ω) : Prop :=
  Integrable (fun x => Real.exp (-S x)) μ

/-- The normalized law represented by `S`, relative to reference measure `μ`. -/
def measure {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Action Ω) : Measure Ω :=
  μ.tilted fun x => -S x

/-- Bundle a normalizable action law as a probability measure. -/
def probabilityMeasure {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) [NeZero μ] (S : Action Ω)
    (hnorm : S.Normalizable μ) : ProbabilityMeasure Ω :=
  ⟨S.measure μ, MeasureTheory.isProbabilityMeasure_tilted hnorm⟩

/-- Expectation under the law represented by an action. -/
def expectation {Ω : Type uΩ} {E : Type uE} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) (S : Action Ω) (O : Ω → E) : E :=
  Renormalization.expectation (S.measure μ) O

/-- The action construction is the existing multiplicative deformation after combining the base
action and perturbing potential.

Informal proof: both sides are the same tilted measure; pointwise,
`-(ε * V x) = -ε * V x`.  This is equation `eq:action-representation-of-distribution` expressed
relative to a reference law rather than a coordinate density.
-/
theorem measure_smul_eq_deform {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) (V : Ω → ℝ) (ε : ℝ) :
    measure μ (fun x => ε * V x) = deform μ V ε := by
  apply congrArg (Measure.tilted μ)
  funext x
  ring

end Action

/-- The quadratic action with precision matrix `P`. -/
def quadraticAction {ι : Type uI} [Fintype ι]
    (P : Matrix ι ι ℝ) (z : EuclideanSpace ℝ ι) : ℝ :=
  (1 / 2 : ℝ) * dotProduct z (P *ᵥ z)

/-- Gaussian expectation, the rigorous counterpart of the source's bra-ket notation. -/
def gaussianExpectation {ι : Type uI} [Fintype ι] {E : Type uE}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Matrix ι ι ℝ) (O : EuclideanSpace ℝ ι → E) : E := by
  classical
  exact expectation (multivariateGaussian 0 K) O

/-- Bra-ket notation for Gaussian expectation with covariance `K`. -/
scoped notation "⟪" O "⟫ᵍ[" K "]" => gaussianExpectation K O

-- Coercivity of a positive-definite quadratic form: `v ↦ vᵀPv` grows at least quadratically.
-- The continuous form is strictly positive on the compact unit sphere (finite-dimensional space),
-- so its minimum there is a positive constant `c`; rescaling any nonzero `v` to the unit sphere
-- and using the degree-two homogeneity of the form gives the global bound `c * ‖v‖² ≤ vᵀPv`.
private lemma posDef_quadraticAction_lower_bound {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : EuclideanSpace ℝ ι, c * ‖v‖ ^ 2 ≤ dotProduct v (P *ᵥ v) := by
  classical
  by_cases h : ∃ v : EuclideanSpace ℝ ι, v ≠ 0
  · -- There is a nonzero vector: the unit sphere is nonempty and we minimize on it.
    rcases h with ⟨v₀, hv₀⟩
    let f : EuclideanSpace ℝ ι → ℝ := fun v => dotProduct v (P *ᵥ v)
    have hf_cont : Continuous f := by
      dsimp [f]
      fun_prop
    have hs_nonempty : (Metric.sphere (0 : EuclideanSpace ℝ ι) 1).Nonempty := by
      refine ⟨‖v₀‖⁻¹ • v₀, ?_⟩
      rw [Metric.mem_sphere, dist_zero_right]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v₀))]
      exact inv_mul_cancel₀ (norm_eq_zero.not.mpr hv₀)
    obtain ⟨x₀, hx₀s, hx₀min⟩ :=
      (isCompact_sphere (0 : EuclideanSpace ℝ ι) 1).exists_isMinOn hs_nonempty hf_cont.continuousOn
    have hx₀norm : ‖x₀‖ = 1 := by simpa using hx₀s
    have hx₀ne : x₀ ≠ 0 := by
      intro hx₀
      simp [hx₀] at hx₀norm
    have hx₀ne' : x₀.ofLp ≠ 0 := by
      simpa using hx₀ne
    have hx₀pos : 0 < f x₀ := by
      dsimp [f]
      simpa using hP.dotProduct_mulVec_pos (x := x₀.ofLp) hx₀ne'
    refine ⟨f x₀, hx₀pos, ?_⟩
    intro v
    by_cases hv : v = 0
    · subst v
      simp [f]
    · -- Rescale `v` onto the unit sphere, then use minimality at `x₀`.
      let u : EuclideanSpace ℝ ι := ‖v‖⁻¹ • v
      have hnorm_ne : ‖v‖ ≠ 0 := norm_eq_zero.not.mpr hv
      have hnorm_u : ‖u‖ = 1 := by
        dsimp [u]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
        exact inv_mul_cancel₀ hnorm_ne
      have hle_u : f x₀ ≤ f u := hx₀min (by simpa using hnorm_u)
      have hveq : v = ‖v‖ • u := by
        dsimp [u]
        rw [smul_smul, mul_inv_cancel₀ hnorm_ne, one_smul]
      -- `f` is homogeneous of degree two, so `f (‖v‖ • u) = ‖v‖² * f u`.
      have hf_smul : ∀ a : ℝ, f (a • u) = a ^ 2 * f u := by
        intro a
        dsimp [f]
        simp [mulVec_smul, smul_dotProduct, dotProduct_smul]
        ring
      calc
        f x₀ * ‖v‖ ^ 2 ≤ f u * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hle_u (sq_nonneg ‖v‖)
        _ = ‖v‖ ^ 2 * f u := by ring
        _ = f (‖v‖ • u) := by rw [hf_smul]
        _ = f v := by rw [← hveq]
  · -- No nonzero vectors exist: the bound is trivial.
    refine ⟨1, zero_lt_one, ?_⟩
    intro v
    have hv : v = 0 := by
      by_contra hne
      exact h ⟨v, hne⟩
    simp [hv]

-- Integrability of the isotropic Gaussian `v ↦ exp (-c * ‖v‖²)` on a finite-dimensional
-- Euclidean space.  This is the dominating integrand for the quadratic form below; Mathlib proves
-- the analogous complex exponential integrable, and taking the real part yields the real Gaussian.
private lemma integrable_exp_neg_mul_normSq {ι : Type*} [Fintype ι] (c : ℝ) (hc : 0 < c) :
    Integrable (fun v : EuclideanSpace ℝ ι => Real.exp (-c * ‖v‖ ^ 2)) volume := by
  have hint : Integrable (fun v : EuclideanSpace ℝ ι =>
      Complex.exp (-(c : ℂ) * ‖v‖ ^ 2 + (0 : ℂ) * inner ℝ (0 : EuclideanSpace ℝ ι) v)) volume :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace
      (b := (c : ℂ)) (by simpa using hc) (0 : ℂ) (0 : EuclideanSpace ℝ ι)
  convert hint.re with v
  -- The real part of the complex Gaussian `cexp (-c * ‖v‖²)` is the real Gaussian.
  simp only [zero_mul, add_zero]
  norm_cast

/-- Integrability of an exponential positive-definite quadratic form on a finite-dimensional
Euclidean space.

Informal proof: diagonalize the real symmetric positive-definite matrix `P` as `Qᵀ D Q` with
positive diagonal entries.  The orthogonal change of variables has Jacobian `1`, after which the
integrand becomes the finite product `∏ i, exp (-(d i / 2) * y i ^ 2)`.  Each one-dimensional
factor is integrable by Mathlib's `integrable_exp_neg_mul_sq`, and Tonelli/Fubini gives the finite
product integrability.  Equivalently, one may derive a coercivity bound
`quadraticAction P z ≥ c * ‖z‖ ^ 2` for some `c > 0` and compare against an isotropic Gaussian.
Source: <https://en.wikipedia.org/wiki/Gaussian_integral#Multidimensional_and_functional_generalizations>.
-/
theorem integrable_exp_neg_quadraticAction_of_posDef {ι : Type uI} [Fintype ι]
    (P : Matrix ι ι ℝ) (hP : P.PosDef) :
    Integrable (fun z : EuclideanSpace ℝ ι => Real.exp (-(quadraticAction P z))) volume := by
  classical
  -- Coercivity gives `c > 0` with `c * ‖z‖² ≤ zᵀPz`, hence `quadraticAction P z ≥ (c / 2) * ‖z‖²`.
  rcases posDef_quadraticAction_lower_bound P hP with ⟨c, hc, hbound⟩
  -- The isotropic Gaussian `z ↦ exp (-(c / 2) * ‖z‖²)` is integrable.
  have hint : Integrable (fun z : EuclideanSpace ℝ ι => Real.exp (-(c / 2) * ‖z‖ ^ 2)) volume :=
    integrable_exp_neg_mul_normSq (c / 2) (div_pos hc zero_lt_two)
  -- The quadratic integrand is bounded pointwise by that isotropic Gaussian, so it is integrable.
  refine Integrable.mono hint ?_ ?_
  · -- The quadratic exponential is continuous, hence strongly measurable a.e.
    have hcont : Continuous fun z : EuclideanSpace ℝ ι => -(quadraticAction P z) := by
      dsimp [quadraticAction]
      fun_prop
    exact (Real.continuous_exp.comp hcont).aestronglyMeasurable
  · filter_upwards with z
    -- Since exp is monotone, it suffices to compare the exponents.
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_exp.mpr
    have hb : c * ‖z‖ ^ 2 ≤ dotProduct z (P *ᵥ z) := hbound z
    have hle : (c / 2) * ‖z‖ ^ 2 ≤ quadraticAction P z := by
      dsimp [quadraticAction]
      calc
        (c / 2 : ℝ) * ‖z‖ ^ 2 = (1 / 2 : ℝ) * (c * ‖z‖ ^ 2) := by ring
        _ ≤ (1 / 2 : ℝ) * dotProduct z (P *ᵥ z) := by
          exact mul_le_mul_of_nonneg_left hb (by positivity)
    simpa using neg_le_neg hle

/-- A positive-definite quadratic action is normalizable against Euclidean volume.

Informal proof: the inverse covariance matrix `K⁻¹` is positive definite by `Matrix.PosDef.inv`,
and the preceding reusable Gaussian-integrability lemma applies to this precision matrix.
-/
theorem quadraticAction_normalizable {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) :
    Action.Normalizable (volume : Measure (EuclideanSpace ℝ ι)) (quadraticAction K⁻¹) := by
  -- The precision matrix `K⁻¹` is positive definite by `Matrix.PosDef.inv`, so the Gaussian
  -- integrability lemma applies with `P := K⁻¹`.
  exact integrable_exp_neg_quadraticAction_of_posDef K⁻¹ hK.inv

/-- The probability measure canonically represented by a positive-definite quadratic action. -/
def quadraticActionProbabilityMeasure {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) : ProbabilityMeasure (EuclideanSpace ℝ ι) :=
  Action.probabilityMeasure volume (quadraticAction K⁻¹) (quadraticAction_normalizable K hK)

/-- The partition function of the positive-definite quadratic action.

The reference measure is Euclidean Lebesgue measure, and `K` is the covariance, so the precision
in the action is `K⁻¹`.

Informal proof: orthogonally diagonalize `K`, change variables to the eigenbasis, and apply the
one-dimensional Gaussian integral in every coordinate.  The Jacobian and eigenvalue product give
`sqrt ((2π)^n det K)`.  Source: equation `eq:intro-quadratic-action-reprint` and the normalization
formula following it in `docs/Renormalization.md`; see also
<https://en.wikipedia.org/wiki/Gaussian_integral#Multidimensional_and_functional_generalizations>.
-/
theorem quadraticAction_partitionFunction {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) :
    Action.partitionFunction (volume : Measure (EuclideanSpace ℝ ι)) (quadraticAction K⁻¹) =
      Real.sqrt ((2 * Real.pi) ^ Fintype.card ι * K.det) := by
  sorry

/-- The normalized law of the quadratic action is exactly Mathlib's multivariate Gaussian.

Informal proof: the preceding Gaussian integral supplies the normalizing constant.  The
Radon--Nikodym density of both measures with respect to Euclidean volume is therefore
`exp (-zᵀK⁻¹z/2) / sqrt ((2π)^n det K)`; equality follows from equality of densities.  Source:
equations `eq:general-prob-ac-map` and `eq:gauss-braket` in `docs/Renormalization.md` and Mathlib's
multivariate Gaussian construction:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Gaussian/Multivariate.html>.
-/
theorem quadraticAction_measure_eq_multivariateGaussian
    {ι : Type uI} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) :
    Action.measure (volume : Measure (EuclideanSpace ℝ ι)) (quadraticAction K⁻¹) =
      multivariateGaussian 0 K := by
  sorry

@[simp] theorem gaussianExpectation_eq_integral {ι : Type uI} [Fintype ι] [DecidableEq ι]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Matrix ι ι ℝ) (O : EuclideanSpace ℝ ι → E) :
    ⟪O⟫ᵍ[K] = ∫ z, O z ∂multivariateGaussian 0 K := rfl

end Renormalization

end

end
