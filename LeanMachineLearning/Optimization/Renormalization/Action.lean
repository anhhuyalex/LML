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
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : Action Ω)
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
