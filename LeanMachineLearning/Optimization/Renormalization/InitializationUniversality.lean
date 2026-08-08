/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.InducedLaw
public import Mathlib.Probability.CentralLimitTheorem

/-!
# Universality of wide i.i.d. scalar initialization

The informal chapter says that replacing Gaussian weights by weights with matching first two
moments changes wide-network behavior only at order inverse width.  There are two distinct facts:

* the i.i.d. central limit theorem gives qualitative convergence of a normalized preactivation to
  a Gaussian under a finite-second-moment hypothesis; and
* inverse-width corrections hold for selected cumulants or moments under stronger hypotheses,
  while a general distributional Berry--Esseen error is only of order inverse square-root width.

This file keeps those statements separate.  The qualitative theorem is a wrapper around Mathlib's
one-dimensional CLT.  The quantitative Berry--Esseen and fourth-moment calculations are explicit,
well-scoped proof obligations rather than an unjustified blanket `O(1 / width)` assertion.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal ProbabilityTheory Real Topology

namespace NeuralNetwork

universe uΩ uΩ' uΩG

/-- A countable i.i.d. scalar initialization with the normalization used by the standard CLT.
The second moment is stated separately from `MemLp` because it is the numerical normalization that
makes the limiting variance equal to one. -/
structure IIDScalarInitialization (Ω : Type uΩ) [MeasurableSpace Ω] (P : Measure Ω) where
  /-- The unscaled scalar weights. -/
  weight : ℕ → Ω → ℝ
  /-- Mutual independence of the weights. -/
  independent : iIndepFun weight P
  /-- Every weight has the same law as the zeroth weight. -/
  identicallyDistributed : ∀ i, IdentDistrib (weight i) (weight 0) P P
  /-- Centering assumption. -/
  centered : P[weight 0] = 0
  /-- Unit second moment. -/
  unitSecondMoment : P[(weight 0) ^ 2] = 1
  /-- Finite variance; this prevents the numerical integral fields from being vacuous. -/
  memLpTwo : MemLp (weight 0) 2 P

namespace IIDScalarInitialization

variable {Ω : Type uΩ} [MeasurableSpace Ω] {P : Measure Ω}

/-- Width-`n` normalized preactivation with zero bias and unit input coordinates.  Equivalently,
these are i.i.d. weights of variance `1 / n` summed across the input coordinates. -/
def normalizedPreactivation (I : IIDScalarInitialization Ω P) (n : ℕ) (ω : Ω) : ℝ :=
  (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, I.weight k ω

/-- A deterministic triangular array of input coefficients applied to the i.i.d. weights.  This is
the appropriate scalar preactivation for inputs that vary with width. -/
def weightedPreactivation (I : IIDScalarInitialization Ω P)
    (a : ℕ → ℕ → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, a n k * I.weight k ω

/-- The initialization law itself need not be Gaussian. -/
def IsNonGaussian (I : IIDScalarInitialization Ω P) : Prop :=
  Measure.map (I.weight 0) P ≠ gaussianReal 0 1

/-- An i.i.d. normalized preactivation converges in distribution to a standard Gaussian.

This is an exact specialization of Mathlib's central limit theorem.  Notice that Gaussianity of a
single weight is not a hypothesis: independence, identical distribution, centering, and finite
unit variance suffice. -/
theorem tendstoInDistribution_normalizedPreactivation [IsProbabilityMeasure P]
    (I : IIDScalarInitialization Ω P) {ΩG : Type uΩG} [MeasurableSpace ΩG]
    {PG : Measure ΩG} [IsProbabilityMeasure PG] {Z : ΩG → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) PG) :
    TendstoInDistribution I.normalizedPreactivation atTop Z (fun _ => P) PG := by
  exact tendstoInDistribution_inv_sqrt_mul_sum hZ I.centered I.unitSecondMoment
    I.independent I.identicallyDistributed

/-- Explicit non-Gaussian-initialization form of the CLT.  The non-Gaussian hypothesis records the
intended use case; the proof works because the underlying CLT does not require Gaussian summands. -/
theorem IsNonGaussian.tendstoInDistribution_normalizedPreactivation [IsProbabilityMeasure P]
    {I : IIDScalarInitialization Ω P} (hI : I.IsNonGaussian)
    {ΩG : Type uΩG} [MeasurableSpace ΩG] {PG : Measure ΩG} [IsProbabilityMeasure PG]
    {Z : ΩG → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) PG) :
    TendstoInDistribution I.normalizedPreactivation atTop Z (fun _ => P) PG := by
  let _ := hI
  exact I.tendstoInDistribution_normalizedPreactivation hZ

/-- Two possibly different i.i.d. initialization distributions with matching mean and variance
have the same Gaussian wide-width limit.  This is the precise qualitative universality statement;
it does not assert a rate. -/
theorem same_limit_of_matching_first_two_moments
    {Ω' : Type uΩ'} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (I : IIDScalarInitialization Ω P) (J : IIDScalarInitialization Ω' P')
    {ΩG : Type uΩG} [MeasurableSpace ΩG] {PG : Measure ΩG} [IsProbabilityMeasure PG]
    {Z : ΩG → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) PG) :
    TendstoInDistribution I.normalizedPreactivation atTop Z (fun _ => P) PG ∧
      TendstoInDistribution J.normalizedPreactivation atTop Z (fun _ => P') PG :=
  ⟨I.tendstoInDistribution_normalizedPreactivation hZ,
    J.tendstoInDistribution_normalizedPreactivation hZ⟩

/-- Lyapunov universality for deterministic width-dependent inputs.

Informal proof: for row `n`, the independent summands are `a n k * X k`.  Their total variance is
the sum of coefficient squares.  The third absolute moment sum is
`E|X|³ * ∑ |a n k|³`, which tends to zero.  Hence the Lyapunov condition holds, and the
triangular-array CLT gives a standard Gaussian limit.  See
<https://en.wikipedia.org/wiki/Central_limit_theorem#Lyapunov_CLT>.

This theorem is deferred because the pinned Mathlib CLT is i.i.d. with equal coefficients and does
not yet expose a triangular-array Lyapunov theorem. -/
theorem tendstoInDistribution_weightedPreactivation [IsProbabilityMeasure P]
    (I : IIDScalarInitialization Ω P) (a : ℕ → ℕ → ℝ)
    (h3 : Integrable (fun ω => |I.weight 0 ω| ^ 3) P)
    (hvariance : Tendsto (fun n => ∑ k ∈ Finset.range n, (a n k) ^ 2)
      atTop (nhds 1))
    (hlyapunov : Tendsto (fun n => ∑ k ∈ Finset.range n, |a n k| ^ 3)
      atTop (nhds 0))
    {ΩG : Type uΩG} [MeasurableSpace ΩG] {PG : Measure ΩG} [IsProbabilityMeasure PG]
    {Z : ΩG → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) PG) :
    TendstoInDistribution (I.weightedPreactivation a) atTop Z (fun _ => P) PG := by
  sorry

/-- Berry--Esseen bound for normalized i.i.d. preactivations.

Informal proof: expand the normalized preactivation as `n` independent centered unit-variance
summands divided by `sqrt n` and apply the classical Berry--Esseen theorem.  Its numerator is the
sum of third absolute moments, `n ρ`, and its variance normalization contributes `n^(3/2)`, leaving
`ρ / sqrt n`.  See the statement and proof references at
<https://en.wikipedia.org/wiki/Berry%E2%80%93Esseen_theorem>.

This result is deferred because Mathlib currently supplies the qualitative CLT but no
Berry--Esseen theorem.  Crucially, the conclusion is `O(n⁻¹/²)`, not `O(n⁻¹)`. -/
theorem berryEsseen_normalizedPreactivation [IsProbabilityMeasure P]
    (I : IIDScalarInitialization Ω P) (h3 : Integrable (fun ω => |I.weight 0 ω| ^ 3) P) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ z : ℝ,
      |P.real {ω | I.normalizedPreactivation n ω ≤ z} -
          (gaussianReal 0 1).real (Set.Iic z)| ≤
        C * (∫ ω, |I.weight 0 ω| ^ 3 ∂P) / Real.sqrt n := by
  sorry

/-- Exact inverse-width correction to the fourth moment.

Informal proof: expand `(sum Xᵢ)^4`.  Centering kills every monomial containing an index exactly
once.  The surviving terms are the `n` fourth powers and the `6 * choose(n,2)` products
`Xᵢ² Xⱼ²`.  Independence factors the latter expectations, and the unit second moment makes each
equal to one.  Division by `n²` gives `3 + (E[X⁴] - 3) / n`.  See, for example, the elementary
fourth-moment expansion in
<https://en.wikipedia.org/wiki/Kurtosis#Pearson_moments>.

The proof is deferred pending a reusable finite-sum moment expansion API; the hypotheses and the
claimed `1 / n` scope are fully explicit. -/
theorem fourthMoment_normalizedPreactivation [IsProbabilityMeasure P]
    (I : IIDScalarInitialization Ω P) (h4 : MemLp (I.weight 0) 4 P)
    (n : ℕ) (hn : 0 < n) :
    (∫ ω, I.normalizedPreactivation n ω ^ 4 ∂P) =
      3 + ((∫ ω, I.weight 0 ω ^ 4 ∂P) - 3) / n := by
  sorry

/-- Matching first two moments yield an exact inverse-width difference for fourth moments.  This
is a valid selected-moment version of the chapter's `1 / width` heuristic. -/
theorem fourthMoment_difference_eq_div_width
    {Ω' : Type uΩ'} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (I : IIDScalarInitialization Ω P) (J : IIDScalarInitialization Ω' P')
    (hI4 : MemLp (I.weight 0) 4 P) (hJ4 : MemLp (J.weight 0) 4 P')
    (n : ℕ) (hn : 0 < n) :
    (∫ ω, I.normalizedPreactivation n ω ^ 4 ∂P) -
        (∫ ω, J.normalizedPreactivation n ω ^ 4 ∂P') =
      ((∫ ω, I.weight 0 ω ^ 4 ∂P) - (∫ ω, J.weight 0 ω ^ 4 ∂P')) / n := by
  rw [I.fourthMoment_normalizedPreactivation hI4 n hn,
    J.fourthMoment_normalizedPreactivation hJ4 n hn]
  ring

end IIDScalarInitialization

end NeuralNetwork

end

end
