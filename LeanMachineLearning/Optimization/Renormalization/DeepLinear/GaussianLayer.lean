/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.DeepLinear.Basic
public import LeanMachineLearning.Optimization.Renormalization.Gaussian

/-!
# One Gaussian layer of a deep linear network

The public API in this file isolates the radial calculation used by every finite-width moment
formula.  In particular, downstream files need not re-expand Gaussian coordinates or pairings.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace NeuralNetwork.DeepLinear

universe uA uI uJ

/-- The coefficient `(2m)! / (2^m m!)` in the `2m`-th centered Gaussian moment. -/
def gaussianEvenCoeff (m : ℕ) : ℝ :=
  ((2 * m).factorial : ℝ) / ((2 : ℝ) ^ m * (m.factorial : ℝ))

/-- The exact finite-width correction for the `m`-th moment of normalized Gaussian energy. -/
def widthMomentFactor (m n : ℕ) : ℝ :=
  ∏ s ∈ Finset.range m, (1 + (2 * s : ℝ) / (n : ℝ))

@[simp] theorem widthMomentFactor_zero (n : ℕ) : widthMomentFactor 0 n = 1 := by
  simp [widthMomentFactor]

@[simp] theorem widthMomentFactor_one (n : ℕ) : widthMomentFactor 1 n = 1 := by
  simp [widthMomentFactor]

theorem widthMomentFactor_two (n : ℕ) :
    widthMomentFactor 2 n = 1 + 2 / (n : ℝ) := by
  norm_num [widthMomentFactor, Finset.prod_range_succ]

theorem widthMomentFactor_three (n : ℕ) :
    widthMomentFactor 3 n = (1 + 2 / (n : ℝ)) * (1 + 4 / (n : ℝ)) := by
  norm_num [widthMomentFactor, Finset.prod_range_succ]

/-- The product law of `n` independent standard real Gaussians. -/
def standardGaussianVectorLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => gaussianReal 0 1

/-- Output law of one freshly initialized bias-free linear layer. -/
def oneLayerOutputLaw {ι : Type uI} {κ : Type uJ} [Fintype ι] [Fintype κ]
    (Cw : ℝ≥0) (x : ι → ℝ) : Measure (κ → ℝ) :=
  Measure.map (fun q : LayerParams ι κ => (DenseLayer.ofParams q).preactivation x)
    (layerGaussianInit (hyperparams Cw) ι κ)

/-- A bias-free initialized layer is a product of centered multivariate Gaussians across output
neurons.

Informal proof: specialize `map_evalBatch_layerGaussianInit`; the bias term vanishes and
`layerCovariance_eq_bias_add_weight_mul_normalizedGram` identifies its covariance with
`Cw • normalizedGram x`.  Independence of rows is already built into that theorem.  Source:
`docs/Renormalization.md`, equation `eq:two-point-function-deep-linear-layer-ell`, and Mathlib's
multivariate Gaussian API at
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Gaussian/Multivariate.html>.
-/
theorem map_batchPreactivation
    {A : Type uA} {ι : Type uI} {κ : Type uJ}
    [Fintype ι] [Fintype κ] [Fintype A] [DecidableEq A]
    (Cw : ℝ≥0) (x : A → ι → ℝ) :
    Measure.map
        (fun q : LayerParams ι κ => fun j => batchToEuclidean (batchPreactivation q x) j)
        (layerGaussianInit (hyperparams Cw) ι κ) =
      Measure.pi (fun _ : κ =>
        multivariateGaussian 0 (fun a b => (Cw : ℝ) * NeuralNetwork.normalizedGram x a b)) := by
  simpa only [NeuralNetwork.layerCovariance_eq_bias_add_weight_mul_normalizedGram,
    hyperparams_biasVariance, hyperparams_weightVariance, NNReal.coe_zero, zero_add] using
    map_evalBatch_layerGaussianInit (p := hyperparams Cw) x

/-- Even-moment recurrence for a standard one-dimensional Gaussian:
`∫ z, z ^ (2 * (a + 1)) = (2a + 1) * ∫ z, z ^ (2 * a)`.

This is the one-coordinate instance of the chi-square recursion used below in
`integral_sumSq_pow_stdGaussian_succ`.  It follows directly from
`Renormalization.integral_mul_pow_gaussianReal` (Stein's lemma for monomials). -/
private lemma integral_pow_two_mul_succ_stdGaussian (a : ℕ) :
    ∫ u : ℝ, u ^ (2 * (a + 1)) ∂gaussianReal 0 1 =
      (2 * (a : ℝ) + 1) * ∫ u : ℝ, u ^ (2 * a) ∂gaussianReal 0 1 := by
  calc
    ∫ u : ℝ, u ^ (2 * (a + 1)) ∂gaussianReal 0 1
        = ∫ u : ℝ, u ^ (2 * a + 2) ∂gaussianReal 0 1 := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with u
            rw [show 2 * (a + 1) = 2 * a + 2 by omega]
    _ = ∫ u : ℝ, u * u ^ (2 * a + 1) ∂gaussianReal 0 1 := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with u
            rw [show 2 * a + 2 = (2 * a + 1) + 1 by omega]
            rw [pow_succ']
    _ = (1 : ℝ) * ((2 * a + 1 : ℕ) : ℝ) *
          ∫ u : ℝ, u ^ (2 * a + 1 - 1) ∂gaussianReal 0 1 := by
            exact Renormalization.integral_mul_pow_gaussianReal 1 (2 * a + 1)
    _ = (2 * (a : ℝ) + 1) * ∫ u : ℝ, u ^ (2 * a + 1 - 1) ∂gaussianReal 0 1 := by
            norm_num
    _ = (2 * (a : ℝ) + 1) * ∫ u : ℝ, u ^ (2 * a) ∂gaussianReal 0 1 := by
            rw [show 2 * a + 1 - 1 = 2 * a by omega]

/-- Closed form for the raw moments of the squared Euclidean norm of a standard Gaussian vector.

This is the chi-square moment formula.  If `g` has law `standardGaussianVectorLaw n`, then
`∑ i, g i ^ 2` has the chi-square distribution with `n` degrees of freedom, whose `m`-th raw
moment is `∏ s<m (n + 2s)`.

Informal proof: expand `(∑ i, g i ^ 2)^m` by the multinomial theorem.  Each monomial factors,
under `Measure.pi`, into a product of one-dimensional even Gaussian moments; those moments are
computed by `Renormalization.integral_pow_gaussianReal_even` (or recursively by
`integral_pow_two_mul_succ_stdGaussian`).  Recombining the multinomial coefficients gives the
standard chi-square product.  Equivalently, the moment generating function of the sum of `n`
independent squares is `(1 - 2t)^{-n/2}`, whose Taylor coefficients are the displayed product;
see <https://en.wikipedia.org/wiki/Chi-squared_distribution#Moments>. -/
private lemma integral_sumSq_pow_stdGaussian_closed_form (m n : ℕ) :
    ∫ g : Fin n → ℝ, ((∑ i, g i ^ 2) ^ m) ∂standardGaussianVectorLaw n =
      ∏ s ∈ Finset.range m, ((n : ℝ) + 2 * s) := by
  sorry

private lemma integral_sumSq_pow_stdGaussian_succ (k n : ℕ) :
    ∫ g : Fin n → ℝ, ((∑ i, g i ^ 2) ^ (k + 1)) ∂standardGaussianVectorLaw n =
      ((n : ℝ) + 2 * k) *
        ∫ g : Fin n → ℝ, ((∑ i, g i ^ 2) ^ k) ∂standardGaussianVectorLaw n := by
  calc
    ∫ g : Fin n → ℝ, ((∑ i, g i ^ 2) ^ (k + 1)) ∂standardGaussianVectorLaw n
        = ∏ s ∈ Finset.range (k + 1), ((n : ℝ) + 2 * s) := by
          exact integral_sumSq_pow_stdGaussian_closed_form (k + 1) n
    _ = ((n : ℝ) + 2 * k) *
          (∏ s ∈ Finset.range k, ((n : ℝ) + 2 * s)) := by
          rw [Finset.prod_range_succ]
          ring
    _ = ((n : ℝ) + 2 * k) *
          ∫ g : Fin n → ℝ, ((∑ i, g i ^ 2) ^ k) ∂standardGaussianVectorLaw n := by
          rw [integral_sumSq_pow_stdGaussian_closed_form k n]

/-- Unnormalized chi-square moments for the squared norm of a standard Gaussian vector.

Informal proof: write `X g = ∑ i, g i ^ 2`.  The Gaussian integration-by-parts/Stein identity
for one coordinate, applied to `z * (z^2 + R)^k` while holding the other coordinates fixed, gives
`∫ X^(k+1) = ((n : ℝ) + 2*k) * ∫ X^k`.  The base case is the integral of the constant `1` under a
probability measure.  Induction over `k` then gives the product formula below.  This is exactly the
standard moment formula for a chi-square random variable with `n` degrees of freedom; see
<https://en.wikipedia.org/wiki/Chi-squared_distribution#Moments>.  A complete formal proof should
combine `Renormalization.integral_mul_pow_gaussianReal` with finite-product Fubini for
`Measure.pi`.
-/
theorem integral_sumSq_pow_stdGaussian (m n : ℕ) :
    ∫ g : Fin n → ℝ, ((∑ i, g i ^ 2) ^ m) ∂standardGaussianVectorLaw n =
      ∏ s ∈ Finset.range m, ((n : ℝ) + 2 * s) := by
  induction m with
  | zero =>
      simp [standardGaussianVectorLaw]
  | succ k ih =>
      calc
        ∫ g : Fin n → ℝ, ((∑ i, g i ^ 2) ^ (k + 1)) ∂standardGaussianVectorLaw n
            = ((n : ℝ) + 2 * k) *
                ∫ g : Fin n → ℝ, ((∑ i, g i ^ 2) ^ k) ∂standardGaussianVectorLaw n := by
              exact integral_sumSq_pow_stdGaussian_succ k n
        _ = ((n : ℝ) + 2 * k) *
              (∏ s ∈ Finset.range k, ((n : ℝ) + 2 * s)) := by
              rw [ih]
        _ = ∏ s ∈ Finset.range (k + 1), ((n : ℝ) + 2 * s) := by
              rw [Finset.prod_range_succ]
              ring

private lemma normalized_chiSquare_product_algebra (m n : ℕ) (hn : 0 < n) :
    ((n : ℝ)⁻¹) ^ m * (∏ s ∈ Finset.range m, ((n : ℝ) + 2 * s)) =
      widthMomentFactor m n := by
  classical
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold widthMomentFactor
  calc
    ((n : ℝ)⁻¹) ^ m * (∏ s ∈ Finset.range m, ((n : ℝ) + 2 * s))
        = (∏ _s ∈ Finset.range m, (n : ℝ)⁻¹) *
            (∏ s ∈ Finset.range m, ((n : ℝ) + 2 * s)) := by
          simp [Finset.prod_const]
    _ = ∏ s ∈ Finset.range m, ((n : ℝ)⁻¹ * ((n : ℝ) + 2 * s)) := by
          rw [Finset.prod_mul_distrib]
    _ = ∏ s ∈ Finset.range m, (1 + (2 * s : ℝ) / (n : ℝ)) := by
          refine Finset.prod_congr rfl ?_
          intro s hs
          field_simp [hn_ne]

/-- Moment formula for the empirical mean of squares of an independent standard Gaussian vector.

This is the radial analytic core used by `integral_normalizedEnergy_pow_stdGaussian`.  In informal
terms, if `X g = ∑ i, g i ^ 2`, then the Gaussian integration-by-parts recurrence gives
`E[X^(m+1)] = ((n : ℝ) + 2 * m) * E[X^m]`; with `E[X^0] = 1`, this yields
`E[X^m] = ∏ s<m ((n : ℝ) + 2*s)`.  Multiplying by `(n : ℝ)⁻¹` inside the `m`-th power gives the
stated product `∏ s<m (1 + 2*s/n)`.  This is also the standard chi-square moment formula; see
<https://en.wikipedia.org/wiki/Chi-squared_distribution#Moments>.  A full Lean proof should derive
the recurrence using the local one-dimensional Stein identity
`Renormalization.integral_mul_pow_gaussianReal` and finite-product Fubini.
-/
theorem integral_normalizedSumSq_pow_stdGaussian (m n : ℕ) (hn : 0 < n) :
    ∫ g : Fin n → ℝ, (((n : ℝ)⁻¹ * ∑ i, g i ^ 2) ^ m) ∂standardGaussianVectorLaw n =
      widthMomentFactor m n := by
  calc
    ∫ g : Fin n → ℝ, (((n : ℝ)⁻¹ * ∑ i, g i ^ 2) ^ m) ∂standardGaussianVectorLaw n
        = ((n : ℝ)⁻¹) ^ m *
            ∫ g : Fin n → ℝ, ((∑ i, g i ^ 2) ^ m) ∂standardGaussianVectorLaw n := by
          simp_rw [mul_pow]
          rw [MeasureTheory.integral_const_mul]
    _ = ((n : ℝ)⁻¹) ^ m * (∏ s ∈ Finset.range m, ((n : ℝ) + 2 * s)) := by
          rw [integral_sumSq_pow_stdGaussian]
    _ = widthMomentFactor m n := normalized_chiSquare_product_algebra m n hn

/-- Exact moments of normalized energy under an independent standard Gaussian vector.

Informal proof: `n * normalizedEnergy g` has the chi-square distribution with `n` degrees of
freedom.  Its `m`-th moment is `∏ s<m (n+2s)`; division by `n^m` gives the stated product.  A Lean
proof can instead induct using Gaussian integration by parts and
`Renormalization.integral_pow_gaussianReal_even`.  Source:
<https://en.wikipedia.org/wiki/Chi-squared_distribution#Moments>.
-/
theorem integral_normalizedEnergy_pow_stdGaussian (m n : ℕ) (hn : 0 < n) :
    ∫ g, NeuralNetwork.normalizedEnergy g ^ m ∂standardGaussianVectorLaw n =
      widthMomentFactor m n := by
  simpa [NeuralNetwork.normalizedEnergy, Fintype.card_fin] using
    integral_normalizedSumSq_pow_stdGaussian m n hn

/-- One freshly initialized layer multiplies the `m`-th normalized-energy moment by
`(Cw * Q(x))^m c_{2m}(n)`.

Informal proof: conditional on `x`, every output is `sqrt(Cw * Q(x))` times an independent
standard Gaussian.  Pull this common scale through normalized energy and apply
`integral_normalizedEnergy_pow_stdGaussian`.  Source: `docs/Renormalization.md`, the radial
recursion leading to equation `eq:deep-linear-2m-point-function`.
-/
theorem integral_normalizedEnergy_pow_randomLayerKernel
    {ι : Type uI} {κ : Type uJ} [Fintype ι] [Fintype κ]
    (Cw : ℝ≥0) (x : ι → ℝ) (m : ℕ) (hκ : 0 < Fintype.card κ) :
    ∫ z : κ → ℝ, NeuralNetwork.normalizedEnergy z ^ m
        ∂oneLayerOutputLaw (ι := ι) (κ := κ) Cw x =
      ((Cw : ℝ) * NeuralNetwork.normalizedEnergy x) ^ m *
        widthMomentFactor m (Fintype.card κ) := by
  sorry

end NeuralNetwork.DeepLinear

end

end
