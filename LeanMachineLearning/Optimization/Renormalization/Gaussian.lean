/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Cumulant
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Wick calculus for Gaussian measures

This file defines a canonical pairing sum and states scalar, coordinate-free, and coordinate Wick
formulae.  The coordinate-free theorem is primary; the multivariate-coordinate theorem and the
sixth-moment theorem are direct specializations.

Deferred proof references:

* L. Isserlis, *On a Formula for the Product-Moment Coefficient of any Order of a Normal Frequency
  Distribution in any Number of Variables*: <https://doi.org/10.1093/biomet/12.1-2.134>.
* Mathlib's Gaussian MGF and `IsGaussian` API:
  <https://github.com/leanprover-community/mathlib4/tree/abb22825db7e020c94f38a007ae3fffe6c3a7532/Mathlib/Probability/Distributions/Gaussian>.

Every deferred theorem below includes its own informal proof.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Renormalization

variable {ι : Type*} [DecidableEq ι]

/-- The canonical weight of an unordered two-element block for a covariance kernel.  Averaging the
two orientations avoids choosing an order on the index type. -/
def pairWeight (C : ι → ι → ℝ) (B : Finset ι) : ℝ :=
  (∑ i ∈ B, ∑ j ∈ B.erase i, C i j) / 2

/-- The Wick sum of a covariance kernel over all pairings of `s`. -/
def wick (C : ι → ι → ℝ) (s : Finset ι) : ℝ :=
  Finpartition.pairingSum (pairWeight C) s

/-- A Wick sum on an odd-cardinality set vanishes.

Informal proof: `Finpartition.Pairing.isEmpty_of_odd_card` says the indexing type of the sum is
empty, so the finite sum is zero. -/
theorem wick_eq_zero_of_odd_card (C : ι → ι → ℝ) (s : Finset ι) (hs : Odd s.card) :
    wick C s = 0 := by
  sorry

/-- Pairing recurrence obtained by choosing the partner of a distinguished element.

Informal proof: use `Pairing.existsUnique_partner` to decompose every pairing uniquely into the
pair `{a,b}` and a pairing of `(s.erase a).erase b`.  Symmetry identifies the canonical averaged
block weight with `C a b`.  This is the standard recursive proof of Isserlis' theorem. -/
theorem wick_erase (C : ι → ι → ℝ) (hC : ∀ i j, C i j = C j i)
    (s : Finset ι) {a : ι} (ha : a ∈ s) :
    wick C s = ∑ b ∈ s.erase a, C a b * wick C ((s.erase a).erase b) := by
  sorry

/-! ## Scalar Gaussian moments -/

/-- Odd moments of a centered real Gaussian vanish.

Informal proof: `mgf_fun_id_gaussianReal` identifies the MGF with `exp (v t² / 2)`; its odd Taylor
coefficients are zero, and `iteratedDeriv_mgf_zero` identifies those coefficients with moments. -/
theorem moment_id_gaussianReal_zero_odd (v : ℝ≥0) (m : ℕ) :
    ∫ x, x ^ (2 * m + 1) ∂gaussianReal 0 v = 0 := by
  sorry

/-- Exact even moments of a centered real Gaussian.

Informal proof: differentiate `exp (v t² / 2)` recursively.  At zero only the term using `m`
quadratic factors remains, giving `(2m)! / (2^m m!) * v^m`; use
`iteratedDeriv_mgf_zero` to return to the integral. -/
theorem moment_id_gaussianReal_zero_even (v : ℝ≥0) (m : ℕ) :
    ∫ x, x ^ (2 * m) ∂gaussianReal 0 v =
      ((2 * m).factorial : ℝ) / ((2 : ℝ) ^ m * (m.factorial : ℝ)) * (v : ℝ) ^ m := by
  sorry

/-! ## Coordinate-free Wick theorem -/

/-- Center a continuous linear functional under `μ`. -/
def centeredDual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (μ : Measure E) (L : StrongDual ℝ E) : E → ℝ :=
  fun x ↦ L x - ∫ y, L y ∂μ

/-- Covariance kernel of two continuous linear functionals. -/
def dualCovariance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) (L K : StrongDual ℝ E) : ℝ :=
  covariance (fun x ↦ L x) (fun x ↦ K x) μ

namespace IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Coordinate-free Wick theorem for centered continuous linear observables.

Informal proof: every linear combination `∑ i, t i • L i` has a one-dimensional Gaussian
pushforward by `ProbabilityTheory.IsGaussian.map_eq_gaussianReal`.  Its centered MGF is therefore
the exponential of the quadratic covariance form.  Comparing finite multivariate coefficients
and using `wick_erase` yields the pairing recurrence and hence the formula.  All products are
integrable by `ProbabilityTheory.IsGaussian.memLp_dual` and finite Hölder. -/
theorem integral_prod_centered_dual_eq_wick (μ : Measure E) [ProbabilityTheory.IsGaussian μ]
    {n : ℕ} (L : Fin n → StrongDual ℝ E) :
    jointMoment μ (fun i ↦ centeredDual μ (L i)) =
      wick (fun i j ↦ dualCovariance μ (L i) (L j)) Finset.univ := by
  sorry

/-- The sixth centered Gaussian moment is one application of the general Wick theorem. -/
theorem sixthMoment_centered_dual_eq_wick (μ : Measure E) [ProbabilityTheory.IsGaussian μ]
    (L : Fin 6 → StrongDual ℝ E) :
    jointMoment μ (fun i ↦ centeredDual μ (L i)) =
      wick (fun i j ↦ dualCovariance μ (L i) (L j)) Finset.univ :=
  integral_prod_centered_dual_eq_wick μ L

/-- The centered second joint cumulant of Gaussian linear observables is their covariance.

Informal proof: apply `jointCumulant_two_eq_covariance`; Gaussian dual observables lie in every
finite `L^p` by `IsGaussian.memLp_dual`. -/
theorem jointCumulant_two_centered_dual (μ : Measure E) [ProbabilityTheory.IsGaussian μ]
    (L : Fin 2 → StrongDual ℝ E) :
    jointCumulant μ (fun i ↦ centeredDual μ (L i)) = dualCovariance μ (L 0) (L 1) := by
  sorry

/-- Centered Gaussian cumulants vanish in every order other than two.

Informal proof: combine the moment--cumulant identity with the coordinate-free Wick theorem.
Wick moments contain only pair blocks, so Möbius inversion leaves a connected contribution only
when the full index set itself is a pair. -/
theorem jointCumulant_centered_dual_eq_zero (μ : Measure E)
    [ProbabilityTheory.IsGaussian μ] {n : ℕ} (hn : n ≠ 2)
    (L : Fin n → StrongDual ℝ E) :
    jointCumulant μ (fun i ↦ centeredDual μ (L i)) = 0 := by
  sorry

/-- Noncentered Gaussian linear observables have no cumulants above order two.

Informal proof: adding constants changes only the first cumulant.  Center every `L i`, apply
multilinearity and the preceding centered theorem, and use `2 < n`. -/
theorem jointCumulant_dual_eq_zero (μ : Measure E) [ProbabilityTheory.IsGaussian μ]
    {n : ℕ} (hn : 2 < n) (L : Fin n → StrongDual ℝ E) :
    jointCumulant μ (fun i x ↦ L i x) = 0 := by
  sorry

end IsGaussian

/-! ## Multivariate Gaussian coordinates -/

/-- Wick theorem for repeated coordinates of a multivariate Gaussian.

Informal proof: specialize the coordinate-free theorem to coordinate projections.  Rewrite their
means with `integral_id_multivariateGaussian` and their covariances with
`covariance_eval_multivariateGaussian hS`. -/
theorem integral_prod_multivariateGaussian_centered_eq_wick
    {κ : Type*} [Fintype κ] [DecidableEq κ] {n : ℕ}
    (m : EuclideanSpace ℝ κ) (S : Matrix κ κ ℝ) (hS : S.PosSemidef)
    (index : Fin n → κ) :
    jointMoment (multivariateGaussian m S)
        (fun r z ↦ z (index r) - m (index r)) =
      wick (fun r q ↦ S (index r) (index q)) Finset.univ := by
  sorry

end Renormalization

end

end
