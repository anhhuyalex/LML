/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Cumulant
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Expectations and moment expansions

This file gives the physics vocabulary of an expectation value a small, representation-independent
API.  It also states the rigorous form of “Taylor-expand an observable and take expectations”: the
termwise identity assumes an actual pointwise expansion and an absolute-integrability condition.
It therefore does not repeat the source's unjustified claim that arbitrary laws are determined by
their moments.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Renormalization

universe uΩ uE uI

/-- The expectation of a Banach-valued observable. -/
def expectation {Ω : Type uΩ} {E : Type uE} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure Ω) (O : Ω → E) : E :=
  ∫ x, O x ∂μ

@[simp] theorem expectation_eq_integral {Ω : Type uΩ} {E : Type uE} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure Ω) (O : Ω → E) :
    expectation μ O = ∫ x, O x ∂μ := rfl

/-- A coordinate monomial with repetitions specified by `index`. -/
def coordinateMonomial {ι : Type uI} {n : ℕ} (index : Fin n → ι)
    (z : EuclideanSpace ℝ ι) : ℝ :=
  ∏ r, z (index r)

/-- The homogeneous degree-`n` term determined by a coefficient tensor. -/
def homogeneousObservable {ι : Type uI} [Fintype ι]
    (n : ℕ) (c : (Fin n → ι) → ℝ) (z : EuclideanSpace ℝ ι) : ℝ :=
  ∑ index : Fin n → ι, c index * coordinateMonomial index z

-- The integral of a homogeneous observable is the weighted finite sum of the joint moments of
-- its coordinate monomials.  Linearity of the Bochner integral distributes the finite sum and the
-- scalar factors, and the remaining monomial integral is `jointMoment` by definition.
-- Used for each degree `n` in `expectation_eq_tsum_jointMoments_of_expansion`.
private lemma integral_homogeneousObservable_eq_sum {ι : Type uI} [Fintype ι]
    (μ : Measure (EuclideanSpace ℝ ι)) (n : ℕ) (c : (Fin n → ι) → ℝ)
    (hcoord_int : ∀ index : Fin n → ι, Integrable (coordinateMonomial index) μ) :
    ∫ z, homogeneousObservable n c z ∂μ =
      ∑ index : Fin n → ι,
        c index * jointMoment μ (fun r : Fin n => fun z => z (index r)) := by
  unfold homogeneousObservable jointMoment blockMoment coordinateMonomial
  rw [integral_finsetSum Finset.univ]
  · exact Finset.sum_congr rfl (fun index _ => by rw [integral_const_mul])
  · exact fun index _ => (hcoord_int index).const_mul (c index)

/-- Expectation of a convergent coordinate Taylor expansion is the corresponding series of joint
moments.

The hypotheses are intentionally analytic rather than merely formal: `hexpansion` supplies the
pointwise series, `hmeas` supplies measurability of every homogeneous term, and `habs` is the
Tonelli/dominated-convergence condition allowing the integral and infinite sum to be exchanged.

Informal proof: substitute `hexpansion`, use the Bochner integral theorem for an absolutely
summable series, distribute each finite coordinate sum through the integral, and identify the
integral of a coordinate monomial with `jointMoment`.  Source: equation
`eq:observables-and-moments` in `docs/Renormalization.md`; the required interchange theorem is
documented at
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner/Basic.html>.
-/
theorem expectation_eq_tsum_jointMoments_of_expansion
    {ι : Type uI} [Fintype ι]
    (μ : Measure (EuclideanSpace ℝ ι)) (O : EuclideanSpace ℝ ι → ℝ)
    (c : (n : ℕ) → (Fin n → ι) → ℝ)
    (hexpansion : ∀ z, O z = ∑' n, homogeneousObservable n (c n) z)
    (hcoord_int : ∀ n (index : Fin n → ι), Integrable (coordinateMonomial index) μ)
    (hint : ∀ n, Integrable (homogeneousObservable n (c n)) μ)
    (habs : Summable fun n => ∫ z, ‖homogeneousObservable n (c n) z‖ ∂μ) :
    expectation μ O =
      ∑' n, ∑ index : Fin n → ι,
        c n index * jointMoment μ (fun r : Fin n => fun z => z (index r)) := by
  rw [expectation_eq_integral,
    integral_congr_ae (.of_forall hexpansion),
    (integral_tsum_of_summable_integral_norm hint habs).symm,
    tsum_congr fun n => integral_homogeneousObservable_eq_sum μ n (c n) (hcoord_int n)]

end Renormalization

end

end
