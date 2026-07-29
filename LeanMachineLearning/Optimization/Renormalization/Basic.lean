/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Finpartition
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Probability.Moments.Basic

/-!
# Joint moments and centering

This file defines finite joint moments independently of cumulants and Gaussianity.  Indexing by an
arbitrary finite type keeps repeated observables distinct and makes reindexing explicit.

The external declarations used here are verified in `Renormalization/APIAudit.lean`.

Deferred proof reference: Mathlib's Bochner-integral API is documented in
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner/Basic.html>.
Every deferred theorem below also gives its informal proof.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace Renormalization

variable {Ω ι κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The moment of the observables indexed by a finite block `B`. -/
def blockMoment (μ : Measure Ω) (X : ι → Ω → ℝ) (B : Finset ι) : ℝ :=
  ∫ ω, ∏ i ∈ B, X i ω ∂μ

/-- The joint moment of a family indexed by a finite type. -/
def jointMoment [Fintype ι] (μ : Measure Ω) (X : ι → Ω → ℝ) : ℝ :=
  blockMoment μ X Finset.univ

/-- All finite products drawn from `X` are integrable.  This is the reusable hypothesis for
multilinearity and independence arguments. -/
def HasFiniteJointMoments (μ : Measure Ω) (X : ι → Ω → ℝ) : Prop :=
  ∀ B : Finset ι, Integrable (fun ω ↦ ∏ i ∈ B, X i ω) μ

/-- The centered version of a real-valued observable. -/
def center (μ : Measure Ω) (X : Ω → ℝ) : Ω → ℝ :=
  fun ω ↦ X ω - ∫ x, X x ∂μ

/-- The empty joint moment is one under a probability measure.

Informal proof: the product over `Fin 0` is the constant one function, whose integral is the mass
of the whole space; that mass is one for a probability measure. -/
@[simp]
theorem jointMoment_zero [IsProbabilityMeasure μ] (X : Fin 0 → Ω → ℝ) :
    jointMoment μ X = 1 := by
  dsimp [jointMoment, blockMoment]
  simp

/-- A one-variable joint moment is its expectation.

Informal proof: `Finset.univ : Finset (Fin 1)` is the singleton containing `0`, so its product
reduces to `X 0`. -/
theorem jointMoment_one (X : Fin 1 → Ω → ℝ) :
    jointMoment μ X = ∫ ω, X 0 ω ∂μ := by
  dsimp [jointMoment, blockMoment]
  simp

/-- Reindexing a joint moment by an equivalence does not change it.

Informal proof: map `Finset.univ` along `e`, use `Finset.prod_equiv`, and observe that the two
integrands agree pointwise. -/
theorem jointMoment_perm [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (X : ι → Ω → ℝ) :
    jointMoment μ (fun j ↦ X (e.symm j)) = jointMoment μ X := by
  dsimp [jointMoment, blockMoment]
  congr 1
  ext ω
  exact Finset.prod_equiv e.symm (by simp) (by simp)

/-- Replacing every observable by an almost-everywhere equal one preserves the joint moment.

Informal proof: intersect the finitely many full-measure sets on which `X i = Y i`; on that
intersection the finite products, hence their integrals, agree. -/
theorem jointMoment_congr_ae [Fintype ι] {X Y : ι → Ω → ℝ}
    (hXY : ∀ i, X i =ᵐ[μ] Y i) :
    jointMoment μ X = jointMoment μ Y := by
  dsimp [jointMoment, blockMoment]
  apply MeasureTheory.integral_congr_ae
  have h : ∀ᵐ ω ∂μ, ∀ i, X i ω = Y i ω := ae_all_iff.mpr hXY
  filter_upwards [h] with ω hω
  apply Finset.prod_congr rfl
  intro i _
  exact hω i

/-- An integrable observable has centered expectation zero.

Informal proof: split the integral of the difference, integrate the constant using the probability
mass one, and cancel the two copies of the expectation. -/
theorem integral_center [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Integrable X μ) :
    ∫ ω, center μ X ω ∂μ = 0 := by
  dsimp [center]
  have h_const : Integrable (fun _ : Ω ↦ ∫ x, X x ∂μ) μ := integrable_const _
  rw [integral_sub hX h_const]
  simp [integral_const]

/-- An integrable odd observable has integral zero against a negation-invariant measure.

Informal proof: `Measure.measurePreserving_neg` changes variables by `x ↦ -x`.  Oddness makes the
transformed integral the negative of the original, so the original equals zero. -/
theorem integral_eq_zero_of_odd {E : Type*} [MeasurableSpace E] [Neg E] [MeasurableNeg E]
    (ν : Measure E) [ν.IsNegInvariant] {F : E → ℝ} (hF : Integrable F ν)
    (hodd : ∀ x, F (-x) = -F x) :
    ∫ x, F x ∂ν = 0 := by
  have h1 : ∫ x, F x ∂ν = ∫ x, F (-x) ∂ν := by
    have h_map : ν = Measure.map (fun x ↦ -x) ν := (Measure.measurePreserving_neg ν).map_eq.symm
    nth_rw 1 [h_map]
    have hfm : AEStronglyMeasurable F (Measure.map (fun x ↦ -x) ν) := by
      rw [← h_map]
      exact hF.1
    rw [MeasureTheory.integral_map measurable_neg.aemeasurable hfm]
  have h2 : ∫ x, F (-x) ∂ν = - ∫ x, F x ∂ν := by
    simp_rw [hodd]
    exact integral_neg F
  rw [h2] at h1
  linarith

end Renormalization

end

end
