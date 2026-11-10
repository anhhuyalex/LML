/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.Moments.Variance

/-!
# Integrals of positive semidefinite matrices

The entrywise integral of an integrable family of real positive semidefinite matrices is positive
semidefinite.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace Matrix

/-- **The entrywise integral of positive semidefinite matrices is positive semidefinite.** -/
theorem posSemidef_integral_of_posSemidef {ι Ω : Type*} [Finite ι] [MeasurableSpace Ω]
    (lam : Measure Ω) (C : Ω → Matrix ι ι ℝ) (hC : ∀ ω, (C ω).PosSemidef)
    (hint : ∀ u v, Integrable (fun ω => C ω u v) lam) :
    (Matrix.of fun u v => ∫ ω, C ω u v ∂lam).PosSemidef := by
  classical
  have := Fintype.ofFinite ι
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext u v
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by
      have := (hC ω).isHermitian.apply u v
      simpa using this)
  · have h : star x ⬝ᵥ (Matrix.of fun u v => ∫ ω, C ω u v ∂lam) *ᵥ x =
        ∫ ω, star x ⬝ᵥ C ω *ᵥ x ∂lam := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
      have hi : ∀ u v, Integrable (fun ω => star x u * (C ω u v * x v)) lam := fun u v =>
        ((hint u v).mul_const (x v)).const_mul (star x u) |>.congr
          (Filter.Eventually.of_forall fun ω => by simp)
      simp_rw [Finset.mul_sum]
      rw [integral_finsetSum Finset.univ fun u _ => integrable_finsetSum _ fun v _ => hi u v]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [integral_finsetSum Finset.univ fun v _ => hi u v]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [integral_const_mul, integral_mul_const]
    rw [h]
    exact integral_nonneg fun ω => (hC ω).dotProduct_mulVec_nonneg x

/-- **The covariance matrix of bounded measurable functions is positive semidefinite.** -/
theorem posSemidef_covariance_of_bounded {ι α : Type*} [Finite ι] [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (g : ι → α → ℝ) (hg : ∀ u, Measurable (g u))
    {B : ℝ} (hB : ∀ u a, |g u a| ≤ B) :
    (Matrix.of fun u v => ∫ a, g u a * g v a ∂ν - (∫ a, g u a ∂ν) * ∫ a, g v a ∂ν).PosSemidef := by
  classical
  have := Fintype.ofFinite ι
  have hi : ∀ u, Integrable (g u) ν := fun u =>
    (integrable_const B).mono' (hg u).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => by simpa using hB u a)
  have hii : ∀ u v, Integrable (fun a => g u a * g v a) ν := fun u v =>
    (integrable_const (B * B)).mono' ((hg u).mul (hg v)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hB u a) (hB v a) (abs_nonneg _) ((abs_nonneg _).trans (hB u a)))
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext u v
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    rw [mul_comm (∫ a, g v a ∂ν)]
    simp_rw [mul_comm (g v _)]
  · set f : α → ℝ := fun a => ∑ u, x u * g u a with hf
    have hfm : Measurable f := Finset.measurable_sum _ fun u _ => (hg u).const_mul _
    have hfb : ∀ a, |f a| ≤ ∑ u, |x u| * B := fun a =>
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB u a) (abs_nonneg _))
    have hfi : MemLp f 2 ν := MemLp.of_bound hfm.aestronglyMeasurable (∑ u, |x u| * B)
      (Filter.Eventually.of_forall fun a => by simpa using hfb a)
    have h1 : ∫ a, f a ^ 2 ∂ν = ∑ u, ∑ v, x u * x v * ∫ a, g u a * g v a ∂ν := by
      have : ∀ a, f a ^ 2 = ∑ u, ∑ v, x u * x v * (g u a * g v a) := fun a => by
        rw [hf, sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
      simp_rw [this]
      rw [integral_finsetSum Finset.univ fun u _ => integrable_finsetSum _ fun v _ =>
        (hii u v).const_mul _]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [integral_finsetSum Finset.univ fun v _ => (hii u v).const_mul _]
      exact Finset.sum_congr rfl fun v _ => integral_const_mul _ _
    have h2 : ∫ a, f a ∂ν = ∑ u, x u * ∫ a, g u a ∂ν := by
      rw [hf]
      rw [integral_finsetSum Finset.univ fun u _ => (hi u).const_mul _]
      exact Finset.sum_congr rfl fun u _ => integral_const_mul _ _
    have hvar := variance_nonneg f ν
    rw [variance_eq_sub hfi, h2] at hvar
    refine le_of_le_of_eq hvar ?_
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial, Finset.mul_sum]
    have h3 : (∑ u, x u * ∫ a, g u a ∂ν) ^ 2 =
        ∑ u, ∑ v, x u * x v * ((∫ a, g u a ∂ν) * ∫ a, g v a ∂ν) := by
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
    have h1' : ∫ a, (f ^ 2) a ∂ν = ∑ u, ∑ v, x u * x v * ∫ a, g u a * g v a ∂ν := h1
    rw [h1', h3, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring

end Matrix
