/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Foundations.MatrixUtil
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Analysis.Matrix.MeasurableSpace

/-!
# Measurability of Matrix Expressions

Entrywise measurability lemmas for products, transposes, matrix-vector products and dot products of
measurable matrix- and vector-valued maps, plus the orthogonal-complement projector. They are the
glue used by the conditional Chebyshev bounds (`Initialization/GaussianConditioning.lean`) and the
deep backward-pass concentration (`Deep/`).
-/

@[expose]
public section

open MeasureTheory Matrix

namespace NTK

section measurability
variable {Z : Type*} [MeasurableSpace Z] {n p q : Type*}

/-- Entry `(i, j)` of a measurable matrix-valued map is measurable. -/
lemma measurable_matrix_entry {A : Z → Matrix n p ℝ} (hA : Measurable A) (i : n) (j : p) :
    Measurable fun z => A z i j :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)

lemma measurable_vec_entry {v : Z → n → ℝ} (hv : Measurable v) (i : n) :
    Measurable fun z => v z i := (measurable_pi_apply i).comp hv

lemma measurable_matrix_mul [Fintype p] {A : Z → Matrix n p ℝ} {B : Z → Matrix p q ℝ}
    (hA : Measurable A) (hB : Measurable B) : Measurable fun z => A z * B z := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ =>
    (measurable_matrix_entry hA i k).mul (measurable_matrix_entry hB k j)

lemma measurable_matrix_transpose {A : Z → Matrix n p ℝ} (hA : Measurable A) :
    Measurable fun z => (A z)ᵀ := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  exact measurable_matrix_entry hA j i

lemma measurable_mulVec [Fintype p] {A : Z → Matrix n p ℝ} {v : Z → p → ℝ}
    (hA : Measurable A) (hv : Measurable v) : Measurable fun z => A z *ᵥ v z := by
  refine Measurable.of_eval fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum _ fun k _ =>
    (measurable_matrix_entry hA i k).mul (measurable_vec_entry hv k)

lemma measurable_dotProduct [Fintype n] {u v : Z → n → ℝ} (hu : Measurable u)
    (hv : Measurable v) : Measurable fun z => u z ⬝ᵥ v z := by
  simp only [dotProduct]
  exact Finset.measurable_sum _ fun k _ =>
    (measurable_vec_entry hu k).mul (measurable_vec_entry hv k)

end measurability

section inverse

/-- The matrix inverse is measurable (it is `det⁻¹ • adjugate`, with the convention `0⁻¹ = 0`). -/
lemma measurable_matrix_nonsing_inv {n : Type*} [Fintype n] [DecidableEq n] :
    Measurable fun A : Matrix n n ℝ => A⁻¹ := by
  have h : (fun A : Matrix n n ℝ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (measurable_inv.comp (continuous_id.matrix_det).measurable).smul
    (continuous_id.matrix_adjugate).measurable

end inverse

section orthogonal

variable {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_orthogonalComplement {p : ℕ} {P : Ω → Matrix (Fin p) (Fin p) ℝ}
    (hP : Measurable P) : Measurable fun a => orthogonalComplement (P a) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  simp only [orthogonalComplement, Matrix.sub_apply]
  exact measurable_const.sub (measurable_matrix_entry hP i j)

end orthogonal

end NTK

end
