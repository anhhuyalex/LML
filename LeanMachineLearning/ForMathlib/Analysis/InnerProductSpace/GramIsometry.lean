/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Families with the same Gram matrix are related by a linear isometry

If `h : ι → H` and `x : ι → H'` have the same Gram matrix, then `h i ↦ x i` extends to a linear
isometry on the closed span of the `h i`, and, after adding to the target a copy of `H` that
receives the orthogonal complement, to a linear isometry of the whole space `H` into
`WithLp 2 (H × H')`.  (Without the extra copy of `H` an isometry `H → H'` need not exist, because
the orthogonal complement of the span of the `h i` may be larger than that of the span of the
`x i`.)

## Main declarations

* `exists_linearIsometry_of_inner_eq`: the isometry `U : H →ₗᵢ[ℝ] WithLp 2 (H × H')` with
  `U (h i) = (0, x i)`.
-/

@[expose] public section

open Set Submodule Topology
open scoped RealInnerProductSpace

variable {ι H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℝ H']

/-- The squared norm of a finite linear combination in terms of the Gram matrix of the family. -/
private lemma norm_sq_linearCombination {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (g : ι → E) (c : ι →₀ ℝ) :
    ‖Finsupp.linearCombination ℝ g c‖ ^ 2 =
      c.sum fun i a => c.sum fun j b => a * b * ⟪g i, g j⟫ := by
  rw [← real_inner_self_eq_norm_sq, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum,
    sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, Finsupp.sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [real_inner_smul_left, real_inner_smul_right, mul_assoc]

/-- The norm of a finite linear combination only depends on the Gram matrix of the family. -/
private lemma norm_linearCombination_eq {h : ι → H} {x : ι → H'}
    (hxh : ∀ i j, ⟪x i, x j⟫ = ⟪h i, h j⟫) (c : ι →₀ ℝ) :
    ‖Finsupp.linearCombination ℝ x c‖ = ‖Finsupp.linearCombination ℝ h c‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_linearCombination,
    norm_sq_linearCombination]
  simp only [hxh]

/-- **Equal Gram matrices give an isometry on the closed span.**  If `x i` and `h i` have the same
inner products, there is a linear isometry from the closure of `span (range h)` to `H'` taking
`h i` to `x i`. -/
private lemma exists_linearIsometry_closure_span [CompleteSpace H'] {h : ι → H} {x : ι → H'}
    (hxh : ∀ i j, ⟪x i, x j⟫ = ⟪h i, h j⟫) :
    ∃ V : (span ℝ (range h)).topologicalClosure →ₗᵢ[ℝ] H',
      ∀ i, V ⟨h i, subset_closure (subset_span ⟨i, rfl⟩)⟩ = x i := by
  set S := (span ℝ (range h)).topologicalClosure
  set e : (ι →₀ ℝ) →ₗ[ℝ] S := (Finsupp.linearCombination ℝ h).codRestrict S fun c =>
    (span ℝ (range h)).le_topologicalClosure (by
      rw [← Finsupp.range_linearCombination]; exact LinearMap.mem_range_self _ c) with he
  have hdense : DenseRange e := by
    rw [DenseRange, dense_iff_closure_eq]
    refine eq_univ_of_forall fun y => ?_
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, mem_preimage,
      ← range_comp]
    have himage : (Subtype.val ∘ e) = Finsupp.linearCombination ℝ h := rfl
    rw [himage, ← LinearMap.coe_range, Finsupp.range_linearCombination]
    exact y.2
  have hnorm : ∀ c, ‖Finsupp.linearCombination ℝ x c‖ = ‖e c‖ := fun c => by
    rw [norm_linearCombination_eq hxh]; rfl
  refine ⟨(Finsupp.linearCombination ℝ x).extendOfIsometry hdense hnorm, fun i => ?_⟩
  have hei : e (Finsupp.single i 1) = ⟨h i, subset_closure (subset_span ⟨i, rfl⟩)⟩ :=
    Subtype.ext (by simp [he])
  have := (Finsupp.linearCombination ℝ x).extendOfIsometry_eq hdense hnorm (Finsupp.single i 1)
  rw [hei] at this
  simpa using this

/-- **Equal Gram matrices give a linear isometry of the whole space.**  If `h : ι → H` and
`x : ι → H'` have the same inner products, there is a linear isometry
`U : H → WithLp 2 (H × H')` with `U (h i) = (0, x i)`: on the closed span of the `h i` it is the
isometry of `exists_linearIsometry_closure_span` into the second factor, and on the orthogonal
complement it is the identity into the first factor. -/
theorem exists_linearIsometry_of_inner_eq [CompleteSpace H] [CompleteSpace H'] {h : ι → H}
    {x : ι → H'} (hxh : ∀ i j, ⟪x i, x j⟫ = ⟪h i, h j⟫) :
    ∃ U : H →ₗᵢ[ℝ] WithLp 2 (H × H'), ∀ i, U (h i) = WithLp.toLp 2 ((0 : H), x i) := by
  set S := (span ℝ (range h)).topologicalClosure
  obtain ⟨V, hV⟩ : ∃ V : S →ₗᵢ[ℝ] H', ∀ i, V ⟨h i, subset_closure (subset_span ⟨i, rfl⟩)⟩ = x i :=
    exists_linearIsometry_closure_span hxh
  have : CompleteSpace S := (isClosed_topologicalClosure _).completeSpace_coe
  let T : H →ₗ[ℝ] WithLp 2 (H × H') := (WithLp.linearEquiv 2 ℝ (H × H')).symm.toLinearMap ∘ₗ
    ((Sᗮ.starProjection : H →L[ℝ] H).toLinearMap.prod
      (V.toLinearMap ∘ₗ (S.orthogonalProjectionOnto : H →L[ℝ] S).toLinearMap))
  refine ⟨⟨T, fun v => ?_⟩, fun i => ?_⟩
  · rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2,
      S.norm_sq_eq_add_norm_sq_starProjection v]
    simp [T, add_comm]
  · have hi : h i ∈ S := subset_closure (subset_span ⟨i, rfl⟩)
    have h0 : Sᗮ.starProjection (h i) = 0 := starProjection_orthogonal_apply_eq_zero hi
    have h1 : S.orthogonalProjectionOnto (h i) = ⟨h i, hi⟩ :=
      orthogonalProjectionOnto_mem_subspace_eq_self ⟨h i, hi⟩
    simpa [T, h0, h1] using hV i
