import Mathlib
open scoped RealInnerProductSpace
open BigOperators

variable {ι : Type u_1} [Fintype ι]
variable (u h x' : EuclideanSpace ℝ ι)
variable (lambda : ℝ)

noncomputable def euclideanOf (x : ι → ℝ) : EuclideanSpace ℝ ι :=
  (WithLp.equiv 2 (ι → ℝ)).symm x

lemma inner_euclideanOf :
  (inner ℝ (euclideanOf fun i ↦ 2 * lambda * (u : ι → ℝ) i) h : ℝ) = 2 * lambda * inner ℝ u h := by
  dsimp [euclideanOf, inner]
  sorry
