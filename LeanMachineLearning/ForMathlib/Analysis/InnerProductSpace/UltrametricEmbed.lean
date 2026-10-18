/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Ultrametric inequality for points on a sphere

If points `h x` of a real inner product space all have the same squared norm `M` and their
scalar products satisfy `min ⟪h x, h y⟫ ⟪h x, h z⟫ ≤ ⟪h y, h z⟫`, then their Euclidean
distances satisfy the ultrametric inequality `‖h y - h z‖ ≤ max ‖h x - h y‖ ‖h x - h z‖`.
-/

@[expose] public section

/-- Points of equal norm whose scalar products satisfy the reverse ultrametric inequality
are at ultrametric distances. -/
theorem norm_sub_le_max_of_inner_min_le {X H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (h : X → H) (M : ℝ) (hnorm : ∀ x, ‖h x‖ ^ 2 = M)
    (hinner : ∀ x y z, min (inner ℝ (h x) (h y)) (inner ℝ (h x) (h z)) ≤ inner ℝ (h y) (h z))
    (x y z : X) : ‖h y - h z‖ ≤ max ‖h x - h y‖ ‖h x - h z‖ := by
  have hdist (a b : X) : ‖h a - h b‖ ^ 2 = 2 * (M - inner ℝ (h a) (h b)) := by
    rw [norm_sub_sq_real, hnorm a, hnorm b]; ring
  refine le_max_iff.mpr ?_
  rcases min_le_iff.mp (hinner x y z) with hxy | hxz
  · exact Or.inl ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
      rw [hdist, hdist]; linarith))
  · exact Or.inr ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
      rw [hdist, hdist]; linarith))
