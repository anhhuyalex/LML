/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Ring

/-!
# Centering the two vectors in a scaled dot product

The same finite-vector identity underlies the overlap decompositions in Talagrand's
Sections 1.8 and 1.10. It is algebra over a commutative ring, with an arbitrary scale.
-/

@[expose] public section

open scoped BigOperators Matrix

/-- Center both vectors, retaining the two linear terms and the common mean term. -/
theorem dotProduct_centering {ι K : Type*} [Fintype ι] [CommRing K]
    (c q : K) (x y b : ι → K) :
    c * (x ⬝ᵥ y) - q = c * ((x - b) ⬝ᵥ (y - b)) + c * ((x - b) ⬝ᵥ b) +
      c * ((y - b) ⬝ᵥ b) + (c * (b ⬝ᵥ b) - q) := by
  have he : x ⬝ᵥ y = (x - b) ⬝ᵥ (y - b) + (x - b) ⬝ᵥ b +
      (y - b) ⬝ᵥ b + b ⬝ᵥ b := by
    simp only [sub_dotProduct, dotProduct_sub]
    rw [dotProduct_comm b y]
    ring
  rw [he]
  ring

/-- Centering by the mean overlap removes the common mean term exactly. -/
theorem dotProduct_sub_mean_decomp {ι K : Type*} [Fintype ι] [CommRing K]
    (c : K) (x y b : ι → K) :
    c * (x ⬝ᵥ y) - c * (b ⬝ᵥ b) = c * ((x - b) ⬝ᵥ (y - b)) +
      c * ((x - b) ⬝ᵥ b) + c * ((y - b) ⬝ᵥ b) := by
  simpa only [sub_self, add_zero] using dotProduct_centering c (c * (b ⬝ᵥ b)) x y b
