/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapSecondMoments.SKTBasisAlgebra
public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapCLT.HigherOrderCavity.SKCavityHigherOrderCorollary
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Rectangular difference operators for overlaps (Talagrand Section 1.11, Eqs. (1.345), (1.348))

This module unifies rectangular sums of two-index quantities across Sections 1.8, 1.10 and 1.11:
* The bivariate rectangular difference operator
  `rectDiff f p q = f p.1 q.1 - f p.2 q.1 - f p.1 q.2 + f p.2 q.2`.
* Additivity and vanishing on functions depending on only one coordinate.
* Exact cancellation of the single-type $T_\ell$ and global $T$ components of $R_{\ell,\ell'} - q$,
  proving $U_J = \operatorname{rectDiff} (R - q) = \operatorname{rectDiff} T$ (Eq. (1.345)).
* Decomposition into the truncated rectangular sum and the last-spin factor:
  $U_J = U_J^- + (N+1)^{-1} \eta_J$ (Eq. (1.348)).
-/

@[expose] public section

open scoped BigOperators Real

namespace SpinGlasses

variable {α β : Type*} [AddCommGroup β]

/-- The bivariate rectangular difference of `f : α → α → β` evaluated at the pairs `p` and `q`. -/
def rectDiff (f : α → α → β) (p q : α × α) : β :=
  f p.1 q.1 - f p.2 q.1 - f p.1 q.2 + f p.2 q.2

/-- Explicit 4-point coordinate form of `rectDiff`. -/
theorem rectDiff_def (f : α → α → β) (p q : α × α) :
    rectDiff f p q = f p.1 q.1 - f p.2 q.1 - f p.1 q.2 + f p.2 q.2 := rfl

/-- Linearity: `rectDiff` distributes over pointwise addition of bivariate functions. -/
theorem rectDiff_add (f g : α → α → β) (p q : α × α) :
    rectDiff (fun x y => f x y + g x y) p q = rectDiff f p q + rectDiff g p q := by
  dsimp [rectDiff]
  abel

/-- Linearity: `rectDiff` distributes over pointwise subtraction of bivariate functions. -/
theorem rectDiff_sub (f g : α → α → β) (p q : α × α) :
    rectDiff (fun x y => f x y - g x y) p q = rectDiff f p q - rectDiff g p q := by
  dsimp [rectDiff]
  abel

/-- Linearity: `rectDiff` distributes over scalar multiplication. -/
theorem rectDiff_smul {R : Type*} [Ring R] [Module R β] (c : R) (f : α → α → β) (p q : α × α) :
    rectDiff (fun x y => c • f x y) p q = c • rectDiff f p q := by
  dsimp [rectDiff]
  simp only [smul_sub, smul_add]

/-- If `f(x, y)` depends only on the first coordinate `x`, its rectangular difference vanishes. -/
theorem rectDiff_of_fst (g : α → β) (p q : α × α) :
    rectDiff (fun x _ => g x) p q = 0 := by
  dsimp [rectDiff]
  abel

/-- If `f(x, y)` depends only on the second coordinate `y`, its rectangular difference vanishes. -/
theorem rectDiff_of_snd (g : α → β) (p q : α × α) :
    rectDiff (fun _ y => g y) p q = 0 := by
  dsimp [rectDiff]
  abel

/-- If `f(x, y)` is a constant `c`, its rectangular difference vanishes. -/
theorem rectDiff_const (c : β) (p q : α × α) :
    rectDiff (fun _ _ => c) p q = 0 := by
  dsimp [rectDiff]
  abel

/-- Adding a term depending only on the first coordinate does not change `rectDiff`. -/
theorem rectDiff_add_fst (f : α → α → β) (g : α → β) (p q : α × α) :
    rectDiff (fun x y => f x y + g x) p q = rectDiff f p q := by
  rw [rectDiff_add, rectDiff_of_fst, add_zero]

/-- Adding a term depending only on the second coordinate does not change `rectDiff`. -/
theorem rectDiff_add_snd (f : α → α → β) (g : α → β) (p q : α × α) :
    rectDiff (fun x y => f x y + g y) p q = rectDiff f p q := by
  rw [rectDiff_add, rectDiff_of_snd, add_zero]

/-- Adding a constant does not change `rectDiff`. -/
theorem rectDiff_add_const (f : α → α → β) (c : β) (p q : α × α) :
    rectDiff (fun x y => f x y + c) p q = rectDiff f p q := by
  rw [rectDiff_add, rectDiff_const, add_zero]

/-- Subtracting a constant does not change `rectDiff`. -/
theorem rectDiff_sub_const (f : α → α → β) (c : β) (p q : α × α) :
    rectDiff (fun x y => f x y - c) p q = rectDiff f p q := by
  rw [rectDiff_sub, rectDiff_const, sub_zero]

/-- Symmetry: for a symmetric bivariate function, `rectDiff f p q = rectDiff f q p`. -/
theorem rectDiff_comm (f : α → α → β) (hf : ∀ x y, f x y = f y x) (p q : α × α) :
    rectDiff f p q = rectDiff f q p := by
  dsimp [rectDiff]
  rw [hf p.1 q.1, hf p.2 q.1, hf p.1 q.2, hf p.2 q.2]
  abel

/-- Product factorization of last-spin differences:
`rectDiff (fun x y => ε x * ε y) p q = (ε p.1 - ε p.2) * (ε q.1 - ε q.2)`. -/
theorem rectDiff_mul_prod {R : Type*} [CommRing R] (ε : α → R) (p q : α × α) :
    rectDiff (fun x y => ε x * ε y) p q = (ε p.1 - ε p.2) * (ε q.1 - ε q.2) := by
  dsimp [rectDiff]
  ring

/-- **Talagrand's Eq. (1.345): The exact cancellation of $T_\ell$ and $T$ in $U_J$.**
For any decomposition $R(x, y) - q = T_{x, y} + T_x + T_y + T$, the rectangular difference
$\operatorname{rectDiff} (R - q) p q$ equals $\operatorname{rectDiff} T_{\cdot, \cdot} p q$. -/
theorem rectDiff_overlap_sub_q_eq_rectDiff_T (R T_pair : α → α → ℝ) (T_single : α → ℝ)
    (T_global q : ℝ)
    (hdecomp : ∀ x y, R x y - q = T_pair x y + T_single x + T_single y + T_global)
    (p q_pair : α × α) :
    rectDiff (fun x y => R x y - q) p q_pair = rectDiff T_pair p q_pair := by
  have he : (fun x y => R x y - q) =
      (fun x y => T_pair x y + T_single x + T_single y + T_global) := by
    funext x y
    exact hdecomp x y
  rw [he]
  have h1 : rectDiff (fun x y => T_pair x y + T_single x + T_single y + T_global) p q_pair =
      rectDiff (fun x y => T_pair x y + T_single x + T_single y) p q_pair :=
    rectDiff_add_const _ _ p q_pair
  rw [h1]
  have h2 : rectDiff (fun x y => T_pair x y + T_single x + T_single y) p q_pair =
      rectDiff (fun x y => T_pair x y + T_single x) p q_pair :=
    rectDiff_add_snd _ _ p q_pair
  rw [h2]
  exact rectDiff_add_fst _ _ p q_pair

/-- **Talagrand's Eq. (1.348): Decomposition of the full rectangular sum into truncated plus spin.**
If $R(x, y) = R^-(x, y) + (N+1)^{-1} \varepsilon(x) \varepsilon(y)$, then
$\operatorname{rectDiff} R p q = \operatorname{rectDiff} R^- p q +$
$(N+1)^{-1} (\varepsilon p.1 - \varepsilon p.2)(\varepsilon q.1 - \varepsilon q.2)$. -/
theorem rectDiff_overlap_eq_truncated_add_spin (N : ℕ) (R R_trunc : α → α → ℝ) (ε : α → ℝ)
    (hsplit : ∀ x y, R x y = R_trunc x y + ((N + 1 : ℝ)⁻¹) * (ε x * ε y)) (p q : α × α) :
    rectDiff R p q = rectDiff R_trunc p q +
      ((N + 1 : ℝ)⁻¹) * ((ε p.1 - ε p.2) * (ε q.1 - ε q.2)) := by
  have he : R = (fun x y => R_trunc x y + ((N + 1 : ℝ)⁻¹) * (ε x * ε y)) := by
    funext x y; exact hsplit x y
  rw [he, rectDiff_add, ← rectDiff_mul_prod ε p q]
  dsimp [rectDiff]
  ring

end SpinGlasses
