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
# Rectangular difference identities for overlaps (Talagrand Section 1.11, Eqs. (1.345), (1.348))

This module unifies rectangular sums of two-index quantities across Sections 1.8, 1.10 and 1.11,
without introducing a wrapper definition:
* Exact cancellation of the single-type $T_\ell$ and global $T$ components of $R_{\ell,\ell'} - q$,
  proving $U_J = T_{2u-1,2v-1} - T_{2u-1,2v} - T_{2u,2v-1} + T_{2u,2v}$ (Eq. (1.345)).
* Decomposition into the truncated rectangular sum and the last-spin factor:
  $U_J = U_J^- + (N+1)^{-1} \eta_J$ (Eq. (1.348)).
* Basic algebraic linearity and vanishing on functions depending on only one coordinate.
-/

@[expose] public section

open scoped BigOperators Real

namespace SpinGlasses

variable {α β : Type*} [AddCommGroup β]

/-- Linearity: distributing over pointwise addition of bivariate functions. -/
theorem rect_add (f g : α → α → β) (x₁ x₂ y₁ y₂ : α) :
    (f x₁ y₁ + g x₁ y₁) - (f x₂ y₁ + g x₂ y₁) - (f x₁ y₂ + g x₁ y₂) + (f x₂ y₂ + g x₂ y₂) =
      (f x₁ y₁ - f x₂ y₁ - f x₁ y₂ + f x₂ y₂) + (g x₁ y₁ - g x₂ y₁ - g x₁ y₂ + g x₂ y₂) := by
  abel

/-- Linearity: distributing over pointwise subtraction of bivariate functions. -/
theorem rect_sub (f g : α → α → β) (x₁ x₂ y₁ y₂ : α) :
    (f x₁ y₁ - g x₁ y₁) - (f x₂ y₁ - g x₂ y₁) - (f x₁ y₂ - g x₁ y₂) + (f x₂ y₂ - g x₂ y₂) =
      (f x₁ y₁ - f x₂ y₁ - f x₁ y₂ + f x₂ y₂) - (g x₁ y₁ - g x₂ y₁ - g x₁ y₂ + g x₂ y₂) := by
  abel

/-- If `f(x, y)` depends only on the first coordinate `x`, the rectangular difference vanishes. -/
theorem rect_of_fst (g : α → β) (x₁ x₂ : α) :
    g x₁ - g x₂ - g x₁ + g x₂ = 0 := by
  abel

/-- If `f(x, y)` depends only on the second coordinate `y`, the rectangular difference vanishes. -/
theorem rect_of_snd (g : α → β) (y₁ y₂ : α) :
    g y₁ - g y₁ - g y₂ + g y₂ = 0 := by
  abel

/-- If `f(x, y)` is a constant `c`, the rectangular difference vanishes. -/
theorem rect_const (c : β) :
    c - c - c + c = 0 := by
  abel

/-- Symmetry: for a symmetric bivariate function, transposing arguments gives the same sum. -/
theorem rect_comm (f : α → α → β) (hf : ∀ x y, f x y = f y x) (x₁ x₂ y₁ y₂ : α) :
    f x₁ y₁ - f x₂ y₁ - f x₁ y₂ + f x₂ y₂ =
      f y₁ x₁ - f y₁ x₂ - f y₂ x₁ + f y₂ x₂ := by
  rw [hf x₁ y₁, hf x₂ y₁, hf x₁ y₂, hf x₂ y₂]

/-- Product factorization of last-spin differences:
`(ε x₁ * ε y₁) - (ε x₂ * ε y₁) - (ε x₁ * ε y₂) + (ε x₂ * ε y₂) = (ε x₁ - ε x₂) * (ε y₁ - ε y₂)`. -/
theorem rect_mul_prod {R : Type*} [CommRing R] (ε : α → R) (x₁ x₂ y₁ y₂ : α) :
    (ε x₁ * ε y₁) - (ε x₂ * ε y₁) - (ε x₁ * ε y₂) + (ε x₂ * ε y₂) =
      (ε x₁ - ε x₂) * (ε y₁ - ε y₂) := by
  ring

/-- Product factorization for coordinate pairs:
`(ε p.1 * ε q.1) - (ε p.2 * ε q.1) - (ε p.1 * ε q.2) + (ε p.2 * ε q.2) =
  (ε p.1 - ε p.2) * (ε q.1 - ε q.2)`. -/
theorem rect_mul_prod_pair {R : Type*} [CommRing R] (ε : α → R) (p q : α × α) :
    (ε p.1 * ε q.1) - (ε p.2 * ε q.1) - (ε p.1 * ε q.2) + (ε p.2 * ε q.2) =
      (ε p.1 - ε p.2) * (ε q.1 - ε q.2) :=
  rect_mul_prod ε p.1 p.2 q.1 q.2

/-- **Talagrand's Eq. (1.345): The exact cancellation of $T_\ell$ and $T$ in $U_J$.**
For any decomposition $R(x, y) - q = T_{x, y} + T_x + T_y + T$, the rectangular difference
$(R x₁ y₁ - q) - (R x₂ y₁ - q) - (R x₁ y₂ - q) + (R x₂ y₂ - q)$
equals $T_{x₁ y₁} - T_{x₂ y₁} - T_{x₁ y₂} + T_{x₂ y₂}$. -/
theorem rect_overlap_sub_q_eq_rect_T (R T_pair : α → α → β) (T_single : α → β)
    (T_global q : β)
    (hdecomp : ∀ x y, R x y - q = T_pair x y + T_single x + T_single y + T_global)
    (x₁ x₂ y₁ y₂ : α) :
    (R x₁ y₁ - q) - (R x₂ y₁ - q) - (R x₁ y₂ - q) + (R x₂ y₂ - q) =
      T_pair x₁ y₁ - T_pair x₂ y₁ - T_pair x₁ y₂ + T_pair x₂ y₂ := by
  rw [hdecomp x₁ y₁, hdecomp x₂ y₁, hdecomp x₁ y₂, hdecomp x₂ y₂]
  abel

/-- Pair form of `rect_overlap_sub_q_eq_rect_T`. -/
theorem rect_overlap_sub_q_eq_rect_T_pair (R T_pair : α → α → β) (T_single : α → β)
    (T_global q : β)
    (hdecomp : ∀ x y, R x y - q = T_pair x y + T_single x + T_single y + T_global)
    (p q_pair : α × α) :
    (R p.1 q_pair.1 - q) - (R p.2 q_pair.1 - q) - (R p.1 q_pair.2 - q) + (R p.2 q_pair.2 - q) =
      T_pair p.1 q_pair.1 - T_pair p.2 q_pair.1 - T_pair p.1 q_pair.2 + T_pair p.2 q_pair.2 :=
  rect_overlap_sub_q_eq_rect_T R T_pair T_single T_global q hdecomp p.1 p.2 q_pair.1 q_pair.2

/-- **Talagrand's Eq. (1.348): Decomposition of the full rectangular sum into truncated plus spin.**
If $R(x, y) = R^-(x, y) + (N+1)^{-1} \varepsilon(x) \varepsilon(y)$, then
$(R x₁ y₁ - R x₂ y₁ - R x₁ y₂ + R x₂ y₂) =
  (R^- x₁ y₁ - R^- x₂ y₁ - R^- x₁ y₂ + R^- x₂ y₂) +
  (N+1)^{-1} (\varepsilon x₁ - \varepsilon x₂)(\varepsilon y₁ - \varepsilon y₂)$. -/
theorem rect_overlap_eq_truncated_add_spin (N : ℕ) (R R_trunc : α → α → ℝ) (ε : α → ℝ)
    (hsplit : ∀ x y, R x y = R_trunc x y + ((N + 1 : ℝ)⁻¹) * (ε x * ε y))
    (x₁ x₂ y₁ y₂ : α) :
    R x₁ y₁ - R x₂ y₁ - R x₁ y₂ + R x₂ y₂ =
      R_trunc x₁ y₁ - R_trunc x₂ y₁ - R_trunc x₁ y₂ + R_trunc x₂ y₂ +
        ((N + 1 : ℝ)⁻¹) * ((ε x₁ - ε x₂) * (ε y₁ - ε y₂)) := by
  have h1 := hsplit x₁ y₁
  have h2 := hsplit x₂ y₁
  have h3 := hsplit x₁ y₂
  have h4 := hsplit x₂ y₂
  linarith

/-- Pair form of `rect_overlap_eq_truncated_add_spin`. -/
theorem rect_overlap_eq_truncated_add_spin_pair (N : ℕ) (R R_trunc : α → α → ℝ) (ε : α → ℝ)
    (hsplit : ∀ x y, R x y = R_trunc x y + ((N + 1 : ℝ)⁻¹) * (ε x * ε y))
    (p q : α × α) :
    R p.1 q.1 - R p.2 q.1 - R p.1 q.2 + R p.2 q.2 =
      R_trunc p.1 q.1 - R_trunc p.2 q.1 - R_trunc p.1 q.2 + R_trunc p.2 q.2 +
        ((N + 1 : ℝ)⁻¹) * ((ε p.1 - ε p.2) * (ε q.1 - ε q.2)) :=
  rect_overlap_eq_truncated_add_spin N R R_trunc ε hsplit p.1 p.2 q.1 q.2

end SpinGlasses
