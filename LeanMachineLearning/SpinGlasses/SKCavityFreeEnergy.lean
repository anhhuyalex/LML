/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityInterpolation

/-!
# The finite cavity partition-function identity

These deterministic identities are the algebraic first step in Talagrand's
Proposition 1.6.8.  They sum out the last Ising spin from an unnormalised
partition function.  The first statement is independent of the SK model; the
second inserts the `FinPairs` decomposition of the SK interaction.  In
particular, the latter can be applied with the common coefficient
`β / √N = β₊ / √(N+1)` without defining a second Hamiltonian or a bundled
partition-function object.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace SpinGlasses

/-- **Unnormalised finite cavity identity.**  Summing the final Ising coordinate of
`exp (A ρ + ε L ρ)` gives `2 exp (A ρ) cosh (L ρ)`.  This is the partition-function
counterpart of `integral_count_tilted_fin_snoc_cavity_units`, and applies to any finite
base energy and cavity field. -/
theorem sum_exp_fin_snoc_cavity (N : ℕ)
    (A L : (Fin N → ℤˣ) → ℝ) :
    (∑ σ : Fin (N + 1) → ℤˣ,
      Real.exp (A (fun i => σ i.castSucc) + (σ (Fin.last N) : ℝ) *
        L (fun i => σ i.castSucc))) =
      2 * ∑ ρ : Fin N → ℤˣ, Real.exp (A ρ) * Real.cosh (L ρ) := by
  let e : ((Fin N → ℤˣ) × ℤˣ) ≃ (Fin (N + 1) → ℤˣ) :=
    (Equiv.prodComm (Fin N → ℤˣ) ℤˣ).trans (Fin.snocEquiv fun _ => ℤˣ)
  rw [← e.sum_comp]
  simp only [e, Equiv.trans_apply, Equiv.prodComm_apply, Fin.snocEquiv_apply,
    Fin.snoc_castSucc, Fin.snoc_last]
  rw [Fintype.sum_prod_type]
  simp_rw [Real.exp_add, sum_units_int]
  simp only [Prod.swap_prod_mk]
  norm_num
  rw [show (fun ρ : Fin N → ℤˣ =>
      Real.exp (A ρ) * Real.exp (L ρ) + Real.exp (A ρ) * Real.exp (-L ρ)) =
      fun ρ => 2 * (Real.exp (A ρ) * Real.cosh (L ρ)) by
        funext ρ
        rw [Real.cosh_eq]
        ring]
  rw [← Finset.mul_sum]

/-- Split a pairwise SK energy and its uniform external field into its old-spin energy and
its final-spin cavity field.  The coefficient is arbitrary, which is exactly what is needed
for Talagrand's `β₊` comparison. -/
theorem sk_cavity_energy_snoc (N : ℕ) (c h : ℝ)
    (g : FinPairs (N + 1) → ℝ) (σ : Fin (N + 1) → ℤˣ) :
    c * (∑ p : FinPairs (N + 1),
      g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ) =
      (c * ∑ p : FinPairs N,
        g (oldPair N p) * (σ p.val.1.castSucc : ℝ) * (σ p.val.2.castSucc : ℝ) +
        h * ∑ i : Fin N, (σ i.castSucc : ℝ)) +
      (σ (Fin.last N) : ℝ) *
        (c * ∑ i : Fin N, g (lastPair N i) * (σ i.castSucc : ℝ) + h) := by
  rw [sum_sk_pairs_succ_cavity, Fin.sum_univ_castSucc]
  ring

/-- The interaction coefficient of the `(N+1)`-spin system at
`β₊ = β √(1 + 1/N)` is the coefficient `β / √N` of its old `N`-spin system. -/
theorem sk_beta_plus_coefficient (N : ℕ) (β : ℝ) (hN : 0 < N) :
    (Real.sqrt (N + 1 : ℝ))⁻¹ * (β * Real.sqrt (1 + (N : ℝ)⁻¹)) =
      (Real.sqrt (N : ℝ))⁻¹ * β := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have hsN : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 hN0).ne'
  have hsNp : Real.sqrt (N + 1 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  have harg : 1 + (N : ℝ)⁻¹ = (N + 1 : ℝ) / N := by field_simp
  rw [harg, Real.sqrt_div (by positivity)]
  field_simp

/-- **Talagrand's Eq. (1.172), pointwise partition-function form.**  At a common pair
coefficient `c`, the `(N+1)`-spin partition function is twice the old-spin partition sum
weighted by the hyperbolic cosine of its final-spin cavity field.  Taking
`c = β / √N = β₊ / √(N+1)` gives the book's comparison of `Z_{N+1}(β₊)` with `Z_N(β)`. -/
theorem sum_exp_sk_cavity_snoc (N : ℕ) (c h : ℝ)
    (g : FinPairs (N + 1) → ℝ) :
    (∑ σ : Fin (N + 1) → ℤˣ,
      Real.exp (c * (∑ p : FinPairs (N + 1),
        g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ))) =
      2 * ∑ ρ : Fin N → ℤˣ,
        Real.exp (c * (∑ p : FinPairs N,
          g (oldPair N p) * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) + h * ∑ i, (ρ i : ℝ)) *
          Real.cosh (c * ∑ i : Fin N, g (lastPair N i) * (ρ i : ℝ) + h) := by
  let A : (Fin N → ℤˣ) → ℝ := fun ρ =>
    c * (∑ p : FinPairs N,
      g (oldPair N p) * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) + h * ∑ i, (ρ i : ℝ)
  let L : (Fin N → ℤˣ) → ℝ := fun ρ =>
    c * ∑ i : Fin N, g (lastPair N i) * (ρ i : ℝ) + h
  have hsplit : ∀ σ : Fin (N + 1) → ℤˣ,
      c * (∑ p : FinPairs (N + 1),
        g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ) =
      A (fun i => σ i.castSucc) + (σ (Fin.last N) : ℝ) * L (fun i => σ i.castSucc) := by
    intro σ
    exact sk_cavity_energy_snoc N c h g σ
  rw [show (fun σ : Fin (N + 1) → ℤˣ =>
      Real.exp (c * (∑ p : FinPairs (N + 1),
        g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ))) =
      fun σ => Real.exp (A (fun i => σ i.castSucc) +
        (σ (Fin.last N) : ℝ) * L (fun i => σ i.castSucc)) by
        funext σ
        rw [hsplit]]
  simpa only [A, L] using sum_exp_fin_snoc_cavity N A L

/-- **Talagrand's Eq. (1.172), `β₊` form.**  For `N > 0`, set
`β₊ = β √(1 + 1/N)`.  The left side is the `(N+1)`-spin partition function at
`β₊`; the right side uses the genuine `N`-spin interaction coefficient `β / √N`.
This is a pointwise identity in the enlarged disorder. -/
theorem sum_exp_sk_cavity_beta_plus (N : ℕ) (β h : ℝ) (hN : 0 < N)
    (g : FinPairs (N + 1) → ℝ) :
    (∑ σ : Fin (N + 1) → ℤˣ,
      Real.exp ((Real.sqrt (N + 1 : ℝ))⁻¹ *
        (β * Real.sqrt (1 + (N : ℝ)⁻¹)) *
        (∑ p : FinPairs (N + 1),
          g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ))) =
      2 * ∑ ρ : Fin N → ℤˣ,
        Real.exp ((Real.sqrt (N : ℝ))⁻¹ * β *
          (∑ p : FinPairs N,
            g (oldPair N p) * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) + h * ∑ i, (ρ i : ℝ)) *
          Real.cosh ((Real.sqrt (N : ℝ))⁻¹ * β *
            ∑ i : Fin N, g (lastPair N i) * (ρ i : ℝ) + h) := by
  rw [sk_beta_plus_coefficient N β hN]
  exact sum_exp_sk_cavity_snoc N ((Real.sqrt (N : ℝ))⁻¹ * β) h g

end SpinGlasses
