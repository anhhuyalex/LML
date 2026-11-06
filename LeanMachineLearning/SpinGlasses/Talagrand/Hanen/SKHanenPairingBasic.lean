/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenRectangular

public import LeanMachineLearning.Optimization.Renormalization.PairingCardinality
public import LeanMachineLearning.Optimization.Renormalization.PairingWick

/-!
# Truncated rectangular overlaps

The rectangular kernel is the block weight in the generic finite-partition Wick sum.
Analytic derivative arguments are kept in `SKHanenPairing.lean`.
-/

@[expose] public section

open Finset
open scoped BigOperators Real Matrix
namespace SpinGlasses

/-- Truncated rectangular difference $U_J^-$ for two replica pairs.
This kernel is used in the pairing derivative and its orientation sums; naming the kernel
keeps those statements readable without introducing a second pairing representation. -/
noncomputable def skCavityRectTrunc (N n m : ℕ) (q : ℝ)
    (pairMap : Fin (2 * m) → Fin n × Fin n) (u v : Fin (2 * m))
    (ρ : Fin n → Fin N → ℤˣ) : ℝ :=
  let x1 := (pairMap u).1
  let x2 := (pairMap u).2
  let y1 := (pairMap v).1
  let y2 := (pairMap v).2
  ((N + 1 : ℝ)⁻¹ * ((fun i => (ρ x1 i : ℝ)) ⬝ᵥ (fun i => (ρ y1 i : ℝ))) - q) -
  ((N + 1 : ℝ)⁻¹ * ((fun i => (ρ x2 i : ℝ)) ⬝ᵥ (fun i => (ρ y1 i : ℝ))) - q) -
  ((N + 1 : ℝ)⁻¹ * ((fun i => (ρ x1 i : ℝ)) ⬝ᵥ (fun i => (ρ y2 i : ℝ))) - q) +
  ((N + 1 : ℝ)⁻¹ * ((fun i => (ρ x2 i : ℝ)) ⬝ᵥ (fun i => (ρ y2 i : ℝ))) - q)

/-- $U_{\{u, v\}}^-$ is a signed sum of four overlap fluctuations, one for each choice of an
endpoint of the pair `u` and of the pair `v`. Here `true` selects the second endpoint and carries
the sign `-1`. -/
theorem skCavityRectTrunc_eq_sum_bool (N n m : ℕ) (q : ℝ)
    (pairMap : Fin (2 * m) → Fin n × Fin n) (u v : Fin (2 * m))
    (ρ : Fin n → Fin N → ℤˣ) :
    skCavityRectTrunc N n m q pairMap u v ρ =
      ∑ e : Bool × Bool, ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (ρ (if e.1 then (pairMap u).2 else (pairMap u).1) i : ℝ)) ⬝ᵥ
            fun i : Fin N => (ρ (if e.2 then (pairMap v).2 else (pairMap v).1) i : ℝ)) - q) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true,
    skCavityRectTrunc]
  ring

/-- Symmetry of $U_{\{u, v\}}^-$ under swapping $u$ and $v$. -/
theorem skCavityRectTrunc_comm (N n m : ℕ) (q : ℝ)
    (pairMap : Fin (2 * m) → Fin n × Fin n) (u v : Fin (2 * m))
    (ρ : Fin n → Fin N → ℤˣ) :
    skCavityRectTrunc N n m q pairMap u v ρ = skCavityRectTrunc N n m q pairMap v u ρ := by
  dsimp only [skCavityRectTrunc]
  have hdot (a b : Fin n) :
      ((fun i => (ρ a i : ℝ)) ⬝ᵥ (fun i => (ρ b i : ℝ))) =
      ((fun i => (ρ b i : ℝ)) ⬝ᵥ (fun i => (ρ a i : ℝ))) := dotProduct_comm _ _
  rw [hdot (pairMap u).1 (pairMap v).1, hdot (pairMap u).2 (pairMap v).1,
      hdot (pairMap u).1 (pairMap v).2, hdot (pairMap u).2 (pairMap v).2]
  ring

end SpinGlasses
