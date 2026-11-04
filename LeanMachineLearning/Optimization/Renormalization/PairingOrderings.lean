/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Finpartition

/-!
# Ordering the blocks of a pair partition

Summing over ordered blocks counts each pairing `m!` times. This is the ordering factor
in the critical cavity derivative, independently of the values of the block weights.
-/

@[expose] public section

open Finset
open scoped BigOperators
namespace Finpartition

/-- Summing weighted products over every ordering of every pairing multiplies the usual
pairing sum by `m!`, for a set of `2m` elements and any commutative semiring of weights. -/
theorem pairingSum_orderings {α R : Type*} [DecidableEq α] [CommSemiring R]
    (s : Finset α) (m : ℕ) (hs : s.card = 2 * m) (w : Finset α → R) :
    (∑ P : Pairing s, ∑ e : Fin m ≃ P.val.parts, ∏ i : Fin m, w (e i).val) =
      (m.factorial : R) * pairingSum w s := by
  rw [pairingSum, Finset.mul_sum]
  apply sum_congr rfl
  intro P _
  have hparts : P.val.parts.card = m := by
    have hp := P.two_mul_card_parts
    omega
  let e0 : Fin m ≃ P.val.parts := Fintype.equivOfCardEq (by simp [hparts])
  have hprod (e : Fin m ≃ P.val.parts) : (∏ i : Fin m, w (e i).val) = P.blockProduct w := by
    calc
      _ = ∏ B : P.val.parts, w B.val := e.prod_comp _
      _ = _ := Finset.prod_coe_sort P.val.parts w
  simp_rw [hprod]
  rw [sum_const, card_univ, Fintype.card_equiv e0, Fintype.card_fin, nsmul_eq_mul]

end Finpartition
