/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPairingFibers
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.SortedPairs
public import LeanMachineLearning.Optimization.Renormalization.PairingWick

/-!
# Rectangular regrouping of a pairing class

The signed sum over one ordered-pairing class factors into rectangular kernel differences.
This is finite algebra for any symmetric replica kernel, independent of the cavity parameters.
-/

@[expose] public section

open Finset
open scoped BigOperators
namespace SpinGlasses

/-- Sum the signed endpoint choices inside one ordered-pairing class. The kernel can be
any symmetric real function; the block weights use the existing generic pairing API. -/
theorem skCavityPairing_signed_fiber_sum {m n : ℕ}
    (pairMap : Fin (2 * m) → Fin n × Fin n)
    (hxy : ∀ v, (pairMap v).1 ≠ (pairMap v).2)
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (Pe : Σ P : Finpartition.Pairing (univ : Finset (Fin (2 * m))), Fin m ≃ P.val.parts)
    (K : Fin n → Fin n → ℝ) (hK : ∀ a b, K a b = K b a) :
    (∑ p ∈ (univ.filter fun p : Fin m → FinPairs n => ∀ i v, v ∈ (Pe.2 i).val ↔
        (p i).val.1 ∈ ({(pairMap v).1, (pairMap v).2} : Finset (Fin n)) ∨
        (p i).val.2 ∈ ({(pairMap v).1, (pairMap v).2} : Finset (Fin n))),
      ∏ i : Fin m,
        (∏ v ∈ (Pe.2 i).val,
          if (pairMap v).1 ∈ ({(p i).val.1, (p i).val.2} : Finset (Fin n)) then
            (1 : ℝ) else -1) * K (p i).val.1 (p i).val.2) =
      Pe.1.blockProduct (Renormalization.pairWeight fun u v =>
        K (pairMap u).1 (pairMap v).1 - K (pairMap u).2 (pairMap v).1 -
          K (pairMap u).1 (pairMap v).2 + K (pairMap u).2 (pairMap v).2) := by
  obtain ⟨u, v, hB, hh⟩ := skCavityPairing_fiber_eq_piFinset pairMap hxy hdisj Pe
  let S := fun i => (univ : Finset (FinPairs n)).filter fun p =>
    p.val ∈ (({(pairMap (u i)).1, (pairMap (u i)).2} : Finset (Fin n)).product
      {(pairMap (v i)).1, (pairMap (v i)).2}).image
        (fun ab => (min ab.1 ab.2, max ab.1 ab.2))
  let C := fun u v => K (pairMap u).1 (pairMap v).1 - K (pairMap u).2 (pairMap v).1 -
    K (pairMap u).1 (pairMap v).2 + K (pairMap u).2 (pairMap v).2
  have hC : ∀ u v, C u v = C v u := by
    intro u v
    dsimp only [C]
    rw [hK (pairMap u).1 (pairMap v).1, hK (pairMap u).2 (pairMap v).1,
      hK (pairMap u).1 (pairMap v).2, hK (pairMap u).2 (pairMap v).2]
    ring
  have hsum (i : Fin m) :
      (∑ p ∈ S i, (∏ w ∈ (Pe.2 i).val,
        if (pairMap w).1 ∈ ({p.val.1, p.val.2} : Finset (Fin n)) then
          (1 : ℝ) else -1) * K p.val.1 p.val.2) = C (u i) (v i) := by
    have hd : Disjoint ({(pairMap (u i)).1, (pairMap (u i)).2} : Finset (Fin n))
        {(pairMap (v i)).1, (pairMap (v i)).2} := by
      simpa only [disjoint_insert_left, disjoint_singleton_left, mem_insert,
        mem_singleton, not_or, and_assoc] using hdisj (u i) (v i) (hB i).1
    simp_rw [(hB i).2, prod_pair (hB i).1]
    exact sum_signed_orderedPairs_product _ _ _ _ (hxy _) (hxy _) hd K hK
  rw [hh.2]
  erw [← prod_univ_sum S (fun i p =>
    (∏ v ∈ (Pe.2 i).val,
      if (pairMap v).1 ∈ ({p.val.1, p.val.2} : Finset (Fin n)) then
        (1 : ℝ) else -1) * K p.val.1 p.val.2)]
  simp_rw [hsum]
  calc
    (∏ i : Fin m, C (u i) (v i)) =
        ∏ i : Fin m, Renormalization.pairWeight C (Pe.2 i).val := by
      apply prod_congr rfl
      intro i _
      rw [(hB i).2, Renormalization.pairWeight_pair C hC (hB i).1]
    _ = ∏ B : Pe.1.val.parts, Renormalization.pairWeight C B.val := Pe.2.prod_comp _
    _ = _ := prod_coe_sort _ _

end SpinGlasses
