/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Series over a finite product of types in `ℝ≥0∞`

For a finite index type `Q` and functions `h q : Y q → ℝ≥0∞`, the unconditional sum over the
dependent product `∀ q, Y q` of `∏ q, h q (y q)` is the product of the sums
(`ENNReal.tsum_pi_prod`). In `ℝ≥0∞` no summability is needed.
-/

@[expose] public section

open scoped ENNReal

namespace ENNReal

/-- The sum over a dependent product indexed by `Fin n` of a product of one-variable functions. -/
theorem tsum_pi_prod_fin {n : ℕ} {Y : Fin n → Type*} (h : ∀ i, Y i → ℝ≥0∞) :
    ∑' y : (∀ i, Y i), ∏ i, h i (y i) = ∏ i, ∑' z, h i z := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    rw [tsum_eq_single (fun i => i.elim0) fun y hy => absurd (funext fun i => i.elim0) hy]
  | succ n ih =>
    rw [← (Fin.consEquiv Y).tsum_eq]
    simp only [Fin.prod_univ_succ]
    change (∑' c : Y 0 × (∀ i : Fin n, Y i.succ),
      h 0 ((Fin.consEquiv Y c) 0) * ∏ i : Fin n, h i.succ ((Fin.consEquiv Y c) i.succ)) = _
    simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_right]
    refine tsum_congr fun z => ?_
    dsimp only
    rw [ENNReal.tsum_mul_left]
    exact congrArg _ (ih (fun i => h i.succ))

/-- The sum over a dependent product indexed by a finite type of a product of one-variable
functions is the product of the sums. -/
theorem tsum_pi_prod {Q : Type*} [Fintype Q] {Y : Q → Type*} (h : ∀ q, Y q → ℝ≥0∞) :
    ∑' y : (∀ q, Y q), ∏ q, h q (y q) = ∏ q, ∑' z, h q z := by
  classical
  let e := Fintype.equivFin Q
  have key := tsum_pi_prod_fin (fun i : Fin (Fintype.card Q) => h (e.symm i))
  have h1 := (Equiv.piCongrLeft' Y e).symm.tsum_eq (fun y : (∀ q, Y q) => ∏ q, h q (y q))
  rw [← h1]
  have h2 : ∀ x : (∀ i : Fin (Fintype.card Q), Y (e.symm i)),
      ∏ q, h q (((Equiv.piCongrLeft' Y e).symm x) q) = ∏ i, h (e.symm i) (x i) := by
    intro x
    rw [← e.symm.prod_comp]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp
  simp_rw [h2]
  rw [key, ← e.symm.prod_comp (fun q => ∑' z, h q z)]

end ENNReal
