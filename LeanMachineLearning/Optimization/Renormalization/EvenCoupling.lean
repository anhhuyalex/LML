/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Expectation

/-!
# Even polynomial couplings

The degree-agnostic core for parity-even interaction potentials.  It is kept upstream of both
quartic perturbations and nearly-Gaussian action hierarchies so that degree four is a genuine
specialization rather than a second parallel implementation.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace Renormalization

universe uI

/-- A totally symmetric coefficient tensor with `2m` finite-index slots. -/
structure EvenCoupling (ι : Type uI) (m : ℕ) where
  /-- Coefficient of an ordered `2m`-tuple. -/
  coeff : (Fin (2 * m) → ι) → ℝ
  /-- Invariance under every permutation of the slots. -/
  coeff_perm : ∀ (σ : Equiv.Perm (Fin (2 * m))) (q : Fin (2 * m) → ι),
    coeff (q ∘ σ) = coeff q

namespace EvenCoupling

/-- The zero coupling at any even order. -/
def zero (ι : Type uI) (m : ℕ) : EvenCoupling ι m where
  coeff := 0
  coeff_perm := by simp

/-- Even homogeneous potential with the conventional `1 / (2m)!` symmetry factor. -/
def potential {ι : Type uI} {m : ℕ} [Fintype ι] (s : EvenCoupling ι m)
    (z : EuclideanSpace ℝ ι) : ℝ :=
  (((2 * m).factorial : ℝ)⁻¹) *
    ∑ q : Fin (2 * m) → ι, s.coeff q * coordinateMonomial q z

/-- Pointwise nonnegativity, used as a sufficient normalizability hypothesis. -/
def Nonnegative {ι : Type uI} {m : ℕ} [Fintype ι] (s : EvenCoupling ι m) : Prop :=
  ∀ z, 0 ≤ s.potential z

/-- An even homogeneous potential is invariant under the global sign flip. -/
theorem potential_neg {ι : Type uI} {m : ℕ} [Fintype ι] (s : EvenCoupling ι m)
    (z : EuclideanSpace ℝ ι) :
    s.potential (-z) = s.potential z := by
  unfold EvenCoupling.potential
  congr 1
  exact Finset.sum_congr rfl (fun q _hq => by
    congr 1
    dsimp [coordinateMonomial]
    rw [Finset.prod_neg]
    have hcard : (Finset.univ : Finset (Fin (2 * m))).card = 2 * m := by simp
    have heven : Even (2 * m) := ⟨m, by ring⟩
    rw [hcard, Even.neg_one_pow heven]
    simp)

/-- An even homogeneous potential is continuous. -/
theorem continuous_potential {ι : Type uI} {m : ℕ} [Fintype ι] (s : EvenCoupling ι m) :
    Continuous s.potential := by
  unfold EvenCoupling.potential coordinateMonomial
  fun_prop

end EvenCoupling

end Renormalization

end

end
