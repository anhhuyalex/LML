/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Integrating out one replica of an i.i.d. family

For an i.i.d. family `ρ : R → α` of a finite probability space, a function that does not depend on
the coordinate `d` except through one evaluation `ρ d` can be integrated in `ρ d` first: the
coordinate is replaced by an independent copy and averaged.
-/

@[expose] public section

open MeasureTheory Finset
open scoped BigOperators

namespace MeasureTheory

variable {α R : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Finite α]
  [Fintype R] [DecidableEq R]

/-- **Integrating out one replica.** If `Φ ρ t` does not depend on the coordinate `d` of `ρ`, then
averaging `Φ ρ (ρ d)` over an i.i.d. family equals averaging `ρ ↦ ∫ t, Φ ρ t ∂μ`. -/
theorem integral_pi_integrate_out_replica (μ : Measure α) [IsProbabilityMeasure μ] (d : R)
    (Φ : (R → α) → α → ℝ) (hΦ : ∀ ρ s t, Φ (Function.update ρ d s) t = Φ ρ t) :
    ∫ ρ, Φ ρ (ρ d) ∂(Measure.pi fun _ : R => μ) =
      ∫ ρ, (∫ t, Φ ρ t ∂μ) ∂(Measure.pi fun _ : R => μ) := by
  have := Fintype.ofFinite α
  have hne : Nonempty α := (nonempty_of_isProbabilityMeasure μ)
  obtain ⟨s0⟩ := hne
  set w : α → ℝ := fun a => μ.real {a} with hw
  have hpi (Ψ : (R → α) → ℝ) :
      ∫ ρ, Ψ ρ ∂(Measure.pi fun _ : R => μ) = ∑ ρ : R → α, (∏ r, w (ρ r)) * Ψ ρ := by
    rw [integral_fintype Integrable.of_finite]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Measure.real, Measure.pi_singleton, ENNReal.toReal_prod, smul_eq_mul]
    rfl
  have hμ (f : α → ℝ) : ∫ t, f t ∂μ = ∑ t, w t * f t := by
    rw [integral_fintype Integrable.of_finite]
    rfl
  have hw1 : ∑ t, w t = 1 := by
    have := hμ (fun _ => 1)
    simpa using this.symm
  let e := Equiv.piSplitAt d (fun _ : R => α)
  have hsymm_d (t : α) (ρ' : {j // j ≠ d} → α) : e.symm (t, ρ') d = t := by
    simp [e, Equiv.piSplitAt_symm_apply]
  have hsymm_ne (t : α) (ρ' : {j // j ≠ d} → α) (j : {j // j ≠ d}) :
      e.symm (t, ρ') j = ρ' j := by
    simp [e, Equiv.piSplitAt_symm_apply, j.2]
  have hupd (t : α) (ρ' : {j // j ≠ d} → α) :
      e.symm (t, ρ') = Function.update (e.symm (s0, ρ')) d t := by
    funext j
    by_cases hj : j = d
    · subst hj
      simp [hsymm_d]
    · have := hsymm_ne t ρ' ⟨j, hj⟩
      have h2 := hsymm_ne s0 ρ' ⟨j, hj⟩
      simp only [Function.update_of_ne hj]
      rw [this, h2]
  have hprod (t : α) (ρ' : {j // j ≠ d} → α) :
      ∏ r, w (e.symm (t, ρ') r) = w t * ∏ j : {j // j ≠ d}, w (ρ' j) := by
    rw [Fintype.prod_eq_mul_prod_subtype_ne (fun r => w (e.symm (t, ρ') r)) d, hsymm_d]
    congr 1
    exact Finset.prod_congr rfl fun j _ => by rw [hsymm_ne]
  have hΦe (t t' : α) (ρ' : {j // j ≠ d} → α) :
      Φ (e.symm (t, ρ')) = Φ (e.symm (s0, ρ')) := by
    funext u
    rw [hupd t ρ']
    exact hΦ _ _ _
  rw [hpi, hpi, ← e.symm.sum_comp, ← e.symm.sum_comp]
  simp only [Fintype.sum_prod_type, hprod, hsymm_d, hμ]
  have h1 : ∀ (t : α) (ρ' : {j // j ≠ d} → α),
      (w t * ∏ j : {j // j ≠ d}, w (ρ' j)) * Φ (e.symm (t, ρ')) t =
        (w t * ∏ j : {j // j ≠ d}, w (ρ' j)) * Φ (e.symm (s0, ρ')) t := fun t ρ' => by
    rw [hΦe t t ρ']
  have h2 : ∀ (x : α) (x1 : {j // j ≠ d} → α), ∑ t, w t * Φ (e.symm (x, x1)) t =
      ∑ t, w t * Φ (e.symm (s0, x1)) t := fun x x1 => by rw [hΦe x x x1]
  simp only [h1, h2]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x1 _ => ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul, hw1, one_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

end MeasureTheory
