/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GibbsReplicaMarginal
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.HypercubeProduct

/-!
# Decoupled last spin (Talagrand's Lemma 1.6.2, finite form)

When the energy is `A a + ε Y` with a constant field `Y` on the last spin, the replicas split:
the last spins are independent of the rest, and each carries mean `tanh Y`.
-/

@[expose] public section

open MeasureTheory Finset

namespace SpinGlasses

/-- **Decoupled last spin.** For the energy `A a + ε Y` on `α × ℤˣ`, an observable that is a
function of the `α`-coordinates times the product of the last spins over `I` has replica average
`(tanh Y)^|I|` times the average of the `α`-observable under the energy `A`. -/
theorem integral_pi_count_tilted_decoupled_spin {α : Type*} [Finite α] [Nonempty α]
    [MeasurableSpace α]
    [MeasurableSingletonClass α] {n : ℕ} (A : α → ℝ) (Y : ℝ) (F : (Fin n → α) → ℝ)
    (I : Finset (Fin n)) :
    ∫ σ : Fin n → α × ℤˣ, F (fun r => (σ r).1) * ∏ r ∈ I, (((σ r).2 : ℤˣ) : ℝ)
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        fun x : α × ℤˣ => A x.1 + ((x.2 : ℤˣ) : ℝ) * Y) =
      Real.tanh Y ^ I.card * ∫ ρ, F ρ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted A) := by
  classical
  have := Fintype.ofFinite α
  rw [integral_pi_count_tilted, integral_pi_count_tilted]
  set ZA : ℝ := ∑ a, Real.exp (A a) with hZA
  set c : ℝ := Real.exp Y + Real.exp (-Y) with hc
  have hc0 : 0 < c := by positivity
  have hZ : (∑ x : α × ℤˣ, Real.exp (A x.1 + ((x.2 : ℤˣ) : ℝ) * Y)) = ZA * c := by
    rw [Fintype.sum_prod_type]
    simp_rw [sum_units_int, Real.exp_add, ← mul_add, ← Finset.sum_mul]
    simp [hc, hZA]
  simp_rw [hZ]
  let e := Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => α) fun _ => ℤˣ
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  have hw (a : Fin n → α) (ε : Fin n → ℤˣ) :
      (∏ r, Real.exp (A (e.symm (a, ε) r).1 + (((e.symm (a, ε) r).2 : ℤˣ) : ℝ) * Y) / (ZA * c)) *
        (F (fun r => (e.symm (a, ε) r).1) * ∏ r ∈ I, (((e.symm (a, ε) r).2 : ℤˣ) : ℝ)) =
      ((∏ r, Real.exp (A (a r)) / ZA) * F a) *
        ((∏ r, Real.exp ((ε r : ℝ) * Y) / c) * ∏ r ∈ I, ((ε r : ℤˣ) : ℝ)) := by
    simp only [e, Equiv.arrowProdEquivProdArrow_symm_apply]
    simp_rw [Real.exp_add, mul_div_mul_comm, Finset.prod_mul_distrib]
    ring
  simp_rw [hw, ← Finset.sum_mul_sum]
  rw [mul_comm (Real.tanh Y ^ I.card)]
  congr 1
  have hε : ∀ ε : Fin n → ℤˣ, (∏ r, Real.exp ((ε r : ℝ) * Y) / c) * ∏ r ∈ I, ((ε r : ℤˣ) : ℝ) =
      ∏ r, (Real.exp ((ε r : ℝ) * Y) / c * if r ∈ I then ((ε r : ℤˣ) : ℝ) else 1) := fun ε => by
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.univ_inter]
  simp_rw [hε]
  rw [hypercube_sum_prod_eq_prod_add
    (fun (r : Fin n) (s : ℤˣ) => Real.exp ((s : ℝ) * Y) / c * if r ∈ I then ((s : ℤˣ) : ℝ) else 1)]
  have htanh : Real.tanh Y = (Real.exp Y - Real.exp (-Y)) / c := by
    rw [hc, Real.tanh_eq]
  have hr : ∀ r : Fin n, (Real.exp (((1 : ℤˣ) : ℝ) * Y) / c *
        (if r ∈ I then (((1 : ℤˣ) : ℤ) : ℝ) else 1) +
      Real.exp (((-1 : ℤˣ) : ℝ) * Y) / c * (if r ∈ I then (((-1 : ℤˣ) : ℤ) : ℝ) else 1)) =
      if r ∈ I then Real.tanh Y else 1 := fun r => by
    by_cases hr : r ∈ I
    · simp only [hr, ite_true, htanh]
      simp
      ring
    · simp only [hr, ite_false]
      simp
      field_simp
      exact hc.symm
  simp_rw [hr]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

end SpinGlasses
