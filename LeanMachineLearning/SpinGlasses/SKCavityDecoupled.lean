/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GaussianIBP
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.HypercubeProduct

/-!
# Decoupled last spin (Talagrand's Lemma 1.6.2, finite form)

When the energy is `A a + ε Y` with a constant field `Y` on the last spin, the replicas split:
the last spins are independent of the rest, and each carries mean `tanh Y`.
-/

@[expose] public section

open MeasureTheory Finset

namespace SpinGlasses

/-- Reindexing the configuration space along an equivalence transports an `R`-replica Gibbs
average. -/
theorem integral_pi_count_tilted_equiv {β γ R : Type*} [Finite β] [Finite γ] [Fintype R]
    [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace γ]
    [MeasurableSingletonClass γ] (e : β ≃ γ) (f : γ → ℝ) (Ψ : (R → γ) → ℝ) :
    ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted f) =
      ∫ σ : R → β, Ψ (fun r => e (σ r))
        ∂(Measure.pi fun _ : R => Measure.count.tilted fun b => f (e b)) := by
  classical
  have := Fintype.ofFinite β
  have := Fintype.ofFinite γ
  rw [integral_pi_count_tilted, integral_pi_count_tilted]
  have hZ : (∑ b : β, Real.exp (f (e b))) = ∑ c : γ, Real.exp (f c) :=
    e.sum_comp fun c => Real.exp (f c)
  simp_rw [hZ]
  exact ((Equiv.piCongrRight fun _ : R => e).sum_comp fun σ : R → γ =>
    (∏ r, Real.exp (f (σ r)) / ∑ c : γ, Real.exp (f c)) * Ψ σ).symm

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
  have hZA0 : 0 < ZA := Finset.sum_pos (fun a _ => Real.exp_pos _) Finset.univ_nonempty
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
  congr 1
  sorry

end SpinGlasses
