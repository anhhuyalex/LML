/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GibbsReplicaMarginal

/-!
# Centering one replica of an i.i.d. Gibbs sample

For independent replicas `σ¹, …, σᵐ` of a Gibbs measure on a finite space, a replica `σˡ` whose
coordinates `z_j(σˡ)` have Gibbs mean zero is orthogonal to everything that does not depend on
`σˡ`: `E[H · ∑_j z_j(σˡ) c_j] = 0` whenever `H` and the `c_j` do not depend on the `ℓ`-th replica.
This is the single elementary mechanism behind the parity vanishing of Theorem 1.7.11
(`GibbsProjectionFluctuation.lean`) and the orthogonality relations of Propositions 1.8.8 and
(1.257) (`GibbsTBasisOrthogonality.lean`); it needs neither Gaussian disorder nor any model.

## Main declarations

* `SpinGlasses.sum_prod_weight_mul_linear_eq_zero`: the finite-sum form.
* `SpinGlasses.integral_pi_centered_replica_eq_zero`: the form for the replica product measure.
-/

@[expose] public section

open MeasureTheory Finset

namespace SpinGlasses

/-- Inserting `a` at `ℓ` is updating the value inserted at `ℓ`. -/
theorem insertNth_eq_update {α : Type*} {n : ℕ} (ℓ : Fin (n + 1)) (a b : α) (σ : Fin n → α) :
    Fin.insertNth (α := fun _ => α) ℓ a σ =
      Function.update (Fin.insertNth (α := fun _ => α) ℓ b σ) ℓ a := by
  funext i
  refine Fin.succAboveCases ℓ ?_ ?_ i
  · simp
  · intro j
    simp

/-- **Single centered replica, finite-sum form.** -/
theorem sum_prod_weight_mul_linear_eq_zero {α : Type*} [Fintype α] {n N : ℕ} (w : α → ℝ)
    (ℓ : Fin (n + 1)) (z : Fin N → α → ℝ) (hz : ∀ j, ∑ a, w a * z j a = 0)
    (H : (Fin (n + 1) → α) → ℝ) (c : Fin N → (Fin (n + 1) → α) → ℝ)
    (hH : ∀ σ a, H (Function.update σ ℓ a) = H σ)
    (hc : ∀ j σ a, c j (Function.update σ ℓ a) = c j σ) :
    ∑ σ : Fin (n + 1) → α, (∏ r, w (σ r)) * (H σ * ∑ j, z j (σ ℓ) * c j σ) = 0 := by
  rw [← (Fin.insertNthEquiv (fun _ => α) ℓ).sum_comp, Fintype.sum_prod_type_right]
  refine Finset.sum_eq_zero fun σ' _ => ?_
  rcases isEmpty_or_nonempty α with hα | ⟨⟨x₀⟩⟩
  · simp
  have hins : ∀ x, (Fin.insertNthEquiv (fun _ => α) ℓ) (x, σ') =
      Function.update ((Fin.insertNthEquiv (fun _ => α) ℓ) (x₀, σ')) ℓ x := fun x =>
    insertNth_eq_update ℓ x x₀ σ'
  have hH' : ∀ x, H ((Fin.insertNthEquiv (fun _ => α) ℓ) (x, σ')) =
      H ((Fin.insertNthEquiv (fun _ => α) ℓ) (x₀, σ')) := fun x => by rw [hins x, hH]
  have hc' : ∀ j x, c j ((Fin.insertNthEquiv (fun _ => α) ℓ) (x, σ')) =
      c j ((Fin.insertNthEquiv (fun _ => α) ℓ) (x₀, σ')) := fun j x => by rw [hins x, hc]
  have hprod : ∀ x, ∏ r, w ((Fin.insertNthEquiv (fun _ => α) ℓ) (x, σ') r) =
      w x * ∏ j, w (σ' j) := fun x => by
    rw [Fin.prod_univ_succAbove _ ℓ]
    simp
  have hz' : ∀ x, ((Fin.insertNthEquiv (fun _ => α) ℓ) (x, σ')) ℓ = x := fun x => by simp
  simp only [hH', hc', hprod, hz']
  have : ∀ x, w x * (∏ j, w (σ' j)) * (H ((Fin.insertNthEquiv (fun _ => α) ℓ) (x₀, σ')) *
      ∑ j, z j x * c j ((Fin.insertNthEquiv (fun _ => α) ℓ) (x₀, σ'))) =
      (∏ j, w (σ' j)) * H ((Fin.insertNthEquiv (fun _ => α) ℓ) (x₀, σ')) *
        ∑ j, (w x * z j x) * c j ((Fin.insertNthEquiv (fun _ => α) ℓ) (x₀, σ')) := fun x => by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [this]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.sum_mul, hz, zero_mul, Finset.sum_const_zero, mul_zero]

set_option linter.unusedFintypeInType false in
/-- **Single centered replica.** For `m` independent replicas of `count.tilted f`, if the
coordinates `z j` of replica `ℓ` have Gibbs mean zero and `H`, `c j` do not depend on replica `ℓ`,
then `E[H · ∑_j z_j(σˡ) c_j] = 0`. -/
theorem integral_pi_centered_replica_eq_zero {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {m N : ℕ} (f : α → ℝ) (ℓ : Fin m) (z : Fin N → α → ℝ)
    (hz : ∀ j, ∫ a, z j a ∂(Measure.count.tilted f) = 0)
    (H : (Fin m → α) → ℝ) (c : Fin N → (Fin m → α) → ℝ)
    (hH : ∀ σ a, H (Function.update σ ℓ a) = H σ)
    (hc : ∀ j σ a, c j (Function.update σ ℓ a) = c j σ) :
    ∫ σ : Fin m → α, H σ * ∑ j, z j (σ ℓ) * c j σ
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted f) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := Nat.exists_eq_succ_of_ne_zero (Fin.pos ℓ).ne'
  rw [integral_pi_count_tilted]
  refine sum_prod_weight_mul_linear_eq_zero (fun a => Real.exp (f a) / ∑ b, Real.exp (f b)) ℓ z
    (fun j => ?_) H c hH hc
  have := hz j
  rw [integral_fintype Integrable.of_finite] at this
  rw [← this]
  exact Finset.sum_congr rfl fun a _ => by rw [real_count_tilted_singleton, smul_eq_mul]

end SpinGlasses
