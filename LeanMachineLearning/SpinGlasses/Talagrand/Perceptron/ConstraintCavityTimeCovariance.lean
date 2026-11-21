/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityCovariance
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathDifferentiation

/-!
# Time covariances of the smart-path fields (2.60)

Exercise 2.3.3 of Talagrand's Section 2.3. Each field `S^ℓ_{k,t}(σ)` is a linear form in the
Gaussian vector `(g_{·,k}, g_k, ξ_k^ℓ)` indexed by `(Fin N ⊕ Unit) ⊕ R`, with coefficient vector
`Sum.elim (cavityCoef N t σ) (Pi.single ℓ √((1 - t)/(N + 1)))`. Its time derivative
`S'^ℓ_{k,t} = (2 √(N+1))⁻¹ (g_k ε_ℓ / √t - ξ_k^ℓ / √(1-t))` (the book's
`S_{k,t}^{ℓ \prime}`) is the linear form with coefficient vector
`Sum.elim (Sum.elim 0 (ε_σ / (2 √(N+1) √t))) (Pi.single ℓ (-1 / (2 √(N+1) √(1-t))))`
(`hasDerivAt_cavityTimeCoef`). The relations (2.60) are the dot products of these vectors:
`E S'^ℓ S^ℓ = 0`, `E S'^ℓ S^{ℓ'} = ε_ℓ ε_{ℓ'} / (2 (N+1))` for `ℓ ≠ ℓ'`. For distinct constraints
`k ≠ k'` the forms involve disjoint independent coordinates, so their covariance vanishes.

* `SpinGlasses.cavityTimeCoef_dotProduct`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

variable {N : ℕ} {t : ℝ} {R : Type*} [Fintype R] [DecidableEq R]

/-- **Relations (2.60) as dot products of coefficient vectors.** For `t ∈ (0,1)`,
`S'^ℓ_σ ⬝ S^{ℓ'}_τ = (ε_σ ε_τ - 1_{ℓ = ℓ'}) / (2 (N + 1))`. -/
theorem cavityTimeCoef_dotProduct (ht : t ∈ Set.Ioo (0 : ℝ) 1) (σ τ : PerceptronSpin N)
    (ℓ ℓ' : R) :
    (Sum.elim (Sum.elim (fun _ : Fin N => (0 : ℝ))
        (fun _ : Unit => ((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t)))
      (Pi.single ℓ (-1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t)))) :
        (Fin N ⊕ Unit) ⊕ R → ℝ) ⬝ᵥ
    (Sum.elim (cavityCoef N t τ) (Pi.single ℓ' (Real.sqrt ((1 - t) / (N + 1)))) :
        (Fin N ⊕ Unit) ⊕ R → ℝ) =
      (((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ) - if ℓ = ℓ' then 1 else 0) / (2 * (N + 1)) := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  have hsN : 0 < Real.sqrt (N + 1 : ℕ) := Real.sqrt_pos.2 (by exact_mod_cast Nat.succ_pos N)
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
  have hs1 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 (sub_pos.2 ht.2)
  have e1 : Real.sqrt (t / (N + 1)) = Real.sqrt t / Real.sqrt (N + 1 : ℕ) := by
    rw [Real.sqrt_div' _ hN.le]; push_cast; rfl
  have e2 : Real.sqrt ((1 - t) / (N + 1)) = Real.sqrt (1 - t) / Real.sqrt (N + 1 : ℕ) := by
    rw [Real.sqrt_div' _ hN.le]; push_cast; rfl
  have e3 : Real.sqrt (N + 1 : ℕ) * Real.sqrt (N + 1 : ℕ) = N + 1 := by
    rw [Real.mul_self_sqrt (by positivity)]; push_cast; rfl
  have hR : ∀ D E : ℝ, ∑ r : R, (Pi.single ℓ D : R → ℝ) r * (Pi.single ℓ' E : R → ℝ) r =
      if ℓ = ℓ' then D * E else 0 := fun D E => by
    by_cases h : ℓ = ℓ'
    · subst h
      simp [Pi.single_apply]
    · simp only [h, ite_false]
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : r = ℓ
      · subst hr
        simp [Ne.symm h]
      · simp [Pi.single_apply, hr]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, cavityCoef,
    Finset.univ_unique, Finset.sum_const, Finset.card_singleton, one_smul, zero_mul,
    smul_zero, zero_add, hR]
  have e4 : Real.sqrt (N + 1 : ℕ) ^ 2 = N + 1 := by rw [sq, e3]
  rw [e1, e2]
  split_ifs with h
  · field_simp
    rw [e4]
    ring
  · field_simp
    rw [e4]
    ring

/-- **The coefficient vector of `S'` is the time derivative of that of `S`** (for `t ∈ (0,1)`):
coordinatewise, the derivative of `t ↦ cavityCoef N t σ` is `0` on the old couplings and
`ε_σ / (2 √(N+1) √t)` on `g_{N,M}`, and that of the `ξ`-coefficient `√((1-t)/(N+1))` is
`-1 / (2 √(N+1) √(1-t))`. -/
theorem hasDerivAt_cavityTimeCoef (ht : t ∈ Set.Ioo (0 : ℝ) 1) (σ : PerceptronSpin N) :
    (∀ i : Fin N, HasDerivAt (fun t => cavityCoef N t σ (Sum.inl i)) 0 t) ∧
    HasDerivAt (fun t => cavityCoef N t σ (Sum.inr ()))
      (((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t)) t ∧
    HasDerivAt (fun t => Real.sqrt ((1 - t) / (N + 1)))
      (-1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t))) t := by
  have hL : (0 : ℝ) ≤ N + 1 := by positivity
  have hsN : 0 < Real.sqrt (N + 1 : ℕ) := Real.sqrt_pos.2 (by exact_mod_cast Nat.succ_pos N)
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht.1
  have hs1 : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 (sub_pos.2 ht.2)
  refine ⟨fun i => by simpa [cavityCoef] using hasDerivAt_const t _, ?_, ?_⟩
  · have hp := (Real.hasDerivAt_sqrt_div_const hL ht.1.ne').mul_const ((σ.2 : ℤ) : ℝ)
    refine (by simpa [cavityCoef] using hp : HasDerivAt _ _ t).congr_deriv ?_
    push_cast
    field_simp
  · have hm := (Real.hasDerivAt_sqrt_div_const hL (sub_pos.mpr ht.2).ne').comp t
      ((hasDerivAt_id t).const_sub 1)
    refine hm.congr_deriv ?_
    push_cast
    field_simp

/-- **(2.60), same replica:** `E S'^ℓ S^ℓ = 0`. -/
theorem cavityTimeCoef_dotProduct_self (ht : t ∈ Set.Ioo (0 : ℝ) 1) (σ : PerceptronSpin N)
    (ℓ : R) :
    (Sum.elim (Sum.elim (fun _ : Fin N => (0 : ℝ))
        (fun _ : Unit => ((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t)))
      (Pi.single ℓ (-1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t)))) :
        (Fin N ⊕ Unit) ⊕ R → ℝ) ⬝ᵥ
    (Sum.elim (cavityCoef N t σ) (Pi.single ℓ (Real.sqrt ((1 - t) / (N + 1)))) :
        (Fin N ⊕ Unit) ⊕ R → ℝ) = 0 := by
  rw [cavityTimeCoef_dotProduct ht]
  simp [← sq, units_cast_sq]

/-- **(2.60), distinct replicas:** `E S'^ℓ S^{ℓ'} = ε_σ ε_τ / (2 (N + 1))` for `ℓ ≠ ℓ'`. -/
theorem cavityTimeCoef_dotProduct_of_ne (ht : t ∈ Set.Ioo (0 : ℝ) 1) (σ τ : PerceptronSpin N)
    {ℓ ℓ' : R} (h : ℓ ≠ ℓ') :
    (Sum.elim (Sum.elim (fun _ : Fin N => (0 : ℝ))
        (fun _ : Unit => ((σ.2 : ℤ) : ℝ) / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt t)))
      (Pi.single ℓ (-1 / (2 * Real.sqrt (N + 1 : ℕ) * Real.sqrt (1 - t)))) :
        (Fin N ⊕ Unit) ⊕ R → ℝ) ⬝ᵥ
    (Sum.elim (cavityCoef N t τ) (Pi.single ℓ' (Real.sqrt ((1 - t) / (N + 1)))) :
        (Fin N ⊕ Unit) ⊕ R → ℝ) =
      ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ) / (2 * (N + 1)) := by
  rw [cavityTimeCoef_dotProduct ht]
  simp [h]

end SpinGlasses
