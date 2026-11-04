/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GibbsCentering

/-!
# Orthogonality of the `T`-basis (Talagrand, Proposition 1.8.8 and Eq. (1.257))

Let `b = ⟨σ⟩` be the mean of a Gibbs measure `count.tilted A` on `Fin M → ℤˣ`, and for replicas
`σ¹, σ², …` of the Gibbs measure put
`T_{st} = M⁻¹ ∑_i (σˢ_i - b_i)(σᵗ_i - b_i)` (`s ≠ t`), `T_s = M⁻¹ ∑_i (σˢ_i - b_i) b_i`, and
`T = M⁻¹ ∑_i b_i² - q`, which does not depend on the replicas.  Every product of two different
elements of this family has Gibbs average zero, because some replica occurs in one factor only and
that replica is centered (`integral_pi_centered_replica_eq_zero`).

## Main declarations

* `SpinGlasses.integral_T_pair_mul_T_pair_of_share`, `..._of_disjoint`: `⟨T_{st} T_{su}⟩ = 0`
  and `⟨T_{st} T_{uv}⟩ = 0` (Proposition 1.8.8).
* `SpinGlasses.integral_T_pair_mul_T_one`, `integral_T_pair_mul_const`:
  `⟨T_{st} T_u⟩ = 0` and `⟨T_{st} T⟩ = 0`.
* `SpinGlasses.integral_T_one_mul_T_one`, `integral_T_one_mul_const`: `⟨T_s T_t⟩ = 0` and
  `⟨T_s T⟩ = 0` (Eq. (1.257)).

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Proposition 1.8.8 and
  Eq. (1.257).
-/

@[expose] public section

open MeasureTheory Finset
open scoped BigOperators

namespace SpinGlasses

variable {M m : ℕ} (A : (Fin M → ℤˣ) → ℝ) (b : Fin M → ℝ)
  (hb : ∀ i, b i = ∫ y : Fin M → ℤˣ, ((y i : ℤˣ) : ℝ) ∂(Measure.count.tilted A))

include hb in
/-- The coordinates `σ_i - b_i` of a spin configuration have Gibbs mean zero. -/
theorem integral_spin_sub_mean (i : Fin M) :
    ∫ x : Fin M → ℤˣ, (((x i : ℤˣ) : ℝ) - b i) ∂(Measure.count.tilted A) = 0 := by
  rw [integral_sub Integrable.of_finite (integrable_const _), ← hb i]
  simp

include hb in
/-- **A centered replica against another replica.** If `H` does not depend on replica `ℓ` and
`s ≠ ℓ`, then `⟨M⁻¹ ∑_i (σˡ_i - b_i)(σˢ_i - b_i) · H⟩ = 0`. -/
theorem integral_dev_dot_dev_mul_eq_zero (ℓ s : Fin m) (hsℓ : s ≠ ℓ)
    (H : (Fin m → Fin M → ℤˣ) → ℝ)
    (hH : ∀ τ x, H (Function.update τ ℓ x) = H τ) :
    ∫ τ : Fin m → Fin M → ℤˣ, ((M : ℝ)⁻¹ * ∑ i, (((τ ℓ i : ℤˣ) : ℝ) - b i) *
        (((τ s i : ℤˣ) : ℝ) - b i)) * H τ
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted A) = 0 := by
  have h := integral_pi_centered_replica_eq_zero A ℓ
    (fun i x => ((x i : ℤˣ) : ℝ) - b i) (integral_spin_sub_mean A b hb) H
    (fun i τ => (M : ℝ)⁻¹ * (((τ s i : ℤˣ) : ℝ) - b i)) hH
    (fun i τ x => by simp [Function.update_of_ne hsℓ])
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

include hb in
/-- **A centered replica against the Gibbs mean.** If `H` does not depend on replica `ℓ`, then
`⟨M⁻¹ ∑_i (σˡ_i - b_i) b_i · H⟩ = 0`. -/
theorem integral_dev_dot_mean_mul_eq_zero (ℓ : Fin m) (H : (Fin m → Fin M → ℤˣ) → ℝ)
    (hH : ∀ τ x, H (Function.update τ ℓ x) = H τ) :
    ∫ τ : Fin m → Fin M → ℤˣ, ((M : ℝ)⁻¹ * ∑ i, (((τ ℓ i : ℤˣ) : ℝ) - b i) * b i) * H τ
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted A) = 0 := by
  have h := integral_pi_centered_replica_eq_zero A ℓ
    (fun i x => ((x i : ℤˣ) : ℝ) - b i) (integral_spin_sub_mean A b hb) H
    (fun i _ => (M : ℝ)⁻¹ * b i) hH (fun i τ x => rfl)
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

include hb in
/-- **Proposition 1.8.8:** `⟨T_{st} T_{su}⟩ = 0` for three distinct replicas. -/
theorem integral_T_pair_mul_T_pair_of_share {s t u : Fin m} (hst : s ≠ t) (hut : u ≠ t) :
    ∫ τ : Fin m → Fin M → ℤˣ, ((M : ℝ)⁻¹ * ∑ i, (((τ t i : ℤˣ) : ℝ) - b i) *
        (((τ s i : ℤˣ) : ℝ) - b i)) *
      ((M : ℝ)⁻¹ * ∑ i, (((τ s i : ℤˣ) : ℝ) - b i) * (((τ u i : ℤˣ) : ℝ) - b i))
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted A) = 0 := by
  refine integral_dev_dot_dev_mul_eq_zero A b hb t s hst _ fun τ x => ?_
  simp [Function.update_of_ne hst, Function.update_of_ne hut]

include hb in
/-- **Proposition 1.8.8:** `⟨T_{st} T_{uv}⟩ = 0` for four distinct replicas. -/
theorem integral_T_pair_mul_T_pair_of_disjoint {s t u v : Fin m} (hst : s ≠ t) (hut : u ≠ t)
    (hvt : v ≠ t) :
    ∫ τ : Fin m → Fin M → ℤˣ, ((M : ℝ)⁻¹ * ∑ i, (((τ t i : ℤˣ) : ℝ) - b i) *
        (((τ s i : ℤˣ) : ℝ) - b i)) *
      ((M : ℝ)⁻¹ * ∑ i, (((τ u i : ℤˣ) : ℝ) - b i) * (((τ v i : ℤˣ) : ℝ) - b i))
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted A) = 0 := by
  refine integral_dev_dot_dev_mul_eq_zero A b hb t s hst _ fun τ x => ?_
  simp [Function.update_of_ne hut, Function.update_of_ne hvt]

include hb in
/-- **Proposition 1.8.8:** `⟨T_{st} T_u⟩ = 0` when `u ≠ t`. -/
theorem integral_T_pair_mul_T_one {s t u : Fin m} (hst : s ≠ t) (hut : u ≠ t) :
    ∫ τ : Fin m → Fin M → ℤˣ, ((M : ℝ)⁻¹ * ∑ i, (((τ t i : ℤˣ) : ℝ) - b i) *
        (((τ s i : ℤˣ) : ℝ) - b i)) *
      ((M : ℝ)⁻¹ * ∑ i, (((τ u i : ℤˣ) : ℝ) - b i) * b i)
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted A) = 0 := by
  refine integral_dev_dot_dev_mul_eq_zero A b hb t s hst _ fun τ x => ?_
  simp [Function.update_of_ne hut]

include hb in
/-- **Proposition 1.8.8:** `⟨T_{st} T⟩ = 0` for any constant `T` (here `T = c`). -/
theorem integral_T_pair_mul_const {s t : Fin m} (hst : s ≠ t) (c : ℝ) :
    ∫ τ : Fin m → Fin M → ℤˣ, ((M : ℝ)⁻¹ * ∑ i, (((τ t i : ℤˣ) : ℝ) - b i) *
        (((τ s i : ℤˣ) : ℝ) - b i)) * c
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted A) = 0 :=
  integral_dev_dot_dev_mul_eq_zero A b hb t s hst (fun _ => c) fun _ _ => rfl

include hb in
/-- **Eq. (1.257):** `⟨T_s T_t⟩ = 0` for two different replicas. -/
theorem integral_T_one_mul_T_one {s t : Fin m} (hts : t ≠ s) :
    ∫ τ : Fin m → Fin M → ℤˣ, ((M : ℝ)⁻¹ * ∑ i, (((τ s i : ℤˣ) : ℝ) - b i) * b i) *
      ((M : ℝ)⁻¹ * ∑ i, (((τ t i : ℤˣ) : ℝ) - b i) * b i)
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted A) = 0 := by
  refine integral_dev_dot_mean_mul_eq_zero A b hb s _ fun τ x => ?_
  simp [Function.update_of_ne hts]

include hb in
/-- **Eq. (1.257):** `⟨T_s T⟩ = 0` for any constant `T` (here `T = c`). -/
theorem integral_T_one_mul_const (s : Fin m) (c : ℝ) :
    ∫ τ : Fin m → Fin M → ℤˣ, ((M : ℝ)⁻¹ * ∑ i, (((τ s i : ℤˣ) : ℝ) - b i) * b i) * c
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted A) = 0 :=
  integral_dev_dot_mean_mul_eq_zero A b hb s (fun _ => c) fun _ _ => rfl

end SpinGlasses
