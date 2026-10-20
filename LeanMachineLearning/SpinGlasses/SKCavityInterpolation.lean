/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GibbsMeasure
public import LeanMachineLearning.SpinGlasses.SKReplicaSymmetricBound

/-!
# The finite Gibbs cavity identity

This module begins Talagrand's cavity-method formalization (Section 1.6) with the exact
last-spin calculation.  It deliberately introduces no cavity-system structure or custom Gibbs
measure: an energy on `α × ℤˣ` is written directly as `A a + ε * L a`, and the Gibbs law remains
`Measure.count.tilted`.

The reusable finite-fibre calculation is
`SpinGlasses.integral_count_tilted_fiber` in `GibbsMeasure.lean`.  The theorem below is its Ising
specialization, where summing the last spin produces `cosh`.  For the random cavity path, the
Gaussian replica derivative is already supplied by
`SpinGlasses.hasDerivAt_integral_replica_trig` in `GaussianInterpolationReplica.lean`; the later
path theorem should specialize that existing result rather than repeat Gaussian integration by
parts.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Real Matrix

namespace SpinGlasses

variable {α : Type*} [Finite α] [Nonempty α] [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- Summing a real-valued observable over the two Ising spins. -/
private theorem sum_int_units (F : ℤˣ → ℝ) : ∑ ε, F ε = F 1 + F (-1) := by
  change ∑ ε ∈ ({1, -1} : Finset ℤˣ), F ε = _
  simp

/-- **Finite Gibbs cavity identity.**  For any finite base configuration space `α`, an Ising
last-spin energy `ε ↦ ε L(a)` can be summed out exactly.  The numerator is the cavity average of
the observable weighted by the two possible last spins, and the denominator is the cavity average
of `cosh L`.  This is Proposition 1.6.1 before specializing `α` to the first `N` SK spins. -/
theorem integral_count_tilted_cavity_units (A L : α → ℝ) (f : α → ℤˣ → ℝ) :
    ∫ x : α × ℤˣ, f x.1 x.2
      ∂(Measure.count.tilted fun x => A x.1 + (x.2 : ℝ) * L x.1) =
      (∫ a, (f a 1 * Real.exp (L a) + f a (-1) * Real.exp (-L a)) / 2
        ∂(Measure.count.tilted A)) /
      (∫ a, Real.cosh (L a) ∂(Measure.count.tilted A)) := by
  let _ := Fintype.ofFinite α
  rw [integral_count_tilted_fiber A (fun a (ε : ℤˣ) => (ε : ℝ) * L a) f]
  simp_rw [sum_int_units]
  norm_num
  rw [integral_count_tilted, integral_count_tilted]
  simp_rw [Real.cosh_eq]
  let Z : ℝ := ∑ a, Real.exp (A a)
  let P : ℝ := ∑ a, Real.exp (A a) *
    (Real.exp (L a) * f a 1 + Real.exp (-L a) * f a (-1))
  let Q : ℝ := ∑ a, Real.exp (A a) * (Real.exp (L a) + Real.exp (-L a))
  change P / Q = _
  have hnum :
      (∑ a, Real.exp (A a) / Z *
        ((f a 1 * Real.exp (L a) + f a (-1) * Real.exp (-L a)) / 2)) =
        P / (Z * 2) := by
    calc
      _ = ∑ a, (Real.exp (A a) *
          (Real.exp (L a) * f a 1 + Real.exp (-L a) * f a (-1))) / (Z * 2) := by
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = _ := by rw [← Finset.sum_div]
  have hden :
      (∑ a, Real.exp (A a) / Z * ((Real.exp (L a) + Real.exp (-L a)) / 2)) =
        Q / (Z * 2) := by
    calc
      _ = ∑ a, (Real.exp (A a) * (Real.exp (L a) + Real.exp (-L a))) / (Z * 2) := by
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = _ := by rw [← Finset.sum_div]
  rw [show (∑ b, Real.exp (A b)) = Z by rfl, hnum, hden]
  have hZ : Z ≠ 0 := by
    dsimp [Z]
    positivity
  exact (div_div_div_cancel_right₀ (mul_ne_zero hZ two_ne_zero) P Q).symm

/-- **Last-coordinate form of the finite Gibbs cavity identity.**  This is
`integral_count_tilted_cavity_units` after the canonical `Fin.snoc` coordinate split.  It states
Proposition 1.6.1 on the actual SK configuration type, while retaining arbitrary base energy and
field.  The change of variables itself is the generic
`integral_count_tilted_equiv`, so other finite-spin models can use their own equivalence. -/
theorem integral_count_tilted_fin_snoc_cavity_units (N : ℕ)
    (A L : (Fin N → ℤˣ) → ℝ) (f : (Fin (N + 1) → ℤˣ) → ℝ) :
    ∫ σ, f σ ∂(Measure.count.tilted fun σ =>
      A (fun i => σ i.castSucc) + (σ (Fin.last N) : ℝ) * L (fun i => σ i.castSucc)) =
      (∫ ρ, (f (Fin.snoc ρ 1) * Real.exp (L ρ) +
          f (Fin.snoc ρ (-1)) * Real.exp (-L ρ)) / 2 ∂(Measure.count.tilted A)) /
        (∫ ρ, Real.cosh (L ρ) ∂(Measure.count.tilted A)) := by
  let e : ((Fin N → ℤˣ) × ℤˣ) ≃ (Fin (N + 1) → ℤˣ) :=
    (Equiv.prodComm (Fin N → ℤˣ) ℤˣ).trans (Fin.snocEquiv fun _ => ℤˣ)
  rw [integral_count_tilted_equiv e _ f]
  simp only [e, Equiv.trans_apply, Equiv.prodComm_apply, Fin.snocEquiv_apply,
    Fin.snoc_castSucc, Fin.snoc_last]
  change ∫ x : (Fin N → ℤˣ) × ℤˣ, f (Fin.snoc x.1 x.2)
    ∂(Measure.count.tilted fun x => A x.1 + (x.2 : ℝ) * L x.1) = _
  exact integral_count_tilted_cavity_units A L fun ρ ε => f (Fin.snoc ρ ε)

/-- **Covariance of the interacting last-spin cavity field.**  The field
`ε β M^{-1/2} ∑ᵢ gᵢ ρᵢ` has covariance
`β² ε ε' M⁻¹ (ρ · ρ')`.  In the `(N+1)`-spin SK model take `M = N+1`;
thus the first `N` spins are normalized by the total number of spins.  The proof is only a
coefficient reindexing of the generic
Gaussian linear-form covariance, so it applies without choosing an SK Hamiltonian or a Gibbs
measure. -/
theorem integral_last_spin_cavity_field_mul (N : ℕ) (M β : ℝ) (hM : 0 ≤ M)
    (σ τ : Fin (N + 1) → ℤˣ) :
    ∫ g : Fin N → ℝ,
      ((Real.sqrt M)⁻¹ * β * (σ (Fin.last N) : ℝ) *
        ∑ i, g i * (σ i.castSucc : ℝ)) *
      ((Real.sqrt M)⁻¹ * β * (τ (Fin.last N) : ℝ) *
        ∑ i, g i * (τ i.castSucc : ℝ))
      ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      β ^ 2 * (σ (Fin.last N) : ℝ) * (τ (Fin.last N) : ℝ) *
        (M⁻¹ *
          ((fun i : Fin N => (σ i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (τ i.castSucc : ℝ))) := by
  let a : Fin N → ℝ := fun i => (σ (Fin.last N) : ℝ) * (σ i.castSucc : ℝ)
  let b : Fin N → ℝ := fun i => (τ (Fin.last N) : ℝ) * (τ i.castSucc : ℝ)
  have hmain := integral_normalized_gaussian_linear_form_mul M β hM a b
  have hab : a ⬝ᵥ b = (σ (Fin.last N) : ℝ) * (τ (Fin.last N) : ℝ) *
      ((fun i : Fin N => (σ i.castSucc : ℝ)) ⬝ᵥ
        fun i : Fin N => (τ i.castSucc : ℝ)) := by
    simp only [a, b, dotProduct]
    calc
      _ = ∑ i : Fin N, ((σ (Fin.last N) : ℝ) * (τ (Fin.last N) : ℝ)) *
          ((σ i.castSucc : ℝ) * (τ i.castSucc : ℝ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [Finset.mul_sum]
  rw [hab] at hmain
  simpa only [a, b, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using hmain

end SpinGlasses
