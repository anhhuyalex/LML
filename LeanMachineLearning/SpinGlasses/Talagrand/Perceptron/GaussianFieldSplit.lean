/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.GaussianFields
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Splitting off the last coordinate of a perceptron field

The full field on `N + 1` spins equals its old-coordinate sum plus the last-coordinate term,
with denominator `sqrt (N + 1)` in both parts. The Gaussian marginal, overlap covariance,
product integrability and independent-column laws are transferred from `GaussianFields` by
this identity; no Gaussian moment calculation is repeated. The case `N = 0` is one full spin.
These laws concern deterministic spins under the prior disorder, not Gibbs-sampled spins.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SpinGlasses

/-- The normalized full field splits into old and last coordinates, both normalized by the
full size `N + 1`. This also holds when there are no old coordinates. -/
theorem normalized_constraint_field_snoc {N : ℕ} (σ : Fin N → ℤˣ) (ε : ℤˣ)
    (x : Fin (N + 1) → ℝ) :
    (Real.sqrt (N + 1 : ℕ))⁻¹ *
        ∑ i, x i * (((Fin.snoc (α := fun _ : Fin (N + 1) => ℤˣ) σ ε) i : ℤˣ) : ℝ) =
      (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, x i.castSucc * ((σ i : ℤ) : ℝ)) +
        (Real.sqrt (N + 1 : ℕ))⁻¹ * x (Fin.last N) * ((ε : ℤ) : ℝ) := by
  simp [Fin.sum_univ_castSucc, mul_add, mul_assoc]

/-- The split field of a fixed spin has the standard normal law, including one full spin. -/
theorem map_split_constraint_field_eq_gaussianReal {N : ℕ} (σ : Fin N → ℤˣ) (ε : ℤˣ) :
    (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).map
      (fun x => (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, x i.castSucc * ((σ i : ℤ) : ℝ)) +
        (Real.sqrt (N + 1 : ℕ))⁻¹ * x (Fin.last N) * ((ε : ℤ) : ℝ)) = gaussianReal 0 1 := by
  simpa only [normalized_constraint_field_snoc] using
    map_normalized_constraint_field_eq_gaussianReal (Nat.succ_pos N) (Fin.snoc σ ε)

/-- The covariance of two split fields is the full overlap, including the last spin. -/
theorem integral_split_constraint_field_mul_eq {N : ℕ} (σ τ : Fin N → ℤˣ) (ε δ : ℤˣ) :
    ∫ x : Fin (N + 1) → ℝ,
      ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, x i.castSucc * ((σ i : ℤ) : ℝ)) +
        (Real.sqrt (N + 1 : ℕ))⁻¹ * x (Fin.last N) * ((ε : ℤ) : ℝ)) *
      ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, x i.castSucc * ((τ i : ℤ) : ℝ)) +
        (Real.sqrt (N + 1 : ℕ))⁻¹ * x (Fin.last N) * ((δ : ℤ) : ℝ))
      ∂(Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) =
        (N + 1 : ℝ)⁻¹ * ((∑ i, ((σ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ)) +
          ((ε : ℤ) : ℝ) * ((δ : ℤ) : ℝ)) := by
  simpa only [normalized_constraint_field_snoc, Fintype.card_fin, Nat.cast_add, Nat.cast_one,
    dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, mul_add, mul_assoc] using
    integral_normalized_constraint_field_mul_eq (Fin.snoc σ ε) (Fin.snoc τ δ)

/-- The split fields of fixed spins in independent constraint rows have the product standard
normal law. An empty constraint index set is allowed. -/
theorem map_split_constraint_fields_eq_pi_gaussianReal {N M : ℕ}
    (σ : Fin M → Fin N → ℤˣ) (ε : Fin M → ℤˣ) :
    (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).map
      (fun g k => (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, g k i.castSucc * ((σ k i : ℤ) : ℝ)) +
        (Real.sqrt (N + 1 : ℕ))⁻¹ * g k (Fin.last N) * ((ε k : ℤ) : ℝ)) =
      Measure.pi fun _ : Fin M => gaussianReal 0 1 := by
  simpa only [normalized_constraint_field_snoc] using
    map_normalized_constraint_fields_eq_pi_gaussianReal (Nat.succ_pos N)
      (fun k => Fin.snoc (σ k) (ε k))

/-- The product of two split fields is Bochner integrable under the full Gaussian row law. -/
theorem integrable_split_constraint_field_mul {N : ℕ} (σ τ : Fin N → ℤˣ) (ε δ : ℤˣ) :
    Integrable (fun x : Fin (N + 1) → ℝ =>
      ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, x i.castSucc * ((σ i : ℤ) : ℝ)) +
        (Real.sqrt (N + 1 : ℕ))⁻¹ * x (Fin.last N) * ((ε : ℤ) : ℝ)) *
      ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, x i.castSucc * ((τ i : ℤ) : ℝ)) +
        (Real.sqrt (N + 1 : ℕ))⁻¹ * x (Fin.last N) * ((δ : ℤ) : ℝ)))
      (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) := by
  simpa only [normalized_constraint_field_snoc] using
    integrable_normalized_constraint_field_mul (Fin.snoc σ ε) (Fin.snoc τ δ)

/-- Splitting each row into old and last coordinates preserves independence of the fields
from distinct constraints. -/
theorem iIndepFun_split_constraint_fields {N M : ℕ}
    (σ : Fin M → Fin N → ℤˣ) (ε : Fin M → ℤˣ) :
    iIndepFun (fun k (g : Fin M → Fin (N + 1) → ℝ) =>
      (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, g k i.castSucc * ((σ k i : ℤ) : ℝ)) +
        (Real.sqrt (N + 1 : ℕ))⁻¹ * g k (Fin.last N) * ((ε k : ℤ) : ℝ))
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) := by
  simpa only [normalized_constraint_field_snoc] using
    iIndepFun_normalized_constraint_fields (fun k => Fin.snoc (σ k) (ε k))

end SpinGlasses
