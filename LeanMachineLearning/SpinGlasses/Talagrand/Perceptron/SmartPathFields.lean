/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.GaussianFields

/-!
# Constant variance along the perceptron smart path

For a fixed old spin and last spin, the three independent Gaussian contributions in
Talagrand (2.15) have coefficient square sum one. Thus the field has the standard normal
prior law at every parameter in `[0, 1]`, including both endpoints and one full spin.
This law concerns deterministic spins before Gibbs tilting, not Gibbs-sampled spins.
The sum index groups the old Gaussian coordinates and the two new independent Gaussians.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SpinGlasses
/-- The old, last-disorder and auxiliary coefficients have total square sum one. -/
theorem sum_sq_perceptron_smart_path_coefficients {N : ℕ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (σ : Fin N → ℤˣ) (ε : ℤˣ) :
    (∑ i, ((Real.sqrt (N + 1 : ℕ))⁻¹ * ((σ i : ℤ) : ℝ)) ^ 2) +
      (Real.sqrt (t / (N + 1)) * ((ε : ℤ) : ℝ)) ^ 2 +
      Real.sqrt ((1 - t) / (N + 1)) ^ 2 = 1 := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  simp only [mul_pow, units_cast_sq, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [Real.sq_sqrt (div_nonneg ht.1 hN.le),
    Real.sq_sqrt (div_nonneg (sub_nonneg.mpr ht.2) hN.le), inv_pow,
    Real.sq_sqrt (by positivity)]
  push_cast
  field_simp
  ring

/-- A fixed-spin smart-path field has standard normal prior law throughout `[0, 1]`.
No lower bound on the number of old spins is required. -/
theorem map_perceptron_smart_path_field_eq_gaussianReal {N : ℕ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (σ : Fin N → ℤˣ) (ε : ℤˣ) :
    (Measure.pi fun _ : Fin N ⊕ Fin 2 => gaussianReal 0 1).map
      (fun x => (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, x (Sum.inl i) * ((σ i : ℤ) : ℝ)) +
        Real.sqrt (t / (N + 1)) * x (Sum.inr 0) * ((ε : ℤ) : ℝ) +
        Real.sqrt ((1 - t) / (N + 1)) * x (Sum.inr 1)) = gaussianReal 0 1 := by
  let c : Fin N ⊕ Fin 2 → ℝ := Sum.elim
    (fun i => (Real.sqrt (N + 1 : ℕ))⁻¹ * ((σ i : ℤ) : ℝ))
    ![Real.sqrt (t / (N + 1)) * ((ε : ℤ) : ℝ), Real.sqrt ((1 - t) / (N + 1))]
  have hc : c ⬝ᵥ c = 1 := by
    simpa only [c, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, pow_two, add_assoc] using
      sum_sq_perceptron_smart_path_coefficients ht σ ε
  have hf (x : Fin N ⊕ Fin 2 → ℝ) :
      (Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, x (Sum.inl i) * ((σ i : ℤ) : ℝ)) +
        Real.sqrt (t / (N + 1)) * x (Sum.inr 0) * ((ε : ℤ) : ℝ) +
        Real.sqrt ((1 - t) / (N + 1)) * x (Sum.inr 1) = c ⬝ᵥ x := by
    simp [c, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm, add_assoc]
  simp_rw [hf]
  exact map_dotProduct_pi_gaussianReal_of_dotProduct_self hc

end SpinGlasses
