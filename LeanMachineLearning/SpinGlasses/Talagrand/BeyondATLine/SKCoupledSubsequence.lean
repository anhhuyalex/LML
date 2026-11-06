/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.BeyondATLine.SKCoupledLimit
public import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Subsequential limits of the coupled free energy (Talagrand, after Theorem 1.9.6)

The existence of `lim ψ_N(λ)` is left to Guerra and Toninelli by the book. What can be proved
without it: the functions `ψ_M` are `1`-Lipschitz with `ψ_M(0) = 0` (because `|R₁,₂| ≤ 1`), so
by the Arzelà-Ascoli theorem every sequence has a subsequence that converges on `[-r, r]`, and
beyond the AT line every such subsequential limit is not differentiable at `0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped BigOperators NNReal

namespace SpinGlasses

/-- The mean overlap of the coupled system lies in `[-1, 1]`: `|ψ_M'(λ)| ≤ 1`. -/
theorem abs_skCoupledOverlapMean_le (M : ℕ) (β h lam : ℝ) :
    |skCoupledOverlapMean M β h lam| ≤ 1 := by
  by_cases hM : M = 0
  · subst hM
    simp [skCoupledOverlapMean]
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  unfold skCoupledOverlapMean
  have hbound : ∀ g : FinPairs M → ℝ, ‖(∑ σ : Fin M → ℤˣ, ∑ τ : Fin M → ℤˣ,
      (∑ i, ((σ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ)) * Real.exp (skGibbsEnergy M β h g σ +
        skGibbsEnergy M β h g τ + lam * ∑ i, ((σ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ))) /
      skCoupledPartition M β h lam g‖ ≤ M := by
    intro g
    have hZ := skCoupledPartition_pos M β h lam g
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hZ, div_le_iff₀ hZ]
    calc |∑ σ : Fin M → ℤˣ, ∑ τ : Fin M → ℤˣ,
          (∑ i, ((σ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ)) * Real.exp (skGibbsEnergy M β h g σ +
            skGibbsEnergy M β h g τ + lam * ∑ i, ((σ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ))|
        ≤ ∑ σ : Fin M → ℤˣ, ∑ τ : Fin M → ℤˣ, |(∑ i, ((σ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ)) *
            Real.exp (skGibbsEnergy M β h g σ + skGibbsEnergy M β h g τ +
              lam * ∑ i, ((σ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ))| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ =>
            Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ σ : Fin M → ℤˣ, ∑ τ : Fin M → ℤˣ, (M : ℝ) * Real.exp (skGibbsEnergy M β h g σ +
            skGibbsEnergy M β h g τ + lam * ∑ i, ((σ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ)) := by
          refine Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun τ _ => ?_
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          calc ∑ i, |((σ i : ℤ) : ℝ) * ((τ i : ℤ) : ℝ)| ≤ ∑ _i : Fin M, (1 : ℝ) :=
                Finset.sum_le_sum fun i _ => by
                  rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one]
            _ = M := by simp
      _ = M * skCoupledPartition M β h lam g := by
          simp only [skCoupledPartition, Finset.mul_sum]
  have hint := norm_integral_le_of_norm_le_const (μ := Measure.pi fun _ : FinPairs M =>
    gaussianReal 0 1) (ae_of_all _ hbound)
  rw [Real.norm_eq_abs, probReal_univ, mul_one] at hint
  rw [abs_mul, abs_of_pos (inv_pos.2 hMpos), inv_mul_le_iff₀ hMpos, mul_one]
  exact hint

end SpinGlasses
