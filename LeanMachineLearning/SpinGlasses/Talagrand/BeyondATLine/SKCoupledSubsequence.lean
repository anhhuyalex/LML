/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.BeyondATLine.SKCoupledLimit
public import LeanMachineLearning.ForMathlib.Topology.LipschitzSubsequence

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

/-- The coupled free energy is `1`-Lipschitz in the coupling. -/
theorem lipschitzWith_skCoupledFreeEnergy (M : ℕ) (β h : ℝ) :
    LipschitzWith 1 (skCoupledFreeEnergy M β h) := by
  refine lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_skCoupledFreeEnergy M β h x)
    |>.differentiableAt) fun x => ?_
  rw [(hasDerivAt_skCoupledFreeEnergy M β h x).deriv]
  have := abs_skCoupledOverlapMean_le M β h x
  rw [← NNReal.coe_le_coe]
  simpa [Real.norm_eq_abs] using this

/-- **Subsequential limits of the coupled free energy have a corner at `0`** (Talagrand, the
discussion after Theorem 1.9.6, without the existence of the limit). Beyond the AT line, for
`r > 0` the sequence `ψ_N` has a subsequence that converges on `[-r, r]`, and every such
subsequential limit is not differentiable at `0`. -/
theorem sk_coupled_subsequential_limit_not_differentiableAt (β h q qhat : ℝ) (hh : h ≠ 0)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    (hAT : 1 < β ^ 2 * (1 - 2 * q + qhat)) {r : ℝ} (hr : 0 < r) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ψ : ℝ → ℝ,
      (∀ lam ∈ Icc (-r) r,
        Tendsto (fun N : ℕ => skCoupledFreeEnergy (φ N + 1) β h lam) atTop (𝓝 (ψ lam))) ∧
      ¬ DifferentiableAt ℝ ψ 0 := by
  obtain ⟨φ, hφ, ψ, hψ⟩ := exists_subseq_tendsto_of_lipschitz
    (fun N => skCoupledFreeEnergy (N + 1) β h) (fun N => lipschitzWith_skCoupledFreeEnergy _ β h)
    (fun N => skCoupledFreeEnergy_zero _ β h) r
  refine ⟨φ, hφ, ψ, hψ, ?_⟩
  obtain ⟨δ', hδ', hsep⟩ := sk_coupled_derivative_separation β h q qhat hh hfix hqhat hAT
  refine not_differentiableAt_of_convexOn_tendsto_of_derivative_gap (c := δ' / 2) hr
    (by positivity) (fun N => (convexOn_skCoupledFreeEnergy (φ N + 1) β h).subset (subset_univ _)
      (convex_Ioo _ _))
    (fun N x _ => hasDerivAt_skCoupledFreeEnergy (φ N + 1) β h x)
    (fun lam hlam => hψ lam ⟨hlam.1.le, hlam.2.le⟩) ?_
  intro lam hlam
  obtain ⟨N₀, hN₀⟩ := hsep lam hlam.1
  filter_upwards [eventually_ge_atTop N₀] with N hN
  exact (hN₀ (φ N) (hN.trans (hφ.id_le N))).le

end SpinGlasses
