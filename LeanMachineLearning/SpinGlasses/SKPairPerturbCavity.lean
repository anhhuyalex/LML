/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GibbsMeasureNested
public import LeanMachineLearning.SpinGlasses.SKCavityGaussian
public import LeanMachineLearning.SpinGlasses.SKCavityInterpolation

/-!
# The last cavity step of the pair-perturbation estimate (Talagrand Eq. 1.182)

At the coupled endpoint the `(N+1)`-spin system at coefficient `β / √N` has the first `N` spins
distributed as an `N`-spin SK system perturbed by the cavity factor `cosh`; averaging the
cavity couplings bounds its overlap average by `cosh(2h) exp(2β²)` times the `N`-spin one.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Two-replica cavity identity on the last spin of `Fin (N+1) → ℤˣ`.**  For an observable
of the first `N` coordinates of two replicas, summing out the last spins gives the
`N`-spin two-replica average weighted by `cosh (L ρ) cosh (L ρ') / ⟨cosh L⟩²`. -/
theorem integral_prod_count_tilted_fin_snoc_cavity_units (N : ℕ)
    (A L : (Fin N → ℤˣ) → ℝ) (g : (Fin N → ℤˣ) → (Fin N → ℤˣ) → ℝ) :
    ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ),
        g (fun i => p.1 i.castSucc) (fun i => p.2 i.castSucc)
      ∂((Measure.count.tilted fun σ : Fin (N + 1) → ℤˣ =>
          A (fun i => σ i.castSucc) + (σ (Fin.last N) : ℝ) * L (fun i => σ i.castSucc)).prod
        (Measure.count.tilted fun σ : Fin (N + 1) → ℤˣ =>
          A (fun i => σ i.castSucc) + (σ (Fin.last N) : ℝ) * L (fun i => σ i.castSucc))) =
      (∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ),
          g p.1 p.2 * Real.cosh (L p.1) * Real.cosh (L p.2)
        ∂((Measure.count.tilted A).prod (Measure.count.tilted A))) /
        (∫ ρ, Real.cosh (L ρ) ∂Measure.count.tilted A) ^ 2 := by
  let e : ((Fin N → ℤˣ) × ℤˣ) ≃ (Fin (N + 1) → ℤˣ) :=
    (Equiv.prodComm (Fin N → ℤˣ) ℤˣ).trans (Fin.snocEquiv fun _ => ℤˣ)
  rw [integral_prod_count_tilted_equiv e _ (fun σ τ =>
    g (fun i => σ i.castSucc) (fun i => τ i.castSucc))]
  simp only [e, Equiv.trans_apply, Equiv.prodComm_apply, Fin.snocEquiv_apply,
    Fin.snoc_castSucc, Fin.snoc_last]
  exact integral_prod_count_tilted_units A L g

/-- The cavity average of a nonnegative observable is dominated by the `cosh`-weighted
`N`-spin average, since `⟨cosh L⟩ ≥ 1`. -/
theorem integral_prod_count_tilted_fin_snoc_cavity_units_le (N : ℕ)
    (A L : (Fin N → ℤˣ) → ℝ) (g : (Fin N → ℤˣ) → (Fin N → ℤˣ) → ℝ) (hg : ∀ a b, 0 ≤ g a b) :
    ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ),
        g (fun i => p.1 i.castSucc) (fun i => p.2 i.castSucc)
      ∂((Measure.count.tilted fun σ : Fin (N + 1) → ℤˣ =>
          A (fun i => σ i.castSucc) + (σ (Fin.last N) : ℝ) * L (fun i => σ i.castSucc)).prod
        (Measure.count.tilted fun σ : Fin (N + 1) → ℤˣ =>
          A (fun i => σ i.castSucc) + (σ (Fin.last N) : ℝ) * L (fun i => σ i.castSucc))) ≤
      ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ),
          g p.1 p.2 * Real.cosh (L p.1) * Real.cosh (L p.2)
        ∂((Measure.count.tilted A).prod (Measure.count.tilted A)) := by
  rw [integral_prod_count_tilted_fin_snoc_cavity_units]
  have hnum : 0 ≤ ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ),
      g p.1 p.2 * Real.cosh (L p.1) * Real.cosh (L p.2)
      ∂((Measure.count.tilted A).prod (Measure.count.tilted A)) :=
    integral_nonneg fun p => by
      have := Real.cosh_pos (L p.1); have := Real.cosh_pos (L p.2); have := hg p.1 p.2
      positivity
  have hcosh : 1 ≤ ∫ a, Real.cosh (L a) ∂Measure.count.tilted A := by
    have h1 : (1 : ℝ) = ∫ _ : Fin N → ℤˣ, (1 : ℝ) ∂Measure.count.tilted A := by
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    rw [h1]
    exact integral_mono (integrable_const _) Integrable.of_finite fun a => Real.one_le_cosh (L a)
  exact div_le_self hnum (by nlinarith)

/-- Gaussian `cosh` product moment: `𝔼 cosh(x_σ + h) cosh(x_τ + h) ≤ cosh(2h) exp(2β²)` for
the N-spin cavity field `x_σ = β N^{-1/2} ∑ gᵢ σᵢ`. -/
theorem integral_cosh_mul_cosh_sk_cavity_le (N : ℕ) (hN : 0 < N) (β h : ℝ)
    (σ τ : Fin N → ℤˣ) :
    ∫ w : Fin N → ℝ,
        Real.cosh ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, w i * (σ i : ℝ) + h) *
        Real.cosh ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, w i * (τ i : ℝ) + h)
      ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) ≤
      Real.cosh (2 * h) * Real.exp (2 * β ^ 2) := by
  sorry

end SpinGlasses
