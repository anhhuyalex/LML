/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKSiteSymmetry
public import LeanMachineLearning.SpinGlasses.SKOverlapConcentration
public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.Pi

/-!
# Decay of truncated spin correlations in the SK model (Talagrand, Eq. (1.132))

Proposition 1.4.14 bounds the truncated correlation of a set of sites by the overlap dispersion
`ν((R₁,₂ - q)²)` in any model with symmetry between sites
(`SpinGlasses.integral_sq_prod_sub_prod_le_finset`).
For the Sherrington-Kirkpatrick model with `β² < 1/4`, the dispersion is `O(1/N)`
(`SpinGlasses.sk_expected_sq_overlap_le`), so the spins decorrelate at the rate `1/N`.

## Main declarations

* `SpinGlasses.sk_correlation_decay_le`: Eq. (1.132),
  `𝔼 (⟨∏_{i ∈ S} σᵢ⟩ - ∏_{i ∈ S} ⟨σᵢ⟩)² ≤ K(|S|) / N`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Proposition 1.4.14 and
  Eq. (1.132).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped Matrix

namespace SpinGlasses

/-- **The SK Gibbs weights as a site-symmetric random state.**  For an energy `E g a` of the SK
form, the Gibbs weights `exp (E g σ) / ∑_b exp (E g b)` are nonnegative, sum to one, depend
measurably on the couplings `g`, and their law is invariant under every relabelling of the sites:
exactly the hypotheses of `integral_sq_prod_sub_prod_le_finset` for the observables
`ξᵢ(σ) = σᵢ`. -/
theorem sk_gibbsWeight_siteSymmetric {N : ℕ} (β h : ℝ) (E : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ)
    (hE : ∀ g a, E g a = (Real.sqrt N)⁻¹ * β *
      (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((a i : ℤ) : ℝ)) :
    (∀ g σ, 0 ≤ Real.exp (E g σ) / ∑ b, Real.exp (E g b)) ∧
      (∀ g, ∑ σ, Real.exp (E g σ) / ∑ b, Real.exp (E g b) = 1) ∧
      (∀ σ, Measurable fun g => Real.exp (E g σ) / ∑ b, Real.exp (E g b)) ∧
      ∀ π : Equiv.Perm (Fin N), ∃ φ : (FinPairs N → ℝ) → (FinPairs N → ℝ),
        MeasurePreserving φ (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
          (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ∧
        ∀ g σ, Real.exp (E (φ g) σ) / ∑ b, Real.exp (E (φ g) b) =
          Real.exp (E g (Equiv.arrowCongr π.symm (Equiv.refl ℤˣ) σ)) / ∑ b, Real.exp (E g b) := by
  have hZ : ∀ g, 0 < ∑ b, Real.exp (E g b) := fun g =>
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hEm : ∀ a, Measurable fun g => E g a := fun a => by
    simp only [hE]; fun_prop
  exact ⟨fun g σ => div_nonneg (Real.exp_pos _).le (hZ g).le,
    fun g => by rw [← Finset.sum_div, div_self (hZ g).ne'],
    fun σ => (Real.measurable_exp.comp (hEm σ)).div
      (Finset.measurable_sum _ fun b _ => Real.measurable_exp.comp (hEm b)),
    fun π => exists_measurePreserving_sk_gibbsWeight β h π E hE⟩

/-- **The overlap bound in terms of the Gibbs weights.**  For an energy `E g a` of the SK form, the
expected squared overlap dispersion `𝔼 ∑_{σ,τ} G(σ) G(τ) (R(σ, τ) - q)²` is at most `K / N` for
`K = ((1/2 - 2 β²)^{-1/2} - 1) / (1/4 - β²)` (`sk_expected_sq_overlap_le`). -/
theorem sk_expected_sq_overlap_le_weights {N : ℕ} (hN : 0 < N) (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : β ^ 2 < 1 / 4) (E : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ)
    (hE : ∀ g a, E g a = (Real.sqrt N)⁻¹ * β *
      (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((a i : ℤ) : ℝ)) :
    ∫ g : FinPairs N → ℝ, ∑ x, ∑ y, Real.exp (E g x) / (∑ b, Real.exp (E g b)) *
        (Real.exp (E g y) / ∑ b, Real.exp (E g b)) * ((N : ℝ)⁻¹ * ∑ i, ((x i : ℤ) : ℝ) *
          ((y i : ℤ) : ℝ) - q) ^ 2 ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
      ((Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ - 1) / ((1 / 4 - β ^ 2) * N) := by
  have hov := sk_expected_sq_overlap_le hN β h q hfix hβ
  simp only [← hE] at hov
  refine le_trans (le_of_eq (integral_congr_ae (ae_of_all _ fun g => ?_))) hov
  exact (integral_pi_fin_two_count_tilted (E g) fun x y => ((N : ℝ)⁻¹ *
    ((fun i => ((x i : ℤ) : ℝ)) ⬝ᵥ fun i => ((y i : ℤ) : ℝ)) - q) ^ 2).symm

/-- **Truncated correlations decay at rate `1/N` (Talagrand, Eq. (1.132)).**  For the SK model with
`β² < 1/4` at the fixed point `q = 𝔼 tanh² (β √q z + h)`, every set `S` of sites satisfies
`𝔼 (⟨∏_{i ∈ S} σᵢ⟩ - ∏_{i ∈ S} ⟨σᵢ⟩)² ≤ K(|S|) / N`, with `K(p) = K'(p) K` for the constant
`K'(p) = spinDecorrConst p` of Proposition 1.4.14 and the overlap constant
`K = ((1/2 - 2 β²)^{-1/2} - 1) / (1/4 - β²)` of `sk_expected_sq_overlap_le`. -/
theorem sk_correlation_decay_le {N : ℕ} (hN : 0 < N) (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : β ^ 2 < 1 / 4) (S : Finset (Fin N)) :
    ∫ g : FinPairs N → ℝ,
        (∫ σ : Fin N → ℤˣ, ∏ i ∈ S, ((σ i : ℤ) : ℝ) ∂(Measure.count.tilted fun a =>
            (Real.sqrt N)⁻¹ * β *
              (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
              h * ∑ i, ((a i : ℤ) : ℝ)) -
          ∏ i ∈ S, ∫ σ : Fin N → ℤˣ, ((σ i : ℤ) : ℝ) ∂(Measure.count.tilted fun a =>
            (Real.sqrt N)⁻¹ * β *
              (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
              h * ∑ i, ((a i : ℤ) : ℝ))) ^ 2
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
      spinDecorrConst S.card *
        (((Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ - 1) / ((1 / 4 - β ^ 2) * N)) := by
  have hq := abs_fixedPoint_le_one hfix
  obtain ⟨E, hE⟩ : ∃ E : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ, ∀ g a, E g a =
      (Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((a i : ℤ) : ℝ) := ⟨_, fun _ _ => rfl⟩
  simp only [← hE]
  obtain ⟨hw0, hw1, hwm, hsym⟩ := sk_gibbsWeight_siteSymmetric β h E hE
  have habs : ∀ (i : Fin N) (σ : Fin N → ℤˣ), |((σ i : ℤ) : ℝ)| ≤ 1 :=
    fun _ _ => abs_units_cast_le_one _
  have hint := integral_sq_prod_sub_prod_le_finset
    (P := Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    (ξ := fun (i : Fin N) (σ : Fin N → ℤˣ) => ((σ i : ℤ) : ℝ))
    (w := fun g σ => Real.exp (E g σ) / ∑ b, Real.exp (E g b)) hN habs hw0 hw1 hwm
    (fun π => Equiv.arrowCongr π.symm (Equiv.refl ℤˣ)) (fun π i σ => by simp) hsym hq S
  have hov' := sk_expected_sq_overlap_le_weights hN β h q hfix hβ E hE
  simp only [integral_count_tilted]
  exact hint.trans (mul_le_mul_of_nonneg_left hov' (spinDecorrConst_nonneg _))

end SpinGlasses
