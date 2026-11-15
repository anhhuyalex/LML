/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.SpinDecorrelation.SKSiteSymmetry
public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapConcentration.SKOverlapConcentration
public import LeanMachineLearning.SpinGlasses.Gaussian.GaussianInterpolationReplica
public import LeanMachineLearning.ForMathlib.Probability.Moments.SecondMoment
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
* `SpinGlasses.sk_gibbs_pair_covariance_sq_le`: Eq. (1.412),
  pairwise covariance decay `𝔼 (⟨σᵢ σⱼ⟩ - ⟨σᵢ⟩⟨σⱼ⟩)² ≤ K / N`.
* `SpinGlasses.sk_expected_gibbs_overlap_sub_sq_le`: Eq. (1.413),
  Gibbs overlap deviation bound `𝔼 (⟨R₁,₂⟩ - q)² ≤ K / N`.
* `SpinGlasses.sk_var_gibbs_overlap_le`: Eq. (1.413),
  disorder variance bound `Var (⟨R₁,₂⟩) ≤ K / N`.
* `SpinGlasses.sk_expected_gibbs_var_overlap_le`: Eq. (1.414),
  Gibbs overlap variance bound `𝔼 ⟨(R₁,₂ - ⟨R₁,₂⟩)²⟩ ≤ K / N`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Proposition 1.4.14,
  Eq. (1.132), and Section 1.14, Eqs. (1.412)-(1.414).
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

/-- **Pairwise covariance decay (Talagrand, Eq. (1.412)).** For the SK model with `β² < 1/4`
at the fixed point `q = 𝔼 tanh² (β √q z + h)`, the covariance of two distinct spins `σᵢ, σⱼ`
under the Gibbs measure satisfies `𝔼 (⟨σᵢ σⱼ⟩ - ⟨σᵢ⟩⟨σⱼ⟩)² ≤ K / N`. -/
theorem sk_gibbs_pair_covariance_sq_le {N : ℕ} (hN : 0 < N) (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : β ^ 2 < 1 / 4) {i j : Fin N} (hij : i ≠ j) :
    ∫ g : FinPairs N → ℝ,
        (∫ σ : Fin N → ℤˣ, ((σ i : ℤ) : ℝ) * ((σ j : ℤ) : ℝ) ∂(Measure.count.tilted fun a =>
            (Real.sqrt N)⁻¹ * β *
              (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
              h * ∑ k, ((a k : ℤ) : ℝ)) -
          (∫ σ : Fin N → ℤˣ, ((σ i : ℤ) : ℝ) ∂(Measure.count.tilted fun a =>
            (Real.sqrt N)⁻¹ * β *
              (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
              h * ∑ k, ((a k : ℤ) : ℝ))) *
          (∫ σ : Fin N → ℤˣ, ((σ j : ℤ) : ℝ) ∂(Measure.count.tilted fun a =>
            (Real.sqrt N)⁻¹ * β *
              (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
              h * ∑ k, ((a k : ℤ) : ℝ)))) ^ 2
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
      spinDecorrConst 2 *
        (((Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ - 1) / ((1 / 4 - β ^ 2) * N)) := by
  obtain ⟨E, hE⟩ : ∃ E : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ, ∀ g a, E g a =
      (Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
        h * ∑ k, ((a k : ℤ) : ℝ) := ⟨_, fun _ _ => rfl⟩
  have hcorr := sk_correlation_decay_le hN β h q hfix hβ {i, j}
  rw [card_pair hij] at hcorr
  simp only [← hE] at hcorr ⊢
  have hp1 (σ : Fin N → ℤˣ) : ∏ k ∈ ({i, j} : Finset (Fin N)), ((σ k : ℤ) : ℝ) =
      ((σ i : ℤ) : ℝ) * ((σ j : ℤ) : ℝ) := prod_pair hij
  have hp2 (g : FinPairs N → ℝ) :
      (∏ k ∈ ({i, j} : Finset (Fin N)),
          ∫ σ : Fin N → ℤˣ, ((σ k : ℤ) : ℝ) ∂(Measure.count.tilted (E g))) =
        (∫ σ : Fin N → ℤˣ, ((σ i : ℤ) : ℝ) ∂(Measure.count.tilted (E g))) *
          (∫ σ : Fin N → ℤˣ, ((σ j : ℤ) : ℝ) ∂(Measure.count.tilted (E g))) := prod_pair hij
  simp_rw [hp1, hp2] at hcorr
  exact hcorr

/-- **Expected squared Gibbs overlap deviation (Talagrand, Eq. (1.413)).** For the SK model with
`β² < 1/4` at the fixed point `q = 𝔼 tanh² (β √q z + h)`, the expected squared deviation of the
Gibbs average `⟨R₁,₂⟩` from `q` is bounded by `K / N`. -/
theorem sk_expected_gibbs_overlap_sub_sq_le {N : ℕ} (hN : 0 < N) (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : β ^ 2 < 1 / 4) :
    ∫ g : FinPairs N → ℝ,
        (∫ σ : Fin 2 → (Fin N → ℤˣ),
            (N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))
              ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
                (Real.sqrt N)⁻¹ * β *
                  (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
                  h * ∑ i, ((a i : ℤ) : ℝ)) - q) ^ 2
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
      ((Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ - 1) / ((1 / 4 - β ^ 2) * N) := by
  have : Nonempty (Fin N → ℤˣ) := ⟨fun _ => 1⟩
  obtain ⟨E, hE⟩ : ∃ E : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ, ∀ g a, E g a =
      (Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((a i : ℤ) : ℝ) := ⟨_, fun _ _ => rfl⟩
  simp only [← hE]
  set Φ : (Fin 2 → Fin N → ℤˣ) → ℝ := fun σ =>
    (N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))
  have h_int_sub (g : FinPairs N → ℝ) :
      (∫ σ : Fin 2 → (Fin N → ℤˣ), Φ σ ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g)))
          - q =
        ∫ σ : Fin 2 → (Fin N → ℤˣ), (Φ σ - q)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g)) := by
    have : IsProbabilityMeasure (Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g)) := by
      infer_instance
    rw [integral_sub Integrable.of_finite (integrable_const q), integral_const, probReal_univ,
      smul_eq_mul, one_mul]
  have hE_ae (a : Fin N → ℤˣ) :
      AEMeasurable (fun g => E g a) (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
    have : Measurable fun g => E g a := by
      simp only [hE]
      refine (measurable_const.mul ?_).add_const _
      exact Finset.measurable_sum _ fun p _ =>
        ((measurable_pi_apply p).mul_const _).mul_const _
    exact this.aemeasurable
  have hjensen := integral_sq_integral_pi_count_tilted_le (R := Fin 2)
    (P := Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    (E := fun a g => E g a) hE_ae (fun σ => Φ σ - q)
  have hov := sk_expected_sq_overlap_le hN β h q hfix hβ
  simp only [← hE] at hov
  simp_rw [h_int_sub]
  exact hjensen.trans hov

/-- **Expected Gibbs overlap variance bound (Talagrand, Eq. (1.414)).** For the SK model with
`β² < 1/4` at the fixed point `q = 𝔼 tanh² (β √q z + h)`, the expected variance of the overlap
under the Gibbs measure is bounded by `K / N`. -/
theorem sk_expected_gibbs_var_overlap_le {N : ℕ} (hN : 0 < N) (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : β ^ 2 < 1 / 4) :
    ∫ g : FinPairs N → ℝ,
        ∫ σ : Fin 2 → (Fin N → ℤˣ),
          ((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ)) -
            ∫ τ : Fin 2 → (Fin N → ℤˣ),
              (N : ℝ)⁻¹ * ((fun i => ((τ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((τ 1 i : ℤ) : ℝ))
                ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
                  (Real.sqrt N)⁻¹ * β *
                    (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
                    h * ∑ i, ((a i : ℤ) : ℝ))) ^ 2
            ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
              (Real.sqrt N)⁻¹ * β *
                (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
                h * ∑ i, ((a i : ℤ) : ℝ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
      ((Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ - 1) / ((1 / 4 - β ^ 2) * N) := by
  have : Nonempty (Fin N → ℤˣ) := ⟨fun _ => 1⟩
  obtain ⟨E, hE⟩ : ∃ E : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ, ∀ g a, E g a =
      (Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((a i : ℤ) : ℝ) := ⟨_, fun _ _ => rfl⟩
  simp only [← hE]
  set Φ : (Fin 2 → Fin N → ℤˣ) → ℝ := fun σ =>
    (N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))
  have hE_ae (a : Fin N → ℤˣ) :
      AEMeasurable (fun g => E g a) (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
    have : Measurable fun g => E g a := by
      simp only [hE]
      refine (measurable_const.mul ?_).add_const _
      exact Finset.measurable_sum _ fun p _ =>
        ((measurable_pi_apply p).mul_const _).mul_const _
    exact this.aemeasurable
  have hi : Integrable (fun g => ∫ σ : Fin 2 → (Fin N → ℤˣ), (Φ σ - q) ^ 2
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g)))
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) :=
    integrable_integral_pi_count_tilted_det (R := Fin 2) (g := fun a g => E g a) hE_ae
      (fun σ => (Φ σ - q) ^ 2)
  have h_pt (g : FinPairs N → ℝ) :
      (∫ σ : Fin 2 → (Fin N → ℤˣ),
        (Φ σ - ∫ τ : Fin 2 → (Fin N → ℤˣ), Φ τ ∂(Measure.pi fun _ : Fin 2 =>
          Measure.count.tilted (E g))) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g))) ≤
      ∫ σ : Fin 2 → (Fin N → ℤˣ), (Φ σ - q) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g)) := by
    have : IsProbabilityMeasure (Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g)) := by
      infer_instance
    have h_mem : MemLp Φ 2 (Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g)) :=
      (memLp_two_iff_integrable_sq (measurable_of_finite Φ).aestronglyMeasurable).2
        Integrable.of_finite
    rw [← variance_eq_integral h_mem.aemeasurable]
    exact variance_le_integral_sub_const_sq h_mem q
  have h_nonneg : 0 ≤ᵐ[Measure.pi fun _ : FinPairs N => gaussianReal 0 1] fun g =>
      ∫ σ : Fin 2 → (Fin N → ℤˣ),
        (Φ σ - ∫ τ : Fin 2 → (Fin N → ℤˣ), Φ τ ∂(Measure.pi fun _ : Fin 2 =>
          Measure.count.tilted (E g))) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E g)) := by
    refine ae_of_all _ fun g => ?_
    exact integral_nonneg fun σ => sq_nonneg _
  have h_mono := integral_mono_of_nonneg h_nonneg hi (ae_of_all _ h_pt)
  have hov := sk_expected_sq_overlap_le hN β h q hfix hβ
  simp only [← hE] at hov
  exact h_mono.trans hov

/-- **Variance of the Gibbs overlap under the disorder (Talagrand, Eq. (1.413)).** For the SK model
with `β² < 1/4` at the fixed point `q = 𝔼 tanh² (β √q z + h)`, the variance of the Gibbs average
`⟨R₁,₂⟩` under the Gaussian disorder is bounded by `K / N`. -/
theorem sk_var_gibbs_overlap_le {N : ℕ} (hN : 0 < N) (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : β ^ 2 < 1 / 4) :
    variance
        (fun g : FinPairs N → ℝ =>
          ∫ σ : Fin 2 → (Fin N → ℤˣ),
            (N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))
              ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
                (Real.sqrt N)⁻¹ * β *
                  (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
                  h * ∑ i, ((a i : ℤ) : ℝ)))
        (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
      ((Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ - 1) / ((1 / 4 - β ^ 2) * N) := by
  have : Nonempty (Fin N → ℤˣ) := ⟨fun _ => 1⟩
  obtain ⟨E, hE⟩ : ∃ E : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ, ∀ g a, E g a =
      (Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((a i : ℤ) : ℝ) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin 2 → Fin N → ℤˣ) → ℝ, ∀ σ, Φ σ =
      (N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ)) :=
    ⟨_, fun _ => rfl⟩
  simp only [← hE, ← hΦ]
  have hE_ae (a : Fin N → ℤˣ) :
      AEMeasurable (fun g => E g a) (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
    have : Measurable fun g => E g a := by
      simp only [hE]
      refine (measurable_const.mul ?_).add_const _
      exact Finset.measurable_sum _ fun p _ =>
        ((measurable_pi_apply p).mul_const _).mul_const _
    exact this.aemeasurable
  have hΦ_bound (σ : Fin 2 → Fin N → ℤˣ) : |Φ σ| ≤ 1 := by
    have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
    have habs : |(fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ)| ≤ N := by
      calc |∑ i, ((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ)|
          ≤ ∑ i : Fin N, |((σ 0 i : ℤ) : ℝ) * ((σ 1 i : ℤ) : ℝ)| := abs_sum_le_sum_abs _ _
        _ = ∑ i : Fin N, |((σ 0 i : ℤ) : ℝ)| * |((σ 1 i : ℤ) : ℝ)| := by
            simp_rw [abs_mul]
        _ = ∑ i : Fin N, (1 : ℝ) * 1 := by
            congr 1 with i
            rw [abs_units_cast_eq_one, abs_units_cast_eq_one]
        _ = N := by simp
    rw [hΦ]
    rw [abs_mul, abs_inv, abs_of_pos hNpos]
    exact (inv_mul_le_iff₀ hNpos).2 (by simpa using habs)
  have hY_mem : MemLp (fun g : FinPairs N → ℝ =>
      ∫ σ : Fin 2 → (Fin N → ℤˣ), Φ σ ∂(Measure.pi fun _ : Fin 2 =>
        Measure.count.tilted (E g))) 2 (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) :=
    memLp_integral_pi_count_tilted_of_bound 2 (fun g a => E g a) hE_ae
      (fun _ σ => Φ σ) (fun _ => aemeasurable_const) 1 (ae_of_all _ fun _ σ => hΦ_bound σ)
  have hvar := variance_le_integral_sub_const_sq hY_mem q
  have hov := sk_expected_gibbs_overlap_sub_sq_le hN β h q hfix hβ
  simp only [← hE, ← hΦ] at hov
  exact hvar.trans hov

end SpinGlasses
