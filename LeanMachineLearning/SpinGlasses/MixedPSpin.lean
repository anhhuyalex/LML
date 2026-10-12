/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiLinearForm
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianSeries
public import LeanMachineLearning.SpinGlasses.Basic
public import LeanMachineLearning.SpinGlasses.FreeEnergy
public import LeanMachineLearning.SpinGlasses.GibbsMeasure
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Pure and mixed `p`-spin models

The pure `p`-spin Hamiltonian ([Panchenko, 2013, Eq. (1.13)]) is
`H_{N,p}(σ) = N^{-(p-1)/2} ∑_{i₁,…,i_p} g_{i₁…i_p} σ_{i₁} ⋯ σ_{i_p}` with i.i.d. standard Gaussian
disorder `g : (Fin p → ι) → ℝ`, and the mixed `p`-spin Hamiltonian is the series
`H_N(σ) = ∑ₚ β_p H_{N,p}(σ)` ([Panchenko, 2013, Eq. (1.14)]) with independent disorders
`g p : (Fin p → ι) → ℝ`.  Both are *Gaussian linear forms* of the disorder, so the covariance
`𝔼[H_N(σ¹) H_N(σ²)] = N ξ(R(σ¹, σ²))` with `ξ(x) = ∑ₚ β_p² x^p` is the diagonal covariance of the
Gaussian series of `ForMathlib/Probability/Moments/GaussianSeries.lean`, evaluated with
`∑_{i : Fin p → ι} ∏ₖ σ¹(iₖ) σ²(iₖ) = (σ¹ ⬝ᵥ σ²)^p`.

No definition is introduced (`purePSpinHamiltonian`, `xiCovarianceFunction`,
`mixedPSpinHamiltonian`, `mixedPartitionFunction` and `mixedFreeEnergy` of the original sketch are
written out; the Hamiltonian is passed through its defining equation `hH`).  The free-energy
statements of Milestones 3–5 apply to the mixed model as soon as measurability and integrability of
the coordinates `G ↦ H_N(G, σ)` are known: they are proved here
(`SpinGlasses.mixedPSpin_measurable`, `SpinGlasses.mixedPSpin_integrable`).

## Main declarations

* `SpinGlasses.integral_purePSpin_mul_purePSpin`: `𝔼[H_{N,p}(σ¹) H_{N,p}(σ²)] = N R(σ¹, σ²)^p`.
* `SpinGlasses.summable_abs_of_summable_two_pow_mul_sq`,
  `SpinGlasses.summable_sq_mul_pow_of_summable_abs`: Panchenko's condition `∑ 2^p β_p² < ∞`
  implies `∑ |β_p| < ∞`, which gives the convergence of `ξ` on `[-1, 1]`.
* `SpinGlasses.integral_mixedPSpin_mul_mixedPSpin`: `𝔼[H_N(σ¹) H_N(σ²)] = N ξ(R(σ¹, σ²))`.
* `SpinGlasses.mixedPSpin_smooth_approximation_error_bound`,
  `SpinGlasses.mixedPSpin_hasDerivAt_free_energy`: the mixed free energy, via Milestones 3 and 5.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace SpinGlasses

section Pure

variable {ι : Type*} [Fintype ι]

/-- `∑_{i : Fin p → ι} ∏ₖ σ(iₖ) τ(iₖ) = (σ ⬝ᵥ τ)^p`: the multi-index sum factorizes. -/
theorem sum_prod_mul_prod_eq_pow (p : ℕ) (σ τ : ι → ℝ) :
    ∑ idx : Fin p → ι, (∏ k, σ (idx k)) * ∏ k, τ (idx k) = (σ ⬝ᵥ τ) ^ p := by
  simp only [← Finset.prod_mul_distrib, dotProduct, Fintype.sum_pow]

/-- The coefficient vector of the pure `p`-spin Hamiltonian in the disorder:
`H_{N,p}(σ) = u ⬝ᵥ g` with `u i = N^{-(p-1)/2} ∏ₖ σ(iₖ)`.  Its Gram matrix is
`u(σ) ⬝ᵥ u(τ) = N (N⁻¹ σ ⬝ᵥ τ)^p` for `p ≥ 1`. -/
theorem pureCoeff_dotProduct_pureCoeff [Nonempty ι] {p : ℕ} (hp : 1 ≤ p) (σ τ : ι → ℝ) :
    (fun idx : Fin p → ι => (Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) * ∏ k, σ (idx k)) ⬝ᵥ
        (fun idx : Fin p → ι => (Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) * ∏ k, τ (idx k)) =
      Fintype.card ι * ((Fintype.card ι : ℝ)⁻¹ * (σ ⬝ᵥ τ)) ^ p := by
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hc : (Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) * (Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) =
      ((Fintype.card ι : ℝ)⁻¹) ^ (p - 1) := by
    rw [← mul_pow, ← mul_inv, Real.mul_self_sqrt hN.le]
  have h : ∀ idx : Fin p → ι,
      ((Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) * ∏ k, σ (idx k)) *
        ((Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) * ∏ k, τ (idx k)) =
      ((Fintype.card ι : ℝ)⁻¹) ^ (p - 1) * ((∏ k, σ (idx k)) * ∏ k, τ (idx k)) := fun idx => by
    rw [← hc]; ring
  simp only [dotProduct, h, ← Finset.mul_sum, sum_prod_mul_prod_eq_pow]
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le' hp
  simp only [Nat.add_sub_cancel, mul_pow, pow_succ, inv_pow]
  field_simp

/-- **Covariance of the pure `p`-spin Hamiltonian** ([Panchenko, 2013, Eq. (1.13)]): for
`H_{N,p}(σ) = N^{-(p-1)/2} ∑_{i} g_i ∏ₖ σ(iₖ)` with i.i.d. standard Gaussian `g`,
`𝔼[H_{N,p}(σ) H_{N,p}(τ)] = N (N⁻¹ σ ⬝ τ)^p`. -/
theorem integral_purePSpin_mul_purePSpin [Nonempty ι] {p : ℕ} (hp : 1 ≤ p) (σ τ : ι → ℝ) :
    ∫ g : (Fin p → ι) → ℝ,
        ((Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) * ∑ idx, g idx * ∏ k, σ (idx k)) *
          ((Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) * ∑ idx, g idx * ∏ k, τ (idx k))
        ∂(Measure.pi fun _ : Fin p → ι => gaussianReal 0 1) =
      Fintype.card ι * ((Fintype.card ι : ℝ)⁻¹ * (σ ⬝ᵥ τ)) ^ p := by
  rw [← pureCoeff_dotProduct_pureCoeff hp, ← integral_dotProduct_mul_dotProduct_pi_gaussianReal]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  have hlin : ∀ υ : ι → ℝ, (Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) *
      ∑ idx, g idx * ∏ k, υ (idx k) =
      (fun idx : Fin p → ι => (Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) * ∏ k, υ (idx k)) ⬝ᵥ g :=
    fun υ => by
      simp only [dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun idx _ => by ring
  beta_reduce
  rw [hlin σ, hlin τ]

end Pure

section Summability

variable {β : ℕ → ℝ}

/-- Panchenko's decay condition `∑ₚ 2^p β_p² < ∞` implies `∑ₚ |β_p| < ∞`, since
`|β_p| ≤ (2^p β_p² + 2^{-p}) / 2`. -/
theorem summable_abs_of_summable_two_pow_mul_sq (hβ : Summable fun p => (2 : ℝ) ^ p * β p ^ 2) :
    Summable fun p => |β p| := by
  have hgeo : Summable fun p : ℕ => ((2 : ℝ) ^ p)⁻¹ := by
    simpa [inv_pow] using summable_geometric_two
  refine Summable.of_nonneg_of_le (fun p => abs_nonneg _) (fun p => ?_)
    ((hβ.add hgeo).mul_left (1 / 2))
  have hu : (0 : ℝ) < 2 ^ p := by positivity
  have key : 2 * 2 ^ p * |β p| ≤ (2 ^ p) ^ 2 * |β p| ^ 2 + 1 := by
    nlinarith [sq_nonneg (2 ^ p * |β p| - 1)]
  calc |β p| = (2 * 2 ^ p * |β p|) / (2 * 2 ^ p) := by field_simp
    _ ≤ ((2 ^ p) ^ 2 * |β p| ^ 2 + 1) / (2 * 2 ^ p) := by gcongr
    _ = 1 / 2 * (2 ^ p * β p ^ 2 + ((2 : ℝ) ^ p)⁻¹) := by rw [sq_abs]; field_simp

/-- If `∑ₚ |β_p| < ∞` then `∑ₚ β_p² < ∞`. -/
theorem summable_sq_of_summable_abs (hβ : Summable fun p => |β p|) : Summable fun p => β p ^ 2 := by
  refine Summable.of_nonneg_of_le (fun p => sq_nonneg _) (fun p => ?_)
    (hβ.mul_left (∑' q, |β q|))
  rw [← sq_abs, sq]
  exact mul_le_mul_of_nonneg_right (hβ.le_tsum p fun _ _ => abs_nonneg _) (abs_nonneg _)

/-- **The covariance function `ξ(x) = ∑ₚ β_p² x^p` converges on `[-1, 1]`.** -/
theorem summable_sq_mul_pow_of_summable_abs (hβ : Summable fun p => |β p|) {x : ℝ}
    (hx : |x| ≤ 1) : Summable fun p => β p ^ 2 * x ^ p :=
  Summable.of_norm_bounded (summable_sq_of_summable_abs hβ) fun p => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_pow, sq_abs]
    exact mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (abs_nonneg _) hx)

end Summability

section Mixed

variable {ι : Type*} [Fintype ι] [Nonempty ι] {β : ℕ → ℝ}

local notation "gaussianDisorder" =>
  Measure.infinitePi fun p : ℕ => Measure.pi fun _ : Fin p → ι => gaussianReal 0 1

omit [Nonempty ι] in
/-- The term of degree `p` of the mixed Hamiltonian is a linear form of the disorder `g p`, with
coefficient vector `idx ↦ β p * (N^{-(p-1)/2} * ∏ₖ σ(idxₖ))`. -/
private lemma mixed_term_eq (p : ℕ) (σ : ι → ℝ) (g : (Fin p → ι) → ℝ) :
    β p * ((Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) * ∑ idx, g idx * ∏ k, σ (idx k)) =
      (fun idx : Fin p → ι => β p * ((Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) *
        ∏ k, σ (idx k))) ⬝ᵥ g := by
  simp only [dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun idx _ => by ring

/-- The Gram matrix of the coefficient vectors:
`⟨a_p(σ), a_p(τ)⟩ = β_p² N (N⁻¹ σ ⬝ τ)^p`, using `β₀ = 0` for `p = 0`. -/
private lemma mixedCoeff_dotProduct (hβ0 : β 0 = 0) (p : ℕ) (σ τ : ι → ℝ) :
    (fun idx : Fin p → ι => β p * ((Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) *
        ∏ k, σ (idx k))) ⬝ᵥ
      (fun idx : Fin p → ι => β p * ((Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) *
        ∏ k, τ (idx k))) =
      β p ^ 2 * (Fintype.card ι * ((Fintype.card ι : ℝ)⁻¹ * (σ ⬝ᵥ τ)) ^ p) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [hβ0]
  · rw [← pureCoeff_dotProduct_pureCoeff hp σ τ]
    simp only [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun idx _ => by ring

/-- The coefficient vectors are square-summable in `ℓ¹`: `‖a_p(σ)‖ ≤ |β_p| √N` for `|σᵢ| ≤ 1`. -/
private lemma summable_sqrt_mixedCoeff (hβ0 : β 0 = 0) (hβ : Summable fun p => |β p|)
    {σ : ι → ℝ} (hσ : ∀ i, |σ i| ≤ 1) :
    Summable fun p => Real.sqrt
      ((fun idx : Fin p → ι => β p * ((Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) *
        ∏ k, σ (idx k))) ⬝ᵥ
      (fun idx : Fin p → ι => β p * ((Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) *
        ∏ k, σ (idx k)))) := by
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hR0 : 0 ≤ (Fintype.card ι : ℝ)⁻¹ * (σ ⬝ᵥ σ) :=
    mul_nonneg (inv_nonneg.2 hN.le) (Finset.sum_nonneg fun i _ => mul_self_nonneg (σ i))
  have hR1 : (Fintype.card ι : ℝ)⁻¹ * (σ ⬝ᵥ σ) ≤ 1 :=
    (le_abs_self _).trans (abs_card_inv_mul_dotProduct_le_one σ σ hσ hσ)
  refine Summable.of_nonneg_of_le (fun p => Real.sqrt_nonneg _) (fun p => ?_)
    (hβ.mul_right (Real.sqrt (Fintype.card ι)))
  rw [mixedCoeff_dotProduct hβ0]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have hsq : (|β p| * Real.sqrt (Fintype.card ι)) ^ 2 = β p ^ 2 * Fintype.card ι := by
    rw [mul_pow, sq_abs, Real.sq_sqrt hN.le]
  rw [hsq]
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hN.le (pow_le_one₀ hR0 hR1))
    (sq_nonneg _)

variable (H : (∀ p : ℕ, (Fin p → ι) → ℝ) → (ι → ℝ) → ℝ)
  (hH : ∀ g σ, H g σ = ∑' p, β p * ((Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) *
    ∑ idx, g p idx * ∏ k, σ (idx k)))

include hH

omit [Nonempty ι] in
private lemma mixedPSpin_eq_tsum (g : ∀ p : ℕ, (Fin p → ι) → ℝ) (σ : ι → ℝ) :
    H g σ = ∑' p, (fun idx : Fin p → ι => β p * ((Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) *
      ∏ k, σ (idx k))) ⬝ᵥ g p := by
  rw [hH]
  exact tsum_congr fun p => mixed_term_eq p σ (g p)

omit [Nonempty ι] in
/-- **The mixed `p`-spin Hamiltonian is measurable in the disorder.** -/
theorem mixedPSpin_measurable (σ : ι → ℝ) : Measurable fun g => H g σ := by
  simp only [mixedPSpin_eq_tsum H hH]
  exact measurable_tsum_dotProduct _

/-- **The mixed `p`-spin Hamiltonian is integrable in the disorder** when `∑ₚ |β_p| < ∞`,
`β₀ = 0` and `|σᵢ| ≤ 1`. -/
theorem mixedPSpin_integrable (hβ0 : β 0 = 0) (hβ : Summable fun p => |β p|) {σ : ι → ℝ}
    (hσ : ∀ i, |σ i| ≤ 1) : Integrable (fun g => H g σ) gaussianDisorder := by
  simp only [mixedPSpin_eq_tsum H hH]
  exact integrable_tsum_dotProduct (summable_sqrt_mixedCoeff hβ0 hβ hσ)

/-- **Covariance of the mixed `p`-spin Hamiltonian** ([Panchenko, 2013, Eq. (1.14)]): for
`H_N(σ) = ∑ₚ β_p N^{-(p-1)/2} ∑_{i} g_{p,i} ∏ₖ σ(iₖ)` with independent standard Gaussian disorders,
`∑ₚ |β_p| < ∞`, `β₀ = 0` and `|σᵢ|, |τᵢ| ≤ 1`,
`𝔼[H_N(σ) H_N(τ)] = N ξ(N⁻¹ σ ⬝ τ)` with `ξ(x) = ∑ₚ β_p² x^p`. -/
theorem integral_mixedPSpin_mul_mixedPSpin (hβ0 : β 0 = 0) (hβ : Summable fun p => |β p|)
    {σ τ : ι → ℝ} (hσ : ∀ i, |σ i| ≤ 1) (hτ : ∀ i, |τ i| ≤ 1) :
    ∫ g, H g σ * H g τ ∂gaussianDisorder =
      Fintype.card ι * ∑' p, β p ^ 2 * ((Fintype.card ι : ℝ)⁻¹ * (σ ⬝ᵥ τ)) ^ p := by
  simp only [mixedPSpin_eq_tsum H hH]
  rw [integral_tsum_dotProduct_mul_tsum_dotProduct (summable_sqrt_mixedCoeff hβ0 hβ hσ)
    (summable_sqrt_mixedCoeff hβ0 hβ hτ), ← tsum_mul_left]
  exact tsum_congr fun p => by rw [mixedCoeff_dotProduct hβ0]; ring

end Mixed

/-- Configurations of the hypercube have coordinates in `[-1, 1]`. -/
private lemma abs_units_cast_le_one (u : ℤˣ) : |((u : ℤ) : ℝ)| ≤ 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

section FreeEnergy

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {β : ℕ → ℝ}

local notation "gaussianDisorder" =>
  Measure.infinitePi fun p : ℕ => Measure.pi fun _ : Fin p → ι => gaussianReal 0 1


variable (H : (∀ p : ℕ, (Fin p → ι) → ℝ) → (ι → ℤˣ) → ℝ)
  (hH : ∀ g σ, H g σ = ∑' p, β p * ((Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) *
    ∑ idx, g p idx * ∏ k, ((σ (idx k) : ℤ) : ℝ)))
  (hβ0 : β 0 = 0) (hβ : Summable fun p => |β p|) {t : ℝ}

include hH hβ0 hβ

omit [DecidableEq ι] in
private lemma mixedPSpin_hypercube_hyps (σ : ι → ℤˣ) :
    Measurable (fun g => H g σ) ∧ Integrable (fun g => H g σ) gaussianDisorder := by
  let H' : (∀ p : ℕ, (Fin p → ι) → ℝ) → (ι → ℝ) → ℝ := fun g v => ∑' p, β p *
    ((Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) * ∑ idx, g p idx * ∏ k, v (idx k))
  have e : (fun g => H g σ) = fun g => H' g (fun i => ((σ i : ℤ) : ℝ)) :=
    funext fun g => hH g σ
  have hm := mixedPSpin_measurable H' (fun _ _ => rfl) (fun i => ((σ i : ℤ) : ℝ))
  have hi := mixedPSpin_integrable H' (fun _ _ => rfl) hβ0 hβ
    (σ := fun i => ((σ i : ℤ) : ℝ)) fun i => abs_units_cast_le_one (σ i)
  rw [e]
  exact ⟨hm, hi⟩

/-- **Smooth approximation for the mixed `p`-spin model** ([Panchenko, 2013, Eq. (1.7)]): for
`t > 0`, `|(N t)⁻¹ 𝔼 log Z_N(t) - N⁻¹ 𝔼 max_σ H_N(σ)| ≤ log 2 / t`.  This is
`smooth_approximation_error_bound` once measurability and integrability of the coordinates are
known (`mixedPSpin_measurable`, `mixedPSpin_integrable`). -/
theorem mixedPSpin_smooth_approximation_error_bound (ht : 0 < t) :
    |((Fintype.card ι : ℝ) * t)⁻¹ * ∫ g, Real.log (∑ σ, Real.exp (t * H g σ)) ∂gaussianDisorder -
        (Fintype.card ι : ℝ)⁻¹ * ∫ g, (H g).max ∂gaussianDisorder| ≤ Real.log 2 / t :=
  smooth_approximation_error_bound ht (fun σ => (mixedPSpin_hypercube_hyps H hH hβ0 hβ σ).1)
    (fun σ => (mixedPSpin_hypercube_hyps H hH hβ0 hβ σ).2)

/-- **Temperature derivative of the mixed `p`-spin free energy:** for `t > 0`,
`(d/dt) N⁻¹ 𝔼 log Z_N(t) = N⁻¹ 𝔼 ⟨H_N⟩_t`, where `⟨·⟩_t` is the Gibbs average
(`hasDerivAt_integral_log_sum_exp`). -/
theorem mixedPSpin_hasDerivAt_free_energy (ht : 0 < t) :
    HasDerivAt (fun s => (Fintype.card ι : ℝ)⁻¹ *
        ∫ g, Real.log (∑ σ, Real.exp (s * H g σ)) ∂gaussianDisorder)
      ((Fintype.card ι : ℝ)⁻¹ * ∫ g, ∫ σ, H g σ ∂(Measure.count.tilted fun σ => t * H g σ)
        ∂gaussianDisorder) t :=
  (hasDerivAt_integral_log_sum_exp ht (fun σ => (mixedPSpin_hypercube_hyps H hH hβ0 hβ σ).1)
    (fun σ => (mixedPSpin_hypercube_hyps H hH hβ0 hβ σ).2)).const_mul _

end FreeEnergy

end SpinGlasses
