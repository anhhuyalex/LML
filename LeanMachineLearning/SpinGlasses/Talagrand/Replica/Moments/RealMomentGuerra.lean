/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapConcentration.FreeEnergyCLT.SKSmartPathProfileComp
public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.Moments.Hyperbolic
public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.Moments.RealPowers
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.SinCosEndpoint

/-!
# A Guerra-type upper bound for the real moments of the SK partition function

Talagrand, *Spin Glasses* Vol. I, end of Section 1.13.  For `0 < t ≤ 1` the derivative of
`ψ(s) = 𝔼 Z_s^t` along the smart path (`exists_sk_smart_path_profile_exp`) is
`(β²/2) t N sin s cos s 𝔼 [Z_s^t ((1 - t) Q_s - (1 - q)² + t q² + t / N)]` with
`Q_s = ⟨(R₁₂ - q)²⟩_s ≥ 0`, hence at least `-κ sin s cos s ψ(s)` with
`κ = (β² t N / 2)((1 - q)² - t q² - t / N)`.  Integrating `(log ψ)'` gives
`𝔼 Z_N^t ≤ 𝔼 Z_{π/2}^t exp (κ / 2)`, and the decoupled endpoint is explicit.  No estimate for
the overlap is needed; this is the real-`t` analogue of Guerra's bound (`t → 0` recovers
`sk_replica_symmetric_upper_bound`, `t = 1` is an equality).

## Main declaration

* `SpinGlasses.sk_real_moment_guerra_bound`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace SpinGlasses

/-- **Guerra-type bound for real moments.**  For `N ≥ 1`, `q ≥ 0` and `0 < t ≤ 1`,
`𝔼 Z_N^t ≤ (2^t 𝔼 cosh^t(β √q z + h))^N exp ((β² t N / 4)((1 - q)² - t q² - t / N))`,
that is `N⁻¹ log 𝔼 Z_N^t ≤ t log 2 + log 𝔼 cosh^t(β √q z + h) + (β² t / 4)((1 - q)² - t q²) -
β² t² / (4 N)`. -/
theorem sk_real_moment_guerra_bound {N : ℕ} (hN : 0 < N) (β h q : ℝ) (hq : 0 ≤ q) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∫ g : FinPairs N → ℝ, (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ t
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
      (2 ^ t * ∫ z : ℝ, Real.cosh (β * Real.sqrt q * z + h) ^ t ∂(gaussianReal 0 1)) ^ N *
        Real.exp (β ^ 2 * t * N / 4 * ((1 - q) ^ 2 - t * q ^ 2 - t / N)) := by
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  obtain ⟨F, G, A, Q, hF, hG, hA, hQ, h0, hπ, hder⟩ :=
    exists_sk_smart_path_profile_exp hN β h q hq (t * N)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℝ, ψ = fun s => ∫ ω, Real.exp (t * N * A s ω)
      ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1)) := ⟨_, rfl⟩
  set κ : ℝ := β ^ 2 * t * N / 2 * ((1 - q) ^ 2 - t * q ^ 2 - t / N) with hκ
  -- `ψ' ≥ -κ sin cos ψ` on `[0, π/2]`
  have hlow : ∀ s, ∃ d, HasDerivAt ψ d s ∧ (s ∈ Set.Icc 0 (Real.pi / 2) →
      -(κ * (Real.sin s * Real.cos s)) * ψ s ≤ d) := fun s => by
    obtain ⟨hd, hint1, hint2⟩ := hder s
    refine ⟨_, hψ ▸ hd, fun hs => ?_⟩
    have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs.1
      (hs.2.trans (by linarith [Real.pi_pos]))
    have hcos : 0 ≤ Real.cos s := Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [hs.1, Real.pi_pos], hs.2⟩
    have hsc : 0 ≤ Real.sin s * Real.cos s := mul_nonneg hsin hcos
    -- the integrand dominates its `Q = 0` part
    have hQ0 (ω) : 0 ≤ Q s ω := by
      rw [hQ]
      exact integral_nonneg fun σ => sq_nonneg _
    have hI : β ^ 2 / 2 * (t * N) * (-(1 - q) ^ 2 + t * q ^ 2 + t / N) * ψ s ≤
        ∫ ω, β ^ 2 / 2 * (t * N * Real.exp (t * N * A s ω) * (Q s ω - (1 - q) ^ 2) -
          (N : ℝ)⁻¹ * ((t * N) ^ 2 * Real.exp (t * N * A s ω)) * (Q s ω - q ^ 2 - (N : ℝ)⁻¹))
          ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin N => gaussianReal 0 1)) := by
      rw [hψ, ← integral_const_mul]
      refine integral_mono (hint2.const_mul _) hint1 fun ω => ?_
      have hd : β ^ 2 / 2 * (t * N * Real.exp (t * N * A s ω) * (Q s ω - (1 - q) ^ 2) -
          (N : ℝ)⁻¹ * ((t * N) ^ 2 * Real.exp (t * N * A s ω)) * (Q s ω - q ^ 2 - (N : ℝ)⁻¹)) -
          β ^ 2 / 2 * (t * N) * (-(1 - q) ^ 2 + t * q ^ 2 + t / N) * Real.exp (t * N * A s ω) =
          β ^ 2 / 2 * (t * N * (1 - t)) * (Q s ω * Real.exp (t * N * A s ω)) := by
        field_simp
        ring
      have : 0 ≤ β ^ 2 / 2 * (t * N * (1 - t)) * (Q s ω * Real.exp (t * N * A s ω)) :=
        mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (by positivity) (by linarith)))
          (mul_nonneg (hQ0 ω) (Real.exp_pos _).le)
      simp only
      linarith
    rw [integral_const_mul] at hI
    have := mul_le_mul_of_nonneg_left hI hsc
    rw [hκ]
    nlinarith [this]
  -- Grönwall along the path, for the reversed function `s ↦ ψ (π/2 - s)`
  have hgron := Real.le_exp_mul_sin_sq_of_exists_hasDerivAt (φ := fun s => ψ (Real.pi / 2 - s))
    (K := κ) (fun s => by
      obtain ⟨d, hd, hlow'⟩ := hlow (Real.pi / 2 - s)
      refine ⟨-d, hd.comp_const_sub _ _, fun hs => ?_⟩
      have := hlow' ⟨by linarith [hs.2], by linarith [hs.1]⟩
      rw [Real.sin_pi_div_two_sub, Real.cos_pi_div_two_sub] at this
      nlinarith [this])
    (s := Real.pi / 2) ⟨by positivity, le_rfl⟩
  simp only [sub_self, sub_zero, Real.sin_pi_div_two, one_pow, mul_one] at hgron
  have hψ0 : ψ 0 = ∫ g : FinPairs N → ℝ,
      (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ t
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
    rw [hψ]
    refine (h0.trans (integral_congr_ae (ae_of_all _ fun g => ?_)))
    have hZ : ∑ σ : Fin N → ℤˣ, Real.exp (F g σ + h * ∑ i, ((σ i : ℤ) : ℝ)) =
        ∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ) :=
      Finset.sum_congr rfl fun σ _ => by rw [skGibbsEnergy_def, hF]
    simp only
    rw [hZ, skPartition_rpow_eq_exp_mul_log N β h t g]
    congr 1
    field_simp
  have hψπ : ψ (Real.pi / 2) = (2 ^ t * ∫ z : ℝ, Real.cosh (β * Real.sqrt q * z + h) ^ t
      ∂(gaussianReal 0 1)) ^ N := by
    rw [hψ]
    refine (hπ.trans ?_).trans (integral_prod_two_mul_cosh_rpow_pi N t (β * Real.sqrt q) h)
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    beta_reduce
    have hpos : 0 < ∏ i, 2 * Real.cosh (β * Real.sqrt q * z i + h) :=
      Finset.prod_pos fun i _ => mul_pos two_pos (Real.cosh_pos _)
    rw [Real.rpow_def_of_pos hpos, Real.log_prod fun i _ => (mul_pos two_pos
      (Real.cosh_pos _)).ne']
    congr 1
    simp only [Real.log_mul two_ne_zero (Real.cosh_pos _).ne', Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [← hψ0, ← hψπ]
  refine hgron.trans_eq ?_
  rw [mul_comm, hκ]
  congr 2
  ring

end SpinGlasses
