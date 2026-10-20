/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapConcentration
public import LeanMachineLearning.SpinGlasses.SKGuerraBound

/-!
# The Aizenman–Lebowitz–Ruelle formula (Talagrand, Theorem 1.4.10)

For `β < 1/2` the free energy of the SK model is the replica-symmetric one up to `O(1/N)`:
$$\left|p_N(\beta, h) - \Big(\log 2 + \mathbb{E}\log\cosh(\beta z\sqrt{q} + h) +
  \tfrac{\beta^2}{4}(1 - q)^2\Big)\right| \le \frac{K}{N},$$
where `q` solves `q = 𝔼 tanh² (β √q z + h)`.  The proof integrates the smart-path derivative
`φ'(s) = (β²/2) sin s cos s (A(s) - (1 - q)²)` between `0` and `π / 2`, using
`0 ≤ A(s) ≤ K' / N` from the uniform overlap bound (`sk_path_expected_sq_overlap_le`).

## Main declarations

* `SpinGlasses.sk_free_energy_sub_rs_le`: the `O(1/N)` bound.
* `SpinGlasses.tendsto_sk_free_energy_of_lt`: the free energy converges to the replica-symmetric
  value for `β < 1/2`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Theorem 1.4.10.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open Filter Topology
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **The ALR high-temperature free energy formula (Talagrand, Theorem 1.4.10).**  For `β² < 1/4`
and `q = 𝔼 tanh² (β √q z + h)`,
`|p_N(β, h) - (log 2 + 𝔼 log cosh (β √q z + h) + β²/4 (1 - q)²)| ≤ K / N` with
`K = (β² / 4) ((1/2 - 2 β²)^{-1/2} - 1) / (1/4 - β²)`. -/
theorem sk_free_energy_sub_rs_le {N : ℕ} (hN : 0 < N) (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : β ^ 2 < 1 / 4) :
    |(N : ℝ)⁻¹ * ∫ g : FinPairs N → ℝ, Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp ((Real.sqrt N)⁻¹ * β *
          (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
          h * ∑ i, ((σ i : ℤ) : ℝ)))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) -
      (Real.log 2 + ∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h)) ∂(gaussianReal 0 1) +
        β ^ 2 / 4 * (1 - q) ^ 2)| ≤
    β ^ 2 / 4 * (((Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ - 1) / ((1 / 4 - β ^ 2) * N)) := by
  have hq : 0 ≤ q := hfix ▸ integral_nonneg fun x => sq_nonneg _
  obtain ⟨φ, A, h0, hpi, hderiv, hAnn, hAexp⟩ := exists_sk_smart_path_profile hN β h q hq
  have hB : ∀ s ∈ Set.Icc 0 (Real.pi / 2),
      A s ≤ ((Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ - 1) / ((1 / 4 - β ^ 2) * N) := fun s hs => by
    rw [hAexp s]
    exact sk_path_expected_sq_overlap_le hN β h q hfix hβ hs
  have hlow := ge_endpoint_of_trig_square_deriv φ A β q _ hderiv hB
  have hup := le_endpoint_of_trig_square_deriv φ A β q hderiv hAnn
  rw [← h0] at *
  rw [abs_le]
  constructor <;> linarith

/-- **The free energy converges to the replica-symmetric value for `β < 1/2`** (consequence of
`sk_free_energy_sub_rs_le`). -/
theorem tendsto_sk_free_energy_of_lt (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : β ^ 2 < 1 / 4) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∫ g : FinPairs N → ℝ, Real.log (∑ σ : Fin N → ℤˣ,
        Real.exp ((Real.sqrt N)⁻¹ * β *
          (∑ p : FinPairs N, g p * ((σ p.val.1 : ℤ) : ℝ) * ((σ p.val.2 : ℤ) : ℝ)) +
          h * ∑ i, ((σ i : ℤ) : ℝ)))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) atTop
      (𝓝 (Real.log 2 + ∫ x : ℝ, Real.log (Real.cosh (β * Real.sqrt q * x + h))
          ∂(gaussianReal 0 1) + β ^ 2 / 4 * (1 - q) ^ 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hc : (0 : ℝ) < 1 / 4 - β ^ 2 := by linarith
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat
      (β ^ 2 / 4 * (((Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ - 1) / (1 / 4 - β ^ 2))))
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [Real.norm_eq_abs]
  refine (sk_free_energy_sub_rs_le hN β h q hfix hβ).trans_eq ?_
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  field_simp

end SpinGlasses
