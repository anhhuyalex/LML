/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.SKReplicaConstant
public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.SKReplicaMoment
public import LeanMachineLearning.ForMathlib.Probability.LaplacePrinciple
public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.PiNeg

/-!
# The replica computation of `lim N⁻¹ log 𝔼 Z_N^n` (Talagrand, Theorem 1.13.1)

For every integer `n ≥ 1`,
`lim N⁻¹ log 𝔼 Z_N^n = n log 2 + max_q Φ_n(q)`, where
`Φ_n(q) = n β²(1-q)²/4 - n² β² q²/4 + log 𝔼 ch^n(β z √q + h)`.

## Main declarations

* `SpinGlasses.sk_replica_theorem_pos`: the case `β > 0`.
* `SpinGlasses.sk_replica_theorem`: all real `β` and `h`.
-/

@[expose] public section

open Finset Real MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace SpinGlasses

variable {n : ℕ}

/-- The limit of `N⁻¹ log 𝔼 Z_N^n` in terms of the maximizer `g` of `B`. -/
theorem tendsto_replica_moment (β h : ℝ) (g : FinPairs n → ℝ)
    (hmax : ∀ g' : FinPairs n → ℝ,
      skReplicaLogPartition n β h g' - (∑ p, g' p ^ 2) / 2 ≤
        skReplicaLogPartition n β h g - (∑ p, g p ^ 2) / 2) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * Real.log (∫ g' : FinPairs N → ℝ,
        (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g' σ)) ^ n
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))) atTop
      (𝓝 (β ^ 2 * n / 4 + (skReplicaLogPartition n β h g - (∑ p, g p ^ 2) / 2))) := by
  have hlap := ProbabilityTheory.tendsto_log_integral_exp_laplace
    (skReplicaLogPartition n β h) (continuous_skReplicaLogPartition β h)
    (n * Real.log 2 + n * |h| + |β|) (fun g' => abs_skReplicaLogPartition_le β h g') g hmax
  have hshift : Tendsto (fun N : ℕ => β ^ 2 * n * ((N : ℝ) - n) / (4 * N)) atTop
      (𝓝 (β ^ 2 * n / 4)) := by
    have h1 : Tendsto (fun N : ℕ => β ^ 2 * n / 4 - β ^ 2 * n ^ 2 / 4 * (N : ℝ)⁻¹) atTop
        (𝓝 (β ^ 2 * n / 4 - β ^ 2 * n ^ 2 / 4 * 0)) :=
      tendsto_const_nhds.sub
        ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul _)
    rw [mul_zero, sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℝ) ≠ 0 := by positivity
    field_simp
  refine (hshift.add hlap).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hI : 0 < ∫ x : FinPairs n → ℝ, Real.exp (N * skReplicaLogPartition n β h
      (fun p => x p / Real.sqrt N)) ∂(Measure.pi fun _ : FinPairs n => gaussianReal 0 1) :=
    integral_exp_pos (integrable_exp_laplace _ (continuous_skReplicaLogPartition β h).measurable
      (n * Real.log 2 + n * |h| + |β|) (fun g' => abs_skReplicaLogPartition_le β h g') _ hmax hN)
  change _ = (N : ℝ)⁻¹ * Real.log _
  rw [integral_sk_partition_pow_eq_laplace hN, Real.log_mul (Real.exp_pos _).ne' hI.ne',
    Real.log_exp]
  field_simp

/-- **Talagrand's Theorem 1.13.1 for `β > 0`.** There is a maximizer `q ≥ 0` of
`Φ_n(q) = n β²(1-q)²/4 - n² β² q²/4 + log 𝔼 ch^n(β z √q + h)` over `q ≥ 0`, and
`N⁻¹ log 𝔼 Z_N^n` tends to `n log 2 + Φ_n(q)`. -/
theorem sk_replica_theorem_pos (β h : ℝ) (hβ : 0 < β) :
    ∃ q : ℝ, 0 ≤ q ∧
      (∀ q' : ℝ, 0 ≤ q' →
        n * β ^ 2 * (1 - q') ^ 2 / 4 - n ^ 2 * β ^ 2 * q' ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q' + h) ^ n ∂(gaussianReal 0 1)) ≤
          n * β ^ 2 * (1 - q) ^ 2 / 4 - n ^ 2 * β ^ 2 * q ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))) ∧
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * Real.log (∫ g' : FinPairs N → ℝ,
          (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g' σ)) ^ n
            ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))) atTop
        (𝓝 (n * Real.log 2 + (n * β ^ 2 * (1 - q) ^ 2 / 4 - n ^ 2 * β ^ 2 * q ^ 2 / 4 +
          Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))))) := by
  obtain ⟨g, hg⟩ := exists_forall_objective_le (n := n) β h
  have hmat : ∀ H : Fin n → Fin n → ℝ, (∀ l l', H l l' = H l' l) → (∀ l, H l l = 0) →
      skReplicaMatObjective n β h H ≤ skReplicaMatObjective n β h (skSymmCoupling g) := by
    intro H hHs hHd
    have := hg (fun p : FinPairs n => H p.val.1 p.val.2)
    rw [skReplicaLogPartition_sub_eq_objective, skReplicaLogPartition_sub_eq_objective,
      skSymmCoupling_of_matrix H hHs hHd] at this
    exact this
  obtain ⟨V, hV, hVeq⟩ := skReplica_maximizer_const β h hβ (skSymmCoupling g)
    (skSymmCoupling_comm g) (skSymmCoupling_diag g) hmat
  refine ⟨V / β, div_nonneg hV hβ.le, fun q' hq' => ?_, ?_⟩
  · have h1 := skReplicaMatObjective_const (n := n) β h q' hβ hq'
    have h2 := skReplicaMatObjective_const (n := n) β h (V / β) hβ (div_nonneg hV hβ.le)
    have hVβ : β * (V / β) = V := by field_simp
    rw [hVβ] at h2
    have h3 := hmat (fun l l' => if l = l' then 0 else β * q') (fun l l' => by
      by_cases h : l = l' <;> simp [h, eq_comm]) (fun l => by simp)
    rw [← hVeq] at h2
    linarith
  · have hlim := tendsto_replica_moment (n := n) β h g hg
    have h2 := skReplicaMatObjective_const (n := n) β h (V / β) hβ (div_nonneg hV hβ.le)
    have hVβ : β * (V / β) = V := by field_simp
    rw [hVβ, ← hVeq, ← skReplicaLogPartition_sub_eq_objective] at h2
    rw [h2] at hlim
    convert hlim using 2
    ring

/-- The moments of the partition function are even in `β`. -/
theorem integral_partition_pow_neg_beta (N n : ℕ) (β h : ℝ) :
    ∫ g : FinPairs N → ℝ, (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N (-β) h g σ)) ^ n
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) =
      ∫ g : FinPairs N → ℝ, (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ n
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  simp_rw [skGibbsEnergy_neg_beta]
  exact integral_neg_pi_gaussianReal (fun g : FinPairs N → ℝ =>
    (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ n)

/-- The function `Φ_n` is even in `β`. -/
theorem replica_phi_neg_beta (β h q : ℝ) :
    n * (-β) ^ 2 * (1 - q) ^ 2 / 4 - n ^ 2 * (-β) ^ 2 * q ^ 2 / 4 +
        Real.log (∫ z : ℝ, cosh (-β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) =
      n * β ^ 2 * (1 - q) ^ 2 / 4 - n ^ 2 * β ^ 2 * q ^ 2 / 4 +
        Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) := by
  have h1 : ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1) =
      ∫ z : ℝ, cosh (-β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1) := by
    rw [← integral_neg_gaussianReal (fun z : ℝ => cosh (-β * z * Real.sqrt q + h) ^ n)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    beta_reduce
    rw [show -β * -z * Real.sqrt q = β * z * Real.sqrt q by ring]
  rw [h1, neg_sq]

/-- **Talagrand's Theorem 1.13.1, case `β = 0`:** the disorder plays no role. -/
theorem sk_replica_theorem_zero (h : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * Real.log (∫ g' : FinPairs N → ℝ,
        (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N 0 h g' σ)) ^ n
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))) atTop
      (𝓝 (n * Real.log 2 + (n * 0 ^ 2 * (1 - 0) ^ 2 / 4 - n ^ 2 * 0 ^ 2 * 0 ^ 2 / 4 +
        Real.log (∫ z : ℝ, cosh (0 * z * Real.sqrt 0 + h) ^ n ∂(gaussianReal 0 1))))) := by
  have hc : 0 < cosh h := Real.cosh_pos h
  have hconst : ∀ N : ℕ, ∫ g' : FinPairs N → ℝ,
      (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N 0 h g' σ)) ^ n
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) = ((2 * cosh h) ^ N) ^ n := by
    intro N
    have : ∀ g' : FinPairs N → ℝ, ∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N 0 h g' σ) =
        (2 * cosh h) ^ N := by
      intro g'
      simp only [skGibbsEnergy, mul_zero, zero_mul, zero_add]
      exact sum_exp_h_mul_spin h
    simp_rw [this]
    simp
  simp only [hconst]
  simp only [mul_zero, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_div, sub_zero, zero_add, integral_const, probReal_univ, smul_eq_mul, one_mul]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : (N : ℝ) ≠ 0 := by positivity
  rw [← pow_mul, Real.log_pow, Real.log_pow, Real.log_mul two_ne_zero hc.ne']
  push_cast
  field_simp

/-- **Talagrand's Theorem 1.13.1 (Eq. (1.396)).** For every `n` (the book takes `n ≥ 1`), all real
`β` and `h`, there is a maximizer `q ≥ 0` of
`Φ_n(q) = n β²(1-q)²/4 - n² β² q²/4 + log 𝔼 ch^n(β z √q + h)` over `q ≥ 0`, and
`N⁻¹ log 𝔼 Z_N^n` tends to `n log 2 + Φ_n(q)`, where
`Z_N = ∑_σ exp (β/√N ∑_{i<j} g_ij σ_i σ_j + h ∑ σ_i)`. -/
theorem sk_replica_theorem (β h : ℝ) :
    ∃ q : ℝ, 0 ≤ q ∧
      (∀ q' : ℝ, 0 ≤ q' →
        n * β ^ 2 * (1 - q') ^ 2 / 4 - n ^ 2 * β ^ 2 * q' ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q' + h) ^ n ∂(gaussianReal 0 1)) ≤
          n * β ^ 2 * (1 - q) ^ 2 / 4 - n ^ 2 * β ^ 2 * q ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))) ∧
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * Real.log (∫ g' : FinPairs N → ℝ,
          (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g' σ)) ^ n
            ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))) atTop
        (𝓝 (n * Real.log 2 + (n * β ^ 2 * (1 - q) ^ 2 / 4 - n ^ 2 * β ^ 2 * q ^ 2 / 4 +
          Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))))) := by
  rcases lt_trichotomy β 0 with hneg | hzero | hpos
  · obtain ⟨q, hq0, hqmax, hlim⟩ := sk_replica_theorem_pos (n := n) (-β) h (neg_pos.2 hneg)
    refine ⟨q, hq0, fun q' hq' => ?_, ?_⟩
    · have := hqmax q' hq'
      rwa [replica_phi_neg_beta, replica_phi_neg_beta] at this
    · rw [replica_phi_neg_beta] at hlim
      simpa only [integral_partition_pow_neg_beta] using hlim
  · subst hzero
    refine ⟨0, le_rfl, fun q' hq' => le_of_eq (by simp), ?_⟩
    exact sk_replica_theorem_zero h
  · exact sk_replica_theorem_pos β h hpos

end SpinGlasses
