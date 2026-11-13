/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.Variational.Stationarity
public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.SKReplicaTheorem
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein
public import LeanMachineLearning.SpinGlasses.Talagrand.GuerraReplicaSymmetric.SKFixedPointRS
public import LeanMachineLearning.SpinGlasses.Talagrand.GuerraReplicaSymmetric.SKFixedPointResidual
public import LeanMachineLearning.SpinGlasses.Talagrand.DecoupledSystems.SKFirstMoment

/-!
# Fixed point of the replica-symmetric variational problem

Talagrand, *Spin Glasses* Vol. I, Section 1.13, Eq. (1.408).
-/

@[expose] public section

open Finset Real MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators

namespace SpinGlasses

/-- At `β = 0`, `Φ_n(q)` is constant and equals `n * log (cosh h)`. -/
theorem replica_phi_zero (n : ℕ) (h q : ℝ) :
    n * (0 : ℝ) ^ 2 * (1 - q) ^ 2 / 4 - (n : ℝ) ^ 2 * 0 ^ 2 * q ^ 2 / 4 +
        Real.log (∫ z : ℝ, cosh (0 * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) =
      n * Real.log (cosh h) := by
  simp [Real.log_pow]

/-- At `β = 0`, the replica ratio is identically `th² h`. -/
theorem skReplica_ratio_zero (n : ℕ) (h q : ℝ) :
    (∫ z : ℝ, cosh (0 * z * Real.sqrt q + h) ^ n *
          tanh (0 * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
        (∫ z : ℝ, cosh (0 * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) =
      tanh h ^ 2 := by
  have heq1 : (fun z : ℝ => cosh (0 * z * Real.sqrt q + h) ^ n *
        tanh (0 * z * Real.sqrt q + h) ^ 2) =
      (fun _ => cosh h ^ n * tanh h ^ 2) := by
    ext z; congr 3 <;> ring
  have heq2 : (fun z : ℝ => cosh (0 * z * Real.sqrt q + h) ^ n) =
      (fun _ => cosh h ^ n) := by
    ext z; congr 2; ring
  simp_rw [heq1, heq2]
  rw [integral_const, integral_const, probReal_univ, smul_eq_mul, one_mul,
    smul_eq_mul, one_mul]
  have hpos : cosh h ^ n ≠ 0 := (pow_pos (Real.cosh_pos h) n).ne'
  exact mul_div_cancel_left₀ _ hpos

/-- **Talagrand's Eq. (1.408) for `β = 0`:** `q = th² h` is a maximizing fixed point. -/
theorem exists_skReplica_maximizer_fixedPoint_zero (n : ℕ) (h : ℝ) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧
      (∀ q' : ℝ, 0 ≤ q' →
        n * (0 : ℝ) ^ 2 * (1 - q') ^ 2 / 4 - (n : ℝ) ^ 2 * 0 ^ 2 * q' ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (0 * z * Real.sqrt q' + h) ^ n ∂(gaussianReal 0 1)) ≤
          n * (0 : ℝ) ^ 2 * (1 - q) ^ 2 / 4 - (n : ℝ) ^ 2 * 0 ^ 2 * q ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (0 * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))) ∧
      q = (∫ z : ℝ, cosh (0 * z * Real.sqrt q + h) ^ n *
            tanh (0 * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (0 * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) ∧
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * Real.log (∫ g' : FinPairs N → ℝ,
          (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N 0 h g' σ)) ^ n
            ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))) atTop
        (𝓝 (n * Real.log 2 + (n * (0 : ℝ) ^ 2 * (1 - q) ^ 2 / 4 -
          (n : ℝ) ^ 2 * 0 ^ 2 * q ^ 2 / 4 +
          Real.log (∫ z : ℝ, cosh (0 * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))))) := by
  refine ⟨tanh h ^ 2, sq_nonneg _, (Real.tanh_sq_lt_one _).le, fun q' _ => ?_, ?_, ?_⟩
  · rw [replica_phi_zero, replica_phi_zero]
  · rw [skReplica_ratio_zero]
  · have hlim := sk_replica_theorem_zero (n := n) h
    rw [replica_phi_zero (q := 0)] at hlim
    rw [replica_phi_zero (q := tanh h ^ 2)]
    exact hlim

/-- For `n = 1`, `Φ_1(q)` is constant on `q ≥ 0` and equals `β² / 4 + log (cosh h)`. -/
theorem replica_phi_one_const (β h q : ℝ) (hq : 0 ≤ q) :
    1 * β ^ 2 * (1 - q) ^ 2 / 4 - (1 : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
        Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ 1 ∂(gaussianReal 0 1)) =
      β ^ 2 / 4 + Real.log (cosh h) := by
  have heq : (fun z : ℝ => cosh (β * z * Real.sqrt q + h) ^ 1) =
      (fun z => cosh ((β * Real.sqrt q) * z + h)) := by
    ext z; rw [pow_one]; congr 1; ring
  rw [heq, integral_cosh_mul_add_gaussianReal]
  have hpos1 : 0 < Real.exp ((β * Real.sqrt q) ^ 2 / 2) := Real.exp_pos _
  have hpos2 : 0 < cosh h := Real.cosh_pos h
  rw [Real.log_mul hpos1.ne' hpos2.ne', Real.log_exp, mul_pow, Real.sq_sqrt hq]
  ring

/-- Existence of a fixed point in `[0, 1]` for the replica ratio map. -/
theorem exists_skReplica_ratio_fixedPoint (n : ℕ) (β h : ℝ) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧
      q = (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
            tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) := by
  set R : ℝ → ℝ := fun q =>
    (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
          tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
        (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))
  have hcont : ContinuousOn (fun x => R x - x) (Set.Icc (0 : ℝ) 1) :=
    ((continuousOn_skReplica_ratio n β h).sub continuous_id.continuousOn)
  have h0 : 0 ≤ R 0 - 0 := by
    rw [sub_zero]; exact skReplica_ratio_nonneg n β h 0
  have h1 : R 1 - 1 ≤ 0 := by
    linarith [skReplica_ratio_le_one n β h 1]
  obtain ⟨q, hq, hq0⟩ := intermediate_value_Icc' (zero_le_one' ℝ) hcont ⟨h1, h0⟩
  refine ⟨q, hq.1, hq.2, ?_⟩
  dsimp [R] at hq0
  linarith

/-- **Talagrand's Eq. (1.408) for `n = 1`:** any fixed point in `[0, 1]` is a maximizer. -/
theorem exists_skReplica_maximizer_fixedPoint_one (β h : ℝ) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧
      (∀ q' : ℝ, 0 ≤ q' →
        1 * β ^ 2 * (1 - q') ^ 2 / 4 - (1 : ℝ) ^ 2 * β ^ 2 * q' ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q' + h) ^ 1 ∂(gaussianReal 0 1)) ≤
          1 * β ^ 2 * (1 - q) ^ 2 / 4 - (1 : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ 1 ∂(gaussianReal 0 1))) ∧
      q = (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ 1 *
            tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ 1 ∂(gaussianReal 0 1)) ∧
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * Real.log (∫ g' : FinPairs N → ℝ,
          (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g' σ)) ^ 1
            ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))) atTop
        (𝓝 (1 * Real.log 2 + (1 * β ^ 2 * (1 - q) ^ 2 / 4 -
          (1 : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
          Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ 1 ∂(gaussianReal 0 1))))) := by
  obtain ⟨q, hq0, hq1, hqfix⟩ := exists_skReplica_ratio_fixedPoint 1 β h
  refine ⟨q, hq0, hq1, fun q' hq' => ?_, hqfix, ?_⟩
  · rw [replica_phi_one_const β h q' hq', replica_phi_one_const β h q hq0]
  · obtain ⟨q0, hq0_ge, -, hlim⟩ := sk_replica_theorem (n := 1) β h
    push_cast at hlim ⊢
    rw [replica_phi_one_const β h q0 hq0_ge] at hlim
    rw [replica_phi_one_const β h q hq0]
    exact hlim

theorem skReplica_ratio_neg_beta (n : ℕ) (β h q : ℝ) :
    (∫ z : ℝ, cosh (-β * z * Real.sqrt q + h) ^ n *
          tanh (-β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
        (∫ z : ℝ, cosh (-β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) =
      (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
          tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
        (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) := by
  have hnum : ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
        tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) =
      ∫ z : ℝ, cosh (-β * z * Real.sqrt q + h) ^ n *
        tanh (-β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) := by
    rw [← integral_neg_gaussianReal (fun z : ℝ => cosh (-β * z * Real.sqrt q + h) ^ n *
      tanh (-β * z * Real.sqrt q + h) ^ 2)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    beta_reduce
    rw [show -β * -z * Real.sqrt q = β * z * Real.sqrt q by ring]
  have hden : ∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1) =
      ∫ z : ℝ, cosh (-β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1) := by
    rw [← integral_neg_gaussianReal (fun z : ℝ => cosh (-β * z * Real.sqrt q + h) ^ n)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    beta_reduce
    rw [show -β * -z * Real.sqrt q = β * z * Real.sqrt q by ring]
  rw [hnum, hden]

theorem skReplica_ratio_q_zero (n : ℕ) (β h : ℝ) :
    (∫ z : ℝ, cosh (β * z * Real.sqrt 0 + h) ^ n *
          tanh (β * z * Real.sqrt 0 + h) ^ 2 ∂(gaussianReal 0 1)) /
        (∫ z : ℝ, cosh (β * z * Real.sqrt 0 + h) ^ n ∂(gaussianReal 0 1)) =
      tanh h ^ 2 := by
  have heq1 : (fun z : ℝ => cosh (β * z * Real.sqrt 0 + h) ^ n *
        tanh (β * z * Real.sqrt 0 + h) ^ 2) =
      (fun _ => cosh h ^ n * tanh h ^ 2) := by
    ext z
    rw [Real.sqrt_zero, mul_zero, zero_add]
  have heq2 : (fun z : ℝ => cosh (β * z * Real.sqrt 0 + h) ^ n) =
      (fun _ => cosh h ^ n) := by
    ext z
    rw [Real.sqrt_zero, mul_zero, zero_add]
  simp_rw [heq1, heq2]
  rw [integral_const, integral_const, probReal_univ, smul_eq_mul, one_mul,
    smul_eq_mul, one_mul]
  have hpos : cosh h ^ n ≠ 0 := (pow_pos (Real.cosh_pos h) n).ne'
  exact mul_div_cancel_left₀ _ hpos

lemma exists_skReplica_maximizer_fixedPoint_pos (n : ℕ) (hn : 2 ≤ n) (β h : ℝ) (hβ : 0 < β) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧
      (∀ q' : ℝ, 0 ≤ q' →
        n * β ^ 2 * (1 - q') ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q' ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q' + h) ^ n ∂(gaussianReal 0 1)) ≤
          n * β ^ 2 * (1 - q) ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))) ∧
      q = (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
            tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) ∧
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * Real.log (∫ g' : FinPairs N → ℝ,
          (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g' σ)) ^ n
            ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))) atTop
        (𝓝 (n * Real.log 2 + (n * β ^ 2 * (1 - q) ^ 2 / 4 -
          (n : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
          Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))))) := by
  obtain ⟨q0, hq0_nonneg, hq0_max, hlim⟩ := sk_replica_theorem_pos (n := n) β h hβ
  have hF_max : ∀ q : ℝ, 0 ≤ q → skReplicaF n β h q ≤ skReplicaF n β h q0 := by
    intro q hq
    rw [skReplicaF_eq_phi n β h q hq, skReplicaF_eq_phi n β h q0 hq0_nonneg]
    exact hq0_max q hq
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hn_sub_pos : 0 < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hC_pos : 0 < (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 := by positivity
  by_cases hq0_pos : 0 < q0
  · have hloc : IsLocalMax (skReplicaF n β h) q0 :=
      (show IsMaxOn (skReplicaF n β h) (Ici 0) q0 from hF_max).isLocalMax (Ici_mem_nhds hq0_pos)
    have hder := hloc.hasDerivAt_eq_zero (hasDerivAt_skReplicaF n β h q0 hq0_nonneg)
    have h_fix : q0 = (∫ z : ℝ, cosh (β * z * Real.sqrt q0 + h) ^ n *
          tanh (β * z * Real.sqrt q0 + h) ^ 2 ∂(gaussianReal 0 1)) /
        (∫ z : ℝ, cosh (β * z * Real.sqrt q0 + h) ^ n ∂(gaussianReal 0 1)) := by
      linarith [(mul_eq_zero.mp hder).resolve_left hC_pos.ne']
    refine ⟨q0, hq0_nonneg, ?_, hq0_max, h_fix, hlim⟩
    rw [h_fix]
    exact skReplica_ratio_le_one n β h q0
  · have hq0_eq : q0 = 0 := by linarith
    by_cases hh : h = 0
    · subst hh
      have hR0 : (∫ z : ℝ, cosh (β * z * Real.sqrt 0 + 0) ^ n *
            tanh (β * z * Real.sqrt 0 + 0) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt 0 + 0) ^ n ∂(gaussianReal 0 1)) = 0 := by
        rw [skReplica_ratio_q_zero, Real.tanh_zero, sq, mul_zero]
      have h_fix : q0 = (∫ z : ℝ, cosh (β * z * Real.sqrt q0 + 0) ^ n *
            tanh (β * z * Real.sqrt q0 + 0) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt q0 + 0) ^ n ∂(gaussianReal 0 1)) := by
        rw [hq0_eq, hR0]
      refine ⟨q0, hq0_nonneg, ?_, hq0_max, h_fix, hlim⟩
      rw [hq0_eq]
      norm_num
    · have hR0_pos : 0 < (∫ z : ℝ, cosh (β * z * Real.sqrt 0 + h) ^ n *
            tanh (β * z * Real.sqrt 0 + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt 0 + h) ^ n ∂(gaussianReal 0 1)) := by
        rw [skReplica_ratio_q_zero]
        have ht : Real.tanh h ≠ 0 := by
          intro hth
          rw [Real.tanh_eq_sinh_div_cosh, div_eq_zero_iff] at hth
          cases hth with
          | inl h1 =>
            rw [Real.sinh_eq_zero] at h1
            exact hh h1
          | inr h2 =>
            exact (Real.cosh_pos h).ne' h2
        exact sq_pos_of_ne_zero ht
      have hd0 := hasDerivAt_skReplicaF n β h 0 le_rfl
      have hd0_val : 0 < (n : ℝ) * ((n : ℝ) - 1) * β ^ 2 / 2 *
          (((∫ z : ℝ, cosh (β * z * Real.sqrt 0 + h) ^ n *
              tanh (β * z * Real.sqrt 0 + h) ^ 2 ∂(gaussianReal 0 1)) /
            (∫ z : ℝ, cosh (β * z * Real.sqrt 0 + h) ^ n ∂(gaussianReal 0 1))) - 0) := by
        rw [sub_zero]
        exact mul_pos hC_pos hR0_pos
      rcases exists_gt_of_hasDerivAt_zero_pos hd0 hd0_val with ⟨x, hx_pos, hx_lt⟩
      have hx_le := hF_max x hx_pos.le
      rw [hq0_eq] at hx_le
      have hfalse : False := by linarith
      exact hfalse.elim
/-- **Talagrand's Eq. (1.408).** For every integer `n ≥ 1` and all `β, h ∈ ℝ`, there exists a
maximizer `q ∈ [0, 1]` of `Φ_n` over `[0, ∞)` that satisfies the tilted fixed-point equation
`q = 𝔼 [ch^n(β z √q + h) th²(β z √q + h)] / 𝔼 [ch^n(β z √q + h)]`, and `N⁻¹ log 𝔼 Z_N^n` tends to
`n log 2 + Φ_n(q)`. -/
theorem exists_skReplica_maximizer_fixedPoint (n : ℕ) [NeZero n] (β h : ℝ) :
    ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧
      (∀ q' : ℝ, 0 ≤ q' →
        n * β ^ 2 * (1 - q') ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q' ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q' + h) ^ n ∂(gaussianReal 0 1)) ≤
          n * β ^ 2 * (1 - q) ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))) ∧
      q = (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
            tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) ∧
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * Real.log (∫ g' : FinPairs N → ℝ,
          (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g' σ)) ^ n
            ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))) atTop
        (𝓝 (n * Real.log 2 + (n * β ^ 2 * (1 - q) ^ 2 / 4 -
          (n : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
          Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))))) := by
  rcases eq_or_ne n 1 with rfl | hn_ne
  · obtain ⟨q, hq0, hq1, hqmax, hqfix, hlim⟩ := exists_skReplica_maximizer_fixedPoint_one β h
    push_cast
    exact ⟨q, hq0, hq1, hqmax, hqfix, hlim⟩
  · have hn2 : 2 ≤ n := by
      have : 0 < n := NeZero.pos n
      omega
    rcases lt_trichotomy β 0 with hneg | hzero | hpos
    · obtain ⟨q, hq0, hq1, hqmax, hqfix, hlim⟩ :=
        exists_skReplica_maximizer_fixedPoint_pos n hn2 (-β) h (neg_pos.2 hneg)
      refine ⟨q, hq0, hq1, fun q' hq' => ?_, ?_, ?_⟩
      · have := hqmax q' hq'
        rwa [replica_phi_neg_beta, replica_phi_neg_beta] at this
      · rw [← skReplica_ratio_neg_beta]
        exact hqfix
      · rw [replica_phi_neg_beta] at hlim
        simpa only [integral_partition_pow_neg_beta] using hlim
    · subst hzero
      exact exists_skReplica_maximizer_fixedPoint_zero n h
    · exact exists_skReplica_maximizer_fixedPoint_pos n hn2 β h hpos

end SpinGlasses
