/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.SKReplicaAlgebra
public import LeanMachineLearning.SpinGlasses.Talagrand.GaussianFluctuation.SKGaussianFluctuation
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiExp
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.HypercubeProduct

/-!
# The moments `𝔼 Z_N^n` as a Gaussian integral (Talagrand, Eqs. (1.398)-(1.399))

For the SK partition function `Z_N = ∑_σ exp (-H_N(g, σ))`,
`𝔼 Z_N^n = exp (β² n (N - n) / 4) 𝔼 exp (N A(x / √N))`, where `x` is a standard Gaussian vector
indexed by the pairs `ℓ < ℓ'` of replicas and
`A(g) = log ∑_{ε ∈ {±1}^n} exp (β ∑_{ℓ<ℓ'} g_{ℓℓ'} ε_ℓ ε_ℓ' + h ∑_ℓ ε_ℓ)`.
This is exact: no limit is taken.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

namespace SpinGlasses

/-- The function `A` of Talagrand's proof of Theorem 1.13.1: the logarithm of the partition
function of `n` coupled replicas of a single site, with couplings `g` between the replicas.
This is a genuine object used in many statements of Section 1.13. -/
noncomputable def skReplicaLogPartition (n : ℕ) (β h : ℝ) (g : FinPairs n → ℝ) : ℝ :=
  Real.log (∑ ε : Fin n → ℤˣ, Real.exp (β * ∑ p : FinPairs n,
    g p * ((ε p.val.1 : ℤ) : ℝ) * ((ε p.val.2 : ℤ) : ℝ) + h * ∑ l, ((ε l : ℤ) : ℝ)))

/-- The exponent of the replica partition function of `N` spins and `n` replicas, written as a
function of replica-major spins. -/
theorem sum_skGibbsEnergy_replicas (N n : ℕ) (β h : ℝ) (g : FinPairs N → ℝ)
    (σ : Fin n → Fin N → ℤˣ) :
    ∑ l, skGibbsEnergy N β h g (σ l) =
      ∑ p : FinPairs N, g p * ((Real.sqrt N)⁻¹ * β *
        ∑ l, ((σ l p.val.1 : ℤ) : ℝ) * ((σ l p.val.2 : ℤ) : ℝ)) +
        h * ∑ l, ∑ i, ((σ l i : ℤ) : ℝ) := by
  simp only [skGibbsEnergy, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- The `n`-replica Boltzmann weight of replica-major spins is the exponential of a linear form in
the couplings times a constant. -/
theorem exp_sum_skGibbsEnergy_replicas (N n : ℕ) (β h : ℝ) (σ : Fin n → Fin N → ℤˣ)
    (g : FinPairs N → ℝ) :
    Real.exp (∑ l, skGibbsEnergy N β h g (σ l)) =
      Real.exp (h * ∑ l, ∑ i, ((σ l i : ℤ) : ℝ)) * Real.exp (∑ p : FinPairs N,
        ((Real.sqrt N)⁻¹ * β * ∑ l, ((σ l p.val.1 : ℤ) : ℝ) * ((σ l p.val.2 : ℤ) : ℝ)) * g p) := by
  rw [← Real.exp_add, sum_skGibbsEnergy_replicas, add_comm]
  congr 1
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- The Gaussian average over the spin couplings of the `n`-replica Boltzmann weight of
replica-major spins `σ`: the right-hand side of Eq. (1.398) before summing over `σ`. -/
theorem integral_exp_sum_skGibbsEnergy_replicas {N : ℕ} (hN : 0 < N) (n : ℕ) (β h : ℝ)
    (σ : Fin n → Fin N → ℤˣ) :
    ∫ g : FinPairs N → ℝ, Real.exp (∑ l, skGibbsEnergy N β h g (σ l))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) =
      Real.exp (β ^ 2 * n * (N - n) / 4) * Real.exp (β ^ 2 / (2 * N) *
        ∑ q : FinPairs n, (∑ i, ((σ q.val.1 i : ℤ) : ℝ) * ((σ q.val.2 i : ℤ) : ℝ)) ^ 2 +
        h * ∑ l, ∑ i, ((σ l i : ℤ) : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set c : FinPairs N → ℝ := fun p => (Real.sqrt N)⁻¹ * β *
    ∑ l, ((σ l p.val.1 : ℤ) : ℝ) * ((σ l p.val.2 : ℤ) : ℝ) with hc
  simp_rw [exp_sum_skGibbsEnergy_replicas]
  rw [integral_const_mul, integral_exp_sum_mul_gaussianReal c, ← Real.exp_add]
  have hsq : ∑ p, c p ^ 2 / 2 = β ^ 2 / (2 * N) *
      ∑ p : FinPairs N, (∑ l, ((σ l p.val.1 : ℤ) : ℝ) * ((σ l p.val.2 : ℤ) : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hc]
    have : ((Real.sqrt N)⁻¹) ^ 2 = (N : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hNpos.le]
    calc ((Real.sqrt N)⁻¹ * β * ∑ l, ((σ l p.val.1 : ℤ) : ℝ) * ((σ l p.val.2 : ℤ) : ℝ)) ^ 2 / 2
        = ((Real.sqrt N)⁻¹) ^ 2 * β ^ 2 *
          (∑ l, ((σ l p.val.1 : ℤ) : ℝ) * ((σ l p.val.2 : ℤ) : ℝ)) ^ 2 / 2 := by ring
      _ = _ := by rw [this]; field_simp
  rw [hsq]
  have h397 := sum_finPairs_sq_replicas n N (fun l i => ((σ l i : ℤ) : ℝ))
    (fun l i => units_cast_sq _)
  rw [h397, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- The `n`-replica Boltzmann weight is integrable in the couplings. -/
theorem integrable_exp_sum_skGibbsEnergy_replicas (N n : ℕ) (β h : ℝ) (σ : Fin n → Fin N → ℤˣ) :
    Integrable (fun g : FinPairs N → ℝ => Real.exp (∑ l, skGibbsEnergy N β h g (σ l)))
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  simp_rw [exp_sum_skGibbsEnergy_replicas]
  exact (integrable_exp_sum_mul_gaussianReal _).const_mul _

/-- **Eqs. (1.397)-(1.398), exactly:** the `n`-th moment of the partition function is
`exp (β² n (N - n) / 4)` times a sum over `n` replicas of the Gaussian weight
`exp (β²/(2N) ∑_{ℓ<ℓ'} (σ^ℓ · σ^ℓ')² + h ∑ σ)`. -/
theorem integral_sk_partition_pow_eq {N : ℕ} (hN : 0 < N) (n : ℕ) (β h : ℝ) :
    ∫ g : FinPairs N → ℝ, (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ n
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) =
      Real.exp (β ^ 2 * n * (N - n) / 4) * ∑ σ : Fin n → Fin N → ℤˣ,
        Real.exp (β ^ 2 / (2 * N) *
          ∑ q : FinPairs n, (∑ i, ((σ q.val.1 i : ℤ) : ℝ) * ((σ q.val.2 i : ℤ) : ℝ)) ^ 2 +
          h * ∑ l, ∑ i, ((σ l i : ℤ) : ℝ)) := by
  have hpow (g : FinPairs N → ℝ) :
      (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ n =
        ∑ σ : Fin n → Fin N → ℤˣ, Real.exp (∑ l, skGibbsEnergy N β h g (σ l)) := by
    rw [Fintype.sum_pow]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Real.exp_sum]
  simp_rw [hpow]
  rw [integral_finsetSum _ (fun σ _ => integrable_exp_sum_skGibbsEnergy_replicas N n β h σ),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_exp_sum_skGibbsEnergy_replicas hN]

/-- **Eq. (1.399), exactly:** the Gaussian average of `exp (N A (x / √N))` over the replica
couplings is the same replica sum. -/
theorem integral_exp_replica_log_partition {N : ℕ} (hN : 0 < N) (n : ℕ) (β h : ℝ) :
    ∫ x : FinPairs n → ℝ, Real.exp (N * skReplicaLogPartition n β h
        (fun p => x p / Real.sqrt N)) ∂(Measure.pi fun _ : FinPairs n => gaussianReal 0 1) =
      ∑ σ : Fin n → Fin N → ℤˣ,
        Real.exp (β ^ 2 / (2 * N) *
          ∑ q : FinPairs n, (∑ i, ((σ q.val.1 i : ℤ) : ℝ) * ((σ q.val.2 i : ℤ) : ℝ)) ^ 2 +
          h * ∑ l, ∑ i, ((σ l i : ℤ) : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hpow (x : FinPairs n → ℝ) : Real.exp (N * skReplicaLogPartition n β h
      (fun p => x p / Real.sqrt N)) = ∑ ρ : Fin N → Fin n → ℤˣ, Real.exp (h * ∑ i, ∑ l,
        ((ρ i l : ℤ) : ℝ)) * Real.exp (∑ q : FinPairs n, ((Real.sqrt N)⁻¹ * β *
          ∑ i, ((ρ i q.val.1 : ℤ) : ℝ) * ((ρ i q.val.2 : ℤ) : ℝ)) * x q) := by
    unfold skReplicaLogPartition
    rw [Real.exp_nat_mul, Real.exp_log (Finset.sum_pos (fun ε _ => Real.exp_pos _)
      Finset.univ_nonempty), Fintype.sum_pow]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [← Real.exp_sum, ← Real.exp_add]
    congr 1
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [add_comm]
    congr 1
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have e : ∑ i, x q / Real.sqrt N * ((ρ i q.val.1 : ℤ) : ℝ) * ((ρ i q.val.2 : ℤ) : ℝ) =
        x q / Real.sqrt N * ∑ i, ((ρ i q.val.1 : ℤ) : ℝ) * ((ρ i q.val.2 : ℤ) : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    field_simp
  simp_rw [hpow]
  rw [integral_finsetSum _ (fun ρ _ => (integrable_exp_sum_mul_gaussianReal _).const_mul _)]
  rw [← Fintype.sum_equiv (Equiv.piComm fun (_ : Fin N) (_ : Fin n) => ℤˣ)
    (fun ρ : Fin N → Fin n → ℤˣ => ∫ x : FinPairs n → ℝ, Real.exp (h * ∑ i, ∑ l,
        ((ρ i l : ℤ) : ℝ)) * Real.exp (∑ q : FinPairs n, ((Real.sqrt N)⁻¹ * β *
          ∑ i, ((ρ i q.val.1 : ℤ) : ℝ) * ((ρ i q.val.2 : ℤ) : ℝ)) * x q)
        ∂(Measure.pi fun _ : FinPairs n => gaussianReal 0 1))
    (fun σ : Fin n → Fin N → ℤˣ => Real.exp (β ^ 2 / (2 * N) *
          ∑ q : FinPairs n, (∑ i, ((σ q.val.1 i : ℤ) : ℝ) * ((σ q.val.2 i : ℤ) : ℝ)) ^ 2 +
          h * ∑ l, ∑ i, ((σ l i : ℤ) : ℝ))) (fun ρ => ?_)]
  rw [integral_const_mul, integral_exp_sum_mul_gaussianReal, ← Real.exp_add]
  congr 1
  have hsq : ∑ q : FinPairs n, ((Real.sqrt N)⁻¹ * β *
      ∑ i, ((ρ i q.val.1 : ℤ) : ℝ) * ((ρ i q.val.2 : ℤ) : ℝ)) ^ 2 / 2 = β ^ 2 / (2 * N) *
      ∑ q : FinPairs n, (∑ i, ((ρ i q.val.1 : ℤ) : ℝ) * ((ρ i q.val.2 : ℤ) : ℝ)) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : ((Real.sqrt N)⁻¹) ^ 2 = (N : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hNpos.le]
    calc ((Real.sqrt N)⁻¹ * β * ∑ i, ((ρ i q.val.1 : ℤ) : ℝ) * ((ρ i q.val.2 : ℤ) : ℝ)) ^ 2 / 2
        = ((Real.sqrt N)⁻¹) ^ 2 * β ^ 2 *
          (∑ i, ((ρ i q.val.1 : ℤ) : ℝ) * ((ρ i q.val.2 : ℤ) : ℝ)) ^ 2 / 2 := by ring
      _ = _ := by rw [this]; field_simp
  rw [hsq, add_comm, Finset.sum_comm]
  rfl

/-- **Eqs. (1.398)-(1.399).** `𝔼 Z_N^n = exp (β² n (N - n) / 4) 𝔼 exp (N A (x / √N))`. -/
theorem integral_sk_partition_pow_eq_laplace {N : ℕ} (hN : 0 < N) (n : ℕ) (β h : ℝ) :
    ∫ g : FinPairs N → ℝ, (∑ σ : Fin N → ℤˣ, Real.exp (skGibbsEnergy N β h g σ)) ^ n
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) =
      Real.exp (β ^ 2 * n * (N - n) / 4) * ∫ x : FinPairs n → ℝ,
        Real.exp (N * skReplicaLogPartition n β h (fun p => x p / Real.sqrt N))
          ∂(Measure.pi fun _ : FinPairs n => gaussianReal 0 1) := by
  rw [integral_sk_partition_pow_eq hN, integral_exp_replica_log_partition hN]

end SpinGlasses
