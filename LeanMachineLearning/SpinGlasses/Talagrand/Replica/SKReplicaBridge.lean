/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.SKReplicaMaximizer
public import LeanMachineLearning.SpinGlasses.Talagrand.SpinDecorrelation.SKSiteSymmetry

/-!
# From pair couplings to symmetric matrices, and the existence of a maximizer of `B`

The Laplace principle is stated for the pair couplings `g : FinPairs n → ℝ`, while the proof of
Proposition 1.13.2 uses symmetric matrices. This file passes between the two, and shows that
`B(g) = A(g) - ½ ∑ g²` attains its maximum.
-/

@[expose] public section

open Finset Real Filter Topology
open scoped BigOperators

namespace SpinGlasses

variable {n : ℕ}

theorem skSymmCoupling_diag (g : FinPairs n → ℝ) (l : Fin n) : skSymmCoupling g l l = 0 := by
  simp [skSymmCoupling]

theorem skSymmCoupling_pair (g : FinPairs n → ℝ) (p : FinPairs n) :
    skSymmCoupling g p.val.1 p.val.2 = g p := by
  simp [skSymmCoupling, p.property]

/-- The pair couplings of a matrix. -/
theorem skSymmCoupling_of_matrix (G : Fin n → Fin n → ℝ) (hs : ∀ l l', G l l' = G l' l)
    (hd : ∀ l, G l l = 0) :
    skSymmCoupling (fun p : FinPairs n => G p.val.1 p.val.2) = G := by
  funext l l'
  unfold skSymmCoupling
  by_cases h : l < l'
  · simp [h]
  · by_cases h' : l' < l
    · simp [h, h', hs l l']
    · have : l = l' := le_antisymm (not_lt.1 h') (not_lt.1 h)
      subst this
      simp [hd]

/-- `∑_p g_p c_p` as half of the symmetric double sum. -/
theorem sum_finPairs_eq_half_sym (g : FinPairs n → ℝ) (c : Fin n → Fin n → ℝ)
    (hc : ∀ l l', c l l' = c l' l) :
    ∑ p : FinPairs n, g p * c p.val.1 p.val.2 =
      (∑ l, ∑ l', skSymmCoupling g l l' * c l l') / 2 := by
  have := sum_fin_symm_eq_diag_add_two_sum_finPairs n (fun l l' => skSymmCoupling g l l' * c l l')
    (fun l l' => by rw [skSymmCoupling_comm g l l', hc l l'])
  simp only [skSymmCoupling_diag, zero_mul, sum_const_zero, zero_add, skSymmCoupling_pair] at this
  linarith

/-- `A(g)` equals the matrix log-partition function of the symmetric extension. -/
theorem skReplicaLogPartition_eq_mat (β h : ℝ) (g : FinPairs n → ℝ) :
    skReplicaLogPartition n β h g = skReplicaMatLogPartition n β h (skSymmCoupling g) := by
  unfold skReplicaLogPartition skReplicaMatLogPartition
  congr 1
  refine Finset.sum_congr rfl fun ε _ => ?_
  congr 1
  have := sum_finPairs_eq_half_sym g (fun l l' => ((ε l : ℤ) : ℝ) * ((ε l' : ℤ) : ℝ))
    (fun l l' => mul_comm _ _)
  have h2 : ∑ p : FinPairs n, g p * ((ε p.val.1 : ℤ) : ℝ) * ((ε p.val.2 : ℤ) : ℝ) =
      ∑ p : FinPairs n, g p * (((ε p.val.1 : ℤ) : ℝ) * ((ε p.val.2 : ℤ) : ℝ)) :=
    Finset.sum_congr rfl fun p _ => by ring
  rw [h2, this]
  have h3 : ∑ l, ∑ l', skSymmCoupling g l l' * (((ε l : ℤ) : ℝ) * ((ε l' : ℤ) : ℝ)) =
      ∑ l, ∑ l', skSymmCoupling g l l' * ((ε l : ℤ) : ℝ) * ((ε l' : ℤ) : ℝ) :=
    Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => by ring
  rw [h3]
  ring

/-- `∑_p g_p²` is half of the sum of squares of the symmetric extension. -/
theorem sum_sq_finPairs_eq_half_sym (g : FinPairs n → ℝ) :
    ∑ p : FinPairs n, g p ^ 2 = (∑ l, ∑ l', skSymmCoupling g l l' ^ 2) / 2 := by
  have := sum_finPairs_eq_half_sym g (skSymmCoupling g) (skSymmCoupling_comm g)
  simp only [skSymmCoupling_pair] at this
  simpa [sq] using this

/-- **`B` for pair couplings:** `B(g) = A(g) - ½ ∑_{ℓ<ℓ'} g_{ℓℓ'}²` is the matrix objective of the
symmetric extension. -/
theorem skReplicaLogPartition_sub_eq_objective (β h : ℝ) (g : FinPairs n → ℝ) :
    skReplicaLogPartition n β h g - (∑ p : FinPairs n, g p ^ 2) / 2 =
      skReplicaMatObjective n β h (skSymmCoupling g) := by
  unfold skReplicaMatObjective
  rw [skReplicaLogPartition_eq_mat, sum_sq_finPairs_eq_half_sym]
  ring

/-- The exponent of the replica Boltzmann weight is at most `|β| ∑|g| + |h| n` in absolute value. -/
theorem abs_replica_energy_le (β h : ℝ) (g : FinPairs n → ℝ) (ε : Fin n → ℤˣ) :
    |β * ∑ p : FinPairs n, g p * ((ε p.val.1 : ℤ) : ℝ) * ((ε p.val.2 : ℤ) : ℝ) +
        h * ∑ l, ((ε l : ℤ) : ℝ)| ≤ |β| * ∑ p, |g p| + |h| * n := by
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
    rw [abs_mul, abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one, mul_one]
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simp [abs_units_cast_eq_one]

/-- **Linear growth of `A`** (used for the Laplace principle): `|A(g)| ≤ K (1 + ∑|g|)`. -/
theorem abs_skReplicaLogPartition_le (β h : ℝ) (g : FinPairs n → ℝ) :
    |skReplicaLogPartition n β h g| ≤
      (n * Real.log 2 + n * |h| + |β|) * (1 + ∑ p, |g p|) := by
  set M : ℝ := |β| * ∑ p, |g p| + |h| * n with hM
  have hM0 : 0 ≤ M := by positivity
  set S : ℝ := ∑ ε : Fin n → ℤˣ, Real.exp (β * ∑ p : FinPairs n,
    g p * ((ε p.val.1 : ℤ) : ℝ) * ((ε p.val.2 : ℤ) : ℝ) + h * ∑ l, ((ε l : ℤ) : ℝ)) with hS
  have hcard : (Finset.univ : Finset (Fin n → ℤˣ)).card = 2 ^ n := by
    simp [Finset.card_univ, Fintype.card_units_int]
  have hup : S ≤ 2 ^ n * Real.exp M := by
    calc S ≤ ∑ _ε : Fin n → ℤˣ, Real.exp M := Finset.sum_le_sum fun ε _ =>
          Real.exp_le_exp.2 ((le_abs_self _).trans (abs_replica_energy_le β h g ε))
      _ = _ := by rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast; ring
  have hlow : 2 ^ n * Real.exp (-M) ≤ S := by
    calc (2 : ℝ) ^ n * Real.exp (-M) = ∑ _ε : Fin n → ℤˣ, Real.exp (-M) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]; push_cast; ring
      _ ≤ S := Finset.sum_le_sum fun ε _ => Real.exp_le_exp.2
          (neg_le_of_abs_le (abs_replica_energy_le β h g ε))
  have hSpos : 0 < S := Finset.sum_pos (fun ε _ => Real.exp_pos _) Finset.univ_nonempty
  have hlog1 : Real.log S ≤ n * Real.log 2 + M := by
    calc Real.log S ≤ Real.log (2 ^ n * Real.exp M) := Real.log_le_log hSpos hup
      _ = _ := by rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow,
          Real.log_exp]
  have hlog2 : n * Real.log 2 - M ≤ Real.log S := by
    calc n * Real.log 2 - M = Real.log (2 ^ n * Real.exp (-M)) := by
          rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow, Real.log_exp]
          ring
      _ ≤ Real.log S := Real.log_le_log (by positivity) hlow
  have hn : 0 ≤ (n : ℝ) * Real.log 2 := by positivity
  change |Real.log S| ≤ _
  rw [abs_le]
  have hsum : 0 ≤ ∑ p, |g p| := Finset.sum_nonneg fun p _ => abs_nonneg _
  have e : (↑n * Real.log 2 + ↑n * |h| + |β|) * (1 + ∑ p, |g p|) =
      n * Real.log 2 + n * |h| + |β| + (n * Real.log 2) * ∑ p, |g p| +
        (n * |h|) * ∑ p, |g p| + |β| * ∑ p, |g p| := by ring
  have h1 : 0 ≤ (n * Real.log 2) * ∑ p, |g p| := mul_nonneg hn hsum
  have h2 : 0 ≤ ((n : ℝ) * |h|) * ∑ p, |g p| := mul_nonneg (by positivity) hsum
  have h3 : 0 ≤ (n : ℝ) * |h| := by positivity
  have h4 : 0 ≤ |β| := abs_nonneg β
  have h5 : |h| * (n : ℝ) = (n : ℝ) * |h| := mul_comm _ _
  rw [e]
  constructor <;> linarith

theorem continuous_skReplicaLogPartition (β h : ℝ) :
    Continuous fun g : FinPairs n → ℝ => skReplicaLogPartition n β h g := by
  unfold skReplicaLogPartition
  refine Continuous.log (continuous_finsetSum _ fun ε _ => by fun_prop) fun g => ?_
  exact (Finset.sum_pos (fun ε _ => Real.exp_pos _) Finset.univ_nonempty).ne'

theorem norm_sq_le_sum_sq (g : FinPairs n → ℝ) : ‖g‖ ^ 2 ≤ ∑ p, g p ^ 2 := by
  have h0 : 0 ≤ ∑ p, g p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  have : ‖g‖ ≤ Real.sqrt (∑ p, g p ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun p => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun p => g p ^ 2)
      (fun p _ => sq_nonneg _) (Finset.mem_univ p))
  calc ‖g‖ ^ 2 ≤ Real.sqrt (∑ p, g p ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = _ := Real.sq_sqrt h0

theorem sum_abs_le_card_mul_norm (g : FinPairs n → ℝ) :
    ∑ p, |g p| ≤ (Fintype.card (FinPairs n) : ℝ) * ‖g‖ := by
  calc ∑ p, |g p| ≤ ∑ _p : FinPairs n, ‖g‖ := Finset.sum_le_sum fun p _ => by
        rw [← Real.norm_eq_abs]; exact norm_le_pi_norm g p
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **`B` attains its maximum.** The function `B(g) = A(g) - ½ ∑ g²` of pair couplings has a
global maximizer (the book writes `max` without proof). -/
theorem exists_forall_objective_le (β h : ℝ) :
    ∃ g : FinPairs n → ℝ, ∀ g' : FinPairs n → ℝ,
      skReplicaLogPartition n β h g' - (∑ p, g' p ^ 2) / 2 ≤
        skReplicaLogPartition n β h g - (∑ p, g p ^ 2) / 2 := by
  set K : ℝ := n * Real.log 2 + n * |h| + |β| with hK
  have hK0 : 0 ≤ K := by positivity
  set d : ℝ := ((Fintype.card (FinPairs n) : ℕ) : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hcont : Continuous fun g : FinPairs n → ℝ =>
      skReplicaLogPartition n β h g - (∑ p, g p ^ 2) / 2 :=
    (continuous_skReplicaLogPartition β h).sub
      ((continuous_finsetSum _ fun p _ => by fun_prop).div_const 2)
  set B0 : ℝ := skReplicaLogPartition n β h 0 - (∑ p : FinPairs n, (0 : FinPairs n → ℝ) p ^ 2) / 2
    with hB0
  obtain ⟨g, hg⟩ := hcont.exists_forall_ge' 0 (by
    filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop
      (max (2 * d * K + 2) (K - B0))] with g hgn
    have h1 := abs_skReplicaLogPartition_le β h g
    have h2 := sum_abs_le_card_mul_norm g
    have h3 := norm_sq_le_sum_sq g
    have hr : 2 * d * K + 2 < ‖g‖ := lt_of_le_of_lt (le_max_left _ _) hgn
    have hr2 : K - B0 < ‖g‖ := lt_of_le_of_lt (le_max_right _ _) hgn
    have h4 : skReplicaLogPartition n β h g ≤ K * (1 + d * ‖g‖) :=
      (le_abs_self _).trans (h1.trans (mul_le_mul_of_nonneg_left (by linarith) hK0))
    show skReplicaLogPartition n β h g - (∑ p, g p ^ 2) / 2 ≤ B0
    nlinarith [mul_nonneg hK0 hd0, norm_nonneg g])
  exact ⟨g, hg⟩

end SpinGlasses
