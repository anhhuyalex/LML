/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Replica.Variational.FixedPoint

/-!
# Large numbers of replicas: the maximizers tend to one

Talagrand, *Spin Glasses* Vol. I, Section 1.13, the paragraph after Eq. (1.411): for `h = 0` and
`β < 1` the book observes that the maximizers `q_n` of the integer-replica problem satisfy
`q_n → 1` as `n → ∞`, which is far from the value `q = 0` of the replica-symmetric solution, and
concludes that the information of Theorem 1.13.1 about large `n` is irrelevant to the
continuation `n → 0`.

The proof here is quantitative and holds for every maximizer, every real `h` and every `β ≠ 0`
(no smallness of `β`): comparing `Φ_n(q)` with `Φ_n(1)` through the two elementary bounds
`exp (n |h| + β² n² / 2) ≤ S_n(1)` and `S_n(q) ≤ 2 ^ n exp (n |h| + β² q n² / 2)` on the finite
sum `S_n` gives `(n - 1) β² (1 - q)² ≤ 4 log 2`.  Nothing is claimed about real `n`, nor about the
exchange of limits.

## Main declarations

* `SpinGlasses.skReplica_maximizer_sq_le`: `(n - 1) β² (1 - q)² ≤ 4 log 2` for every maximizer `q`.
* `SpinGlasses.tendsto_skReplica_maximizer_one`: `q_n → 1` for any choice of maximizers.
* `SpinGlasses.exists_skReplica_maximizer_fixedPoint_tendsto_one`: the maximizing fixed points of
  `exists_skReplica_maximizer_fixedPoint` can be chosen along all `n ≥ 1`, and then `q_n → 1`.
-/

@[expose] public section

open Finset Real MeasureTheory ProbabilityTheory Filter Topology Set

namespace SpinGlasses

lemma abs_sum_units_cast_le (n : ℕ) (ε : Fin n → ℤˣ) :
    |∑ l, ((ε l : ℤ) : ℝ)| ≤ n := by
  calc |∑ l, ((ε l : ℤ) : ℝ)| ≤ ∑ l, |((ε l : ℤ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ _l : Fin n, (1 : ℝ) := Finset.sum_congr rfl fun l _ => abs_units_cast_eq_one (ε l)
    _ = n := by simp

/-- Upper bound for the finite partition sum: every configuration has `|∑ ε| ≤ n`. -/
lemma skReplicaSum_le (n : ℕ) (β h q : ℝ) (hq : 0 ≤ q) :
    skReplicaSum n β h q ≤ (2 : ℝ) ^ n * Real.exp (n * |h| + β ^ 2 * q * (n : ℝ) ^ 2 / 2) := by
  rw [skReplicaSum_def]
  calc ∑ ε : Fin n → ℤˣ, Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
        β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * q / 2)
      ≤ ∑ _ε : Fin n → ℤˣ, Real.exp (n * |h| + β ^ 2 * q * (n : ℝ) ^ 2 / 2) := by
        refine Finset.sum_le_sum fun ε _ => Real.exp_le_exp.2 ?_
        have hm := abs_sum_units_cast_le n ε
        have h1 : h * ∑ l, ((ε l : ℤ) : ℝ) ≤ n * |h| :=
          (le_abs_self _).trans (by
            rw [abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right hm (abs_nonneg h))
        have h2 : (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hm 2
        have h3 : β ^ 2 * q ≥ 0 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h2 h3]
    _ = (2 : ℝ) ^ n * Real.exp (n * |h| + β ^ 2 * q * (n : ℝ) ^ 2 / 2) := by
        simp [Finset.sum_const]

/-- Lower bound at `q = 1`: the all-aligned configuration with the sign of `h`. -/
lemma le_skReplicaSum_one (n : ℕ) (β h : ℝ) :
    Real.exp (n * |h| + β ^ 2 * (n : ℝ) ^ 2 / 2) ≤ skReplicaSum n β h 1 := by
  rw [skReplicaSum_def]
  obtain ⟨ε₀, hε₀⟩ : ∃ ε₀ : Fin n → ℤˣ, h * ∑ l, ((ε₀ l : ℤ) : ℝ) = n * |h| ∧
      (∑ l, ((ε₀ l : ℤ) : ℝ)) ^ 2 = (n : ℝ) ^ 2 := by
    rcases le_total 0 h with hh | hh
    · exact ⟨fun _ => 1, by simp [abs_of_nonneg hh, mul_comm]⟩
    · refine ⟨fun _ => -1, ?_, by simp⟩
      simp [abs_of_nonpos hh]
      ring
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun ε : Fin n → ℤˣ =>
    Real.exp (h * ∑ l, ((ε l : ℤ) : ℝ) +
      β ^ 2 * (∑ l, ((ε l : ℤ) : ℝ)) ^ 2 * 1 / 2)) (fun _ _ => (Real.exp_pos _).le)
    (Finset.mem_univ ε₀))
  rw [hε₀.1, hε₀.2]
  congr 1
  ring

/-- **Quantitative large-replica bound.**  For `1 ≤ n`, any maximizer `q ≥ 0` of the replica
objective `Φ_n` over `[0, ∞)` satisfies `(n - 1) β² (1 - q)² ≤ 4 log 2`. -/
theorem skReplica_maximizer_sq_le (n : ℕ) (hn : 1 ≤ n) (β h q : ℝ) (hq : 0 ≤ q)
    (hmax : ∀ q' : ℝ, 0 ≤ q' →
      n * β ^ 2 * (1 - q') ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q' ^ 2 / 4 +
          Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q' + h) ^ n ∂(gaussianReal 0 1)) ≤
        n * β ^ 2 * (1 - q) ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
          Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))) :
    ((n : ℝ) - 1) * β ^ 2 * (1 - q) ^ 2 ≤ 4 * Real.log 2 := by
  have h1 := hmax 1 zero_le_one
  rw [← skReplicaSmoothObjective_eq_phi n β h 1 zero_le_one,
    ← skReplicaSmoothObjective_eq_phi n β h q hq] at h1
  simp only [skReplicaSmoothObjective_def] at h1
  have hLq : Real.log (skReplicaSum n β h q) ≤
      n * Real.log 2 + (n * |h| + β ^ 2 * q * (n : ℝ) ^ 2 / 2) := by
    refine (Real.log_le_log (skReplicaSum_pos n β h q) (skReplicaSum_le n β h q hq)).trans ?_
    rw [Real.log_mul (pow_pos two_pos n).ne' (Real.exp_pos _).ne', Real.log_pow,
      Real.log_exp]
  have hL1 : n * |h| + β ^ 2 * (n : ℝ) ^ 2 / 2 ≤ Real.log (skReplicaSum n β h 1) := by
    simpa using Real.log_le_log (Real.exp_pos _) (le_skReplicaSum_one n β h)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have key : (n : ℝ) * (((n : ℝ) - 1) * β ^ 2 * (1 - q) ^ 2) ≤ (n : ℝ) * (4 * Real.log 2) := by
    nlinarith [h1, hLq, hL1]
  exact le_of_mul_le_mul_left key hnpos

/-- **The maximizers tend to one** as the number of replicas grows (Talagrand's remark after
Eq. (1.411)).  Let `β ≠ 0`, `h` be real, and `q n` a maximizer of `Φ_n` over `[0, ∞)` for every
`n ≥ 1` (for example the maximizing fixed points of `exists_skReplica_maximizer_fixedPoint`).
Then `q n → 1`.  The book states this for `h = 0` and `β < 1`; the proof needs neither. -/
theorem tendsto_skReplica_maximizer_one {β : ℝ} (hβ : β ≠ 0) (h : ℝ) (q : ℕ → ℝ)
    (hq : ∀ n : ℕ, 1 ≤ n → 0 ≤ q n ∧ ∀ q' : ℝ, 0 ≤ q' →
      n * β ^ 2 * (1 - q') ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q' ^ 2 / 4 +
          Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q' + h) ^ n ∂(gaussianReal 0 1)) ≤
        n * β ^ 2 * (1 - q n) ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q n ^ 2 / 4 +
          Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt (q n) + h) ^ n ∂(gaussianReal 0 1))) :
    Tendsto q atTop (𝓝 1) := by
  have hβ2 : 0 < β ^ 2 := by positivity
  set B : ℕ → ℝ := fun n => 4 * Real.log 2 / β ^ 2 * ((n : ℝ) - 1)⁻¹ with hB
  have hBt : Tendsto B atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => ((n : ℝ) - 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (by
        simpa [sub_eq_add_neg] using
          tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_natCast_atTop_atTop)
    simpa [hB] using this.const_mul (4 * Real.log 2 / β ^ 2)
  have hA : Tendsto (fun n => Real.sqrt (B n)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hBt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hA
  filter_upwards [eventually_ge_atTop 2] with n hn
  obtain ⟨hq0, hmax⟩ := hq n (by omega)
  have hsq := skReplica_maximizer_sq_le n (by omega) β h (q n) hq0 hmax
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hBeq : B n = 4 * Real.log 2 / (((n : ℝ) - 1) * β ^ 2) := by
    simp only [hB]
    field_simp
  have hle : (1 - q n) ^ 2 ≤ B n := by
    rw [hBeq, le_div_iff₀ (mul_pos hn1 hβ2)]
    nlinarith [hsq]
  calc ‖q n - 1‖ = Real.sqrt ((1 - q n) ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, Real.norm_eq_abs, abs_sub_comm]
    _ ≤ Real.sqrt (B n) := Real.sqrt_le_sqrt hle

/-- **Maximizing fixed points along all integers `n ≥ 1` converge to one.**  For `β ≠ 0` and real
`h`, one can choose, for every `n ≥ 1`, a point `q n ∈ [0, 1]` that maximizes `Φ_n` over
`[0, ∞)` and solves the tilted fixed-point equation of Eq. (1.408), and every such choice satisfies
`q n → 1`.  For `h = 0` the equation reads `q = 𝔼 [ch^n Y th² Y] / 𝔼 [ch^n Y]`; the value `q = 0`
that the replica-symmetric solution has for `h = 0`, `β < 1` is therefore not seen by large `n`. -/
theorem exists_skReplica_maximizer_fixedPoint_tendsto_one {β : ℝ} (hβ : β ≠ 0) (h : ℝ) :
    ∃ q : ℕ → ℝ, Tendsto q atTop (𝓝 1) ∧ ∀ n : ℕ, 1 ≤ n → 0 ≤ q n ∧ q n ≤ 1 ∧
      (∀ q' : ℝ, 0 ≤ q' →
        n * β ^ 2 * (1 - q') ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q' ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q' + h) ^ n ∂(gaussianReal 0 1)) ≤
          n * β ^ 2 * (1 - q n) ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q n ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt (q n) + h) ^ n ∂(gaussianReal 0 1))) ∧
      q n = (∫ z : ℝ, cosh (β * z * Real.sqrt (q n) + h) ^ n *
            tanh (β * z * Real.sqrt (q n) + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt (q n) + h) ^ n ∂(gaussianReal 0 1)) := by
  have H : ∀ n : ℕ, ∃ q : ℝ, 1 ≤ n → 0 ≤ q ∧ q ≤ 1 ∧
      (∀ q' : ℝ, 0 ≤ q' →
        n * β ^ 2 * (1 - q') ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q' ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q' + h) ^ n ∂(gaussianReal 0 1)) ≤
          n * β ^ 2 * (1 - q) ^ 2 / 4 - (n : ℝ) ^ 2 * β ^ 2 * q ^ 2 / 4 +
            Real.log (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1))) ∧
      q = (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n *
            tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1)) /
          (∫ z : ℝ, cosh (β * z * Real.sqrt q + h) ^ n ∂(gaussianReal 0 1)) := fun n => by
    by_cases hn : 1 ≤ n
    · have : NeZero n := ⟨by omega⟩
      obtain ⟨q, h0, h1, hm, hf, -⟩ := exists_skReplica_maximizer_fixedPoint n β h
      exact ⟨q, fun _ => ⟨h0, h1, hm, hf⟩⟩
    · exact ⟨0, fun h' => absurd h' hn⟩
  choose q hq using H
  exact ⟨q, tendsto_skReplica_maximizer_one hβ h q fun n hn =>
    ⟨(hq n hn).1, (hq n hn).2.2.1⟩, hq⟩

end SpinGlasses
