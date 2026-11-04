/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTMixed
public import LeanMachineLearning.SpinGlasses.SKTBasisCoefficients

/-!
# The overlap moment theorem with the Section 1.8 covariance constants

The reference variances here are exactly the size-dependent expressions in the earlier
second-moment theorems. The proof transports the already proved mixed moment estimate
through the shared algebraic identities; it does not repeat a moment induction.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real

namespace SpinGlasses

/-- **Theorem 1.10.1 with the covariance constants of Section 1.8.** The variances `A2`,
`B2`, and `C2` already include the inverse system size, as in Theorem 1.8.12. -/
theorem sk_T_mixed_gaussian_moment_covariance_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype R] [LinearOrder R]
    (L S : J → Bool) (hnorm : ∀ j, ¬(L j = true ∧ S j = true) → S j = false)
    (a b : J → R) (hord : ∀ j, L j = true → S j = true → a j < b j) (s : Finset J) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let T : J → (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ :=
      fun j g ρ => ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if L j then (ρ (a j) i : ℝ) - bmean g i else bmean g i) *
        (if S j then (ρ (b j) i : ℝ) - bmean g i else bmean g i)) -
          (if L j || S j then 0 else q)
    let νT : Finset J → ℝ := fun s => ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
      ∏ j ∈ s, T j g ρ ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let D : ℝ := 1 - β ^ 2 * (1 - 4 * q + 3 * qh)
    let A2 : ℝ := α / ((N + 1 : ℝ) * (1 - β ^ 2 * α))
    let B2 : ℝ := (q - qh) / ((N + 1 : ℝ) * (1 - β ^ 2 * α) * D)
    let C2 : ℝ := ((qh - q ^ 2) / (N + 1 : ℝ) + β ^ 2 * (qh - q ^ 2) * A2 +
      2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qh) * B2) / D
    |νT s - (∏ κ : R × R, ∫ x : ℝ,
          (Real.sqrt A2 * x) ^
            (s.filter fun j => (L j = true ∧ S j = true) ∧ (a j, b j) = κ).card
            ∂gaussianReal 0 1) *
        (∏ k : R, ∫ x : ℝ, (Real.sqrt B2 * x) ^
            (s.filter fun j => (L j = true ∧ S j = false) ∧ a j = k).card ∂gaussianReal 0 1) *
        ∫ x : ℝ, (Real.sqrt C2 * x) ^
          (s.filter fun j => L j = false ∧ S j = false).card ∂gaussianReal 0 1| ≤
      C / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := sk_T_mixed_gaussian_moment_uniform β₀ hβ₀ L S hnorm a b hord s
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro E bmean T νT qh α D A2 B2 C2
  have hαeq : 1 - 2 * q + qh = α := by dsimp only [α]; ring
  have hα := tanh_fourth_sub_two_mul_add_one_mem_Icc_of_fixedPoint hfix
  have hp := one_sub_mul_div_bounds (sq_nonneg β)
    (show β ^ 2 ≤ (1 / 4 : ℝ) by linarith) hα (by norm_num : (1 / 4 : ℝ) < 1)
  have hD1 : 1 - β ^ 2 * (1 - 2 * q + qh) ≠ 0 := by
    have hd : (0 : ℝ) < 1 - β ^ 2 * α := by linarith [hp.1]
    rw [hαeq]
    exact hd.ne'
  have hA : A2 = (α / (1 - β ^ 2 * α)) / (N + 1 : ℝ) := by
    simpa only [hαeq] using sk_T_pair_variance_eq β q qh (N + 1 : ℝ)
  have hB : B2 = ((q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) / D) /
      (N + 1 : ℝ) := by
    simpa only [hαeq] using sk_T_single_variance_eq β q qh (N + 1 : ℝ) hD1
  have hG : C2 = ((qh - q ^ 2) + β ^ 2 * (qh - q ^ 2) * (α / (1 - β ^ 2 * α)) +
      2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qh) *
        ((q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) / D)) / D /
          (N + 1 : ℝ) := by
    simpa only [hαeq] using sk_T_global_variance_eq β q qh (N + 1 : ℝ) hD1
  rw [hA, hB, hG]
  exact hC β h q hfix hb N

end SpinGlasses
