/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenProductTaylor

/-!
# The odd spin-product estimate in Hanen's theorem

Taylor expansion at the decoupled endpoint combines vanishing of the low derivatives
with the quantitative endpoint bound for the higher terms (Talagrand Eqs. (1.351)--(1.358)).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix
namespace SpinGlasses

/-- The coupled two-site product of an odd number `2p+1` of disjoint replica spin
differences is bounded by `K/(N+2)^(p+1)`, uniformly in the high-temperature range. -/
theorem sk_hanen_odd_spin_product_bound (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (n p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (pairMap : Fin (2 * p + 1) → Fin n × Fin n)
      (_ : ∀ u v : Fin (2 * p + 1), u ≠ v →
        (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
        (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2),
      |skCavityPathMean (N + 1) n β q h 1 (fun σ =>
        (∏ w : Fin (2 * p + 1), ((σ (pairMap w).1 (Fin.last N).castSucc : ℝ) -
          (σ (pairMap w).2 (Fin.last N).castSucc : ℝ))) *
        ∏ w : Fin (2 * p + 1), ((σ (pairMap w).1 (Fin.last (N + 1)) : ℝ) -
          (σ (pairMap w).2 (Fin.last (N + 1)) : ℝ)))| ≤
        K / ((N : ℝ) + 2) ^ (p + 1 : ℕ) := by
  obtain ⟨K, hK, hKb⟩ := sk_hanen_spin_product_taylor β₀ hβ₀ n (2 * p + 1)
  obtain ⟨C, hC, hCb⟩ := sk_hanen_endpoint_derivative_bound β₀ hβ₀ n (2 * p + 1) (p + 1)
  refine ⟨K + C, add_pos hK hC, ?_⟩
  intro β h q hfix hβ N pairMap hdisj
  let f : (Fin n → Fin (N + 2) → ℤˣ) → ℝ := fun σ =>
    (∏ w : Fin (2 * p + 1), ((σ (pairMap w).1 (Fin.last N).castSucc : ℝ) -
      (σ (pairMap w).2 (Fin.last N).castSucc : ℝ))) *
    ∏ w : Fin (2 * p + 1), ((σ (pairMap w).1 (Fin.last (N + 1)) : ℝ) -
      (σ (pairMap w).2 (Fin.last (N + 1)) : ℝ))
  let φ : ℝ → ℝ := fun u => skCavityPathMean (N + 1) n β q h u f
  have hceil : (2 * p + 1 + 1) / 2 = p + 1 := by omega
  have he : (((2 * p + 1 : ℕ) : ℝ) + 1) / 2 = (p + 1 : ℕ) := by push_cast; ring
  have hr := hKb β h q hfix hβ N pairMap hdisj
  dsimp only at hr
  rw [hceil, he, Real.rpow_natCast] at hr
  have hd := hCb β h q hfix hβ N pairMap hdisj
  rw [hceil] at hd
  have hexp : ((((p + 1 : ℕ) + (p + 1) : ℕ) : ℝ) / 2) = (p + 1 : ℕ) := by
    push_cast
    ring
  rw [hexp, Real.rpow_natCast] at hd
  have hterm : |((p + 1).factorial : ℝ)⁻¹ *
      iteratedDerivWithin (p + 1) φ (Set.Icc 0 1) 0| ≤ C / ((N : ℝ) + 2) ^ (p + 1) := by
    rw [abs_mul, abs_inv, abs_of_pos (Nat.cast_pos.2 (Nat.factorial_pos _)),
      ← div_eq_inv_mul]
    exact (div_le_self (abs_nonneg _)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero (p + 1)))).trans hd
  change |φ 1| ≤ _
  calc
    _ ≤ |φ 1 - ((p + 1).factorial : ℝ)⁻¹ *
        iteratedDerivWithin (p + 1) φ (Set.Icc 0 1) 0| +
        |((p + 1).factorial : ℝ)⁻¹ * iteratedDerivWithin (p + 1) φ (Set.Icc 0 1) 0| := by
      simpa only [sub_add_cancel] using abs_add_le
        (φ 1 - ((p + 1).factorial : ℝ)⁻¹ * iteratedDerivWithin (p + 1) φ (Set.Icc 0 1) 0)
        (((p + 1).factorial : ℝ)⁻¹ * iteratedDerivWithin (p + 1) φ (Set.Icc 0 1) 0)
    _ ≤ K / ((N : ℝ) + 2) ^ (p + 1) + C / ((N : ℝ) + 2) ^ (p + 1) :=
      add_le_add hr hterm
    _ = _ := (add_div _ _ _).symm

end SpinGlasses
