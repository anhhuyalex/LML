/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenEndpointBound

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
  let s := 2 * p + 1
  choose C hC hCb using fun m : ℕ => sk_hanen_endpoint_derivative_bound β₀ hβ₀ n s m
  obtain ⟨D, hD, hDb⟩ := abs_iteratedDerivWithin_skCavityPathMean_le β₀ hβ₀ (s + 1) n
  let K := ∑ m ∈ Finset.range (s + 1), C m
  refine ⟨K + D * 4 ^ s + 1, ?_, ?_⟩
  · have hK : 0 ≤ K := Finset.sum_nonneg fun m _ => (hC m).le
    positivity
  intro β h q hfix hβ N pairMap hdisj
  let t : ℝ := (N : ℝ) + 2
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : 1 ≤ t := by dsimp [t]; linarith [Nat.cast_nonneg (α := ℝ) N]
  let f : (Fin n → Fin (N + 2) → ℤˣ) → ℝ := fun σ =>
    (∏ w : Fin s, ((σ (pairMap w).1 (Fin.last N).castSucc : ℝ) -
      (σ (pairMap w).2 (Fin.last N).castSucc : ℝ))) *
    ∏ w : Fin s, ((σ (pairMap w).1 (Fin.last (N + 1)) : ℝ) -
      (σ (pairMap w).2 (Fin.last (N + 1)) : ℝ))
  let φ : ℝ → ℝ := fun u => skCavityPathMean (N + 1) n β q h u f
  have hq := fixedPoint_mem_Icc hfix
  have hceil : (s + 1) / 2 = p + 1 := by dsimp [s]; omega
  have hf (σ : Fin n → Fin (N + 2) → ℤˣ) : |f σ| ≤ 4 ^ s := by
    have hp (i : Fin (N + 2)) :
        |∏ w : Fin s, ((σ (pairMap w).1 i : ℝ) - (σ (pairMap w).2 i : ℝ))| ≤ 2 ^ s := by
      rw [Finset.abs_prod]
      calc _ ≤ ∏ _w : Fin s, (2 : ℝ) := by
            gcongr with w _
            exact (abs_sub _ _).trans (by norm_num [abs_units_cast_eq_one])
        _ = _ := by simp
    dsimp only [f]
    rw [abs_mul]
    calc _ ≤ 2 ^ s * 2 ^ s := mul_le_mul (hp _) (hp _) (abs_nonneg _) (by positivity)
      _ = _ := by rw [← mul_pow]; norm_num
  have hM : skCavityPathMean (N + 1) n β q h 1 (fun σ => f σ ^ 2) ≤ (4 ^ s) ^ 2 := by
    have hpt (σ : Fin n → Fin (N + 2) → ℤˣ) : |f σ ^ 2| ≤ (4 ^ s) ^ 2 := by
      simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg _) (hf σ) 2
    have hdom := abs_skCavityPathMean_le (N + 1) n β q h 1 hpt
    exact (le_abs_self _).trans (hdom.trans_eq (by simp [skCavityPathMean]))
  have hsqrt : Real.sqrt (skCavityPathMean (N + 1) n β q h 1 (fun σ => f σ ^ 2)) ≤ 4 ^ s :=
    (Real.sqrt_le_sqrt hM).trans_eq (Real.sqrt_sq (by positivity))
  have hder (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      |iteratedDerivWithin (s + 1) φ (Set.Icc 0 1) u| ≤ D * 4 ^ s / t ^ (p + 1) := by
    have hb := hDb β h q hfix hβ (N + 1) f u hu
    have he : (((s + 1 : ℕ) : ℝ) / 2) = (p + 1 : ℕ) := by dsimp [s]; push_cast; ring
    rw [he, Real.rpow_natCast, ← skCavityPathMean_one (N + 1) n β q h] at hb
    simp only [Nat.cast_succ, add_assoc, one_add_one_eq_two] at hb
    calc _ ≤ D / t ^ (p + 1) * 4 ^ s :=
          hb.trans (mul_le_mul_of_nonneg_left hsqrt (by positivity))
      _ = _ := by ring
  have hfac (m : ℕ) (z : ℝ) : |(Nat.factorial m : ℝ)⁻¹ * z| ≤ |z| := by
    rw [abs_mul, abs_inv, abs_of_pos (Nat.cast_pos.2 (Nat.factorial_pos m)), ← div_eq_inv_mul]
    exact div_le_self (abs_nonneg _)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero m))
  have hlow (m : ℕ) (hm : m ≤ p) : iteratedDerivWithin m φ (Set.Icc 0 1) 0 = 0 := by
    have hvan := iteratedDerivWithin_skCavityPathMean_zero_vanishing (N + 1) m n β q h hq
      (Finset.univ : Finset (Fin s)) pairMap (fun u _ v _ huv => hdisj u v huv)
      ∅ (by simp) (r := 0) (by simp only [Finset.card_univ, Fintype.card_fin]; dsimp [s]; omega)
      (fun ρ => ∏ w : Fin s, ((ρ (pairMap w).1 (Fin.last N) : ℝ) -
        (ρ (pairMap w).2 (Fin.last N) : ℝ))) (fun _ => 1) (by intros; rfl)
    simpa only [Finset.prod_empty, mul_one] using hvan
  have hterm (m : ℕ) (hm : m ∈ Finset.range (s + 1)) :
      |(Nat.factorial m : ℝ)⁻¹ * iteratedDerivWithin m φ (Set.Icc 0 1) 0| ≤
        C m / t ^ (p + 1) := by
    by_cases hl : m ≤ p
    · rw [hlow m hl, mul_zero, abs_zero]
      exact div_nonneg (hC m).le (pow_nonneg ht.le _)
    · have hb := hCb m β h q hfix hβ N pairMap hdisj
      rw [hceil] at hb
      refine (hfac m _).trans (hb.trans ?_)
      rw [← Real.rpow_natCast]
      apply div_le_div_of_nonneg_left (hC m).le (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le ht1
      have hm0 : p + 1 ≤ m := by omega
      have hcast : (p : ℝ) + 1 ≤ m := by exact_mod_cast hm0
      push_cast
      linarith
  have hpoly : |taylorWithinEval φ s (Set.Icc 0 1) 0 1| ≤ K / t ^ (p + 1) := by
    rw [taylor_within_apply]
    simp only [sub_zero, one_pow, mul_one, smul_eq_mul]
    calc _ ≤ ∑ m ∈ Finset.range (s + 1),
        |(Nat.factorial m : ℝ)⁻¹ * iteratedDerivWithin m φ (Set.Icc 0 1) 0| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.range (s + 1), C m / t ^ (p + 1) :=
        Finset.sum_le_sum fun m hm => hterm m hm
      _ = _ := by rw [← Finset.sum_div]
  have hc : ∀ k : ℕ, ContDiffOn ℝ k φ (Set.Icc 0 1) :=
    contDiffOn_skCavityPathMean (N + 1) n β q h hq f
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin s φ (Set.Icc 0 1)) (Set.Ioo 0 1) :=
    ((hc (s + 1)).differentiableOn_iteratedDerivWithin (by exact_mod_cast Nat.lt_succ_self s)
      uniqueDiffOn_Icc_zero_one).mono Set.Ioo_subset_Icc_self
  have hu1 : Set.uIcc (0 : ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le zero_le_one
  have hu2 : Set.uIoo (0 : ℝ) 1 = Set.Ioo 0 1 := Set.uIoo_of_le zero_le_one
  obtain ⟨ξ, hξ, hrem⟩ := taylor_mean_remainder_lagrange (f := φ) (x := 1) (x₀ := 0)
    (n := s) zero_ne_one (by rw [hu1]; exact hc s) (by rw [hu1, hu2]; exact hdiff)
  rw [hu1] at hrem
  rw [hu2] at hξ
  have hr : |φ 1 - taylorWithinEval φ s (Set.Icc 0 1) 0 1| ≤ D * 4 ^ s / t ^ (p + 1) := by
    rw [hrem]
    simp only [sub_zero, one_pow, mul_one]
    rw [div_eq_inv_mul]
    exact (hfac (s + 1) _).trans (hder ξ ⟨hξ.1.le, hξ.2.le⟩)
  change |φ 1| ≤ _
  calc
    _ ≤ |φ 1 - taylorWithinEval φ s (Set.Icc 0 1) 0 1| +
        |taylorWithinEval φ s (Set.Icc 0 1) 0 1| := by
          simpa only [sub_add_cancel] using abs_add_le
            (φ 1 - taylorWithinEval φ s (Set.Icc 0 1) 0 1)
            (taylorWithinEval φ s (Set.Icc 0 1) 0 1)
    _ ≤ D * 4 ^ s / t ^ (p + 1) + K / t ^ (p + 1) := add_le_add hr hpoly
    _ ≤ _ := by rw [← add_div]; apply div_le_div_of_nonneg_right _ (by positivity); linarith

end SpinGlasses
