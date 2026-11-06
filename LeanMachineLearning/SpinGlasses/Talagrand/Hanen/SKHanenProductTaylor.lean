/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenEndpointBound
public import LeanMachineLearning.ForMathlib.Analysis.Calculus.TaylorCoefficient

/-!
# The leading Taylor term of a two-site spin product

Both parities use the same expansion. The first potentially nonzero endpoint derivative
is retained exactly; higher terms are controlled by the reduced-system endpoint bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix
namespace SpinGlasses

/-- Isolate the first potentially nonzero Taylor term for any number of disjoint replica
spin differences. The error has one extra half-power of system size in the even case. -/
theorem sk_hanen_spin_product_taylor (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (n s : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (pairMap : Fin s → Fin n × Fin n)
      (_ : ∀ u v : Fin s, u ≠ v →
        (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
        (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2),
      let f : (Fin n → Fin (N + 2) → ℤˣ) → ℝ := fun σ =>
        (∏ w : Fin s, ((σ (pairMap w).1 (Fin.last N).castSucc : ℝ) -
          (σ (pairMap w).2 (Fin.last N).castSucc : ℝ))) *
        ∏ w : Fin s, ((σ (pairMap w).1 (Fin.last (N + 1)) : ℝ) -
          (σ (pairMap w).2 (Fin.last (N + 1)) : ℝ))
      let φ : ℝ → ℝ := fun u => skCavityPathMean (N + 1) n β q h u f
      |φ 1 - (((s + 1) / 2).factorial : ℝ)⁻¹ *
        iteratedDerivWithin ((s + 1) / 2) φ (Set.Icc 0 1) 0| ≤
        K / ((N : ℝ) + 2) ^ (((s : ℝ) + 1) / 2) := by
  choose C hC hCb using fun m : ℕ => sk_hanen_endpoint_derivative_bound β₀ hβ₀ n s m
  obtain ⟨D, hD, hDb⟩ := abs_iteratedDerivWithin_skCavityPathMean_le β₀ hβ₀ (s + 1) n
  let K := ∑ m ∈ Finset.range (s + 1), C m
  refine ⟨K + D * 4 ^ s + 1, ?_, ?_⟩
  · have hK : 0 ≤ K := Finset.sum_nonneg fun m _ => (hC m).le
    positivity
  intro β h q hfix hβ N pairMap hdisj f φ
  let t : ℝ := (N : ℝ) + 2
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : 1 ≤ t := by dsimp [t]; linarith [Nat.cast_nonneg (α := ℝ) N]
  have hq := fixedPoint_mem_Icc hfix
  have hf (σ : Fin n → Fin (N + 2) → ℤˣ) : |f σ| ≤ 4 ^ s := by
    have hp (i : Fin (N + 2)) :
        |∏ w : Fin s, ((σ (pairMap w).1 i : ℝ) - (σ (pairMap w).2 i : ℝ))| ≤ 2 ^ s := by
      simpa using abs_prod_units_sub_le_two_pow (fun w : Fin s => σ (pairMap w).1 i)
        (fun w : Fin s => σ (pairMap w).2 i)
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
      |iteratedDerivWithin (s + 1) φ (Set.Icc 0 1) u| ≤ D * 4 ^ s / t ^ (((s : ℝ) + 1) / 2) := by
    have hb := hDb β h q hfix hβ (N + 1) f u hu
    rw [← skCavityPathMean_one (N + 1) n β q h] at hb
    simp only [Nat.cast_succ, add_assoc, one_add_one_eq_two] at hb
    calc _ ≤ D / t ^ (((s : ℝ) + 1) / 2) * 4 ^ s :=
          hb.trans (mul_le_mul_of_nonneg_left hsqrt (by positivity))
      _ = _ := by ring
  have hfac (m : ℕ) (z : ℝ) : |(Nat.factorial m : ℝ)⁻¹ * z| ≤ |z| := by
    rw [abs_mul, abs_inv, abs_of_pos (Nat.cast_pos.2 (Nat.factorial_pos m)), ← div_eq_inv_mul]
    exact div_le_self (abs_nonneg _)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero m))
  have hlow (m : ℕ) (hm : m < (s + 1) / 2) : iteratedDerivWithin m φ (Set.Icc 0 1) 0 = 0 := by
    have hvan := iteratedDerivWithin_skCavityPathMean_zero_vanishing (N + 1) m n β q h hq
      (Finset.univ : Finset (Fin s)) pairMap (fun u _ v _ huv => hdisj u v huv)
      ∅ (by simp) (r := 0) (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
      (fun ρ => ∏ w : Fin s, ((ρ (pairMap w).1 (Fin.last N) : ℝ) -
        (ρ (pairMap w).2 (Fin.last N) : ℝ))) (fun _ => 1) (by intros; rfl)
    simpa only [Finset.prod_empty, mul_one] using hvan
  have hterm (m : ℕ) (_hm : m ∈ Finset.range (s + 1)) (hne : m ≠ (s + 1) / 2) :
      ‖(Nat.factorial m : ℝ)⁻¹ • iteratedDerivWithin m φ (Set.Icc 0 1) 0‖ ≤
        C m / t ^ (((s : ℝ) + 1) / 2) := by
    simp only [smul_eq_mul, Real.norm_eq_abs]
    by_cases hl : m < (s + 1) / 2
    · rw [hlow m hl, mul_zero, abs_zero]
      exact div_nonneg (hC m).le (Real.rpow_nonneg ht.le _)
    · have hb := hCb m β h q hfix hβ N pairMap hdisj
      refine (hfac m _).trans (hb.trans ?_)
      apply div_le_div_of_nonneg_left (hC m).le (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le ht1
      have hm0 : s + 1 ≤ (s + 1) / 2 + m := by omega
      have hcast : (s : ℝ) + 1 ≤ ((s + 1) / 2 : ℕ) + m := by exact_mod_cast hm0
      push_cast
      linarith
  have hc := contDiffOn_skCavityPathMean (N + 1) n β q h hq f (s + 1)
  have hb := norm_sub_taylor_coefficient_le (f := φ) (s := s) (a := (s + 1) / 2)
    (by omega) hc (fun m => C m / t ^ (((s : ℝ) + 1) / 2))
    (M := D * 4 ^ s / t ^ (((s : ℝ) + 1) / 2)) (by positivity) hterm
    (fun u hu => by simpa only [Real.norm_eq_abs] using hder u hu)
  simp only [smul_eq_mul, Real.norm_eq_abs] at hb
  refine hb.trans ?_
  have hsum : ∑ m ∈ (Finset.range (s + 1)).erase ((s + 1) / 2), C m ≤ K :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun m _ _ => (hC m).le)
  rw [← Finset.sum_div, ← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

end SpinGlasses
