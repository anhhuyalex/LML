/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The expectation of a maximum from high moments

If `Δ_1, ..., Δ_M` are random variables with `𝔼 Δ_i^{2k} ≤ K / M^k` then
`𝔼 max_i |Δ_i| ≤ (1 + K) M^{-(k-1)/(2k)}` (`integral_sup'_abs_le_rpow`).  The proof avoids
Lyapunov's inequality: for `x ≥ 0` and `a > 0`, `x ≤ a + x^{2k} / a^{2k-1}`, and
`max^{2k} ≤ ∑ Δ_i^{2k}`.  This is the argument of Talagrand's Corollary 1.7.8.
-/

@[expose] public section

open MeasureTheory

/-- Any `ε > 0` dominates `1 / (2 k)` for some `k ≥ 1`. -/
theorem exists_nat_one_le_one_div_two_mul_le {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ 1 / (2 * (k : ℝ)) ≤ ε := by
  refine ⟨⌈1 / (2 * ε)⌉₊ + 1, by omega, ?_⟩
  have h1 : 1 / (2 * ε) ≤ ((⌈1 / (2 * ε)⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast; linarith [Nat.le_ceil (1 / (2 * ε))]
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ (by positivity)] at h1
  nlinarith

/-- For `x ≥ 0`, `a > 0`: `x ≤ a + x^{2k} / a^{2k-1}` (Markov-type pointwise bound). -/
theorem le_add_pow_div {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) {k : ℕ} (hk : 1 ≤ k) :
    x ≤ a + x ^ (2 * k) / a ^ (2 * k - 1) := by
  have hpos : 0 < a ^ (2 * k - 1) := pow_pos ha _
  rcases le_total x a with h | h
  · have : 0 ≤ x ^ (2 * k) / a ^ (2 * k - 1) := by positivity
    linarith
  · have h1 : a ^ (2 * k - 1) ≤ x ^ (2 * k - 1) := pow_le_pow_left₀ ha.le h _
    have h2 : x ^ (2 * k) = x * x ^ (2 * k - 1) := by
      rw [← pow_succ']; congr 1; omega
    have : x ≤ x ^ (2 * k) / a ^ (2 * k - 1) := by
      rw [le_div_iff₀ hpos, h2]
      exact mul_le_mul_of_nonneg_left h1 hx
    linarith [ha]

/-- **Expectation of a maximum from `2k`-th moments, with a free parameter.**  For finitely many
random variables with integrable `2k`-th powers and every `a > 0`,
`𝔼 max_i |Δ_i| ≤ a + (∑_i 𝔼 Δ_i^{2k}) / a^{2k-1}`. -/
theorem integral_sup'_abs_le {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [Fintype ι] (hne : (Finset.univ : Finset ι).Nonempty)
    (Δ : ι → Ω → ℝ) {k : ℕ} (hk : 1 ≤ k)
    (hint : ∀ i, Integrable (fun ω => Δ i ω ^ (2 * k)) P) {a : ℝ} (ha : 0 < a) :
    ∫ ω, Finset.univ.sup' hne (fun i => |Δ i ω|) ∂P ≤
      a + (∑ i, ∫ ω, Δ i ω ^ (2 * k) ∂P) / a ^ (2 * k - 1) := by
  have he : Even (2 * k) := ⟨k, by ring⟩
  have hg : Integrable (fun ω => a + (∑ i, Δ i ω ^ (2 * k)) / a ^ (2 * k - 1)) P :=
    (integrable_const a).add ((integrable_finsetSum _ fun i _ => hint i).div_const _)
  have hnn : ∀ ω, 0 ≤ Finset.univ.sup' hne (fun i => |Δ i ω|) := fun ω => by
    obtain ⟨i, -⟩ := hne
    exact (abs_nonneg _).trans (Finset.le_sup' (fun i => |Δ i ω|) (Finset.mem_univ i))
  calc ∫ ω, Finset.univ.sup' hne (fun i => |Δ i ω|) ∂P
      ≤ ∫ ω, (a + (∑ i, Δ i ω ^ (2 * k)) / a ^ (2 * k - 1)) ∂P :=
        integral_mono_of_nonneg (ae_of_all _ hnn) hg (ae_of_all _ fun ω => by
          refine Finset.sup'_le _ _ fun i _ => ?_
          refine (le_add_pow_div (abs_nonneg _) ha hk).trans ?_
          rw [he.pow_abs]
          beta_reduce
          gcongr
          exact Finset.single_le_sum (f := fun j => Δ j ω ^ (2 * k))
            (fun j _ => he.pow_nonneg _) (Finset.mem_univ i))
    _ = _ := by
        rw [integral_add (integrable_const a)
          ((integrable_finsetSum _ fun i _ => hint i).div_const _), integral_const, integral_div,
          integral_finsetSum _ fun i _ => hint i]
        simp

/-- **Expectation of a maximum of `M` variables with `2k`-th moments `≤ K / M^k`:**
`𝔼 max_i |Δ_i| ≤ (1 + K) M^{-(k-1)/(2k)}` (Talagrand, proof of Corollary 1.7.8, with the
parameter `a = M^{-(k-1)/(2k)}` chosen so that `a^{2k} = M^{1-k}`). -/
theorem integral_sup'_abs_le_rpow {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [Fintype ι] [Nonempty ι] (Δ : ι → Ω → ℝ) {k : ℕ} (hk : 1 ≤ k)
    (hint : ∀ i, Integrable (fun ω => Δ i ω ^ (2 * k)) P) {K : ℝ}
    (hmom : ∀ i, ∫ ω, Δ i ω ^ (2 * k) ∂P ≤ K / (Fintype.card ι : ℝ) ^ k) :
    ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => |Δ i ω|) ∂P ≤
      (1 + K) * (Fintype.card ι : ℝ) ^ (-((k : ℝ) - 1) / (2 * k)) := by
  set M : ℝ := (Fintype.card ι : ℝ) with hM
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hM]; exact_mod_cast Fintype.card_pos
  have hM0 : 0 < M := by linarith
  set a : ℝ := M ^ (-((k : ℝ) - 1) / (2 * k)) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hM0 _
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have ha2k : a ^ (2 * k) = 1 / M ^ (k - 1) := by
    rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hM0.le]
    have : -((k : ℝ) - 1) / (2 * k) * ((2 * k : ℕ) : ℝ) = -((k - 1 : ℕ) : ℝ) := by
      have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        rw [Nat.cast_sub hk]; simp
      push_cast
      rw [hk1]
      field_simp
    rw [this, Real.rpow_neg hM0.le, Real.rpow_natCast, one_div]
  have h1 := integral_sup'_abs_le (P := P) Finset.univ_nonempty Δ hk hint ha0
  refine h1.trans ?_
  have hsum : (∑ i, ∫ ω, Δ i ω ^ (2 * k) ∂P) ≤ K / M ^ (k - 1) := by
    calc _ ≤ ∑ _i : ι, K / M ^ k := Finset.sum_le_sum fun i _ => hmom i
      _ = M * (K / M ^ k) := by simp [hM]
      _ = K / M ^ (k - 1) := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ]
        field_simp
  have hpos : 0 < a ^ (2 * k - 1) := pow_pos ha0 _
  have hdiv : (K / M ^ (k - 1)) / a ^ (2 * k - 1) = K * a := by
    have h2k : a ^ (2 * k) = a * a ^ (2 * k - 1) := by
      rw [← pow_succ']; congr 1; omega
    have : K / M ^ (k - 1) = K * a ^ (2 * k) := by rw [ha2k]; ring
    rw [this, h2k]
    field_simp
  calc a + (∑ i, ∫ ω, Δ i ω ^ (2 * k) ∂P) / a ^ (2 * k - 1)
      ≤ a + (K / M ^ (k - 1)) / a ^ (2 * k - 1) := by gcongr
    _ = (1 + K) * a := by rw [hdiv]; ring

/-- `M^{-(k-1)/(2k)} ≤ M^{-(1/2-ε)}` for `M ≥ 1` and `1/(2k) ≤ ε`. -/
theorem rpow_neg_div_le_of_inv_le {M : ℝ} (hM : 1 ≤ M) {k : ℕ} (hk : 1 ≤ k) {ε : ℝ}
    (hε : 1 / (2 * (k : ℝ)) ≤ ε) :
    M ^ (-((k : ℝ) - 1) / (2 * k)) ≤ M ^ (-(1 / 2 - ε)) := by
  refine Real.rpow_le_rpow_of_exponent_le hM ?_
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have : -((k : ℝ) - 1) / (2 * k) = -(1 / 2) + 1 / (2 * k) := by field_simp; ring
  rw [this]; linarith
