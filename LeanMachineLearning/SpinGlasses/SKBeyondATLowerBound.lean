/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import LeanMachineLearning.SpinGlasses.SKSecondMoment

/-!
# Beyond the AT line: the deduction of Proposition 1.9.2 from Lemma 1.9.4 (Talagrand, Section 1.9)

This file contains the real-variable part of Section 1.9 and nothing about the SK model.  The
SK-specific input, Lemma 1.9.4 (the second-moment identities (1.275)/(1.276) with the remainder
(1.277)), is a *hypothesis* here.

* `cubic_le_add_indicator`: the pointwise inequality (1.270),
  `|x|³ ≤ (δ/2) x² + 8 · 1{|x| ≥ δ/2}` for `|x| ≤ 2`.
* `indicator_lower_bound_of_cubic`: from `δ ν(X²) ≤ ν(|X|³)` to the lower bound (1.271),
  `ν(1{|X| ≥ δ/2}) ≥ (δ/16) ν(X²)`, for any positive linear functional `ν` (an average).
* `exists_cubic_lower_bounds`: the deduction of (1.269) from (1.275)/(1.276): if the rectangular
  second moment is nonnegative, its leading term `(4/M) a/(1 - β² a)` is negative (which is what
  `β² a > 1` means), and the remainders are at most `K (M^{-3/2} + ν|R-q|³)`, then
  `ν|R-q|³ ≥ δ ν(R-q)² ≥ δ²/M` for large `M`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 1.9.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **The pointwise inequality (1.270).**  For `|x| ≤ 2` and `δ > 0`:
`|x|³ ≤ (δ/2) x² + 8 · 1{|x| ≥ δ/2}`. -/
theorem cubic_le_add_indicator {δ x : ℝ} (hδ : 0 < δ) (hx : |x| ≤ 2) :
    |x| ^ 3 ≤ δ / 2 * x ^ 2 + 8 * (if δ / 2 ≤ |x| then 1 else 0) := by
  have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  rw [hx2]
  split_ifs with h
  · have : |x| ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (abs_nonneg x) hx 3
    nlinarith [sq_nonneg |x|]
  · push Not at h
    have : |x| ^ 3 = |x| * |x| ^ 2 := by ring
    nlinarith [sq_nonneg |x|, abs_nonneg x]

/-- **From (1.269) to (1.271).**  Let `ν` be an average (additive, homogeneous, monotone,
and `ν 1 = 1` on bounded observables) and `X` a function with `|X| ≤ 2`.  If
`δ ν(X²) ≤ ν(|X|³)`, then `ν(1{|X| ≥ δ/2}) ≥ (δ/16) ν(X²)`. -/
theorem indicator_lower_bound_of_cubic {Ω : Type*} (ν : (Ω → ℝ) → ℝ)
    (hadd : ∀ f g : Ω → ℝ, ν (fun ω => f ω + g ω) = ν f + ν g)
    (hsmul : ∀ (c : ℝ) (f : Ω → ℝ), ν (fun ω => c * f ω) = c * ν f)
    (hmono : ∀ f g : Ω → ℝ, (∀ ω, f ω ≤ g ω) → ν f ≤ ν g) (X : Ω → ℝ) (hX : ∀ ω, |X ω| ≤ 2) {δ : ℝ}
    (hδ : 0 < δ) (h : δ * ν (fun ω => X ω ^ 2) ≤ ν (fun ω => |X ω| ^ 3)) :
    δ / 16 * ν (fun ω => X ω ^ 2) ≤ ν (fun ω => if δ / 2 ≤ |X ω| then 1 else 0) := by
  have h1 : ν (fun ω => |X ω| ^ 3) ≤
      δ / 2 * ν (fun ω => X ω ^ 2) + 8 * ν (fun ω => if δ / 2 ≤ |X ω| then 1 else 0) := by
    calc ν (fun ω => |X ω| ^ 3)
        ≤ ν (fun ω => δ / 2 * X ω ^ 2 + 8 * (if δ / 2 ≤ |X ω| then (1 : ℝ) else 0)) :=
          hmono _ _ fun ω => cubic_le_add_indicator hδ (hX ω)
      _ = _ := by
          rw [hadd (fun ω => δ / 2 * X ω ^ 2) (fun ω => 8 * (if δ / 2 ≤ |X ω| then (1 : ℝ) else 0)),
            hsmul (δ / 2) (fun ω => X ω ^ 2),
            hsmul 8 (fun ω => if δ / 2 ≤ |X ω| then (1 : ℝ) else 0)]
  linarith

/-- **Eq. (1.271) for the SK model.**  On the `N + 1`-spin system with two replicas, if
`δ ν((R₁₂ - q)²) ≤ ν(|R₁₂ - q|³)` (the first inequality of (1.269)) and `|q| ≤ 1`, then
`ν(1{|R₁₂ - q| ≥ δ/2}) ≥ (δ/16) ν((R₁₂ - q)²)`. -/
theorem sk_indicator_lower_bound_of_cubic (N : ℕ) (β h q δ : ℝ) (hq : |q| ≤ 1) (hδ : 0 < δ)
    (ν : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (hcubic : δ * ν (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2) ≤
      ν (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| ^ 3)) :
    δ / 16 * ν (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2) ≤
      ν (fun σ => if δ / 2 ≤ |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q| then 1 else 0) := by
  refine indicator_lower_bound_of_cubic ν (sk_replica_avg_add N 2 β h ν hν)
    (sk_replica_avg_smul N 2 β h ν hν) (fun f g hfg => sk_replica_avg_mono N 2 β h ν hν f g hfg)
    (fun σ => (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
      fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) (fun σ => ?_) hδ hcubic
  have hM : (0 : ℝ) < N + 1 := by positivity
  have hdot : |(fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)| ≤
      N + 1 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simp only [abs_mul, abs_units_cast_eq_one, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    simp
  have hR : |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
      fun i : Fin (N + 1) => (σ 1 i : ℝ))| ≤ 1 := by
    rw [abs_mul, abs_inv, abs_of_pos hM, inv_mul_le_iff₀ hM]
    linarith
  exact (abs_sub _ _).trans (by linarith)

/-- **Proposition 1.9.2 from Lemma 1.9.4.**  Let `S₂ M = ν((R-q)²)`, `S₃ M = ν(|R-q|³)` and `T M`
be the rectangular second moment on the `M`-spin system.  Suppose

* `0 ≤ T M` and `T M = (4/M) a/(1 - β² a) + R₁ M` with `a > 0` and `β² a > 1`
  (the identity (1.275) beyond the AT line);
* `S₂ M = A M + R₂ M` with `0 ≤ A M ≤ K/M` (the identity (1.276), `A = A² + 2B² + C²`);
* `|R_i M| ≤ K (M^{-3/2} + S₃ M)` (the remainder bound (1.277));
* `0 ≤ S₃ M ≤ 2 S₂ M` (as `|R-q| ≤ 2`).

Then there are `δ > 0` and `M₀` with `δ S₂ M ≤ S₃ M` and `δ / M ≤ S₂ M` for all `M ≥ M₀`; in
particular `S₃ M ≥ δ S₂ M ≥ δ²/M`, which is (1.269). -/
theorem exists_cubic_lower_bounds {β a K : ℝ} (ha : 0 < a) (hβa : 1 < β ^ 2 * a) (hK : 0 < K)
    (S₂ S₃ T A R₁ R₂ : ℕ → ℝ)
    (hT0 : ∀ M, 1 ≤ M → 0 ≤ T M)
    (hT : ∀ M, 1 ≤ M → T M = 4 / (M : ℝ) * (a / (1 - β ^ 2 * a)) + R₁ M)
    (hS₂ : ∀ M, 1 ≤ M → S₂ M = A M + R₂ M)
    (hA : ∀ M, 1 ≤ M → 0 ≤ A M ∧ A M ≤ K / M)
    (hR₁ : ∀ M, 1 ≤ M → |R₁ M| ≤ K * ((Real.sqrt M)⁻¹ ^ 3 + S₃ M))
    (hR₂ : ∀ M, 1 ≤ M → |R₂ M| ≤ K * ((Real.sqrt M)⁻¹ ^ 3 + S₃ M))
    (hS₃ : ∀ M, 1 ≤ M → 0 ≤ S₃ M ∧ S₃ M ≤ 2 * S₂ M) :
    ∃ δ > 0, ∃ M₀ : ℕ, ∀ M ≥ M₀, δ * S₂ M ≤ S₃ M ∧ δ / M ≤ S₂ M := by
  set c : ℝ := 4 * a / (β ^ 2 * a - 1) with hc
  have hden : 0 < β ^ 2 * a - 1 := by linarith
  have hcpos : 0 < c := by positivity
  set K' : ℝ := 2 * K ^ 2 / c + 2 * K with hK'
  have hK'pos : 0 < K' := by positivity
  refine ⟨min (1 / K') (c / (4 * K)), by positivity, ⌈(2 * K / c) ^ 2⌉₊ + 1, fun M hM => ?_⟩
  have hM1 : 1 ≤ M := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
  -- the cubic remainder is small compared to `c / M`
  have hsq : 2 * K / c ≤ Real.sqrt M := by
    apply Real.le_sqrt_of_sq_le
    have : (⌈(2 * K / c) ^ 2⌉₊ : ℝ) ≤ M := by exact_mod_cast (by omega : ⌈(2 * K / c) ^ 2⌉₊ ≤ M)
    exact (Nat.le_ceil _).trans this
  have hsqpos : 0 < Real.sqrt M := Real.sqrt_pos.2 hMpos
  have hsmall : K * (Real.sqrt M)⁻¹ ^ 3 ≤ c / (2 * M) := by
    have h3 : (Real.sqrt M) ^ 2 = M := Real.sq_sqrt hMpos.le
    have hinv : (Real.sqrt M)⁻¹ ≤ c / (2 * K) := by
      rw [inv_le_comm₀ hsqpos (by positivity)]
      rw [inv_div]
      exact hsq
    calc K * (Real.sqrt M)⁻¹ ^ 3 = K * (Real.sqrt M)⁻¹ * ((Real.sqrt M)⁻¹) ^ 2 := by ring
      _ ≤ K * (c / (2 * K)) * (Real.sqrt M)⁻¹ ^ 2 := by gcongr
      _ = c / 2 * (M : ℝ)⁻¹ := by
          rw [inv_pow, h3]; field_simp
      _ = c / (2 * M) := by field_simp
  have hR1 := hR₁ M hM1
  have hTM := hT M hM1
  have hT0M := hT0 M hM1
  -- `R₁ M ≥ c / M`
  have hcM : c / M ≤ R₁ M := by
    have : 4 / (M : ℝ) * (a / (1 - β ^ 2 * a)) = -(c / M) := by
      rw [hc]
      have : 1 - β ^ 2 * a = -(β ^ 2 * a - 1) := by ring
      rw [this, div_neg]
      field_simp
    linarith
  obtain ⟨hS3a, hS3b⟩ := hS₃ M hM1
  have hS3M : c / (2 * M) ≤ K * S₃ M := by
    have h1 : c / M ≤ K * ((Real.sqrt M)⁻¹ ^ 3 + S₃ M) := hcM.trans ((le_abs_self _).trans hR1)
    have : c / M = 2 * (c / (2 * M)) := by field_simp
    nlinarith
  have hinvM : (1 : ℝ) / M ≤ 2 * K / c * S₃ M := by
    have h := hS3M
    rw [div_le_iff₀ (by positivity)] at h
    rw [div_le_iff₀ hMpos, show 2 * K / c * S₃ M * M = (2 * K * S₃ M * M) / c by ring,
      le_div_iff₀ hcpos]
    linarith
  obtain ⟨hA0, hA1⟩ := hA M hM1
  have hR2 := hR₂ M hM1
  have hS2 := hS₂ M hM1
  have hS2le : S₂ M ≤ K' * S₃ M := by
    have h2 : S₂ M ≤ K / M + K * ((Real.sqrt M)⁻¹ ^ 3 + S₃ M) :=
      hS2 ▸ add_le_add hA1 ((le_abs_self _).trans hR2)
    have h3 : K / M = K * (1 / M) := by ring
    have h4 : K * (1 / M) ≤ K * (2 * K / c * S₃ M) := by gcongr
    have h5 : K * (Real.sqrt M)⁻¹ ^ 3 ≤ K * S₃ M := by
      refine hsmall.trans ?_
      nlinarith
    have h6 : K * (2 * K / c * S₃ M) = 2 * K ^ 2 / c * S₃ M := by ring
    have h7 : K' * S₃ M = 2 * K ^ 2 / c * S₃ M + 2 * K * S₃ M := by rw [hK']; ring
    have h8 : K * ((Real.sqrt M)⁻¹ ^ 3 + S₃ M) = K * (Real.sqrt M)⁻¹ ^ 3 + K * S₃ M := by ring
    linarith
  have hmin1 : min (1 / K') (c / (4 * K)) ≤ 1 / K' := min_le_left _ _
  have hmin2 : min (1 / K') (c / (4 * K)) ≤ c / (4 * K) := min_le_right _ _
  have hS2pos : 0 ≤ S₂ M := by linarith
  constructor
  · calc min (1 / K') (c / (4 * K)) * S₂ M ≤ 1 / K' * S₂ M := by gcongr
      _ ≤ 1 / K' * (K' * S₃ M) := by gcongr
      _ = S₃ M := by field_simp
  · have : c / (4 * K * M) ≤ S₂ M := by
      have h6 : c / (2 * M) ≤ K * S₃ M := hS3M
      have : S₃ M ≤ 2 * S₂ M := hS3b
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at h6
      nlinarith [mul_le_mul_of_nonneg_left hS3b (le_of_lt (mul_pos hK hMpos))]
    calc min (1 / K') (c / (4 * K)) / M ≤ c / (4 * K) / M := by gcongr
      _ = c / (4 * K * M) := by field_simp
      _ ≤ S₂ M := this

end SpinGlasses
