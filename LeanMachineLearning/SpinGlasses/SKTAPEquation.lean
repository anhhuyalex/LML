/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOldSpinCavity
public import LeanMachineLearning.SpinGlasses.SKLastSpinGaussian

/-!
# The TAP equations with the Onsager reaction term (Talagrand, Theorem 1.7.7, Eq. (1.193))

For the `(N+1)`-spin SK system at `0 ≤ β ≤ β₀`, `4 β₀² < 1`, with `q` a fixed point and `⟨·⟩` the
Gibbs mean of the `(N+1)`-spin system,
`𝔼 (⟨σ_{N+1}⟩ - tanh (β (N+1)^{-1/2} ∑_{i ≤ N} g_i ⟨σ_i⟩ + h - β² (1-q) ⟨σ_{N+1}⟩))^{2k}
  ≤ K/(N+1)^k` (`SpinGlasses.sk_tap_equation`), where `g_i = g_{i,N+1}` are the couplings of the
last spin.

Proof (source text lines 3152-3190).  Both magnetizations are written by the cavity formulas as
ratios of Gibbs averages of the `N`-spin system at `β_- = β √(N/(N+1))`
(`integral_last_spin_eq_sinh_div_cosh`, `integral_old_spin_eq_mul_cosh_div`).  The difference
between the full-system tanh and the tanh of Lemma 1.7.4 is controlled by the reaction bound
`sk_cavity_field_reaction_approx_book` (Eq. (1.210)); replacing `β_-², q_-` by `β², q` costs
`O(1/N)` (`abs_tap_coef_le`).  The three pieces are combined by the `2k`-th power triangle
inequality `integral_pow_le_of_abs_le_add_add`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Theorem 1.7.7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace SpinGlasses

/-- **The deterministic core of the TAP equation.**  With `c √N = b_-`, `X` the integrand of
(1.210), `|s| ≤ 1`, and `A = c ∑ yᵢ mᵢ + h` the (1.185) field,
`|s - tanh (c ∑ yᵢ fᵢ + h - β²(1-q) s)| ≤ |s - tanh A| + |b_-| |X| + |β²(1-q) - b_-²(1-q_-)|`. -/
theorem abs_sub_tanh_tap_le {N : ℕ} (c bm β q qm s h : ℝ) (hs : |s| ≤ 1) (y m f : Fin N → ℝ)
    (hc : c * Real.sqrt N = bm) (hN : 0 < N) :
    |s - Real.tanh (c * ∑ i, y i * f i + h - β ^ 2 * (1 - q) * s)| ≤
      |s - Real.tanh (c * ∑ i, y i * m i + h)| +
        (|bm| * |(Real.sqrt N)⁻¹ * ∑ i, y i * f i - bm * (1 - qm) * s -
            (Real.sqrt N)⁻¹ * ∑ i, y i * m i| +
          |β ^ 2 * (1 - q) - bm ^ 2 * (1 - qm)|) := by
  have hN0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  set X := (Real.sqrt N)⁻¹ * ∑ i, y i * f i - bm * (1 - qm) * s -
    (Real.sqrt N)⁻¹ * ∑ i, y i * m i with hX
  have hAB : c * ∑ i, y i * m i + h - (c * ∑ i, y i * f i + h - β ^ 2 * (1 - q) * s) =
      -(bm * X) + (β ^ 2 * (1 - q) - bm ^ 2 * (1 - qm)) * s := by
    rw [hX, ← hc]
    field_simp
    ring
  calc _ ≤ |s - Real.tanh (c * ∑ i, y i * m i + h)| +
        |Real.tanh (c * ∑ i, y i * m i + h) -
          Real.tanh (c * ∑ i, y i * f i + h - β ^ 2 * (1 - q) * s)| := by
        refine (abs_sub_le s (Real.tanh (c * ∑ i, y i * m i + h)) _).trans le_rfl
    _ ≤ _ := by
        refine add_le_add le_rfl ((Real.abs_tanh_sub_tanh_le _ _).trans ?_)
        rw [hAB]
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_neg, abs_mul]
        · rw [abs_mul]
          calc _ ≤ |β ^ 2 * (1 - q) - bm ^ 2 * (1 - qm)| * 1 :=
                mul_le_mul_of_nonneg_left hs (abs_nonneg _)
            _ = _ := mul_one _

/-- The integrand of (1.210) has integrable even powers: it is dominated by
`(2 N^{-1/2} ∑ |yᵢ| + 1)^{2k}` when `|fᵢ|, |mᵢ|, |s|, |b| ≤ 1`. -/
theorem integrable_pow_tap_field {Ω₀ : Type*} [MeasurableSpace Ω₀] (P : Measure Ω₀)
    [IsProbabilityMeasure P] {N : ℕ} (hN : 0 < N) (b : ℝ) (hb : |b| ≤ 1)
    (F m : Ω₀ × (Fin N → ℝ) → Fin N → ℝ) (s : Ω₀ × (Fin N → ℝ) → ℝ)
    (hF : ∀ i, Measurable fun w => F w i) (hm : ∀ i, Measurable fun w => m w i)
    (hs : Measurable s) (hF1 : ∀ w i, |F w i| ≤ 1) (hm1 : ∀ w i, |m w i| ≤ 1)
    (hs1 : ∀ w, |s w| ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    Integrable (fun w : Ω₀ × (Fin N → ℝ) =>
      ((Real.sqrt N)⁻¹ * ∑ i, w.2 i * F w i - b * s w - (Real.sqrt N)⁻¹ * ∑ i, w.2 i * m w i) ^
        (2 * k)) (P.prod (Measure.pi fun _ : Fin N => gaussianReal 0 1)) := by
  set Q : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => gaussianReal 0 1 with hQ
  have hdom : Integrable (fun w : Ω₀ × (Fin N → ℝ) =>
      (2 * (Real.sqrt N)⁻¹ * ∑ i, |w.2 i| + 1) ^ (2 * k)) (P.prod Q) :=
    (measurePreserving_snd (μ := P) (ν := Q)).integrable_comp_of_integrable
      (integrable_even_pow_const_mul_sum_abs_add (n := N) (2 * (Real.sqrt N)⁻¹) 1 k (by omega))
  have hN0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hsum : ∀ (G : Ω₀ × (Fin N → ℝ) → Fin N → ℝ), (∀ w i, |G w i| ≤ 1) → ∀ w,
      |(Real.sqrt N)⁻¹ * ∑ i, w.2 i * G w i| ≤ (Real.sqrt N)⁻¹ * ∑ i, |w.2 i| := fun G hG w => by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hN0)]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => ?_)) (inv_pos.mpr hN0).le
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hG w i)
  have hmeas : Measurable fun w : Ω₀ × (Fin N → ℝ) =>
      (Real.sqrt N)⁻¹ * ∑ i, w.2 i * F w i - b * s w - (Real.sqrt N)⁻¹ * ∑ i, w.2 i * m w i := by
    refine ((measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp measurable_snd).mul (hF i))).sub
      (measurable_const.mul hs)).sub (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp measurable_snd).mul (hm i)))
  refine hdom.mono' (hmeas.pow_const _).aestronglyMeasurable (ae_of_all _ fun w => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
  have h1 := hsum F hF1 w
  have h2 := hsum m hm1 w
  have h3 : |b * s w| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hb (hs1 w) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have h4 : (Real.sqrt N)⁻¹ * ∑ i, |w.2 i| = (Real.sqrt N)⁻¹ * ∑ i, |w.2 i| := rfl
  calc _ ≤ |(Real.sqrt N)⁻¹ * ∑ i, w.2 i * F w i - b * s w| +
        |(Real.sqrt N)⁻¹ * ∑ i, w.2 i * m w i| := abs_sub _ _
    _ ≤ (|(Real.sqrt N)⁻¹ * ∑ i, w.2 i * F w i| + |b * s w|) +
        |(Real.sqrt N)⁻¹ * ∑ i, w.2 i * m w i| := by gcongr; exact abs_sub _ _
    _ ≤ _ := by linarith

/-- **Replacing `β_-², q_-` by `β², q` costs `1/(N+1)`:** for `4 β² < 1`, `q, q_- ∈ [0, 1]` and
`|q - q_-| ≤ 1/(N+1)`, `|β²(1-q) - (β √(N/(N+1)))² (1-q_-)| ≤ 1/(N+1)`. -/
theorem abs_tap_coef_le {N : ℕ} {β q qm : ℝ} (hβ4 : 4 * β ^ 2 < 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hshift : |q - qm| ≤ 1 / ((N : ℝ) + 1)) :
    |β ^ 2 * (1 - q) - (β * Real.sqrt ((N : ℝ) / (N + 1))) ^ 2 * (1 - qm)| ≤
      1 / ((N : ℝ) + 1) := by
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hsq : (β * Real.sqrt ((N : ℝ) / (N + 1))) ^ 2 = β ^ 2 * ((N : ℝ) / (N + 1)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hdiff : β ^ 2 - β ^ 2 * ((N : ℝ) / (N + 1)) = β ^ 2 / ((N : ℝ) + 1) := by
    field_simp; ring
  have hsh := abs_le.mp hshift
  set ε : ℝ := 1 / ((N : ℝ) + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hb0 : 0 ≤ β ^ 2 / ((N : ℝ) + 1) := by positivity
  have hb1 : β ^ 2 / ((N : ℝ) + 1) ≤ ε / 4 := by
    have h14 : β ^ 2 ≤ 1 / 4 := by linarith
    calc β ^ 2 / ((N : ℝ) + 1) ≤ (1 / 4) / ((N : ℝ) + 1) :=
          div_le_div_of_nonneg_right h14 hN1.le
      _ = ε / 4 := by rw [hε]; field_simp
  have hbm : β ^ 2 * ((N : ℝ) / (N + 1)) ≤ 1 / 4 := by
    have : (N : ℝ) / (N + 1) ≤ 1 := (div_le_one hN1).mpr (by linarith)
    nlinarith [sq_nonneg β]
  have hbm0 : 0 ≤ β ^ 2 * ((N : ℝ) / (N + 1)) := by positivity
  rw [hsq, abs_le]
  have e : β ^ 2 * (1 - q) - β ^ 2 * ((N : ℝ) / (N + 1)) * (1 - qm) =
      (β ^ 2 / ((N : ℝ) + 1)) * (1 - q) + β ^ 2 * ((N : ℝ) / (N + 1)) * (qm - q) := by
    rw [← hdiff]; ring
  rw [e]
  obtain ⟨hq0, hq1⟩ := hq
  set a := β ^ 2 / ((N : ℝ) + 1) with ha
  set b := β ^ 2 * ((N : ℝ) / (N + 1)) with hb
  have h1 : 0 ≤ a * (1 - q) := mul_nonneg hb0 (sub_nonneg.mpr hq1)
  have h2 : a * (1 - q) ≤ a := by nlinarith [mul_nonneg hb0 hq0]
  have h3 : b * (qm - q) ≤ b * ε := mul_le_mul_of_nonneg_left (by linarith) hbm0
  have h4 : -(b * ε) ≤ b * (qm - q) := by
    have := mul_le_mul_of_nonneg_left (show -ε ≤ qm - q by linarith) hbm0
    linarith
  have h5 : b * ε ≤ ε / 4 := by nlinarith
  constructor <;> linarith

/-- A Gibbs mean of a spin has absolute value at most `1`. -/
theorem abs_integral_spin_count_tilted_le {N : ℕ} (f : (Fin N → ℤˣ) → ℝ) (i : Fin N) :
    |∫ a, ((a i : ℤ) : ℝ) ∂(Measure.count.tilted f)| ≤ 1 := by
  have := norm_integral_le_of_norm_le_const (μ := Measure.count.tilted f)
    (f := fun a : Fin N → ℤˣ => ((a i : ℤ) : ℝ)) (C := 1)
    (ae_of_all _ fun a => by simpa [Real.norm_eq_abs] using abs_units_cast_le_one (a i))
  simpa [Real.norm_eq_abs] using this

/-- **Talagrand, Theorem 1.7.7, Eq. (1.193): the TAP equations with the Onsager reaction term, in
`L^{2k}`.**  For `4 β₀² < 1`, `h` and `k ≥ 1` there is `K = K(β₀, h, k)` such that for all
`0 ≤ β ≤ β₀`, every fixed point `q` and `N ≥ 1`,
`𝔼 (⟨σ_{N+1}⟩ - tanh (β (N+1)^{-1/2} ∑_{i ≤ N} g_i ⟨σ_i⟩ + h - β² (1-q) ⟨σ_{N+1}⟩))^{2k}
  ≤ K / (N+1)^k`, where `⟨·⟩` is the Gibbs mean of the `(N+1)`-spin system and
`g_i = (skCavityDisorderEquiv N g).2 i` are the couplings of the last spin. -/
theorem sk_tap_equation (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (hβ₀' : 4 * β₀ ^ 2 < 1) (h : ℝ)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ K : ℝ, 0 < K ∧ ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → ∀ q : ℝ,
      (∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q) →
      ∀ N : ℕ, 0 < N →
      ∫ g : FinPairs (N + 1) → ℝ,
        (∫ σ, ((σ (Fin.last N) : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g)) -
          Real.tanh ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β *
            ∑ i : Fin N, (skCavityDisorderEquiv N g).2 i *
              (∫ σ : Fin (N + 1) → ℤˣ, ((σ i.castSucc : ℤ) : ℝ)
                ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g))) + h -
            β ^ 2 * (1 - q) * ∫ σ, ((σ (Fin.last N) : ℤ) : ℝ)
              ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g)))) ^ (2 * k)
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤ K / ((N : ℝ) + 1) ^ k := by
  obtain ⟨K1, hK10, hK1⟩ := sk_last_spin_tanh_approx_pow β₀ hβ₀ hβ₀' h hk
  obtain ⟨K2, hK20, hK2⟩ := sk_cavity_field_reaction_approx_book β₀ hβ₀ hβ₀' h hk
  have he : Even (2 * k) := ⟨k, by ring⟩
  refine ⟨2 ^ (2 * k - 1) * K1 + 2 ^ (2 * k - 1) * (2 ^ (2 * k - 1) *
    (β₀ ^ (2 * k) * (2 ^ k * K2)) + 2 ^ (2 * k - 1)), by positivity, ?_⟩
  intro β hβ0 hββ₀ q hq N hN
  have hβ4 : 4 * β ^ 2 < 1 := by nlinarith
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set bm : ℝ := β * Real.sqrt ((N : ℝ) / (N + 1)) with hbm
  have hs1 : Real.sqrt ((N : ℝ) / (N + 1)) ≤ 1 :=
    Real.sqrt_le_one.mpr ((div_le_one hN1).mpr (by linarith))
  have hbm0 : 0 ≤ bm := mul_nonneg hβ0 (Real.sqrt_nonneg _)
  have hbmβ : bm ≤ β := by
    calc bm ≤ β * 1 := mul_le_mul_of_nonneg_left hs1 hβ0
      _ = β := mul_one β
  have hbmβ₀ : |bm| ≤ β₀ := by rw [abs_of_nonneg hbm0]; exact hbmβ.trans hββ₀
  obtain ⟨qm, hqmI, hqm, hshift⟩ := exists_fixedPoint_cavity h q hβ0 hβ4 hq (N := N)
  have hqI := fixedPoint_mem_Icc hq
  have hKX := hK2 bm qm hqm hbmβ₀ N hN
  have hKU := hK1 β (by rw [abs_of_nonneg hβ0]; exact hββ₀) N hN
  have hcoef := abs_tap_coef_le (N := N) hβ4 hqI hshift
  set P : Measure (FinPairs N → ℝ) := Measure.pi fun _ : FinPairs N => gaussianReal 0 1 with hP
  set Q : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => gaussianReal 0 1 with hQ
  let Aw : (FinPairs N → ℝ) × (Fin N → ℝ) → (Fin N → ℤˣ) → ℝ := fun w a =>
    skGibbsEnergy N bm h w.1 a
  let Lw : (FinPairs N → ℝ) × (Fin N → ℝ) → (Fin N → ℤˣ) → ℝ := fun w a =>
    ((fun i => (Real.sqrt (N : ℝ))⁻¹ * (bm * ((a i : ℤ) : ℝ))) ⬝ᵥ w.2) + h
  have hA : ∀ a, Measurable fun w : (FinPairs N → ℝ) × (Fin N → ℝ) => Aw w a := fun a => by
    simp only [Aw, skGibbsEnergy]; fun_prop
  have hL : ∀ a, Measurable fun w : (FinPairs N → ℝ) × (Fin N → ℝ) => Lw w a := fun a => by
    simp only [Lw, dotProduct]; fun_prop
  have hD : ∀ w, 0 < ∫ a, Real.cosh (Lw w a) ∂(Measure.count.tilted (Aw w)) := fun w =>
    lt_of_lt_of_le one_pos (one_le_integral_cosh _ _)
  let sW : (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ := fun w =>
    (∫ a, Real.sinh (Lw w a) ∂(Measure.count.tilted (Aw w))) /
      ∫ a, Real.cosh (Lw w a) ∂(Measure.count.tilted (Aw w))
  let FW : (FinPairs N → ℝ) × (Fin N → ℝ) → Fin N → ℝ := fun w i =>
    (∫ a, ((a i : ℤ) : ℝ) * Real.cosh (Lw w a) ∂(Measure.count.tilted (Aw w))) /
      ∫ a, Real.cosh (Lw w a) ∂(Measure.count.tilted (Aw w))
  let mW : (FinPairs N → ℝ) × (Fin N → ℝ) → Fin N → ℝ := fun w i =>
    ∫ a, ((a i : ℤ) : ℝ) ∂(Measure.count.tilted (Aw w))
  have hcosh_m : Measurable fun w : (FinPairs N → ℝ) × (Fin N → ℝ) =>
      ∫ a, Real.cosh (Lw w a) ∂(Measure.count.tilted (Aw w)) :=
    measurable_integral_count_tilted_dep Aw hA _ fun a =>
      Real.continuous_cosh.measurable.comp (hL a)
  have hsW : Measurable sW :=
    (measurable_integral_count_tilted_dep Aw hA _ fun a =>
      Real.continuous_sinh.measurable.comp (hL a)).div hcosh_m
  have hFW : ∀ i, Measurable fun w => FW w i := fun i =>
    (measurable_integral_count_tilted_dep Aw hA _ fun a =>
      measurable_const.mul (Real.continuous_cosh.measurable.comp (hL a))).div hcosh_m
  have hmW : ∀ i, Measurable fun w => mW w i := fun i =>
    measurable_integral_count_tilted_dep Aw hA _ fun a => measurable_const
  have hs1' : ∀ w, |sW w| ≤ 1 := fun w => by
    simp only [sW]
    rw [abs_div, abs_of_pos (hD w), div_le_one (hD w)]
    exact abs_integral_sinh_le_integral_cosh _ _
  have hF1 : ∀ w i, |FW w i| ≤ 1 := fun w i =>
    abs_integral_mul_cosh_div_le _ _ _ fun a => abs_units_cast_le_one (a i)
  have hm1 : ∀ w i, |mW w i| ≤ 1 := fun w i => abs_integral_spin_count_tilted_le _ i
  have hβ₀1 : β₀ ≤ 1 := by nlinarith
  have hb1 : |bm * (1 - qm)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (by linarith [hqmI.2] : 0 ≤ 1 - qm)]
    calc |bm| * (1 - qm) ≤ 1 * 1 :=
          mul_le_mul (hbmβ₀.trans hβ₀1) (by linarith [hqmI.1]) (by linarith [hqmI.2])
            zero_le_one
      _ = 1 := one_mul 1
  let c : ℝ := (Real.sqrt ((N : ℝ) + 1))⁻¹ * β
  let Xf : (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ := fun w =>
    (Real.sqrt N)⁻¹ * ∑ i, w.2 i * FW w i - bm * (1 - qm) * sW w -
      (Real.sqrt N)⁻¹ * ∑ i, w.2 i * mW w i
  let Uf : (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ := fun w =>
    sW w - Real.tanh (c * ∑ i, w.2 i * mW w i + h)
  let Df : (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ := fun w =>
    sW w - Real.tanh (c * ∑ i, w.2 i * FW w i + h - β ^ 2 * (1 - q) * sW w)
  have hX_int : Integrable (fun w => Xf w ^ (2 * k)) (P.prod Q) :=
    integrable_pow_tap_field P hN (bm * (1 - qm)) hb1 FW mW sW hFW hmW hsW hF1 hm1 hs1' hk
  have hX_le : ∫ w, Xf w ^ (2 * k) ∂(P.prod Q) ≤ K2 / (N : ℝ) ^ k := by
    rw [integral_prod _ hX_int]; exact hKX
  have hUmeas : Measurable Uf := by
    refine hsW.sub (Real.continuous_tanh.measurable.comp ?_)
    exact (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp measurable_snd).mul (hmW i))).add_const _
  have hU_int : Integrable (fun w => |Uf w| ^ (2 * k)) (P.prod Q) := by
    refine Integrable.of_bound ((continuous_abs.measurable.comp hUmeas).pow_const
      _).aestronglyMeasurable (2 ^ (2 * k)) (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs, abs_pow, abs_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
    exact (abs_sub _ _).trans
      (by linarith [hs1' w, (Real.abs_tanh_lt_one (c * ∑ i, w.2 i * mW w i + h)).le])
  have hc : c * Real.sqrt N = bm := by
    have := sk_beta_minus_coefficient N β hN
    have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN0
    simp only [c]
    rw [← this]
    field_simp
    rfl
  have hpt : ∀ w, |Df w| ≤ |Uf w| + β₀ * |Xf w| + 1 / ((N : ℝ) + 1) := fun w => by
    have h1 := abs_sub_tanh_tap_le c bm β q qm (sW w) h (hs1' w) w.2 (mW w) (FW w) hc hN
    have h2 : |bm| * |Xf w| ≤ β₀ * |Xf w| := mul_le_mul_of_nonneg_right hbmβ₀ (abs_nonneg _)
    calc |Df w| ≤ _ := h1
      _ ≤ _ := by linarith
  have hb_int : Integrable (fun w => (β₀ * |Xf w|) ^ (2 * k)) (P.prod Q) := by
    have : (fun w => (β₀ * |Xf w|) ^ (2 * k)) = fun w => β₀ ^ (2 * k) * Xf w ^ (2 * k) := by
      ext w; rw [mul_pow, he.pow_abs]
    rw [this]; exact hX_int.const_mul _
  have hmain := integral_pow_le_of_abs_le_add_add hk (μ := P.prod Q) hpt hU_int hb_int
    (integrable_const (((1 : ℝ) / ((N : ℝ) + 1)) ^ (2 * k)))
  set Ptot : Measure (FinPairs (N + 1) → ℝ) := Measure.pi fun _ => gaussianReal 0 1 with hPtot
  have hmp := measurePreserving_skCavityDisorderEquiv N
  have hUle : ∫ w, |Uf w| ^ (2 * k) ∂(P.prod Q) ≤ K1 / ((N : ℝ) + 1) ^ k := by
    have h1 : ∫ w, |Uf w| ^ (2 * k) ∂(P.prod Q) =
        ∫ g, Uf (skCavityDisorderEquiv N g) ^ (2 * k) ∂Ptot := by
      rw [hmp.integral_comp' (fun w => Uf w ^ (2 * k))]
      simp only [he.pow_abs]
      rfl
    rw [h1]
    refine le_trans (le_of_eq (integral_congr_ae (ae_of_all _ fun g => ?_))) hKU
    change Uf (skCavityDisorderEquiv N g) ^ (2 * k) = _
    rw [integral_last_spin_eq_sinh_div_cosh hN β h g]
  have hDle : ∫ g, (∫ σ, ((σ (Fin.last N) : ℤ) : ℝ)
        ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g)) -
      Real.tanh ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β *
        ∑ i : Fin N, (skCavityDisorderEquiv N g).2 i *
          (∫ σ : Fin (N + 1) → ℤˣ, ((σ i.castSucc : ℤ) : ℝ)
            ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g))) + h -
        β ^ 2 * (1 - q) * ∫ σ, ((σ (Fin.last N) : ℤ) : ℝ)
          ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g)))) ^ (2 * k) ∂Ptot =
      ∫ w, Df w ^ (2 * k) ∂(P.prod Q) := by
    rw [← hmp.integral_comp' (fun w => Df w ^ (2 * k))]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    change _ = Df (skCavityDisorderEquiv N g) ^ (2 * k)
    simp only [integral_last_spin_eq_sinh_div_cosh hN β h g,
      integral_old_spin_eq_mul_cosh_div hN β h g]
    rfl
  rw [hDle]
  have hT : (0 : ℝ) < ((N : ℝ) + 1) ^ k := by positivity
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hXN : K2 / (N : ℝ) ^ k ≤ 2 ^ k * K2 / ((N : ℝ) + 1) ^ k := by
    rw [div_le_div_iff₀ (by positivity) hT]
    have h2 : ((N : ℝ) + 1) ^ k ≤ 2 ^ k * (N : ℝ) ^ k := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) k
    calc K2 * ((N : ℝ) + 1) ^ k ≤ K2 * (2 ^ k * (N : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left h2 hK20.le
      _ = 2 ^ k * K2 * (N : ℝ) ^ k := by ring
  have hconst : ((1 : ℝ) / ((N : ℝ) + 1)) ^ (2 * k) ≤ 1 / ((N : ℝ) + 1) ^ k := by
    rw [one_div, inv_pow, one_div]
    refine inv_anti₀ hT ?_
    rw [pow_mul']
    exact le_self_pow₀ (one_le_pow₀ (by linarith)) (by norm_num)
  have hXb : ∫ w, (β₀ * |Xf w|) ^ (2 * k) ∂(P.prod Q) ≤
      β₀ ^ (2 * k) * (2 ^ k * K2 / ((N : ℝ) + 1) ^ k) := by
    have : (fun w => (β₀ * |Xf w|) ^ (2 * k)) = fun w => β₀ ^ (2 * k) * Xf w ^ (2 * k) := by
      ext w; rw [mul_pow, he.pow_abs]
    rw [this, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hX_le.trans hXN) (by positivity)
  rw [integral_const, probReal_univ, one_smul] at hmain
  have hc1 : (0 : ℝ) ≤ 2 ^ (2 * k - 1) := by positivity
  refine hmain.trans ?_
  have : (2 ^ (2 * k - 1) * K1 + 2 ^ (2 * k - 1) * (2 ^ (2 * k - 1) *
      (β₀ ^ (2 * k) * (2 ^ k * K2)) + 2 ^ (2 * k - 1))) / ((N : ℝ) + 1) ^ k =
      2 ^ (2 * k - 1) * (K1 / ((N : ℝ) + 1) ^ k) + 2 ^ (2 * k - 1) * (2 ^ (2 * k - 1) *
        (β₀ ^ (2 * k) * (2 ^ k * K2 / ((N : ℝ) + 1) ^ k)) + 2 ^ (2 * k - 1) *
          (1 / ((N : ℝ) + 1) ^ k)) := by ring
  rw [this]
  gcongr

end SpinGlasses
