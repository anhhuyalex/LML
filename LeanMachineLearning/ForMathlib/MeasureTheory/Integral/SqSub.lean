/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.AddPowEstimates
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.Tanh
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Expanding the integral of a squared difference

For real functions `f`, `g` with `f²`, `g²` and `f g` integrable,
`∫ (f - g)² = ∫ f² - 2 ∫ f g + ∫ g²`.
-/

@[expose] public section

namespace MeasureTheory

/-- A measurable function whose centered `m`-th power is integrable has integrable `m`-th power
about every other center. -/
theorem integrable_sub_pow_of_integrable_abs_pow {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → ℝ} (hX : Measurable X) {c : ℝ} {m : ℕ}
    (h : Integrable (fun ω => |X ω - c| ^ m) P) (a : ℝ) :
    Integrable (fun ω => (X ω - a) ^ m) P := by
  refine ((h.add (integrable_const (|c - a| ^ m))).const_mul (2 ^ (m - 1))).mono'
    ((hX.sub_const a).pow_const m).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  have := abs_add_pow_le (X ω - c) (c - a) m
  rwa [sub_add_sub_cancel] at this


/-- The integral of a squared difference expands as `∫ f² - 2 ∫ f g + ∫ g²`. -/
theorem integral_sq_sub {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f g : Ω → ℝ}
    (hf : Integrable (fun ω => f ω ^ 2) μ) (hg : Integrable (fun ω => g ω ^ 2) μ)
    (hfg : Integrable (fun ω => f ω * g ω) μ) :
    ∫ ω, (f ω - g ω) ^ 2 ∂μ = ∫ ω, f ω ^ 2 ∂μ - 2 * ∫ ω, f ω * g ω ∂μ + ∫ ω, g ω ^ 2 ∂μ := by
  have h1 : Integrable (fun ω => f ω ^ 2 - 2 * (f ω * g ω)) μ := hf.sub (hfg.const_mul 2)
  rw [show (fun ω => (f ω - g ω) ^ 2) = fun ω => (f ω ^ 2 - 2 * (f ω * g ω)) + g ω ^ 2 from
    funext fun ω => by ring, integral_add h1 hg, integral_sub hf (hfg.const_mul 2),
    integral_const_mul]

/-- Every power of a bounded measurable function is integrable for a finite measure. -/
theorem integrable_pow_of_abs_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) (n : ℕ) {C : ℝ}
    (hC : ∀ ω, |f ω| ≤ C) : Integrable (fun ω => f ω ^ n) μ :=
  Integrable.of_bound (hf.pow_const n).aestronglyMeasurable (C ^ n)
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hC ω) n)

/-- The square of a bounded measurable function is integrable for a finite measure. -/
theorem integrable_sq_of_abs_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ ω, |f ω| ≤ C) :
    Integrable (fun ω => f ω ^ 2) μ :=
  integrable_pow_of_abs_le hf 2 hC

/-- Powers of `tanh ∘ Y` are integrable for any finite measure and
almost-everywhere measurable `Y`. -/
theorem integrable_tanh_pow {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (Y : Ω → ℝ) (hY : AEMeasurable Y μ) (k : ℕ) :
    Integrable (fun ω => Real.tanh (Y ω) ^ k) μ := by
  refine Integrable.of_bound ?_ 1 (Filter.Eventually.of_forall fun ω => ?_)
  · exact ((continuous_pow k).comp Real.continuous_tanh).aestronglyMeasurable.comp_aemeasurable hY
  · rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (Real.abs_tanh_lt_one (Y ω)).le

/-- `tanh² ∘ Y` is integrable for any finite measure and almost-everywhere measurable `Y`. -/
theorem integrable_tanh_sq {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (Y : Ω → ℝ) (hY : AEMeasurable Y μ) :
    Integrable (fun ω => Real.tanh (Y ω) ^ 2) μ :=
  integrable_tanh_pow Y hY 2

/-- `𝔼 tanh⁴ Y ≤ 𝔼 tanh² Y` for any finite measure. -/
theorem integral_tanh_pow_four_le_sq {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (Y : Ω → ℝ) (hY : AEMeasurable Y μ) :
    ∫ ω, Real.tanh (Y ω) ^ 4 ∂μ ≤ ∫ ω, Real.tanh (Y ω) ^ 2 ∂μ := by
  refine integral_mono (integrable_tanh_pow Y hY 4) (integrable_tanh_pow Y hY 2) fun ω => ?_
  have h0 : 0 ≤ Real.tanh (Y ω) ^ 2 := sq_nonneg _
  nlinarith [(Real.tanh_sq_lt_one (Y ω)).le]

/-- **Quartic expansion:** if `X²` and `X⁴` are integrable for a finite measure `μ`, then
`𝔼 X⁴ - 2 𝔼 X² + μ(univ) = 𝔼 (1 - X²)²`. -/
theorem integral_pow_four_sub_two_mul_add_eq {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ} (h2 : Integrable (fun ω => X ω ^ 2) μ)
    (h4 : Integrable (fun ω => X ω ^ 4) μ) :
    (∫ ω, X ω ^ 4 ∂μ) - 2 * (∫ ω, X ω ^ 2 ∂μ) + μ.real Set.univ =
      ∫ ω, (1 - X ω ^ 2) ^ 2 ∂μ := by
  have e : ∀ ω, (1 - X ω ^ 2) ^ 2 = (X ω ^ 4 - 2 * X ω ^ 2) + 1 := fun ω => by ring
  simp_rw [e]
  have hi : Integrable (fun ω => X ω ^ 4 - 2 * X ω ^ 2) μ := h4.sub (h2.const_mul 2)
  rw [integral_add hi (integrable_const _), integral_sub h4 (h2.const_mul 2),
    integral_const_mul]
  simp

/-- **Reciprocal-cosh identity:** `𝔼 tanh⁴ Y - 2 𝔼 tanh² Y + μ(univ) = 𝔼 (cosh Y)⁻⁴` for any
finite measure. -/
theorem integral_tanh_pow_four_sub_two_mul_add_eq {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] (Y : Ω → ℝ) (hY : AEMeasurable Y μ) :
    (∫ ω, Real.tanh (Y ω) ^ 4 ∂μ) - 2 * (∫ ω, Real.tanh (Y ω) ^ 2 ∂μ) + μ.real Set.univ =
      ∫ ω, ((Real.cosh (Y ω))⁻¹) ^ 4 ∂μ := by
  rw [integral_pow_four_sub_two_mul_add_eq (integrable_tanh_pow Y hY 2)
    (integrable_tanh_pow Y hY 4)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Real.one_sub_tanh_sq_eq_inv_cosh_sq]
  ring

/-- **Three-term triangle inequality in `L²`:**
`∫ (a + b + c)² ≤ 3 ∫ a² + 3 ∫ b² + 3 ∫ c²` for square-integrable `a, b, c`. -/
theorem integral_sq_add_add_le {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {a b c : Ω → ℝ} (ha : Integrable (fun ω => a ω ^ 2) μ) (hb : Integrable (fun ω => b ω ^ 2) μ)
    (hc : Integrable (fun ω => c ω ^ 2) μ) :
    ∫ ω, (a ω + b ω + c ω) ^ 2 ∂μ ≤
      3 * ∫ ω, a ω ^ 2 ∂μ + 3 * ∫ ω, b ω ^ 2 ∂μ + 3 * ∫ ω, c ω ^ 2 ∂μ := by
  have hab : Integrable (fun ω => 3 * a ω ^ 2 + 3 * b ω ^ 2) μ :=
    (ha.const_mul 3).add (hb.const_mul 3)
  have hint : Integrable (fun ω => 3 * a ω ^ 2 + 3 * b ω ^ 2 + 3 * c ω ^ 2) μ :=
    hab.add (hc.const_mul 3)
  calc ∫ ω, (a ω + b ω + c ω) ^ 2 ∂μ ≤ ∫ ω, (3 * a ω ^ 2 + 3 * b ω ^ 2 + 3 * c ω ^ 2) ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _) hint
          (Filter.Eventually.of_forall fun ω => by
            nlinarith [sq_nonneg (a ω - b ω), sq_nonneg (a ω - c ω), sq_nonneg (b ω - c ω)])
    _ = _ := by
        rw [integral_add hab (hc.const_mul 3), integral_add (ha.const_mul 3) (hb.const_mul 3),
          integral_const_mul, integral_const_mul, integral_const_mul]

/-- **Three-term triangle inequality in `L^{2k}`:** if `|Δ| ≤ a + b + c` pointwise and
`a^{2k}, b^{2k}, c^{2k}` are integrable then
`∫ Δ^{2k} ≤ 2^{2k-1} ∫ a^{2k} + 2^{2k-1} (2^{2k-1} ∫ b^{2k} + 2^{2k-1} ∫ c^{2k})`. -/
theorem integral_pow_le_of_abs_le_add_add {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {k : ℕ} (hk : 1 ≤ k) {Δ a b c : Ω → ℝ} (hΔ : ∀ ω, |Δ ω| ≤ a ω + b ω + c ω)
    (ha : Integrable (fun ω => a ω ^ (2 * k)) μ) (hb : Integrable (fun ω => b ω ^ (2 * k)) μ)
    (hc : Integrable (fun ω => c ω ^ (2 * k)) μ) :
    ∫ ω, Δ ω ^ (2 * k) ∂μ ≤ 2 ^ (2 * k - 1) * ∫ ω, a ω ^ (2 * k) ∂μ +
      2 ^ (2 * k - 1) * (2 ^ (2 * k - 1) * ∫ ω, b ω ^ (2 * k) ∂μ +
        2 ^ (2 * k - 1) * ∫ ω, c ω ^ (2 * k) ∂μ) := by
  have hbc : Integrable (fun ω => 2 ^ (2 * k - 1) * b ω ^ (2 * k) +
      2 ^ (2 * k - 1) * c ω ^ (2 * k)) μ := (hb.const_mul _).add (hc.const_mul _)
  have hint : Integrable (fun ω => 2 ^ (2 * k - 1) * a ω ^ (2 * k) +
      2 ^ (2 * k - 1) * (2 ^ (2 * k - 1) * b ω ^ (2 * k) +
        2 ^ (2 * k - 1) * c ω ^ (2 * k))) μ :=
    (ha.const_mul _).add (hbc.const_mul _)
  have he : Even (2 * k) := ⟨k, by ring⟩
  calc ∫ ω, Δ ω ^ (2 * k) ∂μ ≤ _ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => he.pow_nonneg _) hint
          (Filter.Eventually.of_forall fun ω => by
            beta_reduce
            rw [← he.pow_abs]
            refine (pow_le_pow_left₀ (abs_nonneg _) (hΔ ω) _).trans ?_
            rw [add_assoc]
            refine (add_pow_two_mul_le hk _ _).trans ?_
            have := add_pow_two_mul_le hk (b ω) (c ω)
            nlinarith [pow_pos (two_pos : (0:ℝ) < 2) (2 * k - 1), this,
              he.pow_nonneg (a ω)])
    _ = _ := by
        rw [integral_add (ha.const_mul _) (hbc.const_mul _), integral_const_mul,
          integral_const_mul, integral_add (hb.const_mul _) (hc.const_mul _),
          integral_const_mul, integral_const_mul]

end MeasureTheory
