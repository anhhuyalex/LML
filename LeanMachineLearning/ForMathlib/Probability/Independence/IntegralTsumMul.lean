/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Probability.Independence.Integration

/-!
# Series of independent random variables with summable `L²` norms

Let `X p`, `Y q` be square-integrable random variables on a probability space, indexed by a
countable type, with `∑ₚ ‖X p‖_{L²} < ∞` and `∑_q ‖Y q‖_{L²} < ∞`.  Then the series converge
absolutely almost surely and in `L¹`, and, if `X p` is independent of `Y q` for `p ≠ q` and `X p`
is centered, the covariance of the sums is the sum of the diagonal covariances:
`𝔼[(∑ₚ X p)(∑_q Y q)] = ∑ₚ 𝔼[X p Y p]`.  The off-diagonal terms vanish by independence, and the
double series is exchanged with the integral by `MeasureTheory.integral_tsum`, using Hölder's
inequality `∫ |X p Y q| ≤ ‖X p‖₂ ‖Y q‖₂`.

## Main declarations

* `ProbabilityTheory.integrable_tsum_of_tsum_eLpNorm_ne_top`: the sum of a series with summable
  `Lᵖ` norms is integrable.
* `ProbabilityTheory.integral_tsum_mul_tsum_of_indepFun`: the covariance formula.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] [Countable κ]

omit [IsProbabilityMeasure μ] [Countable κ] in
/-- The `L²` norm of a square-integrable function is at most `C` when `∫ f² ≤ C²`. -/
theorem eLpNorm_two_le_ofReal_of_integral_sq_le {f : Ω → ℝ} {C : ℝ} (hf : MemLp f 2 μ)
    (hC : 0 ≤ C) (h : ∫ ω, f ω ^ 2 ∂μ ≤ C ^ 2) : eLpNorm f 2 μ ≤ ENNReal.ofReal C := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  calc (∫ ω, f ω ^ 2 ∂μ) ^ (2 : ℝ)⁻¹ ≤ (C ^ 2) ^ (2 : ℝ)⁻¹ :=
        Real.rpow_le_rpow (integral_nonneg fun _ => sq_nonneg _) h (by norm_num)
    _ = C := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hC]
        norm_num

/-- **A series with summable `Lᵖ` norms is integrable** (`p ≥ 1`, probability space). -/
theorem integrable_tsum_of_tsum_eLpNorm_ne_top {p : ℝ≥0∞} (hp : 1 ≤ p) {f : κ → Ω → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (h : ∑' n, eLpNorm (f n) p μ ≠ ∞) :
    Integrable (fun ω => ∑' n, f n ω) μ := by
  have h1 : ∑' n, eLpNorm (f n) 1 μ ≠ ∞ := ne_top_of_le_ne_top h
    (ENNReal.tsum_le_tsum fun n => eLpNorm_le_eLpNorm_of_exponent_le hp (hf n))
  refine ⟨(AEMeasurable.tsum fun n => (hf n).aemeasurable).aestronglyMeasurable, ?_⟩
  calc ∫⁻ ω, ‖∑' n, f n ω‖ₑ ∂μ ≤ ∫⁻ ω, ∑' n, ‖f n ω‖ₑ ∂μ :=
        lintegral_mono fun ω => enorm_tsum_le_tsum_enorm
    _ = ∑' n, eLpNorm (f n) 1 μ := by
        rw [lintegral_tsum fun n => (hf n).enorm]
        simp only [eLpNorm_one_eq_lintegral_enorm]
    _ < ∞ := h1.lt_top

omit [IsProbabilityMeasure μ] in
/-- **A series with summable `L¹` norms converges absolutely almost surely.** -/
theorem ae_summable_of_tsum_eLpNorm_ne_top {f : κ → Ω → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (h : ∑' n, eLpNorm (f n) 1 μ ≠ ∞) :
    ∀ᵐ ω ∂μ, Summable fun n => f n ω := by
  have hlint : ∫⁻ ω, ∑' n, ‖f n ω‖ₑ ∂μ ≠ ∞ := by
    rw [lintegral_tsum fun n => (hf n).enorm]
    simpa only [eLpNorm_one_eq_lintegral_enorm] using h
  have hae : ∀ᵐ ω ∂μ, ∑' n, ‖f n ω‖ₑ < ∞ :=
    ae_lt_top' (AEMeasurable.tsum fun n => (hf n).enorm) hlint
  filter_upwards [hae] with ω hω
  refine Summable.of_norm ?_
  have : ∑' n, (‖f n ω‖₊ : ℝ≥0∞) ≠ ∞ := by
    simpa [enorm_eq_nnnorm] using hω.ne
  exact (NNReal.summable_coe.2 (ENNReal.tsum_coe_ne_top_iff_summable.1 this))

omit [IsProbabilityMeasure μ] in
/-- **Covariance of two series of independent random variables.** If `∑ₚ ‖X p‖_{L²}` and
`∑_q ‖Y q‖_{L²}` are finite, `X p` is centered and independent of `Y q` for `p ≠ q`, then
`𝔼[(∑ₚ X p)(∑_q Y q)] = ∑ₚ 𝔼[X p Y p]`. -/
theorem integral_tsum_mul_tsum_of_indepFun {X Y : κ → Ω → ℝ} (hX : ∀ p, MemLp (X p) 2 μ)
    (hY : ∀ p, MemLp (Y p) 2 μ) (hXs : ∑' p, eLpNorm (X p) 2 μ ≠ ∞)
    (hYs : ∑' p, eLpNorm (Y p) 2 μ ≠ ∞) (hind : ∀ p q, p ≠ q → IndepFun (X p) (Y q) μ)
    (hX0 : ∀ p, ∫ ω, X p ω ∂μ = 0) :
    ∫ ω, (∑' p, X p ω) * (∑' q, Y q ω) ∂μ = ∑' p, ∫ ω, X p ω * Y p ω ∂μ := by
  have hXn := summable_norm_of_tsum_eLpNorm_ne_top one_le_two (fun p => (hX p).1) hXs
  have hYn := summable_norm_of_tsum_eLpNorm_ne_top one_le_two (fun p => (hY p).1) hYs
  have hmeas : ∀ z : κ × κ, AEStronglyMeasurable (fun ω => X z.1 ω * Y z.2 ω) μ := fun z =>
    (hX z.1).1.mul (hY z.2).1
  have hbound : ∑' z : κ × κ, ∫⁻ ω, ‖X z.1 ω * Y z.2 ω‖ₑ ∂μ ≠ ∞ := by
    have h1 : ∀ z : κ × κ, ∫⁻ ω, ‖X z.1 ω * Y z.2 ω‖ₑ ∂μ ≤
        eLpNorm (X z.1) 2 μ * eLpNorm (Y z.2) 2 μ := fun z => by
      rw [← eLpNorm_one_eq_lintegral_enorm]
      have h := eLpNorm_smul_le_mul_eLpNorm (μ := μ) (p := 2) (q := 2) (r := 1) (hY z.2).1
        (hX z.1).1 (hpqr := ⟨by simp [ENNReal.inv_two_add_inv_two]⟩)
      exact h
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum h1)
    rw [ENNReal.tsum_prod (f := fun a b => eLpNorm (X a) 2 μ * eLpNorm (Y b) 2 μ)]
    simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top hXs hYs
  have hoff : ∀ z : κ × κ, z.1 ≠ z.2 → ∫ ω, X z.1 ω * Y z.2 ω ∂μ = 0 := fun z hz => by
    rw [(hind _ _ hz).integral_fun_mul_eq_mul_integral (hX z.1).1 (hY z.2).1, hX0, zero_mul]
  calc ∫ ω, (∑' p, X p ω) * (∑' q, Y q ω) ∂μ
      = ∫ ω, ∑' z : κ × κ, X z.1 ω * Y z.2 ω ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hXn, hYn] with ω h1 h2
        exact tsum_mul_tsum_of_summable_norm h1 h2
    _ = ∑' z : κ × κ, ∫ ω, X z.1 ω * Y z.2 ω ∂μ := integral_tsum hmeas hbound
    _ = ∑' p, ∫ ω, X p ω * Y p ω ∂μ := by
        have hinj : Function.Injective fun p : κ => (p, p) := fun a b h => (Prod.ext_iff.1 h).1
        rw [← (hinj.tsum_eq (f := fun z : κ × κ => ∫ ω, X z.1 ω * Y z.2 ω ∂μ) ?_)]
        intro z hz
        by_contra hne
        exact hz (hoff z fun h => hne ⟨z.1, Prod.ext rfl h⟩)

end ProbabilityTheory
