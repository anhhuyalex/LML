/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Chebyshev's association inequality

If two real functions `a, b` on a probability space are similarly ordered, i.e.
`(a x - a y) * (b x - b y) ≥ 0` for all `x, y` (for instance two monotone functions of a common
variable), then `𝔼 a * 𝔼 b ≤ 𝔼 (a * b)`.  The proof integrates the nonnegative function
`(a x - a y) * (b x - b y)` against `μ.prod μ`.  Two monotone functions of a common random
variable are the standard example.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

/-- **Chebyshev's association inequality** for a finite measure: if the integrable functions
`a, b` are similarly ordered for `μ.prod μ`-almost every pair, then
`∫ a * ∫ b ≤ μ(univ) * ∫ a * b`. -/
theorem integral_mul_integral_le_measureReal_univ_mul_integral_mul {Ω : Type*}
    {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] {a b : Ω → ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ) (hab : Integrable (fun x => a x * b x) μ)
    (h : ∀ᵐ z ∂μ.prod μ, 0 ≤ (a z.1 - a z.2) * (b z.1 - b z.2)) :
    (∫ x, a x ∂μ) * ∫ x, b x ∂μ ≤ μ.real Set.univ * ∫ x, a x * b x ∂μ := by
  have h1 : Integrable (fun z : Ω × Ω => a z.1 * b z.1) (μ.prod μ) := hab.comp_fst μ
  have h2 : Integrable (fun z : Ω × Ω => a z.2 * b z.2) (μ.prod μ) := hab.comp_snd μ
  have h3 : Integrable (fun z : Ω × Ω => a z.1 * b z.2) (μ.prod μ) := ha.mul_prod hb
  have h4 : Integrable (fun z : Ω × Ω => a z.2 * b z.1) (μ.prod μ) := by
    simpa only [mul_comm] using hb.mul_prod ha
  have hnn : 0 ≤ ∫ z : Ω × Ω, (a z.1 - a z.2) * (b z.1 - b z.2) ∂(μ.prod μ) :=
    integral_nonneg_of_ae h
  have hexp : ∫ z : Ω × Ω, (a z.1 - a z.2) * (b z.1 - b z.2) ∂(μ.prod μ) =
      ∫ z : Ω × Ω, a z.1 * b z.1 ∂(μ.prod μ) + ∫ z : Ω × Ω, a z.2 * b z.2 ∂(μ.prod μ) -
        ∫ z : Ω × Ω, a z.1 * b z.2 ∂(μ.prod μ) - ∫ z : Ω × Ω, a z.2 * b z.1 ∂(μ.prod μ) := by
    have e : ∀ z : Ω × Ω, (a z.1 - a z.2) * (b z.1 - b z.2) =
        a z.1 * b z.1 + a z.2 * b z.2 - a z.1 * b z.2 - a z.2 * b z.1 := fun z => by ring
    simp_rw [e]
    have i12 : Integrable (fun z : Ω × Ω => a z.1 * b z.1 + a z.2 * b z.2) (μ.prod μ) :=
      h1.add h2
    have i123 : Integrable (fun z : Ω × Ω => a z.1 * b z.1 + a z.2 * b z.2 - a z.1 * b z.2)
        (μ.prod μ) := i12.sub h3
    rw [integral_sub i123 h4, integral_sub i12 h3, integral_add h1 h2]
  rw [hexp, integral_fun_fst (fun x => a x * b x), integral_fun_snd (fun x => a x * b x),
    integral_prod_mul a b, show ∫ z : Ω × Ω, a z.2 * b z.1 ∂(μ.prod μ) =
      (∫ x, a x ∂μ) * ∫ x, b x ∂μ by
    rw [show (fun z : Ω × Ω => a z.2 * b z.1) = fun z => b z.1 * a z.2 from
      funext fun z => mul_comm _ _, integral_prod_mul b a, mul_comm]] at hnn
  simp only [smul_eq_mul] at hnn
  linarith

/-- **Chebyshev's association inequality** on a probability space: similarly ordered integrable
functions are nonnegatively correlated, `∫ a * ∫ b ≤ ∫ a * b`. -/
theorem integral_mul_integral_le_integral_mul {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a b : Ω → ℝ} (ha : Integrable a μ) (hb : Integrable b μ)
    (hab : Integrable (fun x => a x * b x) μ)
    (h : ∀ x y, 0 ≤ (a x - a y) * (b x - b y)) :
    (∫ x, a x ∂μ) * ∫ x, b x ∂μ ≤ ∫ x, a x * b x ∂μ := by
  simpa only [probReal_univ, one_mul] using
    integral_mul_integral_le_measureReal_univ_mul_integral_mul ha hb hab
      (ae_of_all _ fun z => h z.1 z.2)

/-- **Chebyshev's association inequality for monotone functions of a common variable** with
values in a linear order, for a finite measure: `f` and `g` need only be monotone on the range
of `X`. -/
theorem integral_comp_mul_integral_comp_le_of_monotoneOn {Ω β : Type*} [LinearOrder β]
    {m : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → β} {f g : β → ℝ}
    (hf : MonotoneOn f (Set.range X)) (hg : MonotoneOn g (Set.range X))
    (ha : Integrable (fun x => f (X x)) μ) (hb : Integrable (fun x => g (X x)) μ)
    (hab : Integrable (fun x => f (X x) * g (X x)) μ) :
    (∫ x, f (X x) ∂μ) * ∫ x, g (X x) ∂μ ≤ μ.real Set.univ * ∫ x, f (X x) * g (X x) ∂μ :=
  integral_mul_integral_le_measureReal_univ_mul_integral_mul ha hb hab
    (ae_of_all _ fun z => by
      have hx : X z.1 ∈ Set.range X := ⟨_, rfl⟩
      have hy : X z.2 ∈ Set.range X := ⟨_, rfl⟩
      rcases le_total (X z.1) (X z.2) with h | h
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hf hx hy h))
          (sub_nonpos.2 (hg hx hy h))
      · exact mul_nonneg (sub_nonneg.2 (hf hy hx h)) (sub_nonneg.2 (hg hy hx h)))

/-- **Chebyshev's association inequality for monotone functions of a common variable**:
`∫ f (X x) * ∫ g (X x) ≤ ∫ f (X x) * g (X x)` for monotone `f, g`. -/
theorem integral_comp_mul_integral_comp_le {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} {f g : ℝ → ℝ} (hf : Monotone f) (hg : Monotone g)
    (ha : Integrable (fun x => f (X x)) μ) (hb : Integrable (fun x => g (X x)) μ)
    (hab : Integrable (fun x => f (X x) * g (X x)) μ) :
    (∫ x, f (X x) ∂μ) * ∫ x, g (X x) ∂μ ≤ ∫ x, f (X x) * g (X x) ∂μ := by
  simpa only [probReal_univ, one_mul] using
    integral_comp_mul_integral_comp_le_of_monotoneOn (hf.monotoneOn _) (hg.monotoneOn _) ha hb hab

end MeasureTheory
