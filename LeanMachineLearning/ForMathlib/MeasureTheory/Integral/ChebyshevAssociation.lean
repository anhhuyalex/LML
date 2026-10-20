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
`(a x - a y) * (b x - b y)` against `μ.prod μ`.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

/-- **Chebyshev's association inequality** on a probability space: similarly ordered integrable
functions are nonnegatively correlated, `∫ a * ∫ b ≤ ∫ a * b`. -/
theorem integral_mul_integral_le_integral_mul {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {a b : Ω → ℝ} (ha : Integrable a μ) (hb : Integrable b μ)
    (hab : Integrable (fun x => a x * b x) μ)
    (h : ∀ x y, 0 ≤ (a x - a y) * (b x - b y)) :
    (∫ x, a x ∂μ) * ∫ x, b x ∂μ ≤ ∫ x, a x * b x ∂μ := by
  have h1 : Integrable (fun z : Ω × Ω => a z.1 * b z.1) (μ.prod μ) := hab.comp_fst μ
  have h2 : Integrable (fun z : Ω × Ω => a z.2 * b z.2) (μ.prod μ) := hab.comp_snd μ
  have h3 : Integrable (fun z : Ω × Ω => a z.1 * b z.2) (μ.prod μ) := ha.mul_prod hb
  have h4 : Integrable (fun z : Ω × Ω => a z.2 * b z.1) (μ.prod μ) := by
    simpa only [mul_comm] using hb.mul_prod ha
  have hnn : 0 ≤ ∫ z : Ω × Ω, (a z.1 - a z.2) * (b z.1 - b z.2) ∂(μ.prod μ) :=
    integral_nonneg fun z => h z.1 z.2
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
  simp only [probReal_univ, one_smul] at hnn
  linarith

end MeasureTheory
