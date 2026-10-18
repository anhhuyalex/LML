/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrals of functions of two independent variables

For independent random variables `X` and `Y`, the expectation of an integrable function
`H (X, Y)` is obtained by first integrating `y ↦ H (x, y)` against the law of `Y`, for fixed
`x = X ω`, and then integrating over `ω` (Fubini on the law of the pair, which is the product of
the marginal laws).
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω α β E : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → α} {Y : Ω → β}

/-- **Fubini for independent variables with strongly measurable integrand.** -/
theorem IndepFun.integral_comp_pair_eq_integral_integral_map' (hX : Measurable X)
    (hY : Measurable Y) (hind : IndepFun X Y P) {H : α → β → E}
    (hH : StronglyMeasurable (Function.uncurry H)) (hint : Integrable (fun ω => H (X ω) (Y ω)) P) :
    ∫ ω, H (X ω) (Y ω) ∂P = ∫ ω, ∫ y, H (X ω) y ∂(P.map Y) ∂P := by
  have hpair := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hind
  have hXY : Measurable fun ω => (X ω, Y ω) := hX.prodMk hY
  have hI : Integrable (Function.uncurry H) ((P.map X).prod (P.map Y)) := by
    rw [← hpair]
    exact (integrable_map_measure hH.aestronglyMeasurable hXY.aemeasurable).2 hint
  have h1 : ∫ ω, H (X ω) (Y ω) ∂P = ∫ p, Function.uncurry H p ∂(P.map X).prod (P.map Y) := by
    rw [← hpair, integral_map hXY.aemeasurable hH.aestronglyMeasurable]
    rfl
  have hm : AEStronglyMeasurable (fun x => ∫ y, Function.uncurry H (x, y) ∂(P.map Y))
      (P.map X) := (hH.integral_prod_right' (ν := P.map Y)).aestronglyMeasurable
  rw [h1, integral_prod _ hI, integral_map hX.aemeasurable hm]
  rfl

/-- **Fubini for independent variables.** -/
theorem IndepFun.integral_comp_pair_eq_integral_integral_map [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (hX : Measurable X) (hY : Measurable Y) (hind : IndepFun X Y P)
    {H : α → β → E} (hH : Measurable (Function.uncurry H))
    (hint : Integrable (fun ω => H (X ω) (Y ω)) P) :
    ∫ ω, H (X ω) (Y ω) ∂P = ∫ ω, ∫ y, H (X ω) y ∂(P.map Y) ∂P :=
  hind.integral_comp_pair_eq_integral_integral_map' hX hY hH.stronglyMeasurable hint

end ProbabilityTheory
