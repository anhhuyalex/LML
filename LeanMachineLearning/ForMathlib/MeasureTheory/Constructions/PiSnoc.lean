/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Independence.Basic

/-!
# Appending an independent coordinate to an i.i.d. vector

`MeasurableEquiv.finSuccProd` (`(Fin (n+1) → X) ≃ᵐ (Fin n → X) × X`, whose inverse is `Fin.snoc`)
carries the i.i.d. product measure on `Fin (n+1) → X` to the product of the i.i.d. product on
`Fin n → X` with one more factor.  Consequently, if `Y` is an i.i.d. vector of length `n`, and `W`
is an independent random variable with the same marginal law, then `(Y, W)` appended is an i.i.d.
vector of length `n+1` (`map_finSuccProd_symm_eq_pi`).  This is the "append a Gaussian" step of
Talagrand's Theorem 1.7.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

/-- `finSuccProd` is measure preserving for the i.i.d. product measures. -/
theorem measurePreserving_finSuccProd {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [SigmaFinite μ] (n : ℕ) :
    MeasurePreserving (MeasurableEquiv.finSuccProd X n) (Measure.pi fun _ : Fin (n + 1) => μ)
      ((Measure.pi fun _ : Fin n => μ).prod μ) :=
  (Measure.measurePreserving_swap (μ := μ) (ν := Measure.pi fun _ : Fin n => μ)).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) (Fin.last n))

/-- **Appending an independent coordinate to an i.i.d. vector.**  If `Y` has the law `μ^{⊗n}`, `W`
has the law `μ` and `Y, W` are independent, then `Fin.snoc Y W` has the law `μ^{⊗(n+1)}`. -/
theorem map_finSuccProd_symm_eq_pi {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure X} [IsProbabilityMeasure μ] {n : ℕ}
    {Y : Ω → Fin n → X} {W : Ω → X} (hY : Measurable Y) (hW : Measurable W)
    (hind : IndepFun Y W P) (hYl : P.map Y = Measure.pi fun _ : Fin n => μ)
    (hWl : P.map W = μ) :
    P.map (fun ω => (MeasurableEquiv.finSuccProd X n).symm (Y ω, W ω)) =
      Measure.pi fun _ : Fin (n + 1) => μ := by
  have hpair : P.map (fun ω => (Y ω, W ω)) = (Measure.pi fun _ : Fin n => μ).prod μ := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hW.aemeasurable).1 hind, hYl, hWl]
  have h1 : Measurable fun ω => (Y ω, W ω) := hY.prodMk hW
  have hcomp : (fun ω => (MeasurableEquiv.finSuccProd X n).symm (Y ω, W ω)) =
      (MeasurableEquiv.finSuccProd X n).symm ∘ fun ω => (Y ω, W ω) := rfl
  rw [hcomp, ← Measure.map_map (MeasurableEquiv.measurable _) h1, hpair]
  exact (measurePreserving_finSuccProd μ n).symm.map_eq
