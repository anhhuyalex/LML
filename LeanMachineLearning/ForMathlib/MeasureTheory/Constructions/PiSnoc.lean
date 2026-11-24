/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.MeasurableSpace.Embedding
public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.Pi
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

/-- Splitting the last coordinate in every row preserves the product measure, with each row
allowed its own coordinate law. -/
theorem measurePreserving_pi_finSuccProd {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (μ : ι → Measure X) [∀ i, SigmaFinite (μ i)] (n : ℕ) :
    MeasurePreserving
      ((MeasurableEquiv.piCongrRight fun _ : ι => MeasurableEquiv.finSuccProd X n).trans
        (MeasurableEquiv.arrowProdEquivProdArrow (Fin n → X) X ι))
      (Measure.pi fun i : ι => Measure.pi fun _ : Fin (n + 1) => μ i)
      ((Measure.pi fun i : ι => Measure.pi fun _ : Fin n => μ i).prod (Measure.pi μ)) :=
  (measurePreserving_arrowProdEquivProdArrow (Fin n → X) X ι
    (fun i => Measure.pi fun _ : Fin n => μ i) μ).comp
    (measurePreserving_pi (f := fun _ : ι => MeasurableEquiv.finSuccProd X n) _ _
      fun i => measurePreserving_finSuccProd (μ i) n)

/-- **Splitting off the last row of an `(M + 1)`-row i.i.d. array and an auxiliary `(M + 1)`-vector
while keeping an independent extra coordinate:** under product laws, mapping `((g, z), y)` to
`(((Fin.init g, Fin.init z), y), Sum.elim (g (Fin.last M)) (fun _ : Unit => z (Fin.last M)))`
preserves the product measure, grouping the removed row and scalar into `(ι ⊕ Unit) → X`. -/
theorem measurePreserving_lastRow_sumPi_split {ι X Y : Type*} [Fintype ι] [MeasurableSpace X]
    [MeasurableSpace Y] (μ : Measure X) [SigmaFinite μ] (ν : Measure Y) [SigmaFinite ν] (M : ℕ) :
    MeasurePreserving
      (fun ω : ((Fin (M + 1) → ι → X) × (Fin (M + 1) → X)) × Y =>
        (((Fin.init ω.1.1, Fin.init ω.1.2), ω.2),
          (Sum.elim (ω.1.1 (Fin.last M)) (fun _ : Unit => ω.1.2 (Fin.last M)) : ι ⊕ Unit → X)))
      (((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : ι => μ).prod
        (Measure.pi fun _ : Fin (M + 1) => μ)).prod ν)
      ((((Measure.pi fun _ : Fin M => Measure.pi fun _ : ι => μ).prod
        (Measure.pi fun _ : Fin M => μ)).prod ν).prod (Measure.pi fun _ : ι ⊕ Unit => μ)) := by
  let G₀ := Measure.pi fun _ : Fin M => Measure.pi fun _ : ι => μ
  let gM := Measure.pi fun _ : ι => μ
  let Z₀ := Measure.pi fun _ : Fin M => μ
  have hg := measurePreserving_finSuccProd gM M
  have hz := measurePreserving_finSuccProd μ M
  have hunit := (measurePreserving_funUnique μ Unit).symm
  have hsum := (measurePreserving_sumPiEquivProdPi_symm (X := fun _ : ι ⊕ Unit => X)
    (fun _ => μ)).comp ((MeasurePreserving.id gM).prod hunit)
  have step1 : MeasurePreserving
      (Prod.map (Prod.map (MeasurableEquiv.finSuccProd (ι → X) M)
        (MeasurableEquiv.finSuccProd X M)) id)
      (((Measure.pi fun _ : Fin (M + 1) => gM).prod (Measure.pi fun _ : Fin (M + 1) => μ)).prod ν)
      (((G₀.prod gM).prod (Z₀.prod μ)).prod ν) :=
    (hg.prod hz).prod (MeasurePreserving.id ν)
  have step2 := (measurePreserving_prodProdProdComm G₀ gM Z₀ μ).prod (MeasurePreserving.id ν)
  have step3 := measurePreserving_prodAssoc (G₀.prod Z₀) (gM.prod μ) ν
  have step4 := (MeasurePreserving.id (G₀.prod Z₀)).prod
    (Measure.measurePreserving_swap (μ := gM.prod μ) (ν := ν))
  have step5 := (measurePreserving_prodAssoc (G₀.prod Z₀) ν (gM.prod μ)).symm
  have step6 := (MeasurePreserving.id ((G₀.prod Z₀).prod ν)).prod hsum
  have full := step6.comp (step5.comp (step4.comp (step3.comp (step2.comp step1))))
  convert full using 1
  ext ω : 1
  refine Prod.ext ?_ ?_
  · simp [MeasurableEquiv.prodAssoc, Fin.init_def]
  · ext idx
    rcases idx with i | _ <;>
      simp [MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
        Equiv.sumPiEquivProdPi_symm_apply]

/-- **Splitting off the last row of an `(M + 1)`-row i.i.d. array and two auxiliary
`(M + 1)`-vectors while keeping an independent extra coordinate:** under product laws, mapping
`(((g, a), z), y)` to `((((Fin.init g, Fin.init a), Fin.init z), y), ((g_M, a_M), z_M))`
preserves the product measure, grouping the removed row and the two scalars into
`((ι ⊕ Unit) ⊕ Unit) → X`. -/
theorem measurePreserving_lastRow_twoAux_sumPi_split {ι X Y : Type*} [Fintype ι] [MeasurableSpace X]
    [MeasurableSpace Y] (μ : Measure X) [SigmaFinite μ] (ν : Measure Y) [SigmaFinite ν] (M : ℕ) :
    MeasurePreserving
      (fun ω : (((Fin (M + 1) → ι → X) × (Fin (M + 1) → X)) × (Fin (M + 1) → X)) × Y =>
        ((((Fin.init ω.1.1.1, Fin.init ω.1.1.2), Fin.init ω.1.2), ω.2),
          (Sum.elim (Sum.elim (ω.1.1.1 (Fin.last M)) (fun _ : Unit => ω.1.1.2 (Fin.last M)))
            (fun _ : Unit => ω.1.2 (Fin.last M)) : (ι ⊕ Unit) ⊕ Unit → X)))
      ((((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : ι => μ).prod
        (Measure.pi fun _ : Fin (M + 1) => μ)).prod
        (Measure.pi fun _ : Fin (M + 1) => μ)).prod ν)
      (((((Measure.pi fun _ : Fin M => Measure.pi fun _ : ι => μ).prod
        (Measure.pi fun _ : Fin M => μ)).prod
        (Measure.pi fun _ : Fin M => μ)).prod ν).prod
        (Measure.pi fun _ : (ι ⊕ Unit) ⊕ Unit => μ)) := by
  let GA₀ := (Measure.pi fun _ : Fin M => Measure.pi fun _ : ι => μ).prod
    (Measure.pi fun _ : Fin M => μ)
  let Z₀ := Measure.pi fun _ : Fin M => μ
  let g₀ := Measure.pi fun _ : ι => μ
  have hg := measurePreserving_finSuccProd g₀ M
  have ha := measurePreserving_finSuccProd μ M
  have hz := measurePreserving_finSuccProd μ M
  have hunit := (measurePreserving_funUnique μ Unit).symm
  have hsum1 := (measurePreserving_sumPiEquivProdPi_symm (X := fun _ : ι ⊕ Unit => X)
    (fun _ => μ)).comp ((MeasurePreserving.id g₀).prod hunit)
  have hsum2 := (measurePreserving_sumPiEquivProdPi_symm
    (X := fun _ : (ι ⊕ Unit) ⊕ Unit => X) (fun _ => μ)).comp (hsum1.prod hunit)
  have s1 : MeasurePreserving
      (Prod.map (Prod.map (Prod.map (MeasurableEquiv.finSuccProd (ι → X) M)
        (MeasurableEquiv.finSuccProd X M)) (MeasurableEquiv.finSuccProd X M)) id)
      ((((Measure.pi fun _ : Fin (M + 1) => g₀).prod
        (Measure.pi fun _ : Fin (M + 1) => μ)).prod
        (Measure.pi fun _ : Fin (M + 1) => μ)).prod ν)
      ((((((Measure.pi fun _ : Fin M => g₀).prod g₀).prod (Z₀.prod μ)).prod (Z₀.prod μ)).prod ν)) :=
    ((hg.prod ha).prod hz).prod (MeasurePreserving.id ν)
  have s2 := ((measurePreserving_prodProdProdComm
      (Measure.pi fun _ : Fin M => g₀) g₀ Z₀ μ).prod
    (MeasurePreserving.id (Z₀.prod μ))).prod (MeasurePreserving.id ν)
  have s3 := (measurePreserving_prodProdProdComm GA₀ (g₀.prod μ) Z₀ μ).prod
    (MeasurePreserving.id ν)
  have s4 := measurePreserving_prodAssoc (GA₀.prod Z₀) ((g₀.prod μ).prod μ) ν
  have s5 := (MeasurePreserving.id (GA₀.prod Z₀)).prod
    (Measure.measurePreserving_swap (μ := (g₀.prod μ).prod μ) (ν := ν))
  have s6 := (measurePreserving_prodAssoc (GA₀.prod Z₀) ν ((g₀.prod μ).prod μ)).symm
  have s7 := (MeasurePreserving.id ((GA₀.prod Z₀).prod ν)).prod hsum2
  have full := s7.comp (s6.comp (s5.comp (s4.comp (s3.comp (s2.comp s1)))))
  convert full using 1
  ext ω : 1
  refine Prod.ext ?_ ?_
  · simp [MeasurableEquiv.prodAssoc, Fin.init_def]
  · ext idx
    rcases idx with (i | _) | _ <;>
      simp [MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
        Equiv.sumPiEquivProdPi_symm_apply]
