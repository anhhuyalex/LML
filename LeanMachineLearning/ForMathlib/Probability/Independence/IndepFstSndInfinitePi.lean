/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Independence.IndepInfinitePi
public import LeanMachineLearning.ForMathlib.Probability.InfinitePiZip

/-!
# Independent families of pairs with independent components

If the random pairs `D v = (A v, B v)`, `v ∈ V`, are independent and each pair has a product law,
then the families `(A v)ᵥ` and `(B v)ᵥ` are independent.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {Ω V X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
  {P : Measure Ω}

/-- The families of the first and of the second components of independent random pairs with
product laws are independent, with the product laws as marginals. -/
theorem hasLaw_indepFun_fst_snd_of_iIndepFun [IsProbabilityMeasure P] (D : V → Ω → X × Y)
    (hDm : ∀ v, Measurable (D v)) (hD : iIndepFun D P) (μ : V → Measure X) (ν : V → Measure Y)
    [∀ v, IsProbabilityMeasure (μ v)] [∀ v, IsProbabilityMeasure (ν v)]
    (hlaw : ∀ v, HasLaw (D v) ((μ v).prod (ν v)) P) :
    HasLaw (fun ω v => (D v ω).1) (Measure.infinitePi μ) P ∧
    HasLaw (fun ω v => (D v ω).2) (Measure.infinitePi ν) P ∧
    IndepFun (fun ω v => (D v ω).1) (fun ω v => (D v ω).2) P := by
  have hjoint := HasLaw.infinitePi hDm hD hlaw
  have hA : Measurable fun ω v => (D v ω).1 :=
    measurable_pi_iff.2 fun v => measurable_fst.comp (hDm v)
  have hB : Measurable fun ω v => (D v ω).2 :=
    measurable_pi_iff.2 fun v => measurable_snd.comp (hDm v)
  have hunzip : Measurable fun p : V → X × Y => (fun v => (p v).1, fun v => (p v).2) :=
    (measurable_pi_iff.2 fun v => measurable_fst.comp (measurable_pi_apply v)).prodMk
      (measurable_pi_iff.2 fun v => measurable_snd.comp (measurable_pi_apply v))
  have hzip := Measure.infinitePi_prod_map_zip μ ν
  have hpair : HasLaw (fun ω => ((fun v => (D v ω).1), fun v => (D v ω).2))
      ((Measure.infinitePi μ).prod (Measure.infinitePi ν)) P := by
    refine ⟨(hA.prodMk hB).aemeasurable, ?_⟩
    have e : (fun ω => ((fun v => (D v ω).1), fun v => (D v ω).2)) =
        (fun p : V → X × Y => (fun v => (p v).1, fun v => (p v).2)) ∘ fun ω v => D v ω := rfl
    rw [e, ← AEMeasurable.map_map_of_aemeasurable hunzip.aemeasurable hjoint.aemeasurable,
      hjoint.map_eq, ← hzip, Measure.map_map hunzip]
    · have : ((fun p : V → X × Y => (fun v => (p v).1, fun v => (p v).2)) ∘
          fun p : (V → X) × (V → Y) => fun i => (p.1 i, p.2 i)) = id := rfl
      rw [this, Measure.map_id]
    · exact measurable_pi_iff.2 fun v => ((measurable_pi_apply v).comp measurable_fst).prodMk
        ((measurable_pi_apply v).comp measurable_snd)
  have hmA : P.map (fun ω v => (D v ω).1) = Measure.infinitePi μ := by
    have e : (fun ω v => (D v ω).1) = Prod.fst ∘ fun ω =>
        ((fun v => (D v ω).1), fun v => (D v ω).2) := rfl
    rw [e, ← AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
      hpair.aemeasurable, hpair.map_eq, Measure.map_fst_prod, measure_univ, one_smul]
  have hmB : P.map (fun ω v => (D v ω).2) = Measure.infinitePi ν := by
    have e : (fun ω v => (D v ω).2) = Prod.snd ∘ fun ω =>
        ((fun v => (D v ω).1), fun v => (D v ω).2) := rfl
    rw [e, ← AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
      hpair.aemeasurable, hpair.map_eq, Measure.map_snd_prod, measure_univ, one_smul]
  refine ⟨⟨hA.aemeasurable, hmA⟩, ⟨hB.aemeasurable, hmB⟩, ?_⟩
  rw [indepFun_iff_map_prod_eq_prod_map_map hA.aemeasurable hB.aemeasurable, hmA, hmB]
  exact hpair.map_eq

end ProbabilityTheory
