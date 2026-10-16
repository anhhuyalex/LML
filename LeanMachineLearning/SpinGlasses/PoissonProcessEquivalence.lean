/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonProcess
public import LeanMachineLearning.ForMathlib.Probability.HasCondDistrib

/-!
# Poisson blocks: conditional sampling and Campbell's formula

The conditional i.i.d. law is expressed on the block coordinates, without attempting to
canonically enumerate the points of an arbitrary counting measure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpinGlasses

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

/-- Conditionally on a Poisson block's count, its entire sample sequence is i.i.d.
This is stronger than the assertion concerning only the first `N` points. -/
theorem hasCondDistrib_poissonBlockSamples {P : Measure Ω} [IsProbabilityMeasure P]
    (ν : Measure S) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {B : Ω → ℕ × (ℕ → S)}
    (hB : HasLaw B (Po(r).prod (Measure.infinitePi fun _ : ℕ => ν)) P) :
    HasCondDistrib (fun ω => (B ω).2) (fun ω => (B ω).1)
      (ProbabilityTheory.Kernel.const ℕ (Measure.infinitePi fun _ : ℕ => ν)) P := by
  have hN : HasLaw (fun ω => (B ω).1) Po(r) P :=
    measurePreserving_fst.hasLaw.comp hB
  have hX : HasLaw (fun ω => (B ω).2) (Measure.infinitePi fun _ : ℕ => ν) P :=
    measurePreserving_snd.hasLaw.comp hB
  have hind : IndepFun (fun ω => (B ω).1) (fun ω => (B ω).2) P := by
    apply (indepFun_iff_map_prod_eq_prod_map_map hN.aemeasurable hX.aemeasurable).2
    simpa only [hN.map_eq, hX.map_eq] using hB.map_eq
  exact hind.hasCondDistrib_const hN.aemeasurable hX

end SpinGlasses
