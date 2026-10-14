/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.ExchangeableMixture
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Prefix restriction of infinite product measures

Restricting an i.i.d. sequence `ℕ → α` to its first `n` coordinates (indexed by `Fin n`) pushes
`Measure.infinitePi fun _ => ν` forward to the finite product `Measure.pi fun _ : Fin n => ν`.
This is used to pass between the infinite weight populations of the deep-network development and
the finite-width initialization measures.

* `MeasureTheory.Measure.measurePreserving_prefixMap` : the prefix restriction is measure
  preserving (in `ForMathlib`).
* `NTK.map_prefixMap_infinitePi` : the same for an infinite array `ℕ → ℕ → α`, restricting every
  inner sequence to its first `n` coordinates.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NTK

/-- Restricting every inner sequence of an i.i.d. array `ℕ → ℕ → α` to its first `n` coordinates
gives an i.i.d. sequence of `Measure.pi fun _ : Fin n => ν`. -/
theorem map_prefixMap_infinitePi {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => ν).map
        (fun (W : ℕ → ℕ → α) (j : ℕ) (k : Fin n) => W j k.val) =
      Measure.infinitePi fun _ : ℕ => Measure.pi fun _ : Fin n => ν := by
  refine (Measure.infinitePi_map_pi
    (μ := fun _ : ℕ => Measure.infinitePi fun _ : ℕ => ν)
    (f := fun _ (r : ℕ → α) (k : Fin n) => r k.val)
    (fun _ => (Measure.measurePreserving_prefixMap ν n).measurable)).trans ?_
  exact congrArg Measure.infinitePi
    (funext fun _ => (Measure.measurePreserving_prefixMap ν n).map_eq)

end NTK

end
