/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Topology.Constructions

/-!
# A map is dense in any set between its range and the closure of its range

If `f : α → X` takes values in `S` and `S ⊆ closure (range f)`, then the corestriction of `f` to
`S` has dense range.  The typical case is `S = closure (range f)`: the map is dense in the
closure of its range.

## Main declarations

* `denseRange_codRestrict_of_subset_closure`: the statement above.
-/

@[expose] public section

open Set

/-- The corestriction of `f` to a set `S ⊆ closure (range f)` containing its range has dense
range. -/
theorem denseRange_codRestrict_of_subset_closure {α X : Type*} [TopologicalSpace X] {f : α → X}
    {S : Set X} (hf : ∀ a, f a ∈ S) (hS : S ⊆ closure (range f)) :
    DenseRange (Set.codRestrict f S hf) := by
  refine Topology.IsInducing.subtypeVal.dense_iff.2 fun y => ?_
  rw [← range_comp]
  exact hS y.2
