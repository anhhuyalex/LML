/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.NearlyGaussian

/-!
# Counting `(4,2)`-partitions of six labelled positions

`card_fourTwoPartition_fin_six` is not used by any other theorem in this project; it exists only
to record the count claimed informally in `NearlyGaussian.lean`'s six-point worked example. Its
`native_decide` proof is expensive to *compile* (deciding a proposition over
`Finpartition (Finset.univ : Finset (Fin 6))` this way takes minutes and 100GB+ of memory, even
though the runtime search itself is fast) — it lives in its own leaf module so that editing
`NearlyGaussian.lean` never forces recompiling it.
-/

@[expose] public section

noncomputable section

namespace Renormalization

/-- There are fifteen partitions of type `(4,2)` on six labelled positions.

Informal proof: such a partition is uniquely determined by its two-element block; its complement
is the four-element block.  There are `choose 6 2 = 15` choices.  Source: the fifteen `(4,2)`
terms in equation `eq:C6` of `docs/Renormalization.md`.
-/
theorem card_fourTwoPartition_fin_six :
    fourTwoPartitions.card = 15 := by
  -- `fourTwoPartitions` was built with a classical decidability instance; the value of
  -- `Finset.filter` does not depend on that instance (membership is `x ∈ univ ∧ p x`), so the
  -- definition equals the computably filtered universe, which `native_decide` can count.
  letI : DecidablePred IsFourTwoPartition := fun P => by
    unfold IsFourTwoPartition
    infer_instance
  rw [show fourTwoPartitions = Finset.univ.filter IsFourTwoPartition by
    dsimp [fourTwoPartitions]
    ext P
    simp]
  native_decide

end Renormalization

end

end
