/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.Real

/-!
# Lemmas about topology on `ℝ≥0∞`.
-/

@[expose] public section

open Filter

open scoped Topology

namespace ENNReal

/-- The tail bounds `C / (c u²)` of a fourth-moment Markov argument tend to `0` (in `ℝ≥0∞`) as the
sample-size parameter `u → ∞`. -/
lemma tendsto_ofReal_div_mul_sq {α : Type*} {ι : Filter α} {u : α → ℝ} (hu : Tendsto u ι atTop)
    (C : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun k => ENNReal.ofReal (C / (c * u k ^ 2))) ι (𝓝 0) := by
  have h1 : Tendsto (fun k => c * u k ^ 2) ι atTop :=
    Tendsto.const_mul_atTop hc ((tendsto_pow_atTop (by norm_num)).comp hu)
  simpa using ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := C)).div_atTop h1)

end ENNReal
