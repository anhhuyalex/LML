/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Subsequential weak limits of probability measures on a compact set

On a separable metrizable space, a sequence of probability measures that all give mass `1` to a
fixed compact set `K` has a weakly convergent subsequence whose limit still gives mass `1` to `K`
(`ProbabilityMeasure.exists_tendsto_subseq_of_measure_eq_one`).  The proof is Prokhorov's theorem
(a sequence concentrated on a compact set is tight), and the metrizability of the space of
probability measures to pass from a cluster point to a subsequence.

A continuous map `T` that fixes every `μ n` also fixes the limit
(`ProbabilityMeasure.map_eq_of_tendsto`): symmetries pass to weak limits.
-/

@[expose] public section

open Filter Topology TopologicalSpace Set

namespace MeasureTheory.ProbabilityMeasure

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  [PseudoMetrizableSpace E] [SeparableSpace E] [T2Space E]

/-- **Prokhorov, sequential form.**  A sequence of probability measures on a separable metrizable
space, all concentrated on a compact set `K`, has a weakly convergent subsequence, and the limit is
concentrated on `K`. -/
theorem exists_tendsto_subseq_of_measure_eq_one {K : Set E} (hK : IsCompact K)
    (μ : ℕ → ProbabilityMeasure E) (hμ : ∀ n, (μ n : Measure E) K = 1) :
    ∃ (φ : ℕ → ℕ) (ν : ProbabilityMeasure E), StrictMono φ ∧ (ν : Measure E) K = 1 ∧
      Tendsto (μ ∘ φ) atTop (𝓝 ν) := by
  have hKc : IsClosed K := hK.isClosed
  have htight : IsTightMeasureSet {((ν : ProbabilityMeasure E) : Measure E) | ν ∈ range μ} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    refine fun ε _ => ⟨K, hK, ?_⟩
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    rw [prob_compl_eq_zero_iff hKc.measurableSet |>.2 (hμ n)]
    exact zero_le
  obtain ⟨ν, -, φ, hφ, hlim⟩ := (isCompact_closure_of_isTightMeasureSet htight).tendsto_subseq
    fun n => subset_closure ⟨n, rfl⟩
  refine ⟨φ, ν, hφ, ?_, hlim⟩
  have h := limsup_measure_closed_le_of_tendsto hlim hKc
  simp only [Function.comp_apply, hμ, limsup_const] at h
  exact le_antisymm prob_le_one h

omit [SeparableSpace E] [T2Space E] in
/-- **Symmetries pass to weak limits:** if a continuous map `T` fixes every `μ n` and `μ n → ν`
weakly, then `T` fixes `ν`. -/
theorem map_eq_of_tendsto {μ : ℕ → ProbabilityMeasure E} {ν : ProbabilityMeasure E} {T : E → E}
    (hT : Continuous T) (hinv : ∀ n, (μ n).map T = μ n) (hlim : Tendsto μ atTop (𝓝 ν)) :
    ν.map T = ν := by
  have h := tendsto_map_of_tendsto_of_continuous μ ν hlim hT
  simp only [hinv] at h
  exact tendsto_nhds_unique h hlim

end MeasureTheory.ProbabilityMeasure
