/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Deviations of a sum of two statistics

If `A` is within `ε/2` of `a₀` and `B` within `ε / (2 (|σ| + 1))` of `b₀`, then `A + σ B` is within
`ε` of `a₀ + σ b₀`. Hence the event `{ε ≤ |A + σ B - (a₀ + σ b₀)|}` is contained in the union of the
two individual deviation events. This is how bias and variance convergence in probability combine
into convergence of the risk.
-/

@[expose] public section

namespace MeasureTheory

open Filter Topology

/-- **A deviation of `A + σ B` is a deviation of `A` or of `B`.** -/
theorem measure_add_mul_deviation_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (A B : α → ℝ) (σ a₀ b₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    μ {x | ε ≤ |A x + σ * B x - (a₀ + σ * b₀)|} ≤
      μ {x | ε / 2 ≤ |A x - a₀|} + μ {x | ε / (2 * (|σ| + 1)) ≤ |B x - b₀|} := by
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro x hx
  simp only [Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
  by_contra hnot
  simp only [not_or, not_le] at hnot
  obtain ⟨h1, h2⟩ := hnot
  have hσ : 0 < |σ| + 1 := by positivity
  have h3 : |σ| * |B x - b₀| < ε / 2 := by
    have : |σ| * |B x - b₀| ≤ (|σ| + 1) * |B x - b₀| := by
      nlinarith [abs_nonneg (B x - b₀), abs_nonneg σ]
    have h4 : (|σ| + 1) * |B x - b₀| < ε / 2 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have := mul_lt_mul_of_pos_left h2 hσ
      have e : (|σ| + 1) * (ε / (2 * (|σ| + 1))) = ε / 2 := by field_simp
      linarith
    linarith
  have : |A x + σ * B x - (a₀ + σ * b₀)| ≤ |A x - a₀| + |σ| * |B x - b₀| := by
    calc _ = |(A x - a₀) + σ * (B x - b₀)| := by ring_nf
      _ ≤ |A x - a₀| + |σ * (B x - b₀)| := abs_add_le _ _
      _ = _ := by rw [abs_mul]
  linarith

/-- **Convergence in probability of `A + σ B`.** If `A_k → a₀` and `B_k → b₀` in probability, the
sum `R_k = A_k + σ B_k` converges to `a₀ + σ b₀` in probability. -/
theorem tendsto_measure_add_mul_deviation {α : ℕ → Type*} [∀ k, MeasurableSpace (α k)]
    (μ : ∀ k, Measure (α k)) (R A B : ∀ k, α k → ℝ) (σ a₀ b₀ : ℝ)
    (hR : ∀ k x, R k x = A k x + σ * B k x)
    (hA : ∀ ε : ℝ, 0 < ε → Tendsto (fun k => μ k {x | ε ≤ |A k x - a₀|}) atTop (𝓝 0))
    (hB : ∀ ε : ℝ, 0 < ε → Tendsto (fun k => μ k {x | ε ≤ |B k x - b₀|}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => μ k {x | ε ≤ |R k x - (a₀ + σ * b₀)|}) atTop (𝓝 0) := by
  have hsum := (hA (ε / 2) (half_pos hε)).add (hB (ε / (2 * (|σ| + 1))) (by positivity))
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun k => ?_)
  have h := measure_add_mul_deviation_le (μ k) (A k) (B k) σ a₀ b₀ hε
  simpa only [hR] using h

end MeasureTheory

end
