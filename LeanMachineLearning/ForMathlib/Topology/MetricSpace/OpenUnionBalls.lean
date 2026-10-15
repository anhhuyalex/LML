/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Data.Rat.Cast.CharZero

/-!
# Open sets as unions of rational balls around a dense set

In a pseudometric space with a dense subset `D`, every open set `U` is the union of the open balls
`ball d r` with `d ∈ D`, `r` a positive rational, and `ball d r ⊆ U`.  When `D` is countable this
is a countable union, which is how a countable family of balls generates the Borel σ-algebra of a
separable metric space.

## Main declarations

* `Metric.isOpen_eq_iUnion_ball_dense_rat`: the identity above.
-/

@[expose] public section

open Set Metric

/-- **Open sets are unions of rational balls centred in a dense set.** -/
theorem Metric.isOpen_eq_iUnion_ball_dense_rat {β : Type*} [PseudoMetricSpace β] {D : Set β}
    (hD : Dense D) {U : Set β} (hU : IsOpen U) :
    U = ⋃ (d : D) (r : ℚ) (_ : 0 < (r : ℝ) ∧ ball (d : β) r ⊆ U), ball (d : β) r := by
  ext x
  simp only [mem_iUnion]
  refine ⟨fun hx => ?_, fun ⟨d, r, ⟨_, hr⟩, hxd⟩ => hr hxd⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU _ hx
  obtain ⟨r, hr0, hrε⟩ := exists_rat_btwn (half_pos hε)
  obtain ⟨d, hdD, hxd⟩ := hD.exists_dist_lt x (by exact_mod_cast hr0 : (0 : ℝ) < r)
  refine ⟨⟨d, hdD⟩, r, ⟨by exact_mod_cast hr0, fun y hy => hball ?_⟩, hxd⟩
  rw [mem_ball] at hy ⊢
  have h1 := dist_triangle y d x
  have h2 := dist_comm d x
  linarith
