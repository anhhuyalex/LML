/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Interchange of limits for a uniformly approximated family

If `F i x` is within `ε i → 0` of `A x` for all `x`, and each `F i` converges (along `l`) to `L i`,
then in a complete space `L i` converges (along `p`) to some `ℓ`, and `A x` converges (along `l`) to
the same `ℓ`.  Unlike `TendstoUniformly.tendsto_of_eventually_tendsto`, the limit `ℓ` of `L` is not
assumed: it is produced, since `dist (L i) (L j) ≤ ε i + ε j` makes `L` Cauchy.

In `SpinGlasses/ThermodynamicLimit.lean`, `i` is the inverse temperature `β → ∞`, `x` the system
size `N → ∞`, `F β N = F_N(β) / β` the normalized free energy, `A N` the normalized ground-state
energy and `ε β = log 2 / β`.
-/

@[expose] public section

open Filter Topology

/-- **Interchange of limits for a uniformly approximated family** in a complete space. -/
theorem exists_tendsto_of_dist_le_of_tendsto {ι α E : Type*} [PseudoMetricSpace E] [CompleteSpace E]
    {p : Filter ι} [p.NeBot] {l : Filter α} [l.NeBot] {F : ι → α → E} {L : ι → E} {A : α → E}
    {ε : ι → ℝ} (hε : Tendsto ε p (𝓝 0)) (hF : ∀ᶠ i in p, ∀ x, dist (F i x) (A x) ≤ ε i)
    (hL : ∀ᶠ i in p, Tendsto (F i) l (𝓝 (L i))) :
    ∃ ℓ, Tendsto A l (𝓝 ℓ) ∧ Tendsto L p (𝓝 ℓ) := by
  have hdist : ∀ i j, (∀ x, dist (F i x) (A x) ≤ ε i) → (∀ x, dist (F j x) (A x) ≤ ε j) →
      Tendsto (F i) l (𝓝 (L i)) → Tendsto (F j) l (𝓝 (L j)) → dist (L i) (L j) ≤ ε i + ε j :=
    fun i j hi hj hLi hLj => le_of_tendsto (hLi.dist hLj) (Eventually.of_forall fun x =>
      (dist_triangle_right _ _ (A x)).trans (add_le_add (hi x) (hj x)))
  have hcauchy : Cauchy (p.map L) := by
    refine Metric.cauchy_iff.2 ⟨inferInstance, fun δ hδ => ?_⟩
    have hS : ∀ᶠ i in p, ε i < δ / 2 ∧ (∀ x, dist (F i x) (A x) ≤ ε i) ∧
        Tendsto (F i) l (𝓝 (L i)) :=
      ((hε.eventually (gt_mem_nhds (half_pos hδ))).and hF).and hL |>.mono fun i h =>
        ⟨h.1.1, h.1.2, h.2⟩
    refine ⟨L '' {i | ε i < δ / 2 ∧ (∀ x, dist (F i x) (A x) ≤ ε i) ∧
      Tendsto (F i) l (𝓝 (L i))}, image_mem_map hS, ?_⟩
    rintro _ ⟨i, ⟨hi, hFi, hLi⟩, rfl⟩ _ ⟨j, ⟨hj, hFj, hLj⟩, rfl⟩
    exact (hdist i j hFi hFj hLi hLj).trans_lt (by linarith)
  obtain ⟨ℓ, hℓ⟩ := CompleteSpace.complete hcauchy
  refine ⟨ℓ, ?_, hℓ⟩
  have hunif : TendstoUniformly F A p := by
    refine Metric.tendstoUniformly_iff.2 fun δ hδ => ?_
    filter_upwards [hF, hε.eventually (gt_mem_nhds hδ)] with i hi hεi x
    rw [dist_comm]
    exact (hi x).trans_lt hεi
  exact hunif.tendsto_of_eventually_tendsto hL hℓ

end
