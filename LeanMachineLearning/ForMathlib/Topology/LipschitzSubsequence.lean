/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# A convergent subsequence of equi-Lipschitz functions

Every sequence of `1`-Lipschitz functions `ℝ → ℝ` that vanish at `0` has a subsequence that
converges pointwise on a given interval `[-r, r]` (Arzelà-Ascoli).
-/

@[expose] public section

open Filter Topology Set

/-- **Arzelà-Ascoli for `1`-Lipschitz functions vanishing at `0`:** a subsequence converges at
every point of `[-r, r]`. -/
theorem exists_subseq_tendsto_of_lipschitz (f : ℕ → ℝ → ℝ) (hf : ∀ n, LipschitzWith 1 (f n))
    (h0 : ∀ n, f n 0 = 0) (r : ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ ψ : ℝ → ℝ, ∀ x ∈ Icc (-r) r,
      Tendsto (fun n => f (φ n) x) atTop (𝓝 (ψ x)) := by
  have hLip : ∀ n (x y : ℝ), |f n x - f n y| ≤ |x - y| := by
    intro n x y
    simpa [Real.dist_eq] using (hf n).dist_le_mul x y
  let g : ℕ → C(Icc (-r) r, ℝ) := fun n =>
    ⟨fun x => f n x.1, (hf n).continuous.comp continuous_subtype_val⟩
  let S : Set C(Icc (-r) r, ℝ) :=
    {F | (∀ x y : Icc (-r) r, |F x - F y| ≤ dist x y) ∧ ∀ x, |F x| ≤ r}
  let T : Set (Icc (-r) r → ℝ) :=
    {u | (∀ x y : Icc (-r) r, |u x - u y| ≤ dist x y) ∧ ∀ x, |u x| ≤ r}
  have hg : ∀ n, g n ∈ S := by
    intro n
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · simpa [g, Real.dist_eq, Subtype.dist_eq] using hLip n x.1 y.1
    · have := hLip n x.1 0
      rw [h0 n, sub_zero, sub_zero] at this
      exact this.trans (abs_le.2 ⟨by linarith [x.2.1], x.2.2⟩)
  have hTclosed : IsClosed T := by
    have h1 : IsClosed {u : Icc (-r) r → ℝ | ∀ x y : Icc (-r) r, |u x - u y| ≤ dist x y} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun x => isClosed_iInter fun y =>
        isClosed_le (by fun_prop) continuous_const
    have h2 : IsClosed {u : Icc (-r) r → ℝ | ∀ x, |u x| ≤ r} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun x => isClosed_le (by fun_prop) continuous_const
    exact h1.inter h2
  have hTcompact : IsCompact T := by
    refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ : Icc (-r) r => isCompact_Icc
      (a := -r) (b := r)) hTclosed fun u hu x _ => ?_
    exact abs_le.1 (hu.2 x)
  have himg : (ContinuousMap.toFun '' S) = T := by
    ext u
    constructor
    · rintro ⟨F, hF, rfl⟩
      exact hF
    · intro hu
      have hl : LipschitzWith 1 u := LipschitzWith.of_dist_le_mul fun x y => by
        simpa [Real.dist_eq, Subtype.dist_eq] using hu.1 x y
      exact ⟨⟨u, hl.continuous⟩, hu, rfl⟩
  have hS1 : IsCompact (ContinuousMap.toFun '' S) := himg ▸ hTcompact
  have hS2 : Equicontinuous ((↑) : S → Icc (-r) r → ℝ) := by
    refine (LipschitzWith.uniformEquicontinuous (fun i : S => (i : C(Icc (-r) r, ℝ)).toFun) 1
      fun i => LipschitzWith.of_dist_le_mul fun x y => ?_).equicontinuous
    simpa [Real.dist_eq, Subtype.dist_eq] using i.2.1 x y
  have hSc : IsCompact S := ArzelaAscoli.isCompact_of_equicontinuous S hS1 hS2
  obtain ⟨a, -, φ, hφ, hlim⟩ := hSc.tendsto_subseq hg
  refine ⟨φ, hφ, fun x => if hx : x ∈ Icc (-r) r then a ⟨x, hx⟩ else 0, fun x hx => ?_⟩
  simp only [hx, dite_true]
  exact ((ContinuousMap.continuous_eval_const (⟨x, hx⟩ : Icc (-r) r)).tendsto a).comp hlim
