/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct

/-!
# Derivative of the replica difference along a parameter

For a path of energies `E r` on a finite base measure `μ`, the replica difference of a fixed
bounded observable `h` against a bounded replica observable `F`,
`r ↦ replicaDiff (μ.tilted (E r)) F h`, is differentiable. Its derivative is the sum over the
`|R| + 1` replicas of the covariances of `F h(σ_i)` (respectively `F h(σ_*)`) with the sum of the
energy derivatives, i.e. `replicaDiffWith` of the covariance functional, obtained from `hasDerivAt_integral_pi_tilted_of_dominated` for the
`Option R`-indexed product. Only a uniform upper bound on the energy and an integrable bound on
its derivative are assumed.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped Topology

namespace MeasureTheory

/-- **Derivative of a replica difference along a parameter path.** -/
theorem hasDerivAt_replicaDiff_tilted {α R : Type*} [MeasurableSpace α] [Fintype R]
    {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ]
    {E E' : ℝ → α → ℝ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t)
    (hE : ∀ r ∈ s, Measurable (E r)) (hE' : Measurable (E' t))
    {B : ℝ} (hEb : ∀ r ∈ s, ∀ a, E r a ≤ B)
    {b : α → ℝ} (hb : Integrable b μ) (hdb : ∀ r ∈ s, ∀ a, |E' r a| ≤ b a)
    (hd : ∀ a, ∀ r ∈ s, HasDerivAt (fun q => E q a) (E' r a) r)
    {F : (R → α) → ℝ} (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C)
    {h : α → ℝ} (hh : Measurable h) {H : ℝ} (hhb : ∀ a, |h a| ≤ H) :
    HasDerivAt (fun r => replicaDiff (μ.tilted (E r)) F h)
      (replicaDiffWith (fun G => (∫ σ : Option R → α, G σ * (∑ k, E' t (σ k))
          ∂(Measure.pi fun _ : Option R => μ.tilted (E t))) -
        (∫ σ : Option R → α, G σ ∂(Measure.pi fun _ : Option R => μ.tilted (E t))) *
          ∫ σ : Option R → α, (∑ k, E' t (σ k))
            ∂(Measure.pi fun _ : Option R => μ.tilted (E t))) F h) t := by
  have hFo : Measurable fun σ : Option R → α => F (fun j => σ (some j)) :=
    hF.comp (by fun_prop)
  have hG (i : Option R) : HasDerivAt
      (fun r => ∫ σ : Option R → α, F (fun j => σ (some j)) * h (σ i)
        ∂(Measure.pi fun _ : Option R => μ.tilted (E r)))
      ((∫ σ : Option R → α, F (fun j => σ (some j)) * h (σ i) * (∑ k, E' t (σ k))
          ∂(Measure.pi fun _ : Option R => μ.tilted (E t))) -
        (∫ σ : Option R → α, F (fun j => σ (some j)) * h (σ i)
          ∂(Measure.pi fun _ : Option R => μ.tilted (E t))) *
          ∫ σ : Option R → α, (∑ k, E' t (σ k))
            ∂(Measure.pi fun _ : Option R => μ.tilted (E t))) t :=
    hasDerivAt_integral_pi_tilted_of_dominated (R := Option R) hs hE hE' hEb hb hdb hd
      (F := fun σ => F (fun j => σ (some j)) * h (σ i))
      (hFo.mul (hh.comp (measurable_pi_apply i))) (C := C * H) fun σ => by
        rw [abs_mul]
        exact mul_le_mul (hFb _) (hhb _) (abs_nonneg _)
          ((abs_nonneg _).trans (hFb fun j => σ (some j)))
  exact (HasDerivAt.fun_sum fun i _ => hG (some i)).sub ((hG none).const_mul _)

end MeasureTheory
