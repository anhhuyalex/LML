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
energy derivatives, i.e. `replicaDiffWith` of the covariance functional. It is obtained from
`hasDerivAt_integral_pi_tilted_of_dominated` for the `Option R`-indexed product. Only a uniform
upper bound on the energy and an integrable bound on its derivative are assumed.
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped Topology

namespace MeasureTheory

/-- **Derivative of a replica difference along a parameter path, moving observable.** Both the
energy `E r` and the one-spin observable `h r` depend on the parameter. The derivative is the
replica difference of `∂_r h` plus `replicaDiffWith` of the covariance with the energy derivative.
-/
theorem hasDerivAt_replicaDiff_tilted_moving {α R : Type*} [MeasurableSpace α] [Fintype R]
    {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ]
    {E E' : ℝ → α → ℝ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t)
    (hE : ∀ r ∈ s, Measurable (E r)) (hE' : Measurable (E' t))
    {B : ℝ} (hEb : ∀ r ∈ s, ∀ a, E r a ≤ B)
    {b : α → ℝ} (hb : Integrable b μ) (hdb : ∀ r ∈ s, ∀ a, |E' r a| ≤ b a)
    (hd : ∀ a, ∀ r ∈ s, HasDerivAt (fun q => E q a) (E' r a) r)
    {F : (R → α) → ℝ} (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C)
    {h h' : ℝ → α → ℝ} (hh : ∀ r ∈ s, Measurable (h r)) (hh' : Measurable (h' t))
    {H H' : ℝ} (hhb : ∀ r ∈ s, ∀ a, |h r a| ≤ H) (hh'b : ∀ r ∈ s, ∀ a, |h' r a| ≤ H')
    (hhd : ∀ a, ∀ r ∈ s, HasDerivAt (fun q => h q a) (h' r a) r) :
    HasDerivAt (fun r => replicaDiff (μ.tilted (E r)) F (h r))
      (replicaDiff (μ.tilted (E t)) F (h' t) +
        replicaDiffWith (fun G => (∫ σ : Option R → α, G σ * (∑ k, E' t (σ k))
            ∂(Measure.pi fun _ : Option R => μ.tilted (E t))) -
          (∫ σ : Option R → α, G σ ∂(Measure.pi fun _ : Option R => μ.tilted (E t))) *
            ∫ σ : Option R → α, (∑ k, E' t (σ k))
              ∂(Measure.pi fun _ : Option R => μ.tilted (E t))) F (h t)) t := by
  have hFo : Measurable fun σ : Option R → α => F (fun j => σ (some j)) :=
    hF.comp (by fun_prop)
  have hG (i : Option R) := hasDerivAt_integral_pi_tilted_moving (R := Option R) hs hE hE' hEb hb
    hdb hd (Ψ := fun r σ => F (fun j => σ (some j)) * h r (σ i))
    (Ψ' := fun r σ => F (fun j => σ (some j)) * h' r (σ i))
    (fun r hr => hFo.mul ((hh r hr).comp (measurable_pi_apply i)))
    (hFo.mul (hh'.comp (measurable_pi_apply i))) (C := C * H) (C' := C * H')
    (fun r hr σ => by
      rw [abs_mul]
      exact mul_le_mul (hFb _) (hhb r hr _) (abs_nonneg _)
        ((abs_nonneg _).trans (hFb fun j => σ (some j))))
    (fun r hr σ => by
      rw [abs_mul]
      exact mul_le_mul (hFb _) (hh'b r hr _) (abs_nonneg _)
        ((abs_nonneg _).trans (hFb fun j => σ (some j))))
    (fun σ r hr => (hhd (σ i) r hr).const_mul _)
  have hsum := (HasDerivAt.fun_sum (u := (Finset.univ : Finset R)) fun i _ => hG (some i)).sub
    ((hG none).const_mul (Fintype.card R : ℝ))
  refine hsum.congr_deriv ?_
  simp only [replicaDiffWith, replicaDiff, Finset.sum_add_distrib, mul_add]
  ring

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
  have := hasDerivAt_replicaDiff_tilted_moving hs hE hE' hEb hb hdb hd hF hFb (h := fun _ => h)
    (h' := fun _ _ => 0) (fun _ _ => hh) measurable_const (H := H) (H' := 0)
    (fun _ _ a => hhb a) (fun _ _ _ => by simp) (fun a r _ => hasDerivAt_const r (h a))
  refine this.congr_deriv ?_
  rw [show (fun _ : α => (0 : ℝ)) = 0 from rfl, replicaDiff_zero, zero_add]

/-- **The derivative of a replica difference is a replica difference of replica differences.**
When `μ.tilted (E t)` is a probability measure and `E' t` is integrable against it, the covariance
functional of `hasDerivAt_replicaDiff_tilted` is `replicaDiff` for the `Option R` replicas
(`integral_pi_cov_sum_eq_sum_sub_fresh`). -/
theorem hasDerivAt_replicaDiff_tilted_replicaDiff {α R : Type*} [MeasurableSpace α] [Fintype R]
    {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ]
    {E E' : ℝ → α → ℝ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t)
    (hE : ∀ r ∈ s, Measurable (E r)) (hE' : Measurable (E' t))
    {B : ℝ} (hEb : ∀ r ∈ s, ∀ a, E r a ≤ B)
    {b : α → ℝ} (hb : Integrable b μ) (hdb : ∀ r ∈ s, ∀ a, |E' r a| ≤ b a)
    (hd : ∀ a, ∀ r ∈ s, HasDerivAt (fun q => E q a) (E' r a) r)
    {F : (R → α) → ℝ} (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C)
    {h : α → ℝ} (hh : Measurable h) {H : ℝ} (hhb : ∀ a, |h a| ≤ H)
    [IsProbabilityMeasure (μ.tilted (E t))] (hI : Integrable (E' t) (μ.tilted (E t))) :
    HasDerivAt (fun r => replicaDiff (μ.tilted (E r)) F h)
      (replicaDiffWith (fun G => replicaDiff (μ.tilted (E t)) G (E' t)) F h) t := by
  refine (hasDerivAt_replicaDiff_tilted hs hE hE' hEb hb hdb hd hF hFb hh hhb).congr_deriv ?_
  have hL (i : Option R) :
      ((∫ σ : Option R → α, F (fun j => σ (some j)) * h (σ i) * (∑ k, E' t (σ k))
          ∂(Measure.pi fun _ : Option R => μ.tilted (E t))) -
        (∫ σ : Option R → α, F (fun j => σ (some j)) * h (σ i)
          ∂(Measure.pi fun _ : Option R => μ.tilted (E t))) *
          ∫ σ : Option R → α, (∑ k, E' t (σ k))
            ∂(Measure.pi fun _ : Option R => μ.tilted (E t))) =
      replicaDiff (μ.tilted (E t)) (fun σ : Option R → α => F (fun j => σ (some j)) * h (σ i))
        (E' t) := by
    refine integral_pi_cov_sum_eq_sum_sub_fresh (R := Option R) (μ.tilted (E t))
      (fun σ : Option R → α => F (fun j => σ (some j)) * h (σ i)) ?_ (C := C * H) ?_ (E' t) hI
    · exact ((hF.comp (by fun_prop)).mul (hh.comp (measurable_pi_apply i))).aestronglyMeasurable
    · intro σ
      rw [abs_mul]
      exact mul_le_mul (hFb _) (hhb _) (abs_nonneg _)
        ((abs_nonneg _).trans (hFb fun j => σ (some j)))
  simp only [replicaDiffWith]
  rw [Finset.sum_congr rfl fun i _ => hL (some i), hL none]

end MeasureTheory
