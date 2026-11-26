/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Hölder's inequality for an average over a random finite measure

For a measure `κ g` on a state space, depending on a parameter `g ~ μ`, Hölder's
inequality holds for the iterated average `∫ g, ∫ z, · ∂κ g ∂μ`: apply it first under each `κ g`
and then to the resulting functions of `g`.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

/-- **`A ^ (1 / p)` is in `L^p` when `A` is integrable and a.e. nonnegative.** -/
theorem memLp_rpow_inv_of_integrable_of_ae_nonneg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {A : Ω → ℝ} {p : ℝ} (hp : 0 < p) (hA0 : 0 ≤ᵐ[P] A) (hA : Integrable A P) :
    MemLp (fun ω => A ω ^ (1 / p)) (ENNReal.ofReal p) P := by
  have hm : AEStronglyMeasurable (fun ω => A ω ^ (1 / p)) P :=
    (hA.aestronglyMeasurable.aemeasurable.pow_const _).aestronglyMeasurable
  refine (integrable_norm_rpow_iff hm (by positivity) ENNReal.ofReal_ne_top).mp ?_
  rw [ENNReal.toReal_ofReal hp.le]
  refine hA.congr (hA0.mono fun ω hω => ?_)
  dsimp only
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hω _), ← Real.rpow_mul hω,
    one_div_mul_cancel hp.ne', Real.rpow_one]

/-- **`A ^ (1 / p)` is in `L^p` when `A ≥ 0` is integrable.** -/
theorem memLp_rpow_inv_of_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : Ω → ℝ} {p : ℝ} (hp : 0 < p) (hA0 : ∀ ω, 0 ≤ A ω) (hA : Integrable A P) :
    MemLp (fun ω => A ω ^ (1 / p)) (ENNReal.ofReal p) P :=
  memLp_rpow_inv_of_integrable_of_ae_nonneg hp (ae_of_all _ hA0) hA

end MeasureTheory

open MeasureTheory

/-- **Hölder's inequality for an iterated average:** apply Hölder under each measure `κ g`, and
then to the two resulting functions of `g`. -/
theorem integral_integral_mul_le_Lp_mul_Lq_of_memLp {Ω Z : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Z] (μ : Measure Ω) (κ : Ω → Measure Z) {p r : ℝ} (hpr : p.HolderConjugate r)
    {A B : Ω → Z → ℝ} (hA : ∀ᵐ g ∂μ, 0 ≤ᵐ[κ g] A g) (hB : ∀ᵐ g ∂μ, 0 ≤ᵐ[κ g] B g)
    (hLA : ∀ᵐ g ∂μ, MemLp (A g) (ENNReal.ofReal p) (κ g))
    (hLB : ∀ᵐ g ∂μ, MemLp (B g) (ENNReal.ofReal r) (κ g))
    (hiA : Integrable (fun g => ∫ z, A g z ^ p ∂κ g) μ)
    (hiB : Integrable (fun g => ∫ z, B g z ^ r ∂κ g) μ) :
    ∫ g, ∫ z, A g z * B g z ∂κ g ∂μ ≤
      (∫ g, ∫ z, A g z ^ p ∂κ g ∂μ) ^ (1 / p) * (∫ g, ∫ z, B g z ^ r ∂κ g ∂μ) ^ (1 / r) := by
  have hp : 0 < p := hpr.pos
  have hr : 0 < r := hpr.symm.pos
  set a : Ω → ℝ := fun g => ∫ z, A g z ^ p ∂κ g with ha
  set b : Ω → ℝ := fun g => ∫ z, B g z ^ r ∂κ g with hb
  have ha0 : 0 ≤ᵐ[μ] a := hA.mono fun g hg => integral_nonneg_of_ae
    (hg.mono fun z hz => Real.rpow_nonneg hz p)
  have hb0 : 0 ≤ᵐ[μ] b := hB.mono fun g hg => integral_nonneg_of_ae
    (hg.mono fun z hz => Real.rpow_nonneg hz r)
  have hLa := memLp_rpow_inv_of_integrable_of_ae_nonneg hp ha0 hiA
  have hLb := memLp_rpow_inv_of_integrable_of_ae_nonneg hr hb0 hiB
  have := hpr.ennrealOfReal
  have hint : Integrable (fun g => a g ^ (1 / p) * b g ^ (1 / r)) μ := hLa.integrable_mul hLb
  have hinner : ∀ᵐ g ∂μ, ∫ z, A g z * B g z ∂κ g ≤ a g ^ (1 / p) * b g ^ (1 / r) := by
    filter_upwards [hA, hB, hLA, hLB] with g h1 h2 h3 h4 using
      integral_mul_le_Lp_mul_Lq_of_nonneg hpr h1 h2 h3 h4
  have hab : ∀ᵐ g ∂μ, 0 ≤ a g ^ (1 / p) ∧ 0 ≤ b g ^ (1 / r) := by
    filter_upwards [ha0, hb0] with g h1 h2 using
      ⟨Real.rpow_nonneg h1 _, Real.rpow_nonneg h2 _⟩
  calc ∫ g, ∫ z, A g z * B g z ∂κ g ∂μ ≤ ∫ g, a g ^ (1 / p) * b g ^ (1 / r) ∂μ := by
        refine integral_mono_of_nonneg ?_ hint hinner
        filter_upwards [hA, hB] with g h1 h2
        exact integral_nonneg_of_ae (by
          filter_upwards [h1, h2] with z h3 h4 using mul_nonneg h3 h4)
    _ ≤ (∫ g, (a g ^ (1 / p)) ^ p ∂μ) ^ (1 / p) * (∫ g, (b g ^ (1 / r)) ^ r ∂μ) ^ (1 / r) :=
        integral_mul_le_Lp_mul_Lq_of_nonneg hpr (hab.mono fun _ h => h.1)
          (hab.mono fun _ h => h.2) hLa hLb
    _ = _ := by
        have e1 : ∫ g, (a g ^ (1 / p)) ^ p ∂μ = ∫ g, a g ∂μ := integral_congr_ae
          (ha0.mono fun g h => by simp only [one_div, Real.rpow_inv_rpow h hp.ne'])
        have e2 : ∫ g, (b g ^ (1 / r)) ^ r ∂μ = ∫ g, b g ∂μ := integral_congr_ae
          (hb0.mono fun g h => by simp only [one_div, Real.rpow_inv_rpow h hr.ne'])
        rw [e1, e2]

/-- **Hölder's inequality for an iterated average** over a finite state space. -/
theorem integral_integral_mul_le_Lp_mul_Lq {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [Finite Z] [DiscreteMeasurableSpace Z] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (κ : Ω → Measure Z) [∀ g, IsProbabilityMeasure (κ g)] {p r : ℝ} (hpr : p.HolderConjugate r)
    {A B : Z → ℝ} (hA : ∀ z, 0 ≤ A z) (hB : ∀ z, 0 ≤ B z)
    (hmA : AEStronglyMeasurable (fun g => ∫ z, A z ^ p ∂κ g) μ)
    (hmB : AEStronglyMeasurable (fun g => ∫ z, B z ^ r ∂κ g) μ) :
    ∫ g, ∫ z, A z * B z ∂κ g ∂μ ≤
      (∫ g, ∫ z, A z ^ p ∂κ g ∂μ) ^ (1 / p) * (∫ g, ∫ z, B z ^ r ∂κ g ∂μ) ^ (1 / r) := by
  have hbdd : ∀ (C : Z → ℝ) (q : ℝ), 0 < q → (∀ z, 0 ≤ C z) →
      AEStronglyMeasurable (fun g => ∫ z, C z ^ q ∂κ g) μ →
      Integrable (fun g => ∫ z, C z ^ q ∂κ g) μ := fun C q hq hC hm => by
    obtain ⟨M, hM⟩ := (Set.finite_range fun z => C z ^ q).bddAbove
    refine Integrable.of_bound hm M (ae_of_all _ fun g => ?_)
    have h := norm_integral_le_of_norm_le_const (μ := κ g) (f := fun z => C z ^ q) (C := M)
      (ae_of_all _ fun z => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (hC z) q)]
        exact hM ⟨z, rfl⟩)
    simpa using h
  exact integral_integral_mul_le_Lp_mul_Lq_of_memLp μ κ hpr (A := fun _ => A) (B := fun _ => B)
    (ae_of_all _ fun _ => ae_of_all _ hA) (ae_of_all _ fun _ => ae_of_all _ hB)
    (ae_of_all _ fun _ => MemLp.of_discrete) (ae_of_all _ fun _ => MemLp.of_discrete)
    (hbdd A p hpr.pos hA hmA) (hbdd B r hpr.symm.pos hB hmB)
