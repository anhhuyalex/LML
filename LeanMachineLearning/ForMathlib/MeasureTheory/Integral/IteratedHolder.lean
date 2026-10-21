/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Hölder's inequality for an average over a random finite measure

For a random finite state space with law `κ g` depending on a parameter `g ~ μ`, Hölder's
inequality holds for the iterated average `∫ g, ∫ z, · ∂κ g ∂μ`: apply it first under each `κ g`
and then to the resulting functions of `g`.
-/

@[expose] public section

open MeasureTheory

/-- **Hölder's inequality for an iterated average** over a finite state space. -/
theorem integral_integral_mul_le_Lp_mul_Lq {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [Finite Z] [DiscreteMeasurableSpace Z] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (κ : Ω → Measure Z) [∀ g, IsProbabilityMeasure (κ g)] {p r : ℝ} (hpr : p.HolderConjugate r)
    {A B : Z → ℝ} (hA : ∀ z, 0 ≤ A z) (hB : ∀ z, 0 ≤ B z)
    (hmA : AEStronglyMeasurable (fun g => ∫ z, A z ^ p ∂κ g) μ)
    (hmB : AEStronglyMeasurable (fun g => ∫ z, B z ^ r ∂κ g) μ) :
    ∫ g, ∫ z, A z * B z ∂κ g ∂μ ≤
      (∫ g, ∫ z, A z ^ p ∂κ g ∂μ) ^ (1 / p) * (∫ g, ∫ z, B z ^ r ∂κ g ∂μ) ^ (1 / r) := by
  have hp : 0 < p := hpr.pos
  have hr : 0 < r := hpr.symm.pos
  set a : Ω → ℝ := fun g => ∫ z, A z ^ p ∂κ g with ha
  set b : Ω → ℝ := fun g => ∫ z, B z ^ r ∂κ g with hb
  have ha0 : ∀ g, 0 ≤ a g := fun g => integral_nonneg fun z => Real.rpow_nonneg (hA z) p
  have hb0 : ∀ g, 0 ≤ b g := fun g => integral_nonneg fun z => Real.rpow_nonneg (hB z) r
  obtain ⟨M, hM0, hMA, hMB⟩ : ∃ M : ℝ, 0 ≤ M ∧ (∀ z, A z ≤ M) ∧ ∀ z, B z ≤ M := by
    obtain ⟨M1, h1⟩ := (Set.finite_range A).bddAbove
    obtain ⟨M2, h2⟩ := (Set.finite_range B).bddAbove
    refine ⟨max (max M1 M2) 0, le_max_right _ _, fun z => ?_, fun z => ?_⟩
    · exact (h1 ⟨z, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (h2 ⟨z, rfl⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
  have haM : ∀ g, a g ^ (1 / p) ≤ M := fun g => by
    have h1 : a g ≤ M ^ p := by
      have := norm_integral_le_of_norm_le_const (μ := κ g) (f := fun z => A z ^ p) (C := M ^ p)
        (ae_of_all _ fun z => by
          rw [Real.norm_of_nonneg (Real.rpow_nonneg (hA z) p)]
          exact Real.rpow_le_rpow (hA z) (hMA z) hp.le)
      exact (le_abs_self _).trans (by simpa using this)
    calc a g ^ (1 / p) ≤ (M ^ p) ^ (1 / p) := Real.rpow_le_rpow (ha0 g) h1 (by positivity)
      _ = M := by rw [← Real.rpow_mul hM0, mul_one_div_cancel hp.ne', Real.rpow_one]
  have hbM : ∀ g, b g ^ (1 / r) ≤ M := fun g => by
    have h1 : b g ≤ M ^ r := by
      have := norm_integral_le_of_norm_le_const (μ := κ g) (f := fun z => B z ^ r) (C := M ^ r)
        (ae_of_all _ fun z => by
          rw [Real.norm_of_nonneg (Real.rpow_nonneg (hB z) r)]
          exact Real.rpow_le_rpow (hB z) (hMB z) hr.le)
      exact (le_abs_self _).trans (by simpa using this)
    calc b g ^ (1 / r) ≤ (M ^ r) ^ (1 / r) := Real.rpow_le_rpow (hb0 g) h1 (by positivity)
      _ = M := by rw [← Real.rpow_mul hM0, mul_one_div_cancel hr.ne', Real.rpow_one]
  have hma : AEStronglyMeasurable (fun g => a g ^ (1 / p)) μ :=
    (hmA.aemeasurable.pow_const _).aestronglyMeasurable
  have hmb : AEStronglyMeasurable (fun g => b g ^ (1 / r)) μ :=
    (hmB.aemeasurable.pow_const _).aestronglyMeasurable
  have hLa : MemLp (fun g => a g ^ (1 / p)) (ENNReal.ofReal p) μ :=
    MemLp.of_bound hma M (ae_of_all _ fun g => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (ha0 g) _)]; exact haM g)
  have hLb : MemLp (fun g => b g ^ (1 / r)) (ENNReal.ofReal r) μ :=
    MemLp.of_bound hmb M (ae_of_all _ fun g => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (hb0 g) _)]; exact hbM g)
  have hint : Integrable (fun g => a g ^ (1 / p) * b g ^ (1 / r)) μ :=
    Integrable.of_bound (hma.mul hmb) (M * M) (ae_of_all _ fun g => by
      rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (ha0 g) _)
        (Real.rpow_nonneg (hb0 g) _))]
      exact mul_le_mul (haM g) (hbM g) (Real.rpow_nonneg (hb0 g) _) hM0)
  have hinner : ∀ g, ∫ z, A z * B z ∂κ g ≤ a g ^ (1 / p) * b g ^ (1 / r) := fun g =>
    integral_mul_le_Lp_mul_Lq_of_nonneg hpr (ae_of_all _ hA) (ae_of_all _ hB)
      MemLp.of_discrete MemLp.of_discrete
  calc ∫ g, ∫ z, A z * B z ∂κ g ∂μ ≤ ∫ g, a g ^ (1 / p) * b g ^ (1 / r) ∂μ :=
        integral_mono_of_nonneg (ae_of_all _ fun g => integral_nonneg fun z => mul_nonneg
          (hA z) (hB z)) hint (ae_of_all _ hinner)
    _ ≤ (∫ g, (a g ^ (1 / p)) ^ p ∂μ) ^ (1 / p) * (∫ g, (b g ^ (1 / r)) ^ r ∂μ) ^ (1 / r) :=
        integral_mul_le_Lp_mul_Lq_of_nonneg hpr
          (ae_of_all _ fun g => Real.rpow_nonneg (ha0 g) _)
          (ae_of_all _ fun g => Real.rpow_nonneg (hb0 g) _) hLa hLb
    _ = _ := by
        have e1 : ∀ g, (a g ^ (1 / p)) ^ p = a g := fun g => by
          rw [← Real.rpow_mul (ha0 g), one_div_mul_cancel hp.ne', Real.rpow_one]
        have e2 : ∀ g, (b g ^ (1 / r)) ^ r = b g := fun g => by
          rw [← Real.rpow_mul (hb0 g), one_div_mul_cancel hr.ne', Real.rpow_one]
        simp only [e1, e2]
