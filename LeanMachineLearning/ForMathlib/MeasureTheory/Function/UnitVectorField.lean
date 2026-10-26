/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Normalizing a measurable vector field without a case split

A measurable family `m : Ω → (ι → ℝ)` over a nonempty finite index type `ι` has a measurable
*unit* direction field `u` with `m ω = ‖m ω‖ • u ω`, where `‖m ω‖ = √(m ω ⬝ᵥ m ω)`;
where `m ω = 0` the direction is a fixed basis vector.  This removes the case split
`A = 0` / `A ≠ 0` in Talagrand's renormalization `z = A⁻¹ ∑ g_i ⟨σ_i⟩_-` (Lemma 1.7.6).
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

/-- **A measurable unit direction field.**  For a nonempty finite index type `ι` and a measurable
vector field `m` there is a measurable `u` with `u ω ⬝ᵥ u ω = 1` and
`m ω = √(m ω ⬝ᵥ m ω) • u ω`. -/
theorem exists_measurable_unit_field {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    {m : Ω → ι → ℝ} (hm : ∀ i, Measurable fun ω => m ω i) :
    ∃ u : Ω → ι → ℝ, (∀ i, Measurable fun ω => u ω i) ∧ (∀ ω, u ω ⬝ᵥ u ω = 1) ∧
      ∀ ω, m ω = Real.sqrt (m ω ⬝ᵥ m ω) • u ω := by
  classical
  set A : Ω → ℝ := fun ω => Real.sqrt (m ω ⬝ᵥ m ω) with hA
  have hAm : Measurable A := by
    refine Real.continuous_sqrt.measurable.comp ?_
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun i _ => (hm i).mul (hm i)
  have hAsq : ∀ ω, A ω ^ 2 = m ω ⬝ᵥ m ω := fun ω =>
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_self_nonneg _)
  let e0 : ι → ℝ := Pi.single (Classical.arbitrary ι) 1
  refine ⟨fun ω => if A ω = 0 then e0 else (A ω)⁻¹ • m ω, fun i => ?_, fun ω => ?_, fun ω => ?_⟩
  · have hset : MeasurableSet {ω | A ω = 0} := hAm (measurableSet_singleton 0)
    have key : (fun ω => (if A ω = 0 then e0 else (A ω)⁻¹ • m ω) i) =
        fun ω => if A ω = 0 then e0 i else (A ω)⁻¹ * m ω i := by
      funext ω; split_ifs <;> simp
    change Measurable fun ω => (if A ω = 0 then e0 else (A ω)⁻¹ • m ω) i
    rw [key]
    exact Measurable.ite hset measurable_const (hAm.inv.mul (hm i))
  · by_cases h0 : A ω = 0
    · simp [h0, e0]
    · simp only [h0, ite_false, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      rw [← hAsq ω]; field_simp
  · by_cases h0 : A ω = 0
    · have : m ω ⬝ᵥ m ω = 0 := by rw [← hAsq ω, h0]; ring
      have hz : m ω = 0 := funext fun i => mul_self_eq_zero.mp
        ((Finset.sum_eq_zero_iff_of_nonneg
          fun j _ => mul_self_nonneg (m ω j)).mp this i (Finset.mem_univ i))
      simp [h0, hz]
    · simp only [h0, ite_false]
      rw [smul_smul, mul_inv_cancel₀ h0, one_smul]
