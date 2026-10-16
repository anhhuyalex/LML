/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Independence.Basic

/-!
# Independent random variables with nonatomic laws

Independent random variables do not coincide when one marginal law has no atoms. This also gives
pairwise distinctness for countable mutually independent families.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω S ι : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
  [MeasurableEq S] {P : Measure Ω}

/-- The diagonal has zero product measure when the right marginal has no atoms. -/
theorem Measure.prod_diagonal_eq_zero (μ ν : Measure S) [SFinite ν]
    [NullSingletonClass ν] : μ.prod ν (Set.diagonal S) = 0 := by
  rw [Measure.prod_apply measurableSet_diagonal]
  refine (lintegral_congr fun x => ?_).trans lintegral_zero
  rw [show Prod.mk x ⁻¹' Set.diagonal S = {x} by
    ext y
    simp only [Set.mem_preimage, Set.mem_diagonal_iff, Set.mem_singleton_iff]
    exact eq_comm]
  exact measure_singleton x

/-- Independent random variables are almost surely unequal when the law of the second variable
has no atoms. -/
theorem IndepFun.measure_eq_zero {X Y : Ω → S} [IsFiniteMeasure P]
    (hXY : IndepFun X Y P) (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    [NullSingletonClass (Measure.map Y P)] :
    P {ω | X ω = Y ω} = 0 := by
  have hdiag : {ω | X ω = Y ω} = (fun ω => (X ω, Y ω)) ⁻¹' Set.diagonal S := by
    ext ω
    simp [Set.mem_diagonal_iff]
  rw [hdiag, ← Measure.map_apply_of_aemeasurable (hX.prodMk hY) measurableSet_diagonal,
    hXY.map_prod_eq_prod_map_map hX hY, Measure.prod_diagonal_eq_zero]

/-- A countable mutually independent family with nonatomic marginal laws is almost surely
pairwise distinct. -/
theorem iIndepFun.ae_pairwise_ne [Countable ι] [IsFiniteMeasure P]
    {X : ι → Ω → S} (hX : iIndepFun X P)
    (hXm : ∀ i, AEMeasurable (X i) P)
    (hnull : ∀ i, NullSingletonClass (Measure.map (X i) P)) :
    ∀ᵐ ω ∂P, Pairwise fun i j => X i ω ≠ X j ω := by
  have hpair (i j : ι) (hij : i ≠ j) : ∀ᵐ ω ∂P, X i ω ≠ X j ω := by
    let _ : NullSingletonClass (Measure.map (X j) P) := hnull j
    exact measure_eq_zero_iff_ae_notMem.1
      ((hX.indepFun hij).measure_eq_zero (hXm i) (hXm j))
  rw [show (fun ω => Pairwise fun i j => X i ω ≠ X j ω) =
    fun ω => ∀ i, ∀ j, i ≠ j → X i ω ≠ X j ω by ext ω; rfl]
  exact ae_all_iff.2 fun i => ae_all_iff.2 fun j =>
    ae_all_iff.2 fun hij => hpair i j hij

end ProbabilityTheory
