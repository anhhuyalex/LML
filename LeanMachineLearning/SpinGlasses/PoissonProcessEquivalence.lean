/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonProcess
public import LeanMachineLearning.ForMathlib.Probability.HasCondDistrib

/-!
# Poisson blocks: conditional sampling and Campbell's formula

The conditional i.i.d. law is expressed on the block coordinates, without attempting to
canonically enumerate the points of an arbitrary counting measure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpinGlasses

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

/-- Conditionally on a Poisson block's count, its entire sample sequence is i.i.d.
This is stronger than the assertion concerning only the first `N` points. -/
theorem hasCondDistrib_poissonBlockSamples {P : Measure Ω} [IsProbabilityMeasure P]
    (ν : Measure S) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {B : Ω → ℕ × (ℕ → S)}
    (hB : HasLaw B (Po(r).prod (Measure.infinitePi fun _ : ℕ => ν)) P) :
    HasCondDistrib (fun ω => (B ω).2) (fun ω => (B ω).1)
      (ProbabilityTheory.Kernel.const ℕ (Measure.infinitePi fun _ : ℕ => ν)) P := by
  have hN : HasLaw (fun ω => (B ω).1) Po(r) P :=
    measurePreserving_fst.hasLaw.comp hB
  have hX : HasLaw (fun ω => (B ω).2) (Measure.infinitePi fun _ : ℕ => ν) P :=
    measurePreserving_snd.hasLaw.comp hB
  have hind : IndepFun (fun ω => (B ω).1) (fun ω => (B ω).2) P := by
    apply (indepFun_iff_map_prod_eq_prod_map_map hN.aemeasurable hX.aemeasurable).2
    simpa only [hN.map_eq, hX.map_eq] using hB.map_eq
  exact hind.hasCondDistrib_const hN.aemeasurable hX

/-- Campbell's formula for a family of independent Poisson blocks. No atomlessness or
independence is needed for this expectation identity once each block law is known. -/
theorem lintegral_poissonCountingMeasure {P : Measure Ω}
    (ν : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → S)}
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    {f : S → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, ∫⁻ s, f s ∂poissonCountingMeasure
      (fun n => (B n ω).1) (fun n l => (B n ω).2 l) ∂P =
      ∫⁻ s, f s ∂Measure.sum (fun n => (r n : ℝ≥0∞) • ν n) := by
  have hg : Measurable fun q : ℕ × (ℕ → S) =>
      ∑ l ∈ Finset.range q.1, f (q.2 l) := by
    apply measurable_from_prod_countable_right
    intro k
    change Measurable fun y : ℕ → S => ∑ l ∈ Finset.range k, f (y l)
    exact Finset.measurable_sum _ fun l _ => hf.comp (measurable_pi_apply l)
  have hm : ∀ n, AEMeasurable (fun ω =>
      ∑ l ∈ Finset.range (B n ω).1, f ((B n ω).2 l)) P := fun n =>
    hg.comp_aemeasurable (hlaw n).aemeasurable
  simp only [poissonCountingMeasure, lintegral_sum_measure, lintegral_finsetSum_measure,
    lintegral_dirac' _ hf]
  rw [lintegral_tsum (fun n => hm n)]
  congr 1
  ext n
  rw [lintegral_smul_measure, (hlaw n).lintegral_comp hg.aemeasurable]
  rw [lintegral_prod _ hg.aemeasurable]
  have hinner (k : ℕ) :
      (∫⁻ x : ℕ → S, ∑ l ∈ Finset.range k, f (x l) ∂
        Measure.infinitePi fun _ : ℕ => ν n) =
        ∑ l ∈ Finset.range k, ∫⁻ s, f s ∂ν n := by
    rw [lintegral_finsetSum (Finset.range k)
      (f := fun l (x : ℕ → S) => f (x l))
      (fun l _ => hf.comp (measurable_pi_apply l))]
    congr 1
    ext l
    exact (hasLaw_eval_infinitePi (fun _ : ℕ => ν n) l).lintegral_comp
      hf.aemeasurable
  simp_rw [hinner, Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul]
  rw [lintegral_mul_const (∫⁻ s, f s ∂ν n)
    (measurable_of_countable _ : Measurable fun k : ℕ => (k : ℝ≥0∞))]
  have hmean : (∫⁻ k : ℕ, (k : ℝ≥0∞) ∂Po(r n)) = (r n : ℝ≥0∞) := by
    change (∫⁻ k : ℕ, ((k : ℝ≥0) : ℝ≥0∞) ∂Po(r n)) = _
    rw [lintegral_coe_eq_integral _
      (by simpa using integrable_natCast_poissonMeasure (r n))]
    rw [show (∫ k : ℕ, ((k : ℝ≥0) : ℝ) ∂Po(r n)) =
      ∫ k : ℕ, (k : ℝ) ∂Po(r n) from rfl,
      integral_natCast_poissonMeasure]
    simp
  rw [hmean]
  rfl

/-- In the independent-block representation, the counts on partition cells have the
prescribed joint Poisson law. The full configuration law is the pushforward of these blocks;
this avoids choosing an enumeration of the atoms of a general random counting measure. -/
theorem hasLaw_partitionBlockCounts {P : Measure Ω}
    (ν : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → S)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P) :
    HasLaw (fun ω n => (B n ω).1) (Measure.infinitePi fun n => Po(r n)) P := by
  have hi : iIndepFun (fun n ω => (B n ω).1) P :=
    hB.comp (fun _ b => b.1) fun _ => measurable_fst
  have hcount : ∀ n, HasLaw (fun ω => (B n ω).1) (Po(r n)) P :=
    fun n => measurePreserving_fst.hasLaw.comp (hlaw n)
  refine ⟨(measurable_pi_iff.2 fun n => measurable_fst.comp (hBm n)).aemeasurable, ?_⟩
  simpa only [Function.comp_def,
    show (fun n => P.map (fun ω => (B n ω).1)) =
      (fun n => Po(r n)) from funext fun n => (hcount n).map_eq] using
    hi.map_fun_eq_infinitePi_map (fun n => measurable_fst.comp (hBm n))

end SpinGlasses
