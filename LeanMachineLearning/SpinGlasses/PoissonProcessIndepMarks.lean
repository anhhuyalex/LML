/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonProcessTransform

/-!
# Independent second marks of Poisson blocks

If the points of independent Poisson blocks carry two marks with product law `νₙ ⊗ γₙ`, the
array of second marks is independent of the counts and first marks, and is itself an independent
array with laws `γₙ`. In the Poisson-Dirichlet application the first mark is the mass and the
second the Gaussian field, so one can condition on the counts and masses and treat the Gaussian
field as a fixed independent field.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpinGlasses

/-- A block with product mark law `ν ⊗ γ` is, after separating the two marks, the product of a
block with marks `ν` and an i.i.d. sequence of `γ`-marks. -/
theorem map_poissonBlock_split {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (ν : Measure S) [IsProbabilityMeasure ν] (γ : Measure T) [IsProbabilityMeasure γ] (r : ℝ≥0) :
    ((Po(r).prod (Measure.infinitePi fun _ : ℕ => ν.prod γ)).map
      fun b : ℕ × (ℕ → S × T) => ((b.1, fun l => (b.2 l).1), fun l => (b.2 l).2)) =
      (Po(r).prod (Measure.infinitePi fun _ : ℕ => ν)).prod
        (Measure.infinitePi fun _ : ℕ => γ) := by
  have hz := Measure.infinitePi_prod_map_zip (fun _ : ℕ => ν) (fun _ : ℕ => γ)
  have hzm : Measurable fun p : (ℕ → S) × (ℕ → T) => fun i => (p.1 i, p.2 i) :=
    measurable_pi_iff.2 fun i =>
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)
  have h1 := Measure.map_prod_map Po(r) ((Measure.infinitePi fun _ : ℕ => ν).prod
    (Measure.infinitePi fun _ : ℕ => γ)) measurable_id hzm
  rw [Measure.map_id] at h1
  rw [← hz, h1, Measure.map_map (by fun_prop) (by fun_prop)]
  have hassoc := (measurePreserving_prodAssoc Po(r) (Measure.infinitePi fun _ : ℕ => ν)
    (Measure.infinitePi fun _ : ℕ => γ)).symm
  rw [← hassoc.map_eq]
  rfl


/-- **Independent marks.** If Poisson blocks have product mark law `νₙ ⊗ γₙ`, the second marks
`g n l` are independent of the counts and first marks, and form an array of independent samples
from `γₙ`. This is the structure needed to condition on the counts and masses and treat the
Gaussian marks as a fixed independent field. -/
theorem indepFun_poissonBlocks_snd_marks {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [MeasurableSpace T] {P : Measure Ω} [IsProbabilityMeasure P]
    (ν : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ν n)]
    (γ : ℕ → Measure T) [∀ n, IsProbabilityMeasure (γ n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → S × T)} (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => (ν n).prod (γ n))) P) :
    IndepFun (fun ω n => ((B n ω).1, fun l => ((B n ω).2 l).1))
      (fun ω n l => ((B n ω).2 l).2) P ∧
    HasLaw (fun ω n l => ((B n ω).2 l).2)
      (Measure.infinitePi fun n => Measure.infinitePi fun _ : ℕ => γ n) P ∧
    HasLaw (fun ω n => ((B n ω).1, fun l => ((B n ω).2 l).1))
      (Measure.infinitePi fun n => Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P := by
  let ρ : ℕ × (ℕ → S × T) → (ℕ × (ℕ → S)) × (ℕ → T) :=
    fun b => ((b.1, fun l => (b.2 l).1), fun l => (b.2 l).2)
  have hρ : Measurable ρ := by fun_prop
  let A : ℕ → Measure (ℕ × (ℕ → S)) := fun n => Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)
  let C : ℕ → Measure (ℕ → T) := fun n => Measure.infinitePi fun _ : ℕ => γ n
  have hA : ∀ n, IsProbabilityMeasure (A n) := fun n => inferInstance
  have hC : ∀ n, IsProbabilityMeasure (C n) := fun n => inferInstance
  have hBm' : Measurable fun (ω : Ω) (i : ℕ) => B i ω := measurable_pi_iff.2 hBm
  have hjoint : P.map (fun ω n => ρ (B n ω)) = Measure.infinitePi fun n => (A n).prod (C n) := by
    have h1 := (iIndepFun_iff_map_fun_eq_infinitePi_map hBm).1 hB
    have h2 := Measure.infinitePi_map_pi (μ := fun n => P.map (B n)) (f := fun _ => ρ)
      (fun _ => hρ)
    have hcomp : P.map (fun ω n => ρ (B n ω)) =
        (P.map (fun ω i => B i ω)).map (fun x i => ρ (x i)) :=
      (Measure.map_map (g := fun x i => ρ (x i))
          (measurable_pi_iff.2 fun _ => hρ.comp (measurable_pi_apply _)) hBm').symm
    rw [hcomp, h1, h2]
    congr 1
    funext n
    rw [(hlaw n).map_eq, map_poissonBlock_split]
  let unzip : (ℕ → (ℕ × (ℕ → S)) × (ℕ → T)) → (ℕ → ℕ × (ℕ → S)) × (ℕ → ℕ → T) :=
    fun p => (fun n => (p n).1, fun n => (p n).2)
  have hunzip : Measurable unzip := by fun_prop
  have hρB : Measurable fun (ω : Ω) (n : ℕ) => ρ (B n ω) :=
    measurable_pi_iff.2 fun n => hρ.comp (hBm n)
  have hzm : Measurable fun p : (ℕ → ℕ × (ℕ → S)) × (ℕ → ℕ → T) =>
      fun n => (p.1 n, p.2 n) := by fun_prop
  have hz := Measure.infinitePi_prod_map_zip A C
  have hpair : P.map (fun ω => (fun n => (ρ (B n ω)).1, fun n => (ρ (B n ω)).2)) =
      (Measure.infinitePi A).prod (Measure.infinitePi C) := by
    have h : (fun ω => (fun n => (ρ (B n ω)).1, fun n => (ρ (B n ω)).2)) =
        unzip ∘ fun ω n => ρ (B n ω) := rfl
    rw [h, ← Measure.map_map hunzip hρB, hjoint, ← hz, Measure.map_map hunzip hzm]
    exact Measure.map_id' ▸ rfl
  have hZm : Measurable fun ω n => (ρ (B n ω)).1 := measurable_pi_iff.2 fun n =>
    measurable_fst.comp (hρ.comp (hBm n))
  have hGm : Measurable fun ω n => (ρ (B n ω)).2 := measurable_pi_iff.2 fun n =>
    measurable_snd.comp (hρ.comp (hBm n))
  have hZ : HasLaw (fun ω n => (ρ (B n ω)).1) (Measure.infinitePi A) P := by
    refine ⟨hZm.aemeasurable, ?_⟩
    have := congrArg (Measure.map Prod.fst) hpair
    rwa [Measure.map_map measurable_fst (hZm.prodMk hGm), Measure.map_fst_prod,
      measure_univ, one_smul] at this
  have hG : HasLaw (fun ω n => (ρ (B n ω)).2) (Measure.infinitePi C) P := by
    refine ⟨hGm.aemeasurable, ?_⟩
    have := congrArg (Measure.map Prod.snd) hpair
    rwa [Measure.map_map measurable_snd (hZm.prodMk hGm), Measure.map_snd_prod,
      measure_univ, one_smul] at this
  refine ⟨?_, hG, hZ⟩
  rw [indepFun_iff_map_prod_eq_prod_map_map hZm.aemeasurable hGm.aemeasurable, hpair,
    hZ.map_eq, hG.map_eq]

end SpinGlasses
