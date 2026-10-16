/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Distributions.Poisson.Thinning
public import LeanMachineLearning.ForMathlib.Probability.Distributions.Poisson.SumCountable
public import LeanMachineLearning.ForMathlib.Probability.Independence.Nonatomic
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Counting measures built from Poisson blocks

Each block has a Poisson number of sampled points. The point configuration is represented by
its counting measure, so overlapping atoms are counted with multiplicity until simplicity is proved.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

variable {S : Type*} [MeasurableSpace S]

/-- The counting measure of the first `N n` points of each block. This definition is deterministic:
probability is imposed by a law on the block coordinates. -/
noncomputable def poissonCountingMeasure (N : ℕ → ℕ) (X : ℕ → ℕ → S) : Measure S :=
  Measure.sum fun n => ∑ l ∈ Finset.range (N n), Measure.dirac (X n l)

/-- The counting measure is measurable as a function of all the block coordinates, for the
Giry measurable structure on measures. -/
theorem measurable_poissonCountingMeasure :
    Measurable fun q : (n : ℕ) → ℕ × (ℕ → S) =>
      poissonCountingMeasure (fun n => (q n).1) (fun n l => (q n).2 l) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [poissonCountingMeasure, Measure.sum_apply _ hs]
  apply Measurable.tsum
  intro n
  have hblock : Measurable fun q : ℕ × (ℕ → S) =>
      (∑ l ∈ Finset.range q.1, Measure.dirac (q.2 l)) s := by
    apply measurable_from_prod_countable_right
    intro k
    change Measurable fun y : ℕ → S =>
      (∑ l ∈ Finset.range k, Measure.dirac (y l)) s
    rw [show (fun y : ℕ → S => (∑ l ∈ Finset.range k, Measure.dirac (y l)) s) =
      (fun y => ∑ l ∈ Finset.range k, (Measure.dirac (y l)) s) by
        funext y; simp only [Measure.coe_finsetSum, Finset.sum_apply]]
    exact Finset.measurable_sum _ fun l _ =>
      ((Measure.measurable_coe hs).comp Measure.measurable_dirac).comp
        (measurable_pi_apply l)
  exact hblock.comp (measurable_pi_apply n)

/-- Evaluation of the counting measure on a measurable set is the sum of the numbers of
sampled points in that set, counted with multiplicity. -/
theorem poissonCountingMeasure_apply (N : ℕ → ℕ) (X : ℕ → ℕ → S)
    {A : Set S} (hA : MeasurableSet A) :
    poissonCountingMeasure N X A =
      ∑' n, ∑ l ∈ Finset.range (N n), (Measure.dirac (X n l)) A := by
  simp only [poissonCountingMeasure, Measure.sum_apply _ hA, Measure.coe_finsetSum,
    Finset.sum_apply]

/-- The canonical probability law of independent Poisson blocks with independent iid samples.
The input probability measures are kept explicit, allowing arbitrary finite-intensity blocks. -/
noncomputable def poissonBlockLaw (r : ℕ → NNReal) (ν : ℕ → Measure S) :
    Measure (ℕ → (ℕ × (ℕ → S))) :=
  Measure.infinitePi fun n => Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)

/-- Independent block coordinates in the canonical product probability space. -/
theorem iIndepFun_poissonBlocks (r : ℕ → NNReal) (ν : ℕ → Measure S)
    [∀ n : ℕ, IsProbabilityMeasure (ν n)] :
    iIndepFun (fun n (q : ℕ → ℕ × (ℕ → S)) => q n) (poissonBlockLaw r ν) := by
  unfold poissonBlockLaw
  exact iIndepFun_infinitePi
    (P := fun n => Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n))
    (X := fun _ x => x) fun _ => measurable_id

/-- The number of samples in each block has its prescribed Poisson law. -/
theorem hasLaw_poissonBlockCount (r : ℕ → NNReal) (ν : ℕ → Measure S)
    [∀ n : ℕ, IsProbabilityMeasure (ν n)] (n : ℕ) :
    HasLaw (fun q : ℕ → ℕ × (ℕ → S) => (q n).1) Po(r n)
      (poissonBlockLaw r ν) := by
  exact (measurePreserving_fst).hasLaw.comp
    (hasLaw_eval_infinitePi
      (fun n => Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) n)

/-- The sample sequence in a fixed block has its prescribed iid product law. -/
theorem hasLaw_poissonBlockSamples (r : ℕ → NNReal) (ν : ℕ → Measure S)
    [∀ n : ℕ, IsProbabilityMeasure (ν n)] (n : ℕ) :
    HasLaw (fun q : ℕ → ℕ × (ℕ → S) => (q n).2)
      (Measure.infinitePi fun _ : ℕ => ν n) (poissonBlockLaw r ν) := by
  exact measurePreserving_snd.hasLaw.comp
    (hasLaw_eval_infinitePi
      (fun n => Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) n)

/-- Within a block, the Poisson horizon is independent of the entire sample sequence. -/
theorem indepFun_poissonBlockCount_samples (r : ℕ → NNReal) (ν : ℕ → Measure S)
    [∀ n : ℕ, IsProbabilityMeasure (ν n)] (n : ℕ) :
    IndepFun (fun q : ℕ → ℕ × (ℕ → S) => (q n).1)
      (fun q : ℕ → ℕ × (ℕ → S) => (q n).2) (poissonBlockLaw r ν) := by
  have h : IndepFun (fun q : ℕ × (ℕ → S) => q.1) (fun q => q.2)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) := by
    exact indepFun_prod (X := id) (Y := id) measurable_id measurable_id
  have hpair : HasLaw (fun q : ℕ → ℕ × (ℕ → S) => q n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) (poissonBlockLaw r ν) :=
    hasLaw_eval_infinitePi
      (fun n => Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) n
  have : IsProbabilityMeasure (poissonBlockLaw r ν) := by
    unfold poissonBlockLaw
    infer_instance
  have hf : Measurable fun q : ℕ → ℕ × (ℕ → S) => (q n).1 :=
    measurable_fst.comp (measurable_pi_apply n)
  have hg : Measurable fun q : ℕ → ℕ × (ℕ → S) => (q n).2 :=
    measurable_snd.comp (measurable_pi_apply n)
  apply (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).2
  have heq : (fun q : ℕ → ℕ × (ℕ → S) => ((q n).1, (q n).2)) =
      (fun q : ℕ × (ℕ → S) => (q.1, q.2)) ∘ (fun q => q n) := rfl
  rw [heq, ← Measure.map_map
    (by fun_prop : Measurable (fun q : ℕ × (ℕ → S) => (q.1, q.2)))
    (measurable_pi_apply n), hpair.map_eq]
  rw [show (fun q : ℕ → ℕ × (ℕ → S) => (q n).1) =
    Prod.fst ∘ (fun q => q n) from rfl,
    show (fun q : ℕ → ℕ × (ℕ → S) => (q n).2) =
    Prod.snd ∘ (fun q => q n) from rfl]
  rw [← Measure.map_map measurable_fst (measurable_pi_apply n),
    ← Measure.map_map measurable_snd (measurable_pi_apply n),
    hpair.map_eq]
  exact (indepFun_iff_map_prod_eq_prod_map_map
    measurable_fst.aemeasurable measurable_snd.aemeasurable).1 h

/-- Iid point samples within each block under the canonical law. -/
theorem iIndepFun_poissonBlockSamples (r : ℕ → NNReal) (ν : ℕ → Measure S)
    [∀ n : ℕ, IsProbabilityMeasure (ν n)] (n : ℕ) :
    iIndepFun (fun l (q : ℕ → ℕ × (ℕ → S)) => (q n).2 l)
      (poissonBlockLaw r ν) := by
  have h : iIndepFun (fun l (x : ℕ → S) => x l) (Measure.infinitePi fun _ : ℕ => ν n) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => ν n) (X := fun _ x => x)
      fun _ => measurable_id
  have heval : HasLaw (fun q : ℕ → ℕ × (ℕ → S) => (q n).2)
      (Measure.infinitePi fun _ : ℕ => ν n) (poissonBlockLaw r ν) :=
    hasLaw_poissonBlockSamples r ν n
  have : IsProbabilityMeasure (poissonBlockLaw r ν) := by
    unfold poissonBlockLaw
    infer_instance
  have hmeas (l : ℕ) : Measurable fun q : ℕ → ℕ × (ℕ → S) => (q n).2 l :=
    (measurable_pi_apply l).comp (measurable_snd.comp (measurable_pi_apply n))
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map₀'
    (fun l => (hmeas l).aemeasurable)).2
  have hmap : (poissonBlockLaw r ν).map
      (fun q : ℕ → ℕ × (ℕ → S) => fun l => (q n).2 l) =
      Measure.infinitePi fun _ : ℕ => ν n := by
    have hid : (fun q : ℕ → ℕ × (ℕ → S) => fun l => (q n).2 l) =
        id ∘ (fun q => (q n).2) := rfl
    simpa only [Function.id_comp] using heval.map_eq
  rw [hmap]
  congr 1
  funext l
  exact (hasLaw_eval_infinitePi (fun _ : ℕ => ν n) l).comp heval |>.map_eq.symm

/-- Each point sample in a block has the prescribed marginal law. -/
theorem hasLaw_poissonBlockPoint (r : ℕ → NNReal) (ν : ℕ → Measure S)
    [∀ n : ℕ, IsProbabilityMeasure (ν n)] (n l : ℕ) :
    HasLaw (fun q : ℕ → ℕ × (ℕ → S) => (q n).2 l) (ν n)
      (poissonBlockLaw r ν) :=
  (hasLaw_eval_infinitePi (fun _ : ℕ => ν n) l).comp
    (hasLaw_poissonBlockSamples r ν n)

end SpinGlasses
