/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonProcess
public import Mathlib.Probability.Kernel.Basic

/-!
# Transformations of Poisson counting measures

Mapping acts pointwise on every Dirac mass. Superposition concatenates independent families of
Poisson blocks. For marking, a block of marked points has the product law of a Poisson horizon
and iid samples from the kernel-coupled measure.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpinGlasses

/-- Mapping every point of a counting measure commutes with its block construction.
This deterministic statement does not require the image intensity to be nonatomic: coincident
images are retained with their multiplicity. -/
theorem poissonCountingMeasure_map {S T : Type*} [MeasurableSpace S]
    [MeasurableSpace T] (N : ℕ → ℕ) (X : ℕ → ℕ → S) {f : S → T}
    (hf : Measurable f) :
    (poissonCountingMeasure N X).map f = poissonCountingMeasure N (fun n l => f (X n l)) := by
  ext A hA
  rw [Measure.map_apply hf hA, poissonCountingMeasure_apply _ _ (hf hA),
    poissonCountingMeasure_apply _ _ hA]
  refine tsum_congr fun n => Finset.sum_congr rfl fun l _ => ?_
  simp only [Set.indicator, Set.mem_preimage, Pi.one_apply]
  rfl

/-- The law of a mapped Poisson block is obtained by mapping its iid sample law. -/
theorem hasLaw_map_poissonBlock {Ω S T : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSpace T] {P : Measure Ω}
    {r : ℝ≥0} {ν : Measure S} [IsProbabilityMeasure ν]
    {B : Ω → ℕ × (ℕ → S)} (hB : HasLaw B (Po(r).prod
      (Measure.infinitePi fun _ : ℕ => ν)) P) {f : S → T} (hf : Measurable f) :
    HasLaw (fun ω => ((B ω).1, fun l => f ((B ω).2 l)))
      (Po(r).prod (Measure.infinitePi fun _ : ℕ => ν.map f)) P := by
  have hm : Measurable (fun b : ℕ × (ℕ → S) =>
      (b.1, fun l => f (b.2 l))) := by fun_prop
  have hmap : (Po(r).prod (Measure.infinitePi fun _ : ℕ => ν)).map
      (fun b : ℕ × (ℕ → S) => (b.1, fun l => f (b.2 l))) =
      Po(r).prod (Measure.infinitePi fun _ : ℕ => ν.map f) := by
    rw [show (fun b : ℕ × (ℕ → S) => (b.1, fun l => f (b.2 l))) =
      Prod.map id (fun x => fun l => f (x l)) from rfl,
      ← Measure.map_prod_map _ _ measurable_id (by fun_prop :
        Measurable fun x : ℕ → S => fun l => f (x l))]
    simp only [Measure.map_id]
    exact congrArg (Measure.prod (Po(r)))
      (Measure.infinitePi_map_pi (μ := fun _ : ℕ => ν) (fun _ => hf))
  exact ⟨hm.aemeasurable.comp_aemeasurable hB.aemeasurable, by
    rw [← hmap, ← hB.map_eq,
      AEMeasurable.map_map_of_aemeasurable hm.aemeasurable hB.aemeasurable]
    rfl⟩

/-- **Mapping theorem (Panchenko, Theorem 2.1), in the finite-dimensional count-law form.**
The mapped counting measure has independent Poisson counts on disjoint measurable sets of finite
image intensity. No atomlessness assumption is needed when points are counted with multiplicity;
if one wants a *set* of points instead, atomlessness gives simplicity separately. -/
theorem poissonProcess_map {Ω S T κ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSpace T] {P : Measure Ω}
    [IsProbabilityMeasure P] [Finite κ] (ν : ℕ → Measure S)
    [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → S)} (hBm : ∀ n, Measurable (B n))
    (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod
      (Measure.infinitePi fun _ : ℕ => ν n)) P)
    {f : S → T} (hf : Measurable f)
    {A : κ → Set T} (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (hfin : ∀ i, (Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).map f) (A i) ≠ ∞) :
    (∀ i, HasLaw (fun ω =>
        (poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l)).map f (A i))
        (Po(((Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).map f) (A i)).toNNReal).map
          (Nat.cast : ℕ → ℝ≥0∞)) P) ∧
      iIndepFun (fun i ω =>
        (poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l)).map f
          (A i)) P := by
  have : ∀ n, IsProbabilityMeasure ((ν n).map f) := fun _ => inferInstance
  let C : ℕ → Ω → ℕ × (ℕ → T) := fun n ω =>
    ((B n ω).1, fun l => f ((B n ω).2 l))
  have hCm : ∀ n, Measurable (C n) := fun n => by
    dsimp [C]
    fun_prop
  have hCi : iIndepFun C P :=
    hB.comp (fun _ b => (b.1, fun l => f (b.2 l))) (fun _ => by fun_prop)
  have hClaw : ∀ n, HasLaw (C n) (Po(r n).prod
      (Measure.infinitePi fun _ : ℕ => (ν n).map f)) P := fun n =>
    hasLaw_map_poissonBlock (hlaw n) hf
  have hM : ∀ ω, (poissonCountingMeasure (fun n => (B n ω).1)
      (fun n l => (B n ω).2 l)).map f =
      poissonCountingMeasure (fun n => (C n ω).1) (fun n l => (C n ω).2 l) := by
    intro ω
    exact poissonCountingMeasure_map _ _ hf
  exact iIndepFun_hasLaw_poissonCountingMeasure_apply
    (fun n => (ν n).map f) r hCm hCi hClaw rfl hM hA hdisj hfin

/-- Superposing countably many block configurations is itself a block configuration, after
pairing the two countable indices. This identity needs no probabilistic hypotheses. -/
theorem poissonCountingMeasure_superposition {S : Type*} [MeasurableSpace S]
    (N : ℕ → ℕ → ℕ) (X : ℕ → ℕ → ℕ → S) :
    (Measure.sum fun m => poissonCountingMeasure (N m) (X m)) =
      poissonCountingMeasure (fun k => N (Nat.pairEquiv.symm k).1
        (Nat.pairEquiv.symm k).2)
        (fun k l => X (Nat.pairEquiv.symm k).1 (Nat.pairEquiv.symm k).2 l) := by
  simp only [poissonCountingMeasure, Measure.sum_sum]
  exact (Measure.sum_comp_equiv Nat.pairEquiv.symm
    (fun p : ℕ × ℕ => ∑ l ∈ Finset.range (N p.1 p.2), Measure.dirac (X p.1 p.2 l))).symm

/-- **Superposition theorem (Panchenko, Theorem 2.2), for independent Poisson blocks.**
The outer families of blocks are assumed independent, as are the blocks within each family.
Then the sum of the counting measures has independent Poisson counts with the sum intensity. -/
theorem poissonProcess_superposition {Ω S κ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] {P : Measure Ω} [IsProbabilityMeasure P]
    [Finite κ] (ν : ℕ → ℕ → Measure S)
    [∀ m n, IsProbabilityMeasure (ν m n)] (r : ℕ → ℕ → ℝ≥0)
    {B : ℕ → ℕ → Ω → ℕ × (ℕ → S)}
    (hBm : ∀ m n, Measurable (B m n))
    (houter : iIndepFun (fun m ω => fun n => B m n ω) P)
    (hinner : ∀ m, iIndepFun (B m) P)
    (hlaw : ∀ m n, HasLaw (B m n)
      (Po(r m n).prod (Measure.infinitePi fun _ : ℕ => ν m n)) P)
    {A : κ → Set S} (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (hfin : ∀ i, (Measure.sum fun m => Measure.sum fun n =>
      (r m n : ℝ≥0∞) • ν m n) (A i) ≠ ∞) :
    (∀ i, HasLaw (fun ω =>
        (Measure.sum fun m => poissonCountingMeasure (fun n => (B m n ω).1)
          (fun n l => (B m n ω).2 l)) (A i))
        (Po(((Measure.sum fun m => Measure.sum fun n =>
          (r m n : ℝ≥0∞) • ν m n) (A i)).toNNReal).map
          (Nat.cast : ℕ → ℝ≥0∞)) P) ∧
      iIndepFun (fun i ω =>
        (Measure.sum fun m => poissonCountingMeasure (fun n => (B m n ω).1)
          (fun n l => (B m n ω).2 l)) (A i)) P := by
  let C : ℕ → Ω → ℕ × (ℕ → S) := fun k ω =>
    B (Nat.pairEquiv.symm k).1 (Nat.pairEquiv.symm k).2 ω
  have hCm : ∀ k, Measurable (C k) := fun k => hBm _ _
  have hpair : iIndepFun (fun p : ℕ × ℕ => B p.1 p.2) P :=
    iIndepFun_uncurry' hBm houter hinner
  have hCi : iIndepFun C P :=
    hpair.precomp (g := Nat.pairEquiv.symm) Nat.pairEquiv.symm.injective
  have hClaw : ∀ k, HasLaw (C k) (Po(r (Nat.pairEquiv.symm k).1
      (Nat.pairEquiv.symm k).2).prod
      (Measure.infinitePi fun _ : ℕ => ν (Nat.pairEquiv.symm k).1
        (Nat.pairEquiv.symm k).2)) P := fun k => hlaw _ _
  have hM : ∀ ω, (Measure.sum fun m => poissonCountingMeasure
      (fun n => (B m n ω).1) (fun n l => (B m n ω).2 l)) =
      poissonCountingMeasure (fun k => (C k ω).1) (fun k l => (C k ω).2 l) :=
    fun ω => poissonCountingMeasure_superposition _ _
  let v : ℕ → Measure S := fun k => ν (Nat.pairEquiv.symm k).1
    (Nat.pairEquiv.symm k).2
  have hv : ∀ k, IsProbabilityMeasure (v k) := fun _ => inferInstance
  have hμ : (Measure.sum fun m => Measure.sum fun n => (r m n : ℝ≥0∞) • ν m n) =
      Measure.sum fun k => (r (Nat.pairEquiv.symm k).1
        (Nat.pairEquiv.symm k).2 : ℝ≥0∞) • v k := by
    rw [Measure.sum_sum]
    exact (Measure.sum_comp_equiv Nat.pairEquiv.symm
      (fun p : ℕ × ℕ => (r p.1 p.2 : ℝ≥0∞) • ν p.1 p.2)).symm
  exact iIndepFun_hasLaw_poissonCountingMeasure_apply v
    (fun k => r (Nat.pairEquiv.symm k).1 (Nat.pairEquiv.symm k).2)
    hCm hCi hClaw hμ hM hA hdisj hfin

/-- **Marking theorem (Panchenko, Theorem 2.3), in block-law form.** Each block has a Poisson
horizon and iid marked pairs with law `νₙ ⊗ₘ K`. In particular this allows a position-dependent
mark kernel, not merely an independent common mark distribution. The marked counting measure has
independent Poisson counts with intensity `(∑ₙ rₙ νₙ) ⊗ₘ K`. -/
theorem poissonProcess_marking {Ω S T κ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSpace T] {P : Measure Ω}
    [IsProbabilityMeasure P] [Finite κ] (ν : ℕ → Measure S)
    [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    (K : Kernel S T) [IsMarkovKernel K]
    {B : ℕ → Ω → ℕ × (ℕ → S × T)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => (ν n) ⊗ₘ K)) P)
    {A : κ → Set (S × T)} (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (hfin : ∀ i, ((Measure.sum fun n => (r n : ℝ≥0∞) • ν n) ⊗ₘ K) (A i) ≠ ∞) :
    (∀ i, HasLaw (fun ω => poissonCountingMeasure
        (fun n => (B n ω).1) (fun n l => (B n ω).2 l) (A i))
        (Po(((((Measure.sum fun n => (r n : ℝ≥0∞) • ν n) ⊗ₘ K)
          (A i)).toNNReal)).map (Nat.cast : ℕ → ℝ≥0∞)) P) ∧
      iIndepFun (fun i ω => poissonCountingMeasure
        (fun n => (B n ω).1) (fun n l => (B n ω).2 l) (A i)) P := by
  have hμ : (Measure.sum fun n => (r n : ℝ≥0∞) • ν n) ⊗ₘ K =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n ⊗ₘ K) := by
    rw [Measure.compProd_sum_left]
    congr 1
    funext n
    exact Measure.compProd_smul_left _
  exact iIndepFun_hasLaw_poissonCountingMeasure_apply
    (fun n => ν n ⊗ₘ K) r hBm hB hlaw hμ
    (fun _ => rfl) hA hdisj hfin

/-- Mapping the intensity of independent blocks commutes with their countable sum. -/
theorem poissonIntensity_map {S T : Type*} [MeasurableSpace S]
    [MeasurableSpace T] (ν : ℕ → Measure S) (r : ℕ → ℝ≥0)
    {f : S → T} (hf : Measurable f) :
    (Measure.sum fun n => (r n : ℝ≥0∞) • ν n).map f =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).map f := by
  ext A hA
  simp [Measure.map_apply hf hA, Measure.sum_apply _ hA,
    Measure.sum_apply _ (hf hA), Measure.smul_apply]

end SpinGlasses
