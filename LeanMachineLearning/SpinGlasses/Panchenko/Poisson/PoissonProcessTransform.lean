/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonProcess
public import LeanMachineLearning.ForMathlib.Probability.InfinitePiZip
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

/-- Mapping the intensity of independent blocks commutes with their countable sum. -/
theorem poissonIntensity_map {S T : Type*} [MeasurableSpace S]
    [MeasurableSpace T] (ν : ℕ → Measure S) (r : ℕ → ℝ≥0)
    {f : S → T} (hf : Measurable f) :
    (Measure.sum fun n => (r n : ℝ≥0∞) • ν n).map f =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).map f := by
  ext A hA
  simp [Measure.map_apply hf hA, Measure.sum_apply _ hA,
    Measure.sum_apply _ (hf hA), Measure.smul_apply]

/-- Forgetting the marks of a marked counting measure gives the counting measure of the
unmarked points. -/
theorem poissonCountingMeasure_map_fst {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (N : ℕ → ℕ) (X : ℕ → ℕ → S × T) :
    (poissonCountingMeasure N X).map Prod.fst =
      poissonCountingMeasure N (fun n l => (X n l).1) :=
  poissonCountingMeasure_map N X measurable_fst

/-- Applying a measurable map to every sample of independent Poisson blocks gives independent
Poisson blocks with the mapped sample laws. -/
theorem poissonBlocks_map {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [MeasurableSpace T] {P : Measure Ω} {ν : ℕ → Measure S} [∀ n, IsProbabilityMeasure (ν n)]
    {r : ℕ → ℝ≥0} {B : ℕ → Ω → ℕ × (ℕ → S)} (hBm : ∀ n, Measurable (B n))
    (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    {f : S → T} (hf : Measurable f) :
    (∀ n, Measurable fun ω => ((B n ω).1, fun l => f ((B n ω).2 l))) ∧
      iIndepFun (fun n ω => ((B n ω).1, fun l => f ((B n ω).2 l))) P ∧
      ∀ n, HasLaw (fun ω => ((B n ω).1, fun l => f ((B n ω).2 l)))
        (Po(r n).prod (Measure.infinitePi fun _ : ℕ => (ν n).map f)) P :=
  ⟨fun n => by have := hBm n; fun_prop,
    hB.comp (fun _ b => (b.1, fun l => f (b.2 l))) (fun _ => by fun_prop),
    fun n => hasLaw_map_prod_infinitePi (hlaw n) hf⟩

/-- If the image intensity `(∑ rₙ νₙ) ∘ f⁻¹` has no atoms, then every block of positive intensity
has an atomless image law. -/
theorem nullSingletonClass_map_block {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [MeasurableSingletonClass T]
    (ν : ℕ → Measure S) (r : ℕ → ℝ≥0) {f : S → T} (hf : Measurable f)
    (h : NullSingletonClass ((Measure.sum fun n => (r n : ℝ≥0∞) • ν n).map f)) {n : ℕ}
    (hn : r n ≠ 0) : NullSingletonClass ((ν n).map f) := by
  refine ⟨fun x => ?_⟩
  have hx := h.measure_singleton x
  rw [poissonIntensity_map ν r hf, Measure.sum_apply _ (measurableSet_singleton x)] at hx
  have := (ENNReal.tsum_eq_zero.1 hx) n
  simpa [hn] using this

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
  obtain ⟨hCm, hCi, hClaw⟩ := poissonBlocks_map hBm hB hlaw hf
  let C : ℕ → Ω → ℕ × (ℕ → T) := fun n ω => ((B n ω).1, fun l => f ((B n ω).2 l))
  have hM : ∀ ω, (poissonCountingMeasure (fun n => (B n ω).1)
      (fun n l => (B n ω).2 l)).map f =
      poissonCountingMeasure (fun n => (C n ω).1) (fun n l => (C n ω).2 l) := by
    intro ω
    exact poissonCountingMeasure_map _ _ hf
  obtain ⟨h, hind⟩ := iIndepFun_hasLaw_poissonCountingMeasure_apply
    (fun n => (ν n).map f) r hCm hCi hClaw rfl hM hA hdisj
  exact ⟨fun i => by simpa only [hfin i, ↓reduceIte] using h i, hind⟩

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
  obtain ⟨h, hind⟩ := iIndepFun_hasLaw_poissonCountingMeasure_apply v
    (fun k => r (Nat.pairEquiv.symm k).1 (Nat.pairEquiv.symm k).2)
    hCm hCi hClaw hμ hM hA hdisj
  exact ⟨fun i => by simpa only [hfin i, ↓reduceIte] using h i, hind⟩

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
  obtain ⟨h, hind⟩ := iIndepFun_hasLaw_poissonCountingMeasure_apply
    (fun n => ν n ⊗ₘ K) r hBm hB hlaw hμ (fun _ => rfl) hA hdisj
  exact ⟨fun i => by simpa only [hfin i, ↓reduceIte] using h i, hind⟩

/-- **Mapping theorem with simplicity.** If the image intensity has no atoms, then almost surely
the mapped counting measure counts the points of the image set `f(Π)` without multiplicity. -/
theorem ae_poissonProcess_map_eq_encard {Ω S T : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableEq T] {P : Measure Ω}
    [IsProbabilityMeasure P] (ν : ℕ → Measure S)
    [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → S)} (hBm : ∀ n, Measurable (B n))
    (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod
      (Measure.infinitePi fun _ : ℕ => ν n)) P)
    {f : S → T} (hf : Measurable f)
    (hnull : NullSingletonClass ((Measure.sum fun n => (r n : ℝ≥0∞) • ν n).map f)) :
    ∀ᵐ ω ∂P, ∀ A : Set T, MeasurableSet A →
      (poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l)).map f A =
        (A ∩ {y | ∃ n, ∃ l < (B n ω).1, f ((B n ω).2 l) = y}).encard := by
  have : ∀ n, IsProbabilityMeasure ((ν n).map f) := fun _ => inferInstance
  obtain ⟨hCm, hCi, hClaw⟩ := poissonBlocks_map hBm hB hlaw hf
  filter_upwards [ae_poissonCountingMeasure_eq_encard (fun n => (ν n).map f) r hCm hCi hClaw
    (fun n hn => nullSingletonClass_map_block ν r hf hnull hn)] with ω hω A hA
  rw [poissonCountingMeasure_map _ _ hf]
  exact hω A hA

/-- Marking an atomless law with a Markov kernel keeps it atomless. -/
theorem nullSingletonClass_compProd {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    [MeasurableSingletonClass S]
    (ν : Measure S) [SFinite ν] [NullSingletonClass ν] (K : Kernel S T) [IsMarkovKernel K] :
    NullSingletonClass (ν ⊗ₘ K) := by
  refine ⟨fun x => measure_mono_null (t := Prod.fst ⁻¹' {x.1}) ?_ ?_⟩
  · intro y hy
    simp only [Set.mem_singleton_iff] at hy
    simp [hy]
  · rw [← Measure.fst_apply (measurableSet_singleton x.1), Measure.fst_compProd]
    exact measure_singleton _

/-- **Marking theorem, construction.** Marked Poisson blocks with law `Po(rₙ) ⊗ (νₙ ⊗ₘ K)^{⊗ℕ}`
exist, and forgetting the marks gives unmarked blocks with law `Po(rₙ) ⊗ νₙ^{⊗ℕ}` on the same
probability space. Thus the marks of the Poisson process built from the unmarked blocks are
conditionally independent with laws `K (Xₙₗ, ·)`, as in Panchenko's marking construction. -/
theorem exists_markedPoissonBlocks {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    (ν : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0) (K : Kernel S T)
    [IsMarkovKernel K] :
    ∃ P : Measure (ℕ → ℕ × (ℕ → S × T)), IsProbabilityMeasure P ∧
      (∀ n, Measurable fun ω : ℕ → ℕ × (ℕ → S × T) => ω n) ∧
      iIndepFun (fun n (ω : ℕ → ℕ × (ℕ → S × T)) => ω n) P ∧
      (∀ n, HasLaw (fun ω : ℕ → ℕ × (ℕ → S × T) => ω n)
        (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n ⊗ₘ K)) P) ∧
      ∀ n, HasLaw (fun ω : ℕ → ℕ × (ℕ → S × T) => ((ω n).1, fun l => ((ω n).2 l).1))
        (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P := by
  obtain ⟨P, hP, hm, hi, hl⟩ := exists_poissonBlocks (fun n => ν n ⊗ₘ K) r
  refine ⟨P, hP, hm, hi, hl, fun n => ?_⟩
  have := hasLaw_map_prod_infinitePi (hl n) (f := Prod.fst) measurable_fst
  rwa [show (ν n ⊗ₘ K).map Prod.fst = ν n from Measure.fst_compProd _ _] at this

/-- **Marking with simplicity.** If the unmarked block laws of positive intensity have no atoms,
almost surely the marked counting measure counts the points of the marked set `Π*` without
multiplicity. -/
theorem ae_poissonProcess_marking_eq_encard {Ω S T : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableEq (S × T)]
    [MeasurableSingletonClass S] {P : Measure Ω} [IsProbabilityMeasure P] (ν : ℕ → Measure S)
    [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0) (K : Kernel S T) [IsMarkovKernel K]
    {B : ℕ → Ω → ℕ × (ℕ → S × T)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ => (ν n) ⊗ₘ K)) P)
    (hnull : ∀ n, r n ≠ 0 → NullSingletonClass (ν n)) :
    ∀ᵐ ω ∂P, ∀ A : Set (S × T), MeasurableSet A →
      poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l) A =
        (A ∩ {x | ∃ n, ∃ l < (B n ω).1, (B n ω).2 l = x}).encard :=
  ae_poissonCountingMeasure_eq_encard (fun n => ν n ⊗ₘ K) r hBm hB hlaw fun n hn =>
    have := hnull n hn
    nullSingletonClass_compProd (ν n) K

/-- **Superposition with simplicity.** For atomless positive-rate block laws, the sum of
independent process measures counts points of the union without multiplicity, almost surely. -/
theorem ae_poissonProcess_superposition_eq_encard {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableEq S] {P : Measure Ω} [IsProbabilityMeasure P]
    (ν : ℕ → ℕ → Measure S) [∀ m n, IsProbabilityMeasure (ν m n)]
    (r : ℕ → ℕ → ℝ≥0) {B : ℕ → ℕ → Ω → ℕ × (ℕ → S)}
    (hBm : ∀ m n, Measurable (B m n))
    (houter : iIndepFun (fun m ω => fun n => B m n ω) P)
    (hinner : ∀ m, iIndepFun (B m) P)
    (hlaw : ∀ m n, HasLaw (B m n)
      (Po(r m n).prod (Measure.infinitePi fun _ : ℕ => ν m n)) P)
    (hnull : ∀ m n, r m n ≠ 0 → NullSingletonClass (ν m n)) :
    ∀ᵐ ω ∂P, ∀ A : Set S, MeasurableSet A →
      (Measure.sum fun m => poissonCountingMeasure (fun n => (B m n ω).1)
        (fun n l => (B m n ω).2 l)) A =
        (A ∩ {x | ∃ m n, ∃ l < (B m n ω).1, (B m n ω).2 l = x}).encard := by
  let C : ℕ → Ω → ℕ × (ℕ → S) := fun k ω =>
    B (Nat.pairEquiv.symm k).1 (Nat.pairEquiv.symm k).2 ω
  have hCm : ∀ k, Measurable (C k) := fun k => hBm _ _
  have hCi : iIndepFun C P :=
    (iIndepFun_uncurry' hBm houter hinner).precomp
      (g := Nat.pairEquiv.symm) Nat.pairEquiv.symm.injective
  have hClaw : ∀ k, HasLaw (C k)
      (Po(r (Nat.pairEquiv.symm k).1 (Nat.pairEquiv.symm k).2).prod
        (Measure.infinitePi fun _ : ℕ =>
          ν (Nat.pairEquiv.symm k).1 (Nat.pairEquiv.symm k).2)) P :=
    fun k => hlaw _ _
  have hCnull : ∀ k, r (Nat.pairEquiv.symm k).1 (Nat.pairEquiv.symm k).2 ≠ 0 →
      NullSingletonClass (ν (Nat.pairEquiv.symm k).1 (Nat.pairEquiv.symm k).2) :=
    fun k => hnull _ _
  filter_upwards [ae_poissonCountingMeasure_eq_encard
    (fun k => ν (Nat.pairEquiv.symm k).1 (Nat.pairEquiv.symm k).2)
    (fun k => r (Nat.pairEquiv.symm k).1 (Nat.pairEquiv.symm k).2)
    hCm hCi hClaw hCnull] with ω hω A hA
  rw [poissonCountingMeasure_superposition]
  rw [hω A hA]
  have hset : (A ∩ {x | ∃ k, ∃ l < (C k ω).1, (C k ω).2 l = x}) =
      (A ∩ {x | ∃ m n, ∃ l < (B m n ω).1, (B m n ω).2 l = x}) := by
    ext x
    simp only [Set.mem_inter_iff]
    constructor
    · rintro ⟨hx, k, l, hl, heq⟩
      exact ⟨hx, (Nat.pairEquiv.symm k).1, (Nat.pairEquiv.symm k).2, l, hl, heq⟩
    · rintro ⟨hx, m, n, l, hl, heq⟩
      exact ⟨hx, Nat.pairEquiv (m, n), l, by simpa [C] using hl,
        by simpa [C] using heq⟩
  exact congrArg (fun s : Set S => (s.encard : ℝ≥0∞)) hset

/-- **Marking a given family of blocks by independent marks.** Given independent Poisson blocks
`B n` on `(Ω, P)`, enlarge the space to `Ω × (ℕ → ℕ → T)` with the product measure `P ⊗ τ^{⊗ℕ×ℕ}`
and attach to the `l`-th point of block `n` the mark `q.2 n l`. The marked blocks `C n` are
measurable, independent, have law `Po(rₙ) ⊗ (νₙ ⊗ τ)^{⊗ℕ}`, and forget back to `B n` pointwise.
This is the case of marking used in the book's Theorem 2.6, where the marks are independent of
the positions and of the process; the position-dependent case is `poissonProcess_marking`. -/
theorem iIndepFun_hasLaw_indepMarkedBlocks {Ω S T : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSpace T] {P : Measure Ω} [IsProbabilityMeasure P]
    (ν : ℕ → Measure S) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    (τ : Measure T) [IsProbabilityMeasure τ] {B : ℕ → Ω → ℕ × (ℕ → S)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    {C : ℕ → Ω × (ℕ → ℕ → T) → ℕ × (ℕ → S × T)}
    (hC : ∀ n q, C n q = ((B n q.1).1, fun l => ((B n q.1).2 l, q.2 n l))) :
    (∀ n, Measurable (C n)) ∧
      iIndepFun C (P.prod (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => τ)) ∧
      (∀ n, HasLaw (C n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => (ν n).prod τ))
        (P.prod (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => τ))) ∧
      ∀ n q, ((C n q).1, fun l => ((C n q).2 l).1) = B n q.1 := by
  set W : Measure (ℕ → ℕ → T) := Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => τ
  have hΘm : Measurable fun z : (ℕ × (ℕ → S)) × (ℕ → T) =>
      (z.1.1, fun l => (z.1.2 l, z.2 l)) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun l =>
      (((measurable_pi_apply l).comp (measurable_snd.comp measurable_fst))).prodMk
        ((measurable_pi_apply l).comp measurable_snd))
  have hE : ∀ n, Measurable fun q : Ω × (ℕ → ℕ → T) => (B n q.1, q.2 n) := fun n =>
    ((hBm n).comp measurable_fst).prodMk ((measurable_pi_apply n).comp measurable_snd)
  have hCE : ∀ n, C n = (fun z : (ℕ × (ℕ → S)) × (ℕ → T) =>
      (z.1.1, fun l => (z.1.2 l, z.2 l))) ∘ fun q => (B n q.1, q.2 n) := fun n => by
    ext q <;> simp [hC]
  have hCm : ∀ n, Measurable (C n) := fun n => by rw [hCE n]; exact hΘm.comp (hE n)
  -- the law of the pair (block, marks) of index `n`
  have hlawE : ∀ n, HasLaw (fun q : Ω × (ℕ → ℕ → T) => (B n q.1, q.2 n))
      ((Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)).prod
        (Measure.infinitePi fun _ : ℕ => τ)) (P.prod W) := fun n =>
    ⟨(hE n).aemeasurable, by
      rw [show (fun q : Ω × (ℕ → ℕ → T) => (B n q.1, q.2 n)) =
        Prod.map (B n) (fun w : ℕ → ℕ → T => w n) from rfl,
        ← Measure.map_prod_map _ _ (hBm n) (measurable_pi_apply n), (hlaw n).map_eq,
        Measure.infinitePi_map_eval]⟩
  -- independence of the pairs, from the law of the whole vector
  have hvec : HasLaw (fun q : Ω × (ℕ → ℕ → T) => fun n => (B n q.1, q.2 n))
      (Measure.infinitePi fun n => (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)).prod
        (Measure.infinitePi fun _ : ℕ => τ)) (P.prod W) := by
    refine ⟨measurable_pi_iff.2 (fun n => hE n) |>.aemeasurable, ?_⟩
    have hBv : Measurable fun ω n => B n ω := measurable_pi_iff.2 hBm
    have hzip : Measurable fun p : (ℕ → ℕ × (ℕ → S)) × (ℕ → ℕ → T) => fun n => (p.1 n, p.2 n) :=
      measurable_pi_iff.2 fun n => ((measurable_pi_apply n).comp measurable_fst).prodMk
        ((measurable_pi_apply n).comp measurable_snd)
    have h1 : (fun q : Ω × (ℕ → ℕ → T) => fun n => (B n q.1, q.2 n)) =
        (fun p : (ℕ → ℕ × (ℕ → S)) × (ℕ → ℕ → T) => fun n => (p.1 n, p.2 n)) ∘
          Prod.map (fun ω n => B n ω) id := rfl
    have hP : P.map (fun ω n => B n ω) = Measure.infinitePi fun n =>
        Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n) :=
      (hB.hasLaw_infinitePi hlaw hBv.aemeasurable).map_eq
    rw [h1, ← Measure.map_map hzip (hBv.prodMap measurable_id),
      ← Measure.map_prod_map _ _ hBv measurable_id, Measure.map_id, hP,
      Measure.infinitePi_prod_map_zip]
  have hEi : iIndepFun (fun n (q : Ω × (ℕ → ℕ → T)) => (B n q.1, q.2 n)) (P.prod W) :=
    (iIndepFun_iff_hasLaw_Pi_infinitePi hlawE hvec.aemeasurable).2 hvec
  refine ⟨hCm, ?_, fun n => ?_, fun n q => by rw [hC]⟩
  · rw [show C = fun n => (fun z : (ℕ × (ℕ → S)) × (ℕ → T) =>
      (z.1.1, fun l => (z.1.2 l, z.2 l))) ∘ fun q => (B n q.1, q.2 n) from funext hCE]
    exact hEi.comp (fun _ z => (z.1.1, fun l => (z.1.2 l, z.2 l))) fun _ => hΘm
  · have hΘ : ((Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)).prod
        (Measure.infinitePi fun _ : ℕ => τ)).map (fun z : (ℕ × (ℕ → S)) × (ℕ → T) =>
        (z.1.1, fun l => (z.1.2 l, z.2 l))) =
        Po(r n).prod (Measure.infinitePi fun _ : ℕ => (ν n).prod τ) := by
      have hz : Measurable fun p : (ℕ → S) × (ℕ → T) => fun l => (p.1 l, p.2 l) :=
        measurable_pi_iff.2 fun l => ((measurable_pi_apply l).comp measurable_fst).prodMk
          ((measurable_pi_apply l).comp measurable_snd)
      rw [show (fun z : (ℕ × (ℕ → S)) × (ℕ → T) => (z.1.1, fun l => (z.1.2 l, z.2 l))) =
        Prod.map id (fun p : (ℕ → S) × (ℕ → T) => fun l => (p.1 l, p.2 l)) ∘
          MeasurableEquiv.prodAssoc from rfl,
        ← Measure.map_map (measurable_id.prodMap hz) MeasurableEquiv.prodAssoc.measurable,
        (measurePreserving_prodAssoc _ _ _).map_eq,
        ← Measure.map_prod_map _ _ measurable_id hz, Measure.map_id,
        Measure.infinitePi_prod_map_zip]
    rw [hCE n]
    exact (⟨hΘm.aemeasurable, hΘ⟩ : HasLaw _ _ _).comp (hlawE n)

end SpinGlasses
