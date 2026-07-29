/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Joint cumulants and connected correlators

Joint cumulants are defined by the Möbius transform of block moments.  The finite-partition layer
therefore contains all combinatorial coefficients, while this file only supplies probability and
integrability hypotheses.

Deferred proof references:

* G.-C. Rota, Möbius inversion: <https://doi.org/10.1007/BF00531932>.
* Mathlib's analytic MGF theorem:
  <https://github.com/leanprover-community/mathlib4/blob/abb22825db7e020c94f38a007ae3fffe6c3a7532/Mathlib/Probability/Moments/MGFAnalytic.lean>.

Each deferred theorem includes an informal proof specialized to its statement.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace Renormalization

variable {Ω ι κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The cumulant associated with a block of positions.  The Möbius transform makes sense for an
arbitrary measure; probability normalization is imposed only by the theorems that need it. -/
def blockCumulant [DecidableEq ι] (μ : Measure Ω)
    (X : ι → Ω → ℝ) (B : Finset ι) : ℝ :=
  Finpartition.cumulantTransform (blockMoment μ X) B

/-- The joint cumulant, or connected correlator, of a finite family of observables. -/
def jointCumulant [Fintype ι] [DecidableEq ι] (μ : Measure Ω) (X : ι → Ω → ℝ) : ℝ :=
  blockCumulant μ X Finset.univ

/-- The zeroth joint cumulant is zero.

Informal proof: `jointCumulant` evaluates `cumulantTransform` on the empty set, where its defining
convention is zero. -/
@[simp]
theorem jointCumulant_zero (X : Fin 0 → Ω → ℝ) :
    jointCumulant μ X = 0 := by
  simp [jointCumulant, blockCumulant, Finpartition.cumulantTransform]

/-- A block cumulant is the joint cumulant of the family restricted to that block.

Informal proof: reindex subsets of `B` by the equivalence between finsets of the subtype `B` and
subsets of `B`, then apply `Finpartition.cumulantTransform_map`.
A Finpartition of `B : Finset ι` is equivalent to a Finpartition of `Finset.univ : Finset B`.
Informal proof: The parts of the partition are subsets of `B`. Subsets of `B` correspond bijectively
to subsets of `Finset.univ` in the subtype `B`. -/
lemma cumulantTransform_subtype [DecidableEq ι] (B : Finset ι) {R : Type*} [CommRing R]
    (f : Finset ι → R) :
    Finpartition.cumulantTransform f B =
      Finpartition.cumulantTransform
        (fun s : Finset B ↦ f (s.map (Function.Embedding.subtype _))) Finset.univ := by
  sorry

/-- The block moment of a family `X` on a subset of `B` equals the block moment of the
restricted family `X|_B`.

Informal proof: The product of `X i` over a subset is the same whether indexed in `ι` or in the
subtype `B`. -/
lemma blockMoment_subtype [DecidableEq ι] [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (B : Finset ι) (s : Finset B) :
    blockMoment μ X (s.map (Function.Embedding.subtype (· ∈ B))) =
      blockMoment μ (fun i : B ↦ X i.1) s := by
  sorry

theorem blockCumulant_eq_jointCumulant_subtype [DecidableEq ι] [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (B : Finset ι) :
    blockCumulant μ X B = jointCumulant μ (fun i : B ↦ X i.1) := by
  dsimp [blockCumulant, jointCumulant]
  rw [cumulantTransform_subtype B]
  congr 1
  ext s
  rw [blockMoment_subtype]

/-- A joint moment is the block moment on the universal set.

Informal proof: The joint moment is defined as the integral of the product of all `X i`, which
matches `blockMoment` on `univ`. -/
lemma jointMoment_eq_blockMoment_univ [Fintype ι] [DecidableEq ι]
    [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) :
    jointMoment μ X = blockMoment μ X Finset.univ := by
  sorry

/-- The block moment of an empty set is 1.

Informal proof: The product over an empty set is 1, and the integral of 1 is 1 since `μ` is a
probability measure. -/
lemma blockMoment_empty [DecidableEq ι] [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) :
    blockMoment μ X ∅ = 1 := by
  sorry

/-- Applying the partition transform to the cumulant transform recovers the original block
function at `univ`.

Informal proof: By `Finpartition.partitionTransform_cumulantTransform`, Möbius inversion on the
partition lattice is an involution. -/
lemma partitionTransform_cumulantTransform_univ [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R]
    (f : Finset ι → R) (h_empty : f ∅ = 1) :
    Finpartition.partitionTransform (Finpartition.cumulantTransform f) Finset.univ =
      f Finset.univ := by
  sorry

/-- A joint moment is the sum over partitions of products of connected correlators.

Informal proof: apply `Finpartition.partitionTransform_cumulantTransform` to the block-moment
function.  Its empty value is one by the probability-measure assumption; rewrite each block
cumulant with `blockCumulant_eq_jointCumulant_subtype`.  No partition is enumerated. -/
theorem jointMoment_eq_sum_partition_jointCumulant [Fintype ι] [DecidableEq ι]
    [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) :
    jointMoment μ X =
      ∑ P : Finpartition (Finset.univ : Finset ι),
        ∏ B ∈ P.parts, jointCumulant μ (fun i : B ↦ X i.1) := by
  rw [jointMoment_eq_blockMoment_univ]
  have h_empty : blockMoment μ X ∅ = 1 := blockMoment_empty X
  have h_inv := partitionTransform_cumulantTransform_univ (blockMoment μ X) h_empty
  dsimp [Finpartition.partitionTransform] at h_inv
  rw [← h_inv]
  dsimp [Finpartition.blockProduct]
  apply Finset.sum_congr rfl
  intro P _
  apply Finset.prod_congr rfl
  intro B _
  rw [← blockCumulant_eq_jointCumulant_subtype]
  rfl

/-- The sum over partitions of a singleton evaluates to the value at `⊤`.
Informal proof: There is only one partition of a singleton, which is `⊤`. -/
lemma sum_Finpartition_singleton {α : Type*} [DecidableEq α] (x : α)
    {R : Type*} [AddCommMonoid R]
    (f : Finpartition ({x} : Finset α) → R) :
    ∑ P, f P = f ⊤ := by
  sorry

/-- The cumulant coefficient of the top partition is 1.

Informal proof: The top partition has 1 block, so the formula `(-1)^(1-1) * (1-1)!` gives 1. -/
lemma cumulantCoefficient_top {α : Type*} [DecidableEq α] {s : Finset α} (hs : s.Nonempty) :
    (Finpartition.cumulantCoefficient (⊤ : Finpartition s) : ℝ) = 1 := by
  sorry

/-- The block product of a function on the top partition is the function applied to the whole
set.

Informal proof: The top partition has exactly one block, which is `s`. The product over its parts
is just `f s`. -/
lemma blockProduct_top {α : Type*} [DecidableEq α] {s : Finset α} (hs : s.Nonempty)
    {R : Type*} [CommMonoid R]
    (f : Finset α → R) :
    (⊤ : Finpartition s).blockProduct f = f s := by
  sorry

/-- The first cumulant is the expectation.

Informal proof: the only partition of a singleton has one block, whose Möbius coefficient is one. -/
theorem jointCumulant_one (X : Fin 1 → Ω → ℝ) :
    jointCumulant μ X = ∫ ω, X 0 ω ∂μ := by
  dsimp [jointCumulant, blockCumulant, Finpartition.cumulantTransform]
  have h_univ : (Finset.univ : Finset (Fin 1)) = {0} := rfl
  rw [h_univ]
  rw [sum_Finpartition_singleton 0]
  rw [cumulantCoefficient_top (Finset.singleton_nonempty 0)]
  rw [blockProduct_top (Finset.singleton_nonempty 0)]
  dsimp [blockMoment]
  simp

/-- The sum over partitions of a two-element set evaluates to the value at `⊤` plus the value at
`⊥`.

Informal proof: There are exactly two partitions of a two-element set: the discrete partition `⊥`
and the indiscrete partition `⊤`. -/
lemma sum_Finpartition_pair {α : Type*} [DecidableEq α] (x y : α) (hxy : x ≠ y)
    {R : Type*} [AddCommMonoid R]
    (f : Finpartition ({x, y} : Finset α) → R) :
    ∑ P, f P = f ⊤ + f ⊥ := by
  sorry

/-- The cumulant coefficient of the discrete partition of a two-element set is -1.

Informal proof: The discrete partition has 2 blocks, so the formula `(-1)^(2-1) * (2-1)!` gives
`-1`. -/
lemma cumulantCoefficient_bot_pair {α : Type*} [DecidableEq α] (x y : α) (hxy : x ≠ y) :
    (Finpartition.cumulantCoefficient (⊥ : Finpartition ({x, y} : Finset α)) : ℝ) = -1 := by
  sorry

/-- The block product of a function on the discrete partition of a two-element set is the product
of the function on the singletons.

Informal proof: The discrete partition has exactly two blocks, `{x}` and `{y}`. The product over
its parts is `f {x} * f {y}`. -/
lemma blockProduct_bot_pair {α : Type*} [DecidableEq α] (x y : α) (hxy : x ≠ y)
    {R : Type*} [CommMonoid R]
    (f : Finset α → R) :
    (⊥ : Finpartition ({x, y} : Finset α)).blockProduct f = f {x} * f {y} := by
  sorry

/-- The second cumulant is the second moment minus the product of the means.

Informal proof: the two partitions of two positions are the indiscrete partition and the partition
into singletons.  Their Möbius coefficients are `1` and `-1`; this can be obtained by specializing
the generic partition transform rather than expanding later probability proofs. -/
theorem jointCumulant_two (X : Fin 2 → Ω → ℝ) :
    jointCumulant μ X =
      (∫ ω, X 0 ω * X 1 ω ∂μ) - (∫ ω, X 0 ω ∂μ) * ∫ ω, X 1 ω ∂μ := by
  dsimp [jointCumulant, blockCumulant, Finpartition.cumulantTransform]
  have h_univ : (Finset.univ : Finset (Fin 2)) = {0, 1} := rfl
  rw [h_univ]
  rw [sum_Finpartition_pair 0 1 (by decide)]
  have h_ne : ({0, 1} : Finset (Fin 2)).Nonempty := by simp
  rw [cumulantCoefficient_top h_ne, blockProduct_top h_ne]
  rw [cumulantCoefficient_bot_pair 0 1 (by decide)]
  rw [blockProduct_bot_pair 0 1 (by decide)]
  dsimp [blockMoment]
  simp
  ring

/-- Under square-integrability, the second cumulant is Mathlib's covariance.

Informal proof: combine `jointCumulant_two` with `ProbabilityTheory.covariance_eq_sub`. -/
theorem jointCumulant_two_eq_covariance [IsProbabilityMeasure μ] (X : Fin 2 → Ω → ℝ)
    (h0 : MemLp (X 0) 2 μ) (h1 : MemLp (X 1) 2 μ) :
    jointCumulant μ X = covariance (X 0) (X 1) μ := by
  rw [jointCumulant_two, covariance_eq_sub h0 h1]
  rfl

/-- A partition of a 4-element set without singletons must be either the indiscrete partition, or
one of the 3 pairings.

Informal proof: Split the sum into partitions with and without a singleton. For a centered family,
a singleton block moment is zero, so its block product vanishes. Thus only `⊤` (coefficient one)
and the three pairings (coefficient negative one) remain. -/
lemma jointCumulant_four_of_centered_combinatorics [IsProbabilityMeasure μ]
    (X : Fin 4 → Ω → ℝ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    Finpartition.cumulantTransform (blockMoment μ X) Finset.univ =
      blockMoment μ X {0, 1, 2, 3}
      - blockMoment μ X {0, 1} * blockMoment μ X {2, 3}
      - blockMoment μ X {0, 2} * blockMoment μ X {1, 3}
      - blockMoment μ X {0, 3} * blockMoment μ X {1, 2} := by
  sorry

lemma blockMoment_four_eq (X : Fin 4 → Ω → ℝ) :
    blockMoment μ X {0, 1, 2, 3} = ∫ ω, X 0 ω * X 1 ω * X 2 ω * X 3 ω ∂μ := by
  dsimp [blockMoment]
  congr 1
  ext ω
  have h0123 : ({0, 1, 2, 3} : Finset (Fin 4)) = Finset.univ := by decide
  rw [h0123, Fin.prod_univ_four]

lemma blockMoment_pair_eq_01 (X : Fin 4 → Ω → ℝ) :
    blockMoment μ X {0, 1} = ∫ ω, X 0 ω * X 1 ω ∂μ := by
  dsimp [blockMoment]
  congr 1
  ext ω
  simp [Finset.prod_insert, Finset.prod_singleton]

lemma blockMoment_pair_eq_23 (X : Fin 4 → Ω → ℝ) :
    blockMoment μ X {2, 3} = ∫ ω, X 2 ω * X 3 ω ∂μ := by
  dsimp [blockMoment]
  congr 1
  ext ω
  simp [Finset.prod_insert, Finset.prod_singleton]

lemma blockMoment_pair_eq_02 (X : Fin 4 → Ω → ℝ) :
    blockMoment μ X {0, 2} = ∫ ω, X 0 ω * X 2 ω ∂μ := by
  dsimp [blockMoment]
  congr 1
  ext ω
  simp [Finset.prod_insert, Finset.prod_singleton]

lemma blockMoment_pair_eq_13 (X : Fin 4 → Ω → ℝ) :
    blockMoment μ X {1, 3} = ∫ ω, X 1 ω * X 3 ω ∂μ := by
  dsimp [blockMoment]
  congr 1
  ext ω
  simp [Finset.prod_insert, Finset.prod_singleton]

lemma blockMoment_pair_eq_03 (X : Fin 4 → Ω → ℝ) :
    blockMoment μ X {0, 3} = ∫ ω, X 0 ω * X 3 ω ∂μ := by
  dsimp [blockMoment]
  congr 1
  ext ω
  simp [Finset.prod_insert, Finset.prod_singleton]

lemma blockMoment_pair_eq_12 (X : Fin 4 → Ω → ℝ) :
    blockMoment μ X {1, 2} = ∫ ω, X 1 ω * X 2 ω ∂μ := by
  dsimp [blockMoment]
  congr 1
  ext ω
  simp [Finset.prod_insert, Finset.prod_singleton]

/-- Exact centered fourth-cumulant formula.

Informal proof: specialize the generic Möbius formula to four positions.  Every partition with a
singleton block vanishes by `hcenter`; the remaining partitions are the one four-element block and
the three partitions into two pairs.  The classification should be proved once as a finite-
partition lemma, not by enumerating terms in this probability theorem. -/
theorem jointCumulant_four_of_centered [IsProbabilityMeasure μ] (X : Fin 4 → Ω → ℝ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    jointCumulant μ X =
      (∫ ω, X 0 ω * X 1 ω * X 2 ω * X 3 ω ∂μ)
        - (∫ ω, X 0 ω * X 1 ω ∂μ) * (∫ ω, X 2 ω * X 3 ω ∂μ)
        - (∫ ω, X 0 ω * X 2 ω ∂μ) * (∫ ω, X 1 ω * X 3 ω ∂μ)
        - (∫ ω, X 0 ω * X 3 ω ∂μ) * (∫ ω, X 1 ω * X 2 ω ∂μ) := by
  dsimp [jointCumulant, blockCumulant]
  rw [jointCumulant_four_of_centered_combinatorics X hcenter]
  rw [blockMoment_four_eq, blockMoment_pair_eq_01, blockMoment_pair_eq_23]
  rw [blockMoment_pair_eq_02, blockMoment_pair_eq_13]
  rw [blockMoment_pair_eq_03, blockMoment_pair_eq_12]

lemma cumulantTransform_equiv [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {R : Type*} [CommRing R]
    (e : ι ≃ κ) (f : Finset ι → R) :
    Finpartition.cumulantTransform (fun s : Finset κ ↦ f (s.map e.symm.toEmbedding)) Finset.univ =
      Finpartition.cumulantTransform f Finset.univ := by
  sorry

lemma blockMoment_map_equiv [DecidableEq ι] [DecidableEq κ] [IsProbabilityMeasure μ]
    (e : ι ≃ κ) (X : ι → Ω → ℝ) (s : Finset κ) :
    blockMoment μ (fun j ↦ X (e.symm j)) s = blockMoment μ X (s.map e.symm.toEmbedding) := by
  sorry

/-- Joint cumulants are invariant under equivalences of their position types.

Informal proof: use `Finpartition.cumulantTransform_map` and `jointMoment_perm` on every block. -/
theorem jointCumulant_perm [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [IsProbabilityMeasure μ] (e : ι ≃ κ) (X : ι → Ω → ℝ) :
    jointCumulant μ (fun j ↦ X (e.symm j)) = jointCumulant μ X := by
  dsimp [jointCumulant, blockCumulant]
  have h := cumulantTransform_equiv e (blockMoment μ X)
  rw [← h]
  congr 1
  ext s
  rw [blockMoment_map_equiv]

lemma blockProduct_add [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (P : Finpartition (Finset.univ : Finset ι)) (f g h : Finset ι → R) (i : ι)
    (h_add : ∀ s, f s = if i ∈ s then g s + h s else g s)
    (h_id : ∀ s, i ∉ s → h s = g s) :
    P.blockProduct f = P.blockProduct g + P.blockProduct h := by
  sorry

lemma cumulantTransform_add [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (f g h : Finset ι → R) (i : ι)
    (h_add : ∀ s, f s = if i ∈ s then g s + h s else g s)
    (h_id : ∀ s, i ∉ s → h s = g s) :
    Finpartition.cumulantTransform f Finset.univ =
      Finpartition.cumulantTransform g Finset.univ +
        Finpartition.cumulantTransform h Finset.univ := by
  sorry

lemma blockMoment_add_update [DecidableEq ι] [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (i : ι) (Y : Ω → ℝ)
    (hX : HasFiniteJointMoments μ X)
    (hY : HasFiniteJointMoments μ (Function.update X i Y))
    (s : Finset ι) :
    blockMoment μ (Function.update X i (X i + Y)) s =
      if i ∈ s then blockMoment μ X s + blockMoment μ (Function.update X i Y) s
      else blockMoment μ X s := by
  sorry

lemma blockMoment_update_not_mem [DecidableEq ι] [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (i : ι) (Y : Ω → ℝ)
    (s : Finset ι) (hi : i ∉ s) :
    blockMoment μ (Function.update X i Y) s = blockMoment μ X s := by
  sorry

/-- Joint cumulants are additive in one argument when all needed moments are integrable.

Informal proof: split each block moment containing `i` with integral additivity, then distribute
through the finite Möbius sum.  Blocks not containing `i` occur identically on both sides and their
coefficients cancel by the same partition identity. -/
theorem jointCumulant_add [Fintype ι] [DecidableEq ι] [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (i : ι) (Y : Ω → ℝ)
    (hX : HasFiniteJointMoments μ X)
    (hY : HasFiniteJointMoments μ (Function.update X i Y)) :
    jointCumulant μ (Function.update X i (X i + Y)) =
      jointCumulant μ X + jointCumulant μ (Function.update X i Y) := by
  dsimp [jointCumulant, blockCumulant]
  apply cumulantTransform_add _ _ _ i
  · intro s
    exact blockMoment_add_update X i Y hX hY s
  · intro s hs
    exact blockMoment_update_not_mem X i Y s hs

lemma blockProduct_smul [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (P : Finpartition (Finset.univ : Finset ι)) (f : Finset ι → R) (c : R) (i : ι) :
    P.blockProduct (fun s => if i ∈ s then c * f s else f s) = c * P.blockProduct f := by
  sorry

lemma cumulantTransform_smul [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (f : Finset ι → R) (c : R) (i : ι) :
    Finpartition.cumulantTransform (fun s => if i ∈ s then c * f s else f s) Finset.univ =
      c * Finpartition.cumulantTransform f Finset.univ := by
  sorry

lemma blockMoment_smul_update [DecidableEq ι] [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (i : ι) (c : ℝ)
    (s : Finset ι) :
    blockMoment μ (Function.update X i (c • X i)) s =
      if i ∈ s then c * blockMoment μ X s
      else blockMoment μ X s := by
  sorry

/-- Joint cumulants are homogeneous in one argument.

Informal proof: every block containing `i` acquires one factor `c`; finite integral and product
linearity pull that factor through the Möbius sum. -/
theorem jointCumulant_smul [Fintype ι] [DecidableEq ι] [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (i : ι) (c : ℝ) :
    jointCumulant μ (Function.update X i (c • X i)) = c * jointCumulant μ X := by
  dsimp [jointCumulant, blockCumulant]
  have h := cumulantTransform_smul (blockMoment μ X) c i
  rw [← h]
  congr 1
  ext s
  exact blockMoment_smul_update X i c s

/-- Independence of the observables indexed by `A` from those indexed by its complement. -/
def IndepAcross (μ : Measure Ω) (X : ι → Ω → ℝ)
    (A : Finset ι) : Prop :=
  IndepFun (fun ω (i : A) ↦ X i.1 ω) (fun ω (i : {i : ι // i ∉ A}) ↦ X i.1 ω) μ

lemma blockMoment_indepFun_split [Fintype ι] [DecidableEq ι] [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (A : Finset ι) (hX : HasFiniteJointMoments μ X)
    (hmeas : ∀ i, Measurable (X i)) (hindep : IndepAcross μ X A) (s : Finset ι) :
    blockMoment μ X s = blockMoment μ X (s ∩ A) * blockMoment μ X (s \ A) := by
  sorry

lemma cumulantTransform_eq_zero_of_split [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (f : Finset ι → R) (A : Finset ι) (hA : A.Nonempty) (hAc : (Finset.univ \ A).Nonempty)
    (h_factor : ∀ s, f s = f (s ∩ A) * f (s \ A)) :
    Finpartition.cumulantTransform f Finset.univ = 0 := by
  sorry

/-- A joint cumulant vanishes when its positions split into two nonempty independent blocks.

Informal proof: independence factors every mixed block moment into its two restrictions.  Insert
those factorizations into the Möbius formula; Möbius inversion on the product of the two partition
lattices makes the total coefficient zero. -/
theorem jointCumulant_eq_zero_of_indepFun_split [Fintype ι] [DecidableEq ι]
    [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (A : Finset ι)
    (hA : A.Nonempty) (hAc : (Finset.univ \ A).Nonempty)
    (hX : HasFiniteJointMoments μ X) (hmeas : ∀ i, Measurable (X i))
    (hindep : IndepAcross μ X A) :
    jointCumulant μ X = 0 := by
  dsimp [jointCumulant, blockCumulant]
  apply cumulantTransform_eq_zero_of_split _ A hA hAc
  intro s
  exact blockMoment_indepFun_split X A hX hmeas hindep s

/-- The scalar cumulant is the derivative of the cumulant-generating function at zero. -/
def cumulant (μ : Measure Ω) (X : Ω → ℝ) (n : ℕ) : ℝ :=
  iteratedDeriv n (cgf X μ) 0

/-- The block moment of a constant variable function evaluates to the expected value of $X$
raised to the power of the block size.

Informal proof: The product over $B$ of $X$ is $X^{|B|}$. So the block moment is exactly the
expectation of $X^{|B|}$. -/
lemma blockMoment_const_eq_integral_pow [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (n : ℕ) (s : Finset (Fin n)) :
    blockMoment μ (fun _ : Fin n ↦ X) s = ∫ ω, X ω ^ s.card ∂μ := by
  sorry

/-- The $k$-th derivative of the MGF at zero is the $k$-th moment.
Informal proof: Differentiate under the integral sign $k$ times and evaluate at $t=0$. -/
lemma iteratedDeriv_mgf_zero_eq_moment [IsProbabilityMeasure μ] (X : Ω → ℝ) (k : ℕ)
    (hmgf : 0 ∈ interior (integrableExpSet X μ)) :
    iteratedDeriv k (mgf X μ) 0 = ∫ ω, X ω ^ k ∂μ := by
  sorry

/-- The $n$-th derivative of the CGF at zero expands to a sum over partition lattices of products
of MGF derivatives.

Informal proof: By Faà di Bruno's formula (or the relation between moments and cumulants), the
derivatives of the logarithm of a power series are a sum over set partitions, with coefficients
given by the Möbius function of the partition lattice. -/
lemma iteratedDeriv_cgf_zero_eq_sum_partitions [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (n : ℕ) (hn : n ≠ 0)
    (hmgf : 0 ∈ interior (integrableExpSet X μ)) :
    iteratedDeriv n (cgf X μ) 0 =
      ∑ P : Finpartition (Finset.univ : Finset (Fin n)),
        (P.cumulantCoefficient : ℝ) * ∏ B ∈ P.parts, iteratedDeriv B.card (mgf X μ) 0 := by
  sorry

/-- The cumulant of order 0 is 0. -/
lemma cumulant_zero [IsProbabilityMeasure μ] (X : Ω → ℝ) : cumulant μ X 0 = 0 := by sorry

/-- Analytic and set-partition definitions of a repeated-variable cumulant agree.

Informal proof: `iteratedDeriv_mgf_zero` identifies the MGF coefficients with moments.  Expanding
the logarithm of a power series with constant coefficient one gives the partition-lattice Möbius
coefficients, so the `n`th CGF derivative is exactly the joint cumulant of `n` copies of `X`. -/
theorem cumulant_eq_jointCumulant [IsProbabilityMeasure μ] (X : Ω → ℝ) (n : ℕ)
    (hmgf : 0 ∈ interior (integrableExpSet X μ)) :
    cumulant μ X n = jointCumulant μ (fun _ : Fin n ↦ X) := by
  sorry

end Renormalization

end

end
