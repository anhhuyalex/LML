/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Basic
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
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

/-- The canonical equivalence between partitions of a finset `B : Finset ι` and partitions of the
full subtype `{x : ι // x ∈ B}`.  Each block is transported by the preimage/image correspondence
induced by the injective subtype embedding: a block `A ⊆ B` becomes `{x : B | x.1 ∈ A}` and a
block `C : Finset B` becomes `C.map φ`.  Both round-trips are the standard
`Finset.preimage_map`/preimage-of-image identities, and `Finset.univ.map φ = B` supplies the
coverage.  Used by `cumulantTransform_subtype` to reindex the cumulant sum. -/
def finpartitionSubtypeEquiv [DecidableEq ι] (B : Finset ι) :
    Finpartition B ≃ Finpartition (Finset.univ : Finset B) := by
  classical
  -- The injective subtype embedding `φ : B ↪ ι` moves blocks between the two worlds.
  let φ : B ↪ ι := Function.Embedding.subtype (fun x : ι ↦ x ∈ B)
  -- Forward: each part `A ⊆ B` is sent to its subtype preimage `{x : B | x.1 ∈ A}`.
  let toFun : Finpartition B → Finpartition (Finset.univ : Finset B) := fun P => by
    let parts : Finset (Finset B) :=
      P.parts.image fun A : Finset ι ↦ A.preimage φ φ.injective.injOn
    refine Finpartition.ofExistsUnique (s := (Finset.univ : Finset B)) parts ?subset_univ
      ?exists_unique ?empty_notMem
    · exact fun _ _ x _ => Finset.mem_univ x
    · intro x hx
      obtain ⟨A, hA_props, hA_unique⟩ := P.existsUnique_mem x.2
      rcases hA_props with ⟨hA_mem, hxA⟩
      refine ⟨A.preimage φ φ.injective.injOn, ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_image.mpr ⟨A, hA_mem, rfl⟩
      · simpa [φ] using hxA
      · intro C hC_props
        rcases hC_props with ⟨hC_mem, hxC⟩
        rcases Finset.mem_image.mp hC_mem with ⟨A', hA'_mem, rfl⟩
        rw [hA_unique A' ⟨hA'_mem, by simpa [φ] using hxC⟩]
    · intro h_empty_mem
      rcases Finset.mem_image.mp h_empty_mem with ⟨A, hA_mem, hA_preimage⟩
      obtain ⟨a, haA⟩ := P.nonempty_of_mem_parts hA_mem
      have : (⟨a, P.subset hA_mem haA⟩ : B) ∈ (∅ : Finset B) := by
        rw [← hA_preimage]
        simpa [φ] using haA
      exact Finset.notMem_empty _ this
  -- Inverse: each subtype block is mapped back to its image in `ι`.
  let invFun : Finpartition (Finset.univ : Finset B) → Finpartition B := fun Q => by
    let parts : Finset (Finset ι) := Q.parts.image fun C : Finset B ↦ C.map φ
    refine Finpartition.ofExistsUnique (s := B) parts ?subset_B ?_ ?_
    · intro A hA x hx
      rcases Finset.mem_image.mp hA with ⟨C, hC, rfl⟩
      rcases Finset.mem_map.mp hx with ⟨y, hyC, hyx⟩
      simp [φ, ← hyx, y.2]
    · intro a ha
      let x : B := ⟨a, ha⟩
      obtain ⟨C, hC_props, hC_unique⟩ := Q.existsUnique_mem (Finset.mem_univ x)
      rcases hC_props with ⟨hC_mem, hxC⟩
      refine ⟨C.map φ, ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_image.mpr ⟨C, hC_mem, rfl⟩
      · exact Finset.mem_map.mpr ⟨x, hxC, rfl⟩
      · intro A hA_props
        rcases hA_props with ⟨hA_mem, haA⟩
        rcases Finset.mem_image.mp hA_mem with ⟨D, hD_mem, hDmap⟩
        rw [← hDmap] at haA ⊢
        rcases Finset.mem_map.mp haA with ⟨y, hyD, hya⟩
        rw [hC_unique D ⟨hD_mem, by
          simpa [(Subtype.ext (by simpa [φ, x] using hya) : y = x)] using hyD⟩]
    · intro h_empty_mem
      rcases Finset.mem_image.mp h_empty_mem with ⟨C, hC_mem, hCmap⟩
      rw [Finset.map_eq_empty.mp hCmap] at hC_mem
      exact Q.empty_notMem_parts hC_mem
  refine
    { toFun := toFun
      invFun := invFun
      left_inv := ?_
      right_inv := ?_ }
  · intro P
    -- The forward round-trip is `(A.preimage φ _).map φ = A` for every part `A` of `P`,
    -- since parts of `B` are subsets of `B` and φ is injective; extensionality for
    -- `Finpartition` then identifies the partitions.
    have h_roundtrip :
        ∀ A ∈ P.parts, (A.preimage φ φ.injective.injOn).map φ = A := by
      intro A hA
      apply Finset.ext
      intro x
      constructor
      · intro hx
        rcases Finset.mem_map.mp hx with ⟨y, hy, hyx⟩
        simpa [hyx] using hy
      · intro hx
        exact Finset.mem_map.mpr ⟨⟨x, P.subset hA hx⟩, by simpa [φ] using hx, rfl⟩
    apply Finpartition.ext
    ext A
    constructor
    · intro hA
      rcases Finset.mem_image.mp hA with ⟨C, hC, hCA⟩
      rcases Finset.mem_image.mp hC with ⟨A', hA', hCeq⟩
      simpa [show A' = A by rw [← h_roundtrip A' hA', hCeq, hCA]] using hA'
    · intro hA
      exact Finset.mem_image.mpr
        ⟨A.preimage φ φ.injective.injOn, Finset.mem_image.mpr ⟨A, hA, rfl⟩,
          h_roundtrip A hA⟩
  · intro Q
    -- The backward round-trip is the standard `Finset.preimage_map φ` on every subtype part,
    -- again followed by extensionality for `Finpartition`.
    apply Finpartition.ext
    ext C
    constructor
    · intro hC
      rcases Finset.mem_image.mp hC with ⟨A, hA, hAC⟩
      rcases Finset.mem_image.mp hA with ⟨D, hD, hDA⟩
      simpa [show D = C by rw [← Finset.preimage_map φ D, hDA, hAC]] using hD
    · intro hC
      exact Finset.mem_image.mpr
        ⟨C.map φ, Finset.mem_image.mpr ⟨C, hC, rfl⟩, Finset.preimage_map φ C⟩

-- The subtype equivalence preserves the cumulant summand: the number of blocks (hence the Möbius
-- coefficient) is unchanged, and the block products correspond via the preimage/image round-trip
-- `(A.preimage φ _).map φ = A` for parts of `P`.  Used by `cumulantTransform_subtype` to replace
-- each summand by its transported image before reindexing.
private lemma finpartitionSubtypeEquiv_summand [DecidableEq ι] {R : Type*} [CommRing R]
    (B : Finset ι) (f : Finset ι → R) (P : Finpartition B) :
    P.cumulantCoefficient * P.blockProduct f =
      (finpartitionSubtypeEquiv B P).cumulantCoefficient *
        (finpartitionSubtypeEquiv B P).blockProduct
          (fun s : Finset B ↦ f (s.map (Function.Embedding.subtype (· ∈ B)))) := by
  classical
  let φ : B ↪ ι := Function.Embedding.subtype (fun x : ι ↦ x ∈ B)
  let pre : Finset ι → Finset B := fun A ↦ A.preimage φ φ.injective.injOn
  have h_parts : (finpartitionSubtypeEquiv B P).parts = P.parts.image pre := rfl
  have h_roundtrip : ∀ A ∈ P.parts, (pre A).map φ = A := by
    intro A hA
    apply Finset.ext
    intro x
    constructor
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨y, hy, hyx⟩
      simpa [pre, hyx] using hy
    · intro hx
      exact Finset.mem_map.mpr ⟨⟨x, P.subset hA hx⟩, by simpa [pre, φ] using hx, rfl⟩
  have h_pre_inj : Set.InjOn pre (↑P.parts) := by
    intro A hA A' hA' hAA'
    simpa [h_roundtrip A hA, h_roundtrip A' hA'] using
      congrArg (fun C : Finset B ↦ C.map φ) hAA'
  have h_card : (finpartitionSubtypeEquiv B P).parts.card = P.parts.card := by
    rw [h_parts, Finset.card_image_of_injOn h_pre_inj]
  have h_coeff :
      Finpartition.cumulantCoefficient (R := R) (finpartitionSubtypeEquiv B P) =
        Finpartition.cumulantCoefficient (R := R) P := by
    rw [Finpartition.cumulantCoefficient, h_card, Finpartition.cumulantCoefficient]
  have h_block :
      (finpartitionSubtypeEquiv B P).blockProduct (fun s : Finset B ↦ f (s.map φ)) =
        P.blockProduct f := by
    rw [Finpartition.blockProduct, Finpartition.blockProduct, h_parts]
    exact (Finset.prod_image h_pre_inj).trans
      (Finset.prod_congr rfl (fun A hA => congrArg f (h_roundtrip A hA)))
  rw [h_coeff, h_block]

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
  -- If B is empty, both sides are 0 by the convention in cumulantTransform
  by_cases hB : B = ∅
  · simp [Finpartition.cumulantTransform, hB]
  · -- Expand both sides using the nonempty case of cumulantTransform
    simp only [Finpartition.cumulantTransform, if_neg hB,
      if_neg (show (Finset.univ : Finset B) ≠ ∅ by simpa [Finset.univ_eq_attach] using hB)]
    -- Reindex the cumulant sum along the subtype equivalence.  `finpartitionSubtypeEquiv_summand`
    -- shows every summand is transported unchanged, and `Equiv.sum_comp` rewrites the transported
    -- sum back to the sum over partitions of the full subtype.
    rw [← (finpartitionSubtypeEquiv B).sum_comp]
    exact Finset.sum_congr rfl (fun P _ => finpartitionSubtypeEquiv_summand B f P)

/-- The block moment of a family `X` on a subset of `B` equals the block moment of the
restricted family `X|_B`.

Informal proof: The product of `X i` over a subset is the same whether indexed in `ι` or in the
subtype `B`. -/
lemma blockMoment_subtype (X : ι → Ω → ℝ) (B : Finset ι) (s : Finset B) :
    blockMoment μ X (s.map (Function.Embedding.subtype (· ∈ B))) =
      blockMoment μ (fun i : B ↦ X i.1) s := by
  -- Both sides are integrals over `ω` of a pointwise product, so compare the integrands.
  dsimp [blockMoment]
  congr 1
  ext ω
  -- A product over the mapped block reindexes to `s` by `Finset.prod_map`.
  exact Finset.prod_map s (Function.Embedding.subtype (· ∈ B)) (fun i : ι ↦ X i ω)

theorem blockCumulant_eq_jointCumulant_subtype [DecidableEq ι]
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
lemma jointMoment_eq_blockMoment_univ [Fintype ι] (X : ι → Ω → ℝ) :
    jointMoment μ X = blockMoment μ X Finset.univ := by
  rfl

/-- The block moment of an empty set is 1.

Informal proof: The product over an empty set is 1, and the integral of 1 is 1 since `μ` is a
probability measure. -/
lemma blockMoment_empty [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) :
    blockMoment μ X ∅ = 1 := by
  simp [blockMoment]

/-- Applying the partition transform to the cumulant transform recovers the original block
function at `univ`.

Informal proof: By `Finpartition.partitionTransform_cumulantTransform`, Möbius inversion on the
partition lattice is an involution. -/
lemma partitionTransform_cumulantTransform_univ [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R]
    (f : Finset ι → R) (h_empty : f ∅ = 1) :
    Finpartition.partitionTransform (Finpartition.cumulantTransform f) Finset.univ =
      f Finset.univ := by
  have h := Finpartition.partitionTransform_cumulantTransform (R := R) f h_empty
  simpa using congrFun h Finset.univ

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

/-- The parts of the top partition of a nonempty finset are exactly the singleton of the whole
set. -/
private lemma top_parts_eq_singleton {α : Type*} [DecidableEq α] {s : Finset α} (hs : s ≠ ∅) :
    (⊤ : Finpartition s).parts = {s} := by
  classical
  ext B
  constructor
  · intro hB
    exact Finpartition.parts_top_subset s hB
  · intro hB
    rw [Finset.mem_singleton] at hB
    rw [hB]
    have hne : (⊤ : Finpartition s).parts.Nonempty :=
      Finpartition.parts_nonempty (⊤ : Finpartition s) hs
    rcases hne with ⟨C, hC⟩
    have hC_eq : C = s := Finset.mem_singleton.mp (Finpartition.parts_top_subset s hC)
    rwa [hC_eq] at hC

/-- A nonempty subset of a singleton is the singleton itself. -/
private lemma singleton_part_eq {α : Type*} {x : α} {B : Finset α}
    (hB_sub : B ⊆ ({x} : Finset α)) (hB_ne : B ≠ ∅) : B = {x} := by
  classical
  apply le_antisymm hB_sub
  intro z hz
  rw [Finset.mem_singleton.mp hz]
  rcases Finset.nonempty_iff_ne_empty.mpr hB_ne with ⟨x0, hx0⟩
  have hx0_x : x0 = x := Finset.mem_singleton.mp (hB_sub hx0)
  simpa [hx0_x] using hx0

/-- The parts of any partition of a singleton are exactly the singleton of that singleton. -/
private lemma singleton_parts_eq {α : Type*} [DecidableEq α] {x : α}
    (P : Finpartition ({x} : Finset α)) : P.parts = {{x}} := by
  classical
  ext B
  constructor
  · intro hB
    rw [Finset.mem_singleton]
    exact singleton_part_eq (P.le hB) (P.ne_empty hB)
  · intro hB
    rw [Finset.mem_singleton] at hB
    rw [hB]
    have hne : P.parts.Nonempty := Finpartition.parts_nonempty P (by simp)
    rcases hne with ⟨C, hC⟩
    have hC_eq : C = {x} := Finset.mem_singleton.mp (by
      rw [Finset.mem_singleton]
      exact singleton_part_eq (P.le hC) (P.ne_empty hC))
    rwa [hC_eq] at hC

/-- The sum over partitions of a singleton evaluates to the value at `⊤`.
Informal proof: There is only one partition of a singleton, which is `⊤`. -/
lemma sum_Finpartition_singleton {α : Type*} [DecidableEq α] (x : α)
    {R : Type*} [AddCommMonoid R]
    (f : Finpartition ({x} : Finset α) → R) :
    ∑ P, f P = f ⊤ := by
  classical
  rw [Fintype.sum_eq_single ⊤]
  · intro P hP
    exfalso
    apply hP
    apply Finpartition.ext
    rw [singleton_parts_eq P, top_parts_eq_singleton (by simp : ({x} : Finset α) ≠ ∅)]

/-- The cumulant coefficient of the top partition is 1.

Informal proof: The top partition has 1 block, so the formula `(-1)^(1-1) * (1-1)!` gives 1. -/
lemma cumulantCoefficient_top {α : Type*} [DecidableEq α] {s : Finset α} (hs : s.Nonempty) :
    (Finpartition.cumulantCoefficient (⊤ : Finpartition s) : ℝ) = 1 := by
  classical
  dsimp [Finpartition.cumulantCoefficient]
  rw [top_parts_eq_singleton (Finset.nonempty_iff_ne_empty.mp hs)]
  simp

/-- The block product of a function on the top partition is the function applied to the whole
set.

Informal proof: The top partition has exactly one block, which is `s`. The product over its parts
is just `f s`. -/
lemma blockProduct_top {α : Type*} [DecidableEq α] {s : Finset α} (hs : s.Nonempty)
    {R : Type*} [CommMonoid R]
    (f : Finset α → R) :
    (⊤ : Finpartition s).blockProduct f = f s := by
  classical
  dsimp [Finpartition.blockProduct]
  rw [top_parts_eq_singleton (Finset.nonempty_iff_ne_empty.mp hs)]
  simp

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

/-- A partition of a two-element set is either the discrete partition `⊥` or the indiscrete
partition `⊤`.

Informal proof: the block containing `x` is a nonempty subset of `{x, y}` containing `x`, so it is
either `{x}` or `{x, y}`.  In the first case every other block is `{y}` (any block is a nonempty
subset of `{x, y}` different from the full set, hence a singleton, and distinct blocks are
disjoint); in the second case the full block covers everything and no other block can exist. -/
private lemma pair_part_eq_bot_or_top {α : Type*} [DecidableEq α] {x y : α} (hxy : x ≠ y)
    (P : Finpartition ({x, y} : Finset α)) : P = ⊥ ∨ P = ⊤ := by
  classical
  have hx_mem : x ∈ ({x, y} : Finset α) := by simp
  have hy_mem : y ∈ ({x, y} : Finset α) := by simp
  have hpx_sub : P.part x ⊆ ({x, y} : Finset α) := P.le (P.part_mem.2 hx_mem)
  have hpx_card_le : (P.part x).card ≤ 2 := by
    simpa [hxy] using Finset.card_le_card hpx_sub
  have hpx_pos : 0 < (P.part x).card := Finset.card_pos.2 (P.part_nonempty.2 hx_mem)
  by_cases hpx_full : P.part x = ({x, y} : Finset α)
  · right
    apply Finpartition.ext
    ext B
    constructor
    · intro hB
      rw [top_parts_eq_singleton (by simp : ({x, y} : Finset α) ≠ ∅), Finset.mem_singleton]
      by_contra hB_ne
      have hB_sub : B ⊆ ({x, y} : Finset α) := P.le hB
      have hB_card_le : B.card ≤ 2 := by simpa [hxy] using Finset.card_le_card hB_sub
      have hB_pos : 0 < B.card := Finset.card_pos.2 (P.nonempty_of_mem_parts hB)
      have hB_card_ne_two : B.card ≠ 2 := by
        intro hc
        apply hB_ne
        apply Finset.eq_of_subset_of_card_le hB_sub
        rw [hc]
        simp [hxy]
      have hB_card_eq_one : B.card = 1 := by omega
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hB_card_eq_one
      have hzB : z ∈ B := by rw [hz]; simp
      have hz_xy : z ∈ ({x, y} : Finset α) := hB_sub hzB
      have hz_px : z ∈ P.part x := by rw [hpx_full]; exact hz_xy
      have hcontra : B = P.part x := P.eq_of_mem_parts hB (P.part_mem.2 hx_mem) hzB hz_px
      apply hB_ne
      rw [hcontra]
      exact hpx_full
    · intro hB
      rw [top_parts_eq_singleton (by simp : ({x, y} : Finset α) ≠ ∅)] at hB
      rw [Finset.mem_singleton] at hB
      rw [hB]
      simpa [hpx_full] using P.part_mem.2 hx_mem
  · left
    -- `P.part x` is a nonempty subset of `{x, y}` different from the full set, hence `{x}`
    have hpx : P.part x = ({x} : Finset α) := by
      have hpx_card_ne_two : (P.part x).card ≠ 2 := by
        intro hc
        apply hpx_full
        apply Finset.eq_of_subset_of_card_le hpx_sub
        rw [hc]
        simp [hxy]
      have hpx_card_eq_one : (P.part x).card = 1 := by omega
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hpx_card_eq_one
      have hzx : z = x := by
        have hx_px : x ∈ P.part x := P.mem_part hx_mem
        have hx_z : x = z := by
          rw [hz] at hx_px
          simpa using hx_px
        exact hx_z.symm
      rw [hz, hzx]
    -- no block can be the full set, otherwise it overlaps `P.part x = {x}`
    have hnot_full : ∀ B : Finset α, B ∈ P.parts → B ≠ ({x, y} : Finset α) := by
      intro B hB hBf
      have hx_B : x ∈ B := by rw [hBf]; simp
      have hx_px : x ∈ P.part x := P.mem_part hx_mem
      have hcontra : B = P.part x := P.eq_of_mem_parts hB (P.part_mem.2 hx_mem) hx_B hx_px
      have hxy_eq : y = x := by
        have hinsert : ({x, y} : Finset α) = ({x} : Finset α) := by
          calc
            ({x, y} : Finset α) = B := hBf.symm
            _ = P.part x := hcontra
            _ = ({x} : Finset α) := hpx
        have hy_in : y ∈ ({x} : Finset α) := by
          rw [← hinsert]
          simp
        simpa using hy_in
      exact hxy hxy_eq.symm
    have hpyp : P.part y = ({y} : Finset α) := by
      have hpy_sub : P.part y ⊆ ({x, y} : Finset α) := P.le (P.part_mem.2 hy_mem)
      have hpy_card_le : (P.part y).card ≤ 2 := by
        simpa [hxy] using Finset.card_le_card hpy_sub
      have hpy_pos : 0 < (P.part y).card := Finset.card_pos.2 (P.part_nonempty.2 hy_mem)
      have hpy_card_ne_two : (P.part y).card ≠ 2 := by
        intro hc
        apply hnot_full (P.part y) (P.part_mem.2 hy_mem)
        apply Finset.eq_of_subset_of_card_le hpy_sub
        rw [hc]
        simp [hxy]
      have hpy_card_eq_one : (P.part y).card = 1 := by omega
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hpy_card_eq_one
      have hzy : z = y := by
        have hy_py : y ∈ P.part y := P.mem_part hy_mem
        have hy_z : y = z := by
          rw [hz] at hy_py
          simpa using hy_py
        exact hy_z.symm
      rw [hz, hzy]
    apply Finpartition.ext
    ext B
    constructor
    · intro hB
      rw [Finpartition.parts_bot, Finset.mem_map]
      have hB_sub : B ⊆ ({x, y} : Finset α) := P.le hB
      have hB_card_le : B.card ≤ 2 := by simpa [hxy] using Finset.card_le_card hB_sub
      have hB_pos : 0 < B.card := Finset.card_pos.2 (P.nonempty_of_mem_parts hB)
      have hB_card_ne_two : B.card ≠ 2 := by
        intro hc
        apply hnot_full B hB
        apply Finset.eq_of_subset_of_card_le hB_sub
        rw [hc]
        simp [hxy]
      have hB_card_eq_one : B.card = 1 := by omega
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hB_card_eq_one
      have hzB : z ∈ B := by rw [hz]; simp
      have hz_xy : z ∈ ({x, y} : Finset α) := hB_sub hzB
      rcases Finset.mem_insert.mp hz_xy with hzx | hzy
      · exact ⟨x, by simp, by simp [hz, hzx]⟩
      · exact ⟨y, by simp, by simp [hz, Finset.mem_singleton.mp hzy]⟩
    · intro hB
      rw [Finpartition.parts_bot, Finset.mem_map] at hB
      rcases hB with ⟨z, hz, rfl⟩
      rcases Finset.mem_insert.mp hz with hzx | hzy
      · rw [hzx]
        simpa [hpx] using P.part_mem.2 hx_mem
      · rw [Finset.mem_singleton.mp hzy]
        simpa [hpyp] using P.part_mem.2 hy_mem

/-- The sum over partitions of a two-element set evaluates to the value at `⊤` plus the value at
`⊥`.

Informal proof: There are exactly two partitions of a two-element set: the discrete partition `⊥`
and the indiscrete partition `⊤`. -/
lemma sum_Finpartition_pair {α : Type*} [DecidableEq α] (x y : α) (hxy : x ≠ y)
    {R : Type*} [AddCommMonoid R]
    (f : Finpartition ({x, y} : Finset α) → R) :
    ∑ P, f P = f ⊤ + f ⊥ := by
  classical
  have huniv : (Finset.univ : Finset (Finpartition ({x, y} : Finset α))) = {⊥, ⊤} := by
    ext P
    constructor
    · intro hP
      rcases pair_part_eq_bot_or_top hxy P with rfl | rfl <;> simp
    · intro hP
      simp only [Finset.mem_insert, Finset.mem_singleton] at hP
      rcases hP with rfl | rfl <;> simp
  have hbot_ne_top : (⊥ : Finpartition ({x, y} : Finset α)) ≠ ⊤ := by
    intro h
    have hparts := congrArg Finpartition.parts h
    have hx_mem_bot : ({x} : Finset α) ∈ (⊥ : Finpartition ({x, y} : Finset α)).parts := by
      rw [Finpartition.parts_bot]
      simp
    have hx_mem_top : ({x} : Finset α) ∈ (⊤ : Finpartition ({x, y} : Finset α)).parts := by
      rw [← hparts]
      exact hx_mem_bot
    have hx_eq : ({x} : Finset α) = ({x, y} : Finset α) :=
      Finset.mem_singleton.mp (Finpartition.parts_top_subset ({x, y} : Finset α) hx_mem_top)
    have hy_in : y ∈ ({x} : Finset α) := by
      rw [hx_eq]
      simp
    exact hxy (Finset.mem_singleton.mp hy_in).symm
  calc
    ∑ P, f P = ∑ P ∈ (Finset.univ : Finset (Finpartition ({x, y} : Finset α))), f P := rfl
    _ = ∑ P ∈ ({⊥, ⊤} : Finset (Finpartition ({x, y} : Finset α))), f P := by rw [huniv]
    _ = f ⊥ + f ⊤ := by
          rw [Finset.sum_pair hbot_ne_top]
    _ = f ⊤ + f ⊥ := by rw [add_comm]

/-- The cumulant coefficient of the discrete partition of a two-element set is -1.

Informal proof: The discrete partition has 2 blocks, so the formula `(-1)^(2-1) * (2-1)!` gives
`-1`. -/
lemma cumulantCoefficient_bot_pair {α : Type*} [DecidableEq α] (x y : α) (hxy : x ≠ y) :
    (Finpartition.cumulantCoefficient (⊥ : Finpartition ({x, y} : Finset α)) : ℝ) = -1 := by
  classical
  dsimp [Finpartition.cumulantCoefficient]
  rw [Finset.card_map]
  simp [hxy]

/-- The block product of a function on the discrete partition of a two-element set is the product
of the function on the singletons.

Informal proof: The discrete partition has exactly two blocks, `{x}` and `{y}`. The product over
its parts is `f {x} * f {y}`. -/
lemma blockProduct_bot_pair {α : Type*} [DecidableEq α] (x y : α) (hxy : x ≠ y)
    {R : Type*} [CommMonoid R]
    (f : Finset α → R) :
    (⊥ : Finpartition ({x, y} : Finset α)).blockProduct f = f {x} * f {y} := by
  classical
  dsimp [Finpartition.blockProduct]
  rw [Finset.prod_map]
  exact Finset.prod_pair hxy

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

/-- The pairing of `Fin 4` whose block containing `0` is `{0, a}`.

The complementary block is `univ \ {0, a}`.  The definition is total in `a` (no proof argument is
needed); for `a = 1, 2, 3` this is one of the three pairings of the four positions, which are the
only pairings that survive in `cumulantTransform_fin_four_of_singleton_vanish`. -/
private def finFourPairing (a : Fin 4) : Finpartition (Finset.univ : Finset (Fin 4)) := by
  classical
  refine Finpartition.ofExistsUnique (s := Finset.univ)
    ({{(0 : Fin 4), a}, Finset.univ \ ({(0 : Fin 4), a} : Finset (Fin 4))} :
      Finset (Finset (Fin 4))) ?_ ?_ ?_
  · -- every part is a subset of `univ`
    intro B hB
    rcases Finset.mem_insert.mp hB with hB | hB
    · rw [hB]
      simp
    · rw [Finset.mem_singleton.mp hB]
      simp
  · -- `x` lies in exactly one of the two parts: `{0, a}` when it contains `x`, else the complement
    intro x hx
    by_cases hx01 : x ∈ ({(0 : Fin 4), a} : Finset (Fin 4))
    · refine ⟨({(0 : Fin 4), a} : Finset (Fin 4)), ⟨by simp, hx01⟩, ?_⟩
      intro t ht
      rcases ht with ⟨ht_mem, hxt⟩
      rcases Finset.mem_insert.mp ht_mem with ht_eq | ht_mem
      · -- `t = {0, a}` is the distinguished block
        rw [ht_eq]
      · -- the complement cannot contain `x`
        exfalso
        have ht_eq' : t = Finset.univ \ ({(0 : Fin 4), a} : Finset (Fin 4)) :=
          Finset.mem_singleton.mp ht_mem
        have hxt' : x ∈ Finset.univ \ ({(0 : Fin 4), a} : Finset (Fin 4)) := by
          simpa [ht_eq'] using hxt
        exact (Finset.mem_sdiff.mp hxt').2 hx01
    · refine ⟨Finset.univ \ ({(0 : Fin 4), a} : Finset (Fin 4)), ⟨by simp, ?_⟩, ?_⟩
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx01⟩
      · intro t ht
        rcases ht with ⟨ht_mem, hxt⟩
        rcases Finset.mem_insert.mp ht_mem with ht_eq | ht_mem
        · -- `t = {0, a}`, which does not contain `x`
          exfalso
          exact hx01 (by rwa [ht_eq] at hxt)
        · -- `t` is the complement, the distinguished block
          rw [Finset.mem_singleton.mp ht_mem]
  · -- the empty set is not a part: both blocks are nonempty
    intro hB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hB
    rcases hB with hB | hB
    · -- `∅ = {0, a}` would put `0` in the empty set
      have h0in : (0 : Fin 4) ∈ ({(0 : Fin 4), a} : Finset (Fin 4)) := by simp
      have h0empty : (0 : Fin 4) ∈ (∅ : Finset (Fin 4)) := by rwa [← hB] at h0in
      exact Finset.notMem_empty (0 : Fin 4) h0empty
    · -- `∅ = univ \ {0, a}` is impossible because the complement is nonempty
      have hne : (Finset.univ \ ({(0 : Fin 4), a} : Finset (Fin 4))).Nonempty := by
        -- `univ` has four elements and `{0, a}` at most two, so the complement has at least two
        rw [← Finset.card_pos,
          Finset.card_sdiff_of_subset (by simp : ({(0 : Fin 4), a} : Finset (Fin 4)) ⊆ Finset.univ)]
        rw [Finset.card_univ, Fintype.card_fin]
        have hcard : ({(0 : Fin 4), a} : Finset (Fin 4)).card ≤ 2 := by
          by_cases ha : a = 0
          · rw [ha]
            simp
          · rw [Finset.card_insert_of_notMem (by simpa [eq_comm] using ha)]
            simp
        omega
      rcases hne with ⟨x, hx⟩
      have hx_empty : x ∈ (∅ : Finset (Fin 4)) := by rwa [← hB] at hx
      exact Finset.notMem_empty x hx_empty

/-- The parts of `finFourPairing a` are the block `{0, a}` and its complement. -/
private lemma finFourPairing_parts (a : Fin 4) :
    (finFourPairing a).parts =
      ({{(0 : Fin 4), a}, Finset.univ \ ({(0 : Fin 4), a} : Finset (Fin 4))} :
        Finset (Finset (Fin 4))) := by
  dsimp [finFourPairing]
  rw [Finpartition.ofExistsUnique_parts]

/-- The two blocks of `finFourPairing a` are distinct.

This holds because `0` lies in `{0, a}` but never in its complement. -/
private lemma finFourPairing_blocks_ne (a : Fin 4) :
    ({(0 : Fin 4), a} : Finset (Fin 4)) ≠
      Finset.univ \ ({(0 : Fin 4), a} : Finset (Fin 4)) := by
  intro h
  have h0in : (0 : Fin 4) ∈ ({(0 : Fin 4), a} : Finset (Fin 4)) := by simp
  exact (Finset.mem_sdiff.mp (by rw [← h]; exact h0in)).2 h0in

/-- The block product of a pairing factors over its two blocks. -/
private lemma blockProduct_finFourPairing (f : Finset (Fin 4) → ℝ) (a : Fin 4) :
    (finFourPairing a).blockProduct f =
      f {0, a} * f (Finset.univ \ ({0, a} : Finset (Fin 4))) := by
  dsimp [Finpartition.blockProduct]
  rw [finFourPairing_parts, Finset.prod_pair (finFourPairing_blocks_ne a)]

/-- The cumulant coefficient of a pairing of `Fin 4` is `-1`. -/
private lemma cumulantCoefficient_finFourPairing (a : Fin 4) :
    (Finpartition.cumulantCoefficient (finFourPairing a) : ℝ) = -1 := by
  dsimp [Finpartition.cumulantCoefficient]
  rw [finFourPairing_parts, Finset.card_pair (finFourPairing_blocks_ne a)]
  norm_num

/-- The complementary blocks of the three pairings of `Fin 4`.

Each is checked by enumerating the four elements of `Fin 4`. -/
private lemma finFour_sdiff_pair_23 :
    (Finset.univ \ ({(0 : Fin 4), 1} : Finset (Fin 4)) : Finset (Fin 4)) =
      ({2, 3} : Finset (Fin 4)) := by
  ext i
  fin_cases i <;> simp

private lemma finFour_sdiff_pair_13 :
    (Finset.univ \ ({(0 : Fin 4), 2} : Finset (Fin 4)) : Finset (Fin 4)) =
      ({1, 3} : Finset (Fin 4)) := by
  ext i
  fin_cases i <;> simp

private lemma finFour_sdiff_pair_12 :
    (Finset.univ \ ({(0 : Fin 4), 3} : Finset (Fin 4)) : Finset (Fin 4)) =
      ({1, 2} : Finset (Fin 4)) := by
  ext i
  fin_cases i <;> simp

/-- The carrier `Fin 4` is nonempty. -/
private lemma finFour_univ_ne_empty : (Finset.univ : Finset (Fin 4)) ≠ ∅ := by
  intro h
  simpa [h] using (Finset.mem_univ (0 : Fin 4))

/-- The four positions of `Fin 4` are `0, 1, 2, 3`. -/
private lemma finFour_univ_eq_0123 :
    (Finset.univ : Finset (Fin 4)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by
  ext i
  fin_cases i <;> simp

/-- The top partition of `Fin 4` has no singleton block. -/
private lemma finFourTop_no_singleton :
    ∀ i : Fin 4, ({i} : Finset (Fin 4)) ∉
      (⊤ : Finpartition (Finset.univ : Finset (Fin 4))).parts := by
  intro i hi
  rw [top_parts_eq_singleton finFour_univ_ne_empty, Finset.mem_singleton] at hi
  have hc1 : ({i} : Finset (Fin 4)).card = 1 := by simp
  have hc2 : (Finset.univ : Finset (Fin 4)).card = 4 := by simp
  rw [hi, hc2] at hc1
  norm_num at hc1

/-- A pairing of `Fin 4` (with partner `a ≠ 0`) has no singleton block. -/
private lemma finFourPairing_no_singleton {a : Fin 4} (ha : a ≠ 0) :
    ∀ i : Fin 4, ({i} : Finset (Fin 4)) ∉ (finFourPairing a).parts := by
  intro i hi
  rw [finFourPairing_parts] at hi
  rcases Finset.mem_insert.mp hi with hi | hi
  · -- `{i} = {0, a}`: cardinality one versus two
    have hc1 : ({i} : Finset (Fin 4)).card = 1 := by simp
    have hc2 : ({(0 : Fin 4), a} : Finset (Fin 4)).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simpa [eq_comm] using ha)]
      simp
    rw [hi, hc2] at hc1
    norm_num at hc1
  · -- `{i} = univ \ {0, a}`: cardinality one versus two
    have hc1 : ({i} : Finset (Fin 4)).card = 1 := by simp
    have hc2 : ((Finset.univ : Finset (Fin 4)) \ ({(0 : Fin 4), a} : Finset (Fin 4))).card = 2 := by
      rw [Finset.card_sdiff_of_subset (by simp : ({(0 : Fin 4), a} : Finset (Fin 4)) ⊆ Finset.univ),
        Finset.card_univ, Fintype.card_fin,
        Finset.card_insert_of_notMem (by simpa using ha.symm)]
      norm_num
    rw [Finset.mem_singleton.mp hi, hc2] at hc1
    norm_num at hc1

/-- In a partition without singleton blocks, every block has at least two elements. -/
private lemma finFour_no_singleton_card_ge_two (P : Finpartition (Finset.univ : Finset (Fin 4)))
    (hno : ∀ i : Fin 4, ({i} : Finset (Fin 4)) ∉ P.parts) :
    ∀ B ∈ P.parts, 2 ≤ B.card := by
  intro B hB
  by_contra h
  have hBne : B ≠ ∅ := P.ne_empty hB
  have hBcard_ne : B.card ≠ 0 := by
    intro hc
    exact hBne (Finset.card_eq_zero.mp hc)
  have hBcard : B.card = 1 := by omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hBcard
  exact hno x (by simpa [hx] using hB)

/-- A partition of `Fin 4` with exactly two blocks and no singleton blocks is one of the three
pairings.

Informal proof: four elements split into two blocks of cardinality two (no singleton blocks).  The
block of `0` is `{0, a}` with `a ≠ 0`, and the second block is its complement, so `P` is the
pairing `finFourPairing a`; since `a ≠ 0`, the partner is `1`, `2` or `3`. -/
private lemma finFour_two_block_eq_pairing (P : Finpartition (Finset.univ : Finset (Fin 4)))
    (hno : ∀ i : Fin 4, ({i} : Finset (Fin 4)) ∉ P.parts) (hcard : P.parts.card = 2) :
    P = finFourPairing 1 ∨ P = finFourPairing 2 ∨ P = finFourPairing 3 := by
  -- the block of `0`; the remaining part is a singleton `{C}`
  have hB0_mem : P.part (0 : Fin 4) ∈ P.parts := P.part_mem.2 (by simp)
  have hrest : (P.parts.erase (P.part 0)).card = 1 := by
    rw [Finset.card_erase_of_mem hB0_mem, hcard]
  rcases Finset.card_eq_one.mp hrest with ⟨C, hC⟩
  have hparts : P.parts = insert (P.part 0) {C} := by
    rw [← Finset.insert_erase hB0_mem, hC]
  have hC_ne : C ≠ P.part 0 := by
    intro h
    have hC_erase : C ∈ P.parts.erase (P.part 0) := by rw [hC]; simp
    exact (Finset.mem_erase.mp hC_erase).1 h
  -- both blocks have cardinality two (the sum is four and each is at least two)
  have hB0_ge : 2 ≤ (P.part 0).card := finFour_no_singleton_card_ge_two P hno (P.part 0) hB0_mem
  have hC_ge : 2 ≤ C.card := finFour_no_singleton_card_ge_two P hno C (by rw [hparts]; simp)
  have hsum2 : (P.part 0).card + C.card = 4 := by
    simpa [hparts, hC_ne.symm] using P.sum_card_parts
  have hB0_card : (P.part 0).card = 2 := by omega
  have hC_card : C.card = 2 := by omega
  -- `P.part 0 = {0, a}` for a unique `a ≠ 0`
  obtain ⟨a, ha0, ha_eq⟩ : ∃ a : Fin 4, a ≠ 0 ∧ P.part 0 = ({0, a} : Finset (Fin 4)) := by
    have herase : ((P.part 0).erase 0).card = 1 := by
      rw [Finset.card_erase_of_mem (P.mem_part (by simp : (0 : Fin 4) ∈ Finset.univ)), hB0_card]
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp herase
    refine ⟨a, ?_, ?_⟩
    · -- `a ≠ 0`: otherwise `0` would lie in `(P.part 0).erase 0`
      intro ha0
      have h0a : (0 : Fin 4) ∈ (P.part 0).erase 0 := by
        rw [ha, ha0]
        simp
      exact (Finset.mem_erase.mp h0a).1 rfl
    · -- `P.part 0 = {0, a}` by reinserting `0`
      calc
        P.part 0 = insert (0 : Fin 4) ((P.part 0).erase 0) :=
          (Finset.insert_erase (P.mem_part (by simp : (0 : Fin 4) ∈ Finset.univ))).symm
        _ = insert (0 : Fin 4) {a} := by rw [ha]
        _ = ({0, a} : Finset (Fin 4)) := by simp
  -- the second block is the complement of `{0, a}`
  have hC_univ : C = Finset.univ \ ({(0 : Fin 4), a} : Finset (Fin 4)) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, by
        intro hx01
        have hx_B0 : x ∈ P.part 0 := by simpa [ha_eq] using hx01
        have hC_eq' : C = P.part 0 := P.eq_of_mem_parts (by rw [hparts]; simp) hB0_mem hx hx_B0
        exact hC_ne hC_eq'⟩
    · -- both sides have cardinality two
      rw [hC_card,
        Finset.card_sdiff_of_subset (by simp : ({(0 : Fin 4), a} : Finset (Fin 4)) ⊆ Finset.univ),
        Finset.card_univ, Fintype.card_fin]
      rw [Finset.card_insert_of_notMem (by simpa [eq_comm] using ha0)]
      norm_num
  -- assemble the parts and identify `P` with the pairing `finFourPairing a`
  have hparts_eq :
      P.parts = ({{(0 : Fin 4), a}, Finset.univ \ ({(0 : Fin 4), a} : Finset (Fin 4))} :
        Finset (Finset (Fin 4))) := by
    rw [hparts, ha_eq, hC_univ]
  have hP_eq : P = finFourPairing a := by
    apply Finpartition.ext
    simp [hparts_eq, finFourPairing_parts]
  -- `a ≠ 0`, so the partner is one of `1, 2, 3`
  have ha_cases : a = 1 ∨ a = 2 ∨ a = 3 := by
    fin_cases a
    · exact (ha0 rfl).elim
    · simp
    · simp
    · simp
  rcases ha_cases with rfl | rfl | rfl
  · exact Or.inl hP_eq
  · exact Or.inr (Or.inl hP_eq)
  · exact Or.inr (Or.inr hP_eq)

/-- A partition of `Fin 4` without singleton blocks is either the indiscrete partition `⊤` or one
of the three pairings.

Informal proof: every block has at least two elements and the blocks cover four elements, so
`P.parts` has one or two blocks.  One block forces `P = ⊤`; two blocks reduce to
`finFour_two_block_eq_pairing`. -/
private lemma finFour_no_singleton_eq_top_or_pairing
    (P : Finpartition (Finset.univ : Finset (Fin 4)))
    (hno : ∀ i : Fin 4, ({i} : Finset (Fin 4)) ∉ P.parts) :
    P = ⊤ ∨ P = finFourPairing 1 ∨ P = finFourPairing 2 ∨ P = finFourPairing 3 := by
  -- the block cardinalities sum to four and each block contributes at least two
  have hsum : ∑ B ∈ P.parts, B.card = 4 := by
    simpa using P.sum_card_parts
  have hparts_le : P.parts.card ≤ 2 := by
    have hge : ∑ B ∈ P.parts, 2 ≤ ∑ B ∈ P.parts, B.card :=
      Finset.sum_le_sum (fun B hB => finFour_no_singleton_card_ge_two P hno B hB)
    -- `∑ B ∈ P.parts, 2 = P.parts.card * 2` and the total is four, so `2 * card ≤ 4`
    have hge' : P.parts.card * 2 ≤ 4 := by
      simpa [Finset.sum_const, hsum, mul_comm] using hge
    omega
  have hparts_pos : 1 ≤ P.parts.card :=
    Finset.card_pos.mpr (P.parts_nonempty finFour_univ_ne_empty)
  have hcard_cases : P.parts.card = 1 ∨ P.parts.card = 2 := by
    interval_cases P.parts.card <;> simp
  rcases hcard_cases with hcard | hcard
  · -- exactly one block: it must be the whole set, so `P = ⊤`
    rcases Finset.card_eq_one.mp hcard with ⟨B, hB⟩
    have hB_univ : B = (Finset.univ : Finset (Fin 4)) := by
      apply Finset.eq_of_subset_of_card_le
      · exact Finset.subset_univ B
      · -- the single block `B` covers all four elements
        have hsumB : B.card = 4 := by simpa [hB] using P.sum_card_parts
        rw [hsumB]
        simp
    have hP_top : P = ⊤ := by
      apply Finpartition.ext
      rw [hB, hB_univ, top_parts_eq_singleton finFour_univ_ne_empty]
    exact Or.inl hP_top
  · -- exactly two blocks: `P` is one of the three pairings
    exact Or.inr (finFour_two_block_eq_pairing P hno hcard)

-- (unused after `by decide` golf: pairwise-distinctness of the four partitions is decidable)

/-- The singleton-free partitions of `Fin 4` are exactly `⊤` and the three pairings. -/
private lemma finFour_no_singleton_filter :
    (Finset.univ.filter fun P : Finpartition (Finset.univ : Finset (Fin 4)) ↦
      ∀ i : Fin 4, ({i} : Finset (Fin 4)) ∉ P.parts) =
    ({⊤, finFourPairing 1, finFourPairing 2, finFourPairing 3} :
      Finset (Finpartition (Finset.univ : Finset (Fin 4)))) := by
  ext P
  constructor
  · -- every singleton-free partition is one of the four listed
    intro hP
    rcases (Finset.mem_filter.mp hP) with ⟨_, hno⟩
    rcases finFour_no_singleton_eq_top_or_pairing P hno with rfl | rfl | rfl | rfl <;> simp
  · -- each of the four listed partitions is singleton-free
    intro hP
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Fin.isValue, Finset.mem_insert, Finset.mem_singleton] at hP
    rcases hP with rfl | rfl | rfl | rfl
    · exact finFourTop_no_singleton
    · exact finFourPairing_no_singleton (by decide : (1 : Fin 4) ≠ 0)
    · exact finFourPairing_no_singleton (by decide : (2 : Fin 4) ≠ 0)
    · exact finFourPairing_no_singleton (by decide : (3 : Fin 4) ≠ 0)

/-- Fourth-order cumulant expansion for any block weight whose singleton weights vanish.

This is the purely finite combinatorial core of the centered fourth-cumulant formula.  Informally,
expand `Finpartition.cumulantTransform f Finset.univ` as the sum over the 15 set partitions of
`Fin 4`, with coefficient `(-1)^(#parts-1) * (#parts-1)!`.  Any partition containing a singleton
block contributes zero because its block product contains a factor `f {i} = 0`.  A partition of a
4-element set with no singleton blocks is either the one-block partition, or one of the three
pairings `{0,1}|{2,3}`, `{0,2}|{1,3}`, and `{0,3}|{1,2}`.  The one-block coefficient is `1`, and
each two-block coefficient is `-1`, which gives exactly the displayed expression.

References for the coefficient and partition expansion: Rota's Möbius-function formula for the
partition lattice, <https://doi.org/10.1007/BF00531932>, and McCullagh--Kolassa, "Cumulants",
Scholarpedia 4(3):4699 (2009), <http://www.scholarpedia.org/article/Cumulants>. -/
lemma cumulantTransform_fin_four_of_singleton_vanish (f : Finset (Fin 4) → ℝ)
    (hsingle : ∀ i : Fin 4, f {i} = 0) :
    Finpartition.cumulantTransform f Finset.univ =
      f {0, 1, 2, 3}
      - f {0, 1} * f {2, 3}
      - f {0, 2} * f {1, 3}
      - f {0, 3} * f {1, 2} := by
  -- `Fin 4` is nonempty, so the transform is the plain sum over all partitions
  rw [Finpartition.cumulantTransform, if_neg finFour_univ_ne_empty]
  -- Step 1: partitions with a singleton block contribute zero (`f {i} = 0`)
  have hzero : ∀ P ∈ (Finset.univ.filter fun P : Finpartition (Finset.univ : Finset (Fin 4)) ↦
      ¬ ∀ i : Fin 4, ({i} : Finset (Fin 4)) ∉ P.parts),
      Finpartition.cumulantCoefficient P * P.blockProduct f = 0 := by
    intro P hP
    rcases Finset.mem_filter.mp hP with ⟨_, hnot⟩
    push Not at hnot
    rcases hnot with ⟨i, hi⟩
    simp [Finpartition.blockProduct, Finset.prod_eq_zero hi (hsingle i)]
  -- Step 2: split off the zero contribution and keep only the singleton-free partitions
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun P : Finpartition (Finset.univ : Finset (Fin 4)) ↦
      ∀ i : Fin 4, ({i} : Finset (Fin 4)) ∉ P.parts)
    (f := fun P => Finpartition.cumulantCoefficient P * P.blockProduct f),
    Finset.sum_eq_zero hzero, add_zero]
  -- Step 3: the singleton-free partitions are exactly `⊤` and the three pairings
  rw [finFour_no_singleton_filter]
  -- Step 4: the four surviving summands evaluate to the displayed expression
  have h_top : Finpartition.cumulantCoefficient (⊤ : Finpartition (Finset.univ : Finset (Fin 4))) *
      (⊤ : Finpartition (Finset.univ : Finset (Fin 4))).blockProduct f = f {0, 1, 2, 3} := by
    simp [cumulantCoefficient_top, blockProduct_top, finFour_univ_eq_0123]
  have h_p1 : Finpartition.cumulantCoefficient (finFourPairing 1) *
      (finFourPairing 1).blockProduct f = -(f {0, 1} * f {2, 3}) := by
    simp [cumulantCoefficient_finFourPairing 1, blockProduct_finFourPairing f 1,
      finFour_sdiff_pair_23]
  have h_p2 : Finpartition.cumulantCoefficient (finFourPairing 2) *
      (finFourPairing 2).blockProduct f = -(f {0, 2} * f {1, 3}) := by
    simp [cumulantCoefficient_finFourPairing 2, blockProduct_finFourPairing f 2,
      finFour_sdiff_pair_13]
  have h_p3 : Finpartition.cumulantCoefficient (finFourPairing 3) *
      (finFourPairing 3).blockProduct f = -(f {0, 3} * f {1, 2}) := by
    simp [cumulantCoefficient_finFourPairing 3, blockProduct_finFourPairing f 3,
      finFour_sdiff_pair_12]
  -- the four partitions are pairwise distinct, so the sum splits into four summands
  have h_top_not : (⊤ : Finpartition (Finset.univ : Finset (Fin 4))) ∉
      ({finFourPairing 1, finFourPairing 2, finFourPairing 3} :
        Finset (Finpartition (Finset.univ : Finset (Fin 4)))) := by
    decide
  have h_p1_not : finFourPairing 1 ∉
      ({finFourPairing 2, finFourPairing 3} :
        Finset (Finpartition (Finset.univ : Finset (Fin 4)))) := by
    decide
  have h_p2_not : finFourPairing 2 ∉
      ({finFourPairing 3} : Finset (Finpartition (Finset.univ : Finset (Fin 4)))) := by
    decide
  rw [Finset.sum_insert h_top_not, Finset.sum_insert h_p1_not, Finset.sum_insert h_p2_not,
    Finset.sum_singleton, h_top, h_p1, h_p2, h_p3]
  ring

/-- A partition of a 4-element set without singletons must be either the indiscrete partition, or
one of the 3 pairings.

Informal proof: Split the sum into partitions with and without a singleton. For a centered family,
a singleton block moment is zero, so its block product vanishes. Thus only `⊤` (coefficient one)
and the three pairings (coefficient negative one) remain. -/
lemma jointCumulant_four_of_centered_combinatorics
    (X : Fin 4 → Ω → ℝ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    Finpartition.cumulantTransform (blockMoment μ X) Finset.univ =
      blockMoment μ X {0, 1, 2, 3}
      - blockMoment μ X {0, 1} * blockMoment μ X {2, 3}
      - blockMoment μ X {0, 2} * blockMoment μ X {1, 3}
      - blockMoment μ X {0, 3} * blockMoment μ X {1, 2} := by
  have hsingle : ∀ i : Fin 4, blockMoment μ X {i} = 0 :=
    fun i => by simpa [blockMoment] using hcenter i
  simpa using cumulantTransform_fin_four_of_singleton_vanish (blockMoment μ X) hsingle

lemma blockMoment_four_eq (X : Fin 4 → Ω → ℝ) :
    blockMoment μ X {0, 1, 2, 3} = ∫ ω, X 0 ω * X 1 ω * X 2 ω * X 3 ω ∂μ := by
  dsimp [blockMoment]
  congr 1
  ext ω
  rw [← finFour_univ_eq_0123, Fin.prod_univ_four]

lemma blockMoment_pair_eq_01 (X : Fin 4 → Ω → ℝ) :
    blockMoment μ X {0, 1} = ∫ ω, X 0 ω * X 1 ω ∂μ := by
  simp [blockMoment, Finset.prod_insert, Finset.prod_singleton]

lemma blockMoment_pair_eq_23 (X : Fin 4 → Ω → ℝ) :
    blockMoment μ X {2, 3} = ∫ ω, X 2 ω * X 3 ω ∂μ := by
  simp [blockMoment, Finset.prod_insert, Finset.prod_singleton]

lemma blockMoment_pair_eq_02 (X : Fin 4 → Ω → ℝ) :
    blockMoment μ X {0, 2} = ∫ ω, X 0 ω * X 2 ω ∂μ := by
  simp [blockMoment, Finset.prod_insert, Finset.prod_singleton]

lemma blockMoment_pair_eq_13 (X : Fin 4 → Ω → ℝ) :
    blockMoment μ X {1, 3} = ∫ ω, X 1 ω * X 3 ω ∂μ := by
  simp [blockMoment, Finset.prod_insert, Finset.prod_singleton]

lemma blockMoment_pair_eq_03 (X : Fin 4 → Ω → ℝ) :
    blockMoment μ X {0, 3} = ∫ ω, X 0 ω * X 3 ω ∂μ := by
  simp [blockMoment, Finset.prod_insert, Finset.prod_singleton]

lemma blockMoment_pair_eq_12 (X : Fin 4 → Ω → ℝ) :
    blockMoment μ X {1, 2} = ∫ ω, X 1 ω * X 2 ω ∂μ := by
  simp [blockMoment, Finset.prod_insert, Finset.prod_singleton]

/-- Exact centered fourth-cumulant formula.

Informal proof: specialize the generic Möbius formula to four positions.  Every partition with a
singleton block vanishes by `hcenter`; the remaining partitions are the one four-element block and
the three partitions into two pairs.  The classification should be proved once as a finite-
partition lemma, not by enumerating terms in this probability theorem. -/
theorem jointCumulant_four_of_centered (X : Fin 4 → Ω → ℝ)
    (hcenter : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    jointCumulant μ X =
      (∫ ω, X 0 ω * X 1 ω * X 2 ω * X 3 ω ∂μ)
        - (∫ ω, X 0 ω * X 1 ω ∂μ) * (∫ ω, X 2 ω * X 3 ω ∂μ)
        - (∫ ω, X 0 ω * X 2 ω ∂μ) * (∫ ω, X 1 ω * X 3 ω ∂μ)
        - (∫ ω, X 0 ω * X 3 ω ∂μ) * (∫ ω, X 1 ω * X 2 ω ∂μ) := by
  dsimp [jointCumulant, blockCumulant]
  rw [jointCumulant_four_of_centered_combinatorics X hcenter, blockMoment_four_eq,
    blockMoment_pair_eq_01, blockMoment_pair_eq_23, blockMoment_pair_eq_02,
    blockMoment_pair_eq_13, blockMoment_pair_eq_03, blockMoment_pair_eq_12]

lemma cumulantTransform_equiv [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    {R : Type*} [CommRing R]
    (e : ι ≃ κ) (f : Finset ι → R) :
    Finpartition.cumulantTransform (fun s : Finset κ ↦ f (s.map e.symm.toEmbedding)) Finset.univ =
      Finpartition.cumulantTransform f Finset.univ := by
  classical
  let h : Finset κ → R := fun s ↦ f (s.map e.symm.toEmbedding)
  have hround : ∀ B : Finset ι, (B.map e.toEmbedding).map e.symm.toEmbedding = B := by
    intro B
    apply Finset.ext
    intro x
    simp
  have hmap := Finpartition.cumulantTransform_map e h (Finset.univ : Finset ι)
  have hmap' : Finpartition.cumulantTransform h (Finset.univ : Finset κ) =
      Finpartition.cumulantTransform
        (fun B : Finset ι ↦ h (B.map e.toEmbedding)) (Finset.univ : Finset ι) := by
    simpa using hmap
  calc
    Finpartition.cumulantTransform h (Finset.univ : Finset κ)
        = Finpartition.cumulantTransform
            (fun B : Finset ι ↦ h (B.map e.toEmbedding)) (Finset.univ : Finset ι) := hmap'
    _ = Finpartition.cumulantTransform f (Finset.univ : Finset ι) := by
          congr 1
          ext B
          simp [h, hround]

lemma blockMoment_map_equiv
    (e : ι ≃ κ) (X : ι → Ω → ℝ) (s : Finset κ) :
    blockMoment μ (fun j ↦ X (e.symm j)) s = blockMoment μ X (s.map e.symm.toEmbedding) := by
  dsimp [blockMoment]
  congr 1
  ext ω
  exact (Finset.prod_map s e.symm.toEmbedding (fun i : ι ↦ X i ω)).symm

/-- Joint cumulants are invariant under equivalences of their position types.

Informal proof: use `Finpartition.cumulantTransform_map` and `jointMoment_perm` on every block. -/
theorem jointCumulant_perm [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (X : ι → Ω → ℝ) :
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
  classical
  let a : Finset ι := P.part i
  have ha_mem : a ∈ P.parts := P.part_mem.2 (by simp)
  have hi_mem_a : i ∈ a := P.mem_part (by simp)
  let rest : R := ∏ B ∈ P.parts.erase a, g B
  have hf : P.blockProduct f = (g a + h a) * rest := by
    dsimp [Finpartition.blockProduct]
    rw [← Finset.insert_erase ha_mem]
    rw [Finset.prod_insert (Finset.notMem_erase a P.parts)]
    rw [h_add a]
    simp only [hi_mem_a, ↓reduceIte]
    congr 1
    apply Finset.prod_congr rfl
    intro B hB
    have hB_ne : B ≠ a := (Finset.mem_erase.mp hB).1
    have hB_mem : B ∈ P.parts := (Finset.mem_erase.mp hB).2
    have hiB : i ∉ B := by
      intro hiB
      exact hB_ne (P.eq_of_mem_parts hB_mem ha_mem hiB hi_mem_a)
    simp [h_add B, hiB]
  have hg : P.blockProduct g = g a * rest := by
    dsimp [Finpartition.blockProduct]
    rw [← Finset.insert_erase ha_mem]
    rw [Finset.prod_insert (Finset.notMem_erase a P.parts)]
  have hh : P.blockProduct h = h a * rest := by
    dsimp [Finpartition.blockProduct]
    rw [← Finset.insert_erase ha_mem]
    rw [Finset.prod_insert (Finset.notMem_erase a P.parts)]
    congr 1
    apply Finset.prod_congr rfl
    intro B hB
    have hB_ne : B ≠ a := (Finset.mem_erase.mp hB).1
    have hB_mem : B ∈ P.parts := (Finset.mem_erase.mp hB).2
    have hiB : i ∉ B := by
      intro hiB
      exact hB_ne (P.eq_of_mem_parts hB_mem ha_mem hiB hi_mem_a)
    exact h_id B hiB
  calc
    P.blockProduct f = (g a + h a) * rest := hf
    _ = g a * rest + h a * rest := by ring
    _ = P.blockProduct g + P.blockProduct h := by rw [hg, hh]

lemma cumulantTransform_add [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (f g h : Finset ι → R) (i : ι)
    (h_add : ∀ s, f s = if i ∈ s then g s + h s else g s)
    (h_id : ∀ s, i ∉ s → h s = g s) :
    Finpartition.cumulantTransform f Finset.univ =
      Finpartition.cumulantTransform g Finset.univ +
        Finpartition.cumulantTransform h Finset.univ := by
  classical
  by_cases huniv : (Finset.univ : Finset ι) = ∅
  · simp [Finpartition.cumulantTransform, huniv]
  · simp only [Finpartition.cumulantTransform, if_neg huniv]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro P hP
    rw [blockProduct_add P f g h i h_add h_id, mul_add]

lemma blockMoment_add_update [DecidableEq ι]
    (X : ι → Ω → ℝ) (i : ι) (Y : Ω → ℝ)
    (hX : HasFiniteJointMoments μ X)
    (hY : HasFiniteJointMoments μ (Function.update X i Y))
    (s : Finset ι) :
    blockMoment μ (Function.update X i (X i + Y)) s =
      if i ∈ s then blockMoment μ X s + blockMoment μ (Function.update X i Y) s
      else blockMoment μ X s := by
  dsimp [blockMoment]
  by_cases hi : i ∈ s
  · rw [if_pos hi]
    have hIntX : Integrable (fun ω => X i ω * ∏ j ∈ s.erase i, X j ω) μ := by
      convert hX s using 1
      ext ω
      exact Finset.mul_prod_erase s (fun j : ι => X j ω) hi
    have hIntY : Integrable
        (fun ω => (Function.update X i Y) i ω * ∏ j ∈ s.erase i, X j ω) μ := by
      convert hY s using 1
      ext ω
      rw [← Finset.mul_prod_erase s (fun j : ι => (Function.update X i Y) j ω) hi]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [hj_ne]
    calc
      ∫ ω, ∏ j ∈ s, (Function.update X i (X i + Y)) j ω ∂μ
          = ∫ ω, (X i ω + Y ω) * ∏ j ∈ s.erase i, X j ω ∂μ := by
            congr 1
            ext ω
            rw [← Finset.mul_prod_erase s (fun j : ι => (Function.update X i (X i + Y)) j ω) hi]
            have hrest :
                (∏ j ∈ s.erase i, (Function.update X i (X i + Y)) j ω) =
                  ∏ j ∈ s.erase i, X j ω := by
              apply Finset.prod_congr rfl
              intro j hj
              have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
              simp [hj_ne]
            rw [hrest]
            simp [Function.update_self]
      _ = (∫ ω, X i ω * ∏ j ∈ s.erase i, X j ω ∂μ) +
            (∫ ω, (Function.update X i Y) i ω * ∏ j ∈ s.erase i, X j ω ∂μ) := by
            rw [← MeasureTheory.integral_add hIntX hIntY]
            congr 1
            ext ω
            simp [Function.update_self, add_mul]
      _ = blockMoment μ X s + blockMoment μ (Function.update X i Y) s := by
            congr 1
            · rw [blockMoment]
              congr 1
              ext ω
              exact Finset.mul_prod_erase s (fun j : ι => X j ω) hi
            · rw [blockMoment]
              congr 1
              ext ω
              rw [← Finset.mul_prod_erase s (fun j : ι => (Function.update X i Y) j ω) hi]
              congr 1
              apply Finset.prod_congr rfl
              intro j hj
              have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
              simp [hj_ne]
  · rw [if_neg hi]
    congr 1
    ext ω
    apply Finset.prod_congr rfl
    intro j hj
    have hj_ne : j ≠ i := by
      intro hji
      exact hi (by simpa [hji] using hj)
    simp [hj_ne]

lemma blockMoment_update_not_mem [DecidableEq ι]
    (X : ι → Ω → ℝ) (i : ι) (Y : Ω → ℝ)
    (s : Finset ι) (hi : i ∉ s) :
    blockMoment μ (Function.update X i Y) s = blockMoment μ X s := by
  dsimp [blockMoment]
  congr 1
  ext ω
  apply Finset.prod_congr rfl
  intro j hj
  have hj_ne : j ≠ i := by
    intro hji
    exact hi (by simpa [hji] using hj)
  simp [hj_ne]

/-- Joint cumulants are additive in one argument when all needed moments are integrable.

Informal proof: split each block moment containing `i` with integral additivity, then distribute
through the finite Möbius sum.  Blocks not containing `i` occur identically on both sides and their
coefficients cancel by the same partition identity. -/
theorem jointCumulant_add [Fintype ι] [DecidableEq ι]
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
  classical
  let a : Finset ι := P.part i
  have ha_mem : a ∈ P.parts := P.part_mem.2 (by simp)
  have hi_mem_a : i ∈ a := P.mem_part (by simp)
  let rest : R := ∏ B ∈ P.parts.erase a, f B
  have hf : P.blockProduct (fun s => if i ∈ s then c * f s else f s) = (c * f a) * rest := by
    dsimp [Finpartition.blockProduct]
    rw [← Finset.mul_prod_erase P.parts (fun B : Finset ι => if i ∈ B then c * f B else f B) ha_mem]
    simp only [hi_mem_a, ↓reduceIte]
    congr 1
    apply Finset.prod_congr rfl
    intro B hB
    have hB_ne : B ≠ a := (Finset.mem_erase.mp hB).1
    have hB_mem : B ∈ P.parts := (Finset.mem_erase.mp hB).2
    have hiB : i ∉ B := by
      intro hiB
      exact hB_ne (P.eq_of_mem_parts hB_mem ha_mem hiB hi_mem_a)
    simp [hiB]
  have hg : P.blockProduct f = f a * rest := by
    dsimp [Finpartition.blockProduct]
    rw [← Finset.mul_prod_erase P.parts f ha_mem]
  calc
    P.blockProduct (fun s => if i ∈ s then c * f s else f s) = (c * f a) * rest := hf
    _ = c * (f a * rest) := by ring
    _ = c * P.blockProduct f := by rw [hg]

lemma cumulantTransform_smul [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (f : Finset ι → R) (c : R) (i : ι) :
    Finpartition.cumulantTransform (fun s => if i ∈ s then c * f s else f s) Finset.univ =
      c * Finpartition.cumulantTransform f Finset.univ := by
  classical
  by_cases huniv : (Finset.univ : Finset ι) = ∅
  · simp [Finpartition.cumulantTransform, huniv]
  · simp only [Finpartition.cumulantTransform, if_neg huniv]
    rw [show (∑ P : Finpartition (Finset.univ : Finset ι),
          (P.cumulantCoefficient : R) * P.blockProduct (fun s => if i ∈ s then c * f s else f s)) =
        (∑ P : Finpartition (Finset.univ : Finset ι),
          c * ((P.cumulantCoefficient : R) * P.blockProduct f)) by
      apply Finset.sum_congr rfl
      intro P hP
      rw [blockProduct_smul P f c i]
      ring]
    rw [← Finset.mul_sum Finset.univ (fun P : Finpartition (Finset.univ : Finset ι) =>
      (P.cumulantCoefficient : R) * P.blockProduct f)]

lemma blockMoment_smul_update [DecidableEq ι]
    (X : ι → Ω → ℝ) (i : ι) (c : ℝ)
    (s : Finset ι) :
    blockMoment μ (Function.update X i (c • X i)) s =
      if i ∈ s then c * blockMoment μ X s
      else blockMoment μ X s := by
  dsimp [blockMoment]
  by_cases hi : i ∈ s
  · rw [if_pos hi]
    calc
      ∫ ω, ∏ j ∈ s, (Function.update X i (c • X i)) j ω ∂μ
          = ∫ ω, (c • X i ω) * ∏ j ∈ s.erase i, X j ω ∂μ := by
            congr 1
            ext ω
            rw [← Finset.mul_prod_erase s (fun j : ι => (Function.update X i (c • X i)) j ω) hi]
            have hrest :
                (∏ j ∈ s.erase i, (Function.update X i (c • X i)) j ω) =
                  ∏ j ∈ s.erase i, X j ω := by
              apply Finset.prod_congr rfl
              intro j hj
              have hj_ne : j ≠ i := (Finset.mem_erase.mp hj).1
              simp [hj_ne]
            rw [hrest]
            simp [Function.update_self]
      _ = c * ∫ ω, X i ω * ∏ j ∈ s.erase i, X j ω ∂μ := by
            rw [← smul_eq_mul]
            rw [← MeasureTheory.integral_smul]
            congr 1
            ext ω
            simp [smul_eq_mul, mul_assoc]
      _ = c * blockMoment μ X s := by
            congr 1
            rw [blockMoment]
            congr 1
            ext ω
            exact Finset.mul_prod_erase s (fun j : ι => X j ω) hi
  · rw [if_neg hi]
    exact blockMoment_update_not_mem X i (c • X i) s hi

/-- Joint cumulants are homogeneous in one argument.

Informal proof: every block containing `i` acquires one factor `c`; finite integral and product
linearity pull that factor through the Möbius sum. -/
theorem jointCumulant_smul [Fintype ι] [DecidableEq ι]
    (X : ι → Ω → ℝ) (i : ι) (c : ℝ) :
    jointCumulant μ (Function.update X i (c • X i)) = c * jointCumulant μ X := by
  dsimp [jointCumulant, blockCumulant]
  have h := cumulantTransform_smul (blockMoment μ X) c i
  rw [← h]
  congr 1
  ext s
  exact blockMoment_smul_update X i c s

/-- Apply a matrix of coefficients to a finite family of real observables.  The first index is
the output position and the second index selects an observable in the original family. -/
def linearCombinationFamily [Fintype κ] (X : κ → Ω → ℝ) (A : ι → κ → ℝ) :
    ι → Ω → ℝ :=
  fun i ω ↦ ∑ j : κ, A i j * X j ω

/-- Joint cumulant, viewed as a multilinear map in the coefficient vectors of its arguments.

The hypothesis is deliberately stated for every coefficient matrix: `jointCumulant_add` needs
integrability both before and after replacing one row.  Exponential moments of all scalar linear
combinations imply this hypothesis by finite Hölder; see
`hasFiniteJointMoments_linearCombinationFamily_of_integrable_exp` in `Gaussian.lean`. -/
def jointCumulantMultilinearMap [Fintype ι] [DecidableEq ι] [Fintype κ]
    (X : κ → Ω → ℝ)
    (hfinite : ∀ A : ι → κ → ℝ, HasFiniteJointMoments μ (linearCombinationFamily X A)) :
    MultilinearMap ℝ (fun _ : ι ↦ κ → ℝ) ℝ :=
  MultilinearMap.mk'
    (fun A ↦ jointCumulant μ (linearCombinationFamily X A))
    (fun A i x y ↦ by
      let U := linearCombinationFamily X (Function.update A i x)
      let Y : Ω → ℝ := fun ω ↦ ∑ j : κ, y j * X j ω
      have hadd := jointCumulant_add U i Y
        (hfinite (Function.update A i x)) (by
          convert hfinite (Function.update A i y) using 1
          ext r ω
          by_cases hri : r = i
          · subst r
            simp [U, Y, linearCombinationFamily]
          · simp [U, Y, linearCombinationFamily, hri])
      have hleft :
          linearCombinationFamily X (Function.update A i (x + y)) =
            Function.update U i (U i + Y) := by
        ext r ω
        by_cases hri : r = i
        · subst r
          simp [U, Y, linearCombinationFamily, add_mul, Finset.sum_add_distrib]
        · simp [U, Y, linearCombinationFamily, hri]
      have hright :
          linearCombinationFamily X (Function.update A i y) =
            Function.update U i Y := by
        ext r ω
        by_cases hri : r = i
        · subst r
          simp [U, Y, linearCombinationFamily]
        · simp [U, Y, linearCombinationFamily, hri]
      calc
        jointCumulant μ (linearCombinationFamily X (Function.update A i (x + y))) =
            jointCumulant μ (Function.update U i (U i + Y)) := congrArg _ hleft
        _ = jointCumulant μ U + jointCumulant μ (Function.update U i Y) := hadd
        _ = jointCumulant μ (linearCombinationFamily X (Function.update A i x)) +
            jointCumulant μ (linearCombinationFamily X (Function.update A i y)) := by
              rw [hright])
    (fun A i c x ↦ by
      let U := linearCombinationFamily X (Function.update A i x)
      have hsmul := jointCumulant_smul (μ := μ) U i c
      have hleft :
          linearCombinationFamily X (Function.update A i (c • x)) =
            Function.update U i (c • U i) := by
        ext r ω
        by_cases hri : r = i
        · subst r
          simp [U, linearCombinationFamily, Finset.mul_sum, mul_assoc]
        · simp [U, linearCombinationFamily, hri]
      calc
        jointCumulant μ (linearCombinationFamily X (Function.update A i (c • x))) =
            jointCumulant μ (Function.update U i (c • U i)) := congrArg _ hleft
        _ = c * jointCumulant μ U := hsmul
        _ = c • jointCumulant μ (linearCombinationFamily X (Function.update A i x)) := rfl)

-- The joint-cumulant multilinear map is symmetric: permuting the argument coefficient vectors is
-- absorbed by the invariance of joint cumulants under equivalences of position types
-- (`jointCumulant_perm`).  Stated directly in terms of `jointCumulantMultilinearMap` (no `let`
-- binding) so that it unifies cleanly at use sites.
private lemma jointCumulantMultilinearMap_symm [Fintype ι] [DecidableEq ι] [Fintype κ]
    (X : κ → Ω → ℝ)
    (hfinite : ∀ A : ι → κ → ℝ, HasFiniteJointMoments μ (linearCombinationFamily X A))
    (e : Equiv.Perm ι) (A : ι → κ → ℝ) :
    jointCumulantMultilinearMap (μ := μ) X hfinite (fun i ↦ A (e.symm i)) =
      jointCumulantMultilinearMap (μ := μ) X hfinite A :=
  jointCumulant_perm e (linearCombinationFamily X A)

-- Applying `linearCombinationFamily` with the identity matrix (diagonal `1`s, zero elsewhere)
-- recovers the original family; this is the notation conversion that turns the basis value of the
-- multilinear map back into a joint cumulant of `X`.
omit [MeasurableSpace Ω] in
private lemma linearCombinationFamily_id_eq_self [Fintype κ] [DecidableEq κ] (X : κ → Ω → ℝ) :
    linearCombinationFamily X (fun i j : κ ↦ if i = j then (1 : ℝ) else 0) = X := by
  ext i ω
  simp [linearCombinationFamily]

private def finsetComplEquiv [Fintype ι] [DecidableEq ι] : Finset ι ≃ Finset ι where
  toFun s := sᶜ
  invFun s := sᶜ
  left_inv s := by simp
  right_inv s := by simp

private lemma polarizationCoefficient [Fintype ι] [DecidableEq ι] (r : Finset ι) :
    (∑ s : Finset ι, if r ⊆ s then
      (-1 : ℝ) ^ (Fintype.card ι - s.card) else 0) =
      if r = Finset.univ then 1 else 0 := by
  rw [← Finset.sum_filter]
  calc
    (∑ s ∈ (Finset.univ.filter (r ⊆ ·)),
        (-1 : ℝ) ^ (Fintype.card ι - s.card)) =
        ∑ t ∈ rᶜ.powerset, (-1 : ℝ) ^ t.card := by
          apply Finset.sum_equiv (@finsetComplEquiv ι _ _)
          · intro s
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_powerset]
            exact (Finset.compl_subset_compl (s := s) (t := r)).symm
          · intro s hs
            change (-1 : ℝ) ^ (Fintype.card ι - s.card) = (-1 : ℝ) ^ sᶜ.card
            rw [Finset.card_compl]
    _ = if rᶜ = ∅ then 1 else 0 := by
      exact_mod_cast Finset.sum_powerset_neg_one_pow_card (x := rᶜ)
    _ = if r = Finset.univ then 1 else 0 := by simp

/-- A symmetric finite multilinear form over `ℝ` that vanishes on the diagonal vanishes on every
tuple.

This is the vanishing form of the polarization identity.  Expanding the alternating sum of
diagonal values leaves only surjective self-maps of the argument index type.  Since the type is
finite, these are permutations; symmetry identifies all surviving summands, so the sum is
`(Fintype.card ι)! * M v`.  The factorial is nonzero over `ℝ`.

Reference: Erik G. F. Thomas, *A polarization identity for multilinear maps*, Theorem 1,
<https://arxiv.org/abs/1309.1275>. -/
theorem multilinearMap_apply_eq_zero_of_diagonal_eq_zero
    {E : Type*} [Finite ι] [AddCommMonoid E] [Module ℝ E]
    (M : MultilinearMap ℝ (fun _ : ι ↦ E) ℝ)
    (hsymm : ∀ (e : Equiv.Perm ι) (A : ι → E),
      M (fun i ↦ A (e.symm i)) = M A)
    (hdiag : ∀ a : E, M (fun _ : ι ↦ a) = 0) (v : ι → E) : M v = 0 := by
  classical
  let _ := Fintype.ofFinite ι
  let T : (ι → ι) → ℝ := fun f ↦ M (fun i ↦ v (f i))
  have hexpand (s : Finset ι) :
      M (fun _ : ι ↦ ∑ j ∈ s, v j) =
        ∑ f : ι → ι, if Finset.univ.image f ⊆ s then T f else 0 := by
    rw [M.map_sum_finset (fun _ j ↦ v j) (fun _ ↦ s)]
    have hpi : Fintype.piFinset (fun _ : ι ↦ s) =
        (Finset.univ : Finset (ι → ι)).filter
          (fun f ↦ Finset.univ.image f ⊆ s) := by
      ext f
      simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.image_subset_iff, true_implies]
    rw [hpi, Finset.sum_filter]
  have himage (f : ι → ι) :
      Finset.univ.image f = Finset.univ ↔ Function.Surjective f := by
    constructor
    · intro hf y
      have hy : y ∈ Finset.univ.image f := by simp [hf]
      simpa using hy
    · exact Finset.image_univ_of_surjective
  have hzero :
      (∑ s : Finset ι, (-1 : ℝ) ^ (Fintype.card ι - s.card) *
        M (fun _ : ι ↦ ∑ j ∈ s, v j)) = 0 := by
    simp only [hdiag, mul_zero, Finset.sum_const_zero]
  have hsurj : (∑ f : ι → ι, if Function.Surjective f then T f else 0) = 0 := by
    calc
      (∑ f : ι → ι, if Function.Surjective f then T f else 0) =
          ∑ f : ι → ι,
            (∑ s : Finset ι, if Finset.univ.image f ⊆ s then
              (-1 : ℝ) ^ (Fintype.card ι - s.card) else 0) * T f := by
            apply Finset.sum_congr rfl
            intro f hf
            simp only [polarizationCoefficient, himage, ite_mul, one_mul, zero_mul]
      _ = ∑ s : Finset ι, (-1 : ℝ) ^ (Fintype.card ι - s.card) *
          (∑ f : ι → ι, if Finset.univ.image f ⊆ s then T f else 0) := by
            simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro s hs
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro f hf
            by_cases hfs : Finset.univ.image f ⊆ s <;> simp [hfs]
      _ = ∑ s : Finset ι, (-1 : ℝ) ^ (Fintype.card ι - s.card) *
          M (fun _ : ι ↦ ∑ j ∈ s, v j) := by simp_rw [hexpand]
      _ = 0 := hzero
  let surjEquivPerm : {f : ι → ι // Function.Surjective f} ≃ Equiv.Perm ι := {
    toFun f := Equiv.ofBijective f.1 f.2.bijective_of_finite
    invFun e := ⟨e, e.surjective⟩
    left_inv f := by ext i; rfl
    right_inv e := by ext i; rfl }
  have hfactorial : ((Fintype.card ι).factorial : ℝ) * M v = 0 := by
    calc
      ((Fintype.card ι).factorial : ℝ) * M v =
          (∑ f : ι → ι, if Function.Surjective f then T f else 0) := by
        symm
        calc
          (∑ f : ι → ι, if Function.Surjective f then T f else 0) =
              ∑ f : {f : ι → ι // Function.Surjective f}, T f.1 := by
            rw [← Finset.sum_filter]
            apply Finset.sum_subtype
            intro f
            simp
          _ = ∑ e : Equiv.Perm ι, T e := by
            apply Fintype.sum_equiv surjEquivPerm
            intro f
            rfl
          _ = ∑ _e : Equiv.Perm ι, M v := by
            apply Finset.sum_congr rfl
            intro e he
            exact hsymm e.symm v
          _ = ((Fintype.card ι).factorial : ℝ) * M v := by
            simp [Fintype.card_perm]
      _ = 0 := hsurj
  have hfac : ((Fintype.card ι).factorial : ℝ) ≠ 0 := by positivity
  exact (mul_eq_zero.mp hfactorial).resolve_left hfac

/-- A finite-dimensional polarization corollary for symmetric multilinear maps on `ι → ℝ`.

If a symmetric `|ι|`-linear form vanishes on the diagonal, then its coefficient on the tuple of
standard basis vectors is zero.  This is the precise algebraic fact needed below for joint
cumulants: the matrix `(fun i j ↦ if i = j then 1 else 0)` feeds the `i`-th basis vector to the
`i`-th argument of the multilinear map.

Informal proof.  The Bochnak--Siciak/Thomas polarization identity says
`M v = (Fintype.card ι)!⁻¹ • ∑ S : Finset ι, (-1) ^ (Fintype.card ι - S.card) •
  M (fun _ ↦ ∑ i in S, v i)`
for every symmetric multilinear map `M` over `ℝ`.  Apply this to the basis tuple
`v i j = if i = j then 1 else 0`.  Each term on the right is a diagonal value, so it is zero by
`hdiag`; hence the whole sum is zero.  The symmetry hypothesis `hsymm` is exactly the invariance
under permutations used to combine the `|ι|!` surviving terms in the standard proof of the
polarization formula.

Reference: Erik G. F. Thomas, *A polarization identity for multilinear maps*, Theorem 1,
<https://arxiv.org/abs/1309.1275>. -/
theorem multilinearMap_eq_zero_on_basis_of_diagonal_eq_zero [Finite ι] [DecidableEq ι]
    (M : MultilinearMap ℝ (fun _ : ι ↦ ι → ℝ) ℝ)
    (hsymm : ∀ (e : Equiv.Perm ι) (A : ι → ι → ℝ),
      M (fun i ↦ A (e.symm i)) = M A)
    (hdiag : ∀ a : ι → ℝ, M (fun _ : ι ↦ a) = 0) :
    M (fun i j ↦ if i = j then (1 : ℝ) else 0) = 0 := by
  apply multilinearMap_apply_eq_zero_of_diagonal_eq_zero M hsymm hdiag

/-- Polarization for joint cumulants: if every repeated-variable cumulant in the linear span of
`X` vanishes, then the mixed cumulant vanishes.

Informal proof.  Under `hfinite`, `jointCumulantMultilinearMap X hfinite` is a symmetric
multilinear form.  The polarization identity for a symmetric `n`-linear form over a
characteristic-zero field expresses its value at `(x₁, …, xₙ)` as `1 / n!` times an alternating
sum of diagonal values at sums of subsets of the `xᵢ`.  Every diagonal value is zero by `hdiag`.
Symmetry is `jointCumulant_perm`, and multilinearity is packaged by
`jointCumulantMultilinearMap`.

Reference: Erik G. F. Thomas, *A polarization identity for multilinear maps*, Theorem 1,
<https://arxiv.org/abs/1309.1275>.  The paper proves the finite-difference formula over any field
whose characteristic does not divide `n!`, hence in particular over `ℝ`. -/
theorem jointCumulant_eq_zero_of_diagonal_linearCombination [Fintype ι] [DecidableEq ι]
    (X : ι → Ω → ℝ)
    (hfinite : ∀ A : ι → ι → ℝ,
      HasFiniteJointMoments μ (linearCombinationFamily X A))
    (hdiag : ∀ a : ι → ℝ,
      jointCumulant μ (fun _ : ι ↦ fun ω ↦ ∑ j : ι, a j * X j ω) = 0) :
    jointCumulant μ X = 0 := by
  let M := jointCumulantMultilinearMap X hfinite
  exact (linearCombinationFamily_id_eq_self X).symm ▸
    multilinearMap_eq_zero_on_basis_of_diagonal_eq_zero M
      (jointCumulantMultilinearMap_symm X hfinite)
      (by apply hdiag)

/-- Independence of the observables indexed by `A` from those indexed by its complement. -/
def IndepAcross (μ : Measure Ω) (X : ι → Ω → ℝ)
    (A : Finset ι) : Prop :=
  IndepFun (fun ω (i : A) ↦ X i.1 ω) (fun ω (i : {i : ι // i ∉ A}) ↦ X i.1 ω) μ

-- The product over a finset splits into the product over its intersection with `A` and its
-- complement `s \ A`; this is the finite-product form of "disjoint union".
private lemma prod_inter_mul_prod_sdiff [DecidableEq ι] (s A : Finset ι) (f : ι → ℝ) :
    (∏ i ∈ s ∩ A, f i) * (∏ i ∈ s \ A, f i) = ∏ i ∈ s, f i := by
  simpa [← Finset.filter_mem_eq_inter, ← Finset.filter_notMem_eq_sdiff] using
    Finset.prod_filter_mul_prod_filter_not s (fun i ↦ i ∈ A) f

-- Independence of the restrictions of `X` to `A` and to its complement factors the integral of
-- the product over `s` into the product of the integrals over `s ∩ A` and `s \ A`.  The
-- restriction maps and evaluation functionals are defined internally so the statement only
-- mentions integrals of plain products (no `let` leakage across definitional boundaries).
private lemma indepFun_split_integral [DecidableEq ι]
    (X : ι → Ω → ℝ) (A : Finset ι) (hmeas : ∀ i, Measurable (X i))
    (hindep : IndepAcross μ X A) (s : Finset ι) :
    (∫ ω, (∏ i ∈ s ∩ A, X i ω) * (∏ i ∈ s \ A, X i ω) ∂μ) =
      (∫ ω, ∏ i ∈ s ∩ A, X i ω ∂μ) * (∫ ω, ∏ i ∈ s \ A, X i ω ∂μ) := by
  -- `F` and `G` are the observables restricted to `A` and to its complement; independence of the
  -- two families transfers to them.
  let F : Ω → A → ℝ := fun ω i ↦ X i.1 ω
  let G : Ω → {i : ι // i ∉ A} → ℝ := fun ω i ↦ X i.1 ω
  -- `φ` and `ψ` evaluate a tuple of observables into the product over the corresponding part.
  let φ : (A → ℝ) → ℝ :=
    fun y ↦ ∏ i : {i // i ∈ s ∩ A}, y ⟨i.1, (Finset.mem_inter.mp i.2).2⟩
  let ψ : ({i : ι // i ∉ A} → ℝ) → ℝ :=
    fun y ↦ ∏ i : {i // i ∈ s \ A}, y ⟨i.1, (Finset.mem_sdiff.mp i.2).2⟩
  -- Coordinatewise measurability makes the restriction maps AEMeasurable.
  have hF : AEMeasurable F μ :=
    (measurable_pi_lambda F fun i ↦ hmeas i.1).aemeasurable
  have hG : AEMeasurable G μ :=
    (measurable_pi_lambda G fun i ↦ hmeas i.1).aemeasurable
  -- The evaluation functionals are measurable products of coordinate projections.
  have hφ : Measurable φ :=
    Finset.measurable_prod Finset.univ fun i _ ↦
      measurable_pi_apply (⟨i.1, (Finset.mem_inter.mp i.2).2⟩ : A)
  have hψ : Measurable ψ :=
    Finset.measurable_prod Finset.univ fun i _ ↦
      measurable_pi_apply (⟨i.1, (Finset.mem_sdiff.mp i.2).2⟩ : {i : ι // i ∉ A})
  have hindepFG : F ⟂ᵢ[μ] G := hindep
  -- Evaluating the functionals on the restrictions recovers the plain products.
  have hφ_eval (ω : Ω) : φ (F ω) = ∏ i ∈ s ∩ A, X i ω := by
    simpa [φ, F] using (Finset.prod_attach (s ∩ A) (fun i ↦ X i ω))
  have hψ_eval (ω : Ω) : ψ (G ω) = ∏ i ∈ s \ A, X i ω := by
    simpa [ψ, G] using (Finset.prod_attach (s \ A) (fun i ↦ X i ω))
  -- Independence factors the integral of the product of the two functionals.
  have hfactor := IndepFun.integral_fun_comp_mul_comp hindepFG hF hG
    hφ.aestronglyMeasurable hψ.aestronglyMeasurable
  simpa [hφ_eval, hψ_eval] using hfactor

lemma blockMoment_indepFun_split [DecidableEq ι]
    (X : ι → Ω → ℝ) (A : Finset ι) (_hX : HasFiniteJointMoments μ X)
    (hmeas : ∀ i, Measurable (X i)) (hindep : IndepAcross μ X A) (s : Finset ι) :
    blockMoment μ X s = blockMoment μ X (s ∩ A) * blockMoment μ X (s \ A) := by
  simpa [blockMoment, prod_inter_mul_prod_sdiff] using
    indepFun_split_integral X A hmeas hindep s

-- `f ∅` acts as an identity on the values of `f` at subsets of `A`: the split hypothesis applied
-- to such a subset `b` gives `f b = f b * f ∅`.  This is what absorbs the leftover `f ∅` factors
-- produced when a block of a partition lies entirely on one side of the cut.
private lemma split_absorb_empty_left [DecidableEq ι] {R : Type*} [CommRing R]
    (f : Finset ι → R) (A : Finset ι) (h_factor : ∀ s, f s = f (s ∩ A) * f (s \ A))
    {b : Finset ι} (hb : b ⊆ A) : f ∅ * f b = f b :=
  (mul_comm (f ∅) (f b)).trans (by
    simpa [Finset.inter_eq_left.mpr hb, Finset.sdiff_eq_empty_iff_subset.mpr hb] using
      (h_factor b).symm)

-- `f ∅` acts as an identity on the values of `f` at subsets of `univ \ A`: the mirror image of
-- `split_absorb_empty_left` for the other side of the cut.  A subset `b` of the complement misses
-- `A` entirely (`b ∩ A = ∅` and `b \ A = b`), so the split hypothesis gives `f b = f ∅ * f b`.
-- This absorbs the extra `f ∅` factors produced when a partition block lies entirely on the right
-- side of the cut.
private lemma split_absorb_empty_right [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (f : Finset ι → R) (A : Finset ι) (h_factor : ∀ s, f s = f (s ∩ A) * f (s \ A))
    {b : Finset ι} (hb : b ⊆ Finset.univ \ A) : f ∅ * f b = f b := by
  -- `b` avoids `A`, so intersecting with `A` erases `b` and subtracting `A` leaves `b` intact.
  have hb_disj : Disjoint b A := Finset.disjoint_of_subset_left hb Finset.sdiff_disjoint
  simpa [Finset.disjoint_iff_inter_eq_empty.mp hb_disj,
    Finset.sdiff_eq_self_iff_disjoint.mpr hb_disj] using (h_factor b).symm

-- Multiplying a cumulant transform of a function restricted to `A`-side subsets by `f ∅` does
-- nothing: every block of every partition is a subset of `A`, so `split_absorb_empty_left`
-- applies block by block and the sum is unchanged.
private lemma split_cumulantTransform_mul_empty [DecidableEq ι] {R : Type*} [CommRing R]
    (f : Finset ι → R) (A : Finset ι) (h_factor : ∀ s, f s = f (s ∩ A) * f (s \ A))
    (u : Finset ι) (hu : u ⊆ A) :
    f ∅ * Finpartition.cumulantTransform f u = Finpartition.cumulantTransform f u := by
  classical
  by_cases hu_empty : u = ∅
  · simp [Finpartition.cumulantTransform, hu_empty]
  · simp only [Finpartition.cumulantTransform, if_neg hu_empty]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P hP
    -- `f ∅` is absorbed by the block product because some block exists and every block is a
    -- subset of `u ⊆ A`
    calc
      f ∅ * (Finpartition.cumulantCoefficient P * P.blockProduct f)
          = Finpartition.cumulantCoefficient P * (f ∅ * P.blockProduct f) := by ring
      _ = Finpartition.cumulantCoefficient P * P.blockProduct f := by
        congr 1
        have hprod : f ∅ * P.blockProduct f = P.blockProduct f := by
          rcases P.parts_nonempty hu_empty with ⟨B0, hB0⟩
          calc
            f ∅ * P.blockProduct f
                = f ∅ * (f B0 * ∏ B ∈ P.parts.erase B0, f B) := by
                  congr 1
                  exact (Finset.mul_prod_erase P.parts f hB0).symm
            _ = (f ∅ * f B0) * ∏ B ∈ P.parts.erase B0, f B := by ring
            _ = f B0 * ∏ B ∈ P.parts.erase B0, f B := by
              congr 1
              exact split_absorb_empty_left f A h_factor
                (Finset.Subset.trans (P.subset hB0) hu)
            _ = P.blockProduct f := Finset.mul_prod_erase P.parts f hB0
        exact hprod

-- Deleting a block `B` from a partition `P` of `s`: the restricted partition `P.restrict
-- (s \ B ⊆ s)` (intersect every part with `s \ B`) has exactly the parts of `P` other than `B`.
-- This is the block-deletion step used when regrouping partitions by the block containing a
-- distinguished element.
private lemma restrict_sdiff_parts {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (P : Finpartition s) (B : Finset ι) (hB : B ∈ P.parts) :
    (P.restrict (Finset.sdiff_subset : s \ B ⊆ s)).parts = P.parts.erase B := by
  ext C
  by_cases hC : C = ∅
  · -- the empty finset is neither a part of a finpartition nor in `P.parts.erase B`
    simp [Finpartition.restrict, hC]
  · -- a nonempty trace block comes from a unique original block different from `B`
    simp only [Finpartition.restrict, Finset.inf_eq_inter', Finset.bot_eq_empty, Finset.mem_erase,
      ne_eq, hC, not_false_eq_true, Finset.mem_image, true_and]
    constructor
    · rintro ⟨D, hD, hDC⟩
      have hD_ne_B : D ≠ B := by
        intro hDB
        rw [hDB] at hDC
        have hB_inter : B ∩ (s \ B) = ∅ := by simp
        rw [hB_inter] at hDC
        exact hC hDC.symm
      -- `D ∩ (s \ B) = D` because the part `D` is disjoint from the part `B`
      have hD_sub : D ⊆ s \ B := by
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨P.subset hD hx, fun hxB =>
          hD_ne_B (P.eq_of_mem_parts hD hB hx hxB)⟩
      have hD_eq : D = C := by
        rw [← hDC]
        exact (Finset.inter_eq_left.mpr hD_sub).symm
      exact ⟨hD_eq ▸ hD_ne_B, hD_eq ▸ hD⟩
    · rintro ⟨hCneB, hCparts⟩
      -- `C` itself is the original block: `C ∩ (s \ B) = C` because `C` avoids `B`
      have hC_sub : C ⊆ s \ B := by
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨P.subset hCparts hx, fun hxB =>
          hCneB (P.eq_of_mem_parts hCparts hB hx hxB)⟩
      exact ⟨C, hCparts, Finset.inter_eq_left.mpr hC_sub⟩

-- The alternating binomial sum `∑ m, (-1)^m * p.choose m * P(m)` vanishes, where
-- `P(m) = ∏_{j < p-1} (q + (j + 1) - m)`.
--
-- This is the finite-difference step: regard `P` as the evaluation at `m` of the polynomial
-- `∏ j < p-1, (C (q + (j + 1)) - X)`, which has degree at most `p - 1` and therefore degree
-- `< p` because `hp : 0 < p`.  Expanding the `p`-th forward difference at zero gives exactly
-- this alternating binomial sum (up to the harmless global sign `(-1)^p`).
private lemma partialMatching_finiteDifference_sum_eq_zero (p q : ℕ) (hp : 0 < p) :
    (∑ m ∈ Finset.range (p + 1),
      (-1 : ℤ) ^ m * (((p.choose m : ℕ) : ℤ) *
        ∏ j ∈ Finset.range (p - 1), (((q + (j + 1) : ℕ) : ℤ) - (m : ℤ)))) = 0 := by
  let P : ℕ → ℤ := fun m =>
    ∏ j ∈ Finset.range (p - 1), (((q + (j + 1) : ℕ) : ℤ) - (m : ℤ))
  have hFiniteDifference :
      (∑ m ∈ Finset.range (p + 1),
        (-1 : ℤ) ^ m * (((p.choose m : ℕ) : ℤ) * P m)) = 0 := by
    let Q : Polynomial ℤ :=
      ∏ j ∈ Finset.range (p - 1),
        (Polynomial.C (((q + (j + 1) : ℕ) : ℤ)) - Polynomial.X)
    have hQ_eval : ∀ m : ℕ, Q.eval (m : ℤ) = P m := fun m => by
      simp [Q, P, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X]
    have hQ_degree : Q.natDegree < p := by
      have hdeg_le : Q.natDegree ≤ p - 1 := by
        calc
          Q.natDegree ≤
              ∑ j ∈ Finset.range (p - 1),
                (Polynomial.C (((q + (j + 1) : ℕ) : ℤ)) -
                  (Polynomial.X : Polynomial ℤ)).natDegree := by
            simpa [Q] using
              (Polynomial.natDegree_prod_le (Finset.range (p - 1)) fun j ↦
                Polynomial.C (((q + (j + 1) : ℕ) : ℤ)) - (Polynomial.X : Polynomial ℤ))
          _ ≤ ∑ _j ∈ Finset.range (p - 1), 1 :=
            Finset.sum_le_sum (fun j _ => by compute_degree)
          _ = p - 1 := by simp
      exact lt_of_le_of_lt hdeg_le (Nat.sub_lt hp Nat.zero_lt_one)
    have hsum_pminus :
        (∑ m ∈ Finset.range (p + 1),
          (((-1 : ℤ) ^ (p - m) * (((p.choose m : ℕ) : ℤ))) * P m)) = 0 := by
      simpa [hQ_eval, zsmul_eq_mul, mul_assoc,
        fwdDiff_iter_eq_sum_shift (1 : ℤ) Q.eval p (0 : ℤ)] using
        congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hQ_degree) (0 : ℤ)
    have hsign : ∀ m ∈ Finset.range (p + 1),
        (-1 : ℤ) ^ m = (-1 : ℤ) ^ p * (-1 : ℤ) ^ (p - m) := by
      intro m hm
      have hmul : (-1 : ℤ) ^ (p - m) * (-1 : ℤ) ^ m = (-1 : ℤ) ^ p := by
        rw [← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))]
      have hsquare : (-1 : ℤ) ^ (p - m) * (-1 : ℤ) ^ (p - m) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]
        norm_num
      rw [mul_comm, ← hmul, ← mul_assoc, hsquare, one_mul]
    calc
      (∑ m ∈ Finset.range (p + 1),
        (-1 : ℤ) ^ m * (((p.choose m : ℕ) : ℤ) * P m))
          = ∑ m ∈ Finset.range (p + 1),
              (-1 : ℤ) ^ p *
                (((-1 : ℤ) ^ (p - m) * (((p.choose m : ℕ) : ℤ))) * P m) :=
            Finset.sum_congr rfl (fun m hm => by rw [hsign m hm]; ring)
      _ = 0 := by
            rw [← Finset.mul_sum, hsum_pminus, mul_zero]
  -- Unfold the local `P` to recover the stated (inline) form of the conclusion.
  simpa [P] using hFiniteDifference

-- The factorial core of the per-term rewrite: using `q.choose m * m! * (q-m)! = q!`
-- (`Nat.choose_mul_factorial_mul_factorial`) and
-- `(q-m)! * (q-m+1).ascFactorial (p-1) = (p+q-m-1)!`
-- (`Nat.factorial_mul_ascFactorial`), the product of the binomial coefficients and factorials
-- collapses to `q! * p.choose m * (q-m+1).ascFactorial (p-1)`.
private lemma partialMatching_factorial_core (p q m : ℕ) (hp : 0 < p) (hm_le_q : m ≤ q) :
    p.choose m * q.choose m * m.factorial * (p + q - m - 1).factorial =
      q.factorial * (p.choose m * (q - m + 1).ascFactorial (p - 1)) := by
  calc
    p.choose m * q.choose m * m.factorial * (p + q - m - 1).factorial
        = p.choose m * (q.choose m * m.factorial * (q - m).factorial) *
            (q - m + 1).ascFactorial (p - 1) := by
          rw [← show (q - m).factorial * (q - m + 1).ascFactorial (p - 1) =
              (p + q - m - 1).factorial by
            rw [Nat.factorial_mul_ascFactorial (q - m) (p - 1)]
            congr 1
            omega]
          ring
    _ = p.choose m * q.factorial * (q - m + 1).ascFactorial (p - 1) := by
          rw [Nat.choose_mul_factorial_mul_factorial hm_le_q]
    _ = q.factorial * (p.choose m * (q - m + 1).ascFactorial (p - 1)) := by ring

-- Each summand of the original sum rewrites as
-- `q! * (-1)^(p+q-1) * ((-1)^m * p.choose m * P(m))`, with
-- `P(m) = ∏_{j < p-1} (q + (j+1) - m)`.
--
-- The rewrite uses `partialMatching_factorial_core` to collapse the factorial part and the sign
-- identity `(-1)^(p+q-m-1) = (-1)^(p+q-1) * (-1)^m` (the two exponents differ by `m` modulo 2).
private lemma partialMatching_summand_eq (p q m : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hpq : p ≤ q) (hm : m ∈ Finset.range (p + 1)) :
    (((((p.choose m) * (q.choose m) * m.factorial : ℕ) : ℤ) *
      ((-1 : ℤ) ^ (p + q - m - 1) *
        (((p + q - m - 1).factorial : ℕ) : ℤ)))) =
    ((q.factorial : ℕ) : ℤ) * (-1 : ℤ) ^ (p + q - 1) *
      ((-1 : ℤ) ^ m * (((p.choose m : ℕ) : ℤ) *
        ∏ j ∈ Finset.range (p - 1), (((q + (j + 1) : ℕ) : ℤ) - (m : ℤ)))) := by
  -- Here `m ≤ p ≤ q`, since `m ∈ range (p+1)`: the arithmetic side conditions for the factorial
  -- and sign rewrites below.
  have hm_le_q : m ≤ q := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)).trans hpq
  -- `P m` equals the rising factorial `(q - m + 1).ascFactorial (p - 1)`.
  have hP :
      (∏ j ∈ Finset.range (p - 1), (((q + (j + 1) : ℕ) : ℤ) - (m : ℤ))) =
        (((q - m + 1).ascFactorial (p - 1) : ℕ) : ℤ) := by
    simp only [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    refine Finset.prod_congr rfl (fun j _ => by omega)
  -- Collapse the factorial part to `q! * p.choose m * (q-m+1).ascFactorial (p-1)` (in `ℤ`).
  have hfact_core_int :
      (((p.choose m * q.choose m * m.factorial : ℕ) : ℤ) *
        (((p + q - m - 1).factorial : ℕ) : ℤ)) =
        ((q.factorial : ℕ) : ℤ) *
          (((p.choose m : ℕ) : ℤ) *
            (((q - m + 1).ascFactorial (p - 1) : ℕ) : ℤ)) := by
    exact_mod_cast partialMatching_factorial_core p q m hp hm_le_q
  -- Sign identity: the two exponents `p+q-m-1` and `p+q-1` differ by `m` modulo 2.
  have hsign :
      (-1 : ℤ) ^ (p + q - m - 1) =
        (-1 : ℤ) ^ (p + q - 1) * (-1 : ℤ) ^ m := by
    have hmul :
        (-1 : ℤ) ^ (p + q - m - 1) * (-1 : ℤ) ^ m =
          (-1 : ℤ) ^ (p + q - 1) := by
      rw [← pow_add, show p + q - m - 1 + m = p + q - 1 by omega]
    have hsquare : (-1 : ℤ) ^ m * (-1 : ℤ) ^ m = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [← hmul, mul_assoc, hsquare, mul_one]
  rw [hP]
  calc
    (((((p.choose m) * (q.choose m) * m.factorial : ℕ) : ℤ) *
      ((-1 : ℤ) ^ (p + q - m - 1) *
        (((p + q - m - 1).factorial : ℕ) : ℤ))))
        = (-1 : ℤ) ^ (p + q - m - 1) *
            (((p.choose m * q.choose m * m.factorial : ℕ) : ℤ) *
              (((p + q - m - 1).factorial : ℕ) : ℤ)) := by ring
    _ = ((q.factorial : ℕ) : ℤ) * (-1 : ℤ) ^ (p + q - 1) *
          ((-1 : ℤ) ^ m *
            (((p.choose m : ℕ) : ℤ) *
              (((q - m + 1).ascFactorial (p - 1) : ℕ) : ℤ))) := by
          rw [hsign, hfact_core_int]
          ring

/-- Integer version of the partial-matching cancellation in the ordered case `p ≤ q`.

This helper isolates the real combinatorial work needed below.  The proof is intentionally written
as the standard finite-difference reduction: after defining
`P(m) = ∏_{j < p - 1} (q + (j + 1) - m)`, the factorial identities rewrite each summand as the
constant `q! * (-1)^(p + q - 1)` times
`(-1)^m * p.choose m * P(m)`.  The latter alternating binomial sum is the `p`-th forward
difference of a polynomial of degree `< p`, hence zero.  See Speed, "Cumulants and partition
lattices", Austral. J. Statist. 25 (1983), 378--388, and Mathlib's
`Polynomial.fwdDiff_iter_eq_zero_of_degree_lt` / `fwdDiff_iter_eq_sum_shift`. -/
private lemma partialMatching_mobius_coeff_sum_eq_zero_int_of_le
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hpq : p ≤ q) :
    (∑ m ∈ Finset.range (p + 1),
      (((((p.choose m) * (q.choose m) * m.factorial : ℕ) : ℤ) *
        ((-1 : ℤ) ^ (p + q - m - 1) *
          (((p + q - m - 1).factorial : ℕ) : ℤ))))) = 0 := by
  let P : ℕ → ℤ := fun m =>
    ∏ j ∈ Finset.range (p - 1), (((q + (j + 1) : ℕ) : ℤ) - (m : ℤ))
  calc
    (∑ m ∈ Finset.range (p + 1),
      (((((p.choose m) * (q.choose m) * m.factorial : ℕ) : ℤ) *
        ((-1 : ℤ) ^ (p + q - m - 1) *
          (((p + q - m - 1).factorial : ℕ) : ℤ)))))
        = ∑ m ∈ Finset.range (p + 1),
            ((q.factorial : ℕ) : ℤ) * (-1 : ℤ) ^ (p + q - 1) *
              ((-1 : ℤ) ^ m * (((p.choose m : ℕ) : ℤ) * P m)) :=
          Finset.sum_congr rfl (fun m hm => by
            simpa [P] using partialMatching_summand_eq p q m hp hq hpq hm)
    _ = 0 := by
          rw [← Finset.mul_sum,
            show (∑ m ∈ Finset.range (p + 1),
                (-1 : ℤ) ^ m * (((p.choose m : ℕ) : ℤ) * P m)) = 0 by
              simpa [P] using partialMatching_finiteDifference_sum_eq_zero p q hp,
            mul_zero]

-- Integer-valued version of `partialMatching_mobius_coeff_sum_eq_zero` for arbitrary `p, q`.
--
-- The summand is symmetric in `p` and `q`, so `le_total` reduces the claim to the ordered helper
-- `partialMatching_mobius_coeff_sum_eq_zero_int_of_le`; in the `q ≤ p` branch the two traces are
-- swapped, since `simp` rewrites the summand by commutativity of `min`, addition, and
-- multiplication.
private lemma partialMatching_mobius_coeff_sum_eq_zero_int
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    (∑ m ∈ Finset.range (Nat.min p q + 1),
      (((((p.choose m) * (q.choose m) * m.factorial : ℕ) : ℤ) *
        ((-1 : ℤ) ^ (p + q - m - 1) *
          (((p + q - m - 1).factorial : ℕ) : ℤ))))) = 0 := by
  rcases le_total p q with hpq | hqp
  · -- Now `Nat.min p q = p`, so the range is `0, ..., p`; use the ordered integer helper.
    simpa [Nat.min_eq_left hpq] using
      partialMatching_mobius_coeff_sum_eq_zero_int_of_le p q hp hq hpq
  · -- The case `q ≤ p` is identical after swapping the two traces: the summand is symmetric in
    -- `p` and `q` (commutativity of `Nat.min`, addition, and multiplication).
    simpa [Nat.min_eq_right hqp, Nat.add_comm, mul_comm, mul_assoc] using
      partialMatching_mobius_coeff_sum_eq_zero_int_of_le q p hq hp hqp

/-- The signed Möbius coefficient of a non-trivial two-sided partial-matching fiber is zero.

For fixed nonempty traces with `p` left blocks and `q` right blocks, a partition in the fiber is
obtained by choosing a partial matching of size `m`.  This gives
`p.choose m * q.choose m * m.factorial` gluings and `p + q - m` blocks, hence the coefficient below.

Informal proof.  By symmetry assume `p ≤ q`.  Put `N = p + q` and factor the `m`-th summand as
`q! * (-1)^(N-1) * (-1)^m * p.choose m * P(m)`, where
`P(X) = ∏ j = 1..p-1 (q - X + j)` has degree `< p`.  The remaining sum is
`∑ m = 0..p, (-1)^m * p.choose m * P(m)`, which is (up to the harmless global sign) the `p`-th
forward difference of `P` at `0`; it vanishes because a `p`-th finite difference annihilates
polynomials of degree `< p`.  This is the standard finite-difference proof of the partition-lattice
fiber cancellation used in Speed, "Cumulants and partition lattices", Austral. J. Statist. 25
(1983), 378--388; see also Mathlib's `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt` in
`Mathlib/Algebra/Group/ForwardDiff.lean`. -/
private lemma partialMatching_mobius_coeff_sum_eq_zero {R : Type*} [CommRing R]
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    (∑ m ∈ Finset.range (Nat.min p q + 1),
      ((((p.choose m) * (q.choose m) * m.factorial : ℕ) : R) *
        ((-1 : R) ^ (p + q - m - 1) * ((p + q - m - 1).factorial : R)))) = 0 := by
  -- The identity is universal in the target commutative ring: prove it over `ℤ` and cast through
  -- the canonical homomorphism `ℤ → R`; the symmetry reduction to the ordered case is isolated in
  -- `partialMatching_mobius_coeff_sum_eq_zero_int`.
  simpa using congrArg ((↑) : ℤ → R) (partialMatching_mobius_coeff_sum_eq_zero_int p q hp hq)

/-- Trace-pair partial-matching regrouping for the cumulant transform.

This lemma is the missing reusable `Finpartition` API needed by the split-cumulant proof below.
It states that the defining sum over partitions of `univ` can be reindexed by the two trace
partitions on the cut `A | univ \ A`; the fiber over traces `π, σ` is the finite set of partial
matchings between `π.parts` and `σ.parts`, grouped by its size `m`.

Informal proof.  Map `P : Finpartition univ` to its restrictions to `A` and to `univ \ A`.  For
fixed traces `π, σ`, a partition in the fiber is uniquely obtained by choosing a partial matching
between trace blocks and gluing each matched pair; unmatched blocks remain pure.  A matching of size
`m` has `π.parts.card + σ.parts.card - m` blocks and there are
`π.parts.card.choose m * σ.parts.card.choose m * m.factorial` such matchings.  The split hypothesis
makes the block product of every element of the fiber equal to
`π.blockProduct f * σ.blockProduct f`; the pure-block `f ∅` factors are absorbed by the two
trace-identity hypotheses.  Expanding `Finpartition.cumulantTransform`, summing each fiber, and
using `Finpartition.cumulantCoefficient` gives exactly the displayed inner coefficient sum.

This is the classical partition-lattice regrouping used in T. P. Speed, "Cumulants and partition
lattices", Austral. J. Statist. 25 (1983), 378--388.  Future work should move the trace map and
partial-matching fiber equivalence into the `Finpartition` namespace. -/
private lemma cumulantTransform_tracePair_partialMatching_regrouping [Fintype ι]
    [DecidableEq ι] {R : Type*} [CommRing R] (f : Finset ι → R) (A : Finset ι)
    (_hA : A.Nonempty) (_hAc : (Finset.univ \ A).Nonempty)
    (_huniv_ne : (Finset.univ : Finset ι) ≠ ∅)
    (_hcompl_ne : (Finset.univ \ A : Finset ι) ≠ ∅)
    (_hcut_cover : A ∪ (Finset.univ \ A) = (Finset.univ : Finset ι))
    (_hcut_disjoint : Disjoint A (Finset.univ \ A))
    (_hcompl_subset_univ : Finset.univ \ A ⊆ (Finset.univ : Finset ι))
    (_hblock_split_compl : ∀ B : Finset ι,
      f B = f (B ∩ A) * f (B ∩ (Finset.univ \ A)))
    (_hleft_id_on_trace : ∀ ⦃B : Finset ι⦄, B ⊆ A → f B = f ∅ * f B)
    (_hright_id_on_trace : ∀ ⦃B : Finset ι⦄, B ⊆ Finset.univ \ A → f B = f ∅ * f B) :
    Finpartition.cumulantTransform f Finset.univ =
      ∑ π : Finpartition A,
        ∑ σ : Finpartition (Finset.univ \ A),
          (π.blockProduct f * σ.blockProduct f) *
            (∑ m ∈ Finset.range (Nat.min π.parts.card σ.parts.card + 1),
              ((((π.parts.card.choose m) * (σ.parts.card.choose m) * m.factorial : ℕ) : R) *
                ((-1 : R) ^ (π.parts.card + σ.parts.card - m - 1) *
                  ((π.parts.card + σ.parts.card - m - 1).factorial : R)))) := by
  have hne' : A ∪ (Finset.univ \ A) ≠ ∅ := by rw [_hcut_cover]; exact _huniv_ne
  have hkey := Finpartition.cumulantTransform_eq_sum_matching _hcut_disjoint hne' f
    _hblock_split_compl
  rwa [_hcut_cover] at hkey

private lemma cumulantTransform_split_trace_fiber_regrouping [Fintype ι]
    [DecidableEq ι] {R : Type*} [CommRing R] (f : Finset ι → R) (A : Finset ι)
    (hA : A.Nonempty) (hAc : (Finset.univ \ A).Nonempty)
    (huniv_ne : (Finset.univ : Finset ι) ≠ ∅)
    (hcompl_ne : (Finset.univ \ A : Finset ι) ≠ ∅)
    (hcut_cover : A ∪ (Finset.univ \ A) = (Finset.univ : Finset ι))
    (hcut_disjoint : Disjoint A (Finset.univ \ A))
    (hcompl_subset_univ : Finset.univ \ A ⊆ (Finset.univ : Finset ι))
    (hblock_split_compl : ∀ B : Finset ι,
      f B = f (B ∩ A) * f (B ∩ (Finset.univ \ A)))
    (hleft_id_on_trace : ∀ ⦃B : Finset ι⦄, B ⊆ A → f B = f ∅ * f B)
    (hright_id_on_trace : ∀ ⦃B : Finset ι⦄, B ⊆ Finset.univ \ A → f B = f ∅ * f B) :
    Finpartition.cumulantTransform f Finset.univ =
      ∑ π : Finpartition A,
        ∑ σ : Finpartition (Finset.univ \ A),
          (π.blockProduct f * σ.blockProduct f) *
            (∑ m ∈ Finset.range (Nat.min π.parts.card σ.parts.card + 1),
              ((((π.parts.card.choose m) * (σ.parts.card.choose m) * m.factorial : ℕ) : R) *
                ((-1 : R) ^ (π.parts.card + σ.parts.card - m - 1) *
                  ((π.parts.card + σ.parts.card - m - 1).factorial : R)))) :=
  cumulantTransform_tracePair_partialMatching_regrouping f A hA hAc huniv_ne hcompl_ne
    hcut_cover hcut_disjoint hcompl_subset_univ hblock_split_compl hleft_id_on_trace
    hright_id_on_trace

-- For fixed trace partitions `π` of `A` and `σ` of `univ \ A`, the partial-matching coefficient
-- sum vanishes: both sides of the cut are nonempty, so `π.parts` and `σ.parts` have positive
-- cardinalities, and the supplied finite-difference cancellation `hfiber_coeff_cancel` applies
-- with `p = |π.parts|` and `q = |σ.parts|`.  `f` is deliberately not a parameter: the coefficient
-- sum is independent of the block weights.
private lemma trace_fiber_coeff_cancel_eq_zero [Fintype ι] [DecidableEq ι] {R : Type*}
    [CommRing R] (A : Finset ι) (π : Finpartition A) (σ : Finpartition (Finset.univ \ A))
    (hA : A.Nonempty) (hAc : (Finset.univ \ A).Nonempty)
    (hfiber_coeff_cancel : ∀ p q : ℕ, 0 < p → 0 < q →
        (∑ m ∈ Finset.range (Nat.min p q + 1),
          ((((p.choose m) * (q.choose m) * m.factorial : ℕ) : R) *
            ((-1 : R) ^ (p + q - m - 1) * ((p + q - m - 1).factorial : R)))) = 0) :
    (∑ m ∈ Finset.range (Nat.min π.parts.card σ.parts.card + 1),
      ((((π.parts.card.choose m) * (σ.parts.card.choose m) * m.factorial : ℕ) : R) *
        ((-1 : R) ^ (π.parts.card + σ.parts.card - m - 1) *
          ((π.parts.card + σ.parts.card - m - 1).factorial : R)))) = 0 := by
  -- Nonempty sides give nonempty trace partitions, hence positive block counts; with
  -- `p = |π.parts|` and `q = |σ.parts|` both positive, the hypothesis cancels the sum.
  exact hfiber_coeff_cancel π.parts.card σ.parts.card
    (Finset.card_pos.mpr (π.parts_nonempty (Finset.ne_empty_of_mem hA.choose_spec)))
    (Finset.card_pos.mpr (σ.parts_nonempty (Finset.ne_empty_of_mem hAc.choose_spec)))

private lemma cumulantTransform_eq_zero_of_split_trace_fiber_cancel_aux [Fintype ι]
    [DecidableEq ι] {R : Type*} [CommRing R] (f : Finset ι → R) (A : Finset ι)
    (_hA : A.Nonempty) (_hAc : (Finset.univ \ A).Nonempty)
    (_huniv_ne : (Finset.univ : Finset ι) ≠ ∅)
    (_hcompl_ne : (Finset.univ \ A : Finset ι) ≠ ∅)
    (_hcut_cover : A ∪ (Finset.univ \ A) = (Finset.univ : Finset ι))
    (_hcut_disjoint : Disjoint A (Finset.univ \ A))
    (_hcompl_subset_univ : Finset.univ \ A ⊆ (Finset.univ : Finset ι))
    (_hblock_split_compl : ∀ B : Finset ι,
      f B = f (B ∩ A) * f (B ∩ (Finset.univ \ A)))
    (_hleft_id_on_trace : ∀ ⦃B : Finset ι⦄, B ⊆ A → f B = f ∅ * f B)
    (_hright_id_on_trace : ∀ ⦃B : Finset ι⦄, B ⊆ Finset.univ \ A → f B = f ∅ * f B)
    (_hfiber_coeff_cancel : ∀ p q : ℕ, 0 < p → 0 < q →
        (∑ m ∈ Finset.range (Nat.min p q + 1),
          ((((p.choose m) * (q.choose m) * m.factorial : ℕ) : R) *
            ((-1 : R) ^ (p + q - m - 1) * ((p + q - m - 1).factorial : R)))) = 0) :
    Finpartition.cumulantTransform f Finset.univ = 0 :=
  -- First reindex the cumulant sum by the two trace partitions.  The hard combinatorial content
  -- is isolated in `cumulantTransform_split_trace_fiber_regrouping`: after fixing traces `π, σ`,
  -- all terms have the same block-product factor and the remaining fiber coefficient is the
  -- partial-matching sum below.  Every trace partition of a nonempty side has a positive number of
  -- blocks, so the supplied finite-difference cancellation applies fiber by fiber.
  (cumulantTransform_split_trace_fiber_regrouping f A _hA _hAc _huniv_ne _hcompl_ne
    _hcut_cover _hcut_disjoint _hcompl_subset_univ _hblock_split_compl _hleft_id_on_trace
    _hright_id_on_trace).trans
    (Finset.sum_eq_zero (fun π _ => Finset.sum_eq_zero (fun σ _ => by
      rw [trace_fiber_coeff_cancel_eq_zero A π σ _hA _hAc _hfiber_coeff_cancel, mul_zero])))

-- The two sides `A` and `univ \ A` of a cut form a disjoint cover of `univ`, and the complement is
-- a subset of `univ`.  These three set-theoretic facts are always used together: they package the
-- "genuine cut" setup needed to form the trace partitions on both sides of the split.
private lemma cut_cover_disjoint_subset [Fintype ι] [DecidableEq ι] (A : Finset ι) :
    A ∪ (Finset.univ \ A) = (Finset.univ : Finset ι) ∧
      Disjoint A (Finset.univ \ A) ∧
      Finset.univ \ A ⊆ (Finset.univ : Finset ι) := by
  -- The three facts are the Boolean-algebra identities `A ∪ Aᶜ = univ`, `Disjoint A Aᶜ`,
  -- `Aᶜ ⊆ univ` (with `univ \ A = Aᶜ` by definition).
  simp [Finset.disjoint_sdiff]

-- Rewrite the split hypothesis `f s = f (s ∩ A) * f (s \ A)` in terms of the named complement
-- `univ \ A`: for every block `B` we have `B \ A = B ∩ (univ \ A)`, so `f B` factors into its
-- `A`-restriction and its `(univ \ A)`-restriction.
private lemma block_split_compl [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (f : Finset ι → R) (A : Finset ι) (h_factor : ∀ s, f s = f (s ∩ A) * f (s \ A)) :
    ∀ B : Finset ι, f B = f (B ∩ A) * f (B ∩ (Finset.univ \ A)) :=
  -- `B \ A = B ∩ (univ \ A)` is the set-theoretic conversion between the two notations.
  fun B => by simpa [Finset.sdiff_eq_inter_compl] using h_factor B

private lemma cumulantTransform_eq_zero_of_split_trace_fiber_cancel_core [Fintype ι]
    [DecidableEq ι] {R : Type*} [CommRing R] (f : Finset ι → R) (A : Finset ι)
    (_hA : A.Nonempty) (_hAc : (Finset.univ \ A).Nonempty)
    (_h_factor : ∀ s, f s = f (s ∩ A) * f (s \ A))
    (_huniv_ne : (Finset.univ : Finset ι) ≠ ∅)
    (_hcompl_ne : (Finset.univ \ A : Finset ι) ≠ ∅)
    (_hleft_absorb : ∀ ⦃b : Finset ι⦄, b ⊆ A → f ∅ * f b = f b)
    (_hright_absorb : ∀ ⦃b : Finset ι⦄, b ⊆ Finset.univ \ A → f ∅ * f b = f b) :
    Finpartition.cumulantTransform f Finset.univ = 0 :=
  -- The two sides form a genuine non-trivial cut of `univ`: they cover `univ`, are disjoint, and
  -- the complement is a subset of `univ`.  `block_split_compl` rewrites the split hypothesis using
  -- the named complement, and the absorption hypotheses remove the harmless `f ∅` factors from
  -- pure-side trace blocks; the remaining fiber Möbius coefficients cancel by
  -- `partialMatching_mobius_coeff_sum_eq_zero`.
  let hcut := cut_cover_disjoint_subset A
  cumulantTransform_eq_zero_of_split_trace_fiber_cancel_aux f A _hA _hAc _huniv_ne
    _hcompl_ne hcut.1 hcut.2.1 hcut.2.2 (block_split_compl f A _h_factor)
    (fun _ hB => (_hleft_absorb hB).symm) (fun _ hB => (_hright_absorb hB).symm)
    partialMatching_mobius_coeff_sum_eq_zero

/-- Trace-fiber cancellation for split block weights.

This is the reusable combinatorial API missing from Mathlib/project `Finpartition` at the moment.
It packages the three ingredients used below:

1. Restrict a partition of `univ` to the two sides of the cut `A | univ \ A`, discarding empty
   traces.  This gives a pair of nonempty trace partitions because both sides of the cut are
   nonempty.
2. For fixed trace partitions with `p` and `q` blocks, identify the fiber of the restriction map
   with partial matchings between the two block sets.  A matching with `m` glued pairs contributes
   `p + q - m` blocks.
3. Use `h_factor` and `split_absorb_empty_left` to show that the block product is constant on each
   trace fiber, and use the finite-difference identity
   `∑ m, (p.choose m) * (q.choose m) * m! * (-1)^(p+q-m-1) * (p+q-m-1)! = 0`
   for `p,q ≥ 1` to cancel the total Möbius coefficient of that fiber.

Informal references: T. P. Speed, "Cumulants and partition lattices", Austral. J. Statist. 25
(1983), 378--388; the standard partition-lattice proof of vanishing mixed cumulants under an
independence split.  A formal proof should expose the trace restriction/fiber matching bijection as
`Finpartition` API and prove the displayed coefficient identity from
`fwdDiff_iter_sum_mul_pow_eq_zero`. -/
private lemma cumulantTransform_eq_zero_of_split_trace_fiber [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (f : Finset ι → R) (A : Finset ι)
    (hA : A.Nonempty) (hAc : (Finset.univ \ A).Nonempty)
    (h_factor : ∀ s, f s = f (s ∩ A) * f (s \ A)) :
    Finpartition.cumulantTransform f Finset.univ = 0 :=
  cumulantTransform_eq_zero_of_split_trace_fiber_cancel_core f A hA hAc h_factor
    (Finset.ne_empty_of_mem (Finset.mem_univ hA.choose))
    (Finset.ne_empty_of_mem hAc.choose_spec)
    (fun _ hb => split_absorb_empty_left f A h_factor hb)
    (fun _ hb => split_absorb_empty_right f A h_factor hb)

/-- Möbius cancellation for one trace fiber in the split cumulant proof.

This helper is deliberately stated at the level needed by
`cumulantTransform_eq_zero_of_split_trace_fiber`: besides the split hypothesis it receives the two
nonemptiness facts and the two absorption lemmas that the caller proves explicitly.  Its informal
proof is the standard trace-fiber argument.  For a partition `P` of `univ`, restrict its blocks to
`A` and to `univ \ A`, erasing empty intersections, obtaining trace partitions `π` and `σ`.  For
fixed traces, the fiber is equivalent to partial matchings between the blocks of `π` and `σ`; a
matching of size `m` glues `m` pairs and gives `|π.parts| + |σ.parts| - m` blocks.  The split
hypothesis factors every glued block, and the supplied absorption lemmas remove the extra `f ∅`
factors from unmatched pure-side blocks, so the block product is constant on that fiber.  The
remaining coefficient is

`∑ m, (p.choose m) * (q.choose m) * m! * (-1)^(p+q-m-1) * (p+q-m-1)!`,

where `p = |π.parts|` and `q = |σ.parts|`; since both sides of the cut are nonempty, `p,q ≥ 1`.
After assuming `p ≤ q`, this is a `p`-th finite difference of a polynomial of degree `< p`, hence
zero by Mathlib's `fwdDiff_iter_sum_mul_pow_eq_zero` (equivalently
`fwdDiff_iter_eq_sum_shift`).  Summing the zero contribution over all trace pairs proves the whole
cumulant sum is zero.

References: T. P. Speed, "Cumulants and partition lattices", Austral. J. Statist. 25 (1983),
378--388; and the finite-difference identity formalized in
`Mathlib/Algebra/Group/ForwardDiff.lean`. -/
private lemma cumulantTransform_eq_zero_of_split_trace_fiber_cancel [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (f : Finset ι → R) (A : Finset ι)
    (_hA : A.Nonempty) (_hAc : (Finset.univ \ A).Nonempty)
    (_h_factor : ∀ s, f s = f (s ∩ A) * f (s \ A))
    (_huniv_ne : (Finset.univ : Finset ι) ≠ ∅)
    (_hcompl_ne : (Finset.univ \ A : Finset ι) ≠ ∅)
    (_hleft_absorb : ∀ ⦃b : Finset ι⦄, b ⊆ A → f ∅ * f b = f b)
    (_hright_absorb : ∀ ⦃b : Finset ι⦄, b ⊆ Finset.univ \ A → f ∅ * f b = f b) :
    Finpartition.cumulantTransform f Finset.univ = 0 :=
  cumulantTransform_eq_zero_of_split_trace_fiber_cancel_core f A _hA _hAc _h_factor
    _huniv_ne _hcompl_ne _hleft_absorb _hright_absorb

/-- Möbius cancellation for a set function that factors across a non-trivial cut.

Informal proof.  For a partition `P` of `univ`, take the nonempty traces of each block on
`A` and on `univ \ A`.  These traces are partitions `π` of `A` and `σ` of `univ \ A`.  The
hypothesis factors each block weight, and the special cases where a block lies entirely on one
side use the same hypothesis on that block to absorb the extra factors of `f ∅`.  Thus the block
product depends only on `(π, σ)`.  The fiber over fixed trace partitions with `p = |π.parts|` and
`q = |σ.parts|` is the set of matchings between the `p` left blocks and `q` right blocks: matching
`m` pairs glues those pairs and leaves the other blocks unmatched, so the resulting partition has
`p + q - m` blocks.  Hence the total Möbius coefficient of the fiber is

`∑ m, (p.choose m) * (q.choose m) * m! * (-1)^(p+q-m-1) * (p+q-m-1)!`.

Since `hA` and `hAc` force `p,q ≥ 1`, this sum is zero by the standard finite-difference identity
`∑ m=0..p (-1)^m * (p.choose m) * Q(m) = 0` for every polynomial `Q` of degree `< p` (after
assuming `p ≤ q` and taking `Q(m) = (p+q-m-1)!/(q-m)!`).  Therefore every trace fiber contributes
zero, and the whole cumulant sum is zero.  This is the classical partition-lattice proof that mixed
cumulants of independent blocks vanish; see T. P. Speed, "Cumulants and partition lattices",
Austral. J. Statist. 25 (1983), 378--388, and the "Cumulant" article on Wikipedia.

TODO: formalize the trace-partition/matching bijection and the finite-difference coefficient
identity as reusable `Finpartition` API. -/
private lemma cumulantTransform_eq_zero_of_split_mobius [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (f : Finset ι → R) (A : Finset ι)
    (hA : A.Nonempty) (hAc : (Finset.univ \ A).Nonempty)
    (h_factor : ∀ s, f s = f (s ∩ A) * f (s \ A)) :
    Finpartition.cumulantTransform f Finset.univ = 0 :=
  cumulantTransform_eq_zero_of_split_trace_fiber f A hA hAc h_factor

lemma cumulantTransform_eq_zero_of_split [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (f : Finset ι → R) (A : Finset ι) (hA : A.Nonempty) (hAc : (Finset.univ \ A).Nonempty)
    (h_factor : ∀ s, f s = f (s ∩ A) * f (s \ A)) :
    Finpartition.cumulantTransform f Finset.univ = 0 :=
  cumulantTransform_eq_zero_of_split_mobius f A hA hAc h_factor

/-- A joint cumulant vanishes when its positions split into two nonempty independent blocks.

Informal proof: independence factors every mixed block moment into its two restrictions.  Insert
those factorizations into the Möbius formula; Möbius inversion on the product of the two partition
lattices makes the total coefficient zero. -/
theorem jointCumulant_eq_zero_of_indepFun_split [Fintype ι] [DecidableEq ι]
    (X : ι → Ω → ℝ) (A : Finset ι)
    (hA : A.Nonempty) (hAc : (Finset.univ \ A).Nonempty)
    (hX : HasFiniteJointMoments μ X) (hmeas : ∀ i, Measurable (X i))
    (hindep : IndepAcross μ X A) :
    jointCumulant μ X = 0 :=
  cumulantTransform_eq_zero_of_split (blockMoment μ X) A hA hAc
    (blockMoment_indepFun_split X A hX hmeas hindep)

/-- The scalar cumulant is the derivative of the cumulant-generating function at zero. -/
def cumulant (μ : Measure Ω) (X : Ω → ℝ) (n : ℕ) : ℝ :=
  iteratedDeriv n (cgf X μ) 0

/-- The block moment of a constant variable function evaluates to the expected value of $X$
raised to the power of the block size.

Informal proof: The product over $B$ of $X$ is $X^{|B|}$. So the block moment is exactly the
expectation of $X^{|B|}$. -/
lemma blockMoment_const_eq_integral_pow
    (X : Ω → ℝ) (n : ℕ) (s : Finset (Fin n)) :
    blockMoment μ (fun _ : Fin n ↦ X) s = ∫ ω, X ω ^ s.card ∂μ := by
  dsimp [blockMoment]
  congr 1
  ext ω
  rw [Finset.prod_const]

/-- The $k$-th derivative of the MGF at zero is the $k$-th moment.
Informal proof: Differentiate under the integral sign $k$ times and evaluate at $t=0$. -/
lemma iteratedDeriv_mgf_zero_eq_moment (X : Ω → ℝ) (k : ℕ)
    (hmgf : 0 ∈ interior (integrableExpSet X μ)) :
    iteratedDeriv k (mgf X μ) 0 = ∫ ω, X ω ^ k ∂μ := by
  simpa using ProbabilityTheory.iteratedDeriv_mgf_zero hmgf k

/-- The `(k + 1)`-st derivative of `Real.log` at `1` equals `(-1)^k * k!`.

This is the classical `deriv^[k] (1/x)` computation: `deriv log = Inv.inv`, and
`iter_deriv_inv` gives `deriv^[k] Inv.inv x = (-1)^k * k! * x^(-1-k)`, evaluated at `x = 1`. -/
private lemma iteratedDeriv_log_one (k : ℕ) :
    iteratedDeriv (k + 1) Real.log 1 = (-1 : ℝ) ^ k * (k.factorial : ℝ) := by
  rw [iteratedDeriv_eq_iterate, Function.iterate_succ_apply, Real.deriv_log',
    iter_deriv_inv k 1]
  simp

/-- The `k`-th derivative of `Real.log` at `1`, for `k ≥ 1`. -/
private lemma iteratedDeriv_log_one_of_pos {k : ℕ} (hk : 0 < k) :
    iteratedDeriv k Real.log 1 = (-1 : ℝ) ^ (k - 1) * ((k - 1).factorial : ℝ) := by
  simpa [Nat.sub_add_cancel hk] using iteratedDeriv_log_one (k - 1)

namespace OrderedFinpartition

variable {n : ℕ}

/-- The finite partition of `Finset.univ : Finset (Fin n)` obtained from an ordered
finpartition by forgetting the ordering of its parts.  Each part of the ordered finpartition is
sent to the finset `{emb m r | r}`. -/
noncomputable def toFinpartition (n : ℕ) (c : OrderedFinpartition n) :
    Finpartition (Finset.univ : Finset (Fin n)) := by
  let parts : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin c.length)).image (fun m : Fin c.length =>
      (Finset.univ : Finset (Fin (c.partSize m))).image (c.emb m))
  refine Finpartition.ofExistsUnique parts (fun A hA => Finset.subset_univ A) ?_ ?_
  · intro a ha
    rcases c.cover a with ⟨m, r, hr⟩
    refine ⟨(Finset.univ : Finset (Fin (c.partSize m))).image (c.emb m), ?_, ?_⟩
    · constructor
      · exact Finset.mem_image.mpr ⟨m, Finset.mem_univ m, rfl⟩
      · exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, hr⟩
    · intro t ht
      rcases ht with ⟨ht_mem, hat⟩
      rcases Finset.mem_image.mp ht_mem with ⟨m', hm', rfl⟩
      rcases Finset.mem_image.mp hat with ⟨r', hr', hr'eq⟩
      have hm_eq : m = m' := by
        by_contra hne
        have hdisj : Disjoint (Set.range (c.emb m)) (Set.range (c.emb m')) :=
          c.disjoint (Set.mem_univ m) (Set.mem_univ m') hne
        exact (Set.disjoint_iff_forall_ne.mp hdisj) (show a ∈ Set.range (c.emb m) from ⟨r, hr⟩)
          (show a ∈ Set.range (c.emb m') from ⟨r', hr'eq⟩) rfl
      subst hm_eq
      rfl
  · intro hmem
    rcases Finset.mem_image.mp hmem with ⟨m, hm, himg⟩
    have hne : ((Finset.univ : Finset (Fin (c.partSize m))).image (c.emb m)).Nonempty := by
      exact ⟨c.emb m ⟨0, c.partSize_pos m⟩,
        Finset.mem_image.mpr ⟨⟨0, c.partSize_pos m⟩, Finset.mem_univ _, rfl⟩⟩
    rw [himg] at hne
    exact Finset.not_nonempty_empty hne

/-- The maximum element of a part of a finite partition of `Finset.univ`. -/
noncomputable def maxOfPart (P : Finpartition (Finset.univ : Finset (Fin n))) :
    {A : Finset (Fin n) // A ∈ P.parts} → Fin n := fun A =>
  A.1.max' (P.nonempty_of_mem_parts A.2)

/-- Distinct parts have distinct maxima. -/
lemma maxOfPart_injective (P : Finpartition (Finset.univ : Finset (Fin n))) :
    Function.Injective (maxOfPart P) := by
  intro A B hAB
  apply Subtype.ext
  by_contra hne
  have hdisj : Disjoint A.1 B.1 := P.disjoint A.2 B.2 hne
  have hmemA : A.1.max' (P.nonempty_of_mem_parts A.2) ∈ A.1 :=
    Finset.max'_mem A.1 (P.nonempty_of_mem_parts A.2)
  have hmemB' : A.1.max' (P.nonempty_of_mem_parts A.2) ∈ B.1 := by
    dsimp [maxOfPart] at hAB
    rw [hAB]
    exact Finset.max'_mem B.1 (P.nonempty_of_mem_parts B.2)
  exact (Finset.disjoint_left.mp hdisj) hmemA hmemB'

/-- The part of `P` whose maximum is `v`, for `v` the maximum of some part. -/
noncomputable def partOfMax (P : Finpartition (Finset.univ : Finset (Fin n))) (v : Fin n) :
    Finset (Fin n) := by
  classical
  by_cases hv : v ∈ (P.parts.attach.image (maxOfPart P))
  · exact (Classical.choose (Finset.mem_image.mp hv)).1
  · exact ∅

/-- `partOfMax` sends a maximum element back to a part of `P`. -/
lemma partOfMax_mem (P : Finpartition (Finset.univ : Finset (Fin n))) {v : Fin n}
    (hv : v ∈ (P.parts.attach.image (maxOfPart P))) : partOfMax P v ∈ P.parts := by
  dsimp [partOfMax]
  rw [dif_pos hv]
  exact (Classical.choose (Finset.mem_image.mp hv)).2

/-- `partOfMax` is a right inverse of `maxOfPart` on the image. -/
lemma partOfMax_maxOfPart (P : Finpartition (Finset.univ : Finset (Fin n))) {v : Fin n}
    (hv : v ∈ (P.parts.attach.image (maxOfPart P))) :
    maxOfPart P ⟨partOfMax P v, partOfMax_mem P hv⟩ = v := by
  have hsub : (⟨partOfMax P v, partOfMax_mem P hv⟩ : {A : Finset (Fin n) // A ∈ P.parts}) =
      Classical.choose (Finset.mem_image.mp hv) := by
    apply Subtype.ext
    dsimp [partOfMax]
    rw [dif_pos hv]
  simpa [hsub] using (Classical.choose_spec (Finset.mem_image.mp hv)).2

/-- `partOfMax` is a left inverse of `maxOfPart` on the parts. -/
lemma partOfMax_eq_of_mem (P : Finpartition (Finset.univ : Finset (Fin n)))
    {A : Finset (Fin n)} (hA : A ∈ P.parts) : partOfMax P (maxOfPart P ⟨A, hA⟩) = A := by
  let v : Fin n := maxOfPart P ⟨A, hA⟩
  have hv : v ∈ (P.parts.attach.image (maxOfPart P)) :=
    Finset.mem_image.mpr ⟨⟨A, hA⟩, Finset.mem_attach (P.parts) ⟨A, hA⟩, rfl⟩
  have hsub : (⟨partOfMax P v, partOfMax_mem P hv⟩ :
      {A : Finset (Fin n) // A ∈ P.parts}) = ⟨A, hA⟩ :=
    (maxOfPart_injective P) (by
      simpa [v] using partOfMax_maxOfPart P hv)
  exact congrArg Subtype.val hsub

/-- The maxima of the parts of `P`, sorted increasingly. -/
noncomputable def maxes (P : Finpartition (Finset.univ : Finset (Fin n))) : List (Fin n) :=
  (P.parts.attach.image (maxOfPart P)).sort (· ≤ ·)

lemma maxes_length (P : Finpartition (Finset.univ : Finset (Fin n))) :
    (maxes P).length = P.parts.card := by
  rw [maxes, Finset.length_sort, Finset.card_image_of_injective (P.parts.attach)
    (maxOfPart_injective P), Finset.card_attach]

lemma maxes_sorted (P : Finpartition (Finset.univ : Finset (Fin n))) :
    (maxes P).SortedLT :=
  Finset.sortedLT_sort (P.parts.attach.image (maxOfPart P))

lemma maxes_nodup (P : Finpartition (Finset.univ : Finset (Fin n))) :
    (maxes P).Nodup :=
  Finset.sort_nodup _ _

/-- Elements of the sorted list of maxima are maxima of some part. -/
lemma maxes_mem_image (P : Finpartition (Finset.univ : Finset (Fin n))) (v : Fin n) :
    v ∈ maxes P → v ∈ (P.parts.attach.image (maxOfPart P)) := by
  simp [maxes]

/-- The parts of a finite partition of `Finset.univ`, sorted by increasing maximum element and
indexed by `Fin (P.parts.card)`. -/
noncomputable def sortedParts (P : Finpartition (Finset.univ : Finset (Fin n))) :
    Fin (P.parts.card) → Finset (Fin n) := fun m =>
  partOfMax P ((maxes P).get ⟨m.1, by
    rw [maxes_length P]
    exact m.2⟩)

/-- Each sorted part is indeed a part of `P`. -/
lemma sortedParts_mem (P : Finpartition (Finset.univ : Finset (Fin n)))
    (m : Fin (P.parts.card)) : sortedParts P m ∈ P.parts := by
  simpa [sortedParts] using partOfMax_mem P (maxes_mem_image P ((maxes P).get ⟨m.1, by
    rw [maxes_length P]; exact m.2⟩)
    (List.get_mem (maxes P) ⟨m.1, by rw [maxes_length P]; exact m.2⟩))

/-- Sorting parts by maximum is injective: distinct indices give distinct parts. -/
lemma sortedParts_injective (P : Finpartition (Finset.univ : Finset (Fin n))) :
    Function.Injective (sortedParts P) := by
  intro m m' hmm
  apply Fin.ext
  let im : Fin (maxes P).length := ⟨m.1, by rw [maxes_length P]; exact m.2⟩
  let im' : Fin (maxes P).length := ⟨m'.1, by rw [maxes_length P]; exact m'.2⟩
  let x₁ : Fin n := (maxes P).get im
  let x₂ : Fin n := (maxes P).get im'
  let h₁ : x₁ ∈ (P.parts.attach.image (maxOfPart P)) := by
    apply maxes_mem_image
    simp [x₁]
  let h₂ : x₂ ∈ (P.parts.attach.image (maxOfPart P)) := by
    apply maxes_mem_image
    simp [x₂]
  have hx : partOfMax P x₁ = partOfMax P x₂ := by
    simpa [sortedParts, x₁, x₂] using hmm
  have hm' : maxOfPart P ⟨partOfMax P x₁, partOfMax_mem P h₁⟩ =
      maxOfPart P ⟨partOfMax P x₂, partOfMax_mem P h₂⟩ := by
    apply congrArg (maxOfPart P)
    apply Subtype.ext
    simpa [h₁, h₂] using hx
  have hleft : maxOfPart P ⟨partOfMax P x₁, partOfMax_mem P h₁⟩ = x₁ :=
    partOfMax_maxOfPart P h₁
  have hright : maxOfPart P ⟨partOfMax P x₂, partOfMax_mem P h₂⟩ = x₂ :=
    partOfMax_maxOfPart P h₂
  have hx12 : x₁ = x₂ := (hleft.symm.trans hm').trans hright
  have hget : (maxes P).get ⟨m.1, by rw [maxes_length P]; exact m.2⟩ =
      (maxes P).get ⟨m'.1, by rw [maxes_length P]; exact m'.2⟩ := by
    simpa [x₁, x₂] using hx12
  exact congrArg (fun k : Fin (maxes P).length => k.val)
    ((List.Nodup.injective_get (maxes_nodup P)) hget)

/-- Every part of `P` appears among the sorted parts. -/
lemma sortedParts_surj (P : Finpartition (Finset.univ : Finset (Fin n))) :
    ∀ A ∈ P.parts, ∃ m : Fin (P.parts.card), sortedParts P m = A := by
  classical
  intro A hA
  let v : Fin n := maxOfPart P ⟨A, hA⟩
  have hv : v ∈ (P.parts.attach.image (maxOfPart P)) :=
    Finset.mem_image.mpr ⟨⟨A, hA⟩, Finset.mem_attach (P.parts) ⟨A, hA⟩, rfl⟩
  have hmem : v ∈ maxes P := by simpa [maxes] using hv
  rcases List.mem_iff_get.1 hmem with ⟨i, hi⟩
  let m : Fin (P.parts.card) := i.cast (maxes_length P)
  refine ⟨m, ?_⟩
  change partOfMax P ((maxes P).get ⟨m.1, by rw [maxes_length P]; exact m.2⟩) = A
  have hfin : (⟨m.1, by rw [maxes_length P]; exact m.2⟩ : Fin (maxes P).length) = i := rfl
  have hget : (maxes P).get ⟨m.1, by rw [maxes_length P]; exact m.2⟩ = v := by
    rw [hfin, hi]
  rw [hget]
  exact partOfMax_eq_of_mem P hA

/-- The maximum of `sortedParts P m` is the `m`-th sorted maximum. -/
lemma sortedParts_max (P : Finpartition (Finset.univ : Finset (Fin n)))
    (m : Fin (P.parts.card)) :
    (sortedParts P m).max' (P.nonempty_of_mem_parts (sortedParts_mem P m)) =
      (maxes P).get ⟨m.1, by rw [maxes_length P]; exact m.2⟩ := by
  have hv : (maxes P).get ⟨m.1, by rw [maxes_length P]; exact m.2⟩ ∈
      (P.parts.attach.image (maxOfPart P)) :=
    maxes_mem_image P _ (List.get_mem (maxes P) ⟨m.1, by rw [maxes_length P]; exact m.2⟩)
  rw [← show maxOfPart P ⟨sortedParts P m, sortedParts_mem P m⟩ =
      (sortedParts P m).max' (P.nonempty_of_mem_parts (sortedParts_mem P m)) by rfl,
    show (⟨sortedParts P m, sortedParts_mem P m⟩ : {A : Finset (Fin n) // A ∈ P.parts}) =
      ⟨partOfMax P ((maxes P).get ⟨m.1, by rw [maxes_length P]; exact m.2⟩),
        partOfMax_mem P hv⟩ by
      apply Subtype.ext
      rfl]
  exact partOfMax_maxOfPart P hv

/-- The maxima of the sorted parts are strictly increasing in the index. -/
private lemma sortedPartList_max_strictMono (P : Finpartition (Finset.univ : Finset (Fin n))) :
    StrictMono fun m : Fin (P.parts.card) =>
      (sortedParts P m).max' (P.nonempty_of_mem_parts (sortedParts_mem P m)) := by
  intro m₁ m₂ hm₁₂
  simpa [sortedParts_max] using (List.SortedLT.getElem_lt_getElem_of_lt (maxes_sorted P)
    (Fin.lt_def.mpr hm₁₂))

/-- The ordered finpartition of `Fin n` whose parts are the parts of `P` sorted by increasing
maximum element, each part enumerated in increasing order. -/
noncomputable def ofFinpartition (P : Finpartition (Finset.univ : Finset (Fin n))) :
    OrderedFinpartition n where
  length := P.parts.card
  partSize := fun m => (sortedParts P m).card
  partSize_pos := fun m => Finset.card_pos.mpr (P.nonempty_of_mem_parts (sortedParts_mem P m))
  emb := fun m => Finset.orderEmbOfFin (sortedParts P m) rfl
  emb_strictMono := fun m => (Finset.orderEmbOfFin (sortedParts P m) rfl).strictMono
  parts_strictMono := by
    intro m₁ m₂ hm₁₂
    have hpos₁ : 0 < (sortedParts P m₁).card :=
      Finset.card_pos.mpr (P.nonempty_of_mem_parts (sortedParts_mem P m₁))
    have hpos₂ : 0 < (sortedParts P m₂).card :=
      Finset.card_pos.mpr (P.nonempty_of_mem_parts (sortedParts_mem P m₂))
    -- the last element of each part is its maximum, and the maxima are strictly increasing.
    calc
      (Finset.orderEmbOfFin (sortedParts P m₁) rfl)
          ⟨(sortedParts P m₁).card - 1, Nat.sub_one_lt_of_lt hpos₁⟩
          = (sortedParts P m₁).max' (P.nonempty_of_mem_parts (sortedParts_mem P m₁)) := by
        simpa using (Finset.orderEmbOfFin_last
          (rfl : (sortedParts P m₁).card = (sortedParts P m₁).card) hpos₁)
      _ < (sortedParts P m₂).max' (P.nonempty_of_mem_parts (sortedParts_mem P m₂)) := by
        exact sortedPartList_max_strictMono P hm₁₂
      _ = (Finset.orderEmbOfFin (sortedParts P m₂) rfl)
          ⟨(sortedParts P m₂).card - 1, Nat.sub_one_lt_of_lt hpos₂⟩ := by
        simpa using ((Finset.orderEmbOfFin_last
          (rfl : (sortedParts P m₂).card = (sortedParts P m₂).card) hpos₂).symm)
  disjoint := by
    intro m hm m' hm' hne
    have hne' : sortedParts P m ≠ sortedParts P m' := (sortedParts_injective P).ne hne
    have hdisj : Disjoint (sortedParts P m) (sortedParts P m') :=
      P.disjoint (sortedParts_mem P m) (sortedParts_mem P m') hne'
    change Disjoint (Set.range (Finset.orderEmbOfFin (sortedParts P m) rfl))
      (Set.range (Finset.orderEmbOfFin (sortedParts P m') rfl))
    rw [Finset.range_orderEmbOfFin (sortedParts P m) rfl,
      Finset.range_orderEmbOfFin (sortedParts P m') rfl]
    apply Set.disjoint_iff_forall_ne.mpr
    intro x hx y hy hxy
    rw [← hxy] at hy
    exact False.elim ((Finset.disjoint_left.mp hdisj) hx hy)
  cover := by
    intro a
    -- `a ∈ Finset.univ = P.parts.sup id`, so `a` belongs to some part.
    have ha : a ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ a
    rw [← P.sup_parts] at ha
    rcases Finset.mem_sup.mp ha with ⟨A, hA_mem, haA⟩
    rcases sortedParts_surj P A hA_mem with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    -- `a ∈ sortedParts P m = A`, and `orderEmbOfFin (sortedParts P m)` enumerates it.
    exact Set.mem_range.mpr
      ⟨(Finset.orderIsoOfFin (sortedParts P m) rfl).symm ⟨a, by simpa [hm] using haA⟩, by
        have hx := (Finset.orderIsoOfFin (sortedParts P m) rfl).apply_symm_apply
          ⟨a, by simpa [hm] using haA⟩
        change (Finset.orderEmbOfFin (sortedParts P m) rfl)
          ((Finset.orderIsoOfFin (sortedParts P m) rfl).symm ⟨a, by simpa [hm] using haA⟩) = a
        rw [← Finset.coe_orderIsoOfFin_apply]
        exact congrArg Subtype.val hx⟩

/-- The parts of `toFinpartition c` are exactly the ranges of the embeddings of `c`. -/
lemma toFinpartition_parts (c : OrderedFinpartition n) :
    (toFinpartition n c).parts =
      (Finset.univ : Finset (Fin c.length)).image (fun m : Fin c.length =>
        (Finset.univ : Finset (Fin (c.partSize m))).image (c.emb m)) := rfl

/-- The ranges of the embeddings of `c` are pairwise distinct, so they index the parts of
`toFinpartition c` injectively. -/
lemma toFinpartition_parts_injective (c : OrderedFinpartition n) :
    Function.Injective (fun m : Fin c.length =>
      (Finset.univ : Finset (Fin (c.partSize m))).image (c.emb m)) := by
  intro m m' h
  change (Finset.univ : Finset (Fin (c.partSize m))).image (c.emb m) =
    (Finset.univ : Finset (Fin (c.partSize m'))).image (c.emb m') at h
  have hmem : c.emb m ⟨0, c.partSize_pos m⟩ ∈
      (Finset.univ : Finset (Fin (c.partSize m))).image (c.emb m) :=
    Finset.mem_image.mpr ⟨⟨0, c.partSize_pos m⟩, Finset.mem_univ _, rfl⟩
  rw [h] at hmem
  rcases Finset.mem_image.mp hmem with ⟨r', hr', hr'eq⟩
  exact congrArg Sigma.fst
    (c.emb_injective (a₁ := ⟨m, ⟨0, c.partSize_pos m⟩⟩) (a₂ := ⟨m', r'⟩)
      (by simp [hr'eq]))

/-- The number of parts of `toFinpartition c` is the length of `c`. -/
lemma toFinpartition_parts_card (c : OrderedFinpartition n) :
    (toFinpartition n c).parts.card = c.length := by
  rw [toFinpartition_parts, Finset.card_image_of_injective (Finset.univ : Finset (Fin c.length))
    (toFinpartition_parts_injective c)]
  simp

/-- Sorting the image of a strictly increasing family on `Fin l` gives back the family in its
original order. -/
private lemma sort_image_strictMono {α : Type*} [LinearOrder α] (l : ℕ) (f : Fin l → α)
    (hf : StrictMono f) :
    ((Finset.univ : Finset (Fin l)).image f).sort (· ≤ ·) = List.ofFn f := by
  apply List.SortedLT.eq_of_mem_iff
  · exact Finset.sortedLT_sort _
  · exact hf.sortedLT_ofFn
  · intro a
    rw [Finset.mem_sort, Finset.mem_image, List.mem_ofFn]
    constructor
    · rintro ⟨i, _hi, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, Finset.mem_univ i, rfl⟩

/-- `toFinpartition` undoes `ofFinpartition`: reconstructing a finite partition from its sorted
parts gives back `P` itself. -/
lemma toFinpartition_ofFinpartition (P : Finpartition (Finset.univ : Finset (Fin n))) :
    toFinpartition n (ofFinpartition P) = P := by
  apply Finpartition.ext
  rw [toFinpartition_parts]
  -- each part `{emb m r | r}` of `ofFinpartition P` is the sorted part `sortedParts P m`
  change (Finset.univ : Finset (Fin P.parts.card)).image
    (fun m : Fin P.parts.card =>
      (Finset.univ : Finset (Fin ((sortedParts P m).card))).image
        ((sortedParts P m).orderEmbOfFin rfl)) = P.parts
  simp only [Finset.image_orderEmbOfFin_univ]
  ext A
  constructor
  · intro hA
    rcases Finset.mem_image.mp hA with ⟨m, hm, rfl⟩
    exact sortedParts_mem P m
  · intro hA
    rcases sortedParts_surj P A hA with ⟨m, hm⟩
    exact Finset.mem_image.mpr ⟨m, Finset.mem_univ m, hm⟩

/-- `ofFinpartition` undoes `toFinpartition`: sorting the parts of `toFinpartition c` by their
maxima and re-enumerating them recovers exactly `c`. -/
lemma ofFinpartition_toFinpartition (c : OrderedFinpartition n) :
    ofFinpartition (toFinpartition n c) = c := by
  let P : Finpartition (Finset.univ : Finset (Fin n)) := toFinpartition n c
  -- `B m` is the range of the `m`-th embedding of `c`; these are the parts of `P`
  let B : Fin c.length → Finset (Fin n) := fun m =>
    (Finset.univ : Finset (Fin (c.partSize m))).image (c.emb m)
  -- `idx m` is `m` viewed as an index into `P.parts`
  let idx (m : Fin c.length) : Fin P.parts.card :=
    ⟨m.1, by rw [toFinpartition_parts_card]; exact m.2⟩
  have mem (m : Fin c.length) : B m ∈ P.parts := by
    simp [P, B, toFinpartition_parts]
  -- The maximum of the part `B m` is the last element of its increasing enumeration
  have hmaxOfPart (m : Fin c.length) :
      maxOfPart P ⟨B m, mem m⟩ =
        c.emb m ⟨c.partSize m - 1, Nat.sub_one_lt_of_lt (c.partSize_pos m)⟩ := by
    dsimp [maxOfPart, B]
    rw [Finset.max'_image (c.emb_strictMono m).monotone]
    congr 1
    rw [Finset.max'_eq_iff]
    constructor
    · simp
    · intro a ha
      exact Nat.le_pred_of_lt a.2
  -- The maxima of the parts, sorted increasingly, are the values `maxOfPart P ⟨B m, mem m⟩`
  have hmax_image :
      P.parts.attach.image (maxOfPart P) =
        (Finset.univ : Finset (Fin c.length)).image
          (fun m : Fin c.length => maxOfPart P ⟨B m, mem m⟩) := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨⟨A, hA⟩, hmemA, rfl⟩
      have hA' : A ∈ (Finset.univ : Finset (Fin c.length)).image B := by
        simpa [P, B, toFinpartition_parts] using hA
      rcases Finset.mem_image.mp hA' with ⟨m, hm, rfl⟩
      exact Finset.mem_image.mpr ⟨m, Finset.mem_univ m,
        congrArg (maxOfPart P) (Subtype.ext (rfl : B m = B m))⟩
    · intro hv
      rcases Finset.mem_image.mp hv with ⟨m, hm, rfl⟩
      refine Finset.mem_image.mpr ⟨⟨B m, mem m⟩, ?_, rfl⟩
      exact Finset.mem_attach P.parts ⟨B m, mem m⟩
  have hmax : maxes P = List.ofFn (fun m : Fin c.length => maxOfPart P ⟨B m, mem m⟩) := by
    simpa [maxes, hmax_image] using sort_image_strictMono c.length
      (fun m => maxOfPart P ⟨B m, mem m⟩)
      (by
        intro m₁ m₂ hm₁₂
        simpa [hmaxOfPart] using c.parts_strictMono hm₁₂)
  -- The `m`-th sorted part is exactly the range `B m`
  have hpart (m : Fin c.length) : sortedParts P (idx m) = B m := by
    -- `sortedParts` picks the part whose maximum is the `m`-th element of `maxes P`
    change partOfMax P ((maxes P).get ⟨m.1, by rw [maxes_length P]; exact (idx m).2⟩) = B m
    have hget : (maxes P).get ⟨m.1, by rw [maxes_length P]; exact (idx m).2⟩ =
        maxOfPart P ⟨B m, mem m⟩ := by
      simp [hmax]
    rw [hget]
    exact partOfMax_eq_of_mem P (mem m)
  -- The `m`-th part size of `ofFinpartition P` is `c.partSize m`
  have hpartSize (m : Fin c.length) : (ofFinpartition P).partSize (idx m) = c.partSize m := by
    simp [ofFinpartition, hpart m, B,
      Finset.card_image_of_injective (Finset.univ : Finset (Fin (c.partSize m)))
        (c.emb_strictMono m).injective]
  -- The `m`-th embedding of `ofFinpartition P` is `c.emb m` (after aligning the part-size cast)
  have hemb (m : Fin c.length) (r : Fin (c.partSize m)) :
      (ofFinpartition P).emb (idx m) (Fin.cast (hpartSize m).symm r) = c.emb m r := by
    -- `(ofFinpartition P).emb (idx m) = orderEmbOfFin (sortedParts P (idx m)) rfl`, and the
    -- increasing enumeration of the sorted part is `c.emb m`
    have hunique : (sortedParts P (idx m)).orderEmbOfFin (hpartSize m) = c.emb m := by
      exact (Finset.orderEmbOfFin_unique (hpartSize m) (by
        intro x
        -- `c.emb m x` lies in the sorted part `sortedParts P (idx m) = B m`
        rw [hpart m]
        exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩) (c.emb_strictMono m)).symm
    change ((sortedParts P (idx m)).orderEmbOfFin rfl) (Fin.cast (hpartSize m).symm r) =
      c.emb m r
    rw [← hunique]
    -- `orderEmbOfFin` depends only on the index, not on the cardinality proof
    exact (Finset.orderEmbOfFin_eq_orderEmbOfFin_iff (s := sortedParts P (idx m))
      (h := rfl) (h' := hpartSize m)).2 rfl
  -- Compare the three data fields of `ofFinpartition P` and `c`
  have hlength : (ofFinpartition P).length = c.length := by
    simp [ofFinpartition, P, toFinpartition_parts_card]
  have hpartSize' (m : Fin (ofFinpartition P).length) :
      (ofFinpartition P).partSize m = c.partSize (Fin.cast hlength m) := by
    have hm' : m = idx (Fin.cast hlength m) := rfl
    rw [hm']
    exact hpartSize (Fin.cast hlength m)
  have hemb' (m : Fin (ofFinpartition P).length) :
      (ofFinpartition P).emb m ≍ c.emb (Fin.cast hlength m) := by
    refine (Fin.heq_fun_iff (hpartSize' m)).2 ?_
    -- transport `m` to the `idx`-form (this also aligns the domain of the quantifier)
    have hm' : m = idx (Fin.cast hlength m) := rfl
    rw [hm'] at ⊢
    intro r
    -- `r : Fin ((ofFinpartition P).partSize (idx (Fin.cast hlength m)))`; align `r` with the
    -- cast inside `hemb`, whose conclusion now matches the goal exactly
    have hr : r = Fin.cast (hpartSize (Fin.cast hlength m)).symm
        ⟨r.1, hpartSize' (idx (Fin.cast hlength m)) ▸ r.2⟩ := by
      apply Fin.ext
      rfl
    rw [hr]
    exact hemb (Fin.cast hlength m) ⟨r.1, hpartSize' (idx (Fin.cast hlength m)) ▸ r.2⟩
  apply OrderedFinpartition.ext
  · -- lengths agree
    exact hlength
  · -- block sizes agree
    refine (Fin.heq_fun_iff hlength).2 ?_
    · intro m
      exact hpartSize' m
  · -- embedding functions agree
    refine Function.hfunext (congrArg Fin hlength) ?_
    · intro m m' hm
      -- `m : Fin ((ofFinpartition P).length)`, `m' : Fin c.length`, `hm : m ≍ m'`
      have hm' : m' = Fin.cast hlength m :=
        Fin.eq_of_val_eq ((Fin.val_eq_val_of_heq hm.symm).trans rfl)
      subst m'
      exact hemb' m

/-- The Möbius coefficient of `toFinpartition c` is `(-1)^(c.length - 1) * (c.length - 1)!`,
which is exactly the value of the `c.length`-th derivative of `Real.log` at `1`. -/
private lemma toFinpartition_cumulantCoefficient (c : OrderedFinpartition n) :
    (toFinpartition n c).cumulantCoefficient =
      (-1 : ℝ) ^ (c.length - 1) * ((c.length - 1).factorial : ℝ) := by
  rw [Finpartition.cumulantCoefficient, toFinpartition_parts_card]

/-- The product over the parts of `toFinpartition c` of a block weight equals the product over
the blocks `j` of the same weight applied to the range of the `j`-th embedding. -/
private lemma toFinpartition_blockProduct (c : OrderedFinpartition n) (f : Finset (Fin n) → ℝ) :
    ∏ B ∈ (toFinpartition n c).parts, f B =
      ∏ j : Fin c.length, f ((Finset.univ : Finset (Fin (c.partSize j))).image (c.emb j)) := by
  simpa [toFinpartition_parts] using Finset.prod_image (toFinpartition_parts_injective c).injOn

/-- `OrderedFinpartition n` and `Finpartition (Finset.univ : Finset (Fin n))` are in bijection:
`toFinpartition` forgets the ordering of the parts, `ofFinpartition` sorts them by maximum. -/
noncomputable def orderedFinpartitionEquiv (n : ℕ) :
    OrderedFinpartition n ≃ Finpartition (Finset.univ : Finset (Fin n)) where
  toFun := toFinpartition n
  invFun := ofFinpartition
  left_inv := ofFinpartition_toFinpartition
  right_inv := toFinpartition_ofFinpartition

end OrderedFinpartition


/-- Analytic Faà di Bruno expansion of the scalar cumulant-generating function.

This is the reusable analytic/combinatorial core behind
`iteratedDeriv_cgf_zero_eq_sum_partitions`.  Informally, unfold `cgf` as
`Real.log ∘ mgf X μ`, use `ProbabilityTheory.mgf_zero` to get `mgf X μ 0 = 1`, and apply the
one-variable Faà di Bruno formula
`iteratedDeriv_comp_eq_sum_orderedFinpartition` to `Real.log ∘ mgf X μ`.  The assumptions give the
required smoothness (`analyticAt_mgf hmgf`, hence `ContDiffAt`); the derivatives of `Real.log` at
`1` are `(-1)^(k-1) * (k-1)!` for `k ≥ 1`; finally, reindex Mathlib's
`OrderedFinpartition n` by ordinary `Finpartition (Finset.univ : Finset (Fin n))`.

References: Mathlib's `Analysis/Calculus/IteratedDeriv/FaaDiBruno.lean` for the analytic formula,
and the classical cumulant/moment formula, e.g. Scholarpedia "Cumulants"
<http://www.scholarpedia.org/article/Cumulants>. -/
lemma iteratedDeriv_cgf_zero_eq_sum_partitions_faaDiBruno [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (n : ℕ) (hn : n ≠ 0)
    (hmgf : 0 ∈ interior (integrableExpSet X μ)) :
    iteratedDeriv n (cgf X μ) 0 =
      ∑ P : Finpartition (Finset.univ : Finset (Fin n)),
        (P.cumulantCoefficient : ℝ) * ∏ B ∈ P.parts, iteratedDeriv B.card (mgf X μ) 0 := by
  -- `cgf X μ` is the logarithm of the moment-generating function
  change iteratedDeriv n (Real.log ∘ mgf X μ) 0 =
      ∑ P : Finpartition (Finset.univ : Finset (Fin n)),
        (P.cumulantCoefficient : ℝ) * ∏ B ∈ P.parts, iteratedDeriv B.card (mgf X μ) 0
  have hmgf1 : mgf X μ 0 = 1 := ProbabilityTheory.mgf_zero
  -- The derivatives of `Real.log` at `1` are the Möbius coefficients
  have hlog (c : OrderedFinpartition n) :
      iteratedDeriv c.length Real.log 1 =
        (-1 : ℝ) ^ (c.length - 1) * ((c.length - 1).factorial : ℝ) :=
    iteratedDeriv_log_one_of_pos (c.length_pos (Nat.pos_of_ne_zero hn))
  -- Each ordered Faà di Bruno summand coincides with the corresponding finpartition summand
  have hsum (c : OrderedFinpartition n) :
    iteratedDeriv c.length Real.log 1 *
        ∏ j : Fin c.length, iteratedDeriv (c.partSize j) (mgf X μ) 0 =
      (OrderedFinpartition.toFinpartition n c).cumulantCoefficient *
        ∏ B ∈ (OrderedFinpartition.toFinpartition n c).parts, iteratedDeriv B.card (mgf X μ) 0 := by
    rw [hlog c, OrderedFinpartition.toFinpartition_cumulantCoefficient c,
      OrderedFinpartition.toFinpartition_blockProduct c (fun B => iteratedDeriv B.card (mgf X μ) 0)]
    congr 1
    exact Finset.prod_congr rfl (fun j hj => by
      simp [Finset.card_image_of_injective (Finset.univ : Finset (Fin (c.partSize j)))
        (c.emb_strictMono j).injective])
  -- Faà di Bruno for the composition `Real.log ∘ mgf X μ`
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition (𝕜 := ℝ) (g := Real.log) (f := mgf X μ)
    (x := 0) (i := n) (n := (⊤ : WithTop ℕ∞))
    (by simp [Real.contDiffAt_log, hmgf1])
    (analyticAt_mgf hmgf).contDiffAt
    (le_top : (n : WithTop ℕ∞) ≤ ⊤),
    hmgf1]
  -- reindex the sum over ordered finpartitions to a sum over ordinary finpartitions
  rw [← Equiv.sum_comp (OrderedFinpartition.orderedFinpartitionEquiv n)
    (fun P : Finpartition (Finset.univ : Finset (Fin n)) =>
      (P.cumulantCoefficient : ℝ) * ∏ B ∈ P.parts, iteratedDeriv B.card (mgf X μ) 0)]
  -- compare the two sums term by term
  exact Finset.sum_congr rfl (fun c hc => hsum c)


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
        (P.cumulantCoefficient : ℝ) * ∏ B ∈ P.parts, iteratedDeriv B.card (mgf X μ) 0 :=
  iteratedDeriv_cgf_zero_eq_sum_partitions_faaDiBruno X n hn hmgf

/-- The cumulant of order 0 is 0. -/
lemma cumulant_zero [IsProbabilityMeasure μ] (X : Ω → ℝ) : cumulant μ X 0 = 0 := by
  dsimp [cumulant]
  simp

/-- Analytic and set-partition definitions of a repeated-variable cumulant agree.

Informal proof: `iteratedDeriv_mgf_zero` identifies the MGF coefficients with moments.  Expanding
the logarithm of a power series with constant coefficient one gives the partition-lattice Möbius
coefficients, so the `n`th CGF derivative is exactly the joint cumulant of `n` copies of `X`. -/
theorem cumulant_eq_jointCumulant [IsProbabilityMeasure μ] (X : Ω → ℝ) (n : ℕ)
    (hmgf : 0 ∈ interior (integrableExpSet X μ)) :
    cumulant μ X n = jointCumulant μ (fun _ : Fin n ↦ X) := by
  by_cases hn : n = 0
  · subst n
    simp [cumulant]
  · dsimp [cumulant, jointCumulant, blockCumulant]
    rw [iteratedDeriv_cgf_zero_eq_sum_partitions X n hn hmgf]
    have h_univ_ne : (Finset.univ : Finset (Fin n)) ≠ ∅ := by
      intro h_empty
      have hmem : (⟨0, Nat.pos_of_ne_zero hn⟩ : Fin n) ∈
          (Finset.univ : Finset (Fin n)) := by
        simp
      rw [h_empty] at hmem
      simp at hmem
    simp [Finpartition.cumulantTransform, Finpartition.blockProduct, h_univ_ne,
      blockMoment_const_eq_integral_pow, iteratedDeriv_mgf_zero_eq_moment, hmgf]

end Renormalization

end

end
