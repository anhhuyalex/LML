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

-- The canonical equivalence between partitions of a finset `B : Finset ι` and partitions of the
-- full subtype `{x : ι // x ∈ B}`.  Each block is transported by the preimage/image correspondence
-- induced by the injective subtype embedding: a block `A ⊆ B` becomes `{x : B | x.1 ∈ A}` and a
-- block `C : Finset B` becomes `C.map φ`.  Both round-trips are the standard
-- `Finset.preimage_map`/preimage-of-image identities, and `Finset.univ.map φ = B` supplies the
-- coverage.  Used by `cumulantTransform_subtype` to reindex the cumulant sum.
def finpartition_subtypeEquiv [DecidableEq ι] (B : Finset ι) :
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
private lemma finpartition_subtypeEquiv_summand [DecidableEq ι] {R : Type*} [CommRing R]
    (B : Finset ι) (f : Finset ι → R) (P : Finpartition B) :
    P.cumulantCoefficient * P.blockProduct f =
      (finpartition_subtypeEquiv B P).cumulantCoefficient *
        (finpartition_subtypeEquiv B P).blockProduct
          (fun s : Finset B ↦ f (s.map (Function.Embedding.subtype (· ∈ B)))) := by
  classical
  let φ : B ↪ ι := Function.Embedding.subtype (fun x : ι ↦ x ∈ B)
  let pre : Finset ι → Finset B := fun A ↦ A.preimage φ φ.injective.injOn
  have h_parts : (finpartition_subtypeEquiv B P).parts = P.parts.image pre := rfl
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
  have h_card : (finpartition_subtypeEquiv B P).parts.card = P.parts.card := by
    rw [h_parts, Finset.card_image_of_injOn h_pre_inj]
  have h_coeff :
      Finpartition.cumulantCoefficient (R := R) (finpartition_subtypeEquiv B P) =
        Finpartition.cumulantCoefficient (R := R) P := by
    rw [Finpartition.cumulantCoefficient, h_card, Finpartition.cumulantCoefficient]
  have h_block :
      (finpartition_subtypeEquiv B P).blockProduct (fun s : Finset B ↦ f (s.map φ)) =
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
    -- Reindex the cumulant sum along the subtype equivalence.  `finpartition_subtypeEquiv_summand`
    -- shows every summand is transported unchanged, and `Equiv.sum_comp` rewrites the transported
    -- sum back to the sum over partitions of the full subtype.
    rw [← (finpartition_subtypeEquiv B).sum_comp]
    exact Finset.sum_congr rfl (fun P _ => finpartition_subtypeEquiv_summand B f P)

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
lemma jointMoment_eq_blockMoment_univ [Fintype ι]
    [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) :
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
  simpa using congrFun (Finpartition.partitionTransform_cumulantTransform (R := R) f h_empty) Finset.univ

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

lemma blockMoment_map_equiv [IsProbabilityMeasure μ]
    (e : ι ≃ κ) (X : ι → Ω → ℝ) (s : Finset κ) :
    blockMoment μ (fun j ↦ X (e.symm j)) s = blockMoment μ X (s.map e.symm.toEmbedding) := by
  dsimp [blockMoment]
  congr 1
  ext ω
  exact (Finset.prod_map s e.symm.toEmbedding (fun i : ι ↦ X i ω)).symm

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

lemma blockMoment_add_update [DecidableEq ι] [IsProbabilityMeasure μ]
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

lemma blockMoment_update_not_mem [DecidableEq ι] [IsProbabilityMeasure μ]
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

lemma blockMoment_smul_update [DecidableEq ι] [IsProbabilityMeasure μ]
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
                (∏ j ∈ s.erase i, (Function.update X i (c • X i)) j ω) = ∏ j ∈ s.erase i, X j ω := by
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

lemma blockMoment_indepFun_split [DecidableEq ι] [IsProbabilityMeasure μ]
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
  dsimp [blockMoment]
  congr 1
  ext ω
  rw [Finset.prod_const]

/-- The $k$-th derivative of the MGF at zero is the $k$-th moment.
Informal proof: Differentiate under the integral sign $k$ times and evaluate at $t=0$. -/
lemma iteratedDeriv_mgf_zero_eq_moment [IsProbabilityMeasure μ] (X : Ω → ℝ) (k : ℕ)
    (hmgf : 0 ∈ interior (integrableExpSet X μ)) :
    iteratedDeriv k (mgf X μ) 0 = ∫ ω, X ω ^ k ∂μ := by
  simpa using ProbabilityTheory.iteratedDeriv_mgf_zero hmgf k

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
  sorry

end Renormalization

end

end
