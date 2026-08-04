/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Basic
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
lemma jointCumulant_four_of_centered_combinatorics [IsProbabilityMeasure μ]
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
theorem jointCumulant_four_of_centered [IsProbabilityMeasure μ] (X : Fin 4 → Ω → ℝ)
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

lemma blockMoment_indepFun_split [DecidableEq ι] [IsProbabilityMeasure μ]
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
  classical
  -- The identity is universal in the target commutative ring: prove it over `ℤ` and cast through
  -- the canonical homomorphism `ℤ → R`.
  have hInt :
      (∑ m ∈ Finset.range (Nat.min p q + 1),
        (((((p.choose m) * (q.choose m) * m.factorial : ℕ) : ℤ) *
          ((-1 : ℤ) ^ (p + q - m - 1) *
            (((p + q - m - 1).factorial : ℕ) : ℤ))))) = 0 := by
    -- The summand is symmetric in `p` and `q`; thus one may assume `p ≤ q` and treat the other
    -- case by swapping the traces.
    have hsymm :
        (∑ m ∈ Finset.range (Nat.min p q + 1),
          (((((p.choose m) * (q.choose m) * m.factorial : ℕ) : ℤ) *
            ((-1 : ℤ) ^ (p + q - m - 1) *
              (((p + q - m - 1).factorial : ℕ) : ℤ))))) =
        (∑ m ∈ Finset.range (Nat.min q p + 1),
          (((((q.choose m) * (p.choose m) * m.factorial : ℕ) : ℤ) *
            ((-1 : ℤ) ^ (q + p - m - 1) *
              (((q + p - m - 1).factorial : ℕ) : ℤ))))) := by
      -- This is just commutativity of `Nat.min`, addition, and multiplication in each summand.
      simp [Nat.min_comm, Nat.add_comm, mul_comm, mul_assoc]
    rcases le_total p q with hpq | hqp
    · -- Now `Nat.min p q = p`, so the range is `0, ..., p`.  Introduce the polynomial
      -- `P(X) = ∏ j = 1..p-1 (q - X + j)`.  Its degree is `< p`, so
      -- `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt` and `fwdDiff_iter_eq_sum_shift` give
      -- `∑ m = 0..p, (-1)^m * p.choose m * P(m) = 0`.  Factorial-ratio identities rewrite the
      -- original summand as the constant `q! * (-1)^(p+q-1)` times this alternating sum.
      sorry
    · -- The case `q ≤ p` is identical after swapping the two traces.  The equality `hsymm` records
      -- the required symmetry of the integer summand.
      have _ := hsymm
      sorry
  -- Cast the integer identity to the arbitrary commutative ring `R`, distributing the cast through
  -- the finite sum, products, powers of `-1`, and factorial casts.
  sorry

/-- Core trace-fiber Möbius cancellation for split block weights.

This is the reusable combinatorial statement underlying
`cumulantTransform_eq_zero_of_split_trace_fiber`.  It is stated with all elementary side facts
already exposed, so callers can keep their proofs short and readable.

Informal proof.  Restrict each partition of `univ` to the two sides `A` and `univ \ A`, erasing
empty intersections.  For fixed trace partitions with `p` and `q` blocks, the fiber consists of
partial matchings between the two block sets.  A matching of size `m` has
`p + q - m` blocks.  The split hypothesis factors the weight of every glued block, while the two
absorption hypotheses remove the harmless `f ∅` factors from pure-side blocks, so the block product
is constant on each fiber.  The remaining signed Möbius coefficient of the fiber is the standard
finite-difference sum

`∑ m, (p.choose m) * (q.choose m) * m! * (-1)^(p+q-m-1) * (p+q-m-1)!`,

which vanishes for `p,q ≥ 1`: after assuming `p ≤ q`, it is the `p`-th forward difference of a
polynomial of degree `< p`.  This is the classical partition-lattice proof of vanishing mixed
cumulants; see T. P. Speed, "Cumulants and partition lattices", Austral. J. Statist. 25 (1983),
378--388, and Mathlib's finite-difference API in `Mathlib/Algebra/Group/ForwardDiff.lean`.

TODO: formalize the trace restriction map, the partial-matching fiber equivalence, and the displayed
coefficient identity as `Finpartition` API. -/
private lemma cumulantTransform_eq_zero_of_split_trace_fiber_cancel_core [Fintype ι]
    [DecidableEq ι] {R : Type*} [CommRing R] (f : Finset ι → R) (A : Finset ι)
    (_hA : A.Nonempty) (_hAc : (Finset.univ \ A).Nonempty)
    (_h_factor : ∀ s, f s = f (s ∩ A) * f (s \ A))
    (_huniv_ne : (Finset.univ : Finset ι) ≠ ∅)
    (_hcompl_ne : (Finset.univ \ A : Finset ι) ≠ ∅)
    (_hleft_absorb : ∀ ⦃b : Finset ι⦄, b ⊆ A → f ∅ * f b = f b)
    (_hright_absorb : ∀ ⦃b : Finset ι⦄, b ⊆ Finset.univ \ A → f ∅ * f b = f b) :
    Finpartition.cumulantTransform f Finset.univ = 0 := by
  classical
  -- The two sides form a genuine non-trivial cut of `univ`.
  have hcut_cover : A ∪ (Finset.univ \ A) = (Finset.univ : Finset ι) := by
    ext i
    simp [or_iff_not_imp_left]
  have hcut_disjoint : Disjoint A (Finset.univ \ A) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext i
    simp
  have hcompl_subset_univ : Finset.univ \ A ⊆ (Finset.univ : Finset ι) :=
    Finset.sdiff_subset
  -- Rewrite the split hypothesis using the named complement.  This is the identity used on every
  -- block before regrouping partitions by their traces on `A` and on `univ \ A`.
  have hblock_split_compl (B : Finset ι) :
      f B = f (B ∩ A) * f (B ∩ (Finset.univ \ A)) := by
    have hsdiff_eq_inter_compl : B \ A = B ∩ (Finset.univ \ A) := by
      ext i
      simp
    simpa [hsdiff_eq_inter_compl] using _h_factor B
  -- Pure-side trace blocks may pick up a harmless factor `f ∅`; the absorption hypotheses remove
  -- exactly those factors.
  have hleft_id_on_trace : ∀ ⦃B : Finset ι⦄, B ⊆ A → f B = f ∅ * f B :=
    fun {B} hB ↦ (_hleft_absorb (b := B) hB).symm
  have hright_id_on_trace : ∀ ⦃B : Finset ι⦄, B ⊆ Finset.univ \ A → f B = f ∅ * f B :=
    fun {B} hB ↦ (_hright_absorb (b := B) hB).symm
  -- The numerical cancellation left after fixing left/right trace partitions.  For trace sizes
  -- `p,q ≥ 1`, a fiber is enumerated by partial matchings of size `m`; the displayed sum is its
  -- total Möbius coefficient.  The proof is the standard finite-difference argument described in
  -- the lemma docstring and in Speed, "Cumulants and partition lattices" (1983): after assuming
  -- `p ≤ q`, the inner alternating binomial sum is the `p`-th forward difference of a polynomial of
  -- degree `< p`.
  have hfiber_coeff_cancel :
      ∀ p q : ℕ, 0 < p → 0 < q →
        (∑ m ∈ Finset.range (Nat.min p q + 1),
          ((((p.choose m) * (q.choose m) * m.factorial : ℕ) : R) *
            ((-1 : R) ^ (p + q - m - 1) * ((p + q - m - 1).factorial : R)))) = 0 := by
    intro p q hp hq
    exact partialMatching_mobius_coeff_sum_eq_zero p q hp hq
  -- Main trace-fiber step.  Restrict each partition of `univ` to `A` and to `univ \ A`, erasing
  -- empty intersections.  The preceding facts give:
  -- * traces are nonempty because `_hA` and `_hAc` are nonempty;
  -- * `hblock_split_compl`, `hleft_id_on_trace`, and `hright_id_on_trace` make the block product
  --   constant on each trace fiber;
  -- * each fiber is counted by partial matchings of its trace blocks, and `hfiber_coeff_cancel`
  --   makes its total Möbius coefficient vanish.
  -- Summing the zero fiber contributions gives the cumulant cancellation.
  have htrace_fiber_cancellation : Finpartition.cumulantTransform f Finset.univ = 0 := by
    -- TODO: expose the trace restriction map and the partial-matching fiber equivalence as
    -- `Finpartition` API, then finish by reindexing the cumulant sum and applying
    -- `hfiber_coeff_cancel` to every trace pair.
    sorry
  exact htrace_fiber_cancellation

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
    [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (A : Finset ι)
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
