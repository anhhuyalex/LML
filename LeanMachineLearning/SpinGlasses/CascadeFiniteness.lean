/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeTree
public import LeanMachineLearning.SpinGlasses.PoissonDirichletGibbs
public import LeanMachineLearning.ForMathlib.Probability.Independence.IndepInfinitePi
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.NthLargestAtomRank

/-!
# Vertex-indexed Poisson cascade: local mass and probabilistic interfaces

The parent vertices have the single index type `Σ p : ℕ, Fin p → ℕ`. Each vertex owns
its own sequence of Poisson blocks; `nthLargestAtom` orders the resulting child masses.
Independence of the vertex blocks gives independence of entire child-subtree
arrays, their totals, and the root process. The all-depth finite-mass statement
still assumes the marked-sum estimate explicitly. Child-subtree laws and
independence of ranked root masses from the mark vector are established,
as is Tonelli for independent ranked masses and subtree totals. The general-test
rank-to-counting-measure identity holds almost surely for the root blocks;
the independent-mark Campbell identity is proved for arbitrary measurable tests;
the power-moment normalization and induction are not yet established.
-/

@[expose] public section

namespace SpinGlasses

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Restrict a globally independent array of vertex blocks to one vertex. -/
theorem iIndepFun_cascadeVertexBlocks
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P)
    (v : Σ p : ℕ, Fin p → ℕ) : iIndepFun (B v) P := by
  exact hB.precomp (g := fun k => (v, k)) (by
    intro k l h
    exact congrArg Prod.snd h)

/-- The map sending a (child label, vertex inside that child's subtree, block number) to the
corresponding vertex and block number of the whole tree is injective. -/
theorem cascadeSubtree_index_injective :
    Function.Injective (fun nk : (ℕ × (Σ p : ℕ, Fin p → ℕ)) × ℕ =>
      ((⟨nk.1.2.1 + 1, Fin.cons nk.1.1 nk.1.2.2⟩ : Σ p : ℕ, Fin p → ℕ), nk.2)) := by
  rintro ⟨⟨n, ⟨p, gamma⟩⟩, k⟩ ⟨⟨m, ⟨q, delta⟩⟩, l⟩ hab
  have hv := congrArg Prod.fst hab
  have hk := congrArg Prod.snd hab
  have hp : p = q := Nat.succ.inj (congrArg Sigma.fst hv)
  subst hp
  have hcons : (Fin.cons n gamma : Fin (p + 1) → ℕ) = Fin.cons m delta :=
    eq_of_heq (Sigma.mk.inj hv).2
  have hn : n = m := congrArg (fun f => f 0) hcons
  have hg : gamma = delta := (Fin.cons_inj.mp hcons).2
  subst hn hg hk
  rfl

/-- Restrict the global block family to the disjoint subtrees below the root.
The first index is the child label; the second describes a vertex inside that subtree. -/
theorem iIndepFun_cascadeSubtreeBlocks
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P) :
    iIndepFun (fun nk : (ℕ × (Σ p : ℕ, Fin p → ℕ)) × ℕ =>
      B ⟨nk.1.2.1 + 1, Fin.cons nk.1.1 nk.1.2.2⟩ nk.2) P :=
  hB.precomp cascadeSubtree_index_injective

/-- Every individual child-subtree inherits independence among all its blocks. -/
theorem iIndepFun_cascadeChildBlocks
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P)
    (n : ℕ) :
    iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ =>
      B ⟨vk.1.1 + 1, Fin.cons n vk.1.2⟩ vk.2) P :=
  (iIndepFun_cascadeSubtreeBlocks B hB).precomp
    (g := fun (vk : (Σ p : ℕ, Fin p → ℕ) × ℕ) => ((n, vk.1), vk.2))
    fun _ _ h => Prod.ext (congrArg (fun x => x.1.2) h) (congrArg (fun x => x.2) h)

/-- A child has the full joint law of a fresh cascade whose exponent and block
parameters have been shifted by one level. This is a law of block arrays, not yet
the ranked marked-process identity needed for the finite-mass induction. -/
theorem hasLaw_cascadeChildBlockArray
    [IsProbabilityMeasure P]
    (nu : (p : ℕ) → ℕ → Measure ℝ)
    (rate : (p : ℕ) → ℕ → NNReal)
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ v k, Measurable (B v k))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P)
    (hlaw : ∀ v k, HasLaw (B v k)
      ((Po(rate v.1 k)).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k)) P)
    (n : ℕ) :
    HasLaw (fun ω (vk : (Σ p : ℕ, Fin p → ℕ) × ℕ) =>
      B ⟨vk.1.1 + 1, Fin.cons n vk.1.2⟩ vk.2 ω)
      (Measure.infinitePi fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ =>
        (Po(rate (vk.1.1 + 1) vk.2)).prod
          (Measure.infinitePi fun _ : ℕ => nu (vk.1.1 + 1) vk.2)) P := by
  let X (vk : (Σ p : ℕ, Fin p → ℕ) × ℕ) (ω : Ω) :=
    B ⟨vk.1.1 + 1, Fin.cons n vk.1.2⟩ vk.2 ω
  have hXm : ∀ vk, Measurable (X vk) := fun vk =>
    hBm ⟨vk.1.1 + 1, Fin.cons n vk.1.2⟩ vk.2
  have hXi : iIndepFun X P := iIndepFun_cascadeChildBlocks B hB n
  exact HasLaw.infinitePi hXm hXi fun vk => hlaw ⟨vk.1.1 + 1, Fin.cons n vk.1.2⟩ vk.2

/-- The complete block arrays below distinct root children are independent.
This is stronger than independence of the individual blocks: it permits applying
arbitrary measurable functions, such as subtree total masses, to each array. -/
theorem iIndepFun_cascadeSubtreeArrays
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ v k, Measurable (B v k))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P) :
    iIndepFun (fun n ω (vk : (Σ p : ℕ, Fin p → ℕ) × ℕ) =>
      B ⟨vk.1.1 + 1, Fin.cons n vk.1.2⟩ vk.2 ω) P := by
  let X : ℕ → ((Σ p : ℕ, Fin p → ℕ) × ℕ) → Ω → ℕ × (ℕ → ℝ) :=
    fun n vk => B ⟨vk.1.1 + 1, Fin.cons n vk.1.2⟩ vk.2
  change iIndepFun (fun n ω vk => X n vk ω) P
  apply iIndepFun.curry' (X := X)
    (fun n vk => hBm ⟨vk.1.1 + 1, Fin.cons n vk.1.2⟩ vk.2)
  let g : (ℕ × ((Σ p : ℕ, Fin p → ℕ) × ℕ)) →
      (ℕ × (Σ p : ℕ, Fin p → ℕ)) × ℕ :=
    fun x => ((x.1, x.2.1), x.2.2)
  apply (iIndepFun_cascadeSubtreeBlocks B hB).precomp (g := g)
  intro a b h
  exact Prod.ext (congrArg (fun x => x.1.1) h)
    (Prod.ext (congrArg (fun x => x.1.2) h) (congrArg (fun x => x.2) h))

/-- The total masses in all the subtrees below distinct root children are independent.
No identical-law assertion is needed for this step. -/
theorem iIndepFun_cascadeSubtreeTotals
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ v k, Measurable (B v k))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P)
    (r : ℕ) :
    iIndepFun (fun n ω => ∑' beta : Fin r → ℕ,
      cascadeBranchWeight
        (fun p gamma m => nthLargestAtom m (poissonCountingMeasure
          (fun k => (B ⟨p + 1, Fin.cons n gamma⟩ k ω).1)
          (fun k l => (B ⟨p + 1, Fin.cons n gamma⟩ k ω).2 l)))
        beta) P := by
  let F (n : ℕ) (a : ((Σ p : ℕ, Fin p → ℕ) × ℕ) → ℕ × (ℕ → ℝ)) :=
    ∑' beta : Fin r → ℕ, cascadeBranchWeight
      (fun p gamma m => nthLargestAtom m (poissonCountingMeasure
        (fun k => (a (⟨p, gamma⟩, k)).1)
        (fun k l => (a (⟨p, gamma⟩, k)).2 l))) beta
  have hFm : ∀ n, Measurable (F n) := by
    intro n
    apply measurable_tsum_cascadeBranchWeight
    intro p gamma m
    exact (measurable_nthLargestAtom m).comp
      (measurable_poissonCountingMeasure_comp
        (fun k => (measurable_pi_apply
          ((⟨p, gamma⟩ : Σ p : ℕ, Fin p → ℕ), k))))
  have h := (iIndepFun_cascadeSubtreeArrays B hBm hB).comp F hFm
  simpa only [F, Function.comp_def] using h

/-- The entire root block array is independent of the entire collection of
blocks in every root-child subtree. Both arrays are measurable product-valued
random variables; this does not require the subtree block laws to be identical. -/
theorem indepFun_cascadeRoot_subtreeArrays
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ v k, Measurable (B v k))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P) :
    IndepFun (fun ω k => B ⟨0, fun i => i.elim0⟩ k ω)
      (fun ω n (vk : (Σ p : ℕ, Fin p → ℕ) × ℕ) =>
        B ⟨vk.1.1 + 1, Fin.cons n vk.1.2⟩ vk.2 ω) P := by
  let root : Set ((Σ p : ℕ, Fin p → ℕ) × ℕ) :=
    {vk | vk.1.1 = 0}
  let below : Set ((Σ p : ℕ, Fin p → ℕ) × ℕ) :=
    {vk | 0 < vk.1.1}
  have hd : Disjoint root below := Set.disjoint_left.2 fun _ hr hb => by
    have : _ = 0 := hr
    have : 0 < _ := hb
    omega
  have hind := indep_iSup_of_disjoint
    (fun vk => (hBm vk.1 vk.2).comap_le) (show iIndep
      (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ =>
        MeasurableSpace.comap (B vk.1 vk.2) inferInstance) P from hB) hd
  have hrange : Set.range (fun k : ℕ =>
      ((⟨0, fun i => i.elim0⟩ : Σ p : ℕ, Fin p → ℕ), k)) = root := by
    ext vk
    simp only [Set.mem_range, root, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, rfl⟩
      rfl
    · intro hv
      refine ⟨vk.2, ?_⟩
      rcases vk with ⟨⟨p, gamma⟩, k⟩
      cases hv
      exact congrArg (fun v : Fin 0 → ℕ =>
        ((⟨0, v⟩ : Σ p : ℕ, Fin p → ℕ), k))
        (Subsingleton.elim (fun i => i.elim0) gamma)
  have hbelow : Set.range (fun nk : ℕ × ((Σ p : ℕ, Fin p → ℕ) × ℕ) =>
      ((⟨nk.2.1.1 + 1, Fin.cons nk.1 nk.2.1.2⟩ :
        Σ p : ℕ, Fin p → ℕ), nk.2.2)) = below := by
    ext vk
    simp only [Set.mem_range, below, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨nk, rfl⟩
      exact Nat.zero_lt_succ _
    · intro hv
      rcases vk with ⟨⟨p, gamma⟩, k⟩
      cases p with
      | zero =>
        exact False.elim (by simp at hv)
      | succ p =>
        refine ⟨(gamma 0, (⟨p, Fin.tail gamma⟩, k)), ?_⟩
        exact congrArg (fun v : Fin (p + 1) → ℕ =>
          ((⟨p + 1, v⟩ : Σ p : ℕ, Fin p → ℕ), k))
          (Fin.cons_self_tail gamma)
  rw [← hrange, ← hbelow] at hind
  rw [← MeasurableSpace.comap_pi_range
    (fun k : ℕ => ((⟨0, fun i => i.elim0⟩ : Σ p : ℕ, Fin p → ℕ), k))
    (fun vk ω => B vk.1 vk.2 ω),
    ← MeasurableSpace.comap_pi_range
      (fun nk : ℕ × ((Σ p : ℕ, Fin p → ℕ) × ℕ) =>
        ((⟨nk.2.1.1 + 1, Fin.cons nk.1 nk.2.1.2⟩ :
          Σ p : ℕ, Fin p → ℕ), nk.2.2))
      (fun vk ω => B vk.1 vk.2 ω)] at hind
  rw [IndepFun_iff_Indep]
  simp only [MeasurableSpace.comap_pi, iSup_prod] at hind ⊢
  exact hind

/-- The mass in each child subtree has the law obtained by evaluating the
shifted-parameter cascade on its canonical independent block array. -/
theorem hasLaw_cascadeChildTotal
    [IsProbabilityMeasure P]
    (nu : (p : ℕ) → ℕ → Measure ℝ)
    (rate : (p : ℕ) → ℕ → NNReal)
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ v k, Measurable (B v k))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P)
    (hlaw : ∀ v k, HasLaw (B v k)
      ((Po(rate v.1 k)).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k)) P)
    (n r : ℕ) :
    HasLaw (fun ω => ∑' beta : Fin r → ℕ,
      cascadeBranchWeight
        (fun p gamma m => nthLargestAtom m (poissonCountingMeasure
          (fun k => (B ⟨p + 1, Fin.cons n gamma⟩ k ω).1)
          (fun k l => (B ⟨p + 1, Fin.cons n gamma⟩ k ω).2 l)))
        beta)
      ((Measure.infinitePi fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ =>
        (Po(rate (vk.1.1 + 1) vk.2)).prod
          (Measure.infinitePi fun _ : ℕ => nu (vk.1.1 + 1) vk.2)).map
        (fun a => ∑' beta : Fin r → ℕ, cascadeBranchWeight
          (fun p gamma m => nthLargestAtom m (poissonCountingMeasure
            (fun k => (a (⟨p, gamma⟩, k)).1)
            (fun k l => (a (⟨p, gamma⟩, k)).2 l))) beta)) P := by
  let F (a : ((Σ p : ℕ, Fin p → ℕ) × ℕ) → ℕ × (ℕ → ℝ)) :=
    ∑' beta : Fin r → ℕ, cascadeBranchWeight
      (fun p gamma m => nthLargestAtom m (poissonCountingMeasure
        (fun k => (a (⟨p, gamma⟩, k)).1)
        (fun k l => (a (⟨p, gamma⟩, k)).2 l))) beta
  have hF : Measurable F := by
    apply measurable_tsum_cascadeBranchWeight
    intro p gamma m
    exact (measurable_nthLargestAtom m).comp
      (measurable_poissonCountingMeasure_comp
        (fun k => measurable_pi_apply
          ((⟨p, gamma⟩ : Σ p : ℕ, Fin p → ℕ), k)))
  have harray := hasLaw_cascadeChildBlockArray nu rate B hBm hB hlaw n
  have hm : Measurable fun ω (vk : (Σ p : ℕ, Fin p → ℕ) × ℕ) =>
      B ⟨vk.1.1 + 1, Fin.cons n vk.1.2⟩ vk.2 ω :=
    measurable_pi_iff.2 fun vk => hBm _ _
  refine ⟨(hF.comp hm).aemeasurable, ?_⟩
  change P.map (F ∘ fun ω vk =>
    B ⟨vk.1.1 + 1, Fin.cons n vk.1.2⟩ vk.2 ω) =
    (Measure.infinitePi fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ =>
      (Po(rate (vk.1.1 + 1) vk.2)).prod
        (Measure.infinitePi fun _ : ℕ => nu (vk.1.1 + 1) vk.2)).map F
  rw [← Measure.map_map hF hm, harray.map_eq]

/-- The root Poisson blocks are independent of the vector of all subtree totals.
The latter may involve infinitely many vertices in each subtree. -/
theorem indepFun_cascadeRoot_subtreeTotals
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ v k, Measurable (B v k))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P)
    (r : ℕ) :
    IndepFun (fun ω k => B ⟨0, fun i => i.elim0⟩ k ω)
      (fun ω n => ∑' beta : Fin r → ℕ,
        cascadeBranchWeight
          (fun p gamma m => nthLargestAtom m (poissonCountingMeasure
          (fun k => (B ⟨p + 1, Fin.cons n gamma⟩ k ω).1)
          (fun k l => (B ⟨p + 1, Fin.cons n gamma⟩ k ω).2 l)))
          beta) P := by
  let F (a : ((Σ p : ℕ, Fin p → ℕ) × ℕ) → ℕ × (ℕ → ℝ)) :=
    ∑' beta : Fin r → ℕ, cascadeBranchWeight
      (fun p gamma m => nthLargestAtom m (poissonCountingMeasure
        (fun k => (a (⟨p, gamma⟩, k)).1)
        (fun k l => (a (⟨p, gamma⟩, k)).2 l))) beta
  have hFm : Measurable F := by
    apply measurable_tsum_cascadeBranchWeight
    intro p gamma m
    exact (measurable_nthLargestAtom m).comp
      (measurable_poissonCountingMeasure_comp
        (fun k => measurable_pi_apply
          ((⟨p, gamma⟩ : Σ p : ℕ, Fin p → ℕ), k)))
  have hG : Measurable (fun a : ℕ → ((Σ p : ℕ, Fin p → ℕ) × ℕ) →
      ℕ × (ℕ → ℝ) => fun n => F (a n)) :=
    measurable_pi_iff.2 fun n => hFm.comp (measurable_pi_apply n)
  have h := (indepFun_cascadeRoot_subtreeArrays B hBm hB).comp measurable_id hG
  simpa only [F, Function.comp_def, id_eq] using h

/-- The root blocks and the entire sequence of child totals have a product law.
Unlike a marked-process assertion, this does not attach marks to individual
root atoms; it records exactly the independence and common shifted law already
available from the vertex-block construction. -/
theorem hasLaw_cascadeRoot_subtreeTotals_prod
    [IsProbabilityMeasure P]
    (nu : (p : ℕ) → ℕ → Measure ℝ)
    (rate : (p : ℕ) → ℕ → NNReal)
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ v k, Measurable (B v k))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P)
    (hlaw : ∀ v k, HasLaw (B v k)
      ((Po(rate v.1 k)).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k)) P)
    (r : ℕ) :
    HasLaw (fun ω =>
      ((fun k => B ⟨0, fun i => i.elim0⟩ k ω),
        fun n => ∑' beta : Fin r → ℕ,
          cascadeBranchWeight
            (fun p gamma m => nthLargestAtom m (poissonCountingMeasure
              (fun k => (B ⟨p + 1, Fin.cons n gamma⟩ k ω).1)
              (fun k l => (B ⟨p + 1, Fin.cons n gamma⟩ k ω).2 l))) beta))
      ((Measure.infinitePi fun k =>
        (Po(rate 0 k)).prod (Measure.infinitePi fun _ : ℕ => nu 0 k)).prod
        (Measure.infinitePi fun _ : ℕ =>
          (Measure.infinitePi fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ =>
            (Po(rate (vk.1.1 + 1) vk.2)).prod
              (Measure.infinitePi fun _ : ℕ => nu (vk.1.1 + 1) vk.2)).map
            (fun a => ∑' beta : Fin r → ℕ, cascadeBranchWeight
              (fun p gamma m => nthLargestAtom m (poissonCountingMeasure
                (fun k => (a (⟨p, gamma⟩, k)).1)
                (fun k l => (a (⟨p, gamma⟩, k)).2 l))) beta))) P := by
  let X (ω : Ω) (k : ℕ) := B ⟨0, fun i => i.elim0⟩ k ω
  let T (ω : Ω) (n : ℕ) := ∑' beta : Fin r → ℕ,
    cascadeBranchWeight
      (fun p gamma m => nthLargestAtom m (poissonCountingMeasure
        (fun k => (B ⟨p + 1, Fin.cons n gamma⟩ k ω).1)
        (fun k l => (B ⟨p + 1, Fin.cons n gamma⟩ k ω).2 l))) beta
  have hXm : Measurable X := measurable_pi_iff.2 fun k => hBm _ k
  have hTm : Measurable T := measurable_pi_iff.2 fun n => by
    apply measurable_tsum_cascadeBranchWeight
    intro p gamma m
    exact (measurable_nthLargestAtom m).comp
      (measurable_poissonCountingMeasure_comp
        (fun k => hBm ⟨p + 1, Fin.cons n gamma⟩ k))
  have hXlaw : HasLaw X (Measure.infinitePi fun k =>
      (Po(rate 0 k)).prod (Measure.infinitePi fun _ : ℕ => nu 0 k)) P :=
    HasLaw.infinitePi (fun k => hBm ⟨0, fun i => i.elim0⟩ k)
      (iIndepFun_cascadeVertexBlocks B hB ⟨0, fun i => i.elim0⟩)
      fun k => hlaw ⟨0, fun i => i.elim0⟩ k
  have hTlaw : HasLaw T (Measure.infinitePi fun _ : ℕ =>
      (Measure.infinitePi fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ =>
        (Po(rate (vk.1.1 + 1) vk.2)).prod
          (Measure.infinitePi fun _ : ℕ => nu (vk.1.1 + 1) vk.2)).map
        (fun a => ∑' beta : Fin r → ℕ, cascadeBranchWeight
          (fun p gamma m => nthLargestAtom m (poissonCountingMeasure
            (fun k => (a (⟨p, gamma⟩, k)).1)
            (fun k l => (a (⟨p, gamma⟩, k)).2 l))) beta)) P := by
    exact HasLaw.infinitePi (fun n => (measurable_pi_apply n).comp hTm)
      (iIndepFun_cascadeSubtreeTotals B hBm hB r)
      fun n => hasLaw_cascadeChildTotal nu rate B hBm hB hlaw n r
  have hind : IndepFun X T P := indepFun_cascadeRoot_subtreeTotals B hBm hB r
  refine ⟨(hXm.prodMk hTm).aemeasurable, ?_⟩
  calc
    P.map (fun ω => (X ω, T ω)) = (P.map X).prod (P.map T) :=
      (indepFun_iff_map_prod_eq_prod_map_map
        hXm.aemeasurable hTm.aemeasurable).1 hind
    _ = _ := congrArg₂ Measure.prod hXlaw.map_eq hTlaw.map_eq

/-- Ranking the root atoms preserves independence from any measurable mark vector
that is independent of the root blocks. This is a joint law, not a marked-block
representation: no permutation of the marks into the original blocks is asserted. -/
theorem hasLaw_rankedRoot_independent_marks
    [IsProbabilityMeasure P]
    (B : ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ k, Measurable (B k))
    (T : Ω → ℕ → ENNReal) (hTm : Measurable T)
    (hind : IndepFun (fun ω k => B k ω) T P) :
    HasLaw (fun ω =>
      ((fun m => nthLargestAtom m (poissonCountingMeasure
        (fun k => (B k ω).1) (fun k l => (B k ω).2 l))), T ω))
      (((P.map (fun ω k => B k ω)).map
        (fun a m => nthLargestAtom m (poissonCountingMeasure
          (fun k => (a k).1) (fun k l => (a k).2 l)))).prod (P.map T)) P := by
  let F (a : ℕ → ℕ × (ℕ → ℝ)) (m : ℕ) :=
    nthLargestAtom m (poissonCountingMeasure (fun k => (a k).1) (fun k l => (a k).2 l))
  have hF : Measurable F := measurable_pi_iff.2 fun m =>
    (measurable_nthLargestAtom m).comp
      (measurable_poissonCountingMeasure_comp (fun k => measurable_pi_apply k))
  have hXm : Measurable (fun ω k => B k ω) := measurable_pi_iff.2 hBm
  have hpair : P.map (fun ω => ((fun k => B k ω), T ω)) =
      (P.map (fun ω k => B k ω)).prod (P.map T) :=
    (indepFun_iff_map_prod_eq_prod_map_map hXm.aemeasurable hTm.aemeasurable).1 hind
  refine ⟨(hF.comp hXm |>.prodMk hTm).aemeasurable, ?_⟩
  change P.map (fun ω => (F (fun k => B k ω), T ω)) = _
  rw [show (fun ω => (F (fun k => B k ω), T ω)) =
    (Prod.map F id) ∘ (fun ω => ((fun k => B k ω), T ω)) from rfl]
  rw [← Measure.map_map (hF.prodMap measurable_id) (hXm.prodMk hTm), hpair]
  rw [← Measure.map_prod_map (P.map (fun ω k => B k ω)) (P.map T)
    hF measurable_id, Measure.map_id]

/-- Tonelli for an independent sequence of ranked atoms and a vector of identically
 distributed nonnegative marks. This is the product-law part of the marked Campbell
 computation; it requires neither finite marks nor a finite weighted sum. -/
theorem lintegral_ranked_independent_marks
    [IsProbabilityMeasure P]
    (U : Ω → ℕ → ENNReal) (T : Ω → ℕ → ENNReal)
    (hUm : Measurable U) (hTm : Measurable T)
    (hind : IndepFun U T P) (τ : Measure ENNReal) [IsProbabilityMeasure τ]
    (hTlaw : ∀ n, HasLaw (fun ω => T ω n) τ P)
    (g : ENNReal → ENNReal → ENNReal) (hg : Measurable (Function.uncurry g)) :
    (∫⁻ ω, ∑' n, g (U ω n) (T ω n) ∂P) =
      ∫⁻ ω, ∑' n, (∫⁻ t, g (U ω n) t ∂τ) ∂P := by
  have hUmn (n : ℕ) : Measurable (fun ω => U ω n) :=
    (measurable_pi_apply n).comp hUm
  have hTmn (n : ℕ) : Measurable (fun ω => T ω n) :=
    (measurable_pi_apply n).comp hTm
  have hgn (n : ℕ) : Measurable (fun ω => g (U ω n) (T ω n)) :=
    hg.comp (hUmn n |>.prodMk (hTmn n))
  have hinner (n : ℕ) : Measurable (fun x => ∫⁻ t, g x t ∂τ) :=
    hg.lintegral_prod_right'
  rw [lintegral_tsum (fun n => (hgn n).aemeasurable)]
  rw [lintegral_tsum (fun n => by
    exact ((hinner n).comp (hUmn n)).aemeasurable)]
  congr 1
  ext n
  have hpair : HasLaw (fun ω => (U ω n, T ω n))
      ((P.map fun ω => U ω n).prod τ) P := by
    have h := hind.comp ((measurable_pi_apply n :
      Measurable (fun x : ℕ → ENNReal => x n)))
      (measurable_pi_apply n : Measurable (fun x : ℕ → ENNReal => x n))
    have hprod := (indepFun_iff_map_prod_eq_prod_map_map
      (hUmn n).aemeasurable (hTmn n).aemeasurable).1 h
    exact ⟨((hUmn n).prodMk (hTmn n)).aemeasurable,
      hprod.trans (congrArg₂ Measure.prod rfl (hTlaw n).map_eq)⟩
  change ∫⁻ ω, Function.uncurry g (U ω n, T ω n) ∂P = _
  rw [hpair.lintegral_comp hg.aemeasurable]
  rw [lintegral_prod _ hg.aemeasurable]
  exact (lintegral_map' (hinner n).aemeasurable (hUmn n).aemeasurable)

/-- The independent-vertex cascade satisfies the marked Tonelli identity with
 the canonical law of a shifted depth-`r` subtree total. No finiteness of that
 total or of the marked root sum is assumed. -/
theorem lintegral_cascadeRoot_independent_subtreeTotals
    [IsProbabilityMeasure P]
    (nu : (p : ℕ) → ℕ → Measure ℝ)
    (rate : (p : ℕ) → ℕ → NNReal)
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ v k, Measurable (B v k))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P)
    (hlaw : ∀ v k, HasLaw (B v k)
      ((Po(rate v.1 k)).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k)) P)
    (r : ℕ) (g : ENNReal → ENNReal → ENNReal)
    (hg : Measurable (Function.uncurry g)) :
    (∫⁻ ω, ∑' n, g
      (nthLargestAtom n (poissonCountingMeasure
        (fun k => (B ⟨0, fun i => i.elim0⟩ k ω).1)
        (fun k l => (B ⟨0, fun i => i.elim0⟩ k ω).2 l)))
      (∑' beta : Fin r → ℕ, cascadeBranchWeight
        (fun p gamma m => nthLargestAtom m (poissonCountingMeasure
          (fun k => (B ⟨p + 1, Fin.cons n gamma⟩ k ω).1)
          (fun k l => (B ⟨p + 1, Fin.cons n gamma⟩ k ω).2 l))) beta) ∂P) =
    ∫⁻ ω, ∑' n, ∫⁻ t, g
      (nthLargestAtom n (poissonCountingMeasure
        (fun k => (B ⟨0, fun i => i.elim0⟩ k ω).1)
        (fun k l => (B ⟨0, fun i => i.elim0⟩ k ω).2 l))) t
      ∂((Measure.infinitePi fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ =>
        (Po(rate (vk.1.1 + 1) vk.2)).prod
          (Measure.infinitePi fun _ : ℕ => nu (vk.1.1 + 1) vk.2)).map
        (fun a => ∑' beta : Fin r → ℕ, cascadeBranchWeight
          (fun p gamma m => nthLargestAtom m (poissonCountingMeasure
            (fun k => (a (⟨p, gamma⟩, k)).1)
            (fun k l => (a (⟨p, gamma⟩, k)).2 l))) beta)) ∂P := by
  let U (ω : Ω) (n : ℕ) := nthLargestAtom n (poissonCountingMeasure
    (fun k => (B ⟨0, fun i => i.elim0⟩ k ω).1)
    (fun k l => (B ⟨0, fun i => i.elim0⟩ k ω).2 l))
  let T (ω : Ω) (n : ℕ) := ∑' beta : Fin r → ℕ, cascadeBranchWeight
    (fun p gamma m => nthLargestAtom m (poissonCountingMeasure
      (fun k => (B ⟨p + 1, Fin.cons n gamma⟩ k ω).1)
      (fun k l => (B ⟨p + 1, Fin.cons n gamma⟩ k ω).2 l))) beta
  let τ : Measure ENNReal := (Measure.infinitePi
      fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ =>
        (Po(rate (vk.1.1 + 1) vk.2)).prod
          (Measure.infinitePi fun _ : ℕ => nu (vk.1.1 + 1) vk.2)).map
      (fun a => ∑' beta : Fin r → ℕ, cascadeBranchWeight
        (fun p gamma m => nthLargestAtom m (poissonCountingMeasure
          (fun k => (a (⟨p, gamma⟩, k)).1)
          (fun k l => (a (⟨p, gamma⟩, k)).2 l))) beta)
  have hτ : IsProbabilityMeasure τ := by
    let h := hasLaw_cascadeChildTotal nu rate B hBm hB hlaw 0 r
    have heq : τ = P.map (fun ω => T ω 0) := h.map_eq.symm
    rw [heq]
    infer_instance
  let _ : IsProbabilityMeasure τ := hτ
  have hUm : Measurable U := measurable_pi_iff.2 fun n =>
    (measurable_nthLargestAtom n).comp
      (measurable_poissonCountingMeasure_comp (fun k => hBm _ k))
  have hTm : Measurable T := measurable_pi_iff.2 fun n => by
    apply measurable_tsum_cascadeBranchWeight
    intro p gamma m
    exact (measurable_nthLargestAtom m).comp
      (measurable_poissonCountingMeasure_comp
        (fun k => hBm ⟨p + 1, Fin.cons n gamma⟩ k))
  have hroot := indepFun_cascadeRoot_subtreeTotals B hBm hB r
  have hind : IndepFun U T P := by
    have hrank : Measurable (fun a : ℕ → ℕ × (ℕ → ℝ) => fun n =>
        nthLargestAtom n (poissonCountingMeasure
          (fun k => (a k).1) (fun k l => (a k).2 l))) :=
      measurable_pi_iff.2 fun n => (measurable_nthLargestAtom n).comp
        (measurable_poissonCountingMeasure_comp (fun k => measurable_pi_apply k))
    exact hroot.comp hrank measurable_id
  have hTlaw (n : ℕ) : HasLaw (fun ω => T ω n) τ P :=
    hasLaw_cascadeChildTotal nu rate B hBm hB hlaw n r
  exact lintegral_ranked_independent_marks U T hUm hTm hind τ hTlaw g hg

/-- Every parent in a globally independent vertex-block model has positive, finite
ranked atoms simultaneously. This uses the Section 2.2 Poisson--Dirichlet theorem. -/
theorem ae_cascadeRankedMass_pos_finite
    [IsProbabilityMeasure P] (zeta : ℕ → ℝ)
    (hzeta0 : ∀ p, 0 < zeta p) (hzeta1 : ∀ p, zeta p < 1)
    (nu : (p : ℕ) → ℕ → Measure ℝ)
    [∀ p k, IsProbabilityMeasure (nu p k)] (rate : (p : ℕ) → ℕ → NNReal)
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (hu : ∀ ω p gamma m, u ω p gamma m = nthLargestAtom m (poissonCountingMeasure
      (fun k => (B ⟨p, gamma⟩ k ω).1) (fun k l => (B ⟨p, gamma⟩ k ω).2 l)))
    (hBm : ∀ v k, Measurable (B v k))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P)
    (hlaw : ∀ v k, HasLaw (B v k)
      ((Po(rate v.1 k)).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k)) P)
    (hmu : ∀ p, zetaPoissonMeasure (zeta p) =
      Measure.sum fun k => (rate p k : ENNReal) • nu p k) :
    ∀ᵐ ω ∂P, ∀ p gamma m,
      u ω p gamma m ≠ 0 ∧
        u ω p gamma m ≠ ∞ := by
  have hv (v : Σ p : ℕ, Fin p → ℕ) :
      ∀ᵐ ω ∂P, ∀ m, u ω v.1 v.2 m ≠ 0 ∧
        u ω v.1 v.2 m ≠ ∞ := by
    have h := ae_poissonDirichletWeight (nu v.1) (rate v.1)
      (hzeta0 v.1) (hzeta1 v.1) (hBm v) (iIndepFun_cascadeVertexBlocks B hB v)
      (hlaw v) (hmu v.1)
      (M := fun ω => poissonCountingMeasure
        (fun k => (B v k ω).1) (fun k l => (B v k ω).2 l)) (fun _ => rfl)
    filter_upwards [h] with ω hω m
    rw [hu ω v.1 v.2 m]
    change nthLargestAtom m (poissonCountingMeasure
      (fun k => (B v k ω).1) (fun k l => (B v k ω).2 l)) ≠ 0 ∧
      nthLargestAtom m (poissonCountingMeasure
        (fun k => (B v k ω).1) (fun k l => (B v k ω).2 l)) ≠ ∞
    exact ⟨(hω.1 m).ne',
      ne_top_of_le_ne_top hω.2.1.ne
        (ENNReal.le_tsum (f := fun n => nthLargestAtom n
          (poissonCountingMeasure (fun k => (B v k ω).1)
            (fun k l => (B v k ω).2 l))) m)⟩
  have hall : ∀ᵐ ω ∂P, ∀ v : Σ p : ℕ, Fin p → ℕ,
      ∀ m, u ω v.1 v.2 m ≠ 0 ∧
        u ω v.1 v.2 m ≠ ∞ := ae_all_iff.2 hv
  filter_upwards [hall] with ω hω p gamma m
  exact hω ⟨p, gamma⟩ m

/-- At every depth the random total mass of the ranked vertex cascade is measurable. -/
theorem measurable_tsum_cascadeRankedMass
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (hu : ∀ ω p gamma m, u ω p gamma m = nthLargestAtom m (poissonCountingMeasure
      (fun k => (B ⟨p, gamma⟩ k ω).1) (fun k l => (B ⟨p, gamma⟩ k ω).2 l)))
    (hBm : ∀ v k, Measurable (B v k)) (r : ℕ) :
    Measurable fun ω => ∑' alpha : Fin r → ℕ,
      cascadeBranchWeight (u ω) alpha :=
  measurable_tsum_cascadeBranchWeight u (fun p gamma m => by
    simp_rw [hu]
    exact (measurable_nthLargestAtom m).comp
      (measurable_poissonCountingMeasure_comp (fun k => hBm ⟨p, gamma⟩ k))) r

/-- The ranked vertex construction has finite mass at depth one. -/
theorem ae_cascadeRankedMass_one_lt_top
    [IsProbabilityMeasure P] (zeta : ℕ → ℝ)
    (hzeta0 : 0 < zeta 0) (hzeta1 : zeta 0 < 1)
    (nu : (p : ℕ) → ℕ → Measure ℝ)
    [∀ p k, IsProbabilityMeasure (nu p k)] (rate : (p : ℕ) → ℕ → NNReal)
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (hu : ∀ ω p gamma m, u ω p gamma m = nthLargestAtom m (poissonCountingMeasure
      (fun k => (B ⟨p, gamma⟩ k ω).1) (fun k l => (B ⟨p, gamma⟩ k ω).2 l)))
    (hBm : ∀ v k, Measurable (B v k))
    (hlaw : ∀ v k, HasLaw (B v k)
      ((Po(rate v.1 k)).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k)) P)
    (hmu : zetaPoissonMeasure (zeta 0) =
      Measure.sum fun k => (rate 0 k : ENNReal) • nu 0 k) :
    ∀ᵐ ω ∂P, ∑' alpha : Fin 1 → ℕ,
      cascadeBranchWeight (u ω) alpha < ∞ := by
  have h := ae_tsum_cascadeBranchWeight_one_lt_top_of_ranked_poisson_blocks
    hzeta0 hzeta1 (nu 0) (rate 0) (B ⟨0, fun i => i.elim0⟩)
    (hBm ⟨0, fun i => i.elim0⟩)
    (hlaw ⟨0, fun i => i.elim0⟩) hmu
  filter_upwards [h] with ω hω
  rw [tsum_cascadeBranchWeight_succ] at hω ⊢
  simp only [cascadeBranchWeight_zero, one_mul] at hω ⊢
  convert hω using 1
  congr 1
  funext gamma
  rw [Subsingleton.elim gamma (fun i => i.elim0)]
  exact tsum_congr (hu ω 0 _)

/-- The weighted sum of marks bounded by `1 + x n` is controlled by the
unmarked root mass and the weighted excess. This does not assume a Poisson law. -/
theorem tsum_mul_le_tsum_add_tsum_mul
    (u x t : ℕ → ENNReal) (ht : ∀ n, t n ≤ 1 + x n) :
    (∑' n, u n * t n) ≤ (∑' n, u n) + ∑' n, u n * x n := by
  calc
    (∑' n, u n * t n) ≤ ∑' n, u n * (1 + x n) :=
      ENNReal.tsum_le_tsum fun n => mul_le_mul_of_nonneg_left (ht n) zero_le
    _ = (∑' n, u n) + ∑' n, u n * x n := by
      simp only [mul_add, mul_one, ENNReal.tsum_add]

/-- A weighted series of ranked atoms can be reindexed by the active atom indices.
The marks on the right must be transported along the rank equivalence. This is a
pointwise identity; it makes no assertion that the transported marks are independent. -/
theorem exists_tsum_ranked_mul_eq_tsum_active_mul
    {α : Type*} [Infinite α] (x : α → ℝ)
    (hx : Function.Injective x) (hpos : ∀ a, 0 < x a) (hs : Summable x)
    (t : ℕ → ENNReal) :
    ∃ e : α ≃ ℕ,
      (∑' n, nthLargestAtom n (Measure.sum fun a => Measure.dirac (x a)) * t n) =
        ∑' a, ENNReal.ofReal (x a) * t (e a) := by
  obtain ⟨e, he⟩ := exists_equiv_nthLargestAtom_sum_dirac x hx hpos hs
  refine ⟨e, ?_⟩
  rw [← e.tsum_eq (fun n =>
    nthLargestAtom n (Measure.sum fun a => Measure.dirac (x a)) * t n)]
  exact tsum_congr fun a => by rw [he a]

/-- A pointwise change of enumeration for every nonnegative test function, not just
for the total mass. The rank equivalence is not claimed to depend measurably on a
random environment; this lemma is used only after fixing that environment. -/
theorem tsum_comp_nthLargestAtom_sum_dirac
    {α : Type*} [Infinite α] (x : α → ℝ)
    (hx : Function.Injective x) (hpos : ∀ a, 0 < x a) (hs : Summable x)
    (f : ℝ → ENNReal) (hf : Measurable f) :
    (∑' n, f ((nthLargestAtom n
      (Measure.sum fun a : α => Measure.dirac (x a))).toReal)) =
      ∫⁻ y, f y ∂(Measure.sum fun a : α => Measure.dirac (x a)) := by
  obtain ⟨e, he⟩ := exists_equiv_nthLargestAtom_sum_dirac x hx hpos hs
  rw [lintegral_sum_measure]
  rw [← e.tsum_eq (fun n => f ((nthLargestAtom n
    (Measure.sum fun a : α => Measure.dirac (x a))).toReal))]
  apply tsum_congr
  intro a
  rw [he a, ENNReal.toReal_ofReal (hpos a).le, lintegral_dirac' _ hf]

/-- Reindex a nonnegative test on extended atom masses without converting the ranked
atoms to real numbers. This is useful when multiplying them by `ENNReal` subtree totals. -/
theorem tsum_comp_nthLargestAtom_sum_dirac_ennreal
    {α : Type*} [Infinite α] (x : α → ℝ)
    (hx : Function.Injective x) (hpos : ∀ a, 0 < x a) (hs : Summable x)
    (f : ENNReal → ENNReal) :
    (∑' n, f (nthLargestAtom n
      (Measure.sum fun a : α => Measure.dirac (x a)))) =
      ∑' a, f (ENNReal.ofReal (x a)) := by
  obtain ⟨e, he⟩ := exists_equiv_nthLargestAtom_sum_dirac x hx hpos hs
  rw [← e.tsum_eq (fun n => f (nthLargestAtom n
    (Measure.sum fun a : α => Measure.dirac (x a))))]
  exact tsum_congr fun a => by rw [he a]

/-- The active root blocks have infinitely many indices almost surely. This follows
from the infinite count of positive atoms; no enumeration of the atoms is chosen. -/
theorem ae_cascadeRoot_active_infinite
    [IsProbabilityMeasure P] {ζ : ℝ} (hζ : 0 < ζ)
    (nu : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (nu n)]
    (rate : ℕ → NNReal) (B : ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ k, Measurable (B k)) (hB : iIndepFun B P)
    (hlaw : ∀ k, HasLaw (B k)
      ((Po(rate k)).prod (Measure.infinitePi fun _ : ℕ => nu k)) P)
    (hmu : zetaPoissonMeasure ζ =
      Measure.sum fun k => (rate k : ENNReal) • nu k) :
    ∀ᵐ ω ∂P, Infinite {q : ℕ × ℕ // q.2 < (B q.1 ω).1} := by
  let M : Ω → Measure ℝ := fun ω => poissonCountingMeasure
    (fun k => (B k ω).1) (fun k l => (B k ω).2 l)
  have hL := (iIndepFun_hasLaw_poissonCountingMeasure_apply (κ := Unit)
    nu rate hBm hB hlaw hmu (fun _ => rfl)
    (A := fun _ => Set.Ioi (0 : ℝ)) (fun _ => measurableSet_Ioi)
    (fun i j hij => absurd (Subsingleton.elim i j) hij)).1 ()
  simp only [zetaPoissonMeasure_Ioi_zero hζ, ↓reduceIte] at hL
  have htop : ∀ᵐ ω ∂P, M ω (Set.Ioi 0) = ∞ := by
    have hd : ∀ᵐ y ∂(P.map fun ω => M ω (Set.Ioi 0)), y = ∞ := by
      rw [hL.map_eq, ae_dirac_eq]
      simp
    exact (ae_map_iff hL.aemeasurable (measurableSet_singleton ∞)).1 hd
  filter_upwards [htop] with ω hω
  have hcount := poissonCountingMeasure_apply_eq_encard_index
    (fun k => (B k ω).1) (fun k l => (B k ω).2 l)
    (A := Set.Ioi (0 : ℝ)) measurableSet_Ioi
  change M ω (Set.Ioi 0) = _ at hcount
  rw [hcount] at hω
  have hinf : {q : {q : ℕ × ℕ // q.2 < (B q.1 ω).1} |
      0 < (B q.1.1 ω).2 q.1.2}.Infinite :=
    Set.encard_eq_top_iff.mp (by exact_mod_cast hω)
  let _ : Infinite {q : {q : ℕ × ℕ // q.2 < (B q.1 ω).1} |
      0 < (B q.1.1 ω).2 q.1.2} := hinf.to_subtype
  exact Infinite.of_injective
    (fun q : {q : {q : ℕ × ℕ // q.2 < (B q.1 ω).1} |
      0 < (B q.1.1 ω).2 q.1.2} => q.1) Subtype.val_injective

/-- Every active root atom is strictly positive under a zeta intensity. -/
theorem ae_cascadeRoot_active_pos
    [IsProbabilityMeasure P] {ζ : ℝ}
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)]
    (rate : ℕ → NNReal) (B : ℕ → Ω → ℕ × (ℕ → ℝ))
    (hlaw : ∀ k, HasLaw (B k)
      ((Po(rate k)).prod (Measure.infinitePi fun _ : ℕ => nu k)) P)
    (hmu : zetaPoissonMeasure ζ =
      Measure.sum fun k => (rate k : ENNReal) • nu k) :
    ∀ᵐ ω ∂P, ∀ q : {q : ℕ × ℕ // q.2 < (B q.1 ω).1},
      0 < (B q.1.1 ω).2 q.1.2 := by
  have hmem : ∀ k, rate k ≠ 0 → ∀ᵐ x ∂nu k, x ∈ Set.Ioi (0 : ℝ) := by
    intro k hk
    rw [ae_iff]
    have hle := Measure.le_iff'.1
      (Measure.le_sum (fun n => (rate n : ENNReal) • nu n) k) (Set.Iic 0)
    rw [← hmu, zetaPoissonMeasure_Iic_zero] at hle
    rw [Measure.smul_apply, smul_eq_mul, nonpos_iff_eq_zero, mul_eq_zero] at hle
    have hz := hle.resolve_left (by simpa using hk)
    have heq : {x : ℝ | x ∉ Set.Ioi (0 : ℝ)} = Set.Iic 0 := by
      ext x
      simp
    rw [heq]
    exact hz
  filter_upwards [ae_poissonBlocks_forall_mem nu rate hlaw measurableSet_Ioi hmem]
    with ω hω q
  exact hω q.1.1 q.1.2 q.2

/-- The distinct active root atoms are summable, as a consequence of the
unmarked Poisson mass bound. -/
theorem ae_cascadeRoot_active_summable
    [IsProbabilityMeasure P] {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)]
    (rate : ℕ → NNReal) (B : ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ k, Measurable (B k))
    (hlaw : ∀ k, HasLaw (B k)
      ((Po(rate k)).prod (Measure.infinitePi fun _ : ℕ => nu k)) P)
    (hmu : zetaPoissonMeasure ζ =
      Measure.sum fun k => (rate k : ENNReal) • nu k) :
    ∀ᵐ ω ∂P, Summable (fun q : {q : ℕ × ℕ // q.2 < (B q.1 ω).1} =>
      (B q.1.1 ω).2 q.1.2) := by
  have hfin := ae_lintegral_poisson_lt_top_of_blocks
    (P := P) (M := fun ω => poissonCountingMeasure
      (fun k => (B k ω).1) (fun k l => (B k ω).2 l))
    nu rate hζ hζ1 hBm hlaw hmu (fun _ => rfl)
  have hpos := ae_cascadeRoot_active_pos nu rate B hlaw hmu
  filter_upwards [hfin, hpos] with ω hω hp
  have hsum := lintegral_poissonCountingMeasure_restrict_eq_tsum
    (fun k => (B k ω).1) (fun k l => (B k ω).2 l)
    (A := Set.Ioi (0 : ℝ)) measurableSet_Ioi ENNReal.measurable_ofReal
  simp only [Set.mem_Ioi] at hsum
  rw [hsum] at hω
  have hω' : (∑' q : {q : ℕ × ℕ // q.2 < (B q.1 ω).1},
      ENNReal.ofReal ((B q.1.1 ω).2 q.1.2)) < ∞ := by
    convert hω using 1
    apply tsum_congr
    intro q
    simp [hp q]
  exact summable_of_tsum_ofReal_lt_top (fun q => (hp q).le) hω'

/-- Active root masses are distinct almost surely, because the zeta intensity
has no atoms and each positive-rate block inherits this property. -/
theorem ae_cascadeRoot_active_injective
    [IsProbabilityMeasure P] {ζ : ℝ}
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)]
    (rate : ℕ → NNReal) (B : ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ k, Measurable (B k)) (hB : iIndepFun B P)
    (hlaw : ∀ k, HasLaw (B k)
      ((Po(rate k)).prod (Measure.infinitePi fun _ : ℕ => nu k)) P)
    (hmu : zetaPoissonMeasure ζ =
      Measure.sum fun k => (rate k : ENNReal) • nu k) :
    ∀ᵐ ω ∂P, Function.Injective
      (fun q : {q : ℕ × ℕ // q.2 < (B q.1 ω).1} => (B q.1.1 ω).2 q.1.2) := by
  have hnull (k : ℕ) (hk : rate k ≠ 0) : NullSingletonClass (nu k) := by
    have h := nullSingletonClass_map_block nu rate measurable_id
      (by rw [← hmu, Measure.map_id]; infer_instance) hk
    rwa [Measure.map_id] at h
  filter_upwards [ae_poissonBlocks_point_eq_iff_index_eq
    nu rate hBm hB hlaw hnull] with ω hω q s hqs
  exact (hω q s).1 hqs

/-- General-test rank-to-root-counting-measure identity, almost surely. The
rank equivalence is selected only after fixing the sample, not measurably. -/
theorem ae_tsum_rankedRoot_eq_lintegral
    [IsProbabilityMeasure P] {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)]
    (rate : ℕ → NNReal) (B : ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ k, Measurable (B k)) (hB : iIndepFun B P)
    (hlaw : ∀ k, HasLaw (B k)
      ((Po(rate k)).prod (Measure.infinitePi fun _ : ℕ => nu k)) P)
    (hmu : zetaPoissonMeasure ζ =
      Measure.sum fun k => (rate k : ENNReal) • nu k)
    (f : ENNReal → ENNReal) (hf : Measurable f) :
    ∀ᵐ ω ∂P, (∑' n, f (nthLargestAtom n (poissonCountingMeasure
      (fun k => (B k ω).1) (fun k l => (B k ω).2 l)))) =
      ∫⁻ x, f (ENNReal.ofReal x) ∂poissonCountingMeasure
        (fun k => (B k ω).1) (fun k l => (B k ω).2 l) := by
  filter_upwards [ae_cascadeRoot_active_infinite hζ nu rate B hBm hB hlaw hmu,
    ae_cascadeRoot_active_pos nu rate B hlaw hmu,
    ae_cascadeRoot_active_summable hζ hζ1 nu rate B hBm hlaw hmu,
    ae_cascadeRoot_active_injective nu rate B hBm hB hlaw hmu]
    with ω hinf hpos hsum hinj
  let α := {q : ℕ × ℕ // q.2 < (B q.1 ω).1}
  let _ : Infinite α := hinf
  let x : α → ℝ := fun q => (B q.1.1 ω).2 q.1.2
  have hr := tsum_comp_nthLargestAtom_sum_dirac_ennreal x hinj hpos hsum f
  rw [poissonCountingMeasure_eq_sum_dirac] at ⊢
  rw [hr, lintegral_sum_measure]
  exact (tsum_congr fun q => lintegral_dirac' (x q)
    (hf.comp ENNReal.measurable_ofReal)).symm

/-- Campbell's identity for independently marked ranked root atoms, before
specializing the mark law or normalizing its power moment. The mark may be infinite;
no measurable permutation of Poisson blocks is needed. -/
theorem lintegral_rankedRoot_marked_campbell
    [IsProbabilityMeasure P] {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)]
    (rate : ℕ → NNReal) (B : ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ k, Measurable (B k)) (hB : iIndepFun B P)
    (hlaw : ∀ k, HasLaw (B k)
      ((Po(rate k)).prod (Measure.infinitePi fun _ : ℕ => nu k)) P)
    (hmu : zetaPoissonMeasure ζ =
      Measure.sum fun k => (rate k : ENNReal) • nu k)
    (T : Ω → ℕ → ENNReal) (hTm : Measurable T)
    (hind : IndepFun (fun ω => fun k => B k ω) T P)
    (τ : Measure ENNReal) [IsProbabilityMeasure τ]
    (hTlaw : ∀ n, HasLaw (fun ω => T ω n) τ P)
    (g : ENNReal → ENNReal → ENNReal)
    (hg : Measurable (Function.uncurry g)) :
    (∫⁻ ω, ∑' n, g
      (nthLargestAtom n (poissonCountingMeasure
        (fun k => (B k ω).1) (fun k l => (B k ω).2 l))) (T ω n) ∂P) =
      ∫⁻ x, ∫⁻ t, g (ENNReal.ofReal x) t ∂τ ∂zetaPoissonMeasure ζ := by
  let U (ω : Ω) (n : ℕ) := nthLargestAtom n (poissonCountingMeasure
    (fun k => (B k ω).1) (fun k l => (B k ω).2 l))
  have hUm : Measurable U := measurable_pi_iff.2 fun n =>
    (measurable_nthLargestAtom n).comp
      (measurable_poissonCountingMeasure_comp hBm)
  have hind' : IndepFun U T P := by
    have hrank : Measurable (fun a : ℕ → ℕ × (ℕ → ℝ) => fun n =>
        nthLargestAtom n (poissonCountingMeasure
          (fun k => (a k).1) (fun k l => (a k).2 l))) :=
      measurable_pi_iff.2 fun n => (measurable_nthLargestAtom n).comp
        (measurable_poissonCountingMeasure_comp (fun k => measurable_pi_apply k))
    exact hind.comp hrank measurable_id
  rw [lintegral_ranked_independent_marks U T hUm hTm hind' τ hTlaw g hg]
  have hh : Measurable (fun x : ENNReal => ∫⁻ t, g x t ∂τ) :=
    hg.lintegral_prod_right'
  have hr := ae_tsum_rankedRoot_eq_lintegral hζ hζ1 nu rate B hBm hB hlaw hmu
    (fun x => ∫⁻ t, g x t ∂τ) hh
  rw [lintegral_congr_ae hr]
  exact (lintegral_poissonCountingMeasure nu rate hlaw
    (hh.comp ENNReal.measurable_ofReal)).trans (by rw [← hmu]; rfl)

/-- A counting measure with exactly one point in each block integrates a nonnegative
test by summing the tests at its points. This also works for extended-valued marks. -/
theorem lintegral_poissonCountingMeasure_singletons
    {S : Type*} [MeasurableSpace S] (x : ℕ → S)
    {f : S → ENNReal} (hf : Measurable f) :
    (∫⁻ y, f y ∂poissonCountingMeasure (fun _ => 1) (fun n _ => x n)) =
      ∑' n, f (x n) := by
  simp only [poissonCountingMeasure, lintegral_sum_measure, Finset.sum_range_one]
  exact tsum_congr fun n => lintegral_dirac' (x n) hf

/-- Conditional all-depth mass, given the root's weighted marked-sum estimate.
By the first-level decomposition this assumption is equivalent to the desired
positive-depth conclusion: it is an interface for the missing probability proof,
not itself an induction or an unconditional proof of Lemma 2.4. -/
theorem ae_cascadeRankedMass_lt_top_of_marked_step
    (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (hmarked : ∀ r,
      (∀ᵐ ω ∂P, ∑' n, u ω 0 (fun i : Fin 0 => i.elim0) n *
        (∑' beta : Fin r → ℕ,
          cascadeBranchWeight
            (fun p gamma m => u ω (p + 1) (Fin.cons n gamma) m)
            beta) < ∞))
    (r : ℕ) :
    ∀ᵐ ω ∂P, ∑' alpha : Fin r → ℕ,
      cascadeBranchWeight (u ω) alpha < ∞ := by
  cases r with
  | zero =>
    filter_upwards [] with ω
    rw [tsum_cascadeBranchWeight_zero]
    exact ENNReal.one_lt_top
  | succ r =>
    filter_upwards [hmarked r] with ω hω
    rw [tsum_cascadeBranchWeight_cons]
    exact hω

/-- If the marked first-level estimates are supplied, the genuine Poisson
vertices give positive probability weights at every depth. The positivity
input is unconditional; only the all-depth finiteness remains conditional. -/
theorem ae_cascadeRankedMass_div_probability_of_marked_step
    [IsProbabilityMeasure P] (zeta : ℕ → ℝ)
    (hzeta0 : ∀ p, 0 < zeta p) (hzeta1 : ∀ p, zeta p < 1)
    (nu : (p : ℕ) → ℕ → Measure ℝ)
    [∀ p k, IsProbabilityMeasure (nu p k)] (rate : (p : ℕ) → ℕ → NNReal)
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ENNReal)
    (hu : ∀ ω p gamma m, u ω p gamma m = nthLargestAtom m (poissonCountingMeasure
      (fun k => (B ⟨p, gamma⟩ k ω).1) (fun k l => (B ⟨p, gamma⟩ k ω).2 l)))
    (hBm : ∀ v k, Measurable (B v k))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P)
    (hlaw : ∀ v k, HasLaw (B v k)
      ((Po(rate v.1 k)).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k)) P)
    (hmu : ∀ p, zetaPoissonMeasure (zeta p) =
      Measure.sum fun k => (rate p k : ENNReal) • nu p k)
    (hmarked : ∀ r,
      ∀ᵐ ω ∂P, ∑' n, u ω 0 (fun i : Fin 0 => i.elim0) n *
        (∑' beta : Fin r → ℕ,
          cascadeBranchWeight
            (fun p gamma m => u ω (p + 1) (Fin.cons n gamma) m)
            beta) < ∞) (r : ℕ) :
    ∀ᵐ ω ∂P,
      (∑' alpha : Fin r → ℕ, cascadeBranchWeight (u ω) alpha /
        ∑' beta : Fin r → ℕ, cascadeBranchWeight (u ω) beta) = 1 ∧
      ∀ alpha : Fin r → ℕ,
        cascadeBranchWeight (u ω) alpha /
          (∑' beta : Fin r → ℕ, cascadeBranchWeight (u ω) beta) ≠ 0 := by
  have hf := ae_cascadeRankedMass_lt_top_of_marked_step u hmarked r
  have hp := ae_cascadeRankedMass_pos_finite
    zeta hzeta0 hzeta1 nu rate B u hu hBm hB hlaw hmu
  exact ae_cascadeBranchWeight_div_probability (u) r hf
    (hp.mono fun _ h p gamma m => (h p gamma m).1)
    (hp.mono fun _ h p gamma m => (h p gamma m).2)

end SpinGlasses
