/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeTree
public import LeanMachineLearning.ForMathlib.Probability.Independence.IndepInfinitePi

/-!
# Vertex-indexed Poisson cascade: local mass and probabilistic interfaces

The parent vertices have the single index type `Σ p : ℕ, Fin p → ℕ`. Each vertex owns
its own sequence of Poisson blocks; `nthLargestAtom` orders the resulting child masses.
Independence of the vertex blocks gives independence of entire child-subtree
arrays, their totals, and the root process. The all-depth finite-mass statement
below still assumes the marked-process induction explicitly: these independence
facts alone do not establish identical subtree laws or the ranked marked law.
-/

@[expose] public section

namespace SpinGlasses

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The ranked mass of child `m` at vertex `(p, gamma)`, from its Poisson blocks. -/
noncomputable def cascadePoissonMass
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (ω : Ω) (p : ℕ) (gamma : Fin p → ℕ) (m : ℕ) : ENNReal :=
  nthLargestAtom m (poissonCountingMeasure
    (fun k => (B ⟨p, gamma⟩ k ω).1) (fun k l => (B ⟨p, gamma⟩ k ω).2 l))

/-- Each ranked child mass is measurable as a function of the sample. -/
theorem measurable_cascadePoissonMass
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ v k, Measurable (B v k)) (p : ℕ) (gamma : Fin p → ℕ) (m : ℕ) :
    Measurable fun ω => cascadePoissonMass B ω p gamma m :=
  (measurable_nthLargestAtom m).comp (measurable_poissonCountingMeasure_comp
    (fun k => hBm ⟨p, gamma⟩ k))

/-- Restrict a globally independent array of vertex blocks to one vertex. -/
theorem iIndepFun_cascadeVertexBlocks
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P)
    (v : Σ p : ℕ, Fin p → ℕ) : iIndepFun (B v) P := by
  exact hB.precomp (g := fun k => (v, k)) (by
    intro k l h
    exact congrArg Prod.snd h)

/-- Restrict the global block family to the disjoint subtrees below the root.
The first index is the child label; the second describes a vertex inside that subtree. -/
theorem iIndepFun_cascadeSubtreeBlocks
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P) :
    iIndepFun (fun nk : (ℕ × (Σ p : ℕ, Fin p → ℕ)) × ℕ =>
      B ⟨nk.1.2.1 + 1, Fin.cons nk.1.1 nk.1.2.2⟩ nk.2) P := by
  let g : ((ℕ × (Σ p : ℕ, Fin p → ℕ)) × ℕ) →
      (Σ p : ℕ, Fin p → ℕ) × ℕ :=
    fun nk => (⟨nk.1.2.1 + 1, Fin.cons nk.1.1 nk.1.2.2⟩, nk.2)
  change iIndepFun (fun nk => B (g nk).1 (g nk).2) P
  apply hB.precomp (g := g)
  intro a b hab
  have hv := congrArg Prod.fst hab
  have hk := congrArg Prod.snd hab
  rcases a with ⟨⟨n, ⟨p, gamma⟩⟩, k⟩
  rcases b with ⟨⟨m, ⟨q, delta⟩⟩, l⟩
  have hp : p = q := Nat.succ.inj (congrArg Sigma.fst hv)
  cases hp
  have hcons : (Fin.cons n gamma : Fin (p + 1) → ℕ) =
      (Fin.cons m delta : Fin (p + 1) → ℕ) := by
    exact eq_of_heq (Sigma.mk.inj hv).2
  have hn : n = m := congrArg (fun f => f 0) hcons
  subst m
  have hg : gamma = delta := (Fin.cons_inj.mp hcons).2
  subst delta
  cases hk
  rfl

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
  have hXi : iIndepFun X P := by
    apply hB.precomp (g := fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ =>
      ((⟨vk.1.1 + 1, Fin.cons n vk.1.2⟩ : Σ p : ℕ, Fin p → ℕ), vk.2))
    intro a b hab
    have hv := congrArg Prod.fst hab
    have hk := congrArg Prod.snd hab
    rcases a with ⟨⟨p, gamma⟩, k⟩
    rcases b with ⟨⟨q, delta⟩, l⟩
    have hp : p = q := Nat.succ.inj (congrArg Sigma.fst hv)
    cases hp
    have hcons : (Fin.cons n gamma : Fin (p + 1) → ℕ) =
        (Fin.cons n delta : Fin (p + 1) → ℕ) :=
      eq_of_heq (Sigma.mk.inj hv).2
    have hg : gamma = delta := (Fin.cons_inj.mp hcons).2
    subst delta
    cases hk
    rfl
  have hmap := (iIndepFun_iff_map_fun_eq_infinitePi_map hXm).1 hXi
  refine ⟨(measurable_pi_iff.2 hXm).aemeasurable, ?_⟩
  rw [hmap]
  congr 1
  funext vk
  exact (hlaw ⟨vk.1.1 + 1, Fin.cons n vk.1.2⟩ vk.2).map_eq

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
        (fun p gamma m => cascadePoissonMass B ω (p + 1) (Fin.cons n gamma) m)
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
  simpa only [F, Function.comp_def, cascadePoissonMass] using h

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
  have hd : Disjoint root below := by
    simp only [Set.disjoint_left]
    intro vk hr hb
    have heq : vk.1.1 = 0 := hr
    have hlt : 0 < vk.1.1 := hb
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
        (fun p gamma m => cascadePoissonMass B ω (p + 1) (Fin.cons n gamma) m)
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
          (fun p gamma m => cascadePoissonMass B ω (p + 1) (Fin.cons n gamma) m)
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
  simpa only [F, Function.comp_def, cascadePoissonMass, id_eq] using h

/-- Every individual child-subtree inherits independence among all its blocks. -/
theorem iIndepFun_cascadeChildBlocks
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P)
    (n : ℕ) :
    iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ =>
      B ⟨vk.1.1 + 1, Fin.cons n vk.1.2⟩ vk.2) P := by
  exact (iIndepFun_cascadeSubtreeBlocks B hB).precomp
    (g := fun (vk : (Σ p : ℕ, Fin p → ℕ) × ℕ) => ((n, vk.1), vk.2)) (by
      intro a b h
      exact Prod.ext (congrArg (fun x => x.1.2) h) (congrArg (fun x => x.2) h))

/-- Every parent in a globally independent vertex-block model has positive, finite
ranked atoms simultaneously. This uses the Section 2.2 Poisson--Dirichlet theorem. -/
theorem ae_cascadePoissonMass_pos_finite
    [IsProbabilityMeasure P] (zeta : ℕ → ℝ)
    (hzeta0 : ∀ p, 0 < zeta p) (hzeta1 : ∀ p, zeta p < 1)
    (nu : (p : ℕ) → ℕ → Measure ℝ)
    [∀ p k, IsProbabilityMeasure (nu p k)] (rate : (p : ℕ) → ℕ → NNReal)
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ v k, Measurable (B v k))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P)
    (hlaw : ∀ v k, HasLaw (B v k)
      ((Po(rate v.1 k)).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k)) P)
    (hmu : ∀ p, zetaPoissonMeasure (zeta p) =
      Measure.sum fun k => (rate p k : ENNReal) • nu p k) :
    ∀ᵐ ω ∂P, ∀ p gamma m,
      cascadePoissonMass B ω p gamma m ≠ 0 ∧
        cascadePoissonMass B ω p gamma m ≠ ∞ := by
  have hv (v : Σ p : ℕ, Fin p → ℕ) :
      ∀ᵐ ω ∂P, ∀ m, cascadePoissonMass B ω v.1 v.2 m ≠ 0 ∧
        cascadePoissonMass B ω v.1 v.2 m ≠ ∞ := by
    have h := ae_poissonDirichletWeight (nu v.1) (rate v.1)
      (hzeta0 v.1) (hzeta1 v.1) (hBm v) (iIndepFun_cascadeVertexBlocks B hB v)
      (hlaw v) (hmu v.1)
      (M := fun ω => poissonCountingMeasure
        (fun k => (B v k ω).1) (fun k l => (B v k ω).2 l)) (fun _ => rfl)
    filter_upwards [h] with ω hω m
    exact ⟨(hω.1 m).ne',
      ne_top_of_le_ne_top hω.2.1.ne (ENNReal.le_tsum m)⟩
  have hall : ∀ᵐ ω ∂P, ∀ v : Σ p : ℕ, Fin p → ℕ,
      ∀ m, cascadePoissonMass B ω v.1 v.2 m ≠ 0 ∧
        cascadePoissonMass B ω v.1 v.2 m ≠ ∞ := ae_all_iff.2 hv
  filter_upwards [hall] with ω hω p gamma m
  exact hω ⟨p, gamma⟩ m

/-- At every depth the random total mass of the ranked vertex cascade is measurable. -/
theorem measurable_tsum_cascadePoissonMass
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ v k, Measurable (B v k)) (r : ℕ) :
    Measurable fun ω => ∑' alpha : Fin r → ℕ,
      cascadeBranchWeight (cascadePoissonMass B ω) alpha :=
  measurable_tsum_cascadeBranchWeight (cascadePoissonMass B)
    (fun p gamma m => measurable_cascadePoissonMass B hBm p gamma m) r

/-- The ranked vertex construction has finite mass at depth one. -/
theorem ae_cascadePoissonMass_one_lt_top
    [IsProbabilityMeasure P] (zeta : ℕ → ℝ)
    (hzeta0 : 0 < zeta 0) (hzeta1 : zeta 0 < 1)
    (nu : (p : ℕ) → ℕ → Measure ℝ)
    [∀ p k, IsProbabilityMeasure (nu p k)] (rate : (p : ℕ) → ℕ → NNReal)
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ v k, Measurable (B v k))
    (hlaw : ∀ v k, HasLaw (B v k)
      ((Po(rate v.1 k)).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k)) P)
    (hmu : zetaPoissonMeasure (zeta 0) =
      Measure.sum fun k => (rate 0 k : ENNReal) • nu 0 k) :
    ∀ᵐ ω ∂P, ∑' alpha : Fin 1 → ℕ,
      cascadeBranchWeight (cascadePoissonMass B ω) alpha < ∞ := by
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
  exact congrArg (fun v : Fin 0 → ℕ =>
    ∑' n, cascadePoissonMass B ω 0 v n)
    (Subsingleton.elim gamma (fun i => i.elim0))

/-- Conditional all-depth mass, given the root's weighted marked-sum estimate.
By the first-level decomposition this assumption is equivalent to the desired
positive-depth conclusion: it is an interface for the missing probability proof,
not itself an induction or an unconditional proof of Lemma 2.4. -/
theorem ae_cascadePoissonMass_lt_top_of_marked_step
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hmarked : ∀ r,
      (∀ᵐ ω ∂P, ∑' n, cascadePoissonMass B ω 0 (fun i : Fin 0 => i.elim0) n *
        (∑' beta : Fin r → ℕ,
          cascadeBranchWeight
            (fun p gamma m => cascadePoissonMass B ω (p + 1) (Fin.cons n gamma) m)
            beta) < ∞))
    (r : ℕ) :
    ∀ᵐ ω ∂P, ∑' alpha : Fin r → ℕ,
      cascadeBranchWeight (cascadePoissonMass B ω) alpha < ∞ := by
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
theorem ae_cascadePoissonMass_div_probability_of_marked_step
    [IsProbabilityMeasure P] (zeta : ℕ → ℝ)
    (hzeta0 : ∀ p, 0 < zeta p) (hzeta1 : ∀ p, zeta p < 1)
    (nu : (p : ℕ) → ℕ → Measure ℝ)
    [∀ p k, IsProbabilityMeasure (nu p k)] (rate : (p : ℕ) → ℕ → NNReal)
    (B : (Σ p : ℕ, Fin p → ℕ) → ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ v k, Measurable (B v k))
    (hB : iIndepFun (fun vk : (Σ p : ℕ, Fin p → ℕ) × ℕ => B vk.1 vk.2) P)
    (hlaw : ∀ v k, HasLaw (B v k)
      ((Po(rate v.1 k)).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k)) P)
    (hmu : ∀ p, zetaPoissonMeasure (zeta p) =
      Measure.sum fun k => (rate p k : ENNReal) • nu p k)
    (hmarked : ∀ r,
      ∀ᵐ ω ∂P, ∑' n, cascadePoissonMass B ω 0 (fun i : Fin 0 => i.elim0) n *
        (∑' beta : Fin r → ℕ,
          cascadeBranchWeight
            (fun p gamma m => cascadePoissonMass B ω (p + 1) (Fin.cons n gamma) m)
            beta) < ∞) (r : ℕ) :
    ∀ᵐ ω ∂P,
      (∑' alpha : Fin r → ℕ, cascadeBranchWeight (cascadePoissonMass B ω) alpha /
        ∑' beta : Fin r → ℕ, cascadeBranchWeight (cascadePoissonMass B ω) beta) = 1 ∧
      ∀ alpha : Fin r → ℕ,
        cascadeBranchWeight (cascadePoissonMass B ω) alpha /
          (∑' beta : Fin r → ℕ, cascadeBranchWeight (cascadePoissonMass B ω) beta) ≠ 0 := by
  have hf := ae_cascadePoissonMass_lt_top_of_marked_step B hmarked r
  have hp := ae_cascadePoissonMass_pos_finite
    zeta hzeta0 hzeta1 nu rate B hBm hB hlaw hmu
  exact ae_cascadeBranchWeight_div_probability (cascadePoissonMass B) r hf
    (hp.mono fun _ h p gamma m => (h p gamma m).1)
    (hp.mono fun _ h p gamma m => (h p gamma m).2)

end SpinGlasses
