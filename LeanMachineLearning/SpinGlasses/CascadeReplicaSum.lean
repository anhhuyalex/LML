/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeTree
public import LeanMachineLearning.ForMathlib.Topology.Algebra.InfiniteSum.PiProdENNReal

/-!
# Replica sums over the leaves of a cascade

For a finite set `ι` of replicas, a matrix `P` of prescribed overlaps and test functions `a l i`
of the label at level `i` of the `l`-th replica, the replica sum is
`∑_{α : ι → leaves, overlap (α l) (α l') = P l l'} ∏_l w(α l) ∏_i a l i (label of α l at level i)`.
This file contains the deterministic part of the first-level peeling: the replica sum of depth
`r + 1` is a sum over the first-level children `m : ι → ℕ`, each term being a product over the
blocks of replicas that share a child of replica sums of depth `r` in the corresponding subtree.
-/

@[expose] public section

open scoped ENNReal

namespace SpinGlasses

/-- The label of the child `α i` of the vertex `α|_i`. -/
def leafLabel {r : ℕ} (lab : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ) (α : Fin r → ℕ) (i : Fin r) : ℝ :=
  lab i (Fin.take i i.isLt.le α) (α i)

/-- The replica sum of depth `r`: leaves `α l` of the replicas `l`, with prescribed pairwise
overlaps `P l l'`, weighted by the branch weights and by the test functions `a l i` of the labels
along the paths. -/
noncomputable def replicaSum (r : ℕ) {ι : Type*} [Fintype ι] (P : ι → ι → ℕ)
    (a : ι → ℕ → ℝ → ℝ≥0∞) (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ≥0∞)
    (lab : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ) : ℝ≥0∞ :=
  ∑' α : ι → Fin r → ℕ,
    (if ∀ l l', (prefixOverlap (α l) (α l')).val = P l l' then 1 else 0) *
      ∏ l, (cascadeBranchWeight u (α l) * ∏ i : Fin r, a l i (leafLabel lab (α l) i))

/-- The overlap of two leaves below the children `n`, `n'` of the root. -/
theorem prefixOverlap_cons {r : ℕ} (n n' : ℕ) (β β' : Fin r → ℕ) :
    (prefixOverlap (Fin.cons n β : Fin (r + 1) → ℕ) (Fin.cons n' β')).val =
      if n = n' then (prefixOverlap β β').val + 1 else 0 := by
  unfold prefixOverlap
  by_cases h : n = n'
  · subst h
    simp only [ite_true]
    set k := Nat.findGreatest (fun p => ∀ i : Fin r, i.val < p → β i = β' i) r with hk
    have hk_le : k ≤ r := Nat.findGreatest_le r
    have hspec : ∀ i : Fin r, i.val < k → β i = β' i := fun i hi =>
      Nat.findGreatest_spec (P := fun p => ∀ j : Fin r, j.val < p → β j = β' j)
        (Nat.zero_le r) (by simp) i hi
    change Nat.findGreatest (fun p => ∀ i : Fin (r + 1), i.val < p →
      (Fin.cons n β : Fin (r + 1) → ℕ) i = (Fin.cons n β' : Fin (r + 1) → ℕ) i) (r + 1) = k + 1
    refine Nat.findGreatest_eq_iff.2 ⟨Nat.succ_le_succ hk_le, fun _ i hi => ?_,
      fun p hp hpr hP => ?_⟩
    · cases i using Fin.cases with
      | zero => rfl
      | succ j =>
        simp only [Fin.cons_succ]
        exact hspec j (by simpa using hi)
    · refine Nat.findGreatest_is_greatest (P := fun p => ∀ j : Fin r, j.val < p → β j = β' j)
        (n := r) (k := p - 1) (by omega) (by omega) fun j hj => ?_
      simpa using hP j.succ (by simp; omega)
  · simp only [h, ite_false]
    refine Nat.findGreatest_eq_zero_iff.2 fun p hp hpr hP => h ?_
    simpa using hP 0 hp

/-- The Gaussian exponential tilt of a test function of a label: the test is shifted by `c ζ` and
multiplied by `exp (c (y - c ζ / 2))`. -/
noncomputable def tiltTest (c ζ : ℝ) (f : ℝ → ℝ≥0∞) : ℝ → ℝ≥0∞ := fun y =>
  f (y - c * ζ) * ENNReal.ofReal (Real.exp (c * (y - c * ζ / 2)))

theorem measurable_tiltTest (c ζ : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (tiltTest c ζ f) :=
  (hf.comp (measurable_id.sub_const _)).mul
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_id.sub_const _ |>.const_mul c)))

@[simp] theorem tiltTest_zero (ζ : ℝ) (f : ℝ → ℝ≥0∞) : tiltTest 0 ζ f = f := by
  funext y
  simp [tiltTest]

/-- The label of the root child on a path through it. -/
@[simp] theorem leafLabel_cons_zero {r : ℕ} (lab : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ) (n : ℕ)
    (β : Fin r → ℕ) :
    leafLabel lab (Fin.cons n β : Fin (r + 1) → ℕ) 0 = lab 0 (fun i => i.elim0) n := by
  unfold leafLabel
  have h0 : ∀ (h : 0 ≤ r + 1) (c : Fin (r + 1) → ℕ),
      Fin.take 0 h c = fun i : Fin 0 => i.elim0 := fun _ _ => funext fun i => Fin.elim0 i
  simp only [Fin.val_zero, Fin.cons_zero]
  rw [h0 (Nat.zero_le _)]

/-- The labels below the root child are the labels of the subtree. -/
theorem leafLabel_cons_succ {r : ℕ} (lab : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ) (n : ℕ)
    (β : Fin r → ℕ) (i : Fin r) :
    leafLabel lab (Fin.cons n β : Fin (r + 1) → ℕ) i.succ =
      leafLabel (fun p γ k => lab (p + 1) (Fin.cons n γ) k) β i := by
  unfold leafLabel
  simp only [Fin.cons_succ, Fin.val_succ]
  rw [take_succ_cons n β i _ i.isLt.le]

/-- Reindexing the replicas does not change the replica sum. -/
theorem replicaSum_congr_equiv (r : ℕ) {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι' ≃ ι)
    (P : ι → ι → ℕ) (a : ι → ℕ → ℝ → ℝ≥0∞) (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ≥0∞)
    (lab : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ) :
    replicaSum r (fun l l' => P (e l) (e l')) (fun l => a (e l)) u lab =
      replicaSum r P a u lab := by
  unfold replicaSum
  rw [← (Equiv.arrowCongr e (Equiv.refl (Fin r → ℕ))).tsum_eq]
  refine tsum_congr fun α => ?_
  simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply]
  congr 1
  · exact if_congr (e.forall_congr fun l => e.forall_congr fun l' => by simp) rfl rfl
  · exact Fintype.prod_equiv e _ _ fun l => by simp

/-- Splitting a family of leaves of depth `r + 1` into the first-level children and the
leaves of the subtrees below them. -/
def consPiEquiv (ι : Type*) (r : ℕ) :
    ((ι → ℕ) × (ι → Fin r → ℕ)) ≃ (ι → Fin (r + 1) → ℕ) where
  toFun p l := Fin.cons (p.1 l) (p.2 l)
  invFun α := (fun l => α l 0, fun l => Fin.tail (α l))
  left_inv p := by
    refine Prod.ext (funext fun l => ?_) (funext fun l => ?_) <;> simp [Fin.tail_cons]
  right_inv α := funext fun l => Fin.cons_self_tail (α l)

/-- The weight of a leaf below the root child `n` splits into the root factor and the factor in
the subtree. -/
theorem cascadeBranchWeight_mul_prod_cons {r : ℕ} {ι : Type*} (a : ι → ℕ → ℝ → ℝ≥0∞)
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ≥0∞) (lab : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ) (l : ι)
    (n : ℕ) (β : Fin r → ℕ) :
    cascadeBranchWeight u (Fin.cons n β : Fin (r + 1) → ℕ) *
        ∏ i : Fin (r + 1), a l i (leafLabel lab (Fin.cons n β : Fin (r + 1) → ℕ) i) =
      (u 0 (fun i => i.elim0) n * a l 0 (lab 0 (fun i => i.elim0) n)) *
        (cascadeBranchWeight (fun p γ k => u (p + 1) (Fin.cons n γ) k) β *
          ∏ i : Fin r, a l (i + 1)
            (leafLabel (fun p γ k => lab (p + 1) (Fin.cons n γ) k) β i)) := by
  rw [cascadeBranchWeight_cons, Fin.prod_univ_succ]
  simp only [leafLabel_cons_zero, leafLabel_cons_succ, Fin.val_zero, Fin.val_succ]
  ring

/-- A sum over functions `β : ι → Y` of a product of one-variable weights, restricted to the
functions whose values satisfy a constraint on every pair in the same block of `f`, factors over
the blocks. -/
theorem tsum_pi_fiberwise {ι κ Y : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (f : ι → κ)
    (F : ι → Y → ℝ≥0∞) (C : ι → ι → Y → Y → Prop) [∀ l l' x y, Decidable (C l l' x y)] :
    ∑' β : ι → Y, (if ∀ l l', f l = f l' → C l l' (β l) (β l') then 1 else 0) *
        ∏ l, F l (β l) =
      ∏ q : κ, ∑' γ : {l // f l = q} → Y,
        (if ∀ a b : {l // f l = q}, C a.1 b.1 (γ a) (γ b) then 1 else 0) *
          ∏ a : {l // f l = q}, F a.1 (γ a) := by
  classical
  let e : (ι → Y) ≃ ((q : κ) → {l // f l = q} → Y) :=
    Equiv.piCongrFiberwise (f := f) fun q => Equiv.refl _
  rw [← e.symm.tsum_eq]
  have hβ : ∀ (γ : (q : κ) → {l // f l = q} → Y) (q : κ) (a : {l // f l = q}),
      e.symm γ a.1 = γ q a := by
    rintro γ q ⟨l, rfl⟩
    rfl
  have key : ∀ γ : (q : κ) → {l // f l = q} → Y,
      (if ∀ l l', f l = f l' → C l l' (e.symm γ l) (e.symm γ l') then (1 : ℝ≥0∞) else 0) *
          ∏ l, F l (e.symm γ l) =
        ∏ q, ((if ∀ a b : {l // f l = q}, C a.1 b.1 (γ q a) (γ q b) then 1 else 0) *
          ∏ a : {l // f l = q}, F a.1 (γ q a)) := by
    intro γ
    rw [Finset.prod_mul_distrib, Finset.prod_boole]
    have h1 : (∀ l l', f l = f l' → C l l' (e.symm γ l) (e.symm γ l')) ↔
        ∀ q, ∀ a b : {l // f l = q}, C a.1 b.1 (γ q a) (γ q b) := by
      refine ⟨fun h q a b => ?_, fun h l l' hll => ?_⟩
      · have := h a.1 b.1 (a.2.trans b.2.symm)
        rwa [hβ γ q a, hβ γ q b] at this
      · have := h (f l) ⟨l, rfl⟩ ⟨l', hll.symm⟩
        rwa [← hβ γ (f l) ⟨l, rfl⟩, ← hβ γ (f l) ⟨l', hll.symm⟩] at this
    have h2 : ∏ l, F l (e.symm γ l) = ∏ q, ∏ a : {l // f l = q}, F a.1 (γ q a) := by
      rw [← Fintype.prod_fiberwise f (fun l => F l (e.symm γ l))]
      refine Finset.prod_congr rfl fun q _ => Finset.prod_congr rfl fun a _ => ?_
      rw [hβ γ q a]
    simp only [Finset.mem_univ, true_implies]
    rw [h2, if_congr h1 rfl rfl]
  simp_rw [key]
  exact ENNReal.tsum_pi_prod (fun q (γ : {l // f l = q} → Y) =>
    (if ∀ a b : {l // f l = q}, C a.1 b.1 (γ a) (γ b) then 1 else 0) *
      ∏ a : {l // f l = q}, F a.1 (γ a))

section Inner

variable {r : ℕ} {ι : Type*} [Fintype ι] (P : ι → ι → ℕ) (a : ι → ℕ → ℝ → ℝ≥0∞)
  (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ≥0∞) (lab : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ) (m : ι → ℕ)

/-- The summand of the first-level peeling, rewritten with the root factors pulled out. -/
theorem replicaSum_succ_term (H : ∀ l l', m l = m l' ↔ 0 < P l l') (β : ι → Fin r → ℕ) :
    (if ∀ l l', (prefixOverlap (Fin.cons (m l) (β l) : Fin (r + 1) → ℕ)
        (Fin.cons (m l') (β l'))).val = P l l' then (1 : ℝ≥0∞) else 0) *
      ∏ l, (cascadeBranchWeight u (Fin.cons (m l) (β l) : Fin (r + 1) → ℕ) *
        ∏ i : Fin (r + 1), a l i (leafLabel lab (Fin.cons (m l) (β l) : Fin (r + 1) → ℕ) i)) =
    (∏ l, (u 0 (fun i => i.elim0) (m l) * a l 0 (lab 0 (fun i => i.elim0) (m l)))) *
      ((if ∀ l l', m l = m l' → (prefixOverlap (β l) (β l')).val + 1 = P l l' then 1 else 0) *
        ∏ l, (cascadeBranchWeight (fun p γ k => u (p + 1) (Fin.cons (m l) γ) k) (β l) *
            ∏ i : Fin r, a l (i + 1)
              (leafLabel (fun p γ k => lab (p + 1) (Fin.cons (m l) γ) k) (β l) i))) := by
  simp only [cascadeBranchWeight_mul_prod_cons, Finset.prod_mul_distrib]
  have hif : (∀ l l', (prefixOverlap (Fin.cons (m l) (β l) : Fin (r + 1) → ℕ)
        (Fin.cons (m l') (β l'))).val = P l l') ↔
      ∀ l l', m l = m l' → (prefixOverlap (β l) (β l')).val + 1 = P l l' := by
    refine forall_congr' fun l => forall_congr' fun l' => ?_
    rw [prefixOverlap_cons]
    by_cases h : m l = m l'
    · simp only [h, ite_true, forall_const]
    · have hP : P l l' = 0 := by
        by_contra hne
        exact h ((H l l').2 (Nat.pos_of_ne_zero hne))
      simp only [h, ite_false, hP, IsEmpty.forall_iff]
  rw [if_congr hif rfl rfl]
  ring

/-- The sum over the leaves of the subtree for the replicas of one block of equal first-level
children is the block sum of any of its members. -/
theorem fiber_sum_eq_replicaSum_block {κ : Type*} [DecidableEq κ] (f : ι → κ)
    (hf : ∀ l l', f l = f l' ↔ m l = m l') (H : ∀ l l', m l = m l' ↔ 0 < P l l') (l : ι) :
    (∑' γ : {l' // f l' = f l} → Fin r → ℕ,
      (if ∀ x y : {l' // f l' = f l}, (prefixOverlap (γ x) (γ y)).val + 1 = P x.1 y.1
        then (1 : ℝ≥0∞) else 0) *
        ∏ x : {l' // f l' = f l},
          (cascadeBranchWeight (fun p γ k => u (p + 1) (Fin.cons (m x.1) γ) k) (γ x) *
              ∏ i : Fin r, a x.1 (i + 1)
                (leafLabel (fun p γ k => lab (p + 1) (Fin.cons (m x.1) γ) k) (γ x) i))) =
      replicaSum r (ι := {l' // 0 < P l l'}) (fun x y => P x.1 y.1 - 1)
          (fun x i => a x.1 (i + 1)) (fun p γ k => u (p + 1) (Fin.cons (m l) γ) k)
          (fun p γ k => lab (p + 1) (Fin.cons (m l) γ) k) := by
  let e : {l' // f l' = f l} ≃ {l' // 0 < P l l'} :=
    Equiv.subtypeEquivRight fun l' => by rw [hf, eq_comm, H l l']
  rw [← replicaSum_congr_equiv r e]
  unfold replicaSum
  refine tsum_congr fun γ => ?_
  congr 1
  · refine if_congr (forall_congr' fun x => forall_congr' fun y => ?_) rfl rfl
    have hxy : 0 < P x.1 y.1 := (H x.1 y.1).1 ((hf _ _).1 (x.2.trans y.2.symm))
    simp only [e, Equiv.subtypeEquivRight_apply_coe]
    omega
  · refine Finset.prod_congr rfl fun x _ => ?_
    simp only [e, Equiv.subtypeEquivRight_apply_coe, (hf _ _).1 x.2]

/-- The product over the blocks of equal first-level children of the sums over the leaves of
the subtree is the product over the least elements of the blocks of the block sums. -/
theorem prod_fiber_sum_eq [LinearOrder ι] {κ : Type*} [Fintype κ] [DecidableEq κ] (f : ι → κ)
    (hs : Function.Surjective f) (hf : ∀ l l', f l = f l' ↔ m l = m l')
    (H : ∀ l l', m l = m l' ↔ 0 < P l l') :
    (∏ q : κ, ∑' γ : {l // f l = q} → Fin r → ℕ,
      (if ∀ x y : {l // f l = q}, (prefixOverlap (γ x) (γ y)).val + 1 = P x.1 y.1
        then (1 : ℝ≥0∞) else 0) *
        ∏ x : {l // f l = q},
          (cascadeBranchWeight (fun p γ k => u (p + 1) (Fin.cons (m x.1) γ) k) (γ x) *
              ∏ i : Fin r, a x.1 (i + 1)
                (leafLabel (fun p γ k => lab (p + 1) (Fin.cons (m x.1) γ) k) (γ x) i))) =
      ∏ l, (if ∀ l', 0 < P l l' → l ≤ l' then
        replicaSum r (ι := {l' // 0 < P l l'}) (fun x y => P x.1 y.1 - 1)
            (fun x i => a x.1 (i + 1)) (fun p γ k => u (p + 1) (Fin.cons (m l) γ) k)
            (fun p γ k => lab (p + 1) (Fin.cons (m l) γ) k) else 1) := by
  rw [← Finset.prod_filter]
  refine (Finset.prod_nbij f (fun l _ => Finset.mem_univ _) ?_ ?_ fun l _ => ?_).symm
  · intro l1 hl1 l2 hl2 h12
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hl1 hl2
    have hm : m l1 = m l2 := (hf l1 l2).1 h12
    exact le_antisymm (hl1 l2 ((H l1 l2).1 hm)) (hl2 l1 ((H l2 l1).1 hm.symm))
  · intro q _
    obtain ⟨l0, hl0⟩ := hs q
    obtain ⟨l, hl, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun l => f l = q) id
      ⟨l0, by simp [hl0]⟩
    refine ⟨l, ?_, (Finset.mem_filter.1 hl).2⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    intro l' hl'
    refine hmin l' ?_
    have : f l' = f l := (hf l' l).2 ((H l l').2 hl').symm
    simp [this, (Finset.mem_filter.1 hl).2]
  · exact (fiber_sum_eq_replicaSum_block (r := r) P a u lab m f hf H l).symm

/-- **First-level peeling, inner sum.** For first-level children `m` whose coincidences are those
prescribed by `P`, the sum over the leaves below them is the product of the root factors and, for
each block of replicas sharing a child (represented by its least element), the block sum in the
subtree of that child. -/
theorem tsum_replicaSum_succ_inner [LinearOrder ι] (H : ∀ l l', m l = m l' ↔ 0 < P l l') :
    ∑' β : ι → Fin r → ℕ,
      (if ∀ l l', (prefixOverlap (Fin.cons (m l) (β l) : Fin (r + 1) → ℕ)
        (Fin.cons (m l') (β l'))).val = P l l' then (1 : ℝ≥0∞) else 0) *
      ∏ l, (cascadeBranchWeight u (Fin.cons (m l) (β l) : Fin (r + 1) → ℕ) *
        ∏ i : Fin (r + 1), a l i (leafLabel lab (Fin.cons (m l) (β l) : Fin (r + 1) → ℕ) i)) =
    (∏ l, (u 0 (fun i => i.elim0) (m l) * a l 0 (lab 0 (fun i => i.elim0) (m l)))) *
      ∏ l, (if ∀ l', 0 < P l l' → l ≤ l' then
        replicaSum r (ι := {l' // 0 < P l l'}) (fun x y => P x.1 y.1 - 1)
            (fun x i => a x.1 (i + 1)) (fun p γ k => u (p + 1) (Fin.cons (m l) γ) k)
            (fun p γ k => lab (p + 1) (Fin.cons (m l) γ) k) else 1) := by
  simp_rw [replicaSum_succ_term P a u lab m H]
  rw [ENNReal.tsum_mul_left]
  congr 1
  have key : ∀ {κ : Type} [Fintype κ] [DecidableEq κ] (f : ι → κ), Function.Surjective f →
      (∀ l l', f l = f l' ↔ m l = m l') →
      (∑' β : ι → Fin r → ℕ,
        (if ∀ l l', m l = m l' → (prefixOverlap (β l) (β l')).val + 1 = P l l' then 1 else 0) *
          ∏ l, (cascadeBranchWeight (fun p γ k => u (p + 1) (Fin.cons (m l) γ) k) (β l) *
              ∏ i : Fin r, a l (i + 1)
                (leafLabel (fun p γ k => lab (p + 1) (Fin.cons (m l) γ) k) (β l) i))) =
      ∏ l, (if ∀ l', 0 < P l l' → l ≤ l' then
        replicaSum r (ι := {l' // 0 < P l l'}) (fun x y => P x.1 y.1 - 1)
            (fun x i => a x.1 (i + 1)) (fun p γ k => u (p + 1) (Fin.cons (m l) γ) k)
            (fun p γ k => lab (p + 1) (Fin.cons (m l) γ) k) else 1) := by
    intro κ _ _ f hs hf
    have h1 := tsum_pi_fiberwise f
      (fun l x => (cascadeBranchWeight (fun p γ k => u (p + 1) (Fin.cons (m l) γ) k) x *
        ∏ i : Fin r, a l (i + 1)
          (leafLabel (fun p γ k => lab (p + 1) (Fin.cons (m l) γ) k) x i)))
      (fun l l' x y => (prefixOverlap x y).val + 1 = P l l')
    simp_rw [hf] at h1
    rw [h1]
    exact prod_fiber_sum_eq (r := r) P a u lab m f hs hf H
  exact key (fun l => (⟨m l, Finset.mem_image_of_mem m (Finset.mem_univ l)⟩ :
      ↥(Finset.univ.image m)))
    (fun q => by
      obtain ⟨x, hx⟩ := q
      obtain ⟨l0, -, hl0⟩ := Finset.mem_image.1 hx
      exact ⟨l0, Subtype.ext hl0⟩)
    fun l l' => by simp

/-- The overlaps of leaves below the children `m l` force the coincidences of the children. -/
theorem forall_child_eq_iff_of_overlap {r : ℕ} {ι : Type*} (P : ι → ι → ℕ) (m : ι → ℕ)
    (β : ι → Fin r → ℕ)
    (h : ∀ l l', (prefixOverlap (Fin.cons (m l) (β l) : Fin (r + 1) → ℕ)
      (Fin.cons (m l') (β l'))).val = P l l') : ∀ l l', m l = m l' ↔ 0 < P l l' := by
  intro l l'
  have := h l l'
  rw [prefixOverlap_cons] at this
  by_cases hm : m l = m l'
  · simp only [hm, ↓reduceIte] at this
    simp only [hm, true_iff]
    omega
  · simp only [hm, ↓reduceIte] at this
    simp only [hm, false_iff, not_lt]
    omega

/-- **First-level peeling.** The replica sum of depth `r + 1` is the sum over the first-level
children `m` of the replicas whose coincidences are those prescribed by `P`; its summand is the
product of the root factors and of the block sums in the subtrees below the children. -/
theorem replicaSum_succ [LinearOrder ι] :
    replicaSum (r + 1) P a u lab =
      ∑' m : ι → ℕ, if ∀ l l', m l = m l' ↔ 0 < P l l' then
        (∏ l, (u 0 (fun i => i.elim0) (m l) * a l 0 (lab 0 (fun i => i.elim0) (m l)))) *
          ∏ l, (if ∀ l', 0 < P l l' → l ≤ l' then
            replicaSum r (ι := {l' // 0 < P l l'}) (fun x y => P x.1 y.1 - 1)
                (fun x i => a x.1 (i + 1)) (fun p γ k => u (p + 1) (Fin.cons (m l) γ) k)
                (fun p γ k => lab (p + 1) (Fin.cons (m l) γ) k) else 1)
        else 0 := by
  unfold replicaSum
  rw [← (consPiEquiv ι r).tsum_eq]
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun m => ?_
  by_cases H : ∀ l l', m l = m l' ↔ 0 < P l l'
  · rw [ite_eq_left_of_eq_true _ _ (eq_true H)]
    exact tsum_replicaSum_succ_inner (r := r) P a u lab m H
  · rw [ite_eq_right_of_eq_false _ _ (eq_false H)]
    refine ENNReal.tsum_eq_zero.2 fun β => ?_
    have : ¬ ∀ l l', (prefixOverlap (Fin.cons (m l) (β l) : Fin (r + 1) → ℕ)
        (Fin.cons (m l') (β l'))).val = P l l' := fun h =>
      H (forall_child_eq_iff_of_overlap P m β h)
    exact mul_eq_zero_of_left (ite_eq_right_of_eq_false _ _ (eq_false this)) _

end Inner

/-- The tilt of the constant test, multiplied over the levels, is the exponential of the
tilted energy: `∏ᵢ tilt(1)(yᵢ) = exp (t ∑ᵢ σᵢ yᵢ - t²/2 ∑ᵢ σᵢ² ζᵢ)`. -/
theorem prod_tiltTest_one {r : ℕ} (σ ζ : ℕ → ℝ) (t : ℝ) (y : Fin r → ℝ) :
    ∏ i : Fin r, tiltTest (t * σ i) (ζ i) (fun _ => 1) (y i) =
      ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * y i -
        t ^ 2 / 2 * ∑ i : Fin r, σ i ^ 2 * ζ i)) := by
  unfold tiltTest
  simp only [one_mul]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
  congr 2
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The weight of a replica in the tilted Gibbs measure: the branch weight and the exponential of
the energy `t ∑ᵢ σᵢ (label of α at level i)`. -/
theorem tiltTest_apply (c ζ : ℝ) (f : ℝ → ℝ≥0∞) (y : ℝ) :
    tiltTest c ζ f y = f (y - c * ζ) * tiltTest c ζ (fun _ => 1) y := by
  simp [tiltTest]

/-- **Sum of the replica sums over the overlap patterns.** Weighting the replica sums with the
tilted tests by a function `g` of the overlap pattern and summing over the patterns gives, up to
the factor `cⁿ` with `c = exp (-t²/2 ∑ᵢ σᵢ² ζᵢ)`, the sum over all `n`-tuples of leaves of the
tilted weights, the tests evaluated at the shifted labels `labelᵢ - t σᵢ ζᵢ`, and `g (pattern)`. -/
theorem sum_replicaSum_tilt_pattern (r n : ℕ) (σ ζ : ℕ → ℝ) (t : ℝ)
    (a : Fin n → ℕ → ℝ → ℝ≥0∞) (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ≥0∞)
    (lab : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ) (g : (Fin n → Fin n → Fin (r + 1)) → ℝ≥0∞) :
    ∑ P : Fin n → Fin n → Fin (r + 1), g P * replicaSum r (fun l l' => (P l l').val)
        (fun l i => tiltTest (t * σ i) (ζ i) (a l i)) u lab =
      ENNReal.ofReal (Real.exp (-(t ^ 2 / 2 * ∑ i : Fin r, σ i ^ 2 * ζ i))) ^ n *
        ∑' α : Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight u (α l) *
          ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab (α l) i)) *
          ∏ i : Fin r, a l i (leafLabel lab (α l) i - t * σ i * ζ i))) *
          g fun l l' => prefixOverlap (α l) (α l') := by
  classical
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(t ^ 2 / 2 * ∑ i : Fin r, σ i ^ 2 * ζ i))) with hc
  set W : Fin n → (Fin r → ℕ) → ℝ≥0∞ := fun l α => cascadeBranchWeight u α *
    ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i)) *
      ∏ i : Fin r, a l i (leafLabel lab α i - t * σ i * ζ i) with hW
  have hweight : ∀ (l : Fin n) (α : Fin r → ℕ), cascadeBranchWeight u α *
      ∏ i : Fin r, tiltTest (t * σ i) (ζ i) (a l i) (leafLabel lab α i) = c * W l α := by
    intro l α
    simp_rw [tiltTest_apply (t * σ _) (ζ _) (a l _)]
    rw [Finset.prod_mul_distrib, prod_tiltTest_one, sub_eq_add_neg, Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    simp only [hW, hc]
    ring
  -- each replica sum is `cⁿ` times the sum over the leaves with the prescribed overlaps
  have hpat : ∀ (P : Fin n → Fin n → Fin (r + 1)),
      replicaSum r (fun l l' => (P l l').val)
        (fun l i => tiltTest (t * σ i) (ζ i) (a l i)) u lab =
      c ^ n * ∑' α : Fin n → Fin r → ℕ,
        (if (fun l l' => prefixOverlap (α l) (α l')) = P then 1 else 0) * ∏ l, W l (α l) := by
    intro P
    unfold replicaSum
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun α => ?_
    have hind : (∀ l l', (prefixOverlap (α l) (α l')).val = (P l l').val) ↔
        (fun l l' => prefixOverlap (α l) (α l')) = P := by
      refine ⟨fun h => funext fun l => funext fun l' => Fin.ext (h l l'), fun h l l' => ?_⟩
      rw [← h]
    beta_reduce
    rw [Finset.prod_congr rfl fun l _ => hweight l (α l), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    by_cases h : (fun l l' => prefixOverlap (α l) (α l')) = P
    · simp only [eq_true (hind.2 h), eq_true h, ↓reduceIte]
      ring
    · simp only [eq_false (fun h' => h (hind.1 h')), eq_false h, ↓reduceIte]
      simp
  simp_rw [hpat]
  have h1 : ∀ P : Fin n → Fin n → Fin (r + 1), g P * (c ^ n * ∑' α : Fin n → Fin r → ℕ,
      (if (fun l l' => prefixOverlap (α l) (α l')) = P then 1 else 0) * ∏ l, W l (α l)) =
      c ^ n * ∑' α : Fin n → Fin r → ℕ,
        (if (fun l l' => prefixOverlap (α l) (α l')) = P then 1 else 0) *
          (g P * ∏ l, W l (α l)) := fun P => by
    rw [mul_left_comm, ← ENNReal.tsum_mul_left]
    congr 1
    refine tsum_congr fun α => ?_
    ring
  simp_rw [h1]
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
  congr 1
  refine tsum_congr fun α => ?_
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  ring

/-- The Gibbs average `⟨f(Rⁿ)⟩_t` of a function of the overlap matrix `Rₗₗ' = q (αˡ ∧ αˡ')` of `n`
replicas, for the leaf weights `w(α) exp (t g(α))`, where `g(α) = ∑ᵢ σᵢ (label of α at level i)`. -/
noncomputable def replicaGibbs (r n : ℕ) (σ : ℕ → ℝ) (q : Fin (r + 1) → ℝ) (t : ℝ)
    (f : (Fin n → Fin n → ℝ) → ℝ≥0∞) (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ≥0∞)
    (lab : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ) : ℝ≥0∞ :=
  (∑' α : Fin n → Fin r → ℕ, (∏ l, cascadeBranchWeight u (α l) *
      ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab (α l) i))) *
    f fun l l' => q (prefixOverlap (α l) (α l'))) /
  (∑' α : Fin r → ℕ, cascadeBranchWeight u α *
    ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i))) ^ n

/-- **The Gibbs average as a ratio of replica sums.** Summing the replica sums with the tilted
tests over the finitely many overlap patterns recovers the Gibbs average; the factor
`exp (-t²/2 ∑ σᵢ² ζᵢ)` of the tilt cancels between numerator and denominator. -/
theorem replicaGibbs_eq_div (r n : ℕ) (σ ζ : ℕ → ℝ) (q : Fin (r + 1) → ℝ) (t : ℝ)
    (f : (Fin n → Fin n → ℝ) → ℝ≥0∞) (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ≥0∞)
    (lab : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ) :
    replicaGibbs r n σ q t f u lab =
      (∑ P : Fin n → Fin n → Fin (r + 1), f (fun l l' => q (P l l')) *
        replicaSum r (fun l l' => (P l l').val)
          (fun _ i => tiltTest (t * σ i) (ζ i) (fun _ => 1)) u lab) /
      ∑ P : Fin n → Fin n → Fin (r + 1), replicaSum r (fun l l' => (P l l').val)
          (fun _ i => tiltTest (t * σ i) (ζ i) (fun _ => 1)) u lab := by
  classical
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(t ^ 2 / 2 * ∑ i : Fin r, σ i ^ 2 * ζ i))) with hc
  have hc0 : c ≠ 0 := by simp [hc, Real.exp_pos]
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  have h1 := sum_replicaSum_tilt_pattern r n σ ζ t (fun _ _ => fun _ => 1) u lab
    fun P => f fun l l' => q (P l l')
  have h2 := sum_replicaSum_tilt_pattern r n σ ζ t (fun _ _ => fun _ => 1) u lab fun _ => 1
  simp only [one_mul, Finset.prod_const_one, mul_one] at h1 h2
  rw [h1, h2, ENNReal.tsum_pi_prod fun _ α => cascadeBranchWeight u α *
      ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i))]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.mul_div_mul_left _ _ (pow_ne_zero n hc0) (ENNReal.pow_ne_top hct)]
  rfl

/-- A Gibbs average of a bounded function of the overlaps at `t = 0` is bounded by the same
constant when the total mass is positive and finite. -/
theorem replicaGibbs_zero_le (r n : ℕ) (σ : ℕ → ℝ) (q : Fin (r + 1) → ℝ)
    (f : (Fin n → Fin n → ℝ) → ℝ≥0∞) (C : ℝ≥0∞) (hf : ∀ x, f x ≤ C)
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ≥0∞) (lab : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ)
    (h0 : ∑' α : Fin r → ℕ, cascadeBranchWeight u α ≠ 0)
    (ht : ∑' α : Fin r → ℕ, cascadeBranchWeight u α ≠ ∞) :
    replicaGibbs r n σ q 0 f u lab ≤ C := by
  unfold replicaGibbs
  simp only [zero_mul, Real.exp_zero, ENNReal.ofReal_one, mul_one]
  have hn0 : (∑' α : Fin r → ℕ, cascadeBranchWeight u α) ^ n ≠ 0 := pow_ne_zero n h0
  have hnt : (∑' α : Fin r → ℕ, cascadeBranchWeight u α) ^ n ≠ ∞ := ENNReal.pow_ne_top ht
  rw [ENNReal.div_le_iff hn0 hnt]
  calc ∑' α : Fin n → Fin r → ℕ, (∏ l, cascadeBranchWeight u (α l)) *
        f (fun l l' => q (prefixOverlap (α l) (α l')))
      ≤ ∑' α : Fin n → Fin r → ℕ, (∏ l, cascadeBranchWeight u (α l)) * C :=
        ENNReal.tsum_le_tsum fun α => mul_le_mul_right (hf _) _
    _ = C * (∑' α : Fin r → ℕ, cascadeBranchWeight u α) ^ n := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_pi_prod fun _ α => cascadeBranchWeight u α]
        simp [mul_comm]

/-- The Gibbs average `⟨f(Rⁿ) ψ(label of αˡ⁰ at level i₀ - s)⟩_t` with a test of the label of one
replica at one level. -/
noncomputable def replicaGibbsAt (r n : ℕ) (σ : ℕ → ℝ) (q : Fin (r + 1) → ℝ) (t : ℝ)
    (f : (Fin n → Fin n → ℝ) → ℝ≥0∞) (l₀ : Fin n) (i₀ : Fin r) (ψ : ℝ → ℝ≥0∞) (s : ℝ)
    (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ≥0∞) (lab : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ) : ℝ≥0∞ :=
  (∑' α : Fin n → Fin r → ℕ, ((∏ l, cascadeBranchWeight u (α l) *
      ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab (α l) i))) *
    f fun l l' => q (prefixOverlap (α l) (α l'))) * ψ (leafLabel lab (α l₀) i₀ - s)) /
  (∑' α : Fin r → ℕ, cascadeBranchWeight u α *
    ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i))) ^ n

/-- The Gibbs average with a test of one label as a ratio of replica sums, provided that the shift
of the label is the one of the tilt. -/
theorem replicaGibbsAt_eq_div (r n : ℕ) (σ ζ : ℕ → ℝ) (q : Fin (r + 1) → ℝ) (t : ℝ)
    (f : (Fin n → Fin n → ℝ) → ℝ≥0∞) (l₀ : Fin n) (i₀ : Fin r) (ψ : ℝ → ℝ≥0∞) (s : ℝ)
    (hs : s = t * σ i₀ * ζ i₀) (u : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ≥0∞)
    (lab : (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ) :
    replicaGibbsAt r n σ q t f l₀ i₀ ψ s u lab =
      (∑ P : Fin n → Fin n → Fin (r + 1), f (fun l l' => q (P l l')) *
        replicaSum r (fun l l' => (P l l').val)
          (fun l i => tiltTest (t * σ i) (ζ i)
            (if l = l₀ ∧ i = i₀.val then ψ else fun _ => 1)) u lab) /
      ∑ P : Fin n → Fin n → Fin (r + 1), replicaSum r (fun l l' => (P l l').val)
          (fun _ i => tiltTest (t * σ i) (ζ i) (fun _ => 1)) u lab := by
  classical
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(t ^ 2 / 2 * ∑ i : Fin r, σ i ^ 2 * ζ i))) with hc
  have hc0 : c ≠ 0 := by simp [hc, Real.exp_pos]
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  have h1 := sum_replicaSum_tilt_pattern r n σ ζ t
    (fun l i => if l = l₀ ∧ i = i₀.val then ψ else fun _ => 1) u lab
    fun P => f fun l l' => q (P l l')
  have h2 := sum_replicaSum_tilt_pattern r n σ ζ t (fun _ _ => fun _ => 1) u lab fun _ => 1
  simp only [one_mul, Finset.prod_const_one, mul_one] at h2
  rw [h1, h2, ENNReal.tsum_pi_prod fun _ α => cascadeBranchWeight u α *
      ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel lab α i))]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.mul_div_mul_left _ _ (pow_ne_zero n hc0) (ENNReal.pow_ne_top hct)]
  unfold replicaGibbsAt
  congr 1
  refine tsum_congr fun α => ?_
  have htest : ∀ l : Fin n, ∏ i : Fin r, (if l = l₀ ∧ i.val = i₀.val then ψ else fun _ => 1)
      (leafLabel lab (α l) i - t * σ i * ζ i) =
      if l = l₀ then ψ (leafLabel lab (α l₀) i₀ - s) else 1 := by
    intro l
    by_cases hl : l = l₀
    · subst hl
      simp only [true_and, Fin.val_inj, ite_true, ite_apply]
      rw [Finset.prod_ite_eq' Finset.univ i₀ (fun i => ψ (leafLabel lab (α l) i - t * σ i * ζ i))]
      simp [hs]
    · simp [hl]
  simp_rw [htest]
  have hprod : ∀ A : Fin n → ℝ≥0∞, ∏ l, (A l * if l = l₀ then ψ (leafLabel lab (α l₀) i₀ - s)
      else 1) = (∏ l, A l) * ψ (leafLabel lab (α l₀) i₀ - s) := fun A => by
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ l₀]
    simp
  rw [hprod]
  ring

end SpinGlasses
