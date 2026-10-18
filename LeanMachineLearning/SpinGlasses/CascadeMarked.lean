/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeFiniteness
public import LeanMachineLearning.SpinGlasses.PoissonDirichletTransform

/-!
# Independently marked ranked Poisson cascade roots

Marked Tonelli, rank-to-counting-measure reindexing and the root Campbell formula.
The normalized positive-support Campbell formula is established for abstract independent
marks with a finite prescribed moment; its application to all cascade depths remains open.
-/

@[expose] public section

namespace SpinGlasses

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

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

/-- Dilation of the zeta intensity by a positive finite extended-nonnegative mark.
The zero and infinite mark cases require separate treatment when applying this
identity under a mark integral. -/
theorem lintegral_zetaPoissonMeasure_mul_ennreal
    {ζ : ℝ} (hζ : 0 < ζ) (t : ENNReal) (ht0 : t ≠ 0) (htfin : t ≠ ∞)
    (f : ℝ → ENNReal) (hf : Measurable f) :
    (∫⁻ x, f (x * t.toReal) ∂zetaPoissonMeasure ζ) =
      t ^ ζ * ∫⁻ x, f x ∂zetaPoissonMeasure ζ := by
  have htpos : 0 < t.toReal := ENNReal.toReal_pos ht0 htfin
  have hmap := zetaPoissonMeasure_map_mul hζ htpos
  have hm : Measurable (fun x : ℝ => x * t.toReal) := by fun_prop
  rw [← lintegral_map hf hm, hmap, lintegral_smul_measure]
  rw [smul_eq_mul, ← ENNReal.ofReal_rpow_of_pos htpos,
    ENNReal.ofReal_toReal htfin]

/-- For tests supported on positive masses, a zero mark contributes nothing. Thus
homogeneity can be integrated over a mark law allowing zero, provided it has no
infinite marks. This is the scaling step needed for positive-part mass bounds. -/
theorem lintegral_zetaPoissonMeasure_mul_mark_positive
    {ζ : ℝ} (hζ : 0 < ζ) (τ : Measure ENNReal)
    (hfinite : ∀ᵐ t ∂τ, t ≠ ∞)
    (f : ℝ → ENNReal) (hf : Measurable f) (hf0 : f 0 = 0) :
    (∫⁻ t, (∫⁻ x, f (x * t.toReal) ∂zetaPoissonMeasure ζ) ∂τ) =
      (∫⁻ t, t ^ ζ ∂τ) * (∫⁻ x, f x ∂zetaPoissonMeasure ζ) := by
  have hscale : ∀ᵐ t ∂τ,
      (∫⁻ x, f (x * t.toReal) ∂zetaPoissonMeasure ζ) =
        t ^ ζ * (∫⁻ x, f x ∂zetaPoissonMeasure ζ) := by
    filter_upwards [hfinite] with t ht
    by_cases ht0 : t = 0
    · subst t
      simp [hf0, hζ]
    · exact lintegral_zetaPoissonMeasure_mul_ennreal hζ t ht0 ht f hf
  have hpow : Measurable (fun t : ENNReal => t ^ ζ) := by fun_prop
  exact (lintegral_congr_ae hscale).trans (lintegral_mul_const _ hpow)

/-- A positive scaling constant normalizes the Campbell intensity on tests that
vanish at zero. This is precisely the test class needed for the fractional-moment
bound, even if the mark law charges zero. -/
theorem lintegral_zetaPoissonMeasure_normalized_marks_positive
    {ζ : ℝ} (hζ : 0 < ζ) (τ : Measure ENNReal)
    (hfinite : ∀ᵐ t ∂τ, t ≠ ∞) (c : ENNReal) (hc0 : c ≠ 0) (hcfin : c ≠ ∞)
    (hmoment : ∫⁻ t, t ^ ζ ∂τ = c ^ ζ)
    (f : ℝ → ENNReal) (hf : Measurable f) (hf0 : f 0 = 0) :
    (∫⁻ t, (∫⁻ x, f (x * (t / c).toReal) ∂zetaPoissonMeasure ζ) ∂τ) =
      ∫⁻ x, f x ∂zetaPoissonMeasure ζ := by
  have hratio : ∀ᵐ t ∂τ, t / c ≠ ∞ := by
    filter_upwards [hfinite] with t ht
    exact ENNReal.div_ne_top ht hc0
  have hscale : ∀ᵐ t ∂τ,
      (∫⁻ x, f (x * (t / c).toReal) ∂zetaPoissonMeasure ζ) =
        (t / c) ^ ζ * (∫⁻ x, f x ∂zetaPoissonMeasure ζ) := by
    filter_upwards [hratio] with t ht
    by_cases ht0 : t / c = 0
    · rw [ht0]
      simp [hf0, hζ]
    · exact lintegral_zetaPoissonMeasure_mul_ennreal hζ (t / c) ht0 ht f hf
  have hquot : Measurable (fun t : ENNReal => (t / c) ^ ζ) := by fun_prop
  rw [lintegral_congr_ae hscale, lintegral_mul_const _ hquot]
  have hpow : Measurable (fun t : ENNReal => t ^ ζ) := by fun_prop
  simp_rw [ENNReal.div_rpow_of_nonneg _ _ hζ.le]
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const _ hpow, hmoment]
  rw [ENNReal.mul_inv_cancel (ne_of_gt
    (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.mpr hc0) hζ.le))
    (ENNReal.rpow_ne_top_of_nonneg hζ.le hcfin), one_mul]

/-- The normalized positive-test Campbell identity for an independently marked
ranked root, without requiring the marked total to be finite. -/
theorem lintegral_rankedRoot_normalized_marked_positive
    [IsProbabilityMeasure P] {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)]
    (rate : ℕ → NNReal) (B : ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ k, Measurable (B k)) (hB : iIndepFun B P)
    (hlaw : ∀ k, HasLaw (B k)
      ((Po(rate k)).prod (Measure.infinitePi fun _ : ℕ => nu k)) P)
    (hmu : zetaPoissonMeasure ζ = Measure.sum fun k => (rate k : ENNReal) • nu k)
    (T : Ω → ℕ → ENNReal) (hTm : Measurable T)
    (hind : IndepFun (fun ω => fun k => B k ω) T P)
    (τ : Measure ENNReal) [IsProbabilityMeasure τ]
    (hTlaw : ∀ n, HasLaw (fun ω => T ω n) τ P)
    (hfinite : ∀ᵐ t ∂τ, t ≠ ∞)
    (c : ENNReal) (hc0 : c ≠ 0) (hcfin : c ≠ ∞)
    (hmoment : ∫⁻ t, t ^ ζ ∂τ = c ^ ζ)
    (f : ℝ → ENNReal) (hf : Measurable f) (hf0 : f 0 = 0) :
    (∫⁻ ω, ∑' n, f ((nthLargestAtom n (poissonCountingMeasure
      (fun k => (B k ω).1) (fun k l => (B k ω).2 l)) * T ω n / c).toReal) ∂P) =
      ∫⁻ x, f x ∂zetaPoissonMeasure ζ := by
  have hg : Measurable (Function.uncurry
      (fun (x t : ENNReal) => f ((x * t / c).toReal))) := by fun_prop
  rw [lintegral_rankedRoot_marked_campbell hζ hζ1 nu rate B hBm hB hlaw hmu
    T hTm hind τ hTlaw _ hg]
  have heq : ∀ᵐ x ∂zetaPoissonMeasure ζ, ∀ t : ENNReal,
      f ((ENNReal.ofReal x * t / c).toReal) = f (x * (t / c).toReal) := by
    have hpos : ∀ᵐ x ∂zetaPoissonMeasure ζ, x ∈ Set.Ioi (0 : ℝ) := by
      rw [ae_iff]
      change (zetaPoissonMeasure ζ) (Set.Ioi (0 : ℝ))ᶜ = 0
      rw [Set.compl_Ioi]
      exact zetaPoissonMeasure_Iic_zero ζ
    filter_upwards [hpos] with x hx
    intro t
    rw [mul_div_assoc, ENNReal.toReal_mul, ENNReal.toReal_ofReal hx.le]
  have hinner : ∀ᵐ x ∂zetaPoissonMeasure ζ,
      (∫⁻ t, f ((ENNReal.ofReal x * t / c).toReal) ∂τ) =
        ∫⁻ t, f (x * (t / c).toReal) ∂τ := by
    filter_upwards [heq] with x hx
    exact lintegral_congr fun t => hx t
  rw [lintegral_congr_ae hinner]
  rw [lintegral_lintegral_swap (by fun_prop :
    AEMeasurable (Function.uncurry
      (fun (x : ℝ) (t : ENNReal) => f (x * (t / c).toReal)))
      ((zetaPoissonMeasure ζ).prod τ))]
  exact lintegral_zetaPoissonMeasure_normalized_marks_positive hζ τ hfinite
    c hc0 hcfin hmoment f hf hf0

/-- Campbell's formula for the one-point-per-rank counting measure on positive tests.
The identity needs no assumption that the sum of marked masses is finite. -/
theorem lintegral_rankedRoot_normalized_counting_positive
    [IsProbabilityMeasure P] {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)]
    (rate : ℕ → NNReal) (B : ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ k, Measurable (B k)) (hB : iIndepFun B P)
    (hlaw : ∀ k, HasLaw (B k)
      ((Po(rate k)).prod (Measure.infinitePi fun _ : ℕ => nu k)) P)
    (hmu : zetaPoissonMeasure ζ = Measure.sum fun k => (rate k : ENNReal) • nu k)
    (T : Ω → ℕ → ENNReal) (hTm : Measurable T)
    (hind : IndepFun (fun ω => fun k => B k ω) T P)
    (τ : Measure ENNReal) [IsProbabilityMeasure τ]
    (hTlaw : ∀ n, HasLaw (fun ω => T ω n) τ P)
    (hfinite : ∀ᵐ t ∂τ, t ≠ ∞)
    (c : ENNReal) (hc0 : c ≠ 0) (hcfin : c ≠ ∞)
    (hmoment : ∫⁻ t, t ^ ζ ∂τ = c ^ ζ)
    (f : ℝ → ENNReal) (hf : Measurable f) (hf0 : f 0 = 0) :
    (∫⁻ ω, ∫⁻ x, f x ∂poissonCountingMeasure (fun _ => 1)
      (fun n _ => (nthLargestAtom n (poissonCountingMeasure
        (fun k => (B k ω).1) (fun k l => (B k ω).2 l)) * T ω n / c).toReal) ∂P) =
      ∫⁻ x, f x ∂zetaPoissonMeasure ζ := by
  have hsingle (ω : Ω) := lintegral_poissonCountingMeasure_singletons
    (fun n => (nthLargestAtom n (poissonCountingMeasure
      (fun k => (B k ω).1) (fun k l => (B k ω).2 l)) * T ω n / c).toReal) hf
  rw [show (∫⁻ ω, ∫⁻ x, f x ∂poissonCountingMeasure (fun _ => 1)
      (fun n _ => (nthLargestAtom n (poissonCountingMeasure
        (fun k => (B k ω).1) (fun k l => (B k ω).2 l)) * T ω n / c).toReal) ∂P) =
      ∫⁻ ω, ∑' n, f ((nthLargestAtom n (poissonCountingMeasure
        (fun k => (B k ω).1) (fun k l => (B k ω).2 l)) * T ω n / c).toReal) ∂P
    from lintegral_congr fun ω => hsingle ω]
  exact lintegral_rankedRoot_normalized_marked_positive hζ hζ1 nu rate B hBm hB
    hlaw hmu T hTm hind τ hTlaw hfinite c hc0 hcfin hmoment f hf hf0

/-- The two first-moment tests needed for the fractional-moment bound, for an
independently marked ranked root with normalized mark moment. -/
theorem lintegral_rankedRoot_normalized_two_tests
    [IsProbabilityMeasure P] {ζ a : ℝ}
    (hζ : 0 < ζ) (ha0 : 0 < a) (haζ : a < ζ) (hζ1 : ζ < 1)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)]
    (rate : ℕ → NNReal) (B : ℕ → Ω → ℕ × (ℕ → ℝ))
    (hBm : ∀ k, Measurable (B k)) (hB : iIndepFun B P)
    (hlaw : ∀ k, HasLaw (B k)
      ((Po(rate k)).prod (Measure.infinitePi fun _ : ℕ => nu k)) P)
    (hmu : zetaPoissonMeasure ζ = Measure.sum fun k => (rate k : ENNReal) • nu k)
    (T : Ω → ℕ → ENNReal) (hTm : Measurable T)
    (hind : IndepFun (fun ω => fun k => B k ω) T P)
    (τ : Measure ENNReal) [IsProbabilityMeasure τ]
    (hTlaw : ∀ n, HasLaw (fun ω => T ω n) τ P)
    (hfinite : ∀ᵐ t ∂τ, t ≠ ∞)
    (c : ENNReal) (hc0 : c ≠ 0) (hcfin : c ≠ ∞)
    (hmoment : ∫⁻ t, t ^ ζ ∂τ = c ^ ζ) :
    (∫⁻ ω, ∫⁻ x in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal x
      ∂poissonCountingMeasure (fun _ => 1)
        (fun n _ => (nthLargestAtom n (poissonCountingMeasure
          (fun k => (B k ω).1) (fun k l => (B k ω).2 l)) * T ω n / c).toReal) ∂P) =
      ENNReal.ofReal (ζ / (1 - ζ)) ∧
    (∫⁻ ω, ∫⁻ x, (Set.Ici (1 : ℝ)).indicator
      (fun y => ENNReal.ofReal y ^ a) x
      ∂poissonCountingMeasure (fun _ => 1)
        (fun n _ => (nthLargestAtom n (poissonCountingMeasure
          (fun k => (B k ω).1) (fun k l => (B k ω).2 l)) * T ω n / c).toReal) ∂P) =
      ENNReal.ofReal (ζ / (ζ - a)) := by
  have hs : Measurable ((Set.Ioo (0 : ℝ) 1).indicator ENNReal.ofReal) :=
    ENNReal.measurable_ofReal.indicator measurableSet_Ioo
  have hl : Measurable ((Set.Ici (1 : ℝ)).indicator
      (fun y => ENNReal.ofReal y ^ a)) :=
    (ENNReal.measurable_ofReal.pow_const a).indicator measurableSet_Ici
  constructor
  · have h := lintegral_rankedRoot_normalized_counting_positive hζ hζ1 nu rate B
      hBm hB hlaw hmu T hTm hind τ hTlaw hfinite c hc0 hcfin hmoment
      _ hs (by simp [Set.indicator])
    simp only [lintegral_indicator measurableSet_Ioo] at h
    rw [h, ← lintegral_indicator measurableSet_Ioo]
    have hp : (∫⁻ x, (Set.Ioo (0 : ℝ) 1).indicator ENNReal.ofReal x
        ∂zetaPoissonMeasure ζ) =
        ∫⁻ x, (Set.Ioo (0 : ℝ) 1).indicator
          (fun y => ENNReal.ofReal y ^ (1 : ℝ)) x ∂zetaPoissonMeasure ζ := by
      congr 1
      funext x
      simp only [ENNReal.rpow_one]
    rw [hp, lintegral_zetaPoissonMeasure_indicator_rpow hζ.le zero_le_one
      measurableSet_Ioo Set.Ioo_subset_Ioi_self]
    rw [show (1 : ℝ) - 1 - ζ = -ζ by ring]
    have hi : IntegrableOn (fun x : ℝ => ζ * x ^ (-ζ)) (Set.Ioo 0 1) :=
      ((intervalIntegral.integrableOn_Ioo_rpow_iff
        (by norm_num : (0 : ℝ) < 1)).2 (by linarith : -1 < -ζ)).const_mul ζ
    rw [← ofReal_integral_eq_lintegral_ofReal hi, integral_Ioo_zeta_rpow hζ1]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact mul_nonneg hζ.le (Real.rpow_nonneg hx.1.le _)
  · have h := lintegral_rankedRoot_normalized_counting_positive hζ hζ1 nu rate B
      hBm hB hlaw hmu T hTm hind τ hTlaw hfinite c hc0 hcfin hmoment
      _ hl (by simp [Set.indicator])
    exact h.trans (lintegral_zetaPoissonMeasure_Ici_rpow hζ ha0.le haζ)

end SpinGlasses
