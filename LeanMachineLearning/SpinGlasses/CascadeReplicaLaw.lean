/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeReplicaSum
public import LeanMachineLearning.SpinGlasses.CascadeBSReplica
public import LeanMachineLearning.SpinGlasses.CascadeParisiLaw

/-!
# Bolthausen--Sznitman invariance of the replica sums of a Ruelle cascade

Vertex data `d v = (blocks, labels)` as in `CascadeData`. The labels are real numbers. The replica
sum `cascadeReplicaSum r P a d` of depth `r` is `replicaSum` for the ranked atoms and labels of
`d`. The Gaussian exponential tilt acts on the tests `a l i`; the main theorem says that tilting
the tests does not change the joint law of any family of replica sums.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SpinGlasses

/-- The replica sum of depth `r` of the Ruelle cascade with vertex data `d`. -/
noncomputable def cascadeReplicaSum (r : ℕ) {ι : Type*} [Fintype ι] (P : ι → ι → ℕ)
    (a : ι → ℕ → ℝ → ℝ≥0∞)
    (d : (Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) : ℝ≥0∞ :=
  replicaSum r P a (fun p γ m => nthLargestAtom m (poissonCountingMeasure
    (fun k => ((d ⟨p, γ⟩).1 k).1) (fun k l => ((d ⟨p, γ⟩).1 k).2 l)))
    (fun p γ n => (d ⟨p, γ⟩).2 n)

/-- The replica sum is a measurable function of the vertex data. -/
theorem measurable_cascadeReplicaSum (r : ℕ) {ι : Type*} [Fintype ι] (P : ι → ι → ℕ)
    (a : ι → ℕ → ℝ → ℝ≥0∞) (ha : ∀ l i, Measurable (a l i)) :
    Measurable fun d : (Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ) =>
      cascadeReplicaSum r P a d := by
  unfold cascadeReplicaSum replicaSum
  refine Measurable.tsum fun α => ?_
  refine Measurable.mul measurable_const (Finset.measurable_prod _ fun l _ => ?_)
  refine Measurable.mul (Finset.measurable_prod _ fun i _ => measurable_cascadeAtom _ _)
    (Finset.measurable_prod _ fun i _ => (ha l i).comp ?_)
  exact (measurable_pi_apply (α l i)).comp (measurable_snd.comp (measurable_pi_apply _))

open Classical in
/-- The summand of the root step: the replicas sit at the points `z l = (u, (η, V))` of the root,
`u` being a ranked atom, `η` its label and `V` the data of its subtree. The points must coincide
exactly as prescribed by `P`; then the weight is the product of the root factors `u * a₀ l η`
and, for the least element `l` of each block, the block quantity `v l V` of the subtree. -/
noncomputable def replicaTheta {ι W : Type*} [Fintype ι] [LinearOrder ι] (P : ι → ι → ℕ)
    (a₀ : ι → ℝ → ℝ≥0∞) (v : ι → W → ℝ≥0∞) (z : ι → ℝ≥0∞ × (ℝ × W)) : ℝ≥0∞ :=
  if ∀ l l', ((z l).1 = (z l').1 ∧ (z l).2.1 = (z l').2.1) ↔ 0 < P l l' then
    (∏ l, ((z l).1 * a₀ l (z l).2.1)) *
      ∏ l, (if ∀ l', 0 < P l l' → l ≤ l' then v l (z l).2.2 else 1)
  else 0

/-- **First-level peeling of the cascade.** If the ranked atoms of the root are distinct, the
replica sum of depth `r + 1` is the sum over the root children `m` of `replicaTheta` evaluated at
the points `(uₘ, (ηₘ, Vₘ))`, where `Vₘ` collects the replica sums of depth `r` in the subtree
of the child `m`. -/
theorem cascadeReplicaSum_succ {r : ℕ} {ι W : Type*} [Fintype ι] [LinearOrder ι]
    (P : ι → ι → ℕ) (a : ι → ℕ → ℝ → ℝ≥0∞)
    (d : (Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ))
    (hinj : Function.Injective fun n => nthLargestAtom n (poissonCountingMeasure
      (fun k => ((d ⟨0, fun i => i.elim0⟩).1 k).1)
        (fun k l => ((d ⟨0, fun i => i.elim0⟩).1 k).2 l)))
    (V : ℕ → W) (v : ι → W → ℝ≥0∞)
    (hv : ∀ n l, v l (V n) = cascadeReplicaSum r (fun x y : {l' // 0 < P l l'} => P x.1 y.1 - 1)
      (fun x i => a x.1 (i + 1)) (fun w => d ⟨w.1 + 1, Fin.cons n w.2⟩)) :
    cascadeReplicaSum (r + 1) P a d = ∑' m : ι → ℕ, replicaTheta P (fun l => a l 0) v
      (fun l => (nthLargestAtom (m l) (poissonCountingMeasure
        (fun k => ((d ⟨0, fun i => i.elim0⟩).1 k).1)
        (fun k l => ((d ⟨0, fun i => i.elim0⟩).1 k).2 l)),
        ((d ⟨0, fun i => i.elim0⟩).2 (m l), V (m l)))) := by
  unfold cascadeReplicaSum
  rw [replicaSum_succ]
  refine tsum_congr fun m => ?_
  unfold replicaTheta
  have hiff : ∀ l l', (m l = m l' ↔ 0 < P l l') ↔
      ((nthLargestAtom (m l) (poissonCountingMeasure
        (fun k => ((d ⟨0, fun i => i.elim0⟩).1 k).1)
        (fun k l => ((d ⟨0, fun i => i.elim0⟩).1 k).2 l))
        = nthLargestAtom (m l') (poissonCountingMeasure
        (fun k => ((d ⟨0, fun i => i.elim0⟩).1 k).1)
        (fun k l => ((d ⟨0, fun i => i.elim0⟩).1 k).2 l))
        ∧ (d ⟨0, fun i => i.elim0⟩).2 (m l) = (d ⟨0, fun i => i.elim0⟩).2 (m l')) ↔
        0 < P l l') := by
    intro l l'
    have : (m l = m l') ↔ (nthLargestAtom (m l) (poissonCountingMeasure
        (fun k => ((d ⟨0, fun i => i.elim0⟩).1 k).1)
        (fun k l => ((d ⟨0, fun i => i.elim0⟩).1 k).2 l))
        = nthLargestAtom (m l') (poissonCountingMeasure
        (fun k => ((d ⟨0, fun i => i.elim0⟩).1 k).1)
        (fun k l => ((d ⟨0, fun i => i.elim0⟩).1 k).2 l))
        ∧ (d ⟨0, fun i => i.elim0⟩).2 (m l) = (d ⟨0, fun i => i.elim0⟩).2 (m l')) :=
      ⟨fun h => by rw [h]; exact ⟨rfl, rfl⟩, fun h => hinj h.1⟩
    rw [this]
  rw [if_congr (forall_congr' fun l => forall_congr' fun l' => hiff l l') rfl rfl]
  refine ite_congr rfl (fun _ => ?_) fun _ => rfl
  congr 1
  refine Finset.prod_congr rfl fun l _ => if_congr Iff.rfl ?_ rfl
  exact (hv (m l) l).symm

/-- The ranked atoms of independent ζ-Poisson blocks are almost surely distinct. -/
theorem ae_infinitePi_blocks_atoms_injective {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)] (rate : ℕ → ℝ≥0)
    (hmu : zetaPoissonMeasure ζ = Measure.sum fun k => (rate k : ℝ≥0∞) • nu k) :
    ∀ᵐ b ∂(Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)),
      Function.Injective fun n => nthLargestAtom n
        (poissonCountingMeasure (fun k => (b k).1) (fun k l => (b k).2 l)) := by
  filter_upwards [ae_infinitePi_blocks_good hζ0 hζ1 nu rate hmu] with b hb
  obtain ⟨hinf, hpos, hsum, hinj⟩ := hb
  obtain ⟨e, he⟩ := exists_equiv_nthLargestAtom_sum_dirac
    (fun q : {q : ℕ × ℕ // q.2 < (b q.1).1} => (b q.1.1).2 q.1.2) hinj hpos hsum
  have hM := poissonCountingMeasure_eq_sum_dirac (fun k => (b k).1) (fun k l => (b k).2 l)
  have hn : ∀ n, nthLargestAtom n
      (poissonCountingMeasure (fun k => (b k).1) (fun k l => (b k).2 l)) =
      ENNReal.ofReal ((b (e.symm n).1.1).2 (e.symm n).1.2) := fun n => by
    rw [hM, ← he (e.symm n), Equiv.apply_symm_apply]
  intro n n' h
  simp only [hn] at h
  exact e.symm.injective (hinj ((ENNReal.ofReal_eq_ofReal_iff (hpos _).le (hpos _).le).1 h))

/-- Cancelling a nonzero finite factor in `ℝ≥0∞`. -/
theorem ennreal_eq_of_mul_right_eq {a b c : ℝ≥0∞} (h0 : c ≠ 0) (ht : c ≠ ∞) (h : a * c = b * c) :
    a = b := by
  calc a = a * c * c⁻¹ := by rw [mul_assoc, ENNReal.mul_inv_cancel h0 ht, mul_one]
    _ = b * c * c⁻¹ := by rw [h]
    _ = b := by rw [mul_assoc, ENNReal.mul_inv_cancel h0 ht, mul_one]

/-- Applying the tilt to the points of the root step is the tilt of the root tests. -/
theorem replicaTheta_tilt {ι W : Type*} [Fintype ι] [LinearOrder ι] (c ζ : ℝ) (P : ι → ι → ℕ)
    (a₀ : ι → ℝ → ℝ≥0∞) (v : ι → W → ℝ≥0∞) (z : ι → ℝ≥0∞ × (ℝ × W)) :
    replicaTheta P (fun l => tiltTest c ζ (a₀ l)) v z =
      replicaTheta P a₀ v (fun l => ((z l).1 * ENNReal.ofReal
        (Real.exp (c * ((z l).2.1 - c * ζ / 2))), ((z l).2.1 - c * ζ, (z l).2.2))) := by
  unfold replicaTheta
  have hiff : ∀ l l', (((z l).1 = (z l').1 ∧ (z l).2.1 = (z l').2.1) ↔ 0 < P l l') ↔
      ((((z l).1 * ENNReal.ofReal (Real.exp (c * ((z l).2.1 - c * ζ / 2))) =
        (z l').1 * ENNReal.ofReal (Real.exp (c * ((z l').2.1 - c * ζ / 2)))) ∧
        (z l).2.1 - c * ζ = (z l').2.1 - c * ζ) ↔ 0 < P l l') := by
    intro l l'
    have : ((z l).1 = (z l').1 ∧ (z l).2.1 = (z l').2.1) ↔
        ((z l).1 * ENNReal.ofReal (Real.exp (c * ((z l).2.1 - c * ζ / 2))) =
          (z l').1 * ENNReal.ofReal (Real.exp (c * ((z l').2.1 - c * ζ / 2)))) ∧
          (z l).2.1 - c * ζ = (z l').2.1 - c * ζ := by
      refine ⟨fun ⟨h1, h2⟩ => ⟨by rw [h1, h2], by rw [h2]⟩, fun ⟨h1, h2⟩ => ?_⟩
      have h2' : (z l).2.1 = (z l').2.1 := sub_left_inj.1 h2
      rw [h2'] at h1
      exact ⟨ennreal_eq_of_mul_right_eq (by simp [Real.exp_pos]) ENNReal.ofReal_ne_top h1, h2'⟩
    rw [this]
  rw [if_congr (forall_congr' fun l => forall_congr' fun l' => hiff l l') rfl rfl]
  refine ite_congr rfl (fun _ => ?_) fun _ => rfl
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  unfold tiltTest
  ring

/-- The root test of the replica sums is measurable. -/
theorem measurable_replicaTheta {ι W : Type*} [Fintype ι] [LinearOrder ι] [MeasurableSpace W]
    (P : ι → ι → ℕ) (a₀ : ι → ℝ → ℝ≥0∞) (v : ι → W → ℝ≥0∞) (ha₀ : ∀ l, Measurable (a₀ l))
    (hv : ∀ l, Measurable (v l)) : Measurable (replicaTheta P a₀ v) := by
  unfold replicaTheta
  refine Measurable.ite ?_ ?_ measurable_const
  · have hz : ∀ l, Measurable fun z : ι → ℝ≥0∞ × (ℝ × W) => z l := measurable_pi_apply
    have hA : ∀ l l', MeasurableSet {z : ι → ℝ≥0∞ × (ℝ × W) |
        (z l).1 = (z l').1 ∧ (z l).2.1 = (z l').2.1} := fun l l' =>
      (measurableSet_eq_fun (measurable_fst.comp (hz l)) (measurable_fst.comp (hz l'))).inter
        (measurableSet_eq_fun (measurable_fst.comp (measurable_snd.comp (hz l)))
          (measurable_fst.comp (measurable_snd.comp (hz l'))))
    have : {z : ι → ℝ≥0∞ × (ℝ × W) | ∀ l l', ((z l).1 = (z l').1 ∧ (z l).2.1 = (z l').2.1) ↔
        0 < P l l'} = ⋂ l, ⋂ l', {z | ((z l).1 = (z l').1 ∧ (z l).2.1 = (z l').2.1) ↔
        0 < P l l'} := by
      ext z
      simp
    rw [this]
    refine MeasurableSet.iInter fun l => MeasurableSet.iInter fun l' => ?_
    by_cases hP : 0 < P l l'
    · simpa only [hP, iff_true] using hA l l'
    · have h2 : {z : ι → ℝ≥0∞ × (ℝ × W) | ((z l).1 = (z l').1 ∧ (z l).2.1 = (z l').2.1) ↔
          0 < P l l'} = {z : ι → ℝ≥0∞ × (ℝ × W) |
          (z l).1 = (z l').1 ∧ (z l).2.1 = (z l').2.1}ᶜ := by
        ext z
        simp [hP]
      rw [h2]
      exact (hA l l').compl
  · refine Measurable.mul (Finset.measurable_prod _ fun l _ => ?_)
      (Finset.measurable_prod _ fun l _ => ?_)
    · exact (measurable_fst.comp (measurable_pi_apply l)).mul
        ((ha₀ l).comp (measurable_fst.comp (measurable_snd.comp (measurable_pi_apply l))))
    · exact Measurable.ite (MeasurableSet.const _) ((hv l).comp (measurable_snd.comp
        (measurable_snd.comp (measurable_pi_apply l)))) measurable_const

/-- The root blocks together with the labels of the root children and a measurable functional of
the subtree below each root child: its joint law. The functional of the subtrees is
independent of the root data and identically distributed. -/
theorem hasLaw_cascadeRoot_marks {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Ξ W : Type*} [MeasurableSpace Ξ] [MeasurableSpace W]
    (nu₀ : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu₀ k)] (rate₀ : ℕ → ℝ≥0)
    (ρ : Measure Ξ) [IsProbabilityMeasure ρ]
    (𝔡 : ℕ → Measure ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)))
    (h𝔡₀ : 𝔡 0 = (Measure.infinitePi fun k =>
      Po(rate₀ k).prod (Measure.infinitePi fun _ : ℕ => nu₀ k)).prod
        (Measure.infinitePi fun _ : ℕ => ρ))
    (D : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) (hDm : ∀ v, Measurable (D v))
    (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P) [∀ p, IsProbabilityMeasure (𝔡 p)]
    (Y : ((Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) → W) (hY : Measurable Y) :
    HasLaw (fun ω => ((D ⟨0, fun i => i.elim0⟩ ω).1,
        fun n => ((D ⟨0, fun i => i.elim0⟩ ω).2 n,
          Y fun v : Σ p : ℕ, Fin p → ℕ => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω)))
      ((Measure.infinitePi fun k =>
        Po(rate₀ k).prod (Measure.infinitePi fun _ : ℕ => nu₀ k)).prod
        (Measure.infinitePi fun _ : ℕ => ρ.prod
          ((Measure.infinitePi fun v : Σ p : ℕ, Fin p → ℕ => 𝔡 (v.1 + 1)).map Y))) P := by
  have hjoint := hasLaw_cascadeRoot_subtreeData D hDm hD 𝔡 hDlaw
  rw [h𝔡₀] at hjoint
  have hzip := map_prod_prod_zip (Measure.infinitePi fun k =>
      Po(rate₀ k).prod (Measure.infinitePi fun _ : ℕ => nu₀ k)) ρ
    (Measure.infinitePi fun v : Σ p : ℕ, Fin p → ℕ => 𝔡 (v.1 + 1))
  set μ := Measure.infinitePi fun k =>
    Po(rate₀ k).prod (Measure.infinitePi fun _ : ℕ => nu₀ k) with hμ
  set σ := Measure.infinitePi fun v : Σ p : ℕ, Fin p → ℕ => 𝔡 (v.1 + 1) with hσ
  have hz : Measurable fun p : ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) × (ℕ → ((Σ p : ℕ, Fin p → ℕ) →
      (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ))) => (p.1.1, fun n => (p.1.2 n, p.2 n)) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun n =>
      ((measurable_pi_apply n).comp (measurable_snd.comp measurable_fst)).prodMk
        ((measurable_pi_apply n).comp measurable_snd))
  have hG : Measurable fun q : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ × ((Σ p : ℕ, Fin p → ℕ) →
      (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ))) => (q.1, fun n => ((q.2 n).1, Y (q.2 n).2)) :=
    measurable_fst.prodMk (measurable_pi_iff.2 fun n =>
      (measurable_fst.comp ((measurable_pi_apply n).comp measurable_snd)).prodMk
        (hY.comp (measurable_snd.comp ((measurable_pi_apply n).comp measurable_snd))))
  have hg1 : Measurable fun p : ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) × (ℕ → ((Σ p : ℕ, Fin p → ℕ) →
      (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ))) => (p.1.1, fun n => (p.1.2 n, Y (p.2 n))) :=
    measurable_fst.comp measurable_fst |>.prodMk (measurable_pi_iff.2 fun n =>
      ((measurable_pi_apply n).comp (measurable_snd.comp measurable_fst)).prodMk
        (hY.comp ((measurable_pi_apply n).comp measurable_snd)))
  have hmap : ((μ.prod (Measure.infinitePi fun _ : ℕ => ρ)).prod
      (Measure.infinitePi fun _ : ℕ => σ)).map
      (fun p => (p.1.1, fun n => (p.1.2 n, Y (p.2 n)))) =
      μ.prod (Measure.infinitePi fun _ : ℕ => ρ.prod (σ.map Y)) := by
    have e1 : (fun p : ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) × (ℕ → ((Σ p : ℕ, Fin p → ℕ) →
        (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ))) => (p.1.1, fun n => (p.1.2 n, Y (p.2 n)))) =
        (fun q : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ × ((Σ p : ℕ, Fin p → ℕ) →
          (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ))) => (q.1, fun n => ((q.2 n).1, Y (q.2 n).2))) ∘
        (fun p => (p.1.1, fun n => (p.1.2 n, p.2 n))) := rfl
    rw [e1, ← Measure.map_map hG hz, hzip]
    have hid : Measurable fun x : Ξ × ((Σ p : ℕ, Fin p → ℕ) →
        (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) => (x.1, Y x.2) :=
      measurable_fst.prodMk (hY.comp measurable_snd)
    have h1 := Measure.infinitePi_map_pi (fun _ : ℕ => ρ.prod σ) (f := fun _ => fun x : Ξ ×
      ((Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) => (x.1, Y x.2)) fun _ => hid
    have h2 := Measure.map_prod_map μ (Measure.infinitePi fun _ : ℕ => ρ.prod σ) (f := id)
      (g := fun f : ℕ → Ξ × ((Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) =>
        fun n => ((f n).1, Y (f n).2)) measurable_id (measurable_pi_iff.2 fun n =>
          hid.comp (measurable_pi_apply n))
    rw [h1, Measure.map_id] at h2
    have h3 : (ρ.prod σ).map (fun x : Ξ × ((Σ p : ℕ, Fin p → ℕ) →
        (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) => (x.1, Y x.2)) = ρ.prod (σ.map Y) := by
      have := Measure.map_prod_map ρ σ (f := id) (g := Y) measurable_id hY
      rw [Measure.map_id] at this
      exact this.symm
    rw [h3] at h2
    exact h2.symm
  exact (⟨hg1.aemeasurable, hmap⟩ : HasLaw _ _ _).comp hjoint

/-- **The inductive step of the Bolthausen--Sznitman invariance of the replica sums.** -/
theorem identDistrib_cascadeReplicaSum_tilt_succ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (r : ℕ) (ζ σ : ℕ → ℝ) (t : ℝ) (hζ0 : 0 < ζ 0) (hζ1 : ζ 0 < 1)
    (nu₀ : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu₀ k)] (rate₀ : ℕ → ℝ≥0)
    (hmu : zetaPoissonMeasure (ζ 0) = Measure.sum fun k => (rate₀ k : ℝ≥0∞) • nu₀ k)
    (𝔡 : ℕ → Measure ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ))) [∀ p, IsProbabilityMeasure (𝔡 p)]
    (h𝔡₀ : 𝔡 0 = (Measure.infinitePi fun k =>
      Po(rate₀ k).prod (Measure.infinitePi fun _ : ℕ => nu₀ k)).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
    (D : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) (hDm : ∀ v, Measurable (D v))
    (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
    {X : Type} (ι : X → Type) [∀ x, Fintype (ι x)] [∀ x, LinearOrder (ι x)]
    (Pm : ∀ x, ι x → ι x → ℕ) (a : ∀ x, ι x → ℕ → ℝ → ℝ≥0∞)
    (ha : ∀ x l i, Measurable (a x l i))
    (hih : IdentDistrib
      (fun ω (x' : Σ x, ι x) => cascadeReplicaSum r
        (fun y z : {l' // 0 < Pm x'.1 x'.2 l'} => Pm x'.1 y.1 z.1 - 1)
        (fun y i => tiltTest (t * σ (i + 1)) (ζ (i + 1)) (a x'.1 y.1 (i + 1)))
        (fun v => D ⟨v.1 + 1, Fin.cons 0 v.2⟩ ω))
      (fun ω (x' : Σ x, ι x) => cascadeReplicaSum r
        (fun y z : {l' // 0 < Pm x'.1 x'.2 l'} => Pm x'.1 y.1 z.1 - 1)
        (fun y i => a x'.1 y.1 (i + 1)) (fun v => D ⟨v.1 + 1, Fin.cons 0 v.2⟩ ω)) P P) :
    IdentDistrib
      (fun ω x => cascadeReplicaSum (r + 1) (Pm x)
        (fun l i => tiltTest (t * σ i) (ζ i) (a x l i)) (fun v => D v ω))
      (fun ω x => cascadeReplicaSum (r + 1) (Pm x) (a x) (fun v => D v ω)) P P := by
  classical
  have h𝔡p : ∀ p, IsProbabilityMeasure (𝔡 p) := inferInstance
  -- the vectors of subtree quantities, untilted and tilted
  obtain ⟨Vm, hVm⟩ : ∃ Vm : ((Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) →
      (Σ x, ι x) → ℝ≥0∞, ∀ s x', Vm s x' = cascadeReplicaSum r
        (fun y z : {l' // 0 < Pm x'.1 x'.2 l'} => Pm x'.1 y.1 z.1 - 1)
        (fun y i => a x'.1 y.1 (i + 1)) s := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Wm, hWm⟩ : ∃ Wm : ((Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) →
      (Σ x, ι x) → ℝ≥0∞, ∀ s x', Wm s x' = cascadeReplicaSum r
        (fun y z : {l' // 0 < Pm x'.1 x'.2 l'} => Pm x'.1 y.1 z.1 - 1)
        (fun y i => tiltTest (t * σ (i + 1)) (ζ (i + 1)) (a x'.1 y.1 (i + 1))) s :=
    ⟨_, fun _ _ => rfl⟩
  have hVmeas : Measurable Vm := measurable_pi_iff.2 fun x' => by
    have e : (fun s => Vm s x') = fun s => cascadeReplicaSum r
        (fun y z : {l' // 0 < Pm x'.1 x'.2 l'} => Pm x'.1 y.1 z.1 - 1)
        (fun y i => a x'.1 y.1 (i + 1)) s := funext fun s => hVm s x'
    rw [e]
    exact measurable_cascadeReplicaSum r _ _ fun l i => ha _ _ _
  have hWmeas : Measurable Wm := measurable_pi_iff.2 fun x' => by
    have e : (fun s => Wm s x') = fun s => cascadeReplicaSum r
        (fun y z : {l' // 0 < Pm x'.1 x'.2 l'} => Pm x'.1 y.1 z.1 - 1)
        (fun y i => tiltTest (t * σ (i + 1)) (ζ (i + 1)) (a x'.1 y.1 (i + 1))) s :=
      funext fun s => hWm s x'
    rw [e]
    exact measurable_cascadeReplicaSum r _ _ fun l i => measurable_tiltTest _ _ (ha _ _ _)
  set σm := Measure.infinitePi fun v : Σ p : ℕ, Fin p → ℕ => 𝔡 (v.1 + 1) with hσm
  have hlawS : HasLaw (fun ω (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons 0 v.2⟩ ω) σm P :=
    hasLaw_cascadeSubtreeData D hDm hD 𝔡 hDlaw 0
  have hSm : Measurable fun ω (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons 0 v.2⟩ ω :=
    measurable_pi_iff.2 fun v => hDm _
  have hκ : σm.map Wm = σm.map Vm := by
    have e1 : (fun ω (x' : Σ x, ι x) => cascadeReplicaSum r
        (fun y z : {l' // 0 < Pm x'.1 x'.2 l'} => Pm x'.1 y.1 z.1 - 1)
        (fun y i => tiltTest (t * σ (i + 1)) (ζ (i + 1)) (a x'.1 y.1 (i + 1)))
        (fun v => D ⟨v.1 + 1, Fin.cons 0 v.2⟩ ω)) =
        Wm ∘ fun ω (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons 0 v.2⟩ ω :=
      funext fun ω => funext fun x' => (hWm _ _).symm
    have e2 : (fun ω (x' : Σ x, ι x) => cascadeReplicaSum r
        (fun y z : {l' // 0 < Pm x'.1 x'.2 l'} => Pm x'.1 y.1 z.1 - 1)
        (fun y i => a x'.1 y.1 (i + 1)) (fun v => D ⟨v.1 + 1, Fin.cons 0 v.2⟩ ω)) =
        Vm ∘ fun ω (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons 0 v.2⟩ ω :=
      funext fun ω => funext fun x' => (hVm _ _).symm
    have h := hih.map_eq
    rw [e1, e2, ← Measure.map_map hWmeas hSm, ← Measure.map_map hVmeas hSm, hlawS.map_eq] at h
    exact h
  have hκp : IsProbabilityMeasure (σm.map Vm) := inferInstance
  -- the marks of the root children and their joint law
  have hlawY : ∀ {Y : ((Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)) →
      (Σ x, ι x) → ℝ≥0∞}, Measurable Y →
      HasLaw (fun ω => ((D ⟨0, fun i => i.elim0⟩ ω).1,
        fun n => ((D ⟨0, fun i => i.elim0⟩ ω).2 n,
          Y fun v : Σ p : ℕ, Fin p → ℕ => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω)))
        ((Measure.infinitePi fun k =>
          Po(rate₀ k).prod (Measure.infinitePi fun _ : ℕ => nu₀ k)).prod
          (Measure.infinitePi fun _ : ℕ => (gaussianReal 0 1).prod (σm.map Y))) P :=
    fun hY => hasLaw_cascadeRoot_marks nu₀ rate₀ (gaussianReal 0 1) 𝔡 h𝔡₀ D hDm hD hDlaw _ hY
  have hΦV := hlawY hVmeas
  have hΦW := hlawY hWmeas
  rw [hκ] at hΦW
  -- the two functionals of the root points
  obtain ⟨FU, hFU⟩ : ∃ FU : ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ × ((Σ x, ι x) → ℝ≥0∞))) →
      X → ℝ≥0∞, ∀ p x, FU p x = ∑' m : ι x → ℕ, replicaTheta (Pm x) (fun l => a x l 0)
        (fun l w => w ⟨x, l⟩) (fun l => (nthLargestAtom (m l) (poissonCountingMeasure
          (fun k => (p.1 k).1) (fun k l => (p.1 k).2 l)), p.2 (m l))) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨FT, hFT⟩ : ∃ FT : ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ × ((Σ x, ι x) → ℝ≥0∞))) →
      X → ℝ≥0∞, ∀ p x, FT p x = ∑' m : ι x → ℕ, replicaTheta (Pm x) (fun l => a x l 0)
        (fun l w => w ⟨x, l⟩) (fun l => (nthLargestAtom (m l) (poissonCountingMeasure
          (fun k => (p.1 k).1) (fun k l => (p.1 k).2 l)) * ENNReal.ofReal (Real.exp
            ((t * σ 0) * ((p.2 (m l)).1 - (t * σ 0) * ζ 0 / 2))),
          ((p.2 (m l)).1 - (t * σ 0) * ζ 0, (p.2 (m l)).2))) := ⟨_, fun _ _ => rfl⟩
  have hΘ : ∀ x, Measurable (replicaTheta (Pm x) (fun l => a x l 0)
      (fun l (w : (Σ x, ι x) → ℝ≥0∞) => w ⟨x, l⟩)) := fun x =>
    measurable_replicaTheta _ _ _ (fun l => ha x l 0) fun l => measurable_pi_apply _
  have hFUm : Measurable FU := measurable_pi_iff.2 fun x => by
    have e : (fun p => FU p x) = fun p => ∑' m : ι x → ℕ, replicaTheta (Pm x)
        (fun l => a x l 0) (fun l w => w ⟨x, l⟩) (fun l => (nthLargestAtom (m l)
          (poissonCountingMeasure (fun k => (p.1 k).1) (fun k l => (p.1 k).2 l)), p.2 (m l))) :=
      funext fun p => hFU p x
    rw [e]
    exact Measurable.tsum fun m => (hΘ x).comp (measurable_pi_iff.2 fun l =>
      ((measurable_nthLargestAtom (m l)).comp
        (measurable_poissonCountingMeasure.comp measurable_fst)).prodMk
        ((measurable_pi_apply (m l)).comp measurable_snd))
  have hFTm : Measurable FT := measurable_pi_iff.2 fun x => by
    have e : (fun p => FT p x) = fun p => ∑' m : ι x → ℕ, replicaTheta (Pm x)
        (fun l => a x l 0) (fun l w => w ⟨x, l⟩) (fun l => (nthLargestAtom (m l)
          (poissonCountingMeasure (fun k => (p.1 k).1) (fun k l => (p.1 k).2 l)) *
            ENNReal.ofReal (Real.exp ((t * σ 0) * ((p.2 (m l)).1 - (t * σ 0) * ζ 0 / 2))),
          ((p.2 (m l)).1 - (t * σ 0) * ζ 0, (p.2 (m l)).2))) := funext fun p => hFT p x
    rw [e]
    have hη : ∀ n, Measurable fun p : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ × ((Σ x, ι x) → ℝ≥0∞)) =>
        (p.2 n).1 := fun n => measurable_fst.comp ((measurable_pi_apply n).comp measurable_snd)
    exact Measurable.tsum fun m => (hΘ x).comp (measurable_pi_iff.2 fun l =>
      (((measurable_nthLargestAtom (m l)).comp
        (measurable_poissonCountingMeasure.comp measurable_fst)).mul
        (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
          (((hη (m l)).sub_const _).const_mul _)))).prodMk
        (((hη (m l)).sub_const _).prodMk
          (measurable_snd.comp ((measurable_pi_apply (m l)).comp measurable_snd))))
  -- Bolthausen--Sznitman invariance of the replica sums over the ranked atoms of the root
  have hBS := map_replica_ranked_tilt_eq_fintype hζ0 hζ1 nu₀ rate₀ hmu (σm.map Vm) (t * σ 0) ι
    (fun x => replicaTheta (Pm x) (fun l => a x l 0) (fun l (w : (Σ x, ι x) → ℝ≥0∞) => w ⟨x, l⟩))
    hΘ
  have hFTfun : FT = fun p x => ∑' m : ι x → ℕ, replicaTheta (Pm x) (fun l => a x l 0)
      (fun l (w : (Σ x, ι x) → ℝ≥0∞) => w ⟨x, l⟩) (fun l => (nthLargestAtom (m l)
        (poissonCountingMeasure (fun k => (p.1 k).1) (fun k l => (p.1 k).2 l)) *
          ENNReal.ofReal (Real.exp ((t * σ 0) * ((p.2 (m l)).1 - (t * σ 0) * ζ 0 / 2))),
        ((p.2 (m l)).1 - (t * σ 0) * ζ 0, (p.2 (m l)).2))) := funext fun p => funext (hFT p)
  have hFUfun : FU = fun p x => ∑' m : ι x → ℕ, replicaTheta (Pm x) (fun l => a x l 0)
      (fun l (w : (Σ x, ι x) → ℝ≥0∞) => w ⟨x, l⟩) (fun l => (nthLargestAtom (m l)
        (poissonCountingMeasure (fun k => (p.1 k).1) (fun k l => (p.1 k).2 l)), p.2 (m l))) :=
    funext fun p => funext (hFU p)
  rw [← hFTfun, ← hFUfun] at hBS
  -- the ranked atoms of the root are almost surely distinct
  have hae : ∀ᵐ ω ∂P, Function.Injective fun n => nthLargestAtom n (poissonCountingMeasure
      (fun k => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).1)
      (fun k l => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).2 l)) := by
    have hmap : P.map (fun ω => (D ⟨0, fun i => i.elim0⟩ ω).1) =
        Measure.infinitePi fun k => Po(rate₀ k).prod (Measure.infinitePi fun _ : ℕ => nu₀ k) := by
      change P.map (Prod.fst ∘ D ⟨0, fun i => i.elim0⟩) = _
      rw [← Measure.map_map measurable_fst (hDm _), (hDlaw ⟨0, fun i => i.elim0⟩).map_eq]
      change (𝔡 0).map Prod.fst = _
      rw [h𝔡₀, Measure.map_fst_prod, measure_univ, one_smul]
    exact ae_of_ae_map (measurable_fst.comp (hDm _)).aemeasurable
      (hmap ▸ ae_infinitePi_blocks_atoms_injective hζ0 hζ1 nu₀ rate₀ hmu)
  have hDvec : Measurable fun ω (v : Σ p : ℕ, Fin p → ℕ) => D v ω := measurable_pi_iff.2 hDm
  refine identDistrib_of_hasLaw_map_eq_two hΦW hΦV hFTm hFUm hBS ?_ ?_ ?_ ?_
  · filter_upwards [hae] with ω hω
    funext x
    rw [hFT]
    have := cascadeReplicaSum_succ (r := r) (Pm x) (fun l i => tiltTest (t * σ i) (ζ i) (a x l i))
      (fun v => D v ω) hω (fun n => Wm (fun v => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω))
      (fun l w => w ⟨x, l⟩) fun n l => hWm _ _
    rw [this]
    exact tsum_congr fun m => replicaTheta_tilt (t * σ 0) (ζ 0) _ _ _ _
  · filter_upwards [hae] with ω hω
    funext x
    rw [hFU]
    exact cascadeReplicaSum_succ (r := r) (Pm x) (a x) (fun v => D v ω) hω
      (fun n => Vm (fun v => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω)) (fun l w => w ⟨x, l⟩)
      fun n l => hVm _ _
  · exact (measurable_pi_iff.2 fun x => (measurable_cascadeReplicaSum (r + 1) (Pm x) _
      fun l i => measurable_tiltTest _ _ (ha x l i)).comp hDvec).aemeasurable
  · exact (measurable_pi_iff.2 fun x => (measurable_cascadeReplicaSum (r + 1) (Pm x) _
      fun l i => ha x l i).comp hDvec).aemeasurable

/-- **Gaussian Bolthausen--Sznitman invariance of the replica sums of a Ruelle cascade.**
Let the vertex data of depth `p` have the law of ζ_p-Poisson blocks with i.i.d. standard Gaussian
labels, `0 < ζ_p < 1`. For any family of replica sums, indexed by `x`, with replica sets `ι x`,
prescribed overlap matrices `Pm x` and measurable tests `a x l i` of the label at level `i`, the
joint law is unchanged when each test is replaced by its Gaussian exponential tilt
`y ↦ a(y - tσ_iζ_i) exp (tσ_i (y - tσ_iζ_i/2))`. -/
theorem identDistrib_cascadeReplicaSum_tilt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (r : ℕ) :
    ∀ (ζ σ : ℕ → ℝ) (t : ℝ), (∀ p, 0 < ζ p) → (∀ p, ζ p < 1) →
    ∀ (nu : (p : ℕ) → ℕ → Measure ℝ) [∀ p k, IsProbabilityMeasure (nu p k)]
      (rate : (p : ℕ) → ℕ → ℝ≥0),
    (∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k) →
    ∀ (𝔡 : ℕ → Measure ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ))),
    (∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) →
    ∀ (D : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)), (∀ v, Measurable (D v)) →
    iIndepFun D P → (∀ v, HasLaw (D v) (𝔡 v.1) P) →
    ∀ {X : Type} (ι : X → Type) [∀ x, Fintype (ι x)] [∀ x, LinearOrder (ι x)]
      (Pm : ∀ x, ι x → ι x → ℕ) (a : ∀ x, ι x → ℕ → ℝ → ℝ≥0∞),
    (∀ x l i, Measurable (a x l i)) →
    IdentDistrib
      (fun ω x => cascadeReplicaSum r (Pm x)
        (fun l i => tiltTest (t * σ i) (ζ i) (a x l i)) (fun v => D v ω))
      (fun ω x => cascadeReplicaSum r (Pm x) (a x) (fun v => D v ω)) P P := by
  induction r with
  | zero =>
    intro ζ σ t hζ0 hζ1 nu _ rate hmu 𝔡 h𝔡 D hDm hD hDlaw X ι _ _ Pm a ha
    have hz : ∀ (x : X) (b : ι x → ℕ → ℝ → ℝ≥0∞) (d : (Σ p : ℕ, Fin p → ℕ) →
        (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)), cascadeReplicaSum 0 (Pm x) (b) d =
        cascadeReplicaSum 0 (Pm x) (a x) d := fun x b d => by
      simp [cascadeReplicaSum, replicaSum]
    have e : (fun ω x => cascadeReplicaSum 0 (Pm x)
        (fun l i => tiltTest (t * σ i) (ζ i) (a x l i)) (fun v => D v ω)) =
        fun ω x => cascadeReplicaSum 0 (Pm x) (a x) (fun v => D v ω) :=
      funext fun ω => funext fun x => hz x _ _
    rw [e]
    exact IdentDistrib.refl ((measurable_pi_iff.2 fun x => (measurable_cascadeReplicaSum 0 (Pm x)
      (a x) (ha x)).comp (measurable_pi_iff.2 hDm)).aemeasurable)
  | succ r ih =>
    intro ζ σ t hζ0 hζ1 nu _ rate hmu 𝔡 h𝔡 D hDm hD hDlaw X ι _ _ Pm a ha
    have h𝔡p : ∀ p, IsProbabilityMeasure (𝔡 p) := fun p => by rw [h𝔡 p]; infer_instance
    refine identDistrib_cascadeReplicaSum_tilt_succ r ζ σ t (hζ0 0) (hζ1 0) (nu 0) (rate 0)
      (hmu 0) 𝔡 (h𝔡 0) D hDm hD hDlaw ι Pm a ha ?_
    exact ih (fun p => ζ (p + 1)) (fun p => σ (p + 1)) t (fun p => hζ0 _) (fun p => hζ1 _)
      (fun p k => nu (p + 1) k) (fun p k => rate (p + 1) k) (fun p => hmu (p + 1))
      (fun p => 𝔡 (p + 1)) (fun p => h𝔡 (p + 1))
      (fun v => D ⟨v.1 + 1, Fin.cons 0 v.2⟩) (fun v => hDm _)
      (iIndepFun_cascadeChildData D hD 0) (fun v => hDlaw _) (X := Σ x, ι x)
      (fun x' => {l' // 0 < Pm x'.1 x'.2 l'})
      (fun x' y z => Pm x'.1 y.1 z.1 - 1) (fun x' y i => a x'.1 y.1 (i + 1))
      (fun x' y i => ha _ _ _)

end SpinGlasses
