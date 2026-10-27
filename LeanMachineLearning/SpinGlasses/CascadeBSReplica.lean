/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeBS
public import LeanMachineLearning.SpinGlasses.CascadeRankMarks
public import LeanMachineLearning.SpinGlasses.PoissonDirichletInvariance
public import LeanMachineLearning.SpinGlasses.PoissonDirichletIdentities

/-!
# Replica sums under the Gaussian Bolthausen--Sznitman transformation, with an extra mark

For Poisson blocks of the ζ-Poisson process whose points carry i.i.d. marks `(η, V) ~ N(0,1) ⊗ κ`,
every finite family of replica sums keeps its joint law when each point is replaced by the
transformed point `(x e^{t(η - tζ/2)}, (η - tζ, V))`, both for marks attached to the points and (by
the bridging lemma) for marks attached to the ranks of the ranked atoms.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SpinGlasses

variable {S : Type*} [MeasurableSpace S]

/-- The marked block law: every point `(x, (η, V))` of the `k`-th block has the law `ν k ⊗ m`. -/
theorem hasLaw_markedBlocks (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)]
    (rate : ℕ → ℝ≥0) (κ : Measure S) [IsProbabilityMeasure κ] :
    HasLaw (fun ω : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ × S) => fun k =>
        ((ω.1 k).1, fun l => ((ω.1 k).2 l, ω.2 k l)))
      (Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ =>
        (nu k).prod ((gaussianReal 0 1).prod κ)))
      ((Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          (gaussianReal 0 1).prod κ)) := by
  refine ⟨?_, map_prod_infinitePi_allBlockMarks (fun k => Po(rate k)) nu _⟩
  exact (measurable_pi_iff.2 fun k =>
    ((measurable_fst.comp ((measurable_pi_apply k).comp measurable_fst)).prodMk
      (measurable_pi_iff.2 fun l => (((measurable_pi_apply l).comp (measurable_snd.comp
        ((measurable_pi_apply k).comp measurable_fst))).prodMk
        ((measurable_pi_apply l).comp ((measurable_pi_apply k).comp measurable_snd)))))
      ).aemeasurable

open scoped Classical in
/-- Replica integrals against the restriction to `{x > 0}` of a counting measure with finite
positive shells are sums over tuples of active points, when all first coordinates are positive. -/
theorem lintegral_pi_restrict_pos_eq_tsum (N : ℕ → ℕ) (X : ℕ → ℕ → ℝ × S)
    (hshell : ∀ k : ℕ, poissonCountingMeasure N X (Ioi (1 / ((k : ℝ) + 1)) ×ˢ univ) < ∞)
    (hpos : ∀ k l, l < N k → 0 < (X k l).1) (n : ℕ) {Φ : (Fin n → ℝ × S) → ℝ≥0∞}
    (hΦ : Measurable Φ) :
    (∫⁻ q, Φ q ∂Measure.pi fun _ : Fin n =>
      (poissonCountingMeasure N X).restrict (Ioi 0 ×ˢ univ)) =
      ∑' q : Fin n → {p : ℕ × ℕ // p.2 < N p.1}, Φ (fun i => X (q i).1.1 (q i).1.2) := by
  have _ := sigmaFinite_poissonCountingMeasure_restrict_pos_of_shells N X hshell
  rw [lintegral_pi_poissonCountingMeasure_restrict_eq_tsum N X
    (measurableSet_Ioi.prod MeasurableSet.univ) n hΦ]
  refine tsum_congr fun q => ?_
  have hc : ∀ i, X (q i).1.1 (q i).1.2 ∈ Ioi 0 ×ˢ (univ : Set S) := fun i =>
    ⟨hpos _ _ (q i).2, mem_univ _⟩
  simp only [hc, implies_true, ↓reduceIte]

/-- **Gaussian Bolthausen--Sznitman invariance of the replica sums, for marks attached to points.**
The sum is over `n`-tuples of active points of the blocks. -/
theorem identDistrib_replica_point_tilt {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)] (rate : ℕ → ℝ≥0)
    (hmu : zetaPoissonMeasure ζ = Measure.sum fun k => (rate k : ℝ≥0∞) • nu k)
    (κ : Measure S) [IsProbabilityMeasure κ] (t : ℝ) {ι : Type*} (n : ι → ℕ)
    (Θ : (i : ι) → (Fin (n i) → ℝ≥0∞ × (ℝ × S)) → ℝ≥0∞) (hΘ : ∀ i, Measurable (Θ i)) :
    IdentDistrib
      (fun ω : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ × S) => fun i =>
        ∑' q : Fin (n i) → {q : ℕ × ℕ // q.2 < (ω.1 q.1).1}, Θ i (fun l =>
          (ENNReal.ofReal ((ω.1 (q l).1.1).2 (q l).1.2) *
            ENNReal.ofReal (Real.exp (t * ((ω.2 (q l).1.1 (q l).1.2).1 - t * ζ / 2))),
          ((ω.2 (q l).1.1 (q l).1.2).1 - t * ζ, (ω.2 (q l).1.1 (q l).1.2).2))))
      (fun ω => fun i =>
        ∑' q : Fin (n i) → {q : ℕ × ℕ // q.2 < (ω.1 q.1).1}, Θ i (fun l =>
          (ENNReal.ofReal ((ω.1 (q l).1.1).2 (q l).1.2), ω.2 (q l).1.1 (q l).1.2)))
      ((Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          (gaussianReal 0 1).prod κ))
      ((Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).prod
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
          (gaussianReal 0 1).prod κ)) := by
  set m : Measure (ℝ × S) := (gaussianReal 0 1).prod κ with hm
  set 𝓑 := Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)
    with h𝓑
  set P₀ := 𝓑.prod (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => m) with hP₀
  have hP₀p : IsProbabilityMeasure P₀ := by rw [hP₀]; infer_instance
  -- the marked blocks, their independence and laws
  have hBvec := hasLaw_markedBlocks nu rate κ
  obtain ⟨hBi, hBlaw⟩ := iIndepFun_hasLaw_of_hasLaw_infinitePi hBvec
  have hBm : ∀ k, Measurable fun ω : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ × S) =>
      ((ω.1 k).1, fun l => ((ω.1 k).2 l, ω.2 k l)) := fun k =>
    (measurable_fst.comp ((measurable_pi_apply k).comp measurable_fst)).prodMk
      (measurable_pi_iff.2 fun l => (((measurable_pi_apply l).comp (measurable_snd.comp
        ((measurable_pi_apply k).comp measurable_fst))).prodMk
        ((measurable_pi_apply l).comp ((measurable_pi_apply k).comp measurable_snd))))
  -- the transformed marks
  let Ψ : ℝ × S → ℝ × (ℝ × S) := fun y => (Real.exp (t * (y.1 - t * ζ / 2)), (y.1 - t * ζ, y.2))
  have hΨ : Measurable Ψ := by fun_prop
  let f : ℝ × (ℝ × S) → ℝ × (ℝ × (ℝ × S)) := fun z => (z.1, Ψ z.2)
  have hf : Measurable f := by fun_prop
  have hμ0 : (zetaPoissonMeasure ζ).prod m =
      Measure.sum fun k => (rate k : ℝ≥0∞) • (nu k).prod m := by
    rw [hmu, Measure.prod_sum_left]
    simp only [Measure.prod_smul_left]
  have hμW : (zetaPoissonMeasure ζ).prod (m.map Ψ) =
      Measure.sum fun k => (rate k : ℝ≥0∞) • ((nu k).prod m).map f := by
    rw [← poissonIntensity_map _ rate hf, ← hμ0]
    have h := Measure.map_prod_map (zetaPoissonMeasure ζ) m (f := id) (g := Ψ) measurable_id hΨ
    rw [Measure.map_id] at h
    exact h
  obtain ⟨hBWm, hBWi, hBWlaw⟩ := poissonBlocks_map (ν := fun k => (nu k).prod m) (r := rate)
    (B := fun k (ω : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ × S)) =>
      ((ω.1 k).1, fun l => ((ω.1 k).2 l, ω.2 k l))) hBm hBi hBlaw hf
  have hid := identDistrib_poissonDirichlet_gaussian_marked_transform (P := P₀) (Q := P₀) hζ0 t κ
    (fun k => ((nu k).prod m).map f) rate hBWm hBWi hBWlaw hμW (fun k => (nu k).prod m) rate hBm
    hBi hBlaw hμ0
  -- the transformed counting measure
  let Ft : ℝ × (ℝ × S) → ℝ × (ℝ × S) := fun z =>
    (z.1 * Real.exp (t * (z.2.1 - t * ζ / 2)), (z.2.1 - t * ζ, z.2.2))
  have hFt : Measurable Ft := by fun_prop
  have hid' : IdentDistrib
      (fun ω : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ × S) =>
        (poissonCountingMeasure (fun k => (ω.1 k).1)
          (fun k l => ((ω.1 k).2 l, ω.2 k l))).map Ft)
      (fun ω : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ × S) =>
        poissonCountingMeasure (fun k => (ω.1 k).1) (fun k l => ((ω.1 k).2 l, ω.2 k l)))
      P₀ P₀ := by
    have hG : Measurable fun p : ℝ × (ℝ × (ℝ × S)) => (p.1 * p.2.1, p.2.2) := by fun_prop
    convert hid using 1
    funext ω
    rw [← poissonCountingMeasure_map _ _ hf, Measure.map_map hG hf]
    rfl
  -- local finiteness on the exhausting shells, for both measures
  let C : ℕ → Set (ℝ × (ℝ × S)) := fun k => Set.Ioi (1 / ((k : ℝ) + 1)) ×ˢ Set.univ
  have hC : ∀ k, MeasurableSet (C k) := fun k => measurableSet_Ioi.prod MeasurableSet.univ
  have hY := ae_poissonCountingMeasure_Ioi_inv_succ_prod_univ_lt_top hζ0 m
    (fun k => (nu k).prod m) rate hBm hBi hBlaw hμ0
  have hX := hid'.symm.ae_snd (measurableSet_forall_measure_lt_top hC) hY
  have hΦm : ∀ i, Measurable fun z : Fin (n i) → ℝ × (ℝ × S) =>
      Θ i (fun l => (ENNReal.ofReal (z l).1, (z l).2)) := fun i =>
    (hΘ i).comp (measurable_pi_iff.2 fun l => (ENNReal.measurable_ofReal.comp
      (measurable_fst.comp (measurable_pi_apply l))).prodMk
        (measurable_snd.comp (measurable_pi_apply l)))
  have hrep := hid'.lintegral_pi_restrict hC hX hY n hΦm
  simp only [C, iUnion_Ioi_inv_succ_prod_univ] at hrep
  have hgood := ae_infinitePi_blocks_good hζ0 hζ1 nu rate hmu
  have hgoodω := (Measure.quasiMeasurePreserving_fst (μ := 𝓑)
    (ν := Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => m)).ae hgood
  -- right side: untilted replica integrals are sums over active points
  have eR : (fun ω : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ × S) => fun i =>
        ∑' q : Fin (n i) → {q : ℕ × ℕ // q.2 < (ω.1 q.1).1},
        Θ i (fun l => (ENNReal.ofReal ((ω.1 (q l).1.1).2 (q l).1.2), ω.2 (q l).1.1 (q l).1.2)))
      =ᵐ[P₀] fun ω => fun i =>
        ∫⁻ q, Θ i (fun l => (ENNReal.ofReal (q l).1, (q l).2)) ∂Measure.pi fun _ : Fin (n i) =>
        (poissonCountingMeasure (fun k => (ω.1 k).1)
          (fun k l => ((ω.1 k).2 l, ω.2 k l))).restrict (Ioi 0 ×ˢ univ) := by
    filter_upwards [hY, hgoodω] with ω hY' hω
    funext i
    rw [lintegral_pi_restrict_pos_eq_tsum _ _ (fun k => hY' k)
      (fun k l hl => (hω.2.1 ⟨(k, l), hl⟩)) (n i) (hΦm i)]
  -- left side: tilted replica integrals are sums over active points
  have eL : (fun ω : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ × S) => fun i =>
        ∑' q : Fin (n i) → {q : ℕ × ℕ // q.2 < (ω.1 q.1).1},
        Θ i (fun l => (ENNReal.ofReal ((ω.1 (q l).1.1).2 (q l).1.2) *
            ENNReal.ofReal (Real.exp (t * ((ω.2 (q l).1.1 (q l).1.2).1 - t * ζ / 2))),
          ((ω.2 (q l).1.1 (q l).1.2).1 - t * ζ, (ω.2 (q l).1.1 (q l).1.2).2))))
      =ᵐ[P₀] fun ω => fun i =>
        ∫⁻ q, Θ i (fun l => (ENNReal.ofReal (q l).1, (q l).2)) ∂Measure.pi fun _ : Fin (n i) =>
        ((poissonCountingMeasure (fun k => (ω.1 k).1)
          (fun k l => ((ω.1 k).2 l, ω.2 k l))).map Ft).restrict (Ioi 0 ×ˢ univ) := by
    filter_upwards [hX, hgoodω] with ω hX' hω
    funext i
    rw [poissonCountingMeasure_map _ _ hFt] at hX' ⊢
    rw [lintegral_pi_restrict_pos_eq_tsum _ _ (fun k => hX' k)
      (fun k l hl => mul_pos (hω.2.1 ⟨(k, l), hl⟩) (Real.exp_pos _)) (n i) (hΦm i)]
    refine tsum_congr fun q => ?_
    congr 1
    funext l
    simp only [Ft]
    rw [ENNReal.ofReal_mul (hω.2.1 _).le]
  have hV1 := hrep.aemeasurable_fst
  have hV2 := hrep.aemeasurable_snd
  exact (IdentDistrib.of_ae_eq (hV1.congr eL.symm) eL).trans
    (hrep.trans (IdentDistrib.of_ae_eq (hV2.congr eR.symm) eR).symm)

/-- **Gaussian Bolthausen--Sznitman invariance of the replica sums over ranked atoms.** The ranked
atoms `uₘ` of independent ζ-Poisson blocks carry i.i.d. marks `(η, V) ~ N(0,1) ⊗ κ` indexed by rank.
Replacing every pair by `(u e^{t(η - tζ/2)}, (η - tζ, V))` does not change the joint law of any
finite family of replica sums. -/
theorem map_replica_ranked_tilt_eq {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)] (rate : ℕ → ℝ≥0)
    (hmu : zetaPoissonMeasure ζ = Measure.sum fun k => (rate k : ℝ≥0∞) • nu k)
    (κ : Measure S) [IsProbabilityMeasure κ] (t : ℝ) {ι : Type*} (n : ι → ℕ)
    (Θ : (i : ι) → (Fin (n i) → ℝ≥0∞ × (ℝ × S)) → ℝ≥0∞) (hΘ : ∀ i, Measurable (Θ i)) :
    ((Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).prod
        (Measure.infinitePi fun _ : ℕ => (gaussianReal 0 1).prod κ)).map
      (fun p i => ∑' m : Fin (n i) → ℕ, Θ i (fun l =>
        (nthLargestAtom (m l) (poissonCountingMeasure (fun k => (p.1 k).1)
          (fun k l => (p.1 k).2 l)) * ENNReal.ofReal (Real.exp (t * ((p.2 (m l)).1 - t * ζ / 2))),
        ((p.2 (m l)).1 - t * ζ, (p.2 (m l)).2)))) =
    ((Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).prod
        (Measure.infinitePi fun _ : ℕ => (gaussianReal 0 1).prod κ)).map
      (fun p i => ∑' m : Fin (n i) → ℕ, Θ i (fun l => (nthLargestAtom (m l)
        (poissonCountingMeasure (fun k => (p.1 k).1) (fun k l => (p.1 k).2 l)), p.2 (m l)))) := by
  let Ft : ℝ≥0∞ × (ℝ × S) → ℝ≥0∞ × (ℝ × S) := fun z =>
    (z.1 * ENNReal.ofReal (Real.exp (t * (z.2.1 - t * ζ / 2))), (z.2.1 - t * ζ, z.2.2))
  have hFt : Measurable Ft := by fun_prop
  have hΘ' : ∀ i, Measurable fun z : Fin (n i) → ℝ≥0∞ × (ℝ × S) => Θ i (fun l => Ft (z l)) :=
    fun i => (hΘ i).comp (measurable_pi_iff.2 fun l => hFt.comp (measurable_pi_apply l))
  have h1 := map_prod_replica_active_eq_ranked hζ0 hζ1 nu rate hmu ((gaussianReal 0 1).prod κ) n
    (fun i z => Θ i (fun l => Ft (z l))) hΘ'
  have h2 := map_prod_replica_active_eq_ranked hζ0 hζ1 nu rate hmu ((gaussianReal 0 1).prod κ) n
    Θ hΘ
  have h3 := (identDistrib_replica_point_tilt hζ0 hζ1 nu rate hmu κ t n Θ hΘ).map_eq
  rw [← h2, ← h3, ← h1]


/-- **Gaussian Bolthausen--Sznitman invariance of the replica sums over ranked atoms, for
arbitrary finite sets of replicas.** -/
theorem map_replica_ranked_tilt_eq_fintype {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)] (rate : ℕ → ℝ≥0)
    (hmu : zetaPoissonMeasure ζ = Measure.sum fun k => (rate k : ℝ≥0∞) • nu k)
    (κ : Measure S) [IsProbabilityMeasure κ] (t : ℝ) {ι : Type*} (K : ι → Type)
    [∀ i, Finite (K i)] (Θ : (i : ι) → (K i → ℝ≥0∞ × (ℝ × S)) → ℝ≥0∞)
    (hΘ : ∀ i, Measurable (Θ i)) :
    ((Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).prod
        (Measure.infinitePi fun _ : ℕ => (gaussianReal 0 1).prod κ)).map
      (fun p i => ∑' m : K i → ℕ, Θ i (fun l =>
        (nthLargestAtom (m l) (poissonCountingMeasure (fun k => (p.1 k).1)
          (fun k l => (p.1 k).2 l)) * ENNReal.ofReal (Real.exp (t * ((p.2 (m l)).1 - t * ζ / 2))),
        ((p.2 (m l)).1 - t * ζ, (p.2 (m l)).2)))) =
    ((Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).prod
        (Measure.infinitePi fun _ : ℕ => (gaussianReal 0 1).prod κ)).map
      (fun p i => ∑' m : K i → ℕ, Θ i (fun l => (nthLargestAtom (m l)
        (poissonCountingMeasure (fun k => (p.1 k).1) (fun k l => (p.1 k).2 l)), p.2 (m l)))) := by
  have : ∀ i, Fintype (K i) := fun i => Fintype.ofFinite (K i)
  have h := map_replica_ranked_tilt_eq hζ0 hζ1 nu rate hmu κ t (fun i => Fintype.card (K i))
    (fun i z => Θ i (fun k => z (Fintype.equivFin (K i) k))) fun i =>
      (hΘ i).comp (measurable_pi_iff.2 fun k => measurable_pi_apply _)
  have hsum : ∀ (i : ι) (F : (K i → ℕ) → ℝ≥0∞),
      ∑' m : Fin (Fintype.card (K i)) → ℕ, F (fun k => m (Fintype.equivFin (K i) k)) =
        ∑' m : K i → ℕ, F m := fun i F =>
    (Equiv.arrowCongr (Fintype.equivFin (K i)).symm (Equiv.refl ℕ)).tsum_eq F
  convert h using 3
  · exact funext fun i => (hsum i _).symm
  · exact funext fun i => (hsum i _).symm

end SpinGlasses
