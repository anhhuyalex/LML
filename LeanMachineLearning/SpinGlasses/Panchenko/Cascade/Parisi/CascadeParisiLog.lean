/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeParisiLaw

/-!
# Theorem 2.9 for the Ruelle probability cascade

From the distributional identity: `E log ∑_α v_α exp X_r(Ω_α) = X_0`, where `v_α` are the normalized
cascade weights. Integrability of `log S_r`, `S_r = ∑_α w_α`, comes from
`S_{r+1} =_d c ∑ uₙ` (Theorem 2.6 applied to the subtree totals).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SpinGlasses

variable {Ξ : Type*} [MeasurableSpace Ξ]

/-- `log ∑ uₙ` is integrable for the ranked atoms of the ζ-Poisson blocks. -/
theorem integrable_log_tsum_ranked {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)] (rate : ℕ → ℝ≥0)
    (B : ℕ → Ω → ℕ × (ℕ → ℝ)) (hBm : ∀ k, Measurable (B k)) (hB : iIndepFun B P)
    (hlaw : ∀ k, HasLaw (B k) (Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)) P)
    (hmu : zetaPoissonMeasure ζ = Measure.sum fun k => (rate k : ℝ≥0∞) • nu k) :
    Integrable (fun ω => Real.log (∑' n, nthLargestAtom n (poissonCountingMeasure
      (fun k => (B k ω).1) (fun k l => (B k ω).2 l))).toReal) P := by
  have h1 := integrable_log_lintegral_of_blocks (P := P) (ζ := ζ)
    (M := fun ω => poissonCountingMeasure (fun k => (B k ω).1) (fun k l => (B k ω).2 l)) nu rate
    hζ0 hζ1 hBm hB hlaw hmu (fun _ => rfl)
  refine h1.congr ?_
  filter_upwards [ae_tsum_rankedRoot_eq_lintegral hζ0 hζ1 nu rate B hBm hB hlaw hmu
    (fun x => x) measurable_id] with ω hω
  rw [hω, setLIntegral_eq_of_support_subset]
  intro y hy
  simpa using hy

/-- The root-level law of the unmarked partition sum: `S_{r+1} =_d c ∑ uₙ` for
`c = (E (S_r)^{ζ₀})^{1/ζ₀}`, where `∑ uₙ` is the total mass of the root's Poisson process. -/
theorem identDistrib_cascadeMarkedSum_succ_root {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (r : ℕ) (ζ : ℕ → ℝ) (hζ0 : ∀ p, 0 < ζ p) (hζ1 : ∀ p, ζ p < 1)
    (hmono : StrictMono ζ) (nu : (p : ℕ) → ℕ → Measure ℝ) [∀ p k, IsProbabilityMeasure (nu p k)]
    (rate : (p : ℕ) → ℕ → ℝ≥0)
    (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
    (ρ : Measure Ξ) [IsProbabilityMeasure ρ] (𝔡 : ℕ → Measure ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)))
    (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => ρ))
    (D : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) (hDm : ∀ v, Measurable (D v))
    (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
    (g : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) → ℝ≥0∞) (hg : Measurable g)
    (hg0 : ∀ᵐ x ∂𝔡 (r + 1), g x ≠ 0) (hgf : ∀ᵐ x ∂𝔡 (r + 1), g x ≠ ∞)
    (hgm : ∫⁻ x, g x ^ ζ r ∂𝔡 (r + 1) < ∞) :
    ∃ c : ℝ, 0 < c ∧ IdentDistrib (fun ω => cascadeMarkedSum (r + 1) (fun _ => (0 : ℝ)) g
      (fun v => D v ω))
      (fun ω => ENNReal.ofReal c * ∑' n, nthLargestAtom n (poissonCountingMeasure
        (fun k => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).1)
        (fun k l => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).2 l))) P P := by
  have h𝔡p : ∀ p, IsProbabilityMeasure (𝔡 p) := fun p => by rw [h𝔡 p]; infer_instance
  obtain ⟨hfin, hpos, hmom⟩ := cascadeSubtree_unmarked_facts r ζ hζ0 hζ1 hmono nu rate hmu ρ 𝔡
    h𝔡 D hDm hD hDlaw g hg hg0 hgf hgm
  obtain ⟨σ, hσ⟩ : ∃ σ : Measure ((Σ p : ℕ, Fin p → ℕ) →
      (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)), σ = Measure.infinitePi fun v : Σ p : ℕ, Fin p → ℕ =>
        𝔡 (v.1 + 1) := ⟨_, rfl⟩
  have : IsProbabilityMeasure σ := by rw [hσ]; infer_instance
  rw [← hσ] at hfin hpos hmom
  have hlawS : ∀ n, HasLaw (fun ω (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω)
      σ P := fun n => hσ ▸ hasLaw_cascadeSubtreeData D hDm hD 𝔡 hDlaw n
  have hSm : ∀ n, Measurable fun ω (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω :=
    fun n => measurable_pi_iff.2 fun v => hDm _
  have hL0m : Measurable fun s : (Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) =>
      cascadeMarkedSum r (fun _ => (0 : ℝ)) g s :=
    measurable_cascadeMarkedSum r measurable_const hg
  have hDlaw' : ∀ v, HasLaw (D v) ((Measure.infinitePi fun k =>
      Po(rate v.1 k).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k)).prod
        (Measure.infinitePi fun _ : ℕ => ρ)) P := by
    intro v
    rw [← h𝔡 v.1]
    exact hDlaw v
  -- the root blocks
  have hBvec : HasLaw (fun ω => (D ⟨0, fun i => i.elim0⟩ ω).1) (Measure.infinitePi fun k =>
      Po(rate 0 k).prod (Measure.infinitePi fun _ : ℕ => nu 0 k)) P := by
    refine ⟨(measurable_fst.comp (hDm _)).aemeasurable, ?_⟩
    rw [show (fun ω => (D ⟨0, fun i => i.elim0⟩ ω).1) = Prod.fst ∘ D ⟨0, fun i => i.elim0⟩
      from rfl, ← Measure.map_map measurable_fst (hDm _), (hDlaw' _).map_eq,
      Measure.map_fst_prod, measure_univ, one_smul]
  obtain ⟨hB, hBlaw⟩ := iIndepFun_hasLaw_of_hasLaw_infinitePi hBvec
  -- the marks: real parts of the subtree sums
  have hXm : Measurable fun y : (Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) =>
      (cascadeMarkedSum r (fun _ => (0 : ℝ)) g y).toReal := hL0m.ennreal_toReal
  have hofX : ∀ᵐ y ∂σ, ENNReal.ofReal (cascadeMarkedSum r (fun _ => (0 : ℝ)) g y).toReal =
      cascadeMarkedSum r (fun _ => (0 : ℝ)) g y := by
    filter_upwards [hfin] with y hy
    rw [ENNReal.ofReal_toReal hy.ne]
  have hXpos : ∀ᵐ y ∂σ, 0 < (cascadeMarkedSum r (fun _ => (0 : ℝ)) g y).toReal := by
    filter_upwards [hfin, hpos] with y h1 h2
    exact ENNReal.toReal_pos h2 h1.ne
  have hmomX : ∫⁻ y, ENNReal.ofReal (cascadeMarkedSum r (fun _ => (0 : ℝ)) g y).toReal ^ ζ 0
      ∂σ = ∫⁻ y, cascadeMarkedSum r (fun _ => (0 : ℝ)) g y ^ ζ 0 ∂σ :=
    lintegral_congr_ae (by filter_upwards [hofX] with y hy; rw [hy])
  have hposX : 0 < ∫⁻ y, ENNReal.ofReal (cascadeMarkedSum r (fun _ => (0 : ℝ)) g y).toReal ^
      ζ 0 ∂σ := by
    rw [hmomX]
    by_contra hcon
    have h0 : ∫⁻ y, cascadeMarkedSum r (fun _ => (0 : ℝ)) g y ^ ζ 0 ∂σ = 0 :=
      le_antisymm (not_lt.1 hcon) bot_le
    obtain ⟨y, h1, h2⟩ := (((lintegral_eq_zero_iff (hL0m.pow_const (ζ 0))).1 h0).and
      hpos).exists
    exact h2 ((ENNReal.rpow_eq_zero_iff_of_pos (hζ0 0)).1 h1)
  have hY : iIndepFun (fun n ω (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω) P :=
    iIndepFun_cascadeSubtreeData D hDm hD
  have hBY : IndepFun (fun ω k => (D ⟨0, fun i => i.elim0⟩ ω).1 k)
      (fun ω n (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω) P :=
    (indepFun_cascadeRoot_subtreeData D hDm hD).comp
      (φ := fun x : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) => x.1)
      (ψ := fun s : ℕ → (Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) => s)
      measurable_fst measurable_id
  have hid := identDistrib_ranked_marked_sum (hζ0 0) (hζ1 0) (nu 0) (rate 0)
    (fun k ω => (D ⟨0, fun i => i.elim0⟩ ω).1 k)
    (fun k => (measurable_pi_apply k).comp (measurable_fst.comp (hDm _))) hB hBlaw (hmu 0) σ
    (fun n ω (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω) hSm hY hlawS hBY hXm
    hXpos hposX (hmomX ▸ hmom)
  refine ⟨(∫⁻ t, ENNReal.ofReal (cascadeMarkedSum r (fun _ => (0 : ℝ)) g t).toReal ^ ζ 0
    ∂σ).toReal ^ (ζ 0)⁻¹, Real.rpow_pos_of_pos (ENNReal.toReal_pos hposX.ne'
      (hmomX ▸ hmom).ne) _, ?_⟩
  have hofXP : ∀ᵐ ω ∂P, ∀ n, ENNReal.ofReal (cascadeMarkedSum r (fun _ => (0 : ℝ)) g
      (fun v => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω)).toReal =
      cascadeMarkedSum r (fun _ => (0 : ℝ)) g (fun v => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω) :=
    ae_all_iff.2 fun n => ae_of_ae_map (hSm n).aemeasurable
      (by rw [(hlawS n).map_eq]; exact hofX)
  have hDvec : Measurable fun ω (v : Σ p : ℕ, Fin p → ℕ) => D v ω := measurable_pi_iff.2 hDm
  have hSae := (measurable_cascadeMarkedSum (r + 1) (X := fun _ => (0 : ℝ))
    measurable_const hg).comp hDvec
  have hae : (fun ω => cascadeMarkedSum (r + 1) (fun _ => (0 : ℝ)) g (fun v => D v ω)) =ᵐ[P]
      fun ω => ∑' n, nthLargestAtom n (poissonCountingMeasure
        (fun k => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).1)
        (fun k l => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).2 l)) *
        ENNReal.ofReal (cascadeMarkedSum r (fun _ => (0 : ℝ)) g
          (fun v => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω)).toReal := by
    filter_upwards [hofXP] with ω hω
    rw [cascadeMarkedSum_succ]
    simp only [hω]
  exact (IdentDistrib.of_ae_eq hSae.aemeasurable hae).trans hid

/-- Integrability of the logarithm and almost sure positivity and finiteness of the unmarked
partition sum at depth `r + 1`. -/
theorem cascadeMarkedSum_succ_log_facts {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (r : ℕ) (ζ : ℕ → ℝ) (hζ0 : ∀ p, 0 < ζ p) (hζ1 : ∀ p, ζ p < 1)
    (hmono : StrictMono ζ) (nu : (p : ℕ) → ℕ → Measure ℝ) [∀ p k, IsProbabilityMeasure (nu p k)]
    (rate : (p : ℕ) → ℕ → ℝ≥0)
    (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
    (ρ : Measure Ξ) [IsProbabilityMeasure ρ] (𝔡 : ℕ → Measure ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)))
    (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => ρ))
    (D : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) (hDm : ∀ v, Measurable (D v))
    (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
    (g : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) → ℝ≥0∞) (hg : Measurable g)
    (hg0 : ∀ᵐ x ∂𝔡 (r + 1), g x ≠ 0) (hgf : ∀ᵐ x ∂𝔡 (r + 1), g x ≠ ∞)
    (hgm : ∫⁻ x, g x ^ ζ r ∂𝔡 (r + 1) < ∞) :
    Integrable (fun ω => Real.log (cascadeMarkedSum (r + 1) (fun _ => (0 : ℝ)) g
      (fun v => D v ω)).toReal) P ∧
    (∀ᵐ ω ∂P, 0 < cascadeMarkedSum (r + 1) (fun _ => (0 : ℝ)) g (fun v => D v ω)) ∧
    (∀ᵐ ω ∂P, cascadeMarkedSum (r + 1) (fun _ => (0 : ℝ)) g (fun v => D v ω) < ∞) := by
  obtain ⟨c, hc, hid⟩ := identDistrib_cascadeMarkedSum_succ_root r ζ hζ0 hζ1 hmono nu rate hmu ρ
    𝔡 h𝔡 D hDm hD hDlaw g hg hg0 hgf hgm
  have h𝔡p : ∀ p, IsProbabilityMeasure (𝔡 p) := fun p => by rw [h𝔡 p]; infer_instance
  have hDlaw' : ∀ v, HasLaw (D v) ((Measure.infinitePi fun k =>
      Po(rate v.1 k).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k)).prod
        (Measure.infinitePi fun _ : ℕ => ρ)) P := by
    intro v
    rw [← h𝔡 v.1]
    exact hDlaw v
  have hBvec : HasLaw (fun ω => (D ⟨0, fun i => i.elim0⟩ ω).1) (Measure.infinitePi fun k =>
      Po(rate 0 k).prod (Measure.infinitePi fun _ : ℕ => nu 0 k)) P := by
    refine ⟨(measurable_fst.comp (hDm _)).aemeasurable, ?_⟩
    rw [show (fun ω => (D ⟨0, fun i => i.elim0⟩ ω).1) = Prod.fst ∘ D ⟨0, fun i => i.elim0⟩
      from rfl, ← Measure.map_map measurable_fst (hDm _), (hDlaw' _).map_eq,
      Measure.map_fst_prod, measure_univ, one_smul]
  obtain ⟨hB, hBlaw⟩ := iIndepFun_hasLaw_of_hasLaw_infinitePi hBvec
  have hBm : ∀ k, Measurable fun ω => (D ⟨0, fun i => i.elim0⟩ ω).1 k := fun k =>
    (measurable_pi_apply k).comp (measurable_fst.comp (hDm _))
  have hlogU := integrable_log_tsum_ranked (hζ0 0) (hζ1 0) (nu 0) (rate 0)
    (fun k ω => (D ⟨0, fun i => i.elim0⟩ ω).1 k) hBm hB hBlaw (hmu 0)
  have hUpos : ∀ᵐ ω ∂P, 0 < ∑' n, nthLargestAtom n (poissonCountingMeasure
      (fun k => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).1)
      (fun k l => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).2 l)) ∧ ∑' n, nthLargestAtom n
      (poissonCountingMeasure (fun k => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).1)
      (fun k l => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).2 l)) < ∞ := by
    have h := ae_poissonDirichletWeight (P := P) (ζ := ζ 0) (nu 0) (rate 0) (hζ0 0) (hζ1 0) hBm
      hB hBlaw (hmu 0) (B := fun k ω => (D ⟨0, fun i => i.elim0⟩ ω).1 k)
      (M := fun ω => poissonCountingMeasure (fun k => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).1)
        (fun k l => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).2 l)) fun _ => rfl
    filter_upwards [h] with ω hω
    exact ⟨lt_of_lt_of_le (hω.1 0) (ENNReal.le_tsum (f := fun n => nthLargestAtom n
      (poissonCountingMeasure (fun k => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).1)
        (fun k l => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).2 l))) 0), hω.2.1⟩
  have hlogm : Measurable fun x : ℝ≥0∞ => Real.log x.toReal :=
    Real.measurable_log.comp ENNReal.measurable_toReal
  have hlogC : Integrable (fun ω => Real.log (ENNReal.ofReal c * ∑' n, nthLargestAtom n
      (poissonCountingMeasure (fun k => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).1)
        (fun k l => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).2 l))).toReal) P := by
    refine ((integrable_const (Real.log c)).add hlogU).congr ?_
    filter_upwards [hUpos] with ω hω
    simp only [Pi.add_apply]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le, Real.log_mul hc.ne']
    exact (ENNReal.toReal_pos hω.1.ne' hω.2.ne).ne'
  have hint := (hid.comp hlogm).integrable_iff.2 hlogC
  have hCpos : ∀ᵐ ω ∂P, 0 < ENNReal.ofReal c * ∑' n, nthLargestAtom n (poissonCountingMeasure
      (fun k => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).1)
      (fun k l => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).2 l)) := by
    filter_upwards [hUpos] with ω hω
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 hc).ne' hω.1.ne'
  have hCfin : ∀ᵐ ω ∂P, ENNReal.ofReal c * ∑' n, nthLargestAtom n (poissonCountingMeasure
      (fun k => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).1)
      (fun k l => ((D ⟨0, fun i => i.elim0⟩ ω).1 k).2 l)) < ∞ := by
    filter_upwards [hUpos] with ω hω
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hω.2
  refine ⟨hint, ?_, ?_⟩
  · exact hid.symm.ae_snd (p := fun x => 0 < x) (measurableSet_lt measurable_const measurable_id)
      hCpos
  · exact hid.symm.ae_snd (p := fun x => x < ∞) (measurableSet_lt measurable_id measurable_const)
      hCfin

/-- **Theorem 2.9 (Panchenko) for the Ruelle probability cascade.** Let `X_r` be a measurable
function of the labels along a path, and let `X_l` for `l < r` satisfy the Parisi recursion
`E exp (ζ_l X_{l+1}) = exp (ζ_l X_l)`. Then
`X₀ = E log ∑_α v_α exp X_r(Ω_α)`, where `v_α = w_α / ∑_β w_β` are the normalized cascade weights
(the ratio is written as a quotient of the two partition sums). Depth `r + 1 ≥ 1`. -/
theorem integral_log_cascade_ratio_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (r : ℕ) (ζ : ℕ → ℝ) (hζ0 : ∀ p, 0 < ζ p) (hζ1 : ∀ p, ζ p < 1)
    (hmono : StrictMono ζ) (nu : (p : ℕ) → ℕ → Measure ℝ) [∀ p k, IsProbabilityMeasure (nu p k)]
    (rate : (p : ℕ) → ℕ → ℝ≥0)
    (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
    (ρ : Measure Ξ) [IsProbabilityMeasure ρ] (𝔡 : ℕ → Measure ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)))
    (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => ρ))
    (D : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) (hDm : ∀ v, Measurable (D v))
    (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
    (Xf : (l : ℕ) → (Fin l → Ξ) → ℝ) (hXm : ∀ l, Measurable (Xf l))
    (hXint : ∀ l, l < r + 1 → ∀ θ : Fin l → Ξ,
      Integrable (fun ξ => Real.exp (ζ l * Xf (l + 1) (Fin.snoc θ ξ))) ρ)
    (hXrec : ∀ l, l < r + 1 → ∀ θ : Fin l → Ξ,
      ∫ ξ, Real.exp (ζ l * Xf (l + 1) (Fin.snoc θ ξ)) ∂ρ = Real.exp (ζ l * Xf l θ)) :
    ∫ ω, Real.log ((cascadeMarkedSum (r + 1) (Xf (r + 1)) (fun _ => 1) (fun v => D v ω) /
      cascadeMarkedSum (r + 1) (fun _ => (0 : ℝ)) (fun _ => 1) (fun v => D v ω)).toReal) ∂P =
      Xf 0 fun i => i.elim0 := by
  have h𝔡p : ∀ p, IsProbabilityMeasure (𝔡 p) := fun p => by rw [h𝔡 p]; infer_instance
  have hg0 : ∀ᵐ x ∂𝔡 (r + 1), (fun _ : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) => (1 : ℝ≥0∞)) x ≠ 0 :=
    Filter.Eventually.of_forall fun _ => one_ne_zero
  have hgf : ∀ᵐ x ∂𝔡 (r + 1), (fun _ : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) => (1 : ℝ≥0∞)) x ≠ ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.one_ne_top
  have hgm : ∫⁻ x, (fun _ : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) => (1 : ℝ≥0∞)) x ^ ζ r ∂𝔡 (r + 1) < ∞ := by
    simp
  have hdistr := identDistrib_cascadeMarkedSum_parisi (Ξ := Ξ) (P := P) (r + 1) ζ hζ0 hζ1 hmono
    nu rate hmu ρ 𝔡 h𝔡 D hDm hD hDlaw (fun _ => 1) measurable_const hg0 hgf
    (fun k hk => by have : k = r := by omega
                    subst this; exact hgm) Xf hXm hXint hXrec
  obtain ⟨hlogS, hSpos, hSfin⟩ := cascadeMarkedSum_succ_log_facts r ζ hζ0 hζ1 hmono nu rate hmu ρ
    𝔡 h𝔡 D hDm hD hDlaw (fun _ => 1) measurable_const hg0 hgf hgm
  have hlogm : Measurable fun x : ℝ≥0∞ => Real.log x.toReal :=
    Real.measurable_log.comp ENNReal.measurable_toReal
  set X₀ := Xf 0 fun i => i.elim0 with hX₀
  -- the logarithm of the scaled sum
  have hlogY : Integrable (fun ω => Real.log (ENNReal.ofReal (Real.exp X₀) *
      cascadeMarkedSum (r + 1) (fun _ => (0 : ℝ)) (fun _ => 1) (fun v => D v ω)).toReal) P := by
    refine ((integrable_const X₀).add hlogS).congr ?_
    filter_upwards [hSpos, hSfin] with ω h1 h2
    simp only [Pi.add_apply]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      Real.log_mul (Real.exp_pos _).ne' (ENNReal.toReal_pos h1.ne' h2.ne).ne', Real.log_exp]
  have hint := (hdistr.comp hlogm).integrable_iff.2 hlogY
  have hSXpos : ∀ᵐ ω ∂P, 0 < cascadeMarkedSum (r + 1) (Xf (r + 1)) (fun _ => 1)
      (fun v => D v ω) := by
    refine hdistr.symm.ae_snd (p := fun x => 0 < x) (measurableSet_lt measurable_const
      measurable_id) ?_
    filter_upwards [hSpos] with ω h1
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' h1.ne'
  have hSXfin : ∀ᵐ ω ∂P, cascadeMarkedSum (r + 1) (Xf (r + 1)) (fun _ => 1)
      (fun v => D v ω) < ∞ := by
    refine hdistr.symm.ae_snd (p := fun x => x < ∞) (measurableSet_lt measurable_id
      measurable_const) ?_
    filter_upwards [hSfin] with ω h1
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h1
  have hint_eq := (hdistr.comp hlogm).integral_eq
  have hintY : ∫ ω, Real.log (ENNReal.ofReal (Real.exp X₀) *
      cascadeMarkedSum (r + 1) (fun _ => (0 : ℝ)) (fun _ => 1) (fun v => D v ω)).toReal ∂P =
      X₀ + ∫ ω, Real.log (cascadeMarkedSum (r + 1) (fun _ => (0 : ℝ)) (fun _ => 1)
        (fun v => D v ω)).toReal ∂P := by
    have hae : (fun ω => Real.log (ENNReal.ofReal (Real.exp X₀) *
        cascadeMarkedSum (r + 1) (fun _ => (0 : ℝ)) (fun _ => 1) (fun v => D v ω)).toReal) =ᵐ[P]
        fun ω => X₀ + Real.log (cascadeMarkedSum (r + 1) (fun _ => (0 : ℝ)) (fun _ => 1)
          (fun v => D v ω)).toReal := by
      filter_upwards [hSpos, hSfin] with ω h1 h2
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
        Real.log_mul (Real.exp_pos _).ne' (ENNReal.toReal_pos h1.ne' h2.ne).ne', Real.log_exp]
    rw [integral_congr_ae hae, integral_add (integrable_const _) hlogS, integral_const]
    simp
  have hae : (fun ω => Real.log ((cascadeMarkedSum (r + 1) (Xf (r + 1)) (fun _ => 1)
      (fun v => D v ω) / cascadeMarkedSum (r + 1) (fun _ => (0 : ℝ)) (fun _ => 1)
        (fun v => D v ω)).toReal)) =ᵐ[P] fun ω =>
      Real.log (cascadeMarkedSum (r + 1) (Xf (r + 1)) (fun _ => 1) (fun v => D v ω)).toReal -
      Real.log (cascadeMarkedSum (r + 1) (fun _ => (0 : ℝ)) (fun _ => 1)
        (fun v => D v ω)).toReal := by
    filter_upwards [hSpos, hSfin, hSXpos, hSXfin] with ω h1 h2 h3 h4
    rw [ENNReal.toReal_div, Real.log_div (ENNReal.toReal_pos h3.ne' h4.ne).ne'
      (ENNReal.toReal_pos h1.ne' h2.ne).ne']
  have hint' : Integrable (fun ω => Real.log (cascadeMarkedSum (r + 1) (Xf (r + 1))
      (fun _ => 1) (fun v => D v ω)).toReal) P := hint
  have hint_eq' : ∫ ω, Real.log (cascadeMarkedSum (r + 1) (Xf (r + 1)) (fun _ => 1)
      (fun v => D v ω)).toReal ∂P = ∫ ω, Real.log (ENNReal.ofReal (Real.exp X₀) *
      cascadeMarkedSum (r + 1) (fun _ => (0 : ℝ)) (fun _ => 1) (fun v => D v ω)).toReal ∂P :=
    hint_eq
  rw [integral_congr_ae hae, integral_sub hint' hlogS, hint_eq', hintY]
  ring

end SpinGlasses
