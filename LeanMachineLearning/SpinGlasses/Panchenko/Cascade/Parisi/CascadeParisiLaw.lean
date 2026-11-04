/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeParisiMoment

/-!
# The law of the Parisi partition sum

Theorem 2.9, in distributional form: for the Ruelle cascade with exponents `ζ` and labels
`ω_α ~ ρ`, and a function `X_r` of the labels along a path, the partition sum
`∑_α w_α g_α exp (X_r (Ω_α))` has the same law as `exp X₀ ∑_α w_α g_α`, where
`X_l = ζ_l⁻¹ log E exp (ζ_l X_{l+1})` is the Parisi recursion. The proof peels the first level and
uses the root step `map_root_sum_parisi`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SpinGlasses

variable {Ξ : Type*} [MeasurableSpace Ξ]

/-- A finite `a`-th moment, `a > 0`, forces almost sure finiteness. -/
theorem ae_lt_top_of_lintegral_rpow_lt_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {S : Ω → ℝ≥0∞} (hS : Measurable S) {a : ℝ} (ha : 0 < a)
    (h : ∫⁻ ω, S ω ^ a ∂P < ∞) : ∀ᵐ ω ∂P, S ω < ∞ := by
  filter_upwards [ae_lt_top (hS.pow_const a) h.ne] with ω hω
  exact (ENNReal.rpow_lt_top_iff_of_pos ha).1 hω

/-- Prepending a fixed element is measurable. -/
theorem measurable_fin_cons_right {l : ℕ} (θ : Ξ) :
    Measurable fun θ' : Fin l → Ξ => (Fin.cons θ θ' : Fin (l + 1) → Ξ) := by
  refine measurable_pi_iff.2 fun i => ?_
  cases i using Fin.cases with
  | zero => simp
  | succ j => simpa using measurable_pi_apply j

/-- Prepending is jointly measurable. -/
theorem measurable_fin_cons_pair {l : ℕ} :
    Measurable fun p : Ξ × (Fin l → Ξ) => (Fin.cons p.1 p.2 : Fin (l + 1) → Ξ) := by
  refine measurable_pi_iff.2 fun i => ?_
  cases i using Fin.cases with
  | zero => simp only [Fin.cons_zero]; exact measurable_fst
  | succ j => simp only [Fin.cons_succ]; exact (measurable_pi_apply j).comp measurable_snd

/-- The root step applied to the vertex data model. -/
theorem identDistrib_cascadeMarkedSum_of_rootStep {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {r : ℕ} {ζ₀ : ℝ} (hζ0 : 0 < ζ₀) (hζ1 : ζ₀ < 1)
    (nu₀ : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu₀ k)] (rate₀ : ℕ → ℝ≥0)
    (hmu₀ : zetaPoissonMeasure ζ₀ = Measure.sum fun k => (rate₀ k : ℝ≥0∞) • nu₀ k)
    (ρ : Measure Ξ) [IsProbabilityMeasure ρ]
    (σ : Measure ((Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ))) [IsProbabilityMeasure σ]
    (D : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) (hDm : ∀ v, Measurable (D v))
    (hjoint : HasLaw (fun ω => (D ⟨0, fun i => i.elim0⟩ ω,
        fun n (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω))
      (((Measure.infinitePi fun k => Po(rate₀ k).prod (Measure.infinitePi fun _ : ℕ => nu₀ k)).prod
        (Measure.infinitePi fun _ : ℕ => ρ)).prod (Measure.infinitePi fun _ : ℕ => σ)) P)
    (g : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) → ℝ≥0∞) (hg : Measurable g)
    (X : (Fin (r + 1) → Ξ) → ℝ) (hX : Measurable X)
    (V : ((Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) → ℝ) (hVm : Measurable V)
    (h : Ξ → ℝ) (hhm : Measurable h) (h₀ : ℝ)
    (hΦlaw : ∀ θ, σ.map (fun s => cascadeMarkedSum r (fun θ' => X (Fin.cons θ θ')) g s) =
      σ.map (fun s => ENNReal.ofReal (Real.exp (h θ) * V s)))
    (hVpos : ∀ᵐ s ∂σ, 0 < V s) (hVp : 0 < ∫⁻ s, ENNReal.ofReal (V s) ^ ζ₀ ∂σ)
    (hVf : ∫⁻ s, ENNReal.ofReal (V s) ^ ζ₀ ∂σ < ∞)
    (hint : Integrable (fun θ => Real.exp (ζ₀ * h θ)) ρ)
    (hh₀ : ∫ θ, Real.exp (ζ₀ * h θ) ∂ρ = Real.exp (ζ₀ * h₀))
    (hofV : ∀ᵐ ω ∂P, ∀ n, ENNReal.ofReal (V fun v => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω) =
      cascadeMarkedSum r (fun _ => (0 : ℝ)) g fun v => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω) :
    IdentDistrib (fun ω => cascadeMarkedSum (r + 1) X g (fun v => D v ω))
      (fun ω => ENNReal.ofReal (Real.exp h₀) *
        cascadeMarkedSum (r + 1) (fun _ => (0 : ℝ)) g (fun v => D v ω)) P P := by
  have hΦ : Measurable (Function.uncurry fun (θ : Ξ) (s : (Σ p : ℕ, Fin p → ℕ) →
      (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) => cascadeMarkedSum r (fun θ' => X (Fin.cons θ θ')) g s) :=
    measurable_cascadeMarkedSum_param (α := Ξ) r (X := fun θ θ' => X (Fin.cons θ θ'))
      (hX.comp measurable_fin_cons_pair) hg
  have hRS := map_root_sum_parisi hζ0 hζ1 nu₀ rate₀ hmu₀ ρ σ
    (fun θ s => cascadeMarkedSum r (fun θ' => X (Fin.cons θ θ')) g s) hΦ hVm hhm h₀ hΦlaw hVpos
    hVp hVf hint hh₀
  have hFL := measurable_rootMarkedSum _ hΦ
  have hΦ' : Measurable (Function.uncurry fun (_ : Ξ) (s : (Σ p : ℕ, Fin p → ℕ) →
      (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) => ENNReal.ofReal (V s)) :=
    ENNReal.measurable_ofReal.comp (hVm.comp measurable_snd)
  have hFR := (measurable_rootMarkedSum _ hΦ').const_mul (ENNReal.ofReal (Real.exp h₀))
  have hSm : Measurable fun ω (n : ℕ) (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω :=
    measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun v => hDm _
  have hDvec : Measurable fun ω (v : Σ p : ℕ, Fin p → ℕ) => D v ω := measurable_pi_iff.2 hDm
  refine identDistrib_of_hasLaw_map_eq hjoint hFL hFR hRS (fun ω => cascadeMarkedSum_succ r X g _)
    ?_ ((measurable_cascadeMarkedSum (r + 1) hX hg |>.comp hDvec).aemeasurable)
    (((measurable_cascadeMarkedSum (r + 1) measurable_const hg |>.comp hDvec).const_mul _
      ).aemeasurable)
  filter_upwards [hofV] with ω hω
  rw [cascadeMarkedSum_succ]
  simp only [hω]

/-- Finiteness, positivity and the `ζ₀`-moment of the unmarked subtree sum, in the vertex data
model at level `r + 1`. -/
theorem cascadeSubtree_unmarked_facts {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
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
    (∀ᵐ s ∂(Measure.infinitePi fun v : Σ p : ℕ, Fin p → ℕ => 𝔡 (v.1 + 1)),
      cascadeMarkedSum r (fun _ => (0 : ℝ)) g s < ∞) ∧
    (∀ᵐ s ∂(Measure.infinitePi fun v : Σ p : ℕ, Fin p → ℕ => 𝔡 (v.1 + 1)),
      cascadeMarkedSum r (fun _ => (0 : ℝ)) g s ≠ 0) ∧
    (∫⁻ s, cascadeMarkedSum r (fun _ => (0 : ℝ)) g s ^ ζ 0
      ∂(Measure.infinitePi fun v : Σ p : ℕ, Fin p → ℕ => 𝔡 (v.1 + 1)) < ∞) := by
  have h𝔡p : ∀ p, IsProbabilityMeasure (𝔡 p) := fun p => by rw [h𝔡 p]; infer_instance
  have hDlaw' : ∀ v, HasLaw (D v) ((Measure.infinitePi fun k =>
      Po(rate v.1 k).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k)).prod
        (Measure.infinitePi fun _ : ℕ => ρ)) P := by
    intro v
    rw [← h𝔡 v.1]
    exact hDlaw v
  have hlawS := hasLaw_cascadeSubtreeData D hDm hD 𝔡 hDlaw 0
  have hSm : Measurable fun ω (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons 0 v.2⟩ ω :=
    measurable_pi_iff.2 fun v => hDm _
  have hL0m := measurable_cascadeMarkedSum r (X := fun _ => (0 : ℝ)) measurable_const hg
  have hQ := lintegral_cascadeMarkedSum_rpow_lt_top (P := P) r (fun p => ζ (p + 1))
    (fun p => hζ0 _) (fun p => hζ1 _) (fun p q h => hmono (Nat.succ_lt_succ h))
    (fun p k => nu (p + 1) k) (fun p k => rate (p + 1) k) (fun p => hmu (p + 1)) ρ
    (fun p => 𝔡 (p + 1)) (fun p => h𝔡 (p + 1)) (fun v => D ⟨v.1 + 1, Fin.cons 0 v.2⟩)
    (fun v => hDm _) (iIndepFun_cascadeChildData D hD 0) (fun v => hDlaw _) g hg hg0 hgf
    (ζ 0) (ζ r) (hζ0 0) (hmono Nat.zero_lt_one) (fun hr => by rw [hr])
    (fun k hk => by rw [hk]) hgm
  have hmomσ : ∫⁻ s, cascadeMarkedSum r (fun _ => (0 : ℝ)) g s ^ ζ 0
      ∂(Measure.infinitePi fun v : Σ p : ℕ, Fin p → ℕ => 𝔡 (v.1 + 1)) < ∞ := by
    rw [← hlawS.lintegral_comp (f := fun s => cascadeMarkedSum r (fun _ => (0 : ℝ)) g s ^ ζ 0)
      ((hL0m.pow_const (ζ 0)).aemeasurable)]
    exact hQ
  refine ⟨ae_lt_top_of_lintegral_rpow_lt_top hL0m (hζ0 0) hmomσ, ?_, hmomσ⟩
  have hatoms := ae_cascadeData_atoms_pos_finite ζ hζ0 hζ1 nu rate hmu ρ D hDm hDlaw'
  have hgpos : ∀ᵐ ω ∂P, ∀ γ : Fin (r + 1) → ℕ,
      g (D ⟨r + 1, γ⟩ ω) ≠ 0 ∧ g (D ⟨r + 1, γ⟩ ω) ≠ ∞ :=
    ae_all_iff.2 fun γ => ae_of_ae_map (hDm _).aemeasurable
      (by rw [(hDlaw ⟨r + 1, γ⟩).map_eq]; exact hg0.and hgf)
  have hposP : ∀ᵐ ω ∂P, cascadeMarkedSum r (fun _ => (0 : ℝ)) g
      (fun v => D ⟨v.1 + 1, Fin.cons 0 v.2⟩ ω) ≠ 0 := by
    filter_upwards [hatoms, hgpos] with ω h1 h2
    exact cascadeMarkedSum_ne_zero r (fun _ => (0 : ℝ)) g
      (fun v => D ⟨v.1 + 1, Fin.cons 0 v.2⟩ ω) (fun p γ m => (h1 ⟨p + 1, Fin.cons 0 γ⟩ m).1)
      (fun β => (h2 (Fin.cons 0 β)).1)
  have hm : MeasurableSet {s | cascadeMarkedSum r (fun _ => (0 : ℝ)) g s ≠ 0} :=
    (measurableSet_singleton (0 : ℝ≥0∞)).compl.preimage hL0m
  have := (ae_map_iff hlawS.aemeasurable hm).2 hposP
  rwa [hlawS.map_eq] at this

/-- The inductive step of the distributional Parisi identity. -/
theorem identDistrib_cascadeMarkedSum_parisi_succ {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (r : ℕ) (ζ : ℕ → ℝ) (hζ0 : ∀ p, 0 < ζ p)
    (hζ1 : ∀ p, ζ p < 1) (hmono : StrictMono ζ) (nu : (p : ℕ) → ℕ → Measure ℝ)
    [∀ p k, IsProbabilityMeasure (nu p k)] (rate : (p : ℕ) → ℕ → ℝ≥0)
    (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
    (ρ : Measure Ξ) [IsProbabilityMeasure ρ] (𝔡 : ℕ → Measure ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)))
    (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => ρ))
    (D : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) (hDm : ∀ v, Measurable (D v))
    (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
    (g : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) → ℝ≥0∞) (hg : Measurable g)
    (hg0 : ∀ᵐ x ∂𝔡 (r + 1), g x ≠ 0) (hgf : ∀ᵐ x ∂𝔡 (r + 1), g x ≠ ∞)
    (hgm : ∫⁻ x, g x ^ ζ r ∂𝔡 (r + 1) < ∞)
    (Xf : (l : ℕ) → (Fin l → Ξ) → ℝ) (hXm : ∀ l, Measurable (Xf l))
    (hXint : ∀ θ : Fin 0 → Ξ, Integrable (fun ξ => Real.exp (ζ 0 * Xf 1 (Fin.snoc θ ξ))) ρ)
    (hXrec : ∀ θ : Fin 0 → Ξ,
      ∫ ξ, Real.exp (ζ 0 * Xf 1 (Fin.snoc θ ξ)) ∂ρ = Real.exp (ζ 0 * Xf 0 θ))
    (hih : ∀ θ : Ξ, IdentDistrib
      (fun ω => cascadeMarkedSum r (fun θ' => Xf (r + 1) (Fin.cons θ θ')) g
        (fun v => D ⟨v.1 + 1, Fin.cons 0 v.2⟩ ω))
      (fun ω => ENNReal.ofReal (Real.exp (Xf 1 (Fin.cons θ fun i : Fin 0 => i.elim0))) *
        cascadeMarkedSum r (fun _ => (0 : ℝ)) g (fun v => D ⟨v.1 + 1, Fin.cons 0 v.2⟩ ω)) P P) :
    IdentDistrib (fun ω => cascadeMarkedSum (r + 1) (Xf (r + 1)) g (fun v => D v ω))
      (fun ω => ENNReal.ofReal (Real.exp (Xf 0 fun i => i.elim0)) *
        cascadeMarkedSum (r + 1) (fun _ => (0 : ℝ)) g (fun v => D v ω)) P P := by
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
  obtain ⟨V, hV⟩ : ∃ V : ((Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) → ℝ,
      ∀ s, V s = (cascadeMarkedSum r (fun _ => (0 : ℝ)) g s).toReal := ⟨_, fun _ => rfl⟩
  have hVm : Measurable V := by
    have e : V = fun s => (cascadeMarkedSum r (fun _ => (0 : ℝ)) g s).toReal := funext hV
    rw [e]
    exact hL0m.ennreal_toReal
  have hofV : ∀ᵐ s ∂σ, ENNReal.ofReal (V s) = cascadeMarkedSum r (fun _ => (0 : ℝ)) g s := by
    filter_upwards [hfin] with s h
    rw [hV, ENNReal.ofReal_toReal h.ne]
  have hVpos : ∀ᵐ s ∂σ, 0 < V s := by
    filter_upwards [hfin, hpos] with s h1 h2
    rw [hV]
    exact ENNReal.toReal_pos h2 h1.ne
  have hVmom : ∫⁻ s, ENNReal.ofReal (V s) ^ ζ 0 ∂σ =
      ∫⁻ s, cascadeMarkedSum r (fun _ => (0 : ℝ)) g s ^ ζ 0 ∂σ :=
    lintegral_congr_ae (by filter_upwards [hofV] with s h; rw [h])
  have hVf : ∫⁻ s, ENNReal.ofReal (V s) ^ ζ 0 ∂σ < ∞ := hVmom ▸ hmom
  have hVp : 0 < ∫⁻ s, ENNReal.ofReal (V s) ^ ζ 0 ∂σ := by
    rw [hVmom]
    by_contra hcon
    have h0 : ∫⁻ s, cascadeMarkedSum r (fun _ => (0 : ℝ)) g s ^ ζ 0 ∂σ = 0 :=
      le_antisymm (not_lt.1 hcon) bot_le
    obtain ⟨s, h1, h2⟩ := (((lintegral_eq_zero_iff (hL0m.pow_const (ζ 0))).1 h0).and
      hpos).exists
    exact h2 ((ENNReal.rpow_eq_zero_iff_of_pos (hζ0 0)).1 h1)
  have hofVP : ∀ᵐ ω ∂P, ∀ n, ENNReal.ofReal (V fun v => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω) =
      cascadeMarkedSum r (fun _ => (0 : ℝ)) g fun v => D ⟨v.1 + 1, Fin.cons n v.2⟩ ω :=
    ae_all_iff.2 fun n => ae_of_ae_map (hSm n).aemeasurable
      (by rw [(hlawS n).map_eq]; exact hofV)
  -- the first-level label function and the recursion at level `0`
  obtain ⟨h, hh⟩ : ∃ h : Ξ → ℝ, ∀ θ, h θ = Xf 1 (Fin.cons θ fun i : Fin 0 => i.elim0) :=
    ⟨_, fun _ => rfl⟩
  have hhm : Measurable h := by
    have e : h = fun θ => Xf 1 (Fin.cons θ fun i : Fin 0 => i.elim0) := funext hh
    rw [e]
    exact (hXm 1).comp (measurable_fin_cons_pair.comp (measurable_id.prodMk measurable_const))
  have hsc : ∀ ξ : Ξ, (Fin.snoc (fun i : Fin 0 => i.elim0) ξ : Fin 1 → Ξ) =
      Fin.cons ξ fun i : Fin 0 => i.elim0 := fun ξ => by
    funext i
    fin_cases i
    rfl
  have hint : Integrable (fun θ => Real.exp (ζ 0 * h θ)) ρ := by
    have := hXint fun i => i.elim0
    simpa only [hsc, hh] using this
  have hrec : ∫ θ, Real.exp (ζ 0 * h θ) ∂ρ = Real.exp (ζ 0 * Xf 0 fun i => i.elim0) := by
    have := hXrec fun i => i.elim0
    simpa only [hsc, hh] using this
  -- the induction hypothesis in canonical form
  have hΦ : ∀ θ : Ξ, Measurable fun s : (Σ p : ℕ, Fin p → ℕ) →
      (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) =>
      cascadeMarkedSum r (fun θ' => Xf (r + 1) (Fin.cons θ θ')) g s := fun θ =>
    measurable_cascadeMarkedSum r ((hXm (r + 1)).comp (measurable_fin_cons_right θ)) hg
  have hΦlaw : ∀ θ, σ.map (fun s => cascadeMarkedSum r (fun θ' => Xf (r + 1) (Fin.cons θ θ'))
      g s) = σ.map (fun s => ENNReal.ofReal (Real.exp (h θ) * V s)) := by
    intro θ
    have hid := (hih θ).map_eq
    have hψ : Measurable fun s => ENNReal.ofReal (Real.exp (Xf 1 (Fin.cons θ fun i : Fin 0 =>
        i.elim0))) * cascadeMarkedSum r (fun _ => (0 : ℝ)) g s := hL0m.const_mul _
    have e1 : σ.map (fun s => cascadeMarkedSum r (fun θ' => Xf (r + 1) (Fin.cons θ θ')) g s) =
        P.map ((fun s => cascadeMarkedSum r (fun θ' => Xf (r + 1) (Fin.cons θ θ')) g s) ∘
          fun ω (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons 0 v.2⟩ ω) := by
      rw [← (hlawS 0).map_eq]
      exact Measure.map_map (hΦ θ) (hSm 0)
    have e2 : σ.map (fun s => ENNReal.ofReal (Real.exp (Xf 1 (Fin.cons θ fun i : Fin 0 =>
        i.elim0))) * cascadeMarkedSum r (fun _ => (0 : ℝ)) g s) =
        P.map ((fun s => ENNReal.ofReal (Real.exp (Xf 1 (Fin.cons θ fun i : Fin 0 =>
          i.elim0))) * cascadeMarkedSum r (fun _ => (0 : ℝ)) g s) ∘
          fun ω (v : Σ p : ℕ, Fin p → ℕ) => D ⟨v.1 + 1, Fin.cons 0 v.2⟩ ω) := by
      rw [← (hlawS 0).map_eq]
      exact Measure.map_map hψ (hSm 0)
    refine e1.trans (hid.trans (e2.symm.trans ?_))
    refine Measure.map_congr ?_
    filter_upwards [hofV] with s hs
    rw [hh, ENNReal.ofReal_mul (Real.exp_pos _).le, hs]
  have hjoint := hasLaw_cascadeRoot_subtreeData D hDm hD 𝔡 hDlaw
  rw [h𝔡 0, ← hσ] at hjoint
  exact identDistrib_cascadeMarkedSum_of_rootStep (hζ0 0) (hζ1 0) (nu 0) (rate 0) (hmu 0) ρ σ D
    hDm hjoint g hg (Xf (r + 1)) (hXm _) V hVm h hhm (Xf 0 fun i => i.elim0) hΦlaw hVpos hVp hVf
    hint hrec hofVP

/-- **Theorem 2.9 / equation (2.54), in distributional form.** In the vertex data model with
strictly increasing exponents, if `X_l` satisfies the Parisi recursion
`E exp (ζ_l X_{l+1}) = exp (ζ_l X_l)` for `l < r`, then the partition sum
`∑_α w_α g_α exp (X_r (Ω_α))` has the law of `exp X₀ ∑_α w_α g_α`. The leaf mark `g` has a finite
`ζ_{r-1}`-moment when `r ≥ 1`. -/
theorem identDistrib_cascadeMarkedSum_parisi {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (r : ℕ) :
    ∀ (ζ : ℕ → ℝ), (∀ p, 0 < ζ p) → (∀ p, ζ p < 1) → StrictMono ζ →
    ∀ (nu : (p : ℕ) → ℕ → Measure ℝ) [∀ p k, IsProbabilityMeasure (nu p k)]
      (rate : (p : ℕ) → ℕ → ℝ≥0),
    (∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k) →
    ∀ (ρ : Measure Ξ) [IsProbabilityMeasure ρ] (𝔡 : ℕ → Measure ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ))),
    (∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => ρ)) →
    ∀ (D : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)), (∀ v, Measurable (D v)) →
    iIndepFun D P → (∀ v, HasLaw (D v) (𝔡 v.1) P) →
    ∀ (g : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) → ℝ≥0∞), Measurable g →
    (∀ᵐ x ∂𝔡 r, g x ≠ 0) → (∀ᵐ x ∂𝔡 r, g x ≠ ∞) →
    (∀ k, r = k + 1 → ∫⁻ x, g x ^ ζ k ∂𝔡 r < ∞) →
    ∀ (Xf : (l : ℕ) → (Fin l → Ξ) → ℝ), (∀ l, Measurable (Xf l)) →
    (∀ l, l < r → ∀ θ : Fin l → Ξ,
      Integrable (fun ξ => Real.exp (ζ l * Xf (l + 1) (Fin.snoc θ ξ))) ρ) →
    (∀ l, l < r → ∀ θ : Fin l → Ξ,
      ∫ ξ, Real.exp (ζ l * Xf (l + 1) (Fin.snoc θ ξ)) ∂ρ = Real.exp (ζ l * Xf l θ)) →
    IdentDistrib (fun ω => cascadeMarkedSum r (Xf r) g (fun v => D v ω))
      (fun ω => ENNReal.ofReal (Real.exp (Xf 0 fun i => i.elim0)) *
        cascadeMarkedSum r (fun _ => (0 : ℝ)) g (fun v => D v ω)) P P := by
  induction r with
  | zero =>
    intro ζ hζ0 hζ1 hmono nu _ rate hmu ρ _ 𝔡 h𝔡 D hDm hD hDlaw g hg hg0 hgf hgm Xf hXm hXint
      hXrec
    have hS : ∀ (X : (Fin 0 → Ξ) → ℝ) (ω : Ω), cascadeMarkedSum 0 X g (fun v => D v ω) =
        g (D ⟨0, fun i => i.elim0⟩ ω) * ENNReal.ofReal (Real.exp (X fun i => i.elim0)) := by
      intro X ω
      simp only [cascadeMarkedSum, tsum_fintype, cascadeBranchWeight_zero, one_mul]
      refine (Fintype.sum_unique _).trans ?_
      have h2 : ∀ f : Fin 0 → Ξ, f = fun i => i.elim0 := fun f => Subsingleton.elim _ _
      simp only [h2]
      exact congrArg (fun γ : Fin 0 → ℕ => g (D ⟨0, γ⟩ ω) *
        ENNReal.ofReal (Real.exp (X fun i => i.elim0))) (Subsingleton.elim _ _)
    have hm : Measurable fun ω => g (D ⟨0, fun i => i.elim0⟩ ω) := hg.comp (hDm _)
    have e1 : (fun ω => cascadeMarkedSum 0 (Xf 0) g (fun v => D v ω)) =
        fun ω => g (D ⟨0, fun i => i.elim0⟩ ω) * ENNReal.ofReal (Real.exp (Xf 0 fun i => i.elim0))
        := funext fun ω => hS _ ω
    have e2 : (fun ω => ENNReal.ofReal (Real.exp (Xf 0 fun i => i.elim0)) *
        cascadeMarkedSum 0 (fun _ => (0 : ℝ)) g (fun v => D v ω)) =
        fun ω => g (D ⟨0, fun i => i.elim0⟩ ω) * ENNReal.ofReal (Real.exp (Xf 0 fun i => i.elim0))
        := funext fun ω => by rw [hS, Real.exp_zero, ENNReal.ofReal_one, mul_one, mul_comm]
    rw [e1, e2]
    exact IdentDistrib.refl (hm.mul_const _).aemeasurable
  | succ r ih =>
    intro ζ hζ0 hζ1 hmono nu _ rate hmu ρ _ 𝔡 h𝔡 D hDm hD hDlaw g hg hg0 hgf hgm Xf hXm hXint
      hXrec
    refine identDistrib_cascadeMarkedSum_parisi_succ r ζ hζ0 hζ1 hmono nu rate hmu ρ 𝔡 h𝔡 D hDm
      hD hDlaw g hg hg0 hgf (hgm r rfl) Xf hXm (hXint 0 (Nat.succ_pos r))
      (hXrec 0 (Nat.succ_pos r)) fun θ => ?_
    exact ih (fun p => ζ (p + 1)) (fun p => hζ0 _) (fun p => hζ1 _)
      (fun p q h => hmono (Nat.succ_lt_succ h)) (fun p k => nu (p + 1) k)
      (fun p k => rate (p + 1) k) (fun p => hmu (p + 1)) ρ (fun p => 𝔡 (p + 1))
      (fun p => h𝔡 (p + 1)) (fun v => D ⟨v.1 + 1, Fin.cons 0 v.2⟩) (fun v => hDm _)
      (iIndepFun_cascadeChildData D hD 0) (fun v => hDlaw _) g hg hg0 hgf
      (fun k hk => by
        have := hgm r rfl
        have hk' : k + 1 = r := hk.symm
        subst hk'
        exact this)
      (fun l θ' => Xf (l + 1) (Fin.cons θ θ'))
      (fun l => (hXm (l + 1)).comp (measurable_fin_cons_right θ))
      (fun l hl θ' => by
        have h := hXint (l + 1) (Nat.succ_lt_succ hl) (Fin.cons θ θ')
        simpa only [← Fin.cons_snoc_eq_snoc_cons] using h)
      (fun l hl θ' => by
        have h := hXrec (l + 1) (Nat.succ_lt_succ hl) (Fin.cons θ θ')
        simpa only [← Fin.cons_snoc_eq_snoc_cons] using h)

end SpinGlasses
