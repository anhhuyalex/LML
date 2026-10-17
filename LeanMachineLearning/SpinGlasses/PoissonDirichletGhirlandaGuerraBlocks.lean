/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletGhirlandaGuerraAlgebra

/-!
# Gaussian integration by parts on the original Poisson block space

The guarded product-law identity transfers to the active random index subtype.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SpinGlasses

/-- Gaussian IBP for the Gibbs series of the original split Poisson blocks.
The fresh replica is indexed by `none : Option (Fin n)`. -/
theorem integral_poissonDirichlet_gaussian_tilt_ibp_blocks
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1) (t : ℝ)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ =>
        (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1))
    (n : ℕ) (r₀ : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ)
    (hf : Measurable f) :
    (∫ ω, ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 *
          Real.exp (t * ((B (σ j).1.1 ω).2 (σ j).1.2).2) /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1 *
            Real.exp (t * ((B a.1.1 ω).2 a.1.2).2)) *
        (f (fun i j => if σ i = σ j then 1 else 0) *
          ((B (σ r₀).1.1 ω).2 (σ r₀).1.2).2) ∂P) =
    ∫ ω, ∑' τ : Option (Fin n) → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
      (∏ j, ((B (τ j).1.1 ω).2 (τ j).1.2).1 *
          Real.exp (t * ((B (τ j).1.1 ω).2 (τ j).1.2).2) /
        ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          ((B a.1.1 ω).2 a.1.2).1 *
            Real.exp (t * ((B a.1.1 ω).2 a.1.2).2)) *
        (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
          (∑ j : Fin n, t * (if τ (some r₀) = τ (some j) then 1 else 0) -
            n * t * (if τ (some r₀) = τ none then 1 else 0))) ∂P := by
  classical
  let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
    fun ω m => ((B m ω).1, fun l => ((B m ω).2 l).1)
  let G : Ω → ℕ → ℕ → ℝ := fun ω m l => ((B m ω).2 l).2
  let ρ : Measure (ℕ → ℕ × (ℕ → ℝ)) := P.map Z
  let μ : Measure (ℕ → ℕ → ℝ) :=
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  let Φ : (Fin n → ℕ × ℕ) → ℝ := fun σ =>
    f (fun i j => if σ i = σ j then 1 else 0)
  let L : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) → ℝ := fun zg =>
    ∑' σ : Fin n → ℕ × ℕ,
      if ∀ j, (σ j).2 < (zg.1 (σ j).1).1 then
        (∏ j, ((zg.1 (σ j).1).2 (σ j).2 *
            Real.exp (t * zg.2 (σ j).1 (σ j).2)) /
          ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
            (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) *
          (Φ σ * zg.2 (σ r₀).1 (σ r₀).2)
      else 0
  let R : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) → ℝ := fun zg =>
    ∑' τ : Option (Fin n) → ℕ × ℕ,
      if ∀ j, (τ j).2 < (zg.1 (τ j).1).1 then
        (∏ j, ((zg.1 (τ j).1).2 (τ j).2 *
            Real.exp (t * zg.2 (τ j).1 (τ j).2)) /
          ∑' p : ℕ × ℕ, if p.2 < (zg.1 p.1).1 then
            (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0) *
          (Φ (fun i => τ (some i)) *
            (∑ j : Fin n, t * (if τ (some r₀) = τ (some j) then 1 else 0) -
              n * t * (if τ (some r₀) = τ none then 1 else 0)))
      else 0
  obtain ⟨M, hM⟩ := exists_bound_index_overlap_observable (α := ℕ × ℕ) f
  have hZm : Measurable Z := measurable_pi_iff.2 fun m =>
    (measurable_fst.comp (hBm m)).prodMk
      (measurable_pi_iff.2 fun l =>
        measurable_fst.comp ((measurable_pi_apply l).comp
          (measurable_snd.comp (hBm m))))
  have hρ : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff hZm.aemeasurable).2 inferInstance
  have henv : ∀ᵐ z ∂ρ,
      (∃ p : ℕ × ℕ, p.2 < (z p.1).1) ∧
      (∀ p : ℕ × ℕ, p.2 < (z p.1).1 → 0 < (z p.1).2 p.2) ∧
      Summable (fun p : ℕ × ℕ =>
        if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0) := by
    have hZ := ae_poissonDirichlet_gaussian_ibp_environment hζ hζ1
      (fun m => (ν m).prod (gaussianReal 0 1)) r hBm hB hlaw hμ
    have hraw : ∀ᵐ z ∂ρ,
        Nonempty {p : ℕ × ℕ // p.2 < (z p.1).1} ∧
        (∀ p : ℕ × ℕ, p.2 < (z p.1).1 → 0 < (z p.1).2 p.2) ∧
        (∑' p : ℕ × ℕ,
          ENNReal.ofReal (if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0)) < ∞ :=
      (ae_map_iff hZm.aemeasurable measurableSet_gaussian_gibbs_environment).2 (by
        filter_upwards [hZ] with ω ⟨hn, hp, hs⟩
        refine ⟨hn, (fun p h => hp ⟨p, h⟩), ?_⟩
        have ht := (summable_subtype_iff_indicator (s :=
          {p : ℕ × ℕ | p.2 < (Z ω p.1).1})
          (f := fun p : ℕ × ℕ => (Z ω p.1).2 p.2)).1 hs
        have ht' : Summable (fun p : ℕ × ℕ =>
            if p.2 < (Z ω p.1).1 then (Z ω p.1).2 p.2 else 0) := by
          convert ht using 1
          funext p
          by_cases h : p.2 < (Z ω p.1).1 <;> simp [Set.indicator, h]
        exact ht'.tsum_ofReal_lt_top)
    filter_upwards [hraw] with z ⟨hn, hp, hs⟩
    refine ⟨hn.elim fun p => ⟨p.1, p.2⟩, hp, ?_⟩
    exact summable_of_tsum_ofReal_lt_top (fun p => by
      split_ifs with h
      · exact (hp p h).le
      · exact le_refl 0) hs
  have hL : Integrable L (ρ.prod μ) := by
    convert integrable_gaussian_gibbs_tilt_mark_guard_prod
      hζ hζ1 t ν r hBm hB hlaw hμ n r₀ f hf using 1
  have hR : Integrable R (ρ.prod μ) := by
    simpa only [R, Fintype.card_fin] using
      (integrable_gaussian_gibbs_tilt_correction_prod t r₀ Φ M hM ρ henv)
  have hIBP : (∫ zg, L zg ∂ρ.prod μ) = ∫ zg, R zg ∂ρ.prod μ := by
    convert integral_poissonDirichlet_gaussian_tilt_ibp_prod
      hζ hζ1 t ν r hBm hB hlaw hμ n r₀ f hf using 1
  have htransferL := integral_split_poissonBlocks_gaussian ν r hBm hB hlaw hL
  have htransferR := integral_split_poissonBlocks_gaussian ν r hBm hB hlaw hR
  have hactiveL (ω : Ω) : L (Z ω, G ω) =
      ∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 *
            Real.exp (t * ((B (σ j).1.1 ω).2 (σ j).1.2).2) /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1 *
              Real.exp (t * ((B a.1.1 ω).2 a.1.2).2)) *
          (f (fun i j => if σ i = σ j then 1 else 0) *
            ((B (σ r₀).1.1 ω).2 (σ r₀).1.2).2) := by
    simpa only [L, Z, G, Φ, Prod.fst, Prod.snd, Subtype.coe_inj] using
      (gaussian_gibbs_tilt_guard_eq_active t (Z ω) (G ω)
        (fun σ => Φ σ * (G ω (σ r₀).1 (σ r₀).2)) )
  have hactiveR (ω : Ω) : R (Z ω, G ω) =
      ∑' τ : Option (Fin n) → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ j, ((B (τ j).1.1 ω).2 (τ j).1.2).1 *
            Real.exp (t * ((B (τ j).1.1 ω).2 (τ j).1.2).2) /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1 *
              Real.exp (t * ((B a.1.1 ω).2 a.1.2).2)) *
          (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
            (∑ j : Fin n, t * (if τ (some r₀) = τ (some j) then 1 else 0) -
              n * t * (if τ (some r₀) = τ none then 1 else 0))) := by
    simpa only [R, Z, G, Φ, Prod.fst, Prod.snd, Subtype.coe_inj, Fintype.card_fin] using
      (gaussian_gibbs_tilt_guard_eq_active t (Z ω) (G ω)
        (fun τ => Φ (fun i => τ (some i)) *
          (∑ j : Fin n, t * (if τ (some r₀) = τ (some j) then 1 else 0) -
            n * t * (if τ (some r₀) = τ none then 1 else 0))))
  calc
    _ = ∫ ω, L (Z ω, G ω) ∂P := by simp_rw [hactiveL]
    _ = ∫ zg, L zg ∂ρ.prod μ := htransferL
    _ = ∫ zg, R zg ∂ρ.prod μ := hIBP
    _ = ∫ ω, R (Z ω, G ω) ∂P := htransferR.symm
    _ = _ := by simp_rw [hactiveR]

/-- On the original blocks the Gaussian IBP correction is precisely the
old-replica overlap average minus the new-replica overlap average. -/
theorem ae_poissonDirichlet_gaussian_overlap_correction
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1) (t : ℝ)
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ =>
        (ν n).prod (gaussianReal 0 1))) P)
    (hμ : (zetaPoissonMeasure ζ).prod (gaussianReal 0 1) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).prod (gaussianReal 0 1))
    (n : ℕ) (r₀ : Fin n) (f : (Fin n → Fin n → ℝ) → ℝ) :
    ∀ᵐ ω ∂P,
      (∑' τ : Option (Fin n) → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ j, ((B (τ j).1.1 ω).2 (τ j).1.2).1 *
            Real.exp (t * ((B (τ j).1.1 ω).2 (τ j).1.2).2) /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1 *
              Real.exp (t * ((B a.1.1 ω).2 a.1.2).2)) *
          (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
            (∑ j : Fin n, t * (if τ (some r₀) = τ (some j) then 1 else 0) -
              n * t * (if τ (some r₀) = τ none then 1 else 0)))) =
      t * ((∑' σ : Fin n → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
        (∏ j, ((B (σ j).1.1 ω).2 (σ j).1.2).1 *
            Real.exp (t * ((B (σ j).1.1 ω).2 (σ j).1.2).2) /
          ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
            ((B a.1.1 ω).2 a.1.2).1 *
              Real.exp (t * ((B a.1.1 ω).2 a.1.2).2)) *
          (f (fun i j => if σ i = σ j then 1 else 0) *
            ∑ j : Fin n, if σ r₀ = σ j then 1 else 0)) -
        n * (∑' τ : Option (Fin n) → {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
          (∏ j, ((B (τ j).1.1 ω).2 (τ j).1.2).1 *
              Real.exp (t * ((B (τ j).1.1 ω).2 (τ j).1.2).2) /
            ∑' a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1},
              ((B a.1.1 ω).2 a.1.2).1 *
                Real.exp (t * ((B a.1.1 ω).2 a.1.2).2)) *
            (f (fun i j => if τ (some i) = τ (some j) then 1 else 0) *
              (if τ (some r₀) = τ none then 1 else 0)))) := by
  let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
    fun ω m => ((B m ω).1, fun l => ((B m ω).2 l).1)
  let G : Ω → ℕ → ℕ → ℝ := fun ω m l => ((B m ω).2 l).2
  let Φ : (Fin n → ℕ × ℕ) → ℝ := fun σ =>
    f (fun i j => if σ i = σ j then 1 else 0)
  obtain ⟨M, hM⟩ := exists_bound_index_overlap_observable (α := ℕ × ℕ) f
  have henv := ae_poissonDirichlet_gaussian_ibp_environment hζ hζ1
    (fun m => (ν m).prod (gaussianReal 0 1)) r hBm hB hlaw hμ
  have hZm : Measurable Z := measurable_pi_iff.2 fun m =>
    (measurable_fst.comp (hBm m)).prodMk
      (measurable_pi_iff.2 fun l =>
        measurable_fst.comp ((measurable_pi_apply l).comp
          (measurable_snd.comp (hBm m))))
  have hρ : IsProbabilityMeasure (P.map Z) :=
    (Measure.isProbabilityMeasure_map_iff hZm.aemeasurable).2 inferInstance
  have hmass : ∀ᵐ ω ∂P,
      Summable (fun a : {p : ℕ × ℕ // p.2 < (B p.1 ω).1} =>
        ((B a.1.1 ω).2 a.1.2).1 *
          Real.exp (t * ((B a.1.1 ω).2 a.1.2).2)) := by
    have henvρ : ∀ᵐ z ∂P.map Z,
        (∀ p : ℕ × ℕ, p.2 < (z p.1).1 → 0 < (z p.1).2 p.2) ∧
        Summable (fun p : ℕ × ℕ =>
          if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0) := by
      have hmeas := measurableSet_gaussian_gibbs_environment
      have hh : ∀ᵐ z ∂P.map Z,
          Nonempty {p : ℕ × ℕ // p.2 < (z p.1).1} ∧
          (∀ p : ℕ × ℕ, p.2 < (z p.1).1 → 0 < (z p.1).2 p.2) ∧
          (∑' p : ℕ × ℕ, ENNReal.ofReal
            (if p.2 < (z p.1).1 then (z p.1).2 p.2 else 0)) < ∞ :=
        (ae_map_iff hZm.aemeasurable hmeas).2 (by
          filter_upwards [henv] with ω ⟨hn, hp, hs⟩
          refine ⟨hn, (fun p h => hp ⟨p, h⟩), ?_⟩
          have ht := (summable_subtype_iff_indicator (s :=
            {p : ℕ × ℕ | p.2 < (Z ω p.1).1})
            (f := fun p : ℕ × ℕ => (Z ω p.1).2 p.2)).1 hs
          have ht' : Summable (fun p : ℕ × ℕ =>
              if p.2 < (Z ω p.1).1 then (Z ω p.1).2 p.2 else 0) := by
            convert ht using 1
            funext p
            by_cases h : p.2 < (Z ω p.1).1 <;> simp [Set.indicator, h]
          exact ht'.tsum_ofReal_lt_top)
      filter_upwards [hh] with z ⟨_, hp, hs⟩
      refine ⟨hp, summable_of_tsum_ofReal_lt_top (fun p => ?_) hs⟩
      split_ifs with h
      · exact (hp p h).le
      · exact le_refl 0
    have hprod := ae_gaussian_gibbs_tilt_summable_prod t (P.map Z) henvρ
    have hsplit := indepFun_poissonBlocks_snd_marks ν
      (fun _ => gaussianReal 0 1) r hBm hB hlaw
    have hGm : Measurable G := measurable_pi_iff.2 fun m =>
      measurable_pi_iff.2 fun l =>
        measurable_snd.comp ((measurable_pi_apply l).comp
          (measurable_snd.comp (hBm m)))
    have hae : ∀ᵐ ω ∂P,
        (∑' p : ℕ × ℕ, ENNReal.ofReal
          (if p.2 < (Z ω p.1).1 then
            (Z ω p.1).2 p.2 * Real.exp (t * G ω p.1 p.2) else 0)) < ∞ := by
      have hpair : P.map (fun ω => (Z ω, G ω)) =
          (P.map Z).prod (P.map G) :=
        hsplit.1.map_prod_eq_prod_map_map hZm.aemeasurable hGm.aemeasurable
      have hp' : ∀ᵐ zg ∂P.map (fun ω => (Z ω, G ω)),
          (∑' p : ℕ × ℕ, ENNReal.ofReal
            (if p.2 < (zg.1 p.1).1 then
              (zg.1 p.1).2 p.2 * Real.exp (t * zg.2 p.1 p.2) else 0)) < ∞ := by
        rw [hpair, hsplit.2.1.map_eq]
        exact hprod
      exact (ae_map_iff (hZm.prodMk hGm).aemeasurable
        (measurableSet_gaussian_gibbs_tilt_summable t)).1 hp'
    filter_upwards [hae, henv] with ω hs ⟨_, hp, _⟩
    have ht := summable_of_tsum_ofReal_lt_top (fun p : ℕ × ℕ => by
      split_ifs with h
      · exact mul_nonneg (hp ⟨p, h⟩).le (Real.exp_pos _).le
      · exact le_refl 0) hs
    apply (summable_subtype_iff_indicator (s :=
      {p : ℕ × ℕ | p.2 < (Z ω p.1).1})
      (f := fun p : ℕ × ℕ => (Z ω p.1).2 p.2 * Real.exp (t * G ω p.1 p.2))).2
    convert ht using 1
    funext p
    by_cases h : p.2 < (Z ω p.1).1 <;> simp [Set.indicator, h]
  filter_upwards [henv, hmass] with ω ⟨hn, hp, _⟩ hs
  let α := {p : ℕ × ℕ // p.2 < (B p.1 ω).1}
  let _ : Nonempty α := hn
  let u : α → ℝ := fun a => ((B a.1.1 ω).2 a.1.2).1
  let g : α → ℝ := fun a => ((B a.1.1 ω).2 a.1.2).2
  let Ψ : (Fin n → α) → ℝ := fun σ =>
    f (fun i j => if σ i = σ j then 1 else 0)
  have hu (a : α) : 0 < u a := hp a
  have hΨ : ∀ σ, |Ψ σ| ≤ M := by
    intro σ
    simpa only [Ψ, Subtype.coe_inj] using hM (fun i => (σ i).1)
  simpa only [u, g, Ψ, Fintype.card_fin] using
    (gaussian_ibp_overlap_correction_active u hu g t hs r₀ Ψ hΨ)

end SpinGlasses
