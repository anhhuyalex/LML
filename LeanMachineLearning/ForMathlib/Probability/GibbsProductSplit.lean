/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.BoundedTilted

/-!
# A Gibbs measure whose energy splits over the last site is a product

If the energy of a configuration of `N + 1` i.i.d. sites is `E₁(first N sites) + E₂(last site)`,
the Gibbs measure is the product of the Gibbs measures of the two parts.  This is the decoupling of
the last spin at `t = 0` in Talagrand's cavity path (Eq. (1.375)).
-/

@[expose] public section

open MeasureTheory Finset
open scoped BigOperators

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {N : ℕ}

/-- The map `σ ↦ (σ last, σ ∘ castSucc)` is measure preserving for i.i.d. sites. -/
theorem measurePreserving_piFinSuccLast (μ : Measure α) [IsProbabilityMeasure μ] :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => α) (Fin.last N))
      (Measure.pi fun _ : Fin (N + 1) => μ) (μ.prod (Measure.pi fun _ : Fin N => μ)) :=
  measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => μ) (Fin.last N)

/-- The exponential of a bounded measurable function is integrable for a finite measure. -/
theorem integrable_exp_of_abs_le {β : Type*} [MeasurableSpace β] {ν : Measure β}
    [IsFiniteMeasure ν] {E : β → ℝ} (hE : Measurable E) {b : ℝ} (hb : ∀ x, |E x| ≤ b) :
    Integrable (fun x => Real.exp (E x)) ν :=
  integrable_exp_of_ae_le hE.aemeasurable
    (Filter.Eventually.of_forall fun x => (le_abs_self _).trans (hb x))

/-- Splitting off the last site of an i.i.d. configuration. -/
theorem integral_pi_succ_last (μ : Measure α) [IsProbabilityMeasure μ]
    (G : α × (Fin N → α) → ℝ) :
    ∫ σ : Fin (N + 1) → α, G (σ (Fin.last N), fun j => σ j.castSucc)
        ∂(Measure.pi fun _ : Fin (N + 1) => μ) =
      ∫ p, G p ∂(μ.prod (Measure.pi fun _ : Fin N => μ)) := by
  have h := (measurePreserving_piFinSuccLast (N := N) μ).integral_comp' (g := G)
  have he : ∀ σ : Fin (N + 1) → α,
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => α) (Fin.last N) σ =
        (σ (Fin.last N), fun j => σ j.castSucc) := fun σ =>
    Prod.ext rfl (funext fun j => by
      simp [MeasurableEquiv.piFinSuccAbove]; rfl)
  simp only [he] at h
  exact h

/-- **The Gibbs measure of an energy that splits over the last site is a product.**  A function of
the first `N` sites and the last site integrates against the tilted measure as the iterated integral
against the tilted measures of the two parts. -/
theorem integral_tilted_pi_succ_last (μ : Measure α) [IsProbabilityMeasure μ]
    (E₁ : (Fin N → α) → ℝ) (E₂ : α → ℝ) (hE₁ : Measurable E₁) (hE₂ : Measurable E₂)
    {b₁ b₂ : ℝ} (h₁ : ∀ τ, |E₁ τ| ≤ b₁) (h₂ : ∀ a, |E₂ a| ≤ b₂)
    (Φ : (Fin N → α) → α → ℝ) (hΦ : Measurable fun p : (Fin N → α) × α => Φ p.1 p.2) {M : ℝ}
    (hΦb : ∀ τ a, |Φ τ a| ≤ M) :
    ∫ σ : Fin (N + 1) → α, Φ (fun j => σ j.castSucc) (σ (Fin.last N))
        ∂((Measure.pi fun _ : Fin (N + 1) => μ).tilted
          (fun σ => E₁ (fun j => σ j.castSucc) + E₂ (σ (Fin.last N)))) =
      ∫ τ, ∫ a, Φ τ a ∂(μ.tilted E₂) ∂((Measure.pi fun _ : Fin N => μ).tilted E₁) := by
  set ν : Measure (Fin N → α) := Measure.pi fun _ : Fin N => μ with hν
  have he₁m : Measurable fun τ => Real.exp (E₁ τ) := Real.measurable_exp.comp hE₁
  have he₂m : Measurable fun a => Real.exp (E₂ a) := Real.measurable_exp.comp hE₂
  have he₁i : Integrable (fun τ => Real.exp (E₁ τ)) ν :=
    integrable_of_measurable_bound he₁m (M := Real.exp b₁) fun τ => by
      rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.2 ((le_abs_self _).trans (h₁ τ))
  have he₂i : Integrable (fun a => Real.exp (E₂ a)) μ :=
    integrable_of_measurable_bound he₂m (M := Real.exp b₂) fun a => by
      rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.2 ((le_abs_self _).trans (h₂ a))
  have hZ₁ : 0 < ∫ τ, Real.exp (E₁ τ) ∂ν := integral_exp_pos he₁i
  have hZ₂ : 0 < ∫ a, Real.exp (E₂ a) ∂μ := integral_exp_pos he₂i
  have hZ : ∫ σ : Fin (N + 1) → α, Real.exp (E₁ (fun j => σ j.castSucc) + E₂ (σ (Fin.last N)))
      ∂(Measure.pi fun _ : Fin (N + 1) => μ) =
      (∫ a, Real.exp (E₂ a) ∂μ) * ∫ τ, Real.exp (E₁ τ) ∂ν := by
    have := integral_pi_succ_last (N := N) μ
      (fun p => Real.exp (E₂ p.1) * Real.exp (E₁ p.2))
    simp only [← Real.exp_add] at this
    rw [show (fun σ : Fin (N + 1) → α => Real.exp (E₁ (fun j => σ j.castSucc) +
        E₂ (σ (Fin.last N)))) = fun σ => Real.exp (E₂ (σ (Fin.last N)) +
          E₁ (fun j => σ j.castSucc)) from funext fun σ => by rw [add_comm]]
    rw [this]
    simp only [Real.exp_add]
    exact integral_prod_mul (μ := μ) (ν := ν) (fun a => Real.exp (E₂ a))
      (fun τ => Real.exp (E₁ τ))
  set Z₁ : ℝ := ∫ τ, Real.exp (E₁ τ) ∂ν with hZ₁def
  set Z₂ : ℝ := ∫ a, Real.exp (E₂ a) ∂μ with hZ₂def
  have hint : Integrable (fun p : α × (Fin N → α) =>
      Real.exp (E₁ p.2 + E₂ p.1) / (Z₂ * Z₁) * Φ p.2 p.1) (μ.prod ν) := by
    refine integrable_of_measurable_bound (M := Real.exp (b₁ + b₂) / (Z₂ * Z₁) * M) ?_ fun p => ?_
    · exact ((Real.measurable_exp.comp ((hE₁.comp measurable_snd).add
        (hE₂.comp measurable_fst))).div_const _).mul
        (Measurable.comp (g := fun q : (Fin N → α) × α => Φ q.1 q.2) (f := Prod.swap) hΦ
          measurable_swap)
    · rw [abs_mul, abs_of_nonneg (by positivity)]
      refine mul_le_mul (div_le_div_of_nonneg_right (Real.exp_le_exp.2 (by
          have := (le_abs_self (E₁ p.2)).trans (h₁ p.2)
          have := (le_abs_self (E₂ p.1)).trans (h₂ p.1)
          linarith)) (by positivity)) (hΦb _ _) (abs_nonneg _) (by positivity)
  have hLHS : ∫ σ : Fin (N + 1) → α, Φ (fun j => σ j.castSucc) (σ (Fin.last N))
        ∂((Measure.pi fun _ : Fin (N + 1) => μ).tilted
          (fun σ => E₁ (fun j => σ j.castSucc) + E₂ (σ (Fin.last N)))) =
      ∫ τ, ∫ a, Real.exp (E₁ τ + E₂ a) / (Z₂ * Z₁) * Φ τ a ∂μ ∂ν := by
    rw [integral_tilted]
    simp only [smul_eq_mul, hZ]
    rw [integral_pi_succ_last μ (fun p => Real.exp (E₁ p.2 + E₂ p.1) / (Z₂ * Z₁) * Φ p.2 p.1)]
    rw [integral_prod_symm _ hint]
  rw [hLHS, integral_tilted (μ := ν) E₁]
  simp only [smul_eq_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only [integral_tilted, smul_eq_mul]
  rw [← integral_const_mul (Real.exp (E₁ τ) / Z₁)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  beta_reduce
  rw [Real.exp_add, ← hZ₂def]
  field_simp

/-- **The Gibbs measure of a split energy, as a measure statement**: the image of the tilted law of
`N + 1` sites under `σ ↦ (σ last, σ ∘ castSucc)` is the product of the two tilted laws. -/
theorem map_tilted_pi_succ_last (μ : Measure α) [IsProbabilityMeasure μ]
    (E₁ : (Fin N → α) → ℝ) (E₂ : α → ℝ) (hE₁ : Measurable E₁) (hE₂ : Measurable E₂)
    {b₁ b₂ : ℝ} (h₁ : ∀ τ, |E₁ τ| ≤ b₁) (h₂ : ∀ a, |E₂ a| ≤ b₂) :
    ((Measure.pi fun _ : Fin (N + 1) => μ).tilted
        (fun σ => E₁ (fun j => σ j.castSucc) + E₂ (σ (Fin.last N)))).map
      (fun σ => (σ (Fin.last N), fun j => σ j.castSucc)) =
    (μ.tilted E₂).prod ((Measure.pi fun _ : Fin N => μ).tilted E₁) := by
  classical
  classical
  have hE : Measurable fun σ : Fin (N + 1) → α =>
      E₁ (fun j => σ j.castSucc) + E₂ (σ (Fin.last N)) :=
    (hE₁.comp (measurable_pi_iff.2 fun j => measurable_pi_apply _)).add
      (hE₂.comp (measurable_pi_apply _))
  have hb : ∀ σ : Fin (N + 1) → α, |E₁ (fun j => σ j.castSucc) + E₂ (σ (Fin.last N))| ≤ b₁ + b₂ :=
    fun σ => (abs_add_le _ _).trans (add_le_add (h₁ _) (h₂ _))
  have : IsProbabilityMeasure ((Measure.pi fun _ : Fin (N + 1) => μ).tilted
      (fun σ => E₁ (fun j => σ j.castSucc) + E₂ (σ (Fin.last N)))) :=
    isProbabilityMeasure_tilted (integrable_exp_of_abs_le hE hb)
  have : IsProbabilityMeasure (μ.tilted E₂) :=
    isProbabilityMeasure_tilted (integrable_exp_of_abs_le hE₂ h₂)
  have : IsProbabilityMeasure ((Measure.pi fun _ : Fin N => μ).tilted E₁) :=
    isProbabilityMeasure_tilted (integrable_exp_of_abs_le hE₁ h₁)
  refine (Measure.prod_eq fun s t hs ht => ?_).symm
  have hmeas : Measurable fun σ : Fin (N + 1) → α =>
      (σ (Fin.last N), fun j : Fin N => σ j.castSucc) :=
    (measurable_pi_apply _).prodMk (measurable_pi_iff.2 fun j => measurable_pi_apply _)
  rw [Measure.map_apply hmeas (hs.prod ht)]
  have hΦ : Measurable fun p : (Fin N → α) × α => t.indicator (1 : (Fin N → α) → ℝ) p.1 *
      s.indicator (1 : α → ℝ) p.2 :=
    ((measurable_one.indicator ht).comp measurable_fst).mul
      ((measurable_one.indicator hs).comp measurable_snd)
  have key := integral_tilted_pi_succ_last μ E₁ E₂ hE₁ hE₂ h₁ h₂
    (fun τ a => t.indicator (1 : (Fin N → α) → ℝ) τ * s.indicator (1 : α → ℝ) a) hΦ (M := 1)
    (fun τ a => by
      rw [abs_mul]
      have h1 : |t.indicator (1 : (Fin N → α) → ℝ) τ| ≤ 1 := by
        by_cases h : τ ∈ t <;> simp [h]
      have h2 : |s.indicator (1 : α → ℝ) a| ≤ 1 := by
        by_cases h : a ∈ s <;> simp [h]
      calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1)
  have hpre : (fun σ : Fin (N + 1) → α => (σ (Fin.last N), fun j : Fin N => σ j.castSucc)) ⁻¹'
      (s ×ˢ t) = {σ | (fun j => σ j.castSucc) ∈ t} ∩ {σ | σ (Fin.last N) ∈ s} := by
    ext σ; simp [and_comm]
  have hmp := hmeas (hs.prod ht)
  have hl : ∫ σ : Fin (N + 1) → α, t.indicator (1 : (Fin N → α) → ℝ) (fun j => σ j.castSucc) *
      s.indicator (1 : α → ℝ) (σ (Fin.last N)) ∂((Measure.pi fun _ : Fin (N + 1) => μ).tilted
        (fun σ => E₁ (fun j => σ j.castSucc) + E₂ (σ (Fin.last N)))) =
      ((Measure.pi fun _ : Fin (N + 1) => μ).tilted
        (fun σ => E₁ (fun j => σ j.castSucc) + E₂ (σ (Fin.last N)))).real
        ((fun σ : Fin (N + 1) → α =>
          (σ (Fin.last N), fun j : Fin N => σ j.castSucc)) ⁻¹' (s ×ˢ t)) := by
    rw [← integral_indicator_one hmp]
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    by_cases h1 : (fun j => σ j.castSucc) ∈ t <;> by_cases h2 : σ (Fin.last N) ∈ s <;>
      simp [h1, h2]
  have hr : ∫ τ, ∫ a, t.indicator (1 : (Fin N → α) → ℝ) τ * s.indicator (1 : α → ℝ) a
      ∂(μ.tilted E₂) ∂((Measure.pi fun _ : Fin N => μ).tilted E₁) =
      (μ.tilted E₂).real s * ((Measure.pi fun _ : Fin N => μ).tilted E₁).real t := by
    simp_rw [integral_const_mul, integral_indicator_one hs]
    rw [integral_mul_const, integral_indicator_one ht, mul_comm]
  rw [hl, hr] at key
  rw [← ofReal_measureReal (measure_ne_top _ _), key, ENNReal.ofReal_mul measureReal_nonneg,
    ofReal_measureReal (measure_ne_top _ _), ofReal_measureReal (measure_ne_top _ _)]

/-- **Replicas of a split Gibbs measure.**  For `ι` i.i.d. replicas of a configuration of `N + 1`
sites with energy `E₁(first N sites) + E₂(last site)`, the average of a product of a function of the
first `N` sites of all replicas and a function of the last sites of all replicas is the product of
the two replica averages (for the Gibbs measures of `E₁` and of `E₂`). -/
theorem integral_pi_tilted_split {ι : Type*} [Fintype ι] (μ : Measure α) [IsProbabilityMeasure μ]
    (E₁ : (Fin N → α) → ℝ) (E₂ : α → ℝ) (hE₁ : Measurable E₁) (hE₂ : Measurable E₂)
    {b₁ b₂ : ℝ} (h₁ : ∀ τ, |E₁ τ| ≤ b₁) (h₂ : ∀ a, |E₂ a| ≤ b₂)
    (Ψ₁ : (ι → Fin N → α) → ℝ) (Ψ₂ : (ι → α) → ℝ) (hΨ₁ : Measurable Ψ₁) (hΨ₂ : Measurable Ψ₂) :
    ∫ σ : ι → Fin (N + 1) → α, Ψ₁ (fun i j => σ i j.castSucc) * Ψ₂ (fun i => σ i (Fin.last N))
        ∂(Measure.pi fun _ : ι => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
          (fun σ => E₁ (fun j => σ j.castSucc) + E₂ (σ (Fin.last N)))) =
      (∫ τ, Ψ₁ τ ∂(Measure.pi fun _ : ι => (Measure.pi fun _ : Fin N => μ).tilted E₁)) *
        ∫ a, Ψ₂ a ∂(Measure.pi fun _ : ι => μ.tilted E₂) := by
  classical
  set f : (Fin (N + 1) → α) → α × (Fin N → α) :=
    fun σ => (σ (Fin.last N), fun j : Fin N => σ j.castSucc) with hf
  have hfm : Measurable f :=
    (measurable_pi_apply _).prodMk (measurable_pi_iff.2 fun j => measurable_pi_apply _)
  have hE : Measurable fun σ : Fin (N + 1) → α =>
      E₁ (fun j => σ j.castSucc) + E₂ (σ (Fin.last N)) :=
    (hE₁.comp (measurable_pi_iff.2 fun j => measurable_pi_apply _)).add
      (hE₂.comp (measurable_pi_apply _))
  have hb : ∀ σ : Fin (N + 1) → α, |E₁ (fun j => σ j.castSucc) + E₂ (σ (Fin.last N))| ≤ b₁ + b₂ :=
    fun σ => (abs_add_le _ _).trans (add_le_add (h₁ _) (h₂ _))
  have : IsProbabilityMeasure ((Measure.pi fun _ : Fin (N + 1) => μ).tilted
      (fun σ => E₁ (fun j => σ j.castSucc) + E₂ (σ (Fin.last N)))) :=
    isProbabilityMeasure_tilted (integrable_exp_of_abs_le hE hb)
  have : IsProbabilityMeasure (μ.tilted E₂) := isProbabilityMeasure_tilted
    (integrable_exp_of_abs_le hE₂ h₂)
  have : IsProbabilityMeasure ((Measure.pi fun _ : Fin N => μ).tilted E₁) :=
    isProbabilityMeasure_tilted (integrable_exp_of_abs_le hE₁ h₁)
  have hmap := map_tilted_pi_succ_last μ E₁ E₂ hE₁ hE₂ h₁ h₂
  set g : (ι → Fin (N + 1) → α) → (ι → α) × (ι → Fin N → α) :=
    fun σ => (fun i => σ i (Fin.last N), fun i j => σ i j.castSucc) with hg
  have hgm : Measurable g :=
    (measurable_pi_iff.2 fun i => (measurable_pi_apply (Fin.last N)).comp
      (measurable_pi_apply i)).prodMk
      (measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
        (measurable_pi_apply _).comp (measurable_pi_apply i))
  have hgmap : (Measure.pi fun _ : ι => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
      (fun σ => E₁ (fun j => σ j.castSucc) + E₂ (σ (Fin.last N)))).map g =
      (Measure.pi fun _ : ι => μ.tilted E₂).prod
        (Measure.pi fun _ : ι => (Measure.pi fun _ : Fin N => μ).tilted E₁) := by
    have h1 := Measure.pi_map_pi (ι := ι)
      (μ := fun _ => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
        (fun σ => E₁ (fun j => σ j.castSucc) + E₂ (σ (Fin.last N)))) (f := fun _ => f)
      (fun _ => hfm.aemeasurable)
    rw [hmap] at h1
    have h2 := (measurePreserving_arrowProdEquivProdArrow α (Fin N → α) ι
      (fun _ => μ.tilted E₂) (fun _ => (Measure.pi fun _ : Fin N => μ).tilted E₁)).map_eq
    have hF : Measurable fun x : ι → Fin (N + 1) → α => fun i => f (x i) :=
      measurable_pi_iff.2 fun i => hfm.comp (measurable_pi_apply i)
    rw [← h2, ← h1, Measure.map_map (MeasurableEquiv.measurable _) hF]
    rfl
  have := integral_map (μ := Measure.pi fun _ : ι => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
      (fun σ => E₁ (fun j => σ j.castSucc) + E₂ (σ (Fin.last N)))) hgm.aemeasurable
    (f := fun p : (ι → α) × (ι → Fin N → α) => Ψ₂ p.1 * Ψ₁ p.2)
    ((hΨ₂.comp measurable_fst).mul (hΨ₁.comp measurable_snd)).aestronglyMeasurable
  rw [hgmap, integral_prod_mul (μ := Measure.pi fun _ : ι => μ.tilted E₂) (fun a => Ψ₂ a)
    (fun τ => Ψ₁ τ)] at this
  rw [mul_comm (∫ τ, Ψ₁ τ ∂_), this]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

end MeasureTheory
