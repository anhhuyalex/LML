/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.HasLaw
public import LeanMachineLearning.ForMathlib.Probability.ExchangeableMixture
public import LeanMachineLearning.ForMathlib.Probability.Independence.IndepInfinitePi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.StrongLaw

/-!
# The strong law of large numbers for conditionally i.i.d. sequences

Let `a ~ μ` be a parameter and `(c i)_i` an i.i.d. sequence with law `ν`, independent of `a`.  For
a measurable `Ψ`, the averages `n⁻¹ ∑_{i<n} Ψ a (c i)` converge almost surely to the conditional
mean `∫ Ψ a c dν` (`ProbabilityTheory.ae_tendsto_mean_prod_infinitePi`): Etemadi's law
(`ProbabilityTheory.strong_law_ae`) for each fixed `a`, and Fubini.  This is the form used for
exchangeable arrays whose rows are conditionally independent given a random environment.

For an i.i.d. family indexed by a general set `J`, the same conclusion holds for the averages of
a fixed function of *blocks* `σ ∘ f i` of the family along pairwise disjoint blocks `f i : F → J`
(`ProbabilityTheory.ae_tendsto_mean_infinitePi_blocks`).
-/

@[expose] public section

open MeasureTheory Filter Finset
open scoped Topology

namespace ProbabilityTheory

variable {A C : Type*} [MeasurableSpace A] [MeasurableSpace C]

/-- **Strong law of large numbers, mixture form.**  If `Ψ a` is `ν`-integrable for almost every
`a ~ μ`, then for `(a, c) ~ μ ⊗ ν^{⊗ℕ}` the averages `n⁻¹ ∑_{i<n} Ψ a (c i)` converge to
`∫ Ψ a dν` almost surely. -/
theorem ae_tendsto_mean_prod_infinitePi (μ : Measure A)
    (ν : Measure C) [IsProbabilityMeasure ν] {Ψ : A → C → ℝ} (hΨ : Measurable (Function.uncurry Ψ))
    (hint : ∀ᵐ a ∂μ, Integrable (Ψ a) ν) :
    ∀ᵐ z ∂(μ.prod (Measure.infinitePi fun _ : ℕ => ν)),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, Ψ z.1 (z.2 i)) atTop
        (𝓝 (∫ c, Ψ z.1 c ∂ν)) := by
  have hterm : ∀ i : ℕ, Measurable fun z : A × (ℕ → C) => Ψ z.1 (z.2 i) := fun i =>
    hΨ.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hmean : Measurable fun z : A × (ℕ → C) => ∫ c, Ψ z.1 c ∂ν :=
    (StronglyMeasurable.integral_prod_right' (f := Function.uncurry Ψ) (ν := ν)
      hΨ.stronglyMeasurable).measurable.comp measurable_fst
  have hset := measurableSet_tendsto_fun (l := atTop)
    (f := fun (n : ℕ) (z : A × (ℕ → C)) => (n : ℝ)⁻¹ * ∑ i ∈ range n, Ψ z.1 (z.2 i))
    (fun n => measurable_const.mul (Finset.measurable_sum _ fun i _ => hterm i)) hmean
  rw [Measure.ae_prod_iff_ae_ae hset]
  filter_upwards [hint] with a ha
  have hΨa : Measurable (Ψ a) := hΨ.comp (measurable_const.prodMk measurable_id)
  have hlaw : ∀ i : ℕ, HasLaw (fun c : ℕ → C => Ψ a (c i)) (ν.map (Ψ a))
      (Measure.infinitePi fun _ : ℕ => ν) := fun i =>
    (hΨa.hasLaw_map ν).comp (hasLaw_eval_infinitePi (fun _ : ℕ => ν) i)
  have hindep := iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ c => Ψ a c)
    fun _ => hΨa
  have hev := hasLaw_eval_infinitePi (fun _ : ℕ => ν) 0
  have h := strong_law_ae_real (μ := Measure.infinitePi fun _ : ℕ => ν)
    (fun i (c : ℕ → C) => Ψ a (c i)) (hev.integrable_comp ha)
    (fun i j hij => hindep.indepFun hij) fun i => (hlaw i).identDistrib (hlaw 0)
  have hint0 : ∫ c, Ψ a (c 0) ∂(Measure.infinitePi fun _ : ℕ => ν) = ∫ c, Ψ a c ∂ν :=
    hev.integral_comp ha.1
  rw [hint0] at h
  filter_upwards [h] with c hc
  simpa [div_eq_inv_mul] using hc

/-- **Strong law of large numbers along disjoint blocks of an i.i.d. family.**  Let `σ` be an
i.i.d. family indexed by `J` and `f i : F → J` injective maps with pairwise disjoint ranges.  For
`Φ` integrable against the law `ν^{⊗F}` of one block, `n⁻¹ ∑_{i<n} Φ (σ ∘ f i)` converges almost
surely to `∫ Φ d(ν^{⊗F})`. -/
theorem ae_tendsto_mean_infinitePi_blocks {J C F : Type*} [Fintype F] [MeasurableSpace C]
    (ν : Measure C) [IsProbabilityMeasure ν] {f : ℕ → F → J} (hf : ∀ i, Function.Injective (f i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.range (f i)) (Set.range (f j))) {Φ : (F → C) → ℝ}
    (hΦ : Measurable Φ) (hint : Integrable Φ (Measure.pi fun _ : F => ν)) :
    ∀ᵐ σ ∂(Measure.infinitePi fun _ : J => ν),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, Φ (fun a => σ (f i a))) atTop
        (𝓝 (∫ y, Φ y ∂(Measure.pi fun _ : F => ν))) := by
  have hres : ∀ i, MeasurePreserving (fun (σ : J → C) (a : F) => σ (f i a))
      (Measure.infinitePi fun _ : J => ν) (Measure.pi fun _ : F => ν) := fun i =>
    Measure.measurePreserving_restrict_infinitePi ν (hf i)
  have hlaw : ∀ i, HasLaw (fun σ : J → C => Φ fun a => σ (f i a))
      ((Measure.pi fun _ : F => ν).map Φ) (Measure.infinitePi fun _ : J => ν) := fun i =>
    (hΦ.hasLaw_map _).comp (hres i).hasLaw
  have hindep : ∀ i j, i ≠ j → IndepFun (fun σ : J → C => Φ fun a => σ (f i a))
      (fun σ : J → C => Φ fun a => σ (f j a)) (Measure.infinitePi fun _ : J => ν) :=
    fun i j hij => (Measure.indepFun_restrict_infinitePi_of_disjoint ν (hdisj i j hij)).comp hΦ hΦ
  have h := strong_law_ae_real (μ := Measure.infinitePi fun _ : J => ν)
    (fun i (σ : J → C) => Φ fun a => σ (f i a)) ((hres 0).hasLaw.integrable_comp hint)
    (fun i j hij => hindep i j hij) fun i => (hlaw i).identDistrib (hlaw 0)
  have h0 : ∫ σ : J → C, Φ (fun a => σ (f 0 a)) ∂(Measure.infinitePi fun _ : J => ν) =
      ∫ y, Φ y ∂(Measure.pi fun _ : F => ν) :=
    (hres 0).hasLaw.integral_comp hΦ.aestronglyMeasurable
  rw [h0] at h
  filter_upwards [h] with σ hσ
  simpa [div_eq_inv_mul] using hσ

/-- **Averages of a nonintegrable nonnegative block function tend to infinity.**  In the setting of
`ae_tendsto_mean_infinitePi_blocks`, if `Φ ≥ 0` is not integrable then
`n⁻¹ ∑_{i<n} Φ (σ ∘ f i) → ∞` almost surely: truncate `Φ` at `M`, apply the strong law, and let
`M → ∞` (monotone convergence). -/
theorem ae_tendsto_atTop_mean_infinitePi_blocks {J C F : Type*} [Fintype F] [MeasurableSpace C]
    (ν : Measure C) [IsProbabilityMeasure ν] {f : ℕ → F → J} (hf : ∀ i, Function.Injective (f i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Set.range (f i)) (Set.range (f j))) {Φ : (F → C) → ℝ}
    (hΦ : Measurable Φ) (hnn : ∀ y, 0 ≤ Φ y) (hint : ¬ Integrable Φ (Measure.pi fun _ : F => ν)) :
    ∀ᵐ σ ∂(Measure.infinitePi fun _ : J => ν),
      Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, Φ (fun a => σ (f i a))) atTop atTop := by
  set π := Measure.pi fun _ : F => ν with hπ
  have hΦM : ∀ M : ℕ, Measurable fun y => min (Φ y) M := fun M => hΦ.min measurable_const
  have hΦMi : ∀ M : ℕ, Integrable (fun y => min (Φ y) M) π := fun M =>
    Integrable.of_bound (hΦM M).aestronglyMeasurable M (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (le_min (hnn y) M.cast_nonneg)]; exact min_le_right _ _)
  have hall := ae_all_iff.2 fun M : ℕ => ae_tendsto_mean_infinitePi_blocks ν hf hdisj (hΦM M)
    (hΦMi M)
  -- the truncated integrals are unbounded
  have hunb : ∀ K : ℝ, ∃ M : ℕ, K < ∫ y, min (Φ y) M ∂π := by
    intro K
    by_contra hK
    push Not at hK
    refine hint ?_
    have hle : ∀ M : ℕ, ∫⁻ y, ENNReal.ofReal (min (Φ y) M) ∂π ≤
        ENNReal.ofReal (max K 0) := fun M => by
      rw [← ofReal_integral_eq_lintegral_ofReal (hΦMi M)
        (Filter.Eventually.of_forall fun y => le_min (hnn y) M.cast_nonneg)]
      exact ENNReal.ofReal_le_ofReal ((hK M).trans (le_max_left _ _))
    have hsup : ∀ y, ENNReal.ofReal (Φ y) = ⨆ M : ℕ, ENNReal.ofReal (min (Φ y) M) := fun y => by
      refine le_antisymm ?_ (iSup_le fun M => ENNReal.ofReal_le_ofReal (min_le_left _ _))
      obtain ⟨M, hM⟩ := exists_nat_ge (Φ y)
      exact le_iSup_of_le M (by rw [min_eq_left hM])
    have hmono : Monotone fun (M : ℕ) y => ENNReal.ofReal (min (Φ y) M) := fun M N hMN y =>
      ENNReal.ofReal_le_ofReal (min_le_min_left _ (Nat.cast_le.2 hMN))
    have hfin : ∫⁻ y, ENNReal.ofReal (Φ y) ∂π ≠ ⊤ := by
      simp_rw [hsup]
      rw [lintegral_iSup (f := fun (M : ℕ) y => ENNReal.ofReal (min (Φ y) (M : ℝ)))
        (fun M => ENNReal.measurable_ofReal.comp (hΦM M)) hmono]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le hle)
    exact (lintegral_ofReal_ne_top_iff_integrable hΦ.aestronglyMeasurable
      (Filter.Eventually.of_forall hnn)).1 hfin
  filter_upwards [hall] with σ hσ
  refine Filter.tendsto_atTop.2 fun K => ?_
  obtain ⟨M, hM⟩ := hunb (K + 1)
  filter_upwards [(hσ M).eventually_const_lt hM] with n hn
  have h1 : (n : ℝ)⁻¹ * ∑ i ∈ range n, min (Φ fun a => σ (f i a)) (M : ℝ) ≤
      (n : ℝ)⁻¹ * ∑ i ∈ range n, Φ fun a => σ (f i a) :=
    mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => min_le_left _ _)
      (inv_nonneg.2 n.cast_nonneg)
  linarith

end ProbabilityTheory
