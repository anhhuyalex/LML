/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletRankedMarkedLaw

/-!
# The root step of the Parisi recursion

The analytic step of Theorem 2.9, on a canonical product space. The ranked masses `uₙ` of the root
of a Ruelle cascade are marked by i.i.d. labels `λₙ ~ ρ` and i.i.d. subtree data `sₙ ~ σ`. If the
subtree quantity `Φ(θ, s)` has, for every fixed label `θ`, the law of `exp (h θ) V(s)` (the
induction hypothesis), then `∑ uₙ Φ(λₙ, sₙ)` has the law of `exp h₀ ∑ uₙ V(sₙ)`, where
`exp (ζ h₀) = ∫ exp (ζ h) dρ`. This is the recursion `X₀ = ζ⁻¹ log E exp ζ X₁`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SpinGlasses

variable {Ξ S : Type*} [MeasurableSpace Ξ] [MeasurableSpace S]

/-- Replacing the subtree quantity `Φ(λₙ, sₙ)` by a variable with the same conditional law given
the label does not change the law of the root sum. -/
theorem map_root_sum_replace (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)]
    (rate : ℕ → ℝ≥0) (ρ : Measure Ξ) [IsProbabilityMeasure ρ] (σ : Measure S)
    [IsProbabilityMeasure σ] (Φ Ψ : Ξ → S → ℝ≥0∞) (hΦ : Measurable (Function.uncurry Φ))
    (hΨ : Measurable (Function.uncurry Ψ)) (h : ∀ θ, σ.map (Φ θ) = σ.map (Ψ θ)) :
    (((Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).prod
        (Measure.infinitePi fun _ : ℕ => ρ)).prod (Measure.infinitePi fun _ : ℕ => σ)).map
      (fun p => ∑' n, nthLargestAtom n (poissonCountingMeasure
        (fun k => (p.1.1 k).1) (fun k l => (p.1.1 k).2 l)) * Φ (p.1.2 n) (p.2 n)) =
    (((Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).prod
        (Measure.infinitePi fun _ : ℕ => ρ)).prod (Measure.infinitePi fun _ : ℕ => σ)).map
      (fun p => ∑' n, nthLargestAtom n (poissonCountingMeasure
        (fun k => (p.1.1 k).1) (fun k l => (p.1.1 k).2 l)) * Ψ (p.1.2 n) (p.2 n)) := by
  set μ := (Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).prod
    (Measure.infinitePi fun _ : ℕ => ρ) with hμ
  have ha : Measurable fun x : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) => fun n => x.2 n :=
    measurable_pi_iff.2 fun n => (measurable_pi_apply n).comp measurable_snd
  have hrep := Measure.map_prod_infinitePi_replace μ (fun x n => x.2 n) ha σ σ Φ Ψ hΦ hΨ h
  have hG : Measurable fun q : ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) × (ℕ → ℝ≥0∞) =>
      ∑' n, nthLargestAtom n (poissonCountingMeasure
        (fun k => (q.1.1 k).1) (fun k l => (q.1.1 k).2 l)) * q.2 n :=
    Measurable.tsum fun n => ((measurable_nthLargestAtom n).comp
      (measurable_poissonCountingMeasure.comp (measurable_fst.comp measurable_fst))).mul
      ((measurable_pi_apply n).comp measurable_snd)
  have hl : ∀ n, Measurable fun p : ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) × (ℕ → S) =>
      (p.1.2 n, p.2 n) := fun n =>
    ((measurable_pi_apply n).comp (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_pi_apply n).comp measurable_snd)
  have hm1 : Measurable fun p : ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) × (ℕ → S) =>
      (p.1, fun n => Φ (p.1.2 n) (p.2 n)) :=
    measurable_fst.prodMk (measurable_pi_iff.2 fun n => hΦ.comp (hl n))
  have hm2 : Measurable fun p : ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) × (ℕ → S) =>
      (p.1, fun n => Ψ (p.1.2 n) (p.2 n)) :=
    measurable_fst.prodMk (measurable_pi_iff.2 fun n => hΨ.comp (hl n))
  have e1 := Measure.map_map (μ := μ.prod (Measure.infinitePi fun _ : ℕ => σ)) hG hm1
  have e2 := Measure.map_map (μ := μ.prod (Measure.infinitePi fun _ : ℕ => σ)) hG hm2
  rw [show (fun p : ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) × (ℕ → S) => ∑' n, nthLargestAtom n
        (poissonCountingMeasure (fun k => (p.1.1 k).1) (fun k l => (p.1.1 k).2 l)) *
          Φ (p.1.2 n) (p.2 n)) =
      (fun q => ∑' n, nthLargestAtom n (poissonCountingMeasure
        (fun k => (q.1.1 k).1) (fun k l => (q.1.1 k).2 l)) * q.2 n) ∘
        (fun p : ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) × (ℕ → S) =>
          (p.1, fun n => Φ (p.1.2 n) (p.2 n))) from rfl,
    show (fun p : ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) × (ℕ → S) => ∑' n, nthLargestAtom n
        (poissonCountingMeasure (fun k => (p.1.1 k).1) (fun k l => (p.1.1 k).2 l)) *
          Ψ (p.1.2 n) (p.2 n)) =
      (fun q => ∑' n, nthLargestAtom n (poissonCountingMeasure
        (fun k => (q.1.1 k).1) (fun k l => (q.1.1 k).2 l)) * q.2 n) ∘
        (fun p : ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) × (ℕ → S) =>
          (p.1, fun n => Ψ (p.1.2 n) (p.2 n))) from rfl,
    ← e1, ← e2, hrep]

/-- The `ζ`-moment of `exp (h θ) V(s)` over independent `θ ~ ρ` and `s ~ σ` factors. -/
theorem lintegral_prod_rpow_exp_mul {ζ : ℝ} (hζ : 0 < ζ) (ρ : Measure Ξ)
    [IsProbabilityMeasure ρ] (σ : Measure S) [IsProbabilityMeasure σ] {h : Ξ → ℝ}
    (hh : Measurable h) {V : S → ℝ} (hV : Measurable V)
    (hint : Integrable (fun θ => Real.exp (ζ * h θ)) ρ) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (h y.1) * V y.2) ^ ζ ∂ρ.prod σ) =
      ENNReal.ofReal (∫ θ, Real.exp (ζ * h θ) ∂ρ) * ∫⁻ s, ENNReal.ofReal (V s) ^ ζ ∂σ := by
  have hpt : ∀ y : Ξ × S, ENNReal.ofReal (Real.exp (h y.1) * V y.2) ^ ζ =
      ENNReal.ofReal (Real.exp (ζ * h y.1)) * ENNReal.ofReal (V y.2) ^ ζ := by
    intro y
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.mul_rpow_of_nonneg _ _ hζ.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hζ.le, ← Real.exp_mul, mul_comm (h y.1) ζ]
  simp_rw [hpt]
  rw [lintegral_prod_mul
    (f := fun θ => ENNReal.ofReal (Real.exp (ζ * h θ))) (g := fun s => ENNReal.ofReal (V s) ^ ζ)
    (ENNReal.measurable_ofReal.comp (by fun_prop)).aemeasurable
    (ENNReal.measurable_ofReal.pow_const ζ |>.comp hV).aemeasurable,
    ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun θ =>
      (Real.exp_pos _).le)]

/-- Pairing the label and subtree coordinates: `((b, λ), s) ↦ (b, (λₙ, sₙ))`. -/
theorem map_prod_prod_zip {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsProbabilityMeasure μ]
    (ρ : Measure Ξ) [IsProbabilityMeasure ρ] (σ : Measure S) [IsProbabilityMeasure σ] :
    ((μ.prod (Measure.infinitePi fun _ : ℕ => ρ)).prod (Measure.infinitePi fun _ : ℕ => σ)).map
      (fun p => (p.1.1, fun n => (p.1.2 n, p.2 n))) =
    μ.prod (Measure.infinitePi fun _ : ℕ => ρ.prod σ) := by
  have hz : Measurable fun p : (ℕ → Ξ) × (ℕ → S) => fun n => (p.1 n, p.2 n) :=
    measurable_pi_iff.2 fun n => ((measurable_pi_apply n).comp measurable_fst).prodMk
      ((measurable_pi_apply n).comp measurable_snd)
  have hassoc := measurePreserving_prodAssoc μ (Measure.infinitePi fun _ : ℕ => ρ)
    (Measure.infinitePi fun _ : ℕ => σ)
  have hmap := Measure.map_prod_map μ ((Measure.infinitePi fun _ : ℕ => ρ).prod
    (Measure.infinitePi fun _ : ℕ => σ)) (f := id) (g := fun p : (ℕ → Ξ) × (ℕ → S) =>
      fun n => (p.1 n, p.2 n)) measurable_id hz
  rw [Measure.infinitePi_prod_map_zip (fun _ : ℕ => ρ) (fun _ : ℕ => σ), Measure.map_id]
    at hmap
  rw [hmap, ← hassoc.map_eq, Measure.map_map (measurable_id.prodMap hz)
    MeasurableEquiv.prodAssoc.measurable]
  rfl

/-- **The root step of Theorem 2.9.** Let the ranked masses `uₙ` of ζ-Poisson blocks be marked by
i.i.d. labels `λₙ ~ ρ` and i.i.d. subtree data `sₙ ~ σ`. Suppose that for every label `θ` the
subtree quantity `Φ(θ, s)` has the law of `exp (h θ) V(s)`, with `V` positive and
`0 < E V^ζ < ∞`, and that `E exp (ζ h) = exp (ζ h₀)`. Then `∑ uₙ Φ(λₙ, sₙ)` has the law of
`exp h₀ ∑ uₙ V(sₙ)`. -/
theorem map_root_sum_parisi {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (nu : ℕ → Measure ℝ) [∀ k, IsProbabilityMeasure (nu k)] (rate : ℕ → ℝ≥0)
    (hmu : zetaPoissonMeasure ζ = Measure.sum fun k => (rate k : ℝ≥0∞) • nu k)
    (ρ : Measure Ξ) [IsProbabilityMeasure ρ] (σ : Measure S) [IsProbabilityMeasure σ]
    (Φ : Ξ → S → ℝ≥0∞) (hΦ : Measurable (Function.uncurry Φ)) {V : S → ℝ} (hV : Measurable V)
    {h : Ξ → ℝ} (hh : Measurable h) (h₀ : ℝ)
    (hlaw : ∀ θ, σ.map (Φ θ) = σ.map (fun s => ENNReal.ofReal (Real.exp (h θ) * V s)))
    (hVpos : ∀ᵐ s ∂σ, 0 < V s) (hVm : 0 < ∫⁻ s, ENNReal.ofReal (V s) ^ ζ ∂σ)
    (hVf : ∫⁻ s, ENNReal.ofReal (V s) ^ ζ ∂σ < ∞)
    (hint : Integrable (fun θ => Real.exp (ζ * h θ)) ρ)
    (hh₀ : ∫ θ, Real.exp (ζ * h θ) ∂ρ = Real.exp (ζ * h₀)) :
    (((Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).prod
        (Measure.infinitePi fun _ : ℕ => ρ)).prod (Measure.infinitePi fun _ : ℕ => σ)).map
      (fun p => ∑' n, nthLargestAtom n (poissonCountingMeasure
        (fun k => (p.1.1 k).1) (fun k l => (p.1.1 k).2 l)) * Φ (p.1.2 n) (p.2 n)) =
    (((Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)).prod
        (Measure.infinitePi fun _ : ℕ => ρ)).prod (Measure.infinitePi fun _ : ℕ => σ)).map
      (fun p => ENNReal.ofReal (Real.exp h₀) * ∑' n, nthLargestAtom n (poissonCountingMeasure
        (fun k => (p.1.1 k).1) (fun k l => (p.1.1 k).2 l)) * ENNReal.ofReal (V (p.2 n))) := by
  have hΨ : Measurable (Function.uncurry fun (θ : Ξ) (s : S) =>
      ENNReal.ofReal (Real.exp (h θ) * V s)) :=
    ENNReal.measurable_ofReal.comp (((hh.comp measurable_fst).exp).mul (hV.comp measurable_snd))
  rw [map_root_sum_replace nu rate ρ σ Φ _ hΦ hΨ hlaw]
  set 𝓑 := Measure.infinitePi fun k => Po(rate k).prod (Measure.infinitePi fun _ : ℕ => nu k)
    with h𝓑
  have hzip := map_prod_prod_zip 𝓑 ρ σ
  -- moments of the two marks
  have hXpos : ∀ᵐ y ∂ρ.prod σ, 0 < Real.exp (h y.1) * V y.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae hVpos] with y hy
    exact mul_pos (Real.exp_pos _) hy
  have hm1 := lintegral_prod_rpow_exp_mul hζ0 ρ σ hh hV hint
  rw [hh₀] at hm1
  have hVpos' : ∀ᵐ y ∂ρ.prod σ, 0 < V y.2 := Measure.quasiMeasurePreserving_snd.ae hVpos
  have hmV : ∫⁻ y, ENNReal.ofReal (V y.2) ^ ζ ∂ρ.prod σ = ∫⁻ s, ENNReal.ofReal (V s) ^ ζ ∂σ := by
    have hm : Measurable fun y : Ξ × S => ENNReal.ofReal (V y.2) ^ ζ :=
      (ENNReal.measurable_ofReal.pow_const ζ).comp (hV.comp measurable_snd)
    rw [lintegral_prod _ hm.aemeasurable]
    simp
  -- apply Theorem 2.6 for ranked atoms twice
  have hA := map_prod_tsum_ranked_marked_eq hζ0 hζ1 nu rate hmu (ρ.prod σ)
    (X := fun y : Ξ × S => Real.exp (h y.1) * V y.2)
    ((hh.comp measurable_fst).exp.mul (hV.comp measurable_snd)) hXpos
    (by rw [hm1]; exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' hVm.ne')
    (by rw [hm1]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hVf)
  have hB := map_prod_tsum_ranked_marked_eq hζ0 hζ1 nu rate hmu (ρ.prod σ)
    (X := fun y : Ξ × S => V y.2) (hV.comp measurable_snd) hVpos'
    (by rw [hmV]; exact hVm) (by rw [hmV]; exact hVf)
  have hz3 : Measurable fun p : ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) × (ℕ → S) =>
      ((p.1.1, fun n => (p.1.2 n, p.2 n)) : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ × S)) :=
    (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun n =>
      (((measurable_pi_apply n).comp (measurable_snd.comp measurable_fst)).prodMk
        ((measurable_pi_apply n).comp measurable_snd)))
  have hFX := measurable_tsum_ranked_mul (T := Ξ × S)
    (X := fun y : Ξ × S => Real.exp (h y.1) * V y.2)
    ((hh.comp measurable_fst).exp.mul (hV.comp measurable_snd))
  have hFV := measurable_tsum_ranked_mul (T := Ξ × S) (X := fun y : Ξ × S => V y.2)
    (hV.comp measurable_snd)
  have hc0 : Measurable fun z : ℝ≥0∞ => ENNReal.ofReal (Real.exp h₀) * z :=
    measurable_const.mul measurable_id
  have e1 : (((𝓑.prod (Measure.infinitePi fun _ : ℕ => ρ)).prod
        (Measure.infinitePi fun _ : ℕ => σ)).map
      (fun p => ∑' n, nthLargestAtom n (poissonCountingMeasure
        (fun k => (p.1.1 k).1) (fun k l => (p.1.1 k).2 l)) *
          ENNReal.ofReal (Real.exp (h (p.1.2 n)) * V (p.2 n)))) =
      (𝓑.prod (Measure.infinitePi fun _ : ℕ => ρ.prod σ)).map
      (fun p => ∑' n, nthLargestAtom n (poissonCountingMeasure
        (fun k => (p.1 k).1) (fun k l => (p.1 k).2 l)) *
          ENNReal.ofReal (Real.exp (h (p.2 n).1) * V (p.2 n).2)) := by
    rw [← hzip, Measure.map_map hFX hz3]
    rfl
  have e2 : (((𝓑.prod (Measure.infinitePi fun _ : ℕ => ρ)).prod
        (Measure.infinitePi fun _ : ℕ => σ)).map
      (fun p => ENNReal.ofReal (Real.exp h₀) * ∑' n, nthLargestAtom n (poissonCountingMeasure
        (fun k => (p.1.1 k).1) (fun k l => (p.1.1 k).2 l)) * ENNReal.ofReal (V (p.2 n)))) =
      ((𝓑.prod (Measure.infinitePi fun _ : ℕ => ρ.prod σ)).map
      (fun p => ∑' n, nthLargestAtom n (poissonCountingMeasure
        (fun k => (p.1 k).1) (fun k l => (p.1 k).2 l)) *
          ENNReal.ofReal (V (p.2 n).2))).map
        (fun z => ENNReal.ofReal (Real.exp h₀) * z) := by
    rw [← hzip, Measure.map_map hFV hz3, Measure.map_map hc0 (hFV.comp hz3)]
    rfl
  rw [e1, e2, hB, hA]
  have hRm : Measurable fun b : ℕ → ℕ × (ℕ → ℝ) => ENNReal.ofReal
      ((∫⁻ t, ENNReal.ofReal (V t.2) ^ ζ ∂ρ.prod σ).toReal ^ ζ⁻¹) *
        ∑' n, nthLargestAtom n (poissonCountingMeasure
          (fun k => (b k).1) (fun k l => (b k).2 l)) :=
    (Measurable.tsum fun n => (measurable_nthLargestAtom n).comp
      measurable_poissonCountingMeasure).const_mul _
  rw [Measure.map_map hc0 hRm]
  refine Measure.map_congr (Filter.Eventually.of_forall fun b => ?_)
  simp only [Function.comp_apply]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, hm1, hmV, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.mul_rpow (Real.exp_pos _).le
    ENNReal.toReal_nonneg, ← Real.exp_mul, show ζ * h₀ * ζ⁻¹ = h₀ by field_simp]

end SpinGlasses
