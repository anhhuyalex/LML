/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletInvariance

/-!
# Gaussian Bolthausen--Sznitman invariance with an extra independent mark

The Gaussian transformation of the ζ-Poisson process (Eq. (2.85) of the book) keeps its law
when each point carries, besides its Gaussian label, a further independent mark of arbitrary law
`κ`. This is the root step of the Bolthausen--Sznitman invariance of the Ruelle probability cascade.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SpinGlasses

variable {S : Type*} [MeasurableSpace S]

/-- The size-biased law of the transformed marks `(exp (t (η - tζ/2)), (η - tζ, V))`, for an
independent pair `(η, V) ~ N(0,1) ⊗ κ`, is `N(0,1) ⊗ κ` again. -/
theorem poissonMarkTilt_gaussian_prod (ζ t : ℝ) (κ : Measure S) [IsProbabilityMeasure κ] :
    poissonMarkTilt ζ (((gaussianReal 0 1).prod κ).map
      (fun m : ℝ × S => (Real.exp (t * (m.1 - t * ζ / 2)), (m.1 - t * ζ, m.2)))) =
        (gaussianReal 0 1).prod κ := by
  set G := gaussianReal 0 1 with hG
  let f : ℝ → ℝ × ℝ := fun g => (Real.exp (t * (g - t * ζ / 2)), g - t * ζ)
  have hf : Measurable f := by fun_prop
  let Ψ : ℝ × S → ℝ × (ℝ × S) := fun m => (Real.exp (t * (m.1 - t * ζ / 2)), (m.1 - t * ζ, m.2))
  have hΨ : Measurable Ψ := by fun_prop
  have hmult : (∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂(G.prod κ).map Ψ) = 1 := by
    rw [lintegral_map (by fun_prop) hΨ]
    change ∫⁻ m, ENNReal.ofReal (Real.exp (t * (m.1 - t * ζ / 2))) ^ ζ ∂G.prod κ = 1
    rw [lintegral_prod _ (by fun_prop : Measurable fun m : ℝ × S =>
      ENNReal.ofReal (Real.exp (t * (m.1 - t * ζ / 2))) ^ ζ).aemeasurable]
    simp only [lintegral_const, measure_univ, mul_one]
    exact lintegral_gaussian_multiplier ζ t
  have hm1 : (∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂G.map f) = 1 := by
    rw [lintegral_map (by fun_prop) hf]
    exact lintegral_gaussian_multiplier ζ t
  -- the one-dimensional identity of Lemma 2.3, for a measurable set `B` of shifted labels
  have hGB : ∀ B : Set ℝ, MeasurableSet B →
      ∫⁻ η, B.indicator (fun _ => (1 : ℝ≥0∞)) (η - t * ζ) *
        ENNReal.ofReal (Real.exp (t * (η - t * ζ / 2))) ^ ζ ∂G = G B := by
    intro B hB
    have h := congrArg (fun m => m B) (poissonMarkTilt_gaussian ζ t)
    rw [poissonMarkTilt_apply ζ _ hB, hm1, inv_one, one_mul,
      ← lintegral_indicator (hB.preimage measurable_snd),
      lintegral_map ((by fun_prop : Measurable fun p : ℝ × ℝ => ENNReal.ofReal p.1 ^ ζ).indicator
        (hB.preimage measurable_snd)) hf] at h
    rw [← h]
    refine lintegral_congr fun η => ?_
    by_cases hη : η - t * ζ ∈ B
    · simp [Set.indicator, hη, f]
    · simp [Set.indicator, hη, f]
  ext A hA
  rw [poissonMarkTilt_apply ζ _ hA, hmult, inv_one, one_mul,
    ← lintegral_indicator (hA.preimage measurable_snd),
    lintegral_map ((by fun_prop : Measurable fun p : ℝ × ℝ × S => ENNReal.ofReal p.1 ^ ζ).indicator
      (hA.preimage measurable_snd)) hΨ]
  have hint : ∀ m : ℝ × S, (Prod.snd ⁻¹' A).indicator
      (fun p : ℝ × ℝ × S => ENNReal.ofReal p.1 ^ ζ) (Ψ m) =
      Set.indicator {y : ℝ | (y, m.2) ∈ A} (fun _ => (1 : ℝ≥0∞)) (m.1 - t * ζ) *
        ENNReal.ofReal (Real.exp (t * (m.1 - t * ζ / 2))) ^ ζ := by
    intro m
    by_cases hm : (m.1 - t * ζ, m.2) ∈ A
    · simp [Set.indicator, hm, Ψ]
    · simp [Set.indicator, hm, Ψ]
  simp_rw [hint]
  rw [Measure.prod_apply_symm hA, lintegral_prod_symm]
  · refine lintegral_congr fun V => ?_
    exact hGB {y : ℝ | (y, V) ∈ A} (measurable_prodMk_right (y := V) hA)
  · have hm : Measurable fun m : ℝ × S => (Prod.snd ⁻¹' A).indicator
        (fun p : ℝ × ℝ × S => ENNReal.ofReal p.1 ^ ζ) (Ψ m) :=
      ((by fun_prop : Measurable fun p : ℝ × ℝ × S => ENNReal.ofReal p.1 ^ ζ).indicator
        (hA.preimage measurable_snd)).comp hΨ
    simp_rw [hint] at hm
    exact hm.aemeasurable

/-- **Gaussian Bolthausen--Sznitman invariance with an extra mark.** The Poisson process of points
`(u, (x, (η', V)))` with intensity `μ_ζ ⊗ τ`, where `τ` is the law of the transformed mark of
`(η, V) ~ N(0,1) ⊗ κ`, becomes after the rescaling `(u, (x, y)) ↦ (u x, y)` a Poisson process of
points `(u', (η, V))` with intensity `μ_ζ ⊗ (N(0,1) ⊗ κ)`: the retained marks are again
distributed as `(η, V)`. -/
theorem identDistrib_poissonDirichlet_gaussian_marked_transform
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ζ : ℝ} (hζ : 0 < ζ) (t : ℝ) (κ : Measure S) [IsProbabilityMeasure κ]
    (ν : ℕ → Measure (ℝ × (ℝ × (ℝ × S)))) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × (ℝ × (ℝ × S)))}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod (((gaussianReal 0 1).prod κ).map
        (fun m : ℝ × S => (Real.exp (t * (m.1 - t * ζ / 2)), (m.1 - t * ζ, m.2)))) =
      Measure.sum (fun n => (r n : ENNReal) • ν n))
    (ν' : ℕ → Measure (ℝ × (ℝ × S))) [∀ n, IsProbabilityMeasure (ν' n)] (r' : ℕ → ℝ≥0)
    {B' : ℕ → Ω' → ℕ × (ℕ → ℝ × (ℝ × S))}
    (hBm' : ∀ n, Measurable (B' n)) (hB' : iIndepFun B' Q)
    (hlaw' : ∀ n, HasLaw (B' n) (Po(r' n).prod
      (Measure.infinitePi fun _ : ℕ => ν' n)) Q)
    (hμ' : (zetaPoissonMeasure ζ).prod ((gaussianReal 0 1).prod κ) =
      Measure.sum (fun n => (r' n : ENNReal) • ν' n)) :
    IdentDistrib
      (fun ω => (poissonCountingMeasure (fun n => (B n ω).1)
        (fun n l => (B n ω).2 l)).map
          (fun p : ℝ × (ℝ × (ℝ × S)) => (p.1 * p.2.1, p.2.2)))
      (fun ω => poissonCountingMeasure (fun n => (B' n ω).1)
        (fun n l => (B' n ω).2 l)) P Q := by
  let Ψ : ℝ × S → ℝ × (ℝ × S) := fun m => (Real.exp (t * (m.1 - t * ζ / 2)), (m.1 - t * ζ, m.2))
  have hΨ : Measurable Ψ := by fun_prop
  let τ : Measure (ℝ × (ℝ × S)) := ((gaussianReal 0 1).prod κ).map Ψ
  have hτprob : IsProbabilityMeasure τ := inferInstance
  have hτ : ∀ᵐ p ∂τ, 0 < p.1 := by
    apply (ae_map_iff hΨ.aemeasurable (measurableSet_lt measurable_const measurable_fst)).2
    exact Filter.Eventually.of_forall (fun m => Real.exp_pos _)
  have hm : (∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂τ) = 1 := by
    rw [lintegral_map (by fun_prop) hΨ]
    change ∫⁻ m, ENNReal.ofReal (Real.exp (t * (m.1 - t * ζ / 2))) ^ ζ
      ∂(gaussianReal 0 1).prod κ = 1
    rw [lintegral_prod _ (by fun_prop : Measurable fun m : ℝ × S =>
      ENNReal.ofReal (Real.exp (t * (m.1 - t * ζ / 2))) ^ ζ).aemeasurable]
    simp only [lintegral_const, measure_univ, mul_one]
    exact lintegral_gaussian_multiplier ζ t
  have htilt : poissonMarkTilt ζ τ = (gaussianReal 0 1).prod κ :=
    poissonMarkTilt_gaussian_prod ζ t κ
  have hid := identDistrib_poissonDirichlet_marked_transform hζ τ hτ
    (hm ▸ zero_lt_one) (hm ▸ ENNReal.one_lt_top) ν r hBm hB hlaw hμ
    ν' r' hBm' hB' hlaw' (htilt ▸ hμ')
  have hscale : (1 : ℝ) ^ ζ⁻¹ = 1 := by simp
  simp only [hm, ENNReal.toReal_one, hscale, mul_one] at hid
  convert hid using 1
  funext ω
  simp

end SpinGlasses
