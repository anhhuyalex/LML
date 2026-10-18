/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletLogSum

/-!
# The law of a marked sum of a ζ-Poisson process

Equality in law version of Lemma 2.2: if the points `uₙ` of a ζ-Poisson process are marked by
i.i.d. positive `Xₙ` with `0 < E X^ζ < ∞`, then `∑ uₙ Xₙ` has the law of
`c ∑ uₙ` with `c = (E X^ζ)^(1/ζ)`. This is the one-vertex law that Theorem 2.9 uses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SpinGlasses

variable {S : Type*} [MeasurableSpace S]

/-- The total first coordinate of the points of a measure on `ℝ × S` with positive first
coordinate, as a function of the measure. -/
theorem measurable_lintegral_fst_Ioi :
    Measurable fun μ : Measure (ℝ × S) =>
      ∫⁻ p in Prod.fst ⁻¹' Ioi 0, ENNReal.ofReal p.1 ∂μ :=
  Measure.measurable_lintegral_restrict (measurableSet_Ioi.preimage measurable_fst)
    (ENNReal.measurable_ofReal.comp measurable_fst)

/-- **Theorem 2.6 for total masses, with the size-biased reference process.** -/
theorem identDistrib_marked_sum_tilt
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ζ : ℝ} (hζ0 : 0 < ζ) (τ : Measure (ℝ × S)) [IsProbabilityMeasure τ]
    (hτ : ∀ᵐ p ∂τ, 0 < p.1) (hpos : 0 < ∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂τ)
    (hfin : ∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂τ < ∞)
    (ν : ℕ → Measure (ℝ × (ℝ × S))) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × (ℝ × S))} (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod τ = Measure.sum fun n => (r n : ℝ≥0∞) • ν n)
    (ν' : ℕ → Measure (ℝ × S)) [∀ n, IsProbabilityMeasure (ν' n)] (r' : ℕ → ℝ≥0)
    {B' : ℕ → Ω' → ℕ × (ℕ → ℝ × S)} (hBm' : ∀ n, Measurable (B' n)) (hB' : iIndepFun B' Q)
    (hlaw' : ∀ n, HasLaw (B' n) (Po(r' n).prod (Measure.infinitePi fun _ : ℕ => ν' n)) Q)
    (hμ' : (zetaPoissonMeasure ζ).prod (poissonMarkTilt ζ τ) =
      Measure.sum fun n => (r' n : ℝ≥0∞) • ν' n) :
    IdentDistrib
      (fun ω => ∫⁻ x in Ioi 0, ENNReal.ofReal x ∂((poissonCountingMeasure
        (fun n => (B n ω).1) (fun n l => (B n ω).2 l)).map
          (fun p : ℝ × (ℝ × S) => p.1 * p.2.1)))
      (fun ω' => ENNReal.ofReal ((∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂τ).toReal ^ ζ⁻¹) *
        ∫⁻ x in Ioi 0, ENNReal.ofReal x ∂((poissonCountingMeasure
          (fun n => (B' n ω').1) (fun n l => (B' n ω').2 l)).map Prod.fst)) P Q := by
  have hid := identDistrib_poissonDirichlet_marked_transform hζ0 τ hτ hpos hfin ν r hBm hB hlaw
    hμ ν' r' hBm' hB' hlaw' hμ'
  set m : ℝ≥0∞ := ∫⁻ q, ENNReal.ofReal q.1 ^ ζ ∂τ with hm
  set c : ℝ := (m.toReal) ^ ζ⁻¹ with hc
  have hmpos : 0 < m.toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hcpos : 0 < c := Real.rpow_pos_of_pos hmpos _
  have hint := hid.comp (measurable_lintegral_fst_Ioi (S := S))
  have hL : ∀ ω, ∫⁻ x in Ioi 0, ENNReal.ofReal x ∂((poissonCountingMeasure
        (fun n => (B n ω).1) (fun n l => (B n ω).2 l)).map
          (fun p : ℝ × (ℝ × S) => p.1 * p.2.1)) =
      ∫⁻ p in Prod.fst ⁻¹' Ioi 0, ENNReal.ofReal p.1 ∂((poissonCountingMeasure
        (fun n => (B n ω).1) (fun n l => (B n ω).2 l)).map
          (fun p : ℝ × (ℝ × S) => (p.1 * p.2.1, p.2.2))) := by
    intro ω
    rw [← lintegral_map_fst_Ioi, Measure.map_map measurable_fst (by fun_prop)]
    rfl
  have hR : ∀ ω', ∫⁻ p in Prod.fst ⁻¹' Ioi 0, ENNReal.ofReal p.1 ∂((poissonCountingMeasure
        (fun n => (B' n ω').1) (fun n l => (B' n ω').2 l)).map
          (fun p : ℝ × S => (p.1 * c, p.2))) =
      ENNReal.ofReal c * ∫⁻ x in Ioi 0, ENNReal.ofReal x ∂((poissonCountingMeasure
        (fun n => (B' n ω').1) (fun n l => (B' n ω').2 l)).map Prod.fst) := by
    intro ω'
    rw [lintegral_map_scale_fst _ hcpos, lintegral_map_fst_Ioi]
  simpa only [Function.comp_def, hL, hR] using hint

/-- **Theorem 2.6 for total masses.** Let `Π = {uₙ}` be a ζ-Poisson process marked by i.i.d.
`t ~ τ` (blocks `B`, intensity `μ_ζ ⊗ τ`), and `X` a positive measurable function of the mark
with `0 < E X^ζ < ∞`. Then `∑ uₙ X(tₙ)` has the law of `c ∑ uₙ'`, where `c = (E X^ζ)^(1/ζ)`
and `uₙ'` is any construction of the ζ-Poisson process. -/
theorem identDistrib_marked_sum
    {Ω Ω₀ T : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] [MeasurableSpace T]
    {P : Measure Ω} {Q : Measure Ω₀} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ζ : ℝ} (hζ0 : 0 < ζ) (τ : Measure T) [IsProbabilityMeasure τ]
    {X : T → ℝ} (hX : Measurable X) (hXpos : ∀ᵐ t ∂τ, 0 < X t)
    (hpos : 0 < ∫⁻ t, ENNReal.ofReal (X t) ^ ζ ∂τ)
    (hfin : ∫⁻ t, ENNReal.ofReal (X t) ^ ζ ∂τ < ∞)
    (ν : ℕ → Measure (ℝ × T)) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × T)} (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod τ = Measure.sum fun n => (r n : ℝ≥0∞) • ν n)
    (ν₀ : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν₀ n)] (r₀ : ℕ → ℝ≥0)
    {B₀ : ℕ → Ω₀ → ℕ × (ℕ → ℝ)} (hBm₀ : ∀ n, Measurable (B₀ n)) (hB₀ : iIndepFun B₀ Q)
    (hlaw₀ : ∀ n, HasLaw (B₀ n) (Po(r₀ n).prod (Measure.infinitePi fun _ : ℕ => ν₀ n)) Q)
    (hμ₀ : zetaPoissonMeasure ζ = Measure.sum fun n => (r₀ n : ℝ≥0∞) • ν₀ n) :
    IdentDistrib
      (fun ω => ∫⁻ y in Ioi 0, ENNReal.ofReal y ∂((poissonCountingMeasure
        (fun n => (B n ω).1) (fun n l => (B n ω).2 l)).map
          (fun p : ℝ × T => p.1 * X p.2)))
      (fun ω₀ => ENNReal.ofReal ((∫⁻ t, ENNReal.ofReal (X t) ^ ζ ∂τ).toReal ^ ζ⁻¹) *
        ∫⁻ y in Ioi 0, ENNReal.ofReal y ∂(poissonCountingMeasure
          (fun n => (B₀ n ω₀).1) (fun n l => (B₀ n ω₀).2 l))) P Q := by
  let g : T → ℝ × T := fun t => (X t, t)
  have hg : Measurable g := by fun_prop
  let f : ℝ × T → ℝ × (ℝ × T) := fun p => (p.1, g p.2)
  have hf : Measurable f := by fun_prop
  have _ : IsProbabilityMeasure (τ.map g) :=
    (Measure.isProbabilityMeasure_map_iff hg.aemeasurable).2 inferInstance
  have _ : ∀ n, IsProbabilityMeasure ((ν n).map f) := fun _ => inferInstance
  have hmom : ∫⁻ q, ENNReal.ofReal q.1 ^ ζ ∂(τ.map g) = ∫⁻ t, ENNReal.ofReal (X t) ^ ζ ∂τ :=
    lintegral_map (f := fun q : ℝ × T => ENNReal.ofReal q.1 ^ ζ) (by fun_prop) hg
  obtain ⟨hCm, hCi, hClaw⟩ := poissonBlocks_map hBm hB hlaw hf
  have hμ1 : (zetaPoissonMeasure ζ).prod (τ.map g) =
      Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).map f := by
    rw [← poissonIntensity_map ν r hf, ← hμ]
    have h := Measure.map_prod_map (zetaPoissonMeasure ζ) τ (f := id) (g := g) measurable_id hg
    rwa [Measure.map_id] at h
  have _ : IsProbabilityMeasure (poissonMarkTilt ζ (τ.map g)) :=
    poissonMarkTilt_isProbability (hmom ▸ hpos) (hmom ▸ hfin)
  have _ : Nonempty (ℝ × T) := ⟨(0, (nonempty_of_isProbabilityMeasure τ).some)⟩
  obtain ⟨ν', r', hν', hμ'⟩ := exists_probabilityMeasure_sum_smul_eq_of_sigmaFinite
    ((zetaPoissonMeasure ζ).prod (poissonMarkTilt ζ (τ.map g)))
  obtain ⟨Q', hQ', hBm', hB', hlaw'⟩ := exists_poissonBlocks ν' r'
  have _ := hν'
  have key := identDistrib_marked_sum_tilt (P := P) (Q := Q') hζ0 (τ.map g)
    (ae_map_iff hg.aemeasurable (measurableSet_Ioi.preimage measurable_fst) |>.2 hXpos)
    (hmom ▸ hpos) (hmom ▸ hfin) (fun n => (ν n).map f) r hCm hCi hClaw hμ1 ν' r' hBm' hB'
    hlaw' hμ'
  rw [hmom] at key
  have hL : ∀ ω, (poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l)).map
        (fun p : ℝ × T => p.1 * X p.2) =
      (poissonCountingMeasure (fun n => ((B n ω).1)) (fun n l => f ((B n ω).2 l))).map
        (fun p : ℝ × (ℝ × T) => p.1 * p.2.1) := fun ω => by
    rw [← poissonCountingMeasure_map _ _ hf, Measure.map_map (by fun_prop) hf]
    rfl
  simp only [hL]
  -- the reference constructions agree
  obtain ⟨hCm', hCi', hClaw'⟩ := poissonBlocks_map hBm' hB' hlaw' (measurable_fst (β := T))
  have _ : ∀ n, IsProbabilityMeasure ((ν' n).map Prod.fst) := fun _ => inferInstance
  have hR := identDistrib_poissonCountingMeasure_of_intensity_eq
    (fun n => (ν' n).map Prod.fst) r' ν₀ r₀ hCm' hCi' hClaw' hBm₀ hB₀ hlaw₀
    ((eq_sum_map_fst_of_prod_eq ν' r' hμ').symm.trans hμ₀)
  have hψ : Measurable fun m : Measure ℝ => ENNReal.ofReal
      ((∫⁻ t, ENNReal.ofReal (X t) ^ ζ ∂τ).toReal ^ ζ⁻¹) *
        ∫⁻ y in Ioi 0, ENNReal.ofReal y ∂m :=
    (Measure.measurable_lintegral_restrict measurableSet_Ioi
      ENNReal.measurable_ofReal).const_mul _
  refine key.trans ?_
  have := hR.comp hψ
  simpa only [Function.comp_def, poissonCountingMeasure_map _ _ (measurable_fst (β := T))]
    using this

end SpinGlasses
