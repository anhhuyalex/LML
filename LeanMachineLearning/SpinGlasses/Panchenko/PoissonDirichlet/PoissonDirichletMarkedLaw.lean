/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Panchenko.PoissonDirichlet.PoissonDirichletLogSum

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

/-- **Lemma 2.2 (Panchenko).** Let `Π = {uₙ}` be a ζ-Poisson process, marked by i.i.d. `t ~ τ`
(blocks `B`, intensity `μ_ζ ⊗ τ`), and let `X` be a positive measurable function of the mark with
`E X^ζ` positive and finite. Then
`E log ∑ uₙ Xₙ = E log ∑ uₙ + (1/ζ) log E X^ζ`,
where the first sum is `∫ y dM` over the positive points of the pushforward under
`(u, t) ↦ u X t`, and the second is the same functional of any construction `B₀` of the
ζ-Poisson process. This is `identDistrib_marked_sum` composed with `log`; the logarithm of the
reference total mass is integrable and its total mass is almost surely in `(0, ∞)`. -/
theorem integral_log_marked_sum_eq
    {Ω Ω₀ T : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] [MeasurableSpace T]
    {P : Measure Ω} {Q : Measure Ω₀} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (τ : Measure T) [IsProbabilityMeasure τ]
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
    ∫ ω, Real.log (∫⁻ y in Ioi 0, ENNReal.ofReal y ∂((poissonCountingMeasure
        (fun n => (B n ω).1) (fun n l => (B n ω).2 l)).map
          (fun p : ℝ × T => p.1 * X p.2))).toReal ∂P =
      ∫ ω, Real.log (∫⁻ y in Ioi 0, ENNReal.ofReal y ∂(poissonCountingMeasure
        (fun n => (B₀ n ω).1) (fun n l => (B₀ n ω).2 l))).toReal ∂Q +
        ζ⁻¹ * Real.log (∫⁻ t, ENNReal.ofReal (X t) ^ ζ ∂τ).toReal := by
  have hid := identDistrib_marked_sum hζ0 τ hX hXpos hpos hfin ν r hBm hB hlaw hμ ν₀ r₀ hBm₀ hB₀
    hlaw₀ hμ₀
  set m : ℝ≥0∞ := ∫⁻ t, ENNReal.ofReal (X t) ^ ζ ∂τ with hm
  set c : ℝ := (m.toReal) ^ ζ⁻¹ with hc
  have hmpos : 0 < m.toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hcpos : 0 < c := Real.rpow_pos_of_pos hmpos _
  let M₀ : Ω₀ → Measure ℝ := fun ω₀ =>
    poissonCountingMeasure (fun n => (B₀ n ω₀).1) (fun n l => (B₀ n ω₀).2 l)
  have hlog := integrable_log_lintegral_of_blocks (P := Q) (M := M₀) ν₀ r₀ hζ0 hζ1 hBm₀ hB₀ hlaw₀
    hμ₀ fun _ => rfl
  have hlt := ae_lintegral_poisson_lt_top_of_blocks (P := Q) (M := M₀) ν₀ r₀ hζ0 hζ1 hBm₀ hlaw₀
    hμ₀ fun _ => rfl
  have hgt := ae_pos_of_tail (P := Q) (T := fun ω₀ => ∫⁻ y in Ioi 0, ENNReal.ofReal y ∂(M₀ ω₀))
    hζ0 fun s hs => measure_lintegral_lt_le_of_blocks (M := M₀) ν₀ r₀ hζ0 hBm₀ hB₀ hlaw₀ hμ₀
      (fun _ => rfl) hs
  have hψ : Measurable fun x : ℝ≥0∞ => Real.log x.toReal :=
    Real.measurable_log.comp ENNReal.measurable_toReal
  have hint := (hid.comp hψ).integral_eq
  have hR : ∀ᵐ ω₀ ∂Q,
      Real.log (ENNReal.ofReal c * ∫⁻ y in Ioi 0, ENNReal.ofReal y ∂(M₀ ω₀)).toReal =
      Real.log c + Real.log (∫⁻ y in Ioi 0, ENNReal.ofReal y ∂(M₀ ω₀)).toReal := by
    filter_upwards [hlt, hgt] with ω₀ h1 h2
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcpos.le,
      Real.log_mul hcpos.ne' (ENNReal.toReal_pos h2.ne' h1.ne).ne']
  simp only [Function.comp_def] at hint
  rw [hint, integral_congr_ae hR, integral_add (integrable_const _) hlog, integral_const]
  simp [hc, Real.log_rpow hmpos]
  ring

/-- The ζ-moment of a product of independent random variables, the first of them positive,
factors. -/
theorem lintegral_prod_rpow_mul {ζ : ℝ} (hζ : 0 < ζ) (τX τZ : Measure ℝ)
    [SFinite τZ] (hX : ∀ᵐ x ∂τX, 0 < x) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (p.1 * p.2) ^ ζ ∂τX.prod τZ) =
      (∫⁻ x, ENNReal.ofReal x ^ ζ ∂τX) * (∫⁻ z, ENNReal.ofReal z ^ ζ ∂τZ) := by
  rw [← lintegral_prod_mul (ENNReal.measurable_ofReal.pow_const ζ).aemeasurable
    (ENNReal.measurable_ofReal.pow_const ζ).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hX] with p hp
  rw [ENNReal.ofReal_mul hp.le, ENNReal.mul_rpow_of_nonneg _ _ hζ.le]

/-- **Equation (2.22) (Panchenko).** Let `Π = {uₙ}` be a ζ-Poisson process marked by i.i.d. pairs
`(Xₙ, Zₙ)` with independent positive coordinates (law `τX ⊗ τZ`, finite positive ζ-moments). Then
`E log ∑ uₙ Xₙ Zₙ = E log ∑ uₙ Zₙ + (1/ζ) log E X^ζ`,
where the sums are `∫ y dM` over the positive points of the pushforward of the marked
counting measure under `(u, (x, z)) ↦ u x z`, respectively `(u, (x, z)) ↦ u z`. -/
theorem integral_log_marked_sum_mul_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (τX τZ : Measure ℝ)
    [IsProbabilityMeasure τX] [IsProbabilityMeasure τZ]
    (hX : ∀ᵐ x ∂τX, 0 < x) (hZ : ∀ᵐ z ∂τZ, 0 < z)
    (hXp : 0 < ∫⁻ x, ENNReal.ofReal x ^ ζ ∂τX) (hXf : ∫⁻ x, ENNReal.ofReal x ^ ζ ∂τX < ∞)
    (hZp : 0 < ∫⁻ z, ENNReal.ofReal z ^ ζ ∂τZ) (hZf : ∫⁻ z, ENNReal.ofReal z ^ ζ ∂τZ < ∞)
    (ν : ℕ → Measure (ℝ × (ℝ × ℝ))) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × (ℝ × ℝ))} (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod (τX.prod τZ) = Measure.sum fun n => (r n : ℝ≥0∞) • ν n) :
    ∫ ω, Real.log (∫⁻ y in Ioi 0, ENNReal.ofReal y ∂((poissonCountingMeasure
        (fun n => (B n ω).1) (fun n l => (B n ω).2 l)).map
          (fun p : ℝ × (ℝ × ℝ) => p.1 * p.2.1 * p.2.2))).toReal ∂P =
      ∫ ω, Real.log (∫⁻ y in Ioi 0, ENNReal.ofReal y ∂((poissonCountingMeasure
        (fun n => (B n ω).1) (fun n l => (B n ω).2 l)).map
          (fun p : ℝ × (ℝ × ℝ) => p.1 * p.2.2))).toReal ∂P +
        ζ⁻¹ * Real.log (∫⁻ x, ENNReal.ofReal x ^ ζ ∂τX).toReal := by
  have _ : Nonempty ℝ := ⟨0⟩
  obtain ⟨ν₀, r₀, hν₀, hμ₀⟩ := exists_probabilityMeasure_sum_smul_eq_of_sigmaFinite
    (zetaPoissonMeasure ζ)
  obtain ⟨Q, hQ, hBm₀, hB₀, hlaw₀⟩ := exists_poissonBlocks ν₀ r₀
  have _ := hν₀
  have hfst := Measure.quasiMeasurePreserving_fst (μ := τX) (ν := τZ)
  have hsnd := Measure.quasiMeasurePreserving_snd (μ := τX) (ν := τZ)
  have hmul := lintegral_prod_rpow_mul hζ0 τX τZ hX
  have hmZ : ∫⁻ q : ℝ × ℝ, ENNReal.ofReal q.2 ^ ζ ∂τX.prod τZ =
      ∫⁻ z, ENNReal.ofReal z ^ ζ ∂τZ := by
    rw [lintegral_prod _ (by fun_prop : Measurable fun q : ℝ × ℝ =>
      ENNReal.ofReal q.2 ^ ζ).aemeasurable]
    simp
  -- Lemma 2.2 for the marks `x z` and for the marks `z`, with the same reference process
  have h1 := integral_log_marked_sum_eq hζ0 hζ1 (τX.prod τZ)
    (X := fun q : ℝ × ℝ => q.1 * q.2) (by fun_prop) ((hfst.ae hX).and (hsnd.ae hZ)
      |>.mono fun q hq => mul_pos hq.1 hq.2)
    (by rw [hmul]; exact ENNReal.mul_pos hXp.ne' hZp.ne')
    (by rw [hmul]; exact ENNReal.mul_lt_top hXf hZf)
    ν r hBm hB hlaw hμ ν₀ r₀ hBm₀ hB₀ hlaw₀ hμ₀
  have h2 := integral_log_marked_sum_eq hζ0 hζ1 (τX.prod τZ)
    (X := fun q : ℝ × ℝ => q.2) measurable_snd (hsnd.ae hZ)
    (by rw [hmZ]; exact hZp) (by rw [hmZ]; exact hZf)
    ν r hBm hB hlaw hμ ν₀ r₀ hBm₀ hB₀ hlaw₀ hμ₀
  rw [hmul, ENNReal.toReal_mul, Real.log_mul (ENNReal.toReal_pos hXp.ne' hXf.ne).ne'
    (ENNReal.toReal_pos hZp.ne' hZf.ne).ne'] at h1
  rw [hmZ] at h2
  have e : (fun p : ℝ × (ℝ × ℝ) => p.1 * p.2.1 * p.2.2) = fun p => p.1 * (p.2.1 * p.2.2) :=
    funext fun p => mul_assoc _ _ _
  rw [e, h1, h2]
  ring

end SpinGlasses
