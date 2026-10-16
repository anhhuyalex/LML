/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichlet
public import LeanMachineLearning.SpinGlasses.PoissonProcessTransform
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Transformations of the Poisson–Dirichlet intensity

The power-law intensity is homogeneous under positive dilations. This is the analytic input
for the marked Poisson-process transformation in Theorem 2.6.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SpinGlasses

/-- Multiplying all points of the `ζ`-Poisson intensity by a positive constant multiplies
its mass by the `ζ`-th power of that constant. -/
theorem zetaPoissonMeasure_map_mul {ζ c : ℝ} (hζ : 0 < ζ) (hc : 0 < c) :
    (zetaPoissonMeasure ζ).map (fun u => u * c) =
      ENNReal.ofReal (c ^ ζ) • zetaPoissonMeasure ζ := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  let d : ℝ → ℝ≥0∞ := fun u =>
    if 0 < u then ENNReal.ofReal (ζ * u ^ (-1 - ζ)) else 0
  have hd : Measurable d :=
    (ENNReal.measurable_ofReal.comp (by fun_prop)).ite measurableSet_Ioi measurable_const
  have hdi : ∀ u : ℝ, d (u * c⁻¹) * ENNReal.ofReal c⁻¹ =
      ENNReal.ofReal (c ^ ζ) * d u := by
    intro u
    by_cases hu : 0 < u
    · have hui : 0 < u * c⁻¹ := mul_pos hu (inv_pos.mpr hc)
      simp only [d, ite_eq_left hui, ite_eq_left hu]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ ζ * (u * c⁻¹) ^ (-1 - ζ)),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ c ^ ζ)]
      congr 1
      rw [Real.mul_rpow hu.le (inv_pos.mpr hc).le]
      have hp : (c⁻¹) ^ (-1 - ζ) * c⁻¹ = c ^ ζ := by
        calc
          _ = (c⁻¹) ^ (-ζ) := by
            conv_lhs => rhs; rw [← Real.rpow_one (c⁻¹)]
            rw [← Real.rpow_add (inv_pos.mpr hc)]
            congr 1
            ring
          _ = c ^ ζ := by
            rw [Real.inv_rpow hc.le, ← Real.rpow_neg hc.le]
            congr 1
            ring
      calc
        _ = ζ * u ^ (-1 - ζ) * ((c⁻¹) ^ (-1 - ζ) * c⁻¹) := by ring
        _ = _ := by rw [hp]; ring
    · have hui : ¬ 0 < u * c⁻¹ := not_lt.mpr (mul_nonpos_of_nonpos_of_nonneg
        (le_of_not_gt hu) (inv_pos.mpr hc).le)
      simp [d, hu, hui]
  ext A hA
  have hmeas : Measurable fun u : ℝ => u * c := by fun_prop
  rw [Measure.map_apply hmeas hA, Measure.smul_apply, zetaPoissonMeasure,
    withDensity_apply _ (hA.preimage hmeas), withDensity_apply _ hA]
  have heq : ∀ u : ℝ, (A.preimage (fun v => v * c)).indicator d u =
      A.indicator (fun v => d (v * c⁻¹)) (u * c) := by
    intro u
    have hi : u * c * c⁻¹ = u := by field_simp
    by_cases h : u * c ∈ A <;> simp [indicator, h, hi]
  have hmap := Real.map_volume_mul_right hc0
  have hf : Measurable (A.indicator (fun v => d (v * c⁻¹))) :=
    (hd.comp (by fun_prop)).indicator hA
  have hchange : (∫⁻ u, (A.preimage (fun v => v * c)).indicator d u ∂volume) =
      ∫⁻ v, A.indicator (fun w => d (w * c⁻¹)) v
        ∂(Measure.map (fun u : ℝ => u * c) volume) := by
    rw [lintegral_map hf hmeas]
    exact lintegral_congr heq
  rw [← lintegral_indicator (hA.preimage hmeas), ← lintegral_indicator hA]
  change (∫⁻ u, (A.preimage (fun v => v * c)).indicator d u ∂volume) =
    ENNReal.ofReal (c ^ ζ) * ∫⁻ u, A.indicator d u ∂volume
  rw [hchange, hmap, lintegral_smul_measure]
  simp only [abs_inv, abs_of_pos hc]
  change ENNReal.ofReal c⁻¹ * (∫⁻ u, A.indicator (fun v => d (v * c⁻¹)) u ∂volume) = _
  rw [← lintegral_const_mul _ (hd.indicator hA), ← lintegral_const_mul _ hf]
  apply lintegral_congr
  intro u
  by_cases hu : u ∈ A
  · simp only [indicator_of_mem hu]
    rw [mul_comm]
    exact hdi u
  · simp [indicator_of_notMem hu]

/-- The ζ-power size bias of a pair of marks `(X,Y)`, normalized to a probability
measure on the mark space. The normalizing constant is required to be positive and finite. -/
noncomputable def poissonMarkTilt {S : Type*} [MeasurableSpace S] (ζ : ℝ)
    (ν : Measure (ℝ × S)) : Measure S :=
  (∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂ν)⁻¹ •
    ((ν.withDensity fun p => ENNReal.ofReal p.1 ^ ζ).map Prod.snd)

/-- The normalized ζ-power tilt is a probability measure. -/
theorem poissonMarkTilt_isProbability {S : Type*} [MeasurableSpace S]
    {ζ : ℝ} {ν : Measure (ℝ × S)}
    (hpos : 0 < ∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂ν)
    (hfin : ∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂ν < ∞) :
    IsProbabilityMeasure (poissonMarkTilt ζ ν) := by
  constructor
  simp only [poissonMarkTilt]
  rw [Measure.smul_apply, Measure.map_apply (by fun_prop : Measurable (Prod.snd : ℝ × S → S))
    MeasurableSet.univ, Set.preimage_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  have hne : (∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂ν) ≠ ∞ := hfin.ne
  exact ENNReal.inv_mul_cancel hpos.ne' hne

/-- The tilted law evaluates a measurable set by its ζ-weighted mark mass. -/
theorem poissonMarkTilt_apply {S : Type*} [MeasurableSpace S] (ζ : ℝ)
    (ν : Measure (ℝ × S)) {A : Set S} (hA : MeasurableSet A) :
    poissonMarkTilt ζ ν A =
      (∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂ν)⁻¹ *
        ∫⁻ p in Prod.snd ⁻¹' A, ENNReal.ofReal p.1 ^ ζ ∂ν := by
  rw [poissonMarkTilt, Measure.smul_apply, Measure.map_apply (by fun_prop) hA,
    withDensity_apply _ (hA.preimage (by fun_prop))]
  rfl

/-- The transformed intensity of independently marked positive Poisson points factors into
its power-law spatial intensity and the ζ-size-biased mark measure. This version avoids
normalizing the mark law, so it also covers zero or infinite ζ-moments. -/
theorem zetaPoissonMeasure_prod_map_mul {S : Type*} [MeasurableSpace S]
    {ζ : ℝ} (hζ : 0 < ζ) (ν : Measure (ℝ × S)) [SFinite ν]
    (hν : ∀ᵐ p ∂ν, 0 < p.1) :
    ((zetaPoissonMeasure ζ).prod ν).map
        (fun p : ℝ × (ℝ × S) => (p.1 * p.2.1, p.2.2)) =
      (zetaPoissonMeasure ζ).prod
        ((ν.withDensity fun p => ENNReal.ofReal p.1 ^ ζ).map Prod.snd) := by
  let f : ℝ × S → ℝ≥0∞ := fun p => ENNReal.ofReal p.1 ^ ζ
  have hf : Measurable f := by fun_prop
  let g : ℝ × (ℝ × S) → ℝ × S := fun p => (p.1 * p.2.1, p.2.2)
  have hg : Measurable g := by fun_prop
  let τ : Measure S := (ν.withDensity f).map Prod.snd
  have hτ : ∀ A : Set S, MeasurableSet A → τ A =
      ∫⁻ p in Prod.snd ⁻¹' A, f p ∂ν := by
    intro A hA
    exact Measure.map_apply (by fun_prop) hA |>.trans
      (withDensity_apply _ (hA.preimage (by fun_prop)))
  have hs : ∀ (p : ℝ × S), 0 < p.1 →
      (zetaPoissonMeasure ζ).map (fun u => u * p.1) =
        ENNReal.ofReal (p.1 ^ ζ) • zetaPoissonMeasure ζ :=
    fun p hp => zetaPoissonMeasure_map_mul hζ hp
  ext A hA
  rw [Measure.map_apply hg hA, Measure.prod_apply hA]
  have hsection : ∀ p : ℝ × S, 0 < p.1 →
      (zetaPoissonMeasure ζ) {u | g (u, p) ∈ A} =
        ENNReal.ofReal (p.1 ^ ζ) *
          (zetaPoissonMeasure ζ) {u | (u, p.2) ∈ A} := by
    intro p hp
    have hmeas : Measurable fun u : ℝ => u * p.1 := by fun_prop
    have hsectionmeas : MeasurableSet {u : ℝ | (u, p.2) ∈ A} :=
      hA.preimage (by fun_prop)
    have := congrArg (fun m : Measure ℝ => m {u | (u, p.2) ∈ A}) (hs p hp)
    simpa only [Measure.map_apply hmeas hsectionmeas, Measure.smul_apply,
      smul_eq_mul, g, Set.mem_ofPred_eq, Set.preimage_ofPred_eq] using this
  have hleft : ((zetaPoissonMeasure ζ).prod ν) (g ⁻¹' A) =
      ∫⁻ p, (zetaPoissonMeasure ζ) {u | g (u, p) ∈ A} ∂ν :=
    Measure.prod_apply_symm (hA.preimage hg)
  rw [hleft]
  have hsections : (fun p => (zetaPoissonMeasure ζ) {u | g (u, p) ∈ A}) =ᵐ[ν]
      (fun p => f p * (zetaPoissonMeasure ζ) {u | (u, p.2) ∈ A}) := by
    filter_upwards [hν] with p hp
    simpa only [f, ENNReal.ofReal_rpow_of_pos hp] using hsection p hp
  rw [lintegral_congr_ae hsections]
  have hprod : ((zetaPoissonMeasure ζ).prod τ) A =
      ∫⁻ p, f p * (zetaPoissonMeasure ζ) {u | (u, p.2) ∈ A} ∂ν := by
    have hmeas : Measurable fun p : ℝ × S =>
        (zetaPoissonMeasure ζ) ((fun x => (x, p.2)) ⁻¹' A) :=
      (measurable_measure_prodMk_right hA).comp measurable_snd
    rw [Measure.prod_apply_symm hA, lintegral_map (measurable_measure_prodMk_right hA)
      measurable_snd, lintegral_withDensity_eq_lintegral_mul _ hf hmeas]
    rfl
  simpa only [Measure.prod_apply hA, τ, f] using hprod.symm

/-- The product intensity after transformation, expressed using the probability-valued
size-biased mark law. This is the intensity identification in Theorem 2.6; the process-law
statement additionally requires transfer of the Poisson counting-measure law. -/
theorem zetaPoissonMeasure_prod_map_mul_normalized {S : Type*} [MeasurableSpace S]
    {ζ : ℝ} (hζ : 0 < ζ) (ν : Measure (ℝ × S)) [SFinite ν]
    (hν : ∀ᵐ p ∂ν, 0 < p.1)
    (hpos : 0 < ∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂ν)
    (hfin : ∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂ν < ∞) :
    ((zetaPoissonMeasure ζ).prod ν).map
        (fun p : ℝ × (ℝ × S) => (p.1 * p.2.1, p.2.2)) =
      ((∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂ν) • zetaPoissonMeasure ζ).prod
        (poissonMarkTilt ζ ν) := by
  have _hp : IsProbabilityMeasure (poissonMarkTilt ζ ν) :=
    poissonMarkTilt_isProbability hpos hfin
  rw [zetaPoissonMeasure_prod_map_mul hζ ν hν, Measure.prod_smul_left]
  simp only [poissonMarkTilt]
  rw [Measure.prod_smul_right, smul_smul, ENNReal.mul_inv_cancel hpos.ne' hfin.ne, one_smul]

/-- **Theorem 2.6, finite-dimensional Poisson-process law.** Independent Poisson blocks
of positive points, independently marked with a joint law of `(X,Y)`, are mapped by
`(u,(x,y)) ↦ (u*x,y)`. Counts on disjoint sets of finite transformed intensity are
independent Poisson variables with the normalized size-biased intensity. -/
theorem poissonDirichlet_marked_transform
    {Ω S κ : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [Finite κ] {P : Measure Ω} [IsProbabilityMeasure P]
    {ζ : ℝ} (hζ : 0 < ζ)
    (ν : ℕ → Measure (ℝ × (ℝ × S)))
    [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    (τ : Measure (ℝ × S)) [IsProbabilityMeasure τ]
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × (ℝ × S))}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (ProbabilityTheory.poissonMeasure (r n) |>.prod
        (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod τ =
      Measure.sum fun n => (r n : ℝ≥0∞) • ν n)
    (hτ : ∀ᵐ p ∂τ, 0 < p.1)
    (hpos : 0 < ∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂τ)
    (hfin : ∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂τ < ∞)
    {A : κ → Set (ℝ × S)} (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (hfinite : ∀ i, (((∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂τ) • zetaPoissonMeasure ζ).prod
          (poissonMarkTilt ζ τ)) (A i) ≠ ∞) :
    (∀ i, HasLaw (fun ω =>
        (poissonCountingMeasure (fun n => (B n ω).1)
          (fun n l => (B n ω).2 l)).map
            (fun p : ℝ × (ℝ × S) => (p.1 * p.2.1, p.2.2)) (A i))
        ((ProbabilityTheory.poissonMeasure
          ((((∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂τ) • zetaPoissonMeasure ζ).prod
            (poissonMarkTilt ζ τ)) (A i)).toNNReal).map
          (Nat.cast : ℕ → ℝ≥0∞)) P) ∧
      iIndepFun (fun i ω =>
        (poissonCountingMeasure (fun n => (B n ω).1)
          (fun n l => (B n ω).2 l)).map
            (fun p : ℝ × (ℝ × S) => (p.1 * p.2.1, p.2.2)) (A i)) P := by
  have hmap : Measurable (fun p : ℝ × (ℝ × S) => (p.1 * p.2.1, p.2.2)) := by
    fun_prop
  have hmass : (Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).map
      (fun p : ℝ × (ℝ × S) => (p.1 * p.2.1, p.2.2))) =
      ((∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂τ) • zetaPoissonMeasure ζ).prod
        (poissonMarkTilt ζ τ) := by
    rw [← poissonIntensity_map ν r hmap, ← hμ]
    exact zetaPoissonMeasure_prod_map_mul_normalized hζ τ hτ hpos hfin
  rw [← hmass]
  exact poissonProcess_map ν r hBm hB hlaw hmap hA hdisj
    (fun i => hmass.symm ▸ hfinite i)

/-- **Theorem 2.6 (Panchenko), equality in law.** Let `μ_ζ ⊗ τ` be the intensity of a Poisson
process of points `(u, (x, y))` with positive marks `x` of finite positive ζ-moment `m = E X^ζ`.
Then the transformed process `(u, (x, y)) ↦ (u x, y)` has the same law, as a random measure, as
the process with intensity `μ_ζ ⊗ ν_ζ` whose points are scaled by `c = m^{1/ζ}`, where `ν_ζ` is the
size-biased mark law `poissonMarkTilt ζ τ`. The two processes may be built from different block
decompositions (this is where the Equivalence Theorem 2.4 is used). -/
theorem identDistrib_poissonDirichlet_marked_transform
    {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S]
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ζ : ℝ} (hζ : 0 < ζ) (τ : Measure (ℝ × S)) [IsProbabilityMeasure τ]
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
      (fun ω => (poissonCountingMeasure (fun n => (B n ω).1)
        (fun n l => (B n ω).2 l)).map (fun p : ℝ × (ℝ × S) => (p.1 * p.2.1, p.2.2)))
      (fun ω => (poissonCountingMeasure (fun n => (B' n ω).1)
        (fun n l => (B' n ω).2 l)).map
          (fun p : ℝ × S => (p.1 * (∫⁻ q, ENNReal.ofReal q.1 ^ ζ ∂τ).toReal ^ ζ⁻¹, p.2)))
      P Q := by
  set m : ℝ≥0∞ := ∫⁻ q, ENNReal.ofReal q.1 ^ ζ ∂τ with hm
  set c : ℝ := (m.toReal) ^ ζ⁻¹ with hc
  have hmpos : 0 < m.toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hcpos : 0 < c := Real.rpow_pos_of_pos hmpos _
  have hF : Measurable (fun p : ℝ × (ℝ × S) => (p.1 * p.2.1, p.2.2)) := by fun_prop
  have hG : Measurable (fun p : ℝ × S => (p.1 * c, p.2)) := by fun_prop
  have hmapF : ∀ n, IsProbabilityMeasure ((ν n).map
      (fun p : ℝ × (ℝ × S) => (p.1 * p.2.1, p.2.2))) := fun _ => inferInstance
  have hmapG : ∀ n, IsProbabilityMeasure ((ν' n).map
      (fun p : ℝ × S => (p.1 * c, p.2))) := fun _ => inferInstance
  -- the mapped blocks
  have _hτ : IsProbabilityMeasure (poissonMarkTilt ζ τ) := poissonMarkTilt_isProbability hpos hfin
  have hCi : iIndepFun (fun n ω => ((B n ω).1, fun l => (fun p : ℝ × (ℝ × S) =>
      (p.1 * p.2.1, p.2.2)) ((B n ω).2 l))) P :=
    hB.comp (fun _ b => (b.1, fun l => (fun p : ℝ × (ℝ × S) =>
      (p.1 * p.2.1, p.2.2)) (b.2 l))) (fun _ => by fun_prop)
  have hCi' : iIndepFun (fun n ω => ((B' n ω).1, fun l => (fun p : ℝ × S =>
      (p.1 * c, p.2)) ((B' n ω).2 l))) Q :=
    hB'.comp (fun _ b => (b.1, fun l => (fun p : ℝ × S => (p.1 * c, p.2)) (b.2 l)))
      (fun _ => by fun_prop)
  -- the two intensities coincide
  have hint : (Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).map
        (fun p : ℝ × (ℝ × S) => (p.1 * p.2.1, p.2.2))) =
      Measure.sum fun n => (r' n : ℝ≥0∞) • (ν' n).map (fun p : ℝ × S => (p.1 * c, p.2)) := by
    rw [← poissonIntensity_map ν r hF, ← hμ,
      zetaPoissonMeasure_prod_map_mul_normalized hζ τ hτ hpos hfin,
      ← poissonIntensity_map ν' r' hG, ← hμ']
    have hprod := Measure.map_prod_map (zetaPoissonMeasure ζ) (poissonMarkTilt ζ τ)
      (f := fun u : ℝ => u * c) (g := id) (by fun_prop) measurable_id
    have hcm : ENNReal.ofReal (c ^ ζ) = m := by
      rw [hc, Real.rpow_inv_rpow hmpos.le hζ.ne', ENNReal.ofReal_toReal hfin.ne]
    rw [show (fun p : ℝ × S => (p.1 * c, p.2)) = Prod.map (fun u : ℝ => u * c) id from rfl,
      ← hprod, Measure.map_id, zetaPoissonMeasure_map_mul hζ hcpos, hcm]
  have key := identDistrib_poissonCountingMeasure_of_intensity_eq
    (fun n => (ν n).map (fun p : ℝ × (ℝ × S) => (p.1 * p.2.1, p.2.2))) r
    (fun n => (ν' n).map (fun p : ℝ × S => (p.1 * c, p.2))) r'
    (fun n => by fun_prop) hCi (fun n => hasLaw_map_prod_infinitePi (hlaw n) hF)
    (fun n => by fun_prop) hCi' (fun n => hasLaw_map_prod_infinitePi (hlaw' n) hG) hint
  simpa only [poissonCountingMeasure_map _ _ hF, poissonCountingMeasure_map _ _ hG] using key

end SpinGlasses
