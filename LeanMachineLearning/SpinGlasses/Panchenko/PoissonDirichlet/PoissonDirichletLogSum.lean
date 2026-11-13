/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.LogRpow
public import LeanMachineLearning.SpinGlasses.Panchenko.PoissonDirichlet.PoissonDirichletTransform

/-!
# The logarithm of the total mass of the ζ-Poisson process

Integrability of `log ∑_{x ∈ Π} x`, the input of Lemma 2.2. The positive part is controlled by
Lemma 2.1 (`x ↦ log x ≤ x ^ a / a`); the negative part by a polynomial lower tail,
`ℙ(∑ x < s) ≤ s ^ ζ`, which comes from the Poisson law of the number of atoms above `s`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SpinGlasses


/-- If the total mass `∑ x` is below `s`, then no atom exceeds `s`: `M (Ioi s) < 1`. -/
theorem measure_Ioi_lt_one_of_lintegral_lt {M : Measure ℝ} {s : ℝ} (hs : 0 < s)
    (h : ∫⁻ x in Ioi 0, ENNReal.ofReal x ∂M < ENNReal.ofReal s) : M (Ioi s) < 1 := by
  by_contra hM
  push Not at hM
  have h1 : ENNReal.ofReal s * M (Ioi s) ≤ ∫⁻ x in Ioi 0, ENNReal.ofReal x ∂M := by
    refine le_trans (mul_le_mul_right ?_ _)
      (mul_meas_ge_le_lintegral (μ := M.restrict (Ioi 0)) ENNReal.measurable_ofReal
        (ENNReal.ofReal s))
    rw [Measure.restrict_apply (measurableSet_le measurable_const ENNReal.measurable_ofReal)]
    exact measure_mono fun x hx => ⟨ENNReal.ofReal_le_ofReal (mem_Ioi.1 hx).le, lt_trans hs hx⟩
  have : ENNReal.ofReal s ≤ ∫⁻ x in Ioi 0, ENNReal.ofReal x ∂M :=
    le_trans (le_mul_of_one_le_right bot_le hM) h1
  exact absurd h (not_lt.2 this)



/-- **Negative moment from a polynomial lower tail.** If `ℙ(T < s) ≤ s ^ ζ` for all `s > 0`, then
`T ^ (-ζ/2)` is integrable (with `T` read as `0` where it is infinite). -/
theorem lintegral_ofReal_toReal_rpow_neg_lt_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω → ℝ≥0∞} (hT : Measurable T) {ζ : ℝ} (hζ : 0 < ζ)
    (htail : ∀ s : ℝ, 0 < s → P {ω | T ω < ENNReal.ofReal s} ≤ ENNReal.ofReal (s ^ ζ)) :
    ∫⁻ ω, ENNReal.ofReal ((T ω).toReal ^ (-(ζ / 2))) ∂P < ∞ := by
  set a : ℝ := ζ / 2 with ha
  have ha0 : 0 < a := by positivity
  have hf : Measurable fun ω => (T ω).toReal ^ (-a) := hT.ennreal_toReal.pow_const _
  rw [lintegral_eq_lintegral_meas_lt P (Filter.Eventually.of_forall fun ω =>
    Real.rpow_nonneg ENNReal.toReal_nonneg _) hf.aemeasurable]
  -- the tail bound `ℙ(t < f) ≤ t ^ (-2)`
  have hbound : ∀ t : ℝ, 0 < t →
      P {ω | t < (T ω).toReal ^ (-a)} ≤ ENNReal.ofReal (t ^ (-2 : ℝ)) := by
    intro t ht
    have hsub : {ω | t < (T ω).toReal ^ (-a)} ⊆
        {ω | T ω < ENNReal.ofReal (t ^ (-1 / a))} := by
      intro ω hω
      have hω : t < (T ω).toReal ^ (-a) := hω
      have hz : 0 < (T ω).toReal := by
        rcases (ENNReal.toReal_nonneg (a := T ω)).eq_or_lt with h0 | h0
        · rw [← h0, Real.zero_rpow (by linarith)] at hω; linarith
        · exact h0
      have hTne : T ω ≠ ∞ := fun h => by simp [h] at hz
      have hlt : (T ω).toReal < t ^ (-1 / a) := (Real.rpow_neg_lt_iff hz ht ha0).1 hω
      change T ω < _
      rw [← ENNReal.ofReal_toReal hTne]
      exact (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos ht _)).2 hlt
    refine (measure_mono hsub).trans ((htail _ (Real.rpow_pos_of_pos ht _)).trans ?_)
    refine le_of_eq (congrArg ENNReal.ofReal ?_)
    rw [← Real.rpow_mul ht.le]
    congr 1
    rw [ha]; field_simp
  have hone : ∀ t : ℝ, P {ω | t < (T ω).toReal ^ (-a)} ≤ 1 := fun t => prob_le_one
  calc ∫⁻ t in Ioi (0 : ℝ), P {ω | t < (T ω).toReal ^ (-a)}
      ≤ (∫⁻ t in Ioc (0 : ℝ) 1, (1 : ℝ≥0∞)) +
          ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (t ^ (-2 : ℝ)) := by
        rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, lintegral_union measurableSet_Ioi
          (Ioc_disjoint_Ioi le_rfl)]
        refine add_le_add (lintegral_mono fun t => hone t) ?_
        exact setLIntegral_mono' measurableSet_Ioi fun t ht =>
          hbound t (lt_trans zero_lt_one ht)
    _ < ∞ := by
        refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
        · simp
        · exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
            zero_lt_one).lintegral_lt_top

/-- **Integrability of the logarithm of the total mass.** If `ℙ(T < s) ≤ s ^ ζ` for all `s > 0` and
`T ^ (ζ/2)` is integrable, then `log T` is integrable. -/
theorem integrable_log_toReal_of_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {T : Ω → ℝ≥0∞} (hT : Measurable T) {ζ : ℝ} (hζ : 0 < ζ)
    (htail : ∀ s : ℝ, 0 < s → P {ω | T ω < ENNReal.ofReal s} ≤ ENNReal.ofReal (s ^ ζ))
    (hpos : Integrable (fun ω => (T ω).toReal ^ (ζ / 2)) P) :
    Integrable (fun ω => Real.log (T ω).toReal) P := by
  have ha : 0 < ζ / 2 := by positivity
  have hneg : Integrable (fun ω => (T ω).toReal ^ (-(ζ / 2))) P := by
    have hf : Measurable fun ω => (T ω).toReal ^ (-(ζ / 2)) := hT.ennreal_toReal.pow_const _
    exact (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg ENNReal.toReal_nonneg _)).1
      (lintegral_ofReal_toReal_rpow_neg_lt_top hT hζ htail).ne
  refine Integrable.mono' ((hpos.add hneg).div_const (ζ / 2))
    (Real.measurable_log.comp hT.ennreal_toReal).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact Real.abs_log_le_rpow_add_rpow_neg ENNReal.toReal_nonneg ha

section BlockModel

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ζ : ℝ}
  {M : Ω → Measure ℝ} (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
  {B : ℕ → Ω → ℕ × (ℕ → ℝ)}

/-- **Lower tail of the total mass.** For the ζ-Poisson counting measure,
`ℙ(∑_{x ∈ Π} x < s) ≤ s ^ ζ`: if the total mass is below `s`, there is no atom above `s`, which has
probability `exp (-s ^ (-ζ)) ≤ s ^ ζ`. -/
theorem measure_lintegral_lt_le_of_blocks (hζ0 : 0 < ζ) (hBm : ∀ n, Measurable (B n))
    (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : zetaPoissonMeasure ζ = Measure.sum fun n => (r n : ℝ≥0∞) • ν n)
    (hM : ∀ ω, M ω = poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l))
    {s : ℝ} (hs : 0 < s) :
    P {ω | ∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(M ω) < ENNReal.ofReal s} ≤
      ENNReal.ofReal (s ^ ζ) := by
  have hfin : zetaPoissonMeasure ζ (Ioi s) ≠ ∞ := by
    rw [zetaPoissonMeasure_Ioi hζ0 hs]; exact ENNReal.ofReal_ne_top
  have hL := (iIndepFun_hasLaw_poissonCountingMeasure_apply (κ := Unit) ν r hBm hB hlaw hμ hM
    (A := fun _ => Ioi s) (fun _ => measurableSet_Ioi)
    (fun i j hij => absurd (Subsingleton.elim i j) hij)).1 ()
  simp only [hfin, ↓reduceIte] at hL
  set lam : ℝ≥0 := (zetaPoissonMeasure ζ (Ioi s)).toNNReal with hlam
  have hlamval : (lam : ℝ) = s ^ (-ζ) := by
    rw [hlam, zetaPoissonMeasure_Ioi hζ0 hs]
    exact ENNReal.toReal_ofReal (Real.rpow_nonneg hs.le _)
  have hsub : {ω | ∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(M ω) < ENNReal.ofReal s} ⊆
      {ω | M ω (Ioi s) < 1} := fun ω hω => measure_Ioi_lt_one_of_lintegral_lt hs hω
  refine (measure_mono hsub).trans ?_
  have h0 := hL.measure_eq (p := fun y : ℝ≥0∞ => y < 1) measurableSet_Iio
  have hpre : (Nat.cast : ℕ → ℝ≥0∞) ⁻¹' Iio 1 = {0} := by
    ext n; simp [Nat.cast_lt_one]
  have h1 : P {ω | M ω (Ioi s) < 1} = ENNReal.ofReal (Real.exp (-(lam : ℝ))) := by
    change P ((fun ω => M ω (Ioi s)) ⁻¹' Iio 1) = _
    rw [← Measure.map_apply_of_aemeasurable hL.aemeasurable measurableSet_Iio, hL.map_eq,
      Measure.map_apply (measurable_of_countable _) measurableSet_Iio, hpre,
      poissonMeasure_singleton]
    simp
  rw [h1]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpos : 0 < (lam : ℝ) := by rw [hlamval]; exact Real.rpow_pos_of_pos hs _
  calc Real.exp (-(lam : ℝ)) = (Real.exp (lam : ℝ))⁻¹ := Real.exp_neg _
    _ ≤ (lam : ℝ)⁻¹ := by
        apply inv_anti₀ hpos
        linarith [Real.add_one_le_exp (lam : ℝ)]
    _ = s ^ ζ := by rw [hlamval, Real.rpow_neg hs.le, inv_inv]




/-- **`log ∑_{x ∈ Π} x` is integrable** for the ζ-Poisson counting measure built from blocks. -/
theorem integrable_log_lintegral_of_blocks (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : zetaPoissonMeasure ζ = Measure.sum fun n => (r n : ℝ≥0∞) • ν n)
    (hM : ∀ ω, M ω = poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l)) :
    Integrable (fun ω => Real.log (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(M ω)).toReal) P := by
  have hMm := measurable_poissonCountingMeasure_of_blocks hBm hM
  refine integrable_log_toReal_of_tail
    ((Measure.measurable_lintegral_restrict measurableSet_Ioi ENNReal.measurable_ofReal).comp
      hMm) hζ0 (fun s hs => measure_lintegral_lt_le_of_blocks ν r hζ0 hBm hB hlaw hμ hM hs) ?_
  exact (integral_poisson_sum_rpow_le_of_blocks ν r (half_pos hζ0) (by linarith) hζ1 hBm hlaw hμ
    hM).1

end BlockModel


variable {S : Type*} [MeasurableSpace S]

/-- If `μ ⊗ ρ = ∑ rₙ νₙ` for a probability measure `ρ`, then the first coordinates of the blocks
have intensity `μ`. -/
theorem eq_sum_map_fst_of_prod_eq {μ : Measure ℝ} {ρ : Measure S} [IsProbabilityMeasure ρ]
    (ν : ℕ → Measure (ℝ × S)) (r : ℕ → ℝ≥0)
    (h : μ.prod ρ = Measure.sum fun n => (r n : ℝ≥0∞) • ν n) :
    μ = Measure.sum fun n => (r n : ℝ≥0∞) • (ν n).map Prod.fst := by
  rw [← poissonIntensity_map ν r measurable_fst, ← h, Measure.map_fst_prod, measure_univ,
    one_smul]

/-- The total first coordinate of the points of `m` lying in `{p | 0 < p.1}`. -/
theorem lintegral_map_fst_Ioi (m : Measure (ℝ × S)) :
    ∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(m.map Prod.fst) =
      ∫⁻ p in Prod.fst ⁻¹' Ioi 0, ENNReal.ofReal p.1 ∂m := by
  rw [Measure.restrict_map measurable_fst measurableSet_Ioi,
    lintegral_map ENNReal.measurable_ofReal measurable_fst]

/-- Scaling the first coordinate of all points by `c > 0` scales the total first coordinate. -/
theorem lintegral_map_scale_fst (m : Measure (ℝ × S)) {c : ℝ} (hc : 0 < c) :
    ∫⁻ p in Prod.fst ⁻¹' Ioi 0, ENNReal.ofReal p.1 ∂(m.map fun p : ℝ × S => (p.1 * c, p.2)) =
      ENNReal.ofReal c * ∫⁻ p in Prod.fst ⁻¹' Ioi 0, ENNReal.ofReal p.1 ∂m := by
  have hG : Measurable fun p : ℝ × S => (p.1 * c, p.2) := by fun_prop
  have hpre : (fun p : ℝ × S => (p.1 * c, p.2)) ⁻¹' (Prod.fst ⁻¹' Ioi 0) =
      Prod.fst ⁻¹' Ioi 0 := by
    ext p; simp [mul_pos_iff_of_pos_right hc]
  rw [Measure.restrict_map hG (measurableSet_Ioi.preimage measurable_fst),
    lintegral_map (f := fun p : ℝ × S => ENNReal.ofReal p.1) (by fun_prop) hG, hpre,
    ← lintegral_const_mul _ (by fun_prop : Measurable fun p : ℝ × S => ENNReal.ofReal p.1)]
  refine setLIntegral_congr_fun (measurableSet_Ioi.preimage measurable_fst) fun p hp => ?_
  change ENNReal.ofReal (p.1 * c) = _
  rw [ENNReal.ofReal_mul (le_of_lt hp), mul_comm]

/-- A measure of the form `ℙ(T < s) ≤ s ^ ζ` for all `s > 0` makes `T` positive almost surely. -/
theorem ae_pos_of_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : Ω → ℝ≥0∞} {ζ : ℝ}
    (hζ : 0 < ζ)
    (htail : ∀ s : ℝ, 0 < s → P {ω | T ω < ENNReal.ofReal s} ≤ ENNReal.ofReal (s ^ ζ)) :
    ∀ᵐ ω ∂P, 0 < T ω := by
  have h0 : P {ω | T ω = 0} = 0 := by
    refine le_antisymm ?_ bot_le
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have hs : 0 < (ε : ℝ) ^ ζ⁻¹ := Real.rpow_pos_of_pos (by exact_mod_cast hε) _
    have hsub : {ω | T ω = 0} ⊆ {ω | T ω < ENNReal.ofReal ((ε : ℝ) ^ ζ⁻¹)} := fun ω hω => by
      simpa [show T ω = 0 from hω] using hs
    refine (measure_mono hsub).trans ((htail _ hs).trans ?_)
    rw [Real.rpow_inv_rpow ε.coe_nonneg hζ.ne', zero_add]
    exact le_of_eq (by simp)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
  exact pos_iff_ne_zero.2 hω

/-- **Local finiteness of the marked process.** For a ζ-Poisson process with marks `ρ`, almost
surely only finitely many points have first coordinate above any level `s > 0`. -/
theorem ae_poissonCountingMeasure_Ioi_prod_univ_lt_top {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {ζ : ℝ} (hζ : 0 < ζ) (ρ : Measure S)
    [IsProbabilityMeasure ρ] (ν : ℕ → Measure (ℝ × S)) [∀ n, IsProbabilityMeasure (ν n)]
    (r : ℕ → ℝ≥0) {B : ℕ → Ω → ℕ × (ℕ → ℝ × S)} (hBm : ∀ n, Measurable (B n))
    (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod ρ = Measure.sum fun n => (r n : ℝ≥0∞) • ν n)
    {s : ℝ} (hs : 0 < s) :
    ∀ᵐ ω ∂P, poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l)
      (Ioi s ×ˢ univ) < ∞ := by
  have _ : ∀ n, IsProbabilityMeasure ((ν n).map Prod.fst) := fun _ => inferInstance
  obtain ⟨hCm, hCi, hClaw⟩ := poissonBlocks_map hBm hB hlaw (measurable_fst (β := S))
  have hμ0 := eq_sum_map_fst_of_prod_eq ν r hμ
  have hM0 := fun ω => poissonCountingMeasure_map_fst (fun n => (B n ω).1)
    (fun n l => (B n ω).2 l)
  have hMm0 := measurable_poissonCountingMeasure_of_blocks
    (M := fun ω => (poissonCountingMeasure (fun n => (B n ω).1)
        (fun n l => (B n ω).2 l)).map Prod.fst) (B := fun n ω => ((B n ω).1,
          fun l => ((B n ω).2 l).1)) hCm hM0
  have hCamp := lintegral_lintegral_zeta_of_blocks (P := P)
    (M := fun ω => (poissonCountingMeasure (fun n => (B n ω).1)
        (fun n l => (B n ω).2 l)).map Prod.fst) (fun n => (ν n).map Prod.fst) r hClaw hμ0 hM0
    (f := (Ioi s).indicator 1) (measurable_one.indicator measurableSet_Ioi)
  simp only [lintegral_indicator measurableSet_Ioi, Pi.one_apply, lintegral_one,
    Measure.restrict_apply MeasurableSet.univ, univ_inter] at hCamp
  have hfin : ∫⁻ ω, (poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l)).map
      Prod.fst (Ioi s) ∂P ≠ ∞ := by
    rw [hCamp, zetaPoissonMeasure_Ioi hζ hs]; exact ENNReal.ofReal_ne_top
  have hmeas : Measurable fun ω => (poissonCountingMeasure (fun n => (B n ω).1)
      (fun n l => (B n ω).2 l)).map Prod.fst (Ioi s) :=
    (Measure.measurable_coe measurableSet_Ioi).comp hMm0
  filter_upwards [ae_lt_top hmeas hfin] with ω hω
  rw [Measure.map_apply measurable_fst measurableSet_Ioi] at hω
  rwa [show Ioi s ×ˢ (univ : Set S) = Prod.fst ⁻¹' Ioi s by ext; simp]

/-- Almost surely every shell `{x > 1/(k+1)}` has finitely many points, simultaneously in `k`. -/
theorem ae_poissonCountingMeasure_Ioi_inv_succ_prod_univ_lt_top {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {ζ : ℝ} (hζ : 0 < ζ) (ρ : Measure S)
    [IsProbabilityMeasure ρ] (ν : ℕ → Measure (ℝ × S)) [∀ n, IsProbabilityMeasure (ν n)]
    (r : ℕ → ℝ≥0) {B : ℕ → Ω → ℕ × (ℕ → ℝ × S)} (hBm : ∀ n, Measurable (B n))
    (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    (hμ : (zetaPoissonMeasure ζ).prod ρ = Measure.sum fun n => (r n : ℝ≥0∞) • ν n) :
    ∀ᵐ ω ∂P, ∀ k : ℕ, poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l)
      (Ioi (1 / ((k : ℝ) + 1)) ×ˢ univ) < ∞ :=
  ae_all_iff.2 fun _ =>
    ae_poissonCountingMeasure_Ioi_prod_univ_lt_top hζ ρ ν r hBm hB hlaw hμ (by positivity)

end SpinGlasses
