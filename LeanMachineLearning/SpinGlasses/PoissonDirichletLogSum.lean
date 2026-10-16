/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletTransform

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
    calc ENNReal.ofReal s * M (Ioi s) = ∫⁻ x in Ioi s, ENNReal.ofReal s ∂M := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ x in Ioi s, ENNReal.ofReal x ∂M :=
          setLIntegral_mono' measurableSet_Ioi fun x hx =>
            ENNReal.ofReal_le_ofReal (mem_Ioi.1 hx).le
      _ ≤ ∫⁻ x in Ioi 0, ENNReal.ofReal x ∂M := lintegral_mono_set (Ioi_subset_Ioi hs.le)
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
      have hlt : (T ω).toReal < t ^ (-1 / a) := by
        have h1 : ((T ω).toReal ^ (-a)) ^ (-1 / a) < t ^ (-1 / a) :=
          Real.rpow_lt_rpow_of_neg ht hω (by
            have : 0 < 1 / a := by positivity
            have h2 : -1 / a = -(1 / a) := by ring
            rw [h2]; linarith)
        rwa [← Real.rpow_mul hz.le, show -a * (-1 / a) = 1 by field_simp, Real.rpow_one] at h1
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

/-- `|log z| ≤ (z ^ a + z ^ (-a)) / a` for `z ≥ 0`, `a > 0` (both sides vanish at `z = 0`). -/
theorem abs_log_le_rpow_add_rpow_neg {z a : ℝ} (hz : 0 ≤ z) (ha : 0 < a) :
    |Real.log z| ≤ (z ^ a + z ^ (-a)) / a := by
  rcases hz.eq_or_lt with rfl | hz0
  · simp [Real.zero_rpow ha.ne', Real.zero_rpow (neg_ne_zero.2 ha.ne')]
  have h1 : 0 ≤ z ^ a := Real.rpow_nonneg hz _
  have h2 : 0 ≤ z ^ (-a) := Real.rpow_nonneg hz _
  rcases le_total 1 z with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    exact (Real.log_le_rpow_div hz ha).trans (div_le_div_of_nonneg_right (by linarith) ha.le)
  · rw [abs_of_nonpos (Real.log_nonpos hz h), ← Real.log_inv]
    refine (Real.log_le_rpow_div (inv_nonneg.2 hz) ha).trans
      (div_le_div_of_nonneg_right ?_ ha.le)
    rw [Real.inv_rpow hz, ← Real.rpow_neg hz]
    linarith

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
  exact abs_log_le_rpow_add_rpow_neg ENNReal.toReal_nonneg ha

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

/-- The expected logarithm of the total mass `∑ x` of a Poisson process does not depend on the
block construction, only on the intensity (Equivalence Theorem 2.4). -/
theorem integral_log_lintegral_eq_of_intensity_eq {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)]
    (r : ℕ → ℝ≥0) (ν' : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν' n)] (r' : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ)} (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n) (Po(r n).prod (Measure.infinitePi fun _ : ℕ => ν n)) P)
    {B' : ℕ → Ω' → ℕ × (ℕ → ℝ)} (hBm' : ∀ n, Measurable (B' n)) (hB' : iIndepFun B' Q)
    (hlaw' : ∀ n, HasLaw (B' n) (Po(r' n).prod (Measure.infinitePi fun _ : ℕ => ν' n)) Q)
    (hμ : (Measure.sum fun n => (r n : ℝ≥0∞) • ν n) =
      Measure.sum fun n => (r' n : ℝ≥0∞) • ν' n) :
    ∫ ω, Real.log (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(poissonCountingMeasure
        (fun n => (B n ω).1) (fun n l => (B n ω).2 l))).toReal ∂P =
      ∫ ω, Real.log (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂(poissonCountingMeasure
        (fun n => (B' n ω).1) (fun n l => (B' n ω).2 l))).toReal ∂Q := by
  have hψ : Measurable fun m : Measure ℝ => Real.log (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂m).toReal :=
    Real.measurable_log.comp (ENNReal.measurable_toReal.comp
      (Measure.measurable_lintegral_restrict measurableSet_Ioi ENNReal.measurable_ofReal))
  exact ((identDistrib_poissonCountingMeasure_of_intensity_eq ν r ν' r' hBm hB hlaw hBm' hB'
    hlaw' hμ).comp hψ).integral_eq

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

/-- **Lemma 2.2 (Panchenko), with the size-biased reference process.** Let the first process
(blocks `B`) have intensity `μ_ζ ⊗ τ`, where the marks have positive first coordinate `x` with
`E X^ζ = m` positive and finite, and let the second process (blocks `B'`) have intensity
`μ_ζ ⊗ ν_ζ`, so that its first coordinates form a ζ-Poisson process. Then
`E log ∑ uₙ Xₙ = E log ∑ uₙ' + (1/ζ) log E X^ζ`,
where the sums are `∫ x dM` over the positive points of the pushforward under
`(u, (x, y)) ↦ u x`, respectively under `(u, y) ↦ u`. See `integral_log_marked_sum_eq` for the
version with an arbitrary reference construction. -/
theorem integral_log_marked_sum_eq_tilt
    {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S]
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) (τ : Measure (ℝ × S)) [IsProbabilityMeasure τ]
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
    ∫ ω, Real.log (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂((poissonCountingMeasure
        (fun n => (B n ω).1) (fun n l => (B n ω).2 l)).map
          (fun p : ℝ × (ℝ × S) => p.1 * p.2.1))).toReal ∂P =
      ∫ ω, Real.log (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂((poissonCountingMeasure
        (fun n => (B' n ω).1) (fun n l => (B' n ω).2 l)).map Prod.fst)).toReal ∂Q +
        ζ⁻¹ * Real.log (∫⁻ p, ENNReal.ofReal p.1 ^ ζ ∂τ).toReal := by
  set m : ℝ≥0∞ := ∫⁻ q, ENNReal.ofReal q.1 ^ ζ ∂τ with hm
  set c : ℝ := (m.toReal) ^ ζ⁻¹ with hc
  have hmpos : 0 < m.toReal := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hcpos : 0 < c := Real.rpow_pos_of_pos hmpos _
  have hid := identDistrib_poissonDirichlet_marked_transform hζ0 τ hτ hpos hfin ν r hBm hB hlaw
    hμ ν' r' hBm' hB' hlaw' hμ'
  -- the functional and its measurability
  let ψ : Measure (ℝ × S) → ℝ := fun μ =>
    Real.log (∫⁻ p in Prod.fst ⁻¹' Ioi 0, ENNReal.ofReal p.1 ∂μ).toReal
  have hψ : Measurable ψ :=
    Real.measurable_log.comp (ENNReal.measurable_toReal.comp
      (Measure.measurable_lintegral_restrict (measurableSet_Ioi.preimage measurable_fst)
        (ENNReal.measurable_ofReal.comp measurable_fst)))
  have hint := (hid.comp hψ).integral_eq
  -- left side
  have hL : ∀ ω, Real.log (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂((poissonCountingMeasure
        (fun n => (B n ω).1) (fun n l => (B n ω).2 l)).map
          (fun p : ℝ × (ℝ × S) => p.1 * p.2.1))).toReal =
      ψ ((poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l)).map
        (fun p : ℝ × (ℝ × S) => (p.1 * p.2.1, p.2.2))) := by
    intro ω
    simp only [ψ]
    rw [← lintegral_map_fst_Ioi, Measure.map_map measurable_fst (by fun_prop)]
    rfl
  -- the unmarked reference process: first coordinates of the second process
  have _hτ : IsProbabilityMeasure (poissonMarkTilt ζ τ) := poissonMarkTilt_isProbability hpos hfin
  have : ∀ n, IsProbabilityMeasure ((ν' n).map Prod.fst) := fun _ => inferInstance
  obtain ⟨hCm, hCi, hClaw⟩ := poissonBlocks_map hBm' hB' hlaw' (measurable_fst (β := S))
  have hμ0 := eq_sum_map_fst_of_prod_eq ν' r' hμ'
  have hM0 : ∀ ω', (poissonCountingMeasure (fun n => (B' n ω').1)
        (fun n l => (B' n ω').2 l)).map Prod.fst =
      poissonCountingMeasure (fun n => (B' n ω').1) (fun n l => ((B' n ω').2 l).1) :=
    fun ω' => poissonCountingMeasure_map _ _ measurable_fst
  have hMm0 := measurable_poissonCountingMeasure_of_blocks
    (M := fun ω' => (poissonCountingMeasure (fun n => (B' n ω').1)
        (fun n l => (B' n ω').2 l)).map Prod.fst) (B := fun n ω' => ((B' n ω').1,
          fun l => ((B' n ω').2 l).1)) hCm hM0
  have hlog := integrable_log_lintegral_of_blocks (P := Q) (M := fun ω' =>
    (poissonCountingMeasure (fun n => (B' n ω').1) (fun n l => (B' n ω').2 l)).map Prod.fst)
    (fun n => (ν' n).map Prod.fst) r' hζ0 hζ1 hCm hCi hClaw hμ0 hM0
  have hlt := ae_lintegral_poisson_lt_top (P := Q) (M := fun ω' =>
    (poissonCountingMeasure (fun n => (B' n ω').1) (fun n l => (B' n ω').2 l)).map Prod.fst)
    hζ0 hζ1 hMm0 (fun ω' => ⟨_, _, hM0 ω'⟩)
    (fun f hf => lintegral_lintegral_zeta_of_blocks (fun n => (ν' n).map Prod.fst) r' hClaw hμ0
      hM0 hf)
  have hgt := ae_pos_of_tail (P := Q) (T := fun ω' => ∫⁻ x in Ioi 0, ENNReal.ofReal x ∂
    ((poissonCountingMeasure (fun n => (B' n ω').1) (fun n l => (B' n ω').2 l)).map Prod.fst))
    hζ0 (fun s hs => measure_lintegral_lt_le_of_blocks (M := fun ω' =>
      (poissonCountingMeasure (fun n => (B' n ω').1) (fun n l => (B' n ω').2 l)).map Prod.fst)
      (fun n => (ν' n).map Prod.fst) r' hζ0 hCm hCi hClaw hμ0 hM0 hs)
  -- the scaling identity pointwise
  have hR : ∀ᵐ ω' ∂Q, ψ ((poissonCountingMeasure (fun n => (B' n ω').1)
        (fun n l => (B' n ω').2 l)).map (fun p : ℝ × S => (p.1 * c, p.2))) =
      Real.log c + Real.log (∫⁻ x in Ioi 0, ENNReal.ofReal x ∂((poissonCountingMeasure
        (fun n => (B' n ω').1) (fun n l => (B' n ω').2 l)).map Prod.fst)).toReal := by
    filter_upwards [hlt, hgt] with ω' h1 h2
    simp only [ψ]
    rw [lintegral_map_scale_fst _ hcpos, ← lintegral_map_fst_Ioi,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hcpos.le,
      Real.log_mul hcpos.ne' (ENNReal.toReal_pos h2.ne' h1.ne).ne']
  rw [integral_congr_ae (Filter.Eventually.of_forall hL)]
  refine hint.trans ?_
  have hY := integral_congr_ae (μ := Q) hR
  refine hY.trans ?_
  rw [integral_add (integrable_const _) hlog, integral_const]
  simp [hc, Real.log_rpow hmpos]
  ring

/-- **Lemma 2.2 (Panchenko).** Let `Π = {uₙ}` be a ζ-Poisson process, marked by i.i.d. `t ~ τ`
(blocks `B`, intensity `μ_ζ ⊗ τ`), and let `X` be a positive measurable function of the mark with
`E X^ζ` positive and finite. Then
`E log ∑ uₙ Xₙ = E log ∑ uₙ + (1/ζ) log E X^ζ`,
where the first sum is `∫ y dM` over the positive points of the pushforward under
`(u, t) ↦ u X t`, and the second is the same functional of any construction `B₀` of the
ζ-Poisson process (all constructions agree in law by Theorem 2.4). -/
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
  -- mark each point with its own `X`, so that `X` becomes the first mark coordinate
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
  -- a size-biased reference process, whose first coordinates form a ζ-Poisson process
  have _ : IsProbabilityMeasure (poissonMarkTilt ζ (τ.map g)) :=
    poissonMarkTilt_isProbability (hmom ▸ hpos) (hmom ▸ hfin)
  have _ : Nonempty (ℝ × T) := ⟨(0, (nonempty_of_isProbabilityMeasure τ).some)⟩
  obtain ⟨ν', r', hν', hμ'⟩ := exists_probabilityMeasure_sum_smul_eq_of_sigmaFinite
    ((zetaPoissonMeasure ζ).prod (poissonMarkTilt ζ (τ.map g)))
  obtain ⟨Q', hQ', hBm', hB', hlaw'⟩ := exists_poissonBlocks ν' r'
  have _ := hν'
  have key := integral_log_marked_sum_eq_tilt (P := P) (Q := Q') hζ0 hζ1 (τ.map g)
    (ae_map_iff hg.aemeasurable (measurableSet_Ioi.preimage measurable_fst) |>.2 hXpos)
    (hmom ▸ hpos) (hmom ▸ hfin) (fun n => (ν n).map f) r hCm hCi hClaw hμ1 ν' r' hBm' hB'
    hlaw' hμ'
  rw [hmom] at key
  -- the left sides agree because `p.1 * (f p).2.1 = p.1 * X p.2`
  have hL : ∀ ω, (poissonCountingMeasure (fun n => (B n ω).1) (fun n l => (B n ω).2 l)).map
        (fun p : ℝ × T => p.1 * X p.2) =
      (poissonCountingMeasure (fun n => ((B n ω).1)) (fun n l => f ((B n ω).2 l))).map
        (fun p : ℝ × (ℝ × T) => p.1 * p.2.1) := fun ω => by
    rw [← poissonCountingMeasure_map _ _ hf, Measure.map_map (by fun_prop) hf]
    rfl
  simp only [hL]
  rw [key]
  congr 1
  -- the reference constructions agree
  obtain ⟨hCm', hCi', hClaw'⟩ := poissonBlocks_map hBm' hB' hlaw' (measurable_fst (β := T))
  have _ : ∀ n, IsProbabilityMeasure ((ν' n).map Prod.fst) := fun _ => inferInstance
  have hR := integral_log_lintegral_eq_of_intensity_eq (fun n => (ν' n).map Prod.fst) r' ν₀ r₀
    hCm' hCi' hClaw' hBm₀ hB₀ hlaw₀ ((eq_sum_map_fst_of_prod_eq ν' r' hμ').symm.trans hμ₀)
  simpa only [poissonCountingMeasure_map _ _ (measurable_fst (β := T))] using hR

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
