/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.FixedPoint.Bounds

/-!
# Comparison along the cavity path (Talagrand, proof of Theorem 1.12.1)

Along the interpolation `t ∈ [0, 1]` the expectation `ν_t(f)` is continuous (also at the
endpoints, where `√t` and `√(1-t)` are not differentiable), differentiable on `(0, 1)` by
Proposition 1.12.4, and by Eq. (1.379) its derivative is controlled by `ν_t(f)` itself when
`f ≥ 0`.  This gives the comparison `ν_t(f) ≤ e^{c(1-t)} ν_1(f)` and the mean-value form
`ν_1(f) ≤ ν_0(f) + |ν_ξ'(f)|`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

/-- The Gaussian data of the cavity path (Section 1.12): jointly Gaussian centered couplings `g`,
`g'` of identity covariance and a field `Y` of covariance `β² q`, uncorrelated with the
couplings. -/
structure SKVectorCavityGaussianData {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N d : ℕ) (β
  : ℝ)
    (q : Fin d → Fin d → ℝ) (g : FinPairs N → Ω → ℝ) (g' : Fin N → Ω → ℝ)
    (Y : Fin d → Ω → ℝ) : Prop where
  hasGaussianLaw : HasGaussianLaw (fun ω (k : (FinPairs N ⊕ Fin N) ⊕ Fin d) =>
    Sum.elim (Sum.elim (fun p => g p ω) fun i => g' i ω) (fun u => Y u ω) k) P
  measurable_old_coupling : ∀ p, Measurable (g p)
  measurable_new_coupling : ∀ i, Measurable (g' i)
  measurable_field : ∀ u, Measurable (Y u)
  integral_coupling_mul_coupling : ∀ k l : FinPairs N ⊕ Fin N,
    ∫ ω, Sum.elim (fun p => g p ω) (fun i => g' i ω) k *
      Sum.elim (fun p => g p ω) (fun i => g' i ω) l ∂P = if k = l then 1 else 0
  integral_field_mul_field : ∀ u v, ∫ ω, Y u ω * Y v ω ∂P = β ^ 2 * q u v
  integral_coupling_mul_field : ∀ (k : FinPairs N ⊕ Fin N) u,
    ∫ ω, Sum.elim (fun p => g p ω) (fun i => g' i ω) k * Y u ω ∂P = 0
  integral_old_coupling : ∀ p, ∫ ω, g p ω ∂P = 0
  integral_new_coupling : ∀ i, ∫ ω, g' i ω ∂P = 0
  integral_field : ∀ u, ∫ ω, Y u ω ∂P = 0

variable {α : Type*} [MeasurableSpace α]

/-- **Continuity of `ν_t(f)` on the whole line** (in particular at the endpoints `t = 0, 1`). -/
theorem continuous_skVectorCavityAverage {d N : ℕ} {Ω R : Type*} [MeasurableSpace Ω] [Fintype R]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    (ρ q : Fin d → Fin d → ℝ) (F : (R → Fin (N + 1) → α) → ℝ) (hF : Measurable F) {M : ℝ}
    (hM : 0 ≤ M) (hFb : ∀ σ, |F σ| ≤ M) {P : Measure Ω} [IsProbabilityMeasure P]
    {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : Fin d → Ω → ℝ}
    (hn : SKVectorCavityGaussianData P N d β q g g' Y) :
    Continuous (fun s => ∫ ω, ∫ σ : R → Fin (N + 1) → α, F σ ∂(Measure.pi fun _ : R =>
        (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
          (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) s)) ∂P) := by
  set Z : (FinPairs N ⊕ Fin N) ⊕ Fin d → Ω → ℝ := fun k ω =>
    Sum.elim (Sum.elim (fun p => g p ω) fun i => g' i ω) (fun u => Y u ω) k with hZdef
  set sc : (FinPairs N ⊕ Fin N) ⊕ Fin d → ℝ → ℝ := fun k r =>
    Sum.elim (Sum.elim (fun _ => 1) fun _ => Real.sqrt r) (fun _ => Real.sqrt (1 - r)) k
    with hsc
  have hZmeas : ∀ k, Measurable (Z k) := by
    rintro ((p | i) | u)
    · exact hn.measurable_old_coupling p
    · exact hn.measurable_new_coupling i
    · exact hn.measurable_field u
  have hBnn : 0 ≤ skVectorCavityBound (Fin d) d β ρ q := by
    unfold skVectorCavityBound; positivity
  have hfe : ∀ (r' : ℝ) (ω : Ω), (fun a : Fin (N + 1) → α => (fun _ => (0 : ℝ)) a +
      ∑ k, sc k r' * Z k ω * skVectorCavityFeature ξ N β k a +
      ∑ j : Unit, (1 - r') * skVectorCavityCompensation ξ N β ρ q a) =
      skVectorCavityEnergy ξ N β ρ q (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) r' :=
    fun r' ω => funext fun a => by
      rw [skVectorCavityEnergy_eq_features]
      simp [hsc, hZdef]
  have := continuous_integral_gibbs_replica_path (μ := Measure.pi fun _ : Fin (N + 1) => μ)
    (P := P) (D := fun _ => (0 : ℝ)) (X := skVectorCavityFeature ξ N β)
    (Xs := fun _ : Unit => skVectorCavityCompensation ξ N β ρ q) (F := F) (Eb := 0)
    (B := skVectorCavityBound (Fin d) d β ρ q) (M := M) measurable_const
    (measurable_skVectorCavityFeature hξ N β)
    (fun _ => measurable_skVectorCavityCompensation hξ N β ρ q) hF hBnn hM (fun _ => by simp)
    (abs_skVectorCavityFeature_le (Nat.cast_nonneg d) hbound N β ρ q)
    (fun _ => abs_skVectorCavityCompensation_le (Nat.cast_nonneg d) hbound N β ρ q) hFb
    (Z := Z) hZmeas (s := sc) (c := fun _ r => 1 - r)
    (by
      rintro ((p | i) | u)
      · exact continuous_const
      · exact Real.continuous_sqrt
      · exact Real.continuous_sqrt.comp (continuous_const.sub continuous_id))
    (fun _ => continuous_const.sub continuous_id)
  simp only [hfe] at this
  exact this

/-- The expectation of a function of the old replicas does not depend on the extra replicas. -/
theorem skVectorCavityAverage_old {d N : ℕ} {Ω R : Type*} [MeasurableSpace Ω] [Fintype R]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    (ρ q : Fin d → Fin d → ℝ) (G : (R → Fin (N + 1) → α) → ℝ) (hG : Measurable G)
    {P : Measure Ω} {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : Fin d → Ω → ℝ} (t : ℝ) :
    skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ : Option (Option R) → Fin (N + 1) → α =>
        G fun c => σ (some (some c))) =
      ∫ ω, ∫ σ : R → Fin (N + 1) → α, G σ ∂(Measure.pi fun _ : R =>
        (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
          (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t)) ∂P := by
  unfold skVectorCavityAverage
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have := isProbabilityMeasure_tilted_skVectorCavityEnergy μ ξ hξ (Nat.cast_nonneg d) hbound N β ρ q
    (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t
  exact integral_pi_comp_injective _ (ρ := fun c : R => some (some c))
    (fun a b hab => Option.some_injective _ (Option.some_injective _ hab)) G hG.aestronglyMeasurable

/-- For `f ≥ 0` the expectation `φ(s) = ν_s(f)` is differentiable on `(0, 1)` with
`|φ'(s)| ≤ c φ(s)`, `c = 2n(2n+1)β²d²` (Proposition 1.12.4 and Eq. (1.379)). -/
theorem abs_deriv_skVectorCavityAverage_le_mul_self {d N : ℕ} {Ω R : Type*} [MeasurableSpace Ω]
  [Fintype R]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    (ρ q : Fin d → Fin d → ℝ) (hq : ∀ u v, q u v = q v u)
    (hq2 : ∑ u, ∑ v, q u v ^ 2 ≤ (d : ℝ) ^ 2) (hρ2 : ∑ u, ∑ v, ρ u v ^ 2 ≤ (d : ℝ) ^ 2)
    (F : (R → Fin (N + 1) → α) → ℝ) (hF : Measurable F) {M : ℝ} (hM : 0 ≤ M)
    (hFb : ∀ σ, |F σ| ≤ M) (hF0 : ∀ σ, 0 ≤ F σ) {P : Measure Ω} [IsProbabilityMeasure P]
    {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : Fin d → Ω → ℝ}
    (hn : SKVectorCavityGaussianData P N d β q g g' Y) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => ∫ ω, ∫ σ : R → Fin (N + 1) → α, F σ ∂(Measure.pi fun _ : R =>
        (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
          (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) s)) ∂P)
      (deriv (fun s => ∫ ω, ∫ σ : R → Fin (N + 1) → α, F σ ∂(Measure.pi fun _ : R =>
        (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
          (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) s)) ∂P) s) s ∧
    |deriv (fun s => ∫ ω, ∫ σ : R → Fin (N + 1) → α, F σ ∂(Measure.pi fun _ : R =>
        (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
          (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) s)) ∂P) s| ≤
      2 * Fintype.card R * (2 * Fintype.card R + 1) * β ^ 2 * (d : ℝ) ^ 2 *
        ∫ ω, ∫ σ : R → Fin (N + 1) → α, F σ ∂(Measure.pi fun _ : R =>
        (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
          (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) s)) ∂P := by
  have hd := hasDerivAt_skVectorCavityAverage μ ξ hξ (Nat.cast_nonneg d) hbound N β ρ q hq F hF hM
    hFb
    hn.hasGaussianLaw hn.measurable_old_coupling hn.measurable_new_coupling hn.measurable_field
      hn.integral_coupling_mul_coupling hn.integral_field_mul_field hn.integral_coupling_mul_field
      hn.integral_old_coupling
    hn.integral_new_coupling hn.integral_field hs.1 hs.2
  refine ⟨hd.differentiableAt.hasDerivAt, ?_⟩
  have hb := abs_deriv_skVectorCavityAverage_le μ ξ hξ hbound β ρ q hq hq2 hρ2 F hF hM hFb
    hn.hasGaussianLaw
    hn.measurable_old_coupling hn.measurable_new_coupling hn.measurable_field
      hn.integral_coupling_mul_coupling hn.integral_field_mul_field hn.integral_coupling_mul_field
      hn.integral_old_coupling hn.integral_new_coupling
    hn.integral_field hs.1 hs.2
  have habs : skVectorCavityAverage μ ξ N β ρ q P g g' Y s
      (fun σ : Option (Option R) → Fin (N + 1) → α => |F fun c => σ (some (some c))|) =
      ∫ ω, ∫ σ : R → Fin (N + 1) → α, F σ ∂(Measure.pi fun _ : R =>
        (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
          (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) s)) ∂P := by
    rw [← skVectorCavityAverage_old μ ξ hξ hbound β ρ q F hF s]
    congr 1
    funext σ
    exact abs_of_nonneg (hF0 _)
  rw [habs] at hb
  exact hb

/-- **The comparison `ν_t(f) ≤ e^{c(1-t)} ν_1(f)` for `f ≥ 0`** used in the proof of
Theorem 1.12.1, with `c = 2n(2n+1)β²d²` from Eq. (1.379). -/
theorem skVectorCavityAverage_le_exp_mul_endpoint {d N : ℕ} {Ω R : Type*} [MeasurableSpace Ω]
  [Fintype R]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    (ρ q : Fin d → Fin d → ℝ) (hq : ∀ u v, q u v = q v u)
    (hq2 : ∑ u, ∑ v, q u v ^ 2 ≤ (d : ℝ) ^ 2) (hρ2 : ∑ u, ∑ v, ρ u v ^ 2 ≤ (d : ℝ) ^ 2)
    (F : (R → Fin (N + 1) → α) → ℝ) (hF : Measurable F) {M : ℝ} (hM : 0 ≤ M)
    (hFb : ∀ σ, |F σ| ≤ M) (hF0 : ∀ σ, 0 ≤ F σ) {P : Measure Ω} [IsProbabilityMeasure P]
    {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : Fin d → Ω → ℝ}
    (hn : SKVectorCavityGaussianData P N d β q g g' Y) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    skVectorCavityAverage μ ξ N β ρ q P g g' Y t
        (fun σ : Option (Option R) → Fin (N + 1) → α => F fun c => σ (some (some c))) ≤
      Real.exp (2 * Fintype.card R * (2 * Fintype.card R + 1) * β ^ 2 * (d : ℝ) ^ 2 * (1 - t)) *
        skVectorCavityAverage μ ξ N β ρ q P g g' Y 1
          (fun σ : Option (Option R) → Fin (N + 1) → α => F fun c => σ (some (some c))) := by
  classical
  set c : ℝ := 2 * Fintype.card R * (2 * Fintype.card R + 1) * β ^ 2 * (d : ℝ) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  set φ : ℝ → ℝ := fun s => ∫ ω, ∫ σ : R → Fin (N + 1) → α, F σ ∂(Measure.pi fun _ : R =>
        (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
          (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) s)) ∂P with hφ
  have hold : ∀ s, skVectorCavityAverage μ ξ N β ρ q P g g' Y s
      (fun σ : Option (Option R) → Fin (N + 1) → α => F fun c => σ (some (some c))) = φ s :=
    fun s => skVectorCavityAverage_old μ ξ hξ hbound β ρ q F hF s
  rw [hold, hold]
  have hcont : Continuous φ := continuous_skVectorCavityAverage μ ξ hξ hbound β ρ q F hF hM hFb hn
  have hder : ∀ s ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt φ (deriv φ s) s ∧ -(c * φ s) ≤ deriv φ s := by
    intro s hs
    obtain ⟨h1, h2⟩ := abs_deriv_skVectorCavityAverage_le_mul_self μ ξ hξ hbound β ρ q hq hq2 hρ2
      F hF hM hFb hF0
      hn hs
    exact ⟨h1, by have := (abs_le.1 h2).1; simpa [hc] using this⟩
  -- the function `e^{cs} φ(s)` is monotone on `[0, 1]`
  set G : ℝ → ℝ := fun s => Real.exp (c * s) * φ s with hG
  have hGmono : MonotoneOn G (Set.Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hcont).continuousOn
      (fun s hs => ?_) (fun s hs => ?_)
    · rw [interior_Icc] at hs
      exact ((((hasDerivAt_id s).const_mul c).exp).mul (hder s hs).1).differentiableAt
        |>.differentiableWithinAt
    · rw [interior_Icc] at hs
      have h1 : HasDerivAt G (Real.exp (c * s) * c * φ s + Real.exp (c * s) * deriv φ s) s := by
        have h := (((hasDerivAt_id s).const_mul c).exp).mul (hder s hs).1
        exact h.congr_deriv (by simp only [id]; ring)
      rw [h1.deriv]
      have := (hder s hs).2
      nlinarith [Real.exp_pos (c * s)]
  have := hGmono ⟨ht0, ht1⟩ ⟨zero_le_one, le_rfl⟩ ht1
  simp only [hG, mul_one] at this
  have he : Real.exp (c * (1 - t)) * Real.exp (c * t) = Real.exp c := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (c * t) * φ t ≤ Real.exp c * φ 1 := this
  calc φ t = (Real.exp (c * t))⁻¹ * (Real.exp (c * t) * φ t) := by
        rw [← mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul]
    _ ≤ (Real.exp (c * t))⁻¹ * (Real.exp c * φ 1) :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 (Real.exp_pos _).le)
    _ = Real.exp (c * (1 - t)) * φ 1 := by
        rw [← he]; field_simp

/-- **The endpoint inequality of the smart path**: for `f ≥ 0`,
`ν_1(f) ≤ ν_0(f) + c e^{c} ν_1(f)` with `c = 2n(2n+1)β²d²` (the integrated form of Eq. (1.379),
via the mean value theorem and the comparison `ν_ξ(f) ≤ e^{c} ν_1(f)`). -/
theorem skVectorCavityAverage_one_le_zero_add {d N : ℕ} {Ω R : Type*} [MeasurableSpace Ω] [Fintype
  R]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    (ρ q : Fin d → Fin d → ℝ) (hq : ∀ u v, q u v = q v u)
    (hq2 : ∑ u, ∑ v, q u v ^ 2 ≤ (d : ℝ) ^ 2) (hρ2 : ∑ u, ∑ v, ρ u v ^ 2 ≤ (d : ℝ) ^ 2)
    (F : (R → Fin (N + 1) → α) → ℝ) (hF : Measurable F) {M : ℝ} (hM : 0 ≤ M)
    (hFb : ∀ σ, |F σ| ≤ M) (hF0 : ∀ σ, 0 ≤ F σ) {P : Measure Ω} [IsProbabilityMeasure P]
    {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : Fin d → Ω → ℝ}
    (hn : SKVectorCavityGaussianData P N d β q g g' Y) :
    skVectorCavityAverage μ ξ N β ρ q P g g' Y 1
        (fun σ : Option (Option R) → Fin (N + 1) → α => F fun c => σ (some (some c))) ≤
      skVectorCavityAverage μ ξ N β ρ q P g g' Y 0
        (fun σ : Option (Option R) → Fin (N + 1) → α => F fun c => σ (some (some c))) +
      2 * Fintype.card R * (2 * Fintype.card R + 1) * β ^ 2 * (d : ℝ) ^ 2 *
        Real.exp (2 * Fintype.card R * (2 * Fintype.card R + 1) * β ^ 2 * (d : ℝ) ^ 2) *
        skVectorCavityAverage μ ξ N β ρ q P g g' Y 1
          (fun σ : Option (Option R) → Fin (N + 1) → α => F fun c => σ (some (some c))) := by
  classical
  set c : ℝ := 2 * Fintype.card R * (2 * Fintype.card R + 1) * β ^ 2 * (d : ℝ) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  set φ : ℝ → ℝ := fun s => ∫ ω, ∫ σ : R → Fin (N + 1) → α, F σ ∂(Measure.pi fun _ : R =>
        (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
          (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) s)) ∂P with hφ
  have hold : ∀ s, skVectorCavityAverage μ ξ N β ρ q P g g' Y s
      (fun σ : Option (Option R) → Fin (N + 1) → α => F fun c => σ (some (some c))) = φ s :=
    fun s => skVectorCavityAverage_old μ ξ hξ hbound β ρ q F hF s
  rw [hold, hold]
  have hcont : Continuous φ := continuous_skVectorCavityAverage μ ξ hξ hbound β ρ q F hF hM hFb hn
  have hφ0 : ∀ s, 0 ≤ φ s := fun s => by
    rw [← hold s]
    exact skVectorCavityAverage_nonneg μ ξ _ β ρ q s _ fun σ => hF0 _
  obtain ⟨x, hx, hxd⟩ := exists_deriv_eq_slope φ zero_lt_one hcont.continuousOn
    (fun s hs => (abs_deriv_skVectorCavityAverage_le_mul_self μ ξ hξ hbound β ρ q hq hq2 hρ2 F hF
      hM hFb hF0 hn
      hs).1.differentiableAt.differentiableWithinAt)
  obtain ⟨-, hxb⟩ := abs_deriv_skVectorCavityAverage_le_mul_self μ ξ hξ hbound β ρ q hq hq2 hρ2 F
    hF hM hFb hF0 hn hx
  have hcmp := skVectorCavityAverage_le_exp_mul_endpoint μ ξ hξ hbound β ρ q hq hq2 hρ2 F hF hM
    hFb hF0 hn
    hx.1.le hx.2.le
  rw [hold, hold] at hcmp
  have hslope : φ 1 - φ 0 = deriv φ x := by
    rw [hxd]; simp
  have h1 : Real.exp (c * (1 - x)) ≤ Real.exp c :=
    Real.exp_le_exp.2 (by nlinarith [hx.1])
  calc φ 1 = φ 0 + (φ 1 - φ 0) := by ring
    _ ≤ φ 0 + c * φ x := by
        rw [hslope]; linarith [le_abs_self (deriv φ x)]
    _ ≤ φ 0 + c * (Real.exp (c * (1 - x)) * φ 1) := by
        gcongr
    _ ≤ φ 0 + c * (Real.exp c * φ 1) := by
        gcongr
        exact hφ0 1
    _ = φ 0 + c * Real.exp c * φ 1 := by ring

end SpinGlasses
