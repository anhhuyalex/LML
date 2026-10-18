/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeGibbsReal
public import LeanMachineLearning.SpinGlasses.CascadeGaussianField
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.SignedToReal
public import LeanMachineLearning.ForMathlib.Probability.Independence.IntegralIndepFun
public import LeanMachineLearning.ForMathlib.Probability.Independence.IndepFstSndInfinitePi
public import LeanMachineLearning.ForMathlib.Data.Finset.SumBound

/-!
# Ghirlanda--Guerra identities for the Ruelle cascade

Real-valued forms of the Bolthausen--Sznitman invariance (Lemma 2.5 of Panchenko) and, from them
and Gaussian integration by parts, the Ghirlanda--Guerra identities of the cascade.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SpinGlasses

section Setting

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (r : ℕ) (ζ σ : ℕ → ℝ) (nu : (p : ℕ) → ℕ → Measure ℝ) [∀ p k, IsProbabilityMeasure (nu p k)]
  (rate : (p : ℕ) → ℕ → ℝ≥0)
  (𝔡 : ℕ → Measure ((ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ)))
  (D : (Σ p : ℕ, Fin p → ℕ) → Ω → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℝ))
  (u : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ≥0∞)
  (lab : Ω → (p : ℕ) → (Fin p → ℕ) → ℕ → ℝ)

/-- The Gibbs average of a pattern observable is a measurable function of the vertex data. -/
theorem measurable_replicaGibbs_omega (hDm : ∀ v, Measurable (D v))
    (hu : u = fun ω p γ m => nthLargestAtom m (poissonCountingMeasure
      (fun k => ((D ⟨p, γ⟩ ω).1 k).1) (fun k l => ((D ⟨p, γ⟩ ω).1 k).2 l)))
    (hlab : lab = fun ω p γ k => (D ⟨p, γ⟩ ω).2 k) (n : ℕ) (t : ℝ)
    (F : (Fin n → Fin n → Fin (r + 1)) → ℝ≥0∞) :
    Measurable fun ω => replicaGibbs r n σ t F (u ω) (lab ω) := by
  have hDvec : Measurable fun ω (v : Σ p : ℕ, Fin p → ℕ) => D v ω := measurable_pi_iff.2 hDm
  have hrs : ∀ P : Fin n → Fin n → Fin (r + 1), Measurable fun ω => cascadeReplicaSum r
      (fun l l' => (P l l').val) (fun l i => tiltTest (t * σ i) 0 (fun _ => 1))
      (fun v => D v ω) := by
    intro P
    have hcr := measurable_cascadeReplicaSum r (ι := Fin n) (fun l l' => ((P l l').val : ℕ))
      (fun l i => tiltTest (t * σ i) 0 (fun _ => 1))
      (fun l i => measurable_tiltTest _ _ measurable_const)
    have h := hcr.comp hDvec
    exact h
  have e : ∀ ω, replicaGibbs r n σ t F (u ω) (lab ω) =
      (∑ P : Fin n → Fin n → Fin (r + 1), F P * cascadeReplicaSum r (fun l l' => (P l l').val)
        (fun l i => tiltTest (t * σ i) 0 (fun _ => 1)) (fun v => D v ω)) /
      ∑ P : Fin n → Fin n → Fin (r + 1), cascadeReplicaSum r (fun l l' => (P l l').val)
        (fun l i => tiltTest (t * σ i) 0 (fun _ => 1)) (fun v => D v ω) := fun ω => by
    subst hu hlab
    rw [replicaGibbs_eq_div r n σ (fun _ => 0) t F]
    rfl
  simp_rw [e]
  exact (Finset.measurable_sum _ fun P _ => (hrs P).const_mul _).mul
    (Finset.measurable_sum _ fun P _ => hrs P).inv

/-- **The tilted total mass is almost surely positive and finite.** The total mass
`∑_α w_α exp (t g(α))` has, up to the constant `exp (-t²/2 ∑ σᵢ² ζᵢ)`, the law of the untilted
total mass (Bolthausen--Sznitman invariance of the replica sums for one replica). -/
theorem ae_tiltedMass_pos_finite (hζ0 : ∀ p, 0 < ζ p) (hζ1 : ∀ p, ζ p < 1)
    (hmono : StrictMono ζ)
    (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
    (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
    (hDm : ∀ v, Measurable (D v)) (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
    (hu : u = fun ω p γ m => nthLargestAtom m (poissonCountingMeasure
      (fun k => ((D ⟨p, γ⟩ ω).1 k).1) (fun k l => ((D ⟨p, γ⟩ ω).1 k).2 l)))
    (hlab : lab = fun ω p γ k => (D ⟨p, γ⟩ ω).2 k) (t : ℝ) :
    ∀ᵐ ω ∂P, (∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α *
        ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) α i))) ≠ 0 ∧
      (∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α *
        ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) α i))) ≠ ∞ := by
  have h := identDistrib_cascadeReplicaSum_tilt (P := P) r ζ σ t hζ0 hζ1 nu rate hmu 𝔡 h𝔡 D hDm
    hD hDlaw (X := Fin 1 → Fin 1 → Fin (r + 1)) (fun _ => Fin 1) (fun P l l' => (P l l').val)
    (fun _ _ _ => fun _ => 1) fun _ _ _ => measurable_const
  have hΨm : Measurable fun z : (Fin 1 → Fin 1 → Fin (r + 1)) → ℝ≥0∞ => ∑ P, z P :=
    Finset.measurable_sum _ fun P _ => measurable_pi_apply P
  have h2 := h.comp hΨm
  have key : ∀ (ω : Ω) (t' : ℝ), ∑ P : Fin 1 → Fin 1 → Fin (r + 1), cascadeReplicaSum r
      (fun l l' => (P l l').val) (fun l i => tiltTest (t' * σ i) (ζ i) (fun _ => 1))
      (fun v => D v ω) = ENNReal.ofReal (Real.exp (-(t' ^ 2 / 2 * ∑ i : Fin r, σ i ^ 2 * ζ i))) *
      ∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α *
        ENNReal.ofReal (Real.exp (t' * ∑ i : Fin r, σ i * leafLabel (lab ω) α i)) := by
    intro ω t'
    have e := sum_replicaSum_tilt_pattern r 1 σ ζ t' (fun _ _ _ => 1) (u ω) (lab ω) (fun _ => 1)
    simp only [one_mul, Finset.prod_const_one, mul_one, pow_one] at e
    rw [ENNReal.tsum_pi_prod fun _ α => cascadeBranchWeight (u ω) α *
      ENNReal.ofReal (Real.exp (t' * ∑ i : Fin r, σ i * leafLabel (lab ω) α i))] at e
    simp only [Finset.univ_unique, Finset.prod_singleton] at e
    subst hu hlab
    exact e
  have key0 : ∀ ω, ∑ P : Fin 1 → Fin 1 → Fin (r + 1), cascadeReplicaSum r
      (fun l l' => (P l l').val) (fun l i => fun _ => (1 : ℝ≥0∞)) (fun v => D v ω) =
      ∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α := fun ω => by
    have := key ω 0
    simp only [zero_mul, tiltTest_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one, one_mul,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_div] at this
    exact this
  have hc0 : ENNReal.ofReal (Real.exp (-(t ^ 2 / 2 * ∑ i : Fin r, σ i ^ 2 * ζ i))) ≠ 0 := by
    simp [Real.exp_pos]
  have hct : ENNReal.ofReal (Real.exp (-(t ^ 2 / 2 * ∑ i : Fin r, σ i ^ 2 * ζ i))) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have hae := ae_cascadeMass_pos_finite (P := P) r ζ hζ0 hζ1 hmono nu rate hmu 𝔡 h𝔡 D hDm hD
    hDlaw
  have hident : IdentDistrib (fun ω => ENNReal.ofReal (Real.exp (-(t ^ 2 / 2 *
      ∑ i : Fin r, σ i ^ 2 * ζ i))) * ∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α *
        ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) α i)))
      (fun ω => ∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α) P P := by
    have h3 : IdentDistrib (fun ω => ∑ P : Fin 1 → Fin 1 → Fin (r + 1), cascadeReplicaSum r
        (fun l l' => (P l l').val) (fun l i => tiltTest (t * σ i) (ζ i) (fun _ => 1))
        (fun v => D v ω)) (fun ω => ∑ P : Fin 1 → Fin 1 → Fin (r + 1), cascadeReplicaSum r
        (fun l l' => (P l l').val) (fun l i => fun _ => (1 : ℝ≥0∞)) (fun v => D v ω)) P P := h2
    simp_rw [key, key0] at h3
    exact h3
  have hnull : ∀ x : ℝ≥0∞, (∀ᵐ ω ∂P, ∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α ≠ x) →
      ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp (-(t ^ 2 / 2 * ∑ i : Fin r, σ i ^ 2 * ζ i))) *
        ∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α *
        ENNReal.ofReal (Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) α i)) ≠ x :=
    fun x hx => hident.symm.ae_snd (measurableSet_singleton x).compl hx
  have hae' : (∀ᵐ ω ∂P, ∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α ≠ 0) ∧
      ∀ᵐ ω ∂P, ∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α ≠ ∞ := by
    subst hu hlab
    exact ⟨hae.mono fun ω h => h.1, hae.mono fun ω h => h.2.ne⟩
  filter_upwards [hnull 0 hae'.1, hnull ∞ hae'.2] with ω h0 h1
  refine ⟨fun h => h0 (by rw [h, mul_zero]), fun h => h1 (by rw [h, ENNReal.mul_top hc0])⟩

/-- The total mass of the cascade is almost surely positive and finite, in terms of the atoms
`u ω`. -/
theorem ae_cascadeMass_pos_finite_omega (hζ0 : ∀ p, 0 < ζ p) (hζ1 : ∀ p, ζ p < 1)
    (hmono : StrictMono ζ)
    (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
    (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
    (hDm : ∀ v, Measurable (D v)) (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
    (hu : u = fun ω p γ m => nthLargestAtom m (poissonCountingMeasure
      (fun k => ((D ⟨p, γ⟩ ω).1 k).1) (fun k l => ((D ⟨p, γ⟩ ω).1 k).2 l))) :
    ∀ᵐ ω ∂P, (∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α) ≠ 0 ∧
      (∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α) < ∞ := by
  subst hu
  exact ae_cascadeMass_pos_finite (P := P) r ζ hζ0 hζ1 hmono nu rate hmu 𝔡 h𝔡 D hDm hD hDlaw

/-- The expected Gibbs series of a bounded pattern observable through the positive and negative
parts of the observable. -/
theorem integral_cascadeSeries_eq (hζ0 : ∀ p, 0 < ζ p) (hζ1 : ∀ p, ζ p < 1)
    (hmono : StrictMono ζ)
    (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
    (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
    (hDm : ∀ v, Measurable (D v)) (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
    (hu : u = fun ω p γ m => nthLargestAtom m (poissonCountingMeasure
      (fun k => ((D ⟨p, γ⟩ ω).1 k).1) (fun k l => ((D ⟨p, γ⟩ ω).1 k).2 l)))
    (hlab : lab = fun ω p γ k => (D ⟨p, γ⟩ ω).2 k) (n : ℕ) (t : ℝ)
    (Ξ : (Fin n → Fin n → Fin (r + 1)) → ℝ) {M : ℝ} (hΞ : ∀ P, |Ξ P| ≤ M) :
    ∫ ω, ∑' τ : Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        Ξ (fun l l' => prefixOverlap (τ l) (τ l')) ∂P =
      (∫⁻ ω, replicaGibbs r n σ t (fun P => ENNReal.ofReal (Ξ P)) (u ω) (lab ω) ∂P).toReal -
        (∫⁻ ω, replicaGibbs r n σ t (fun P => ENNReal.ofReal (-Ξ P)) (u ω) (lab ω) ∂P).toReal := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hΞ fun _ _ => 0)
  have h0 := ae_cascadeMass_pos_finite_omega r ζ nu rate 𝔡 D u hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu
  have ht := ae_tiltedMass_pos_finite (P := P) r ζ σ nu rate 𝔡 D u lab hζ0 hζ1 hmono hmu h𝔡 hDm hD
    hDlaw hu hlab t
  have hle : ∀ (F : (Fin n → Fin n → Fin (r + 1)) → ℝ≥0∞), (∀ P, F P ≤ ENNReal.ofReal M) →
      ∀ᵐ ω ∂P, replicaGibbs r n σ t F (u ω) (lab ω) ≤ ENNReal.ofReal M := fun F hF =>
    ht.mono fun ω h => replicaGibbs_le r n σ t F _ hF _ _ h.1 h.2
  have hint : ∀ (F : (Fin n → Fin n → Fin (r + 1)) → ℝ≥0∞), (∀ P, F P ≤ ENNReal.ofReal M) →
      Integrable (fun ω => (replicaGibbs r n σ t F (u ω) (lab ω)).toReal) P := fun F hF => by
    refine integrable_toReal_of_lintegral_ne_top
      (measurable_replicaGibbs_omega r σ D u lab hDm hu hlab n t F).aemeasurable ?_
    refine ne_top_of_le_ne_top (b := ∫⁻ _, ENNReal.ofReal M ∂P) (by simp)
      (lintegral_mono_ae (hle F hF))
  have hFp : ∀ P, ENNReal.ofReal (Ξ P) ≤ ENNReal.ofReal M := fun P =>
    ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hΞ P))
  have hFn : ∀ P, ENNReal.ofReal (-Ξ P) ≤ ENNReal.ofReal M := fun P =>
    ENNReal.ofReal_le_ofReal ((neg_le_abs _).trans (hΞ P))
  have hcongr : (fun ω => ∑' τ : Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        Ξ (fun l l' => prefixOverlap (τ l) (τ l'))) =ᵐ[P] fun ω =>
      (replicaGibbs r n σ t (fun P => ENNReal.ofReal (Ξ P)) (u ω) (lab ω)).toReal -
        (replicaGibbs r n σ t (fun P => ENNReal.ofReal (-Ξ P)) (u ω) (lab ω)).toReal := by
    filter_upwards [h0, ht] with ω hω0 hωt
    refine tsum_cascadeSeries_eq_toReal_sub r n σ t (u ω) (lab ω) Ξ hΞ (fun α => ?_) hωt.1 hωt.2
    exact ENNReal.ne_top_of_tsum_ne_top (by simpa using hω0.2.ne) α
  rw [integral_congr_ae hcongr, integral_sub (hint _ hFp) (hint _ hFn),
    integral_toReal (measurable_replicaGibbs_omega r σ D u lab hDm hu hlab n t _).aemeasurable
      (hle _ hFp |>.mono fun ω h => lt_of_le_of_lt h ENNReal.ofReal_lt_top),
    integral_toReal (measurable_replicaGibbs_omega r σ D u lab hDm hu hlab n t _).aemeasurable
      (hle _ hFn |>.mono fun ω h => lt_of_le_of_lt h ENNReal.ofReal_lt_top)]

/-- **Lemma 2.5 for `k = 0`, in real form.** The expected Gibbs series of a bounded function of
the overlap pattern does not depend on the tilt `t`. -/
theorem integral_cascadeSeries_tilt (hζ0 : ∀ p, 0 < ζ p) (hζ1 : ∀ p, ζ p < 1)
    (hmono : StrictMono ζ)
    (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
    (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
    (hDm : ∀ v, Measurable (D v)) (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
    (hu : u = fun ω p γ m => nthLargestAtom m (poissonCountingMeasure
      (fun k => ((D ⟨p, γ⟩ ω).1 k).1) (fun k l => ((D ⟨p, γ⟩ ω).1 k).2 l)))
    (hlab : lab = fun ω p γ k => (D ⟨p, γ⟩ ω).2 k) (n : ℕ) (t : ℝ)
    (Ξ : (Fin n → Fin n → Fin (r + 1)) → ℝ) {M : ℝ} (hΞ : ∀ P, |Ξ P| ≤ M) :
    ∫ ω, ∑' τ : Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        Ξ (fun l l' => prefixOverlap (τ l) (τ l')) ∂P =
      ∫ ω, ∑' τ : Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (0 * ∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (0 * ∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        Ξ (fun l l' => prefixOverlap (τ l) (τ l')) ∂P := by
  rw [integral_cascadeSeries_eq r ζ σ nu rate 𝔡 D u lab hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu hlab
    n t Ξ hΞ, integral_cascadeSeries_eq r ζ σ nu rate 𝔡 D u lab hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw
    hu hlab n 0 Ξ hΞ, lintegral_cascadeGibbs_tilt r ζ σ t hζ0 hζ1 nu rate hmu 𝔡 h𝔡 D hDm hD hDlaw
    u hu lab hlab n, lintegral_cascadeGibbs_tilt r ζ σ t hζ0 hζ1 nu rate hmu 𝔡 h𝔡 D hDm hD hDlaw
    u hu lab hlab n]

/-- **Lemma 2.5 for `k = (1, 0, …, 0)`, in real form.** For a bounded nonnegative function `F` of
the overlap pattern, the Gibbs series of `F (g(σ^{l₀}) - t b)` with `b = ∑ᵢ σᵢ² ζᵢ` is integrable
and has expectation zero. -/
theorem integral_cascadeEnergy (hζ0 : ∀ p, 0 < ζ p) (hζ1 : ∀ p, ζ p < 1)
    (hmono : StrictMono ζ)
    (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
    (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
    (hDm : ∀ v, Measurable (D v)) (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
    (hu : u = fun ω p γ m => nthLargestAtom m (poissonCountingMeasure
      (fun k => ((D ⟨p, γ⟩ ω).1 k).1) (fun k l => ((D ⟨p, γ⟩ ω).1 k).2 l)))
    (hlab : lab = fun ω p γ k => (D ⟨p, γ⟩ ω).2 k) (n : ℕ) (t : ℝ)
    (F : (Fin n → Fin n → Fin (r + 1)) → ℝ≥0∞) (C : ℝ≥0∞) (hC : C ≠ ∞) (hf : ∀ P, F P ≤ C)
    (l₀ : Fin n) :
    (∀ᵐ ω ∂P, Summable fun τ : Fin n → Fin r → ℕ => (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        ((F fun l l' => prefixOverlap (τ l) (τ l')).toReal *
          (∑ i : Fin r, σ i * leafLabel (lab ω) (τ l₀) i - t * ∑ i : Fin r, σ i ^ 2 * ζ i))) ∧
    Integrable (fun ω => ∑' τ : Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        ((F fun l l' => prefixOverlap (τ l) (τ l')).toReal *
          (∑ i : Fin r, σ i * leafLabel (lab ω) (τ l₀) i - t * ∑ i : Fin r, σ i ^ 2 * ζ i))) P ∧
    ∫ ω, ∑' τ : Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        ((F fun l l' => prefixOverlap (τ l) (τ l')).toReal *
          (∑ i : Fin r, σ i * leafLabel (lab ω) (τ l₀) i - t * ∑ i : Fin r, σ i ^ 2 * ζ i)) ∂P
      = 0 := by
  have h0 := ae_cascadeMass_pos_finite_omega r ζ nu rate 𝔡 D u hζ0 hζ1 hmono hmu h𝔡 hDm hD hDlaw hu
  have ht := ae_tiltedMass_pos_finite (P := P) r ζ σ nu rate 𝔡 D u lab hζ0 hζ1 hmono hmu h𝔡 hDm hD
    hDlaw hu hlab t
  have hsym := fun i : Fin r => lintegral_cascadeGibbsAt_tilt_symm (P := P) r ζ σ t hζ0 hζ1 hmono
    nu rate hmu 𝔡 h𝔡 D hDm hD hDlaw u hu lab hlab n F C hC hf l₀ i
  have hid := identDistrib_cascadeGibbsAt_tilt (P := P) r ζ σ t hζ0 hζ1 nu rate hmu 𝔡 h𝔡 D hDm hD
    hDlaw u hu lab hlab n F l₀
  have hmp : ∀ i : Fin r, AEMeasurable (fun ω => replicaGibbsAt r n σ t F l₀ i
      (fun y => ENNReal.ofReal (σ i * y)) (t * σ i * ζ i) (u ω) (lab ω)) P := fun i => by
    have h := (hid.comp (measurable_pi_apply (i, true))).aemeasurable_fst
    exact h
  have hmn : ∀ i : Fin r, AEMeasurable (fun ω => replicaGibbsAt r n σ t F l₀ i
      (fun y => ENNReal.ofReal (-(σ i * y))) (t * σ i * ζ i) (u ω) (lab ω)) P := fun i => by
    have h := (hid.comp (measurable_pi_apply (i, false))).aemeasurable_fst
    exact h
  have hfin : ∀ i : Fin r, ∫⁻ ω, replicaGibbsAt r n σ t F l₀ i
      (fun y => ENNReal.ofReal (-(σ i * y))) (t * σ i * ζ i) (u ω) (lab ω) ∂P ≠ ∞ := fun i =>
    ((hsym i).1 ▸ (hsym i).2).ne
  have hint : ∀ i : Fin r, Integrable (fun ω => (replicaGibbsAt r n σ t F l₀ i
      (fun y => ENNReal.ofReal (σ i * y)) (t * σ i * ζ i) (u ω) (lab ω)).toReal) P ∧
      Integrable (fun ω => (replicaGibbsAt r n σ t F l₀ i
      (fun y => ENNReal.ofReal (-(σ i * y))) (t * σ i * ζ i) (u ω) (lab ω)).toReal) P :=
    fun i => ⟨integrable_toReal_of_lintegral_ne_top (hmp i) (hsym i).2.ne,
      integrable_toReal_of_lintegral_ne_top (hmn i) (hfin i)⟩
  have hae : ∀ᵐ ω ∂P, ∀ i : Fin r, replicaGibbsAt r n σ t F l₀ i
      (fun y => ENNReal.ofReal (σ i * y)) (t * σ i * ζ i) (u ω) (lab ω) ≠ ∞ ∧
      replicaGibbsAt r n σ t F l₀ i (fun y => ENNReal.ofReal (-(σ i * y))) (t * σ i * ζ i)
        (u ω) (lab ω) ≠ ∞ := by
    rw [ae_all_iff]
    exact fun i => (ae_lt_top' (hmp i) (hsym i).2.ne).and (ae_lt_top' (hmn i) (hfin i))
      |>.mono fun ω h => ⟨h.1.ne, h.2.ne⟩
  have hsumm : ∀ᵐ ω ∂P, Summable fun τ : Fin n → Fin r → ℕ => (∏ l, (cascadeBranchWeight (u ω) (τ
      l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        ((F fun l l' => prefixOverlap (τ l) (τ l')).toReal *
          (∑ i : Fin r, σ i * leafLabel (lab ω) (τ l₀) i - t * ∑ i : Fin r, σ i ^ 2 * ζ i)) := by
    filter_upwards [h0, ht, hae] with ω hω0 hωt hωA
    exact (tsum_cascadeSeries_energy_eq r n σ t (u ω) (lab ω) ζ F
      (fun P => ne_top_of_le_ne_top hC (hf P)) l₀
      (fun α => ENNReal.ne_top_of_tsum_ne_top hω0.2.ne α) hωt.2 hωA).1
  have hcongr : (fun ω => ∑' τ : Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (t * ∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        ((F fun l l' => prefixOverlap (τ l) (τ l')).toReal *
          (∑ i : Fin r, σ i * leafLabel (lab ω) (τ l₀) i - t * ∑ i : Fin r, σ i ^ 2 * ζ i)))
      =ᵐ[P] fun ω => ∑ i : Fin r, ((replicaGibbsAt r n σ t F l₀ i
        (fun y => ENNReal.ofReal (σ i * y)) (t * σ i * ζ i) (u ω) (lab ω)).toReal -
        (replicaGibbsAt r n σ t F l₀ i (fun y => ENNReal.ofReal (-(σ i * y))) (t * σ i * ζ i)
          (u ω) (lab ω)).toReal) := by
    filter_upwards [h0, ht, hae] with ω hω0 hωt hωA
    exact tsum_cascadeSeries_energy_eq r n σ t (u ω) (lab ω) ζ F
      (fun P => ne_top_of_le_ne_top hC (hf P)) l₀
      (fun α => ENNReal.ne_top_of_tsum_ne_top hω0.2.ne α) hωt.2 hωA |>.2
  have hdiff : ∀ i : Fin r, Integrable (fun ω => (replicaGibbsAt r n σ t F l₀ i
      (fun y => ENNReal.ofReal (σ i * y)) (t * σ i * ζ i) (u ω) (lab ω)).toReal -
      (replicaGibbsAt r n σ t F l₀ i (fun y => ENNReal.ofReal (-(σ i * y))) (t * σ i * ζ i)
        (u ω) (lab ω)).toReal) P := fun i => (hint i).1.sub (hint i).2
  refine ⟨hsumm, (integrable_finsetSum _ fun i _ => hdiff i).congr hcongr.symm, ?_⟩
  rw [integral_congr_ae hcongr, integral_finsetSum _ fun i _ => hdiff i]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_sub (hint i).1 (hint i).2, integral_toReal (hmp i) (ae_lt_top' (hmp i)
    (hsym i).2.ne), integral_toReal (hmn i) (ae_lt_top' (hmn i) (hfin i)), (hsym i).1, sub_self]

/-- The measure of the label array: independent standard Gaussians. -/
local notation "μΛ" => Measure.infinitePi fun _ : Σ p : ℕ, Fin p → ℕ =>
  Measure.infinitePi fun _ : ℕ => gaussianReal 0 1

/-- **Integrated Gaussian integration by parts for the Gibbs measure of the cascade.** Conditionally
on the Poisson blocks the leaf field `g(α) = ∑ᵢ σᵢ ℓ(α|ᵢ, αᵢ)` is a Gaussian process with covariance
`Q (α ∧ β)`, `Q m = ∑_{i < m} σᵢ²`; integrating over the blocks gives, for a bounded nonnegative
function `F` of the overlap pattern of `n` replicas,
`E ⟨F g(σ^{l₀})⟩ = E ⟨F (∑_l Q(σ^{l₀} ∧ σ^l) - n Q(σ^{l₀} ∧ σ^{n+1}))⟩`,
where the Gibbs measure has the weights `w_α exp (g(α))`. -/
theorem integral_cascade_ibp (hζ0 : ∀ p, 0 < ζ p) (hζ1 : ∀ p, ζ p < 1)
    (hmono : StrictMono ζ)
    (hmu : ∀ p, zetaPoissonMeasure (ζ p) = Measure.sum fun k => (rate p k : ℝ≥0∞) • nu p k)
    (h𝔡 : ∀ p, 𝔡 p = (Measure.infinitePi fun k =>
      Po(rate p k).prod (Measure.infinitePi fun _ : ℕ => nu p k)).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
    (hDm : ∀ v, Measurable (D v)) (hD : iIndepFun D P) (hDlaw : ∀ v, HasLaw (D v) (𝔡 v.1) P)
    (hu : u = fun ω p γ m => nthLargestAtom m (poissonCountingMeasure
      (fun k => ((D ⟨p, γ⟩ ω).1 k).1) (fun k l => ((D ⟨p, γ⟩ ω).1 k).2 l)))
    (hlab : lab = fun ω p γ k => (D ⟨p, γ⟩ ω).2 k) (n : ℕ)
    (F : (Fin n → Fin n → Fin (r + 1)) → ℝ≥0∞) (C : ℝ≥0∞) (hC : C ≠ ∞) (hf : ∀ P, F P ≤ C)
    (l₀ : Fin n) (Q : Fin (r + 1) → ℝ)
    (hQ : ∀ m, Q m = ∑ i : Fin r, if i.val < m.val then σ i ^ 2 else 0) :
    Integrable (fun ω => ∑' τ : Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        ((F fun l l' => prefixOverlap (τ l) (τ l')).toReal *
          ∑ i : Fin r, σ i * leafLabel (lab ω) (τ l₀) i)) P ∧
    ∫ ω, ∑' τ : Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        ((F fun l l' => prefixOverlap (τ l) (τ l')).toReal *
          ∑ i : Fin r, σ i * leafLabel (lab ω) (τ l₀) i) ∂P = (∑ i : Fin r, σ i ^ 2 * ζ i) * ∫ ω,
      ∑' τ : Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        (F fun l l' => prefixOverlap (τ l) (τ l')).toReal ∂P ∧
    ∫ ω, ∑' τ : Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        ((F fun l l' => prefixOverlap (τ l) (τ l')).toReal *
          ∑ i : Fin r, σ i * leafLabel (lab ω) (τ l₀) i) ∂P = ∫ ω, ∑' τ : Option (Fin n) → Fin r →
      ℕ, (∏ o, (cascadeBranchWeight (u ω) (τ o)).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) (τ o) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        ((F fun l l' => prefixOverlap (τ (some l)) (τ (some l'))).toReal *
          (∑ k : Fin n, Q (prefixOverlap (τ (some l₀)) (τ (some k))) -
            n * Q (prefixOverlap (τ (some l₀)) (τ none)))) ∂P := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : (Fin r → ℕ) → ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ) → ℝ, ∀ α ℓ,
      g α ℓ = ∑ i : Fin r, σ i * ℓ ⟨i, Fin.take i i.isLt.le α⟩ (α i) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℕ × (ℕ → ℝ)) → (Fin r → ℕ) → ℝ, ∀ b α,
      G b α = (cascadeBranchWeight (fun p γ m => nthLargestAtom m (poissonCountingMeasure
        (fun k => (b ⟨p, γ⟩ k).1) (fun k l => (b ⟨p, γ⟩ k).2 l))) α).toReal :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin n → Fin r → ℕ) → ℝ, ∀ τ,
      Φ τ = (F fun l l' => prefixOverlap (τ l) (τ l')).toReal := ⟨_, fun _ => rfl⟩
  obtain ⟨H1, hH1⟩ : ∃ H1 : ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℕ × (ℕ → ℝ)) →
      ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ) → ℝ, ∀ b ℓ, H1 b ℓ =
      ∑' τ : Fin n → Fin r → ℕ, (∏ k, G b (τ k) * Real.exp (g (τ k) ℓ) /
        ∑' c, G b c * Real.exp (g c ℓ)) * (Φ τ * g (τ l₀) ℓ) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨H2, hH2⟩ : ∃ H2 : ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℕ × (ℕ → ℝ)) →
      ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ) → ℝ, ∀ b ℓ, H2 b ℓ =
      ∑' τ : Option (Fin n) → Fin r → ℕ, (∏ o, G b (τ o) * Real.exp (g (τ o) ℓ) /
        ∑' c, G b c * Real.exp (g c ℓ)) * (Φ (fun k => τ (some k)) *
        (∑ k : Fin n, Q (prefixOverlap (τ (some l₀)) (τ (some k))) -
          n * Q (prefixOverlap (τ (some l₀)) (τ none)))) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨H0, hH0⟩ : ∃ H0 : ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℕ × (ℕ → ℝ)) →
      ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ) → ℝ, ∀ b ℓ, H0 b ℓ =
      ∑' τ : Fin n → Fin r → ℕ, (∏ k, G b (τ k) * Real.exp (g (τ k) ℓ) /
        ∑' c, G b c * Real.exp (g c ℓ)) * Φ τ := ⟨_, fun _ _ => rfl⟩
  -- measurability
  have hGm : ∀ α, Measurable fun b : (Σ p : ℕ, Fin p → ℕ) → ℕ → ℕ × (ℕ → ℝ) => G b α := fun α => by
    have e : (fun b : (Σ p : ℕ, Fin p → ℕ) → ℕ → ℕ × (ℕ → ℝ) => G b α) = fun b =>
        (cascadeBranchWeight (fun p γ m => nthLargestAtom m (poissonCountingMeasure
          (fun k => (b ⟨p, γ⟩ k).1) (fun k l => (b ⟨p, γ⟩ k).2 l))) α).toReal :=
      funext fun b => hG b α
    rw [e]
    exact ENNReal.measurable_toReal.comp (measurable_branchWeight_blocks α)
  have hgm : ∀ α, Measurable fun ℓ : (Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ => g α ℓ := fun α => by
    have e : (fun ℓ : (Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ => g α ℓ) = fun ℓ =>
        ∑ i : Fin r, σ i * ℓ ⟨i, Fin.take i i.isLt.le α⟩ (α i) := funext fun ℓ => hg α ℓ
    rw [e]
    exact Finset.measurable_sum _ fun i _ => measurable_const.mul
      ((measurable_pi_apply (α i)).comp (measurable_pi_apply _))
  have hWm : ∀ α, Measurable fun p : ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℕ × (ℕ → ℝ)) ×
      ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ) => G p.1 α * Real.exp (g α p.2) := fun α =>
    ((hGm α).comp measurable_fst).mul (Real.measurable_exp.comp ((hgm α).comp measurable_snd))
  have hH1m : Measurable (Function.uncurry H1) := by
    have h := measurable_tsum_prod_div_mul (K := Fin n)
      (fun (p : ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℕ × (ℕ → ℝ)) × ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ))
        (α : Fin r → ℕ) => G p.1 α * Real.exp (g α p.2)) hWm
      (fun τ p => Φ τ * g (τ l₀) p.2) fun τ => measurable_const.mul ((hgm _).comp measurable_snd)
    have e : Function.uncurry H1 = _ := funext fun p => hH1 p.1 p.2
    rw [e]
    exact h
  have hH0m : Measurable (Function.uncurry H0) := by
    have h := measurable_tsum_prod_div_mul (K := Fin n)
      (fun (p : ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℕ × (ℕ → ℝ)) × ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ))
        (α : Fin r → ℕ) => G p.1 α * Real.exp (g α p.2)) hWm
      (fun τ p => Φ τ) fun τ => measurable_const
    have e : Function.uncurry H0 = _ := funext fun p => hH0 p.1 p.2
    rw [e]
    exact h
  have hH2m : Measurable (Function.uncurry H2) := by
    have h := measurable_tsum_prod_div_mul (K := Option (Fin n))
      (fun (p : ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℕ × (ℕ → ℝ)) × ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ))
        (α : Fin r → ℕ) => G p.1 α * Real.exp (g α p.2)) hWm
      (fun τ p => Φ (fun k => τ (some k)) *
        (∑ k : Fin n, Q (prefixOverlap (τ (some l₀)) (τ (some k))) -
          n * Q (prefixOverlap (τ (some l₀)) (τ none)))) fun τ => measurable_const
    have e : Function.uncurry H2 = _ := funext fun p => hH2 p.1 p.2
    rw [e]
    exact h
  -- blocks and labels
  have hlaw : ∀ v : Σ p : ℕ, Fin p → ℕ, HasLaw (D v) ((Measure.infinitePi fun k =>
      Po(rate v.1 k).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k)).prod
        (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) P := fun v => by
    rw [← h𝔡 v.1]; exact hDlaw v
  obtain ⟨-, hLlaw, hind⟩ := hasLaw_indepFun_fst_snd_of_iIndepFun D hDm hD
    (fun v : Σ p : ℕ, Fin p → ℕ => Measure.infinitePi fun k =>
      Po(rate v.1 k).prod (Measure.infinitePi fun _ : ℕ => nu v.1 k))
    (fun _ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) hlaw
  have hBm : Measurable fun ω (v : Σ p : ℕ, Fin p → ℕ) => (D v ω).1 :=
    measurable_pi_iff.2 fun v => measurable_fst.comp (hDm v)
  have hLm : Measurable fun ω (v : Σ p : ℕ, Fin p → ℕ) => (D v ω).2 :=
    measurable_pi_iff.2 fun v => measurable_snd.comp (hDm v)
  have hLmap : P.map (fun ω (v : Σ p : ℕ, Fin p → ℕ) => (D v ω).2) = μΛ := hLlaw.map_eq
  -- the integrands as functions of blocks and labels
  have hp1 : ∀ ω, ∑' τ : Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        ((F fun l l' => prefixOverlap (τ l) (τ l')).toReal *
          ∑ i : Fin r, σ i * leafLabel (lab ω) (τ l₀) i) =
      H1 (fun v => (D v ω).1) (fun v => (D v ω).2) := fun ω => by
    subst hu hlab
    rw [hH1]
    simp only [hG, hg, hΦ]
    rfl
  have hp2 : ∀ ω, ∑' τ : Option (Fin n) → Fin r → ℕ, (∏ o, (cascadeBranchWeight (u ω) (τ
      o)).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) (τ o) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        ((F fun l l' => prefixOverlap (τ (some l)) (τ (some l'))).toReal *
          (∑ k : Fin n, Q (prefixOverlap (τ (some l₀)) (τ (some k))) -
            n * Q (prefixOverlap (τ (some l₀)) (τ none)))) =
      H2 (fun v => (D v ω).1) (fun v => (D v ω).2) := fun ω => by
    subst hu hlab
    rw [hH2]
    simp only [hG, hg, hΦ]
    rfl
  -- almost sure properties
  have hgood : ∀ᵐ ω ∂P, (∀ α : Fin r → ℕ, cascadeBranchWeight (u ω) α ≠ 0 ∧
      cascadeBranchWeight (u ω) α ≠ ∞) ∧ (∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α) ≠ 0 ∧
      (∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α) < ∞ ∧
      (∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α *
        ENNReal.ofReal (Real.exp (1 * ∑ i : Fin r, σ i * leafLabel (lab ω) α i))) ≠ 0 ∧
      (∑' α : Fin r → ℕ, cascadeBranchWeight (u ω) α *
        ENNReal.ofReal (Real.exp (1 * ∑ i : Fin r, σ i * leafLabel (lab ω) α i))) ≠ ∞ := by
    have h0 := ae_cascadeMass_pos_finite_omega r ζ nu rate 𝔡 D u hζ0 hζ1 hmono hmu h𝔡 hDm hD
      hDlaw hu
    have hat : ∀ᵐ ω ∂P, ∀ α : Fin r → ℕ, cascadeBranchWeight (u ω) α ≠ 0 ∧
        cascadeBranchWeight (u ω) α ≠ ∞ := by
      have h := ae_cascadeData_atoms_pos_finite (P := P) ζ hζ0 hζ1 nu rate hmu (gaussianReal 0 1)
        D hDm hlaw
      subst hu
      filter_upwards [h] with ω hω α
      exact cascadeBranchWeight_pos_finite _ (fun p γ m => (hω ⟨p, γ⟩ m).1)
        (fun p γ m => (hω ⟨p, γ⟩ m).2) α
    have ht := ae_tiltedMass_pos_finite (P := P) r ζ σ nu rate 𝔡 D u lab hζ0 hζ1 hmono hmu h𝔡 hDm
      hD hDlaw hu hlab 1
    filter_upwards [h0, hat, ht] with ω a b c
    exact ⟨b, a.1, a.2, c.1, c.2⟩
  have hGω : ∀ ω α, G (fun v => (D v ω).1) α = (cascadeBranchWeight (u ω) α).toReal :=
    fun ω α => by subst hu; rw [hG]
  have hgω : ∀ ω α, g α (fun v => (D v ω).2) = ∑ i : Fin r, σ i * leafLabel (lab ω) α i :=
    fun ω α => by subst hlab; rw [hg]; rfl
  have hM : ∀ τ, |Φ τ| ≤ C.toReal := fun τ => by
    rw [hΦ, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono hC (hf _)
  -- integrated Gaussian integration by parts, conditionally on the blocks
  have hIBP : ∀ᵐ ω ∂P, ∫ ℓ, H1 (fun v => (D v ω).1) ℓ ∂μΛ = ∫ ℓ, H2 (fun v => (D v ω).1) ℓ ∂μΛ := by
    filter_upwards [hgood] with ω hω
    obtain ⟨hpos, -, hZ0, -, -⟩ := hω
    have hGpos : ∀ α, 0 < G (fun v => (D v ω).1) α := fun α => by
      rw [hGω]; exact ENNReal.toReal_pos (hpos α).1 (hpos α).2
    have hGsum : Summable (G (fun v => (D v ω).1)) := by
      rw [show G (fun v => (D v ω).1) = fun α => (cascadeBranchWeight (u ω) α).toReal from
        funext (hGω ω)]
      exact ENNReal.summable_toReal hZ0.ne
    have h := integral_gibbs_leafField_ibp hg Q hQ (G (fun v => (D v ω).1)) hGpos hGsum l₀ Φ hM
    simp only [Fintype.card_fin] at h
    simp_rw [hH1, hH2]
    exact h
  have hWgood : ∀ᵐ ω ∂P, (∀ α, 0 ≤ G (fun v => (D v ω).1) α *
        Real.exp (g α (fun v => (D v ω).2))) ∧
      Summable (fun α => G (fun v => (D v ω).1) α * Real.exp (g α (fun v => (D v ω).2))) ∧
      ∑' α, G (fun v => (D v ω).1) α * Real.exp (g α (fun v => (D v ω).2)) ≠ 0 := by
    filter_upwards [hgood] with ω hω
    obtain ⟨hpos, -, -, hZ1, hZ1t⟩ := hω
    obtain ⟨hs, hne⟩ := summable_tsum_ne_zero_cascadeWeight r σ 1 (u ω) (lab ω)
      (fun α => (hpos α).2) hZ1 hZ1t
    simp only [one_mul] at hs hne
    simp_rw [hGω, hgω]
    exact ⟨fun α => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le, hs, hne⟩
  have hmeasPair : ∀ H : ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℕ × (ℕ → ℝ)) →
      ((Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ) → ℝ, Measurable (Function.uncurry H) →
      AEStronglyMeasurable (fun ω => H (fun v => (D v ω).1) (fun v => (D v ω).2)) P :=
    fun H hH => by
      have h := hH.comp (hBm.prodMk hLm)
      exact h.aestronglyMeasurable
  have hI0 : Integrable (fun ω => H0 (fun v => (D v ω).1) (fun v => (D v ω).2)) P := by
    refine Integrable.of_bound (hmeasPair H0 hH0m) C.toReal ?_
    filter_upwards [hWgood] with ω ⟨h1, h2, h3⟩
    rw [Real.norm_eq_abs, hH0]
    exact abs_tsum_prod_div_mul_le (W := fun α => G (fun v => (D v ω).1) α *
      Real.exp (g α (fun v => (D v ω).2))) h1 h2 h3 hM
  have hQ0 : ∀ m, 0 ≤ Q m := fun m => by
    rw [hQ]
    refine Finset.sum_nonneg fun i _ => ?_
    split_ifs with h
    · exact sq_nonneg (σ i)
    · exact le_rfl
  have hQr : ∀ m, Q m ≤ ∑ i : Fin r, σ i ^ 2 := fun m => by
    rw [hQ]
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs with h
    · exact le_rfl
    · exact sq_nonneg (σ i)
  have hb2 : ∀ τ : Option (Fin n) → Fin r → ℕ,
      |∑ k : Fin n, Q (prefixOverlap (τ (some l₀)) (τ (some k))) -
        n * Q (prefixOverlap (τ (some l₀)) (τ none))| ≤ 2 * n * ∑ i : Fin r, σ i ^ 2 := fun τ => by
    simpa using Finset.abs_sum_sub_card_mul_le (ι := Fin n) Q hQ0 hQr
      (fun k => prefixOverlap (τ (some l₀)) (τ (some k))) (prefixOverlap (τ (some l₀)) (τ none))
  have hI2 : Integrable (fun ω => H2 (fun v => (D v ω).1) (fun v => (D v ω).2)) P := by
    refine Integrable.of_bound (hmeasPair H2 hH2m) (C.toReal * (2 * n * ∑ i : Fin r, σ i ^ 2)) ?_
    filter_upwards [hWgood] with ω ⟨h1, h2, h3⟩
    rw [Real.norm_eq_abs, hH2]
    refine abs_tsum_prod_div_mul_le (W := fun α => G (fun v => (D v ω).1) α *
      Real.exp (g α (fun v => (D v ω).2))) h1 h2 h3 fun τ => ?_
    rw [abs_mul]
    exact mul_le_mul (hM _) (hb2 τ) (abs_nonneg _) ENNReal.toReal_nonneg
  obtain ⟨hsumE, hintE, hzeroE⟩ := integral_cascadeEnergy r ζ σ nu rate 𝔡 D u lab hζ0 hζ1 hmono
    hmu h𝔡 hDm hD hDlaw hu hlab n 1 F C hC hf l₀
  simp only [one_mul] at hsumE hintE hzeroE
  have key : ∀ f : Ω → ℝ, Integrable f P → ∫ ω, f ω ∂P = 0 →
      (∀ᵐ ω ∂P, f ω + (∑ i : Fin r, σ i ^ 2 * ζ i) *
        H0 (fun v => (D v ω).1) (fun v => (D v ω).2) =
        H1 (fun v => (D v ω).1) (fun v => (D v ω).2)) →
      Integrable (fun ω => H1 (fun v => (D v ω).1) (fun v => (D v ω).2)) P ∧
      ∫ ω, H1 (fun v => (D v ω).1) (fun v => (D v ω).2) ∂P =
        (∑ i : Fin r, σ i ^ 2 * ζ i) * ∫ ω, H0 (fun v => (D v ω).1) (fun v => (D v ω).2) ∂P :=
    fun f hf0 hz hae => by
      have hI := hf0.add (hI0.const_mul (∑ i : Fin r, σ i ^ 2 * ζ i))
      refine ⟨hI.congr hae, ?_⟩
      rw [← integral_congr_ae hae, integral_add hf0 (hI0.const_mul _), hz, zero_add,
        integral_const_mul]
  obtain ⟨hI1, hEq⟩ := key _ hintE hzeroE (by
    filter_upwards [hWgood, hsumE] with ω ⟨h1, h2, h3⟩ hs
    rw [← hp1 ω, hH0]
    simp only [hGω, hgω, hΦ]
    have hsb := summable_prod_div_mul (K := Fin n) h1 h2 h3 (Φ := fun τ => (F fun l l' =>
      prefixOverlap (τ l) (τ l')).toReal) (M := C.toReal) fun τ => by
      have := hM τ
      rwa [hΦ] at this
    simp only [hGω, hgω] at hsb
    rw [← tsum_mul_left, ← Summable.tsum_add hs (hsb.mul_left _)]
    refine tsum_congr fun τ => ?_
    ring)
  have hF1 := IndepFun.integral_comp_pair_eq_integral_integral_map hBm hLm hind hH1m hI1
  have hF2 := IndepFun.integral_comp_pair_eq_integral_integral_map hBm hLm hind hH2m hI2
  rw [hLmap] at hF1 hF2
  have hcalc : ∫ ω, H1 (fun v => (D v ω).1) (fun v => (D v ω).2) ∂P =
      ∫ ω, H2 (fun v => (D v ω).1) (fun v => (D v ω).2) ∂P :=
    hF1.trans ((integral_congr_ae hIBP).trans hF2.symm)
  have e1 : (fun ω => H1 (fun v => (D v ω).1) (fun v => (D v ω).2)) = fun ω => ∑' τ :
      Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        ((F fun l l' => prefixOverlap (τ l) (τ l')).toReal *
          ∑ i : Fin r, σ i * leafLabel (lab ω) (τ l₀) i) := funext fun ω => (hp1 ω).symm
  have e2 : (fun ω => H2 (fun v => (D v ω).1) (fun v => (D v ω).2)) = fun ω => ∑' τ :
      Option (Fin n) → Fin r → ℕ, (∏ o, (cascadeBranchWeight (u ω) (τ o)).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) (τ o) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        ((F fun l l' => prefixOverlap (τ (some l)) (τ (some l'))).toReal *
          (∑ k : Fin n, Q (prefixOverlap (τ (some l₀)) (τ (some k))) -
            n * Q (prefixOverlap (τ (some l₀)) (τ none)))) := funext fun ω => (hp2 ω).symm
  have e0 : (fun ω => H0 (fun v => (D v ω).1) (fun v => (D v ω).2)) = fun ω => ∑' τ :
      Fin n → Fin r → ℕ, (∏ l, (cascadeBranchWeight (u ω) (τ l)).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) (τ l) i) /
        ∑' b : Fin r → ℕ, (cascadeBranchWeight (u ω) b).toReal *
          Real.exp (∑ i : Fin r, σ i * leafLabel (lab ω) b i)) *
        (F fun l l' => prefixOverlap (τ l) (τ l')).toReal := funext fun ω => by
    rw [hH0]; simp only [hGω, hgω, hΦ]
  rw [e1] at hI1 hEq hcalc
  rw [e2] at hcalc
  rw [e0] at hEq
  exact ⟨hI1, hEq, hcalc⟩

end Setting

end SpinGlasses
