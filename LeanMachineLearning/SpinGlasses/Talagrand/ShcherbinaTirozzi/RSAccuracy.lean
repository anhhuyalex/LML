/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.PiFinMul
import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ReplicaOverlaps

public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.CavityConcentration
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.CavityLastSpinMoments
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.CavityOverlapRate

/-!
# The Shcherbina--Tirozzi model: RS equation accuracy at rate `K / √N` (Proposition 3.2.12)

This file proves **Proposition 3.2.12** (Eq. (3.115)): combining Proposition 3.2.10
(`CavityLastSpinMoments.lean`) with Eq. (3.111) (`CavityConcentration.lean`) and Lemma 3.2.11
(`CavityOverlapRate.lean`), the physical overlaps `(q, ρ)` satisfy the replica-symmetric equations
(3.69), (3.76), (3.77) with accuracy `K / √(N + 1)`, for every `N`:
```
|ρ - (1 / a + (r + h²) / a²)| ≤ K / √(N + 1),
|q - (r + h²) / a²| ≤ K / √(N + 1),
```
where `a = 2 κ + r - r̄` and `(r, r̄)` are the RS parameters (3.69) at `α = M / (N + 1)`.

## Main declarations

* `SpinGlasses.exists_shcherbinaTirozzi_rsEquations_accuracy`: Proposition 3.2.12 (Eq. (3.115))
  at the physical parameters `(q, ρ, r, r̄)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal NNReal Topology RealInnerProductSpace Real

namespace SpinGlasses

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

local notation "Dis[" N ", " M "]" =>
  ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))

local notation "cavLaw[" N ", " M ", " r "]" =>
  Measure.prod (gaussianReal 0 r)
    (Measure.prod
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
      (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))

section Proposition3212

/-- Auxiliary quadratic triangle bound: under probability measures `P` and `G d`,
`√(∫ d, ∫ (X - c)² ∂G d ∂P) ≤ √(∫ d, ∫ (X - c_t)² ∂G d ∂P) + |c_t - c|`. -/
private lemma sqrt_integral_integral_sub_sq_le {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] {P : Measure Ω} [IsProbabilityMeasure P] {G : Ω → Measure α}
    [∀ d, IsProbabilityMeasure (G d)] {X : α → ℝ} {c c_t : ℝ}
    (hXm : Measurable X)
    (hX_int : ∀ d, Integrable (fun x => (X x - c_t) ^ 2) (G d))
    (h_int : Integrable (fun d => ∫ x, (X x - c_t) ^ 2 ∂(G d)) P) :
    Real.sqrt (∫ d, ∫ x, (X x - c) ^ 2 ∂(G d) ∂P) ≤
      Real.sqrt (2 * ∫ d, ∫ x, (X x - c_t) ^ 2 ∂(G d) ∂P) + Real.sqrt 2 * |c_t - c| := by
  have hpt_x : ∀ x, (X x - c) ^ 2 ≤ 2 * (X x - c_t) ^ 2 + 2 * (c_t - c) ^ 2 := fun x => by
    have hsq := sq_nonneg ((X x - c_t) - (c_t - c))
    have hid : (X x - c) ^ 2 = ((X x - c_t) + (c_t - c)) ^ 2 := by ring
    nlinarith [hid, hsq]
  have hpt_d : ∀ d, ∫ x, (X x - c) ^ 2 ∂(G d) ≤
      2 * (∫ x, (X x - c_t) ^ 2 ∂(G d)) + 2 * (c_t - c) ^ 2 := fun d => by
    have hi_c : Integrable (fun x => (X x - c) ^ 2) (G d) :=
      (((hX_int d).const_mul 2).add (integrable_const _)).mono'
        ((hXm.sub_const c).pow_const 2).aestronglyMeasurable
        (ae_of_all _ fun x => by rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hpt_x x)
    refine (integral_mono hi_c (((hX_int d).const_mul 2).add (integrable_const _)) hpt_x).trans_eq
      ?_
    change ∫ x, (2 * (X x - c_t) ^ 2 + 2 * (c_t - c) ^ 2) ∂(G d) = _
    rw [integral_add ((hX_int d).const_mul 2) (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, one_smul]
  have htot : ∫ d, ∫ x, (X x - c) ^ 2 ∂(G d) ∂P ≤
      2 * (∫ d, ∫ x, (X x - c_t) ^ 2 ∂(G d) ∂P) + 2 * (c_t - c) ^ 2 := by
    by_cases hi : Integrable (fun d => ∫ x, (X x - c) ^ 2 ∂(G d)) P
    · refine (integral_mono hi ((h_int.const_mul 2).add (integrable_const _)) hpt_d).trans_eq ?_
      change ∫ d, (2 * (∫ x, (X x - c_t) ^ 2 ∂(G d)) + 2 * (c_t - c) ^ 2) ∂P = _
      rw [integral_add (h_int.const_mul 2) (integrable_const _), integral_const_mul,
        integral_const, probReal_univ, one_smul]
    · rw [integral_undef hi]
      exact add_nonneg (mul_nonneg zero_le_two (integral_nonneg fun d =>
        integral_nonneg fun _ => sq_nonneg _)) (by positivity)
  have hsq_add : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
    intro a b ha hb
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    linarith [mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
  calc Real.sqrt (∫ d, ∫ x, (X x - c) ^ 2 ∂(G d) ∂P)
      ≤ Real.sqrt (2 * (∫ d, ∫ x, (X x - c_t) ^ 2 ∂(G d) ∂P) + 2 * (c_t - c) ^ 2) :=
        Real.sqrt_le_sqrt htot
    _ ≤ Real.sqrt (2 * ∫ d, ∫ x, (X x - c_t) ^ 2 ∂(G d) ∂P) + Real.sqrt (2 * (c_t - c) ^ 2) :=
        hsq_add _ _ (mul_nonneg zero_le_two (integral_nonneg fun _ =>
          integral_nonneg fun _ => sq_nonneg _)) (by positivity)
    _ = Real.sqrt (2 * ∫ d, ∫ x, (X x - c_t) ^ 2 ∂(G d) ∂P) + Real.sqrt 2 * |c_t - c| := by
        congr 1; rw [Real.sqrt_mul zero_le_two, Real.sqrt_sq_eq_abs]

/-- Recenter a second-moment bound when the displacement is bounded at the same scale. -/
private lemma sqrt_integral_integral_sub_sq_le_of_le_div {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] {P : Measure Ω} [IsProbabilityMeasure P] {G : Ω → Measure α}
    [∀ d, IsProbabilityMeasure (G d)] {X : α → ℝ} {c c_t n A B : ℝ}
    (hA : 0 ≤ A) (hXm : Measurable X)
    (hX_int : ∀ d, Integrable (fun x => (X x - c_t) ^ 2) (G d))
    (h_int : Integrable (fun d => ∫ x, (X x - c_t) ^ 2 ∂(G d)) P)
    (hvar : ∫ d, ∫ x, (X x - c_t) ^ 2 ∂(G d) ∂P ≤ A / n)
    (hmean : |c_t - c| ≤ B / Real.sqrt n) :
    Real.sqrt (∫ d, ∫ x, (X x - c) ^ 2 ∂(G d) ∂P) ≤
      (Real.sqrt (2 * A) + Real.sqrt 2 * B) / Real.sqrt n := by
  refine (sqrt_integral_integral_sub_sq_le hXm hX_int h_int).trans ?_
  rw [add_div, ← Real.sqrt_div (mul_nonneg zero_le_two hA), mul_div_assoc, mul_div_assoc]
  exact add_le_add (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hvar zero_le_two))
    (mul_le_mul_of_nonneg_left hmean (Real.sqrt_nonneg _))

/-- The coordinate expansion of the squared norm of the mean spin. -/
private lemma norm_integral_sq_eq_sum_sq {ι : Type*} [Fintype ι]
    {μ : Measure (EuclideanSpace ℝ ι)} (hi : Integrable (fun x : EuclideanSpace ℝ ι => x) μ) :
    ‖∫ σ, σ ∂μ‖ ^ 2 = ∑ i, (∫ σ, σ i ∂μ) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg (fun x : ℝ => x ^ 2)
    ((EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hi).symm

/-- A second norm moment controls the centered square of a scaled replica inner product. -/
private lemma integrable_sq_scaled_inner_sub_pi {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure E) [IsProbabilityMeasure μ] (s c : ℝ)
    (hnorm : Integrable (fun x : E => ‖x‖ ^ 2) μ) :
    Integrable (fun p : Fin 2 → E => (s * ⟪p 0, p 1⟫ - c) ^ 2)
      (Measure.pi fun _ : Fin 2 => μ) := by
  have hprod := Integrable.fintype_prod (f := fun _ : Fin 2 => fun x : E => ‖x‖ ^ 2)
    (fun _ => hnorm)
  simp only [Fin.prod_univ_two] at hprod
  refine integrable_sub_pow_of_integrable_abs_pow
    (((measurable_pi_apply (0 : Fin 2)).inner (measurable_pi_apply (1 : Fin 2))).const_mul _)
    (c := 0) ((hprod.const_mul (s ^ 2)).mono' (by fun_prop) (ae_of_all _ fun p => ?_)) c
  rw [sub_zero, Real.norm_of_nonneg (sq_nonneg _), abs_mul, mul_pow, sq_abs]
  have h := pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm (p 0) (p 1)) 2
  exact mul_le_mul_of_nonneg_left (by simpa only [mul_pow] using h) (sq_nonneg _)

/-- A cavity Gibbs measure has finite norm moments of every order, for `t ∈ [0, 1]`. -/
private lemma integrable_norm_pow_shcherbinaTirozziCavity {N M : ℕ} {κ h t rBar : ℝ}
    {r : ℝ≥0} {u : ℝ → ℝ} (hκ : 0 < κ) (hrr : rBar ≤ r) (ht : t ∈ Icc (0 : ℝ) 1)
    (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0) (k : ℕ) (d : Dis[N, M]) :
    Integrable (fun x : ℝ^(N + 1) => ‖x‖ ^ k) (volume.tilted fun σ =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 σ) :=
  (memLp_of_poly_bound_of_confining hκ
    (measurable_shcherbinaTirozziCavityHamiltonian_apply κ h r rBar t d.1 hu d.2.1 d.2.2).neg
    (fun σ => by
      rw [zero_add]
      exact neg_shcherbinaTirozziCavityHamiltonian_le κ h d.1 hrr ht.1 ht.2 hu0 d.2.1 d.2.2 σ)
    (measurable_norm.pow_const k).aestronglyMeasurable (C := 1) (m := k) (fun x => by
      rw [one_mul, Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) k)
    1).integrable le_rfl

/-- At `t = 1` the cavity state does not depend on `y`: any functional of it averages as the
same functional of the Gibbs measure of the model, for any law of `y` and of the couplings. -/
private lemma integral_apply_shcherbinaTirozziCavity_one {N M : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (κ h r rBar : ℝ) (u : ℝ → ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ]
    (ν : Measure ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) [SFinite ν]
    (Φ : Measure (ℝ^(N + 1)) → E) :
    ∫ d, Φ (volume.tilted fun σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar 1 d.1 u d.2.1 d.2.2 σ) ∂(μ.prod ν) =
      ∫ e, Φ (volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u e.1 e.2 σ) ∂ν := by
  obtain ⟨F, hF⟩ : ∃ F : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) → E, ∀ e, F e =
      Φ (volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u e.1 e.2 σ) :=
    ⟨_, fun _ => rfl⟩
  have h1 (d : Dis[N, M]) : Φ (volume.tilted fun σ =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar 1 d.1 u d.2.1 d.2.2 σ) = F d.2 := by
    simp only [hF, shcherbinaTirozziCavityHamiltonian_one]
  simp only [h1, ← hF]
  exact integral_prod_fun_snd_of_isProbabilityMeasure μ ν F

/-- The quenched average of a replica observable of polynomial growth can be taken first over
the couplings and then over the field `y`. -/
private lemma integral_integral_pi_shcherbinaTirozziCavity_eq_iterated {N M : ℕ} {R : Type*}
    [Fintype R] {κ h t rBar D : ℝ} {r : ℝ≥0} {u : ℝ → ℝ} (hκ : 0 < κ) (hrr : rBar ≤ r)
    (ht : t ∈ Icc (0 : ℝ) 1) (hu0 : ∀ x, u x ≤ 0) (hu1 : Differentiable ℝ u)
    (hD : ∀ x, |deriv u x| ≤ D) {f : Dis[N, M] → (R → ℝ^(N + 1)) → ℝ}
    (hf : Measurable fun p : Dis[N, M] × (R → ℝ^(N + 1)) => f p.1 p.2) {C : ℝ} {m : ℕ}
    (hfb : ∀ d σ, |f d σ| ≤ C * ∏ l, (1 + ‖σ l‖) ^ m) :
    ∫ d, ∫ σ, f d σ ∂(Measure.pi fun _ : R => volume.tilted fun x =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 x)
        ∂cavLaw[N, M, r] =
      ∫ y, ∫ e, ∫ σ, f (y, e) σ ∂(Measure.pi fun _ : R => volume.tilted fun x =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u e.1 e.2 x)
        ∂((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)) ∂(gaussianReal 0 r) :=
  integral_prod _ (integrable_integral_pi_shcherbinaTirozziCavity (R := R) (h := h) hκ r hrr
    ht hu0 hu1 hD hfb hf)

/-- At `t = 0`, with `r̄ = r` and `y = 0`, the cavity Hamiltonian is the Hamiltonian of the model
when no constraint involves the last spin (in particular when there is no constraint). -/
private lemma shcherbinaTirozziCavityHamiltonian_zero_of_last_eq_zero {N M : ℕ} (κ h r : ℝ)
    (u : ℝ → ℝ) {g : Fin M → Fin (N + 1) → ℝ} (hg : ∀ k, g k (Fin.last N) = 0)
    (g₀ : Fin (N + 1) → ℝ) (σ : ℝ^(N + 1)) :
    shcherbinaTirozziCavityHamiltonian κ h r r 0 0 u g g₀ σ =
      shcherbinaTirozziHamiltonian κ h u g g₀ σ := by
  simp only [shcherbinaTirozziCavityHamiltonian, shcherbinaTirozziHamiltonian,
    Fin.sum_univ_castSucc (fun i => g _ i * σ i), hg, Real.sqrt_zero, zero_mul, mul_zero,
    add_zero, sub_self, zero_div, sub_zero, Nat.cast_add, Nat.cast_one]

/-- The replica-symmetric residuals are bounded when the parameters are. This covers the finitely
many small sizes in Proposition 3.2.12. -/
private lemma abs_sub_rsEquations_le_of_bounds {κ₀ h₀ κ h q ρ r rBar Q R : ℝ} (hκ₀ : 0 < κ₀)
    (hκ : κ₀ ≤ κ) (hh : |h| ≤ h₀) (hq : 0 ≤ q) (hqρ : q ≤ ρ) (hρ : ρ ≤ Q) (hr : 0 ≤ r)
    (hrR : r ≤ R) (hrr : rBar ≤ r) :
    |ρ - ((2 * κ + r - rBar)⁻¹ + (r + h ^ 2) / (2 * κ + r - rBar) ^ 2)| ≤
        Q + (2 * κ₀)⁻¹ + (R + h₀ ^ 2) / (2 * κ₀) ^ 2 ∧
      |q - (r + h ^ 2) / (2 * κ + r - rBar) ^ 2| ≤
        Q + (2 * κ₀)⁻¹ + (R + h₀ ^ 2) / (2 * κ₀) ^ 2 := by
  set a : ℝ := 2 * κ + r - rBar
  have ha : 2 * κ₀ ≤ a := by dsimp only [a]; linarith
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hinv : a⁻¹ ≤ (2 * κ₀)⁻¹ := inv_anti₀ (by positivity) ha
  have hh2 : h ^ 2 ≤ h₀ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hh 2
  have hX : (r + h ^ 2) / a ^ 2 ≤ (R + h₀ ^ 2) / (2 * κ₀) ^ 2 :=
    div_le_div₀ (add_nonneg (hr.trans hrR) (sq_nonneg _)) (add_le_add hrR hh2) (by positivity)
      (pow_le_pow_left₀ (by positivity) ha 2)
  have hX0 : 0 ≤ (r + h ^ 2) / a ^ 2 := div_nonneg (add_nonneg hr (sq_nonneg _)) (sq_nonneg _)
  have hinv0 : 0 ≤ a⁻¹ := inv_nonneg.2 ha0.le
  have hQ : 0 ≤ Q := hq.trans (hqρ.trans hρ)
  constructor <;> rw [abs_sub_le_iff] <;> constructor <;> linarith

/-- **Eq. (3.114) at rate `K / √(N + 1)`:** along the whole cavity path the self-overlap is, in
`L²`, within `K / √(N + 1)` of its average at `t = 1`, up to the distance from that average to
the chosen centre `c`. -/
private theorem exists_sqrt_integral_shcherbinaTirozziCavity_selfOverlap_sub_one_sq_le
    (κ₀ h₀ D R R_diff : ℝ) (hκ₀ : 0 < κ₀) (hR : 0 ≤ R) (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M : ℕ) (κ h t rBar : ℝ) (r : ℝ≥0) (u : ℝ → ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → rBar ≤ r → (r : ℝ) ≤ R →
      (r : ℝ) - rBar ≤ R_diff → M ≤ 10 * (N + 1) → 4 ≤ N + 1 →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → (∀ x, -D * (1 + |x|) ≤ u x) →
      Differentiable ℝ u → Differentiable ℝ (deriv u) →
      (∀ x, |deriv u x| ≤ D) → (∀ x, |deriv (deriv u) x| ≤ D) →
      let G (s : ℝ) (d : Dis[N, M]) : Measure (ℝ^(N + 1)) :=
        volume.tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar s d.1 u d.2.1 d.2.2 σ
      ∀ c : ℝ, Real.sqrt (∫ d, ∫ x : ℝ^(N + 1), (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - c) ^ 2 ∂(G t d)
          ∂cavLaw[N, M, r]) ≤ K / Real.sqrt ((N : ℝ) + 1) + Real.sqrt 2 *
        |(∫ d, ∫ x : ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 ∂(G 1 d) ∂cavLaw[N, M, r]) - c| := by
  obtain ⟨K_c, hK_c, hconc⟩ :=
    exists_integral_shcherbinaTirozziCavity_selfOverlap_sub_pow_le κ₀ h₀ D R R_diff hκ₀ hR hR_diff
  obtain ⟨K_l, hK_l, hlem⟩ :=
    exists_abs_shcherbinaTirozziCavity_selfOverlap_sub_le κ₀ h₀ D R R_diff hκ₀ hR hR_diff
  refine ⟨Real.sqrt (2 * K_c) + Real.sqrt 2 * K_l, by positivity,
    fun N M κ h t rBar r u hκ hh ht0 ht1 hrr hrR hrr_diff hM hN4 huc hu0 hgrow hu1 hu2 hD1
      hD2 => ?_⟩
  intro G c
  have hsqrt : Real.sqrt ((N : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum : Measurable u := hu1.continuous.measurable
  have hD_lip : ∀ x y : ℝ, |deriv u x - deriv u y| ≤ D * |x - y| := fun x y => by
    simpa only [Real.norm_eq_abs] using convex_univ.norm_image_sub_le_of_norm_deriv_le
      (f := deriv u) (C := D) (fun z _ => hu2 z)
      (fun z _ => by simpa only [Real.norm_eq_abs] using hD2 z) (Set.mem_univ y) (Set.mem_univ x)
  have : ∀ d, IsProbabilityMeasure (G t d) := fun d => isProbabilityMeasure_tilted
    (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ0
      (mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hrr)) hum hu0 d.2.1 d.2.2)
  obtain ⟨hc_i, hc_le⟩ := hconc N M 1 κ h t rBar r u hκ hh ht0 ht1 hrr hrR hrr_diff hM
    (by omega) huc hu0 hgrow hu1 hD1 hD_lip
  simp only [mul_one, Nat.cast_one, pow_one] at hc_i hc_le
  set ρ_t : ℝ := ∫ e, ∫ τ : ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ‖τ‖ ^ 2 ∂(G t e) ∂cavLaw[N, M, r]
  set ρ₁ : ℝ := ∫ d, ∫ x : ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 ∂(G 1 d) ∂cavLaw[N, M, r]
  have hdiff : |ρ_t - c| ≤ (K_l + |ρ₁ - c| * Real.sqrt ((N : ℝ) + 1)) /
      Real.sqrt ((N : ℝ) + 1) := by
    rw [add_div, mul_div_cancel_right₀ _ hsqrt]
    exact (abs_sub_le ρ_t ρ₁ c).trans (add_le_add (hlem N M κ h t rBar r u hκ hh ht0 ht1 hrr
      hrR hrr_diff hM hN4 huc hu0 hgrow hu1 hu2 hD1 hD2) le_rfl)
  have hX_int (d : Dis[N, M]) : Integrable (fun x : ℝ^(N + 1) =>
      (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - ρ_t) ^ 2) (G t d) :=
    integrable_sub_pow_of_integrable_abs_pow
      ((measurable_norm.pow_const 2).const_mul _) (c := 0)
      (by simpa only [sub_zero, abs_mul, abs_pow, abs_norm, mul_pow, ← pow_mul] using
        (integrable_norm_pow_shcherbinaTirozziCavity (h := h) hκ0 hrr ⟨ht0, ht1⟩ hum hu0 4
          d).const_mul (|((N : ℝ) + 1)⁻¹| ^ 2))
      ρ_t
  refine (sqrt_integral_integral_sub_sq_le_of_le_div (P := cavLaw[N, M, r]) (G := G t)
    (X := fun x : ℝ^(N + 1) => ((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2) hK_c
    ((measurable_norm.pow_const 2).const_mul _) hX_int hc_i hc_le hdiff).trans_eq ?_
  field_simp
  ring

/-- **Eq. (3.113) at rate `K / √(N + 1)`:** along the whole cavity path the overlap of two
replicas is, in `L²`, within `K / √(N + 1)` of its average at `t = 1`, up to the distance from
that average to the chosen centre `c`. -/
private theorem exists_sqrt_integral_shcherbinaTirozziCavity_overlap_sub_one_sq_le
    (κ₀ h₀ D R R_diff : ℝ) (hκ₀ : 0 < κ₀) (hR : 0 ≤ R) (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M : ℕ) (κ h t rBar : ℝ) (r : ℝ≥0) (u : ℝ → ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → rBar ≤ r → (r : ℝ) ≤ R →
      (r : ℝ) - rBar ≤ R_diff → M ≤ 10 * (N + 1) → 4 ≤ N + 1 →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → (∀ x, -D * (1 + |x|) ≤ u x) →
      Differentiable ℝ u → Differentiable ℝ (deriv u) →
      (∀ x, |deriv u x| ≤ D) → (∀ x, |deriv (deriv u) x| ≤ D) →
      let G (s : ℝ) (d : Dis[N, M]) : Measure (ℝ^(N + 1)) :=
        volume.tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar s d.1 u d.2.1 d.2.2 σ
      ∀ c : ℝ, Real.sqrt (∫ d, ∫ p : Fin 2 → ℝ^(N + 1),
          (((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫ - c) ^ 2
          ∂(Measure.pi fun _ : Fin 2 => G t d) ∂cavLaw[N, M, r]) ≤
        K / Real.sqrt ((N : ℝ) + 1) + Real.sqrt 2 *
          |(∫ d, ∫ p : Fin 2 → ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫
            ∂(Measure.pi fun _ : Fin 2 => G 1 d) ∂cavLaw[N, M, r]) - c| := by
  obtain ⟨K_c, hK_c, hconc⟩ :=
    exists_integral_shcherbinaTirozziCavity_overlap_sub_pow_le κ₀ h₀ D R R_diff hκ₀ hR hR_diff
  obtain ⟨K_l, hK_l, hlem⟩ :=
    exists_abs_shcherbinaTirozziCavity_overlap_sub_le κ₀ h₀ D R R_diff hκ₀ hR hR_diff
  refine ⟨Real.sqrt (2 * K_c) + Real.sqrt 2 * K_l, by positivity,
    fun N M κ h t rBar r u hκ hh ht0 ht1 hrr hrR hrr_diff hM hN4 huc hu0 hgrow hu1 hu2 hD1
      hD2 => ?_⟩
  intro G c
  have hsqrt : Real.sqrt ((N : ℝ) + 1) ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum : Measurable u := hu1.continuous.measurable
  have hD_lip : ∀ x y : ℝ, |deriv u x - deriv u y| ≤ D * |x - y| := fun x y => by
    simpa only [Real.norm_eq_abs] using convex_univ.norm_image_sub_le_of_norm_deriv_le
      (f := deriv u) (C := D) (fun z _ => hu2 z)
      (fun z _ => by simpa only [Real.norm_eq_abs] using hD2 z) (Set.mem_univ y) (Set.mem_univ x)
  have : ∀ d, IsProbabilityMeasure (G t d) := fun d => isProbabilityMeasure_tilted
    (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ0
      (mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hrr)) hum hu0 d.2.1 d.2.2)
  obtain ⟨hc_i, hc_le⟩ := hconc N M 1 κ h t rBar r u hκ hh ht0 ht1 hrr hrR hrr_diff hM
    (by omega) huc hu0 hgrow hu1 hD1 hD_lip
  simp only [mul_one, Nat.cast_one, pow_one] at hc_i hc_le
  set q_t : ℝ := ∫ e, ∫ p : ℝ^(N + 1) × ℝ^(N + 1),
    ((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ ∂((G t e).prod (G t e)) ∂cavLaw[N, M, r]
  have hqt_pi : q_t = ∫ e, ∫ p : Fin 2 → ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫
      ∂(Measure.pi fun _ : Fin 2 => G t e) ∂cavLaw[N, M, r] :=
    integral_congr_ae (ae_of_all _ fun e => (integral_pi_pair_eq_prod (G t e)
      (show (0 : Fin 2) ≠ 1 by decide) (fun x y => ((N : ℝ) + 1)⁻¹ * ⟪x, y⟫) (by fun_prop)).symm)
  set q₁ : ℝ := ∫ d, ∫ p : Fin 2 → ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫
    ∂(Measure.pi fun _ : Fin 2 => G 1 d) ∂cavLaw[N, M, r]
  have hdiff : |q_t - c| ≤ (K_l + |q₁ - c| * Real.sqrt ((N : ℝ) + 1)) /
      Real.sqrt ((N : ℝ) + 1) := by
    rw [add_div, mul_div_cancel_right₀ _ hsqrt]
    refine (abs_sub_le q_t q₁ c).trans (add_le_add ?_ le_rfl)
    rw [hqt_pi]
    exact hlem N M κ h t rBar r u hκ hh ht0 ht1 hrr hrR hrr_diff hM hN4 huc hu0 hgrow hu1 hu2
      hD1 hD2
  have hpi_sq (b : ℝ) (d : Dis[N, M]) :
      ∫ p : Fin 2 → ℝ^(N + 1), (((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫ - b) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => G t d) =
      ∫ p : ℝ^(N + 1) × ℝ^(N + 1), (((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ - b) ^ 2
        ∂((G t d).prod (G t d)) :=
    integral_pi_pair_eq_prod (G t d) (show (0 : Fin 2) ≠ 1 by decide)
      (fun x y => (((N : ℝ) + 1)⁻¹ * ⟪x, y⟫ - b) ^ 2) (by fun_prop)
  have hpi_int (d : Dis[N, M]) : Integrable (fun p : Fin 2 → ℝ^(N + 1) =>
      (((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫ - q_t) ^ 2) (Measure.pi fun _ : Fin 2 => G t d) :=
    integrable_sq_scaled_inner_sub_pi (G t d) (((N : ℝ) + 1)⁻¹) q_t
      (integrable_norm_pow_shcherbinaTirozziCavity (h := h) hκ0 hrr ⟨ht0, ht1⟩ hum hu0 2 d)
  refine (sqrt_integral_integral_sub_sq_le_of_le_div (P := cavLaw[N, M, r])
    (G := fun d => Measure.pi fun _ : Fin 2 => G t d)
    (X := fun p : Fin 2 → ℝ^(N + 1) => ((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫) hK_c
    (((measurable_pi_apply (0 : Fin 2)).inner (measurable_pi_apply (1 : Fin 2))).const_mul _)
    hpi_int (hc_i.congr (ae_of_all _ fun d => (hpi_sq q_t d).symm))
    ((integral_congr_ae (ae_of_all _ (hpi_sq q_t))).trans_le hc_le) hdiff).trans_eq ?_
  field_simp
  ring

/-- **Eq. (3.115) along the path:** with `M + 1` constraints at the parameters (3.69), and
`(q, ρ)` the overlaps at `t = 1`, the averages of `ε₁²` and `ε₁ ε₂` change by at most
`K / √(N + 1)` between `t = 0` and `t = 1`. -/
private theorem exists_abs_shcherbinaTirozziCavity_last_one_sub_zero_le (κ₀ h₀ D Q : ℝ)
    (hκ₀ : 0 < κ₀) (hQ : 0 ≤ Q) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ) (κ h q ρ r rBar : ℝ) (u : ℝ → ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ q → q ≤ ρ → ρ ≤ Q → M + 1 ≤ 10 * (N + 1) → 4 ≤ N + 1 →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → (∀ x, -D * (1 + |x|) ≤ u x) →
      Differentiable ℝ u → Differentiable ℝ (deriv u) →
      Differentiable ℝ (deriv (deriv u)) → Differentiable ℝ (deriv (deriv (deriv u))) →
      (∀ x, |deriv u x| ≤ D) → (∀ x, |deriv (deriv u) x| ≤ D) →
      (∀ x, |deriv (deriv (deriv u)) x| ≤ D) →
      (∀ x, |deriv (deriv (deriv (deriv u))) x| ≤ D) →
      let c : ℝ := Real.sqrt (ρ - q)
      let Z : ℝ → ℝ := fun y => ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)
      let V : ℝ → ℝ := fun y =>
        (∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z y
      let W : ℝ → ℝ := fun y => (∫ ξ, (deriv (deriv u) (y + c * ξ) + deriv u (y + c * ξ) ^ 2) *
        Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z y
      r = ((M : ℝ) + 1) / ((N : ℝ) + 1) *
        ∫ z, V (Real.sqrt q * z) ^ 2 ∂(gaussianReal 0 1) →
      rBar = ((M : ℝ) + 1) / ((N : ℝ) + 1) * ∫ z, W (Real.sqrt q * z) ∂(gaussianReal 0 1) →
      let G (s : ℝ) (d : Dis[N, M + 1]) : Measure (ℝ^(N + 1)) :=
        volume.tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r.toNNReal rBar s d.1 u d.2.1 d.2.2 σ
      let P := cavLaw[N, M + 1, r.toNNReal]
      ∫ d, ∫ x : ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 ∂(G 1 d) ∂P = ρ →
      ∫ d, ∫ p : Fin 2 → ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫
        ∂(Measure.pi fun _ : Fin 2 => G 1 d) ∂P = q →
      |(∫ d, ∫ x : ℝ^(N + 1), x (Fin.last N) ^ 2 ∂(G 1 d) ∂P) -
          ∫ d, ∫ x : ℝ^(N + 1), x (Fin.last N) ^ 2 ∂(G 0 d) ∂P| ≤
          K / Real.sqrt ((N : ℝ) + 1) ∧
        |(∫ d, ∫ σ : Fin 2 → ℝ^(N + 1), (σ 0) (Fin.last N) * (σ 1) (Fin.last N)
              ∂(Measure.pi fun _ : Fin 2 => G 1 d) ∂P) -
          ∫ d, ∫ σ : Fin 2 → ℝ^(N + 1), (σ 0) (Fin.last N) * (σ 1) (Fin.last N)
              ∂(Measure.pi fun _ : Fin 2 => G 0 d) ∂P| ≤
          K / Real.sqrt ((N : ℝ) + 1) := by
  set R : ℝ := 10 * D ^ 2
  set R_diff : ℝ := 10 * (2 * D ^ 2 + |D|)
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hRdiff0 : 0 ≤ R_diff := by dsimp only [R_diff]; positivity
  obtain ⟨K_sq, hK_sq, hprop_sq⟩ :=
    exists_hasDerivAt_shcherbinaTirozziCavity_sq_last_abs_le κ₀ h₀ D Q hκ₀ hQ
  obtain ⟨K_mul, hK_mul, hprop_mul⟩ :=
    exists_hasDerivAt_shcherbinaTirozziCavity_mul_last_abs_le κ₀ h₀ D Q hκ₀ hQ
  obtain ⟨K_self, hK_self, hself⟩ :=
    exists_sqrt_integral_shcherbinaTirozziCavity_selfOverlap_sub_one_sq_le κ₀ h₀ D R R_diff hκ₀
      hR0 hRdiff0
  obtain ⟨K_ov, hK_ov, hov⟩ :=
    exists_sqrt_integral_shcherbinaTirozziCavity_overlap_sub_one_sq_le κ₀ h₀ D R R_diff hκ₀
      hR0 hRdiff0
  set E : ℝ := K_ov + K_self + 1
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  set K : ℝ := max K_sq K_mul * E + 1
  have hK0 : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK0, fun N M κ h q ρ r rBar u hκ hh hq0 hqρ hρQ hM hN4 huc hu0 hgrow hu1 hu2 hu3
    hu4 hD1 hD2 hD3 hD4 => ?_⟩
  intro c Z V W hr_def hrBar_def G P hρ hq
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum : Measurable u := hu1.continuous.measurable
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD1 0)
  -- bounds on the parameters (3.69)
  set α : ℝ := ((M : ℝ) + 1) / ((N : ℝ) + 1) with hα
  have hα0 : 0 ≤ α := by positivity
  have hα10 : α ≤ 10 := by
    rw [hα, div_le_iff₀ (by positivity)]
    exact_mod_cast hM
  obtain ⟨hr0, hrD, hrr, hrBar⟩ :
      0 ≤ r ∧ r ≤ α * D ^ 2 ∧ rBar ≤ r ∧ -(α * (D + D ^ 2)) ≤ rBar := by
    rw [hr_def, hrBar_def]
    exact shcherbinaTirozzi_rsParameters_bounds huc hu0 hu1 hu2 hD1 hD2 hα0 q c
  have hrR : r ≤ R := hrD.trans (mul_le_mul_of_nonneg_right hα10 (sq_nonneg D))
  have hrr_diff : r - rBar ≤ R_diff := by
    have h1 : r - rBar ≤ α * (2 * D ^ 2 + |D|) := by
      rw [abs_of_nonneg hD0]; linarith
    exact h1.trans (mul_le_mul_of_nonneg_right hα10 (by positivity))
  have huD : -D ≤ u 0 := by simpa only [abs_zero, add_zero, mul_one] using hgrow 0
  have hr_coe : (r.toNNReal : ℝ) = r := Real.coe_toNNReal r hr0
  have hrr' : rBar ≤ (r.toNNReal : ℝ) := by rwa [hr_coe]
  have hprob : ∀ s ∈ Icc (0 : ℝ) 1, ∀ d : Dis[N, M + 1], IsProbabilityMeasure (G s d) :=
    fun s hs d => isProbabilityMeasure_tilted
      (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ0
        (mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 hrr')) hum hu0 d.2.1 d.2.2)
  -- the error term of Proposition 3.2.10, Eq. (3.107)
  have hErr : ∀ t ∈ Ioo (0 : ℝ) 1,
      Real.sqrt (∫ d, ∫ p : Fin 2 → ℝ^(N + 1), (((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫ - q) ^ 2
          ∂(Measure.pi fun _ : Fin 2 => G t d) ∂P) +
        Real.sqrt (∫ d, ∫ x : ℝ^(N + 1), (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - ρ) ^ 2 ∂(G t d) ∂P) +
        ((N : ℝ) + 1)⁻¹ ≤ E / Real.sqrt ((N : ℝ) + 1) := by
    intro t ht
    have h1 := hov N (M + 1) κ h t rBar r.toNNReal u hκ hh ht.1.le ht.2.le hrr'
      (by rwa [hr_coe]) (by rwa [hr_coe]) hM hN4 huc hu0 hgrow hu1 hu2 hD1 hD2 q
    have h2 := hself N (M + 1) κ h t rBar r.toNNReal u hκ hh ht.1.le ht.2.le hrr'
      (by rwa [hr_coe]) (by rwa [hr_coe]) hM hN4 huc hu0 hgrow hu1 hu2 hD1 hD2 ρ
    dsimp only [G, P] at hρ hq
    rw [hq, sub_self, abs_zero, mul_zero, add_zero] at h1
    rw [hρ, sub_self, abs_zero, mul_zero, add_zero] at h2
    have h3 : ((N : ℝ) + 1)⁻¹ ≤ 1 / Real.sqrt ((N : ℝ) + 1) := by
      have h1N : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
      rw [one_div]
      exact inv_anti₀ (Real.sqrt_pos.2 (by positivity))
        (Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩)
    refine (add_le_add (add_le_add h1 h2) h3).trans_eq ?_
    dsimp only [E]; ring
  -- a derivative bounded by the error term gives the increment bound
  have hstep : ∀ (φ : ℝ → ℝ) (K' : ℝ), 0 ≤ K' → K' ≤ max K_sq K_mul →
      ContinuousOn φ (Icc 0 1) →
      (∀ t ∈ Ioo (0 : ℝ) 1, ∃ d, HasDerivAt φ d t ∧
        |d| ≤ K' * (E / Real.sqrt ((N : ℝ) + 1))) →
      |φ 1 - φ 0| ≤ K / Real.sqrt ((N : ℝ) + 1) := by
    intro φ K' hK'0 hK' hcont hder
    have hmv := abs_sub_le_of_continuousOn_Icc_of_hasDerivAt_Ioo hcont hder
      (x := 0) (y := 1) ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
    rw [sub_zero, abs_one, mul_one, ← mul_div_assoc] at hmv
    refine hmv.trans (div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    exact (mul_le_mul_of_nonneg_right hK' hE0).trans (le_add_of_nonneg_right zero_le_one)
  have hlast : ∀ x : ℝ^(N + 1), |x (Fin.last N)| ≤ 1 + ‖x‖ := fun x => by
    have h := PiLp.norm_apply_le x (Fin.last N)
    rw [Real.norm_eq_abs] at h
    linarith
  have hlast_m : Measurable fun x : ℝ^(N + 1) => x (Fin.last N) :=
    (PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable
  constructor
  · refine hstep (fun s => ∫ d, ∫ x : ℝ^(N + 1), x (Fin.last N) ^ 2 ∂(G s d) ∂P) K_sq hK_sq.le
      (le_max_left _ _) ?_ fun t ht => ?_
    · have hc := continuousOn_integral_integral_pi_shcherbinaTirozziCavity (R := Fin 1)
        (N := N) (M := M + 1) (h := h) hκ0 r.toNNReal hrr' hu0 hu1 hD1
        (f := fun σ => (σ 0) (Fin.last N) ^ 2)
        ((hlast_m.comp (measurable_pi_apply 0)).pow_const 2) (C := 1) (m := 2) fun σ => by
          rw [one_mul, Fin.prod_univ_one, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hlast _) 2
      refine hc.congr fun s hs => integral_congr_ae (ae_of_all _ fun d => ?_)
      have := hprob s hs d
      exact (integral_pi_eval (G s d) (0 : Fin 1) (fun x : ℝ^(N + 1) => x (Fin.last N) ^ 2)
        (hlast_m.pow_const 2).aestronglyMeasurable).symm
    · subst hr_def hrBar_def
      obtain ⟨d, hd, hbd⟩ := hprop_sq N M κ h t q ρ u hκ hh ht.1 ht.2 hq0 hqρ hρQ (by omega)
        huc hu0 hu1 hu2 hu3 hu4 hD1 hD2 hD3 hD4 huD
      exact ⟨d, hd, hbd.trans (mul_le_mul_of_nonneg_left (hErr t ht) hK_sq.le)⟩
  · refine hstep (fun s => ∫ d, ∫ σ : Fin 2 → ℝ^(N + 1), (σ 0) (Fin.last N) * (σ 1) (Fin.last N)
      ∂(Measure.pi fun _ : Fin 2 => G s d) ∂P) K_mul hK_mul.le (le_max_right _ _) ?_
      fun t ht => ?_
    · exact continuousOn_integral_integral_pi_shcherbinaTirozziCavity (R := Fin 2)
        (N := N) (M := M + 1) (h := h) hκ0 r.toNNReal hrr' hu0 hu1 hD1
        (f := fun σ => (σ 0) (Fin.last N) * (σ 1) (Fin.last N))
        ((hlast_m.comp (measurable_pi_apply 0)).mul (hlast_m.comp (measurable_pi_apply 1)))
        (C := 1) (m := 1) fun σ => by
          rw [one_mul, Fin.prod_univ_two, pow_one, pow_one, abs_mul]
          exact mul_le_mul (hlast _) (hlast _) (abs_nonneg _) (by positivity)
    · subst hr_def hrBar_def
      obtain ⟨d, hd, hbd⟩ := hprop_mul N M κ h t q ρ u hκ hh ht.1 ht.2 hq0 hqρ hρQ (by omega)
        huc hu0 hu1 hu2 hu3 hu4 hD1 hD2 hD3 hD4 huD
      exact ⟨d, hd, hbd.trans (mul_le_mul_of_nonneg_left (hErr t ht) hK_mul.le)⟩

/-- **Talagrand, Proposition 3.2.12 (Eq. (3.115)):** at the physical parameters `(q, ρ, r, r̄)`
for the Shcherbina--Tirozzi model on `ℝ^(N+1)` with `M` constraints (`M ≤ 10 (N + 1)`), the
replica-symmetric equations (3.69), (3.76), (3.77) hold with accuracy `K / √(N + 1)`:
```
|ρ - (1 / a + (r + h²) / a²)| ≤ K / √(N + 1),
|q - (r + h²) / a²| ≤ K / √(N + 1),
```
where `a = 2 κ + r - r̄ > 0`, and `K > 0` depends only on `κ₀, h₀, D`. -/
theorem exists_shcherbinaTirozzi_rsEquations_accuracy (κ₀ h₀ D : ℝ) (hκ₀ : 0 < κ₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ) (κ h : ℝ) (u : ℝ → ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → M ≤ 10 * (N + 1) →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → (∀ x, -D * (1 + |x|) ≤ u x) →
      Differentiable ℝ u → Differentiable ℝ (deriv u) →
      Differentiable ℝ (deriv (deriv u)) → Differentiable ℝ (deriv (deriv (deriv u))) →
      (∀ x, |deriv u x| ≤ D) → (∀ x, |deriv (deriv u) x| ≤ D) →
      (∀ x, |deriv (deriv (deriv u)) x| ≤ D) →
      (∀ x, |deriv (deriv (deriv (deriv u))) x| ≤ D) →
      let P : Measure ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) :=
        (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
      let G : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) → Measure (ℝ^(N + 1)) := fun d =>
        volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u d.1 d.2 σ
      let ρ : ℝ := ∫ d, ∫ σ, ((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 ∂(G d) ∂P
      let q : ℝ := ∫ d, ((N : ℝ) + 1)⁻¹ * ∑ i, (∫ σ, σ i ∂(G d)) ^ 2 ∂P
      let c : ℝ := Real.sqrt (ρ - q)
      let Z : ℝ → ℝ := fun y => ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)
      let V : ℝ → ℝ := fun y =>
        (∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z y
      let W : ℝ → ℝ := fun y => (∫ ξ, (deriv (deriv u) (y + c * ξ) + deriv u (y + c * ξ) ^ 2) *
        Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z y
      let r : ℝ := (M / (N + 1)) * ∫ z, V (Real.sqrt q * z) ^ 2 ∂(gaussianReal 0 1)
      let rBar : ℝ := (M / (N + 1)) * ∫ z, W (Real.sqrt q * z) ∂(gaussianReal 0 1)
      let a : ℝ := 2 * κ + r - rBar
      0 < a ∧
        |ρ - (a⁻¹ + (r + h ^ 2) / a ^ 2)| ≤ K / Real.sqrt ((N : ℝ) + 1) ∧
        |q - (r + h ^ 2) / a ^ 2| ≤ K / Real.sqrt ((N : ℝ) + 1) := by
  obtain ⟨Q, hQ0, hphys⟩ := exists_shcherbinaTirozzi_physical_parameter_bounds κ₀ h₀ D hκ₀
  obtain ⟨K_inc, hK_inc, hinc⟩ :=
    exists_abs_shcherbinaTirozziCavity_last_one_sub_zero_le κ₀ h₀ D Q hκ₀ hQ0
  set B : ℝ := Q + (2 * κ₀)⁻¹ + (10 * D ^ 2 + h₀ ^ 2) / (2 * κ₀) ^ 2
  have hB0 : 0 ≤ B := by positivity
  set K : ℝ := K_inc + 2 * B with hK
  have hK0 : 0 < K := by positivity
  refine ⟨K, hK0, fun N M κ h u hκ hh hM huc hu0 hgrow hu1 hu2 hu3 hu4 hD1 hD2 hD3 hD4 => ?_⟩
  intro P G ρ q c Z V W r rBar a
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum : Measurable u := hu1.continuous.measurable
  -- Physical parameter bounds
  obtain ⟨hq0, hqρ, hρQ, hr0, hrR, hrr, hrr_diff0⟩ :=
    hphys N M κ h D u hκ hh hM huc hu0 hgrow hu1 hu2 hD1 hD2
  have hr_coe : (r.toNNReal : ℝ) = r := Real.coe_toNNReal r hr0
  -- Proposition 3.2.4: the residuals are increments between `t = 0` and `t = 1`
  obtain ⟨ha_pos, hres_ρ, hres_q⟩ :=
    shcherbinaTirozzi_overlaps_sub_decoupled (N := N) (M := M) (κ := κ) (h := h) (D := D) (D₂ := D)
      hκ0 hM huc hu0 hgrow hu1 hu2 hD1 hD2
  have hres_ρ' : ρ - (a⁻¹ + (r + h ^ 2) / a ^ 2) =
      (∫ d, ∫ σ, σ (Fin.last N) ^ 2 ∂(G d) ∂P) -
        ∫ y, ∫ d, ∫ σ, σ (Fin.last N) ^ 2 ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar 0 y u d.1 d.2 σ) ∂P
          ∂(gaussianReal 0 r.toNNReal) := hres_ρ
  have hres_q' : q - (r + h ^ 2) / a ^ 2 =
      (∫ d, (∫ σ, σ (Fin.last N) ∂(G d)) ^ 2 ∂P) -
        ∫ y, ∫ d, (∫ σ, σ (Fin.last N) ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar 0 y u d.1 d.2 σ)) ^ 2 ∂P
          ∂(gaussianReal 0 r.toNNReal) := hres_q
  refine ⟨ha_pos, ?_⟩
  by_cases hN4 : 4 ≤ N + 1
  swap
  -- For `N + 1 < 4` it is enough that the residuals are bounded.
  · have hsqrt : Real.sqrt ((N : ℝ) + 1) ≤ 2 := by
      have hN : (N : ℝ) ≤ 2 := by exact_mod_cast (show N ≤ 2 by omega)
      exact Real.sqrt_le_iff.2 ⟨zero_le_two, by linarith⟩
    have hBK : B ≤ K / Real.sqrt ((N : ℝ) + 1) := by
      rw [le_div_iff₀ (Real.sqrt_pos.2 (by positivity))]
      have h2 := mul_le_mul_of_nonneg_left hsqrt hB0
      linarith
    have hres := abs_sub_rsEquations_le_of_bounds hκ₀ hκ hh hq0 hqρ hρQ hr0 hrR hrr
    exact ⟨hres.1.trans hBK, hres.2.trans hBK⟩
  have hKK : K_inc / Real.sqrt ((N : ℝ) + 1) ≤ K / Real.sqrt ((N : ℝ) + 1) :=
    div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
  rw [hres_ρ', hres_q']
  rcases M with _ | M
  -- With no constraint the cavity path is constant, so both increments vanish.
  · have hr_zero : r = 0 := by dsimp only [r]; simp
    have hrBar_zero : rBar = 0 := by dsimp only [rBar]; simp
    have hy0 : gaussianReal 0 r.toNNReal = Measure.dirac 0 := by
      rw [hr_zero, Real.toNNReal_zero, gaussianReal_zero_var]
    have hG0 (d : (Fin 0 → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) :
        ((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h 0 0 0 0 u d.1 d.2 σ) = G d := by
      dsimp only [G]
      congr 1
      funext σ
      rw [shcherbinaTirozziCavityHamiltonian_zero_of_last_eq_zero κ h 0 u fun k => k.elim0]
    rw [hy0, integral_dirac, integral_dirac, hr_zero, hrBar_zero]
    simp only [hG0, sub_self, abs_zero]
    exact ⟨by positivity, by positivity⟩
  have : ∀ e : (Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ), IsProbabilityMeasure (G e) :=
    fun e => isProbabilityMeasure_shcherbinaTirozziGibbs hκ0 hum hu0 _ _
  set law := cavLaw[N, M + 1, r.toNNReal] with hlaw
  set Gc : ℝ → Dis[N, M + 1] → Measure (ℝ^(N + 1)) := fun s d =>
    volume.tilted fun σ =>
      -shcherbinaTirozziCavityHamiltonian κ h r.toNNReal rBar s d.1 u d.2.1 d.2.2 σ with hGc
  -- averages at `t = 1` are averages for the model
  have hone (Φ : Measure (ℝ^(N + 1)) → ℝ) : ∫ d, Φ (Gc 1 d) ∂law = ∫ e, Φ (G e) ∂P :=
    integral_apply_shcherbinaTirozziCavity_one κ h r.toNNReal rBar u
      (gaussianReal 0 r.toNNReal) P Φ
  have hρ1 : ∫ d, ∫ x : ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 ∂(Gc 1 d) ∂law = ρ :=
    hone fun μ => ∫ x, ((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 ∂μ
  have hq1 : ∫ d, ∫ p : Fin 2 → ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫
      ∂(Measure.pi fun _ : Fin 2 => Gc 1 d) ∂law = q := by
    refine (hone fun μ => ∫ p : Fin 2 → ℝ^(N + 1), ((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫
      ∂(Measure.pi fun _ : Fin 2 => μ)).trans (integral_congr_ae (ae_of_all _ fun e => ?_))
    have hi : Integrable (fun σ : ℝ^(N + 1) => σ) (G e) :=
      (memLp_id_shcherbinaTirozziGibbs (h := h) hκ0 hum hu0 e.1 e.2).integrable one_le_two
    exact (integral_pi_overlap_eq_mean_sq_inner (G e) hi rfl _
      (show (0 : Fin 2) ≠ 1 by decide)).trans
      (by rw [real_inner_self_eq_norm_sq, norm_integral_sq_eq_sum_sq hi])
  have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := Nat.cast_add_one M
  obtain ⟨hsq, hmul⟩ := hinc N M κ h q ρ r rBar u hκ hh hq0 hqρ hρQ hM hN4 huc hu0 hgrow hu1 hu2
    hu3 hu4 hD1 hD2 hD3 hD4 (by simp only [r, V, Z, c, hcast])
    (by simp only [rBar, W, Z, c, hcast]) hρ1 hq1
  -- identify the four averages
  have hrr' : rBar ≤ (r.toNNReal : ℝ) := by rwa [hr_coe]
  have hlast_m : Measurable fun x : ℝ^(N + 1) => x (Fin.last N) :=
    (PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable
  have hlast : ∀ x : ℝ^(N + 1), |x (Fin.last N)| ≤ 1 + ‖x‖ := fun x => by
    have h := PiLp.norm_apply_le x (Fin.last N)
    rw [Real.norm_eq_abs] at h
    linarith
  have hsq1 : ∫ d, ∫ x : ℝ^(N + 1), x (Fin.last N) ^ 2 ∂(Gc 1 d) ∂law =
      ∫ e, ∫ x : ℝ^(N + 1), x (Fin.last N) ^ 2 ∂(G e) ∂P :=
    hone fun μ => ∫ x, x (Fin.last N) ^ 2 ∂μ
  have hmul1 : ∫ d, ∫ σ : Fin 2 → ℝ^(N + 1), (σ 0) (Fin.last N) * (σ 1) (Fin.last N)
        ∂(Measure.pi fun _ : Fin 2 => Gc 1 d) ∂law =
      ∫ e, (∫ x : ℝ^(N + 1), x (Fin.last N) ∂(G e)) ^ 2 ∂P :=
    (hone fun μ => ∫ σ : Fin 2 → ℝ^(N + 1), (σ 0) (Fin.last N) * (σ 1) (Fin.last N)
      ∂(Measure.pi fun _ : Fin 2 => μ)).trans (integral_congr_ae (ae_of_all _ fun e =>
        (integral_pi_fin_two_mul_fun (G e) (fun x => x (Fin.last N))
          (fun x => x (Fin.last N))).trans (sq _).symm))
  have hprob0 : ∀ d, IsProbabilityMeasure (Gc 0 d) := fun d => isProbabilityMeasure_tilted
    (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ0
      (mul_nonneg (sub_nonneg.2 zero_le_one) (sub_nonneg.2 hrr')) hum hu0 d.2.1 d.2.2)
  have hsq0 : ∫ d, ∫ x : ℝ^(N + 1), x (Fin.last N) ^ 2 ∂(Gc 0 d) ∂law =
      ∫ y, ∫ d, ∫ σ, σ (Fin.last N) ^ 2 ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar 0 y u d.1 d.2 σ) ∂P
        ∂(gaussianReal 0 r.toNNReal) := by
    have hone_replica (μ : Measure (ℝ^(N + 1))) [IsProbabilityMeasure μ] :
        ∫ σ : Fin 1 → ℝ^(N + 1), (σ 0) (Fin.last N) ^ 2 ∂(Measure.pi fun _ : Fin 1 => μ) =
          ∫ x : ℝ^(N + 1), x (Fin.last N) ^ 2 ∂μ :=
      integral_pi_eval μ (0 : Fin 1) (fun x : ℝ^(N + 1) => x (Fin.last N) ^ 2)
        (hlast_m.pow_const 2).aestronglyMeasurable
    have hz := integral_integral_pi_shcherbinaTirozziCavity_eq_iterated (R := Fin 1) (N := N)
      (M := M + 1) (t := 0) (h := h) hκ0 hrr' ⟨le_rfl, zero_le_one⟩ hu0 hu1 hD1
      (f := fun _ σ => (σ 0) (Fin.last N) ^ 2)
      ((hlast_m.comp ((measurable_pi_apply 0).comp measurable_snd)).pow_const 2)
      (C := 1) (m := 2) fun _ σ => by
        rw [one_mul, Fin.prod_univ_one, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hlast _) 2
    refine (integral_congr_ae (ae_of_all _ fun d => ?_)).trans
      (hz.trans (integral_congr_ae (ae_of_all _ fun y =>
        integral_congr_ae (ae_of_all _ fun e => ?_))))
    · have := hprob0 d
      exact (hone_replica (Gc 0 d)).symm
    · have : IsProbabilityMeasure ((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar 0 y u e.1 e.2 σ) := by
        simpa only [Gc, hr_coe] using hprob0 (y, e)
      rw [hr_coe]
      exact hone_replica _
  have hmul0 : ∫ d, ∫ σ : Fin 2 → ℝ^(N + 1), (σ 0) (Fin.last N) * (σ 1) (Fin.last N)
        ∂(Measure.pi fun _ : Fin 2 => Gc 0 d) ∂law =
      ∫ y, ∫ d, (∫ σ, σ (Fin.last N) ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar 0 y u d.1 d.2 σ)) ^ 2 ∂P
        ∂(gaussianReal 0 r.toNNReal) := by
    have hz := integral_integral_pi_shcherbinaTirozziCavity_eq_iterated (R := Fin 2) (N := N)
      (M := M + 1) (t := 0) (h := h) hκ0 hrr' ⟨le_rfl, zero_le_one⟩ hu0 hu1 hD1
      (f := fun _ σ => (σ 0) (Fin.last N) * (σ 1) (Fin.last N))
      ((hlast_m.comp ((measurable_pi_apply 0).comp measurable_snd)).mul
        (hlast_m.comp ((measurable_pi_apply 1).comp measurable_snd)))
      (C := 1) (m := 1) fun _ σ => by
        rw [one_mul, Fin.prod_univ_two, pow_one, pow_one, abs_mul]
        exact mul_le_mul (hlast _) (hlast _) (abs_nonneg _) (by positivity)
    refine hz.trans (integral_congr_ae (ae_of_all _ fun y =>
      integral_congr_ae (ae_of_all _ fun e => ?_)))
    have : IsProbabilityMeasure ((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar 0 y u e.1 e.2 σ) := by
      simpa only [Gc, hr_coe] using hprob0 (y, e)
    rw [hr_coe]
    exact (integral_pi_fin_two_mul_fun _ (fun x : ℝ^(N + 1) => x (Fin.last N))
      (fun x : ℝ^(N + 1) => x (Fin.last N))).trans (sq _).symm
  rw [← hsq1, ← hmul1, ← hsq0, ← hmul0]
  exact ⟨hsq.trans hKK, hmul.trans hKK⟩

end Proposition3212

end SpinGlasses
