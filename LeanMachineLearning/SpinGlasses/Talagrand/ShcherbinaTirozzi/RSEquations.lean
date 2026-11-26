/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.LogSmoothing
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.LastSpinTail
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.Moments

/-!
# The Shcherbina--Tirozzi model: the replica-symmetric choice of the parameters

Statements of Talagrand, *Spin Glasses*, Vol. I, Section 3.2, at the choice (3.69)
`r = Ψ (q, ρ)`, `r̄ = Ψ̄ (q, ρ)` of the parameters of the cavity path. With `c = √(ρ - q)`,
`Z y = 𝔼 e^{u (y + c ξ)}`, `V y = 𝔼 u' e^{u} / Z y` and `W y = 𝔼 (u'' + u'²) e^{u} / Z y`, one has
`r = α 𝔼 V (√q z)²` and `r̄ = α 𝔼 W (√q z)`.

## Main declarations

* `SpinGlasses.shcherbinaTirozzi_rsParameters_bounds`: `0 ≤ r ≤ α D²` and `r̄ ≤ r`.
* `SpinGlasses.exists_integral_exp_sq_shcherbinaTirozziCavity_last_le_of_rsParameters`:
  Lemma 3.2.6 at this choice, with a constant depending only on `κ₀`, `h₀` and `D`.
* `SpinGlasses.shcherbinaTirozzi_overlaps_sub_decoupled`: Proposition 3.2.4, the overlaps minus
  their values at the decoupled end are the increments of the last-spin averages along the path.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SpinGlasses

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

/-- **The choice (3.69) of the parameters** satisfies `0 ≤ r ≤ α D²` and `r̄ ≤ r`, for every
`q` and every smoothing scale `c` (the book takes `c = √(ρ - q)`). -/
theorem shcherbinaTirozzi_rsParameters_bounds {u : ℝ → ℝ} (hu : ConcaveOn ℝ Set.univ u)
    (hu0 : ∀ x, u x ≤ 0) (hu1 : Differentiable ℝ u) (hu2 : Differentiable ℝ (deriv u))
    {D D₂ : ℝ} (hD : ∀ x, |deriv u x| ≤ D) (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) {α : ℝ}
    (hα : 0 ≤ α) (q c : ℝ) :
    let Z : ℝ → ℝ := fun y => ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)
    let V : ℝ → ℝ := fun y =>
      (∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z y
    let W : ℝ → ℝ := fun y => (∫ ξ, (deriv (deriv u) (y + c * ξ) + deriv u (y + c * ξ) ^ 2) *
      Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z y
    let r : ℝ := α * ∫ z, V (Real.sqrt q * z) ^ 2 ∂(gaussianReal 0 1)
    let rBar : ℝ := α * ∫ z, W (Real.sqrt q * z) ∂(gaussianReal 0 1)
    0 ≤ r ∧ r ≤ α * D ^ 2 ∧ rBar ≤ r := by
  intro Z V W r rBar
  have hum : Measurable u := hu1.continuous.measurable
  have hVD : ∀ y, |V y| ≤ D := fun y => abs_integral_mul_exp_comp_add_div_le hD
    (integrable_exp_comp_add_gaussianReal hum hu0 y c)
  refine ⟨mul_nonneg hα (integral_nonneg fun _ => sq_nonneg _),
    mul_le_mul_of_nonneg_left ?_ hα, mul_le_mul_of_nonneg_left
      (integral_deriv_two_add_sq_div_le_integral_sq_div (μ := gaussianReal 0 1) hu hu1 hu2
        hD hD₂ (a := fun z => Real.sqrt q * z) (by fun_prop) c) hα⟩
  refine (integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) (integrable_const (D ^ 2))
    (ae_of_all _ fun z => ?_)).trans_eq (by simp)
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hVD (Real.sqrt q * z)) 2

/-- **Talagrand, Lemma 3.2.6, at the choice (3.69):** `ν_t (exp (ε² / K)) ≤ K` with `K`
depending only on `κ₀`, `h₀` and `D`, uniformly in the size, in `t ∈ [0, 1]` and in `q`, `ρ`. -/
theorem exists_integral_exp_sq_shcherbinaTirozziCavity_last_le_of_rsParameters (κ₀ h₀ D : ℝ)
    (hκ₀ : 0 < κ₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ) (κ h t q ρ : ℝ) (u : ℝ → ℝ) (D₂ : ℝ), κ₀ ≤ κ → |h| ≤ h₀ →
      0 ≤ t → t ≤ 1 → M ≤ 10 * (N + 1) →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → Differentiable ℝ u →
      Differentiable ℝ (deriv u) → (∀ x, |deriv u x| ≤ D) → (∀ x, |deriv (deriv u) x| ≤ D₂) →
      let c : ℝ := Real.sqrt (ρ - q)
      let Z : ℝ → ℝ := fun y => ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)
      let V : ℝ → ℝ := fun y =>
        (∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z y
      let W : ℝ → ℝ := fun y => (∫ ξ, (deriv (deriv u) (y + c * ξ) + deriv u (y + c * ξ) ^ 2) *
        Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z y
      let r : ℝ := (M / (N + 1)) * ∫ z, V (Real.sqrt q * z) ^ 2 ∂(gaussianReal 0 1)
      let rBar : ℝ := (M / (N + 1)) * ∫ z, W (Real.sqrt q * z) ∂(gaussianReal 0 1)
      let P : Measure (ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) :=
        (gaussianReal 0 r.toNNReal).prod
          ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))
      let F : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) → ℝ := fun p =>
        ∫ σ, Real.exp (σ (Fin.last N) ^ 2 / K)
          ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
            -shcherbinaTirozziCavityHamiltonian κ h r rBar t p.1 u p.2.1 p.2.2 σ)
      Integrable F P ∧ ∫ p, F p ∂P ≤ K := by
  obtain ⟨K, hK0, hK⟩ := exists_integral_exp_sq_shcherbinaTirozziCavity_last_le κ₀ h₀ D
    (10 * D ^ 2) hκ₀ (by positivity)
  refine ⟨K, hK0, fun N M κ h t q ρ u D₂ hκ hh ht0 ht1 hM huc hu0 hu1 hu2 hD hD₂ => ?_⟩
  intro c Z V W r rBar P F
  have hα : (0 : ℝ) ≤ M / (N + 1) := by positivity
  have hα10 : (M : ℝ) / (N + 1) ≤ 10 := by
    rw [div_le_iff₀ (by positivity)]
    exact_mod_cast hM
  obtain ⟨hr0, hrD, hrr⟩ : 0 ≤ r ∧ r ≤ M / (N + 1) * D ^ 2 ∧ rBar ≤ r :=
    shcherbinaTirozzi_rsParameters_bounds huc hu0 hu1 hu2 hD hD₂ hα q c
  have hr : (r.toNNReal : ℝ) = r := Real.coe_toNNReal r hr0
  have h := hK N M κ h t rBar r.toNNReal u hκ hh ht0 ht1 (by rwa [hr])
    (by rw [hr]; exact hrD.trans (mul_le_mul_of_nonneg_right hα10 (sq_nonneg D))) hM huc hu0
    hu1 hD
  simp only [hr] at h
  exact h

/-- **Talagrand, Proposition 3.2.4**, for the model with `N + 1` spins at the choice (3.69) of
the parameters, `ρ` and `q` being the quenched self-overlap and overlap. With
`a = 2 κ + r - r̄ > 0`, the differences `ρ - (1 / a + (r + h²) / a²)` and `q - (r + h²) / a²`
are the increments of `ν_t (ε²)` and `ν_t (⟨ε⟩²)` from `t = 0` to `t = 1`. -/
theorem shcherbinaTirozzi_overlaps_sub_decoupled {N M : ℕ} {κ h D D₂ : ℝ} (hκ : 0 < κ)
    (hM : M ≤ 10 * (N + 1)) {u : ℝ → ℝ} (huc : ConcaveOn ℝ Set.univ u)
    (hu0 : ∀ x, u x ≤ 0) (hgrow : ∀ x, -D * (1 + |x|) ≤ u x) (hu1 : Differentiable ℝ u)
    (hu2 : Differentiable ℝ (deriv u)) (hD : ∀ x, |deriv u x| ≤ D)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) :
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
    let G₀ : ℝ → (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) → Measure (ℝ^(N + 1)) :=
      fun y d => volume.tilted fun σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar 0 y u d.1 d.2 σ
    0 < a ∧
      ρ - (a⁻¹ + (r + h ^ 2) / a ^ 2) =
        (∫ d, ∫ σ, σ (Fin.last N) ^ 2 ∂(G d) ∂P) -
          ∫ y, ∫ d, ∫ σ, σ (Fin.last N) ^ 2 ∂(G₀ y d) ∂P ∂(gaussianReal 0 r.toNNReal) ∧
      q - (r + h ^ 2) / a ^ 2 =
        (∫ d, (∫ σ, σ (Fin.last N) ∂(G d)) ^ 2 ∂P) -
          ∫ y, ∫ d, (∫ σ, σ (Fin.last N) ∂(G₀ y d)) ^ 2 ∂P ∂(gaussianReal 0 r.toNNReal) := by
  intro P G ρ q c Z V W r rBar a G₀
  have hum : Measurable u := hu1.continuous.measurable
  obtain ⟨hr0, -, hrr⟩ : 0 ≤ r ∧ r ≤ M / (N + 1) * D ^ 2 ∧ rBar ≤ r :=
    shcherbinaTirozzi_rsParameters_bounds huc hu0 hu1 hu2 hD hD₂ (by positivity) q c
  have hr : (r.toNNReal : ℝ) = r := Real.coe_toNNReal r hr0
  have ha : 0 < a := by
    change 0 < 2 * κ + r - rBar
    linarith
  -- the quenched second moment is finite
  have hint : Integrable (fun d => ∫ σ, ‖σ‖ ^ 2 ∂(G d)) P := by
    obtain ⟨K, hK0, hK⟩ := exists_integral_sq_norm_pow_shcherbinaTirozziGibbs_le κ |h| D hκ
    have hrad := (integral_shcherbinaTirozzi_radius_pow_le (N := N + 1) (M := M) hM
      (k := 1) (by omega)).1
    simp only [pow_one] at hrad
    refine (hrad.const_mul K).mono' (measurable_integral_tilted
      (e := fun (d : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) σ =>
        -shcherbinaTirozziHamiltonian κ h u d.1 d.2 σ)
      (measurable_shcherbinaTirozziHamiltonian κ h hum).neg
      (measurable_norm.pow_const 2)).aestronglyMeasurable (ae_of_all _ fun d => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
    have h1 := (hK (N + 1) M 1 κ h u d.1 d.2 le_rfl le_rfl hM (by omega) hum hu0 hgrow).2
    simpa only [mul_one, pow_one] using h1
  obtain ⟨hρ, hq⟩ := integral_shcherbinaTirozzi_overlaps_eq_last_spin (M := M) (N := N)
    (h := h) hκ hum hu0 G (fun _ => rfl) P rfl hint
  have ha' : 0 < 2 * κ + (r.toNNReal : ℝ) - rBar := by rwa [hr]
  have h0sq := integral_integral_shcherbinaTirozziCavityGibbs_zero_sq_last (M := M) (N := N)
    (h := h) (rBar := rBar) (r := r.toNNReal) hκ ha' hum hu0 P rfl
  have h0 := integral_integral_sq_shcherbinaTirozziCavityGibbs_zero_last (M := M) (N := N)
    (h := h) (rBar := rBar) (r := r.toNNReal) hκ ha' hum hu0 P rfl
  simp only [hr] at h0sq h0
  refine ⟨ha, ?_, ?_⟩
  · rw [show ρ = _ from hρ]
    exact congrArg _ h0sq.symm
  · rw [show q = _ from hq]
    exact congrArg _ h0.symm

end SpinGlasses
