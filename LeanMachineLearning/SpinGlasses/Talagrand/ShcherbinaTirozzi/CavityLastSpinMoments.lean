/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

import Mathlib.Analysis.MeanInequalities

public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.CavityLastSpinAssembly

/-!
# The Shcherbina--Tirozzi model: Proposition 3.2.10 for `ε₁²` and `ε₁ ε₂`

This file specializes `exists_hasDerivAt_shcherbinaTirozziCavity_abs_le_of_mul_last_sq_le`
(`CavityLastSpinAssembly.lean`) to `f(σ) = ε₁²` (1 replica) and `f(σ) = ε₁ ε₂` (2 replicas),
obtaining **Talagrand, Proposition 3.2.10** (Eq. (3.107)):
```
|ν_t'(f)| ≤ K * (√(ν_t((R_{1,2} - q)²)) + √(ν_t((R_{1,1} - ρ)²)) + (N + 1)⁻¹)
```
uniformly in `N, M, t`, with `K` depending only on `κ₀, h₀, D, Q, R, R_diff`.

The uniform `L²` bound on `(ε_a ε_b ε_c ε_d)²` along `ν_{t,s}` is derived directly from Eq. (3.100)
(`exists_integral_exp_sq_shcherbinaTirozziAuxCavity_last_le`) via the elementary AM-GM inequality
`(ε_a ε_b ε_c ε_d)² ≤ (ε_a⁸ + ε_b⁸ + ε_c⁸ + ε_d⁸) / 4` and `x⁸ / (4! K⁴) ≤ exp(x² / K)`.

## Main declarations

* `SpinGlasses.exists_hasDerivAt_shcherbinaTirozziCavity_sq_last_abs_le`: Proposition 3.2.10 for
  `f = ε₁²`.
* `SpinGlasses.exists_hasDerivAt_shcherbinaTirozziCavity_mul_last_abs_le`: Proposition 3.2.10 for
  `f = ε₁ ε₂`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal NNReal Topology RealInnerProductSpace Real

namespace SpinGlasses

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

/-- The disorder `((y, (g, g₀)), z)` of the auxiliary cavity system with `M + 1` constraints and
shared Gaussian `z`. -/
local notation "AuxDis[" N ", " M "]" =>
  (ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) × ℝ

/-- The law of `AuxDis` with `y ~ 𝒩(0, r)` and standard Gaussian `g, g₀, z`. -/
local notation "auxLaw[" N ", " M ", " r "]" =>
  Measure.prod
    (Measure.prod (gaussianReal 0 r)
      (Measure.prod
        (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)))
    (gaussianReal 0 1)

/-- The cavity field `S_{k,t}` on `ℝ^(N+1)`. -/
local notation "cfield[" N ", " t ", " g ", " k ", " σ "]" =>
  (Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, g k (Fin.castSucc i) * σ (Fin.castSucc i)) +
    Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N)))

/-- Elementary 4-factor AM-GM bound: `(a * b * c * d)² ≤ (a⁸ + b⁸ + c⁸ + d⁸) / 4`. -/
private lemma mul_four_sq_le_sum_pow_eight (a b c d : ℝ) :
    (a * b * c * d) ^ 2 ≤ (a ^ 8 + b ^ 8 + c ^ 8 + d ^ 8) / 4 := by
  have hp (x : ℝ) : (x ^ 8) ^ (1 / 4 : ℝ) = x ^ 2 := by
    have habs : |x| ^ 8 = x ^ 8 := (even_two_mul 4).pow_abs x
    rw [← habs, ← Real.rpow_natCast_mul (abs_nonneg _),
      show ((8 : ℕ) : ℝ) * (1 / 4) = 2 by norm_num, Real.rpow_two, sq_abs]
  have h := Real.geom_mean_le_arith_mean4_weighted
    (w₁ := 1 / 4) (w₂ := 1 / 4) (w₃ := 1 / 4) (w₄ := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (show 0 ≤ a ^ 8 by positivity) (show 0 ≤ b ^ 8 by positivity)
    (show 0 ≤ c ^ 8 by positivity) (show 0 ≤ d ^ 8 by positivity) (by norm_num)
  simp only [hp] at h
  convert h using 1 <;> ring

/-- Under `ν_{t,s}`, the second moment of any 4-fold product of last spins
`ε_{i₁} ε_{i₂} ε_{i₃} ε_{i₄}` is uniformly bounded by `24 * K_last ^ 5` via Eq. (3.100). -/
private lemma integrable_and_integral_mul_four_last_spin_sq_le
    {R_big : Type} [Fintype R_big] {N M : ℕ} {κ₀ κ h t s q ρ rBar K_last : ℝ} {r : ℝ≥0}
    {u : ℝ → ℝ} (hκ₀ : 0 < κ₀) (hκ : κ₀ ≤ κ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hrr : rBar ≤ r) (hum : Measurable u) (hu0 : ∀ x, u x ≤ 0)
    (hK_last_pos : 0 < K_last) (hK_last_ge : 16 / κ₀ ≤ K_last)
    (i₁ i₂ i₃ i₄ : R_big) :
    let E_old : AuxDis[N, M] → ℝ^(N + 1) → ℝ := fun w σ =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t w.1.1 u
        (fun j => w.1.2.1 j.castSucc) w.1.2.2 σ
    let S_v : AuxDis[N, M] → ℝ^(N + 1) × ℝ → ℝ := fun w p =>
      Real.sqrt s * cfield[N, t, w.1.2.1, Fin.last M, p.1] +
        Real.sqrt (1 - s) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2)
    let G_aux : AuxDis[N, M] → Measure (ℝ^(N + 1) × ℝ) := fun w =>
      ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
        fun p => E_old w p.1 + u (S_v w p)
    Integrable (fun w => ∫ p : ℝ^(N + 1) × ℝ, Real.exp (p.1 (Fin.last N) ^ 2 / K_last)
      ∂(G_aux w)) auxLaw[N, M, r] →
    (∫ w, ∫ p : ℝ^(N + 1) × ℝ, Real.exp (p.1 (Fin.last N) ^ 2 / K_last)
      ∂(G_aux w) ∂auxLaw[N, M, r] ≤ K_last) →
    Integrable (fun w => ∫ σ : R_big → ℝ^(N + 1) × ℝ,
        ((σ i₁).1 (Fin.last N) * (σ i₂).1 (Fin.last N) *
          (σ i₃).1 (Fin.last N) * (σ i₄).1 (Fin.last N)) ^ 2
        ∂(Measure.pi fun _ : R_big => G_aux w)) auxLaw[N, M, r] ∧
      ∫ w, ∫ σ : R_big → ℝ^(N + 1) × ℝ,
        ((σ i₁).1 (Fin.last N) * (σ i₂).1 (Fin.last N) *
          (σ i₃).1 (Fin.last N) * (σ i₄).1 (Fin.last N)) ^ 2
        ∂(Measure.pi fun _ : R_big => G_aux w) ∂auxLaw[N, M, r] ≤ 24 * K_last ^ 5 := by
  intro E_old S_v G_aux hlast_i hlast_le
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have ha_last : K_last⁻¹ < κ := by
    refine inv_lt_of_inv_lt₀ hκ0 (lt_of_lt_of_le ?_
      ((div_le_div_of_nonneg_left (by norm_num) hκ₀ hκ).trans hK_last_ge))
    rw [inv_eq_one_div]
    exact div_lt_div_of_pos_right (by norm_num) hκ0
  have hstate := shcherbinaTirozziAuxCavity_state_properties (R_rep := R_big) (N := N) (M := M)
    (h := h) hκ0 hrr ht0 ht1 hum hu0 ha_last (r := r) (v := s) (q := q) (ρ := ρ)
  have hprob : ∀ w, IsProbabilityMeasure (G_aux w) := fun w => hstate.1 w
  have hc_m : ∀ i : R_big, Measurable fun σ : R_big → ℝ^(N + 1) × ℝ => (σ i).1 (Fin.last N) :=
    fun i => ((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable).comp
      (measurable_fst.comp (measurable_pi_apply i))
  have hm_sq : Measurable fun σ : R_big → ℝ^(N + 1) × ℝ =>
      ((σ i₁).1 (Fin.last N) * (σ i₂).1 (Fin.last N) *
        (σ i₃).1 (Fin.last N) * (σ i₄).1 (Fin.last N)) ^ 2 :=
    ((((hc_m i₁).mul (hc_m i₂)).mul (hc_m i₃)).mul (hc_m i₄)).pow_const 2
  have h8_pt : ∀ x : ℝ, x ^ 8 ≤ 24 * K_last ^ 4 * Real.exp (x ^ 2 / K_last) := fun x => by
    have hts := Real.pow_div_factorial_le_exp (x ^ 2 / K_last) (by positivity) 4
    rw [div_pow, show (4 : ℕ).factorial = 24 by rfl, Nat.cast_ofNat,
      div_le_iff₀ (by norm_num)] at hts
    rw [show x ^ 8 = (x ^ 2) ^ 4 by ring]
    have hK4 : 0 < K_last ^ 4 := by positivity
    calc (x ^ 2) ^ 4 = K_last ^ 4 * ((x ^ 2) ^ 4 / K_last ^ 4) := by field_simp
      _ ≤ K_last ^ 4 * (Real.exp (x ^ 2 / K_last) * 24) := mul_le_mul_of_nonneg_left hts hK4.le
      _ = 24 * K_last ^ 4 * Real.exp (x ^ 2 / K_last) := by ring
  have hpt_w : ∀ w : AuxDis[N, M],
      ∫ σ : R_big → ℝ^(N + 1) × ℝ,
        ((σ i₁).1 (Fin.last N) * (σ i₂).1 (Fin.last N) *
          (σ i₃).1 (Fin.last N) * (σ i₄).1 (Fin.last N)) ^ 2
        ∂(Measure.pi fun _ : R_big => G_aux w) ≤
      24 * K_last ^ 4 * ∫ p : ℝ^(N + 1) × ℝ, Real.exp (p.1 (Fin.last N) ^ 2 / K_last)
        ∂(G_aux w) := by
    intro w
    have := hprob w
    have hexp_w : Integrable (fun p : ℝ^(N + 1) × ℝ =>
        Real.exp (p.1 (Fin.last N) ^ 2 / K_last)) (G_aux w) := by
      refine (hstate.2.1 w).mono' ((((PiLp.continuous_apply 2
        (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable.comp
        measurable_fst).pow_const 2).div_const K_last).exp.aestronglyMeasurable
        (ae_of_all _ fun p => ?_)
      rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
      refine div_le_div_of_nonneg_right ?_ hK_last_pos.le
      have hcoord : |p.1 (Fin.last N)| ≤ ‖p.1‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p.1 (Fin.last N)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hcoord 2
    have h8_w : Integrable (fun p : ℝ^(N + 1) × ℝ => p.1 (Fin.last N) ^ 8) (G_aux w) :=
      (hexp_w.const_mul (24 * K_last ^ 4)).mono'
        ((((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable.comp
          measurable_fst).pow_const 8)).aestronglyMeasurable
        (ae_of_all _ fun p => by
          rw [Real.norm_of_nonneg (by positivity)]
          exact h8_pt _)
    have hev : ∀ i : R_big, Integrable (fun σ : R_big → ℝ^(N + 1) × ℝ => (σ i).1 (Fin.last N) ^ 8)
        (Measure.pi fun _ : R_big => G_aux w) := fun i =>
      (measurePreserving_eval (fun _ : R_big => G_aux w) i).integrable_comp_of_integrable h8_w
    have hdom : Integrable (fun σ : R_big → ℝ^(N + 1) × ℝ =>
        ((σ i₁).1 (Fin.last N) ^ 8 + (σ i₂).1 (Fin.last N) ^ 8 +
          (σ i₃).1 (Fin.last N) ^ 8 + (σ i₄).1 (Fin.last N) ^ 8) / 4)
        (Measure.pi fun _ : R_big => G_aux w) :=
      ((((hev i₁).add (hev i₂)).add (hev i₃)).add (hev i₄)).div_const 4
    have hsq_i : Integrable (fun σ : R_big → ℝ^(N + 1) × ℝ =>
        ((σ i₁).1 (Fin.last N) * (σ i₂).1 (Fin.last N) *
          (σ i₃).1 (Fin.last N) * (σ i₄).1 (Fin.last N)) ^ 2)
        (Measure.pi fun _ : R_big => G_aux w) :=
      hdom.mono' hm_sq.aestronglyMeasurable (ae_of_all _ fun σ => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact mul_four_sq_le_sum_pow_eight _ _ _ _)
    have hdom_eq : ∫ σ : R_big → ℝ^(N + 1) × ℝ,
        ((σ i₁).1 (Fin.last N) ^ 8 + (σ i₂).1 (Fin.last N) ^ 8 +
          (σ i₃).1 (Fin.last N) ^ 8 + (σ i₄).1 (Fin.last N) ^ 8) / 4
        ∂(Measure.pi fun _ : R_big => G_aux w) =
        ∫ p : ℝ^(N + 1) × ℝ, p.1 (Fin.last N) ^ 8 ∂(G_aux w) := by
      have h12 : Integrable (fun σ : R_big → ℝ^(N + 1) × ℝ =>
          (σ i₁).1 (Fin.last N) ^ 8 + (σ i₂).1 (Fin.last N) ^ 8)
          (Measure.pi fun _ : R_big => G_aux w) := (hev i₁).add (hev i₂)
      have h123 : Integrable (fun σ : R_big → ℝ^(N + 1) × ℝ =>
          (σ i₁).1 (Fin.last N) ^ 8 + (σ i₂).1 (Fin.last N) ^ 8 + (σ i₃).1 (Fin.last N) ^ 8)
          (Measure.pi fun _ : R_big => G_aux w) := h12.add (hev i₃)
      rw [integral_div, integral_add h123 (hev i₄), integral_add h12 (hev i₃),
        integral_add (hev i₁) (hev i₂),
        integral_pi_eval (G_aux w) i₁ (fun p : ℝ^(N + 1) × ℝ => p.1 (Fin.last N) ^ 8)
          h8_w.aestronglyMeasurable,
        integral_pi_eval (G_aux w) i₂ (fun p : ℝ^(N + 1) × ℝ => p.1 (Fin.last N) ^ 8)
          h8_w.aestronglyMeasurable,
        integral_pi_eval (G_aux w) i₃ (fun p : ℝ^(N + 1) × ℝ => p.1 (Fin.last N) ^ 8)
          h8_w.aestronglyMeasurable,
        integral_pi_eval (G_aux w) i₄ (fun p : ℝ^(N + 1) × ℝ => p.1 (Fin.last N) ^ 8)
          h8_w.aestronglyMeasurable]
      ring
    calc ∫ σ, ((σ i₁).1 (Fin.last N) * (σ i₂).1 (Fin.last N) *
            (σ i₃).1 (Fin.last N) * (σ i₄).1 (Fin.last N)) ^ 2
          ∂(Measure.pi fun _ : R_big => G_aux w)
        ≤ ∫ σ, ((σ i₁).1 (Fin.last N) ^ 8 + (σ i₂).1 (Fin.last N) ^ 8 +
            (σ i₃).1 (Fin.last N) ^ 8 + (σ i₄).1 (Fin.last N) ^ 8) / 4
          ∂(Measure.pi fun _ : R_big => G_aux w) :=
          integral_mono hsq_i hdom fun σ => mul_four_sq_le_sum_pow_eight _ _ _ _
      _ = ∫ p, p.1 (Fin.last N) ^ 8 ∂(G_aux w) := hdom_eq
      _ ≤ ∫ p, 24 * K_last ^ 4 * Real.exp (p.1 (Fin.last N) ^ 2 / K_last) ∂(G_aux w) :=
          integral_mono h8_w (hexp_w.const_mul _) fun p => h8_pt _
      _ = 24 * K_last ^ 4 * ∫ p, Real.exp (p.1 (Fin.last N) ^ 2 / K_last) ∂(G_aux w) :=
          integral_const_mul _ _
  have hint : Integrable (fun w => ∫ σ : R_big → ℝ^(N + 1) × ℝ,
      ((σ i₁).1 (Fin.last N) * (σ i₂).1 (Fin.last N) *
        (σ i₃).1 (Fin.last N) * (σ i₄).1 (Fin.last N)) ^ 2
      ∂(Measure.pi fun _ : R_big => G_aux w)) auxLaw[N, M, r] :=
    (hlast_i.const_mul (24 * K_last ^ 4)).mono' (hstate.2.2 _ hm_sq).aestronglyMeasurable
      (ae_of_all _ fun w => by
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
        exact hpt_w w)
  refine ⟨hint, ?_⟩
  calc _ ≤ ∫ w, 24 * K_last ^ 4 * ∫ p : ℝ^(N + 1) × ℝ, Real.exp (p.1 (Fin.last N) ^ 2 / K_last)
            ∂(G_aux w) ∂auxLaw[N, M, r] :=
          integral_mono hint (hlast_i.const_mul _) hpt_w
    _ = 24 * K_last ^ 4 * ∫ w, ∫ p : ℝ^(N + 1) × ℝ, Real.exp (p.1 (Fin.last N) ^ 2 / K_last)
          ∂(G_aux w) ∂auxLaw[N, M, r] := integral_const_mul _ _
    _ ≤ 24 * K_last ^ 4 * K_last := mul_le_mul_of_nonneg_left hlast_le (by positivity)
    _ = 24 * K_last ^ 5 := by ring

/-- **Talagrand, Proposition 3.2.10 (Eq. (3.107)) for `f = ε₁²`:**
along the cavity path `ν_t` on `ℝ^(N+1)` with `M + 1` constraints (`M ≤ 10 (N + 1)`) at the RS
parameters `(r, r̄)` of Eq. (3.69) with `α = (M + 1) / (N + 1)`,
`|d/dt ν_t(ε₁²)| ≤ K * (√(ν_t((R_{1,2} - q)²)) + √(ν_t((R_{1,1} - ρ)²)) + (N + 1)⁻¹)`,
where `K > 0` depends only on `κ₀, h₀, D, Q, R, R_diff`. -/
theorem exists_hasDerivAt_shcherbinaTirozziCavity_sq_last_abs_le
    (κ₀ h₀ D Q R R_diff : ℝ) (hκ₀ : 0 < κ₀) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ) (κ h t q ρ : ℝ) (u : ℝ → ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 < t → t < 1 → 0 ≤ q → q ≤ ρ → ρ ≤ Q →
      M ≤ 10 * (N + 1) → ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) →
      Differentiable ℝ u → Differentiable ℝ (deriv u) →
      Differentiable ℝ (deriv (deriv u)) → Differentiable ℝ (deriv (deriv (deriv u))) →
      (∀ x, |deriv u x| ≤ D) → (∀ x, |deriv (deriv u) x| ≤ D) →
      (∀ x, |deriv (deriv (deriv u)) x| ≤ D) →
      (∀ x, |deriv (deriv (deriv (deriv u))) x| ≤ D) → -D ≤ u 0 →
      let α : ℝ := ((M : ℝ) + 1) / ((N : ℝ) + 1)
      let c : ℝ := Real.sqrt (ρ - q)
      let Z : ℝ → ℝ := fun y => ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)
      let V : ℝ → ℝ := fun y =>
        (∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z y
      let W : ℝ → ℝ := fun y => (∫ ξ, (deriv (deriv u) (y + c * ξ) + deriv u (y + c * ξ) ^ 2) *
        Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z y
      let r : ℝ := α * ∫ z, V (Real.sqrt q * z) ^ 2 ∂(gaussianReal 0 1)
      let rBar : ℝ := α * ∫ z, W (Real.sqrt q * z) ∂(gaussianReal 0 1)
      r ≤ R → r - rBar ≤ R_diff →
      let P_full := ((gaussianReal 0 r.toNNReal).prod
        ((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)))
      let G_full (s : ℝ) (d : ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) :
          Measure (ℝ^(N + 1)) :=
        (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r.toNNReal rBar s d.1 u d.2.1 d.2.2 σ
      ∃ D_val : ℝ, HasDerivAt
          (fun s => ∫ d, ∫ x : ℝ^(N + 1), x (Fin.last N) ^ 2 ∂(G_full s d) ∂P_full) D_val t ∧
        |D_val| ≤ K *
          (Real.sqrt (∫ d, ∫ p : Fin 2 → ℝ^(N + 1),
              (((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫ - q) ^ 2
              ∂(Measure.pi fun _ : Fin 2 => G_full t d) ∂P_full) +
            Real.sqrt (∫ d, ∫ x : ℝ^(N + 1),
              (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - ρ) ^ 2 ∂(G_full t d) ∂P_full) +
            ((N : ℝ) + 1)⁻¹) := by
  obtain ⟨K₀, hK₀_pos, hmain⟩ :=
    exists_hasDerivAt_shcherbinaTirozziCavity_abs_le_of_mul_last_sq_le (R_rep := Fin 1)
      κ₀ h₀ D Q R R_diff hκ₀ hQ hR hR_diff
  obtain ⟨K_last, hK_last_pos, hK_last_ge, h3100⟩ :=
    exists_integral_exp_sq_shcherbinaTirozziAuxCavity_last_le κ₀ h₀ D R hκ₀ hR
  set A : ℝ := Real.sqrt (24 * K_last ^ 5)
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  set K : ℝ := K₀ * A + 1
  have hK_pos : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK_pos, fun N M κ h t q ρ u hκ hh ht0 ht1 hq0 hqρ hρQ hM huc hu0 hu1 hu2 hu3 hu4
    hD1 hD2 hD3 hD4 huD => ?_⟩
  intro α c Z V W r rBar hrR hrr_diff P_full G_full
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum : Measurable u := hu1.continuous.measurable
  have hα0 : 0 ≤ α := by dsimp only [α]; positivity
  obtain ⟨hr0, -, hrr, -⟩ :=
    shcherbinaTirozzi_rsParameters_bounds huc hu0 hu1 hu2 hD1 hD2 hα0 q c
  have hr_coe : (r.toNNReal : ℝ) = r := Real.coe_toNNReal r hr0
  have hrr' : rBar ≤ (r.toNNReal : ℝ) := by rw [hr_coe]; exact hrr
  have hrR' : (r.toNNReal : ℝ) ≤ R := by rw [hr_coe]; exact hrR
  set f : (Fin 1 → ℝ^(N + 1)) → ℝ := fun σ => (σ 0) (Fin.last N) ^ 2
  have hfm : Measurable f :=
    (((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable).comp
      (measurable_pi_apply (0 : Fin 1))).pow_const 2
  have hfb : ∀ σ, |f σ| ≤ 1 * ∏ l : Fin 1, (1 + ‖σ l‖) ^ 2 := fun σ => by
    rw [one_mul, Fin.prod_univ_one]
    dsimp only [f]
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      ((show |(σ 0) (Fin.last N)| ≤ ‖σ 0‖ by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (σ 0) (Fin.last N)).trans
        (by linarith)) 2
  have hA_sq : A ^ 2 = 24 * K_last ^ 5 := Real.sq_sqrt (by positivity)
  have hA1 : ∀ (o : Option (Fin 1)) (s : ℝ), s ∈ Ioo (0 : ℝ) 1 →
      Integrable (fun w : AuxDis[N, M] => ∫ σ : Option (Fin 1) → ℝ^(N + 1) × ℝ,
          (f (fun l => (σ (some l)).1) * (σ o).1 (Fin.last N) ^ 2) ^ 2
          ∂(Measure.pi fun _ : Option (Fin 1) =>
            ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted fun p =>
              -shcherbinaTirozziCavityHamiltonian κ h r.toNNReal rBar t w.1.1 u
                  (fun j => w.1.2.1 j.castSucc) w.1.2.2 p.1 +
                u (Real.sqrt s * cfield[N, t, w.1.2.1, Fin.last M, p.1] +
                  Real.sqrt (1 - s) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2))))
          auxLaw[N, M, r.toNNReal] ∧
        ∫ w : AuxDis[N, M], ∫ σ : Option (Fin 1) → ℝ^(N + 1) × ℝ,
          (f (fun l => (σ (some l)).1) * (σ o).1 (Fin.last N) ^ 2) ^ 2
          ∂(Measure.pi fun _ : Option (Fin 1) =>
            ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted fun p =>
              -shcherbinaTirozziCavityHamiltonian κ h r.toNNReal rBar t w.1.1 u
                  (fun j => w.1.2.1 j.castSucc) w.1.2.2 p.1 +
                u (Real.sqrt s * cfield[N, t, w.1.2.1, Fin.last M, p.1] +
                  Real.sqrt (1 - s) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2)))
          ∂auxLaw[N, M, r.toNNReal] ≤ A ^ 2 := by
    intro o s hs
    obtain ⟨hl_i, hl_le⟩ := h3100 N M κ h t s q ρ rBar r.toNNReal u D hκ hh ht0.le ht1.le
      hs.1.le hs.2.le hrr' hrR' hM huc hu0 hu1 hu2 hD1 hD2
    have h4 := integrable_and_integral_mul_four_last_spin_sq_le (R_big := Option (Fin 1))
      hκ₀ hκ ht0.le ht1.le hrr' hum hu0 hK_last_pos hK_last_ge (some 0) (some 0) o o hl_i hl_le
    rw [hA_sq]
    have heq : ∀ σ : Option (Fin 1) → ℝ^(N + 1) × ℝ,
        (f (fun l => (σ (some l)).1) * (σ o).1 (Fin.last N) ^ 2) ^ 2 =
        ((σ (some 0)).1 (Fin.last N) * (σ (some 0)).1 (Fin.last N) *
          (σ o).1 (Fin.last N) * (σ o).1 (Fin.last N)) ^ 2 := fun σ => by
      dsimp only [f]; ring
    simp_rw [heq]
    exact h4
  have hA2 : ∀ (a b : Option (Option (Fin 1))) (s : ℝ), s ∈ Ioo (0 : ℝ) 1 →
      Integrable (fun w : AuxDis[N, M] => ∫ σ : Option (Option (Fin 1)) → ℝ^(N + 1) × ℝ,
          (f (fun l => (σ (some (some l))).1) *
            ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) ^ 2
          ∂(Measure.pi fun _ : Option (Option (Fin 1)) =>
            ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted fun p =>
              -shcherbinaTirozziCavityHamiltonian κ h r.toNNReal rBar t w.1.1 u
                  (fun j => w.1.2.1 j.castSucc) w.1.2.2 p.1 +
                u (Real.sqrt s * cfield[N, t, w.1.2.1, Fin.last M, p.1] +
                  Real.sqrt (1 - s) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2))))
          auxLaw[N, M, r.toNNReal] ∧
        ∫ w : AuxDis[N, M], ∫ σ : Option (Option (Fin 1)) → ℝ^(N + 1) × ℝ,
          (f (fun l => (σ (some (some l))).1) *
            ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) ^ 2
          ∂(Measure.pi fun _ : Option (Option (Fin 1)) =>
            ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted fun p =>
              -shcherbinaTirozziCavityHamiltonian κ h r.toNNReal rBar t w.1.1 u
                  (fun j => w.1.2.1 j.castSucc) w.1.2.2 p.1 +
                u (Real.sqrt s * cfield[N, t, w.1.2.1, Fin.last M, p.1] +
                  Real.sqrt (1 - s) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2)))
          ∂auxLaw[N, M, r.toNNReal] ≤ A ^ 2 := by
    intro a b s hs
    obtain ⟨hl_i, hl_le⟩ := h3100 N M κ h t s q ρ rBar r.toNNReal u D hκ hh ht0.le ht1.le
      hs.1.le hs.2.le hrr' hrR' hM huc hu0 hu1 hu2 hD1 hD2
    have h4 := integrable_and_integral_mul_four_last_spin_sq_le (R_big := Option (Option (Fin 1)))
      hκ₀ hκ ht0.le ht1.le hrr' hum hu0 hK_last_pos hK_last_ge
      (some (some 0)) (some (some 0)) a b hl_i hl_le
    rw [hA_sq]
    have heq : ∀ σ : Option (Option (Fin 1)) → ℝ^(N + 1) × ℝ,
        (f (fun l => (σ (some (some l))).1) * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) ^ 2 =
        ((σ (some (some 0))).1 (Fin.last N) * (σ (some (some 0))).1 (Fin.last N) *
          (σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)) ^ 2 := fun σ => by
      dsimp only [f]; ring
    simp_rw [heq]
    exact h4
  obtain ⟨D_val, hderiv, hbd⟩ := hmain N M κ h t q ρ u hκ hh ht0 ht1 hq0 hqρ hρQ hM huc hu0 hu1
    hu2 hu3 hu4 hD1 hD2 hD3 hD4 huD hfm hfb hA0 hrR hrr_diff hA1 hA2
  -- Identify `Fin 1` integral with single-replica integral for all `s ∈ [0, 1]`
  have hfun_eq : (fun s => ∫ d, ∫ σ : Fin 1 → ℝ^(N + 1), f σ
        ∂(Measure.pi fun _ : Fin 1 => G_full s d) ∂P_full) =ᶠ[𝓝 t]
      (fun s => ∫ d, ∫ x : ℝ^(N + 1), x (Fin.last N) ^ 2 ∂(G_full s d) ∂P_full) := by
    filter_upwards [Ioo_mem_nhds ht0 ht1] with s hs
    refine integral_congr_ae (ae_of_all _ fun d => ?_)
    have : IsProbabilityMeasure (G_full s d) := isProbabilityMeasure_tilted
      (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ0
        (mul_nonneg (sub_nonneg.2 hs.2.le) (sub_nonneg.2 hrr')) hum hu0 d.2.1 d.2.2)
    exact integral_pi_eval (G_full s d) (0 : Fin 1)
      (fun x : ℝ^(N + 1) => x (Fin.last N) ^ 2)
      (((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable).pow_const
        2).aestronglyMeasurable
  refine ⟨D_val, hderiv.congr_of_eventuallyEq hfun_eq.symm, hbd.trans ?_⟩
  refine mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) (by positivity)

/-- **Talagrand, Proposition 3.2.10 (Eq. (3.107)) for `f = ε₁ ε₂`:**
along the cavity path `ν_t` on `ℝ^(N+1)` with `M + 1` constraints (`M ≤ 10 (N + 1)`) at the RS
parameters `(r, r̄)` of Eq. (3.69) with `α = (M + 1) / (N + 1)`,
`|d/dt ν_t(ε₁ ε₂)| ≤ K * (√(ν_t((R_{1,2} - q)²)) + √(ν_t((R_{1,1} - ρ)²)) + (N + 1)⁻¹)`,
where `K > 0` depends only on `κ₀, h₀, D, Q, R, R_diff`. -/
theorem exists_hasDerivAt_shcherbinaTirozziCavity_mul_last_abs_le
    (κ₀ h₀ D Q R R_diff : ℝ) (hκ₀ : 0 < κ₀) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ) (κ h t q ρ : ℝ) (u : ℝ → ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 < t → t < 1 → 0 ≤ q → q ≤ ρ → ρ ≤ Q →
      M ≤ 10 * (N + 1) → ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) →
      Differentiable ℝ u → Differentiable ℝ (deriv u) →
      Differentiable ℝ (deriv (deriv u)) → Differentiable ℝ (deriv (deriv (deriv u))) →
      (∀ x, |deriv u x| ≤ D) → (∀ x, |deriv (deriv u) x| ≤ D) →
      (∀ x, |deriv (deriv (deriv u)) x| ≤ D) →
      (∀ x, |deriv (deriv (deriv (deriv u))) x| ≤ D) → -D ≤ u 0 →
      let α : ℝ := ((M : ℝ) + 1) / ((N : ℝ) + 1)
      let c : ℝ := Real.sqrt (ρ - q)
      let Z : ℝ → ℝ := fun y => ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)
      let V : ℝ → ℝ := fun y =>
        (∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z y
      let W : ℝ → ℝ := fun y => (∫ ξ, (deriv (deriv u) (y + c * ξ) + deriv u (y + c * ξ) ^ 2) *
        Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) / Z y
      let r : ℝ := α * ∫ z, V (Real.sqrt q * z) ^ 2 ∂(gaussianReal 0 1)
      let rBar : ℝ := α * ∫ z, W (Real.sqrt q * z) ∂(gaussianReal 0 1)
      r ≤ R → r - rBar ≤ R_diff →
      let P_full := ((gaussianReal 0 r.toNNReal).prod
        ((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)))
      let G_full (s : ℝ) (d : ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) :
          Measure (ℝ^(N + 1)) :=
        (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r.toNNReal rBar s d.1 u d.2.1 d.2.2 σ
      ∃ D_val : ℝ, HasDerivAt
          (fun s => ∫ d, ∫ σ : Fin 2 → ℝ^(N + 1),
            (σ 0) (Fin.last N) * (σ 1) (Fin.last N)
            ∂(Measure.pi fun _ : Fin 2 => G_full s d) ∂P_full) D_val t ∧
        |D_val| ≤ K *
          (Real.sqrt (∫ d, ∫ p : Fin 2 → ℝ^(N + 1),
              (((N : ℝ) + 1)⁻¹ * ⟪p 0, p 1⟫ - q) ^ 2
              ∂(Measure.pi fun _ : Fin 2 => G_full t d) ∂P_full) +
            Real.sqrt (∫ d, ∫ x : ℝ^(N + 1),
              (((N : ℝ) + 1)⁻¹ * ‖x‖ ^ 2 - ρ) ^ 2 ∂(G_full t d) ∂P_full) +
            ((N : ℝ) + 1)⁻¹) := by
  obtain ⟨K₀, hK₀_pos, hmain⟩ :=
    exists_hasDerivAt_shcherbinaTirozziCavity_abs_le_of_mul_last_sq_le (R_rep := Fin 2)
      κ₀ h₀ D Q R R_diff hκ₀ hQ hR hR_diff
  obtain ⟨K_last, hK_last_pos, hK_last_ge, h3100⟩ :=
    exists_integral_exp_sq_shcherbinaTirozziAuxCavity_last_le κ₀ h₀ D R hκ₀ hR
  set A : ℝ := Real.sqrt (24 * K_last ^ 5)
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  set K : ℝ := K₀ * A + 1
  have hK_pos : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK_pos, fun N M κ h t q ρ u hκ hh ht0 ht1 hq0 hqρ hρQ hM huc hu0 hu1 hu2 hu3 hu4
    hD1 hD2 hD3 hD4 huD => ?_⟩
  intro α c Z V W r rBar hrR hrr_diff P_full G_full
  have hum : Measurable u := hu1.continuous.measurable
  have hα0 : 0 ≤ α := by dsimp only [α]; positivity
  obtain ⟨hr0, -, hrr, -⟩ :=
    shcherbinaTirozzi_rsParameters_bounds huc hu0 hu1 hu2 hD1 hD2 hα0 q c
  have hr_coe : (r.toNNReal : ℝ) = r := Real.coe_toNNReal r hr0
  have hrr' : rBar ≤ (r.toNNReal : ℝ) := by rw [hr_coe]; exact hrr
  have hrR' : (r.toNNReal : ℝ) ≤ R := by rw [hr_coe]; exact hrR
  set f : (Fin 2 → ℝ^(N + 1)) → ℝ := fun σ => (σ 0) (Fin.last N) * (σ 1) (Fin.last N)
  have hfm : Measurable f :=
    (((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable).comp
      (measurable_pi_apply (0 : Fin 2))).mul
      (((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable).comp
        (measurable_pi_apply (1 : Fin 2)))
  have hfb : ∀ σ, |f σ| ≤ 1 * ∏ l : Fin 2, (1 + ‖σ l‖) ^ 1 := fun σ => by
    rw [one_mul, Fin.prod_univ_two, pow_one, pow_one]
    dsimp only [f]
    rw [abs_mul]
    have h0 : |(σ 0) (Fin.last N)| ≤ 1 + ‖σ 0‖ :=
      (show |(σ 0) (Fin.last N)| ≤ ‖σ 0‖ by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (σ 0) (Fin.last N)).trans
        (by linarith)
    have h1 : |(σ 1) (Fin.last N)| ≤ 1 + ‖σ 1‖ :=
      (show |(σ 1) (Fin.last N)| ≤ ‖σ 1‖ by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (σ 1) (Fin.last N)).trans
        (by linarith)
    exact mul_le_mul h0 h1 (abs_nonneg _) (by positivity)
  have hA_sq : A ^ 2 = 24 * K_last ^ 5 := Real.sq_sqrt (by positivity)
  have hA1 : ∀ (o : Option (Fin 2)) (s : ℝ), s ∈ Ioo (0 : ℝ) 1 →
      Integrable (fun w : AuxDis[N, M] => ∫ σ : Option (Fin 2) → ℝ^(N + 1) × ℝ,
          (f (fun l => (σ (some l)).1) * (σ o).1 (Fin.last N) ^ 2) ^ 2
          ∂(Measure.pi fun _ : Option (Fin 2) =>
            ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted fun p =>
              -shcherbinaTirozziCavityHamiltonian κ h r.toNNReal rBar t w.1.1 u
                  (fun j => w.1.2.1 j.castSucc) w.1.2.2 p.1 +
                u (Real.sqrt s * cfield[N, t, w.1.2.1, Fin.last M, p.1] +
                  Real.sqrt (1 - s) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2))))
          auxLaw[N, M, r.toNNReal] ∧
        ∫ w : AuxDis[N, M], ∫ σ : Option (Fin 2) → ℝ^(N + 1) × ℝ,
          (f (fun l => (σ (some l)).1) * (σ o).1 (Fin.last N) ^ 2) ^ 2
          ∂(Measure.pi fun _ : Option (Fin 2) =>
            ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted fun p =>
              -shcherbinaTirozziCavityHamiltonian κ h r.toNNReal rBar t w.1.1 u
                  (fun j => w.1.2.1 j.castSucc) w.1.2.2 p.1 +
                u (Real.sqrt s * cfield[N, t, w.1.2.1, Fin.last M, p.1] +
                  Real.sqrt (1 - s) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2)))
          ∂auxLaw[N, M, r.toNNReal] ≤ A ^ 2 := by
    intro o s hs
    obtain ⟨hl_i, hl_le⟩ := h3100 N M κ h t s q ρ rBar r.toNNReal u D hκ hh ht0.le ht1.le
      hs.1.le hs.2.le hrr' hrR' hM huc hu0 hu1 hu2 hD1 hD2
    have h4 := integrable_and_integral_mul_four_last_spin_sq_le (R_big := Option (Fin 2))
      hκ₀ hκ ht0.le ht1.le hrr' hum hu0 hK_last_pos hK_last_ge (some 0) (some 1) o o hl_i hl_le
    rw [hA_sq]
    have heq : ∀ σ : Option (Fin 2) → ℝ^(N + 1) × ℝ,
        (f (fun l => (σ (some l)).1) * (σ o).1 (Fin.last N) ^ 2) ^ 2 =
        ((σ (some 0)).1 (Fin.last N) * (σ (some 1)).1 (Fin.last N) *
          (σ o).1 (Fin.last N) * (σ o).1 (Fin.last N)) ^ 2 := fun σ => by
      dsimp only [f]; ring
    simp_rw [heq]
    exact h4
  have hA2 : ∀ (a b : Option (Option (Fin 2))) (s : ℝ), s ∈ Ioo (0 : ℝ) 1 →
      Integrable (fun w : AuxDis[N, M] => ∫ σ : Option (Option (Fin 2)) → ℝ^(N + 1) × ℝ,
          (f (fun l => (σ (some (some l))).1) *
            ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) ^ 2
          ∂(Measure.pi fun _ : Option (Option (Fin 2)) =>
            ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted fun p =>
              -shcherbinaTirozziCavityHamiltonian κ h r.toNNReal rBar t w.1.1 u
                  (fun j => w.1.2.1 j.castSucc) w.1.2.2 p.1 +
                u (Real.sqrt s * cfield[N, t, w.1.2.1, Fin.last M, p.1] +
                  Real.sqrt (1 - s) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2))))
          auxLaw[N, M, r.toNNReal] ∧
        ∫ w : AuxDis[N, M], ∫ σ : Option (Option (Fin 2)) → ℝ^(N + 1) × ℝ,
          (f (fun l => (σ (some (some l))).1) *
            ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) ^ 2
          ∂(Measure.pi fun _ : Option (Option (Fin 2)) =>
            ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted fun p =>
              -shcherbinaTirozziCavityHamiltonian κ h r.toNNReal rBar t w.1.1 u
                  (fun j => w.1.2.1 j.castSucc) w.1.2.2 p.1 +
                u (Real.sqrt s * cfield[N, t, w.1.2.1, Fin.last M, p.1] +
                  Real.sqrt (1 - s) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2)))
          ∂auxLaw[N, M, r.toNNReal] ≤ A ^ 2 := by
    intro a b s hs
    obtain ⟨hl_i, hl_le⟩ := h3100 N M κ h t s q ρ rBar r.toNNReal u D hκ hh ht0.le ht1.le
      hs.1.le hs.2.le hrr' hrR' hM huc hu0 hu1 hu2 hD1 hD2
    have h4 := integrable_and_integral_mul_four_last_spin_sq_le (R_big := Option (Option (Fin 2)))
      hκ₀ hκ ht0.le ht1.le hrr' hum hu0 hK_last_pos hK_last_ge
      (some (some 0)) (some (some 1)) a b hl_i hl_le
    rw [hA_sq]
    have heq : ∀ σ : Option (Option (Fin 2)) → ℝ^(N + 1) × ℝ,
        (f (fun l => (σ (some (some l))).1) * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) ^ 2 =
        ((σ (some (some 0))).1 (Fin.last N) * (σ (some (some 1))).1 (Fin.last N) *
          (σ a).1 (Fin.last N) * (σ b).1 (Fin.last N)) ^ 2 := fun σ => by
      dsimp only [f]; ring
    simp_rw [heq]
    exact h4
  obtain ⟨D_val, hderiv, hbd⟩ := hmain N M κ h t q ρ u hκ hh ht0 ht1 hq0 hqρ hρQ hM huc hu0 hu1
    hu2 hu3 hu4 hD1 hD2 hD3 hD4 huD hfm hfb hA0 hrR hrr_diff hA1 hA2
  refine ⟨D_val, hderiv, hbd.trans ?_⟩
  refine mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) (by positivity)

end SpinGlasses
