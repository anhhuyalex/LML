/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.CavityOverlapConcentration

/-!
# The Shcherbina--Tirozzi model: uniform-in-`t` disorder concentration along the cavity path

This file finishes the uniform-in-`t` Section 3.1 overlap concentration along the cavity path
`H_{N,M,t}` of Eq. (3.61) on `ℝ^(N+1)`, giving **Talagrand, Eq. (3.111)** (uniform-in-`t`
Theorem 3.1.18):
```
ν_t ((R_{1,1} - ρ_t) ^ (2 k)) ≤ (K k / (N + 1)) ^ k,
ν_t ((R_{1,2} - q_t) ^ (2 k)) ≤ (K k / (N + 1)) ^ k,
```
for `4 k ≤ N + 1`, where `q_t = ν_t(R_{1,2})`, `ρ_t = ν_t(R_{1,1})`, and `K` depends only on
`κ₀, h₀, D, R, R_diff`.

## Main declarations

* `SpinGlasses.exists_integral_shcherbinaTirozziCavity_selfOverlap_sub_pow_le`: Eq. (3.111) for
  `R_{1,1}`.
* `SpinGlasses.exists_integral_shcherbinaTirozziCavity_overlap_sub_pow_le`: Eq. (3.111) for
  `R_{1,2}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Module Matrix
open scoped RealInnerProductSpace Real NNReal Matrix.Norms.L2Operator Topology

namespace SpinGlasses

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

local notation "Dis[" N ", " M "]" =>
  ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))

local notation "cavLaw[" N ", " M ", " r "]" =>
  Measure.prod (gaussianReal 0 r)
    (Measure.prod
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
      (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))

local notation "cfield[" N ", " t ", " g ", " k ", " σ "]" =>
  (Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, g k (Fin.castSucc i) * σ (Fin.castSucc i)) +
    Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N)))

section CavityGradient

/-- Covariance bound for a Lipschitz vector function of the configuration under the cavity Gibbs
measure: `‖⟨f (F - ⟨F⟩_t)⟩_t‖ ≤ A √(32 ⟨f²⟩_t / κ)`. -/
private theorem norm_integral_smul_sub_mean_cavity_le_of_lipschitz {N M : ℕ}
    {κ h r rBar t y : ℝ} (hκ : 0 < κ) (hrr : rBar ≤ r) (ht1 : t ≤ 1)
    {u : ℝ → ℝ} (hu : ConcaveOn ℝ Set.univ u) (hu0 : ∀ x, u x ≤ 0)
    (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) (G : Measure (ℝ^(N + 1)))
    (hG : G = volume.tilted fun σ => -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F : ℝ^(N + 1) → V} {A : ℝ} (hA : 0 ≤ A)
    (hlip : ∀ σ τ, ‖F σ - F τ‖ ≤ A * ‖σ - τ‖) {f : ℝ^(N + 1) → ℝ} (hf : MemLp f 2 G) :
    ‖∫ σ, f σ • (F σ - ∫ τ, F τ ∂G) ∂G‖ ≤ A * Real.sqrt (32 / κ * ∫ σ, f σ ^ 2 ∂G) := by
  have hum := hu.measurable_of_univ
  have hq : 0 ≤ (1 - t) * (r - rBar) := mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hrr)
  have key := norm_integral_smul_sub_integral_le_of_lipschitz (μ₀ := volume) (C := Set.univ)
    (H := shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀) convex_univ MeasurableSet.univ
    (NeZero.ne _) (measurable_shcherbinaTirozziCavityHamiltonian_apply κ h r rBar t y hum g g₀)
    (integrableOn_univ.2 (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ hq hum hu0 g g₀))
    (fun x _ z _ => shcherbinaTirozziCavityHamiltonian_midpoint_gap κ h y hq hu g g₀ x z) hκ
    (F := F) (f := f) hA (fun x _ z _ => hlip x z)
  simp only [Measure.restrict_univ, ← hG] at key
  exact key hf

/-- Contraction by `√t` on the last coordinate of a vector on `ℝ^(N+1)`. -/
private noncomputable def lastScale {N : ℕ} (t : ℝ) (σ : ℝ^(N + 1)) : ℝ^(N + 1) :=
  WithLp.toLp 2 fun i => (if i = Fin.last N then Real.sqrt t else 1) * σ i

private lemma norm_lastScale_le {N : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (σ : ℝ^(N + 1)) :
    ‖lastScale t σ‖ ≤ ‖σ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  simp only [lastScale, Real.norm_eq_abs, sq_abs, mul_pow]
  refine mul_le_of_le_one_left (sq_nonneg _) ?_
  split
  · rw [Real.sq_sqrt ht0]; exact ht1
  · norm_num

private lemma cfield_eq_mul_sum_lastScale {N M : ℕ} {t : ℝ} (g : Fin M → Fin (N + 1) → ℝ)
    (k : Fin M) (σ : ℝ^(N + 1)) :
    cfield[N, t, g, k, σ] = (Real.sqrt (N + 1))⁻¹ * ∑ i : Fin (N + 1), g k i * lastScale t σ i := by
  have hcast : ∀ i : Fin N, (i.castSucc : Fin (N + 1)) ≠ Fin.last N :=
    fun i => (Fin.castSucc_lt_last i).ne
  congr 1
  rw [Fin.sum_univ_castSucc (n := N)]
  simp only [lastScale, hcast, reduceIte, one_mul]
  ring

private lemma lastScale_sub {N : ℕ} (t : ℝ) (σ τ : ℝ^(N + 1)) :
    lastScale t σ - lastScale t τ = lastScale t (σ - τ) := by
  ext i
  change (if i = Fin.last N then Real.sqrt t else 1) * σ i -
      (if i = Fin.last N then Real.sqrt t else 1) * τ i =
    (if i = Fin.last N then Real.sqrt t else 1) * (σ i - τ i)
  ring

/-- The map `σ ↦ (u'(S_{k,t}(σ)))_k` is `D ‖g‖ / √(N + 1)`-Lipschitz uniformly in `t ∈ [0, 1]`. -/
private theorem norm_cavity_deriv_field_sub_le {N M : ℕ} {t D : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {u : ℝ → ℝ} (hD : ∀ a b, |deriv u a - deriv u b| ≤ D * |a - b|)
    (g : Fin M → Fin (N + 1) → ℝ) (σ τ : ℝ^(N + 1)) :
    ‖(WithLp.toLp 2 fun k => deriv u cfield[N, t, g, k, σ] : ℝ^M) -
        WithLp.toLp 2 fun k => deriv u cfield[N, t, g, k, τ]‖ ≤
      D * ((Real.sqrt (N + 1))⁻¹ * ‖Matrix.of g‖) * ‖σ - τ‖ := by
  have hD0 : 0 ≤ D := by simpa using (abs_nonneg _).trans (hD 1 0)
  have hlip : LipschitzWith D.toNNReal (deriv u) := LipschitzWith.of_dist_le_mul fun a b => by
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal D hD0]
    exact hD a b
  have h := (PiLp.lipschitzWith_toLp_comp (p := 2) fun _ : Fin M => hlip).dist_le_mul
    (WithLp.toLp 2 fun k => cfield[N, t, g, k, σ])
    (WithLp.toLp 2 fun k => cfield[N, t, g, k, τ])
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal D hD0] at h
  have hfield : ‖(WithLp.toLp 2 fun k => cfield[N, t, g, k, σ] : ℝ^M) -
      WithLp.toLp 2 fun k => cfield[N, t, g, k, τ]‖ ≤
      (Real.sqrt (N + 1))⁻¹ * (‖Matrix.of g‖ * ‖σ - τ‖) := by
    rw [EuclideanSpace.norm_eq]
    have hsq : ∑ k : Fin M, (cfield[N, t, g, k, σ] - cfield[N, t, g, k, τ]) ^ 2 ≤
        ((Real.sqrt (N + 1))⁻¹ * (‖Matrix.of g‖ * ‖lastScale t (σ - τ)‖)) ^ 2 := by
      have hmv := pow_le_pow_left₀ (norm_nonneg _)
        (Matrix.l2_opNorm_mulVec (Matrix.of g) (lastScale t (σ - τ))) 2
      rw [EuclideanSpace.real_norm_sq_eq] at hmv
      have hterm : ∀ k : Fin M, (cfield[N, t, g, k, σ] - cfield[N, t, g, k, τ]) ^ 2 =
          ((Real.sqrt (N + 1))⁻¹) ^ 2 *
            (∑ i : Fin (N + 1), g k i * lastScale t (σ - τ) i) ^ 2 := fun k => by
        rw [cfield_eq_mul_sum_lastScale, cfield_eq_mul_sum_lastScale, ← mul_sub,
          ← Finset.sum_sub_distrib, mul_pow]
        congr 2
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← mul_sub]
        have hsub : lastScale t σ i - lastScale t τ i = lastScale t (σ - τ) i := by
          rw [← lastScale_sub]; rfl
        rw [hsub]
      simp_rw [hterm]
      rw [← Finset.mul_sum, mul_pow]
      exact mul_le_mul_of_nonneg_left hmv (sq_nonneg _)
    have h1 : Real.sqrt (∑ k : Fin M, ‖cfield[N, t, g, k, σ] - cfield[N, t, g, k, τ]‖ ^ 2) ≤
        (Real.sqrt (N + 1))⁻¹ * (‖Matrix.of g‖ * ‖lastScale t (σ - τ)‖) := by
      refine (Real.sqrt_le_sqrt (le_of_eq_of_le (Finset.sum_congr rfl fun k _ => by
        rw [Real.norm_eq_abs, sq_abs]) hsq)).trans_eq (Real.sqrt_sq (by positivity))
    exact h1.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (norm_lastScale_le ht0 ht1 _) (norm_nonneg _)) (by positivity))
  exact h.trans ((mul_le_mul_of_nonneg_left hfield hD0).trans_eq (by ring))

/-- **Differentiation of a cavity Gibbs average along a line in the disorder `(y, g, g₀)`:**
for an observable `F` of polynomial growth and direction `(Δy, Δg, Δg₀)` with fixed
`t ∈ [0, 1]`, `s ↦ ⟨F⟩_{y + s Δy, g + s Δg, g₀ + s Δg₀}` has derivative
`⟨F X⟩ - ⟨F⟩ ⟨X⟩` at `0`, where
`X σ = ∑_k u'(S_{k,t}(σ)) S_{k,t}^{Δg}(σ) + h ∑_i Δg₀_i σ_i + √(1 - t) Δy σ_N`. -/
private theorem hasDerivAt_integral_shcherbinaTirozziCavityGibbs_line {N M : ℕ}
    {κ h r rBar t : ℝ} (hκ : 0 < κ) (hrr : rBar ≤ r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0) {D : ℝ}
    (hD : ∀ x, |deriv u x| ≤ D) (y Δy : ℝ) (g Δg : Fin M → Fin (N + 1) → ℝ)
    (g₀ Δg₀ : Fin (N + 1) → ℝ) {F : ℝ^(N + 1) → ℝ} (hF : Measurable F) {c : ℝ} {m : ℕ}
    (hFb : ∀ σ, |F σ| ≤ c * (1 + ‖σ‖) ^ m) :
    let G (s : ℝ) := (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t (y + s * Δy) u
        (fun k i => g k i + s * Δg k i) (fun i => g₀ i + s * Δg₀ i) σ
    let X : ℝ^(N + 1) → ℝ := fun σ =>
      (∑ k : Fin M, deriv u cfield[N, t, g, k, σ] * cfield[N, t, Δg, k, σ]) +
        h * (∑ i, Δg₀ i * σ i) + Real.sqrt (1 - t) * Δy * σ (Fin.last N)
    HasDerivAt (fun s => ∫ σ, F σ ∂(G s))
      ((∫ σ, F σ * X σ ∂(G 0)) - (∫ σ, F σ ∂(G 0)) * ∫ σ, X σ ∂(G 0)) 0 := by
  intro G X
  have hum : Measurable u := hu.continuous.measurable
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hc0 : 0 ≤ c := by simpa using (abs_nonneg _).trans (hFb 0)
  have hcast : ∀ i : Fin N, (i.castSucc : Fin (N + 1)) ≠ Fin.last N :=
    fun i => (Fin.castSucc_lt_last i).ne
  set e : ℝ → ℝ^(N + 1) → ℝ := fun s σ =>
    -shcherbinaTirozziCavityHamiltonian κ h r rBar t (y + s * Δy) u
      (fun k i => g k i + s * Δg k i) (fun i => g₀ i + s * Δg₀ i) σ
  set X_s : ℝ → ℝ^(N + 1) → ℝ := fun s σ =>
    (∑ k : Fin M, deriv u cfield[N, t, (fun k i => g k i + s * Δg k i), k, σ] *
      cfield[N, t, Δg, k, σ]) +
      h * (∑ i, Δg₀ i * σ i) + Real.sqrt (1 - t) * Δy * σ (Fin.last N)
  -- Linear growth of `X_s s σ` uniformly in `s`
  set v_Δ : Fin M → ℝ^(N + 1) := fun k => WithLp.toLp 2 fun i =>
    (Real.sqrt (N + 1))⁻¹ * ((if i = Fin.last N then Real.sqrt t else 1) * Δg k i)
  have hv_Δ : ∀ k σ, ⟪v_Δ k, σ⟫ = cfield[N, t, Δg, k, σ] := fun k σ => by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
      Fin.sum_univ_castSucc (n := N)]
    simp only [v_Δ, hcast, reduceIte, one_mul, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · ring
  set a_Δ : ℝ^(N + 1) := WithLp.toLp 2 fun i =>
    h * Δg₀ i + if i = Fin.last N then Real.sqrt (1 - t) * Δy else 0
  have ha_Δ : ∀ σ, ⟪a_Δ, σ⟫ = h * (∑ i, Δg₀ i * σ i) + Real.sqrt (1 - t) * Δy * σ (Fin.last N) :=
    fun σ => by
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
      simp only [a_Δ, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, reduceIte, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · ring
  set L : ℝ := D * (∑ k : Fin M, ‖v_Δ k‖) + ‖a_Δ‖
  have hL0 : 0 ≤ L := add_nonneg (mul_nonneg hD0 (Finset.sum_nonneg fun _ _ => norm_nonneg _))
    (norm_nonneg _)
  have hXb : ∀ s σ, |X_s s σ| ≤ L * ‖σ‖ := fun s σ => by
    have heq : X_s s σ = (∑ k : Fin M, deriv u cfield[N, t, (fun k i => g k i + s * Δg k i), k, σ] *
        ⟪v_Δ k, σ⟫) + ⟪a_Δ, σ⟫ := by
      dsimp only [X_s]; simp_rw [hv_Δ]; rw [ha_Δ]; ring
    rw [heq]
    have h1 : |∑ k : Fin M, deriv u cfield[N, t, (fun k i => g k i + s * Δg k i), k, σ] *
        ⟪v_Δ k, σ⟫| ≤ D * (∑ k : Fin M, ‖v_Δ k‖) * ‖σ‖ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul, mul_assoc]
      exact mul_le_mul (hD _) (abs_real_inner_le_norm _ _) (abs_nonneg _) hD0
    rw [add_mul]
    exact (abs_add_le _ _).trans (add_le_add h1 (abs_real_inner_le_norm _ _))
  -- Uniform confinement on `ball 0 1`
  set R_conf : ℝ := |h| * (∑ i, |g₀ i| + ∑ i, |Δg₀ i|) + (|y| + |Δy|)
  have hconf : ∀ s ∈ Metric.ball (0 : ℝ) 1, ∀ σ : ℝ^(N + 1),
      e s σ ≤ 0 + R_conf * ‖σ‖ - κ * ‖σ‖ ^ 2 := fun s hs σ => by
    rw [zero_add]
    have hs1 : |s| ≤ 1 := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hs; exact hs.le
    refine (neg_shcherbinaTirozziCavityHamiltonian_le κ h (y + s * Δy) hrr ht0 ht1 hu0 _ _ σ).trans ?_
    have h1 : ∑ i : Fin (N + 1), |g₀ i + s * Δg₀ i| ≤ (∑ i, |g₀ i|) + ∑ i, |Δg₀ i| := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hs1
    have h2 : |y + s * Δy| ≤ |y| + |Δy| := by
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hs1
    have h3 : |h| * ∑ i, |g₀ i + s * Δg₀ i| + |y + s * Δy| ≤ R_conf := by
      dsimp only [R_conf]
      linarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg h)]
    linarith [mul_le_mul_of_nonneg_right h3 (norm_nonneg σ)]
  -- Envelope
  set b : ℝ^(N + 1) → ℝ := fun σ => (1 + c) * Real.exp ((R_conf + L + m) ^ 2 / (2 * κ)) *
    Real.exp (-(κ / 2) * ‖σ‖ ^ 2)
  have hbi : Integrable b := by
    have := integrable_exp_neg_mul_sq_norm_add_inner (E := ℝ^(N + 1)) (half_pos hκ) 0
    simp only [inner_zero_left, add_zero] at this
    exact this.const_mul _
  have hder : ∀ (σ : ℝ^(N + 1)) (s : ℝ), HasDerivAt (fun q => e q σ) (X_s s σ) s := fun σ s => by
    have hfield : ∀ k : Fin M, HasDerivAt
        (fun q => u cfield[N, t, (fun k i => g k i + q * Δg k i), k, σ])
        (deriv u cfield[N, t, (fun k i => g k i + s * Δg k i), k, σ] * cfield[N, t, Δg, k, σ]) s := by
      intro k
      have hlin : (fun q => cfield[N, t, (fun k i => g k i + q * Δg k i), k, σ]) =
          fun q => cfield[N, t, g, k, σ] + q * cfield[N, t, Δg, k, σ] := funext fun q => by
        simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]; ring
      have hd : HasDerivAt (fun q => cfield[N, t, (fun k i => g k i + q * Δg k i), k, σ])
          cfield[N, t, Δg, k, σ] s := by
        rw [hlin]
        have hd1 : HasDerivAt (fun q : ℝ => q * cfield[N, t, Δg, k, σ])
            (1 * cfield[N, t, Δg, k, σ]) s := (hasDerivAt_id s).mul_const _
        simpa only [one_mul] using hd1.const_add cfield[N, t, g, k, σ]
      exact (hu _).hasDerivAt.comp s hd
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun k _ => hfield k
    have hg0 : HasDerivAt (fun q => h * ∑ i, (g₀ i + q * Δg₀ i) * σ i)
        (h * ∑ i, Δg₀ i * σ i) s := by
      have hlin : (fun q => h * ∑ i, (g₀ i + q * Δg₀ i) * σ i) =
          fun q => (h * ∑ i, g₀ i * σ i) + q * (h * ∑ i, Δg₀ i * σ i) := funext fun q => by
        simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]; ring
      rw [hlin]
      have hd1 : HasDerivAt (fun q : ℝ => q * (h * ∑ i, Δg₀ i * σ i))
          (1 * (h * ∑ i, Δg₀ i * σ i)) s := (hasDerivAt_id s).mul_const _
      simpa only [one_mul] using hd1.const_add (h * ∑ i, g₀ i * σ i)
    have hy : HasDerivAt (fun q => σ (Fin.last N) * (Real.sqrt (1 - t) * (y + q * Δy)))
        (Real.sqrt (1 - t) * Δy * σ (Fin.last N)) s := by
      have hlin : (fun q => σ (Fin.last N) * (Real.sqrt (1 - t) * (y + q * Δy))) =
          fun q => σ (Fin.last N) * (Real.sqrt (1 - t) * y) +
            q * (Real.sqrt (1 - t) * Δy * σ (Fin.last N)) := funext fun q => by ring
      rw [hlin]
      have hd1 : HasDerivAt (fun q : ℝ => q * (Real.sqrt (1 - t) * Δy * σ (Fin.last N)))
          (1 * (Real.sqrt (1 - t) * Δy * σ (Fin.last N))) s :=
        (hasDerivAt_id s).mul_const _
      simpa only [one_mul] using hd1.const_add (σ (Fin.last N) * (Real.sqrt (1 - t) * y))
    have he_eq : (fun q => e q σ) = fun q =>
        (∑ k : Fin M, u cfield[N, t, (fun k i => g k i + q * Δg k i), k, σ]) +
        (h * ∑ i, (g₀ i + q * Δg₀ i) * σ i) +
        (σ (Fin.last N) * (Real.sqrt (1 - t) * (y + q * Δy))) -
        (κ * ‖σ‖ ^ 2 + (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2) := funext fun q => by
      dsimp only [e, shcherbinaTirozziCavityHamiltonian]; ring
    rw [he_eq]
    exact ((hsum.add hg0).add hy).sub_const _
  have hem : ∀ s, Measurable (e s) := fun s =>
    (measurable_shcherbinaTirozziCavityHamiltonian_apply κ h r rBar t _ hum _ _).neg
  have hXm : Measurable (X_s 0) := by
    have heq : X_s 0 = fun σ =>
        (∑ k : Fin M, deriv u cfield[N, t, g, k, σ] * ⟪v_Δ k, σ⟫) + ⟪a_Δ, σ⟫ := funext fun σ => by
      dsimp only [X_s]; simp only [zero_mul, add_zero, hv_Δ, ha_Δ, add_assoc]
    rw [heq]
    refine (Finset.measurable_sum _ fun k _ => ?_).add (by fun_prop)
    exact ((measurable_deriv u).comp (by
      have hc : Continuous fun σ : ℝ^(N + 1) => cfield[N, t, g, k, σ] := by fun_prop
      exact hc.measurable)).mul (by fun_prop)
  have hX0 : X_s 0 = X := funext fun σ => by dsimp only [X_s, X]; simp
  have hmain := hasDerivAt_integral_tilted_of_envelope (μ := volume) (s := Metric.ball (0 : ℝ) 1)
    (e := e) (e' := X_s) (F := F) (b := b) (Metric.ball_mem_nhds 0 one_pos)
    (fun s _ => hem s) hXm hF hbi (fun s hs σ => ?_) (fun σ s _ => hder σ s)
  · rwa [hX0] at hmain
  · -- Envelope bound: `(1 + |F σ|) * (1 + |X_s s σ|) * exp (e s σ) ≤ b σ`
    have hX1 : 1 + |X_s s σ| ≤ Real.exp (L * ‖σ‖) :=
      (add_le_add le_rfl (hXb s σ)).trans (by linarith [Real.add_one_le_exp (L * ‖σ‖)])
    have hF1 : 1 + |F σ| ≤ (1 + c) * Real.exp (m * ‖σ‖) := by
      have h1 : (1 + ‖σ‖) ^ m ≤ Real.exp (m * ‖σ‖) := by
        rw [Real.exp_nat_mul]
        exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ‖σ‖]) m
      have h2 : 1 ≤ Real.exp (m * ‖σ‖) := Real.one_le_exp (by positivity)
      calc 1 + |F σ| ≤ 1 + c * (1 + ‖σ‖) ^ m := add_le_add le_rfl (hFb σ)
        _ ≤ Real.exp (m * ‖σ‖) + c * Real.exp (m * ‖σ‖) :=
            add_le_add h2 (mul_le_mul_of_nonneg_left h1 hc0)
        _ = (1 + c) * Real.exp (m * ‖σ‖) := by ring
    have he1 : Real.exp (e s σ) ≤ Real.exp (R_conf * ‖σ‖ - κ * ‖σ‖ ^ 2) :=
      Real.exp_le_exp.2 (by linarith [hconf s hs σ])
    have hquad : (R_conf + L + m) * ‖σ‖ - κ * ‖σ‖ ^ 2 ≤
        (R_conf + L + m) ^ 2 / (2 * κ) - κ / 2 * ‖σ‖ ^ 2 := by
      have hsq : 0 ≤ (κ * ‖σ‖ - (R_conf + L + m)) ^ 2 / (2 * κ) := by positivity
      have hid : (κ * ‖σ‖ - (R_conf + L + m)) ^ 2 / (2 * κ) =
          κ / 2 * ‖σ‖ ^ 2 - (R_conf + L + m) * ‖σ‖ + (R_conf + L + m) ^ 2 / (2 * κ) := by
        field_simp; ring
      linarith
    calc (1 + |F σ|) * (1 + |X_s s σ|) * Real.exp (e s σ)
        ≤ ((1 + c) * Real.exp (m * ‖σ‖)) * Real.exp (L * ‖σ‖) *
            Real.exp (R_conf * ‖σ‖ - κ * ‖σ‖ ^ 2) :=
          mul_le_mul (mul_le_mul hF1 hX1 (by positivity) (by positivity)) he1
            (Real.exp_pos _).le (by positivity)
      _ = (1 + c) * Real.exp ((R_conf + L + m) * ‖σ‖ - κ * ‖σ‖ ^ 2) := by
          rw [mul_assoc (1 + c), mul_assoc (1 + c), ← Real.exp_add, ← Real.exp_add]
          congr 2; ring
      _ ≤ (1 + c) * Real.exp ((R_conf + L + m) ^ 2 / (2 * κ) - κ / 2 * ‖σ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hquad) (by positivity)
      _ = b σ := by
          dsimp only [b]; rw [sub_eq_add_neg, Real.exp_add, neg_mul]; ring

/-- **Covariance bound for the cavity disorder derivative:** for a centered `f ∈ L²(G)` and the
directional derivative `X` of `-H_{N,M,t}` in direction `(Δy, Δg, Δg₀)`,
`|⟨f X⟩_t| ≤ √(32 ⟨f²⟩_t / κ) (D √(M / (N+1)) + |h| + 1 + D ‖g‖ ‖⟨σ⟩_t‖ / (N+1)) √(∑ Δg² + ∑ Δg₀² + Δy²)`. -/
private theorem abs_integral_mul_cavityDisorderDerivative_le {N M : ℕ}
    {κ h r rBar t y : ℝ} (hκ : 0 < κ) (hrr : rBar ≤ r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {u : ℝ → ℝ} (hu : ConcaveOn ℝ Set.univ u) (hu0 : ∀ x, u x ≤ 0)
    {D : ℝ} (hD1 : ∀ x, |deriv u x| ≤ D) (hD2 : ∀ a b, |deriv u a - deriv u b| ≤ D * |a - b|)
    (Δy : ℝ) (g Δg : Fin M → Fin (N + 1) → ℝ) (g₀ Δg₀ : Fin (N + 1) → ℝ)
    (G : Measure (ℝ^(N + 1)))
    (hG : G = volume.tilted fun σ => -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ)
    {f : ℝ^(N + 1) → ℝ} (hf : MemLp f 2 G) (hf0 : ∫ σ, f σ ∂G = 0)
    (X : ℝ^(N + 1) → ℝ)
    (hX : ∀ σ, X σ = (∑ k : Fin M, deriv u cfield[N, t, g, k, σ] * cfield[N, t, Δg, k, σ]) +
      h * (∑ i, Δg₀ i * σ i) + Real.sqrt (1 - t) * Δy * σ (Fin.last N)) :
    |∫ σ, f σ * X σ ∂G| ≤ Real.sqrt (32 / κ * ∫ σ, f σ ^ 2 ∂G) *
      (D * Real.sqrt (M / ((N : ℝ) + 1)) + |h| + 1 +
        D * ‖Matrix.of g‖ * ‖∫ σ, σ ∂G‖ / ((N : ℝ) + 1)) *
      Real.sqrt ((∑ k : Fin M, ∑ i : Fin (N + 1), Δg k i ^ 2) +
        (∑ i : Fin (N + 1), Δg₀ i ^ 2) + Δy ^ 2) := by
  have hum := hu.measurable_of_univ
  have hcast : ∀ i : Fin N, (i.castSucc : Fin (N + 1)) ≠ Fin.last N :=
    fun i => (Fin.castSucc_lt_last i).ne
  have : IsProbabilityMeasure G := by
    rw [hG]; exact isProbabilityMeasure_tilted (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian
      hκ (mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hrr)) hum hu0 g g₀)
  have hid : MemLp (fun σ : ℝ^(N + 1) => σ) 2 G := by
    rw [hG]
    have hconf : ∀ σ : ℝ^(N + 1),
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ ≤
          0 + (|h| * ∑ i, |g₀ i| + |y|) * ‖σ‖ - κ * ‖σ‖ ^ 2 := fun σ => by
      rw [zero_add]; exact neg_shcherbinaTirozziCavityHamiltonian_le κ h y hrr ht0 ht1 hu0 g g₀ σ
    exact_mod_cast memLp_of_poly_bound_of_confining hκ
      (measurable_shcherbinaTirozziCavityHamiltonian_apply κ h r rBar t y hum g g₀).neg hconf
      (f := fun σ : ℝ^(N + 1) => σ) aestronglyMeasurable_id (C := 1) (m := 1) (fun σ => by simp) 2
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD1 0)
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set b : ℝ^(N + 1) := ∫ σ, σ ∂G with hb
  set Φ : ℝ := Real.sqrt (32 / κ * ∫ σ, f σ ^ 2 ∂G) with hΦ
  have hΦ0 : 0 ≤ Φ := Real.sqrt_nonneg _
  set A : ℝ := ∑ k : Fin M, ∑ i : Fin (N + 1), Δg k i ^ 2 with hA
  set A₀ : ℝ := ∑ i : Fin (N + 1), Δg₀ i ^ 2 with hA₀
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hA00 : 0 ≤ A₀ := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set δ : ℝ := Real.sqrt (A + A₀ + Δy ^ 2) with hδ
  have hfield : ∀ k : Fin M, Measurable fun σ : ℝ^(N + 1) =>
      deriv u cfield[N, t, g, k, σ] := fun k =>
    (measurable_deriv u).comp (by
      have hc : Continuous fun σ : ℝ^(N + 1) => cfield[N, t, g, k, σ] := by fun_prop
      exact hc.measurable)
  set φ : Fin M → ℝ^(N + 1) → ℝ := fun k σ => f σ * deriv u cfield[N, t, g, k, σ] with hφ
  have hφb : ∀ k σ, ‖φ k σ‖ ≤ D * ‖f σ‖ := fun k σ => by
    rw [hφ, norm_mul, mul_comm D]
    exact mul_le_mul_of_nonneg_left (hD1 _) (norm_nonneg _)
  have hφL : ∀ k, MemLp (φ k) 2 G := fun k =>
    hf.of_le_mul (hf.aestronglyMeasurable.mul (hfield k).aestronglyMeasurable) (ae_of_all _ (hφb k))
  set v : Fin M → ℝ^(N + 1) := fun k => WithLp.toLp 2 fun i =>
    (Real.sqrt (N + 1))⁻¹ * ((if i = Fin.last N then Real.sqrt t else 1) * Δg k i) with hv
  have hv_inner : ∀ k σ, ⟪v k, σ⟫ = cfield[N, t, Δg, k, σ] := fun k σ => by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
      Fin.sum_univ_castSucc (n := N)]
    simp only [v, hcast, reduceIte, one_mul, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · ring
  set d₀ : ℝ^(N + 1) := WithLp.toLp 2 Δg₀ with hd₀
  set e_last : ℝ^(N + 1) := EuclideanSpace.single (Fin.last N) (1 : ℝ) with he_last
  -- Maurey covariance bounds for `σ` and `U σ`
  set w : Fin M → ℝ^(N + 1) := fun k => ∫ σ, φ k σ • (σ - b) ∂G with hw
  have hwn : ∀ k, ‖w k‖ ≤ D * Φ := fun k => by
    refine (norm_integral_smul_sub_mean_cavity_le_of_lipschitz (h := h) (y := y) hκ hrr ht1 hu hu0
      g g₀ G hG (F := fun σ : ℝ^(N + 1) => σ) zero_le_one (fun σ τ => (one_mul _).ge)
      (hφL k)).trans ?_
    rw [one_mul]
    have h1 : ∫ σ, φ k σ ^ 2 ∂G ≤ D ^ 2 * ∫ σ, f σ ^ 2 ∂G := by
      rw [← integral_const_mul]
      refine integral_mono (hφL k).integrable_sq (hf.integrable_sq.const_mul _) fun σ => ?_
      have := pow_le_pow_left₀ (norm_nonneg _) (hφb k σ) 2
      simpa only [mul_pow, Real.norm_eq_abs, sq_abs] using this
    refine (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h1 (by positivity))).trans_eq ?_
    rw [hΦ, show 32 / κ * (D ^ 2 * ∫ σ, f σ ^ 2 ∂G) =
      D ^ 2 * (32 / κ * ∫ σ, f σ ^ 2 ∂G) by ring, Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq hD0]
  set z : ℝ^(N + 1) := ∫ σ, f σ • (σ - b) ∂G with hz
  have hzn : ‖z‖ ≤ Φ := by
    have h := norm_integral_smul_sub_mean_cavity_le_of_lipschitz (h := h) (y := y) hκ hrr ht1 hu hu0
      g g₀ G hG (F := fun σ : ℝ^(N + 1) => σ) zero_le_one (fun σ τ => (one_mul _).ge) hf
    rwa [one_mul] at h
  set U : ℝ^(N + 1) → ℝ^M := fun σ => WithLp.toLp 2 fun k => deriv u cfield[N, t, g, k, σ] with hU
  set V : ℝ^M := ∫ σ, f σ • (U σ - ∫ τ, U τ ∂G) ∂G with hV
  have hVn : ‖V‖ ≤ D * ((Real.sqrt (N + 1))⁻¹ * ‖Matrix.of g‖) * Φ :=
    norm_integral_smul_sub_mean_cavity_le_of_lipschitz (h := h) (y := y) hκ hrr ht1 hu hu0
      g g₀ G hG (F := U) (by positivity) (fun σ τ => norm_cavity_deriv_field_sub_le ht0 ht1 hD2 g σ τ)
      hf
  have hUm : Measurable U := (WithLp.measurable_toLp 2 (Fin M → ℝ)).comp
    (Measurable.of_eval fun k => hfield k)
  have hUL : MemLp U 2 G := by
    refine MemLp.of_bound hUm.aestronglyMeasurable (Real.sqrt (M * D ^ 2)) (ae_of_all _ fun σ => ?_)
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ((Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) =>
      pow_le_pow_left₀ (norm_nonneg _) (show ‖U σ k‖ ≤ D from hD1 _) 2).trans_eq ?_)
    simp
  have hVk : ∀ k, V k = ∫ σ, φ k σ ∂G := fun k => by
    have h := (integral_smul_apply_eq_apply_integral_smul_sub_add hf hUL
      (EuclideanSpace.proj (𝕜 := ℝ) k) (∫ τ, U τ ∂G)).2
    rw [hf0, zero_smul, add_zero] at h
    exact h.symm
  -- Expand `⟨f X⟩`
  have hterm : ∀ k, Integrable (fun σ => φ k σ * ⟪v k, σ⟫) G ∧
      ∫ σ, φ k σ * ⟪v k, σ⟫ ∂G = ⟪v k, w k⟫ + V k * ⟪v k, b⟫ := fun k => by
    rw [hVk]
    exact integral_smul_apply_eq_apply_integral_smul_sub_add (hφL k) hid (innerSL ℝ (v k)) b
  have hlast_g0 : Integrable (fun σ => f σ * ⟪d₀, σ⟫) G ∧ ∫ σ, f σ * ⟪d₀, σ⟫ ∂G = ⟪d₀, z⟫ := by
    have h := integral_smul_apply_eq_apply_integral_smul_sub_add hf hid (innerSL ℝ d₀) b
    rw [hf0, zero_smul, add_zero] at h; exact h
  have hlast_y : Integrable (fun σ => f σ * ⟪e_last, σ⟫) G ∧ ∫ σ, f σ * ⟪e_last, σ⟫ ∂G = ⟪e_last, z⟫ := by
    have h := integral_smul_apply_eq_apply_integral_smul_sub_add hf hid (innerSL ℝ e_last) b
    rw [hf0, zero_smul, add_zero] at h; exact h
  have hfX : ∫ σ, f σ * X σ ∂G =
      (∑ k, (⟪v k, w k⟫ + V k * ⟪v k, b⟫)) + h * ⟪d₀, z⟫ +
        Real.sqrt (1 - t) * Δy * ⟪e_last, z⟫ := by
    have e : (fun σ => f σ * X σ) = fun σ =>
        (∑ k, φ k σ * ⟪v k, σ⟫) + h * (f σ * ⟪d₀, σ⟫) +
          (Real.sqrt (1 - t) * Δy) * (f σ * ⟪e_last, σ⟫) := funext fun σ => by
      have h2 : ∑ i, Δg₀ i * σ i = ⟪d₀, σ⟫ := by
        have := inner_toLp_inv_sqrt_mul_eq 1 Δg₀ σ; simpa only [one_mul] using this.symm
      have h3 : σ (Fin.last N) = ⟪e_last, σ⟫ := by
        rw [he_last, EuclideanSpace.inner_single_left]; simp
      rw [hX, h2]
      simp only [hφ, hv_inner]
      rw [mul_add, mul_add, Finset.mul_sum, ← h3]
      congr 1
      · congr 1
        · exact Finset.sum_congr rfl fun k _ => (mul_assoc _ _ _).symm
        · ring
      · ring
    have hsum : Integrable (fun σ => ∑ k, φ k σ * ⟪v k, σ⟫) G :=
      integrable_finsetSum _ fun k _ => (hterm k).1
    have h12 : Integrable (fun σ => (∑ k, φ k σ * ⟪v k, σ⟫) + h * (f σ * ⟪d₀, σ⟫)) G :=
      hsum.add (hlast_g0.1.const_mul h)
    rw [e, integral_add h12 (hlast_y.1.const_mul _),
      integral_add hsum (hlast_g0.1.const_mul h),
      integral_finsetSum _ fun k _ => (hterm k).1, integral_const_mul, integral_const_mul,
      hlast_g0.2, hlast_y.2]
    congr 2
    exact Finset.sum_congr rfl fun k _ => (hterm k).2
  -- Norms of the direction
  have hvn : ∑ k, ‖v k‖ ^ 2 ≤ ((N : ℝ) + 1)⁻¹ * A := by
    rw [hA, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    dsimp only [v]
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity), mul_pow]
    refine mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (sq_nonneg _) ?_) (by positivity)
    split
    · rw [Real.sq_sqrt ht0]; exact ht1
    · norm_num
  have hsA : Real.sqrt A ≤ δ := Real.sqrt_le_sqrt (by linarith [sq_nonneg Δy])
  have hsumv : ∑ k, ‖v k‖ ≤ Real.sqrt (M / ((N : ℝ) + 1)) * δ := by
    have h1 : (∑ k, ‖v k‖) ^ 2 ≤ M / ((N : ℝ) + 1) * A := by
      have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => ‖v k‖)
      rw [Finset.card_univ, Fintype.card_fin] at h2
      exact h2.trans ((mul_le_mul_of_nonneg_left hvn (Nat.cast_nonneg M)).trans_eq (by ring))
    refine (Real.le_sqrt_of_sq_le h1).trans ?_
    rw [Real.sqrt_mul (by positivity)]
    exact mul_le_mul_of_nonneg_left hsA (Real.sqrt_nonneg _)
  have hsumV : ∑ k, ‖v k‖ * |V k| ≤ D * ‖Matrix.of g‖ * Φ / ((N : ℝ) + 1) * δ := by
    have h1 : ∑ k, ‖v k‖ * |V k| ≤ Real.sqrt (∑ k, ‖v k‖ ^ 2) * ‖V‖ := by
      rw [EuclideanSpace.norm_eq]; simp only [Real.norm_eq_abs]
      exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun k => ‖v k‖) fun k => |V k|
    have h2 : Real.sqrt (∑ k, ‖v k‖ ^ 2) ≤ (Real.sqrt (N + 1))⁻¹ * δ := by
      refine (Real.sqrt_le_sqrt hvn).trans ?_
      rw [Real.sqrt_mul (inv_nonneg.2 hN0.le), Real.sqrt_inv]
      exact mul_le_mul_of_nonneg_left hsA (inv_nonneg.2 (Real.sqrt_nonneg _))
    refine h1.trans ((mul_le_mul h2 hVn (norm_nonneg _)
      (mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))).trans_eq ?_)
    have hsq : (Real.sqrt (N + 1))⁻¹ * (Real.sqrt (N + 1))⁻¹ = ((N : ℝ) + 1)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hN0.le]
    rw [div_eq_mul_inv, ← hsq]; ring
  have hd₀n : ‖d₀‖ ≤ δ := by
    have e : ‖d₀‖ = Real.sqrt A₀ := by
      rw [EuclideanSpace.norm_eq]; simp only [Real.norm_eq_abs, sq_abs]; rfl
    rw [e]; exact Real.sqrt_le_sqrt (by linarith [sq_nonneg Δy])
  have hΔy_le : |Δy| ≤ δ := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by linarith)
  have h1 : |∑ k, (⟪v k, w k⟫ + V k * ⟪v k, b⟫)| ≤
      D * Φ * ∑ k, ‖v k‖ + ‖b‖ * ∑ k, ‖v k‖ * |V k| := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (abs_real_inner_le_norm _ _).trans ?_
      rw [mul_comm (D * Φ)]
      exact mul_le_mul_of_nonneg_left (hwn k) (norm_nonneg _)
    · rw [abs_mul]
      refine (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)).trans_eq ?_
      ring
  have h2 : |h * ⟪d₀, z⟫| ≤ |h| * (δ * Φ) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul hd₀n hzn (norm_nonneg _) (Real.sqrt_nonneg _))) (abs_nonneg h)
  have h3_y : |Real.sqrt (1 - t) * Δy * ⟪e_last, z⟫| ≤ 1 * (δ * Φ) := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), one_mul]
    have hs1 : Real.sqrt (1 - t) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
    have he1 : |⟪e_last, z⟫| ≤ Φ := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      simp [e_last, hzn]
    calc Real.sqrt (1 - t) * |Δy| * |⟪e_last, z⟫|
        ≤ 1 * |Δy| * |⟪e_last, z⟫| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs1 (abs_nonneg _)) (abs_nonneg _)
      _ = |Δy| * |⟪e_last, z⟫| := by rw [one_mul]
      _ ≤ δ * Φ := mul_le_mul hΔy_le he1 (abs_nonneg _) (Real.sqrt_nonneg _)
  rw [hfX]
  refine (abs_add_le _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add h1 h2)) h3_y).trans ?_)
  have h3 := mul_le_mul_of_nonneg_left hsumv (mul_nonneg hD0 hΦ0)
  have h4 := mul_le_mul_of_nonneg_left hsumV (norm_nonneg b)
  refine (add_le_add (add_le_add (add_le_add h3 h4) le_rfl) le_rfl).trans_eq ?_
  ring

/-- Square of the cavity covariance bound for a centered observable with second moment
`≤ c B / (N + 1)²`. -/
private theorem sq_integral_mul_cavityDisorderDerivative_le {N M : ℕ}
    {κ₀ κ h h₀ D c K₉ B r rBar t y : ℝ} (hκ₀ : 0 < κ₀) (hκ : κ₀ ≤ κ) (hh : |h| ≤ h₀)
    (hrr : rBar ≤ r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hM : M ≤ 10 * (N + 1))
    {u : ℝ → ℝ} (hu : ConcaveOn ℝ Set.univ u) (hu0 : ∀ x, u x ≤ 0)
    (hD1 : ∀ x, |deriv u x| ≤ D) (hD2 : ∀ a b, |deriv u a - deriv u b| ≤ D * |a - b|)
    (Δy : ℝ) (g Δg : Fin M → Fin (N + 1) → ℝ) (g₀ Δg₀ : Fin (N + 1) → ℝ)
    (G : Measure (ℝ^(N + 1)))
    (hG : G = volume.tilted fun σ => -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ)
    {f : ℝ^(N + 1) → ℝ} (hf : MemLp f 2 G) (hf0 : ∫ σ, f σ ∂G = 0)
    (hc : 0 ≤ c) (hK₉ : 0 ≤ K₉) (hB : 0 ≤ B)
    (hf2 : ∫ σ, f σ ^ 2 ∂G ≤ c * B / ((N : ℝ) + 1) ^ 2)
    (hb : ‖∫ σ, σ ∂G‖ ^ 2 ≤ K₉ * B)
    (X : ℝ^(N + 1) → ℝ)
    (hX : ∀ σ, X σ = (∑ k : Fin M, deriv u cfield[N, t, g, k, σ] * cfield[N, t, Δg, k, σ]) +
      h * (∑ i, Δg₀ i * σ i) + Real.sqrt (1 - t) * Δy * σ (Fin.last N)) :
    (∫ σ, f σ * X σ ∂G) ^ 2 ≤
      64 * c / κ₀ * ((4 * D + h₀ + 1) ^ 2 + D ^ 2 * K₉) *
        (B / ((N : ℝ) + 1) ^ 2 + B ^ 2 * ‖Matrix.of g‖ ^ 2 / ((N : ℝ) + 1) ^ 4) *
        ((∑ k : Fin M, ∑ i : Fin (N + 1), Δg k i ^ 2) +
          (∑ i : Fin (N + 1), Δg₀ i ^ 2) + Δy ^ 2) := by
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD1 0)
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hMN : Real.sqrt (M / ((N : ℝ) + 1)) ≤ 4 := by
    refine Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩
    rw [div_le_iff₀ hN0]
    have h10 : (M : ℝ) ≤ 10 * ((N : ℝ) + 1) := by exact_mod_cast hM
    linarith
  have key : |∫ σ, f σ * X σ ∂G| ≤ Real.sqrt (32 / κ * ∫ σ, f σ ^ 2 ∂G) *
      (4 * D + |h| + 1 + D * ‖Matrix.of g‖ * ‖∫ σ, σ ∂G‖ / ((N : ℝ) + 1)) *
      Real.sqrt ((∑ k : Fin M, ∑ i : Fin (N + 1), Δg k i ^ 2) +
        (∑ i : Fin (N + 1), Δg₀ i ^ 2) + Δy ^ 2) := by
    refine (abs_integral_mul_cavityDisorderDerivative_le hκ0 hrr ht0 ht1 hu hu0 hD1 hD2 Δy g Δg
      g₀ Δg₀ G hG hf hf0 X hX).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    have h4 : D * Real.sqrt (M / ((N : ℝ) + 1)) ≤ 4 * D :=
      (mul_le_mul_of_nonneg_left hMN hD0).trans_eq (mul_comm _ _)
    linarith
  set δ2 : ℝ := (∑ k : Fin M, ∑ i : Fin (N + 1), Δg k i ^ 2) +
    (∑ i : Fin (N + 1), Δg₀ i ^ 2) + Δy ^ 2 with hδ2
  have hδ20 : 0 ≤ δ2 := add_nonneg (add_nonneg
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (sq_nonneg Δy)
  set n : ℝ := ‖Matrix.of g‖ with hn
  set β : ℝ := ‖∫ σ, σ ∂G‖ with hβ
  have hf20 : 0 ≤ ∫ σ, f σ ^ 2 ∂G := integral_nonneg fun _ => sq_nonneg _
  have h1 := pow_le_pow_left₀ (abs_nonneg _) key 2
  rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg (by positivity) hf20),
    Real.sq_sqrt hδ20] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ hδ20)
  have h2 : 32 / κ * ∫ σ, f σ ^ 2 ∂G ≤ 32 / κ₀ * (c * B / ((N : ℝ) + 1) ^ 2) :=
    mul_le_mul (div_le_div_of_nonneg_left (by norm_num) hκ₀ hκ) hf2 hf20 (by positivity)
  have hh0 : 0 ≤ h₀ := (abs_nonneg _).trans hh
  have h3 : (4 * D + |h| + 1 + D * n * β / ((N : ℝ) + 1)) ^ 2 ≤
      2 * (4 * D + h₀ + 1) ^ 2 + 2 * (D ^ 2 * n ^ 2 * (K₉ * B) / ((N : ℝ) + 1) ^ 2) := by
    refine (add_sq_le).trans ?_
    rw [mul_add]
    refine add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
      (by linarith) 2) zero_le_two) (mul_le_mul_of_nonneg_left ?_ zero_le_two)
    rw [div_pow, mul_pow, mul_pow]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb (by positivity)) (by positivity)
  refine (mul_le_mul h2 h3 (sq_nonneg _) (by positivity)).trans ?_
  have hexp : 32 / κ₀ * (c * B / ((N : ℝ) + 1) ^ 2) *
        (2 * (4 * D + h₀ + 1) ^ 2 + 2 * (D ^ 2 * n ^ 2 * (K₉ * B) / ((N : ℝ) + 1) ^ 2)) =
      64 * c / κ₀ * ((4 * D + h₀ + 1) ^ 2 * (B / ((N : ℝ) + 1) ^ 2) +
        D ^ 2 * K₉ * (B ^ 2 * n ^ 2 / ((N : ℝ) + 1) ^ 4)) := by field_simp; ring
  rw [hexp, mul_assoc (64 * c / κ₀)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hP : 0 ≤ B / ((N : ℝ) + 1) ^ 2 := by positivity
  have hQ : 0 ≤ B ^ 2 * n ^ 2 / ((N : ℝ) + 1) ^ 4 := by positivity
  nlinarith [mul_nonneg (sq_nonneg (4 * D + h₀ + 1)) hQ,
    mul_nonneg (mul_nonneg (sq_nonneg D) hK₉) hP]

/-- Square integrability of the cavity disorder derivative under a probability measure with
square integrable configuration. -/
private theorem memLp_cavityDisorderDerivative {N M : ℕ} {t D h Δy : ℝ} {u : ℝ → ℝ}
    (hD : ∀ x, |deriv u x| ≤ D) (g Δg : Fin M → Fin (N + 1) → ℝ) (Δg₀ : Fin (N + 1) → ℝ)
    (G : Measure (ℝ^(N + 1))) (hid : MemLp (fun σ : ℝ^(N + 1) => σ) 2 G)
    (X : ℝ^(N + 1) → ℝ)
    (hX : ∀ σ, X σ = (∑ k : Fin M, deriv u cfield[N, t, g, k, σ] * cfield[N, t, Δg, k, σ]) +
      h * (∑ i, Δg₀ i * σ i) + Real.sqrt (1 - t) * Δy * σ (Fin.last N)) :
    MemLp X 2 G := by
  have hcast : ∀ i : Fin N, (i.castSucc : Fin (N + 1)) ≠ Fin.last N :=
    fun i => (Fin.castSucc_lt_last i).ne
  have hlin_c : ∀ k : Fin M, MemLp (fun σ : ℝ^(N + 1) => cfield[N, t, Δg, k, σ]) 2 G := fun k => by
    set v : ℝ^(N + 1) := WithLp.toLp 2 fun i =>
      (Real.sqrt (N + 1))⁻¹ * ((if i = Fin.last N then Real.sqrt t else 1) * Δg k i)
    have hv : ∀ σ, ⟪v, σ⟫ = cfield[N, t, Δg, k, σ] := fun σ => by
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
        Fin.sum_univ_castSucc (n := N)]
      simp only [v, hcast, reduceIte, one_mul, mul_add, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => by ring
      · ring
    simpa only [hv] using hid.const_inner (𝕜 := ℝ) v
  have hfield : ∀ k : Fin M, Measurable fun σ : ℝ^(N + 1) =>
      deriv u cfield[N, t, g, k, σ] := fun k =>
    (measurable_deriv u).comp (by
      have hc : Continuous fun σ : ℝ^(N + 1) => cfield[N, t, g, k, σ] := by fun_prop
      exact hc.measurable)
  have hsum : MemLp (fun σ : ℝ^(N + 1) =>
      ∑ k : Fin M, deriv u cfield[N, t, g, k, σ] * cfield[N, t, Δg, k, σ]) 2 G := by
    refine memLp_finsetSum _ fun k _ => (hlin_c k).of_le_mul (c := D)
      ((hfield k).aestronglyMeasurable.mul (hlin_c k).aestronglyMeasurable) (ae_of_all _ fun σ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _)
  have hg0 : MemLp (fun σ : ℝ^(N + 1) => h * ∑ i, Δg₀ i * σ i) 2 G := by
    have h1 := hid.const_inner (𝕜 := ℝ) (WithLp.toLp 2 (fun i => h * Δg₀ i) : ℝ^(N + 1))
    simpa only [inner_toLp_inv_sqrt_mul_eq] using h1
  have hy : MemLp (fun σ : ℝ^(N + 1) => Real.sqrt (1 - t) * Δy * σ (Fin.last N)) 2 G :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (Fin.last N)).comp_memLp' hid).const_mul _
  have e : X = fun σ =>
      (∑ k : Fin M, deriv u cfield[N, t, g, k, σ] * cfield[N, t, Δg, k, σ]) +
        h * (∑ i, Δg₀ i * σ i) + Real.sqrt (1 - t) * Δy * σ (Fin.last N) := funext hX
  rw [e]
  exact (hsum.add hg0).add hy

/-- **Gradient bound for `⟨R_{1,1}⟩_t` along any line of the cavity disorder `(y, g, g₀)`:**
uniform in `t ∈ [0, 1]`. -/
theorem exists_hasDerivAt_integral_shcherbinaTirozziCavity_selfOverlap_line
    (κ₀ h₀ D R_diff : ℝ) (hκ₀ : 0 < κ₀) (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M : ℕ) (κ h r rBar t y Δy : ℝ) (u : ℝ → ℝ)
      (g Δg : Fin M → Fin (N + 1) → ℝ) (g₀ Δg₀ : Fin (N + 1) → ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → rBar ≤ r → r - rBar ≤ R_diff →
      M ≤ 10 * (N + 1) → ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) →
      (∀ x, -D * (1 + |x|) ≤ u x) → Differentiable ℝ u → (∀ x, |deriv u x| ≤ D) →
      (∀ a b, |deriv u a - deriv u b| ≤ D * |a - b|) →
      ∃ d : ℝ, HasDerivAt (fun s => ∫ σ, ((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2
            ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
              -shcherbinaTirozziCavityHamiltonian κ h r rBar t (y + s * Δy) u
                (fun k i => g k i + s * Δg k i) (fun i => g₀ i + s * Δg₀ i) σ)) d 0 ∧
        d ^ 2 ≤ K * ((((N : ℝ) + 1) + Real.sqrt (∑ k : Fin M, ∑ i : Fin (N + 1), g k i ^ 2) +
              (∑ i : Fin (N + 1), g₀ i ^ 2) + y ^ 2) / ((N : ℝ) + 1) ^ 2 +
            (((N : ℝ) + 1) + Real.sqrt (∑ k : Fin M, ∑ i : Fin (N + 1), g k i ^ 2) +
              (∑ i : Fin (N + 1), g₀ i ^ 2) + y ^ 2) ^ 2 * ‖Matrix.of g‖ ^ 2 /
              ((N : ℝ) + 1) ^ 4) *
          ((∑ k : Fin M, ∑ i : Fin (N + 1), Δg k i ^ 2) +
            (∑ i : Fin (N + 1), Δg₀ i ^ 2) + Δy ^ 2) := by
  obtain ⟨K₁₁, hK₁₁, h335⟩ :=
    exists_integral_shcherbinaTirozziCavity_selfOverlap_sub_mean_pow_le κ₀ h₀ D R_diff hκ₀ hR_diff
  obtain ⟨K₉, hK₉, h319⟩ :=
    exists_integral_sq_norm_pow_shcherbinaTirozziCavity_le κ₀ h₀ D R_diff hκ₀ hR_diff
  refine ⟨64 * K₁₁ / κ₀ * ((4 * D + h₀ + 1) ^ 2 + D ^ 2 * K₉), by positivity,
    fun N M κ h r rBar t y Δy u g Δg g₀ Δg₀ hκ hh ht0 ht1 hrr hrr_diff hM hu hu0 hD hud
      hD1 hD2 => ?_⟩
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum := hu.measurable_of_univ
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  set G := (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
    -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ with hG
  have : IsProbabilityMeasure G :=
    isProbabilityMeasure_tilted (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ0
      (mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hrr)) hum hu0 g g₀)
  have hid : MemLp (fun σ : ℝ^(N + 1) => σ) 2 G := by
    rw [hG]
    have hconf : ∀ σ : ℝ^(N + 1),
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ ≤
          0 + (|h| * ∑ i, |g₀ i| + |y|) * ‖σ‖ - κ * ‖σ‖ ^ 2 := fun σ => by
      rw [zero_add]; exact neg_shcherbinaTirozziCavityHamiltonian_le κ h y hrr ht0 ht1 hu0 g g₀ σ
    exact_mod_cast memLp_of_poly_bound_of_confining hκ0
      (measurable_shcherbinaTirozziCavityHamiltonian_apply κ h r rBar t y hum g g₀).neg hconf
      (f := fun σ : ℝ^(N + 1) => σ) aestronglyMeasurable_id (C := 1) (m := 1) (fun σ => by simp) 2
  set B : ℝ := ((N : ℝ) + 1) + Real.sqrt (∑ k : Fin M, ∑ i : Fin (N + 1), g k i ^ 2) +
    (∑ i : Fin (N + 1), g₀ i ^ 2) + y ^ 2 with hB
  have hB0 : 0 ≤ B := add_nonneg (add_nonneg (by positivity)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (sq_nonneg y)
  set F : ℝ^(N + 1) → ℝ := fun σ => ((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 with hF
  have hFm : Measurable F := by fun_prop
  have hFb : ∀ σ, |F σ| ≤ 1 * (1 + ‖σ‖) ^ 2 := fun σ => by
    rw [hF, abs_of_nonneg (mul_nonneg (inv_nonneg.2 hN0.le) (sq_nonneg _)), one_mul]
    exact (mul_le_of_le_one_left (sq_nonneg _) (inv_le_one_of_one_le₀ hN1)).trans
      (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) 2)
  set X : ℝ^(N + 1) → ℝ := fun σ =>
    (∑ k : Fin M, deriv u cfield[N, t, g, k, σ] * cfield[N, t, Δg, k, σ]) +
      h * (∑ i, Δg₀ i * σ i) + Real.sqrt (1 - t) * Δy * σ (Fin.last N) with hX
  have hder := hasDerivAt_integral_shcherbinaTirozziCavityGibbs_line (h := h) hκ0 hrr ht0 ht1 hud
    hu0 hD1 y Δy g Δg g₀ Δg₀ hFm hFb
  simp only [zero_mul, add_zero, ← hG] at hder
  refine ⟨_, hder, ?_⟩
  have hFL : MemLp F 2 G := by
    refine (memLp_two_iff_integrable_sq hFm.aestronglyMeasurable).2 ?_
    have h4 := (h319 N M 2 κ h r rBar t y u g g₀ hκ hh ht0 ht1 hrr hrr_diff hM (by omega) hum
      hu0 hD).1
    rw [← hG] at h4
    have e : (fun σ => F σ ^ 2) = fun σ => (((N : ℝ) + 1)⁻¹) ^ 2 * ‖σ‖ ^ (2 * 2) := funext fun σ => by
      rw [hF]; ring
    rw [e]; exact h4.const_mul _
  have hXL := memLp_cavityDisorderDerivative hD1 g Δg Δg₀ G hid X fun _ => rfl
  set f : ℝ^(N + 1) → ℝ := fun σ => F σ - ∫ τ, F τ ∂G with hf
  have hfL : MemLp f 2 G := hFL.sub (memLp_const _)
  have hf0 : ∫ σ, f σ ∂G = 0 := by
    rw [hf, integral_sub (hFL.integrable one_le_two) (integrable_const _), integral_const,
      probReal_univ, one_smul, sub_self]
  have hcov : (∫ σ, F σ * X σ ∂G) - (∫ σ, F σ ∂G) * ∫ σ, X σ ∂G = ∫ σ, f σ * X σ ∂G := by
    have e : (fun σ => f σ * X σ) = fun σ => F σ * X σ - (∫ τ, F τ ∂G) * X σ := funext fun σ => by
      rw [hf]; ring
    have h1 : Integrable (fun σ => F σ * X σ) G := hFL.integrable_mul hXL
    rw [e, integral_sub h1 ((hXL.integrable one_le_two).const_mul _),
      integral_const_mul (∫ τ, F τ ∂G) X]
  have hf2 : ∫ σ, f σ ^ 2 ∂G ≤ K₁₁ * B / ((N : ℝ) + 1) ^ 2 := by
    have h1 := (h335 N M 1 κ h r rBar t y u g g₀ hκ hh ht0 ht1 hrr hrr_diff hM (by omega) hu hu0
      hD G hG).2
    simpa only [mul_one, pow_one, Nat.cast_one] using h1
  have hbary : ‖∫ σ, σ ∂G‖ ^ 2 ≤ K₉ * B := by
    refine (sq_norm_integral_le_integral_sq_norm hid).trans ?_
    have h1 := (h319 N M 1 κ h r rBar t y u g g₀ hκ hh ht0 ht1 hrr hrr_diff hM (by omega) hum
      hu0 hD).2
    rw [← hG] at h1
    simpa only [mul_one, pow_one] using h1
  rw [hcov]
  exact sq_integral_mul_cavityDisorderDerivative_le hκ₀ hκ hh hrr ht0 ht1 hM hu hu0 hD1 hD2
    Δy g Δg g₀ Δg₀ G hG hfL hf0 hK₁₁ hK₉ hB0 hf2 hbary X fun _ => rfl

/-- **Gradient bound for `⟨R_{1,2}⟩_t` along any line of the cavity disorder `(y, g, g₀)`:**
uniform in `t ∈ [0, 1]`. -/
theorem exists_hasDerivAt_integral_shcherbinaTirozziCavity_overlap_line
    (κ₀ h₀ D R_diff : ℝ) (hκ₀ : 0 < κ₀) (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M : ℕ) (κ h r rBar t y Δy : ℝ) (u : ℝ → ℝ)
      (g Δg : Fin M → Fin (N + 1) → ℝ) (g₀ Δg₀ : Fin (N + 1) → ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → rBar ≤ r → r - rBar ≤ R_diff →
      M ≤ 10 * (N + 1) → ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) →
      (∀ x, -D * (1 + |x|) ≤ u x) → Differentiable ℝ u → (∀ x, |deriv u x| ≤ D) →
      (∀ a b, |deriv u a - deriv u b| ≤ D * |a - b|) →
      ∀ G : ℝ → Measure (ℝ^(N + 1)),
      (∀ s, G s = volume.tilted fun σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t (y + s * Δy) u
          (fun k i => g k i + s * Δg k i) (fun i => g₀ i + s * Δg₀ i) σ) →
      ∃ d : ℝ, HasDerivAt (fun s => ∫ p, ((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ ∂((G s).prod (G s))) d 0 ∧
        d ^ 2 ≤ K * ((((N : ℝ) + 1) + Real.sqrt (∑ k : Fin M, ∑ i : Fin (N + 1), g k i ^ 2) +
              (∑ i : Fin (N + 1), g₀ i ^ 2) + y ^ 2) / ((N : ℝ) + 1) ^ 2 +
            (((N : ℝ) + 1) + Real.sqrt (∑ k : Fin M, ∑ i : Fin (N + 1), g k i ^ 2) +
              (∑ i : Fin (N + 1), g₀ i ^ 2) + y ^ 2) ^ 2 * ‖Matrix.of g‖ ^ 2 /
              ((N : ℝ) + 1) ^ 4) *
          ((∑ k : Fin M, ∑ i : Fin (N + 1), Δg k i ^ 2) +
            (∑ i : Fin (N + 1), Δg₀ i ^ 2) + Δy ^ 2) := by
  obtain ⟨K₉, hK₉, h319⟩ :=
    exists_integral_sq_norm_pow_shcherbinaTirozziCavity_le κ₀ h₀ D R_diff hκ₀ hR_diff
  refine ⟨64 * (128 * K₉ / κ₀) / κ₀ * ((4 * D + h₀ + 1) ^ 2 + D ^ 2 * K₉), by positivity,
    fun N M κ h r rBar t y Δy u g Δg g₀ Δg₀ hκ hh ht0 ht1 hrr hrr_diff hM hu hu0 hD hud
      hD1 hD2 G hGs => ?_⟩
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum := hu.measurable_of_univ
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hq : 0 ≤ (1 - t) * (r - rBar) := mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hrr)
  have hG : G 0 = volume.tilted fun σ =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ := by
    rw [hGs 0]; simp
  have hprob : ∀ s, IsProbabilityMeasure (G s) := fun s => by
    rw [hGs s]; exact isProbabilityMeasure_tilted
      (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ0 hq hum hu0 _ _)
  have hidt : ∀ s, MemLp (fun σ : ℝ^(N + 1) => σ) 2 (G s) := fun s => by
    rw [hGs s]
    have hconf : ∀ σ : ℝ^(N + 1),
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t (y + s * Δy) u
            (fun k i => g k i + s * Δg k i) (fun i => g₀ i + s * Δg₀ i) σ ≤
          0 + (|h| * ∑ i, |g₀ i + s * Δg₀ i| + |y + s * Δy|) * ‖σ‖ - κ * ‖σ‖ ^ 2 := fun σ => by
      rw [zero_add]
      exact neg_shcherbinaTirozziCavityHamiltonian_le κ h (y + s * Δy) hrr ht0 ht1 hu0 _ _ σ
    exact_mod_cast memLp_of_poly_bound_of_confining hκ0
      (measurable_shcherbinaTirozziCavityHamiltonian_apply κ h r rBar t _ hum _ _).neg hconf
      (f := fun σ : ℝ^(N + 1) => σ) aestronglyMeasurable_id (C := 1) (m := 1) (fun σ => by simp) 2
  have := hprob 0
  have hid := hidt 0
  set B : ℝ := ((N : ℝ) + 1) + Real.sqrt (∑ k : Fin M, ∑ i : Fin (N + 1), g k i ^ 2) +
    (∑ i : Fin (N + 1), g₀ i ^ 2) + y ^ 2 with hB
  have hB0 : 0 ≤ B := add_nonneg (add_nonneg (by positivity)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (sq_nonneg y)
  set b : ℝ^(N + 1) := ∫ σ, σ ∂(G 0) with hb
  set X : ℝ^(N + 1) → ℝ := fun σ =>
    (∑ k : Fin M, deriv u cfield[N, t, g, k, σ] * cfield[N, t, Δg, k, σ]) +
      h * (∑ i, Δg₀ i * σ i) + Real.sqrt (1 - t) * Δy * σ (Fin.last N) with hX
  have hXL := memLp_cavityDisorderDerivative hD1 g Δg Δg₀ (G 0) hid X fun _ => rfl
  have hcoordL : ∀ i : Fin (N + 1), MemLp (fun σ : ℝ^(N + 1) => σ i) 2 (G 0) :=
    fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hid
  have hbi : ∀ s i, (∫ σ, σ ∂(G s)) i = ∫ σ, σ i ∂(G s) := fun s i =>
    ((EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm ((hidt s).integrable one_le_two)).symm
  have hcoord : ∀ i : Fin (N + 1), HasDerivAt (fun s => ∫ σ, σ i ∂(G s))
      ((∫ σ, σ i * X σ ∂(G 0)) - b i * ∫ σ, X σ ∂(G 0)) 0 := fun i => by
    have hm : Measurable fun σ : ℝ^(N + 1) => σ i :=
      (PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) i).measurable
    have hbound : ∀ σ : ℝ^(N + 1), |σ i| ≤ 1 * (1 + ‖σ‖) ^ 1 := fun σ => by
      have h1 : |σ i| ≤ ‖σ‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le σ i
      rw [one_mul, pow_one]; exact h1.trans (le_add_of_nonneg_left zero_le_one)
    have h := hasDerivAt_integral_shcherbinaTirozziCavityGibbs_line (h := h) hκ0 hrr ht0 ht1 hud
      hu0 hD1 y Δy g Δg g₀ Δg₀ hm hbound
    simp only [← hGs] at h
    rw [hb, hbi]; exact h
  have hsq : HasDerivAt (fun s => ((N : ℝ) + 1)⁻¹ * ∑ i, (∫ σ, σ i ∂(G s)) ^ 2)
      (((N : ℝ) + 1)⁻¹ * ∑ i, 2 * b i * ((∫ σ, σ i * X σ ∂(G 0)) - b i * ∫ σ, X σ ∂(G 0))) 0 := by
    refine (HasDerivAt.fun_sum fun i _ => ?_).const_mul _
    refine ((hcoord i).pow 2).congr_deriv ?_
    rw [hb, hbi]; ring
  have hfun : (fun s => ∫ p, ((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ ∂((G s).prod (G s))) =
      fun s => ((N : ℝ) + 1)⁻¹ * ∑ i, (∫ σ, σ i ∂(G s)) ^ 2 := funext fun s => by
    have := hprob s
    have h1 := (hidt s).integrable one_le_two
    rw [integral_const_mul]
    have h2 : ∫ p, ⟪p.1, p.2⟫ ∂((G s).prod (G s)) = ‖∫ σ, σ ∂(G s)‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]; exact integral_prod_bilin (innerSL ℝ) h1 h1
    rw [h2, EuclideanSpace.real_norm_sq_eq]; simp_rw [hbi]
  rw [hfun]
  refine ⟨_, hsq, ?_⟩
  set f : ℝ^(N + 1) → ℝ := fun σ => 2 * ((N : ℝ) + 1)⁻¹ * (⟪b, σ⟫ - ⟪b, b⟫) with hf
  have hbL : MemLp (fun σ => ⟪b, σ⟫) 2 (G 0) := hid.const_inner b
  have hfL : MemLp f 2 (G 0) := (hbL.sub (memLp_const _)).const_mul _
  have hinner : ∫ σ, ⟪b, σ⟫ ∂(G 0) = ⟪b, b⟫ := integral_inner (hid.integrable one_le_two) b
  have hf0 : ∫ σ, f σ ∂(G 0) = 0 := by
    rw [hf, integral_const_mul, integral_sub (hbL.integrable one_le_two) (integrable_const _),
      hinner, integral_const, probReal_univ, one_smul, sub_self, mul_zero]
  have hcov : ((N : ℝ) + 1)⁻¹ * ∑ i, 2 * b i *
      ((∫ σ, σ i * X σ ∂(G 0)) - b i * ∫ σ, X σ ∂(G 0)) = ∫ σ, f σ * X σ ∂(G 0) := by
    have h1 : ∀ i : Fin (N + 1), Integrable (fun σ => σ i * X σ) (G 0) := fun i =>
      (hcoordL i).integrable_mul hXL
    have h2 : Integrable (fun σ => ⟪b, σ⟫ * X σ) (G 0) := hbL.integrable_mul hXL
    have h3 : ∑ i, b i * ∫ σ, σ i * X σ ∂(G 0) = ∫ σ, ⟪b, σ⟫ * X σ ∂(G 0) := by
      simp_rw [← integral_const_mul]
      rw [← integral_finsetSum _ fun i _ => (h1 i).const_mul _]
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      simp only [PiLp.inner_apply, Finset.sum_mul, RCLike.inner_apply, conj_trivial]
      exact Finset.sum_congr rfl fun i _ => by ring
    have h4 : ∑ i, b i * b i = ⟪b, b⟫ := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    have e : (fun σ => f σ * X σ) = fun σ =>
        2 * ((N : ℝ) + 1)⁻¹ * (⟪b, σ⟫ * X σ) - 2 * ((N : ℝ) + 1)⁻¹ * ⟪b, b⟫ * X σ :=
      funext fun σ => by rw [hf]; ring
    rw [e, integral_sub (h2.const_mul _) ((hXL.integrable one_le_two).const_mul _),
      integral_const_mul, integral_const_mul, ← h3, ← h4]
    have h5 : ∑ i, 2 * b i * ((∫ σ, σ i * X σ ∂(G 0)) - b i * ∫ σ, X σ ∂(G 0)) =
        2 * (∑ i, b i * ∫ σ, σ i * X σ ∂(G 0)) -
          2 * (∑ i, b i * b i) * ∫ σ, X σ ∂(G 0) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h5]; ring
  have hbary : ‖b‖ ^ 2 ≤ K₉ * B := by
    refine (sq_norm_integral_le_integral_sq_norm hid).trans ?_
    have h1 := (h319 N M 1 κ h r rBar t y u g g₀ hκ hh ht0 ht1 hrr hrr_diff hM (by omega) hum
      hu0 hD).2
    rw [← hG] at h1
    simpa only [mul_one, pow_one] using h1
  have hf2 : ∫ σ, f σ ^ 2 ∂(G 0) ≤ 128 * K₉ / κ₀ * B / ((N : ℝ) + 1) ^ 2 := by
    have hlip : ∀ x z : ℝ^(N + 1), |⟪b, x⟫ - ⟪b, z⟫| ≤ ‖b‖ * ‖x - z‖ := fun x z => by
      rw [← inner_sub_right]; exact abs_real_inner_le_norm _ _
    have hMau := (integral_sub_integral_pow_le_of_lipschitz (μ₀ := volume) (C := Set.univ)
      (H := shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀) convex_univ MeasurableSet.univ
      (NeZero.ne _) (measurable_shcherbinaTirozziCavityHamiltonian_apply κ h r rBar t y hum g g₀)
      (integrableOn_univ.2 (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ0 hq hum hu0 g g₀))
      (fun x _ z _ => shcherbinaTirozziCavityHamiltonian_midpoint_gap κ h y hq hu g g₀ x z)
      hκ0 (norm_nonneg b) (fun x _ z _ => hlip x z) 1).2
    simp only [Measure.restrict_univ, ← hG, hinner, Nat.cast_one, mul_one, pow_one] at hMau
    have ef : (fun σ => f σ ^ 2) = fun σ =>
        (2 * ((N : ℝ) + 1)⁻¹) ^ 2 * (⟪b, σ⟫ - ⟪b, b⟫) ^ 2 := funext fun σ => by
      rw [hf, mul_pow]
    rw [ef, integral_const_mul]
    have h1 : (2 * ((N : ℝ) + 1)⁻¹) ^ 2 * (4 * (8 * ‖b‖ ^ 2 / κ)) ≤
        128 * K₉ / κ₀ * B / ((N : ℝ) + 1) ^ 2 := by
      have h2 : ‖b‖ ^ 2 / κ ≤ K₉ * B / κ₀ := div_le_div₀ (mul_nonneg hK₉ hB0) hbary hκ₀ hκ
      calc (2 * ((N : ℝ) + 1)⁻¹) ^ 2 * (4 * (8 * ‖b‖ ^ 2 / κ))
          = 128 / ((N : ℝ) + 1) ^ 2 * (‖b‖ ^ 2 / κ) := by field_simp; ring
        _ ≤ 128 / ((N : ℝ) + 1) ^ 2 * (K₉ * B / κ₀) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 128 * K₉ / κ₀ * B / ((N : ℝ) + 1) ^ 2 := by ring
    exact (mul_le_mul_of_nonneg_left hMau (sq_nonneg _)).trans h1
  rw [hcov]
  exact sq_integral_mul_cavityDisorderDerivative_le hκ₀ hκ hh hrr ht0 ht1 hM hu hu0 hD1 hD2
    Δy g Δg g₀ Δg₀ (G 0) hG hfL hf0 (by positivity) hK₉ hB0 hf2 hbary X fun _ => rfl

end CavityGradient

end SpinGlasses
