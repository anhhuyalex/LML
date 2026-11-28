/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianConvexConcentration
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianMatrixNorm
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.CavityDerivative
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.DisorderConcentration

/-!
# The Shcherbina--Tirozzi model: uniform-in-`t` overlap concentration along the cavity path

Along the cavity path `H_{N,M,t}` of Eq. (3.61) on `ℝ^(N+1)`, Talagrand's Section 3.1 overlap
concentration (Theorem 3.1.18) holds uniformly in `t ∈ [0, 1]`, giving Eq. (3.111):
```
ν_t ((R_{1,1} - ρ_t) ^ (2 k)) ≤ (K k / (N + 1)) ^ k,
ν_t ((R_{1,2} - q_t) ^ (2 k)) ≤ (K k / (N + 1)) ^ k,
```
for `4 k ≤ N + 1`, where `q_t = ν_t(R_{1,2})`, `ρ_t = ν_t(R_{1,1})`, and `K` depends only on
`κ₀, h₀, D, R, R_diff`.

The proof follows Section 3.1 word for word with the cavity radius
`B^*_{cav}(y, g, g₀) = (N + 1) + √(∑_{k,i} g_{k,i}²) + ∑_i g₀_i² + y²`:
1. Quenched exponential moment `⟨exp (κ ‖σ‖² / 2)⟩_t ≤ exp (K₁ B^*_{cav})` and `2k`-th norm
   moments `⟨‖σ‖^{2k}⟩_t ≤ (K₉ B^*_{cav})^k` for `k ≤ 4(N+1)`.
2. Quenched Maurey concentration for `R_{1,2} - ⟨R_{1,2}⟩_t` and `R_{1,1} - ⟨R_{1,1}⟩_t`.
3. Disorder gradient bound for `⟨R_{1,1}⟩_t` and `⟨R_{1,2}⟩_t` as functions of `(y, g, g₀)`.
4. Gaussian concentration on the convex good disorder set `{B^*_{cav} ≤ L(N+1), ‖g‖ ≤ √(L(N+1))}`
   for `(y/√r, g, g₀)` (or `(g, g₀)` when `r = 0`), combined with the quenched concentration.

## Main declarations

* `SpinGlasses.exists_integral_shcherbinaTirozziCavity_selfOverlap_sub_pow_le`: Eq. (3.111) for
  `R_{1,1}` (arbitrary `4 k ≤ N + 1`).
* `SpinGlasses.exists_integral_shcherbinaTirozziCavity_overlap_sub_pow_le`: Eq. (3.111) for
  `R_{1,2}` (arbitrary `4 k ≤ N + 1`).
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

local notation "B_cav[" N ", " M "]" d:arg =>
  ((N : ℝ) + 1) + Real.sqrt (∑ k : Fin M, ∑ i : Fin (N + 1), d.2.1 k i ^ 2) +
    (∑ i : Fin (N + 1), d.2.2 i ^ 2) + d.1 ^ 2

local notation "cfield[" N ", " t ", " g ", " k ", " σ "]" =>
  (Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, g k (Fin.castSucc i) * σ (Fin.castSucc i)) +
    Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N)))

section QuenchedMoments

/-- The cavity Gibbs measure is a probability measure whenever `κ > 0`, `rBar ≤ r`, `t ≤ 1`,
`u` is measurable and `u ≤ 0`. -/
private theorem isProbabilityMeasure_shcherbinaTirozziCavityGibbs {N M : ℕ}
    {κ h r rBar t y : ℝ} (hκ : 0 < κ) (hrr : rBar ≤ r) (ht1 : t ≤ 1)
    {u : ℝ → ℝ} (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0)
    (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) :
    IsProbabilityMeasure ((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ) :=
  isProbabilityMeasure_tilted (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ
    (mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hrr)) hu hu0 g g₀)

/-- Square integrability of the configuration under the cavity Gibbs measure. -/
private theorem memLp_id_shcherbinaTirozziCavityGibbs {N M : ℕ}
    {κ h r rBar t y : ℝ} (hκ : 0 < κ) (hrr : rBar ≤ r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {u : ℝ → ℝ} (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0)
    (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) :
    MemLp (fun σ : ℝ^(N + 1) => σ) 2
      ((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ) := by
  have hconf : ∀ σ : ℝ^(N + 1),
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ ≤
        0 + (|h| * ∑ i, |g₀ i| + |y|) * ‖σ‖ - κ * ‖σ‖ ^ 2 := fun σ => by
    rw [zero_add]
    exact neg_shcherbinaTirozziCavityHamiltonian_le κ h y hrr ht0 ht1 hu0 g g₀ σ
  exact_mod_cast memLp_of_poly_bound_of_confining hκ
    (measurable_shcherbinaTirozziCavityHamiltonian_apply κ h r rBar t y hu g g₀).neg hconf
    (f := fun σ : ℝ^(N + 1) => σ) aestronglyMeasurable_id (C := 1) (m := 1) (fun σ => by simp) 2

/-- **Quenched exponential squared-norm bound along the cavity path (uniform in `t ∈ [0, 1]`):**
`⟨exp (κ ‖σ‖² / 2)⟩_t ≤ exp (K₁ * B_cav(y, g, g₀))` with `K₁` depending only on
`κ₀, h₀, D, R_diff`. -/
theorem exists_integral_exp_half_sq_norm_shcherbinaTirozziCavity_le_exp
    (κ₀ h₀ D R_diff : ℝ) (hκ₀ : 0 < κ₀) (hR_diff : 0 ≤ R_diff) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ (N M : ℕ) (κ h r rBar t y : ℝ) (u : ℝ → ℝ)
      (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → rBar ≤ r → r - rBar ≤ R_diff →
      M ≤ 10 * (N + 1) → Measurable u → (∀ x, u x ≤ 0) → (∀ x, -D * (1 + |x|) ≤ u x) →
      let G := (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ
      Integrable (fun σ : ℝ^(N + 1) => Real.exp (κ / 2 * ‖σ‖ ^ 2)) G ∧
        ∫ σ, Real.exp (κ / 2 * ‖σ‖ ^ 2) ∂G ≤
          Real.exp (K₁ * (((N : ℝ) + 1) +
            Real.sqrt (∑ k : Fin M, ∑ i : Fin (N + 1), g k i ^ 2) +
            (∑ i : Fin (N + 1), g₀ i ^ 2) + y ^ 2)) := by
  set K₁ : ℝ := 1 + 10 * |D| + |D| * Real.sqrt (10 / κ₀) + R_diff / (4 * κ₀) +
    (h₀ ^ 2 + 1) / κ₀ with hK₁
  refine ⟨K₁, by positivity, fun N M κ h r rBar t y u g g₀ hκ hh ht0 ht1 hrr hrr_diff hM
    hu hu0 hD => ?_⟩
  intro G
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hD0 : 0 ≤ D := by
    have h1 := (hD 0).trans (hu0 0)
    simp only [abs_zero, add_zero, mul_one] at h1
    linarith
  have hcast : ∀ i : Fin N, (i.castSucc : Fin (N + 1)) ≠ Fin.last N :=
    fun i => (Fin.castSucc_lt_last i).ne
  set v_vec : Fin M → ℝ^(N + 1) := fun k => WithLp.toLp 2 fun i =>
    (Real.sqrt (N + 1))⁻¹ * ((if i = Fin.last N then Real.sqrt t else 1) * g k i)
  have hv_inner : ∀ (k : Fin M) (σ : ℝ^(N + 1)),
      ⟪v_vec k, σ⟫ = cfield[N, t, g, k, σ] := fun k σ => by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
      Fin.sum_univ_castSucc (n := N)]
    simp only [v_vec, hcast, reduceIte, one_mul, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · ring
  have hv_norm : ∀ k : Fin M, ‖v_vec k‖ ^ 2 ≤
      ((N : ℝ) + 1)⁻¹ * ∑ i : Fin (N + 1), g k i ^ 2 := fun k => by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    dsimp only [v_vec]
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [mul_pow]
    refine mul_le_of_le_one_left (sq_nonneg _) ?_
    split
    · rw [Real.sq_sqrt ht0]; exact ht1
    · norm_num
  set U : ℝ^(N + 1) → ℝ := fun σ =>
    (∑ k : Fin M, u ⟪v_vec k, σ⟫) - (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2
  set a : ℝ^(N + 1) := WithLp.toLp 2 fun i =>
    h * g₀ i + if i = Fin.last N then Real.sqrt (1 - t) * y else 0
  have ha_inner : ∀ σ : ℝ^(N + 1),
      ⟪a, σ⟫ = h * (∑ i, g₀ i * σ i) + σ (Fin.last N) * (Real.sqrt (1 - t) * y) := fun σ => by
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
    simp only [a, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, reduceIte, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
  have hH_eq : (fun σ : ℝ^(N + 1) =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ) =
      fun σ => U σ - κ * ‖σ‖ ^ 2 + ⟪a, σ⟫ := funext fun σ => by
    simp only [shcherbinaTirozziCavityHamiltonian, U, hv_inner, ha_inner]
    ring
  have hUm : Measurable U :=
    (Finset.measurable_sum _ fun k _ => hu.comp (by fun_prop)).sub
      ((((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable.pow_const
        2).const_mul _).div_const 2)
  have hU0 : ∀ σ, U σ ≤ 0 := fun σ => by
    dsimp only [U]
    have h1 : ∑ k : Fin M, u ⟪v_vec k, σ⟫ ≤ 0 := Finset.sum_nonpos fun k _ => hu0 _
    have h2 : 0 ≤ (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2 :=
      div_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hrr)) (sq_nonneg _))
        zero_le_two
    linarith
  set c : ℝ := (Real.sqrt (2 * κ))⁻¹
  have hc0 : 0 < c := inv_pos.2 (Real.sqrt_pos.2 (by positivity))
  have hcκ : c ≤ (Real.sqrt κ)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.2 hκ0) (Real.sqrt_le_sqrt (by linarith))
  have hk_int : ∀ k : Fin M, Integrable (fun z : ℝ^(N + 1) => u ⟪v_vec k, c • z⟫)
      (stdGaussian (ℝ^(N + 1))) ∧
      ‖∫ z : ℝ^(N + 1), u ⟪v_vec k, c • z⟫ ∂stdGaussian (ℝ^(N + 1))‖ ≤ D + D * c * ‖v_vec k‖ :=
    fun k => integrable_and_norm_integral_stdGaussian_le_of_le_abs_inner
      (hu.comp (by fun_prop : Measurable fun z : ℝ^(N + 1) =>
        ⟪v_vec k, c • z⟫)).aestronglyMeasurable
      (mul_nonneg hD0 hc0.le) fun z => by
        rw [Function.comp_apply, Real.norm_eq_abs, abs_of_nonpos (hu0 _), neg_le]
        refine le_trans (le_of_eq ?_) (hD _)
        rw [real_inner_smul_right, abs_mul, abs_of_pos hc0]
        ring
  set e_last : ℝ^(N + 1) := EuclideanSpace.single (Fin.last N) (1 : ℝ)
  have he_last_norm : ‖e_last‖ = 1 := by simp [e_last]
  have hlast_inner : ∀ z : ℝ^(N + 1), z (Fin.last N) = ⟪e_last, z⟫ := fun z => by
    simp [e_last, EuclideanSpace.inner_single_left]
  have hq_int : Integrable (fun z : ℝ^(N + 1) =>
      (1 - t) * (r - rBar) * ((c • z) (Fin.last N)) ^ 2 / 2) (stdGaussian (ℝ^(N + 1))) := by
    have h1 : MemLp (fun z : ℝ^(N + 1) => z (Fin.last N)) 2 (stdGaussian (ℝ^(N + 1))) := by
      have hmp : MeasurePreserving (fun z : ℝ^(N + 1) => z.ofLp)
          (stdGaussian (ℝ^(N + 1))) (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) :=
        ⟨WithLp.measurable_ofLp 2 _, pi_gaussianReal_eq_map_stdGaussian.symm⟩
      exact (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
        ((measurePreserving_eval (fun _ : Fin (N + 1) => gaussianReal 0 1) (Fin.last N)).comp hmp)
    have hsq : Integrable (fun z : ℝ^(N + 1) => z (Fin.last N) ^ 2) (stdGaussian (ℝ^(N + 1))) :=
      h1.integrable_sq
    have heq : (fun z : ℝ^(N + 1) => (1 - t) * (r - rBar) * ((c • z) (Fin.last N)) ^ 2 / 2) =
        fun z => ((1 - t) * (r - rBar) * c ^ 2 / 2) * z (Fin.last N) ^ 2 := funext fun z => by
      change (1 - t) * (r - rBar) * (c * z (Fin.last N)) ^ 2 / 2 = _
      ring
    rw [heq]
    exact hsq.const_mul _
  have hq_eval : ∫ z : ℝ^(N + 1), (1 - t) * (r - rBar) * ((c • z) (Fin.last N)) ^ 2 / 2
      ∂stdGaussian (ℝ^(N + 1)) = (1 - t) * (r - rBar) / (4 * κ) := by
    have heq : (fun z : ℝ^(N + 1) => (1 - t) * (r - rBar) * ((c • z) (Fin.last N)) ^ 2 / 2) =
        fun z => ((1 - t) * (r - rBar) * c ^ 2 / 2) * (⟪e_last, z⟫ * ⟪e_last, z⟫) :=
      funext fun z => by
        rw [← hlast_inner]
        change (1 - t) * (r - rBar) * (c * z (Fin.last N)) ^ 2 / 2 = _
        ring
    rw [heq, integral_const_mul, integral_inner_mul_inner_stdGaussian, real_inner_self_eq_norm_sq,
      he_last_norm, one_pow, mul_one]
    have hc2 : c ^ 2 = (2 * κ)⁻¹ := by dsimp only [c]; rw [inv_pow, Real.sq_sqrt (by positivity)]
    rw [hc2]; field_simp; ring
  have hUi : Integrable (fun z : ℝ^(N + 1) => U (c • z)) (stdGaussian (ℝ^(N + 1))) :=
    (integrable_finsetSum _ fun k _ => (hk_int k).1).sub hq_int
  have hkey := integral_exp_half_sq_norm_tilted_le_two_rpow hUm hU0 hκ0 a hUi
  rw [← hH_eq, finrank_euclideanSpace_fin] at hkey
  refine ⟨hkey.1, hkey.2.trans ?_⟩
  -- Bound each piece by `K₁ * B_cav`
  set S : ℝ := ∑ k : Fin M, ∑ i : Fin (N + 1), g k i ^ 2
  set T : ℝ := ∑ i : Fin (N + 1), g₀ i ^ 2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2pow : (2 : ℝ) ^ (((N + 1 : ℕ) : ℝ) / 2) ≤ Real.exp ((N : ℝ) + 1) := by
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    refine (Real.rpow_le_rpow zero_le_two h2e (by positivity)).trans ?_
    rw [Real.exp_one_rpow, Real.exp_le_exp]
    push_cast; linarith [Nat.cast_nonneg (α := ℝ) N]
  have ha_sq : ‖a‖ ^ 2 / (2 * κ) ≤ (h₀ ^ 2 + 1) / κ₀ * (T + y ^ 2) := by
    have hnorm_a : ‖a‖ ^ 2 ≤ 2 * (h ^ 2 * T + y ^ 2) := by
      rw [EuclideanSpace.real_norm_sq_eq]
      have hpt : ∀ i : Fin (N + 1), a i ^ 2 ≤
          2 * h ^ 2 * g₀ i ^ 2 + 2 * (if i = Fin.last N then y ^ 2 else 0) := fun i => by
        dsimp only [a]
        split_ifs with hi
        · have h1 : (h * g₀ i + Real.sqrt (1 - t) * y) ^ 2 ≤
              2 * (h * g₀ i) ^ 2 + 2 * (Real.sqrt (1 - t) * y) ^ 2 := by
            nlinarith [sq_nonneg (h * g₀ i - Real.sqrt (1 - t) * y)]
          have h2 : (Real.sqrt (1 - t) * y) ^ 2 ≤ y ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (sub_nonneg.2 ht1)]
            exact mul_le_of_le_one_left (sq_nonneg y) (by linarith)
          linarith [show (h * g₀ i) ^ 2 = h ^ 2 * g₀ i ^ 2 by ring]
        · rw [add_zero, mul_zero, add_zero, mul_pow]
          nlinarith [sq_nonneg (h * g₀ i)]
      calc ∑ i, a i ^ 2 ≤ ∑ i, (2 * h ^ 2 * g₀ i ^ 2 +
              2 * (if i = Fin.last N then y ^ 2 else 0)) := Finset.sum_le_sum fun i _ => hpt i
        _ = 2 * h ^ 2 * T + 2 * y ^ 2 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq']
            simp [T]
        _ = 2 * (h ^ 2 * T + y ^ 2) := by ring
    have hh2 : h ^ 2 ≤ h₀ ^ 2 := by
      rw [← sq_abs h]; exact pow_le_pow_left₀ (abs_nonneg _) hh 2
    have hnum : ‖a‖ ^ 2 ≤ 2 * ((h₀ ^ 2 + 1) * (T + y ^ 2)) := by
      nlinarith [mul_le_mul_of_nonneg_right hh2 hT0, sq_nonneg y, sq_nonneg h₀]
    calc ‖a‖ ^ 2 / (2 * κ) ≤ (2 * ((h₀ ^ 2 + 1) * (T + y ^ 2))) / (2 * κ) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = (h₀ ^ 2 + 1) / κ * (T + y ^ 2) := by field_simp
      _ ≤ (h₀ ^ 2 + 1) / κ₀ * (T + y ^ 2) :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_left (by positivity) hκ₀ hκ) (by positivity)
  have hEU : -(∫ z : ℝ^(N + 1), U (c • z) ∂stdGaussian (ℝ^(N + 1))) ≤
      10 * D * ((N : ℝ) + 1) + D * Real.sqrt (10 / κ₀) * Real.sqrt S +
        R_diff / (4 * κ₀) * ((N : ℝ) + 1) := by
    have hsplit : ∫ z : ℝ^(N + 1), U (c • z) ∂stdGaussian (ℝ^(N + 1)) =
        (∑ k : Fin M, ∫ z : ℝ^(N + 1), u ⟪v_vec k, c • z⟫ ∂stdGaussian (ℝ^(N + 1))) -
          (1 - t) * (r - rBar) / (4 * κ) := by
      dsimp only [U]
      rw [integral_sub (integrable_finsetSum _ fun k _ => (hk_int k).1) hq_int,
        integral_finsetSum _ fun k _ => (hk_int k).1, hq_eval]
    rw [hsplit, neg_sub]
    have hsum_v : ∑ k : Fin M, ‖v_vec k‖ ≤ Real.sqrt (M * ((N : ℝ) + 1)⁻¹ * S) := by
      have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin M)))
        (f := fun k => ‖v_vec k‖)
      rw [Finset.card_univ, Fintype.card_fin] at hcs
      have hss : ∑ k : Fin M, ‖v_vec k‖ ^ 2 ≤ ((N : ℝ) + 1)⁻¹ * S := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum fun k _ => hv_norm k
      exact Real.le_sqrt_of_sq_le (hcs.trans ((mul_le_mul_of_nonneg_left hss
        (Nat.cast_nonneg M)).trans_eq (by ring)))
    have hsum_u : -(∑ k : Fin M, ∫ z : ℝ^(N + 1), u ⟪v_vec k, c • z⟫ ∂stdGaussian (ℝ^(N + 1))) ≤
        D * M + D * c * Real.sqrt (M * ((N : ℝ) + 1)⁻¹ * S) := by
      rw [← Finset.sum_neg_distrib]
      calc ∑ k : Fin M, -(∫ z : ℝ^(N + 1), u ⟪v_vec k, c • z⟫ ∂stdGaussian (ℝ^(N + 1)))
          ≤ ∑ k : Fin M, (D + D * c * ‖v_vec k‖) :=
            Finset.sum_le_sum fun k _ => by
              have h := (hk_int k).2
              rw [Real.norm_eq_abs] at h
              exact neg_le.1 (neg_le_of_abs_le h)
        _ = D * M + D * c * ∑ k : Fin M, ‖v_vec k‖ := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              nsmul_eq_mul, mul_comm (M : ℝ) D, ← Finset.mul_sum]
        _ ≤ D * M + D * c * Real.sqrt (M * ((N : ℝ) + 1)⁻¹ * S) :=
            add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum_v (by positivity))
    have hM' : (M : ℝ) ≤ 10 * ((N : ℝ) + 1) := by exact_mod_cast hM
    have hMN10 : (M : ℝ) * ((N : ℝ) + 1)⁻¹ ≤ 10 := by
      rw [mul_inv_le_iff₀ (by positivity)]; exact hM'
    have hsqrt_le : c * Real.sqrt (M * ((N : ℝ) + 1)⁻¹ * S) ≤
        Real.sqrt (10 / κ₀) * Real.sqrt S := by
      rw [Real.sqrt_mul (by positivity), ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg S)
      have hc2 : c ≤ Real.sqrt (1 / κ₀) :=
        hcκ.trans (by
          rw [one_div, Real.sqrt_inv]
          exact inv_anti₀ (Real.sqrt_pos.2 hκ₀) (Real.sqrt_le_sqrt hκ))
      calc c * Real.sqrt (M * ((N : ℝ) + 1)⁻¹)
          ≤ Real.sqrt (1 / κ₀) * Real.sqrt 10 :=
            mul_le_mul hc2 (Real.sqrt_le_sqrt hMN10) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        _ = Real.sqrt (10 / κ₀) := by rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
    have hq_le : (1 - t) * (r - rBar) / (4 * κ) ≤ R_diff / (4 * κ₀) * ((N : ℝ) + 1) := by
      have h1 : (1 - t) * (r - rBar) ≤ R_diff :=
        (mul_le_of_le_one_left (sub_nonneg.2 hrr) (by linarith)).trans hrr_diff
      have h2 : (1 - t) * (r - rBar) / (4 * κ) ≤ R_diff / (4 * κ₀) :=
        div_le_div₀ hR_diff h1 (by positivity) (by linarith)
      exact h2.trans (le_mul_of_one_le_right (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) N]))
    have hDM : D * M ≤ 10 * D * ((N : ℝ) + 1) := by nlinarith
    have hDc : D * c * Real.sqrt (M * ((N : ℝ) + 1)⁻¹ * S) ≤
        D * Real.sqrt (10 / κ₀) * Real.sqrt S := by
      rw [mul_assoc D, mul_assoc D]; exact mul_le_mul_of_nonneg_left hsqrt_le hD0
    linarith
  calc (2 : ℝ) ^ (((N + 1 : ℕ) : ℝ) / 2) *
        Real.exp (‖a‖ ^ 2 / (2 * κ) - ∫ z, U (c • z) ∂stdGaussian (ℝ^(N + 1)))
      ≤ Real.exp ((N : ℝ) + 1) *
          Real.exp (‖a‖ ^ 2 / (2 * κ) - ∫ z, U (c • z) ∂stdGaussian (ℝ^(N + 1))) :=
        mul_le_mul_of_nonneg_right h2pow (Real.exp_pos _).le
    _ = Real.exp (((N : ℝ) + 1) + (‖a‖ ^ 2 / (2 * κ) + -(∫ z, U (c • z) ∂stdGaussian (ℝ^(N + 1))))) := by
        rw [← Real.exp_add, sub_eq_add_neg]
    _ ≤ Real.exp (K₁ * (((N : ℝ) + 1) + Real.sqrt S + T + y ^ 2)) := by
        rw [Real.exp_le_exp]
        have hDabs : |D| = D := abs_of_nonneg hD0
        rw [hK₁, hDabs]
        have hN1 : (0 : ℝ) ≤ (N : ℝ) + 1 := by positivity
        have hN_term : (1 + 10 * D + R_diff / (4 * κ₀)) * ((N : ℝ) + 1) ≤
            (1 + 10 * D + D * Real.sqrt (10 / κ₀) + R_diff / (4 * κ₀) +
              (h₀ ^ 2 + 1) / κ₀) * ((N : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (by linarith [show 0 ≤ D * Real.sqrt (10 / κ₀) by positivity,
            show 0 ≤ (h₀ ^ 2 + 1) / κ₀ by positivity]) hN1
        have hpos1 : 0 ≤ 1 + 10 * D + R_diff / (4 * κ₀) + (h₀ ^ 2 + 1) / κ₀ := by positivity
        have hpos2 : 0 ≤ 1 + 10 * D + D * Real.sqrt (10 / κ₀) + R_diff / (4 * κ₀) := by positivity
        have hS_term : D * Real.sqrt (10 / κ₀) * Real.sqrt S ≤
            (1 + 10 * D + D * Real.sqrt (10 / κ₀) + R_diff / (4 * κ₀) +
              (h₀ ^ 2 + 1) / κ₀) * Real.sqrt S :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg S)
        have hTy_term : (h₀ ^ 2 + 1) / κ₀ * (T + y ^ 2) ≤
            (1 + 10 * D + D * Real.sqrt (10 / κ₀) + R_diff / (4 * κ₀) +
              (h₀ ^ 2 + 1) / κ₀) * (T + y ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        linarith

/-- **Quenched `2k`-th norm moments along the cavity path (uniform in `t ∈ [0, 1]`):**
for `k ≤ 4 * (N + 1)`, `⟨‖σ‖^{2k}⟩_t ≤ (K₉ * B_cav(y, g, g₀))^k`, with `K₉` depending only on
`κ₀, h₀, D, R_diff`. -/
theorem exists_integral_sq_norm_pow_shcherbinaTirozziCavity_le
    (κ₀ h₀ D R_diff : ℝ) (hκ₀ : 0 < κ₀) (hR_diff : 0 ≤ R_diff) :
    ∃ K₉ : ℝ, 0 ≤ K₉ ∧ ∀ (N M k : ℕ) (κ h r rBar t y : ℝ) (u : ℝ → ℝ)
      (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → rBar ≤ r → r - rBar ≤ R_diff →
      M ≤ 10 * (N + 1) → k ≤ 4 * (N + 1) → Measurable u → (∀ x, u x ≤ 0) →
      (∀ x, -D * (1 + |x|) ≤ u x) →
      let G := (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ
      Integrable (fun σ : ℝ^(N + 1) => ‖σ‖ ^ (2 * k)) G ∧
        ∫ σ, ‖σ‖ ^ (2 * k) ∂G ≤
          (K₉ * (((N : ℝ) + 1) +
            Real.sqrt (∑ k : Fin M, ∑ i : Fin (N + 1), g k i ^ 2) +
            (∑ i : Fin (N + 1), g₀ i ^ 2) + y ^ 2)) ^ k := by
  obtain ⟨K₁, hK₁, h317⟩ :=
    exists_integral_exp_half_sq_norm_shcherbinaTirozziCavity_le_exp κ₀ h₀ D R_diff hκ₀ hR_diff
  refine ⟨4 / κ₀ * (4 + K₁), by positivity,
    fun N M k κ h r rBar t y u g g₀ hκ hh ht0 ht1 hrr hrr_diff hM hk hu hu0 hD => ?_⟩
  intro G
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have := isProbabilityMeasure_shcherbinaTirozziCavityGibbs (h := h) (y := y) hκ0 hrr ht1 hu hu0 g g₀
  set B : ℝ := ((N : ℝ) + 1) + Real.sqrt (∑ k : Fin M, ∑ i : Fin (N + 1), g k i ^ 2) +
    (∑ i : Fin (N + 1), g₀ i ^ 2) + y ^ 2 with hB
  have hNB : ((N : ℝ) + 1) ≤ B := by
    have h2 : 0 ≤ ∑ i : Fin (N + 1), g₀ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [hB]; linarith [Real.sqrt_nonneg (∑ k : Fin M, ∑ i : Fin (N + 1), g k i ^ 2), sq_nonneg y]
  have hB0 : 0 ≤ B := le_trans (by positivity) hNB
  have hX0 : 0 ≤ᵐ[G] fun σ : ℝ^(N + 1) => κ / 2 * ‖σ‖ ^ 2 :=
    ae_of_all _ fun σ => mul_nonneg (by positivity) (sq_nonneg _)
  obtain ⟨hexp_i, hexp_le⟩ := h317 N M κ h r rBar t y u g g₀ hκ hh ht0 ht1 hrr hrr_diff hM hu
    hu0 hD
  have hmom := integral_pow_le_of_integral_exp_le hX0 hexp_i hexp_le k
  have hpow : ∀ σ : ℝ^(N + 1),
      ‖σ‖ ^ (2 * k) = (2 / κ) ^ k * (κ / 2 * ‖σ‖ ^ 2) ^ k := fun σ => by
    rw [← mul_pow, pow_mul]; congr 1; field_simp
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  simp_rw [hpow]
  refine ⟨hmom.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  refine (mul_le_mul_of_nonneg_left hmom.2 (by positivity)).trans ?_
  have h1 : (k : ℝ) ^ k ≤ (4 * B) ^ k := by
    refine pow_le_pow_left₀ (Nat.cast_nonneg _) ?_ k
    have h4 : (k : ℝ) ≤ 4 * ((N : ℝ) + 1) := by exact_mod_cast hk
    exact h4.trans (mul_le_mul_of_nonneg_left hNB (by norm_num))
  have h2 : (k : ℝ) ^ k + (K₁ * B) ^ k ≤ ((4 + K₁) * B) ^ k := by
    refine (add_le_add h1 le_rfl).trans ?_
    rw [add_mul]
    exact pow_add_pow_le (by positivity) (mul_nonneg hK₁ hB0) hk0
  have h3 : (2 / κ) ^ k * 2 ^ k ≤ (4 / κ₀) ^ k := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ k
    rw [div_mul_eq_mul_div]
    exact div_le_div₀ (by norm_num) (by norm_num) hκ₀ hκ
  calc (2 / κ) ^ k * (2 ^ k * ((k : ℝ) ^ k + (K₁ * B) ^ k))
      = ((2 / κ) ^ k * 2 ^ k) * ((k : ℝ) ^ k + (K₁ * B) ^ k) := by ring
    _ ≤ (4 / κ₀) ^ k * ((4 + K₁) * B) ^ k :=
        mul_le_mul h3 h2 (add_nonneg (by positivity) (pow_nonneg (mul_nonneg hK₁ hB0) _))
          (by positivity)
    _ = (4 / κ₀ * (4 + K₁) * B) ^ k := by rw [← mul_pow]; ring

end QuenchedMoments

section QuenchedConcentration

/-- **Maurey's inequality for the cavity Gibbs measure:** for concave `u ≤ 0`, `rBar ≤ r`,
`t ≤ 1`, and an `A`-Lipschitz function `f` on `ℝ^(N+1)`,
`⟨(f - ⟨f⟩_t) ^ (2 k)⟩_t ≤ 4 (8 k A² / κ) ^ k`. -/
private theorem integral_sub_integral_pow_shcherbinaTirozziCavityGibbs_le {N M : ℕ}
    {κ h r rBar t y : ℝ} (hκ : 0 < κ) (hrr : rBar ≤ r) (ht1 : t ≤ 1)
    {u : ℝ → ℝ} (hu : ConcaveOn ℝ Set.univ u) (hu0 : ∀ x, u x ≤ 0)
    (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ)
    {f : ℝ^(N + 1) → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hlip : ∀ x z, |f x - f z| ≤ A * ‖x - z‖) (k : ℕ) :
    let G := (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ
    Integrable (fun σ => (f σ - ∫ τ, f τ ∂G) ^ (2 * k)) G ∧
      ∫ σ, (f σ - ∫ τ, f τ ∂G) ^ (2 * k) ∂G ≤ 4 * (8 * k * A ^ 2 / κ) ^ k := by
  have hq : 0 ≤ (1 - t) * (r - rBar) := mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hrr)
  have key := integral_sub_integral_pow_le_of_lipschitz (μ₀ := volume) (C := Set.univ)
    (H := shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀) convex_univ MeasurableSet.univ
    (NeZero.ne _)
    (measurable_shcherbinaTirozziCavityHamiltonian_apply κ h r rBar t y hu.measurable_of_univ g g₀)
    (integrableOn_univ.2 (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ hq
      hu.measurable_of_univ hu0 g g₀))
    (fun x _ z _ => shcherbinaTirozziCavityHamiltonian_midpoint_gap κ h y hq hu g g₀ x z)
    hκ hA (fun x _ z _ => hlip x z) k
  simpa only [Measure.restrict_univ] using key

/-- **Quenched overlap concentration for `R_{1,2}` along the cavity path (uniform in `t`):**
for `k ≤ N + 1`, `⟨(R_{1,2} - ⟨R_{1,2}⟩_t) ^ (2 k)⟩_t ≤ (K k B_cav / (N + 1)²) ^ k`. -/
theorem exists_integral_shcherbinaTirozziCavity_overlap_sub_mean_pow_le
    (κ₀ h₀ D R_diff : ℝ) (hκ₀ : 0 < κ₀) (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M k : ℕ) (κ h r rBar t y : ℝ) (u : ℝ → ℝ)
      (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → rBar ≤ r → r - rBar ≤ R_diff →
      M ≤ 10 * (N + 1) → k ≤ N + 1 →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → (∀ x, -D * (1 + |x|) ≤ u x) →
      ∀ G : Measure (ℝ^(N + 1)),
        G = volume.tilted (fun σ => -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ) →
        Integrable (fun p : ℝ^(N + 1) × ℝ^(N + 1) =>
            (((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ -
              ∫ q, ((N : ℝ) + 1)⁻¹ * ⟪q.1, q.2⟫ ∂(G.prod G)) ^ (2 * k))
            (G.prod G) ∧
          ∫ p, (((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ -
              ∫ q, ((N : ℝ) + 1)⁻¹ * ⟪q.1, q.2⟫ ∂(G.prod G)) ^ (2 * k)
              ∂(G.prod G) ≤
            (K * k * (((N : ℝ) + 1) +
              Real.sqrt (∑ k : Fin M, ∑ i : Fin (N + 1), g k i ^ 2) +
              (∑ i : Fin (N + 1), g₀ i ^ 2) + y ^ 2) / ((N : ℝ) + 1) ^ 2) ^ k := by
  obtain ⟨K₉, hK₉, h319⟩ :=
    exists_integral_sq_norm_pow_shcherbinaTirozziCavity_le κ₀ h₀ D R_diff hκ₀ hR_diff
  refine ⟨128 * K₉ / κ₀, by positivity,
    fun N M k κ h r rBar t y u g g₀ hκ hh ht0 ht1 hrr hrr_diff hM hk hu hu0 hD G hG => ?_⟩
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum := hu.measurable_of_univ
  have : IsProbabilityMeasure G := by
    rw [hG]; exact isProbabilityMeasure_shcherbinaTirozziCavityGibbs (h := h) (y := y) hκ0 hrr ht1
      hum hu0 g g₀
  set B : ℝ := ((N : ℝ) + 1) + Real.sqrt (∑ k : Fin M, ∑ i : Fin (N + 1), g k i ^ 2) +
    (∑ i : Fin (N + 1), g₀ i ^ 2) + y ^ 2 with hB
  have hB0 : 0 ≤ B := add_nonneg (add_nonneg (by positivity)
    (Finset.sum_nonneg fun i _ => sq_nonneg _)) (sq_nonneg y)
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hmom : ∀ j, j ≤ 4 * (N + 1) → Integrable (fun σ : ℝ^(N + 1) => ‖σ‖ ^ (2 * j)) G ∧
      ∫ σ, ‖σ‖ ^ (2 * j) ∂G ≤ (K₉ * B) ^ j := fun j hj => by
    rw [hG]
    exact h319 N M j κ h r rBar t y u g g₀ hκ hh ht0 ht1 hrr hrr_diff hM hj hum hu0 hD
  have hk4 : k ≤ 4 * (N + 1) := by omega
  have hnorm : Integrable (fun σ : ℝ^(N + 1) => ‖σ‖) G := by
    refine Integrable.mono' ((integrable_const 1).add (hmom 1 (by omega)).1)
      continuous_norm.aestronglyMeasurable (ae_of_all _ fun σ => ?_)
    rw [norm_norm, Pi.add_apply, mul_one]
    nlinarith [sq_nonneg (‖σ‖ - 1), norm_nonneg σ]
  have hid : Integrable (fun σ : ℝ^(N + 1) => σ) G :=
    (integrable_norm_iff aestronglyMeasurable_id).1 hnorm
  set b : ℝ^(N + 1) := ∫ σ, σ ∂G with hb
  have hinner : ∀ a : ℝ^(N + 1), ∫ τ, ⟪a, τ⟫ ∂G = ⟪a, b⟫ := fun a => integral_inner hid a
  have hmean : ∫ q, ((N : ℝ) + 1)⁻¹ * ⟪q.1, q.2⟫ ∂(G.prod G) = ((N : ℝ) + 1)⁻¹ * ⟪b, b⟫ := by
    rw [integral_const_mul]
    exact congrArg _ (integral_prod_bilin (innerSL ℝ) hid hid)
  set C : ℝ := 8 * k * (K₉ * B) / (((N : ℝ) + 1) ^ 2 * κ) with hC
  have hC0 : 0 ≤ C := by have := mul_nonneg hK₉ hB0; positivity
  have hMau : ∀ a : ℝ^(N + 1),
      Integrable (fun τ => (((N : ℝ) + 1)⁻¹ * ⟪a, τ⟫ - ((N : ℝ) + 1)⁻¹ * ⟪a, b⟫) ^ (2 * k)) G ∧
        ∫ τ, (((N : ℝ) + 1)⁻¹ * ⟪a, τ⟫ - ((N : ℝ) + 1)⁻¹ * ⟪a, b⟫) ^ (2 * k) ∂G ≤
          4 * (8 * k / (((N : ℝ) + 1) ^ 2 * κ)) ^ k * ‖a‖ ^ (2 * k) := fun a => by
    have hlip : ∀ x z : ℝ^(N + 1),
        |((N : ℝ) + 1)⁻¹ * ⟪a, x⟫ - ((N : ℝ) + 1)⁻¹ * ⟪a, z⟫| ≤
          ‖a‖ / ((N : ℝ) + 1) * ‖x - z‖ := fun x z => by
      rw [← mul_sub, ← inner_sub_right, abs_mul, abs_of_pos (inv_pos.2 hN0), div_eq_inv_mul,
        mul_assoc]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (inv_pos.2 hN0).le
    have key := integral_sub_integral_pow_shcherbinaTirozziCavityGibbs_le (h := h) (y := y)
      hκ0 hrr ht1 hu hu0 g g₀ (f := fun τ => ((N : ℝ) + 1)⁻¹ * ⟪a, τ⟫)
      (by positivity : 0 ≤ ‖a‖ / ((N : ℝ) + 1)) hlip k
    rw [← hG] at key
    simp only [integral_const_mul, hinner] at key
    refine ⟨key.1, key.2.trans_eq ?_⟩
    rw [pow_mul ‖a‖, mul_assoc (4 : ℝ), ← mul_pow]
    congr 2; field_simp
  set X : ℝ^(N + 1) × ℝ^(N + 1) → ℝ :=
    fun p => ((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ - ((N : ℝ) + 1)⁻¹ * ⟪p.1, b⟫ with hX
  set Y : ℝ^(N + 1) → ℝ :=
    fun σ => ((N : ℝ) + 1)⁻¹ * ⟪b, σ⟫ - ((N : ℝ) + 1)⁻¹ * ⟪b, b⟫ with hY
  have hXm : Measurable X := by fun_prop
  have hYm : Measurable Y := by fun_prop
  have heven : Even (2 * k) := even_two_mul k
  set c : ℝ := 4 * (8 * k / (((N : ℝ) + 1) ^ 2 * κ)) ^ k with hc
  have hc0 : 0 ≤ c := by positivity
  have hcC : c * (K₉ * B) ^ k = 4 * C ^ k := by
    rw [hc, hC, mul_assoc, ← mul_pow]; congr 2; ring
  have hXsec : Integrable (fun σ => ∫ τ, ‖X (σ, τ) ^ (2 * k)‖ ∂G) G := by
    refine Integrable.mono' ((hmom k hk4).1.const_mul c)
      (((hXm.pow_const _).norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable)
      (ae_of_all _ fun σ => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp_rw [Real.norm_of_nonneg (heven.pow_nonneg _)]
    exact (hMau σ).2
  have hXi : Integrable (fun p => X p ^ (2 * k)) (G.prod G) :=
    (integrable_prod_iff (hXm.pow_const _).aestronglyMeasurable).2
      ⟨ae_of_all _ fun σ => (hMau σ).1, hXsec⟩
  have hXI : ∫ p, X p ^ (2 * k) ∂(G.prod G) ≤ 4 * C ^ k := by
    rw [integral_prod _ hXi]
    refine (integral_mono hXi.integral_prod_left ((hmom k hk4).1.const_mul c)
      fun σ => (hMau σ).2).trans ?_
    rw [integral_const_mul, ← hcC]
    exact mul_le_mul_of_nonneg_left (hmom k hk4).2 hc0
  have hbk : ‖b‖ ^ (2 * k) ≤ (K₉ * B) ^ k := by
    have h1 : ‖b‖ ≤ ∫ σ, ‖σ‖ ∂G := norm_integral_le_integral_norm _
    have h2 : (∫ σ, ‖σ‖ ∂G) ^ (2 * k) ≤ ∫ σ, ‖σ‖ ^ (2 * k) ∂G :=
      ConvexOn.map_integral_le (heven.convexOn_pow (𝕜 := ℝ)) (continuous_pow _).continuousOn
        isClosed_univ (ae_of_all _ fun _ => Set.mem_univ _) hnorm (hmom k hk4).1
    exact ((pow_le_pow_left₀ (norm_nonneg _) h1 _).trans h2).trans (hmom k hk4).2
  have hYi : Integrable (fun p : ℝ^(N + 1) × ℝ^(N + 1) =>
      Y p.1 ^ (2 * k)) (G.prod G) := (hMau b).1.comp_fst G
  have hYI : ∫ p : ℝ^(N + 1) × ℝ^(N + 1), Y p.1 ^ (2 * k) ∂(G.prod G) ≤ 4 * C ^ k := by
    rw [integral_fun_fst (fun σ => Y σ ^ (2 * k)), probReal_univ, one_smul]
    refine (hMau b).2.trans ?_
    rw [← hcC]
    exact mul_le_mul_of_nonneg_left hbk hc0
  have hsum := integral_add_pow_two_mul_le (μ := G.prod G) (X := X) (Y := fun p => Y p.1)
    hXm.aestronglyMeasurable (hYm.comp measurable_fst).aestronglyMeasurable hXi hYi
  have e : (fun p : ℝ^(N + 1) × ℝ^(N + 1) =>
      (((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ -
        ∫ q, ((N : ℝ) + 1)⁻¹ * ⟪q.1, q.2⟫ ∂(G.prod G)) ^ (2 * k)) =
      fun p => (X p + Y p.1) ^ (2 * k) := funext fun p => by
    rw [hmean, hX, hY]; simp only; rw [real_inner_comm p.1 b]; congr 1; ring
  rw [e]
  refine ⟨hsum.1, hsum.2.trans ?_⟩
  refine (mul_le_mul_of_nonneg_left (add_le_add hXI hYI) (by positivity)).trans ?_
  have h4 : (2 : ℝ) ^ (2 * k - 1) * 2 = 4 ^ k := by
    rw [← pow_succ, show 2 * k - 1 + 1 = 2 * k by omega, pow_mul]; norm_num
  have h16 : (2 : ℝ) ^ (2 * k - 1) * (4 * C ^ k + 4 * C ^ k) ≤ (16 * C) ^ k := by
    have h4k : (4 : ℝ) ≤ 4 ^ k := le_self_pow₀ (by norm_num) hk0
    calc (2 : ℝ) ^ (2 * k - 1) * (4 * C ^ k + 4 * C ^ k)
        = (2 ^ (2 * k - 1) * 2) * (4 * C ^ k) := by ring
      _ = 4 ^ k * (4 * C ^ k) := by rw [h4]
      _ ≤ 4 ^ k * (4 ^ k * C ^ k) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h4k (pow_nonneg hC0 _))
            (by positivity)
      _ = (16 * C) ^ k := by rw [← mul_pow, ← mul_pow]; congr 1; ring
  refine h16.trans (pow_le_pow_left₀ (by positivity) ?_ k)
  rw [hC]
  have hnum : 0 ≤ 128 * K₉ * k * B / ((N : ℝ) + 1) ^ 2 := by
    have := mul_nonneg hK₉ hB0; positivity
  calc 16 * (8 * k * (K₉ * B) / (((N : ℝ) + 1) ^ 2 * κ))
      = 128 * K₉ * k * B / ((N : ℝ) + 1) ^ 2 / κ := by field_simp; ring
    _ ≤ 128 * K₉ * k * B / ((N : ℝ) + 1) ^ 2 / κ₀ :=
        div_le_div_of_nonneg_left hnum hκ₀ hκ
    _ = 128 * K₉ / κ₀ * k * B / ((N : ℝ) + 1) ^ 2 := by ring

/-- The recombination `2^{2k-1} (4 x^k + (4 y)^k) ≤ (8 x + 16 y)^k`. -/
private theorem two_pow_mul_four_mul_pow_add_le' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {k : ℕ}
    (hk : k ≠ 0) : (2 : ℝ) ^ (2 * k - 1) * (4 * x ^ k + (4 * y) ^ k) ≤ (8 * x + 16 * y) ^ k := by
  have h8 : (2 : ℝ) ^ (2 * k - 1) * (4 * x ^ k) ≤ (8 * x) ^ k := by
    have h4 : (2 : ℝ) ^ (2 * k - 1) * 4 = 4 ^ k * 2 := by
      have : (2 : ℝ) ^ (2 * k - 1) * 2 = 4 ^ k := by
        rw [← pow_succ, show 2 * k - 1 + 1 = 2 * k by omega, pow_mul]; norm_num
      linear_combination 2 * this
    have h2 : (2 : ℝ) ≤ 2 ^ k := le_self_pow₀ (by norm_num) hk
    rw [← mul_assoc, h4, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hx _)
    calc (4 : ℝ) ^ k * 2 ≤ 4 ^ k * 2 ^ k := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 8 ^ k := by rw [← mul_pow]; norm_num
  have h16 : (2 : ℝ) ^ (2 * k - 1) * (4 * y) ^ k ≤ (16 * y) ^ k := by
    have h2 : (2 : ℝ) ^ (2 * k - 1) ≤ 4 ^ k := by
      rw [show (4 : ℝ) ^ k = 2 ^ (2 * k) by rw [pow_mul]; norm_num]
      exact pow_le_pow_right₀ one_le_two (by omega)
    refine (mul_le_mul_of_nonneg_right h2 (pow_nonneg (by linarith) _)).trans_eq ?_
    rw [← mul_pow]; congr 1; ring
  rw [mul_add]
  exact (add_le_add h8 h16).trans (pow_add_pow_le (by linarith) (by linarith) hk)

/-- **Quenched self-overlap concentration for `R_{1,1}` along the cavity path (uniform in `t`):**
for `k ≤ N + 1`, `⟨(R_{1,1} - ⟨R_{1,1}⟩_t) ^ (2 k)⟩_t ≤ (K k B_cav / (N + 1)²) ^ k`. -/
theorem exists_integral_shcherbinaTirozziCavity_selfOverlap_sub_mean_pow_le
    (κ₀ h₀ D R_diff : ℝ) (hκ₀ : 0 < κ₀) (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M k : ℕ) (κ h r rBar t y : ℝ) (u : ℝ → ℝ)
      (g : Fin M → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → rBar ≤ r → r - rBar ≤ R_diff →
      M ≤ 10 * (N + 1) → k ≤ N + 1 →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → (∀ x, -D * (1 + |x|) ≤ u x) →
      ∀ G : Measure (ℝ^(N + 1)),
        G = volume.tilted (fun σ => -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ) →
        Integrable (fun σ : ℝ^(N + 1) =>
            (((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 -
              ∫ τ, ((N : ℝ) + 1)⁻¹ * ‖τ‖ ^ 2 ∂G) ^ (2 * k)) G ∧
          ∫ σ, (((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 -
              ∫ τ, ((N : ℝ) + 1)⁻¹ * ‖τ‖ ^ 2 ∂G) ^ (2 * k) ∂G ≤
            (K * k * (((N : ℝ) + 1) +
              Real.sqrt (∑ k : Fin M, ∑ i : Fin (N + 1), g k i ^ 2) +
              (∑ i : Fin (N + 1), g₀ i ^ 2) + y ^ 2) / ((N : ℝ) + 1) ^ 2) ^ k := by
  obtain ⟨K₁, hK₁, h317⟩ :=
    exists_integral_exp_half_sq_norm_shcherbinaTirozziCavity_le_exp κ₀ h₀ D R_diff hκ₀ hR_diff
  obtain ⟨K₉, hK₉, h319⟩ :=
    exists_integral_sq_norm_pow_shcherbinaTirozziCavity_le κ₀ h₀ D R_diff hκ₀ hR_diff
  refine ⟨512 * (K₁ + 2) / κ₀ ^ 2 + 16 * K₉ ^ 2, by positivity,
    fun N M k κ h r rBar t y u g g₀ hκ hh ht0 ht1 hrr hrr_diff hM hk hu hu0 hD G hG => ?_⟩
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum := hu.measurable_of_univ
  have : IsProbabilityMeasure G := by
    rw [hG]; exact isProbabilityMeasure_shcherbinaTirozziCavityGibbs (h := h) (y := y) hκ0 hrr ht1
      hum hu0 g g₀
  set B : ℝ := ((N : ℝ) + 1) + Real.sqrt (∑ k : Fin M, ∑ i : Fin (N + 1), g k i ^ 2) +
    (∑ i : Fin (N + 1), g₀ i ^ 2) + y ^ 2 with hB
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hBN : ((N : ℝ) + 1) ≤ B := by
    have h2 : 0 ≤ ∑ i : Fin (N + 1), g₀ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [hB]; linarith [Real.sqrt_nonneg (∑ k : Fin M, ∑ i : Fin (N + 1), g k i ^ 2), sq_nonneg y]
  have hB0 : 0 < B := hN0.trans_le hBN
  have heven : Even (2 * k) := even_two_mul k
  have hmom : ∀ j, j ≤ 4 * (N + 1) → Integrable (fun σ : ℝ^(N + 1) => ‖σ‖ ^ (2 * j)) G ∧
      ∫ σ, ‖σ‖ ^ (2 * j) ∂G ≤ (K₉ * B) ^ j := fun j hj => by
    rw [hG]
    exact h319 N M j κ h r rBar t y u g g₀ hκ hh ht0 ht1 hrr hrr_diff hM hj hum hu0 hD
  set a : ℝ := Real.sqrt (2 * (K₁ + 2) * B / κ) with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 2 * (K₁ + 2) * B / κ := by
    rw [ha, Real.sq_sqrt (div_nonneg (mul_nonneg (by linarith) hB0.le) hκ0.le)]
  set f : ℝ^(N + 1) → ℝ := fun σ => ((N : ℝ) + 1)⁻¹ * min ‖σ‖ a ^ 2 with hf
  set φ : ℝ^(N + 1) → ℝ := fun σ => ((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 - f σ with hφ
  have hfm : Measurable f := by fun_prop
  have hφm : Measurable φ := by fun_prop
  have hlip : ∀ x z : ℝ^(N + 1), |f x - f z| ≤ 2 * a / ((N : ℝ) + 1) * ‖x - z‖ := fun x z => by
    rw [hf]
    simp only [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hN0), div_eq_inv_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left ((abs_min_norm_sq_sub_le ha0 x z).trans_eq (mul_assoc _ _ _))
      (inv_pos.2 hN0).le
  have hfMau := integral_sub_integral_pow_shcherbinaTirozziCavityGibbs_le (h := h) (y := y)
    hκ0 hrr ht1 hu hu0 g g₀ (by positivity : 0 ≤ 2 * a / ((N : ℝ) + 1)) hlip k
  rw [← hG] at hfMau
  have hfb : ∀ σ, |f σ| ≤ ((N : ℝ) + 1)⁻¹ * a ^ 2 := fun σ => by
    have h1 : 0 ≤ min ‖σ‖ a := le_min (norm_nonneg _) ha0
    rw [hf, abs_of_nonneg (mul_nonneg (inv_pos.2 hN0).le (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1 (min_le_right _ _) 2)
      (inv_pos.2 hN0).le
  have hfi : Integrable f G := Integrable.of_bound hfm.aestronglyMeasurable _
    (ae_of_all _ fun σ => by simpa only [Real.norm_eq_abs] using hfb σ)
  have hsq : Integrable (fun σ : ℝ^(N + 1) => ((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2) G :=
    (by simpa using (hmom 1 (by omega)).1 : Integrable
      (fun σ : ℝ^(N + 1) => ‖σ‖ ^ 2) G).const_mul _
  have hφi : Integrable φ G := hsq.sub hfi
  set S : Set (ℝ^(N + 1)) := {σ | a ≤ ‖σ‖} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const measurable_norm
  have hGS : G.real S ≤ Real.exp (-(2 * B)) := by
    obtain ⟨hexp, hbound⟩ := h317 N M κ h r rBar t y u g g₀ hκ hh ht0 ht1 hrr hrr_diff hM hum
      hu0 hD
    rw [← hG] at hexp hbound
    have h1 : Real.exp (κ / 2 * a ^ 2) * G.real S ≤ Real.exp (K₁ * B) := by
      refine le_trans ?_ hbound
      have h2 := mul_meas_ge_le_integral_of_nonneg
        (μ := G) (f := fun σ : ℝ^(N + 1) => Real.exp (κ / 2 * ‖σ‖ ^ 2))
        (ae_of_all _ fun _ => (Real.exp_pos _).le) hexp (Real.exp (κ / 2 * a ^ 2))
      refine le_trans (mul_le_mul_of_nonneg_left (measureReal_mono ?_ (measure_ne_top G _))
        (Real.exp_pos _).le) h2
      intro σ (hσ : a ≤ ‖σ‖)
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha0 hσ 2)
        (by positivity))
    have h3 : κ / 2 * a ^ 2 = (K₁ + 2) * B := by rw [ha2]; field_simp
    rw [h3] at h1
    refine le_of_mul_le_mul_left (h1.trans_eq ?_) (Real.exp_pos ((K₁ + 2) * B))
    rw [← Real.exp_add]; congr 1; ring
  set Q : ℝ^(N + 1) → ℝ := fun σ => ((N : ℝ) + 1)⁻¹ ^ (2 * k) * ‖σ‖ ^ (2 * (2 * k)) with hQ
  have hφpt : ∀ σ, φ σ ^ (2 * k) ≤ S.indicator Q σ := fun σ => by
    by_cases hσ : a ≤ ‖σ‖
    · rw [Set.indicator_of_mem (show σ ∈ S from hσ)]
      simp only [hQ]
      rw [pow_mul ‖σ‖, ← mul_pow]
      have h0 : 0 ≤ φ σ := by
        have : min ‖σ‖ a ^ 2 ≤ ‖σ‖ ^ 2 :=
          pow_le_pow_left₀ (le_min (norm_nonneg _) ha0) (min_le_left _ _) 2
        simp only [hφ, hf]
        exact sub_nonneg.2 (mul_le_mul_of_nonneg_left this (inv_pos.2 hN0).le)
      refine pow_le_pow_left₀ h0 ?_ _
      simp only [hφ, hf]
      exact sub_le_self _ (mul_nonneg (inv_pos.2 hN0).le (sq_nonneg _))
    · have h0 : φ σ = 0 := by
        simp only [hφ, hf, min_eq_left (le_of_not_ge hσ), sub_self]
      rw [h0, zero_pow (by omega), Set.indicator_of_notMem (show σ ∉ S from hσ)]
  have h4k' : 4 * k ≤ 4 * (N + 1) := by omega
  have eQ : ∀ σ, Q σ ^ 2 = (((N : ℝ) + 1)⁻¹ ^ (2 * k)) ^ 2 * ‖σ‖ ^ (2 * (4 * k)) := fun σ => by
    simp only [hQ]; rw [mul_pow, ← pow_mul ‖σ‖]; congr 2; ring
  have hQL : MemLp Q 2 G := by
    refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
    simp_rw [eQ]; exact (hmom _ h4k').1.const_mul _
  have hQi : Integrable (S.indicator Q) G := (hQL.integrable one_le_two).indicator hSm
  have hφki : Integrable (fun σ => φ σ ^ (2 * k)) G :=
    Integrable.mono' hQi (hφm.pow_const _).aestronglyMeasurable (ae_of_all _ fun σ => by
      rw [Real.norm_of_nonneg (heven.pow_nonneg _)]; exact hφpt σ)
  set T : ℝ := (K₉ * B / ((N : ℝ) + 1)) ^ (2 * k) with hT
  have hKB : 0 ≤ K₉ * B := mul_nonneg hK₉ hB0.le
  have hQ2 : ∫ σ, Q σ ^ 2 ∂G ≤ T ^ 2 := by
    simp_rw [eQ]; rw [integral_const_mul]
    refine (mul_le_mul_of_nonneg_left (hmom _ h4k').2 (by positivity)).trans_eq ?_
    rw [hT, div_eq_inv_mul]; ring_nf
  have hφI : ∫ σ, φ σ ^ (2 * k) ∂G ≤ Real.exp (-B) * T := by
    refine (integral_mono hφki hQi hφpt).trans ?_
    rw [integral_indicator hSm]
    refine (Real.le_norm_self _).trans (norm_setIntegral_le_mul_of_integral_sq_le hSm
      (measure_ne_top _ _) hQL (Real.exp_pos _).le (pow_nonneg (div_nonneg hKB hN0.le) _)
      (hGS.trans_eq ?_) (by simpa only [Real.norm_eq_abs, sq_abs] using hQ2))
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hφsym := integral_sub_integral_pow_two_mul_le (μ := G) (f := φ) (m := 0) (k := k)
    hφm.aestronglyMeasurable (by simpa only [sub_zero] using hφki)
  simp only [sub_zero] at hφsym
  have hsum := integral_add_pow_two_mul_le (μ := G) (X := fun σ => f σ - ∫ τ, f τ ∂G)
    (Y := fun σ => φ σ - ∫ τ, φ τ ∂G) (hfm.sub_const _).aestronglyMeasurable
    (hφm.sub_const _).aestronglyMeasurable hfMau.1 hφsym.1
  have e : (fun σ : ℝ^(N + 1) =>
      (((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 - ∫ τ, ((N : ℝ) + 1)⁻¹ * ‖τ‖ ^ 2 ∂G) ^ (2 * k)) =
      fun σ => ((f σ - ∫ τ, f τ ∂G) + (φ σ - ∫ τ, φ τ ∂G)) ^ (2 * k) := funext fun σ => by
    have : ∫ τ, φ τ ∂G = (∫ τ, ((N : ℝ) + 1)⁻¹ * ‖τ‖ ^ 2 ∂G) - ∫ τ, f τ ∂G := integral_sub hsq hfi
    rw [this, hφ]; congr 1; ring
  rw [e]
  refine ⟨hsum.1, hsum.2.trans ?_⟩
  set x : ℝ := 64 * (K₁ + 2) * k * B / (((N : ℝ) + 1) ^ 2 * κ ^ 2) with hx
  set y' : ℝ := K₉ ^ 2 * k * B / ((N : ℝ) + 1) ^ 2 with hy'
  have hK2 : 0 ≤ K₁ + 2 := by linarith
  have hx0 : 0 ≤ x := by
    rw [hx]
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK2)
      (Nat.cast_nonneg k)) hB0.le) (by positivity)
  have hy0 : 0 ≤ y' := by have := hB0.le; positivity
  have hX : ∫ σ, (f σ - ∫ τ, f τ ∂G) ^ (2 * k) ∂G ≤ 4 * x ^ k := by
    refine hfMau.2.trans_eq ?_
    congr 2; rw [hx, div_pow, mul_pow, ha2]; field_simp; ring
  have hY : ∫ σ, (φ σ - ∫ τ, φ τ ∂G) ^ (2 * k) ∂G ≤ (4 * y') ^ k := by
    refine hφsym.2.trans ?_
    have h1 : Real.exp (-B) * T ≤ y' ^ k := by
      refine (mul_le_mul_of_nonneg_right (Real.exp_neg_le_natCast_div_pow hB0 k)
        (pow_nonneg (div_nonneg hKB hN0.le) _)).trans_eq ?_
      rw [pow_mul, ← mul_pow, hy']; congr 1; field_simp
    refine (mul_le_mul_of_nonneg_left (hφI.trans h1) (by positivity)).trans_eq ?_
    rw [pow_mul, ← mul_pow]; norm_num
  calc (2 : ℝ) ^ (2 * k - 1) * ((∫ σ, (f σ - ∫ τ, f τ ∂G) ^ (2 * k) ∂G) +
        ∫ σ, (φ σ - ∫ τ, φ τ ∂G) ^ (2 * k) ∂G)
      ≤ 2 ^ (2 * k - 1) * (4 * x ^ k + (4 * y') ^ k) :=
        mul_le_mul_of_nonneg_left (add_le_add hX hY) (by positivity)
    _ ≤ (8 * x + 16 * y') ^ k := two_pow_mul_four_mul_pow_add_le' hx0 hy0 hk0
    _ ≤ ((512 * (K₁ + 2) / κ₀ ^ 2 + 16 * K₉ ^ 2) * k * B / ((N : ℝ) + 1) ^ 2) ^ k := by
        refine pow_le_pow_left₀ (by linarith) ?_ k
        have e1 : (512 * (K₁ + 2) / κ₀ ^ 2 + 16 * K₉ ^ 2) * k * B / ((N : ℝ) + 1) ^ 2 =
            512 * (K₁ + 2) * k * B / ((N : ℝ) + 1) ^ 2 / κ₀ ^ 2 + 16 * y' := by
          rw [hy']; ring
        have e2 : 8 * x = 512 * (K₁ + 2) * k * B / ((N : ℝ) + 1) ^ 2 / κ ^ 2 := by
          rw [hx]; field_simp; ring
        rw [e1, e2]
        have h0 : 0 ≤ 512 * (K₁ + 2) * k * B / ((N : ℝ) + 1) ^ 2 :=
          div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK2)
            (Nat.cast_nonneg k)) hB0.le) (by positivity)
        exact add_le_add (div_le_div_of_nonneg_left h0 (pow_pos hκ₀ 2)
          (pow_le_pow_left₀ hκ₀.le hκ 2)) le_rfl

end QuenchedConcentration

end SpinGlasses
