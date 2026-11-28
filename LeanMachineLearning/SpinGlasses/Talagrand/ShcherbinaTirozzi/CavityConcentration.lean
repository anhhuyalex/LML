/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.CavityDisorderConcentration

/-!
# The Shcherbina--Tirozzi model: uniform-in-`t` overlap concentration along `ν_t` (Eq. (3.111))

This file proves **Talagrand, Eq. (3.111)** (uniform-in-`t` Theorem 3.1.18) along the cavity path
`H_{N,M,t}` on `ℝ^(N+1)` with `M ≤ 10 (N + 1)`: for `4 k ≤ N + 1`,
```
ν_t ((R_{1,1} - ρ_t) ^ (2 k)) ≤ (K k / (N + 1)) ^ k,
ν_t ((R_{1,2} - q_t) ^ (2 k)) ≤ (K k / (N + 1)) ^ k,
```
where `ρ_t = ν_t(R_{1,1})`, `q_t = ν_t(R_{1,2})`, and `K` depends only on
`κ₀, h₀, D, R, R_diff` (uniformly in `N, M, k, t, r, rBar`).

The proof follows `DisorderConcentration.lean` for the extended Gaussian disorder
`(z, g, g₀)` with `y = √r * z` (`z ~ 𝒩(0, 1)`), using the quenched bounds from
`CavityOverlapConcentration.lean` and the disorder gradient bounds from
`CavityDisorderConcentration.lean`.

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

local notation "stdDisLaw[" N ", " M "]" =>
  Measure.prod (gaussianReal 0 1)
    (Measure.prod
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
      (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))

local notation "B_std[" N ", " M "]" d:arg =>
  ((N : ℝ) + 1) + Real.sqrt (∑ k : Fin M, ∑ i : Fin (N + 1), d.2.1 k i ^ 2) +
    (∑ i : Fin (N + 1), d.2.2 i ^ 2) + d.1 ^ 2

/-- The standard Gaussian vector on `(Fin M × Fin (N+1)) ⊕ Fin (N+1) ⊕ Unit` pushes forward to
`stdDisLaw[N, M]`. -/
private theorem measurePreserving_stdGaussian_cavityDisorder (N M : ℕ) :
    MeasurePreserving
      (fun ω : EuclideanSpace ℝ (Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1))) =>
        ((ω (Sum.inl ()),
          (fun k i => ω (Sum.inr (Sum.inl (k, i))),
           fun i => ω (Sum.inr (Sum.inr i)))) : Dis[N, M]))
      (stdGaussian (EuclideanSpace ℝ (Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1)))))
      stdDisLaw[N, M] := by
  have h1 : MeasurePreserving
      (fun ω : EuclideanSpace ℝ (Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1))) => ω.ofLp)
      (stdGaussian (EuclideanSpace ℝ (Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1)))))
      (Measure.pi fun _ : Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1)) => gaussianReal 0 1) :=
    ⟨WithLp.measurable_ofLp 2 _, pi_gaussianReal_eq_map_stdGaussian.symm⟩
  have h2 := measurePreserving_sumPiEquivProdPi
    (X := fun _ : Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1)) => ℝ) fun _ => gaussianReal 0 1
  have hunit : MeasurePreserving (fun f : Unit → ℝ => f ())
      (Measure.pi fun _ : Unit => gaussianReal 0 1) (gaussianReal 0 1) :=
    measurePreserving_eval (fun _ : Unit => gaussianReal 0 1) ()
  have hrest1 := measurePreserving_sumPiEquivProdPi
    (X := fun _ : (Fin M × Fin (N + 1)) ⊕ Fin (N + 1) => ℝ) fun _ => gaussianReal 0 1
  have hrest2 := (measurePreserving_curry_symm (X := ℝ)
    (fun (_ : Fin M) (_ : Fin (N + 1)) => gaussianReal 0 1)).symm
    (MeasurableEquiv.curry (Fin M) (Fin (N + 1)) ℝ).symm
  have hrest := (hrest2.prod (MeasurePreserving.id
    (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))).comp hrest1
  exact (hunit.prod hrest).comp (h2.comp h1)

/-- Scaling the first coordinate by `√r` turns `stdDisLaw[N, M]` into `cavLaw[N, M, r]`. -/
private theorem measurePreserving_scale_y (N M : ℕ) (r : ℝ≥0) :
    MeasurePreserving (fun d : Dis[N, M] => (Real.sqrt (r : ℝ) * d.1, d.2))
      stdDisLaw[N, M] cavLaw[N, M, r] := by
  have h1 : MeasurePreserving (fun z : ℝ => Real.sqrt (r : ℝ) * z)
      (gaussianReal 0 1) (gaussianReal 0 r) := by
    refine ⟨measurable_const.mul measurable_id, ?_⟩
    rw [gaussianReal_map_const_mul]
    simp [Real.sq_sqrt r.coe_nonneg]
  exact h1.prod (MeasurePreserving.id _)

/-- Exponential moment of `B_std / 4` under `stdDisLaw[N, M]`:
`𝔼 exp (B_std / 4) ≤ exp (5 (N + 1))`. -/
private theorem integral_exp_cavity_radius_div_four_le {N M : ℕ} (hM : M ≤ 10 * (N + 1)) :
    Integrable (fun d : Dis[N, M] => Real.exp (B_std[N, M] d / 4)) stdDisLaw[N, M] ∧
      ∫ d : Dis[N, M], Real.exp (B_std[N, M] d / 4) ∂stdDisLaw[N, M] ≤
        Real.exp (5 * ((N : ℝ) + 1)) := by
  have hB0 := integral_exp_shcherbinaTirozzi_radius_div_four_le (N := N + 1) (M := M) hM
  have hy : Integrable (fun z : ℝ => Real.exp (z ^ 2 / 4)) (gaussianReal 0 1) := by
    have h := integrable_exp_mul_sq_gaussianReal (l := 1 / 4) (by norm_num)
    exact h.congr (ae_of_all _ fun z => congrArg Real.exp (by ring))
  have hy_val : ∫ z : ℝ, Real.exp (z ^ 2 / 4) ∂(gaussianReal 0 1) ≤ Real.exp 1 := by
    have heq : (fun z : ℝ => Real.exp (z ^ 2 / 4)) = fun z => Real.exp ((1 / 4 : ℝ) * z ^ 2) :=
      funext fun z => by ring
    rw [heq, integral_exp_mul_sq_gaussianReal (l := 1 / 4) (by norm_num)]
    have h1 : (Real.sqrt (1 - 2 * (1 / 4 : ℝ)))⁻¹ = Real.sqrt 2 := by
      rw [show (1 - 2 * (1 / 4 : ℝ)) = 2⁻¹ by norm_num, Real.sqrt_inv, inv_inv]
    rw [h1]
    have h2 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
    linarith [Real.add_one_le_exp (1 : ℝ)]
  let f₁ : ℝ → ℝ := fun z => Real.exp (z ^ 2 / 4)
  let f₂ : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) → ℝ := fun p =>
    Real.exp ((((N + 1 : ℕ) : ℝ) + Real.sqrt (∑ k, ∑ i, p.1 k i ^ 2) +
      ∑ i, p.2 i ^ 2) / 4)
  have hsplit : ∀ d : Dis[N, M], Real.exp (B_std[N, M] d / 4) = f₁ d.1 * f₂ d.2 := fun d => by
    dsimp only [f₁, f₂]
    rw [← Real.exp_add]; congr 1; push_cast; ring
  simp_rw [hsplit]
  refine ⟨hy.mul_prod hB0.1, ?_⟩
  rw [integral_prod_mul f₁ f₂]
  have h1 : (∫ z : ℝ, f₁ z ∂(gaussianReal 0 1)) *
      ∫ p, f₂ p ∂((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) =>
          gaussianReal 0 1).prod (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)) ≤
      Real.exp 1 * Real.exp (4 * ((N + 1 : ℕ) : ℝ)) :=
    mul_le_mul hy_val hB0.2 (integral_nonneg fun _ => (Real.exp_pos _).le) (Real.exp_pos _).le
  refine h1.trans ?_
  rw [← Real.exp_add, Real.exp_le_exp]
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) N]

/-- `k`-th moment of `B_std` under `stdDisLaw[N, M]`: for `k ≤ N + 1`,
`𝔼 (B_std ^ k) ≤ (48 (N + 1)) ^ k`. -/
private theorem integral_cavity_radius_pow_le {N M k : ℕ} (hM : M ≤ 10 * (N + 1))
    (hk : k ≤ N + 1) :
    Integrable (fun d : Dis[N, M] => B_std[N, M] d ^ k) stdDisLaw[N, M] ∧
      ∫ d : Dis[N, M], B_std[N, M] d ^ k ∂stdDisLaw[N, M] ≤ (48 * ((N : ℝ) + 1)) ^ k := by
  have hexp := integral_exp_cavity_radius_div_four_le hM
  have h0 : 0 ≤ᵐ[stdDisLaw[N, M]] fun d : Dis[N, M] => B_std[N, M] d / 4 :=
    ae_of_all _ fun d => div_nonneg (add_nonneg (add_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (sq_nonneg d.1)) (by norm_num)
  have hmom := integral_pow_le_of_integral_exp_le h0 hexp.1 hexp.2 k
  have hpow : ∀ d : Dis[N, M], B_std[N, M] d ^ k = (4 : ℝ) ^ k * (B_std[N, M] d / 4) ^ k :=
    fun d => by rw [← mul_pow]; congr 1; ring
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  simp_rw [hpow]
  refine ⟨hmom.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  refine (mul_le_mul_of_nonneg_left hmom.2 (by positivity)).trans ?_
  have h1 : (k : ℝ) ^ k ≤ ((N : ℝ) + 1) ^ k :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hk) k
  have h2 : ((N : ℝ) + 1) ^ k + (5 * ((N : ℝ) + 1)) ^ k ≤ (6 * ((N : ℝ) + 1)) ^ k := by
    have := pow_add_pow_le (show (0 : ℝ) ≤ (N : ℝ) + 1 by positivity)
      (show (0 : ℝ) ≤ 5 * ((N : ℝ) + 1) by positivity) hk0
    exact this.trans_eq (by congr 1; ring)
  have h3 : (2 : ℝ) ^ k * ((k : ℝ) ^ k + (5 * ((N : ℝ) + 1)) ^ k) ≤
      (2 : ℝ) ^ k * (6 * ((N : ℝ) + 1)) ^ k :=
    mul_le_mul_of_nonneg_left ((add_le_add h1 le_rfl).trans h2) (by positivity)
  refine (mul_le_mul_of_nonneg_left h3 (by positivity)).trans_eq ?_
  rw [← mul_pow, ← mul_pow]
  congr 1; ring

/-- The good set of the extended disorder `(z, g, g₀)`, where `B_std ≤ 768 (N + 1)` and
`‖Matrix.of g‖ ≤ √(768 (N + 1))`, is convex, measurable, of positive Gaussian mass, and carries
all but `3 e^{-2(N + 1)}` of the mass. -/
private theorem goodCavityDisorderSet_props {N M : ℕ} (hM : M ≤ 10 * (N + 1))
    (C : Set (EuclideanSpace ℝ (Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1)))))
    (hC : C = {ω | ((N : ℝ) + 1) + Real.sqrt (∑ k, ∑ i, ω (Sum.inr (Sum.inl (k, i))) ^ 2) +
          (∑ i, ω (Sum.inr (Sum.inr i)) ^ 2) + ω (Sum.inl ()) ^ 2 ≤ 768 * ((N : ℝ) + 1) ∧
        ‖Matrix.of fun k i => ω (Sum.inr (Sum.inl (k, i)))‖ ≤
          Real.sqrt (768 * ((N : ℝ) + 1))}) :
    Convex ℝ C ∧ MeasurableSet C ∧
      (stdGaussian (EuclideanSpace ℝ (Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1))))).real Cᶜ ≤
        3 * Real.exp (-(2 * ((N : ℝ) + 1))) ∧
      0 < (stdGaussian
        (EuclideanSpace ℝ (Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1))))).real C := by
  set L : ℝ := 768 with hL
  set T : EuclideanSpace ℝ (Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1))) → Dis[N, M] :=
    fun ω => (ω (Sum.inl ()),
      (fun k i => ω (Sum.inr (Sum.inl (k, i))), fun i => ω (Sum.inr (Sum.inr i)))) with hT
  have hmp : MeasurePreserving T
      (stdGaussian (EuclideanSpace ℝ (Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1)))))
      stdDisLaw[N, M] := measurePreserving_stdGaussian_cavityDisorder N M
  set γ := stdGaussian (EuclideanSpace ℝ (Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1)))) with hγ
  have hBm : Measurable fun d : Dis[N, M] => B_std[N, M] d := by fun_prop
  subst hC
  set C : Set (EuclideanSpace ℝ (Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1)))) :=
    {ω | B_std[N, M] (T ω) ≤ L * ((N : ℝ) + 1) ∧
      ‖Matrix.of (T ω).2.1‖ ≤ Real.sqrt (L * ((N : ℝ) + 1))} with hC
  have hnc : Continuous fun ω :
      EuclideanSpace ℝ (Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1))) =>
      ‖Matrix.of (T ω).2.1‖ := by
    have h1 : Continuous fun ω :
        EuclideanSpace ℝ (Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1))) =>
        (Matrix.of (T ω).2.1 : Matrix (Fin M) (Fin (N + 1)) ℝ) :=
      continuous_matrix fun k i =>
        PiLp.continuous_apply 2 _ (Sum.inr (Sum.inl (k, i)))
    exact continuous_norm.comp h1
  have hCm : MeasurableSet C :=
    (measurableSet_le (hBm.comp hmp.measurable) measurable_const).inter
      (measurableSet_le hnc.measurable measurable_const)
  have hCconv : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    refine ⟨?_, ?_⟩
    · have hflat : ∀ ω : EuclideanSpace ℝ (Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1))),
          Real.sqrt (∑ k, ∑ i, (T ω).2.1 k i ^ 2) =
            ‖(WithLp.toLp 2 fun p : Fin M × Fin (N + 1) => (T ω).2.1 p.1 p.2)‖ := fun ω => by
        rw [EuclideanSpace.norm_eq, Fintype.sum_prod_type]
        simp only [Real.norm_eq_abs, sq_abs]
      have h1 : Real.sqrt (∑ k, ∑ i, (T (a • x + b • y)).2.1 k i ^ 2) ≤
          a * Real.sqrt (∑ k, ∑ i, (T x).2.1 k i ^ 2) +
            b * Real.sqrt (∑ k, ∑ i, (T y).2.1 k i ^ 2) := by
        rw [hflat, hflat, hflat]
        have e : (WithLp.toLp 2 fun p : Fin M × Fin (N + 1) => (T (a • x + b • y)).2.1 p.1 p.2) =
            a • (WithLp.toLp 2 fun p : Fin M × Fin (N + 1) => (T x).2.1 p.1 p.2) +
              b • (WithLp.toLp 2 fun p : Fin M × Fin (N + 1) => (T y).2.1 p.1 p.2) := rfl
        rw [e]
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      have h2 : ∑ i, (T (a • x + b • y)).2.2 i ^ 2 ≤
          a * (∑ i, (T x).2.2 i ^ 2) + b * ∑ i, (T y).2.2 i ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        have h := (even_two.convexOn_pow (𝕜 := ℝ)).2 (Set.mem_univ ((T x).2.2 i))
          (Set.mem_univ ((T y).2.2 i)) ha hb hab
        change (a * (T x).2.2 i + b * (T y).2.2 i) ^ 2 ≤
          a * (T x).2.2 i ^ 2 + b * (T y).2.2 i ^ 2
        simpa only [smul_eq_mul] using h
      have h2' : (T (a • x + b • y)).1 ^ 2 ≤ a * (T x).1 ^ 2 + b * (T y).1 ^ 2 := by
        have h := (even_two.convexOn_pow (𝕜 := ℝ)).2 (Set.mem_univ ((T x).1))
          (Set.mem_univ ((T y).1)) ha hb hab
        change (a * (T x).1 + b * (T y).1) ^ 2 ≤ a * (T x).1 ^ 2 + b * (T y).1 ^ 2
        simpa only [smul_eq_mul] using h
      have hx1 := hx.1
      have hy1 := hy.1
      have h3 := mul_le_mul_of_nonneg_left hx1 ha
      have h4 := mul_le_mul_of_nonneg_left hy1 hb
      have h5 : a * (L * ((N : ℝ) + 1)) + b * (L * ((N : ℝ) + 1)) = L * ((N : ℝ) + 1) := by
        rw [← add_mul, hab, one_mul]
      have h6 : a * ((N : ℝ) + 1) + b * ((N : ℝ) + 1) = (N : ℝ) + 1 := by
        rw [← add_mul, hab, one_mul]
      linarith
    · have e : (Matrix.of (T (a • x + b • y)).2.1 : Matrix (Fin M) (Fin (N + 1)) ℝ) =
          a • Matrix.of (T x).2.1 + b • Matrix.of (T y).2.1 := rfl
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      refine (add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
        (mul_le_mul_of_nonneg_left hy.2 hb)).trans_eq ?_
      rw [← add_mul, hab, one_mul]
  have hbad : γ.real Cᶜ ≤ 3 * Real.exp (-(2 * ((N : ℝ) + 1))) := by
    set S₁ : Set Dis[N, M] := {d | L * ((N : ℝ) + 1) ≤ B_std[N, M] d} with hS₁
    set S₂ : Set (Fin M → Fin (N + 1) → ℝ) :=
      {g | Real.sqrt (L * ((N : ℝ) + 1)) < ‖Matrix.of g‖} with hS₂
    have hsub : Cᶜ ⊆ T ⁻¹' S₁ ∪ T ⁻¹' (Set.univ ×ˢ (S₂ ×ˢ Set.univ)) := fun ω hω => by
      by_contra h
      rw [Set.mem_union, not_or] at h
      refine hω ⟨le_of_lt (not_le.1 h.1),
        le_of_not_gt fun hlt => h.2 ⟨Set.mem_univ _, hlt, Set.mem_univ _⟩⟩
    have h1 : stdDisLaw[N, M].real S₁ ≤ Real.exp (-(2 * ((N : ℝ) + 1))) := by
      have hexp := integral_exp_cavity_radius_div_four_le (N := N) (M := M) hM
      have hmk := mul_meas_ge_le_integral_of_nonneg (μ := stdDisLaw[N, M])
        (f := fun d => Real.exp (B_std[N, M] d / 4)) (ae_of_all _ fun _ => (Real.exp_pos _).le)
        hexp.1 (Real.exp (L * ((N : ℝ) + 1) / 4))
      have h2 : stdDisLaw[N, M].real S₁ ≤
          stdDisLaw[N, M].real
            {d | Real.exp (L * ((N : ℝ) + 1) / 4) ≤ Real.exp (B_std[N, M] d / 4)} := by
        refine measureReal_mono (fun d (hd : L * ((N : ℝ) + 1) ≤ B_std[N, M] d) => ?_)
          (measure_ne_top _ _)
        exact Real.exp_le_exp.2 (div_le_div_of_nonneg_right hd (by norm_num))
      have h3 := (mul_le_mul_of_nonneg_left h2 (Real.exp_pos (L * ((N : ℝ) + 1) / 4)).le).trans
        (hmk.trans hexp.2)
      refine le_of_mul_le_mul_left (h3.trans ?_) (Real.exp_pos (L * ((N : ℝ) + 1) / 4))
      rw [← Real.exp_add, Real.exp_le_exp, hL]
      linarith [Nat.cast_nonneg (α := ℝ) N]
    have h2 : stdDisLaw[N, M].real (Set.univ ×ˢ (S₂ ×ˢ Set.univ)) ≤
        2 * Real.exp (-(2 * ((N : ℝ) + 1))) := by
      rw [measureReal_prod_prod, probReal_univ, one_mul, measureReal_prod_prod, probReal_univ,
        mul_one]
      refine (measureReal_l2_opNorm_gaussian_gt_le (ι := Fin (N + 1)) (κ := Fin M)
        (Real.sqrt_nonneg _)).trans ?_
      rw [Fintype.card_fin, Fintype.card_fin, Real.sq_sqrt (by rw [hL]; positivity), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ zero_le_two
      have h5 : (5 : ℝ) ^ (N + 1 + M) ≤ Real.exp (22 * ((N : ℝ) + 1)) := by
        have h25 : (5 : ℝ) ≤ Real.exp 2 := by
          have := Real.quadratic_le_exp_of_nonneg (zero_le_two : (0 : ℝ) ≤ 2)
          linarith
        refine (pow_le_pow_left₀ (by norm_num) h25 _).trans ?_
        rw [← Real.exp_nat_mul, Real.exp_le_exp]
        have hMN : (M : ℝ) ≤ 10 * ((N : ℝ) + 1) := by exact_mod_cast hM
        push_cast; linarith
      refine (mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le).trans ?_
      rw [← Real.exp_add, Real.exp_le_exp, hL]
      linarith
    have hS₁m : MeasurableSet S₁ := measurableSet_le measurable_const hBm
    have hS₂m : MeasurableSet S₂ := by
      have h1 : Continuous fun g : Fin M → Fin (N + 1) → ℝ =>
          (Matrix.of g : Matrix (Fin M) (Fin (N + 1)) ℝ) :=
        continuous_matrix fun k i => (continuous_apply i).comp (continuous_apply k)
      exact measurableSet_lt measurable_const (continuous_norm.comp h1).measurable
    have hpre : ∀ S : Set Dis[N, M], MeasurableSet S →
        γ.real (T ⁻¹' S) = stdDisLaw[N, M].real S := fun S hS => by
      rw [measureReal_def, measureReal_def, hmp.measure_preimage hS.nullMeasurableSet]
    calc γ.real Cᶜ ≤ γ.real (T ⁻¹' S₁ ∪ T ⁻¹' (Set.univ ×ˢ (S₂ ×ˢ Set.univ))) :=
          measureReal_mono hsub (measure_ne_top γ _)
      _ ≤ γ.real (T ⁻¹' S₁) + γ.real (T ⁻¹' (Set.univ ×ˢ (S₂ ×ˢ Set.univ))) :=
          measureReal_union_le _ _
      _ ≤ 3 * Real.exp (-(2 * ((N : ℝ) + 1))) := by
          rw [hpre S₁ hS₁m,
            hpre _ (MeasurableSet.univ.prod (hS₂m.prod MeasurableSet.univ))]
          linarith
  have hCpos : 0 < γ.real C := by
    have h1 : γ.real Cᶜ < 1 := by
      refine hbad.trans_lt ?_
      have h2 : Real.exp (-(2 * ((N : ℝ) + 1))) ≤ Real.exp (-2) :=
        Real.exp_le_exp.2 (by linarith [Nat.cast_nonneg (α := ℝ) N])
      have h3 : Real.exp (-2) < 1 / 3 := by
        rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
        have := Real.quadratic_le_exp_of_nonneg (zero_le_two : (0 : ℝ) ≤ 2)
        linarith
      linarith
    rw [probReal_compl_eq_one_sub hCm] at h1
    linarith
  exact ⟨hCconv, hCm, hbad, hCpos⟩

/-- Fourth-order moments around a centre for functions of the standardized cavity disorder. -/
private theorem integral_sub_pow_four_mul_le_of_cavityDisorder_growth {K₉ : ℝ} (hK₉ : 0 ≤ K₉)
    {N M k : ℕ} (hM : M ≤ 10 * (N + 1)) (hk0 : k ≠ 0) (hk : 4 * k ≤ N + 1)
    {f : Dis[N, M] → ℝ} (hf : Measurable f)
    (hgrowth : ∀ d, |f d| ≤ K₉ * B_std[N, M] d / ((N : ℝ) + 1))
    {m : ℝ} (hmb : |m| ≤ K₉ * 768) :
    Integrable (fun d : Dis[N, M] => (f d - m) ^ (4 * k)) stdDisLaw[N, M] ∧
      ∫ d : Dis[N, M], (f d - m) ^ (4 * k) ∂stdDisLaw[N, M] ≤
        ((2 * (K₉ * (48 + 768)) + 1) ^ (2 * k)) ^ 2 := by
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  set L : ℝ := 768 with hL
  set Q : ℝ := 2 * (K₉ * (48 + L)) + 1 with hQ
  have hB0 : ∀ d : Dis[N, M], 0 ≤ B_std[N, M] d := fun d =>
    add_nonneg (add_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _))
      (sq_nonneg d.1)
  have hKL : 0 ≤ K₉ * L := mul_nonneg hK₉ (by rw [hL]; norm_num)
  have hrad := integral_cavity_radius_pow_le (N := N) (M := M) hM hk
  have heven4 : Even (4 * k) := ⟨2 * k, by ring⟩
  have hpt4 : ∀ d : Dis[N, M], (f d - m) ^ (4 * k) ≤
      2 ^ (4 * k - 1) *
        ((K₉ / ((N : ℝ) + 1)) ^ (4 * k) * B_std[N, M] d ^ (4 * k) + (K₉ * L) ^ (4 * k)) := by
    intro d
    rw [← heven4.pow_abs]
    have h1 : |f d - m| ≤ K₉ / ((N : ℝ) + 1) * B_std[N, M] d + K₉ * L := by
      refine (abs_sub _ _).trans (add_le_add ((hgrowth d).trans_eq ?_) hmb)
      ring
    refine (pow_le_pow_left₀ (abs_nonneg _) h1 _).trans ?_
    rw [← mul_pow]
    exact add_pow_le (mul_nonneg (div_nonneg hK₉ hN0.le) (hB0 d)) hKL _
  have hdom4 : Integrable (fun d : Dis[N, M] => 2 ^ (4 * k - 1) *
      ((K₉ / ((N : ℝ) + 1)) ^ (4 * k) * B_std[N, M] d ^ (4 * k) + (K₉ * L) ^ (4 * k)))
      stdDisLaw[N, M] :=
    ((hrad.1.const_mul _).add (integrable_const _)).const_mul _
  have hi4 : Integrable (fun d : Dis[N, M] => (f d - m) ^ (4 * k)) stdDisLaw[N, M] :=
    Integrable.mono' hdom4 ((hf.sub_const m).pow_const _).aestronglyMeasurable
      (ae_of_all _ fun d => by
        rw [Real.norm_of_nonneg (heven4.pow_nonneg _)]
        exact hpt4 d)
  refine ⟨hi4, (integral_mono hi4 hdom4 hpt4).trans ?_⟩
  rw [integral_const_mul, integral_add (hrad.1.const_mul _) (integrable_const _),
    integral_const_mul, integral_const, probReal_univ, one_smul, ← pow_mul,
    show 2 * k * 2 = 4 * k by ring]
  have h1 : (K₉ / ((N : ℝ) + 1)) ^ (4 * k) * ∫ d, B_std[N, M] d ^ (4 * k) ∂stdDisLaw[N, M] ≤
      (48 * K₉) ^ (4 * k) := by
    refine (mul_le_mul_of_nonneg_left hrad.2 (pow_nonneg (div_nonneg hK₉ hN0.le) _)).trans_eq ?_
    rw [← mul_pow]; congr 1; field_simp
  have h2 : (48 * K₉) ^ (4 * k) + (K₉ * L) ^ (4 * k) ≤ (K₉ * (48 + L)) ^ (4 * k) := by
    refine (pow_add_pow_le (mul_nonneg (by norm_num) hK₉) hKL (by omega)).trans_eq ?_
    ring
  refine (mul_le_mul_of_nonneg_left ((add_le_add h1 le_rfl).trans h2) (by positivity)).trans ?_
  have h3 : (2 : ℝ) ^ (4 * k - 1) ≤ 2 ^ (4 * k) := pow_le_pow_right₀ one_le_two (by omega)
  refine (mul_le_mul_of_nonneg_right h3
    (pow_nonneg (mul_nonneg hK₉ (by rw [hL]; norm_num)) _)).trans ?_
  rw [← mul_pow]
  refine pow_le_pow_left₀ (mul_nonneg zero_le_two (mul_nonneg hK₉ (by rw [hL]; norm_num))) ?_ _
  rw [hQ]; linarith

/-- **Concentration of a function of the standardized cavity disorder `(z, g, g₀)`.** -/
private theorem exists_integral_sub_integral_pow_le_of_cavityDisorder_gradient (K₉ K₁₆ : ℝ)
    (hK₉ : 0 ≤ K₉) (hK₁₆ : 0 ≤ K₁₆) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M k : ℕ), M ≤ 10 * (N + 1) → 4 * k ≤ N + 1 →
      ∀ f : Dis[N, M] → ℝ, Measurable f →
      (∀ d, |f d| ≤ K₉ * B_std[N, M] d / ((N : ℝ) + 1)) →
      (∀ d Δ : Dis[N, M], ∃ f' : ℝ,
        HasDerivAt (fun s : ℝ => f (d + s • Δ)) f' 0 ∧
        f' ^ 2 ≤ K₁₆ * (B_std[N, M] d / ((N : ℝ) + 1) ^ 2 +
          B_std[N, M] d ^ 2 * ‖Matrix.of d.2.1‖ ^ 2 / ((N : ℝ) + 1) ^ 4) *
          ((∑ k, ∑ i, Δ.2.1 k i ^ 2) + (∑ i, Δ.2.2 i ^ 2) + Δ.1 ^ 2)) →
      Integrable (fun d => (f d - ∫ e, f e ∂stdDisLaw[N, M]) ^ (2 * k)) stdDisLaw[N, M] ∧
        ∫ d, (f d - ∫ e, f e ∂stdDisLaw[N, M]) ^ (2 * k) ∂stdDisLaw[N, M] ≤
          (K * k / ((N : ℝ) + 1)) ^ k := by
  set L : ℝ := 768 with hL
  set Q : ℝ := 2 * (K₉ * (48 + L)) + 1 with hQ
  have hQ1 : 1 ≤ Q := by
    have : 0 ≤ K₉ * (48 + L) := mul_nonneg hK₉ (by rw [hL]; norm_num)
    rw [hQ]; linarith
  set Kg : ℝ := K₁₆ * (L + L ^ 3) with hKg
  have hKg0 : 0 ≤ Kg := mul_nonneg hK₁₆ (by rw [hL]; norm_num)
  refine ⟨4 * (64 * Kg + 2 * Q ^ 2), by positivity,
    fun N M k hM hk f hf hgrowth hgrad => ?_⟩
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hB0 : ∀ d : Dis[N, M], 0 ≤ B_std[N, M] d := fun d =>
    add_nonneg (add_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _))
      (sq_nonneg d.1)
  set T : EuclideanSpace ℝ (Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1))) → Dis[N, M] :=
    fun ω => (ω (Sum.inl ()),
      (fun k i => ω (Sum.inr (Sum.inl (k, i))), fun i => ω (Sum.inr (Sum.inr i)))) with hT
  have hmp : MeasurePreserving T
      (stdGaussian (EuclideanSpace ℝ (Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1)))))
      stdDisLaw[N, M] := measurePreserving_stdGaussian_cavityDisorder N M
  set γ := stdGaussian (EuclideanSpace ℝ (Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1)))) with hγ
  have htrans : ∀ F : Dis[N, M] → ℝ, Measurable F →
      ∫ ω, F (T ω) ∂γ = ∫ d, F d ∂stdDisLaw[N, M] := fun F hF => by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hF.aestronglyMeasurable]
  set C : Set (EuclideanSpace ℝ (Unit ⊕ ((Fin M × Fin (N + 1)) ⊕ Fin (N + 1)))) :=
    {ω | B_std[N, M] (T ω) ≤ L * ((N : ℝ) + 1) ∧
      ‖Matrix.of (T ω).2.1‖ ≤ Real.sqrt (L * ((N : ℝ) + 1))} with hC
  obtain ⟨hCconv, hCm, hbad, hCpos⟩ : Convex ℝ C ∧ MeasurableSet C ∧
      γ.real Cᶜ ≤ 3 * Real.exp (-(2 * ((N : ℝ) + 1))) ∧ 0 < γ.real C :=
    goodCavityDisorderSet_props hM C rfl
  have hbad2 : γ.real Cᶜ ≤ (2 * Real.exp (-((N : ℝ) + 1))) ^ 2 := by
    refine hbad.trans ?_
    have e : (2 * Real.exp (-((N : ℝ) + 1))) ^ 2 = 4 * Real.exp (-(2 * ((N : ℝ) + 1))) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 1
      · norm_num
      · congr 1; push_cast; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
  set A : ℝ := Real.sqrt (Kg / ((N : ℝ) + 1)) with hA
  have hA2 : A ^ 2 = Kg / ((N : ℝ) + 1) := by rw [hA, Real.sq_sqrt (div_nonneg hKg0 hN0.le)]
  have hlip : ∀ x ∈ C, ∀ y ∈ C, |f (T x) - f (T y)| ≤ A * ‖x - y‖ := by
    intro x hx y hy
    have hδ : (∑ k, ∑ i, (T y - T x).2.1 k i ^ 2) + (∑ i, (T y - T x).2.2 i ^ 2) +
        (T y - T x).1 ^ 2 = ‖x - y‖ ^ 2 := by
      rw [norm_sub_rev, EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type,
        Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique (ι := Unit)]
      change (∑ k, ∑ i, (y (Sum.inr (Sum.inl (k, i))) - x (Sum.inr (Sum.inl (k, i)))) ^ 2) +
          (∑ i, (y (Sum.inr (Sum.inr i)) - x (Sum.inr (Sum.inr i))) ^ 2) +
          (y (Sum.inl ()) - x (Sum.inl ())) ^ 2 =
        (y (Sum.inl ()) - x (Sum.inl ())) ^ 2 +
          ((∑ k, ∑ i, (y (Sum.inr (Sum.inl (k, i))) - x (Sum.inr (Sum.inl (k, i)))) ^ 2) +
            ∑ i, (y (Sum.inr (Sum.inr i)) - x (Sum.inr (Sum.inr i))) ^ 2)
      ring
    rw [abs_sub_comm]
    refine hCconv.norm_sub_le_of_forall_hasDerivAt_line (g := fun ω => f (T ω)) hx hy
      fun z hz => ?_
    obtain ⟨d, hd, hdb⟩ := hgrad (T z) (T y - T x)
    refine ⟨d, hd, abs_le_of_sq_le_sq ?_ (by positivity)⟩
    rw [mul_pow, hA2]
    refine hdb.trans ?_
    rw [hδ]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hB1 : B_std[N, M] (T z) ≤ L * ((N : ℝ) + 1) := hz.1
    have hn1 : ‖Matrix.of (T z).2.1‖ ^ 2 ≤ L * ((N : ℝ) + 1) := by
      have h := pow_le_pow_left₀ (norm_nonneg _)
        (show ‖Matrix.of (T z).2.1‖ ≤ Real.sqrt (L * ((N : ℝ) + 1)) from hz.2) 2
      rwa [Real.sq_sqrt (by rw [hL]; positivity)] at h
    have h2 : B_std[N, M] (T z) / ((N : ℝ) + 1) ^ 2 +
        B_std[N, M] (T z) ^ 2 * ‖Matrix.of (T z).2.1‖ ^ 2 / ((N : ℝ) + 1) ^ 4 ≤
        (L + L ^ 3) / ((N : ℝ) + 1) := by
      have h3 : B_std[N, M] (T z) / ((N : ℝ) + 1) ^ 2 ≤ L / ((N : ℝ) + 1) := by
        refine (div_le_div_of_nonneg_right hB1 (by positivity)).trans_eq ?_
        field_simp
      have h4 : B_std[N, M] (T z) ^ 2 * ‖Matrix.of (T z).2.1‖ ^ 2 / ((N : ℝ) + 1) ^ 4 ≤
          L ^ 3 / ((N : ℝ) + 1) := by
        refine (div_le_div_of_nonneg_right (mul_le_mul
          (pow_le_pow_left₀ (hB0 _) hB1 2) hn1 (sq_nonneg _) (sq_nonneg _))
          (by positivity)).trans_eq ?_
        field_simp
      rw [add_div L]
      exact add_le_add h3 h4
    refine (mul_le_mul_of_nonneg_left h2 hK₁₆).trans_eq ?_
    rw [hKg]; ring
  have hfT : Measurable fun ω => f (T ω) := hf.comp hmp.measurable
  have hfC : ∀ ω ∈ C, |f (T ω)| ≤ K₉ * L := fun ω hω => by
    refine (hgrowth (T ω)).trans ?_
    rw [div_le_iff₀ hN0, mul_assoc]
    exact mul_le_mul_of_nonneg_left hω.1 hK₉
  have h4mom : ∀ m : ℝ, |m| ≤ K₉ * L →
      Integrable (fun ω => (f (T ω) - m) ^ (4 * k)) γ ∧
        ∫ ω, (f (T ω) - m) ^ (4 * k) ∂γ ≤ (Q ^ (2 * k)) ^ 2 := fun m hmb => by
    obtain ⟨hi4, hI4⟩ :=
      integral_sub_pow_four_mul_le_of_cavityDisorder_growth hK₉ hM hk0 hk hf hgrowth
        (by rw [← hL]; exact hmb)
    refine ⟨(hmp.integrable_comp ((hf.sub_const m).pow_const _).aestronglyMeasurable).2 hi4, ?_⟩
    rwa [htrans (fun d => (f d - m) ^ (4 * k)) ((hf.sub_const m).pow_const _)]
  obtain ⟨m, -, hiγ, hγle⟩ := exists_integral_stdGaussian_sub_pow_le_of_lipschitzOn hCconv hCm
    hCpos hfT (Real.sqrt_nonneg _) hlip hfC (by positivity)
    (pow_nonneg (zero_le_one.trans hQ1) _) hbad2 h4mom
  rw [← hA] at hγle
  have hi2 : Integrable (fun d => (f d - m) ^ (2 * k)) stdDisLaw[N, M] :=
    (hmp.integrable_comp ((hf.sub_const m).pow_const _).aestronglyMeasurable).1 hiγ
  have hmed : ∫ d, (f d - m) ^ (2 * k) ∂stdDisLaw[N, M] ≤
      ((64 * Kg + 2 * Q ^ 2) * k / ((N : ℝ) + 1)) ^ k := by
    rw [← htrans (fun d => (f d - m) ^ (2 * k)) ((hf.sub_const m).pow_const _)]
    refine hγle.trans ?_
    set x : ℝ := 16 * k * A ^ 2 with hx
    set y : ℝ := Q ^ 2 * k / ((N : ℝ) + 1) with hy
    have hx0 : 0 ≤ x := by positivity
    have hy0 : 0 ≤ y := by positivity
    have h1 : 2 * Real.exp (-((N : ℝ) + 1)) * Q ^ (2 * k) ≤ 2 * y ^ k := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ zero_le_two
      refine (mul_le_mul_of_nonneg_right (Real.exp_neg_le_natCast_div_pow hN0 k)
        (pow_nonneg (zero_le_one.trans hQ1) _)).trans_eq ?_
      rw [pow_mul, ← mul_pow, hy]; congr 1; ring
    have h4 : 4 * x ^ k ≤ (4 * x) ^ k := by
      rw [mul_pow (4 : ℝ) x]
      exact mul_le_mul_of_nonneg_right (le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 4) hk0)
        (pow_nonneg hx0 _)
    have h2 : 2 * y ^ k ≤ (2 * y) ^ k := by
      rw [mul_pow (2 : ℝ) y]
      exact mul_le_mul_of_nonneg_right (le_self_pow₀ one_le_two hk0) (pow_nonneg hy0 _)
    refine (add_le_add h4 (h1.trans h2)).trans ?_
    refine (pow_add_pow_le (by positivity) (by positivity) hk0).trans_eq ?_
    rw [hx, hy, hA2]; congr 1; ring
  have hsym := integral_sub_integral_pow_two_mul_le (μ := stdDisLaw[N, M]) (f := f) (m := m)
    (k := k) hf.aestronglyMeasurable hi2
  refine ⟨hsym.1, hsym.2.trans ?_⟩
  refine (mul_le_mul_of_nonneg_left hmed (by positivity)).trans_eq ?_
  rw [pow_mul, ← mul_pow]; congr 1; ring

/-- Combining quenched and disorder fluctuations (copy of the private helper in
`DisorderConcentration.lean`). -/
private theorem integral_integral_sub_pow_le' {Ω α : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] {P : Measure Ω} {G : Ω → Measure α}
    [∀ d, IsProbabilityMeasure (G d)] {R : α → ℝ} (hR : Measurable R) {k : ℕ} (hk : k ≠ 0)
    (c : ℝ) (hm : Measurable fun d => ∫ σ, (R σ - c) ^ (2 * k) ∂(G d))
    (hfix : ∀ d, Integrable (fun σ => (R σ - ∫ τ, R τ ∂(G d)) ^ (2 * k)) (G d))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h1i : Integrable (fun d => ∫ σ, (R σ - ∫ τ, R τ ∂(G d)) ^ (2 * k) ∂(G d)) P)
    (h1 : ∫ d, ∫ σ, (R σ - ∫ τ, R τ ∂(G d)) ^ (2 * k) ∂(G d) ∂P ≤ a ^ k)
    (h2i : Integrable (fun d => ((∫ τ, R τ ∂(G d)) - c) ^ (2 * k)) P)
    (h2 : ∫ d, ((∫ τ, R τ ∂(G d)) - c) ^ (2 * k) ∂P ≤ b ^ k) :
    Integrable (fun d => ∫ σ, (R σ - c) ^ (2 * k) ∂(G d)) P ∧
      ∫ d, ∫ σ, (R σ - c) ^ (2 * k) ∂(G d) ∂P ≤ (4 * (a + b)) ^ k := by
  have heven : Even (2 * k) := even_two_mul k
  have hpt : ∀ d, ∫ σ, (R σ - c) ^ (2 * k) ∂(G d) ≤ 2 ^ (2 * k - 1) *
      ((∫ σ, (R σ - ∫ τ, R τ ∂(G d)) ^ (2 * k) ∂(G d)) +
        ((∫ τ, R τ ∂(G d)) - c) ^ (2 * k)) := fun d => by
    have h := (integral_add_pow_two_mul_le (μ := G d)
      (X := fun σ => R σ - ∫ τ, R τ ∂(G d)) (Y := fun _ => (∫ τ, R τ ∂(G d)) - c)
      (hR.sub_const _).aestronglyMeasurable aestronglyMeasurable_const (hfix d)
      (integrable_const _)).2
    simpa only [sub_add_sub_cancel, integral_const, probReal_univ, one_smul] using h
  have hdom := (h1i.add h2i).const_mul (2 ^ (2 * k - 1) : ℝ)
  have hi : Integrable (fun d => ∫ σ, (R σ - c) ^ (2 * k) ∂(G d)) P :=
    Integrable.mono' hdom hm.aestronglyMeasurable (ae_of_all _ fun d => by
      rw [Real.norm_of_nonneg (integral_nonneg fun σ => heven.pow_nonneg _)]
      exact hpt d)
  refine ⟨hi, (integral_mono hi hdom hpt).trans ?_⟩
  simp only [Pi.add_apply]
  rw [integral_const_mul, integral_add h1i h2i]
  refine (mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)).trans ?_
  have h4 : (2 : ℝ) ^ (2 * k - 1) ≤ 4 ^ k := by
    rw [show (4 : ℝ) ^ k = 2 ^ (2 * k) by rw [pow_mul]; norm_num]
    exact pow_le_pow_right₀ one_le_two (by omega)
  rw [mul_pow]
  exact mul_le_mul h4 (pow_add_pow_le ha hb hk) (by positivity) (by positivity)

/-- **Talagrand, Eq. (3.111) (uniform-in-`t` Theorem 3.1.18) for `R_{1,1}`:** for `4 k ≤ N + 1`,
`ν_t ((R_{1,1} - ν_t (R_{1,1})) ^ (2 k)) ≤ (K k / (N + 1)) ^ k`, uniformly in `t ∈ [0, 1]`,
where `K` depends only on `κ₀, h₀, D, R, R_diff`. -/
theorem exists_integral_shcherbinaTirozziCavity_selfOverlap_sub_pow_le
    (κ₀ h₀ D R R_diff : ℝ) (hκ₀ : 0 < κ₀) (hR : 0 ≤ R) (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M k : ℕ) (κ h t rBar : ℝ) (r : ℝ≥0) (u : ℝ → ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → rBar ≤ r → (r : ℝ) ≤ R →
      (r : ℝ) - rBar ≤ R_diff → M ≤ 10 * (N + 1) → 4 * k ≤ N + 1 →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → (∀ x, -D * (1 + |x|) ≤ u x) →
      Differentiable ℝ u → (∀ x, |deriv u x| ≤ D) →
      (∀ a b, |deriv u a - deriv u b| ≤ D * |a - b|) →
      let G : Dis[N, M] → Measure (ℝ^(N + 1)) := fun d =>
        volume.tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 σ
      Integrable (fun d => ∫ σ, (((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 -
            ∫ e, ∫ τ, ((N : ℝ) + 1)⁻¹ * ‖τ‖ ^ 2 ∂(G e) ∂cavLaw[N, M, r]) ^ (2 * k) ∂(G d))
          cavLaw[N, M, r] ∧
        ∫ d, ∫ σ, (((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 -
            ∫ e, ∫ τ, ((N : ℝ) + 1)⁻¹ * ‖τ‖ ^ 2 ∂(G e) ∂cavLaw[N, M, r]) ^ (2 * k) ∂(G d)
            ∂cavLaw[N, M, r] ≤
          (K * k / ((N : ℝ) + 1)) ^ k := by
  obtain ⟨K₉, hK₉, h319⟩ :=
    exists_integral_sq_norm_pow_shcherbinaTirozziCavity_le κ₀ h₀ D R_diff hκ₀ hR_diff
  obtain ⟨K₁₁, hK₁₁, h335⟩ :=
    exists_integral_shcherbinaTirozziCavity_selfOverlap_sub_mean_pow_le κ₀ h₀ D R_diff hκ₀ hR_diff
  obtain ⟨K₁₆, hK₁₆, h316⟩ :=
    exists_hasDerivAt_integral_shcherbinaTirozziCavity_selfOverlap_line κ₀ h₀ D R_diff hκ₀ hR_diff
  obtain ⟨K₁₇, hK₁₇, h317⟩ := exists_integral_sub_integral_pow_le_of_cavityDisorder_gradient
    (K₉ * (1 + R)) (K₁₆ * (1 + R) ^ 3) (by positivity) (by positivity)
  refine ⟨4 * (48 * K₁₁ * (1 + R) + K₁₇), by positivity,
    fun N M k κ h t rBar r u hκ hh ht0 ht1 hrr hrR hrr_diff hM hk hu hu0 hD hud hD1 hD2 => ?_⟩
  intro G
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum := hu.measurable_of_univ
  have hq : 0 ≤ (1 - t) * ((r : ℝ) - rBar) := mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hrr)
  have hprob : ∀ d, IsProbabilityMeasure (G d) := fun d =>
    isProbabilityMeasure_tilted
      (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ0 hq hum hu0 d.2.1 d.2.2)
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hkN : k ≤ N + 1 := by omega
  let S : Dis[N, M] → Dis[N, M] := fun d => (Real.sqrt (r : ℝ) * d.1, d.2)
  have hmpS : MeasurePreserving S stdDisLaw[N, M] cavLaw[N, M, r] :=
    measurePreserving_scale_y N M r
  have hE : Measurable fun p : Dis[N, M] × ℝ^(N + 1) =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t p.1.1 u p.1.2.1 p.1.2.2 p.2 :=
    (measurable_shcherbinaTirozziCavityHamiltonian κ h r rBar t hum).neg
  have hRm : Measurable fun σ : ℝ^(N + 1) => ((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 := by fun_prop
  obtain ⟨m, hm⟩ : ∃ m : Dis[N, M] → ℝ, ∀ d,
      ∫ τ, ((N : ℝ) + 1)⁻¹ * ‖τ‖ ^ 2 ∂(G d) = m d := ⟨_, fun _ => rfl⟩
  have hmm : Measurable m :=
    (funext hm) ▸ measurable_integral_tilted hE hRm
  have hB_scale : ∀ d : Dis[N, M],
      ((N : ℝ) + 1) + Real.sqrt (∑ k, ∑ i, d.2.1 k i ^ 2) + (∑ i, d.2.2 i ^ 2) +
          (Real.sqrt (r : ℝ) * d.1) ^ 2 ≤
        (1 + R) * B_std[N, M] d := fun d => by
    have hr1 : (Real.sqrt (r : ℝ) * d.1) ^ 2 ≤ R * d.1 ^ 2 := by
      rw [mul_pow, Real.sq_sqrt r.coe_nonneg]
      exact mul_le_mul_of_nonneg_right hrR (sq_nonneg _)
    have hnn : 0 ≤ ((N : ℝ) + 1) + Real.sqrt (∑ k, ∑ i, d.2.1 k i ^ 2) +
        ∑ i, d.2.2 i ^ 2 := add_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    nlinarith [sq_nonneg d.1]
  have hgrowth : ∀ d : Dis[N, M],
      |m (S d)| ≤ (K₉ * (1 + R)) * B_std[N, M] d / ((N : ℝ) + 1) := fun d => by
    have h1 := (h319 N M 1 κ h r rBar t (Real.sqrt (r : ℝ) * d.1) u d.2.1 d.2.2
      hκ hh ht0 ht1 hrr hrr_diff hM (by omega) hum hu0 hD).2
    simp only [mul_one, pow_one] at h1
    rw [← hm, abs_of_nonneg (integral_nonneg fun τ =>
      mul_nonneg (inv_nonneg.2 hN0.le) (sq_nonneg _)), integral_const_mul, div_eq_inv_mul]
    calc ((N : ℝ) + 1)⁻¹ * ∫ τ, ‖τ‖ ^ 2 ∂(G (S d))
        ≤ ((N : ℝ) + 1)⁻¹ * (K₉ * (((N : ℝ) + 1) + Real.sqrt (∑ k, ∑ i, d.2.1 k i ^ 2) +
            (∑ i, d.2.2 i ^ 2) + (Real.sqrt (r : ℝ) * d.1) ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hN0.le)
      _ ≤ ((N : ℝ) + 1)⁻¹ * (K₉ * ((1 + R) * B_std[N, M] d)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hB_scale d) hK₉)
            (inv_nonneg.2 hN0.le)
      _ = ((N : ℝ) + 1)⁻¹ * (K₉ * (1 + R) * B_std[N, M] d) := by ring
  have hgrad : ∀ d Δ : Dis[N, M], ∃ f' : ℝ,
      HasDerivAt (fun s : ℝ => m (S (d + s • Δ))) f' 0 ∧
      f' ^ 2 ≤ (K₁₆ * (1 + R) ^ 3) * (B_std[N, M] d / ((N : ℝ) + 1) ^ 2 +
        B_std[N, M] d ^ 2 * ‖Matrix.of d.2.1‖ ^ 2 / ((N : ℝ) + 1) ^ 4) *
        ((∑ k, ∑ i, Δ.2.1 k i ^ 2) + (∑ i, Δ.2.2 i ^ 2) + Δ.1 ^ 2) := fun d Δ => by
    obtain ⟨f', hf', hb⟩ := h316 N M κ h r rBar t (Real.sqrt (r : ℝ) * d.1)
      (Real.sqrt (r : ℝ) * Δ.1) u d.2.1 Δ.2.1 d.2.2 Δ.2.2
      hκ hh ht0 ht1 hrr hrr_diff hM hu hu0 hD hud hD1 hD2
    refine ⟨f', hf'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_), ?_⟩
    · refine (hm _).symm.trans ?_
      have heq : Real.sqrt (r : ℝ) * (d.1 + s * Δ.1) =
          Real.sqrt (r : ℝ) * d.1 + s * (Real.sqrt (r : ℝ) * Δ.1) := by ring
      change ∫ σ, ((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 ∂(volume.tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar t (Real.sqrt (r : ℝ) * (d.1 + s * Δ.1))
            u (fun k i => d.2.1 k i + s * Δ.2.1 k i) (fun i => d.2.2 i + s * Δ.2.2 i) σ) = _
      rw [heq]
    · set Bc := ((N : ℝ) + 1) + Real.sqrt (∑ k, ∑ i, d.2.1 k i ^ 2) + (∑ i, d.2.2 i ^ 2) +
          (Real.sqrt (r : ℝ) * d.1) ^ 2
      have hBc0 : 0 ≤ Bc := add_nonneg (add_nonneg (by positivity)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (sq_nonneg _)
      have hBc_le : Bc ≤ (1 + R) * B_std[N, M] d := hB_scale d
      have hR1 : (1 : ℝ) ≤ 1 + R := by linarith
      have hterm1 : Bc / ((N : ℝ) + 1) ^ 2 ≤ (1 + R) ^ 2 * (B_std[N, M] d / ((N : ℝ) + 1) ^ 2) := by
        have h1 : Bc ≤ (1 + R) ^ 2 * B_std[N, M] d := hBc_le.trans (mul_le_mul_of_nonneg_right
          (le_self_pow₀ hR1 (by norm_num)) (add_nonneg (add_nonneg (by positivity)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (sq_nonneg _)))
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right h1 (by positivity)
      have hterm2 : Bc ^ 2 * ‖Matrix.of d.2.1‖ ^ 2 / ((N : ℝ) + 1) ^ 4 ≤
          (1 + R) ^ 2 * (B_std[N, M] d ^ 2 * ‖Matrix.of d.2.1‖ ^ 2 / ((N : ℝ) + 1) ^ 4) := by
        have h1 : Bc ^ 2 ≤ (1 + R) ^ 2 * B_std[N, M] d ^ 2 := by
          rw [← mul_pow]; exact pow_le_pow_left₀ hBc0 hBc_le 2
        rw [← mul_div_assoc, ← mul_assoc]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (sq_nonneg _))
          (by positivity)
      have hΔ : (∑ k, ∑ i, Δ.2.1 k i ^ 2) + (∑ i, Δ.2.2 i ^ 2) + (Real.sqrt (r : ℝ) * Δ.1) ^ 2 ≤
          (1 + R) * ((∑ k, ∑ i, Δ.2.1 k i ^ 2) + (∑ i, Δ.2.2 i ^ 2) + Δ.1 ^ 2) := by
        have h1 : (Real.sqrt (r : ℝ) * Δ.1) ^ 2 ≤ R * Δ.1 ^ 2 := by
          rw [mul_pow, Real.sq_sqrt r.coe_nonneg]
          exact mul_le_mul_of_nonneg_right hrR (sq_nonneg _)
        have hnn : 0 ≤ (∑ k, ∑ i, Δ.2.1 k i ^ 2) + ∑ i, Δ.2.2 i ^ 2 :=
          add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)
        nlinarith [sq_nonneg Δ.1]
      refine hb.trans ?_
      have hsum : Bc / ((N : ℝ) + 1) ^ 2 + Bc ^ 2 * ‖Matrix.of d.2.1‖ ^ 2 / ((N : ℝ) + 1) ^ 4 ≤
          (1 + R) ^ 2 * (B_std[N, M] d / ((N : ℝ) + 1) ^ 2 +
            B_std[N, M] d ^ 2 * ‖Matrix.of d.2.1‖ ^ 2 / ((N : ℝ) + 1) ^ 4) := by
        rw [mul_add]; exact add_le_add hterm1 hterm2
      have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hsum hK₁₆) hΔ
        (add_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (sq_nonneg _)) (by positivity)
      exact hprod.trans_eq (by ring)
  have h17 := h317 N M k hM hk (fun d => m (S d)) (hmm.comp hmpS.measurable) hgrowth hgrad
  have hmean_eq : ∫ e, m (S e) ∂stdDisLaw[N, M] = ∫ e, m e ∂cavLaw[N, M, r] := by
    rw [← hmpS.map_eq, integral_map hmpS.measurable.aemeasurable hmm.aestronglyMeasurable]
  rw [hmean_eq] at h17
  set c : ℝ := ∫ e, m e ∂cavLaw[N, M, r] with hc_def
  have h17' : Integrable (fun d => (m d - c) ^ (2 * k)) cavLaw[N, M, r] ∧
      ∫ d, (m d - c) ^ (2 * k) ∂cavLaw[N, M, r] ≤
        (K₁₇ * k / ((N : ℝ) + 1)) ^ k := by
    refine ⟨(hmpS.integrable_comp ((hmm.sub_const c).pow_const _).aestronglyMeasurable).1 h17.1, ?_⟩
    rw [← hmpS.map_eq,
      integral_map hmpS.measurable.aemeasurable ((hmm.sub_const c).pow_const _).aestronglyMeasurable]
    exact h17.2
  -- Quenched fluctuation integrated over `cavLaw[N, M, r]`
  have hfix : ∀ d, Integrable (fun σ => (((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 -
      ∫ τ, ((N : ℝ) + 1)⁻¹ * ‖τ‖ ^ 2 ∂(G d)) ^ (2 * k)) (G d) := fun d =>
    (h335 N M k κ h r rBar t d.1 u d.2.1 d.2.2 hκ hh ht0 ht1 hrr hrr_diff hM hkN hu hu0 hD
      (G d) rfl).1
  have hq_meas : Measurable fun d : Dis[N, M] =>
      ∫ σ, (((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 - m d) ^ (2 * k) ∂(G d) :=
    measurable_integral_tilted_dep hE
      (Y := fun d σ => (((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 - m d) ^ (2 * k))
      (((hRm.comp measurable_snd).sub (hmm.comp measurable_fst)).pow_const _)
  have hq_std : Integrable (fun d => ∫ σ, (((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 - m (S d)) ^ (2 * k)
        ∂(G (S d))) stdDisLaw[N, M] ∧
      ∫ d, ∫ σ, (((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 - m (S d)) ^ (2 * k) ∂(G (S d)) ∂stdDisLaw[N, M] ≤
        (48 * K₁₁ * (1 + R) * k / ((N : ℝ) + 1)) ^ k := by
    have hrad := integral_cavity_radius_pow_le (N := N) (M := M) hM hkN
    have hpt : ∀ d : Dis[N, M],
        ∫ σ, (((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 - m (S d)) ^ (2 * k) ∂(G (S d)) ≤
          (K₁₁ * (1 + R) * k / ((N : ℝ) + 1) ^ 2) ^ k * B_std[N, M] d ^ k := fun d => by
      have h1 := (h335 N M k κ h r rBar t (Real.sqrt (r : ℝ) * d.1) u d.2.1 d.2.2
        hκ hh ht0 ht1 hrr hrr_diff hM hkN hu hu0 hD (G (S d)) rfl).2
      rw [hm (S d)] at h1
      refine h1.trans ?_
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ k
      calc K₁₁ * k * (((N : ℝ) + 1) + Real.sqrt (∑ k, ∑ i, d.2.1 k i ^ 2) +
              (∑ i, d.2.2 i ^ 2) + (Real.sqrt (r : ℝ) * d.1) ^ 2) / ((N : ℝ) + 1) ^ 2
          ≤ K₁₁ * k * ((1 + R) * B_std[N, M] d) / ((N : ℝ) + 1) ^ 2 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hB_scale d) (by positivity))
              (by positivity)
        _ = K₁₁ * (1 + R) * k / ((N : ℝ) + 1) ^ 2 * B_std[N, M] d := by ring
    have hi : Integrable (fun d => ∫ σ, (((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 - m (S d)) ^ (2 * k)
        ∂(G (S d))) stdDisLaw[N, M] :=
      Integrable.mono' (hrad.1.const_mul _) (hq_meas.comp hmpS.measurable).aestronglyMeasurable
        (ae_of_all _ fun d => by
          rw [Real.norm_of_nonneg (integral_nonneg fun σ => (even_two_mul k).pow_nonneg _)]
          exact hpt d)
    refine ⟨hi, (integral_mono hi (hrad.1.const_mul _) hpt).trans ?_⟩
    rw [integral_const_mul]
    refine (mul_le_mul_of_nonneg_left hrad.2 (by positivity)).trans_eq ?_
    rw [← mul_pow]; congr 1; field_simp
  have h12 : Integrable (fun d => ∫ σ, (((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 -
        ∫ τ, ((N : ℝ) + 1)⁻¹ * ‖τ‖ ^ 2 ∂(G d)) ^ (2 * k) ∂(G d)) cavLaw[N, M, r] ∧
      ∫ d, ∫ σ, (((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 -
        ∫ τ, ((N : ℝ) + 1)⁻¹ * ‖τ‖ ^ 2 ∂(G d)) ^ (2 * k) ∂(G d) ∂cavLaw[N, M, r] ≤
        (48 * K₁₁ * (1 + R) * k / ((N : ℝ) + 1)) ^ k := by
    simp_rw [hm]
    refine ⟨(hmpS.integrable_comp hq_meas.aestronglyMeasurable).1 hq_std.1, ?_⟩
    rw [← hmpS.map_eq, integral_map hmpS.measurable.aemeasurable hq_meas.aestronglyMeasurable]
    exact hq_std.2
  have hcm : (∫ e, ∫ τ, ((N : ℝ) + 1)⁻¹ * ‖τ‖ ^ 2 ∂(G e) ∂cavLaw[N, M, r]) = c := by
    rw [hc_def]; simp only [hm]
  rw [hcm]
  have hmc : Measurable fun d => ∫ σ, (((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2 - c) ^ (2 * k) ∂(G d) :=
    measurable_integral_tilted hE ((hRm.sub_const c).pow_const _)
  have h := integral_integral_sub_pow_le' (P := cavLaw[N, M, r]) (G := G)
    (R := fun σ : ℝ^(N + 1) => ((N : ℝ) + 1)⁻¹ * ‖σ‖ ^ 2) hRm hk0 c hmc hfix
    (a := 48 * K₁₁ * (1 + R) * k / ((N : ℝ) + 1)) (b := K₁₇ * k / ((N : ℝ) + 1))
    (by positivity) (by positivity) h12.1 h12.2
    (by simpa only [hm] using h17'.1) (by simpa only [hm] using h17'.2)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  congr 1; ring

/-- **Talagrand, Eq. (3.111) (uniform-in-`t` Theorem 3.1.18) for `R_{1,2}`:** for `4 k ≤ N + 1`,
`ν_t ((R_{1,2} - ν_t (R_{1,2})) ^ (2 k)) ≤ (K k / (N + 1)) ^ k`, uniformly in `t ∈ [0, 1]`,
where `K` depends only on `κ₀, h₀, D, R, R_diff`. -/
theorem exists_integral_shcherbinaTirozziCavity_overlap_sub_pow_le
    (κ₀ h₀ D R R_diff : ℝ) (hκ₀ : 0 < κ₀) (hR : 0 ≤ R) (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M k : ℕ) (κ h t rBar : ℝ) (r : ℝ≥0) (u : ℝ → ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → rBar ≤ r → (r : ℝ) ≤ R →
      (r : ℝ) - rBar ≤ R_diff → M ≤ 10 * (N + 1) → 4 * k ≤ N + 1 →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → (∀ x, -D * (1 + |x|) ≤ u x) →
      Differentiable ℝ u → (∀ x, |deriv u x| ≤ D) →
      (∀ a b, |deriv u a - deriv u b| ≤ D * |a - b|) →
      let G : Dis[N, M] → Measure (ℝ^(N + 1)) := fun d =>
        volume.tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 σ
      Integrable (fun d => ∫ p, (((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ -
            ∫ e, ∫ q, ((N : ℝ) + 1)⁻¹ * ⟪q.1, q.2⟫ ∂((G e).prod (G e)) ∂cavLaw[N, M, r]) ^ (2 * k)
            ∂((G d).prod (G d))) cavLaw[N, M, r] ∧
        ∫ d, ∫ p, (((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ -
            ∫ e, ∫ q, ((N : ℝ) + 1)⁻¹ * ⟪q.1, q.2⟫ ∂((G e).prod (G e)) ∂cavLaw[N, M, r]) ^ (2 * k)
            ∂((G d).prod (G d)) ∂cavLaw[N, M, r] ≤
          (K * k / ((N : ℝ) + 1)) ^ k := by
  obtain ⟨K₉, hK₉, h319⟩ :=
    exists_integral_sq_norm_pow_shcherbinaTirozziCavity_le κ₀ h₀ D R_diff hκ₀ hR_diff
  obtain ⟨K₁₁, hK₁₁, h334⟩ :=
    exists_integral_shcherbinaTirozziCavity_overlap_sub_mean_pow_le κ₀ h₀ D R_diff hκ₀ hR_diff
  obtain ⟨K₁₆, hK₁₆, h316⟩ :=
    exists_hasDerivAt_integral_shcherbinaTirozziCavity_overlap_line κ₀ h₀ D R_diff hκ₀ hR_diff
  obtain ⟨K₁₇, hK₁₇, h317⟩ := exists_integral_sub_integral_pow_le_of_cavityDisorder_gradient
    (K₉ * (1 + R)) (K₁₆ * (1 + R) ^ 3) (by positivity) (by positivity)
  refine ⟨4 * (48 * K₁₁ * (1 + R) + K₁₇), by positivity,
    fun N M k κ h t rBar r u hκ hh ht0 ht1 hrr hrR hrr_diff hM hk hu hu0 hD hud hD1 hD2 => ?_⟩
  intro G
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum := hu.measurable_of_univ
  have hq : 0 ≤ (1 - t) * ((r : ℝ) - rBar) := mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hrr)
  have hprob : ∀ d, IsProbabilityMeasure (G d) := fun d =>
    isProbabilityMeasure_tilted
      (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ0 hq hum hu0 d.2.1 d.2.2)
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  have hN0 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hkN : k ≤ N + 1 := by omega
  let S : Dis[N, M] → Dis[N, M] := fun d => (Real.sqrt (r : ℝ) * d.1, d.2)
  have hmpS : MeasurePreserving S stdDisLaw[N, M] cavLaw[N, M, r] :=
    measurePreserving_scale_y N M r
  have hE : Measurable fun p : Dis[N, M] × ℝ^(N + 1) =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t p.1.1 u p.1.2.1 p.1.2.2 p.2 :=
    (measurable_shcherbinaTirozziCavityHamiltonian κ h r rBar t hum).neg
  have hRm : Measurable fun p : ℝ^(N + 1) × ℝ^(N + 1) =>
      ((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ := by fun_prop
  have hnorm : ∀ d, MemLp (fun σ : ℝ^(N + 1) => σ) 2 (G d) := fun d => by
    have hconf : ∀ σ : ℝ^(N + 1),
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 σ ≤
          0 + (|h| * ∑ i, |d.2.2 i| + |d.1|) * ‖σ‖ - κ * ‖σ‖ ^ 2 := fun σ => by
      rw [zero_add]
      exact neg_shcherbinaTirozziCavityHamiltonian_le κ h d.1 hrr ht0 ht1 hu0 d.2.1 d.2.2 σ
    exact_mod_cast memLp_of_poly_bound_of_confining hκ0
      (measurable_shcherbinaTirozziCavityHamiltonian_apply κ h r rBar t d.1 hum d.2.1 d.2.2).neg
      hconf (f := fun σ : ℝ^(N + 1) => σ) aestronglyMeasurable_id (C := 1) (m := 1)
      (fun σ => by simp) 2
  have hbary : ∀ d, ∫ q, ((N : ℝ) + 1)⁻¹ * ⟪q.1, q.2⟫ ∂((G d).prod (G d)) =
      ((N : ℝ) + 1)⁻¹ * ‖∫ σ, σ ∂(G d)‖ ^ 2 := fun d => by
    have h1 := (hnorm d).integrable one_le_two
    rw [integral_const_mul, ← real_inner_self_eq_norm_sq]
    exact congrArg _ (integral_prod_bilin (innerSL ℝ) h1 h1)
  have hmeas : ∀ F : Dis[N, M] → ℝ^(N + 1) × ℝ^(N + 1) → ℝ,
      Measurable (Function.uncurry F) →
      (∀ d, Integrable (F d) ((G d).prod (G d))) →
      Measurable fun d => ∫ p, F d p ∂((G d).prod (G d)) := fun F hF hFi =>
    measurable_integral_prod_tilted_dep hE hF hFi
  have hRi : ∀ d, Integrable (fun p : ℝ^(N + 1) × ℝ^(N + 1) =>
      ((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫) ((G d).prod (G d)) := fun d =>
    have h1 := (hnorm d).integrable one_le_two
    (h1.inner_fst_snd h1).const_mul _
  obtain ⟨m, hm⟩ : ∃ m : Dis[N, M] → ℝ, ∀ d,
      ∫ q, ((N : ℝ) + 1)⁻¹ * ⟪q.1, q.2⟫ ∂((G d).prod (G d)) = m d := ⟨_, fun _ => rfl⟩
  have hmm : Measurable m :=
    (funext hm) ▸ hmeas (fun _ p => ((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫) (hRm.comp measurable_snd) hRi
  have hB_scale : ∀ d : Dis[N, M],
      ((N : ℝ) + 1) + Real.sqrt (∑ k, ∑ i, d.2.1 k i ^ 2) + (∑ i, d.2.2 i ^ 2) +
          (Real.sqrt (r : ℝ) * d.1) ^ 2 ≤
        (1 + R) * B_std[N, M] d := fun d => by
    have hr1 : (Real.sqrt (r : ℝ) * d.1) ^ 2 ≤ R * d.1 ^ 2 := by
      rw [mul_pow, Real.sq_sqrt r.coe_nonneg]
      exact mul_le_mul_of_nonneg_right hrR (sq_nonneg _)
    have hnn : 0 ≤ ((N : ℝ) + 1) + Real.sqrt (∑ k, ∑ i, d.2.1 k i ^ 2) +
        ∑ i, d.2.2 i ^ 2 := add_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    nlinarith [sq_nonneg d.1]
  have hgrowth : ∀ d : Dis[N, M],
      |m (S d)| ≤ (K₉ * (1 + R)) * B_std[N, M] d / ((N : ℝ) + 1) := fun d => by
    have h1 := (h319 N M 1 κ h r rBar t (Real.sqrt (r : ℝ) * d.1) u d.2.1 d.2.2
      hκ hh ht0 ht1 hrr hrr_diff hM (by omega) hum hu0 hD).2
    simp only [mul_one, pow_one] at h1
    rw [← hm, hbary, abs_of_nonneg (mul_nonneg (inv_nonneg.2 hN0.le) (sq_nonneg _)), div_eq_inv_mul]
    calc ((N : ℝ) + 1)⁻¹ * ‖∫ σ, σ ∂(G (S d))‖ ^ 2
        ≤ ((N : ℝ) + 1)⁻¹ * ∫ τ, ‖τ‖ ^ 2 ∂(G (S d)) :=
          mul_le_mul_of_nonneg_left (sq_norm_integral_le_integral_sq_norm (hnorm (S d)))
            (inv_nonneg.2 hN0.le)
      _ ≤ ((N : ℝ) + 1)⁻¹ * (K₉ * (((N : ℝ) + 1) + Real.sqrt (∑ k, ∑ i, d.2.1 k i ^ 2) +
            (∑ i, d.2.2 i ^ 2) + (Real.sqrt (r : ℝ) * d.1) ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hN0.le)
      _ ≤ ((N : ℝ) + 1)⁻¹ * (K₉ * ((1 + R) * B_std[N, M] d)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hB_scale d) hK₉)
            (inv_nonneg.2 hN0.le)
      _ = ((N : ℝ) + 1)⁻¹ * (K₉ * (1 + R) * B_std[N, M] d) := by ring
  have hgrad : ∀ d Δ : Dis[N, M], ∃ f' : ℝ,
      HasDerivAt (fun s : ℝ => m (S (d + s • Δ))) f' 0 ∧
      f' ^ 2 ≤ (K₁₆ * (1 + R) ^ 3) * (B_std[N, M] d / ((N : ℝ) + 1) ^ 2 +
        B_std[N, M] d ^ 2 * ‖Matrix.of d.2.1‖ ^ 2 / ((N : ℝ) + 1) ^ 4) *
        ((∑ k, ∑ i, Δ.2.1 k i ^ 2) + (∑ i, Δ.2.2 i ^ 2) + Δ.1 ^ 2) := fun d Δ => by
    obtain ⟨f', hf', hb⟩ := h316 N M κ h r rBar t (Real.sqrt (r : ℝ) * d.1)
      (Real.sqrt (r : ℝ) * Δ.1) u d.2.1 Δ.2.1 d.2.2 Δ.2.2
      hκ hh ht0 ht1 hrr hrr_diff hM hu hu0 hD hud hD1 hD2
      (fun s => G (S (d + s • Δ))) (fun s => by
        have heq : Real.sqrt (r : ℝ) * (d.1 + s * Δ.1) =
            Real.sqrt (r : ℝ) * d.1 + s * (Real.sqrt (r : ℝ) * Δ.1) := by ring
        change volume.tilted (fun σ =>
            -shcherbinaTirozziCavityHamiltonian κ h r rBar t (Real.sqrt (r : ℝ) * (d.1 + s * Δ.1))
              u (fun k i => d.2.1 k i + s * Δ.2.1 k i) (fun i => d.2.2 i + s * Δ.2.2 i) σ) = _
        rw [heq])
    refine ⟨f', hf'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => (hm _).symm), ?_⟩
    set Bc := ((N : ℝ) + 1) + Real.sqrt (∑ k, ∑ i, d.2.1 k i ^ 2) + (∑ i, d.2.2 i ^ 2) +
        (Real.sqrt (r : ℝ) * d.1) ^ 2
    have hBc0 : 0 ≤ Bc := add_nonneg (add_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (sq_nonneg _)
    have hBc_le : Bc ≤ (1 + R) * B_std[N, M] d := hB_scale d
    have hR1 : (1 : ℝ) ≤ 1 + R := by linarith
    have hterm1 : Bc / ((N : ℝ) + 1) ^ 2 ≤ (1 + R) ^ 2 * (B_std[N, M] d / ((N : ℝ) + 1) ^ 2) := by
      have h1 : Bc ≤ (1 + R) ^ 2 * B_std[N, M] d := hBc_le.trans (mul_le_mul_of_nonneg_right
        (le_self_pow₀ hR1 (by norm_num)) (add_nonneg (add_nonneg (by positivity)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (sq_nonneg _)))
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right h1 (by positivity)
    have hterm2 : Bc ^ 2 * ‖Matrix.of d.2.1‖ ^ 2 / ((N : ℝ) + 1) ^ 4 ≤
        (1 + R) ^ 2 * (B_std[N, M] d ^ 2 * ‖Matrix.of d.2.1‖ ^ 2 / ((N : ℝ) + 1) ^ 4) := by
      have h1 : Bc ^ 2 ≤ (1 + R) ^ 2 * B_std[N, M] d ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ hBc0 hBc_le 2
      rw [← mul_div_assoc, ← mul_assoc]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (sq_nonneg _))
        (by positivity)
    have hΔ : (∑ k, ∑ i, Δ.2.1 k i ^ 2) + (∑ i, Δ.2.2 i ^ 2) + (Real.sqrt (r : ℝ) * Δ.1) ^ 2 ≤
        (1 + R) * ((∑ k, ∑ i, Δ.2.1 k i ^ 2) + (∑ i, Δ.2.2 i ^ 2) + Δ.1 ^ 2) := by
      have h1 : (Real.sqrt (r : ℝ) * Δ.1) ^ 2 ≤ R * Δ.1 ^ 2 := by
        rw [mul_pow, Real.sq_sqrt r.coe_nonneg]
        exact mul_le_mul_of_nonneg_right hrR (sq_nonneg _)
      have hnn : 0 ≤ (∑ k, ∑ i, Δ.2.1 k i ^ 2) + ∑ i, Δ.2.2 i ^ 2 :=
        add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      nlinarith [sq_nonneg Δ.1]
    refine hb.trans ?_
    have hsum : Bc / ((N : ℝ) + 1) ^ 2 + Bc ^ 2 * ‖Matrix.of d.2.1‖ ^ 2 / ((N : ℝ) + 1) ^ 4 ≤
        (1 + R) ^ 2 * (B_std[N, M] d / ((N : ℝ) + 1) ^ 2 +
          B_std[N, M] d ^ 2 * ‖Matrix.of d.2.1‖ ^ 2 / ((N : ℝ) + 1) ^ 4) := by
      rw [mul_add]; exact add_le_add hterm1 hterm2
    have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hsum hK₁₆) hΔ
      (add_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (sq_nonneg _)) (by positivity)
    exact hprod.trans_eq (by ring)
  have h17 := h317 N M k hM hk (fun d => m (S d)) (hmm.comp hmpS.measurable) hgrowth hgrad
  have hmean_eq : ∫ e, m (S e) ∂stdDisLaw[N, M] = ∫ e, m e ∂cavLaw[N, M, r] := by
    rw [← hmpS.map_eq, integral_map hmpS.measurable.aemeasurable hmm.aestronglyMeasurable]
  rw [hmean_eq] at h17
  set c : ℝ := ∫ e, m e ∂cavLaw[N, M, r] with hc_def
  have h17' : Integrable (fun d => (m d - c) ^ (2 * k)) cavLaw[N, M, r] ∧
      ∫ d, (m d - c) ^ (2 * k) ∂cavLaw[N, M, r] ≤
        (K₁₇ * k / ((N : ℝ) + 1)) ^ k := by
    refine ⟨(hmpS.integrable_comp ((hmm.sub_const c).pow_const _).aestronglyMeasurable).1 h17.1, ?_⟩
    rw [← hmpS.map_eq,
      integral_map hmpS.measurable.aemeasurable ((hmm.sub_const c).pow_const _).aestronglyMeasurable]
    exact h17.2
  have hfix : ∀ d, Integrable (fun p : ℝ^(N + 1) × ℝ^(N + 1) =>
      (((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ -
        ∫ q, ((N : ℝ) + 1)⁻¹ * ⟪q.1, q.2⟫ ∂((G d).prod (G d))) ^ (2 * k))
      ((G d).prod (G d)) := fun d =>
    (h334 N M k κ h r rBar t d.1 u d.2.1 d.2.2 hκ hh ht0 ht1 hrr hrr_diff hM hkN hu hu0 hD
      (G d) rfl).1
  have hq_meas : Measurable fun d : Dis[N, M] =>
      ∫ p, (((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ - m d) ^ (2 * k) ∂((G d).prod (G d)) :=
    hmeas (fun d p => (((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ - m d) ^ (2 * k))
      (((hRm.comp measurable_snd).sub (hmm.comp measurable_fst)).pow_const _)
      (fun d => by simpa only [hm] using hfix d)
  have hq_std : Integrable (fun d => ∫ p, (((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ - m (S d)) ^ (2 * k)
        ∂((G (S d)).prod (G (S d)))) stdDisLaw[N, M] ∧
      ∫ d, ∫ p, (((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ - m (S d)) ^ (2 * k)
        ∂((G (S d)).prod (G (S d))) ∂stdDisLaw[N, M] ≤
        (48 * K₁₁ * (1 + R) * k / ((N : ℝ) + 1)) ^ k := by
    have hrad := integral_cavity_radius_pow_le (N := N) (M := M) hM hkN
    have hpt : ∀ d : Dis[N, M],
        ∫ p, (((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ - m (S d)) ^ (2 * k)
            ∂((G (S d)).prod (G (S d))) ≤
          (K₁₁ * (1 + R) * k / ((N : ℝ) + 1) ^ 2) ^ k * B_std[N, M] d ^ k := fun d => by
      have h1 := (h334 N M k κ h r rBar t (Real.sqrt (r : ℝ) * d.1) u d.2.1 d.2.2
        hκ hh ht0 ht1 hrr hrr_diff hM hkN hu hu0 hD (G (S d)) rfl).2
      rw [hm (S d)] at h1
      refine h1.trans ?_
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by positivity) ?_ k
      calc K₁₁ * k * (((N : ℝ) + 1) + Real.sqrt (∑ k, ∑ i, d.2.1 k i ^ 2) +
              (∑ i, d.2.2 i ^ 2) + (Real.sqrt (r : ℝ) * d.1) ^ 2) / ((N : ℝ) + 1) ^ 2
          ≤ K₁₁ * k * ((1 + R) * B_std[N, M] d) / ((N : ℝ) + 1) ^ 2 :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hB_scale d) (by positivity))
              (by positivity)
        _ = K₁₁ * (1 + R) * k / ((N : ℝ) + 1) ^ 2 * B_std[N, M] d := by ring
    have hi : Integrable (fun d => ∫ p, (((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ - m (S d)) ^ (2 * k)
        ∂((G (S d)).prod (G (S d)))) stdDisLaw[N, M] :=
      Integrable.mono' (hrad.1.const_mul _) (hq_meas.comp hmpS.measurable).aestronglyMeasurable
        (ae_of_all _ fun d => by
          rw [Real.norm_of_nonneg (integral_nonneg fun p => (even_two_mul k).pow_nonneg _)]
          exact hpt d)
    refine ⟨hi, (integral_mono hi (hrad.1.const_mul _) hpt).trans ?_⟩
    rw [integral_const_mul]
    refine (mul_le_mul_of_nonneg_left hrad.2 (by positivity)).trans_eq ?_
    rw [← mul_pow]; congr 1; field_simp
  have h12 : Integrable (fun d => ∫ p, (((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ -
        ∫ q, ((N : ℝ) + 1)⁻¹ * ⟪q.1, q.2⟫ ∂((G d).prod (G d))) ^ (2 * k)
        ∂((G d).prod (G d))) cavLaw[N, M, r] ∧
      ∫ d, ∫ p, (((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ -
        ∫ q, ((N : ℝ) + 1)⁻¹ * ⟪q.1, q.2⟫ ∂((G d).prod (G d))) ^ (2 * k)
        ∂((G d).prod (G d)) ∂cavLaw[N, M, r] ≤
        (48 * K₁₁ * (1 + R) * k / ((N : ℝ) + 1)) ^ k := by
    simp_rw [hm]
    refine ⟨(hmpS.integrable_comp hq_meas.aestronglyMeasurable).1 hq_std.1, ?_⟩
    rw [← hmpS.map_eq, integral_map hmpS.measurable.aemeasurable hq_meas.aestronglyMeasurable]
    exact hq_std.2
  have hcm : (∫ e, ∫ q, ((N : ℝ) + 1)⁻¹ * ⟪q.1, q.2⟫ ∂((G e).prod (G e)) ∂cavLaw[N, M, r]) = c := by
    rw [hc_def]; simp only [hm]
  rw [hcm]
  have hci : ∀ d, Integrable (fun p : ℝ^(N + 1) × ℝ^(N + 1) =>
      (((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ - c) ^ (2 * k)) ((G d).prod (G d)) := fun d => by
    have h := (integral_add_pow_two_mul_le (μ := (G d).prod (G d))
      (X := fun p => ((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ -
        ∫ q, ((N : ℝ) + 1)⁻¹ * ⟪q.1, q.2⟫ ∂((G d).prod (G d)))
      (Y := fun _ => (∫ q, ((N : ℝ) + 1)⁻¹ * ⟪q.1, q.2⟫ ∂((G d).prod (G d))) - c)
      (hRm.sub_const _).aestronglyMeasurable aestronglyMeasurable_const (hfix d)
      (integrable_const _)).1
    simpa only [sub_add_sub_cancel] using h
  have hmc : Measurable fun d => ∫ p, (((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ - c) ^ (2 * k)
      ∂((G d).prod (G d)) :=
    hmeas (fun _ p => (((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫ - c) ^ (2 * k))
      (((hRm.sub_const c).pow_const _).comp measurable_snd) hci
  have h := integral_integral_sub_pow_le' (P := cavLaw[N, M, r]) (G := fun d => (G d).prod (G d))
    (R := fun p : ℝ^(N + 1) × ℝ^(N + 1) => ((N : ℝ) + 1)⁻¹ * ⟪p.1, p.2⟫) hRm hk0 c hmc hfix
    (a := 48 * K₁₁ * (1 + R) * k / ((N : ℝ) + 1)) (b := K₁₇ * k / ((N : ℝ) + 1))
    (by positivity) (by positivity) h12.1 h12.2
    (by simpa only [hm] using h17'.1) (by simpa only [hm] using h17'.2)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  congr 1; ring

end SpinGlasses
