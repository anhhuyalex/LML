/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.Pi
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianMatrixNorm
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.GradientBound

/-!
# The Shcherbina--Tirozzi model: the overlaps are nearly constant

Averaged over the disorder, the Gibbs averages `⟨R_{1,1}⟩` and `⟨R_{1,2}⟩` concentrate at rate
`(K k / N)^k` (Talagrand, Proposition 3.1.17): they are Lipschitz with constant of order `1 / √N`
on a convex set of the disorder space carrying all but exponentially little Gaussian mass, and
Maurey's inequality applies to the Gaussian measure conditioned on that set. Combined with the
concentration under the Gibbs measure this gives Theorem 3.1.18 (and Theorem 3.1.1): for
`4 k ≤ N`, `ν ((R_{1,1} - ν R_{1,1}) ^ (2 k)) ≤ (K k / N) ^ k` and the same for `R_{1,2}`, where
`ν (f) = 𝔼 ⟨f⟩` and `K` depends only on `κ₀, h₀, D`.

## Main declarations

* `SpinGlasses.measurePreserving_stdGaussian_shcherbinaTirozziDisorder`: the disorder
  `(g, g₀)` as a standard Gaussian vector.
* `SpinGlasses.exists_integral_sub_integral_pow_le_of_disorder_gradient`: concentration of a
  function of the disorder with the growth and gradient bounds of the overlaps.
* `SpinGlasses.exists_integral_shcherbinaTirozzi_selfOverlap_sub_pow_le`: Eqs. (3.8), (3.57).
* `SpinGlasses.exists_integral_shcherbinaTirozzi_overlap_sub_pow_le`: Eqs. (3.9), (3.58).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Module Matrix
open scoped RealInnerProductSpace Real Matrix.Norms.L2Operator

namespace SpinGlasses

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {N M : ℕ}

/-- The standard Gaussian vector indexed by all the disorder variables has the law of the
independent standard Gaussians `(g, g₀)`. -/
theorem measurePreserving_stdGaussian_shcherbinaTirozziDisorder (N M : ℕ) :
    MeasurePreserving (fun ω : EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N) =>
        ((fun k i => ω (Sum.inl (k, i)), fun i => ω (Sum.inr i)) :
          (Fin M → Fin N → ℝ) × (Fin N → ℝ)))
      (stdGaussian (EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N)))
      ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1)) := by
  have h1 : MeasurePreserving
      (fun ω : EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N) => ω.ofLp)
      (stdGaussian (EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N)))
      (Measure.pi fun _ : (Fin M × Fin N) ⊕ Fin N => gaussianReal 0 1) :=
    ⟨WithLp.measurable_ofLp 2 _, pi_gaussianReal_eq_map_stdGaussian.symm⟩
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : (Fin M × Fin N) ⊕ Fin N => ℝ)
    fun _ => gaussianReal 0 1
  have h3 := (measurePreserving_curry_symm (X := ℝ)
    (fun (_ : Fin M) (_ : Fin N) => gaussianReal 0 1)).symm
    (MeasurableEquiv.curry (Fin M) (Fin N) ℝ).symm
  have h4 := (h3.prod (MeasurePreserving.id
    (Measure.pi fun _ : Fin N => gaussianReal 0 1))).comp (h2.comp h1)
  exact h4

/-- The good set of the disorder, where `B^* ≤ 768 N` and the operator norm of `g` is at most
`√(768 N)`, is convex, measurable, of positive Gaussian mass, and carries all but
`3 e^{-2N}` of the mass. -/
private theorem goodDisorderSet_props (hM : M ≤ 10 * N) (hN : 1 ≤ N)
    (C : Set (EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N)))
    (hC : C = {ω | (N : ℝ) + Real.sqrt (∑ k, ∑ i, ω (Sum.inl (k, i)) ^ 2) +
          ∑ i, ω (Sum.inr i) ^ 2 ≤ 768 * N ∧
        ‖Matrix.of fun k i => ω (Sum.inl (k, i))‖ ≤ Real.sqrt (768 * N)}) :
    Convex ℝ C ∧ MeasurableSet C ∧
      (stdGaussian (EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N))).real Cᶜ ≤
        3 * Real.exp (-(2 * N)) ∧
      0 < (stdGaussian (EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N))).real C := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set L : ℝ := 768 with hL
  set B : (Fin M → Fin N → ℝ) × (Fin N → ℝ) → ℝ := fun d =>
    N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2 with hB
  have hBm : Measurable B := by fun_prop
  set T : EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N) →
      (Fin M → Fin N → ℝ) × (Fin N → ℝ) := fun ω =>
    (fun k i => ω (Sum.inl (k, i)), fun i => ω (Sum.inr i)) with hT
  set P := (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
    (Measure.pi fun _ : Fin N => gaussianReal 0 1) with hP
  have hmp : MeasurePreserving T
      (stdGaussian (EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N))) P :=
    measurePreserving_stdGaussian_shcherbinaTirozziDisorder N M
  set γ := stdGaussian (EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N)) with hγ
  subst hC
  set C : Set (EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N)) :=
    {ω | B (T ω) ≤ L * N ∧ ‖Matrix.of (T ω).1‖ ≤ Real.sqrt (L * N)} with hC
  have hnc : Continuous fun ω : EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N) =>
      ‖Matrix.of (T ω).1‖ := by
    have h1 : Continuous fun ω : EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N) =>
        (Matrix.of (T ω).1 : Matrix (Fin M) (Fin N) ℝ) :=
      continuous_matrix fun k i =>
        PiLp.continuous_apply 2 (fun _ : (Fin M × Fin N) ⊕ Fin N => ℝ) (Sum.inl (k, i))
    exact continuous_norm.comp h1
  have hCm : MeasurableSet C :=
    (measurableSet_le (hBm.comp hmp.measurable) measurable_const).inter
      (measurableSet_le hnc.measurable measurable_const)
  have hCconv : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    have hTlin : T (a • x + b • y) = a • T x + b • T y := rfl
    refine ⟨?_, ?_⟩
    · have hflat : ∀ ω : EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N),
          Real.sqrt (∑ k, ∑ i, (T ω).1 k i ^ 2) =
            ‖(WithLp.toLp 2 fun p : Fin M × Fin N => (T ω).1 p.1 p.2)‖ := fun ω => by
        rw [EuclideanSpace.norm_eq, Fintype.sum_prod_type]
        simp only [Real.norm_eq_abs, sq_abs]
      have h1 : Real.sqrt (∑ k, ∑ i, (T (a • x + b • y)).1 k i ^ 2) ≤
          a * Real.sqrt (∑ k, ∑ i, (T x).1 k i ^ 2) +
            b * Real.sqrt (∑ k, ∑ i, (T y).1 k i ^ 2) := by
        rw [hflat, hflat, hflat]
        have e : (WithLp.toLp 2 fun p : Fin M × Fin N => (T (a • x + b • y)).1 p.1 p.2) =
            a • (WithLp.toLp 2 fun p : Fin M × Fin N => (T x).1 p.1 p.2) +
              b • (WithLp.toLp 2 fun p : Fin M × Fin N => (T y).1 p.1 p.2) := rfl
        rw [e]
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      have h2 : ∑ i, (T (a • x + b • y)).2 i ^ 2 ≤
          a * (∑ i, (T x).2 i ^ 2) + b * ∑ i, (T y).2 i ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun i _ => ?_
        have h := (even_two.convexOn_pow (𝕜 := ℝ)).2 (Set.mem_univ ((T x).2 i))
          (Set.mem_univ ((T y).2 i)) ha hb hab
        change (a * (T x).2 i + b * (T y).2 i) ^ 2 ≤ a * (T x).2 i ^ 2 + b * (T y).2 i ^ 2
        simpa only [smul_eq_mul] using h
      have hx1 := hx.1
      have hy1 := hy.1
      simp only [hB] at hx1 hy1 ⊢
      have h3 := mul_le_mul_of_nonneg_left hx1 ha
      have h4 := mul_le_mul_of_nonneg_left hy1 hb
      have h5 : a * (L * N) + b * (L * N) = L * N := by
        rw [← add_mul, hab, one_mul]
      have h6 : a * (N : ℝ) + b * N = N := by rw [← add_mul, hab, one_mul]
      linarith
    · have e : (Matrix.of (T (a • x + b • y)).1 : Matrix (Fin M) (Fin N) ℝ) =
          a • Matrix.of (T x).1 + b • Matrix.of (T y).1 := rfl
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      refine (add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
        (mul_le_mul_of_nonneg_left hy.2 hb)).trans_eq ?_
      rw [← add_mul, hab, one_mul]
  -- the complement of the good set is exponentially small
  have hbad : γ.real Cᶜ ≤ 3 * Real.exp (-(2 * N)) := by
    set S₁ : Set ((Fin M → Fin N → ℝ) × (Fin N → ℝ)) := {d | L * N ≤ B d} with hS₁
    set S₂ : Set (Fin M → Fin N → ℝ) := {g | Real.sqrt (L * N) < ‖Matrix.of g‖} with hS₂
    have hsub : Cᶜ ⊆ T ⁻¹' S₁ ∪ T ⁻¹' (S₂ ×ˢ Set.univ) := fun ω hω => by
      by_contra h
      rw [Set.mem_union, not_or] at h
      refine hω ⟨le_of_lt (not_le.1 h.1), le_of_not_gt fun hlt => h.2 ⟨hlt, Set.mem_univ _⟩⟩
    have h1 : P.real S₁ ≤ Real.exp (-(2 * N)) := by
      have h333 := integral_exp_shcherbinaTirozzi_radius_div_four_le (N := N) (M := M) hM
      rw [← hP] at h333
      have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P)
        (f := fun d => Real.exp (B d / 4)) (ae_of_all _ fun _ => (Real.exp_pos _).le) h333.1
        (Real.exp (L * N / 4))
      have h2 : P.real S₁ ≤ P.real {d | Real.exp (L * N / 4) ≤ Real.exp (B d / 4)} := by
        refine measureReal_mono (fun d (hd : L * N ≤ B d) => ?_) (measure_ne_top P _)
        exact Real.exp_le_exp.2 (div_le_div_of_nonneg_right hd (by norm_num))
      have h3 := (mul_le_mul_of_nonneg_left h2 (Real.exp_pos (L * N / 4)).le).trans
        (hmk.trans h333.2)
      refine le_of_mul_le_mul_left (h3.trans ?_) (Real.exp_pos (L * N / 4))
      rw [← Real.exp_add, Real.exp_le_exp, hL]
      linarith [Nat.cast_nonneg (α := ℝ) N]
    have h2 : P.real (S₂ ×ˢ Set.univ) ≤ 2 * Real.exp (-(2 * N)) := by
      rw [hP, measureReal_prod_prod, probReal_univ, mul_one]
      refine (measureReal_l2_opNorm_gaussian_gt_le (ι := Fin N) (κ := Fin M)
        (Real.sqrt_nonneg _)).trans ?_
      rw [Fintype.card_fin, Fintype.card_fin, Real.sq_sqrt (by rw [hL]; positivity), mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ zero_le_two
      have h5 : (5 : ℝ) ^ (N + M) ≤ Real.exp (22 * N) := by
        have h25 : (5 : ℝ) ≤ Real.exp 2 := by
          have := Real.quadratic_le_exp_of_nonneg (zero_le_two : (0 : ℝ) ≤ 2)
          linarith
        refine (pow_le_pow_left₀ (by norm_num) h25 _).trans ?_
        rw [← Real.exp_nat_mul, Real.exp_le_exp]
        have hMN : (M : ℝ) ≤ 10 * N := by exact_mod_cast hM
        push_cast
        linarith
      refine (mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le).trans ?_
      rw [← Real.exp_add, Real.exp_le_exp, hL]
      linarith
    have hS₁m : MeasurableSet S₁ := measurableSet_le measurable_const hBm
    have hS₂m : MeasurableSet S₂ := by
      have h1 : Continuous fun g : Fin M → Fin N → ℝ =>
          (Matrix.of g : Matrix (Fin M) (Fin N) ℝ) :=
        continuous_matrix fun k i => (continuous_apply i).comp (continuous_apply k)
      exact measurableSet_lt measurable_const (continuous_norm.comp h1).measurable
    have hpre : ∀ S : Set ((Fin M → Fin N → ℝ) × (Fin N → ℝ)), MeasurableSet S →
        γ.real (T ⁻¹' S) = P.real S := fun S hS => by
      rw [measureReal_def, measureReal_def, hmp.measure_preimage hS.nullMeasurableSet]
    calc γ.real Cᶜ ≤ γ.real (T ⁻¹' S₁ ∪ T ⁻¹' (S₂ ×ˢ Set.univ)) :=
          measureReal_mono hsub (measure_ne_top γ _)
      _ ≤ γ.real (T ⁻¹' S₁) + γ.real (T ⁻¹' (S₂ ×ˢ Set.univ)) := measureReal_union_le _ _
      _ ≤ 3 * Real.exp (-(2 * N)) := by
          rw [hpre S₁ hS₁m, hpre _ (hS₂m.prod MeasurableSet.univ)]
          linarith
  have hCpos : 0 < γ.real C := by
    have h1 : γ.real Cᶜ < 1 := by
      refine hbad.trans_lt ?_
      have h2 : Real.exp (-(2 * N)) ≤ Real.exp (-2) := by
        have : (1 : ℝ) ≤ N := by exact_mod_cast hN
        exact Real.exp_le_exp.2 (by linarith)
      have h3 : Real.exp (-2) < 1 / 3 := by
        rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
        have := Real.quadratic_le_exp_of_nonneg (zero_le_two : (0 : ℝ) ≤ 2)
        linarith
      linarith
    rw [probReal_compl_eq_one_sub hCm] at h1
    linarith
  exact ⟨hCconv, hCm, hbad, hCpos⟩


/-- Fourth-order moments around a centre: if `|f| ≤ K₉ B^* / N` and `|m| ≤ 768 K₉`, then for
`4 k ≤ N` the moment of order `4 k` of `f - m` is at most the square of `Q^{2k}`, where
`Q = 2 K₉ (40 + 768) + 1`. -/
private theorem integral_sub_pow_four_mul_le_of_disorder_growth {K₉ : ℝ} (hK₉ : 0 ≤ K₉) {k : ℕ}
    (hM : M ≤ 10 * N) (hN : 1 ≤ N) (hk0 : k ≠ 0) (hk : 4 * k ≤ N)
    {f : (Fin M → Fin N → ℝ) × (Fin N → ℝ) → ℝ} (hf : Measurable f)
    (hgrowth : ∀ d,
      |f d| ≤ K₉ * (N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) / N)
    {m : ℝ} (hmb : |m| ≤ K₉ * 768) :
    Integrable (fun d => (f d - m) ^ (4 * k))
        ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)) ∧
      ∫ d, (f d - m) ^ (4 * k) ∂((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N =>
          gaussianReal 0 1).prod (Measure.pi fun _ : Fin N => gaussianReal 0 1)) ≤
        ((2 * (K₉ * (40 + 768)) + 1) ^ (2 * k)) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set L : ℝ := 768 with hL
  set Q : ℝ := 2 * (K₉ * (40 + L)) + 1 with hQ
  set B : (Fin M → Fin N → ℝ) × (Fin N → ℝ) → ℝ := fun d =>
    N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2 with hB
  have hB0 : ∀ d, 0 ≤ B d := fun d =>
    add_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  set P := (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
    (Measure.pi fun _ : Fin N => gaussianReal 0 1) with hP
  have hKL : 0 ≤ K₉ * L := mul_nonneg hK₉ (by rw [hL]; norm_num)
  have hrad := integral_shcherbinaTirozzi_radius_pow_le (N := N) (M := M) hM hk
  have heven4 : Even (4 * k) := ⟨2 * k, by ring⟩
  have hpt4 : ∀ d, (f d - m) ^ (4 * k) ≤
      2 ^ (4 * k - 1) * ((K₉ / N) ^ (4 * k) * B d ^ (4 * k) + (K₉ * L) ^ (4 * k)) := fun d => by
    rw [← heven4.pow_abs]
    have h1 : |f d - m| ≤ K₉ / N * B d + K₉ * L := by
      refine (abs_sub _ _).trans (add_le_add ((hgrowth d).trans_eq ?_) hmb)
      rw [hB]; ring
    refine (pow_le_pow_left₀ (abs_nonneg _) h1 _).trans ?_
    rw [← mul_pow]
    exact add_pow_le (mul_nonneg (div_nonneg hK₉ hN0.le) (hB0 d)) hKL _
  have hdom4 : Integrable (fun d => 2 ^ (4 * k - 1) *
      ((K₉ / N) ^ (4 * k) * B d ^ (4 * k) + (K₉ * L) ^ (4 * k))) P :=
    ((hrad.1.const_mul _).add (integrable_const _)).const_mul _
  have hi4 : Integrable (fun d => (f d - m) ^ (4 * k)) P :=
    Integrable.mono' hdom4 ((hf.sub_const m).pow_const _).aestronglyMeasurable
      (ae_of_all _ fun d => by
        rw [Real.norm_of_nonneg (heven4.pow_nonneg _)]
        exact hpt4 d)
  refine ⟨hi4, ?_⟩
  refine (integral_mono hi4 hdom4 hpt4).trans ?_
  rw [integral_const_mul, integral_add (hrad.1.const_mul _) (integrable_const _),
    integral_const_mul, integral_const, probReal_univ, one_smul, ← pow_mul,
    show 2 * k * 2 = 4 * k by ring]
  have h1 : (K₉ / N) ^ (4 * k) * ∫ d, B d ^ (4 * k) ∂P ≤ (40 * K₉) ^ (4 * k) := by
    refine (mul_le_mul_of_nonneg_left hrad.2 (pow_nonneg (div_nonneg hK₉ hN0.le) _)).trans_eq ?_
    rw [← mul_pow]
    congr 1
    field_simp
  have h2 : (40 * K₉) ^ (4 * k) + (K₉ * L) ^ (4 * k) ≤ (K₉ * (40 + L)) ^ (4 * k) := by
    refine (pow_add_pow_le (mul_nonneg (by norm_num) hK₉) hKL (by omega)).trans_eq ?_
    ring
  refine (mul_le_mul_of_nonneg_left ((add_le_add h1 le_rfl).trans h2) (by positivity)).trans ?_
  have h3 : (2 : ℝ) ^ (4 * k - 1) ≤ 2 ^ (4 * k) := pow_le_pow_right₀ one_le_two (by omega)
  refine (mul_le_mul_of_nonneg_right h3
    (pow_nonneg (mul_nonneg hK₉ (by rw [hL]; norm_num)) _)).trans ?_
  rw [← mul_pow]
  refine pow_le_pow_left₀ (mul_nonneg zero_le_two (mul_nonneg hK₉ (by rw [hL]; norm_num))) ?_ _
  rw [hQ]; linarith


/-- **Concentration of a function of the disorder.** Suppose `|f| ≤ K₉ B^* / N` and that along
every line of the disorder the derivative `f'` of `f` satisfies
`f'² ≤ K₁₆ (B^* / N² + B^{*2} ‖g‖² / N⁴) ‖(Δ, Δ₀)‖²`. Then for `4 k ≤ N`,
`𝔼 (f - 𝔼 f) ^ (2 k) ≤ (K k / N) ^ k`, with `K` depending only on `K₉, K₁₆`. This is the proof
of Talagrand's Proposition 3.1.17. -/
theorem exists_integral_sub_integral_pow_le_of_disorder_gradient (K₉ K₁₆ : ℝ) (hK₉ : 0 ≤ K₉)
    (hK₁₆ : 0 ≤ K₁₆) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M k : ℕ), M ≤ 10 * N → 1 ≤ N → 4 * k ≤ N →
      ∀ f : (Fin M → Fin N → ℝ) × (Fin N → ℝ) → ℝ, Measurable f →
      (∀ d, |f d| ≤ K₉ * (N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) / N) →
      (∀ d Δ : (Fin M → Fin N → ℝ) × (Fin N → ℝ), ∃ f' : ℝ,
        HasDerivAt (fun t : ℝ => f (d + t • Δ)) f' 0 ∧
        f' ^ 2 ≤ K₁₆ * ((N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) / (N : ℝ) ^ 2 +
          (N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) ^ 2 * ‖Matrix.of d.1‖ ^ 2 /
            (N : ℝ) ^ 4) * ((∑ k, ∑ i, Δ.1 k i ^ 2) + ∑ i, Δ.2 i ^ 2)) →
      ∀ P : Measure ((Fin M → Fin N → ℝ) × (Fin N → ℝ)),
      P = (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1) →
      Integrable (fun d => (f d - ∫ e, f e ∂P) ^ (2 * k)) P ∧
        ∫ d, (f d - ∫ e, f e ∂P) ^ (2 * k) ∂P ≤ (K * k / N) ^ k := by
  set L : ℝ := 768 with hL
  set Q : ℝ := 2 * (K₉ * (40 + L)) + 1 with hQ
  have hQ1 : 1 ≤ Q := by
    have : 0 ≤ K₉ * (40 + L) := mul_nonneg hK₉ (by rw [hL]; norm_num)
    rw [hQ]; linarith
  set Kg : ℝ := K₁₆ * (L + L ^ 3) with hKg
  have hKg0 : 0 ≤ Kg := mul_nonneg hK₁₆ (by rw [hL]; norm_num)
  refine ⟨4 * (64 * Kg + 2 * Q ^ 2), by positivity,
    fun N M k hM hN hk f hf hgrowth hgrad P hP => ?_⟩
  have : IsProbabilityMeasure P := by rw [hP]; infer_instance
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have heven : Even (2 * k) := even_two_mul k
  set B : (Fin M → Fin N → ℝ) × (Fin N → ℝ) → ℝ := fun d =>
    N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2 with hB
  have hBm : Measurable B := by fun_prop
  have hB0 : ∀ d, 0 ≤ B d := fun d =>
    add_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  set T : EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N) →
      (Fin M → Fin N → ℝ) × (Fin N → ℝ) := fun ω =>
    (fun k i => ω (Sum.inl (k, i)), fun i => ω (Sum.inr i)) with hT
  have hmp : MeasurePreserving T
      (stdGaussian (EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N))) P := by
    rw [hP]; exact measurePreserving_stdGaussian_shcherbinaTirozziDisorder N M
  set γ := stdGaussian (EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N)) with hγ
  have htrans : ∀ F : (Fin M → Fin N → ℝ) × (Fin N → ℝ) → ℝ, Measurable F →
      ∫ ω, F (T ω) ∂γ = ∫ d, F d ∂P := fun F hF => by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable hF.aestronglyMeasurable]
  -- the good set of the disorder
  set C : Set (EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N)) :=
    {ω | B (T ω) ≤ L * N ∧ ‖Matrix.of (T ω).1‖ ≤ Real.sqrt (L * N)} with hC
  obtain ⟨hCconv, hCm, hbad, hCpos⟩ : Convex ℝ C ∧ MeasurableSet C ∧
      γ.real Cᶜ ≤ 3 * Real.exp (-(2 * N)) ∧ 0 < γ.real C :=
    goodDisorderSet_props hM hN C rfl
  have hbad2 : γ.real Cᶜ ≤ (2 * Real.exp (-N)) ^ 2 := by
    refine hbad.trans ?_
    have e : (2 * Real.exp (-N)) ^ 2 = 4 * Real.exp (-(2 * N)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 1
      · norm_num
      · congr 1; push_cast; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
  have hCvol : volume C ≠ 0 := fun h0 => by
    have h1 : γ C = 0 := by
      have hac : γ ≪ volume := by
        rw [hγ, stdGaussian_eq_withDensity]
        exact withDensity_absolutelyContinuous _ _
      exact hac h0
    rw [measureReal_def, h1] at hCpos
    simp at hCpos
  -- Lipschitz continuity on the good set
  set A : ℝ := Real.sqrt (Kg / N) with hA
  have hA2 : A ^ 2 = Kg / N := by rw [hA, Real.sq_sqrt (div_nonneg hKg0 hN0.le)]
  have hlip : ∀ x ∈ C, ∀ y ∈ C, |f (T x) - f (T y)| ≤ A * ‖x - y‖ := by
    intro x hx y hy
    have hδ : (∑ k, ∑ i, (T y - T x).1 k i ^ 2) + ∑ i, (T y - T x).2 i ^ 2 = ‖x - y‖ ^ 2 := by
      rw [norm_sub_rev, EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type,
        Fintype.sum_prod_type]
      rfl
    rw [abs_sub_comm]
    refine hCconv.norm_sub_le_of_forall_hasDerivAt_line (g := fun ω => f (T ω)) hx hy
      fun z hz => ?_
    obtain ⟨d, hd, hdb⟩ := hgrad (T z) (T y - T x)
    refine ⟨d, hd, abs_le_of_sq_le_sq ?_ (by positivity)⟩
    rw [mul_pow, hA2]
    refine hdb.trans ?_
    rw [hδ]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hB1 : B (T z) ≤ L * N := hz.1
    have hn1 : ‖Matrix.of (T z).1‖ ^ 2 ≤ L * N := by
      have h := pow_le_pow_left₀ (norm_nonneg _)
        (show ‖Matrix.of (T z).1‖ ≤ Real.sqrt (L * N) from hz.2) 2
      rwa [Real.sq_sqrt (by rw [hL]; positivity)] at h
    have h2 : B (T z) / (N : ℝ) ^ 2 + B (T z) ^ 2 * ‖Matrix.of (T z).1‖ ^ 2 / (N : ℝ) ^ 4 ≤
        (L + L ^ 3) / N := by
      have h3 : B (T z) / (N : ℝ) ^ 2 ≤ L / N := by
        refine (div_le_div_of_nonneg_right hB1 (by positivity)).trans_eq ?_
        field_simp
      have h4 : B (T z) ^ 2 * ‖Matrix.of (T z).1‖ ^ 2 / (N : ℝ) ^ 4 ≤ L ^ 3 / N := by
        refine (div_le_div_of_nonneg_right (mul_le_mul
          (pow_le_pow_left₀ (hB0 _) hB1 2) hn1 (sq_nonneg _) (sq_nonneg _))
          (by positivity)).trans_eq ?_
        field_simp
      rw [add_div L]
      exact add_le_add h3 h4
    refine (mul_le_mul_of_nonneg_left h2 hK₁₆).trans_eq ?_
    rw [hKg]; ring
  -- Maurey's inequality for the conditioned Gaussian measure
  set γ' := (volume.restrict C).tilted
    (fun ω : EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N) => -(‖ω‖ ^ 2 / 2)) with hγ'
  have hint : IntegrableOn (fun ω : EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N) =>
      Real.exp (-(‖ω‖ ^ 2 / 2))) C volume := by
    have h := integrable_exp_neg_mul_sq_norm_add_inner
      (E := EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N)) (by norm_num : (0 : ℝ) < 1 / 2) 0
    refine (h.congr (ae_of_all _ fun ω => ?_)).integrableOn
    simp only [inner_zero_left, add_zero]
    congr 1; ring
  have hfT : Measurable fun ω => f (T ω) := hf.comp hmp.measurable
  have hmid : ∀ x ∈ C, ∀ y ∈ C, (1 / 2 : ℝ) * ‖(1 / 2 : ℝ) • (x - y)‖ ^ 2 ≤
      (‖x‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2) / 2 - ‖(1 / 2 : ℝ) • (x + y)‖ ^ 2 / 2 := fun x _ y _ => by
    have := parallelogram_law_with_norm ℝ x y
    simp only [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_pow]
    nlinarith
  have hMau := integral_sub_integral_pow_le_of_lipschitz (μ₀ := volume) (C := C)
    (H := fun ω => ‖ω‖ ^ 2 / 2) (κ := 1 / 2) hCconv hCm hCvol
    ((measurable_norm.pow_const 2).div_const 2) hint hmid (by norm_num) hfT
    (Real.sqrt_nonneg _) hlip k
  rw [← hγ', ← hA] at hMau
  have hprob' : IsProbabilityMeasure γ' :=
    isProbabilityMeasure_tilted_restrict (H := fun ω => ‖ω‖ ^ 2 / 2) hCvol hint
  set m : ℝ := ∫ ω, f (T ω) ∂γ' with hm
  have hfC : ∀ ω ∈ C, |f (T ω)| ≤ K₉ * L := fun ω hω => by
    refine (hgrowth (T ω)).trans ?_
    rw [div_le_iff₀ hN0, mul_assoc]
    exact mul_le_mul_of_nonneg_left hω.1 hK₉
  have hmb : |m| ≤ K₉ * L := by
    have h := norm_integral_le_of_norm_le_const (μ := γ') (f := fun ω => f (T ω))
      (C := K₉ * L) ((ae_mem_of_tilted_restrict (μ₀ := volume)
        (H := fun ω => ‖ω‖ ^ 2 / 2) hCm).mono fun ω hω => by
          simpa only [Real.norm_eq_abs] using hfC ω hω)
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h
  -- fourth-order moments from Lemma 3.1.10
  obtain ⟨hi4, hI4⟩ : Integrable (fun d => (f d - m) ^ (4 * k)) P ∧
      ∫ d, (f d - m) ^ (4 * k) ∂P ≤ (Q ^ (2 * k)) ^ 2 := by
    rw [hP, hQ, hL]
    exact integral_sub_pow_four_mul_le_of_disorder_growth hK₉ hM hN hk0 hk hf hgrowth
      (by rw [← hL]; exact hmb)
  have hi2 : Integrable (fun d => (f d - m) ^ (2 * k)) P := by
    refine Integrable.mono' (hi4.add (integrable_const 1))
      ((hf.sub_const m).pow_const _).aestronglyMeasurable (ae_of_all _ fun d => ?_)
    rw [Real.norm_of_nonneg (heven.pow_nonneg _), Pi.add_apply,
      show 4 * k = 2 * k * 2 by ring, pow_mul (f d - m) (2 * k) 2]
    nlinarith [sq_nonneg ((f d - m) ^ (2 * k) - 1), heven.pow_nonneg (f d - m)]
  -- split along the good set
  have hiγ : ∀ n : ℕ, Integrable (fun d => (f d - m) ^ n) P →
      Integrable (fun ω => (f (T ω) - m) ^ n) γ := fun n h =>
    (hmp.integrable_comp ((hf.sub_const m).pow_const _).aestronglyMeasurable).2 h
  have hgood : ∫ ω in C, (f (T ω) - m) ^ (2 * k) ∂γ ≤ 4 * (16 * k * A ^ 2) ^ k := by
    have h := integral_tilted_restrict_neg_half_sq_norm hCm
      (fun ω : EuclideanSpace ℝ ((Fin M × Fin N) ⊕ Fin N) => (f (T ω) - m) ^ (2 * k))
    rw [← hγ', ← hγ] at h
    have h1 : ∫ ω in C, (f (T ω) - m) ^ (2 * k) ∂γ =
        γ.real C * ∫ ω, (f (T ω) - m) ^ (2 * k) ∂γ' := by
      rw [h, mul_div_cancel₀ _ hCpos.ne']
    rw [h1]
    refine (mul_le_of_le_one_left (integral_nonneg fun _ => heven.pow_nonneg _)
      measureReal_le_one).trans (hMau.2.trans_eq ?_)
    congr 2
    ring
  have hfar : ∫ ω in Cᶜ, (f (T ω) - m) ^ (2 * k) ∂γ ≤ 2 * Real.exp (-N) * Q ^ (2 * k) := by
    have h2 : MemLp (fun ω => (f (T ω) - m) ^ (2 * k)) 2 γ := by
      refine (memLp_two_iff_integrable_sq ((hfT.sub_const m).pow_const _).aestronglyMeasurable).2
        ?_
      simp_rw [← pow_mul, show 2 * k * 2 = 4 * k by ring]
      exact hiγ _ hi4
    refine (Real.le_norm_self _).trans (norm_setIntegral_le_mul_of_integral_sq_le hCm.compl
      (measure_ne_top _ _) h2 (by positivity) (pow_nonneg (zero_le_one.trans hQ1) _) hbad2 ?_)
    simp_rw [Real.norm_eq_abs, sq_abs, ← pow_mul, show 2 * k * 2 = 4 * k by ring]
    rw [htrans (fun d => (f d - m) ^ (4 * k)) ((hf.sub_const m).pow_const _)]
    exact hI4.trans_eq (by rw [← pow_mul, show 2 * k * 2 = 4 * k by ring])
  have hmed : ∫ d, (f d - m) ^ (2 * k) ∂P ≤ ((64 * Kg + 2 * Q ^ 2) * k / N) ^ k := by
    rw [← htrans (fun d => (f d - m) ^ (2 * k)) ((hf.sub_const m).pow_const _),
      ← integral_add_compl hCm (hiγ _ hi2)]
    set x : ℝ := 16 * k * A ^ 2 with hx
    set y : ℝ := Q ^ 2 * k / N with hy
    have hx0 : 0 ≤ x := by positivity
    have hy0 : 0 ≤ y := by positivity
    have h1 : 2 * Real.exp (-N) * Q ^ (2 * k) ≤ 2 * y ^ k := by
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ zero_le_two
      refine (mul_le_mul_of_nonneg_right (Real.exp_neg_le_natCast_div_pow hN0 k)
        (pow_nonneg (zero_le_one.trans hQ1) _)).trans_eq ?_
      rw [pow_mul, ← mul_pow, hy]
      congr 1
      ring
    have h4 : 4 * x ^ k ≤ (4 * x) ^ k := by
      rw [mul_pow (4 : ℝ) x]
      exact mul_le_mul_of_nonneg_right (le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 4) hk0)
        (pow_nonneg hx0 _)
    have h2 : 2 * y ^ k ≤ (2 * y) ^ k := by
      rw [mul_pow (2 : ℝ) y]
      exact mul_le_mul_of_nonneg_right (le_self_pow₀ one_le_two hk0) (pow_nonneg hy0 _)
    refine (add_le_add (hgood.trans h4) (hfar.trans (h1.trans h2))).trans ?_
    refine (pow_add_pow_le (by positivity) (by positivity) hk0).trans_eq ?_
    rw [hx, hy, hA2]
    congr 1
    ring
  have hsym := integral_sub_integral_pow_two_mul_le (μ := P) (f := f) (m := m) (k := k)
    hf.aestronglyMeasurable hi2
  refine ⟨hsym.1, hsym.2.trans ?_⟩
  refine (mul_le_mul_of_nonneg_left hmed (by positivity)).trans_eq ?_
  rw [pow_mul, ← mul_pow]
  congr 1
  ring


/-- **Combining the two concentrations.** If the Gibbs fluctuations `𝔼⟨(R - ⟨R⟩)^{2k}⟩` are at
most `a ^ k` and the disorder fluctuations `𝔼 (⟨R⟩ - 𝔼⟨R⟩)^{2k}` at most `b ^ k`, then
`𝔼⟨(R - 𝔼⟨R⟩)^{2k}⟩ ≤ (4 (a + b)) ^ k`. -/
private theorem integral_integral_sub_pow_le {Ω α : Type*} [MeasurableSpace Ω]
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

/-- **Theorem 3.1.18 (Theorem 3.1.1) for `R_{1,1}`, Eqs. (3.8), (3.57):** for `4 k ≤ N`,
`ν ((R_{1,1} - ν (R_{1,1})) ^ (2 k)) ≤ (K k / N) ^ k`, where `ν f = 𝔼 ⟨f⟩` and `K` depends only
on `κ₀, h₀, D`. -/
theorem exists_integral_shcherbinaTirozzi_selfOverlap_sub_pow_le (κ₀ h₀ D : ℝ) (hκ₀ : 0 < κ₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M k : ℕ) (κ h : ℝ) (u : ℝ → ℝ), κ₀ ≤ κ → 0 ≤ h → h ≤ h₀ →
      M ≤ 10 * N → 1 ≤ N → 4 * k ≤ N → ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) →
      (∀ x, -D * (1 + |x|) ≤ u x) → Differentiable ℝ u → Differentiable ℝ (deriv u) →
      (∀ x, |deriv u x| ≤ D) → (∀ x, |deriv (deriv u) x| ≤ D) →
      ∀ G : (Fin M → Fin N → ℝ) × (Fin N → ℝ) → Measure (ℝ^N),
        (∀ d, G d = volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u d.1 d.2 σ) →
        ∀ P : Measure ((Fin M → Fin N → ℝ) × (Fin N → ℝ)),
        P = (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1) →
        Integrable (fun d => ∫ σ, ((N : ℝ)⁻¹ * ‖σ‖ ^ 2 -
              ∫ e, ∫ τ, (N : ℝ)⁻¹ * ‖τ‖ ^ 2 ∂(G e) ∂P) ^ (2 * k) ∂(G d)) P ∧
          ∫ d, ∫ σ, ((N : ℝ)⁻¹ * ‖σ‖ ^ 2 -
              ∫ e, ∫ τ, (N : ℝ)⁻¹ * ‖τ‖ ^ 2 ∂(G e) ∂P) ^ (2 * k) ∂(G d) ∂P ≤
            (K * k / N) ^ k := by
  obtain ⟨K₉, hK₉, h319⟩ := exists_integral_sq_norm_pow_shcherbinaTirozziGibbs_le κ₀ h₀ D hκ₀
  obtain ⟨K₁₆, hK₁₆, h316⟩ :=
    exists_hasDerivAt_integral_shcherbinaTirozzi_selfOverlap_line κ₀ h₀ D hκ₀
  obtain ⟨K₁₇, hK₁₇, h317⟩ :=
    exists_integral_sub_integral_pow_le_of_disorder_gradient K₉ K₁₆ hK₉ hK₁₆
  obtain ⟨K₁₂, hK₁₂, h312⟩ :=
    exists_integral_integral_shcherbinaTirozzi_selfOverlap_sub_mean_pow_le κ₀ h₀ D hκ₀
  obtain ⟨K₁₁, -, h335⟩ :=
    exists_integral_shcherbinaTirozzi_selfOverlap_sub_mean_pow_le κ₀ h₀ D hκ₀
  refine ⟨4 * (K₁₂ + K₁₇), by positivity, fun N M k κ h u hκ hh0 hh hM hN hk hu hu0 hD hud hu'
    hD1 hD2 G hG P hP => ?_⟩
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum := hu.measurable_of_univ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have hprob : ∀ d, IsProbabilityMeasure (G d) := fun d => by
    rw [hG d]
    exact isProbabilityMeasure_shcherbinaTirozziGibbs hκ0 hum hu0 d.1 d.2
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  have hkN : k ≤ N := by omega
  have hE : Measurable fun p : ((Fin M → Fin N → ℝ) × (Fin N → ℝ)) ×
      ℝ^N => -shcherbinaTirozziHamiltonian κ h u p.1.1 p.1.2 p.2 :=
    (measurable_shcherbinaTirozziHamiltonian κ h hum).neg
  have hRm : Measurable fun σ : ℝ^N => (N : ℝ)⁻¹ * ‖σ‖ ^ 2 := by fun_prop
  obtain ⟨m, hm⟩ : ∃ m : (Fin M → Fin N → ℝ) × (Fin N → ℝ) → ℝ, ∀ d,
      ∫ τ, (N : ℝ)⁻¹ * ‖τ‖ ^ 2 ∂(G d) = m d := ⟨_, fun _ => rfl⟩
  have hmm : Measurable m := by
    have h : Measurable fun d => ∫ τ, (N : ℝ)⁻¹ * ‖τ‖ ^ 2 ∂(G d) := by
      simp_rw [hG]
      exact measurable_integral_tilted hE hRm
    exact (funext hm) ▸ h
  have hgrowth : ∀ d, |m d| ≤
      K₉ * (N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) / N := fun d => by
    have h1 := (h319 N M 1 κ h u d.1 d.2 hκ hh0 hh hM (by omega) hum hu0 hD).2
    rw [← hG d] at h1
    simp only [mul_one, pow_one] at h1
    rw [← hm, abs_of_nonneg (integral_nonneg fun τ =>
      mul_nonneg (inv_nonneg.2 hN0.le) (sq_nonneg _)), integral_const_mul, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hN0.le)
  have hgrad : ∀ d Δ : (Fin M → Fin N → ℝ) × (Fin N → ℝ), ∃ f' : ℝ,
      HasDerivAt (fun t : ℝ => m (d + t • Δ)) f' 0 ∧
      f' ^ 2 ≤ K₁₆ * ((N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) / (N : ℝ) ^ 2 +
        (N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) ^ 2 * ‖Matrix.of d.1‖ ^ 2 /
          (N : ℝ) ^ 4) * ((∑ k, ∑ i, Δ.1 k i ^ 2) + ∑ i, Δ.2 i ^ 2) := fun d Δ => by
    obtain ⟨f', hf', hb⟩ := h316 N M κ h u d.1 Δ.1 d.2 Δ.2 hκ hh0 hh hM hN hu hu0 hD hud hu'
      hD1 hD2
    refine ⟨f', hf'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_), hb⟩
    refine (hm _).symm.trans ?_
    rw [hG]
    rfl
  have h17 := h317 N M k hM hN hk m hmm hgrowth hgrad P hP
  have h12 := h312 N M k κ h u hκ hh0 hh hM hN hkN hu hu0 hD G hG P hP
  have hfix : ∀ d, Integrable (fun σ => ((N : ℝ)⁻¹ * ‖σ‖ ^ 2 -
      ∫ τ, (N : ℝ)⁻¹ * ‖τ‖ ^ 2 ∂(G d)) ^ (2 * k)) (G d) := fun d =>
    (h335 N M k κ h u d.1 d.2 hκ hh0 hh hM hN hkN hu hu0 hD (G d) (hG d)).1
  set c : ℝ := ∫ e, ∫ τ, (N : ℝ)⁻¹ * ‖τ‖ ^ 2 ∂(G e) ∂P with hc
  have hcm : c = ∫ e, m e ∂P := by rw [hc]; simp only [hm]
  have hmc : Measurable fun d => ∫ σ, ((N : ℝ)⁻¹ * ‖σ‖ ^ 2 - c) ^ (2 * k) ∂(G d) := by
    simp_rw [hG]
    exact measurable_integral_tilted hE ((hRm.sub_const c).pow_const _)
  have h := integral_integral_sub_pow_le (P := P) (G := G)
    (R := fun σ : ℝ^N => (N : ℝ)⁻¹ * ‖σ‖ ^ 2) hRm hk0 c hmc hfix
    (a := K₁₂ * k / N) (b := K₁₇ * k / N) (by positivity) (by positivity) h12.1 h12.2
    (by simpa only [hm, hcm] using h17.1) (by simpa only [hm, hcm] using h17.2)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  congr 1
  ring

/-- **Theorem 3.1.18 (Theorem 3.1.1) for `R_{1,2}`, Eqs. (3.9), (3.58):** for `4 k ≤ N`,
`ν ((R_{1,2} - ν (R_{1,2})) ^ (2 k)) ≤ (K k / N) ^ k`, where `ν f = 𝔼 ⟨f⟩` and `K` depends only
on `κ₀, h₀, D`. -/
theorem exists_integral_shcherbinaTirozzi_overlap_sub_pow_le (κ₀ h₀ D : ℝ) (hκ₀ : 0 < κ₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M k : ℕ) (κ h : ℝ) (u : ℝ → ℝ), κ₀ ≤ κ → 0 ≤ h → h ≤ h₀ →
      M ≤ 10 * N → 1 ≤ N → 4 * k ≤ N → ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) →
      (∀ x, -D * (1 + |x|) ≤ u x) → Differentiable ℝ u → Differentiable ℝ (deriv u) →
      (∀ x, |deriv u x| ≤ D) → (∀ x, |deriv (deriv u) x| ≤ D) →
      ∀ G : (Fin M → Fin N → ℝ) × (Fin N → ℝ) → Measure (ℝ^N),
        (∀ d, G d = volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u d.1 d.2 σ) →
        ∀ P : Measure ((Fin M → Fin N → ℝ) × (Fin N → ℝ)),
        P = (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1) →
        Integrable (fun d => ∫ p, ((N : ℝ)⁻¹ * ⟪p.1, p.2⟫ -
              ∫ e, ∫ q, (N : ℝ)⁻¹ * ⟪q.1, q.2⟫ ∂((G e).prod (G e)) ∂P) ^ (2 * k)
              ∂((G d).prod (G d))) P ∧
          ∫ d, ∫ p, ((N : ℝ)⁻¹ * ⟪p.1, p.2⟫ -
              ∫ e, ∫ q, (N : ℝ)⁻¹ * ⟪q.1, q.2⟫ ∂((G e).prod (G e)) ∂P) ^ (2 * k)
              ∂((G d).prod (G d)) ∂P ≤ (K * k / N) ^ k := by
  obtain ⟨K₉, hK₉, h319⟩ := exists_integral_sq_norm_pow_shcherbinaTirozziGibbs_le κ₀ h₀ D hκ₀
  obtain ⟨K₁₆, hK₁₆, h316⟩ :=
    exists_hasDerivAt_integral_shcherbinaTirozzi_overlap_line κ₀ h₀ D hκ₀
  obtain ⟨K₁₇, hK₁₇, h317⟩ :=
    exists_integral_sub_integral_pow_le_of_disorder_gradient K₉ K₁₆ hK₉ hK₁₆
  obtain ⟨K₁₂, hK₁₂, h312⟩ :=
    exists_integral_integral_shcherbinaTirozzi_overlap_sub_mean_pow_le κ₀ h₀ D hκ₀
  obtain ⟨K₁₁, -, h334⟩ := exists_integral_shcherbinaTirozzi_overlap_sub_mean_pow_le κ₀ h₀ D hκ₀
  refine ⟨4 * (K₁₂ + K₁₇), by positivity, fun N M k κ h u hκ hh0 hh hM hN hk hu hu0 hD hud hu'
    hD1 hD2 G hG P hP => ?_⟩
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum := hu.measurable_of_univ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have hprob : ∀ d, IsProbabilityMeasure (G d) := fun d => by
    rw [hG d]
    exact isProbabilityMeasure_shcherbinaTirozziGibbs hκ0 hum hu0 d.1 d.2
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  have hkN : k ≤ N := by omega
  have hE : Measurable fun p : ((Fin M → Fin N → ℝ) × (Fin N → ℝ)) ×
      ℝ^N => -shcherbinaTirozziHamiltonian κ h u p.1.1 p.1.2 p.2 :=
    (measurable_shcherbinaTirozziHamiltonian κ h hum).neg
  have hRm : Measurable fun p : ℝ^N × ℝ^N =>
      (N : ℝ)⁻¹ * ⟪p.1, p.2⟫ := by fun_prop
  have hnorm : ∀ d, MemLp (fun σ : ℝ^N => σ) 2 (G d) := fun d => by
    rw [hG d]; exact memLp_id_shcherbinaTirozziGibbs hκ0 hum hu0 d.1 d.2
  have hbary : ∀ d, ∫ q, (N : ℝ)⁻¹ * ⟪q.1, q.2⟫ ∂((G d).prod (G d)) =
      (N : ℝ)⁻¹ * ‖∫ σ, σ ∂(G d)‖ ^ 2 := fun d => by
    have h1 := (hnorm d).integrable one_le_two
    rw [integral_const_mul, ← real_inner_self_eq_norm_sq]
    exact congrArg _ (integral_prod_bilin (innerSL ℝ) h1 h1)
  have hmeas : ∀ F : ℝ^N × ℝ^N → ℝ, Measurable F →
      (∀ d, Integrable F ((G d).prod (G d))) →
      Measurable fun d => ∫ p, F p ∂((G d).prod (G d)) := fun F hF hFi => by
    simp only [hG] at hFi ⊢
    exact measurable_integral_prod_tilted_dep hE (F := fun _ => F) (hF.comp measurable_snd) hFi
  have hRi : ∀ d, Integrable (fun p : ℝ^N × ℝ^N =>
      (N : ℝ)⁻¹ * ⟪p.1, p.2⟫) ((G d).prod (G d)) := fun d =>
    have h1 := (hnorm d).integrable one_le_two
    (h1.inner_fst_snd h1).const_mul _
  obtain ⟨m, hm⟩ : ∃ m : (Fin M → Fin N → ℝ) × (Fin N → ℝ) → ℝ, ∀ d,
      ∫ q, (N : ℝ)⁻¹ * ⟪q.1, q.2⟫ ∂((G d).prod (G d)) = m d := ⟨_, fun _ => rfl⟩
  have hmm : Measurable m := (funext hm) ▸ hmeas _ hRm hRi
  have hgrowth : ∀ d, |m d| ≤
      K₉ * (N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) / N := fun d => by
    have h1 := (h319 N M 1 κ h u d.1 d.2 hκ hh0 hh hM (by omega) hum hu0 hD).2
    rw [← hG d] at h1
    simp only [mul_one, pow_one] at h1
    rw [← hm, hbary, abs_of_nonneg (mul_nonneg (inv_nonneg.2 hN0.le) (sq_nonneg _)),
      div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left
      ((sq_norm_integral_le_integral_sq_norm (hnorm d)).trans h1) (inv_nonneg.2 hN0.le)
  have hgrad : ∀ d Δ : (Fin M → Fin N → ℝ) × (Fin N → ℝ), ∃ f' : ℝ,
      HasDerivAt (fun t : ℝ => m (d + t • Δ)) f' 0 ∧
      f' ^ 2 ≤ K₁₆ * ((N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) / (N : ℝ) ^ 2 +
        (N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) ^ 2 * ‖Matrix.of d.1‖ ^ 2 /
          (N : ℝ) ^ 4) * ((∑ k, ∑ i, Δ.1 k i ^ 2) + ∑ i, Δ.2 i ^ 2) := fun d Δ => by
    obtain ⟨f', hf', hb⟩ := h316 N M κ h u d.1 Δ.1 d.2 Δ.2 hκ hh0 hh hM hN hu hu0 hD hud hu'
      hD1 hD2 (fun t => G (d + t • Δ)) fun t => by rw [hG]; rfl
    exact ⟨f', hf'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (hm _).symm), hb⟩
  have h17 := h317 N M k hM hN hk m hmm hgrowth hgrad P hP
  have h12 := h312 N M k κ h u hκ hh0 hh hM hN hkN hu hu0 hD G hG P hP
  have hfix : ∀ d, Integrable (fun p : ℝ^N × ℝ^N =>
      ((N : ℝ)⁻¹ * ⟪p.1, p.2⟫ - ∫ q, (N : ℝ)⁻¹ * ⟪q.1, q.2⟫ ∂((G d).prod (G d))) ^ (2 * k))
      ((G d).prod (G d)) := fun d =>
    (h334 N M k κ h u d.1 d.2 hκ hh0 hh hM hN hkN hu hu0 hD (G d) (hG d)).1
  set c : ℝ := ∫ e, ∫ q, (N : ℝ)⁻¹ * ⟪q.1, q.2⟫ ∂((G e).prod (G e)) ∂P with hc
  have hcm : c = ∫ e, m e ∂P := by rw [hc]; simp only [hm]
  have hci : ∀ d, Integrable (fun p : ℝ^N × ℝ^N =>
      ((N : ℝ)⁻¹ * ⟪p.1, p.2⟫ - c) ^ (2 * k)) ((G d).prod (G d)) := fun d => by
    have h := (integral_add_pow_two_mul_le (μ := (G d).prod (G d))
      (X := fun p => (N : ℝ)⁻¹ * ⟪p.1, p.2⟫ -
        ∫ q, (N : ℝ)⁻¹ * ⟪q.1, q.2⟫ ∂((G d).prod (G d)))
      (Y := fun _ => (∫ q, (N : ℝ)⁻¹ * ⟪q.1, q.2⟫ ∂((G d).prod (G d))) - c)
      (hRm.sub_const _).aestronglyMeasurable aestronglyMeasurable_const (hfix d)
      (integrable_const _)).1
    simpa only [sub_add_sub_cancel] using h
  have hmc : Measurable fun d => ∫ p, ((N : ℝ)⁻¹ * ⟪p.1, p.2⟫ - c) ^ (2 * k)
      ∂((G d).prod (G d)) :=
    hmeas _ ((hRm.sub_const c).pow_const _) hci
  have h := integral_integral_sub_pow_le (P := P) (G := fun d => (G d).prod (G d))
    (R := fun p : ℝ^N × ℝ^N =>
      (N : ℝ)⁻¹ * ⟪p.1, p.2⟫) hRm hk0 c hmc hfix
    (a := K₁₂ * k / N) (b := K₁₇ * k / N) (by positivity) (by positivity) h12.1 h12.2
    (by simpa only [hm, hcm] using h17.1) (by simpa only [hm, hcm] using h17.2)
  refine ⟨h.1, h.2.trans_eq ?_⟩
  congr 1
  ring

end SpinGlasses
