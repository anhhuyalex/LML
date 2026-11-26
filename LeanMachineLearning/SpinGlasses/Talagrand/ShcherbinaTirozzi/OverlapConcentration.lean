/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.BoundedTilted
public import LeanMachineLearning.ForMathlib.Probability.Moments.LogConcaveConcentration
public import LeanMachineLearning.ForMathlib.Probability.Moments.SecondMoment
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.Moments

/-!
# The Shcherbina--Tirozzi model: concentration of the overlaps under the Gibbs measure

For every realization of the disorder the Gibbs measure is uniformly log-concave, so Maurey's
inequality controls Lipschitz functions of the configuration. Since the measure essentially lives
on a ball of radius `√(B^*)`, the overlaps `R_{1,2} = σ¹ · σ² / N` and `R_{1,1} = ‖σ‖² / N`
concentrate around their Gibbs averages (Talagrand, Theorem 3.1.11), and, after averaging over
the disorder, at rate `(K k / N)^k` (Proposition 3.1.12). The constants depend only on
`κ₀, h₀, D`.

## Main declarations

* `SpinGlasses.integral_sub_integral_pow_shcherbinaTirozziGibbs_le`: Maurey's inequality for the
  Gibbs measure.
* `SpinGlasses.exists_integral_shcherbinaTirozzi_overlap_sub_mean_pow_le`: Eq. (3.34).
* `SpinGlasses.exists_integral_shcherbinaTirozzi_selfOverlap_sub_mean_pow_le`: Eq. (3.35).
* `SpinGlasses.exists_integral_integral_shcherbinaTirozzi_overlap_sub_mean_pow_le`: Eq. (3.42).
* `SpinGlasses.exists_integral_integral_shcherbinaTirozzi_selfOverlap_sub_mean_pow_le`:
  Eq. (3.43).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Module
open scoped RealInnerProductSpace Real

/-- A concave function on the whole real line is measurable. -/
theorem ConcaveOn.measurable_of_univ {u : ℝ → ℝ} (hu : ConcaveOn ℝ Set.univ u) : Measurable u :=
  (continuousOn_univ.1 (hu.continuousOn isOpen_univ)).measurable

namespace SpinGlasses

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

variable {N M : ℕ}

/-- **Maurey's inequality for the Gibbs measure** (Talagrand, Theorem 3.1.4 applied to (3.5)):
for concave `u ≤ 0` and an `A`-Lipschitz function `f` of the configuration,
`⟨(f - ⟨f⟩) ^ (2 k)⟩ ≤ 4 (8 k A² / κ) ^ k`. -/
theorem integral_sub_integral_pow_shcherbinaTirozziGibbs_le {κ h : ℝ} (hκ : 0 < κ) {u : ℝ → ℝ}
    (hu : ConcaveOn ℝ Set.univ u) (hu0 : ∀ x, u x ≤ 0) (g : Fin M → Fin N → ℝ)
    (g₀ : Fin N → ℝ) {f : ℝ^N → ℝ} (hf : Measurable f) {A : ℝ} (hA : 0 ≤ A)
    (hlip : ∀ x y, |f x - f y| ≤ A * ‖x - y‖) (k : ℕ) :
    Integrable (fun σ => (f σ - ∫ τ, f τ
          ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ)) ^ (2 * k))
        (volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ) ∧
      ∫ σ, (f σ - ∫ τ, f τ
          ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ)) ^ (2 * k)
          ∂(volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ) ≤
        4 * (8 * k * A ^ 2 / κ) ^ k := by
  have key := integral_sub_integral_pow_le_of_lipschitz (μ₀ := volume) (C := Set.univ)
    (H := shcherbinaTirozziHamiltonian κ h u g g₀) convex_univ MeasurableSet.univ
    (NeZero.ne _) (measurable_shcherbinaTirozziHamiltonian_apply κ h hu.measurable_of_univ g g₀)
    (integrableOn_univ.2 (integrable_exp_neg_shcherbinaTirozziHamiltonian hκ
      hu.measurable_of_univ hu0 g g₀))
    (fun x _ y _ => shcherbinaTirozziHamiltonian_midpoint_gap κ h hu g g₀ x y) hκ hf hA
    (fun x _ y _ => hlip x y) k
  simpa only [Measure.restrict_univ] using key

/-- **Theorem 3.1.11, Eq. (3.34):** for `k ≤ N`,
`⟨(R_{1,2} - ⟨R_{1,2}⟩) ^ (2 k)⟩ ≤ (K k B^* / N²) ^ k`. -/
theorem exists_integral_shcherbinaTirozzi_overlap_sub_mean_pow_le (κ₀ h₀ D : ℝ) (hκ₀ : 0 < κ₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M k : ℕ) (κ h : ℝ) (u : ℝ → ℝ) (g : Fin M → Fin N → ℝ)
      (g₀ : Fin N → ℝ), κ₀ ≤ κ → 0 ≤ h → h ≤ h₀ → M ≤ 10 * N → 1 ≤ N → k ≤ N →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → (∀ x, -D * (1 + |x|) ≤ u x) →
      ∀ G : Measure (ℝ^N),
        G = volume.tilted (fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ) →
        Integrable (fun p : ℝ^N × ℝ^N =>
            ((N : ℝ)⁻¹ * ⟪p.1, p.2⟫ - ∫ q, (N : ℝ)⁻¹ * ⟪q.1, q.2⟫ ∂(G.prod G)) ^ (2 * k))
            (G.prod G) ∧
          ∫ p, ((N : ℝ)⁻¹ * ⟪p.1, p.2⟫ - ∫ q, (N : ℝ)⁻¹ * ⟪q.1, q.2⟫ ∂(G.prod G)) ^ (2 * k)
              ∂(G.prod G) ≤
            (K * k * (N + Real.sqrt (∑ k, ∑ i, g k i ^ 2) + ∑ i, g₀ i ^ 2) /
              (N : ℝ) ^ 2) ^ k := by
  obtain ⟨K₉, hK₉, h319⟩ := exists_integral_sq_norm_pow_shcherbinaTirozziGibbs_le κ₀ h₀ D hκ₀
  refine ⟨128 * K₉ / κ₀, by positivity,
    fun N M k κ h u g g₀ hκ hh0 hh hM hN hk hu hu0 hD G hG => ?_⟩
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum := hu.measurable_of_univ
  have : IsProbabilityMeasure G := by
    rw [hG]
    exact isProbabilityMeasure_shcherbinaTirozziGibbs hκ0 hum hu0 g g₀
  set B : ℝ := N + Real.sqrt (∑ k, ∑ i, g k i ^ 2) + ∑ i, g₀ i ^ 2 with hB
  have hB0 : 0 ≤ B := add_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  have hmom : ∀ j, j ≤ 4 * N → Integrable (fun σ : ℝ^N => ‖σ‖ ^ (2 * j)) G ∧
      ∫ σ, ‖σ‖ ^ (2 * j) ∂G ≤ (K₉ * B) ^ j := fun j hj => by
    rw [hG]
    exact h319 N M j κ h u g g₀ hκ hh0 hh hM hj hum hu0 hD
  have hk4 : k ≤ 4 * N := by omega
  have hnorm : Integrable (fun σ : ℝ^N => ‖σ‖) G := by
    refine Integrable.mono' ((integrable_const 1).add (hmom 1 (by omega)).1)
      continuous_norm.aestronglyMeasurable (ae_of_all _ fun σ => ?_)
    rw [norm_norm, Pi.add_apply, mul_one]
    nlinarith [sq_nonneg (‖σ‖ - 1), norm_nonneg σ]
  have hid : Integrable (fun σ : ℝ^N => σ) G :=
    (integrable_norm_iff aestronglyMeasurable_id).1 hnorm
  set b : ℝ^N := ∫ σ, σ ∂G with hb
  -- the Gibbs average of the overlap
  have hinner : ∀ a : ℝ^N, ∫ τ, ⟪a, τ⟫ ∂G = ⟪a, b⟫ := fun a =>
    integral_inner hid a
  have h12 : Integrable (fun q : ℝ^N × ℝ^N =>
      (N : ℝ)⁻¹ * ⟪q.1, q.2⟫) (G.prod G) := by
    refine ((hnorm.mul_prod hnorm).mono' (by fun_prop) (ae_of_all _ fun q => ?_)).const_mul _
    rw [Real.norm_eq_abs]
    exact abs_real_inner_le_norm _ _
  have hmean : ∫ q, (N : ℝ)⁻¹ * ⟪q.1, q.2⟫ ∂(G.prod G) = (N : ℝ)⁻¹ * ⟪b, b⟫ := by
    rw [integral_const_mul]
    exact congrArg _ (integral_prod_bilin (innerSL ℝ) hid hid)
  set C : ℝ := 8 * k * (K₉ * B) / ((N : ℝ) ^ 2 * κ) with hC
  have hC0 : 0 ≤ C := by
    have := mul_nonneg hK₉ hB0
    positivity
  have hMau : ∀ a : ℝ^N,
      Integrable (fun τ => ((N : ℝ)⁻¹ * ⟪a, τ⟫ - (N : ℝ)⁻¹ * ⟪a, b⟫) ^ (2 * k)) G ∧
        ∫ τ, ((N : ℝ)⁻¹ * ⟪a, τ⟫ - (N : ℝ)⁻¹ * ⟪a, b⟫) ^ (2 * k) ∂G ≤
          4 * (8 * k / ((N : ℝ) ^ 2 * κ)) ^ k * ‖a‖ ^ (2 * k) := fun a => by
    have hlip : ∀ x y : ℝ^N,
        |(N : ℝ)⁻¹ * ⟪a, x⟫ - (N : ℝ)⁻¹ * ⟪a, y⟫| ≤ ‖a‖ / N * ‖x - y‖ := fun x y => by
      rw [← mul_sub, ← inner_sub_right, abs_mul, abs_of_pos (inv_pos.2 hN0), div_eq_inv_mul,
        mul_assoc]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (inv_pos.2 hN0).le
    have key := integral_sub_integral_pow_shcherbinaTirozziGibbs_le (h := h) hκ0 hu hu0 g g₀
      (f := fun τ => (N : ℝ)⁻¹ * ⟪a, τ⟫) (by fun_prop) (by positivity : 0 ≤ ‖a‖ / N) hlip k
    rw [← hG] at key
    simp only [integral_const_mul, hinner] at key
    refine ⟨key.1, key.2.trans_eq ?_⟩
    rw [pow_mul ‖a‖, mul_assoc (4 : ℝ), ← mul_pow]
    congr 2
    field_simp
  set X : ℝ^N × ℝ^N → ℝ :=
    fun p => (N : ℝ)⁻¹ * ⟪p.1, p.2⟫ - (N : ℝ)⁻¹ * ⟪p.1, b⟫ with hX
  set Y : ℝ^N → ℝ :=
    fun σ => (N : ℝ)⁻¹ * ⟪b, σ⟫ - (N : ℝ)⁻¹ * ⟪b, b⟫ with hY
  have hXm : Measurable X := by fun_prop
  have hYm : Measurable Y := by fun_prop
  have heven : Even (2 * k) := even_two_mul k
  set c : ℝ := 4 * (8 * k / ((N : ℝ) ^ 2 * κ)) ^ k with hc
  have hc0 : 0 ≤ c := by positivity
  have hcC : c * (K₉ * B) ^ k = 4 * C ^ k := by
    rw [hc, hC, mul_assoc, ← mul_pow]
    congr 2
    ring
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
  have hYi : Integrable (fun p : ℝ^N × ℝ^N =>
      Y p.1 ^ (2 * k)) (G.prod G) := (hMau b).1.comp_fst G
  have hYI : ∫ p : ℝ^N × ℝ^N, Y p.1 ^ (2 * k)
      ∂(G.prod G) ≤ 4 * C ^ k := by
    rw [integral_fun_fst (fun σ => Y σ ^ (2 * k)), probReal_univ, one_smul]
    refine (hMau b).2.trans ?_
    rw [← hcC]
    exact mul_le_mul_of_nonneg_left hbk hc0
  have hsum := integral_add_pow_two_mul_le (μ := G.prod G) (X := X) (Y := fun p => Y p.1)
    hXm.aestronglyMeasurable (hYm.comp measurable_fst).aestronglyMeasurable hXi hYi
  have e : (fun p : ℝ^N × ℝ^N =>
      ((N : ℝ)⁻¹ * ⟪p.1, p.2⟫ - ∫ q, (N : ℝ)⁻¹ * ⟪q.1, q.2⟫ ∂(G.prod G)) ^ (2 * k)) =
      fun p => (X p + Y p.1) ^ (2 * k) := by
    funext p
    rw [hmean, hX, hY]
    simp only
    rw [real_inner_comm p.1 b]
    congr 1
    ring
  rw [e]
  refine ⟨hsum.1, hsum.2.trans ?_⟩
  refine (mul_le_mul_of_nonneg_left (add_le_add hXI hYI) (by positivity)).trans ?_
  have h4 : (2 : ℝ) ^ (2 * k - 1) * 2 = 4 ^ k := by
    rw [← pow_succ, show 2 * k - 1 + 1 = 2 * k by omega, pow_mul]
    norm_num
  have h44 : (4 : ℝ) ^ k * 4 ≤ 16 ^ k := by
    have h1 : (4 : ℝ) ≤ 4 ^ k := le_self_pow₀ (by norm_num) hk0
    calc (4 : ℝ) ^ k * 4 ≤ 4 ^ k * 4 ^ k := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 16 ^ k := by rw [← mul_pow]; norm_num
  calc (2 : ℝ) ^ (2 * k - 1) * (4 * C ^ k + 4 * C ^ k)
      = (2 ^ (2 * k - 1) * 2) * 4 * C ^ k := by ring
    _ ≤ 16 ^ k * C ^ k := by
        rw [h4]
        exact mul_le_mul_of_nonneg_right h44 (pow_nonneg hC0 _)
    _ = (16 * C) ^ k := (mul_pow _ _ _).symm
    _ ≤ (128 * K₉ / κ₀ * k * B / (N : ℝ) ^ 2) ^ k := by
        refine pow_le_pow_left₀ (by positivity) ?_ k
        have e1 : 16 * C = 128 * K₉ * k * B / (N : ℝ) ^ 2 / κ := by
          rw [hC]; field_simp; ring
        have e2 : 128 * K₉ / κ₀ * k * B / (N : ℝ) ^ 2 =
            128 * K₉ * k * B / (N : ℝ) ^ 2 / κ₀ := by ring
        rw [e1, e2]
        have : 0 ≤ 128 * K₉ * k * B / (N : ℝ) ^ 2 := by positivity
        exact div_le_div_of_nonneg_left this hκ₀ hκ

/-- `exp (-B) ≤ (k / B) ^ k` for `B > 0` (Talagrand, Eq. (3.41)). -/
theorem _root_.Real.exp_neg_le_natCast_div_pow {B : ℝ} (hB : 0 < B) (k : ℕ) :
    Real.exp (-B) ≤ ((k : ℝ) / B) ^ k := by
  have h := Real.pow_le_natCast_pow_mul_exp hB.le k
  rw [div_pow, le_div_iff₀ (pow_pos hB k), Real.exp_neg]
  rwa [inv_mul_le_iff₀ (Real.exp_pos _), mul_comm]

/-- **Theorem 3.1.11, Eq. (3.35):** for `k ≤ N`,
`⟨(R_{1,1} - ⟨R_{1,1}⟩) ^ (2 k)⟩ ≤ (K k B^* / N²) ^ k`. -/
theorem exists_integral_shcherbinaTirozzi_selfOverlap_sub_mean_pow_le (κ₀ h₀ D : ℝ)
    (hκ₀ : 0 < κ₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M k : ℕ) (κ h : ℝ) (u : ℝ → ℝ) (g : Fin M → Fin N → ℝ)
      (g₀ : Fin N → ℝ), κ₀ ≤ κ → 0 ≤ h → h ≤ h₀ → M ≤ 10 * N → 1 ≤ N → k ≤ N →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → (∀ x, -D * (1 + |x|) ≤ u x) →
      ∀ G : Measure (ℝ^N),
        G = volume.tilted (fun σ => -shcherbinaTirozziHamiltonian κ h u g g₀ σ) →
        Integrable (fun σ : ℝ^N =>
            ((N : ℝ)⁻¹ * ‖σ‖ ^ 2 - ∫ τ, (N : ℝ)⁻¹ * ‖τ‖ ^ 2 ∂G) ^ (2 * k)) G ∧
          ∫ σ, ((N : ℝ)⁻¹ * ‖σ‖ ^ 2 - ∫ τ, (N : ℝ)⁻¹ * ‖τ‖ ^ 2 ∂G) ^ (2 * k) ∂G ≤
            (K * k * (N + Real.sqrt (∑ k, ∑ i, g k i ^ 2) + ∑ i, g₀ i ^ 2) /
              (N : ℝ) ^ 2) ^ k := by
  obtain ⟨K₁, hK₁, h317⟩ :=
    exists_integral_exp_half_sq_norm_shcherbinaTirozziGibbs_le_exp κ₀ h₀ D hκ₀
  obtain ⟨K₉, hK₉, h319⟩ := exists_integral_sq_norm_pow_shcherbinaTirozziGibbs_le κ₀ h₀ D hκ₀
  refine ⟨512 * (K₁ + 2) / κ₀ ^ 2 + 16 * K₉ ^ 2, by positivity,
    fun N M k κ h u g g₀ hκ hh0 hh hM hN hk hu hu0 hD G hG => ?_⟩
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum := hu.measurable_of_univ
  have : IsProbabilityMeasure G := by
    rw [hG]
    exact isProbabilityMeasure_shcherbinaTirozziGibbs hκ0 hum hu0 g g₀
  set B : ℝ := N + Real.sqrt (∑ k, ∑ i, g k i ^ 2) + ∑ i, g₀ i ^ 2 with hB
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hBN : (N : ℝ) ≤ B := by
    have h2 : 0 ≤ ∑ i, g₀ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [hB]
    linarith [Real.sqrt_nonneg (∑ k, ∑ i, g k i ^ 2)]
  have hB0 : 0 < B := hN0.trans_le hBN
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  have heven : Even (2 * k) := even_two_mul k
  have hmom : ∀ j, j ≤ 4 * N → Integrable (fun σ : ℝ^N => ‖σ‖ ^ (2 * j)) G ∧
      ∫ σ, ‖σ‖ ^ (2 * j) ∂G ≤ (K₉ * B) ^ j := fun j hj => by
    rw [hG]
    exact h319 N M j κ h u g g₀ hκ hh0 hh hM hj hum hu0 hD
  -- the truncation radius
  set a : ℝ := Real.sqrt (2 * (K₁ + 2) * B / κ) with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = 2 * (K₁ + 2) * B / κ := by
    rw [ha, Real.sq_sqrt (div_nonneg (mul_nonneg (by linarith) hB0.le) hκ0.le)]
  set f : ℝ^N → ℝ := fun σ => (N : ℝ)⁻¹ * min ‖σ‖ a ^ 2 with hf
  set φ : ℝ^N → ℝ := fun σ => (N : ℝ)⁻¹ * ‖σ‖ ^ 2 - f σ with hφ
  have hfm : Measurable f := by fun_prop
  have hφm : Measurable φ := by fun_prop
  have hlip : ∀ x y : ℝ^N, |f x - f y| ≤ 2 * a / N * ‖x - y‖ :=
    fun x y => by
      have h1 : |min ‖x‖ a - min ‖y‖ a| ≤ ‖x - y‖ := by
        refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le (abs_norm_sub_norm_le x y) ?_)
        rw [sub_self, abs_zero]
        exact norm_nonneg _
      have h2 : |min ‖x‖ a + min ‖y‖ a| ≤ 2 * a := by
        rw [abs_of_nonneg (add_nonneg (le_min (norm_nonneg _) ha0) (le_min (norm_nonneg _) ha0))]
        linarith [min_le_right ‖x‖ a, min_le_right ‖y‖ a]
      have e : f x - f y = (N : ℝ)⁻¹ *
          ((min ‖x‖ a + min ‖y‖ a) * (min ‖x‖ a - min ‖y‖ a)) := by
        rw [hf]; ring
      rw [e, abs_mul, abs_of_pos (inv_pos.2 hN0), abs_mul, div_eq_inv_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul h2 h1 (abs_nonneg _) (by positivity)) (inv_pos.2 hN0).le
  have hfMau := integral_sub_integral_pow_shcherbinaTirozziGibbs_le (h := h) hκ0 hu hu0 g g₀
    hfm (by positivity : 0 ≤ 2 * a / N) hlip k
  rw [← hG] at hfMau
  have hfb : ∀ σ, |f σ| ≤ (N : ℝ)⁻¹ * a ^ 2 := fun σ => by
    have h1 : 0 ≤ min ‖σ‖ a := le_min (norm_nonneg _) ha0
    rw [hf, abs_of_nonneg (mul_nonneg (inv_pos.2 hN0).le (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1 (min_le_right _ _) 2)
      (inv_pos.2 hN0).le
  have hfi : Integrable f G := Integrable.of_bound hfm.aestronglyMeasurable _
    (ae_of_all _ fun σ => by simpa only [Real.norm_eq_abs] using hfb σ)
  have hsq : Integrable (fun σ : ℝ^N => (N : ℝ)⁻¹ * ‖σ‖ ^ 2) G :=
    (by simpa using (hmom 1 (by omega)).1 : Integrable
      (fun σ : ℝ^N => ‖σ‖ ^ 2) G).const_mul _
  have hφi : Integrable φ G := hsq.sub hfi
  -- the tail of the truncation
  set S : Set (ℝ^N) := {σ | a ≤ ‖σ‖} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const measurable_norm
  have hGS : G.real S ≤ Real.exp (-(2 * B)) := by
    have hexp := (integral_exp_half_sq_norm_shcherbinaTirozziGibbs_le (h := h) hκ0 hum hu0
      g g₀).1
    rw [← hG] at hexp
    have hbound := h317 N M κ h u g g₀ hκ hh0 hh hM hum hu0 hD
    rw [← hG] at hbound
    have h1 : Real.exp (κ / 2 * a ^ 2) * G.real S ≤ Real.exp (K₁ * B) := by
      refine le_trans ?_ hbound
      have h2 := mul_meas_ge_le_integral_of_nonneg
        (μ := G) (f := fun σ : ℝ^N => Real.exp (κ / 2 * ‖σ‖ ^ 2))
        (ae_of_all _ fun _ => (Real.exp_pos _).le) hexp (Real.exp (κ / 2 * a ^ 2))
      refine le_trans (mul_le_mul_of_nonneg_left (measureReal_mono ?_ (measure_ne_top G _))
        (Real.exp_pos _).le) h2
      intro σ (hσ : a ≤ ‖σ‖)
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha0 hσ 2)
        (by positivity))
    have h3 : κ / 2 * a ^ 2 = (K₁ + 2) * B := by
      rw [ha2]; field_simp
    rw [h3] at h1
    refine le_of_mul_le_mul_left (h1.trans_eq ?_) (Real.exp_pos ((K₁ + 2) * B))
    rw [← Real.exp_add]
    congr 1
    ring
  have hφpt : ∀ σ, φ σ ^ (2 * k) ≤
      S.indicator 1 σ * ((N : ℝ)⁻¹ ^ (2 * k) * ‖σ‖ ^ (2 * (2 * k))) := fun σ => by
    by_cases hσ : a ≤ ‖σ‖
    · rw [Set.indicator_of_mem (show σ ∈ S from hσ), Pi.one_apply, one_mul, pow_mul ‖σ‖,
        ← mul_pow]
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
      rw [h0, zero_pow (by omega),
        Set.indicator_of_notMem (show σ ∉ S from hσ), zero_mul]
  have h4k : 2 * k ≤ 4 * N := by omega
  have h4k' : 4 * k ≤ 4 * N := by omega
  set Q : ℝ^N → ℝ := fun σ => (N : ℝ)⁻¹ ^ (2 * k) * ‖σ‖ ^ (2 * (2 * k))
    with hQ
  have hQL : MemLp Q 2 G := by
    refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
    have e : (fun σ => Q σ ^ 2) = fun σ =>
        ((N : ℝ)⁻¹ ^ (2 * k)) ^ 2 * ‖σ‖ ^ (2 * (4 * k)) := by
      funext σ
      rw [hQ]
      simp only
      rw [mul_pow, ← pow_mul ‖σ‖]
      congr 2
      ring
    rw [e]
    exact (hmom _ h4k').1.const_mul _
  have h1S : MemLp (S.indicator (1 : ℝ^N → ℝ)) 2 G :=
    (memLp_const (1 : ℝ)).indicator hSm.nullMeasurableSet
  have hdom : Integrable (fun σ => S.indicator 1 σ * Q σ) G := h1S.integrable_mul hQL
  have hφki : Integrable (fun σ => φ σ ^ (2 * k)) G :=
    Integrable.mono' hdom (hφm.pow_const _).aestronglyMeasurable (ae_of_all _ fun σ => by
      rw [Real.norm_of_nonneg (heven.pow_nonneg _)]
      exact hφpt σ)
  set T : ℝ := (K₉ * B / N) ^ (2 * k) with hT
  have hKB : 0 ≤ K₉ * B := mul_nonneg hK₉ hB0.le
  have hQ2 : ∫ σ, Q σ ^ 2 ∂G ≤ T ^ 2 := by
    have e : ∀ σ, Q σ ^ 2 = ((N : ℝ)⁻¹ ^ (2 * k)) ^ 2 * ‖σ‖ ^ (2 * (4 * k)) := fun σ => by
      rw [hQ]
      simp only
      rw [mul_pow, ← pow_mul ‖σ‖]
      congr 2
      ring
    simp_rw [e]
    rw [integral_const_mul]
    refine (mul_le_mul_of_nonneg_left (hmom _ h4k').2 (by positivity)).trans_eq ?_
    rw [hT, div_eq_inv_mul]
    ring_nf
  have h1S2 : ∫ σ, S.indicator (1 : ℝ^N → ℝ) σ ^ 2 ∂G ≤
      Real.exp (-B) ^ 2 := by
    have e : ∀ σ, S.indicator (1 : ℝ^N → ℝ) σ ^ 2 = S.indicator 1 σ :=
      fun σ => by
        by_cases hσ : σ ∈ S <;> simp [hσ]
    simp_rw [e]
    rw [integral_indicator_one hSm]
    refine hGS.trans_eq ?_
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hφI : ∫ σ, φ σ ^ (2 * k) ∂G ≤ Real.exp (-B) * T := by
    refine (integral_mono hφki hdom hφpt).trans ((le_abs_self _).trans ?_)
    have hTnn : 0 ≤ T := pow_nonneg (div_nonneg hKB hN0.le) (2 * k)
    rcases hTnn.eq_or_lt with hT0 | hT0
    · have hQ0 : (fun σ => Q σ ^ 2) =ᵐ[G] 0 := by
        refine (integral_eq_zero_iff_of_nonneg (fun σ => sq_nonneg _) hQL.integrable_sq).1
          (le_antisymm ?_ (integral_nonneg fun σ => sq_nonneg _))
        rw [← hT0] at hQ2
        simpa using hQ2
      have : (fun σ => S.indicator 1 σ * Q σ) =ᵐ[G] 0 := hQ0.mono fun σ hσ => by
        have : Q σ = 0 := pow_eq_zero_iff two_ne_zero |>.1 hσ
        simp [this]
      rw [integral_congr_ae this, ← hT0]
      simp
    · exact abs_integral_mul_le_of_integral_sq_le h1S hQL (Real.exp_pos _) hT0 h1S2 hQ2
  have hφsym := integral_sub_integral_pow_two_mul_le (μ := G) (f := φ) (m := 0) (k := k)
    hφm.aestronglyMeasurable (by simpa only [sub_zero] using hφki)
  simp only [sub_zero] at hφsym
  have hsum := integral_add_pow_two_mul_le (μ := G) (X := fun σ => f σ - ∫ τ, f τ ∂G)
    (Y := fun σ => φ σ - ∫ τ, φ τ ∂G) (hfm.sub_const _).aestronglyMeasurable
    (hφm.sub_const _).aestronglyMeasurable hfMau.1 hφsym.1
  have e : (fun σ : ℝ^N =>
      ((N : ℝ)⁻¹ * ‖σ‖ ^ 2 - ∫ τ, (N : ℝ)⁻¹ * ‖τ‖ ^ 2 ∂G) ^ (2 * k)) =
      fun σ => ((f σ - ∫ τ, f τ ∂G) + (φ σ - ∫ τ, φ τ ∂G)) ^ (2 * k) := by
    funext σ
    have : ∫ τ, φ τ ∂G = (∫ τ, (N : ℝ)⁻¹ * ‖τ‖ ^ 2 ∂G) - ∫ τ, f τ ∂G := integral_sub hsq hfi
    rw [this, hφ]
    congr 1
    ring
  rw [e]
  refine ⟨hsum.1, hsum.2.trans ?_⟩
  -- assemble the two bounds
  set x : ℝ := 64 * (K₁ + 2) * k * B / ((N : ℝ) ^ 2 * κ ^ 2) with hx
  set y : ℝ := K₉ ^ 2 * k * B / (N : ℝ) ^ 2 with hy
  have hK2 : 0 ≤ K₁ + 2 := by linarith
  have hx0 : 0 ≤ x := by
    rw [hx]
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK2)
      (Nat.cast_nonneg k)) hB0.le) (by positivity)
  have hy0 : 0 ≤ y := by
    have := hB0.le
    positivity
  have hX : ∫ σ, (f σ - ∫ τ, f τ ∂G) ^ (2 * k) ∂G ≤ 4 * x ^ k := by
    refine hfMau.2.trans_eq ?_
    congr 2
    rw [hx, div_pow, mul_pow, ha2]
    field_simp
    ring
  have hY : ∫ σ, (φ σ - ∫ τ, φ τ ∂G) ^ (2 * k) ∂G ≤ (4 * y) ^ k := by
    refine hφsym.2.trans ?_
    have h1 : Real.exp (-B) * T ≤ y ^ k := by
      refine (mul_le_mul_of_nonneg_right (Real.exp_neg_le_natCast_div_pow hB0 k)
        (pow_nonneg (div_nonneg hKB hN0.le) _)).trans_eq ?_
      rw [pow_mul, ← mul_pow, hy]
      congr 1
      field_simp
    refine (mul_le_mul_of_nonneg_left (hφI.trans h1) (by positivity)).trans_eq ?_
    rw [pow_mul, ← mul_pow]
    norm_num
  have h8 : (2 : ℝ) ^ (2 * k - 1) * (4 * x ^ k) ≤ (8 * x) ^ k := by
    have h4 : (2 : ℝ) ^ (2 * k - 1) * 4 = 4 ^ k * 2 := by
      have : (2 : ℝ) ^ (2 * k - 1) * 2 = 4 ^ k := by
        rw [← pow_succ, show 2 * k - 1 + 1 = 2 * k by omega, pow_mul]
        norm_num
      linear_combination 2 * this
    have h2 : (2 : ℝ) ≤ 2 ^ k := le_self_pow₀ (by norm_num) hk0
    rw [← mul_assoc, h4, mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hx0 _)
    calc (4 : ℝ) ^ k * 2 ≤ 4 ^ k * 2 ^ k := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 8 ^ k := by rw [← mul_pow]; norm_num
  have h16 : (2 : ℝ) ^ (2 * k - 1) * (4 * y) ^ k ≤ (16 * y) ^ k := by
    have h2 : (2 : ℝ) ^ (2 * k - 1) ≤ 4 ^ k := by
      rw [show (4 : ℝ) ^ k = 2 ^ (2 * k) by rw [pow_mul]; norm_num]
      exact pow_le_pow_right₀ one_le_two (by omega)
    refine (mul_le_mul_of_nonneg_right h2 (pow_nonneg (by linarith) _)).trans_eq ?_
    rw [← mul_pow]
    congr 1
    ring
  calc (2 : ℝ) ^ (2 * k - 1) * ((∫ σ, (f σ - ∫ τ, f τ ∂G) ^ (2 * k) ∂G) +
        ∫ σ, (φ σ - ∫ τ, φ τ ∂G) ^ (2 * k) ∂G)
      ≤ 2 ^ (2 * k - 1) * (4 * x ^ k + (4 * y) ^ k) :=
        mul_le_mul_of_nonneg_left (add_le_add hX hY) (by positivity)
    _ ≤ (8 * x) ^ k + (16 * y) ^ k := by
        rw [mul_add]; exact add_le_add h8 h16
    _ ≤ (8 * x + 16 * y) ^ k := pow_add_pow_le (by linarith) (by linarith) hk0
    _ ≤ ((512 * (K₁ + 2) / κ₀ ^ 2 + 16 * K₉ ^ 2) * k * B / (N : ℝ) ^ 2) ^ k := by
        refine pow_le_pow_left₀ (by linarith) ?_ k
        have e1 : (512 * (K₁ + 2) / κ₀ ^ 2 + 16 * K₉ ^ 2) * k * B / (N : ℝ) ^ 2 =
            512 * (K₁ + 2) * k * B / (N : ℝ) ^ 2 / κ₀ ^ 2 + 16 * y := by
          rw [hy]; ring
        have e2 : 8 * x = 512 * (K₁ + 2) * k * B / (N : ℝ) ^ 2 / κ ^ 2 := by
          rw [hx]; field_simp; ring
        rw [e1, e2]
        have h0 : 0 ≤ 512 * (K₁ + 2) * k * B / (N : ℝ) ^ 2 :=
          div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK2)
            (Nat.cast_nonneg k)) hB0.le) (by positivity)
        exact add_le_add (div_le_div_of_nonneg_left h0 (pow_pos hκ₀ 2)
          (pow_le_pow_left₀ hκ₀.le hκ 2)) le_rfl

/-- **Proposition 3.1.12, Eq. (3.42):** for `k ≤ N`,
`𝔼⟨(R_{1,2} - ⟨R_{1,2}⟩) ^ (2 k)⟩ ≤ (K k / N) ^ k` over the standard Gaussian disorder. -/
theorem exists_integral_integral_shcherbinaTirozzi_overlap_sub_mean_pow_le (κ₀ h₀ D : ℝ)
    (hκ₀ : 0 < κ₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M k : ℕ) (κ h : ℝ) (u : ℝ → ℝ), κ₀ ≤ κ → 0 ≤ h → h ≤ h₀ →
      M ≤ 10 * N → 1 ≤ N → k ≤ N → ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) →
      (∀ x, -D * (1 + |x|) ≤ u x) →
      ∀ G : (Fin M → Fin N → ℝ) × (Fin N → ℝ) → Measure (ℝ^N),
        (∀ d, G d = volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u d.1 d.2 σ) →
        ∀ P : Measure ((Fin M → Fin N → ℝ) × (Fin N → ℝ)),
        P = (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1) →
        Integrable (fun d => ∫ p, ((N : ℝ)⁻¹ * ⟪p.1, p.2⟫ -
              ∫ q, (N : ℝ)⁻¹ * ⟪q.1, q.2⟫ ∂((G d).prod (G d))) ^ (2 * k)
              ∂((G d).prod (G d))) P ∧
          ∫ d, ∫ p, ((N : ℝ)⁻¹ * ⟪p.1, p.2⟫ -
              ∫ q, (N : ℝ)⁻¹ * ⟪q.1, q.2⟫ ∂((G d).prod (G d))) ^ (2 * k)
              ∂((G d).prod (G d)) ∂P ≤ (K * k / N) ^ k := by
  obtain ⟨K, hK, h334⟩ := exists_integral_shcherbinaTirozzi_overlap_sub_mean_pow_le κ₀ h₀ D hκ₀
  refine ⟨40 * K, by positivity,
    fun N M k κ h u hκ hh0 hh hM hN hk hu hu0 hD G hG P hP => ?_⟩
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum := hu.measurable_of_univ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hprob : ∀ d, IsProbabilityMeasure (G d) := fun d => by
    rw [hG d]
    exact isProbabilityMeasure_shcherbinaTirozziGibbs hκ0 hum hu0 d.1 d.2
  -- measurability in the disorder
  have hE : Measurable fun p : ((Fin M → Fin N → ℝ) × (Fin N → ℝ)) ×
      ℝ^N => -shcherbinaTirozziHamiltonian κ h u p.1.1 p.1.2 p.2 :=
    (measurable_shcherbinaTirozziHamiltonian κ h hum).neg
  have h12m : Measurable fun p : ((Fin M → Fin N → ℝ) × (Fin N → ℝ)) ×
      (ℝ^N × ℝ^N) => (N : ℝ)⁻¹ * ⟪p.2.1, p.2.2⟫ := by
    fun_prop
  have h12i : ∀ d, Integrable (fun q : ℝ^N × ℝ^N =>
      (N : ℝ)⁻¹ * ⟪q.1, q.2⟫) ((G d).prod (G d)) := fun d => by
    have := hprob d
    obtain ⟨K₉, -, h319⟩ := exists_integral_sq_norm_pow_shcherbinaTirozziGibbs_le κ₀ h₀ D hκ₀
    have h2 := (h319 N M 1 κ h u d.1 d.2 hκ hh0 hh hM (by omega) hum hu0 hD).1
    rw [← hG d] at h2
    have hnorm : Integrable (fun σ : ℝ^N => ‖σ‖) (G d) := by
      refine Integrable.mono' ((integrable_const 1).add h2)
        continuous_norm.aestronglyMeasurable (ae_of_all _ fun σ => ?_)
      rw [norm_norm, Pi.add_apply, mul_one]
      nlinarith [sq_nonneg (‖σ‖ - 1), norm_nonneg σ]
    refine ((hnorm.mul_prod hnorm).mono' (by fun_prop) (ae_of_all _ fun q => ?_)).const_mul _
    rw [Real.norm_eq_abs]
    exact abs_real_inner_le_norm _ _
  have hmeas2 : ∀ F : (Fin M → Fin N → ℝ) × (Fin N → ℝ) →
      ℝ^N × ℝ^N → ℝ,
      (Measurable fun p : ((Fin M → Fin N → ℝ) × (Fin N → ℝ)) ×
        (ℝ^N × ℝ^N) => F p.1 p.2) →
      (∀ d, Integrable (F d) ((G d).prod (G d))) →
      Measurable fun d => ∫ p, F d p ∂((G d).prod (G d)) := fun F hF hFi => by
    simp only [hG] at hFi ⊢
    exact measurable_integral_prod_tilted_dep hE hF hFi
  -- name the Gibbs average of the overlap so that it is not unfolded during unification
  obtain ⟨m, hm⟩ : ∃ m : (Fin M → Fin N → ℝ) × (Fin N → ℝ) → ℝ, ∀ d,
      ∫ q, (N : ℝ)⁻¹ * ⟪q.1, q.2⟫ ∂((G d).prod (G d)) = m d := ⟨_, fun _ => rfl⟩
  have hmm : Measurable m := by
    have h := hmeas2 (fun _ q => (N : ℝ)⁻¹ * ⟪q.1, q.2⟫) h12m h12i
    exact (funext hm) ▸ h
  have hfix := fun d : (Fin M → Fin N → ℝ) × (Fin N → ℝ) =>
    h334 N M k κ h u d.1 d.2 hκ hh0 hh hM hN hk hu hu0 hD (G d) (hG d)
  simp only [hm] at hfix ⊢
  have hFj : Measurable fun p : ((Fin M → Fin N → ℝ) × (Fin N → ℝ)) ×
      (ℝ^N × ℝ^N) =>
      ((N : ℝ)⁻¹ * ⟪p.2.1, p.2.2⟫ - m p.1) ^ (2 * k) :=
    (h12m.sub (hmm.comp measurable_fst)).pow_const _
  have hFm := hmeas2 (fun d p => ((N : ℝ)⁻¹ * ⟪p.1, p.2⟫ - m d) ^ (2 * k)) hFj
    fun d => (hfix d).1
  have hB := integral_shcherbinaTirozzi_radius_pow_le (N := N) (M := M) hM hk
  rw [← hP] at hB
  set c : ℝ := (K * k / (N : ℝ) ^ 2) ^ k with hc
  have hc0 : 0 ≤ c := by positivity
  have hbound : ∀ d : (Fin M → Fin N → ℝ) × (Fin N → ℝ),
      (K * k * (N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) / (N : ℝ) ^ 2) ^ k =
        c * (N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) ^ k := fun d => by
    rw [hc, ← mul_pow]
    congr 1
    ring
  have hdom := hB.1.const_mul c
  have hFnn : ∀ d, 0 ≤ ∫ p, ((N : ℝ)⁻¹ * ⟪p.1, p.2⟫ - m d) ^ (2 * k) ∂((G d).prod (G d)) :=
    fun d => integral_nonneg fun p => (even_two_mul k).pow_nonneg _
  have hi : Integrable (fun d => ∫ p, ((N : ℝ)⁻¹ * ⟪p.1, p.2⟫ - m d) ^ (2 * k)
      ∂((G d).prod (G d))) P :=
    Integrable.mono' hdom hFm.aestronglyMeasurable (ae_of_all _ fun d => by
      rw [Real.norm_of_nonneg (hFnn d), ← hbound]
      exact (hfix d).2)
  refine ⟨hi, (integral_mono hi hdom fun d => (hfix d).2.trans_eq (hbound d)).trans ?_⟩
  rw [integral_const_mul]
  refine (mul_le_mul_of_nonneg_left hB.2 hc0).trans_eq ?_
  rw [hc, ← mul_pow]
  congr 1
  field_simp

/-- **Proposition 3.1.12, Eq. (3.43):** for `k ≤ N`,
`𝔼⟨(R_{1,1} - ⟨R_{1,1}⟩) ^ (2 k)⟩ ≤ (K k / N) ^ k` over the standard Gaussian disorder. -/
theorem exists_integral_integral_shcherbinaTirozzi_selfOverlap_sub_mean_pow_le (κ₀ h₀ D : ℝ)
    (hκ₀ : 0 < κ₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N M k : ℕ) (κ h : ℝ) (u : ℝ → ℝ), κ₀ ≤ κ → 0 ≤ h → h ≤ h₀ →
      M ≤ 10 * N → 1 ≤ N → k ≤ N → ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) →
      (∀ x, -D * (1 + |x|) ≤ u x) →
      ∀ G : (Fin M → Fin N → ℝ) × (Fin N → ℝ) → Measure (ℝ^N),
        (∀ d, G d = volume.tilted fun σ => -shcherbinaTirozziHamiltonian κ h u d.1 d.2 σ) →
        ∀ P : Measure ((Fin M → Fin N → ℝ) × (Fin N → ℝ)),
        P = (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1) →
        Integrable (fun d => ∫ σ, ((N : ℝ)⁻¹ * ‖σ‖ ^ 2 -
              ∫ τ, (N : ℝ)⁻¹ * ‖τ‖ ^ 2 ∂(G d)) ^ (2 * k) ∂(G d)) P ∧
          ∫ d, ∫ σ, ((N : ℝ)⁻¹ * ‖σ‖ ^ 2 -
              ∫ τ, (N : ℝ)⁻¹ * ‖τ‖ ^ 2 ∂(G d)) ^ (2 * k) ∂(G d) ∂P ≤ (K * k / N) ^ k := by
  obtain ⟨K, hK, h335⟩ :=
    exists_integral_shcherbinaTirozzi_selfOverlap_sub_mean_pow_le κ₀ h₀ D hκ₀
  refine ⟨40 * K, by positivity,
    fun N M k κ h u hκ hh0 hh hM hN hk hu hu0 hD G hG P hP => ?_⟩
  have hum := hu.measurable_of_univ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hE : Measurable fun p : ((Fin M → Fin N → ℝ) × (Fin N → ℝ)) ×
      ℝ^N => -shcherbinaTirozziHamiltonian κ h u p.1.1 p.1.2 p.2 :=
    (measurable_shcherbinaTirozziHamiltonian κ h hum).neg
  have hmean : Measurable fun d => ∫ τ, (N : ℝ)⁻¹ * ‖τ‖ ^ 2 ∂(G d) := by
    simp_rw [hG]
    exact measurable_integral_tilted hE (by fun_prop)
  have hsq : Measurable fun p : ((Fin M → Fin N → ℝ) × (Fin N → ℝ)) ×
      ℝ^N => (N : ℝ)⁻¹ * ‖p.2‖ ^ 2 := by fun_prop
  have hFm : Measurable fun d => ∫ σ, ((N : ℝ)⁻¹ * ‖σ‖ ^ 2 -
      ∫ τ, (N : ℝ)⁻¹ * ‖τ‖ ^ 2 ∂(G d)) ^ (2 * k) ∂(G d) := by
    have h1 := measurable_integral_tilted_dep (μ := volume)
      (e := fun d σ => -shcherbinaTirozziHamiltonian κ h u d.1 d.2 σ)
      (Y := fun d σ => ((N : ℝ)⁻¹ * ‖σ‖ ^ 2 - ∫ τ, (N : ℝ)⁻¹ * ‖τ‖ ^ 2 ∂(G d)) ^ (2 * k)) hE
      ((hsq.sub (hmean.comp measurable_fst)).pow_const _)
    simpa only [← hG] using h1
  have hfix := fun d : (Fin M → Fin N → ℝ) × (Fin N → ℝ) =>
    h335 N M k κ h u d.1 d.2 hκ hh0 hh hM hN hk hu hu0 hD (G d) (hG d)
  have hB := integral_shcherbinaTirozzi_radius_pow_le (N := N) (M := M) hM hk
  rw [← hP] at hB
  set c : ℝ := (K * k / (N : ℝ) ^ 2) ^ k with hc
  have hc0 : 0 ≤ c := by positivity
  have hbound : ∀ d : (Fin M → Fin N → ℝ) × (Fin N → ℝ),
      (K * k * (N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) / (N : ℝ) ^ 2) ^ k =
        c * (N + Real.sqrt (∑ k, ∑ i, d.1 k i ^ 2) + ∑ i, d.2 i ^ 2) ^ k := fun d => by
    rw [hc, ← mul_pow]
    congr 1
    ring
  have hdom := hB.1.const_mul c
  have hi : Integrable (fun d => ∫ σ, ((N : ℝ)⁻¹ * ‖σ‖ ^ 2 -
      ∫ τ, (N : ℝ)⁻¹ * ‖τ‖ ^ 2 ∂(G d)) ^ (2 * k) ∂(G d)) P :=
    Integrable.mono' hdom hFm.aestronglyMeasurable (ae_of_all _ fun d => by
      rw [Real.norm_of_nonneg (integral_nonneg fun σ => (even_two_mul k).pow_nonneg _),
        ← hbound]
      exact (hfix d).2)
  refine ⟨hi, (integral_mono hi hdom fun d => (hfix d).2.trans_eq (hbound d)).trans ?_⟩
  rw [integral_const_mul]
  refine (mul_le_mul_of_nonneg_left hB.2 hc0).trans_eq ?_
  rw [hc, ← mul_pow]
  congr 1
  field_simp

end SpinGlasses
