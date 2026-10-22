/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GaussianCovarianceInterpolation
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IteratedBound
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiExp
public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.PiUpdate

/-!
# Interpolation between a Gaussian projection and independent Gaussians

Fix deterministic vectors `u l ∈ ℝ^N` (`l ∈ Fin m`) and a scalar `v`, and let `ξ ∈ ℝ^m`,
`y ∈ ℝ^N` be independent standard Gaussian vectors.  The path
`Z_s = cos s (v ξ) + sin s (u ⬝ y)` interpolates between the independent Gaussians `v ξ_l`
(`s = 0`) and the projections `u l ⬝ y` of `y` (`s = π / 2`).  This is the engine of the general
Gaussian fluctuation principle of Talagrand's Theorem 1.7.11.

For a smooth `V` all of whose derivatives grow at most exponentially (`ExpTame`) and a
multi-index `a`, the products `derivProd V a (x) = ∏ l, V^{(a l)} (x l)` are closed under the
partial derivatives `∂_k` (`a ↦ a + e_k`).  Writing `T_{l k} = u l ⬝ u k - v² δ_{l k}`
(`projGram`), Gaussian interpolation gives

`(d/ds) 𝔼 derivProd V a (Z_s) = sin s cos s ∑_{l,k} T_{l k} 𝔼 derivProd V (a + e_l + e_k) (Z_s)`.

Iterating, `projSum V u v r s` (a sum over lists of `r` pairs of the products of entries of `T`
against `𝔼 derivProd V (pairCount p) (Z_s)`) satisfies
`(d/ds) projSum r = sin s cos s · projSum (r + 1)`.

## Main declarations

* `SpinGlasses.ExpTame`: smooth functions with exponentially bounded derivatives.
* `SpinGlasses.ExpTame.hasDerivAt_integral_derivProd_projPath`: the first derivative.
* `SpinGlasses.ExpTame.hasDerivAt_projSum`: the iterated derivative structure.
* `SpinGlasses.ExpTame.exists_abs_projSum_le`: a bound uniform in the data and in `N`.
* `SpinGlasses.ExpTame.measurable_projSum`: measurability in the data `u`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Theorem 1.7.11.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace SpinGlasses

open scoped ContDiff in
/-- A smooth function of one variable all of whose derivatives grow at most exponentially. -/
structure ExpTame (V : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ V
  bound : ∀ j : ℕ, ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧
    ∀ x, |deriv^[j] V x| ≤ C * Real.exp (c * |x|)

theorem ExpTame.deriv_tame {V : ℝ → ℝ} (hV : ExpTame V) : ExpTame (deriv V) where
  contDiff := hV.contDiff.deriv'
  bound j := by
    obtain ⟨C, c, hC, hc, h⟩ := hV.bound (j + 1)
    exact ⟨C, c, hC, hc, fun x => by simpa [Function.iterate_succ_apply] using h x⟩

theorem ExpTame.iterate_deriv_tame {V : ℝ → ℝ} (hV : ExpTame V) (n : ℕ) :
    ExpTame (deriv^[n] V) where
  contDiff := hV.contDiff.iterate_deriv n
  bound j := by
    obtain ⟨C, c, hC, hc, h⟩ := hV.bound (j + n)
    exact ⟨C, c, hC, hc, fun x => by simpa [← Function.iterate_add_apply] using h x⟩

/-- The product `∏ ℓ, V^{(a ℓ)}(x ℓ)` of derivatives of `V` of orders `a ℓ` in the coordinates. -/
noncomputable def derivProd {m : ℕ} (V : ℝ → ℝ) (a : Fin m → ℕ) (x : Fin m → ℝ) : ℝ :=
  ∏ ℓ, deriv^[a ℓ] V (x ℓ)

variable {m : ℕ} {V : ℝ → ℝ}

open scoped ContDiff in
theorem ExpTame.contDiff_derivProd (hV : ExpTame V) (a : Fin m → ℕ) :
    ContDiff ℝ ∞ (derivProd V a) := by
  unfold derivProd
  refine contDiff_prod fun ℓ _ => ?_
  exact (hV.contDiff.iterate_deriv (a ℓ)).comp (contDiff_apply ℝ ℝ ℓ)

theorem ExpTame.hasFDerivAt_derivProd (hV : ExpTame V) (a : Fin m → ℕ) (x : Fin m → ℝ)
    (k : Fin m) :
    fderiv ℝ (derivProd V a) x (Pi.single k 1) = derivProd V (a + Pi.single k 1) x := by
  classical
  unfold derivProd
  have hd : ∀ ℓ, HasFDerivAt (fun y : Fin m → ℝ => deriv^[a ℓ] V (y ℓ))
      (deriv (deriv^[a ℓ] V) (x ℓ) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) ℓ)
      x := fun ℓ => by
    have hdiff : Differentiable ℝ (deriv^[a ℓ] V) :=
      ((hV.contDiff.iterate_deriv (a ℓ)).differentiable (by simp))
    have h1 := (hdiff (x ℓ)).hasDerivAt.hasFDerivAt.comp x
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) ℓ).hasFDerivAt
    refine h1.congr_fderiv ?_
    ext y
    simp [mul_comm]
  have hprod := HasFDerivAt.finsetProd (u := Finset.univ) (fun ℓ _ => hd ℓ)
  rw [hprod.fderiv]
  simp only [_root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.proj_apply,
    Pi.single_apply, smul_eq_mul]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    have : j ≠ k := Finset.ne_of_mem_erase hj
    simp [this]
  · simp [Function.iterate_succ_apply']


theorem ExpTame.abs_derivProd_le (hV : ExpTame V) (a : Fin m → ℕ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ y, |derivProd V a y| ≤ C * Real.exp (c * ∑ l, |y l|) := by
  choose C c hC hc h using fun ℓ : Fin m => hV.bound (a ℓ)
  refine ⟨∏ ℓ, C ℓ, ∑ ℓ, c ℓ, Finset.prod_nonneg fun ℓ _ => hC ℓ,
    Finset.sum_nonneg fun ℓ _ => hc ℓ, fun y => ?_⟩
  have hS : ∀ ℓ, |y ℓ| ≤ ∑ l, |y l| := fun ℓ =>
    Finset.single_le_sum (f := fun l => |y l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ ℓ)
  unfold derivProd
  rw [Finset.abs_prod]
  calc ∏ ℓ, |deriv^[a ℓ] V (y ℓ)| ≤ ∏ ℓ, (C ℓ * Real.exp (c ℓ * |y ℓ|)) :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun ℓ _ => h ℓ (y ℓ)
    _ = (∏ ℓ, C ℓ) * Real.exp (∑ ℓ, c ℓ * |y ℓ|) := by
        rw [Finset.prod_mul_distrib, Real.exp_sum]
    _ ≤ (∏ ℓ, C ℓ) * Real.exp ((∑ ℓ, c ℓ) * ∑ l, |y l|) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
          (Finset.prod_nonneg fun ℓ _ => hC ℓ)
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_left (hS ℓ) (hc ℓ)


/-- The covariance defect `T l k = u l ⬝ u k - v² δ_{l k}` of the projection path. -/
noncomputable def projGram {m N : ℕ} (u : Fin m → Fin N → ℝ) (v : ℝ) (l k : Fin m) : ℝ :=
  u l ⬝ᵥ u k - if l = k then v ^ 2 else 0

/-- The path point `cos s (v ξ) + sin s (u ⬝ y)` for `ω = (ξ, y)`. -/
noncomputable def projPath {m N : ℕ} (u : Fin m → Fin N → ℝ) (v s : ℝ)
    (ω : (Fin m → ℝ) × (Fin N → ℝ)) : Fin m → ℝ :=
  fun l => Real.cos s * (v * ω.1 l) + Real.sin s * (u l ⬝ᵥ ω.2)


variable {N : ℕ}

/-- **Derivative of the Gaussian-projection path.**  For deterministic vectors `u l` and a scalar
`v`, set `Z_s = cos s (v ξ) + sin s (u ⬝ y)` for independent standard Gaussian vectors `ξ`, `y`.
The expectation of a product of derivatives of an exponentially tame `V` has derivative
`sin t cos t ∑_{l,k} T_{l k} 𝔼 ∂_l ∂_k (...)(Z_t)`, where `T` is `projGram u v`. -/
theorem ExpTame.hasDerivAt_integral_derivProd_projPath (hV : ExpTame V)
    (u : Fin m → Fin N → ℝ) (v : ℝ) (a : Fin m → ℕ) (t : ℝ) :
    HasDerivAt (fun s => ∫ ω, derivProd V a (projPath u v s ω)
        ∂((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)))
      (Real.sin t * Real.cos t * ∑ l, ∑ k, projGram u v l k *
        ∫ ω, derivProd V (a + Pi.single l 1 + Pi.single k 1) (projPath u v t ω)
          ∂((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin N => gaussianReal 0 1))) t := by
  classical
  set P : Measure ((Fin m → ℝ) × (Fin N → ℝ)) := (Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
    (Measure.pi fun _ : Fin N => gaussianReal 0 1) with hP
  let X : Fin m → (Fin m → ℝ) × (Fin N → ℝ) → ℝ := fun l ω => v * ω.1 l
  let Y : Fin m → (Fin m → ℝ) × (Fin N → ℝ) → ℝ := fun l ω => u l ⬝ᵥ ω.2
  have hXe : ∀ l ω, X l ω = Pi.single l v ⬝ᵥ ω.1 := fun l ω => by
    simp [X, single_dotProduct]
  have hXf : HasGaussianLaw (fun (ξ : Fin m → ℝ) (l : Fin m) => Pi.single l v ⬝ᵥ ξ)
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) :=
    hasGaussianLaw_dotProduct_family (fun l : Fin m => (Pi.single l v : Fin m → ℝ))
  have hYf : HasGaussianLaw (fun (y : Fin N → ℝ) (l : Fin m) => u l ⬝ᵥ y)
      (Measure.pi fun _ : Fin N => gaussianReal 0 1) := hasGaussianLaw_dotProduct_family u
  have hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P := by
    have h := HasGaussianLaw.sumElim_prod_of_independent hXf hYf
      (by fun_prop) (by fun_prop)
    convert h using 1
    funext z s
    cases s <;> simp [X, Y, single_dotProduct]
  have hXm : ∀ l, Measurable (X l) := fun l => by simp only [X]; fun_prop
  have hYm : ∀ l, Measurable (Y l) := fun l => by simp only [Y]; fun_prop
  have hX : ∀ l, ∫ ω, X l ω ∂P = 0 := fun l => by
    have : ∫ ω, X l ω ∂P =
        ∫ ξ, (Pi.single l v ⬝ᵥ ξ) ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
      simp_rw [hXe]
      exact integral_prod_fun_fst_of_isProbabilityMeasure _ _ (fun ξ => Pi.single l v ⬝ᵥ ξ)
    rw [this]
    exact integral_dotProduct_pi_gaussianReal _
  have hY : ∀ l, ∫ ω, Y l ω ∂P = 0 := fun l => by
    have : ∫ ω, Y l ω ∂P = ∫ y, (u l ⬝ᵥ y) ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) :=
      integral_prod_fun_snd_of_isProbabilityMeasure _ _ (fun y => u l ⬝ᵥ y)
    rw [this]
    exact integral_dotProduct_pi_gaussianReal _
  have h0 : ∀ l k, ∫ ω, X l ω * Y k ω ∂P = 0 := fun l k => by
    have := integral_prod_mul (μ := Measure.pi fun _ : Fin m => gaussianReal 0 1)
      (ν := Measure.pi fun _ : Fin N => gaussianReal 0 1) (fun ξ => Pi.single l v ⬝ᵥ ξ)
      (fun y => u k ⬝ᵥ y)
    rw [show (fun ω => X l ω * Y k ω) = fun ω : (Fin m → ℝ) × (Fin N → ℝ) =>
      (Pi.single l v ⬝ᵥ ω.1) * (u k ⬝ᵥ ω.2) from funext fun ω => by simp only [hXe, Y], hP, this,
      integral_dotProduct_pi_gaussianReal, zero_mul]
  have hYY : ∀ l k, ∫ ω, Y l ω * Y k ω ∂P = u l ⬝ᵥ u k := fun l k => by
    have : ∫ ω, Y l ω * Y k ω ∂P = ∫ y, (u l ⬝ᵥ y) * (u k ⬝ᵥ y)
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) :=
      integral_prod_fun_snd_of_isProbabilityMeasure _ _ (fun y => (u l ⬝ᵥ y) * (u k ⬝ᵥ y))
    rw [this]
    exact integral_dotProduct_mul_dotProduct_pi_gaussianReal _ _
  have hXX : ∀ l k, ∫ ω, X l ω * X k ω ∂P = if l = k then v ^ 2 else 0 := fun l k => by
    have : ∫ ω, X l ω * X k ω ∂P = ∫ ξ, (Pi.single l v ⬝ᵥ ξ) * (Pi.single k v ⬝ᵥ ξ)
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
      simp_rw [hXe]
      exact integral_prod_fun_fst_of_isProbabilityMeasure _ _ (fun ξ => (Pi.single l v ⬝ᵥ ξ) *
        (Pi.single k v ⬝ᵥ ξ))
    rw [this, integral_dotProduct_mul_dotProduct_pi_gaussianReal]
    by_cases h : l = k
    · subst h; simp [dotProduct_single, sq]
    · simp [h, dotProduct_single, Ne.symm h]
  have hFc : ContDiff ℝ 2 (derivProd V a) := (hV.contDiff_derivProd a).of_le (by simp)
  have hfd : ∀ (b : Fin m → ℕ) (l : Fin m) (y : Fin m → ℝ),
      fderiv ℝ (derivProd V b) y (Pi.single l 1) = derivProd V (b + Pi.single l 1) y :=
    fun b l y => hV.hasFDerivAt_derivProd b y l
  obtain ⟨C₀, c₀, hC₀, hc₀, hF0⟩ := hV.abs_derivProd_le a
  choose C₁ c₁ hC₁ hc₁ hF1 using fun l : Fin m => hV.abs_derivProd_le (a + Pi.single l 1)
  choose C₂ c₂ hC₂ hc₂ hF2 using fun (k l : Fin m) =>
    hV.abs_derivProd_le (a + Pi.single l 1 + Pi.single k 1)
  have hS : ∀ y : Fin m → ℝ, 0 ≤ ∑ l, |y l| := fun y => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h := hasDerivAt_integral_comp_trig (X := X) (Y := Y) (P := P) hXY hX hY h0
    (F := derivProd V a) hFc (C₀ := C₀) (c₀ := c₀) hF0 (D := C₁) (c₁ := ∑ l, c₁ l)
    (fun l y => by
      rw [hfd]
      exact (hF1 l y).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := c₁) (fun _ _ => hc₁ _)
          (Finset.mem_univ l)) (hS y))) (hC₁ l)))
    (D2 := C₂) (c₂ := ∑ k, ∑ l, c₂ k l)
    (fun k l y => by
      have : (fun y => fderiv ℝ (derivProd V a) y (Pi.single l 1)) =
          derivProd V (a + Pi.single l 1) := funext fun y => hfd a l y
      rw [this, hfd]
      refine (hF2 k l y).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_right ?_ (hS y))) (hC₂ k l))
      exact (Finset.single_le_sum (f := c₂ k) (fun _ _ => hc₂ _ _) (Finset.mem_univ l)).trans
        (Finset.single_le_sum (f := fun k => ∑ l, c₂ k l) (fun _ _ =>
          Finset.sum_nonneg fun _ _ => hc₂ _ _) (Finset.mem_univ k))) t
  refine h.congr_deriv ?_
  congr 1
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  have e1 : (fun y => fderiv ℝ (derivProd V a) y (Pi.single l 1)) =
      derivProd V (a + Pi.single l 1) := funext fun y => hfd a l y
  rw [hYY, hXX]
  simp only [projGram, hfd]
  congr 1


section Lists

variable {r : ℕ}

/-- The multi-index counting how often each replica occurs in a list of `r` pairs. -/
def pairCount (p : Fin r → Fin m × Fin m) : Fin m → ℕ := fun ℓ =>
  ∑ i, ((if (p i).1 = ℓ then 1 else 0) + (if (p i).2 = ℓ then 1 else 0))

/-- The product `∏ i, T (p i).1 (p i).2` of matrix entries along a list of pairs. -/
def pairProd (T : Fin m → Fin m → ℝ) (p : Fin r → Fin m × Fin m) : ℝ :=
  ∏ i, T (p i).1 (p i).2

theorem pairCount_cons (q : Fin m × Fin m) (p : Fin r → Fin m × Fin m) :
    pairCount (Fin.cons q p : Fin (r + 1) → Fin m × Fin m) =
      pairCount p + Pi.single q.1 1 + Pi.single q.2 1 := by
  funext ℓ
  have key : ∀ a : Fin m, (Pi.single a (1 : ℕ) : Fin m → ℕ) ℓ = if a = ℓ then 1 else 0 :=
      fun a => by
    simp [Pi.single_apply, eq_comm]
  simp only [pairCount, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Pi.add_apply, key]
  ring

theorem pairProd_cons (T : Fin m → Fin m → ℝ) (q : Fin m × Fin m) (p : Fin r → Fin m × Fin m) :
    pairProd T (Fin.cons q p : Fin (r + 1) → Fin m × Fin m) = T q.1 q.2 * pairProd T p := by
  simp [pairProd, Fin.prod_univ_succ]

/-- The total multiplicity of all replicas across a list of `r` pairs is `2 * r`. -/
theorem sum_pairCount (p : Fin r → Fin m × Fin m) :
    ∑ ℓ : Fin m, pairCount p ℓ = 2 * r := by
  classical
  unfold pairCount
  rw [sum_comm]
  have h (i : Fin r) : (∑ ℓ : Fin m, ((if (p i).1 = ℓ then 1 else 0) +
      (if (p i).2 = ℓ then 1 else 0))) = 2 := by
    rw [sum_add_distrib]
    simp only [sum_ite_eq, mem_univ, ite_true]
  simp [h, mul_comm]

/-- If `r < m`, any list of `r` pairs of replicas in `Fin m` must leave some replica with
multiplicity 0 or 1. -/
theorem exists_pairCount_le_one_of_lt (p : Fin r → Fin m × Fin m) (hr : r < m) :
    ∃ ℓ : Fin m, pairCount p ℓ = 0 ∨ pairCount p ℓ = 1 := by
  by_contra! h
  have h2 : ∀ ℓ : Fin m, 2 ≤ pairCount p ℓ := fun ℓ => by
    have := h ℓ
    omega
  have hle : 2 * m ≤ ∑ ℓ : Fin m, pairCount p ℓ := by
    calc 2 * m = ∑ _ℓ : Fin m, 2 := by simp [mul_comm]
    _ ≤ ∑ ℓ : Fin m, pairCount p ℓ := sum_le_sum fun ℓ _ => h2 ℓ
  rw [sum_pairCount] at hle
  omega

/-- If every replica in `Fin m` occurs with multiplicity at least 2 in a list of `r` pairs,
then `m ≤ r`. -/
theorem card_le_of_forall_two_le_pairCount (p : Fin r → Fin m × Fin m)
    (hp : ∀ ℓ : Fin m, 2 ≤ pairCount p ℓ) : m ≤ r := by
  have hle : 2 * m ≤ ∑ ℓ : Fin m, pairCount p ℓ := by
    calc 2 * m = ∑ _ℓ : Fin m, 2 := by simp [mul_comm]
    _ ≤ ∑ ℓ : Fin m, pairCount p ℓ := sum_le_sum fun ℓ _ => hp ℓ
  rw [sum_pairCount] at hle
  omega

/-- The path functional `s ↦ ∑_p ∏ T_{p} 𝔼 ∂^{count p} (…)(Z_s)`, i.e. `𝔼 (D^r F)(Z_s)` with
`D = ∑ T_{l k} ∂_l ∂_k`. -/
noncomputable def projSum (V : ℝ → ℝ) (u : Fin m → Fin N → ℝ) (v : ℝ) (r : ℕ) (s : ℝ) : ℝ :=
  ∑ p : Fin r → Fin m × Fin m, pairProd (projGram u v) p *
    ∫ ω, derivProd V (pairCount p) (projPath u v s ω)
      ∂((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1))

theorem ExpTame.hasDerivAt_projSum (hV : ExpTame V) (u : Fin m → Fin N → ℝ) (v : ℝ) (r : ℕ)
    (t : ℝ) :
    HasDerivAt (projSum V u v r) (Real.sin t * Real.cos t * projSum V u v (r + 1) t) t := by
  classical
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (A := fun (p : Fin r → Fin m × Fin m) (s : ℝ) => pairProd (projGram u v) p *
      ∫ ω, derivProd V (pairCount p) (projPath u v s ω)
        ∂((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)))
    (A' := fun (p : Fin r → Fin m × Fin m) => pairProd (projGram u v) p *
      (Real.sin t * Real.cos t * ∑ l, ∑ k, projGram u v l k *
        ∫ ω, derivProd V (pairCount p + Pi.single l 1 + Pi.single k 1) (projPath u v t ω)
          ∂((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin N => gaussianReal 0 1))))
    (fun p _ => (hV.hasDerivAt_integral_derivProd_projPath u v (pairCount p) t).const_mul
      (pairProd (projGram u v) p))
  unfold projSum
  refine h.congr_deriv ?_
  have hc := (Fin.consEquiv (fun _ : Fin (r + 1) => Fin m × Fin m)).sum_comp
    (fun p' : Fin (r + 1) → Fin m × Fin m => pairProd (projGram u v) p' *
      ∫ ω, derivProd V (pairCount p') (projPath u v t ω)
        ∂((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)))
  rw [← hc]
  simp only [Fintype.sum_prod_type,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ => ?_
  have hcons : (Fin.consEquiv (fun _ : Fin (r + 1) => Fin m × Fin m)) ((l, k), p) =
      Fin.cons (l, k) p := rfl
  rw [hcons, pairProd_cons, pairCount_cons]
  ring

end Lists



theorem exp_sum_le_avg_exp (hm : 0 < m) (a : Fin m → ℝ) :
    Real.exp (∑ l, a l) ≤ (1 / (m : ℝ)) * ∑ l, Real.exp (m * a l) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hw : ∀ l ∈ (Finset.univ : Finset (Fin m)), (0 : ℝ) ≤ 1 / (m : ℝ) := fun _ _ => by positivity
  have hsum : ∑ _l : Fin m, (1 / (m : ℝ)) = 1 := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; field_simp
  have h := convexOn_exp.map_sum_le hw hsum (fun l _ => Set.mem_univ (m * a l))
  simp only [smul_eq_mul] at h
  have e : ∑ l, 1 / (m : ℝ) * (m * a l) = ∑ l, a l := by
    refine Finset.sum_congr rfl fun l _ => ?_
    field_simp
  rw [e] at h
  rwa [← Finset.mul_sum] at h


/-- The Gaussian measure on pairs `(ξ, y)` used in the projection path. -/
noncomputable abbrev projMeasure (m N : ℕ) : Measure ((Fin m → ℝ) × (Fin N → ℝ)) :=
  (Measure.pi fun _ : Fin m => gaussianReal 0 1).prod (Measure.pi fun _ : Fin N => gaussianReal 0 1)

theorem projPath_apply_exp (u : Fin m → Fin N → ℝ) (v s b : ℝ) (l : Fin m)
    (ω : (Fin m → ℝ) × (Fin N → ℝ)) :
    Real.exp (b * projPath u v s ω l) =
      Real.exp (∑ e, (Pi.single l (b * (Real.cos s * v)) : Fin m → ℝ) e * ω.1 e) *
        Real.exp (∑ i, (b * Real.sin s * u l i) * ω.2 i) := by
  rw [← Real.exp_add]
  congr 1
  simp only [projPath, Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, dotProduct, Finset.mul_sum]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _ => by ring


theorem integrable_exp_mul_projPath (u : Fin m → Fin N → ℝ) (v s b : ℝ) (l : Fin m) :
    Integrable (fun ω => Real.exp (b * projPath u v s ω l)) (projMeasure m N) := by
  simp_rw [projPath_apply_exp]
  exact integrable_exp_prod_mul_gaussianReal _ _

theorem integral_exp_mul_projPath (u : Fin m → Fin N → ℝ) (v s b : ℝ) (l : Fin m) :
    ∫ ω, Real.exp (b * projPath u v s ω l) ∂(projMeasure m N) =
      Real.exp (b ^ 2 / 2 * ((Real.cos s * v) ^ 2 + Real.sin s ^ 2 * (u l ⬝ᵥ u l))) := by
  simp_rw [projPath_apply_exp]
  rw [integral_prod_mul (fun ξ : Fin m → ℝ => Real.exp (∑ e, (Pi.single l (b * (Real.cos s * v)) :
      Fin m → ℝ) e * ξ e)) (fun y : Fin N → ℝ => Real.exp (∑ i, (b * Real.sin s * u l i) * y i)),
    integral_exp_sum_mul_gaussianReal, integral_exp_sum_mul_gaussianReal, ← Real.exp_add]
  congr 1
  have h1 : ∑ e : Fin m, (Pi.single l (b * (Real.cos s * v)) : Fin m → ℝ) e ^ 2 / 2 =
      (b * (Real.cos s * v)) ^ 2 / 2 := by
    simp [Pi.single_apply, ite_pow, apply_ite (fun x : ℝ => x / 2)]
  rw [h1]
  have h2 : ∑ i, (b * Real.sin s * u l i) ^ 2 / 2 =
      b ^ 2 / 2 * (Real.sin s ^ 2 * (u l ⬝ᵥ u l)) := by
    simp only [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2]
  ring


theorem exp_abs_le_add (x : ℝ) : Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; linarith [Real.exp_pos (-x)]
  · rw [h]; linarith [Real.exp_pos x]

theorem ExpTame.exists_abs_integral_derivProd_projPath_le (hV : ExpTame V) (hm : 0 < m)
    (a : Fin m → ℕ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (u : Fin m → Fin N → ℝ) (v s : ℝ),
      (∀ l, u l ⬝ᵥ u l ≤ B) → v ^ 2 ≤ B →
        |∫ ω, derivProd V a (projPath u v s ω) ∂(projMeasure m N)| ≤ C := by
  obtain ⟨C₀, c, hC₀, hc, hbd⟩ := hV.abs_derivProd_le a
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set B' : ℝ := max B 0 with hB'
  refine ⟨2 * C₀ * Real.exp ((m * c) ^ 2 / 2 * B'), by positivity, fun N u v s hu hv => ?_⟩
  set b : ℝ := m * c with hb
  let G : (Fin m → ℝ) × (Fin N → ℝ) → ℝ := fun ω =>
    C₀ * ((1 / (m : ℝ)) * ∑ l, (Real.exp (b * projPath u v s ω l) +
      Real.exp (-b * projPath u v s ω l)))
  have hGi : Integrable G (projMeasure m N) := by
    refine Integrable.const_mul (Integrable.const_mul (integrable_finsetSum _ fun l _ => ?_) _) _
    exact (integrable_exp_mul_projPath u v s b l).add (integrable_exp_mul_projPath u v s (-b) l)
  have hpt : ∀ ω, |derivProd V a (projPath u v s ω)| ≤ G ω := fun ω => by
    refine (hbd _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₀
    have h1 := exp_sum_le_avg_exp hm (fun l => c * |projPath u v s ω l|)
    rw [← Finset.mul_sum] at h1
    refine (le_of_eq_of_le (by rw [Finset.mul_sum]) h1).trans ?_
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_) (by positivity)
    have h2 := exp_abs_le_add (b * projPath u v s ω l)
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ b)] at h2
    rw [← mul_assoc, ← hb, neg_mul]
    exact h2
  have hnorm := norm_integral_le_of_norm_le hGi (f := fun ω => derivProd V a (projPath u v s ω))
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hpt ω)
  rw [Real.norm_eq_abs] at hnorm
  refine hnorm.trans ?_
  have hvar : ∀ l, (Real.cos s * v) ^ 2 + Real.sin s ^ 2 * (u l ⬝ᵥ u l) ≤ B' := fun l => by
    have h1 : v ^ 2 ≤ B' := hv.trans (le_max_left _ _)
    have h2 : u l ⬝ᵥ u l ≤ B' := (hu l).trans (le_max_left _ _)
    calc (Real.cos s * v) ^ 2 + Real.sin s ^ 2 * (u l ⬝ᵥ u l)
        ≤ Real.cos s ^ 2 * B' + Real.sin s ^ 2 * B' := by
          rw [mul_pow]
          exact add_le_add (mul_le_mul_of_nonneg_left h1 (sq_nonneg _))
            (mul_le_mul_of_nonneg_left h2 (sq_nonneg _))
      _ = B' := by rw [← add_mul, Real.cos_sq_add_sin_sq, one_mul]
  have hI : ∀ (b' : ℝ) (l : Fin m), ∫ ω, Real.exp (b' * projPath u v s ω l)
      ∂(projMeasure m N) ≤ Real.exp (b' ^ 2 / 2 * B') := fun b' l => by
    rw [integral_exp_mul_projPath]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hvar l) (by positivity))
  have hGint : ∫ ω, G ω ∂(projMeasure m N) = C₀ * ((1 / (m : ℝ)) * ∑ l,
      ((∫ ω, Real.exp (b * projPath u v s ω l) ∂(projMeasure m N)) +
        ∫ ω, Real.exp (-b * projPath u v s ω l) ∂(projMeasure m N))) := by
    simp only [G]
    rw [integral_const_mul, integral_const_mul]
    congr 2
    rw [integral_finsetSum (f := fun (l : Fin m) (ω : (Fin m → ℝ) × (Fin N → ℝ)) =>
      Real.exp (b * projPath u v s ω l) + Real.exp (-b * projPath u v s ω l)) _ fun l _ =>
      (integrable_exp_mul_projPath u v s b l).add (integrable_exp_mul_projPath u v s (-b) l)]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact integral_add (integrable_exp_mul_projPath u v s b l)
      (integrable_exp_mul_projPath u v s (-b) l)
  rw [hGint]
  have hsum : ∑ l : Fin m, ((∫ ω, Real.exp (b * projPath u v s ω l) ∂(projMeasure m N)) +
      ∫ ω, Real.exp (-b * projPath u v s ω l) ∂(projMeasure m N)) ≤
      ∑ _l : Fin m, 2 * Real.exp (b ^ 2 / 2 * B') := by
    refine Finset.sum_le_sum fun l _ => ?_
    have := hI b l
    have := hI (-b) l
    rw [neg_sq] at this
    linarith
  calc C₀ * ((1 / (m : ℝ)) * ∑ l : Fin m, _) ≤ C₀ * ((1 / (m : ℝ)) *
        ∑ _l : Fin m, 2 * Real.exp (b ^ 2 / 2 * B')) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) hC₀
    _ = 2 * C₀ * Real.exp (b ^ 2 / 2 * B') := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp




theorem continuous_projPath_uncurry (v s : ℝ) :
    Continuous fun x : (Fin m → Fin N → ℝ) × ((Fin m → ℝ) × (Fin N → ℝ)) =>
      projPath x.1 v s x.2 := by
  refine continuous_pi fun l => ?_
  simp only [projPath, dotProduct]
  fun_prop

theorem ExpTame.measurable_projSum (hV : ExpTame V) (v s : ℝ) (r : ℕ) :
    Measurable fun u : Fin m → Fin N → ℝ => projSum V u v r s := by
  unfold projSum
  refine Finset.measurable_sum _ fun p _ => Measurable.mul ?_ ?_
  · refine Finset.measurable_prod _ fun i _ => ?_
    simp only [projGram, dotProduct]
    fun_prop
  · have hc : Continuous fun x : (Fin m → Fin N → ℝ) × ((Fin m → ℝ) × (Fin N → ℝ)) =>
        derivProd V (pairCount p) (projPath x.1 v s x.2) :=
      ((hV.contDiff_derivProd (pairCount p)).continuous).comp (continuous_projPath_uncurry v s)
    exact (hc.stronglyMeasurable.integral_prod_right' (ν := projMeasure m N)).measurable


theorem abs_dotProduct_le_of_self_le {N : ℕ} {B : ℝ} (x y : Fin N → ℝ) (hx : x ⬝ᵥ x ≤ B)
    (hy : y ⬝ᵥ y ≤ B) : |x ⬝ᵥ y| ≤ B := by
  have h1 : 0 ≤ (x + y) ⬝ᵥ (x + y) := dotProduct_self_star_nonneg _
  have h2 : 0 ≤ (x - y) ⬝ᵥ (x - y) := dotProduct_self_star_nonneg _
  simp only [add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub,
    dotProduct_comm y x] at h1 h2
  rw [abs_le]
  constructor <;> linarith

theorem abs_projGram_le {N : ℕ} {B : ℝ} (u : Fin m → Fin N → ℝ) (v : ℝ)
    (hu : ∀ l, u l ⬝ᵥ u l ≤ B) (hv : v ^ 2 ≤ B) (hB : 0 ≤ B) (l k : Fin m) :
    |projGram u v l k| ≤ 2 * B := by
  unfold projGram
  have h1 := abs_dotProduct_le_of_self_le (u l) (u k) (hu l) (hu k)
  by_cases h : l = k
  · simp only [h, ite_true]
    have : 0 ≤ u k ⬝ᵥ u k := dotProduct_self_star_nonneg _
    have h3 := hu k
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg v]
  · simp only [h, ite_false, sub_zero]
    linarith

theorem ExpTame.exists_abs_projSum_le (hV : ExpTame V) (hm : 0 < m) (r : ℕ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (u : Fin m → Fin N → ℝ) (v s : ℝ),
      (∀ l, u l ⬝ᵥ u l ≤ B) → v ^ 2 ≤ B →
        |projSum V u v r s| ≤ C * ∑ p : Fin r → Fin m × Fin m, |pairProd (projGram u v) p| := by
  choose C hC0 hC using fun a : Fin m → ℕ => hV.exists_abs_integral_derivProd_projPath_le hm a B
  refine ⟨∑ p : Fin r → Fin m × Fin m, C (pairCount p), Finset.sum_nonneg fun p _ => hC0 _,
    fun N u v s hu hv => ?_⟩
  unfold projSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [abs_mul, mul_comm]
  refine mul_le_mul ?_ le_rfl (abs_nonneg _) (Finset.sum_nonneg fun p _ => hC0 _)
  exact (hC (pairCount p) N u v s hu hv).trans (Finset.single_le_sum
    (f := fun p => C (pairCount p)) (fun p _ => hC0 _) (Finset.mem_univ p))

theorem continuous_projPath (u : Fin m → Fin N → ℝ) (v s : ℝ) :
    Continuous fun ω : (Fin m → ℝ) × (Fin N → ℝ) => projPath u v s ω := by
  refine continuous_pi fun l => ?_
  simp only [projPath, dotProduct]
  fun_prop

@[simp] theorem projPath_zero (u : Fin m → Fin N → ℝ) (v : ℝ)
    (ω : (Fin m → ℝ) × (Fin N → ℝ)) : projPath u v 0 ω = fun l => v * ω.1 l := by
  funext l
  simp [projPath]

theorem ExpTame.integrable_derivProd_projPath (hV : ExpTame V) (hm : 0 < m)
    (u : Fin m → Fin N → ℝ) (v s : ℝ) (a : Fin m → ℕ) :
    Integrable (fun ω => derivProd V a (projPath u v s ω)) (projMeasure m N) := by
  obtain ⟨C₀, c, hC₀, hc, hbd⟩ := hV.abs_derivProd_le a
  set b : ℝ := m * c with hb
  let G : (Fin m → ℝ) × (Fin N → ℝ) → ℝ := fun ω =>
    C₀ * ((1 / (m : ℝ)) * ∑ l, (Real.exp (b * projPath u v s ω l) +
      Real.exp (-b * projPath u v s ω l)))
  have hGi : Integrable G (projMeasure m N) := by
    refine Integrable.const_mul (Integrable.const_mul (integrable_finsetSum _ fun l _ => ?_) _) _
    exact (integrable_exp_mul_projPath u v s b l).add (integrable_exp_mul_projPath u v s (-b) l)
  have hpt : ∀ ω, |derivProd V a (projPath u v s ω)| ≤ G ω := fun ω => by
    refine (hbd _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hC₀
    have h1 := exp_sum_le_avg_exp hm (fun l => c * |projPath u v s ω l|)
    rw [← Finset.mul_sum] at h1
    refine (le_of_eq_of_le (by rw [Finset.mul_sum]) h1).trans ?_
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => ?_) (by positivity)
    have h2 := exp_abs_le_add (b * projPath u v s ω l)
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ b)] at h2
    rw [← mul_assoc, ← hb, neg_mul]
    exact h2
  have hc_meas : AEStronglyMeasurable (fun ω => derivProd V a (projPath u v s ω))
      (projMeasure m N) :=
    ((hV.contDiff_derivProd a).continuous.comp (continuous_projPath u v s)).aestronglyMeasurable
  exact hGi.mono' hc_meas (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hpt ω)

theorem ExpTame.integrable_derivProd_scale_gaussian (hV : ExpTame V) (hm : 0 < m)
    (v : ℝ) (a : Fin m → ℕ) :
    Integrable (fun ξ : Fin m → ℝ => derivProd V a (fun l => v * ξ l))
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  let u : Fin m → Fin 1 → ℝ := fun _ _ => 0
  have hI := hV.integrable_derivProd_projPath (N := 1) hm u v 0 a
  have heq : (fun ω : (Fin m → ℝ) × (Fin 1 → ℝ) => derivProd V a (projPath u v 0 ω)) =
      fun ω => derivProd V a (fun l => v * ω.1 l) := by
    funext ω
    congr 1
    funext l
    simp [projPath]
  rw [heq] at hI
  have hP : IsProbabilityMeasure (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) := by infer_instance
  have h_int_y : (fun ξ : Fin m → ℝ => ∫ y : Fin 1 → ℝ,
      ‖derivProd V a (fun l => v * ξ l)‖ ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1)) =
      fun ξ => ‖derivProd V a (fun l => v * ξ l)‖ := by
    funext ξ
    rw [integral_const, probReal_univ, one_smul]
  have h_prod := (integrable_prod_iff (f := fun ω : (Fin m → ℝ) × (Fin 1 → ℝ) =>
    derivProd V a (fun l => v * ω.1 l)) (μ := Measure.pi fun _ : Fin m => gaussianReal 0 1)
    (ν := Measure.pi fun _ : Fin 1 => gaussianReal 0 1) hI.aestronglyMeasurable).mp hI
  have h_norm := h_prod.2
  rw [h_int_y] at h_norm
  have hc : Continuous (fun ξ : Fin m → ℝ => derivProd V a (fun l => v * ξ l)) :=
    (hV.contDiff_derivProd a).continuous.comp
      (continuous_pi fun l => continuous_const.mul (continuous_apply l))
  exact Integrable.mono' h_norm hc.aestronglyMeasurable (ae_of_all _ fun _ => le_rfl)

theorem integral_derivProd_projPath_zero (u : Fin m → Fin N → ℝ) (v : ℝ) (a : Fin m → ℕ) :
    ∫ ω, derivProd V a (projPath u v 0 ω) ∂(projMeasure m N) =
      ∫ ξ : Fin m → ℝ, derivProd V a (fun l => v * ξ l)
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  simp_rw [projPath_zero]
  exact integral_prod_fun_fst_of_isProbabilityMeasure
    (Measure.pi fun _ : Fin m => gaussianReal 0 1)
    (Measure.pi fun _ : Fin N => gaussianReal 0 1)
    (fun ξ => derivProd V a (fun l => v * ξ l))

theorem ExpTame.integral_derivProd_projPath_zero_eq_zero (hV : ExpTame V) (hm : 0 < m)
    (u : Fin m → Fin N → ℝ) (v : ℝ) (a : Fin m → ℕ) (j : Fin m) (hj : a j = 0)
    (hV0 : ∫ t, V (v * t) ∂(gaussianReal 0 1) = 0) :
    ∫ ω, derivProd V a (projPath u v 0 ω) ∂(projMeasure m N) = 0 := by
  rw [integral_derivProd_projPath_zero u v a]
  have hprod : (fun ξ : Fin m → ℝ => derivProd V a (fun l => v * ξ l)) =
      fun ξ => ∏ l : Fin m, deriv^[a l] V (v * ξ l) := by
    funext ξ; rfl
  rw [hprod]
  have hI := hV.integrable_derivProd_scale_gaussian hm v a
  rw [hprod] at hI
  refine integral_pi_prod_eq_zero_of_coord_zero
    (μ := fun _ : Fin m => gaussianReal 0 1)
    (fun l t => deriv^[a l] V (v * t)) hI j ?_
  rw [hj]
  exact hV0


end SpinGlasses
