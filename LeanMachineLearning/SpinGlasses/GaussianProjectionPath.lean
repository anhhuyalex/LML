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
multi-index `a`, the products `∏ ℓ, deriv^[a ℓ] V (x ℓ)` (that is, `∏ ℓ, V^{(a ℓ)} (x ℓ)`) are closed under the
partial derivatives `∂_k` (`a ↦ a + e_k`).  Writing `T_{l k} = u l ⬝ u k - v² δ_{l k}`
(`projGram`), Gaussian interpolation gives

`(d/ds) 𝔼 ∏ ℓ, deriv^[a ℓ] V (Z_s ℓ) = sin s cos s ∑_{l,k} T_{l k} 𝔼 ∏ ℓ, deriv^[(a + e_l + e_k) ℓ] V (Z_s ℓ)`.

Iterating, `projSum V u v r s` (a sum over lists of `r` pairs of the products of entries of `T`
against `𝔼 ∏ ℓ, deriv^[pairCount p ℓ] V (Z_s ℓ)`) satisfies
`(d/ds) projSum r = sin s cos s · projSum (r + 1)`.

## Main declarations

* `SpinGlasses.ExpTame`: smooth functions with exponentially bounded derivatives.
* `SpinGlasses.ExpTame.hasDerivAt_integral_derivProd_projPath`: the first derivative.
* `SpinGlasses.ExpTame.hasDerivAt_projSum`: the iterated derivative structure.
* `SpinGlasses.exists_abs_projSum_le_of_bound`: a bound uniform in the data, in `N` and in all `V`
  with the same explicit exponential bounds on their derivatives.
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

variable {m : ℕ} {V : ℝ → ℝ}

open scoped ContDiff in
theorem ExpTame.contDiff_derivProd (hV : ExpTame V) (a : Fin m → ℕ) :
    ContDiff ℝ ∞ (fun x : Fin m → ℝ => ∏ ℓ, deriv^[a ℓ] V (x ℓ)) := by
  refine contDiff_prod fun ℓ _ => ?_
  exact (hV.contDiff.iterate_deriv (a ℓ)).comp (contDiff_apply ℝ ℝ ℓ)

theorem ExpTame.hasFDerivAt_derivProd (hV : ExpTame V) (a : Fin m → ℕ) (x : Fin m → ℝ)
    (k : Fin m) :
    fderiv ℝ (fun x : Fin m → ℝ => ∏ ℓ, deriv^[a ℓ] V (x ℓ)) x (Pi.single k 1) = ∏ ℓ, deriv^[(a + Pi.single k 1 : Fin m → ℕ) ℓ] V (x ℓ) := by
  classical
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


/-- Finitely many derivatives of an exponentially tame function have a common exponential rate. -/
theorem ExpTame.exists_bound_upTo (hV : ExpTame V) (J : ℕ) :
    ∃ (Cb : ℕ → ℝ) (c : ℝ), (∀ j, 0 ≤ Cb j) ∧ 0 ≤ c ∧
      ∀ j ≤ J, ∀ x, |deriv^[j] V x| ≤ Cb j * Real.exp (c * |x|) := by
  choose C cc hC hcc h using hV.bound
  refine ⟨C, ∑ j ∈ Finset.range (J + 1), cc j, hC, Finset.sum_nonneg fun j _ => hcc j,
    fun j hj x => (h j x).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hC j))⟩
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := cc) (fun i _ => hcc i)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hj))) (abs_nonneg x)

/-- The bound on `∏ ℓ, deriv^[a ℓ] V (y ℓ)` from explicit bounds on the derivatives of `V` up to order `J`. -/
theorem abs_derivProd_le_of_bound {J : ℕ} {Cb : ℕ → ℝ} {c : ℝ} (hCb : ∀ j ≤ J, 0 ≤ Cb j)
    (hc : 0 ≤ c) (hbd : ∀ j ≤ J, ∀ x, |deriv^[j] V x| ≤ Cb j * Real.exp (c * |x|))
    (a : Fin m → ℕ) (ha : ∀ ℓ, a ℓ ≤ J) (y : Fin m → ℝ) :
    |∏ ℓ, deriv^[a ℓ] V (y ℓ)| ≤ (∏ ℓ, Cb (a ℓ)) * Real.exp ((m * c) * ∑ l, |y l|) := by
  have hS : ∀ ℓ, |y ℓ| ≤ ∑ l, |y l| := fun ℓ =>
    Finset.single_le_sum (f := fun l => |y l|) (fun _ _ => abs_nonneg _) (Finset.mem_univ ℓ)
  rw [Finset.abs_prod]
  calc ∏ ℓ, |deriv^[a ℓ] V (y ℓ)| ≤ ∏ ℓ, (Cb (a ℓ) * Real.exp (c * |y ℓ|)) :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun ℓ _ => hbd (a ℓ) (ha ℓ) (y ℓ)
    _ = (∏ ℓ, Cb (a ℓ)) * Real.exp (∑ ℓ, c * |y ℓ|) := by
        rw [Finset.prod_mul_distrib, Real.exp_sum]
    _ ≤ (∏ ℓ, Cb (a ℓ)) * Real.exp ((m * c) * ∑ l, |y l|) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_)
          (Finset.prod_nonneg fun ℓ _ => hCb _ (ha ℓ))
        calc ∑ ℓ, c * |y ℓ| ≤ ∑ _ℓ : Fin m, c * ∑ l, |y l| :=
              Finset.sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_left (hS ℓ) hc
          _ = (m * c) * ∑ l, |y l| := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              ring

theorem ExpTame.abs_derivProd_le (hV : ExpTame V) (a : Fin m → ℕ) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 ≤ c ∧ ∀ y : Fin m → ℝ, |∏ ℓ, deriv^[a ℓ] V (y ℓ)| ≤ C * Real.exp (c * ∑ l, |y l|) := by
  obtain ⟨Cb, c, hCb, hc, hbd⟩ := hV.exists_bound_upTo (∑ ℓ, a ℓ)
  exact ⟨∏ ℓ, Cb (a ℓ), m * c, Finset.prod_nonneg fun ℓ _ => hCb _, by positivity,
    abs_derivProd_le_of_bound (fun j _ => hCb j) hc hbd a fun ℓ =>
      Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ℓ)⟩


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
    HasDerivAt (fun s => ∫ ω, ∏ ℓ, deriv^[a ℓ] V (projPath u v s ω ℓ)
        ∂((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)))
      (Real.sin t * Real.cos t * ∑ l, ∑ k, projGram u v l k *
        ∫ ω, ∏ ℓ, deriv^[(a + Pi.single l 1 + Pi.single k 1 : Fin m → ℕ) ℓ] V (projPath u v t ω ℓ)
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
  have hFc : ContDiff ℝ 2 (fun x : Fin m → ℝ => ∏ ℓ, deriv^[a ℓ] V (x ℓ)) := (hV.contDiff_derivProd a).of_le (by simp)
  have hfd : ∀ (b : Fin m → ℕ) (l : Fin m) (y : Fin m → ℝ),
      fderiv ℝ (fun x : Fin m → ℝ => ∏ ℓ, deriv^[b ℓ] V (x ℓ)) y (Pi.single l 1) = ∏ ℓ, deriv^[(b + Pi.single l 1 : Fin m → ℕ) ℓ] V (y ℓ) :=
    fun b l y => hV.hasFDerivAt_derivProd b y l
  obtain ⟨C₀, c₀, hC₀, hc₀, hF0⟩ := hV.abs_derivProd_le a
  choose C₁ c₁ hC₁ hc₁ hF1 using fun l : Fin m => hV.abs_derivProd_le (a + Pi.single l 1)
  choose C₂ c₂ hC₂ hc₂ hF2 using fun (k l : Fin m) =>
    hV.abs_derivProd_le (a + Pi.single l 1 + Pi.single k 1)
  have hS : ∀ y : Fin m → ℝ, 0 ≤ ∑ l, |y l| := fun y => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h := hasDerivAt_integral_comp_trig (X := X) (Y := Y) (P := P) hXY hX hY h0
    (F := (fun x : Fin m → ℝ => ∏ ℓ, deriv^[a ℓ] V (x ℓ))) hFc (C₀ := C₀) (c₀ := c₀) hF0 (D := C₁) (c₁ := ∑ l, c₁ l)
    (fun l y => by
      rw [hfd]
      exact (hF1 l y).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := c₁) (fun _ _ => hc₁ _)
          (Finset.mem_univ l)) (hS y))) (hC₁ l)))
    (D2 := C₂) (c₂ := ∑ k, ∑ l, c₂ k l)
    (fun k l y => by
      have : (fun y => fderiv ℝ (fun x : Fin m → ℝ => ∏ ℓ, deriv^[a ℓ] V (x ℓ)) y (Pi.single l 1)) =
          (fun x : Fin m → ℝ => ∏ ℓ, deriv^[(a + Pi.single l 1 : Fin m → ℕ) ℓ] V (x ℓ)) := funext fun y => hfd a l y
      rw [this, hfd]
      refine (hF2 k l y).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
        (mul_le_mul_of_nonneg_right ?_ (hS y))) (hC₂ k l))
      exact (Finset.single_le_sum (f := c₂ k) (fun _ _ => hc₂ _ _) (Finset.mem_univ l)).trans
        (Finset.single_le_sum (f := fun k => ∑ l, c₂ k l) (fun _ _ =>
          Finset.sum_nonneg fun _ _ => hc₂ _ _) (Finset.mem_univ k))) t
  refine h.congr_deriv ?_
  congr 1
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  have e1 : (fun y => fderiv ℝ (fun x : Fin m → ℝ => ∏ ℓ, deriv^[a ℓ] V (x ℓ)) y (Pi.single l 1)) =
      (fun x : Fin m → ℝ => ∏ ℓ, deriv^[(a + Pi.single l 1 : Fin m → ℕ) ℓ] V (x ℓ)) := funext fun y => hfd a l y
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
    ∫ ω, ∏ ℓ, deriv^[pairCount p ℓ] V (projPath u v s ω ℓ)
      ∂((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1))

theorem ExpTame.hasDerivAt_projSum (hV : ExpTame V) (u : Fin m → Fin N → ℝ) (v : ℝ) (r : ℕ)
    (t : ℝ) :
    HasDerivAt (projSum V u v r) (Real.sin t * Real.cos t * projSum V u v (r + 1) t) t := by
  classical
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (A := fun (p : Fin r → Fin m × Fin m) (s : ℝ) => pairProd (projGram u v) p *
      ∫ ω, ∏ ℓ, deriv^[pairCount p ℓ] V (projPath u v s ω ℓ)
        ∂((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)))
    (A' := fun (p : Fin r → Fin m × Fin m) => pairProd (projGram u v) p *
      (Real.sin t * Real.cos t * ∑ l, ∑ k, projGram u v l k *
        ∫ ω, ∏ ℓ, deriv^[(pairCount p + Pi.single l 1 + Pi.single k 1) ℓ] V (projPath u v t ω ℓ)
          ∂((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin N => gaussianReal 0 1))))
    (fun p _ => (hV.hasDerivAt_integral_derivProd_projPath u v (pairCount p) t).const_mul
      (pairProd (projGram u v) p))
  unfold projSum
  refine h.congr_deriv ?_
  have hc := (Fin.consEquiv (fun _ : Fin (r + 1) => Fin m × Fin m)).sum_comp
    (fun p' : Fin (r + 1) → Fin m × Fin m => pairProd (projGram u v) p' *
      ∫ ω, ∏ ℓ, deriv^[pairCount p' ℓ] V (projPath u v t ω ℓ)
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

theorem abs_integral_derivProd_projPath_le {C₀ c : ℝ} (hm : 0 < m) (a : Fin m → ℕ) (B : ℝ)
    (hC₀ : 0 ≤ C₀) (hc : 0 ≤ c)
    (hbd : ∀ y : Fin m → ℝ, |∏ ℓ, deriv^[a ℓ] V (y ℓ)| ≤ C₀ * Real.exp (c * ∑ l, |y l|)) :
    ∀ (N : ℕ) (u : Fin m → Fin N → ℝ) (v s : ℝ),
      (∀ l, u l ⬝ᵥ u l ≤ B) → v ^ 2 ≤ B →
        |∫ ω, ∏ ℓ, deriv^[a ℓ] V (projPath u v s ω ℓ) ∂(projMeasure m N)| ≤
          2 * C₀ * Real.exp ((m * c) ^ 2 / 2 * max B 0) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set B' : ℝ := max B 0 with hB'
  intro N u v s hu hv
  set b : ℝ := m * c with hb
  let G : (Fin m → ℝ) × (Fin N → ℝ) → ℝ := fun ω =>
    C₀ * ((1 / (m : ℝ)) * ∑ l, (Real.exp (b * projPath u v s ω l) +
      Real.exp (-b * projPath u v s ω l)))
  have hGi : Integrable G (projMeasure m N) := by
    refine Integrable.const_mul (Integrable.const_mul (integrable_finsetSum _ fun l _ => ?_) _) _
    exact (integrable_exp_mul_projPath u v s b l).add (integrable_exp_mul_projPath u v s (-b) l)
  have hpt : ∀ ω, |∏ ℓ, deriv^[a ℓ] V (projPath u v s ω ℓ)| ≤ G ω := fun ω => by
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
  have hnorm := norm_integral_le_of_norm_le hGi (f := fun ω => ∏ ℓ, deriv^[a ℓ] V (projPath u v s ω ℓ))
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
        ∏ ℓ, deriv^[pairCount p ℓ] V (projPath x.1 v s x.2 ℓ) :=
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

theorem pairCount_le {r : ℕ} (p : Fin r → Fin m × Fin m) (ℓ : Fin m) : pairCount p ℓ ≤ 2 * r := by
  rw [← sum_pairCount p]
  exact Finset.single_le_sum (f := fun ℓ => pairCount p ℓ) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ ℓ)

/-- **Uniform bound on the path functional.**  The constant `C` depends only on `m`, `r`, `B`
and on explicit exponential bounds `Cb`, `c` for the derivatives of `V` up to order `2 r`,
not on `V` itself. -/
theorem exists_abs_projSum_le_of_bound (hm : 0 < m) (r : ℕ) (B : ℝ) {Cb : ℕ → ℝ} {c : ℝ}
    (hCb : ∀ j ≤ 2 * r, 0 ≤ Cb j) (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : ℝ → ℝ),
      (∀ j ≤ 2 * r, ∀ x, |deriv^[j] V x| ≤ Cb j * Real.exp (c * |x|)) →
      ∀ (N : ℕ) (u : Fin m → Fin N → ℝ) (v s : ℝ), (∀ l, u l ⬝ᵥ u l ≤ B) → v ^ 2 ≤ B →
        |projSum V u v r s| ≤ C * ∑ p : Fin r → Fin m × Fin m, |pairProd (projGram u v) p| := by
  set K : (Fin r → Fin m × Fin m) → ℝ := fun p =>
    2 * (∏ ℓ, Cb (pairCount p ℓ)) * Real.exp ((m * (m * c)) ^ 2 / 2 * max B 0) with hK
  have hK0 : ∀ p, 0 ≤ K p := fun p => by
    simp only [hK]
    exact mul_nonneg (mul_nonneg (by norm_num)
      (Finset.prod_nonneg fun ℓ _ => hCb _ (pairCount_le p ℓ))) (Real.exp_pos _).le
  refine ⟨∑ p, K p, Finset.sum_nonneg fun p _ => hK0 p, fun V hbd N u v s hu hv => ?_⟩
  unfold projSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [abs_mul, mul_comm]
  refine mul_le_mul ?_ le_rfl (abs_nonneg _) (Finset.sum_nonneg fun p _ => hK0 p)
  have hder := abs_integral_derivProd_projPath_le hm (pairCount p) B
    (Finset.prod_nonneg fun ℓ _ => hCb _ (pairCount_le p ℓ)) (by positivity)
    (abs_derivProd_le_of_bound (fun j hj => hCb j hj) hc hbd (pairCount p)
      (fun ℓ => pairCount_le p ℓ)) N u v s hu hv
  exact hder.trans ((Finset.single_le_sum (f := K) (fun p _ => hK0 p) (Finset.mem_univ p)))

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
    Integrable (fun ω => ∏ ℓ, deriv^[a ℓ] V (projPath u v s ω ℓ)) (projMeasure m N) := by
  obtain ⟨C₀, c, hC₀, hc, hbd⟩ := hV.abs_derivProd_le a
  set b : ℝ := m * c with hb
  let G : (Fin m → ℝ) × (Fin N → ℝ) → ℝ := fun ω =>
    C₀ * ((1 / (m : ℝ)) * ∑ l, (Real.exp (b * projPath u v s ω l) +
      Real.exp (-b * projPath u v s ω l)))
  have hGi : Integrable G (projMeasure m N) := by
    refine Integrable.const_mul (Integrable.const_mul (integrable_finsetSum _ fun l _ => ?_) _) _
    exact (integrable_exp_mul_projPath u v s b l).add (integrable_exp_mul_projPath u v s (-b) l)
  have hpt : ∀ ω, |∏ ℓ, deriv^[a ℓ] V (projPath u v s ω ℓ)| ≤ G ω := fun ω => by
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
  have hc_meas : AEStronglyMeasurable (fun ω => ∏ ℓ, deriv^[a ℓ] V (projPath u v s ω ℓ))
      (projMeasure m N) :=
    ((hV.contDiff_derivProd a).continuous.comp (continuous_projPath u v s)).aestronglyMeasurable
  exact hGi.mono' hc_meas (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hpt ω)

theorem ExpTame.integrable_derivProd_scale_gaussian (hV : ExpTame V) (hm : 0 < m)
    (v : ℝ) (a : Fin m → ℕ) :
    Integrable (fun ξ : Fin m → ℝ => ∏ ℓ, deriv^[a ℓ] V (v * ξ ℓ))
      (Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  let u : Fin m → Fin 1 → ℝ := fun _ _ => 0
  have hI := hV.integrable_derivProd_projPath (N := 1) hm u v 0 a
  have heq : (fun ω : (Fin m → ℝ) × (Fin 1 → ℝ) => ∏ ℓ, deriv^[a ℓ] V (projPath u v 0 ω ℓ)) =
      fun ω => ∏ ℓ, deriv^[a ℓ] V (v * ω.1 ℓ) := by
    funext ω
    congr 1
    funext l
    simp [projPath]
  rw [heq] at hI
  have hP : IsProbabilityMeasure (Measure.pi fun _ : Fin 1 => gaussianReal 0 1) := by infer_instance
  have h_int_y : (fun ξ : Fin m → ℝ => ∫ y : Fin 1 → ℝ,
      ‖∏ ℓ, deriv^[a ℓ] V (v * ξ ℓ)‖ ∂(Measure.pi fun _ : Fin 1 => gaussianReal 0 1)) =
      fun ξ => ‖∏ ℓ, deriv^[a ℓ] V (v * ξ ℓ)‖ := by
    funext ξ
    rw [integral_const, probReal_univ, one_smul]
  have h_prod := (integrable_prod_iff (f := fun ω : (Fin m → ℝ) × (Fin 1 → ℝ) =>
    ∏ ℓ, deriv^[a ℓ] V (v * ω.1 ℓ)) (μ := Measure.pi fun _ : Fin m => gaussianReal 0 1)
    (ν := Measure.pi fun _ : Fin 1 => gaussianReal 0 1) hI.aestronglyMeasurable).mp hI
  have h_norm := h_prod.2
  rw [h_int_y] at h_norm
  have hc : Continuous (fun ξ : Fin m → ℝ => ∏ ℓ, deriv^[a ℓ] V (v * ξ ℓ)) :=
    (hV.contDiff_derivProd a).continuous.comp
      (continuous_pi fun l => continuous_const.mul (continuous_apply l))
  exact Integrable.mono' h_norm hc.aestronglyMeasurable (ae_of_all _ fun _ => le_rfl)

theorem integral_derivProd_projPath_zero (u : Fin m → Fin N → ℝ) (v : ℝ) (a : Fin m → ℕ) :
    ∫ ω, ∏ ℓ, deriv^[a ℓ] V (projPath u v 0 ω ℓ) ∂(projMeasure m N) =
      ∫ ξ : Fin m → ℝ, ∏ ℓ, deriv^[a ℓ] V (v * ξ ℓ)
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  simp_rw [projPath_zero]
  exact integral_prod_fun_fst_of_isProbabilityMeasure
    (Measure.pi fun _ : Fin m => gaussianReal 0 1)
    (Measure.pi fun _ : Fin N => gaussianReal 0 1)
    (fun ξ => ∏ ℓ, deriv^[a ℓ] V (v * ξ ℓ))

theorem ExpTame.integral_derivProd_projPath_zero_eq_zero (hV : ExpTame V) (hm : 0 < m)
    (u : Fin m → Fin N → ℝ) (v : ℝ) (a : Fin m → ℕ) (j : Fin m) (hj : a j = 0)
    (hV0 : ∫ t, V (v * t) ∂(gaussianReal 0 1) = 0) :
    ∫ ω, ∏ ℓ, deriv^[a ℓ] V (projPath u v 0 ω ℓ) ∂(projMeasure m N) = 0 := by
  rw [integral_derivProd_projPath_zero u v a]
  have hprod : (fun ξ : Fin m → ℝ => ∏ ℓ, deriv^[a ℓ] V (v * ξ ℓ)) =
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

/-- Derivative of `y ↦ exp (c * y)`. -/
theorem hasDerivAt_exp_mul (c x : ℝ) :
    HasDerivAt (fun y => Real.exp (c * y)) (c * Real.exp (c * x)) x := by
  have h := ((hasDerivAt_id' x).const_mul c).exp
  convert h using 1
  ring

/-- Iterated derivatives of `y ↦ exp (c * y)`. -/
theorem iterate_deriv_exp (c : ℝ) (j : ℕ) (x : ℝ) :
    deriv^[j] (fun y => Real.exp (c * y)) x = c ^ j * Real.exp (c * x) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have h_eq : deriv^[j] (fun y => Real.exp (c * y)) = fun y => c ^ j * Real.exp (c * y) := by
      ext y; exact ih y
    rw [h_eq]
    have h1 := (hasDerivAt_exp_mul c x).const_mul (c ^ j)
    have h : HasDerivAt (fun y => c ^ j * Real.exp (c * y)) (c ^ (j + 1) * Real.exp (c * x)) x := by
      convert h1 using 1
      ring
    exact h.deriv

/-- The exponential function `x ↦ exp(c * x)` is exponentially tame. -/
theorem expTame_exp (c : ℝ) : ExpTame (fun x => Real.exp (c * x)) where
  contDiff := Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  bound j := by
    refine ⟨|c| ^ j, |c|, by positivity, by positivity, fun x => ?_⟩
    rw [iterate_deriv_exp]
    rw [abs_mul, abs_pow, Real.abs_exp]
    have h_le : c * x ≤ |c| * |x| := by
      calc c * x ≤ |c * x| := le_abs_self _
        _ = |c| * |x| := abs_mul c x
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le h_le) (by positivity)

/-- Iterated derivatives of `y ↦ y * exp (c * y)`. -/
theorem iterate_deriv_id_mul_exp (c : ℝ) (j : ℕ) (x : ℝ) :
    deriv^[j] (fun y => y * Real.exp (c * y)) x =
      ((j : ℝ) * c ^ (j - 1) + c ^ j * x) * Real.exp (c * x) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have h_eq : deriv^[j] (fun y => y * Real.exp (c * y)) =
        fun y => ((j : ℝ) * c ^ (j - 1) + c ^ j * y) * Real.exp (c * y) := by
      ext y; exact ih y
    rw [h_eq]
    have h1 : HasDerivAt (fun y => (j : ℝ) * c ^ (j - 1) + c ^ j * y) (c ^ j) x := by
      have h_lin := (hasDerivAt_id' x).const_mul (c ^ j)
      have h_add := h_lin.const_add ((j : ℝ) * c ^ (j - 1))
      convert h_add using 1
      ring
    have h2 := hasDerivAt_exp_mul c x
    have h := h1.mul h2
    change HasDerivAt (fun y => ((j : ℝ) * c ^ (j - 1) + c ^ j * y) * Real.exp (c * y)) _ x at h
    rw [h.deriv]
    simp only [Nat.succ_sub_one]
    cases j with
    | zero =>
      simp only [Nat.zero_sub, pow_zero, CharP.cast_eq_zero, zero_mul, zero_add,
        one_mul, pow_one]
      ring
    | succ m =>
      simp only [Nat.succ_sub_one]
      have h1 : c ^ (m + 1) = c ^ m * c := pow_succ c m
      have h2 : c ^ (m + 1 + 1) = (c ^ m * c) * c := by
        rw [pow_succ c (m + 1), pow_succ c m]
      have h3 : (↑(m + 1 + 1) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
      have h4 : (↑(m + 1) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [h1, h2, h3, h4]
      ring

/-- The function `x ↦ x * exp(c * x)` is exponentially tame. -/
theorem expTame_id_mul_exp (c : ℝ) : ExpTame (fun x => x * Real.exp (c * x)) where
  contDiff := contDiff_id.mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  bound j := by
    refine ⟨2 * ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j), |c| + 1,
      by positivity, by positivity, fun x => ?_⟩
    rw [iterate_deriv_id_mul_exp]
    rw [abs_mul, Real.abs_exp]
    have h_le1 : |(j : ℝ) * c ^ (j - 1) + c ^ j * x| ≤ (j : ℝ) * |c| ^ (j - 1) + |c| ^ j * |x| := by
      calc |(j : ℝ) * c ^ (j - 1) + c ^ j * x|
        _ ≤ |(j : ℝ) * c ^ (j - 1)| + |c ^ j * x| := abs_add_le _ _
        _ = (j : ℝ) * |c| ^ (j - 1) + |c| ^ j * |x| := by
          simp only [abs_mul, abs_pow]
          rw [abs_of_nonneg (by positivity)]
    have h_x_le : |x| ≤ Real.exp |x| := by
      linarith [Real.add_one_le_exp |x|, abs_nonneg x]
    have h_one_le : (1 : ℝ) ≤ Real.exp |x| := by
      have := Real.exp_le_exp_of_le (abs_nonneg x)
      rwa [Real.exp_zero] at this
    have h_poly : (j : ℝ) * |c| ^ (j - 1) + |c| ^ j * |x| ≤
        2 * ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j) * Real.exp |x| := by
      calc (j : ℝ) * |c| ^ (j - 1) + |c| ^ j * |x|
        _ ≤ (j : ℝ) * |c| ^ (j - 1) * Real.exp |x| + |c| ^ j * Real.exp |x| := by
          have h1 : (j : ℝ) * |c| ^ (j - 1) ≤ (j : ℝ) * |c| ^ (j - 1) * Real.exp |x| := by
            calc (j : ℝ) * |c| ^ (j - 1) = (j : ℝ) * |c| ^ (j - 1) * 1 := by ring
              _ ≤ (j : ℝ) * |c| ^ (j - 1) * Real.exp |x| :=
                mul_le_mul_of_nonneg_left h_one_le (by positivity)
          have h2 : |c| ^ j * |x| ≤ |c| ^ j * Real.exp |x| :=
            mul_le_mul_of_nonneg_left h_x_le (by positivity)
          linarith
        _ = ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j) * Real.exp |x| := by ring
        _ ≤ ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j) * Real.exp |x| +
            ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j) * Real.exp |x| :=
          le_add_of_nonneg_right (by positivity)
        _ = 2 * ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j) * Real.exp |x| := by ring
    have h_exp : Real.exp (c * x) ≤ Real.exp (|c| * |x|) := by
      have : c * x ≤ |c| * |x| := (le_abs_self _).trans_eq (abs_mul c x)
      exact Real.exp_le_exp_of_le this
    have h_prod : Real.exp |x| * Real.exp (|c| * |x|) = Real.exp ((|c| + 1) * |x|) := by
      rw [← Real.exp_add]
      ring_nf
    calc |(j : ℝ) * c ^ (j - 1) + c ^ j * x| * Real.exp (c * x)
      _ ≤ ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j * |x|) * Real.exp (|c| * |x|) :=
        mul_le_mul h_le1 h_exp (by positivity) (by positivity)
      _ ≤ (2 * ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j) * Real.exp |x|) * Real.exp (|c| * |x|) :=
        mul_le_mul_of_nonneg_right h_poly (by positivity)
      _ = 2 * ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j) * (Real.exp |x| * Real.exp (|c| * |x|)) := by ring
      _ = 2 * ((j : ℝ) * |c| ^ (j - 1) + |c| ^ j) * Real.exp ((|c| + 1) * |x|) := by rw [h_prod]

/-! ### Exponentially tame functions: shifts and Gaussian averages -/

open scoped ContDiff in
/-- Subtracting a constant preserves exponential tameness. -/
theorem ExpTame.sub_const {V : ℝ → ℝ} (hV : ExpTame V) (c₀ : ℝ) : ExpTame (fun x => V x - c₀) where
  contDiff := hV.contDiff.sub contDiff_const
  bound j := by
    cases j with
    | zero =>
      obtain ⟨C, c, hC, hc, h⟩ := hV.bound 0
      refine ⟨C + |c₀|, c, by positivity, hc, fun x => ?_⟩
      have h1 : 1 ≤ Real.exp (c * |x|) := Real.one_le_exp (by positivity)
      have h2 := h x
      simp only [Function.iterate_zero, id] at h2 ⊢
      calc |V x - c₀| ≤ |V x| + |c₀| := abs_sub _ _
        _ ≤ C * Real.exp (c * |x|) + |c₀| * Real.exp (c * |x|) := by
          gcongr
          exact le_mul_of_one_le_right (abs_nonneg _) h1
        _ = _ := by ring
    | succ j =>
      obtain ⟨C, c, hC, hc, h⟩ := hV.bound (j + 1)
      refine ⟨C, c, hC, hc, fun x => ?_⟩
      have hd : deriv (fun x => V x - c₀) = deriv V := by
        funext y; exact deriv_sub_const c₀
      rw [Function.iterate_succ_apply, hd, ← Function.iterate_succ_apply]
      exact h x

/-- An exponentially tame function of a scaled standard Gaussian is integrable. -/
theorem ExpTame.integrable_comp_mul_gaussianReal {V : ℝ → ℝ} (hV : ExpTame V) (v : ℝ) :
    Integrable (fun t => V (v * t)) (gaussianReal 0 1) := by
  obtain ⟨C, c, hC, hc, h⟩ := hV.bound 0
  refine ((integrable_exp_mul_abs_gaussianReal (c * |v|)).const_mul C).mono'
    (hV.contDiff.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun t => ?_)
  have := h (v * t)
  simp only [Function.iterate_zero, id, abs_mul] at this
  rw [Real.norm_eq_abs]
  calc |V (v * t)| ≤ C * Real.exp (c * (|v| * |t|)) := this
    _ = _ := by rw [mul_assoc]

/-- Centering `U` at its Gaussian mean `∫ U(v t) dγ` gives a function with Gaussian mean zero. -/
theorem ExpTame.integral_sub_const_mul_gaussianReal {V : ℝ → ℝ} (hV : ExpTame V) (v : ℝ) :
    ∫ t, (V (v * t) - ∫ s, V (v * s) ∂(gaussianReal 0 1)) ∂(gaussianReal 0 1) = 0 := by
  rw [integral_sub (hV.integrable_comp_mul_gaussianReal v) (integrable_const _)]
  simp

end SpinGlasses
