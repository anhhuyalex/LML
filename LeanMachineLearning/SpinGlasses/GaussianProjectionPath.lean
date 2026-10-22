/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GaussianCovarianceInterpolation
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IteratedBound

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

end SpinGlasses
