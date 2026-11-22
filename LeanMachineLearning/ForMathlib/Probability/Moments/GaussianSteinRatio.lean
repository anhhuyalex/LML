/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianVector

/-!
# Gaussian integration by parts for a ratio with a normalizer

Talagrand's cavity computation (Section 2.3, the "term created by the denominator") integrates by
parts a quantity `F(X) / Z(Y)^n`, where the numerator `F` depends on one Gaussian family `X` and
the normalizer `Z` on another family `Y` (`Z` is positive and bounded below). With `W` a centered
Gaussian variable jointly Gaussian with `(X, Y)`,

`𝔼[W F(X) / Z(Y)^n] = ∑ₗ 𝔼[W Xₗ] 𝔼[∂ₗF(X) / Z(Y)^n]
  - n ∑ₘ 𝔼[W Yₘ] 𝔼[F(X) ∂ₘZ(Y) / Z(Y)^{n+1}]`.

* `integral_mul_div_pow_eq_sum`: the identity for bounded `F` with bounded partials.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω κ₁ κ₂ κ₃ : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [Finite κ₁] [Fintype κ₂] [Fintype κ₃] [DecidableEq κ₂] [DecidableEq κ₃]

/-- **Gaussian integration by parts with a normalizer.** -/
theorem integral_mul_div_pow_eq_sum {W : κ₁ → Ω → ℝ} {X : κ₂ → Ω → ℝ} {Y : κ₃ → Ω → ℝ}
    (hWXY : HasGaussianLaw (fun ω s => Sum.elim W (Sum.elim X Y) s ω) P)
    (hW : ∀ k, ∫ ω, W k ω ∂P = 0) (hX : ∀ l, ∫ ω, X l ω ∂P = 0)
    (hY : ∀ m, ∫ ω, Y m ω ∂P = 0) (i : κ₁)
    {F : (κ₂ → ℝ) → ℝ} (hF : Differentiable ℝ F) {C : ℝ} (hFb : ∀ x, |F x| ≤ C)
    {D : κ₂ → ℝ} (hFd : ∀ l x, |fderiv ℝ F x (Pi.single l 1)| ≤ D l)
    {Z : (κ₃ → ℝ) → ℝ} (hZ : Differentiable ℝ Z) {z₀ : ℝ} (hz₀ : 0 < z₀)
    (hZb : ∀ y, z₀ ≤ Z y) {DZ : κ₃ → ℝ} (hZd : ∀ m y, |fderiv ℝ Z y (Pi.single m 1)| ≤ DZ m)
    (n : ℕ) :
    ∫ ω, W i ω * (F (fun l => X l ω) / Z (fun m => Y m ω) ^ n) ∂P =
      (∑ l, (∫ ω, W i ω * X l ω ∂P) *
        ∫ ω, fderiv ℝ F (fun k => X k ω) (Pi.single l 1) / Z (fun m => Y m ω) ^ n ∂P) -
      n * ∑ m, (∫ ω, W i ω * Y m ω ∂P) *
        ∫ ω, F (fun l => X l ω) * fderiv ℝ Z (fun k => Y k ω) (Pi.single m 1) /
          Z (fun k => Y k ω) ^ (n + 1) ∂P := by
  classical
  let Rx : (κ₂ ⊕ κ₃ → ℝ) →L[ℝ] (κ₂ → ℝ) :=
    ContinuousLinearMap.pi fun l => ContinuousLinearMap.proj (Sum.inl l)
  let Ry : (κ₂ ⊕ κ₃ → ℝ) →L[ℝ] (κ₃ → ℝ) :=
    ContinuousLinearMap.pi fun m => ContinuousLinearMap.proj (Sum.inr m)
  have hRx : ∀ v, Rx v = fun l => v (Sum.inl l) := fun v => rfl
  have hRy : ∀ v, Ry v = fun m => v (Sum.inr m) := fun v => rfl
  have hZne : ∀ y, Z y ≠ 0 := fun y => (hz₀.trans_le (hZb y)).ne'
  let Φ : (κ₂ ⊕ κ₃ → ℝ) → ℝ := fun v => F (Rx v) / Z (Ry v) ^ n
  have hΦd : Differentiable ℝ Φ := by
    intro v
    have h1 : DifferentiableAt ℝ (fun w => F (Rx w)) v := (hF.comp Rx.differentiable) v
    have h2 : DifferentiableAt ℝ (fun w => Z (Ry w) ^ n) v :=
      ((hZ.comp Ry.differentiable) v).fun_pow n
    have h3 : DifferentiableAt ℝ (fun w => F (Rx w) * (Z (Ry w) ^ n)⁻¹) v :=
      h1.mul (h2.inv (pow_ne_zero _ (hZne _)))
    change DifferentiableAt ℝ (fun w => F (Rx w) / Z (Ry w) ^ n) v
    simpa only [div_eq_mul_inv] using h3
  -- the directional derivative of `Φ` as an ordinary derivative along a line
  have hline (v e : κ₂ ⊕ κ₃ → ℝ) :
      HasDerivAt (fun t : ℝ => Φ (v + t • e)) (fderiv ℝ Φ v e) 0 := by
    have hf : HasDerivAt (fun t : ℝ => v + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add v
    have := (hΦd (v + (0 : ℝ) • e)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf
    simp only [zero_smul, add_zero] at this
    exact this
  have hdx (v : κ₂ ⊕ κ₃ → ℝ) (l : κ₂) :
      fderiv ℝ Φ v (Pi.single (Sum.inl l) 1) =
        fderiv ℝ F (Rx v) (Pi.single l 1) / Z (Ry v) ^ n := by
    refine (hline v _).unique ?_
    have hRe : Rx (Pi.single (Sum.inl l) (1 : ℝ)) = Pi.single l 1 := by
      ext m; simp [hRx, Pi.single_apply]
    have hRe' : Ry (Pi.single (Sum.inl l) (1 : ℝ)) = 0 := by
      ext m; simp [hRy]
    have hfun : (fun t : ℝ => Φ (v + t • Pi.single (Sum.inl l) (1 : ℝ))) =
        fun t => F (Rx v + t • Pi.single l 1) / Z (Ry v) ^ n := by
      funext t; simp [Φ, map_add, map_smul, hRe, hRe']
    rw [hfun]
    have hl : HasDerivAt (fun t : ℝ => Rx v + t • (Pi.single l (1 : ℝ) : κ₂ → ℝ))
        (Pi.single l 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single l (1 : ℝ) : κ₂ → ℝ)).const_add
        (Rx v)
    have := ((hF (Rx v + (0 : ℝ) • (Pi.single l (1 : ℝ) : κ₂ → ℝ))).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) hl).div_const (Z (Ry v) ^ n)
    simpa using this
  have hdy (v : κ₂ ⊕ κ₃ → ℝ) (m : κ₃) :
      fderiv ℝ Φ v (Pi.single (Sum.inr m) 1) =
        -(n * (F (Rx v) * fderiv ℝ Z (Ry v) (Pi.single m 1) / Z (Ry v) ^ (n + 1))) := by
    refine (hline v _).unique ?_
    have hRe : Ry (Pi.single (Sum.inr m) (1 : ℝ)) = Pi.single m 1 := by
      ext k; simp [hRy, Pi.single_apply]
    have hRe' : Rx (Pi.single (Sum.inr m) (1 : ℝ)) = 0 := by
      ext k; simp [hRx]
    have hfun : (fun t : ℝ => Φ (v + t • Pi.single (Sum.inr m) (1 : ℝ))) =
        fun t => F (Rx v) / Z (Ry v + t • Pi.single m 1) ^ n := by
      funext t; simp [Φ, map_add, map_smul, hRe, hRe']
    rw [hfun]
    have hl : HasDerivAt (fun t : ℝ => Ry v + t • (Pi.single m (1 : ℝ) : κ₃ → ℝ))
        (Pi.single m 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single m (1 : ℝ) : κ₃ → ℝ)).const_add
        (Ry v)
    have hZl := (hZ (Ry v + (0 : ℝ) • (Pi.single m (1 : ℝ) : κ₃ → ℝ))).hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) hl
    have hg : HasDerivAt (fun t : ℝ => Z (Ry v + t • (Pi.single m (1 : ℝ) : κ₃ → ℝ)))
        (fderiv ℝ Z (Ry v) (Pi.single m 1)) 0 := by
      simpa [Function.comp_def] using hZl
    have hg0 : Z (Ry v + (0 : ℝ) • (Pi.single m (1 : ℝ) : κ₃ → ℝ)) = Z (Ry v) := by simp
    have hp := hg.fun_pow n
    have hi := hp.inv (by rw [hg0]; exact pow_ne_zero _ (hZne _))
    have hq := hi.const_mul (F (Rx v))
    simp only [hg0] at hq
    have hfun2 : (fun t : ℝ => F (Rx v) / Z (Ry v + t • Pi.single m 1) ^ n) =
        fun t => F (Rx v) * (Z (Ry v + t • (Pi.single m (1 : ℝ) : κ₃ → ℝ)) ^ n)⁻¹ := by
      funext t; rw [div_eq_mul_inv]
    rw [hfun2]
    refine hq.congr_deriv ?_
    rcases n with _ | k
    · simp
    · have hz := hZne (Ry v)
      simp only [Nat.add_sub_cancel]
      field_simp
      ring
  have hvx : ∀ ω, Rx (fun k => Sum.elim X Y k ω) = fun l => X l ω := fun ω => rfl
  have hvy : ∀ ω, Ry (fun k => Sum.elim X Y k ω) = fun m => Y m ω := fun ω => rfl
  have hzn : 0 < z₀ ^ n := pow_pos hz₀ n
  have hzn' : 0 < z₀ ^ (n + 1) := pow_pos hz₀ (n + 1)
  have hΦb (v : κ₂ ⊕ κ₃ → ℝ) : |Φ v| ≤ C / z₀ ^ n := by
    simp only [Φ, abs_div]
    have hZp : z₀ ^ n ≤ |Z (Ry v) ^ n| := by
      rw [abs_of_pos (pow_pos (hz₀.trans_le (hZb _)) n)]
      exact pow_le_pow_left₀ hz₀.le (hZb _) n
    have hC : 0 ≤ C := (abs_nonneg _).trans (hFb 0)
    exact (div_le_div₀ hC (hFb _) hzn hZp)
  have hΦg : ∀ v : κ₂ ⊕ κ₃ → ℝ, |Φ v| ≤ C / z₀ ^ n * Real.exp (0 * ∑ s, |v s|) := fun v => by
    simpa using hΦb v
  have hΦ' : ∀ (s : κ₂ ⊕ κ₃) (v : κ₂ ⊕ κ₃ → ℝ),
      |fderiv ℝ Φ v (Pi.single s 1)| ≤
        Sum.elim (fun l => D l / z₀ ^ n) (fun m => n * C * DZ m / z₀ ^ (n + 1)) s *
          Real.exp (0 * ∑ s, |v s|) := by
    rintro (l | m) v
    · simp only [hdx, Sum.elim_inl, zero_mul, Real.exp_zero, mul_one, abs_div]
      rw [abs_of_pos (pow_pos (hz₀.trans_le (hZb _)) n)]
      exact div_le_div₀ ((abs_nonneg _).trans (hFd l (Rx v))) (hFd l _) hzn
        (pow_le_pow_left₀ hz₀.le (hZb _) n)
    · simp only [hdy, Sum.elim_inr, zero_mul, Real.exp_zero, mul_one, abs_neg, abs_mul, abs_div]
      have hC : 0 ≤ C := (abs_nonneg _).trans (hFb 0)
      rw [abs_of_pos (pow_pos (hz₀.trans_le (hZb _)) (n + 1)), Nat.abs_cast]
      have hDZ : 0 ≤ DZ m := (abs_nonneg _).trans (hZd m 0)
      calc (n : ℝ) * (|F (Rx v)| * |fderiv ℝ Z (Ry v) (Pi.single m 1)| / Z (Ry v) ^ (n + 1))
          ≤ (n : ℝ) * (C * DZ m / z₀ ^ (n + 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            exact div_le_div₀ (mul_nonneg hC hDZ)
              (mul_le_mul (hFb _) (hZd m _) (abs_nonneg _) hC) hzn'
              (pow_le_pow_left₀ hz₀.le (hZb _) _)
        _ = _ := by ring
  have h := integral_mul_comp_eq_sum_integral_mul_of_sum (W := W) (X := Sum.elim X Y) hWXY hW
    (by rintro (l | m); exacts [hX l, hY m]) i hΦd (C := C / z₀ ^ n) (c := 0) hΦg
    (D := Sum.elim (fun l => D l / z₀ ^ n) (fun m => n * C * DZ m / z₀ ^ (n + 1)))
    (d := fun _ => 0) (fun s v => by simpa using hΦ' s v)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hdx, hdy, hvx, hvy] at h
  have e1 : ∀ ω, Φ (fun k => Sum.elim X Y k ω) = F (fun l => X l ω) / Z (fun m => Y m ω) ^ n :=
    fun ω => rfl
  simp only [e1] at h
  rw [h]
  have hneg : ∀ m, (∫ ω, W i ω * Y m ω ∂P) * ∫ ω, -((n : ℝ) *
      (F (fun l => X l ω) * fderiv ℝ Z (fun k => Y k ω) (Pi.single m 1) /
        Z (fun k => Y k ω) ^ (n + 1))) ∂P =
      -((n : ℝ) * ((∫ ω, W i ω * Y m ω ∂P) * ∫ ω, F (fun l => X l ω) *
        fderiv ℝ Z (fun k => Y k ω) (Pi.single m 1) / Z (fun k => Y k ω) ^ (n + 1) ∂P)) := by
    intro m
    rw [integral_neg, integral_const_mul]
    ring
  simp_rw [hneg]
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  ring

end ProbabilityTheory
