/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.SecondMoment
public import LeanMachineLearning.ForMathlib.Probability.Moments.SubGaussianSymmetrization
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianVector
public import LeanMachineLearning.SpinGlasses.GaussianComparison
public import LeanMachineLearning.SpinGlasses.MixedPSpin

/-!
# Concentration of the free energy

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology Real NNReal

namespace SpinGlasses

section LogSumExp

variable {α : Type*} [Fintype α] [Nonempty α]

/-- **`log ∑ₐ exp (· + h)` is 1-Lipschitz for the sup norm:** if `|uₐ - vₐ| ≤ M` for all `a`, then
`|log ∑ₐ exp (uₐ + hₐ) - log ∑ₐ exp (vₐ + hₐ)| ≤ M`. -/
theorem abs_log_sum_exp_sub_le_of_forall (h u v : α → ℝ) {M : ℝ} (hM : ∀ a, |u a - v a| ≤ M) :
    |Real.log (∑ a, Real.exp (u a + h a)) - Real.log (∑ a, Real.exp (v a + h a))| ≤ M := by
  have key : ∀ u v : α → ℝ, (∀ a, u a - v a ≤ M) → Real.log (∑ a, Real.exp (u a + h a)) -
      Real.log (∑ a, Real.exp (v a + h a)) ≤ M := by
    intro u v huv
    have hu : 0 < ∑ a, Real.exp (u a + h a) :=
      Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
    have hv : 0 < ∑ a, Real.exp (v a + h a) :=
      Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
    rw [sub_le_iff_le_add', ← Real.log_exp M, ← Real.log_mul hv.ne' (Real.exp_pos _).ne']
    refine Real.log_le_log hu ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith [huv a])
  rw [abs_le]
  refine ⟨?_, key u v fun a => (le_abs_self _).trans (hM a)⟩
  have := key v u fun a => (le_abs_self _).trans ((abs_sub_comm _ _).trans_le (hM a))
  linarith

/-- **`log ∑ₐ exp (· + h)` is 1-Lipschitz** for the `ℓ¹` norm:
`|log ∑ₐ exp (uₐ + hₐ) - log ∑ₐ exp (vₐ + hₐ)| ≤ ∑ₐ |uₐ - vₐ|`. -/
theorem abs_log_sum_exp_sub_le (h u v : α → ℝ) :
    |Real.log (∑ a, Real.exp (u a + h a)) - Real.log (∑ a, Real.exp (v a + h a))| ≤
      ∑ a, |u a - v a| :=
  abs_log_sum_exp_sub_le_of_forall h u v fun a => Finset.single_le_sum
    (f := fun b => |u b - v b|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)

/-- The gradient of `w ↦ log ∑ₐ exp (wₐ + hₐ)` is the Gibbs weight vector. -/
theorem hasFDerivAt_log_sum_exp (h u : α → ℝ) :
    HasFDerivAt (fun w : α → ℝ => Real.log (∑ a, Real.exp (w a + h a)))
      (∑ b, (Real.exp (u b + h b) / ∑ a, Real.exp (u a + h a)) •
        (ContinuousLinearMap.proj b : (α → ℝ) →L[ℝ] ℝ)) u := by
  have hpos : 0 < ∑ a, Real.exp (u a + h a) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hs : HasFDerivAt (fun w : α → ℝ => ∑ a, Real.exp (w a + h a))
      (∑ b, Real.exp (u b + h b) • (ContinuousLinearMap.proj b : (α → ℝ) →L[ℝ] ℝ)) u :=
    HasFDerivAt.fun_sum fun b _ => ((hasFDerivAt_apply b u).add_const (h b)).exp
  convert hs.log hpos.ne' using 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul, div_eq_inv_mul]

end LogSumExp

section Path

variable {α : Type*} [Fintype α] [Nonempty α]

/-- Along the path `u_s = cos s u + sin s v + h`, the partition-function ratio
`exp (t (log Z(u_s) - log Z(v)))` has derivative `exp (…) · t ⟨u_s'⟩_s`, with `u_s' = -sin s u +
cos s v` and `⟨·⟩_s` the Gibbs average of `u_s`. -/
theorem hasDerivAt_exp_mul_log_sum_exp_trig (h u v : α → ℝ) (t s : ℝ) :
    HasDerivAt (fun s => Real.exp (t * (Real.log (∑ a, Real.exp (Real.cos s * u a +
        Real.sin s * v a + h a)) - Real.log (∑ a, Real.exp (v a + h a)))))
      (Real.exp (t * (Real.log (∑ a, Real.exp (Real.cos s * u a + Real.sin s * v a + h a)) -
          Real.log (∑ a, Real.exp (v a + h a)))) *
        (t * ∑ a, Real.exp (Real.cos s * u a + Real.sin s * v a + h a) /
          (∑ b, Real.exp (Real.cos s * u b + Real.sin s * v b + h b)) *
          (-Real.sin s * u a + Real.cos s * v a))) s := by
  let _ : MeasurableSpace α := ⊤
  have _ : MeasurableSingletonClass α := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have hf := hasDerivAt_log_sum_exp_path (f := fun s a => Real.cos s * u a + Real.sin s * v a + h a)
    (f' := fun a => -Real.sin s * u a + Real.cos s * v a) (t := s) fun a =>
    hasDerivAt_cos_mul_add_sin_mul (u a) (v a) (h a) s
  have := ((hf.sub_const (Real.log (∑ a, Real.exp (v a + h a)))).const_mul t).exp
  rwa [integral_count_tilted] at this

/-- The ratio `exp (t (log Z(u_s) - log Z(v)))` is at most `exp (2 |t| (‖u‖₁ + ‖v‖₁))`. -/
theorem exp_mul_log_sum_exp_trig_le (h u v : α → ℝ) (t s : ℝ) :
    Real.exp (t * (Real.log (∑ a, Real.exp (Real.cos s * u a + Real.sin s * v a + h a)) -
        Real.log (∑ a, Real.exp (v a + h a)))) ≤
      Real.exp (2 * |t| * (∑ a, |u a| + ∑ a, |v a|)) := by
  refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
  rw [abs_mul]
  have h1 := abs_log_sum_exp_sub_le h (fun a => Real.cos s * u a + Real.sin s * v a) v
  have h2 : ∑ a, |Real.cos s * u a + Real.sin s * v a - v a| ≤ 2 * (∑ a, |u a| + ∑ a, |v a|) := by
    calc _ ≤ ∑ a, (|u a| + 2 * |v a|) := Finset.sum_le_sum fun a _ => by
          calc |Real.cos s * u a + Real.sin s * v a - v a|
              ≤ |Real.cos s * u a| + |Real.sin s * v a| + |v a| := by
                refine (abs_sub _ _).trans ?_
                gcongr
                exact abs_add_le _ _
            _ ≤ |u a| + 2 * |v a| := by
                rw [abs_mul, abs_mul]
                nlinarith [Real.abs_cos_le_one s, Real.abs_sin_le_one s, abs_nonneg (u a),
                  abs_nonneg (v a)]
      _ ≤ 2 * (∑ a, |u a| + ∑ a, |v a|) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          nlinarith [Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) => abs_nonneg (u a)),
            Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) => abs_nonneg (v a))]
  calc |t| * |Real.log (∑ a, Real.exp (Real.cos s * u a + Real.sin s * v a + h a)) -
        Real.log (∑ a, Real.exp (v a + h a))| ≤ |t| * (2 * (∑ a, |u a| + ∑ a, |v a|)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (abs_nonneg t)
    _ = 2 * |t| * (∑ a, |u a| + ∑ a, |v a|) := by ring

/-- The derivative of `s ↦ exp (t (log Z(u_s) - log Z(v)))` is bounded by
`|t| exp ((2 |t| + 1) (‖u‖₁ + ‖v‖₁))`. -/
theorem abs_exp_mul_gibbs_average_le (h u v : α → ℝ) (t s : ℝ) :
    |Real.exp (t * (Real.log (∑ a, Real.exp (Real.cos s * u a + Real.sin s * v a + h a)) -
          Real.log (∑ a, Real.exp (v a + h a)))) *
        (t * ∑ a, Real.exp (Real.cos s * u a + Real.sin s * v a + h a) /
          (∑ b, Real.exp (Real.cos s * u b + Real.sin s * v b + h b)) *
          (-Real.sin s * u a + Real.cos s * v a))| ≤
      |t| * Real.exp ((2 * |t| + 1) * (∑ a, |u a| + ∑ a, |v a|)) := by
  set S : ℝ := ∑ a, |u a| + ∑ a, |v a| with hS
  have hS0 : 0 ≤ S := add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  set Z : ℝ := ∑ b, Real.exp (Real.cos s * u b + Real.sin s * v b + h b) with hZ
  have hZpos : 0 < Z := Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hw : |∑ a, Real.exp (Real.cos s * u a + Real.sin s * v a + h a) / Z *
      (-Real.sin s * u a + Real.cos s * v a)| ≤ S := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ a, |Real.exp (Real.cos s * u a + Real.sin s * v a + h a) / Z *
            (-Real.sin s * u a + Real.cos s * v a)|
        ≤ ∑ a, (|u a| + |v a|) := Finset.sum_le_sum fun a _ => by
          rw [abs_mul, abs_of_pos (div_pos (Real.exp_pos _) hZpos)]
          have h1 : Real.exp (Real.cos s * u a + Real.sin s * v a + h a) / Z ≤ 1 := by
            rw [div_le_one hZpos]
            exact Finset.single_le_sum (f := fun b => Real.exp (Real.cos s * u b +
              Real.sin s * v b + h b)) (fun _ _ => (Real.exp_pos _).le) (Finset.mem_univ a)
          have h2 := abs_neg_sin_mul_add_cos_mul_le (u a) (v a) s
          calc _ ≤ 1 * (|u a| + |v a|) :=
                mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
            _ = _ := one_mul _
      _ = S := by rw [Finset.sum_add_distrib]
  have hΦ := exp_mul_log_sum_exp_trig_le h u v t s
  have hΦ' : Real.exp (t * (Real.log Z - Real.log (∑ a, Real.exp (v a + h a)))) ≤
      Real.exp (2 * |t| * S) := hΦ
  clear_value S Z
  rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
  calc _ ≤ Real.exp (2 * |t| * S) * (|t| * S) := by
        refine mul_le_mul hΦ' (mul_le_mul_of_nonneg_left hw (abs_nonneg t)) (by positivity)
          (Real.exp_pos _).le
    _ ≤ Real.exp (2 * |t| * S) * (|t| * Real.exp S) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg t))
          (Real.exp_pos _).le
        linarith [Real.add_one_le_exp S]
    _ = |t| * Real.exp ((2 * |t| + 1) * S) := by
        rw [show (2 * |t| + 1) * S = 2 * |t| * S + S by ring, Real.exp_add]; ring

section Random

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {g₁ g₂ : α → Ω → ℝ}

/-- **Derivative of the exponential moment along the interpolation path.**  For a centered
Gaussian pair `(g₁, g₂)`, `φ(s) = 𝔼 exp (t (log Z(cos s g₁ + sin s g₂) - log Z(g₂)))` is
differentiable, with `φ'(s) = 𝔼 [exp (…) · t ⟨u_s'⟩_s]`, `u_s' = -sin s g₁ + cos s g₂`.  This is
`hasDerivAt_integral_comp_of_exp_growth` for the pointwise derivative
`hasDerivAt_exp_mul_log_sum_exp_trig`, whose exponential growth is
`abs_exp_mul_gibbs_average_le`. -/
theorem hasDerivAt_integral_exp_mul_log_sum_exp_trig
    (hg : HasGaussianLaw (fun ω s => Sum.elim g₁ g₂ s ω) P)
    (h₁ : ∀ a, ∫ ω, g₁ a ω ∂P = 0) (h₂ : ∀ a, ∫ ω, g₂ a ω ∂P = 0) (h : α → ℝ) (t s : ℝ) :
    HasDerivAt (fun s => ∫ ω, Real.exp (t * (Real.log (∑ a, Real.exp (Real.cos s * g₁ a ω +
        Real.sin s * g₂ a ω + h a)) - Real.log (∑ a, Real.exp (g₂ a ω + h a)))) ∂P)
      (∫ ω, Real.exp (t * (Real.log (∑ a, Real.exp (Real.cos s * g₁ a ω +
          Real.sin s * g₂ a ω + h a)) - Real.log (∑ a, Real.exp (g₂ a ω + h a)))) *
        (t * ∑ a, Real.exp (Real.cos s * g₁ a ω + Real.sin s * g₂ a ω + h a) /
          (∑ b, Real.exp (Real.cos s * g₁ b ω + Real.sin s * g₂ b ω + h b)) *
          (-Real.sin s * g₁ a ω + Real.cos s * g₂ a ω)) ∂P) s := by
  classical
  have hmean : ∀ k, ∫ ω, Sum.elim g₁ g₂ k ω ∂P = 0 := by
    rintro (a | a)
    exacts [h₁ a, h₂ a]
  have hsum : ∀ y : α ⊕ α → ℝ, ∑ l, |y l| = ∑ a, |y (Sum.inl a)| + ∑ a, |y (Sum.inr a)| :=
    fun y => Fintype.sum_sum_type _
  have := hasDerivAt_integral_comp_of_exp_growth (P := P) (X := Sum.elim g₁ g₂) hg hmean
    (G := fun s y => Real.exp (t * (Real.log (∑ a, Real.exp (Real.cos s * y (Sum.inl a) +
        Real.sin s * y (Sum.inr a) + h a)) - Real.log (∑ a, Real.exp (y (Sum.inr a) + h a)))))
    (G' := fun s y => Real.exp (t * (Real.log (∑ a, Real.exp (Real.cos s * y (Sum.inl a) +
          Real.sin s * y (Sum.inr a) + h a)) - Real.log (∑ a, Real.exp (y (Sum.inr a) + h a)))) *
        (t * ∑ a, Real.exp (Real.cos s * y (Sum.inl a) + Real.sin s * y (Sum.inr a) + h a) /
          (∑ b, Real.exp (Real.cos s * y (Sum.inl b) + Real.sin s * y (Sum.inr b) + h b)) *
          (-Real.sin s * y (Sum.inl a) + Real.cos s * y (Sum.inr a))))
    s (fun s => by fun_prop) (by fun_prop)
    (fun s y => hasDerivAt_exp_mul_log_sum_exp_trig h (fun a => y (Sum.inl a))
      (fun a => y (Sum.inr a)) t s) (C := |t|) (c := 2 * |t| + 1)
    (fun s y => by
      rw [hsum]
      exact abs_exp_mul_gibbs_average_le h (fun a => y (Sum.inl a)) (fun a => y (Sum.inr a)) t s)
    (C₀ := 1) (c₀ := 2 * |t|) (fun y => by
      rw [hsum, abs_of_pos (Real.exp_pos _), one_mul]
      exact exp_mul_log_sum_exp_trig_le h (fun a => y (Sum.inl a)) (fun a => y (Sum.inr a)) t s)
  simpa using this

end Random

end Path

section Exponent

variable {α : Type*} [Fintype α] [Nonempty α]

/-- **The Gibbs exponent.**  For `y = (u, v)` on `α ⊕ α`, the function
`A_σ(y) = t (log Z(u) - log Z(v)) + (u_σ + h_σ - log Z(u))` satisfies
`exp A_σ(y) = exp (t (log Z(u) - log Z(v))) · (Gibbs weight of σ under u)`: it is the integrand of
the Gaussian integration by parts, and is smooth with `‖∂ A_σ‖ ≤ |t| + 2`. -/
theorem hasFDerivAt_gibbs_exponent (h : α → ℝ) (t : ℝ) (σ : α) (y : α ⊕ α → ℝ) :
    HasFDerivAt (fun y : α ⊕ α → ℝ =>
      t * (Real.log (∑ a, Real.exp (y (Sum.inl a) + h a)) -
        Real.log (∑ a, Real.exp (y (Sum.inr a) + h a))) +
        (y (Sum.inl σ) + h σ - Real.log (∑ a, Real.exp (y (Sum.inl a) + h a))))
      (t • (((∑ b, (Real.exp (y (Sum.inl b) + h b) / ∑ a, Real.exp (y (Sum.inl a) + h a)) •
            (ContinuousLinearMap.proj b : (α → ℝ) →L[ℝ] ℝ)).comp
              (ContinuousLinearMap.pi fun a => ContinuousLinearMap.proj (Sum.inl a))) -
          ((∑ b, (Real.exp (y (Sum.inr b) + h b) / ∑ a, Real.exp (y (Sum.inr a) + h a)) •
            (ContinuousLinearMap.proj b : (α → ℝ) →L[ℝ] ℝ)).comp
              (ContinuousLinearMap.pi fun a => ContinuousLinearMap.proj (Sum.inr a)))) +
        ((ContinuousLinearMap.proj (Sum.inl σ) : (α ⊕ α → ℝ) →L[ℝ] ℝ) -
          ((∑ b, (Real.exp (y (Sum.inl b) + h b) / ∑ a, Real.exp (y (Sum.inl a) + h a)) •
            (ContinuousLinearMap.proj b : (α → ℝ) →L[ℝ] ℝ)).comp
              (ContinuousLinearMap.pi fun a => ContinuousLinearMap.proj (Sum.inl a))))) y := by
  have h1 := (hasFDerivAt_log_sum_exp h fun a => y (Sum.inl a)).comp y
    (ContinuousLinearMap.pi fun a => ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : α ⊕ α => ℝ) (Sum.inl a)).hasFDerivAt
  have h2 := (hasFDerivAt_log_sum_exp h fun a => y (Sum.inr a)).comp y
    (ContinuousLinearMap.pi fun a => ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : α ⊕ α => ℝ) (Sum.inr a)).hasFDerivAt
  have h3 : HasFDerivAt (fun y : α ⊕ α → ℝ => y (Sum.inl σ))
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : α ⊕ α => ℝ) (Sum.inl σ)) y :=
    hasFDerivAt_apply _ _
  exact ((h1.sub h2).const_mul t).add ((h3.add_const (h σ)).sub h1)

omit [Nonempty α] in
/-- `|log ∑ₐ exp (wₐ + hₐ)| ≤ |log ∑ₐ exp hₐ| + ∑ₐ |wₐ|`. -/
theorem abs_log_sum_exp_le [Nonempty α] (h w : α → ℝ) :
    |Real.log (∑ a, Real.exp (w a + h a))| ≤ |Real.log (∑ a, Real.exp (h a))| + ∑ a, |w a| := by
  have := abs_log_sum_exp_sub_le h w (fun _ => 0)
  simp only [zero_add, sub_zero] at this
  calc _ = |(Real.log (∑ a, Real.exp (w a + h a)) - Real.log (∑ a, Real.exp (h a))) +
        Real.log (∑ a, Real.exp (h a))| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by linarith)

/-- **A log-average is controlled by the log of the observable:** for a positive observable `F`,
`|log ⟨F⟩| ≤ ∑ₐ |log F(a)|`, where `⟨·⟩` is the Gibbs average for any energy `f`. -/
theorem abs_log_integral_count_tilted_le [MeasurableSpace α] [MeasurableSingletonClass α]
    (f F : α → ℝ) (hF : ∀ a, 0 < F a) :
    |Real.log (∫ a, F a ∂(Measure.count.tilted f))| ≤ ∑ a, |Real.log (F a)| := by
  have h := abs_log_sum_exp_sub_le f (fun a => Real.log (F a)) fun _ => 0
  have e : ∀ a, Real.exp (Real.log (F a) + f a) = Real.exp (f a) * F a := fun a => by
    rw [Real.exp_add, Real.exp_log (hF a), mul_comm]
  simp only [e, zero_add, sub_zero] at h
  rwa [log_integral_count_tilted f F hF]

variable {A : α → (α ⊕ α → ℝ) → ℝ} {h : α → ℝ} {t : ℝ}
  (hA : ∀ σ y, A σ y = t * (Real.log (∑ a, Real.exp (y (Sum.inl a) + h a)) -
        Real.log (∑ a, Real.exp (y (Sum.inr a) + h a))) +
        (y (Sum.inl σ) + h σ - Real.log (∑ a, Real.exp (y (Sum.inl a) + h a))))

include hA in
theorem differentiable_gibbs_exponent (σ : α) : Differentiable ℝ (A σ) := by
  have : A σ = _ := funext (hA σ)
  rw [this]
  exact fun y => (hasFDerivAt_gibbs_exponent h t σ y).differentiableAt

include hA in
theorem fderiv_gibbs_exponent_apply_single [DecidableEq α] (σ : α) (y : α ⊕ α → ℝ)
    (l : α ⊕ α) :
    fderiv ℝ (A σ) y (Pi.single l 1) =
      Sum.elim (fun b => (t - 1) * (Real.exp (y (Sum.inl b) + h b) /
          ∑ a, Real.exp (y (Sum.inl a) + h a)) + if b = σ then 1 else 0)
        (fun b => -(t * (Real.exp (y (Sum.inr b) + h b) /
          ∑ a, Real.exp (y (Sum.inr a) + h a)))) l := by
  have : A σ = _ := funext (hA σ)
  rw [this, (hasFDerivAt_gibbs_exponent h t σ y).fderiv]
  rcases l with b | b
  · simp [Pi.single_apply, eq_comm (a := σ)]
    ring
  · simp [Pi.single_apply]

include hA in
/-- Linear growth of the Gibbs exponent in `‖y‖₁`. -/
theorem abs_gibbs_exponent_le (σ : α) (y : α ⊕ α → ℝ) :
    |A σ y| ≤ ((2 * |t| + 1) * |Real.log (∑ a, Real.exp (h a))| + |h σ|) +
      (|t| + 2) * ∑ l, |y l| := by
  rw [hA, Fintype.sum_sum_type]
  have h1 := abs_log_sum_exp_le h fun a => y (Sum.inl a)
  have h2 := abs_log_sum_exp_le h fun a => y (Sum.inr a)
  have h3 : |y (Sum.inl σ)| ≤ ∑ a, |y (Sum.inl a)| :=
    Finset.single_le_sum (f := fun a => |y (Sum.inl a)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ σ)
  set K := |Real.log (∑ a, Real.exp (h a))|
  set Su := ∑ a, |y (Sum.inl a)|
  set Sv := ∑ a, |y (Sum.inr a)|
  set Lu := Real.log (∑ a, Real.exp (y (Sum.inl a) + h a))
  set Lv := Real.log (∑ a, Real.exp (y (Sum.inr a) + h a))
  have hK : 0 ≤ K := abs_nonneg _
  have hSu : 0 ≤ Su := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hSv : 0 ≤ Sv := Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc |t * (Lu - Lv) + (y (Sum.inl σ) + h σ - Lu)|
      ≤ |t| * (|Lu| + |Lv|) + (|y (Sum.inl σ)| + |h σ| + |Lu|) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg t)
        · exact (abs_sub _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ _ := by nlinarith [abs_nonneg t, abs_nonneg (h σ)]

include hA in
/-- The partial derivatives of the Gibbs exponent are bounded by `|t| + 2`. -/
theorem abs_fderiv_gibbs_exponent_le [DecidableEq α] (σ : α) (y : α ⊕ α → ℝ) (l : α ⊕ α) :
    |fderiv ℝ (A σ) y (Pi.single l 1)| ≤ |t| + 2 := by
  rw [fderiv_gibbs_exponent_apply_single hA]
  rcases l with b | b
  · simp only [Sum.elim_inl]
    obtain ⟨hp0, hp1⟩ := gibbsWeight_mem_Icc (fun a => y (Sum.inl a)) h b
    have hite : |(if b = σ then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
    calc _ ≤ |(t - 1) * (Real.exp (y (Sum.inl b) + h b) / ∑ a, Real.exp (y (Sum.inl a) + h a))| +
          |(if b = σ then (1 : ℝ) else 0)| := abs_add_le _ _
      _ ≤ (|t| + 1) * 1 + 1 := by
          refine add_le_add ?_ hite
          rw [abs_mul, abs_of_nonneg hp0]
          exact mul_le_mul ((abs_sub _ _).trans (by simp)) hp1 hp0 (by positivity)
      _ = |t| + 2 := by ring
  · simp only [Sum.elim_inr]
    obtain ⟨hp0, hp1⟩ := gibbsWeight_mem_Icc (fun a => y (Sum.inr a)) h b
    rw [abs_neg, abs_mul, abs_of_nonneg hp0]
    nlinarith [abs_nonneg t]

include hA in
/-- `exp A_σ(y)` is the partition-function ratio times the Gibbs weight of `σ`. -/
theorem exp_gibbs_exponent (σ : α) (y : α ⊕ α → ℝ) :
    Real.exp (A σ y) = Real.exp (t * (Real.log (∑ a, Real.exp (y (Sum.inl a) + h a)) -
      Real.log (∑ a, Real.exp (y (Sum.inr a) + h a)))) *
      (Real.exp (y (Sum.inl σ) + h σ) / ∑ a, Real.exp (y (Sum.inl a) + h a)) := by
  have hZ : 0 < ∑ a, Real.exp (y (Sum.inl a) + h a) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  rw [hA, Real.exp_add, Real.exp_sub, Real.exp_log hZ]

end Exponent

section IBP

variable {α : Type*} [Fintype α] [Nonempty α] {Ω : Type*}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {g₁ g₂ : α → Ω → ℝ}

/-- **Integration by parts for the interpolated Gibbs average** (the heart of the concentration
argument).  Let `(g₁, g₂)` be a centered jointly Gaussian pair with `𝔼 g₁ g₂ = 0` and the same
covariance `C = 𝔼 g₁ g₁ = 𝔼 g₂ g₂`.  With `u_s = cos s g₁ + sin s g₂ + h`, `u_s' = -sin s g₁ +
cos s g₂`, `p` the Gibbs weights, and `Φ = exp (t (log Z(u_s) - log Z(g₂ + h)))`,
`𝔼 [Φ t ⟨u_s'⟩_s] = -t² cos s 𝔼 [Φ ∑ₐ ∑_b p_a(u_s) p_b(g₂) C(a, b)]`.
Indeed `u_s'` is uncorrelated with `u_s` and has covariance `cos s · C` with `g₂`; the Gaussian
integration by parts (`integral_mul_exp_comp_eq_sum_integral_mul_of_sum`) applied to
`exp A_σ = Φ p_σ` only sees the dependence of `Φ p_σ` on `g₂`, `∂_{g₂(b)} A_σ = -t p_b(g₂)`. -/
theorem integral_exp_mul_gibbs_average_trig
    (hg : HasGaussianLaw (fun ω s => Sum.elim g₁ g₂ s ω) P)
    (hm₁ : ∀ a, Measurable (g₁ a)) (hm₂ : ∀ a, Measurable (g₂ a))
    (h₁ : ∀ a, ∫ ω, g₁ a ω ∂P = 0) (h₂ : ∀ a, ∫ ω, g₂ a ω ∂P = 0)
    (h12 : ∀ a b, ∫ ω, g₁ a ω * g₂ b ω ∂P = 0) {C : α → α → ℝ}
    (hC₁ : ∀ a b, ∫ ω, g₁ a ω * g₁ b ω ∂P = C a b)
    (hC₂ : ∀ a b, ∫ ω, g₂ a ω * g₂ b ω ∂P = C a b) (h : α → ℝ) (t s : ℝ) :
    ∫ ω, Real.exp (t * (Real.log (∑ a, Real.exp (Real.cos s * g₁ a ω +
          Real.sin s * g₂ a ω + h a)) - Real.log (∑ a, Real.exp (g₂ a ω + h a)))) *
        (t * ∑ a, Real.exp (Real.cos s * g₁ a ω + Real.sin s * g₂ a ω + h a) /
          (∑ b, Real.exp (Real.cos s * g₁ b ω + Real.sin s * g₂ b ω + h b)) *
          (-Real.sin s * g₁ a ω + Real.cos s * g₂ a ω)) ∂P =
      -(t ^ 2 * Real.cos s) * ∫ ω, Real.exp (t * (Real.log (∑ a, Real.exp (Real.cos s * g₁ a ω +
          Real.sin s * g₂ a ω + h a)) - Real.log (∑ a, Real.exp (g₂ a ω + h a)))) *
        ∑ a, ∑ b, Real.exp (Real.cos s * g₁ a ω + Real.sin s * g₂ a ω + h a) /
          (∑ c, Real.exp (Real.cos s * g₁ c ω + Real.sin s * g₂ c ω + h c)) *
          (Real.exp (g₂ b ω + h b) / ∑ c, Real.exp (g₂ c ω + h c)) * C a b ∂P := by
  have hP := hg.isProbabilityMeasure
  obtain ⟨A, hA⟩ : ∃ A : α → (α ⊕ α → ℝ) → ℝ, ∀ σ y, A σ y = t *
      (Real.log (∑ a, Real.exp (y (Sum.inl a) + h a)) -
        Real.log (∑ a, Real.exp (y (Sum.inr a) + h a))) +
      (y (Sum.inl σ) + h σ - Real.log (∑ a, Real.exp (y (Sum.inl a) + h a))) :=
    ⟨fun σ y => _, fun _ _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : α → Ω → ℝ, ∀ σ ω, W σ ω = -Real.sin s * g₁ σ ω + Real.cos s * g₂ σ ω :=
    ⟨fun σ ω => _, fun _ _ => rfl⟩
  obtain ⟨X, hXl, hXr⟩ : ∃ X : α ⊕ α → Ω → ℝ,
      (∀ a ω, X (Sum.inl a) ω = Real.cos s * g₁ a ω + Real.sin s * g₂ a ω) ∧
      ∀ a ω, X (Sum.inr a) ω = g₂ a ω :=
    ⟨Sum.elim (fun a ω => Real.cos s * g₁ a ω + Real.sin s * g₂ a ω) g₂, fun _ _ => rfl,
      fun _ _ => rfl⟩
  have hWX : HasGaussianLaw (fun ω k => Sum.elim W X k ω) P := by
    let L : (α ⊕ α → ℝ) →L[ℝ] (α ⊕ (α ⊕ α) → ℝ) := ContinuousLinearMap.pi
      (Sum.elim (fun σ => (-Real.sin s) • ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : α ⊕ α => ℝ) (Sum.inl σ) + Real.cos s • ContinuousLinearMap.proj
          (Sum.inr σ))
        (Sum.elim (fun a => Real.cos s • ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : α ⊕ α => ℝ) (Sum.inl a) + Real.sin s • ContinuousLinearMap.proj
          (Sum.inr a)) (fun a => ContinuousLinearMap.proj (Sum.inr a))))
    convert hg.map_fun L using 1
    ext ω (σ | a | a)
    · simp [L, hW]
    · simp [L, hXl]
    · simp [L, hXr]
  classical
  have hint1 : ∀ a, Integrable (g₁ a) P := fun a => (hg.eval (Sum.inl a)).integrable
  have hint2 : ∀ a, Integrable (g₂ a) P := fun a => (hg.eval (Sum.inr a)).integrable
  have hW0 : ∀ σ, ∫ ω, W σ ω ∂P = 0 := fun σ => by
    simp only [hW]
    exact integral_lincomb_eq_zero h₁ h₂ hint1 hint2 (-Real.sin s) (Real.cos s) σ
  have hX0 : ∀ l, ∫ ω, X l ω ∂P = 0 := by
    rintro (a | a)
    · simp only [hXl]
      exact integral_lincomb_eq_zero h₁ h₂ hint1 hint2 (Real.cos s) (Real.sin s) a
    · simp only [hXr]
      exact h₂ a
  have hcov_l : ∀ σ b, ∫ ω, W σ ω * X (Sum.inl b) ω ∂P = 0 := fun σ b => by
    simp only [hW, hXl]
    rw [integral_lincomb_mul_lincomb hg h12 (-Real.sin s) (Real.cos s) (Real.cos s) (Real.sin s)
      σ b, hC₁, hC₂]
    ring
  have hcov_r : ∀ σ b, ∫ ω, W σ ω * X (Sum.inr b) ω ∂P = Real.cos s * C σ b := fun σ b => by
    simp only [hW, hXr]
    have := integral_lincomb_mul_lincomb hg h12 (-Real.sin s) (Real.cos s) 0 1 σ b
    simp only [zero_mul, zero_add, one_mul] at this
    rw [this, hC₂]
    ring
  have hibp : ∀ σ, ∫ ω, W σ ω * Real.exp (A σ fun l => X l ω) ∂P =
      -(t * Real.cos s) * ∑ b, C σ b * ∫ ω, Real.exp (A σ fun l => X l ω) *
        (Real.exp (g₂ b ω + h b) / ∑ c, Real.exp (g₂ c ω + h c)) ∂P := by
    intro σ
    rw [integral_mul_exp_comp_eq_sum_integral_mul_of_sum hWX hW0 hX0 σ
      (differentiable_gibbs_exponent hA σ) (fun y => abs_gibbs_exponent_le hA σ y)
      (fun l y => abs_fderiv_gibbs_exponent_le hA σ y l), Fintype.sum_sum_type]
    simp only [hcov_l, zero_mul, Finset.sum_const_zero, zero_add, hcov_r]
    simp only [fderiv_gibbs_exponent_apply_single hA, Sum.elim_inr, hXr]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e : ∀ ω, Real.exp (A σ fun l => X l ω) * -(t * (Real.exp (g₂ b ω + h b) /
        ∑ c, Real.exp (g₂ c ω + h c))) = -t * (Real.exp (A σ fun l => X l ω) *
        (Real.exp (g₂ b ω + h b) / ∑ c, Real.exp (g₂ c ω + h c))) := fun ω => by ring
    simp_rw [e]
    rw [integral_const_mul]
    ring
  have hXm : ∀ l, Measurable (X l) := by
    rintro (a | a)
    · have : X (Sum.inl a) = fun ω => Real.cos s * g₁ a ω + Real.sin s * g₂ a ω :=
        funext (hXl a)
      rw [this]
      exact ((hm₁ a).const_mul _).add ((hm₂ a).const_mul _)
    · have : X (Sum.inr a) = g₂ a := funext (hXr a)
      rw [this]
      exact hm₂ a
  have hXv : Measurable fun ω l => X l ω := Measurable.of_eval hXm
  have hAm : ∀ σ, Measurable (A σ) := fun σ =>
    (differentiable_gibbs_exponent hA σ).continuous.measurable
  have hint_e : ∀ σ, Integrable (fun ω => W σ ω * Real.exp (A σ fun l => X l ω)) P := fun σ =>
    integrable_mul_exp_comp_of_sum hWX hW0 hX0 σ (hAm σ) (fun y => abs_gibbs_exponent_le hA σ y)
  have hint_x : ∀ σ, Integrable (fun ω => Real.exp (A σ fun l => X l ω)) P := fun σ =>
    integrable_exp_comp_of_sum hWX hW0 hX0 (hAm σ) (fun y => abs_gibbs_exponent_le hA σ y)
  have hint_xp : ∀ σ b, Integrable (fun ω => Real.exp (A σ fun l => X l ω) *
      (Real.exp (g₂ b ω + h b) / ∑ c, Real.exp (g₂ c ω + h c))) P := fun σ b => by
    refine Integrable.mono' (hint_x σ) ?_ (Eventually.of_forall fun ω => ?_)
    · exact ((Real.measurable_exp.comp ((hAm σ).comp hXv)).mul (by fun_prop)).aestronglyMeasurable
    · obtain ⟨hp0, hp1⟩ := gibbsWeight_mem_Icc (fun c => g₂ c ω) h b
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hp0]
      exact mul_le_of_le_one_right (Real.exp_pos _).le hp1
  have hE : ∀ σ ω, Real.exp (A σ fun l => X l ω) =
      Real.exp (t * (Real.log (∑ a, Real.exp (Real.cos s * g₁ a ω + Real.sin s * g₂ a ω + h a)) -
        Real.log (∑ a, Real.exp (g₂ a ω + h a)))) *
      (Real.exp (Real.cos s * g₁ σ ω + Real.sin s * g₂ σ ω + h σ) /
        ∑ a, Real.exp (Real.cos s * g₁ a ω + Real.sin s * g₂ a ω + h a)) := fun σ ω => by
    rw [exp_gibbs_exponent hA]
    simp only [hXl, hXr]
  have hL : ∀ ω, Real.exp (t * (Real.log (∑ a, Real.exp (Real.cos s * g₁ a ω +
          Real.sin s * g₂ a ω + h a)) - Real.log (∑ a, Real.exp (g₂ a ω + h a)))) *
        (t * ∑ a, Real.exp (Real.cos s * g₁ a ω + Real.sin s * g₂ a ω + h a) /
          (∑ b, Real.exp (Real.cos s * g₁ b ω + Real.sin s * g₂ b ω + h b)) *
          (-Real.sin s * g₁ a ω + Real.cos s * g₂ a ω)) =
      t * ∑ σ, W σ ω * Real.exp (A σ fun l => X l ω) := fun ω => by
    simp only [hE, hW]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    ring
  have hR : ∀ ω, Real.exp (t * (Real.log (∑ a, Real.exp (Real.cos s * g₁ a ω +
          Real.sin s * g₂ a ω + h a)) - Real.log (∑ a, Real.exp (g₂ a ω + h a)))) *
        ∑ a, ∑ b, Real.exp (Real.cos s * g₁ a ω + Real.sin s * g₂ a ω + h a) /
          (∑ c, Real.exp (Real.cos s * g₁ c ω + Real.sin s * g₂ c ω + h c)) *
          (Real.exp (g₂ b ω + h b) / ∑ c, Real.exp (g₂ c ω + h c)) * C a b =
      ∑ σ, ∑ b, C σ b * (Real.exp (A σ fun l => X l ω) *
        (Real.exp (g₂ b ω + h b) / ∑ c, Real.exp (g₂ c ω + h c))) := fun ω => by
    simp only [hE]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  simp_rw [hL, hR]
  rw [integral_const_mul, integral_finsetSum _ fun σ _ => hint_e σ,
    integral_finsetSum _ fun σ _ => integrable_finsetSum _ fun b _ =>
      (hint_xp σ b).const_mul _, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hibp σ, integral_finsetSum _ fun b _ => (hint_xp σ b).const_mul _]
  simp only [integral_const_mul]
  ring

end IBP

section Gronwall

variable {α : Type*} [Fintype α] [Nonempty α] {Ω : Type*}
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {g₁ g₂ : α → Ω → ℝ}

/-- **Exponential moment of the free-energy difference of two independent copies.**
Let `(g₁, g₂)` be a centered jointly Gaussian pair of fields on a finite set with `𝔼 g₁ g₂ = 0` and
the same covariance `C ≤ a`.  Then for every bias `h` and every `t`,
`𝔼 exp (t (log Z(g₁) - log Z(g₂))) ≤ exp (a t²)`, with `Z(g) = ∑ₓ exp (g x + h x)`.
Along `x_s = cos s g₁ + sin s g₂`, the function `φ(s) = 𝔼 exp (t (log Z(x_s) - log Z(g₂)))`
has derivative `-t² cos s 𝔼[Φ_s ∑ₓ,ᵧ pₓ qᵧ C(x, y)] ≥ -a t² cos s φ(s)`
(`integral_exp_mul_gibbs_average_trig`), so `φ(s) exp (a t² sin s)` is non-decreasing on
`[0, π/2]`, where `φ(π/2) = 1`. -/
theorem integral_exp_mul_log_sum_exp_sub_le
    (hg : HasGaussianLaw (fun ω s => Sum.elim g₁ g₂ s ω) P)
    (hm₁ : ∀ a, Measurable (g₁ a)) (hm₂ : ∀ a, Measurable (g₂ a))
    (h₁ : ∀ a, ∫ ω, g₁ a ω ∂P = 0) (h₂ : ∀ a, ∫ ω, g₂ a ω ∂P = 0)
    (h12 : ∀ a b, ∫ ω, g₁ a ω * g₂ b ω ∂P = 0) {C : α → α → ℝ}
    (hC₁ : ∀ a b, ∫ ω, g₁ a ω * g₁ b ω ∂P = C a b)
    (hC₂ : ∀ a b, ∫ ω, g₂ a ω * g₂ b ω ∂P = C a b) {a : ℝ} (ha : ∀ x y, C x y ≤ a)
    (h : α → ℝ) (t : ℝ) :
    ∫ ω, Real.exp (t * (Real.log (∑ x, Real.exp (g₁ x ω + h x)) -
      Real.log (∑ x, Real.exp (g₂ x ω + h x)))) ∂P ≤ Real.exp (t ^ 2 * a) := by
  have hP := hg.isProbabilityMeasure
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℝ, ∀ s, φ s = ∫ ω, Real.exp (t * (Real.log (∑ x, Real.exp
      (Real.cos s * g₁ x ω + Real.sin s * g₂ x ω + h x)) -
        Real.log (∑ x, Real.exp (g₂ x ω + h x)))) ∂P := ⟨_, fun _ => rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ → ℝ, ∀ s, R s = ∫ ω, Real.exp (t * (Real.log (∑ x, Real.exp
      (Real.cos s * g₁ x ω + Real.sin s * g₂ x ω + h x)) -
        Real.log (∑ x, Real.exp (g₂ x ω + h x)))) *
      ∑ x, ∑ y, Real.exp (Real.cos s * g₁ x ω + Real.sin s * g₂ x ω + h x) /
        (∑ c, Real.exp (Real.cos s * g₁ c ω + Real.sin s * g₂ c ω + h c)) *
        (Real.exp (g₂ y ω + h y) / ∑ c, Real.exp (g₂ c ω + h c)) * C x y ∂P :=
    ⟨_, fun _ => rfl⟩
  have hmean : ∀ k, ∫ ω, Sum.elim g₁ g₂ k ω ∂P = 0 := by
    rintro (a | a)
    exacts [h₁ a, h₂ a]
  have hΦi : ∀ s, Integrable (fun ω => Real.exp (t * (Real.log (∑ x, Real.exp
      (Real.cos s * g₁ x ω + Real.sin s * g₂ x ω + h x)) -
        Real.log (∑ x, Real.exp (g₂ x ω + h x))))) P := fun s => by
    have := integrable_comp_of_exp_growth hg hmean
      (F := fun y : α ⊕ α → ℝ => Real.exp (t * (Real.log (∑ x, Real.exp
        (Real.cos s * y (Sum.inl x) + Real.sin s * y (Sum.inr x) + h x)) -
          Real.log (∑ x, Real.exp (y (Sum.inr x) + h x))))) (by fun_prop) (C := 1)
      (c := 2 * |t|) fun y => by
        rw [Fintype.sum_sum_type, abs_of_pos (Real.exp_pos _), one_mul]
        exact exp_mul_log_sum_exp_trig_le h _ _ t s
    simpa using this
  have hd : ∀ s, HasDerivAt φ (-(t ^ 2 * Real.cos s) * R s) s := fun s => by
    have h1 := hasDerivAt_integral_exp_mul_log_sum_exp_trig hg h₁ h₂ h t s
    rw [integral_exp_mul_gibbs_average_trig hg hm₁ hm₂ h₁ h₂ h12 hC₁ hC₂ h t s] at h1
    have e : φ = fun s => ∫ ω, Real.exp (t * (Real.log (∑ x, Real.exp
      (Real.cos s * g₁ x ω + Real.sin s * g₂ x ω + h x)) -
        Real.log (∑ x, Real.exp (g₂ x ω + h x)))) ∂P := funext hφ
    rw [e, hR]
    exact h1
  have hRle : ∀ s, R s ≤ a * φ s := fun s => by
    rw [hR, hφ, ← integral_const_mul]
    refine integral_mono ?_ ((hΦi s).const_mul a) fun ω => ?_
    · refine (hΦi s).mul_bdd (c := ∑ x, ∑ y, |C x y|) (by fun_prop)
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs]
      exact abs_sum_sum_gibbsWeight_mul_le (fun x => Real.cos s * g₁ x ω + Real.sin s * g₂ x ω)
        (fun x => g₂ x ω) h C
    · rw [mul_comm a]
      exact mul_le_mul_of_nonneg_left
        (sum_sum_gibbsWeight_mul_le (fun x => Real.cos s * g₁ x ω + Real.sin s * g₂ x ω)
          (fun x => g₂ x ω) h ha) (Real.exp_pos _).le
  have hψ : ∀ s, HasDerivAt (fun s => φ s * Real.exp (t ^ 2 * a * Real.sin s))
      ((-(t ^ 2 * Real.cos s) * R s) * Real.exp (t ^ 2 * a * Real.sin s) +
        φ s * (Real.exp (t ^ 2 * a * Real.sin s) * (t ^ 2 * a * Real.cos s))) s := fun s =>
    (hd s).mul (((Real.hasDerivAt_sin s).const_mul (t ^ 2 * a)).exp)
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc 0 (π / 2))
    (fun s _ => (hψ s).differentiableAt.continuousAt.continuousWithinAt)
    (fun s _ => (hψ s).differentiableAt.differentiableWithinAt) (fun s hs => by
      rw [interior_Icc] at hs
      rw [(hψ s).deriv]
      have hcos : 0 ≤ Real.cos s := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs.1, Real.pi_pos],
        hs.2.le⟩
      have := mul_nonneg (mul_nonneg (Real.exp_pos (t ^ 2 * a * Real.sin s)).le
        (mul_nonneg (sq_nonneg t) hcos)) (sub_nonneg.2 (hRle s))
      nlinarith [this])
  have h0 : φ 0 = ∫ ω, Real.exp (t * (Real.log (∑ x, Real.exp (g₁ x ω + h x)) -
      Real.log (∑ x, Real.exp (g₂ x ω + h x)))) ∂P := by
    rw [hφ]
    simp
  have hπ : φ (π / 2) = 1 := by
    rw [hφ]
    simp
  have := hmono ⟨le_rfl, by linarith [Real.pi_pos]⟩ ⟨by linarith [Real.pi_pos], le_rfl⟩
    (by linarith [Real.pi_pos])
  simp only [Real.sin_zero, mul_zero, Real.exp_zero, mul_one, Real.sin_pi_div_two, hπ,
    one_mul] at this
  rwa [h0] at this

end Gronwall

section Concentration

variable {α : Type*} [Fintype α] [Nonempty α] {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} {g : α → Ω → ℝ}

/-- **The free energy is sub-Gaussian** (Panchenko, Theorem 1.2, in the form of the moment
generating function).  Let `g` be a centered Gaussian field on a finite set with
`𝔼 g(a)² ≤ v`, and `h` a deterministic bias.  Then
`F = log ∑ₐ exp (g a + h a)` satisfies `𝔼 exp (t (F - 𝔼 F)) ≤ exp (v t²)`, i.e.
`F - 𝔼 F` is sub-Gaussian with parameter `2 v`.  By symmetrization this follows from
`integral_exp_mul_log_sum_exp_sub_le` for two independent copies of `g`. -/
theorem hasSubgaussianMGF_log_sum_exp (hg : HasGaussianLaw (fun ω a => g a ω) P)
    (hm : ∀ a, Measurable (g a)) (h0 : ∀ a, ∫ ω, g a ω ∂P = 0) {v : ℝ}
    (hv : ∀ a, ∫ ω, g a ω ^ 2 ∂P ≤ v) (h : α → ℝ) :
    HasSubgaussianMGF (fun ω => Real.log (∑ a, Real.exp (g a ω + h a)) -
      ∫ ω', Real.log (∑ a, Real.exp (g a ω' + h a)) ∂P) (2 * v.toNNReal) P := by
  have hP := hg.isProbabilityMeasure
  obtain ⟨a₀⟩ := ‹Nonempty α›
  have hv0 : 0 ≤ v := (integral_nonneg fun _ => sq_nonneg _).trans (hv a₀)
  have hgi : ∀ a, MemLp (g a) 2 P := fun a => (hg.eval a).memLp_two
  refine hasSubgaussianMGF_sub_integral_of_integral_exp_sub_le (by fun_prop) (fun t => ?_)
    fun t => ?_
  · have := integrable_comp_of_exp_growth hg h0
      (F := fun y : α → ℝ => Real.exp (t * Real.log (∑ a, Real.exp (y a + h a)))) (by fun_prop)
      (C := Real.exp (|t| * |Real.log (∑ a, Real.exp (h a))|)) (c := |t|) fun y => by
        rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add, ← mul_add]
        refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_log_sum_exp_le h y) (abs_nonneg t)
    simpa using this
  · have hcore := integral_exp_mul_log_sum_exp_sub_le (P := P.prod P)
      (g₁ := fun a z => g a z.1) (g₂ := fun a z => g a z.2)
      (HasGaussianLaw.sumElim_prod hg hm) (fun a => (hm a).comp measurable_fst)
      (fun a => (hm a).comp measurable_snd)
      (fun a => by rw [integral_fun_fst (fun ω => g a ω)]; simp [h0 a])
      (fun a => by rw [integral_fun_snd (fun ω => g a ω)]; simp [h0 a])
      (fun a b => by rw [integral_prod_mul (fun ω => g a ω) (fun ω => g b ω)]; simp [h0 a])
      (C := fun a b => ∫ ω, g a ω * g b ω ∂P)
      (fun a b => by rw [integral_fun_fst (fun ω => g a ω * g b ω)]; simp)
      (fun a b => by rw [integral_fun_snd (fun ω => g a ω * g b ω)]; simp) (a := v)
      (fun x y => by linarith [integral_mul_le_half_add (hgi x) (hgi y), hv x, hv y]) h t
    refine hcore.trans_eq ?_
    rw [show ((2 * v.toNNReal : ℝ≥0) : ℝ) * t ^ 2 / 2 = t ^ 2 * v by
      push_cast; rw [Real.coe_toNNReal _ hv0]; ring]

/-- **Gaussian concentration of the free energy** ([Panchenko, 2013, Theorem 1.2, Eq. (1.41)]):
for a centered Gaussian field `g` on a finite set with `𝔼 g(a)² ≤ v`,
`ℙ(|F - 𝔼 F| ≥ x) ≤ 2 exp (-x² / (4 v))` for `F = log ∑ₐ exp (g a + h a)`.  It is Chernoff's bound
for the sub-Gaussian variable `F - 𝔼 F` (`hasSubgaussianMGF_log_sum_exp`), on both tails. -/
theorem measureReal_abs_sub_integral_ge_le_of_log_sum_exp
    (hg : HasGaussianLaw (fun ω a => g a ω) P) (hm : ∀ a, Measurable (g a))
    (h0 : ∀ a, ∫ ω, g a ω ∂P = 0) {v : ℝ} (hv : ∀ a, ∫ ω, g a ω ^ 2 ∂P ≤ v) (h : α → ℝ)
    {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | x ≤ |Real.log (∑ a, Real.exp (g a ω + h a)) -
      ∫ ω', Real.log (∑ a, Real.exp (g a ω' + h a)) ∂P|} ≤ 2 * Real.exp (-x ^ 2 / (4 * v)) := by
  have hP := hg.isProbabilityMeasure
  obtain ⟨a₀⟩ := ‹Nonempty α›
  have hv0 : 0 ≤ v := (integral_nonneg fun _ => sq_nonneg _).trans (hv a₀)
  have hsub := hasSubgaussianMGF_log_sum_exp hg hm h0 hv h
  have hc : 2 * ((2 * v.toNNReal : ℝ≥0) : ℝ) = 4 * v := by
    push_cast
    rw [Real.coe_toNNReal _ hv0]
    ring
  simpa only [hc] using hsub.measureReal_abs_ge_le hx

/-- **Variance of the free energy** ([Panchenko, 2013, Theorem 1.2]): under the assumptions of
`hasSubgaussianMGF_log_sum_exp`, `𝔼 (F - 𝔼 F)² ≤ 2 v` (the book states `8 v`). -/
theorem integral_sq_sub_integral_le_of_log_sum_exp
    (hg : HasGaussianLaw (fun ω a => g a ω) P) (hm : ∀ a, Measurable (g a))
    (h0 : ∀ a, ∫ ω, g a ω ∂P = 0) {v : ℝ} (hv : ∀ a, ∫ ω, g a ω ^ 2 ∂P ≤ v) (h : α → ℝ) :
    ∫ ω, (Real.log (∑ a, Real.exp (g a ω + h a)) -
      ∫ ω', Real.log (∑ a, Real.exp (g a ω' + h a)) ∂P) ^ 2 ∂P ≤ 2 * v := by
  have hP := hg.isProbabilityMeasure
  obtain ⟨a₀⟩ := ‹Nonempty α›
  have hv0 : 0 ≤ v := (integral_nonneg fun _ => sq_nonneg _).trans (hv a₀)
  refine (hasSubgaussianMGF_log_sum_exp hg hm h0 hv h).integral_sq_le.trans_eq ?_
  push_cast
  rw [Real.coe_toNNReal _ hv0]

end Concentration

section MixedPSpin

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] {β : ℕ → ℝ}
  (H : (∀ p : ℕ, (Fin p → ι) → ℝ) → (ι → ℤˣ) → ℝ)
  (hH : ∀ g σ, H g σ = ∑' p, β p * ((Real.sqrt (Fintype.card ι))⁻¹ ^ (p - 1) *
    ∑ idx, g p idx * ∏ k, ((σ (idx k) : ℤ) : ℝ)))
  (hβ0 : β 0 = 0) (hβ : Summable fun p => |β p|)

include hH hβ0 hβ

omit [DecidableEq ι] in
/-- The variance of the mixed Hamiltonian at a hypercube point is `N ξ(1)`, `ξ(1) = ∑ₚ β_p²`: the
self-overlap is `1`. -/
theorem integral_mixedPSpin_sq (σ : ι → ℤˣ) :
    ∫ g, H g σ ^ 2 ∂(Measure.infinitePi fun p : ℕ => Measure.pi fun _ : Fin p → ι =>
      gaussianReal 0 1) = Fintype.card ι * ∑' p, β p ^ 2 := by
  have h := integral_mixedPSpin_hypercube_mul_mixedPSpin_hypercube H hH hβ0 hβ σ σ
  have hself := card_inv_mul_dotProduct_self_eq_one (fun i => ((σ i : ℤ) : ℝ))
    fun i => units_cast_sq (σ i)
  rw [show (fun g => H g σ ^ 2) = fun g => H g σ * H g σ from funext fun g => sq (H g σ), h,
    hself]
  simp

/-- **The free energy of the mixed `p`-spin model is sub-Gaussian**: `X_N - 𝔼 X_N` with
`X_N = N⁻¹ log Z_N`, `Z_N = ∑_σ exp (H_N(σ))`, is sub-Gaussian with parameter `2 ξ(1) / N`,
`ξ(1) = ∑ₚ β_p²`.  This is `hasSubgaussianMGF_log_sum_exp` rescaled by `N⁻¹`
(`HasSubgaussianMGF.const_mul`). -/
theorem mixedPSpin_free_energy_hasSubgaussianMGF :
    HasSubgaussianMGF
      (fun g => (Fintype.card ι : ℝ)⁻¹ * Real.log (∑ σ, Real.exp (H g σ)) -
        (Fintype.card ι : ℝ)⁻¹ * ∫ g', Real.log (∑ σ, Real.exp (H g' σ))
          ∂(Measure.infinitePi fun p : ℕ => Measure.pi fun _ : Fin p → ι => gaussianReal 0 1))
      (2 * (∑' p, β p ^ 2) / Fintype.card ι).toNNReal
      (Measure.infinitePi fun p : ℕ => Measure.pi fun _ : Fin p → ι => gaussianReal 0 1) := by
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hξ : 0 ≤ ∑' p, β p ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have hc : 0 ≤ 2 * (∑' p, β p ^ 2) / Fintype.card ι := by positivity
  have key := (hasSubgaussianMGF_log_sum_exp (mixedPSpin_hasGaussianLaw H hH hβ0 hβ)
    (fun σ => (mixedPSpin_hypercube_hyps H hH hβ0 hβ σ).1)
    (integral_mixedPSpin_eq_zero H hH hβ0 hβ) (v := Fintype.card ι * ∑' p, β p ^ 2)
    (fun σ => (integral_mixedPSpin_sq H hH hβ0 hβ σ).le) (fun _ => 0)).const_mul
    (Fintype.card ι : ℝ)⁻¹
  simp only [add_zero] at key
  convert key using 1
  · ext g
    ring
  · refine NNReal.eq ?_
    rw [Real.coe_toNNReal _ hc]
    change _ = ((Fintype.card ι : ℝ)⁻¹) ^ 2 *
      (2 * ((Fintype.card ι * ∑' p, β p ^ 2).toNNReal : ℝ))
    rw [Real.coe_toNNReal _ (mul_nonneg hN.le hξ)]
    field_simp

/-- **Concentration of the free energy of the mixed `p`-spin model**
([Panchenko, 2013, Eq. (1.42)]): for `X_N = N⁻¹ log Z_N`, `Z_N = ∑_σ exp (H_N(σ))`,
`ℙ(|X_N - 𝔼 X_N| ≥ x) ≤ 2 exp (-N x² / (4 ξ(1)))`, `ξ(1) = ∑ₚ β_p²`. -/
theorem mixedPSpin_free_energy_concentration {x : ℝ} (hx : 0 ≤ x) :
    (Measure.infinitePi fun p : ℕ => Measure.pi fun _ : Fin p → ι => gaussianReal 0 1).real
      {g | x ≤ |(Fintype.card ι : ℝ)⁻¹ * Real.log (∑ σ, Real.exp (H g σ)) -
        (Fintype.card ι : ℝ)⁻¹ * ∫ g', Real.log (∑ σ, Real.exp (H g' σ))
          ∂(Measure.infinitePi fun p : ℕ => Measure.pi fun _ : Fin p → ι => gaussianReal 0 1)|} ≤
      2 * Real.exp (-(Fintype.card ι : ℝ) * x ^ 2 / (4 * ∑' p, β p ^ 2)) := by
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hξ : 0 ≤ ∑' p, β p ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have hc : 0 ≤ 2 * (∑' p, β p ^ 2) / Fintype.card ι := by positivity
  refine ((mixedPSpin_free_energy_hasSubgaussianMGF H hH hβ0 hβ).measureReal_abs_ge_le
    hx).trans_eq ?_
  rw [Real.coe_toNNReal _ hc]
  rcases eq_or_ne (∑' p, β p ^ 2) 0 with h0 | h0
  · simp [h0]
  · congr 2
    field_simp
    ring

/-- **Variance of the free energy of the mixed `p`-spin model:** `Var(X_N) ≤ 2 ξ(1) / N`
(the book has the constant `8`). -/
theorem mixedPSpin_free_energy_variance_le :
    ∫ g, ((Fintype.card ι : ℝ)⁻¹ * Real.log (∑ σ, Real.exp (H g σ)) -
        (Fintype.card ι : ℝ)⁻¹ * ∫ g', Real.log (∑ σ, Real.exp (H g' σ))
          ∂(Measure.infinitePi fun p : ℕ => Measure.pi fun _ : Fin p → ι => gaussianReal 0 1)) ^ 2
      ∂(Measure.infinitePi fun p : ℕ => Measure.pi fun _ : Fin p → ι => gaussianReal 0 1) ≤
      2 * (∑' p, β p ^ 2) / Fintype.card ι := by
  have hN : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 Fintype.card_pos
  have hξ : 0 ≤ ∑' p, β p ^ 2 := tsum_nonneg fun _ => sq_nonneg _
  have hc : 0 ≤ 2 * (∑' p, β p ^ 2) / Fintype.card ι := by positivity
  refine (mixedPSpin_free_energy_hasSubgaussianMGF H hH hβ0 hβ).integral_sq_le.trans_eq ?_
  exact Real.coe_toNNReal _ hc

end MixedPSpin

end SpinGlasses
