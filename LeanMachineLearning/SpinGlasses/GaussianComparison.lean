/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GaussianIBP

/-!
# Gaussian comparison for the free energy

Let `X` and `Y` be independent-of-each-other centered Gaussian fields on a finite set `α`
(jointly Gaussian with `𝔼 X(a) Y(b) = 0`) with the same variances,
`𝔼 X(a)² = 𝔼 Y(a)²`, and `𝔼 X(a) X(b) ≤ 𝔼 Y(a) Y(b)` for all `a, b`.  Then
`𝔼 log ∑ₐ exp (Y(a) + h(a)) ≤ 𝔼 log ∑ₐ exp (X(a) + h(a))`
for every deterministic bias `h`: less correlated fields have a larger free energy (the smooth
form of Slepian's inequality).  This is the Gaussian interpolation behind the Guerra–Toninelli
superadditivity ([Panchenko, 2013, §1.3]); `SpinGlasses/GuerraToninelli.lean` applies it with
`X` the Hamiltonian of size `N + M` and `Y` the sum of independent Hamiltonians of sizes `N`
and `M`.  No definitions are introduced.

## Main declarations

* `SpinGlasses.hasDerivAt_integral_log_sum_exp_trig`: along the path
  `u_s = cos s X + sin s Y + h`, the derivative of `φ(s) = 𝔼 log ∑ₐ exp (u_s(a))` is, by
  Gaussian integration by parts for the Gibbs measure (Lemma 1.1), `sin s cos s` times the Gibbs
  average of `(B - A)(σ¹, σ¹) - (B - A)(σ¹, σ²)` with `A = Cov X`, `B = Cov Y`.
* `SpinGlasses.integral_log_sum_exp_le_of_covariance_le`: the comparison inequality.

The trigonometric path `cos s X + sin s Y` (rather than `√t X + √(1 - t) Y`) is smooth on all of
`ℝ`, so no endpoint continuity or singular derivative has to be handled.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.2–1.3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology Real

namespace SpinGlasses

variable {α Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y : α → Ω → ℝ}

/-- Linear combinations of the coordinates of a jointly Gaussian pair `(X, Y)` are again jointly
Gaussian: `(p X + q Y, r X + s Y)` is a Gaussian field on `α ⊕ α`. -/
theorem hasGaussianLaw_sumElim_lincomb [Finite α]
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P) (p q r s : ℝ) :
    HasGaussianLaw (fun ω c => Sum.elim (fun a ω => p * X a ω + q * Y a ω)
      (fun a ω => r * X a ω + s * Y a ω) c ω) P := by
  have := Fintype.ofFinite α
  let L : (α ⊕ α → ℝ) →L[ℝ] (α ⊕ α → ℝ) := ContinuousLinearMap.pi
    (Sum.elim (fun a => p • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : α ⊕ α => ℝ)
        (Sum.inl a) + q • ContinuousLinearMap.proj (Sum.inr a))
      (fun a => r • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : α ⊕ α => ℝ) (Sum.inl a) +
        s • ContinuousLinearMap.proj (Sum.inr a)))
  convert hXY.map_fun L using 1
  ext ω (a | a) <;> simp [L]

/-- Covariance of two linear combinations of a Gaussian pair `(X, Y)` with `𝔼 X Y = 0`:
`𝔼 (p X(a) + q Y(a)) (r X(b) + s Y(b)) = p r 𝔼 X(a)X(b) + q s 𝔼 Y(a)Y(b)`. -/
theorem integral_lincomb_mul_lincomb [Finite α]
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (h0 : ∀ a b, ∫ ω, X a ω * Y b ω ∂P = 0) (p q r s : ℝ) (a b : α) :
    ∫ ω, (p * X a ω + q * Y a ω) * (r * X b ω + s * Y b ω) ∂P =
      p * r * ∫ ω, X a ω * X b ω ∂P + q * s * ∫ ω, Y a ω * Y b ω ∂P := by
  have hX : ∀ a, MemLp (X a) 2 P := fun a => (hXY.eval (Sum.inl a)).memLp_two
  have hY : ∀ a, MemLp (Y a) 2 P := fun a => (hXY.eval (Sum.inr a)).memLp_two
  have e : ∀ ω, (p * X a ω + q * Y a ω) * (r * X b ω + s * Y b ω) =
      p * r * (X a ω * X b ω) + (p * s * (X a ω * Y b ω) + (q * r * (Y a ω * X b ω) +
        q * s * (Y a ω * Y b ω))) := fun ω => by ring
  have hYX : ∫ ω, Y a ω * X b ω ∂P = 0 := by
    simp_rw [mul_comm (Y a _) (X b _)]
    exact h0 b a
  have hf1 : Integrable (fun ω => p * r * (X a ω * X b ω)) P :=
    ((hX a).integrable_mul (hX b)).const_mul _
  have hf2 : Integrable (fun ω => p * s * (X a ω * Y b ω)) P :=
    ((hX a).integrable_mul (hY b)).const_mul _
  have hf3 : Integrable (fun ω => q * r * (Y a ω * X b ω)) P :=
    ((hY a).integrable_mul (hX b)).const_mul _
  have hf4 : Integrable (fun ω => q * s * (Y a ω * Y b ω)) P :=
    ((hY a).integrable_mul (hY b)).const_mul _
  have hf34 : Integrable (fun ω => q * r * (Y a ω * X b ω) + q * s * (Y a ω * Y b ω)) P :=
    hf3.add hf4
  have hf234 : Integrable (fun ω => p * s * (X a ω * Y b ω) +
      (q * r * (Y a ω * X b ω) + q * s * (Y a ω * Y b ω))) P := hf2.add hf34
  simp_rw [e]
  rw [integral_add hf1 hf234, integral_add hf2 hf34, integral_add hf3 hf4]
  simp only [integral_const_mul, h0 a b, hYX]
  ring

section Path

/-- The centered combination `p X(a) + q Y(a)` has mean zero. -/
private lemma integral_lincomb_eq_zero (hX : ∀ a, ∫ ω, X a ω ∂P = 0)
    (hY : ∀ a, ∫ ω, Y a ω ∂P = 0) (hXi : ∀ a, Integrable (X a) P)
    (hYi : ∀ a, Integrable (Y a) P) (p q : ℝ) (a : α) :
    ∫ ω, (p * X a ω + q * Y a ω) ∂P = 0 := by
  rw [integral_add ((hXi a).const_mul p) ((hYi a).const_mul q), integral_const_mul,
    integral_const_mul, hX a, hY a]
  simp

/-- **Derivative of the interpolating free energy** along `u_s = cos s X + sin s Y + h`: for jointly
Gaussian centered `(X, Y)` with `𝔼 X Y = 0`, writing `A = 𝔼 X X`, `B = 𝔼 Y Y` and `⟨·⟩_s` for the
Gibbs average of `u_s`,
`φ'(s) = sin s cos s · 𝔼 ⟨(B - A)(σ¹, σ¹) - (B - A)(σ¹, σ²)⟩_s`
with `φ(s) = 𝔼 log ∑ₐ exp (u_s(a))`.  This is Lemma 1.1 applied to the field
`x_s = u_s' = -sin s X + cos s Y` against `u_s`, whose covariance `𝔼 x_s(a) u_s(b)` is
`sin s cos s (B - A)(a, b)`. -/
theorem hasDerivAt_integral_log_sum_exp_trig [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hXm : ∀ a, Measurable (X a)) (hYm : ∀ a, Measurable (Y a))
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (hX : ∀ a, ∫ ω, X a ω ∂P = 0) (hY : ∀ a, ∫ ω, Y a ω ∂P = 0)
    (h0 : ∀ a b, ∫ ω, X a ω * Y b ω ∂P = 0) (h : α → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ∫ ω, Real.log (∑ a, Real.exp (Real.cos s * X a ω +
        Real.sin s * Y a ω + h a)) ∂P)
      (∫ ω, ∫ p : α × α, Real.sin t * Real.cos t *
          ((∫ ω', Y p.1 ω' * Y p.1 ω' ∂P - ∫ ω', X p.1 ω' * X p.1 ω' ∂P) -
            (∫ ω', Y p.1 ω' * Y p.2 ω' ∂P - ∫ ω', X p.1 ω' * X p.2 ω' ∂P))
        ∂((Measure.count.tilted fun a => Real.cos t * X a ω + Real.sin t * Y a ω + h a).prod
          (Measure.count.tilted fun a => Real.cos t * X a ω + Real.sin t * Y a ω + h a)) ∂P) t := by
  have hP := hXY.isProbabilityMeasure
  have hXi : ∀ a, Integrable (X a) P := fun a => (hXY.eval (Sum.inl a)).integrable
  have hYi : ∀ a, Integrable (Y a) P := fun a => (hXY.eval (Sum.inr a)).integrable
  have hlin := hasGaussianLaw_sumElim_lincomb hXY (-Real.sin t) (Real.cos t) (Real.cos t)
    (Real.sin t)
  have hcov := fun a b => integral_lincomb_mul_lincomb hXY h0 (-Real.sin t) (Real.cos t)
    (Real.cos t) (Real.sin t) a b
  have hmain := integral_gibbs_average_gaussian (P := P)
    (fun a ω => -Real.sin t * X a ω + Real.cos t * Y a ω)
    (fun a ω => Real.cos t * X a ω + Real.sin t * Y a ω) hlin
    (integral_lincomb_eq_zero hX hY hXi hYi _ _) (integral_lincomb_eq_zero hX hY hXi hYi _ _)
    (fun a b => ∫ ω, (-Real.sin t * X a ω + Real.cos t * Y a ω) *
      (Real.cos t * X b ω + Real.sin t * Y b ω) ∂P) (fun a b => rfl) h
  have hpath := hasDerivAt_integral_log_sum_exp_path (μ := P) (t := t) (S := Set.univ)
    (f := fun s ω a => Real.cos s * X a ω + Real.sin s * Y a ω + h a)
    (f' := fun s ω a => -Real.sin s * X a ω + Real.cos s * Y a ω)
    Filter.univ_mem
    (fun s a => (((hXm a).const_mul _).add ((hYm a).const_mul _)).add_const _ |>.aemeasurable)
    (fun a => (((hXm a).const_mul _).add ((hYm a).const_mul _)).aemeasurable)
    (integrable_log_sum_exp (β := 1) one_pos
      (H := fun ω a => Real.cos t * X a ω + Real.sin t * Y a ω + h a)
      (fun a => (((hXm a).const_mul _).add ((hYm a).const_mul _)).add_const _)
      (fun a => (((hXi a).const_mul _).add ((hYi a).const_mul _)).add (integrable_const _))
      |>.congr (ae_of_all _ fun ω => by simp))
    (fun ω s _ a => by
      have h1 := (((Real.hasDerivAt_cos s).mul_const (X a ω)).add
        ((Real.hasDerivAt_sin s).mul_const (Y a ω))).add_const (h a)
      convert h1 using 1)
    (B := fun ω => ∑ a, (|X a ω| + |Y a ω|))
    (integrable_finsetSum _ fun a _ => (hXi a).abs.add (hYi a).abs)
    (fun ω s _ a => by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_neg]
      refine le_trans ?_ (Finset.single_le_sum (f := fun b => |X b ω| + |Y b ω|)
        (fun _ _ => by positivity) (mem_univ a))
      exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one s))
        (mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one s)))
  refine hpath.congr_deriv ?_
  rw [hmain]
  refine integral_congr_ae (ae_of_all _ fun ω => integral_congr_ae (ae_of_all _ fun p => ?_))
  simp only [hcov]
  ring

/-- **Gaussian comparison for the free energy** (the smooth form of Slepian's inequality).
Let `(X, Y)` be a centered jointly Gaussian pair of fields on a finite set with `𝔼 X(a) Y(b) = 0`,
equal variances `𝔼 X(a)² = 𝔼 Y(a)²` and `𝔼 X(a) X(b) ≤ 𝔼 Y(a) Y(b)`.  Then for every bias `h`,
`𝔼 log ∑ₐ exp (Y(a) + h(a)) ≤ 𝔼 log ∑ₐ exp (X(a) + h(a))`.
Indeed `φ(s) = 𝔼 log ∑ₐ exp (cos s X(a) + sin s Y(a) + h(a))` has derivative
`sin s cos s · 𝔼 ⟨(B - A)(σ¹, σ¹) - (B - A)(σ¹, σ²)⟩ = -sin s cos s · 𝔼 ⟨(B - A)(σ¹, σ²)⟩ ≤ 0`
on `[0, π/2]` (`hasDerivAt_integral_log_sum_exp_trig`), and `φ(0)`, `φ(π/2)` are the two sides. -/
theorem integral_log_sum_exp_le_of_covariance_le [Fintype α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (hXm : ∀ a, Measurable (X a)) (hYm : ∀ a, Measurable (Y a))
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (hX : ∀ a, ∫ ω, X a ω ∂P = 0) (hY : ∀ a, ∫ ω, Y a ω ∂P = 0)
    (h0 : ∀ a b, ∫ ω, X a ω * Y b ω ∂P = 0)
    (hdiag : ∀ a, ∫ ω, Y a ω * Y a ω ∂P = ∫ ω, X a ω * X a ω ∂P)
    (hle : ∀ a b, ∫ ω, X a ω * X b ω ∂P ≤ ∫ ω, Y a ω * Y b ω ∂P) (h : α → ℝ) :
    ∫ ω, Real.log (∑ a, Real.exp (Y a ω + h a)) ∂P ≤
      ∫ ω, Real.log (∑ a, Real.exp (X a ω + h a)) ∂P := by
  have hd := hasDerivAt_integral_log_sum_exp_trig hXm hYm hXY hX hY h0 h
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc 0 (π / 2))
    (fun s _ => (hd s).differentiableAt.continuousAt.continuousWithinAt)
    (fun s _ => (hd s).differentiableAt.differentiableWithinAt) (fun s hs => by
      rw [interior_Icc] at hs
      rw [(hd s).deriv]
      have hsin : 0 ≤ Real.sin s := Real.sin_nonneg_of_nonneg_of_le_pi hs.1.le
        (hs.2.le.trans (by linarith [Real.pi_pos]))
      have hcos : 0 ≤ Real.cos s := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs.1, Real.pi_pos],
        hs.2.le⟩
      refine integral_nonpos fun ω => integral_nonpos fun p => ?_
      simp only [hdiag, sub_self, Pi.zero_apply, zero_sub]
      exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hsin hcos) (by linarith [hle p.1 p.2]))
  have := hanti ⟨le_rfl, by linarith [Real.pi_pos]⟩ ⟨by linarith [Real.pi_pos], le_rfl⟩
    (by linarith [Real.pi_pos])
  simpa using this

end Path

end SpinGlasses
