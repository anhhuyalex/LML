/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GaussianIBP

/-!
# Gaussian interpolation for the free energy

Let `X` and `Y` be independent centered Gaussian fields on a finite set `α` (jointly Gaussian with
`𝔼 X(a) Y(b) = 0`).  Along the trigonometric path `u_s = cos s X + sin s Y + h` the expected free
energy `φ(s) = 𝔼 log ∑ₐ exp (u_s(a))` has an explicit derivative, given by Gaussian integration
by parts for the Gibbs measure (Lemma 1.1).  This file proves that derivative formula; the
comparison inequality `𝔼 log ∑ₐ exp (Y(a) + h(a)) ≤ 𝔼 log ∑ₐ exp (X(a) + h(a))`, the smooth form of
Slepian's inequality behind the Guerra–Toninelli superadditivity ([Panchenko, 2013, §1.3]), is
`SpinGlasses.integral_log_sum_exp_le_of_covariance_le` in
`SpinGlasses/GaussianCovarianceInterpolation.lean`, a special case of Slepian's lemma for a general
test function (`SpinGlasses.integral_comp_le_of_covariance_le`).  No definitions are introduced.

## Main declarations

* `SpinGlasses.hasDerivAt_integral_log_sum_exp_trig`: along the path
  `u_s = cos s X + sin s Y + h`, the derivative of `φ(s) = 𝔼 log ∑ₐ exp (u_s(a))` is, by
  Gaussian integration by parts for the Gibbs measure (Lemma 1.1), `sin s cos s` times the Gibbs
  average of `(B - A)(σ¹, σ¹) - (B - A)(σ¹, σ²)` with `A = Cov X`, `B = Cov Y`.
* `SpinGlasses.hasDerivAt_integral_log_integral_cosh_trig`: the corresponding derivative for
  the logarithm of a Gibbs average of `cosh`, obtained by adjoining one Ising sign.

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
theorem integral_lincomb_mul_lincomb
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
lemma integral_lincomb_eq_zero (hX : ∀ a, ∫ ω, X a ω ∂P = 0)
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
    (fun ω s _ a => hasDerivAt_cos_mul_add_sin_mul (X a ω) (Y a ω) (h a) s)
    (B := fun ω => ∑ a, (|X a ω| + |Y a ω|))
    (integrable_finsetSum _ fun a _ => (hXi a).abs.add (hYi a).abs)
    (fun ω s _ a => abs_neg_sin_mul_add_cos_mul_le_sum (fun b => X b ω) (fun b => Y b ω) s a)
  refine hpath.congr_deriv ?_
  rw [hmain]
  refine integral_congr_ae (ae_of_all _ fun ω => integral_congr_ae (ae_of_all _ fun p => ?_))
  simp only [hcov]
  ring

/-- **Gaussian derivative of a logarithmic `cosh` Gibbs average.**  An auxiliary Ising sign
rewrites `log ⟨cosh (Z + h)⟩` as a log partition function on `α × ℤˣ`, so the general Gaussian
log-partition derivative applies directly.  This is the model-independent `f = cosh`
specialization of Talagrand's Eq. (1.178); unlike a quotient differentiation proof, it needs no
new smooth-functional or integrability API. -/
theorem hasDerivAt_integral_log_integral_cosh_trig [Finite α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (hXm : ∀ a, Measurable (X a)) (hYm : ∀ a, Measurable (Y a))
    (hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P)
    (hX : ∀ a, ∫ ω, X a ω ∂P = 0) (hY : ∀ a, ∫ ω, Y a ω ∂P = 0)
    (h0 : ∀ a b, ∫ ω, X a ω * Y b ω ∂P = 0) (A h : α → ℝ) (t : ℝ) :
    HasDerivAt (fun s => ∫ ω,
      Real.log (∫ a, Real.cosh (Real.cos s * X a ω + Real.sin s * Y a ω + h a)
        ∂Measure.count.tilted A) ∂P)
      (∫ ω, ∫ p : (α × ℤˣ) × (α × ℤˣ), Real.sin t * Real.cos t *
        ((∫ ω', (p.1.2 : ℝ) * Y p.1.1 ω' * ((p.1.2 : ℝ) * Y p.1.1 ω') ∂P -
            ∫ ω', (p.1.2 : ℝ) * X p.1.1 ω' * ((p.1.2 : ℝ) * X p.1.1 ω') ∂P) -
          (∫ ω', (p.1.2 : ℝ) * Y p.1.1 ω' * ((p.2.2 : ℝ) * Y p.2.1 ω') ∂P -
            ∫ ω', (p.1.2 : ℝ) * X p.1.1 ω' * ((p.2.2 : ℝ) * X p.2.1 ω') ∂P))
        ∂((Measure.count.tilted fun x : α × ℤˣ =>
          Real.cos t * ((x.2 : ℝ) * X x.1 ω) +
          Real.sin t * ((x.2 : ℝ) * Y x.1 ω) + A x.1 + (x.2 : ℝ) * h x.1).prod
          (Measure.count.tilted fun x : α × ℤˣ =>
            Real.cos t * ((x.2 : ℝ) * X x.1 ω) +
            Real.sin t * ((x.2 : ℝ) * Y x.1 ω) + A x.1 + (x.2 : ℝ) * h x.1)) ∂P) t := by
  let _ := Fintype.ofFinite α
  let Xs : (α × ℤˣ) → Ω → ℝ := fun x ω => (x.2 : ℝ) * X x.1 ω
  let Ys : (α × ℤˣ) → Ω → ℝ := fun x ω => (x.2 : ℝ) * Y x.1 ω
  let B : (α × ℤˣ) → ℝ := fun x => A x.1 + (x.2 : ℝ) * h x.1
  have hXYs : HasGaussianLaw (fun ω s => Sum.elim Xs Ys s ω) P := by
    let e : ((α × ℤˣ) ⊕ (α × ℤˣ)) → (α ⊕ α) := fun s => match s with
      | Sum.inl x => Sum.inl x.1
      | Sum.inr x => Sum.inr x.1
    let c : ((α × ℤˣ) ⊕ (α × ℤˣ)) → ℝ := fun s => match s with
      | Sum.inl x => (x.2 : ℝ)
      | Sum.inr x => (x.2 : ℝ)
    have hsign := hXY.reindex_mul e c
    convert hsign using 1
    funext ω s
    rcases s with ⟨a, ε⟩ | ⟨a, ε⟩ <;> rfl
  have hXsm : ∀ x, Measurable (Xs x) := fun x => measurable_const.mul (hXm x.1)
  have hYsm : ∀ x, Measurable (Ys x) := fun x => measurable_const.mul (hYm x.1)
  have hXs : ∀ x, ∫ ω, Xs x ω ∂P = 0 := fun x => by
    simp only [Xs, integral_const_mul, hX, mul_zero]
  have hYs : ∀ x, ∫ ω, Ys x ω ∂P = 0 := fun x => by
    simp only [Ys, integral_const_mul, hY, mul_zero]
  have h0s : ∀ x y, ∫ ω, Xs x ω * Ys y ω ∂P = 0 := fun x y => by
    simp only [Xs, Ys]
    rw [show (fun ω => (x.2 : ℝ) * X x.1 ω * ((y.2 : ℝ) * Y y.1 ω)) =
      fun ω => ((x.2 : ℝ) * (y.2 : ℝ)) * (X x.1 ω * Y y.1 ω) by funext ω; ring,
      integral_const_mul, h0, mul_zero]
  have hd := hasDerivAt_integral_log_sum_exp_trig hXsm hYsm hXYs hXs hYs h0s B t
  let C : ℝ := Real.log 2 + Real.log (∑ a, Real.exp (A a))
  let Φ : ℝ → ℝ := fun s => ∫ ω,
    Real.log (∫ a, Real.cosh (Real.cos s * X a ω + Real.sin s * Y a ω + h a)
      ∂Measure.count.tilted A) ∂P
  have hP := hXY.isProbabilityMeasure
  have hsigned (s : ℝ) : (fun ω => Real.log (∑ x : α × ℤˣ,
      Real.exp (Real.cos s * Xs x ω + Real.sin s * Ys x ω + B x))) =
      fun ω => C + Real.log (∫ a,
        Real.cosh (Real.cos s * X a ω + Real.sin s * Y a ω + h a)
        ∂Measure.count.tilted A) := by
    funext ω
    rw [show (∑ x : α × ℤˣ,
        Real.exp (Real.cos s * Xs x ω + Real.sin s * Ys x ω + B x)) =
      ∑ x : α × ℤˣ, Real.exp (A x.1 + (x.2 : ℝ) *
        (Real.cos s * X x.1 ω + Real.sin s * Y x.1 ω + h x.1)) by
          apply Finset.sum_congr rfl
          intro x _
          congr 1
          simp only [Xs, Ys, B]
          ring]
    simpa only [C] using log_sum_exp_prod_units (α := α) A
      (fun a => Real.cos s * X a ω + Real.sin s * Y a ω + h a)
  have hXi : ∀ a, Integrable (X a) P := fun a => (hXY.eval (Sum.inl a)).integrable
  have hYi : ∀ a, Integrable (Y a) P := fun a => (hXY.eval (Sum.inr a)).integrable
  have hlog (s : ℝ) : Integrable (fun ω => Real.log (∑ x : α × ℤˣ,
      Real.exp (Real.cos s * Xs x ω + Real.sin s * Ys x ω + B x))) P := by
    simpa only [one_mul] using integrable_log_sum_exp (μ := P) (β := 1) one_pos
      (H := fun ω x => Real.cos s * Xs x ω + Real.sin s * Ys x ω + B x)
      (fun x => (((hXsm x).const_mul _).add ((hYsm x).const_mul _)).add_const _)
      (fun x => ((((hXi x.1).const_mul (x.2 : ℝ)).const_mul _).add
        (((hYi x.1).const_mul (x.2 : ℝ)).const_mul _)).add (integrable_const _))
  have hphi (s : ℝ) : Integrable (fun ω =>
      Real.log (∫ a, Real.cosh (Real.cos s * X a ω + Real.sin s * Y a ω + h a)
        ∂Measure.count.tilted A)) P := by
    have hc : Integrable (fun _ : Ω => C) P := integrable_const C
    have hi := (hlog s).sub hc
    refine hi.congr (ae_of_all _ fun ω => ?_)
    rw [hsigned s]
    simp
  have hfun (s : ℝ) : ∫ ω, Real.log (∑ x : α × ℤˣ,
      Real.exp (Real.cos s * Xs x ω + Real.sin s * Ys x ω + B x)) ∂P = C + Φ s := by
    rw [hsigned s, integral_add (integrable_const C) (hphi s), integral_const,
      probReal_univ, one_smul]
  have hout := hd.add_const (-C)
  change HasDerivAt (fun s => Φ s) _ t
  convert hout using 1
  · funext s
    rw [hfun]
    ring
  · simp only [Xs, Ys, B, add_assoc]

end Path

end SpinGlasses
