/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GibbsGramMoments
public import LeanMachineLearning.SpinGlasses.SKSpinDecorrelation
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiExp
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.Hyperbolic

/-!
# The effect of a cavity field on a Gibbs average (model-independent part of Eq. (1.186))

Let `μ = count.tilted f` be a Gibbs measure on a finite set `α` carrying `±1` observables `ξ_i`
(`i < N`), and let `y` be a standard Gaussian vector.  Adding a last spin with field
`L_y(a) = c ∑ y_j ξ_j(a) + h` changes the Gibbs mean of `ξ_i` by
`⟨ξ̇_i cosh L_y⟩ / ⟨cosh L_y⟩`, where `ξ̇_i = ξ_i - ⟨ξ_i⟩` (see `SKOldSpinCavity.lean`).

This file bounds the numerator.  Taking first the Gaussian average of two replicas gives an
explicit kernel of the overlap (`integral_gibbs_cosh_sq`), which is Lipschitz.  Since the Gram
entry `T = N⁻¹ ∑ ξ̇_i ξ̇_i'` has Gibbs mean zero, the kernel may be centered at `q`, and the product
`|T| |R - q|` is bounded by the overlap moment through the Gram-moment bound
`integral_projGram_pow_le`.  The result (`sum_integral_gibbs_cosh_sq_le`) is

`∑_{i<N} 𝔼_y ⟨ξ̇_i cosh L_y⟩² ≤ N Λ (17/2) E⟨(R - q)²⟩`,  `Λ = B e^{2B} (cosh 2h + 1) / 2`,
`B = N c²`.

## Main declarations

* `SpinGlasses.abs_cavityKernel_sub_le`: Lipschitz bound for the two-replica Gaussian kernel.
* `SpinGlasses.integral_gibbs_cosh_sq`: `𝔼_y ⟨g cosh L_y⟩²` as a double Gibbs sum of an overlap
  kernel.
* `SpinGlasses.sum_integral_gibbs_cosh_sq_le`: the sum over the sites is bounded by the overlap
  moment.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace SpinGlasses

/-- **Lipschitz bound for the two-replica Gaussian kernel.**  For `B ≥ 0` and `|x|, |q| ≤ 1`
the function `x ↦ (cosh (2h) e^{B(1+x)} + e^{B(1-x)}) / 2` moves by at most
`B e^{2B} (cosh (2h) + 1) / 2 · |x - q|`. -/
theorem abs_cavityKernel_sub_le {B : ℝ} (hB : 0 ≤ B) (h : ℝ) {x q : ℝ} (hx : |x| ≤ 1)
    (hq : |q| ≤ 1) :
    |(Real.cosh (2 * h) * Real.exp (B * (1 + x)) + Real.exp (B * (1 - x))) / 2 -
        (Real.cosh (2 * h) * Real.exp (B * (1 + q)) + Real.exp (B * (1 - q))) / 2| ≤
      B * Real.exp (2 * B) * (Real.cosh (2 * h) + 1) / 2 * |x - q| := by
  have hc := Real.cosh_pos (2 * h)
  have hp : ∀ y : ℝ, |y| ≤ 1 → |B * (1 + y)| ≤ 2 * B := fun y hy => by
    obtain ⟨h1, h2⟩ := abs_le.1 hy
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have hm : ∀ y : ℝ, |y| ≤ 1 → |B * (1 - y)| ≤ 2 * B := fun y hy => by
    obtain ⟨h1, h2⟩ := abs_le.1 hy
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have e1 := Real.abs_exp_sub_exp_le_of_abs_le (hp x hx) (hp q hq)
  have e2 := Real.abs_exp_sub_exp_le_of_abs_le (hm x hx) (hm q hq)
  have d1 : |B * (1 + x) - B * (1 + q)| = B * |x - q| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hB]; congr 2; ring
  have d2 : |B * (1 - x) - B * (1 - q)| = B * |x - q| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hB, ← abs_neg (1 - x - (1 - q))]; congr 2; ring
  rw [d1] at e1
  rw [d2] at e2
  have hE : (Real.cosh (2 * h) * Real.exp (B * (1 + x)) + Real.exp (B * (1 - x))) / 2 -
        (Real.cosh (2 * h) * Real.exp (B * (1 + q)) + Real.exp (B * (1 - q))) / 2 =
      (Real.cosh (2 * h) * (Real.exp (B * (1 + x)) - Real.exp (B * (1 + q))) +
        (Real.exp (B * (1 - x)) - Real.exp (B * (1 - q)))) / 2 := by ring
  rw [hE, abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2), div_le_iff₀ two_pos]
  calc |Real.cosh (2 * h) * (Real.exp (B * (1 + x)) - Real.exp (B * (1 + q))) +
        (Real.exp (B * (1 - x)) - Real.exp (B * (1 - q)))|
      ≤ |Real.cosh (2 * h) * (Real.exp (B * (1 + x)) - Real.exp (B * (1 + q)))| +
        |Real.exp (B * (1 - x)) - Real.exp (B * (1 - q))| := abs_add_le _ _
    _ = Real.cosh (2 * h) * |Real.exp (B * (1 + x)) - Real.exp (B * (1 + q))| +
        |Real.exp (B * (1 - x)) - Real.exp (B * (1 - q))| := by
        rw [abs_mul, abs_of_pos hc]
    _ ≤ Real.cosh (2 * h) * (Real.exp (2 * B) * (B * |x - q|)) +
        Real.exp (2 * B) * (B * |x - q|) := by gcongr
    _ = B * Real.exp (2 * B) * (Real.cosh (2 * h) + 1) / 2 * |x - q| * 2 := by ring

section Gibbs

variable {α : Type*} [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {N : ℕ} (ξ : Fin N → α → ℝ)

omit [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- For `±1` observables, `∑ (c (ξ(a) ± ξ(b)))² / 2 = c² (N ± ∑ ξ(a) ξ(b))`. -/
theorem sum_sq_cavity_add (hξ2 : ∀ i a, ξ i a ^ 2 = 1) (c : ℝ) (a b : α) (s : ℝ)
    (hs : s = 1 ∨ s = -1) :
    ∑ i, (c * (ξ i a + s * ξ i b)) ^ 2 / 2 = c ^ 2 * (N + s * ∑ i, ξ i a * ξ i b) := by
  have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
  have : ∀ i, (c * (ξ i a + s * ξ i b)) ^ 2 / 2 = c ^ 2 + c ^ 2 * s * (ξ i a * ξ i b) := by
    intro i
    have h1 := hξ2 i a
    have h2 := hξ2 i b
    have : (c * (ξ i a + s * ξ i b)) ^ 2 / 2 =
        c ^ 2 * (ξ i a ^ 2 + s ^ 2 * ξ i b ^ 2) / 2 + c ^ 2 * s * (ξ i a * ξ i b) := by ring
    rw [this, h1, h2, hs2]; ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

omit [Nonempty α] in
/-- The square of a Gibbs average of `g cosh L_y` is a double Gibbs sum over two replicas. -/
theorem sq_integral_gibbs_cosh (f : α → ℝ) (c h : ℝ) (g : α → ℝ) (y : Fin N → ℝ) :
    (∫ a, g a * Real.cosh (c * ∑ j, y j * ξ j a + h) ∂(Measure.count.tilted f)) ^ 2 =
      ∑ a, ∑ b, (Real.exp (f a) / ∑ x, Real.exp (f x)) * (Real.exp (f b) / ∑ x, Real.exp (f x)) *
        (g a * g b) *
        (Real.cosh (c * ∑ j, y j * ξ j a + h) * Real.cosh (c * ∑ j, y j * ξ j b + h)) := by
  rw [integral_count_tilted, sq, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

omit [Nonempty α] in
set_option linter.unusedFintypeInType false in
/-- The Gaussian second moment of a Gibbs average of `g cosh L_y` is integrable. -/
theorem integrable_sq_integral_gibbs_cosh (f : α → ℝ) (c h : ℝ) (g : α → ℝ) :
    Integrable (fun y : Fin N → ℝ => (∫ a, g a * Real.cosh (c * ∑ j, y j * ξ j a + h)
      ∂(Measure.count.tilted f)) ^ 2) (Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  simp_rw [sq_integral_gibbs_cosh ξ f c h g]
  exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    (integrable_cosh_mul_cosh_sum_mul_gaussianReal c h (fun j => ξ j a)
      (fun j => ξ j b)).const_mul _

omit [Nonempty α] in
/-- **Gaussian average of two replicas of a cavity field.**  For `±1` observables and a
cavity field `L_y(a) = c ∑ y_j ξ_j(a) + h`, with `y` standard Gaussian, the Gaussian second moment
of the Gibbs average `⟨g cosh L_y⟩` is the double Gibbs sum of
`g(a) g(b) (cosh (2h) e^{c²(N + S)} + e^{c²(N - S)}) / 2`, `S = ∑ ξ_i(a) ξ_i(b)`. -/
theorem integral_gibbs_cosh_sq (hξ2 : ∀ i a, ξ i a ^ 2 = 1) (f : α → ℝ) (c h : ℝ) (g : α → ℝ) :
    ∫ y : Fin N → ℝ, (∫ a, g a * Real.cosh (c * ∑ j, y j * ξ j a + h)
        ∂(Measure.count.tilted f)) ^ 2 ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      ∑ a, ∑ b, (Real.exp (f a) / ∑ x, Real.exp (f x)) * (Real.exp (f b) / ∑ x, Real.exp (f x)) *
        (g a * g b) *
        ((Real.cosh (2 * h) * Real.exp (c ^ 2 * (N + ∑ i, ξ i a * ξ i b)) +
          Real.exp (c ^ 2 * (N - ∑ i, ξ i a * ξ i b))) / 2) := by
  have hint : ∀ a b, Integrable (fun y : Fin N → ℝ =>
      (Real.exp (f a) / ∑ x, Real.exp (f x)) * (Real.exp (f b) / ∑ x, Real.exp (f x)) *
        (g a * g b) * (Real.cosh (c * ∑ j, y j * ξ j a + h) *
          Real.cosh (c * ∑ j, y j * ξ j b + h))) (Measure.pi fun _ : Fin N => gaussianReal 0 1) :=
    fun a b => (integrable_cosh_mul_cosh_sum_mul_gaussianReal c h (fun j => ξ j a)
      (fun j => ξ j b)).const_mul _
  simp_rw [sq_integral_gibbs_cosh ξ f c h g]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hint a b]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => hint a b]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, integral_cosh_mul_cosh_sum_mul_gaussianReal c h (fun j => ξ j a)
    (fun j => ξ j b)]
  have e1 : ∑ j, (c * (ξ j a + ξ j b)) ^ 2 / 2 = c ^ 2 * (N + ∑ i, ξ i a * ξ i b) := by
    simpa using sum_sq_cavity_add ξ hξ2 c a b 1 (Or.inl rfl)
  have e2 : ∑ j, (c * (ξ j a - ξ j b)) ^ 2 / 2 = c ^ 2 * (N - ∑ i, ξ i a * ξ i b) := by
    simpa [sub_eq_add_neg] using sum_sq_cavity_add ξ hξ2 c a b (-1) (Or.inr rfl)
  rw [e1, e2]

omit [Nonempty α] in
/-- **The centered cavity deviation, averaged over the field.**  The same double Gibbs sum with
the centered observable `ξ̇_i = ξ_i - ⟨ξ_i⟩`, the mean being written as a weighted sum. -/
theorem integral_gibbs_cosh_sq_centered (hξ2 : ∀ i a, ξ i a ^ 2 = 1) (f : α → ℝ) (c h : ℝ)
    (i : Fin N) :
    ∫ y : Fin N → ℝ, (∫ a, (ξ i a - ∫ b, ξ i b ∂(Measure.count.tilted f)) *
        Real.cosh (c * ∑ j, y j * ξ j a + h) ∂(Measure.count.tilted f)) ^ 2
      ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      ∑ a, ∑ b, (Real.exp (f a) / ∑ x, Real.exp (f x)) * (Real.exp (f b) / ∑ x, Real.exp (f x)) *
        ((ξ i a - ∑ x, (Real.exp (f x) / ∑ z, Real.exp (f z)) * ξ i x) *
          (ξ i b - ∑ x, (Real.exp (f x) / ∑ z, Real.exp (f z)) * ξ i x)) *
        ((Real.cosh (2 * h) * Real.exp (c ^ 2 * (N + ∑ i, ξ i a * ξ i b)) +
          Real.exp (c ^ 2 * (N - ∑ i, ξ i a * ξ i b))) / 2) := by
  rw [integral_gibbs_cosh_sq ξ hξ2 f c h (fun a => ξ i a - ∫ b, ξ i b ∂(Measure.count.tilted f)),
    integral_count_tilted f (ξ i)]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- Gibbs weights sum to one. -/
theorem sum_exp_div_sum_exp (f : α → ℝ) : ∑ a, Real.exp (f a) / ∑ b, Real.exp (f b) = 1 := by
  rw [← Finset.sum_div]
  exact div_self (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne'

/-- The Gibbs average of the centered observable `ξ_i - ⟨ξ_i⟩` vanishes. -/
theorem sum_weight_mul_sub_integral (f : α → ℝ) (i : Fin N) :
    ∑ a, (Real.exp (f a) / ∑ x, Real.exp (f x)) *
      (ξ i a - ∫ b, ξ i b ∂(Measure.count.tilted f)) = 0 := by
  have hm : ∫ b, ξ i b ∂(Measure.count.tilted f) =
      ∑ a, (Real.exp (f a) / ∑ x, Real.exp (f x)) * ξ i a := integral_count_tilted f _
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_exp_div_sum_exp, one_mul, ← hm]
  exact sub_self _

/-- **The Gram entry has Gibbs mean zero:** `∑_{a,b} w_a w_b N⁻¹ ∑_i ξ̇_i(a) ξ̇_i(b) = 0`. -/
theorem sum_sum_weight_mul_gram_eq_zero (f : α → ℝ) :
    ∑ a, ∑ b, (Real.exp (f a) / ∑ x, Real.exp (f x)) * (Real.exp (f b) / ∑ x, Real.exp (f x)) *
      ((N : ℝ)⁻¹ * ∑ i, (ξ i a - ∫ x, ξ i x ∂(Measure.count.tilted f)) *
        (ξ i b - ∫ x, ξ i x ∂(Measure.count.tilted f))) = 0 := by
  set w : α → ℝ := fun a => Real.exp (f a) / ∑ x, Real.exp (f x) with hw
  obtain ⟨m, hm⟩ : ∃ m : Fin N → ℝ, ∀ i, m i = ∫ x, ξ i x ∂(Measure.count.tilted f) :=
    ⟨_, fun _ => rfl⟩
  simp only [← hm]
  change ∑ a, ∑ b, w a * w b * ((N : ℝ)⁻¹ * ∑ i, (ξ i a - m i) * (ξ i b - m i)) = 0
  have e : ∀ a b, w a * w b * ((N : ℝ)⁻¹ * ∑ i, (ξ i a - m i) * (ξ i b - m i)) =
      ∑ i, (N : ℝ)⁻¹ * ((w a * (ξ i a - m i)) * (w b * (ξ i b - m i))) := fun a b => by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  have e2 : ∀ a, ∑ b, ∑ i, (N : ℝ)⁻¹ * ((w a * (ξ i a - m i)) * (w b * (ξ i b - m i))) =
      ∑ i, ∑ b, (N : ℝ)⁻¹ * ((w a * (ξ i a - m i)) * (w b * (ξ i b - m i))) :=
    fun a => Finset.sum_comm
  simp_rw [e2]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp_rw [← Finset.mul_sum]
  have h0 : ∑ a, w a * (ξ i a - m i) = 0 := by
    rw [hm]; exact sum_weight_mul_sub_integral ξ f i
  rw [← Finset.sum_mul, h0, zero_mul, mul_zero]

set_option linter.unusedFintypeInType false in
/-- **Sum over the sites of the cavity deviation (model-independent part of Eq. (1.186)).**  For
`±1` observables `ξ_i` on a Gibbs measure `μ = count.tilted f`, a Gaussian vector `y` and a cavity
field `L_y(a) = c ∑ y_j ξ_j(a) + h`,
`∑_i 𝔼_y ⟨ξ̇_i cosh L_y⟩² ≤ N Λ (17/2) E⟨(R - q)²⟩`, with `ξ̇_i = ξ_i - ⟨ξ_i⟩`,
`B = N c²`, `Λ = B e^{2B} (cosh (2h) + 1) / 2` and `q ∈ [0, 1]` arbitrary. -/
theorem sum_integral_gibbs_cosh_sq_le (hξ2 : ∀ i a, ξ i a ^ 2 = 1) (hN : 0 < N) (f : α → ℝ)
    (c h q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ∑ i, ∫ y : Fin N → ℝ, (∫ a, (ξ i a - ∫ b, ξ i b ∂(Measure.count.tilted f)) *
        Real.cosh (c * ∑ j, y j * ξ j a + h) ∂(Measure.count.tilted f)) ^ 2
      ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) ≤
    N * (N * c ^ 2 * Real.exp (2 * (N * c ^ 2)) * (Real.cosh (2 * h) + 1) / 2) * (17 / 2) *
      overlapMoment ξ f q 1 := by
  have hN0 : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set w : α → ℝ := fun a => Real.exp (f a) / ∑ x, Real.exp (f x) with hw
  have hw0 : ∀ a, 0 ≤ w a := fun a =>
    div_nonneg (Real.exp_pos _).le (Finset.sum_pos (fun _ _ => Real.exp_pos _)
      Finset.univ_nonempty).le
  obtain ⟨m, hm⟩ : ∃ m : Fin N → ℝ, ∀ i, m i = ∫ x, ξ i x ∂(Measure.count.tilted f) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : α → α → ℝ, ∀ a b, R a b = (N : ℝ)⁻¹ * ∑ i, ξ i a * ξ i b :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : α → α → ℝ, ∀ a b,
      T a b = (N : ℝ)⁻¹ * ∑ i, (ξ i a - m i) * (ξ i b - m i) := ⟨_, fun _ _ => rfl⟩
  set B : ℝ := N * c ^ 2 with hBdef
  have hB : 0 ≤ B := by positivity
  set Λ : ℝ := B * Real.exp (2 * B) * (Real.cosh (2 * h) + 1) / 2 with hΛ
  have hΛ0 : 0 ≤ Λ := by
    have := Real.cosh_pos (2 * h)
    positivity
  set Fk : ℝ → ℝ := fun x =>
    (Real.cosh (2 * h) * Real.exp (B * (1 + x)) + Real.exp (B * (1 - x))) / 2 with hFk
  have hRle : ∀ a b, |R a b| ≤ 1 := fun a b => by
    rw [hR]
    refine abs_inv_mul_sum_mul_le_one hN ξ (fun i a => ?_) a b
    exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith [hξ2 i a])
  have hq1 : |q| ≤ 1 := abs_le.2 ⟨by linarith [hq.1], hq.2⟩
  -- the Gaussian average
  have hS : ∀ a b, (Real.cosh (2 * h) * Real.exp (c ^ 2 * (N + ∑ i, ξ i a * ξ i b)) +
      Real.exp (c ^ 2 * (N - ∑ i, ξ i a * ξ i b))) / 2 = Fk (R a b) := fun a b => by
    have e1 : c ^ 2 * (N + ∑ i, ξ i a * ξ i b) = B * (1 + R a b) := by
      rw [hR, hBdef]; field_simp
    have e2 : c ^ 2 * (N - ∑ i, ξ i a * ξ i b) = B * (1 - R a b) := by
      rw [hR, hBdef]; field_simp
    rw [e1, e2]
  have hstep1 : ∀ i, ∫ y : Fin N → ℝ, (∫ a, (ξ i a - ∫ b, ξ i b ∂(Measure.count.tilted f)) *
        Real.cosh (c * ∑ j, y j * ξ j a + h) ∂(Measure.count.tilted f)) ^ 2
      ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      ∑ a, ∑ b, w a * w b * ((ξ i a - m i) * (ξ i b - m i)) * Fk (R a b) := fun i => by
    rw [integral_gibbs_cosh_sq ξ hξ2 f c h (fun a => ξ i a - ∫ b, ξ i b ∂(Measure.count.tilted f))]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hS a b, hm i]
  simp_rw [hstep1]
  have hstep2 : ∑ i, ∑ a, ∑ b, w a * w b * ((ξ i a - m i) * (ξ i b - m i)) * Fk (R a b) =
      N * ∑ a, ∑ b, w a * w b * T a b * Fk (R a b) := by
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    have : ∑ i, w a * w b * ((ξ i a - m i) * (ξ i b - m i)) * Fk (R a b) =
        (w a * w b * Fk (R a b)) * ∑ i, (ξ i a - m i) * (ξ i b - m i) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, hT]; field_simp
  rw [hstep2]
  -- centering of the kernel
  have hzero : ∑ a, ∑ b, w a * w b * T a b = 0 := by
    have := sum_sum_weight_mul_gram_eq_zero ξ f
    simp only [← hm, ← hT] at this
    exact this
  set Fq : ℝ := Fk q with hFq
  have hcenter : ∑ a, ∑ b, w a * w b * T a b * Fk (R a b) =
      ∑ a, ∑ b, w a * w b * (T a b * (Fk (R a b) - Fq)) := by
    have : ∑ a, ∑ b, w a * w b * (T a b * (Fk (R a b) - Fq)) =
        ∑ a, ∑ b, w a * w b * T a b * Fk (R a b) - Fq * ∑ a, ∑ b, w a * w b * T a b := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [this, hzero, mul_zero, sub_zero]
  rw [hcenter]
  -- Lipschitz bound
  have hpt : ∀ a b, w a * w b * (T a b * (Fk (R a b) - Fq)) ≤
      Λ / 2 * (w a * w b * (T a b ^ 2 + (R a b - q) ^ 2)) := fun a b => by
    have hL : |Fk (R a b) - Fq| ≤ Λ * |R a b - q| := by
      have := abs_cavityKernel_sub_le hB h (hRle a b) hq1
      simpa only [hFk, hFq, hΛ] using this
    have h1 : T a b * (Fk (R a b) - Fq) ≤ Λ / 2 * (T a b ^ 2 + (R a b - q) ^ 2) := by
      calc T a b * (Fk (R a b) - Fq) ≤ |T a b * (Fk (R a b) - Fq)| := le_abs_self _
        _ = |T a b| * |Fk (R a b) - Fq| := abs_mul _ _
        _ ≤ |T a b| * (Λ * |R a b - q|) := by gcongr
        _ ≤ Λ / 2 * (T a b ^ 2 + (R a b - q) ^ 2) := by
          nlinarith [sq_nonneg (|T a b| - |R a b - q|), sq_abs (T a b), sq_abs (R a b - q)]
    have hww : 0 ≤ w a * w b := mul_nonneg (hw0 a) (hw0 b)
    calc w a * w b * (T a b * (Fk (R a b) - Fq))
        ≤ w a * w b * (Λ / 2 * (T a b ^ 2 + (R a b - q) ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 hww
      _ = _ := by ring
  -- moments of the Gram entry and of the overlap
  have hOM : overlapMoment ξ f q 1 = ∑ a, ∑ b, w a * w b * (R a b - q) ^ 2 := by
    unfold overlapMoment
    have h2 := integral_pi_fin_two_count_tilted f
      (fun a b => ((N : ℝ)⁻¹ * ∑ i, ξ i a * ξ i b - q) ^ (2 * 1))
    rw [h2]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hw, hR, mul_one]
  have hTm : ∑ a, ∑ b, w a * w b * T a b ^ 2 ≤ 16 * overlapMoment ξ f q 1 := by
    obtain ⟨u, hu⟩ : ∃ u : α → Fin N → ℝ, ∀ a j, u a j = (Real.sqrt N)⁻¹ * (ξ j a - m j) :=
      ⟨_, fun _ _ => rfl⟩
    have hu' : ∀ a j, u a j = (Real.sqrt N)⁻¹ * (ξ j a - ∫ b, ξ j b ∂(Measure.count.tilted f)) :=
      fun a j => by rw [hu, hm]
    have hv : Real.sqrt (1 - q) ^ 2 = 1 - q := Real.sq_sqrt (by linarith [hq.2])
    have h := integral_projGram_pow_le ξ hξ2 hN (m := 2) f u hu' q _ hv (k := 1) le_rfl 0 1
    have hdot : ∀ a b, u a ⬝ᵥ u b = T a b := fun a b => by
      rw [hT, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have : (Real.sqrt N)⁻¹ * (Real.sqrt N)⁻¹ = (N : ℝ)⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg N)]
      rw [hu, hu, ← this]; ring
    have h01 : ((0 : Fin 2) = 1) = False := by decide
    simp only [h01, ite_false, sub_zero, hdot] at h
    rw [integral_pi_fin_two_count_tilted f (fun a b => T a b ^ (2 * 1))] at h
    simp only [mul_one] at h
    have h16 : (4 : ℝ) ^ 2 = 16 := by norm_num
    rw [h16] at h
    exact h
  have hsum : ∑ a, ∑ b, Λ / 2 * (w a * w b * (T a b ^ 2 + (R a b - q) ^ 2)) ≤
      Λ / 2 * (16 * overlapMoment ξ f q 1 + overlapMoment ξ f q 1) := by
    have : ∑ a, ∑ b, Λ / 2 * (w a * w b * (T a b ^ 2 + (R a b - q) ^ 2)) =
        Λ / 2 * (∑ a, ∑ b, w a * w b * T a b ^ 2 + ∑ a, ∑ b, w a * w b * (R a b - q) ^ 2) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [this, ← hOM]
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  calc (N : ℝ) * ∑ a, ∑ b, w a * w b * (T a b * (Fk (R a b) - Fq))
      ≤ N * (Λ / 2 * (16 * overlapMoment ξ f q 1 + overlapMoment ξ f q 1)) :=
        mul_le_mul_of_nonneg_left ((Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          hpt a b).trans hsum) hN0.le
    _ = _ := by rw [hΛ]; ring

end Gibbs

end SpinGlasses
