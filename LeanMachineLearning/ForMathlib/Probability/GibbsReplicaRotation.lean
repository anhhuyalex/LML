/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct

/-!
# Derivative of a replica Gibbs average along a rotation path

For an energy `E₀(a) + u(cos r · X(a) + sin r · Y(a))` the path parameter `r` rotates the pair
`(X, Y)`. This is the shape of the interpolation in Talagrand's cavity in `M` (Section 2.3), where
`X` is the removed constraint's field and `Y = √q z + √(1-q) ξ`.

* `hasDerivAt_integral_pi_tilted_rotation`: the derivative at `t` of the `R`-replica average of a
  bounded measurable observable is the covariance of the observable with `∑ᵢ E'(σᵢ)`, where
  `E' = u'(cos t X + sin t Y) (-sin t X + cos t Y)` is the pathwise derivative of the energy.

Only the exponential bound `E₀ + u ≤ B` and integrability of `|X| + |Y|` are used: the unbounded
Gaussian factor `-sin t X + cos t Y` is dominated by `|X| + |Y|`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace MeasureTheory

/-- **Derivative of a replica average along a rotation path.** -/
theorem hasDerivAt_integral_pi_tilted_rotation {α R : Type*} [MeasurableSpace α] [Fintype R]
    {ρ : Measure α} [IsFiniteMeasure ρ] [NeZero ρ] {E₀ X Y : α → ℝ} (hE₀ : Measurable E₀)
    (hX : Measurable X) (hY : Measurable Y) {u : ℝ → ℝ} (hu : Differentiable ℝ u) {B₀ B₁ D : ℝ}
    (hE₀b : ∀ a, E₀ a ≤ B₀) (hub : ∀ x, u x ≤ B₁) (hD : ∀ x, |deriv u x| ≤ D)
    (hint : Integrable (fun a => |X a| + |Y a|) ρ) {f : (R → α) → ℝ} (hf : Measurable f)
    {C : ℝ} (hfb : ∀ σ, |f σ| ≤ C) (t : ℝ) :
    HasDerivAt (fun r => ∫ σ, f σ ∂(Measure.pi fun _ : R =>
        ρ.tilted fun a => E₀ a + u (Real.cos r * X a + Real.sin r * Y a)))
      ((∫ σ, f σ * ∑ i, (deriv u (Real.cos t * X (σ i) + Real.sin t * Y (σ i)) *
          (-Real.sin t * X (σ i) + Real.cos t * Y (σ i)))
          ∂(Measure.pi fun _ : R => ρ.tilted fun a =>
            E₀ a + u (Real.cos t * X a + Real.sin t * Y a))) -
        (∫ σ, f σ ∂(Measure.pi fun _ : R => ρ.tilted fun a =>
            E₀ a + u (Real.cos t * X a + Real.sin t * Y a))) *
          ∫ σ, ∑ i, (deriv u (Real.cos t * X (σ i) + Real.sin t * Y (σ i)) *
            (-Real.sin t * X (σ i) + Real.cos t * Y (σ i)))
            ∂(Measure.pi fun _ : R => ρ.tilted fun a =>
              E₀ a + u (Real.cos t * X a + Real.sin t * Y a))) t := by
  have hum : Measurable u := hu.continuous.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have h := hasDerivAt_integral_pi_tilted_moving (R := R) (μ := ρ)
    (E := fun r a => E₀ a + u (Real.cos r * X a + Real.sin r * Y a))
    (E' := fun r a => deriv u (Real.cos r * X a + Real.sin r * Y a) *
      (-Real.sin r * X a + Real.cos r * Y a))
    (t := t) (s := Set.univ) Filter.univ_mem
    (fun r _ => by fun_prop)
    (by
      refine (hdu.comp (by fun_prop)).mul (by fun_prop))
    (B := B₀ + B₁) (fun r _ a => add_le_add (hE₀b a) (hub _))
    (b := fun a => D * (|X a| + |Y a|)) (hint.const_mul D)
    (fun r _ a => by
      rw [abs_mul]
      have hs := Real.abs_sin_le_one r
      have hc := Real.abs_cos_le_one r
      calc _ ≤ D * (|X a| + |Y a|) := by
            refine mul_le_mul (hD _) ?_ (abs_nonneg _) hD0
            calc |-Real.sin r * X a + Real.cos r * Y a|
                ≤ |-Real.sin r * X a| + |Real.cos r * Y a| := abs_add_le _ _
              _ = |Real.sin r| * |X a| + |Real.cos r| * |Y a| := by
                  rw [abs_mul, abs_mul, abs_neg]
              _ ≤ 1 * |X a| + 1 * |Y a| :=
                  add_le_add (mul_le_mul_of_nonneg_right hs (abs_nonneg _))
                    (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
              _ = |X a| + |Y a| := by ring
        _ = _ := rfl)
    (fun a r _ => by
      have hin : HasDerivAt (fun q => Real.cos q * X a + Real.sin q * Y a)
          (-Real.sin r * X a + Real.cos r * Y a) r :=
        ((Real.hasDerivAt_cos r).mul_const (X a)).add ((Real.hasDerivAt_sin r).mul_const (Y a))
      exact (((hu.differentiableAt).hasDerivAt.comp r hin).const_add (E₀ a)))
    (Ψ := fun _ => f) (Ψ' := fun _ _ => 0) (fun r _ => hf) measurable_const
    (C := C) (C' := 0) (fun r _ σ => hfb σ) (fun r _ σ => by simp)
    (fun σ r _ => hasDerivAt_const r (f σ))
  simpa using h

/-- **Derivative along a rotation path of an average with a moving two-replica factor.** The
observable is `f σ · u'(S_r(σ_i)) u'(S_r(σ_j))` with `S_r = cos r X + sin r Y`, which moves with the
path parameter; its derivative contains the unbounded Gaussian factor `-sin r X + cos r Y` and is
dominated by `C D D₂ (w(σ_i) + w(σ_j))`, `w = |X| + |Y|`. This is the setting of the cavity
`B_v = u'(S_v^1) u'(S_v^2)`. -/
theorem hasDerivAt_integral_pi_tilted_rotation_deriv_mul {α R : Type*} [MeasurableSpace α]
    [Fintype R] {ρ : Measure α} [IsFiniteMeasure ρ] [NeZero ρ] {E₀ X Y : α → ℝ}
    (hE₀ : Measurable E₀) (hX : Measurable X) (hY : Measurable Y) {u : ℝ → ℝ}
    (hu : Differentiable ℝ u) (hu₂ : Differentiable ℝ (deriv u)) {B₀ B₁ D D₂ : ℝ}
    (hE₀b : ∀ a, E₀ a ≤ B₀) (hub : ∀ x, u x ≤ B₁) (hD : ∀ x, |deriv u x| ≤ D)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂)
    (hint : Integrable (fun a => |X a| + |Y a|) ρ) {f : (R → α) → ℝ} (hf : Measurable f)
    {C : ℝ} (hfb : ∀ σ, |f σ| ≤ C) (i j : R) (t : ℝ) :
    HasDerivAt (fun r => ∫ σ, f σ * (deriv u (Real.cos r * X (σ i) + Real.sin r * Y (σ i)) *
        deriv u (Real.cos r * X (σ j) + Real.sin r * Y (σ j))) ∂(Measure.pi fun _ : R =>
        ρ.tilted fun a => E₀ a + u (Real.cos r * X a + Real.sin r * Y a)))
      ((∫ σ, f σ * (deriv (deriv u) (Real.cos t * X (σ i) + Real.sin t * Y (σ i)) *
          (-Real.sin t * X (σ i) + Real.cos t * Y (σ i)) *
          deriv u (Real.cos t * X (σ j) + Real.sin t * Y (σ j)) +
        deriv u (Real.cos t * X (σ i) + Real.sin t * Y (σ i)) *
          (deriv (deriv u) (Real.cos t * X (σ j) + Real.sin t * Y (σ j)) *
            (-Real.sin t * X (σ j) + Real.cos t * Y (σ j))))
          ∂(Measure.pi fun _ : R => ρ.tilted fun a =>
            E₀ a + u (Real.cos t * X a + Real.sin t * Y a))) +
      ((∫ σ, f σ * (deriv u (Real.cos t * X (σ i) + Real.sin t * Y (σ i)) *
          deriv u (Real.cos t * X (σ j) + Real.sin t * Y (σ j))) *
          ∑ k, (deriv u (Real.cos t * X (σ k) + Real.sin t * Y (σ k)) *
            (-Real.sin t * X (σ k) + Real.cos t * Y (σ k)))
          ∂(Measure.pi fun _ : R => ρ.tilted fun a =>
            E₀ a + u (Real.cos t * X a + Real.sin t * Y a))) -
        (∫ σ, f σ * (deriv u (Real.cos t * X (σ i) + Real.sin t * Y (σ i)) *
          deriv u (Real.cos t * X (σ j) + Real.sin t * Y (σ j)))
          ∂(Measure.pi fun _ : R => ρ.tilted fun a =>
            E₀ a + u (Real.cos t * X a + Real.sin t * Y a))) *
          ∫ σ, ∑ k, (deriv u (Real.cos t * X (σ k) + Real.sin t * Y (σ k)) *
            (-Real.sin t * X (σ k) + Real.cos t * Y (σ k)))
            ∂(Measure.pi fun _ : R => ρ.tilted fun a =>
              E₀ a + u (Real.cos t * X a + Real.sin t * Y a)))) t := by
  have hum : Measurable u := hu.continuous.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  have hddu : Measurable (deriv (deriv u)) := measurable_deriv (deriv u)
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hD₂0 : 0 ≤ D₂ := (abs_nonneg _).trans (hD₂ 0)
  obtain ⟨a₀, -⟩ := nonempty_of_measure_ne_zero (NeZero.ne (ρ Set.univ))
  have : Nonempty α := ⟨a₀⟩
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hfb fun _ => Classical.arbitrary α)
  have hw0 (a : α) : 0 ≤ |X a| + |Y a| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hz (r : ℝ) (a : α) : |-Real.sin r * X a + Real.cos r * Y a| ≤ |X a| + |Y a| := by
    calc |-Real.sin r * X a + Real.cos r * Y a|
        ≤ |-Real.sin r * X a| + |Real.cos r * Y a| := abs_add_le _ _
      _ = |Real.sin r| * |X a| + |Real.cos r| * |Y a| := by rw [abs_mul, abs_mul, abs_neg]
      _ ≤ 1 * |X a| + 1 * |Y a| :=
          add_le_add (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one r) (abs_nonneg _))
            (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one r) (abs_nonneg _))
      _ = |X a| + |Y a| := by ring
  have hin (a : α) (r : ℝ) : HasDerivAt (fun q => Real.cos q * X a + Real.sin q * Y a)
      (-Real.sin r * X a + Real.cos r * Y a) r :=
    ((Real.hasDerivAt_cos r).mul_const (X a)).add ((Real.hasDerivAt_sin r).mul_const (Y a))
  have hG (a : α) (r : ℝ) : HasDerivAt
      (fun q => deriv u (Real.cos q * X a + Real.sin q * Y a))
      (deriv (deriv u) (Real.cos r * X a + Real.sin r * Y a) *
        (-Real.sin r * X a + Real.cos r * Y a)) r :=
    (hu₂ _).hasDerivAt.comp r (hin a r)
  have hwI : Integrable (fun σ : R → α =>
      (|X (σ i)| + |Y (σ i)|) + (|X (σ j)| + |Y (σ j)|)) (Measure.pi fun _ : R => ρ) :=
    (integrable_comp_eval (μ := fun _ : R => ρ) (i := i) hint).add
      (integrable_comp_eval (μ := fun _ : R => ρ) (i := j) hint)
  have h := hasDerivAt_integral_pi_tilted_moving_of_integrable (R := R) (μ := ρ)
    (E := fun r a => E₀ a + u (Real.cos r * X a + Real.sin r * Y a))
    (E' := fun r a => deriv u (Real.cos r * X a + Real.sin r * Y a) *
      (-Real.sin r * X a + Real.cos r * Y a))
    (t := t) (s := Set.univ) Filter.univ_mem (fun r _ => by fun_prop)
    ((hdu.comp (by fun_prop)).mul (by fun_prop)) (B := B₀ + B₁)
    (fun r _ a => add_le_add (hE₀b a) (hub _)) (b := fun a => D * (|X a| + |Y a|))
    (hint.const_mul D)
    (fun r _ a => by
      rw [abs_mul]
      exact mul_le_mul (hD _) (hz r a) (abs_nonneg _) hD0)
    (fun a r _ => ((hu.differentiableAt).hasDerivAt.comp r (hin a r)).const_add (E₀ a))
    (Ψ := fun r σ => f σ * (deriv u (Real.cos r * X (σ i) + Real.sin r * Y (σ i)) *
      deriv u (Real.cos r * X (σ j) + Real.sin r * Y (σ j))))
    (Ψ' := fun r σ => f σ * (deriv (deriv u) (Real.cos r * X (σ i) + Real.sin r * Y (σ i)) *
        (-Real.sin r * X (σ i) + Real.cos r * Y (σ i)) *
        deriv u (Real.cos r * X (σ j) + Real.sin r * Y (σ j)) +
      deriv u (Real.cos r * X (σ i) + Real.sin r * Y (σ i)) *
        (deriv (deriv u) (Real.cos r * X (σ j) + Real.sin r * Y (σ j)) *
          (-Real.sin r * X (σ j) + Real.cos r * Y (σ j)))))
    (fun r _ => by fun_prop) (by fun_prop) (C := C * (D * D))
    (fun r _ σ => by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (hfb σ) (mul_le_mul (hD _) (hD _) (abs_nonneg _) hD0)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hC0)
    (b₂ := fun σ => C * (D * D₂) * ((|X (σ i)| + |Y (σ i)|) + (|X (σ j)| + |Y (σ j)|)))
    (hwI.const_mul _)
    (fun r _ σ => by
      rw [abs_mul]
      have e1 : |deriv (deriv u) (Real.cos r * X (σ i) + Real.sin r * Y (σ i)) *
          (-Real.sin r * X (σ i) + Real.cos r * Y (σ i)) *
          deriv u (Real.cos r * X (σ j) + Real.sin r * Y (σ j))| ≤
          D₂ * (|X (σ i)| + |Y (σ i)|) * D := by
        rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul (hD₂ _) (hz r _) (abs_nonneg _) hD₂0) (hD _)
          (abs_nonneg _) (mul_nonneg hD₂0 (hw0 _))
      have e2 : |deriv u (Real.cos r * X (σ i) + Real.sin r * Y (σ i)) *
          (deriv (deriv u) (Real.cos r * X (σ j) + Real.sin r * Y (σ j)) *
            (-Real.sin r * X (σ j) + Real.cos r * Y (σ j)))| ≤
          D * (D₂ * (|X (σ j)| + |Y (σ j)|)) := by
        rw [abs_mul, abs_mul]
        exact mul_le_mul (hD _) (mul_le_mul (hD₂ _) (hz r _) (abs_nonneg _) hD₂0)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hD0
      calc _ ≤ C * (D₂ * (|X (σ i)| + |Y (σ i)|) * D + D * (D₂ * (|X (σ j)| + |Y (σ j)|))) :=
            mul_le_mul (hfb σ) ((abs_add_le _ _).trans (add_le_add e1 e2)) (abs_nonneg _) hC0
        _ = _ := by ring)
    (fun σ r _ => ((hG (σ i) r).mul (hG (σ j) r)).const_mul (f σ))
  simpa using h


end MeasureTheory
