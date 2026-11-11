/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.FreeEnergy.LogPartition
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Stationarity of the replica-symmetric functional (Talagrand Lemma 1.12.6)

The partial derivatives of `Φ = -(β²/4) ∑ (ρᵤᵥ² - qᵤᵥ²) + 𝔼 log ∫ ℰ dμ` in the free parameters `ρ`
and `q` vanish exactly when Eqs. (1.373) and (1.372) hold.  The derivative in `ρ` is taken in an
arbitrary matrix direction; the derivative in `q` is taken along a segment between two covariance
matrices (a Gaussian interpolation, Proposition 1.3.2), which is how admissible directions are
described at singular covariances.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

variable {α D Ω : Type*} [MeasurableSpace α] [Fintype D] [MeasurableSpace Ω]

/-- **Linearity of the Gibbs average in the observable.**  For a quadratic observable
`∑ᵤᵥ cᵤᵥ ξᵤ ξᵥ` the Gibbs average is the combination of the Gibbs averages of `ξᵤ ξᵥ`. -/
theorem gibbs_ratio_sum_sum {μ : Measure α} (ξ : α → D → ℝ) (c : D → D → ℝ) (e : α → ℝ)
    (hint : ∀ u v, Integrable (fun a => ξ a u * ξ a v * Real.exp (e a)) μ) :
    (∫ a, (∑ u, ∑ v, c u v * (ξ a u * ξ a v)) * Real.exp (e a) ∂μ) /
        ∫ a, Real.exp (e a) ∂μ =
      ∑ u, ∑ v, c u v * ((∫ a, ξ a u * ξ a v * Real.exp (e a) ∂μ) /
        ∫ a, Real.exp (e a) ∂μ) := by
  have hpt : ∀ a, (∑ u, ∑ v, c u v * (ξ a u * ξ a v)) * Real.exp (e a) =
      ∑ u, ∑ v, c u v * (ξ a u * ξ a v * Real.exp (e a)) := by
    intro a
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  rw [integral_congr_ae (ae_of_all _ hpt),
    integral_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ => (hint u v).const_mul _,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [integral_finsetSum _ fun v _ => (hint u v).const_mul _, Finset.sum_div]
  exact Finset.sum_congr rfl fun v _ => by rw [integral_const_mul]; ring

/-- **Lemma 1.12.6, the derivative in `ρ`.**  In every matrix direction `E` the derivative of
`𝔼 log ∫ ℰ dμ` with respect to `ρ` is `(β²/2) ∑ᵤᵥ Eᵤᵥ 𝔼⟨ξᵤ ξᵥ⟩`. -/
theorem hasDerivAt_skVectorGaussianFreeEnergy_rho (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → D → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u)) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r) (ρ q E : D → D → ℝ)
    {P : Measure Ω} [IsProbabilityMeasure P] {X : D → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω u => X u ω) P) (hXm : ∀ u, Measurable (X u))
    (hX0 : ∀ u, ∫ ω, X u ω ∂P = 0) (β s₀ : ℝ) :
    HasDerivAt (fun s => skVectorGaussianFreeEnergy μ ξ (fun u v => ρ u v + s * E u v) q P X β)
      (β ^ 2 / 2 * ∑ u, ∑ v, E u v * ∫ ω, ∫ a, ξ a u * ξ a v ∂(μ.tilted
        (fun a => β * ∑ w, X w ω * ξ a w +
          β ^ 2 / 2 * ∑ w, ∑ w', ξ a w * ξ a w' * (ρ w w' + s₀ * E w w' - q w w'))) ∂P) s₀ := by
  classical
  set Xs : Unit → α → ℝ := fun _ a => ∑ w, ∑ w', E w w' * (ξ a w * ξ a w') with hXs
  set Xf : D → α → ℝ := fun u a => ξ a u with hXf
  set D0 : α → ℝ := fun a => β ^ 2 / 2 * ∑ w, ∑ w', ξ a w * ξ a w' * (ρ w w' - q w w') with hD0
  have hξb : ∀ a u, |ξ a u| ≤ Real.sqrt r := abs_spin_le ξ hbound
  have hξξ : ∀ a u v, |ξ a u * ξ a v| ≤ r := fun a u v =>
    abs_spin_mul_le ξ hr hbound a a u v
  set B : ℝ := Real.sqrt r + ∑ w, ∑ w', r * |E w w'| with hBdef
  have hB0 : 0 ≤ B := by positivity
  set Eb : ℝ := β ^ 2 / 2 * ∑ w, ∑ w', r * |ρ w w' - q w w'| with hEb
  have hξm2 : ∀ u v, Measurable fun a => ξ a u * ξ a v := fun u v => (hξ u).mul (hξ v)
  have hD0m : Measurable D0 :=
    measurable_const.mul (Finset.measurable_sum _ fun w _ => Finset.measurable_sum _ fun w' _ =>
      (hξm2 w w').mul measurable_const)
  have hD0b : ∀ a, |D0 a| ≤ Eb := fun a => by
    simp only [hD0, hEb]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ β ^ 2 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w' _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hξξ a w w') (abs_nonneg _)
  have hXfm : ∀ u, Measurable (Xf u) := hξ
  have hXfb : ∀ u a, |Xf u a| ≤ B := fun u a => by
    have : 0 ≤ ∑ w, ∑ w', r * |E w w'| := by positivity
    linarith [hξb a u]
  have hXsm : ∀ j, Measurable (Xs j) := fun j =>
    Finset.measurable_sum _ fun w _ => Finset.measurable_sum _ fun w' _ =>
      measurable_const.mul (hξm2 w w')
  have hXsb : ∀ j a, |Xs j a| ≤ B := fun j a => by
    have h1 : |∑ w, ∑ w', E w w' * (ξ a w * ξ a w')| ≤ ∑ w, ∑ w', r * |E w w'| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w' _ => ?_)
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hξξ a w w') (abs_nonneg _)
    have := Real.sqrt_nonneg r
    simp only [hXs]
    linarith
  set R : (α → ℝ) → (D ⊕ Unit → ℝ) → ℝ := fun Y z =>
    (∫ a, Y a * Real.exp (D0 a + ∑ k, z k * Sum.elim Xf Xs k a) ∂μ) /
      ∫ a, Real.exp (D0 a + ∑ k, z k * Sum.elim Xf Xs k a) ∂μ with hRdef
  have hmain := hasDerivAt_integral_log_partition_cavity_path (μ := μ) (P := P)
    (D := D0) (X := Xf) (Xs := Xs) (Eb := Eb) (B := B) R (fun _ _ => rfl)
    hD0m hXfm hXsm hB0 hD0b hXfb hXsb
    (Z := X) hX hXm hX0 (s := fun _ _ => β) (s' := fun _ _ => (0 : ℝ))
    (c := fun _ b => β ^ 2 / 2 * b) (c' := fun _ _ => β ^ 2 / 2) (t := s₀) (δ := 1)
    (C := β ^ 2 / 2) one_pos
    (fun _ r _ => hasDerivAt_const r β)
    (fun _ r _ => (hasDerivAt_id r).const_mul _ |>.congr_deriv (by ring))
    (fun _ r _ => by simp only [abs_zero]; positivity)
    (fun _ r _ => by rw [abs_of_nonneg (by positivity)])
    (fun _ => Or.inl rfl)
  have hexpo : ∀ (ω : Ω) (a : α) (r' : ℝ), D0 a +
      ∑ l : D ⊕ Unit, Sum.elim (fun k => β * X k ω) (fun _ => β ^ 2 / 2 * r') l *
        Sum.elim Xf Xs l a =
      β * ∑ u, X u ω * ξ a u +
        β ^ 2 / 2 * ∑ w, ∑ w', ξ a w * ξ a w' * (ρ w w' + r' * E w w' - q w w') := by
    intro ω a r'
    have h : ∑ w, ∑ w', ξ a w * ξ a w' * (ρ w w' + r' * E w w' - q w w') =
        ∑ w, ∑ w', ξ a w * ξ a w' * (ρ w w' - q w w') +
          r' * ∑ w, ∑ w', E w w' * (ξ a w * ξ a w') := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => by ring
    rw [h]
    have h2 : ∑ k, β * X k ω * ξ a k = β * ∑ u, X u ω * ξ a u := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hXf, hXs, hD0,
      Finset.univ_unique, Finset.sum_singleton, h2]
    ring
  have hfun : (fun s => skVectorGaussianFreeEnergy μ ξ (fun u v => ρ u v + s * E u v) q P X β) =
      fun r' => ∫ ω, Real.log (∫ a, Real.exp (D0 a + ∑ l : D ⊕ Unit,
        Sum.elim (fun k => β * X k ω) (fun _ => β ^ 2 / 2 * r') l * Sum.elim Xf Xs l a) ∂μ)
        ∂P := by
    funext r'
    unfold skVectorGaussianFreeEnergy
    simp only [hexpo]
  rw [hfun]
  refine hmain.congr_deriv ?_
  obtain ⟨zt, hzt⟩ : ∃ zt : Ω → D ⊕ Unit → ℝ, ∀ ω,
      zt ω = Sum.elim (fun k => β * X k ω) fun _ => β ^ 2 / 2 * s₀ := ⟨_, fun _ => rfl⟩
  simp only [← hzt]
  have hztm : Measurable zt := by
    refine measurable_pi_iff.2 fun l => ?_
    rcases l with k | j
    · simpa [hzt] using (hXm k).const_mul β
    · simp [hzt]
  have hXall : ∀ l, Measurable (Sum.elim Xf Xs l) := by
    rintro (k | j)
    · exact hXfm k
    · exact hXsm j
  have hXallb : ∀ l a, |Sum.elim Xf Xs l a| ≤ B := by
    rintro (k | j) a
    · exact hXfb k a
    · exact hXsb j a
  have hRcont : ∀ (Y : α → ℝ) (M : ℝ), 0 ≤ M → Measurable Y → (∀ a, |Y a| ≤ M) →
      Continuous (R Y) := fun Y M hM hY hYb =>
    continuous_gibbs_ratio_linear (μ := μ) (K := D ⊕ Unit) (X := Sum.elim Xf Xs)
      (D := D0) (Eb := Eb) R (fun _ _ => rfl) hD0m hXall hY hB0 hM hD0b hXallb hYb
  have hRb : ∀ (Y : α → ℝ) (M : ℝ), (∀ a, |Y a| ≤ M) → ∀ z, |R Y z| ≤ M := fun Y M hYb z =>
    abs_gibbs_ratio_le (μ := μ) (K := D ⊕ Unit) (X := Sum.elim Xf Xs) (D := D0)
      (Eb := Eb) hD0m hXall hD0b hXallb hYb z
  have hRz : ∀ (Y : α → ℝ) ω, R Y (zt ω) = ∫ a, Y a ∂(μ.tilted (fun a => β * ∑ w, X w ω * ξ a w +
      β ^ 2 / 2 * ∑ w, ∑ w', ξ a w * ξ a w' * (ρ w w' + s₀ * E w w' - q w w'))) := by
    intro Y ω
    simp only [hRdef, hzt, hexpo]
    rw [integral_tilted, ← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [smul_eq_mul]
    ring
  have hi1 : ∀ u v, Integrable (fun ω => R (fun a => ξ a u * ξ a v) (zt ω)) P := fun u v =>
    (integrable_const r).mono'
      ((hRcont _ r hr (hξm2 u v) (hξξ · u v)).measurable.comp hztm).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hRb _ r (hξξ · u v) _)
  have hlin : ∀ ω, R (Xs ()) (zt ω) = ∑ w, ∑ w', E w w' * R (fun a => ξ a w * ξ a w') (zt ω) := by
    intro ω
    simp only [hRdef, hzt, hexpo]
    have hexpI := integrable_exp_linear (μ := μ) (K := D ⊕ Unit) (X := Sum.elim Xf Xs)
      (D := D0) (Eb := Eb) hD0m hXall hD0b hXallb (zt ω)
    simp only [hzt, hexpo] at hexpI
    refine gibbs_ratio_sum_sum ξ E _ fun w w' => ?_
    exact hexpI.bdd_mul (hξm2 w w').aestronglyMeasurable (c := r)
      (ae_of_all _ fun a => by simpa [Real.norm_eq_abs] using hξξ a w w')
  simp only [Finset.univ_unique, Finset.sum_singleton, zero_mul, Finset.sum_const_zero,
    zero_add]
  simp only [hlin]
  have hsum : ∫ ω, ∑ w, ∑ w', E w w' * R (fun a => ξ a w * ξ a w') (zt ω) ∂P =
      ∑ w, ∑ w', E w w' * ∫ ω, R (fun a => ξ a w * ξ a w') (zt ω) ∂P := by
    rw [integral_finsetSum Finset.univ fun w _ => integrable_finsetSum Finset.univ
      fun w' _ => (hi1 w w').const_mul (E w w')]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [integral_finsetSum Finset.univ fun w' _ => (hi1 w w').const_mul (E w w')]
    exact Finset.sum_congr rfl fun w' _ => integral_const_mul _ _
  rw [hsum]
  simp only [hRz]

/-- **Lemma 1.12.6, the derivative in `q`** (Gaussian interpolation, Proposition 1.3.2).  Along the
segment `q(t) = t q₁ + (1 - t) q₀` between two covariance matrices, realized by the independent
Gaussian vectors `Z₁`, `Z₀`, the derivative of `𝔼 log ∫ ℰ dμ` at `0 < t < 1` is
`-(β²/2) ∑ᵤᵥ (q₁ - q₀)ᵤᵥ 𝔼 ⟨ξᵤ⟩⟨ξᵥ⟩`. -/
theorem hasDerivAt_skVectorSegment (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → D → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u)) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r) (ρ q₀ q₁ : D → D → ℝ)
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : D ⊕ D → Ω → ℝ}
    (hZ : HasGaussianLaw (fun ω l => Z l ω) P) (hZm : ∀ l, Measurable (Z l))
    (hZ0 : ∀ l, ∫ ω, Z l ω ∂P = 0)
    (h11 : ∀ u v, ∫ ω, Z (.inl u) ω * Z (.inl v) ω ∂P = q₁ u v)
    (h00 : ∀ u v, ∫ ω, Z (.inr u) ω * Z (.inr v) ω ∂P = q₀ u v)
    (h10 : ∀ u v, ∫ ω, Z (.inl u) ω * Z (.inr v) ω ∂P = 0)
    {β : ℝ} (hβ : β ≠ 0) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun s => ∫ ω, Real.log (∫ a, Real.exp (skVectorFieldExponent ξ β ρ
        (fun u v => s * q₁ u v + (1 - s) * q₀ u v)
        (fun u => β * (Real.sqrt s * Z (.inl u) ω +
          Real.sqrt (1 - s) * Z (.inr u) ω)) a) ∂μ) ∂P)
      (-(β ^ 2 / 2) * ∑ u, ∑ v, (q₁ u v - q₀ u v) * ∫ ω,
        (∫ a, ξ a u ∂(μ.tilted (skVectorFieldExponent ξ β ρ
          (fun u v => t * q₁ u v + (1 - t) * q₀ u v)
          (fun u => β * (Real.sqrt t * Z (.inl u) ω +
            Real.sqrt (1 - t) * Z (.inr u) ω))))) *
        (∫ a, ξ a v ∂(μ.tilted (skVectorFieldExponent ξ β ρ
          (fun u v => t * q₁ u v + (1 - t) * q₀ u v)
          (fun u => β * (Real.sqrt t * Z (.inl u) ω +
            Real.sqrt (1 - t) * Z (.inr u) ω))))) ∂P) t := by
  classical
  set Xs : Unit → α → ℝ := fun _ a => ∑ w, ∑ w', (q₁ w w' - q₀ w w') * (ξ a w * ξ a w') with hXs
  set Xf : D ⊕ D → α → ℝ := Sum.elim (fun u a => ξ a u) (fun u a => ξ a u) with hXf
  set D0 : α → ℝ := fun a => β ^ 2 / 2 * ∑ w, ∑ w', ξ a w * ξ a w' * (ρ w w' - q₀ w w') with hD0
  have hξb : ∀ a u, |ξ a u| ≤ Real.sqrt r := abs_spin_le ξ hbound
  have hξξ : ∀ a u v, |ξ a u * ξ a v| ≤ r := fun a u v =>
    abs_spin_mul_le ξ hr hbound a a u v
  set B : ℝ := Real.sqrt r + ∑ w, ∑ w', r * |q₁ w w' - q₀ w w'| with hBdef
  have hB0 : 0 ≤ B := by positivity
  set Eb : ℝ := β ^ 2 / 2 * ∑ w, ∑ w', r * |ρ w w' - q₀ w w'| with hEb
  have hξm2 : ∀ u v, Measurable fun a => ξ a u * ξ a v := fun u v => (hξ u).mul (hξ v)
  have hD0m : Measurable D0 :=
    measurable_const.mul (Finset.measurable_sum _ fun w _ => Finset.measurable_sum _ fun w' _ =>
      (hξm2 w w').mul measurable_const)
  have hD0b : ∀ a, |D0 a| ≤ Eb := fun a => by
    simp only [hD0, hEb]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ β ^ 2 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w' _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hξξ a w w') (abs_nonneg _)
  have hXfm : ∀ k, Measurable (Xf k) := by
    rintro (u | u) <;> exact hξ u
  have hXfb : ∀ k a, |Xf k a| ≤ B := by
    rintro (u | u) a <;>
    · have : 0 ≤ ∑ w, ∑ w', r * |q₁ w w' - q₀ w w'| := by positivity
      simp only [hXf, Sum.elim_inl, Sum.elim_inr]
      linarith [hξb a u]
  have hXsm : ∀ j, Measurable (Xs j) := fun j =>
    Finset.measurable_sum _ fun w _ => Finset.measurable_sum _ fun w' _ =>
      measurable_const.mul (hξm2 w w')
  have hXsb : ∀ j a, |Xs j a| ≤ B := fun j a => by
    have h1 : |∑ w, ∑ w', (q₁ w w' - q₀ w w') * (ξ a w * ξ a w')| ≤
        ∑ w, ∑ w', r * |q₁ w w' - q₀ w w'| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w' _ => ?_)
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hξξ a w w') (abs_nonneg _)
    have := Real.sqrt_nonneg r
    simp only [hXs]
    linarith
  set R : (α → ℝ) → ((D ⊕ D) ⊕ Unit → ℝ) → ℝ := fun Y z =>
    (∫ a, Y a * Real.exp (D0 a + ∑ k, z k * Sum.elim Xf Xs k a) ∂μ) /
      ∫ a, Real.exp (D0 a + ∑ k, z k * Sum.elim Xf Xs k a) ∂μ with hRdef
  -- the time window
  set m : ℝ := min t (1 - t) / 2 with hmdef
  have hm : 0 < m := by
    have := lt_min ht0 (sub_pos.2 ht1)
    simp only [hmdef]; positivity
  have hmt : m ≤ t / 2 := by
    have := min_le_left t (1 - t); simp only [hmdef]; linarith
  have hmt' : m ≤ (1 - t) / 2 := by
    have := min_le_right t (1 - t); simp only [hmdef]; linarith
  have hball : ∀ r ∈ Metric.ball t m, m ≤ r ∧ m ≤ 1 - r := by
    intro r hr
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hr
    constructor <;> linarith [hr.1, hr.2]
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hb : ∀ x, m ≤ x → |1 / (2 * Real.sqrt x)| ≤ 1 / (2 * Real.sqrt m) := by
    intro x hx
    have hx' : Real.sqrt m ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
    rw [abs_of_nonneg (by positivity)]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hmain := hasDerivAt_integral_log_partition_cavity_path (μ := μ) (P := P)
    (D := D0) (X := Xf) (Xs := Xs) (Eb := Eb) (B := B) R (fun _ _ => rfl)
    hD0m hXfm hXsm hB0 hD0b hXfb hXsb
    (Z := Z) hZ hZm hZ0
    (s := Sum.elim (fun _ r => β * Real.sqrt r) (fun _ r => β * Real.sqrt (1 - r)))
    (s' := Sum.elim (fun _ r => β * (1 / (2 * Real.sqrt r)))
      (fun _ r => β * (-(1 / (2 * Real.sqrt (1 - r))))))
    (c := fun _ b => -(β ^ 2 / 2) * b) (c' := fun _ _ => -(β ^ 2 / 2)) (t := t) (δ := m)
    (C := |β| * (1 / (2 * Real.sqrt m)) + β ^ 2 / 2) hm
    (by
      rintro (u | u) r hr
      · exact (Real.hasDerivAt_sqrt (ne_of_gt (lt_of_lt_of_le hm (hball r hr).1))).const_mul β
      · have h1r : 1 - r ≠ 0 := ne_of_gt (lt_of_lt_of_le hm (hball r hr).2)
        have := ((Real.hasDerivAt_sqrt h1r).comp r ((hasDerivAt_id r).const_sub 1)).const_mul β
        refine this.congr_deriv ?_
        simp only [Sum.elim_inr]
        ring)
    (fun _ r _ => (hasDerivAt_id r).const_mul _ |>.congr_deriv (by ring))
    (by
      rintro (u | u) r hr
      · simp only [Sum.elim_inl, abs_mul]
        have := hb r (hball r hr).1
        have := abs_nonneg β
        nlinarith [sq_nonneg β]
      · simp only [Sum.elim_inr, abs_mul, abs_neg]
        have := hb (1 - r) (hball r hr).2
        have := abs_nonneg β
        nlinarith [sq_nonneg β])
    (fun _ r _ => by
      rw [abs_neg, abs_of_nonneg (by positivity)]
      have := abs_nonneg β
      have : 0 ≤ |β| * (1 / (2 * Real.sqrt m)) := by positivity
      linarith)
    (by
      rintro (u | u)
      · exact Or.inr (mul_ne_zero hβ (Real.sqrt_pos.2 ht0).ne')
      · exact Or.inr (mul_ne_zero hβ (Real.sqrt_pos.2 (sub_pos.2 ht1)).ne'))
  have hexpo : ∀ (ω : Ω) (a : α) (r' : ℝ), D0 a + ∑ l : (D ⊕ D) ⊕ Unit,
      Sum.elim (fun k => Sum.elim (fun _ r => β * Real.sqrt r) (fun _ r => β * Real.sqrt (1 - r))
        k r' * Z k ω) (fun _ => -(β ^ 2 / 2) * r') l * Sum.elim Xf Xs l a =
      skVectorFieldExponent ξ β ρ (fun u v => r' * q₁ u v + (1 - r') * q₀ u v)
        (fun u => β * (Real.sqrt r' * Z (.inl u) ω + Real.sqrt (1 - r') * Z (.inr u) ω)) a := by
    intro ω a r'
    have e1 : ∑ u, β * Real.sqrt r' * Z (.inl u) ω * ξ a u +
        ∑ u, β * Real.sqrt (1 - r') * Z (.inr u) ω * ξ a u =
        ∑ u, β * (Real.sqrt r' * Z (.inl u) ω + Real.sqrt (1 - r') * Z (.inr u) ω) * ξ a u := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun u _ => by ring
    have e2 : ∑ w, ∑ w', ξ a w * ξ a w' * (ρ w w' - (r' * q₁ w w' + (1 - r') * q₀ w w')) =
        ∑ w, ∑ w', ξ a w * ξ a w' * (ρ w w' - q₀ w w') +
          (-r') * ∑ w, ∑ w', (q₁ w w' - q₀ w w') * (ξ a w * ξ a w') := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => by ring
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hXf, hXs, hD0,
      skVectorFieldExponent, Finset.univ_unique, Finset.sum_singleton]
    rw [e2, ← e1]
    ring
  have hfun : (fun s => ∫ ω, Real.log (∫ a, Real.exp (skVectorFieldExponent ξ β ρ
        (fun u v => s * q₁ u v + (1 - s) * q₀ u v)
        (fun u => β * (Real.sqrt s * Z (.inl u) ω + Real.sqrt (1 - s) * Z (.inr u) ω)) a) ∂μ) ∂P) =
      fun r' => ∫ ω, Real.log (∫ a, Real.exp (D0 a + ∑ l : (D ⊕ D) ⊕ Unit,
        Sum.elim (fun k => Sum.elim (fun _ r => β * Real.sqrt r)
          (fun _ r => β * Real.sqrt (1 - r)) k r' * Z k ω) (fun _ => -(β ^ 2 / 2) * r') l *
          Sum.elim Xf Xs l a) ∂μ) ∂P := by
    funext r'
    simp only [hexpo]
  rw [hfun]
  refine hmain.congr_deriv ?_
  obtain ⟨zt, hzt⟩ : ∃ zt : Ω → (D ⊕ D) ⊕ Unit → ℝ, ∀ ω, zt ω = Sum.elim (fun k =>
      Sum.elim (fun _ r => β * Real.sqrt r) (fun _ r => β * Real.sqrt (1 - r)) k t * Z k ω)
      (fun _ => -(β ^ 2 / 2) * t) := ⟨_, fun _ => rfl⟩
  simp only [← hzt]
  have hztm : Measurable zt := by
    refine measurable_pi_iff.2 fun l => ?_
    rcases l with (k | k) | j
    · simpa [hzt] using (hZm (.inl k)).const_mul (β * Real.sqrt t)
    · simpa [hzt] using (hZm (.inr k)).const_mul (β * Real.sqrt (1 - t))
    · simp [hzt]
  have hXall : ∀ l, Measurable (Sum.elim Xf Xs l) := by
    rintro (k | j)
    · exact hXfm k
    · exact hXsm j
  have hXallb : ∀ l a, |Sum.elim Xf Xs l a| ≤ B := by
    rintro (k | j) a
    · exact hXfb k a
    · exact hXsb j a
  have hRcont : ∀ (Y : α → ℝ) (M : ℝ), 0 ≤ M → Measurable Y → (∀ a, |Y a| ≤ M) →
      Continuous (R Y) := fun Y M hM hY hYb =>
    continuous_gibbs_ratio_linear (μ := μ) (K := (D ⊕ D) ⊕ Unit) (X := Sum.elim Xf Xs)
      (D := D0) (Eb := Eb) R (fun _ _ => rfl) hD0m hXall hY hB0 hM hD0b hXallb hYb
  have hRb : ∀ (Y : α → ℝ) (M : ℝ), (∀ a, |Y a| ≤ M) → ∀ z, |R Y z| ≤ M := fun Y M hYb z =>
    abs_gibbs_ratio_le (μ := μ) (K := (D ⊕ D) ⊕ Unit) (X := Sum.elim Xf Xs) (D := D0)
      (Eb := Eb) hD0m hXall hD0b hXallb hYb z
  have hRz : ∀ (Y : α → ℝ) ω, R Y (zt ω) =
      ∫ a, Y a ∂(μ.tilted (skVectorFieldExponent ξ β ρ
        (fun u v => t * q₁ u v + (1 - t) * q₀ u v)
        (fun u => β * (Real.sqrt t * Z (.inl u) ω + Real.sqrt (1 - t) * Z (.inr u) ω)))) := by
    intro Y ω
    simp only [hRdef, hzt, hexpo]
    rw [integral_tilted, ← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [smul_eq_mul]
    ring
  have hi1 : ∀ u v, Integrable (fun ω => R (fun a => ξ a u * ξ a v) (zt ω)) P := fun u v =>
    (integrable_const r).mono'
      ((hRcont _ r hr (hξm2 u v) (hξξ · u v)).measurable.comp hztm).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hRb _ r (hξξ · u v) _)
  have hi2 : ∀ u v, Integrable (fun ω => R (fun a => ξ a u) (zt ω) *
      R (fun a => ξ a v) (zt ω)) P := fun u v => by
    refine (integrable_const (Real.sqrt r * Real.sqrt r)).mono'
      ((((hRcont (fun a => ξ a u) (Real.sqrt r) (Real.sqrt_nonneg _) (hξ u)
        (hξb · u)).measurable.comp hztm).mul ((hRcont (fun a => ξ a v) (Real.sqrt r)
        (Real.sqrt_nonneg _) (hξ v) (hξb · v)).measurable.comp hztm))).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hRb _ _ (hξb · u) _) (hRb _ _ (hξb · v) _) (abs_nonneg _)
      (Real.sqrt_nonneg _)
  have hlin : ∀ ω, R (Xs ()) (zt ω) = ∑ w, ∑ w', (q₁ w w' - q₀ w w') *
      R (fun a => ξ a w * ξ a w') (zt ω) := by
    intro ω
    simp only [hRdef]
    have hexpI := integrable_exp_linear (μ := μ) (K := (D ⊕ D) ⊕ Unit) (X := Sum.elim Xf Xs)
      (D := D0) (Eb := Eb) hD0m hXall hD0b hXallb (zt ω)
    exact gibbs_ratio_sum_sum ξ (fun w w' => q₁ w w' - q₀ w w') _ fun w w' =>
      hexpI.bdd_mul (hξm2 w w').aestronglyMeasurable (c := r)
        (ae_of_all _ fun a => by simpa [Real.norm_eq_abs] using hξξ a w w')
  have h01 : ∀ u v, ∫ ω, Z (.inr u) ω * Z (.inl v) ω ∂P = 0 := fun u v => by
    rw [← h10 v u]
    exact integral_congr_ae (ae_of_all _ fun ω => mul_comm _ _)
  have hcov : ∀ u v, ∫ ω, (R (fun a => ξ a u * ξ a v) (zt ω) -
      R (fun a => ξ a u) (zt ω) * R (fun a => ξ a v) (zt ω)) ∂P =
      (∫ ω, R (fun a => ξ a u * ξ a v) (zt ω) ∂P) -
        ∫ ω, R (fun a => ξ a u) (zt ω) * R (fun a => ξ a v) (zt ω) ∂P := fun u v =>
    integral_sub (hi1 u v) (hi2 u v)
  have hsumA : ∫ ω, R (Xs ()) (zt ω) ∂P = ∑ w, ∑ w', (q₁ w w' - q₀ w w') *
      ∫ ω, R (fun a => ξ a w * ξ a w') (zt ω) ∂P := by
    simp_rw [hlin]
    rw [integral_finsetSum Finset.univ fun w _ => integrable_finsetSum Finset.univ
      fun w' _ => (hi1 w w').const_mul (q₁ w w' - q₀ w w')]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [integral_finsetSum Finset.univ fun w' _ => (hi1 w w').const_mul (q₁ w w' - q₀ w w')]
    exact Finset.sum_congr rfl fun w' _ => integral_const_mul _ _
  have hs0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht0).ne'
  have hs1 : Real.sqrt (1 - t) ≠ 0 := (Real.sqrt_pos.2 (sub_pos.2 ht1)).ne'
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, h11, h00, h10, h01, hXf,
    Finset.univ_unique, Finset.sum_singleton, mul_zero, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add, hcov, hsumA]
  have c1 : β * (1 / (2 * Real.sqrt t)) * (β * Real.sqrt t) = β ^ 2 / 2 := by
    field_simp
  have c2 : β * -(1 / (2 * Real.sqrt (1 - t))) * (β * Real.sqrt (1 - t)) = -(β ^ 2 / 2) := by
    field_simp
  simp only [c1, c2, hRz]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  ring

/-- **Lemma 1.12.6 for `ρ`.**  The derivative in the matrix direction `E` of the replica-symmetric
functional `-(β²/4) ∑ᵤᵥ (ρᵤᵥ² - qᵤᵥ²) + 𝔼 log ∫ ℰ dμ` is `(β²/2) ∑ᵤᵥ Eᵤᵥ (𝔼⟨ξᵤ ξᵥ⟩ - ρᵤᵥ)`;
it vanishes in every direction exactly when `ρᵤᵥ = 𝔼⟨ξᵤ ξᵥ⟩`, which is Eq. (1.373). -/
theorem hasDerivAt_skVectorPressure_rho (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → D → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u)) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r) (ρ q E : D → D → ℝ)
    {P : Measure Ω} [IsProbabilityMeasure P] {X : D → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω u => X u ω) P) (hXm : ∀ u, Measurable (X u))
    (hX0 : ∀ u, ∫ ω, X u ω ∂P = 0) (β s₀ : ℝ) :
    HasDerivAt (fun s => -(β ^ 2 / 4) * ∑ u, ∑ v, ((ρ u v + s * E u v) ^ 2 - q u v ^ 2) +
        skVectorGaussianFreeEnergy μ ξ (fun u v => ρ u v + s * E u v) q P X β)
      (β ^ 2 / 2 * ∑ u, ∑ v, E u v * ((∫ ω, ∫ a, ξ a u * ξ a v ∂(μ.tilted
        (fun a => β * ∑ w, X w ω * ξ a w +
          β ^ 2 / 2 * ∑ w, ∑ w', ξ a w * ξ a w' * (ρ w w' + s₀ * E w w' - q w w'))) ∂P) -
        (ρ u v + s₀ * E u v))) s₀ := by
  have hpoly : HasDerivAt (fun s => -(β ^ 2 / 4) * ∑ u, ∑ v, ((ρ u v + s * E u v) ^ 2 - q u v ^ 2))
      (-(β ^ 2 / 4) * ∑ u, ∑ v, (2 * (ρ u v + s₀ * E u v) * E u v)) s₀ := by
    refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun u _ => HasDerivAt.fun_sum fun v _ => ?_)
    have h := ((hasDerivAt_id s₀).mul_const (E u v)).const_add (ρ u v)
    simpa using (h.pow 2).sub_const (q u v ^ 2)
  refine (hpoly.add (hasDerivAt_skVectorGaussianFreeEnergy_rho μ ξ hξ hr hbound ρ q E hX hXm hX0 β
    s₀)).congr_deriv ?_
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, mul_sub]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring

/-- **Lemma 1.12.6 for `q`.**  Along the segment `q(s) = s q₁ + (1 - s) q₀` the derivative of the
replica-symmetric functional at `0 < t < 1` is
`(β²/2) ∑ᵤᵥ (q₁ - q₀)ᵤᵥ (q(t)ᵤᵥ - 𝔼 ⟨ξᵤ⟩⟨ξᵥ⟩)`; it vanishes when `q(t)` satisfies Eq. (1.372). -/
theorem hasDerivAt_skVectorPressure_segment (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → D → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u)) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r) (ρ q₀ q₁ : D → D → ℝ)
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : D ⊕ D → Ω → ℝ}
    (hZ : HasGaussianLaw (fun ω l => Z l ω) P) (hZm : ∀ l, Measurable (Z l))
    (hZ0 : ∀ l, ∫ ω, Z l ω ∂P = 0)
    (h11 : ∀ u v, ∫ ω, Z (.inl u) ω * Z (.inl v) ω ∂P = q₁ u v)
    (h00 : ∀ u v, ∫ ω, Z (.inr u) ω * Z (.inr v) ω ∂P = q₀ u v)
    (h10 : ∀ u v, ∫ ω, Z (.inl u) ω * Z (.inr v) ω ∂P = 0)
    {β : ℝ} (hβ : β ≠ 0) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun s => -(β ^ 2 / 4) * ∑ u, ∑ v,
        (ρ u v ^ 2 - (s * q₁ u v + (1 - s) * q₀ u v) ^ 2) +
        ∫ ω, Real.log (∫ a, Real.exp (skVectorFieldExponent ξ β ρ
          (fun u v => s * q₁ u v + (1 - s) * q₀ u v)
          (fun u => β * (Real.sqrt s * Z (.inl u) ω +
            Real.sqrt (1 - s) * Z (.inr u) ω)) a) ∂μ) ∂P)
      (β ^ 2 / 2 * ∑ u, ∑ v, (q₁ u v - q₀ u v) *
        ((t * q₁ u v + (1 - t) * q₀ u v) - ∫ ω,
          (∫ a, ξ a u ∂(μ.tilted (skVectorFieldExponent ξ β ρ
            (fun u v => t * q₁ u v + (1 - t) * q₀ u v)
            (fun u => β * (Real.sqrt t * Z (.inl u) ω +
              Real.sqrt (1 - t) * Z (.inr u) ω))))) *
          (∫ a, ξ a v ∂(μ.tilted (skVectorFieldExponent ξ β ρ
            (fun u v => t * q₁ u v + (1 - t) * q₀ u v)
            (fun u => β * (Real.sqrt t * Z (.inl u) ω +
              Real.sqrt (1 - t) * Z (.inr u) ω))))) ∂P)) t := by
  have hpoly : HasDerivAt (fun s => -(β ^ 2 / 4) * ∑ u, ∑ v,
        (ρ u v ^ 2 - (s * q₁ u v + (1 - s) * q₀ u v) ^ 2))
      (-(β ^ 2 / 4) * ∑ u, ∑ v, (-(2 * (t * q₁ u v + (1 - t) * q₀ u v) *
        (q₁ u v - q₀ u v)))) t := by
    refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun u _ => HasDerivAt.fun_sum fun v _ => ?_)
    have h : HasDerivAt (fun s => s * q₁ u v + (1 - s) * q₀ u v) (q₁ u v - q₀ u v) t := by
      have := ((hasDerivAt_id t).mul_const (q₁ u v)).add
        ((((hasDerivAt_id t).const_sub 1)).mul_const (q₀ u v))
      refine this.congr_deriv ?_
      ring
    have := (h.pow 2).const_sub (ρ u v ^ 2)
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat]
    ring
  refine (hpoly.add (hasDerivAt_skVectorSegment μ ξ hξ hr hbound ρ q₀ q₁ hZ hZm hZ0 h11 h00 h10
    hβ ht0 ht1)).congr_deriv ?_
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, mul_sub]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring

/-- Eq. (1.372) makes the functional stationary along every admissible segment through `q`. -/
theorem hasDerivAt_skVectorPressure_segment_eq_zero (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → D → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u)) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r) (ρ q₀ q₁ : D → D → ℝ)
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : D ⊕ D → Ω → ℝ}
    (hZ : HasGaussianLaw (fun ω l => Z l ω) P) (hZm : ∀ l, Measurable (Z l))
    (hZ0 : ∀ l, ∫ ω, Z l ω ∂P = 0)
    (h11 : ∀ u v, ∫ ω, Z (.inl u) ω * Z (.inl v) ω ∂P = q₁ u v)
    (h00 : ∀ u v, ∫ ω, Z (.inr u) ω * Z (.inr v) ω ∂P = q₀ u v)
    (h10 : ∀ u v, ∫ ω, Z (.inl u) ω * Z (.inr v) ω ∂P = 0)
    {β : ℝ} (hβ : β ≠ 0) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (h372 : ∀ u v, t * q₁ u v + (1 - t) * q₀ u v = ∫ ω,
          (∫ a, ξ a u ∂(μ.tilted (skVectorFieldExponent ξ β ρ
            (fun u v => t * q₁ u v + (1 - t) * q₀ u v)
            (fun u => β * (Real.sqrt t * Z (.inl u) ω +
              Real.sqrt (1 - t) * Z (.inr u) ω))))) *
          (∫ a, ξ a v ∂(μ.tilted (skVectorFieldExponent ξ β ρ
            (fun u v => t * q₁ u v + (1 - t) * q₀ u v)
            (fun u => β * (Real.sqrt t * Z (.inl u) ω +
              Real.sqrt (1 - t) * Z (.inr u) ω))))) ∂P) :
    HasDerivAt (fun s => -(β ^ 2 / 4) * ∑ u, ∑ v,
        (ρ u v ^ 2 - (s * q₁ u v + (1 - s) * q₀ u v) ^ 2) +
        ∫ ω, Real.log (∫ a, Real.exp (skVectorFieldExponent ξ β ρ
          (fun u v => s * q₁ u v + (1 - s) * q₀ u v)
          (fun u => β * (Real.sqrt s * Z (.inl u) ω +
            Real.sqrt (1 - s) * Z (.inr u) ω)) a) ∂μ) ∂P) 0 t := by
  have hd := hasDerivAt_skVectorPressure_segment μ ξ hξ hr hbound ρ q₀ q₁ hZ hZm hZ0 h11 h00 h10
    hβ ht0 ht1
  have hzero : β ^ 2 / 2 * ∑ u, ∑ v, (q₁ u v - q₀ u v) *
        ((t * q₁ u v + (1 - t) * q₀ u v) - ∫ ω,
          (∫ a, ξ a u ∂(μ.tilted (skVectorFieldExponent ξ β ρ
            (fun u v => t * q₁ u v + (1 - t) * q₀ u v)
            (fun u => β * (Real.sqrt t * Z (.inl u) ω +
              Real.sqrt (1 - t) * Z (.inr u) ω))))) *
          (∫ a, ξ a v ∂(μ.tilted (skVectorFieldExponent ξ β ρ
            (fun u v => t * q₁ u v + (1 - t) * q₀ u v)
            (fun u => β * (Real.sqrt t * Z (.inl u) ω +
              Real.sqrt (1 - t) * Z (.inr u) ω))))) ∂P) = 0 := by
    have hsub : ∀ u v, ((t * q₁ u v + (1 - t) * q₀ u v) - ∫ ω,
          (∫ a, ξ a u ∂(μ.tilted (skVectorFieldExponent ξ β ρ
            (fun u v => t * q₁ u v + (1 - t) * q₀ u v)
            (fun u => β * (Real.sqrt t * Z (.inl u) ω +
              Real.sqrt (1 - t) * Z (.inr u) ω))))) *
          (∫ a, ξ a v ∂(μ.tilted (skVectorFieldExponent ξ β ρ
            (fun u v => t * q₁ u v + (1 - t) * q₀ u v)
            (fun u => β * (Real.sqrt t * Z (.inl u) ω +
              Real.sqrt (1 - t) * Z (.inr u) ω))))) ∂P) = 0 :=
      fun u v => by rw [h372 u v, sub_self]
    simp only [hsub, mul_zero, Finset.sum_const_zero]
  exact hd.congr_deriv (by rw [hzero])

end SpinGlasses
