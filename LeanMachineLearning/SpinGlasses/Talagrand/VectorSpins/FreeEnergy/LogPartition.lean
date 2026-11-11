/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsLogPartitionCavity
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Model.Energy

/-!
# The replica-symmetric free energy for vector spins (Talagrand Eqs. (1.371), (1.387), (1.393))

For a probability spin law `μ` with bounded measurable coordinates `ξ`, matrices `ρ`, `q` and a
centered Gaussian vector `X` of covariance `q`, put `Y = βX` and
`ℰ(x) = exp(∑ᵤ xᵤ Yᵤ + (β²/2) ∑ᵤᵥ xᵤ xᵥ (ρᵤᵥ - qᵤᵥ))`.  The functional `𝔼 log ∫ ℰ dμ` is the
random part of the limiting pressure of Theorem 1.12.3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

variable {α D Ω : Type*} [MeasurableSpace α] [Fintype D] [MeasurableSpace Ω]

/-- **The random part of the replica-symmetric free energy**, `𝔼 log ∫ ℰ(x) dμ(x)` with
`ℰ(x) = exp(β ∑ᵤ xᵤ Xᵤ + (β²/2) ∑ᵤᵥ xᵤ xᵥ (ρᵤᵥ - qᵤᵥ))`, Eq. (1.371) with `Y = β X`. -/
noncomputable def skVectorGaussianFreeEnergy (μ : Measure α) (ξ : α → D → ℝ) (ρ q : D → D → ℝ)
    (P : Measure Ω) (X : D → Ω → ℝ) (β : ℝ) : ℝ :=
  ∫ ω, Real.log (∫ a, Real.exp (β * ∑ u, X u ω * ξ a u +
    β ^ 2 / 2 * ∑ u, ∑ v, ξ a u * ξ a v * (ρ u v - q u v)) ∂μ) ∂P


/-- **Equation (1.393).**  If `(q, ρ)` satisfy the replica-symmetric equations (1.372)--(1.373) at
the inverse temperature `β ≠ 0`, then the partial derivative in `β` of `𝔼 log ∫ ℰ dμ`, with `q` and
`ρ` held fixed, is `β ∑ᵤᵥ (ρᵤᵥ² - qᵤᵥ²)`. -/
theorem hasDerivAt_skVectorGaussianFreeEnergy (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → D → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u)) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r) (ρ q : D → D → ℝ)
    {P : Measure Ω} [IsProbabilityMeasure P] {X : D → Ω → ℝ}
    (hX : HasGaussianLaw (fun ω u => X u ω) P) (hXm : ∀ u, Measurable (X u))
    (hX0 : ∀ u, ∫ ω, X u ω ∂P = 0) (hXcov : ∀ u v, ∫ ω, X u ω * X v ω ∂P = q u v)
    {β : ℝ} (hβ : β ≠ 0)
    (hρ : ∀ u v, ρ u v = ∫ ω, ∫ a, ξ a u * ξ a v ∂(μ.tilted (skVectorFieldExponent ξ β ρ q
        (fun w => β * X w ω))) ∂P)
    (hq : ∀ u v, q u v = ∫ ω, (∫ a, ξ a u ∂(μ.tilted (skVectorFieldExponent ξ β ρ q
        (fun w => β * X w ω)))) *
      (∫ a, ξ a v ∂(μ.tilted (skVectorFieldExponent ξ β ρ q
        (fun w => β * X w ω)))) ∂P) :
    HasDerivAt (skVectorGaussianFreeEnergy μ ξ ρ q P X) (β * ∑ u, ∑ v, (ρ u v ^ 2 - q u v ^ 2)) β
      := by
  classical
  set Xs : Unit → α → ℝ := fun _ a => ∑ w, ∑ w', ξ a w * ξ a w' * (ρ w w' - q w w') with hXs
  set Xf : D → α → ℝ := fun u a => ξ a u with hXf
  have hξb : ∀ a u, |ξ a u| ≤ Real.sqrt r := abs_spin_le ξ hbound
  have hξξ : ∀ a u v, |ξ a u * ξ a v| ≤ r := fun a u v =>
    abs_spin_mul_le ξ hr hbound a a u v
  set B : ℝ := Real.sqrt r + ∑ w, ∑ w', r * |ρ w w' - q w w'| with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hXfm : ∀ u, Measurable (Xf u) := hξ
  have hXfb : ∀ u a, |Xf u a| ≤ B := fun u a => by
    have : 0 ≤ ∑ w, ∑ w', r * |ρ w w' - q w w'| := by positivity
    linarith [hξb a u]
  have hXsm : ∀ j, Measurable (Xs j) := fun j =>
    Finset.measurable_sum _ fun w _ => Finset.measurable_sum _ fun w' _ =>
      (measurable_spin_mul ξ hξ w w').mul measurable_const
  have hXsb : ∀ j a, |Xs j a| ≤ B := fun j a => by
    have h1 : |∑ w, ∑ w', ξ a w * ξ a w' * (ρ w w' - q w w')| ≤
        ∑ w, ∑ w', r * |ρ w w' - q w w'| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w' _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hξξ a w w') (abs_nonneg _)
    have := Real.sqrt_nonneg r
    simp only [hXs]
    linarith
  set R : (α → ℝ) → (D ⊕ Unit → ℝ) → ℝ := fun Y z =>
    (∫ a, Y a * Real.exp ((fun _ => (0 : ℝ)) a + ∑ k, z k * Sum.elim Xf Xs k a) ∂μ) /
      ∫ a, Real.exp ((fun _ => (0 : ℝ)) a + ∑ k, z k * Sum.elim Xf Xs k a) ∂μ with hRdef
  have hmain := hasDerivAt_integral_log_partition_cavity_path (μ := μ) (P := P)
    (D := fun _ => (0 : ℝ)) (X := Xf) (Xs := Xs) (Eb := 0) (B := B) R (fun _ _ => rfl)
    measurable_const hXfm hXsm hB0 (fun _ => by simp) hXfb hXsb
    (Z := X) hX hXm hX0 (s := fun _ b => b) (s' := fun _ _ => (1 : ℝ))
    (c := fun _ b => b ^ 2 / 2) (c' := fun _ b => b) (t := β) (δ := 1) (C := |β| + 1) one_pos
    (fun _ r _ => hasDerivAt_id r)
    (fun _ r _ => by
      simpa using ((hasDerivAt_pow 2 r).div_const 2))
    (fun _ r _ => by simp [abs_nonneg])
    (fun _ r hr => by
      rw [Metric.mem_ball, Real.dist_eq] at hr
      have := abs_sub_abs_le_abs_sub r β
      linarith)
    (fun _ => Or.inr hβ)
  have hexpo : ∀ (ω : Ω) (a : α) (r' : ℝ), (fun _ => (0 : ℝ)) a +
      ∑ l : D ⊕ Unit, Sum.elim (fun k => r' * X k ω) (fun _ => r' ^ 2 / 2) l *
        Sum.elim Xf Xs l a =
      r' * ∑ u, X u ω * ξ a u + r' ^ 2 / 2 * ∑ w, ∑ w', ξ a w * ξ a w' * (ρ w w' - q w w') := by
    intro ω a r'
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hXf, hXs, Finset.univ_unique,
      Finset.sum_singleton, zero_add, Finset.mul_sum]
    ring_nf
  have hfun : skVectorGaussianFreeEnergy μ ξ ρ q P X = fun r' => ∫ ω, Real.log (∫ a, Real.exp
      ((fun _ => (0 : ℝ)) a + ∑ l : D ⊕ Unit, Sum.elim (fun k => r' * X k ω)
        (fun _ => r' ^ 2 / 2) l * Sum.elim Xf Xs l a) ∂μ) ∂P := by
    funext r'
    unfold skVectorGaussianFreeEnergy
    simp only [hexpo]
  rw [hfun]
  refine hmain.congr_deriv ?_
  set zt : Ω → D ⊕ Unit → ℝ := fun ω => Sum.elim (fun k => β * X k ω) fun _ => β ^ 2 / 2 with hzt
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
      (D := fun _ => (0 : ℝ)) (Eb := 0) R (fun _ _ => rfl) measurable_const hXall hY hB0 hM
      (fun _ => by simp) hXallb hYb
  have hRb : ∀ (Y : α → ℝ) (M : ℝ), (∀ a, |Y a| ≤ M) → ∀ z, |R Y z| ≤ M := fun Y M hYb z =>
    abs_gibbs_ratio_le (μ := μ) (K := D ⊕ Unit) (X := Sum.elim Xf Xs) (D := fun _ => (0 : ℝ))
      (Eb := 0) measurable_const hXall (fun _ => by simp) hXallb hYb z
  have hRint : ∀ (Y : α → ℝ) (M : ℝ), 0 ≤ M → Measurable Y → (∀ a, |Y a| ≤ M) →
      Integrable (fun ω => R Y (zt ω)) P := fun Y M hM hY hYb =>
    (integrable_const M).mono' ((hRcont Y M hM hY hYb).measurable.comp hztm).aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hRb Y M hYb _)
  have hRz : ∀ (Y : α → ℝ) ω, R Y (zt ω) =
      ∫ a, Y a ∂(μ.tilted (skVectorFieldExponent ξ β ρ q (fun w => β * X w ω))) := by
    intro Y ω
    rw [integral_tilted_eq_div]
    simp only [hRdef, hzt, hexpo, skVectorFieldExponent_mul_left]
  have hξm2 : ∀ u v, Measurable fun a => ξ a u * ξ a v := measurable_spin_mul ξ hξ
  have hI1 : ∀ u v, ∫ ω, R (fun a => ξ a u * ξ a v) (zt ω) ∂P = ρ u v := fun u v => by
    rw [hρ u v]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    dsimp only
    rw [hRz]
  have hI2 : ∀ u v, ∫ ω, R (Xf u) (zt ω) * R (Xf v) (zt ω) ∂P = q u v := fun u v => by
    rw [hq u v]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    dsimp only [hXf]
    rw [hRz, hRz]
  have hi1 : ∀ u v, Integrable (fun ω => R (fun a => ξ a u * ξ a v) (zt ω)) P := fun u v =>
    hRint _ r hr (hξm2 u v) (hξξ · u v)
  have hi2 : ∀ u v, Integrable (fun ω => R (Xf u) (zt ω) * R (Xf v) (zt ω)) P := fun u v => by
    refine (integrable_const (Real.sqrt r * Real.sqrt r)).mono'
      ((((hRcont (Xf u) (Real.sqrt r) (Real.sqrt_nonneg _) (hξ u) (hξb · u)).measurable.comp
        hztm).mul ((hRcont (Xf v) (Real.sqrt r) (Real.sqrt_nonneg _) (hξ v)
        (hξb · v)).measurable.comp hztm))).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hRb (Xf u) _ (hξb · u) _) (hRb (Xf v) _ (hξb · v) _) (abs_nonneg _)
      (Real.sqrt_nonneg _)
  have hRlin : ∀ z, R (Xs ()) z = ∑ w, ∑ w', (ρ w w' - q w w') * R (fun a => ξ a w * ξ a w') z := by
    intro z
    simp only [hRdef]
    have hexpI := integrable_exp_linear (μ := μ) (K := D ⊕ Unit) (X := Sum.elim Xf Xs)
      (D := fun _ => (0 : ℝ)) (Eb := 0) measurable_const hXall (fun _ => by simp) hXallb z
    have hint : ∀ w w', Integrable (fun a => ξ a w * ξ a w' * Real.exp ((fun _ => (0 : ℝ)) a +
        ∑ k, z k * Sum.elim Xf Xs k a)) μ := fun w w' =>
      hexpI.bdd_mul (hξm2 w w').aestronglyMeasurable (c := r) (ae_of_all _ fun a => by
        simpa [Real.norm_eq_abs] using hξξ a w w')
    have hpt : ∀ a, Xs () a * Real.exp ((fun _ => (0 : ℝ)) a +
        ∑ k, z k * Sum.elim Xf Xs k a) = ∑ w, ∑ w', (ρ w w' - q w w') *
        (ξ a w * ξ a w' * Real.exp ((fun _ => (0 : ℝ)) a + ∑ k, z k * Sum.elim Xf Xs k a)) := by
      intro a
      simp only [hXs, Finset.sum_mul]
      exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun w' _ => by ring
    rw [integral_congr_ae (ae_of_all _ hpt),
      integral_finsetSum _ fun w _ => integrable_finsetSum _ fun w' _ => (hint w w').const_mul _,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [integral_finsetSum _ fun w' _ => (hint w w').const_mul _, Finset.sum_div]
    exact Finset.sum_congr rfl fun w' _ => by rw [integral_const_mul]; ring
  have hI3 : ∫ ω, R (Xs ()) (zt ω) ∂P = ∑ w, ∑ w', (ρ w w' - q w w') * ρ w w' := by
    simp_rw [hRlin]
    rw [integral_finsetSum _ fun w _ => integrable_finsetSum _ fun w' _ => (hi1 w w').const_mul _]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [integral_finsetSum _ fun w' _ => (hi1 w w').const_mul _]
    exact Finset.sum_congr rfl fun w' _ => by rw [integral_const_mul, hI1]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  have e1 : ∀ k l, ∫ ω, (R (fun a => Xf k a * Xf l a) (zt ω) -
      R (Xf k) (zt ω) * R (Xf l) (zt ω)) ∂P = ρ k l - q k l := fun k l => by
    rw [integral_sub (hi1 k l) (hi2 k l), hI1, hI2]
  simp only [hzt] at hI3 e1
  simp only [e1, hI3, hXcov, one_mul]
  rw [Finset.mul_sum]
  simp only [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end SpinGlasses
