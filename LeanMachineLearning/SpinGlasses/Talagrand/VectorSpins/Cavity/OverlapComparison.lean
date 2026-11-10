/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Cavity.Comparison
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Cavity.Bounds

/-!
# The smart-path step of Theorem 1.12.1

For a bounded function `F` of two replicas the mean value theorem on the cavity path gives
`ν_1(F) ≤ ν_0(F) + |ν_c'(F)|` for some `c ∈ (0, 1)` (this holds for functions of either sign), and
Eq. (1.378) together with the comparison `ν_t ≤ e^{20 β² d²} ν_1` for nonnegative functions bounds
the derivative by the square roots of the squared overlap errors at `t = 1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

variable {α : Type*} [MeasurableSpace α]

/-- The real-number bookkeeping of the smart-path step: square roots of the comparison
bounds. -/
theorem sqrt_mul_add_le_of_le_mul {β D E a wc xbc xac w1 xb1 xa1 : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E)
    (ha : a ≤ 4 * D ^ 2 * wc) (hw : wc ≤ E * w1) (hxb : xbc ≤ E * xb1) (hxa : xac ≤ E * xa1) :
    8 * β ^ 2 * D * Real.sqrt a * (Real.sqrt xbc + Real.sqrt xac) ≤
      16 * β ^ 2 * D ^ 2 * E * Real.sqrt w1 * (Real.sqrt xb1 + Real.sqrt xa1) := by
  have hsE : Real.sqrt E * Real.sqrt E = E := Real.mul_self_sqrt hE
  have h1 : Real.sqrt a ≤ 2 * D * Real.sqrt E * Real.sqrt w1 := by
    calc Real.sqrt a ≤ Real.sqrt (4 * D ^ 2 * (E * w1)) :=
          Real.sqrt_le_sqrt (ha.trans (mul_le_mul_of_nonneg_left hw (by positivity)))
      _ = 2 * D * Real.sqrt E * Real.sqrt w1 := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hE,
            show (4 : ℝ) * D ^ 2 = (2 * D) ^ 2 by ring, Real.sqrt_sq (by positivity)]
          ring
  have h2 : Real.sqrt xbc ≤ Real.sqrt E * Real.sqrt xb1 := by
    rw [← Real.sqrt_mul hE]; exact Real.sqrt_le_sqrt hxb
  have h3 : Real.sqrt xac ≤ Real.sqrt E * Real.sqrt xa1 := by
    rw [← Real.sqrt_mul hE]; exact Real.sqrt_le_sqrt hxa
  have hnn : 0 ≤ Real.sqrt xbc + Real.sqrt xac := by positivity
  calc 8 * β ^ 2 * D * Real.sqrt a * (Real.sqrt xbc + Real.sqrt xac) ≤
        8 * β ^ 2 * D * (2 * D * Real.sqrt E * Real.sqrt w1) *
          (Real.sqrt E * Real.sqrt xb1 + Real.sqrt E * Real.sqrt xa1) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) (add_le_add h2 h3) hnn
          (by positivity)
    _ = 16 * β ^ 2 * D ^ 2 * (Real.sqrt E * Real.sqrt E) * Real.sqrt w1 *
          (Real.sqrt xb1 + Real.sqrt xa1) := by ring
    _ = _ := by rw [hsE]

/-- The squared overlap error `∑ᵤᵥ (R⁻ᵢⱼᵘᵛ - Qᵤᵥ)²` of two replicas is measurable, nonnegative
and at most `4 d²` when `‖Q‖_F ≤ d`. -/
theorem measurable_nonneg_bounded_sq_overlap_sub {d N : ℕ} (ξ : α → Fin d → ℝ) (hξ : ∀ u,
  Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (i j : Fin 2) (Q : Fin d → Fin d → ℝ)
    (hQ : ∑ u, ∑ v, Q u v ^ 2 ≤ (d : ℝ) ^ 2) :
    Measurable (fun τ : Fin 2 → Fin (N + 1) → α => ∑ u, ∑ v,
        (skVectorCavityOverlap ξ N (τ i) (τ j) u v - Q u v) ^ 2) ∧
      (∀ τ : Fin 2 → Fin (N + 1) → α, 0 ≤ ∑ u, ∑ v,
        (skVectorCavityOverlap ξ N (τ i) (τ j) u v - Q u v) ^ 2) ∧
      (∀ τ : Fin 2 → Fin (N + 1) → α, |∑ u, ∑ v,
        (skVectorCavityOverlap ξ N (τ i) (τ j) u v - Q u v) ^ 2| ≤ 4 * (d : ℝ) ^ 2) := by
  have hpair : Measurable fun τ : Fin 2 → Fin (N + 1) → α => (τ i, τ j) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have hm : ∀ u v, Measurable fun τ : Fin 2 → Fin (N + 1) → α =>
      skVectorCavityOverlap ξ N (τ i) (τ j) u v - Q u v := fun u v =>
    (((measurable_skVectorCavityOverlap hξ N u v).comp hpair :
      Measurable fun τ : Fin 2 → Fin (N + 1) → α =>
        skVectorCavityOverlap ξ N (τ i) (τ j) u v)).sub measurable_const
  refine ⟨Finset.measurable_sum _ fun u _ => Finset.measurable_sum _ fun v _ =>
    (hm u v).pow_const 2,
    fun τ => Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => sq_nonneg _,
    fun τ => ?_⟩
  rw [abs_of_nonneg (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => sq_nonneg _)]
  exact sum_sq_overlap_error_le ξ hbound Q hQ (τ i) (τ j)

/-- **Comparison of `ν_t` with `ν_1` for two replicas**: `ν_t(F) ≤ e^{20 β² d²} ν_1(F)` for
`0 ≤ t ≤ 1` and a nonnegative bounded `F`. -/
theorem skVectorCavityAverage_two_le_exp_mul_endpoint {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    (ρ q : Fin d → Fin d → ℝ) (hq : ∀ u v, q u v = q v u)
    (hq2 : ∑ u, ∑ v, q u v ^ 2 ≤ (d : ℝ) ^ 2) (hρ2 : ∑ u, ∑ v, ρ u v ^ 2 ≤ (d : ℝ) ^ 2)
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : Fin d → Ω → ℝ}
    (hn : SKVectorCavityGaussianData P N d β q g g' Y)
    (F : (Fin 2 → Fin (N + 1) → α) → ℝ) (hF : Measurable F) {M : ℝ} (hM : 0 ≤ M)
    (hFb : ∀ σ, |F σ| ≤ M) (hF0 : ∀ σ, 0 ≤ F σ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ : Option (Option (Fin 2)) →
        Fin (N + 1) → α => F fun c => σ (some (some c))) ≤
      Real.exp (20 * β ^ 2 * (d : ℝ) ^ 2) *
        skVectorCavityAverage μ ξ N β ρ q P g g' Y 1 (fun σ : Option (Option (Fin 2)) →
          Fin (N + 1) → α => F fun c => σ (some (some c))) := by
  refine (skVectorCavityAverage_le_exp_mul_endpoint μ ξ hξ hbound β ρ q hq hq2 hρ2 F hF hM hFb hF0
    hn ht0
    ht1).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ ?_
  · refine Real.exp_le_exp.2 ?_
    simp only [Fintype.card_fin, Nat.cast_ofNat]
    have : 0 ≤ β ^ 2 * (d : ℝ) ^ 2 := by positivity
    nlinarith [mul_nonneg this ht0]
  · unfold skVectorCavityAverage
    exact integral_nonneg fun _ => integral_nonneg fun σ => hF0 _

/-- If `F² ≤ 4 d² W` pointwise, then `ν_t(F²) ≤ 4 d² ν_t(W)`. -/
theorem skVectorCavityAverage_sq_le {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    (ρ q : Fin d → Fin d → ℝ) {P : Measure Ω} [IsProbabilityMeasure P]
    {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : Fin d → Ω → ℝ}
    (hgm : ∀ p, Measurable (g p)) (hg'm : ∀ i, Measurable (g' i)) (hYm : ∀ u, Measurable (Y u))
    (F W : (Fin 2 → Fin (N + 1) → α) → ℝ) (hW : Measurable W) {MW : ℝ}
    (hWb : ∀ σ, |W σ| ≤ MW) (hW0 : ∀ σ, 0 ≤ W σ)
    (hFW : ∀ σ, F σ ^ 2 ≤ 4 * (d : ℝ) ^ 2 * W σ) (t : ℝ) :
    skVectorCavityAverage μ ξ N β ρ q P g g' Y t (fun σ : Option (Option (Fin 2)) →
        Fin (N + 1) → α => (F fun c => σ (some (some c))) ^ 2) ≤
      4 * (d : ℝ) ^ 2 * skVectorCavityAverage μ ξ N β ρ q P g g' Y t
        (fun σ : Option (Option (Fin 2)) → Fin (N + 1) → α => W fun c => σ (some (some c))) := by
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hrep : Measurable fun (σ : Option (Option (Fin 2)) → Fin (N + 1) → α) (c' : Fin 2) =>
      σ (some (some c')) := measurable_pi_iff.2 fun c' => measurable_pi_apply (some (some c'))
  have hHm : Measurable fun σ : Option (Option (Fin 2)) → Fin (N + 1) → α =>
      4 * (d : ℝ) ^ 2 * W fun c' => σ (some (some c')) := measurable_const.mul (hW.comp hrep)
  have h := abs_skVectorCavityAverage_le (R := Fin 2) (P := P) μ ξ hξ hr hbound N β ρ q hgm hg'm
    hYm t
    (fun σ => (F fun c' => σ (some (some c'))) ^ 2)
    (fun σ => 4 * (d : ℝ) ^ 2 * W fun c' => σ (some (some c'))) hHm
    ⟨4 * (d : ℝ) ^ 2 * MW, fun σ => by
      rw [abs_of_nonneg (mul_nonneg (by positivity) (hW0 _))]
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hWb _)) (by positivity)⟩
    (fun σ => by rw [abs_of_nonneg (sq_nonneg _)]; exact hFW _)
  rw [skVectorCavityAverage_const_mul μ ξ N β ρ q t] at h
  exact (le_abs_self _).trans h

/-- **The smart-path step.**  Let `F` be a bounded function of two replicas whose square is at most
`4 d² W` for a nonnegative bounded `W`.  Then
`ν_1(F) ≤ ν_0(F) + 16 β² d² e^{20 β² d²} ν_1(W)^{1/2} (ν_1(X_B)^{1/2} + ν_1(X_A)^{1/2})`, where
`X_A = ∑ᵤᵥ (R⁻_{1,2}ᵘᵛ - qᵤᵥ)²` and `X_B = ∑ᵤᵥ (R⁻_{1,1}ᵘᵛ - ρᵤᵥ)²` are the cavity-overlap
errors. -/
theorem skVectorCavityAverage_one_le_zero_add_deriv {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    (ρ q : Fin d → Fin d → ℝ) (hq : ∀ u v, q u v = q v u)
    (hq2 : ∑ u, ∑ v, q u v ^ 2 ≤ (d : ℝ) ^ 2) (hρ2 : ∑ u, ∑ v, ρ u v ^ 2 ≤ (d : ℝ) ^ 2)
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : Fin d → Ω → ℝ}
    (hn : SKVectorCavityGaussianData P N d β q g g' Y)
    (F W : (Fin 2 → Fin (N + 1) → α) → ℝ) (hF : Measurable F) (hW : Measurable W)
    {MF MW : ℝ} (hMF : 0 ≤ MF) (hMW : 0 ≤ MW) (hFb : ∀ σ, |F σ| ≤ MF) (hWb : ∀ σ, |W σ| ≤ MW)
    (hW0 : ∀ σ, 0 ≤ W σ) (hFW : ∀ σ, F σ ^ 2 ≤ 4 * (d : ℝ) ^ 2 * W σ) :
    skVectorCavityAverage μ ξ N β ρ q P g g' Y 1 (fun σ : Option (Option (Fin 2)) → Fin (N + 1) →
      α =>
        F fun c => σ (some (some c))) ≤
      skVectorCavityAverage μ ξ N β ρ q P g g' Y 0 (fun σ : Option (Option (Fin 2)) →
        Fin (N + 1) → α => F fun c => σ (some (some c))) +
      16 * β ^ 2 * (d : ℝ) ^ 2 * Real.exp (20 * β ^ 2 * (d : ℝ) ^ 2) *
        Real.sqrt (skVectorCavityAverage μ ξ N β ρ q P g g' Y 1 (fun σ : Option (Option (Fin 2)) →
          Fin (N + 1) → α => W fun c => σ (some (some c)))) *
        (Real.sqrt (skVectorCavityAverage μ ξ N β ρ q P g g' Y 1 (fun σ => ∑ u, ∑ v,
            (skVectorCavityOverlap ξ N (σ (some (some (0 : Fin 2)))) (σ (some (some (0 : Fin 2))))
              u v - ρ u v) ^ 2)) +
          Real.sqrt (skVectorCavityAverage μ ξ N β ρ q P g g' Y 1 (fun σ => ∑ u, ∑ v,
            (skVectorCavityOverlap ξ N (σ (some (some (0 : Fin 2)))) (σ (some (some (1 : Fin 2))))
              u v - q u v) ^ 2))) := by
  classical
  set φ : ℝ → ℝ := fun s => ∫ ω, ∫ σ : Fin 2 → Fin (N + 1) → α, F σ ∂(Measure.pi fun _ : Fin 2 =>
      (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
        (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) s)) ∂P with hφ
  have hold : ∀ F' : (Fin 2 → Fin (N + 1) → α) → ℝ, Measurable F' → ∀ s,
      skVectorCavityAverage μ ξ N β ρ q P g g' Y s (fun σ : Option (Option (Fin 2)) →
        Fin (N + 1) → α => F' fun c => σ (some (some c))) =
      ∫ ω, ∫ σ : Fin 2 → Fin (N + 1) → α, F' σ ∂(Measure.pi fun _ : Fin 2 =>
        (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
          (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) s)) ∂P :=
    fun F' hF' s => skVectorCavityAverage_old μ ξ hξ hbound β ρ q F' hF' s
  have hcont : Continuous φ := continuous_skVectorCavityAverage μ ξ hξ hbound β ρ q F hF hMF hFb hn
  have hdiffOn : DifferentiableOn ℝ φ (Set.Ioo 0 1) := fun s hs =>
    (hasDerivAt_skVectorCavityAverage μ ξ hξ (Nat.cast_nonneg d) hbound N β ρ q hq F hF hMF hFb
      hn.hasGaussianLaw hn.measurable_old_coupling hn.measurable_new_coupling hn.measurable_field
        hn.integral_coupling_mul_coupling hn.integral_field_mul_field
        hn.integral_coupling_mul_field hn.integral_old_coupling
      hn.integral_new_coupling hn.integral_field hs.1 hs.2).differentiableAt.differentiableWithinAt
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope φ zero_lt_one hcont.continuousOn hdiffOn
  rw [hold F hF 1, hold F hF 0]
  have h1 : φ 1 ≤ φ 0 + |deriv φ c| := by
    have e : φ 1 - φ 0 = deriv φ c := by rw [hcd]; ring
    linarith [le_abs_self (deriv φ c)]
  refine h1.trans ?_
  have h378 := abs_deriv_skVectorCavityAverage_le_sqrt μ ξ hξ hbound β ρ q hq hq2 hρ2 F hF hMF hFb
    hn.hasGaussianLaw hn.measurable_old_coupling hn.measurable_new_coupling hn.measurable_field
      hn.integral_coupling_mul_coupling hn.integral_field_mul_field hn.integral_coupling_mul_field
      hn.integral_old_coupling
    hn.integral_new_coupling hn.integral_field hc.1 hc.2
  refine add_le_add le_rfl (h378.trans ?_)
  have hgm := hn.measurable_old_coupling
  have hg'm := hn.measurable_new_coupling
  have hYm := hn.measurable_field
  obtain ⟨hXBm, hXB0, hXBb⟩ := measurable_nonneg_bounded_sq_overlap_sub (N := N) ξ hξ hbound 0 0 ρ
    hρ2
  obtain ⟨hXAm, hXA0, hXAb⟩ := measurable_nonneg_bounded_sq_overlap_sub (N := N) ξ hξ hbound 0 1 q
    hq2
  have hcmp := fun F' (hF' : Measurable F') (M : ℝ) (hM : 0 ≤ M) (hb : ∀ σ, |F' σ| ≤ M)
      (h0 : ∀ σ, 0 ≤ F' σ) => skVectorCavityAverage_two_le_exp_mul_endpoint μ ξ hξ hbound β ρ q hq
        hq2 hρ2 hn F'
      hF' hM hb h0 hc.1.le hc.2.le
  exact sqrt_mul_add_le_of_le_mul (β := β) (D := d) (by positivity) (Real.exp_pos _).le
    (skVectorCavityAverage_sq_le μ ξ hξ hbound β ρ q hgm hg'm hYm F W hW hWb hW0 hFW c)
    (hcmp W hW MW hMW hWb hW0)
    (hcmp _ hXBm (4 * (d : ℝ) ^ 2) (by positivity) hXBb hXB0)
    (hcmp _ hXAm (4 * (d : ℝ) ^ 2) (by positivity) hXAb hXA0)

end SpinGlasses
