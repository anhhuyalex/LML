/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct

/-!
# Tails and moments of a two-replica observable from an exponential moment

Let `ω ↦ ν ω` be a family of probability measures and `s ≥ 0` a function on the state space with
`𝔼 ∫ exp s ∂(ν ω) ≤ exp (L n)`, where `n ≥ 1`. If a nonnegative observable `D` of the replicas
satisfies `D σ ≤ c (s (σ a) / n + s (σ b) / n) / 2 + Q`, then it exceeds `c (L + 5) + Q` with
quenched probability at most `exp (-4 n)`, and its fourth and eighth quenched moments are bounded
uniformly in `n`. This is the argument for Eqs. (3.97), (3.98) and (3.104) of Talagrand,
*Spin Glasses*, Vol. I.

## Main statements

* `MeasureTheory.integral_integral_pi_tail_and_pow_le_of_exp_moment`: for a general observable.
* `MeasureTheory.integral_integral_pi_overlap_tail_and_pow_le_of_exp_moment`: for the centred
  overlap of two replicas in an inner product space.
-/

@[expose] public section

open scoped Real RealInnerProductSpace

namespace MeasureTheory

/-- Tail and fourth and eighth moment bounds for a replica observable `D` dominated by
`c (s (σ a) / n + s (σ b) / n) / 2 + Q`, from the exponential moment
`𝔼 ∫ exp s ∂(ν ω) ≤ exp (L n)`. -/
theorem integral_integral_pi_tail_and_pow_le_of_exp_moment {Ω α R : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [Fintype R] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure α) [∀ ω, IsProbabilityMeasure (ν ω)]
    (hν : ∀ Y : (R → α) → ℝ, Measurable Y →
      Measurable fun ω => ∫ σ, Y σ ∂(Measure.pi fun _ : R => ν ω))
    {s : α → ℝ} (hs0 : ∀ x, 0 ≤ s x) (hsi : ∀ ω, Integrable (fun x => Real.exp (s x)) (ν ω))
    (hEi : Integrable (fun ω => ∫ x, Real.exp (s x) ∂(ν ω)) P)
    {L n : ℝ} (hL : 0 ≤ L) (hn : 1 ≤ n)
    (hE : ∫ ω, ∫ x, Real.exp (s x) ∂(ν ω) ∂P ≤ Real.exp (L * n))
    (a b : R) {D : (R → α) → ℝ} (hDm : Measurable D) (hD0 : ∀ σ, 0 ≤ D σ) {c Q : ℝ}
    (hc : 0 < c) (hQ : 0 ≤ Q) (hD : ∀ σ, D σ ≤ c * ((s (σ a) / n + s (σ b) / n) / 2) + Q) :
    (∀ K : ℝ, c * (L + 5) + Q < K →
      Integrable (fun ω => ∫ σ, {τ | K ≤ D τ}.indicator (fun _ => (1 : ℝ)) σ
          ∂(Measure.pi fun _ : R => ν ω)) P ∧
        ∫ ω, ∫ σ, {τ | K ≤ D τ}.indicator (fun _ => (1 : ℝ)) σ
          ∂(Measure.pi fun _ : R => ν ω) ∂P ≤ Real.exp (-4 * n)) ∧
      (Integrable (fun ω => ∫ σ, D σ ^ 4 ∂(Measure.pi fun _ : R => ν ω)) P ∧
        ∫ ω, ∫ σ, D σ ^ 4 ∂(Measure.pi fun _ : R => ν ω) ∂P ≤
          1 + 2 ^ 7 * (2 ^ 7 * c ^ 8 * (8 ^ 8 + L ^ 8) + Q ^ 8)) ∧
      Integrable (fun ω => ∫ σ, D σ ^ 8 ∂(Measure.pi fun _ : R => ν ω)) P ∧
        ∫ ω, ∫ σ, D σ ^ 8 ∂(Measure.pi fun _ : R => ν ω) ∂P ≤
          2 ^ 7 * (2 ^ 7 * c ^ 8 * (8 ^ 8 + L ^ 8) + Q ^ 8) := by
  have hn0 : 0 < n := one_pos.trans_le hn
  -- every bound reduces to the average of `exp (s (σ a)) + exp (s (σ b))`
  have hbound : ∀ Y : (R → α) → ℝ, Measurable Y → (∀ σ, 0 ≤ Y σ) → ∀ A B : ℝ, 0 ≤ B →
      (∀ σ, Y σ ≤ A + B * (Real.exp (s (σ a)) + Real.exp (s (σ b)))) →
      Integrable (fun ω => ∫ σ, Y σ ∂(Measure.pi fun _ : R => ν ω)) P ∧
        ∫ ω, ∫ σ, Y σ ∂(Measure.pi fun _ : R => ν ω) ∂P ≤
          A + 2 * B * Real.exp (L * n) := by
    intro Y hY hY0 A B hB hle
    have hin : ∀ ω, ∫ σ, Y σ ∂(Measure.pi fun _ : R => ν ω) ≤
        A + 2 * B * ∫ x, Real.exp (s x) ∂(ν ω) := fun ω => by
      have hmp := fun i : R => measurePreserving_eval (fun _ : R => ν ω) i
      have hi := fun i : R => (hmp i).integrable_comp_of_integrable (hsi ω)
      have he := fun i : R => integral_pi_eval (ν ω) i (fun x => Real.exp (s x))
        (hsi ω).aestronglyMeasurable
      have hsum : Integrable (fun σ : R → α => Real.exp (s (σ a)) + Real.exp (s (σ b)))
          (Measure.pi fun _ : R => ν ω) := (hi a).add (hi b)
      have hdom : Integrable
          (fun σ : R → α => A + B * (Real.exp (s (σ a)) + Real.exp (s (σ b))))
          (Measure.pi fun _ : R => ν ω) := (integrable_const A).add (hsum.const_mul B)
      have hYi : Integrable Y (Measure.pi fun _ : R => ν ω) :=
        hdom.mono' hY.aestronglyMeasurable (ae_of_all _ fun σ => by
          rw [Real.norm_of_nonneg (hY0 σ)]; exact hle σ)
      refine (integral_mono hYi hdom hle).trans_eq ?_
      have hia : Integrable (fun σ : R → α => Real.exp (s (σ a)))
          (Measure.pi fun _ : R => ν ω) := hi a
      have hib : Integrable (fun σ : R → α => Real.exp (s (σ b)))
          (Measure.pi fun _ : R => ν ω) := hi b
      rw [integral_add (integrable_const A) (hsum.const_mul B), integral_const, probReal_univ,
        one_smul, integral_const_mul, integral_add hia hib, he a, he b]
      ring
    have hmaj : Integrable (fun ω => A + 2 * B * ∫ x, Real.exp (s x) ∂(ν ω)) P :=
      (integrable_const A).add (hEi.const_mul (2 * B))
    have hYw : Integrable (fun ω => ∫ σ, Y σ ∂(Measure.pi fun _ : R => ν ω)) P :=
      hmaj.mono' (hν Y hY).aestronglyMeasurable (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (integral_nonneg hY0)]; exact hin ω)
    refine ⟨hYw, (integral_mono hYw hmaj hin).trans ?_⟩
    rw [integral_add (integrable_const A) (hEi.const_mul _), integral_const, probReal_univ,
      one_smul, integral_const_mul]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hE (by positivity))
  -- the eighth power of `x / n` is dominated by an exponential
  have hpow8 : ∀ x : ℝ, 0 ≤ x →
      (x / n) ^ 8 ≤ 2 ^ 7 * (L ^ 8 + 8 ^ 8 * Real.exp (-(L * n)) * Real.exp x) := by
    intro x hx
    have hexp8 : ∀ y : ℝ, 0 ≤ y → y ^ 8 ≤ 8 ^ 8 * Real.exp y := fun y hy => by
      have h1 : (y / 8) ^ 8 ≤ Real.exp (y / 8) ^ 8 :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (y / 8)]) 8
      rw [← Real.exp_nat_mul, show ((8 : ℕ) : ℝ) * (y / 8) = y by push_cast; ring, div_pow,
        div_le_iff₀' (by positivity)] at h1
      exact h1
    set m : ℝ := max (x - L * n) 0 with hm
    have hm8 : m ^ 8 ≤ 8 ^ 8 * (Real.exp (-(L * n)) * Real.exp x) := by
      rw [← Real.exp_add, neg_add_eq_sub]
      rcases le_total (x - L * n) 0 with h0 | h0
      · rw [hm, max_eq_right h0, zero_pow (by norm_num)]; positivity
      · rw [hm, max_eq_left h0]; exact hexp8 _ h0
    have hxm : x ≤ L * n + m := by linarith [le_max_left (x - L * n) 0]
    have h1 : x ^ 8 ≤ 2 ^ 7 * ((L * n) ^ 8 + m ^ 8) :=
      (pow_le_pow_left₀ hx hxm 8).trans
        (add_pow_le (mul_nonneg hL hn0.le) (le_max_right _ _) 8)
    rw [div_pow, div_le_iff₀ (by positivity)]
    refine h1.trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [add_mul, ← mul_pow]
    refine add_le_add le_rfl (hm8.trans ?_)
    rw [← mul_assoc]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hn)
  set A8 : ℝ := 2 ^ 7 * (2 ^ 7 * c ^ 8 * L ^ 8 + Q ^ 8) with hA8
  set B8 : ℝ := 2 ^ 13 * c ^ 8 * 8 ^ 8 * Real.exp (-(L * n)) with hB8
  have hB80 : 0 ≤ B8 := by positivity
  have hD8 : ∀ σ, D σ ^ 8 ≤ A8 + B8 * (Real.exp (s (σ a)) + Real.exp (s (σ b))) := by
    intro σ
    set xa : ℝ := s (σ a) / n with hxa
    set xb : ℝ := s (σ b) / n with hxb
    have hxa0 : 0 ≤ xa := div_nonneg (hs0 _) hn0.le
    have hxb0 : 0 ≤ xb := div_nonneg (hs0 _) hn0.le
    have h1 : D σ ^ 8 ≤ 2 ^ 7 * ((c * ((xa + xb) / 2)) ^ 8 + Q ^ 8) :=
      (pow_le_pow_left₀ (hD0 σ) (hD σ) 8).trans (add_pow_le (by positivity) hQ 8)
    have h2 : ((xa + xb) / 2) ^ 8 ≤ (xa ^ 8 + xb ^ 8) / 2 := by
      rw [div_pow, div_le_iff₀ (by positivity)]
      exact (add_pow_le hxa0 hxb0 8).trans_eq (by ring)
    have h3 : (c * ((xa + xb) / 2)) ^ 8 ≤ 2 ^ 7 * c ^ 8 * L ^ 8 +
        2 ^ 6 * c ^ 8 * 8 ^ 8 * Real.exp (-(L * n)) *
          (Real.exp (s (σ a)) + Real.exp (s (σ b))) := by
      rw [mul_pow]
      refine (mul_le_mul_of_nonneg_left (h2.trans (div_le_div_of_nonneg_right
        (add_le_add (hpow8 _ (hs0 (σ a))) (hpow8 _ (hs0 (σ b)))) zero_le_two))
        (by positivity)).trans_eq ?_
      ring
    refine h1.trans ((mul_le_mul_of_nonneg_left (add_le_add h3 le_rfl)
      (by positivity)).trans_eq ?_)
    rw [hA8, hB8]
    ring
  have hnum8 : A8 + 2 * B8 * Real.exp (L * n) =
      2 ^ 7 * (2 ^ 7 * c ^ 8 * (8 ^ 8 + L ^ 8) + Q ^ 8) := by
    have hexp : Real.exp (-(L * n)) * Real.exp (L * n) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    rw [hA8, hB8]
    linear_combination (2 ^ 14 * c ^ 8 * 8 ^ 8) * hexp
  have h8 := hbound (fun σ => D σ ^ 8) (hDm.pow_const 8) (fun σ => pow_nonneg (hD0 σ) 8) A8 B8
    hB80 hD8
  have h4 := hbound (fun σ => D σ ^ 4) (hDm.pow_const 4) (fun σ => pow_nonneg (hD0 σ) 4)
    (1 + A8) B8 hB80 fun σ => by
      have h : D σ ^ 4 ≤ 1 + D σ ^ 8 := by
        nlinarith [sq_nonneg (D σ ^ 4 - 1), pow_nonneg (hD0 σ) 8]
      linarith [hD8 σ]
  refine ⟨fun K hK => ?_, ⟨h4.1, h4.2.trans_eq (by rw [add_assoc, hnum8])⟩, h8.1,
    h8.2.trans_eq hnum8⟩
  have htail_pt : ∀ σ : R → α, {τ | K ≤ D τ}.indicator (fun _ => (1 : ℝ)) σ ≤
      0 + Real.exp (-((L + 5) * n)) * (Real.exp (s (σ a)) + Real.exp (s (σ b))) := by
    intro σ
    rw [zero_add]
    by_cases hσ : σ ∈ {τ | K ≤ D τ}
    · rw [Set.indicator_of_mem hσ]
      have hmax : (L + 5) * n ≤ s (σ a) ∨ (L + 5) * n ≤ s (σ b) := by
        have h1 : c * (L + 5) ≤ c * ((s (σ a) / n + s (σ b) / n) / 2) := by
          have h0 : K ≤ D σ := hσ
          linarith [hD σ]
        have h2 := le_of_mul_le_mul_left h1 hc
        rw [← add_div, div_div, le_div_iff₀ (by positivity)] at h2
        by_contra hcon
        push Not at hcon
        nlinarith
      have hexp_ab : Real.exp ((L + 5) * n) ≤ Real.exp (s (σ a)) + Real.exp (s (σ b)) := by
        rcases hmax with ha | hb
        · exact (Real.exp_le_exp.2 ha).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
        · exact (Real.exp_le_exp.2 hb).trans (le_add_of_nonneg_left (Real.exp_pos _).le)
      calc (1 : ℝ) = Real.exp (-((L + 5) * n)) * Real.exp ((L + 5) * n) := by
            rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp_ab (Real.exp_pos _).le
    · rw [Set.indicator_of_notMem hσ]
      positivity
  have htail := hbound _ (measurable_const.indicator (measurableSet_le measurable_const hDm))
    (fun σ => Set.indicator_nonneg (fun _ _ => zero_le_one) σ) 0 _ (Real.exp_pos _).le htail_pt
  refine ⟨htail.1, htail.2.trans ?_⟩
  have h2 : (2 : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp n]
  rw [zero_add, mul_assoc, ← Real.exp_add]
  refine (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le).trans_eq ?_
  rw [← Real.exp_add]
  congr 1
  ring

/-- The bounds of `integral_integral_pi_tail_and_pow_le_of_exp_moment` for the centred overlap
`|⟪X (σ a), X (σ b)⟫ / n - m|` of two replicas, with `|m| ≤ Q`, when `‖X x‖² ≤ c s x` and
`𝔼 ∫ exp s ∂(ν ω) ≤ exp (L n)`. A single moment bound thus serves every contraction `X`. -/
theorem integral_integral_pi_overlap_tail_and_pow_le_of_exp_moment {Ω α R F : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [Fintype R] [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure α)
    [∀ ω, IsProbabilityMeasure (ν ω)]
    (hν : ∀ Y : (R → α) → ℝ, Measurable Y →
      Measurable fun ω => ∫ σ, Y σ ∂(Measure.pi fun _ : R => ν ω))
    {X : α → F} (hX : Measurable X) {s : α → ℝ} {c : ℝ} (hc : 0 < c)
    (hXs : ∀ x, ‖X x‖ ^ 2 ≤ c * s x)
    (hsi : ∀ ω, Integrable (fun x => Real.exp (s x)) (ν ω))
    (hEi : Integrable (fun ω => ∫ x, Real.exp (s x) ∂(ν ω)) P)
    {L n : ℝ} (hL : 0 ≤ L) (hn : 1 ≤ n)
    (hE : ∫ ω, ∫ x, Real.exp (s x) ∂(ν ω) ∂P ≤ Real.exp (L * n))
    (a b : R) {m Q : ℝ} (hm : |m| ≤ Q) :
    let D : (R → α) → ℝ := fun σ => |n⁻¹ * ⟪X (σ a), X (σ b)⟫ - m|
    (∀ K : ℝ, c * (L + 5) + Q < K →
      Integrable (fun ω => ∫ σ, {τ | K ≤ D τ}.indicator (fun _ => (1 : ℝ)) σ
          ∂(Measure.pi fun _ : R => ν ω)) P ∧
        ∫ ω, ∫ σ, {τ | K ≤ D τ}.indicator (fun _ => (1 : ℝ)) σ
          ∂(Measure.pi fun _ : R => ν ω) ∂P ≤ Real.exp (-4 * n)) ∧
      (Integrable (fun ω => ∫ σ, D σ ^ 4 ∂(Measure.pi fun _ : R => ν ω)) P ∧
        ∫ ω, ∫ σ, D σ ^ 4 ∂(Measure.pi fun _ : R => ν ω) ∂P ≤
          1 + 2 ^ 7 * (2 ^ 7 * c ^ 8 * (8 ^ 8 + L ^ 8) + Q ^ 8)) ∧
      Integrable (fun ω => ∫ σ, D σ ^ 8 ∂(Measure.pi fun _ : R => ν ω)) P ∧
        ∫ ω, ∫ σ, D σ ^ 8 ∂(Measure.pi fun _ : R => ν ω) ∂P ≤
          2 ^ 7 * (2 ^ 7 * c ^ 8 * (8 ^ 8 + L ^ 8) + Q ^ 8) := by
  intro D
  have hn0 : 0 < n := one_pos.trans_le hn
  have hDm : Measurable D :=
    continuous_abs.measurable.comp
      ((((hX.comp (measurable_pi_apply a)).inner
        (hX.comp (measurable_pi_apply b))).const_mul _).sub_const _)
  refine integral_integral_pi_tail_and_pow_le_of_exp_moment P ν hν
    (fun x => nonneg_of_mul_nonneg_right ((sq_nonneg _).trans (hXs x)) hc) hsi hEi hL hn hE a b
    hDm (fun _ => abs_nonneg _) hc ((abs_nonneg m).trans hm) fun σ => ?_
  have hinner : |⟪X (σ a), X (σ b)⟫| ≤ c * ((s (σ a) + s (σ b)) / 2) := by
    nlinarith [abs_real_inner_le_norm (X (σ a)) (X (σ b)),
      sq_nonneg (‖X (σ a)‖ - ‖X (σ b)‖), hXs (σ a), hXs (σ b)]
  refine (abs_sub _ _).trans (add_le_add ?_ hm)
  rw [abs_mul, abs_of_pos (inv_pos.2 hn0)]
  refine (mul_le_mul_of_nonneg_left hinner (inv_pos.2 hn0).le).trans_eq ?_
  ring

end MeasureTheory
