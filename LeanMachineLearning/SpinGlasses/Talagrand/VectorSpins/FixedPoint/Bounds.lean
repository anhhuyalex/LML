/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IntegrableOfBound
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Cavity.Bounds
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Model.Energy
public import Mathlib.Analysis.Convex.Integral

/-!
# Frobenius bounds for the replica-symmetric equations (end of the proof of Corollary 1.12.5)

If `q` and `ρ` satisfy the fixed-point equations (1.372)--(1.373) for spins with
`∑ᵤ ξᵤ² ≤ r`, then `‖q‖_F² ≤ r²` and `‖ρ‖_F² ≤ r²`.  These are the two hypotheses that
`abs_deriv_skVectorCavityAverage_le` and `abs_deriv_skVectorCavityAverage_le_sqrt` need.
-/

@[expose] public section

open MeasureTheory Finset
open scoped BigOperators
namespace SpinGlasses

variable {α Ω ι : Type*} [MeasurableSpace α] [MeasurableSpace Ω]

section Gibbs

variable {μ : Measure α} [IsProbabilityMeasure μ]

/-- The Gibbs measure and Jensen's inequality: for bounded measurable observables `hᵢ`,
`∑ᵢ (∫ hᵢ d(μ.tilted e))² ≤ ∫ ∑ᵢ hᵢ² d(μ.tilted e)`. -/
theorem sum_sq_integral_tilted_le [Fintype ι] {e : α → ℝ}
    (he : Integrable (fun a => Real.exp (e a)) μ) (h : ι → α → ℝ) (hm : ∀ i, Measurable (h i))
    {M : ℝ} (hb : ∀ i a, |h i a| ≤ M) :
    ∑ i, (∫ a, h i a ∂(μ.tilted e)) ^ 2 ≤ ∫ a, ∑ i, h i a ^ 2 ∂(μ.tilted e) := by
  have := isProbabilityMeasure_tilted he
  exact sum_sq_integral_le h hm hb

omit [IsProbabilityMeasure μ] in
/-- The integral against the tilted probability measure written as a quotient of integrals. -/
theorem integral_tilted_eq_div (e Y : α → ℝ) :
    ∫ a, Y a ∂(μ.tilted e) = (∫ a, Y a * Real.exp (e a) ∂μ) / ∫ a, Real.exp (e a) ∂μ := by
  rw [integral_tilted, ← integral_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [smul_eq_mul]
  ring

/-- The tilted integral of a measurable observable is measurable in a jointly measurable random
log-density. -/
theorem measurable_integral_tilted {e : Ω → α → ℝ} (hE : Measurable fun p : Ω × α => e p.1 p.2)
    {Y : α → ℝ} (hY : Measurable Y) : Measurable fun ω => ∫ a, Y a ∂(μ.tilted (e ω)) := by
  simp_rw [integral_tilted_eq_div]
  have h1 : Measurable fun p : Ω × α => Y p.2 * Real.exp (e p.1 p.2) :=
    (hY.comp measurable_snd).mul (Real.measurable_exp.comp hE)
  have h2 : Measurable fun p : Ω × α => Real.exp (e p.1 p.2) := Real.measurable_exp.comp hE
  exact (h1.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable.div
    (h2.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

/-- A tilted integral of an observable bounded by `M` is bounded by `M`. -/
theorem abs_integral_tilted_le {e Y : α → ℝ} (he : Integrable (fun a => Real.exp (e a)) μ) {M : ℝ}
    (hY : ∀ a, |Y a| ≤ M) : |∫ a, Y a ∂(μ.tilted e)| ≤ M := by
  have := isProbabilityMeasure_tilted he
  rw [← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := μ.tilted e) (f := Y) (C := M)
    (Filter.Eventually.of_forall fun a => by simpa [Real.norm_eq_abs] using hY a)
  simpa using this

end Gibbs

/-- **The Frobenius bounds of Eq. (1.382) for the fixed point.**  If `q` and `ρ` satisfy the
replica-symmetric equations (1.372)--(1.373) for a random log-density `e ω` and spins with
`∑ᵤ ξᵤ² ≤ r`, then `∑ᵤᵥ qᵤᵥ² ≤ r²` and `∑ᵤᵥ ρᵤᵥ² ≤ r²`. -/
theorem sum_sq_skVectorFixedPoint_le {D : Type*} [Fintype D] (μ : Measure α) [IsProbabilityMeasure
  μ]
    (ξ : α → D → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u)) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r) (q ρ : D → D → ℝ)
    {P : Measure Ω} [IsProbabilityMeasure P] {e : Ω → α → ℝ}
    (hE : ∀ ω, Integrable (fun a => Real.exp (e ω a)) μ)
    (hEm : Measurable fun p : Ω × α => e p.1 p.2)
    (hρ : ∀ u v, ρ u v = ∫ ω, ∫ a, ξ a u * ξ a v ∂(μ.tilted (e ω)) ∂P)
    (hq : ∀ u v, q u v = ∫ ω, (∫ a, ξ a u ∂(μ.tilted (e ω))) *
      (∫ a, ξ a v ∂(μ.tilted (e ω))) ∂P) :
    (∑ u, ∑ v, q u v ^ 2 ≤ r ^ 2) ∧ (∑ u, ∑ v, ρ u v ^ 2 ≤ r ^ 2) := by
  have hξb : ∀ a u, |ξ a u| ≤ Real.sqrt r := abs_spin_le ξ hbound
  have hξξ : ∀ a u v, |ξ a u * ξ a v| ≤ r := fun a u v =>
    abs_spin_mul_le ξ hr hbound a a u v
  have hξm2 : ∀ u v, Measurable fun a => ξ a u * ξ a v := fun u v => (hξ u).mul (hξ v)
  -- pointwise (in `ω`) Jensen bounds for the Gibbs measure
  have hG : ∀ ω, ∑ u, (∫ a, ξ a u ∂(μ.tilted (e ω))) ^ 2 ≤ r := fun ω => by
    refine (sum_sq_integral_tilted_le (hE ω) (fun u a => ξ a u) hξ (M := Real.sqrt r)
      fun u a => hξb a u).trans ?_
    have := isProbabilityMeasure_tilted (hE ω)
    calc ∫ a, ∑ u, ξ a u ^ 2 ∂(μ.tilted (e ω)) ≤ ∫ _a, r ∂(μ.tilted (e ω)) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun a =>
            Finset.sum_nonneg fun u _ => sq_nonneg _) (integrable_const r)
            (Filter.Eventually.of_forall hbound)
      _ = r := by simp
  have hH : ∀ ω, ∑ uv : D × D, (∫ a, ξ a uv.1 * ξ a uv.2 ∂(μ.tilted (e ω))) ^ 2 ≤
      r ^ 2 := fun ω => by
    refine (sum_sq_integral_tilted_le (ι := D × D) (hE ω)
      (fun (uv : D × D) a => ξ a uv.1 * ξ a uv.2)
      (fun uv => hξm2 uv.1 uv.2) (M := r) fun uv a => hξξ a uv.1 uv.2).trans ?_
    have := isProbabilityMeasure_tilted (hE ω)
    calc ∫ a, ∑ uv : D × D, (ξ a uv.1 * ξ a uv.2) ^ 2 ∂(μ.tilted (e ω))
        ≤ ∫ _a, r ^ 2 ∂(μ.tilted (e ω)) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun a =>
            Finset.sum_nonneg fun uv _ => sq_nonneg _) (integrable_const _)
            (Filter.Eventually.of_forall fun a => ?_)
          beta_reduce
          rw [Fintype.sum_prod_type]
          calc ∑ u, ∑ v, (ξ a u * ξ a v) ^ 2 = (∑ u, ξ a u ^ 2) * ∑ v, ξ a v ^ 2 := by
                rw [Finset.sum_mul_sum]
                exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
            _ ≤ r * r := mul_le_mul (hbound a) (hbound a)
                (Finset.sum_nonneg fun _ _ => sq_nonneg _) hr
            _ = r ^ 2 := by ring
      _ = r ^ 2 := by simp
  set g : D → Ω → ℝ := fun u ω => ∫ a, ξ a u ∂(μ.tilted (e ω)) with hg
  have hgm : ∀ u, Measurable (g u) := fun u => measurable_integral_tilted hEm (hξ u)
  have hgb : ∀ u ω, |g u ω| ≤ Real.sqrt r := fun u ω =>
    abs_integral_tilted_le (hE ω) (fun a => hξb a u)
  set H : D × D → Ω → ℝ := fun uv ω => ∫ a, ξ a uv.1 * ξ a uv.2 ∂(μ.tilted (e ω))
    with hHdef
  have hHm : ∀ uv, Measurable (H uv) := fun uv => measurable_integral_tilted hEm (hξm2 uv.1 uv.2)
  have hHb : ∀ uv ω, |H uv ω| ≤ r := fun uv ω =>
    abs_integral_tilted_le (hE ω) (fun a => hξξ a uv.1 uv.2)
  constructor
  · have h1 := sum_sq_integral_le (ι := D × D) (P := P) (fun uv ω => g uv.1 ω * g uv.2 ω)
      (fun uv => (hgm uv.1).mul (hgm uv.2)) (M := r) fun uv ω => by
        rw [abs_mul]
        calc |g uv.1 ω| * |g uv.2 ω| ≤ Real.sqrt r * Real.sqrt r :=
              mul_le_mul (hgb _ ω) (hgb _ ω) (abs_nonneg _) (Real.sqrt_nonneg _)
          _ = r := Real.mul_self_sqrt hr
    refine le_trans (le_of_eq ?_) (h1.trans ?_)
    · rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hq u v]
    · have hpt : ∀ ω, ∑ uv : D × D, (g uv.1 ω * g uv.2 ω) ^ 2 ≤ r ^ 2 := fun ω => by
        rw [Fintype.sum_prod_type]
        calc ∑ u, ∑ v, (g u ω * g v ω) ^ 2 = (∑ u, g u ω ^ 2) * ∑ v, g v ω ^ 2 := by
              rw [Finset.sum_mul_sum]
              exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
          _ ≤ r * r := mul_le_mul (hG ω) (hG ω) (Finset.sum_nonneg fun _ _ => sq_nonneg _) hr
          _ = r ^ 2 := by ring
      calc ∫ ω, ∑ uv : D × D, (g uv.1 ω * g uv.2 ω) ^ 2 ∂P ≤ ∫ _ω, r ^ 2 ∂P :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
              Finset.sum_nonneg fun uv _ => sq_nonneg _) (integrable_const _)
              (Filter.Eventually.of_forall hpt)
        _ = r ^ 2 := by simp
  · have h1 := sum_sq_integral_le (ι := D × D) (P := P) H hHm (M := r) hHb
    refine le_trans (le_of_eq ?_) (h1.trans ?_)
    · rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by rw [hρ u v]
    · calc ∫ ω, ∑ uv : D × D, H uv ω ^ 2 ∂P ≤ ∫ _ω, r ^ 2 ∂P :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω =>
              Finset.sum_nonneg fun uv _ => sq_nonneg _) (integrable_const _)
              (Filter.Eventually.of_forall hH)
        _ = r ^ 2 := by simp

omit [MeasurableSpace Ω] in
/-- The decoupled log-density has an integrable exponential and is jointly measurable. -/
theorem integrable_exp_skVectorFieldExponent {D : Type*} [Fintype D] (μ : Measure α)
    [IsProbabilityMeasure μ] (ξ : α → D → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u)) {r : ℝ}
    (hr : 0 ≤ r) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r) (β : ℝ) (ρ q : D → D → ℝ) (y : D → ℝ) :
    Integrable (fun a => Real.exp (skVectorFieldExponent ξ β ρ q y a)) μ := by
  have hξb : ∀ a u, |ξ a u| ≤ Real.sqrt r := abs_spin_le ξ hbound
  have hξξ : ∀ a u v, |ξ a u * ξ a v| ≤ r := fun a u v =>
    abs_spin_mul_le ξ hr hbound a a u v
  have hm : Measurable fun a => skVectorFieldExponent ξ β ρ q y a :=
    (Finset.measurable_sum _ fun u _ => (hξ u).const_mul _).add
      (measurable_const.mul (Finset.measurable_sum _ fun u _ => Finset.measurable_sum _
        fun v _ => ((hξ u).mul (hξ v)).mul measurable_const))
  refine (integrable_const (Real.exp (∑ u, |y u| * Real.sqrt r +
    β ^ 2 / 2 * ∑ u, ∑ v, r * |ρ u v - q u v|))).mono' hm.exp.aestronglyMeasurable
    (Filter.Eventually.of_forall fun a => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  refine Real.exp_le_exp.2 ?_
  unfold skVectorFieldExponent
  have h1 : ∑ u, y u * ξ a u ≤ ∑ u, |y u| * Real.sqrt r :=
    Finset.sum_le_sum fun u _ => (le_abs_self _).trans (by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hξb a u) (abs_nonneg _))
  have h2 : ∑ u, ∑ v, ξ a u * ξ a v * (ρ u v - q u v) ≤ ∑ u, ∑ v, r * |ρ u v - q u v| :=
    Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => (le_abs_self _).trans (by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hξξ a u v) (abs_nonneg _))
  have : 0 ≤ β ^ 2 / 2 := by positivity
  nlinarith

/-- **The fixed point satisfies the Frobenius bounds** `‖q‖_F² ≤ d²`, `‖ρ‖_F² ≤ d²` of Eq. (1.382),
for the Gaussian field `Y` of the cavity path: these are the hypotheses `hq2`, `hρ2` of
Corollary 1.12.5 (`abs_deriv_skVectorCavityAverage_le`,
  `abs_deriv_skVectorCavityAverage_le_sqrt`). -/
theorem sum_sq_skVectorFixedPoint_field_le {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ) (q ρ : Fin d → Fin d → ℝ)
    {P : Measure Ω} [IsProbabilityMeasure P] {Y : Fin d → Ω → ℝ} (hYm : ∀ u, Measurable (Y u))
    (hρ : ∀ u v, ρ u v = ∫ ω, ∫ a, ξ a u * ξ a v ∂(μ.tilted
      (skVectorFieldExponent ξ β ρ q (fun w => Y w ω))) ∂P)
    (hq : ∀ u v, q u v = ∫ ω, (∫ a, ξ a u ∂(μ.tilted
      (skVectorFieldExponent ξ β ρ q (fun w => Y w ω)))) *
      (∫ a, ξ a v ∂(μ.tilted (skVectorFieldExponent ξ β ρ q (fun w => Y w ω)))) ∂P) :
    (∑ u, ∑ v, q u v ^ 2 ≤ (d : ℝ) ^ 2) ∧ (∑ u, ∑ v, ρ u v ^ 2 ≤ (d : ℝ) ^ 2) :=
  sum_sq_skVectorFixedPoint_le μ ξ hξ (Nat.cast_nonneg d) hbound q ρ
    (e := fun ω => skVectorFieldExponent ξ β ρ q (fun w => Y w ω))
    (fun ω => integrable_exp_skVectorFieldExponent μ ξ hξ (Nat.cast_nonneg d) hbound β ρ q _)
    (by
      unfold skVectorFieldExponent
      exact (Finset.measurable_sum _ fun u _ => ((hYm u).comp measurable_fst).mul
        ((hξ u).comp measurable_snd)).add
        (measurable_const.mul (Finset.measurable_sum _ fun u _ => Finset.measurable_sum _
          fun v _ => (((hξ u).comp measurable_snd).mul ((hξ v).comp measurable_snd)).mul
            measurable_const)))
    hρ hq

end SpinGlasses
