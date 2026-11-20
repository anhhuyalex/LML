/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathModel

/-!
# Well-defined Gibbs averages along the perceptron smart path

Talagrand (2.15)--(2.19). The configuration contains the old spins, the last spin and the
auxiliary Gaussian vector. Its base measure is counting measure times a Gaussian probability
measure. Old and last disorder coordinates and the last field are held fixed when tilting.

Measurability and an upper bound on the potential suffice for exponential integrability,
a positive normalizer and a probability Gibbs law. A two-sided potential bound also gives
an absolute energy bound. A bounded jointly
measurable replica observable then has an integrable environment average under any finite
measure, including the Gaussian disorder law with variance-zero last field.
These statements hold for all real coefficient parameters; the book uses `[0, 1]`.
No differentiability, positive number of constraints or positive number of old spins is needed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SpinGlasses

variable {N M : ℕ}

/-- An upper bound on the potential gives an upper bound on the smart-path energy. -/
theorem perceptron_smart_path_energy_le {u : ℝ → ℝ} {D : ℝ} (hD : ∀ x, u x ≤ D) (t : ℝ)
    (ω : SmartPathDisorder N M) (x : SmartPathState N M) :
    smartPathEnergy u t ω x ≤ M * D + Real.sqrt (1 - t) * |ω.2| := by
  have hb : |((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * ω.2| =
      Real.sqrt (1 - t) * |ω.2| := by
    simp only [abs_mul, abs_units_cast_eq_one, abs_of_nonneg (Real.sqrt_nonneg _), one_mul]
  unfold smartPathEnergy
  calc
    _ ≤ Real.sqrt (1 - t) * |ω.2| + ∑ _k : Fin M, D :=
      add_le_add ((le_abs_self _).trans hb.le) (Finset.sum_le_sum fun k _ => hD _)
    _ = _ := by simp [add_comm]

/-- For a nonnegative path parameter the last-field coefficient is at most one. This bound
is uniform over the auxiliary coordinates and does not require `t ≤ 1`. -/
theorem perceptron_smart_path_energy_le_of_nonneg {u : ℝ → ℝ} {D : ℝ} (hD : ∀ x, u x ≤ D)
    (t : ℝ) (ht : 0 ≤ t) (ω : SmartPathDisorder N M) (x : SmartPathState N M) :
    smartPathEnergy u t ω x ≤ M * D + |ω.2| := by
  have hsq : Real.sqrt (1 - t) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  exact (perceptron_smart_path_energy_le hD t ω x).trans
    (add_le_add le_rfl (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hsq (abs_nonneg ω.2)))

/-- The auxiliary coordinates do not affect the bound for a bounded potential. -/
theorem abs_perceptron_smart_path_energy_le {u : ℝ → ℝ} {D : ℝ} (hD : ∀ x, |u x| ≤ D)
    (t : ℝ) (ω : SmartPathDisorder N M) (x : SmartPathState N M) :
    |smartPathEnergy u t ω x| ≤ M * D + Real.sqrt (1 - t) * |ω.2| := by
  refine abs_le.mpr ⟨?_, perceptron_smart_path_energy_le
    (fun z => le_of_abs_le (hD z)) t ω x⟩
  have hn := perceptron_smart_path_energy_le (u := fun z => -u z)
    (fun z => by linarith [neg_le_of_abs_le (hD z)]) t (ω.1, -ω.2) x
  have hfield (k : Fin M) : smartPathField t (ω.1, -ω.2) x k = smartPathField t ω x k := rfl
  have hneg : -smartPathEnergy u t ω x ≤ M * D + Real.sqrt (1 - t) * |ω.2| := by
    simpa only [smartPathEnergy, hfield, abs_neg, mul_neg, Finset.sum_neg_distrib,
      ← neg_add] using hn
  exact neg_le.mp hneg

/-- The two-sided bound for a nonnegative path parameter, with the `|y|` bound. -/
theorem abs_perceptron_smart_path_energy_le_of_nonneg {u : ℝ → ℝ} {D : ℝ}
    (hD : ∀ x, |u x| ≤ D) (t : ℝ) (ht : 0 ≤ t) (ω : SmartPathDisorder N M)
    (x : SmartPathState N M) :
    |smartPathEnergy u t ω x| ≤ M * D + |ω.2| := by
  have hsq : Real.sqrt (1 - t) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have := mul_le_mul_of_nonneg_right hsq (abs_nonneg ω.2)
  exact (abs_perceptron_smart_path_energy_le hD t ω x).trans
    (add_le_add le_rfl (by simpa only [one_mul] using this))

/-- A coordinate is bounded by the exponential of the sum of absolute coordinates. -/
theorem abs_apply_le_exp_sum_abs {ι : Type*} [Fintype ι] (x : ι → ℝ) (k : ι) :
    |x k| ≤ Real.exp (∑ i, |x i|) :=
  (Finset.single_le_sum (fun i _ => abs_nonneg (x i)) (Finset.mem_univ k)).trans
    ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))

/-- Integrability of `exp (∑ |ξ_k|)` gives integrability of each auxiliary coordinate. -/
theorem integrable_abs_snd_of_exp_sum {N M : ℕ} {μ : Measure (SmartPathState N M)}
    (hb : Integrable (fun x : SmartPathState N M => Real.exp (∑ k, |x.2 k|)) μ) (k : Fin M) :
    Integrable (fun x : SmartPathState N M => |x.2 k|) μ :=
  hb.mono' (by fun_prop) (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_abs]; exact abs_apply_le_exp_sum_abs x.2 k)

section BaseMeasure

variable {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ]

omit [NeZero μ] in
/-- The Gibbs weight is integrable for every fixed disorder and path parameter. -/
theorem integrable_exp_perceptron_smart_path_energy {u : ℝ → ℝ} (hu : Measurable u)
    {D : ℝ} (hD : ∀ x, u x ≤ D) (ω : SmartPathDisorder N M) (t : ℝ) :
    Integrable (fun x => Real.exp (smartPathEnergy u t ω x)) μ :=
  integrable_exp_of_ae_le (C := M * D + Real.sqrt (1 - t) * |ω.2|)
    (measurable_smartPathEnergy_slice hu t ω).aemeasurable
    (Filter.Eventually.of_forall (perceptron_smart_path_energy_le hD t ω))

/-- The partition integral is strictly positive; its finiteness follows from exponential
integrability. Counting mass is retained rather than normalized to a spin probability law. -/
theorem integral_exp_perceptron_smart_path_energy_pos {u : ℝ → ℝ} (hu : Measurable u)
    {D : ℝ} (hD : ∀ x, u x ≤ D) (ω : SmartPathDisorder N M) (t : ℝ) :
    0 < ∫ x, Real.exp (smartPathEnergy u t ω x) ∂μ :=
  integral_exp_pos_of_ae_le (C := M * D + Real.sqrt (1 - t) * |ω.2|)
    (measurable_smartPathEnergy_slice hu t ω).aemeasurable
    (Filter.Eventually.of_forall (perceptron_smart_path_energy_le hD t ω))

/-- The counting-times-Gaussian tilt defines a probability measure along the entire path. -/
theorem isProbabilityMeasure_tilted_perceptron_smart_path_energy {u : ℝ → ℝ} (hu : Measurable u)
    {D : ℝ} (hD : ∀ x, u x ≤ D) (ω : SmartPathDisorder N M) (t : ℝ) :
    IsProbabilityMeasure (μ.tilted (smartPathEnergy u t ω)) :=
  isProbabilityMeasure_tilted_of_ae_le (C := M * D + Real.sqrt (1 - t) * |ω.2|)
    (measurable_smartPathEnergy_slice hu t ω).aemeasurable
    (Filter.Eventually.of_forall (perceptron_smart_path_energy_le hD t ω))

/-- A uniformly bounded jointly measurable replica observable has an integrable disorder
average. The observable can depend on the shared disorder, as in the derivative formula.
The finite environment measure need not be Gaussian. -/
theorem integrable_integral_pi_perceptron_smart_path {R : Type*} [Fintype R]
    {u : ℝ → ℝ} (hu : Measurable u) {D : ℝ} (hD : ∀ x, u x ≤ D) (t : ℝ)
    {P : Measure (SmartPathDisorder N M)} [IsFiniteMeasure P]
    {Φ : SmartPathDisorder N M → (R → SmartPathState N M) → ℝ}
    (hΦ : Measurable fun p : SmartPathDisorder N M × (R → SmartPathState N M) => Φ p.1 p.2)
    {C : ℝ} (hC : ∀ ω x, |Φ ω x| ≤ C) :
    Integrable (fun ω => ∫ x : R → SmartPathState N M, Φ ω x
      ∂(Measure.pi fun _ : R => μ.tilted (smartPathEnergy u t ω))) P :=
  integrable_integral_pi_tilted (E := smartPathEnergy u t) (G := Φ)
    (measurable_smartPathEnergy hu t)
    (fun ω => isProbabilityMeasure_tilted_perceptron_smart_path_energy hu hD ω t)
    hΦ hC

end BaseMeasure

end SpinGlasses
