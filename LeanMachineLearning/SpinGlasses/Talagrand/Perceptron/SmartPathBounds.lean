/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.GibbsAverages

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

/-- The smart-path energy is jointly measurable in the quenched disorder and configuration. -/
theorem measurable_perceptron_smart_path_energy {u : ℝ → ℝ} (hu : Measurable u) (t : ℝ) :
    Measurable fun p :
      (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) ×
        (((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ((p.2.1.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * p.1.2 +
        ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ *
          (∑ i, p.1.1.1 k i * ((p.2.1.1 i : ℤ) : ℝ)) +
            Real.sqrt (t / (N + 1)) * p.1.1.2 k * ((p.2.1.2 : ℤ) : ℝ) +
            Real.sqrt ((1 - t) / (N + 1)) * p.2.2 k) := by
  have hcast : Measurable (fun ε : ℤˣ => ((ε : ℤ) : ℝ)) := measurable_of_countable _
  fun_prop

/-- An upper bound on the potential gives an upper bound on the smart-path energy. -/
theorem perceptron_smart_path_energy_le {u : ℝ → ℝ} {D : ℝ} (hD : ∀ x, u x ≤ D)
    (g : Fin M → Fin N → ℝ) (a : Fin M → ℝ) (y t : ℝ)
    (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) :
    ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * y +
      ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, g k i * ((x.1.1 i : ℤ) : ℝ)) +
        Real.sqrt (t / (N + 1)) * a k * ((x.1.2 : ℤ) : ℝ) +
        Real.sqrt ((1 - t) / (N + 1)) * x.2 k) ≤
      M * D + Real.sqrt (1 - t) * |y| := by
  have hb : |((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * y| =
      Real.sqrt (1 - t) * |y| := by
    simp only [abs_mul, abs_units_cast_eq_one, abs_of_nonneg (Real.sqrt_nonneg _), one_mul]
  calc
    _ ≤ Real.sqrt (1 - t) * |y| + ∑ _k : Fin M, D :=
      add_le_add ((le_abs_self _).trans hb.le) (Finset.sum_le_sum fun k _ => hD _)
    _ = _ := by simp [add_comm]

/-- The auxiliary coordinates do not affect the bound for a bounded potential. -/
theorem abs_perceptron_smart_path_energy_le {u : ℝ → ℝ} {D : ℝ} (hD : ∀ x, |u x| ≤ D)
    (g : Fin M → Fin N → ℝ) (a : Fin M → ℝ) (y t : ℝ)
    (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) :
    |((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * y +
      ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, g k i * ((x.1.1 i : ℤ) : ℝ)) +
        Real.sqrt (t / (N + 1)) * a k * ((x.1.2 : ℤ) : ℝ) +
        Real.sqrt ((1 - t) / (N + 1)) * x.2 k)| ≤
      M * D + Real.sqrt (1 - t) * |y| := by
  refine abs_le.mpr ⟨?_, perceptron_smart_path_energy_le
    (fun z => le_of_abs_le (hD z)) g a y t x⟩
  have hn := perceptron_smart_path_energy_le (u := fun z => -u z)
    (fun z => by linarith [neg_le_of_abs_le (hD z)]) g a (-y) t x
  have hneg : -(((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * y +
      ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, g k i * ((x.1.1 i : ℤ) : ℝ)) +
        Real.sqrt (t / (N + 1)) * a k * ((x.1.2 : ℤ) : ℝ) +
        Real.sqrt ((1 - t) / (N + 1)) * x.2 k)) ≤
      M * D + Real.sqrt (1 - t) * |y| := by
    simpa only [abs_neg, mul_neg, Finset.sum_neg_distrib, ← neg_add] using hn
  exact neg_le.mp hneg

/-- The Gibbs weight is integrable for every fixed disorder and path parameter. -/
theorem integrable_exp_perceptron_smart_path_energy {u : ℝ → ℝ} (hu : Measurable u)
    {D : ℝ} (hD : ∀ x, u x ≤ D) (g : Fin M → Fin N → ℝ)
    (a : Fin M → ℝ) (y t : ℝ) :
    Integrable (fun x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) =>
      Real.exp (((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * y +
        ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, g k i * ((x.1.1 i : ℤ) : ℝ)) +
          Real.sqrt (t / (N + 1)) * a k * ((x.1.2 : ℤ) : ℝ) +
          Real.sqrt ((1 - t) / (N + 1)) * x.2 k)))
      ((Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ)).prod
        (Measure.pi fun _ : Fin M => gaussianReal 0 1)) := by
  exact integrable_exp_of_ae_le (C := M * D + Real.sqrt (1 - t) * |y|)
    (((measurable_perceptron_smart_path_energy (N := N) (M := M) hu t).comp
      ((measurable_const (a := ((g, a), y))).prodMk measurable_id)).aemeasurable)
    (Filter.Eventually.of_forall (perceptron_smart_path_energy_le hD g a y t))

/-- The partition integral is strictly positive; its finiteness follows from exponential
integrability. Counting mass is retained rather than normalized to a spin probability law. -/
theorem integral_exp_perceptron_smart_path_energy_pos {u : ℝ → ℝ} (hu : Measurable u)
    {D : ℝ} (hD : ∀ x, u x ≤ D) (g : Fin M → Fin N → ℝ)
    (a : Fin M → ℝ) (y t : ℝ) :
    0 < ∫ x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ),
      Real.exp (((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * y +
        ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, g k i * ((x.1.1 i : ℤ) : ℝ)) +
          Real.sqrt (t / (N + 1)) * a k * ((x.1.2 : ℤ) : ℝ) +
          Real.sqrt ((1 - t) / (N + 1)) * x.2 k))
      ∂((Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ)).prod
        (Measure.pi fun _ : Fin M => gaussianReal 0 1)) := by
  exact integral_exp_pos_of_ae_le (C := M * D + Real.sqrt (1 - t) * |y|)
    (((measurable_perceptron_smart_path_energy (N := N) (M := M) hu t).comp
      ((measurable_const (a := ((g, a), y))).prodMk measurable_id)).aemeasurable)
    (Filter.Eventually.of_forall (perceptron_smart_path_energy_le hD g a y t))

/-- The counting-times-Gaussian tilt defines a probability measure along the entire path. -/
theorem isProbabilityMeasure_tilted_perceptron_smart_path_energy {u : ℝ → ℝ} (hu : Measurable u)
    {D : ℝ} (hD : ∀ x, u x ≤ D) (g : Fin M → Fin N → ℝ)
    (a : Fin M → ℝ) (y t : ℝ) :
    IsProbabilityMeasure (((Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ)).prod
        (Measure.pi fun _ : Fin M => gaussianReal 0 1)).tilted
      (fun x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ) => ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * y +
        ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, g k i * ((x.1.1 i : ℤ) : ℝ)) +
          Real.sqrt (t / (N + 1)) * a k * ((x.1.2 : ℤ) : ℝ) +
          Real.sqrt ((1 - t) / (N + 1)) * x.2 k))) := by
  exact isProbabilityMeasure_tilted_of_ae_le (C := M * D + Real.sqrt (1 - t) * |y|)
    (((measurable_perceptron_smart_path_energy (N := N) (M := M) hu t).comp
      ((measurable_const (a := ((g, a), y))).prodMk measurable_id)).aemeasurable)
    (Filter.Eventually.of_forall (perceptron_smart_path_energy_le hD g a y t))

/-- A uniformly bounded jointly measurable replica observable has an integrable disorder
average. The observable can depend on the shared disorder, as in the derivative formula.
The finite environment measure need not be Gaussian. -/
theorem integrable_integral_pi_perceptron_smart_path {R : Type*} [Fintype R]
    {u : ℝ → ℝ} (hu : Measurable u) {D : ℝ} (hD : ∀ x, u x ≤ D) (t : ℝ)
    {P : Measure (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)} [IsFiniteMeasure P]
    {Φ : (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) →
      (R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) → ℝ}
    (hΦ : Measurable fun p : (((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ) ×
      (R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) => Φ p.1 p.2) {C : ℝ} (hC : ∀ ω x, |Φ ω x| ≤ C) :
    let E := fun (ω : ((Fin M → Fin N → ℝ) × (Fin M → ℝ)) × ℝ)
      (x : ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ)) =>
      ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * ω.2 +
        ∑ k, u ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i, ω.1.1 k i * ((x.1.1 i : ℤ) : ℝ)) +
          Real.sqrt (t / (N + 1)) * ω.1.2 k * ((x.1.2 : ℤ) : ℝ) +
          Real.sqrt ((1 - t) / (N + 1)) * x.2 k)
    Integrable (fun ω => ∫ x : R → ((Fin N → ℤˣ) × ℤˣ) × (Fin M → ℝ), Φ ω x
      ∂(Measure.pi fun _ : R => ((Measure.count : Measure ((Fin N → ℤˣ) × ℤˣ)).prod
        (Measure.pi fun _ : Fin M => gaussianReal 0 1)).tilted (E ω))) P := by
  intro E
  exact integrable_integral_pi_tilted (E := E) (G := Φ)
    (measurable_perceptron_smart_path_energy (N := N) (M := M) hu t)
    (fun ω => isProbabilityMeasure_tilted_perceptron_smart_path_energy (N := N) (M := M)
      hu hD ω.1.1 ω.1.2 ω.2 t)
    hΦ hC

end SpinGlasses
