/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Order.Interval.UnitIoo
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathBounds
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathDifferentiation

/-!
# Differentiating replica Gibbs averages of the perceptron smart path

The auxiliary Gaussian coordinates belong to each replica's configuration. At fixed
quenched disorder the derivative of a bounded replica average is the sum of the energy
derivative terms at the observed replicas, minus their number times a fresh-replica term.

The proof supplies the integrable Gaussian envelope needed to differentiate the numerator
and normalizer. It reuses arbitrary-base exponential-tilt and replica differentiation lemmas.
No passage through the quenched-disorder integral or Gaussian integration by parts is
asserted in this file yet. Empty constraint and replica types and one full spin are allowed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace SpinGlasses

/-- **Talagrand (2.26), at fixed disorder.** Differentiation through all replica and auxiliary
integrals is justified by Gaussian first moments. A measurable upper-bounded potential with
bounded first derivative suffices; the replica observable is bounded and independent of `t`.
The observed replicas are indexed by `R`, and `none : Option R` is one fresh replica. -/
theorem hasDerivAt_integral_pi_perceptron_smart_path {N M : ℕ} {R : Type*} [Fintype R] {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    {B D : ℝ} (hB : ∀ z, u z ≤ B) (hD : ∀ z, |deriv u z| ≤ D)
    (ω : SmartPathDisorder N M) (F : (R → SmartPathState N M) → ℝ)
    (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    HasDerivAt (fun s => ∫ σ, F σ
        ∂(Measure.pi fun _ : R => (smartPathBase N M).tilted (smartPathEnergy u s ω)))
      (replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t ω)) F
        (fun x => smartPathEnergyDerivA u t ω x + smartPathEnergyDerivXi u t ω x +
          smartPathEnergyDerivY t ω x)) t := by
  obtain ⟨δ, hδ, hδt, hδ1⟩ := exists_pos_lt_of_mem_Ioo ht
  let s := Set.Ioo δ (1 - δ)
  have hs : s ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨hδt, by linarith⟩
  have hmE (r : ℝ) : Measurable (smartPathEnergy u r ω) :=
    measurable_smartPathEnergy_slice hu.continuous.measurable r ω
  have hEb (r : ℝ) (hr : r ∈ s) (x : SmartPathState N M) :
      smartPathEnergy u r ω x ≤ M * B + |ω.2| :=
    perceptron_smart_path_energy_le_of_nonneg hB r (hδ.trans hr.1).le ω x
  have hib := integrable_perceptron_smart_path_envelope (N := N) (M := M) D δ ω.2 ω.1.2
  have hcalc (x : SmartPathState N M) (r : ℝ) (hr : r ∈ s) :
      HasDerivAt (fun q => smartPathEnergy u q ω x)
        (smartPathEnergyDerivA u r ω x + smartPathEnergyDerivXi u r ω x +
          smartPathEnergyDerivY r ω x) r :=
    hasDerivAt_smartPathEnergy ⟨hδ.trans hr.1, by linarith [hr.2, hδ]⟩ hu ω x
  have hdb (r : ℝ) (hr : r ∈ s) (x : SmartPathState N M) :
      |smartPathEnergyDerivA u r ω x + smartPathEnergyDerivXi u r ω x +
        smartPathEnergyDerivY r ω x| ≤
      |ω.2| / (2 * Real.sqrt δ) + ∑ k, D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        ((|ω.1.2 k| + |x.2 k|) / Real.sqrt δ) :=
    abs_deriv_perceptron_smart_path_energy_le hδ ⟨hr.1.le, hr.2.le⟩ hD ω x
  have hres := hasDerivAt_integral_pi_tilted_of_dominated (μ := smartPathBase N M)
    (E := fun r => smartPathEnergy u r ω)
    (E' := fun r x => smartPathEnergyDerivA u r ω x + smartPathEnergyDerivXi u r ω x +
      smartPathEnergyDerivY r ω x) hs (fun r _ => hmE r)
    (measurable_smartPathEnergyDeriv_slice u t ω) hEb hib hdb hcalc hF hFb
  have hts : t ∈ s := mem_of_mem_nhds hs
  have hν :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.continuous.measurable hB ω t
  have hiTilted := integrable_tilted_of_abs_le_envelope (hmE t).aemeasurable
    (measurable_smartPathEnergyDeriv_slice u t ω).aestronglyMeasurable hib
    (ae_of_all _ (hEb t hts)) (ae_of_all _ (hdb t hts))
  convert hres using 1
  exact (integral_pi_cov_sum_eq_sum_sub_fresh _ F hF.aestronglyMeasurable hFb _ hiTilted).symm

/-- The energy derivative is integrable against the tilted measure for any `t ∈ (0, 1)`. -/
theorem integrable_tilted_perceptron_smart_path_energy_deriv {N M : ℕ} {u : ℝ → ℝ}
    (hu : Differentiable ℝ u) {B D : ℝ} (hB : ∀ x, u x ≤ B) (hD : ∀ z, |deriv u z| ≤ D)
    (ω : SmartPathDisorder N M) (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
    Integrable (fun x => smartPathEnergyDerivA u t ω x + smartPathEnergyDerivXi u t ω x +
      smartPathEnergyDerivY t ω x) ((smartPathBase N M).tilted (smartPathEnergy u t ω)) := by
  obtain ⟨δ, hδ, hδt, hδ1⟩ := exists_pos_lt_of_mem_Ioo ht
  exact integrable_tilted_of_abs_le_envelope
    (measurable_smartPathEnergy_slice hu.continuous.measurable t ω).aemeasurable
    (measurable_smartPathEnergyDeriv_slice u t ω).aestronglyMeasurable
    (integrable_perceptron_smart_path_envelope (N := N) (M := M) D δ ω.2 ω.1.2)
    (ae_of_all _ (perceptron_smart_path_energy_le_of_nonneg hB t ht.1.le ω))
    (ae_of_all _ (abs_deriv_perceptron_smart_path_energy_le hδ ⟨hδt.le, by linarith⟩ hD ω))

end SpinGlasses
