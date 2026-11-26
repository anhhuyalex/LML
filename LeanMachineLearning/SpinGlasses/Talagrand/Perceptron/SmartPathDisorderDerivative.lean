/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathGibbsDerivative
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ExpectedTilted
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein

/-!
# The quenched-disorder derivative of the perceptron smart path

This file justifies averaging the fixed-disorder derivative in Talagrand (2.26)--(2.27).
The two-sided bound on the potential controls the normalized density. Gaussian absolute
exponential moments give a common integrable disorder envelope on an interior interval.

The old disorder can have any finite law: the bound does not depend on its coordinates.
The last field has any nonnegative Gaussian variance, including zero. Replicas have
independent auxiliary coordinates and shared disorder. The three-term expansion (2.28)
is formalized as `hasDerivAt_integral_integral_pi_perceptron_smart_path_three_terms`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace SpinGlasses

/-- **Disorder-averaged Talagrand (2.26), with (2.27) substituted.** A differentiable potential
with bounded value and first derivative suffices to pass the derivative through the auxiliary,
replica and disorder integrals. The observable is bounded, measurable and independent of `t`.
The full number of spins is `N + 1`; empty replica/constraint types and zero variance are allowed.
No Gaussian integration-by-parts identity is assumed or asserted. -/
theorem hasDerivAt_integral_integral_pi_perceptron_smart_path {N M : ℕ}
    {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ]
    (hb : ∀ k : Fin M, Integrable (fun x : SmartPathState N M => |x.2 k|) μ)
    {R : Type*} [Fintype R] {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    {B D : ℝ} (hB : ∀ z, |u z| ≤ B) (hD : ∀ z, |deriv u z| ≤ D)
    (v : NNReal) {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    HasDerivAt (fun s => ∫ ω, ∫ σ, F σ
        ∂(Measure.pi fun _ : R => μ.tilted (smartPathEnergy u s ω))
        ∂smartPathDisorder Pold v)
      (∫ ω, replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
        (fun x => smartPathEnergyDerivA u t ω x + smartPathEnergyDerivXi u t ω x +
          smartPathEnergyDerivY t ω x) ∂smartPathDisorder Pold v) t := by
  obtain ⟨δ, hδ, hδt, hδ1⟩ := exists_pos_lt_of_mem_Ioo ht
  let V := Set.Ioo δ (1 - δ)
  have htV : t ∈ V := ⟨hδt, by linarith⟩
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  let K := 1 / (2 * Real.sqrt δ) + D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) / Real.sqrt δ
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let A := fun ω : SmartPathDisorder N M => (M : ℝ) * B + |ω.2|
  let Q := fun ω : SmartPathDisorder N M => K * Real.exp (|ω.2| + ∑ k, |ω.1.2 k|)
  let b := fun x : SmartPathState N M => 1 + ∑ k, |x.2 k|
  have hbi : Integrable b μ :=
    (integrable_const (1 : ℝ)).add (integrable_finsetSum _ fun k _ => hb k)
  have hEb (s : ℝ) (hs : s ∈ V) (ω : SmartPathDisorder N M) (x : SmartPathState N M) :
      |smartPathEnergy u s ω x| ≤ A ω :=
    abs_perceptron_smart_path_energy_le_of_nonneg hB s (hδ.trans hs.1).le ω x
  have hdb (s : ℝ) (hs : s ∈ V) (ω : SmartPathDisorder N M) (x : SmartPathState N M) :
      |smartPathEnergyDerivA u s ω x + smartPathEnergyDerivXi u s ω x +
        smartPathEnergyDerivY s ω x| ≤ Q ω * b x := by
    have hδ0 : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
    have hcoef : 0 ≤ D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) := by positivity
    have hlin := abs_deriv_perceptron_smart_path_energy_le hδ ⟨hs.1.le, hs.2.le⟩ hD ω x
    have hY0 := abs_nonneg ω.2
    have hA0 : 0 ≤ ∑ k, |ω.1.2 k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hX0 : 0 ≤ ∑ k, |x.2 k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hsum : ∑ k, D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) *
        ((|ω.1.2 k| + |x.2 k|) / Real.sqrt δ) =
        D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) / Real.sqrt δ *
          ((∑ k, |ω.1.2 k|) + ∑ k, |x.2 k|) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hp : 0 ≤ 1 / (2 * Real.sqrt δ) := by positivity
    have hr : 0 ≤ D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) / Real.sqrt δ := by positivity
    have e1 : |ω.2| + (∑ k, |ω.1.2 k|) + ∑ k, |x.2 k| ≤
        (1 + (|ω.2| + ∑ k, |ω.1.2 k|)) * (1 + ∑ k, |x.2 k|) := by
      nlinarith [mul_nonneg (add_nonneg hY0 hA0) hX0]
    have e2 : 1 + (|ω.2| + ∑ k, |ω.1.2 k|) ≤ Real.exp (|ω.2| + ∑ k, |ω.1.2 k|) := by
      linarith [Real.add_one_le_exp (|ω.2| + ∑ k, |ω.1.2 k|)]
    calc _ ≤ |ω.2| / (2 * Real.sqrt δ) + ∑ k,
          D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) *
            ((|ω.1.2 k| + |x.2 k|) / Real.sqrt δ) := hlin
      _ = 1 / (2 * Real.sqrt δ) * |ω.2| +
          D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) / Real.sqrt δ *
            ((∑ k, |ω.1.2 k|) + ∑ k, |x.2 k|) := by rw [hsum]; ring
      _ ≤ K * (|ω.2| + (∑ k, |ω.1.2 k|) + ∑ k, |x.2 k|) := by
          dsimp only [K]
          nlinarith [mul_nonneg hr hY0, mul_nonneg hp (add_nonneg hA0 hX0)]
      _ ≤ K * ((1 + (|ω.2| + ∑ k, |ω.1.2 k|)) * (1 + ∑ k, |x.2 k|)) :=
          mul_le_mul_of_nonneg_left e1 hK
      _ ≤ K * (Real.exp (|ω.2| + ∑ k, |ω.1.2 k|) * (1 + ∑ k, |x.2 k|)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e2 (by positivity)) hK
      _ = _ := by dsimp only [Q, b]; ring
  have hξ : Integrable (fun ξ : Fin M → ℝ => Real.exp (∑ k, |ξ k|))
      (Measure.pi fun _ : Fin M => gaussianReal 0 1) := by
    simpa only [one_mul] using integrable_exp_sum_mul_abs_pi_stdGaussian (fun _ : Fin M => (1 : ℝ))
  have houter : Integrable (fun ω => Real.exp (2 * ((Fintype.card R : ℝ) * A ω)) * Q ω)
      (smartPathDisorder Pold v) := by
    have hyexp : Integrable (fun y : ℝ =>
        Real.exp ((2 * (Fintype.card R : ℝ) + 1) * |y|)) (gaussianReal 0 v) :=
      integrable_exp_mul_abs_gaussianReal _
    have hi := ((hξ.comp_snd Pold).mul_prod hyexp).const_mul
      (K * Real.exp (2 * (Fintype.card R : ℝ) * M * B))
    apply hi.congr (ae_of_all _ fun ω => ?_)
    dsimp only [A, Q]
    rw [show 2 * ((Fintype.card R : ℝ) * ((M : ℝ) * B + |ω.2|)) =
      2 * (Fintype.card R : ℝ) * M * B + 2 * (Fintype.card R : ℝ) * |ω.2| by ring,
      show (2 * (Fintype.card R : ℝ) + 1) * |ω.2| =
        2 * (Fintype.card R : ℝ) * |ω.2| + |ω.2| by ring]
    simp only [Real.exp_add]
    ring
  exact hasDerivAt_integral_integral_pi_tilted_of_dominated (P := smartPathDisorder Pold v)
    (μ := μ) (E := smartPathEnergy u)
    (E' := fun s ω x => smartPathEnergyDerivA u s ω x + smartPathEnergyDerivXi u s ω x +
      smartPathEnergyDerivY s ω x) (A := A) (B := Q) (b := b) (s := V)
    isOpen_Ioo htV (fun s _ => measurable_smartPathEnergy hu.continuous.measurable s)
    (fun s _ => measurable_smartPathEnergyDeriv u s) hEb hbi hdb houter
    (fun ω x s hs => hasDerivAt_smartPathEnergy ⟨hδ.trans hs.1, by linarith [hs.2]⟩ hu ω x)
    hF hFb

/-- Splitting of the replica difference operator for the perceptron smart path energy into
three terms: the quenched disorder term, the auxiliary spin term, and the last-field term. -/
theorem perceptron_smart_path_diff_eq_three_terms {N M : ℕ}
    {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ]
    (hb : ∀ k : Fin M, Integrable (fun x : SmartPathState N M => |x.2 k|) μ) {u : ℝ → ℝ} {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (hu : Differentiable ℝ u) {B D : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hD : ∀ x, |deriv u x| ≤ D) (ω : SmartPathDisorder N M)
    {R : Type*} [Fintype R] (F : (R → SmartPathState N M) → ℝ)
    (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
        (fun x => smartPathEnergyDerivA u t ω x + smartPathEnergyDerivXi u t ω x +
          smartPathEnergyDerivY t ω x) =
      replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
          (smartPathEnergyDerivA u t ω) +
        replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
          (smartPathEnergyDerivXi u t ω) +
        replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
          (smartPathEnergyDerivY t ω) := by
  have hν : IsProbabilityMeasure (μ.tilted (smartPathEnergy u t ω)) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.continuous.measurable
      (fun x => le_of_abs_le (hB x)) ω t
  have hIY : Integrable (smartPathEnergyDerivY t ω)
      (μ.tilted (smartPathEnergy u t ω)) :=
    integrable_of_measurable_bound (measurable_smartPathEnergyDerivY_slice t ω)
      (M := |ω.2| / (2 * Real.sqrt (1 - t)))
      (abs_smartPathEnergyDerivY_le (sub_pos.2 ht.2) le_rfl ω)
  have hIa : Integrable (smartPathEnergyDerivA u t ω)
      (μ.tilted (smartPathEnergy u t ω)) :=
    integrable_of_measurable_bound (measurable_smartPathEnergyDerivA_slice u t ω)
      (M := ∑ k, D * (1 / (2 * Real.sqrt (N + 1 : ℕ))) * (|ω.1.2 k| / Real.sqrt t))
      (abs_smartPathEnergyDerivA_le hD ht.1 le_rfl ω)
  have hIE' := integrable_tilted_perceptron_smart_path_energy_deriv
    hb hu
    (fun x => le_of_abs_le (hB x)) hD ω t ht
  have hI_aξ : Integrable (fun x => smartPathEnergyDerivA u t ω x +
      smartPathEnergyDerivXi u t ω x) (μ.tilted (smartPathEnergy u t ω)) :=
    (hIE'.sub hIY).congr (ae_of_all _ fun x => by simp)
  have hIξ : Integrable (smartPathEnergyDerivXi u t ω)
      (μ.tilted (smartPathEnergy u t ω)) :=
    (hI_aξ.sub hIa).congr (ae_of_all _ fun x => by simp)
  rw [replicaDiff_add _ F hF.aestronglyMeasurable hFb hI_aξ hIY,
    replicaDiff_add _ F hF.aestronglyMeasurable hFb hIa hIξ]

/-- **(2.26)--(2.27) with the three groups of (2.28), before constraint symmetry.**
Differentiates the quenched replica average and splits the energy derivative into the
quenched-disorder term `E'_a`, the auxiliary-spin term `E'_ξ`, and the last-field term `E'_Y`.
This is the three-group split before the permutation symmetry in `k` that reduces the `k`-sum
to `α√N` times the last constraint. -/
theorem hasDerivAt_integral_integral_pi_perceptron_smart_path_three_terms {N M : ℕ}
    {μ : Measure (SmartPathState N M)} [IsFiniteMeasure μ] [NeZero μ]
    (hb : ∀ k : Fin M, Integrable (fun x : SmartPathState N M => |x.2 k|) μ)
    {R : Type*} [Fintype R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) {B D : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hD : ∀ x, |deriv u x| ≤ D) (v : NNReal)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (F : (R → SmartPathState N M) → ℝ) (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    HasDerivAt (fun s => ∫ ω, ∫ σ, F σ
        ∂(Measure.pi fun _ : R => μ.tilted (smartPathEnergy u s ω))
        ∂smartPathDisorder Pold v)
      (∫ ω, replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
            (smartPathEnergyDerivA u t ω) +
          replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
            (smartPathEnergyDerivXi u t ω) +
          replicaDiff (μ.tilted (smartPathEnergy u t ω)) F
            (smartPathEnergyDerivY t ω) ∂smartPathDisorder Pold v) t := by
  refine (hasDerivAt_integral_integral_pi_perceptron_smart_path hb ht hu hB hD v F hF
    hFb).congr_deriv (integral_congr_ae (ae_of_all _ fun ω => ?_))
  exact perceptron_smart_path_diff_eq_three_terms hb ht hu hB hD ω F hF hFb

/-- A spin-only replica observable is automatically measurable on the configuration space. -/
theorem measurable_spin_only {N M : ℕ} {R : Type*} [Finite R]
    (f : (R → PerceptronSpin N) → ℝ) :
    Measurable (fun x : R → SmartPathState N M => f (fun r => (x r).1)) :=
  (measurable_of_finite f).comp (by fun_prop)

/-- **Spin-only derivative of the quenched replica average.** A spin-only observable
requires no separate measurability or boundedness hypothesis. -/
theorem hasDerivAt_integral_integral_pi_perceptron_smart_path_spin_only {N M : ℕ}
    {R : Type*} [Fintype R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) {B D : ℝ} (hB : ∀ z, |u z| ≤ B)
    (hD : ∀ z, |deriv u z| ≤ D) (v : NNReal)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (f : (R → PerceptronSpin N) → ℝ) :
    HasDerivAt (fun s => ∫ ω, ∫ σ : R → SmartPathState N M, f (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => (smartPathBase N M).tilted (smartPathEnergy u s ω))
        ∂smartPathDisorder Pold v)
      (∫ ω, replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t ω))
        (fun σ => f (fun r => (σ r).1))
        (fun x => smartPathEnergyDerivA u t ω x + smartPathEnergyDerivXi u t ω x +
          smartPathEnergyDerivY t ω x) ∂smartPathDisorder Pold v) t := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_finite f
  exact hasDerivAt_integral_integral_pi_perceptron_smart_path
    (fun k => integrable_abs_snd_smartPathBase k) ht hu hB hD v
    (fun σ => f (fun r => (σ r).1)) (measurable_spin_only f) fun x => hC _

/-- **Spin-only three-term expansion of the quenched replica derivative.** -/
theorem hasDerivAt_integral_integral_pi_perceptron_smart_path_three_terms_spin_only {N M : ℕ}
    {R : Type*} [Fintype R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) {B D : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hD : ∀ x, |deriv u x| ≤ D) (v : NNReal)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (f : (R → PerceptronSpin N) → ℝ) :
    HasDerivAt (fun s => ∫ ω, ∫ σ : R → SmartPathState N M, f (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => (smartPathBase N M).tilted (smartPathEnergy u s ω))
        ∂smartPathDisorder Pold v)
      (∫ ω, replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t ω))
            (fun σ => f (fun r => (σ r).1)) (smartPathEnergyDerivA u t ω) +
          replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t ω))
            (fun σ => f (fun r => (σ r).1)) (smartPathEnergyDerivXi u t ω) +
          replicaDiff ((smartPathBase N M).tilted (smartPathEnergy u t ω))
            (fun σ => f (fun r => (σ r).1)) (smartPathEnergyDerivY t ω)
            ∂smartPathDisorder Pold v) t := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_finite f
  exact hasDerivAt_integral_integral_pi_perceptron_smart_path_three_terms
    (fun k => integrable_abs_snd_smartPathBase k) ht hu hB hD v
    (fun σ => f (fun r => (σ r).1)) (measurable_spin_only f) fun x => hC _

end SpinGlasses
