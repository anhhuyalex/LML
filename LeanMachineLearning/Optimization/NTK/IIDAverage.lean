/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import LeanMachineLearning.Optimization.ConvexOpt.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Empirical averages of i.i.d. samples

Generic probability facts with no neural-network content: the strong law for an i.i.d. sequence
drawn from a probability measure `ν` (as a statement on the infinite product measure), and
expectation, variance and Chebyshev bounds for the empirical average of an `ℒ²` observable under
a finite product probability measure.
-/
@[expose] public section

open Real MeasureTheory ProbabilityTheory Filter ConvexOpt
open scoped RealInnerProductSpace Matrix

namespace NTK

/-- The strong law for empirical averages of a measurable integrable observable
over an i.i.d. sequence drawn from an arbitrary probability measure `ν`. This packages
product-measure independence, identical distribution, expectation transport,
and `Finset.range`/`Fin` conversion. -/
lemma iid_average_tendsto_integral {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (g : Ω → ℝ)
    (hg_meas : Measurable g)
    (hg_int : Integrable g ν) :
    ∀ᵐ seq : ℕ → Ω ∂(Measure.infinitePi fun _ : ℕ => ν),
      Filter.Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j : Fin n, g (seq j))
        Filter.atTop
        (nhds (∫ ω, g ω ∂ν)) := by
  set μ := Measure.infinitePi (fun _ : ℕ => ν)
  have hmap_eval : ∀ i : ℕ, μ.map (fun seq => seq i) = ν :=
    fun i => Measure.infinitePi_map_eval _ i
  have hmp : MeasurePreserving (fun seq : ℕ → Ω => seq 0) μ ν :=
    measurePreserving_eval_infinitePi (fun _ : ℕ => ν) 0
  have hint : Integrable (fun seq : ℕ → Ω => g (seq 0)) μ :=
    (hmp.integrable_comp hg_meas.aestronglyMeasurable).2 hg_int
  have hindep : Pairwise (Function.onFun (· ⟂ᵢ[μ] ·) fun j seq => g (seq j)) := by
    have h := iIndepFun_infinitePi (P := fun _ : ℕ => ν)
      (X := fun _ : ℕ => g) (fun _ => hg_meas)
    intro i j hij
    exact h.indepFun hij
  have hident : ∀ i : ℕ,
      IdentDistrib (fun seq : ℕ → Ω => g (seq i))
        (fun seq : ℕ → Ω => g (seq 0)) μ μ := by
    intro i
    have hcoord : IdentDistrib (fun seq : ℕ → Ω => seq i)
        (fun seq : ℕ → Ω => seq 0) μ μ := by
      refine ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable, ?_⟩
      rw [hmap_eval i, hmap_eval 0]
    exact hcoord.comp hg_meas
  have hslln : ∀ᵐ seq ∂μ, Filter.Tendsto
      (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, g (seq i))
      Filter.atTop (nhds (∫ seq, g (seq 0) ∂μ)) :=
    strong_law_ae _ hint hindep hident
  have hexp : ∫ seq, g (seq 0) ∂μ = ∫ ω, g ω ∂ν := by
    rw [← hmap_eval 0]
    exact (MeasureTheory.integral_map (measurable_pi_apply 0).aemeasurable
      hg_meas.stronglyMeasurable.aestronglyMeasurable).symm
  filter_upwards [hslln] with seq hseq
  rw [← hexp]
  convert hseq using 1
  ext width
  rw [smul_eq_mul, Fin.sum_univ_eq_sum_range (fun i => g (seq i)) width]

/-! ### Generic Finite-Sample Concentration for i.i.d. Averages -/

section IIDAverageConcentration

/-- Integration of coordinate evaluation under a finite product probability measure. -/
private lemma integral_coord_pi {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    {n : ℕ} (Y : Ω → ℝ) (hY : MemLp Y 2 ν) (i : Fin n) :
    ∫ ω : Fin n → Ω, Y (ω i) ∂(Measure.pi fun _ : Fin n => ν) = ∫ x, Y x ∂ν := by
  have h_mp := measurePreserving_eval (fun _ : Fin n => ν) i
  have h_meas : AEMeasurable (Function.eval i) (Measure.pi fun _ : Fin n => ν) :=
    (measurable_pi_apply i).aemeasurable
  have h_aestrong :
      AEStronglyMeasurable Y (Measure.map (Function.eval i) (Measure.pi fun _ : Fin n => ν)) := by
    rw [h_mp.map_eq]
    exact hY.aestronglyMeasurable
  have h_eq : (∫ x, Y x ∂ν) =
      ∫ x, Y x ∂(Measure.map (Function.eval i) (Measure.pi fun _ : Fin n => ν)) := by
    rw [h_mp.map_eq]
  rw [h_eq]
  exact (integral_map h_meas h_aestrong).symm

/-- An empirical average of coordinate functions is in `ℒ²` under a product probability measure. -/
private lemma memLp_two_average_pi {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (Y : Ω → ℝ) (hY : MemLp Y 2 ν) :
    MemLp (fun ω : Fin n → Ω => (n : ℝ)⁻¹ * ∑ i : Fin n, Y (ω i)) 2
      (Measure.pi fun _ : Fin n => ν) := by
  have h_coord : ∀ i : Fin n, MemLp (fun ω : Fin n → Ω => Y (ω i)) 2
      (Measure.pi fun _ : Fin n => ν) := fun i =>
    hY.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => ν) i)
  have h_sum : MemLp (fun ω : Fin n → Ω => ∑ i : Fin n, Y (ω i)) 2
      (Measure.pi fun _ : Fin n => ν) :=
    memLp_finsetSum (Finset.univ : Finset (Fin n)) (fun i _ => h_coord i)
  exact h_sum.const_mul (n : ℝ)⁻¹

/-- Expectation of an empirical average under a finite product probability measure. -/
private lemma integral_average_pi {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) (Y : Ω → ℝ) (hY : MemLp Y 2 ν) :
    ∫ ω : Fin n → Ω, ((n : ℝ)⁻¹ * ∑ i : Fin n, Y (ω i)) ∂(Measure.pi fun _ : Fin n => ν) =
      ∫ x, Y x ∂ν := by
  have h_coord_int : ∀ i : Fin n,
      Integrable (fun ω : Fin n → Ω => Y (ω i)) (Measure.pi fun _ : Fin n => ν) := fun i =>
    (hY.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => ν) i)).integrable
      (by norm_num)
  have h_sum_int : ∫ ω : Fin n → Ω, (∑ i : Fin n, Y (ω i)) ∂(Measure.pi fun _ : Fin n => ν) =
      (n : ℝ) * ∫ x, Y x ∂ν := by
    rw [integral_finsetSum Finset.univ (fun i _ => h_coord_int i)]
    simp_rw [integral_coord_pi ν Y hY, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [integral_const_mul, h_sum_int]
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (ne_of_gt hn)
  rw [← mul_assoc, inv_mul_cancel₀ hn_ne, one_mul]

/-- Variance of an empirical average under an i.i.d. finite product probability measure. -/
lemma variance_average_pi {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) (Y : Ω → ℝ) (hY : MemLp Y 2 ν) :
    Var[fun ω : Fin n → Ω => (n : ℝ)⁻¹ * ∑ i : Fin n, Y (ω i); Measure.pi fun _ : Fin n => ν] =
      (n : ℝ)⁻¹ * Var[Y; ν] := by
  have h_sum : Var[∑ i : Fin n, fun ω : Fin n → Ω => Y (ω i); Measure.pi fun _ : Fin n => ν] =
      (n : ℝ) * Var[Y; ν] := by
    have h := @variance_sum_pi (Fin n) _ (fun _ => Ω) (fun _ => inferInstance)
      (fun _ => ν) (fun _ => inferInstance) (fun _ => Y) (fun _ => hY)
    rw [h]
    simp [Finset.sum_const]
  have heq : (∑ i : Fin n, fun ω : Fin n → Ω => Y (ω i)) = (fun ω => ∑ i : Fin n, Y (ω i)) := by
    ext ω
    simp only [Finset.sum_apply]
  rw [heq] at h_sum
  have h_scale : (fun ω : Fin n → Ω => (n : ℝ)⁻¹ * ∑ i : Fin n, Y (ω i)) =
      (n : ℝ)⁻¹ • (fun ω => ∑ i : Fin n, Y (ω i)) := by
    ext ω
    rfl
  rw [h_scale, variance_smul, h_sum, sq, mul_assoc]
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (ne_of_gt hn)
  congr 1
  rw [← mul_assoc, inv_mul_cancel₀ hn_ne, one_mul]

/-- Chebyshev inequality for empirical averages of an `ℒ²` observable under an i.i.d.
finite product probability measure. -/
theorem chebyshev_average_pi {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] {n : ℕ} (hn : 0 < n) (Y : Ω → ℝ) (hY : MemLp Y 2 ν)
    {c : ℝ} (hc : 0 < c) :
    (Measure.pi fun _ : Fin n => ν)
      {ω | c ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, Y (ω i) - ∫ x, Y x ∂ν|} ≤
      ENNReal.ofReal (Var[Y; ν] / ((n : ℝ) * c ^ 2)) := by
  have h_cheb := meas_ge_le_variance_div_sq (memLp_two_average_pi ν n Y hY) hc
  rw [integral_average_pi ν hn Y hY, variance_average_pi ν hn Y hY] at h_cheb
  have heq : ((n : ℝ)⁻¹ * Var[Y; ν]) / c ^ 2 = Var[Y; ν] / ((n : ℝ) * c ^ 2) := by
    ring
  rwa [heq] at h_cheb

/-- Chebyshev inequality for empirical averages bounded by the uncentered second moment
`∫ x, (Y x)^2 ∂ν`. -/
theorem chebyshev_average_pi_le_second_moment {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    [IsProbabilityMeasure ν] {n : ℕ} (hn : 0 < n) (Y : Ω → ℝ) (hY : MemLp Y 2 ν)
    {c : ℝ} (hc : 0 < c) :
    (Measure.pi fun _ : Fin n => ν)
      {ω | c ≤ |(n : ℝ)⁻¹ * ∑ i : Fin n, Y (ω i) - ∫ x, Y x ∂ν|} ≤
      ENNReal.ofReal ((∫ x, Y x ^ 2 ∂ν) / ((n : ℝ) * c ^ 2)) := by
  refine (chebyshev_average_pi ν hn Y hY hc).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have h_var_le := variance_le_expectation_sq hY.aestronglyMeasurable (μ := ν)
  have hc2_pos : 0 < (n : ℝ) * c ^ 2 := mul_pos (Nat.cast_pos.2 hn) (sq_pos_of_ne_zero hc.ne')
  exact div_le_div_of_nonneg_right h_var_le hc2_pos.le

end IIDAverageConcentration

end NTK

end
