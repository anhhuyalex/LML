/-
Copyright (c) 2025 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.StrongLawMixture
public import LeanMachineLearning.ForMathlib.Probability.Moments.PiSumChebyshev
public import LeanMachineLearning.Optimization.NTK.Basic
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import LeanMachineLearning.Optimization.ConvexOpt.Basic
public import Mathlib.Analysis.Calculus.Deriv.Pi

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
over an i.i.d. sequence drawn from an arbitrary probability measure `ν`, with the average written
over `Fin n` (`ProbabilityTheory.ae_tendsto_mean_infinitePi` is the `Finset.range` form). -/
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
  filter_upwards [ProbabilityTheory.ae_tendsto_mean_infinitePi ν hg_meas hg_int] with seq hseq
  convert hseq using 1
  ext width
  rw [Fin.sum_univ_eq_sum_range (fun i => g (seq i)) width]

/-- Almost-sure convergence of a sequence of matrices follows from almost-sure convergence of
each entry (the index types are finite, so the countably many null sets can be merged). -/
lemma ae_tendsto_matrix_of_forall_entry {Ω ι κ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [Finite ι] [Finite κ] {F : ℕ → Ω → Matrix ι κ ℝ} {L : Matrix ι κ ℝ}
    (h : ∀ i j, ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω i j) atTop (nhds (L i j))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (nhds L) := by
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j => h i j] with ω hω
  exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hω i j

/-- **Independence across coordinates.** Under an i.i.d. product measure, the `ℓ`-th coordinate is
independent of the family of all earlier coordinates `(ω i)_{i < ℓ}`. -/
theorem indepFun_pi_apply_Iio {ι X : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
    [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ] (ℓ : ι) :
    IndepFun (fun ω : ι → X => ω ℓ) (fun ω : ι → X => fun i : Finset.Iio ℓ => ω i)
      (Measure.pi fun _ : ι => μ) := by
  have h_indep : iIndepFun (fun ℓ : ι => fun ω : ι → X => ω ℓ) (Measure.pi fun _ : ι => μ) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have h_disj : Disjoint ({ℓ} : Finset ι) (Finset.Iio ℓ) :=
    Finset.disjoint_singleton_left.2 (by simp)
  have h := h_indep.indepFun_finset {ℓ} (Finset.Iio ℓ) h_disj fun i => measurable_pi_apply i
  exact h.comp (measurable_pi_apply (⟨ℓ, Finset.mem_singleton_self ℓ⟩ : ({ℓ} : Finset ι)))
    measurable_id

/-! ### Generic Finite-Sample Concentration for i.i.d. Averages -/

section IIDAverageConcentration

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
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hint : Integrable Y ν := hY.integrable one_le_two
  have h := measure_pi_ge_abs_mul_sum_le ν (fun _ : Fin n => fun x => Y x - ∫ y, Y y ∂ν)
    (fun _ => hY.sub (memLp_const _)) (fun _ => by
      rw [integral_sub hint (integrable_const _)]; simp) (n : ℝ)⁻¹ hc
  simp_rw [variance_sub_const hY.aestronglyMeasurable, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at h
  have hset : ∀ ω : Fin n → Ω, (n : ℝ)⁻¹ * ∑ i, (Y (ω i) - ∫ y, Y y ∂ν) =
      (n : ℝ)⁻¹ * ∑ i, Y (ω i) - ∫ x, Y x ∂ν := fun ω => by
    simp [Finset.sum_sub_distrib, mul_sub, Finset.sum_const, hn_ne]
  simp_rw [hset] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  field_simp

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
