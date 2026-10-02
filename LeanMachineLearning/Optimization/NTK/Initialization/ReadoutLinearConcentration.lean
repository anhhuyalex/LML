/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Initialization.ReadoutConcentration
public import LeanMachineLearning.Optimization.NTK.Initialization.ResidualConcentration

/-!
# Gaussian Linear Forms in the Readout

`g_{d-1} = W_d ⊙ φ'(h_{d-1})`, so the gradient-independence quantity at the top hidden layer
`n⁻¹ ⟨h_{d-1}^b, g_{d-1}^a⟩ = n⁻¹ ∑ⱼ (h^b φ'(h^a))ⱼ W_{d,j}` is a centred Gaussian linear form in
the independent readout.

* `chebyshev_linear_weighted`: `P(|n⁻¹ ∑ⱼ aⱼ yⱼ| ≥ ε) ≤ (∑ⱼ yⱼ²) / (n² ε²)` for `a ~ 𝒩(0, Iₙ)`.
* `tendstoInMeasure_gaussianLinear_average`: if the weights `y n w` (a function of the past `w`)
  satisfy `n⁻¹ ∑ⱼ yⱼ² ≤` a convergent sequence, then `n⁻¹ ∑ⱼ yⱼ vⱼ → 0` in measure for an
  independent standard Gaussian readout `v`.
-/

@[expose]
public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace NTK

/-- **Chebyshev for a weighted Gaussian linear form.** -/
theorem chebyshev_linear_weighted (n : ℕ) (hn : 0 < n) (y : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1)
      {a | ε ≤ |(n : ℝ)⁻¹ * ∑ j : Fin n, a j * y j|} ≤
      ENNReal.ofReal ((∑ j, y j ^ 2) / ((n : ℝ) ^ 2 * ε ^ 2)) := by
  classical
  let μ : Measure (Fin n → ℝ) := Measure.pi fun _ : Fin n => gaussianReal 0 1
  let g : Fin n → ℝ → ℝ := fun j x => x * y j
  have hg : ∀ j, MemLp (g j) 2 (gaussianReal 0 1) := fun j =>
    (memLp_id_gaussianReal 2).mul_const (y j)
  let S : (Fin n → ℝ) → ℝ := ∑ j, fun a => g j (a j)
  have hS_eq : ∀ a, S a = ∑ j : Fin n, a j * y j := by
    intro a; simp [S, g, Finset.sum_apply]
  have hS_mem : MemLp S 2 μ := by
    refine memLp_finsetSum' _ fun j _ => ?_
    exact (hg j).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) j)
  have hX_mem : MemLp (fun a => (n : ℝ)⁻¹ * S a) 2 μ := hS_mem.const_mul _
  have hS_fun : S = fun a => ∑ j : Fin n, g j (a j) := by
    funext a; simp [S, Finset.sum_apply]
  have hmean_S : μ[S] = 0 := by
    have hj : ∀ j : Fin n, ∫ a, g j (a j) ∂μ = 0 := by
      intro j
      have hmp := measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) j
      have hgm : AEStronglyMeasurable (g j) (Measure.map (Function.eval j) μ) :=
        (by fun_prop : Measurable (g j)).aestronglyMeasurable
      calc ∫ a, g j (a j) ∂μ
          = ∫ x, g j x ∂(Measure.map (Function.eval j) μ) :=
            (integral_map hmp.measurable.aemeasurable hgm).symm
        _ = ∫ x, g j x ∂(gaussianReal 0 1) := by rw [hmp.map_eq]
        _ = 0 := by
          simp only [g]
          rw [integral_mul_const]
          rw [integral_id_gaussianReal, zero_mul]
    rw [hS_fun]
    rw [integral_finsetSum (f := fun (j : Fin n) (a : Fin n → ℝ) => g j (a j)) _
      (fun j _ => ((hg j).comp_measurePreserving
        (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) j)).integrable
          (by norm_num))]
    exact Finset.sum_eq_zero fun j _ => hj j
  have hmean : μ[fun a => (n : ℝ)⁻¹ * S a] = 0 := by
    rw [integral_const_mul, hmean_S, mul_zero]
  have hvarS : Var[S; μ] = ∑ j, y j ^ 2 := by
    have h := variance_sum_pi (μ := fun _ : Fin n => gaussianReal 0 1) hg
    simp only [S]
    rw [h]
    have hvj : ∀ j, Var[g j; gaussianReal 0 1] = y j ^ 2 := by
      intro j
      have : g j = fun x => y j * id x := by funext x; simp [g, mul_comm]
      rw [this, variance_const_mul, variance_id_gaussianReal]
      simp
    simp_rw [hvj]
  have hvar : Var[fun a => (n : ℝ)⁻¹ * S a; μ] = (n : ℝ)⁻¹ ^ 2 * ∑ j, y j ^ 2 := by
    rw [variance_const_mul, hvarS]
  have hcheb := meas_ge_le_variance_div_sq hX_mem hε
  rw [hmean, hvar] at hcheb
  have hset : {a : Fin n → ℝ | ε ≤ |(n : ℝ)⁻¹ * ∑ j : Fin n, a j * y j|} =
      {a | ε ≤ |(n : ℝ)⁻¹ * S a - 0|} := by
    ext a; simp [hS_eq]
  rw [hset]
  refine hcheb.trans (le_of_eq ?_)
  congr 1
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- **Gaussian linear forms in the readout vanish.** Let `v ~ 𝒩(0, I)` (the readout population) be
independent of the weights `y n w`, with `n⁻¹ ∑ⱼ yⱼ²` bounded by a convergent sequence. Then
`n⁻¹ ∑ⱼ vⱼ yⱼ → 0` in measure. -/
theorem tendstoInMeasure_gaussianLinear_average
    {Ω : Type*} [MeasurableSpace Ω] (νH : Measure Ω) [IsProbabilityMeasure νH]
    (y : ∀ n : ℕ, Ω → Fin n → ℝ) (hy : ∀ n j, Measurable fun w => y n w j)
    (hb : BddByConv νH (fun (n : ℕ) (w : Ω) => (n : ℝ)⁻¹ * ∑ j : Fin n, y n w j ^ 2)) :
    TendstoInMeasure (νH.prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (fun (n : ℕ) (q : Ω × (ℕ → ℝ)) => (n : ℝ)⁻¹ * ∑ j : Fin n, q.2 j.val * y n q.1 j)
      atTop (fun _ => 0) := by
  obtain ⟨B, cB, hB, hBc⟩ := hb
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hscaled := tendstoInMeasure_inv_nat_mul hBc
  have hb0 : TendstoInMeasure νH (fun (n : ℕ) (w : Ω) => (ε ^ 2)⁻¹ * ((n : ℝ)⁻¹ * B n w)) atTop
      (fun _ => 0) := by
    have h := tendstoInMeasure_mul (tendstoInMeasure_const (μ := νH) ((ε ^ 2)⁻¹)) hscaled
    rwa [mul_zero] at h
  set S : ℕ → Set (Ω × (ℕ → ℝ)) := fun n =>
    {q | ε ≤ dist ((n : ℝ)⁻¹ * ∑ j : Fin n, q.2 j.val * y n q.1 j) 0} with hS
  have hS_meas : ∀ n, MeasurableSet (S n) := by
    intro n
    have h1 : Measurable (fun q : Ω × (ℕ → ℝ) =>
        (n : ℝ)⁻¹ * ∑ j : Fin n, q.2 j.val * y n q.1 j) :=
      measurable_const.mul (Finset.measurable_sum _ fun j _ =>
        ((measurable_pi_apply j.val).comp measurable_snd).mul ((hy n j).comp measurable_fst))
    exact measurableSet_le measurable_const (h1.dist measurable_const)
  have hsec : ∀ n : ℕ, 0 < n → ∀ w : Ω,
      (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) {v | (w, v) ∈ S n} ≤
        min 1 (ENNReal.ofReal ((ε ^ 2)⁻¹ * ((n : ℝ)⁻¹ * B n w))) := by
    intro n hn w
    refine le_min prob_le_one ?_
    have hrestr : Measurable (fun v : ℕ → ℝ => fun j : Fin n => v j.val) :=
      measurable_pi_iff.2 fun j => measurable_pi_apply j.val
    have hT : MeasurableSet {a : Fin n → ℝ |
        ε ≤ |(n : ℝ)⁻¹ * ∑ j : Fin n, a j * y n w j|} := by
      refine measurableSet_le measurable_const (continuous_abs.measurable.comp ?_)
      exact measurable_const.mul (Finset.measurable_sum _ fun j _ =>
        (measurable_pi_apply j).mul_const _)
    have hset : {v | (w, v) ∈ S n} = (fun v : ℕ → ℝ => fun j : Fin n => v j.val) ⁻¹'
        {a : Fin n → ℝ | ε ≤ |(n : ℝ)⁻¹ * ∑ j : Fin n, a j * y n w j|} := by
      ext v
      simp [hS]
    rw [hset, ← Measure.map_apply hrestr hT, map_infinitePi_real_eq_gaussianReadoutMeasure]
    refine (chebyshev_linear_weighted n hn (y n w) hε).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hsum : ∑ j : Fin n, y n w j ^ 2 = n * ((n : ℝ)⁻¹ * ∑ j : Fin n, y n w j ^ 2) := by
      field_simp
    rw [hsum]
    have hle := hB n w
    calc (n * ((n : ℝ)⁻¹ * ∑ j : Fin n, y n w j ^ 2)) / ((n : ℝ) ^ 2 * ε ^ 2)
        = (ε ^ 2)⁻¹ * ((n : ℝ)⁻¹ * ((n : ℝ)⁻¹ * ∑ j : Fin n, y n w j ^ 2)) := by
          field_simp
      _ ≤ (ε ^ 2)⁻¹ * ((n : ℝ)⁻¹ * B n w) := by gcongr
  have hP : ∀ n, (νH.prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) (S n) =
      ∫⁻ w, (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) {v | (w, v) ∈ S n} ∂νH :=
    fun n => Measure.prod_apply (hS_meas n)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_lintegral_min_one_ofReal hb0) (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [hP n]
  exact lintegral_mono fun w => hsec n hn w

end NTK

end
