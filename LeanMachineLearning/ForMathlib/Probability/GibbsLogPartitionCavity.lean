/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsLogPartition
public import LeanMachineLearning.ForMathlib.Probability.GibbsCavityPath

/-!
# The derivative of the expected log-partition function along an interpolation

The log-partition companion of `GibbsCavityPath.lean`: for the energy
`D + ∑ₖ sₖ(r) Zₖ Xₖ + ∑ⱼ cⱼ(r) X'ⱼ` with `Z` centered jointly Gaussian,
`d/dr 𝔼 log ∫ e^{energy} dμ = ∑ₖₗ sₖ' sₗ 𝔼[ZₖZₗ] 𝔼(⟨XₖXₗ⟩ - ⟨Xₖ⟩⟨Xₗ⟩) + ∑ⱼ cⱼ' 𝔼⟨X'ⱼ⟩`.
This is the computation behind Eq. (1.393) of Talagrand's book.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped BigOperators

namespace MeasureTheory

variable {α K Ks : Type*} [MeasurableSpace α] [Fintype K] [Fintype Ks]
  {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ]

/-- **The derivative of the expected log-partition function along a Gaussian interpolation.**
`R Y z` is the Gibbs average of `Y` for the parameters `z : K ⊕ Ks → ℝ`. -/
theorem hasDerivAt_integral_log_partition_cavity_path {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : α → ℝ} {X : K → α → ℝ} {Xs : Ks → α → ℝ}
    {Eb B : ℝ} (R : (α → ℝ) → (K ⊕ Ks → ℝ) → ℝ)
    (hR : ∀ Y' z, R Y' z = (∫ a, Y' a * Real.exp (D a + ∑ k, z k * Sum.elim X Xs k a) ∂μ) /
      ∫ a, Real.exp (D a + ∑ k, z k * Sum.elim X Xs k a) ∂μ)
    (hD : Measurable D) (hX : ∀ k, Measurable (X k)) (hXs : ∀ j, Measurable (Xs j))
    (hB : 0 ≤ B) (hDb : ∀ a, |D a| ≤ Eb) (hXb : ∀ k a, |X k a| ≤ B)
    (hXsb : ∀ j a, |Xs j a| ≤ B)
    {Z : K → Ω → ℝ} (hZ : HasGaussianLaw (fun ω k => Z k ω) P) (hZm : ∀ k, Measurable (Z k))
    (hmean : ∀ k, ∫ ω, Z k ω ∂P = 0)
    {s s' : K → ℝ → ℝ} {c c' : Ks → ℝ → ℝ} {t δ C : ℝ} (hδ : 0 < δ)
    (hs : ∀ k, ∀ r ∈ Metric.ball t δ, HasDerivAt (s k) (s' k r) r)
    (hc : ∀ j, ∀ r ∈ Metric.ball t δ, HasDerivAt (c j) (c' j r) r)
    (hsC : ∀ k, ∀ r ∈ Metric.ball t δ, |s' k r| ≤ C)
    (hcC : ∀ j, ∀ r ∈ Metric.ball t δ, |c' j r| ≤ C)
    (hsz : ∀ k, s' k t = 0 ∨ s k t ≠ 0) :
    HasDerivAt (fun r => ∫ ω, Real.log (∫ a, Real.exp (D a + ∑ l : K ⊕ Ks,
        Sum.elim (fun k => s k r * Z k ω) (fun j => c j r) l * Sum.elim X Xs l a) ∂μ) ∂P)
      (∑ k, ∑ l, s' k t * s l t * (∫ ω, Z k ω * Z l ω ∂P) *
          ∫ ω, (R (fun a => X k a * X l a) (Sum.elim (fun k => s k t * Z k ω) (fun j => c j t)) -
            R (X k) (Sum.elim (fun k => s k t * Z k ω) (fun j => c j t)) *
              R (X l) (Sum.elim (fun k => s k t * Z k ω) (fun j => c j t))) ∂P +
        ∑ j, c' j t * ∫ ω, R (Xs j) (Sum.elim (fun k => s k t * Z k ω) (fun j => c j t)) ∂P) t := by
  classical
  set zp : ℝ → Ω → K ⊕ Ks → ℝ := fun r ω => Sum.elim (fun k => s k r * Z k ω) (fun j => c j r)
    with hzp
  set Xall : K ⊕ Ks → α → ℝ := Sum.elim X Xs with hXall
  have hXallm : ∀ l, Measurable (Xall l) := by
    exact Sum.forall.2 ⟨hX, hXs⟩
  have hXallb : ∀ l a, |Xall l a| ≤ B := by
    exact Sum.forall.2 ⟨hXb, hXsb⟩
  have hint : ∀ k, Integrable (fun ω => |Z k ω|) P := fun k => ((hZ.eval k).integrable).norm
  have hg : Integrable (fun ω => C * (1 + ∑ k, |Z k ω|)) P :=
    ((integrable_const 1).add (integrable_finsetSum _ fun k _ => hint k)).const_mul C
  have hstep1 := hasDerivAt_integral_log_partition_path (μ := μ) (P := P) (K := K ⊕ Ks)
    (X := Xall) (D := D) hD hXallm hB hDb hXallb
    (z := zp) (z' := fun r ω => Sum.elim (fun k => s' k r * Z k ω) (fun j => c' j r))
    (t := t) (δ := δ) hδ
    (fun ω r hr => by
      rw [hasDerivAt_pi]
      intro l
      rcases l with k | j
      · simpa [hzp] using (hs k r hr).mul_const (Z k ω)
      · simpa [hzp] using hc j r hr)
    (fun r => by
      refine measurable_pi_iff.2 fun l => ?_
      rcases l with k | j
      · simpa [hzp] using (hZm k).const_mul (s k r)
      · simp [hzp])
    (by
      refine measurable_pi_iff.2 fun l => ?_
      rcases l with k | j
      · simpa using (hZm k).const_mul (s' k t)
      · simp)
    (fun l => by
      rcases l with k | j
      · simpa [hzp] using ((hZ.eval k).integrable).const_mul (s k t)
      · exact integrable_const (c j t))
    hg
    (fun ω r hr l => by
      rcases l with k | j
      · simp only [Sum.elim_inl, abs_mul]
        calc |s' k r| * |Z k ω| ≤ C * |Z k ω| :=
              mul_le_mul_of_nonneg_right (hsC k r hr) (abs_nonneg _)
          _ ≤ C * (1 + ∑ k, |Z k ω|) := by
              have hC0 : 0 ≤ C := (abs_nonneg _).trans (hsC k r hr)
              refine mul_le_mul_of_nonneg_left ?_ hC0
              have := Finset.single_le_sum (f := fun k => |Z k ω|) (fun _ _ => abs_nonneg _)
                (Finset.mem_univ k)
              linarith
      · simp only [Sum.elim_inr]
        have hC0 : 0 ≤ C := (abs_nonneg _).trans (hcC j r hr)
        calc |c' j r| ≤ C := hcC j r hr
          _ ≤ C * (1 + ∑ k, |Z k ω|) := by
              have : 0 ≤ ∑ k, |Z k ω| := Finset.sum_nonneg fun _ _ => abs_nonneg _
              nlinarith)
  refine hstep1.congr_deriv ?_
  set zt : Ω → K ⊕ Ks → ℝ := fun ω => zp t ω with hzt
  have hztm : Measurable zt := by
    refine measurable_pi_iff.2 fun l => ?_
    rcases l with k | j
    · simpa [hzt, hzp] using (hZm k).const_mul (s k t)
    · simp [hzt, hzp]
  have hcont : ∀ l, Continuous (R (Xall l)) := fun l =>
    continuous_gibbs_ratio_linear (μ := μ) (K := K ⊕ Ks) (X := Xall) R hR hD hXallm
      (hXallm l) hB hB hDb hXallb (hXallb l)
  have hRb : ∀ l z, |R (Xall l) z| ≤ B := fun l z0 => by
    rw [hR]
    exact abs_gibbs_ratio_le (K := K ⊕ Ks) (X := Xall) hD hXallm hDb hXallb (hXallb l) z0
  have hRm : ∀ l, Measurable fun ω => R (Xall l) (zt ω) := fun l => (hcont l).measurable.comp hztm
  have hpt : ∀ ω, ∑ l : K ⊕ Ks, Sum.elim (fun k => s' k t * Z k ω) (fun j => c' j t) l *
        ((∫ a, Xall l a * Real.exp (D a + ∑ k, zp t ω k * Xall k a) ∂μ) /
          ∫ a, Real.exp (D a + ∑ k, zp t ω k * Xall k a) ∂μ) =
      ∑ k, s' k t * Z k ω * R (X k) (zt ω) + ∑ j, c' j t * R (Xs j) (zt ω) := by
    intro ω
    rw [Fintype.sum_sum_type]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [hR]; rfl
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [hR]; rfl
  have hintk : ∀ k, Integrable (fun ω => s' k t * Z k ω * R (X k) (zt ω)) P := by
    intro k
    refine ((hint k).const_mul (|s' k t| * B)).mono'
      (((hZm k).const_mul _).mul (hRm (Sum.inl k))).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |s' k t| * |Z k ω| * |R (X k) (zt ω)| ≤ |s' k t| * |Z k ω| * B :=
          mul_le_mul_of_nonneg_left (hRb (Sum.inl k) _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = |s' k t| * B * |Z k ω| := by ring
  have hintj : ∀ j, Integrable (fun ω => c' j t * R (Xs j) (zt ω)) P := by
    intro j
    refine (integrable_const (|c' j t| * B)).mono'
      ((hRm (Sum.inr j)).const_mul _).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hRb (Sum.inr j) _) (abs_nonneg _)
  rw [integral_congr_ae (ae_of_all _ hpt),
    integral_add (integrable_finsetSum _ fun k _ => hintk k)
      (integrable_finsetSum _ fun j _ => hintj j),
    integral_finsetSum _ fun k _ => hintk k, integral_finsetSum _ fun j _ => hintj j]
  congr 1
  · set Zt : K → Ω → ℝ := fun k ω => s k t * Z k ω with hZt
    have hZtG : HasGaussianLaw (fun ω k => Zt k ω) P := by
      have := hZ.map (F := K → ℝ)
        (ContinuousLinearMap.pi fun k => s k t • ContinuousLinearMap.proj k)
      convert this using 1
      funext ω k
      simp [hZt]
    set Dt : α → ℝ := fun a => D a + ∑ j, c j t * Xs j a with hDt
    have hDtm : Measurable Dt := by
      refine hD.add (Finset.measurable_sum _ fun j _ => (hXs j).const_mul _)
    have hDtb : ∀ a, |Dt a| ≤ Eb + ∑ j, |c j t| * B := fun a => by
      exact abs_add_sum_mul_le _ (fun j => c j t) _ (hDb a) (fun j => hXsb j a)
    set Rt : (α → ℝ) → (K → ℝ) → ℝ := fun Y' w => (∫ a, Y' a * Real.exp (Dt a +
      ∑ k, w k * X k a) ∂μ) / ∫ a, Real.exp (Dt a + ∑ k, w k * X k a) ∂μ with hRt
    have hexp : ∀ ω a, Dt a + ∑ k, Zt k ω * X k a = D a + ∑ l, zt ω l * Xall l a := by
      intro ω a
      simp only [hDt, hzt, hzp, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hXall, hZt]
      ring
    have hbridge : ∀ Y' ω, Rt Y' (fun k => Zt k ω) = R Y' (zt ω) := by
      intro Y' ω
      rw [hR, hRt]
      simp only [hexp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rcases hsz k with h0 | hne
    · simp [h0]
    have hibp := integral_mul_gibbs_ratio_eq_sum (μ := μ) (D := Dt) (X := X) (Y := X k)
      (Z := Zt) (B := B) (M := B) (Eb := Eb + ∑ j, |c j t| * B) Rt (fun _ _ => rfl) hZtG
      (fun i => by simp only [hZt, integral_const_mul, hmean i, mul_zero]) k hDtm hX (hX k) hB hB
      hDtb hXb (hXb k)
    simp only [hbridge] at hibp
    have hZZ : ∀ l, ∫ ω, Zt k ω * Zt l ω ∂P = s k t * s l t * ∫ ω, Z k ω * Z l ω ∂P := by
      intro l
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun ω => by simp only [hZt]; ring)
    calc ∫ ω, s' k t * Z k ω * R (X k) (zt ω) ∂P
        = (s' k t / s k t) * ∫ ω, Zt k ω * R (X k) (zt ω) ∂P := by
          rw [← integral_const_mul]
          refine integral_congr_ae (ae_of_all _ fun ω => ?_)
          simp only [hZt]
          field_simp
      _ = (s' k t / s k t) * ∑ l, (∫ ω, Zt k ω * Zt l ω ∂P) *
            ∫ ω, (R (fun a => X k a * X l a) (zt ω) - R (X k) (zt ω) * R (X l) (zt ω)) ∂P := by
          rw [hibp]
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hZZ l]
          field_simp
          rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]

end MeasureTheory
