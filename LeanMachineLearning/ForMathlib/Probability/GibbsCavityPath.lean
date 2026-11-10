/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsIBPLinear
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The derivative of an interpolating Gibbs average (the abstract form of Talagrand's (1.376))

Consider a Gibbs measure on an arbitrary base space with energy
`∑ₖ sₖ(t) Zₖ Xₖ + ∑ⱼ cⱼ(t) X'ⱼ`, where `Z` is a centered jointly Gaussian vector (singular
covariance allowed), `sₖ`, `cⱼ` are differentiable scalar functions and the features are bounded.
Then `d/dt 𝔼 ⟨f⟩_t` is the sum over `k, l` of `sₖ'(t) sₗ(t) 𝔼[ZₖZₗ]` times the expectation of the
Gibbs covariance derivative `⟨Yₖ Xₗ⟩ - ⟨Yₖ⟩⟨Xₗ⟩`, where `⟨Yₖ⟩ = ⟨f Xₖ⟩ - ⟨f⟩⟨Xₖ⟩`, plus the
deterministic part `∑ⱼ cⱼ'(t) 𝔼[⟨f X'ⱼ⟩ - ⟨f⟩⟨X'ⱼ⟩]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped BigOperators

namespace MeasureTheory

variable {α K Ks : Type*} [MeasurableSpace α] [Fintype K] [Fintype Ks]
  {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ]

/-- **The abstract cavity derivative** (the shape of Proposition 1.12.4 before the replica
bookkeeping). `R Y z` is the Gibbs average of `Y` for the parameters `z : K ⊕ Ks → ℝ`. -/
theorem hasDerivAt_integral_gibbs_cavity_path {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : α → ℝ} {X : K → α → ℝ} {Xs : Ks → α → ℝ}
    {f : α → ℝ} {Y : K → α → ℝ} {Eb B M M' : ℝ}
    (R : (α → ℝ) → (K ⊕ Ks → ℝ) → ℝ)
    (hR : ∀ Y' z, R Y' z = (∫ a, Y' a * Real.exp (D a + ∑ k, z k * Sum.elim X Xs k a) ∂μ) /
      ∫ a, Real.exp (D a + ∑ k, z k * Sum.elim X Xs k a) ∂μ)
    (hD : Measurable D) (hX : ∀ k, Measurable (X k)) (hXs : ∀ j, Measurable (Xs j))
    (hf : Measurable f) (hY : ∀ k, Measurable (Y k))
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hDb : ∀ a, |D a| ≤ Eb) (hXb : ∀ k a, |X k a| ≤ B) (hXsb : ∀ j a, |Xs j a| ≤ B)
    (hfb : ∀ a, |f a| ≤ M) (hYb : ∀ k a, |Y k a| ≤ M')
    (hYk : ∀ k z, R (Y k) z = R (fun a => f a * X k a) z - R f z * R (X k) z)
    {Z : K → Ω → ℝ} (hZ : HasGaussianLaw (fun ω k => Z k ω) P) (hZm : ∀ k, Measurable (Z k))
    (hmean : ∀ k, ∫ ω, Z k ω ∂P = 0)
    {s s' : K → ℝ → ℝ} {c c' : Ks → ℝ → ℝ} {t δ C : ℝ} (hδ : 0 < δ)
    (hs : ∀ k, ∀ r ∈ Metric.ball t δ, HasDerivAt (s k) (s' k r) r)
    (hc : ∀ j, ∀ r ∈ Metric.ball t δ, HasDerivAt (c j) (c' j r) r)
    (hsC : ∀ k, ∀ r ∈ Metric.ball t δ, |s' k r| ≤ C)
    (hcC : ∀ j, ∀ r ∈ Metric.ball t δ, |c' j r| ≤ C)
    (hsz : ∀ k, s' k t = 0 ∨ s k t ≠ 0) :
    HasDerivAt (fun r => ∫ ω, R f (Sum.elim (fun k => s k r * Z k ω) (fun j => c j r)) ∂P)
      (∑ k, ∑ l, s' k t * s l t * (∫ ω, Z k ω * Z l ω ∂P) *
          ∫ ω, (R (fun a => Y k a * X l a) (Sum.elim (fun k => s k t * Z k ω) (fun j => c j t)) -
            R (Y k) (Sum.elim (fun k => s k t * Z k ω) (fun j => c j t)) *
              R (X l) (Sum.elim (fun k => s k t * Z k ω) (fun j => c j t))) ∂P +
        ∑ j, c' j t * ∫ ω, (R (fun a => f a * Xs j a)
            (Sum.elim (fun k => s k t * Z k ω) (fun j => c j t)) -
          R f (Sum.elim (fun k => s k t * Z k ω) (fun j => c j t)) *
            R (Xs j) (Sum.elim (fun k => s k t * Z k ω) (fun j => c j t))) ∂P) t := by
  classical
  -- notation for the path
  set zp : ℝ → Ω → K ⊕ Ks → ℝ := fun r ω => Sum.elim (fun k => s k r * Z k ω) (fun j => c j r)
    with hzp
  set Xall : K ⊕ Ks → α → ℝ := Sum.elim X Xs with hXall
  have hXallm : ∀ l, Measurable (Xall l) := by
    intro l; rcases l with k | j
    · exact hX k
    · exact hXs j
  have hXallb : ∀ l a, |Xall l a| ≤ B := by
    intro l a; rcases l with k | j
    · exact hXb k a
    · exact hXsb j a
  -- Step 1: derivative of the expected Gibbs average along the path
  have hint : ∀ k, Integrable (fun ω => |Z k ω|) P := fun k => ((hZ.eval k).integrable).norm
  have hg : Integrable (fun ω => C * (1 + ∑ k, |Z k ω|)) P :=
    ((integrable_const 1).add (integrable_finsetSum _ fun k _ => hint k)).const_mul C
  have hstep1 := hasDerivAt_integral_gibbs_ratio_path (μ := μ) (P := P) (K := K ⊕ Ks)
    (X := Xall) (Y := f) (D := D) R hR hD hXallm hf hB hM hDb hXallb hfb
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
  -- the path at time `t`, and its covariance terms
  set zt : Ω → K ⊕ Ks → ℝ := fun ω => zp t ω with hzt
  have hztm : Measurable zt := by
    refine measurable_pi_iff.2 fun l => ?_
    rcases l with k | j
    · simpa [hzt, hzp] using (hZm k).const_mul (s k t)
    · simp [hzt, hzp]
  have hMB : 0 ≤ M * B := mul_nonneg hM hB
  have hXallm' : ∀ l, Measurable fun a => f a * Xall l a := fun l => hf.mul (hXallm l)
  have hfXb : ∀ l a, |f a * Xall l a| ≤ M * B := fun l a => by
    rw [abs_mul]; exact mul_le_mul (hfb a) (hXallb l a) (abs_nonneg _) hM
  have hcont : ∀ (Y' : α → ℝ) (M'' : ℝ), 0 ≤ M'' → Measurable Y' → (∀ a, |Y' a| ≤ M'') →
      Continuous (R Y') := fun Y' M'' hM'' hY' hY'b =>
    continuous_gibbs_ratio_linear (μ := μ) (K := K ⊕ Ks) (X := Xall) R hR hD hXallm hY' hB hM''
      hDb hXallb hY'b
  have hRb : ∀ (Y' : α → ℝ) (M'' : ℝ), (∀ a, |Y' a| ≤ M'') → ∀ z, |R Y' z| ≤ M'' := by
    intro Y' M'' hY'b z0
    rw [hR]
    exact abs_gibbs_ratio_le (K := K ⊕ Ks) (X := Xall) hD hXallm hDb hXallb hY'b z0
  have hmeasR : ∀ (Y' : α → ℝ) (M'' : ℝ), 0 ≤ M'' → Measurable Y' → (∀ a, |Y' a| ≤ M'') →
      Measurable fun ω => R Y' (zt ω) := fun Y' M'' hM'' hY' hY'b =>
    (hcont Y' M'' hM'' hY' hY'b).measurable.comp hztm
  set cov : K ⊕ Ks → Ω → ℝ := fun l ω => R (fun a => f a * Xall l a) (zt ω) -
    R f (zt ω) * R (Xall l) (zt ω) with hcov
  have hcovm : ∀ l, Measurable (cov l) := fun l =>
    (hmeasR _ _ hMB (hXallm' l) (hfXb l)).sub
      ((hmeasR f M hM hf hfb).mul (hmeasR (Xall l) B hB (hXallm l) (hXallb l)))
  have hcovb : ∀ l ω, |cov l ω| ≤ 2 * M * B := fun l ω => by
    calc |cov l ω| ≤ |R (fun a => f a * Xall l a) (zt ω)| + |R f (zt ω)| * |R (Xall l) (zt ω)| :=
          (abs_sub _ _).trans (by rw [abs_mul])
      _ ≤ M * B + M * B := add_le_add (hRb _ _ (hfXb l) _)
          (mul_le_mul (hRb f M hfb _) (hRb (Xall l) B (hXallb l) _) (abs_nonneg _) hM)
      _ = 2 * M * B := by ring
  -- splitting the sum over `K ⊕ Ks`
  have hsplit : ∀ ω, ∑ l : K ⊕ Ks, Sum.elim (fun k => s' k t * Z k ω) (fun j => c' j t) l *
        cov l ω =
      ∑ k, s' k t * Z k ω * cov (Sum.inl k) ω + ∑ j, c' j t * cov (Sum.inr j) ω := by
    intro ω
    rw [Fintype.sum_sum_type]
    rfl
  have hintk : ∀ k, Integrable (fun ω => s' k t * Z k ω * cov (Sum.inl k) ω) P := by
    intro k
    refine ((hint k).const_mul (|s' k t| * (2 * M * B))).mono'
      (((hZm k).const_mul _).mul (hcovm _)).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    calc |s' k t| * |Z k ω| * |cov (Sum.inl k) ω| ≤ |s' k t| * |Z k ω| * (2 * M * B) :=
          mul_le_mul_of_nonneg_left (hcovb _ _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = |s' k t| * (2 * M * B) * |Z k ω| := by ring
  have hintj : ∀ j, Integrable (fun ω => c' j t * cov (Sum.inr j) ω) P := by
    intro j
    refine (integrable_const (|c' j t| * (2 * M * B))).mono'
      ((hcovm _).const_mul _).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hcovb _ _) (abs_nonneg _)
  rw [integral_congr_ae (ae_of_all _ hsplit),
    integral_add (integrable_finsetSum _ fun k _ => hintk k)
      (integrable_finsetSum _ fun j _ => hintj j),
    integral_finsetSum _ fun k _ => hintk k, integral_finsetSum _ fun j _ => hintj j]
  congr 1
  · -- the Gaussian integration by parts at the frozen time `t`
    set Zt : K → Ω → ℝ := fun k ω => s k t * Z k ω with hZt
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
      refine (abs_add_le _ _).trans (add_le_add (hDb a) ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hXsb j a) (abs_nonneg _)
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
    have hibp := integral_mul_gibbs_ratio_eq_sum (μ := μ) (D := Dt) (X := X) (Y := Y k)
      (Z := Zt) (B := B) (M := M') (Eb := Eb + ∑ j, |c j t| * B) Rt (fun _ _ => rfl) hZtG
      (fun i => by simp only [hZt, integral_const_mul, hmean i, mul_zero]) k hDtm hX (hY k) hB hM'
      hDtb hXb (hYb k)
    simp only [hbridge] at hibp
    have hcovk : ∀ ω, cov (Sum.inl k) ω = R (Y k) (zt ω) := fun ω => (hYk k (zt ω)).symm
    have hZZ : ∀ l, ∫ ω, Zt k ω * Zt l ω ∂P = s k t * s l t * ∫ ω, Z k ω * Z l ω ∂P := by
      intro l
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun ω => by simp only [hZt]; ring)
    calc ∫ ω, s' k t * Z k ω * cov (Sum.inl k) ω ∂P
        = (s' k t / s k t) * ∫ ω, Zt k ω * R (Y k) (zt ω) ∂P := by
          rw [← integral_const_mul]
          refine integral_congr_ae (ae_of_all _ fun ω => ?_)
          simp only [hcovk, hZt]
          field_simp
      _ = (s' k t / s k t) * ∑ l, (∫ ω, Zt k ω * Zt l ω ∂P) *
            ∫ ω, (R (fun a => Y k a * X l a) (zt ω) - R (Y k) (zt ω) * R (X l) (zt ω)) ∂P := by
          rw [hibp]
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hZZ l]
          field_simp
          rfl
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    rfl

end MeasureTheory
