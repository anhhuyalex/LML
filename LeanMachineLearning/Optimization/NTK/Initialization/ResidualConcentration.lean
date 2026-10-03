/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Initialization.GaussianConditioning
public import LeanMachineLearning.Optimization.NTK.Initialization.DeepRecursion
public import LeanMachineLearning.Optimization.NTK.Foundations.GramProjector
public import LeanMachineLearning.Optimization.NTK.Foundations.TendstoInMeasureUtil

/-!
# Convergence in Measure of Residual Gaussian Forms

Sequence-level (`n → ∞`) versions of the conditional Chebyshev bounds of
`Initialization/GaussianConditioning.lean`, stated over an arbitrary probability space `(Ω, μ)`
equipped, for each width `n`, with a measure-preserving coordinate map
`Ψ n : Ω → Z × (Fin n → Fin n → ℝ)` onto `ρ.prod (𝒩(0,1)^{n×n})` (past `z ∈ Z`, Gaussian layer
`V`). The projector is the Gram projector `P = gramProjector (Φ n z)` of past features.

* `tendsto_residualQuadForm`: for vectors `u, v` depending on `(V P, z)` and a past-measurable
  matrix `A`, the normalized residual quadratic form
  `n⁻² uᵀ (V Pᗮ) A (V Pᗮ)ᵀ v` is within `ε` of its conditional mean `n⁻² (u ⬝ᵥ v) tr(Pᗮ A Pᗮ)`
  with probability `→ 1`, provided `n⁻¹‖u‖²`, `n⁻¹‖v‖²`, `n⁻¹‖A‖_F²` converge in measure.
* `tendsto_residualLinearForm`: `n⁻¹ √(n⁻¹) u ⬝ᵥ ((V Pᗮ) b) → 0` in measure, provided `n⁻¹‖u‖²`
  and `n⁻¹‖b‖²` converge in measure.
-/

@[expose]
public section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped ENNReal Matrix

namespace NTK

/-- A real sequence of random variables is bounded above by a sequence converging in measure. This
is the form of "tightness" needed for the Chebyshev bounds (it is implied by convergence in
measure, and also holds for quantities dominated by averages of fourth powers). -/
def BddByConv {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω) (q : ℕ → Ω → ℝ) : Prop :=
  ∃ (B : ℕ → Ω → ℝ) (c : ℝ), (∀ n ω, q n ω ≤ B n ω) ∧
    TendstoInMeasure μ B atTop (fun _ => c)

lemma BddByConv.of_tendstoInMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {q : ℕ → Ω → ℝ} {c : ℝ} (h : TendstoInMeasure μ q atTop (fun _ => c)) : BddByConv μ q :=
  ⟨q, c, fun _ _ => le_rfl, h⟩

section prelim

variable {Z : Type*} [MeasurableSpace Z] {n m : ℕ}

lemma measurable_gramProjector {Φ : Z → Matrix (Fin n) (Fin m) ℝ} (hΦ : Measurable Φ) :
    Measurable fun z => gramProjector (Φ z) := by
  unfold gramProjector
  have hT : Measurable fun z => (Φ z)ᵀ := measurable_matrix_transpose hΦ
  exact measurable_matrix_mul (measurable_matrix_mul hΦ
    (measurable_matrix_nonsing_inv.comp (measurable_matrix_mul hT hΦ))) hT

/-- `u` evaluated at the projected weight `V P` and the past: the argument of the conditional
Chebyshev bounds. -/
noncomputable def atProj (Φ : Z → Matrix (Fin n) (Fin m) ℝ)
    (u : Matrix (Fin n) (Fin n) ℝ × Z → Fin n → ℝ) (q : Z × (Fin n → Fin n → ℝ)) :
    Fin n → ℝ :=
  u (Matrix.of q.2 * gramProjector (Φ q.1), q.1)

lemma measurable_atProj {Φ : Z → Matrix (Fin n) (Fin m) ℝ} (hΦ : Measurable Φ)
    {u : Matrix (Fin n) (Fin n) ℝ × Z → Fin n → ℝ} (hu : Measurable u) :
    Measurable (atProj Φ u) := by
  refine hu.comp (Measurable.prodMk ?_ measurable_fst)
  exact measurable_matrix_mul measurable_snd
    ((measurable_gramProjector hΦ).comp measurable_fst)

/-- If `f n → c` in measure then `n⁻¹ f n → 0`. -/
lemma tendstoInMeasure_inv_nat_mul {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {f : ℕ → Ω → ℝ} {c : ℝ} (hf : TendstoInMeasure μ f atTop (fun _ => c)) :
    TendstoInMeasure μ (fun (n : ℕ) (ω : Ω) => (n : ℝ)⁻¹ * f n ω) atTop (fun _ => 0) := by
  have h := tendstoInMeasure_mul
    (tendstoInMeasure_of_tendsto (μ := μ)
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)) hf
  simpa using h

end prelim

section quad

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] {m : ℕ}

/-- **Residual quadratic form concentrates around its conditional mean.** -/
theorem tendsto_residualQuadForm (μ : Measure Ω) [IsProbabilityMeasure μ] (ρ : Measure Z)
    (Ψ : ∀ n : ℕ, Ω → Z × (Fin n → Fin n → ℝ))
    (hΨ : ∀ n, MeasurePreserving (Ψ n) μ (ρ.prod (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin
        n => gaussianReal 0 1)))
    (Φ : ∀ n : ℕ, Z → Matrix (Fin n) (Fin m) ℝ) (hΦ : ∀ n, Measurable (Φ n))
    (A : ∀ n : ℕ, Z → Matrix (Fin n) (Fin n) ℝ) (hA : ∀ n, Measurable (A n))
    (u v : ∀ n : ℕ, Matrix (Fin n) (Fin n) ℝ × Z → Fin n → ℝ)
    (hu : ∀ n, Measurable (u n)) (hv : ∀ n, Measurable (v n))
    (hcu : BddByConv μ (fun (n : ℕ) (ω : Ω) =>
      (n : ℝ)⁻¹ * (atProj (Φ n) (u n) (Ψ n ω) ⬝ᵥ atProj (Φ n) (u n) (Ψ n ω))))
    (hcv : BddByConv μ (fun (n : ℕ) (ω : Ω) =>
      (n : ℝ)⁻¹ * (atProj (Φ n) (v n) (Ψ n ω) ⬝ᵥ atProj (Φ n) (v n) (Ψ n ω))))
    (hcA : BddByConv μ (fun (n : ℕ) (ω : Ω) =>
      (n : ℝ)⁻¹ * ∑ k, ∑ l, A n (Ψ n ω).1 k l ^ 2))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => μ {ω | ε ≤ |((n : ℝ) ^ 2)⁻¹ *
        (atProj (Φ n) (u n) (Ψ n ω) ⬝ᵥ
          ((Matrix.of (Ψ n ω).2 * (1 - gramProjector (Φ n (Ψ n ω).1)) *
              A n (Ψ n ω).1 *
            (Matrix.of (Ψ n ω).2 * (1 - gramProjector (Φ n (Ψ n ω).1)))ᵀ) *ᵥ
            atProj (Φ n) (v n) (Ψ n ω))) -
      ((n : ℝ) ^ 2)⁻¹ * ((atProj (Φ n) (u n) (Ψ n ω) ⬝ᵥ atProj (Φ n) (v n) (Ψ n ω)) *
        ((1 - gramProjector (Φ n (Ψ n ω).1)) * A n (Ψ n ω).1 *
          (1 - gramProjector (Φ n (Ψ n ω).1))).trace)|})
      atTop (nhds 0) := by
  classical
  obtain ⟨Bu, cu, hBu, hBuc⟩ := hcu
  obtain ⟨Bv, cv, hBv, hBvc⟩ := hcv
  obtain ⟨BA, cA, hBA, hBAc⟩ := hcA
  set bq : ∀ n : ℕ, Z × (Fin n → Fin n → ℝ) → ℝ := fun n q =>
    2 * ((n : ℝ)⁻¹ * (atProj (Φ n) (u n) q ⬝ᵥ atProj (Φ n) (u n) q)) *
      ((n : ℝ)⁻¹ * (atProj (Φ n) (v n) q ⬝ᵥ atProj (Φ n) (v n) q)) *
      ((n : ℝ)⁻¹ * ∑ k, ∑ l, A n q.1 k l ^ 2) / ((n : ℝ) * ε ^ 2) with hbq
  have hprod := tendstoInMeasure_mul (tendstoInMeasure_mul hBuc hBvc) hBAc
  have hscaled := tendstoInMeasure_inv_nat_mul hprod
  have hb0 : TendstoInMeasure μ (fun (n : ℕ) (ω : Ω) =>
      (2 * (ε ^ 2)⁻¹) * ((n : ℝ)⁻¹ * (Bu n ω * Bv n ω * BA n ω))) atTop (fun _ => 0) := by
    have h := tendstoInMeasure_mul (tendstoInMeasure_const (μ := μ) (2 * (ε ^ 2)⁻¹)) hscaled
    rw [mul_zero] at h
    exact h
  have hle : ∀ (n : ℕ) (ω : Ω), bq n (Ψ n ω) ≤
      (2 * (ε ^ 2)⁻¹) * ((n : ℝ)⁻¹ * (Bu n ω * Bv n ω * BA n ω)) := by
    intro n ω
    have hu0 : 0 ≤ (n : ℝ)⁻¹ * (atProj (Φ n) (u n) (Ψ n ω) ⬝ᵥ atProj (Φ n) (u n) (Ψ n ω)) :=
      mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg n)) (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
    have hv0 : 0 ≤ (n : ℝ)⁻¹ * (atProj (Φ n) (v n) (Ψ n ω) ⬝ᵥ atProj (Φ n) (v n) (Ψ n ω)) :=
      mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg n)) (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
    have hA0 : 0 ≤ (n : ℝ)⁻¹ * ∑ k, ∑ l, A n (Ψ n ω).1 k l ^ 2 :=
      mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg n))
        (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hBu0 := hu0.trans (hBu n ω)
    have hBv0 := hv0.trans (hBv n ω)
    have hmul : (n : ℝ)⁻¹ * (atProj (Φ n) (u n) (Ψ n ω) ⬝ᵥ atProj (Φ n) (u n) (Ψ n ω)) *
        ((n : ℝ)⁻¹ * (atProj (Φ n) (v n) (Ψ n ω) ⬝ᵥ atProj (Φ n) (v n) (Ψ n ω))) *
        ((n : ℝ)⁻¹ * ∑ k, ∑ l, A n (Ψ n ω).1 k l ^ 2) ≤ Bu n ω * Bv n ω * BA n ω :=
      mul_le_mul (mul_le_mul (hBu n ω) (hBv n ω) hv0 hBu0) (hBA n ω) hA0 (mul_nonneg hBu0 hBv0)
    have heq : bq n (Ψ n ω) = (2 * (ε ^ 2)⁻¹) * ((n : ℝ)⁻¹ *
        ((n : ℝ)⁻¹ * (atProj (Φ n) (u n) (Ψ n ω) ⬝ᵥ atProj (Φ n) (u n) (Ψ n ω)) *
        ((n : ℝ)⁻¹ * (atProj (Φ n) (v n) (Ψ n ω) ⬝ᵥ atProj (Φ n) (v n) (Ψ n ω))) *
        ((n : ℝ)⁻¹ * ∑ k, ∑ l, A n (Ψ n ω).1 k l ^ 2))) := by
      simp only [hbq]; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmul
      (inv_nonneg.2 (Nat.cast_nonneg n))) (by positivity)
  have hmain : ∀ n : ℕ, 0 < n → μ {ω | ε ≤ |((n : ℝ) ^ 2)⁻¹ *
        (atProj (Φ n) (u n) (Ψ n ω) ⬝ᵥ
          ((Matrix.of (Ψ n ω).2 * (1 - gramProjector (Φ n (Ψ n ω).1)) *
              A n (Ψ n ω).1 *
            (Matrix.of (Ψ n ω).2 * (1 - gramProjector (Φ n (Ψ n ω).1)))ᵀ) *ᵥ
            atProj (Φ n) (v n) (Ψ n ω))) -
      ((n : ℝ) ^ 2)⁻¹ * ((atProj (Φ n) (u n) (Ψ n ω) ⬝ᵥ atProj (Φ n) (v n) (Ψ n ω)) *
        ((1 - gramProjector (Φ n (Ψ n ω).1)) * A n (Ψ n ω).1 *
          (1 - gramProjector (Φ n (Ψ n ω).1))).trace)|} ≤
      ∫⁻ ω, min 1 (ENNReal.ofReal ((2 * (ε ^ 2)⁻¹) *
        ((n : ℝ)⁻¹ * (Bu n ω * Bv n ω * BA n ω)))) ∂μ := by
    intro n hn
    have hPm : Measurable fun z => gramProjector (Φ n z) := measurable_gramProjector (hΦ n)
    have hcond := conditional_quadForm_chebyshev_normalized ρ n n hn
      (fun z => gramProjector (Φ n z)) (fun z => isOrthogonalProjection_gramProjector_all _) hPm
      (A n) (hA n) (u n) (v n) (hu n) (hv n) hε
    have hau := measurable_atProj (hΦ n) (hu n)
    have hav := measurable_atProj (hΦ n) (hv n)
    have hbm : Measurable (bq n) := by
      refine Measurable.div_const (((measurable_const.mul
        (measurable_const.mul (measurable_dotProduct hau hau))).mul
        (measurable_const.mul (measurable_dotProduct hav hav))).mul
        (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
          Finset.measurable_sum _ fun l _ =>
            (measurable_matrix_entry ((hA n).comp measurable_fst) k l).pow_const 2))) _
    have hg : Measurable fun q => min 1 (ENNReal.ofReal (bq n q)) :=
      measurable_const.min (ENNReal.measurable_ofReal.comp hbm)
    calc μ {ω | _} ≤ (μ.map (Ψ n)) _ := Measure.le_map_apply (hΨ n).measurable.aemeasurable _
      _ = (ρ.prod (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n =>
          gaussianReal 0 1)) _ := by rw [(hΨ n).map_eq]
      _ ≤ ∫⁻ q, min 1 (ENNReal.ofReal (bq n q)) ∂(ρ.prod (Measure.pi fun _ : Fin n => Measure.pi fun
          _ : Fin n => gaussianReal 0 1)) := hcond
      _ = ∫⁻ ω, min 1 (ENNReal.ofReal (bq n (Ψ n ω))) ∂μ := ((hΨ n).lintegral_comp hg).symm
      _ ≤ _ := lintegral_mono fun ω =>
        min_le_min_left _ (ENNReal.ofReal_le_ofReal (hle n ω))
  exact tendsto_measure_of_le_lintegral_min_one
    (Filter.eventually_atTop.2 ⟨1, fun n hn => hmain n hn⟩) hb0

end quad

section linear

variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z] {m : ℕ}

/-- **The residual linear form tends to zero.** -/
theorem tendsto_residualLinearForm (μ : Measure Ω) [IsProbabilityMeasure μ] (ρ : Measure Z)
    (Ψ : ∀ n : ℕ, Ω → Z × (Fin n → Fin n → ℝ))
    (hΨ : ∀ n, MeasurePreserving (Ψ n) μ (ρ.prod (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin
        n => gaussianReal 0 1)))
    (Φ : ∀ n : ℕ, Z → Matrix (Fin n) (Fin m) ℝ) (hΦ : ∀ n, Measurable (Φ n))
    (b : ∀ n : ℕ, Z → Fin n → ℝ) (hb : ∀ n, Measurable (b n))
    (u : ∀ n : ℕ, Matrix (Fin n) (Fin n) ℝ × Z → Fin n → ℝ) (hu : ∀ n, Measurable (u n))
    (hcu : BddByConv μ (fun (n : ℕ) (ω : Ω) =>
      (n : ℝ)⁻¹ * (atProj (Φ n) (u n) (Ψ n ω) ⬝ᵥ atProj (Φ n) (u n) (Ψ n ω))))
    (hcb : BddByConv μ (fun (n : ℕ) (ω : Ω) =>
      (n : ℝ)⁻¹ * (b n (Ψ n ω).1 ⬝ᵥ b n (Ψ n ω).1)))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => μ {ω | ε ≤ |((n : ℝ)⁻¹ * Real.sqrt ((n : ℝ)⁻¹)) *
        (atProj (Φ n) (u n) (Ψ n ω) ⬝ᵥ
          ((Matrix.of (Ψ n ω).2 * (1 - gramProjector (Φ n (Ψ n ω).1))) *ᵥ
            b n (Ψ n ω).1))|})
      atTop (nhds 0) := by
  classical
  obtain ⟨Bu, cu, hBu, hBuc⟩ := hcu
  obtain ⟨Bb, cb, hBb, hBbc⟩ := hcb
  set bq : ∀ n : ℕ, Z × (Fin n → Fin n → ℝ) → ℝ := fun n q =>
    ((n : ℝ)⁻¹ * (atProj (Φ n) (u n) q ⬝ᵥ atProj (Φ n) (u n) q)) *
      ((n : ℝ)⁻¹ * (b n q.1 ⬝ᵥ b n q.1)) / ((n : ℝ) * ε ^ 2) with hbq
  have hprod := tendstoInMeasure_mul hBuc hBbc
  have hscaled := tendstoInMeasure_inv_nat_mul hprod
  have hb0 : TendstoInMeasure μ (fun (n : ℕ) (ω : Ω) =>
      ((ε ^ 2)⁻¹) * ((n : ℝ)⁻¹ * (Bu n ω * Bb n ω))) atTop (fun _ => 0) := by
    have h := tendstoInMeasure_mul (tendstoInMeasure_const (μ := μ) ((ε ^ 2)⁻¹)) hscaled
    rw [mul_zero] at h
    exact h
  have hle : ∀ (n : ℕ) (ω : Ω), bq n (Ψ n ω) ≤ ((ε ^ 2)⁻¹) * ((n : ℝ)⁻¹ * (Bu n ω * Bb n ω)) := by
    intro n ω
    have hu0 : 0 ≤ (n : ℝ)⁻¹ * (atProj (Φ n) (u n) (Ψ n ω) ⬝ᵥ atProj (Φ n) (u n) (Ψ n ω)) :=
      mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg n)) (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
    have hb0' : 0 ≤ (n : ℝ)⁻¹ * (b n (Ψ n ω).1 ⬝ᵥ b n (Ψ n ω).1) :=
      mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg n)) (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
    have hBu0 := hu0.trans (hBu n ω)
    have hmul : (n : ℝ)⁻¹ * (atProj (Φ n) (u n) (Ψ n ω) ⬝ᵥ atProj (Φ n) (u n) (Ψ n ω)) *
        ((n : ℝ)⁻¹ * (b n (Ψ n ω).1 ⬝ᵥ b n (Ψ n ω).1)) ≤ Bu n ω * Bb n ω :=
      mul_le_mul (hBu n ω) (hBb n ω) hb0' hBu0
    have heq : bq n (Ψ n ω) = ((ε ^ 2)⁻¹) * ((n : ℝ)⁻¹ *
        ((n : ℝ)⁻¹ * (atProj (Φ n) (u n) (Ψ n ω) ⬝ᵥ atProj (Φ n) (u n) (Ψ n ω)) *
        ((n : ℝ)⁻¹ * (b n (Ψ n ω).1 ⬝ᵥ b n (Ψ n ω).1)))) := by
      simp only [hbq]; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmul
      (inv_nonneg.2 (Nat.cast_nonneg n))) (by positivity)
  have hmain : ∀ n : ℕ, 0 < n → μ {ω | ε ≤ |((n : ℝ)⁻¹ * Real.sqrt ((n : ℝ)⁻¹)) *
        (atProj (Φ n) (u n) (Ψ n ω) ⬝ᵥ
          ((Matrix.of (Ψ n ω).2 * (1 - gramProjector (Φ n (Ψ n ω).1))) *ᵥ
            b n (Ψ n ω).1))|} ≤
      ∫⁻ ω, min 1 (ENNReal.ofReal (((ε ^ 2)⁻¹) *
        ((n : ℝ)⁻¹ * (Bu n ω * Bb n ω)))) ∂μ := by
    intro n hn
    have hPm : Measurable fun z => gramProjector (Φ n z) := measurable_gramProjector (hΦ n)
    have hcond := conditional_linearForm_chebyshev_normalized ρ n n hn
      (fun z => gramProjector (Φ n z)) (fun z => isOrthogonalProjection_gramProjector_all _) hPm
      (b n) (hb n) (u n) (hu n) hε
    have hau := measurable_atProj (hΦ n) (hu n)
    have hbb : Measurable fun q : Z × (Fin n → Fin n → ℝ) => b n q.1 := (hb n).comp measurable_fst
    have hbm : Measurable (bq n) :=
      Measurable.div_const ((measurable_const.mul (measurable_dotProduct hau hau)).mul
        (measurable_const.mul (measurable_dotProduct hbb hbb))) _
    have hg : Measurable fun q => min 1 (ENNReal.ofReal (bq n q)) :=
      measurable_const.min (ENNReal.measurable_ofReal.comp hbm)
    calc μ {ω | _} ≤ (μ.map (Ψ n)) _ := Measure.le_map_apply (hΨ n).measurable.aemeasurable _
      _ = (ρ.prod (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n =>
          gaussianReal 0 1)) _ := by rw [(hΨ n).map_eq]
      _ ≤ ∫⁻ q, min 1 (ENNReal.ofReal (bq n q)) ∂(ρ.prod (Measure.pi fun _ : Fin n => Measure.pi fun
          _ : Fin n => gaussianReal 0 1)) := hcond
      _ = ∫⁻ ω, min 1 (ENNReal.ofReal (bq n (Ψ n ω))) ∂μ := ((hΨ n).lintegral_comp hg).symm
      _ ≤ _ := lintegral_mono fun ω =>
        min_le_min_left _ (ENNReal.ofReal_le_ofReal (hle n ω))
  exact tendsto_measure_of_le_lintegral_min_one
    (Filter.eventually_atTop.2 ⟨1, fun n hn => hmain n hn⟩) hb0

end linear

end NTK

end
