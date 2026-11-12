/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.FixedPoint.Map
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.MatrixPosSemidef

/-!
# Invariance of the cone for the fixed-point map

`T(q, ρ) = (E⟨ξ⟩⟨ξ⟩ᵀ, E⟨ξ ξᵀ⟩)` always takes values in `{Q ⪰ 0, ρ - Q ⪰ 0}`: `E⟨ξ⟩⟨ξ⟩ᵀ` is a mean
of Gram matrices and `E⟨ξ ξᵀ⟩ - E⟨ξ⟩⟨ξ⟩ᵀ = E Cov(ξ)` is a mean of covariance matrices of
probability measures.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix
namespace SpinGlasses

variable {α : Type*} [MeasurableSpace α]

instance {d : ℕ} (β : ℝ) (Q : Fin d → Fin d → ℝ) : IsProbabilityMeasure (skVectorGaussianLaw β Q)
  := by
  unfold skVectorGaussianLaw
  infer_instance

variable {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
  (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
  (ρ q : Fin d → Fin d → ℝ)

omit [IsProbabilityMeasure μ] in
/-- Two-replica Gibbs averages of products are products of Gibbs means. -/
theorem skVectorFieldAverage_pair (u v : Fin d) (y : Fin d → ℝ) :
    skVectorFieldAverage μ ξ β ρ q (fun σ : Fin 2 → α => ξ (σ 0) u * ξ (σ 1) v) y =
      (∫ a, ξ a u ∂(μ.tilted (skVectorFieldExponent ξ β ρ q y))) *
        (∫ a, ξ a v ∂(μ.tilted (skVectorFieldExponent ξ β ρ q y))) := by
  unfold skVectorFieldAverage
  have := integral_fintype_prod_eq_prod (ι := Fin 2) (E := fun _ => α)
    (fun i => ![fun a => ξ a u, fun a => ξ a v] i)
    (μ := fun _ => μ.tilted (skVectorFieldExponent ξ β ρ q y))
  simp only [Fin.prod_univ_two] at this
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
  exact this

include hξ hbound in
/-- One-replica Gibbs averages of products. -/
theorem skVectorFieldAverage_diag (u v : Fin d) (y : Fin d → ℝ) :
    skVectorFieldAverage μ ξ β ρ q (fun σ : Fin 2 → α => ξ (σ 0) u * ξ (σ 0) v) y =
      ∫ a, ξ a u * ξ a v ∂(μ.tilted (skVectorFieldExponent ξ β ρ q y)) := by
  unfold skVectorFieldAverage
  have hexpi := integrable_exp_skVectorFieldExponent μ ξ hξ (Nat.cast_nonneg d) hbound β ρ q y
  have : IsProbabilityMeasure (μ.tilted (skVectorFieldExponent ξ β ρ q y)) :=
    isProbabilityMeasure_tilted hexpi
  exact integral_pi_eval (μ.tilted (skVectorFieldExponent ξ β ρ q y)) (J := Fin 2) 0
    (fun a => ξ a u * ξ a v) (measurable_spin_mul ξ hξ u v).aestronglyMeasurable

include hξ hbound in
/-- The first component of the fixed-point map is positive semidefinite. -/
theorem skVectorFixedPointMap_fst_posSemidef (x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)) :
    (Matrix.of (skVectorFixedPointMap μ ξ β x).1).PosSemidef := by
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hb : ∀ a w, |ξ a w| ≤ Real.sqrt d := abs_spin_le ξ hbound
  set G : (Fin d → ℝ) → Fin d → ℝ := fun y w =>
    ∫ a, ξ a w ∂(μ.tilted (skVectorFieldExponent ξ β x.2 x.1 y)) with hG
  have hGm : ∀ w, Measurable fun y => G y w := fun w =>
    measurable_integral_tilted (e := fun y a => skVectorFieldExponent ξ β x.2 x.1 y a)
      (measurable_skVectorFieldExponent_joint ξ hξ β x.2 x.1) (hξ w)
  have hGb : ∀ y w, |G y w| ≤ Real.sqrt d := fun y w =>
    abs_integral_tilted_le (integrable_exp_skVectorFieldExponent μ ξ hξ hr hbound β x.2 x.1 y)
      fun a => hb a w
  have := Matrix.posSemidef_integral_of_posSemidef (skVectorGaussianLaw β x.1)
    (fun y => Matrix.vecMulVec (G y) (star (G y)))
    (fun y => Matrix.posSemidef_vecMulVec_self_star (G y)) (fun u v => by
      refine integrable_of_measurable_bound ((hGm u).mul (hGm v)) (M := d) fun y => ?_
      simp only [Matrix.vecMulVec_apply, star_trivial, abs_mul]
      calc |G y u| * |G y v| ≤ Real.sqrt d * Real.sqrt d :=
            mul_le_mul (hGb y u) (hGb y v) (abs_nonneg _) (Real.sqrt_nonneg _)
        _ = d := Real.mul_self_sqrt hr)
  convert this using 2
  ext u v
  simp only [skVectorFixedPointMap, Matrix.vecMulVec_apply, star_trivial]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y =>
    skVectorFieldAverage_pair μ ξ β x.2 x.1 u v y)

include hξ hbound in
/-- The difference of the two components of the fixed-point map is positive semidefinite. -/
theorem skVectorFixedPointMap_sub_posSemidef (x : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)) :
    (Matrix.of (skVectorFixedPointMap μ ξ β x).2 - Matrix.of (skVectorFixedPointMap μ ξ β
      x).1).PosSemidef :=
        by
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hb : ∀ a w, |ξ a w| ≤ Real.sqrt d := abs_spin_le ξ hbound
  have hxs : ∀ a u v, |ξ a u * ξ a v| ≤ d := fun a u v =>
    abs_spin_mul_le ξ (Nat.cast_nonneg d) hbound a a u v
  have hexp := fun y => integrable_exp_skVectorFieldExponent μ ξ hξ hr hbound β x.2 x.1 y
  have hprob : ∀ y, IsProbabilityMeasure (μ.tilted (skVectorFieldExponent ξ β x.2 x.1 y)) :=
    fun y => isProbabilityMeasure_tilted (hexp y)
  set e : (Fin d → ℝ) → α → ℝ := fun y => skVectorFieldExponent ξ β x.2 x.1 y with he
  have hem : Measurable fun p : (Fin d → ℝ) × α => e p.1 p.2 :=
    measurable_skVectorFieldExponent_joint ξ hξ β x.2 x.1
  have hGm : ∀ w, Measurable fun y => ∫ a, ξ a w ∂(μ.tilted (e y)) := fun w =>
    measurable_integral_tilted (e := e) hem (hξ w)
  have hHm : ∀ u v, Measurable fun y => ∫ a, ξ a u * ξ a v ∂(μ.tilted (e y)) :=
    fun u v => measurable_integral_tilted (e := e) hem (measurable_spin_mul ξ hξ u v)
  have hGb : ∀ y w, |∫ a, ξ a w ∂(μ.tilted (e y))| ≤ Real.sqrt d := fun y w =>
    abs_integral_tilted_le (hexp y) fun a => hb a w
  have hHb : ∀ y u v, |∫ a, ξ a u * ξ a v ∂(μ.tilted (e y))| ≤ d := fun y u v =>
    abs_integral_tilted_le (hexp y) fun a => hxs a u v
  have hHi : ∀ u v, Integrable (fun y => ∫ a, ξ a u * ξ a v ∂(μ.tilted (e y)))
      (skVectorGaussianLaw β x.1) := fun u v =>
    integrable_of_measurable_bound (hHm u v) (M := d) (hHb · u v)
  have hGGi : ∀ u v, Integrable (fun y => (∫ a, ξ a u ∂(μ.tilted (e y))) *
      (∫ a, ξ a v ∂(μ.tilted (e y)))) (skVectorGaussianLaw β x.1) := fun u v =>
    integrable_of_measurable_bound ((hGm u).mul (hGm v)) (M := d) fun y => by
      rw [abs_mul]
      calc _ ≤ Real.sqrt d * Real.sqrt d :=
            mul_le_mul (hGb y u) (hGb y v) (abs_nonneg _) (Real.sqrt_nonneg _)
        _ = d := Real.mul_self_sqrt hr
  have hcov : ∀ y, (Matrix.of fun u v => (∫ a, ξ a u * ξ a v ∂(μ.tilted (e y))) -
      (∫ a, ξ a u ∂(μ.tilted (e y))) * (∫ a, ξ a v ∂(μ.tilted (e y)))).PosSemidef := fun y => by
    have := hprob y
    exact Matrix.posSemidef_covariance_of_bounded (μ.tilted (e y)) (fun u a => ξ a u) hξ
      (B := Real.sqrt d) fun u a => hb a u
  have := Matrix.posSemidef_integral_of_posSemidef (skVectorGaussianLaw β x.1)
    (fun y => Matrix.of fun u v => (∫ a, ξ a u * ξ a v ∂(μ.tilted (e y))) -
      (∫ a, ξ a u ∂(μ.tilted (e y))) * (∫ a, ξ a v ∂(μ.tilted (e y)))) hcov
    (fun u v => (hHi u v).sub (hGGi u v))
  convert this using 1
  ext u v
  simp only [skVectorFixedPointMap, Matrix.sub_apply, Matrix.of_apply]
  rw [integral_sub (hHi u v) (hGGi u v)]
  congr 1
  · exact integral_congr_ae (Filter.Eventually.of_forall fun y =>
      skVectorFieldAverage_diag μ ξ hξ hbound β x.2 x.1 u v y)
  · exact integral_congr_ae (Filter.Eventually.of_forall fun y =>
      skVectorFieldAverage_pair μ ξ β x.2 x.1 u v y)

end SpinGlasses
