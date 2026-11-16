/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.StdGaussianRadial

/-!
# The direction of a standard Gaussian vector is uniform on the sphere

On a nontrivial finite-dimensional real inner product space `E`, the normalized vector
`x ↦ ‖x‖⁻¹ • x` of a standard Gaussian `x` has the normalized surface measure of the unit sphere
as its law.  Here the surface measure is Mathlib's `Measure.toSphere` of the volume, and the law is
a measure on `E` supported on the sphere, so no sphere-valued default is needed (the map sends `0`
to `0`, which the Gaussian never charges).

The proof uses the polar-coordinate measure isomorphism
`MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd` and the radial Lebesgue density
of `stdGaussian E` (`stdGaussian_eq_withDensity`): the density depends only on the radius, so
the direction marginal is a constant multiple of the surface measure, and total mass one fixes the
constant.  Dimension one is included.

## Main declarations

* `ProbabilityTheory.map_normalize_stdGaussian_eq`: the law of the direction of `stdGaussian E`.
* `ProbabilityTheory.inner_nonneg_normalize_iff`: normalizing a normal vector keeps its
  half-space `{x | 0 ≤ ⟪x, g⟫}`.
* `ProbabilityTheory.map_normalize_toLp_pi_pi_gaussianReal`: the rows of a matrix of i.i.d.
  standard normals, normalized, are i.i.d. with the uniform-direction law.
* `ProbabilityTheory.iIndepFun_normalize_toLp_pi_pi_gaussianReal`: the normalized rows are
  independent.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal InnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The direction of a standard Gaussian is uniform on the unit sphere.**  For `E` nontrivial,
the law of `‖x‖⁻¹ • x` under `stdGaussian E` is the surface measure `ν = volume.toSphere`
normalized to total mass one, viewed as a measure on `E`. -/
theorem map_normalize_stdGaussian_eq [Nontrivial E] :
    (stdGaussian E).map (fun x : E => ‖x‖⁻¹ • x) =
      (((volume : Measure E).toSphere univ)⁻¹ • (volume : Measure E).toSphere).map
        (Subtype.val : sphere (0 : E) 1 → E) := by
  set ν := (volume : Measure E).toSphere with hν
  set c : ℝ := (2 * Real.pi) ^ (-(Module.finrank ℝ E : ℝ) / 2) with hc
  set m : ℝ≥0∞ := ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (c * Real.exp (-(r : ℝ) ^ 2 / 2))
    ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1)) with hm
  have key : ∀ s : Set E, MeasurableSet s →
      stdGaussian E ((fun x : E => ‖x‖⁻¹ • x) ⁻¹' s) = m * ν (Subtype.val ⁻¹' s) := by
    intro s hs
    have hψ : Measurable (fun x : E => ‖x‖⁻¹ • x) := by fun_prop
    have hρ0 : stdGaussian E {0} = 0 := by
      simpa using stdGaussian_submodule_eq_zero (E := E) ⊥ bot_ne_top
    have hcompl : stdGaussian E ({0}ᶜ)ᶜ = 0 := by simpa using hρ0
    rw [← measure_inter_conull hcompl, stdGaussian_eq_withDensity,
      withDensity_apply _ ((hψ hs).inter (measurableSet_singleton 0).compl)]
    set t : Set ({0}ᶜ : Set E) := Subtype.val ⁻¹' ((fun x : E => ‖x‖⁻¹ • x) ⁻¹' s) with ht
    have himg : (Subtype.val '' t) = (fun x : E => ‖x‖⁻¹ • x) ⁻¹' s ∩ {0}ᶜ := by
      rw [ht, Subtype.image_preimage_coe, inter_comm]
    rw [← himg, ← setLIntegral_subtype (measurableSet_singleton 0).compl]
    set A : Set (sphere (0 : E) 1) := Subtype.val ⁻¹' s with hA
    have hAm : MeasurableSet A := measurable_subtype_coe hs
    set Φ : sphere (0 : E) 1 × Ioi (0 : ℝ) → ℝ≥0∞ := fun p =>
      A.indicator 1 p.1 * ENNReal.ofReal (c * Real.exp (-(p.2 : ℝ) ^ 2 / 2)) with hΦ
    have hΦm : Measurable Φ := by
      have : Measurable (A.indicator (1 : sphere (0 : E) 1 → ℝ≥0∞)) :=
        measurable_one.indicator hAm
      fun_prop
    have hcomp : ∀ y : ({0}ᶜ : Set E),
        t.indicator (fun y : ({0}ᶜ : Set E) =>
          ENNReal.ofReal (c * Real.exp (-‖(y : E)‖ ^ 2 / 2))) y =
          Φ (homeomorphUnitSphereProd E y) := by
      intro y
      have hmem : y ∈ t ↔ (homeomorphUnitSphereProd E y).1 ∈ A := by
        simp [ht, hA]
      simp only [hΦ]
      by_cases h : y ∈ t
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.1 h)]
        simp
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hmem.2 h'))]
        simp
    have htm : MeasurableSet t := (hψ.comp measurable_subtype_coe) hs
    have hmp := Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure E)
    calc _ = ∫⁻ y, Φ (homeomorphUnitSphereProd E y) ∂((volume : Measure E).comap Subtype.val) := by
          rw [← lintegral_indicator htm]
          exact lintegral_congr hcomp
      _ = ∫⁻ b, Φ b ∂(ν.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) :=
          hmp.lintegral_comp_emb (Homeomorph.measurableEmbedding _) Φ
      _ = m * ν A := by
          rw [lintegral_prod _ hΦm.aemeasurable]
          have h1 : ∀ a : sphere (0 : E) 1, ∫⁻ r, Φ (a, r) ∂(Measure.volumeIoiPow
              (Module.finrank ℝ E - 1)) = A.indicator 1 a * m := fun a => by
            simp only [hΦ]
            exact lintegral_const_mul' _ _ (by
              by_cases h : a ∈ A <;> simp [Set.indicator, h])
          simp_rw [h1]
          rw [lintegral_mul_const _ (measurable_one.indicator hAm), lintegral_indicator_one hAm,
            mul_comm]
  have hm1 : m * ν univ = 1 := by
    have := key univ MeasurableSet.univ
    simpa [eq_comm] using this
  have hνne : ν univ ≠ 0 := Measure.measure_univ_ne_zero.2 (Measure.toSphere_ne_zero _)
  have hm2 : m = (ν univ)⁻¹ := ENNReal.eq_inv_of_mul_eq_one_left hm1
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, key s hs,
    Measure.map_apply measurable_subtype_coe hs, smul_apply, smul_eq_mul, hm2]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **Normalizing a normal vector keeps its half-space.**  For any `g`, `x ∈ E`:
`0 ≤ ⟪x, ‖g‖⁻¹ • g⟫ ↔ 0 ≤ ⟪x, g⟫`.  For `g = 0` both sides hold. -/
theorem inner_nonneg_normalize_iff (g x : E) :
    0 ≤ ⟪x, ‖g‖⁻¹ • g⟫_ℝ ↔ 0 ≤ ⟪x, g⟫_ℝ := by
  rw [real_inner_smul_right]
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · exact mul_nonneg_iff_of_pos_left (inv_pos.2 (norm_pos_iff.2 hg))

section Rows

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **A normalized Gaussian vector in coordinates has the uniform-direction law.**  For `κ`
nonempty, the normalized `toLp` image of a vector of i.i.d. standard normals has the law of
`map_normalize_stdGaussian_eq` on `EuclideanSpace ℝ κ`. -/
theorem map_normalize_toLp_pi_gaussianReal [Nonempty κ] :
    (Measure.pi fun _ : κ => gaussianReal 0 1).map
        (fun x : κ → ℝ => ‖WithLp.toLp 2 x‖⁻¹ • WithLp.toLp 2 x) =
      (((volume : Measure (EuclideanSpace ℝ κ)).toSphere univ)⁻¹ •
        (volume : Measure (EuclideanSpace ℝ κ)).toSphere).map
          (Subtype.val : sphere (0 : EuclideanSpace ℝ κ) 1 → EuclideanSpace ℝ κ) := by
  rw [← map_normalize_stdGaussian_eq, ← map_pi_eq_stdGaussian,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- **The normalized rows of an i.i.d. Gaussian matrix are i.i.d. uniform directions.**  The
pushforward of `Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1` under the normalized rows
is the product of the uniform-direction law. -/
theorem map_normalize_toLp_pi_pi_gaussianReal [Nonempty κ] :
    (Measure.pi fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1).map
        (fun (g : ι → κ → ℝ) (k : ι) => ‖WithLp.toLp 2 (g k)‖⁻¹ • WithLp.toLp 2 (g k)) =
      Measure.pi fun _ : ι =>
        (((volume : Measure (EuclideanSpace ℝ κ)).toSphere univ)⁻¹ •
          (volume : Measure (EuclideanSpace ℝ κ)).toSphere).map
            (Subtype.val : sphere (0 : EuclideanSpace ℝ κ) 1 → EuclideanSpace ℝ κ) := by
  rw [Measure.pi_map_pi (f := fun (_ : ι) (x : κ → ℝ) => ‖WithLp.toLp 2 x‖⁻¹ • WithLp.toLp 2 x)
    fun _ => (by fun_prop : Measurable _).aemeasurable]
  simp only [map_normalize_toLp_pi_gaussianReal]

/-- **The normalized rows of an i.i.d. Gaussian matrix are independent.** -/
theorem iIndepFun_normalize_toLp_pi_pi_gaussianReal :
    iIndepFun (fun (k : ι) (g : ι → κ → ℝ) => ‖WithLp.toLp 2 (g k)‖⁻¹ • WithLp.toLp 2 (g k))
      (Measure.pi fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1) :=
  iIndepFun_pi (X := fun _ (x : κ → ℝ) => ‖WithLp.toLp 2 x‖⁻¹ • WithLp.toLp 2 x)
    (μ := fun _ : ι => Measure.pi fun _ : κ => gaussianReal 0 1)
    fun _ => (by fun_prop : Measurable _).aemeasurable

end Rows

end ProbabilityTheory
