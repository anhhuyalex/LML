/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Regularity of a parametric integral over a non-compact space

Mathlib's `ContDiff.parametric_integral` integrates over a subset of a compact set. For a Gaussian
(or any finite) measure on a non-compact space, a jointly `Cⁿ` integrand whose parameter
derivatives are dominated uniformly by integrable functions gives a `Cⁿ` parametric integral.

* `MeasureTheory.fderivLeft`: the partial derivative in the parameter, as a continuous linear map.
* `MeasureTheory.contDiff_one_integral_of_bound`, `MeasureTheory.contDiff_two_integral_of_bounds`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace MeasureTheory

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The partial derivative in the first variable of a function on a product, as a continuous
linear map `P →L[ℝ] F`. -/
noncomputable def fderivLeft (G : P × E → F) (q : P × E) : P →L[ℝ] F :=
  (fderiv ℝ G q).comp (ContinuousLinearMap.inl ℝ P E)

theorem hasFDerivAt_fderivLeft {G : P × E → F} {q : P × E} (hd : DifferentiableAt ℝ G q) :
    HasFDerivAt (fun p => G (p, q.2)) (fderivLeft G q) q.1 := by
  have h1 : HasFDerivAt (fun p : P => (p, q.2)) (ContinuousLinearMap.inl ℝ P E) q.1 :=
    (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)
  exact hd.hasFDerivAt.comp q.1 (by simpa using h1)

theorem fderivLeft_eq {G : P × E → F} {q : P × E} (hd : DifferentiableAt ℝ G q) :
    fderivLeft G q = fderiv ℝ (fun p => G (p, q.2)) q.1 :=
  (hasFDerivAt_fderivLeft hd).fderiv.symm

theorem contDiff_fderivLeft {G : P × E → F} {n : ℕ} (hG : ContDiff ℝ (n + 1) G) :
    ContDiff ℝ n (fderivLeft G) :=
  (hG.fderiv_right (by exact_mod_cast le_rfl)).clm_comp contDiff_const

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {ν : Measure E}

/-- **`C¹` regularity of a parametric integral over a non-compact space.** -/
theorem contDiff_one_integral_of_bound {G : P × E → F} (hG : ContDiff ℝ 1 G)
    (hint : ∀ p, Integrable (fun η => G (p, η)) ν) {b : E → ℝ} (hb : Integrable b ν)
    (hbd : ∀ q, ‖fderivLeft G q‖ ≤ b q.2) :
    ContDiff ℝ 1 (fun p => ∫ η, G (p, η) ∂ν) ∧
      ∀ p, HasFDerivAt (fun p => ∫ η, G (p, η) ∂ν) (∫ η, fderivLeft G (p, η) ∂ν) p := by
  have hd : ∀ q, DifferentiableAt ℝ G q := fun q =>
    (hG.differentiable (by simp)) q
  have hcG : Continuous G := hG.continuous
  have hcD : Continuous (fderivLeft G) :=
    (contDiff_fderivLeft (n := 0) (by simpa using hG)).continuous
  have hmeas : ∀ p, AEStronglyMeasurable (fun η => G (p, η)) ν := fun p =>
    (hcG.comp (Continuous.prodMk_right p)).aestronglyMeasurable
  have hmeas' : ∀ p, AEStronglyMeasurable (fun η => fderivLeft G (p, η)) ν := fun p =>
    (hcD.comp (Continuous.prodMk_right p)).aestronglyMeasurable
  have hder : ∀ p, HasFDerivAt (fun p => ∫ η, G (p, η) ∂ν) (∫ η, fderivLeft G (p, η) ∂ν) p :=
    fun p => hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ) (bound := b)
      (F := fun p η => G (p, η)) (F' := fun p η => fderivLeft G (p, η)) Filter.univ_mem
      (Eventually.of_forall hmeas) (hint p) (hmeas' p)
      (ae_of_all _ fun η x _ => hbd (x, η)) hb
      (ae_of_all _ fun η x _ => hasFDerivAt_fderivLeft (hd (x, η)))
  refine ⟨?_, hder⟩
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun p => (hder p).differentiableAt, ?_⟩
  have : fderiv ℝ (fun p => ∫ η, G (p, η) ∂ν) = fun p => ∫ η, fderivLeft G (p, η) ∂ν :=
    funext fun p => (hder p).fderiv
  rw [this]
  exact continuous_of_dominated (bound := b) hmeas' (fun p => ae_of_all _ fun η => hbd (p, η)) hb
    (ae_of_all _ fun η => hcD.comp (Continuous.prodMk_left η))

/-- **`C²` regularity of a parametric integral over a non-compact space.** If `G` is `C²`
jointly, each `G(p, ·)` is integrable, and the first and second parameter derivatives are bounded by
integrable functions of the integration variable, then `p ↦ ∫ G(p, η) dν` is `C²`. -/
theorem contDiff_two_integral_of_bounds {G : P × E → F} (hG : ContDiff ℝ 2 G)
    (hint : ∀ p, Integrable (fun η => G (p, η)) ν) {b₁ b₂ : E → ℝ} (hb₁ : Integrable b₁ ν)
    (hb₂ : Integrable b₂ ν) (h1 : ∀ q, ‖fderivLeft G q‖ ≤ b₁ q.2)
    (h2 : ∀ q, ‖fderivLeft (fderivLeft G) q‖ ≤ b₂ q.2) :
    ContDiff ℝ 2 (fun p => ∫ η, G (p, η) ∂ν) := by
  have hG1 : ContDiff ℝ 1 G := hG.of_le (by norm_num)
  obtain ⟨-, hder⟩ := contDiff_one_integral_of_bound hG1 hint hb₁ h1
  have hD1 : ContDiff ℝ 1 (fderivLeft G) :=
    contDiff_fderivLeft (n := 1) (by simpa [one_add_one_eq_two] using hG)
  have hintD : ∀ p, Integrable (fun η => fderivLeft G (p, η)) ν := fun p =>
    hb₁.mono' ((hD1.continuous.comp (Continuous.prodMk_right p)).aestronglyMeasurable)
      (ae_of_all _ fun η => h1 (p, η))
  obtain ⟨hC, -⟩ := contDiff_one_integral_of_bound hD1 hintD hb₂ h2
  have hfd : fderiv ℝ (fun p => ∫ η, G (p, η) ∂ν) = fun p => ∫ η, fderivLeft G (p, η) ∂ν :=
    funext fun p => (hder p).fderiv
  have : ContDiff ℝ (1 + 1) (fun p => ∫ η, G (p, η) ∂ν) := by
    rw [contDiff_succ_iff_fderiv]
    exact ⟨fun p => (hder p).differentiableAt, fun h => absurd h (by simp), by rwa [hfd]⟩
  simpa [one_add_one_eq_two] using this

end MeasureTheory
