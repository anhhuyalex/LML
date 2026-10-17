/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletGhirlandaGuerraExpectation

/-!
# Centering overlap observables under Gaussian Poisson--Dirichlet tilts

An algebraic identity for random normalized replica weights, with no
assumptions about the probability space or the provenance of the weights.
-/

@[expose] public section

open MeasureTheory

namespace SpinGlasses

/-- If the marked and plain series converge almost surely, removing a constant
from the mark amounts to adding that constant times the plain expected average.
Unlike `integral_gibbs_centered_mark_add_constant`, this version permits the
index set and the replica observable to depend on the random environment. -/
theorem integral_gibbs_centered_mark_add_constant_dep
    {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (P : Measure Ω) (α : Ω → Type*)
    (w : (ω : Ω) → α ω → ℝ)
    (Φ : (ω : Ω) → (J → α ω) → ℝ)
    (x : (ω : Ω) → (J → α ω) → ℝ) (c : ℝ)
    (hs : ∀ᵐ ω ∂P, Summable (fun σ : J → α ω =>
      (∏ j, w ω (σ j)) * (Φ ω σ * (x ω σ - c))) ∧
      Summable (fun σ : J → α ω => (∏ j, w ω (σ j)) * Φ ω σ))
    (hcenter : Integrable (fun ω => ∑' σ : J → α ω,
      (∏ j, w ω (σ j)) * (Φ ω σ * (x ω σ - c))) P)
    (hplain : Integrable (fun ω => ∑' σ : J → α ω,
      (∏ j, w ω (σ j)) * Φ ω σ) P) :
    (∫ ω, ∑' σ : J → α ω,
      (∏ j, w ω (σ j)) * (Φ ω σ * x ω σ) ∂P) =
      (∫ ω, ∑' σ : J → α ω,
        (∏ j, w ω (σ j)) * (Φ ω σ * (x ω σ - c)) ∂P) +
        c * ∫ ω, ∑' σ : J → α ω,
          (∏ j, w ω (σ j)) * Φ ω σ ∂P := by
  have hpoint : ∀ᵐ ω ∂P,
      (∑' σ : J → α ω, (∏ j, w ω (σ j)) * (Φ ω σ * x ω σ)) =
        (∑' σ : J → α ω,
          (∏ j, w ω (σ j)) * (Φ ω σ * (x ω σ - c))) +
          c * ∑' σ : J → α ω, (∏ j, w ω (σ j)) * Φ ω σ := by
    filter_upwards [hs] with ω ⟨hmark, hbase⟩
    have hterm (σ : J → α ω) :
        (∏ j, w ω (σ j)) * (Φ ω σ * x ω σ) =
          (∏ j, w ω (σ j)) * (Φ ω σ * (x ω σ - c)) +
            c * ((∏ j, w ω (σ j)) * Φ ω σ) := by ring
    simp_rw [hterm]
    rw [hmark.tsum_add (hbase.mul_left c), tsum_mul_left]
  rw [integral_congr_ae hpoint, integral_add hcenter (hplain.const_mul c),
    integral_const_mul]

end SpinGlasses
