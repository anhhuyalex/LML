/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import LeanMachineLearning.ForMathlib.Analysis.Calculus.BoundedC2
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Regularity of a parametric integral over a non-compact space

Mathlib's `ContDiff.parametric_integral` integrates over a subset of a compact set. For a Gaussian
(or any finite) measure on a non-compact space, a jointly `Cⁿ` integrand whose parameter
derivatives are dominated uniformly by integrable functions gives a `Cⁿ` parametric integral.
The parameter derivative of `G : P × E → F` at `(p, η)` is `fderiv ℝ (fun p => G (p, η)) p`.

* `MeasureTheory.hasFDerivAt_section_left`: this partial derivative from the joint derivative.
* `MeasureTheory.contDiff_one_integral_of_dominated`,
  `MeasureTheory.contDiff_two_integral_of_dominated`: only the sections `p ↦ G p ω` need be
  smooth, for a.e. `ω`, with local domination of the parameter derivatives.
* `MeasureTheory.contDiff_one_integral_of_bound`, `MeasureTheory.contDiff_two_integral_of_bounds`,
  `MeasureTheory.boundedC2_integral_of_bounds`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace MeasureTheory

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The partial derivative of a jointly differentiable function in its first variable. -/
theorem hasFDerivAt_section_left {G : P × E → F} {p : P} {η : E}
    (hd : DifferentiableAt ℝ G (p, η)) :
    HasFDerivAt (fun p => G (p, η)) ((fderiv ℝ G (p, η)).comp (ContinuousLinearMap.inl ℝ P E))
      p := by
  have h1 : HasFDerivAt (fun p : P => (p, η)) (ContinuousLinearMap.inl ℝ P E) p :=
    (hasFDerivAt_id p).prodMk (hasFDerivAt_const η p)
  exact hd.hasFDerivAt.comp p (by simpa using h1)

/-- If `G` is jointly `C^{n+1}`, its partial derivative in the first variable is jointly `Cⁿ`. -/
theorem contDiff_fderiv_section_left {G : P × E → F} {n : ℕ} (hG : ContDiff ℝ (n + 1) G) :
    ContDiff ℝ n (fun q : P × E => fderiv ℝ (fun p => G (p, q.2)) q.1) := by
  have h : ContDiff ℝ n (fun q : P × E => (fderiv ℝ G q).comp (ContinuousLinearMap.inl ℝ P E)) :=
    (hG.fderiv_right (by exact_mod_cast le_rfl)).clm_comp contDiff_const
  have heq : (fun q : P × E => fderiv ℝ (fun p => G (p, q.2)) q.1) =
      fun q : P × E => (fderiv ℝ G q).comp (ContinuousLinearMap.inl ℝ P E) := funext fun q =>
    (hasFDerivAt_section_left
      ((hG.differentiable (by exact_mod_cast Nat.succ_ne_zero n)) q)).fderiv
  rw [heq]
  exact h

section Dominated

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- **`C¹` regularity of a parametric integral under local domination.** Let every `G p` be
integrable, `p ↦ G p ω` be `C¹` for a.e. `ω`, the parameter derivative at each point be
measurable in `ω`, and dominated near each point by an integrable function. Then
`p ↦ ∫ G p ω dν` is `C¹` and may be differentiated under the integral sign. -/
theorem contDiff_one_integral_of_dominated {G : P → Ω → F} (hint : ∀ p, Integrable (G p) ν)
    (hC : ∀ᵐ ω ∂ν, ContDiff ℝ 1 fun p => G p ω)
    (hm : ∀ p, AEStronglyMeasurable (fun ω => fderiv ℝ (fun p => G p ω) p) ν)
    (hdom : ∀ p₀, ∃ s ∈ 𝓝 p₀, ∃ b : Ω → ℝ, Integrable b ν ∧
      ∀ᵐ ω ∂ν, ∀ p ∈ s, ‖fderiv ℝ (fun p => G p ω) p‖ ≤ b ω) :
    ContDiff ℝ 1 (fun p => ∫ ω, G p ω ∂ν) ∧
      ∀ p, HasFDerivAt (fun p => ∫ ω, G p ω ∂ν)
        (∫ ω, fderiv ℝ (fun p => G p ω) p ∂ν) p := by
  have hder : ∀ p, HasFDerivAt (fun p => ∫ ω, G p ω ∂ν)
      (∫ ω, fderiv ℝ (fun p => G p ω) p ∂ν) p := fun p => by
    obtain ⟨s, hs, b, hb, hbd⟩ := hdom p
    exact hasFDerivAt_integral_of_dominated_of_fderiv_le (s := s) (bound := b)
      (F := fun p ω => G p ω) (F' := fun p ω => fderiv ℝ (fun p => G p ω) p)
      hs (Eventually.of_forall fun p => (hint p).aestronglyMeasurable) (hint p) (hm p)
      hbd hb (hC.mono fun ω h x _ => ((h.differentiable one_ne_zero) x).hasFDerivAt)
  refine ⟨?_, hder⟩
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun p => (hder p).differentiableAt, ?_⟩
  have : fderiv ℝ (fun p => ∫ ω, G p ω ∂ν) =
      fun p => ∫ ω, fderiv ℝ (fun p => G p ω) p ∂ν := funext fun p => (hder p).fderiv
  rw [this, continuous_iff_continuousAt]
  intro p₀
  obtain ⟨s, hs, b, hb, hbd⟩ := hdom p₀
  exact continuousAt_of_dominated (bound := b) (Eventually.of_forall hm)
    (Filter.eventually_of_mem hs fun p hp => hbd.mono fun ω h => h p hp) hb
    (hC.mono fun ω h => (h.continuous_fderiv one_ne_zero).continuousAt)

/-- **`C²` regularity of a parametric integral under local domination** of the first and second
parameter derivatives. -/
theorem contDiff_two_integral_of_dominated {G : P → Ω → F} (hint : ∀ p, Integrable (G p) ν)
    (hC : ∀ᵐ ω ∂ν, ContDiff ℝ 2 fun p => G p ω)
    (hm1 : ∀ p, AEStronglyMeasurable (fun ω => fderiv ℝ (fun p => G p ω) p) ν)
    (hm2 : ∀ p, AEStronglyMeasurable (fun ω => fderiv ℝ (fderiv ℝ fun p => G p ω) p) ν)
    (hdom1 : ∀ p₀, ∃ s ∈ 𝓝 p₀, ∃ b : Ω → ℝ, Integrable b ν ∧
      ∀ᵐ ω ∂ν, ∀ p ∈ s, ‖fderiv ℝ (fun p => G p ω) p‖ ≤ b ω)
    (hdom2 : ∀ p₀, ∃ s ∈ 𝓝 p₀, ∃ b : Ω → ℝ, Integrable b ν ∧
      ∀ᵐ ω ∂ν, ∀ p ∈ s, ‖fderiv ℝ (fderiv ℝ fun p => G p ω) p‖ ≤ b ω) :
    ContDiff ℝ 2 (fun p => ∫ ω, G p ω ∂ν) ∧
      (∀ p, fderiv ℝ (fun p => ∫ ω, G p ω ∂ν) p = ∫ ω, fderiv ℝ (fun p => G p ω) p ∂ν) ∧
      ∀ p, fderiv ℝ (fderiv ℝ (fun p => ∫ ω, G p ω ∂ν)) p =
        ∫ ω, fderiv ℝ (fderiv ℝ fun p => G p ω) p ∂ν := by
  obtain ⟨-, hder⟩ := contDiff_one_integral_of_dominated hint
    (hC.mono fun ω h => h.of_le (by norm_num)) hm1 hdom1
  have hintD : ∀ p, Integrable (fun ω => fderiv ℝ (fun p => G p ω) p) ν := fun p => by
    obtain ⟨s, hs, b, hb, hbd⟩ := hdom1 p
    exact hb.mono' (hm1 p) (hbd.mono fun ω h => h p (mem_of_mem_nhds hs))
  obtain ⟨hC1, hder2⟩ := contDiff_one_integral_of_dominated
    (G := fun p ω => fderiv ℝ (fun p => G p ω) p) hintD
    (hC.mono fun ω h => h.fderiv_right (m := 1) (by norm_num)) hm2 hdom2
  have hfd : fderiv ℝ (fun p => ∫ ω, G p ω ∂ν) =
      fun p => ∫ ω, fderiv ℝ (fun p => G p ω) p ∂ν := funext fun p => (hder p).fderiv
  refine ⟨?_, fun p => (hder p).fderiv, fun p => ?_⟩
  · have : ContDiff ℝ (1 + 1) (fun p => ∫ ω, G p ω ∂ν) := by
      rw [contDiff_succ_iff_fderiv]
      exact ⟨fun p => (hder p).differentiableAt, fun h => absurd h (by simp), by rwa [hfd]⟩
    simpa [one_add_one_eq_two] using this
  · rw [hfd]
    exact (hder2 p).fderiv

end Dominated

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {ν : Measure E}

/-- **`C¹` regularity of a parametric integral over a non-compact space.** -/
theorem contDiff_one_integral_of_bound {G : P × E → F} (hG : ContDiff ℝ 1 G)
    (hint : ∀ p, Integrable (fun η => G (p, η)) ν) {b : E → ℝ} (hb : Integrable b ν)
    (hbd : ∀ p η, ‖fderiv ℝ (fun p => G (p, η)) p‖ ≤ b η) :
    ContDiff ℝ 1 (fun p => ∫ η, G (p, η) ∂ν) ∧
      ∀ p, HasFDerivAt (fun p => ∫ η, G (p, η) ∂ν)
        (∫ η, fderiv ℝ (fun p => G (p, η)) p ∂ν) p := by
  have hcD : Continuous (fun q : P × E => fderiv ℝ (fun p => G (p, q.2)) q.1) :=
    (contDiff_fderiv_section_left (n := 0) (by simpa using hG)).continuous
  exact contDiff_one_integral_of_dominated (G := fun p η => G (p, η)) hint
    (ae_of_all _ fun η => hG.comp (contDiff_id.prodMk contDiff_const))
    (fun p => (hcD.comp (Continuous.prodMk_right p)).aestronglyMeasurable)
    fun _ => ⟨Set.univ, univ_mem, b, hb, ae_of_all _ fun η p _ => hbd p η⟩

/-- **`C²` regularity of a parametric integral over a non-compact space.** If `G` is `C²`
jointly, each `G(p, ·)` is integrable, and the first and second parameter derivatives are bounded by
integrable functions of the integration variable, then `p ↦ ∫ G(p, η) dν` is `C²`; its derivative
and second derivative are the integrals of the parameter derivatives. -/
theorem contDiff_two_integral_of_bounds {G : P × E → F} (hG : ContDiff ℝ 2 G)
    (hint : ∀ p, Integrable (fun η => G (p, η)) ν) {b₁ b₂ : E → ℝ} (hb₁ : Integrable b₁ ν)
    (hb₂ : Integrable b₂ ν) (h1 : ∀ p η, ‖fderiv ℝ (fun p => G (p, η)) p‖ ≤ b₁ η)
    (h2 : ∀ p η, ‖fderiv ℝ (fun p' => fderiv ℝ (fun p => G (p, η)) p') p‖ ≤ b₂ η) :
    ContDiff ℝ 2 (fun p => ∫ η, G (p, η) ∂ν) ∧
      (∀ p, fderiv ℝ (fun p => ∫ η, G (p, η) ∂ν) p = ∫ η, fderiv ℝ (fun p => G (p, η)) p ∂ν) ∧
      ∀ p, fderiv ℝ (fderiv ℝ (fun p => ∫ η, G (p, η) ∂ν)) p =
        ∫ η, fderiv ℝ (fun p' => fderiv ℝ (fun p => G (p, η)) p') p ∂ν := by
  have hD1 : ContDiff ℝ 1 (fun q : P × E => fderiv ℝ (fun p => G (p, q.2)) q.1) :=
    contDiff_fderiv_section_left (n := 1) (by simpa [one_add_one_eq_two] using hG)
  have hcD2 : Continuous (fun q : P × E =>
      fderiv ℝ (fderiv ℝ fun p => G (p, q.2)) q.1) :=
    (contDiff_fderiv_section_left (n := 0) (by simpa using hD1)).continuous
  have : TopologicalSpace.PseudoMetrizableSpace (P →L[ℝ] P →L[ℝ] F) :=
    @PseudoEMetricSpace.pseudoMetrizableSpace _
      (ContinuousLinearMap.toSeminormedAddCommGroup (E := P) (F := P →L[ℝ] F)
        (σ₁₂ := RingHom.id ℝ)).toPseudoMetricSpace.toPseudoEMetricSpace
  exact contDiff_two_integral_of_dominated (G := fun p η => G (p, η)) hint
    (ae_of_all _ fun η => hG.comp (contDiff_id.prodMk contDiff_const))
    (fun p => (hD1.continuous.comp (Continuous.prodMk_right p)).aestronglyMeasurable)
    (fun p => (hcD2.comp (Continuous.prodMk_right p)).aestronglyMeasurable)
    (fun _ => ⟨Set.univ, univ_mem, b₁, hb₁, ae_of_all _ fun η p _ => h1 p η⟩)
    fun _ => ⟨Set.univ, univ_mem, b₂, hb₂, ae_of_all _ fun η p _ => h2 p η⟩

/-- **A dominated parametric integral is `BoundedC2`.** If, in addition, `G` and its first and
second parameter derivatives are dominated by integrable `b₀, b₁, b₂`, then
`p ↦ ∫ G(p, η) dν` has bounded value, derivative and second derivative. -/
theorem boundedC2_integral_of_bounds {G : P × E → ℝ} (hG : ContDiff ℝ 2 G)
    (hint : ∀ p, Integrable (fun η => G (p, η)) ν) {b₀ b₁ b₂ : E → ℝ} (hb₀ : Integrable b₀ ν)
    (hb₁ : Integrable b₁ ν) (hb₂ : Integrable b₂ ν) (h0 : ∀ p η, |G (p, η)| ≤ b₀ η)
    (h1 : ∀ p η, ‖fderiv ℝ (fun p => G (p, η)) p‖ ≤ b₁ η)
    (h2 : ∀ p η, ‖fderiv ℝ (fun p' => fderiv ℝ (fun p => G (p, η)) p') p‖ ≤ b₂ η) :
    BoundedC2 (fun p => ∫ η, G (p, η) ∂ν) := by
  obtain ⟨hC2, hd1, hd2⟩ := contDiff_two_integral_of_bounds hG hint hb₁ hb₂ h1 h2
  refine ⟨hC2, max (∫ η, b₀ η ∂ν) (max (∫ η, b₁ η ∂ν) (∫ η, b₂ η ∂ν)), fun p => ⟨?_, ?_, ?_⟩⟩
  · have := norm_integral_le_of_norm_le (f := fun η => G (p, η)) hb₀
      (ae_of_all _ fun η => by simpa using h0 p η)
    exact (Real.norm_eq_abs _ ▸ this).trans (le_max_left _ _)
  · rw [hd1 p]
    exact (norm_integral_le_of_norm_le hb₁ (ae_of_all _ fun η => h1 p η)).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · rw [hd2 p]
    exact (norm_integral_le_of_norm_le hb₂ (ae_of_all _ fun η => h2 p η)).trans
      ((le_max_right _ _).trans (le_max_right _ _))

end MeasureTheory
