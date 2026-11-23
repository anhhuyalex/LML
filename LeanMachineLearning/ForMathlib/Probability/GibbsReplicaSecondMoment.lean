/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct

/-!
# Comparison of replica second moments

If two uniformly bounded, jointly measurable replica observables satisfy `g² ≤ f² + err`
pointwise, then the Gibbs and environment average of `g²` is at most that of `f²` plus `err`.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory

variable {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [Fintype ι]
  {μ : Measure α} [IsFiniteMeasure μ]

/-- **Second-moment comparison under replica Gibbs averages.** For a jointly measurable energy
`E`, a probability law `P` on the environment, and jointly measurable observables `f, g` of the
replicas bounded by `C`, the pointwise bound `g² ≤ f² + err` gives
`∫ ∫ g² ≤ ∫ ∫ f² + err`, the inner integral being against the product of tilted laws. -/
theorem integral_integral_pi_tilted_sq_le_add {E : Ω → α → ℝ}
    (hE : Measurable fun p : Ω × α => E p.1 p.2)
    (hprob : ∀ ω, IsProbabilityMeasure (μ.tilted (E ω)))
    {P : Measure Ω} [IsProbabilityMeasure P] {f g : Ω → (ι → α) → ℝ}
    (hg : Measurable fun p : Ω × (ι → α) => g p.1 p.2)
    (hf : Measurable fun p : Ω × (ι → α) => f p.1 p.2) {C : ℝ}
    (hgb : ∀ ω σ, |g ω σ| ≤ C) (hfb : ∀ ω σ, |f ω σ| ≤ C) {err : ℝ}
    (hpt : ∀ ω σ, g ω σ ^ 2 ≤ f ω σ ^ 2 + err) :
    ∫ ω, ∫ σ, g ω σ ^ 2 ∂(Measure.pi fun _ : ι => μ.tilted (E ω)) ∂P ≤
      ∫ ω, ∫ σ, f ω σ ^ 2 ∂(Measure.pi fun _ : ι => μ.tilted (E ω)) ∂P + err := by
  have hP (ω : Ω) : IsProbabilityMeasure (Measure.pi fun _ : ι => μ.tilted (E ω)) := by
    have := hprob ω
    infer_instance
  have hsq {G : Ω → (ι → α) → ℝ} (hGm : Measurable fun p : Ω × (ι → α) => G p.1 p.2)
      (hGb : ∀ ω σ, |G ω σ| ≤ C) :
      (∀ ω, Integrable (fun σ => G ω σ ^ 2) (Measure.pi fun _ : ι => μ.tilted (E ω))) ∧
      Integrable (fun ω => ∫ σ, G ω σ ^ 2 ∂(Measure.pi fun _ : ι => μ.tilted (E ω))) P := by
    have hb (ω : Ω) (σ : ι → α) : |G ω σ ^ 2| ≤ C ^ 2 := by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hGb ω σ) 2
    refine ⟨fun ω => Integrable.of_bound
      (((hGm.comp (measurable_const.prodMk measurable_id)).pow_const 2).aestronglyMeasurable)
      (C ^ 2) (ae_of_all _ fun σ => by simpa only [Real.norm_eq_abs] using hb ω σ), ?_⟩
    exact integrable_integral_pi_tilted (μ := μ) (G := fun ω σ => G ω σ ^ 2) hE hprob
      (hGm.pow_const 2) hb
  obtain ⟨hg2, hgo⟩ := hsq hg hgb
  obtain ⟨hf2, hfo⟩ := hsq hf hfb
  have h1 (ω : Ω) : ∫ σ, g ω σ ^ 2 ∂(Measure.pi fun _ : ι => μ.tilted (E ω)) ≤
      ∫ σ, f ω σ ^ 2 ∂(Measure.pi fun _ : ι => μ.tilted (E ω)) + err := by
    have := hP ω
    have h : ∫ σ, g ω σ ^ 2 ∂(Measure.pi fun _ : ι => μ.tilted (E ω)) ≤
        ∫ σ, (f ω σ ^ 2 + err) ∂(Measure.pi fun _ : ι => μ.tilted (E ω)) :=
      integral_mono (hg2 ω) ((hf2 ω).add (integrable_const err)) (hpt ω)
    rwa [integral_add (hf2 ω) (integrable_const err), integral_const, probReal_univ,
      one_smul] at h
  calc ∫ ω, ∫ σ, g ω σ ^ 2 ∂(Measure.pi fun _ : ι => μ.tilted (E ω)) ∂P
      ≤ ∫ ω, (∫ σ, f ω σ ^ 2 ∂(Measure.pi fun _ : ι => μ.tilted (E ω)) + err) ∂P :=
        integral_mono hgo (hfo.add (integrable_const err)) h1
    _ = ∫ ω, ∫ σ, f ω σ ^ 2 ∂(Measure.pi fun _ : ι => μ.tilted (E ω)) ∂P + err := by
        rw [integral_add hfo (integrable_const err), integral_const, probReal_univ, one_smul]

end MeasureTheory
