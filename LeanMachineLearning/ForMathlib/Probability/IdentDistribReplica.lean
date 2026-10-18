/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Measure.LocallyFiniteKernel
public import Mathlib.Probability.IdentDistrib

/-!
# Replica integrals of identically distributed random measures

If two random measures have the same law and are a.s. finite on each set of an exhaustion `C`,
then every finite family of `n`-fold integrals `∫⁻ Φᵢ d(M.restrict U)^{⊗n}` has the same joint
law for both. This is Lemma 2.3-style invariance in its order-free form: no enumeration of the
points of the random measure is needed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω Ω' α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α]
  {P : Measure Ω} {Q : Measure Ω'} {C : ℕ → Set α}

/-- **Equality in law of replica integrals.** -/
theorem IdentDistrib.lintegral_pi_restrict {X : Ω → Measure α} {Y : Ω' → Measure α}
    (h : IdentDistrib X Y P Q) (hC : ∀ k, MeasurableSet (C k))
    (hX : ∀ᵐ ω ∂P, ∀ k, X ω (C k) < ∞) (hY : ∀ᵐ ω ∂Q, ∀ k, Y ω (C k) < ∞) (n : ι → ℕ)
    {Φ : (i : ι) → (Fin (n i) → α) → ℝ≥0∞} (hΦ : ∀ i, Measurable (Φ i)) :
    IdentDistrib
      (fun ω i => ∫⁻ q, Φ i q ∂Measure.pi fun _ : Fin (n i) => (X ω).restrict (⋃ k, C k))
      (fun ω i => ∫⁻ q, Φ i q ∂Measure.pi fun _ : Fin (n i) => (Y ω).restrict (⋃ k, C k))
      P Q := by
  choose F hFm hF using fun i => exists_measurable_lintegral_pi_restrict hC (n i) (hΦ i)
  have hFv : Measurable fun (M : Measure α) (i : ι) => F i M := measurable_pi_iff.2 hFm
  have h1 := h.comp hFv
  have hXF : (fun ω i =>
      ∫⁻ q, Φ i q ∂Measure.pi fun _ : Fin (n i) => (X ω).restrict (⋃ k, C k)) =ᵐ[P]
      (fun M i => F i M) ∘ X := by
    filter_upwards [hX] with ω hω
    funext i
    exact (hF i _ hω).symm
  have hYF : (fun ω i =>
      ∫⁻ q, Φ i q ∂Measure.pi fun _ : Fin (n i) => (Y ω).restrict (⋃ k, C k)) =ᵐ[Q]
      (fun M i => F i M) ∘ Y := by
    filter_upwards [hY] with ω hω
    funext i
    exact (hF i _ hω).symm
  exact (IdentDistrib.of_ae_eq (hFv.comp_aemeasurable h.aemeasurable_fst) hXF.symm).symm.trans
    (h1.trans (IdentDistrib.of_ae_eq (hFv.comp_aemeasurable h.aemeasurable_snd) hYF.symm))

end ProbabilityTheory
