/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Extend

/-! # Extending a continuous derivative to a closed interval -/

@[expose] public section

open Filter Set
open scoped Topology

/-- A continuous interior derivative formula extends to both ends of a closed interval. -/
theorem hasDerivWithinAt_Icc_of_continuous_derivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a < b) (F G : ℝ → E)
    (hF : Continuous F) (hG : Continuous G)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt F (G x) x) :
    ∀ x ∈ Icc a b, HasDerivWithinAt F (G x) (Icc a b) x := by
  have hdiff : DifferentiableOn ℝ F (Ioo a b) :=
    fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  intro x hx
  rcases hx.1.eq_or_lt with rfl | hax
  · have heq : deriv F =ᶠ[𝓝[>] a] G := by
      filter_upwards [Ioo_mem_nhdsGT hab] with t ht
      exact (hd t ht).deriv
    have hlim : Tendsto (deriv F) (𝓝[>] a) (𝓝 (G a)) :=
      (hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm
    exact (hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hF.continuousAt.continuousWithinAt
      (Ioo_mem_nhdsGT hab) hlim).mono Icc_subset_Ici_self
  · rcases hx.2.eq_or_lt with rfl | hxb
    · have heq : deriv F =ᶠ[𝓝[<] x] G := by
        filter_upwards [Ioo_mem_nhdsLT hab] with t ht
        exact (hd t ht).deriv
      have hlim : Tendsto (deriv F) (𝓝[<] x) (𝓝 (G x)) :=
        (hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm
      exact (hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hF.continuousAt.continuousWithinAt
        (Ioo_mem_nhdsLT hab) hlim).mono Icc_subset_Iic_self
    · exact (hd x ⟨hax, hxb⟩).hasDerivWithinAt
