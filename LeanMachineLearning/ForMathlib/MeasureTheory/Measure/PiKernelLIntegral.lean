/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Measurability of `n`-fold integrals against a kernel

For an s-finite kernel `κ : Kernel A α` whose values are σ-finite, the `n`-fold integral
`a ↦ ∫⁻ q, Φ (a, q) ∂Measure.pi (fun _ : Fin n => κ a)` of a jointly measurable function is
measurable in the parameter `a`. Mathlib has a `Kernel.pi` neither for this nor for
`Measure.pi`, and `Measurable.lintegral_kernel_prod_right'` only treats one factor.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

variable {A α : Type*} [MeasurableSpace A] [MeasurableSpace α]

/-- **Measurability of `n`-fold integrals.** The `n`-fold power integral of a jointly measurable
function against a kernel with σ-finite values is measurable in the parameter. Proved by peeling
off the last coordinate with `measurePreserving_piFinSuccAbove`. -/
theorem Measurable.lintegral_pi_kernel (κ : Kernel A α) [IsSFiniteKernel κ]
    [∀ a, SigmaFinite (κ a)] (n : ℕ) {Φ : A × (Fin n → α) → ℝ≥0∞} (hΦ : Measurable Φ) :
    Measurable fun a => ∫⁻ q, Φ (a, q) ∂Measure.pi fun _ : Fin n => κ a := by
  induction n with
  | zero =>
    have h0 : ∀ a, (Measure.pi fun _ : Fin 0 => κ a) = Measure.dirac isEmptyElim :=
      fun a => Measure.pi_of_empty _ _
    have h1 : ∀ a, ∫⁻ q, Φ (a, q) ∂Measure.pi (fun _ : Fin 0 => κ a) =
        Φ (a, isEmptyElim) := fun a => by
      rw [h0]
      exact lintegral_dirac' _ (hΦ.comp measurable_prodMk_left)
    simp_rw [h1]
    exact hΦ.comp (measurable_id.prodMk measurable_const)
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) (Fin.last n)
    have hmp : ∀ a, MeasurePreserving e (Measure.pi fun _ : Fin (n + 1) => κ a)
        ((κ a).prod (Measure.pi fun _ : Fin n => κ a)) := fun a =>
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => κ a) (Fin.last n)
    have hΨ : Measurable fun z : (A × (Fin n → α)) × α => Φ (z.1.1, e.symm (z.2, z.1.2)) :=
      hΦ.comp ((measurable_fst.comp measurable_fst).prodMk
        (e.symm.measurable.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
    have key : ∀ a, ∫⁻ q, Φ (a, q) ∂Measure.pi (fun _ : Fin (n + 1) => κ a) =
        ∫⁻ q', ∫⁻ x, Φ (a, e.symm (x, q')) ∂κ a ∂Measure.pi fun _ : Fin n => κ a := by
      intro a
      have h := (hmp a).lintegral_comp_emb e.measurableEmbedding
        (fun z => Φ (a, e.symm z))
      simp only [MeasurableEquiv.symm_apply_apply] at h
      rw [h, lintegral_prod_symm]
      exact (hΦ.comp (measurable_const.prodMk (e.symm.measurable))).aemeasurable
    simp_rw [key]
    exact ih (Φ := fun p => ∫⁻ x, Φ (p.1, e.symm (x, p.2)) ∂κ p.1)
      (Measurable.lintegral_kernel_prod_right' (κ := Kernel.comap κ Prod.fst measurable_fst) hΨ)

end MeasureTheory
