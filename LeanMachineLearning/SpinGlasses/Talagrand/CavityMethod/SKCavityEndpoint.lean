/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityGaussian
public import LeanMachineLearning.SpinGlasses.GaussianInterpolationReplica

/-!
# The coupled endpoint of the cavity path

The old-pair and new-edge Gaussian blocks are the original SK disorder in law.
At angle zero the scalar cavity Gaussian disappears, and the path energy is
exactly the enlarged SK energy, with the same normalization on both blocks.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- At the coupled endpoint, averaging a replica observable over the split old
and new Gaussian disorder and the unused scalar Gaussian gives its SK average.
This statement holds for every replica number, including zero. -/
theorem integral_sk_cavity_coupled_endpoint (N n : ℕ) (β h : ℝ)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    (∫ g' : FinPairs N → ℝ, ∫ g : Fin N → ℝ, ∫ _z : ℝ,
      ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
          (fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N,
                g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
            (Real.sqrt (N + 1))⁻¹ * β * (a (Fin.last N) : ℝ) *
              (∑ i : Fin N, g i * (a i.castSucc : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ)))
      ∂(gaussianReal 0 1)
      ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    ∫ g : FinPairs (N + 1) → ℝ,
      ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
          (fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1),
                g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  let F : (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ := fun w =>
    ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        (fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs N,
              w.1 p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
          (Real.sqrt (N + 1))⁻¹ * β * (a (Fin.last N) : ℝ) *
            (∑ i : Fin N, w.2 i * (a i.castSucc : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ)))
  let E : ((FinPairs N → ℝ) × (Fin N → ℝ)) → (Fin (N + 1) → ℤˣ) → ℝ :=
    fun w a => (Real.sqrt (N + 1))⁻¹ * β *
      (∑ p : FinPairs N,
        w.1 p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
      (Real.sqrt (N + 1))⁻¹ * β * (a (Fin.last N) : ℝ) *
        (∑ i : Fin N, w.2 i * (a i.castSucc : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
  have hFE : F = fun w => ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E w)) := rfl
  have hFm : Measurable F := by
    have hm : ∀ a : Fin (N + 1) → ℤˣ, Measurable (fun w => E w a) := by
      intro a
      dsimp [E]
      fun_prop
    rw [hFE]
    exact measurable_integral_pi_count_tilted hm fun _ => measurable_const
  have hFi : Integrable F ((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin N => gaussianReal 0 1)) := by
    let M : ℝ := ∑ σ : Fin n → Fin (N + 1) → ℤˣ, |f σ|
    have hb : ∀ w, |F w| ≤ M := fun w => by
      dsimp [F]
      exact abs_integral_pi_count_tilted_le _ (fun σ => Finset.single_le_sum
        (fun τ hτ => abs_nonneg (f τ)) (Finset.mem_univ σ))
    exact Integrable.of_bound hFm.aestronglyMeasurable M (ae_of_all _ fun w => by
      simpa only [Real.norm_eq_abs] using hb w)
  have heq (g : FinPairs (N + 1) → ℝ) :
      F (fun p => g (⟨(p.val.1.castSucc, p.val.2.castSucc),
          Fin.castSucc_lt_castSucc_iff.mpr p.property⟩ : FinPairs (N + 1)),
        fun i => g (⟨(i.castSucc, Fin.last N),
          Fin.castSucc_lt_last i⟩ : FinPairs (N + 1))) =
      ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
          (fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1),
                g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))) := by
    dsimp [F]
    congr 1
    exact congrArg (fun E : (Fin (N + 1) → ℤˣ) → ℝ =>
      Measure.pi fun _ : Fin n => Measure.count.tilted E)
      (funext fun a => sk_cavity_energy_coupled_eq N β h g a)
  simp only [integral_const, probReal_univ, one_smul]
  rw [← integral_prod F hFi]
  change (∫ w, F w ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
    (Measure.pi fun _ : Fin N => gaussianReal 0 1))) = _
  rw [← integral_comp_sk_cavity_disorder N F]
  simp_rw [heq]

end SpinGlasses
