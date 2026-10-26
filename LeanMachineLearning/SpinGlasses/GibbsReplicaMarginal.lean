/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.Pi
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.MeasurePreservingSymmetry
public import LeanMachineLearning.SpinGlasses.GaussianIBP

/-!
# Reindexing and marginals of replica Gibbs averages

An `R`-replica Gibbs average is an integral against the product `Measure.pi` of copies of
`Measure.count.tilted f`. Relabelling the replicas leaves it unchanged, and a function of two
distinct replicas integrates to the two-replica average.
-/

@[expose] public section

open MeasureTheory Finset

namespace SpinGlasses

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- Reindexing the configuration space along an equivalence transports an `R`-replica Gibbs
average. -/
theorem integral_pi_count_tilted_equiv {β γ R : Type*} [Finite β] [Finite γ] [Fintype R]
    [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace γ]
    [MeasurableSingletonClass γ] (e : β ≃ γ) (f : γ → ℝ) (Ψ : (R → γ) → ℝ) :
    ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted f) =
      ∫ σ : R → β, Ψ (fun r => e (σ r))
        ∂(Measure.pi fun _ : R => Measure.count.tilted fun b => f (e b)) := by
  classical
  have := Fintype.ofFinite β
  have := Fintype.ofFinite γ
  rw [integral_pi_count_tilted, integral_pi_count_tilted]
  have hZ : (∑ b : β, Real.exp (f (e b))) = ∑ c : γ, Real.exp (f c) :=
    e.sum_comp fun c => Real.exp (f c)
  simp_rw [hZ]
  exact ((Equiv.piCongrRight fun _ : R => e).sum_comp fun σ : R → γ =>
    (∏ r, Real.exp (f (σ r)) / ∑ c : γ, Real.exp (f c)) * Ψ σ).symm

/-- **Replica relabelling.** An `R`-replica Gibbs average is invariant under an equivalence of the
replica index type. -/
theorem integral_pi_count_tilted_reindex {R R' : Type*} [Finite α] [Fintype R] [Fintype R']
    (e : R ≃ R') (f : α → ℝ) (G : (R → α) → ℝ) :
    ∫ τ, G τ ∂(Measure.pi fun _ : R => Measure.count.tilted f) =
      ∫ σ : R' → α, G (fun r => σ (e r)) ∂(Measure.pi fun _ : R' => Measure.count.tilted f) := by
  classical
  have := Fintype.ofFinite α
  rw [integral_pi_count_tilted, integral_pi_count_tilted]
  refine ((Equiv.arrowCongr e.symm (Equiv.refl α)).sum_comp fun τ : R → α =>
    (∏ r, Real.exp (f (τ r)) / ∑ b, Real.exp (f b)) * G τ).symm.trans
    (Finset.sum_congr rfl fun σ _ => ?_)
  congr 1
  exact Equiv.prod_comp e (fun r' => Real.exp (f (σ r')) / ∑ b, Real.exp (f b))

/-- **Marginal along an injection of the replicas.** An observable of the replicas `ρ r`
(`ρ : R → R'` injective) has the same average under `R'` independent replicas as under `R`. -/
theorem integral_pi_count_tilted_comp_injective {R R' : Type*} [Finite α] [Nonempty α] [Fintype R]
    [Fintype R'] {ρ : R → R'} (hρ : Function.Injective ρ) (f : α → ℝ) (G : (R → α) → ℝ) :
    ∫ τ : R' → α, G (fun r => τ (ρ r)) ∂(Measure.pi fun _ : R' => Measure.count.tilted f) =
      ∫ σ : R → α, G σ ∂(Measure.pi fun _ : R => Measure.count.tilted f) := by
  exact (measurePreserving_pi_comp_injective (Measure.count.tilted f)
    hρ).integral_comp_of_aestronglyMeasurable Integrable.of_finite.aestronglyMeasurable

/-- **Two-replica marginal.** A function of two distinct replicas of an `R`-replica Gibbs average
has the same average as under two independent replicas. -/
theorem integral_pi_count_tilted_pair {R : Type*} [Finite α] [Nonempty α] [Fintype R]
    {a b : R} (hab : a ≠ b)
    (f : α → ℝ) (H : α → α → ℝ) :
    ∫ τ : R → α, H (τ a) (τ b) ∂(Measure.pi fun _ : R => Measure.count.tilted f) =
      ∫ σ : Fin 2 → α, H (σ 0) (σ 1) ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted f) := by
  classical
  have := Fintype.ofFinite α
  rw [integral_pi_count_tilted, integral_pi_fin_two_count_tilted]
  set w : α → ℝ := fun x => Real.exp (f x) / ∑ b, Real.exp (f b) with hw
  have hw1 : ∑ x, w x = 1 := by
    simp only [hw, ← Finset.sum_div]
    exact div_self (Finset.sum_pos (fun x _ => Real.exp_pos _) Finset.univ_nonempty).ne'
  have hfiber (p : α × α) :
      ∑ τ ∈ Finset.univ.filter (fun τ : R → α => (τ a, τ b) = p), ∏ r, w (τ r) = w p.1 * w p.2 := by
    have hset : Finset.univ.filter (fun τ : R → α => (τ a, τ b) = p) =
        Fintype.piFinset fun r =>
          if r = a then {p.1} else if r = b then {p.2} else Finset.univ := by
      ext τ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, Prod.ext_iff]
      constructor
      · rintro ⟨h1, h2⟩ r
        by_cases hra : r = a
        · simp [hra, h1]
        · by_cases hrb : r = b
          · subst hrb
            simp [Ne.symm hab, h2]
          · simp [hra, hrb]
      · intro h
        refine ⟨?_, ?_⟩
        · simpa using h a
        · simpa [hab.symm] using h b
    rw [hset, ← Finset.prod_univ_sum]
    rw [Fintype.prod_eq_mul a b hab]
    · simp [hab.symm]
    · intro r hr
      simp [hr.1, hr.2, hw1]
  calc _ = ∑ p : α × α, ∑ τ ∈ Finset.univ.filter (fun τ : R → α => (τ a, τ b) = p),
        (∏ r, w (τ r)) * H (τ a) (τ b) :=
        (Finset.sum_fiberwise Finset.univ (fun τ : R → α => (τ a, τ b))
          fun τ => (∏ r, w (τ r)) * H (τ a) (τ b)).symm
    _ = ∑ p : α × α, w p.1 * w p.2 * H p.1 p.2 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        calc _ = ∑ τ ∈ Finset.univ.filter (fun τ : R → α => (τ a, τ b) = p),
              (∏ r, w (τ r)) * H p.1 p.2 :=
              Finset.sum_congr rfl fun τ hτ => by
                obtain ⟨h1, h2⟩ := Prod.ext_iff.1 (Finset.mem_filter.1 hτ).2
                simp only at h1 h2
                rw [h1, h2]
          _ = w p.1 * w p.2 * H p.1 p.2 := by rw [← Finset.sum_mul, hfiber]
    _ = _ := by rw [Fintype.sum_prod_type]

end SpinGlasses
