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
theorem integral_pi_count_tilted_comp_injective {R R' : Type*} [Finite α] [Nonempty α]
    [Fintype R] [Fintype R'] {ρ : R → R'} (hρ : Function.Injective ρ) (f : α → ℝ)
    (G : (R → α) → ℝ) :
    ∫ τ : R' → α, G (fun r => τ (ρ r)) ∂(Measure.pi fun _ : R' => Measure.count.tilted f) =
      ∫ σ : R → α, G σ ∂(Measure.pi fun _ : R => Measure.count.tilted f) :=
  (measurePreserving_pi_comp_injective (Measure.count.tilted f)
    hρ).integral_comp_of_aestronglyMeasurable Integrable.of_finite.aestronglyMeasurable

/-- **Independence of two blocks of an i.i.d. vector:** a product of a function of the first `m`
coordinates and a function of the last `n` coordinates integrates to the product of the
integrals. -/
theorem integral_pi_fin_add_mul {X : Type*} [MeasurableSpace X] [Finite X]
    [MeasurableSingletonClass X] (μ : Measure X) [IsProbabilityMeasure μ] (m n : ℕ)
    (F : (Fin m → X) → ℝ) (G : (Fin n → X) → ℝ) :
    ∫ σ : Fin (m + n) → X, F (fun i => σ (Fin.castAdd n i)) * G (fun j => σ (Fin.natAdd m j))
        ∂(Measure.pi fun _ : Fin (m + n) => μ) =
      (∫ a : Fin m → X, F a ∂(Measure.pi fun _ : Fin m => μ)) *
        ∫ b : Fin n → X, G b ∂(Measure.pi fun _ : Fin n => μ) := by
  let e : Fin m ⊕ Fin n ≃ Fin (m + n) := finSumFinEquiv
  have h1 := measurePreserving_piCongrLeft (fun _ : Fin (m + n) => μ) e
  have h2 := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin m ⊕ Fin n => X)
    (fun _ => μ)
  have hH : ∀ x : Fin m ⊕ Fin n → X,
      F (fun i => (MeasurableEquiv.piCongrLeft (fun _ => X) e x) (Fin.castAdd n i)) *
        G (fun j => (MeasurableEquiv.piCongrLeft (fun _ => X) e x) (Fin.natAdd m j)) =
      F (fun i => x (Sum.inl i)) * G (fun j => x (Sum.inr j)) := fun x => by
    have hl : ∀ i, (MeasurableEquiv.piCongrLeft (fun _ => X) e x) (Fin.castAdd n i) =
        x (Sum.inl i) := fun i => by
      have := Equiv.piCongrLeft_apply_apply (fun _ => X) e x (Sum.inl i)
      rw [finSumFinEquiv_apply_left] at this
      exact this
    have hr : ∀ j, (MeasurableEquiv.piCongrLeft (fun _ => X) e x) (Fin.natAdd m j) =
        x (Sum.inr j) := fun j => by
      have := Equiv.piCongrLeft_apply_apply (fun _ => X) e x (Sum.inr j)
      rw [finSumFinEquiv_apply_right] at this
      exact this
    simp only [hl, hr]
  rw [← h1.integral_comp_of_aestronglyMeasurable
    (g := fun σ : Fin (m + n) → X => F (fun i => σ (Fin.castAdd n i)) *
      G (fun j => σ (Fin.natAdd m j))) Integrable.of_finite.aestronglyMeasurable]
  simp only [hH]
  have h3 := h2.integral_comp_of_aestronglyMeasurable
    (g := fun p : (Fin m → X) × (Fin n → X) => F p.1 * G p.2)
    Integrable.of_finite.aestronglyMeasurable
  rw [integral_prod_mul] at h3
  exact h3

/-- **Two-replica marginal.** A function of two distinct replicas of an `R`-replica Gibbs average
has the same average as under two independent replicas. -/
theorem integral_pi_count_tilted_pair {R : Type*} [Finite α] [Nonempty α] [Fintype R]
    {a b : R} (hab : a ≠ b)
    (f : α → ℝ) (H : α → α → ℝ) :
    ∫ τ : R → α, H (τ a) (τ b) ∂(Measure.pi fun _ : R => Measure.count.tilted f) =
      ∫ σ : Fin 2 → α, H (σ 0) (σ 1) ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted f) := by
  have hρ : Function.Injective (![a, b] : Fin 2 → R) := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all [Ne.symm hab]
  simpa using integral_pi_count_tilted_comp_injective hρ f
    (fun σ : Fin 2 → α => H (σ 0) (σ 1))

/-- **Moving one replica to a fresh one.** If `F` does not depend on the replica `k`, then the
average of `F · K(σ_i, σ_k)` equals that of `F · K(σ_i, σ_{x₀})`, where `x₀` is a replica outside
the range of the injection `e` and `i ≠ k`. -/
theorem integral_pi_count_tilted_replace_replica {R R' : Type*} [Finite α] [Nonempty α]
    [Finite R] [Fintype R'] [DecidableEq R] {e : R → R'} (he : Function.Injective e) {x₀ : R'}
    (hx₀ : ∀ r, e r ≠ x₀) {i k : R} (hik : i ≠ k) (f : α → ℝ) (F : (R → α) → ℝ)
    (hF : ∀ σ x, F (Function.update σ k x) = F σ) (K : α → α → ℝ) :
    ∫ τ : R' → α, F (fun r => τ (e r)) * K (τ (e i)) (τ (e k))
        ∂(Measure.pi fun _ : R' => Measure.count.tilted f) =
      ∫ τ : R' → α, F (fun r => τ (e r)) * K (τ (e i)) (τ x₀)
        ∂(Measure.pi fun _ : R' => Measure.count.tilted f) := by
  have := Fintype.ofFinite R
  have he' : Function.Injective (Function.update e k x₀) := by
    intro r r' h
    by_cases hr : r = k <;> by_cases hr' : r' = k
    · rw [hr, hr']
    · subst hr
      simp only [Function.update_self, Function.update_of_ne hr'] at h
      exact absurd h.symm (hx₀ r')
    · subst hr'
      simp only [Function.update_self, Function.update_of_ne hr] at h
      exact absurd h (hx₀ r)
    · simp only [Function.update_of_ne hr, Function.update_of_ne hr'] at h
      exact he h
  have h1 := integral_pi_count_tilted_comp_injective he f
    (fun σ : R → α => F σ * K (σ i) (σ k))
  have h2 := integral_pi_count_tilted_comp_injective he' f
    (fun σ : R → α => F σ * K (σ i) (σ k))
  refine h1.trans (h2.symm.trans (integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)))
  have hc : (fun r => τ (Function.update e k x₀ r)) =
      Function.update (fun r => τ (e r)) k (τ x₀) := Function.comp_update τ e k x₀
  simp only [hc, hF, Function.update_self, Function.update_of_ne hik]


/-- **Four replicas and a covariance:** for the Gibbs measure of an energy `A`, the average over
four independent replicas of `(σ¹_i - σ²_i)(σ¹_j - σ²_j)(σ³_i - σ⁴_i)(σ³_j - σ⁴_j)` is
`4 (⟨σ_i σ_j⟩ - ⟨σ_i⟩⟨σ_j⟩)²` (the identity behind Corollary 1.8.6). -/
theorem integral_four_replicas_cov_sq {M : ℕ} (A : (Fin M → ℤˣ) → ℝ) (i j : Fin M) :
    ∫ τ : Fin 4 → Fin M → ℤˣ,
        ((((τ 0 i : ℤˣ) : ℝ) - ((τ 1 i : ℤˣ) : ℝ)) * (((τ 0 j : ℤˣ) : ℝ) - ((τ 1 j : ℤˣ) : ℝ))) *
          ((((τ 2 i : ℤˣ) : ℝ) - ((τ 3 i : ℤˣ) : ℝ)) *
            (((τ 2 j : ℤˣ) : ℝ) - ((τ 3 j : ℤˣ) : ℝ)))
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted A) =
      4 * ((∫ x : Fin M → ℤˣ, ((x i : ℤˣ) : ℝ) * ((x j : ℤˣ) : ℝ) ∂(Measure.count.tilted A)) -
        (∫ x : Fin M → ℤˣ, ((x i : ℤˣ) : ℝ) ∂(Measure.count.tilted A)) *
          ∫ x : Fin M → ℤˣ, ((x j : ℤˣ) : ℝ) ∂(Measure.count.tilted A)) ^ 2 := by
  set μ : Measure (Fin M → ℤˣ) := Measure.count.tilted A with hμ
  let b : (Fin 2 → Fin M → ℤˣ) → ℝ := fun ρ =>
    (((ρ 0 i : ℤˣ) : ℝ) - ((ρ 1 i : ℤˣ) : ℝ)) * (((ρ 0 j : ℤˣ) : ℝ) - ((ρ 1 j : ℤˣ) : ℝ))
  have h4 := integral_pi_fin_add_mul μ 2 2 b b
  have hb : ∫ ρ : Fin 2 → Fin M → ℤˣ, b ρ ∂(Measure.pi fun _ : Fin 2 => μ) =
      2 * ((∫ x : Fin M → ℤˣ, ((x i : ℤˣ) : ℝ) * ((x j : ℤˣ) : ℝ) ∂μ) -
        (∫ x : Fin M → ℤˣ, ((x i : ℤˣ) : ℝ) ∂μ) * ∫ x : Fin M → ℤˣ, ((x j : ℤˣ) : ℝ) ∂μ) := by
    let Θ : (Fin M → ℤˣ) → (Fin M → ℤˣ) → ℝ := fun x y =>
      (((x i : ℤˣ) : ℝ) - ((y i : ℤˣ) : ℝ)) * (((x j : ℤˣ) : ℝ) - ((y j : ℤˣ) : ℝ))
    have hbΘ : ∫ ρ : Fin 2 → Fin M → ℤˣ, b ρ ∂(Measure.pi fun _ : Fin 2 => μ) =
        ∫ ρ : Fin 2 → Fin M → ℤˣ, Θ (ρ 0) (ρ 1) ∂(Measure.pi fun _ : Fin 2 => μ) := rfl
    rw [hbΘ, integral_pi_fin_two]
    have hm1 : ∫ y : Fin M → ℤˣ, (1 : ℝ) ∂μ = 1 := by simp [hμ]
    have e : ∀ x, ∫ y, Θ x y ∂μ = (((x i : ℤˣ) : ℝ) * ((x j : ℤˣ) : ℝ)) -
        ((x i : ℤˣ) : ℝ) * (∫ y : Fin M → ℤˣ, ((y j : ℤˣ) : ℝ) ∂μ) -
        ((x j : ℤˣ) : ℝ) * (∫ y : Fin M → ℤˣ, ((y i : ℤˣ) : ℝ) ∂μ) +
        ∫ y : Fin M → ℤˣ, ((y i : ℤˣ) : ℝ) * ((y j : ℤˣ) : ℝ) ∂μ := fun x => by
      have : (fun y => Θ x y) = fun y => (((x i : ℤˣ) : ℝ) * ((x j : ℤˣ) : ℝ)) * 1 -
          ((x i : ℤˣ) : ℝ) * ((y j : ℤˣ) : ℝ) - ((x j : ℤˣ) : ℝ) * ((y i : ℤˣ) : ℝ) +
          ((y i : ℤˣ) : ℝ) * ((y j : ℤˣ) : ℝ) := funext fun y => by simp only [Θ]; ring
      rw [this, integral_add (Integrable.of_finite) Integrable.of_finite,
        integral_sub Integrable.of_finite Integrable.of_finite,
        integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul,
        integral_const_mul, integral_const_mul, hm1]
      ring
    simp only [e]
    rw [integral_add Integrable.of_finite Integrable.of_finite,
      integral_sub Integrable.of_finite Integrable.of_finite,
      integral_sub Integrable.of_finite Integrable.of_finite, integral_mul_const,
      integral_mul_const]
    simp only [integral_const, probReal_univ, one_smul]
    ring
  rw [hb] at h4
  exact h4.trans (by ring)

end SpinGlasses
