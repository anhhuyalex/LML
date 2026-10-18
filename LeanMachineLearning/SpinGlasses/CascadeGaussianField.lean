/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeReplicaSum
public import LeanMachineLearning.SpinGlasses.PoissonDirichletIdentities

/-!
# The Gaussian field of a Ruelle cascade

Let `ℓ` be an array of i.i.d. standard Gaussians indexed by the vertices `v` of the tree and the
children `m` of `v`. The field `g(α) = ∑ᵢ σᵢ ℓ(α|ᵢ, αᵢ)` on the leaves `α : Fin r → ℕ` is a
centred Gaussian process with covariance `E g(α) g(β) = ∑_{i < α ∧ β} σᵢ²`, because the labels of
two leaves at level `i` are the same coordinate of `ℓ` exactly when the leaves agree up to and
including level `i`. With this field the countable Gaussian integration by parts of
`GaussianIBPCountable.lean` applies to the Gibbs measure of the cascade.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SpinGlasses

/-- The coordinate of the label array read by the `i`-th step of the leaf `α`. -/
theorem coordinate_eq_iff {r : ℕ} (α β : Fin r → ℕ) (i j : Fin r) :
    ((⟨i, Fin.take i i.isLt.le α⟩ : Σ p : ℕ, Fin p → ℕ), α i) =
      ((⟨j, Fin.take j j.isLt.le β⟩ : Σ p : ℕ, Fin p → ℕ), β j) ↔
      i = j ∧ i.val < (prefixOverlap α β).val := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have hij : i = j := Fin.ext (congrArg Sigma.fst h1)
    subst hij
    have htake : Fin.take i i.isLt.le α = Fin.take i i.isLt.le β := eq_of_heq (Sigma.mk.inj h1).2
    refine ⟨rfl, ?_⟩
    refine Nat.lt_of_succ_le (le_prefixOverlap α β (i.val + 1) i.isLt (fun k hk => ?_))
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
    · exact congrFun htake ⟨k, hk⟩
    · have : k = i := Fin.ext hk
      subst this
      exact h2
  · rintro ⟨rfl, hi⟩
    have htake : Fin.take i i.isLt.le α = Fin.take i i.isLt.le β :=
      (take_eq_take_iff_le_prefixOverlap i.isLt.le α β).2 hi.le
    rw [htake, prefixOverlap_agree α β i hi]

variable {r : ℕ} (σ : ℕ → ℝ)

/-- The i.i.d. standard Gaussian label array. -/
theorem isGaussianProcess_labelArray :
    IsGaussianProcess (fun (c : (Σ p : ℕ, Fin p → ℕ) × ℕ)
        (ℓ : (Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ) => ℓ c.1 c.2)
      (Measure.infinitePi fun _ : Σ p : ℕ, Fin p → ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) := by
  have hi : iIndepFun (fun (c : (Σ p : ℕ, Fin p → ℕ) × ℕ)
        (ℓ : (Σ p : ℕ, Fin p → ℕ) → ℕ → ℝ) => ℓ c.1 c.2)
      (Measure.infinitePi fun _ : Σ p : ℕ, Fin p → ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) :=
    iIndepFun_uncurry_infinitePi'
      (μ := fun _ : Σ p : ℕ, Fin p → ℕ => fun _ : ℕ => gaussianReal 0 1)
      (X := fun _ _ x => x) (by fun_prop)
  exact isGaussianProcess_of_iIndepFun_gaussianReal hi fun c =>
    hasLaw_eval_infinitePi_infinitePi (fun _ _ => gaussianReal 0 1) c.1 c.2

end SpinGlasses
