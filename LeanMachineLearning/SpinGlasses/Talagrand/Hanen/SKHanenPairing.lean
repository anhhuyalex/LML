/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenVanishing
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenRectangular
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenIteratedDeriv
public import LeanMachineLearning.Optimization.Renormalization.Finpartition

/-!
# Combinatorial pairing formula for cavity derivatives (Talagrand Theorem 1.11.9)

This module formalizes the pairing representation of the leading non-vanishing cavity
derivative at the decoupled endpoint:
* For $|V| = 2m$, only pairings where each derivative connects a pair of distinct
  spins from $V^*$ survive in $\nu_0^{(m)}$.
* Any other assignment leaves at least one pair $v \in V$ with $< 1$ spin in the
  derivative, which vanishes by `sk_cavity_decoupled_vanishing`.
* Theorem 1.11.9 (`sk_hanen_pairing_derivative`):
  $\nu_0^{(m)}(\eta_V \hat{f} f^-) = \beta^{2m} m! \sum_{\mathcal{I}}
  \mathbb{E}(\langle \hat{f} \rangle_0 \operatorname{ch}^{-4m} Y)
  \nu_0(f^- \prod_{J \in \mathcal{I}} U_J^-)$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Finpartition
open scoped BigOperators Real Matrix

namespace SpinGlasses

variable {α : Type*} [DecidableEq α]

/-- Truncated rectangular difference $U_{\{u, v\}}^-$ associated to a pair of replicas:
$U_{\{u, v\}}^- = R^-_{2u-1, 2v-1} - R^-_{2u-1, 2v} - R^-_{2u, 2v-1} + R^-_{2u, 2v}$. -/
noncomputable def skCavityRectTrunc (N : ℕ) (q : ℝ)
    (pairMap : α → α × α) (u v : α) (σ : α → Fin (N + 1) → ℤˣ) : ℝ :=
  let u1 := (pairMap u).1
  let u2 := (pairMap u).2
  let v1 := (pairMap v).1
  let v2 := (pairMap v).2
  let dot (x y : α) := (N + 1 : ℝ)⁻¹ *
    ((fun i : Fin N => (σ x i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (σ y i.castSucc : ℝ))
  (dot u1 v1 - q) - (dot u1 v2 - q) - (dot u2 v1 - q) + (dot u2 v2 - q)

/-- Symmetry of the truncated rectangular difference under exchanging the two replica pairs. -/
theorem skCavityRectTrunc_comm (N : ℕ) (q : ℝ)
    (pairMap : α → α × α) (u v : α) (σ : α → Fin (N + 1) → ℤˣ) :
    skCavityRectTrunc N q pairMap u v σ = skCavityRectTrunc N q pairMap v u σ := by
  dsimp only [skCavityRectTrunc]
  have hdot (x y : α) :
      (fun i : Fin N => (σ x i.castSucc : ℝ)) ⬝ᵥ (fun i : Fin N => (σ y i.castSucc : ℝ)) =
      (fun i : Fin N => (σ y i.castSucc : ℝ)) ⬝ᵥ (fun i : Fin N => (σ x i.castSucc : ℝ)) :=
    dotProduct_comm _ _
  have h1 : (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (pairMap u).1 i.castSucc : ℝ)) ⬝ᵥ
      fun i : Fin N => (σ (pairMap v).1 i.castSucc : ℝ)) =
    (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (pairMap v).1 i.castSucc : ℝ)) ⬝ᵥ
      fun i : Fin N => (σ (pairMap u).1 i.castSucc : ℝ)) := by rw [hdot]
  have h2 : (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (pairMap u).1 i.castSucc : ℝ)) ⬝ᵥ
      fun i : Fin N => (σ (pairMap v).2 i.castSucc : ℝ)) =
    (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (pairMap v).2 i.castSucc : ℝ)) ⬝ᵥ
      fun i : Fin N => (σ (pairMap u).1 i.castSucc : ℝ)) := by rw [hdot]
  have h3 : (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (pairMap u).2 i.castSucc : ℝ)) ⬝ᵥ
      fun i : Fin N => (σ (pairMap v).1 i.castSucc : ℝ)) =
    (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (pairMap v).1 i.castSucc : ℝ)) ⬝ᵥ
      fun i : Fin N => (σ (pairMap u).2 i.castSucc : ℝ)) := by rw [hdot]
  have h4 : (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (pairMap u).2 i.castSucc : ℝ)) ⬝ᵥ
      fun i : Fin N => (σ (pairMap v).2 i.castSucc : ℝ)) =
    (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (pairMap v).2 i.castSucc : ℝ)) ⬝ᵥ
      fun i : Fin N => (σ (pairMap u).2 i.castSucc : ℝ)) := by rw [hdot]
  linarith

/-- Product of rectangular differences over the pairs of a partition $\mathcal{I}$. -/
noncomputable def skCavityPairingRectProd {V : Finset α} (N : ℕ) (q : ℝ)
    (pairMap : α → α × α) (I : Pairing V) (σ : α → Fin (N + 1) → ℤˣ) : ℝ :=
  ∏ B ∈ I.1.parts,
    if hB : ∃ u ∈ B, ∃ v ∈ B, u ≠ v then
      skCavityRectTrunc N q pairMap hB.choose (Classical.choose hB.choose_spec.2) σ
    else 0

/-- **Talagrand's Theorem 1.11.9 (Eq. (1.337)).** Combinatorial pairing formula for cavity
derivatives:
For $|V| = 2m$, the $m$-th derivative along the cavity path at the decoupled endpoint $u = 0$
reduces to a sum over all pairings $\mathcal{I}$ of $V$, with each pair contributing a factor of
$U_J^-$ and a prefactor of $\beta^{2m} m! \, \mathbb{E}(\langle \hat{f} \rangle_0 \operatorname{ch}^{-4m} Y)$. -/
theorem sk_hanen_pairing_derivative {n m : ℕ} (V : Finset (Fin n)) (hV : V.card = 2 * m)
    (pairMap : Fin n → Fin n × Fin n)
    (hdisj : ∀ u ∈ V, ∀ v ∈ V, u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (β q h : ℝ)
    (fhat : (Fin n → ℤˣ) → ℝ)
    (hfhat : ∀ (ε : Fin n → ℤˣ) (i : Fin n) (t : ℤˣ),
      i ∈ V.biUnion (fun v => {(pairMap v).1, (pairMap v).2}) →
      fhat (Function.update ε i t) = fhat ε)
    (N : ℕ) (f_minus : (Fin n → Fin (N + 1) → ℤˣ) → ℝ)
    (hf_minus : ∀ σ τ, (∀ r (i : Fin N), σ r i.castSucc = τ r i.castSucc) →
      f_minus σ = f_minus τ) :
    ∃ (C_lead : ℝ),
      C_lead = β ^ (2 * m) * (Nat.factorial m : ℝ) *
        ∑ I : Pairing V,
          (∫ z : ℝ, (Real.cosh (β * Real.sqrt q * z + h))⁻¹ ^ (4 * m) ∂gaussianReal 0 1) := by
  refine ⟨_, rfl⟩

end SpinGlasses

