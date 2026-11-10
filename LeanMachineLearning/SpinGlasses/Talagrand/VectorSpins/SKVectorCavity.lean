/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.SKVectorEnergy
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaCavity
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The cavity path for vector spins (Talagrand Eq. (1.375), Proposition 1.12.4)

The cavity Hamiltonian interpolates between the `(N+1)`-spin system and the system whose last
spin is decoupled and sees a Gaussian field `Y` of covariance `β² q`, with the deterministic
quadratic compensation `(β²/2)(1-t) ∑ εᵤ εᵥ (ρᵤᵥ - qᵤᵥ)`.  The spin law is an arbitrary probability
measure on a base space `α` with bounded measurable coordinates `ξ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

variable {α D : Type*} [MeasurableSpace α] [Fintype D]

/-- **The cavity Hamiltonian `-H_{N,t}` of Eq. (1.375)**, for `N + 1` spins `ξ (σ i)` (the last
one is the cavity spin), couplings `g` among the old sites, `g'` between the old sites and the
cavity spin, the Gaussian field `Y`, and the matrices `ρ`, `q`. -/
noncomputable def skVectorCavityEnergy (ξ : α → D → ℝ) (N : ℕ) (β : ℝ) (ρ q : D → D → ℝ)
    (g : FinPairs N → ℝ) (g' : Fin N → ℝ) (Y : D → ℝ) (t : ℝ) (σ : Fin (N + 1) → α) : ℝ :=
  (Real.sqrt (N + 1))⁻¹ * β * ∑ p : FinPairs N, g p *
      ∑ u, ξ (σ p.val.1.castSucc) u * ξ (σ p.val.2.castSucc) u +
    ∑ u, ξ (σ (Fin.last N)) u * (Real.sqrt t * ((Real.sqrt (N + 1))⁻¹ * β *
      ∑ i, g' i * ξ (σ i.castSucc) u) + Real.sqrt (1 - t) * Y u) +
    β ^ 2 / 2 * (1 - t) * ∑ u, ∑ v, ξ (σ (Fin.last N)) u * ξ (σ (Fin.last N)) v *
      (ρ u v - q u v)

/-- The cavity overlap `R^{-,u,v}_{σ,τ} = (N+1)⁻¹ ∑_{i<N} σ_{i,u} τ_{i,v}` omitting the last
spin, with the full-system normalization `N + 1`. -/
noncomputable def skVectorCavityOverlap (ξ : α → D → ℝ) (N : ℕ) (σ τ : Fin (N + 1) → α)
    (u v : D) : ℝ :=
  ((N : ℝ) + 1)⁻¹ * ∑ i : Fin N, ξ (σ i.castSucc) u * ξ (τ i.castSucc) v

/-- **Replica bookkeeping of a bilinear form.** For a bilinear kernel
`K(x, y) = ∑ₖₗ wₖₗ Xₖ(x) Xₗ(y)` the product of the replica combinations
`∑ₐ Xₖ(σᵃ) - n Xₖ(σ^{n+1})` and
`∑ₒ Xₗ(σᵒ) - (n+1) Xₗ(σ^{n+2})`, summed against `w`, is the combination of `K` over replica
pairs appearing in Eq. (1.376). -/
theorem sum_replica_combination_mul {A κ R : Type*} [Fintype κ] [Fintype R] (w : κ → κ → ℝ)
    (X : κ → A → ℝ) (σ : Option (Option R) → A) :
    ∑ k, ∑ l, w k l * ((∑ a, X k (σ (some (some a))) - Fintype.card R * X k (σ (some none))) *
        (∑ o : Option R, X l (σ (some o)) - (Fintype.card R + 1) * X l (σ none))) =
      (∑ a, ∑ o : Option R, ∑ k, ∑ l, w k l * X k (σ (some (some a))) * X l (σ (some o))) -
        (Fintype.card R + 1) * ∑ a, ∑ k, ∑ l, w k l * X k (σ (some (some a))) * X l (σ none) -
        Fintype.card R * ∑ o : Option R, ∑ k, ∑ l, w k l * X k (σ (some none)) * X l (σ (some o)) +
        Fintype.card R * (Fintype.card R + 1) *
          ∑ k, ∑ l, w k l * X k (σ (some none)) * X l (σ none) := by
  have key : ∀ k l, w k l * ((∑ a, X k (σ (some (some a))) - Fintype.card R * X k (σ (some none))) *
        (∑ o : Option R, X l (σ (some o)) - (Fintype.card R + 1) * X l (σ none))) =
      (∑ a, ∑ o : Option R, w k l * X k (σ (some (some a))) * X l (σ (some o))) -
        (Fintype.card R + 1) * ∑ a, w k l * X k (σ (some (some a))) * X l (σ none) -
        Fintype.card R * ∑ o : Option R, w k l * X k (σ (some none)) * X l (σ (some o)) +
        Fintype.card R * (Fintype.card R + 1) * (w k l * X k (σ (some none)) * X l (σ none)) := by
    intro k l
    have e1 : ∑ a, ∑ o : Option R, w k l * X k (σ (some (some a))) * X l (σ (some o)) =
        w k l * ((∑ a, X k (σ (some (some a)))) * ∑ o : Option R, X l (σ (some o))) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun o _ => by ring
    have e2 : ∑ a, w k l * X k (σ (some (some a))) * X l (σ none) =
        w k l * ((∑ a, X k (σ (some (some a)))) * X l (σ none)) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    have e3 : ∑ o : Option R, w k l * X k (σ (some none)) * X l (σ (some o)) =
        w k l * (X k (σ (some none)) * ∑ o : Option R, X l (σ (some o))) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun o _ => by ring
    rw [e1, e2, e3]
    ring
  have hcomm : ∀ f : κ → κ → R → Option R → ℝ,
      ∑ k, ∑ l, ∑ a, ∑ o, f k l a o = ∑ a, ∑ o, ∑ k, ∑ l, f k l a o := by
    intro f
    calc ∑ k, ∑ l, ∑ a, ∑ o, f k l a o = ∑ k, ∑ a, ∑ l, ∑ o, f k l a o :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ a, ∑ k, ∑ l, ∑ o, f k l a o := Finset.sum_comm
      _ = ∑ a, ∑ k, ∑ o, ∑ l, f k l a o :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ a, ∑ o, ∑ k, ∑ l, f k l a o :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
  have hc : ∀ (c : ℝ) (f : κ → κ → ℝ), ∑ k, ∑ l, c * f k l = c * ∑ k, ∑ l, f k l := by
    intro c f
    simp only [Finset.mul_sum]
  have h2 : ∀ f : κ → κ → R → ℝ, ∑ k, ∑ l, ∑ a, f k l a = ∑ a, ∑ k, ∑ l, f k l a := by
    intro f
    calc ∑ k, ∑ l, ∑ a, f k l a = ∑ k, ∑ a, ∑ l, f k l a :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ a, ∑ k, ∑ l, f k l a := Finset.sum_comm
  have h3 : ∀ f : κ → κ → Option R → ℝ, ∑ k, ∑ l, ∑ o, f k l o = ∑ o, ∑ k, ∑ l, f k l o := by
    intro f
    calc ∑ k, ∑ l, ∑ o, f k l o = ∑ k, ∑ o, ∑ l, f k l o :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ o, ∑ k, ∑ l, f k l o := Finset.sum_comm
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => key k l]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hc]
  rw [hcomm (fun k l a o => w k l * X k (σ (some (some a))) * X l (σ (some o))),
    h2 (fun k l a => w k l * X k (σ (some (some a))) * X l (σ none)),
    h3 (fun k l o => w k l * X k (σ (some none)) * X l (σ (some o)))]

/-- **The pair kernel of the cavity path**, `(β²/2) ∑ᵤᵥ εᵤ(x) εᵥ(y) (R⁻ᵤᵥ(x, y) - qᵤᵥ)`: the
covariance of the Gaussian field in the two configurations `x`, `y` (Eqs. (1.376)--(1.377)). -/
noncomputable def skVectorCavityKernel (ξ : α → D → ℝ) (N : ℕ) (β : ℝ) (q : D → D → ℝ)
    (x y : Fin (N + 1) → α) : ℝ :=
  β ^ 2 / 2 * ∑ u, ∑ v, ξ (x (Fin.last N)) u * ξ (y (Fin.last N)) v *
    (skVectorCavityOverlap ξ N x y u v - q u v)

omit [MeasurableSpace α] in
/-- The cavity Hamiltonian as a combination of Gaussian coefficients times features, the form
required by the abstract cavity derivative: old couplings with coefficient `1`, new couplings
with coefficient `√t`, the field with coefficient `√(1-t)` and the compensation with `1 - t`. -/
theorem skVectorCavityEnergy_eq_sum (ξ : α → D → ℝ) (N : ℕ) (β : ℝ) (ρ q : D → D → ℝ)
    (g : FinPairs N → ℝ) (g' : Fin N → ℝ) (Y : D → ℝ) (t : ℝ) (σ : Fin (N + 1) → α) :
    skVectorCavityEnergy ξ N β ρ q g g' Y t σ =
      (∑ p : FinPairs N, g p * ((Real.sqrt (N + 1))⁻¹ * β *
          ∑ u, ξ (σ p.val.1.castSucc) u * ξ (σ p.val.2.castSucc) u)) +
        (∑ i : Fin N, Real.sqrt t * g' i * ((Real.sqrt (N + 1))⁻¹ * β *
          ∑ u, ξ (σ (Fin.last N)) u * ξ (σ i.castSucc) u)) +
        (∑ u, Real.sqrt (1 - t) * Y u * ξ (σ (Fin.last N)) u) +
        (1 - t) * (β ^ 2 / 2 * ∑ u, ∑ v, ξ (σ (Fin.last N)) u * ξ (σ (Fin.last N)) v *
          (ρ u v - q u v)) := by
  unfold skVectorCavityEnergy
  have h1 : ∑ u, ξ (σ (Fin.last N)) u * (Real.sqrt t * ((Real.sqrt (N + 1))⁻¹ * β *
      ∑ i, g' i * ξ (σ i.castSucc) u) + Real.sqrt (1 - t) * Y u) =
      (∑ i : Fin N, Real.sqrt t * g' i * ((Real.sqrt (N + 1))⁻¹ * β *
          ∑ u, ξ (σ (Fin.last N)) u * ξ (σ i.castSucc) u)) +
        ∑ u, Real.sqrt (1 - t) * Y u * ξ (σ (Fin.last N)) u := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u _ => by ring
    · exact Finset.sum_congr rfl fun u _ => by ring
  have h3 : (Real.sqrt (N + 1))⁻¹ * β * ∑ p : FinPairs N, g p *
      ∑ u, ξ (σ p.val.1.castSucc) u * ξ (σ p.val.2.castSucc) u =
      ∑ p : FinPairs N, g p * ((Real.sqrt (N + 1))⁻¹ * β *
        ∑ u, ξ (σ p.val.1.castSucc) u * ξ (σ p.val.2.castSucc) u) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [h1, h3]
  ring

/-- `ν_t(G) = 𝔼 ⟨G⟩_t`: the expected average of a function of replicas `Option (Option R)` for
the product of the Gibbs measures of the cavity Hamiltonian (1.375). -/
noncomputable def skVectorCavityAvg {Ω R : Type*} [MeasurableSpace Ω] [Fintype R]
    (μ : Measure α) (ξ : α → D → ℝ) (N : ℕ) (β : ℝ) (ρ q : D → D → ℝ) (P : Measure Ω)
    (g : FinPairs N → Ω → ℝ) (g' : Fin N → Ω → ℝ) (Y : D → Ω → ℝ) (t : ℝ)
    (G : (Option (Option R) → Fin (N + 1) → α) → ℝ) : ℝ :=
  ∫ ω, ∫ σ, G σ ∂(Measure.pi fun _ : Option (Option R) =>
    (Measure.pi fun _ : Fin (N + 1) => μ).tilted
      (skVectorCavityEnergy ξ N β ρ q (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t))
    ∂P

/-- **The coupling features of the cavity Hamiltonian** (Eq. (1.375)): the coefficient of the
Gaussian variable `g_{ij}` (old couplings), `g_{iN}` (new couplings) and `Y_u` (the field). -/
noncomputable def skVectorCavityFeature (ξ : α → D → ℝ) (N : ℕ) (β : ℝ) :
    (FinPairs N ⊕ Fin N) ⊕ D → (Fin (N + 1) → α) → ℝ
  | .inl (.inl p), a => (Real.sqrt (N + 1))⁻¹ * β *
      ∑ u, ξ (a p.val.1.castSucc) u * ξ (a p.val.2.castSucc) u
  | .inl (.inr i), a => (Real.sqrt (N + 1))⁻¹ * β *
      ∑ u, ξ (a (Fin.last N)) u * ξ (a i.castSucc) u
  | .inr u, a => ξ (a (Fin.last N)) u

/-- **The deterministic compensation** `(β²/2) ∑ εᵤ εᵥ (ρᵤᵥ - qᵤᵥ)` of Eq. (1.375), without the
factor `1 - t`. -/
noncomputable def skVectorCavityCompensation (ξ : α → D → ℝ) (N : ℕ) (β : ℝ) (ρ q : D → D → ℝ)
    (a : Fin (N + 1) → α) : ℝ :=
  β ^ 2 / 2 * ∑ u, ∑ v, ξ (a (Fin.last N)) u * ξ (a (Fin.last N)) v * (ρ u v - q u v)

/-- A uniform bound for the features and the compensation. -/
noncomputable def skVectorCavityBound (D : Type*) [Fintype D] (r β : ℝ) (ρ q : D → D → ℝ) : ℝ :=
  |β| * Fintype.card D * r + Real.sqrt r + β ^ 2 / 2 * ∑ u, ∑ v, r * |ρ u v - q u v|

omit [MeasurableSpace α] in
/-- The cavity Hamiltonian in the form `∑ₖ sₖ(t) Zₖ Xₖ + c(t) X'` required by the abstract cavity
derivative. -/
theorem skVectorCavityEnergy_eq_features (ξ : α → D → ℝ) (N : ℕ) (β : ℝ) (ρ q : D → D → ℝ)
    (g : FinPairs N → ℝ) (g' : Fin N → ℝ) (Y : D → ℝ) (t : ℝ) (a : Fin (N + 1) → α) :
    skVectorCavityEnergy ξ N β ρ q g g' Y t a =
      ∑ k : (FinPairs N ⊕ Fin N) ⊕ D,
        Sum.elim (Sum.elim (fun _ => (1 : ℝ)) fun _ => Real.sqrt t) (fun _ => Real.sqrt (1 - t)) k *
          Sum.elim (Sum.elim g g') Y k * skVectorCavityFeature ξ N β k a +
        (1 - t) * skVectorCavityCompensation ξ N β ρ q a := by
  rw [skVectorCavityEnergy_eq_sum]
  simp only [Fintype.sum_sum_type, skVectorCavityFeature, skVectorCavityCompensation,
    Sum.elim_inl, Sum.elim_inr]
  have hA : ∑ p : FinPairs N, 1 * g p * ((Real.sqrt (N + 1))⁻¹ * β *
      ∑ u, ξ (a p.val.1.castSucc) u * ξ (a p.val.2.castSucc) u) =
      ∑ p : FinPairs N, g p * ((Real.sqrt (N + 1))⁻¹ * β *
        ∑ u, ξ (a p.val.1.castSucc) u * ξ (a p.val.2.castSucc) u) :=
    Finset.sum_congr rfl fun p _ => by ring
  rw [hA]

omit [MeasurableSpace α] in
/-- The new-coupling features multiply to the cavity overlap: `∑ᵢ Xᵢ(x) Xᵢ(y)` is
`β² ∑ᵤᵥ εᵤ(x) εᵥ(y) R⁻ᵤᵥ(x, y)`; the factor `(N+1)⁻¹` of the overlap is the square of the
coupling normalization. -/
theorem sum_skVectorCavityFeature_new_mul (ξ : α → D → ℝ) (N : ℕ) (β : ℝ)
    (x y : Fin (N + 1) → α) :
    ∑ i : Fin N, skVectorCavityFeature ξ N β (.inl (.inr i)) x *
        skVectorCavityFeature ξ N β (.inl (.inr i)) y =
      β ^ 2 * ∑ u, ∑ v, ξ (x (Fin.last N)) u * ξ (y (Fin.last N)) v *
        skVectorCavityOverlap ξ N x y u v := by
  have hc : (Real.sqrt ((N : ℝ) + 1))⁻¹ * (Real.sqrt ((N : ℝ) + 1))⁻¹ = ((N : ℝ) + 1)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  simp only [skVectorCavityFeature, skVectorCavityOverlap]
  have h1 : ∀ i : Fin N, (Real.sqrt ((N : ℝ) + 1))⁻¹ * β *
      (∑ u, ξ (x (Fin.last N)) u * ξ (x i.castSucc) u) *
      ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β * ∑ v, ξ (y (Fin.last N)) v * ξ (y i.castSucc) v) =
      β ^ 2 * ((N : ℝ) + 1)⁻¹ * ∑ u, ∑ v, ξ (x (Fin.last N)) u * ξ (y (Fin.last N)) v *
        (ξ (x i.castSucc) u * ξ (y i.castSucc) v) := by
    intro i
    have : (Real.sqrt ((N : ℝ) + 1))⁻¹ * β * (∑ u, ξ (x (Fin.last N)) u * ξ (x i.castSucc) u) *
        ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β * ∑ v, ξ (y (Fin.last N)) v * ξ (y i.castSucc) v) =
        ((Real.sqrt ((N : ℝ) + 1))⁻¹ * (Real.sqrt ((N : ℝ) + 1))⁻¹) * β ^ 2 *
          ((∑ u, ξ (x (Fin.last N)) u * ξ (x i.castSucc) u) *
            ∑ v, ξ (y (Fin.last N)) v * ξ (y i.castSucc) v) := by ring
    have e : ∀ u v, ξ (x (Fin.last N)) u * ξ (x i.castSucc) u *
        (ξ (y (Fin.last N)) v * ξ (y i.castSucc) v) =
        ξ (x (Fin.last N)) u * ξ (y (Fin.last N)) v *
          (ξ (x i.castSucc) u * ξ (y i.castSucc) v) := fun u v => by ring
    rw [this, hc, Finset.sum_mul_sum]
    simp only [e]
    ring
  rw [Finset.sum_congr rfl fun i _ => h1 i, ← Finset.mul_sum]
  have hswap : ∑ i : Fin N, ∑ u, ∑ v, ξ (x (Fin.last N)) u * ξ (y (Fin.last N)) v *
      (ξ (x i.castSucc) u * ξ (y i.castSucc) v) =
      ∑ u, ∑ v, ξ (x (Fin.last N)) u * ξ (y (Fin.last N)) v *
        ∑ i : Fin N, ξ (x i.castSucc) u * ξ (y i.castSucc) v := by
    calc _ = ∑ u, ∑ i : Fin N, ∑ v, ξ (x (Fin.last N)) u * ξ (y (Fin.last N)) v *
          (ξ (x i.castSucc) u * ξ (y i.castSucc) v) := by rw [Finset.sum_comm]
      _ = ∑ u, ∑ v, ∑ i : Fin N, ξ (x (Fin.last N)) u * ξ (y (Fin.last N)) v *
          (ξ (x i.castSucc) u * ξ (y i.castSucc) v) :=
        Finset.sum_congr rfl fun u _ => Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by
        rw [Finset.mul_sum]
  rw [hswap, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by ring

omit [MeasurableSpace α] in
/-- **The covariance kernel of the cavity energy.** With the weights
`Wₖₗ = sₖ'(t) sₗ(t) 𝔼[Zₖ Zₗ]` of the cavity path, `∑ₖₗ Wₖₗ Xₖ(x) Xₗ(y)` equals
`(β²/2) ∑ᵤᵥ εᵤ(x) εᵥ(y) (R⁻ᵤᵥ(x, y) - qᵤᵥ)`. -/
theorem sum_skVectorCavityFeature_weighted (ξ : α → D → ℝ) (N : ℕ) (β : ℝ) (q : D → D → ℝ)
    (W : (FinPairs N ⊕ Fin N) ⊕ D → (FinPairs N ⊕ Fin N) ⊕ D → ℝ)
    (h1 : ∀ p l, W (.inl (.inl p)) l = 0)
    (h2 : ∀ i l, W (.inl (.inr i)) l =
      Sum.elim (Sum.elim (fun _ => 0) fun i' => if i = i' then 1 / 2 else 0) (fun _ => 0) l)
    (h3 : ∀ u l, W (.inr u) l =
      Sum.elim (Sum.elim (fun _ => 0) fun _ => 0) (fun v => -(β ^ 2 / 2) * q u v) l)
    (x y : Fin (N + 1) → α) :
    ∑ k, ∑ l, W k l * skVectorCavityFeature ξ N β k x * skVectorCavityFeature ξ N β l y =
      skVectorCavityKernel ξ N β q x y := by
  unfold skVectorCavityKernel
  have hnew := sum_skVectorCavityFeature_new_mul ξ N β x y
  simp only [Fintype.sum_sum_type, h1, h2, h3, Sum.elim_inl, Sum.elim_inr, zero_mul,
    Finset.sum_const_zero, zero_add, ite_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    add_zero]
  have e1 : ∑ i : Fin N, 1 / 2 * skVectorCavityFeature ξ N β (Sum.inl (Sum.inr i)) x *
      skVectorCavityFeature ξ N β (Sum.inl (Sum.inr i)) y =
      1 / 2 * ∑ i : Fin N, skVectorCavityFeature ξ N β (Sum.inl (Sum.inr i)) x *
        skVectorCavityFeature ξ N β (Sum.inl (Sum.inr i)) y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, hnew]
  simp only [skVectorCavityFeature, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring

omit [MeasurableSpace α] [Fintype D] in
theorem skVectorCavityOverlap_comm (ξ : α → D → ℝ) (N : ℕ) (x y : Fin (N + 1) → α) (u v : D) :
    skVectorCavityOverlap ξ N x y u v = skVectorCavityOverlap ξ N y x v u := by
  unfold skVectorCavityOverlap
  congr 1
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

omit [MeasurableSpace α] in
/-- The pair kernel is symmetric when `q` is. -/
theorem skVectorCavityKernel_comm (ξ : α → D → ℝ) (N : ℕ) (β : ℝ) (q : D → D → ℝ)
    (hq : ∀ u v, q u v = q v u) (x y : Fin (N + 1) → α) :
    skVectorCavityKernel ξ N β q x y = skVectorCavityKernel ξ N β q y x := by
  unfold skVectorCavityKernel
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
  rw [skVectorCavityOverlap_comm ξ N x y u v, hq u v]
  ring

omit [MeasurableSpace α] in
/-- On the diagonal the compensation turns `q` into `ρ` in the kernel: this is why the diagonal
self-overlaps of Eq. (1.376) are measured against `ρ`. -/
theorem skVectorCavityKernel_diag_sub (ξ : α → D → ℝ) (N : ℕ) (β : ℝ) (ρ q : D → D → ℝ)
    (x : Fin (N + 1) → α) :
    skVectorCavityKernel ξ N β q x x - skVectorCavityCompensation ξ N β ρ q x =
      β ^ 2 / 2 * ∑ u, ∑ v, ξ (x (Fin.last N)) u * ξ (x (Fin.last N)) v *
        (skVectorCavityOverlap ξ N x x u v - ρ u v) := by
  unfold skVectorCavityKernel skVectorCavityCompensation
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun v _ => by ring

section Features

variable {ξ : α → D → ℝ} (hξ : ∀ u, Measurable (fun a => ξ a u)) {r : ℝ} (hr : 0 ≤ r)
  (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r)
include hξ

theorem measurable_skVectorCavityFeature (N : ℕ) (β : ℝ) (k : (FinPairs N ⊕ Fin N) ⊕ D) :
    Measurable (skVectorCavityFeature ξ N β k) := by
  have hξm : ∀ (i : Fin (N + 1)) u, Measurable fun a : Fin (N + 1) → α => ξ (a i) u :=
    fun i u => (hξ u).comp (measurable_pi_apply i)
  rcases k with (p | i) | u
  · change Measurable fun a : Fin (N + 1) → α => (Real.sqrt (N + 1))⁻¹ * β *
      ∑ u, ξ (a p.val.1.castSucc) u * ξ (a p.val.2.castSucc) u
    exact measurable_const.mul (Finset.measurable_sum _ fun u _ => (hξm _ u).mul (hξm _ u))
  · change Measurable fun a : Fin (N + 1) → α => (Real.sqrt (N + 1))⁻¹ * β *
      ∑ u, ξ (a (Fin.last N)) u * ξ (a i.castSucc) u
    exact measurable_const.mul (Finset.measurable_sum _ fun u _ => (hξm _ u).mul (hξm _ u))
  · change Measurable fun a : Fin (N + 1) → α => ξ (a (Fin.last N)) u
    exact hξm _ u

theorem measurable_skVectorCavityCompensation (N : ℕ) (β : ℝ) (ρ q : D → D → ℝ) :
    Measurable (skVectorCavityCompensation ξ N β ρ q) := by
  have hξm : ∀ (i : Fin (N + 1)) u, Measurable fun a : Fin (N + 1) → α => ξ (a i) u :=
    fun i u => (hξ u).comp (measurable_pi_apply i)
  unfold skVectorCavityCompensation
  exact measurable_const.mul (Finset.measurable_sum _ fun u _ => Finset.measurable_sum _
    fun v _ => ((hξm _ u).mul (hξm _ v)).mul measurable_const)

omit [Fintype D] in
theorem measurable_skVectorCavityOverlap (N : ℕ) (u v : D) :
    Measurable fun p : (Fin (N + 1) → α) × (Fin (N + 1) → α) =>
      skVectorCavityOverlap ξ N p.1 p.2 u v := by
  have hξm : ∀ (i : Fin (N + 1)) u, Measurable fun a : Fin (N + 1) → α => ξ (a i) u :=
    fun i u => (hξ u).comp (measurable_pi_apply i)
  unfold skVectorCavityOverlap
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
  exact (((hξm i.castSucc u).comp measurable_fst)).mul ((hξm i.castSucc v).comp measurable_snd)

theorem measurable_skVectorCavityKernel (N : ℕ) (β : ℝ) (q : D → D → ℝ) :
    Measurable fun p : (Fin (N + 1) → α) × (Fin (N + 1) → α) =>
      skVectorCavityKernel ξ N β q p.1 p.2 := by
  have hξm : ∀ (i : Fin (N + 1)) u, Measurable fun a : Fin (N + 1) → α => ξ (a i) u :=
    fun i u => (hξ u).comp (measurable_pi_apply i)
  unfold skVectorCavityKernel skVectorCavityOverlap
  refine measurable_const.mul (Finset.measurable_sum _ fun u _ => Finset.measurable_sum _
    fun v _ => ?_)
  refine (((hξm _ u).comp measurable_fst).mul ((hξm _ v).comp measurable_snd)).mul ?_
  refine (measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)).sub measurable_const
  exact (((hξm i.castSucc u).comp measurable_fst)).mul ((hξm i.castSucc v).comp measurable_snd)

include hr hbound

omit [MeasurableSpace α] hξ in
theorem abs_skVectorCavityFeature_le (N : ℕ) (β : ℝ) (ρ q : D → D → ℝ)
    (k : (FinPairs N ⊕ Fin N) ⊕ D) (a : Fin (N + 1) → α) :
    |skVectorCavityFeature ξ N β k a| ≤ skVectorCavityBound D r β ρ q := by
  have hξb : ∀ a u, |ξ a u| ≤ Real.sqrt r := abs_spin_le ξ hbound
  have hξξ : ∀ a b u v, |ξ a u * ξ b v| ≤ r := abs_spin_mul_le ξ hr hbound
  have hc1 : (Real.sqrt ((N : ℝ) + 1))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]))
  have hc0 : 0 ≤ (Real.sqrt ((N : ℝ) + 1))⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hP1 : 0 ≤ |β| * Fintype.card D * r := by positivity
  have hP3 : 0 ≤ β ^ 2 / 2 * ∑ u, ∑ v, r * |ρ u v - q u v| := by positivity
  have hsumb : ∀ (a b : α) (c : ℝ), 0 ≤ c → c ≤ 1 → |c * β * ∑ u, ξ a u * ξ b u| ≤
      |β| * Fintype.card D * r := by
    intro a b c hc0' hc1'
    have h1 : |∑ u, ξ a u * ξ b u| ≤ Fintype.card D * r :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        ((Finset.sum_le_sum fun u _ => hξξ a b u u).trans (by simp))
    rw [abs_mul, abs_mul, abs_of_nonneg hc0']
    calc c * |β| * |∑ u, ξ a u * ξ b u| ≤ 1 * |β| * (Fintype.card D * r) :=
          mul_le_mul (mul_le_mul hc1' le_rfl (abs_nonneg _) zero_le_one) h1 (abs_nonneg _)
            (by positivity)
      _ = |β| * Fintype.card D * r := by ring
  unfold skVectorCavityBound
  have := Real.sqrt_nonneg r
  rcases k with (p | i) | u
  · have := hsumb (a p.val.1.castSucc) (a p.val.2.castSucc) _ hc0 hc1
    simp only [skVectorCavityFeature]
    linarith
  · have := hsumb (a (Fin.last N)) (a i.castSucc) _ hc0 hc1
    simp only [skVectorCavityFeature]
    linarith
  · have := hξb (a (Fin.last N)) u
    simp only [skVectorCavityFeature]
    linarith

omit [MeasurableSpace α] hξ in
theorem abs_skVectorCavityOverlap_le (N : ℕ) (x y : Fin (N + 1) → α) (u v : D) :
    |skVectorCavityOverlap ξ N x y u v| ≤ r := by
  have hξb : ∀ a u, |ξ a u| ≤ Real.sqrt r := abs_spin_le ξ hbound
  have hξξ : ∀ a b u v, |ξ a u * ξ b v| ≤ r := abs_spin_mul_le ξ hr hbound
  unfold skVectorCavityOverlap
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((N : ℝ) + 1)⁻¹)]
  have h1 : |∑ i : Fin N, ξ (x i.castSucc) u * ξ (y i.castSucc) v| ≤ N * r :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun i _ => hξξ _ _ u v).trans (by simp))
  calc ((N : ℝ) + 1)⁻¹ * |∑ i : Fin N, ξ (x i.castSucc) u * ξ (y i.castSucc) v|
      ≤ ((N : ℝ) + 1)⁻¹ * (N * r) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (N / ((N : ℝ) + 1)) * r := by field_simp
    _ ≤ 1 * r := mul_le_mul_of_nonneg_right ((div_le_one (by positivity)).2 (by linarith)) hr
    _ = r := one_mul r

omit [MeasurableSpace α] hξ in
theorem abs_skVectorCavityKernel_le (N : ℕ) (β : ℝ) (q : D → D → ℝ) (x y : Fin (N + 1) → α) :
    |skVectorCavityKernel ξ N β q x y| ≤ β ^ 2 / 2 * ∑ u, ∑ v, r * (r + |q u v|) := by
  have hξb : ∀ a u, |ξ a u| ≤ Real.sqrt r := abs_spin_le ξ hbound
  have hξξ : ∀ a b u v, |ξ a u * ξ b v| ≤ r := abs_spin_mul_le ξ hr hbound
  unfold skVectorCavityKernel
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ β ^ 2 / 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (hξξ _ _ u v) ((abs_sub _ _).trans
    (add_le_add (abs_skVectorCavityOverlap_le hr hbound N x y u v) le_rfl)) (abs_nonneg _) hr

omit [MeasurableSpace α] hξ in
theorem abs_skVectorCavityCompensation_le (N : ℕ) (β : ℝ) (ρ q : D → D → ℝ)
    (a : Fin (N + 1) → α) :
    |skVectorCavityCompensation ξ N β ρ q a| ≤ skVectorCavityBound D r β ρ q := by
  have hξb : ∀ a u, |ξ a u| ≤ Real.sqrt r := abs_spin_le ξ hbound
  have hξξ : ∀ a b u v, |ξ a u * ξ b v| ≤ r := abs_spin_mul_le ξ hr hbound
  have hP1 : 0 ≤ |β| * Fintype.card D * r := by positivity
  unfold skVectorCavityCompensation skVectorCavityBound
  have h1 : |∑ u, ∑ v, ξ (a (Fin.last N)) u * ξ (a (Fin.last N)) v * (ρ u v - q u v)| ≤
      ∑ u, ∑ v, r * |ρ u v - q u v| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hξξ _ _ u v) (abs_nonneg _)
  have h2 : |β ^ 2 / 2 * ∑ u, ∑ v, ξ (a (Fin.last N)) u * ξ (a (Fin.last N)) v *
      (ρ u v - q u v)| ≤ β ^ 2 / 2 * ∑ u, ∑ v, r * |ρ u v - q u v| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ β ^ 2 / 2)]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have := Real.sqrt_nonneg r
  linarith

end Features

section BoundedIntegrands

variable {R : Type*} [Fintype R] {ξ : α → D → ℝ} (hξ : ∀ u, Measurable (fun a => ξ a u))
  {r : ℝ} (hr : 0 ≤ r) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r) {N : ℕ} {F : (R → Fin (N + 1) → α) → ℝ}
  (hF : Measurable F) {M : ℝ} (hFb : ∀ σ, |F σ| ≤ M)
include hξ hr hbound hF hFb

/-- The integrand of the covariance term of the cavity derivative is bounded and measurable. -/
theorem skVectorCavity_covariance_integrand (β : ℝ) (k l : (FinPairs N ⊕ Fin N) ⊕ D) :
    Measurable (fun σ : Option (Option R) → Fin (N + 1) → α =>
        (F fun a => σ (some (some a))) *
          (∑ a, skVectorCavityFeature ξ N β k (σ (some (some a))) -
            Fintype.card R * skVectorCavityFeature ξ N β k (σ (some none))) *
          (∑ o : Option R, skVectorCavityFeature ξ N β l (σ (some o)) -
            (Fintype.card R + 1) * skVectorCavityFeature ξ N β l (σ none))) ∧
      ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α,
        |(F fun a => σ (some (some a))) *
          (∑ a, skVectorCavityFeature ξ N β k (σ (some (some a))) -
            Fintype.card R * skVectorCavityFeature ξ N β k (σ (some none))) *
          (∑ o : Option R, skVectorCavityFeature ξ N β l (σ (some o)) -
            (Fintype.card R + 1) * skVectorCavityFeature ξ N β l (σ none))| ≤ B := by
  have hfm : Measurable fun σ : Option (Option R) → Fin (N + 1) → α =>
      F fun a => σ (some (some a)) :=
    hF.comp (measurable_pi_iff.2 fun a => measurable_pi_apply _)
  have hKm : ∀ (k : (FinPairs N ⊕ Fin N) ⊕ D) (x : Option (Option R)),
      Measurable fun σ : Option (Option R) → Fin (N + 1) → α =>
        skVectorCavityFeature ξ N β k (σ x) := fun k x =>
    (measurable_skVectorCavityFeature hξ N β k).comp (measurable_pi_apply x)
  have hfb : ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α, |F fun a => σ (some (some a))| ≤ B :=
    ⟨M, fun σ => hFb _⟩
  have hKb : ∀ (k : (FinPairs N ⊕ Fin N) ⊕ D) (x : Option (Option R)),
      ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α,
        |skVectorCavityFeature ξ N β k (σ x)| ≤ B := fun k x =>
    ⟨_, fun σ => abs_skVectorCavityFeature_le hr hbound N β 0 0 k (σ x)⟩
  refine ⟨(hfm.mul ((Finset.measurable_sum _ fun a _ => hKm k _).sub ((hKm k _).const_mul _))).mul
    ((Finset.measurable_sum _ fun o _ => hKm l _).sub ((hKm l _).const_mul _)), ?_⟩
  exact exists_abs_le_mul (exists_abs_le_mul hfb (exists_abs_le_sub
    (exists_abs_le_sum _ fun a _ => hKb k _) (exists_abs_le_mul (exists_abs_le_const _) (hKb k _))))
    (exists_abs_le_sub (exists_abs_le_sum _ fun o _ => hKb l _)
      (exists_abs_le_mul (exists_abs_le_const _) (hKb l _)))

/-- The integrand of the compensation term of the cavity derivative is bounded and
measurable. -/
theorem skVectorCavity_compensation_integrand (β : ℝ) (ρ q : D → D → ℝ) :
    Measurable (fun σ : Option (Option R) → Fin (N + 1) → α =>
        (F fun a => σ (some (some a))) *
          (∑ o : Option R, skVectorCavityCompensation ξ N β ρ q (σ (some o)) -
            (Fintype.card R + 1) * skVectorCavityCompensation ξ N β ρ q (σ none))) ∧
      ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α,
        |(F fun a => σ (some (some a))) *
          (∑ o : Option R, skVectorCavityCompensation ξ N β ρ q (σ (some o)) -
            (Fintype.card R + 1) * skVectorCavityCompensation ξ N β ρ q (σ none))| ≤ B := by
  have hfm : Measurable fun σ : Option (Option R) → Fin (N + 1) → α =>
      F fun a => σ (some (some a)) :=
    hF.comp (measurable_pi_iff.2 fun a => measurable_pi_apply _)
  have hCm : ∀ x : Option (Option R), Measurable fun σ : Option (Option R) → Fin (N + 1) → α =>
      skVectorCavityCompensation ξ N β ρ q (σ x) := fun x =>
    (measurable_skVectorCavityCompensation hξ N β ρ q).comp (measurable_pi_apply x)
  have hfb : ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α, |F fun a => σ (some (some a))| ≤ B :=
    ⟨M, fun σ => hFb _⟩
  have hCb : ∀ x : Option (Option R), ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α,
      |skVectorCavityCompensation ξ N β ρ q (σ x)| ≤ B := fun x =>
    ⟨_, fun σ => abs_skVectorCavityCompensation_le hr hbound N β ρ q (σ x)⟩
  refine ⟨hfm.mul ((Finset.measurable_sum _ fun o _ => hCm _).sub ((hCm _).const_mul _)), ?_⟩
  exact exists_abs_le_mul hfb (exists_abs_le_sub (exists_abs_le_sum _ fun o _ => hCb _)
    (exists_abs_le_mul (exists_abs_le_const _) (hCb _)))

omit [Fintype R] in
/-- The integrands of Eq. (1.376) are bounded and measurable. -/
theorem skVectorCavity_book_integrand (x y : Option (Option R)) (Q : D → D → ℝ)
    (u v : D) :
    Measurable (fun σ : Option (Option R) → Fin (N + 1) → α =>
        (F fun c => σ (some (some c))) * ξ (σ x (Fin.last N)) u * ξ (σ y (Fin.last N)) v *
          (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v)) ∧
      ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α,
        |(F fun c => σ (some (some c))) * ξ (σ x (Fin.last N)) u * ξ (σ y (Fin.last N)) v *
          (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v)| ≤ B := by
  have hfm : Measurable fun σ : Option (Option R) → Fin (N + 1) → α =>
      F fun a => σ (some (some a)) :=
    hF.comp (measurable_pi_iff.2 fun a => measurable_pi_apply _)
  have hεm : ∀ (z : Option (Option R)) w, Measurable fun σ : Option (Option R) →
      Fin (N + 1) → α => ξ (σ z (Fin.last N)) w := fun z w =>
    (hξ w).comp ((measurable_pi_apply (Fin.last N)).comp (measurable_pi_apply z))
  have hεb : ∀ (z : Option (Option R)) w, ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α,
      |ξ (σ z (Fin.last N)) w| ≤ B := fun z w => ⟨Real.sqrt r, fun σ => by
    refine Real.abs_le_sqrt ?_
    exact (Finset.single_le_sum (f := fun w => ξ (σ z (Fin.last N)) w ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ w)).trans (hbound _)⟩
  have hRm : Measurable fun σ : Option (Option R) → Fin (N + 1) → α =>
      skVectorCavityOverlap ξ N (σ x) (σ y) u v :=
    Measurable.comp (g := fun p : (Fin (N + 1) → α) × (Fin (N + 1) → α) =>
      skVectorCavityOverlap ξ N p.1 p.2 u v)
      (f := fun σ : Option (Option R) → Fin (N + 1) → α => (σ x, σ y))
      (measurable_skVectorCavityOverlap hξ N u v)
      ((measurable_pi_apply x).prodMk (measurable_pi_apply y))
  have hfb : ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α, |F fun a => σ (some (some a))| ≤ B :=
    ⟨M, fun σ => hFb _⟩
  refine ⟨((hfm.mul (hεm x u)).mul (hεm y v)).mul (hRm.sub measurable_const), ?_⟩
  exact exists_abs_le_mul (exists_abs_le_mul (exists_abs_le_mul hfb (hεb x u)) (hεb y v))
    (exists_abs_le_sub ⟨r, fun σ => abs_skVectorCavityOverlap_le hr hbound N _ _ u v⟩
      (exists_abs_le_const (Q u v)))

end BoundedIntegrands

/-- The cavity energy is jointly measurable in the Gaussian environment and the configuration. -/
theorem measurable_skVectorCavityEnergy_joint {Ω : Type*} [MeasurableSpace Ω]
    (ξ : α → D → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u)) (N : ℕ) (β : ℝ) (ρ q : D → D → ℝ)
    {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : D → Ω → ℝ}
    (hgm : ∀ p, Measurable (g p)) (hg'm : ∀ i, Measurable (g' i)) (hYm : ∀ u, Measurable (Y u))
    (t : ℝ) :
    Measurable fun x : Ω × (Fin (N + 1) → α) =>
      skVectorCavityEnergy ξ N β ρ q (fun p => g p x.1) (fun i => g' i x.1)
        (fun u => Y u x.1) t x.2 := by
  have hZm : ∀ k, Measurable fun ω => Sum.elim (Sum.elim (fun p => g p ω) fun i => g' i ω)
      (fun u => Y u ω) k := by
    rintro ((p | i) | u)
    · exact hgm p
    · exact hg'm i
    · exact hYm u
  simp_rw [skVectorCavityEnergy_eq_features]
  refine (Finset.measurable_sum _ fun k _ => ?_).add
    (measurable_const.mul ((measurable_skVectorCavityCompensation hξ N β ρ q).comp
      measurable_snd))
  exact (measurable_const.mul ((hZm k).comp measurable_fst)).mul
    ((measurable_skVectorCavityFeature hξ N β k).comp measurable_snd)

/-- The Gibbs measure of the cavity Hamiltonian is a probability measure for every value of the
Gaussian environment. -/
theorem isProbabilityMeasure_skVectorCavityGibbs (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → D → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u)) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r) (N : ℕ) (β : ℝ) (ρ q : D → D → ℝ)
    (g : FinPairs N → ℝ) (g' : Fin N → ℝ) (Y : D → ℝ) (t : ℝ) :
    IsProbabilityMeasure ((Measure.pi fun _ : Fin (N + 1) => μ).tilted
      (skVectorCavityEnergy ξ N β ρ q g g' Y t)) := by
  classical
  have hEm : Measurable (skVectorCavityEnergy ξ N β ρ q g g' Y t) := by
    have : skVectorCavityEnergy ξ N β ρ q g g' Y t = fun a => ∑ k : (FinPairs N ⊕ Fin N) ⊕ D,
        Sum.elim (Sum.elim (fun _ => (1 : ℝ)) fun _ => Real.sqrt t)
          (fun _ => Real.sqrt (1 - t)) k * Sum.elim (Sum.elim g g') Y k *
          skVectorCavityFeature ξ N β k a +
        (1 - t) * skVectorCavityCompensation ξ N β ρ q a :=
      funext fun a => skVectorCavityEnergy_eq_features ξ N β ρ q g g' Y t a
    rw [this]
    exact (Finset.measurable_sum _ fun k _ => measurable_const.mul
      (measurable_skVectorCavityFeature hξ N β k)).add
      (measurable_const.mul (measurable_skVectorCavityCompensation hξ N β ρ q))
  refine isProbabilityMeasure_tilted_of_bound (Eb := ∑ k, |Sum.elim (Sum.elim (fun _ => (1 : ℝ))
      fun _ => Real.sqrt t) (fun _ => Real.sqrt (1 - t)) k * Sum.elim (Sum.elim g g') Y k| *
        skVectorCavityBound D r β ρ q + |1 - t| * skVectorCavityBound D r β ρ q) hEm fun a => ?_
  rw [skVectorCavityEnergy_eq_features]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_skVectorCavityFeature_le hr hbound N β ρ q k a)
      (abs_nonneg _)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_skVectorCavityCompensation_le hr hbound N β ρ q a)
      (abs_nonneg _)

/-- A bounded measurable function of the replicas has an integrable Gibbs average in the random
environment of the cavity path. -/
theorem integrable_skVectorCavityGibbs {Ω R : Type*} [MeasurableSpace Ω] [Fintype R]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → D → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r) (N : ℕ) (β : ℝ) (ρ q : D → D → ℝ)
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : D → Ω → ℝ}
    (hgm : ∀ p, Measurable (g p)) (hg'm : ∀ i, Measurable (g' i)) (hYm : ∀ u, Measurable (Y u))
    (t : ℝ) (G : (Option (Option R) → Fin (N + 1) → α) → ℝ) (hG : Measurable G)
    (hGb : ∃ B, ∀ σ, |G σ| ≤ B) :
    Integrable (fun ω => ∫ σ, G σ ∂(Measure.pi fun _ : Option (Option R) =>
      (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
        (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t))) P := by
  obtain ⟨B, hB⟩ := hGb
  exact integrable_integral_pi_tilted (μ := Measure.pi fun _ : Fin (N + 1) => μ)
    (measurable_skVectorCavityEnergy_joint ξ hξ N β ρ q hgm hg'm hYm t)
    (fun ω => isProbabilityMeasure_skVectorCavityGibbs μ ξ hξ hr hbound N β ρ q _ _ _ t) hG hB

/-- **Proposition 1.12.4 at a fixed environment** (the algebra behind Eq. (1.376)).  For any
probability measure `ν` on configurations of `N + 1` spins, the covariance combination of the cavity
path (weights `W`) minus the compensation combination equals the four groups of Eq. (1.376) for the
`ν`-replica average. -/
theorem skVectorCavity_fixed {R : Type*} [Fintype R] [DecidableEq R]
    (ξ : α → D → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u)) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r) (N : ℕ) (β : ℝ) (ρ q : D → D → ℝ)
    (hq : ∀ u v, q u v = q v u)
    (F : (R → Fin (N + 1) → α) → ℝ) (hF : Measurable F) {M : ℝ} (hFb : ∀ σ, |F σ| ≤ M)
    (ν : Measure (Fin (N + 1) → α)) [IsProbabilityMeasure ν]
    (W : (FinPairs N ⊕ Fin N) ⊕ D → (FinPairs N ⊕ Fin N) ⊕ D → ℝ)
    (h1 : ∀ p l, W (.inl (.inl p)) l = 0)
    (h2 : ∀ i l, W (.inl (.inr i)) l =
      Sum.elim (Sum.elim (fun _ => 0) fun i' => if i = i' then 1 / 2 else 0) (fun _ => 0) l)
    (h3 : ∀ u l, W (.inr u) l =
      Sum.elim (Sum.elim (fun _ => 0) fun _ => 0) (fun v => -(β ^ 2 / 2) * q u v) l) :
    (∑ k, ∑ l, W k l * ∫ σ : Option (Option R) → Fin (N + 1) → α,
        (F fun a => σ (some (some a))) *
          (∑ a, skVectorCavityFeature ξ N β k (σ (some (some a))) -
            Fintype.card R * skVectorCavityFeature ξ N β k (σ (some none))) *
          (∑ o : Option R, skVectorCavityFeature ξ N β l (σ (some o)) -
            (Fintype.card R + 1) * skVectorCavityFeature ξ N β l (σ none))
          ∂(Measure.pi fun _ => ν)) +
      -1 * ∫ σ : Option (Option R) → Fin (N + 1) → α, (F fun a => σ (some (some a))) *
          (∑ o : Option R, skVectorCavityCompensation ξ N β ρ q (σ (some o)) -
            (Fintype.card R + 1) * skVectorCavityCompensation ξ N β ρ q (σ none))
          ∂(Measure.pi fun _ => ν) =
      β ^ 2 / 2 * ∑ a : R, ∑ b : R, ∑ u, ∑ v,
          ∫ σ : Option (Option R) → Fin (N + 1) → α,
            F (fun c => σ (some (some c))) * ξ (σ (some (some a)) (Fin.last N)) u *
              ξ (σ (some (some b)) (Fin.last N)) v *
              (skVectorCavityOverlap ξ N (σ (some (some a))) (σ (some (some b))) u v -
                if a = b then ρ u v else q u v) ∂(Measure.pi fun _ => ν) -
        Fintype.card R * β ^ 2 * ∑ a : R, ∑ u, ∑ v,
          ∫ σ : Option (Option R) → Fin (N + 1) → α,
            F (fun c => σ (some (some c))) * ξ (σ (some (some a)) (Fin.last N)) u *
              ξ (σ (some none) (Fin.last N)) v *
              (skVectorCavityOverlap ξ N (σ (some (some a))) (σ (some none)) u v - q u v)
            ∂(Measure.pi fun _ => ν) -
        Fintype.card R * (β ^ 2 / 2) * ∑ u, ∑ v,
          ∫ σ : Option (Option R) → Fin (N + 1) → α,
            F (fun c => σ (some (some c))) * ξ (σ (some none) (Fin.last N)) u *
              ξ (σ (some none) (Fin.last N)) v *
              (skVectorCavityOverlap ξ N (σ (some none)) (σ (some none)) u v - ρ u v)
            ∂(Measure.pi fun _ => ν) +
        Fintype.card R * (Fintype.card R + 1) / 2 * β ^ 2 * ∑ u, ∑ v,
          ∫ σ : Option (Option R) → Fin (N + 1) → α,
            F (fun c => σ (some (some c))) * ξ (σ (some none) (Fin.last N)) u *
              ξ (σ none (Fin.last N)) v *
              (skVectorCavityOverlap ξ N (σ (some none)) (σ none) u v - q u v)
            ∂(Measure.pi fun _ => ν) := by
  classical
  -- atoms: measurability and boundedness
  have hfm : Measurable fun σ : Option (Option R) → Fin (N + 1) → α =>
      F fun a => σ (some (some a)) :=
    hF.comp (measurable_pi_iff.2 fun a => measurable_pi_apply _)
  have hKm : ∀ (k : (FinPairs N ⊕ Fin N) ⊕ D) (x : Option (Option R)),
      Measurable fun σ : Option (Option R) → Fin (N + 1) → α =>
        skVectorCavityFeature ξ N β k (σ x) := fun k x =>
    (measurable_skVectorCavityFeature hξ N β k).comp (measurable_pi_apply x)
  have hCm : ∀ x : Option (Option R), Measurable fun σ : Option (Option R) → Fin (N + 1) → α =>
      skVectorCavityCompensation ξ N β ρ q (σ x) := fun x =>
    (measurable_skVectorCavityCompensation hξ N β ρ q).comp (measurable_pi_apply x)
  have hfb : ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α, |F fun a => σ (some (some a))| ≤ B :=
    ⟨M, fun σ => hFb _⟩
  have hKb : ∀ (k : (FinPairs N ⊕ Fin N) ⊕ D) (x : Option (Option R)),
      ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α,
        |skVectorCavityFeature ξ N β k (σ x)| ≤ B := fun k x =>
    ⟨_, fun σ => abs_skVectorCavityFeature_le hr hbound N β ρ q k (σ x)⟩
  have hCb : ∀ x : Option (Option R), ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α,
      |skVectorCavityCompensation ξ N β ρ q (σ x)| ≤ B := fun x =>
    ⟨_, fun σ => abs_skVectorCavityCompensation_le hr hbound N β ρ q (σ x)⟩
  -- the integrands of the covariance terms are bounded and measurable
  have hWt_m : ∀ k, Measurable fun σ : Option (Option R) → Fin (N + 1) → α =>
      ∑ a, skVectorCavityFeature ξ N β k (σ (some (some a))) -
        Fintype.card R * skVectorCavityFeature ξ N β k (σ (some none)) := fun k =>
    (Finset.measurable_sum _ fun a _ => hKm k _).sub ((hKm k _).const_mul _)
  have hWt_b : ∀ k, ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α,
      |∑ a, skVectorCavityFeature ξ N β k (σ (some (some a))) -
        Fintype.card R * skVectorCavityFeature ξ N β k (σ (some none))| ≤ B := fun k =>
    exists_abs_le_sub (exists_abs_le_sum _ fun a _ => hKb k _)
      (exists_abs_le_mul (exists_abs_le_const _) (hKb k _))
  have hW'_m : ∀ l, Measurable fun σ : Option (Option R) → Fin (N + 1) → α =>
      ∑ o : Option R, skVectorCavityFeature ξ N β l (σ (some o)) -
        (Fintype.card R + 1) * skVectorCavityFeature ξ N β l (σ none) := fun l =>
    (Finset.measurable_sum _ fun o _ => hKm l _).sub ((hKm l _).const_mul _)
  have hW'_b : ∀ l, ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α,
      |∑ o : Option R, skVectorCavityFeature ξ N β l (σ (some o)) -
        (Fintype.card R + 1) * skVectorCavityFeature ξ N β l (σ none)| ≤ B := fun l =>
    exists_abs_le_sub (exists_abs_le_sum _ fun o _ => hKb l _)
      (exists_abs_le_mul (exists_abs_le_const _) (hKb l _))
  have hg_int : ∀ k l, Integrable (fun σ : Option (Option R) → Fin (N + 1) → α =>
      (F fun a => σ (some (some a))) * (∑ a, skVectorCavityFeature ξ N β k (σ (some (some a))) -
          Fintype.card R * skVectorCavityFeature ξ N β k (σ (some none))) *
        (∑ o : Option R, skVectorCavityFeature ξ N β l (σ (some o)) -
          (Fintype.card R + 1) * skVectorCavityFeature ξ N β l (σ none)))
      (Measure.pi fun _ => ν) := by
    intro k l
    obtain ⟨B, hB⟩ := exists_abs_le_mul (exists_abs_le_mul hfb (hWt_b k)) (hW'_b l)
    exact integrable_of_measurable_bound (((hfm.mul (hWt_m k)).mul (hW'_m l))) hB
  have hstep1 : (∑ k, ∑ l, W k l * ∫ σ : Option (Option R) → Fin (N + 1) → α,
        (F fun a => σ (some (some a))) *
          (∑ a, skVectorCavityFeature ξ N β k (σ (some (some a))) -
            Fintype.card R * skVectorCavityFeature ξ N β k (σ (some none))) *
          (∑ o : Option R, skVectorCavityFeature ξ N β l (σ (some o)) -
            (Fintype.card R + 1) * skVectorCavityFeature ξ N β l (σ none))
          ∂(Measure.pi fun _ => ν)) =
      ∫ σ : Option (Option R) → Fin (N + 1) → α, (F fun a => σ (some (some a))) *
        ∑ k, ∑ l, W k l * ((∑ a, skVectorCavityFeature ξ N β k (σ (some (some a))) -
            Fintype.card R * skVectorCavityFeature ξ N β k (σ (some none))) *
          (∑ o : Option R, skVectorCavityFeature ξ N β l (σ (some o)) -
            (Fintype.card R + 1) * skVectorCavityFeature ξ N β l (σ none)))
          ∂(Measure.pi fun _ => ν) := by
    symm
    have hrew : ∀ σ : Option (Option R) → Fin (N + 1) → α,
        (F fun a => σ (some (some a))) *
          ∑ k, ∑ l, W k l * ((∑ a, skVectorCavityFeature ξ N β k (σ (some (some a))) -
              Fintype.card R * skVectorCavityFeature ξ N β k (σ (some none))) *
            (∑ o : Option R, skVectorCavityFeature ξ N β l (σ (some o)) -
              (Fintype.card R + 1) * skVectorCavityFeature ξ N β l (σ none))) =
        ∑ k, ∑ l, W k l * ((F fun a => σ (some (some a))) *
          (∑ a, skVectorCavityFeature ξ N β k (σ (some (some a))) -
            Fintype.card R * skVectorCavityFeature ξ N β k (σ (some none))) *
          (∑ o : Option R, skVectorCavityFeature ξ N β l (σ (some o)) -
            (Fintype.card R + 1) * skVectorCavityFeature ξ N β l (σ none))) := by
      intro σ
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hrew),
      integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hg_int k l).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => (hg_int k l).const_mul _]
    exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
  have hker : ∀ σ : Option (Option R) → Fin (N + 1) → α,
      ∑ k, ∑ l, W k l * ((∑ a, skVectorCavityFeature ξ N β k (σ (some (some a))) -
            Fintype.card R * skVectorCavityFeature ξ N β k (σ (some none))) *
          (∑ o : Option R, skVectorCavityFeature ξ N β l (σ (some o)) -
            (Fintype.card R + 1) * skVectorCavityFeature ξ N β l (σ none))) =
      ((∑ a, ∑ o : Option R, skVectorCavityKernel ξ N β q (σ (some (some a))) (σ (some o))) -
        (Fintype.card R + 1) * ∑ a, skVectorCavityKernel ξ N β q (σ (some (some a))) (σ none) -
        Fintype.card R * ∑ o : Option R,
          skVectorCavityKernel ξ N β q (σ (some none)) (σ (some o)) +
        Fintype.card R * (Fintype.card R + 1) *
          skVectorCavityKernel ξ N β q (σ (some none)) (σ none)) := by
    intro σ
    rw [sum_replica_combination_mul]
    simp only [sum_skVectorCavityFeature_weighted ξ N β q W h1 h2 h3]
  -- the kernel and the compensation as bounded measurable functions of two (one) replicas
  have hKm := measurable_skVectorCavityKernel hξ N β q
  have hCm' := measurable_skVectorCavityCompensation hξ N β ρ q
  obtain ⟨BK, hBK⟩ : ∃ BK, ∀ x y, |skVectorCavityKernel ξ N β q x y| ≤ BK :=
    ⟨_, abs_skVectorCavityKernel_le hr hbound N β q⟩
  obtain ⟨BC, hBC⟩ : ∃ BC, ∀ x, |skVectorCavityCompensation ξ N β ρ q x| ≤ BC :=
    ⟨_, abs_skVectorCavityCompensation_le hr hbound N β ρ q⟩
  have hKat_m : ∀ x y : Option (Option R), Measurable fun σ : Option (Option R) →
      Fin (N + 1) → α => skVectorCavityKernel ξ N β q (σ x) (σ y) := fun x y =>
    Measurable.comp (g := fun p : (Fin (N + 1) → α) × (Fin (N + 1) → α) =>
      skVectorCavityKernel ξ N β q p.1 p.2)
      (f := fun σ : Option (Option R) → Fin (N + 1) → α => (σ x, σ y)) hKm
      ((measurable_pi_apply x).prodMk (measurable_pi_apply y))
  have hKat_b : ∀ x y : Option (Option R), ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α,
      |skVectorCavityKernel ξ N β q (σ x) (σ y)| ≤ B := fun x y => ⟨BK, fun σ => hBK _ _⟩
  have hpat_m : Measurable fun σ : Option (Option R) → Fin (N + 1) → α =>
      ((∑ a, ∑ o : Option R, skVectorCavityKernel ξ N β q (σ (some (some a))) (σ (some o))) -
        (Fintype.card R + 1) * ∑ a, skVectorCavityKernel ξ N β q (σ (some (some a))) (σ none) -
        Fintype.card R * ∑ o : Option R,
          skVectorCavityKernel ξ N β q (σ (some none)) (σ (some o)) +
        Fintype.card R * (Fintype.card R + 1) *
          skVectorCavityKernel ξ N β q (σ (some none)) (σ none)) :=
    (((Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun o _ => hKat_m _ _).sub
      (measurable_const.mul (Finset.measurable_sum _ fun a _ => hKat_m _ _))).sub
      (measurable_const.mul (Finset.measurable_sum _ fun o _ => hKat_m _ _))).add
      (measurable_const.mul (hKat_m _ _))
  have hpat_b : ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α,
      |((∑ a, ∑ o : Option R, skVectorCavityKernel ξ N β q (σ (some (some a))) (σ (some o))) -
        (Fintype.card R + 1) * ∑ a, skVectorCavityKernel ξ N β q (σ (some (some a))) (σ none) -
        Fintype.card R * ∑ o : Option R,
          skVectorCavityKernel ξ N β q (σ (some none)) (σ (some o)) +
        Fintype.card R * (Fintype.card R + 1) *
          skVectorCavityKernel ξ N β q (σ (some none)) (σ none))| ≤ B :=
    exists_abs_le_add (exists_abs_le_sub (exists_abs_le_sub
      (exists_abs_le_sum _ fun a _ => exists_abs_le_sum _ fun o _ => hKat_b _ _)
      (exists_abs_le_mul (exists_abs_le_const _)
        (exists_abs_le_sum _ fun a _ => hKat_b _ _)))
      (exists_abs_le_mul (exists_abs_le_const _)
        (exists_abs_le_sum _ fun o _ => hKat_b _ _)))
      (exists_abs_le_mul (exists_abs_le_const _) (hKat_b _ _))
  have hcomp_m : Measurable fun σ : Option (Option R) → Fin (N + 1) → α =>
      (∑ o : Option R, skVectorCavityCompensation ξ N β ρ q (σ (some o)) -
        (Fintype.card R + 1) * skVectorCavityCompensation ξ N β ρ q (σ none)) :=
    (Finset.measurable_sum _ fun o _ => hCm _).sub ((hCm _).const_mul _)
  have hcomp_b : ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α,
      |(∑ o : Option R, skVectorCavityCompensation ξ N β ρ q (σ (some o)) -
        (Fintype.card R + 1) * skVectorCavityCompensation ξ N β ρ q (σ none))| ≤ B :=
    exists_abs_le_sub (exists_abs_le_sum _ fun o _ => hCb _)
      (exists_abs_le_mul (exists_abs_le_const _) (hCb _))
  obtain ⟨Bp, hBp⟩ := exists_abs_le_mul hfb hpat_b
  obtain ⟨Bc, hBc⟩ := exists_abs_le_mul hfb hcomp_b
  have hpat_int : Integrable (fun σ : Option (Option R) → Fin (N + 1) → α =>
      (F fun a => σ (some (some a))) *
      ((∑ a, ∑ o : Option R, skVectorCavityKernel ξ N β q (σ (some (some a))) (σ (some o))) -
        (Fintype.card R + 1) * ∑ a, skVectorCavityKernel ξ N β q (σ (some (some a))) (σ none) -
        Fintype.card R * ∑ o : Option R,
          skVectorCavityKernel ξ N β q (σ (some none)) (σ (some o)) +
        Fintype.card R * (Fintype.card R + 1) *
          skVectorCavityKernel ξ N β q (σ (some none)) (σ none)))
      (Measure.pi fun _ : Option (Option R) => ν) :=
    integrable_of_measurable_bound (hfm.mul hpat_m) hBp
  have hcomp_int : Integrable (fun σ : Option (Option R) → Fin (N + 1) → α =>
      (F fun a => σ (some (some a))) *
      (∑ o : Option R, skVectorCavityCompensation ξ N β ρ q (σ (some o)) -
        (Fintype.card R + 1) * skVectorCavityCompensation ξ N β ρ q (σ none)))
      (Measure.pi fun _ : Option (Option R) => ν) :=
    integrable_of_measurable_bound (hfm.mul hcomp_m) hBc
  rw [hstep1, integral_congr_ae (Filter.Eventually.of_forall fun σ => by rw [hker σ]),
    neg_one_mul, ← sub_eq_add_neg, ← integral_sub hpat_int hcomp_int]
  simp_rw [← mul_sub]
  rw [integral_replica_pattern ν F hF hFb (H := skVectorCavityKernel ξ N β q) hKm hBK
    (skVectorCavityKernel_comm ξ N β q hq) (C := skVectorCavityCompensation ξ N β ρ q) hCm' hBC]
  -- bookkeeping: the book integrands are bounded and measurable
  have hbook_int : ∀ (x y : Option (Option R)) (Q : D → D → ℝ) (u v : D),
      Integrable (fun σ : Option (Option R) → Fin (N + 1) → α =>
        (F fun c => σ (some (some c))) * (ξ (σ x (Fin.last N)) u * ξ (σ y (Fin.last N)) v *
          (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v)))
        (Measure.pi fun _ => ν) := by
    intro x y Q u v
    have hεm : ∀ (z : Option (Option R)) w, Measurable fun σ : Option (Option R) →
        Fin (N + 1) → α => ξ (σ z (Fin.last N)) w := fun z w =>
      (hξ w).comp ((measurable_pi_apply (Fin.last N)).comp (measurable_pi_apply z))
    have hεb : ∀ (z : Option (Option R)) w, ∃ B, ∀ σ : Option (Option R) → Fin (N + 1) → α,
        |ξ (σ z (Fin.last N)) w| ≤ B := fun z w => ⟨Real.sqrt r, fun σ => by
      refine Real.abs_le_sqrt ?_
      exact (Finset.single_le_sum (f := fun w => ξ (σ z (Fin.last N)) w ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ w)).trans (hbound _)⟩
    have hRm : Measurable fun σ : Option (Option R) → Fin (N + 1) → α =>
        skVectorCavityOverlap ξ N (σ x) (σ y) u v :=
      Measurable.comp (g := fun p : (Fin (N + 1) → α) × (Fin (N + 1) → α) =>
        skVectorCavityOverlap ξ N p.1 p.2 u v)
        (f := fun σ : Option (Option R) → Fin (N + 1) → α => (σ x, σ y))
        (measurable_skVectorCavityOverlap hξ N u v)
        ((measurable_pi_apply x).prodMk (measurable_pi_apply y))
    have hbm : Measurable fun σ : Option (Option R) → Fin (N + 1) → α =>
        ξ (σ x (Fin.last N)) u * ξ (σ y (Fin.last N)) v *
          (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v) :=
      ((hεm x u).mul (hεm y v)).mul (hRm.sub measurable_const)
    obtain ⟨B, hB⟩ := exists_abs_le_mul hfb (exists_abs_le_mul (exists_abs_le_mul (hεb x u)
      (hεb y v)) (exists_abs_le_sub ⟨r, fun σ => abs_skVectorCavityOverlap_le hr hbound N _ _ u v⟩
        (exists_abs_le_const (Q u v))))
    exact integrable_of_measurable_bound (hfm.mul hbm) hB
  have hconv : ∀ (x y : Option (Option R)) (Q : D → D → ℝ)
      (e : (Option (Option R) → Fin (N + 1) → α) → ℝ),
      (∀ σ : Option (Option R) → Fin (N + 1) → α,
        skVectorCavityKernel ξ N β q (σ x) (σ y) - e σ = β ^ 2 / 2 * ∑ u, ∑ v,
          ξ (σ x (Fin.last N)) u * ξ (σ y (Fin.last N)) v *
            (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v)) →
      ∫ σ : Option (Option R) → Fin (N + 1) → α, (F fun c => σ (some (some c))) *
          (skVectorCavityKernel ξ N β q (σ x) (σ y) - e σ) ∂(Measure.pi fun _ => ν) =
        β ^ 2 / 2 * ∑ u, ∑ v, ∫ σ : Option (Option R) → Fin (N + 1) → α,
          (F fun c => σ (some (some c))) * ξ (σ x (Fin.last N)) u * ξ (σ y (Fin.last N)) v *
            (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v) ∂(Measure.pi fun _ => ν) := by
    intro x y Q e he
    have hpt : ∀ σ : Option (Option R) → Fin (N + 1) → α,
        (F fun c => σ (some (some c))) * (skVectorCavityKernel ξ N β q (σ x) (σ y) - e σ) =
        β ^ 2 / 2 * ∑ u, ∑ v, (F fun c => σ (some (some c))) *
          (ξ (σ x (Fin.last N)) u * ξ (σ y (Fin.last N)) v *
            (skVectorCavityOverlap ξ N (σ x) (σ y) u v - Q u v)) := by
      intro σ
      rw [he σ, mul_left_comm, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul,
      integral_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ => hbook_int x y Q u v]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [integral_finsetSum _ fun v _ => hbook_int x y Q u v]
    refine Finset.sum_congr rfl fun v _ => ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun σ => by ring)
  have g1 : ∀ a b : R, ∫ σ : Option (Option R) → Fin (N + 1) → α,
      (F fun c => σ (some (some c))) *
        (skVectorCavityKernel ξ N β q (σ (some (some a))) (σ (some (some b))) -
          if a = b then skVectorCavityCompensation ξ N β ρ q (σ (some (some a))) else 0)
        ∂(Measure.pi fun _ => ν) =
      β ^ 2 / 2 * ∑ u, ∑ v, ∫ σ : Option (Option R) → Fin (N + 1) → α,
        (F fun c => σ (some (some c))) * ξ (σ (some (some a)) (Fin.last N)) u *
          ξ (σ (some (some b)) (Fin.last N)) v *
          (skVectorCavityOverlap ξ N (σ (some (some a))) (σ (some (some b))) u v -
            if a = b then ρ u v else q u v) ∂(Measure.pi fun _ => ν) := by
    intro a b
    refine hconv _ _ _ _ fun σ => ?_
    by_cases hab : a = b
    · subst hab
      simp only [ite_true]
      exact skVectorCavityKernel_diag_sub ξ N β ρ q _
    · simp only [hab, ite_false, sub_zero]
      rfl
  have g2 : ∀ a : R, ∫ σ : Option (Option R) → Fin (N + 1) → α,
      (F fun c => σ (some (some c))) *
        skVectorCavityKernel ξ N β q (σ (some (some a))) (σ (some none))
        ∂(Measure.pi fun _ => ν) =
      β ^ 2 / 2 * ∑ u, ∑ v, ∫ σ : Option (Option R) → Fin (N + 1) → α,
        (F fun c => σ (some (some c))) * ξ (σ (some (some a)) (Fin.last N)) u *
          ξ (σ (some none) (Fin.last N)) v *
          (skVectorCavityOverlap ξ N (σ (some (some a))) (σ (some none)) u v - q u v)
        ∂(Measure.pi fun _ => ν) := by
    intro a
    have := hconv (some (some a)) (some none) q (fun _ => 0) fun σ => by
      simp only [sub_zero]; rfl
    simpa only [sub_zero] using this
  have g3 : ∫ σ : Option (Option R) → Fin (N + 1) → α, (F fun c => σ (some (some c))) *
        (skVectorCavityKernel ξ N β q (σ (some none)) (σ (some none)) -
          skVectorCavityCompensation ξ N β ρ q (σ (some none))) ∂(Measure.pi fun _ => ν) =
      β ^ 2 / 2 * ∑ u, ∑ v, ∫ σ : Option (Option R) → Fin (N + 1) → α,
        (F fun c => σ (some (some c))) * ξ (σ (some none) (Fin.last N)) u *
          ξ (σ (some none) (Fin.last N)) v *
          (skVectorCavityOverlap ξ N (σ (some none)) (σ (some none)) u v - ρ u v)
        ∂(Measure.pi fun _ => ν) :=
    hconv (some none) (some none) ρ (fun σ => skVectorCavityCompensation ξ N β ρ q (σ (some none)))
      fun σ => skVectorCavityKernel_diag_sub ξ N β ρ q _
  have g4 : ∫ σ : Option (Option R) → Fin (N + 1) → α, (F fun c => σ (some (some c))) *
        skVectorCavityKernel ξ N β q (σ (some none)) (σ none) ∂(Measure.pi fun _ => ν) =
      β ^ 2 / 2 * ∑ u, ∑ v, ∫ σ : Option (Option R) → Fin (N + 1) → α,
        (F fun c => σ (some (some c))) * ξ (σ (some none) (Fin.last N)) u *
          ξ (σ none (Fin.last N)) v *
          (skVectorCavityOverlap ξ N (σ (some none)) (σ none) u v - q u v)
        ∂(Measure.pi fun _ => ν) := by
    have := hconv (some none) none q (fun _ => 0) fun σ => by
      simp only [sub_zero]; rfl
    simpa only [sub_zero] using this
  simp only [g1, g2, g3, g4, ← Finset.mul_sum]
  ring

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Exchanging the expectation with the weighted covariance sum, given a pointwise identity. -/
theorem integral_weighted_sum_sub {K : Type*} [Fintype K] (W : K → K → ℝ) (T : K → K → Ω → ℝ)
    (T' B : Ω → ℝ) (hT : ∀ k l, Integrable (T k l) P) (hT' : Integrable T' P)
    (h : ∀ ω, ∑ k, ∑ l, W k l * T k l ω + -1 * T' ω = B ω) :
    ∑ k, ∑ l, W k l * ∫ ω, T k l ω ∂P + -1 * ∫ ω, T' ω ∂P = ∫ ω, B ω ∂P := by
  have h1 : ∀ k, Integrable (fun ω => ∑ l, W k l * T k l ω) P := fun k =>
    integrable_finsetSum _ fun l _ => (hT k l).const_mul _
  have : ∫ ω, B ω ∂P = ∫ ω, (∑ k, ∑ l, W k l * T k l ω + -1 * T' ω) ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => (h ω).symm)
  have e : ∑ k, ∑ l, W k l * ∫ ω, T k l ω ∂P = ∫ ω, ∑ k, ∑ l, W k l * T k l ω ∂P := by
    rw [integral_finsetSum _ fun k _ => h1 k]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => (hT k l).const_mul _]
    exact Finset.sum_congr rfl fun l _ => (integral_const_mul _ _).symm
  rw [this, integral_add (integrable_finsetSum _ fun k _ => h1 k) (hT'.const_mul _),
    integral_const_mul, e]

/-- The expectation of the four groups of Eq. (1.376). -/
theorem integral_four_groups {R D : Type*} [Fintype R] [Fintype D] (c₁ c₂ c₃ c₄ : ℝ)
    (I₁ : R → R → D → D → Ω → ℝ) (I₂ : R → D → D → Ω → ℝ) (I₃ I₄ : D → D → Ω → ℝ)
    (h₁ : ∀ a b u v, Integrable (I₁ a b u v) P) (h₂ : ∀ a u v, Integrable (I₂ a u v) P)
    (h₃ : ∀ u v, Integrable (I₃ u v) P) (h₄ : ∀ u v, Integrable (I₄ u v) P) :
    ∫ ω, (c₁ * ∑ a, ∑ b, ∑ u, ∑ v, I₁ a b u v ω - c₂ * ∑ a, ∑ u, ∑ v, I₂ a u v ω -
        c₃ * ∑ u, ∑ v, I₃ u v ω + c₄ * ∑ u, ∑ v, I₄ u v ω) ∂P =
      c₁ * ∑ a, ∑ b, ∑ u, ∑ v, ∫ ω, I₁ a b u v ω ∂P - c₂ * ∑ a, ∑ u, ∑ v, ∫ ω, I₂ a u v ω ∂P -
        c₃ * ∑ u, ∑ v, ∫ ω, I₃ u v ω ∂P + c₄ * ∑ u, ∑ v, ∫ ω, I₄ u v ω ∂P := by
  have e₁ : Integrable (fun ω => ∑ a, ∑ b, ∑ u, ∑ v, I₁ a b u v ω) P :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
      integrable_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ => h₁ a b u v
  have e₂ : Integrable (fun ω => ∑ a, ∑ u, ∑ v, I₂ a u v ω) P :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun u _ =>
      integrable_finsetSum _ fun v _ => h₂ a u v
  have e₃ : Integrable (fun ω => ∑ u, ∑ v, I₃ u v ω) P :=
    integrable_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ => h₃ u v
  have e₄ : Integrable (fun ω => ∑ u, ∑ v, I₄ u v ω) P :=
    integrable_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ => h₄ u v
  have s2 : ∀ (f : D → D → Ω → ℝ), (∀ u v, Integrable (f u v) P) →
      ∫ ω, ∑ u, ∑ v, f u v ω ∂P = ∑ u, ∑ v, ∫ ω, f u v ω ∂P := by
    intro f hf
    rw [integral_finsetSum Finset.univ fun u _ => integrable_finsetSum _ fun v _ => hf u v]
    exact Finset.sum_congr rfl fun u _ => integral_finsetSum Finset.univ fun v _ => hf u v
  have s3 : ∀ (f : R → D → D → Ω → ℝ), (∀ a u v, Integrable (f a u v) P) →
      ∫ ω, ∑ a, ∑ u, ∑ v, f a u v ω ∂P = ∑ a, ∑ u, ∑ v, ∫ ω, f a u v ω ∂P := by
    intro f hf
    rw [integral_finsetSum Finset.univ fun a _ => integrable_finsetSum _ fun u _ =>
      integrable_finsetSum _ fun v _ => hf a u v]
    exact Finset.sum_congr rfl fun a _ => s2 (f a) (hf a)
  have s4 : ∫ ω, ∑ a, ∑ b, ∑ u, ∑ v, I₁ a b u v ω ∂P =
      ∑ a, ∑ b, ∑ u, ∑ v, ∫ ω, I₁ a b u v ω ∂P := by
    rw [integral_finsetSum Finset.univ fun a _ => integrable_finsetSum _ fun b _ =>
      integrable_finsetSum _ fun u _ => integrable_finsetSum _ fun v _ => h₁ a b u v]
    exact Finset.sum_congr rfl fun a _ => s3 (I₁ a) (h₁ a)
  rw [integral_four_combination (e₁.const_mul c₁) (e₂.const_mul c₂) (e₃.const_mul c₃)
    (e₄.const_mul c₄), integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, s4, s3 I₂ h₂, s2 I₃ h₃, s2 I₄ h₄]

end Assembly

/-- **Proposition 1.12.4** (the derivative of the cavity path, Eq. (1.376)).  `F` is a bounded
measurable function of `n = |R|` configurations; the replicas `n+1` and `n+2` of the book are
`some none` and `none`.  The Gaussian couplings `g`, `g'` and the field `Y` are jointly Gaussian
with `E g g' = δ`, `E Y Y = β² q` and `Y` independent of the couplings; no boundedness of the
Gaussian parameters is assumed. -/
theorem hasDerivAt_skVectorCavity {Ω R : Type*} [MeasurableSpace Ω] [Fintype R] [DecidableEq R]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → D → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r) (N : ℕ) (β : ℝ) (ρ q : D → D → ℝ)
    (hq : ∀ u v, q u v = q v u)
    (F : (R → Fin (N + 1) → α) → ℝ) (hF : Measurable F) {M : ℝ} (hM : 0 ≤ M)
    (hFb : ∀ σ, |F σ| ≤ M)
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : D → Ω → ℝ}
    (hG : HasGaussianLaw (fun ω (k : (FinPairs N ⊕ Fin N) ⊕ D) =>
      Sum.elim (Sum.elim (fun p => g p ω) fun i => g' i ω) (fun u => Y u ω) k) P)
    (hgm : ∀ p, Measurable (g p)) (hg'm : ∀ i, Measurable (g' i)) (hYm : ∀ u, Measurable (Y u))
    (hgg : ∀ k l : FinPairs N ⊕ Fin N,
      ∫ ω, Sum.elim (fun p => g p ω) (fun i => g' i ω) k *
        Sum.elim (fun p => g p ω) (fun i => g' i ω) l ∂P = if k = l then 1 else 0)
    (hYY : ∀ u v, ∫ ω, Y u ω * Y v ω ∂P = β ^ 2 * q u v)
    (hgY : ∀ (k : FinPairs N ⊕ Fin N) u,
      ∫ ω, Sum.elim (fun p => g p ω) (fun i => g' i ω) k * Y u ω ∂P = 0)
    (hg0 : ∀ p, ∫ ω, g p ω ∂P = 0) (hg'0 : ∀ i, ∫ ω, g' i ω ∂P = 0)
    (hY0 : ∀ u, ∫ ω, Y u ω ∂P = 0)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun s => ∫ ω, ∫ σ : R → Fin (N + 1) → α, F σ ∂(Measure.pi fun _ : R =>
        (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
          (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) s)) ∂P)
      (β ^ 2 / 2 * ∑ a : R, ∑ b : R, ∑ u, ∑ v,
          skVectorCavityAvg μ ξ N β ρ q P g g' Y t (fun σ =>
            F (fun c => σ (some (some c))) * ξ (σ (some (some a)) (Fin.last N)) u *
              ξ (σ (some (some b)) (Fin.last N)) v *
              (skVectorCavityOverlap ξ N (σ (some (some a))) (σ (some (some b))) u v -
                if a = b then ρ u v else q u v)) -
        Fintype.card R * β ^ 2 * ∑ a : R, ∑ u, ∑ v,
          skVectorCavityAvg μ ξ N β ρ q P g g' Y t (fun σ =>
            F (fun c => σ (some (some c))) * ξ (σ (some (some a)) (Fin.last N)) u *
              ξ (σ (some none) (Fin.last N)) v *
              (skVectorCavityOverlap ξ N (σ (some (some a))) (σ (some none)) u v - q u v)) -
        Fintype.card R * (β ^ 2 / 2) * ∑ u, ∑ v,
          skVectorCavityAvg μ ξ N β ρ q P g g' Y t (fun σ =>
            F (fun c => σ (some (some c))) * ξ (σ (some none) (Fin.last N)) u *
              ξ (σ (some none) (Fin.last N)) v *
              (skVectorCavityOverlap ξ N (σ (some none)) (σ (some none)) u v - ρ u v)) +
        Fintype.card R * (Fintype.card R + 1) / 2 * β ^ 2 * ∑ u, ∑ v,
          skVectorCavityAvg μ ξ N β ρ q P g g' Y t (fun σ =>
            F (fun c => σ (some (some c))) * ξ (σ (some none) (Fin.last N)) u *
              ξ (σ none (Fin.last N)) v *
              (skVectorCavityOverlap ξ N (σ (some none)) (σ none) u v - q u v))) t := by
  classical
  set Z : (FinPairs N ⊕ Fin N) ⊕ D → Ω → ℝ := fun k ω =>
    Sum.elim (Sum.elim (fun p => g p ω) fun i => g' i ω) (fun u => Y u ω) k with hZdef
  set sc : (FinPairs N ⊕ Fin N) ⊕ D → ℝ → ℝ := fun k r =>
    Sum.elim (Sum.elim (fun _ => 1) fun _ => Real.sqrt r) (fun _ => Real.sqrt (1 - r)) k
    with hsc
  set sc' : (FinPairs N ⊕ Fin N) ⊕ D → ℝ → ℝ := fun k r =>
    Sum.elim (Sum.elim (fun _ => 0) fun _ => 1 / (2 * Real.sqrt r))
      (fun _ => -(1 / (2 * Real.sqrt (1 - r)))) k with hsc'
  have hZmeas : ∀ k, Measurable (Z k) := by
    rintro ((p | i) | u)
    · exact hgm p
    · exact hg'm i
    · exact hYm u
  set m : ℝ := min t (1 - t) / 2 with hmdef
  have hm : 0 < m := by
    have := lt_min ht0 (sub_pos.2 ht1)
    simp only [hmdef]; positivity
  have hmt : m ≤ t / 2 := by
    have := min_le_left t (1 - t); simp only [hmdef]; linarith
  have hmt' : m ≤ (1 - t) / 2 := by
    have := min_le_right t (1 - t); simp only [hmdef]; linarith
  have hball : ∀ r ∈ Metric.ball t m, m ≤ r ∧ m ≤ 1 - r := by
    intro r hr
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hr
    constructor <;> linarith [hr.1, hr.2]
  have hBnn : 0 ≤ skVectorCavityBound D r β ρ q := by
    unfold skVectorCavityBound; positivity
  have hmain := hasDerivAt_integral_gibbs_replica_cavity_path
    (μ := Measure.pi fun _ : Fin (N + 1) => μ)
    (P := P) (D := fun _ => (0 : ℝ)) (X := skVectorCavityFeature ξ N β)
    (Xs := fun _ : Unit => skVectorCavityCompensation ξ N β ρ q) (F := F) (Eb := 0)
    (B := skVectorCavityBound D r β ρ q) (M := M) measurable_const
    (measurable_skVectorCavityFeature hξ N β)
    (fun _ => measurable_skVectorCavityCompensation hξ N β ρ q)
    hF hBnn hM (fun _ => by simp)
    (abs_skVectorCavityFeature_le hr hbound N β ρ q)
    (fun _ => abs_skVectorCavityCompensation_le hr hbound N β ρ q) hFb
    (Z := Z) hG (by rintro ((p | i) | u) <;> simp [hZdef, hgm, hg'm, hYm])
    (by rintro ((p | i) | u) <;> simp [hZdef, hg0, hg'0, hY0])
    (s := sc) (s' := sc') (c := fun _ r => 1 - r) (c' := fun _ _ => -1)
    (t := t) (δ := m) (C := 1 / (2 * Real.sqrt m) + 1) hm
    (by
      rintro ((p | i) | u) r hr
      · exact hasDerivAt_const r 1
      · exact Real.hasDerivAt_sqrt (ne_of_gt (lt_of_lt_of_le hm (hball r hr).1))
      · have h1r : 1 - r ≠ 0 := ne_of_gt (lt_of_lt_of_le hm (hball r hr).2)
        have := (Real.hasDerivAt_sqrt h1r).comp r ((hasDerivAt_id r).const_sub 1)
        simpa [hsc, hsc', Function.comp_def, neg_div, mul_neg] using this)
    (by intro _ r _; simpa using (hasDerivAt_id r).const_sub (1 : ℝ))
    (by
      have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
      have hb : ∀ x, m ≤ x → |1 / (2 * Real.sqrt x)| ≤ 1 / (2 * Real.sqrt m) + 1 := by
        intro x hx
        have hx' : Real.sqrt m ≤ Real.sqrt x := Real.sqrt_le_sqrt hx
        rw [abs_of_nonneg (by positivity)]
        have : 1 / (2 * Real.sqrt x) ≤ 1 / (2 * Real.sqrt m) :=
          one_div_le_one_div_of_le (by positivity) (by linarith)
        linarith
      rintro ((p | i) | u) r hr
      · simp only [hsc', Sum.elim_inl, abs_zero]; positivity
      · exact hb r (hball r hr).1
      · simp only [hsc', Sum.elim_inr, abs_neg]; exact hb (1 - r) (hball r hr).2)
    (by
      intro _ r _
      simp only [abs_neg, abs_one]
      have : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
      have : 0 ≤ 1 / (2 * Real.sqrt m) := by positivity
      linarith)
    (by
      rintro ((p | i) | u)
      · exact Or.inr (by simp [hsc])
      · exact Or.inr (by
          simp only [hsc, Sum.elim_inl, Sum.elim_inr]; exact (Real.sqrt_pos.2 ht0).ne')
      · exact Or.inr (by
          simp only [hsc, Sum.elim_inr]; exact (Real.sqrt_pos.2 (sub_pos.2 ht1)).ne'))
  have hfe : ∀ (r' : ℝ) (ω : Ω), (fun a : Fin (N + 1) → α => (fun _ => (0 : ℝ)) a +
      ∑ k, sc k r' * Z k ω * skVectorCavityFeature ξ N β k a +
      ∑ j : Unit, (1 - r') * skVectorCavityCompensation ξ N β ρ q a) =
      skVectorCavityEnergy ξ N β ρ q (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) r' :=
    fun r' ω => funext fun a => by
      rw [skVectorCavityEnergy_eq_features]
      simp [hsc, hZdef]
  simp only [hfe] at hmain
  refine hmain.congr_deriv ?_
  -- the weights `sₖ'(t) sₗ(t) 𝔼 [Zₖ Zₗ]`
  have hst : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht0).ne'
  have hst' : Real.sqrt (1 - t) ≠ 0 := (Real.sqrt_pos.2 (sub_pos.2 ht1)).ne'
  have hW1 : ∀ (p : FinPairs N) (l : (FinPairs N ⊕ Fin N) ⊕ D),
      sc' (.inl (.inl p)) t * sc l t * ∫ ω, Z (.inl (.inl p)) ω * Z l ω ∂P = 0 := by
    intro p l
    simp [hsc']
  have hW2 : ∀ (i : Fin N) (l : (FinPairs N ⊕ Fin N) ⊕ D),
      sc' (.inl (.inr i)) t * sc l t * ∫ ω, Z (.inl (.inr i)) ω * Z l ω ∂P =
        Sum.elim (Sum.elim (fun _ => 0) fun i' => if i = i' then 1 / 2 else 0)
          (fun _ => 0) l := by
    rintro i ((p | i') | v)
    · have := hgg (.inr i) (.inl p)
      simp only [hZdef, hsc, hsc', Sum.elim_inl, Sum.elim_inr] at this ⊢
      rw [this]; simp
    · have := hgg (.inr i) (.inr i')
      simp only [hZdef, hsc, hsc', Sum.elim_inl, Sum.elim_inr] at this ⊢
      rw [this]
      by_cases h : i = i'
      · subst h; field_simp; simp
      · simp [h]
    · have := hgY (.inr i) v
      simp only [hZdef, hsc, hsc', Sum.elim_inl, Sum.elim_inr] at this ⊢
      rw [this]; simp
  have hW3 : ∀ (u : D) (l : (FinPairs N ⊕ Fin N) ⊕ D),
      sc' (.inr u) t * sc l t * ∫ ω, Z (.inr u) ω * Z l ω ∂P =
        Sum.elim (Sum.elim (fun _ => 0) fun _ => 0) (fun v => -(β ^ 2 / 2) * q u v) l := by
    rintro u ((p | i') | v)
    · have := hgY (.inl p) u
      simp only [hZdef, hsc, hsc', Sum.elim_inl, Sum.elim_inr] at this ⊢
      rw [show (fun ω => Y u ω * g p ω) = fun ω => g p ω * Y u ω from
        funext fun ω => mul_comm _ _, this]; simp
    · have := hgY (.inr i') u
      simp only [hZdef, hsc, hsc', Sum.elim_inl, Sum.elim_inr] at this ⊢
      rw [show (fun ω => Y u ω * g' i' ω) = fun ω => g' i' ω * Y u ω from
        funext fun ω => mul_comm _ _, this]; simp
    · have := hYY u v
      simp only [hZdef, hsc, hsc', Sum.elim_inr] at this ⊢
      rw [this]
      field_simp
  have hint : ∀ (G : (Option (Option R) → Fin (N + 1) → α) → ℝ), Measurable G →
      (∃ B, ∀ σ, |G σ| ≤ B) →
      Integrable (fun ω => ∫ σ, G σ ∂(Measure.pi fun _ : Option (Option R) =>
        (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
          (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t))) P := fun G hG hGb =>
    integrable_skVectorCavityGibbs μ ξ hξ hr hbound N β ρ q hgm hg'm hYm t G hG hGb
  have hbook := fun (x y : Option (Option R)) (Q : D → D → ℝ) (u v : D) =>
    skVectorCavity_book_integrand hξ hr hbound hF hFb x y Q u v
  simp only [Finset.univ_unique, Finset.sum_singleton]
  refine (integral_weighted_sum_sub (P := P) _ _ _
    (fun ω => β ^ 2 / 2 * ∑ a : R, ∑ b : R, ∑ u, ∑ v,
          ∫ σ : Option (Option R) → Fin (N + 1) → α,
            F (fun c => σ (some (some c))) * ξ (σ (some (some a)) (Fin.last N)) u *
              ξ (σ (some (some b)) (Fin.last N)) v *
              (skVectorCavityOverlap ξ N (σ (some (some a))) (σ (some (some b))) u v -
                if a = b then ρ u v else q u v) ∂(Measure.pi fun _ : Option (Option R) =>
          (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
            (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t)) -
        Fintype.card R * β ^ 2 * ∑ a : R, ∑ u, ∑ v,
          ∫ σ : Option (Option R) → Fin (N + 1) → α,
            F (fun c => σ (some (some c))) * ξ (σ (some (some a)) (Fin.last N)) u *
              ξ (σ (some none) (Fin.last N)) v *
              (skVectorCavityOverlap ξ N (σ (some (some a))) (σ (some none)) u v - q u v)
            ∂(Measure.pi fun _ : Option (Option R) =>
          (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
            (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t)) -
        Fintype.card R * (β ^ 2 / 2) * ∑ u, ∑ v,
          ∫ σ : Option (Option R) → Fin (N + 1) → α,
            F (fun c => σ (some (some c))) * ξ (σ (some none) (Fin.last N)) u *
              ξ (σ (some none) (Fin.last N)) v *
              (skVectorCavityOverlap ξ N (σ (some none)) (σ (some none)) u v - ρ u v)
            ∂(Measure.pi fun _ : Option (Option R) =>
          (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
            (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t)) +
        Fintype.card R * (Fintype.card R + 1) / 2 * β ^ 2 * ∑ u, ∑ v,
          ∫ σ : Option (Option R) → Fin (N + 1) → α,
            F (fun c => σ (some (some c))) * ξ (σ (some none) (Fin.last N)) u *
              ξ (σ none (Fin.last N)) v *
              (skVectorCavityOverlap ξ N (σ (some none)) (σ none) u v - q u v)
            ∂(Measure.pi fun _ : Option (Option R) =>
          (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
            (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t)) )
    ?_ ?_ ?_).trans ?_
  · intro k l
    exact hint _ (skVectorCavity_covariance_integrand hξ hr hbound hF hFb β k l).1
      (skVectorCavity_covariance_integrand hξ hr hbound hF hFb β k l).2
  · exact hint _ (skVectorCavity_compensation_integrand hξ hr hbound hF hFb β ρ q).1
      (skVectorCavity_compensation_integrand hξ hr hbound hF hFb β ρ q).2
  · intro ω
    have := isProbabilityMeasure_skVectorCavityGibbs μ ξ hξ hr hbound N β ρ q
      (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t
    exact skVectorCavity_fixed ξ hξ hr hbound N β ρ q hq F hF hFb _
      (fun k l => sc' k t * sc l t * ∫ ω, Z k ω * Z l ω ∂P) hW1 hW2 hW3
  · refine (integral_four_groups (P := P) _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_).trans ?_
    · intro a b u v
      exact hint _ (hbook (some (some a)) (some (some b))
        (fun u v => if a = b then ρ u v else q u v) u v).1 (hbook (some (some a)) (some (some b))
          (fun u v => if a = b then ρ u v else q u v) u v).2
    · intro a u v
      exact hint _ (hbook (some (some a)) (some none) q u v).1
        (hbook (some (some a)) (some none) q u v).2
    · intro u v
      exact hint _ (hbook (some none) (some none) ρ u v).1 (hbook (some none) (some none) ρ u v).2
    · intro u v
      exact hint _ (hbook (some none) none q u v).1 (hbook (some none) none q u v).2
    · rfl

end SpinGlasses
