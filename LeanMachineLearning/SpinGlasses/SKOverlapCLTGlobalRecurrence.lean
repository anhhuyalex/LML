/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTGlobalFeedback

/-!
# The recurrence for the global factors (Talagrand, proof of Theorem 1.10.1)

Combining the last-site expansion (1.325), the term I (1.326), the leading cavity term
(Lemma 1.10.2) and its evaluation (1.327)-(1.328) gives, with `ν_j = 𝔼 T^j`,
`(1 - β²(1-4q+3q̂)) ν_k = (k-1) E ν_{k-2} + O(k+1)` where
`E = (q̂-q²)/(N+1) + β²(q̂-q²) A²/(N+1) + 2β²(2q+q²-3q̂) B²/(N+1)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- The triangle inequality for four terms. -/
theorem abs_add_four (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
    (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)

/-- **The recurrence for `ν_k = 𝔼 T^k`** (Theorem 1.10.1, the induction step). -/
theorem sk_T_global_recurrence_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {V : Type*} [Fintype V] (p : V) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (Esk g))
    let Tg : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
      ((N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i) - q
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let ν : ℕ → ℝ := fun j =>
      ∫ g, Tg g ^ j ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let B2 : ℝ := (q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) /
      (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) / (N + 1 : ℝ)
    let A2 : ℝ := α / (1 - β ^ 2 * α) / (N + 1 : ℝ)
    |(1 - β ^ 2 * (1 - 4 * q + 3 * qh)) * ν (Fintype.card V) -
        ((Fintype.card V - 1 : ℕ) : ℝ) * ((qh - q ^ 2) / (N + 1 : ℝ) +
          β ^ 2 * (qh - q ^ 2) * A2 + 2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qh) * B2) *
          ν (Fintype.card V - 2)| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2) := by
  classical
  let n := Fintype.card (V ⊕ V)
  let e : V ⊕ V ≃ Fin n := Fintype.equivFin (V ⊕ V)
  obtain ⟨C₁, hC₁0, hC₁⟩ := sk_global_step_uniform β₀ hβ₀ e p
  obtain ⟨C₂, hC₂0, hC₂⟩ := sk_global_feedback_uniform β₀ hβ₀ e p
  obtain ⟨C₃, hC₃0, hC₃⟩ := sk_global_feedback_eval_uniform β₀ hβ₀ e p
  obtain ⟨C₄, hC₄0, hC₄⟩ := sk_global_termI_uniform β₀ hβ₀ e p
  refine ⟨C₁ + C₂ + C₃ + C₄, by positivity, fun β h q hfix hb N => ?_⟩
  intro Esk bmean Tg qh α ν B2 A2
  have hqhat : ∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 4 ∂gaussianReal 0 1 = qh := by
    apply integral_congr_ae (ae_of_all _ fun t => ?_)
    congr 2
    ring
  have h1 := hC₁ β h q hfix hb N
  have h2 := hC₂ β h q qh hfix hqhat hb N
  have h3 := hC₃ β h q hfix hb N
  have h4 := hC₄ β h q hfix hb N
  let νF : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
    ∫ g, ∫ σ, f σ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  have hinjV : Function.Injective (Sum.elim (fun u : V => e (.inl u)) (fun u : V => e (.inr u)) :
      V ⊕ V → Fin n) := by
    intro a b hab
    have : e a = e b := by
      rcases a with a | a <;> rcases b with b | b <;>
        simpa only [Sum.elim_inl, Sum.elim_inr] using hab
    exact e.injective this
  have hX : νF (fun σ => ∏ u : V, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
      (σ (e (.inl u)) v : ℝ) * (σ (e (.inr u)) v : ℝ) - q)) = ν (Fintype.card V) := by
    have := sk_global_blocks_moment (fun u : V => e (.inl u)) (fun u : V => e (.inr u)) hinjV
      Finset.univ N β h q
    simpa using this
  let ν₂ : ((Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
    ∫ g, ∫ σ, f σ
      ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  let Lead : ℝ := νF (fun σ => (((σ (e (.inl p)) (Fin.last N) : ℝ) *
      (σ (e (.inr p)) (Fin.last N) : ℝ)) - q) *
    ∏ u : {u // u ≠ p}, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
      (σ (e (.inl u.1)) v.castSucc : ℝ) * (σ (e (.inr u.1)) v.castSucc : ℝ) - q))
  let I : ℝ := (N + 1 : ℝ)⁻¹ * ∑ u : {u // u ≠ p}, νF (fun σ =>
    (((σ (e (.inl p)) (Fin.last N) : ℝ) * (σ (e (.inr p)) (Fin.last N) : ℝ)) - q) *
      (((σ (e (.inl u.1)) (Fin.last N) : ℝ) * (σ (e (.inr u.1)) (Fin.last N) : ℝ)) *
        ∏ w ∈ Finset.univ.erase u, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
          (σ (e (.inl w.1)) v.castSucc : ℝ) * (σ (e (.inr w.1)) v.castSucc : ℝ) - q)))
  let S2 : ℝ := ∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
        (skCavityBCoef β q qh (skCavityReplicaPairCoincidences (e (.inl p)) (e (.inr p)) j) *
          ν₂ (fun σ => (∏ u : {u // u ≠ p}, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
              (σ (some (some (e (.inl u.1)))) v.castSucc : ℝ) *
                (σ (some (some (e (.inr u.1)))) v.castSucc : ℝ) - q)) *
            ((N + 1 : ℝ)⁻¹ * ∑ v : Fin N,
              (σ (skCavityReplicaPairMap j).1 v.castSucc : ℝ) *
                (σ (skCavityReplicaPairMap j).2 v.castSucc : ℝ) - q)))
  let T : ℝ := β ^ 2 * (1 - 4 * q + 3 * qh) * ν (Fintype.card V) +
    ((Fintype.card V - 1 : ℕ) : ℝ) * (β ^ 2 * (qh - q ^ 2) * A2 +
      2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qh) * B2) * ν (Fintype.card V - 2)
  let Ix : ℝ := (((Fintype.card V - 1 : ℕ) : ℝ) * (qh - q ^ 2) / (N + 1 : ℝ)) *
    ν (Fintype.card V - 2)
  have h1' : |νF (fun σ => ∏ u : V, ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
      (σ (e (.inl u)) v : ℝ) * (σ (e (.inr u)) v : ℝ) - q)) - (Lead + I)| ≤
      C₁ / ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2) := h1
  have h2' : |Lead - S2| ≤ C₂ / ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2) := h2
  have h3' : |S2 - T| ≤ C₃ / ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2) := h3
  have h4' : |I - Ix| ≤ C₄ / ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2) := h4
  rw [hX] at h1'
  have hkey : (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) * ν (Fintype.card V) -
      ((Fintype.card V - 1 : ℕ) : ℝ) * ((qh - q ^ 2) / (N + 1 : ℝ) +
        β ^ 2 * (qh - q ^ 2) * A2 + 2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qh) * B2) *
        ν (Fintype.card V - 2) =
      (ν (Fintype.card V) - (Lead + I)) + (Lead - S2) + (S2 - T) + (I - Ix) := by
    simp only [T, Ix]
    ring
  rw [hkey]
  have hsum := abs_add_four ((ν (Fintype.card V) - (Lead + I))) (Lead - S2) (S2 - T) (I - Ix)
  refine hsum.trans ?_
  have : (C₁ + C₂ + C₃ + C₄) / ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2) =
      C₁ / ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2) +
      C₂ / ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2) +
      C₃ / ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2) +
      C₄ / ((N : ℝ) + 1) ^ (((Fintype.card V + 1 : ℕ) : ℝ) / 2) := by ring
  rw [this]
  exact add_le_add (add_le_add (add_le_add h1' h2') h3') h4'

end SpinGlasses
