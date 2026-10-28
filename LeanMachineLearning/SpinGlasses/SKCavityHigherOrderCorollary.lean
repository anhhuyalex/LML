/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityHigherOrderLinear
public import LeanMachineLearning.SpinGlasses.SKTBasisAlgebra

/-!
# Higher-order rectangular and third-replica expansions

Talagrand's Corollary 1.10.3, Eqs. (1.301)-(1.302), follows by the exact coefficient algebra
of Section 1.8 applied to the quantitative pair expansion. The products may be products of
finite linear combinations. Constants precede `N`. The second formula retains independence
from the distinguished third replica.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Corollary 1.10.3, Eq. (1.301).** The rectangular combination for a product of
`k` finite linear combinations, with explicit error of order `k + 2`. -/
theorem sk_cavity_rect_lincomb_expansion (β h q : ℝ) (hβ : 4 * β ^ 2 < 1)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q)
    (qhat : ℝ)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂gaussianReal 0 1 = qhat)
    (n k : ℕ)
    {i₁ i₂ j₁ j₂ : Fin n} (h12 : i₁ ≠ i₂)
    (h13 : i₁ ≠ j₁) (h14 : i₁ ≠ j₂) (h23 : i₂ ≠ j₁) (h24 : i₂ ≠ j₂)
    {ι : Fin k → Type*} [∀ j, Fintype (ι j)] (c : ∀ j, ι j → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a b : ∀ j, ι j → Fin n), (∀ j i, a j i ≠ b j i) →
    let F : (Fin n → Fin N → ℤˣ) → ℝ := fun ρ => ∏ j : Fin k, ∑ i : ι j,
      c j i * ((N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (ρ (a j i) v : ℝ)) ⬝ᵥ
        fun v : Fin N => (ρ (b j i) v : ℝ)) - q)
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let ν₂ : ((Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let J : Option (Option (Fin n)) → Option (Option (Fin n)) → ℝ := fun x y =>
      ν₂ (fun σ => F (fun r i => σ (some (some r)) i.castSucc) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ x i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ y i.castSucc : ℝ)) - q))
    |ν (fun σ => F (fun r i => σ r i.castSucc) *
        (((σ i₁ (Fin.last N) : ℝ) - (σ i₂ (Fin.last N) : ℝ)) *
          ((σ j₁ (Fin.last N) : ℝ) - (σ j₂ (Fin.last N) : ℝ)))) -
      β ^ 2 * (1 - 2 * q + qhat) *
        (J (some (some i₁)) (some (some j₁)) - J (some (some i₂)) (some (some j₁)) -
          (J (some (some i₁)) (some (some j₂)) - J (some (some i₂)) (some (some j₂))))| ≤
      C / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) := by
  obtain ⟨C₀, hC₀p, hC₀⟩ := sk_cavity_pair_lincomb_expansion β h q hβ hfix qhat hqhat n k h13 c
  obtain ⟨C₁, hC₁p, hC₁⟩ := sk_cavity_pair_lincomb_expansion β h q hβ hfix qhat hqhat n k h23 c
  obtain ⟨C₂, hC₂p, hC₂⟩ := sk_cavity_pair_lincomb_expansion β h q hβ hfix qhat hqhat n k h14 c
  obtain ⟨C₃, hC₃p, hC₃⟩ := sk_cavity_pair_lincomb_expansion β h q hβ hfix qhat hqhat n k h24 c
  refine ⟨C₀ + C₁ + C₂ + C₃, by positivity, ?_⟩
  intro N a b hab F E ν ν₂ J
  let A : Fin n → Fin n → (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun x y σ =>
    F (fun r i => σ r i.castSucc) *
      ((σ x (Fin.last N) : ℝ) * (σ y (Fin.last N) : ℝ) - q)
  let P : Fin n → Fin n → ℝ := fun x y => ν (A x y)
  let B : Fin n → Fin n → ℝ := fun x y => ∑ p : SKCavityReplicaPair n,
    skCavityReplicaPairWeight n p *
      (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences x y p) *
        J (skCavityReplicaPairMap p).1 (skCavityReplicaPairMap p).2)
  have h₀ := hC₀ N a b hab
  have h₁ := hC₁ N a b hab
  have h₂ := hC₂ N a b hab
  have h₃ := hC₃ N a b hab
  change |P i₁ j₁ - B i₁ j₁| ≤ _ at h₀
  change |P i₂ j₁ - B i₂ j₁| ≤ _ at h₁
  change |P i₁ j₂ - B i₁ j₂| ≤ _ at h₂
  change |P i₂ j₂ - B i₂ j₂| ≤ _ at h₃
  obtain ⟨hadd, hsmul, -, -⟩ := sk_replica_avg_calculus N n β h ν (fun _ => rfl)
  let Λ : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := ν, map_add' := hadd, map_smul' := hsmul }
  have he : (fun σ : Fin n → Fin (N + 1) → ℤˣ => F (fun r i => σ r i.castSucc) *
      (((σ i₁ (Fin.last N) : ℝ) - (σ i₂ (Fin.last N) : ℝ)) *
        ((σ j₁ (Fin.last N) : ℝ) - (σ j₂ (Fin.last N) : ℝ)))) =
      A i₁ j₁ - A i₂ j₁ - A i₁ j₂ + A i₂ j₂ := by
    funext σ
    simp only [Pi.sub_apply, Pi.add_apply, A]
    ring
  have hl : ν (fun σ => F (fun r i => σ r i.castSucc) *
      (((σ i₁ (Fin.last N) : ℝ) - (σ i₂ (Fin.last N) : ℝ)) *
        ((σ j₁ (Fin.last N) : ℝ) - (σ j₂ (Fin.last N) : ℝ)))) =
      P i₁ j₁ - P i₂ j₁ - P i₁ j₂ + P i₂ j₂ := by
    rw [he]
    change Λ (A i₁ j₁ - A i₂ j₁ - A i₁ j₂ + A i₂ j₂) = _
    rw [map_add, map_sub, map_sub]
    rfl
  have hJsym (x y : Option (Option (Fin n))) : J x y = J y x := by
    dsimp only [J]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    dsimp
    rw [dotProduct_comm]
  have hb : B i₁ j₁ - B i₂ j₁ - B i₁ j₂ + B i₂ j₂ =
      β ^ 2 * (1 - 2 * q + qhat) *
        (J (some (some i₁)) (some (some j₁)) - J (some (some i₂)) (some (some j₁)) -
          (J (some (some i₁)) (some (some j₂)) - J (some (some i₂)) (some (some j₂)))) := by
    have ht := sk_cavity_replica_pair_sum_rect (skCavityBCoef β q qhat)
      h12 h13 h14 h23 h24 J hJsym
    rw [sk_at_eigenvalue_one_eq] at ht
    refine Eq.trans ?_ ht
    dsimp only [B]
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have htriangle (w x y z : ℝ) : |w - x - y + z| ≤ |w| + |x| + |y| + |z| := by
    have h1 := abs_add_le (w - x - y) z
    have h2 := abs_sub (w - x) y
    have h3 := abs_sub w x
    linarith only [h1, h2, h3]
  rw [hl, ← hb]
  calc
    _ = |(P i₁ j₁ - B i₁ j₁) - (P i₂ j₁ - B i₂ j₁) -
        (P i₁ j₂ - B i₁ j₂) + (P i₂ j₂ - B i₂ j₂)| := congrArg abs (by ring)
    _ ≤ |P i₁ j₁ - B i₁ j₁| + |P i₂ j₁ - B i₂ j₁| +
        |P i₁ j₂ - B i₁ j₂| + |P i₂ j₂ - B i₂ j₂| := by
      exact htriangle (P i₁ j₁ - B i₁ j₁) (P i₂ j₁ - B i₂ j₁)
        (P i₁ j₂ - B i₁ j₂) (P i₂ j₂ - B i₂ j₂)
    _ ≤ C₀ / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) +
        C₁ / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) +
        C₂ / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) +
        C₃ / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) :=
      add_le_add (add_le_add (add_le_add h₀ h₁) h₂) h₃
    _ = _ := by ring

/-- **Corollary 1.10.3, Eq. (1.302).** If the product is unchanged when the distinguished
third replica is replaced, the third-replica and extra-replica terms regroup into the
book's two coefficients. The independence condition is imposed on the actual observable. -/
theorem sk_cavity_sub_third_lincomb_expansion (β h q : ℝ) (hβ : 4 * β ^ 2 < 1)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q)
    (qhat : ℝ)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂gaussianReal 0 1 = qhat)
    (n k : ℕ)
    {i₁ i₂ r : Fin n} (h12 : i₁ ≠ i₂) (h1r : i₁ ≠ r) (h2r : i₂ ≠ r)
    {ι : Fin k → Type*} [∀ j, Fintype (ι j)] (c : ∀ j, ι j → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (a b : ∀ j, ι j → Fin n), (∀ j i, a j i ≠ b j i) →
    let F : (Fin n → Fin N → ℤˣ) → ℝ := fun ρ => ∏ j : Fin k, ∑ i : ι j,
      c j i * ((N + 1 : ℝ)⁻¹ * ((fun v : Fin N => (ρ (a j i) v : ℝ)) ⬝ᵥ
        fun v : Fin N => (ρ (b j i) v : ℝ)) - q)
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let ν₂ : ((Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun f =>
      ∫ g, ∫ σ, f σ
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let J : Option (Option (Fin n)) → Option (Option (Fin n)) → ℝ := fun x y =>
      ν₂ (fun σ => F (fun r i => σ (some (some r)) i.castSucc) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ x i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ y i.castSucc : ℝ)) - q))
    (∀ (ρ : Fin n → Fin N → ℤˣ) z, F (Function.update ρ r z) = F ρ) →
    |ν (fun σ => F (fun l i => σ l i.castSucc) *
        (((σ i₁ (Fin.last N) : ℝ) - (σ i₂ (Fin.last N) : ℝ)) *
          (σ r (Fin.last N) : ℝ))) -
      (β ^ 2 * (1 - 4 * q + 3 * qhat) *
        (J (some (some i₁)) (some (some r)) - J (some (some i₂)) (some (some r))) +
      β ^ 2 * (q - qhat) *
        ∑ l ∈ Finset.univ.filter (fun l => l ≠ i₁ ∧ l ≠ i₂ ∧ l ≠ r),
          (J (some (some i₁)) (some (some l)) - J (some (some i₂)) (some (some l)) -
            (J (some (some i₁)) (some none) - J (some (some i₂)) (some none))))| ≤
      C / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) := by
  obtain ⟨C₁, hC₁p, hC₁⟩ := sk_cavity_pair_lincomb_expansion β h q hβ hfix qhat hqhat n k h1r c
  obtain ⟨C₂, hC₂p, hC₂⟩ := sk_cavity_pair_lincomb_expansion β h q hβ hfix qhat hqhat n k h2r c
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  intro N a b hab F E ν ν₂ J hF
  let A : Fin n → (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun x σ =>
    F (fun l i => σ l i.castSucc) *
      ((σ x (Fin.last N) : ℝ) * (σ r (Fin.last N) : ℝ) - q)
  let P : Fin n → ℝ := fun x => ν (A x)
  let B : Fin n → ℝ := fun x => ∑ p : SKCavityReplicaPair n,
    skCavityReplicaPairWeight n p *
      (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences x r p) *
        J (skCavityReplicaPairMap p).1 (skCavityReplicaPairMap p).2)
  have h₁ := hC₁ N a b hab
  have h₂ := hC₂ N a b hab
  change |P i₁ - B i₁| ≤ _ at h₁
  change |P i₂ - B i₂| ≤ _ at h₂
  obtain ⟨hadd, hsmul, -, -⟩ := sk_replica_avg_calculus N n β h ν (fun _ => rfl)
  let Λ : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := ν, map_add' := hadd, map_smul' := hsmul }
  have he : (fun σ : Fin n → Fin (N + 1) → ℤˣ => F (fun l i => σ l i.castSucc) *
      (((σ i₁ (Fin.last N) : ℝ) - (σ i₂ (Fin.last N) : ℝ)) *
        (σ r (Fin.last N) : ℝ))) = A i₁ - A i₂ := by
    funext σ
    simp only [Pi.sub_apply, A]
    ring
  have hl : ν (fun σ => F (fun l i => σ l i.castSucc) *
      (((σ i₁ (Fin.last N) : ℝ) - (σ i₂ (Fin.last N) : ℝ)) *
        (σ r (Fin.last N) : ℝ))) = P i₁ - P i₂ := by
    rw [he]
    change Λ (A i₁ - A i₂) = _
    rw [map_sub]
    rfl
  have hJsym (x y : Option (Option (Fin n))) : J x y = J y x := by
    dsimp only [J]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    dsimp
    rw [dotProduct_comm]
  have hb0 : B i₁ - B i₂ =
      (skCavityBCoef β q qhat 2 - skCavityBCoef β q qhat 1) *
        (J (some (some i₁)) (some (some r)) - J (some (some i₂)) (some (some r))) +
      (skCavityBCoef β q qhat 1 - skCavityBCoef β q qhat 0) *
        ((∑ l ∈ Finset.univ.filter (fun l => l ≠ i₁ ∧ l ≠ i₂ ∧ l ≠ r),
          (J (some (some i₁)) (some (some l)) - J (some (some i₂)) (some (some l)))) -
          (n : ℝ) * (J (some (some i₁)) (some none) - J (some (some i₂)) (some none))) := by
    have ht := sk_cavity_replica_pair_sum_sub_third (skCavityBCoef β q qhat)
      h12 h1r h2r J hJsym
    refine Eq.trans ?_ ht
    dsimp only [B]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← mul_sub, ← sub_mul]
    simp only [skCavityReplicaPairCoincidences]
    rw [sk_cavity_coincidences_sub_eq (skCavityBCoef β q qhat)
      (i₁ := some (some i₁)) (i₂ := some (some i₂)) (k := some (some r))
      (by simpa only [ne_eq, Option.some.injEq] using h12)
      (by simpa only [ne_eq, Option.some.injEq] using h1r)
      (by simpa only [ne_eq, Option.some.injEq] using h2r)
      (skCavityReplicaPair_ne p)]
  have hFu (σ : Fin n → Fin (N + 1) → ℤˣ) (z : Fin (N + 1) → ℤˣ) :
      F (fun l i => Function.update σ r z l i.castSucc) = F (fun l i => σ l i.castSucc) := by
    have hu : (fun (l : Fin n) (i : Fin N) => Function.update σ r z l i.castSucc) =
        Function.update (fun (l : Fin n) (i : Fin N) => σ l i.castSucc) r
          (fun i : Fin N => z i.castSucc) := by
      funext l i
      by_cases hl : l = r <;> simp [hl]
    rw [hu]
    exact hF _ _
  have hswap (i : Fin n) (hir : i ≠ r) :
      J (some (some i)) (some (some r)) = J (some (some i)) (some none) := by
    dsimp only [J, ν₂]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    exact integral_pi_count_tilted_replace_replica (e := fun l : Fin n => some (some l))
      (fun l l' h => Option.some.inj (Option.some.inj h)) (x₀ := some none)
      (fun l => by simp) hir (E g) (fun σ => F (fun l i => σ l i.castSucc)) hFu
      (fun x y => (N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (x i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (y i.castSucc : ℝ)) - q)
  have hsplit := sk_at_deriv_coef_split
    (Finset.univ.filter fun l : Fin n => l ≠ i₁ ∧ l ≠ i₂ ∧ l ≠ r) n
    (card_filter_ne_three h12 h1r h2r)
    (skCavityBCoef β q qhat 2) (skCavityBCoef β q qhat 1) (skCavityBCoef β q qhat 0)
    (J (some (some i₁)) (some (some r)) - J (some (some i₂)) (some (some r)))
    (J (some (some i₁)) (some none) - J (some (some i₂)) (some none))
    (fun l => J (some (some i₁)) (some (some l)) - J (some (some i₂)) (some (some l)))
    (by rw [hswap i₁ h1r, hswap i₂ h2r])
  have hcoef : skCavityBCoef β q qhat 1 - skCavityBCoef β q qhat 0 =
      β ^ 2 * (q - qhat) := by
    dsimp [skCavityBCoef, skCavityBUnscaled]
    ring
  rw [hsplit, sk_at_eigenvalue_two_eq, hcoef] at hb0
  rw [hl, ← hb0]
  calc
    _ = |(P i₁ - B i₁) - (P i₂ - B i₂)| := congrArg abs (by ring)
    _ ≤ |P i₁ - B i₁| + |P i₂ - B i₂| := abs_sub _ _
    _ ≤ C₁ / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) +
        C₂ / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) := add_le_add h₁ h₂
    _ = _ := by ring

end SpinGlasses
