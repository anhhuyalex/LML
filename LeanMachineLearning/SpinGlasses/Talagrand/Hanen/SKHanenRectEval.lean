/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenRectGaussian
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenRectComparison
public import
  LeanMachineLearning.SpinGlasses.Talagrand.OverlapCLT.GibbsMoments.SKOverlapCLTGibbsPolynomials

/-!
# The Gaussian leading term of a product of two pairings of full rectangles

Step E3d of Proposition 1.11.10 (Talagrand, Eq. (1.345)-(1.346)): the coupled mean of
`∏_{P₀} U ∏_P U`, with `U` the full rectangle on `N + 1` sites of the replica pairs `pairMap`,
is `(4 A²/(N+1))^m` if `P = P₀` and `0` otherwise, up to `O((N+1)^{-(2m+1)/2})`.
The pair `T` variables of the rectangles are Gaussian (`sk_T_lincomb_gibbs_moments_uniform`),
and the Gaussian computation is the spin-free `hanen_gaussian_rect_pairing_sq`,
`hanen_gaussian_rect_pairings_of_ne`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix
namespace SpinGlasses

/-- The signed sum over the four choices of one replica in each difference of the centered pair
overlap `T` (replicas ordered by `min`/`max`) is the full rectangle: the centering `b` cancels,
because each difference of replicas is centered. -/
theorem hanen_rect_T_identity (N n : ℕ) (ρ : Fin n → Fin (N + 1) → ℤˣ) (b : Fin (N + 1) → ℝ)
    (x₁ x₂ y₁ y₂ : Fin n) :
    ∑ e : Bool × Bool, ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
      ((N + 1 : ℝ)⁻¹ * ∑ i : Fin (N + 1),
        ((ρ (min (if e.1 then x₂ else x₁) (if e.2 then y₂ else y₁)) i : ℝ) - b i) *
        ((ρ (max (if e.1 then x₂ else x₁) (if e.2 then y₂ else y₁)) i : ℝ) - b i)) =
      (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (ρ x₁ i : ℝ) * (ρ y₁ i : ℝ)) -
      (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (ρ x₂ i : ℝ) * (ρ y₁ i : ℝ)) -
      (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (ρ x₁ i : ℝ) * (ρ y₂ i : ℝ)) +
      (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (ρ x₂ i : ℝ) * (ρ y₂ i : ℝ)) := by
  have hsymm (p q : Fin n) : ∑ i : Fin (N + 1),
      ((ρ (min p q) i : ℝ) - b i) * ((ρ (max p q) i : ℝ) - b i) =
      ∑ i : Fin (N + 1), ((ρ p i : ℝ) - b i) * ((ρ q i : ℝ) - b i) := by
    rcases le_total p q with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hsum : (∑ i : Fin (N + 1), ((ρ x₁ i : ℝ) - b i) * ((ρ y₁ i : ℝ) - b i)) -
      (∑ i : Fin (N + 1), ((ρ x₂ i : ℝ) - b i) * ((ρ y₁ i : ℝ) - b i)) -
      (∑ i : Fin (N + 1), ((ρ x₁ i : ℝ) - b i) * ((ρ y₂ i : ℝ) - b i)) +
      (∑ i : Fin (N + 1), ((ρ x₂ i : ℝ) - b i) * ((ρ y₂ i : ℝ) - b i)) =
      (∑ i : Fin (N + 1), (ρ x₁ i : ℝ) * (ρ y₁ i : ℝ)) -
      (∑ i : Fin (N + 1), (ρ x₂ i : ℝ) * (ρ y₁ i : ℝ)) -
      (∑ i : Fin (N + 1), (ρ x₁ i : ℝ) * (ρ y₂ i : ℝ)) +
      (∑ i : Fin (N + 1), (ρ x₂ i : ℝ) * (ρ y₂ i : ℝ)) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hsymm, Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, ite_false,
    ite_true]
  linear_combination ((N + 1 : ℝ)⁻¹) * hsum

/-- **Eq. (1.345)-(1.346), one fixed configuration.** For fixed pairings `P₀`, `P` and fixed
replica pairs, the coupled mean of the product of the full rectangles is the Gaussian reference
times `(N+1)^{-m}`, up to `O((N+1)^{-(2m+1)/2})`. The constant may depend on the configuration;
`sk_hanen_full_pairings_gaussian` makes it uniform by taking a maximum over the finitely many
configurations. -/
theorem sk_hanen_full_pairings_gaussian_data (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (m n : ℕ)
    (P₀ P : Finpartition.Pairing (univ : Finset (Fin (2 * m))))
    (pairMap : Fin (2 * m) → Fin n × Fin n) (hxy : ∀ v, (pairMap v).1 ≠ (pairMap v).2)
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2) (hn : Nonempty (Fin n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ),
      let α := (∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 4
        ∂gaussianReal 0 1) - 2 * q + 1
      let A_sq := α / (1 - β ^ 2 * α)
      let Cf := fun (σ : Fin n → Fin (N + 1) → ℤˣ) (u v : Fin (2 * m)) =>
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).1 i : ℝ) * (σ (pairMap v).1 i : ℝ)) -
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).2 i : ℝ) * (σ (pairMap v).1 i : ℝ)) -
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).1 i : ℝ) * (σ (pairMap v).2 i : ℝ)) +
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).2 i : ℝ) * (σ (pairMap v).2 i : ℝ))
      |skCavityPathMean N n β q h 1 (fun σ =>
          P₀.blockProduct (Renormalization.pairWeight (Cf σ)) *
            P.blockProduct (Renormalization.pairWeight (Cf σ))) -
        ((N : ℝ) + 1) ⁻¹ ^ m *
          ∫ z : (Fin n × Fin n) ⊕ Fin n → ℝ,
            P₀.blockProduct (Renormalization.pairWeight fun a b => ∑ e : Bool × Bool,
              ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
                (Real.sqrt A_sq * z (Sum.inl
                  (min (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1),
                   max (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1))))) *
            P.blockProduct (Renormalization.pairWeight fun a b => ∑ e : Bool × Bool,
              ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
                (Real.sqrt A_sq * z (Sum.inl
                  (min (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1),
                   max (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1)))))
            ∂(Measure.pi fun _ : (Fin n × Fin n) ⊕ Fin n => gaussianReal 0 1)| ≤
        C / ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨u, v, huv, hlab⟩ :=
    Renormalization.exists_labels_prod_pairWeight_mul (m := m) P₀ P (by simp)
  let rep : Fin (2 * m) → Bool → Fin n := fun w e => if e then (pairMap w).2 else (pairMap w).1
  have hne (j : Fin (m + m)) (e : Bool × Bool) : rep (u j) e.1 ≠ rep (v j) e.2 := by
    intro h
    exact huv j (hanen_replica_injective pairMap hxy hdisj _ _ _ _ h).1
  have ho : ∀ (j : Fin (m + m)) (e : Bool × Bool), (fun _ _ => true) j e = true →
      min (rep (u j) e.1) (rep (v j) e.2) < max (rep (u j) e.1) (rep (v j) e.2) :=
    fun j e _ => min_lt_max.2 (hne j e)
  obtain ⟨C, hCpos, hCs⟩ := @sk_T_lincomb_gibbs_moments_uniform β₀ hβ₀ (Fin n)
    inferInstance inferInstance hn (Fin (m + m)) inferInstance (Bool × Bool) inferInstance
    (fun _ _ => true) (fun j e => min (rep (u j) e.1) (rep (v j) e.2))
    (fun j e => max (rep (u j) e.1) (rep (v j) e.2))
    (fun _ e => (if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) ho
  refine ⟨C, hCpos, fun β h q hfix hβ N => ?_⟩
  intro α A_sq Cf
  have hs := hCs β h q hfix hβ N
  dsimp only at hs
  obtain ⟨-, hdev, -⟩ := hs
  have hexp : ((N : ℝ) + 1) ^ ((Fintype.card (Fin (m + m)) : ℝ) / 2) = ((N : ℝ) + 1) ^ m := by
    have : ((Fintype.card (Fin (m + m)) : ℕ) : ℝ) / 2 = (m : ℝ) := by
      rw [Fintype.card_fin]; push_cast; ring
    rw [this, Real.rpow_natCast]
  rw [hexp] at hdev
  have hpos : (0 : ℝ) < ((N : ℝ) + 1) ^ m := by positivity
  have hmain : |(skCavityPathMean N n β q h 1 fun σ =>
          P₀.blockProduct (Renormalization.pairWeight (Cf σ)) *
            P.blockProduct (Renormalization.pairWeight (Cf σ))) -
        ((N : ℝ) + 1)⁻¹ ^ m * (∫ (z : Fin n × Fin n ⊕ Fin n → ℝ),
            P₀.blockProduct (Renormalization.pairWeight fun a b => ∑ e : Bool × Bool,
              ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
                (Real.sqrt A_sq * z (Sum.inl
                  (min (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1),
                   max (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1))))) *
            P.blockProduct (Renormalization.pairWeight fun a b => ∑ e : Bool × Bool,
              ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
                (Real.sqrt A_sq * z (Sum.inl
                  (min (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1),
                   max (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1)))))
            ∂(Measure.pi fun _ : (Fin n × Fin n) ⊕ Fin n => gaussianReal 0 1))| =
      ((N : ℝ) + 1)⁻¹ ^ m * |(∫ g, ((N : ℝ) + 1) ^ m * ∫ ρ : Fin n → Fin (N + 1) → ℤˣ,
          P₀.blockProduct (Renormalization.pairWeight (Cf ρ)) *
            P.blockProduct (Renormalization.pairWeight (Cf ρ))
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
        ∫ (z : Fin n × Fin n ⊕ Fin n → ℝ),
            P₀.blockProduct (Renormalization.pairWeight fun a b => ∑ e : Bool × Bool,
              ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
                (Real.sqrt A_sq * z (Sum.inl
                  (min (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1),
                   max (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1))))) *
            P.blockProduct (Renormalization.pairWeight fun a b => ∑ e : Bool × Bool,
              ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
                (Real.sqrt A_sq * z (Sum.inl
                  (min (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1),
                   max (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1)))))
            ∂(Measure.pi fun _ : (Fin n × Fin n) ⊕ Fin n => gaussianReal 0 1)| := by
    rw [integral_const_mul, ← skCavityPathMean_one N n β q h]
    set G' := ∫ (z : Fin n × Fin n ⊕ Fin n → ℝ),
            P₀.blockProduct (Renormalization.pairWeight fun a b => ∑ e : Bool × Bool,
              ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
                (Real.sqrt A_sq * z (Sum.inl
                  (min (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1),
                   max (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1))))) *
            P.blockProduct (Renormalization.pairWeight fun a b => ∑ e : Bool × Bool,
              ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
                (Real.sqrt A_sq * z (Sum.inl
                  (min (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1),
                   max (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1)))))
            ∂(Measure.pi fun _ : (Fin n × Fin n) ⊕ Fin n => gaussianReal 0 1) with hG'
    set X := skCavityPathMean N n β q h 1 fun σ =>
          P₀.blockProduct (Renormalization.pairWeight (Cf σ)) *
            P.blockProduct (Renormalization.pairWeight (Cf σ)) with hX
    have hk : (0 : ℝ) < ((N : ℝ) + 1)⁻¹ ^ m := by positivity
    have : X - ((N : ℝ) + 1)⁻¹ ^ m * G' =
        ((N : ℝ) + 1)⁻¹ ^ m * (((N : ℝ) + 1) ^ m * X - G') := by
      have : ((N : ℝ) + 1)⁻¹ ^ m * ((N : ℝ) + 1) ^ m = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ (by positivity), one_pow]
      linear_combination (-X) * this
    rw [this, abs_mul, abs_of_pos hk]
  have hdev' : |(∫ g, ((N : ℝ) + 1) ^ m * ∫ ρ : Fin n → Fin (N + 1) → ℤˣ,
          P₀.blockProduct (Renormalization.pairWeight (Cf ρ)) *
            P.blockProduct (Renormalization.pairWeight (Cf ρ))
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
        ∫ (z : Fin n × Fin n ⊕ Fin n → ℝ),
            P₀.blockProduct (Renormalization.pairWeight fun a b => ∑ e : Bool × Bool,
              ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
                (Real.sqrt A_sq * z (Sum.inl
                  (min (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1),
                   max (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1))))) *
            P.blockProduct (Renormalization.pairWeight fun a b => ∑ e : Bool × Bool,
              ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
                (Real.sqrt A_sq * z (Sum.inl
                  (min (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1),
                   max (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1)))))
            ∂(Measure.pi fun _ : (Fin n × Fin n) ⊕ Fin n => gaussianReal 0 1)| ≤
        C / Real.sqrt ((N : ℝ) + 1) := by
    have hCsymm (σ : Fin n → Fin (N + 1) → ℤˣ) (x y : Fin (2 * m)) : Cf σ x y = Cf σ y x := by
      simp only [Cf]
      have h1 (s t : Fin n) : ∑ i : Fin (N + 1), (σ s i : ℝ) * (σ t i : ℝ) =
          ∑ i : Fin (N + 1), (σ t i : ℝ) * (σ s i : ℝ) :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [h1 (pairMap x).1 (pairMap y).1, h1 (pairMap x).2 (pairMap y).1,
        h1 (pairMap x).1 (pairMap y).2, h1 (pairMap x).2 (pairMap y).2]
      ring
    obtain ⟨hVs, -, -, hVz⟩ := hanen_rect_coeff pairMap hxy hdisj (Real.sqrt A_sq)
    have hKsymm (z : (Fin n × Fin n) ⊕ Fin n → ℝ) (a b : Fin (2 * m)) :
        (∑ e : Bool × Bool, ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
          (Real.sqrt A_sq * z (Sum.inl
            (min (if e.1 then (pairMap a).2 else (pairMap a).1)
              (if e.2 then (pairMap b).2 else (pairMap b).1),
             max (if e.1 then (pairMap a).2 else (pairMap a).1)
              (if e.2 then (pairMap b).2 else (pairMap b).1))))) =
        ∑ e : Bool × Bool, ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
          (Real.sqrt A_sq * z (Sum.inl
            (min (if e.1 then (pairMap b).2 else (pairMap b).1)
              (if e.2 then (pairMap a).2 else (pairMap a).1),
             max (if e.1 then (pairMap b).2 else (pairMap b).1)
              (if e.2 then (pairMap a).2 else (pairMap a).1)))) := by
      have h1 := hVz a b z
      have h2 := hVz b a z
      have h3 := congrArg (fun V' => V' ⬝ᵥ z) (hVs a b)
      exact h1.symm.trans (h3.trans h2)
    convert hdev using 4
    · funext g
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ρ
      rw [← hlab _ (hCsymm ρ)]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [ite_true]
      exact (hanen_rect_T_identity N n ρ _ _ _ _ _).symm
    · funext z
      rw [← hlab _ (hKsymm z)]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [ite_true]
      rfl
  rw [hmain]
  have hsq : ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) =
      ((N : ℝ) + 1) ^ m * Real.sqrt ((N : ℝ) + 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add (by positivity)]
    congr 1
    push_cast
    ring
  rw [hsq]
  calc ((N : ℝ) + 1)⁻¹ ^ m * _ ≤ ((N : ℝ) + 1)⁻¹ ^ m * (C / Real.sqrt ((N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hdev' (by positivity)
    _ = C / (((N : ℝ) + 1) ^ m * Real.sqrt ((N : ℝ) + 1)) := by
        rw [inv_pow]
        field_simp

/-- A family of statements indexed by a finite type, each holding for some positive constant and
monotone in the constant, holds for one common positive constant. -/
theorem exists_pos_forall_of_finite {X : Type*} [Finite X] (Q : X → ℝ → Prop)
    (hmono : ∀ x C C', C ≤ C' → Q x C → Q x C') (hex : ∀ x, ∃ C : ℝ, 0 < C ∧ Q x C) :
    ∃ K : ℝ, 0 < K ∧ ∀ x, Q x K := by
  have := Fintype.ofFinite X
  choose C hC hQ using hex
  have hs : 0 ≤ ∑ x, C x := Finset.sum_nonneg fun x _ => (hC x).le
  refine ⟨1 + ∑ x, C x, by linarith, fun x => hmono x (C x) _ ?_ (hQ x)⟩
  have := Finset.single_le_sum (f := C) (fun y _ => (hC y).le) (Finset.mem_univ x)
  linarith

/-- The coupled cavity-path mean of a constant is the constant. -/
theorem skCavityPathMean_one_const (N n : ℕ) (β q h c : ℝ) :
    skCavityPathMean N n β q h 1 (fun _ => c) = c := by
  rw [skCavityPathMean_one]
  simp

/-- **Eq. (1.345)-(1.346), uniform in the configuration.** The constant depends on `m`, `n`
and `β₀` only: it is the maximum of the finitely many constants of
`sk_hanen_full_pairings_gaussian_data`. -/
theorem sk_hanen_full_pairings_gaussian (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (m n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (P₀ P : Finpartition.Pairing (univ : Finset (Fin (2 * m))))
      (pairMap : Fin (2 * m) → Fin n × Fin n), (∀ v, (pairMap v).1 ≠ (pairMap v).2) →
      (∀ u v : Fin (2 * m), u ≠ v →
        (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
        (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2) →
      let α := (∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 4
        ∂gaussianReal 0 1) - 2 * q + 1
      let A_sq := α / (1 - β ^ 2 * α)
      let Cf := fun (σ : Fin n → Fin (N + 1) → ℤˣ) (u v : Fin (2 * m)) =>
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).1 i : ℝ) * (σ (pairMap v).1 i : ℝ)) -
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).2 i : ℝ) * (σ (pairMap v).1 i : ℝ)) -
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).1 i : ℝ) * (σ (pairMap v).2 i : ℝ)) +
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).2 i : ℝ) * (σ (pairMap v).2 i : ℝ))
      |skCavityPathMean N n β q h 1 (fun σ =>
          P₀.blockProduct (Renormalization.pairWeight (Cf σ)) *
            P.blockProduct (Renormalization.pairWeight (Cf σ))) -
        ((N : ℝ) + 1) ⁻¹ ^ m *
          ∫ z : (Fin n × Fin n) ⊕ Fin n → ℝ,
            P₀.blockProduct (Renormalization.pairWeight fun a b => ∑ e : Bool × Bool,
              ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
                (Real.sqrt A_sq * z (Sum.inl
                  (min (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1),
                   max (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1))))) *
            P.blockProduct (Renormalization.pairWeight fun a b => ∑ e : Bool × Bool,
              ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
                (Real.sqrt A_sq * z (Sum.inl
                  (min (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1),
                   max (if e.1 then (pairMap a).2 else (pairMap a).1)
                    (if e.2 then (pairMap b).2 else (pairMap b).1)))))
            ∂(Measure.pi fun _ : (Fin n × Fin n) ⊕ Fin n => gaussianReal 0 1)| ≤
        K / ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) := by
  by_cases hm : m = 0
  · subst hm
    refine ⟨1, one_pos, ?_⟩
    intro β h q hfix hβ N P₀ P pairMap hxy hdisj α A_sq Cf
    have hb (Q : Finpartition.Pairing (univ : Finset (Fin (2 * 0))))
        (f : Finset (Fin (2 * 0)) → ℝ) :
        Q.blockProduct f = 1 := by
      have h0 : Q.1.parts.card = 0 := Q.card_parts_of_card_eq (m := 0) (by simp)
      rw [Finset.card_eq_zero] at h0
      simp [Finpartition.Pairing.blockProduct, Finpartition.blockProduct, h0]
    simp only [hb, mul_one, skCavityPathMean_one_const, integral_const, pow_zero,
      probReal_univ, smul_eq_mul, sub_self, abs_zero]
    positivity
  by_cases hn : Nonempty (Fin n)
  · classical
    let Q : Finpartition.Pairing (univ : Finset (Fin (2 * m))) ×
        Finpartition.Pairing (univ : Finset (Fin (2 * m))) × (Fin (2 * m) → Fin n × Fin n) →
        ℝ → Prop := fun x C =>
      (∀ v, (x.2.2 v).1 ≠ (x.2.2 v).2) →
      (∀ u v : Fin (2 * m), u ≠ v →
        (x.2.2 u).1 ≠ (x.2.2 v).1 ∧ (x.2.2 u).1 ≠ (x.2.2 v).2 ∧
        (x.2.2 u).2 ≠ (x.2.2 v).1 ∧ (x.2.2 u).2 ≠ (x.2.2 v).2) →
      ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ),
      let α := (∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 4
        ∂gaussianReal 0 1) - 2 * q + 1
      let A_sq := α / (1 - β ^ 2 * α)
      let Cf := fun (σ : Fin n → Fin (N + 1) → ℤˣ) (u v : Fin (2 * m)) =>
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (x.2.2 u).1 i : ℝ) * (σ (x.2.2 v).1 i : ℝ)) -
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (x.2.2 u).2 i : ℝ) * (σ (x.2.2 v).1 i : ℝ)) -
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (x.2.2 u).1 i : ℝ) * (σ (x.2.2 v).2 i : ℝ)) +
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (x.2.2 u).2 i : ℝ) * (σ (x.2.2 v).2 i : ℝ))
      |skCavityPathMean N n β q h 1 (fun σ =>
          x.1.blockProduct (Renormalization.pairWeight (Cf σ)) *
            x.2.1.blockProduct (Renormalization.pairWeight (Cf σ))) -
        ((N : ℝ) + 1) ⁻¹ ^ m *
          ∫ z : (Fin n × Fin n) ⊕ Fin n → ℝ,
            x.1.blockProduct (Renormalization.pairWeight fun a b => ∑ e : Bool × Bool,
              ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
                (Real.sqrt A_sq * z (Sum.inl
                  (min (if e.1 then (x.2.2 a).2 else (x.2.2 a).1)
                    (if e.2 then (x.2.2 b).2 else (x.2.2 b).1),
                   max (if e.1 then (x.2.2 a).2 else (x.2.2 a).1)
                    (if e.2 then (x.2.2 b).2 else (x.2.2 b).1))))) *
            x.2.1.blockProduct (Renormalization.pairWeight fun a b => ∑ e : Bool × Bool,
              ((if e.1 then (-1 : ℝ) else 1) * (if e.2 then (-1 : ℝ) else 1)) *
                (Real.sqrt A_sq * z (Sum.inl
                  (min (if e.1 then (x.2.2 a).2 else (x.2.2 a).1)
                    (if e.2 then (x.2.2 b).2 else (x.2.2 b).1),
                   max (if e.1 then (x.2.2 a).2 else (x.2.2 a).1)
                    (if e.2 then (x.2.2 b).2 else (x.2.2 b).1)))))
            ∂(Measure.pi fun _ : (Fin n × Fin n) ⊕ Fin n => gaussianReal 0 1)| ≤
        C / ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2)
    have hmono : ∀ x C C', C ≤ C' → Q x C → Q x C' := by
      intro x C C' hCC' hQ hxy hdisj β h q hfix hβ N α A_sq Cf
      have h1 := hQ hxy hdisj β h q hfix hβ N
      dsimp only at h1
      exact h1.trans (div_le_div_of_nonneg_right hCC' (by positivity))
    have hex : ∀ x, ∃ C : ℝ, 0 < C ∧ Q x C := by
      intro x
      by_cases hg : (∀ v, (x.2.2 v).1 ≠ (x.2.2 v).2) ∧
          (∀ u v : Fin (2 * m), u ≠ v →
            (x.2.2 u).1 ≠ (x.2.2 v).1 ∧ (x.2.2 u).1 ≠ (x.2.2 v).2 ∧
            (x.2.2 u).2 ≠ (x.2.2 v).1 ∧ (x.2.2 u).2 ≠ (x.2.2 v).2)
      · obtain ⟨C, hC, hCb⟩ := sk_hanen_full_pairings_gaussian_data β₀ hβ₀ m n x.1 x.2.1 x.2.2
          hg.1 hg.2 hn
        exact ⟨C, hC, fun _ _ => hCb⟩
      · exact ⟨1, one_pos, fun hxy hdisj => absurd ⟨hxy, hdisj⟩ hg⟩
    obtain ⟨K, hK, hKb⟩ := exists_pos_forall_of_finite Q hmono hex
    refine ⟨K, hK, ?_⟩
    intro β h q hfix hβ N P₀ P pairMap hxy hdisj
    exact hKb (P₀, P, pairMap) hxy hdisj β h q hfix hβ N
  · refine ⟨1, one_pos, ?_⟩
    intro β h q hfix hβ N P₀ P pairMap hxy hdisj
    exact absurd ⟨(pairMap ⟨0, by omega⟩).1⟩ hn

/-- Positivity of the variance `A² = α / (1 - β² α)` at a fixed point. -/
theorem hanen_A_sq_nonneg (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (β h q : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q)
    (hβ : β ^ 2 ≤ β₀ ^ 2) :
    0 ≤ ((∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1) - 2 * q + 1) /
      (1 - β ^ 2 * ((∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1)
        - 2 * q + 1)) := by
  have hα := tanh_fourth_sub_two_mul_add_one_mem_Icc_of_fixedPoint hfix
  refine div_nonneg hα.1 ?_
  have h2 : β ^ 2 * ((∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1)
      - 2 * q + 1) ≤ β ^ 2 * 1 := mul_le_mul_of_nonneg_left hα.2 (sq_nonneg _)
  nlinarith [sq_nonneg β₀]

/-- **E3d, same pairing.** The coupled mean of the square of the block product of full
rectangles is `(4 A² / (N+1))^m` up to `O((N+1)^{-(2m+1)/2})`. -/
theorem sk_hanen_full_pairing_sq (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (m n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (P₀ : Finpartition.Pairing (univ : Finset (Fin (2 * m))))
      (pairMap : Fin (2 * m) → Fin n × Fin n), (∀ v, (pairMap v).1 ≠ (pairMap v).2) →
      (∀ u v : Fin (2 * m), u ≠ v →
        (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
        (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2) →
      let α := (∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 4
        ∂gaussianReal 0 1) - 2 * q + 1
      let A_sq := α / (1 - β ^ 2 * α)
      let Cf := fun (σ : Fin n → Fin (N + 1) → ℤˣ) (u v : Fin (2 * m)) =>
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).1 i : ℝ) * (σ (pairMap v).1 i : ℝ)) -
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).2 i : ℝ) * (σ (pairMap v).1 i : ℝ)) -
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).1 i : ℝ) * (σ (pairMap v).2 i : ℝ)) +
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).2 i : ℝ) * (σ (pairMap v).2 i : ℝ))
      |skCavityPathMean N n β q h 1 (fun σ =>
          P₀.blockProduct (Renormalization.pairWeight (Cf σ)) *
            P₀.blockProduct (Renormalization.pairWeight (Cf σ))) -
        (4 * A_sq / ((N : ℝ) + 1)) ^ m| ≤
        K / ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨K, hK, hKb⟩ := sk_hanen_full_pairings_gaussian β₀ hβ₀ m n
  refine ⟨K, hK, ?_⟩
  intro β h q hfix hβ N P₀ pairMap hxy hdisj α A_sq Cf
  have h1 := hKb β h q hfix hβ N P₀ P₀ pairMap hxy hdisj
  dsimp only at h1
  rw [hanen_gaussian_rect_pairing_sq pairMap hxy hdisj (Real.sqrt A_sq) P₀,
    Real.sq_sqrt (hanen_A_sq_nonneg β₀ hβ₀ β h q hfix hβ), ← mul_pow] at h1
  have e : ∀ X : ℝ, ((N : ℝ) + 1)⁻¹ * (4 * X) = 4 * X / ((N : ℝ) + 1) :=
    fun X => inv_mul_eq_div _ _
  simp only [e] at h1
  exact h1

/-- **E3d, different pairings.** For two different pairings the coupled mean of the product of
the two block products of full rectangles is `O((N+1)^{-(2m+1)/2})`: the Gaussian reference
vanishes, because a block of one pairing that is not a block of the other occurs once. -/
theorem sk_hanen_full_pairings_of_ne (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (m n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (P₀ P : Finpartition.Pairing (univ : Finset (Fin (2 * m)))), P ≠ P₀ →
      ∀ (pairMap : Fin (2 * m) → Fin n × Fin n), (∀ v, (pairMap v).1 ≠ (pairMap v).2) →
      (∀ u v : Fin (2 * m), u ≠ v →
        (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
        (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2) →
      let Cf := fun (σ : Fin n → Fin (N + 1) → ℤˣ) (u v : Fin (2 * m)) =>
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).1 i : ℝ) * (σ (pairMap v).1 i : ℝ)) -
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).2 i : ℝ) * (σ (pairMap v).1 i : ℝ)) -
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).1 i : ℝ) * (σ (pairMap v).2 i : ℝ)) +
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap u).2 i : ℝ) * (σ (pairMap v).2 i : ℝ))
      |skCavityPathMean N n β q h 1 (fun σ =>
          P₀.blockProduct (Renormalization.pairWeight (Cf σ)) *
            P.blockProduct (Renormalization.pairWeight (Cf σ)))| ≤
        K / ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨K, hK, hKb⟩ := sk_hanen_full_pairings_gaussian β₀ hβ₀ m n
  refine ⟨K, hK, ?_⟩
  intro β h q hfix hβ N P₀ P hne pairMap hxy hdisj Cf
  have h1 := hKb β h q hfix hβ N P₀ P pairMap hxy hdisj
  dsimp only at h1
  rw [hanen_gaussian_rect_pairings_of_ne pairMap hxy hdisj _ P₀ P hne, mul_zero, sub_zero] at h1
  exact h1

end SpinGlasses
