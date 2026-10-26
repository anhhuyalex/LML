/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKSecondMoment

/-!
# The variance of the truncated spin correlation (Talagrand's Corollary 1.8.6)

Site symmetry decomposes `ν(rect²)` into the diagonal term `ν(a_N²)/M` and the off-diagonal term
`(M-1)/M · ν(a_1 a_2)`; the latter is `4 𝔼(⟨σ_1σ_2⟩ - ⟨σ_1⟩⟨σ_2⟩)²` because the replicas `(1,2)` and
`(3,4)` are independent.  Proposition 1.8.5 for `ν(rect²)` and Eq. (1.215) for `ν(a_N²)` then give
`𝔼(⟨σ_1σ_2⟩ - ⟨σ_1⟩⟨σ_2⟩)² = β² c₂² / (M (1 - β² c₂)) + O(M^{-3/2})`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- Finite combinations commute with an `n`-replica SK average. -/
theorem sk_replica_avg_sum (N n : ℕ) (β h : ℝ)
    (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (Φ : ι → (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    ν (fun σ => ∑ j ∈ s, c j * Φ j σ) = ∑ j ∈ s, c j * ν (Φ j) :=
  sk_replica_avg_finset_sum N n β h ν hν s c Φ

/-- **Diagonal and off-diagonal parts of `ν(rect²)`** (Corollary 1.8.6): with
`a_k = (σ¹_k - σ²_k)(σ³_k - σ⁴_k)`, `rect = M⁻¹ ∑_k a_k` and `M = N + 1`,
`ν(rect²) = ν(a_N²)/M + (M-1)/M · ν(a_i a_j)` for any two distinct sites `i ≠ j`. -/
theorem sk_rect_sq_eq_diag_add_offdiag (N : ℕ) (β h : ℝ)
    (ν : ((Fin 4 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    {i j : Fin (N + 1)} (hij : i ≠ j) :
    let a : Fin (N + 1) → (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun k σ =>
      (((σ 0 k : ℤˣ) : ℝ) - ((σ 1 k : ℤˣ) : ℝ)) * (((σ 2 k : ℤˣ) : ℝ) - ((σ 3 k : ℤˣ) : ℝ))
    let rect : (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
      (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ) - (σ 1 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 2 i : ℝ) - (σ 3 i : ℝ))
    ν (fun σ => rect σ ^ 2) = 1 / ((N : ℝ) + 1) * ν (fun σ => a (Fin.last N) σ ^ 2) +
      (((N : ℝ) + 1 - 1) / ((N : ℝ) + 1)) * ν (fun σ => a i σ * a j σ) := by
  intro a rect
  -- symmetry of the pair averages
  have hperm : ∀ (pm : Equiv.Perm (Fin (N + 1))) (k l : Fin (N + 1)),
      ν (fun σ => a (pm k) σ * a (pm l) σ) = ν (fun σ => a k σ * a l σ) := fun pm k l => by
    rw [hν, hν]
    have := sk_replica_site_perm (R := Fin 4) N β h pm (fun σ => a k σ * a l σ)
    exact this
  have hdiag : ∀ k, ν (fun σ => a k σ * a k σ) = ν (fun σ => a (Fin.last N) σ ^ 2) := fun k => by
    have := hperm (Equiv.swap k (Fin.last N)) k k
    simp only [Equiv.swap_apply_left] at this
    simp only [sq]
    exact this.symm
  have hpair : ∀ k l : Fin (N + 1), k ≠ l → ν (fun σ => a k σ * a l σ) =
      ν (fun σ => a i σ * a j σ) := fun k l hkl => by
    let π₁ : Equiv.Perm (Fin (N + 1)) := Equiv.swap i k
    have h1 : π₁ i = k := Equiv.swap_apply_left i k
    have h2 : π₁ j ≠ k := fun h => hij (π₁.injective (h.trans h1.symm)).symm
    let π₂ : Equiv.Perm (Fin (N + 1)) := Equiv.swap (π₁ j) l
    have h3 : π₂ k = k := Equiv.swap_apply_of_ne_of_ne (Ne.symm h2) hkl
    have h4 : π₂ (π₁ j) = l := Equiv.swap_apply_left _ _
    have := hperm (π₁.trans π₂) i j
    simp only [Equiv.trans_apply, h1, h3, h4] at this
    exact this
  have hΞ : ∀ k l : Fin (N + 1), ν (fun σ => a k σ * a l σ) =
      ν (fun σ => a i σ * a j σ) + if k = l then
        (ν (fun σ => a (Fin.last N) σ ^ 2) - ν (fun σ => a i σ * a j σ)) else 0 := fun k l => by
    by_cases hkl : k = l
    · subst hkl
      simp [hdiag]
    · simp [hkl, hpair k l hkl]
  have hrect : ∀ σ, rect σ ^ 2 = ∑ p : Fin (N + 1) × Fin (N + 1),
      (1 / ((N : ℝ) + 1) ^ 2) * (a p.1 σ * a p.2 σ) := fun σ => by
    have hr : rect σ = (N + 1 : ℝ)⁻¹ * ∑ k, a k σ := by
      simp only [rect, a, dotProduct]
    rw [hr, mul_pow, ← Finset.mul_sum, Fintype.sum_prod_type, sq (∑ k, a k σ),
      Finset.sum_mul_sum]
    simp only [inv_pow, one_div]
  have hsum := sk_replica_avg_sum N 4 β h ν hν (Finset.univ : Finset (Fin (N + 1) × Fin (N + 1)))
    (fun _ => 1 / ((N : ℝ) + 1) ^ 2) (fun p σ => a p.1 σ * a p.2 σ)
  rw [show (fun σ => rect σ ^ 2) = fun σ => ∑ p ∈ (Finset.univ : Finset (Fin (N + 1) ×
      Fin (N + 1))), (1 / ((N : ℝ) + 1) ^ 2) * (a p.1 σ * a p.2 σ) from funext hrect, hsum,
    Fintype.sum_prod_type]
  generalize ν (fun σ => a i σ * a j σ) = Pij at hΞ ⊢
  generalize ν (fun σ => a (Fin.last N) σ ^ 2) = Paa at hΞ ⊢
  simp only [hΞ]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.mul_sum]
  have hM : ((N : ℝ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero N
  push_cast
  field_simp
  ring


/-- The elementary estimate behind Corollary 1.8.6: solving
`X = Pa/M + (M-1)/M · 4V` for the variance `V`. -/
theorem pair_variance_arith {X Pa V M lam c2 E e : ℝ} (hM : 2 ≤ M) (hlam0 : 0 ≤ lam)
    (hlam1 : lam ≤ 1 / 4) (hc0 : 0 ≤ c2) (hc1 : c2 ≤ 1)
    (hX : |X - 4 * c2 / (M * (1 - lam))| ≤ E) (hPa : |Pa - 4 * c2| ≤ e)
    (hrel : X = Pa / M + (M - 1) / M * (4 * V)) :
    |V - lam * c2 / (M * (1 - lam))| ≤ 2 / 3 / M ^ 2 + E / 2 + e / (2 * M) := by
  have hM0 : 0 < M := by linarith
  have hM1 : 0 < M - 1 := by linarith
  have hD : 0 < 1 - lam := by linarith
  set E₁ := X - 4 * c2 / (M * (1 - lam)) with hE₁
  set e₁ := Pa - 4 * c2 with he₁
  have hV : V - lam * c2 / (M * (1 - lam)) =
      lam * c2 / ((1 - lam) * M * (M - 1)) + (M * E₁ - e₁) / (4 * (M - 1)) := by
    have h4V : 4 * V = (M * X - Pa) / (M - 1) := by
      field_simp
      field_simp at hrel
      linarith
    have : V = (M * X - Pa) / (4 * (M - 1)) := by
      field_simp at h4V ⊢
      linarith
    rw [this, hE₁, he₁]
    field_simp
    ring
  rw [hV]
  have t1 : |lam * c2 / ((1 - lam) * M * (M - 1))| ≤ 2 / 3 / M ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    have h1 : lam * c2 ≤ 1 / 4 := by nlinarith
    have h2 : (3 : ℝ) / 4 ≤ 1 - lam := by linarith
    have h3 : M / 2 ≤ M - 1 := by linarith
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hM0 hM0, mul_pos hD hM0, mul_pos (mul_pos hD hM0) hM1, sq_nonneg M]
  have t2 : |(M * E₁ - e₁) / (4 * (M - 1))| ≤ E / 2 + e / (2 * M) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 4 * (M - 1))]
    have h1 : |M * E₁ - e₁| ≤ M * E + e := by
      calc _ ≤ |M * E₁| + |e₁| := abs_sub _ _
        _ ≤ M * E + e := by
          rw [abs_mul, abs_of_pos hM0]
          exact add_le_add (mul_le_mul_of_nonneg_left hX hM0.le) hPa
    rw [div_le_iff₀ (by positivity)]
    have : (E / 2 + e / (2 * M)) * (4 * (M - 1)) ≥ (E / 2 + e / (2 * M)) * (2 * M) := by
      apply mul_le_mul_of_nonneg_left _ (by
        have := (abs_nonneg _).trans hX
        have := (abs_nonneg _).trans hPa
        positivity)
      linarith
    have e2 : (E / 2 + e / (2 * M)) * (2 * M) = M * E + e := by field_simp
    linarith
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add t1 t2
    _ = _ := by ring

/-- `ν(a_i a_j) = 4 𝔼(⟨σ_iσ_j⟩ - ⟨σ_i⟩⟨σ_j⟩)²`: the replicas `(1,2)` and `(3,4)` are independent. -/
theorem sk_nu_a_prod_eq_cov_sq (N : ℕ) (β h : ℝ)
    (ν : ((Fin 4 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (i j : Fin (N + 1)) :
    ν (fun σ => ((((σ 0 i : ℤˣ) : ℝ) - ((σ 1 i : ℤˣ) : ℝ)) * (((σ 2 i : ℤˣ) : ℝ) -
        ((σ 3 i : ℤˣ) : ℝ))) * ((((σ 0 j : ℤˣ) : ℝ) - ((σ 1 j : ℤˣ) : ℝ)) *
          (((σ 2 j : ℤˣ) : ℝ) - ((σ 3 j : ℤˣ) : ℝ)))) =
      4 * ∫ g : FinPairs (N + 1) → ℝ,
        ((∫ x : Fin (N + 1) → ℤˣ, ((x i : ℤˣ) : ℝ) * ((x j : ℤˣ) : ℝ)
            ∂(Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ))) -
          (∫ x : Fin (N + 1) → ℤˣ, ((x i : ℤˣ) : ℝ)
            ∂(Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ))) *
            ∫ x : Fin (N + 1) → ℤˣ, ((x j : ℤˣ) : ℝ)
            ∂(Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ))) ^ 2
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  rw [hν, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  beta_reduce
  exact Eq.trans (integral_congr_ae (ae_of_all _ fun σ => by ring))
    (integral_four_replicas_cov_sq _ i j)

/-- **Talagrand's Corollary 1.8.6 (Eq. (1.244))** for the `(N+1)`-spin system, `i ≠ j` two sites:
`𝔼(⟨σ_iσ_j⟩ - ⟨σ_i⟩⟨σ_j⟩)² = β² c₂² / ((N+1)(1 - β² c₂)) + O((N+1)^{-3/2})` with
`c₂ = 1 - 2q + q̂`, uniformly in `|β| ≤ β₀ < 1/2`. -/
theorem sk_truncated_pair_variance (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (h : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β q : ℝ), |β| ≤ β₀ →
      (∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q) →
      ∀ (N : ℕ) (i j : Fin (N + 1)), i ≠ j →
      |(∫ g : FinPairs (N + 1) → ℝ,
        ((∫ x : Fin (N + 1) → ℤˣ, ((x i : ℤˣ) : ℝ) * ((x j : ℤˣ) : ℝ)
            ∂(Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ))) -
          (∫ x : Fin (N + 1) → ℤˣ, ((x i : ℤˣ) : ℝ)
            ∂(Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ))) *
            ∫ x : Fin (N + 1) → ℤˣ, ((x j : ℤˣ) : ℝ)
            ∂(Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ))) ^ 2
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
        β ^ 2 * ((∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1)) -
            2 * q + 1) ^ 2 /
          (((N : ℝ) + 1) * (1 - β ^ 2 * ((∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4
            ∂(gaussianReal 0 1)) - 2 * q + 1)))| ≤ K / Real.sqrt ((N : ℝ) + 1) ^ 3 := by
  obtain ⟨KX, hKX, hX⟩ := sk_rect_second_moment β₀ hβ₀ h
  obtain ⟨K₁, hK₁, hM1⟩ := sk_dev_moment_le β₀ hβ₀ 1
  set Ce : ℝ := 256 * β₀ ^ 2 * Real.exp (144 * β₀ ^ 2) * (K₁ + 1) with hCe
  have hCe0 : 0 ≤ Ce := by positivity
  refine ⟨2 / 3 + KX / 2 + Ce / 2 + 1, by positivity, fun β q hβ hfix N i j hij => ?_⟩
  have hβ2 : β ^ 2 ≤ β₀ ^ 2 := by
    rw [← sq_abs β]
    exact pow_le_pow_left₀ (abs_nonneg _) hβ 2
  have hβ4 : 4 * β ^ 2 < 1 := by linarith
  have hD2 := hM1 β h q hfix hβ2 N
  simp only [mul_one, pow_one] at hD2
  set c₂ : ℝ := (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1)) -
    2 * q + 1 with hc₂def
  have hc₂ : c₂ ∈ Set.Icc (0 : ℝ) 1 := by
    have := tanh_fourth_sub_two_add_one_mem_Icc (β * Real.sqrt q) h
    rwa [hfix] at this
  have hlam0 : 0 ≤ β ^ 2 * c₂ := mul_nonneg (sq_nonneg _) hc₂.1
  have hlam1 : β ^ 2 * c₂ ≤ 1 / 4 := by nlinarith only [hc₂.2, sq_nonneg β, hβ4]
  obtain ⟨ν, hν⟩ : ∃ ν : ((Fin 4 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ, ∀ Φ, ν Φ =
      ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Φ σ
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := ⟨_, fun _ => rfl⟩
  have hrel := sk_rect_sq_eq_diag_add_offdiag N β h ν hν hij
  have hcov := sk_nu_a_prod_eq_cov_sq N β h ν hν i j
  obtain ⟨ν₀, -, -, hC3⟩ := sk_rect_nu_decoupled N β h q hfix ν hν
  have hD1 := sk_abs_dev_le N β h q K₁ hD2
  have hXb := hX β q hβ hfix N
  simp only [] at hrel hC3
  have hM2 : (2 : ℝ) ≤ (N : ℝ) + 1 := by
    have : 2 ≤ Fintype.card (Fin (N + 1)) := Fintype.one_lt_card_iff.2 ⟨i, j, hij⟩
    simp only [Fintype.card_fin] at this
    have : (2 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast this
    simpa using this
  have hs1 : 1 ≤ Real.sqrt ((N : ℝ) + 1) := by
    rw [Real.one_le_sqrt]; linarith
  have hs0 : 0 < Real.sqrt ((N : ℝ) + 1) := by linarith
  have hs2 : Real.sqrt ((N : ℝ) + 1) ^ 2 = (N : ℝ) + 1 := Real.sq_sqrt (by linarith)
  have hPa : |ν (fun σ => ((((σ 0 (Fin.last N) : ℤˣ) : ℝ) - ((σ 1 (Fin.last N) : ℤˣ) : ℝ)) *
        (((σ 2 (Fin.last N) : ℤˣ) : ℝ) - ((σ 3 (Fin.last N) : ℤˣ) : ℝ))) ^ 2) - 4 * c₂| ≤
      Ce / Real.sqrt ((N : ℝ) + 1) := by
    refine hC3.trans ?_
    have h1 : 32 * β ^ 2 * Real.exp (144 * β ^ 2) * 16 *
        ((K₁ + 1) / (2 * Real.sqrt ((N : ℝ) + 1))) ≤
        Ce / Real.sqrt ((N : ℝ) + 1) := by
      have e : 32 * β ^ 2 * Real.exp (144 * β ^ 2) * 16 *
          ((K₁ + 1) / (2 * Real.sqrt ((N : ℝ) + 1))) =
          256 * β ^ 2 * Real.exp (144 * β ^ 2) * (K₁ + 1) / Real.sqrt ((N : ℝ) + 1) := by
        field_simp
        ring
      rw [e]
      refine div_le_div_of_nonneg_right ?_ hs0.le
      have : Real.exp (144 * β ^ 2) ≤ Real.exp (144 * β₀ ^ 2) :=
        Real.exp_le_exp.2 (by linarith)
      rw [hCe]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hβ2 (by norm_num))
        this (by positivity) (by positivity)) (by linarith)
    exact le_trans (mul_le_mul_of_nonneg_left hD1 (by positivity)) h1
  set V : ℝ := ∫ g : FinPairs (N + 1) → ℝ,
      ((∫ x : Fin (N + 1) → ℤˣ, ((x i : ℤˣ) : ℝ) * ((x j : ℤˣ) : ℝ)
          ∂(Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))) -
        (∫ x : Fin (N + 1) → ℤˣ, ((x i : ℤˣ) : ℝ)
          ∂(Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))) *
          ∫ x : Fin (N + 1) → ℤˣ, ((x j : ℤˣ) : ℝ)
          ∂(Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))) ^ 2
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) with hV
  have key := pair_variance_arith (X := ν (fun σ => ((N + 1 : ℝ)⁻¹ *
      ((fun i : Fin (N + 1) => (σ 0 i : ℝ) - (σ 1 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 2 i : ℝ) - (σ 3 i : ℝ))) ^ 2))
    (Pa := ν (fun σ => ((((σ 0 (Fin.last N) : ℤˣ) : ℝ) - ((σ 1 (Fin.last N) : ℤˣ) : ℝ)) *
        (((σ 2 (Fin.last N) : ℤˣ) : ℝ) - ((σ 3 (Fin.last N) : ℤˣ) : ℝ))) ^ 2))
    (V := V) (M := (N : ℝ) + 1) (lam := β ^ 2 * c₂) (c2 := c₂)
    (E := KX / Real.sqrt ((N : ℝ) + 1) ^ 3) (e := Ce / Real.sqrt ((N : ℝ) + 1)) hM2 hlam0
    hlam1 hc₂.1 hc₂.2 (by rw [hν]; exact hXb) hPa (by rw [hrel, hcov]; ring)
  rw [show β ^ 2 * c₂ ^ 2 = β ^ 2 * c₂ * c₂ by ring]
  refine key.trans ?_
  clear_value c₂ V
  generalize hs : Real.sqrt ((N : ℝ) + 1) = s at *
  have hMs : (N : ℝ) + 1 = s ^ 2 := hs2.symm
  rw [hMs]
  have hs3 : 0 < s ^ 3 := by positivity
  have hs1' : s ^ 3 ≤ s ^ 4 := pow_le_pow_right₀ hs1 (by norm_num)
  have t1 : 2 / 3 / (s ^ 2) ^ 2 ≤ (2 / 3) / s ^ 3 := by
    have : (s ^ 2) ^ 2 = s ^ 4 := by ring
    rw [this]
    exact div_le_div_of_nonneg_left (by norm_num) hs3 hs1'
  have t2 : Ce / s / (2 * s ^ 2) = Ce / 2 / s ^ 3 := by
    field_simp
  calc _ ≤ 2 / 3 / s ^ 3 + KX / s ^ 3 / 2 + Ce / 2 / s ^ 3 := by
        rw [← t2]
        linarith only [t1]
    _ = (2 / 3 + KX / 2 + Ce / 2) / s ^ 3 := by ring
    _ ≤ _ := by
        refine div_le_div_of_nonneg_right ?_ hs3.le
        linarith

end SpinGlasses
