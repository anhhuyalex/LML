/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKSecondMoment

/-!
# Higher-order cavity errors (Talagrand, Section 1.10)

A truncated centered overlap contributes one inverse square root of the system size.
We use the uniform high-temperature moments of Section 1.7, the exact last-spin split,
and the existing cavity Taylor estimates of Section 1.8. All constants are chosen before
`N`; the number of sites is `N + 1`, including when `N = 0`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Eq. (1.296), even powers.** Truncating the last site preserves the uniform moment
scale, for any two distinct replicas in any finite replica type. -/
theorem sk_cavity_dev_even_moment_le (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (r : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) {R : Type*} [Fintype R] (x y : R), x ≠ y →
      ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : R → Fin (N + 1) → ℤˣ,
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ x i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (σ y i.castSucc : ℝ)) - q) ^ (2 * r)
          ∂(Measure.pi fun _ : R => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
        K / ((N : ℝ) + 1) ^ r := by
  obtain ⟨K, hK0, hK⟩ := sk_dev_moment_le β₀ hβ₀ r
  refine ⟨2 ^ (2 * r - 1) * (K + 1), by positivity, ?_⟩
  intro β h q hfix hb N R _ x y hxy
  let E := fun (g : FinPairs (N + 1) → ℝ) (a : Fin (N + 1) → ℤˣ) =>
    (Real.sqrt (N + 1))⁻¹ * β *
      (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
  let D := fun (a b : Fin (N + 1) → ℤˣ) =>
    (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (a i : ℝ)) ⬝ᵥ
      fun i : Fin (N + 1) => (b i : ℝ)) - q
  let Dm := fun (a b : Fin (N + 1) → ℤˣ) =>
    (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ
      fun i : Fin N => (b i.castSucc : ℝ)) - q
  have hpt (a b : Fin (N + 1) → ℤˣ) :
      Dm a b ^ (2 * r) ≤ 2 ^ (2 * r - 1) *
        (D a b ^ (2 * r) + ((N : ℝ) + 1)⁻¹ ^ (2 * r)) := by
    have he : Dm a b = D a b +
        (-((N : ℝ) + 1)⁻¹ * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ)) := by
      dsimp [Dm, D]
      rw [sk_overlap_succ_eq_cavity]
      ring
    have hl : |-((N : ℝ) + 1)⁻¹ * (a (Fin.last N) : ℝ) *
        (b (Fin.last N) : ℝ)| = ((N : ℝ) + 1)⁻¹ := by
      simp [abs_mul, abs_units_cast_eq_one, abs_of_nonneg (by positivity : 0 ≤ ((N : ℝ) + 1)⁻¹)]
    have ht := abs_add_pow_le (D a b)
      (-((N : ℝ) + 1)⁻¹ * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ)) (2 * r)
    rw [← he, hl, Even.pow_abs (by exact ⟨r, by omega⟩),
      Even.pow_abs (by exact ⟨r, by omega⟩)] at ht
    exact ht
  have hm : (∫ g : FinPairs (N + 1) → ℝ,
      ∫ σ : R → Fin (N + 1) → ℤˣ, D (σ x) (σ y) ^ (2 * r)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ≤
      K / ((N : ℝ) + 1) ^ r := by
    simp_rw [integral_pi_count_tilted_pair hxy (E _) (fun a b => D a b ^ (2 * r))]
    exact hK β h q hfix hb N
  have hint (F : (R → Fin (N + 1) → ℤˣ) → ℝ) :
      Integrable (fun g : FinPairs (N + 1) → ℝ =>
        ∫ σ : R → Fin (N + 1) → ℤˣ, F σ
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)))
        (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
    integrable_integral_pi_count_tilted_det
      (g := fun a g => E g a) (by intro a; fun_prop) F
  have hs : ((N : ℝ) + 1)⁻¹ ^ (2 * r) ≤ 1 / ((N : ℝ) + 1) ^ r := by
    rw [one_div, ← inv_pow]
    exact pow_le_pow_of_le_one (by positivity) (by
      exact (inv_le_one₀ (by positivity)).2 (by linarith)) (by omega)
  change (∫ g, ∫ σ : R → Fin (N + 1) → ℤˣ, Dm (σ x) (σ y) ^ (2 * r)
    ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
    ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ≤ _
  calc
    _ ≤ ∫ g, ∫ σ : R → Fin (N + 1) → ℤˣ,
        2 ^ (2 * r - 1) * (D (σ x) (σ y) ^ (2 * r) + ((N : ℝ) + 1)⁻¹ ^ (2 * r))
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
      integral_mono (hint _) (hint _) fun g =>
        integral_mono Integrable.of_finite Integrable.of_finite fun σ => hpt _ _
    _ = 2 ^ (2 * r - 1) * ((∫ g, ∫ σ : R → Fin (N + 1) → ℤˣ,
        D (σ x) (σ y) ^ (2 * r)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) +
        ((N : ℝ) + 1)⁻¹ ^ (2 * r)) := by
      simp_rw [integral_const_mul, integral_add Integrable.of_finite (integrable_const _),
        integral_const, probReal_univ, one_smul]
      rw [integral_add (hint _) (integrable_const _)]
      simp
    _ ≤ 2 ^ (2 * r - 1) * (K / ((N : ℝ) + 1) ^ r + 1 / ((N : ℝ) + 1) ^ r) :=
      mul_le_mul_of_nonneg_left (add_le_add hm hs) (by positivity)
    _ = _ := by ring

/-- **Eq. (1.297), squared form.** A bounded factor times a product of `k` truncated
centered overlaps has second moment at most `K / (N+1)^k`. Replica pairs may repeat and
share indices; only the two indices within each pair must be distinct. -/
theorem sk_cavity_prod_sq_le (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (k : ℕ)
    (M : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N n : ℕ) (x y : Fin k → Fin n),
      (∀ j, x j ≠ y j) → ∀ W : (Fin n → Fin (N + 1) → ℤˣ) → ℝ,
      (∀ σ, |W σ| ≤ M) →
      ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
          (W σ * ∏ j : Fin k, ((N + 1 : ℝ)⁻¹ *
            ((fun i : Fin N => (σ (x j) i.castSucc : ℝ)) ⬝ᵥ
              fun i : Fin N => (σ (y j) i.castSucc : ℝ)) - q)) ^ 2
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
        K / ((N : ℝ) + 1) ^ k := by
  by_cases hk : k = 0
  · subst k
    refine ⟨M ^ 2 + 1, by positivity, fun β h q _ _ N n x y _ W hW => ?_⟩
    simp only [Fin.prod_univ_zero, mul_one, pow_zero, div_one]
    have hpt (σ : Fin n → Fin (N + 1) → ℤˣ) : W σ ^ 2 ≤ M ^ 2 + 1 := by
      have := pow_le_pow_left₀ (abs_nonneg _) (hW σ) 2
      rw [sq_abs] at this
      linarith
    exact (integral_integral_sk_replica_mono N n β h hpt).trans_eq (by simp)
  obtain ⟨C, hC0, hC⟩ := sk_cavity_dev_even_moment_le β₀ hβ₀ k
  refine ⟨M ^ 2 * k * C + 1, by positivity, ?_⟩
  intro β h q hfix hb N n x y hxy W hW
  let D : Fin k → (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun j σ =>
    (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (x j) i.castSucc : ℝ)) ⬝ᵥ
      fun i : Fin N => (σ (y j) i.castSucc : ℝ)) - q
  let ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun F =>
    ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, F σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  have hpt (σ : Fin n → Fin (N + 1) → ℤˣ) :
      (W σ * ∏ j : Fin k, D j σ) ^ 2 ≤ M ^ 2 * ∑ j : Fin k, D j σ ^ (2 * k) := by
    have he : (∏ j : Fin k, D j σ) ^ 2 ≤ ∑ j : Fin k, D j σ ^ (2 * k) := by
      have hp := prod_abs_le_sum_pow (Finset.univ : Finset (Fin k))
        (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hk)))
        (fun j => D j σ ^ 2)
      simpa only [abs_pow, sq_abs, Finset.prod_pow, Finset.card_univ,
        Fintype.card_fin, ← pow_mul] using hp
    have hw : W σ ^ 2 ≤ M ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hW σ) 2
    rw [mul_pow]
    exact mul_le_mul hw he (sq_nonneg _) (sq_nonneg _)
  change ν (fun σ => (W σ * ∏ j : Fin k, D j σ) ^ 2) ≤ _
  calc
    _ ≤ ν (fun σ => M ^ 2 * ∑ j : Fin k, D j σ ^ (2 * k)) :=
      sk_replica_avg_mono N n β h ν (fun _ => rfl) _ _ hpt
    _ = M ^ 2 * ∑ j : Fin k, ν (fun σ => D j σ ^ (2 * k)) := by
      rw [sk_replica_avg_smul N n β h ν (fun _ => rfl)]
      congr 1
      simpa only [one_mul] using sk_replica_avg_finset_sum N n β h ν
        (fun _ => rfl) Finset.univ (fun _ : Fin k => 1) (fun j σ => D j σ ^ (2 * k))
    _ ≤ M ^ 2 * ∑ _j : Fin k, C / ((N : ℝ) + 1) ^ k := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact Finset.sum_le_sum fun j _ => hC β h q hfix hb N (x j) (y j) (hxy j)
    _ ≤ (M ^ 2 * k * C + 1) / ((N : ℝ) + 1) ^ k := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [show M ^ 2 * ((k : ℝ) * (C / ((N : ℝ) + 1) ^ k)) =
        (M ^ 2 * k * C) / ((N : ℝ) + 1) ^ k by ring]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- **Uniform Eqs. (1.298)--(1.299) from an observable's second-moment bound.**
Choose the constant before the temperature, field, fixed point, size and observable.
The temperature ranges over `β² ≤ β₀²`, with `4 β₀² < 1`. -/
theorem sk_cavity_expansion_of_sq_le_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    (n k : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ),
    (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ ^ 2
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ≤
        H / ((N : ℝ) + 1) ^ k →
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) →
        (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let J : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)) - q)
    |(∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((k + 1 : ℕ) : ℝ) / 2) ∧
    |(∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f (fun r => τ (some (some r))) *
            ((∑ p : Fin n × Fin n with p.1 < p.2,
                J (τ (some (some p.1))) (τ (some (some p.2)))) -
              (n : ℝ) * ∑ r : Fin n, J (τ (some (some r))) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) / 2 * J (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) := by
  obtain ⟨A, hA0, hA⟩ := sk_dev_moment_le β₀ hβ₀ 1
  obtain ⟨B₄, hB₄0, hB₄⟩ := sk_dev_moment_le β₀ hβ₀ 2
  let c₁ := 2 * (n : ℝ) ^ 2 * β₀ ^ 2 * Real.exp (4 * ((n : ℝ) + 2) ^ 2 * β₀ ^ 2)
  let c₂ := 4 * (n : ℝ) ^ 2 * ((n : ℝ) + 2) ^ 2 * β₀ ^ 4 *
    Real.exp (4 * ((n : ℝ) + 4) ^ 2 * β₀ ^ 2)
  let C₁ := c₁ * Real.sqrt H * Real.sqrt A
  let C₂ := c₂ * Real.sqrt H * Real.sqrt B₄
  have hc₁ : 0 ≤ c₁ := by positivity
  have hc₂ : 0 ≤ c₂ := by positivity
  have hC₁ : 0 ≤ C₁ := by positivity
  have hC₂ : 0 ≤ C₂ := by positivity
  refine ⟨C₁ + C₂ + 1, by positivity, ?_⟩
  intro β h q hfix hβle N f hf B E Esk J
  have hs (a : ℝ) (ha : 0 ≤ a) (j : ℕ) :
      Real.sqrt (a / ((N : ℝ) + 1) ^ j) =
        Real.sqrt a / Real.sqrt ((N : ℝ) + 1) ^ j := by
    rw [Real.sqrt_div ha, Real.sqrt_pow_nat (by positivity)]
  have hp := Real.sqrt_le_sqrt hf
  rw [hs H hH k] at hp
  have ha := Real.sqrt_le_sqrt (hA β h q hfix hβle N)
  rw [hs A hA0.le 1] at ha
  have hb := Real.sqrt_le_sqrt (hB₄ β h q hfix hβle N)
  rw [hs B₄ hB₄0.le 2] at hb
  have h₁ := sk_cavity_nu_sub_nu_zero_le N n β q h (fixedPoint_mem_Icc hfix)
    f Real.HolderConjugate.two_two
  simp only [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] at h₁
  have h₂ := sk_cavity_nu_sub_nu_zero_sub_deriv_le_two N n β q h
    (fixedPoint_mem_Icc hfix) f
  have hβ4 : β ^ 4 ≤ β₀ ^ 4 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg β) hβle 2
  have hb₁ : 2 * (n : ℝ) ^ 2 * β ^ 2 *
      Real.exp (4 * ((n : ℝ) + 2) ^ 2 * β ^ 2) ≤ c₁ := by
    dsimp [c₁]
    gcongr
  have hb₂ : 4 * (n : ℝ) ^ 2 * ((n : ℝ) + 2) ^ 2 * β ^ 4 *
      Real.exp (4 * ((n : ℝ) + 4) ^ 2 * β ^ 2) ≤ c₂ := by
    dsimp [c₂]
    gcongr
  have hd (j : ℕ) : ((N : ℝ) + 1) ^ (((k + j : ℕ) : ℝ) / 2) =
      Real.sqrt ((N : ℝ) + 1) ^ (k + j) := by
    rw [Real.rpow_div_two_eq_sqrt _ (by positivity), Real.rpow_natCast]
  constructor
  · refine h₁.trans ?_
    calc
      _ ≤ c₁ * ((Real.sqrt H / Real.sqrt ((N : ℝ) + 1) ^ k) *
          (Real.sqrt A / Real.sqrt ((N : ℝ) + 1) ^ 1)) :=
        mul_le_mul hb₁ (mul_le_mul hp ha (Real.sqrt_nonneg _) (by positivity))
          (by positivity) hc₁
      _ = C₁ / ((N : ℝ) + 1) ^ (((k + 1 : ℕ) : ℝ) / 2) := by
        rw [hd 1, pow_add]
        dsimp [C₁]
        ring
      _ ≤ (C₁ + C₂ + 1) / ((N : ℝ) + 1) ^ (((k + 1 : ℕ) : ℝ) / 2) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
  · refine h₂.trans ?_
    calc
      _ ≤ c₂ * ((Real.sqrt H / Real.sqrt ((N : ℝ) + 1) ^ k) *
          (Real.sqrt B₄ / Real.sqrt ((N : ℝ) + 1) ^ 2)) :=
        mul_le_mul hb₂ (mul_le_mul hp hb (Real.sqrt_nonneg _) (by positivity))
          (by positivity) hc₂
      _ = C₂ / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) := by
        rw [hd 2, pow_add]
        dsimp [C₂]
        ring
      _ ≤ (C₁ + C₂ + 1) / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- **Eqs. (1.298)--(1.299) from an observable's second-moment bound.** The constant
is chosen before the size and the observable. This separates the analytic Taylor estimate
from the representation used to prove the observable's moment scale. -/
theorem sk_cavity_expansion_of_sq_le (β h q : ℝ) (hβ : 4 * β ^ 2 < 1)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q)
    (n k : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ),
    (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ ^ 2
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ≤
        H / ((N : ℝ) + 1) ^ k →
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) →
        (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let J : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)) - q)
    |(∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((k + 1 : ℕ) : ℝ) / 2) ∧
    |(∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f (fun r => τ (some (some r))) *
            ((∑ p : Fin n × Fin n with p.1 < p.2,
                J (τ (some (some p.1))) (τ (some (some p.2)))) -
              (n : ℝ) * ∑ r : Fin n, J (τ (some (some r))) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) / 2 * J (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := sk_cavity_expansion_of_sq_le_uniform β hβ n k H hH
  exact ⟨C, hC0, hC β h q hfix le_rfl⟩

/-- **Eqs. (1.298)--(1.299) for products of truncated centered overlaps.** The bounded
factor may depend on every spin, including the last. The same positive constant works for
both errors and is chosen before the system size, replica pairs and bounded factor.
The derivative is the actual decoupled cavity derivative with its signed replica sum. -/
theorem sk_cavity_prod_expansion_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    (n k : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (x y : Fin k → Fin n), (∀ j, x j ≠ y j) →
    ∀ W : (Fin n → Fin (N + 1) → ℤˣ) → ℝ, (∀ σ, |W σ| ≤ M) →
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) →
        (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let J : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)) - q)
    let f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
      W σ * ∏ j : Fin k, ((N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (σ (x j) i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ (y j) i.castSucc : ℝ)) - q)
    |(∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((k + 1 : ℕ) : ℝ) / 2) ∧
    |(∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f (fun r => τ (some (some r))) *
            ((∑ p : Fin n × Fin n with p.1 < p.2,
                J (τ (some (some p.1))) (τ (some (some p.2)))) -
              (n : ℝ) * ∑ r : Fin n, J (τ (some (some r))) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) / 2 * J (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) := by
  obtain ⟨H, hH0, hH⟩ := sk_cavity_prod_sq_le β₀ hβ₀ k M
  obtain ⟨C, hC0, hC⟩ := sk_cavity_expansion_of_sq_le_uniform β₀ hβ₀ n k H hH0.le
  refine ⟨C, hC0, ?_⟩
  intro β h q hfix hb N x y hxy W hW B E Esk J f
  exact hC β h q hfix hb N f (hH β h q hfix hb N n x y hxy W hW)

/-- **Eqs. (1.298)--(1.299) with fixed model parameters.** A specialization of the
uniform product estimate; its constant still precedes the size and bounded observable. -/
theorem sk_cavity_prod_expansion (β h q : ℝ) (hβ : 4 * β ^ 2 < 1)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q)
    (n k : ℕ) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (x y : Fin k → Fin n), (∀ j, x j ≠ y j) →
    ∀ W : (Fin n → Fin (N + 1) → ℤˣ) → ℝ, (∀ σ, |W σ| ≤ M) →
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) →
        (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let J : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)) - q)
    let f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
      W σ * ∏ j : Fin k, ((N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (σ (x j) i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ (y j) i.castSucc : ℝ)) - q)
    |(∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((k + 1 : ℕ) : ℝ) / 2) ∧
    |(∫ g, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (Esk g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) -
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f (fun r => τ (some (some r))) *
            ((∑ p : Fin n × Fin n with p.1 < p.2,
                J (τ (some (some p.1))) (τ (some (some p.2)))) -
              (n : ℝ) * ∑ r : Fin n, J (τ (some (some r))) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) / 2 * J (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((k + 2 : ℕ) : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := sk_cavity_prod_expansion_uniform β hβ n k M
  exact ⟨C, hC0, hC β h q hfix le_rfl⟩

/-- **Eq. (1.298) evaluated on the old spins.** The old system retains the coefficient
`β / sqrt (N+1)`, exactly as at the decoupled endpoint; there is no change of temperature. -/
theorem sk_cavity_prod_old_spin_compare_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    (n k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (x y : Fin k → Fin n), (∀ j, x j ≠ y j) →
    let F : (Fin n → Fin N → ℤˣ) → ℝ := fun ρ => ∏ j : Fin k,
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ (x j) i : ℝ)) ⬝ᵥ
        fun i : Fin N => (ρ (y j) i : ℝ)) - q)
    |(∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
        F (fun r i => σ r i.castSucc)
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g : FinPairs N → ℝ, ∫ ρ : Fin n → Fin N → ℤˣ, F ρ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin N → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs N, g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((k + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := sk_cavity_prod_expansion_uniform β₀ hβ₀ n k 1
  refine ⟨C, hC0, ?_⟩
  intro β h q hfix hb N x y hxy F
  have ht := (hC β h q hfix hb N x y hxy (fun _ => 1) (fun _ => by norm_num)).1
  have h0 := sk_cavity_decoupled_endpoint_replicas N β q h (∅ : Finset (Fin n)) F
  simp only [one_mul] at ht
  simp only [Finset.prod_empty, mul_one, Finset.card_empty, pow_zero, integral_const,
    probReal_univ, one_smul, one_mul] at h0
  rw [h0] at ht
  exact ht

/-- **The old-spin comparison with fixed model parameters.** Both systems retain
normalization `N+1`; this specializes the uniform estimate. -/
theorem sk_cavity_prod_old_spin_compare (β h q : ℝ) (hβ : 4 * β ^ 2 < 1)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q)
    (n k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (x y : Fin k → Fin n), (∀ j, x j ≠ y j) →
    let F : (Fin n → Fin N → ℤˣ) → ℝ := fun ρ => ∏ j : Fin k,
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ (x j) i : ℝ)) ⬝ᵥ
        fun i : Fin N => (ρ (y j) i : ℝ)) - q)
    |(∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
        F (fun r i => σ r i.castSucc)
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g : FinPairs N → ℝ, ∫ ρ : Fin n → Fin N → ℤˣ, F ρ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin N → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs N, g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((k + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := sk_cavity_prod_old_spin_compare_uniform β hβ n k
  exact ⟨C, hC0, hC β h q hfix le_rfl⟩

end SpinGlasses
