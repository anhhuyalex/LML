/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenFullOverlapBound
public import LeanMachineLearning.SpinGlasses.Talagrand.GaussianFluctuation.SKLastSpinGaussian
public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.Symmetry

/-!
# The reduced cavity system in Hanen's moment proof

The old system has inverse temperature `β √((N+1)/(N+2))`. Its fixed point differs from
that of the full system by at most `1/(N+2)`. Scaling its overlaps back to the full-system
normalization produces the shift handled by Corollary 1.11.7, with one uniform constant.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped Real BigOperators Matrix
namespace SpinGlasses

/-- The cavity fixed-point shift holds for either sign of the inverse temperature. -/
theorem exists_fixedPoint_cavity_of_sq_lt (β h q : ℝ) (hβ4 : 4 * β ^ 2 < 1)
    (hq : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q)
    (N : ℕ) :
    ∃ qm ∈ Set.Icc (0 : ℝ) 1,
      (∫ z : ℝ, Real.tanh
        (β * Real.sqrt ((N : ℝ) / (N + 1)) * Real.sqrt qm * z + h) ^ 2
        ∂gaussianReal 0 1 = qm) ∧ |q - qm| ≤ 1 / ((N : ℝ) + 1) := by
  have hsign (c d : ℝ) :
      (∫ z : ℝ, Real.tanh (|β| * c * d * z + h) ^ 2 ∂gaussianReal 0 1) =
      ∫ z : ℝ, Real.tanh (β * c * d * z + h) ^ 2 ∂gaussianReal 0 1 := by
    have he := integral_gaussianReal_abs_mul 1
      (fun z => Real.tanh (z * c * d + h) ^ 2) β
    convert he using 1 <;> congr 1 <;> funext z <;> congr 1 <;> congr 1 <;> ring
  have hqabs : ∫ z : ℝ, Real.tanh (|β| * Real.sqrt q * z + h) ^ 2
      ∂gaussianReal 0 1 = q := by
    simpa only [mul_one] using (hsign 1 (Real.sqrt q)).trans (by simpa only [mul_one] using hq)
  obtain ⟨qm, hqm, hfix, hshift⟩ := exists_fixedPoint_cavity h q (abs_nonneg β)
    (by simpa only [sq_abs] using hβ4) hqabs (N := N)
  exact ⟨qm, hqm, (hsign _ _).symm.trans hfix, hshift⟩


/-- Talagrand Eq. (1.354): the reduced cavity system retains the spin-difference
product estimate, including the original full-system normalization of its overlaps. -/
theorem sk_hanen_reduced_overlap_bound (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (n s m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (pairMap : Fin s → Fin n × Fin n)
      (_ : ∀ u v : Fin s, u ≠ v →
        (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
        (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
      (x y : Fin m → Fin n) (_ : ∀ j, x j ≠ y j),
      |∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
          (∏ w : Fin s, ((σ (pairMap w).1 (Fin.last N) : ℝ) -
            (σ (pairMap w).2 (Fin.last N) : ℝ))) *
          ∏ j : Fin m, ((N + 2 : ℝ)⁻¹ *
            ((fun i : Fin (N + 1) => (σ (x j) i : ℝ)) ⬝ᵥ
              fun i : Fin (N + 1) => (σ (y j) i : ℝ)) - q)
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (skCavityOldEnergy (N + 1) β h g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      K / ((N : ℝ) + 2) ^ (((((s + 1) / 2 + m : ℕ) : ℝ)) / 2) := by
  let e : ℝ := (((s + 1) / 2 + m : ℕ) : ℝ) / 2
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  obtain ⟨K, hK, hbound⟩ := sk_eta_full_overlap_shift_bound β₀ hβ₀ n s m 2 (by norm_num)
  refine ⟨2 ^ e * K, by positivity, ?_⟩
  intro β h q hfix hβ N pairMap hdisj x y hxy
  let u : ℝ := (N : ℝ) + 1
  let t : ℝ := (N : ℝ) + 2
  have hu : 0 < u := by dsimp [u]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hut : u ≤ t := by dsimp [u,t]; linarith
  let θ := u / t
  have hθ0 : 0 ≤ θ := div_nonneg hu.le ht.le
  have hθ1 : θ ≤ 1 := (div_le_one ht).2 hut
  let βm := β * Real.sqrt θ
  obtain ⟨qm, hqm, hfixm, hshift⟩ := exists_fixedPoint_cavity_of_sq_lt β h q
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hβ (by norm_num)) hβ₀) hfix (N + 1)
  have hfixm' : ∫ z : ℝ, Real.tanh (βm * Real.sqrt qm * z + h) ^ 2
      ∂gaussianReal 0 1 = qm := by
    simpa only [βm, θ, u, t, Nat.cast_succ, add_assoc, one_add_one_eq_two] using hfixm
  have hβm : βm ^ 2 ≤ β₀ ^ 2 := by
    have hsq : βm ^ 2 = β ^ 2 * θ := by dsimp [βm]; rw [mul_pow, Real.sq_sqrt hθ0]
    rw [hsq]
    exact (mul_le_mul_of_nonneg_left hθ1 (sq_nonneg β)).trans (by simpa using hβ)
  let q' := t / u * q
  have hq1 : |q| ≤ 1 := abs_fixedPoint_le_one hfix
  have hqq : |q - q'| ≤ 1 / u := by
    have hd : q - q' = -(q / u) := by
      dsimp [q', t, u]
      field_simp
      ring
    rw [hd, abs_neg, abs_div, abs_of_pos hu]
    exact div_le_div_of_nonneg_right hq1 hu.le
  have hqshift : |qm - q'| ≤ 2 / u := by
    have hs : |qm - q| ≤ 1 / u := by
      have hst : 1 / t ≤ 1 / u := one_div_le_one_div_of_le hu hut
      apply le_trans _ hst
      simpa only [Nat.cast_succ, add_assoc, one_add_one_eq_two, abs_sub_comm, t] using hshift
    exact (abs_sub_le qm q q').trans ((add_le_add hs hqq).trans_eq (by ring))
  have hcoef : (Real.sqrt (N + 1 : ℝ))⁻¹ * βm =
      (Real.sqrt (N + 2 : ℝ))⁻¹ * β := by
    have hc := sk_beta_minus_coefficient (N + 1) β (by omega)
    simpa only [Nat.cast_succ, add_assoc, one_add_one_eq_two, βm, θ, u, t] using hc
  have henergy (g : FinPairs (N + 1) → ℝ) :
      (fun a : Fin (N + 1) → ℤˣ => (Real.sqrt (N + 1))⁻¹ * βm *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ)) = skCavityOldEnergy (N + 1) β h g := by
    funext a
    rw [hcoef]
    simp only [skCavityOldEnergy, Nat.cast_succ, add_assoc, one_add_one_eq_two]
  have key := hbound βm h qm q' hfixm' hβm N pairMap hdisj x y hxy hqshift
  simp_rw [henergy] at key
  let ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun F =>
    ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, F σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (skCavityOldEnergy (N + 1) β h g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  let H : (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
    (∏ w : Fin s, ((σ (pairMap w).1 (Fin.last N) : ℝ) -
      (σ (pairMap w).2 (Fin.last N) : ℝ))) * ∏ j : Fin m, ((N + 1 : ℝ)⁻¹ *
        ((fun i : Fin (N + 1) => (σ (x j) i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ (y j) i : ℝ)) - q')
  change |ν H| ≤ K / u ^ e at key
  have hfun : (fun σ : Fin n → Fin (N + 1) → ℤˣ =>
      (∏ w : Fin s, ((σ (pairMap w).1 (Fin.last N) : ℝ) -
        (σ (pairMap w).2 (Fin.last N) : ℝ))) * ∏ j : Fin m, ((N + 2 : ℝ)⁻¹ *
          ((fun i : Fin (N + 1) => (σ (x j) i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ (y j) i : ℝ)) - q)) =
      fun σ => θ ^ m * H σ := by
    funext σ
    have hd (z : ℝ) : (N + 2 : ℝ)⁻¹ * z - q = θ * ((N + 1 : ℝ)⁻¹ * z - q') := by
      dsimp [θ, q', t, u]
      field_simp
    simp_rw [hd]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, H]
    ring
  have hnorm : |ν (fun σ => θ ^ m * H σ)| = θ ^ m * |ν H| := by
    dsimp only [ν]
    simp_rw [integral_const_mul]
    rw [abs_mul, abs_of_nonneg (pow_nonneg hθ0 _)]
  change |ν _| ≤ _
  rw [hfun, hnorm]
  calc
    _ ≤ |ν H| := mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hθ0 hθ1)
    _ ≤ K / u ^ e := key
    _ ≤ 2 ^ e * K / t ^ e := by
      have hscale : t ^ e ≤ 2 ^ e * u ^ e := by
        rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hu.le]
        apply Real.rpow_le_rpow ht.le _ he0
        dsimp [t, u]
        linarith [Nat.cast_nonneg (α := ℝ) N]
      apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hu _) (Real.rpow_pos_of_pos ht _)).2
      calc K * t ^ e ≤ K * (2 ^ e * u ^ e) := mul_le_mul_of_nonneg_left hscale hK.le
        _ = _ := by ring

end SpinGlasses
