/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenReducedSystem

/-!
# Bounds for the endpoint derivatives in Hanen's moment proof

The exact iterated-kernel expansion and decoupled factorization reduce every term to
an old-system overlap product. The reduced-system bound then supplies the extra decay
coming from the spin differences at the second site (Talagrand Eq. (1.352)).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix
namespace SpinGlasses

/-- Talagrand Eq. (1.352): the `m`-th endpoint derivative of the two-site product
of `s` disjoint spin differences is of order `(N+2)^(-(ceil(s/2)+m)/2)`. -/
theorem sk_hanen_endpoint_derivative_bound (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (n s m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (pairMap : Fin s → Fin n × Fin n)
      (_ : ∀ u v : Fin s, u ≠ v →
        (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
        (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2),
      |iteratedDerivWithin m (fun t => skCavityPathMean (N + 1) n β q h t
        (fun σ => (∏ w : Fin s,
          ((σ (pairMap w).1 (Fin.last N).castSucc : ℝ) -
            (σ (pairMap w).2 (Fin.last N).castSucc : ℝ))) *
          ∏ w : Fin s, ((σ (pairMap w).1 (Fin.last (N + 1)) : ℝ) -
            (σ (pairMap w).2 (Fin.last (N + 1)) : ℝ)))) (Set.Icc 0 1) 0| ≤
        K / ((N : ℝ) + 2) ^ (((((s + 1) / 2 + m : ℕ) : ℝ)) / 2) := by
  obtain ⟨T, hT, w, ι, a, b, hι, hab, hw, hiter⟩ := skCavityIterKernel_structure m n
  let n' := skCavityIterReplicaCount m n
  obtain ⟨C, hC, hbound⟩ := sk_hanen_reduced_overlap_bound β₀ hβ₀ n' s m
  let K := (β₀ ^ 2) ^ m * 2 ^ s * C * skCavityIterWeightBound m n
  refine ⟨K + 1, ?_, ?_⟩
  · have hK : 0 ≤ K := mul_nonneg (by positivity) (skCavityIterWeightBound_nonneg m n)
    linarith
  intro β h q hfix hβ N pairMap hdisj
  have hq := fixedPoint_mem_Icc hfix
  let pm : Fin s → Fin n' × Fin n' := fun v => (ι (pairMap v).1, ι (pairMap v).2)
  have hdisj' : ∀ u v : Fin s, u ≠ v →
      (pm u).1 ≠ (pm v).1 ∧ (pm u).1 ≠ (pm v).2 ∧
      (pm u).2 ≠ (pm v).1 ∧ (pm u).2 ≠ (pm v).2 := by
    intro u v huv
    obtain ⟨h1, h2, h3, h4⟩ := hdisj u v huv
    exact ⟨hι.ne h1, hι.ne h2, hι.ne h3, hι.ne h4⟩
  let F : T → (Fin n' → Fin (N + 1) → ℤˣ) → ℝ := fun t ρ =>
    (∏ v : Fin s, ((ρ (pm v).1 (Fin.last N) : ℝ) -
      (ρ (pm v).2 (Fin.last N) : ℝ))) *
    ∏ r : Fin m, ((N + 2 : ℝ)⁻¹ *
      ((fun i : Fin (N + 1) => (ρ (a t r) i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (ρ (b t r) i : ℝ)) - q)
  let G : T → (Fin n' → ℤˣ) → ℝ := fun t ε =>
    (∏ v : Fin s, ((ε (pm v).1 : ℝ) - (ε (pm v).2 : ℝ))) *
      ∏ r : Fin m, (ε (a t r) : ℝ) * (ε (b t r) : ℝ)
  have hG (t : T) (ε : Fin n' → ℤˣ) : |G t ε| ≤ 2 ^ s := by
    have hε : |∏ r : Fin m, (ε (a t r) : ℝ) * (ε (b t r) : ℝ)| = 1 := by
      rw [Finset.abs_prod]
      simp [abs_mul, abs_units_cast_eq_one]
    dsimp only [G]
    rw [abs_mul, hε, mul_one]
    simpa using abs_prod_units_sub_le_two_pow (fun v : Fin s => ε (pm v).1)
      (fun v : Fin s => ε (pm v).2)
  have hspin (t : T) : |∫ z : ℝ, ∫ ε : Fin n' → ℤˣ, G t ε
      ∂(Measure.pi fun _ : Fin n' => Measure.count.tilted
        fun r : ℤˣ => (r : ℝ) * (β * z * Real.sqrt q + h)) ∂gaussianReal 0 1| ≤ 2 ^ s := by
    have hinner (z : ℝ) : |∫ ε : Fin n' → ℤˣ, G t ε
        ∂(Measure.pi fun _ : Fin n' => Measure.count.tilted
          fun r : ℤˣ => (r : ℝ) * (β * z * Real.sqrt q + h))| ≤ 2 ^ s := by
      have he := norm_integral_le_of_norm_le_const
        (μ := Measure.pi fun _ : Fin n' => Measure.count.tilted
          fun r : ℤˣ => (r : ℝ) * (β * z * Real.sqrt q + h))
        (f := G t) (C := (2 : ℝ) ^ s)
        (Filter.Eventually.of_forall fun ε => by simpa only [Real.norm_eq_abs] using hG t ε)
      simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using he
    have he := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1)
      (f := fun z : ℝ => ∫ ε : Fin n' → ℤˣ, G t ε
        ∂(Measure.pi fun _ : Fin n' => Measure.count.tilted
          fun r : ℤˣ => (r : ℝ) * (β * z * Real.sqrt q + h))) (C := (2 : ℝ) ^ s)
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hinner z)
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using he
  have hprod (t : T) :
      |skCavityPathMean (N + 1) n' β q h 0 (fun σ =>
        F t (fun r i => σ r i.castSucc) * G t (fun r => σ r (Fin.last (N + 1))))| ≤
        (2 ^ s * C) / ((N : ℝ) + 2) ^ (((((s + 1) / 2 + m : ℕ) : ℝ)) / 2) := by
    rw [skCavityPathMean_zero_mul, abs_mul]
    have hF := hbound β h q hfix hβ N pm hdisj' (a t) (b t) (hab t)
    calc _ ≤ 2 ^ s * (C / ((N : ℝ) + 2) ^ (((((s + 1) / 2 + m : ℕ) : ℝ)) / 2)) :=
          mul_le_mul (hspin t) hF (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hfun : skCavityIterKernel (N + 1) β q m n (fun σ =>
        (∏ v : Fin s, ((σ (pairMap v).1 (Fin.last N).castSucc : ℝ) -
          (σ (pairMap v).2 (Fin.last N).castSucc : ℝ))) *
        ∏ v : Fin s, ((σ (pairMap v).1 (Fin.last (N + 1)) : ℝ) -
          (σ (pairMap v).2 (Fin.last (N + 1)) : ℝ))) =
      fun σ => ∑ t : T, (w t * (β ^ 2) ^ m) *
        (F t (fun r i => σ r i.castSucc) * G t (fun r => σ r (Fin.last (N + 1)))) := by
    funext σ
    rw [hiter (N + 1) β q _ σ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    dsimp only [F, G, pm, skCavityPathKernel]
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Nat.cast_succ, add_assoc, one_add_one_eq_two]
    ring
  rw [iteratedDerivWithin_skCavityPathMean (N + 1) m β q h hq n _ 0 ⟨le_rfl, zero_le_one⟩,
    hfun, skCavityPathMean_finset_sum]
  have hβpow : (β ^ 2) ^ m ≤ (β₀ ^ 2) ^ m := pow_le_pow_left₀ (sq_nonneg _) hβ m
  calc
    _ ≤ ∑ t : T, |w t * (β ^ 2) ^ m * skCavityPathMean (N + 1) n' β q h 0
        (fun σ => F t (fun r i => σ r i.castSucc) * G t (fun r => σ r (Fin.last (N + 1))))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t : T, |w t| * ((β₀ ^ 2) ^ m *
        ((2 ^ s * C) / ((N : ℝ) + 2) ^ (((((s + 1) / 2 + m : ℕ) : ℝ)) / 2))) := by
      refine Finset.sum_le_sum fun t _ => ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (β ^ 2) ^ m), mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact mul_le_mul hβpow (hprod t) (abs_nonneg _) (by positivity)
    _ = K / ((N : ℝ) + 2) ^ (((((s + 1) / 2 + m : ℕ) : ℝ)) / 2) := by
      rw [← Finset.sum_mul, hw]
      dsimp only [K]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)

end SpinGlasses
