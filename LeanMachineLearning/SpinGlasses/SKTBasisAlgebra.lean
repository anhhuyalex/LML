/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityCovariance
public import LeanMachineLearning.SpinGlasses.GibbsReplicaMarginal
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.SqSub
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.Tanh

/-!
# Algebra of the `T`-basis (Talagrand, Section 1.8, Eqs. (1.245)-(1.265))

The algebra and elementary Gaussian-integral facts behind Propositions 1.8.7-1.8.12:

* `sk_cavity_coincidences_sub_eq`: the difference of two coincidence coefficients of pairs
  `{i₁, k}` and `{i₂, k}` against a pair `{a, b}` (the computation of `c(ℓ, ℓ')` in the proof of
  Lemma 1.8.9);
* `sk_cavity_deriv_zero_sub_third`: Lemma 1.8.9 in sum form over the replica families;
* `sk_cavity_replica_pair_sum_sub_third`: the regrouping of that sum into the book's right-hand
  side, and `sk_cavity_deriv_zero_sub_third_displayed`: Eq. (1.253);
* `sk_at_deriv_coef_split`: the algebra from Eq. (1.253) to Eq. (1.254), and
  `sk_cavity_deriv_zero_sub_third_of_indep`: Eq. (1.254) when `f⁻` does not depend on the third
  replica (the replica `k` is moved to the extra replica by
  `integral_pi_count_tilted_replace_replica`);
* the coefficients of `ν(T²)`, `A²`, `B²` in Eq. (1.264) (`sk_t_coeff_T_sq`, `sk_t_coeff_B_sq`);
* `qhat_le_of_fixedPoint`, `three_quarters_le_one_sub_beta_sq_mul`: `q̂ ≤ q` and
  `1 - β²(1 - 4q + 3q̂) ≥ 3/4`;
* `dotProduct_div_sub_decomp`: the decomposition (1.246),
  `R_{ℓℓ'} - q = T_{ℓℓ'} + T_ℓ + T_ℓ' + T`;
* `one_sub_two_mul_add_qhat_eq`: `1 - 2q + q̂ = 𝔼 ch⁻⁴(β √q z + h)`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 1.8.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real

namespace SpinGlasses

/-- **The coefficient `c(ℓ, ℓ')` of Lemma 1.8.9.**  For distinct `i₁, i₂, k` and a pair `a ≠ b`,
the coefficient `B(coinc(i₁, k; a, b)) - B(coinc(i₂, k; a, b))` is
`(ϑ a + ϑ b)` times `B 2 - B 1` if `k ∈ {a, b}` and `B 1 - B 0` otherwise, where
`ϑ r = 1[r = i₁] - 1[r = i₂]`. -/
theorem sk_cavity_coincidences_sub_eq {R : Type*} [DecidableEq R] (B : ℕ → ℝ)
    {i₁ i₂ k a b : R} (h12 : i₁ ≠ i₂) (h1k : i₁ ≠ k) (h2k : i₂ ≠ k) (hab : a ≠ b) :
    B (skCavityCoincidences i₁ k a b) - B (skCavityCoincidences i₂ k a b) =
      (((if i₁ = a then (1 : ℝ) else 0) + (if i₁ = b then 1 else 0)) -
          ((if i₂ = a then (1 : ℝ) else 0) + (if i₂ = b then 1 else 0))) *
        (if k = a ∨ k = b then B 2 - B 1 else B 1 - B 0) := by
  unfold skCavityCoincidences
  by_cases ha1 : i₁ = a <;> by_cases hb1 : i₁ = b <;> by_cases ha2 : i₂ = a <;>
    by_cases hb2 : i₂ = b <;> by_cases hka : k = a <;> by_cases hkb : k = b <;>
    simp_all [eq_comm]

/-- Every replica is `i₁`, `i₂`, `k` or one of the other replicas. -/
theorem univ_eq_insert_three_filter {n : ℕ} {i₁ i₂ k : Fin n} (h12 : i₁ ≠ i₂) (h1k : i₁ ≠ k)
    (h2k : i₂ ≠ k) :
    (Finset.univ : Finset (Fin n)) =
      insert i₁ (insert i₂ (insert k (Finset.univ.filter fun l => l ≠ i₁ ∧ l ≠ i₂ ∧ l ≠ k))) := by
  ext l
  by_cases a : l = i₁ <;> by_cases b : l = i₂ <;> by_cases c : l = k <;> simp [*]

/-- A sum over `Fin n` splits into the three distinguished replicas and the remaining ones. -/
theorem sum_eq_three_add_sum_filter {n : ℕ} {i₁ i₂ k : Fin n} (h12 : i₁ ≠ i₂) (h1k : i₁ ≠ k)
    (h2k : i₂ ≠ k) (g : Fin n → ℝ) :
    ∑ l, g l = g i₁ + g i₂ + g k + ∑ l ∈ Finset.univ.filter (fun l => l ≠ i₁ ∧ l ≠ i₂ ∧ l ≠ k), g l
      := by
  generalize hs : Finset.univ.filter (fun l => l ≠ i₁ ∧ l ≠ i₂ ∧ l ≠ k) = s
  have hU : (Finset.univ : Finset (Fin n)) = insert i₁ (insert i₂ (insert k s)) := by
    rw [← hs]; exact univ_eq_insert_three_filter h12 h1k h2k
  rw [hU, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert]
  · ring
  all_goals simp [← hs, h12, h1k, h2k, h12.symm, h1k.symm, h2k.symm]


/-- **Regrouping the replica-family sum of Lemma 1.8.9.**  For a symmetric kernel `J`, the sum over
the three families of Eq. (1.152), with the signed coincidence coefficients of
`(ε_{i₁} - ε_{i₂}) ε_k`, is the book's right-hand side of Eq. (1.253): the pair `{i₁, k}` against
`{i₂, k}` with coefficient `b(2) - b(1)`, and the replicas `ℓ ∉ {i₁, i₂, k}` and the extra replica
with coefficient `b(1) - b(0)`. -/
theorem sk_cavity_replica_pair_sum_sub_third {n : ℕ} (b : ℕ → ℝ) {i₁ i₂ k : Fin n}
    (h12 : i₁ ≠ i₂) (h1k : i₁ ≠ k) (h2k : i₂ ≠ k)
    (J : Option (Option (Fin n)) → Option (Option (Fin n)) → ℝ) (hJ : ∀ x y, J x y = J y x) :
    ∑ j : SKCavityReplicaPair n,
      skCavityReplicaPairWeight n j *
        ((((if some (some i₁) = (skCavityReplicaPairMap j).1 then (1 : ℝ) else 0) +
              (if some (some i₁) = (skCavityReplicaPairMap j).2 then 1 else 0)) -
            ((if some (some i₂) = (skCavityReplicaPairMap j).1 then (1 : ℝ) else 0) +
              (if some (some i₂) = (skCavityReplicaPairMap j).2 then 1 else 0))) *
          (if some (some k) = (skCavityReplicaPairMap j).1 ∨
              some (some k) = (skCavityReplicaPairMap j).2 then b 2 - b 1 else b 1 - b 0) *
          J (skCavityReplicaPairMap j).1 (skCavityReplicaPairMap j).2) =
      (b 2 - b 1) * (J (some (some i₁)) (some (some k)) - J (some (some i₂)) (some (some k))) +
        (b 1 - b 0) *
          (∑ l ∈ Finset.univ.filter (fun l => l ≠ i₁ ∧ l ≠ i₂ ∧ l ≠ k),
              (J (some (some i₁)) (some (some l)) - J (some (some i₂)) (some (some l))) -
            (n : ℝ) * (J (some (some i₁)) (some none) - J (some (some i₂)) (some none))) := by
  set D : Option (Option (Fin n)) → Option (Option (Fin n)) → ℝ := fun x y =>
    ((((if some (some i₁) = x then (1 : ℝ) else 0) + (if some (some i₁) = y then 1 else 0)) -
      ((if some (some i₂) = x then (1 : ℝ) else 0) + (if some (some i₂) = y then 1 else 0))) *
      (if some (some k) = x ∨ some (some k) = y then b 2 - b 1 else b 1 - b 0) * J x y) with hD
  set ϑ : Fin n → ℝ := fun a => (if i₁ = a then 1 else 0) - (if i₂ = a then 1 else 0) with hϑ
  set cc : Fin n → Fin n → ℝ := fun a c => if k = a ∨ k = c then b 2 - b 1 else b 1 - b 0
    with hcc
  set X : Fin n → Fin n → ℝ := fun a c => ϑ a * (cc a c * J (some (some a)) (some (some c)))
    with hXdef
  have hsum := sk_cavity_signed_pair_sum D id
  have hX : ∀ a c : Fin n, D (some (some a)) (some (some c)) = X a c + X c a := fun a c => by
    simp only [hD, hXdef, hϑ, hcc, Option.some.injEq, hJ (some (some c)) (some (some a)),
      or_comm (a := k = c) (b := k = a)]
    ring
  have hϑsum : ∀ g : Fin n → ℝ, ∑ r, ϑ r * g r = g i₁ - g i₂ := fun g => by
    simp [hϑ, sub_mul, Finset.sum_sub_distrib]
  have hG : ∀ i : Fin n, i ≠ k → ∑ c, cc i c * J (some (some i)) (some (some c)) =
      (b 1 - b 0) * ∑ c, J (some (some i)) (some (some c)) +
        (b 2 - 2 * b 1 + b 0) * J (some (some i)) (some (some k)) := fun i hik => by
    have : ∀ c, cc i c * J (some (some i)) (some (some c)) =
        (b 1 - b 0) * J (some (some i)) (some (some c)) +
          (b 2 - 2 * b 1 + b 0) * (if c = k then J (some (some i)) (some (some c)) else 0) :=
      fun c => by
        by_cases hc : c = k
        · subst hc; simp [hcc]; ring
        · simp [hcc, hik.symm, Ne.symm hc, hc]
    rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, Finset.sum_ite_eq']
    simp
  have hA : ∑ p : Fin n × Fin n with p.1 < p.2,
      D (id (some (some p.1))) (id (some (some p.2))) = (∑ a, ∑ c, X a c) - ∑ a, X a a := by
    rw [← sum_filter_lt_add_swap X]
    exact Finset.sum_congr rfl fun p _ => hX p.1 p.2
  have hAA : (∑ a, ∑ c, X a c) - ∑ a, X a a =
      (b 2 - b 1) * (J (some (some i₁)) (some (some k)) - J (some (some i₂)) (some (some k))) +
        (b 1 - b 0) * ∑ l ∈ Finset.univ.filter (fun l => l ≠ i₁ ∧ l ≠ i₂ ∧ l ≠ k),
          (J (some (some i₁)) (some (some l)) - J (some (some i₂)) (some (some l))) := by
    have e1 : ∑ a, ∑ c, X a c = ∑ a, ϑ a * ∑ c, cc a c * J (some (some a)) (some (some c)) :=
      Finset.sum_congr rfl fun a _ => by simp only [hXdef, Finset.mul_sum]
    have e2 : ∑ a, X a a = (b 1 - b 0) * (J (some (some i₁)) (some (some i₁)) -
        J (some (some i₂)) (some (some i₂))) := by
      have : ∀ a, X a a = ϑ a * ((b 1 - b 0) * J (some (some a)) (some (some a))) := fun a => by
        by_cases ha : ϑ a = 0
        · simp [hXdef, ha]
        · have : a = i₁ ∨ a = i₂ := by
            by_contra hh
            push Not at hh
            exact ha (by simp [hϑ, Ne.symm hh.1, Ne.symm hh.2])
          rcases this with rfl | rfl
          · simp [hXdef, hcc, Ne.symm h1k]
          · simp [hXdef, hcc, Ne.symm h2k]
      rw [Finset.sum_congr rfl fun a _ => this a, hϑsum (fun a =>
        (b 1 - b 0) * J (some (some a)) (some (some a)))]
      ring
    rw [e1, hϑsum (fun a => ∑ c, cc a c * J (some (some a)) (some (some c))), e2,
      hG i₁ h1k, hG i₂ h2k, sum_eq_three_add_sum_filter h12 h1k h2k (fun c => J _ (some (some c))),
      sum_eq_three_add_sum_filter h12 h1k h2k (fun c => J (some (some i₂)) (some (some c))),
      hJ (some (some i₂)) (some (some i₁))]
    simp only [Finset.sum_sub_distrib]
    ring
  have hB : ∑ r, D (id (some (some r))) (id (some none)) =
      (b 1 - b 0) * (J (some (some i₁)) (some none) - J (some (some i₂)) (some none)) := by
    have : ∀ r, D (id (some (some r))) (id (some none)) = ϑ r *
        ((if k = r then b 2 - b 1 else b 1 - b 0) * J (some (some r)) (some none)) := fun r => by
      simp [hD, hϑ, mul_assoc]
    rw [Finset.sum_congr rfl fun r _ => this r, hϑsum (fun r =>
      (if k = r then b 2 - b 1 else b 1 - b 0) * J (some (some r)) (some none))]
    simp [Ne.symm h1k, Ne.symm h2k]
    ring
  have hC : D (id (some none)) (id none) = 0 := by simp [hD]
  calc _ = ∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
        D (id (skCavityReplicaPairMap j).1) (id (skCavityReplicaPairMap j).2) := rfl
    _ = _ := by
      rw [← hsum, hA, hAA, hB, hC]
      ring


/-- The rectangular signed pair coefficients collapse against every symmetric kernel.
This is the algebra shared by Eqs. (1.237) and (1.301), independent of the Gibbs measure. -/
theorem sk_cavity_replica_pair_sum_rect {n : ℕ} (b : ℕ → ℝ)
    {i₁ i₂ j₁ j₂ : Fin n} (h12 : i₁ ≠ i₂)
    (h13 : i₁ ≠ j₁) (h14 : i₁ ≠ j₂) (h23 : i₂ ≠ j₁) (h24 : i₂ ≠ j₂)
    (J : Option (Option (Fin n)) → Option (Option (Fin n)) → ℝ)
    (hJ : ∀ x y, J x y = J y x) :
    ∑ p : SKCavityReplicaPair n, skCavityReplicaPairWeight n p *
      ((b (skCavityReplicaPairCoincidences i₁ j₁ p) -
          b (skCavityReplicaPairCoincidences i₂ j₁ p) -
          (b (skCavityReplicaPairCoincidences i₁ j₂ p) -
            b (skCavityReplicaPairCoincidences i₂ j₂ p))) *
        J (skCavityReplicaPairMap p).1 (skCavityReplicaPairMap p).2) =
      (b 2 - 2 * b 1 + b 0) *
        (J (some (some i₁)) (some (some j₁)) - J (some (some i₂)) (some (some j₁)) -
          (J (some (some i₁)) (some (some j₂)) - J (some (some i₂)) (some (some j₂)))) := by
  let D : Fin n → ℝ := fun l =>
    J (some (some i₁)) (some (some l)) - J (some (some i₂)) (some (some l))
  have hs (k : Fin n) (h1k : i₁ ≠ k) (h2k : i₂ ≠ k) :
      (∑ p : SKCavityReplicaPair n, skCavityReplicaPairWeight n p *
        ((b (skCavityReplicaPairCoincidences i₁ k p) -
          b (skCavityReplicaPairCoincidences i₂ k p)) *
          J (skCavityReplicaPairMap p).1 (skCavityReplicaPairMap p).2)) =
      (b 2 - b 1) * D k + (b 1 - b 0) *
        ((∑ l ∈ Finset.univ.filter (fun l => l ≠ i₁ ∧ l ≠ i₂ ∧ l ≠ k), D l) -
          (n : ℝ) * (J (some (some i₁)) (some none) - J (some (some i₂)) (some none))) := by
    refine Eq.trans ?_ (sk_cavity_replica_pair_sum_sub_third b h12 h1k h2k J hJ)
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [skCavityReplicaPairCoincidences]
    rw [sk_cavity_coincidences_sub_eq b
      (i₁ := some (some i₁)) (i₂ := some (some i₂)) (k := some (some k))
      (by simpa only [ne_eq, Option.some.injEq] using h12)
      (by simpa only [ne_eq, Option.some.injEq] using h1k)
      (by simpa only [ne_eq, Option.some.injEq] using h2k)
      (skCavityReplicaPair_ne p)]
  have he : (∑ l ∈ Finset.univ.filter (fun l => l ≠ i₁ ∧ l ≠ i₂ ∧ l ≠ j₁), D l) -
      (∑ l ∈ Finset.univ.filter (fun l => l ≠ i₁ ∧ l ≠ i₂ ∧ l ≠ j₂), D l) = D j₂ - D j₁ := by
    linarith [sum_eq_three_add_sum_filter h12 h13 h23 D,
      sum_eq_three_add_sum_filter h12 h14 h24 D]
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib] at hs ⊢
  have h1 := hs j₁ h13 h23
  have h2 := hs j₂ h14 h24
  dsimp only [D] at h1 h2 he
  linear_combination h1 - h2 + (b 1 - b 0) * he

/-- **From Eq. (1.253) to Eq. (1.254).**  If the observable does not depend on the third replica,
the term of replica `3` equals the term of replica `n + 1`, and the book's coefficients
`b(2) - b(1)` and `b(1) - b(0)` regroup into `b(2) - 4 b(1) + 3 b(0)` and `b(1) - b(0)`.
Here `s` is the index set `{4, ..., n}`, so `|s| + 3 = n`. -/
theorem sk_at_deriv_coef_split {ι : Type*} (s : Finset ι) (n : ℕ) (hn : s.card + 3 = n)
    (b2 b1 b0 S3 Sn : ℝ) (S : ι → ℝ) (h : S3 = Sn) :
    (b2 - b1) * S3 + (b1 - b0) * (∑ l ∈ s, S l - (n : ℝ) * Sn) =
      (b2 - 4 * b1 + 3 * b0) * S3 + (b1 - b0) * ∑ l ∈ s, (S l - Sn) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← hn]
  subst h
  push_cast
  ring

/-- **Coefficient of `ν(T²)` in Eq. (1.264).**  Over the pairs `1 ≤ ℓ < ℓ' ≤ 4` with respect to
`(x, y) = (1, 2)` the coefficients are `b(2)` (for `(1,2)`), `b(1)` four times, `b(0)` (for
`(3,4)`); over `(ℓ, 5)` they are `b(1)` twice and `b(0)` twice; and `(5, 6)` gives `b(0)`. -/
theorem sk_t_coeff_T_sq (β q qhat : ℝ) :
    (skCavityBCoef β q qhat 2 + 4 * skCavityBCoef β q qhat 1 + skCavityBCoef β q qhat 0) -
        4 * (2 * skCavityBCoef β q qhat 1 + 2 * skCavityBCoef β q qhat 0) +
        10 * skCavityBCoef β q qhat 0 = β ^ 2 * (1 - 4 * q + 3 * qhat) := by
  dsimp [skCavityBCoef, skCavityBUnscaled]
  ring

/-- **Coefficient of `B²` in Eq. (1.264):** the four pairs `(ℓ, ℓ')` with `ℓ ∈ {1,2}`,
`ℓ' ∈ {3,4}` carry `b(1)`, the pair `(3,4)` carries `2 b(0)`, and `(3,5)`, `(4,5)` carry
`-4 b(0)` each. -/
theorem sk_t_coeff_B_sq (β q qhat : ℝ) :
    4 * skCavityBCoef β q qhat 1 + 2 * skCavityBCoef β q qhat 0 -
        4 * (skCavityBCoef β q qhat 0 + skCavityBCoef β q qhat 0) =
      2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qhat) := by
  dsimp [skCavityBCoef, skCavityBUnscaled]
  ring

/-- For the fixed point `q` and `q̂ = 𝔼 tanh⁴ Y`, one has `q̂ ≤ q`. -/
theorem qhat_le_of_fixedPoint (β q h qhat : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat) :
    qhat ≤ q := by
  calc qhat = ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) := hqhat.symm
    _ ≤ ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) :=
        integral_tanh_pow_four_le_sq (μ := gaussianReal 0 1)
          (fun z : ℝ => β * Real.sqrt q * z + h) (by fun_prop)
    _ = q := hfix

/-- At a fixed point, `0 ≤ q - q̂ ≤ 1` for `q̂ = 𝔼 tanh⁴ (β z √q + h)`; this is the coefficient
size of the single-factor contraction. -/
theorem abs_sub_integral_tanh_fourth_le_one_of_fixedPoint {β q h : ℝ}
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q) :
    |q - ∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 4 ∂(gaussianReal 0 1)| ≤ 1 := by
  have h1 := fixedPoint_mem_Icc hfix
  have h2 := qhat_le_of_fixedPoint β q h _ hfix rfl
  have h3 : 0 ≤ ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) :=
    integral_nonneg fun t => by positivity
  rw [integral_tanh_pow_mul_z_sqrt_eq]
  exact abs_le.mpr ⟨by linarith [h1.1, h1.2], by linarith [h1.1, h1.2]⟩

/-- At a fixed point, `|1 - 4 q + 3 q̂| ≤ 3`. -/
theorem abs_one_sub_four_mul_add_three_mul_le {β q h : ℝ}
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q) :
    |1 - 4 * q + 3 * ∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 4 ∂(gaussianReal 0 1)| ≤ 3 := by
  have h1 := fixedPoint_mem_Icc hfix
  have h2 := qhat_le_of_fixedPoint β q h _ hfix rfl
  have h3 : 0 ≤ ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) :=
    integral_nonneg fun t => by positivity
  rw [integral_tanh_pow_mul_z_sqrt_eq]
  exact abs_le.mpr ⟨by linarith [h1.1, h1.2], by linarith [h1.1, h1.2]⟩

/-- **The denominator of Propositions 1.8.10 and 1.8.11.**  For `4 β² < 1`, `0 ≤ q` and
`q̂ ≤ q`: `1 - β² (1 - 4 q + 3 q̂) ≥ 3/4`. -/
theorem three_quarters_le_one_sub_beta_sq_mul {β q qhat : ℝ} (hβ : 4 * β ^ 2 < 1) (hq : 0 ≤ q)
    (hqhat : qhat ≤ q) : 3 / 4 ≤ 1 - β ^ 2 * (1 - 4 * q + 3 * qhat) := by
  have h1 : 1 - 4 * q + 3 * qhat ≤ 1 := by linarith
  have h2 : β ^ 2 * (1 - 4 * q + 3 * qhat) ≤ β ^ 2 * 1 :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg β)
  linarith

/-- **The decomposition (1.246).**  For vectors `x, y, b` and the centered parts
`T_{xy} = (x - b)·(y - b)/N`, `T_x = (x - b)·b/N`, `T = b·b/N - q`:
`x·y/N - q = T_{xy} + T_x + T_y + T`. -/
theorem dotProduct_div_sub_decomp {ι : Type*} [Fintype ι] (N q : ℝ) (x y b : ι → ℝ) :
    x ⬝ᵥ y / N - q = (x - b) ⬝ᵥ (y - b) / N + (x - b) ⬝ᵥ b / N + (y - b) ⬝ᵥ b / N +
      (b ⬝ᵥ b / N - q) := by
  have : x ⬝ᵥ y = (x - b) ⬝ᵥ (y - b) + (x - b) ⬝ᵥ b + (y - b) ⬝ᵥ b + b ⬝ᵥ b := by
    simp only [sub_dotProduct, dotProduct_sub]
    rw [dotProduct_comm b y]
    ring
  rw [this]
  ring

/-- **Talagrand, Lemma 1.8.9, first form (Eq. 1.253), as a sum over the replica families.**
For distinct replicas `i₁, i₂, k` of `n` replicas and a function `F` of the old coordinates, the
cavity derivative at the decoupled endpoint of `F (ε_{i₁} - ε_{i₂}) ε_k` is the weighted sum over
the families `j = (a, b)` of Eq. (1.152) of
`(ϑ a + ϑ b) · (if k ∈ {a, b} then b(2) - b(1) else b(1) - b(0)) · ν₀(F (R⁻_{ab} - q))`,
where `ϑ r = 1[r = i₁] - 1[r = i₂]`.  It is the difference of two applications of Lemma 1.8.2
(`sk_cavity_deriv_zero_pair_combo` with the coefficients `1, -1`), so the `-q` cancels. -/
theorem sk_cavity_deriv_zero_sub_third (N n : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (qhat : ℝ)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    {i₁ i₂ k : Fin n} (h12 : i₁ ≠ i₂) (h1k : i₁ ≠ k) (h2k : i₂ ≠ k)
    (F : (Fin n → Fin N → ℤˣ) → ℝ) :
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
    let so : Fin n → Option (Option (Fin n)) := fun r => some (some r)
    let f : (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ := fun τ =>
      F (fun r i => τ (so r) i.castSucc) *
        ((((τ (so i₁) (Fin.last N) : ℤˣ) : ℝ) - ((τ (so i₂) (Fin.last N) : ℤˣ) : ℝ)) *
          ((τ (so k) (Fin.last N) : ℤˣ) : ℝ))
    let K : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)) - q)
    (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f τ *
            ((∑ p : Fin n × Fin n with p.1 < p.2,
                K (τ (so p.1)) (τ (so p.2))) -
              (n : ℝ) * ∑ r : Fin n, K (τ (so r)) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
      ∑ j : SKCavityReplicaPair n,
        skCavityReplicaPairWeight n j *
          ((((if so i₁ = (skCavityReplicaPairMap j).1 then (1 : ℝ) else 0) +
                (if so i₁ = (skCavityReplicaPairMap j).2 then 1 else 0)) -
              ((if so i₂ = (skCavityReplicaPairMap j).1 then (1 : ℝ) else 0) +
                (if so i₂ = (skCavityReplicaPairMap j).2 then 1 else 0))) *
            (if so k = (skCavityReplicaPairMap j).1 ∨ so k = (skCavityReplicaPairMap j).2 then
                skCavityBCoef β q qhat 2 - skCavityBCoef β q qhat 1
              else skCavityBCoef β q qhat 1 - skCavityBCoef β q qhat 0) *
            ∫ g', ∫ ρ : Option (Option (Fin n)) → Fin N → ℤˣ,
              F (fun r => ρ (so r)) *
                ((N + 1 : ℝ)⁻¹ *
                  ((fun i : Fin N => (ρ (skCavityReplicaPairMap j).1 i : ℝ)) ⬝ᵥ
                    fun i : Fin N => (ρ (skCavityReplicaPairMap j).2 i : ℝ)) - q)
              ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
                (fun r : Fin N → ℤˣ =>
                  (Real.sqrt (N + 1))⁻¹ * β *
                    (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
                  h * ∑ i : Fin N, (r i : ℝ)))
              ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) := by
  intro B E so f K
  have hx : ∀ m : Bool, (if m then i₁ else i₂) ≠ k := fun m => by
    cases m
    exacts [h2k, h1k]
  have h1 := sk_cavity_deriv_zero_pair_combo N n β q h hfix qhat hqhat (ι := Bool)
    (fun m => if m then 1 else -1) (x := fun m => if m then i₁ else i₂) (y := fun _ => k)
    (fun m => (hx m)) F
  simp only [Fintype.sum_bool, ite_true, ite_false, Bool.false_eq_true] at h1
  have hpt : ∀ u v w : ℝ, 1 * (u * w - q) + -1 * (v * w - q) = (u - v) * w := fun u v w => by
    ring
  simp only [hpt] at h1
  refine h1.trans (Finset.sum_congr rfl fun j _ => ?_)
  have hso : ∀ r r' : Fin n, r ≠ r' → so r ≠ so r' := fun r r' hr he =>
    hr (Option.some.inj (Option.some.inj he))
  have hc := sk_cavity_coincidences_sub_eq (skCavityBCoef β q qhat) (hso _ _ h12)
    (hso _ _ h1k) (hso _ _ h2k) (skCavityReplicaPair_ne j)
  have e : ∀ u v : ℝ, 1 * u + -1 * v = u - v := fun u v => by ring
  simp only [e, skCavityReplicaPairCoincidences, so] at hc ⊢
  rw [hc, mul_assoc]

/-- **A pair of replicas outside `i₁, i₂, k` leaves `k`.**  The replicas other than `i₁, i₂, k`
number `n - 3`. -/
theorem card_filter_ne_three {n : ℕ} {i₁ i₂ k : Fin n} (h12 : i₁ ≠ i₂) (h1k : i₁ ≠ k)
    (h2k : i₂ ≠ k) :
    (Finset.univ.filter fun l => l ≠ i₁ ∧ l ≠ i₂ ∧ l ≠ k).card + 3 = n := by
  have := sum_eq_three_add_sum_filter h12 h1k h2k fun _ => (1 : ℝ)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at this
  exact_mod_cast (by linarith : ((Finset.univ.filter fun l => l ≠ i₁ ∧ l ≠ i₂ ∧ l ≠ k).card : ℝ) +
    3 = n)

/-- **Talagrand, Lemma 1.8.9, Eq. (1.253).**  For distinct replicas `i₁, i₂, k` of `n` replicas
(the book's `1, 2, 3`) and a function `F` of the old coordinates, the cavity derivative at the
decoupled endpoint of `F (ε_{i₁} - ε_{i₂}) ε_k` is
`(b(2) - b(1)) ν₀(F (R⁻_{i₁ k} - R⁻_{i₂ k}))` plus `b(1) - b(0)` times the sum over the replicas
`ℓ ∉ {i₁, i₂, k}` (the book's `4 ≤ ℓ ≤ n`) of `ν₀(F (R⁻_{i₁ ℓ} - R⁻_{i₂ ℓ}))`, minus `n` times
`ν₀(F (R⁻_{i₁ n+1} - R⁻_{i₂ n+1}))`.  Here `J x y` is the decoupled average
`ν₀(F (R⁻_{x y} - q))` of Lemma 1.8.2 (given by `hJ`), and the `q` cancels in each difference. -/
theorem sk_cavity_deriv_zero_sub_third_displayed (N n : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (qhat : ℝ)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    {i₁ i₂ k : Fin n} (h12 : i₁ ≠ i₂) (h1k : i₁ ≠ k) (h2k : i₂ ≠ k)
    (F : (Fin n → Fin N → ℤˣ) → ℝ)
    (J : Option (Option (Fin n)) → Option (Option (Fin n)) → ℝ)
    (hJ : ∀ x y, J x y =
      ∫ g', ∫ ρ : Option (Option (Fin n)) → Fin N → ℤˣ,
        F (fun r => ρ (some (some r))) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ x i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ y i : ℝ)) - q)
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) :
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
    let so : Fin n → Option (Option (Fin n)) := fun r => some (some r)
    let f : (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ := fun τ =>
      F (fun r i => τ (so r) i.castSucc) *
        ((((τ (so i₁) (Fin.last N) : ℤˣ) : ℝ) - ((τ (so i₂) (Fin.last N) : ℤˣ) : ℝ)) *
          ((τ (so k) (Fin.last N) : ℤˣ) : ℝ))
    let K : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)) - q)
    (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f τ *
            ((∑ p : Fin n × Fin n with p.1 < p.2,
                K (τ (so p.1)) (τ (so p.2))) -
              (n : ℝ) * ∑ r : Fin n, K (τ (so r)) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
      (skCavityBCoef β q qhat 2 - skCavityBCoef β q qhat 1) *
          (J (some (some i₁)) (some (some k)) - J (some (some i₂)) (some (some k))) +
        (skCavityBCoef β q qhat 1 - skCavityBCoef β q qhat 0) *
          (∑ l ∈ Finset.univ.filter (fun l => l ≠ i₁ ∧ l ≠ i₂ ∧ l ≠ k),
              (J (some (some i₁)) (some (some l)) - J (some (some i₂)) (some (some l))) -
            (n : ℝ) * (J (some (some i₁)) (some none) - J (some (some i₂)) (some none))) := by
  intro B E so f K
  have hsymm : ∀ x y, J x y = J y x := fun x y => by
    rw [hJ, hJ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g' => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
    beta_reduce
    rw [dotProduct_comm]
  refine (sk_cavity_deriv_zero_sub_third N n β q h hfix qhat hqhat h12 h1k h2k F).trans ?_
  rw [← sk_cavity_replica_pair_sum_sub_third (skCavityBCoef β q qhat) h12 h1k h2k J hsymm]
  exact Finset.sum_congr rfl fun j _ => by rw [hJ]

/-- **Talagrand, Lemma 1.8.9, Eq. (1.254).**  If `F` does not depend on the replica `k` (the
book's third replica), the replica `k` and the extra replica `n + 1` give the same average, and
Eq. (1.253) regroups into `(b(2) - 4 b(1) + 3 b(0)) ν₀(F (R⁻_{i₁ k} - R⁻_{i₂ k}))` plus
`(b(1) - b(0))` times the sum over `ℓ ∉ {i₁, i₂, k}` of
`ν₀(F (R⁻_{i₁ ℓ} - R⁻_{i₂ ℓ} - R⁻_{i₁ n+1} + R⁻_{i₂ n+1}))`, which in terms of `β, q, q̂` is
`β²(1 - 4q + 3q̂)` and `β²(q - q̂)`.  The hypotheses on `J` are those of
`sk_cavity_deriv_zero_sub_third_displayed`, with `hF` stating that `F` is unchanged when the
`k`-th replica is replaced; the fixed-point equations are not needed for this regrouping. -/
theorem sk_cavity_deriv_zero_sub_third_of_indep (N n : ℕ) (β q h : ℝ)
    (qhat : ℝ)
    {i₁ i₂ k : Fin n} (h12 : i₁ ≠ i₂) (h1k : i₁ ≠ k) (h2k : i₂ ≠ k)
    (F : (Fin n → Fin N → ℤˣ) → ℝ)
    (hF : ∀ (ρ : Fin n → Fin N → ℤˣ) x, F (Function.update ρ k x) = F ρ)
    (J : Option (Option (Fin n)) → Option (Option (Fin n)) → ℝ)
    (hJ : ∀ x y, J x y =
      ∫ g', ∫ ρ : Option (Option (Fin n)) → Fin N → ℤˣ,
        F (fun r => ρ (some (some r))) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ x i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ y i : ℝ)) - q)
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) :
    (skCavityBCoef β q qhat 2 - skCavityBCoef β q qhat 1) *
          (J (some (some i₁)) (some (some k)) - J (some (some i₂)) (some (some k))) +
        (skCavityBCoef β q qhat 1 - skCavityBCoef β q qhat 0) *
          (∑ l ∈ Finset.univ.filter (fun l => l ≠ i₁ ∧ l ≠ i₂ ∧ l ≠ k),
              (J (some (some i₁)) (some (some l)) - J (some (some i₂)) (some (some l))) -
            (n : ℝ) * (J (some (some i₁)) (some none) - J (some (some i₂)) (some none))) =
      β ^ 2 * (1 - 4 * q + 3 * qhat) *
          (J (some (some i₁)) (some (some k)) - J (some (some i₂)) (some (some k))) +
        β ^ 2 * (q - qhat) *
          ∑ l ∈ Finset.univ.filter (fun l => l ≠ i₁ ∧ l ≠ i₂ ∧ l ≠ k),
            (J (some (some i₁)) (some (some l)) - J (some (some i₂)) (some (some l)) -
              (J (some (some i₁)) (some none) - J (some (some i₂)) (some none))) := by
  have hswap : ∀ i, i ≠ k → J (some (some i)) (some (some k)) = J (some (some i)) (some none) :=
    fun i hik => by
    rw [hJ, hJ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g' => ?_)
    exact integral_pi_count_tilted_replace_replica (e := fun r : Fin n => some (some r))
      (fun r r' hr => Option.some.inj (Option.some.inj hr)) (x₀ := some none)
      (fun r => by simp) hik _ F hF
      (fun x y => (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (x i : ℝ)) ⬝ᵥ fun i : Fin N => (y i : ℝ)) - q)
  rw [sk_at_deriv_coef_split _ n (card_filter_ne_three h12 h1k h2k) _ _ _
    (J (some (some i₁)) (some (some k)) - J (some (some i₂)) (some (some k)))
    (J (some (some i₁)) (some none) - J (some (some i₂)) (some none))
    (fun l => J (some (some i₁)) (some (some l)) - J (some (some i₂)) (some (some l)))
    (by rw [hswap i₁ h1k, hswap i₂ h2k])]
  have e1 := sk_at_eigenvalue_two_eq β q qhat
  have e2 : skCavityBCoef β q qhat 1 - skCavityBCoef β q qhat 0 = β ^ 2 * (q - qhat) := by
    dsimp [skCavityBCoef, skCavityBUnscaled]
    ring
  rw [e1, e2]

/-- `1 - 2q + q̂ = 𝔼 ch⁻⁴(β √q z + h)` for the fixed point `q` and `q̂ = 𝔼 tanh⁴`. -/
theorem one_sub_two_mul_add_qhat_eq (β q h qhat : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat) :
    1 - 2 * q + qhat =
      ∫ z : ℝ, ((Real.cosh (β * Real.sqrt q * z + h))⁻¹) ^ 4 ∂(gaussianReal 0 1) := by
  have := integral_tanh_pow_four_sub_two_mul_add_eq (μ := gaussianReal 0 1)
    (fun z : ℝ => β * Real.sqrt q * z + h) (by fun_prop)
  rw [hfix, hqhat] at this
  simp only [probReal_univ] at this
  linarith

end SpinGlasses
