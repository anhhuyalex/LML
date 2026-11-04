/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTGlobalIntegrate
public import LeanMachineLearning.SpinGlasses.SKOverlapCLTSingleFinal

/-!
# The mixed moments needed in the global stage of Theorem 1.10.1

After the exact integration of the replicas not touched by the leading overlap (see
`SKOverlapCLTGlobalIntegrate.lean`), three kinds of moments of the variables
`T = N⁻¹ ∑ b² - q`, `T_x = N⁻¹ ∑ (σ^x - b) b`, `T_{x,y} = N⁻¹ ∑ (σ^x - b)(σ^y - b)` remain. Writing
`ν_j = 𝔼 T^j`, this file proves with Propositions 1.10.4 and 1.10.5

* `𝔼 T_x² T^j = B²/(N+1) ν_j + O(j+3)`,
* `𝔼 T_{xy}² T^j = A²/(N+1) ν_j + O(j+3)`,
* `𝔼 T_{xy} T_x T_y T^j = O(j+4)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real

namespace SpinGlasses

/-- **`𝔼 T_x² T^j` (Proposition 1.10.5 for two equal singles and `j` globals).** -/
theorem sk_T_single_square_moment_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R : Type*} [Fintype R] (x : R) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tg : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
      ((N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i) - q
    let A : (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ := fun g ρ =>
      (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * bmean g i
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    |(∫ g, Tg g ^ j * ∫ ρ : R → Fin (N + 1) → ℤˣ, A g ρ ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      ((q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) /
        (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) / (N + 1 : ℝ)) *
      ∫ g, Tg g ^ j ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      C / ((N : ℝ) + 1) ^ (((j + 3 : ℕ) : ℝ) / 2) := by
  classical
  obtain ⟨C, hC0, hC⟩ := sk_T_single_gaussian_moment_uniform β₀ hβ₀ (R := R) (J := Fin (j + 2))
    (fun i => decide (i.val < 2)) (fun _ => false) (fun _ => rfl) (fun _ => x) (fun _ => x)
    Finset.univ
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro E bmean Tg A qh α
  have h1 := hC β h q hfix hb N
  obtain ⟨-, -, hX0, -⟩ := single_coeff_facts β₀ hβ₀ β h q hfix hb
  let Tf : Fin (j + 2) → (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ :=
    fun i g ρ => ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
        (if decide (i.val < 2) = true then (ρ x v : ℝ) - bmean g v else bmean g v) *
        (if (false : Bool) = true then (ρ x v : ℝ) - bmean g v else bmean g v)) -
          (if (decide (i.val < 2) || false) = true then 0 else q)
  have hT : ∀ (i : Fin (j + 2)) (g : FinPairs (N + 1) → ℝ) (ρ : R → Fin (N + 1) → ℤˣ),
      Tf i g ρ = if i.val < 2 then A g ρ else Tg g := fun i g ρ => by
    by_cases hi : i.val < 2
    · have hi' : (i : ℕ) ≤ 1 := by omega
      simp [Tf, hi, hi', A, Tg]
    · have hi' : ¬ (i : ℕ) ≤ 1 := by omega
      simp [Tf, hi, hi', A, Tg]
  have hprod : ∀ (g : FinPairs (N + 1) → ℝ) (ρ : R → Fin (N + 1) → ℤˣ),
      (∏ i : Fin (j + 2), Tf i g ρ) = A g ρ ^ 2 * Tg g ^ j := fun g ρ => by
    simp only [hT]
    simp [Fin.prod_univ_succ, pow_succ]
    ring
  have hcard : (Finset.univ.filter fun i : Fin (j + 2) =>
        ¬(decide (i.val < 2) = true ∧ (false : Bool) = false)).card = j := by
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (j + 2))))
      (fun i : Fin (j + 2) => i.val < 2)
    rw [Fin.card_filter_val_lt] at h2
    simp only [decide_eq_true_eq, and_true, Finset.card_univ, Fintype.card_fin] at h2 ⊢
    omega
  have hfilt : ∀ (g : FinPairs (N + 1) → ℝ) (ρ : R → Fin (N + 1) → ℤˣ),
      (∏ i ∈ (Finset.univ.filter fun i : Fin (j + 2) =>
        ¬(decide (i.val < 2) = true ∧ (false : Bool) = false)), Tf i g ρ) = Tg g ^ j :=
      fun g ρ => by
    rw [Finset.prod_congr rfl (g := fun _ => Tg g) fun i hi => ?_, Finset.prod_const, hcard]
    rw [hT]
    have : ¬ i.val < 2 := by
      simpa using hi
    simp [this]
  change |(∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, ∏ i ∈ (Finset.univ : Finset (Fin (j + 2))), Tf i g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∏ k : R, ∫ z : ℝ, (Real.sqrt ((q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) /
          (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) / (N + 1 : ℝ)) * z) ^
          ((Finset.univ.filter fun i : Fin (j + 2) =>
            (decide (i.val < 2) = true ∧ (false : Bool) = false) ∧ x = k).card)
          ∂gaussianReal 0 1) *
      (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, ∏ i ∈ (Finset.univ.filter fun i : Fin (j + 2) =>
          ¬(decide (i.val < 2) = true ∧ (false : Bool) = false)), Tf i g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((Finset.univ : Finset (Fin (j + 2))).card + 1 : ℕ) / 2 : ℝ) at h1
  have e1 : (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, ∏ i ∈ (Finset.univ : Finset (Fin (j + 2))), Tf i g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      ∫ g, Tg g ^ j * ∫ ρ : R → Fin (N + 1) → ℤˣ, A g ρ ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    beta_reduce
    simp only [hprod, mul_comm (A g _ ^ 2)]
    rw [integral_const_mul]
  have e2 : (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, ∏ i ∈ (Finset.univ.filter fun i : Fin (j + 2) =>
          ¬(decide (i.val < 2) = true ∧ (false : Bool) = false)), Tf i g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      ∫ g, Tg g ^ j ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    beta_reduce
    have hc : (fun ρ : R → Fin (N + 1) → ℤˣ => ∏ i ∈ (Finset.univ.filter fun i : Fin (j + 2) =>
          ¬(decide (i.val < 2) = true ∧ (false : Bool) = false)), Tf i g ρ) =
        fun _ => Tg g ^ j := funext (hfilt g)
    rw [hc]
    simp
  have e3 : (∏ k : R, ∫ z : ℝ, (Real.sqrt ((q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) /
          (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) / (N + 1 : ℝ)) * z) ^
          ((Finset.univ.filter fun i : Fin (j + 2) =>
            (decide (i.val < 2) = true ∧ (false : Bool) = false) ∧ x = k).card)
          ∂gaussianReal 0 1) =
      (q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) /
          (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) / (N + 1 : ℝ) := by
    have hX : 0 ≤ (q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) /
        (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) / (N + 1 : ℝ) := div_nonneg hX0 (by positivity)
    rw [Finset.prod_eq_single x]
    · have hc2 : (Finset.univ.filter fun i : Fin (j + 2) =>
          (decide (i.val < 2) = true ∧ (false : Bool) = false) ∧ x = x).card = 2 := by
        have := Fin.card_filter_val_lt (n := j + 2) (m := 2)
        simp only [decide_eq_true_eq, and_true]
        simpa using this
      rw [hc2]
      have := integral_pow_add_two_scaled_gaussianReal
        (Real.sqrt ((q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) /
          (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) / (N + 1 : ℝ))) 0
      simp only [zero_add, pow_zero, integral_const, probReal_univ, one_smul, Nat.cast_zero,
        mul_one, Real.sq_sqrt hX, one_mul] at this
      simpa using this
    · intro k _ hk
      have : (Finset.univ.filter fun i : Fin (j + 2) =>
          (decide (i.val < 2) = true ∧ (false : Bool) = false) ∧ x = k).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _ hi
        exact hk hi.2.symm
      rw [this]
      simp
    · intro h
      exact absurd (Finset.mem_univ x) h
  rw [e1, e2, e3] at h1
  simpa only [Finset.card_univ, Fintype.card_fin] using h1

/-- **`𝔼 T_{xy}² T^j` (Proposition 1.10.4 for one squared pair and `j` globals).** -/
theorem sk_T_pair_square_moment_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R : Type*} [Fintype R] [LinearOrder R] {x y : R} (hxy : x ≠ y) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tg : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
      ((N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i) - q
    let P : (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ := fun g ρ =>
      (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * ((ρ y i : ℝ) - bmean g i)
    let α : ℝ := (∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1) - 2 * q + 1
    |(∫ g, Tg g ^ j * ∫ ρ : R → Fin (N + 1) → ℤˣ, P g ρ ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) *
      ∫ g, Tg g ^ j ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      C / ((N : ℝ) + 1) ^ (((j + 3 : ℕ) : ℝ) / 2) := by
  classical
  obtain ⟨C, hC0, hC⟩ := sk_T_pair_gaussian_moment_uniform β₀ hβ₀ (R := R) (J := Fin (j + 2))
    (fun i => decide (i.val < 2)) (fun i => decide (i.val < 2)) (fun _ => min x y)
    (fun _ => max x y) (fun _ _ _ => min_lt_max.mpr hxy) Finset.univ
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro E bmean Tg P α
  have h1 := hC β h q hfix hb N
  have hα := tanh_fourth_sub_two_mul_add_one_mem_Icc_of_fixedPoint hfix
  let Tf : Fin (j + 2) → (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ :=
    fun i g ρ => ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
        (if decide (i.val < 2) = true then (ρ (min x y) v : ℝ) - bmean g v else bmean g v) *
        (if decide (i.val < 2) = true then (ρ (max x y) v : ℝ) - bmean g v else bmean g v)) -
          (if (decide (i.val < 2) || decide (i.val < 2)) = true then 0 else q)
  have hPmm : ∀ (g : FinPairs (N + 1) → ℝ) (ρ : R → Fin (N + 1) → ℤˣ),
      (N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1), ((ρ (min x y) v : ℝ) - bmean g v) *
        ((ρ (max x y) v : ℝ) - bmean g v) = P g ρ := fun g ρ => by
    rcases le_total x y with hle | hle
    · simp [min_eq_left hle, max_eq_right hle, P]
    · simp only [min_eq_right hle, max_eq_left hle, P]
      simp only [mul_comm (((ρ y _ : ℤˣ) : ℝ) - _)]
  have hT : ∀ (i : Fin (j + 2)) (g : FinPairs (N + 1) → ℝ) (ρ : R → Fin (N + 1) → ℤˣ),
      Tf i g ρ = if i.val < 2 then P g ρ else Tg g := fun i g ρ => by
    by_cases hi : i.val < 2
    · have hi' : (i : ℕ) ≤ 1 := by omega
      simp [Tf, hi, hi', hPmm, Tg]
    · have hi' : ¬ (i : ℕ) ≤ 1 := by omega
      simp [Tf, hi, hi', P, Tg]
  have hprod : ∀ (g : FinPairs (N + 1) → ℝ) (ρ : R → Fin (N + 1) → ℤˣ),
      (∏ i : Fin (j + 2), Tf i g ρ) = P g ρ ^ 2 * Tg g ^ j := fun g ρ => by
    simp only [hT]
    simp [Fin.prod_univ_succ, pow_succ]
    ring
  have hcard : (Finset.univ.filter fun i : Fin (j + 2) =>
        ¬(decide (i.val < 2) = true ∧ decide (i.val < 2) = true)).card = j := by
    have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (j + 2))))
      (fun i : Fin (j + 2) => i.val < 2)
    rw [Fin.card_filter_val_lt] at h2
    simp only [decide_eq_true_eq, and_self, Finset.card_univ, Fintype.card_fin] at h2 ⊢
    omega
  have hfilt : ∀ (g : FinPairs (N + 1) → ℝ) (ρ : R → Fin (N + 1) → ℤˣ),
      (∏ i ∈ (Finset.univ.filter fun i : Fin (j + 2) =>
        ¬(decide (i.val < 2) = true ∧ decide (i.val < 2) = true)), Tf i g ρ) = Tg g ^ j :=
      fun g ρ => by
    rw [Finset.prod_congr rfl (g := fun _ => Tg g) fun i hi => ?_, Finset.prod_const, hcard]
    rw [hT]
    have : ¬ i.val < 2 := by
      simpa using hi
    simp [this]
  change |(∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, ∏ i ∈ (Finset.univ : Finset (Fin (j + 2))), Tf i g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∏ k : R × R, ∫ z : ℝ, (Real.sqrt (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) * z) ^
          ((Finset.univ.filter fun i : Fin (j + 2) =>
            (decide (i.val < 2) = true ∧ decide (i.val < 2) = true) ∧
              (min x y, max x y) = k).card)
          ∂gaussianReal 0 1) *
      (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, ∏ i ∈ (Finset.univ.filter fun i : Fin (j + 2) =>
          ¬(decide (i.val < 2) = true ∧ decide (i.val < 2) = true)), Tf i g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((Finset.univ : Finset (Fin (j + 2))).card + 1 : ℕ) / 2 : ℝ) at h1
  have e1 : (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, ∏ i ∈ (Finset.univ : Finset (Fin (j + 2))), Tf i g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      ∫ g, Tg g ^ j * ∫ ρ : R → Fin (N + 1) → ℤˣ, P g ρ ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    beta_reduce
    simp only [hprod, mul_comm (P g _ ^ 2)]
    rw [integral_const_mul]
  have e2 : (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, ∏ i ∈ (Finset.univ.filter fun i : Fin (j + 2) =>
          ¬(decide (i.val < 2) = true ∧ decide (i.val < 2) = true)), Tf i g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      ∫ g, Tg g ^ j ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    beta_reduce
    have hc : (fun ρ : R → Fin (N + 1) → ℤˣ => ∏ i ∈ (Finset.univ.filter fun i : Fin (j + 2) =>
          ¬(decide (i.val < 2) = true ∧ decide (i.val < 2) = true)), Tf i g ρ) =
        fun _ => Tg g ^ j := funext (hfilt g)
    rw [hc]
    simp
  have e3 : (∏ k : R × R, ∫ z : ℝ, (Real.sqrt (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) * z) ^
          ((Finset.univ.filter fun i : Fin (j + 2) =>
            (decide (i.val < 2) = true ∧ decide (i.val < 2) = true) ∧
              (min x y, max x y) = k).card)
          ∂gaussianReal 0 1) = α / (1 - β ^ 2 * α) / (N + 1 : ℝ) := by
    have hDpos : 0 < 1 - β ^ 2 * α := by
      have h2 : β ^ 2 * α ≤ β ^ 2 * 1 := mul_le_mul_of_nonneg_left hα.2 (sq_nonneg _)
      linarith only [h2, hb, hβ₀]
    have hX : 0 ≤ α / (1 - β ^ 2 * α) / (N + 1 : ℝ) :=
      div_nonneg (div_nonneg hα.1 hDpos.le) (by positivity)
    rw [Finset.prod_eq_single (min x y, max x y)]
    · have hc2 : (Finset.univ.filter fun i : Fin (j + 2) =>
          (decide (i.val < 2) = true ∧ decide (i.val < 2) = true) ∧
            (min x y, max x y) = (min x y, max x y)).card = 2 := by
        have := Fin.card_filter_val_lt (n := j + 2) (m := 2)
        simp only [decide_eq_true_eq, and_self, and_true]
        simpa using this
      rw [hc2]
      have := integral_pow_add_two_scaled_gaussianReal
        (Real.sqrt (α / (1 - β ^ 2 * α) / (N + 1 : ℝ))) 0
      simp only [zero_add, pow_zero, integral_const, probReal_univ, one_smul, Nat.cast_zero,
        mul_one, Real.sq_sqrt hX, one_mul] at this
      simpa using this
    · intro k _ hk
      have : (Finset.univ.filter fun i : Fin (j + 2) =>
          (decide (i.val < 2) = true ∧ decide (i.val < 2) = true) ∧
            (min x y, max x y) = k).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i _ hi
        exact hk hi.2.symm
      rw [this]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [e1, e2, e3] at h1
  simpa only [Finset.card_univ, Fintype.card_fin] using h1

/-- **`𝔼 T_{xy} T_x T_y T^j = O(j+4)`:** a pair label that occurs once makes the Gaussian
reference of Proposition 1.10.4 vanish. -/
theorem sk_T_pair_two_singles_moment_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R : Type*} [Fintype R] [LinearOrder R] {x y : R} (hxy : x ≠ y) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tg : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
      ((N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i) - q
    let A : R → (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ := fun z g ρ =>
      (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ z i : ℝ) - bmean g i) * bmean g i
    let P : (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ := fun g ρ =>
      (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * ((ρ y i : ℝ) - bmean g i)
    |∫ g, Tg g ^ j * ∫ ρ : R → Fin (N + 1) → ℤˣ, P g ρ * A x g ρ * A y g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      C / ((N : ℝ) + 1) ^ (((j + 4 : ℕ) : ℝ) / 2) := by
  classical
  have hodd : Odd (Finset.univ.filter fun i : Fin (j + 3) =>
      (decide (i.val < 3) = true ∧ decide (i.val = 0) = true) ∧
        ((if i.val = 0 then min x y else if i.val = 2 then y else x), max x y) =
          (min x y, max x y)).card := by
    have : (Finset.univ.filter fun i : Fin (j + 3) =>
        (decide (i.val < 3) = true ∧ decide (i.val = 0) = true) ∧
          ((if i.val = 0 then min x y else if i.val = 2 then y else x), max x y) =
            (min x y, max x y)) = {⟨0, by omega⟩} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        decide_eq_true_eq, Fin.ext_iff]
      constructor
      · rintro ⟨⟨-, h0⟩, -⟩
        exact h0
      · intro h0
        refine ⟨⟨by omega, h0⟩, ?_⟩
        simp [h0]
    rw [this, Finset.card_singleton]
    exact odd_one
  obtain ⟨C, hC0, hC⟩ := sk_T_pair_odd_class_moment_uniform β₀ hβ₀ (R := R) (J := Fin (j + 3))
    (fun i => decide (i.val < 3)) (fun i => decide (i.val = 0))
    (fun i => if i.val = 0 then min x y else if i.val = 2 then y else x) (fun _ => max x y)
    (fun i _ hS => by
      have : i.val = 0 := by simpa using hS
      simp [this, min_lt_max.mpr hxy]) Finset.univ (min x y, max x y) hodd
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro E bmean Tg A P
  have h1 := hC β h q hfix hb N
  let Tn : ℕ → (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ :=
    fun n g ρ => ((N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1),
        (if decide (n < 3) = true then
          (ρ (if n = 0 then min x y else if n = 2 then y else x) v : ℝ) - bmean g v
          else bmean g v) *
        (if decide (n = 0) = true then (ρ (max x y) v : ℝ) - bmean g v else bmean g v)) -
          (if (decide (n < 3) || decide (n = 0)) = true then 0 else q)
  let Tf : Fin (j + 3) → (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ :=
    fun i g ρ => Tn i.val g ρ
  have hPmm : ∀ (g : FinPairs (N + 1) → ℝ) (ρ : R → Fin (N + 1) → ℤˣ),
      (N + 1 : ℝ)⁻¹ * ∑ v : Fin (N + 1), ((ρ (min x y) v : ℝ) - bmean g v) *
        ((ρ (max x y) v : ℝ) - bmean g v) = P g ρ := fun g ρ => by
    rcases le_total x y with hle | hle
    · simp [min_eq_left hle, max_eq_right hle, P]
    · simp only [min_eq_right hle, max_eq_left hle, P]
      simp only [mul_comm (((ρ y _ : ℤˣ) : ℝ) - _)]
  have hT : ∀ (n : ℕ) (g : FinPairs (N + 1) → ℝ) (ρ : R → Fin (N + 1) → ℤˣ),
      Tn n g ρ = if n = 0 then P g ρ else if n = 1 then A x g ρ else
        if n = 2 then A y g ρ else Tg g := fun n g ρ => by
    by_cases h0 : n = 0
    · subst h0
      simp [Tn, hPmm]
    by_cases h1 : n = 1
    · subst h1
      simp [Tn, A]
    by_cases h2 : n = 2
    · subst h2
      simp [Tn, A]
    have h3 : ¬ n < 3 := by omega
    simp [Tn, h0, h1, h2, h3, Tg]
  have hprod : ∀ (g : FinPairs (N + 1) → ℝ) (ρ : R → Fin (N + 1) → ℤˣ),
      (∏ i : Fin (j + 3), Tf i g ρ) = P g ρ * A x g ρ * A y g ρ * Tg g ^ j := fun g ρ => by
    have : ∀ i : Fin (j + 3), Tf i g ρ = if i.val = 0 then P g ρ else if i.val = 1 then A x g ρ
        else if i.val = 2 then A y g ρ else Tg g := fun i => hT i.val g ρ
    simp only [this]
    simp [Fin.prod_univ_succ]
    ring
  change |∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, ∏ i ∈ (Finset.univ : Finset (Fin (j + 3))), Tf i g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      C / ((N : ℝ) + 1) ^ (((Finset.univ : Finset (Fin (j + 3))).card + 1 : ℕ) / 2 : ℝ) at h1
  have e1 : (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, ∏ i ∈ (Finset.univ : Finset (Fin (j + 3))), Tf i g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      ∫ g, Tg g ^ j * ∫ ρ : R → Fin (N + 1) → ℤˣ, P g ρ * A x g ρ * A y g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    beta_reduce
    simp only [hprod, mul_comm (P g _ * A x g _ * A y g _)]
    rw [integral_const_mul]
  rw [e1] at h1
  simpa only [Finset.card_univ, Fintype.card_fin] using h1

end SpinGlasses
