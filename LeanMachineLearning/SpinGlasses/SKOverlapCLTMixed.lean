/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTGlobalGaussian
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianMomentBound

/-!
# Theorem 1.10.1 (Talagrand, Eq. (1.290)): the mixed moments of the overlaps

The T-moment `νT s` of a finite family of pair, single and global factors is, up to
`O(card s + 1)`, the product of Gaussian moments: the pair factors with the same ordered pair of
replica labels share a Gaussian of variance `A²/(N+1)` (Proposition 1.10.4), the single factors with
the same replica label share a Gaussian of variance `B²/(N+1)` (Proposition 1.10.5), and the global
factors are the powers of one Gaussian of variance `C²/(N+1)` (the induction of Section 1.10).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Nat

namespace SpinGlasses

/-- **Error propagation for a factorisation into three classes.** -/
theorem abs_sub_prod_le_of_three {X Y Z GP GS GG e₁ e₂ e₃ : ℝ} (h1 : |X - GP * Y| ≤ e₁)
    (h2 : |Y - GS * Z| ≤ e₂) (h3 : |Z - GG| ≤ e₃) :
    |X - GP * GS * GG| ≤ e₁ + |GP| * e₂ + |GP| * |GS| * e₃ := by
  have e : X - GP * GS * GG = (X - GP * Y) + GP * (Y - GS * Z) + GP * GS * (Z - GG) := by ring
  rw [e]
  refine (abs_add_three _ _ _).trans ?_
  rw [abs_mul, abs_mul, abs_mul]
  gcongr

/-- The sizes of the classes partition the selected factors. -/
theorem card_filter_eq_sum_class {J ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset J)
    (P : J → Prop) [DecidablePred P] (f : J → ι) :
    (s.filter P).card = ∑ k : ι, (s.filter fun j => P j ∧ f j = k).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (s := s.filter P) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.filter_filter]

/-- **Proposition 1.10.5 for a family whose selected factors have `S = false`.** The hypothesis
`S = false` is only needed on the selected factors. -/
theorem sk_T_single_gaussian_moment_on (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype R] [DecidableEq R]
    (L S : J → Bool) (a b : J → R) (s : Finset J) (hs : ∀ j ∈ s, S j = false) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let T : J → (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ :=
      fun j g ρ => ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if L j then (ρ (a j) i : ℝ) - bmean g i else bmean g i) *
        (if S j then (ρ (b j) i : ℝ) - bmean g i else bmean g i)) -
          (if L j || S j then 0 else q)
    let νT : Finset J → ℝ := fun s => ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
      ∏ j ∈ s, T j g ρ ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    |νT s - (∏ k : R, ∫ x : ℝ,
        (Real.sqrt ((q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) /
          (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) / (N + 1 : ℝ)) * x) ^
          (s.filter fun j => (L j = true ∧ S j = false) ∧ a j = k).card ∂gaussianReal 0 1) *
      νT (s.filter fun j => ¬(L j = true ∧ S j = false))| ≤
      C / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
  classical
  obtain ⟨C, hC0, hC⟩ := sk_T_single_gaussian_moment_uniform β₀ hβ₀ (R := R) (J := J) L
    (fun _ => false) (fun _ => rfl) a b s
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro E bmean T νT qh α
  have h1 := hC β h q hfix hb N
  let T' : J → (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ :=
    fun j g ρ => ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if L j then (ρ (a j) i : ℝ) - bmean g i else bmean g i) *
        (if (false : Bool) then (ρ (b j) i : ℝ) - bmean g i else bmean g i)) -
          (if L j || (false : Bool) then 0 else q)
  let νT' : Finset J → ℝ := fun t => ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
      ∏ j ∈ t, T' j g ρ ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  have hνT : ∀ t : Finset J, t ⊆ s → νT t = νT' t := fun t ht => by
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
    exact Finset.prod_congr rfl fun j hj => by simp only [T, T', hs j (ht hj)]
  have hsub : (s.filter fun j => ¬(L j = true ∧ S j = false)) ⊆ s := Finset.filter_subset _ _
  have hfilt1 : ∀ k, (s.filter fun j => (L j = true ∧ (false : Bool) = false) ∧ a j = k) =
      s.filter fun j => (L j = true ∧ S j = false) ∧ a j = k := fun k =>
    Finset.filter_congr fun j hj => by simp [hs j hj]
  have hfilt2 : (s.filter fun j => ¬(L j = true ∧ (false : Bool) = false)) =
      s.filter fun j => ¬(L j = true ∧ S j = false) :=
    Finset.filter_congr fun j hj => by simp [hs j hj]
  have h1' : |νT' s - (∏ k : R, ∫ x : ℝ,
        (Real.sqrt ((q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) /
          (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) / (N + 1 : ℝ)) * x) ^
          (s.filter fun j => (L j = true ∧ (false : Bool) = false) ∧ a j = k).card
          ∂gaussianReal 0 1) *
      νT' (s.filter fun j => ¬(L j = true ∧ (false : Bool) = false))| ≤
      C / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := h1
  have hprod : (∏ k : R, ∫ x : ℝ,
        (Real.sqrt ((q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) /
          (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) / (N + 1 : ℝ)) * x) ^
          (s.filter fun j => (L j = true ∧ (false : Bool) = false) ∧ a j = k).card
          ∂gaussianReal 0 1) = ∏ k : R, ∫ x : ℝ,
        (Real.sqrt ((q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) /
          (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) / (N + 1 : ℝ)) * x) ^
          (s.filter fun j => (L j = true ∧ S j = false) ∧ a j = k).card ∂gaussianReal 0 1 :=
    Finset.prod_congr rfl fun k _ => by rw [hfilt1 k]
  rw [hprod, hfilt2, ← hνT s le_rfl, ← hνT _ hsub] at h1'
  exact h1'

/-- **Theorem 1.10.1 (Eq. (1.290)), enumerated form.** The moment `νT s` of a finite family of
pair, single and global factors is the product of the Gaussian moments of the three classes, up
to `O(card s + 1)`. The single factors are normalized as `(L,S) = (true,false)`. -/
theorem sk_T_mixed_gaussian_moment_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R J : Type*} [Fintype R] [LinearOrder R]
    (L S : J → Bool) (hnorm : ∀ j, ¬(L j = true ∧ S j = true) → S j = false)
    (a b : J → R) (hord : ∀ j, L j = true → S j = true → a j < b j) (s : Finset J) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let T : J → (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ :=
      fun j g ρ => ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if L j then (ρ (a j) i : ℝ) - bmean g i else bmean g i) *
        (if S j then (ρ (b j) i : ℝ) - bmean g i else bmean g i)) -
          (if L j || S j then 0 else q)
    let νT : Finset J → ℝ := fun s => ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
      ∏ j ∈ s, T j g ρ ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let D : ℝ := 1 - β ^ 2 * (1 - 4 * q + 3 * qh)
    let B2 : ℝ := (q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) / D
    let E0 : ℝ := (qh - q ^ 2) + β ^ 2 * (qh - q ^ 2) * (α / (1 - β ^ 2 * α)) +
      2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qh) * B2
    |νT s - (∏ κ : R × R, ∫ x : ℝ,
          (Real.sqrt (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) * x) ^
            (s.filter fun j => (L j = true ∧ S j = true) ∧ (a j, b j) = κ).card
            ∂gaussianReal 0 1) *
        (∏ k : R, ∫ x : ℝ, (Real.sqrt (B2 / (N + 1 : ℝ)) * x) ^
            (s.filter fun j => (L j = true ∧ S j = false) ∧ a j = k).card ∂gaussianReal 0 1) *
        ∫ x : ℝ, (Real.sqrt (E0 / D / (N + 1 : ℝ)) * x) ^
          (s.filter fun j => L j = false ∧ S j = false).card ∂gaussianReal 0 1| ≤
      C / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
  classical
  let sn : Finset J := s.filter fun j => ¬(L j = true ∧ S j = true)
  let sg : Finset J := s.filter fun j => L j = false ∧ S j = false
  have hsn : ∀ j ∈ sn, S j = false := fun j hj => hnorm j (Finset.mem_filter.mp hj).2
  obtain ⟨C₁, hC₁0, hC₁⟩ := sk_T_pair_gaussian_moment_uniform β₀ hβ₀ L S a b hord s
  obtain ⟨C₂, hC₂0, hC₂⟩ := sk_T_single_gaussian_moment_on β₀ hβ₀ L S a b sn hsn
  obtain ⟨C₃, hC₃0, hC₃⟩ := sk_T_global_gaussian_moment_uniform β₀ hβ₀ sg.card
  let cP : R × R → ℕ := fun κ =>
    (s.filter fun j => (L j = true ∧ S j = true) ∧ (a j, b j) = κ).card
  let cS : R → ℕ := fun k => (s.filter fun j => (L j = true ∧ S j = false) ∧ a j = k).card
  let MP : ℝ := (∏ κ, ((cP κ)! : ℝ)) * Real.sqrt 12 ^ (∑ κ, cP κ)
  let MS : ℝ := (∏ k, ((cS k)! : ℝ)) * Real.sqrt 12 ^ (∑ k, cS k)
  have hMP : 0 ≤ MP := by positivity
  have hMS : 0 ≤ MS := by positivity
  refine ⟨C₁ + MP * C₂ + MP * MS * C₃ + 1, by positivity, fun β h q hfix hb N => ?_⟩
  intro E bmean T νT qh α D B2 E0
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := fixedPoint_mem_Icc hfix
  obtain ⟨hdq, hD, hB0, hB2⟩ := single_coeff_facts β₀ hβ₀ β h q hfix hb
  have hα : 0 ≤ α ∧ α ≤ 1 := tanh_fourth_sub_two_mul_add_one_mem_Icc_of_fixedPoint hfix
  have hβ4 : β ^ 2 ≤ 1 / 4 := by linarith
  have hDα : 3 / 4 ≤ 1 - β ^ 2 * α := by
    have h2 : β ^ 2 * α ≤ β ^ 2 * 1 := mul_le_mul_of_nonneg_left hα.2 (sq_nonneg _)
    linarith
  have hA0 : 0 ≤ α / (1 - β ^ 2 * α) := div_nonneg hα.1 (by linarith)
  have hA12 : α / (1 - β ^ 2 * α) ≤ 12 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  let GP : ℝ := ∏ κ : R × R, ∫ x : ℝ,
    (Real.sqrt (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) * x) ^ (cP κ) ∂gaussianReal 0 1
  let GS : ℝ := ∏ k : R, ∫ x : ℝ, (Real.sqrt (B2 / (N + 1 : ℝ)) * x) ^ (cS k) ∂gaussianReal 0 1
  let GG : ℝ := ∫ x : ℝ, (Real.sqrt (E0 / D / (N + 1 : ℝ)) * x) ^ sg.card ∂gaussianReal 0 1
  have e1 : |νT s - GP * νT sn| ≤
      C₁ / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := hC₁ β h q hfix hb N
  have hcS : ∀ k, (sn.filter fun j => (L j = true ∧ S j = false) ∧ a j = k) =
      s.filter fun j => (L j = true ∧ S j = false) ∧ a j = k := fun k => by
    ext j
    simp only [sn, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hjs, -⟩, h1, h2⟩
      exact ⟨hjs, h1, h2⟩
    · rintro ⟨hjs, h1, h2⟩
      exact ⟨⟨hjs, fun hh => by rw [h1.2] at hh; exact absurd hh.2 (by simp)⟩, h1, h2⟩
  have hsgeq : (sn.filter fun j => ¬(L j = true ∧ S j = false)) = sg := by
    ext j
    simp only [sn, sg, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hjs, hnp⟩, hh⟩
      have hL : L j = false := by
        by_contra hL
        exact hh ⟨by simpa using hL, hnorm j hnp⟩
      exact ⟨hjs, hL, hnorm j hnp⟩
    · rintro ⟨hjs, hL, hS⟩
      refine ⟨⟨hjs, fun hh => by rw [hL] at hh; exact absurd hh.1 (by simp)⟩, ?_⟩
      intro hh
      rw [hL] at hh
      exact absurd hh.1 (by simp)
  have e2 : |νT sn - GS * νT sg| ≤
      C₂ / ((N : ℝ) + 1) ^ (((sn.card + 1 : ℕ) : ℝ) / 2) := by
    have := hC₂ β h q hfix hb N
    rw [hsgeq] at this
    have hGS : (∏ k : R, ∫ x : ℝ, (Real.sqrt (B2 / (N + 1 : ℝ)) * x) ^
        (sn.filter fun j => (L j = true ∧ S j = false) ∧ a j = k).card ∂gaussianReal 0 1) = GS :=
      Finset.prod_congr rfl fun k _ => by rw [hcS k]
    have this' : |νT sn - (∏ k : R, ∫ x : ℝ, (Real.sqrt (B2 / (N + 1 : ℝ)) * x) ^
        (sn.filter fun j => (L j = true ∧ S j = false) ∧ a j = k).card ∂gaussianReal 0 1) *
        νT sg| ≤ C₂ / ((N : ℝ) + 1) ^ (((sn.card + 1 : ℕ) : ℝ) / 2) := this
    rw [hGS] at this'
    exact this'
  have hZ : νT sg = ∫ g, (((N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i) - q) ^ sg.card
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have hT : ∀ j ∈ sg, ∀ ρ : R → Fin (N + 1) → ℤˣ,
        T j g ρ = ((N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i) - q := fun j hj ρ => by
      have hj' := (Finset.mem_filter.mp hj).2
      simp [T, hj'.1, hj'.2]
    have : ∀ ρ : R → Fin (N + 1) → ℤˣ, ∏ j ∈ sg, T j g ρ =
        (((N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i) - q) ^ sg.card := fun ρ => by
      rw [Finset.prod_congr rfl (fun j hj => hT j hj ρ), Finset.prod_const]
    simp only [this, integral_const, probReal_univ, smul_eq_mul, one_mul]
  have e3 : |νT sg - GG| ≤ C₃ / ((N : ℝ) + 1) ^ (((sg.card + 1 : ℕ) : ℝ) / 2) := by
    rw [hZ]
    exact hC₃ β h q hfix hb N
  -- cardinalities
  have hp : (∑ κ, cP κ) = (s.filter fun j => L j = true ∧ S j = true).card :=
    (card_filter_eq_sum_class s (fun j => L j = true ∧ S j = true) (fun j => (a j, b j))).symm
  have hr : (∑ k, cS k) = (s.filter fun j => L j = true ∧ S j = false).card :=
    (card_filter_eq_sum_class s (fun j => L j = true ∧ S j = false) a).symm
  have hsn1 : (sn.filter fun j => L j = true) = s.filter fun j => L j = true ∧ S j = false := by
    ext j
    simp only [sn, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hjs, hnp⟩, hL⟩
      exact ⟨hjs, hL, hnorm j hnp⟩
    · rintro ⟨hjs, hL, hS⟩
      exact ⟨⟨hjs, fun hh => by rw [hS] at hh; exact absurd hh.2 (by simp)⟩, hL⟩
  have hsn2 : (sn.filter fun j => ¬(L j = true)) = sg := by
    ext j
    simp only [sn, sg, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hjs, hnp⟩, hL⟩
      exact ⟨hjs, by simpa using hL, hnorm j hnp⟩
    · rintro ⟨hjs, hL, hS⟩
      exact ⟨⟨hjs, fun hh => by rw [hL] at hh; exact absurd hh.1 (by simp)⟩, by simp [hL]⟩
  have hc1 : s.card = (∑ κ, cP κ) + sn.card := by
    rw [hp]
    exact (Finset.card_filter_add_card_filter_not (s := s) (fun j => L j = true ∧ S j = true)).symm
  have hc2 : sn.card = (∑ k, cS k) + sg.card := by
    rw [hr, ← hsn2, ← hsn1]
    exact (Finset.card_filter_add_card_filter_not (s := sn) (fun j => L j = true)).symm
  -- magnitudes
  have hx : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hGP : |GP| ≤ MP / ((N : ℝ) + 1) ^ (((∑ κ, cP κ : ℕ) : ℝ) / 2) := by
    refine (abs_prod_integral_pow_scaled_gaussianReal_le cP (Real.sqrt_nonneg _)).trans ?_
    have := Real.sqrt_div_pow_le (by positivity) hA0 hA12 (∑ κ, cP κ)
    calc (∏ κ, ((cP κ)! : ℝ)) * Real.sqrt (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) ^ (∑ κ, cP κ)
        ≤ (∏ κ, ((cP κ)! : ℝ)) * (Real.sqrt 12 ^ (∑ κ, cP κ) /
          ((N : ℝ) + 1) ^ (((∑ κ, cP κ : ℕ) : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by simp only [MP]; ring
  have hGS : |GS| ≤ MS / ((N : ℝ) + 1) ^ (((∑ k, cS k : ℕ) : ℝ) / 2) := by
    refine (abs_prod_integral_pow_scaled_gaussianReal_le cS (Real.sqrt_nonneg _)).trans ?_
    have := Real.sqrt_div_pow_le (v := B2) (by positivity) hB0
      (show B2 ≤ 12 by linarith) (∑ k, cS k)
    calc (∏ k, ((cS k)! : ℝ)) * Real.sqrt (B2 / (N + 1 : ℝ)) ^ (∑ k, cS k)
        ≤ (∏ k, ((cS k)! : ℝ)) * (Real.sqrt 12 ^ (∑ k, cS k) /
          ((N : ℝ) + 1) ^ (((∑ k, cS k : ℕ) : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by simp only [MS]; ring
  have h3 := abs_sub_prod_le_of_three e1 e2 e3
  have hε2 : ((∑ κ, cP κ : ℕ) : ℝ) / 2 + ((sn.card + 1 : ℕ) : ℝ) / 2 =
      ((s.card + 1 : ℕ) : ℝ) / 2 := by
    rw [hc1]
    push_cast
    ring
  have hε3 : ((∑ κ, cP κ : ℕ) : ℝ) / 2 + ((∑ k, cS k : ℕ) : ℝ) / 2 +
      ((sg.card + 1 : ℕ) : ℝ) / 2 = ((s.card + 1 : ℕ) : ℝ) / 2 := by
    rw [hc1, hc2]
    push_cast
    ring
  have t2 : |GP| * (C₂ / ((N : ℝ) + 1) ^ (((sn.card + 1 : ℕ) : ℝ) / 2)) ≤
      (MP * C₂) / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
    calc _ ≤ (MP / ((N : ℝ) + 1) ^ (((∑ κ, cP κ : ℕ) : ℝ) / 2)) *
          (C₂ / ((N : ℝ) + 1) ^ (((sn.card + 1 : ℕ) : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right hGP (by positivity)
      _ = (MP * C₂) / (((N : ℝ) + 1) ^ (((∑ κ, cP κ : ℕ) : ℝ) / 2) *
          ((N : ℝ) + 1) ^ (((sn.card + 1 : ℕ) : ℝ) / 2)) := by rw [div_mul_div_comm]
      _ = _ := by rw [← Real.rpow_add hx, hε2]
  have t3 : |GP| * |GS| * (C₃ / ((N : ℝ) + 1) ^ (((sg.card + 1 : ℕ) : ℝ) / 2)) ≤
      (MP * MS * C₃) / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
    calc _ ≤ (MP / ((N : ℝ) + 1) ^ (((∑ κ, cP κ : ℕ) : ℝ) / 2)) *
          (MS / ((N : ℝ) + 1) ^ (((∑ k, cS k : ℕ) : ℝ) / 2)) *
          (C₃ / ((N : ℝ) + 1) ^ (((sg.card + 1 : ℕ) : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hGP hGS (abs_nonneg _) (by positivity))
            (by positivity)
      _ = (MP * MS * C₃) / (((N : ℝ) + 1) ^ (((∑ κ, cP κ : ℕ) : ℝ) / 2) *
          ((N : ℝ) + 1) ^ (((∑ k, cS k : ℕ) : ℝ) / 2) *
          ((N : ℝ) + 1) ^ (((sg.card + 1 : ℕ) : ℝ) / 2)) := by
        rw [div_mul_div_comm, div_mul_div_comm]
      _ = _ := by rw [← Real.rpow_add hx, ← Real.rpow_add hx, hε3]
  change |νT s - GP * GS * GG| ≤ _
  refine h3.trans ?_
  have hsum : C₁ / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) +
      (MP * C₂) / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) +
      (MP * MS * C₃) / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) ≤
      (C₁ + MP * C₂ + MP * MS * C₃ + 1) / ((N : ℝ) + 1) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  exact (add_le_add (add_le_add le_rfl t2) t3).trans hsum

end SpinGlasses
