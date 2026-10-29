/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTGibbsPolynomials
public import LeanMachineLearning.SpinGlasses.GaussianOverlapCovariance

/-!
# Conditional polynomial moments of Gibbs-centered overlaps

The exact centering identity (1.295) and the pair/single polynomial theorem give
Talagrand's consequences immediately after (1.295), with explicit uniform errors.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real ENNReal

universe u v

namespace SpinGlasses

/-- The explicit SK Gaussian reference in the paragraph after (1.295), including
the covariance cases. The statement is independent of the system size. -/
theorem sk_centered_overlap_gaussian_reference (β h q : ℝ) (hβ : 4 * β ^ 2 < 1)
    (hfix : ∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q)
    {R : Type u} [Fintype R] [LinearOrder R] :
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let A2 : ℝ := α / (1 - β ^ 2 * α)
    let B2 : ℝ := (q - qh) * (1 + β ^ 2 * A2) / (1 - β ^ 2 * (1 - 4 * q + 3 * qh))
    let G := fun (p : R × R) (z : (R × R) ⊕ R → ℝ) =>
      Real.sqrt A2 * z (.inl p) + Real.sqrt B2 * z (.inr p.1) +
        Real.sqrt B2 * z (.inr p.2)
    let P := Measure.pi fun _ : (R × R) ⊕ R => gaussianReal 0 1
    HasGaussianLaw (fun z p => G p z) P ∧
      (∀ p, ∫ z, G p z ∂P = 0) ∧ ∀ p q, p.1 < p.2 → q.1 < q.2 →
        (∫ z, G p z * G q z ∂P) = if p = q then A2 + 2 * B2 else
          if (({p.1, p.2} : Finset R) ∩ {q.1, q.2}).Nonempty then B2 else 0 := by
  intro qh α A2 B2 G P
  have hp := one_sub_mul_div_bounds (sq_nonneg β)
    (show β ^ 2 ≤ (1 / 4 : ℝ) by linarith)
    (tanh_fourth_sub_two_mul_add_one_mem_Icc_of_fixedPoint hfix)
    (by norm_num : (1 / 4 : ℝ) < 1)
  have ha : 0 ≤ A2 := hp.2.1
  have hb : 0 ≤ B2 := (single_coeff_facts β hβ β h q hfix le_rfl).2.2.1
  have hg := gaussian_overlap_reference (R := R) ha hb
  exact ⟨hg.1, hg.2.1, fun p q hp hq => gaussian_overlap_covariance_of_lt ha hb p q hp hq⟩

/-- **The polynomial consequence after Talagrand (1.295).** The normalized conditional
moment of Gibbs-centered overlaps has a deterministic Gaussian reference and small
variance over the disorder. Repeated factors are allowed. -/
theorem sk_centered_overlap_gibbs_moments_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R : Type u} [Fintype R] [LinearOrder R] (r s : R) (hrs : r ≠ s)
    {K : Type v} [Fintype K] (x y : K → R)
    (hxy : ∀ j, x j < y j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let qbar := fun g => ∫ ρ : R → Fin (N + 1) → ℤˣ,
      (N + 1 : ℝ)⁻¹ * ∑ i, (ρ r i : ℝ) * (ρ s i : ℝ)
      ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
    let W := fun g => ((N : ℝ) + 1) ^ ((Fintype.card K : ℝ) / 2) *
      ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ j, (((N + 1 : ℝ)⁻¹ * ∑ i, (ρ (x j) i : ℝ) * (ρ (y j) i : ℝ)) - qbar g)
      ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let A2 : ℝ := α / (1 - β ^ 2 * α)
    let B2 : ℝ := (q - qh) * (1 + β ^ 2 * A2) / (1 - β ^ 2 * (1 - 4 * q + 3 * qh))
    let G : ℝ := ∫ z : (R × R) ⊕ R → ℝ,
      ∏ j, (Real.sqrt A2 * z (.inl (x j, y j)) +
        Real.sqrt B2 * z (.inr (x j)) + Real.sqrt B2 * z (.inr (y j)))
      ∂(Measure.pi fun _ : (R × R) ⊕ R => gaussianReal 0 1)
    let P := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1
    MemLp W 2 P ∧ |(∫ g, W g ∂P) - G| ≤ C / Real.sqrt ((N : ℝ) + 1) ∧
      (∫ g, (W g - G) ^ 2 ∂P) ≤ C / Real.sqrt ((N : ℝ) + 1) ∧
      (∫ g, (W g - ∫ g', W g' ∂P) ^ 2 ∂P) ≤ C / Real.sqrt ((N : ℝ) + 1) := by
  let S : K → Option Bool → Bool := fun _ m => m.isNone
  let a : K → Option Bool → R := fun j m =>
    match m with | some true => y j | _ => x j
  let b : K → Option Bool → R := fun j _ => y j
  have hsum (F : Option Bool → ℝ) :
      (∑ m, F m) = F none + F (some false) + F (some true) := by
    rw [Fintype.sum_option, Fintype.sum_bool]
    ring
  have ho : ∀ j m, S j m = true → a j m < b j m := by
    intro j m
    cases m with
    | none => intro _; exact hxy j
    | some c => cases c <;> simp [S]
  obtain ⟨C, hCpos, hCs⟩ := @sk_T_lincomb_gibbs_moments_uniform β₀ hβ₀ R
    inferInstance inferInstance ⟨r⟩ K inferInstance (Option Bool) inferInstance
    S a b (fun _ _ => 1) ho
  refine ⟨C, hCpos, fun β h q hfix hb N => ?_⟩
  intro E qbar W qh α A2 B2 G P
  let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
    ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
  let T := fun j m g (ρ : R → Fin (N + 1) → ℤˣ) =>
    (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ (a j m) i : ℝ) - bmean g i) *
      (if S j m then (ρ (b j m) i : ℝ) - bmean g i else bmean g i)
  let V := fun g => ((N : ℝ) + 1) ^ ((Fintype.card K : ℝ) / 2) *
    ∫ ρ : R → Fin (N + 1) → ℤˣ, ∏ j, ∑ m : Option Bool, T j m g ρ
      ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
  let G₀ : ℝ := ∫ z : (R × R) ⊕ R → ℝ,
    ∏ j, ∑ m : Option Bool,
      if S j m then Real.sqrt A2 * z (.inl (a j m, b j m))
        else Real.sqrt B2 * z (.inr (a j m))
    ∂(Measure.pi fun _ : (R × R) ⊕ R => gaussianReal 0 1)
  have hs : MemLp V 2 P ∧ |(∫ g, V g ∂P) - G₀| ≤ C / Real.sqrt ((N : ℝ) + 1) ∧
      (∫ g, (V g - G₀) ^ 2 ∂P) ≤ C / Real.sqrt ((N : ℝ) + 1) := by
    simpa only [one_mul] using hCs β h q hfix hb N
  have hW : W = V := by
    funext g
    dsimp only [W, V]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ρ
    apply prod_congr rfl
    intro j _
    have he := integral_pi_overlap_centered_decomp (Measure.count.tilted (E g))
      (fun (σ : Fin (N + 1) → ℤˣ) i => (σ i : ℝ)) (bmean g) (fun _ => rfl)
      (N + 1 : ℝ)⁻¹ hrs (x j) (y j) ρ
    rw [hsum]
    exact he
  have hG : G₀ = G := by
    apply integral_congr_ae
    filter_upwards [] with z
    apply prod_congr rfl
    intro j _
    rw [hsum]
    rfl
  rw [← hW, hG] at hs
  have hv : variance W P ≤ C / Real.sqrt ((N : ℝ) + 1) := by
    calc
      variance W P = variance (fun g => W g - G) P :=
        (variance_sub_const hs.1.aestronglyMeasurable G).symm
      _ ≤ ∫ g, (W g - G) ^ 2 ∂P :=
        variance_le_expectation_sq (hs.1.sub (memLp_const G)).aestronglyMeasurable
      _ ≤ _ := hs.2.2
  refine ⟨hs.1, hs.2.1, hs.2.2, ?_⟩
  simpa only [variance_eq_integral hs.1.aemeasurable] using hv

end SpinGlasses
