/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTGibbsEnumerated

/-!
# Conditional moments of products of finite linear combinations

A finite expansion transfers both the mean error and the mean-square error from
pair/single monomials to arbitrary products of finite linear combinations. The
Gaussian reference uses the same independent coordinate family in every summand.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real ENNReal

universe u v w

namespace SpinGlasses

/-- Conditional polynomial moments of the pair and single factors, with their explicit
Gaussian reference. Coefficients and labels are fixed before the uniform constants. -/
theorem sk_T_lincomb_gibbs_moments_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R : Type u} [Fintype R] [LinearOrder R] [Nonempty R]
    {K : Type v} [Fintype K] [DecidableEq K] {M : Type w} [Fintype M]
    (S : K → M → Bool) (a b : K → M → R) (γ : K → M → ℝ)
    (hord : ∀ j m, S j m = true → a j m < b j m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let T := fun j m g (ρ : R → Fin (N + 1) → ℤˣ) =>
      (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ (a j m) i : ℝ) - bmean g i) *
        (if S j m then (ρ (b j m) i : ℝ) - bmean g i else bmean g i)
    let V := fun g => ((N : ℝ) + 1) ^ ((Fintype.card K : ℝ) / 2) *
      ∫ ρ : R → Fin (N + 1) → ℤˣ, ∏ j, ∑ m, γ j m * T j m g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let A2 : ℝ := α / (1 - β ^ 2 * α)
    let B2 : ℝ := (q - qh) * (1 + β ^ 2 * A2) / (1 - β ^ 2 * (1 - 4 * q + 3 * qh))
    let G : ℝ := ∫ z : (R × R) ⊕ R → ℝ,
      ∏ j, ∑ m, γ j m *
        (if S j m then Real.sqrt A2 * z (.inl (a j m, b j m))
          else Real.sqrt B2 * z (.inr (a j m)))
      ∂(Measure.pi fun _ : (R × R) ⊕ R => gaussianReal 0 1)
    let P := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1
    MemLp V 2 P ∧ |(∫ g, V g ∂P) - G| ≤ C / Real.sqrt ((N : ℝ) + 1) ∧
      (∫ g, (V g - G) ^ 2 ∂P) ≤ C / Real.sqrt ((N : ℝ) + 1) := by
  choose C hCpos hCs using fun f : K → M => sk_T_enumerated_gibbs_moments_uniform
    β₀ hβ₀ (fun j => S j (f j)) (fun j => a j (f j)) (fun j => b j (f j))
      (fun j => hord j (f j))
  let c : (K → M) → ℝ := fun f => ∏ j, γ j (f j)
  let CM : ℝ := ∑ f, |c f| * C f
  let CS : ℝ := (Fintype.card (K → M) : ℝ) * ∑ f, c f ^ 2 * C f
  have hCM : 0 ≤ CM := sum_nonneg fun f _ => mul_nonneg (abs_nonneg _) (hCpos f).le
  have hCS : 0 ≤ CS := mul_nonneg (Nat.cast_nonneg _)
    (sum_nonneg fun f _ => mul_nonneg (sq_nonneg _) (hCpos f).le)
  refine ⟨CM + CS + 1, by positivity, fun β h q hfix hb N => ?_⟩
  intro E bmean T V qh α A2 B2 G P
  let I := K → M
  let D := (R × R) ⊕ R
  let Q := Measure.pi fun _ : D => gaussianReal 0 1
  let σ : D → ℝ := Sum.elim (fun _ => Real.sqrt A2) (fun _ => Real.sqrt B2)
  let Z := fun j m (z : D → ℝ) =>
    if S j m then Real.sqrt A2 * z (.inl (a j m, b j m))
      else Real.sqrt B2 * z (.inr (a j m))
  let X := fun (f : I) g => ((N : ℝ) + 1) ^ ((Fintype.card K : ℝ) / 2) *
    ∫ ρ : R → Fin (N + 1) → ℤˣ, ∏ j, T j (f j) g ρ
      ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
  let Gf := fun f : I => ∫ z, ∏ j, Z j (f j) z ∂Q
  have hf (f : I) : MemLp (X f) 2 P ∧
      |(∫ g, X f g ∂P) - Gf f| ≤ C f / Real.sqrt ((N : ℝ) + 1) ∧
      (∫ g, (X f g - Gf f) ^ 2 ∂P) ≤ C f / Real.sqrt ((N : ℝ) + 1) :=
    hCs f β h q hfix hb N
  have hV : V = fun g => ∑ f : I, c f * X f g := by
    funext g
    have he (ρ : R → Fin (N + 1) → ℤˣ) :
        (∏ j, ∑ m, γ j m * T j m g ρ) =
          ∑ f : I, c f * ∏ j, T j (f j) g ρ := by
      rw [prod_univ_sum (fun _ => univ), Fintype.piFinset_univ]
      exact sum_congr rfl fun f _ => prod_mul_distrib
    dsimp only [V]
    simp_rw [he]
    rw [integral_finsetSum _ fun _ _ => Integrable.of_finite, mul_sum]
    apply sum_congr rfl
    intro f _
    rw [integral_const_mul]
    dsimp only [X]
    ring
  have hGi (f : I) : Integrable (fun z : D → ℝ => ∏ j, Z j (f j) z) Q := by
    let d : K → D := fun j =>
      if S j (f j) then .inl (a j (f j), b j (f j)) else .inr (a j (f j))
    let n : D → ℕ := fun κ => (univ.filter fun j => d j = κ).card
    have he (z : D → ℝ) : (∏ j, Z j (f j) z) = ∏ κ, (σ κ * z κ) ^ n κ := by
      have hh := (prod_fiberwise' (univ : Finset K) d (fun κ => σ κ * z κ)).symm
      simp only [prod_const] at hh
      rw [← hh]
      apply prod_congr rfl
      intro j _
      cases hs : S j (f j) <;> simp [Z, d, σ, hs]
    simp_rw [he]
    apply Integrable.fintype_prod
    intro κ
    simpa only [mul_pow] using (integrable_pow_gaussianReal 0 1 (n κ)).const_mul (σ κ ^ n κ)
  have hG : G = ∑ f : I, c f * Gf f := by
    have he (z : D → ℝ) : (∏ j, ∑ m, γ j m * Z j m z) =
        ∑ f : I, c f * ∏ j, Z j (f j) z := by
      rw [prod_univ_sum (fun _ => univ), Fintype.piFinset_univ]
      exact sum_congr rfl fun f _ => prod_mul_distrib
    change (∫ z, ∏ j, ∑ m, γ j m * Z j m z ∂Q) = _
    simp_rw [he]
    rw [integral_finsetSum _ fun f _ => (hGi f).const_mul _]
    simp only [integral_const_mul, Gf]
  have hX : MemLp V 2 P := by
    rw [hV]
    exact memLp_finsetSum univ fun f _ => (hf f).1.const_mul _
  have hY (f : I) : MemLp (fun g => c f * (X f g - Gf f)) 2 P :=
    ((hf f).1.sub (memLp_const _)).const_mul _
  have hsub (g : FinPairs (N + 1) → ℝ) :
      V g - G = ∑ f : I, c f * (X f g - Gf f) := by
    rw [hV, hG, ← sum_sub_distrib]
    exact sum_congr rfl fun _ _ => (mul_sub _ _ _).symm
  have hmean : |(∫ g, V g ∂P) - G| ≤ CM / Real.sqrt ((N : ℝ) + 1) := by
    rw [hV, hG, integral_finsetSum _ fun f _ => ((hf f).1.integrable one_le_two).const_mul _]
    simp_rw [integral_const_mul]
    rw [← sum_sub_distrib]
    simp_rw [← mul_sub]
    calc
      |∑ f : I, c f * ((∫ g, X f g ∂P) - Gf f)| ≤
          ∑ f : I, |c f| * |(∫ g, X f g ∂P) - Gf f| := by
        simpa only [abs_mul] using abs_sum_le_sum_abs _ _
      _ ≤ ∑ f : I, |c f| * (C f / Real.sqrt ((N : ℝ) + 1)) :=
        sum_le_sum fun f _ => mul_le_mul_of_nonneg_left (hf f).2.1 (abs_nonneg _)
      _ = _ := by simp only [CM, mul_div_assoc, sum_div]
  have hmse : (∫ g, (V g - G) ^ 2 ∂P) ≤ CS / Real.sqrt ((N : ℝ) + 1) := by
    simp_rw [hsub]
    refine (integral_sq_fintype_sum_le hY).trans ?_
    simp_rw [mul_pow, integral_const_mul]
    calc
      (Fintype.card I : ℝ) * ∑ f : I, c f ^ 2 * (∫ g, (X f g - Gf f) ^ 2 ∂P) ≤
          (Fintype.card I : ℝ) * ∑ f : I, c f ^ 2 *
            (C f / Real.sqrt ((N : ℝ) + 1)) := by
        gcongr with f
        exact (hf f).2.2
      _ = _ := by simp only [CS, mul_div_assoc, sum_div]
  refine ⟨hX, hmean.trans ?_, hmse.trans ?_⟩
  · exact div_le_div_of_nonneg_right (by dsimp only [CM, CS] at hCM hCS ⊢; linarith)
      (Real.sqrt_nonneg _)
  · exact div_le_div_of_nonneg_right (by dsimp only [CM, CS] at hCM hCS ⊢; linarith)
      (Real.sqrt_nonneg _)

end SpinGlasses
