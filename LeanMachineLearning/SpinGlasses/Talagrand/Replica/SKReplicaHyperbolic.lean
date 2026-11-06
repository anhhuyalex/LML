/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The hyperbolic Cauchy-Schwarz inequality (Talagrand, Lemma 1.13.4)

`ch a₁ ch a₂ ch g + sh a₁ sh a₂ sh g ≤ (ch² a₁ ch|g| + sh² a₁ sh|g|)^{1/2}
(ch² a₂ ch|g| + sh² a₂ sh|g|)^{1/2}`, with equality only for `a₁ = a₂` (if `g > 0`) or
`a₁ = -a₂` (if `g < 0`).
-/

@[expose] public section

open Real

namespace SpinGlasses

theorem sinh_abs_eq_abs_sinh (g : ℝ) : sinh |g| = |sinh g| := by
  rcases le_total 0 g with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (Real.sinh_nonneg_iff.2 h)]
  · rw [abs_of_nonpos h, Real.sinh_neg, abs_of_nonpos (Real.sinh_nonpos_iff.2 h)]

/-- The defect of the hyperbolic Cauchy-Schwarz inequality, as a quadratic form. -/
theorem hyp_cs_defect (a₁ a₂ g : ℝ) :
    (cosh a₁ ^ 2 * cosh |g| + sinh a₁ ^ 2 * sinh |g|) *
        (cosh a₂ ^ 2 * cosh |g| + sinh a₂ ^ 2 * sinh |g|) -
      (cosh a₁ * cosh a₂ * cosh g + sinh a₁ * sinh a₂ * sinh g) ^ 2 =
    cosh g * (|sinh g| * ((cosh a₁ * sinh a₂) ^ 2 + (sinh a₁ * cosh a₂) ^ 2) -
      2 * sinh g * (cosh a₁ * sinh a₂) * (sinh a₁ * cosh a₂)) := by
  rw [Real.cosh_abs, sinh_abs_eq_abs_sinh]
  have h : sinh g ^ 2 = |sinh g| ^ 2 := (sq_abs _).symm
  linear_combination (sinh a₁ ^ 2 * sinh a₂ ^ 2) * (-h)

theorem hyp_cs_defect_nonneg (a₁ a₂ g : ℝ) :
    0 ≤ |sinh g| * ((cosh a₁ * sinh a₂) ^ 2 + (sinh a₁ * cosh a₂) ^ 2) -
      2 * sinh g * (cosh a₁ * sinh a₂) * (sinh a₁ * cosh a₂) := by
  set x := cosh a₁ * sinh a₂
  set y := sinh a₁ * cosh a₂
  have h1 : sinh g * (x * y) ≤ |sinh g| * |x * y| := by
    calc sinh g * (x * y) ≤ |sinh g * (x * y)| := le_abs_self _
      _ = |sinh g| * |x * y| := abs_mul _ _
  have h2 : 2 * |x * y| ≤ x ^ 2 + y ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
  nlinarith [abs_nonneg (sinh g)]

/-- **Talagrand's Lemma 1.13.4**, inequality (1.400). -/
theorem hyp_cs_le (a₁ a₂ g : ℝ) :
    cosh a₁ * cosh a₂ * cosh g + sinh a₁ * sinh a₂ * sinh g ≤
      √(cosh a₁ ^ 2 * cosh |g| + sinh a₁ ^ 2 * sinh |g|) *
        √(cosh a₂ ^ 2 * cosh |g| + sinh a₂ ^ 2 * sinh |g|) := by
  have hQ1 : 0 ≤ cosh a₁ ^ 2 * cosh |g| + sinh a₁ ^ 2 * sinh |g| := by
    have : 0 ≤ sinh |g| := Real.sinh_nonneg_iff.2 (abs_nonneg g)
    positivity
  rw [← Real.sqrt_mul hQ1]
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  have := hyp_cs_defect a₁ a₂ g
  have h2 : 0 ≤ cosh g * (|sinh g| * ((cosh a₁ * sinh a₂) ^ 2 + (sinh a₁ * cosh a₂) ^ 2) -
      2 * sinh g * (cosh a₁ * sinh a₂) * (sinh a₁ * cosh a₂)) :=
    mul_nonneg (Real.cosh_pos g).le (hyp_cs_defect_nonneg a₁ a₂ g)
  linarith

/-- **Talagrand's Lemma 1.13.4**, equality case: if (1.400) is an equality and `g ≠ 0`, then
`a₁ = a₂` for `g > 0` and `a₁ = -a₂` for `g < 0`. -/
theorem hyp_cs_eq (a₁ a₂ g : ℝ)
    (heq : cosh a₁ * cosh a₂ * cosh g + sinh a₁ * sinh a₂ * sinh g =
      √(cosh a₁ ^ 2 * cosh |g| + sinh a₁ ^ 2 * sinh |g|) *
        √(cosh a₂ ^ 2 * cosh |g| + sinh a₂ ^ 2 * sinh |g|)) :
    (0 < g → a₁ = a₂) ∧ (g < 0 → a₁ = -a₂) := by
  have hQ1 : 0 ≤ cosh a₁ ^ 2 * cosh |g| + sinh a₁ ^ 2 * sinh |g| := by
    have : 0 ≤ sinh |g| := Real.sinh_nonneg_iff.2 (abs_nonneg g)
    positivity
  have hQ2 : 0 ≤ cosh a₂ ^ 2 * cosh |g| + sinh a₂ ^ 2 * sinh |g| := by
    have : 0 ≤ sinh |g| := Real.sinh_nonneg_iff.2 (abs_nonneg g)
    positivity
  have hsq : (cosh a₁ * cosh a₂ * cosh g + sinh a₁ * sinh a₂ * sinh g) ^ 2 =
      (cosh a₁ ^ 2 * cosh |g| + sinh a₁ ^ 2 * sinh |g|) *
        (cosh a₂ ^ 2 * cosh |g| + sinh a₂ ^ 2 * sinh |g|) := by
    rw [heq, mul_pow, Real.sq_sqrt hQ1, Real.sq_sqrt hQ2]
  have hdef := hyp_cs_defect a₁ a₂ g
  rw [hsq, sub_self] at hdef
  have hu := Real.cosh_pos g
  have h0 : |sinh g| * ((cosh a₁ * sinh a₂) ^ 2 + (sinh a₁ * cosh a₂) ^ 2) -
      2 * sinh g * (cosh a₁ * sinh a₂) * (sinh a₁ * cosh a₂) = 0 := by
    rcases mul_eq_zero.1 hdef.symm with h | h
    · exact absurd h hu.ne'
    · exact h
  constructor
  · intro hg
    have hs : 0 < sinh g := Real.sinh_pos_iff.2 hg
    rw [abs_of_pos hs] at h0
    have h1 : sinh g * (cosh a₁ * sinh a₂ - sinh a₁ * cosh a₂) ^ 2 = 0 := by
      linear_combination h0
    have h2 : cosh a₁ * sinh a₂ - sinh a₁ * cosh a₂ = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h hs.ne'
      · exact pow_eq_zero_iff (two_ne_zero) |>.1 h
    have : sinh (a₂ - a₁) = 0 := by
      rw [Real.sinh_sub]
      linarith
    exact (sub_eq_zero.1 (Real.sinh_eq_zero.1 this)).symm
  · intro hg
    have hs : sinh g < 0 := Real.sinh_neg_iff.2 hg
    rw [abs_of_neg hs] at h0
    have h1 : (-sinh g) * (cosh a₁ * sinh a₂ + sinh a₁ * cosh a₂) ^ 2 = 0 := by
      linear_combination h0
    have h2 : cosh a₁ * sinh a₂ + sinh a₁ * cosh a₂ = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h (neg_ne_zero.2 hs.ne)
      · exact pow_eq_zero_iff (two_ne_zero) |>.1 h
    have : sinh (a₁ + a₂) = 0 := by
      rw [Real.sinh_add]
      linarith
    exact eq_neg_of_add_eq_zero_left (Real.sinh_eq_zero.1 this)

theorem sqrt_mul_sqrt_mul_eq' {w : ℝ} (hw : 0 ≤ w) (b₁ b₂ : ℝ) :
    √(w * b₁) * √(w * b₂) = w * (√b₁ * √b₂) := by
  rw [Real.sqrt_mul hw, Real.sqrt_mul hw]
  calc √w * √b₁ * (√w * √b₂) = (√w * √w) * (√b₁ * √b₂) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hw]

/-- Weighted sums: the inequality (1.407) with the Cauchy-Schwarz step that follows it. -/
theorem hyp_sum_cs_le {S : Type*} [Fintype S] (w : S → ℝ) (hw : ∀ s, 0 < w s)
    (a₁ a₂ : S → ℝ) (γ : ℝ) :
    ∑ s, w s * (cosh (a₁ s) * cosh (a₂ s) * cosh γ + sinh (a₁ s) * sinh (a₂ s) * sinh γ) ≤
      √(∑ s, w s * (cosh (a₁ s) ^ 2 * cosh |γ| + sinh (a₁ s) ^ 2 * sinh |γ|)) *
        √(∑ s, w s * (cosh (a₂ s) ^ 2 * cosh |γ| + sinh (a₂ s) ^ 2 * sinh |γ|)) := by
  have hB (a : ℝ) : 0 ≤ cosh a ^ 2 * cosh |γ| + sinh a ^ 2 * sinh |γ| := by
    have : 0 ≤ sinh |γ| := Real.sinh_nonneg_iff.2 (abs_nonneg γ)
    positivity
  calc _ ≤ ∑ s, √(w s * (cosh (a₁ s) ^ 2 * cosh |γ| + sinh (a₁ s) ^ 2 * sinh |γ|)) *
        √(w s * (cosh (a₂ s) ^ 2 * cosh |γ| + sinh (a₂ s) ^ 2 * sinh |γ|)) := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [sqrt_mul_sqrt_mul_eq' (hw s).le]
        exact mul_le_mul_of_nonneg_left (hyp_cs_le _ _ _) (hw s).le
    _ ≤ _ := Real.sum_sqrt_mul_sqrt_le _
        (fun s => mul_nonneg (hw s).le (hB _)) (fun s => mul_nonneg (hw s).le (hB _))

/-- Weighted sums, equality case: if the weighted hyperbolic Cauchy-Schwarz inequality is an
equality and `γ ≠ 0`, then `a₁ = a₂` for `γ > 0` and `a₁ = -a₂` for `γ < 0`, at every point. -/
theorem hyp_sum_cs_eq {S : Type*} [Fintype S] (w : S → ℝ) (hw : ∀ s, 0 < w s)
    (a₁ a₂ : S → ℝ) (γ : ℝ)
    (heq : ∑ s, w s * (cosh (a₁ s) * cosh (a₂ s) * cosh γ + sinh (a₁ s) * sinh (a₂ s) * sinh γ) =
      √(∑ s, w s * (cosh (a₁ s) ^ 2 * cosh |γ| + sinh (a₁ s) ^ 2 * sinh |γ|)) *
        √(∑ s, w s * (cosh (a₂ s) ^ 2 * cosh |γ| + sinh (a₂ s) ^ 2 * sinh |γ|))) :
    (0 < γ → ∀ s, a₁ s = a₂ s) ∧ (γ < 0 → ∀ s, a₁ s = -a₂ s) := by
  have hB (a : ℝ) : 0 ≤ cosh a ^ 2 * cosh |γ| + sinh a ^ 2 * sinh |γ| := by
    have : 0 ≤ sinh |γ| := Real.sinh_nonneg_iff.2 (abs_nonneg γ)
    positivity
  set mid : ℝ := ∑ s, w s * (√(cosh (a₁ s) ^ 2 * cosh |γ| + sinh (a₁ s) ^ 2 * sinh |γ|) *
    √(cosh (a₂ s) ^ 2 * cosh |γ| + sinh (a₂ s) ^ 2 * sinh |γ|)) with hmid
  have h1 : ∑ s, w s * (cosh (a₁ s) * cosh (a₂ s) * cosh γ +
      sinh (a₁ s) * sinh (a₂ s) * sinh γ) ≤ mid :=
    Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hyp_cs_le _ _ _) (hw s).le
  have h2 : mid ≤ √(∑ s, w s * (cosh (a₁ s) ^ 2 * cosh |γ| + sinh (a₁ s) ^ 2 * sinh |γ|)) *
        √(∑ s, w s * (cosh (a₂ s) ^ 2 * cosh |γ| + sinh (a₂ s) ^ 2 * sinh |γ|)) := by
    calc mid = ∑ s, √(w s * (cosh (a₁ s) ^ 2 * cosh |γ| + sinh (a₁ s) ^ 2 * sinh |γ|)) *
          √(w s * (cosh (a₂ s) ^ 2 * cosh |γ| + sinh (a₂ s) ^ 2 * sinh |γ|)) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [sqrt_mul_sqrt_mul_eq' (hw s).le]
      _ ≤ _ := Real.sum_sqrt_mul_sqrt_le _
          (fun s => mul_nonneg (hw s).le (hB _)) (fun s => mul_nonneg (hw s).le (hB _))
  have hfirst : ∑ s, w s * (cosh (a₁ s) * cosh (a₂ s) * cosh γ +
      sinh (a₁ s) * sinh (a₂ s) * sinh γ) = mid := le_antisymm h1 (heq ▸ h2)
  have hterm : ∀ s, w s * (cosh (a₁ s) * cosh (a₂ s) * cosh γ +
      sinh (a₁ s) * sinh (a₂ s) * sinh γ) = w s * (√(cosh (a₁ s) ^ 2 * cosh |γ| +
        sinh (a₁ s) ^ 2 * sinh |γ|) * √(cosh (a₂ s) ^ 2 * cosh |γ| +
        sinh (a₂ s) ^ 2 * sinh |γ|)) :=
    (Finset.sum_eq_sum_iff_of_le fun s _ =>
      mul_le_mul_of_nonneg_left (hyp_cs_le _ _ _) (hw s).le).1 hfirst |>
      fun h s => h s (Finset.mem_univ s)
  have hpt : ∀ s, cosh (a₁ s) * cosh (a₂ s) * cosh γ + sinh (a₁ s) * sinh (a₂ s) * sinh γ =
      √(cosh (a₁ s) ^ 2 * cosh |γ| + sinh (a₁ s) ^ 2 * sinh |γ|) *
        √(cosh (a₂ s) ^ 2 * cosh |γ| + sinh (a₂ s) ^ 2 * sinh |γ|) :=
    fun s => mul_left_cancel₀ (hw s).ne' (hterm s)
  exact ⟨fun hγ s => (hyp_cs_eq _ _ _ (hpt s)).1 hγ, fun hγ s => (hyp_cs_eq _ _ _ (hpt s)).2 hγ⟩

end SpinGlasses
