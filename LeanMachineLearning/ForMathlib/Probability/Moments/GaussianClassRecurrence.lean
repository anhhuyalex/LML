/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianClassMoments
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein
public import LeanMachineLearning.ForMathlib.Data.Nat.Recurrence

/-!
# Gaussian class-product reference for a two-factor moment recurrence

A family `F` of mixed moments indexed by finite sets of factors satisfies, for a selected
factor `p`, an approximate recurrence that deletes `p` and a partner `u` of the same class and
multiplies by `(class size - 1) * c / (N + 1)`. Then `F` agrees, up to the usual
`(N+1)^(-(card + 1)/2)` error, with the product of centered Gaussian moments of the class sizes
times the moment of the unselected factors. This is the common reference step of the three
inductions of Talagrand, Section 1.10 (Propositions 1.10.4, 1.10.5 and the `T` step).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ProbabilityTheory

/-- The scaled Gaussian moments satisfy the two-step recurrence `a(n+2) = (n+1) s² a(n)`. -/
theorem integral_pow_add_two_scaled_gaussianReal (s : ℝ) (n : ℕ) :
    ∫ x : ℝ, (s * x) ^ (n + 2) ∂(gaussianReal 0 1) =
      (n + 1 : ℝ) * s ^ 2 * ∫ x : ℝ, (s * x) ^ n ∂(gaussianReal 0 1) := by
  simp only [mul_pow]
  rw [integral_const_mul, integral_const_mul, integral_pow_add_two_gaussianReal]
  ring

/-- Scaled Gaussian moments of odd order vanish. -/
theorem integral_pow_scaled_gaussianReal_of_odd (s : ℝ) {m : ℕ} (hm : Odd m) :
    ∫ x : ℝ, (s * x) ^ m ∂(gaussianReal 0 1) = 0 := by
  apply Nat.eq_zero_of_odd_of_two_step_mul
    (a := fun n => ∫ x : ℝ, (s * x) ^ n ∂gaussianReal 0 1)
    (c := fun n => (n + 1 : ℝ) * s ^ 2) ?_ ?_ hm
  · simp only [pow_one]
    rw [integral_const_mul, integral_id_gaussianReal, mul_zero]
  · exact integral_pow_add_two_scaled_gaussianReal s

/-- The square-root and variance-power presentations of a Gaussian moment agree.
Odd moments vanish, so the integer division in the variance power causes no loss. -/
theorem integral_pow_sqrt_mul_gaussianReal {v : ℝ} (hv : 0 ≤ v) (n : ℕ) :
    (∫ x : ℝ, (Real.sqrt v * x) ^ n ∂gaussianReal 0 1) =
      (∫ x : ℝ, x ^ n ∂gaussianReal 0 1) * v ^ (n / 2) := by
  rcases Nat.even_or_odd n with he | ho
  · obtain ⟨k, rfl⟩ := he
    simp only [mul_pow, integral_const_mul]
    rw [show (k + k) / 2 = k by omega, show k + k = 2 * k by omega,
      pow_mul, Real.sq_sqrt hv, mul_comm]
  · rw [integral_pow_scaled_gaussianReal_of_odd _ ho]
    have hz := integral_pow_scaled_gaussianReal_of_odd (1 : ℝ) ho
    simp only [one_mul] at hz
    rw [hz, zero_mul]

/-- **Gaussian reference for a two-factor recurrence.** Let `P` select the factors that
carry a class `label`. Suppose that for every selected `p`, every partner `u` of the same
class (whenever one exists) and every parameter the moment `F s` equals
`(class size - 1) * c / (N + 1)` times `F ((s.erase p).erase u)`, up to a prescribed error.
Then, for every finite factor set `s`, `F s` is within `K / (N+1)^((card s + 1) / 2)` of the
product over classes `k` of the Gaussian moment `∫ (√(c/(N+1)) x)^(class size) dγ` times
`F` of the unselected factors. The constant `K` precedes the parameter and `N`. -/
theorem exists_gaussian_class_moment_error
    {J ι Θ : Type*} [DecidableEq J] [DecidableEq ι] [Fintype ι] (P : J → Prop) [DecidablePred P]
    (label : J → ι) (valid : Θ → Prop) (F : Θ → ℕ → Finset J → ℝ) (c : Θ → ℝ) (B : ℝ)
    (hc0 : ∀ θ, valid θ → 0 ≤ c θ) (hc : ∀ θ, valid θ → |c θ| ≤ B)
    (hF : ∀ (s : Finset J) (p u : J), p ∈ s → P p → u ∈ s →
      (((s.filter fun j => P j ∧ label j = label p).erase p).Nonempty →
        u ∈ (s.filter fun j => P j ∧ label j = label p).erase p) →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ θ, valid θ → ∀ N : ℕ,
        |F θ N s - ((((s.filter fun j => P j ∧ label j = label p).card - 1 : ℕ) : ℝ) *
          c θ / (N + 1 : ℝ)) * F θ N ((s.erase p).erase u)| ≤
          K / (N + 1 : ℝ) ^ (((s.card + 1 : ℕ) : ℝ) / 2)) :
    ∀ s : Finset J, ∃ K : ℝ, 0 < K ∧ ∀ θ, valid θ → ∀ N : ℕ,
      |F θ N s - (∏ k : ι, ∫ x : ℝ,
          (Real.sqrt (c θ / (N + 1 : ℝ)) * x) ^
            (s.filter fun j => P j ∧ label j = k).card ∂(gaussianReal 0 1)) *
        F θ N (s.filter fun j => ¬P j)| ≤
        K / (N + 1 : ℝ) ^ (((s.card + 1 : ℕ) : ℝ) / 2) := by
  let cls : Finset J → J → Finset J := fun s p => s.filter fun j => P j ∧ label j = label p
  let u₀ : Finset J → J → J := fun s p =>
    if h : (cls s p).erase p |>.Nonempty then h.choose else p
  have hu₀ : ∀ s p, ((cls s p).erase p).Nonempty → u₀ s p ∈ (cls s p).erase p := fun s p h => by
    simp only [u₀, dite_eq_left h]
    exact h.choose_spec
  have hmem : ∀ s p, p ∈ s → u₀ s p ∈ s := by
    intro s p hp
    by_cases hne : ((cls s p).erase p).Nonempty
    · exact (Finset.mem_filter.mp (Finset.mem_erase.mp (hu₀ s p hne)).2).1
    · simp only [u₀, dite_eq_right hne]
      exact hp
  intro s
  obtain ⟨K, hK0, hK⟩ := exists_finset_gaussian_class_moment_error P label valid F c B hc u₀
    (fun s p _ _ => hu₀ s p)
    (fun s p hp hP => hF s p (u₀ s p) hp hP (hmem s p hp) (hu₀ s p)) s
  refine ⟨K, hK0, fun θ hθ N => ?_⟩
  have hv : 0 ≤ c θ / (N + 1 : ℝ) := div_nonneg (hc0 θ hθ) (by positivity)
  simp_rw [integral_pow_sqrt_mul_gaussianReal hv]
  exact hK θ hθ N

end ProbabilityTheory
