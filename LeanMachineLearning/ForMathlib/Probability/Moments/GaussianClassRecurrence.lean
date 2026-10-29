/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.FiniteRecurrence
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianStein

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
  obtain ⟨k, rfl⟩ := hm
  induction k with
  | zero =>
    simp only [mul_zero, zero_add, pow_one]
    rw [integral_const_mul, integral_id_gaussianReal, mul_zero]
  | succ k ih =>
    have e : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    rw [e, integral_pow_add_two_scaled_gaussianReal, ih, mul_zero]

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
  classical
  let cls : Finset J → J → Finset J := fun s p => s.filter fun j => P j ∧ label j = label p
  let u₀ : Finset J → J → J := fun s p =>
    if h : (cls s p).erase p |>.Nonempty then h.choose else p
  have hu₀ : ∀ s p, ((cls s p).erase p).Nonempty → u₀ s p ∈ (cls s p).erase p := fun s p h => by
    simp only [u₀, dite_eq_left h]
    exact h.choose_spec
  let f : Θ → ℕ → ℕ → ℝ := fun θ N n =>
    ∫ x : ℝ, (Real.sqrt (c θ / (N + 1 : ℝ)) * x) ^ n ∂(gaussianReal 0 1)
  let G : Θ → ℕ → Finset J → ℝ := fun θ N s =>
    (∏ k : ι, f θ N (s.filter fun j => P j ∧ label j = k).card) *
      F θ N (s.filter fun j => ¬P j)
  refine ProbabilityTheory.exists_finset_moment_error_of_two_factor_recurrence P valid F G c B hc
    (fun s p => (s.erase p).erase (u₀ s p)) (fun s p => (((cls s p).card - 1 : ℕ) : ℝ))
    ?_ ?_ ?_ ?_
  · intro s p hp hP
    by_cases hne : ((cls s p).erase p).Nonempty
    · right
      have hu := hu₀ s p hne
      have hus : u₀ s p ∈ s.erase p :=
        Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hu).1,
          (Finset.mem_filter.mp (Finset.mem_erase.mp hu).2).1⟩
      rw [Finset.card_erase_of_mem hus, Finset.card_erase_of_mem hp]
      have := Finset.card_pos.mpr (⟨p, hp⟩ : s.Nonempty)
      have h2 := Finset.card_pos.mpr (⟨u₀ s p, hus⟩ : (s.erase p).Nonempty)
      rw [Finset.card_erase_of_mem hp] at h2
      omega
    · left
      have he : (cls s p).erase p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hpc : p ∈ cls s p := Finset.mem_filter.mpr ⟨hp, hP, rfl⟩
      have h1 := Finset.card_erase_add_one hpc
      rw [he, Finset.card_empty] at h1
      have : (cls s p).card - 1 = 0 := by omega
      simp only [this, Nat.cast_zero]
  · intro s hs θ _ N
    have hfilt : (s.filter fun j => ¬P j) = s := Finset.filter_true_of_mem hs
    have hz : ∀ k, (s.filter fun j => P j ∧ label j = k) = ∅ := fun k =>
      Finset.filter_false_of_mem fun j hj h => hs j hj h.1
    simp only [G, f, hfilt, hz, Finset.card_empty, pow_zero, integral_const, probReal_univ,
      smul_eq_mul, mul_one, Finset.prod_const_one, one_mul]
  · intro s p hps hP θ hθ N
    have hz0 := hc0 θ hθ
    have hzN : 0 ≤ c θ / (N + 1 : ℝ) := div_nonneg hz0 (by positivity)
    have hfirst : ∀ _ : ι, f θ N 1 = 0 := fun _ => by
      simp only [f, pow_one]
      rw [integral_const_mul, integral_id_gaussianReal, mul_zero]
    have hrec : ∀ (_ : ι) (n : ℕ), f θ N (n + 2) = ((n + 1 : ℕ) : ℝ) * (c θ / (N + 1 : ℝ)) *
        f θ N n := fun _ n => by
      simp only [f]
      rw [integral_pow_add_two_scaled_gaussianReal, Real.sq_sqrt hzN]
      push_cast
      ring
    have hPu : P (u₀ s p) := by
      by_cases hne : ((cls s p).erase p).Nonempty
      · exact (Finset.mem_filter.mp (Finset.mem_erase.mp (hu₀ s p hne)).2).2.1
      · simp only [u₀, dite_eq_right hne]
        exact hP
    have key := prod_class_moments_erase_pair (A := ℝ) s (Finset.univ : Finset ι) P label
      (fun _ n => f θ N n) (fun _ => c θ / (N + 1 : ℝ)) hfirst hrec hps hP
      (Finset.mem_univ _) (hu₀ s p)
    have hfilt : ((s.erase p).erase (u₀ s p)).filter (fun j => ¬P j) =
        s.filter fun j => ¬P j := by
      rw [Finset.filter_erase, Finset.filter_erase,
        Finset.erase_eq_of_notMem (a := p) (by simp [hP]),
        Finset.erase_eq_of_notMem (a := u₀ s p) (by simp [hPu])]
    simp only [G]
    rw [key, hfilt]
    ring
  · intro s p hps hP
    have hu : ((cls s p).erase p).Nonempty → u₀ s p ∈ (cls s p).erase p := hu₀ s p
    have hmem : u₀ s p ∈ s := by
      by_cases hne : ((cls s p).erase p).Nonempty
      · exact (Finset.mem_filter.mp (Finset.mem_erase.mp (hu hne)).2).1
      · simp only [u₀, dite_eq_right hne]
        exact hps
    exact hF s p (u₀ s p) hps hP hmem hu

end ProbabilityTheory
