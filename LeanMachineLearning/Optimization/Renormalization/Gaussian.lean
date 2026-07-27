/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Cumulant
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Wick calculus for Gaussian measures

This file defines a canonical pairing sum and states scalar, coordinate-free, and coordinate Wick
formulae.  The coordinate-free theorem is primary; the multivariate-coordinate theorem and the
sixth-moment theorem are direct specializations.

Deferred proof references:

* L. Isserlis, *On a Formula for the Product-Moment Coefficient of any Order of a Normal Frequency
  Distribution in any Number of Variables*: <https://doi.org/10.1093/biomet/12.1-2.134>.
* Mathlib's Gaussian MGF and `IsGaussian` API:
  <https://github.com/leanprover-community/mathlib4/tree/abb22825db7e020c94f38a007ae3fffe6c3a7532/Mathlib/Probability/Distributions/Gaussian>.

Every deferred theorem below includes its own informal proof.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Renormalization

variable {ι : Type*} [DecidableEq ι]

/-- The canonical weight of an unordered two-element block for a covariance kernel.  Averaging the
two orientations avoids choosing an order on the index type. -/
def pairWeight (C : ι → ι → ℝ) (B : Finset ι) : ℝ :=
  (∑ i ∈ B, ∑ j ∈ B.erase i, C i j) / 2

/-- The Wick sum of a covariance kernel over all pairings of `s`. -/
def wick (C : ι → ι → ℝ) (s : Finset ι) : ℝ :=
  Finpartition.pairingSum (pairWeight C) s

/-- A Wick sum on an odd-cardinality set vanishes.

Informal proof: `Finpartition.Pairing.isEmpty_of_odd_card` says the indexing type of the sum is
empty, so the finite sum is zero. -/
theorem wick_eq_zero_of_odd_card (C : ι → ι → ℝ) (s : Finset ι) (hs : Odd s.card) :
    wick C s = 0 := by
  haveI h : IsEmpty (Finpartition.Pairing s) := Finpartition.Pairing.isEmpty_of_odd_card hs
  unfold wick Finpartition.pairingSum
  apply Fintype.sum_empty

/-- The canonical block weight of a two-element set is the covariance of its elements.

Informal proof:
By definition, `pairWeight C {a, b} = (∑ i ∈ {a, b}, ∑ j ∈ {a, b} \ {i}, C i j) / 2`.
When `a ≠ b`, the outer sum has two terms: `i = a` and `i = b`.
For `i = a`, the inner sum is over `{b}`, yielding `C a b`.
For `i = b`, the inner sum is over `{a}`, yielding `C b a`.
Summing these gives `(C a b + C b a) / 2`. Since `C` is symmetric (`hC`), this is `C a b`.
(Source: Covariance matrix, Wikipedia, https://en.wikipedia.org/wiki/Covariance_matrix) -/
theorem pairWeight_pair (C : ι → ι → ℝ) (hC : ∀ i j, C i j = C j i) {a b : ι} (hab : a ≠ b) :
    pairWeight C {a, b} = C a b := by
  unfold pairWeight
  rw [Finset.sum_pair hab]
  have h1 : ({a, b} : Finset ι).erase a = {b} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxa, hx⟩
      cases hx with
      | inl h => exact False.elim (hxa h)
      | inr h => exact h
    · rintro hxb
      subst hxb
      exact ⟨hab.symm, Or.inr rfl⟩
  have h2 : ({a, b} : Finset ι).erase b = {a} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxb, hx⟩
      cases hx with
      | inl h => exact h
      | inr h => exact False.elim (hxb h)
    · rintro hxa
      subst hxa
      exact ⟨hab, Or.inl rfl⟩
  rw [h1, h2]
  rw [Finset.sum_singleton, Finset.sum_singleton]
  rw [hC b a]
  ring

/-- Pairing recurrence obtained by choosing the partner of a distinguished element.

Informal proof:
For a non-empty set `s` containing a distinguished element `a`, any perfect matching (pairing)
of `s` must pair `a` with a unique partner `b ∈ s \ {a}`. Thus, the set of pairings of `s` is
partitioned by the choice of `b`. For a fixed `b`, the remaining pairings are exactly the pairings
of `s \ {a, b}`. Since the weight of a pairing is the product of covariances and the covariance
`C(a, b)` is symmetric (by `hC`), we can factor out `C a b` and sum over all choices of `b`.
This yields the recurrence relation.
This is the standard recursive proof of Isserlis' theorem. (Source: Wick's Theorem, nLab, https://ncatlab.org/nlab/show/Wick%27s+theorem) -/
theorem wick_erase (C : ι → ι → ℝ) (hC : ∀ i j, C i j = C j i)
    (s : Finset ι) {a : ι} (ha : a ∈ s) :
    wick C s = ∑ b ∈ s.erase a, C a b * wick C ((s.erase a).erase b) := by
  unfold wick
  rw [Finpartition.pairingSum_erase (pairWeight C) s ha]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mem_erase] at hb
  have h_pair := pairWeight_pair C hC hb.1.symm
  rw [h_pair]

/-- The moment of a centered real Gaussian is given by the derivative of its MGF at zero.
Informal proof:
Apply `ProbabilityTheory.iteratedDeriv_mgf_zero`.
The MGF of a centered Gaussian `mgf (gaussianReal 0 v) t` is `exp(v t² / 2)`
by `mgf_fun_id_gaussianReal`.
(Source: Wikipedia, https://en.wikipedia.org/wiki/Moment-generating_function) -/
theorem moment_eq_iteratedDeriv_mgf (v : ℝ≥0) (k : ℕ) :
    ∫ x, x ^ k ∂gaussianReal 0 v = iteratedDeriv k (fun t => Real.exp (v * t ^ 2 / 2)) 0 := by
  have h_mgf : mgf (fun x ↦ x) (gaussianReal 0 v) = fun t => Real.exp (v * t ^ 2 / 2) := by
    ext t
    rw [mgf_fun_id_gaussianReal]
    simp
  rw [← h_mgf]
  rw [iteratedDeriv_mgf_zero]
  · simp
  · simp

/-- The odd derivatives of `exp(v t² / 2)` evaluated at zero vanish.
Informal proof:
`exp(v t² / 2)` is an even function. The derivative of an even function is an odd function,
and the derivative of an odd function is an even function. Therefore, the odd-order derivatives
are odd functions, which must be zero at `t = 0`.
(Source: Even and odd functions, Wikipedia, https://en.wikipedia.org/wiki/Even_and_odd_functions#Derivatives) -/
theorem iteratedDeriv_exp_quadratic_zero_odd (v : ℝ) (m : ℕ) :
    iteratedDeriv (2 * m + 1) (fun t => Real.exp (v * t ^ 2 / 2)) 0 = 0 := by
  -- Let `f(t) = exp (v * t^2 / 2)` and `n = 2*m+1`.
  let f : ℝ → ℝ := fun t => Real.exp (v * t ^ 2 / 2)
  let n : ℕ := 2 * m + 1

  -- The function is even: composing it with negation does not change it.
  have heven : (fun x : ℝ => f (-x)) = f := by
    funext x
    simp [f]

  -- Mathlib's chain rule for iterated derivatives under `x ↦ -x` gives
  -- `D = (-1)^n D` at zero, after using evenness and `-0 = 0`.
  have hcomp := iteratedDeriv_comp_neg n f (0 : ℝ)
  have hD : iteratedDeriv n f 0 = (-1 : ℝ) ^ n * iteratedDeriv n f 0 := by
    simpa [heven] using hcomp

  -- Since `n = 2*m+1` is odd, `(-1)^n = -1`.
  have hpow : (-1 : ℝ) ^ n = -1 := by
    have hnodd : Odd n := by
      dsimp [n]
      exact odd_two_mul_add_one m
    simpa using (Odd.neg_one_pow (α := ℝ) hnodd)

  -- Therefore `D = -D`, hence `D = 0` over the reals.
  have hDneg : iteratedDeriv n f 0 = -iteratedDeriv n f 0 := by
    simpa [hpow] using hD
  have hzero : iteratedDeriv n f 0 = 0 := by
    linarith

  simpa [f, n] using hzero

/-- The even derivatives of `exp(v t² / 2)` evaluated at zero give the expected coefficients.
Informal proof:
The Taylor series expansion of `exp(v t² / 2)` is `∑_{m=0}^∞ v^m t^{2m} / (2^m m!)`.
By Taylor's theorem, the `2m`-th derivative at zero is `(2m)!` times the coefficient of `t^{2m}`
in the Taylor series, which is `(2m)! / (2^m m!) * v^m`.
(Source: Taylor series, Wikipedia, https://en.wikipedia.org/wiki/Taylor_series) -/
theorem iteratedDeriv_exp_quadratic_zero_even (v : ℝ) (m : ℕ) :
    iteratedDeriv (2 * m) (fun t => Real.exp (v * t ^ 2 / 2)) 0 =
      ((2 * m).factorial : ℝ) / ((2 : ℝ) ^ m * (m.factorial : ℝ)) * (v : ℝ) ^ m := by
  -- Let `f(t) = exp (v * t^2 / 2)`.  The key analytic step is the
  -- differential equation `f' = (fun t ↦ v * t * f t)`.  Applying the
  -- iterated Leibniz rule to `v * t * f t` and evaluating at `0` leaves
  -- only the term where the linear factor `t` is differentiated once.
  -- This gives the two-step recurrence for the Taylor coefficients.
  have h_recurrence : ∀ n : ℕ,
      iteratedDeriv (n + 2) (fun t => Real.exp (v * t ^ 2 / 2)) 0 =
        ((n + 1 : ℕ) : ℝ) * v *
          iteratedDeriv n (fun t => Real.exp (v * t ^ 2 / 2)) 0 := by
    intro n
    -- Proof sketch:
    -- 1. Prove `deriv (fun t ↦ Real.exp (v * t^2 / 2)) t =
    --      v * t * Real.exp (v * t^2 / 2)` by the chain rule.
    -- 2. Rewrite `iteratedDeriv (n+2) f 0` as the `n+1`-st iterated
    --    derivative of `fun t ↦ v * t * f t` at zero using
    --    `iteratedDeriv_succ`.
    -- 3. Use `iteratedDeriv_mul`; derivatives of `t` at zero vanish
    --    except in order one, yielding exactly `(n+1) * v * D_n`.
    sorry

  -- Base coefficient: the zeroth derivative is just the value at zero.
  have h_base :
      iteratedDeriv 0 (fun t => Real.exp (v * t ^ 2 / 2)) 0 = 1 := by
    simp

  -- Induct on `m`, using the recurrence at `n = 2*m`.
  have h_closed : ∀ m : ℕ,
      iteratedDeriv (2 * m) (fun t => Real.exp (v * t ^ 2 / 2)) 0 =
        ((2 * m).factorial : ℝ) / ((2 : ℝ) ^ m * (m.factorial : ℝ)) *
          (v : ℝ) ^ m := by
    intro m
    induction m with
    | zero =>
        -- Here the right hand side simplifies to `1`.
        simpa using h_base
    | succ m ih =>
        -- The recurrence turns the `(2*(m+1))`-st derivative into
        -- `(2*m+1) * v` times the `(2*m)`-th derivative.
        have h_step := h_recurrence (2 * m)
        -- The remaining work is factorial arithmetic:
        -- `(2*m+2)! / (2^(m+1) * (m+1)!)`
        -- equals `(2*m+1) * ((2*m)! / (2^m * m!))`.
        -- Substitute `ih` into `h_step` and finish with `ring_nf`,
        -- `norm_num`, and the identities for `Nat.factorial_succ`.
        sorry

  exact h_closed m

/-- Odd moments of a centered real Gaussian vanish.

Informal proof:
The moment-generating function (MGF) of a centered real Gaussian with variance `v`
is `M(t) = exp(v t² / 2)`.
`mgf_fun_id_gaussianReal` identifies the MGF with `exp(v t² / 2)`.
The `n`-th moment is given by the `n`-th derivative of the MGF evaluated at `t = 0`.
Since `exp(v t² / 2)` is an even function, all of its odd derivatives vanish at zero.
`iteratedDeriv_mgf_zero` identifies those coefficients with the moments.
(Source: Moment-generating function of the normal distribution, Wikipedia,
https://en.wikipedia.org/wiki/Normal_distribution#Moments) -/
theorem integral_pow_gaussianReal_odd (v : ℝ≥0) (m : ℕ) :
    ∫ x, x ^ (2 * m + 1) ∂gaussianReal 0 v = 0 := by
  rw [moment_eq_iteratedDeriv_mgf v (2 * m + 1)]
  apply iteratedDeriv_exp_quadratic_zero_odd

/-- Exact even moments of a centered real Gaussian.

Informal proof:
The MGF of a centered real Gaussian with variance `v` is `M(t) = exp(v t² / 2)`.
Its Taylor series expansion is `∑_{m=0}^∞ (v t² / 2)^m / m! = ∑_{m=0}^∞ v^m t^{2m} / (2^m m!)`.
The `2m`-th moment is given by the `2m`-th derivative evaluated at `t = 0`.
By Taylor's theorem, this derivative gives `(2m)!` times the coefficient of `t^{2m}` in the
Taylor series, which is `(2m)! / (2^m m!) * v^m`.
We can use `iteratedDeriv_mgf_zero` to relate the moment to the iterated derivative, and
differentiate `exp(v t² / 2)` recursively or match coefficients to find the exact value.
(Source: Moment-generating function of the normal distribution, Wikipedia,
https://en.wikipedia.org/wiki/Normal_distribution#Moments) -/
theorem integral_pow_gaussianReal_even (v : ℝ≥0) (m : ℕ) :
    ∫ x, x ^ (2 * m) ∂gaussianReal 0 v =
      ((2 * m).factorial : ℝ) / ((2 : ℝ) ^ m * (m.factorial : ℝ)) * (v : ℝ) ^ m := by
  rw [moment_eq_iteratedDeriv_mgf v (2 * m)]
  apply iteratedDeriv_exp_quadratic_zero_even

/-! ## Coordinate-free Wick theorem -/

/-- Stein's lemma in 1D for polynomials.
Informal proof:
For a 1D real Gaussian measure with mean 0 and variance `v`, the expectation of `x * x^n` is given by integration by parts.
Specifically, `∫ x, x * x^n dN(0, v) = ∫ x, x^(n+1) dN(0, v) = v * n * ∫ x, x^(n-1) dN(0, v)`.
This follows directly from `integral_pow_gaussianReal_even` and `integral_pow_gaussianReal_odd`.
(Source: Stein's lemma, Wikipedia, https://en.wikipedia.org/wiki/Stein%27s_lemma) -/
theorem integral_mul_pow_gaussianReal (v : ℝ≥0) (n : ℕ) :
    ∫ x, x * x ^ n ∂gaussianReal 0 v = (v : ℝ) * (n : ℝ) * ∫ x, x ^ (n - 1) ∂gaussianReal 0 v := by
  sorry

/-- Center a continuous linear functional under `μ`. -/
def centeredDual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (μ : Measure E) (L : StrongDual ℝ E) : E → ℝ :=
  fun x ↦ L x - ∫ y, L y ∂μ

/-- Covariance kernel of two continuous linear functionals. -/
def dualCovariance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) (L K : StrongDual ℝ E) : ℝ :=
  covariance (fun x ↦ L x) (fun x ↦ K x) μ

namespace IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Stein's Lemma (Integration by parts) for Gaussian measures.
Informal proof:
For a centered Gaussian measure `μ` on `E` and a continuous linear functional `L`,
the expectation of `L(x) * F(x)` is given by the sum over `i` of the covariance of `L` and `x_i`
times the expectation of the partial derivative of `F` with respect to `x_i`.
In a coordinate-free setting, if `F` is a product of linear functionals `K_j`, the derivative of
`F` in the direction of the covariance `Cov(L, -)` yields `∑_j Cov(L, K_j) ∏_{k ≠ j} K_k(x)`.
Integrating this identity gives:
`∫ x, L(x) * ∏ K_j(x) dμ = ∑_j Cov(L, K_j) ∫ x, ∏_{k ≠ j} K_k(x) dμ`.
(Source: Stein's lemma, Wikipedia, https://en.wikipedia.org/wiki/Stein%27s_lemma) -/
theorem integral_mul_prod_centered_dual_eq_sum (μ : Measure E) [ProbabilityTheory.IsGaussian μ]
    {n : ℕ} (L : StrongDual ℝ E) (K : Fin n → StrongDual ℝ E) :
    ∫ x, centeredDual μ L x * ∏ i, centeredDual μ (K i) x ∂μ =
      ∑ j, dualCovariance μ L (K j) *
        ∫ x, ∏ i ∈ Finset.univ.erase j, centeredDual μ (K i) x ∂μ := by
  sorry

/-- Coordinate-free Wick theorem for centered continuous linear observables.

Informal proof:
For centered continuous linear observables `L i` of a Gaussian measure `μ`, any linear combination
`L = ∑_i t_i L_i` is a one-dimensional centered Gaussian variable. By considering the MGF of this
combination, which is `exp(1/2 Cov(L, L))`, the multivariate Taylor coefficients match the Wick
expansion.
Specifically, every linear combination `∑_i t_i L_i` has a one-dimensional Gaussian pushforward by
`ProbabilityTheory.IsGaussian.map_eq_gaussianReal`. Its centered MGF is therefore the exponential
of the quadratic covariance form.
Comparing finite multivariate coefficients (using the scalar exact moments) and applying
`wick_erase` yields the pairing recurrence and hence the formula. Alternatively, this can
be proved using Gaussian integration by parts (Stein's lemma).
All products are integrable by `ProbabilityTheory.IsGaussian.memLp_dual` and finite Hölder.
(Source: Wick's probability theorem, Wikipedia,
https://en.wikipedia.org/wiki/Isserlis%27_theorem#Coordinate-free_Wick's_theorem) -/
theorem integral_prod_centered_dual_eq_wick (μ : Measure E) [ProbabilityTheory.IsGaussian μ]
    {n : ℕ} (L : Fin n → StrongDual ℝ E) :
    jointMoment μ (fun i ↦ centeredDual μ (L i)) =
      wick (fun i j ↦ dualCovariance μ (L i) (L j)) Finset.univ := by
  sorry

/-- The sixth centered Gaussian moment is one application of the general Wick theorem. -/
theorem sixthMoment_centered_dual_eq_wick (μ : Measure E) [ProbabilityTheory.IsGaussian μ]
    (L : Fin 6 → StrongDual ℝ E) :
    jointMoment μ (fun i ↦ centeredDual μ (L i)) =
      wick (fun i j ↦ dualCovariance μ (L i) (L j)) Finset.univ :=
  integral_prod_centered_dual_eq_wick μ L

/-- The centered second joint cumulant of Gaussian linear observables is their covariance.

Informal proof:
The second joint cumulant of any distribution is precisely the covariance.
For Gaussian variables, this is well-defined as they have all moments.
Apply `jointCumulant_two_eq_covariance`; Gaussian dual observables lie in every finite
`L^p` by `IsGaussian.memLp_dual`. -/
theorem jointCumulant_two_centered_dual (μ : Measure E) [ProbabilityTheory.IsGaussian μ]
    (L : Fin 2 → StrongDual ℝ E) :
    jointCumulant μ (fun i ↦ centeredDual μ (L i)) = dualCovariance μ (L 0) (L 1) := by
  have h0 : MemLp (centeredDual μ (L 0)) 2 μ := by
    change MemLp (fun ω ↦ L 0 ω - _) 2 μ
    exact MemLp.sub (IsGaussian.memLp_dual μ (L 0) 2 (by norm_num)) (memLp_const _)
  have h1 : MemLp (centeredDual μ (L 1)) 2 μ := by
    change MemLp (fun ω ↦ L 1 ω - _) 2 μ
    exact MemLp.sub (IsGaussian.memLp_dual μ (L 1) 2 (by norm_num)) (memLp_const _)
  rw [jointCumulant_two_eq_covariance _ h0 h1]
  change cov[fun ω ↦ L 0 ω - _, fun ω ↦ L 1 ω - _; μ] = _
  rw [covariance_sub_const_left]
  · rw [covariance_sub_const_right]
    · rfl
    · exact (IsGaussian.memLp_dual μ (L 1) 2 (by norm_num)).integrable (by norm_num)
  · exact (IsGaussian.memLp_dual μ (L 0) 2 (by norm_num)).integrable (by norm_num)

/-- Cumulants of a Wick-moment sequence vanish in orders other than two.
Informal proof:
If the moments of a sequence of variables are given by `wick C s` for some covariance `C`,
then by the moment-cumulant relation and Möbius inversion, the cumulants are the connected
components of the moments. Since `wick C` is a sum over pairings (blocks of size 2), the only
non-zero connected component of size `n` occurs when `n = 2` and the partition is just a single pair.
For `n ≠ 2`, the cumulant must be zero.
(Source: Cumulant, Wikipedia, https://en.wikipedia.org/wiki/Cumulant#Joint_cumulants) -/
theorem cumulantTransform_wick_eq_zero (C : ι → ι → ℝ) (hC : ∀ i j, C i j = C j i)
    {s : Finset ι} (hs : s.card ≠ 2) :
    Finpartition.cumulantTransform (wick C) s = 0 := by
  sorry

/-- Adding constants to random variables only affects their first cumulant.
Informal proof:
The cumulant transform is translation-invariant for orders greater than 1. This follows from the
multilinearity of cumulants and the fact that constants have zero cumulants for orders > 1.
(Source: Cumulant, Wikipedia, https://en.wikipedia.org/wiki/Cumulant#Properties) -/
theorem jointCumulant_add_const {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [Fintype ι]
    (hs : 1 < Fintype.card ι) (X : ι → Ω → ℝ) (c : ι → ℝ) :
    jointCumulant μ (fun i x ↦ X i x + c i) = jointCumulant μ X := by
  sorry

/-- Centered Gaussian cumulants vanish in every order other than two.

Informal proof:
Combine the general moment-cumulant identity with the coordinate-free Wick theorem.
The joint moments of a centered Gaussian are given by the sum over all pairings
(coordinate-free Wick's theorem). The moment-cumulant formula relates moments to cumulants
via a sum over partitions. By Möbius inversion, the cumulants are non-zero only for connected
components of the moments. Since Gaussian Wick moments contain only pair blocks (size 2),
Möbius inversion leaves a connected contribution only when the full index set itself is a pair.
Therefore, cumulants of size `n ≠ 2` must vanish. -/
theorem jointCumulant_centered_dual_eq_zero (μ : Measure E)
    [ProbabilityTheory.IsGaussian μ] {n : ℕ} (hn : n ≠ 2)
    (L : Fin n → StrongDual ℝ E) :
    jointCumulant μ (fun i ↦ centeredDual μ (L i)) = 0 := by
  sorry

/-- Noncentered Gaussian linear observables have no cumulants above order two.

Informal proof:
Adding constants (the mean) changes only the first cumulant. For `n > 2`, the cumulants
of noncentered variables are identical to those of centered variables, which vanish by the
previous theorem.
Center every `L i`, apply multilinearity and translation invariance of cumulants for
`n > 1`, apply the preceding centered theorem, and use `2 < n`. -/
theorem jointCumulant_dual_eq_zero (μ : Measure E) [ProbabilityTheory.IsGaussian μ]
    {n : ℕ} (hn : 2 < n) (L : Fin n → StrongDual ℝ E) :
    jointCumulant μ (fun i x ↦ L i x) = 0 := by
  sorry

end IsGaussian

/-! ## Multivariate Gaussian coordinates -/

/-- Wick theorem for repeated coordinates of a multivariate Gaussian.

Informal proof:
This is a direct specialization of the coordinate-free Wick theorem to coordinate projections
of a multivariate Gaussian. The covariance is given by the matrix `S`.
Specialize the coordinate-free theorem (`integral_prod_centered_dual_eq_wick`) to
coordinate projections. Rewrite their means with `integral_id_multivariateGaussian` and
their covariances with `covariance_eval_multivariateGaussian hS`. -/
theorem integral_prod_multivariateGaussian_centered_eq_wick
    {κ : Type*} [Fintype κ] [DecidableEq κ] {n : ℕ}
    (m : EuclideanSpace ℝ κ) (S : Matrix κ κ ℝ) (hS : S.PosSemidef)
    (index : Fin n → κ) :
    jointMoment (multivariateGaussian m S)
        (fun r z ↦ z (index r) - m (index r)) =
      wick (fun r q ↦ S (index r) (index q)) Finset.univ := by
  sorry

end Renormalization

end

end
