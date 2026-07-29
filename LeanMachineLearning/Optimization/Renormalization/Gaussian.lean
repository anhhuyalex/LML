/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Cumulant
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Wick calculus for Gaussian measures

This file defines a canonical pairing sum and states scalar, coordinate-free, and coordinate Wick
formulae.  The coordinate-free theorem is primary; the multivariate-coordinate theorem and the
sixth-moment theorem are direct specializations.

Deferred proof references:

* L. Isserlis, *On a Formula for the Product-Moment Coefficient of any Order of a Normal Frequency
  Distribution in any Number of Variables*: <https://doi.org/10.1093/biomet/12.1-2.134>.
* Mathlib's Gaussian MGF and `IsGaussian` API:
  see `Mathlib/Probability/Distributions/Gaussian`.

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
    · rintro ⟨hxa, h | h⟩; exacts [False.elim (hxa h), h]
    · rintro rfl; exact ⟨hab.symm, Or.inr rfl⟩
  have h2 : ({a, b} : Finset ι).erase b = {a} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hxb, h | h⟩; exacts [h, False.elim (hxb h)]
    · rintro rfl; exact ⟨hab, Or.inl rfl⟩
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
This is the standard recursive proof of Isserlis' theorem.
(Source: Wick's Theorem, nLab) -/
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
    ext t; simp [mgf_fun_id_gaussianReal]
  rw [← h_mgf, iteratedDeriv_mgf_zero] <;> simp

/-- The odd derivatives of `exp(v t² / 2)` evaluated at zero vanish.
Informal proof:
`exp(v t² / 2)` is an even function. The derivative of an even function is an odd function,
and the derivative of an odd function is an even function. Therefore, the odd-order derivatives
are odd functions, which must be zero at `t = 0`.
(Source: Even and odd functions, Wikipedia) -/
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
    let f : ℝ → ℝ := fun t ↦ Real.exp (v * t ^ 2 / 2)
    change iteratedDeriv (n + 2) f 0 =
      ((n + 1 : ℕ) : ℝ) * v * iteratedDeriv n f 0
    -- Step 1: the Gaussian quadratic exponential satisfies the first-order
    -- differential equation `f' t = v * t * f t`.
    -- This is the chain rule for `Real.exp` composed with `t ↦ v * t^2 / 2`.
    have h_deriv : deriv f = fun t ↦ v * t * f t := by
      funext t
      -- First differentiate the inner quadratic `t ↦ v * t^2 / 2`.
      have hg : HasDerivAt (fun x : ℝ => v * x ^ 2 / 2) (v * t) t := by
        have hpow : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℝ) * t) t := by
          simpa using
            (hasDerivAt_pow 2 t :
              HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℝ) * t ^ (2 - 1)) t)
        have hdiv : HasDerivAt (fun x : ℝ => (v * x ^ 2) / 2) ((v * ((2 : ℝ) * t)) / 2) t :=
          (HasDerivAt.const_mul v hpow).div_const 2
        convert hdiv using 1; ring
      -- Compose the inner derivative with `Real.exp` and commute the scalar factor.
      have h_exp : HasDerivAt f (Real.exp (v * t ^ 2 / 2) * (v * t)) t := by
        simpa [f] using hg.exp
      have hf : HasDerivAt f (v * t * f t) t := by
        convert h_exp using 1
        simp [f]
        ring
      exact hf.deriv
    -- Step 2: peel off one derivative from the `(n+2)`-nd iterated derivative,
    -- then rewrite the ordinary derivative using `h_deriv`.
    have h_shift :
        iteratedDeriv (n + 2) f 0 =
          iteratedDeriv (n + 1) (fun t ↦ v * t * f t) 0 := by
      -- Peel off the first derivative from the `(n+2)`-nd iterated derivative,
      -- then identify `deriv f` using the differential equation proved above.
      calc
        iteratedDeriv (n + 2) f 0 = iteratedDeriv (n + 1) (deriv f) 0 := by
          simpa [Nat.add_assoc] using
            congrFun (iteratedDeriv_succ' (n := n + 1) (f := f)) 0
        _ = iteratedDeriv (n + 1) (fun t ↦ v * t * f t) 0 := by
          rw [h_deriv]
    -- Step 3: pull the constant `v` out of the iterated derivative.
    have h_const :
        iteratedDeriv (n + 1) (fun t ↦ v * t * f t) 0 =
          v * iteratedDeriv (n + 1) (fun t ↦ t * f t) 0 := by
      -- Reassociate `v * t * f t` as the constant multiple `v * (t * f t)`,
      -- then use linearity of iterated derivatives under constant multiplication.
      simp [mul_assoc]
    -- Step 4: apply the iterated Leibniz rule to `t * f t` at zero.
    -- In the resulting sum, the `i = 0` term vanishes because `t = 0`,
    -- the `i = 1` term contributes `(n+1) * iteratedDeriv n f 0`, and
    -- all terms with `2 ≤ i` vanish because higher derivatives of `t` are zero.
    have h_linear_product :
        iteratedDeriv (n + 1) (fun t ↦ t * f t) 0 =
          ((n + 1 : ℕ) : ℝ) * iteratedDeriv n f 0 := by
      -- Smoothness hypotheses needed by the generalized Leibniz rule.
      have h_id_smooth : ContDiffAt ℝ (n + 1) (fun t : ℝ ↦ t) 0 := by
        fun_prop
      have hf_smooth : ContDiffAt ℝ (n + 1) f 0 := by
        dsimp [f]
        fun_prop
      -- Generalized Leibniz rule for the `(n+1)`-st derivative of `t * f t`.
      have h_leibniz :
          iteratedDeriv (n + 1) (fun t : ℝ ↦ t * f t) 0 =
            ∑ i ∈ Finset.range ((n + 1) + 1),
              (((n + 1).choose i : ℕ) : ℝ) *
                iteratedDeriv i (fun t : ℝ ↦ t) 0 *
                  iteratedDeriv ((n + 1) - i) f 0 := by
        -- `iteratedDeriv_mul` is stated for point-free multiplication of
        -- functions, so first identify the lambda product with `(fun t => t) * f`.
        rw [show (fun t : ℝ ↦ t * f t) = (fun t : ℝ ↦ t) * f by
          ext t
          rfl]
        exact
          (iteratedDeriv_mul (𝕜 := ℝ) (𝔸 := ℝ) (n := n + 1) (x := (0 : ℝ))
            (f := fun t : ℝ ↦ t) (g := f) h_id_smooth hf_smooth)
      -- In the Leibniz sum, `iteratedDeriv i (fun t => t) 0` is zero except
      -- at `i = 1`.  Thus only the `i = 1` term survives; its binomial
      -- coefficient is `(n+1).choose 1 = n+1`, and `(n+1)-1 = n`.
      have h_sum_collapse :
          (∑ i ∈ Finset.range ((n + 1) + 1),
              (((n + 1).choose i : ℕ) : ℝ) *
                iteratedDeriv i (fun t : ℝ ↦ t) 0 *
                  iteratedDeriv ((n + 1) - i) f 0) =
            ((n + 1 : ℕ) : ℝ) * iteratedDeriv n f 0 := by
        -- Collapse the sum to the unique nonzero contribution, namely `i = 1`.
        -- For every other index the iterated derivative of the identity at zero is zero.
        have hsingle :
            (∑ i ∈ Finset.range ((n + 1) + 1),
                (((n + 1).choose i : ℕ) : ℝ) *
                  iteratedDeriv i (fun t : ℝ ↦ t) 0 *
                    iteratedDeriv ((n + 1) - i) f 0) =
              (((n + 1).choose 1 : ℕ) : ℝ) *
                iteratedDeriv 1 (fun t : ℝ ↦ t) 0 *
                  iteratedDeriv ((n + 1) - 1) f 0 := by
          apply Finset.sum_eq_single_of_mem 1
          · simp
          · intro i _hi hi_ne
            -- Away from `i = 1`, `iteratedDeriv i id 0 = 0`.
            simp [iteratedDeriv_fun_id_zero, hi_ne]
        -- The surviving term has derivative `1`, binomial coefficient `n+1`,
        -- and derivative order `(n+1)-1 = n`.
        rw [hsingle]
        simp [iteratedDeriv_fun_id_zero]
      calc
        iteratedDeriv (n + 1) (fun t : ℝ ↦ t * f t) 0
            = ∑ i ∈ Finset.range ((n + 1) + 1),
                (((n + 1).choose i : ℕ) : ℝ) *
                  iteratedDeriv i (fun t : ℝ ↦ t) 0 *
                    iteratedDeriv ((n + 1) - i) f 0 := h_leibniz
        _ = ((n + 1 : ℕ) : ℝ) * iteratedDeriv n f 0 := h_sum_collapse
    -- Combine the analytic reduction with a final commutative-ring rearrangement.
    calc
      iteratedDeriv (n + 2) f 0
          = iteratedDeriv (n + 1) (fun t ↦ v * t * f t) 0 := h_shift
      _ = v * iteratedDeriv (n + 1) (fun t ↦ t * f t) 0 := h_const
      _ = v * (((n + 1 : ℕ) : ℝ) * iteratedDeriv n f 0) := by
          rw [h_linear_product]
      _ = ((n + 1 : ℕ) : ℝ) * v * iteratedDeriv n f 0 := by
          ring
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
        simp
    | succ m ih =>
        -- The recurrence turns the `(2*(m+1))`-st derivative into
        -- `(2*m+1) * v` times the `(2*m)`-th derivative.
        have h_step := h_recurrence (2 * m)
        -- First normalize the derivative order `2 * (m + 1)` to the
        -- recurrence order `2 * m + 2`.
        have h_order : 2 * (m + 1) = 2 * m + 2 := by
          omega
        -- The remaining work is factorial arithmetic:
        -- after substituting the induction hypothesis into the recurrence,
        -- the coefficient `(2*m+1) * (2*m)! / (2^m*m!)` has to be
        -- identified with `(2*m+2)! / (2^(m+1)*(m+1)!)`.
        have h_coeff :
            ((2 * m + 1 : ℕ) : ℝ) * v *
                (((2 * m).factorial : ℝ) /
                    ((2 : ℝ) ^ m * (m.factorial : ℝ)) * v ^ m) =
              ((2 * (m + 1)).factorial : ℝ) /
                  ((2 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ)) *
                v ^ (m + 1) := by
          -- Normalize the new even order and expose the successor factorials.
          rw [h_order]
          have h_fact_big :
              (((2 * m + 2).factorial : ℕ) : ℝ) =
                ((2 * m + 2 : ℕ) : ℝ) * ((2 * m + 1 : ℕ) : ℝ) *
                  (((2 * m).factorial : ℕ) : ℝ) := by
            rw [Nat.factorial_succ (2 * m + 1), Nat.factorial_succ (2 * m)]
            norm_num
            ring
          have h_fact_small : (((m + 1).factorial : ℕ) : ℝ) =
              ((m + 1 : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ) := by
            rw [Nat.factorial_succ m]
            norm_num
          -- The denominator is nonzero, so we may clear it safely.
          have hden_m : (2 : ℝ) ^ m * ((m.factorial : ℕ) : ℝ) ≠ 0 := by
            positivity
          have hden_succ :
              (2 : ℝ) ^ (m + 1) * (((m + 1).factorial : ℕ) : ℝ) ≠ 0 := by
            positivity
          -- After the successor rewrites, `field_simp` cancels the positive
          -- factorial/power denominators and `ring_nf` proves the remaining
          -- polynomial identity, using `2*m+2 = 2*(m+1)`.
          rw [h_fact_big, h_fact_small, pow_succ, pow_succ]
          field_simp [hden_m]
          norm_num
          ring_nf
        calc
          iteratedDeriv (2 * (m + 1)) (fun t => Real.exp (v * t ^ 2 / 2)) 0
              = iteratedDeriv (2 * m + 2) (fun t => Real.exp (v * t ^ 2 / 2)) 0 := by
                  rw [h_order]
          _ = ((2 * m + 1 : ℕ) : ℝ) * v *
                iteratedDeriv (2 * m) (fun t => Real.exp (v * t ^ 2 / 2)) 0 := h_step
          _ = ((2 * m + 1 : ℕ) : ℝ) * v *
                (((2 * m).factorial : ℝ) /
                    ((2 : ℝ) ^ m * (m.factorial : ℝ)) * v ^ m) := by
                  rw [ih]
          _ = ((2 * (m + 1)).factorial : ℝ) /
                  ((2 : ℝ) ^ (m + 1) * ((m + 1).factorial : ℝ)) *
                v ^ (m + 1) := h_coeff
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
For a 1D real Gaussian measure with mean 0 and variance `v`, the expectation of
`x * x^n` is given by integration by parts.
Specifically, `∫ x, x * x^n dN(0, v) = ∫ x, x^(n+1) dN(0, v)`,
and this equals `v * n * ∫ x, x^(n-1) dN(0, v)`.
This follows directly from `integral_pow_gaussianReal_even` and `integral_pow_gaussianReal_odd`.
(Source: Stein's lemma, Wikipedia, https://en.wikipedia.org/wiki/Stein%27s_lemma) -/
theorem integral_mul_pow_gaussianReal (v : ℝ≥0) (n : ℕ) :
    ∫ x, x * x ^ n ∂gaussianReal 0 v = (v : ℝ) * (n : ℝ) * ∫ x, x ^ (n - 1) ∂gaussianReal 0 v := by
  -- First reduce the left-hand side to the ordinary `(n+1)`-st moment.
  have h_integrand :
      ∫ x, x * x ^ n ∂gaussianReal 0 v = ∫ x, x ^ (n + 1) ∂gaussianReal 0 v := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [pow_succ']
  -- Prove the moment recurrence by splitting on the parity of `n` and using the
  -- two moment formulas proved just above.
  have h_moment_rec :
      ∫ x, x ^ (n + 1) ∂gaussianReal 0 v =
        (v : ℝ) * (n : ℝ) * ∫ x, x ^ (n - 1) ∂gaussianReal 0 v := by
    rcases Nat.even_or_odd' n with ⟨m, hnm | hnm⟩
    · -- If `n = 2*m`, then the left side is an odd moment.  For `m = 0`
      -- the right side is zero because of the factor `n`; for `m > 0`,
      -- `n - 1 = 2*(m-1)+1`, so the right side also contains an odd moment.
      subst n
      by_cases hm : m = 0
      · subst m
        simp
      · -- This is the parity case `m = k+1`; rewrite both sides with
        -- `integral_pow_gaussianReal_odd` and simplify the remaining algebra.
        have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        have hpred : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
        rw [integral_pow_gaussianReal_odd v m]
        have h_rhs_odd :
            ∫ x, x ^ (2 * m - 1) ∂gaussianReal 0 v = 0 := by
          rw [hpred]
          exact integral_pow_gaussianReal_odd v (m - 1)
        rw [h_rhs_odd]
        ring
    · -- If `n = 2*m + 1`, then the identity relates two even moments:
      -- `2*m+2` on the left and `2*m` on the right.  Rewrite both sides using
      -- `integral_pow_gaussianReal_even`; the remaining statement is the
      -- factorial identity
      --   `(2m+2)!/(2^(m+1)(m+1)!) * v^(m+1)
      --      = v*(2m+1)*(2m)!/(2^m m!) * v^m`,
      -- proved by `Nat.factorial_succ`, `field_simp`, and `ring_nf`.
      subst n
      have hleft_exp : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
      have hright_exp : 2 * m + 1 - 1 = 2 * m := by omega
      rw [hleft_exp, hright_exp]
      rw [integral_pow_gaussianReal_even v (m + 1), integral_pow_gaussianReal_even v m]
      -- After substituting the closed form for the two even moments, this is a
      -- pure factorial identity together with `v^(m+1) = v * v^m`.
      -- We first rewrite `2*(m+1)` as `2*m+2`, expose the successor
      -- factorials, clear the nonzero factorial/power denominator, and finish
      -- the polynomial identity by normalization.
      have h_order : 2 * (m + 1) = 2 * m + 2 := by
        omega
      rw [h_order]
      have h_fact_big :
          (((2 * m + 2).factorial : ℕ) : ℝ) =
            ((2 * m + 2 : ℕ) : ℝ) * ((2 * m + 1 : ℕ) : ℝ) *
              (((2 * m).factorial : ℕ) : ℝ) := by
        rw [Nat.factorial_succ (2 * m + 1), Nat.factorial_succ (2 * m)]
        norm_num
        ring
      have h_fact_small : (((m + 1).factorial : ℕ) : ℝ) =
          ((m + 1 : ℕ) : ℝ) * ((m.factorial : ℕ) : ℝ) := by
        rw [Nat.factorial_succ m]
        norm_num
      have hden_m : (2 : ℝ) ^ m * ((m.factorial : ℕ) : ℝ) ≠ 0 := by
        positivity
      have hden_succ :
          (2 : ℝ) ^ (m + 1) * (((m + 1).factorial : ℕ) : ℝ) ≠ 0 := by
        positivity
      rw [h_fact_big, h_fact_small, pow_succ, pow_succ]
      field_simp [hden_m, hden_succ]
      all_goals first
        | exact Or.inl (Or.inl trivial)
        | ring_nf
          rw [show (2 + m * 2 : ℕ) = (1 + m) * 2 by omega]
          norm_num
          ring_nf
  calc
    ∫ x, x * x ^ n ∂gaussianReal 0 v = ∫ x, x ^ (n + 1) ∂gaussianReal 0 v := h_integrand
    _ = (v : ℝ) * (n : ℝ) * ∫ x, x ^ (n - 1) ∂gaussianReal 0 v := h_moment_rec

/-- Center a continuous linear functional under `μ`. -/
def centeredDual {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (μ : Measure E) (L : StrongDual ℝ E) : E → ℝ :=
  fun x ↦ L x - ∫ y, L y ∂μ

/-- Covariance kernel of two continuous linear functionals. -/
def dualCovariance {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) (L K : StrongDual ℝ E) : ℝ :=
  covariance (fun x ↦ L x) (fun x ↦ K x) μ

/-- The covariance kernel of continuous linear functionals is symmetric. -/
theorem dualCovariance_comm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) (L K : StrongDual ℝ E) :
    dualCovariance μ L K = dualCovariance μ K L := by
  simpa [dualCovariance] using covariance_comm (fun x ↦ L x) (fun x ↦ K x)

namespace IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

-- Any finite linear combination of centered continuous linear observables is
-- Gaussian: it is a translate of the pushforward by one continuous linear functional.
private lemma isGaussian_map_centeredDual_linearCombination (μ : Measure E)
    [ProbabilityTheory.IsGaussian μ] {n : ℕ} (L : StrongDual ℝ E)
    (K : Fin n → StrongDual ℝ E) (a₀ : ℝ) (a : Fin n → ℝ) :
    ProbabilityTheory.IsGaussian
      (Measure.map
        (fun x ↦ a₀ * centeredDual μ L x + ∑ i, a i * centeredDual μ (K i) x) μ) := by
  -- Combine the finitely many continuous linear functionals into one continuous
  -- linear functional.  Its centered pushforward is the displayed scalar linear
  -- combination of centered observables.
  let H : StrongDual ℝ E := a₀ • L + ∑ i, a i • K i
  let c : ℝ := a₀ * (∫ y, L y ∂μ) + ∑ i, a i * (∫ y, K i y ∂μ)
  -- Pointwise algebra identifies the centered linear combination with an
  -- affine translate of the single continuous linear observable `H`.
  have h_pointwise :
      (fun x ↦ a₀ * centeredDual μ L x + ∑ i, a i * centeredDual μ (K i) x)
        = (fun x ↦ H x - c) := by
    funext x
    simp [centeredDual, H, c]
    ring_nf
    rw [Finset.sum_sub_distrib]
    ring
  -- Translating the resulting real Gaussian law by a constant preserves Gaussianity.
  have h_translated_gaussian :
      ProbabilityTheory.IsGaussian
        (Measure.map (fun y : ℝ ↦ y - c) (Measure.map (fun x ↦ H x) μ)) := by
    haveI : ProbabilityTheory.IsGaussian (Measure.map (fun x ↦ H x) μ) := by
      change ProbabilityTheory.IsGaussian (Measure.map H μ)
      infer_instance
    infer_instance
  -- Functoriality of pushforward measures identifies the affine map from `E`
  -- with first applying `H` and then translating by `-c`.
  have h_map_comp :
      Measure.map (fun x ↦ H x - c) μ =
        Measure.map (fun y : ℝ ↦ y - c) (Measure.map (fun x ↦ H x) μ) := by
    simpa [Function.comp_def] using
      (Measure.map_map (μ := μ) (f := fun x : E ↦ H x) (g := fun y : ℝ ↦ y - c)
        (continuous_id.sub continuous_const).measurable H.continuous.measurable).symm
  exact h_pointwise ▸ h_map_comp ▸ h_translated_gaussian

-- The product of one distinguished centered observable and a finite family of
-- centered observables is integrable by Gaussian finite moments and Hölder.
private lemma integrable_centeredDual_mul_prod (μ : Measure E)
    [ProbabilityTheory.IsGaussian μ] {n : ℕ} (L : StrongDual ℝ E)
    (K : Fin n → StrongDual ℝ E) :
    Integrable (fun x ↦ centeredDual μ L x * ∏ i, centeredDual μ (K i) x) μ := by
  -- Every centered continuous linear observable has the finite moment needed
  -- for a Hölder estimate over the `n + 1` factors.
  have h_centered_memLp : ∀ A : StrongDual ℝ E,
      MemLp (centeredDual μ A) (((n + 1 : ℕ) : ℝ≥0∞)) μ := fun A ↦ by
    change MemLp (fun ω ↦ A ω - _) (((n + 1 : ℕ) : ℝ≥0∞)) μ
    exact MemLp.sub
      (ProbabilityTheory.IsGaussian.memLp_dual μ A (((n + 1 : ℕ) : ℝ≥0∞)) (by norm_num))
      (memLp_const _)
  -- Hölder over the finite family indexed by `Option (Fin n)` gives the product
  -- of the distinguished factor `L` and all `K i` in `L¹`.
  have h_holder_product :
      MemLp (fun x ↦ centeredDual μ L x * ∏ i, centeredDual μ (K i) x) 1 μ := by
    have h_all_factors : ∀ o : Option (Fin n),
        MemLp (fun x ↦ match o with
          | none => centeredDual μ L x
          | some i => centeredDual μ (K i) x)
          (((n + 1 : ℕ) : ℝ≥0∞)) μ
      | none => by simpa using h_centered_memLp L
      | some i => by simpa using h_centered_memLp (K i)
    -- Index the `n + 1` factors by `Option (Fin n)`: `none` is the
    -- distinguished `L` factor, and `some i` is the `K i` factor.
    let F : Option (Fin n) → E → ℝ := fun o x ↦
      match o with
      | none => centeredDual μ L x
      | some i => centeredDual μ (K i) x
    -- Hölder for finite products with equal exponents gives an `Lᵖ` bound whose
    -- exponent is the inverse of the sum of reciprocal exponents.
    have h_option_product :
        MemLp (∏ o : Option (Fin n), F o)
          ((∑ o : Option (Fin n), (((n + 1 : ℕ) : ℝ≥0∞))⁻¹)⁻¹) μ := by
      simpa [F] using
        (MeasureTheory.MemLp.prod
          (μ := μ)
          (f := F)
          (p := fun _ : Option (Fin n) ↦ (((n + 1 : ℕ) : ℝ≥0∞)))
          (s := Finset.univ)
          (fun o _ho ↦ by simpa [F] using h_all_factors o))
    -- `Option (Fin n)` has cardinality `n + 1`, so the sum of `n + 1` copies
    -- of `(n+1)⁻¹` is `1` in `ℝ≥0∞`.
    have h_exponent :
        ((∑ o : Option (Fin n), (((n + 1 : ℕ) : ℝ≥0∞))⁻¹)⁻¹) =
          (1 : ℝ≥0∞) := by
      rw [Finset.sum_const, Finset.card_univ]
      simp only [Fintype.card_option, Fintype.card_fin]
      rw [nsmul_eq_mul]
      have h0 : (((n + 1 : ℕ) : ℝ≥0∞) ≠ 0) := by norm_num
      have htop : (((n + 1 : ℕ) : ℝ≥0∞) ≠ ∞) := ENNReal.natCast_ne_top _
      have hmul :
          (((n + 1 : ℕ) : ℝ≥0∞) * (((n + 1 : ℕ) : ℝ≥0∞)⁻¹)) =
            (1 : ℝ≥0∞) :=
        ENNReal.mul_inv_cancel h0 htop
      change ((((n + 1 : ℕ) : ℝ≥0∞) * (((n + 1 : ℕ) : ℝ≥0∞)⁻¹))⁻¹) =
        (1 : ℝ≥0∞)
      rw [hmul]
      simp
    -- Unfold the `Option`-indexed product into the displayed pointwise product.
    convert (h_exponent ▸ h_option_product : MemLp (∏ o : Option (Fin n), F o) 1 μ) using 1
    ext x
    simp [F, Fintype.prod_option]
  exact h_holder_product.integrable (by norm_num)

-- Finite products of centered Gaussian linear observables are integrable.  This
-- is the reusable Hölder estimate behind erased-product moments in Stein/Wick
-- recurrences; the empty product is handled separately as the constant `1`.
private lemma integrable_finset_prod_centeredDual (μ : Measure E)
    [ProbabilityTheory.IsGaussian μ] {ι : Type*} (s : Finset ι)
    (K : ι → StrongDual ℝ E) :
    Integrable (fun x ↦ ∏ i ∈ s, centeredDual μ (K i) x) μ := by
  by_cases hs : s.Nonempty
  · -- Nonempty products: put every factor in the same `L^{|s|}` space and use Hölder.
    have h_centered_memLp : ∀ i ∈ s,
        MemLp (centeredDual μ (K i)) (((s.card : ℕ) : ℝ≥0∞)) μ := fun i _hi ↦ by
      change MemLp (fun ω ↦ K i ω - _)
        (((s.card : ℕ) : ℝ≥0∞)) μ
      exact MemLp.sub
        (ProbabilityTheory.IsGaussian.memLp_dual μ (K i)
          (((s.card : ℕ) : ℝ≥0∞)) (ENNReal.natCast_ne_top _))
        (memLp_const _)
    have h_holder_product :
        MemLp (fun x ↦ ∏ i ∈ s, centeredDual μ (K i) x)
          ((∑ i ∈ s, (((s.card : ℕ) : ℝ≥0∞))⁻¹)⁻¹) μ := by
      convert
        (MeasureTheory.MemLp.prod
          (μ := μ)
          (f := fun i x ↦ centeredDual μ (K i) x)
          (p := fun _ : ι ↦ (((s.card : ℕ) : ℝ≥0∞)))
          (s := s)
          h_centered_memLp) using 1
      ext x
      simp
    -- Since `s` has `s.card` elements, the Hölder exponent collapses to `1`.
    have h_exponent :
        ((∑ i ∈ s, (((s.card : ℕ) : ℝ≥0∞))⁻¹)⁻¹) =
          (1 : ℝ≥0∞) := by
      rw [Finset.sum_const]
      rw [nsmul_eq_mul]
      have hcard_pos : 0 < s.card := Finset.card_pos.mpr hs
      have hcard_ne_zero : s.card ≠ 0 := Nat.ne_of_gt hcard_pos
      have h0 : (((s.card : ℕ) : ℝ≥0∞) ≠ 0) := by
        norm_num [hcard_ne_zero]
      have htop : (((s.card : ℕ) : ℝ≥0∞) ≠ ∞) := ENNReal.natCast_ne_top _
      have hmul :
          (((s.card : ℕ) : ℝ≥0∞) * (((s.card : ℕ) : ℝ≥0∞)⁻¹)) =
            (1 : ℝ≥0∞) :=
        ENNReal.mul_inv_cancel h0 htop
      change ((((s.card : ℕ) : ℝ≥0∞) *
        (((s.card : ℕ) : ℝ≥0∞)⁻¹))⁻¹) = (1 : ℝ≥0∞)
      rw [hmul]
      simp
    exact (h_exponent ▸ h_holder_product :
      MemLp (fun x ↦ ∏ i ∈ s, centeredDual μ (K i) x) 1 μ).integrable (by norm_num)
  · -- Empty products reduce to the integrable constant `1`.
    have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hs_empty]

-- Centering subtracts exactly the mean, so the centered observable has integral zero.
private lemma integral_centeredDual_eq_zero (μ : Measure E) [ProbabilityTheory.IsGaussian μ]
    (A : StrongDual ℝ E) :
    ∫ x, centeredDual μ A x ∂μ = 0 := by
  unfold centeredDual
  rw [MeasureTheory.integral_sub
    ((ProbabilityTheory.IsGaussian.memLp_dual μ A 2 (by norm_num)).integrable (by norm_num))
    (integrable_const _)]
  simp [MeasureTheory.integral_const]

-- Subtracting constants from both arguments does not change covariance, so the
-- covariance of centered observables is the covariance kernel used in this file.
private lemma covariance_centeredDual_eq_dualCovariance (μ : Measure E)
    [ProbabilityTheory.IsGaussian μ] (L K : StrongDual ℝ E) :
    covariance (centeredDual μ L) (centeredDual μ K) μ = dualCovariance μ L K := by
  unfold centeredDual dualCovariance
  change cov[fun ω ↦ L ω - _, fun ω ↦ K ω - _; μ] =
    cov[fun x ↦ L x, fun x ↦ K x; μ]
  rw [covariance_sub_const_left
    (X := fun x : E ↦ L x) (Y := fun x : E ↦ K x - ∫ y, K y ∂μ)
    ((ProbabilityTheory.IsGaussian.memLp_dual μ L 2 (by norm_num)).integrable
      (by norm_num)),
    covariance_sub_const_right
    (X := fun x : E ↦ L x) (Y := fun x : E ↦ K x)
    ((ProbabilityTheory.IsGaussian.memLp_dual μ K 2 (by norm_num)).integrable
      (by norm_num))]

-- Cramér-Wold joint Gaussianity restricts to the subtype of indices in a finset.
-- Extend subtype coefficients by zero so the restricted sum is the original sum.
private lemma jointGaussian_restrict_finset_subtype {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (ν : Measure Ω) (Z : ι → Ω → ℝ) (s : Finset ι)
    (h_joint : ∀ a : ι → ℝ,
      ProbabilityTheory.IsGaussian
        (Measure.map (fun ω ↦ ∑ k, a k * Z k ω) ν)) :
    ∀ a : {k : ι // k ∈ s} → ℝ,
      ProbabilityTheory.IsGaussian
        (Measure.map (fun ω ↦ ∑ k : {k : ι // k ∈ s}, a k * Z k.1 ω) ν) := by
  classical
  intro a
  let a_ext : ι → ℝ := fun k ↦ if hk : k ∈ s then a ⟨k, hk⟩ else 0
  have h_sum_restrict :
      (fun ω ↦ ∑ k : {k : ι // k ∈ s}, a k * Z k.1 ω) =
        (fun ω ↦ ∑ k : ι, a_ext k * Z k ω) := by
    -- Reindex the subtype sum as the sum over `s`; zero coefficients remove all
    -- indices outside `s` from the ambient finite sum.
    funext ω
    dsimp [a_ext]
    calc
      ∑ k : {k : ι // k ∈ s}, a k * Z (↑k) ω =
          ∑ k ∈ s, (if hk : k ∈ s then a ⟨k, hk⟩ else 0) * Z k ω := by
        rw [← Finset.sum_attach s
          (fun k ↦ (if hk : k ∈ s then a ⟨k, hk⟩ else 0) * Z k ω),
          ← Finset.attach_eq_univ]
        refine Finset.sum_congr rfl fun x _hx ↦ ?_
        simp
      _ = ∑ k : ι, (if hk : k ∈ s then a ⟨k, hk⟩ else 0) * Z k ω :=
        Finset.sum_subset (Finset.subset_univ s) (fun k _ hk ↦ by simp [hk])
  exact h_sum_restrict ▸ h_joint a_ext

-- Componentwise centering is unchanged after restricting to a finset subtype.
private lemma centered_restrict_finset_subtype {Ω ι : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (Z : ι → Ω → ℝ) (s : Finset ι)
    (h_centered : ∀ k : ι, ∫ ω, Z k ω ∂ν = 0) :
    ∀ k : {k : ι // k ∈ s}, ∫ ω, Z k.1 ω ∂ν = 0 :=
  fun k ↦ h_centered k.1

-- A product over a finset is definitionally the product over its attached subtype
-- after reindexing by the subtype value map.
private lemma prod_finset_eq_prod_subtype {Ω ι : Type*}
    (Z : ι → Ω → ℝ) (s : Finset ι) (ω : Ω) :
    (∏ k ∈ s, Z k ω) = ∏ k : {k : ι // k ∈ s}, Z k.1 ω :=
  (Finset.prod_attach s (fun k ↦ Z k ω)).symm

-- A Cramér-Wold hypothesis includes the zero linear combination.  Its Gaussian
-- constant pushforward is a probability measure, and comparing masses of `univ`
-- transfers probability normalization back to the original measure.
private lemma isProbabilityMeasure_of_jointGaussian_zero_linear {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) (Z : ι → Ω → ℝ)
    (h_joint : ∀ a : ι → ℝ,
      ProbabilityTheory.IsGaussian
        (Measure.map (fun ω ↦ ∑ k, a k * Z k ω) ν)) :
    IsProbabilityMeasure ν := by
  haveI : ProbabilityTheory.IsGaussian (Measure.map (fun _ : Ω ↦ (0 : ℝ)) ν) := by
    simpa using h_joint (fun _ : ι ↦ 0)
  exact MeasureTheory.Measure.isProbabilityMeasure_of_map (μ := ν) fun _ : Ω ↦ (0 : ℝ)

-- A coordinate is a jointly Gaussian linear combination: choose the one-hot
-- coefficient vector and identify the finite sum with the selected coordinate.
-- Integrability then pulls back from the one-dimensional Gaussian pushforward.
private lemma integrable_coordinate_of_jointGaussian {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Z : ι → Ω → ℝ)
    (h_joint : ∀ a : ι → ℝ,
      ProbabilityTheory.IsGaussian
        (Measure.map (fun ω ↦ ∑ k : ι, a k * Z k ω) ν)) :
    ∀ k : ι, Integrable (fun ω ↦ Z k ω) ν := by
  classical
  intro k
  let e : ι → ℝ := fun l ↦ if l = k then 1 else 0
  haveI : ProbabilityTheory.IsGaussian (Measure.map (fun ω ↦ Z k ω) ν) := by
    simpa [e] using h_joint e
  have hZ_ae : AEMeasurable (fun ω ↦ Z k ω) ν :=
    aemeasurable_of_map_neZero (μ := ν) (f := fun ω ↦ Z k ω)
      inferInstance
  simpa [id, Function.comp_def] using
    (ProbabilityTheory.IsGaussian.integrable_dual
      (Measure.map (fun ω ↦ Z k ω) ν)
      (ContinuousLinearMap.id ℝ ℝ)).comp_aemeasurable hZ_ae

-- Once coordinates are integrable, centering passes to every finite linear
-- combination by integrating the finite sum termwise and pulling out constants.
private lemma integral_linear_combination_eq_zero_of_centered_jointGaussian {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω)
    [IsProbabilityMeasure ν] (Z : ι → Ω → ℝ)
    (h_joint : ∀ a : ι → ℝ,
      ProbabilityTheory.IsGaussian
        (Measure.map (fun ω ↦ ∑ k : ι, a k * Z k ω) ν))
    (h_centered : ∀ k : ι, ∫ ω, Z k ω ∂ν = 0) (a : ι → ℝ) :
    ∫ ω, (∑ k : ι, a k * Z k ω) ∂ν = 0 := by
  calc
    ∫ ω, (∑ k : ι, a k * Z k ω) ∂ν =
        ∑ k : ι, ∫ ω, a k * Z k ω ∂ν := by
      simpa using
        (MeasureTheory.integral_finsetSum (Finset.univ : Finset ι)
          (μ := ν) (f := fun k ω ↦ a k * Z k ω)
          (fun k _hk ↦
            (integrable_coordinate_of_jointGaussian ν Z h_joint k).const_mul (a k)))
    _ = ∑ k : ι, a k * ∫ ω, Z k ω ∂ν := by
      simp [MeasureTheory.integral_const_mul]
    _ = 0 := by
      simp [h_centered]

-- A coordinate has finite second moment because it is itself a jointly
-- Gaussian linear combination (the one-hot combination).  This mirrors the
-- integrability helper above, but uses the Gaussian `MemLp` API needed for
-- covariance and variance calculations.
private lemma memLp_coordinate_of_jointGaussian {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Z : ι → Ω → ℝ)
    (h_joint : ∀ a : ι → ℝ,
      ProbabilityTheory.IsGaussian
        (Measure.map (fun ω ↦ ∑ k : ι, a k * Z k ω) ν)) :
    ∀ k : ι, MemLp (fun ω ↦ Z k ω) 2 ν := by
  classical
  intro k
  let e : ι → ℝ := fun l ↦ if l = k then 1 else 0
  haveI : ProbabilityTheory.IsGaussian (Measure.map (fun ω ↦ Z k ω) ν) := by
    simpa [e] using h_joint e
  have h_id_memLp : MemLp id 2 (Measure.map (fun ω ↦ Z k ω) ν) := by
    simpa [id] using
      (ProbabilityTheory.IsGaussian.memLp_dual
        (Measure.map (fun ω ↦ Z k ω) ν)
        (ContinuousLinearMap.id ℝ ℝ) 2 (by norm_num))
  have hZ_ae : AEMeasurable (fun ω ↦ Z k ω) ν :=
    aemeasurable_of_map_neZero (μ := ν) (f := fun ω ↦ Z k ω)
      (show NeZero (Measure.map (fun ω ↦ Z k ω) ν) from inferInstance)
  simpa [id, Function.comp_def] using h_id_memLp.comp_of_map hZ_ae

-- Variance of a finite weighted sum is the covariance quadratic form.
-- The only analytic input needed here is `MemLp` for each coordinate; the rest
-- is finite covariance bilinearity, so this helper is independent of Gaussianity.
private lemma variance_linear_combination_eq_covariance_quadratic {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) [IsFiniteMeasure ν]
    (Z : ι → Ω → ℝ)
    (hZ_memLp : ∀ k : ι, MemLp (fun ω ↦ Z k ω) 2 ν) (a : ι → ℝ) :
    Var[(fun ω ↦ ∑ k : ι, a k * Z k ω); ν] =
      ∑ i : ι, ∑ j : ι, a i * a j * covariance (Z i) (Z j) ν := by
  calc
    Var[(fun ω ↦ ∑ k : ι, a k * Z k ω); ν] =
        ∑ i : ι, ∑ j : ι,
          covariance (fun ω ↦ a i * Z i ω) (fun ω ↦ a j * Z j ω) ν := by
      simpa using
        (ProbabilityTheory.variance_fun_sum
          (μ := ν) (X := fun i ω ↦ a i * Z i ω)
          (fun i ↦ (hZ_memLp i).const_mul (a i)))
    _ = ∑ i : ι, ∑ j : ι, a i * a j * covariance (Z i) (Z j) ν := by
      refine Finset.sum_congr rfl fun i _hi ↦ ?_
      refine Finset.sum_congr rfl fun j _hj ↦ ?_
      simp only [ProbabilityTheory.covariance_const_mul_left,
        ProbabilityTheory.covariance_const_mul_right]
      ring

-- For a centered jointly Gaussian finite family, every scalar linear
-- combination has the one-dimensional Gaussian MGF whose variance is the
-- covariance quadratic form.  This isolates the analytic Gaussian calculation
-- from the later finite partition/cumulant bookkeeping.
private lemma mgf_linear_combination_centered_jointGaussian {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Z : ι → Ω → ℝ)
    (h_joint : ∀ a : ι → ℝ,
      ProbabilityTheory.IsGaussian
        (Measure.map (fun ω ↦ ∑ k : ι, a k * Z k ω) ν))
    (h_centered : ∀ k : ι, ∫ ω, Z k ω ∂ν = 0) :
    ∀ a : ι → ℝ,
      (fun t : ℝ ↦ ProbabilityTheory.mgf
          (fun ω ↦ ∑ k : ι, a k * Z k ω) ν t) =
        (fun t : ℝ ↦ Real.exp
          (((∑ i : ι, ∑ j : ι,
              a i * a j * covariance (Z i) (Z j) ν) * t ^ 2) / 2)) := fun a ↦ by
  let X : Ω → ℝ := fun ω ↦ ∑ k : ι, a k * Z k ω
  -- The Cramér-Wold hypothesis says that this scalar linear combination has a
  -- Gaussian pushforward law.
  have hX_gaussian : ProbabilityTheory.IsGaussian (Measure.map X ν) := by
    simpa [X] using h_joint a
  -- Centering of coordinates passes to finite linear combinations once the
  -- Gaussian law supplies integrability of each coordinate.
  have hX_mean_zero : ∫ ω, X ω ∂ν = 0 := by
    simpa [X] using
      integral_linear_combination_eq_zero_of_centered_jointGaussian ν Z h_joint
        h_centered a
  -- The variance is the covariance quadratic form by finite covariance
  -- bilinearity.
  have hX_variance :
      Var[X; ν] =
        ∑ i : ι, ∑ j : ι,
          a i * a j * covariance (Z i) (Z j) ν := by
    simpa [X] using
      variance_linear_combination_eq_covariance_quadratic ν Z
        (memLp_coordinate_of_jointGaussian ν Z h_joint) a
  -- Identify the one-dimensional Gaussian law by its pushed-forward mean and
  -- variance, then pull those parameters back along `X`.
  have hX_law :
      Measure.map X ν = gaussianReal 0 (Var[X; ν]).toNNReal := by
    haveI : ProbabilityTheory.IsGaussian (Measure.map X ν) := hX_gaussian
    have hX_ae : AEMeasurable X ν :=
      aemeasurable_of_map_neZero (μ := ν) (f := X)
        inferInstance
    calc
      Measure.map X ν
          = gaussianReal (Measure.map X ν)[id]
              (Var[id; Measure.map X ν]).toNNReal :=
            hX_gaussian.eq_gaussianReal (Measure.map X ν)
      _ = gaussianReal ν[X] (Var[X; ν]).toNNReal := by
            rw [MeasureTheory.integral_map hX_ae (by fun_prop),
              ProbabilityTheory.variance_map (by fun_prop) hX_ae]
            rfl
      _ = gaussianReal 0 (Var[X; ν]).toNNReal := by
            simp [hX_mean_zero]
  -- Apply the one-dimensional Gaussian MGF formula and replace the variance by
  -- the covariance quadratic form.
  have hX_mgf :
      (fun t : ℝ ↦ ProbabilityTheory.mgf X ν t) =
        fun t : ℝ ↦ Real.exp ((Var[X; ν] * t ^ 2) / 2) := by
    ext t
    have hvar_coe : ((Var[X; ν]).toNNReal : ℝ) = Var[X; ν] := by
      simp [Real.toNNReal_of_nonneg (ProbabilityTheory.variance_nonneg X ν)]
    rw [ProbabilityTheory.mgf_gaussianReal hX_law t]
    simp [hvar_coe]
  calc
    (fun t : ℝ ↦ ProbabilityTheory.mgf
        (fun ω ↦ ∑ k : ι, a k * Z k ω) ν t)
        = (fun t : ℝ ↦ Real.exp ((Var[X; ν] * t ^ 2) / 2)) := by
          simpa [X] using hX_mgf
    _ = (fun t : ℝ ↦ Real.exp
          (((∑ i : ι, ∑ j : ι,
              a i * a j * covariance (Z i) (Z j) ν) * t ^ 2) / 2)) :=
          funext fun t ↦ by rw [hX_variance]

-- On a two-element block, the cumulant transform is the covariance, which is
-- exactly the symmetric pairing weight.  This separates the finite partition
-- bookkeeping from the higher-order Gaussian coefficient extraction in Isserlis.
private lemma cumulantTransform_pair_eq_pairWeight_covariance {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] (ν : Measure Ω)
    [IsProbabilityMeasure ν] (Z : ι → Ω → ℝ)
    (h_joint : ∀ a : ι → ℝ,
      ProbabilityTheory.IsGaussian
        (Measure.map (fun ω ↦ ∑ k : ι, a k * Z k ω) ν))
    (hsym : ∀ i j : ι, covariance (Z i) (Z j) ν = covariance (Z j) (Z i) ν)
    {B : Finset ι} (hBcard : B.card = 2) :
    Finpartition.cumulantTransform (blockMoment ν Z) B =
      pairWeight (fun k l : ι ↦ covariance (Z k) (Z l) ν) B := by
  classical
  -- First reduce the two-element block to an explicit unordered pair.
  have h_pair_decomp : ∃ i j : ι, i ≠ j ∧ B = ({i, j} : Finset ι) := by
    simpa using (Finset.card_eq_two.mp hBcard)
  rcases h_pair_decomp with ⟨i, j, hij, rfl⟩
  -- The explicit two-block cumulant is the second moment minus the product of
  -- first moments; covariance rewrites this probabilistic expression.
  have h_lhs_cov :
      Finpartition.cumulantTransform (blockMoment ν Z) ({i, j} : Finset ι) =
        covariance (Z i) (Z j) ν := by
    have hMem : ∀ k : ι, MemLp (fun ω ↦ Z k ω) 2 ν :=
      memLp_coordinate_of_jointGaussian ν Z h_joint
    have hiMem : MemLp (fun ω ↦ Z i ω) 2 ν := hMem i
    have hjMem : MemLp (fun ω ↦ Z j ω) 2 ν := hMem j
    have h_cumulant_expand :
        Finpartition.cumulantTransform (blockMoment ν Z) ({i, j} : Finset ι) =
          blockMoment ν Z ({i, j} : Finset ι)
            - blockMoment ν Z ({i} : Finset ι) * blockMoment ν Z ({j} : Finset ι) := by
      dsimp [Finpartition.cumulantTransform]
      rw [if_neg]
      · rw [sum_Finpartition_pair i j hij]
        have hne : ({i, j} : Finset ι).Nonempty := by simp
        rw [cumulantCoefficient_top hne, blockProduct_top hne]
        rw [cumulantCoefficient_bot_pair i j hij]
        rw [blockProduct_bot_pair i j hij]
        ring
      · simp
    have h_pair_moment :
        blockMoment ν Z ({i, j} : Finset ι) =
          ∫ ω, Z i ω * Z j ω ∂ν := by
      dsimp [blockMoment]
      congr 1
      ext ω
      simp [Finset.prod_insert, Finset.prod_singleton, hij]
    have h_single_i :
        blockMoment ν Z ({i} : Finset ι) = ∫ ω, Z i ω ∂ν := by
      dsimp [blockMoment]
      simp
    have h_single_j :
        blockMoment ν Z ({j} : Finset ι) = ∫ ω, Z j ω ∂ν := by
      dsimp [blockMoment]
      simp
    calc
      Finpartition.cumulantTransform (blockMoment ν Z) ({i, j} : Finset ι)
          = blockMoment ν Z ({i, j} : Finset ι)
              - blockMoment ν Z ({i} : Finset ι) * blockMoment ν Z ({j} : Finset ι) :=
            h_cumulant_expand
      _ = (∫ ω, Z i ω * Z j ω ∂ν)
              - (∫ ω, Z i ω ∂ν) * ∫ ω, Z j ω ∂ν := by
            rw [h_pair_moment, h_single_i, h_single_j]
      _ = covariance (Z i) (Z j) ν := by
            exact (covariance_eq_sub hiMem hjMem).symm
  -- The pairing weight averages the two orientations; symmetry identifies them.
  have h_rhs_cov :
      pairWeight (fun k l : ι ↦ covariance (Z k) (Z l) ν) ({i, j} : Finset ι) =
        covariance (Z i) (Z j) ν := by
    exact pairWeight_pair (fun k l : ι ↦ covariance (Z k) (Z l) ν) hsym hij
  exact h_lhs_cov.trans h_rhs_cov.symm

-- Combine the two cardinality branches for a block-local formula.  This keeps
-- analytic proofs focused on the pair and non-pair cases, leaving the `if`
-- bookkeeping to a reusable finite-set helper.
private lemma eq_if_card_two_of_eq_of_ne {ι : Type*}
    (F K : Finset ι → ℝ)
    (h_pair : ∀ {B : Finset ι}, B.card = 2 → F B = K B)
    (h_not_pair : ∀ {B : Finset ι}, B.card ≠ 2 → F B = 0)
    (B : Finset ι) :
    F B = if B.card = 2 then K B else 0 := by
  by_cases hBcard : B.card = 2
  · exact (if_pos hBcard).symm ▸ h_pair hBcard
  · exact (if_neg hBcard).symm ▸ h_not_pair hBcard

/-- Finite-dimensional centered Wick/Isserlis theorem for a jointly Gaussian real family.

This is the analytic theorem missing from the current Mathlib/project API.  The Cramér-Wold
hypothesis `h_joint` says that every real linear combination of the finite family `Z` is Gaussian;
`h_centered` removes the linear term in the multivariate MGF; and `h_integrability` is the moment
side-condition for the product over `s`.  The standard proof derives
`exp ((1 / 2) * ∑ i, ∑ j, t i * t j * covariance (Z i) (Z j) ν)` as the multivariate MGF and
extracts the squarefree coefficient indexed by `s`, which is exactly the Wick pairing sum. -/
private lemma isserlis_centered_jointGaussian_finset {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] (ν : Measure Ω) (Z : ι → Ω → ℝ) (s : Finset ι)
    (h_joint : ∀ a : ι → ℝ,
      ProbabilityTheory.IsGaussian
        (Measure.map (fun ω ↦ ∑ k, a k * Z k ω) ν))
    (h_centered : ∀ k : ι, ∫ ω, Z k ω ∂ν = 0)
    (h_integrability : Integrable (fun ω ↦ ∏ k ∈ s, Z k ω) ν) :
    ∫ ω, ∏ k ∈ s, Z k ω ∂ν =
      wick (fun k l ↦ covariance (Z k) (Z l) ν) s := by
  classical
  let C : ι → ι → ℝ := fun k l ↦ covariance (Z k) (Z l) ν

  -- Step 1: analytic Gaussian input.  From the Cramér-Wold hypothesis `h_joint`,
  -- the finite vector `(Z k)_{k : ι}` is jointly Gaussian.  Since `h_centered`
  -- makes all first moments vanish, its multivariate MGF is
  --   `exp ((1 / 2) * ∑ i, ∑ j, t i * t j * C i j)`.
  -- Differentiating once in each squarefree direction indexed by `s` and using
  -- `h_integrability` to justify the moment gives the pairing expansion below.
  -- This is the missing finite-dimensional Wick/Isserlis theorem.
  have h_pairing_formula :
      ∫ ω, ∏ k ∈ s, Z k ω ∂ν =
        Finpartition.pairingSum (pairWeight C) s := by
    -- Work on the subtype of indices actually appearing in the product.  This
    -- isolates the genuinely finite-dimensional vector whose full mixed moment
    -- is being computed.
    let σ := {k : ι // k ∈ s}
    let Zs : σ → Ω → ℝ := fun k ω ↦ Z k.1 ω

    -- The Cramér-Wold, centering, and integrability hypotheses all restrict to
    -- the subtype of indices in `s`; the helpers isolate this bookkeeping so the
    -- remaining proof can focus on the analytic Isserlis input.
    have h_joint_s : ∀ a : σ → ℝ,
        ProbabilityTheory.IsGaussian
          (Measure.map (fun ω ↦ ∑ k : σ, a k * Zs k ω) ν) :=
      jointGaussian_restrict_finset_subtype ν Z s h_joint

    have h_centered_s : ∀ k : σ, ∫ ω, Zs k ω ∂ν = 0 :=
      centered_restrict_finset_subtype ν Z s h_centered

    -- Analytic Wick/Isserlis input on the restricted finite vector.  This is the
    -- missing theorem: from `h_joint_s`, `h_centered_s`, and `h_integrability_s`,
    -- derive the multivariate Gaussian MGF `exp (1 / 2 * tᵀ C t)` and extract the
    -- coefficient of the squarefree monomial containing every subtype index.
    have h_isserlis_subtype :
        ∫ ω, ∏ k : σ, Zs k ω ∂ν =
          Finpartition.pairingSum
            (pairWeight (fun k l : σ ↦ covariance (Zs k) (Zs l) ν))
            Finset.univ := by
      -- This is the finite-dimensional centered Isserlis theorem for the subtype
      -- family.  We record the standard proof as a chain of reusable subgoals:
      -- compute the centered Gaussian MGF of every linear combination, translate
      -- that MGF computation into the statement that all cumulants except the
      -- quadratic ones vanish, and then apply the moment-cumulant inversion.
      let K : Finset σ → ℝ :=
        pairWeight (fun k l : σ ↦ covariance (Zs k) (Zs l) ν)

      -- The zero linear combination supplies the probability normalization
      -- required by moment-cumulant inversion.
      haveI : IsProbabilityMeasure ν :=
        isProbabilityMeasure_of_jointGaussian_zero_linear ν Zs h_joint_s

      -- Analytic Gaussian input: Cramér-Wold plus centering gives the
      -- multivariate MGF `exp ((t^2 / 2) * aᵀ C a)` for each direction `a`.
      have h_mgf_linear :
          ∀ a : σ → ℝ,
            (fun t : ℝ ↦ ProbabilityTheory.mgf
                (fun ω ↦ ∑ k : σ, a k * Zs k ω) ν t) =
              (fun t : ℝ ↦ Real.exp
                (((∑ i : σ, ∑ j : σ,
                    a i * a j * covariance (Zs i) (Zs j) ν) * t ^ 2) / 2)) :=
        mgf_linear_combination_centered_jointGaussian ν Zs h_joint_s h_centered_s

      -- Coefficient extraction from the logarithm of the MGF: the only nonzero
      -- joint cumulants of a centered Gaussian vector are the second cumulants,
      -- and on a two-element block the cumulant is exactly the covariance weight.
      have h_cumulant_blocks :
          ∀ B : Finset σ,
            Finpartition.cumulantTransform (blockMoment ν Zs) B =
              if B.card = 2 then K B else 0 := fun B ↦ by
        -- Second-order coefficient extraction.  If `B = {i,j}`, the mixed
        -- second derivative of `log M(a)` is the coefficient of `a i * a j` in
        -- `(1 / 2) * ∑ p q, a p * a q * cov[Zs p,Zs q]`, namely the covariance.
        -- Formally, one first rewrites the block cumulant as a two-variable
        -- joint cumulant (`blockCumulant_eq_jointCumulant_subtype`), applies
        -- `jointCumulant_two_eq_covariance`, and finally uses `pairWeight_pair`
        -- together with `h_cov_symm`.
        have h_pair_from_cgf :
            (∀ a : σ → ℝ,
              (fun t : ℝ ↦ ProbabilityTheory.mgf
                  (fun ω ↦ ∑ k : σ, a k * Zs k ω) ν t) =
                (fun t : ℝ ↦ Real.exp
                  (((∑ i : σ, ∑ j : σ,
                      a i * a j * covariance (Zs i) (Zs j) ν) * t ^ 2) / 2))) →
            (∀ i j : σ,
              covariance (Zs i) (Zs j) ν = covariance (Zs j) (Zs i) ν) →
            ∀ {B : Finset σ}, B.card = 2 →
              Finpartition.cumulantTransform (blockMoment ν Zs) B = K B := by
          intro _hmgf hsym B hBcard
          dsimp [K]
          exact cumulantTransform_pair_eq_pairWeight_covariance ν Zs h_joint_s hsym hBcard

        -- Non-quadratic coefficient extraction.  The same logarithmic MGF is a
        -- homogeneous quadratic polynomial in the coefficients `a`; hence every
        -- squarefree mixed derivative of order other than two vanishes.  The
        -- order-one case is also zero because the coordinates are centered.
        have h_not_pair_from_cgf :
            (∀ a : σ → ℝ,
              (fun t : ℝ ↦ ProbabilityTheory.mgf
                  (fun ω ↦ ∑ k : σ, a k * Zs k ω) ν t) =
                (fun t : ℝ ↦ Real.exp
                  (((∑ i : σ, ∑ j : σ,
                      a i * a j * covariance (Zs i) (Zs j) ν) * t ^ 2) / 2))) →
            (∀ k : σ, ∫ ω, Zs k ω ∂ν = 0) →
            ∀ {B : Finset σ}, B.card ≠ 2 →
              Finpartition.cumulantTransform (blockMoment ν Zs) B = 0 := by
          intro hmgf hcent B hBcard
          -- TODO: split on `B.card`.  For `0`, unfold
          -- `Finpartition.cumulantTransform` and use the empty-block convention;
          -- for `1`, rewrite as `jointCumulant_one` and use `hcent`; for
          -- cardinality at least `3`, all mixed derivatives of the quadratic
          -- cumulant generating function supplied by `hmgf` vanish.
          sorry

        exact eq_if_card_two_of_eq_of_ne
          (Finpartition.cumulantTransform (blockMoment ν Zs)) K
          (h_pair_from_cgf h_mgf_linear (fun i j ↦ covariance_comm (Zs i) (Zs j)))
          (h_not_pair_from_cgf h_mgf_linear h_centered_s) B

      -- Moment-cumulant inversion expresses the full moment as the partition
      -- transform of the block cumulants.  The explicit integrability hypothesis
      -- `h_integrability_s` is the side condition for the left-hand moment.
      have h_moment_cumulant :
          ∫ ω, ∏ k : σ, Zs k ω ∂ν =
            Finpartition.partitionTransform
              (Finpartition.cumulantTransform (blockMoment ν Zs))
              (Finset.univ : Finset σ) := by
        rw [partitionTransform_cumulantTransform_univ
          (blockMoment ν Zs) (blockMoment_empty Zs)]
        simp [blockMoment]

      -- If the block weight is zero away from two-element blocks, then the
      -- partition transform restricts exactly to pair partitions, i.e. to the
      -- project's `pairingSum`.
      have h_partition_to_pairings :
          Finpartition.partitionTransform
              (fun B : Finset σ ↦ if B.card = 2 then K B else 0)
              (Finset.univ : Finset σ) =
            Finpartition.pairingSum K (Finset.univ : Finset σ) := by
        -- Expand `Finpartition.partitionTransform`; every partition containing a
        -- block of cardinality different from two has product zero, while the
        -- remaining partitions are precisely `Finpartition.Pairing`.
        sorry

      rw [h_moment_cumulant, funext h_cumulant_blocks]
      simpa [K] using h_partition_to_pairings

    -- Transport the subtype statement back to the original finset `s`.  The left
    -- side is just the same product, and the right side is the same sum over
    -- pairings after relabelling blocks by the subtype equivalence.
    calc
      ∫ ω, ∏ k ∈ s, Z k ω ∂ν = ∫ ω, ∏ k : σ, Zs k ω ∂ν := by
        -- Pointwise reindex the product over `s` by the subtype `σ`.
        rw [funext (prod_finset_eq_prod_subtype Z s)]
      _ = Finpartition.pairingSum (pairWeight fun k l : σ ↦ covariance (Zs k) (Zs l) ν)
            Finset.univ := h_isserlis_subtype
      _ = Finpartition.pairingSum (pairWeight C) s := by
        -- Relabel pairings of `Finset.univ : Finset σ` as pairings of `s` by
        -- the subtype-value equivalence.  Block weights agree by unfolding `C`
        -- and `Zs`; covariance symmetry handles unordered blocks.
        sorry

  -- Step 2: unfold the local definition of the Wick sum.  The previous step is
  -- already expressed with exactly the block weight used by `wick`.
  simpa [wick, C] using h_pairing_formula

/-- Finite-dimensional centered Gaussian Stein identity for a product of coordinates.

This is the genuine analytic input needed by `integral_mul_prod_centered_dual_eq_sum`.
The hypotheses say that `Y0, Y i` are a centered jointly Gaussian real vector and that the
full and erased products are integrable.  The usual proof differentiates the centered Gaussian
MGF, or equivalently applies Wick/Isserlis and separates the unique partner of `Y0`. -/
private lemma gaussian_stein_product_centered {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) {n : ℕ} (Y0 : Ω → ℝ) (Y : Fin n → Ω → ℝ)
    (h_joint : ∀ (a0 : ℝ) (a : Fin n → ℝ),
      ProbabilityTheory.IsGaussian
        (Measure.map (fun ω ↦ a0 * Y0 ω + ∑ i, a i * Y i ω) ν))
    (h_integrability : Integrable (fun ω ↦ Y0 ω * ∏ i, Y i ω) ν)
    (h_erased_integrability : ∀ j : Fin n,
      Integrable (fun ω ↦ ∏ i ∈ Finset.univ.erase j, Y i ω) ν)
    (h_centered_means : (∫ ω, Y0 ω ∂ν = 0) ∧
      (∀ i : Fin n, ∫ ω, Y i ω ∂ν = 0)) :
    ∫ ω, Y0 ω * ∏ i, Y i ω ∂ν =
      ∑ j, covariance Y0 (Y j) ν *
        ∫ ω, ∏ i ∈ Finset.univ.erase j, Y i ω ∂ν := by
  classical
  -- Package the distinguished variable and the `n` coordinate variables into one
  -- finite family.  Using `Option (Fin n)` keeps the distinguished coordinate
  -- definitionally separate from the remaining coordinates.
  let Z : Option (Fin n) → Ω → ℝ := fun k ω ↦
    match k with
    | none => Y0 ω
    | some i => Y i ω
  let C : Option (Fin n) → Option (Fin n) → ℝ := fun k l ↦ covariance (Z k) (Z l) ν
  -- Step 1 (analytic input): the scalar Cramér-Wold hypothesis `h_joint` gives
  -- the usual finite-dimensional centered Gaussian vector `Z`, hence its mixed
  -- moments are given by the Wick/Isserlis pairing formula.  Formally this is
  -- the theorem missing from Mathlib/project API: derive the multivariate MGF
  -- `exp (1 / 2 * tᵀ C t)` from `h_joint`, use `h_centered_means` for the zero
  -- linear term, and differentiate at the origin.  The supplied integrability
  -- hypotheses justify the displayed moments for the two products used below.
  have h_stein_for_Z :
      ∫ ω, Z none ω * ∏ i : Fin n, Z (some i) ω ∂ν =
        ∑ j : Fin n, C none (some j) *
          ∫ ω, ∏ i ∈ Finset.univ.erase j, Z (some i) ω ∂ν := by
    -- This is exactly Gaussian integration by parts / Wick recurrence for the
    -- centered jointly Gaussian finite family `Z`, applied to the monomial
    -- `fun z ↦ ∏ i, z (some i)`.  The following skeleton isolates the two genuine
    -- mathematical inputs and leaves only finite `Option`/`Finset` bookkeeping.
    -- The covariance kernel used in the Wick pairing sum is symmetric.
    have hC_symm : ∀ k l : Option (Fin n), C k l = C l k := fun k l ↦ by
      dsimp [C]
      exact covariance_comm (Z k) (Z l)
    -- Repackage the original Cramér-Wold hypothesis as joint Gaussianity of the
    -- `Option (Fin n)`-indexed family.  The proof expands the `Option`-sum into
    -- the distinguished coefficient and the `some i` coefficients.
    -- Use `h_joint (a none) (fun i ↦ a (some i))` and simplify the finite sum
    -- over `Option (Fin n)` into the `none` term plus the `some` terms.
    have h_joint_Z : ∀ a : Option (Fin n) → ℝ,
        ProbabilityTheory.IsGaussian
          (Measure.map (fun ω ↦ ∑ k : Option (Fin n), a k * Z k ω) ν) :=
      fun a ↦ by simpa [Z, Fintype.sum_option] using h_joint (a none) (fun i ↦ a (some i))
    -- The same repackaging applies to the centering assumptions.
    have h_centered_Z : ∀ k : Option (Fin n), ∫ ω, Z k ω ∂ν = 0
      | none => by simpa [Z] using h_centered_means.1
      | some i => by simpa [Z] using h_centered_means.2 i
    -- Analytic Wick/Isserlis theorem for the full product.  The top-level lemma
    -- above isolates the missing finite-dimensional Gaussian analysis; this
    -- block only rewrites the product over `Option (Fin n)` into the distinguished
    -- `none` factor and the product over the `some` coordinates.
    have h_full_wick :
        ∫ ω, Z none ω * ∏ i : Fin n, Z (some i) ω ∂ν =
          wick C (Finset.univ : Finset (Option (Fin n))) := by
      have h_prod_univ :
          ∫ ω, ∏ k ∈ (Finset.univ : Finset (Option (Fin n))), Z k ω ∂ν =
            wick C (Finset.univ : Finset (Option (Fin n))) := by
        simpa [C] using
          isserlis_centered_jointGaussian_finset ν Z
            (Finset.univ : Finset (Option (Fin n))) h_joint_Z h_centered_Z
            (by simpa [Z, Fintype.prod_option] using h_integrability)
      simpa [Fintype.prod_option] using h_prod_univ
    -- Analytic Wick/Isserlis theorem for every erased product.  These are the
    -- lower-order moments left after pairing `none` with `some j`; the only
    -- bookkeeping is that erasing `none` and `some j` from `univ : Finset (Option (Fin n))`
    -- leaves exactly the embedded set of indices `some i` with `i ≠ j`.
    have h_erased_wick : ∀ j : Fin n,
        wick C (((Finset.univ : Finset (Option (Fin n))).erase none).erase (some j)) =
          ∫ ω, ∏ i ∈ Finset.univ.erase j, Z (some i) ω ∂ν := by
      intro j
      have h_prod_erased :
          ∫ ω, ∏ k ∈ (((Finset.univ : Finset (Option (Fin n))).erase none).erase (some j)),
              Z k ω ∂ν =
            wick C (((Finset.univ : Finset (Option (Fin n))).erase none).erase (some j)) := by
        simpa [C] using
          isserlis_centered_jointGaussian_finset ν Z
            (((Finset.univ : Finset (Option (Fin n))).erase none).erase (some j))
            h_joint_Z h_centered_Z
            (by
              -- Finite-product reindexing side condition: the product over
              -- `univ.erase none |>.erase (some j)` is the same as the product
              -- over `Finset.univ.erase j` after the embedding `Option.some`.
              -- Together with `Z (some i) = Y i`, this is exactly
              -- `h_erased_integrability j`.
              have h_prod_eq : ∀ ω,
                  (∏ k ∈
                      (((Finset.univ : Finset (Option (Fin n))).erase none).erase (some j)),
                    Z k ω) =
                    ∏ i ∈ Finset.univ.erase j, Z (some i) ω := by
                intro ω
                symm
                refine Finset.prod_bij (fun i _ ↦ some i) ?_ ?_ ?_ ?_
                · intro i hi
                  simp only [Finset.mem_erase, ne_eq, Option.some.injEq, reduceCtorEq,
                    not_false_eq_true, Finset.mem_univ, and_self, and_true] at hi ⊢
                  exact hi
                · intro i₁ _ i₂ _ h
                  cases h
                  rfl
                · intro b hb
                  rcases b with _ | i
                  · simp at hb
                  · exact ⟨i, by simpa using hb, rfl⟩
                · intro i _
                  rfl
              simpa [h_prod_eq] using h_erased_integrability j)
      rw [← h_prod_erased]
      -- Same finite-set reindexing as above, now at the level of the integral.
      -- The map is the equivalence between `Finset.univ.erase j` and
      -- `((univ : Finset (Option (Fin n))).erase none).erase (some j)` induced by `Option.some`.
      have h_prod_eq : ∀ ω,
          (∏ k ∈ (((Finset.univ : Finset (Option (Fin n))).erase none).erase (some j)),
            Z k ω) =
            ∏ i ∈ Finset.univ.erase j, Z (some i) ω := by
        intro ω
        symm
        refine Finset.prod_bij (fun i _ ↦ some i) ?_ ?_ ?_ ?_
        · intro i hi
          simp only [Finset.mem_erase, ne_eq, Option.some.injEq, reduceCtorEq,
            not_false_eq_true, Finset.mem_univ, and_self, and_true] at hi ⊢
          exact hi
        · intro i₁ _ i₂ _ h
          cases h
          rfl
        · intro b hb
          rcases b with _ | i
          · simp at hb
          · exact ⟨i, by simpa using hb, rfl⟩
        · intro i _
          rfl
      simp_rw [h_prod_eq]
    -- Pure finite-set bookkeeping: summing over all partners of `none` in
    -- `Option (Fin n)` is the same as summing over `j : Fin n` with partner
    -- `some j`.
    have h_partner_sum :
        (∑ b ∈ (Finset.univ : Finset (Option (Fin n))).erase none,
            C none b * wick C (((Finset.univ : Finset (Option (Fin n))).erase none).erase b)) =
          ∑ j : Fin n,
            C none (some j) *
              wick C (((Finset.univ : Finset (Option (Fin n))).erase none).erase (some j)) := by
      -- The set `(univ : Finset (Option (Fin n))).erase none` contains exactly
      -- the elements `some j`; reindex the left sum by `Option.some`.
      refine Finset.sum_bij (fun b hb => ?_) ?_ ?_ ?_ ?_
      · rcases b with _ | j
        · simp at hb
        · exact j
      · intro b hb
        simp
      · intro b₁ hb₁ b₂ hb₂ h
        rcases b₁ with _ | j₁
        · simp at hb₁
        rcases b₂ with _ | j₂
        · simp at hb₂
        simpa using congrArg Option.some h
      · intro j _hj
        exact ⟨some j, by simp, rfl⟩
      · intro b hb
        rcases b with _ | _
        · simp at hb
        · rfl
    calc
      ∫ ω, Z none ω * ∏ i : Fin n, Z (some i) ω ∂ν
          = wick C (Finset.univ : Finset (Option (Fin n))) := h_full_wick
      _ = ∑ b ∈ (Finset.univ : Finset (Option (Fin n))).erase none,
            C none b * wick C (((Finset.univ : Finset (Option (Fin n))).erase none).erase b) :=
          wick_erase C hC_symm (Finset.univ : Finset (Option (Fin n))) (by simp)
      _ = ∑ j : Fin n,
            C none (some j) *
              wick C (((Finset.univ : Finset (Option (Fin n))).erase none).erase (some j)) :=
          h_partner_sum
      _ = ∑ j : Fin n, C none (some j) *
            ∫ ω, ∏ i ∈ Finset.univ.erase j, Z (some i) ω ∂ν := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [h_erased_wick j]
  -- Step 2 (definition unfolding): after expanding `Z` and `C`, the abstract
  -- finite-family identity is syntactically the desired statement.
  simpa [Z, C] using h_stein_for_Z

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
        ∫ x, ∏ i ∈ Finset.univ.erase j, centeredDual μ (K i) x ∂μ :=
  (gaussian_stein_product_centered μ (centeredDual μ L)
    (fun i ↦ centeredDual μ (K i))
    (fun a₀ a ↦ isGaussian_map_centeredDual_linearCombination μ L K a₀ a)
    (integrable_centeredDual_mul_prod μ L K)
    (fun j ↦ integrable_finset_prod_centeredDual μ (Finset.univ.erase j) K)
    ⟨integral_centeredDual_eq_zero μ L, fun i ↦ integral_centeredDual_eq_zero μ (K i)⟩).trans
    (Finset.sum_congr rfl fun j _ ↦ by
      rw [covariance_centeredDual_eq_dualCovariance μ L (K j)])


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
  have h_joint : ∀ a : Fin n → ℝ,
      ProbabilityTheory.IsGaussian
        (Measure.map (fun x ↦ ∑ k, a k * centeredDual μ (L k) x) μ) := by
    intro a
    simpa using
      isGaussian_map_centeredDual_linearCombination μ (0 : StrongDual ℝ E) L 0 a
  have h_moment :
      ∫ x, ∏ k ∈ (Finset.univ : Finset (Fin n)), centeredDual μ (L k) x ∂μ =
        wick (fun k l ↦ covariance (centeredDual μ (L k)) (centeredDual μ (L l)) μ)
          (Finset.univ : Finset (Fin n)) :=
    isserlis_centered_jointGaussian_finset μ (fun k x ↦ centeredDual μ (L k) x)
      (Finset.univ : Finset (Fin n)) h_joint
      (fun k ↦ integral_centeredDual_eq_zero μ (L k))
      (integrable_finset_prod_centeredDual μ (Finset.univ : Finset (Fin n)) L)
  calc
    jointMoment μ (fun i ↦ centeredDual μ (L i)) =
        ∫ x, ∏ k ∈ (Finset.univ : Finset (Fin n)), centeredDual μ (L k) x ∂μ := by
          simp [jointMoment, blockMoment]
    _ = wick (fun k l ↦ covariance (centeredDual μ (L k)) (centeredDual μ (L l)) μ)
          (Finset.univ : Finset (Fin n)) := h_moment
    _ = wick (fun i j ↦ dualCovariance μ (L i) (L j)) Finset.univ := by
          congr 1
          funext i j
          exact covariance_centeredDual_eq_dualCovariance μ (L i) (L j)

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
components of the moments. Since `wick C` is a sum over pairings (blocks of size 2),
the only non-zero connected component of size `n` occurs when `n = 2` and the partition
is just a single pair.
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
  classical
  let C : Fin n → Fin n → ℝ := fun i j ↦ dualCovariance μ (L i) (L j)
  have h_blocks : blockMoment μ (fun i ↦ centeredDual μ (L i)) = wick C := by
    funext B
    have h_joint : ∀ a : Fin n → ℝ,
        ProbabilityTheory.IsGaussian
          (Measure.map (fun x ↦ ∑ k, a k * centeredDual μ (L k) x) μ) := by
      intro a
      simpa using
        isGaussian_map_centeredDual_linearCombination μ (0 : StrongDual ℝ E) L 0 a
    have h_moment :
        ∫ x, ∏ k ∈ B, centeredDual μ (L k) x ∂μ =
          wick (fun k l ↦ covariance (centeredDual μ (L k)) (centeredDual μ (L l)) μ) B :=
      isserlis_centered_jointGaussian_finset μ (fun k x ↦ centeredDual μ (L k) x) B
        h_joint (fun k ↦ integral_centeredDual_eq_zero μ (L k))
        (integrable_finset_prod_centeredDual μ B L)
    calc
      blockMoment μ (fun i ↦ centeredDual μ (L i)) B =
          ∫ x, ∏ k ∈ B, centeredDual μ (L k) x ∂μ := rfl
      _ = wick (fun k l ↦ covariance (centeredDual μ (L k)) (centeredDual μ (L l)) μ) B :=
          h_moment
      _ = wick C B := by
          congr 1
          funext i j
          exact covariance_centeredDual_eq_dualCovariance μ (L i) (L j)
  dsimp [jointCumulant, blockCumulant]
  rw [h_blocks]
  exact cumulantTransform_wick_eq_zero C
    (fun i j ↦ dualCovariance_comm μ (L i) (L j)) (by simpa using hn)

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
  have hcard : 1 < Fintype.card (Fin n) := by
    simp
    omega
  let X : Fin n → E → ℝ := fun i x ↦ centeredDual μ (L i) x
  let c : Fin n → ℝ := fun i ↦ ∫ y, L i y ∂μ
  have htranslate :
      jointCumulant μ (fun i x ↦ X i x + c i) = jointCumulant μ X :=
    jointCumulant_add_const (μ := μ) hcard X c
  have hpoint : (fun i x ↦ X i x + c i) = (fun i x ↦ L i x) := by
    funext i x
    simp [X, c, centeredDual]
  calc
    jointCumulant μ (fun i x ↦ L i x)
        = jointCumulant μ (fun i x ↦ X i x + c i) := by
            rw [hpoint]
    _ = jointCumulant μ X := htranslate
    _ = 0 := by
        have hn_ne : n ≠ 2 := by omega
        simpa [X] using jointCumulant_centered_dual_eq_zero μ hn_ne L

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
  let L : Fin n → StrongDual ℝ (EuclideanSpace ℝ κ) := fun r ↦ EuclideanSpace.proj (index r)
  have hwick := Renormalization.IsGaussian.integral_prod_centered_dual_eq_wick
    (μ := multivariateGaussian m S) L
  have hcenter :
      (fun r z ↦ centeredDual (multivariateGaussian m S) (L r) z) =
        (fun r z ↦ z (index r) - m (index r)) := by
    funext r z
    have hmean_coord :
        ∫ y, y.ofLp (index r) ∂multivariateGaussian m S = m.ofLp (index r) := by
      have hmean_vec : ∫ y, y ∂multivariateGaussian m S = m :=
        ProbabilityTheory.integral_id_multivariateGaussian (μ := m) (S := S)
      let P : (EuclideanSpace ℝ κ) →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) (index r)
      have hcomm :
          ∫ y, P y ∂multivariateGaussian m S = P (∫ y, y ∂multivariateGaussian m S) := by
        exact ContinuousLinearMap.integral_comp_comm P
          (ProbabilityTheory.IsGaussian.integrable_id (μ := multivariateGaussian m S))
      calc
        ∫ y, y.ofLp (index r) ∂multivariateGaussian m S =
            ∫ y, P y ∂multivariateGaussian m S := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with y
          rfl
        _ = P (∫ y, y ∂multivariateGaussian m S) := hcomm
        _ = m.ofLp (index r) := by
          rw [hmean_vec]
          rfl
    simp [centeredDual, L, hmean_coord]
  have hcov : ∀ r q : Fin n,
      dualCovariance (multivariateGaussian m S) (L r) (L q) = S (index r) (index q) := by
    intro r q
    unfold dualCovariance
    simpa [L] using ProbabilityTheory.covariance_eval_multivariateGaussian (μ := m) (S := S) hS
      (index r) (index q)
  rw [hcenter] at hwick
  convert hwick using 2
  ext r q
  exact (hcov r q).symm

end Renormalization

end

end
