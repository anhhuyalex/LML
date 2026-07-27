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
    ext t; simp [mgf_fun_id_gaussianReal]
  rw [← h_mgf, iteratedDeriv_mgf_zero] <;> simp

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
          simpa using (hasDerivAt_pow 2 t : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℝ) * t ^ (2 - 1)) t)
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
      simpa [mul_assoc] using
        (iteratedDeriv_const_mul_field (n := n + 1) (x := (0 : ℝ))
          (c := v) (f := fun t : ℝ ↦ t * f t))

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
        simpa using h_base
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
For a 1D real Gaussian measure with mean 0 and variance `v`, the expectation of `x * x^n` is given by integration by parts.
Specifically, `∫ x, x * x^n dN(0, v) = ∫ x, x^(n+1) dN(0, v) = v * n * ∫ x, x^(n-1) dN(0, v)`.
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
  -- Step 1: Package the observables as a finite centered Gaussian vector.
  -- A future proof should define the map
  --   `x ↦ (centeredDual μ L x, fun i ↦ centeredDual μ (K i) x)`
  -- into a finite-dimensional real space.  Any linear combination of its
  -- coordinates is a centered translate of a continuous linear functional of
  -- `x`, hence is Gaussian by `ProbabilityTheory.IsGaussian.map_eq_gaussianReal`.
  have h_joint_gaussian : ∀ (a₀ : ℝ) (a : Fin n → ℝ),
      ProbabilityTheory.IsGaussian (Measure.map (fun x ↦ a₀ * centeredDual μ L x + ∑ i, a i * centeredDual μ (K i) x) μ) := by
    intro a₀ a
    -- Combine the finitely many continuous linear functionals into one
    -- continuous linear functional.  Its centered pushforward is the displayed
    -- scalar linear combination of centered observables.
    let H : StrongDual ℝ E := a₀ • L + ∑ i, a i • K i
    let c : ℝ := a₀ * (∫ y, L y ∂μ) + ∑ i, a i * (∫ y, K i y ∂μ)

    -- Step 1.  Pointwise algebra: the requested linear combination is an
    -- affine translate of the single continuous linear observable `H`.
    have h_pointwise :
        (fun x ↦ a₀ * centeredDual μ L x + ∑ i, a i * centeredDual μ (K i) x)
          = (fun x ↦ H x - c) := by
      -- This is only pointwise algebra: unfold the centering definition and
      -- the local linear combination, then normalize the finite-sum identity.
      funext x
      simp [centeredDual, H, c]
      ring_nf
      rw [Finset.sum_sub_distrib]
      ring

    -- Step 2.  A Gaussian measure remains Gaussian after pushing forward by a
    -- continuous linear functional.  Here the functional is `H`.
    have h_linear_gaussian :
        ProbabilityTheory.IsGaussian (Measure.map (fun x ↦ H x) μ) := by
      -- This is supplied by Mathlib's Gaussian pushforward instance for maps
      -- by continuous linear maps.  The displayed function is eta-equivalent
      -- to the bundled functional `H : StrongDual ℝ E`.
      change ProbabilityTheory.IsGaussian (Measure.map H μ)
      infer_instance

    -- Step 3.  Translating a real Gaussian random variable by the constant `c`
    -- preserves Gaussianity.
    have h_translated_gaussian :
        ProbabilityTheory.IsGaussian
          (Measure.map (fun y : ℝ ↦ y - c) (Measure.map (fun x ↦ H x) μ)) := by
      -- Install the already-proved Gaussianity of the intermediate real law as
      -- a local instance.  Mathlib has an `IsGaussian` instance saying that the
      -- pushforward of a Gaussian measure by `fun y ↦ y - c` is Gaussian.
      haveI : ProbabilityTheory.IsGaussian (Measure.map (fun x ↦ H x) μ) :=
        h_linear_gaussian
      infer_instance

    -- Step 4.  Identify the affine map from `E` with the composition of first
    -- applying `H` and then translating by `-c`.
    have h_map_comp :
        Measure.map (fun x ↦ H x - c) μ =
          Measure.map (fun y : ℝ ↦ y - c) (Measure.map (fun x ↦ H x) μ) := by
      -- This is functoriality of pushforward measures.  The map `x ↦ H x`
      -- is measurable because `H` is a continuous linear functional, and the
      -- real translation `y ↦ y - c` is measurable because it is continuous.
      have hf : Measurable (fun x : E ↦ H x) := H.continuous.measurable
      have hg : Measurable (fun y : ℝ ↦ y - c) :=
        (continuous_id.sub continuous_const).measurable
      simpa [Function.comp_def] using
        (Measure.map_map (μ := μ) (f := fun x : E ↦ H x) (g := fun y : ℝ ↦ y - c)
          hg hf).symm

    rw [h_pointwise, h_map_comp]
    exact h_translated_gaussian

  -- Step 2: Record the analytic side conditions.  These are not visible in the
  -- final equality because Mathlib's Bochner integral is total, but they are
  -- needed to justify integration-by-parts and all algebraic manipulations of
  -- the integrals.  They follow from Gaussian finite moments for continuous
  -- linear functionals and finite-product Hölder estimates.
  have h_integrability : Integrable (fun x ↦ centeredDual μ L x * ∏ i, centeredDual μ (K i) x) μ := by
    -- Sketch: use `ProbabilityTheory.IsGaussian.memLp_dual` for each `L` and
    -- `K i`; constants are in every finite `Lᵖ`, so centered observables are
    -- also in finite `Lᵖ`; then apply Hölder to the finite products.
    sorry

  -- Step 3: Apply the finite-dimensional Gaussian Stein identity to the vector
  -- from Step 1 with the polynomial `p(y) = ∏ i, y i`.  Its derivative in the
  -- `j`-th coordinate is exactly the product with the `j`-th factor erased.
  have h_finite_dimensional_stein :
      ∫ x, centeredDual μ L x * ∏ i, centeredDual μ (K i) x ∂μ =
        ∑ j, dualCovariance μ L (K j) *
          ∫ x, ∏ i ∈ Finset.univ.erase j, centeredDual μ (K i) x ∂μ := by
    -- Sketch of the missing lemma: if `(Y₀, Y₁, ..., Yₙ)` is centered jointly
    -- Gaussian, then
    --   `E[Y₀ * ∏ i, Yᵢ] = ∑ j, Cov(Y₀,Yⱼ) * E[∏ i≠j, Yᵢ]`.
    -- Prove it from the multivariate Gaussian MGF
    --   `M(t) = exp (1 / 2 * tᵀ Γ t)`
    -- by differentiating first in `t₀`, then in all remaining coordinates.
    -- The covariance of the centered variables is `dualCovariance μ L (K j)`;
    -- subtracting constants does not change covariance.
    sorry

  -- Step 4: This is exactly the desired recurrence in the original notation.
  exact h_finite_dimensional_stein

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
  -- Step 1: the covariance kernel is symmetric, so the combinatorial Wick recurrence applies.
  have hC : ∀ i j : Fin n,
      dualCovariance μ (L i) (L j) = dualCovariance μ (L j) (L i) := by
    intro i j
    unfold dualCovariance
    exact covariance_comm (fun x ↦ L i x) (fun x ↦ L j x)

  -- Step 2: unfold the local definition of `jointMoment` into the integral of the full product.
  -- This is the analytic object controlled by Gaussian integration by parts.
  have h_joint_def :
      jointMoment μ (fun i ↦ centeredDual μ (L i)) =
        ∫ x, ∏ i, centeredDual μ (L i) x ∂μ := by
    simp [jointMoment, blockMoment]

  -- Step 3: record the already-proved Stein / Gaussian integration-by-parts recurrence.
  -- This is the moment recurrence: after separating one factor, the moment is a sum over
  -- choices of its partner, weighted by the covariance, times the smaller centered moment.
  have h_stein : ∀ {m : ℕ} (A : StrongDual ℝ E) (K : Fin m → StrongDual ℝ E),
      ∫ x, centeredDual μ A x * ∏ i, centeredDual μ (K i) x ∂μ =
        ∑ j, dualCovariance μ A (K j) *
          ∫ x, ∏ i ∈ Finset.univ.erase j, centeredDual μ (K i) x ∂μ := by
    intro m A K
    exact integral_mul_prod_centered_dual_eq_sum μ A K

  -- Step 4: record the matching Wick recurrence, obtained by choosing the partner of a
  -- distinguished index in a pairing.
  have h_wick_rec : ∀ {m : ℕ} (K : Fin m → StrongDual ℝ E) (a : Fin m),
      wick (fun i j ↦ dualCovariance μ (K i) (K j)) Finset.univ =
        ∑ b ∈ (Finset.univ : Finset (Fin m)).erase a,
          dualCovariance μ (K a) (K b) *
            wick (fun i j ↦ dualCovariance μ (K i) (K j))
              (((Finset.univ : Finset (Fin m)).erase a).erase b) := by
    intro m K a
    have hCK : ∀ i j : Fin m,
        dualCovariance μ (K i) (K j) = dualCovariance μ (K j) (K i) := by
      intro i j
      unfold dualCovariance
      exact covariance_comm (fun x ↦ K i x) (fun x ↦ K j x)
    exact wick_erase (fun i j ↦ dualCovariance μ (K i) (K j)) hCK
      (Finset.univ : Finset (Fin m)) (by simp)

  -- Step 5: prove the theorem by induction on the number of observables.
  -- Induction sketch:
  -- * `n = 0`: `jointMoment_zero` gives the left side as `1`; the empty pairing sum is also `1`.
  -- * `n = 1`: separate the only centered factor and use centering / Stein with an empty product;
  --   the Wick sum is zero because there are no pairings.
  -- * successor step: choose a distinguished index `a` (typically `0 : Fin (m+1)`).  Rewrite the
  --   product as `centeredDual μ (K a) *` the product over the remaining indices, apply `h_stein`,
  --   then apply the induction hypothesis to each smaller integral.  The resulting finite sum is
  --   identified with the right-hand side by `h_wick_rec`.
  -- The remaining proof work is bookkeeping: reindexing products over
  -- `Finset.univ.erase a` and `((Finset.univ.erase a).erase b)` as products over smaller `Fin`
  -- types, plus the definitional bridge `h_joint_def`.
  have h_induction : ∀ {m : ℕ} (K : Fin m → StrongDual ℝ E),
      jointMoment μ (fun i ↦ centeredDual μ (K i)) =
        wick (fun i j ↦ dualCovariance μ (K i) (K j)) Finset.univ := by
    intro m K
    -- Use `h_stein` for the analytic recurrence and `h_wick_rec` for the combinatorial one.
    -- The hard sublemmas needed here are product/Finset reindexing lemmas for erasing one or two
    -- indices from `Fin (m+1)` and identifying the resulting integrals with lower-order
    -- `jointMoment`s.
    sorry

  exact h_induction L

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
