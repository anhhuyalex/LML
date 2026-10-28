/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.SinCosEndpoint
public import LeanMachineLearning.ForMathlib.Probability.Moments.IidSumExpansion

/-!
# The induction on the degree for the moment expansion of the free energy

Talagrand's Theorem 1.4.11 expands the moments of `A_N - SK(β, h)` as
`𝔼 (A_N - SK)^k = N^{-k/2} a(k) b^{k/2} + O(N^{-(k+1)/2})`, where `a(k)` is the `k`-th moment of a
standard Gaussian.  The proof integrates, along the smart path, a differential inequality
`ψ_k' = sin s cos s ((k (k - 1) / 2) N⁻¹ B ψ_{k-2} + D_k)` for the centered moments
`ψ_k(s) = 𝔼 (A_N(s) - RS(s))^k`, where `D_k = O(N^{-(k+1)/2})`, from the decoupled endpoint
`s = π/2` back to `s`, and inducts on `k`.

This file proves that induction in an abstract form.  The scale is a number `ε > 0` (`ε = N^{-1/2}`
in the application), `a` is any sequence with `a 0 = 1`, `a 1 = 0` and `a (k + 2) = (k + 1) a k`
(the Gaussian moments), and `b` is a function with `b' = B sin cos` (the path variance).

The differential equation with remainder and the decoupled endpoint estimate are hypotheses
of this abstract induction. For the SK model with deterministic field they are constructed in
`SKCenteredPathMoments.lean`, `SKCenteredPathODE.lean` and `IidSumExpansion.lean`, and assembled
in `SKFreeEnergyCLT.lean`. The random Gaussian external-field extension remains open.

## Main declarations

* `SpinGlasses.exists_clt_const`: constants dominating the recursion of the induction.
* `SpinGlasses.hasDerivAt_clt_ref`: the derivative of the reference term `ε^k a(k) b(s)^{k/2}`.
* `SpinGlasses.abs_sub_ref_le_of_ode`: one step of the induction, from `π/2` to every `s`.
* `SpinGlasses.clt_induction`: the induction on `k`, with bounds for all `s ∈ [0, π/2]`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Theorem 1.4.11.
-/

@[expose] public section

open Set ProbabilityTheory
open scoped Real

namespace SpinGlasses

variable {ε B : ℝ} {a : ℕ → ℝ} {b : ℝ → ℝ}

/-- **The derivative of the reference term of the moment expansion.**  If `b' = B sin cos`, then
for `k ≥ 1` the function `s ↦ ε^k a(k) b(s)^{k/2}` (natural division) has derivative
`sin s cos s ((k (k - 1) / 2) ε² B) (ε^{k-2} a(k-2) b(s)^{(k-2)/2})`, for any `a` with `a 1 = 0`
and `a (k + 2) = (k + 1) a k`. -/
theorem hasDerivAt_clt_ref (ha1 : a 1 = 0) (ha : ∀ k, a (k + 2) = (k + 1) * a k)
    (hb : ∀ s, HasDerivAt b (B * Real.sin s * Real.cos s) s) {k : ℕ} (hk : 1 ≤ k) (s : ℝ) :
    HasDerivAt (fun x => ε ^ k * a k * b x ^ (k / 2))
      (Real.sin s * Real.cos s * ((k : ℝ) * (k - 1) / 2 * ε ^ 2 * B *
        (ε ^ (k - 2) * a (k - 2) * b s ^ ((k - 2) / 2)))) s := by
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | hodd
  · obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 2 := ⟨m - 1, by omega⟩
    rw [show (2 * j + 2) / 2 = j + 1 by omega, show 2 * j + 2 - 2 = 2 * j by omega,
      show 2 * j / 2 = j by omega]
    have hd := ((hb s).pow (j + 1)).const_mul (ε ^ (2 * j + 2) * a (2 * j + 2))
    convert hd using 1
    rw [ha (2 * j)]
    push_cast
    ring
  · have h1 := Nat.eq_zero_of_odd_of_two_step_mul ha1 ha hodd
    simp only [h1, mul_zero, zero_mul]
    rcases hodd with ⟨m, rfl⟩
    rcases m with _ | m
    · simpa using hasDerivAt_const s (0 : ℝ)
    · rw [show 2 * (m + 1) + 1 - 2 = 2 * m + 1 by omega,
        Nat.eq_zero_of_odd_of_two_step_mul ha1 ha ⟨m, rfl⟩]
      simpa using hasDerivAt_const s (0 : ℝ)

/-- **One step of the induction.**  Let `ψ` satisfy, for every `s`, `ψ' = sin s cos s (c ε² B ψₚ(s)
+ D)` with `c = m (m - 1) / 2`, `|D| ≤ C_rem ε^{m+1}` on `[0, π/2]`; let `ψₚ` be within
`C_ind ε^{m-1}` of the reference term of degree `m - 2` on `[0, π/2]`; and let `ψ(π/2)` be within
`C_dec ε^{m+1}` of the reference term of degree `m`.  Then for all `s ∈ [0, π/2]`,
`|ψ(s) - ε^m a(m) b(s)^{m/2}| ≤ (C_dec + C_rem / 2 + (m (m - 1) / 4) |B| C_ind) ε^{m+1}`. -/
theorem abs_sub_ref_le_of_ode (hε : 0 < ε) (ha1 : a 1 = 0) (ha : ∀ k, a (k + 2) = (k + 1) * a k)
    (hb : ∀ s, HasDerivAt b (B * Real.sin s * Real.cos s) s) {m : ℕ} (hm : 1 ≤ m)
    {ψ ψp : ℝ → ℝ} {C_rem C_ind C_dec : ℝ}
    (hode : ∀ s, ∃ D, HasDerivAt ψ (Real.sin s * Real.cos s *
        ((m : ℝ) * (m - 1) / 2 * ε ^ 2 * B * ψp s + D)) s ∧
      (s ∈ Icc 0 (π / 2) → |D| ≤ C_rem * ε ^ (m + 1)))
    (hind : ∀ s ∈ Icc 0 (π / 2),
      |ψp s - ε ^ (m - 2) * a (m - 2) * b s ^ ((m - 2) / 2)| ≤ C_ind * ε ^ (m - 1))
    (hdec : |ψ (π / 2) - ε ^ m * a m * b (π / 2) ^ (m / 2)| ≤ C_dec * ε ^ (m + 1))
    {s : ℝ} (hs : s ∈ Icc 0 (π / 2)) :
    |ψ s - ε ^ m * a m * b s ^ (m / 2)| ≤
      (C_dec + C_rem / 2 + (m : ℝ) * (m - 1) / 4 * |B| * C_ind) * ε ^ (m + 1) := by
  set c : ℝ := (m : ℝ) * (m - 1) / 2 with hc_def
  have hc : 0 ≤ c := by
    have : (1 : ℝ) ≤ m := Nat.one_le_cast.2 hm
    rw [hc_def]; nlinarith
  set K : ℝ := (C_rem + c * |B| * C_ind) * ε ^ (m + 1) with hK
  have hεm : ε ^ 2 * ε ^ (m - 1) = ε ^ (m + 1) := by
    rw [← pow_add]; congr 1; omega
  have hΦ : ∀ x, ∃ D, HasDerivAt (fun y => ψ y - ε ^ m * a m * b y ^ (m / 2))
      (Real.sin x * Real.cos x * D) x ∧ (x ∈ Icc 0 (π / 2) → |D| ≤ K) := fun x => by
    obtain ⟨D, hD, hDb⟩ := hode x
    refine ⟨D + c * ε ^ 2 * B * (ψp x - ε ^ (m - 2) * a (m - 2) * b x ^ ((m - 2) / 2)),
      ?_, fun hx => ?_⟩
    · convert hD.sub (hasDerivAt_clt_ref ha1 ha hb hm x) using 1
      ring
    · calc |D + c * ε ^ 2 * B * (ψp x - ε ^ (m - 2) * a (m - 2) * b x ^ ((m - 2) / 2))|
          ≤ |D| + c * ε ^ 2 * |B| * |ψp x - ε ^ (m - 2) * a (m - 2) * b x ^ ((m - 2) / 2)| := by
            refine (abs_add_le _ _).trans (add_le_add_right ?_ _)
            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ c * ε ^ 2)]
        _ ≤ C_rem * ε ^ (m + 1) + c * ε ^ 2 * |B| * (C_ind * ε ^ (m - 1)) :=
            add_le_add (hDb hx) (mul_le_mul_of_nonneg_left (hind x hx) (by positivity))
        _ = K := by rw [hK, ← hεm]; ring
  have hK0 : 0 ≤ K := by
    obtain ⟨D, -, hDb⟩ := hΦ 0
    exact (abs_nonneg D).trans (hDb ⟨le_rfl, by positivity⟩)
  have hdiff := Real.abs_sub_le_of_exists_hasDerivAt_Icc hΦ hs.1 hs.2 le_rfl
  have hsin : Real.sin (π / 2) ^ 2 - Real.sin s ^ 2 ≤ 1 := by
    rw [Real.sin_pi_div_two, one_pow]; linarith [sq_nonneg (Real.sin s)]
  have h1 : |ψ s - ε ^ m * a m * b s ^ (m / 2)| ≤
      |ψ (π / 2) - ε ^ m * a m * b (π / 2) ^ (m / 2)| +
        |(ψ (π / 2) - ε ^ m * a m * b (π / 2) ^ (m / 2)) -
          (ψ s - ε ^ m * a m * b s ^ (m / 2))| := by
    rw [abs_sub_comm (_ - _) (ψ s - _)]
    calc _ = |(ψ (π / 2) - ε ^ m * a m * b (π / 2) ^ (m / 2)) +
          ((ψ s - ε ^ m * a m * b s ^ (m / 2)) -
            (ψ (π / 2) - ε ^ m * a m * b (π / 2) ^ (m / 2)))| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  calc _ ≤ C_dec * ε ^ (m + 1) + K / 2 * 1 :=
        h1.trans (add_le_add hdec (hdiff.trans (mul_le_mul_of_nonneg_left hsin (by positivity))))
    _ = _ := by rw [hK]; ring

/-- **Constants for the induction on the degree:** for any `B` and any sequences `C_rem`, `C_dec`
there is a sequence `C` with `C 0 = 0` and
`C_dec m + C_rem m / 2 + (m (m - 1) / 4) |B| C (m - 2) ≤ C m` for all `m ≥ 1` (a recursion
with two initial values, defined by `Nat.twoStepInduction`). -/
theorem exists_clt_const (B : ℝ) (C_rem C_dec : ℕ → ℝ) :
    ∃ C : ℕ → ℝ, C 0 = 0 ∧ ∀ m, 1 ≤ m →
      C_dec m + C_rem m / 2 + (m : ℝ) * (m - 1) / 4 * |B| * C (m - 2) ≤ C m := by
  let u : ℕ → ℝ := fun m => C_dec m + C_rem m / 2
  let w : ℕ → ℝ := fun m => (m : ℝ) * (m - 1) / 4 * |B|
  let C : ℕ → ℝ := Nat.twoStepInduction 0 (u 1)
    (fun k a _ => u (k + 2) + w (k + 2) * a)
  refine ⟨C, rfl, fun m hm => ?_⟩
  rcases m with _ | _ | k
  · omega
  · simp [C, u, w, Nat.twoStepInduction]
  · exact le_of_eq rfl

/-- **The induction on the degree.**  Let `ε > 0`, `a 0 = 1`, `a 1 = 0`, `a (k + 2) = (k + 1) a k`,
`b' = B sin cos`, and let `ψ k` be real functions with `ψ 0 = 1` such that for every `m ≥ 1`
(i) `(ψ m)' = sin s cos s ((m (m - 1) / 2) ε² B ψ_{m-2}(s) + D)` with `|D| ≤ C_rem(m) ε^{m+1}` on
`[0, π/2]`, and (ii) `|ψ_m(π/2) - ε^m a(m) b(π/2)^{m/2}| ≤ C_dec(m) ε^{m+1}`.
If the constants satisfy `C 0 ≥ 0` and
`C_dec(m) + C_rem(m) / 2 + (m (m - 1) / 4) |B| C(m - 2) ≤ C(m)` for `m ≥ 1`, then for every `k` and
every `s ∈ [0, π/2]`, `|ψ_k(s) - ε^k a(k) b(s)^{k/2}| ≤ C(k) ε^{k+1}`. -/
theorem clt_induction (hε : 0 < ε) (ha0 : a 0 = 1) (ha1 : a 1 = 0)
    (ha : ∀ k, a (k + 2) = (k + 1) * a k)
    (hb : ∀ s, HasDerivAt b (B * Real.sin s * Real.cos s) s) {ψ : ℕ → ℝ → ℝ}
    (hψ0 : ∀ s, ψ 0 s = 1) {C_rem C_dec C : ℕ → ℝ} (hC0 : 0 ≤ C 0)
    (hode : ∀ m, 1 ≤ m → ∀ s, ∃ D, HasDerivAt (ψ m) (Real.sin s * Real.cos s *
        ((m : ℝ) * (m - 1) / 2 * ε ^ 2 * B * ψ (m - 2) s + D)) s ∧
      (s ∈ Icc 0 (π / 2) → |D| ≤ C_rem m * ε ^ (m + 1)))
    (hdec : ∀ m, 1 ≤ m →
      |ψ m (π / 2) - ε ^ m * a m * b (π / 2) ^ (m / 2)| ≤ C_dec m * ε ^ (m + 1))
    (hC : ∀ m, 1 ≤ m →
      C_dec m + C_rem m / 2 + (m : ℝ) * (m - 1) / 4 * |B| * C (m - 2) ≤ C m)
    (k : ℕ) {s : ℝ} (hs : s ∈ Icc 0 (π / 2)) :
    |ψ k s - ε ^ k * a k * b s ^ (k / 2)| ≤ C k * ε ^ (k + 1) := by
  induction k using Nat.strong_induction_on generalizing s with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [hψ0, ha0, pow_zero, one_mul, Nat.zero_div, pow_zero, mul_one, sub_self, abs_zero]
      exact mul_nonneg hC0 (by positivity)
    · have hprev : ∀ s ∈ Icc 0 (π / 2),
          |ψ (k - 2) s - ε ^ (k - 2) * a (k - 2) * b s ^ ((k - 2) / 2)| ≤
            C (k - 2) * ε ^ (k - 1) := fun s hs => by
        rcases Nat.lt_or_ge k 2 with hk2 | hk2
        · obtain rfl : k = 1 := by omega
          simp [hψ0, ha0, hC0]
        · have := ih (k - 2) (by omega) hs
          rwa [show k - 2 + 1 = k - 1 by omega] at this
      refine (abs_sub_ref_le_of_ode hε ha1 ha hb hk (hode k hk) hprev (hdec k hk) hs).trans ?_
      exact mul_le_mul_of_nonneg_right (hC k hk) (by positivity)

end SpinGlasses
