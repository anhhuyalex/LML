/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityCovariance
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.SqSub
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.Tanh

/-!
# Algebra of the `T`-basis (Talagrand, Section 1.8, Eqs. (1.245)-(1.265))

The algebra and elementary Gaussian-integral facts behind Propositions 1.8.7-1.8.12:

* `sk_cavity_coincidences_sub_eq`: the difference of two coincidence coefficients of pairs
  `{i₁, k}` and `{i₂, k}` against a pair `{a, b}` (the computation of `c(ℓ, ℓ')` in the proof of
  Lemma 1.8.9);
* `sk_cavity_deriv_zero_sub_third`: Lemma 1.8.9 in sum form;
* `sk_at_deriv_coef_split`: Eq. (1.253) turned into Eq. (1.254) when `f⁻` does not depend on the
  third replica (the replica-independence substitution itself is not carried out; the covariance
  system of `SKCovarianceRows.lean` replaces it);
* the coefficients of `ν(T²)`, `A²`, `B²` in Eq. (1.264) (`sk_t_coeff_T_sq`, `sk_t_coeff_B_sq`);
* `qhat_le_of_fixedPoint`, `three_quarters_le_one_sub_beta_sq_mul`: `q̂ ≤ q` and
  `1 - β²(1 - 4q + 3q̂) ≥ 3/4`;
* `dotProduct_div_sub_decomp`: the decomposition (1.246),
  `R_{ℓℓ'} - q = T_{ℓℓ'} + T_ℓ + T_ℓ' + T`;
* `one_sub_two_mul_add_qhat_eq`: `1 - 2q + q̂ = 𝔼 ch⁻⁴(β √q z + h)`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 1.8.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators Real

namespace SpinGlasses

/-- **The coefficient `c(ℓ, ℓ')` of Lemma 1.8.9.**  For distinct `i₁, i₂, k` and a pair `a ≠ b`,
the coefficient `B(coinc(i₁, k; a, b)) - B(coinc(i₂, k; a, b))` is
`(ϑ a + ϑ b)` times `B 2 - B 1` if `k ∈ {a, b}` and `B 1 - B 0` otherwise, where
`ϑ r = 1[r = i₁] - 1[r = i₂]`. -/
theorem sk_cavity_coincidences_sub_eq {R : Type*} [DecidableEq R] (B : ℕ → ℝ)
    {i₁ i₂ k a b : R} (h12 : i₁ ≠ i₂) (h1k : i₁ ≠ k) (h2k : i₂ ≠ k) (hab : a ≠ b) :
    B (skCavityCoincidences i₁ k a b) - B (skCavityCoincidences i₂ k a b) =
      (((if i₁ = a then (1 : ℝ) else 0) + (if i₁ = b then 1 else 0)) -
          ((if i₂ = a then (1 : ℝ) else 0) + (if i₂ = b then 1 else 0))) *
        (if k = a ∨ k = b then B 2 - B 1 else B 1 - B 0) := by
  unfold skCavityCoincidences
  by_cases ha1 : i₁ = a <;> by_cases hb1 : i₁ = b <;> by_cases ha2 : i₂ = a <;>
    by_cases hb2 : i₂ = b <;> by_cases hka : k = a <;> by_cases hkb : k = b <;>
    simp_all [eq_comm]

/-- **From Eq. (1.253) to Eq. (1.254).**  If the observable does not depend on the third replica,
the term of replica `3` equals the term of replica `n + 1`, and the book's coefficients
`b(2) - b(1)` and `b(1) - b(0)` regroup into `b(2) - 4 b(1) + 3 b(0)` and `b(1) - b(0)`.
Here `s` is the index set `{4, ..., n}`, so `|s| + 3 = n`. -/
theorem sk_at_deriv_coef_split {ι : Type*} (s : Finset ι) (n : ℕ) (hn : s.card + 3 = n)
    (b2 b1 b0 S3 Sn : ℝ) (S : ι → ℝ) (h : S3 = Sn) :
    (b2 - b1) * S3 + (b1 - b0) * (∑ l ∈ s, S l - (n : ℝ) * Sn) =
      (b2 - 4 * b1 + 3 * b0) * S3 + (b1 - b0) * ∑ l ∈ s, (S l - Sn) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← hn]
  subst h
  push_cast
  ring

/-- **Coefficient of `ν(T²)` in Eq. (1.264).**  Over the pairs `1 ≤ ℓ < ℓ' ≤ 4` with respect to
`(x, y) = (1, 2)` the coefficients are `b(2)` (for `(1,2)`), `b(1)` four times, `b(0)` (for
`(3,4)`); over `(ℓ, 5)` they are `b(1)` twice and `b(0)` twice; and `(5, 6)` gives `b(0)`. -/
theorem sk_t_coeff_T_sq (β q qhat : ℝ) :
    (skCavityBCoef β q qhat 2 + 4 * skCavityBCoef β q qhat 1 + skCavityBCoef β q qhat 0) -
        4 * (2 * skCavityBCoef β q qhat 1 + 2 * skCavityBCoef β q qhat 0) +
        10 * skCavityBCoef β q qhat 0 = β ^ 2 * (1 - 4 * q + 3 * qhat) := by
  dsimp [skCavityBCoef, skCavityBUnscaled]
  ring

/-- **Coefficient of `B²` in Eq. (1.264):** the four pairs `(ℓ, ℓ')` with `ℓ ∈ {1,2}`,
`ℓ' ∈ {3,4}` carry `b(1)`, the pair `(3,4)` carries `2 b(0)`, and `(3,5)`, `(4,5)` carry
`-4 b(0)` each. -/
theorem sk_t_coeff_B_sq (β q qhat : ℝ) :
    4 * skCavityBCoef β q qhat 1 + 2 * skCavityBCoef β q qhat 0 -
        4 * (skCavityBCoef β q qhat 0 + skCavityBCoef β q qhat 0) =
      2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qhat) := by
  dsimp [skCavityBCoef, skCavityBUnscaled]
  ring

/-- For the fixed point `q` and `q̂ = 𝔼 tanh⁴ Y`, one has `q̂ ≤ q`. -/
theorem qhat_le_of_fixedPoint (β q h qhat : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat) :
    qhat ≤ q := by
  calc qhat = ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) := hqhat.symm
    _ ≤ ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) :=
        integral_tanh_pow_four_le_sq (P := gaussianReal 0 1)
          (fun z : ℝ => β * Real.sqrt q * z + h) (by fun_prop)
    _ = q := hfix

/-- **The denominator of Propositions 1.8.10 and 1.8.11.**  For `4 β² < 1`, `0 ≤ q` and
`q̂ ≤ q`: `1 - β² (1 - 4 q + 3 q̂) ≥ 3/4`. -/
theorem three_quarters_le_one_sub_beta_sq_mul {β q qhat : ℝ} (hβ : 4 * β ^ 2 < 1) (hq : 0 ≤ q)
    (hqhat : qhat ≤ q) : 3 / 4 ≤ 1 - β ^ 2 * (1 - 4 * q + 3 * qhat) := by
  have h1 : 1 - 4 * q + 3 * qhat ≤ 1 := by linarith
  have h2 : β ^ 2 * (1 - 4 * q + 3 * qhat) ≤ β ^ 2 * 1 :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg β)
  linarith

/-- **The decomposition (1.246).**  For vectors `x, y, b` and the centered parts
`T_{xy} = (x - b)·(y - b)/N`, `T_x = (x - b)·b/N`, `T = b·b/N - q`:
`x·y/N - q = T_{xy} + T_x + T_y + T`. -/
theorem dotProduct_div_sub_decomp {ι : Type*} [Fintype ι] (N q : ℝ) (x y b : ι → ℝ) :
    x ⬝ᵥ y / N - q = (x - b) ⬝ᵥ (y - b) / N + (x - b) ⬝ᵥ b / N + (y - b) ⬝ᵥ b / N +
      (b ⬝ᵥ b / N - q) := by
  have : x ⬝ᵥ y = (x - b) ⬝ᵥ (y - b) + (x - b) ⬝ᵥ b + (y - b) ⬝ᵥ b + b ⬝ᵥ b := by
    simp only [sub_dotProduct, dotProduct_sub]
    rw [dotProduct_comm b y]
    ring
  rw [this]
  ring

/-- **Talagrand, Lemma 1.8.9, first form (Eq. 1.253), as a sum over the replica families.**
For distinct replicas `i₁, i₂, k` of `n` replicas and a function `F` of the old coordinates, the
cavity derivative at the decoupled endpoint of `F (ε_{i₁} - ε_{i₂}) ε_k` is the weighted sum over
the families `j = (a, b)` of Eq. (1.152) of
`(ϑ a + ϑ b) · (if k ∈ {a, b} then b(2) - b(1) else b(1) - b(0)) · ν₀(F (R⁻_{ab} - q))`,
where `ϑ r = 1[r = i₁] - 1[r = i₂]`.  It is the difference of two applications of Lemma 1.8.2
(`sk_cavity_deriv_zero_pair_combo` with the coefficients `1, -1`), so the `-q` cancels. -/
theorem sk_cavity_deriv_zero_sub_third (N n : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (qhat : ℝ)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    {i₁ i₂ k : Fin n} (h12 : i₁ ≠ i₂) (h1k : i₁ ≠ k) (h2k : i₂ ≠ k)
    (F : (Fin n → Fin N → ℤˣ) → ℝ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) →
        (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    let so : Fin n → Option (Option (Fin n)) := fun r => some (some r)
    let f : (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ := fun τ =>
      F (fun r i => τ (so r) i.castSucc) *
        ((((τ (so i₁) (Fin.last N) : ℤˣ) : ℝ) - ((τ (so i₂) (Fin.last N) : ℤˣ) : ℝ)) *
          ((τ (so k) (Fin.last N) : ℤˣ) : ℝ))
    let K : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)) - q)
    (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f τ *
            ((∑ p : Fin n × Fin n with p.1 < p.2,
                K (τ (so p.1)) (τ (so p.2))) -
              (n : ℝ) * ∑ r : Fin n, K (τ (so r)) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
      ∑ j : SKCavityReplicaPair n,
        skCavityReplicaPairWeight n j *
          ((((if so i₁ = (skCavityReplicaPairMap j).1 then (1 : ℝ) else 0) +
                (if so i₁ = (skCavityReplicaPairMap j).2 then 1 else 0)) -
              ((if so i₂ = (skCavityReplicaPairMap j).1 then (1 : ℝ) else 0) +
                (if so i₂ = (skCavityReplicaPairMap j).2 then 1 else 0))) *
            (if so k = (skCavityReplicaPairMap j).1 ∨ so k = (skCavityReplicaPairMap j).2 then
                skCavityBCoef β q qhat 2 - skCavityBCoef β q qhat 1
              else skCavityBCoef β q qhat 1 - skCavityBCoef β q qhat 0) *
            ∫ g', ∫ ρ : Option (Option (Fin n)) → Fin N → ℤˣ,
              F (fun r => ρ (so r)) *
                ((N + 1 : ℝ)⁻¹ *
                  ((fun i : Fin N => (ρ (skCavityReplicaPairMap j).1 i : ℝ)) ⬝ᵥ
                    fun i : Fin N => (ρ (skCavityReplicaPairMap j).2 i : ℝ)) - q)
              ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
                (fun r : Fin N → ℤˣ =>
                  (Real.sqrt (N + 1))⁻¹ * β *
                    (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
                  h * ∑ i : Fin N, (r i : ℝ)))
              ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) := by
  intro B E so f K
  have hx : ∀ m : Bool, (if m then i₁ else i₂) ≠ k := fun m => by
    cases m
    exacts [h2k, h1k]
  have h1 := sk_cavity_deriv_zero_pair_combo N n β q h hfix qhat hqhat (ι := Bool)
    (fun m => if m then 1 else -1) (x := fun m => if m then i₁ else i₂) (y := fun _ => k)
    (fun m => (hx m)) F
  simp only [Fintype.sum_bool, ite_true, ite_false, Bool.false_eq_true] at h1
  have hpt : ∀ u v w : ℝ, 1 * (u * w - q) + -1 * (v * w - q) = (u - v) * w := fun u v w => by
    ring
  simp only [hpt] at h1
  refine h1.trans (Finset.sum_congr rfl fun j _ => ?_)
  have hso : ∀ r r' : Fin n, r ≠ r' → so r ≠ so r' := fun r r' hr he =>
    hr (Option.some.inj (Option.some.inj he))
  have hc := sk_cavity_coincidences_sub_eq (skCavityBCoef β q qhat) (hso _ _ h12)
    (hso _ _ h1k) (hso _ _ h2k) (skCavityReplicaPair_ne j)
  have e : ∀ u v : ℝ, 1 * u + -1 * v = u - v := fun u v => by ring
  simp only [e, skCavityReplicaPairCoincidences, so] at hc ⊢
  rw [hc, mul_assoc]

/-- `1 - 2q + q̂ = 𝔼 ch⁻⁴(β √q z + h)` for the fixed point `q` and `q̂ = 𝔼 tanh⁴`. -/
theorem one_sub_two_mul_add_qhat_eq (β q h qhat : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat) :
    1 - 2 * q + qhat =
      ∫ z : ℝ, ((Real.cosh (β * Real.sqrt q * z + h))⁻¹) ^ 4 ∂(gaussianReal 0 1) := by
  have := integral_tanh_pow_four_sub_two_mul_add_eq (μ := gaussianReal 0 1)
    (fun z : ℝ => β * Real.sqrt q * z + h) (by fun_prop)
  rw [hfix, hqhat] at this
  simpa using this

end SpinGlasses
