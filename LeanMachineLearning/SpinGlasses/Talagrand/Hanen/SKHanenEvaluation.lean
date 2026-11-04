/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenTaylor
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenRectangular
public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapCLT.Pair.SKOverlapCLTPairGaussian
public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapSecondMoments.SKCovarianceRows
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.SqSub

/-!
# Evaluation of rectangular overlap products (Talagrand, Propositions 1.11.10, 1.11.11)

This module evaluates the cavity path expectation of rectangular overlap products:
* `SpinGlasses.sk_hanen_truncated_rect_eval`: Proposition 1.11.10 (Eq. (1.341)), evaluating
  the truncated rectangular product $\nu(\eta_V \hat f \prod_{J \in \mathcal I} U_J^-)$.
* `SpinGlasses.sk_hanen_full_rect_eval`: Proposition 1.11.11 (Eq. (1.347)), evaluating
  the full rectangular product $\nu(\eta_V \prod_{J \in \mathcal I} U_J)$ via the binomial
  expansion $U_J = U_J^- + (N+1)^{-1} \eta_J$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- The first index of the $w$-th pair in `Fin (2 * m)`. -/
def finPair0 {m : ℕ} (w : Fin m) : Fin (2 * m) :=
  ⟨2 * w.val, by omega⟩

/-- The second index of the $w$-th pair in `Fin (2 * m)`. -/
def finPair1 {m : ℕ} (w : Fin m) : Fin (2 * m) :=
  ⟨2 * w.val + 1, by omega⟩

/-- The two indices of a pair are distinct. -/
theorem finPair0_ne_finPair1 {m : ℕ} (w : Fin m) : finPair0 w ≠ finPair1 w := by
  intro h
  have : (finPair0 w).val = (finPair1 w).val := congr_arg Fin.val h
  dsimp [finPair0, finPair1] at this
  omega

/-- `finPair0` is injective. -/
theorem finPair0_injective {m : ℕ} : Function.Injective (@finPair0 m) := by
  intro w₁ w₂ h
  ext
  have : (finPair0 w₁).val = (finPair0 w₂).val := congr_arg Fin.val h
  dsimp [finPair0] at this
  omega

/-- `finPair1` is injective. -/
theorem finPair1_injective {m : ℕ} : Function.Injective (@finPair1 m) := by
  intro w₁ w₂ h
  ext
  have : (finPair1 w₁).val = (finPair1 w₂).val := congr_arg Fin.val h
  dsimp [finPair1] at this
  omega

/-- Any even index is distinct from any odd index. -/
theorem finPair0_ne_finPair1_of_ne {m : ℕ} (w₁ w₂ : Fin m) : finPair0 w₁ ≠ finPair1 w₂ := by
  intro h
  have : (finPair0 w₁).val = (finPair1 w₂).val := congr_arg Fin.val h
  dsimp [finPair0, finPair1] at this
  omega

/-- **Relation between $\alpha$ and $\mathbb{E} \cosh^{-4} Y$:**
$\alpha = 1 - 2q + \hat q = \mathbb{E} \cosh^{-4} Y$. -/
theorem alpha_eq_integral_inv_cosh_four (β h q : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) :
    (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂gaussianReal 0 1) - 2 * q + 1 =
      ∫ z : ℝ, (Real.cosh (β * Real.sqrt q * z + h) ^ 4)⁻¹ ∂gaussianReal 0 1 := by
  have h_alpha := one_sub_two_mul_add_qhat_eq β q h
    (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂gaussianReal 0 1) hfix rfl
  have heq : (fun z : ℝ => ((Real.cosh (β * Real.sqrt q * z + h))⁻¹) ^ 4) =
      (fun z => (Real.cosh (β * Real.sqrt q * z + h) ^ 4)⁻¹) := by
    funext z
    exact inv_pow _ 4
  rw [heq] at h_alpha
  linarith

/-- Algebraic cancellation in Hanen's variance:
$(N+1)^{-1} + \beta^2 \frac{A^2}{N+1} = \frac{1}{(N+1)(1 - \beta^2 \alpha)}$. -/
theorem inv_add_beta_sq_mul_A_sq_eq (N : ℕ) (β α : ℝ) (hden : 1 - β ^ 2 * α ≠ 0) :
    (N + 1 : ℝ)⁻¹ + β ^ 2 * (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) =
      1 / ((N + 1 : ℝ) * (1 - β ^ 2 * α)) := by
  have : (N + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Exact cancellation of the factor 4 with the two-site reduction factor $2^{-2p} = 4^{-p}$. -/
theorem four_mul_pow_mul_two_inv_pow (p : ℕ) (X : ℝ) :
    (4 * X) ^ p * ((2 : ℝ)⁻¹) ^ (2 * p) = X ^ p := by
  rw [mul_pow]
  have h4 : (4 : ℝ) ^ p * ((2 : ℝ)⁻¹) ^ (2 * p) = 1 := by
    rw [inv_pow, pow_mul]
    have : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [this]
    exact mul_inv_cancel₀ (by positivity)
  calc 4 ^ p * X ^ p * (2 : ℝ)⁻¹ ^ (2 * p)
    _ = (4 ^ p * (2 : ℝ)⁻¹ ^ (2 * p)) * X ^ p := by ring
    _ = 1 * X ^ p := by rw [h4]
    _ = X ^ p := by ring

/-- **Talagrand's Proposition 1.11.10 (Eq. (1.341)).** Evaluation of truncated rectangular
products: for $|V| = 2m$ and a pairing of $V$, the coupled expectation of
$\eta_V \hat f \prod_{J \in \mathcal I} U_J^-$ equals
$\mathbb E(\langle \hat f \rangle_0 \operatorname{ch}^{-4m} Y) (4 \beta^2 A^2)^m$ up to
$O((N+1)^{-(2m+1)/2})$, uniformly in $\beta^2 \le \beta_0^2 < 1/4$. -/
theorem sk_hanen_truncated_rect_eval (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (m n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (x y : Fin (2 * m) → Fin n) (_ : ∀ j, x j ≠ y j)
      (fhat : (Fin n → ℤˣ) → ℝ) (_ : ∀ ε, |fhat ε| ≤ 1),
      let α : ℝ := (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4
        ∂gaussianReal 0 1) - 2 * q + 1
      let A_sq : ℝ := α / (1 - β ^ 2 * α)
      |∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
          (∏ w : Fin m, (((σ (x (finPair0 w)) (Fin.last N) : ℤˣ) : ℝ) -
            ((σ (y (finPair0 w)) (Fin.last N) : ℤˣ) : ℝ)) *
            (((σ (x (finPair1 w)) (Fin.last N) : ℤˣ) : ℝ) -
            ((σ (y (finPair1 w)) (Fin.last N) : ℤˣ) : ℝ))) *
          fhat (fun k => σ k (Fin.last N)) *
          ∏ w : Fin m,
            (((N + 1 : ℝ)⁻¹ *
              ((fun i : Fin N => (σ (x (finPair0 w)) i.castSucc : ℝ)) ⬝ᵥ
                (fun i : Fin N => (σ (x (finPair1 w)) i.castSucc : ℝ))) - q) -
            ((N + 1 : ℝ)⁻¹ *
              ((fun i : Fin N => (σ (y (finPair0 w)) i.castSucc : ℝ)) ⬝ᵥ
                (fun i : Fin N => (σ (x (finPair1 w)) i.castSucc : ℝ))) - q) -
            ((N + 1 : ℝ)⁻¹ *
              ((fun i : Fin N => (σ (x (finPair0 w)) i.castSucc : ℝ)) ⬝ᵥ
                (fun i : Fin N => (σ (y (finPair1 w)) i.castSucc : ℝ))) - q) +
            ((N + 1 : ℝ)⁻¹ *
              ((fun i : Fin N => (σ (y (finPair0 w)) i.castSucc : ℝ)) ⬝ᵥ
                (fun i : Fin N => (σ (y (finPair1 w)) i.castSucc : ℝ))) - q))
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) -
        (∫ z : ℝ, (∫ ε : Fin n → ℤˣ, fhat ε
            ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
              fun s : ℤˣ => ((s : ℤˣ) : ℝ) * (β * z * Real.sqrt q + h))) *
          (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * m))⁻¹
          ∂gaussianReal 0 1) *
        (4 * β ^ 2 * A_sq / (N + 1 : ℝ)) ^ m| ≤
      K / ((N : ℝ) + 1) ^ ((((2 * m + 1 : ℕ) : ℝ)) / 2) := by
  obtain ⟨K1, hK1pos, hK1⟩ := abs_sk_eta_taylor_le β₀ hβ₀ n (2 * m) 0
  obtain ⟨K2, hK2pos, hK2⟩ := sk_cavity_prod_sq_le β₀ hβ₀ m 1
  refine ⟨K1 * (Real.sqrt K2 + 1) + (4 * β₀ ^ 2 * 4) ^ m + 1, by positivity, ?_⟩
  intro β h q hfix hβ N x y hxy fhat hfbound α A_sq
  sorry

/-- **Talagrand's Proposition 1.11.11 (Eq. (1.347)).** Evaluation of full rectangular products:
for $|V| = 2p$ and a pairing of $V$, the coupled expectation of
$\eta_V \prod_{J \in \mathcal I} U_J$ equals
$(4 (1 / (N+1) + \beta^2 A^2))^p \mathbb E \operatorname{ch}^{-4p} Y$ up to
$O((N+1)^{-(2p+1)/2})$, uniformly in $\beta^2 \le \beta_0^2 < 1/4$. -/
theorem sk_hanen_full_rect_eval (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (p n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (x y : Fin (2 * p) → Fin n) (_ : ∀ j, x j ≠ y j),
      let α : ℝ := (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4
        ∂gaussianReal 0 1) - 2 * q + 1
      let A_sq : ℝ := α / (1 - β ^ 2 * α)
      |∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ,
          (∏ w : Fin p, (((σ (x (finPair0 w)) (Fin.last N) : ℤˣ) : ℝ) -
            ((σ (y (finPair0 w)) (Fin.last N) : ℤˣ) : ℝ)) *
            (((σ (x (finPair1 w)) (Fin.last N) : ℤˣ) : ℝ) -
            ((σ (y (finPair1 w)) (Fin.last N) : ℤˣ) : ℝ))) *
          ∏ w : Fin p,
            (((N + 1 : ℝ)⁻¹ *
              ((fun i : Fin (N + 1) => (σ (x (finPair0 w)) i : ℝ)) ⬝ᵥ
                (fun i : Fin (N + 1) => (σ (x (finPair1 w)) i : ℝ))) - q) -
            ((N + 1 : ℝ)⁻¹ *
              ((fun i : Fin (N + 1) => (σ (y (finPair0 w)) i : ℝ)) ⬝ᵥ
                (fun i : Fin (N + 1) => (σ (x (finPair1 w)) i : ℝ))) - q) -
            ((N + 1 : ℝ)⁻¹ *
              ((fun i : Fin (N + 1) => (σ (x (finPair0 w)) i : ℝ)) ⬝ᵥ
                (fun i : Fin (N + 1) => (σ (y (finPair1 w)) i : ℝ))) - q) +
            ((N + 1 : ℝ)⁻¹ *
              ((fun i : Fin (N + 1) => (σ (y (finPair0 w)) i : ℝ)) ⬝ᵥ
                (fun i : Fin (N + 1) => (σ (y (finPair1 w)) i : ℝ))) - q))
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) -
        (4 * ((N + 1 : ℝ)⁻¹ + β ^ 2 * (A_sq / (N + 1 : ℝ)))) ^ p *
          ∫ z : ℝ, (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * p))⁻¹
            ∂gaussianReal 0 1| ≤
      K / ((N : ℝ) + 1) ^ ((((2 * p + 1 : ℕ) : ℝ)) / 2) := by
  sorry

end SpinGlasses
