/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenTaylor
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPairingBasic
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

/-- **Talagrand's Proposition 1.11.10 (Eq. (1.341)).** Evaluation for any pairing of the
`2m` difference labels, with error linear in an arbitrary bound `M` on `fhat`.
Distinct endpoints, disjoint replica pairs and independence of `fhat` from their replicas
are implicit in the book's notation and necessary for the nonzero leading term. -/
theorem sk_hanen_truncated_rect_eval (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (m n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (P : Finpartition.Pairing (univ : Finset (Fin (2 * m))))
      (x y : Fin (2 * m) → Fin n), (∀ j, x j ≠ y j) →
      (∀ u v : Fin (2 * m), u ≠ v →
        x u ≠ x v ∧ x u ≠ y v ∧ y u ≠ x v ∧ y u ≠ y v) →
      ∀ (fhat : (Fin n → ℤˣ) → ℝ) (M : ℝ), (∀ ε, |fhat ε| ≤ M) →
      (∀ (ε : Fin n → ℤˣ) (i : Fin n) (t : ℤˣ),
        i ∈ (univ : Finset (Fin (2 * m))).biUnion (fun j => {x j, y j}) →
        fhat (Function.update ε i t) = fhat ε) →
      let α := (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4
        ∂gaussianReal 0 1) - 2 * q + 1
      let A_sq := α / (1 - β ^ 2 * α)
      let F := fun ρ : Fin n → Fin N → ℤˣ => P.blockProduct
        (Renormalization.pairWeight fun u v =>
          skCavityRectTrunc N n m q (fun j => (x j, y j)) u v ρ)
      |skCavityPathMean N n β q h 1 (fun σ =>
          (∏ v : Fin (2 * m), ((σ (x v) (Fin.last N) : ℝ) -
            (σ (y v) (Fin.last N) : ℝ))) * fhat (fun r => σ r (Fin.last N)) *
          F (fun r i => σ r i.castSucc)) -
        (∫ z : ℝ, (∫ ε : Fin n → ℤˣ, fhat ε
            ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
              fun s : ℤˣ => (s : ℝ) * (β * z * Real.sqrt q + h))) *
          (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * m))⁻¹ ∂gaussianReal 0 1) *
        (4 * β ^ 2 * A_sq / (N + 1 : ℝ)) ^ m| ≤
      K * M / ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) := by
  sorry

/-- **Talagrand's Proposition 1.11.11 (Eq. (1.347)).** Evaluation of the full rectangular
product for any pairing of the difference labels. The distinct, mutually disjoint replica
pairs are implicit in the book's notation; the leading term is independent of the pairing. -/
theorem sk_hanen_full_rect_eval (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (p n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (P : Finpartition.Pairing (univ : Finset (Fin (2 * p))))
      (x y : Fin (2 * p) → Fin n), (∀ j, x j ≠ y j) →
      (∀ u v : Fin (2 * p), u ≠ v →
        x u ≠ x v ∧ x u ≠ y v ∧ y u ≠ x v ∧ y u ≠ y v) →
      let α := (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4
        ∂gaussianReal 0 1) - 2 * q + 1
      let A_sq := α / (1 - β ^ 2 * α)
      let C := fun (σ : Fin n → Fin (N + 1) → ℤˣ) u v =>
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (x u) i : ℝ) * (σ (x v) i : ℝ)) -
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (y u) i : ℝ) * (σ (x v) i : ℝ)) -
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (x u) i : ℝ) * (σ (y v) i : ℝ)) +
        (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (y u) i : ℝ) * (σ (y v) i : ℝ))
      |skCavityPathMean N n β q h 1 (fun σ =>
          (∏ v : Fin (2 * p), ((σ (x v) (Fin.last N) : ℝ) -
            (σ (y v) (Fin.last N) : ℝ))) *
          P.blockProduct (Renormalization.pairWeight (C σ))) -
        (4 * ((N + 1 : ℝ)⁻¹ + β ^ 2 * (A_sq / (N + 1 : ℝ)))) ^ p *
          ∫ z : ℝ, (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * p))⁻¹
            ∂gaussianReal 0 1| ≤
      K / ((N : ℝ) + 1) ^ (((2 * p + 1 : ℕ) : ℝ) / 2) := by
  sorry

end SpinGlasses
