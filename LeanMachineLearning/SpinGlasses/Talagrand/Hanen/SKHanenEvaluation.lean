/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenTaylor
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPairingBasic
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenRectEval
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenRectFull
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
  obtain ⟨K1, hK1, hb1⟩ := sk_hanen_rect_leading β₀ hβ₀ m n
  obtain ⟨K2, hK2, hb2⟩ := sk_hanen_trunc_old_vs_coupled β₀ hβ₀ m n
  obtain ⟨K3, hK3, hb3⟩ := sk_hanen_trunc_vs_full β₀ hβ₀ m n
  obtain ⟨K4, hK4, hb4⟩ := sk_hanen_full_pairing_sq β₀ hβ₀ m n
  obtain ⟨K5, hK5, hb5⟩ := sk_hanen_full_pairings_of_ne β₀ hβ₀ m n
  refine ⟨K1 + (Fintype.card (Finpartition.Pairing (univ : Finset (Fin (2 * m)))) : ℝ) *
    (K2 + K3 + (K4 + K5)), by positivity, ?_⟩
  classical
  intro β h q hfix hβ N P x y hxy hdisj fhat M hM hfhat α A_sq F
  have hM0 : 0 ≤ M := (abs_nonneg (fhat fun _ => 1)).trans (hM _)
  have hD : (0 : ℝ) < ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) := by positivity
  let pairMap : Fin (2 * m) → Fin n × Fin n := fun j => (x j, y j)
  have hconv : (∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1) =
      ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂gaussianReal 0 1 :=
    integral_tanh_pow_mul_z_sqrt_eq β q h 4
  have hb1' := hb1 β h q hfix hβ N P pairMap hxy hdisj fhat M hM hfhat
  have hb4' := hb4 β h q hfix hβ N P pairMap hxy hdisj
  dsimp only at hb1' hb4'
  simp only [hconv] at hb4'
  -- the Wick-sum term for each pairing `P'`
  let t : Finpartition.Pairing (univ : Finset (Fin (2 * m))) → ℝ := fun P' =>
    skCavityPathMean N n β q h 0 (fun σ =>
      P.blockProduct (Renormalization.pairWeight fun u v =>
        skCavityRectTrunc N n m q pairMap u v (fun r i => σ r i.castSucc)) *
      P'.blockProduct (Renormalization.pairWeight fun u v =>
        skCavityRectTrunc N n m q pairMap u v (fun r i => σ r i.castSucc)))
  have hterm : ∀ P' : Finpartition.Pairing (univ : Finset (Fin (2 * m))),
      |t P' - (if P' = P then (4 * A_sq / ((N : ℝ) + 1)) ^ m else 0)| ≤
        (K2 + K3 + (K4 + K5)) / ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) := by
    intro P'
    have h2 := hb2 β h q hfix hβ N P P' pairMap hdisj
    have h3 := hb3 β h q hfix hβ N P P' pairMap hdisj hxy
    dsimp only at h2 h3
    have hsplit : (K2 + K3 + (K4 + K5)) / ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) =
        K2 / ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) +
        K3 / ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) +
        K4 / ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) +
        K5 / ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) := by ring
    have hK4D : 0 ≤ K4 / ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) := by positivity
    have hK5D : 0 ≤ K5 / ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) := by positivity
    have h2' := abs_le.1 h2
    have h3' := abs_le.1 h3
    by_cases hPP : P' = P
    · subst hPP
      simp only [eq_self, ↓reduceIte]
      have h4' := abs_le.1 hb4'
      refine abs_le.2 ⟨?_, ?_⟩ <;> simp only [t] <;> rw [hsplit] <;> linarith [h2'.1, h2'.2, h3'.1,
        h3'.2, h4'.1, h4'.2]
    · simp only [hPP, ↓reduceIte, sub_zero]
      have h5 := hb5 β h q hfix hβ N P P' hPP pairMap hxy hdisj
      dsimp only at h5
      have h5' := abs_le.1 h5
      refine abs_le.2 ⟨?_, ?_⟩ <;> simp only [t] <;> rw [hsplit] <;> linarith [h2'.1, h2'.2, h3'.1,
        h3'.2, h5'.1, h5'.2]
  set D := ((N : ℝ) + 1) ^ (((2 * m + 1 : ℕ) : ℝ) / 2) with hDdef
  set T := (4 * A_sq / ((N : ℝ) + 1)) ^ m with hT
  set Z := ∫ z : ℝ, (∫ ε : Fin n → ℤˣ, fhat ε
            ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
              fun s : ℤˣ => (s : ℝ) * (β * z * Real.sqrt q + h))) *
          (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * m))⁻¹ ∂gaussianReal 0 1 with hZ
  have hsum : |(∑ P' : Finpartition.Pairing (univ : Finset (Fin (2 * m))), t P') - T| ≤
      (Fintype.card (Finpartition.Pairing (univ : Finset (Fin (2 * m)))) : ℝ) *
        ((K2 + K3 + (K4 + K5)) / D) := by
    have h1 : (∑ P' : Finpartition.Pairing (univ : Finset (Fin (2 * m))), t P') - T =
        ∑ P' : Finpartition.Pairing (univ : Finset (Fin (2 * m))),
          (t P' - if P' = P then T else 0) := by
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ P (fun _ => T)]
      simp
    rw [h1]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun P' _ => hterm P').trans ?_
    simp
  have hZb : |Z| ≤ M := by
    have hb : ∀ z : ℝ, ‖(∫ ε : Fin n → ℤˣ, fhat ε
            ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
              fun s : ℤˣ => (s : ℝ) * (β * z * Real.sqrt q + h))) *
          (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * m))⁻¹‖ ≤ M := by
      intro z
      have hc : 1 ≤ Real.cosh (β * z * Real.sqrt q + h) ^ (4 * m) :=
        one_le_pow₀ (Real.one_le_cosh _)
      have hinv : ‖(Real.cosh (β * z * Real.sqrt q + h) ^ (4 * m))⁻¹‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact inv_le_one_of_one_le₀ hc
      have hf : ‖∫ ε : Fin n → ℤˣ, fhat ε
            ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
              fun s : ℤˣ => (s : ℝ) * (β * z * Real.sqrt q + h))‖ ≤ M := by
        refine (norm_integral_le_of_norm_le_const (C := M)
          (Filter.Eventually.of_forall fun ε => ?_)).trans ?_
        · simpa using hM ε
        · simp
      rw [norm_mul]
      calc _ ≤ M * 1 := mul_le_mul hf hinv (norm_nonneg _) hM0
        _ = M := mul_one M
    have := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1) (C := M)
      (Filter.Eventually.of_forall hb)
    simpa [hZ] using this
  have hβm : (β ^ 2) ^ m ≤ 1 :=
    pow_le_one₀ (sq_nonneg β) (by nlinarith [sq_nonneg β₀])
  have hid : Z * (4 * β ^ 2 * A_sq / ((N : ℝ) + 1)) ^ m = β ^ (2 * m) * Z * T := by
    rw [hT, pow_mul, show 4 * β ^ 2 * A_sq / ((N : ℝ) + 1) = β ^ 2 * (4 * A_sq / ((N : ℝ) + 1))
      by ring, mul_pow]
    ring
  have hlead := hb1'
  simp only [hid]
  have hcomb : |(skCavityPathMean N n β q h 1 fun σ =>
        (∏ v : Fin (2 * m), ((σ (x v) (Fin.last N) : ℝ) - (σ (y v) (Fin.last N) : ℝ))) *
          fhat (fun r => σ r (Fin.last N)) * F (fun r i => σ r i.castSucc)) -
      β ^ (2 * m) * Z * T| ≤ K1 * M / D +
        |β ^ (2 * m) * Z| *
          |(∑ P' : Finpartition.Pairing (univ : Finset (Fin (2 * m))), t P') - T| := by
    have hsplit : (skCavityPathMean N n β q h 1 fun σ =>
        (∏ v : Fin (2 * m), ((σ (x v) (Fin.last N) : ℝ) - (σ (y v) (Fin.last N) : ℝ))) *
          fhat (fun r => σ r (Fin.last N)) * F (fun r i => σ r i.castSucc)) -
        β ^ (2 * m) * Z * T =
        ((skCavityPathMean N n β q h 1 fun σ =>
        (∏ v : Fin (2 * m), ((σ (x v) (Fin.last N) : ℝ) - (σ (y v) (Fin.last N) : ℝ))) *
          fhat (fun r => σ r (Fin.last N)) * F (fun r i => σ r i.castSucc)) -
          β ^ (2 * m) * Z * ∑ P' : Finpartition.Pairing (univ : Finset (Fin (2 * m))), t P') +
        β ^ (2 * m) * Z *
          ((∑ P' : Finpartition.Pairing (univ : Finset (Fin (2 * m))), t P') - T) := by
      ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    exact add_le_add hlead le_rfl
  have hbz : |β ^ (2 * m) * Z| ≤ M := by
    rw [abs_mul, abs_of_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg β) m)]
    calc β ^ (2 * m) * |Z| ≤ 1 * M :=
          mul_le_mul (by rw [pow_mul]; exact hβm) hZb (abs_nonneg _) zero_le_one
      _ = M := one_mul M
  have hnp : (0 : ℝ) ≤ (Fintype.card (Finpartition.Pairing (univ : Finset (Fin (2 * m)))) : ℝ) *
      ((K2 + K3 + (K4 + K5)) / D) :=
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by linarith) hD.le)
  calc _ ≤ K1 * M / D + |β ^ (2 * m) * Z| * |(∑ P' : Finpartition.Pairing
          (univ : Finset (Fin (2 * m))), t P') - T| := hcomb
    _ ≤ K1 * M / D + M * ((Fintype.card (Finpartition.Pairing (univ : Finset (Fin (2 * m)))) : ℝ) *
          ((K2 + K3 + (K4 + K5)) / D)) := by gcongr
    _ = _ := by ring

/-- **Proposition 1.11.11, one subset of blocks.** For a subset `S` of the blocks of the pairing
`P`, the coupled mean of `∏_{B ∈ S} η_B · ∏_{B ∉ S} η_B² · ∏_{B ∈ S} U_B⁻` is
`4^{p - |S|} 𝔼 ch^{-4p} (4 β² A²/(N+1))^{|S|}` up to `16^{p-|S|} K_{|S|} / (N+1)^{(2|S|+1)/2}`.
It is Proposition 1.11.10 applied to the sub-pairing of `S` (relabelled by
`exists_relabel_pairing_subset`) with `f̂ = ∏_{B ∉ S} η_B²`, whose Gibbs mean at `u = 0` is
`(4 ch^{-4})^{p-|S|}`. -/
theorem sk_hanen_full_subset_term (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (p n : ℕ) :
    ∃ K : ℕ → ℝ, (∀ k, 0 < K k) ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (P : Finpartition.Pairing (univ : Finset (Fin (2 * p))))
      (x y : Fin (2 * p) → Fin n), (∀ j, x j ≠ y j) →
      (∀ u v : Fin (2 * p), u ≠ v →
        x u ≠ x v ∧ x u ≠ y v ∧ y u ≠ x v ∧ y u ≠ y v) →
      ∀ S : Finset (Finset (Fin (2 * p))), S ⊆ P.val.parts →
      let α := (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4
        ∂gaussianReal 0 1) - 2 * q + 1
      let A_sq := α / (1 - β ^ 2 * α)
      |skCavityPathMean N n β q h 1 (fun σ =>
          (∏ B ∈ S, ∏ v ∈ B, ((σ (x v) (Fin.last N) : ℝ) - (σ (y v) (Fin.last N) : ℝ))) *
          (∏ B ∈ P.val.parts \ S,
            (∏ v ∈ B, ((σ (x v) (Fin.last N) : ℝ) - (σ (y v) (Fin.last N) : ℝ))) ^ 2) *
          ∏ B ∈ S, Renormalization.pairWeight (fun a b =>
            skCavityRectTrunc N n p q (fun j => (x j, y j)) a b
              (fun r i => σ r i.castSucc)) B) -
        4 ^ (p - S.card) * (∫ z : ℝ, (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * p))⁻¹
          ∂gaussianReal 0 1) * (4 * β ^ 2 * A_sq / (N + 1 : ℝ)) ^ S.card| ≤
      K S.card * 16 ^ (p - S.card) / ((N : ℝ) + 1) ^ (((2 * S.card + 1 : ℕ) : ℝ) / 2) := by
  choose K hKpos hKb using fun k : ℕ => sk_hanen_truncated_rect_eval β₀ hβ₀ k n
  refine ⟨K, hKpos, ?_⟩
  intro β h q hfix hβ N P x y hxy hdisj S hS α A_sq
  classical
  obtain ⟨w, Q, hwinj, hwrange, hQ⟩ := Renormalization.exists_relabel_pairing_subset P S hS
  have hparts : P.val.parts.card = p := P.card_parts_of_card_eq (m := p) (by simp)
  have hcard2 : ∀ B ∈ P.val.parts, B.card = 2 := fun B hB => P.2 B hB
  have hmp : S.card ≤ p := by have := Finset.card_le_card hS; omega
  let Λ : Finset (Fin (2 * p)) := (P.val.parts \ S).biUnion id
  have hΛcard : Λ.card = 2 * (p - S.card) :=
    hanen_card_biUnion_sdiff P.val.parts S P.val.disjoint hcard2 hS hparts
  let fhat' : (Fin n → ℤˣ) → ℝ := fun ε => ∏ v ∈ Λ, ((ε (x v) : ℝ) - (ε (y v) : ℝ)) ^ 2
  have hdisj' : ∀ u v : Fin (2 * S.card), u ≠ v →
      x (w u) ≠ x (w v) ∧ x (w u) ≠ y (w v) ∧ y (w u) ≠ x (w v) ∧ y (w u) ≠ y (w v) :=
    fun u v huv => hdisj (w u) (w v) (fun h => huv (hwinj h))
  have hM : ∀ ε, |fhat' ε| ≤ 16 ^ (p - S.card) := by
    intro ε
    have hf (v : Fin (2 * p)) : ((ε (x v) : ℝ) - (ε (y v) : ℝ)) ^ 2 ≤ 4 := by
      have h1 := units_cast_sq (ε (x v))
      have h2 := units_cast_sq (ε (y v))
      nlinarith [sq_nonneg ((ε (x v) : ℝ) + (ε (y v) : ℝ))]
    have h0 : 0 ≤ fhat' ε := Finset.prod_nonneg fun v _ => sq_nonneg _
    rw [abs_of_nonneg h0]
    calc fhat' ε ≤ ∏ _v ∈ Λ, (4 : ℝ) := by
          change (∏ v ∈ Λ, ((ε (x v) : ℝ) - (ε (y v) : ℝ)) ^ 2) ≤ ∏ _v ∈ Λ, (4 : ℝ)
          gcongr with v _
          exact hf v
      _ = 16 ^ (p - S.card) := by
          rw [Finset.prod_const, hΛcard, pow_mul]; norm_num
  have hfhat' : ∀ (ε : Fin n → ℤˣ) (i : Fin n) (t : ℤˣ),
      i ∈ (univ : Finset (Fin (2 * S.card))).biUnion
        (fun k => {(x (w k), y (w k)).1, (x (w k), y (w k)).2}) →
      fhat' (Function.update ε i t) = fhat' ε := by
    intro ε i t hi
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at hi
    obtain ⟨k, hk⟩ := hi
    refine Finset.prod_congr rfl fun v hv => ?_
    obtain ⟨B', hB', hvB'⟩ := Finset.mem_biUnion.1 hv
    obtain ⟨B, hBS, hwk⟩ := (hwrange (w k)).1 ⟨k, rfl⟩
    have hBB' : B ≠ B' := fun h => (Finset.mem_sdiff.1 hB').2 (h ▸ hBS)
    have hdj := P.val.disjoint (hS hBS) (Finset.mem_sdiff.1 hB').1 hBB'
    have hvw : w k ≠ v := fun h => Finset.disjoint_left.1 hdj hwk (h ▸ hvB')
    have hd := hdisj (w k) v hvw
    have hne : i ≠ x v ∧ i ≠ y v := by
      rcases hk with rfl | rfl
      · exact ⟨hd.1, hd.2.1⟩
      · exact ⟨hd.2.2.1, hd.2.2.2⟩
    simp only [Function.update_of_ne hne.1.symm, Function.update_of_ne hne.2.symm]
  have hb := hKb S.card β h q hfix hβ N Q (fun k => x (w k)) (fun k => y (w k))
    (fun k => hxy _) hdisj' fhat' (16 ^ (p - S.card)) hM hfhat'
  dsimp only at hb
  -- the observable of `hb` is the observable of the statement
  have hobs : (fun σ : Fin n → Fin (N + 1) → ℤˣ =>
      ((∏ v : Fin (2 * S.card), ((σ (x (w v)) (Fin.last N) : ℝ) -
          (σ (y (w v)) (Fin.last N) : ℝ))) * fhat' (fun r => σ r (Fin.last N))) *
        Q.blockProduct (Renormalization.pairWeight fun u v =>
          skCavityRectTrunc N n S.card q (fun j => (x (w j), y (w j))) u v
            (fun r i => σ r i.castSucc))) =
      fun σ => ((∏ B ∈ S, ∏ v ∈ B, ((σ (x v) (Fin.last N) : ℝ) - (σ (y v) (Fin.last N) : ℝ))) *
          (∏ B ∈ P.val.parts \ S,
            (∏ v ∈ B, ((σ (x v) (Fin.last N) : ℝ) - (σ (y v) (Fin.last N) : ℝ))) ^ 2)) *
        ∏ B ∈ S, Renormalization.pairWeight (fun a b =>
          skCavityRectTrunc N n p q (fun j => (x j, y j)) a b
            (fun r i => σ r i.castSucc)) B := by
    funext σ
    have F1 := hanen_prod_relabel_eq_prod_blocks P.val.parts S P.val.disjoint hS w hwinj hwrange
      (fun v => (σ (x v) (Fin.last N) : ℝ) - (σ (y v) (Fin.last N) : ℝ))
    have F2 := hanen_prod_sq_blocks P.val.parts S P.val.disjoint
      (fun v => (σ (x v) (Fin.last N) : ℝ) - (σ (y v) (Fin.last N) : ℝ))
    have F3 : Q.blockProduct (Renormalization.pairWeight fun u v =>
        skCavityRectTrunc N n S.card q (fun j => (x (w j), y (w j))) u v
          (fun r i => σ r i.castSucc)) =
        ∏ B ∈ S, Renormalization.pairWeight (fun a b =>
          skCavityRectTrunc N n p q (fun j => (x j, y j)) a b
            (fun r i => σ r i.castSucc)) B :=
      hQ (fun a b => skCavityRectTrunc N n p q (fun j => (x j, y j)) a b
        (fun r i => σ r i.castSucc))
        (fun a b => skCavityRectTrunc_comm N n p q _ a b _)
    rw [F1, F3]
    change _ * (∏ v ∈ Λ, _) * _ = _
    rw [F2]
  have hZ : (∫ z : ℝ, (∫ ε : Fin n → ℤˣ, fhat' ε
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
          fun s : ℤˣ => (s : ℝ) * (β * z * Real.sqrt q + h))) *
        (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * S.card))⁻¹ ∂gaussianReal 0 1) =
      4 ^ (p - S.card) * ∫ z : ℝ, (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * p))⁻¹
        ∂gaussianReal 0 1 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [show (∫ ε : Fin n → ℤˣ, fhat' ε ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
          fun s : ℤˣ => (s : ℝ) * (β * z * Real.sqrt q + h))) =
        (2 * ((Real.cosh (β * z * Real.sqrt q + h))⁻¹) ^ 2) ^ Λ.card from
      integral_prod_spin_diff_sq _ x y hxy hdisj Λ, hΛcard]
    have hc : 0 < Real.cosh (β * z * Real.sqrt q + h) := Real.cosh_pos _
    have key : ∀ (c : ℝ), 0 < c → ∀ k m' : ℕ,
        (2 * c⁻¹ ^ 2) ^ (2 * k) * (c ^ (4 * m'))⁻¹ = 4 ^ k * (c ^ (4 * (k + m')))⁻¹ := by
      intro c hc k m'
      have h4 : (4 : ℝ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
      rw [h4]
      ring
    rw [show 4 * p = 4 * ((p - S.card) + S.card) by omega]
    exact key _ hc _ _
  rw [hZ, hobs] at hb
  exact hb

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
  obtain ⟨K, hKpos, hKb⟩ := sk_hanen_full_subset_term β₀ hβ₀ p n
  classical
  refine ⟨2 ^ p * 16 ^ p * ∑ k ∈ range (p + 1), K k, by
    have : 0 < ∑ k ∈ range (p + 1), K k :=
      Finset.sum_pos (fun k _ => hKpos k) ⟨0, by simp⟩
    positivity, ?_⟩
  intro β h q hfix hβ N P x y hxy hdisj α A_sq C
  have hparts : P.val.parts.card = p := P.card_parts_of_card_eq (m := p) (by simp)
  have hcard2 : ∀ B ∈ P.val.parts, B.card = 2 := fun B hB => P.2 B hB
  -- Stage 1: pointwise expansion over subsets of the blocks
  have hpt : ∀ σ : Fin n → Fin (N + 1) → ℤˣ,
      (∏ v : Fin (2 * p), ((σ (x v) (Fin.last N) : ℝ) - (σ (y v) (Fin.last N) : ℝ))) *
        P.blockProduct (Renormalization.pairWeight (C σ)) =
      ∑ S ∈ P.val.parts.powerset, ((N : ℝ) + 1)⁻¹ ^ (p - S.card) *
        ((∏ B ∈ S, ∏ v ∈ B, ((σ (x v) (Fin.last N) : ℝ) - (σ (y v) (Fin.last N) : ℝ))) *
          (∏ B ∈ P.val.parts \ S,
            (∏ v ∈ B, ((σ (x v) (Fin.last N) : ℝ) - (σ (y v) (Fin.last N) : ℝ))) ^ 2) *
          ∏ B ∈ S, Renormalization.pairWeight (fun a b =>
            skCavityRectTrunc N n p q (fun j => (x j, y j)) a b
              (fun r i => σ r i.castSucc)) B) := by
    intro σ
    have hη : (∏ v : Fin (2 * p), ((σ (x v) (Fin.last N) : ℝ) - (σ (y v) (Fin.last N) : ℝ))) =
        ∏ B ∈ P.val.parts, ∏ v ∈ B, ((σ (x v) (Fin.last N) : ℝ) -
          (σ (y v) (Fin.last N) : ℝ)) :=
      (P.val.prod_parts fun v => (σ (x v) (Fin.last N) : ℝ) - (σ (y v) (Fin.last N) : ℝ)).symm
    have hCsymm (a b : Fin (2 * p)) : C σ a b = C σ b a := by
      simp only [C]
      have h1 (s t : Fin n) : ∑ i : Fin (N + 1), (σ s i : ℝ) * (σ t i : ℝ) =
          ∑ i : Fin (N + 1), (σ t i : ℝ) * (σ s i : ℝ) :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      rw [h1 (x a) (x b), h1 (y a) (x b), h1 (x a) (y b), h1 (y a) (y b)]
      ring
    have hblock : ∀ B ∈ P.val.parts, Renormalization.pairWeight (C σ) B =
        Renormalization.pairWeight (fun a b => skCavityRectTrunc N n p q (fun j => (x j, y j)) a b
          (fun r i => σ r i.castSucc)) B +
        ((N : ℝ) + 1)⁻¹ * ∏ v ∈ B, ((σ (x v) (Fin.last N) : ℝ) -
          (σ (y v) (Fin.last N) : ℝ)) := by
      intro B hB
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 (hcard2 B hB)
      rw [Renormalization.pairWeight_pair (C σ) hCsymm hab,
        Renormalization.pairWeight_pair _ (fun a b => skCavityRectTrunc_comm N n p q _ a b _) hab,
        Finset.prod_pair hab]
      exact hanen_full_rect_eq_trunc_add_spin N n p q (fun j => (x j, y j)) σ a b
    have hbp : P.blockProduct (Renormalization.pairWeight (C σ)) =
        ∏ B ∈ P.val.parts, (Renormalization.pairWeight (fun a b =>
          skCavityRectTrunc N n p q (fun j => (x j, y j)) a b (fun r i => σ r i.castSucc)) B +
          ((N : ℝ) + 1)⁻¹ * ∏ v ∈ B, ((σ (x v) (Fin.last N) : ℝ) -
            (σ (y v) (Fin.last N) : ℝ))) :=
      Finset.prod_congr rfl hblock
    rw [hη, hbp, hanen_block_expansion P.val.parts _ _ _, hparts]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.prod_mul_distrib]
    ring
  -- Stage 2: linearity of the path mean over the subsets
  set D : ℝ := ((N : ℝ) + 1) ^ (((2 * p + 1 : ℕ) : ℝ) / 2) with hDdef
  have hD : 0 < D := by positivity
  set J : ℝ := ∫ z : ℝ, (Real.cosh (β * z * Real.sqrt q + h) ^ (4 * p))⁻¹ ∂gaussianReal 0 1
    with hJ
  set yl : ℝ := 4 * β ^ 2 * A_sq / (N + 1 : ℝ) with hyl
  have hlin := skCavityPathMean_finset_sum N n β q h 1 P.val.parts.powerset
    (fun S => ((N : ℝ) + 1)⁻¹ ^ (p - S.card))
    (fun S σ =>
      (∏ B ∈ S, ∏ v ∈ B, ((σ (x v) (Fin.last N) : ℝ) - (σ (y v) (Fin.last N) : ℝ))) *
        (∏ B ∈ P.val.parts \ S,
          (∏ v ∈ B, ((σ (x v) (Fin.last N) : ℝ) - (σ (y v) (Fin.last N) : ℝ))) ^ 2) *
        ∏ B ∈ S, Renormalization.pairWeight (fun a b =>
          skCavityRectTrunc N n p q (fun j => (x j, y j)) a b
            (fun r i => σ r i.castSucc)) B)
  simp only [hpt]
  rw [hlin]
  -- the leading terms add up to the target (binomial theorem)
  have hlead : (4 * (((N : ℝ) + 1)⁻¹ + β ^ 2 * (A_sq / (N + 1 : ℝ)))) ^ p * J =
      ∑ S ∈ P.val.parts.powerset, ((N : ℝ) + 1)⁻¹ ^ (p - S.card) *
        (4 ^ (p - S.card) * J * yl ^ S.card) := by
    have h1 : ∀ S ∈ P.val.parts.powerset, ((N : ℝ) + 1)⁻¹ ^ (p - S.card) *
        (4 ^ (p - S.card) * J * yl ^ S.card) =
        J * ((4 * ((N : ℝ) + 1)⁻¹) ^ (p - S.card) * yl ^ S.card) := by
      intro S _
      rw [mul_pow]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
    have h2 := Finset.sum_powerset_apply_card (x := P.val.parts)
      (fun m => (4 * ((N : ℝ) + 1)⁻¹) ^ (p - m) * yl ^ m)
    rw [h2, hparts]
    have h3 := add_pow yl (4 * ((N : ℝ) + 1)⁻¹) p
    have e : 4 * (((N : ℝ) + 1)⁻¹ + β ^ 2 * (A_sq / (N + 1 : ℝ))) = yl + 4 * ((N : ℝ) + 1)⁻¹ := by
      rw [hyl]; field_simp; ring
    rw [e, h3, mul_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [nsmul_eq_mul]
    ring
  rw [hlead, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ S ∈ P.val.parts.powerset,
      |((N : ℝ) + 1)⁻¹ ^ (p - S.card) * skCavityPathMean N n β q h 1 (fun σ =>
        (∏ B ∈ S, ∏ v ∈ B, ((σ (x v) (Fin.last N) : ℝ) - (σ (y v) (Fin.last N) : ℝ))) *
        (∏ B ∈ P.val.parts \ S,
          (∏ v ∈ B, ((σ (x v) (Fin.last N) : ℝ) - (σ (y v) (Fin.last N) : ℝ))) ^ 2) *
        ∏ B ∈ S, Renormalization.pairWeight (fun a b =>
          skCavityRectTrunc N n p q (fun j => (x j, y j)) a b
            (fun r i => σ r i.castSucc)) B) -
        ((N : ℝ) + 1)⁻¹ ^ (p - S.card) * (4 ^ (p - S.card) * J * yl ^ S.card)| ≤
      (∑ k ∈ range (p + 1), K k) * 16 ^ p / D := by
    intro S hS
    have hSsub := Finset.mem_powerset.1 hS
    have hmS : S.card ≤ p := by have := Finset.card_le_card hSsub; omega
    have hb := hKb β h q hfix hβ N P x y hxy hdisj S hSsub
    dsimp only at hb
    have hc : 0 ≤ ((N : ℝ) + 1)⁻¹ ^ (p - S.card) := by positivity
    rw [← mul_sub, abs_mul, abs_of_nonneg hc]
    have key : ((N : ℝ) + 1) ^ (p - S.card) *
        ((N : ℝ) + 1) ^ (((2 * S.card + 1 : ℕ) : ℝ) / 2) = D := by
      rw [hDdef, ← Real.rpow_natCast, ← Real.rpow_add (by positivity)]
      congr 1
      push_cast [Nat.cast_sub hmS]
      ring
    have hKS : K S.card ≤ ∑ k ∈ range (p + 1), K k :=
      Finset.single_le_sum (f := K) (fun k _ => (hKpos k).le)
        (Finset.mem_range.2 (by omega))
    have h16 : (16 : ℝ) ^ (p - S.card) ≤ 16 ^ p :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    calc ((N : ℝ) + 1)⁻¹ ^ (p - S.card) * _ ≤ ((N : ℝ) + 1)⁻¹ ^ (p - S.card) *
          (K S.card * 16 ^ (p - S.card) / ((N : ℝ) + 1) ^ (((2 * S.card + 1 : ℕ) : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hb hc
      _ = K S.card * 16 ^ (p - S.card) / D := by
        rw [← key, inv_pow]
        field_simp
      _ ≤ (∑ k ∈ range (p + 1), K k) * 16 ^ p / D :=
        div_le_div_of_nonneg_right (mul_le_mul hKS h16 (by positivity)
          (Finset.sum_nonneg fun k _ => (hKpos k).le)) hD.le
  calc _ ≤ ∑ _S ∈ P.val.parts.powerset, (∑ k ∈ range (p + 1), K k) * 16 ^ p / D :=
        Finset.sum_le_sum hterm
    _ = _ := by
        rw [Finset.sum_const, Finset.card_powerset, hparts, nsmul_eq_mul]
        push_cast
        ring

end SpinGlasses
