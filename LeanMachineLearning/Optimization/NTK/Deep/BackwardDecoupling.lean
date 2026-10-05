/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Deep.DecouplingBounds
public import LeanMachineLearning.Optimization.NTK.Deep.DeepSpaceForward

/-!
# The Decoupling Approximation `G_k ≈ G_{k+1} Φ'_k` and Gradient Independence

Wiring of the algebra (`Deep/BackwardAlgebra.lean`), the convergence calculus
(`Deep/DecouplingBounds.lean`), the residual concentration
(`Initialization/ResidualConcentration.lean`) and the layer splitting (`Deep/LayerSplit.lean`)
into the backward induction of the deep NTK.

**Section 1 (deterministic, one parameter record).** With `Φ = [φ(h_k^α)]_α`, `Σ̂ = n⁻¹ ΦᵀΦ`,
`V = Wh k`, `u^α = g_{k+1}^α` and `ζ^α_b = n⁻¹ ⟨h_{k+1}^b, u^α⟩`:
`g_k^α = φ'(h_k^α) ⊙ (x^α + y^α)` with the projected part `x^α = Φ (Σ̂⁻¹ ζ^α)` and the residual
`y^α = n^{-1/2} (V Pᗮ)ᵀ u^α` (`backwardSensitivity_hidden_decomp`).
-/

@[expose]
public section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Matrix BigOperators

namespace NTK

section theta

variable {d n0 m n : ℕ} (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)

/-- The forward feature matrix `Φ_k = [φ(h_k^α)]_α ∈ ℝ^{n × m}`. -/
noncomputable def netFeat (θ : DeepMLPParams d n0 n) (k : Fin d) : Matrix (Fin n) (Fin m) ℝ :=
  Matrix.of fun j a => φ (deepMLPPreactivation d n0 n m φ X θ k a j)

/-- The normalized Gram matrix `Σ̂ = n⁻¹ ΦᵀΦ` of the forward features (the empirical activation
Gram). -/
noncomputable def netGram (θ : DeepMLPParams d n0 n) (k : Fin d) : Matrix (Fin m) (Fin m) ℝ :=
  (n : ℝ)⁻¹ • ((netFeat φ X θ k)ᵀ * netFeat φ X θ k)

/-- The gradient-independence quantity `n⁻¹ ⟨h_ℓ^b, g_ℓ^a⟩`. -/
noncomputable def gradIndep (θ : DeepMLPParams d n0 n) (ℓ : Fin d) (a b : Fin m) : ℝ :=
  (n : ℝ)⁻¹ * (deepMLPPreactivation d n0 n m φ X θ ℓ b ⬝ᵥ
    backwardSensitivity d n0 n m φ φ' X θ ℓ a)

/-- The projected part `x^a = Φ (Σ̂⁻¹ ζ^a)` of `n^{-1/2} Wh kᵀ g_{k+1}^a`. -/
noncomputable def projPart (θ : DeepMLPParams d n0 n) (k : ℕ) (hk : k + 1 < d) (a : Fin m) :
    Fin n → ℝ :=
  netFeat φ X θ ⟨k, by omega⟩ *ᵥ ((netGram φ X θ ⟨k, by omega⟩)⁻¹ *ᵥ
    fun b => gradIndep φ φ' X θ ⟨k + 1, hk⟩ a b)

/-- The residual part `y^a = n^{-1/2} (Wh k Pᗮ)ᵀ g_{k+1}^a`. -/
noncomputable def resPart (θ : DeepMLPParams d n0 n) (k : ℕ) (hk : k + 1 < d) (a : Fin m) :
    Fin n → ℝ :=
  Real.sqrt ((n : ℝ)⁻¹) •
    ((θ.Wh ⟨k, by omega⟩ * (1 - gramProjector (netFeat φ X θ ⟨k, by omega⟩)))ᵀ *ᵥ
      backwardSensitivity d n0 n m φ φ' X θ ⟨k + 1, hk⟩ a)

/-- **Decomposition of the hidden sensitivity.** If `Σ̂` is invertible, then
`g_k^a = φ'(h_k^a) ⊙ (x^a + y^a)`. -/
lemma backwardSensitivity_hidden_decomp (θ : DeepMLPParams d n0 n) (k : ℕ) (hk : k + 1 < d)
    (hn : n ≠ 0) (hS : IsUnit (netGram φ X θ ⟨k, by omega⟩).det) (a : Fin m) :
    backwardSensitivity d n0 n m φ φ' X θ ⟨k, by omega⟩ a = fun j =>
      φ' (deepMLPPreactivation d n0 n m φ X θ ⟨k, by omega⟩ a j) *
        (projPart φ φ' X θ k hk a j + resPart φ φ' X θ k hk a j) := by
  have hk' : k < d := by omega
  set Φ := netFeat φ X θ ⟨k, hk'⟩ with hΦ
  set V := θ.Wh ⟨k, by omega⟩ with hV
  set u := backwardSensitivity d n0 n m φ φ' X θ ⟨k + 1, hk⟩ a with hu
  rw [backwardSensitivity_succ_mulVec φ φ' X θ k hk a]
  funext j
  congr 1
  have hdec := transpose_mulVec_eq_gramProjector_add Φ V u
  have hS' : IsUnit ((n : ℝ)⁻¹ • (Φᵀ * Φ)).det := hS
  have hproj := projected_part_eq hn Φ V u hS'
  have key : ∀ b : Fin m, ((Real.sqrt ((n : ℝ)⁻¹) • (V * Φ))ᵀ *ᵥ u) b =
      (Real.sqrt ((n : ℝ)⁻¹) • (V *ᵥ fun j => φ (deepMLPPreactivation d n0 n m φ X θ ⟨k, hk'⟩ b j)))
        ⬝ᵥ u := by
    intro b
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.smul_apply,
      Matrix.mul_apply, Pi.smul_apply, smul_eq_mul, hΦ, netFeat, Matrix.of_apply]
  have hzeta : (n : ℝ)⁻¹ • ((Real.sqrt ((n : ℝ)⁻¹) • (V * Φ))ᵀ *ᵥ u) =
      fun b => gradIndep φ φ' X θ ⟨k + 1, hk⟩ a b := by
    funext b
    rw [Pi.smul_apply, smul_eq_mul, key b]
    unfold gradIndep
    rw [deepMLPPreactivation_succ_mulVec φ X θ k hk b]
  rw [hdec, smul_add, Pi.add_apply]
  congr 1
  rw [hproj, hzeta]
  rfl

/-- The derivative features `φ'(h_k^a)` as a vector. -/
noncomputable def netDeriv (θ : DeepMLPParams d n0 n) (k : Fin d) (a : Fin m) : Fin n → ℝ :=
  fun j => φ' (deepMLPPreactivation d n0 n m φ X θ k a j)

/-- `G_k^{ab} = n⁻¹ ∑ⱼ φ'(h^a)ⱼ φ'(h^b)ⱼ (x^a + y^a)ⱼ (x^b + y^b)ⱼ`. -/
lemma deepSensitivityGram_hidden_eq_wcov (θ : DeepMLPParams d n0 n) (k : ℕ) (hk : k + 1 < d)
    (hn : n ≠ 0) (hS : IsUnit (netGram φ X θ ⟨k, by omega⟩).det) (a b : Fin m) :
    deepSensitivityGram d n0 n m φ φ' X θ ⟨k, by omega⟩ a b =
      (𝔼 j, (netDeriv φ φ' X θ ⟨k, by omega⟩ a) j * (netDeriv φ φ' X θ ⟨k, by omega⟩ b) j *
          ((projPart φ φ' X θ k hk a + resPart φ φ' X θ k hk a) j * (projPart φ φ' X θ k hk b +
          resPart φ φ' X θ k hk b) j)) := by
  rw [deepSensitivityGram_hidden d n0 n m φ φ' X θ k (by omega), Matrix.of_apply,
    backwardSensitivity_hidden_decomp φ φ' X θ k hk hn hS a,
    backwardSensitivity_hidden_decomp φ φ' X θ k hk hn hS b]
  simp only [expect_fin_eq_inv_mul_sum]
  unfold netDeriv
  simp only [dotProduct, Pi.add_apply]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The weighted pairing of the residuals is the normalized residual quadratic form
`n⁻² uᵀ (V Pᗮ) diag(f g) (V Pᗮ)ᵀ v`. -/
lemma wcov_resPart_eq (θ : DeepMLPParams d n0 n) (k : ℕ) (hk : k + 1 < d) (a b : Fin m) :
    (𝔼 j, (netDeriv φ φ' X θ ⟨k, by omega⟩ a) j * (netDeriv φ φ' X θ ⟨k, by omega⟩ b) j *
        ((resPart φ φ' X θ k hk a) j * (resPart φ φ' X θ k hk b) j)) =
      ((n : ℝ) ^ 2)⁻¹ * (backwardSensitivity d n0 n m φ φ' X θ ⟨k + 1, hk⟩ a ⬝ᵥ
        (((θ.Wh ⟨k, by omega⟩ *
              (1 - gramProjector (netFeat φ X θ ⟨k, by omega⟩))) *
            Matrix.diagonal (fun j => netDeriv φ φ' X θ ⟨k, by omega⟩ a j *
              netDeriv φ φ' X θ ⟨k, by omega⟩ b j) *
          (θ.Wh ⟨k, by omega⟩ *
              (1 - gramProjector (netFeat φ X θ ⟨k, by omega⟩)))ᵀ) *ᵥ
          backwardSensitivity d n0 n m φ φ' X θ ⟨k + 1, hk⟩ b)) :=
  wcov_smul_transpose_mulVec _ _ _ _ _ _ (Real.sq_sqrt (by positivity))

/-- **The conditional mean of the residual form.** With `D = diag(φ'(h^a) φ'(h^b))`,
`n⁻² (u^a ⬝ u^b) tr(Pᗮ D Pᗮ) = G_{k+1}^{ab} Φ'^{ab}_k − G_{k+1}^{ab} · n⁻¹ tr(D P)`, and
`tr(D P) = ∑_{a'b'} (Σ̂⁻¹)_{a'b'} M(f,g)_{b'a'}`. -/
lemma resid_mean_eq (θ : DeepMLPParams d n0 n) (k : ℕ) (hk : k + 1 < d) (hn : n ≠ 0)
    (hS : IsUnit (netGram φ X θ ⟨k, by omega⟩).det) (a b : Fin m) :
    ((n : ℝ) ^ 2)⁻¹ * ((backwardSensitivity d n0 n m φ φ' X θ ⟨k + 1, hk⟩ a ⬝ᵥ
        backwardSensitivity d n0 n m φ φ' X θ ⟨k + 1, hk⟩ b) *
      ((1 - gramProjector (netFeat φ X θ ⟨k, by omega⟩)) *
        Matrix.diagonal (fun j => netDeriv φ φ' X θ ⟨k, by omega⟩ a j *
          netDeriv φ φ' X θ ⟨k, by omega⟩ b j) *
        (1 - gramProjector (netFeat φ X θ ⟨k, by omega⟩))).trace) =
      deepSensitivityGram d n0 n m φ φ' X θ ⟨k + 1, by omega⟩ a b *
        deepDerivativeGram d n0 n m φ φ' X θ ⟨k, by omega⟩ a b -
      deepSensitivityGram d n0 n m φ φ' X θ ⟨k + 1, by omega⟩ a b *
        ((n : ℝ)⁻¹ * ∑ a', ∑ b', (netGram φ X θ ⟨k, by omega⟩)⁻¹ a' b' *
          (𝔼 j, (netDeriv φ φ' X θ ⟨k, by omega⟩ a) j * (netDeriv φ φ' X θ ⟨k, by omega⟩ b) j *
              (netFeat φ X θ ⟨k, by omega⟩) j b' * (netFeat φ X θ ⟨k, by omega⟩) j a')) := by
  have hP := isOrthogonalProjection_gramProjector_all (netFeat φ X θ ⟨k, by omega⟩)
  rw [trace_compress_orthogonalComplement _ _ hP,
    trace_diagonal_gramProjector hn _ _ _ hS,
    deepSensitivityGram_hidden d n0 n m φ φ' X θ (k + 1) hk, Matrix.of_apply]
  have e1 : (Matrix.diagonal (fun j => netDeriv φ φ' X θ ⟨k, by omega⟩ a j *
      netDeriv φ φ' X θ ⟨k, by omega⟩ b j)).trace =
      netDeriv φ φ' X θ ⟨k, by omega⟩ a ⬝ᵥ netDeriv φ φ' X θ ⟨k, by omega⟩ b :=
    Matrix.trace_diagonal _
  have e2 : deepDerivativeGram d n0 n m φ φ' X θ ⟨k, by omega⟩ a b =
      (n : ℝ)⁻¹ * (netDeriv φ φ' X θ ⟨k, by omega⟩ a ⬝ᵥ netDeriv φ φ' X θ ⟨k, by omega⟩ b) := rfl
  rw [e1, e2]
  simp only [netGram]
  generalize backwardSensitivity d n0 n m φ φ' X θ ⟨k + 1, hk⟩ a = ua
  generalize backwardSensitivity d n0 n m φ φ' X θ ⟨k + 1, hk⟩ b = ub
  ring

/-- **Decomposition of `n⁻¹ ⟨h_k^c, g_k^a⟩`.** On the event that `Σ̂` is invertible,
`n⁻¹ ⟨h^c, g_k^a⟩ = n⁻¹ ∑ⱼ φ'(h^a)ⱼ h^cⱼ x^aⱼ + n⁻¹ √(n⁻¹) ⟨u^a, (V Pᗮ) (h^c ⊙ φ'(h^a))⟩`: the
projected part pairs through Cauchy–Schwarz, the residual part is a Gaussian linear form. -/
lemma gradIndep_decomp (θ : DeepMLPParams d n0 n) (k : ℕ) (hk : k + 1 < d) (hn : n ≠ 0)
    (hS : IsUnit (netGram φ X θ ⟨k, by omega⟩).det) (a c : Fin m) :
    gradIndep φ φ' X θ ⟨k, by omega⟩ a c =
      (𝔼 j, 1 * (netDeriv φ φ' X θ ⟨k, by omega⟩ a) j * ((deepMLPPreactivation d n0 n m φ X θ ⟨k,
          by omega⟩ c) j * (projPart φ φ' X θ k hk a) j)) +
      ((n : ℝ)⁻¹ * Real.sqrt ((n : ℝ)⁻¹)) *
        (backwardSensitivity d n0 n m φ φ' X θ ⟨k + 1, hk⟩ a ⬝ᵥ
          ((θ.Wh ⟨k, by omega⟩ *
              (1 - gramProjector (netFeat φ X θ ⟨k, by omega⟩))) *ᵥ
            fun j => deepMLPPreactivation d n0 n m φ X θ ⟨k, by omega⟩ c j *
              netDeriv φ φ' X θ ⟨k, by omega⟩ a j)) := by
  unfold gradIndep
  rw [backwardSensitivity_hidden_decomp φ φ' X θ k hk hn hS a]
  set W := θ.Wh ⟨k, by omega⟩ * (1 - gramProjector (netFeat φ X θ ⟨k, by omega⟩))
    with hW
  set u := backwardSensitivity d n0 n m φ φ' X θ ⟨k + 1, hk⟩ a with hu
  set b : Fin n → ℝ := fun j => deepMLPPreactivation d n0 n m φ X θ ⟨k, by omega⟩ c j *
    netDeriv φ φ' X θ ⟨k, by omega⟩ a j with hb
  have hy : ∀ j, resPart φ φ' X θ k hk a j = Real.sqrt ((n : ℝ)⁻¹) * (Wᵀ *ᵥ u) j := by
    intro j; simp [resPart, hW, hu]
  have hdot : b ⬝ᵥ (Wᵀ *ᵥ u) = u ⬝ᵥ (W *ᵥ b) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  have hsplit : ∑ j, deepMLPPreactivation d n0 n m φ X θ ⟨k, by omega⟩ c j *
      (netDeriv φ φ' X θ ⟨k, by omega⟩ a j *
        (projPart φ φ' X θ k hk a j + resPart φ φ' X θ k hk a j)) =
      ∑ j, 1 * netDeriv φ φ' X θ ⟨k, by omega⟩ a j *
          (deepMLPPreactivation d n0 n m φ X θ ⟨k, by omega⟩ c j * projPart φ φ' X θ k hk a j) +
        Real.sqrt ((n : ℝ)⁻¹) * (u ⬝ᵥ (W *ᵥ b)) := by
    rw [← hdot, dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hy j, hb]
    simp only [netDeriv]
    ring
  simp only [expect_fin_eq_inv_mul_sum]
  simp only [dotProduct, netDeriv] at hsplit ⊢
  rw [hsplit]
  ring

end theta

/-! ### Splitting the layer `Wh k` from the rest -/

section split

variable {d n0 m : ℕ} (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)

/-- The forward features `Φ_k` as a function of the point of `DeepSpace`. -/
noncomputable def pastFeat (n : ℕ) (k : ℕ) (hk : k + 1 < d) (z : DeepSpace d) :
    Matrix (Fin n) (Fin m) ℝ :=
  netFeat φ X (deepParams d n0 n z) ⟨k, by omega⟩

/-- `g_{k+1}^a` as a function of the substituted weight `x` for `Wh k` and the point `z` of
`DeepSpace`: the vector `u` of the conditional Chebyshev bounds. -/
noncomputable def nextSens (n : ℕ) (k : ℕ) (hk : k + 1 < d) (a : Fin m) :
    Matrix (Fin n) (Fin n) ℝ × DeepSpace d → Fin n → ℝ := fun p =>
  backwardSensitivity d n0 n m φ φ' X ((deepParams d n0 n p.2).updateWh ⟨k, by omega⟩ p.1)
    ⟨k + 1, hk⟩ a

/-- Zeroing the layer `k + 1` does not change the forward pass up to layer `k`. -/
lemma preactivation_zeroLayer (n : ℕ) (k : ℕ) (hk : k + 1 < d) (ω : DeepSpace d) (ℓ : Fin d)
    (hℓ : ℓ.val ≤ k) (a : Fin m) :
    deepMLPPreactivation d n0 n m φ X
        (deepParams d n0 n (Function.update ω.1 (⟨k + 1, hk⟩ : Fin d) 0, ω.2)) ℓ a =
      deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω) ℓ a := by
  conv_rhs => rw [deepParams_eq_updateWh (n0 := n0) (n := n) ⟨k, by omega⟩ ω]
  rw [deepMLPPreactivation_updateWh_of_le φ X _ ⟨k, by omega⟩ _ ℓ hℓ]

/-- Zeroing the layer-`k + 1` weights does not change the past features `pastFeat` (they read only
layers `≤ k`). -/
lemma pastFeat_zeroLayer (n : ℕ) (k : ℕ) (hk : k + 1 < d) (ω : DeepSpace d) :
    pastFeat φ X n k hk (Function.update ω.1 (⟨k + 1, hk⟩ : Fin d) 0, ω.2) =
      pastFeat φ X n k hk ω := by
  ext j a
  simp only [pastFeat, netFeat, Matrix.of_apply]
  rw [preactivation_zeroLayer φ X n k hk ω ⟨k, by omega⟩ le_rfl]

/-- Zeroing the layer-`k + 1` weights does not change the layer-`k` activation Gram matrix
`netGram`. -/
lemma netGram_zeroLayer (n : ℕ) (k : ℕ) (hk : k + 1 < d) (ω : DeepSpace d) :
    netGram φ X (deepParams d n0 n (Function.update ω.1 (⟨k + 1, hk⟩ : Fin d) 0, ω.2))
        ⟨k, by omega⟩ =
      netGram φ X (deepParams d n0 n ω) ⟨k, by omega⟩ := by
  have := pastFeat_zeroLayer (n0 := n0) φ X n k hk ω
  simp only [netGram]
  unfold pastFeat at this
  rw [this]

/-- Zeroing the layer-`k + 1` weights does not change the layer-`k` derivative vectors `netDeriv`.
-/
lemma netDeriv_zeroLayer (n : ℕ) (k : ℕ) (hk : k + 1 < d) (ω : DeepSpace d) (c : Fin m) :
    netDeriv φ φ' X (deepParams d n0 n (Function.update ω.1 (⟨k + 1, hk⟩ : Fin d) 0, ω.2))
        ⟨k, by omega⟩ c =
      netDeriv φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ c := by
  funext j
  simp only [netDeriv]
  rw [preactivation_zeroLayer φ X n k hk ω ⟨k, by omega⟩ le_rfl]

/-- If the normalized Gram matrix `n⁻¹ ΦᵀΦ` has unit determinant, so does `ΦᵀΦ`. -/
lemma isUnit_det_gram_of_netGram {n : ℕ} (Φ : Matrix (Fin n) (Fin m) ℝ)
    (h : IsUnit ((n : ℝ)⁻¹ • (Φᵀ * Φ)).det) : IsUnit (Φᵀ * Φ).det := by
  rw [Matrix.det_smul] at h
  exact (IsUnit.mul_iff.1 h).2

/-- On the event that `Σ̂` is invertible, the sensitivity `g_{k+1}` of the network at `ω` is
`nextSens` evaluated at the projected weight `V P` and the past: the structural fact that lets the
conditional Chebyshev bounds apply. -/
lemma atProj_nextSens_eq (n : ℕ) (k : ℕ) (hk : k + 1 < d) (ω : DeepSpace d)
    (a : Fin m) (hS : IsUnit (netGram φ X (deepParams d n0 n ω) ⟨k, by omega⟩).det) :
    atProj (pastFeat φ X n k hk) (nextSens φ φ' X n k hk a)
      ((Function.update ω.1 (⟨k + 1, hk⟩ : Fin d) 0, ω.2), layerBlock n (ω.1 ⟨k + 1, hk⟩)) =
      backwardSensitivity d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k + 1, hk⟩ a := by
  set z := (Function.update ω.1 (⟨k + 1, hk⟩ : Fin d) 0, ω.2) with hz
  set Y : Matrix (Fin n) (Fin n) ℝ := Matrix.of (layerBlock n (ω.1 ⟨k + 1, hk⟩)) with hY
  have hΦ : pastFeat φ X n k hk z = pastFeat φ X n k hk ω := pastFeat_zeroLayer φ X n k hk ω
  have hS' : IsUnit ((n : ℝ)⁻¹ • ((pastFeat φ X n k hk z)ᵀ * pastFeat φ X n k hk z)).det := by
    have := netGram_zeroLayer (n0 := n0) φ X n k hk ω
    rw [← hz] at this
    rw [← this] at hS
    exact hS
  have hU := isUnit_det_gram_of_netGram _ hS'
  have hdecomp := deepParams_eq_updateWh (n0 := n0) (n := n) ⟨k, by omega⟩ ω
  rw [← hz, ← hY] at hdecomp
  unfold atProj nextSens
  simp only
  rw [hdecomp]
  refine congrFun (backwardSensitivity_updateWh_congr φ φ' X (deepParams d n0 n z) k hk _ _
    fun b => ?_) a
  funext i
  have h := congrFun (congrFun (mul_eq_mul_gramProjector_mul Y (pastFeat φ X n k hk z) hU) i) b
  simp only [Matrix.mul_apply] at h
  simpa [Matrix.mulVec, dotProduct, pastFeat, netFeat, Matrix.mul_apply, hY] using h.symm

end split

/-! ### Measurability of the network objects fed to the residual lemmas -/

section measurability

variable {d n0 m : ℕ} {φ φ' : ℝ → ℝ} (hφ : Measurable φ) (hφ' : Measurable φ')
  (X : Fin m → Fin n0 → ℝ)

/-- The substitution `(Y, ω) ↦ θ(ω)[W_{k+1} ← Y]` is a measurable family of parameter records. -/
lemma paramsMeasurable_updateWh_matrix (n : ℕ) (k : Fin (d - 1)) :
    ParamsMeasurable (fun p : Matrix (Fin n) (Fin n) ℝ × DeepSpace d =>
      (deepParams d n0 n p.2).updateWh k p.1) where
  W0 j i := (paramsMeasurable_deepParams d n0 n).W0 j i |>.comp measurable_snd
  Wh ℓ j i := by
    by_cases h : ℓ = k
    · subst h
      simp only [DeepMLPParams.updateWh_Wh_self]
      exact measurable_matrix_entry measurable_fst j i
    · simp only [DeepMLPParams.updateWh_Wh_of_ne _ _ h]
      exact (paramsMeasurable_deepParams d n0 n).Wh ℓ j i |>.comp measurable_snd
  Wd j := (paramsMeasurable_deepParams d n0 n).Wd j |>.comp measurable_snd

include hφ hφ' in
/-- The next-layer sensitivity vector `g_{k+1}` is measurable on `DeepSpace`. -/
lemma measurable_nextSens (n k : ℕ) (hk : k + 1 < d) (a : Fin m) :
    Measurable (nextSens φ φ' X (d := d) (n0 := n0) n k hk a) := by
  refine measurable_pi_iff.2 fun j => ?_
  exact measurable_backwardSensitivity (paramsMeasurable_updateWh_matrix (n0 := n0) n ⟨k, by omega⟩)
    hφ hφ' X ⟨k + 1, hk⟩ a j

include hφ in
/-- The preactivations of the network `deepParams` are measurable on `DeepSpace`. -/
lemma measurable_netPre (n : ℕ) (ℓ : Fin d) (a : Fin m) (j : Fin n) :
    Measurable fun ω : DeepSpace d =>
      deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω) ℓ a j :=
  measurable_deepMLPPreactivation (paramsMeasurable_deepParams d n0 n) hφ X ℓ a j

/-- Fourth-moment averages `𝔼 j, (v z j)⁴` of a measurable family are measurable. -/
lemma measurable_avg4 {Z : Type*} [MeasurableSpace Z] {n : ℕ} {v : Z → Fin n → ℝ}
    (hv : ∀ j, Measurable fun z => v z j) : Measurable fun z => (𝔼 j, (v z) j ^ 4) := by
  simp only [expect_fin_eq_inv_mul_sum]
  exact measurable_const.mul (Finset.measurable_sum _ fun j _ => (hv j).pow_const 4)

include hφ in
/-- The past feature matrix `pastFeat` is measurable on `DeepSpace`. -/
lemma measurable_pastFeat (n k : ℕ) (hk : k + 1 < d) :
    Measurable (pastFeat φ X (d := d) (n0 := n0) n k hk) := by
  refine Measurable.of_eval_matrix _ fun j a => ?_
  exact hφ.comp (measurable_netPre hφ X n ⟨k, by omega⟩ a j)

include hφ hφ' in
/-- The diagonal matrix `diag (φ'(h_k^a) φ'(h_k^b))` is measurable on `DeepSpace`. -/
lemma measurable_diagDeriv (n k : ℕ) (hk : k + 1 < d) (a b : Fin m) :
    Measurable fun ω : DeepSpace d =>
      (Matrix.diagonal (fun j => netDeriv φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ a j *
        netDeriv φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ b j) : Matrix (Fin n) (Fin n) ℝ) := by
  refine Measurable.of_eval_matrix _ fun i j => ?_
  by_cases h : i = j
  · subst h
    simp only [Matrix.diagonal_apply_eq]
    exact (hφ'.comp (measurable_netPre hφ X n ⟨k, by omega⟩ a i)).mul
      (hφ'.comp (measurable_netPre hφ X n ⟨k, by omega⟩ b i))
  · simp only [Matrix.diagonal_apply_ne _ h]
    exact measurable_const

end measurability

/-! ### Forward ingredients as convergent sequences on `DeepSpace` -/

/-- The standing regularity of the activation `φ` and its derivative `φ'`: continuity and a common
polynomial growth bound. -/
structure ActivationData (φ φ' : ℝ → ℝ) : Type where
  /-- `φ` is continuous. -/
  cont : Continuous φ
  /-- `φ'` is continuous. -/
  cont' : Continuous φ'
  /-- The growth constant. -/
  C : ℝ
  /-- The growth constant is nonnegative. -/
  hC : 0 ≤ C
  /-- The growth exponent. -/
  p : ℕ
  /-- The growth exponent is positive. -/
  hp : 0 < p
  /-- `φ` has polynomial growth. -/
  growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p)
  /-- `φ'` has polynomial growth with the same constants. -/
  growth' : ∀ x : ℝ, |φ' x| ≤ C * (1 + |x| ^ p)

section forward

variable {d n0 m : ℕ} {φ φ' : ℝ → ℝ} (A : ActivationData φ φ') (X : Fin m → Fin n0 → ℝ)

include A

/-- A normalized same-feature average of the preactivations of layer `ℓ` converges in measure. -/
lemma featCov_cvg (ψ : ℝ → ℝ) (hψ : Continuous ψ) (Cψ : ℝ) (hCψ : 0 ≤ Cψ) (pψ : ℕ) (hpψ : 0 < pψ)
    (hg : ∀ x : ℝ, |ψ x| ≤ Cψ * (1 + |x| ^ pψ)) (ℓ : ℕ) (hℓ : ℓ < d) (a b : Fin m) :
    ∃ c : ℝ, TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) => (n : ℝ)⁻¹ * ∑ j : Fin n,
        ψ (deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω) ⟨ℓ, hℓ⟩ a j) *
        ψ (deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω) ⟨ℓ, hℓ⟩ b j))
      atTop (fun _ => c) :=
  ⟨_, deepSpace_featureCov_tendsto φ ψ A.cont hψ A.C A.hC A.p A.hp A.growth Cψ hCψ pψ hpψ hg X ℓ
    hℓ a b⟩

/-- Polynomial growth of `φ'²`: `|φ'(x)²| ≤ 2 C² (1 + |x|^{2p})`. -/
lemma growth_sq_deriv : ∀ x : ℝ, |φ' x ^ 2| ≤ (2 * A.C ^ 2) * (1 + |x| ^ (2 * A.p)) :=
  polynomial_growth_sq φ' A.C A.p A.growth'

/-- Polynomial growth of `φ²`: `|φ(x)²| ≤ 2 C² (1 + |x|^{2p})`. -/
lemma growth_sq_act : ∀ x : ℝ, |φ x ^ 2| ≤ (2 * A.C ^ 2) * (1 + |x| ^ (2 * A.p)) :=
  polynomial_growth_sq φ A.C A.p A.growth

/-- Same-sample fourth-moment averages `n⁻¹ ∑ⱼ φ'(h_ℓ^a,ⱼ)⁴` converge (feature `ψ = φ'²`), and more
generally the cross averages `n⁻¹ ∑ⱼ φ'(h^a)² φ'(h^b)²`. -/
lemma derivSq_cvg (ℓ : ℕ) (hℓ : ℓ < d) (a b : Fin m) :
    ∃ c : ℝ, TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) => (n : ℝ)⁻¹ * ∑ j : Fin n,
        (φ' (deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω) ⟨ℓ, hℓ⟩ a j) *
          φ' (deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω) ⟨ℓ, hℓ⟩ b j)) ^ 2)
      atTop (fun _ => c) := by
  obtain ⟨c, hc⟩ := featCov_cvg (n0 := n0) A X (fun x => φ' x ^ 2) (A.cont'.pow 2)
    (2 * A.C ^ 2) (by have := A.hC; positivity) (2 * A.p) (by have := A.hp; omega)
    (growth_sq_deriv A) ℓ hℓ a b
  refine ⟨c, hc.congr_left fun n => Eventually.of_forall fun ω => ?_⟩
  refine congrArg _ (Finset.sum_congr rfl fun j _ => by ring)

/-- `n⁻¹ ∑ⱼ φ(h_ℓ^a,ⱼ)⁴` converges (feature `ψ = φ²`). -/
lemma actSq_cvg (ℓ : ℕ) (hℓ : ℓ < d) (a : Fin m) :
    ∃ c : ℝ, TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) => (n : ℝ)⁻¹ * ∑ j : Fin n,
        φ (deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω) ⟨ℓ, hℓ⟩ a j) ^ 4)
      atTop (fun _ => c) := by
  obtain ⟨c, hc⟩ := featCov_cvg (n0 := n0) A X (fun x => φ x ^ 2) (A.cont.pow 2)
    (2 * A.C ^ 2) (by have := A.hC; positivity) (2 * A.p) (by have := A.hp; omega)
    (growth_sq_act A) ℓ hℓ a a
  refine ⟨c, hc.congr_left fun n => Eventually.of_forall fun ω => ?_⟩
  refine congrArg _ (Finset.sum_congr rfl fun j _ => by ring)

/-- `n⁻¹ ∑ⱼ (h_ℓ^a,ⱼ)⁴` converges (feature `ψ = x²`). -/
lemma preFour_cvg (ℓ : ℕ) (hℓ : ℓ < d) (a : Fin m) :
    ∃ c : ℝ, TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        𝔼 j, deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω) ⟨ℓ, hℓ⟩ a j ^ 4)
      atTop (fun _ => c) := by
  obtain ⟨c, hc⟩ := featCov_cvg (n0 := n0) A X (fun x => x ^ 2) (continuous_id.pow 2) 1
    zero_le_one 2 (by norm_num) (fun x => by
      simp only [one_mul]; rw [abs_of_nonneg (by positivity)]; linarith [sq_abs x]) ℓ hℓ a a
  refine ⟨c, hc.congr_left fun n => Eventually.of_forall fun ω => ?_⟩
  simp only [expect_fin_eq_inv_mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => by ring)

/-- `n⁻¹ ∑ⱼ (h_ℓ^a,ⱼ)²` converges (feature `ψ = id`, i.e. the preactivation Gram diagonal). -/
lemma preSq_cvg (ℓ : ℕ) (hℓ : ℓ < d) (a : Fin m) :
    ∃ c : ℝ, TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) => (n : ℝ)⁻¹ * ∑ j : Fin n,
        deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω) ⟨ℓ, hℓ⟩ a j ^ 2)
      atTop (fun _ => c) := by
  obtain ⟨c, hc⟩ := featCov_cvg (n0 := n0) A X (fun x => x) continuous_id 1 zero_le_one 1
    one_pos (fun x => by simp only [one_mul, pow_one]; linarith [abs_nonneg x]) ℓ hℓ a a
  refine ⟨c, hc.congr_left fun n => Eventually.of_forall fun ω => ?_⟩
  refine congrArg _ (Finset.sum_congr rfl fun j _ => by ring)

end forward

/-! ### The empirical Gram `Σ̂` and its inverse -/

section gram

variable {d n0 m : ℕ} {φ φ' : ℝ → ℝ} (A : ActivationData φ φ') (X : Fin m → Fin n0 → ℝ)

/-- Entrywise formula `netGram θ k a b = n⁻¹ ∑ⱼ φ(h_k^a j) φ(h_k^b j)`. -/
lemma netGram_apply {n : ℕ} (θ : DeepMLPParams d n0 n) (k : Fin d) (a b : Fin m) :
    netGram φ X θ k a b = (n : ℝ)⁻¹ * ∑ j : Fin n,
      φ (deepMLPPreactivation d n0 n m φ X θ k a j) *
        φ (deepMLPPreactivation d n0 n m φ X θ k b j) := by
  simp [netGram, netFeat, Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply]

include A in
/-- `Σ̂_k → Σ^{k+1}` entrywise. -/
lemma netGram_entry_tendsto (k : ℕ) (hk : k < d) (a b : Fin m) :
    TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) => netGram φ X (deepParams d n0 n ω) ⟨k, hk⟩ a b) atTop
      (fun _ => layerCovarianceSeq 1 0 φ m
        (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (k + 1) a b) := by
  have := deepSpace_activationGram_tendsto φ A.cont A.C A.hC A.p A.hp A.growth X k hk a b
  simpa only [netGram_apply] using this

include A in
/-- The activation Gram matrix `netGram` converges in measure to the limiting forward kernel
`Σ^{k+1}` (entrywise convergence assembled into a matrix statement). -/
lemma netGram_matrix_tendsto (k : ℕ) (hk : k < d) :
    TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) => netGram φ X (deepParams d n0 n ω) ⟨k, hk⟩) atTop
      (fun _ => layerCovarianceSeq 1 0 φ m
        (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (k + 1)) :=
  tendstoInMeasure_matrix_of_entries fun a b => netGram_entry_tendsto A X k hk a b

include A in
/-- Under positive definiteness of the limit, `Σ̂⁻¹ → (Σ^{k+1})⁻¹` entrywise. -/
lemma netGram_inv_entry_tendsto (k : ℕ) (hk : k < d)
    (hpd : (layerCovarianceSeq 1 0 φ m
      (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (k + 1)).PosDef) (a b : Fin m) :
    TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) => (netGram φ X (deepParams d n0 n ω) ⟨k, hk⟩)⁻¹ a b)
      atTop
      (fun _ => (layerCovarianceSeq 1 0 φ m
        (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (k + 1))⁻¹ a b) := by
  have h := tendstoInMeasure_matrix_inv_of_posDef (netGram_matrix_tendsto A X k hk) hpd
  exact tendstoInMeasure_comp_of_continuousAt (g := fun M : Matrix (Fin m) (Fin m) ℝ => M a b) h
    (by exact ((continuous_apply b).comp (continuous_apply a)).continuousAt)

include A in
/-- **The bad event is asymptotically null.** `μ {Σ̂ singular} → 0` when the limit is positive
definite (the determinant converges to a positive number). -/
lemma netGram_singular_tendsto (k : ℕ) (hk : k < d)
    (hpd : (layerCovarianceSeq 1 0 φ m
      (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (k + 1)).PosDef) :
    Tendsto (fun n : ℕ => ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      {ω : DeepSpace d | ¬ IsUnit (netGram φ X (deepParams d n0 n ω) ⟨k, hk⟩).det})
      atTop (nhds 0) := by
  have hdet := tendstoInMeasure_comp_of_continuousAt
    (g := fun M : Matrix (Fin m) (Fin m) ℝ => M.det) (netGram_matrix_tendsto A X k hk)
    (by exact (continuous_id.matrix_det).continuousAt)
  rw [tendstoInMeasure_iff_dist] at hdet
  have hpos := hpd.det_pos
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hdet _ hpos)
    (fun _ => zero_le) fun n => measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq, Real.dist_eq] at hω ⊢
  have h0 : (netGram φ X (deepParams d n0 n ω) ⟨k, hk⟩).det = 0 := by
    by_contra h
    exact hω (isUnit_iff_ne_zero.2 h)
  rw [h0, zero_sub, abs_neg, abs_of_pos hpos]

end gram

/-! ### From the abstract residual lemma to the network -/

section bridge

variable {d n0 m : ℕ} (φ φ' : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)

/-- The layer split of `DeepSpace` at the population of `Wh k`: past (the population zeroed) and
the Gaussian block. -/
noncomputable def splitPt (n k : ℕ) (hk : k + 1 < d) (ω : DeepSpace d) :
    DeepSpace d × (Fin n → Fin n → ℝ) :=
  ((Function.update ω.1 (⟨k + 1, hk⟩ : Fin d) 0, ω.2), layerBlock n (ω.1 (⟨k + 1, hk⟩ : Fin d)))

/-- The expression whose concentration is given by `tendsto_residualQuadForm`, at the split
point of `ω`. -/
noncomputable def residAbs (n k : ℕ) (hk : k + 1 < d) (a b : Fin m) (ω : DeepSpace d) : ℝ :=
  let q := splitPt (d := d) n k hk ω
  ((n : ℝ) ^ 2)⁻¹ *
        (atProj (pastFeat φ X n k hk) (nextSens φ φ' X n k hk a) q ⬝ᵥ
          ((Matrix.of q.2 * (1 - gramProjector (pastFeat φ X n k hk q.1)) *
              Matrix.diagonal (fun j => netDeriv φ φ' X (deepParams d n0 n q.1) ⟨k, by omega⟩ a j *
                netDeriv φ φ' X (deepParams d n0 n q.1) ⟨k, by omega⟩ b j) *
            (Matrix.of q.2 * (1 - gramProjector (pastFeat φ X n k hk q.1)))ᵀ) *ᵥ
            atProj (pastFeat φ X n k hk) (nextSens φ φ' X n k hk b) q)) -
      ((n : ℝ) ^ 2)⁻¹ * ((atProj (pastFeat φ X n k hk) (nextSens φ φ' X n k hk a) q ⬝ᵥ
          atProj (pastFeat φ X n k hk) (nextSens φ φ' X n k hk b) q) *
        ((1 - gramProjector (pastFeat φ X n k hk q.1)) *
          Matrix.diagonal (fun j => netDeriv φ φ' X (deepParams d n0 n q.1) ⟨k, by omega⟩ a j *
            netDeriv φ φ' X (deepParams d n0 n q.1) ⟨k, by omega⟩ b j) *
          (1 - gramProjector (pastFeat φ X n k hk q.1))).trace)

/-- At a point where `Σ̂` is invertible, `residAbs` is the network quantity
`n⁻¹ ∑ⱼ φ'(h^a)ⱼ φ'(h^b)ⱼ y^aⱼ y^bⱼ` minus the conditional mean. -/
lemma residAbs_eq (n : ℕ) (k : ℕ) (hk : k + 1 < d) (a b : Fin m) (ω : DeepSpace d)
    (hS : IsUnit (netGram φ X (deepParams d n0 n ω) ⟨k, by omega⟩).det) :
    residAbs φ φ' X n k hk a b ω =
      (𝔼 j, (netDeriv φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ a) j * (netDeriv φ φ' X
          (deepParams d n0 n ω) ⟨k, by omega⟩ b) j * ((resPart φ φ' X
          (deepParams d n0 n ω) k hk a) j * (resPart φ φ' X (deepParams d n0 n ω) k hk b) j)) -
      ((n : ℝ) ^ 2)⁻¹ * ((backwardSensitivity d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k + 1, hk⟩ a ⬝ᵥ
          backwardSensitivity d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k + 1, hk⟩ b) *
        ((1 - gramProjector (netFeat φ X (deepParams d n0 n ω) ⟨k, by omega⟩)) *
          Matrix.diagonal (fun j => netDeriv φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ a j *
            netDeriv φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ b j) *
          (1 - gramProjector (netFeat φ X (deepParams d n0 n ω) ⟨k, by omega⟩))).trace) := by
  have hua := atProj_nextSens_eq φ φ' X n k hk ω a hS
  have hub := atProj_nextSens_eq φ φ' X n k hk ω b hS
  have hΦ : pastFeat φ X n k hk (Function.update ω.1 (⟨k + 1, hk⟩ : Fin d) 0, ω.2) =
      netFeat φ X (deepParams d n0 n ω) ⟨k, by omega⟩ := pastFeat_zeroLayer φ X n k hk ω
  have hD : ∀ c : Fin m, netDeriv φ φ' X
      (deepParams d n0 n (Function.update ω.1 (⟨k + 1, hk⟩ : Fin d) 0, ω.2))
      ⟨k, by omega⟩ c = netDeriv φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ c := by
    intro c
    funext j
    simp only [netDeriv]
    rw [preactivation_zeroLayer φ X n k hk ω ⟨k, by omega⟩ le_rfl]
  have hV : (deepParams d n0 n ω).Wh ⟨k, by omega⟩ =
      Matrix.of (layerBlock n (ω.1 (⟨k + 1, hk⟩ : Fin d))) := by
    have := deepParams_eq_updateWh (n0 := n0) (n := n) ⟨k, by omega⟩ ω
    rw [this]
    simp
  rw [wcov_resPart_eq φ φ' X (deepParams d n0 n ω) k hk a b, hV, ← hΦ]
  unfold residAbs splitPt
  simp only [hD]
  rw [hua, hub]

/-- The linear-form expression whose concentration is given by `tendsto_residualLinearForm`, at the
split point of `ω`, for `b = h_k^c ⊙ φ'(h_k^a)`. -/
noncomputable def linAbs (n k : ℕ) (hk : k + 1 < d) (a c : Fin m) (ω : DeepSpace d) : ℝ :=
  let q := splitPt (d := d) n k hk ω
  ((n : ℝ)⁻¹ * Real.sqrt ((n : ℝ)⁻¹)) *
    (atProj (pastFeat φ X n k hk) (nextSens φ φ' X n k hk a) q ⬝ᵥ
      ((Matrix.of q.2 * (1 - gramProjector (pastFeat φ X n k hk q.1))) *ᵥ
        fun j => deepMLPPreactivation d n0 n m φ X (deepParams d n0 n q.1) ⟨k, by omega⟩ c j *
          netDeriv φ φ' X (deepParams d n0 n q.1) ⟨k, by omega⟩ a j))

/-- At a point where `Σ̂` is invertible, `linAbs` is the residual contribution to
`n⁻¹ ⟨h^c, g_k^a⟩`. -/
lemma linAbs_eq (n : ℕ) (k : ℕ) (hk : k + 1 < d) (a c : Fin m) (ω : DeepSpace d)
    (hS : IsUnit (netGram φ X (deepParams d n0 n ω) ⟨k, by omega⟩).det) :
    linAbs φ φ' X n k hk a c ω =
      ((n : ℝ)⁻¹ * Real.sqrt ((n : ℝ)⁻¹)) *
        (backwardSensitivity d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k + 1, hk⟩ a ⬝ᵥ
          (((deepParams d n0 n ω).Wh ⟨k, by omega⟩ *
              (1 - gramProjector (netFeat φ X (deepParams d n0 n ω) ⟨k, by omega⟩))) *ᵥ
            fun j => deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω) ⟨k, by omega⟩ c j *
              netDeriv φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ a j)) := by
  have hua := atProj_nextSens_eq φ φ' X n k hk ω a hS
  have hΦ : pastFeat φ X n k hk (Function.update ω.1 (⟨k + 1, hk⟩ : Fin d) 0, ω.2) =
      netFeat φ X (deepParams d n0 n ω) ⟨k, by omega⟩ := pastFeat_zeroLayer φ X n k hk ω
  have hV : (deepParams d n0 n ω).Wh ⟨k, by omega⟩ =
      Matrix.of (layerBlock n (ω.1 (⟨k + 1, hk⟩ : Fin d))) := by
    have := deepParams_eq_updateWh (n0 := n0) (n := n) ⟨k, by omega⟩ ω
    rw [this]
    simp
  have hh : deepMLPPreactivation d n0 n m φ X
      (deepParams d n0 n (Function.update ω.1 (⟨k + 1, hk⟩ : Fin d) 0, ω.2)) ⟨k, by omega⟩ c =
      deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω) ⟨k, by omega⟩ c :=
    preactivation_zeroLayer φ X n k hk ω ⟨k, by omega⟩ le_rfl c
  rw [hV, ← hΦ]
  unfold linAbs splitPt
  simp only [netDeriv_zeroLayer φ φ' X n k hk ω, hh]
  rw [hua]

end bridge

/-! ### Concentration of the residual quadratic form -/

section residual

variable {d n0 m : ℕ} {φ φ' : ℝ → ℝ} (A : ActivationData φ φ') (X : Fin m → Fin n0 → ℝ)

/-- The squared Frobenius norm of a diagonal matrix is the sum of squares of its diagonal entries.
-/
lemma sum_sq_diagonal {n : ℕ} (v : Fin n → ℝ) :
    ∑ k, ∑ l, (Matrix.diagonal v) k l ^ 2 = ∑ j, v j ^ 2 := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hl; simp [Matrix.diagonal_apply_ne _ (Ne.symm hl)]
  · simp

/-- The set where `Σ̂_k` is invertible (and the width is positive). -/
def goodSet (X : Fin m → Fin n0 → ℝ) (k : ℕ) (hk : k < d) (n : ℕ) : Set (DeepSpace d) :=
  {ω | n ≠ 0 ∧ IsUnit (netGram φ X (deepParams d n0 n ω) ⟨k, hk⟩).det}

include A in
/-- The probability of the complement of the good set (where the empirical activation Gram is
invertible) tends to `0`, given positive definiteness of the limit. -/
lemma goodSet_compl_tendsto (k : ℕ) (hk : k < d)
    (hpd : (layerCovarianceSeq 1 0 φ m
      (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (k + 1)).PosDef) :
    Tendsto (fun n : ℕ => ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1)) (goodSet (φ := φ) X k hk n)ᶜ) atTop (nhds 0) := by
  refine (netGram_singular_tendsto A X k hk hpd).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  congr 1
  ext ω
  simp [goodSet, hn]

include A in
/-- `n⁻¹ ‖u^c‖²` at the projected point is tight: it equals `G_{k+1}^{cc}` on the good event. -/
lemma atProj_sq_bddByConv (k : ℕ) (hk : k + 1 < d)
    (hpd : (layerCovarianceSeq 1 0 φ m
      (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (k + 1)).PosDef)
    (hG : ∀ c : Fin m, ∃ c0 : ℝ, TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi
        fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi
            fun _ : ℕ => gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        deepSensitivityGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k + 1, by omega⟩ c c)
      atTop (fun _ => c0)) (c : Fin m) :
    BddByConv ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _
        : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) (fun
            (n : ℕ) (ω : DeepSpace d) =>
      (n : ℝ)⁻¹ * (atProj (pastFeat φ X n k hk) (nextSens φ φ' X n k hk c) (splitPt n k hk ω) ⬝ᵥ
        atProj (pastFeat φ X n k hk) (nextSens φ φ' X n k hk c) (splitPt n k hk ω))) := by
  have hbad := goodSet_compl_tendsto (d := d) (n0 := n0) A X k (by omega) hpd
  obtain ⟨c0, hc⟩ := hG c
  refine BddByConv.of_tendstoInMeasure (c := c0) (tendstoInMeasure_congr_on_good
    (good := goodSet (d := d) (n0 := n0) (φ := φ) X k (by omega)) ?_ hbad hc)
  intro n ω hω
  obtain ⟨hn, hS⟩ := hω
  have := atProj_nextSens_eq φ φ' X n k hk ω c hS
  simp only [splitPt]
  rw [this, deepSensitivityGram_hidden d n0 n m φ φ' X _ (k + 1) hk, Matrix.of_apply]

include A in
/-- **The centered residual form tends to zero.** `n⁻² uᵀ (V Pᗮ) D (V Pᗮ)ᵀ v` minus its conditional
mean (`residAbs`) tends to `0` in measure, given that `G_{k+1}^{cc}` converges for every `c`. -/
theorem residAbs_tendsto (k : ℕ) (hk : k + 1 < d)
    (hpd : (layerCovarianceSeq 1 0 φ m
      (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (k + 1)).PosDef)
    (hG : ∀ c : Fin m, ∃ c0 : ℝ, TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi
        fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi
            fun _ : ℕ => gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        deepSensitivityGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k + 1, by omega⟩ c c)
      atTop (fun _ => c0)) (a b : Fin m) :
    TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) => residAbs φ φ' X n k hk a b ω) atTop (fun _ => 0) := by
  have hbad := goodSet_compl_tendsto (d := d) (n0 := n0) A X k (by omega) hpd
  have hφm : Measurable φ := A.cont.measurable
  have hφ'm : Measurable φ' := A.cont'.measurable
  have hcu : ∀ c : Fin m, BddByConv ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
          gaussianReal 0 1)) (fun (n : ℕ) (ω : DeepSpace d) =>
      (n : ℝ)⁻¹ * (atProj (pastFeat φ X n k hk) (nextSens φ φ' X n k hk c) (splitPt n k hk ω) ⬝ᵥ
        atProj (pastFeat φ X n k hk) (nextSens φ φ' X n k hk c) (splitPt n k hk ω))) :=
    atProj_sq_bddByConv A X k hk hpd hG
  have hcA : BddByConv ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
          gaussianReal 0 1)) (fun (n : ℕ) (ω : DeepSpace d) =>
      (n : ℝ)⁻¹ * ∑ i, ∑ l, (Matrix.diagonal (fun j =>
        netDeriv φ φ' X (deepParams d n0 n (splitPt n k hk ω).1) ⟨k, by omega⟩ a j *
        netDeriv φ φ' X (deepParams d n0 n (splitPt n k hk ω).1) ⟨k, by omega⟩ b j) :
        Matrix (Fin n) (Fin n) ℝ) i l ^ 2) := by
    obtain ⟨c, hc⟩ := derivSq_cvg (d := d) (n0 := n0) A X k (by omega) a b
    refine BddByConv.of_tendstoInMeasure (c := c) (hc.congr_left fun n =>
      Eventually.of_forall fun ω => ?_)
    simp only [splitPt, netDeriv_zeroLayer φ φ' X n k hk ω, sum_sq_diagonal]
    rfl
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have h := tendsto_residualQuadForm ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
          gaussianReal 0 1))
    (((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
        gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)).map
      (fun ω : DeepSpace d => (Function.update ω.1 (⟨k + 1, hk⟩ : Fin d) 0, ω.2)))
    (fun n ω => splitPt n k hk ω)
    (fun n => measurePreserving_layerSplit (⟨k + 1, hk⟩ : Fin d) n)
    (fun n => pastFeat φ X n k hk) (fun n => measurable_pastFeat hφm X n k hk)
    (fun (n : ℕ) (z : DeepSpace d) => (Matrix.diagonal (fun j =>
      netDeriv φ φ' X (deepParams d n0 n z) ⟨k, by omega⟩ a j *
      netDeriv φ φ' X (deepParams d n0 n z) ⟨k, by omega⟩ b j) : Matrix (Fin n) (Fin n) ℝ))
    (fun n => measurable_diagDeriv hφm hφ'm X n k hk a b)
    (fun n => nextSens φ φ' X n k hk a) (fun n => nextSens φ φ' X n k hk b)
    (fun n => measurable_nextSens hφm hφ'm X n k hk a)
    (fun n => measurable_nextSens hφm hφ'm X n k hk b) (hcu a) (hcu b) hcA hε
  simpa [residAbs, Real.dist_eq] using h

end residual

/-! ### Convergence of fourth-moment averages in the notation of the algebra -/

section avg

variable {d n0 m : ℕ} {φ φ' : ℝ → ℝ} (A : ActivationData φ φ') (X : Fin m → Fin n0 → ℝ)

include A in
/-- The fourth-moment averages of the derivative vectors `φ'(h_ℓ^a)` converge in measure to a
constant. -/
lemma avg4_deriv_cvg (ℓ : ℕ) (hℓ : ℓ < d) (a : Fin m) :
    ∃ c : ℝ, TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        (𝔼 j, (netDeriv φ φ' X (deepParams d n0 n ω) ⟨ℓ, hℓ⟩ a) j ^ 4)) atTop (fun _ => c) := by
  obtain ⟨c, hc⟩ := derivSq_cvg A X ℓ hℓ a a
  refine ⟨c, hc.congr_left fun n => Eventually.of_forall fun ω => ?_⟩
  simp only [expect_fin_eq_inv_mul_sum, netDeriv]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => by ring)

include A in
/-- The fourth-moment averages of the feature vectors `φ(h_ℓ^a)` converge in measure to a constant.
-/
lemma avg4_feat_cvg (ℓ : ℕ) (hℓ : ℓ < d) (a : Fin m) :
    ∃ c : ℝ, TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        (𝔼 j, netFeat φ X (deepParams d n0 n ω) ⟨ℓ, hℓ⟩ j a ^ 4)) atTop (fun _ => c) := by
  obtain ⟨c, hc⟩ := actSq_cvg A X ℓ hℓ a
  refine ⟨c, hc.congr_left fun n => Eventually.of_forall fun ω => ?_⟩
  simp only [expect_fin_eq_inv_mul_sum, netFeat, Matrix.of_apply]

end avg

/-! ### `G_⊥ − G_{k+1} Φ'_k → 0` -/

section gperp

variable {d n0 m : ℕ} {φ φ' : ℝ → ℝ} (A : ActivationData φ φ') (X : Fin m → Fin n0 → ℝ)

include A in
/-- **The residual Gram entry `G_⊥ = n⁻¹ ∑ⱼ φ'(h^a)ⱼ φ'(h^b)ⱼ y^aⱼ y^bⱼ` is asymptotically
`G_{k+1} Φ'_k`.** -/
theorem gperp_sub_tendsto (k : ℕ) (hk : k + 1 < d)
    (hpd : (layerCovarianceSeq 1 0 φ m
      (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (k + 1)).PosDef)
    (hG : ∀ c c' : Fin m, ∃ c0 : ℝ, TendstoInMeasure ((Measure.pi fun _ : Fin d =>
        Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
            (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        deepSensitivityGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k + 1, by omega⟩ c c')
      atTop (fun _ => c0)) (a b : Fin m) :
    TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        (𝔼 j, (netDeriv φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ a) j * (netDeriv φ φ' X
            (deepParams d n0 n ω) ⟨k, by omega⟩ b) j * ((resPart φ φ' X
            (deepParams d n0 n ω) k hk a) j * (resPart φ φ' X (deepParams d n0 n ω) k hk b) j)) -
        deepSensitivityGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k + 1, by omega⟩ a b *
          deepDerivativeGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ a b)
      atTop (fun _ => 0) := by
  have h1 := residAbs_tendsto A X k hk hpd (fun c => hG c c) a b
  obtain ⟨c0, hc0⟩ := hG a b
  have htr := tendstoInMeasure_inv_nat_mul_trace (μ := ((Measure.pi fun _ : Fin d =>
      Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
          (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)))
    (fun n ω => netDeriv φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ a)
    (fun n ω => netDeriv φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ b)
    (fun n ω => netFeat φ X (deepParams d n0 n ω) ⟨k, by omega⟩)
    (fun n ω => (netGram φ X (deepParams d n0 n ω) ⟨k, by omega⟩)⁻¹)
    (fun c c' => ⟨_, netGram_inv_entry_tendsto A X k (by omega) hpd c c'⟩)
    (avg4_deriv_cvg A X k (by omega) a) (avg4_deriv_cvg A X k (by omega) b)
    (fun c => avg4_feat_cvg A X k (by omega) c)
  have h2 := tendstoInMeasure_mul hc0 htr
  rw [mul_zero] at h2
  have h3 := tendstoInMeasure_sub h1 h2
  rw [sub_zero] at h3
  refine tendstoInMeasure_congr_on_good
    (good := goodSet (d := d) (n0 := n0) (φ := φ) X k (by omega)) ?_
    (goodSet_compl_tendsto (d := d) (n0 := n0) A X k (by omega) hpd) h3
  intro n ω hω
  obtain ⟨hn, hS⟩ := hω
  rw [residAbs_eq φ φ' X n k hk a b ω hS]
  have hmean := resid_mean_eq φ φ' X (deepParams d n0 n ω) k hk hn hS a b
  rw [hmean]
  ring

include A in
/-- **The residual linear form tends to zero.** -/
theorem linAbs_tendsto (k : ℕ) (hk : k + 1 < d)
    (hpd : (layerCovarianceSeq 1 0 φ m
      (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (k + 1)).PosDef)
    (hG : ∀ c : Fin m, ∃ c0 : ℝ, TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi
        fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi
            fun _ : ℕ => gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        deepSensitivityGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k + 1, by omega⟩ c c)
      atTop (fun _ => c0)) (a c : Fin m) :
    TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) => linAbs φ φ' X n k hk a c ω) atTop (fun _ => 0) := by
  have hφm : Measurable φ := A.cont.measurable
  have hφ'm : Measurable φ' := A.cont'.measurable
  have hcb : BddByConv ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
          gaussianReal 0 1)) (fun (n : ℕ) (ω : DeepSpace d) =>
      (n : ℝ)⁻¹ * ((fun j => deepMLPPreactivation d n0 n m φ X
          (deepParams d n0 n (splitPt n k hk ω).1) ⟨k, by omega⟩ c j *
        netDeriv φ φ' X (deepParams d n0 n (splitPt n k hk ω).1) ⟨k, by omega⟩ a j) ⬝ᵥ
        (fun j => deepMLPPreactivation d n0 n m φ X
          (deepParams d n0 n (splitPt n k hk ω).1) ⟨k, by omega⟩ c j *
        netDeriv φ φ' X (deepParams d n0 n (splitPt n k hk ω).1) ⟨k, by omega⟩ a j))) := by
    obtain ⟨c1, hc1⟩ := preFour_cvg (d := d) (n0 := n0) A X k (by omega) c
    obtain ⟨c2, hc2⟩ := avg4_deriv_cvg (d := d) (n0 := n0) A X k (by omega) a
    refine ⟨fun n ω => ((𝔼 j, (deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω)
        ⟨k, by omega⟩ c) j ^ 4) + (𝔼 j, (netDeriv φ φ' X (deepParams d n0 n ω) ⟨k,
            by omega⟩ a) j ^ 4)) / 2,
      (c1 + c2) / 2, fun n ω => ?_, tendstoInMeasure_half_sum hc1 hc2⟩
    have hh := preactivation_zeroLayer φ X n k hk ω ⟨k, by omega⟩ le_rfl c
    have hf := netDeriv_zeroLayer φ φ' X n k hk ω a
    simp only [splitPt]
    rw [hh, hf]
    exact avg_sq_mul_le_avg4
      (deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω) ⟨k, by omega⟩ c)
      (netDeriv φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ a)
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have h := tendsto_residualLinearForm ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
          gaussianReal 0 1))
    (((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
        gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)).map
      (fun ω : DeepSpace d => (Function.update ω.1 (⟨k + 1, hk⟩ : Fin d) 0, ω.2)))
    (fun n ω => splitPt n k hk ω)
    (fun n => measurePreserving_layerSplit (⟨k + 1, hk⟩ : Fin d) n)
    (fun n => pastFeat φ X n k hk) (fun n => measurable_pastFeat hφm X n k hk)
    (fun (n : ℕ) (z : DeepSpace d) (j : Fin n) => deepMLPPreactivation d n0 n m φ X
      (deepParams d n0 n z) ⟨k, by omega⟩ c j *
      netDeriv φ φ' X (deepParams d n0 n z) ⟨k, by omega⟩ a j)
    (fun n => measurable_pi_iff.2 fun j =>
      (measurable_netPre hφm X n ⟨k, by omega⟩ c j).mul
        (hφ'm.comp (measurable_netPre hφm X n ⟨k, by omega⟩ a j)))
    (fun n => nextSens φ φ' X n k hk a) (fun n => measurable_nextSens hφm hφ'm X n k hk a)
    (atProj_sq_bddByConv A X k hk hpd hG a) hcb hε
  simpa [linAbs, Real.dist_eq] using h

end gperp

/-! ### The projected part vanishes, and the decoupling statement -/

section decoupling

variable {d n0 m : ℕ} {φ φ' : ℝ → ℝ} (A : ActivationData φ φ') (X : Fin m → Fin n0 → ℝ)

/-- The diagonal of the weighted pairing is the weighted square: `wcov (f, f; y, y) = wsq (f; y)`.
-/
lemma wcov_self_eq_wsq {n : ℕ} (f y : Fin n → ℝ) : (𝔼 j, f j * f j * (y j * y j)) =
    (𝔼 j, f j ^ 2 * y j ^ 2) := by
  simp only [expect_fin_eq_inv_mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

include A in
/-- **The weighted size of the projected part tends to zero** under gradient independence
`I(k+1)`. -/
lemma wsq_projPart_tendsto (k : ℕ) (hk : k + 1 < d)
    (hpd : (layerCovarianceSeq 1 0 φ m
      (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (k + 1)).PosDef)
    (hI : ∀ a b : Fin m, TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ
        => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        gradIndep φ φ' X (deepParams d n0 n ω) ⟨k + 1, hk⟩ a b) atTop (fun _ => 0))
    (a : Fin m) :
    TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        (𝔼 j, (netDeriv φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ a) j ^ 2 * (projPart φ φ' X
            (deepParams d n0 n ω) k hk a) j ^ 2)) atTop (fun _ => 0) := by
  refine tendstoInMeasure_wsq_mulVec (μ := ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ :
      ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
          gaussianReal 0 1)))
    (fun n ω => netDeriv φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ a)
    (fun n ω => netFeat φ X (deepParams d n0 n ω) ⟨k, by omega⟩)
    (fun n ω => (netGram φ X (deepParams d n0 n ω) ⟨k, by omega⟩)⁻¹ *ᵥ
      fun b => gradIndep φ φ' X (deepParams d n0 n ω) ⟨k + 1, hk⟩ a b)
    ?_ (avg4_deriv_cvg A X k (by omega) a) (fun c => avg4_feat_cvg A X k (by omega) c)
  intro c
  have := tendstoInMeasure_sum_mul (μ := ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ
      => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
          gaussianReal 0 1)))
    (a := fun (b : Fin m) (n : ℕ) (ω : DeepSpace d) =>
      (netGram φ X (deepParams d n0 n ω) ⟨k, by omega⟩)⁻¹ c b)
    (b := fun (b : Fin m) (n : ℕ) (ω : DeepSpace d) =>
      gradIndep φ φ' X (deepParams d n0 n ω) ⟨k + 1, hk⟩ a b)
    (a' := fun b => (layerCovarianceSeq 1 0 φ m
      (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (k + 1))⁻¹ c b) (b' := fun _ => 0)
    (fun b => netGram_inv_entry_tendsto A X k (by omega) hpd c b) (fun b => hI a b)
  simpa [Matrix.mulVec, dotProduct] using this

include A in
/-- The derivative Gram entries converge in measure to a constant (`∃`-form of `derivGram_tendsto`).
-/
lemma derivGram_cvg (k : ℕ) (hk : k < d) (a b : Fin m) :
    ∃ c : ℝ, TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        deepDerivativeGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k, hk⟩ a b)
      atTop (fun _ => c) := by
  obtain ⟨c, hc⟩ := featCov_cvg (n0 := n0) A X φ' A.cont' A.C A.hC A.p A.hp A.growth' k hk a b
  refine ⟨c, hc.congr_left fun n => Eventually.of_forall fun ω => ?_⟩
  simp [deepDerivativeGram, dotProduct]

include A in
/-- **The decoupling approximation (the hard core of the backward induction).** For a
hidden layer `k` with `k + 1 < d`, the backward Gram entry at layer `k` is asymptotically the
product of the backward Gram entry at layer `k + 1` and the derivative Gram entry at layer `k`:
`G_k^{(n),αβ} - G_{k+1}^{(n),αβ} · Φ'^{(n),αβ}_k → 0` in measure.

**Extra hypothesis `hnd`:** the limiting forward kernel `Σ^ℓ = layerCovarianceSeq 1 0 φ m Φ0 ℓ`
(the limit of the activation Gram `n⁻¹ ⟨φ(h_{ℓ-1}^α), φ(h_{ℓ-1}^β)⟩`, `Φ0 = X Xᵀ / n0`) is
**positive definite** for every `1 ≤ ℓ < d` (the input layer `ℓ = 0` is not constrained). The
orthogonal projector onto the span of the `m` forward features is controlled through the inverse
`Σ̂⁻¹` of the empirical Gram, which is only uniformly bounded when the limiting Gram is invertible.
The hypothesis is expected to hold for generic inputs and a non-polynomial activation (not proved
here), but it fails for linear `φ` once `m > n0`, and for repeated or collinear inputs. It is *not*
needed for the forward results, and is the only reason the backward induction and Theorem 2.27
below carry it.

**Proof.** With `D = diag(φ'(h_k^α) φ'(h_k^β))` and `u^γ = g_{k+1}^γ`,
`G_k^{αβ} = n⁻² (u^α)ᵀ W_{k+1} D W_{k+1}ᵀ u^β`. Let `Φ = [φ(h_k^1) … φ(h_k^m)]` and `P` the
orthogonal projector onto its span, so `n^{-1/2} W_{k+1}ᵀ u = x + y` with the projected part
`x = Φ (Σ̂⁻¹ ζ)`, `ζ = n⁻¹ ⟨h_{k+1}, u⟩`, and the residual `y = n^{-1/2} (W_{k+1} Pᗮ)ᵀ u`
(`backwardSensitivity_hidden_decomp`). The forward pass, hence `u`, sees `W_{k+1}` only through
`W_{k+1} P` (`backwardSensitivity_updateWh_congr`), while the residual `W_{k+1} Pᗮ` is independent
of `(W_{k+1} P, later layers)` (Lemma 2.26, `measurePreserving_layerSplit`).

* *Residual part* (`gperp_sub_tendsto`): conditionally on `(W_{k+1} P, past, future)` the
  quadratic form `n⁻² uᵀ (W Pᗮ) D (W Pᗮ)ᵀ v` has mean `G_{k+1} Φ'_k − G_{k+1} n⁻¹ tr(D P)` and
  variance `O(n⁻¹)` (`tendsto_residualQuadForm`, from Isserlis), and `n⁻¹ tr(D P) → 0`
  (`tendstoInMeasure_inv_nat_mul_trace`).
* *Projected part* (`wsq_projPart_tendsto`): vanishes thanks to the **gradient-independence
  invariant** `I(ℓ): n⁻¹ ⟨h_ℓ^b, g_ℓ^a⟩ → 0` (`ζ → 0`), with `Σ̂⁻¹ → (Σ^{k+1})⁻¹` bounded.
* *Assembly* (`decoupling_tendsto`): Cauchy–Schwarz `|G_k − G_⊥|² ≤ 3 [N_f(x) N_g(x') + N_f(x)
  N_g(y') + N_f(y) N_g(x')]` (`wcov_sub_sq_le`).

The invariant `I` and the decoupling are proved in one joint downward induction on `DeepSpace`
(`deepSpace_sensitivity_induction`, `Deep/BackwardInduction.lean`); this statement is its
`ℓ = k` instance, with `hnd` at layer `k + 1`, convergence of `G_{k+1}` and gradient independence
`I(k+1)` as hypotheses. -/
theorem decoupling_tendsto (k : ℕ) (hk : k + 1 < d)
    (hpd : (layerCovarianceSeq 1 0 φ m
      (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (k + 1)).PosDef)
    (hG : ∀ c c' : Fin m, ∃ c0 : ℝ, TendstoInMeasure ((Measure.pi fun _ : Fin d =>
        Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
            (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        deepSensitivityGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k + 1, by omega⟩ c c')
      atTop (fun _ => c0))
    (hI : ∀ a b : Fin m, TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ
        => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        gradIndep φ φ' X (deepParams d n0 n ω) ⟨k + 1, hk⟩ a b) atTop (fun _ => 0))
    (a b : Fin m) :
    TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        deepSensitivityGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ a b -
        deepSensitivityGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k + 1, by omega⟩ a b *
          deepDerivativeGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ a b)
      atTop (fun _ => 0) := by
  have hgp := gperp_sub_tendsto A X k hk hpd hG a b
  have hgpcc : ∀ c : Fin m, ∃ c1 : ℝ, TendstoInMeasure ((Measure.pi fun _ : Fin d =>
      Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
          (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        (𝔼 j, (netDeriv φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ c) j ^ 2 * (resPart φ φ' X
            (deepParams d n0 n ω) k hk c) j ^ 2)) atTop (fun _ => c1) := by
    intro c
    obtain ⟨c0, hc0⟩ := hG c c
    obtain ⟨c1, hc1⟩ := derivGram_cvg (d := d) (n0 := n0) A X k (by omega) c c
    have h := gperp_sub_tendsto A X k hk hpd hG c c
    have hsum := tendstoInMeasure_add h (tendstoInMeasure_mul hc0 hc1)
    refine ⟨0 + c0 * c1, hsum.congr_left fun n => Eventually.of_forall fun ω => ?_⟩
    simp only [wcov_self_eq_wsq]
    ring
  obtain ⟨cya, hya⟩ := hgpcc a
  obtain ⟨cyb, hyb⟩ := hgpcc b
  have hT := tendstoInMeasure_three_terms
    (wsq_projPart_tendsto A X k hk hpd hI a) (wsq_projPart_tendsto A X k hk hpd hI b) hya hyb
  have h1 : TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
          gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        deepSensitivityGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ a b -
        (𝔼 j, (netDeriv φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ a) j * (netDeriv φ φ' X
            (deepParams d n0 n ω) ⟨k, by omega⟩ b) j * ((resPart φ φ' X
            (deepParams d n0 n ω) k hk a) j * (resPart φ φ' X (deepParams d n0 n
            ω) k hk b) j))) atTop (fun _ => 0) := by
    refine tendstoInMeasure_zero_of_sq_le_on_good
      (good := goodSet (d := d) (n0 := n0) (φ := φ) X k (by omega)) ?_ hT
      (goodSet_compl_tendsto (d := d) (n0 := n0) A X k (by omega) hpd)
    intro n ω hω
    obtain ⟨hn, hS⟩ := hω
    rw [deepSensitivityGram_hidden_eq_wcov φ φ' X (deepParams d n0 n ω) k hk hn hS a b]
    exact wcov_sub_sq_le _ _ _ _ _ _
  have := tendstoInMeasure_add h1 hgp
  rw [add_zero] at this
  refine this.congr_left fun n => Eventually.of_forall fun ω => ?_
  ring

include A in
/-- **Gradient independence propagates down one layer.** `I(k+1)` and the convergence of
`G_{k+1}` give `I(k)`: `n⁻¹ ⟨h_k^c, g_k^a⟩ → 0`. -/
theorem gradIndep_step_tendsto (k : ℕ) (hk : k + 1 < d)
    (hpd : (layerCovarianceSeq 1 0 φ m
      (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) (k + 1)).PosDef)
    (hG : ∀ c c' : Fin m, ∃ c0 : ℝ, TendstoInMeasure ((Measure.pi fun _ : Fin d =>
        Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
            (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        deepSensitivityGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k + 1, by omega⟩ c c')
      atTop (fun _ => c0))
    (hI : ∀ a b : Fin m, TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ
        => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        gradIndep φ φ' X (deepParams d n0 n ω) ⟨k + 1, hk⟩ a b) atTop (fun _ => 0))
    (a c : Fin m) :
    TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
            gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        gradIndep φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ a c) atTop (fun _ => 0) := by
  have hx := wsq_projPart_tendsto A X k hk hpd hI a
  obtain ⟨c1, hc1⟩ := preSq_cvg (d := d) (n0 := n0) A X k (by omega) c
  have hprod := tendstoInMeasure_mul hc1 hx
  rw [mul_zero] at hprod
  have hT1 : TendstoInMeasure ((Measure.pi fun _ : Fin d => Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ =>
          gaussianReal 0 1))
      (fun (n : ℕ) (ω : DeepSpace d) =>
        (𝔼 j, 1 * (netDeriv φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ a) j *
            ((deepMLPPreactivation d n0 n m φ X (deepParams d n0 n ω) ⟨k, by omega⟩ c) j *
            (projPart φ φ' X (deepParams d n0 n ω) k hk a) j))) atTop (fun _ => 0) := by
    refine tendstoInMeasure_zero_of_sq_le (fun n ω => ?_) hprod
    refine (wcov_sq_le _ _ _ _).trans (le_of_eq ?_)
    congr 1
    simp only [expect_fin_eq_inv_mul_sum, one_pow, one_mul]
  have hT2 := linAbs_tendsto A X k hk hpd (fun c' => hG c' c') a c
  have hsum := tendstoInMeasure_add hT1 hT2
  rw [add_zero] at hsum
  refine tendstoInMeasure_congr_on_good
    (good := goodSet (d := d) (n0 := n0) (φ := φ) X k (by omega)) ?_
    (goodSet_compl_tendsto (d := d) (n0 := n0) A X k (by omega) hpd) hsum
  intro n ω hω
  obtain ⟨hn, hS⟩ := hω
  rw [gradIndep_decomp φ φ' X (deepParams d n0 n ω) k hk hn hS a c,
    linAbs_eq φ φ' X n k hk a c ω hS]

end decoupling

end NTK

end
