/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Foundations.GramProjector

/-!
# Deterministic Algebra of the Backward Decoupling

Pure finite-dimensional identities and inequalities used in the decoupling approximation
`G_k ≈ G_{k+1} · Φ'_k` of `Deep/BackwardDecoupling.lean`. Nothing here is probabilistic.

Normalized pairings of vectors in `ℝⁿ` (`n⁻¹ ∑ⱼ …`):

* `wcov f g a b = n⁻¹ ∑ⱼ fⱼ gⱼ aⱼ bⱼ` and `wsq f a = n⁻¹ ∑ⱼ fⱼ² aⱼ²`;
* `wcov_sq_le`: Cauchy–Schwarz `wcov f g a b ² ≤ wsq f a · wsq g b`;
* `wcov_sub_sq_le`: if `s = x + y`, `s' = x' + y'` then
  `(wcov s s' − wcov y y')² ≤ 3 (N_f(x) N_g(x') + N_f(x) N_g(y') + N_f(y) N_g(x'))`.

The projected part of a back-propagated vector (`Vᵀ u = Φ c + (V Pᗮ)ᵀ u`, see
`transpose_mulVec_eq_gramProjector_add`) in normalized form: with `Σ̂ = n⁻¹ ΦᵀΦ`,
`H = n^{-1/2} V Φ` and `ζ = n⁻¹ Hᵀ u`, `n^{-1/2} Φ c = Φ (Σ̂⁻¹ ζ)` (`projected_part_eq`), and the
trace `tr(D P) = ∑_{ab} (Σ̂⁻¹)_{ab} M_{ba}` for `D = diag(f g)` (`trace_diagonal_gramProjector`).
Fourth-moment bounds (`abs_wmat_le`) dominate every such weighted Gram entry by averages of
fourth powers, which are covered by the forward feature-covariance theorem.
-/

@[expose]
public section

open Matrix
open scoped Matrix BigOperators

namespace NTK

variable {n m : ℕ}

/-- The weighted mean square `n⁻¹ ∑ⱼ fⱼ² aⱼ²` is nonnegative. -/
lemma wsq_nonneg (f a : Fin n → ℝ) : 0 ≤ 𝔼 j, f j ^ 2 * a j ^ 2 :=
  Finset.expect_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The normalized fourth moment `n⁻¹ ∑ⱼ vⱼ⁴` is nonnegative. -/
lemma avg4_nonneg (v : Fin n → ℝ) : 0 ≤ 𝔼 j, v j ^ 4 :=
  Finset.expect_nonneg fun _ _ => by positivity

/-- **Cauchy–Schwarz** for the weighted pairing. -/
lemma wcov_sq_le (f g a b : Fin n → ℝ) : (𝔼 j, f j * g j * (a j *
    b j)) ^ 2 ≤ (𝔼 j, f j ^ 2 * a j ^ 2) * (𝔼 j, g j ^ 2 * b j ^ 2) := by
  have hcs := dotProduct_sq_le_mul_self (fun j => f j * a j) (fun j => g j * b j)
  simp only [dotProduct] at hcs
  have hn : 0 ≤ ((n : ℝ)⁻¹) ^ 2 := sq_nonneg _
  have h1 : (𝔼 j, f j * g j * (a j * b j)) ^ 2 = ((n : ℝ)⁻¹) ^ 2 * (∑ j, f j * a j * (g j *
      b j)) ^ 2 := by
    simp only [expect_fin_eq_inv_mul_sum]
    rw [mul_pow]
    congr 2
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : (𝔼 j, f j ^ 2 * a j ^ 2) * (𝔼 j, g j ^ 2 * b j ^ 2) = ((n : ℝ)⁻¹) ^ 2 *
      ((∑ j, f j * a j * (f j * a j)) * ∑ j, g j * b j * (g j * b j)) := by
    simp only [expect_fin_eq_inv_mul_sum]
    rw [show ((n : ℝ)⁻¹ * ∑ j, f j ^ 2 * a j ^ 2) * ((n : ℝ)⁻¹ * ∑ j, g j ^ 2 * b j ^ 2) =
      ((n : ℝ)⁻¹) ^ 2 * ((∑ j, f j ^ 2 * a j ^ 2) * ∑ j, g j ^ 2 * b j ^ 2) by ring]
    congr 2
    · exact Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_congr rfl fun j _ => by ring
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_left hcs hn

lemma wcov_add_add (f g x y x' y' : Fin n → ℝ) :
    (𝔼 j, f j * g j * ((x + y) j * (x' + y') j)) =
      (𝔼 j, f j * g j * (x j * x' j)) + (𝔼 j, f j * g j * (x j * y' j)) + (𝔼 j, f j * g j * (y j *
          x' j)) + (𝔼 j, f j * g j * (y j * y' j)) := by
  simp only [expect_fin_eq_inv_mul_sum, Pi.add_apply]
  rw [← mul_add, ← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Decoupling of the weighted pairing.** If `s = x + y` and `s' = x' + y'` then the pairing of
`s, s'` differs from the pairing of the residuals `y, y'` by a quantity controlled by
`N_f(x) N_g(x') + N_f(x) N_g(y') + N_f(y) N_g(x')`. -/
lemma wcov_sub_sq_le (f g x y x' y' : Fin n → ℝ) :
    ((𝔼 j, f j * g j * ((x + y) j * (x' + y') j)) - (𝔼 j, f j * g j * (y j * y' j))) ^ 2 ≤
      3 * ((𝔼 j, f j ^ 2 * x j ^ 2) * (𝔼 j, g j ^ 2 * x' j ^ 2) + (𝔼 j, f j ^ 2 * x j ^ 2) * (𝔼 j, g j ^ 2 * y' j ^ 2) + (𝔼 j, f j ^ 2 * y j ^ 2) * (𝔼 j, g j ^ 2 * x' j ^ 2)) := by
  rw [wcov_add_add]
  have h1 := wcov_sq_le f g x x'
  have h2 := wcov_sq_le f g x y'
  have h3 := wcov_sq_le f g y x'
  set A := (𝔼 j, f j * g j * (x j * x' j))
  set B := (𝔼 j, f j * g j * (x j * y' j))
  set C := (𝔼 j, f j * g j * (y j * x' j))
  have : (A + B + C + (𝔼 j, f j * g j * (y j * y' j)) - (𝔼 j, f j * g j * (y j * y' j))) ^ 2 = (A +
      B + C) ^ 2 := by ring
  rw [this]
  nlinarith [sq_nonneg (A - B), sq_nonneg (B - C), sq_nonneg (A - C)]

/-! ### Fourth-moment domination of weighted Gram entries -/

lemma abs_mul_mul_mul_le (p q r s : ℝ) : |p * q * r * s| ≤ (p ^ 4 + q ^ 4 + r ^ 4 + s ^ 4) / 4 := by
  have h1 : |p * q| ≤ (p ^ 2 + q ^ 2) / 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (p + q), sq_nonneg (p - q)]
  have h2 : |r * s| ≤ (r ^ 2 + s ^ 2) / 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (r + s), sq_nonneg (r - s)]
  have h3 : |p * q * r * s| = |p * q| * |r * s| := by rw [mul_assoc, abs_mul]
  rw [h3]
  calc |p * q| * |r * s| ≤ ((p ^ 2 + q ^ 2) / 2) * ((r ^ 2 + s ^ 2) / 2) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ ≤ (p ^ 4 + q ^ 4 + r ^ 4 + s ^ 4) / 4 := by
        nlinarith [sq_nonneg (p ^ 2 - r ^ 2), sq_nonneg (p ^ 2 - s ^ 2),
          sq_nonneg (q ^ 2 - r ^ 2), sq_nonneg (q ^ 2 - s ^ 2)]

/-- Every weighted Gram entry is dominated by an average of fourth powers. -/
lemma abs_wmat_le (f g : Fin n → ℝ) (Φ : Matrix (Fin n) (Fin m) ℝ) (a b : Fin m) :
    |(𝔼 j, f j * g j * Φ j a * Φ j b)| ≤ ((𝔼 j, f j ^ 4) + (𝔼 j, g j ^ 4) + (𝔼 j, Φ j a ^ 4) + (𝔼 j, (fun j =>
        Φ j b) j ^ 4)) / 4 := by
  simp only [expect_fin_eq_inv_mul_sum]
  have hn : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg n)
  rw [abs_mul, abs_of_nonneg hn]
  calc (n : ℝ)⁻¹ * |∑ j, f j * g j * Φ j a * Φ j b|
      ≤ (n : ℝ)⁻¹ * ∑ j, (f j ^ 4 + g j ^ 4 + Φ j a ^ 4 + Φ j b ^ 4) / 4 := by
        refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => abs_mul_mul_mul_le _ _ _ _)) hn
    _ = ((n : ℝ)⁻¹ * ∑ j, f j ^ 4 + (n : ℝ)⁻¹ * ∑ j, g j ^ 4 +
          (n : ℝ)⁻¹ * ∑ j, Φ j a ^ 4 + (n : ℝ)⁻¹ * ∑ j, Φ j b ^ 4) / 4 := by
        simp only [← Finset.sum_div, Finset.sum_add_distrib, mul_add, mul_div_assoc']

/-- `N_f(Φ w) = ∑_{ab} w_a w_b M(f,f)_{ab}`. -/
lemma wsq_mulVec_eq (f : Fin n → ℝ) (Φ : Matrix (Fin n) (Fin m) ℝ) (w : Fin m → ℝ) :
    (𝔼 j, f j ^ 2 * (Φ *ᵥ w) j ^ 2) = ∑ a, ∑ b, w a * w b * (𝔼 j, f j * f j * Φ j a * Φ j b) := by
  have key : ∀ j, f j ^ 2 * (∑ a, Φ j a * w a) ^ 2 =
      ∑ a, ∑ b, w a * w b * (f j * f j * Φ j a * Φ j b) := by
    intro j
    rw [sq (∑ a, _), Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  simp only [expect_fin_eq_inv_mul_sum]
  simp only [Matrix.mulVec, dotProduct, key, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring_nf

/-! ### The projected part of a back-propagated vector -/

/-- `(ΦᵀΦ)⁻¹ = n⁻¹ • (n⁻¹ ΦᵀΦ)⁻¹` when the normalized Gram matrix is invertible. -/
lemma inv_gram_eq_smul_inv_normalized (hn : n ≠ 0) (Φ : Matrix (Fin n) (Fin m) ℝ)
    (hS : IsUnit ((n : ℝ)⁻¹ • (Φᵀ * Φ)).det) :
    (Φᵀ * Φ)⁻¹ = (n : ℝ)⁻¹ • ((n : ℝ)⁻¹ • (Φᵀ * Φ))⁻¹ := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  refine Matrix.inv_eq_right_inv ?_
  have h1 : (Φᵀ * Φ) = (n : ℝ) • ((n : ℝ)⁻¹ • (Φᵀ * Φ)) := by
    rw [smul_smul, mul_inv_cancel₀ hn', one_smul]
  rw [Matrix.mul_smul]
  calc (n : ℝ)⁻¹ • ((Φᵀ * Φ) * ((n : ℝ)⁻¹ • (Φᵀ * Φ))⁻¹)
      = (n : ℝ)⁻¹ • (((n : ℝ) • ((n : ℝ)⁻¹ • (Φᵀ * Φ))) * ((n : ℝ)⁻¹ • (Φᵀ * Φ))⁻¹) := by
        rw [← h1]
    _ = (n : ℝ)⁻¹ • ((n : ℝ) • (((n : ℝ)⁻¹ • (Φᵀ * Φ)) * ((n : ℝ)⁻¹ • (Φᵀ * Φ))⁻¹)) := by
        rw [Matrix.smul_mul]
    _ = 1 := by
        rw [Matrix.mul_nonsing_inv _ hS, smul_smul, inv_mul_cancel₀ hn', one_smul]

/-- The projected part in normalized form: with `Σ̂ = n⁻¹ ΦᵀΦ` (invertible), `H = n^{-1/2} V Φ` and
`ζ = n⁻¹ Hᵀ u`, one has `n^{-1/2} Φ c = Φ (Σ̂⁻¹ ζ)` for `c = (ΦᵀΦ)⁻¹ (VΦ)ᵀ u`. -/
lemma projected_part_eq (hn : n ≠ 0) (Φ : Matrix (Fin n) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ)
    (u : Fin n → ℝ) (hS : IsUnit ((n : ℝ)⁻¹ • (Φᵀ * Φ)).det) :
    Real.sqrt ((n : ℝ)⁻¹) • (Φ *ᵥ ((Φᵀ * Φ)⁻¹ *ᵥ ((V * Φ)ᵀ *ᵥ u))) =
      Φ *ᵥ (((n : ℝ)⁻¹ • (Φᵀ * Φ))⁻¹ *ᵥ
        ((n : ℝ)⁻¹ • ((Real.sqrt ((n : ℝ)⁻¹) • (V * Φ))ᵀ *ᵥ u))) := by
  have hinv := inv_gram_eq_smul_inv_normalized hn Φ hS
  simp only [hinv, Matrix.transpose_smul, Matrix.smul_mulVec, Matrix.mulVec_smul]
  exact smul_comm _ _ _

/-- `tr(D P) = ∑_{ab} (Σ̂⁻¹)_{ab} M(f,g)_{ba}` for `D = diag(f g)`, `P` the Gram projector and
`Σ̂ = n⁻¹ ΦᵀΦ`. -/
lemma trace_diagonal_gramProjector (hn : n ≠ 0) (f g : Fin n → ℝ)
    (Φ : Matrix (Fin n) (Fin m) ℝ) (hS : IsUnit ((n : ℝ)⁻¹ • (Φᵀ * Φ)).det) :
    (Matrix.diagonal (fun j => f j * g j) * gramProjector Φ).trace =
      ∑ a, ∑ b, ((n : ℝ)⁻¹ • (Φᵀ * Φ))⁻¹ a b * (𝔼 j, f j * g j * Φ j b * Φ j a) := by
  have hinv := inv_gram_eq_smul_inv_normalized hn Φ hS
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
  simp only [gramProjector, hinv, Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply,
    smul_eq_mul, expect_fin_eq_inv_mul_sum]
  generalize ((n : ℝ)⁻¹ • (Φᵀ * Φ))⁻¹ = T
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine (Finset.sum_comm.trans ((Finset.sum_congr rfl fun _ _ => Finset.sum_comm).trans
    Finset.sum_comm)).trans ?_
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The weighted pairing of two residual vectors `s • (Wᵀ u)`, `s • (Wᵀ v)` with `s² = n⁻¹` is the
normalized quadratic form `n⁻² uᵀ W diag(f g) Wᵀ v`. -/
lemma wcov_smul_transpose_mulVec (f g u v : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (s : ℝ)
    (hs : s ^ 2 = (n : ℝ)⁻¹) :
    (𝔼 j, f j * g j * ((s • (Wᵀ *ᵥ u)) j * (s • (Wᵀ *ᵥ v)) j)) =
      ((n : ℝ) ^ 2)⁻¹ * (u ⬝ᵥ ((W * Matrix.diagonal (fun j => f j * g j) * Wᵀ) *ᵥ v)) := by
  have h1 : u ⬝ᵥ ((W * Matrix.diagonal (fun j => f j * g j) * Wᵀ) *ᵥ v) =
      ∑ j, f j * g j * ((Wᵀ *ᵥ u) j * (Wᵀ *ᵥ v) j) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [h1]
  simp only [expect_fin_eq_inv_mul_sum, Pi.smul_apply, smul_eq_mul]
  have : ∀ j, f j * g j * (s * (Wᵀ *ᵥ u) j * (s * (Wᵀ *ᵥ v) j)) =
      s ^ 2 * (f j * g j * ((Wᵀ *ᵥ u) j * (Wᵀ *ᵥ v) j)) := fun j => by ring
  simp only [this, ← Finset.mul_sum, hs]
  rw [← mul_assoc, ← mul_inv]
  ring_nf

/-- `n⁻¹ ‖h ⊙ f‖² ≤ (avg4 h + avg4 f) / 2` (AM–GM). -/
lemma avg_sq_mul_le_avg4 (h f : Fin n → ℝ) :
    (n : ℝ)⁻¹ * ((fun j => h j * f j) ⬝ᵥ (fun j => h j * f j)) ≤ ((𝔼 j, h j ^ 4) + (𝔼 j, f j ^ 4)) / 2 := by
  simp only [expect_fin_eq_inv_mul_sum, dotProduct]
  have hn : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg n)
  calc (n : ℝ)⁻¹ * ∑ j, h j * f j * (h j * f j)
      ≤ (n : ℝ)⁻¹ * ∑ j, (h j ^ 4 + f j ^ 4) / 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hn
        nlinarith [sq_nonneg (h j ^ 2 - f j ^ 2)]
    _ = ((n : ℝ)⁻¹ * ∑ j, h j ^ 4 + (n : ℝ)⁻¹ * ∑ j, f j ^ 4) / 2 := by
        simp only [← Finset.sum_div, Finset.sum_add_distrib, mul_add, mul_div_assoc']

end NTK

end
