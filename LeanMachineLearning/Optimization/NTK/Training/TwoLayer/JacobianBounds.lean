/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.Packing

/-!
# Two-layer network: Lipschitz bounds on the output Jacobian

Gap 4: the output Jacobian of the packed network is `O(1/√n)`-Lipschitz given a bound `R` on the
readout weights (`outputJacobian_netFromParams_frobenius_sub_le`), and the second-order Taylor
bound for the training outputs (Phase 12.2).

## Main results and proof outline

- `empiricalNTKMatrix_netFromParams_apply`:
  Two-block decomposition of the empirical NTK matrix.
- `outputJacobian_netFromParams_frobenius_sub_le` : **Gap 4 deliverable** - the output Jacobian
  is `O(1/√n)`-Lipschitz, given a bound `R` on the readout weights.
- `norm_trainingOutputs_netFromParams_sub_linearization_le` : **Phase 12.2** - second-order Taylor
  bound `(K / (2 √n)) ‖θ - θ₀‖²` for the packed network (hidden and readout weights trained).

See `LeanMachineLearning.Optimization.NTK.Training.TwoLayer` for the overview of the whole
development.
-/

namespace NTK

open ConvexOpt MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Matrix Matrix.Norms.Frobenius

attribute [local instance]
  Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace

@[expose] public section

/-! ### Phase 4: Local Lipschitz Bound on the Output Jacobian -/

lemma two_mul_add_two_mul_sq (u v : ℝ) :
    (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := by
  have : 0 ≤ (u - v) ^ 2 := sq_nonneg (u - v)
  linarith

lemma norm_sq_sub_unpack (n d : ℕ) (θ₁ θ₂ : EuclideanSpace ℝ (Fin (n * d + n))) :
    ‖θ₁ - θ₂‖ ^ 2 =
      (∑ i : Fin n, ∑ j : Fin d, (unpackW θ₁ i j - unpackW θ₂ i j) ^ 2) +
      ∑ i : Fin n, (unpackA θ₁ i - unpackA θ₂ i) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [← Equiv.sum_comp (paramIndexEquiv n d)]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  apply congr_arg₂
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change ((θ₁ - θ₂) (idxW i j)) ^ 2 = _
    simp only [PiLp.sub_apply, unpackW]
  · apply Finset.sum_congr rfl
    intro i _
    change ((θ₁ - θ₂) (idxA i)) ^ 2 = _
    simp only [PiLp.sub_apply, unpackA]

lemma dotProduct_sub_sq_le (d : ℕ) (x y z : Fin d → ℝ) :
    (x ⬝ᵥ z - y ⬝ᵥ z) ^ 2 ≤ (∑ j : Fin d, (x j - y j) ^ 2) * (∑ j : Fin d, z j ^ 2) := by
  rw [← sub_dotProduct]
  exact sq_dotProduct_le (x - y) z

lemma outputJacobian_sub_frobenius_norm_sq (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (θ₁ θ₂ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ₁ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ₁ i ⬝ᵥ X α))
    (hφ₂ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ₂ i ⬝ᵥ X α)) :
    ‖outputJacobian (netFromParams φ n d) X θ₁ -
        outputJacobian (netFromParams φ n d) X θ₂‖ ^ 2 =
      (∑ α : Fin m, ∑ i : Fin n, ∑ j : Fin d,
        (gradW φ n d (X α) θ₁ i j - gradW φ n d (X α) θ₂ i j) ^ 2) +
      ∑ α : Fin m, ∑ i : Fin n,
        (gradA φ n d (X α) θ₁ i - gradA φ n d (X α) θ₂ i) ^ 2 := by
  rw [matrix_frobenius_norm_sq]
  simp_rw [Matrix.sub_apply]
  simp_rw [← Equiv.sum_comp (paramIndexEquiv n d)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change (outputJacobian (netFromParams φ n d) X θ₁ α (idxW i j) -
            outputJacobian (netFromParams φ n d) X θ₂ α (idxW i j)) ^ 2 = _
    rw [outputJacobian_netFromParams_apply_W φ n d m X θ₁ hφ₁ α i j]
    rw [outputJacobian_netFromParams_apply_W φ n d m X θ₂ hφ₂ α i j]
  · apply Finset.sum_congr rfl
    intro i _
    change (outputJacobian (netFromParams φ n d) X θ₁ α (idxA i) -
            outputJacobian (netFromParams φ n d) X θ₂ α (idxA i)) ^ 2 = _
    rw [outputJacobian_netFromParams_apply_a φ n d m X θ₁ hφ₁ α i]
    rw [outputJacobian_netFromParams_apply_a φ n d m X θ₂ hφ₂ α i]

lemma grad_single_neuron_sub_le (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ₁ θ₂ : EuclideanSpace ℝ (Fin (n * d + n))) (i : Fin n)
    (C₁ C₂ R : ℝ) (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hR_nonneg : 0 ≤ R)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_bound : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (ha₁ : |unpackA θ₁ i| ≤ R) :
    let Sx := ∑ j : Fin d, x j ^ 2
    let Wdiff := ∑ j : Fin d, (unpackW θ₁ i j - unpackW θ₂ i j) ^ 2
    let Adiff := (unpackA θ₁ i - unpackA θ₂ i) ^ 2
    (∑ j : Fin d, (gradW φ n d x θ₁ i j - gradW φ n d x θ₂ i j) ^ 2) +
      (gradA φ n d x θ₁ i - gradA φ n d x θ₂ i) ^ 2 ≤
        (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx) * (Wdiff + Adiff) := by
  dsimp only
  let Sx := ∑ j : Fin d, x j ^ 2
  let Wdiff := ∑ j : Fin d, (unpackW θ₁ i j - unpackW θ₂ i j) ^ 2
  let Adiff := (unpackA θ₁ i - unpackA θ₂ i) ^ 2
  have hSx_nonneg : 0 ≤ Sx := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hWdiff_nonneg : 0 ≤ Wdiff := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hAdiff_nonneg : 0 ≤ Adiff := sq_nonneg _
  have hroot_sq : ((n : ℝ)⁻¹.sqrt) ^ 2 = (n : ℝ)⁻¹ := by
    rw [Real.sq_sqrt]
    positivity
  let u₁ := unpackW θ₁ i ⬝ᵥ x
  let u₂ := unpackW θ₂ i ⬝ᵥ x
  have hu_diff_sq : (u₁ - u₂) ^ 2 ≤ Wdiff * Sx := by
    dsimp [u₁, u₂, Wdiff, Sx]
    exact dotProduct_sub_sq_le d (unpackW θ₁ i) (unpackW θ₂ i) x
  have hφ_sub_sq : (φ u₁ - φ u₂) ^ 2 ≤ C₁ ^ 2 * (Sx * Wdiff) := by
    have h1 : |φ u₁ - φ u₂| ≤ C₁ * |u₁ - u₂| := hφ_lip u₁ u₂
    have h2 : |φ u₁ - φ u₂| ^ 2 ≤ (C₁ * |u₁ - u₂|) ^ 2 := by
      apply (sq_le_sq₀ (abs_nonneg _) _).2 h1
      exact mul_nonneg hC₁_nonneg (abs_nonneg _)
    rw [sq_abs, mul_pow, sq_abs] at h2
    calc
      (φ u₁ - φ u₂) ^ 2 ≤ C₁ ^ 2 * (u₁ - u₂) ^ 2 := h2
      _ ≤ C₁ ^ 2 * (Wdiff * Sx) :=
        mul_le_mul_of_nonneg_left hu_diff_sq (by positivity)
      _ = C₁ ^ 2 * (Sx * Wdiff) := by ring
  have hderiv_sub_sq : (deriv φ u₁ - deriv φ u₂) ^ 2 ≤ C₂ ^ 2 * (Sx * Wdiff) := by
    have h1 : |deriv φ u₁ - deriv φ u₂| ≤ C₂ * |u₁ - u₂| := hderiv_lip u₁ u₂
    have h2 : |deriv φ u₁ - deriv φ u₂| ^ 2 ≤ (C₂ * |u₁ - u₂|) ^ 2 := by
      apply (sq_le_sq₀ (abs_nonneg _) _).2 h1
      exact mul_nonneg hC₂_nonneg (abs_nonneg _)
    rw [sq_abs, mul_pow, sq_abs] at h2
    calc
      (deriv φ u₁ - deriv φ u₂) ^ 2 ≤ C₂ ^ 2 * (u₁ - u₂) ^ 2 := h2
      _ ≤ C₂ ^ 2 * (Wdiff * Sx) :=
        mul_le_mul_of_nonneg_left hu_diff_sq (by positivity)
      _ = C₂ ^ 2 * (Sx * Wdiff) := by ring
  have hA_term : (gradA φ n d x θ₁ i - gradA φ n d x θ₂ i) ^ 2 ≤
      (n : ℝ)⁻¹ * (C₁ ^ 2 * Sx * Wdiff) := by
    dsimp [gradA, u₁, u₂]
    rw [← mul_sub, mul_pow, hroot_sq]
    have h_sub : (φ (unpackW θ₁ i ⬝ᵥ x) - φ (unpackW θ₂ i ⬝ᵥ x)) ^ 2 ≤
        C₁ ^ 2 * (Sx * Wdiff) := hφ_sub_sq
    have h_prod := mul_le_mul_of_nonneg_left h_sub (by positivity : 0 ≤ (n : ℝ)⁻¹)
    calc
      (n : ℝ)⁻¹ * (φ (unpackW θ₁ i ⬝ᵥ x) - φ (unpackW θ₂ i ⬝ᵥ x)) ^ 2
        ≤ (n : ℝ)⁻¹ * (C₁ ^ 2 * (Sx * Wdiff)) := h_prod
      _ = (n : ℝ)⁻¹ * (C₁ ^ 2 * Sx * Wdiff) := by ring
  have hD_sq : (unpackA θ₁ i * deriv φ u₁ - unpackA θ₂ i * deriv φ u₂) ^ 2 ≤
      2 * R ^ 2 * C₂ ^ 2 * Sx * Wdiff + 2 * C₁ ^ 2 * Adiff := by
    have hsplit : unpackA θ₁ i * deriv φ u₁ - unpackA θ₂ i * deriv φ u₂ =
        unpackA θ₁ i * (deriv φ u₁ - deriv φ u₂) +
        (unpackA θ₁ i - unpackA θ₂ i) * deriv φ u₂ := by ring
    rw [hsplit]
    have h2 := two_mul_add_two_mul_sq (unpackA θ₁ i * (deriv φ u₁ - deriv φ u₂))
      ((unpackA θ₁ i - unpackA θ₂ i) * deriv φ u₂)
    have ha₁_sq : (unpackA θ₁ i) ^ 2 ≤ R ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hR_nonneg).2 ha₁
    have hderiv_sq : (deriv φ u₂) ^ 2 ≤ C₁ ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hC₁_nonneg).2 (hderiv_bound u₂)
    have hpart1 : (unpackA θ₁ i * (deriv φ u₁ - deriv φ u₂)) ^ 2 ≤
        R ^ 2 * C₂ ^ 2 * Sx * Wdiff := by
      rw [mul_pow]
      calc
        (unpackA θ₁ i) ^ 2 * (deriv φ u₁ - deriv φ u₂) ^ 2
          ≤ R ^ 2 * (deriv φ u₁ - deriv φ u₂) ^ 2 :=
            mul_le_mul_of_nonneg_right ha₁_sq (sq_nonneg _)
        _ ≤ R ^ 2 * (C₂ ^ 2 * (Sx * Wdiff)) :=
          mul_le_mul_of_nonneg_left hderiv_sub_sq (by positivity)
        _ = R ^ 2 * C₂ ^ 2 * Sx * Wdiff := by ring
    have hpart2 : ((unpackA θ₁ i - unpackA θ₂ i) * deriv φ u₂) ^ 2 ≤
        C₁ ^ 2 * Adiff := by
      rw [mul_pow]
      dsimp [Adiff]
      calc
        (unpackA θ₁ i - unpackA θ₂ i) ^ 2 * (deriv φ u₂) ^ 2
          ≤ (unpackA θ₁ i - unpackA θ₂ i) ^ 2 * C₁ ^ 2 :=
            mul_le_mul_of_nonneg_left hderiv_sq (sq_nonneg _)
        _ = C₁ ^ 2 * (unpackA θ₁ i - unpackA θ₂ i) ^ 2 := by ring
    linarith
  have hW_term : (∑ j : Fin d, (gradW φ n d x θ₁ i j - gradW φ n d x θ₂ i j) ^ 2) ≤
      (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 * Wdiff + 2 * C₁ ^ 2 * Sx * Adiff) := by
    have hj : ∀ j : Fin d, (gradW φ n d x θ₁ i j - gradW φ n d x θ₂ i j) ^ 2 =
        (n : ℝ)⁻¹ * (unpackA θ₁ i * deriv φ u₁ - unpackA θ₂ i * deriv φ u₂) ^ 2 * x j ^ 2 := by
      intro j
      dsimp [gradW, u₁, u₂]
      have : (n : ℝ)⁻¹.sqrt * unpackA θ₁ i * deriv φ (unpackW θ₁ i ⬝ᵥ x) * x j -
             (n : ℝ)⁻¹.sqrt * unpackA θ₂ i * deriv φ (unpackW θ₂ i ⬝ᵥ x) * x j =
             (n : ℝ)⁻¹.sqrt *
              (unpackA θ₁ i * deriv φ (unpackW θ₁ i ⬝ᵥ x) -
               unpackA θ₂ i * deriv φ (unpackW θ₂ i ⬝ᵥ x)) * x j := by ring
      rw [this, mul_pow, mul_pow, hroot_sq]
    simp_rw [hj]
    rw [← Finset.mul_sum]
    have h_sum : (∑ j : Fin d, x j ^ 2) = Sx := rfl
    rw [h_sum]
    have h_prod := mul_le_mul_of_nonneg_right hD_sq hSx_nonneg
    have h_final := mul_le_mul_of_nonneg_left h_prod (by positivity : 0 ≤ (n : ℝ)⁻¹)
    calc
      (n : ℝ)⁻¹ * (unpackA θ₁ i * deriv φ u₁ - unpackA θ₂ i * deriv φ u₂) ^ 2 * Sx
        = (n : ℝ)⁻¹ * ((unpackA θ₁ i * deriv φ u₁ - unpackA θ₂ i * deriv φ u₂) ^ 2 * Sx) := by ring
      _ ≤ (n : ℝ)⁻¹ * ((2 * R ^ 2 * C₂ ^ 2 * Sx * Wdiff + 2 * C₁ ^ 2 * Adiff) * Sx) := h_final
      _ = (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 * Wdiff + 2 * C₁ ^ 2 * Sx * Adiff) := by ring
  calc
    (∑ j : Fin d, (gradW φ n d x θ₁ i j - gradW φ n d x θ₂ i j) ^ 2) +
        (gradA φ n d x θ₁ i - gradA φ n d x θ₂ i) ^ 2
      ≤ (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 * Wdiff + 2 * C₁ ^ 2 * Sx * Adiff) +
          (n : ℝ)⁻¹ * (C₁ ^ 2 * Sx * Wdiff) := add_le_add hW_term hA_term
    _ = (n : ℝ)⁻¹ * ((2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + C₁ ^ 2 * Sx) * Wdiff +
          2 * C₁ ^ 2 * Sx * Adiff) := by ring
    _ ≤ (n : ℝ)⁻¹ * ((2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx) * Wdiff +
          (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx) * Adiff) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hcoeff1 : 2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + C₁ ^ 2 * Sx ≤
          2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx := by
        have : C₁ ^ 2 * Sx ≤ 3 * C₁ ^ 2 * Sx := by nlinarith [sq_nonneg C₁]
        linarith
      have hcoeff2 : 2 * C₁ ^ 2 * Sx ≤
          2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx := by
        have hpos1 : 0 ≤ 2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 := by positivity
        have hpos2 : 2 * C₁ ^ 2 * Sx ≤ 3 * C₁ ^ 2 * Sx := by nlinarith [sq_nonneg C₁]
        linarith
      have h1 := mul_le_mul_of_nonneg_right hcoeff1 hWdiff_nonneg
      have h2 := mul_le_mul_of_nonneg_right hcoeff2 hAdiff_nonneg
      linarith
    _ = (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx) * (Wdiff + Adiff) := by
      ring


lemma grad_sum_neurons_sub_le (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ₁ θ₂ : EuclideanSpace ℝ (Fin (n * d + n)))
    (C₁ C₂ R : ℝ) (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hR_nonneg : 0 ≤ R)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_bound : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (ha₁ : ∀ i : Fin n, |unpackA θ₁ i| ≤ R) :
    let Sx := ∑ j : Fin d, x j ^ 2
    (∑ i : Fin n, ∑ j : Fin d, (gradW φ n d x θ₁ i j - gradW φ n d x θ₂ i j) ^ 2) +
      ∑ i : Fin n, (gradA φ n d x θ₁ i - gradA φ n d x θ₂ i) ^ 2 ≤
        (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx) * ‖θ₁ - θ₂‖ ^ 2 := by
  dsimp only
  let Sx := ∑ j : Fin d, x j ^ 2
  have h_single : ∀ i : Fin n,
      (∑ j : Fin d, (gradW φ n d x θ₁ i j - gradW φ n d x θ₂ i j) ^ 2) +
        (gradA φ n d x θ₁ i - gradA φ n d x θ₂ i) ^ 2 ≤
          (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx) *
            ((∑ j : Fin d, (unpackW θ₁ i j - unpackW θ₂ i j) ^ 2) +
             (unpackA θ₁ i - unpackA θ₂ i) ^ 2) := by
    intro i
    exact grad_single_neuron_sub_le φ n d x θ₁ θ₂ i C₁ C₂ R hC₁_nonneg hC₂_nonneg hR_nonneg
      hφ_lip hderiv_bound hderiv_lip (ha₁ i)
  rw [← Finset.sum_add_distrib]
  calc
    (∑ i : Fin n, ((∑ j : Fin d, (gradW φ n d x θ₁ i j - gradW φ n d x θ₂ i j) ^ 2) +
        (gradA φ n d x θ₁ i - gradA φ n d x θ₂ i) ^ 2))
      ≤ ∑ i : Fin n, (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx) *
          ((∑ j : Fin d, (unpackW θ₁ i j - unpackW θ₂ i j) ^ 2) +
           (unpackA θ₁ i - unpackA θ₂ i) ^ 2) := by
        apply Finset.sum_le_sum
        intro i _
        exact h_single i
    _ = (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx) *
        ∑ i : Fin n, ((∑ j : Fin d, (unpackW θ₁ i j - unpackW θ₂ i j) ^ 2) +
           (unpackA θ₁ i - unpackA θ₂ i) ^ 2) := by
      rw [← Finset.mul_sum]
    _ = (n : ℝ)⁻¹ * (2 * R ^ 2 * C₂ ^ 2 * Sx ^ 2 + 3 * C₁ ^ 2 * Sx) * ‖θ₁ - θ₂‖ ^ 2 := by
      rw [Finset.sum_add_distrib]
      rw [← norm_sq_sub_unpack n d θ₁ θ₂]

/-- Local Lipschitz bound on the output Jacobian of `netFromParams` in Frobenius norm.
For parameters `θ₁, θ₂` whose readout weights are bounded by `R`, the Frobenius difference
`‖J(θ₁) - J(θ₂)‖` is bounded by `(K / √n) * ‖θ₁ - θ₂‖`, where `K` is width-independent.
The `1 / √n` scaling rate is explicit. -/
theorem outputJacobian_netFromParams_frobenius_sub_le
    (φ : ℝ → ℝ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ)
    (θ₁ θ₂ : EuclideanSpace ℝ (Fin (n * d + n)))
    (C₁ C₂ R : ℝ) (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hR_nonneg : 0 ≤ R)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_bound : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (hφ₁ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ₁ i ⬝ᵥ X α))
    (hφ₂ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ₂ i ⬝ᵥ X α))
    (ha₁ : ∀ i : Fin n, |unpackA θ₁ i| ≤ R) :
    let K := Real.sqrt (∑ α : Fin m, (2 * R ^ 2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2 +
      3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2)))
    ‖outputJacobian (netFromParams φ n d) X θ₁ -
      outputJacobian (netFromParams φ n d) X θ₂‖ ≤
        (K / Real.sqrt (n : ℝ)) * ‖θ₁ - θ₂‖ := by
  dsimp only
  let S : Fin m → ℝ := fun α => ∑ j : Fin d, X α j ^ 2
  let term : Fin m → ℝ := fun α => 2 * R ^ 2 * C₂ ^ 2 * (S α) ^ 2 + 3 * C₁ ^ 2 * S α
  let K := Real.sqrt (∑ α : Fin m, term α)
  have hK_nonneg : 0 ≤ K := Real.sqrt_nonneg _
  have hroot_n_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have h_single : ∀ α : Fin m,
      (∑ i : Fin n, ∑ j : Fin d,
        (gradW φ n d (X α) θ₁ i j - gradW φ n d (X α) θ₂ i j) ^ 2) +
      ∑ i : Fin n, (gradA φ n d (X α) θ₁ i - gradA φ n d (X α) θ₂ i) ^ 2 ≤
        (n : ℝ)⁻¹ * term α * ‖θ₁ - θ₂‖ ^ 2 := by
    intro α
    exact grad_sum_neurons_sub_le φ n d (X α) θ₁ θ₂ C₁ C₂ R hC₁_nonneg hC₂_nonneg hR_nonneg
      hφ_lip hderiv_bound hderiv_lip ha₁
  have h_norm_sq := outputJacobian_sub_frobenius_norm_sq φ n d m X θ₁ θ₂ hφ₁ hφ₂
  have h_sum_le :
      ‖outputJacobian (netFromParams φ n d) X θ₁ -
          outputJacobian (netFromParams φ n d) X θ₂‖ ^ 2 ≤
        (K / Real.sqrt (n : ℝ)) ^ 2 * ‖θ₁ - θ₂‖ ^ 2 := by
    rw [h_norm_sq]
    rw [← Finset.sum_add_distrib]
    calc
      ∑ α : Fin m,
          ((∑ i : Fin n, ∑ j : Fin d,
            (gradW φ n d (X α) θ₁ i j - gradW φ n d (X α) θ₂ i j) ^ 2) +
          ∑ i : Fin n, (gradA φ n d (X α) θ₁ i - gradA φ n d (X α) θ₂ i) ^ 2)
        ≤ ∑ α : Fin m, (n : ℝ)⁻¹ * term α * ‖θ₁ - θ₂‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro α _
          exact h_single α
      _ = (n : ℝ)⁻¹ * (∑ α : Fin m, term α) * ‖θ₁ - θ₂‖ ^ 2 := by
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]
        rw [show (∑ α : Fin m, term α * ‖θ₁ - θ₂‖ ^ 2) =
            (∑ α : Fin m, term α) * ‖θ₁ - θ₂‖ ^ 2 by rw [← Finset.sum_mul]]
      _ = (K / Real.sqrt (n : ℝ)) ^ 2 * ‖θ₁ - θ₂‖ ^ 2 := by
        have h_sum_nonneg : 0 ≤ ∑ α : Fin m, term α := by
          apply Finset.sum_nonneg
          intro α _
          dsimp [term, S]
          positivity
        have hK_sq : K ^ 2 = ∑ α : Fin m, term α := Real.sq_sqrt h_sum_nonneg
        have hroot_sq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
        rw [div_pow, hK_sq, hroot_sq]
        ring
  rw [← mul_pow] at h_sum_le
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h_sum_le

/-- **Second-order Taylor bound for the packed two-layer network.** The network `netFromParams`
trains both the hidden weights and the readout weights, so its linearization at `θ₀` involves the
mixed hidden/readout derivative; the remainder is nevertheless controlled by the Jacobian Lipschitz
bound `outputJacobian_netFromParams_frobenius_sub_le`, which needs a bound `R` only on the readout
weights of the *base point* `θ₀`, not of `θ`. For every `θ`,
`‖f(θ) - f(θ₀) - J(θ₀) (θ - θ₀)‖ ≤ (K / (2 √n)) ‖θ - θ₀‖²`, where `f` and `J` are the training
outputs and the output Jacobian on the dataset `X`, and `K` is the constant of the Jacobian bound.
For a single test input use `m = 1`. -/
theorem norm_trainingOutputs_netFromParams_sub_linearization_le
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (n d m : ℕ) (hn : 0 < n) (X : Fin m → Fin d → ℝ)
    (θ₀ θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (C₁ C₂ R : ℝ) (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hR_nonneg : 0 ≤ R)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_bound : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (ha : ∀ i : Fin n, |unpackA θ₀ i| ≤ R) :
    ‖trainingOutputs (netFromParams φ n d) X θ - trainingOutputs (netFromParams φ n d) X θ₀ -
        (matrixCLM (outputJacobian (netFromParams φ n d) X θ₀) (θ - θ₀))‖ ≤
      (Real.sqrt (∑ α : Fin m, (2 * R ^ 2 * C₂ ^ 2 * (∑ j : Fin d, X α j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, X α j ^ 2))) / Real.sqrt (n : ℝ)) / 2 * ‖θ - θ₀‖ ^ 2 :=
  norm_trainingOutputs_sub_linearization_le (netFromParams φ n d) X θ₀ ‖θ - θ₀‖ _
    (fun z _ β => (hasFDerivAt_netFromParams φ n d (X β) z
      fun _ => hφ.differentiableAt).differentiableAt)
    (fun z _ => by
      rw [norm_sub_rev (outputJacobian _ X z), norm_sub_rev z θ₀]
      exact outputJacobian_netFromParams_frobenius_sub_le φ n d m hn X θ₀ z C₁ C₂ R hC₁_nonneg
        hC₂_nonneg hR_nonneg hφ_lip hderiv_bound hderiv_lip (fun _ _ => hφ.differentiableAt)
        (fun _ _ => hφ.differentiableAt) ha)
    le_rfl

/-- **Second-order Taylor bound at a single input.** The scalar form of
`norm_trainingOutputs_netFromParams_sub_linearization_le`, valid at any (training or test) input
`x`: `|f(x; θ) - f(x; θ₀) - ⟪∇f(x; θ₀), θ - θ₀⟫| ≤ (K_x / (2 √n)) ‖θ - θ₀‖²`, where
`K_x² = 2 R² C₂² ‖x‖⁴ + 3 C₁² ‖x‖²` and `R` bounds the readout weights of `θ₀`. -/
theorem abs_netFromParams_sub_linearization_le
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (n d : ℕ) (hn : 0 < n) (x : Fin d → ℝ)
    (θ₀ θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (C₁ C₂ R : ℝ) (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hR_nonneg : 0 ≤ R)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_bound : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (ha : ∀ i : Fin n, |unpackA θ₀ i| ≤ R) :
    |netFromParams φ n d x θ - netFromParams φ n d x θ₀ -
        ⟪gradParams φ n d x θ₀, θ - θ₀⟫| ≤
      (Real.sqrt (2 * R ^ 2 * C₂ ^ 2 * (∑ j : Fin d, x j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, x j ^ 2)) / Real.sqrt (n : ℝ)) / 2 * ‖θ - θ₀‖ ^ 2 := by
  have h := norm_trainingOutputs_netFromParams_sub_linearization_le φ hφ n d 1 hn (fun _ => x)
    θ₀ θ C₁ C₂ R hC₁_nonneg hC₂_nonneg hR_nonneg hφ_lip hderiv_bound hderiv_lip ha
  have hcoord : ∀ v : EuclideanSpace ℝ (Fin 1), ‖v‖ = |v 0| := fun v => by
    simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
  rw [hcoord] at h
  simp only [trainingOutputs, PiLp.sub_apply, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton] at h
  convert h using 2
  simp only [outputJacobian, Matrix.mulVec_apply, dotProduct, tangentFeature, PiLp.inner_apply]
  rw [gradient_netFromParams φ n d x θ₀ (fun _ => hφ _)]
  simp [mul_comm]

/-- **Lipschitz bound for the tangent feature at one input.** The packed gradient at an input `x`
is `(K_x / √n)`-Lipschitz relative to a base point `θ₀` whose readout weights are bounded by `R`,
`K_x² = 2 R² C₂² ‖x‖⁴ + 3 C₁² ‖x‖²`. This is `outputJacobian_netFromParams_frobenius_sub_le` for
the one-point dataset `{x}`, whose Jacobian is the row `∇f(x; θ)`. -/
theorem norm_gradParams_sub_le
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (n d : ℕ) (hn : 0 < n) (x : Fin d → ℝ)
    (θ₀ θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (C₁ C₂ R : ℝ) (hC₁_nonneg : 0 ≤ C₁) (hC₂_nonneg : 0 ≤ C₂) (hR_nonneg : 0 ≤ R)
    (hφ_lip : ∀ u v, |φ u - φ v| ≤ C₁ * |u - v|)
    (hderiv_bound : ∀ z, |deriv φ z| ≤ C₁)
    (hderiv_lip : ∀ u v, |deriv φ u - deriv φ v| ≤ C₂ * |u - v|)
    (ha : ∀ i : Fin n, |unpackA θ₀ i| ≤ R) :
    ‖gradParams φ n d x θ - gradParams φ n d x θ₀‖ ≤
      (Real.sqrt (2 * R ^ 2 * C₂ ^ 2 * (∑ j : Fin d, x j ^ 2) ^ 2 +
        3 * C₁ ^ 2 * (∑ j : Fin d, x j ^ 2)) / Real.sqrt (n : ℝ)) * ‖θ - θ₀‖ := by
  have h := outputJacobian_netFromParams_frobenius_sub_le φ n d 1 hn (fun _ => x) θ₀ θ C₁ C₂ R
    hC₁_nonneg hC₂_nonneg hR_nonneg hφ_lip hderiv_bound hderiv_lip (fun _ _ => hφ.differentiableAt)
    (fun _ _ => hφ.differentiableAt) ha
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  rw [norm_sub_rev θ₀ θ] at h
  have hEq : ‖outputJacobian (netFromParams φ n d) (fun _ : Fin 1 => x) θ₀ -
      outputJacobian (netFromParams φ n d) (fun _ : Fin 1 => x) θ‖ =
      ‖gradParams φ n d x θ - gradParams φ n d x θ₀‖ := by
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    rw [matrix_frobenius_norm_sq, EuclideanSpace.real_norm_sq_eq]
    simp only [outputJacobian, Matrix.sub_apply, Matrix.of_apply, Finset.univ_unique,
      Finset.sum_singleton, tangentFeature_netFromParams_of_differentiable φ hφ, PiLp.sub_apply]
    exact Finset.sum_congr rfl fun j _ => by ring
  exact hEq ▸ h

/-- The empirical NTK Gram matrix of `netFromParams` decomposes into the sum of the
input-weight Gram matrix and the readout Gram matrix (empirical covariance). -/
theorem empiricalNTKMatrix_netFromParams_apply (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⬝ᵥ X α))
    (α β : Fin m) :
    empiricalNTKMatrix (netFromParams φ n d) X θ α β =
      (∑ i : Fin n, gradW φ n d (X α) θ i ⬝ᵥ gradW φ n d (X β) θ i) +
      ∑ i : Fin n, gradA φ n d (X α) θ i * gradA φ n d (X β) θ i := by
  rw [empiricalNTKMatrix_apply]
  rw [tangentFeature_netFromParams φ n d (X α) θ (hφ α)]
  rw [tangentFeature_netFromParams φ n d (X β) θ (hφ β)]
  exact inner_packParams_packParams _ _ _ _

end

end NTK
