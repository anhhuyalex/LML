/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.TwoLayer.JacobianBounds

/-!
# Two-layer network: neuron-sum formula for the empirical NTK

The empirical NTK matrix of the packed network as an explicit sum over neurons, its evaluation on
the scaled dataset `X / √d`, and the bridge between sequence prefixes and `𝒩(0,1)^{n×d} ⊗ 𝒩(0,
I_n)`.

## Main results and proof outline

- `empiricalNTKMatrix_netFromParams_eq_neuron_sum`:
  Explicit empirical-NTK neuron-sum formula.
- `netFromParams_scaled_input`, `netFromParams_scaled_input_div`:
  Evaluation on scaled inputs `x / √d`.
- `gradW_scaled_input`, `gradA_scaled_input`:
  Gradients on scaled inputs factoring out `1 / √d` and `1 / √n`.
- `empiricalNTKMatrix_netFromParams_scaled_dataset_eq_neuron_sum`:
  Full empirical NTK on the scaled dataset `X / √d`.

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

/-! ### Full Neuron-Sum Formula for the Empirical NTK

Derives the explicit single-sum representation of the full empirical NTK Gram matrix
from the two-block decomposition `empiricalNTKMatrix_netFromParams_apply`. Each Gram entry
is expressed directly as an empirical average over the `n` hidden neurons with both
activation and derivative-weight contributions.
-/

section FullTwoLayerNTKFormula

private lemma gradA_mul_gradA (φ : ℝ → ℝ) (n d : ℕ) (x x' : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) (i : Fin n) :
    gradA φ n d x θ i * gradA φ n d x' θ i =
      (n : ℝ)⁻¹ * (φ (unpackW θ i ⬝ᵥ x) * φ (unpackW θ i ⬝ᵥ x')) := by
  dsimp [gradA]
  have h_sqrt : (n : ℝ)⁻¹.sqrt * (n : ℝ)⁻¹.sqrt = (n : ℝ)⁻¹ :=
    Real.mul_self_sqrt (by positivity)
  calc
    ((n : ℝ)⁻¹.sqrt * φ (unpackW θ i ⬝ᵥ x)) * ((n : ℝ)⁻¹.sqrt * φ (unpackW θ i ⬝ᵥ x')) =
      ((n : ℝ)⁻¹.sqrt * (n : ℝ)⁻¹.sqrt) *
        (φ (unpackW θ i ⬝ᵥ x) * φ (unpackW θ i ⬝ᵥ x')) := by ring
    _ = (n : ℝ)⁻¹ * (φ (unpackW θ i ⬝ᵥ x) * φ (unpackW θ i ⬝ᵥ x')) := by rw [h_sqrt]

private lemma gradW_dotProduct_gradW (φ : ℝ → ℝ) (n d : ℕ) (x x' : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) (i : Fin n) :
    gradW φ n d x θ i ⬝ᵥ gradW φ n d x' θ i =
      (n : ℝ)⁻¹ * (unpackA θ i ^ 2 * deriv φ (unpackW θ i ⬝ᵥ x) *
        deriv φ (unpackW θ i ⬝ᵥ x') * (x ⬝ᵥ x')) := by
  have hW1 : gradW φ n d x θ i =
      fun j => ((n : ℝ)⁻¹.sqrt * unpackA θ i * deriv φ (unpackW θ i ⬝ᵥ x)) * x j := by
    ext j; rfl
  have hW2 : gradW φ n d x' θ i =
      fun j => ((n : ℝ)⁻¹.sqrt * unpackA θ i * deriv φ (unpackW θ i ⬝ᵥ x')) * x' j := by
    ext j; rfl
  rw [hW1, hW2, dotProduct_mul_mul]
  have h_sqrt : (n : ℝ)⁻¹.sqrt * (n : ℝ)⁻¹.sqrt = (n : ℝ)⁻¹ :=
    Real.mul_self_sqrt (by positivity)
  have h_alg : (((n : ℝ)⁻¹.sqrt * unpackA θ i * deriv φ (unpackW θ i ⬝ᵥ x)) *
      ((n : ℝ)⁻¹.sqrt * unpackA θ i * deriv φ (unpackW θ i ⬝ᵥ x'))) * (x ⬝ᵥ x') =
      (n : ℝ)⁻¹ * (unpackA θ i ^ 2 * deriv φ (unpackW θ i ⬝ᵥ x) *
        deriv φ (unpackW θ i ⬝ᵥ x') * (x ⬝ᵥ x')) := by
    calc
      (((n : ℝ)⁻¹.sqrt * unpackA θ i * deriv φ (unpackW θ i ⬝ᵥ x)) *
        ((n : ℝ)⁻¹.sqrt * unpackA θ i * deriv φ (unpackW θ i ⬝ᵥ x'))) * (x ⬝ᵥ x') =
        ((n : ℝ)⁻¹.sqrt * (n : ℝ)⁻¹.sqrt) *
          (unpackA θ i ^ 2 * deriv φ (unpackW θ i ⬝ᵥ x) *
            deriv φ (unpackW θ i ⬝ᵥ x') * (x ⬝ᵥ x')) := by ring
      _ = (n : ℝ)⁻¹ * (unpackA θ i ^ 2 * deriv φ (unpackW θ i ⬝ᵥ x) *
            deriv φ (unpackW θ i ⬝ᵥ x') * (x ⬝ᵥ x')) := by rw [h_sqrt]
  exact h_alg

private lemma gradW_dotProduct_add_gradA_mul (φ : ℝ → ℝ) (n d : ℕ) (x x' : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) (i : Fin n) :
    gradW φ n d x θ i ⬝ᵥ gradW φ n d x' θ i + gradA φ n d x θ i * gradA φ n d x' θ i =
      (n : ℝ)⁻¹ *
        (φ (unpackW θ i ⬝ᵥ x) * φ (unpackW θ i ⬝ᵥ x') +
         unpackA θ i ^ 2 * deriv φ (unpackW θ i ⬝ᵥ x) *
           deriv φ (unpackW θ i ⬝ᵥ x') * (x ⬝ᵥ x')) := by
  rw [gradW_dotProduct_gradW, gradA_mul_gradA]
  ring

/-- The full empirical NTK matrix of `netFromParams` evaluated at sample pair `(α, β)`
expressed explicitly as an empirical average over the `n` hidden neurons. -/
theorem empiricalNTKMatrix_netFromParams_eq_neuron_sum (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ α : Fin m, ∀ i : Fin n, DifferentiableAt ℝ φ (unpackW θ i ⬝ᵥ X α))
    (α β : Fin m) :
    empiricalNTKMatrix (netFromParams φ n d) X θ α β =
      (n : ℝ)⁻¹ * ∑ i : Fin n,
        (φ (unpackW θ i ⬝ᵥ X α) * φ (unpackW θ i ⬝ᵥ X β) +
         unpackA θ i ^ 2 *
           deriv φ (unpackW θ i ⬝ᵥ X α) *
           deriv φ (unpackW θ i ⬝ᵥ X β) *
           (X α ⬝ᵥ X β)) := by
  rw [empiricalNTKMatrix_netFromParams_apply φ n d m X θ hφ α β]
  rw [← Finset.sum_add_distrib]
  simp_rw [gradW_dotProduct_add_gradA_mul]
  rw [← Finset.mul_sum]

/-! ### Scaled-Dataset Network Evaluation and Gradients -/

lemma netFromParams_scaled_input (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) θ =
      (n : ℝ)⁻¹.sqrt * ∑ i : Fin n,
        unpackA θ i * φ ((Real.sqrt (d : ℝ))⁻¹ * (unpackW θ i ⬝ᵥ x)) := by
  rw [netFromParams_eq_normalized_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [dotProduct_scaled_input]

lemma netFromParams_scaled_input_div (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) :
    netFromParams φ n d (fun j => (Real.sqrt (d : ℝ))⁻¹ * x j) θ =
      (n : ℝ)⁻¹.sqrt * ∑ i : Fin n,
        unpackA θ i * φ ((unpackW θ i ⬝ᵥ x) / Real.sqrt (d : ℝ)) := by
  rw [netFromParams_eq_normalized_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [dotProduct_scaled_input_div]

lemma gradW_scaled_input (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) (i : Fin n) (j : Fin d) :
    gradW φ n d (fun k => (Real.sqrt (d : ℝ))⁻¹ * x k) θ i j =
      ((n : ℝ)⁻¹.sqrt * (Real.sqrt (d : ℝ))⁻¹) *
        (unpackA θ i * deriv φ ((Real.sqrt (d : ℝ))⁻¹ * (unpackW θ i ⬝ᵥ x)) * x j) := by
  dsimp [gradW]
  rw [dotProduct_scaled_input]
  ring

lemma gradA_scaled_input (φ : ℝ → ℝ) (n d : ℕ) (x : Fin d → ℝ)
    (θ : EuclideanSpace ℝ (Fin (n * d + n))) (i : Fin n) :
    gradA φ n d (fun k => (Real.sqrt (d : ℝ))⁻¹ * x k) θ i =
      (n : ℝ)⁻¹.sqrt * φ ((Real.sqrt (d : ℝ))⁻¹ * (unpackW θ i ⬝ᵥ x)) := by
  dsimp [gradA]
  rw [dotProduct_scaled_input]

/-! ### Scaled-Dataset Corollaries -/

/-- The full empirical NTK matrix of `netFromParams` evaluated on the paper's scaled
dataset `(1 / √d) * X`, yielding the canonical two-layer NTK neuron-sum formula with
both activation covariance and `(1 / d) * (X α ⬝ᵥ X β)` derivative covariance. -/
theorem empiricalNTKMatrix_netFromParams_scaled_dataset_eq_neuron_sum
    (φ : ℝ → ℝ) (n d m : ℕ) (hd : 0 < d)
    (X : Fin m → Fin d → ℝ) (θ : EuclideanSpace ℝ (Fin (n * d + n)))
    (hφ : ∀ α : Fin m, ∀ i : Fin n,
      DifferentiableAt ℝ φ (unpackW θ i ⬝ᵥ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j)))
    (α β : Fin m) :
    empiricalNTKMatrix (netFromParams φ n d) (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j) θ α β =
      (n : ℝ)⁻¹ * ∑ i : Fin n,
        (φ ((Real.sqrt (d : ℝ))⁻¹ * (unpackW θ i ⬝ᵥ X α)) *
           φ ((Real.sqrt (d : ℝ))⁻¹ * (unpackW θ i ⬝ᵥ X β)) +
         unpackA θ i ^ 2 *
           deriv φ ((Real.sqrt (d : ℝ))⁻¹ * (unpackW θ i ⬝ᵥ X α)) *
           deriv φ ((Real.sqrt (d : ℝ))⁻¹ * (unpackW θ i ⬝ᵥ X β)) *
           ((d : ℝ)⁻¹ * (X α ⬝ᵥ X β))) := by
  rw [empiricalNTKMatrix_netFromParams_eq_neuron_sum φ n d m _ θ hφ α β]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [dotProduct_scaled_input d (unpackW θ i) (X α)]
  rw [dotProduct_scaled_input d (unpackW θ i) (X β)]
  rw [dotProduct_scaled_dataset d hd (X α) (X β)]

/-! ### Sequence-Prefix Bridge -/

/-- The empirical NTK at the parameters obtained by packing the first `n` neurons of an
infinite sequence is the corresponding `n`-neuron empirical average. The packed parameter
expression is written explicitly to avoid introducing a thin sequence-parameter wrapper. -/
lemma empiricalNTKMatrix_netFromParams_of_seq (φ : ℝ → ℝ) (n d m : ℕ)
    (X : Fin m → Fin d → ℝ) (seq : ℕ → (Fin d → ℝ) × ℝ)
    (hφ : ∀ α : Fin m, ∀ i : Fin n,
      DifferentiableAt ℝ φ ((seq i.val).1 ⬝ᵥ X α))
    (α β : Fin m) :
    empiricalNTKMatrix (netFromParams φ n d) X
      (packParams (fun i : Fin n => (seq i.val).1) (fun i : Fin n => (seq i.val).2)) α β =
      (n : ℝ)⁻¹ * ∑ i : Fin n,
        (φ ((seq i.val).1 ⬝ᵥ X α) * φ ((seq i.val).1 ⬝ᵥ X β) +
          (seq i.val).2 ^ 2 *
            deriv φ ((seq i.val).1 ⬝ᵥ X α) * deriv φ ((seq i.val).1 ⬝ᵥ X β) *
              (X α ⬝ᵥ X β)) := by
  have h := empiricalNTKMatrix_netFromParams_eq_neuron_sum φ n d m X
    (packParams (fun i : Fin n => (seq i.val).1) (fun i : Fin n => (seq i.val).2))
    (by intro α i; simp only [unpackW_packParams]; exact hφ α i) α β
  simpa only [unpackW_packParams, unpackA_packParams] using h

/-- Scaled-dataset version of `empiricalNTKMatrix_netFromParams_of_seq`, with the input
Gram factor written as `(X α ⬝ᵥ X β) / d`. -/
lemma empiricalNTKMatrix_netFromParams_scaled_dataset_of_seq
    (φ : ℝ → ℝ) (n d m : ℕ) (hd : 0 < d)
    (X : Fin m → Fin d → ℝ) (seq : ℕ → (Fin d → ℝ) × ℝ)
    (hφ : ∀ α : Fin m, ∀ i : Fin n,
      DifferentiableAt ℝ φ
        ((seq i.val).1 ⬝ᵥ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j)))
    (α β : Fin m) :
    empiricalNTKMatrix (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
      (packParams (fun i : Fin n => (seq i.val).1) (fun i : Fin n => (seq i.val).2)) α β =
      (n : ℝ)⁻¹ * ∑ i : Fin n,
        (φ ((Real.sqrt (d : ℝ))⁻¹ * ((seq i.val).1 ⬝ᵥ X α)) *
           φ ((Real.sqrt (d : ℝ))⁻¹ * ((seq i.val).1 ⬝ᵥ X β)) +
         (seq i.val).2 ^ 2 *
           deriv φ ((Real.sqrt (d : ℝ))⁻¹ * ((seq i.val).1 ⬝ᵥ X α)) *
           deriv φ ((Real.sqrt (d : ℝ))⁻¹ * ((seq i.val).1 ⬝ᵥ X β)) *
           ((d : ℝ)⁻¹ * (X α ⬝ᵥ X β))) := by
  have h := empiricalNTKMatrix_netFromParams_scaled_dataset_eq_neuron_sum φ n d m hd X
    (packParams (fun i : Fin n => (seq i.val).1) (fun i : Fin n => (seq i.val).2))
    (by intro α i; simp only [unpackW_packParams]; exact hφ α i) α β
  simpa only [unpackW_packParams, unpackA_packParams] using h

/-- Matrix equation identifying the canonical empirical NTK on the scaled dataset at the
explicitly packed sequence-prefix parameters with the explicit neuron-average matrix. -/
lemma empiricalNTKMatrix_netFromParams_scaled_dataset_of_seq_matrix
    {m d : ℕ} (hd : 0 < d)
    (φ : ℝ → ℝ) (hφ_diff : Differentiable ℝ φ)
    (X : Fin m → Fin d → ℝ) (seq : ℕ → (Fin d → ℝ) × ℝ) (n : ℕ) :
    empiricalNTKMatrix (netFromParams φ n d)
      (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
      (packParams (fun i : Fin n => (seq i.val).1) (fun i : Fin n => (seq i.val).2)) =
    ((fun α β => (n : ℝ)⁻¹ * ∑ i : Fin n,
        (φ ((seq i.val).1 ⬝ᵥ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j)) *
           φ ((seq i.val).1 ⬝ᵥ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X β j)) +
         (seq i.val).2 ^ 2 *
           deriv φ ((seq i.val).1 ⬝ᵥ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j)) *
           deriv φ ((seq i.val).1 ⬝ᵥ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X β j)) *
           ((d : ℝ)⁻¹ * (X α ⬝ᵥ X β)))) : Matrix (Fin m) (Fin m) ℝ) := by
  ext α β
  have h_entry := empiricalNTKMatrix_netFromParams_scaled_dataset_of_seq φ n d m hd X seq
    (fun α i => hφ_diff.differentiableAt) α β
  rw [h_entry]
  simp_rw [dotProduct_mul_right]

/-- Almost-sure convergence of the canonical empirical NTK matrix at the explicitly packed
sequence-prefix initialization parameters to `limitingFullNTKMatrix`. -/
theorem empiricalNTKMatrix_netFromParams_scaled_dataset_tendsto_limitingFullNTKMatrix
    {m d : ℕ} (hd : 0 < d)
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (hdφ_meas : Measurable (deriv φ))
    (hφ_diff : Differentiable ℝ φ)
    (X : Fin m → Fin d → ℝ)
    (hφ_int : ∀ α β : Fin m,
      Integrable (fun w => φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β
            k))) (Measure.pi fun _ : Fin d => gaussianReal 0 1))
    (hdφ_int : ∀ α β : Fin m,
      Integrable (fun w => deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β
            k))) (Measure.pi fun _ : Fin d => gaussianReal 0 1)) :
    ∀ᵐ seq : ℕ → (Fin d → ℝ) × ℝ ∂(Measure.infinitePi fun _ => ((Measure.pi fun _ : Fin d =>
        gaussianReal 0 1).prod (gaussianReal 0 1))),
      Filter.Tendsto
        (fun n : ℕ =>
          empiricalNTKMatrix (netFromParams φ n d)
            (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
            (packParams (fun i : Fin n => (seq i.val).1) (fun i : Fin n => (seq i.val).2)))
        Filter.atTop
        (nhds (limitingFullNTKMatrix φ X)) := by
  have h_slln := fullNTKMatrix_scaled_dataset_tendsto_limitingFullNTKMatrix hd φ
    hφ_meas hdφ_meas X hφ_int hdφ_int
  filter_upwards [h_slln] with seq hseq
  have heq (n : ℕ) :
      empiricalNTKMatrix (netFromParams φ n d)
        (fun α j => (Real.sqrt (d : ℝ))⁻¹ * X α j)
        (packParams (fun i : Fin n => (seq i.val).1) (fun i : Fin n => (seq i.val).2)) =
      ((fun α β => (n : ℝ)⁻¹ * ∑ i : Fin n,
          (φ ((seq i.val).1 ⬝ᵥ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j)) *
             φ ((seq i.val).1 ⬝ᵥ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X β j)) +
           (seq i.val).2 ^ 2 *
             deriv φ ((seq i.val).1 ⬝ᵥ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X α j)) *
             deriv φ ((seq i.val).1 ⬝ᵥ (fun j => (Real.sqrt (d : ℝ))⁻¹ * X β j)) *
             ((d : ℝ)⁻¹ * (X α ⬝ᵥ X β)))) : Matrix (Fin m) (Fin m) ℝ) :=
    empiricalNTKMatrix_netFromParams_scaled_dataset_of_seq_matrix hd φ hφ_diff X seq n
  simp_rw [heq]
  exact hseq

end FullTwoLayerNTKFormula

end

end NTK
