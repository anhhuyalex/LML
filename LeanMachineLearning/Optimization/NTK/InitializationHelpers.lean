/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Initialization

/-!
# Peripheral initialization API

This module contains secondary consequences and convenience API for the NTK initialization
development.  The definitions, core proof infrastructure, main theorems, and their detailed
proof narratives are in `LeanMachineLearning.Optimization.NTK.Initialization`.
-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory Matrix Complex
open scoped BigOperators MatrixOrder RealInnerProductSpace Kronecker ENNReal

namespace NTK

variable {d n m : ℕ}

/-- The conditional expectation of the output vector vanishes. -/
lemma integral_conditional_output_eq_zero
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ) :
    ∫ v, v ∂(Measure.map (fun a => evalVector φ W a X) (gaussianReadoutMeasure n)) = 0 := by
  rw [exact_conditional_normality]
  exact integral_id_multivariateGaussian

/-- The conditional covariance between outputs `f(X α)` and `f(X β)` is `Φ^{(n), α β}`. -/
lemma cov_conditional_output_eq_covariance
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ) (α β : Fin m) :
    cov[fun (v : EuclideanSpace ℝ (Fin m)) => v.ofLp α, fun v => v.ofLp β;
      Measure.map (fun a => evalVector φ W a X) (gaussianReadoutMeasure n)] =
      empiricalCovariance n φ W X α β := by
  rw [exact_conditional_normality]
  have hPos : (empiricalCovariance n φ W X).PosSemidef :=
    empiricalCovariance_posSemidef n φ W X
  have (i : Fin m) : (fun (v : EuclideanSpace ℝ (Fin m)) => v.ofLp i) = (fun v => v i) := rfl
  rw [this, this]
  exact covariance_eval_multivariateGaussian hPos α β



/-! ### Independence Across Depth -/

/-- **Independence Across Depth**: if the per-layer weight matrices `W_0, …, W_{L-1}` are mutually
independent and identically initialized (`Measure.pi (fun _ : Fin L => gaussianInit n d)`), then
for every layer `ℓ`, the weight matrix `W_ℓ` is independent of the history
`(W_i)_{i < ℓ}` — the finite-width analogue of "`W_ℓ` is independent of `F_ℓ`". -/
theorem indepFun_layer_history (L n d : ℕ) (ℓ : Fin L) :
    IndepFun (fun ω : Fin L → Fin n → Fin d → ℝ => ω ℓ)
      (fun ω : Fin L → Fin n → Fin d → ℝ => fun i : Finset.Iio ℓ => ω i)
      (Measure.pi (fun _ : Fin L => gaussianInit n d)) := by
  have h_indep : iIndepFun (fun ℓ : Fin L => fun ω : Fin L → Fin n → Fin d → ℝ => ω ℓ)
      (Measure.pi (fun _ : Fin L => gaussianInit n d)) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have h_meas : ∀ i : Fin L, Measurable (fun ω : Fin L → Fin n → Fin d → ℝ => ω i) :=
    fun i => measurable_pi_apply i
  have h_disj : Disjoint ({ℓ} : Finset (Fin L)) (Finset.Iio ℓ) :=
    Finset.disjoint_singleton_left.2 (by simp)
  have h := h_indep.indepFun_finset {ℓ} (Finset.Iio ℓ) h_disj h_meas
  exact h.comp (measurable_pi_apply (⟨ℓ, Finset.mem_singleton_self ℓ⟩ :
    ({ℓ} : Finset (Fin L)))) measurable_id



/-! ### Arc-Cosine Kernel Representation (Cho & Saul) -/

/-- **Connection to Arc-Cosine Kernel Geometry (Cho & Saul)**:
with `θ := arccos ρ ∈ [0, π]`, Proposition 2.5's derivative kernel is exactly half of the
0-th order arc-cosine kernel `J₀(θ) = (1/π) * (π - θ)`. -/
theorem expected_reluDeriv_mul_reluDeriv_bivariate_eq_arcCosineJ0
    (Φαα Φββ Φαβ : ℝ) (hΦαα : 0 < Φαα) (hΦββ : 0 < Φββ)
    (hSigma : (show Matrix (Fin 2) (Fin 2) ℝ from !![Φαα, Φαβ; Φαβ, Φββ]).PosSemidef) :
    let ρ := Φαβ / Real.sqrt (Φαα * Φββ)
    ∫ z : EuclideanSpace ℝ (Fin 2), reluDeriv (z.ofLp 0) * reluDeriv (z.ofLp 1)
      ∂(multivariateGaussian 0 !![Φαα, Φαβ; Φαβ, Φββ]) =
      (1 / 2) * ((1 / Real.pi) * (Real.pi - Real.arccos ρ)) := by
  intro ρ
  rw [expected_reluDeriv_mul_reluDeriv_bivariate Φαα Φββ Φαβ hΦαα hΦββ hSigma,
    ← div_two_pi_pi_sub_arccos_eq_arcsin ρ]
  ring

/-- **Connection to Arc-Cosine Kernel Geometry (Cho & Saul)**:
with `θ := arccos ρ ∈ [0, π]`, Proposition 2.5's activation kernel is exactly
`(√(Φαα * Φββ) / 2) * J₁(θ)` for the 1-st order arc-cosine kernel
`J₁(θ) = (1/π) * (sin θ + (π - θ) * cos θ)`. -/
theorem expected_relu_mul_relu_bivariate_eq_arcCosineJ1
    (Φαα Φββ Φαβ : ℝ) (hΦαα : 0 < Φαα) (hΦββ : 0 < Φββ)
    (hSigma : (show Matrix (Fin 2) (Fin 2) ℝ from !![Φαα, Φαβ; Φαβ, Φββ]).PosSemidef) :
    let ρ := Φαβ / Real.sqrt (Φαα * Φββ)
    ∫ z : EuclideanSpace ℝ (Fin 2), relu (z.ofLp 0) * relu (z.ofLp 1)
      ∂(multivariateGaussian 0 !![Φαα, Φαβ; Φαβ, Φββ]) =
      (Real.sqrt (Φαα * Φββ) / 2) * ((1 / Real.pi) * (Real.sin (Real.arccos ρ) +
        (Real.pi - Real.arccos ρ) * Real.cos (Real.arccos ρ))) := by
  intro ρ
  have hρ : ρ ∈ Set.Icc (-1) 1 := pearsonRho_mem_Icc Φαα Φββ Φαβ hΦαα hΦββ hSigma
  rw [expected_relu_mul_relu_bivariate Φαα Φββ Φαβ hΦαα hΦββ hSigma,
    Real.cos_arccos hρ.1 hρ.2, Real.sin_arccos]
  have hangle : Real.pi - Real.arccos ρ = Real.pi / 2 + Real.arcsin ρ := by
    rw [Real.arccos_eq_pi_div_two_sub_arcsin]; ring
  rw [hangle]
  ring



/-- The conditional expectation of the depth-`L` network's output vector vanishes. -/
lemma integral_conditional_deepOutput_eq_zero
    (d m n L : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) (w : Fin L → ℕ → ℕ → ℝ) :
    ∫ v, v ∂(Measure.map
      (fun r : (ℕ → ℝ) × ℝ => WithLp.toLp 2 fun α : Fin m => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n,
        r.1 j.val * φ (deepPreactivation d m n φ X
          (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j))
      ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1))) = 0 := by
  rw [map_deepEval_snd_eq_multivariateGaussian d m n L φ X w]
  exact integral_id_multivariateGaussian

/-- The conditional covariance between depth-`L` network outputs at `X α` and `X β` is
`Φ_L^{(n), α β}`. -/
lemma cov_conditional_deepOutput_eq_covariance
    (d m n L : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) (w : Fin L → ℕ → ℕ → ℝ)
    (α β : Fin m) :
    cov[fun (v : EuclideanSpace ℝ (Fin m)) => v.ofLp α, fun v => v.ofLp β;
      Measure.map
        (fun r : (ℕ → ℝ) × ℝ => WithLp.toLp 2 fun α : Fin m => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n,
          r.1 j.val * φ (deepPreactivation d m n φ X
            (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j))
        ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1))] =
      (n : ℝ)⁻¹ * ∑ j : Fin n,
        φ (deepPreactivation d m n φ X
          (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
        φ (deepPreactivation d m n φ X
          (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j) := by
  rw [map_deepEval_snd_eq_multivariateGaussian d m n L φ X w]
  have hPos : (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
      φ (deepPreactivation d m n φ X
        (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
      φ (deepPreactivation d m n φ X
        (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j)).PosSemidef :=
    deepEval_covariance_posSemidef d m n L φ X w
  have (i : Fin m) : (fun (v : EuclideanSpace ℝ (Fin m)) => v.ofLp i) = (fun v => v i) := rfl
  rw [this, this]
  exact covariance_eval_multivariateGaussian hPos α β


end NTK

end

