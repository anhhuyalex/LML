/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.InfiniteWidth

/-!
# Stability of linear ODEs under coefficient perturbation

Generic, network-independent estimate comparing `r' = -(1/m) K(t) r` with the frozen dynamics
`s' = -(1/m) K_∞ s`.

See
`LeanMachineLearning.Optimization.NTK.Training.GradientFlow`
for the overview of the whole development.
-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory Filter ConvexOpt
open scoped RealInnerProductSpace Matrix Matrix.Norms.Frobenius Topology

namespace NTK

variable {ι : Type*} {d m P : ℕ}

attribute [local instance]
  Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra

attribute [local instance 2000] instCompleteSpaceMatrix

/-! ### Stability of Linear ODEs under Coefficient Perturbation

Generic, network-independent stability estimate used to compare the actual residual dynamics
`r' = -(1 / m) K(t) r` with the frozen dynamics `s' = -(1 / m) K_∞ s`. -/

section LinearODECoefficientPerturbation

/-- One-point estimate behind coefficient-perturbation stability: if `A` is PSD then the error
`e = r - s` between solutions of `r' = -A r` and `s' = -B s` satisfies
`⟪e, e'⟫ ≤ ‖e‖ ‖A - B‖ ‖s‖`. -/
private lemma inner_sub_le_of_psd_coefficient (A B : Matrix (Fin m) (Fin m) ℝ)
    (r s : EuclideanSpace ℝ (Fin m))
    (hA : ∀ v : EuclideanSpace ℝ (Fin m), 0 ≤ v.ofLp ⬝ᵥ (A *ᵥ v.ofLp)) :
    ⟪r - s, (WithLp.toLp 2 (-(A *ᵥ r.ofLp)) : EuclideanSpace ℝ (Fin m)) -
        WithLp.toLp 2 (-(B *ᵥ s.ofLp))⟫ ≤ ‖r - s‖ * (‖A - B‖ * ‖s‖) := by
  have hvec : (WithLp.toLp 2 (-(A *ᵥ r.ofLp)) : EuclideanSpace ℝ (Fin m)) -
      WithLp.toLp 2 (-(B *ᵥ s.ofLp)) =
      -(WithLp.toLp 2 (A *ᵥ (r - s).ofLp) : EuclideanSpace ℝ (Fin m)) -
        WithLp.toLp 2 ((A - B) *ᵥ s.ofLp) := by
    ext i
    simp [Matrix.mulVec_sub, Matrix.sub_mulVec]
    ring
  rw [hvec, inner_sub_right, inner_neg_right, inner_toLp_mulVec_eq_dotProduct]
  have h1 := hA (r - s)
  have h2 : -⟪r - s, (WithLp.toLp 2 ((A - B) *ᵥ s.ofLp) : EuclideanSpace ℝ (Fin m))⟫ ≤
      ‖r - s‖ * (‖A - B‖ * ‖s‖) := by
    calc -⟪r - s, (WithLp.toLp 2 ((A - B) *ᵥ s.ofLp) : EuclideanSpace ℝ (Fin m))⟫
        ≤ |⟪r - s, (WithLp.toLp 2 ((A - B) *ᵥ s.ofLp) : EuclideanSpace ℝ (Fin m))⟫| := neg_le_abs _
      _ ≤ ‖r - s‖ * ‖(WithLp.toLp 2 ((A - B) *ᵥ s.ofLp) : EuclideanSpace ℝ (Fin m))‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ ‖r - s‖ * (‖A - B‖ * ‖s‖) :=
          mul_le_mul_of_nonneg_left (mulVec_frobenius_norm_le (A - B) s) (norm_nonneg _)
  linarith

/-- **Stability of linear ODEs under coefficient perturbation (PSD case).** Let `r' = -A(t) r` and
`s' = -B(t) s` on `[0, T]` with `A(t)` positive semidefinite, and suppose
`‖A(t) - B(t)‖ ‖s(t)‖ ≤ a` there. Then `‖r(t) - s(t)‖ ≤ ‖r(0) - s(0)‖ + a t` for `t ∈ [0, T]`.
The equation for `r` is only needed on `(0, T)`, with `r` continuous on `[0, T]`, so forward-time
trajectories qualify.
The PSD hypothesis on `A` removes any exponential Grönwall factor: the dissipative part
`-⟪e, A e⟫` of the error equation is nonpositive and only the forcing `(A - B) s` remains.
Independent of neural networks, initialization and width. -/
theorem norm_sub_le_of_linear_ode_perturbation
    (A B : ℝ → Matrix (Fin m) (Fin m) ℝ) (r s : ℝ → EuclideanSpace ℝ (Fin m)) {T a : ℝ}
    (hT : 0 ≤ T) (hrc : ContinuousOn r (Set.Icc 0 T))
    (hr : ∀ t ∈ Set.Ioo 0 T, HasDerivAt r (WithLp.toLp 2 (-(A t *ᵥ (r t).ofLp))) t)
    (hs : ∀ t ∈ Set.Icc 0 T, HasDerivAt s (WithLp.toLp 2 (-(B t *ᵥ (s t).ofLp))) t)
    (hA : ∀ t ∈ Set.Icc 0 T, ∀ v : EuclideanSpace ℝ (Fin m), 0 ≤ v.ofLp ⬝ᵥ (A t *ᵥ v.ofLp))
    (hab : ∀ t ∈ Set.Icc 0 T, ‖A t - B t‖ * ‖s t‖ ≤ a) :
    ∀ t ∈ Set.Icc 0 T, ‖r t - s t‖ ≤ ‖r 0 - s 0‖ + a * t := by
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT⟩
  have ha : 0 ≤ a := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans (hab 0 h0)
  have he : ∀ t ∈ Set.Ioo 0 T, HasDerivAt (fun τ => r τ - s τ)
      ((WithLp.toLp 2 (-(A t *ᵥ (r t).ofLp)) : EuclideanSpace ℝ (Fin m)) -
        WithLp.toLp 2 (-(B t *ᵥ (s t).ofLp))) t := fun t ht =>
    (hr t ht).sub (hs t (Set.Ioo_subset_Icc_self ht))
  have hsc : ContinuousOn s (Set.Icc 0 T) := fun t ht => (hs t ht).continuousAt.continuousWithinAt
  -- Regularized comparison: `√(‖e‖² + η²) - a t` is nonincreasing on `[0, T]`.
  have key : ∀ η > 0, ∀ t ∈ Set.Icc 0 T,
      Real.sqrt (‖r t - s t‖ ^ 2 + η ^ 2) ≤ Real.sqrt (‖r 0 - s 0‖ ^ 2 + η ^ 2) + a * t := by
    intro η hη t ht
    have hpos : ∀ τ, 0 < ‖r τ - s τ‖ ^ 2 + η ^ 2 := fun τ => by positivity
    have hu : ∀ τ ∈ Set.Ioo 0 T, HasDerivAt
        (fun σ => Real.sqrt (‖r σ - s σ‖ ^ 2 + η ^ 2) - a * σ)
        ((2 * ⟪r τ - s τ, (WithLp.toLp 2 (-(A τ *ᵥ (r τ).ofLp)) : EuclideanSpace ℝ (Fin m)) -
            WithLp.toLp 2 (-(B τ *ᵥ (s τ).ofLp))⟫) /
          (2 * Real.sqrt (‖r τ - s τ‖ ^ 2 + η ^ 2)) - a * 1) τ := by
      intro τ hτ
      have h1 := ((he τ hτ).norm_sq.add_const (η ^ 2)).sqrt
        (hpos τ).ne'
      exact h1.sub ((hasDerivAt_id τ).const_mul a)
    have hanti : AntitoneOn (fun σ => Real.sqrt (‖r σ - s σ‖ ^ 2 + η ^ 2) - a * σ)
        (Set.Icc 0 T) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
        ((((hrc.sub hsc).norm.pow 2).add continuousOn_const).sqrt.sub
          (continuousOn_const.mul continuousOn_id))
        (fun τ hτ => (hu τ (by rwa [interior_Icc] at hτ)).differentiableAt.differentiableWithinAt)
        (fun τ hτ => ?_)
      have hτ'' : τ ∈ Set.Ioo 0 T := by rwa [interior_Icc] at hτ
      have hτ' := Set.Ioo_subset_Icc_self hτ''
      rw [(hu τ hτ'').deriv]
      have hS : 0 < Real.sqrt (‖r τ - s τ‖ ^ 2 + η ^ 2) := Real.sqrt_pos.2 (hpos τ)
      have hle : ‖r τ - s τ‖ ≤ Real.sqrt (‖r τ - s τ‖ ^ 2 + η ^ 2) := by
        calc ‖r τ - s τ‖ = Real.sqrt (‖r τ - s τ‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg η])
      have hin := inner_sub_le_of_psd_coefficient (A τ) (B τ) (r τ) (s τ) (hA τ hτ')
      have hin' : ⟪r τ - s τ, (WithLp.toLp 2 (-(A τ *ᵥ (r τ).ofLp)) : EuclideanSpace ℝ (Fin m)) -
          WithLp.toLp 2 (-(B τ *ᵥ (s τ).ofLp))⟫ ≤
          Real.sqrt (‖r τ - s τ‖ ^ 2 + η ^ 2) * a := by
        refine hin.trans ?_
        calc ‖r τ - s τ‖ * (‖A τ - B τ‖ * ‖s τ‖) ≤ ‖r τ - s τ‖ * a :=
            mul_le_mul_of_nonneg_left (hab τ hτ') (norm_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_right hle ha
      rw [mul_one, sub_nonpos, mul_div_mul_left _ _ two_ne_zero, div_le_iff₀ hS]
      linarith [hin']
    have := hanti h0 ht ht.1
    simp only [mul_zero, sub_zero] at this
    linarith
  intro t ht
  refine le_of_forall_pos_le_add fun η hη => ?_
  have h1 : ‖r t - s t‖ ≤ Real.sqrt (‖r t - s t‖ ^ 2 + η ^ 2) := by
    calc ‖r t - s t‖ = Real.sqrt (‖r t - s t‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg η])
  have h2 : Real.sqrt (‖r 0 - s 0‖ ^ 2 + η ^ 2) ≤ ‖r 0 - s 0‖ + η := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [norm_nonneg (r 0 - s 0)]
  linarith [key η hη t ht]

/-- **Residual vs. frozen-kernel residual.** Specialization of
`norm_sub_le_of_linear_ode_perturbation` to `A t = (1 / m) K t` and `B t = (1 / m) K_inf`, i.e. to
the NTK residual dynamics: if the kernel `K t` is positive semidefinite along `[0, T]` and
`‖K t - K_inf‖ ‖s t‖ ≤ b`, then `‖r t - s t‖ ≤ ‖r 0 - s 0‖ + (1 / m) b t`. -/
theorem residual_sub_frozen_residual_le
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ) (K_inf : Matrix (Fin m) (Fin m) ℝ)
    (r s : ℝ → EuclideanSpace ℝ (Fin m)) {T b : ℝ} (hT : 0 ≤ T)
    (hrc : ContinuousOn r (Set.Icc 0 T))
    (hr : ∀ t ∈ Set.Ioo 0 T,
      HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t)
    (hs : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt s (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K_inf *ᵥ (s t).ofLp))) t)
    (hK : ∀ t ∈ Set.Icc 0 T, ∀ v : EuclideanSpace ℝ (Fin m), 0 ≤ v.ofLp ⬝ᵥ (K t *ᵥ v.ofLp))
    (hb : ∀ t ∈ Set.Icc 0 T, ‖K t - K_inf‖ * ‖s t‖ ≤ b) :
    ∀ t ∈ Set.Icc 0 T, ‖r t - s t‖ ≤ ‖r 0 - s 0‖ + (m : ℝ)⁻¹ * b * t := by
  have hcoeff : ∀ (M : Matrix (Fin m) (Fin m) ℝ) (v : EuclideanSpace ℝ (Fin m)),
      (-(m : ℝ)⁻¹ • (M *ᵥ v.ofLp) : Fin m → ℝ) = -(((m : ℝ)⁻¹ • M) *ᵥ v.ofLp) := by
    intro M v
    rw [Matrix.smul_mulVec, neg_smul]
  have h := norm_sub_le_of_linear_ode_perturbation (fun t => (m : ℝ)⁻¹ • K t)
    (fun _ => (m : ℝ)⁻¹ • K_inf) r s (a := (m : ℝ)⁻¹ * b) hT hrc
    (fun t ht => by simpa only [hcoeff] using hr t ht)
    (fun t ht => by simpa only [hcoeff] using hs t ht)
    (fun t ht v => by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.2 (Nat.cast_nonneg m)) (hK t ht v))
    (fun t ht => by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (Nat.cast_nonneg m)),
        mul_assoc]
      exact mul_le_mul_of_nonneg_left (hb t ht) (inv_nonneg.2 (Nat.cast_nonneg m)))
  exact h

/-- **Actual residual vs. the frozen matrix-exponential residual.** If `r' = -(1 / m) K(t) r` on
`[0, T]` with `K(t)` and `K_inf` positive semidefinite and `‖K(t) - K_inf‖ ≤ ε_K` there, then
`‖r(t) - exp(-(t / m) K_inf) r(0)‖ ≤ (1 / m) ε_K ‖r(0)‖ t`. The frozen residual starts at the same
initial condition and its norm never exceeds `‖r(0)‖` (positive semidefiniteness of `K_inf`), which
is what makes the coefficient error `‖K - K_inf‖ ‖s‖` controlled by `ε_K ‖r(0)‖`. -/
theorem residual_sub_matrix_exp_le
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ) (K_inf : Matrix (Fin m) (Fin m) ℝ)
    (r : ℝ → EuclideanSpace ℝ (Fin m)) {T ε_K : ℝ} (hT : 0 ≤ T) (hm : 0 < (m : ℝ))
    (hrc : ContinuousOn r (Set.Icc 0 T))
    (hr : ∀ t ∈ Set.Ioo 0 T,
      HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t)
    (hK : ∀ t ∈ Set.Icc 0 T, ∀ v : EuclideanSpace ℝ (Fin m), 0 ≤ v.ofLp ⬝ᵥ (K t *ᵥ v.ofLp))
    (hK_inf : ∀ v : EuclideanSpace ℝ (Fin m), 0 ≤ v.ofLp ⬝ᵥ (K_inf *ᵥ v.ofLp))
    (hb : ∀ t ∈ Set.Icc 0 T, ‖K t - K_inf‖ ≤ ε_K) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖r t - (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • K_inf)) *ᵥ (r 0).ofLp) :
        EuclideanSpace ℝ (Fin m))‖ ≤ (m : ℝ)⁻¹ * (ε_K * ‖r 0‖) * t := by
  have hε_K : 0 ≤ ε_K := (norm_nonneg _).trans (hb 0 ⟨le_rfl, hT⟩)
  have hs0 : (WithLp.toLp 2 ((NormedSpace.exp (-(0 / (m : ℝ)) • K_inf)) *ᵥ (r 0).ofLp) :
      EuclideanSpace ℝ (Fin m)) = r 0 := by simp
  have h := residual_sub_frozen_residual_le K K_inf r
    (fun t => (WithLp.toLp 2 ((NormedSpace.exp (-(t / (m : ℝ)) • K_inf)) *ᵥ (r 0).ofLp) :
      EuclideanSpace ℝ (Fin m))) (b := ε_K * ‖r 0‖) hT hrc hr
    (fun t _ => matrix_exp_residual_trajectory_hasDerivAt K_inf (r 0) t) hK
    (fun t ht => mul_le_mul (hb t ht) (by
      simpa using matrix_exp_residual_decay K_inf (r 0) 0
        (fun v => by simpa using hK_inf v) hm t ht.1) (norm_nonneg _) hε_K)
  intro t ht
  have := h t ht
  simpa [hs0] using this

/-- **Eigenmodes of the actual residual.** Under the hypotheses of `residual_sub_matrix_exp_le`,
each eigenmode of the training residual follows the frozen-kernel decay up to the lazy-training
error:
`|⟪v_k, r(t)⟫ - exp(-(t/m) λ_k) ⟪v_k, r(0)⟫| ≤ (1/m) ε_K ‖r(0)‖ t`, where `(λ_k, v_k)` are the
eigenpairs of the positive semidefinite limiting kernel `K_inf`. -/
theorem abs_inner_eigenvector_residual_sub_mode_le
    (K : ℝ → Matrix (Fin m) (Fin m) ℝ) {K_inf : Matrix (Fin m) (Fin m) ℝ}
    (hK_inf : K_inf.PosSemidef) (r : ℝ → EuclideanSpace ℝ (Fin m)) {T ε_K : ℝ} (hT : 0 ≤ T)
    (hm : 0 < (m : ℝ)) (hrc : ContinuousOn r (Set.Icc 0 T))
    (hr : ∀ t ∈ Set.Ioo 0 T,
      HasDerivAt r (WithLp.toLp 2 (-(m : ℝ)⁻¹ • (K t *ᵥ (r t).ofLp))) t)
    (hK : ∀ t ∈ Set.Icc 0 T, ∀ v : EuclideanSpace ℝ (Fin m), 0 ≤ v.ofLp ⬝ᵥ (K t *ᵥ v.ofLp))
    (hb : ∀ t ∈ Set.Icc 0 T, ‖K t - K_inf‖ ≤ ε_K) (k : Fin m) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      |⟪hK_inf.isHermitian.eigenvectorBasis k, r t⟫ -
          Real.exp (-(t / (m : ℝ)) * hK_inf.isHermitian.eigenvalues k) *
            ⟪hK_inf.isHermitian.eigenvectorBasis k, r 0⟫| ≤
        (m : ℝ)⁻¹ * (ε_K * ‖r 0‖) * t := by
  intro t ht
  have hmain := residual_sub_matrix_exp_le K K_inf r hT hm hrc hr hK
    (fun v => by simpa using hK_inf.dotProduct_mulVec_nonneg v.ofLp) hb t ht
  have hmode := inner_eigenvectorBasis_matrix_exp_mulVec hK_inf.isHermitian (-(t / (m : ℝ)))
    (r 0) k
  rw [← hmode, ← inner_sub_right]
  exact (abs_real_inner_le_norm _ _).trans (by
    rw [OrthonormalBasis.norm_eq_one, one_mul]; exact hmain)

end LinearODECoefficientPerturbation

end NTK

end
