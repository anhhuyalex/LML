/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Training.GradientFlow.LinearDynamics

/-!
# Gradient flow: Lipschitz propagation and Rayleigh-quotient stability

Deterministic Lipschitz propagation for the empirical NTK (Gap 2), the second-order Taylor bound
for the training outputs, and quadratic-form and Rayleigh-quotient perturbation.

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

/-! ### Deterministic Lipschitz Propagation for Empirical NTK (Gap 2)

Under parameter displacement `‖θ - θ₀‖`, the variation in the empirical NTK Gram matrix
`K(θ) = J(θ) J(θ)ᵀ` is controlled by the Jacobian operator/Frobenius norm bound `M`
and the Jacobian Lipschitz constant `L_J`:
  `‖K(θ₁) - K(θ₂)‖_F ≤ (2 * M * L_J) * ‖θ₁ - θ₂‖`.
Combined with lazy training displacement `‖θ(t) - θ₀‖ ≤ C / √n`, this establishes the
kernel freeze bound with explicit constant `L_K = 2 * M * L_J`.
-/

/-- Algebraic decomposition of the difference of two Gram matrices:
`A Aᵀ - B Bᵀ = (A - B) Aᵀ + B (A - B)ᵀ`. -/
lemma matrix_mul_transpose_sub_mul_transpose
    (A B : Matrix (Fin m) (Fin P) ℝ) :
    A * Aᵀ - B * Bᵀ = (A - B) * Aᵀ + B * (A - B)ᵀ := by
  rw [Matrix.sub_mul, Matrix.transpose_sub, Matrix.mul_sub, sub_add_sub_cancel]

/-- Frobenius norm bound on the difference of two Gram matrices given an upper bound `M`
on their factors: `‖A Aᵀ - B Bᵀ‖_F ≤ 2 * M * ‖A - B‖_F`. -/
lemma norm_mul_transpose_sub_mul_transpose_le
    (A B : Matrix (Fin m) (Fin P) ℝ) (M : ℝ)
    (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M) :
    ‖A * Aᵀ - B * Bᵀ‖ ≤ 2 * M * ‖A - B‖ := by
  rw [matrix_mul_transpose_sub_mul_transpose]
  have h_add := norm_add_le ((A - B) * Aᵀ) (B * (A - B)ᵀ)
  have h_mul1 := Matrix.frobenius_norm_mul (A - B) Aᵀ
  have h_mul2 := Matrix.frobenius_norm_mul B (A - B)ᵀ
  rw [Matrix.frobenius_norm_transpose A] at h_mul1
  rw [Matrix.frobenius_norm_transpose (A - B)] at h_mul2
  have h_term1 : ‖A - B‖ * ‖A‖ ≤ ‖A - B‖ * M :=
    mul_le_mul_of_nonneg_left hA (norm_nonneg _)
  have h_term2 : ‖B‖ * ‖A - B‖ ≤ M * ‖A - B‖ :=
    mul_le_mul_of_nonneg_right hB (norm_nonneg _)
  have h_comb : ‖A - B‖ * ‖A‖ + ‖B‖ * ‖A - B‖ ≤ 2 * M * ‖A - B‖ := by
    linarith
  linarith

/-- Pointwise algebraic identity for the difference of two empirical NTK Gram matrices. -/
lemma empiricalNTKMatrix_sub_empiricalNTKMatrix
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ₁ θ₂ : EuclideanSpace ℝ (Fin P)) :
    empiricalNTKMatrix f X θ₁ - empiricalNTKMatrix f X θ₂ =
      (outputJacobian f X θ₁ - outputJacobian f X θ₂) * (outputJacobian f X θ₁)ᵀ +
      outputJacobian f X θ₂ * (outputJacobian f X θ₁ - outputJacobian f X θ₂)ᵀ := by
  change outputJacobian f X θ₁ * (outputJacobian f X θ₁)ᵀ -
    outputJacobian f X θ₂ * (outputJacobian f X θ₂)ᵀ = _
  exact matrix_mul_transpose_sub_mul_transpose _ _

/-- The distance between two empirical NTK Gram matrices is bounded by `2 * M` times the
distance between their output Jacobians. -/
theorem empiricalNTKMatrix_sub_le_of_jacobian_bound
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ₁ θ₂ : EuclideanSpace ℝ (Fin P)) (M : ℝ)
    (hJ₁ : ‖outputJacobian f X θ₁‖ ≤ M) (hJ₂ : ‖outputJacobian f X θ₂‖ ≤ M) :
    ‖empiricalNTKMatrix f X θ₁ - empiricalNTKMatrix f X θ₂‖ ≤
      2 * M * ‖outputJacobian f X θ₁ - outputJacobian f X θ₂‖ := by
  change ‖outputJacobian f X θ₁ * (outputJacobian f X θ₁)ᵀ -
    outputJacobian f X θ₂ * (outputJacobian f X θ₂)ᵀ‖ ≤ _
  exact norm_mul_transpose_sub_mul_transpose_le _ _ M hJ₁ hJ₂

/-- Lipschitz propagation from output Jacobian to empirical NTK Gram matrix:
if the output Jacobian is bounded by `M` and has local Lipschitz constant `L_J`, then
the empirical NTK Gram matrix has local Lipschitz constant `2 * M * L_J`. -/
theorem empiricalNTKMatrix_sub_le_of_jacobian_lipschitz
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ₁ θ₂ : EuclideanSpace ℝ (Fin P)) (M L_J : ℝ)
    (hJ₁ : ‖outputJacobian f X θ₁‖ ≤ M) (hJ₂ : ‖outputJacobian f X θ₂‖ ≤ M)
    (hJ_lip : ‖outputJacobian f X θ₁ - outputJacobian f X θ₂‖ ≤ L_J * ‖θ₁ - θ₂‖) :
    ‖empiricalNTKMatrix f X θ₁ - empiricalNTKMatrix f X θ₂‖ ≤ (2 * M * L_J) * ‖θ₁ - θ₂‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hJ₁
  have h1 := empiricalNTKMatrix_sub_le_of_jacobian_bound f X θ₁ θ₂ M hJ₁ hJ₂
  have h2 : 2 * M * ‖outputJacobian f X θ₁ - outputJacobian f X θ₂‖ ≤
      2 * M * (L_J * ‖θ₁ - θ₂‖) := by
    have h2M : 0 ≤ 2 * M := by linarith
    exact mul_le_mul_of_nonneg_left hJ_lip h2M
  have h3 : 2 * M * (L_J * ‖θ₁ - θ₂‖) = (2 * M * L_J) * ‖θ₁ - θ₂‖ := by ring
  rw [h3] at h2
  exact h1.trans h2

/-- Deterministic Lipschitz propagation (Gap 2 deliverable):
On any set `S` containing `θ₀`, if `‖outputJacobian f X θ‖ ≤ M` and
`‖outputJacobian f X θ - outputJacobian f X θ₀‖ ≤ L_J * ‖θ - θ₀‖` for all `θ ∈ S`,
then `‖empiricalNTKMatrix f X θ - empiricalNTKMatrix f X θ₀‖ ≤ (2 * M * L_J) * ‖θ - θ₀‖`. -/
theorem empiricalNTKMatrix_lipschitz_of_jacobian_bound
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (S : Set (EuclideanSpace ℝ (Fin P))) (θ₀ : EuclideanSpace ℝ (Fin P)) (hθ₀ : θ₀ ∈ S)
    (M L_J : ℝ)
    (hJ_bdd : ∀ θ ∈ S, ‖outputJacobian f X θ‖ ≤ M)
    (hJ_lip : ∀ θ ∈ S, ‖outputJacobian f X θ - outputJacobian f X θ₀‖ ≤ L_J * ‖θ - θ₀‖)
    {θ : EuclideanSpace ℝ (Fin P)} (hθ : θ ∈ S) :
    ‖empiricalNTKMatrix f X θ - empiricalNTKMatrix f X θ₀‖ ≤ (2 * M * L_J) * ‖θ - θ₀‖ :=
  empiricalNTKMatrix_sub_le_of_jacobian_lipschitz f X θ θ₀ M L_J
    (hJ_bdd θ hθ) (hJ_bdd θ₀ hθ₀) (hJ_lip θ hθ)

/-! ### Second-Order Taylor Bound for the Training Outputs

If the output Jacobian is Lipschitz near `θ₀`, the outputs are approximated by their
linearization `f(θ₀) + J(θ₀) (θ - θ₀)` up to a quadratic remainder. This is the deterministic
half of the "lazy training" statement that the *nonlinear* network stays close to its
initialization linearization; it only needs a Lipschitz Jacobian, not twice differentiability. -/

/-- **`C^{1,1}` Taylor bound (first-order remainder under a Lipschitz derivative).** Let `G : E → F`
be Fréchet differentiable with derivative `G' z` at every `z` in the closed ball of radius `r`
around `x₀`, and suppose `‖G' z - G' x₀‖ ≤ L ‖z - x₀‖` there. Then for `‖x - x₀‖ ≤ r`,
`‖G x - G x₀ - G' x₀ (x - x₀)‖ ≤ (L / 2) ‖x - x₀‖²`. Mathlib's Taylor theorems need `n + 1` times
continuous differentiability (`taylor_mean_remainder_bound`); this only needs a Lipschitz derivative
and keeps the sharp constant `1 / 2`. The proof applies
`image_norm_le_of_norm_deriv_right_le_deriv_boundary` on `[0, 1]` to `s ↦ G (x₀ + s (x - x₀)) - ...`
with boundary `L ‖x - x₀‖² s² / 2`. -/
theorem norm_sub_sub_fderiv_le_of_lipschitz_fderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {G : E → F} {G' : E → E →L[ℝ] F} {x₀ x : E} {r L : ℝ}
    (hd : ∀ z, ‖z - x₀‖ ≤ r → HasFDerivAt G (G' z) z)
    (hlip : ∀ z, ‖z - x₀‖ ≤ r → ‖G' z - G' x₀‖ ≤ L * ‖z - x₀‖) (hx : ‖x - x₀‖ ≤ r) :
    ‖G x - G x₀ - G' x₀ (x - x₀)‖ ≤ L / 2 * ‖x - x₀‖ ^ 2 := by
  set Δ := x - x₀ with hΔ
  have hseg : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖x₀ + s • Δ - x₀‖ ≤ r := fun s hs => by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) hs.2).trans hx
  set g : ℝ → F := fun s => G (x₀ + s • Δ) - G x₀ - s • G' x₀ Δ with hg
  have hgd : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g ((G' (x₀ + s • Δ) - G' x₀) Δ) s := by
    intro s hs
    have hline : HasDerivAt (fun u : ℝ => x₀ + u • Δ) Δ s := by
      simpa using ((hasDerivAt_id s).smul_const Δ).const_add x₀
    have h1 := (hd _ (hseg s hs)).comp_hasDerivAt s hline
    have h2 := (h1.sub_const (G x₀)).sub ((hasDerivAt_id s).smul_const (G' x₀ Δ))
    refine h2.congr_deriv ?_
    simp
  have hbound := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := g) (a := 0) (b := 1) (B := fun s => L * ‖Δ‖ ^ 2 * s ^ 2 / 2)
    (B' := fun s => L * ‖Δ‖ ^ 2 * s)
    (fun s hs => (hgd s hs).continuousAt.continuousWithinAt)
    (fun s hs => (hgd s ⟨hs.1, hs.2.le⟩).hasDerivWithinAt)
    (by simp [hg])
    (fun s => by
      have := ((hasDerivAt_pow 2 s).const_mul (L * ‖Δ‖ ^ 2)).div_const 2
      convert this using 1
      push_cast
      ring)
    (fun s hs => by
      have hs' : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
      calc ‖(G' (x₀ + s • Δ) - G' x₀) Δ‖
          ≤ ‖G' (x₀ + s • Δ) - G' x₀‖ * ‖Δ‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (L * ‖s • Δ‖) * ‖Δ‖ := by
            gcongr
            simpa using hlip _ (hseg s hs')
        _ = L * ‖Δ‖ ^ 2 * s := by
            rw [norm_smul, Real.norm_of_nonneg hs.1]; ring)
    (x := 1) ⟨zero_le_one, le_rfl⟩
  have hθΔ : x₀ + Δ = x := by rw [hΔ]; abel
  simp only [hg, one_smul, hθΔ] at hbound
  linarith

/-- **Second-order Taylor bound for the training outputs under a Lipschitz Jacobian.** If the output
Jacobian is `L`-Lipschitz at `θ₀` on the closed ball of radius `r` around `θ₀`
(`‖J θ - J θ₀‖ ≤ L ‖θ - θ₀‖`, Frobenius norm) and each output is differentiable there, then for
`‖θ - θ₀‖ ≤ r`
`‖f(θ) - f(θ₀) - J(θ₀) (θ - θ₀)‖ ≤ (L / 2) ‖θ - θ₀‖²`. This is
`norm_sub_sub_fderiv_le_of_lipschitz_fderiv` for `G = trainingOutputs`, with `G' z` the linear map
`v ↦ J(z) v` (its operator norm is at most the Frobenius norm, `mulVec_frobenius_norm_le`). -/
theorem norm_trainingOutputs_sub_linearization_le
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι) (θ₀ : EuclideanSpace ℝ (Fin P)) (r L : ℝ)
    (hdiff : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r → ∀ β : Fin m,
      DifferentiableAt ℝ (fun θ' => f (X β) θ') θ)
    (hJ_lip : ∀ θ : EuclideanSpace ℝ (Fin P), ‖θ - θ₀‖ ≤ r →
      ‖outputJacobian f X θ - outputJacobian f X θ₀‖ ≤ L * ‖θ - θ₀‖)
    {θ : EuclideanSpace ℝ (Fin P)} (hθ : ‖θ - θ₀‖ ≤ r) :
    ‖trainingOutputs f X θ - trainingOutputs f X θ₀ -
        WithLp.toLp 2 (outputJacobian f X θ₀ *ᵥ (θ - θ₀).ofLp)‖ ≤ L / 2 * ‖θ - θ₀‖ ^ 2 := by
  have h := norm_sub_sub_fderiv_le_of_lipschitz_fderiv (G := trainingOutputs f X)
    (G' := fun z => matrixCLM (outputJacobian f X z)) (x₀ := θ₀) (x := θ) (r := r) (L := L)
    (fun z hz => by
      rw [← hasFDerivWithinAt_univ, hasFDerivWithinAt_euclidean]
      intro α
      rw [hasFDerivWithinAt_univ]
      have h := (hdiff z hz α).hasGradientAt.hasFDerivAt
      have hcl : PiLp.proj 2 (fun _ : Fin m => ℝ) α ∘SL matrixCLM (outputJacobian f X z) =
          InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin P))
            (gradient (fun θ' => f (X α) θ') z) := by
        ext v
        rw [InnerProductSpace.toDual_apply_apply]
        simp only [ContinuousLinearMap.comp_apply, matrixCLM_apply, PiLp.proj_apply,
          Matrix.mulVec_apply, dotProduct, outputJacobian, tangentFeature, PiLp.inner_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [mul_comm]
      exact h.congr_fderiv hcl.symm)
    (fun z hz => by
      rw [matrixCLM_sub]; exact (norm_matrixCLM_le _).trans (hJ_lip z hz)) hθ
  simpa [matrixCLM_apply] using h

/-! ### Reusable Analytic Tool: Quadratic Form Perturbation and Rayleigh-Quotient Stability

If two matrices are close in Frobenius norm, their quadratic forms are close, and consequently a
Rayleigh-quotient lower bound established at one matrix propagates - with a correspondingly
weaker constant - to any matrix within that Frobenius distance. This is Gap 5's Step 2: it shows
the spectral-gap hypothesis assumed at initialization `θ₀` continues to hold, with a degraded but
still positive constant, at any `θ` close enough to `θ₀` in parameter space - exactly what the
Gap 5 bootstrap needs to keep re-deriving a uniform-in-time Rayleigh bound along the trajectory.
-/

/-- The quadratic forms of two matrices differ by at most their Frobenius distance times `‖v‖²`:
  `|vᵀ A v - vᵀ B v| ≤ ‖A - B‖ ‖v‖²`. -/
theorem abs_dotProduct_mulVec_sub_le (A B : Matrix (Fin m) (Fin m) ℝ)
    (v : EuclideanSpace ℝ (Fin m)) :
    |v.ofLp ⬝ᵥ (A *ᵥ v.ofLp) - v.ofLp ⬝ᵥ (B *ᵥ v.ofLp)| ≤ ‖A - B‖ * ‖v‖ ^ 2 := by
  have heq : v.ofLp ⬝ᵥ (A *ᵥ v.ofLp) - v.ofLp ⬝ᵥ (B *ᵥ v.ofLp) =
      v.ofLp ⬝ᵥ ((A - B) *ᵥ v.ofLp) := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
  rw [heq]
  rw [← inner_toLp_mulVec_eq_dotProduct]
  calc
    |⟪v, (WithLp.toLp 2 ((A - B) *ᵥ v.ofLp) : EuclideanSpace ℝ (Fin m))⟫| ≤
        ‖v‖ * ‖(WithLp.toLp 2 ((A - B) *ᵥ v.ofLp) : EuclideanSpace ℝ (Fin m))‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖A - B‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (mulVec_frobenius_norm_le (A - B) v) (norm_nonneg _)
    _ = ‖A - B‖ * ‖v‖ ^ 2 := by ring

/-- A shifted positive semidefinite matrix `K - lambda_min • 1` satisfies the Rayleigh quotient
lower bound `lambda_min * ‖v‖² ≤ vᵀ K v` for all `v`. -/
theorem rayleigh_lower_bound_of_sub_smul_posSemidef
    {m : ℕ} (K : Matrix (Fin m) (Fin m) ℝ) (lambda_min : ℝ)
    (hK : (K - lambda_min • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef)
    (v : EuclideanSpace ℝ (Fin m)) :
    lambda_min * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K *ᵥ v.ofLp) := by
  have h_nonneg := Matrix.PosSemidef.dotProduct_mulVec_nonneg hK v.ofLp
  rw [star_trivial] at h_nonneg
  have h_mul : (K - lambda_min • (1 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ v.ofLp =
      K *ᵥ v.ofLp - lambda_min • v.ofLp := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [h_mul, dotProduct_sub, dotProduct_smul, smul_eq_mul] at h_nonneg
  have h_norm : v.ofLp ⬝ᵥ v.ofLp = ‖v‖ ^ 2 := by
    rw [dotProduct, EuclideanSpace.real_norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => (sq (v.ofLp i)).symm
  rw [h_norm] at h_nonneg
  linarith

/-- Rayleigh-quotient stability under a matrix distance bound: if `K₀`'s Rayleigh quotient is
bounded below by `lambda_min₀` and `‖K - K₀‖ ≤ ε`, then `K`'s Rayleigh quotient is bounded below
by `lambda_min₀ - ε`. -/
theorem rayleigh_quotient_lower_bound_of_matrix_dist
    (K K₀ : Matrix (Fin m) (Fin m) ℝ) (lambda_min₀ ε : ℝ)
    (h_rr₀ : ∀ v : EuclideanSpace ℝ (Fin m), lambda_min₀ * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K₀ *ᵥ v.ofLp))
    (hK_dist : ‖K - K₀‖ ≤ ε) (v : EuclideanSpace ℝ (Fin m)) :
    (lambda_min₀ - ε) * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ (K *ᵥ v.ofLp) := by
  have h1 := h_rr₀ v
  have h2 := (abs_le.mp (abs_dotProduct_mulVec_sub_le K K₀ v)).1
  have h3 : ‖K - K₀‖ * ‖v‖ ^ 2 ≤ ε * ‖v‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hK_dist (sq_nonneg _)
  nlinarith [h1, h2, h3]

/-- Rayleigh-quotient stability of the empirical NTK Gram matrix under parameter displacement:
if `θ₀`'s empirical NTK matrix has Rayleigh quotient bounded below by `lambda_min₀`, and the
output Jacobian is `M`-bounded at both `θ` and `θ₀` and `L_J`-Lipschitz between them, then `θ`'s
empirical NTK matrix has Rayleigh quotient bounded below by
`lambda_min₀ - (2 * M * L_J) * ‖θ - θ₀‖`. This is Gap 5's Step 2, connecting Gap 2's Lipschitz
propagation directly to the spectral-gap hypothesis the Gap 5 bootstrap needs at each `θ`. -/
theorem rayleigh_quotient_lower_bound_of_displacement
    (f : ι → EuclideanSpace ℝ (Fin P) → ℝ) (X : Fin m → ι)
    (θ₀ θ : EuclideanSpace ℝ (Fin P)) (M L_J lambda_min₀ : ℝ)
    (hJ₀ : ‖outputJacobian f X θ₀‖ ≤ M) (hJ : ‖outputJacobian f X θ‖ ≤ M)
    (hJ_lip : ‖outputJacobian f X θ - outputJacobian f X θ₀‖ ≤ L_J * ‖θ - θ₀‖)
    (h_rr₀ : ∀ v : EuclideanSpace ℝ (Fin m),
      lambda_min₀ * ‖v‖ ^ 2 ≤ v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X θ₀) *ᵥ v.ofLp))
    (v : EuclideanSpace ℝ (Fin m)) :
    (lambda_min₀ - (2 * M * L_J) * ‖θ - θ₀‖) * ‖v‖ ^ 2 ≤
      v.ofLp ⬝ᵥ ((empiricalNTKMatrix f X θ) *ᵥ v.ofLp) :=
  rayleigh_quotient_lower_bound_of_matrix_dist (empiricalNTKMatrix f X θ)
    (empiricalNTKMatrix f X θ₀) lambda_min₀ ((2 * M * L_J) * ‖θ - θ₀‖) h_rr₀
    (empiricalNTKMatrix_sub_le_of_jacobian_lipschitz f X θ θ₀ M L_J hJ hJ₀ hJ_lip) v

end NTK

end
