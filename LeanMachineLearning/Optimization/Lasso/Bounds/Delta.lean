/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Lasso.Definitions

/-! ## Section 4.6: positive-path estimate chain -/

@[expose] public section

namespace Lasso

open Filter Topology
variable {ι : Type*} [Fintype ι]
set_option linter.unusedFintypeInType false

/--
Chain rule for `matVec M` along a curve: if `g` has derivative `g'` at `τ`,
then `matVec M ∘ g` has derivative `matVec M g'` at `τ`.
-/
lemma matVec_hasDerivAt (M : Matrix ι ι ℝ) (g : ℝ → EuclideanSpace ℝ ι)
    (g' : EuclideanSpace ℝ ι) (τ : ℝ)
    (hg : HasDerivAt g g' τ) :
    HasDerivAt (fun τ => matVec M (g τ)) (matVec M g') τ := by
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv
  have h1 : HasDerivAt (fun τ => e (g τ)) (e g') τ := e.hasFDerivAt.comp_hasDerivAt τ hg
  dsimp [matVec, euclideanOf]
  apply e.symm.hasFDerivAt.comp_hasDerivAt τ
  apply hasDerivAt_pi.2
  intro i
  dsimp [Matrix.mulVec, dotProduct]
  exact HasDerivAt.fun_sum (fun j _ => (hasDerivAt_pi.1 h1 j).const_mul (M i j))

/--
Generalized FTC identity for the entropy mirror gradient along the positive DLN flow.

Proof. Define `F(τ) = ∇h(x(τ)) - τ•r + (τ*λ)•ones + M z(τ)`. Show `F'(τ) = 0`
using the mirror-flow ODE, then apply FTC to get `F(t) = F(0)`, which simplifies
to the stated identity.
-/
lemma entropyMirrorGradient_sub_eq (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ)
    (β : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r lambda ε β u)
    (hu_pos : ∀ t i, posEffectiveParameter u t i ≠ 0) (hM : M.IsSymm) (t : ℝ) :
    entropyMirrorGradient (posEffectiveParameter u t) -
      entropyMirrorGradient (posEffectiveParameter u 0) =
      t • r - (t * lambda) • ones - matVec M (posIntegratedTrajectory u t) := by
  set x := posEffectiveParameter u
  set z := posIntegratedTrajectory u
  -- Continuity of the effective parameter (from its differentiability)
  have hcont : Continuous x :=
    continuous_iff_continuousAt.mpr
      (fun τ => (pos_effective_parameter_hasDerivAt M r lambda ε β u hu hM τ).continuousAt)
  -- Coordinate projection is continuous
  have h_cont_apply (i : ι) : Continuous (fun x : EuclideanSpace ℝ ι => x i) :=
    (continuous_apply i).comp (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv.continuous
  -- Derivative of the integrated trajectory z(τ) = ∫₀ᵗ x(v) dv is x(τ)
  have hz_deriv (τ : ℝ) : HasDerivAt z (x τ) τ := by
    let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) :=
      (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv
    dsimp [z, posIntegratedTrajectory, euclideanOf]
    have h_pi : HasDerivAt (fun τ => (fun i => ∫ v in (0:ℝ)..τ, x v i))
        (fun i => x τ i) τ := by
      apply hasDerivAt_pi.2
      intro i
      have hcont_i : Continuous (fun v => x v i) :=
        (h_cont_apply i).comp hcont
      exact intervalIntegral.integral_hasDerivAt_right
        (hcont_i.intervalIntegrable 0 τ)
        (hcont_i.stronglyMeasurableAtFilter _ _)
        hcont_i.continuousAt
    exact e.symm.hasFDerivAt.comp_hasDerivAt τ h_pi
  -- Define the "constant" function F
  set F : ℝ → EuclideanSpace ℝ ι := fun τ =>
    entropyMirrorGradient (x τ) - τ • r + (τ * lambda) • ones + matVec M (z τ)
  -- Show F'(τ) = 0 everywhere
  have hderiv : ∀ τ : ℝ, HasDerivAt F 0 τ := by
    intro τ
    -- Derivative of the first term: ∇h(x(τ))
    have h1 : HasDerivAt (fun τ => entropyMirrorGradient (x τ))
        (r - matVec M (x τ) - lambda • ones) τ := by
      have hmf_raw := pos_dln_is_entropy_mirror_flow M r lambda ε β u hu hu_pos hM τ
      dsimp [IsEntropyMirrorFlow] at hmf_raw
      rw [gradient_tiltedLoss M r lambda hM (x τ)] at hmf_raw
      convert hmf_raw using 1
      ext i
      simp [matVec, euclideanOf, ones]
      ring
    -- Derivative of τ • r
    have h2 : HasDerivAt (fun τ : ℝ => τ • r) r τ := by
      simpa using (hasDerivAt_id τ).smul_const r
    -- Derivative of (τ*λ) • ones
    have h2b : HasDerivAt (fun τ : ℝ => (τ * lambda) • (ones : EuclideanSpace ℝ ι))
        (lambda • (ones : EuclideanSpace ℝ ι)) τ := by
      simpa [smul_smul, mul_comm] using
        (hasDerivAt_id τ).smul_const (lambda • (ones : EuclideanSpace ℝ ι))
    -- Derivative of matVec M (z τ)
    have h3 : HasDerivAt (fun τ => matVec M (z τ)) (matVec M (x τ)) τ :=
      matVec_hasDerivAt M z (x τ) τ (hz_deriv τ)
    -- Combine: F' = h1 - h2 + h2b + h3 = 0
    have hsum := ((h1.sub h2).add h2b).add h3
    have hzero : (r - matVec M (x τ) - lambda • ones) - r +
      lambda • ones + matVec M (x τ) = 0 := by abel
    rw [hzero] at hsum
    exact hsum
  -- Apply FTC: F(t) - F(0) = ∫₀ᵗ 0 = 0, so F(t) = F(0)
  have hconst : F t - F 0 = ∫ _τ in (0:ℝ)..t, (0 : EuclideanSpace ℝ ι) :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hderiv τ)
      intervalIntegrable_const).symm
  simp only [intervalIntegral.integral_zero, sub_eq_zero] at hconst
  -- Compute F(0) and F(t)
  have hF0 : F 0 = entropyMirrorGradient (x 0) := by
    dsimp [F]
    have hz0 : z 0 = 0 := by ext i; simp [z, posIntegratedTrajectory, euclideanOf]
    have hmz0 : matVec M (0 : EuclideanSpace ℝ ι) = 0 := by ext i; simp [matVec, euclideanOf]
    rw [hz0, hmz0]; simp
  rw [hF0] at hconst
  dsimp [F] at hconst
  -- hconst: ∇h(x t) - t•r + (t*λ)•ones + M z t = ∇h(x 0)
  -- Rearrange to get desired form
  rw [← hconst]
  abel

/--
By the Fundamental Theorem of Calculus (FTC), the entropy mirror map's gradient
integrates to the negated tilted loss gradient over time.

Informal proof reference: `docs/Lasso.md`, Section 4.2.
By `dln_is_mirror_flow`, `d/dt (1/4 log(x_i)) = - (M x - r + λ 1)_i`.
Integrating from `0` to `t` and applying coordinate-wise rescaling by `4 / log(1/ε)`
gives the integrated mirror equation. We provide this as a reusable API.
-/
lemma posRescaledMirrorVariable_sub_eq_integral
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ)
    (β : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r lambda ε β u)
    (hu_pos : ∀ t i, posEffectiveParameter u t i ≠ 0) (hM : M.IsSymm) (s : ℝ)
    (hlog : Real.log (1 / ε) ≠ 0) :
    posRescaledMirrorVariable ε u s - posRescaledMirrorVariable ε u 0 =
      matVec M (posIntegratedTrajectoryRescaled ε u s) - s • r + (s * lambda) • ones := by
  -- Abbreviations for readability
  set t_s := posTimeFromRescaled ε s
  set x := posEffectiveParameter u
  set c := (4 : ℝ) / Real.log (1 / ε)
  -- Generalized FTC identity from the extracted lemma
  -- Relationship between posRescaledMirrorVariable and entropyMirrorGradient
  have h_mirror (τ : ℝ) : posRescaledMirrorVariable ε u τ =
      -c • entropyMirrorGradient (x (posTimeFromRescaled ε τ)) := by
    ext i
    simp [posRescaledMirrorVariable, entropyMirrorGradient, c, x, euclideanOf]
    ring
  -- posTimeFromRescaled ε 0 = 0
  have ht0 : posTimeFromRescaled ε 0 = 0 := by
    dsimp [posTimeFromRescaled]; ring
  -- Relate posIntegratedTrajectoryRescaled to the unscaled integrated trajectory
  have h_z_rescaled :
      posIntegratedTrajectoryRescaled ε u s = c • (posIntegratedTrajectory u) t_s := by
    dsimp [posIntegratedTrajectoryRescaled, c, t_s]
  -- Now compute the main equality
  calc
    posRescaledMirrorVariable ε u s - posRescaledMirrorVariable ε u 0
        = (-c • entropyMirrorGradient (x t_s)) -
          (-c • entropyMirrorGradient (x (posTimeFromRescaled ε 0))) := by
      rw [h_mirror s, h_mirror 0]
    _ = (-c • entropyMirrorGradient (x t_s)) - (-c • entropyMirrorGradient (x 0)) := by rw [ht0]
    _ = -c • (entropyMirrorGradient (x t_s) - entropyMirrorGradient (x 0)) := by
      rw [← smul_sub]
    _ = -c • (t_s • r - (t_s * lambda) • ones - matVec M ((posIntegratedTrajectory u) t_s)) := by
      rw [entropyMirrorGradient_sub_eq M r lambda ε β u hu hu_pos hM t_s]
    _ = (-c • (t_s • r)) + (-c • (-((t_s * lambda) • ones))) +
        (-c • (-matVec M ((posIntegratedTrajectory u) t_s))) := by
      simp [smul_sub, add_assoc]
    _ = (-(c * t_s)) • r + (c * (t_s * lambda)) • ones +
        c • matVec M ((posIntegratedTrajectory u) t_s) := by
      simp [smul_smul, neg_smul]
    _ = -(c * t_s) • r + (c * t_s * lambda) • ones +
        c • matVec M ((posIntegratedTrajectory u) t_s) := by ring_nf
    _ = -s • r + (s * lambda) • ones + c • matVec M ((posIntegratedTrajectory u) t_s) := by
      have hct : c * t_s = s := by
        dsimp [c, t_s, posTimeFromRescaled]; field_simp [hlog]
      rw [hct]
    _ = -s • r + (s * lambda) • ones +
        matVec M (c • (posIntegratedTrajectory u) t_s) := by rw [matVec_smul_eq]
    _ = matVec M (posIntegratedTrajectoryRescaled ε u s) - s • r + (s * lambda) • ones := by
      rw [h_z_rescaled]
      simp [sub_eq_add_neg]; abel

/--
Section 4.6, integrated mirror-flow identity in rescaled time.

Informal proof reference: `docs/Lasso.md`, Section 4.6, Eq. (4.13).  Integrate
`d wᵋ / ds = M xᵋ - r + λ 𝟙` from `0` to `s`, using the corrected rescaled
integrated trajectory API.
-/
theorem positive_integrated_mirror_equation
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda ε : ℝ)
    (β : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hu : posDlnGradientFlow M r lambda ε β u)
    (hu_pos : ∀ t i, posEffectiveParameter u t i ≠ 0) (hM : M.IsSymm) (s : ℝ)
    (hlog : Real.log (1 / ε) ≠ 0) :
    posRescaledMirrorVariable ε u s =
      posRescaledMirrorVariable ε u 0 - s • r +
        matVec M (posIntegratedTrajectoryRescaled ε u s) + (s * lambda) • ones := by
  have hsub := posRescaledMirrorVariable_sub_eq_integral M r lambda ε β u hu hu_pos hM s hlog
  have h1 : posRescaledMirrorVariable ε u s = posRescaledMirrorVariable ε u 0 +
    (posRescaledMirrorVariable ε u s - posRescaledMirrorVariable ε u 0) := by abel
  rw [h1, hsub]
  abel

/--
Section 4.6, Eq. (4.14), Term 1.
Informal proof reference: `docs/Lasso.md`, Section 4.6.
Bounds the inner product of `x^\varepsilon` and `w^\varepsilon`.

**Proof Sketch**:
1. By the definition of the primal path, $\dot{z}^\varepsilon(s) = x^\varepsilon(s)$.
2. By the mirror mapping, the dual variable is
   $w^\varepsilon_i(s) = - \frac{1}{\log(1/\varepsilon)} \log(x^\varepsilon_i(s))$.
3. Therefore, $\langle \dot{z}^\varepsilon(s), w^\varepsilon(s) \rangle =$
   $\frac{1}{\log(1/\varepsilon)} \sum_{i} -x^\varepsilon_i(s) \log(x^\varepsilon_i(s))$.
4. The function $x \mapsto -x \log x$ is bounded on bounded intervals (and extends continuously to
   $0$ with value $0$).
5. Since $x^\varepsilon(s)$ is uniformly bounded on $s \in [0, s_{max}]$, the sum is bounded by a
   uniform constant $C > 0$.
6. Thus the term is $\leq C / \log(1/\varepsilon)$.
-/
-- Bounds the function f(t) = -t * log(t) for t ≥ 0.
-- For t = 0, f(0) = 0 ≤ 1. For t > 0, use log(1/t) ≤ 1/t - 1 to get -t log t ≤ 1 - t ≤ 1.
private lemma neg_mul_log_le_one (t : ℝ) (ht : 0 ≤ t) : -t * Real.log t ≤ 1 := by
  by_cases ht0 : t = 0
  · rw [ht0]; simp
  · have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hlog := Real.log_le_sub_one_of_pos (one_div_pos.mpr ht_pos)
    rw [one_div, Real.log_inv] at hlog
    -- hlog : -Real.log t ≤ t⁻¹ - 1
    have h_mul : -t * Real.log t ≤ 1 - t := by
      calc
        -t * Real.log t = t * (-Real.log t) := by ring
        _ ≤ t * (t⁻¹ - 1) := mul_le_mul_of_nonneg_left hlog (by linarith)
        _ = t * t⁻¹ - t := by ring
        _ = 1 - t := by field_simp [ht0]
    nlinarith

-- Helper: derivative of `posIntegratedTrajectoryRescaled` cancels the scaling factors,
-- yielding `posEffectiveParameter` as the derivative.
-- Uses the chain rule: derivative of `posIntegratedTrajectory` is `posEffectiveParameter`,
-- and `posTimeFromRescaled` scales time by `log(1/ε)/4` which cancels the outer factor `c`.
private lemma posIntegratedTrajectoryRescaled_hasDerivAt
    (ε : ℝ) (u_eps : ℝ → EuclideanSpace ℝ ι) (τ : ℝ)
    (h_cont_u : Continuous u_eps)
    (h_log_ne_zero : Real.log (1 / ε) ≠ 0) :
    HasDerivAt (fun ρ => posIntegratedTrajectoryRescaled ε u_eps ρ)
      (posEffectiveParameter u_eps (posTimeFromRescaled ε τ)) τ := by
  set c := (4 : ℝ) / Real.log (1 / ε)
  set t_ετ := posTimeFromRescaled ε τ with ht_ετ_def
  -- Projection `x ↦ x i` is continuous on `EuclideanSpace`
  have h_proj_cont (i : ι) : Continuous (fun (x : EuclideanSpace ℝ ι) => x i) :=
    (continuous_apply i).comp
      ((WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv.continuous)
  -- `coordinateSquare` is continuous
  have h_cont_coordSquare :
      Continuous (coordinateSquare : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) := by
    let e : (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ ι :=
      (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toContinuousLinearEquiv
    have h_sq : Continuous (fun (x : EuclideanSpace ℝ ι) (i : ι) => x i * x i) :=
      continuous_pi (fun i => Continuous.mul (h_proj_cont i) (h_proj_cont i))
    have h_eq : coordinateSquare = e ∘ (fun (x : EuclideanSpace ℝ ι) => fun i => x i * x i) := by
      ext x i; simp [coordinateSquare, euclideanOf, e]
    rw [h_eq]
    exact e.continuous.comp h_sq
  -- FTC: derivative of `posIntegratedTrajectory` is `posEffectiveParameter`
  have h_z_deriv : HasDerivAt (posIntegratedTrajectory u_eps)
      (posEffectiveParameter u_eps t_ετ) t_ετ := by
    -- Work on `ι → ℝ` first using `hasDerivAt_pi`, then lift back to `EuclideanSpace`
    let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) :=
      (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv
    have h_pi : HasDerivAt
        (fun σ : ℝ => (fun i : ι =>
          ∫ v in (0:ℝ)..σ, posEffectiveParameter u_eps v i))
        (fun i : ι => posEffectiveParameter u_eps t_ετ i) t_ετ := by
      apply hasDerivAt_pi.mpr
      intro i
      have hcont_i : Continuous (fun v : ℝ => posEffectiveParameter u_eps v i) :=
        (h_proj_cont i).comp (h_cont_coordSquare.comp h_cont_u)
      exact intervalIntegral.integral_hasDerivAt_right
        (hcont_i.intervalIntegrable 0 t_ετ)
        (hcont_i.stronglyMeasurableAtFilter _ _)
        hcont_i.continuousAt
    exact e.symm.hasFDerivAt.comp_hasDerivAt t_ετ h_pi
  -- Derivative of `posTimeFromRescaled ε ρ = (ρ/4) * log(1/ε)`
  have h_time_deriv : HasDerivAt (fun ρ => posTimeFromRescaled ε ρ)
      (Real.log (1 / ε) / 4) τ := by
    dsimp [posTimeFromRescaled]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id τ).div_const 4).mul_const (Real.log (1 / ε))
  have h_smul : HasDerivAt
      (fun ρ => c • ((posIntegratedTrajectory u_eps) (posTimeFromRescaled ε ρ)))
      (c • ((Real.log (1 / ε) / 4) •
        posEffectiveParameter u_eps t_ετ)) τ :=
    (h_z_deriv.scomp τ h_time_deriv).const_smul c
  -- The scaling factors cancel: c * (log(1/ε)/4) = 1
  have h_factor : c * (Real.log (1 / ε) / 4) = 1 := by
    dsimp [c]
    field_simp [h_log_ne_zero]
  have h_target : c • ((Real.log (1 / ε) / 4) • posEffectiveParameter u_eps t_ετ) =
      posEffectiveParameter u_eps t_ετ := by
    rw [smul_smul, h_factor, one_smul]
  rw [h_target] at h_smul
  simpa [posIntegratedTrajectoryRescaled, c, ht_ετ_def] using h_smul

lemma pos_delta_bound_1
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ) (_hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (_hdata : ProblemData M r lambda) (_hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε)) :
    ∃ C > 0, ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        inner ℝ (deriv (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) τ)
          (posRescaledMirrorVariable ε (u ε) τ)
        ≤ C / Real.log (1 / ε) := by
  set d := Fintype.card ι
  set C := max 1 (d : ℝ)
  refine ⟨C, lt_max_of_lt_left (by norm_num), ?_⟩
  -- Restrict to ε ∈ (0, 1/2), where log(1/ε) > 0
  have h_mem : Set.Ioo (0 : ℝ) (1/2) ∈ 𝓝[>] (0 : ℝ) := by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨1/2, by norm_num, fun x hx => hx⟩
  filter_upwards [h_mem] with ε hε
  rcases hε with ⟨hε_pos, hε_lt_half⟩
  have hε_lt_one : ε < 1 := by linarith
  have h_log_pos : 0 < Real.log (1 / ε) :=
    Real.log_pos (one_lt_one_div hε_pos hε_lt_one)
  have h_log_ne_zero : Real.log (1 / ε) ≠ 0 := ne_of_gt h_log_pos
  have hu_eps : posDlnGradientFlow M r lambda ε β (u ε) := hu ε hε_pos
  intro τ hτ
  -- Key: prove `HasDerivAt` for the rescaled integrated trajectory.
  -- The derivative equals `posEffectiveParameter` because the rescaling factors cancel.
  have h_hasDeriv : HasDerivAt (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
      (posEffectiveParameter (u ε) (posTimeFromRescaled ε τ)) τ :=
    posIntegratedTrajectoryRescaled_hasDerivAt ε (u ε) τ
      hu_eps.cont_diff.continuous h_log_ne_zero
  -- Now rewrite `deriv` using the hasDeriv lemma
  rw [h_hasDeriv.deriv]
  set x := posEffectiveParameter (u ε) (posTimeFromRescaled ε τ)
  have hx_nonneg : ∀ i, 0 ≤ x i :=
    posEffectiveParameter_nonnegative (u ε) (posTimeFromRescaled ε τ)
  -- Expand the inner product: ⟨x, w⟩ where w_i = -log(x_i)/log(1/ε)
  have h_inner_eq : inner ℝ x (posRescaledMirrorVariable ε (u ε) τ) =
      (1 / Real.log (1 / ε)) * (∑ i : ι, (-(x i) * Real.log (x i))) := by
    -- Use `PiLp.inner_apply` to expand the inner product into a sum
    rw [PiLp.inner_apply]
    simp_rw [Real.inner_apply]
    -- Now goal: ∑ i, x i * (posRescaledMirrorVariable ε (u ε) τ) i =
    --   (1 / log(1/ε)) * ∑ i, -(x i) * log (x i)
    have h_w (i : ι) : (posRescaledMirrorVariable ε (u ε) τ) i =
        -Real.log (x i) / Real.log (1 / ε) := rfl
    simp_rw [h_w]
    -- Now: ∑ i, x i * (-Real.log (x i) / Real.log (1 / ε)) =
    --   (1/log(1/ε)) * ∑ i, -(x i) * Real.log (x i)
    calc
      ∑ i : ι, x i * (-Real.log (x i) / Real.log (1 / ε)) =
          ∑ i : ι, (-(x i) * Real.log (x i)) / Real.log (1 / ε) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      _ = (∑ i : ι, (-(x i) * Real.log (x i))) / Real.log (1 / ε) := by rw [Finset.sum_div]
      _ = (1 / Real.log (1 / ε)) * (∑ i : ι, (-(x i) * Real.log (x i))) := by ring
  rw [h_inner_eq]
  -- Bound each term: -x_i * log(x_i) ≤ 1 for x_i ≥ 0
  -- Proof: f(t) = -t log t has maximum 1/e at t = 1/e, and 1/e ≤ 1.
  -- We use: for t > 0, log(1/t) ≤ 1/t - 1  →  -log t ≤ 1/t - 1  →  -t log t ≤ 1 - t ≤ 1.
  have h_each (i : ι) : -(x i) * Real.log (x i) ≤ 1 :=
    neg_mul_log_le_one (x i) (hx_nonneg i)
  -- Sum the per-coordinate bounds
  have h_sum_bound : (∑ i : ι, (-(x i) * Real.log (x i))) ≤ C := by
    calc
      (∑ i : ι, (-(x i) * Real.log (x i))) ≤ (∑ i : ι, (1 : ℝ)) :=
        Finset.sum_le_sum (fun i _ => h_each i)
      _ = (d : ℝ) := by simp [d]
      _ ≤ C := by simp [C]
  -- Final: divide by log(1/ε) > 0
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    (1 * (Real.log (1 / ε))⁻¹) * (∑ i : ι, (-(x i) * Real.log (x i))) =
        (Real.log (1 / ε))⁻¹ * (∑ i : ι, (-(x i) * Real.log (x i))) := by ring
    _ ≤ (Real.log (1 / ε))⁻¹ * C :=
      mul_le_mul_of_nonneg_left h_sum_bound (inv_nonneg.mpr (by linarith))
    _ = C * (Real.log (1 / ε))⁻¹ := mul_comm _ _

-- Inner product of two nonnegative vectors is nonnegative.
private lemma inner_nonneg_of_nonneg (x w : EuclideanSpace ℝ ι)
    (hx : Nonnegative x) (hw : Nonnegative w) : 0 ≤ inner ℝ x w := by
  rw [PiLp.inner_apply]
  simp_rw [Real.inner_apply]
  refine Finset.sum_nonneg (fun i _ => mul_nonneg (hx i) (hw i))

-- Given the LCP dual variable v, scaling by τ gives the target expression.
-- Uses the relation parametricLcpQ r lambda τ = (-τ) • r + (1 + τ * lambda) • ones.
private lemma lcp_dual_scale_eq_target
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (τ : ℝ) (hτ_ne : τ ≠ 0)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (v : EuclideanSpace ℝ ι)
    (hv_eq : v = lcpQ r lambda τ + matVec M (x_lasso τ)) :
    τ • v = matVec M (scaledPrimalPath x_lasso τ) - τ • r + (1 + τ * lambda) • ones := by
  calc
    τ • v = τ • (lcpQ r lambda τ + matVec M (x_lasso τ)) := by rw [hv_eq]
    _ = τ • lcpQ r lambda τ + τ • matVec M (x_lasso τ) := by rw [smul_add]
    _ = τ • lcpQ r lambda τ + matVec M (τ • (x_lasso τ)) := by rw [matVec_smul_eq]
    _ = parametricLcpQ r lambda τ + matVec M (scaledPrimalPath x_lasso τ) := by
      have h_lcpQ_smul : τ • lcpQ r lambda τ = parametricLcpQ r lambda τ := by
        ext i
        simp [lcpQ, parametricLcpQ, euclideanOf]
        field_simp [hτ_ne]
        ring
      rw [h_lcpQ_smul, scaledPrimalPath]
    _ = ((-τ) • r + (1 + τ * lambda) • ones) + matVec M (scaledPrimalPath x_lasso τ) := by
      have h_para_expand : parametricLcpQ r lambda τ = (-τ) • r + (1 + τ * lambda) • ones := by
        ext i
        simp [parametricLcpQ, ones, euclideanOf]
        ring
      rw [h_para_expand]
    _ = matVec M (scaledPrimalPath x_lasso τ) - τ • r + (1 + τ * lambda) • ones := by
      simp [add_comm, add_left_comm, sub_eq_add_neg]

/--
Section 4.6, Eq. (4.14), Term 2.
Informal proof reference: `docs/Lasso.md`, Section 4.6.
Bounds the cross term $-<x^\varepsilon, w>$ by 0.

**Proof Sketch**:
1. We have $\dot{z}^\varepsilon(s) = x^\varepsilon(s)$. The primal flow $x^\varepsilon(s)$
   is defined as the square of the parameter $u(s)$, so $x^\varepsilon(s) \ge 0$ component-wise.
2. The dual variable $w(s) = M z(s) - s r + (1 + s \lambda) \mathbf{1}$ represents the dual slack
   of the target positive lasso path. By LCP conditions, $w(s) \ge 0$.
3. The inner product of two nonnegative vectors is nonnegative:
   $\langle x^\varepsilon(s), w(s) \rangle \ge 0$.
4. Taking the negative gives $-\langle \dot{z}^\varepsilon(s), w(s) \rangle \le 0$.
-/
lemma pos_delta_bound_2
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ) (_hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ)) :
    ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        - inner ℝ (deriv (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) τ)
          (matVec M (scaledPrimalPath x_lasso τ) - τ • r + (1 + τ * lambda) • ones)
        ≤ 0 := by
  filter_upwards [by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨1/2, by norm_num, fun x hx => hx⟩] with ε hε
  rcases hε with ⟨hε_pos, _⟩
  have h_log_ne_zero : Real.log (1 / ε) ≠ 0 :=
    ne_of_gt (Real.log_pos (one_lt_one_div hε_pos (by linarith)))
  intro τ hτ
  rcases hτ with ⟨hτ0, _⟩
  rw [(posIntegratedTrajectoryRescaled_hasDerivAt ε (u ε) τ
    (hu ε hε_pos).cont_diff.continuous h_log_ne_zero).deriv]
  set x := posEffectiveParameter (u ε) (posTimeFromRescaled ε τ)
  have hx_nonneg : Nonnegative x :=
    posEffectiveParameter_nonnegative (u ε) (posTimeFromRescaled ε τ)
  -- Need to show: -⟨x, M z - τ r + (1 + τ λ) 𝟙⟩ ≤ 0
  -- i.e., ⟨x, M z - τ r + (1 + τ λ) 𝟙⟩ ≥ 0
  -- Since x ≥ 0, it suffices to show M z - τ r + (1 + τ λ) 𝟙 ≥ 0
  by_cases hτ_zero : τ = 0
  · -- Case τ = 0: the vector simplifies to ones
    subst τ
    rw [show matVec M (scaledPrimalPath x_lasso 0) - (0 : ℝ) • r +
        (1 + (0 : ℝ) * lambda) • ones = ones by
      simp [scaledPrimalPath, ones, matVec, euclideanOf]]
    linarith [inner_nonneg_of_nonneg x ones hx_nonneg
      (by intro i; simp [ones, euclideanOf])]
  · -- Case τ > 0: use LCP conditions to get nonnegativity of the dual variable
    have hτ_pos : 0 < τ := by
      by_contra! h
      exact hτ_zero (le_antisymm h hτ0)
    rcases (pos_lasso_is_lcp M r lambda τ (x_lasso τ) hdata.psd.symm hdata.psd).mp
      (hx_lasso τ hτ_pos) with
      ⟨v, hv_eq, hv_nonneg, hx_lasso_nonneg, hvx_zero⟩
    have h_nonneg : 0 ≤ inner ℝ x (τ • v) :=
      inner_nonneg_of_nonneg x (τ • v) hx_nonneg
        (by
          intro i
          simp only [PiLp.smul_apply, smul_eq_mul]
          exact mul_nonneg (by linarith) (hv_nonneg i))
    rw [lcp_dual_scale_eq_target M r lambda τ hτ_pos.ne.symm x_lasso v hv_eq] at h_nonneg
    linarith

/--
Section 4.6, Eq. (4.14), Term 3.
Informal proof reference: `docs/Lasso.md`, Section 4.6.
Bounds the cross term $-<\dot{z}, w^\varepsilon>$ using trajectory variations.

**Proof Sketch**:
1. We analyze $-\langle \dot{z}(s), w^\varepsilon(s) \rangle$ by decomposing the target velocity
   $\dot{z}(s) = \dot{z}_+ - \dot{z}_-$.
2. For the positive part, we bound $w^\varepsilon_i(s)$ from below. Since $x^\varepsilon(s)$
   is uniformly bounded above by some $X$,
   $w^\varepsilon_i(s) \ge -\frac{\log X}{\log(1/\varepsilon)}$.
3. Thus, $-\langle \dot{z}_+(s), w^\varepsilon(s) \rangle \le
   \frac{C_1}{\log(1/\varepsilon)} \sum (\dot{z}_+)_i$,
   which contributes to the $\dot{z}^\uparrow$ bound.
4. For the negative part, we have $+\langle \dot{z}_-(s), w^\varepsilon(s) \rangle$. Although
   $w^\varepsilon_i(s)$ can be large positive when $x^\varepsilon_i \to 0$, we use the uniform
   trajectory bound to control this term, giving $C_2 \sum (\dot{z}_-)_i$.
5. Combining these bounds yields a uniform bound weighted by the absolute variations
   $\dot{z}^\uparrow$ and $\dot{z}^\downarrow$.
-/
lemma pos_delta_bound_3
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        - inner ℝ (deriv (scaledPrimalPath x_lasso) τ)
            (posRescaledMirrorVariable ε (u ε) τ)
        ≤ C * (1 / Real.log (1 / ε) * deriv (positiveZUpward x_lasso) τ +
          deriv (positiveZDownward x_lasso) τ) := by
  -- Postulate the uniform trajectory bound (Proposition 4.1, not yet formalized).
  -- This gives a constant X > 0 such that for all sufficiently small ε and all
  -- τ ∈ [0,s], every coordinate of xᵋ(τ) is bounded above by X.
  have h_uniform_bound : ∃ X > 0, ∀ᶠ ε in 𝓝[>] 0, ∀ τ ∈ Set.Icc (0 : ℝ) s,
      ∀ i, posEffectiveParameter (u ε) (posTimeFromRescaled ε τ) i ≤ X := by
    -- This requires Proposition 4.1 from the paper (Section 4.3).
    -- Proof sketch: use energy monotonicity (Lemma 4.2), Bregman divergence
    -- characterization (Lemma 4.3), bounds on dual iterates (Lemmas 4.4-4.5),
    -- and Carathéodory's cone theorem (Lemmas 4.6-4.7).
    sorry
  rcases h_uniform_bound with ⟨X, hX_pos, hX_ev⟩
  -- From the trajectory bound and the definition wᵋ_i = -log(xᵋ_i)/log(1/ε),
  -- we obtain a lower bound: wᵋ_i(τ) ≥ -C_low / log(1/ε).
  -- Since xᵋ_i ≤ X, we have log(xᵋ_i) ≤ max(0, log X), so
  -- -log(xᵋ_i) ≥ -max(0, log X), giving the bound.
  have h_w_lower : ∃ C_low > 0, ∀ᶠ ε in 𝓝[>] 0, ∀ τ ∈ Set.Icc (0 : ℝ) s,
      ∀ i, -C_low / Real.log (1 / ε) ≤ posRescaledMirrorVariable ε (u ε) τ i := by
    -- Let C_low := max(0, log X) if X ≥ 1, or 1 if X < 1 (to keep positivity).
    -- For each i: wᵋ_i = -log(xᵋ_i)/log(1/ε) ≥ -max(0, log X)/log(1/ε) ≥ -C_low/log(1/ε)
    sorry
  rcases h_w_lower with ⟨C_low, hC_low_pos, hW_low_ev⟩
  -- From the integrated mirror equation (positive_integrated_mirror_equation)
  -- together with the trajectory bound, we obtain an upper bound:
  -- |wᵋ_i(τ)| ≤ C_w * (1 + τ).
  -- The integrated mirror equation gives:
  --   wᵋ(τ) = wᵋ(0) - τ·r + M·zᵋ(τ) + τ·λ·𝟙
  -- Since xᵋ is bounded, zᵋ(τ) = ∫₀ᵗ xᵋ is bounded by τ·X, and wᵋ(0) ≈ 𝟙 is bounded.
  have h_w_upper : ∃ C_w > 0, ∀ᶠ ε in 𝓝[>] 0, ∀ τ ∈ Set.Icc (0 : ℝ) s,
      ∀ i, |posRescaledMirrorVariable ε (u ε) τ i| ≤ C_w * (1 + τ) := by
    -- This follows from positive_integrated_mirror_equation plus the trajectory bound.
    -- The proof requires M.IsSymm (from hdata.psd.symm) and the positivity condition
    -- hu_pos : ∀ t i, posEffectiveParameter u t i ≠ 0 (which follows from hβ and
    -- the gradient flow preserving positivity — also not yet formalized).
    sorry
  rcases h_w_upper with ⟨C_w, hC_w_pos, hW_ev⟩
  -- Combine the constants
  set C := max C_low C_w with hC_def
  have hC_pos : 0 < C := lt_max_of_lt_left hC_low_pos
  refine ⟨C, hC_pos, ?_⟩
  -- Intersect the three "eventually" filters
  filter_upwards [hX_ev, hW_low_ev, hW_ev] with ε hXε hW_low_ε hW_ε
  intro τ hτ
  rcases hτ with ⟨hτ0, hτs⟩
  -- Notation for the derivative and the dual variable
  set ż := deriv (scaledPrimalPath x_lasso) τ with hż_def
  set w := posRescaledMirrorVariable ε (u ε) τ with hw_def
  -- Expand the inner product on EuclideanSpace into a coordinate sum
  have h_inner_eq : inner ℝ ż w = ∑ i : ι, ż i * w i := by
    rw [PiLp.inner_apply]
    simp_rw [Real.inner_apply]
  -- The key algebraic decomposition:
  --   -⟨ż, w⟩ = -∑_i max(0, ż_i)·w_i + ∑_i max(0, -ż_i)·w_i
  -- This uses the identity a = max(0,a) - max(0,-a) for any real a.
  have h_decomp : -inner ℝ ż w =
      -(∑ i, max 0 (ż i) * w i) + (∑ i, max 0 (-ż i) * w i) := by
    rw [h_inner_eq]
    have h_sum_eq : (∑ i : ι, ż i * w i) =
        (∑ i : ι, max 0 (ż i) * w i) - (∑ i : ι, max 0 (-ż i) * w i) := by
      calc
        (∑ i : ι, ż i * w i) = (∑ i : ι, (max 0 (ż i) - max 0 (-ż i)) * w i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          by_cases hpos : 0 ≤ ż i
          · -- Case ż i ≥ 0: max 0 (ż i) = ż i, max 0 (-ż i) = 0
            have hmax1 : max 0 (ż i) = ż i := max_eq_right hpos
            have hmax2 : max 0 (-ż i) = 0 :=
              max_eq_left (by linarith : -ż i ≤ 0)
            calc
              ż i * w i = (ż i - 0) * w i := by ring
              _ = (max 0 (ż i) - max 0 (-ż i)) * w i := by rw [hmax1, hmax2]
          · -- Case ż i < 0: max 0 (ż i) = 0, max 0 (-ż i) = -ż i
            have hneg' : ż i ≤ 0 := by linarith
            have hmax1 : max 0 (ż i) = 0 := max_eq_left hneg'
            have hmax2 : max 0 (-ż i) = -ż i :=
              max_eq_right (by linarith : 0 ≤ -ż i)
            calc
              ż i * w i = (0 - (-ż i)) * w i := by ring
              _ = (max 0 (ż i) - max 0 (-ż i)) * w i := by rw [hmax1, hmax2]
        _ = (∑ i : ι, (max 0 (ż i) * w i - max 0 (-ż i) * w i)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
        _ = (∑ i : ι, max 0 (ż i) * w i) - (∑ i : ι, max 0 (-ż i) * w i) := by
          rw [Finset.sum_sub_distrib]
    rw [h_sum_eq]
    ring
  -- Now bound each part using the bounds on w.
  -- For the positive part: since w_i ≥ -C_low / log(1/ε) and max(0, ż_i) ≥ 0,
  --   -(max(0, ż_i)) * w_i ≤ max(0, ż_i) * C_low / log(1/ε)
  -- For the negative part: since |w_i| ≤ C_w * (1+τ) and max(0, -ż_i) ≥ 0,
  --   max(0, -ż_i) * w_i ≤ max(0, -ż_i) * C_w * (1+τ)
  have h_bound_pos : -(∑ i, max 0 (ż i) * w i) ≤
      (C_low / Real.log (1 / ε)) * (∑ i, max 0 (ż i)) := by
    -- For each i: -(max(0, ż_i)) * w_i ≤ max(0, ż_i) * C_low / log(1/ε)
    -- This uses hW_low_ε which gives -C_low / log(1/ε) ≤ w_i
    sorry
  have h_bound_neg : (∑ i, max 0 (-ż i) * w i) ≤
      C_w * (∑ i, (1 + τ) * max 0 (-ż i)) := by
    -- For each i: max(0, -ż_i) * w_i ≤ max(0, -ż_i) * C_w * (1+τ)
    -- This uses hW_ε which gives |w_i| ≤ C_w * (1+τ), so w_i ≤ C_w * (1+τ)
    sorry
  -- Relate the sums to derivatives of positiveZUpward and positiveZDownward.
  -- By the Fundamental Theorem of Calculus:
  --   deriv (positiveZUpward x_lasso) τ = ∑_i max 0 (deriv (scaledPrimalPath x_lasso) τ i)
  --   deriv (positiveZDownward x_lasso) τ
  --     = ∑_i (1+τ) * max 0 (-deriv (scaledPrimalPath x_lasso) τ i)
  have h_upward_eq : deriv (positiveZUpward x_lasso) τ = ∑ i, max 0 (ż i) := by
    -- This follows from the definition of positiveZUpward and the FTC.
    -- At points where the derivative does not exist, both sides are 0 (deriv returns 0,
    -- and ż = 0, so max 0 (ż i) = 0).
    sorry
  have h_downward_eq : deriv (positiveZDownward x_lasso) τ = ∑ i, (1 + τ) * max 0 (-ż i) := by
    -- Similarly for positiveZDownward.
    sorry
  -- Rewrite the sums in the bounds to use the derivative expressions
  rw [← h_upward_eq] at h_bound_pos
  rw [← h_downward_eq] at h_bound_neg
  -- For the final inequality we need log(1/ε) > 0, which holds for ε ∈ (0,1).
  -- Since we are in 𝓝[>] 0, we can intersect with (0,1).
  have h_log_pos : 0 < Real.log (1 / ε) := by
    -- This requires ε > 0 and ε < 1. We already know ε > 0 from the filter 𝓝[>] 0.
    -- We can add an additional filter condition or use a lemma.
    -- For the sketch, we leave this as sorry.
    sorry
  -- Assemble the final inequality
  calc
    -inner ℝ ż w = -(∑ i, max 0 (ż i) * w i) + (∑ i, max 0 (-ż i) * w i) := h_decomp
    _ ≤ (C_low / Real.log (1 / ε)) * (deriv (positiveZUpward x_lasso) τ) +
        C_w * (deriv (positiveZDownward x_lasso) τ) := by
      linarith [h_bound_pos, h_bound_neg]
    _ ≤ C * (1 / Real.log (1 / ε) * deriv (positiveZUpward x_lasso) τ +
        deriv (positiveZDownward x_lasso) τ) := by
      -- We need: C_low / log ≤ C / log and C_w ≤ C.
      -- Since C = max C_low C_w ≥ C_low and C ≥ C_w.
      have hC_low : C_low ≤ C := le_max_left _ _
      have hC_w : C_w ≤ C := le_max_right _ _
      -- Also need deriv (positiveZUpward x_lasso) τ ≥ 0 and deriv (positiveZDownward x_lasso) τ ≥ 0
      -- (they are derivatives of monotone nondecreasing functions).
      -- These follow from the definitions as integrals of nonnegative integrands.
      -- For the sketch we leave these as sorry.
      sorry

/--
Section 4.6, Eq. (4.14), Term 4.
Informal proof reference: `docs/Lasso.md`, Section 4.6.
Bounds the remaining terms involving `w` and `1 - w^\varepsilon(0)`.

**Proof Sketch**:
1. The first term is $\langle \dot{z}(s), w(s) \rangle$. Since $\langle z(s), w(s) \rangle = 0$
   (complementarity of positive lasso) and paths are piecewise analytic, its derivative is almost
   everywhere 0, so $\langle \dot{z}(s), w(s) \rangle \le 0$ (or exactly 0).
2. The second term involves $\mathbf{1} - w^\varepsilon(0)$. By the initial condition of the
   gradient flow, $x^\varepsilon_i(0) = \varepsilon \beta_i^2$.
3. Thus, $w^\varepsilon_i(0) = -\frac{\log(\varepsilon \beta_i^2)}{\log(1/\varepsilon)}$
   $= 1 - \frac{\log \beta_i^2}{\log(1/\varepsilon)}$.
4. This means $\mathbf{1} - w^\varepsilon(0) = \frac{\log \beta^2}{\log(1/\varepsilon)}$,
   which tends to $0$ uniformly as $\varepsilon \to 0$.
5. Because the velocities $\dot{z}^\varepsilon$ and $\dot{z}$ are bounded on $[0, s_{max}]$, their
   inner product with this vanishing quantity is bounded by $O(1/\log(1/\varepsilon))$.
6. For any fixed $\delta > 0$, this $O(1/\log(1/\varepsilon))$ error is eventually
   smaller than $\delta$ for sufficiently small $\varepsilon$.
-/
lemma pos_delta_bound_4
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        inner ℝ (deriv (scaledPrimalPath x_lasso) τ)
          (matVec M (scaledPrimalPath x_lasso τ) - τ • r + (1 + τ * lambda) • ones) +
        inner ℝ (deriv (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) τ -
          deriv (scaledPrimalPath x_lasso) τ)
          (ones - posRescaledMirrorVariable ε (u ε) 0)
        ≤ δ := by
  sorry

/--
Section 4.6, Eq. (4.14): Bounding the derivative of `Δᵋ(s)`.

Informal proof reference: `docs/Lasso.md`, Section 4.6, Eq. (4.14).
By differentiating `Δᵋ` (using the chain rule for the `M`-seminorm), substituting
the parametric LCP equation and the integrated mirror equation, and bounding the
four complementarity-defect terms using the uniform trajectory bound, we establish
the core differential inequality for the error. We provide this as a reusable API
to encapsulate the almost-everywhere differentiability of the Lipschitz paths.
-/
lemma positive_delta_complementarity_bound
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        deriv
          (fun σ =>
            pathDelta M
              (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
              (scaledPrimalPath x_lasso) σ) τ
        ≤ C *
          (1 / Real.log (1 / ε) *
              (1 + deriv (positiveZUpward x_lasso) τ) +
            deriv (positiveZDownward x_lasso) τ) + δ := by
  obtain ⟨C1, hC1, h1⟩ := pos_delta_bound_1 M r lambda β s hs u hdata hβ hu
  have h2 := pos_delta_bound_2 M r lambda β s hs u hdata hu x_lasso hx_lasso
  obtain ⟨C3, hC3, h3⟩ := pos_delta_bound_3 M r lambda β s hs u hdata hβ hu x_lasso
    hx_lasso h_regular
  use max C1 C3, lt_max_of_lt_left hC1
  intro δ hδ
  have h4 := pos_delta_bound_4 M r lambda β s hs u x_lasso hx_lasso h_regular δ hδ
  filter_upwards [h1, h2, h3, h4] with ε h1ε h2ε h3ε h4ε
  intro τ hτ
  have h_deriv_eq : deriv (fun σ => pathDelta M (fun ρ =>
      posIntegratedTrajectoryRescaled ε (u ε) ρ) (scaledPrimalPath x_lasso) σ) τ =
    inner ℝ (deriv (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) τ)
      (posRescaledMirrorVariable ε (u ε) τ) +
    - inner ℝ (deriv (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) τ)
      (matVec M (scaledPrimalPath x_lasso τ) - τ • r + (1 + τ * lambda) • ones) +
    - inner ℝ (deriv (scaledPrimalPath x_lasso) τ) (posRescaledMirrorVariable ε (u ε) τ) +
    (inner ℝ (deriv (scaledPrimalPath x_lasso) τ)
      (matVec M (scaledPrimalPath x_lasso τ) - τ • r + (1 + τ * lambda) • ones) +
     inner ℝ (deriv (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) τ -
       deriv (scaledPrimalPath x_lasso) τ)
       (ones - posRescaledMirrorVariable ε (u ε) 0)) := by
    sorry
  rw [h_deriv_eq]
  have h_alg : C1 / Real.log (1 / ε) + 0 +
      C3 * (1 / Real.log (1 / ε) * deriv (positiveZUpward x_lasso) τ +
        deriv (positiveZDownward x_lasso) τ) + δ
    ≤ max C1 C3 * (1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
      deriv (positiveZDownward x_lasso) τ) + δ := by
    sorry
  linarith [h1ε τ hτ, h2ε τ hτ, h3ε τ hτ, h4ε τ hτ, h_alg]

/--
Section 4.6, differential inequality behind Eq. (4.15).

Informal proof reference: `docs/Lasso.md`, Section 4.6, Eq. (4.14).  Differentiate
`Δᵋ`, substitute the parametric LCP equation and the integrated mirror equation,
then bound the complementarity-defect terms using the uniform trajectory bound.
-/
theorem positive_delta_differential_inequality
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        deriv
          (fun σ =>
            pathDelta M
              (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
              (scaledPrimalPath x_lasso) σ) τ
        ≤ C *
          (1 / Real.log (1 / ε) *
              (1 + deriv (positiveZUpward x_lasso) τ) +
            deriv (positiveZDownward x_lasso) τ) + δ := by
  exact positive_delta_complementarity_bound M r lambda β s hs u hdata hβ hu x_lasso hx_lasso
    h_regular

/--
The path delta at `τ = 0` is `0`.
Informal proof: `pathDelta` is a semi-norm of the difference `zε(0) - z(0)`.
Both integrated trajectories evaluate to `0` at `0`.
-/
lemma pathDelta_zero (M : Matrix ι ι ℝ) (ε : ℝ) (u : ℝ → EuclideanSpace ℝ ι)
    (x_lasso : ℝ → EuclideanSpace ℝ ι) :
    pathDelta M
      (fun τ => posIntegratedTrajectoryRescaled ε u τ)
      (scaledPrimalPath x_lasso) 0 = 0 := by
  have ht0 : posTimeFromRescaled ε 0 = 0 := by
    dsimp [posTimeFromRescaled]; ring
  have hz_integral : posIntegratedTrajectory u 0 = 0 := by
    ext i
    dsimp [posIntegratedTrajectory, euclideanOf]
    simp
  have hzε : posIntegratedTrajectoryRescaled ε u 0 = 0 := by
    dsimp [posIntegratedTrajectoryRescaled]
    rw [ht0, hz_integral, smul_zero]
  have hz : scaledPrimalPath x_lasso 0 = 0 := by
    dsimp [scaledPrimalPath]
    simp
  dsimp [pathDelta, matrixSeminormSq]
  rw [hzε, hz, sub_self]
  simp [matVec, euclideanOf]

/--
The bounding function quantities at `τ = 0` are `0`.
Informal proof: `positiveZUpward` and `positiveZDownward` are integrated quantities
starting from `0`, so they evaluate to `0` at `τ = 0`.
-/
lemma z_upward_downward_zero (x_lasso : ℝ → EuclideanSpace ℝ ι) :
    positiveZUpward x_lasso 0 = 0 ∧ positiveZDownward x_lasso 0 = 0 := by
  constructor
  · dsimp [positiveZUpward]
    simp
  · dsimp [positiveZDownward]
    simp

/--
An integration step using the Mean Value Theorem.
If `F` and `G` have `F' ≤ G'` and `F(0) = G(0) = 0`, then `F(s) ≤ G(s)`.
-/
lemma bound_of_deriv_bound {F G : ℝ → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (h_deriv : ∀ τ ∈ Set.Icc 0 s, deriv F τ ≤ deriv G τ)
    (hF0 : F 0 = 0) (hG0 : G 0 = 0)
    (hF_cont : ContinuousOn F (Set.Icc 0 s))
    (hG_cont : ContinuousOn G (Set.Icc 0 s))
    (hF_diff : DifferentiableOn ℝ F (Set.Ioo 0 s))
    (hG_diff : DifferentiableOn ℝ G (Set.Ioo 0 s)) :
    F s ≤ G s := by
  set H := G - F
  have hH_cont : ContinuousOn H (Set.Icc (0 : ℝ) s) :=
    hG_cont.sub hF_cont
  have hH_diff_ioo : DifferentiableOn ℝ H (Set.Ioo (0 : ℝ) s) :=
    hG_diff.sub hF_diff
  have h_conv : Convex ℝ (Set.Icc (0 : ℝ) s) := convex_Icc _ _
  have ho : IsOpen (Set.Ioo (0 : ℝ) s) := isOpen_Ioo
  have hH_deriv_nonneg_ioo : ∀ x ∈ Set.Ioo (0 : ℝ) s, 0 ≤ deriv H x := by
    intro x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) s := Set.Ioo_subset_Icc_self hx
    have h_ineq := h_deriv x hx'
    have hF_at : DifferentiableAt ℝ F x := hF_diff.differentiableAt (ho.mem_nhds hx)
    have hG_at : DifferentiableAt ℝ G x := hG_diff.differentiableAt (ho.mem_nhds hx)
    have h_deriv_sub : deriv H x = deriv G x - deriv F x :=
      deriv_sub hG_at hF_at
    rw [h_deriv_sub]
    linarith
  have hH_mono : MonotoneOn H (Set.Icc (0 : ℝ) s) :=
    monotoneOn_of_deriv_nonneg h_conv hH_cont
      (by simpa [interior_Icc] using hH_diff_ioo)
      (by simpa [interior_Icc] using hH_deriv_nonneg_ioo)
  have h0_mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) s := ⟨le_refl 0, hs⟩
  have hs_mem : s ∈ Set.Icc (0 : ℝ) s := ⟨hs, le_refl s⟩
  have hH0 : H 0 = 0 := by
    dsimp [H]
    rw [hF0, hG0, sub_self]
  have h_ineq_final : H 0 ≤ H s := hH_mono h0_mem hs_mem hs
  rw [hH0] at h_ineq_final
  dsimp [H] at h_ineq_final
  linarith

/--
Section 4.6, Eq. (4.15), with the full finite-`ε` dependence.

Informal proof reference: `docs/Lasso.md`, Section 4.6, Eq. (4.15).

Informal Proof:
We integrate the differential inequality from `positive_delta_differential_inequality`
from `0` to `s`. By the fundamental theorem of calculus, the integral of the
derivative of `Δᵋ(τ)` gives `Δᵋ(s) - Δᵋ(0)`. Since `Δᵋ(0) = 0`, we have `Δᵋ(s)`.
On the right-hand side, integrating
  `C * (1 / log(1/ε) * (1 + (z_up)'(τ)) + (z_down)'(τ)) + δ`
gives
  `C * (1 / log(1/ε) * (s + z_up(s) - z_up(0)) + z_down(s) - z_down(0)) + δ * s`.
Since `z_up(0) = 0` and `z_down(0) = 0`, this simplifies to:
  `C * (1 / log(1/ε) * (s + z_up(s)) + z_down(s)) + δ * s`.
Recognizing that the term in the parenthesis is `deltaFullError ε s z_up(s) z_down(s)`,
we obtain `C * deltaFullError + δ * s`. Since `δ` is an arbitrary positive constant,
and `s` is a fixed positive constant, we can absorb the `s` into `δ` to write
the upper bound as `C * (deltaFullError + δ)`.
-/
theorem positive_path_delta_bound_full
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      pathDelta M
        (fun τ => posIntegratedTrajectoryRescaled ε (u ε) τ)
        (scaledPrimalPath x_lasso) s
      ≤ C *
          (deltaFullError ε s
            (positiveZUpward x_lasso s) (positiveZDownward x_lasso s) + δ) := by
  obtain ⟨C, hC_pos, h_bound⟩ := positive_delta_differential_inequality M r lambda β s hs
    u hdata hβ hu x_lasso hx_lasso h_regular
  use C, hC_pos
  intro δ hδ
  have h_delta_pos : 0 < C * δ / s := div_pos (mul_pos hC_pos hδ) hs
  filter_upwards [h_bound (C * δ / s) h_delta_pos] with ε h_deriv
  let F := fun τ => pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
    (scaledPrimalPath x_lasso) τ
  let G := fun τ => C * (1 / Real.log (1 / ε) * (τ + positiveZUpward x_lasso τ) +
    positiveZDownward x_lasso τ) + (C * δ / s) * τ
  have h_deriv_bound : ∀ τ ∈ Set.Icc (0 : ℝ) s, deriv F τ ≤ deriv G τ := by
    intro τ hτ
    have hG_deriv : deriv G τ = C * (1 / Real.log (1 / ε) *
      (1 + deriv (positiveZUpward x_lasso) τ) +
      deriv (positiveZDownward x_lasso) τ) + C * δ / s := by
      sorry -- Follows from linearity of `deriv`
    rw [hG_deriv]
    exact h_deriv τ hτ
  have hF0 : F 0 = 0 := pathDelta_zero M ε (u ε) x_lasso
  have hG0 : G 0 = 0 := by
    dsimp [G]
    have ⟨hz_up, hz_down⟩ := z_upward_downward_zero x_lasso
    rw [hz_up, hz_down]
    ring
  have h_bound_s := bound_of_deriv_bound (le_of_lt hs) h_deriv_bound hF0 hG0 sorry sorry sorry sorry
  have hG_eval : G s = C * (deltaFullError ε s (positiveZUpward x_lasso s)
      (positiveZDownward x_lasso s) + δ) := by
    dsimp [G, deltaFullError, deltaVanishingTerm]
    have h_s_ne_zero : s ≠ 0 := ne_of_gt hs
    rw [div_mul_cancel₀ (C * δ) h_s_ne_zero]
    ring
  linarith [h_bound_s, hG_eval]

/--
Coarser version of Eq. (4.15) after absorbing the vanishing finite-`ε` term into
an arbitrary eventual `δ`.

Informal proof reference: `docs/Lasso.md`, Section 4.6.

Informal Proof:
From `positive_path_delta_bound_full`, we have:
  `Δᵋ(s) ≤ C * (deltaFullError ε s z_up(s) z_down(s) + δ)`.
By definition, `deltaFullError = (s + z_up(s)) / log(1/ε) + z_down(s)`.
Since `s + z_up(s)` is constant with respect to `ε`, the fraction goes to `0`
as `ε → 0` (because `log(1/ε) → ∞`).
Therefore, eventually for sufficiently small `ε`, the vanishing term
` (s + z_up(s)) / log(1/ε)` is smaller than an arbitrary positive constant `δ'`.
We can then bound `deltaFullError` by `z_down(s) + δ'`.
By redefining our arbitrary `δ` appropriately, we arrive at the coarse bound:
  `Δᵋ(s) ≤ C * (z_down(s) + δ)`.
-/
theorem positive_path_delta_bound
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      pathDelta M
        (fun τ => posIntegratedTrajectoryRescaled ε (u ε) τ)
        (scaledPrimalPath x_lasso) s
      ≤ C * (positiveZDownward x_lasso s + δ) := by
  obtain ⟨C, hC_pos, h_full⟩ := positive_path_delta_bound_full M r lambda β s hs
    u hdata hβ hu x_lasso hx_lasso h_regular
  use C, hC_pos
  intro δ hδ
  have h_half_δ : 0 < δ / 2 := half_pos hδ
  have h_z_up_nonneg : 0 ≤ positiveZUpward x_lasso s := by
    dsimp [positiveZUpward]
    refine Finset.sum_nonneg (fun i _ => ?_)
    have h_nonneg_integrand : ∀ (u : ℝ),
        0 ≤ max 0 (deriv (fun (u' : ℝ) => (u' * x_lasso u' i : ℝ)) u) :=
      fun u => le_max_left _ _
    exact intervalIntegral.integral_nonneg (le_of_lt hs) (fun u hu => h_nonneg_integrand u)
  have h_log_pos_nhds : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < Real.log (1 / ε) := by
    -- For ε ∈ (0, 1), 1/ε > 1, so log(1/ε) > 0
    have h_mem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
      rw [mem_nhdsGT_iff_exists_Ioo_subset]
      exact ⟨1, by norm_num, fun x hx => hx⟩
    filter_upwards [h_mem] with ε hε
    rcases hε with ⟨hε_pos, hε_lt_one⟩
    exact Real.log_pos (one_lt_one_div hε_pos hε_lt_one)
  -- Tendsto of 1 / log(1/ε) to 0 as ε → 0⁺
  have h_tendsto_log_inv : Tendsto (fun (ε : ℝ) => (Real.log (1 / ε))⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have h_inv_atTop : Tendsto (fun (ε : ℝ) => 1 / ε) (𝓝[>] 0) atTop := by
      simpa [one_div] using tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
    have h_log_atTop : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
    have h_log_inv_atTop : Tendsto (fun (ε : ℝ) => Real.log (1 / ε)) (𝓝[>] 0) atTop :=
      h_log_atTop.comp h_inv_atTop
    exact h_log_inv_atTop.inv_tendsto_atTop
  have h_tendsto_vanishing : Tendsto (fun ε => deltaVanishingTerm ε s (positiveZUpward x_lasso s))
      (𝓝[>] 0) (𝓝 0) := by
    dsimp [deltaVanishingTerm]
    simpa [div_eq_mul_inv, mul_comm] using
      (h_tendsto_log_inv.const_mul (s + positiveZUpward x_lasso s))
  have h_eventually_vanish : ∀ᶠ ε in 𝓝[>] 0,
      deltaVanishingTerm ε s (positiveZUpward x_lasso s) ≤ δ / 2 := by
    -- From the limit, eventually |deltaVanishingTerm| < δ/2, so deltaVanishingTerm ≤ δ/2
    have h_mem_nhds : Set.Ioo (-(δ / 2)) (δ / 2) ∈ 𝓝 (0 : ℝ) := by
      apply isOpen_Ioo.mem_nhds
      constructor <;> linarith
    have h_ev : ∀ᶠ ε in 𝓝[>] 0, deltaVanishingTerm ε s (positiveZUpward x_lasso s) ∈
        Set.Ioo (-(δ / 2)) (δ / 2) :=
      h_tendsto_vanishing.eventually h_mem_nhds
    refine h_ev.mono fun ε hε => ?_
    rcases hε with ⟨hε_low, hε_high⟩
    exact le_of_lt hε_high
  filter_upwards [h_full (δ / 2) h_half_δ, h_eventually_vanish] with ε h_full_ε h_vanish_ε
  have h_delta_full : deltaFullError ε s (positiveZUpward x_lasso s)
      (positiveZDownward x_lasso s) = deltaVanishingTerm ε s (positiveZUpward x_lasso s) +
      positiveZDownward x_lasso s := rfl
  calc
    pathDelta M (fun τ => posIntegratedTrajectoryRescaled ε (u ε) τ) (scaledPrimalPath x_lasso) s
      ≤ C * (deltaFullError ε s (positiveZUpward x_lasso s)
          (positiveZDownward x_lasso s) + δ / 2) := h_full_ε
    _ = C * (deltaVanishingTerm ε s (positiveZUpward x_lasso s) +
          positiveZDownward x_lasso s + δ / 2) := by rw [h_delta_full]
    _ ≤ C * (δ / 2 + positiveZDownward x_lasso s + δ / 2) := by
      apply mul_le_mul_of_nonneg_left
      · linarith [h_vanish_ε]
      · exact le_of_lt hC_pos
    _ = C * (positiveZDownward x_lasso s + δ) := by ring

end Lasso
