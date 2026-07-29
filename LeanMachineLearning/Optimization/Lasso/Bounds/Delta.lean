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
    rw [show (r - matVec M (x τ) - lambda • ones) - r +
      lambda • ones + matVec M (x τ) = 0 by abel] at hsum
    exact hsum
  -- Apply FTC: F(t) - F(0) = ∫₀ᵗ 0 = 0, so F(t) = F(0)
  have hconst : F t - F 0 = ∫ _τ in (0:ℝ)..t, (0 : EuclideanSpace ℝ ι) :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hderiv τ)
      intervalIntegrable_const).symm
  simp only [intervalIntegral.integral_zero, sub_eq_zero] at hconst
  -- Compute F(0) and F(t)
  have hF0 : F 0 = entropyMirrorGradient (x 0) := by
    dsimp [F]
    rw [show z 0 = 0 by ext i; simp [z, posIntegratedTrajectory, euclideanOf],
      show matVec M (0 : EuclideanSpace ℝ ι) = 0 by ext i; simp [matVec, euclideanOf]]
    simp
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
  -- Now compute the main equality
  calc
    posRescaledMirrorVariable ε u s - posRescaledMirrorVariable ε u 0
        = (-c • entropyMirrorGradient (x t_s)) -
          (-c • entropyMirrorGradient (x (posTimeFromRescaled ε 0))) := by
      rw [h_mirror s, h_mirror 0]
    _ = (-c • entropyMirrorGradient (x t_s)) - (-c • entropyMirrorGradient (x 0)) := by
      rw [show posTimeFromRescaled ε 0 = 0 by dsimp [posTimeFromRescaled]; ring]
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
      rw [show c * t_s = s by
        dsimp [c, t_s, posTimeFromRescaled]; field_simp [hlog]]
    _ = -s • r + (s * lambda) • ones +
        matVec M (c • (posIntegratedTrajectory u) t_s) := by rw [matVec_smul_eq]
    _ = matVec M (posIntegratedTrajectoryRescaled ε u s) - s • r + (s * lambda) • ones := by
      rw [show posIntegratedTrajectoryRescaled ε u s = c • (posIntegratedTrajectory u) t_s from by
        dsimp [posIntegratedTrajectoryRescaled, c, t_s]]
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
  rw [show posRescaledMirrorVariable ε u s = posRescaledMirrorVariable ε u 0 +
    (posRescaledMirrorVariable ε u s - posRescaledMirrorVariable ε u 0) by abel,
    posRescaledMirrorVariable_sub_eq_integral M r lambda ε β u hu hu_pos hM s hlog]
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
  set t_ετ := posTimeFromRescaled ε τ
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
  rw [show c • ((Real.log (1 / ε) / 4) • posEffectiveParameter u_eps t_ετ) =
      posEffectiveParameter u_eps t_ετ by
    rw [smul_smul]; dsimp [c]; field_simp [h_log_ne_zero]; simp] at h_smul
  simpa [posIntegratedTrajectoryRescaled, c, t_ετ] using h_smul

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
  set C := max 1 (Fintype.card ι : ℝ)
  refine ⟨C, lt_max_of_lt_left (by norm_num), ?_⟩
  -- Restrict to ε ∈ (0, 1/2), where log(1/ε) > 0
  filter_upwards [by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨1/2, by norm_num, fun x hx => hx⟩] with ε hε
  rcases hε with ⟨hε_pos, hε_lt_half⟩
  have h_log_pos : 0 < Real.log (1 / ε) :=
    Real.log_pos (one_lt_one_div hε_pos (by linarith : ε < 1))
  intro τ hτ
  rw [(posIntegratedTrajectoryRescaled_hasDerivAt ε (u ε) τ
    (hu ε hε_pos).cont_diff.continuous (ne_of_gt h_log_pos)).deriv]
  set x := posEffectiveParameter (u ε) (posTimeFromRescaled ε τ)
  have hx_nonneg : ∀ i, 0 ≤ x i :=
    posEffectiveParameter_nonnegative (u ε) (posTimeFromRescaled ε τ)
  -- Expand the inner product: ⟨x, w⟩ where w_i = -log(x_i)/log(1/ε)
  have h_inner_eq : inner ℝ x (posRescaledMirrorVariable ε (u ε) τ) =
      (1 / Real.log (1 / ε)) * (∑ i : ι, (-(x i) * Real.log (x i))) := by
    rw [PiLp.inner_apply]
    simp_rw [Real.inner_apply]
    simp_rw [show ∀ i, (posRescaledMirrorVariable ε (u ε) τ) i =
      -Real.log (x i) / Real.log (1 / ε) from fun _ => rfl]
    calc
      ∑ i : ι, x i * (-Real.log (x i) / Real.log (1 / ε)) =
          ∑ i : ι, (-(x i) * Real.log (x i)) / Real.log (1 / ε) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      _ = (∑ i : ι, (-(x i) * Real.log (x i))) / Real.log (1 / ε) := by rw [Finset.sum_div]
      _ = (1 / Real.log (1 / ε)) * (∑ i : ι, (-(x i) * Real.log (x i))) := by ring
  rw [h_inner_eq]
  have h_sum_bound : (∑ i : ι, (-(x i) * Real.log (x i))) ≤ C := by
    calc
      (∑ i : ι, (-(x i) * Real.log (x i))) ≤ (∑ i : ι, (1 : ℝ)) :=
        Finset.sum_le_sum (fun i _ => neg_mul_log_le_one (x i) (hx_nonneg i))
      _ = (Fintype.card ι : ℝ) := by simp
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
  rw [PiLp.inner_apply]; simp_rw [Real.inner_apply]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hx i) (hw i))

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
      ext i; simp [lcpQ, parametricLcpQ, scaledPrimalPath, euclideanOf]; field_simp [hτ_ne]; ring
    _ = ((-τ) • r + (1 + τ * lambda) • ones) + matVec M (scaledPrimalPath x_lasso τ) := by
      ext i; simp [parametricLcpQ, ones, euclideanOf]; ring
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
  intro τ hτ
  rcases hτ with ⟨hτ0, _⟩
  rw [(posIntegratedTrajectoryRescaled_hasDerivAt ε (u ε) τ
    (hu ε hε_pos).cont_diff.continuous
    (ne_of_gt (Real.log_pos (one_lt_one_div hε_pos (by linarith))))).deriv]
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
    have hτ_pos : 0 < τ := lt_of_le_of_ne hτ0 (Ne.symm hτ_zero)
    rcases (pos_lasso_is_lcp M r lambda τ (x_lasso τ) hdata.psd.symm hdata.psd).mp
      (hx_lasso τ hτ_pos) with
      ⟨v, hv_eq, hv_nonneg, hx_lasso_nonneg, hvx_zero⟩
    have h_nonneg : 0 ≤ inner ℝ x (τ • v) :=
      inner_nonneg_of_nonneg x (τ • v) hx_nonneg
        (fun i => by simpa [PiLp.smul_apply] using mul_nonneg (by linarith) (hv_nonneg i))
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
-- Decompose -⟨x, y⟩ into positive and negative parts of x:
--   -⟨x, y⟩ = -(Σ_i max(0, x_i)·y_i) + (Σ_i max(0, -x_i)·y_i)
-- This uses the identity a = max(0,a) - max(0,-a) for each coordinate.
private lemma inner_decomp_pos_neg {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℝ ι) :
    -inner ℝ x y = -(∑ i, max 0 (x i) * y i) + (∑ i, max 0 (-(x i)) * y i) := by
  rw [PiLp.inner_apply]
  simp_rw [Real.inner_apply]
  have h_sum_eq : (∑ i : ι, x i * y i) =
      (∑ i : ι, max 0 (x i) * y i) - (∑ i : ι, max 0 (-(x i)) * y i) := by
    calc
      (∑ i : ι, x i * y i) = (∑ i : ι, (max 0 (x i) - max 0 (-(x i))) * y i) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        by_cases hpos : 0 ≤ x i
        · have hmax1 : max 0 (x i) = x i := max_eq_right hpos
          have hmax2 : max 0 (-(x i)) = 0 := max_eq_left (by linarith)
          simp [hmax1, hmax2]
        · have hmax1 : max 0 (x i) = 0 := max_eq_left (by linarith)
          have hmax2 : max 0 (-(x i)) = -(x i) := max_eq_right (by linarith)
          simp [hmax1, hmax2]
      _ = (∑ i : ι, (max 0 (x i) * y i - max 0 (-(x i)) * y i)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      _ = (∑ i : ι, max 0 (x i) * y i) - (∑ i : ι, max 0 (-(x i)) * y i) := by
        rw [Finset.sum_sub_distrib]
  rw [h_sum_eq]
  ring

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
    -- The existing theorem `pos_trajectory_uniform_bound` in MirrorFlow.lean
    -- (Proposition 4.1) gives a uniform norm bound ‖xᵋ(t)‖ ≤ C under the
    -- additional hypothesis `hu_pos` that the effective parameter never vanishes.
    -- This positivity follows from hβ (NonzeroCoordinates β) and the gradient
    -- flow ODE: u_i'(t) = -2 u_i(t) * ((M x(t))_i - r_i + λ), a linear ODE
    -- whose solution u_i(t) = u_i(0) exp(∫₀ᵗ A_i) never crosses zero when
    -- u_i(0) = √ε β_i ≠ 0.  The formal lemma is not yet proved.
    have hu_pos : ∀ ε > 0, ∀ t i, posEffectiveParameter (u ε) t i ≠ 0 := by
      intro ε hε t i
      have hM_symm : M.IsSymm := hdata.psd.symm
      have hflow := hu ε hε
      set x := fun τ => posEffectiveParameter (u ε) τ with hx_def
      -- Initial value x(0) = ε • β², so x_i(0) = ε * β_i² ≠ 0
      have hx0 : x 0 = ε • coordinateSquare β := by
        change posEffectiveParameter (u ε) 0 = _
        rw [posEffectiveParameter_zero_eq_smul_coordinateSquare M r lambda ε β (u ε)
          hflow (by linarith)]
      have hx0_i : (x 0) i = ε * (β i * β i) := by
        rw [hx0]; simp [coordinateSquare, euclideanOf]
      have hx0_ne_zero : (x 0) i ≠ 0 := by
        rw [hx0_i]
        have hβ_sq_ne_zero : β i * β i ≠ 0 := mul_ne_zero (hβ i) (hβ i)
        exact mul_ne_zero (by linarith) hβ_sq_ne_zero
      -- ODE for x(t) from the gradient flow
      have hx_ode_all := pos_effective_parameter_hasDerivAt M r lambda ε β (u ε) hflow hM_symm
      have hx_ode_t := hx_ode_all t
      -- Linear isomorphism to pull back componentwise derivatives
      let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) :=
        (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv
      have h_pi : HasDerivAt (fun τ => e (x τ))
          (e (positiveEffectiveVectorField M r lambda (x t))) t :=
        e.hasFDerivAt.comp_hasDerivAt t hx_ode_t
      have hxi_deriv : HasDerivAt (fun τ => (x τ) i)
          (-4 * (x t) i * ((matVec M (x t)) i - r i + lambda)) t := by
        have h := hasDerivAt_pi.1 h_pi i
        simpa [e, positiveEffectiveVectorField, euclideanOf] using h
      -- Define a_i(τ) = -4 * ((M x(τ))_i - r_i + λ), so that x_i'(τ) = a_i(τ) * x_i(τ)
      set a_i := fun (τ : ℝ) => -4 * ((matVec M (x τ)) i - r i + lambda) with ha_def
      have hxi_deriv' : HasDerivAt (fun τ => (x τ) i) (a_i t * (x t) i) t := by
        have h_eq : -4 * (x t) i * ((matVec M (x t)) i - r i + lambda) = a_i t * (x t) i := by
          dsimp [a_i]
          let x_i : ℝ := (x t) i
          let M_i : ℝ := (matVec M (x t)) i
          let r_i : ℝ := r i
          let lam : ℝ := lambda
          change -4 * x_i * (M_i - r_i + lam) = -4 * (M_i - r_i + lam) * x_i
          ring
        exact h_eq ▸ hxi_deriv
      -- Componentwise ODE at any time τ
      have hxi_deriv_at (τ : ℝ) : HasDerivAt (fun τ => (x τ) i) (a_i τ * (x τ) i) τ := by
        have hx_ode := hx_ode_all τ
        have h_pi' : HasDerivAt (fun τ => e (x τ))
            (e (positiveEffectiveVectorField M r lambda (x τ))) τ :=
          e.hasFDerivAt.comp_hasDerivAt τ hx_ode
        have h := hasDerivAt_pi.1 h_pi' i
        have h_eq : (e (positiveEffectiveVectorField M r lambda (x τ))) i = a_i τ * (x τ) i := by
          dsimp [e, positiveEffectiveVectorField, euclideanOf, a_i]
          let x_i : ℝ := (x τ) i
          let M_i : ℝ := (matVec M (x τ)) i
          let r_i : ℝ := r i
          let lam : ℝ := lambda
          change -4 * x_i * (M_i - r_i + lam) = -4 * (M_i - r_i + lam) * x_i
          ring
        exact h_eq ▸ h
      -- a_i is continuous (x is C^1, matVec is linear)
      have ha_cont : Continuous a_i := by
        dsimp [a_i]
        have hx_cont (j : ι) : Continuous (fun τ => (x τ) j) := by
          change Continuous (fun τ => e (u ε τ) j * e (u ε τ) j)
          have h1 : Continuous (fun τ => e (u ε τ)) := e.continuous.comp hflow.cont_diff.continuous
          have huj : Continuous (fun τ => e (u ε τ) j) := (continuous_apply j).comp h1
          exact huj.mul huj
        have h_matVec : Continuous (fun τ => (matVec M (x τ)) i) := by
          dsimp [matVec, euclideanOf]
          apply continuous_finsetSum
          intro j _
          exact continuous_const.mul (hx_cont j)
        exact h_matVec.sub continuous_const |>.add continuous_const |>.const_mul (-4)
      -- Integrating factor: I(τ) = ∫₀^τ a_i(s) ds, E(τ) = exp(-I(τ))
      have h_int_deriv (τ : ℝ) : HasDerivAt (fun τ => ∫ s in (0:ℝ)..τ, a_i s) (a_i τ) τ := by
        apply intervalIntegral.integral_hasDerivAt_right
          (ha_cont.intervalIntegrable _ _) (ha_cont.stronglyMeasurableAtFilter _ _)
          ha_cont.continuousAt
      set I := fun (τ : ℝ) => ∫ s in (0:ℝ)..τ, a_i s with hI_def
      have hI_deriv (τ : ℝ) : HasDerivAt I (a_i τ) τ := h_int_deriv τ
      have hE_deriv (τ : ℝ) : HasDerivAt (fun τ => Real.exp (-I τ))
          (-a_i τ * Real.exp (-I τ)) τ := by
        have h_neg_I : HasDerivAt (-I) (-a_i τ) τ := (hI_deriv τ).neg
        have h_exp : HasDerivAt (fun x => Real.exp ((-I) x)) (Real.exp ((-I) τ) * -a_i τ) τ := h_neg_I.exp
        have h_eq2 : Real.exp ((-I) τ) * -a_i τ = -a_i τ * Real.exp (-I τ) := mul_comm _ _
        exact h_eq2 ▸ h_exp
      set E := fun (τ : ℝ) => Real.exp (-I τ) with hE_def
      have hE_pos : ∀ τ, 0 < E τ := by
        intro τ; dsimp [E]; exact Real.exp_pos _
      -- Product rule: (x_i * E)' = x_i' * E + x_i * E' = (a_i * x_i) * E + x_i * (-a_i * E) = 0
      have h_prod_deriv (τ : ℝ) : HasDerivAt (fun τ => (x τ) i * E τ) 0 τ := by
        have hxi := hxi_deriv_at τ
        have hE := hE_deriv τ
        have h_mul := HasDerivAt.mul hxi hE
        have h_eq : a_i τ * (x τ) i * E τ + (x τ) i * (-a_i τ * Real.exp (-I τ)) = 0 := by
          dsimp [E]
          let a : ℝ := a_i τ
          let x_i : ℝ := (x τ) i
          let E_t : ℝ := Real.exp (-I τ)
          change a * x_i * E_t + x_i * (-a * E_t) = 0
          ring
        exact h_eq ▸ h_mul
      -- Zero derivative everywhere implies constant
      have h_prod_const : ∀ τ, (x τ) i * E τ = (x 0) i * E 0 := by
        set f := fun (τ : ℝ) => (x τ) i * E τ with hf_def
        have h_diff : Differentiable ℝ f := fun τ => (h_prod_deriv τ).differentiableAt
        have h_deriv_eq_zero : ∀ τ, deriv f τ = 0 := fun τ => (h_prod_deriv τ).deriv
        have h_const := is_const_of_deriv_eq_zero h_diff h_deriv_eq_zero
        intro τ
        exact h_const τ 0
      have hE0 : E 0 = 1 := by
        dsimp [E, I]; simp
      -- Conclusion: (x t) i * E t = (x 0) i ≠ 0, and E t > 0, so (x t) i ≠ 0
      have hx_t_ne_zero : (x t) i ≠ 0 := by
        have h_eq := h_prod_const t
        rw [hE0] at h_eq
        intro hzero
        have h_symm : (x 0) i = 0 := by
          calc (x 0) i = (x 0) i * 1 := by ring
          _ = (x t) i * E t := h_eq.symm
          _ = 0 * E t := by rw [hzero]
          _ = 0 := by ring
        exact hx0_ne_zero h_symm
      simpa [hx_def] using hx_t_ne_zero
    -- Apply the uniform trajectory bound (Proposition 4.1 from the paper).
    obtain ⟨C, ε₀, hCpos, hε₀pos, hbound⟩ :=
      pos_trajectory_uniform_bound M r lambda β u hdata hβ hu hu_pos
    -- Shrink ε₀ to also be ≤ 1, so that log(1/ε) ≥ 0 for the rescaled time.
    set ε₁ := min ε₀ 1
    have hε₁pos : 0 < ε₁ := lt_min hε₀pos one_pos
    -- The interval (0, ε₁) is in the right-neighborhood filter 𝓝[>] 0.
    have h_mem : Set.Ioo (0 : ℝ) ε₁ ∈ 𝓝[>] (0 : ℝ) := by
      rw [mem_nhdsGT_iff_exists_Ioo_subset]
      exact ⟨ε₁, hε₁pos, fun x hx => hx⟩
    refine ⟨C, hCpos, ?_⟩
    filter_upwards [h_mem] with ε hε
    have hε_pos : 0 < ε := hε.1
    have hε_lt₁ : ε < ε₁ := hε.2
    have hε_le₀ : ε ≤ ε₀ := by
      have hε₁_le₀ : ε₁ ≤ ε₀ := min_le_left _ _
      linarith
    have hε_le_one : ε ≤ 1 := by
      have hε₁_le_one : ε₁ ≤ 1 := min_le_right _ _
      linarith
    intro τ hτ
    rcases hτ with ⟨hτ0, hτs⟩
    intro i
    -- The rescaled time t := (τ/4)·log(1/ε) is nonnegative.
    set t := posTimeFromRescaled ε τ with ht_def
    have ht_nonneg : 0 ≤ t := by
      rw [ht_def, posTimeFromRescaled]
      have h_one_div : 1 ≤ 1 / ε := (one_le_div hε_pos).mpr hε_le_one
      have h_log_nonneg : 0 ≤ Real.log (1 / ε) := Real.log_nonneg h_one_div
      have h_tau_div : 0 ≤ τ / 4 := div_nonneg hτ0 (by norm_num)
      exact mul_nonneg h_tau_div h_log_nonneg
    -- The uniform norm bound from Proposition 4.1.
    have h_norm_bound : ‖posEffectiveParameter (u ε) t‖ ≤ C :=
      hbound ε hε_pos hε_le₀ t ht_nonneg
    -- Each coordinate is nonnegative (it's a square).
    have hx_nonneg : 0 ≤ posEffectiveParameter (u ε) t i :=
      posEffectiveParameter_nonnegative (u ε) t i
    -- Bound the coordinate by the norm: ‖x_i‖ ≤ ‖x‖ ≤ C.
    have h_coord_norm : ‖posEffectiveParameter (u ε) t i‖ ≤ C := by
      calc
        ‖posEffectiveParameter (u ε) t i‖ ≤ ‖posEffectiveParameter (u ε) t‖ :=
          PiLp.norm_apply_le (posEffectiveParameter (u ε) t) i
        _ ≤ C := h_norm_bound
    -- For a nonnegative real, the norm equals the value itself.
    have h_coord : posEffectiveParameter (u ε) t i ≤ C := by
      have h_norm_eq_abs : ‖posEffectiveParameter (u ε) t i‖ =
          |posEffectiveParameter (u ε) t i| := by rw [Real.norm_eq_abs]
      have h_abs_eq_val : |posEffectiveParameter (u ε) t i| =
          posEffectiveParameter (u ε) t i := abs_of_nonneg hx_nonneg
      rw [h_norm_eq_abs, h_abs_eq_val] at h_coord_norm
      exact h_coord_norm
    simpa [ht_def]
  rcases h_uniform_bound with ⟨X, hX_pos, hX_ev⟩
  -- From the trajectory bound and the definition wᵋ_i = -log(xᵋ_i)/log(1/ε),
  -- we obtain a lower bound: wᵋ_i(τ) ≥ -C_low / log(1/ε).
  -- Since xᵋ_i ≤ X, we have log(xᵋ_i) ≤ max(0, log X), so
  -- -log(xᵋ_i) ≥ -max(0, log X), giving the bound.
  have h_w_lower : ∃ C_low > 0, ∀ᶠ ε in 𝓝[>] 0, ∀ τ ∈ Set.Icc (0 : ℝ) s,
      ∀ i, -C_low / Real.log (1 / ε) ≤ posRescaledMirrorVariable ε (u ε) τ i := by
    /-
    INFORMAL PROOF (docs/Lasso.md, Section 4.3):
    By the uniform trajectory bound, all coordinates of the effective parameter xᵋ_i
    are bounded above by some uniform constant X > 0.
    Since wᵋ_i = -log(xᵋ_i) / log(1/ε), the upper bound xᵋ_i ≤ X implies
    a lower bound on -log(xᵋ_i) ≥ -max(0, log X).
    Dividing by log(1/ε) > 0 gives wᵋ_i ≥ -C_low / log(1/ε) where C_low = max(0, log X).
    -/
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
    /-
    INFORMAL PROOF (docs/Lasso.md, Section 4.3):
    The integrated mirror equation expresses wᵋ(τ) as:
      wᵋ(τ) = wᵋ(0) - τ·r + M·zᵋ(τ) + τ·λ·𝟙
    Since xᵋ(τ) is bounded uniformly by X on [0, s], its integral zᵋ(τ) = ∫₀^τ xᵋ(t) dt
    is bounded in norm by τ * X.
    Since wᵋ(0) converges to 𝟙, it is also bounded.
    Thus, by the triangle inequality, the norm of wᵋ(τ) is bounded by C_w * (1 + τ)
    for some constant C_w combining the bounds of the individual terms.
    -/
    sorry
  rcases h_w_upper with ⟨C_w, hC_w_pos, hW_ev⟩
  -- Combine the constants
  set C := max C_low C_w
  refine ⟨C, lt_max_of_lt_left hC_low_pos, ?_⟩
  -- Intersect the three "eventually" filters, also restrict to ε ∈ (0,1) so that log(1/ε) > 0
  filter_upwards [hX_ev, hW_low_ev, hW_ev, by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨1, by norm_num, fun x hx => hx⟩] with ε hXε hW_low_ε hW_ε hε_one
  intro τ hτ
  rcases hτ with ⟨hτ0, hτs⟩
  -- Notation for the derivative and the dual variable
  set zDot := deriv (scaledPrimalPath x_lasso) τ
  set w := posRescaledMirrorVariable ε (u ε) τ
  -- For the final inequality we need log(1/ε) > 0, which holds for ε ∈ (0,1).
  have h_log_pos : 0 < Real.log (1 / ε) := by
    rcases hε_one with ⟨hε_pos, hε_lt_one⟩
    have h_one_div_gt_one : 1 < 1 / ε := one_lt_one_div hε_pos hε_lt_one
    exact Real.log_pos h_one_div_gt_one
  -- Now bound each part using the bounds on w.
  -- For the positive part: since w_i ≥ -C_low / log(1/ε) and max(0, zDot_i) ≥ 0,
  --   -(max(0, zDot_i)) * w_i ≤ max(0, zDot_i) * C_low / log(1/ε)
  -- For the negative part: since |w_i| ≤ C_w * (1+τ) and max(0, -zDot_i) ≥ 0,
  --   max(0, -zDot_i) * w_i ≤ max(0, -zDot_i) * C_w * (1+τ)
  have h_bound_pos : -(∑ i, max 0 (zDot i) * w i) ≤
      (C_low / Real.log (1 / ε)) * (∑ i, max 0 (zDot i)) := by
    calc
      -(∑ i, max 0 (zDot i) * w i) = ∑ i, (-(max 0 (zDot i)) * w i) := by
        simp [Finset.sum_neg_distrib]
      _ ≤ ∑ i, (max 0 (zDot i) * (C_low / Real.log (1 / ε))) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        by_cases hzDot : 0 ≤ zDot i
        · have hmax : max 0 (zDot i) = zDot i := max_eq_right hzDot
          rw [hmax]
          have hw_low : -C_low / Real.log (1 / ε) ≤ w i := by
            simpa [w] using hW_low_ε τ ⟨hτ0, hτs⟩ i
          have hneg_w : -w i ≤ C_low / Real.log (1 / ε) := by
            simpa [neg_div] using neg_le_neg hw_low
          calc
            -(zDot i) * w i = zDot i * (-w i) := by ring
            _ ≤ zDot i * (C_low / Real.log (1 / ε)) :=
              mul_le_mul_of_nonneg_left hneg_w hzDot
        · have hmax : max 0 (zDot i) = 0 := max_eq_left (by linarith)
          simp [hmax]
      _ = (C_low / Real.log (1 / ε)) * (∑ i, max 0 (zDot i)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
  have h_bound_neg : (∑ i, max 0 (-zDot i) * w i) ≤
      C_w * (∑ i, (1 + τ) * max 0 (-zDot i)) := by
    calc
      (∑ i, max 0 (-zDot i) * w i) ≤ (∑ i, max 0 (-zDot i) * (C_w * (1 + τ))) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        have hw_bound := hW_ε τ ⟨hτ0, hτs⟩ i
        have hw_le : w i ≤ C_w * (1 + τ) :=
          (abs_le.mp (by simpa [w] using hw_bound)).2
        have h_nonneg : 0 ≤ max 0 (-zDot i) := le_max_left _ _
        exact mul_le_mul_of_nonneg_left hw_le h_nonneg
      _ = C_w * (∑ i, (1 + τ) * max 0 (-zDot i)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
  -- Relate the sums to derivatives of positiveZUpward and positiveZDownward.
  -- By the Fundamental Theorem of Calculus:
  --   deriv (positiveZUpward x_lasso) τ = ∑_i max 0 (deriv (scaledPrimalPath x_lasso) τ i)
  --   deriv (positiveZDownward x_lasso) τ
  --     = ∑_i (1+τ) * max 0 (-deriv (scaledPrimalPath x_lasso) τ i)
  have h_upward_eq : deriv (positiveZUpward x_lasso) τ = ∑ i, max 0 (zDot i) := by
    /-
    INFORMAL PROOF (docs/Lasso.md, Section 4.6):
    The positiveZUpward and positiveZDownward functions are defined as the integrals
    of the positive and negative variations of the scaled primal path, respectively.
    By the Fundamental Theorem of Calculus (specifically, Lebesgue differentiation theorem
    for Lipschitz paths), the derivative of the integral recovers the integrand almost everywhere.
    Thus, differentiating positiveZUpward with respect to τ gives ∑_i max(0, zDot_i).
    -/
    sorry
  have h_downward_eq : deriv (positiveZDownward x_lasso) τ = ∑ i, (1 + τ) * max 0 (-zDot i) := by
    /-
    INFORMAL PROOF (docs/Lasso.md, Section 4.6):
    Similarly, differentiating positiveZDownward with respect to τ yields
    ∑_i (1 + τ) * max(0, -zDot_i), since it is the integral of (1+τ) * (x_lasso' ₋).
    -/
    sorry
  -- Rewrite the sums in the bounds to use the derivative expressions
  rw [← h_upward_eq] at h_bound_pos
  rw [← h_downward_eq] at h_bound_neg
  -- Assemble the final inequality
  calc
    -inner ℝ zDot w = -(∑ i, max 0 (zDot i) * w i) + (∑ i, max 0 (-zDot i) * w i) :=
      inner_decomp_pos_neg zDot w
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
    /-
    INFORMAL PROOF (docs/Lasso.md, Section 4.6, Eq 4.14):
    This algebraic identity differentiates the seminorm pathDelta Δᵋ(τ) = 1/2 ‖zᵋ(τ) - z(τ)‖_M^2.
    Using the chain rule, the derivative is inner(zᵋ' - z', M(zᵋ - z)).
    We substitute M zᵋ = wᵋ - wᵋ(0) + τ·r - τ·λ·𝟙 from the integrated mirror flow equation,
    and M z = -z(0) + τ·r - τ·λ·𝟙 + w(τ) from the exact Lasso path LCP.
    Expanding the inner product and collecting terms grouping the primal path derivatives
    and LCP complementarity errors gives exactly the four terms on the RHS.
    -/
    sorry
  rw [h_deriv_eq]
  have h_alg : C1 / Real.log (1 / ε) + 0 +
      C3 * (1 / Real.log (1 / ε) * deriv (positiveZUpward x_lasso) τ +
        deriv (positiveZDownward x_lasso) τ) + δ
    ≤ max C1 C3 * (1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
      deriv (positiveZDownward x_lasso) τ) + δ := by
    /-
    INFORMAL PROOF (docs/Lasso.md, Section 4.6):
    This is a purely algebraic inequality combining the bounds from the four complementarity terms.
    Since C1 and C3 are positive, C1 / log(1/ε) ≤ max(C1, C3) / log(1/ε).
    Similarly, C3 * (1/log(1/ε) * z_up' + z_down') ≤ max(C1, C3) * (1/log(1/ε) * z_up' + z_down').
    Factoring out max(C1, C3) and adding the delta term matches the target bound.
    -/
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
  have hz_int : posIntegratedTrajectory u 0 = 0 := by
    ext i; simp [posIntegratedTrajectory, euclideanOf]
  simp [pathDelta, matrixSeminormSq, posIntegratedTrajectoryRescaled, scaledPrimalPath,
    ht0, hz_int, matVec, euclideanOf]

/--
The bounding function quantities at `τ = 0` are `0`.
Informal proof: `positiveZUpward` and `positiveZDownward` are integrated quantities
starting from `0`, so they evaluate to `0` at `τ = 0`.
-/
lemma z_upward_downward_zero (x_lasso : ℝ → EuclideanSpace ℝ ι) :
    positiveZUpward x_lasso 0 = 0 ∧ positiveZDownward x_lasso 0 = 0 := by
  simp [positiveZUpward, positiveZDownward]

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
  have hH_deriv_nonneg_ioo : ∀ x ∈ Set.Ioo (0 : ℝ) s, 0 ≤ deriv H x := by
    intro x hx
    have hF_at : DifferentiableAt ℝ F x := hF_diff.differentiableAt (isOpen_Ioo.mem_nhds hx)
    have hG_at : DifferentiableAt ℝ G x := hG_diff.differentiableAt (isOpen_Ioo.mem_nhds hx)
    rw [deriv_sub hG_at hF_at]
    linarith [h_deriv x (Set.Ioo_subset_Icc_self hx)]
  have hH_mono : MonotoneOn H (Set.Icc (0 : ℝ) s) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _) (hG_cont.sub hF_cont)
      (by simpa [interior_Icc] using hG_diff.sub hF_diff)
      (by simpa [interior_Icc] using hH_deriv_nonneg_ioo)
  have hH0 : H 0 = 0 := by
    dsimp [H]; rw [hF0, hG0, sub_self]
  have h_ineq : H 0 ≤ H s := hH_mono ⟨le_refl 0, hs⟩ ⟨hs, le_refl s⟩ hs
  rw [hH0] at h_ineq
  dsimp [H] at h_ineq
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
      /-
      INFORMAL PROOF:
      This follows from the linearity of the derivative operator `deriv`.
      Since G(τ) = C * (1 / log(1/ε) * (τ + z_up(τ)) + z_down(τ)) + (C * δ / s) * τ,
      we have G'(τ) = C * (1 / log(1/ε) * (1 + z_up'(τ)) + z_down'(τ)) + C * δ / s.
      -/
      sorry
    rw [hG_deriv]
    exact h_deriv τ hτ
  have hF0 : F 0 = 0 := pathDelta_zero M ε (u ε) x_lasso
  have hG0 : G 0 = 0 := by
    dsimp [G]
    have ⟨hz_up, hz_down⟩ := z_upward_downward_zero x_lasso
    rw [hz_up, hz_down]
    ring
  have hF_cont : ContinuousOn F (Set.Icc 0 s) := sorry
  have hG_cont : ContinuousOn G (Set.Icc 0 s) := sorry
  have hF_diff : DifferentiableOn ℝ F (Set.Ioo 0 s) := sorry
  have hG_diff : DifferentiableOn ℝ G (Set.Ioo 0 s) := sorry
  /-
  INFORMAL PROOF (docs/Lasso.md, Section 4.6):
  We apply the integration lemma bound_of_deriv_bound (Mean Value Theorem).
  The functions F (the path delta) and G (the algebraic upper bound) are 
  differentiable almost everywhere because they are composed of locally Lipschitz 
  integrated trajectories. They are continuous everywhere.
  Applying the integration lemma yields F(s) ≤ G(s).
  -/
  have h_bound_s := bound_of_deriv_bound (le_of_lt hs) h_deriv_bound hF0 hG0 hF_cont hG_cont hF_diff hG_diff
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
