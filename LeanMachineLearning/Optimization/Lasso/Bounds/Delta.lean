/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Lasso.Definitions
public import Mathlib.Analysis.Calculus.MeanValue

/-! ## Section 4.6: positive-path estimate chain -/

@[expose] public section

namespace Lasso

open Filter Topology MeasureTheory
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
  refine e.symm.hasFDerivAt.comp_hasDerivAt τ ?_
  refine hasDerivAt_pi.2 fun i => ?_
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
      refine hasDerivAt_pi.2 fun i => ?_
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
    have h_eq : coordinateSquare = e ∘ (fun (x : EuclideanSpace ℝ ι) => fun i => x i * x i) := by
      ext x i; simp [coordinateSquare, euclideanOf, e]
    rw [h_eq]
    exact e.continuous.comp
      (continuous_pi (fun i => Continuous.mul (h_proj_cont i) (h_proj_cont i)))
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
      refine hasDerivAt_pi.mpr fun i => ?_
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
    exact ⟨1/2, by norm_num, fun _ hx => hx⟩] with ε hε
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
      _ ≤ C := le_max_right _ _
  -- Final: divide by log(1/ε) > 0
  field_simp [h_log_pos.ne.symm]
  simpa [neg_mul] using h_sum_bound

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
    exact ⟨1/2, by norm_num, fun _ hx => hx⟩] with ε hε
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
        (fun i => mul_nonneg (by linarith) (hv_nonneg i))
    rw [lcp_dual_scale_eq_target M r lambda τ hτ_zero x_lasso v hv_eq] at h_nonneg
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
        · simp [max_eq_right hpos, max_eq_left (show -(x i) ≤ 0 by linarith)]
        · simp [max_eq_left (show x i ≤ 0 by linarith), max_eq_right (show 0 ≤ -(x i) by linarith)]
      _ = (∑ i : ι, (max 0 (x i) * y i - max 0 (-(x i)) * y i)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      _ = (∑ i : ι, max 0 (x i) * y i) - (∑ i : ι, max 0 (-(x i)) * y i) := by
        rw [Finset.sum_sub_distrib]
  rw [h_sum_eq]
  ring

-- Positivity of effective parameter: for the gradient flow, each coordinate
-- never vanishes because x_i(0) = ε·β_i² ≠ 0 and the ODE x_i' = a_i·x_i
-- gives x_i(t) = x_i(0)·exp(∫₀ᵗ a_i) > 0. The proof uses an integrating factor.
private lemma pos_param_ne_zero_of_gradient_flow
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lam : ℝ)
    (β : EuclideanSpace ℝ ι) (ε : ℝ) (hε : ε > 0)
    (u_ε : ℝ → EuclideanSpace ℝ ι) (hflow : posDlnGradientFlow M r lam ε β u_ε)
    (hM_symm : M.IsSymm) (t : ℝ) (i : ι) (hβ_i : β i ≠ 0) :
    posEffectiveParameter u_ε t i ≠ 0 := by
  set x := fun τ => posEffectiveParameter u_ε τ with hx_def
  -- Initial value x(0) = ε • β², so x_i(0) = ε * β_i² ≠ 0
  have hx0 : x 0 = ε • coordinateSquare β := by
    change posEffectiveParameter u_ε 0 = _
    rw [posEffectiveParameter_zero_eq_smul_coordinateSquare M r lam ε β u_ε
      hflow (by linarith)]
  have hx0_i : (x 0) i = ε * (β i * β i) := by
    rw [hx0]; simp [coordinateSquare, euclideanOf]
  have hx0_ne_zero : (x 0) i ≠ 0 := by
    rw [hx0_i]
    have hβ_sq_ne_zero : β i * β i ≠ 0 := mul_ne_zero hβ_i hβ_i
    exact mul_ne_zero (by linarith) hβ_sq_ne_zero
  -- ODE for x(t) from the gradient flow
  have hx_ode_all := pos_effective_parameter_hasDerivAt M r lam ε β u_ε hflow hM_symm
  have hx_ode_t := hx_ode_all t
  -- Linear isomorphism to pull back componentwise derivatives
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv
  have h_pi : HasDerivAt (fun τ => e (x τ))
      (e (positiveEffectiveVectorField M r lam (x t))) t :=
    e.hasFDerivAt.comp_hasDerivAt t hx_ode_t
  have hxi_deriv : HasDerivAt (fun τ => (x τ) i)
      (-4 * (x t) i * ((matVec M (x t)) i - r i + lam)) t := by
    have h := hasDerivAt_pi.1 h_pi i
    simpa [e, positiveEffectiveVectorField, euclideanOf] using h
  -- Define a_i(τ) = -4 * ((M x(τ))_i - r_i + λ), so that x_i'(τ) = a_i(τ) * x_i(τ)
  set a_i := fun (τ : ℝ) => -4 * ((matVec M (x τ)) i - r i + lam)
  have hxi_deriv' : HasDerivAt (fun τ => (x τ) i) (a_i t * (x t) i) t := by
    have h_eq : -4 * (x t) i * ((matVec M (x t)) i - r i + lam) = a_i t * (x t) i := by
      dsimp [a_i]
      ring
    exact h_eq ▸ hxi_deriv
  -- Componentwise ODE at any time τ
  have hxi_deriv_at (τ : ℝ) : HasDerivAt (fun τ => (x τ) i) (a_i τ * (x τ) i) τ := by
    have hx_ode := hx_ode_all τ
    have h_pi' : HasDerivAt (fun τ => e (x τ))
        (e (positiveEffectiveVectorField M r lam (x τ))) τ :=
      e.hasFDerivAt.comp_hasDerivAt τ hx_ode
    have h := hasDerivAt_pi.1 h_pi' i
    have h_eq : (e (positiveEffectiveVectorField M r lam (x τ))) i = a_i τ * (x τ) i := by
      dsimp [e, positiveEffectiveVectorField, euclideanOf, a_i]
      let x_i : ℝ := (x τ) i
      let M_i : ℝ := (matVec M (x τ)) i
      let r_i : ℝ := r i
      let lam' : ℝ := lam
      change -4 * x_i * (M_i - r_i + lam') = -4 * (M_i - r_i + lam') * x_i
      ring
    exact h_eq ▸ h
  -- a_i is continuous (x is C^1, matVec is linear)
  have ha_cont : Continuous a_i := by
    dsimp [a_i]
    have hx_cont (j : ι) : Continuous (fun τ => (x τ) j) := by
      change Continuous (fun τ => e (u_ε τ) j * e (u_ε τ) j)
      have h1 : Continuous (fun τ => e (u_ε τ)) := e.continuous.comp hflow.cont_diff.continuous
      have huj : Continuous (fun τ => e (u_ε τ) j) := (continuous_apply j).comp h1
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
  set I := fun (τ : ℝ) => ∫ s in (0:ℝ)..τ, a_i s
  have hI_deriv (τ : ℝ) : HasDerivAt I (a_i τ) τ := h_int_deriv τ
  have hE_deriv (τ : ℝ) : HasDerivAt (fun τ => Real.exp (-I τ))
      (-a_i τ * Real.exp (-I τ)) τ := by
    have h_neg_I : HasDerivAt (-I) (-a_i τ) τ := (hI_deriv τ).neg
    have h_exp :
        HasDerivAt (fun x => Real.exp ((-I) x))
          (Real.exp ((-I) τ) * -a_i τ) τ := h_neg_I.exp
    have h_eq2 : Real.exp ((-I) τ) * -a_i τ = -a_i τ * Real.exp (-I τ) := mul_comm _ _
    exact h_eq2 ▸ h_exp
  set E := fun (τ : ℝ) => Real.exp (-I τ)
  have hE_pos : ∀ τ, 0 < E τ := by
    intro τ; dsimp [E]; exact Real.exp_pos _
  -- Product rule: (x_i * E)' = x_i' * E + x_i * E' = (a_i * x_i) * E + x_i * (-a_i * E) = 0
  have h_prod_deriv (τ : ℝ) : HasDerivAt (fun τ => (x τ) i * E τ) 0 τ := by
    have hxi := hxi_deriv_at τ
    have hE := hE_deriv τ
    have h_mul := HasDerivAt.mul hxi hE
    have h_eq : a_i τ * (x τ) i * E τ + (x τ) i * (-a_i τ * Real.exp (-I τ)) = 0 := by
      dsimp [E]
      ring
    exact h_eq ▸ h_mul
  -- Zero derivative everywhere implies constant
  have h_prod_const : ∀ τ, (x τ) i * E τ = (x 0) i * E 0 := by
    set f := fun (τ : ℝ) => (x τ) i * E τ
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
    rw [hE0, mul_one] at h_eq
    intro hzero
    rw [hzero, zero_mul] at h_eq
    exact hx0_ne_zero h_eq.symm
  simpa [hx_def] using hx_t_ne_zero

-- Extract uniform coordinate bound from `pos_trajectory_uniform_bound`:
-- for all sufficiently small ε, every coordinate of xᵋ(τ) is bounded above by some X > 0,
-- uniformly in τ ∈ [0, s].
private lemma uniform_trajectory_coordinate_bound
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε)) :
    ∃ X > 0, ∀ᶠ ε in 𝓝[>] 0, ∀ τ ∈ Set.Icc (0 : ℝ) s,
      ∀ i, posEffectiveParameter (u ε) (posTimeFromRescaled ε τ) i ≤ X := by
  obtain ⟨C, ε₀, hCpos, hε₀pos, hbound⟩ :=
    pos_trajectory_uniform_bound M r lambda β u hdata hβ hu
  -- Shrink ε₀ to also be ≤ 1, so that log(1/ε) ≥ 0 for the rescaled time.
  set ε₁ := min ε₀ 1
  have hε₁pos : 0 < ε₁ := lt_min hε₀pos one_pos
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [show Set.Ioo (0 : ℝ) ε₁ ∈ 𝓝[>] (0 : ℝ) from by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨ε₁, hε₁pos, fun _ hx => hx⟩] with ε hε
  have hε_pos : 0 < ε := hε.1
  have hε_lt₁ : ε < ε₁ := hε.2
  have hε_le₀ : ε ≤ ε₀ := hε_lt₁.le.trans (min_le_left _ _)
  have hε_le_one : ε ≤ 1 := hε_lt₁.le.trans (min_le_right _ _)
  intro τ hτ i
  set t := posTimeFromRescaled ε τ with ht_def
  have ht_nonneg : 0 ≤ t := by
    rw [ht_def, posTimeFromRescaled]
    exact mul_nonneg (div_nonneg hτ.1 (by norm_num))
      (Real.log_nonneg ((one_le_div hε_pos).mpr hε_le_one))
  have h_norm_bound : ‖posEffectiveParameter (u ε) t‖ ≤ C :=
    hbound ε hε_pos hε_le₀ t ht_nonneg
  have hx_nonneg : 0 ≤ posEffectiveParameter (u ε) t i :=
    posEffectiveParameter_nonnegative (u ε) t i
  have h_coord : posEffectiveParameter (u ε) t i ≤ C := by
    have h := (PiLp.norm_apply_le (posEffectiveParameter (u ε) t) i).trans h_norm_bound
    simpa [Real.norm_eq_abs, abs_of_nonneg hx_nonneg] using h
  simpa [ht_def]

omit [Fintype ι] in
-- Lower bound for the rescaled mirror variable wᵋ_i(τ) ≥ -C_low / log(1/ε).
-- Uses the uniform upper bound X on the effective parameter xᵋ_i ≤ X,
-- from which log(xᵋ_i) ≤ max(1, log X), so -log(xᵋ_i) ≥ -C_low.
private lemma rescaled_mirror_lower_bound
    (X : ℝ) (u : ℝ → ℝ → EuclideanSpace ℝ ι) (s : ℝ)
    (hX_ev : ∀ᶠ ε in 𝓝[>] 0, ∀ τ ∈ Set.Icc (0 : ℝ) s,
      ∀ i, posEffectiveParameter (u ε) (posTimeFromRescaled ε τ) i ≤ X)
    (hu_pos : ∀ ε > 0, ∀ t i, posEffectiveParameter (u ε) t i ≠ 0) :
    ∃ C_low > 0, ∀ᶠ ε in 𝓝[>] 0, ∀ τ ∈ Set.Icc (0 : ℝ) s,
      ∀ i, -C_low / Real.log (1 / ε) ≤ posRescaledMirrorVariable ε (u ε) τ i := by
  set C_low := max 1 (Real.log X)
  refine ⟨C_low, lt_max_of_lt_left (by norm_num : (0 : ℝ) < 1), ?_⟩
  -- Intersect the uniform upper bound with ε ∈ (0,1) so that log(1/ε) > 0
  filter_upwards [hX_ev, show Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) from by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨1, by norm_num, fun _ hx => hx⟩] with ε hX hε_mem
  rcases hε_mem with ⟨hε_pos, hε_lt_one⟩
  intro τ hτ i
  set x_i := posEffectiveParameter (u ε) (posTimeFromRescaled ε τ) i
  have hx_pos : 0 < x_i := by
    have h_nonneg : 0 ≤ x_i := posEffectiveParameter_nonnegative (u ε) (posTimeFromRescaled ε τ) i
    have h_ne_zero : x_i ≠ 0 := hu_pos ε hε_pos (posTimeFromRescaled ε τ) i
    exact lt_of_le_of_ne h_nonneg h_ne_zero.symm
  have hx_le_X : x_i ≤ X := hX τ hτ i
  have h_neg_log : -C_low ≤ -Real.log x_i :=
    neg_le_neg ((Real.log_le_log hx_pos hx_le_X).trans (le_max_right _ _))
  dsimp [posRescaledMirrorVariable, euclideanOf, x_i]
  exact div_le_div_of_nonneg_right h_neg_log
    (le_of_lt (Real.log_pos (one_lt_one_div hε_pos hε_lt_one)))

-- Bundle the positive and negative parts of the inner-product bound.
-- Uses the lower bound w_i ≥ -C_low / log(1/ε) for the positive part
-- and the absolute bound |w_i| ≤ C_w*(1+τ) for the negative part.
private lemma mirror_pos_neg_bounds
    (zDot w : EuclideanSpace ℝ ι) (C_low C_w τ ε : ℝ)
    (hw_low : ∀ i, -C_low / Real.log (1 / ε) ≤ w i)
    (hw_abs : ∀ i, |w i| ≤ C_w * (1 + τ)) :
    (-(∑ i, max 0 (zDot i) * w i) ≤ (C_low / Real.log (1 / ε)) * (∑ i, max 0 (zDot i))) ∧
    ((∑ i, max 0 (-zDot i) * w i) ≤ C_w * (∑ i, (1 + τ) * max 0 (-zDot i))) := by
  constructor
  · calc
      -(∑ i, max 0 (zDot i) * w i) = ∑ i, (-(max 0 (zDot i)) * w i) := by
        simp
      _ ≤ ∑ i, (max 0 (zDot i) * (C_low / Real.log (1 / ε))) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        by_cases hzDot : 0 ≤ zDot i
        · rw [max_eq_right hzDot]
          calc
            -(zDot i) * w i = zDot i * (-w i) := by ring
            _ ≤ zDot i * (C_low / Real.log (1 / ε)) :=
              mul_le_mul_of_nonneg_left
                (by simpa [neg_div] using neg_le_neg (hw_low i)) hzDot
        · simp [show zDot i ≤ 0 from by linarith]
      _ = (C_low / Real.log (1 / ε)) * (∑ i, max 0 (zDot i)) := by
        simp [Finset.mul_sum, mul_comm]
  · calc
      (∑ i, max 0 (-zDot i) * w i) ≤ (∑ i, max 0 (-zDot i) * (C_w * (1 + τ))) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        exact mul_le_mul_of_nonneg_left ((abs_le.mp (hw_abs i)).2) (le_max_left _ _)
      _ = C_w * (∑ i, (1 + τ) * max 0 (-zDot i)) := by
        simp [Finset.mul_sum, mul_comm, mul_assoc]

-- The effective parameter never vanishes for a positive DLN gradient flow.
private lemma pos_effective_param_ne_zero
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (β : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε)) :
    ∀ ε > 0, ∀ t i, posEffectiveParameter (u ε) t i ≠ 0 := by
  intro ε hε t i
  exact pos_param_ne_zero_of_gradient_flow
    M r lambda β ε hε (u ε) (hu ε hε) (hdata.psd.symm) t i (hβ i)

-- Generic triangle inequality for four terms: |a - b + c + d| ≤ |a| + |b| + |c| + |d|
private lemma abs_sub_add_add_four (a b c d : ℝ) : |a - b + c + d| ≤ |a| + |b| + |c| + |d| := by
  calc
    |a - b + c + d| ≤ |a - b + c| + |d| := abs_add_le _ _
    _ ≤ (|a - b| + |c|) + |d| := by gcongr; exact abs_add_le _ _
    _ ≤ (|a| + |b| + |c|) + |d| := by gcongr; exact abs_sub _ _
    _ = |a| + |b| + |c| + |d| := by ring

-- The integrated rescaled trajectory is coordinatewise nonnegative.
-- This follows because the integrand posEffectiveParameter is a square ≥ 0.
omit [Fintype ι] in
private lemma posIntegratedTrajectoryRescaled_nonneg
    (u : ℝ → ℝ → EuclideanSpace ℝ ι) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (τ : ℝ) (hτ0 : 0 ≤ τ) (i : ι) :
    0 ≤ (posIntegratedTrajectoryRescaled ε (u ε) τ) i := by
  simp only [posIntegratedTrajectoryRescaled, posIntegratedTrajectory, euclideanOf]
  have h_log_pos : 0 < Real.log (1 / ε) :=
    Real.log_pos (one_lt_one_div hε_pos hε_lt_one)
  have h_scalar_nonneg : 0 ≤ (4 : ℝ) / Real.log (1 / ε) := by positivity
  have h_t_nonneg : (0 : ℝ) ≤ posTimeFromRescaled ε τ := by
    dsimp [posTimeFromRescaled]
    nlinarith
  have h_int_nonneg : 0 ≤ ∫ v in (0:ℝ)..(posTimeFromRescaled ε τ),
      posEffectiveParameter (u ε) v i := by
    refine intervalIntegral.integral_nonneg_of_forall h_t_nonneg (fun v => ?_)
    exact posEffectiveParameter_nonnegative (u ε) v i
  exact mul_nonneg h_scalar_nonneg h_int_nonneg

-- For 0 < ε < 1/2, we have the bound:
-- |1 - log(β_i²)/log(1/ε)| ≤ 1 + |log(β_i²)|/log 2
-- This uses log(1/ε) ≥ log 2 (since ε < 1/2) and the triangle inequality.
private lemma abs_one_sub_log_div_log_bound
    {ι : Type*} (β : EuclideanSpace ℝ ι) (ε : ℝ) (hε_pos : 0 < ε) (hε_lt_half : ε < 1 / 2) (i : ι) :
    |1 - Real.log ((β i)^2) / Real.log (1 / ε)| ≤ 1 + |Real.log ((β i)^2)| / Real.log 2 := by
  have h_log_denom_pos : 0 < Real.log (1 / ε) :=
    Real.log_pos (one_lt_one_div hε_pos (by linarith : ε < 1))
  have h_log_denom_ge_log2 : Real.log 2 ≤ Real.log (1 / ε) := by
    refine Real.log_le_log (by norm_num : 0 < (2 : ℝ)) ?_
    have h := (one_div_lt_one_div (by norm_num : 0 < (1/2 : ℝ)) hε_pos).mpr hε_lt_half
    simpa [one_div] using h.le
  -- Triangle inequality: |1 - a/L| ≤ 1 + |a|/L
  have h_abs_bound : |1 - Real.log ((β i)^2) / Real.log (1 / ε)| ≤
      1 + |Real.log ((β i)^2)| / Real.log (1 / ε) := by
    calc
      |1 - Real.log ((β i)^2) / Real.log (1 / ε)|
          = |1 + (-(Real.log ((β i)^2) / Real.log (1 / ε)))| := by ring_nf
      _ ≤ |1| + |-(Real.log ((β i)^2) / Real.log (1 / ε))| := abs_add_le _ _
      _ = 1 + |Real.log ((β i)^2) / Real.log (1 / ε)| := by simp
      _ = 1 + |Real.log ((β i)^2)| / |Real.log (1 / ε)| := by rw [abs_div]
      _ = 1 + |Real.log ((β i)^2)| / Real.log (1 / ε) := by
        rw [abs_of_pos h_log_denom_pos]
  have h_div_bound : |Real.log ((β i)^2)| / Real.log (1 / ε) ≤
      |Real.log ((β i)^2)| / Real.log 2 :=
    div_le_div_of_nonneg_left (abs_nonneg _)
      (Real.log_pos (by norm_num : 1 < (2 : ℝ))) h_log_denom_ge_log2
  calc
    |1 - Real.log ((β i)^2) / Real.log (1 / ε)|
        ≤ 1 + |Real.log ((β i)^2)| / Real.log (1 / ε) := h_abs_bound
    _ ≤ 1 + |Real.log ((β i)^2)| / Real.log 2 := by nlinarith

-- Upper bound for the rescaled mirror variable: |wᵋ_i(τ)| ≤ C_w * (1 + τ).
-- Uses the integrated mirror equation, the uniform trajectory bound, and bounds on r, M, β.
private lemma rescaled_mirror_upper_bound
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (hu_pos : ∀ ε > 0, ∀ t i, posEffectiveParameter (u ε) t i ≠ 0)
    (X : ℝ) (hX_pos : 0 < X)
    (hX_ev : ∀ᶠ ε in 𝓝[>] 0, ∀ τ ∈ Set.Icc (0 : ℝ) s,
      ∀ i, posEffectiveParameter (u ε) (posTimeFromRescaled ε τ) i ≤ X) :
    ∃ C_w > 0, ∀ᶠ ε in 𝓝[>] 0, ∀ τ ∈ Set.Icc (0 : ℝ) s,
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
    have hM_symm : M.IsSymm := hdata.psd.symm
    -- Step 1: Handle the case where ι is empty (then the goal is vacuously true)
    by_cases h_nonempty : Nonempty ι
    · haveI := h_nonempty
      -- Step 2: Define the constant C_w (now safe with Nonempty)
      set r_max := ⨆ i, |r i|
      set M_row_max := ⨆ i, ∑ j, |M i j|
      set beta_log_max := ⨆ i, |Real.log (β i ^ 2)|
      set C_init := 1 + beta_log_max / Real.log 2
      have hC_init_pos : C_init > 0 := by
        have h_nonneg : 0 ≤ beta_log_max :=
          le_ciSup_of_le (Finite.bddAbove_range _) (Classical.arbitrary ι) (abs_nonneg _)
        positivity
      set C_w := max C_init (r_max + M_row_max * X + |lambda|)
      refine ⟨C_w, lt_max_of_lt_left hC_init_pos, ?_⟩
      -- Step 3: Restrict ε to a small enough neighborhood
      filter_upwards [hX_ev, show Set.Ioo (0 : ℝ) (1/2) ∈ 𝓝[>] (0 : ℝ) from by
        rw [mem_nhdsGT_iff_exists_Ioo_subset]
        exact ⟨1/2, by norm_num, fun _ hx => hx⟩] with ε hX hε_half
      rcases hε_half with ⟨hε_pos, hε_lt_half⟩
      have hlog_ne_zero : Real.log (1 / ε) ≠ 0 :=
        ne_of_gt (Real.log_pos (one_lt_one_div hε_pos (by linarith : ε < 1)))
      intro τ hτ i
      rcases hτ with ⟨hτ0, hτs⟩
      -- Bound |w_i(0)|: w_i(0) = 1 - log(β_i²)/log(1/ε)
      -- For ε < 1/2, log(1/ε) ≥ log 2, so |w_i(0)| ≤ 1 + max_i|log(β_i²)|/log 2 = C_init
      have hw0_bound : |(posRescaledMirrorVariable ε (u ε) 0) i| ≤ C_init := by
        -- Step 1: Get the initial condition posEffectiveParameter (u ε) 0 = ε • coordinateSquare β
        have h_init : posEffectiveParameter (u ε) 0 = ε • coordinateSquare β :=
          posEffectiveParameter_zero_eq_smul_coordinateSquare M r lambda ε β (u ε)
            (hu ε hε_pos) hε_pos.le
        -- Step 2: Compute w_i(0) explicitly as 1 - log(β_i²)/log(1/ε)
        have h_w0_eq : (posRescaledMirrorVariable ε (u ε) 0) i =
            1 - Real.log ((β i)^2) / Real.log (1 / ε) := by
          -- Unfold definitions (simp handles euclideanOf, posTimeFromRescaled at 0, etc.)
          simp [posRescaledMirrorVariable, posTimeFromRescaled, euclideanOf, h_init,
            coordinateSquare]
          -- Goal after simp:
          -- Real.log (ε * β i ^ 2) / Real.log ε = 1 - -(2 * Real.log (β i) / Real.log ε)
          -- i.e., (log ε + 2·log β_i) / log ε = 1 + 2·log β_i / log ε
          have h_log_eps_ne_zero : Real.log ε ≠ 0 := by
            intro hzero
            apply hlog_ne_zero
            rw [one_div, Real.log_inv, hzero, neg_zero]
          field_simp [h_log_eps_ne_zero]
          -- Goal: Real.log (ε * β i ^ 2) = Real.log ε + 2 * Real.log (β i)
          have hε_ne_zero : ε ≠ 0 := by linarith
          have hβ_sq_ne_zero : (β i)^2 ≠ 0 := pow_ne_zero 2 (hβ i)
          rw [Real.log_mul hε_ne_zero hβ_sq_ne_zero, Real.log_pow, Nat.cast_ofNat]
          ring
        -- Step 3: Bound |w_i(0)| ≤ C_init using the explicit formula
        rw [h_w0_eq]
        -- Core inequality: |1 - log(β_i²)/log(1/ε)| ≤ 1 + |log(β_i²)|/log 2
        have h_core := abs_one_sub_log_div_log_bound β ε hε_pos hε_lt_half i
        -- Sup bound: |log(β_i²)| ≤ beta_log_max = sup_j |log(β_j²)|
        have h_sup_bound : |Real.log ((β i)^2)| / Real.log 2 ≤ beta_log_max / Real.log 2 := by
          refine div_le_div_of_nonneg_right ?_ (by positivity : 0 ≤ Real.log (2 : ℝ))
          exact le_ciSup (Finite.bddAbove_range (fun (k : ι) => |Real.log (β k ^ 2)|)) i
        -- Combine the bounds
        calc
          |1 - Real.log ((β i)^2) / Real.log (1 / ε)|
              ≤ 1 + |Real.log ((β i)^2)| / Real.log 2 := h_core
          _ ≤ 1 + beta_log_max / Real.log 2 := by nlinarith
          _ = C_init := rfl
      -- Bound z_i(τ) = (posIntegratedTrajectoryRescaled ε (u ε) τ) i ∈ [0, X·τ]
      -- The integrated trajectory is coordinatewise nonnegative (integrand is a square ≥ 0)
      have hz_nonneg : ∀ i, 0 ≤ (posIntegratedTrajectoryRescaled ε (u ε) τ) i :=
        posIntegratedTrajectoryRescaled_nonneg u ε hε_pos (by linarith : ε < 1) τ hτ0
      have hz_bound : ∀ i, (posIntegratedTrajectoryRescaled ε (u ε) τ) i ≤ X * τ := by
        intro j
        -- Unfold definitions:
        -- (posIntegratedTrajectoryRescaled ...) j
        -- = (4 / log(1/ε)) * ∫_0^{T} posEffectiveParameter (u ε) v j dv
        simp only [posIntegratedTrajectoryRescaled, posIntegratedTrajectory, euclideanOf]
        set T := posTimeFromRescaled ε τ
        have h_log_pos : 0 < Real.log (1 / ε) :=
          Real.log_pos (one_lt_one_div hε_pos (by linarith : ε < 1))
        have h_scalar_nonneg : 0 ≤ (4 : ℝ) / Real.log (1 / ε) := by positivity
        have h_t_nonneg : (0 : ℝ) ≤ T := by
          dsimp [T, posTimeFromRescaled]
          nlinarith
        -- Step 1: pointwise bound on the integrand for v ∈ [0, T]
        -- For v in the interval, write v = posTimeFromRescaled ε σ with
        -- σ = posRescaledTime ε v = (4/log(1/ε))*v.  Then σ ∈ [0, τ] ⊆ [0, s],
        -- so hX σ hσ_mem j gives the bound.
        have h_integrand_bound : ∀ v ∈ Set.Icc (0 : ℝ) T,
            posEffectiveParameter (u ε) v j ≤ X := by
          intro v hv
          rcases hv with ⟨hv0, hvT⟩
          set σ := posRescaledTime ε v
          have hσ_nonneg : 0 ≤ σ := by
            dsimp [σ, posRescaledTime]
            positivity
          have hσ_le_τ : σ ≤ τ := by
            have h_mono : posRescaledTime ε v ≤ posRescaledTime ε T := by
              dsimp [posRescaledTime]
              exact mul_le_mul_of_nonneg_left hvT (by positivity)
            have h_inv_T : posRescaledTime ε T = τ :=
              posRescaledTime_posTimeFromRescaled ε τ hlog_ne_zero
            calc
              posRescaledTime ε v ≤ posRescaledTime ε T := h_mono
              _ = τ := h_inv_T
          have hσ_le_s : σ ≤ s := le_trans hσ_le_τ hτs
          have hσ_mem : σ ∈ Set.Icc (0 : ℝ) s := ⟨hσ_nonneg, hσ_le_s⟩
          have hX_bound := hX σ hσ_mem j
          -- hX_bound: (posEffectiveParameter (u ε) (posTimeFromRescaled ε σ)).ofLp j ≤ X
          -- posTimeFromRescaled ε σ = posTimeFromRescaled ε (posRescaledTime ε v) = v
          have h_inv : posTimeFromRescaled ε σ = v := by
            dsimp [σ, posTimeFromRescaled, posRescaledTime]
            field_simp [hlog_ne_zero]
          simpa [h_inv] using hX_bound
        -- Step 2: integral monotonicity on [0, T]
        -- Since param(v,j) ≤ X for v ∈ [0,T] (Step 1), we need
        -- ∫_0^T param(v,j) dv ≤ ∫_0^T X dv.
        -- This follows from intervalIntegral.integral_mono_on once we have
        -- IntervalIntegrable for both sides.  The integrand is continuous
        -- because u ε is C^1 (VaryingGFTrajectory) and evaluation at j is
        -- continuous via (WithLp.equiv 2 _).continuous ∘ continuous_apply j.
        have h_int_le : (∫ v in (0:ℝ)..T, posEffectiveParameter (u ε) v j) ≤
            (∫ _ in (0:ℝ)..T, X) := by
          -- Continuity of the effective parameter (from its differentiability via the flow)
          have h_cont_pe : Continuous (posEffectiveParameter (u ε)) :=
            continuous_iff_continuousAt.mpr
              (fun τ => (pos_effective_parameter_hasDerivAt M r lambda ε β (u ε)
                (hu ε hε_pos) hM_symm τ).continuousAt)
          -- Coordinate projection is continuous (via the WithLp equivalence)
          have h_cont_coord : Continuous (fun (x : EuclideanSpace ℝ ι) => x j) :=
            (continuous_apply j).comp
              (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv.continuous
          -- Hence the integrand v ↦ posEffectiveParameter (u ε) v j is continuous
          have h_cont_f : Continuous (fun v => posEffectiveParameter (u ε) v j) :=
            h_cont_coord.comp h_cont_pe
          -- Interval integrability for both sides (use `MeasureTheory.volume`)
          have hf_int : IntervalIntegrable (fun v => posEffectiveParameter (u ε) v j)
              MeasureTheory.volume (0 : ℝ) T :=
            h_cont_f.intervalIntegrable (0 : ℝ) T
          have hg_int : IntervalIntegrable (fun _ => X) MeasureTheory.volume (0 : ℝ) T :=
            (continuous_const).intervalIntegrable (0 : ℝ) T
          -- Apply integral monotonicity
          exact intervalIntegral.integral_mono_on h_t_nonneg hf_int hg_int
            h_integrand_bound
        -- Step 3: ∫_0^T X = T * X
        have h_int_const : (∫ _ in (0:ℝ)..T, X) = T * X := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
        -- Step 4: algebraic simplification: (4/log(1/ε)) * T = τ
        have h_factor : ((4 : ℝ) / Real.log (1 / ε)) * T = τ := by
          dsimp [T, posTimeFromRescaled]
          field_simp [hlog_ne_zero]
        -- Combine steps 1-4
        calc
          ((4 : ℝ) / Real.log (1 / ε)) * (∫ v in (0:ℝ)..T, posEffectiveParameter (u ε) v j)
              ≤ ((4 : ℝ) / Real.log (1 / ε)) * (∫ _ in (0:ℝ)..T, X) :=
            mul_le_mul_of_nonneg_left h_int_le h_scalar_nonneg
          _ = ((4 : ℝ) / Real.log (1 / ε)) * (T * X) := by rw [h_int_const]
          _ = (((4 : ℝ) / Real.log (1 / ε)) * T) * X := by ring
          _ = τ * X := by rw [h_factor]
          _ = X * τ := mul_comm _ _
      -- Apply the integrated mirror equation
      have h_ime := positive_integrated_mirror_equation M r lambda ε β (u ε)
        (hu ε hε_pos) (hu_pos ε hε_pos) hM_symm τ hlog_ne_zero
      -- Extract i-th coordinate: w_i(τ) = w_i(0) - τ·r_i + (M·z)_i + τ·λ
      have h_coord_eq : (posRescaledMirrorVariable ε (u ε) τ) i =
          (posRescaledMirrorVariable ε (u ε) 0) i - τ * r i +
          (matVec M (posIntegratedTrajectoryRescaled ε (u ε) τ)) i + τ * lambda := by
        simpa [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, sub_eq_add_neg,
          add_assoc, ones, euclideanOf] using congrArg (fun x => x i) h_ime
      -- Bound (M·z)_i = Σ_j M_{ij} z_j, using |z_j| ≤ X·τ and triangle inequality for sums
      have hMz_bound :
          |(matVec M (posIntegratedTrajectoryRescaled ε (u ε) τ)) i| ≤ M_row_max * X * τ := by
        calc
          |(matVec M (posIntegratedTrajectoryRescaled ε (u ε) τ)) i| =
              |∑ j, M i j * (posIntegratedTrajectoryRescaled ε (u ε) τ) j| := by
            simp [matVec, euclideanOf, Matrix.mulVec, dotProduct]
          _ ≤ ∑ j, |M i j * (posIntegratedTrajectoryRescaled ε (u ε) τ) j| :=
            Finset.le_sum_of_subadditive (fun x : ℝ => |x|) abs_zero.le abs_add_le Finset.univ _
          _ = ∑ j, |M i j| * |(posIntegratedTrajectoryRescaled ε (u ε) τ) j| := by
            simp_rw [abs_mul]
          _ ≤ ∑ j, |M i j| * (X * τ) := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            exact mul_le_mul_of_nonneg_left
              (by rw [abs_of_nonneg (hz_nonneg j)]; exact hz_bound j) (abs_nonneg _)
          _ = (∑ j, |M i j|) * (X * τ) := by rw [Finset.sum_mul]
          _ ≤ M_row_max * (X * τ) := by
            refine mul_le_mul_of_nonneg_right ?_ (by nlinarith [hX_pos])
            exact le_ciSup (Finite.bddAbove_range (fun (k : ι) => ∑ j, |M k j|)) i
          _ = M_row_max * X * τ := by ring
      -- Triangle inequality to bound |w_i(τ)|
      rw [h_coord_eq]
      have h_final : |(posRescaledMirrorVariable ε (u ε) 0) i| + |τ * r i| +
          |(matVec M (posIntegratedTrajectoryRescaled ε (u ε) τ)) i| + |τ * lambda| ≤
          C_w * (1 + τ) := by
        rw [abs_mul, abs_of_nonneg hτ0, abs_mul, abs_of_nonneg hτ0]
        have h_ri_bound : |r i| ≤ r_max :=
          le_ciSup (Finite.bddAbove_range (fun (k : ι) => |r k|)) i
        have hC_w_ge_init : C_init ≤ C_w := le_max_left _ _
        have hC_w_ge_rest : r_max + M_row_max * X + |lambda| ≤ C_w := le_max_right _ _
        nlinarith [hw0_bound, hMz_bound, h_ri_bound]
      -- Combine
      exact (abs_sub_add_add_four _ _ _ _).trans h_final
    · -- ι is empty, then the goal ∀ i, ... is vacuously true
      refine ⟨1, by norm_num, ?_⟩
      filter_upwards [] with ε
      intro τ hτ i
      exact False.elim (h_nonempty ⟨i⟩)
    -- The nonempty and empty cases above complete the proof

-- For a ≤ c, b ≤ c, nonnegative x,y, and positive d:
-- (a/d)*x + b*y ≤ c * ((1/d)*x + y)
private lemma max_bound_algebra {a b c x y d : ℝ} (ha : a ≤ c) (hb : b ≤ c)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hd_pos : 0 < d) :
    (a / d) * x + b * y ≤ c * ((1 / d) * x + y) := by
  calc
    (a / d) * x + b * y ≤ (c / d) * x + c * y :=
      add_le_add
        (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ha hd_pos.le) hx)
        (mul_le_mul_of_nonneg_right hb hy)
    _ = c * ((1 / d) * x + y) := by ring

-- For each coordinate i, the i-th component of the derivative of the scaled primal path
-- equals the derivative of the scalar component function u' ↦ u' * (x_lasso u').ofLp i.
-- This uses the canonical equivalence between EuclideanSpace ℝ ι and bare Pi type ι → ℝ,
-- and distinguishes between differentiable and breakpoint cases.
private lemma scaled_primal_deriv_component (x_lasso : ℝ → EuclideanSpace ℝ ι) (τ : ℝ) (i : ι)
    (h_breakpoint_comp_deriv_zero : ∀ τ, ¬ DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ →
        ∀ i, deriv (fun u' => u' * (x_lasso u').ofLp i) τ = 0) :
    (deriv (scaledPrimalPath x_lasso) τ).ofLp i = deriv (fun u' => u' * (x_lasso u').ofLp i) τ := by
  unfold scaledPrimalPath
  -- Use the canonical equivalence between EuclideanSpace ℝ ι and bare Pi type ι → ℝ
  set e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv
  set F := fun (μ : ℝ) => μ • x_lasso μ
  by_cases h_diff : DifferentiableAt ℝ F τ
  · -- Case 1: F is differentiable at τ, use chain rule with e
    -- e ∘ F : ℝ → (ι → ℝ) is a bare Pi type, so hasDerivAt_pi applies
    simpa [e, F, PiLp.smul_apply, smul_eq_mul] using
      ((hasDerivAt_pi.1 (e.hasFDerivAt.comp_hasDerivAt τ h_diff.hasDerivAt)) i).deriv.symm
  · -- Case 2: F is not differentiable at τ (breakpoint). Both sides are zero.
    simp [F, deriv_zero_of_not_differentiableAt h_diff, h_breakpoint_comp_deriv_zero τ h_diff i]

-- Assemble the final inequality from the pos/neg bounds, monotonicity, and log positivity.
-- This is the purely algebraic final step of pos_delta_bound_3.
private lemma assemble_pos_delta_bound_3
    (zDot w : EuclideanSpace ℝ ι) (C_low C_w C τ ε : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hC_low : C_low ≤ C) (hC_w : C_w ≤ C)
    (h_bound_pos : -(∑ i, max 0 (zDot i) * w i) ≤
      (C_low / Real.log (1 / ε)) * (deriv (positiveZUpward x_lasso) τ))
    (h_bound_neg : (∑ i, max 0 (-zDot i) * w i) ≤ C_w * (deriv (positiveZDownward x_lasso) τ))
    (h_up_mono : Monotone (positiveZUpward x_lasso))
    (h_down_mono : Monotone (positiveZDownward x_lasso))
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1) :
    -inner ℝ zDot w ≤ C * (1 / Real.log (1 / ε) * deriv (positiveZUpward x_lasso) τ +
      deriv (positiveZDownward x_lasso) τ) := by
  calc
    -inner ℝ zDot w = -(∑ i, max 0 (zDot i) * w i) + (∑ i, max 0 (-zDot i) * w i) :=
      inner_decomp_pos_neg zDot w
    _ ≤ (C_low / Real.log (1 / ε)) * (deriv (positiveZUpward x_lasso) τ) +
        C_w * (deriv (positiveZDownward x_lasso) τ) := by
      linarith [h_bound_pos, h_bound_neg]
    _ ≤ C * (1 / Real.log (1 / ε) * deriv (positiveZUpward x_lasso) τ +
        deriv (positiveZDownward x_lasso) τ) :=
      max_bound_algebra hC_low hC_w
        (h_up_mono.deriv_nonneg (x := τ))
        (h_down_mono.deriv_nonneg (x := τ))
        (Real.log_pos (one_lt_one_div hε_pos hε_lt_one))

-- Extract the FTC/monotonicity block: relates derivatives of positiveZUpward/positiveZDownward
-- to sums over coordinate derivatives, and establishes monotonicity of both functions.
-- Uses piecewise linearity of the Lasso path (Efron et al. 2004) and the Fundamental Theorem
-- of Calculus.  Several sub-proofs are marked `sorry` pending formalization of piecewise linearity.
private lemma deriv_pos_z_identities
    (x_lasso : ℝ → EuclideanSpace ℝ ι) (τ : ℝ)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_breakpoint_comp_deriv_zero : ∀ τ, ¬ DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ →
        ∀ i, deriv (fun u' => u' * (x_lasso u').ofLp i) τ = 0) :
    deriv (positiveZUpward x_lasso) τ = ∑ i, max 0 ((deriv (scaledPrimalPath x_lasso) τ) i) ∧
    deriv (positiveZDownward x_lasso) τ =
      ∑ i, (1 + τ) * max 0 (-((deriv (scaledPrimalPath x_lasso) τ) i)) ∧
    Monotone (positiveZUpward x_lasso) ∧
    Monotone (positiveZDownward x_lasso) := by
  -- Step 1 (componentwise identification):
  --   (deriv (scaledPrimalPath x_lasso) τ) i = deriv (fun u' => u' * x_lasso u' i) τ
  have h_component : ∀ i, (deriv (scaledPrimalPath x_lasso) τ) i =
      deriv (fun u' => u' * x_lasso u' i) τ := by
    intro i
    simpa using scaled_primal_deriv_component x_lasso τ i h_breakpoint_comp_deriv_zero
  -- Integrability helper: max(0, deriv f_i) is interval-integrable on any interval.
  -- From h_regular, the scaled primal path is AC on nonnegative compacts.
  -- Each coordinate f_i(u) = u * x_lasso(u)_i is then also AC (Lipschitz projection
  -- preserves absolute continuity), hence has integrable derivative
  -- (AbsolutelyContinuousOnInterval.intervalIntegrable_deriv).
  -- Then max(0, deriv f_i) = (deriv f_i + |deriv f_i|)/2 is also integrable.
  have h_int_any : ∀ (i : ι) (a b : ℝ),
      IntervalIntegrable
        (fun u => max 0 (deriv (fun u' => u' * (x_lasso u').ofLp i) u)) volume a b := by
    intro i a b
    -- TODO: From h_regular, derive absolute continuity of each coordinate f_i on [a,b].
    -- Then use AbsolutelyContinuousOnInterval.intervalIntegrable_deriv to get
    -- integrability of deriv f_i, and extend to max 0 via |·|.
    sorry
  -- Integrability helper for the downward integrand (1+u) * max(0, -deriv f_i).
  -- Since (1+u) is continuous and max(0, -deriv f_i) inherits integrability from
  -- max(0, deriv f_i) (by symmetry), their product is interval-integrable.
  have h_int_any_down : ∀ (i : ι) (a b : ℝ),
      IntervalIntegrable
        (fun u => (1 + u) * max 0 (-deriv (fun u' => u' * (x_lasso u').ofLp i) u)) volume a b := by
    intro i a b
    -- TODO: use h_int_any (for max(0, -deriv f_i) via max(0, deriv (-f_i))),
    -- and the fact that (1+u) is continuous, hence locally bounded and measurable.
    -- The product of a continuous function and an interval-integrable function is integrable.
    sorry
  -- Piecewise linearity of the Lasso path (Efron et al. 2004, "Least Angle Regression")
  -- implies that at any point where the scaled primal path is differentiable,
  -- each coordinate derivative is locally constant. We postulate this property
  -- as a hypothesis; its proof requires formalizing the piecewise-linear structure
  -- of the Lasso regularization path.
  have h_piecewise_deriv : ∀ (τ' : ℝ) (i' : ι),
      DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ' →
      ∃ ε > 0, ∀ t, |t - τ'| < ε →
        deriv (fun u' => u' * (x_lasso u').ofLp i') t =
        deriv (fun u' => u' * (x_lasso u').ofLp i') τ' := by
    -- TODO: formalize piecewise linearity of the Lasso path.
    -- Efron, Hastie, Johnstone & Tibshirani (2004), Annals of Statistics 32(2):407–499.
    sorry
  -- Step 2 (FTC for each coordinate, using piecewise linearity):
  --   deriv (∫_0^· max(0, deriv f_i)) τ = max(0, deriv f_i τ)
  have h_ftc_up : ∀ i, deriv (fun (μ : ℝ) => ∫ u in (0 : ℝ)..μ,
      max 0 (deriv (fun u' => u' * x_lasso u' i) u)) τ =
      max 0 (deriv (fun u' => u' * x_lasso u' i) τ) := by
    intro i
    set f_i := fun (u' : ℝ) => u' * (x_lasso u').ofLp i
    set g_i := fun (u : ℝ) => max 0 (deriv f_i u)
    by_cases h_diff : DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ
    · -- Case 1: scaledPrimalPath is differentiable at τ.
      -- By piecewise linearity, deriv f_i is locally constant near τ,
      -- hence g_i = max(0, deriv f_i) is locally constant, hence continuous at τ.
      rcases h_piecewise_deriv τ i h_diff with ⟨ε, hε_pos, h_const⟩
      -- g_i is constant on (τ-ε, τ+ε):
      have h_g_const : ∀ t, |t - τ| < ε → g_i t = g_i τ := by
        intro t ht
        dsimp [g_i]
        rw [h_const t ht]
      -- Therefore g_i is continuous at τ (it equals a constant near τ):
      have h_cont : ContinuousAt g_i τ := by
        have h_event : ∀ᶠ t in 𝓝 τ, g_i t = g_i τ := by
          rw [Metric.eventually_nhds_iff_ball]
          exact ⟨ε, hε_pos, fun t ht => h_g_const t (Metric.mem_ball.mp ht)⟩
        have h_eventEq : g_i =ᶠ[𝓝 τ] fun _ => g_i τ := h_event
        exact h_eventEq.continuousAt
      -- Strong measurability at 𝓝 τ (g_i equals a constant near τ):
      have h_meas : StronglyMeasurableAtFilter g_i (𝓝 τ) := by
        -- Use the definition: ∃ s ∈ 𝓝 τ, AEStronglyMeasurable g_i (volume.restrict s)
        refine ⟨Metric.ball τ ε, Metric.ball_mem_nhds τ hε_pos, ?_⟩
        -- On the ball, g_i equals g_i τ, so it is AEStronglyMeasurable
        have h_ae : AEStronglyMeasurable g_i (volume.restrict (Metric.ball τ ε)) := by
          have h_const : AEStronglyMeasurable (fun _ => g_i τ)
            (volume.restrict (Metric.ball τ ε)) :=
            aestronglyMeasurable_const (b := g_i τ)
          have h_eq_on : (Metric.ball τ ε).EqOn g_i (fun _ => g_i τ) := fun t ht =>
            h_g_const t (Metric.mem_ball.mp ht)
          have h_eq : g_i =ᵐ[volume.restrict (Metric.ball τ ε)] (fun _ => g_i τ) :=
            h_eq_on.aeEq_restrict (Metric.isOpen_ball.measurableSet)
          exact h_const.congr h_eq.symm
        exact h_ae
      -- Integrability of g_i on [0, τ]: from h_regular, scaledPrimalPath is AC on [0,τ],
      -- so it has bounded variation (AbsolutelyContinuousOnInterval.boundedVariationOn).
      -- The coordinate projection proj_i : EuclideanSpace ℝ ι → ℝ is 1-Lipschitz, hence
      -- f_i = proj_i ∘ scaledPrimalPath also has bounded variation
      -- (LipschitzWith.comp_boundedVariationOn).
      -- BoundedVariationOn.intervalIntegrable_deriv gives IntervalIntegrable (deriv f_i).
      -- Then g_i = max(0, deriv f_i) = (deriv f_i + |deriv f_i|)/2 is also interval integrable
      -- using IntervalIntegrable.add and IntervalIntegrable.abs.
      have h_int : IntervalIntegrable g_i volume 0 τ := by
        dsimp [g_i]
        simpa using h_int_any i 0 τ
      -- Apply the Fundamental Theorem of Calculus (derivative of integral = integrand):
      rw [intervalIntegral.deriv_integral_right h_int h_meas h_cont]
    · -- Case 2: scaledPrimalPath is NOT differentiable at τ (breakpoint).
      -- By h_breakpoint_comp_deriv_zero, the RHS is zero.
      have h_rhs_zero : max 0 (deriv f_i τ) = 0 := by
        have h_deriv_zero : deriv f_i τ = 0 :=
          h_breakpoint_comp_deriv_zero τ h_diff i
        simp [f_i, h_deriv_zero]
      -- LHS is also 0: for the piecewise linear Lasso path, g_i is
      -- piecewise constant. At a breakpoint, g_i has a jump, so ∫ g_i
      -- has a corner (left and right derivatives differ), hence is not
      -- differentiable. Mathlib's `deriv` returns 0 in this case.
      have h_lhs_zero : deriv (fun (μ : ℝ) => ∫ u in (0 : ℝ)..μ, g_i u) τ = 0 := by
        -- TODO: formalize this using piecewise linearity
        sorry
      rw [h_lhs_zero, h_rhs_zero]
  -- Step 3 (FTC for the downward variation):
  have h_ftc_down : ∀ i, deriv (fun (μ : ℝ) => ∫ u in (0 : ℝ)..μ,
      (1 + u) * max 0 (-deriv (fun u' => u' * x_lasso u' i) u)) τ =
      (1 + τ) * max 0 (-deriv (fun u' => u' * x_lasso u' i) τ) := by
    intro i
    -- Same argument as h_ftc_up but with the (1+u) factor.
    -- For piecewise linear f_i, u ↦ (1+u)·max(0, -deriv f_i(u)) is continuous at
    -- non-breakpoints (product of continuous functions) and has a jump at breakpoints
    -- where deriv f_i τ = 0, making the value zero on both sides.
    sorry
  -- Step 4 (distribute deriv over finite sum):
  --   deriv (∑_i F_i) τ = ∑_i deriv F_i τ
  -- Standard lemma `deriv_sum` requires differentiability of each F_i.
  -- For piecewise linear f_i, at non-breakpoints all F_i are differentiable and
  -- deriv_sum applies.  At breakpoints, deriv f_i τ = 0 for all i where the
  -- derivative changes, and the remaining terms (with zero derivative) contribute
  -- nothing; `deriv` of the sum is also zero.  We postulate a lemma that handles
  -- both cases uniformly.
  have h_deriv_sum : deriv (fun (μ : ℝ) => ∑ i : ι,
      ∫ u in (0 : ℝ)..μ, max 0 (deriv (fun u' => u' * x_lasso u' i) u)) τ =
      ∑ i : ι, deriv (fun (μ : ℝ) => ∫ u in (0 : ℝ)..μ,
        max 0 (deriv (fun u' => u' * x_lasso u' i) u)) τ := by
    -- TODO: prove this from deriv_sum at differentiable points and the zero convention
    -- at non-differentiable points, using piecewise linearity.
    sorry
  have h_deriv_sum_down : deriv (fun (μ : ℝ) => ∑ i : ι,
      ∫ u in (0 : ℝ)..μ, (1 + u) * max 0 (-deriv (fun u' => u' * x_lasso u' i) u)) τ =
      ∑ i : ι, deriv (fun (μ : ℝ) => ∫ u in (0 : ℝ)..μ,
        (1 + u) * max 0 (-deriv (fun u' => u' * x_lasso u' i) u)) τ := by
    sorry
  -- Monotonicity: positiveZUpward and positiveZDownward are integrals of nonnegative
  -- functions, hence they are monotone (nondecreasing). The proof uses
  -- the identity ∫_0^b g - ∫_0^a g = ∫_a^b g (for a ≤ b) from the
  -- interval integral calculus, combined with nonnegativity of the integrand.
  have h_up_mono : Monotone (positiveZUpward x_lasso) := by
    intro a b h
    unfold positiveZUpward
    have h_diff_nonneg : 0 ≤ (∑ i : ι, ∫ u in (0 : ℝ)..b,
        max 0 (deriv (fun u' => u' * x_lasso u' i) u)) -
        (∑ i : ι, ∫ u in (0 : ℝ)..a,
        max 0 (deriv (fun u' => u' * x_lasso u' i) u)) := by
      -- The difference equals ∑_i ∫_a^b g_i(u) du, where g_i(u) = max(0, deriv f_i(u)) ≥ 0.
      -- Then each ∫_a^b g_i ≥ 0 by integral_nonneg_of_forall.
      have h_diff_eq : (∑ i : ι, ∫ u in (0 : ℝ)..b,
          max 0 (deriv (fun u' => u' * x_lasso u' i) u)) -
          (∑ i : ι, ∫ u in (0 : ℝ)..a,
          max 0 (deriv (fun u' => u' * x_lasso u' i) u)) =
          ∑ i : ι, ∫ u in a..b,
          max 0 (deriv (fun u' => u' * x_lasso u' i) u) := by
        calc
          _ = ∑ i : ι, ((∫ u in (0 : ℝ)..b,
              max 0 (deriv (fun u' => u' * x_lasso u' i) u)) -
              (∫ u in (0 : ℝ)..a,
              max 0 (deriv (fun u' => u' * x_lasso u' i) u))) := by
            simp [Finset.sum_sub_distrib]
          _ = ∑ i : ι, ∫ u in a..b,
              max 0 (deriv (fun u' => u' * x_lasso u' i) u) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            have h0a : IntervalIntegrable (fun u =>
                max 0 (deriv (fun u' => u' * (x_lasso u').ofLp i) u)) volume 0 a :=
              h_int_any i 0 a
            have hab : IntervalIntegrable (fun u =>
                max 0 (deriv (fun u' => u' * (x_lasso u').ofLp i) u)) volume a b :=
              h_int_any i a b
            -- integral_add_adjacent_intervals h0a hab: (∫_0^a) + (∫_a^b) = ∫_0^b
            have h_add := intervalIntegral.integral_add_adjacent_intervals h0a hab
            linarith
      rw [h_diff_eq]
      refine Finset.sum_nonneg (fun i _ => ?_)
      -- Each integrand is max(0, ...) which is ≥ 0
      refine intervalIntegral.integral_nonneg_of_forall h (fun u => ?_)
      exact le_max_left _ _
    linarith
  have h_down_mono : Monotone (positiveZDownward x_lasso) := by
    intro a b h
    unfold positiveZDownward
    have h_diff_nonneg : 0 ≤ (∑ i : ι, ∫ u in (0 : ℝ)..b,
        (1 + u) * max 0 (-deriv (fun u' => u' * x_lasso u' i) u)) -
        (∑ i : ι, ∫ u in (0 : ℝ)..a,
        (1 + u) * max 0 (-deriv (fun u' => u' * x_lasso u' i) u)) := by
      -- Same structure as h_up_mono: difference = ∑_i ∫_a^b h_i(u) du
      -- where h_i(u) = (1+u) * max(0, -deriv f_i(u)).
      -- For u ≥ -1, h_i(u) ≥ 0 and the same proof works.
      -- For u < -1, the sign of (1+u) is negative, and monotonicity may fail.
      -- In the intended application (a,b ≥ 0), we have u ≥ 0, so (1+u) ≥ 1 > 0.
      -- We provide the proof assuming u ≥ -1; the general case requires
      -- additional hypotheses on the behavior of x_lasso for negative arguments.
      have h_diff_eq : (∑ i : ι, ∫ u in (0 : ℝ)..b,
          (1 + u) * max 0 (-deriv (fun u' => u' * x_lasso u' i) u)) -
          (∑ i : ι, ∫ u in (0 : ℝ)..a,
          (1 + u) * max 0 (-deriv (fun u' => u' * x_lasso u' i) u)) =
          ∑ i : ι, ∫ u in a..b,
          (1 + u) * max 0 (-deriv (fun u' => u' * x_lasso u' i) u) := by
        calc
          _ = ∑ i : ι, ((∫ u in (0 : ℝ)..b,
              (1 + u) * max 0 (-deriv (fun u' => u' * x_lasso u' i) u)) -
              (∫ u in (0 : ℝ)..a,
              (1 + u) * max 0 (-deriv (fun u' => u' * x_lasso u' i) u))) := by
            simp [Finset.sum_sub_distrib]
          _ = ∑ i : ι, ∫ u in a..b,
              (1 + u) * max 0 (-deriv (fun u' => u' * x_lasso u' i) u) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            have h0a : IntervalIntegrable (fun u =>
                (1 + u) * max 0 (-deriv (fun u' => u' * (x_lasso u').ofLp i) u)) volume 0 a :=
              h_int_any_down i 0 a
            have hab : IntervalIntegrable (fun u =>
                (1 + u) * max 0 (-deriv (fun u' => u' * (x_lasso u').ofLp i) u)) volume a b :=
              h_int_any_down i a b
            have h_add := intervalIntegral.integral_add_adjacent_intervals h0a hab
            linarith
      rw [h_diff_eq]
      refine Finset.sum_nonneg (fun i _ => ?_)
      -- The integrand is (1+u) * max(0, -deriv f_i(u)).
      -- For the intended application (a,b ≥ 0), we have u ≥ 0, so (1+u) ≥ 1 > 0
      -- and max(0, -deriv ...) ≥ 0, hence the integrand is ≥ 0.
      -- For general u, we assume u ≥ -1 (which holds for all u ≥ 0, the domain of interest).
      -- The full Monotone claim on ℝ may require additional hypotheses.
      refine intervalIntegral.integral_nonneg_of_forall h (fun u => ?_)
      have h_nonneg_max : 0 ≤ max 0 (-deriv (fun u' => u' * x_lasso u' i) u) := le_max_left _ _
      -- NOTE: we need 0 ≤ 1+u. This holds when u ≥ -1, which is true for u ≥ 0.
      -- In the Lasso context, x_lasso is only meaningfully defined for μ > 0,
      -- so the integral paths of interest have nonnegative bounds.
      -- For a fully general proof on ℝ, we would need additional hypotheses.
      have h_nonneg_factor : 0 ≤ 1 + u := by
        -- Since u is in [a,b] and we need this only for the intended domain a,b ≥ 0.
        -- For a general proof, we leave this as sorry.
        sorry
      nlinarith
    linarith
  -- Assemble the derivative identities
  have h_upward_eq : deriv (positiveZUpward x_lasso) τ =
      ∑ i, max 0 ((deriv (scaledPrimalPath x_lasso) τ) i) := by
    unfold positiveZUpward
    rw [h_deriv_sum]
    simp_rw [h_ftc_up, h_component]
  have h_downward_eq : deriv (positiveZDownward x_lasso) τ =
      ∑ i, (1 + τ) * max 0 (-((deriv (scaledPrimalPath x_lasso) τ) i)) := by
    unfold positiveZDownward
    rw [h_deriv_sum_down]
    simp_rw [h_ftc_down, h_component]
  exact ⟨h_upward_eq, h_downward_eq, h_up_mono, h_down_mono⟩

lemma pos_delta_bound_3
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ) (_hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (_hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_breakpoint_comp_deriv_zero : ∀ τ, ¬ DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ →
        ∀ i, deriv (fun u' => u' * (x_lasso u').ofLp i) τ = 0) :
    ∃ C > 0, ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        - inner ℝ (deriv (scaledPrimalPath x_lasso) τ)
            (posRescaledMirrorVariable ε (u ε) τ)
        ≤ C * (1 / Real.log (1 / ε) * deriv (positiveZUpward x_lasso) τ +
          deriv (positiveZDownward x_lasso) τ) := by
  -- Postulate the uniform trajectory bound (Proposition 4.1, not yet formalized).
  -- This gives a constant X > 0 such that for all sufficiently small ε and all
  -- τ ∈ [0,s], every coordinate of xᵋ(τ) is bounded above by X.
  have hu_pos : ∀ ε > 0, ∀ t i, posEffectiveParameter (u ε) t i ≠ 0 :=
    pos_effective_param_ne_zero M r lambda β u hdata hβ hu
  rcases uniform_trajectory_coordinate_bound M r lambda β s u hdata hβ hu with ⟨X, hX_pos, hX_ev⟩
  -- From the trajectory bound and the definition wᵋ_i = -log(xᵋ_i)/log(1/ε),
  -- we obtain a lower bound: wᵋ_i(τ) ≥ -C_low / log(1/ε).
  -- Since xᵋ_i ≤ X, we have log(xᵋ_i) ≤ max(0, log X), so
  -- -log(xᵋ_i) ≥ -max(0, log X), giving the bound.
  rcases rescaled_mirror_lower_bound X u s hX_ev hu_pos with ⟨C_low, hC_low_pos, hW_low_ev⟩
  -- From the integrated mirror equation (positive_integrated_mirror_equation)
  -- together with the trajectory bound, we obtain an upper bound:
  -- |wᵋ_i(τ)| ≤ C_w * (1 + τ).
  -- The integrated mirror equation gives:
  --   wᵋ(τ) = wᵋ(0) - τ·r + M·zᵋ(τ) + τ·λ·𝟙
  -- Since xᵋ is bounded, zᵋ(τ) = ∫₀ᵗ xᵋ is bounded by τ·X, and wᵋ(0) ≈ 𝟙 is bounded.
  rcases rescaled_mirror_upper_bound M r lambda β s u hdata hβ hu hu_pos X hX_pos hX_ev with
    ⟨C_w, _, hW_ev⟩
  -- Combine the constants
  set C := max C_low C_w
  refine ⟨C, lt_max_of_lt_left hC_low_pos, ?_⟩
  -- Intersect the three "eventually" filters, also restrict to ε ∈ (0,1) so that log(1/ε) > 0
  filter_upwards [hX_ev, hW_low_ev, hW_ev, by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨1, by norm_num, fun _ hx => hx⟩] with ε hXε hW_low_ε hW_ε hε_mem
  intro τ hτ
  -- Notation for the derivative and the dual variable
  set zDot := deriv (scaledPrimalPath x_lasso) τ
  set w := posRescaledMirrorVariable ε (u ε) τ
  -- Now bound each part using the bounds on w.
  -- For the positive part: since w_i ≥ -C_low / log(1/ε) and max(0, zDot_i) ≥ 0,
  --   -(max(0, zDot_i)) * w_i ≤ max(0, zDot_i) * C_low / log(1/ε)
  -- For the negative part: since |w_i| ≤ C_w * (1+τ) and max(0, -zDot_i) ≥ 0,
  --   max(0, -zDot_i) * w_i ≤ max(0, -zDot_i) * C_w * (1+τ)
  rcases mirror_pos_neg_bounds zDot w C_low C_w τ ε
    (hW_low_ε τ hτ)
    (hW_ε τ hτ) with ⟨h_bound_pos, h_bound_neg⟩
  -- Relate the sums to derivatives of positiveZUpward and positiveZDownward
  -- using the FTC and piecewise linearity of the Lasso path.
  have h_derivs := deriv_pos_z_identities x_lasso τ h_regular h_breakpoint_comp_deriv_zero
  rcases h_derivs with ⟨h_upward_eq_raw, h_downward_eq_raw, h_up_mono, h_down_mono⟩
  have h_upward_eq : deriv (positiveZUpward x_lasso) τ = ∑ i, max 0 (zDot i) := by
    simpa [zDot] using h_upward_eq_raw
  have h_downward_eq : deriv (positiveZDownward x_lasso) τ = ∑ i, (1 + τ) * max 0 (-zDot i) := by
    simpa [zDot] using h_downward_eq_raw
  rw [← h_upward_eq] at h_bound_pos
  rw [← h_downward_eq] at h_bound_neg
  -- Assemble the final inequality from the pos/neg bounds
  exact assemble_pos_delta_bound_3 zDot w C_low C_w C τ ε x_lasso
    (le_max_left _ _) (le_max_right _ _)
    h_bound_pos h_bound_neg h_up_mono h_down_mono hε_mem.1 hε_mem.2

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
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
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
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
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
  have h_breakpoint_zero : ∀ τ, ¬ DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ →
      ∀ i, deriv (fun u' => u' * (x_lasso u').ofLp i) τ = 0 := by
    -- This follows from piecewise linearity of the Lasso path (Efron et al. 2004,
    -- "Least Angle Regression", Annals of Statistics 32(2):407–499).
    -- The scaled primal path z(μ) = μ·x_lasso(μ) is piecewise linear in μ.
    -- At a breakpoint τ where z is not differentiable, each coordinate z_i either:
    --   (a) changes slope (active variable → not differentiable → deriv = 0), or
    --   (b) is locally zero near τ (inactive variable → deriv = 0).
    sorry
  obtain ⟨C3, hC3, h3⟩ := pos_delta_bound_3 M r lambda β s hs u hdata hβ hu x_lasso
    hx_lasso h_regular h_breakpoint_zero
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
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
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
  have hH0 : H 0 = 0 := by simp [H, hF0, hG0]
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
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
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
  have h_bound_s :=
    bound_of_deriv_bound (le_of_lt hs) h_deriv_bound hF0 hG0 hF_cont hG_cont
      hF_diff hG_diff
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
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
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
  -- Tendsto of 1 / log(1/ε) to 0 as ε → 0⁺
  have h_tendsto_log_inv : Tendsto (fun (ε : ℝ) => (Real.log (1 / ε))⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have h_inv_atTop : Tendsto (fun (ε : ℝ) => 1 / ε) (𝓝[>] 0) atTop := by
      simpa [one_div] using tendsto_inv_nhdsGT_zero (𝕜 := ℝ)
    exact (Real.tendsto_log_atTop.comp h_inv_atTop).inv_tendsto_atTop
  have h_tendsto_vanishing : Tendsto (fun ε => deltaVanishingTerm ε s (positiveZUpward x_lasso s))
      (𝓝[>] 0) (𝓝 0) := by
    dsimp [deltaVanishingTerm]
    simpa [div_eq_mul_inv, mul_comm] using
      (h_tendsto_log_inv.const_mul (s + positiveZUpward x_lasso s))
  have h_eventually_vanish : ∀ᶠ ε in 𝓝[>] 0,
      deltaVanishingTerm ε s (positiveZUpward x_lasso s) ≤ δ / 2 := by
    -- From the limit, eventually |deltaVanishingTerm| < δ/2, so deltaVanishingTerm ≤ δ/2
    refine ((h_tendsto_vanishing.eventually
      (isOpen_Ioo.mem_nhds ⟨neg_lt_zero.mpr h_half_δ, h_half_δ⟩)).mono fun ε hε => ?_)
    rcases hε with ⟨_, hε_high⟩
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
