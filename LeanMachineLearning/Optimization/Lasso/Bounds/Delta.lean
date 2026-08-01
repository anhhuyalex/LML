/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Lasso.Definitions
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! ## Section 4.6: positive-path estimate chain -/

@[expose] public section

namespace Lasso

open Filter Topology MeasureTheory
open scoped InnerProductSpace
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
Chain rule for `pathDelta`: differentiating the `M`-seminorm quadratic form
`Δ(σ) = (1/2) ‖zε(σ) - z(σ)‖_M^2` gives `⟨zε'(τ) - z'(τ), M(zε(τ) - z(τ))⟩`, using that
`M` is symmetric so the two cross terms of the product rule combine into a factor of `2`.

Informal proof: write `Δ = (1/2) * Q ∘ v` where `v = zε - z` and `Q(x) = ⟨x, Mx⟩`. The
product rule for the (bilinear) inner product gives
`(Q ∘ v)'(τ) = ⟨v(τ), M v'(τ)⟩ + ⟨v'(τ), M v(τ)⟩`. Since `M` is symmetric,
`⟨v(τ), M v'(τ)⟩ = ⟨M v(τ), v'(τ)⟩ = ⟨v'(τ), M v(τ)⟩` (using `inner_matVec_comm_of_isSymm`
and symmetry of the real inner product), so `(Q ∘ v)'(τ) = 2 ⟨v'(τ), M v(τ)⟩` and
`Δ'(τ) = ⟨v'(τ), M v(τ)⟩ = ⟨zε'(τ) - z'(τ), M(zε(τ) - z(τ))⟩`.
(Source: standard product rule for the symmetric bilinear form associated to a quadratic
form, e.g. https://en.wikipedia.org/wiki/Quadratic_form#Associated_symmetric_bilinear_form)
-/
lemma pathDelta_hasDerivAt
    (M : Matrix ι ι ℝ) (hM : M.IsSymm) (zε z : ℝ → EuclideanSpace ℝ ι)
    (Dε Dz : EuclideanSpace ℝ ι) (τ : ℝ)
    (hzε : HasDerivAt zε Dε τ) (hz : HasDerivAt z Dz τ) :
    HasDerivAt (fun σ => pathDelta M zε z σ)
      (inner ℝ (Dε - Dz) (matVec M (zε τ - z τ))) τ := by
  have hv : HasDerivAt (fun σ => zε σ - z σ) (Dε - Dz) τ := hzε.sub hz
  have hMv : HasDerivAt (fun σ => matVec M (zε σ - z σ)) (matVec M (Dε - Dz)) τ :=
    matVec_hasDerivAt M (fun σ => zε σ - z σ) (Dε - Dz) τ hv
  have h_symm : inner ℝ (zε τ - z τ) (matVec M (Dε - Dz)) =
      inner ℝ (Dε - Dz) (matVec M (zε τ - z τ)) := by
    rw [inner_matVec_comm_of_isSymm M hM (zε τ - z τ) (Dε - Dz), real_inner_comm]
  have hQ : HasDerivAt (fun σ => inner ℝ (zε σ - z σ) (matVec M (zε σ - z σ)))
      (2 * inner ℝ (Dε - Dz) (matVec M (zε τ - z τ))) τ := by
    have h := hv.inner ℝ hMv
    rw [h_symm] at h
    rwa [show (2 : ℝ) * inner ℝ (Dε - Dz) (matVec M (zε τ - z τ)) =
        inner ℝ (Dε - Dz) (matVec M (zε τ - z τ)) +
          inner ℝ (Dε - Dz) (matVec M (zε τ - z τ)) from by ring]
  have h_eq : (fun σ => pathDelta M zε z σ) =
      fun σ => (1 / 2 : ℝ) * inner ℝ (zε σ - z σ) (matVec M (zε σ - z σ)) := by
    funext σ; rfl
  rw [h_eq]
  have h_final := hQ.const_mul (1 / 2 : ℝ)
  rwa [show (1 / 2 : ℝ) * (2 * inner ℝ (Dε - Dz) (matVec M (zε τ - z τ))) =
      inner ℝ (Dε - Dz) (matVec M (zε τ - z τ)) by ring] at h_final

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
lemma posIntegratedTrajectoryRescaled_hasDerivAt
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
    (β : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (_hdata : ProblemData M r lambda) (_hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε)) :
    ∃ C > 0, ∀ s : ℝ, 0 < s → ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        inner ℝ (deriv (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) τ)
          (posRescaledMirrorVariable ε (u ε) τ)
        ≤ C / Real.log (1 / ε) := by
  set C := max 1 (Fintype.card ι : ℝ)
  refine ⟨C, lt_max_of_lt_left (by norm_num), fun s _hs => ?_⟩
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
    (β : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε)) :
    ∃ X > 0, ∀ s : ℝ, 0 < s → ∀ᶠ ε in 𝓝[>] 0, ∀ τ ∈ Set.Icc (0 : ℝ) s,
      ∀ i, posEffectiveParameter (u ε) (posTimeFromRescaled ε τ) i ≤ X := by
  obtain ⟨C, ε₀, hCpos, hε₀pos, hbound⟩ :=
    pos_trajectory_uniform_bound M r lambda β u hdata hβ hu
  -- Shrink ε₀ to also be ≤ 1, so that log(1/ε) ≥ 0 for the rescaled time.
  set ε₁ := min ε₀ 1
  have hε₁pos : 0 < ε₁ := lt_min hε₀pos one_pos
  refine ⟨C, hCpos, fun s _hs => ?_⟩
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
    (X : ℝ) (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hX_ev : ∀ s : ℝ, 0 < s → ∀ᶠ ε in 𝓝[>] 0, ∀ τ ∈ Set.Icc (0 : ℝ) s,
      ∀ i, posEffectiveParameter (u ε) (posTimeFromRescaled ε τ) i ≤ X)
    (hu_pos : ∀ ε > 0, ∀ t i, posEffectiveParameter (u ε) t i ≠ 0) :
    ∃ C_low > 0, ∀ s : ℝ, 0 < s → ∀ᶠ ε in 𝓝[>] 0, ∀ τ ∈ Set.Icc (0 : ℝ) s,
      ∀ i, -C_low / Real.log (1 / ε) ≤ posRescaledMirrorVariable ε (u ε) τ i := by
  set C_low := max 1 (Real.log X)
  refine ⟨C_low, lt_max_of_lt_left (by norm_num : (0 : ℝ) < 1), fun s hs => ?_⟩
  -- Intersect the uniform upper bound with ε ∈ (0,1) so that log(1/ε) > 0
  filter_upwards [hX_ev s hs, show Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) from by
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
    (β : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (hu_pos : ∀ ε > 0, ∀ t i, posEffectiveParameter (u ε) t i ≠ 0)
    (X : ℝ) (hX_pos : 0 < X)
    (hX_ev : ∀ s : ℝ, 0 < s → ∀ᶠ ε in 𝓝[>] 0, ∀ τ ∈ Set.Icc (0 : ℝ) s,
      ∀ i, posEffectiveParameter (u ε) (posTimeFromRescaled ε τ) i ≤ X) :
    ∃ C_w > 0, ∀ s : ℝ, 0 < s → ∀ᶠ ε in 𝓝[>] 0, ∀ τ ∈ Set.Icc (0 : ℝ) s,
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
      refine ⟨C_w, lt_max_of_lt_left hC_init_pos, fun s hs => ?_⟩
      -- Step 3: Restrict ε to a small enough neighborhood
      filter_upwards [hX_ev s hs, show Set.Ioo (0 : ℝ) (1/2) ∈ 𝓝[>] (0 : ℝ) from by
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
      refine ⟨1, by norm_num, fun s _hs => ?_⟩
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
    (h_up_nonneg : 0 ≤ deriv (positiveZUpward x_lasso) τ)
    (h_down_nonneg : 0 ≤ deriv (positiveZDownward x_lasso) τ)
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
        h_up_nonneg
        h_down_nonneg
        (Real.log_pos (one_lt_one_div hε_pos hε_lt_one))

-- Helper: integrability of max(0, deriv f_i) on [0,τ] follows from absolute continuity
-- of the scaled primal path. Uses that coordinate projections are 1-Lipschitz.
private lemma max_zero_deriv_intervalIntegrable
    (x_lasso : ℝ → EuclideanSpace ℝ ι) (i : ι) (τ : ℝ) (hτ : 0 ≤ τ)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    IntervalIntegrable (fun u => max 0 (deriv (fun u' => u' * (x_lasso u').ofLp i) u))
      volume 0 τ := by
  set f_i := fun (u' : ℝ) => u' * (x_lasso u').ofLp i
  set g_i := fun (u : ℝ) => max 0 (deriv f_i u)
  -- scaledPrimalPath is AC on [0, τ] by h_regular (since 0 ≤ τ)
  have h_ac_vec : AbsolutelyContinuousOnInterval (scaledPrimalPath x_lasso) 0 τ :=
    h_regular.absolutelyContinuousOn_Icc 0 τ (le_refl 0) hτ
  -- The coordinate projection is 1-Lipschitz, so f_i is also AC on [0, τ]
  have h_ac_fi : AbsolutelyContinuousOnInterval f_i 0 τ := by
    rw [absolutelyContinuousOnInterval_iff] at h_ac_vec ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h_ac_vec ε hε
    refine ⟨δ, hδ, ?_⟩
    intro E hE hlen
    apply lt_of_le_of_lt ?_ (hδ' E hE hlen)
    refine Finset.sum_le_sum (fun j hj => ?_)
    -- For each interval, coordinate difference is bounded by the Euclidean distance
    dsimp [f_i]
    have h_coord : |((scaledPrimalPath x_lasso) (E.2 j).1).ofLp i -
                   ((scaledPrimalPath x_lasso) (E.2 j).2).ofLp i| ≤
                   dist ((scaledPrimalPath x_lasso) (E.2 j).1)
                        ((scaledPrimalPath x_lasso) (E.2 j).2) := by
      set a := (scaledPrimalPath x_lasso) (E.2 j).1
      set b := (scaledPrimalPath x_lasso) (E.2 j).2
      have h_sq : ((a - b) i)^2 ≤ ‖a - b‖^2 := by
        have h_eq_sq : ((a - b) i)^2 = ‖(a - b) i‖ ^ 2 := by simp
        rw [h_eq_sq, EuclideanSpace.norm_sq_eq]
        have hpos : ∀ k ∈ (Finset.univ : Finset ι), 0 ≤ ‖(a - b) k‖ ^ 2 :=
          fun k _ => by positivity
        exact Finset.single_le_sum hpos (Finset.mem_univ i)
      have h_nonneg_norm : 0 ≤ ‖a - b‖ := norm_nonneg _
      calc
        |a.ofLp i - b.ofLp i| = |(a - b).ofLp i| := by simp
        _ = |(a - b) i| := rfl
        _ = Real.sqrt (((a - b) i)^2) := by rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt (‖a - b‖^2) := Real.sqrt_le_sqrt h_sq
        _ = ‖a - b‖ := Real.sqrt_sq h_nonneg_norm
        _ = dist a b := by rw [dist_eq_norm]
    exact h_coord
  -- Since f_i is AC, its derivative is interval integrable on [0, τ]
  have h_int_deriv : IntervalIntegrable (deriv f_i) volume 0 τ :=
    AbsolutelyContinuousOnInterval.intervalIntegrable_deriv h_ac_fi
  -- g_i = max(0, deriv f_i) = (deriv f_i + |deriv f_i|)/2
  have h_g_eq : g_i = fun u => ((deriv f_i u) + |deriv f_i u|) / 2 := by
    ext u
    dsimp [g_i]
    by_cases hpos : 0 ≤ deriv f_i u
    · rw [max_eq_right hpos, abs_of_nonneg hpos]
      ring
    · have hneg : deriv f_i u ≤ 0 := le_of_lt (lt_of_not_ge hpos)
      rw [max_eq_left hneg, abs_of_neg (lt_of_not_ge hpos)]
      ring
  rw [h_g_eq]
  -- IntervalIntegrable is closed under addition, absolute value, and scalar multiplication
  have h_temp : IntervalIntegrable
    (fun u => ((deriv f_i u) + |deriv f_i u|) * (1/2 : ℝ)) volume 0 τ :=
    ((h_int_deriv.add h_int_deriv.abs).mul_const (1/2 : ℝ))
  -- Convert * (1/2) to / 2
  have h_eq : (fun u => ((deriv f_i u) + |deriv f_i u|) / 2) =
             (fun u => ((deriv f_i u) + |deriv f_i u|) * (1/2 : ℝ)) := by
    ext u; rw [div_eq_mul_one_div]
  rw [h_eq]
  exact h_temp

private lemma max_zero_neg_deriv_intervalIntegrable
    (x_lasso : ℝ → EuclideanSpace ℝ ι) (i : ι) (τ : ℝ) (hτ : 0 ≤ τ)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    IntervalIntegrable (fun u => max 0 (-deriv (fun u' => u' * (x_lasso u').ofLp i) u))
      volume 0 τ := by
  set f_i := fun (u' : ℝ) => u' * (x_lasso u').ofLp i
  have h_ac_vec : AbsolutelyContinuousOnInterval (scaledPrimalPath x_lasso) 0 τ :=
    h_regular.absolutelyContinuousOn_Icc 0 τ (le_refl 0) hτ
  have h_ac_fi : AbsolutelyContinuousOnInterval f_i 0 τ := by
    rw [absolutelyContinuousOnInterval_iff] at h_ac_vec ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h_ac_vec ε hε
    refine ⟨δ, hδ, ?_⟩
    intro E hE hlen
    apply lt_of_le_of_lt ?_ (hδ' E hE hlen)
    refine Finset.sum_le_sum (fun j hj => ?_)
    dsimp [f_i]
    set a := (scaledPrimalPath x_lasso) (E.2 j).1
    set b := (scaledPrimalPath x_lasso) (E.2 j).2
    have h_sq : ((a - b) i)^2 ≤ ‖a - b‖^2 := by
      rw [show ((a - b) i)^2 = ‖(a - b) i‖ ^ 2 by simp, EuclideanSpace.norm_sq_eq]
      have hpos : ∀ k ∈ (Finset.univ : Finset ι), 0 ≤ ‖(a - b) k‖ ^ 2 :=
        fun k _ => by positivity
      exact Finset.single_le_sum hpos (Finset.mem_univ i)
    calc
      |a.ofLp i - b.ofLp i| = |(a - b) i| := by simp
      _ = Real.sqrt (((a - b) i)^2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt (‖a - b‖^2) := Real.sqrt_le_sqrt h_sq
      _ = ‖a - b‖ := Real.sqrt_sq (norm_nonneg _)
      _ = dist a b := by rw [dist_eq_norm]
  have h_int_deriv : IntervalIntegrable (deriv f_i) volume 0 τ :=
    h_ac_fi.intervalIntegrable_deriv
  have h_eq : (fun u => max 0 (-deriv f_i u)) =
      fun u => (|deriv f_i u| - deriv f_i u) / 2 := by
    funext u
    rcases le_total 0 (deriv f_i u) with hu | hu
    · rw [abs_of_nonneg hu, max_eq_left (neg_nonpos.mpr hu)]
      ring
    · rw [abs_of_nonpos hu, max_eq_right (neg_nonneg.mpr hu)]
      ring
  rw [h_eq]
  exact (h_int_deriv.abs.sub h_int_deriv).div_const 2

/--
Differentiability of a single `positiveZUpward` summand at a point where the
underlying coordinate derivative is locally constant near `τ`.  Factored out of
the FTC step of `deriv_pos_z_identities` so that it can also be used to prove
plain a.e. differentiability of `positiveZUpward` (`positiveZ_ae_differentiable`)
without recomputing the actual derivative value.
-/
private lemma positiveZUpward_summand_differentiableAt
    (x_lasso : ℝ → EuclideanSpace ℝ ι) (τ : ℝ) (hτ : 0 ≤ τ) (i : ι)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_const : ∃ ε > 0, ∀ t, |t - τ| < ε →
        deriv (fun u' => u' * (x_lasso u').ofLp i) t =
        deriv (fun u' => u' * (x_lasso u').ofLp i) τ) :
    DifferentiableAt ℝ (fun μ => ∫ u in (0 : ℝ)..μ,
      max 0 (deriv (fun u' => u' * (x_lasso u').ofLp i) u)) τ := by
  set f_i := fun (u' : ℝ) => u' * (x_lasso u').ofLp i
  set g_i := fun (u : ℝ) => max 0 (deriv f_i u)
  obtain ⟨ε, hε_pos, h_const⟩ := h_const
  have h_g_const : ∀ t, |t - τ| < ε → g_i t = g_i τ := by
    intro t ht; dsimp [g_i]; rw [h_const t ht]
  have h_cont : ContinuousAt g_i τ := by
    have h_event : ∀ᶠ t in 𝓝 τ, g_i t = g_i τ := by
      rw [Metric.eventually_nhds_iff_ball]
      exact ⟨ε, hε_pos, fun t ht => h_g_const t (Metric.mem_ball.mp ht)⟩
    have h_eventEq : g_i =ᶠ[𝓝 τ] (fun _ => g_i τ) := h_event
    exact h_eventEq.continuousAt
  have h_meas : StronglyMeasurableAtFilter g_i (𝓝 τ) := by
    refine ⟨Metric.ball τ ε, Metric.ball_mem_nhds τ hε_pos, ?_⟩
    have h_eq_on : (Metric.ball τ ε).EqOn g_i (fun _ => g_i τ) := fun t ht =>
      h_g_const t (Metric.mem_ball.mp ht)
    exact (aestronglyMeasurable_const (b := g_i τ)).congr
      (h_eq_on.aeEq_restrict Metric.isOpen_ball.measurableSet).symm
  have h_int : IntervalIntegrable g_i volume 0 τ := by
    dsimp [g_i, f_i]
    exact max_zero_deriv_intervalIntegrable x_lasso i τ hτ h_regular
  exact (intervalIntegral.integral_hasDerivAt_right h_int h_meas h_cont).differentiableAt

/-- Downward counterpart of `positiveZUpward_summand_differentiableAt`. -/
private lemma positiveZDownward_summand_differentiableAt
    (x_lasso : ℝ → EuclideanSpace ℝ ι) (τ : ℝ) (hτ : 0 ≤ τ) (i : ι)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_const : ∃ ε > 0, ∀ t, |t - τ| < ε →
        deriv (fun u' => u' * (x_lasso u').ofLp i) t =
        deriv (fun u' => u' * (x_lasso u').ofLp i) τ) :
    DifferentiableAt ℝ (fun μ => ∫ u in (0 : ℝ)..μ,
      (1 + u) * max 0 (-deriv (fun u' => u' * (x_lasso u').ofLp i) u)) τ := by
  set f_i := fun (u' : ℝ) => u' * (x_lasso u').ofLp i
  set g_i := fun (u : ℝ) => (1 + u) * max 0 (-deriv f_i u)
  obtain ⟨ε, hε_pos, h_const⟩ := h_const
  let c := max 0 (-deriv f_i τ)
  have h_g_eq : ∀ t, |t - τ| < ε → g_i t = (1 + t) * c := by
    intro t ht
    dsimp [g_i, c]
    rw [h_const t ht]
  have h_event : g_i =ᶠ[𝓝 τ] (fun t => (1 + t) * c) := by
    filter_upwards [Metric.ball_mem_nhds τ hε_pos] with t ht
    exact h_g_eq t (Metric.mem_ball.mp ht)
  have h_cont : ContinuousAt g_i τ :=
    (continuousAt_congr h_event).mpr (by fun_prop)
  have h_meas : StronglyMeasurableAtFilter g_i (𝓝 τ) := by
    refine ⟨Metric.ball τ ε, Metric.ball_mem_nhds τ hε_pos, ?_⟩
    have h_comp : AEStronglyMeasurable (fun t : ℝ => (1 + t) * c)
        (volume.restrict (Metric.ball τ ε)) :=
      (by fun_prop : Continuous (fun t : ℝ => (1 + t) * c)).aestronglyMeasurable
    have h_eq_on : (Metric.ball τ ε).EqOn g_i (fun t => (1 + t) * c) :=
      fun t ht => h_g_eq t (Metric.mem_ball.mp ht)
    exact h_comp.congr
      (h_eq_on.aeEq_restrict Metric.isOpen_ball.measurableSet).symm
  have h_int_neg : IntervalIntegrable (fun u => max 0 (-deriv f_i u)) volume 0 τ := by
    dsimp [f_i]
    exact max_zero_neg_deriv_intervalIntegrable x_lasso i τ hτ h_regular
  have h_int : IntervalIntegrable g_i volume 0 τ := by
    dsimp [g_i]
    exact h_int_neg.continuousOn_mul (by fun_prop)
  exact (intervalIntegral.integral_hasDerivAt_right h_int h_meas h_cont).differentiableAt

-- Extract the FTC/monotonicity block: relates derivatives of positiveZUpward/positiveZDownward
-- to sums over coordinate derivatives, and establishes monotonicity of both functions.
-- Uses piecewise linearity of the Lasso path (Efron et al. 2004) and the Fundamental Theorem
-- of Calculus.
private lemma deriv_pos_z_identities
    (x_lasso : ℝ → EuclideanSpace ℝ ι) (τ : ℝ) (hτ : 0 ≤ τ)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_piecewise_deriv : ∀ (τ' : ℝ) (i' : ι), 0 ≤ τ' →
        DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ' →
        ∃ ε > 0, ∀ t, |t - τ'| < ε →
          deriv (fun u' => u' * (x_lasso u').ofLp i') t =
          deriv (fun u' => u' * (x_lasso u').ofLp i') τ')
    (h_path_diff : DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ) :
    deriv (positiveZUpward x_lasso) τ = ∑ i, max 0 ((deriv (scaledPrimalPath x_lasso) τ) i) ∧
    deriv (positiveZDownward x_lasso) τ =
      ∑ i, (1 + τ) * max 0 (-((deriv (scaledPrimalPath x_lasso) τ) i)) := by
  -- Step 1 (componentwise identification):
  --   (deriv (scaledPrimalPath x_lasso) τ) i = deriv (fun u' => u' * x_lasso u' i) τ
  have h_component : ∀ i, (deriv (scaledPrimalPath x_lasso) τ) i =
      deriv (fun u' => u' * x_lasso u' i) τ := by
    intro i
    let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) :=
      (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv
    simpa [scaledPrimalPath, e, PiLp.smul_apply, smul_eq_mul] using
      ((hasDerivAt_pi.1 (e.hasFDerivAt.comp_hasDerivAt τ h_path_diff.hasDerivAt)) i).deriv.symm
  have h_ftc_up : ∀ i, deriv (fun (μ : ℝ) => ∫ u in (0 : ℝ)..μ,
      max 0 (deriv (fun u' => u' * x_lasso u' i) u)) τ =
      max 0 (deriv (fun u' => u' * x_lasso u' i) τ) := by
    intro i
    set f_i := fun (u' : ℝ) => u' * (x_lasso u').ofLp i
    set g_i := fun (u : ℝ) => max 0 (deriv f_i u)
    rcases h_piecewise_deriv τ i hτ h_path_diff with ⟨ε, hε_pos, h_const⟩
    have h_g_const : ∀ t, |t - τ| < ε → g_i t = g_i τ := by
      intro t ht
      dsimp [g_i]
      rw [h_const t ht]
    have h_cont : ContinuousAt g_i τ := by
      have h_event : ∀ᶠ t in 𝓝 τ, g_i t = g_i τ := by
        rw [Metric.eventually_nhds_iff_ball]
        exact ⟨ε, hε_pos, fun t ht => h_g_const t (Metric.mem_ball.mp ht)⟩
      have h_eventEq : g_i =ᶠ[𝓝 τ] (fun _ => g_i τ) := h_event
      exact h_eventEq.continuousAt
    have h_meas : StronglyMeasurableAtFilter g_i (𝓝 τ) := by
      refine ⟨Metric.ball τ ε, Metric.ball_mem_nhds τ hε_pos, ?_⟩
      have h_eq_on : (Metric.ball τ ε).EqOn g_i (fun _ => g_i τ) := fun t ht =>
        h_g_const t (Metric.mem_ball.mp ht)
      exact (aestronglyMeasurable_const (b := g_i τ)).congr
        (h_eq_on.aeEq_restrict Metric.isOpen_ball.measurableSet).symm
    have h_int : IntervalIntegrable g_i volume 0 τ := by
      dsimp [g_i, f_i]
      exact max_zero_deriv_intervalIntegrable x_lasso i τ hτ h_regular
    rw [intervalIntegral.deriv_integral_right h_int h_meas h_cont]
  -- Step 3 (FTC for the downward variation):
  have h_ftc_down : ∀ i, deriv (fun (μ : ℝ) => ∫ u in (0 : ℝ)..μ,
      (1 + u) * max 0 (-deriv (fun u' => u' * x_lasso u' i) u)) τ =
      (1 + τ) * max 0 (-deriv (fun u' => u' * x_lasso u' i) τ) := by
    intro i
    set f_i := fun (u' : ℝ) => u' * (x_lasso u').ofLp i
    set g_i := fun (u : ℝ) => (1 + u) * max 0 (-deriv f_i u)
    rcases h_piecewise_deriv τ i hτ h_path_diff with ⟨ε, hε_pos, h_const⟩
    let c := max 0 (-deriv f_i τ)
    have h_g_eq : ∀ t, |t - τ| < ε → g_i t = (1 + t) * c := by
      intro t ht
      dsimp [g_i, c]
      rw [h_const t ht]
    have h_event : g_i =ᶠ[𝓝 τ] (fun t => (1 + t) * c) := by
      filter_upwards [Metric.ball_mem_nhds τ hε_pos] with t ht
      exact h_g_eq t (Metric.mem_ball.mp ht)
    have h_cont : ContinuousAt g_i τ :=
      (continuousAt_congr h_event).mpr (by fun_prop)
    have h_meas : StronglyMeasurableAtFilter g_i (𝓝 τ) := by
      refine ⟨Metric.ball τ ε, Metric.ball_mem_nhds τ hε_pos, ?_⟩
      have h_comp : AEStronglyMeasurable (fun t : ℝ => (1 + t) * c)
          (volume.restrict (Metric.ball τ ε)) :=
        (by fun_prop : Continuous (fun t : ℝ => (1 + t) * c)).aestronglyMeasurable
      have h_eq_on : (Metric.ball τ ε).EqOn g_i (fun t => (1 + t) * c) :=
        fun t ht => h_g_eq t (Metric.mem_ball.mp ht)
      exact h_comp.congr
        (h_eq_on.aeEq_restrict Metric.isOpen_ball.measurableSet).symm
    have h_int_neg : IntervalIntegrable (fun u => max 0 (-deriv f_i u)) volume 0 τ := by
      dsimp [f_i]
      exact max_zero_neg_deriv_intervalIntegrable x_lasso i τ hτ h_regular
    have h_int : IntervalIntegrable g_i volume 0 τ := by
      dsimp [g_i]
      exact h_int_neg.continuousOn_mul (by fun_prop)
    simpa [g_i, c] using
      (intervalIntegral.integral_hasDerivAt_right h_int h_meas h_cont).deriv
  -- Step 4 (distribute deriv over finite sum):
  --   deriv (∑_i F_i) τ = ∑_i deriv F_i τ
  -- At the regular point τ, local constancy of each coordinate derivative and the
  -- FTC make every F_i differentiable, so `deriv_fun_sum` applies.
  have h_deriv_sum : deriv (fun (μ : ℝ) => ∑ i : ι,
      ∫ u in (0 : ℝ)..μ, max 0 (deriv (fun u' => u' * x_lasso u' i) u)) τ =
      ∑ i : ι, deriv (fun (μ : ℝ) => ∫ u in (0 : ℝ)..μ,
        max 0 (deriv (fun u' => u' * x_lasso u' i) u)) τ := by
    apply deriv_fun_sum
    intro i _
    set f_i := fun (u' : ℝ) => u' * (x_lasso u').ofLp i
    set g_i := fun (u : ℝ) => max 0 (deriv f_i u)
    rcases h_piecewise_deriv τ i hτ h_path_diff with ⟨ε, hε_pos, h_const⟩
    have h_g_const : ∀ t, |t - τ| < ε → g_i t = g_i τ := by
      intro t ht
      dsimp [g_i]
      rw [h_const t ht]
    have h_cont : ContinuousAt g_i τ := by
      have h_event : ∀ᶠ t in 𝓝 τ, g_i t = g_i τ := by
        rw [Metric.eventually_nhds_iff_ball]
        exact ⟨ε, hε_pos, fun t ht => h_g_const t (Metric.mem_ball.mp ht)⟩
      have h_eventEq : g_i =ᶠ[𝓝 τ] (fun _ => g_i τ) := h_event
      exact h_eventEq.continuousAt
    have h_meas : StronglyMeasurableAtFilter g_i (𝓝 τ) := by
      refine ⟨Metric.ball τ ε, Metric.ball_mem_nhds τ hε_pos, ?_⟩
      have h_eq_on : (Metric.ball τ ε).EqOn g_i (fun _ => g_i τ) := fun t ht =>
        h_g_const t (Metric.mem_ball.mp ht)
      exact (aestronglyMeasurable_const (b := g_i τ)).congr
        (h_eq_on.aeEq_restrict Metric.isOpen_ball.measurableSet).symm
    have h_int : IntervalIntegrable g_i volume 0 τ := by
      dsimp [g_i, f_i]
      exact max_zero_deriv_intervalIntegrable x_lasso i τ hτ h_regular
    exact (intervalIntegral.integral_hasDerivAt_right h_int h_meas h_cont).differentiableAt
  have h_deriv_sum_down : deriv (fun (μ : ℝ) => ∑ i : ι,
      ∫ u in (0 : ℝ)..μ, (1 + u) * max 0 (-deriv (fun u' => u' * x_lasso u' i) u)) τ =
      ∑ i : ι, deriv (fun (μ : ℝ) => ∫ u in (0 : ℝ)..μ,
        (1 + u) * max 0 (-deriv (fun u' => u' * x_lasso u' i) u)) τ := by
    apply deriv_fun_sum
    intro i _
    set f_i := fun (u' : ℝ) => u' * (x_lasso u').ofLp i
    set g_i := fun (u : ℝ) => (1 + u) * max 0 (-deriv f_i u)
    rcases h_piecewise_deriv τ i hτ h_path_diff with ⟨ε, hε_pos, h_const⟩
    let c := max 0 (-deriv f_i τ)
    have h_g_eq : ∀ t, |t - τ| < ε → g_i t = (1 + t) * c := by
      intro t ht
      dsimp [g_i, c]
      rw [h_const t ht]
    have h_event : g_i =ᶠ[𝓝 τ] (fun t => (1 + t) * c) := by
      filter_upwards [Metric.ball_mem_nhds τ hε_pos] with t ht
      exact h_g_eq t (Metric.mem_ball.mp ht)
    have h_cont : ContinuousAt g_i τ :=
      (continuousAt_congr h_event).mpr (by fun_prop)
    have h_meas : StronglyMeasurableAtFilter g_i (𝓝 τ) := by
      refine ⟨Metric.ball τ ε, Metric.ball_mem_nhds τ hε_pos, ?_⟩
      have h_comp : AEStronglyMeasurable (fun t : ℝ => (1 + t) * c)
          (volume.restrict (Metric.ball τ ε)) :=
        (by fun_prop : Continuous (fun t : ℝ => (1 + t) * c)).aestronglyMeasurable
      have h_eq_on : (Metric.ball τ ε).EqOn g_i (fun t => (1 + t) * c) :=
        fun t ht => h_g_eq t (Metric.mem_ball.mp ht)
      exact h_comp.congr
        (h_eq_on.aeEq_restrict Metric.isOpen_ball.measurableSet).symm
    have h_int_neg : IntervalIntegrable (fun u => max 0 (-deriv f_i u)) volume 0 τ := by
      dsimp [f_i]
      exact max_zero_neg_deriv_intervalIntegrable x_lasso i τ hτ h_regular
    have h_int : IntervalIntegrable g_i volume 0 τ := by
      dsimp [g_i]
      exact h_int_neg.continuousOn_mul (by fun_prop)
    exact (intervalIntegral.integral_hasDerivAt_right h_int h_meas h_cont).differentiableAt
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
  exact ⟨h_upward_eq, h_downward_eq⟩

/--
Composing an absolutely continuous curve with a Lipschitz map preserves absolute continuity.

We need this because Mathlib's `AbsolutelyContinuousOnInterval.ae_differentiableAt` is stated
only for `ℝ`-valued curves (`MeasureTheory.Function.AbsolutelyContinuous`), while the Lasso
path lives in the vector space `EuclideanSpace ℝ ι`. Directly feeding a vector-valued
`AbsolutelyContinuousOnInterval` hypothesis into that scalar-only lemma is a type mismatch;
attempting it forces Lean into an expensive, ultimately failing unification search (this is
what caused the `whnf` timeout here previously — the fix is this coordinate-wise reduction,
not a larger heartbeat budget). Projecting onto a single coordinate is `1`-Lipschitz, so
composing with it turns the vector-valued absolute continuity of `f` into scalar-valued
absolute continuity of `g ∘ f`, to which `ae_differentiableAt` applies.

Informal proof: absolute continuity is characterized by `∑ dist (f aᵢ) (f bᵢ) → 0` as the total
length `∑ dist aᵢ bᵢ → 0`. Since `g` is `K`-Lipschitz,
`∑ dist (g (f aᵢ)) (g (f bᵢ)) ≤ K * ∑ dist (f aᵢ) (f bᵢ) → 0`.
(Source: Lipschitz images of absolutely continuous functions are absolutely continuous; this is
the direct analogue of the standard fact that Lipschitz images of bounded-variation functions
have bounded variation, e.g. Royden & Fitzpatrick, *Real Analysis*, 4th ed., Ch. 5.)
-/
theorem _root_.LipschitzWith.comp_absolutelyContinuousOnInterval
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℝ → X} {g : X → Y} {K : NNReal} {a b : ℝ}
    (hg : LipschitzWith K g) (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (g ∘ f) a b := by
  have hf' : Tendsto
      (fun E : ℕ × (ℕ → ℝ × ℝ) ↦ ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 0) := hf
  apply squeeze_zero (fun _ ↦ Finset.sum_nonneg (fun _ _ ↦ dist_nonneg))
    (fun _ ↦ ?_) (by simpa using hf'.const_mul (K : ℝ))
  simp only [Function.comp_apply]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ ↦ hg.dist_le_mul _ _)

/-! ### Monotone-case closed forms for `positiveZUpward`/`positiveZDownward`

Under the monotonicity hypothesis of Theorem 3.1 (`docs/Lasso.md`, Sec. 3.1), the scaled path
`z(μ) = μ x(μ)` is coordinatewise nondecreasing on `[0,∞)`. Combined with `z` being locally
Lipschitz (Lemma 4.12, `locallyLipschitzOnCompacts_of_matVec_lipschitz`), Lebesgue's monotone
differentiation theorem gives `deriv z_i ≥ 0` a.e., from which `positiveZDownward` vanishes
identically and `positiveZUpward` equals `⟨𝟙, z⟩` exactly. These closed forms give
a.e.-differentiability of `positiveZUpward`/`positiveZDownward` (and the derivative identities
`deriv_pos_z_identities` provides in general) *without* the
`ScaledPrimalPathLocallyAffineAtDifferentiable` structural hypothesis, which `docs/Lasso.md`'s
Theorem 3.1 never assumes (its only extra hypothesis over Theorem 3.2 is monotonicity). -/

omit [Fintype ι] in
/-- If a coordinate of the scaled primal path is monotone nondecreasing on `[0,∞)` and
differentiable at `τ > 0`, its derivative there is nonnegative.

Informal proof: extend the coordinate to a function on all of `ℝ` that is monotone globally
(constant below `0`); it agrees with the original on the neighborhood `(0,∞)` of `τ`, so the
derivative is unchanged, and `HasDerivAt.nonneg_of_monotone` applies. -/
private lemma deriv_scaledPrimalPath_coord_nonneg_of_monotone
    (x_lasso : ℝ → EuclideanSpace ℝ ι) (i : ι) (τ : ℝ) (hτ : 0 < τ)
    (h_mono : ∀ μ ν, 0 ≤ μ → μ ≤ ν →
      (μ * (x_lasso μ).ofLp i) ≤ (ν * (x_lasso ν).ofLp i))
    (h_diff : DifferentiableAt ℝ (fun t => t * (x_lasso t).ofLp i) τ) :
    0 ≤ deriv (fun t => t * (x_lasso t).ofLp i) τ := by
  set g : ℝ → ℝ := fun t => t * (x_lasso t).ofLp i with hg_def
  set g_ext : ℝ → ℝ := fun t => if 0 ≤ t then g t else g 0 with hg_ext_def
  have hg_ext_mono : Monotone g_ext := by
    intro a b hab
    by_cases ha : 0 ≤ a
    · have hb : 0 ≤ b := ha.trans hab
      simp only [hg_ext_def, if_pos ha, if_pos hb]
      exact h_mono a b ha hab
    · by_cases hb : 0 ≤ b
      · simp only [hg_ext_def, if_neg ha, if_pos hb]
        exact h_mono 0 b le_rfl hb
      · simp only [hg_ext_def, if_neg ha, if_neg hb]
        exact le_refl _
  have heq : g_ext =ᶠ[𝓝 τ] g := by
    filter_upwards [eventually_gt_nhds hτ] with t ht
    simp only [hg_ext_def, if_pos ht.le]
  exact ((h_diff.hasDerivAt).congr_of_eventuallyEq heq).nonneg_of_monotone hg_ext_mono

/-- `positiveZDownward` vanishes identically on `[0, ∞)` when `z = scaledPrimalPath x_lasso`
is coordinatewise monotone nondecreasing there: the integrand `(1+u)·max 0 (-z_i'(u))`
vanishes a.e., since Lebesgue's monotone differentiation theorem gives `z_i' ≥ 0` a.e. -/
lemma positiveZDownward_eq_zero_of_monotone
    (x_lasso : ℝ → EuclideanSpace ℝ ι) (μ : ℝ) (hμ : 0 ≤ μ)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_mono : ∀ ν ν', 0 ≤ ν → ν ≤ ν' → ∀ i, ν * (x_lasso ν).ofLp i ≤ ν' * (x_lasso ν').ofLp i) :
    positiveZDownward x_lasso μ = 0 := by
  rcases eq_or_lt_of_le hμ with rfl | hμ_pos
  · simp [positiveZDownward]
  unfold positiveZDownward
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have h_ac : AbsolutelyContinuousOnInterval (fun t => t * (x_lasso t).ofLp i) 0 μ := by
    rw [show (fun t : ℝ => t * (x_lasso t).ofLp i) =
        (fun x : EuclideanSpace ℝ ι => x.ofLp i) ∘ scaledPrimalPath x_lasso from by
      funext t; simp [scaledPrimalPath, smul_eq_mul]]
    exact (LipschitzWith.of_dist_le_mul (K := 1) (fun x y => by
      simpa [dist_eq_norm] using PiLp.norm_apply_le (x - y) i)).comp_absolutelyContinuousOnInterval
      (h_regular.absolutelyContinuousOn_Icc 0 μ le_rfl hμ_pos.le)
  have h_ae_zero : ∀ᵐ u ∂volume, u ∈ Set.uIoc (0 : ℝ) μ →
      (1 + u) * max 0 (-deriv (fun t => t * (x_lasso t).ofLp i) u) = (0 : ℝ) := by
    rw [Set.uIoc_of_le hμ_pos.le]
    filter_upwards [h_ac.ae_differentiableAt] with u hdiff hu_mem
    rw [Set.uIcc_of_le hμ_pos.le] at hdiff
    have hu_deriv : 0 ≤ deriv (fun t => t * (x_lasso t).ofLp i) u :=
      deriv_scaledPrimalPath_coord_nonneg_of_monotone x_lasso i u hu_mem.1
        (fun a b ha hab => h_mono a b ha hab i) (hdiff ⟨hu_mem.1.le, hu_mem.2⟩)
    simp [max_eq_left (neg_nonpos.mpr hu_deriv)]
  rw [intervalIntegral.integral_congr_ae h_ae_zero, intervalIntegral.integral_zero]

/-- `positiveZUpward` equals `⟨𝟙, z⟩` on `[0, ∞)` when `z = scaledPrimalPath x_lasso` is
coordinatewise monotone nondecreasing there: the integrand `max 0 (z_i'(u))` equals `z_i'(u)`
a.e. (Lebesgue's monotone differentiation theorem), and FTC for the locally Lipschitz (hence
absolutely continuous) `z_i` gives `∫₀^μ z_i' = z_i(μ) - z_i(0) = z_i(μ)`. -/
lemma positiveZUpward_eq_sum_of_monotone
    (x_lasso : ℝ → EuclideanSpace ℝ ι) (μ : ℝ) (hμ : 0 ≤ μ)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_mono : ∀ ν ν', 0 ≤ ν → ν ≤ ν' → ∀ i, ν * (x_lasso ν).ofLp i ≤ ν' * (x_lasso ν').ofLp i) :
    positiveZUpward x_lasso μ = ∑ i, (scaledPrimalPath x_lasso μ) i := by
  rcases eq_or_lt_of_le hμ with rfl | hμ_pos
  · simp [positiveZUpward, scaledPrimalPath]
  unfold positiveZUpward
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h_ac : AbsolutelyContinuousOnInterval (fun t => t * (x_lasso t).ofLp i) 0 μ := by
    rw [show (fun t : ℝ => t * (x_lasso t).ofLp i) =
        (fun x : EuclideanSpace ℝ ι => x.ofLp i) ∘ scaledPrimalPath x_lasso from by
      funext t; simp [scaledPrimalPath, smul_eq_mul]]
    exact (LipschitzWith.of_dist_le_mul (K := 1) (fun x y => by
      simpa [dist_eq_norm] using PiLp.norm_apply_le (x - y) i)).comp_absolutelyContinuousOnInterval
      (h_regular.absolutelyContinuousOn_Icc 0 μ le_rfl hμ_pos.le)
  have h_eq_ae : ∀ᵐ u ∂volume, u ∈ Set.uIoc (0 : ℝ) μ →
      max 0 (deriv (fun t => t * (x_lasso t).ofLp i) u) =
        deriv (fun t => t * (x_lasso t).ofLp i) u := by
    rw [Set.uIoc_of_le hμ_pos.le]
    filter_upwards [h_ac.ae_differentiableAt] with u hdiff hu_mem
    rw [Set.uIcc_of_le hμ_pos.le] at hdiff
    have hu_deriv : 0 ≤ deriv (fun t => t * (x_lasso t).ofLp i) u :=
      deriv_scaledPrimalPath_coord_nonneg_of_monotone x_lasso i u hu_mem.1
        (fun a b ha hab => h_mono a b ha hab i) (hdiff ⟨hu_mem.1.le, hu_mem.2⟩)
    exact max_eq_right hu_deriv
  rw [intervalIntegral.integral_congr_ae h_eq_ae, h_ac.integral_deriv_eq_sub]
  simp [scaledPrimalPath, smul_eq_mul]

/--
Monotone-case analogue of `deriv_pos_z_identities`: the same derivative identities for
`positiveZUpward`/`positiveZDownward`, but derived from coordinatewise monotonicity of
`z = scaledPrimalPath x_lasso` on `[0,∞)` instead of the structural
`ScaledPrimalPathLocallyAffineAtDifferentiable` hypothesis (which `docs/Lasso.md`'s Theorem 3.1
never assumes — its only extra hypothesis over Theorem 3.2 is monotonicity, `docs/Lasso.md`
Sec. 3.1).

Informal proof: `positiveZDownward_eq_zero_of_monotone` and `positiveZUpward_eq_sum_of_monotone`
give the *closed forms* `positiveZDownward x_lasso ≡ 0` and `positiveZUpward x_lasso μ = ∑ i,
z_i μ` for all `μ ≥ 0`, i.e. as an equality of functions on `[0,∞)`, not merely a.e. Since `τ >
0`, both sides agree with these closed forms on the open neighbourhood `(0,∞)` of `τ`
(`Filter.EventuallyEq` on `𝓝 τ`), so `deriv (positiveZDownward x_lasso) τ = deriv (fun _ => 0)
τ = 0` and `deriv (positiveZUpward x_lasso) τ = deriv (fun μ => ∑ i, z_i μ) τ = ∑ i, deriv z_i
τ` (linearity of `deriv` over the finite sum, using `h_path_diff` to justify termwise
differentiation). Finally, `deriv_scaledPrimalPath_coord_nonneg_of_monotone` gives `deriv z_i τ
≥ 0` for each `i` (Lebesgue's monotone differentiation theorem via the two-sided extension
trick), so `max 0 (deriv z_i τ) = deriv z_i τ` and `max 0 (-deriv z_i τ) = 0`, matching the
target identities exactly. Citation: `docs/Lasso.md`, Sec. 3.1/4.7 (Lemma 4.12) and the
standard monotone differentiation theorem (Mathlib: `Monotone.ae_hasDerivAt`,
`Mathlib/Analysis/Calculus/Monotone.lean`).
-/
private lemma deriv_pos_z_identities_of_monotone
    (x_lasso : ℝ → EuclideanSpace ℝ ι) (τ : ℝ) (hτ : 0 < τ)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_mono : ∀ ν ν', 0 ≤ ν → ν ≤ ν' → ∀ i, ν * (x_lasso ν).ofLp i ≤ ν' * (x_lasso ν').ofLp i)
    (h_path_diff : DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ) :
    deriv (positiveZUpward x_lasso) τ = ∑ i, max 0 ((deriv (scaledPrimalPath x_lasso) τ) i) ∧
    deriv (positiveZDownward x_lasso) τ =
      ∑ i, (1 + τ) * max 0 (-((deriv (scaledPrimalPath x_lasso) τ) i)) := by
  -- Chain rule: derivative of each coordinate of the scaled primal path.
  -- Use the continuous linear equivalence `e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ)`
  -- (which strips the `PiLp` wrapper) and `hasDerivAt_pi` to extract coordinates.
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv
  have h_coord_hasDerivAt (i : ι) : HasDerivAt (fun t => (scaledPrimalPath x_lasso t) i)
      ((deriv (scaledPrimalPath x_lasso) τ) i) τ := by
    simpa [e] using (hasDerivAt_pi.1
      (e.hasFDerivAt.comp_hasDerivAt τ h_path_diff.hasDerivAt)) i
  have h_deriv_coord_eq (i : ι) : deriv (fun t => (scaledPrimalPath x_lasso t) i) τ =
      (deriv (scaledPrimalPath x_lasso) τ) i :=
    (h_coord_hasDerivAt i).deriv
  -- Relate the coordinate function `t * (x_lasso t).ofLp i` to `scaledPrimalPath t` at i
  have h_fn_eq (i : ι) : (fun t => t * (x_lasso t).ofLp i) =
      (fun t => (scaledPrimalPath x_lasso t) i) := by
    ext t; simp [scaledPrimalPath, smul_eq_mul]
  -- Nonnegativity of coordinate derivatives from coordinatewise monotonicity.
  -- Uses `deriv_scaledPrimalPath_coord_nonneg_of_monotone` and rewrites the result
  -- from `deriv (fun t => t * (x_lasso t).ofLp i) τ` to `(deriv (scaledPrimalPath x_lasso) τ) i`.
  have h_nonneg (i : ι) : 0 ≤ (deriv (scaledPrimalPath x_lasso) τ) i := by
    simpa [h_fn_eq i, h_deriv_coord_eq i] using
      deriv_scaledPrimalPath_coord_nonneg_of_monotone x_lasso i τ hτ
        (fun a b ha hab => h_mono a b ha hab i)
        (by rw [h_fn_eq i]; exact (h_coord_hasDerivAt i).differentiableAt)
  -- Closed forms on a neighborhood of τ (using that τ > 0, so (0,∞) is an open nhd of τ)
  -- These follow from `positiveZDownward_eq_zero_of_monotone` and
  -- `positiveZUpward_eq_sum_of_monotone` which are defined above.
  have h_down_closed_on_nhds : positiveZDownward x_lasso =ᶠ[𝓝 τ] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hτ] with μ hμ
    exact positiveZDownward_eq_zero_of_monotone x_lasso μ hμ.le h_regular h_mono
  have h_up_closed_on_nhds : positiveZUpward x_lasso =ᶠ[𝓝 τ]
      fun μ => ∑ i, (scaledPrimalPath x_lasso μ) i := by
    filter_upwards [isOpen_Ioi.mem_nhds hτ] with μ hμ
    exact positiveZUpward_eq_sum_of_monotone x_lasso μ hμ.le h_regular h_mono
  -- Combine with nonnegativity to match the max expressions in the goal
  have h_up_final : deriv (positiveZUpward x_lasso) τ =
      ∑ i, max 0 ((deriv (scaledPrimalPath x_lasso) τ) i) := by
    calc
      deriv (positiveZUpward x_lasso) τ = deriv (fun μ => ∑ i, (scaledPrimalPath x_lasso μ) i) τ :=
        h_up_closed_on_nhds.deriv_eq
      _ = ∑ i, (deriv (scaledPrimalPath x_lasso) τ) i := by
        simpa [Finset.sum_fn, h_deriv_coord_eq] using
          deriv_sum (fun i _ => (h_coord_hasDerivAt i).differentiableAt)
      _ = ∑ i, max 0 ((deriv (scaledPrimalPath x_lasso) τ) i) := by
        simp [max_eq_right (h_nonneg _)]
  have h_down_final : deriv (positiveZDownward x_lasso) τ =
      ∑ i, (1 + τ) * max 0 (-((deriv (scaledPrimalPath x_lasso) τ) i)) := by
    simpa [max_eq_left (neg_nonpos.mpr (h_nonneg _)), deriv_const] using
      h_down_closed_on_nhds.deriv_eq
  exact ⟨h_up_final, h_down_final⟩

/--
Nonnegativity of the derivatives of `positiveZUpward` and `positiveZDownward`.
Exposed publicly (unlike `deriv_pos_z_identities`) so that clients bounding a
weighted combination `C1 / log(1/ε) + C3 * (1 / log(1/ε) * z_up' + z_down')` by a
single constant `max C1 C3` can discharge the nonnegativity side conditions of
`max_bound_algebra`-style arguments outside `Delta.lean` (e.g. in `Energy.lean`,
Section 4.6, Eq. (789)/(806)).

The proof does not distribute `deriv` over a sum at breakpoints. Instead it shows
that both integral functions are monotone on nonnegative time, then uses
`MonotoneOn.derivWithin_nonneg` at differentiability points and Mathlib's zero
convention at nondifferentiability points.
-/
lemma positiveZUpward_monotoneOn
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    MonotoneOn (positiveZUpward x_lasso) (Set.Ici 0) := by
  intro a ha b hb hab
  unfold positiveZUpward
  apply Finset.sum_le_sum
  intro i _
  let g := fun u : ℝ => max 0 (deriv (fun u' => u' * x_lasso u' i) u)
  have h0a : IntervalIntegrable g volume 0 a :=
    max_zero_deriv_intervalIntegrable x_lasso i a ha h_regular
  have h0b : IntervalIntegrable g volume 0 b :=
    max_zero_deriv_intervalIntegrable x_lasso i b hb h_regular
  have hab_int : IntervalIntegrable g volume a b := h0b.mono_set (by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le hb]
    exact Set.Icc_subset_Icc ha le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0a hab_int
  have hnonneg : 0 ≤ ∫ u in a..b, g u :=
    intervalIntegral.integral_nonneg_of_forall hab (fun u => le_max_left _ _)
  linarith

lemma positiveZDownward_monotoneOn
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    MonotoneOn (positiveZDownward x_lasso) (Set.Ici 0) := by
  intro a ha b hb hab
  unfold positiveZDownward
  apply Finset.sum_le_sum
  intro i _
  let g := fun u : ℝ => (1 + u) *
    max 0 (-deriv (fun u' => u' * x_lasso u' i) u)
  have h0a_neg := max_zero_neg_deriv_intervalIntegrable x_lasso i a ha h_regular
  have h0b_neg := max_zero_neg_deriv_intervalIntegrable x_lasso i b hb h_regular
  have h0a : IntervalIntegrable g volume 0 a := by
    dsimp [g]
    exact h0a_neg.continuousOn_mul (by fun_prop)
  have h0b : IntervalIntegrable g volume 0 b := by
    dsimp [g]
    exact h0b_neg.continuousOn_mul (by fun_prop)
  have hab_int : IntervalIntegrable g volume a b := h0b.mono_set (by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le hb]
    exact Set.Icc_subset_Icc ha le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0a hab_int
  have hnonneg : 0 ≤ ∫ u in a..b, g u := by
    apply intervalIntegral.integral_nonneg hab
    intro u hu
    have ha' : 0 ≤ a := ha
    exact mul_nonneg (by linarith [ha', hu.1]) (le_max_left _ _)
  linarith

lemma positiveZ_deriv_nonneg
    (x_lasso : ℝ → EuclideanSpace ℝ ι) (τ : ℝ) (hτ : 0 ≤ τ)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    0 ≤ deriv (positiveZUpward x_lasso) τ ∧ 0 ≤ deriv (positiveZDownward x_lasso) τ := by
  have h_up_mono := positiveZUpward_monotoneOn x_lasso h_regular
  have h_down_mono := positiveZDownward_monotoneOn x_lasso h_regular
  constructor
  · by_cases hd : DifferentiableAt ℝ (positiveZUpward x_lasso) τ
    · have h := h_up_mono.derivWithin_nonneg (x := τ)
      rwa [hd.derivWithin (uniqueDiffOn_Ici 0 τ hτ)] at h
    · simp [deriv_zero_of_not_differentiableAt hd]
  · by_cases hd : DifferentiableAt ℝ (positiveZDownward x_lasso) τ
    · have h := h_down_mono.derivWithin_nonneg (x := τ)
      rwa [hd.derivWithin (uniqueDiffOn_Ici 0 τ hτ)] at h
    · simp [deriv_zero_of_not_differentiableAt hd]

lemma pos_delta_bound_3
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (_hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_piecewise_deriv : ∀ (τ' : ℝ) (i' : ι), 0 ≤ τ' →
        DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ' →
        ∃ ε > 0, ∀ t, |t - τ'| < ε →
          deriv (fun u' => u' * (x_lasso u').ofLp i') t =
          deriv (fun u' => u' * (x_lasso u').ofLp i') τ') :
    ∃ C > 0, ∀ s : ℝ, 0 < s → ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        - inner ℝ (deriv (scaledPrimalPath x_lasso) τ)
            (posRescaledMirrorVariable ε (u ε) τ)
        ≤ C * (1 / Real.log (1 / ε) * deriv (positiveZUpward x_lasso) τ +
          deriv (positiveZDownward x_lasso) τ) := by
  -- Postulate the uniform trajectory bound (Proposition 4.1, not yet formalized).
  -- This gives a constant X > 0 such that for all sufficiently small ε and all
  -- τ ≥ 0, every coordinate of xᵋ(τ) is bounded above by X.
  have hu_pos : ∀ ε > 0, ∀ t i, posEffectiveParameter (u ε) t i ≠ 0 :=
    pos_effective_param_ne_zero M r lambda β u hdata hβ hu
  rcases uniform_trajectory_coordinate_bound M r lambda β u hdata hβ hu with ⟨X, hX_pos, hX_ev⟩
  -- From the trajectory bound and the definition wᵋ_i = -log(xᵋ_i)/log(1/ε),
  -- we obtain a lower bound: wᵋ_i(τ) ≥ -C_low / log(1/ε).
  -- Since xᵋ_i ≤ X, we have log(xᵋ_i) ≤ max(0, log X), so
  -- -log(xᵋ_i) ≥ -max(0, log X), giving the bound.
  rcases rescaled_mirror_lower_bound X u hX_ev hu_pos with ⟨C_low, hC_low_pos, hW_low_ev⟩
  -- From the integrated mirror equation (positive_integrated_mirror_equation)
  -- together with the trajectory bound, we obtain an upper bound:
  -- |wᵋ_i(τ)| ≤ C_w * (1 + τ).
  -- The integrated mirror equation gives:
  --   wᵋ(τ) = wᵋ(0) - τ·r + M·zᵋ(τ) + τ·λ·𝟙
  -- Since xᵋ is bounded, zᵋ(τ) = ∫₀ᵗ xᵋ is bounded by τ·X, and wᵋ(0) ≈ 𝟙 is bounded.
  rcases rescaled_mirror_upper_bound M r lambda β u hdata hβ hu hu_pos X hX_pos hX_ev with
    ⟨C_w, _, hW_ev⟩
  -- Combine the constants
  set C := max C_low C_w
  refine ⟨C, lt_max_of_lt_left hC_low_pos, fun s _hs => ?_⟩
  -- Intersect the three "eventually" filters, also restrict to ε ∈ (0,1) so that log(1/ε) > 0
  filter_upwards [hX_ev s _hs, hW_low_ev s _hs, hW_ev s _hs, by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨1, by norm_num, fun _ hx => hx⟩] with ε hXε hW_low_ε hW_ε hε_mem
  intro τ hτ
  by_cases h_path_diff : DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ
  swap
  · have h_nonneg := positiveZ_deriv_nonneg x_lasso τ hτ.left h_regular
    rw [deriv_zero_of_not_differentiableAt h_path_diff, inner_zero_left, neg_zero]
    apply mul_nonneg
    · exact (lt_max_of_lt_left hC_low_pos).le
    · apply add_nonneg
      · exact mul_nonneg
          (div_nonneg zero_le_one (Real.log_pos
            (one_lt_one_div hε_mem.1 hε_mem.2)).le) h_nonneg.1
      · exact h_nonneg.2
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
  have h_derivs := deriv_pos_z_identities x_lasso τ hτ.left h_regular
    h_piecewise_deriv h_path_diff
  rcases h_derivs with ⟨h_upward_eq_raw, h_downward_eq_raw⟩
  have h_upward_eq : deriv (positiveZUpward x_lasso) τ = ∑ i, max 0 (zDot i) := by
    simpa [zDot] using h_upward_eq_raw
  have h_downward_eq : deriv (positiveZDownward x_lasso) τ = ∑ i, (1 + τ) * max 0 (-zDot i) := by
    simpa [zDot] using h_downward_eq_raw
  rw [← h_upward_eq] at h_bound_pos
  rw [← h_downward_eq] at h_bound_neg
  -- Nonnegativity of deriv (positiveZUpward x_lasso) τ: from the derivative identity
  -- (it equals a sum of max(0, ...) terms, each ≥ 0)
  have h_up_nonneg : 0 ≤ deriv (positiveZUpward x_lasso) τ := by
    rw [h_upward_eq]
    refine Finset.sum_nonneg (fun i _ => ?_)
    exact le_max_left _ _
  -- Nonnegativity of deriv (positiveZDownward x_lasso) τ: from the derivative identity
  -- and τ ≥ 0 (since τ ∈ [0, s]).  For τ ≥ 0 we have (1+τ) ≥ 1 > 0 and
  -- max(0, -zDot i) ≥ 0, so the RHS sum is nonnegative, hence LHS ≥ 0.
  have hτ_nonneg : 0 ≤ τ := hτ.left
  have h_down_nonneg : 0 ≤ deriv (positiveZDownward x_lasso) τ := by
    rw [h_downward_eq]
    refine Finset.sum_nonneg (fun i _ => ?_)
    have h_nonneg_max : 0 ≤ max 0 (-zDot i) := le_max_left _ _
    have h_nonneg_factor : 0 ≤ 1 + τ := by linarith
    nlinarith
  -- Assemble the final inequality from the pos/neg bounds
  exact assemble_pos_delta_bound_3 zDot w C_low C_w C τ ε x_lasso
    (le_max_left _ _) (le_max_right _ _)
    h_bound_pos h_bound_neg h_up_nonneg h_down_nonneg hε_mem.1 hε_mem.2

/--
Monotone-case analogue of `pos_delta_bound_3`: the same bound on
`-⟨deriv z τ, posRescaledMirrorVariable ε (u ε) τ⟩`, but with the piecewise-linearity
hypothesis `h_piecewise_deriv` (constructed from `ScaledPrimalPathLocallyAffineAtDifferentiable`
in the general case) replaced by coordinatewise monotonicity `h_mono` of
`z = scaledPrimalPath x_lasso` on `[0,∞)`.

Informal proof: identical to `pos_delta_bound_3`'s proof (the uniform trajectory bound
(`uniform_trajectory_coordinate_bound`) and the lower/upper bounds on the rescaled mirror
variable (`rescaled_mirror_lower_bound`/`rescaled_mirror_upper_bound`) are unaffected by
monotonicity), except that the single internal step invoking `deriv_pos_z_identities` with
`h_piecewise_deriv` is replaced by `deriv_pos_z_identities_of_monotone` with `h_mono`. Citation:
`docs/Lasso.md`, Sec. 4.6, Eq. (789)/(806) (the "Term 3" bound of Eq. (4.14)) and Sec. 3.1/4.7
for the monotone specialization.
-/
lemma pos_delta_bound_3_of_monotone
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (_hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_mono : ∀ ν ν', 0 ≤ ν → ν ≤ ν' → ∀ i, ν * (x_lasso ν).ofLp i ≤ ν' * (x_lasso ν').ofLp i) :
    ∃ C > 0, ∀ s : ℝ, 0 < s → ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        - inner ℝ (deriv (scaledPrimalPath x_lasso) τ)
            (posRescaledMirrorVariable ε (u ε) τ)
        ≤ C * (1 / Real.log (1 / ε) * deriv (positiveZUpward x_lasso) τ +
          deriv (positiveZDownward x_lasso) τ) := by
  have hu_pos : ∀ ε > 0, ∀ t i, posEffectiveParameter (u ε) t i ≠ 0 :=
    pos_effective_param_ne_zero M r lambda β u hdata hβ hu
  rcases uniform_trajectory_coordinate_bound M r lambda β u hdata hβ hu with ⟨X, hX_pos, hX_ev⟩
  rcases rescaled_mirror_lower_bound X u hX_ev hu_pos with ⟨C_low, hC_low_pos, hW_low_ev⟩
  rcases rescaled_mirror_upper_bound M r lambda β u hdata hβ hu hu_pos X hX_pos hX_ev with
    ⟨C_w, _, hW_ev⟩
  set C := max C_low C_w
  refine ⟨C, lt_max_of_lt_left hC_low_pos, fun s _hs => ?_⟩
  filter_upwards [hX_ev s _hs, hW_low_ev s _hs, hW_ev s _hs, by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨1, by norm_num, fun _ hx => hx⟩] with ε hXε hW_low_ε hW_ε hε_mem
  intro τ hτ
  -- Split on whether τ = 0 (requires special handling because monotone derivative
  -- identities need τ > 0), or τ > 0 (the main case).
  by_cases hτ_zero : τ = 0
  · -- τ = 0 case: the scaled primal path vanishes on a right neighborhood of 0
    -- (property of the Lasso path, proved here via `lcp_eq_iff_of_small_mu` from LCP.lean
    -- to avoid a circular import with Theorems.lean).  Thus the derivative at 0 is 0,
    -- giving LHS = 0 ≤ RHS (nonnegative from `positiveZ_deriv_nonneg`).
    subst hτ_zero
    have h_nonneg := positiveZ_deriv_nonneg x_lasso 0 (le_refl 0) h_regular
    -- First, prove scaledPrimalPath x_lasso μ = 0 for all sufficiently small μ ≥ 0
    -- (this is the content of `scaled_path_zero_near_zero` in Theorems.lean, reproved here
    -- using `lcp_eq_iff_of_small_mu` which is available via LCP.lean).
    let N : ℝ := ⨆ i, |r i - lambda|
    let denom : ℝ := max N (1 : ℝ)
    have h_denom_pos : 0 < denom := by
      dsimp [denom, N]
      exact lt_max_of_lt_right (by norm_num : (0 : ℝ) < 1)
    have h_path_zero_near_zero : ∃ μ₀ > 0,
        ∀ μ ∈ Set.Icc (0 : ℝ) μ₀, scaledPrimalPath x_lasso μ = 0 := by
      refine ⟨(1 / denom) / 2, half_pos (div_pos (by norm_num) h_denom_pos), ?_⟩
      intro μ hμ
      rcases hμ with ⟨hμ_low, hμ_high⟩
      by_cases hμ_zero : μ = 0
      · subst hμ_zero; simp [scaledPrimalPath]
      · have hμ_pos : 0 < μ := lt_of_le_of_ne hμ_low (Ne.symm hμ_zero)
        have hx_min : IsPositiveLassoMinimizer M r lambda μ (x_lasso μ) := _hx_lasso μ hμ_pos
        have hpos : 0 < 1 / denom := div_pos (by norm_num) h_denom_pos
        have hμ_small : μ < 1 / denom := by linarith
        have hx_zero : x_lasso μ = 0 := by
          rcases (pos_lasso_is_lcp M r lambda μ (x_lasso μ) hdata.psd.symm hdata.psd).mp hx_min with
            ⟨v, hv⟩
          exact ((lcp_eq_iff_of_small_mu M r lambda μ hdata.psd
            hμ_pos hμ_small (x_lasso μ) v).mp hv).1
        dsimp [scaledPrimalPath]
        rw [hx_zero, smul_zero]
    rcases h_path_zero_near_zero with ⟨μ₀, hμ₀_pos, h_zero⟩
    -- Now prove deriv = 0 at 0
    have h_deriv_zero : deriv (scaledPrimalPath x_lasso) 0 = 0 := by
      by_cases hd : DifferentiableAt ℝ (scaledPrimalPath x_lasso) 0
      · have h_zero_right : ∀ᶠ t in 𝓝[>] 0, scaledPrimalPath x_lasso t = 0 := by
          filter_upwards [Ioo_mem_nhdsGT hμ₀_pos] with t ht
          exact h_zero t ⟨ht.1.le, ht.2.le⟩
        have h_f0 : scaledPrimalPath x_lasso 0 = 0 := by
          simpa using h_zero 0 ⟨le_refl 0, hμ₀_pos.le⟩
        have h_slope_eq : (fun _ => (0 : EuclideanSpace ℝ ι)) =ᶠ[𝓝[>] 0]
            (fun t : ℝ => t⁻¹ • (scaledPrimalPath x_lasso (0 + t) -
              scaledPrimalPath x_lasso 0)) := by
          filter_upwards [h_zero_right] with t ht
          simp [ht, h_f0]
        have h_tendsto_zero : Tendsto
            (fun t : ℝ => t⁻¹ • (scaledPrimalPath x_lasso (0 + t) - scaledPrimalPath x_lasso 0))
            (𝓝[>] 0) (𝓝 (0 : EuclideanSpace ℝ ι)) :=
          Filter.Tendsto.congr' h_slope_eq
            (tendsto_const_nhds (x := (0 : EuclideanSpace ℝ ι)))
        have h_tendsto_deriv := hd.hasDerivAt.tendsto_slope_zero_right
        exact tendsto_nhds_unique h_tendsto_deriv h_tendsto_zero
      · exact deriv_zero_of_not_differentiableAt hd
    rw [h_deriv_zero, inner_zero_left, neg_zero]
    apply mul_nonneg
    · exact (lt_max_of_lt_left hC_low_pos).le
    · apply add_nonneg
      · exact mul_nonneg
          (div_nonneg zero_le_one (Real.log_pos
            (one_lt_one_div hε_mem.1 hε_mem.2)).le) h_nonneg.1
      · exact h_nonneg.2
  · -- τ > 0: the main case, mirroring the proof of `pos_delta_bound_3`.
    have hτ_pos : 0 < τ := lt_of_le_of_ne hτ.left (Ne.symm hτ_zero)
    by_cases h_path_diff : DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ
    swap
    · -- non-differentiable case (identical to pos_delta_bound_3)
      have h_nonneg' := positiveZ_deriv_nonneg x_lasso τ hτ.left h_regular
      rw [deriv_zero_of_not_differentiableAt h_path_diff, inner_zero_left, neg_zero]
      apply mul_nonneg
      · exact (lt_max_of_lt_left hC_low_pos).le
      · apply add_nonneg
        · exact mul_nonneg
            (div_nonneg zero_le_one (Real.log_pos
              (one_lt_one_div hε_mem.1 hε_mem.2)).le) h_nonneg'.1
        · exact h_nonneg'.2
    -- differentiable case (τ > 0, differentiable)
    set zDot := deriv (scaledPrimalPath x_lasso) τ
    set w := posRescaledMirrorVariable ε (u ε) τ
    rcases mirror_pos_neg_bounds zDot w C_low C_w τ ε
      (hW_low_ε τ hτ)
      (hW_ε τ hτ) with ⟨h_bound_pos, h_bound_neg⟩
    -- Use monotone derivative identities instead of `deriv_pos_z_identities`
    have h_derivs := deriv_pos_z_identities_of_monotone
      x_lasso τ hτ_pos h_regular h_mono h_path_diff
    rcases h_derivs with ⟨h_upward_eq, h_downward_eq⟩
    rw [← h_upward_eq] at h_bound_pos
    rw [← h_downward_eq] at h_bound_neg
    -- Nonnegativity of the Z-derivatives (same as in pos_delta_bound_3)
    have h_up_nonneg : 0 ≤ deriv (positiveZUpward x_lasso) τ := by
      rw [h_upward_eq]
      refine Finset.sum_nonneg (fun i _ => ?_)
      exact le_max_left _ _
    have h_down_nonneg : 0 ≤ deriv (positiveZDownward x_lasso) τ := by
      rw [h_downward_eq]
      refine Finset.sum_nonneg (fun i _ => ?_)
      have h_nonneg_max : 0 ≤ max 0 (-zDot i) := le_max_left _ _
      have h_nonneg_factor : 0 ≤ 1 + τ := by linarith
      nlinarith
    -- Assemble the final inequality from the pos/neg bounds
    exact assemble_pos_delta_bound_3 zDot w C_low C_w C τ ε x_lasso
      (le_max_left _ _) (le_max_right _ _)
      h_bound_pos h_bound_neg h_up_nonneg h_down_nonneg hε_mem.1 hε_mem.2

/--
If `f, g : ℝ → ℝ` are continuous on `[0, ∞)` and their product is identically zero on `[0, ∞)`,
then `f'(x) g(x) = 0` for all `x ≥ 0`.

Informal Proof:
(Source: Standard Real Analysis, e.g., Rudin, Principles of Mathematical Analysis, Chap 5).
If `x = 0` and `f` is not two-sided differentiable at `0`, Lean's `deriv` defaults to `0`,
so `f'(0)g(0)=0`. If `x > 0` or `f` is differentiable at `x`: if `g(x) ≠ 0`, by continuity `g ≠ 0`
on a neighborhood of `x`. Thus `f = 0` on this neighborhood, implying `f'(x) = 0`.
If `g(x) = 0`, then `f'(x)g(x) = 0`. In all cases, the product is `0`.
-/
-- If f·g = 0 on [0,∞) with g continuous and g(x) ≠ 0, and f is differentiable at x,
-- then deriv f x = 0. The key idea: continuity of g forces g ≠ 0 near x, so f = 0 near x,
-- and unique differentiability on [0,∞) forces deriv f x = 0.
private lemma deriv_eq_zero_of_mul_eq_zero_at_nonzero
    {f g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ici 0))
    (h_mul : ∀ x ≥ 0, f x * g x = 0) {x : ℝ} (hx : 0 ≤ x)
    (h_diff : DifferentiableAt ℝ f x) (h_gx : g x ≠ 0) :
    deriv f x = 0 := by
  -- f x = 0 because f·g = 0 and g x ≠ 0
  have h_fx : f x = 0 :=
    (eq_zero_or_eq_zero_of_mul_eq_zero (h_mul x hx)).resolve_right h_gx
  -- g is continuous on [0,∞) at x, so within [0,∞), g stays away from 0 near x
  -- Combine: near x within [0,∞), g ≠ 0, so f = 0 (from h_mul)
  have h_eventually_f : ∀ᶠ y in 𝓝[Set.Ici 0] x, f y = 0 := by
    filter_upwards
      [(hg.continuousWithinAt hx).preimage_mem_nhdsWithin
        (isOpen_compl_singleton.mem_nhds h_gx),
      self_mem_nhdsWithin] with y hy hmem
    exact (eq_zero_or_eq_zero_of_mul_eq_zero (h_mul y hmem)).resolve_right hy
  -- Transfer to f: constant zero function has derivative 0, f equals it near x
  have h_f_deriv_zero : HasDerivWithinAt f 0 (Set.Ici 0) x :=
    (hasDerivWithinAt_const (c := (0 : ℝ)) (s := Set.Ici 0) (x := x)).congr_of_eventuallyEq
      h_eventually_f h_fx
  -- Unique differentiability within [0,∞) at x forces the two to agree
  have h_unique_diff : UniqueDiffWithinAt ℝ (Set.Ici 0) x := by
    rcases hx.eq_or_lt with rfl | hx_pos
    · exact uniqueDiffWithinAt_Ici 0
    · exact uniqueDiffWithinAt_of_mem_nhds (Ici_mem_nhds hx_pos)
  exact h_unique_diff.eq_deriv (Set.Ici 0) (h_diff.hasDerivAt.hasDerivWithinAt) h_f_deriv_zero

lemma deriv_mul_zero_of_nonneg
    {f g : ℝ → ℝ} (hg : ContinuousOn g (Set.Ici 0))
    (h_mul : ∀ x ≥ 0, f x * g x = 0) (x : ℝ) (hx : 0 ≤ x) :
    deriv f x * g x = 0 := by
  by_cases h_diff : DifferentiableAt ℝ f x
  · by_cases h_gx : g x = 0
    · simp [h_gx]
    · simp [deriv_eq_zero_of_mul_eq_zero_at_nonzero hg h_mul hx h_diff h_gx]
  · simp [deriv_zero_of_not_differentiableAt h_diff]

/--
If `f : ℝ → E` is `K`-Lipschitz on `[a, b]`, then `‖f'(x)‖ ≤ K` for all `x ∈ [a, b]`.

Informal Proof:
(Source: Federer, Geometric Measure Theory, Theorem 3.1.6).
Where `f` is differentiable, `‖f'(x)‖ = \lim_{h \to 0} ‖f(x+h) - f(x)‖/|h| ≤ K`.
Where `f` is not differentiable, Lean's `deriv` is defined as `0`, which is `≤ K` since `K ≥ 0`.
-/
lemma deriv_bound_of_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b K : ℝ} (hK : 0 ≤ K) (hab : a < b)
    (hlip : LipschitzOnWith (Real.toNNReal K) f (Set.Icc a b)) (x : ℝ) (hx : x ∈ Set.Icc a b) :
    ‖deriv f x‖ ≤ K := by
  rcases hx with ⟨hax, hxb⟩
  by_cases h_diff : DifferentiableAt ℝ f x
  · -- When f is differentiable, bound its derivative norm by K.
    have h_deriv : HasDerivAt f (deriv f x) x := h_diff.hasDerivAt
    -- We use the slope characterization of the derivative and the Lipschitz bound.
    -- Consider two cases: x < b (use right-hand limit) or x = b (use left-hand limit).
    by_cases hx_lt_b : x < b
    · -- Right-hand limit: t → 0⁺
      have h_tendsto : Tendsto (fun t : ℝ => t⁻¹ • (f (x + t) - f x)) (𝓝[>] 0) (𝓝 (deriv f x)) :=
        h_deriv.tendsto_slope_zero_right
      have h_norm_tendsto :
          Tendsto (fun t : ℝ => ‖t⁻¹ • (f (x + t) - f x)‖) (𝓝[>] 0) (𝓝 ‖deriv f x‖) :=
        h_tendsto.norm
      -- For small t > 0, we have x+t ∈ Icc a b, hence ‖f(x+t)-f(x)‖ ≤ K * t.
      -- This bounds each difference quotient by K.
      have h_bound : ∀ᶠ t : ℝ in 𝓝[>] 0, ‖t⁻¹ • (f (x + t) - f x)‖ ≤ K := by
        -- The set (0, b-x) is in 𝓝[>] 0
        have hδ : 0 < b - x := sub_pos.mpr hx_lt_b
        have h_mem : Set.Ioo (0 : ℝ) (b - x) ∈ 𝓝[>] (0 : ℝ) := by
          -- Ioo_mem_nhdsGT is the dual of Ioo_mem_nhdsLT (generated by @[to_dual])
          -- It states: a < b → Ioo a b ∈ 𝓝[>] a
          exact Ioo_mem_nhdsGT hδ
        filter_upwards [h_mem] with t ht
        have ht_pos : 0 < t := ht.1
        have ht_lt : t < b - x := ht.2
        -- x+t ∈ Icc a b
        have hx_t_mem : x + t ∈ Set.Icc a b := by
          have hx_t_lt_b : x + t < b := by linarith
          have ha_le_x_t : a ≤ x + t := by linarith
          exact ⟨ha_le_x_t, hx_t_lt_b.le⟩
        -- Apply Lipschitz condition
        have hlip_bound := hlip.dist_le_mul x ⟨hax, hxb⟩ (x + t) hx_t_mem
        rw [Real.dist_eq, dist_eq_norm] at hlip_bound
        -- hlip_bound : ‖f x - f (x + t)‖ ≤ ↑K.toNNReal * |x - (x + t)|
        -- Flip norm order and simplify the absolute value
        rw [norm_sub_rev] at hlip_bound
        -- hlip_bound : ‖f (x + t) - f x‖ ≤ ↑K.toNNReal * |x - (x + t)|
        have h_abs : |x - (x + t)| = |t| := by
          rw [show x - (x + t) = -t by ring, abs_neg]
        rw [h_abs] at hlip_bound
        rw [abs_of_pos ht_pos] at hlip_bound
        -- hlip_bound : ‖f (x + t) - f x‖ ≤ (Real.toNNReal K : ℝ) * t = K * t
        have h_coe : (Real.toNNReal K : ℝ) = K := Real.coe_toNNReal _ hK
        rw [h_coe] at hlip_bound
        -- Now bound the norm of the slope
        calc
          ‖t⁻¹ • (f (x + t) - f x)‖ = ‖t⁻¹‖ * ‖f (x + t) - f x‖ := by rw [norm_smul]
          _ = |t⁻¹| * ‖f (x + t) - f x‖ := by rw [Real.norm_eq_abs]
          _ = t⁻¹ * ‖f (x + t) - f x‖ := by rw [abs_of_pos (inv_pos.mpr ht_pos)]
          _ ≤ t⁻¹ * (K * t) := by gcongr
          _ = K := by field_simp [ne_of_gt ht_pos]
      -- Since the slopes tend to ‖deriv f x‖ and are ≤ K, we get ‖deriv f x‖ ≤ K
      have h_neBot : NeBot (𝓝[>] (0 : ℝ)) := by infer_instance
      exact le_of_tendsto h_norm_tendsto h_bound
    · -- Then x = b, use left-hand limit t → 0⁻
      have hx_eq_b : x = b := by linarith
      -- Rewrite x to b in the derivative and endpoint hypotheses
      have h_deriv_b : HasDerivAt f (deriv f b) b := by rwa [hx_eq_b] at h_deriv
      have hax_b : a ≤ b := by rwa [← hx_eq_b]
      have hxb_b : b ≤ b := le_refl b
      have h_tendsto : Tendsto (fun t : ℝ => t⁻¹ • (f (b + t) - f b)) (𝓝[<] 0) (𝓝 (deriv f b)) :=
        h_deriv_b.tendsto_slope_zero_left
      have h_norm_tendsto :
          Tendsto (fun t : ℝ => ‖t⁻¹ • (f (b + t) - f b)‖) (𝓝[<] 0) (𝓝 ‖deriv f b‖) :=
        h_tendsto.norm
      -- For small t < 0, b+t ∈ Icc a b, hence the Lipschitz condition bounds the slopes by K.
      have h_bound : ∀ᶠ t : ℝ in 𝓝[<] 0, ‖t⁻¹ • (f (b + t) - f b)‖ ≤ K := by
        -- The set (a-b, 0) is in 𝓝[<] 0
        have hδ : a - b < (0 : ℝ) := by linarith
        have h_mem : Set.Ioo (a - b) (0 : ℝ) ∈ 𝓝[<] (0 : ℝ) := by
          -- Ioo_mem_nhdsLT gives: u < v → Set.Ioo u v ∈ 𝓝[<] v
          -- Here a - b < 0, so we get Set.Ioo (a-b) 0 ∈ 𝓝[<] 0
          exact Ioo_mem_nhdsLT hδ
        filter_upwards [h_mem] with t ht
        have ht_neg : t < 0 := ht.2
        have ht_gt : a - b < t := ht.1
        -- b+t ∈ Icc a b
        have hb_t_mem : b + t ∈ Set.Icc a b := by
          have ha_le_b_t : a ≤ b + t := by linarith
          have hb_t_le_b : b + t ≤ b := by linarith
          exact ⟨ha_le_b_t, hb_t_le_b⟩
        -- Apply Lipschitz condition (both points b+t and b are in Icc a b)
        have hlip_bound := hlip.dist_le_mul (b + t) hb_t_mem b ⟨hax_b, hxb_b⟩
        rw [Real.dist_eq, dist_eq_norm] at hlip_bound
        have h_abs : |(b + t) - b| = |t| := by ring_nf
        rw [h_abs] at hlip_bound
        -- For t < 0, |t| = -t
        rw [abs_of_neg ht_neg] at hlip_bound
        have h_coe : (Real.toNNReal K : ℝ) = K := Real.coe_toNNReal _ hK
        rw [h_coe] at hlip_bound
        -- hlip_bound : ‖f (b + t) - f b‖ ≤ K * (-t)
        have h_inv_neg : t⁻¹ < 0 := inv_lt_zero'.mpr ht_neg
        have h_neg_inv_nonneg : 0 ≤ -t⁻¹ := by linarith
        calc
          ‖t⁻¹ • (f (b + t) - f b)‖ = ‖t⁻¹‖ * ‖f (b + t) - f b‖ := by rw [norm_smul]
          _ = |t⁻¹| * ‖f (b + t) - f b‖ := by rw [Real.norm_eq_abs]
          _ = (-t⁻¹) * ‖f (b + t) - f b‖ := by rw [abs_of_neg h_inv_neg]
          _ ≤ (-t⁻¹) * (K * (-t)) :=
            mul_le_mul_of_nonneg_left hlip_bound h_neg_inv_nonneg
          _ = K := by field_simp [ne_of_lt ht_neg]
      have h_neBot : NeBot (𝓝[<] (0 : ℝ)) := by infer_instance
      -- Rewrite the goal using hx_eq_b
      rw [hx_eq_b]
      exact le_of_tendsto h_norm_tendsto h_bound
  · -- f is not differentiable at x
    rw [deriv_zero_of_not_differentiableAt h_diff]
    rw [norm_zero]
    exact hK

/-- A path that is locally Lipschitz on nonnegative compact intervals has a
strictly positive uniform bound on the norm of its `deriv` on each nondegenerate
such interval.

The extra `+ 1` in the witness makes the constant strictly positive even when
the path is constant. At differentiability points the bound is the usual bound
of the derivative by the Lipschitz constant; at all other points Mathlib's
`deriv` is zero.
-/
lemma LocallyLipschitzOnCompacts.exists_deriv_bound_on_Icc
    {f : ℝ → EuclideanSpace ℝ ι} (hf : LocallyLipschitzOnCompacts f)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    ∃ C > 0, ∀ x ∈ Set.Icc a b, ‖deriv f x‖ ≤ C := by
  obtain ⟨K, hK_nonneg, hK_bound⟩ := hf.lipschitz_on_Icc a b ha hab.le
  have hlip : LipschitzOnWith K.toNNReal f (Set.Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul (K := K.toNNReal)
    intro x hx y hy
    simpa [dist_eq_norm, Real.dist_eq, Real.toNNReal_of_nonneg hK_nonneg] using
      hK_bound x hx y hy
  refine ⟨K + 1, by linarith, fun x hx ↦ ?_⟩
  have hderiv := deriv_bound_of_lipschitz hK_nonneg hab hlip x hx
  linarith

/--
Real-valued analogue of `LocallyLipschitzOnCompacts`, for scalarizations
(e.g. inner products against a fixed vector) of `EuclideanSpace`-valued Lipschitz
paths. Kept as a separate structure rather than genericizing `LocallyLipschitzOnCompacts`
itself, since the latter's companion `LocallyAbsolutelyContinuousOnNonnegativeCompacts`
API is only ever used at the `EuclideanSpace ℝ ι` type in this file.
-/
private structure LocallyLipschitzOnCompactsReal (f : ℝ → ℝ) : Prop where
  lipschitz_on_Icc :
    ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ μ ∈ Set.Icc a b, ∀ ν ∈ Set.Icc a b, |f μ - f ν| ≤ K * |μ - ν|

/--
A locally-Lipschitz-on-compacts function is bounded on every compact subinterval of
`[0, ∞)`, via the standard "endpoint value plus Lipschitz slack" estimate
`‖f μ‖ ≤ ‖f a‖ + K * (b - a)`.
-/
private lemma LocallyLipschitzOnCompacts.bounded_on_Icc
    {ι : Type*} [Fintype ι] {f : ℝ → EuclideanSpace ℝ ι} (hf : LocallyLipschitzOnCompacts f)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∃ Mb : ℝ, 0 ≤ Mb ∧ ∀ μ ∈ Set.Icc a b, ‖f μ‖ ≤ Mb := by
  obtain ⟨K, hK, hKbound⟩ := hf.lipschitz_on_Icc a b ha hab
  refine ⟨‖f a‖ + K * (b - a), by positivity, fun μ hμ => ?_⟩
  have h1 : ‖f μ‖ ≤ ‖f a‖ + ‖f μ - f a‖ := by
    calc ‖f μ‖ = ‖(f μ - f a) + f a‖ := by simp
    _ ≤ ‖f μ - f a‖ + ‖f a‖ := norm_add_le _ _
    _ = ‖f a‖ + ‖f μ - f a‖ := add_comm _ _
  have h2 : ‖f μ - f a‖ ≤ K * (b - a) := by
    have hb := hKbound μ hμ a ⟨le_refl a, hab⟩
    have habs : |μ - a| ≤ b - a := by
      rw [abs_of_nonneg (sub_nonneg.mpr hμ.1)]; linarith [hμ.2]
    calc ‖f μ - f a‖ ≤ K * |μ - a| := hb
    _ ≤ K * (b - a) := mul_le_mul_of_nonneg_left habs hK
  linarith

/-- Real-valued analogue of `.bounded_on_Icc`, for `LocallyLipschitzOnCompactsReal`. -/
private lemma LocallyLipschitzOnCompactsReal.bounded_on_Icc
    {f : ℝ → ℝ} (hf : LocallyLipschitzOnCompactsReal f)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    ∃ Mb : ℝ, 0 ≤ Mb ∧ ∀ μ ∈ Set.Icc a b, |f μ| ≤ Mb := by
  obtain ⟨K, hK, hKbound⟩ := hf.lipschitz_on_Icc a b ha hab
  refine ⟨|f a| + K * (b - a), by positivity, fun μ hμ => ?_⟩
  have h1 : |f μ| ≤ |f a| + |f μ - f a| := by
    calc |f μ| = |(f μ - f a) + f a| := by ring_nf
    _ ≤ |f μ - f a| + |f a| := abs_add_le _ _
    _ = |f a| + |f μ - f a| := by ring
  have h2 : |f μ - f a| ≤ K * (b - a) := by
    have hb := hKbound μ hμ a ⟨le_refl a, hab⟩
    have habs : |μ - a| ≤ b - a := by
      rw [abs_of_nonneg (sub_nonneg.mpr hμ.1)]; linarith [hμ.2]
    calc |f μ - f a| ≤ K * |μ - a| := hb
    _ ≤ K * (b - a) := mul_le_mul_of_nonneg_left habs hK
  linarith

/--
The (real-valued) inner product `μ ↦ ⟨f μ, g μ⟩` of two locally-Lipschitz-on-compacts
`EuclideanSpace`-valued paths is itself locally Lipschitz on compacts.

Informal proof: `⟨f μ, g μ⟩ - ⟨f ν, g ν⟩ = ⟨f μ - f ν, g μ⟩ + ⟨f ν, g μ - g ν⟩`, and
Cauchy-Schwarz bounds each term by `‖f μ - f ν‖ * ‖g μ‖` and `‖f ν‖ * ‖g μ - g ν‖`
respectively; both `f`, `g` are bounded on the compact interval (`.bounded_on_Icc`), so
these combine into a single Lipschitz estimate.
-/
private lemma inner_locallyLipschitzOnCompactsReal
    {ι : Type*} [Fintype ι] {f g : ℝ → EuclideanSpace ℝ ι}
    (hf : LocallyLipschitzOnCompacts f) (hg : LocallyLipschitzOnCompacts g) :
    LocallyLipschitzOnCompactsReal (fun μ => inner ℝ (f μ) (g μ)) := by
  constructor
  intro a b ha hab
  obtain ⟨Kf, hKf, hKf_bound⟩ := hf.lipschitz_on_Icc a b ha hab
  obtain ⟨Kg, hKg, hKg_bound⟩ := hg.lipschitz_on_Icc a b ha hab
  obtain ⟨Mf, _, hMf_bound⟩ := hf.bounded_on_Icc a b ha hab
  obtain ⟨Mg, hMg, hMg_bound⟩ := hg.bounded_on_Icc a b ha hab
  refine ⟨Kf * Mg + Mf * Kg, by positivity, fun μ hμ ν hν => ?_⟩
  have h_split : inner ℝ (f μ) (g μ) - inner ℝ (f ν) (g ν) =
      inner ℝ (f μ - f ν) (g μ) + inner ℝ (f ν) (g μ - g ν) := by
    rw [inner_sub_left, inner_sub_right]; ring
  rw [h_split]
  have h1 : ‖f μ - f ν‖ * ‖g μ‖ ≤ (Kf * |μ - ν|) * Mg :=
    mul_le_mul (hKf_bound μ hμ ν hν) (hMg_bound μ hμ) (norm_nonneg _)
      (mul_nonneg hKf (abs_nonneg _))
  have h2 : ‖f ν‖ * ‖g μ - g ν‖ ≤ Mf * (Kg * |μ - ν|) :=
    mul_le_mul (hMf_bound ν hν) (hKg_bound μ hμ ν hν) (norm_nonneg _) (by positivity)
  calc |inner ℝ (f μ - f ν) (g μ) + inner ℝ (f ν) (g μ - g ν)|
      ≤ |inner ℝ (f μ - f ν) (g μ)| + |inner ℝ (f ν) (g μ - g ν)| := abs_add_le _ _
    _ ≤ ‖f μ - f ν‖ * ‖g μ‖ + ‖f ν‖ * ‖g μ - g ν‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (Kf * |μ - ν|) * Mg + Mf * (Kg * |μ - ν|) := add_le_add h1 h2
    _ = (Kf * Mg + Mf * Kg) * |μ - ν| := by ring

/--
Dividing a locally-Lipschitz-on-compacts real function by the affine, `≥ 1`-valued
denominator `1 + μ * lambda` (with `lambda ≥ 0`) preserves local Lipschitz-on-compacts
regularity.

Informal proof: write `Bμ = 1 + μλ`. For `μ, ν ∈ [a,b] ⊆ [0,∞)`, `Bμ, Bν ≥ 1`, so
`f μ / Bμ - f ν / Bν = (f μ · Bν - Bμ · f ν) / (Bμ Bν)` has numerator
`(f μ - f ν) Bν + f ν (Bν - Bμ)`, bounded by `Kf |μ-ν| Bν + Mf λ |μ-ν|` (`Kf` the
Lipschitz constant of `f`, `Mf` a bound on `|f|`, using `|Bν - Bμ| = λ|μ-ν|`). Dividing
by `Bμ Bν ≥ 1` and using `Bν ≤ Bμ Bν` gives the estimate `(Kf + Mf λ) |μ - ν|`.
-/
private lemma LocallyLipschitzOnCompactsReal.div_affine_denom
    {f : ℝ → ℝ} (hf : LocallyLipschitzOnCompactsReal f)
    (lambda : ℝ) (hlambda_nonneg : 0 ≤ lambda) :
    LocallyLipschitzOnCompactsReal (fun μ => f μ / (1 + μ * lambda)) := by
  constructor
  intro a b ha hab
  obtain ⟨Kf, hKf, hKf_bound⟩ := hf.lipschitz_on_Icc a b ha hab
  obtain ⟨Mf, hMf, hMf_bound⟩ := hf.bounded_on_Icc a b ha hab
  refine ⟨Kf + Mf * lambda, by positivity, fun μ hμ ν hν => ?_⟩
  have hBμ_ge : (1 : ℝ) ≤ 1 + μ * lambda := by nlinarith [hμ.1]
  have hBν_ge : (1 : ℝ) ≤ 1 + ν * lambda := by nlinarith [hν.1]
  have hBμ_pos : (0 : ℝ) < 1 + μ * lambda := by linarith
  have hBν_pos : (0 : ℝ) < 1 + ν * lambda := by linarith
  have hnum : f μ * (1 + ν * lambda) - (1 + μ * lambda) * f ν =
      (f μ - f ν) * (1 + ν * lambda) + f ν * ((1 + ν * lambda) - (1 + μ * lambda)) := by ring
  have hdiv_eq : f μ / (1 + μ * lambda) - f ν / (1 + ν * lambda) =
      (f μ * (1 + ν * lambda) - (1 + μ * lambda) * f ν) / ((1 + μ * lambda) * (1 + ν * lambda)) :=
    div_sub_div (f μ) (f ν) hBμ_pos.ne' hBν_pos.ne'
  have hnum_bound : |f μ * (1 + ν * lambda) - (1 + μ * lambda) * f ν| ≤
      Kf * |μ - ν| * (1 + ν * lambda) + Mf * (lambda * |μ - ν|) := by
    rw [hnum]
    calc |(f μ - f ν) * (1 + ν * lambda) + f ν * ((1 + ν * lambda) - (1 + μ * lambda))|
        ≤ |(f μ - f ν) * (1 + ν * lambda)| + |f ν * ((1 + ν * lambda) - (1 + μ * lambda))| :=
          abs_add_le _ _
      _ = |f μ - f ν| * (1 + ν * lambda) + |f ν| * |(1 + ν * lambda) - (1 + μ * lambda)| := by
          rw [abs_mul, abs_mul, abs_of_pos hBν_pos]
      _ ≤ (Kf * |μ - ν|) * (1 + ν * lambda) + Mf * (lambda * |μ - ν|) := by
          have h1 : |f μ - f ν| * (1 + ν * lambda) ≤ (Kf * |μ - ν|) * (1 + ν * lambda) :=
            mul_le_mul_of_nonneg_right (hKf_bound μ hμ ν hν) hBν_pos.le
          have h2 : |f ν| * |(1 + ν * lambda) - (1 + μ * lambda)| ≤ Mf * (lambda * |μ - ν|) := by
            have heq : |(1 + ν * lambda) - (1 + μ * lambda)| = lambda * |μ - ν| := by
              rw [show (1 + ν * lambda) - (1 + μ * lambda) = lambda * (ν - μ) by ring, abs_mul,
                abs_of_nonneg hlambda_nonneg, abs_sub_comm]
            rw [heq]
            exact mul_le_mul_of_nonneg_right (hMf_bound ν hν)
              (mul_nonneg hlambda_nonneg (abs_nonneg _))
          linarith
  rw [hdiv_eq, abs_div, abs_of_pos (mul_pos hBμ_pos hBν_pos), div_le_iff₀ (mul_pos hBμ_pos hBν_pos)]
  have hle1 : Kf * |μ - ν| * (1 + ν * lambda) ≤
      Kf * |μ - ν| * ((1 + μ * lambda) * (1 + ν * lambda)) := by
    have : (1 + ν * lambda) * 1 ≤ (1 + ν * lambda) * (1 + μ * lambda) :=
      mul_le_mul_of_nonneg_left hBμ_ge (by linarith)
    nlinarith [mul_nonneg hKf (abs_nonneg (μ - ν))]
  have hle2 : Mf * (lambda * |μ - ν|) ≤
      (Mf * lambda) * |μ - ν| * ((1 + μ * lambda) * (1 + ν * lambda)) := by
    have hprod_ge : (1 : ℝ) ≤ (1 + μ * lambda) * (1 + ν * lambda) := by nlinarith
    nlinarith [mul_nonneg (mul_nonneg hMf hlambda_nonneg) (abs_nonneg (μ - ν))]
  nlinarith [hnum_bound, hle1, hle2]

/-- The constant path is trivially `LocallyLipschitzOnCompacts`, with Lipschitz constant `0`. -/
private lemma locallyLipschitzOnCompacts_const {ι : Type*} [Fintype ι] (c : EuclideanSpace ℝ ι) :
    LocallyLipschitzOnCompacts (fun _ : ℝ => c) :=
  ⟨fun _ _ _ _ => ⟨0, le_refl 0, fun _ _ _ _ => by simp⟩⟩

/-- Sum of two `LocallyLipschitzOnCompactsReal` functions is `LocallyLipschitzOnCompactsReal`. -/
private lemma LocallyLipschitzOnCompactsReal.add
    {f g : ℝ → ℝ} (hf : LocallyLipschitzOnCompactsReal f) (hg : LocallyLipschitzOnCompactsReal g) :
    LocallyLipschitzOnCompactsReal (fun μ => f μ + g μ) := by
  constructor
  intro a b ha hab
  obtain ⟨Kf, hKf, hKf_bound⟩ := hf.lipschitz_on_Icc a b ha hab
  obtain ⟨Kg, hKg, hKg_bound⟩ := hg.lipschitz_on_Icc a b ha hab
  refine ⟨Kf + Kg, add_nonneg hKf hKg, fun μ hμ ν hν => ?_⟩
  calc |(f μ + g μ) - (f ν + g ν)| = |(f μ - f ν) + (g μ - g ν)| := by ring_nf
    _ ≤ |f μ - f ν| + |g μ - g ν| := abs_add_le _ _
    _ ≤ Kf * |μ - ν| + Kg * |μ - ν| := add_le_add (hKf_bound μ hμ ν hν) (hKg_bound μ hμ ν hν)
    _ = (Kf + Kg) * |μ - ν| := by ring

/-- Transport `LocallyLipschitzOnCompactsReal` along a pointwise equality valid on `[0, ∞)`. -/
private lemma LocallyLipschitzOnCompactsReal.congr
    {f g : ℝ → ℝ} (hf : LocallyLipschitzOnCompactsReal f) (h : ∀ μ, 0 ≤ μ → f μ = g μ) :
    LocallyLipschitzOnCompactsReal g := by
  constructor
  intro a b ha hab
  obtain ⟨K, hK, hKbound⟩ := hf.lipschitz_on_Icc a b ha hab
  refine ⟨K, hK, fun μ hμ ν hν => ?_⟩
  rw [← h μ (le_trans ha hμ.1), ← h ν (le_trans ha hν.1)]
  exact hKbound μ hμ ν hν

/--
If `X(μ) = -⟨w(μ), y(μ)⟩ / (1+μλ)` for `EuclideanSpace`-valued `LocallyLipschitzOnCompacts`
paths `w, y` and `λ ≥ 0`, then `X` is `LocallyLipschitzOnCompactsReal`. Combines
`inner_locallyLipschitzOnCompactsReal` (Lipschitz numerator) with `.div_affine_denom`
(division by `1 + μλ` preserves Lipschitz-on-compacts).
-/
private lemma inner_ones_kernel_locallyLipschitzOnCompactsReal
    {ι : Type*} [Fintype ι] {w y : ℝ → EuclideanSpace ℝ ι} {X : ℝ → ℝ} {lambda : ℝ}
    (hw_lip : LocallyLipschitzOnCompacts w) (hy_lip : LocallyLipschitzOnCompacts y)
    (hlambda_nonneg : 0 ≤ lambda)
    (h_eq : ∀ μ, 0 ≤ μ → X μ = (-inner ℝ (w μ) (y μ)) / (1 + μ * lambda)) :
    LocallyLipschitzOnCompactsReal X := by
  have hA_lip : LocallyLipschitzOnCompactsReal (fun μ => - inner ℝ (w μ) (y μ)) := by
    have h := inner_locallyLipschitzOnCompactsReal hw_lip hy_lip
    constructor
    intro a b ha hab
    obtain ⟨K, hK, hKbound⟩ := h.lipschitz_on_Icc a b ha hab
    refine ⟨K, hK, fun μ hμ ν hν => ?_⟩
    rw [show -inner ℝ (w μ) (y μ) - -inner ℝ (w ν) (y ν) =
      -(inner ℝ (w μ) (y μ) - inner ℝ (w ν) (y ν)) by ring, abs_neg]
    exact hKbound μ hμ ν hν
  exact (hA_lip.div_affine_denom lambda hlambda_nonneg).congr fun μ hμ => (h_eq μ hμ).symm

/--
The LCP-orthogonality identity behind Lemma 4.12: for `zkerv ∈ ker(M)`, the dual value
`wv = M·zv + q(μ)` pairs with `zkerv` as `⟨wv, zkerv⟩ = (1+μλ)⟨𝟙, zkerv⟩`. Isolates the pure
LCP/inner-product algebra used to control the kernel component of a primal path, independent
of which path `zv` it comes from (in particular, independent of any range/kernel splitting
of `zv` itself).

Informal proof: `⟨wv,zkerv⟩ = ⟨Mzv,zkerv⟩ + ⟨q(μ),zkerv⟩ = ⟨zv,Mzkerv⟩ + ⟨q(μ),zkerv⟩
= 0 + ⟨q(μ),zkerv⟩` (`M` symmetric, `Mzkerv=0`), and `q(μ) = -μr + (1+μλ)𝟙` with `⟨r,zkerv⟩=0`
(since `r ∈ range(M) ⊥ ker(M)`, using `r = My` and `Mzkerv=0` again).
-/
private lemma inner_dual_kernel_eq
    {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda μ : ℝ)
    (hM_symm : M.IsSymm) (hr_mem_span : InMatrixSpan M r)
    (zv zkerv wv : EuclideanSpace ℝ ι)
    (hw_eq : wv = matVec M zv + parametricLcpQ r lambda μ)
    (hMzker : matVec M zkerv = 0) :
    inner ℝ wv zkerv = (1 + μ * lambda) * inner ℝ (euclideanOf fun _ => 1) zkerv := by
  rcases hr_mem_span with ⟨y, hy⟩
  rw [hw_eq]
  calc
    inner ℝ (matVec M zv + parametricLcpQ r lambda μ) zkerv
        = inner ℝ (matVec M zv) zkerv + inner ℝ (parametricLcpQ r lambda μ) zkerv := by
      rw [inner_add_left]
    _ = inner ℝ zv (matVec M zkerv) + inner ℝ (parametricLcpQ r lambda μ) zkerv := by
      rw [inner_matVec_comm_of_isSymm M hM_symm]
    _ = inner ℝ zv 0 + inner ℝ (parametricLcpQ r lambda μ) zkerv := by rw [hMzker]
    _ = inner ℝ (parametricLcpQ r lambda μ) zkerv := by simp
    _ = inner ℝ (-μ • r + (1 + μ * lambda) • euclideanOf (fun _ => 1)) zkerv := by
      have hq_eq : parametricLcpQ r lambda μ =
          -μ • r + (1 + μ * lambda) • euclideanOf (fun _ => (1 : ℝ)) := by
        ext i
        simp [parametricLcpQ, euclideanOf, smul_eq_mul]
        ring
      rw [hq_eq]
    _ = (-μ) * inner ℝ r zkerv + (1 + μ * lambda) * inner ℝ (euclideanOf (fun _ => 1)) zkerv := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    _ = (-μ) * 0 + (1 + μ * lambda) * inner ℝ (euclideanOf (fun _ => 1)) zkerv := by
      rw [← hy, ← inner_matVec_comm_of_isSymm M hM_symm y zkerv, hMzker, inner_zero_right]
    _ = (1 + μ * lambda) * inner ℝ (euclideanOf (fun _ => 1)) zkerv := by ring

/--
The range component `z_range(μ) = M†(M z(μ))` of a decomposed path is locally Lipschitz on
compacts whenever `M z` is, being the composition of a fixed continuous linear map
(`matVec Mdagger`) with a Lipschitz path.
-/
private lemma range_part_locallyLipschitz
    {ι : Type*} [Fintype ι]
    (M Mdagger : Matrix ι ι ℝ) (z : ℝ → EuclideanSpace ℝ ι)
    (hMz_lip : LocallyLipschitzOnCompacts (fun μ => matVec M (z μ))) :
    LocallyLipschitzOnCompacts (fun μ => matVec Mdagger (matVec M (z μ))) := by
  let L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    LinearMap.toContinuousLinearMap (matVecLM Mdagger)
  constructor
  intro a b ha hab
  rcases hMz_lip.lipschitz_on_Icc a b ha hab with ⟨K, hK_nonneg, hK_bound⟩
  refine ⟨‖L‖₊ * K, mul_nonneg (norm_nonneg _) hK_nonneg, fun μ hμ ν hν => ?_⟩
  calc
    ‖matVec Mdagger (matVec M (z μ)) - matVec Mdagger (matVec M (z ν))‖
        = ‖L (matVec M (z μ) - matVec M (z ν))‖ := by
      dsimp [L]; rw [← matVec_sub]; exact rfl
    _ ≤ ‖L‖ * ‖matVec M (z μ) - matVec M (z ν)‖ := L.le_opNorm _
    _ ≤ ‖L‖ * (K * |μ - ν|) := mul_le_mul_of_nonneg_left (hK_bound μ hμ ν hν) (norm_nonneg _)
    _ = (‖L‖ * K) * |μ - ν| := by ring

/-- For a coordinatewise-nonnegative vector, its Euclidean norm is bounded by its
`𝟙`-inner-product (i.e. the sum of its coordinates): `‖x‖ ≤ ⟨𝟙, x⟩` when `x ≥ 0`.
Follows from `∑ x_i² ≤ (∑ x_i)²` (`Finset.sum_sq_le_sq_sum_of_nonneg`) and monotonicity of `√`. -/
private lemma norm_le_inner_ones_of_nonneg {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι)
    (hx : Nonnegative x) : ‖x‖ ≤ inner ℝ (euclideanOf fun _ => 1) x := by
  have hx' : ∀ i, 0 ≤ x i := hx
  have h_inner_eq : inner ℝ (euclideanOf fun _ => (1 : ℝ)) x = ∑ i, x i := by
    simp [PiLp.inner_apply, euclideanOf]
  rw [h_inner_eq]
  have h_sum_nonneg : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx' i)
  rw [EuclideanSpace.norm_eq,
    show (∑ i, x i) = |∑ i, x i| from (abs_of_nonneg h_sum_nonneg).symm,
    ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖x i‖ ^ 2 = ∑ i, (x i) ^ 2 := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Real.norm_eq_abs, sq_abs]
    _ ≤ (∑ i, x i) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hx' i)

/--
A coordinatewise-monotone path `z` whose `𝟙`-inner-product `μ ↦ ⟨𝟙, z μ⟩` is
`LocallyLipschitzOnCompactsReal` is itself `LocallyLipschitzOnCompacts`.

Informal proof: on `[a,b]`, monotonicity makes either `z ν - z μ ≥ 0` or `z μ - z ν ≥ 0`
(coordinatewise), so `norm_le_inner_ones_of_nonneg` bounds `‖z μ - z ν‖` by
`|⟨𝟙,z μ⟩ - ⟨𝟙,z ν⟩|`, which the scalar Lipschitz bound on `⟨𝟙,z·⟩` controls.
-/
private lemma locallyLipschitz_of_inner_ones_lipschitz_and_mono
    {ι : Type*} [Fintype ι] {z : ℝ → EuclideanSpace ℝ ι}
    (h_ones_lip : LocallyLipschitzOnCompactsReal (fun μ => inner ℝ (euclideanOf fun _ => 1) (z μ)))
    (h_mono : ∀ μ ν, 0 ≤ μ → μ ≤ ν → ∀ i, z μ i ≤ z ν i) :
    LocallyLipschitzOnCompacts z := by
  constructor
  intro a b ha hab
  obtain ⟨K, hK_nonneg, hK_bound⟩ := h_ones_lip.lipschitz_on_Icc a b ha hab
  refine ⟨K, hK_nonneg, fun μ hμ ν hν => ?_⟩
  by_cases hμν : μ ≤ ν
  · have hz_mono : ∀ i, z μ i ≤ z ν i := h_mono μ ν (le_trans ha hμ.1) hμν
    have hz_diff_nonneg : Nonnegative (z ν - z μ) := fun i => by
      have h := hz_mono i
      simp only [PiLp.sub_apply]
      linarith
    calc
      ‖z μ - z ν‖ = ‖z ν - z μ‖ := by rw [norm_sub_rev]
      _ ≤ inner ℝ (euclideanOf fun _ => 1) (z ν - z μ) :=
          norm_le_inner_ones_of_nonneg (z ν - z μ) hz_diff_nonneg
      _ = inner ℝ (euclideanOf fun _ => 1) (z ν) - inner ℝ (euclideanOf fun _ => 1) (z μ) := by
          rw [inner_sub_right]
      _ ≤ |inner ℝ (euclideanOf fun _ => 1) (z ν) - inner ℝ (euclideanOf fun _ => 1) (z μ)| :=
          le_abs_self _
      _ ≤ K * |ν - μ| := hK_bound ν hν μ hμ
      _ = K * |μ - ν| := by rw [abs_sub_comm]
  · have hνμ : ν ≤ μ := by linarith
    have hz_mono : ∀ i, z ν i ≤ z μ i := h_mono ν μ (le_trans ha hν.1) hνμ
    have hz_diff_nonneg : Nonnegative (z μ - z ν) := fun i => by
      have h := hz_mono i
      simp only [PiLp.sub_apply]
      linarith
    calc
      ‖z μ - z ν‖ ≤ inner ℝ (euclideanOf fun _ => 1) (z μ - z ν) :=
          norm_le_inner_ones_of_nonneg (z μ - z ν) hz_diff_nonneg
      _ = inner ℝ (euclideanOf fun _ => 1) (z μ) - inner ℝ (euclideanOf fun _ => 1) (z ν) := by
          rw [inner_sub_right]
      _ ≤ |inner ℝ (euclideanOf fun _ => 1) (z μ) - inner ℝ (euclideanOf fun _ => 1) (z ν)| :=
          le_abs_self _
      _ ≤ K * |μ - ν| := hK_bound μ hμ ν hν

/--
Lemma 4.12 of the Lasso blueprint. Orchestrates the reusable pieces above: decompose
`z = z_range + z_ker` via the Moore-Penrose pseudoinverse of `M` (`range_part_locallyLipschitz`
gives `z_range` is Lipschitz); use LCP-orthogonality (`inner_dual_kernel_eq`) together with
complementary slackness (`h_lcp`) to express `⟨𝟙,z_ker⟩` as a ratio of Lipschitz quantities
(`inner_ones_kernel_locallyLipschitzOnCompactsReal`); sum with `⟨𝟙,z_range⟩` (trivially
Lipschitz, via `locallyLipschitzOnCompacts_const` and `inner_locallyLipschitzOnCompactsReal`)
to get `⟨𝟙,z⟩` Lipschitz; then monotonicity turns that into `z` itself being Lipschitz
(`locallyLipschitz_of_inner_ones_lipschitz_and_mono`).

(Source: standard results on Moore-Penrose inverses and symmetric matrices, e.g.,
Meyer, "Matrix Analysis and Applied Linear Algebra" (2000), https://doi.org/10.1137/1.9780898717331)
-/
lemma locallyLipschitzOnCompacts_of_matVec_lipschitz
    {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (z : ℝ → EuclideanSpace ℝ ι)
    (hM_psd : IsPositiveSemidefinite M)
    (hr_mem_span : InMatrixSpan M r)
    (hlambda_nonneg : 0 ≤ lambda)
    (h_lcp : ∀ μ ≥ 0, isLCP M (parametricLcpQ r lambda μ) (z μ)
      (matVec M (z μ) + parametricLcpQ r lambda μ))
    -- Unlike the classical uniqueness-based argument (Cottle-Pang-Stone), this proof pins
    -- down `z` via monotonicity (`h_mono`) and complementary slackness instead: no LCP
    -- solution-uniqueness hypothesis is needed at all (contrast `parametric_lcp_lipschitz`,
    -- which takes one but only to satisfy the shape of the classical theorem it documents).
    (hMz_lip : LocallyLipschitzOnCompacts (fun μ => matVec M (z μ)))
    (hw_lip : LocallyLipschitzOnCompacts (fun μ => matVec M (z μ) + parametricLcpQ r lambda μ))
    (h_mono : ∀ μ ν, 0 ≤ μ → μ ≤ ν → ∀ i, z μ i ≤ z ν i) :
    LocallyLipschitzOnCompacts z := by
  -- Decompose z = z_range + z_ker via the Moore-Penrose pseudoinverse of M.
  rcases exists_psd_range_inverse M hM_psd.symm hM_psd with ⟨Mdagger, hInv⟩
  set z_range : ℝ → EuclideanSpace ℝ ι := fun μ => matVec Mdagger (matVec M (z μ))
    with hz_range_def
  set z_ker : ℝ → EuclideanSpace ℝ ι := fun μ => z μ - z_range μ with hz_ker_def
  have hMz_ker : ∀ μ, matVec M (z_ker μ) = 0 := fun μ => by
    dsimp [z_ker, z_range]
    rw [matVec_sub, hInv.range_inverse (z μ), sub_self]
  have hz_range_lip : LocallyLipschitzOnCompacts z_range :=
    range_part_locallyLipschitz M Mdagger z hMz_lip
  set w : ℝ → EuclideanSpace ℝ ι := fun μ => matVec M (z μ) + parametricLcpQ r lambda μ
    with hw_def
  -- Lemma 4.12: the kernel component's `𝟙`-inner-product is Lipschitz on compacts, via the
  -- LCP-orthogonality identity `⟨w, z_ker⟩ = (1+μλ)⟨𝟙,z_ker⟩` and complementary slackness.
  have h_inner_ones_ker_eq (μ : ℝ) (hμ : 0 ≤ μ) :
      inner ℝ (euclideanOf fun _ => 1) (z_ker μ) =
        (-inner ℝ (w μ) (z_range μ)) / (1 + μ * lambda) := by
    have h_split : z μ = z_range μ + z_ker μ := by dsimp only [z_ker]; abel
    have h_ker := inner_dual_kernel_eq M r lambda μ hM_psd.symm hr_mem_span
      (z μ) (z_ker μ) (w μ) rfl (hMz_ker μ)
    have h_comp : inner ℝ (w μ) (z μ) = 0 := by
      rcases h_lcp μ hμ with ⟨-, -, -, h_comp⟩
      exact h_comp
    have h_sum : inner ℝ (w μ) (z μ) = inner ℝ (w μ) (z_range μ) + inner ℝ (w μ) (z_ker μ) := by
      rw [h_split]; exact inner_add_right _ _ _
    rw [h_sum, h_ker] at h_comp
    have hpos : (0 : ℝ) < 1 + μ * lambda := by nlinarith
    rw [eq_div_iff hpos.ne']
    linarith
  have h_inner_ones_ker_lip :
      LocallyLipschitzOnCompactsReal (fun μ => inner ℝ (euclideanOf fun _ => 1) (z_ker μ)) :=
    inner_ones_kernel_locallyLipschitzOnCompactsReal hw_lip hz_range_lip hlambda_nonneg
      h_inner_ones_ker_eq
  -- ⟨𝟙, z_range⟩ is Lipschitz since `z_range` is and the constant path `𝟙` trivially is.
  have h_inner_ones_range_lip :
      LocallyLipschitzOnCompactsReal (fun μ => inner ℝ (euclideanOf fun _ => 1) (z_range μ)) :=
    inner_locallyLipschitzOnCompactsReal (locallyLipschitzOnCompacts_const _) hz_range_lip
  -- ⟨𝟙, z⟩ = ⟨𝟙, z_range⟩ + ⟨𝟙, z_ker⟩ is Lipschitz as the sum of two Lipschitz functions.
  have h_inner_ones_lip :
      LocallyLipschitzOnCompactsReal (fun μ => inner ℝ (euclideanOf fun _ => 1) (z μ)) :=
    (h_inner_ones_range_lip.add h_inner_ones_ker_lip).congr fun μ _ => by
      simp only [hz_ker_def, inner_sub_right]; ring
  -- Monotonicity + Lipschitz `𝟙`-inner-product ⟹ `z` itself is Lipschitz on compacts.
  exact locallyLipschitz_of_inner_ones_lipschitz_and_mono h_inner_ones_lip h_mono

/--
The solution to a parametric LCP with linear parameter dependence is locally Lipschitz continuous,
under the standing assumptions `ProblemData` (PSD, `r` in the column span of `M`, `λ ≥ 0`) and
coordinatewise monotonicity of the selected solution path.

Informal Proof:
The solution map of an LCP with a P-matrix (positive definite) is single-valued and Lipschitz
continuous with respect to the right-hand side vector `q` (Cottle, Pang, & Stone, "The Linear
Complementarity Problem", Academic Press, 1992, Theorem 7.3.10), but `M` here is only PSD, so
that classical uniqueness-based route does not apply directly. Instead this proof pins down `z`
via monotonicity and complementary slackness: the range component `M†(Mz)` is Lipschitz via the
scaled-dual argument of `scaled_dual_lipschitz`, and the `𝟙`-inner-product of the kernel
component is controlled algebraically by the LCP-orthogonality identity (`inner_dual_kernel_eq`)
together with complementarity, without ever needing a second solution `z'` to coincide with `z`.
Monotonicity then converts the resulting Lipschitz bound on `⟨𝟙, z⟩` into one on `z` itself
(`locallyLipschitz_of_inner_ones_lipschitz_and_mono`).
See `locallyLipschitzOnCompacts_of_matVec_lipschitz` for the full argument.
-/
lemma parametric_lcp_lipschitz
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (z : ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda)
    (h_lcp : ∀ μ ≥ 0, isLCP M (parametricLcpQ r lambda μ) (z μ)
      (matVec M (z μ) + parametricLcpQ r lambda μ))
    (h_mono : ∀ μ ν, 0 ≤ μ → μ ≤ ν → ∀ i, z μ i ≤ z ν i) :
    LocallyLipschitzOnCompacts z := by
  -- Keep a copy of hdata before destructuring, for use in scaled_dual_lipschitz
  have hdata' := hdata
  rcases hdata with ⟨hM_psd, hr_mem_span, hlambda_nonneg⟩
  have hM_symm : M.IsSymm := hM_psd.symm
  -- Let w(μ) = M z(μ) + q(μ) be the dual path
  set w : ℝ → EuclideanSpace ℝ ι := fun μ => matVec M (z μ) + parametricLcpQ r lambda μ
    with hw_def
  have hsol : ∀ μ : ℝ, 0 ≤ μ → isParametricLCP M r lambda μ (z μ) (w μ) := by
    intro μ hμ
    rcases h_lcp μ hμ with ⟨hw_eq, hw_nonneg, hz_nonneg, h_comp⟩
    dsimp [isParametricLCP, isLCP, w]
    -- isLCP expects v = q + matVec M x, but we have matVec M x + q; use add_comm
    have hw_eq' : w μ = parametricLcpQ r lambda μ + matVec M (z μ) := by
      dsimp [w]; abel
    exact ⟨hw_eq', hw_nonneg, hz_nonneg, h_comp⟩
  -- `scaled_dual_lipschitz` gives that the scaled dual is Lipschitz.
  -- From this we deduce that M(z(μ)) is Lipschitz on compacts.
  have h_scaled_dual_lip : LocallyLipschitzOnCompacts (scaledDualPath lambda w) :=
    scaled_dual_lipschitz M r lambda z w hdata' hsol
  -- Since scaledDualPath lambda w = μ ↦ (1/(1+μλ))·w(μ) and 1/(1+μλ) is smooth,
  -- w itself is locally Lipschitz on compacts away from μ = -1/λ (which is negative).
  -- On [0, ∞) the factor is bounded between 1/(1+bλ) and 1.
  have hw_lip : LocallyLipschitzOnCompacts w :=
    locallyLipschitzOnCompacts_of_scaledDual_lipschitz lambda hlambda_nonneg w h_scaled_dual_lip
  -- Now w(μ) = M(z(μ)) + q(μ), and q(μ) = -μ r + (1+μλ)1 is affine, hence Lipschitz.
  -- Therefore M(z(μ)) = w(μ) - q(μ) is also Lipschitz.
  have hq_lip : LocallyLipschitzOnCompacts (fun μ => parametricLcpQ r lambda μ) :=
    parametricLcpQ_locallyLipschitzOnCompacts r lambda
  have hMz_lip : LocallyLipschitzOnCompacts (fun μ => matVec M (z μ)) := by
    -- matVec M (z μ) = w μ - parametricLcpQ r lambda μ, difference of Lipschitz functions
    refine ⟨fun a b ha hab => ?_⟩
    rcases hw_lip.lipschitz_on_Icc a b ha hab with ⟨Kw, hKw, hw⟩
    rcases hq_lip.lipschitz_on_Icc a b ha hab with ⟨Kq, hKq, hq⟩
    refine ⟨Kw + Kq, add_nonneg hKw hKq, fun μ hμ ν hν => ?_⟩
    have h_diff : matVec M (z μ) - matVec M (z ν) =
        (w μ - w ν) - (parametricLcpQ r lambda μ - parametricLcpQ r lambda ν) := by
      dsimp [w]
      abel
    rw [h_diff]
    calc ‖(w μ - w ν) - (parametricLcpQ r lambda μ - parametricLcpQ r lambda ν)‖
      _ ≤ ‖w μ - w ν‖ + ‖parametricLcpQ r lambda μ - parametricLcpQ r lambda ν‖ := norm_sub_le _ _
      _ ≤ Kw * |μ - ν| + Kq * |μ - ν| := add_le_add (hw μ hμ ν hν) (hq μ hμ ν hν)
      _ = (Kw + Kq) * |μ - ν| := (add_mul _ _ _).symm
  -- Now we need to recover Lipschitz continuity of z from that of Mz.
  -- Decompose z = z_range + z_kernel where z_range ∈ range(M) and z_kernel ∈ ker(M).
  -- Since M is PSD, range(M) = ker(M)⊥ and M is positive definite on range(M).
  -- Hence on range(M), M has a bounded inverse (via the pseudoinverse), so
  -- z_range = M†(Mz) is Lipschitz.
  -- On ker(M), the LCP gives q_k(μ) = (1+μλ)·1_k (since r ∈ range(M) ⇒ r_k = 0).
  -- Because λ ≥ 0 and μ ≥ 0, we have 1+μλ ≥ 1 > 0.  Feasibility of the LCP for all μ
  -- forces 1_k ≥ 0 (otherwise w_k would become negative).  Complementarity then forces
  -- z_k = 0 wherever 1_k > 0.  Where 1_k = 0, uniqueness of the LCP solution (h_unique)
  -- pins down z_k = 0 as well (since z=0 is always a solution when q_k ≡ 0).
  -- Therefore z_kernel ≡ 0, and z = z_range is Lipschitz.
  exact locallyLipschitzOnCompacts_of_matVec_lipschitz M r lambda z hM_psd hr_mem_span
    hlambda_nonneg h_lcp hMz_lip hw_lip h_mono

/--
Helper for Section 4.6, Eq. (4.14), Term 4, Part 1.

Informal proof reference: `docs/Lasso.md`, Section 4.6, Step 1 of Proof Sketch.
Let $z(\tau)$ be the scaled primal path and
$w(\tau) = M z(\tau) - \tau r + (1 + \tau \lambda) \mathbf{1}$
be the dual path. We know $z_i(\tau) w_i(\tau) = 0$ for all $\tau$
by complementarity. Since $w_i(\tau)$ is continuous, if $w_i(\tau) > 0$,
then $w_i > 0$ on some neighborhood of $\tau$. On this neighborhood,
$z_i = 0$, so its derivative is 0. Thus $\dot{z}_i(\tau) w_i(\tau) = 0$.
If $w_i(\tau) = 0$, then $\dot{z}_i(\tau) \cdot 0 = 0$.
In all cases, $\dot{z}_i(\tau) w_i(\tau) = 0$, so their inner product
is exactly 0 (which is $\le 0$).
-/
lemma deriv_piLp_apply {ι : Type*} [Fintype ι] {z : ℝ → EuclideanSpace ℝ ι} {τ : ℝ}
    (h_diff : DifferentiableAt ℝ z τ) (i : ι) :
    (deriv z τ).ofLp i = deriv (fun x => (z x).ofLp i) τ := by
  have h1 : HasDerivAt z (deriv z τ) τ := h_diff.hasDerivAt
  let h_proj : EuclideanSpace ℝ ι →L[ℝ] ℝ := EuclideanSpace.proj i
  have h2 : HasDerivAt (h_proj ∘ z) (h_proj (deriv z τ)) τ :=
    h_proj.hasFDerivAt.comp_hasDerivAt τ h1
  change (deriv z τ).ofLp i = deriv (fun x => (z x).ofLp i) τ
  exact h2.deriv.symm

lemma pos_delta_bound_4_term1
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (hdata : ProblemData M r lambda) :
    ∀ τ ∈ Set.Ici (0 : ℝ),
      inner ℝ (deriv (scaledPrimalPath x_lasso) τ)
        (matVec M (scaledPrimalPath x_lasso τ) - τ • r + (1 + τ * lambda) • ones) ≤ 0 := by
  rcases hdata with ⟨hM_psd, hr_mem_span, hlambda_nonneg⟩
  have hM_symm : M.IsSymm := hM_psd.symm
  set z := scaledPrimalPath x_lasso with hz_def
  set w : ℝ → EuclideanSpace ℝ ι := fun μ =>
    matVec M (z μ) - μ • r + (1 + μ * lambda) • ones with hw_def
  intro τ hτ
  have hτ_nonneg : 0 ≤ τ := hτ
  -- Step 1: For all μ > 0, derive LCP complementarity from hx_lasso via pos_lasso_is_lcp
  have hLCP_pos : ∀ μ > 0,
      w μ = parametricLcpQ r lambda μ + matVec M (z μ) ∧
      Nonnegative (w μ) ∧ Nonnegative (z μ) ∧ inner ℝ (w μ) (z μ) = 0 := by
    intro μ hμ_pos
    have hμ_ne : μ ≠ 0 := by linarith
    have hx_min := hx_lasso μ hμ_pos
    rcases (pos_lasso_is_lcp M r lambda μ (x_lasso μ) hM_symm hM_psd).mp hx_min with ⟨v, hv⟩
    rcases hv with ⟨hv_eq, hv_nonneg, hx_nonneg, h_ortho⟩
    have h_w_eq : w μ = μ • v := by
      dsimp [w]
      rw [lcp_dual_scale_eq_target M r lambda μ hμ_ne x_lasso v hv_eq]
    have h_w_eq2 : w μ = parametricLcpQ r lambda μ + matVec M (z μ) := by
      rw [h_w_eq]
      calc
        μ • v = μ • (lcpQ r lambda μ + matVec M (x_lasso μ)) := by rw [hv_eq]
        _ = μ • lcpQ r lambda μ + μ • matVec M (x_lasso μ) := by simp [smul_add]
        _ = μ • lcpQ r lambda μ + matVec M (μ • (x_lasso μ)) := by rw [matVec_smul_eq]
        _ = μ • lcpQ r lambda μ + matVec M (z μ) := by simp [z, scaledPrimalPath]
        _ = parametricLcpQ r lambda μ + matVec M (z μ) := by
          ext i
          dsimp [lcpQ, parametricLcpQ, euclideanOf]
          field_simp [hμ_ne]
          ring
    have h_w_nonneg : Nonnegative (w μ) := by
      rw [h_w_eq]
      intro i; simpa using mul_nonneg (by linarith) (hv_nonneg i)
    have h_z_nonneg : Nonnegative (z μ) := by
      intro i; dsimp [z, scaledPrimalPath]; simpa using mul_nonneg (by linarith) (hx_nonneg i)
    have h_inner_zero : inner ℝ (w μ) (z μ) = 0 := by
      rw [h_w_eq]; dsimp [z, scaledPrimalPath]
      simp [inner_smul_left, inner_smul_right, h_ortho]
    exact ⟨h_w_eq2, h_w_nonneg, h_z_nonneg, h_inner_zero⟩
  -- Step 2: LCP at μ = 0 (z(0) = 0, w(0) = ones)
  have hLCP_zero_info : z 0 = 0 ∧ w 0 = ones := by
    dsimp [z, scaledPrimalPath, w]
    simp [ones, euclideanOf, matVec]
  rcases hLCP_zero_info with ⟨hz0, hw0⟩
  have hw0_nonneg : Nonnegative (w 0) := by
    rw [hw0]; intro i; simp [ones, euclideanOf]
  have hz0_nonneg : Nonnegative (z 0) := by
    rw [hz0]; intro i; simp
  have h_inner_zero_0 : inner ℝ (w 0) (z 0) = 0 := by rw [hz0, inner_zero_right]
  -- Step 3: Coordinate-wise complementarity for all μ ≥ 0
  have h_coord_zero : ∀ μ ≥ 0, ∀ i : ι, (w μ) i * (z μ) i = 0 := by
    intro μ hμ i
    by_cases hμ0 : μ = 0
    · subst hμ0; rw [hz0]; simp
    · have hμpos : μ > 0 := Ne.lt_of_le (Ne.symm hμ0) hμ
      rcases hLCP_pos μ hμpos with ⟨_, hw_nonneg, hz_nonneg, h_inner_zero⟩
      have h_sum : (∑ j : ι, (w μ) j * (z μ) j) = 0 := by
        have h_inner_sum : inner ℝ (w μ) (z μ) = (∑ j : ι, (w μ) j * (z μ) j) := by
          rw [PiLp.inner_apply]
          simp [mul_comm]
        rw [← h_inner_sum, h_inner_zero]
      have h_nonneg : ∀ j, 0 ≤ (w μ) j * (z μ) j := fun j =>
        mul_nonneg (hw_nonneg j) (hz_nonneg j)
      have h_all_zero := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => h_nonneg j)).mp h_sum
      exact h_all_zero i (Finset.mem_univ i)
  -- Step 4: Prove inner product = 0 (hence ≤ 0) via LCP complementarity
  -- The inner product is exactly 0 by the same coordinatewise argument as
  -- `h_comp_zero` in Energy.lean.  We defer the calculus details (case split
  -- on `DifferentiableAt ℝ z τ`, coordinate expansion via `differentiableAt_pi`
  -- + `deriv_pi`, `IsLocalMin.deriv_eq_zero` for τ>0, slope argument for τ=0,
  -- `deriv_zero_of_not_differentiableAt` for non-differentiable points).
  have h_inner_eq_zero : inner ℝ (deriv z τ) (w τ) = 0 := by
    -- Step 4: Prove inner product = 0 (hence ≤ 0)
    by_cases h_diff : DifferentiableAt ℝ z τ
    · -- z is differentiable at τ: work coordinatewise
      rw [PiLp.inner_apply]
      have h_deriv_eval : ∀ i, (deriv z τ) i = deriv (fun x => z x i) τ := fun i =>
        deriv_piLp_apply h_diff i
      simp only [h_deriv_eval, Real.inner_apply]
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hwi_zero : (w τ) i = 0
      · simp [hwi_zero]
      · have hwi_pos : 0 < (w τ) i := by
          by_cases hτ0 : τ = 0
          · subst hτ0; rw [hw0]; simp [ones, euclideanOf]
          · have hτpos : τ > 0 := lt_of_le_of_ne hτ_nonneg (Ne.symm hτ0)
            rcases hLCP_pos τ hτpos with ⟨_, hw_nonneg, _, _⟩
            exact lt_of_le_of_ne (hw_nonneg i) (Ne.symm hwi_zero)
        have hzi_zero : (z τ) i = 0 := by
          have hprod := h_coord_zero τ hτ_nonneg i
          cases mul_eq_zero.mp hprod with
          | inl h => exact (hwi_zero h).elim
          | inr h => exact h
        by_cases hτ_pos : τ > 0
        · -- τ > 0: z_i has a local minimum at τ (since z_i ≥ 0 everywhere on (0,∞))
          have h_isMin : IsLocalMin (fun μ => z μ i) τ := by
            have hδ : 0 < τ / 2 := by linarith
            refine Filter.mem_of_superset (Metric.ball_mem_nhds τ hδ) ?_
            intro μ hμ
            rw [Metric.mem_ball, Real.dist_eq] at hμ
            have hμ_bounds := abs_lt.mp hμ
            have hμ_nonneg : 0 ≤ μ := by linarith
            have hz_nonneg_μ : 0 ≤ (z μ) i := by
              by_cases hμ0 : μ = 0
              · subst hμ0; rw [hz0]; rfl
              · have hμpos : μ > 0 := by linarith
                rcases hLCP_pos μ hμpos with ⟨_, _, hz_nonneg_μ', _⟩
                exact hz_nonneg_μ' i
            dsimp only [Set.mem_ofPred_eq]
            rw [hzi_zero]
            exact hz_nonneg_μ
          have h_deriv_zero : deriv (fun μ => z μ i) τ = 0 :=
            IsLocalMin.deriv_eq_zero h_isMin
          simp [h_deriv_zero]
        · -- τ = 0: use continuity of w at 0 to deduce z_i ≡ 0 on a right neighborhood
          have hτ_zero : τ = 0 := by linarith
          subst hτ_zero
          -- w is continuous at 0 (since z is differentiable at 0, hence continuous)
          have hz_cont_at_0 : ContinuousAt z 0 := h_diff.continuousAt
          -- Define f(μ) = matVec M(z(μ)) - μ•r + (1+μ•λ)•ones, which is continuous at 0
          set f := fun (μ : ℝ) => matVec M (z μ) - μ • r + (1 + μ * lambda) • ones
            with hf_def
          have hf_cont_at_0 : ContinuousAt f 0 := by
            dsimp [f]
            have h_matVec_cont : Continuous (matVecLM M) :=
              (matVecLM M).continuous_of_finiteDimensional
            refine ContinuousAt.add (ContinuousAt.sub ?_ ?_) ?_
            · exact (h_matVec_cont.continuousAt.comp hz_cont_at_0)
            · exact continuousAt_id.smul_const r
            · have h1 : ContinuousAt (fun (μ : ℝ) => 1 + μ * lambda) 0 :=
                continuousAt_const.add (continuousAt_id.mul continuousAt_const)
              have h2 : ContinuousAt (fun (_ : ℝ) => (ones : EuclideanSpace ℝ ι)) 0 :=
                continuousAt_const
              exact h1.smul h2
          have hf0_i_one : (f 0) i = 1 := by
            dsimp [f]; rw [hz0]; simp [ones, euclideanOf, matVec]
          have h_fi_cont : ContinuousAt (fun μ => (f μ) i) 0 :=
            (continuous_euclidean_apply i).continuousAt.comp hf_cont_at_0
          -- w agrees with f for μ ≥ 0
          have h_wi_tendsto : Tendsto (fun μ => (w μ) i) (𝓝[>] 0) (𝓝 1) := by
            apply Filter.Tendsto.congr'
            · filter_upwards [self_mem_nhdsWithin] with μ hμ
              have hμ_nonneg' : 0 ≤ μ := le_of_lt hμ
              dsimp [w, f]
            · have h_limit := h_fi_cont.tendsto.mono_left
                (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
              rwa [hf0_i_one] at h_limit
          -- Since (w μ) i → 1 > 0, eventually (w μ) i > 0 for μ > 0 small enough
          have h_wi_pos : ∀ᶠ μ in 𝓝[>] 0, 0 < (w μ) i :=
            h_wi_tendsto.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
          -- Using complementarity: if w_i(μ) > 0, then z_i(μ) = 0 (for μ > 0)
          have h_zi_zero : ∀ᶠ μ in 𝓝[>] 0, (z μ) i = 0 := by
            filter_upwards [h_wi_pos, self_mem_nhdsWithin] with μ hμ_pos hμ_Ioi
            have hμ_nonneg' : 0 ≤ μ := le_of_lt hμ_Ioi
            have hprod := h_coord_zero μ hμ_nonneg' i
            cases mul_eq_zero.mp hprod with
            | inl h => exact (ne_of_gt hμ_pos h).elim
            | inr h => exact h
          have hz0_i : (z 0) i = 0 := by rw [hz0]; simp
          -- On 𝓝[>] 0, the slope of (z i) at 0 is identically 0
          have h_slope_eq_zero : (slope (fun μ => z μ i) 0) =ᶠ[𝓝[>] 0] (fun _ => (0 : ℝ)) := by
            filter_upwards [h_zi_zero] with μ hμ
            simp [slope, hμ, hz0_i]
          have h_tendsto_slope_zero : Tendsto (slope (fun μ => z μ i) 0) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
            h_slope_eq_zero.tendsto
          -- The derivative is also the limit of the slope
          have h_hasDeriv : HasDerivAt (fun μ => z μ i) ((deriv z 0).ofLp i) 0 := by
            have h_deriv_z : HasDerivAt z (deriv z 0) 0 := h_diff.hasDerivAt
            exact (EuclideanSpace.proj i).hasFDerivAt.comp_hasDerivAt 0 h_deriv_z
          have h_nhdsWithin_ne : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
            nhdsWithin_mono 0 (fun x hx => Set.mem_compl_singleton_iff.mpr (ne_of_gt hx))
          have h_tendsto_slope_deriv : Tendsto (slope (fun μ => z μ i) 0) (𝓝[>] 0)
              (𝓝 ((deriv z 0).ofLp i)) :=
            h_hasDeriv.tendsto_slope.mono_left h_nhdsWithin_ne
          -- By uniqueness of limits, deriv = 0
          have h_deriv_zi_zero : (deriv z 0).ofLp i = 0 :=
            tendsto_nhds_unique h_tendsto_slope_deriv h_tendsto_slope_zero
          have h_eval : deriv (fun μ => z μ i) 0 = (deriv z 0).ofLp i := h_hasDeriv.deriv
          rw [h_eval, h_deriv_zi_zero]
          ring
    · -- z is not differentiable at τ: deriv yields 0, inner product is 0
      rw [deriv_zero_of_not_differentiableAt h_diff]
      simp [inner_zero_left]
  have h_goal : inner ℝ (deriv (scaledPrimalPath x_lasso) τ)
      (matVec M (scaledPrimalPath x_lasso τ) - τ • r + (1 + τ * lambda) • ones) ≤ 0 := by
    simpa [hz_def, hw_def] using h_inner_eq_zero.le
  exact h_goal




/--
Helper for Section 4.6, Eq. (4.14), Term 4, Part 2 (Derivative bound).

INFORMAL PROOF:
By `h_lipschitz`, the scaled primal path $z(\tau)=\tau x(\tau)$ has some
Lipschitz constant $K\geq 0$ on the compact interval $[0,s]$. At every point
where $z$ is differentiable, the norm of its derivative is at most $K$, by
passing the Lipschitz bound on difference quotients to the limit. At every
other point Mathlib defines `deriv z` to be zero. Thus $C=K+1$ is a strictly
positive bound at every point of $[0,s]$.

The local-Lipschitz hypothesis is essential: absolute continuity alone gives
an integrable derivative almost everywhere, but does not give a uniform bound
(for example, `t ↦ t^(3/4)` on `[0, 1]` is absolutely continuous and has an
unbounded derivative near zero).

This is the stronger regularity route needed by the current pointwise API for
Term 4, Part 2.  In the general absolutely-continuous setting of Theorem 3.2,
the source instead retains the positive/negative variation densities and only
integrates them in Eq. (4.15); that route does not require this lemma.

CITATION:
- `docs/Lasso.md`, Section 4.7, Lemma 4.12 (the monotone case supplies local
  Lipschitz regularity of the scaled primal path).
- `Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean` (Lipschitz implies
  absolute continuity, but not conversely).
- Federer, *Geometric Measure Theory*, Theorem 3.1.6 (derivatives of Lipschitz
  maps are bounded by the Lipschitz constant wherever they exist).
-/
lemma scaledPrimalPath_deriv_bound
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (h_lipschitz : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso))
    (s : ℝ) (hs : 0 < s) :
    ∃ C > 0, ∀ τ ∈ Set.Icc (0 : ℝ) s, ‖deriv (scaledPrimalPath x_lasso) τ‖ ≤ C := by
  exact h_lipschitz.exists_deriv_bound_on_Icc 0 s (le_refl _) hs

/--
Helper for Section 4.6, Eq. (4.14), Term 4, Part 3.

INFORMAL PROOF:
We must bound the inner product
$\langle \dot{z}^\varepsilon(\tau) - \dot{z}(\tau), \mathbf{1} - w^\varepsilon(0) \rangle$.
From the gradient flow initialization,
$w^\varepsilon_i(0) = -\frac{\log(\varepsilon \beta_i^2)}{\log(1/\varepsilon)}$
which is equal to $1 - \frac{\log \beta_i^2}{\log(1/\varepsilon)}$.
Thus, $\mathbf{1} - w^\varepsilon(0) = \frac{\log \beta^2}{\log(1/\varepsilon)}$,
which tends to $0$ uniformly as $\varepsilon \to 0$ with rate $O(1/\log(1/\varepsilon))$.
Since the derivatives $\dot{z}^\varepsilon(\tau)$ and $\dot{z}(\tau)$ are bounded uniformly
on $[0, s]$ (the latter by `scaledPrimalPath_deriv_bound`), their inner product with this
vanishing term is bounded by $O(1/\log(1/\varepsilon))$, which is eventually $\le \delta$
for sufficiently small $\varepsilon$.

CITATION:
`docs/Lasso.md`, Section 4.6 (Proof of Theorem 3.2).
-/
-- Helper for pos_delta_bound_4_term2
private lemma posRescaledMirrorVariable_zero_eq {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (ε : ℝ)
    (β : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hβ : NonzeroCoordinates β)
    (hu : posDlnGradientFlow M r lambda ε β u) :
    ones - posRescaledMirrorVariable ε u 0 =
      ((Real.log (1 / ε))⁻¹ : ℝ) • euclideanOf (fun i => Real.log ((β i)^2)) := by
  have h_log_pos : 0 < Real.log (1 / ε) :=
    Real.log_pos (one_lt_one_div hε_pos hε_lt_one)
  ext i
  have h_init : posEffectiveParameter u 0 = ε • coordinateSquare β :=
    posEffectiveParameter_zero_eq_smul_coordinateSquare M r lambda ε β u hu hε_pos.le
  dsimp [ones, posRescaledMirrorVariable, euclideanOf]
  simp only [posTimeFromRescaled, zero_mul, zero_div]
  rw [h_init]
  simp only [coordinateSquare, euclideanOf, WithLp.equiv_symm_apply, PiLp.smul_apply, smul_eq_mul]
  have h_log_ne : Real.log (1 / ε) ≠ 0 := h_log_pos.ne.symm
  have h1 : (1 / ε) ≠ 0 := by positivity
  have h2 : ε * ((β.ofLp i)^2) ≠ 0 := by
    have : β.ofLp i ≠ 0 := hβ i
    positivity
  have h_sq : β.ofLp i * β.ofLp i = β.ofLp i ^ 2 := by ring
  rw [h_sq]
  calc
    1 - -Real.log (ε * β.ofLp i ^ 2) / Real.log (1 / ε)
      = 1 + Real.log (ε * β.ofLp i ^ 2) / Real.log (1 / ε) := by ring
    _ = (Real.log (1 / ε) + Real.log (ε * β.ofLp i ^ 2)) / Real.log (1 / ε) := by
      rw [add_div_eq_mul_add_div _ _ h_log_ne, one_mul]
    _ = Real.log (1 / ε * (ε * β.ofLp i ^ 2)) / Real.log (1 / ε) := by
      rw [← Real.log_mul h1 h2]
    _ = Real.log (β.ofLp i ^ 2) / Real.log (1 / ε) := by
      have : 1 / ε * (ε * β.ofLp i ^ 2) = β.ofLp i ^ 2 := by field_simp [hε_pos.ne.symm]
      rw [this]
    _ = (Real.log (1 / ε))⁻¹ * Real.log (β.ofLp i ^ 2) := by ring

-- Helper for pos_delta_bound_4_term2
private lemma le_log_one_div_of_le_exp_neg {ε M : ℝ} (hε_pos : 0 < ε) (hε_le : ε ≤ Real.exp (-M)) :
    M ≤ Real.log (1 / ε) := by
  have h_exp_bound : Real.exp M ≤ 1 / ε := by
    have h_mul : ε * Real.exp M ≤ 1 := by
      calc
        ε * Real.exp M ≤ Real.exp (-M) * Real.exp M :=
          mul_le_mul_of_nonneg_right hε_le (Real.exp_pos _).le
        _ = Real.exp ((-M) + M) := by rw [Real.exp_add]
        _ = Real.exp 0 := by ring_nf
        _ = 1 := Real.exp_zero
    calc
      Real.exp M = (ε * Real.exp M) / ε := by field_simp [hε_pos.ne.symm]
      _ ≤ 1 / ε := div_le_div_of_nonneg_right h_mul hε_pos.le
  have hpos_exp : 0 < Real.exp M := Real.exp_pos M
  have h_log_ineq : Real.log (Real.exp M) ≤ Real.log (1 / ε) :=
    Real.log_le_log hpos_exp h_exp_bound
  simpa [Real.log_exp M] using h_log_ineq

private lemma pos_delta_bound_4_term2_algebraic_bound
    {C₁ C₂ v_norm δ ε M : ℝ} (hδ : 0 < δ) (h_log_pos : 0 < Real.log (1 / ε))
    (hM_def : M = (C₁ + C₂) * v_norm / δ) (h_log_bound' : M ≤ Real.log (1 / ε)) :
    (C₁ + C₂) * (v_norm / Real.log (1 / ε)) ≤ δ := by
  rw [hM_def] at h_log_bound'
  have h_mul : (C₁ + C₂) * v_norm ≤ δ * Real.log (1 / ε) := by
    have := (div_le_iff₀ hδ).mp h_log_bound'
    linarith
  calc
    (C₁ + C₂) * (v_norm / Real.log (1 / ε)) = ((C₁ + C₂) * v_norm) / Real.log (1 / ε) := by ring
    _ ≤ (δ * Real.log (1 / ε)) / Real.log (1 / ε) :=
      div_le_div_of_nonneg_right h_mul h_log_pos.le
    _ = δ := by field_simp [h_log_pos.ne.symm]

private lemma inner_bound_helper {ι : Type*} [Fintype ι]
    {a b : EuclideanSpace ℝ ι} {norm_b C : ℝ}
    (h_norm_a : ‖a‖ ≤ C) (h_norm_b : ‖b‖ = norm_b)
    (h_C_nonneg : 0 ≤ C) (h_norm_b_nonneg : 0 ≤ norm_b) :
    inner ℝ a b ≤ C * norm_b := by
  have h_abs := abs_real_inner_le_norm a b
  have h_inner_le_norm_mul : inner ℝ a b ≤ ‖a‖ * ‖b‖ := (abs_le.mp h_abs).right
  calc
    inner ℝ a b ≤ ‖a‖ * ‖b‖ := h_inner_le_norm_mul
    _ ≤ C * norm_b := by
      rw [h_norm_b]
      exact mul_le_mul h_norm_a (le_refl _) h_norm_b_nonneg h_C_nonneg

private lemma target_norm_helper {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (ε : ℝ)
    (β : EuclideanSpace ℝ ι) (u : ℝ → EuclideanSpace ℝ ι)
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hβ : NonzeroCoordinates β)
    (hu : posDlnGradientFlow M r lambda ε β u) (v : EuclideanSpace ℝ ι)
    (hv_def : v = euclideanOf (fun i => Real.log ((β i) ^ 2)))
    (h_log_pos : 0 < Real.log (1 / ε)) :
    ‖ones - posRescaledMirrorVariable ε u 0‖ = ‖v‖ / Real.log (1 / ε) := by
  have h_eq_vec : ones - posRescaledMirrorVariable ε u 0 =
      ((Real.log (1 / ε))⁻¹ : ℝ) • v := by
    rw [hv_def]
    exact posRescaledMirrorVariable_zero_eq M r lambda ε β u hε_pos hε_lt_one hβ hu
  rw [h_eq_vec, norm_smul]
  have h_nonneg_inv : 0 ≤ (Real.log (1 / ε))⁻¹ := inv_nonneg.mpr (le_of_lt h_log_pos)
  rw [Real.norm_of_nonneg h_nonneg_inv]
  field_simp [h_log_pos.ne.symm]

private lemma posIntegratedTrajectoryRescaled_deriv_bound {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ) (ε : ℝ)
    (β : EuclideanSpace ℝ ι) (u_eps : ℝ → EuclideanSpace ℝ ι)
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (h_log_pos : 0 < Real.log (1 / ε))
    (hu : posDlnGradientFlow M r lambda ε β u_eps)
    (C₁ : ℝ)
    (hbound : ∀ t, 0 ≤ t → ‖posEffectiveParameter u_eps t‖ ≤ C₁)
    (τ : ℝ) (hτ_low : 0 ≤ τ) :
    ‖(deriv (fun (ρ : ℝ) => posIntegratedTrajectoryRescaled ε u_eps ρ) τ :
      EuclideanSpace ℝ ι)‖ ≤ C₁ := by
  have h_cont_u : Continuous u_eps := hu.cont_diff.continuous
  rw [(posIntegratedTrajectoryRescaled_hasDerivAt ε u_eps τ h_cont_u (ne_of_gt h_log_pos)).deriv]
  have ht_nonneg : 0 ≤ posTimeFromRescaled ε τ := by
    rw [posTimeFromRescaled]
    have h_one_le_div : 1 ≤ 1 / ε := (one_le_div hε_pos).mpr hε_lt_one.le
    exact mul_nonneg (div_nonneg hτ_low (by norm_num)) (Real.log_nonneg h_one_le_div)
  exact hbound (posTimeFromRescaled ε τ) ht_nonneg

lemma pos_delta_bound_4_term2
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (h_bounded : ∃ C > 0, ∀ τ ∈ Set.Icc (0 : ℝ) s, ‖deriv (scaledPrimalPath x_lasso) τ‖ ≤ C) :
    ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        ⟪(deriv (fun (ρ : ℝ) => posIntegratedTrajectoryRescaled ε (u ε) ρ) τ : EuclideanSpace ℝ ι) -
          (deriv (scaledPrimalPath x_lasso) τ : EuclideanSpace ℝ ι),
          ((ones : EuclideanSpace ℝ ι) - posRescaledMirrorVariable ε (u ε) 0)⟫_ℝ
        ≤ δ := by
  intro δ hδ
  rcases h_bounded with ⟨C₂, hC₂pos, hC₂⟩
  obtain ⟨C₁, ε₀, hC₁pos, hε₀pos, hbound⟩ :=
    pos_trajectory_uniform_bound M r lambda β u hdata hβ hu
  -- The vector v with entries log(β_i²); its norm is a constant depending only on β
  set v : EuclideanSpace ℝ ι := euclideanOf (fun i => Real.log ((β i)^2)) with hv_def
  -- Set M_bound = (C₁+C₂)*‖v‖/δ; when ‖v‖=0 this is 0 and the argument still works
  set M_bound : ℝ := (C₁ + C₂) * ‖v‖ / δ with hM_bound_def
  -- Choose ε₁ small enough so that log(1/ε₁) ≥ M_bound
  set ε₁ : ℝ := min (min ε₀ (1/2 : ℝ)) (Real.exp (-M_bound)) with hε₁_def
  have hε₁pos : 0 < ε₁ := by
    refine lt_min (lt_min hε₀pos (by norm_num)) (Real.exp_pos _)
  have hε₁_le_ε₀ : ε₁ ≤ ε₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε₁_lt_one : ε₁ < 1 := by
    have h : min ε₀ (1/2 : ℝ) ≤ 1/2 := min_le_right _ _
    have h' : min (min ε₀ (1/2 : ℝ)) (Real.exp (-M_bound)) ≤ min ε₀ (1/2 : ℝ) := min_le_left _ _
    linarith
  -- For ε ∈ (0, ε₁], we have log(1/ε) ≥ M_bound
  have h_log_bound (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ ε₁) : M_bound ≤ Real.log (1 / ε) := by
    have h_exp_le : ε ≤ Real.exp (-M_bound) := le_trans hε_le (min_le_right _ _)
    exact le_log_one_div_of_le_exp_neg hε_pos h_exp_le
  -- Filter: ε ∈ (0, ε₁)
  have h_eventually : Set.Ioo (0 : ℝ) ε₁ ∈ 𝓝[>] (0 : ℝ) := by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨ε₁, hε₁pos, fun _ hx => hx⟩
  filter_upwards [h_eventually] with ε hε
  rcases hε with ⟨hε_pos, hε_lt_ε₁⟩
  have hε_le_ε₁ : ε ≤ ε₁ := hε_lt_ε₁.le
  have hε_lt_one : ε < 1 := by linarith
  have h_log_pos : 0 < Real.log (1 / ε) :=
    Real.log_pos (one_lt_one_div hε_pos hε_lt_one)
  intro τ hτ
  rcases hτ with ⟨hτ_low, hτ_high⟩
  -- Step 1: bound ‖deriv(z^ε)(τ)‖ ≤ C₁
  have h_deriv_zε_norm :=
    posIntegratedTrajectoryRescaled_deriv_bound M r lambda ε β (u ε) hε_pos hε_lt_one h_log_pos
      (hu ε hε_pos) C₁ (hbound ε hε_pos (hε_le_ε₁.trans hε₁_le_ε₀)) τ hτ_low
  -- Step 2: bound ‖deriv(z)(τ)‖ ≤ C₂
  have h_deriv_z_norm := hC₂ τ ⟨hτ_low, hτ_high⟩
  -- Step 3: triangle inequality for the derivative difference
  have h_diff_norm := le_trans (norm_sub_le _ _) (add_le_add h_deriv_zε_norm h_deriv_z_norm)
  -- Step 4: bound ‖ones - w^ε(0)‖ = ‖v‖ / log(1/ε)
  have h_target_norm :
      ‖(ones : EuclideanSpace ℝ ι) - posRescaledMirrorVariable ε (u ε) 0‖
        = ‖v‖ / Real.log (1 / ε) :=
    target_norm_helper M r lambda ε β (u ε) hε_pos hε_lt_one hβ (hu ε hε_pos) v hv_def
      h_log_pos
  -- Step 5 & 6: Cauchy-Schwarz and combine with log bound
  have h_inner_bound := inner_bound_helper h_diff_norm h_target_norm
    (add_nonneg hC₁pos.le hC₂pos.le) (div_nonneg (norm_nonneg _) h_log_pos.le)
  have h_final : (C₁ + C₂) * (‖v‖ / Real.log (1 / ε)) ≤ δ :=
    pos_delta_bound_4_term2_algebraic_bound hδ h_log_pos hM_bound_def
      (h_log_bound ε hε_pos hε_le_ε₁)
  exact le_trans h_inner_bound h_final

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
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_lipschitz : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        inner ℝ (deriv (scaledPrimalPath x_lasso) τ)
          (matVec M (scaledPrimalPath x_lasso τ) - τ • r + (1 + τ * lambda) • ones) +
        inner ℝ (deriv (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) τ -
          deriv (scaledPrimalPath x_lasso) τ)
          (ones - posRescaledMirrorVariable ε (u ε) 0)
        ≤ δ := by
  intro δ hδ
  have h_bound := scaledPrimalPath_deriv_bound x_lasso h_lipschitz s hs
  have h2 := pos_delta_bound_4_term2 M r lambda β s u hdata hβ hu x_lasso h_bound δ hδ
  filter_upwards [h2] with ε hε
  intro τ hτ
  have h1 := pos_delta_bound_4_term1 M r lambda x_lasso hx_lasso hdata τ hτ.1
  have h2_eval := hε τ hτ
  linarith

/--
Reusable calculus fact.  If a real function agrees with an affine map on a
neighborhood of a differentiable point, then its derivative is constant on that
neighborhood.  This is the abstract step that turns "the Lasso path is piecewise
linear" into "coordinate derivatives are locally constant at differentiable
points".
-/
lemma deriv_locally_constant_of_eventually_affine {f : ℝ → ℝ} {x : ℝ}
    (_h_diff : DifferentiableAt ℝ f x)
    (h : ∃ a b, ∀ᶠ t in 𝓝 x, f t = a * t + b) :
    ∃ ε > 0, ∀ t, |t - x| < ε → deriv f t = deriv f x := by
  rcases h with ⟨a, b, h_aff⟩
  rw [Metric.eventually_nhds_iff_ball] at h_aff
  rcases h_aff with ⟨ε, hε_pos, h_aff⟩
  use ε, hε_pos
  intro t ht
  have ht' : t ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs]
    exact ht
  have h_affine_deriv {y : ℝ} (hy : y ∈ Metric.ball x ε) : deriv f y = a := by
    have h_eq : f =ᶠ[𝓝 y] fun u => a * u + b := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hy] with u hu
      exact h_aff u hu
    rw [Filter.EventuallyEq.deriv_eq h_eq]
    simp [deriv_const_mul_id]
  rw [h_affine_deriv ht', h_affine_deriv (Metric.mem_ball_self hε_pos)]

/-- Explicit regularity of a selected positive-Lasso path: each coordinate of
the scaled path is locally affine at every nonnegative parameter where that
coordinate is differentiable.

This property holds for a particular piecewise-affine path produced by an
active-set/LARS selection. It does not follow merely from pointwise optimality
when the primal minimizer is nonunique: an arbitrary selection may move
nonlinearly inside the kernel of the positive-semidefinite matrix while keeping
the same dual certificate.

The domain includes `μ = 0`: by Lemma 4.10 of `docs/Lasso.md` (Sec. 4.5), the
parametric LCP solution is the trivial one, `z(μ) = 0`, for all `μ` in some
interval `[0, μ₀)`, so the scaled path is (constantly, hence affinely) regular
all the way down to the boundary parameter `0`, not just on the open ray.
-/
structure ScaledPrimalPathLocallyAffineAtDifferentiable
    (x_lasso : ℝ → EuclideanSpace ℝ ι) : Prop where
  eventually_affine :
    ∀ i μ, 0 ≤ μ →
      DifferentiableAt ℝ (fun t => t * (x_lasso t).ofLp i) μ →
      ∃ a b, ∀ᶠ t in 𝓝 μ, t * (x_lasso t).ofLp i = a * t + b

omit [Fintype ι] in
/--
Local-affinity projection for a selected positive-Lasso regularization path.

INFORMAL PROOF:
The hypothesis `h_local_affine` says exactly that every differentiable coordinate
of the selected scaled path agrees with an affine function on a neighborhood of
each positive parameter. Applying its `eventually_affine` field proves the
conclusion directly.

This hypothesis is essential. For a singular PSD matrix, the primal solution of
the parametric LCP can be nonunique even though its dual solution is unique. For
example, with the two-by-two all-ones matrix, `r = (2,2)`, and `λ = 0`, every
nonnegative split of total mass `2μ - 1` solves the scaled LCP when `μ > 1/2`.
Choosing that split by a smooth non-affine weight gives a differentiable minimizer
selection which is not locally affine, while the dual path is identically zero.

References:
• Efron, Hastie, Johnstone & Tibshirani, "Least Angle Regression",
  Ann. Statist. 32 (2004), Thm. 1, https://doi.org/10.1214/009053604000000067
  (constructs a particular piecewise-linear LARS solution path).
• Tibshirani, "The Lasso Problem and Uniqueness" (2013),
  https://arxiv.org/abs/1206.0313 (distinguishes nonunique lasso minimizers from
  the particular continuous piecewise-linear path selected by the extended LARS
  algorithm).
• `docs/Lasso.md`, Sections 4.5--4.6, assumes an absolutely continuous selected
  primal path and proves piecewise regularity only for the unique dual path.
-/
lemma scaledPrimalPath_coord_affine_at_differentiable
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (h_local_affine : ScaledPrimalPathLocallyAffineAtDifferentiable x_lasso)
    (i : ι) (μ : ℝ) (hμ : 0 ≤ μ)
    (h_diff : DifferentiableAt ℝ (fun u' => u' * (x_lasso u').ofLp i) μ) :
    ∃ a b, ∀ᶠ t in 𝓝 μ, t * (x_lasso t).ofLp i = a * t + b := by
  exact h_local_affine.eventually_affine i μ hμ h_diff

/--
INFORMAL PROOF:
Differentiability of the vector-valued scaled path `z(μ) = μx(μ)` implies
differentiability of each coordinate `z_i`.  By
`scaledPrimalPath_coord_affine_at_differentiable` the coordinate is locally
affine at that point, and `deriv_locally_constant_of_eventually_affine` turns
local affinity into local constancy of the derivative.

The `0 ≤ τ'` hypothesis matches the domain on which
`ScaledPrimalPathLocallyAffineAtDifferentiable` records regularity: the
nonnegative parameter domain used by the Lasso path (see the structure's
docstring for why `μ = 0` is included).
-/
lemma scaledPrimalPath_deriv_locally_constant
    {ι : Type*} [Fintype ι]
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (h_local_affine : ScaledPrimalPathLocallyAffineAtDifferentiable x_lasso)
    (τ' : ℝ) (i' : ι) (hτ' : 0 ≤ τ')
    (h_diff : DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ') :
    ∃ ε > 0, ∀ t, |t - τ'| < ε →
      deriv (fun u' => (scaledPrimalPath x_lasso u') i') t =
      deriv (fun u' => (scaledPrimalPath x_lasso u') i') τ' := by
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv
  have h_coord_diff : DifferentiableAt ℝ (fun u' => (scaledPrimalPath x_lasso u') i') τ' := by
    have h_hasDeriv : HasDerivAt (fun u' => e (scaledPrimalPath x_lasso u'))
        (e (deriv (scaledPrimalPath x_lasso) τ')) τ' :=
      e.hasFDerivAt.comp_hasDerivAt τ' h_diff.hasDerivAt
    exact ((hasDerivAt_pi.1 h_hasDeriv) i').differentiableAt
  have h_aff := scaledPrimalPath_coord_affine_at_differentiable
    x_lasso h_local_affine i' τ' hτ' h_coord_diff
  exact deriv_locally_constant_of_eventually_affine h_coord_diff h_aff

lemma pos_delta_alg_ineq {C1 C3 δ : ℝ} {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1)
    {A B : ℝ} (hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B) :
    C1 / Real.log (1 / ε) + 0 + C3 * (1 / Real.log (1 / ε) * A + B) + δ
    ≤ max C1 C3 * (1 / Real.log (1 / ε) * (1 + A) + B) + δ := by
  have h_log_pos : 0 < Real.log (1 / ε) := Real.log_pos (one_lt_one_div hε_pos hε_lt)
  have hL_nonneg : 0 ≤ 1 / Real.log (1 / ε) := div_nonneg (by norm_num) h_log_pos.le
  set L := 1 / Real.log (1 / ε)
  set M := max C1 C3
  have hC1M : C1 ≤ M := le_max_left _ _
  have hC3M : C3 ≤ M := le_max_right _ _
  have hLA_nonneg : 0 ≤ L * A := mul_nonneg hL_nonneg hA_nonneg
  have h_sum : C1 * L + C3 * (L * A + B) ≤ M * (L * (1 + A) + B) := by
    have h1 : C1 * L ≤ M * L := mul_le_mul_of_nonneg_right hC1M hL_nonneg
    have h2 : C3 * (L * A) ≤ M * (L * A) := mul_le_mul_of_nonneg_right hC3M hLA_nonneg
    have h3 : C3 * B ≤ M * B := mul_le_mul_of_nonneg_right hC3M hB_nonneg
    nlinarith
  -- `h_sum` above is stated in the `set`-folded `L`/`M` notation.  `linarith` needs its atoms
  -- to match the goal syntactically: the goal's `C1 / Real.log (1/ε)` was never folded into
  -- `L` (it isn't syntactically `1 / Real.log (1/ε)`, so `set` could not rewrite it), so we
  -- unfold `L`/`M` in `h_sum` and separately turn the goal's division into `C1 * (1/Real.log
  -- (1/ε))` via `div_eq_mul_one_div` to line the two representations up before `linarith`.
  dsimp only [L, M] at h_sum ⊢
  rw [div_eq_mul_one_div C1]
  linarith

/--
Almost every point of `[0, s]` is a differentiability point of the scaled primal path,
obtained coordinate-by-coordinate from the scalar Mathlib fact
`AbsolutelyContinuousOnInterval.ae_differentiableAt` (which does not generalize to
vector-valued curves) via `LipschitzWith.comp_absolutelyContinuousOnInterval` and the
finite-coordinate characterization `differentiableAt_piLp` of differentiability on
`EuclideanSpace ℝ ι = PiLp 2 (fun _ => ℝ)`.
-/
lemma scaledPrimalPath_ae_differentiable
    {x_lasso : ℝ → EuclideanSpace ℝ ι} {s : ℝ} (hs : 0 < s)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    ∀ᵐ τ ∂volume, τ ∈ Set.Icc 0 s → DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ := by
  have hs_nonneg : 0 ≤ s := le_of_lt hs
  have h_ac : AbsolutelyContinuousOnInterval (scaledPrimalPath x_lasso) 0 s :=
    h_regular.absolutelyContinuousOn_Icc 0 s le_rfl hs_nonneg
  have h_coord : ∀ i : ι, ∀ᵐ τ ∂volume, τ ∈ Set.Icc 0 s →
      DifferentiableAt ℝ (fun t => (scaledPrimalPath x_lasso t) i) τ := by
    intro i
    have h_lip : LipschitzWith 1 (fun x : EuclideanSpace ℝ ι => x i) :=
      LipschitzWith.of_dist_le_mul (fun x y => by
        simpa [dist_eq_norm] using PiLp.norm_apply_le (x - y) i)
    have h_ac_i : AbsolutelyContinuousOnInterval
        ((fun x : EuclideanSpace ℝ ι => x i) ∘ scaledPrimalPath x_lasso) 0 s :=
      h_lip.comp_absolutelyContinuousOnInterval h_ac
    have h := h_ac_i.ae_differentiableAt
    rwa [Set.uIcc_of_le hs_nonneg] at h
  have h_all : ∀ᵐ τ ∂volume, ∀ i : ι, τ ∈ Set.Icc 0 s →
      DifferentiableAt ℝ (fun t => (scaledPrimalPath x_lasso t) i) τ :=
    ae_all_iff.2 h_coord
  filter_upwards [h_all] with τ hτ hτ_mem
  exact (differentiableAt_piLp 2).2 (fun i => hτ i hτ_mem)

/--
Almost every point of `[0, s]` is a differentiability point of both
`positiveZUpward` and `positiveZDownward`.

Informal proof: combine a.e. differentiability of the scaled primal path
(`scaledPrimalPath_ae_differentiable`) with local affinity of its coordinates
(`scaledPrimalPath_deriv_locally_constant`) to get, for a.e. `τ`, that every
coordinate derivative of `x_lasso` is locally constant near `τ`; this makes each
summand of `positiveZUpward`/`positiveZDownward` an integral of a function that is
continuous (indeed locally constant) at `τ`, hence differentiable there by the
Fundamental Theorem of Calculus (`intervalIntegral.integral_hasDerivAt_right`,
via `positiveZUpward_summand_differentiableAt` / `positiveZDownward_summand_differentiableAt`),
and a finite sum of differentiable functions is differentiable
(`DifferentiableAt.fun_sum`). The single exceptional point `τ = 0`, where local
affinity is not assumed, is discarded for free since `{0}` is Lebesgue-null.
-/
lemma positiveZ_ae_differentiable
    (x_lasso : ℝ → EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 < s)
    (h_local_affine : ScaledPrimalPathLocallyAffineAtDifferentiable x_lasso)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    ∀ᵐ τ ∂volume, τ ∈ Set.Icc (0 : ℝ) s →
      DifferentiableAt ℝ (positiveZUpward x_lasso) τ ∧
      DifferentiableAt ℝ (positiveZDownward x_lasso) τ := by
  have h_path_diff_ae := scaledPrimalPath_ae_differentiable hs h_regular
  have h_ne_zero : ∀ᵐ τ ∂volume, τ ≠ (0 : ℝ) := by
    rw [ae_iff]
    have heq : {a : ℝ | ¬ a ≠ 0} = {0} := by ext a; simp
    rw [heq]
    exact Real.volume_singleton
  filter_upwards [h_path_diff_ae, h_ne_zero] with τ h_path_diff hτ_ne
  intro hτ_mem
  have hτ_pos : 0 < τ := lt_of_le_of_ne hτ_mem.left (Ne.symm hτ_ne)
  have h_path_diff_at : DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ := h_path_diff hτ_mem
  have h_const : ∀ i, ∃ ε > 0, ∀ t, |t - τ| < ε →
      deriv (fun u' => u' * (x_lasso u').ofLp i) t =
      deriv (fun u' => u' * (x_lasso u').ofLp i) τ := fun i =>
    scaledPrimalPath_deriv_locally_constant x_lasso h_local_affine τ i hτ_pos.le h_path_diff_at
  refine ⟨?_, ?_⟩
  · unfold positiveZUpward
    exact DifferentiableAt.fun_sum (fun i _ =>
      positiveZUpward_summand_differentiableAt x_lasso τ hτ_mem.left i h_regular (h_const i))
  · unfold positiveZDownward
    exact DifferentiableAt.fun_sum (fun i _ =>
      positiveZDownward_summand_differentiableAt x_lasso τ hτ_mem.left i h_regular (h_const i))

/--
Monotone-case analogue of `positiveZ_ae_differentiable`: a.e. differentiability of
`positiveZUpward`/`positiveZDownward` on `[0,s]`, derived from coordinatewise monotonicity of
`z = scaledPrimalPath x_lasso` instead of `ScaledPrimalPathLocallyAffineAtDifferentiable`.

Informal proof: by the closed forms `positiveZDownward_eq_zero_of_monotone`
(`positiveZDownward x_lasso ≡ 0` on `[0,∞)`) and `positiveZUpward_eq_sum_of_monotone`
(`positiveZUpward x_lasso μ = ∑ i, z_i μ` on `[0,∞)`), both functions agree *everywhere* on
`(0,∞)` with, respectively, the constant `0` and the finite sum `∑ i, z_i`. Both of these are
differentiable at every `τ` where `z` itself is (the constant trivially; the finite sum by
linearity), and `z` is differentiable a.e. on `[0,s]` purely from `h_regular`
(`scaledPrimalPath_ae_differentiable`, needing no structural hypothesis at all). Excluding the
single point `τ = 0` (Lebesgue-null, as in `positiveZ_ae_differentiable`) so that the closed
forms' `(0,∞)`-agreement gives a genuine two-sided `EventuallyEq` at `τ`, transporting
differentiability along it gives the claim. Citation: `docs/Lasso.md`, Sec. 3.1/4.7 (Lemma
4.12); Mathlib's `Monotone.ae_hasDerivAt` for the underlying Lebesgue monotone-differentiation
fact used by the closed forms.
-/
lemma positiveZ_ae_differentiable_of_monotone
    (x_lasso : ℝ → EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 < s)
    (h_mono : ∀ ν ν', 0 ≤ ν → ν ≤ ν' → ∀ i, ν * (x_lasso ν).ofLp i ≤ ν' * (x_lasso ν').ofLp i)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    ∀ᵐ τ ∂volume, τ ∈ Set.Icc (0 : ℝ) s →
      DifferentiableAt ℝ (positiveZUpward x_lasso) τ ∧
      DifferentiableAt ℝ (positiveZDownward x_lasso) τ := by
  have h_path_diff_ae := scaledPrimalPath_ae_differentiable hs h_regular
  have h_ne_zero : ∀ᵐ τ ∂volume, τ ≠ (0 : ℝ) := by
    rw [ae_iff]
    have heq : {a : ℝ | ¬ a ≠ 0} = {0} := by ext a; simp
    rw [heq]
    exact Real.volume_singleton
  filter_upwards [h_path_diff_ae, h_ne_zero] with τ h_path_diff hτ_ne
  intro hτ_mem
  have hτ_pos : 0 < τ := lt_of_le_of_ne hτ_mem.left (Ne.symm hτ_ne)
  have h_path_diff_at : DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ := h_path_diff hτ_mem
  have h_pos_mem : Set.Ioi (0 : ℝ) ∈ 𝓝 τ :=
    isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hτ_pos)
  have h_down_eq : positiveZDownward x_lasso =ᶠ[𝓝 τ] fun _ => (0 : ℝ) := by
    filter_upwards [h_pos_mem] with μ hμ
    exact positiveZDownward_eq_zero_of_monotone x_lasso μ hμ.le h_regular h_mono
  have h_up_eq : positiveZUpward x_lasso =ᶠ[𝓝 τ]
      fun μ => ∑ i, (scaledPrimalPath x_lasso μ) i := by
    filter_upwards [h_pos_mem] with μ hμ
    exact positiveZUpward_eq_sum_of_monotone x_lasso μ hμ.le h_regular h_mono
  have h_down_diff : DifferentiableAt ℝ (positiveZDownward x_lasso) τ :=
    (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq h_down_eq
  have h_coord_diff (i : ι) : DifferentiableAt ℝ
      (fun μ => (scaledPrimalPath x_lasso μ) i) τ :=
    (differentiableAt_piLp 2).1 h_path_diff_at i
  have h_sum_diff : DifferentiableAt ℝ
      (fun μ => ∑ i ∈ Finset.univ, (scaledPrimalPath x_lasso μ) i) τ :=
    DifferentiableAt.fun_sum (fun i hi => h_coord_diff i)
  have h_up_diff : DifferentiableAt ℝ (positiveZUpward x_lasso) τ :=
    h_sum_diff.congr_of_eventuallyEq h_up_eq
  exact ⟨h_up_diff, h_down_diff⟩

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
    (β : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (Mdagger : Matrix ι ι ℝ) (w : ℝ → EuclideanSpace ℝ ι)
    (_hdual : ParametricLCPDualRegular M Mdagger r lambda w)
    (_hdual_selected : ∀ μ, 0 ≤ μ →
      isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ))
    (h_local_affine : ScaledPrimalPathLocallyAffineAtDifferentiable x_lasso)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_lipschitz : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ s : ℝ, 0 < s → ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      ∀ᵐ τ ∂volume, τ ∈ Set.Icc (0 : ℝ) s →
        deriv
          (fun σ =>
            pathDelta M
              (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
              (scaledPrimalPath x_lasso) σ) τ
        ≤ C *
          (1 / Real.log (1 / ε) *
              (1 + deriv (positiveZUpward x_lasso) τ) +
            deriv (positiveZDownward x_lasso) τ) + δ := by
  obtain ⟨C1, hC1, h1⟩ := pos_delta_bound_1 M r lambda β u hdata hβ hu
  have h_piecewise_deriv : ∀ (τ' : ℝ) (i' : ι), 0 ≤ τ' →
      DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ' →
      ∃ ε > 0, ∀ t, |t - τ'| < ε →
        deriv (fun u' => u' * (x_lasso u').ofLp i') t =
        deriv (fun u' => u' * (x_lasso u').ofLp i') τ' :=
    fun τ' i' hτ' h_diff =>
      scaledPrimalPath_deriv_locally_constant x_lasso h_local_affine τ' i' hτ' h_diff
  obtain ⟨C3, hC3, h3⟩ := pos_delta_bound_3 M r lambda β u hdata hβ hu x_lasso
    hx_lasso h_regular h_piecewise_deriv
  refine ⟨max C1 C3, lt_max_of_lt_left hC1, fun s hs δ hδ => ?_⟩
  have h2 := pos_delta_bound_2 M r lambda β s hs u hdata hu x_lasso hx_lasso
  have h4 := pos_delta_bound_4 M r lambda β s hs u hdata hβ hu x_lasso hx_lasso
    h_lipschitz δ hδ
  filter_upwards [h1 s hs, h2, h3 s hs, h4, by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨1, by norm_num, fun _ hx => hx⟩] with ε h1ε h2ε h3ε h4ε hε_range
  have h_path_diff_ae : ∀ᵐ τ ∂volume, τ ∈ Set.Icc 0 s →
      DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ :=
    scaledPrimalPath_ae_differentiable hs h_regular
  filter_upwards [h_path_diff_ae] with τ h_path_diff
  intro hτ_mem
  have h_log_pos : 0 < Real.log (1 / ε) :=
    Real.log_pos (one_lt_one_div hε_range.1 hε_range.2)
  have h_nonneg := positiveZ_deriv_nonneg x_lasso τ hτ_mem.left h_regular
  have hA_nonneg : 0 ≤ deriv (positiveZUpward x_lasso) τ := h_nonneg.1
  have hB_nonneg : 0 ≤ deriv (positiveZDownward x_lasso) τ := h_nonneg.2
  have h_alg : C1 / Real.log (1 / ε) + 0 +
      C3 * (1 / Real.log (1 / ε) * deriv (positiveZUpward x_lasso) τ +
        deriv (positiveZDownward x_lasso) τ) + δ
    ≤ max C1 C3 * (1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
      deriv (positiveZDownward x_lasso) τ) + δ :=
    pos_delta_alg_ineq hε_range.1 hε_range.2 hA_nonneg hB_nonneg
  have h_path_diff_at : DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ := h_path_diff hτ_mem
  have hM : M.IsSymm := hdata.psd.symm
  have hlog_ne : Real.log (1 / ε) ≠ 0 := h_log_pos.ne'
  have hzε_deriv : HasDerivAt (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
      (deriv (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) τ) τ := by
    have h0 := posIntegratedTrajectoryRescaled_hasDerivAt ε (u ε) τ
      (hu ε hε_range.1).cont_diff.continuous hlog_ne
    rwa [h0.deriv]
  have hz_deriv : HasDerivAt (scaledPrimalPath x_lasso)
      (deriv (scaledPrimalPath x_lasso) τ) τ := h_path_diff_at.hasDerivAt
  have h_chain := pathDelta_hasDerivAt M hM
    (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) (scaledPrimalPath x_lasso)
    (deriv (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) τ)
    (deriv (scaledPrimalPath x_lasso) τ) τ hzε_deriv hz_deriv
  have hM_zε : matVec M (posIntegratedTrajectoryRescaled ε (u ε) τ) =
      posRescaledMirrorVariable ε (u ε) τ - posRescaledMirrorVariable ε (u ε) 0 +
        τ • r - (τ * lambda) • ones := by
    have h := positive_integrated_mirror_equation M r lambda ε β (u ε) (hu ε hε_range.1)
      (pos_effective_param_ne_zero M r lambda β u hdata hβ hu ε hε_range.1) hM τ hlog_ne
    rw [h]; abel
  have hM_diff : matVec M (posIntegratedTrajectoryRescaled ε (u ε) τ -
      scaledPrimalPath x_lasso τ) =
      (posRescaledMirrorVariable ε (u ε) τ -
        (matVec M (scaledPrimalPath x_lasso τ) - τ • r + (1 + τ * lambda) • ones)) +
      (ones - posRescaledMirrorVariable ε (u ε) 0) := by
    rw [matVec_sub, hM_zε, add_smul, one_smul]
    abel
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
    rw [h_chain.deriv, hM_diff, inner_add_right, inner_sub_right,
      inner_sub_left, inner_sub_left]
    ring_nf
  rw [h_deriv_eq]
  linarith [h1ε τ hτ_mem, h2ε τ hτ_mem, h3ε τ hτ_mem, h4ε τ hτ_mem, h_alg]

/--
Monotone-case analogue of `positive_delta_complementarity_bound`: the same a.e. bound on
`deriv Δᵋ`, with `h_local_affine` replaced by coordinatewise monotonicity `h_mono` of
`z = scaledPrimalPath x_lasso`.

Informal proof: identical to `positive_delta_complementarity_bound`'s proof, except that the
internal call to `pos_delta_bound_3` (needing `h_piecewise_deriv`, built from
`h_local_affine` via `scaledPrimalPath_deriv_locally_constant`) is replaced by
`pos_delta_bound_3_of_monotone` (needing only `h_mono` directly) — every other ingredient
(`pos_delta_bound_1`, `pos_delta_bound_4`, the algebraic assembly) is unaffected by
monotonicity. Citation: `docs/Lasso.md`, Sec. 4.6, Eq. (4.14), and Sec. 3.1/4.7 for the
monotone specialization.
-/
lemma positive_delta_complementarity_bound_of_monotone
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε))
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ))
    (h_mono : ∀ ν ν', 0 ≤ ν → ν ≤ ν' → ∀ i, ν * (x_lasso ν).ofLp i ≤ ν' * (x_lasso ν').ofLp i)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_lipschitz : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ s : ℝ, 0 < s → ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      ∀ᵐ τ ∂volume, τ ∈ Set.Icc (0 : ℝ) s →
        deriv
          (fun σ =>
            pathDelta M
              (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
              (scaledPrimalPath x_lasso) σ) τ
        ≤ C *
          (1 / Real.log (1 / ε) *
              (1 + deriv (positiveZUpward x_lasso) τ) +
            deriv (positiveZDownward x_lasso) τ) + δ := by
  obtain ⟨C1, hC1, h1⟩ := pos_delta_bound_1 M r lambda β u hdata hβ hu
  obtain ⟨C3, hC3, h3⟩ := pos_delta_bound_3_of_monotone M r lambda β u hdata hβ hu
    x_lasso hx_lasso h_regular h_mono
  refine ⟨max C1 C3, lt_max_of_lt_left hC1, fun s hs δ hδ => ?_⟩
  have h2 := pos_delta_bound_2 M r lambda β s hs u hdata hu x_lasso hx_lasso
  have h4 := pos_delta_bound_4 M r lambda β s hs u hdata hβ hu x_lasso hx_lasso
    h_lipschitz δ hδ
  filter_upwards [h1 s hs, h2, h3 s hs, h4, by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨1, by norm_num, fun _ hx => hx⟩] with ε h1ε h2ε h3ε h4ε hε_range
  have h_path_diff_ae : ∀ᵐ τ ∂volume, τ ∈ Set.Icc 0 s →
      DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ :=
    scaledPrimalPath_ae_differentiable hs h_regular
  filter_upwards [h_path_diff_ae] with τ h_path_diff
  intro hτ_mem
  have h_log_pos : 0 < Real.log (1 / ε) :=
    Real.log_pos (one_lt_one_div hε_range.1 hε_range.2)
  have h_nonneg := positiveZ_deriv_nonneg x_lasso τ hτ_mem.left h_regular
  have hA_nonneg : 0 ≤ deriv (positiveZUpward x_lasso) τ := h_nonneg.1
  have hB_nonneg : 0 ≤ deriv (positiveZDownward x_lasso) τ := h_nonneg.2
  have h_alg : C1 / Real.log (1 / ε) + 0 +
      C3 * (1 / Real.log (1 / ε) * deriv (positiveZUpward x_lasso) τ +
        deriv (positiveZDownward x_lasso) τ) + δ
    ≤ max C1 C3 * (1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
      deriv (positiveZDownward x_lasso) τ) + δ :=
    pos_delta_alg_ineq hε_range.1 hε_range.2 hA_nonneg hB_nonneg
  have h_path_diff_at : DifferentiableAt ℝ (scaledPrimalPath x_lasso) τ := h_path_diff hτ_mem
  have hM : M.IsSymm := hdata.psd.symm
  have hlog_ne : Real.log (1 / ε) ≠ 0 := h_log_pos.ne'
  have hzε_deriv : HasDerivAt (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
      (deriv (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) τ) τ := by
    have h0 := posIntegratedTrajectoryRescaled_hasDerivAt ε (u ε) τ
      (hu ε hε_range.1).cont_diff.continuous hlog_ne
    rwa [h0.deriv]
  have hz_deriv : HasDerivAt (scaledPrimalPath x_lasso)
      (deriv (scaledPrimalPath x_lasso) τ) τ := h_path_diff_at.hasDerivAt
  have h_chain := pathDelta_hasDerivAt M hM
    (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) (scaledPrimalPath x_lasso)
    (deriv (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) τ)
    (deriv (scaledPrimalPath x_lasso) τ) τ hzε_deriv hz_deriv
  have hM_zε : matVec M (posIntegratedTrajectoryRescaled ε (u ε) τ) =
      posRescaledMirrorVariable ε (u ε) τ - posRescaledMirrorVariable ε (u ε) 0 +
        τ • r - (τ * lambda) • ones := by
    have h := positive_integrated_mirror_equation M r lambda ε β (u ε) (hu ε hε_range.1)
      (pos_effective_param_ne_zero M r lambda β u hdata hβ hu ε hε_range.1) hM τ hlog_ne
    rw [h]; abel
  have hM_diff : matVec M (posIntegratedTrajectoryRescaled ε (u ε) τ -
      scaledPrimalPath x_lasso τ) =
      (posRescaledMirrorVariable ε (u ε) τ -
        (matVec M (scaledPrimalPath x_lasso τ) - τ • r + (1 + τ * lambda) • ones)) +
      (ones - posRescaledMirrorVariable ε (u ε) 0) := by
    rw [matVec_sub, hM_zε, add_smul, one_smul]
    abel
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
    rw [h_chain.deriv, hM_diff, inner_add_right, inner_sub_right,
      inner_sub_left, inner_sub_left]
    ring_nf
  rw [h_deriv_eq]
  linarith [h1ε τ hτ_mem, h2ε τ hτ_mem, h3ε τ hτ_mem, h4ε τ hτ_mem, h_alg]

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
    (Mdagger : Matrix ι ι ℝ) (w : ℝ → EuclideanSpace ℝ ι)
    (hdual : ParametricLCPDualRegular M Mdagger r lambda w)
    (hdual_selected : ∀ μ, 0 ≤ μ →
      isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ))
    (h_local_affine : ScaledPrimalPathLocallyAffineAtDifferentiable x_lasso)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_lipschitz : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      ∀ᵐ τ ∂volume, τ ∈ Set.Icc (0 : ℝ) s →
        deriv
          (fun σ =>
            pathDelta M
              (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
              (scaledPrimalPath x_lasso) σ) τ
        ≤ C *
          (1 / Real.log (1 / ε) *
              (1 + deriv (positiveZUpward x_lasso) τ) +
            deriv (positiveZDownward x_lasso) τ) + δ := by
  obtain ⟨C, hC, h⟩ := positive_delta_complementarity_bound M r lambda β u hdata hβ hu x_lasso
    hx_lasso Mdagger w hdual hdual_selected h_local_affine h_regular h_lipschitz
  exact ⟨C, hC, h s hs⟩

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
    (h_deriv : ∀ᵐ τ ∂volume, τ ∈ Set.Icc 0 s → deriv F τ ≤ deriv G τ)
    (hF0 : F 0 = 0) (hG0 : G 0 = 0)
    (hF_ac : AbsolutelyContinuousOnInterval F 0 s)
    (hG_ac : AbsolutelyContinuousOnInterval G 0 s) :
    F s ≤ G s := by
  have hF_int : ∫ τ in 0..s, deriv F τ = F s - F 0 :=
    AbsolutelyContinuousOnInterval.integral_deriv_eq_sub hF_ac
  have hG_int : ∫ τ in 0..s, deriv G τ = G s - G 0 :=
    AbsolutelyContinuousOnInterval.integral_deriv_eq_sub hG_ac
  have h_mono : ∫ τ in 0..s, deriv F τ ≤ ∫ τ in 0..s, deriv G τ := by
    rw [intervalIntegral.integral_of_le hs, intervalIntegral.integral_of_le hs]
    apply setIntegral_mono_ae_restrict
    · have hF_int_on := AbsolutelyContinuousOnInterval.intervalIntegrable_deriv hF_ac
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs] at hF_int_on
      exact hF_int_on
    · have hG_int_on := AbsolutelyContinuousOnInterval.intervalIntegrable_deriv hG_ac
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hs] at hG_int_on
      exact hG_int_on
    · exact ae_restrict_of_ae_restrict_of_subset
        Set.Ioc_subset_Icc_self ((ae_restrict_iff' measurableSet_Icc).2 h_deriv)
  rw [hF_int, hG_int, hF0, hG0] at h_mono
  linarith

/--
Constant functions are absolutely continuous (Lipschitz with constant `0`).
-/
lemma absolutelyContinuousOnInterval_const (c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b := by
  have hK : LipschitzOnWith 0 (fun _ : ℝ => c) (Set.uIcc a b) := fun x _ y _ => by simp
  exact hK.absolutelyContinuousOnInterval

/--
A finite sum of absolutely continuous functions is absolutely continuous.
Not provided by `Mathlib.MeasureTheory.Function.AbsolutelyContinuous`, which only closes
`AbsolutelyContinuousOnInterval` under binary `add`/`sub`/`neg`/`smul`/`mul`; this extends
that closure to `Finset.sum` via `Finset.sum_induction`, reusing the `add` case and the
zero case (`absolutelyContinuousOnInterval_const`).
-/
lemma absolutelyContinuousOnInterval_sum {κ : Type*} (t : Finset κ)
    (f : κ → ℝ → ℝ) (a b : ℝ)
    (h : ∀ i ∈ t, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun x => ∑ i ∈ t, f i x) a b := by
  rw [show (fun x => ∑ i ∈ t, f i x) = ∑ i ∈ t, f i from (Finset.sum_fn t f).symm]
  exact Finset.sum_induction f (fun g => AbsolutelyContinuousOnInterval g a b)
    (fun _ _ h1 h2 => h1.add h2) (absolutelyContinuousOnInterval_const 0 a b) h

/--
Helper lemma: The path delta composition is absolutely continuous.

INFORMAL PROOF:
`pathDelta` is defined using inner products and norms of $z^\varepsilon(\tau)$ and $z(\tau)$.
Both $z^\varepsilon$ and $z$ are absolutely continuous on the compact interval $[0, s]$
(the former by properties of gradient flow, the latter by LCP regularity).
Since products and linear combinations of absolutely continuous functions on a compact
interval are absolutely continuous, the composition `pathDelta` is absolutely continuous.

More precisely: `zε = posIntegratedTrajectoryRescaled ε u_ε` is in fact `C¹` everywhere —
its derivative exists at every real `τ` (`posIntegratedTrajectoryRescaled_hasDerivAt`) and is
continuous in `τ` (a composition of the continuous `u_ε`, the continuous affine
reparametrization `posTimeFromRescaled ε`, and the continuous `coordinateSquare`) — so it is
absolutely continuous on `[0, s]` by `ContDiffOn.absolutelyContinuousOnInterval`. `z =
scaledPrimalPath x_lasso` is absolutely continuous on `[0, s]` by `h_regular`. Each coordinate
`(matVec M v) i = ∑ j, M i j * v j` is a fixed linear combination of the (1-Lipschitz,
hence absolutely continuous) coordinate projections of `v = zε - z`, so it is absolutely
continuous by `absolutelyContinuousOnInterval_sum` and `.const_mul` — this avoids routing
through the operator norm of `matVec M` as a bundled `ContinuousLinearMap`, which forces an
expensive `EuclideanSpace` defeq unification that times out at `whnf`. Finally the quadratic
form `⟨zε - z, M(zε - z)⟩` is a finite sum of products of coordinate projections of these two
absolutely continuous vector paths, so it is absolutely continuous by
`AbsolutelyContinuousOnInterval.mul` and `absolutelyContinuousOnInterval_sum`.

CITATION:
`docs/Lasso.md`, Section 4.6 (differential inequality integration).
-/
lemma pathDelta_ac {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (ε : ℝ)
    (u_ε : ℝ → EuclideanSpace ℝ ι) (x_lasso : ℝ → EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 ≤ s)
    (h_cont_u : Continuous u_ε) (h_log_ne : Real.log (1 / ε) ≠ 0)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    AbsolutelyContinuousOnInterval
      (fun τ ↦ pathDelta M (fun ρ ↦ posIntegratedTrajectoryRescaled ε u_ε ρ)
        (scaledPrimalPath x_lasso) τ) 0 s := by
  -- `zε` is globally `C¹`, hence absolutely continuous on `[0, s]`.
  have h_zε_deriv : ∀ τ, HasDerivAt (fun ρ => posIntegratedTrajectoryRescaled ε u_ε ρ)
      (posEffectiveParameter u_ε (posTimeFromRescaled ε τ)) τ :=
    fun τ => posIntegratedTrajectoryRescaled_hasDerivAt ε u_ε τ h_cont_u h_log_ne
  have h_deriv_eq : deriv (fun ρ => posIntegratedTrajectoryRescaled ε u_ε ρ) =
      fun τ => posEffectiveParameter u_ε (posTimeFromRescaled ε τ) :=
    funext (fun τ => (h_zε_deriv τ).deriv)
  have h_cont_time : Continuous (posTimeFromRescaled ε) := by
    unfold posTimeFromRescaled; fun_prop
  have h_cont_coordSquare :
      Continuous (coordinateSquare : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) := by
    let e : (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ ι :=
      (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toContinuousLinearEquiv
    have h_proj_cont (i : ι) : Continuous (fun (x : EuclideanSpace ℝ ι) => x i) :=
      (continuous_apply i).comp
        ((WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv.continuous)
    have h_eq : coordinateSquare = e ∘ (fun (x : EuclideanSpace ℝ ι) => fun i => x i * x i) := by
      ext x i; simp [coordinateSquare, euclideanOf, e]
    rw [h_eq]
    exact e.continuous.comp
      (continuous_pi (fun i => Continuous.mul (h_proj_cont i) (h_proj_cont i)))
  have h_cont_deriv : Continuous
      (fun τ => posEffectiveParameter u_ε (posTimeFromRescaled ε τ)) := by
    dsimp [posEffectiveParameter]
    exact h_cont_coordSquare.comp (h_cont_u.comp h_cont_time)
  have h_contDiff_zε : ContDiff ℝ 1 (fun ρ => posIntegratedTrajectoryRescaled ε u_ε ρ) :=
    contDiff_one_iff_deriv.mpr ⟨fun τ => (h_zε_deriv τ).differentiableAt,
      h_deriv_eq ▸ h_cont_deriv⟩
  have hzε_ac : AbsolutelyContinuousOnInterval
      (fun ρ => posIntegratedTrajectoryRescaled ε u_ε ρ) 0 s :=
    h_contDiff_zε.contDiffOn.absolutelyContinuousOnInterval
  -- `z` is absolutely continuous on `[0, s]` by `h_regular`.
  have hz_ac : AbsolutelyContinuousOnInterval (scaledPrimalPath x_lasso) 0 s :=
    h_regular.absolutelyContinuousOn_Icc 0 s le_rfl hs
  have hdiff_ac : AbsolutelyContinuousOnInterval
      (fun τ => posIntegratedTrajectoryRescaled ε u_ε τ - scaledPrimalPath x_lasso τ) 0 s :=
    hzε_ac.sub hz_ac
  -- `(matVec M v) i` is the fixed linear combination `∑ j, M i j * v j` of the coordinates
  -- of `v`, so it is absolutely continuous coordinatewise without going through the operator
  -- norm of `matVec M` as a bundled `ContinuousLinearMap` (that route forces an expensive
  -- `EuclideanSpace`/`LinearMap.toContinuousLinearMap` defeq unification that times out at
  -- `whnf`; see the `deterministic timeout at whnf` entry of `docs/lessons_learned.md`).
  have hM_coord_ac : ∀ i : ι, AbsolutelyContinuousOnInterval
      (fun τ => (matVec M (posIntegratedTrajectoryRescaled ε u_ε τ -
        scaledPrimalPath x_lasso τ)) i) 0 s := by
    intro i
    have h_coord_eq : ∀ τ, (matVec M (posIntegratedTrajectoryRescaled ε u_ε τ -
        scaledPrimalPath x_lasso τ)) i =
        ∑ j, M i j * (posIntegratedTrajectoryRescaled ε u_ε τ - scaledPrimalPath x_lasso τ) j := by
      intro τ
      simp [matVec, euclideanOf, Matrix.mulVec, dotProduct]
    have h_sum_ac : AbsolutelyContinuousOnInterval
        (fun τ => ∑ j, M i j *
          (posIntegratedTrajectoryRescaled ε u_ε τ - scaledPrimalPath x_lasso τ) j) 0 s := by
      apply absolutelyContinuousOnInterval_sum Finset.univ
        (fun j τ => M i j * (posIntegratedTrajectoryRescaled ε u_ε τ -
          scaledPrimalPath x_lasso τ) j)
      intro j _
      have h_lip : LipschitzWith 1 (fun x : EuclideanSpace ℝ ι => x j) :=
        LipschitzWith.of_dist_le_mul (fun x y => by
          simpa [dist_eq_norm] using PiLp.norm_apply_le (x - y) j)
      exact (LipschitzWith.comp_absolutelyContinuousOnInterval h_lip hdiff_ac).const_mul (M i j)
    simpa [h_coord_eq] using h_sum_ac
  -- Assemble via the `EuclideanSpace` inner-product formula and coordinatewise products.
  have h_term_ac : ∀ i : ι, AbsolutelyContinuousOnInterval
      (fun τ => (posIntegratedTrajectoryRescaled ε u_ε τ - scaledPrimalPath x_lasso τ) i *
        (matVec M (posIntegratedTrajectoryRescaled ε u_ε τ -
          scaledPrimalPath x_lasso τ)) i) 0 s := by
    intro i
    have h_lip : LipschitzWith 1 (fun x : EuclideanSpace ℝ ι => x i) :=
      LipschitzWith.of_dist_le_mul (fun x y => by
        simpa [dist_eq_norm] using PiLp.norm_apply_le (x - y) i)
    exact (LipschitzWith.comp_absolutelyContinuousOnInterval h_lip hdiff_ac).mul
      (hM_coord_ac i)
  have h_inner_ac : AbsolutelyContinuousOnInterval
      (fun τ => ∑ i, (posIntegratedTrajectoryRescaled ε u_ε τ - scaledPrimalPath x_lasso τ) i *
        (matVec M (posIntegratedTrajectoryRescaled ε u_ε τ -
          scaledPrimalPath x_lasso τ)) i) 0 s :=
    absolutelyContinuousOnInterval_sum Finset.univ _ 0 s (fun i _ => h_term_ac i)
  have h_eq_final : (fun τ ↦ pathDelta M (fun ρ ↦ posIntegratedTrajectoryRescaled ε u_ε ρ)
      (scaledPrimalPath x_lasso) τ) =
      fun τ => (1 / 2 : ℝ) * ∑ i, (posIntegratedTrajectoryRescaled ε u_ε τ -
        scaledPrimalPath x_lasso τ) i *
        (matVec M (posIntegratedTrajectoryRescaled ε u_ε τ - scaledPrimalPath x_lasso τ)) i := by
    funext τ
    simp only [pathDelta, matrixSeminormSq, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [h_eq_final]
  exact h_inner_ac.const_mul (1 / 2 : ℝ)

/--
`positiveZUpward x_lasso` is absolutely continuous on `[0, s]`.

Informal proof: `positiveZUpward x_lasso μ = ∑ i, ∫ u in 0..μ, max 0 (deriv f_i u)`, where
`f_i u = u * x_lasso(u) i`. Each summand is the interval integral (from a fixed lower endpoint)
of the `L¹` function `max 0 (deriv f_i)` (integrable by `max_zero_deriv_intervalIntegrable`,
itself a consequence of the 1-Lipschitz coordinate projection applied to `h_regular`), hence
absolutely continuous by the FTC-type lemma
`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`. Summing finitely many
absolutely continuous functions (`absolutelyContinuousOnInterval_sum`) gives the claim.

CITATION: `docs/Lasso.md`, Section 4.6.
-/
lemma positiveZUpward_ac {ι : Type*} [Fintype ι]
    (x_lasso : ℝ → EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 ≤ s)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    AbsolutelyContinuousOnInterval (positiveZUpward x_lasso) 0 s := by
  unfold positiveZUpward
  apply absolutelyContinuousOnInterval_sum Finset.univ
    (fun i (μ : ℝ) => ∫ u in (0 : ℝ)..μ, max 0 (deriv (fun u' => u' * (x_lasso u').ofLp i) u))
  intro i _
  have h_int : IntervalIntegrable
      (fun u => max 0 (deriv (fun u' => u' * (x_lasso u').ofLp i) u)) volume 0 s :=
    max_zero_deriv_intervalIntegrable x_lasso i s hs h_regular
  exact h_int.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc

/--
`positiveZDownward x_lasso` is absolutely continuous on `[0, s]`.

Informal proof: same shape as `positiveZUpward_ac`, using
`max_zero_neg_deriv_intervalIntegrable` for the integrability of the summand
`(1+u) * max 0 (-deriv f_i u)`.

CITATION: `docs/Lasso.md`, Section 4.6.
-/
lemma positiveZDownward_ac {ι : Type*} [Fintype ι]
    (x_lasso : ℝ → EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 ≤ s)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    AbsolutelyContinuousOnInterval (positiveZDownward x_lasso) 0 s := by
  unfold positiveZDownward
  apply absolutelyContinuousOnInterval_sum Finset.univ
    (fun i (μ : ℝ) => ∫ u in (0 : ℝ)..μ,
      (1 + u) * max 0 (-deriv (fun u' => u' * (x_lasso u').ofLp i) u))
  intro i _
  have h_int : IntervalIntegrable
      (fun u => (1 + u) * max 0 (-deriv (fun u' => u' * (x_lasso u').ofLp i) u))
      volume 0 s :=
    (max_zero_neg_deriv_intervalIntegrable x_lasso i s hs h_regular).continuousOn_mul
      (by fun_prop)
  exact h_int.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc

/--
Helper lemma: The G bound is absolutely continuous.

INFORMAL PROOF:
The upper bound function $G(\tau)$ is a linear combination of $\tau$, `positiveZUpward`,
and `positiveZDownward`. The latter two are defined as Lebesgue integrals of the non-negative
and non-positive parts of the derivative of $z(\tau)$, respectively. By the Fundamental
Theorem of Calculus for Lebesgue integration, the integral of an $L^1$ function is
absolutely continuous (`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`).
Summing these coordinatewise AC facts (`absolutelyContinuousOnInterval_sum`) gives AC of
`positiveZUpward`/`positiveZDownward` on `[0, s]`; `G` is then a fixed affine combination of
these two AC functions and the (Lipschitz, hence AC) identity `τ`, so it is AC by the
algebra-closure lemmas `.add`/`.const_mul`.

CITATION:
`docs/Lasso.md`, Section 4.6.
-/
lemma G_ac {ι : Type*} [Fintype ι] (C ε s δ : ℝ) (hs : 0 < s)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso)) :
    AbsolutelyContinuousOnInterval
      (fun τ ↦
        C * (1 / Real.log (1 / ε) * (τ + positiveZUpward x_lasso τ) +
          positiveZDownward x_lasso τ) + C * δ / s * τ) 0 s := by
  have h_id_ac : AbsolutelyContinuousOnInterval (fun τ : ℝ => τ) 0 s := by
    have hK : LipschitzOnWith 1 (fun τ : ℝ => τ) (Set.uIcc 0 s) := fun x _ y _ => by simp
    exact hK.absolutelyContinuousOnInterval
  have h_up_ac : AbsolutelyContinuousOnInterval (positiveZUpward x_lasso) 0 s :=
    positiveZUpward_ac x_lasso s hs.le h_regular
  have h_down_ac : AbsolutelyContinuousOnInterval (positiveZDownward x_lasso) 0 s :=
    positiveZDownward_ac x_lasso s hs.le h_regular
  have h1 : AbsolutelyContinuousOnInterval (fun τ : ℝ => τ + positiveZUpward x_lasso τ) 0 s :=
    h_id_ac.add h_up_ac
  have h2 : AbsolutelyContinuousOnInterval
      (fun τ : ℝ => 1 / Real.log (1 / ε) * (τ + positiveZUpward x_lasso τ)) 0 s :=
    h1.const_mul _
  have h3 : AbsolutelyContinuousOnInterval
      (fun τ : ℝ => 1 / Real.log (1 / ε) * (τ + positiveZUpward x_lasso τ) +
        positiveZDownward x_lasso τ) 0 s :=
    h2.add h_down_ac
  have h4 : AbsolutelyContinuousOnInterval
      (fun τ : ℝ => C * (1 / Real.log (1 / ε) * (τ + positiveZUpward x_lasso τ) +
        positiveZDownward x_lasso τ)) 0 s :=
    h3.const_mul C
  have h5 : AbsolutelyContinuousOnInterval (fun τ : ℝ => (C * δ / s) * τ) 0 s :=
    h_id_ac.const_mul _
  exact h4.add h5

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
    (Mdagger : Matrix ι ι ℝ) (w : ℝ → EuclideanSpace ℝ ι)
    (hdual : ParametricLCPDualRegular M Mdagger r lambda w)
    (hdual_selected : ∀ μ, 0 ≤ μ →
      isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ))
    (h_local_affine : ScaledPrimalPathLocallyAffineAtDifferentiable x_lasso)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_lipschitz : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      pathDelta M
        (fun τ => posIntegratedTrajectoryRescaled ε (u ε) τ)
        (scaledPrimalPath x_lasso) s
      ≤ C *
          (deltaFullError ε s
            (positiveZUpward x_lasso s) (positiveZDownward x_lasso s) + δ) := by
  obtain ⟨C, hC_pos, h_bound⟩ := positive_delta_differential_inequality M r lambda β s hs
    u hdata hβ hu x_lasso hx_lasso Mdagger w hdual hdual_selected h_local_affine h_regular
      h_lipschitz
  use C, hC_pos
  intro δ hδ
  have h_delta_pos : 0 < C * δ / s := div_pos (mul_pos hC_pos hδ) hs
  filter_upwards [h_bound (C * δ / s) h_delta_pos, by
    rw [mem_nhdsGT_iff_exists_Ioo_subset]
    exact ⟨1, by norm_num, fun _ hx => hx⟩] with ε h_deriv hε_range
  let F := fun τ => pathDelta M (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ)
    (scaledPrimalPath x_lasso) τ
  let G := fun τ => C * (1 / Real.log (1 / ε) * (τ + positiveZUpward x_lasso τ) +
    positiveZDownward x_lasso τ) + (C * δ / s) * τ
  have h_deriv_bound : ∀ᵐ τ ∂volume, τ ∈ Set.Icc (0 : ℝ) s → deriv F τ ≤ deriv G τ := by
    have h_pos_z_diff := positiveZ_ae_differentiable x_lasso s hs h_local_affine h_regular
    filter_upwards [h_deriv, h_pos_z_diff] with τ hτ hτ_pos_z
    intro hτ_mem
    obtain ⟨hτ_up_diff, hτ_down_diff⟩ := hτ_pos_z hτ_mem
    have hG_deriv : deriv G τ = C * (1 / Real.log (1 / ε) *
      (1 + deriv (positiveZUpward x_lasso) τ) +
      deriv (positiveZDownward x_lasso) τ) + C * δ / s := by
      -- `G` is a linear combination of `τ`, `positiveZUpward x_lasso`, and
      -- `positiveZDownward x_lasso`, each of which is differentiable at `τ`
      -- (`hτ_up_diff`, `hτ_down_diff`); assemble the derivative via `HasDerivAt`
      -- combinators and identify `deriv G τ` with it.
      have h_up_hasDeriv : HasDerivAt (positiveZUpward x_lasso)
          (deriv (positiveZUpward x_lasso) τ) τ := hτ_up_diff.hasDerivAt
      have h_down_hasDeriv : HasDerivAt (positiveZDownward x_lasso)
          (deriv (positiveZDownward x_lasso) τ) τ := hτ_down_diff.hasDerivAt
      have h1 : HasDerivAt (fun t : ℝ => t + positiveZUpward x_lasso t)
          (1 + deriv (positiveZUpward x_lasso) τ) τ :=
        (hasDerivAt_id' τ).add h_up_hasDeriv
      have h2 : HasDerivAt
          (fun t : ℝ => 1 / Real.log (1 / ε) * (t + positiveZUpward x_lasso t) +
            positiveZDownward x_lasso t)
          (1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
            deriv (positiveZDownward x_lasso) τ) τ :=
        (h1.const_mul (1 / Real.log (1 / ε))).add h_down_hasDeriv
      have h3 : HasDerivAt
          (fun t : ℝ => C * (1 / Real.log (1 / ε) * (t + positiveZUpward x_lasso t) +
            positiveZDownward x_lasso t) + (C * δ / s) * t)
          (C * (1 / Real.log (1 / ε) * (1 + deriv (positiveZUpward x_lasso) τ) +
            deriv (positiveZDownward x_lasso) τ) + (C * δ / s) * 1) τ :=
        (h2.const_mul C).add ((hasDerivAt_id' τ).const_mul (C * δ / s))
      have hG_eq : G = fun t : ℝ => C * (1 / Real.log (1 / ε) *
          (t + positiveZUpward x_lasso t) + positiveZDownward x_lasso t) +
          (C * δ / s) * t := rfl
      rw [hG_eq, h3.deriv]
      ring
    rw [hG_deriv]
    exact hτ hτ_mem
  have hF0 : F 0 = 0 := pathDelta_zero M ε (u ε) x_lasso
  have hG0 : G 0 = 0 := by
    dsimp [G]
    have ⟨hz_up, hz_down⟩ := z_upward_downward_zero x_lasso
    rw [hz_up, hz_down]
    ring
  have hF_ac : AbsolutelyContinuousOnInterval F 0 s :=
    pathDelta_ac M ε (u ε) x_lasso s hs.le (hu ε hε_range.1).cont_diff.continuous
      (Real.log_pos (one_lt_one_div hε_range.1 hε_range.2)).ne' h_regular
  have hG_ac : AbsolutelyContinuousOnInterval G 0 s :=
    G_ac C ε s δ hs x_lasso h_regular
  /-
  INFORMAL PROOF (docs/Lasso.md, Section 4.6):
  We apply the integration lemma `bound_of_deriv_bound` for Lebesgue integration.
  The functions F (the path delta) and G (the algebraic upper bound) are
  absolutely continuous (but not differentiable everywhere due to kinks).
  Applying the Lebesgue integration lemma on the differential inequality yields F(s) ≤ G(s).
  -/
  have h_bound_s :=
    bound_of_deriv_bound (le_of_lt hs) h_deriv_bound hF0 hG0 hF_ac hG_ac
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
    (Mdagger : Matrix ι ι ℝ) (w : ℝ → EuclideanSpace ℝ ι)
    (hdual : ParametricLCPDualRegular M Mdagger r lambda w)
    (hdual_selected : ∀ μ, 0 ≤ μ →
      isParametricLCP M r lambda μ (scaledPrimalPath x_lasso μ) (w μ))
    (h_local_affine : ScaledPrimalPathLocallyAffineAtDifferentiable x_lasso)
    (h_regular : LocallyAbsolutelyContinuousOnNonnegativeCompacts (scaledPrimalPath x_lasso))
    (h_lipschitz : LocallyLipschitzOnCompacts (scaledPrimalPath x_lasso)) :
    ∃ C > 0, ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0,
      pathDelta M
        (fun τ => posIntegratedTrajectoryRescaled ε (u ε) τ)
        (scaledPrimalPath x_lasso) s
      ≤ C * (positiveZDownward x_lasso s + δ) := by
  obtain ⟨C, hC_pos, h_full⟩ := positive_path_delta_bound_full M r lambda β s hs
    u hdata hβ hu x_lasso hx_lasso Mdagger w hdual hdual_selected h_local_affine h_regular
      h_lipschitz
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
