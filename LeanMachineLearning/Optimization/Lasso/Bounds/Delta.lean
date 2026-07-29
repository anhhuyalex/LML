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
lemma matVec_hasDerivAt (M : Matrix ι ι ℝ) (g : ℝ → EuclideanSpace ℝ ι) (g' : EuclideanSpace ℝ ι) (τ : ℝ)
    (hg : HasDerivAt g g' τ) : HasDerivAt (fun τ => matVec M (g τ)) (matVec M g') τ := by
  let e : EuclideanSpace ℝ ι ≃L[ℝ] (ι → ℝ) :=
    (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv
  have h1 : HasDerivAt (fun τ => e (g τ)) (e g') τ := e.hasFDerivAt.comp_hasDerivAt τ hg
  dsimp [matVec, euclideanOf]
  have hd_pi : HasDerivAt (fun τ => M.mulVec (e (g τ))) (M.mulVec (e g')) τ := by
    apply hasDerivAt_pi.2
    intro i
    dsimp [Matrix.mulVec, dotProduct]
    have hterm : ∀ j, HasDerivAt (fun τ => M i j * e (g τ) j) (M i j * e g' j) τ := fun j =>
      (hasDerivAt_pi.1 h1 j).const_mul (M i j)
    exact HasDerivAt.fun_sum (fun j _ => hterm j)
  exact e.symm.hasFDerivAt.comp_hasDerivAt τ hd_pi

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
    entropyMirrorGradient (posEffectiveParameter u t) - entropyMirrorGradient (posEffectiveParameter u 0) =
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
    entropyMirrorGradient (x τ) - τ • r + (τ * lambda) • ones + matVec M (z τ) with hF_def
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
    rw [show (r - matVec M (x τ) - lambda • ones) - r + lambda • ones + matVec M (x τ) = 0 by abel] at hsum
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
  have h_z_rescaled : posIntegratedTrajectoryRescaled ε u s = c • (posIntegratedTrajectory u) t_s := by
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
    _ = (-c • (t_s • r)) + (-c • (-((t_s * lambda) • ones))) + (-c • (-matVec M ((posIntegratedTrajectory u) t_s))) := by
      simp [smul_sub, add_assoc]
    _ = (-(c * t_s)) • r + (c * (t_s * lambda)) • ones + c • matVec M ((posIntegratedTrajectory u) t_s) := by
      simp [smul_smul, neg_smul]
    _ = -(c * t_s) • r + (c * t_s * lambda) • ones + c • matVec M ((posIntegratedTrajectory u) t_s) := by ring_nf
    _ = -s • r + (s * lambda) • ones + c • matVec M ((posIntegratedTrajectory u) t_s) := by
      rw [show c * t_s = s by dsimp [c, t_s, posTimeFromRescaled]; field_simp [hlog]]
    _ = -s • r + (s * lambda) • ones + matVec M (c • (posIntegratedTrajectory u) t_s) := by rw [matVec_smul_eq]
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
lemma pos_delta_bound_1
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (hdata : ProblemData M r lambda) (hβ : NonzeroCoordinates β)
    (hu : ∀ ε > 0, posDlnGradientFlow M r lambda ε β (u ε)) :
    ∃ C > 0, ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        inner ℝ (deriv (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) τ)
          (posRescaledMirrorVariable ε (u ε) τ)
        ≤ C / Real.log (1 / ε) := by
  sorry

/--
Section 4.6, Eq. (4.14), Term 2.
Informal proof reference: `docs/Lasso.md`, Section 4.6.
Bounds the cross term $-<x^\varepsilon, w>$ by 0.

**Proof Sketch**:
1. We have $\dot{z}^\varepsilon(s) = x^\varepsilon(s)$. The primal flow $x^\varepsilon(s)$
   is defined as the square of the parameter $u(s)$, so $x^\varepsilon(s) \ge 0$ component-wise.
2. The dual variable $w(s) = M z(s) - s r + s \lambda \mathbf{1}$ represents the dual slack
   of the target positive lasso path. By LCP conditions, $w(s) \ge 0$.
3. The inner product of two nonnegative vectors is nonnegative:
   $\langle x^\varepsilon(s), w(s) \rangle \ge 0$.
4. Taking the negative gives $-\langle \dot{z}^\varepsilon(s), w(s) \rangle \le 0$.
-/
lemma pos_delta_bound_2
    (M : Matrix ι ι ℝ) (r : EuclideanSpace ℝ ι) (lambda : ℝ)
    (β : EuclideanSpace ℝ ι) (s : ℝ) (hs : 0 < s)
    (u : ℝ → ℝ → EuclideanSpace ℝ ι)
    (x_lasso : ℝ → EuclideanSpace ℝ ι)
    (hx_lasso : ∀ μ > 0, IsPositiveLassoMinimizer M r lambda μ (x_lasso μ)) :
    ∀ᶠ ε in 𝓝[>] 0,
      ∀ τ ∈ Set.Icc (0 : ℝ) s,
        - inner ℝ (deriv (fun ρ => posIntegratedTrajectoryRescaled ε (u ε) ρ) τ)
          (matVec M (scaledPrimalPath x_lasso τ) - τ • r + (τ * lambda) • ones)
        ≤ 0 := by
  sorry

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
          (matVec M (scaledPrimalPath x_lasso τ) - τ • r + (τ * lambda) • ones) +
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
  have h2 := pos_delta_bound_2 M r lambda β s hs u x_lasso hx_lasso
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
      (matVec M (scaledPrimalPath x_lasso τ) - τ • r + (τ * lambda) • ones) +
    - inner ℝ (deriv (scaledPrimalPath x_lasso) τ) (posRescaledMirrorVariable ε (u ε) τ) +
    (inner ℝ (deriv (scaledPrimalPath x_lasso) τ)
      (matVec M (scaledPrimalPath x_lasso τ) - τ • r + (τ * lambda) • ones) +
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
  sorry

/--
The bounding function quantities at `τ = 0` are `0`.
Informal proof: `positiveZUpward` and `positiveZDownward` are integrated quantities
starting from `0`, so they evaluate to `0` at `τ = 0`.
-/
lemma z_upward_downward_zero (x_lasso : ℝ → EuclideanSpace ℝ ι) :
    positiveZUpward x_lasso 0 = 0 ∧ positiveZDownward x_lasso 0 = 0 := by
  sorry

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
  sorry

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
  have h_eventually_vanish : ∀ᶠ ε in 𝓝[>] 0,
      deltaVanishingTerm ε s (positiveZUpward x_lasso s) ≤ δ / 2 := by
    sorry -- Follows from 1 / log(1/ε) → 0 as ε → 0
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
