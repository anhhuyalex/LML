/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianSteinRatio
public import LeanMachineLearning.SpinGlasses.Gaussian.GaussianTiltedSteinRatio
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ReplicaSymmetricFreeEnergy
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.OverlapHighMoments
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.EmpiricalVarianceHighMoments
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.Binomial
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.SqSub
public import LeanMachineLearning.ForMathlib.Probability.Moments.IidSumMoments
public import LeanMachineLearning.Optimization.NTK.Foundations.ODE

/-!
# Log-weighted Stein identity and centered-moment ODE along the `s`-interpolation

Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 2.5, proof of Theorem
2.5.3, Eqs. (2.107)--(2.110).

For `N + 1` spins and `M` constraints with load `α = M / (N + 1)`, let
$$A(s, \omega) = \frac{1}{N + 1}\,\log \int_{\Sigma_{N+1} \times \mathbb{R}^M}
  \exp\bigl(E_s(s, \omega, x)\bigr)\,\mathrm{d}\mu_s(x),$$
$$\mathrm{RS}(s) = \mathrm{perceptronRSFunctional}(u, \alpha, r, q) +
  \frac{1 - s}{2}\,r(1 - q), \qquad V(s, \omega) = A(s, \omega) - \mathrm{RS}(s).$$

## Main declarations

* `SpinGlasses.stein_tilted_unit_replica_deriv_mul_comp_log`: model-free single-replica Stein
  identity multiplied by `G(log Z_w(w))` with zero diagonal covariance, derived from
  `stein_tilted_replica_ratio_mul_comp_log`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology

namespace SpinGlasses

/-! ### Section 1: Log-weighted single-replica Stein identity -/

/-- **Log-weighted marked-replica Stein identity for `deriv u` with zero diagonal covariance.**
Let `μ₀` be a probability measure on `α` with measurable projection `π : α → L` onto a finite set
`L`, and let `Z_w w = ∫ q, exp(u(S(w, q))) d(μ₀ × γ_aux)`. Under `SmartPathPotential₂`,
`W_sh τ₁ ⬝ᵥ α_sh τ₂ = (1 / 2) * c τ₁ τ₂`, `W_sh τ ⬝ᵥ α_sh τ + W_aux τ ⬝ᵥ α_aux τ = 0`, and `G`
differentiable with bounded value and derivative on `[-|B|, |B|]`:
`𝔼_w[⟨Wt(y) u'(S(w, y))⟩_{ν_w} * G(log Z_w(w))] =
  (1 / 2) * 𝔼_w[⟨c(π σ_0, π σ_1) u'(S(w, σ_0)) u'(S(w, σ_1))⟩_{ν_w^{⊗2}} *
    (G'(log Z_w(w)) - G(log Z_w(w)))]`. -/
theorem stein_tilted_unit_replica_deriv_mul_comp_log
    {α L K_sh K_aux : Type*} [MeasurableSpace α]
    [Finite L] [MeasurableSpace L] [MeasurableSingletonClass L]
    [Fintype K_sh] [Fintype K_aux]
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (π : α → L) (hπ : Measurable π)
    (α_sh W_sh : L → K_sh → ℝ) (α_aux W_aux : L → K_aux → ℝ)
    {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    (c : L → L → ℝ)
    (hcov_sh : ∀ τ₁ τ₂, W_sh τ₁ ⬝ᵥ α_sh τ₂ = (1 / 2) * c τ₁ τ₂)
    (hcov_diag : ∀ τ, W_sh τ ⬝ᵥ α_sh τ + W_aux τ ⬝ᵥ α_aux τ = 0)
    {G : ℝ → ℝ} (hG : Differentiable ℝ G) {CG CG' : ℝ}
    (hGb : ∀ t ∈ Set.Icc (-|B|) |B|, |G t| ≤ CG)
    (hGd : ∀ t ∈ Set.Icc (-|B|) |B|, |deriv G t| ≤ CG') :
    let γ_sh := Measure.pi fun _ : K_sh => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : K_aux => gaussianReal 0 1
    let S (w : K_sh → ℝ) (y : α × (K_aux → ℝ)) : ℝ :=
      α_sh (π y.1) ⬝ᵥ w + α_aux (π y.1) ⬝ᵥ y.2
    let Wt (w : K_sh → ℝ) (y : α × (K_aux → ℝ)) : ℝ :=
      W_sh (π y.1) ⬝ᵥ w + W_aux (π y.1) ⬝ᵥ y.2
    let Z_w (w : K_sh → ℝ) : ℝ := ∫ y, Real.exp (u (S w y)) ∂(μ₀.prod γ_aux)
    ∫ w, (∫ y : α × (K_aux → ℝ), Wt w y * deriv u (S w y)
        ∂((μ₀.prod γ_aux).tilted (fun y => u (S w y)))) * G (Real.log (Z_w w)) ∂γ_sh =
      (1 / 2) * ∫ w, (∫ σ : Option Unit → α × (K_aux → ℝ),
        c (π (σ (some ())).1) (π (σ none).1) *
          deriv u (S w (σ (some ()))) * deriv u (S w (σ none))
        ∂(Measure.pi fun _ : Option Unit => (μ₀.prod γ_aux).tilted (fun y => u (S w y)))) *
        (deriv G (Real.log (Z_w w)) - G (Real.log (Z_w w))) ∂γ_sh := by
  intro γ_sh γ_aux S Wt Z_w
  have hB_abs : ∀ x, |u x| ≤ |B| := fun x => (hu.abs_le x).trans (le_abs_self B)
  have hψ_deriv := hu.hasDerivAt_deriv_mul_exp
  have hst := stein_tilted_replica_ratio_mul_comp_log (R := Unit) (μ₀ := μ₀)
    (π := π) hπ α_sh W_sh α_aux W_aux
    hu.differentiable hB_abs hu.abs_deriv_le
    (fun _ => deriv u)
    (fun _ x => (hψ_deriv x).differentiableAt)
    (M₀ := fun _ => |D₁|) (M' := fun _ => (|D₂| + |D₁| ^ 2) * Real.exp |B|)
    (fun _ x => hu.abs_deriv_le_abs x)
    (fun _ x => by
      rw [(hψ_deriv x).deriv, abs_mul, abs_of_pos (Real.exp_pos _)]
      refine mul_le_mul ?_ (Real.exp_le_exp.2 (hu.le_abs x)) (Real.exp_pos _).le (by positivity)
      refine (abs_add_le _ _).trans (add_le_add
        ((hu.abs_deriv₂_le x).trans (le_abs_self D₂)) ?_)
      rw [abs_mul, sq]
      exact mul_le_mul (hu.abs_deriv_le_abs x) (hu.abs_deriv_le_abs x)
        (abs_nonneg _) (abs_nonneg _))
    (fun _ x => deriv (deriv u) x + deriv u x * deriv u x)
    (fun _ x => (hψ_deriv x).deriv)
    hG hGb hGd () (f := fun _ => (1 : ℝ)) (integrable_const 1)
  dsimp only at hst
  have hlhs_eq :
      (∫ w, (∫ y : α × (K_aux → ℝ), Wt w y * deriv u (S w y)
          ∂((μ₀.prod γ_aux).tilted (fun y => u (S w y)))) * G (Real.log (Z_w w)) ∂γ_sh) =
      ∫ w, (∫ σ : Unit → α × (K_aux → ℝ),
          1 * Wt w (σ ()) * (∏ r_u : Unit, deriv u (S w (σ r_u)))
          ∂(Measure.pi fun _ : Unit => (μ₀.prod γ_aux).tilted (fun y => u (S w y)))) *
        G (Real.log (Z_w w)) ∂γ_sh := by
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    dsimp only
    congr 1
    let ν_w := (μ₀.prod γ_aux).tilted (fun y => u (S w y))
    have hm_y : Measurable fun y : α × (K_aux → ℝ) => Wt w y * deriv u (S w y) := by
      have hmS : Measurable (S w) := by
        refine ((measurable_of_finite fun m => α_sh m ⬝ᵥ w).comp (hπ.comp measurable_fst)).add ?_
        simp only [dotProduct]
        exact Finset.measurable_sum _ fun k _ =>
          ((measurable_of_finite fun m => α_aux m k).comp (hπ.comp measurable_fst)).mul
            ((measurable_pi_apply k).comp measurable_snd)
      have hmWt : Measurable (Wt w) := by
        refine ((measurable_of_finite fun m => W_sh m ⬝ᵥ w).comp (hπ.comp measurable_fst)).add ?_
        simp only [dotProduct]
        exact Finset.measurable_sum _ fun k _ =>
          ((measurable_of_finite fun m => W_aux m k).comp (hπ.comp measurable_fst)).mul
            ((measurable_pi_apply k).comp measurable_snd)
      exact hmWt.mul ((measurable_deriv u).comp hmS)
    have : SigmaFinite ν_w := by
      have hmS : Measurable (S w) := by
        refine ((measurable_of_finite fun m => α_sh m ⬝ᵥ w).comp (hπ.comp measurable_fst)).add ?_
        simp only [dotProduct]
        exact Finset.measurable_sum _ fun k _ =>
          ((measurable_of_finite fun m => α_aux m k).comp (hπ.comp measurable_fst)).mul
            ((measurable_pi_apply k).comp measurable_snd)
      have : IsProbabilityMeasure ν_w :=
        isProbabilityMeasure_tilted_of_ae_le (hu.measurable.comp hmS).aemeasurable
          (ae_of_all _ fun _ => hu.le_abs _)
      infer_instance
    rw [← (measurePreserving_funUnique ν_w Unit).integral_comp_of_aestronglyMeasurable
      hm_y.aestronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ fun σ => by
      simp [Finset.univ_unique])
  rw [hlhs_eq, hst]
  have hdiag_zero :
      (∑ j : Unit, ∫ w, (∫ σ : Unit → α × (K_aux → ℝ),
        1 * (W_sh (π (σ ()).1) ⬝ᵥ α_sh (π (σ j).1) +
            if () = j then W_aux (π (σ ()).1) ⬝ᵥ α_aux (π (σ j).1) else 0) *
          ((deriv (deriv u) (S w (σ j)) + deriv u (S w (σ j)) * deriv u (S w (σ j))) *
            ∏ r_u ∈ Finset.univ.erase j, deriv u (S w (σ r_u)))
        ∂(Measure.pi fun _ : Unit => (μ₀.prod γ_aux).tilted (fun y => u (S w y)))) *
        G (Real.log (Z_w w)) ∂γ_sh) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have hj : j = () := Subsingleton.elim _ _
    subst hj
    refine (integral_congr_ae (g := fun _ => (0 : ℝ)) (ae_of_all _ fun w => ?_)).trans
      (integral_zero _ ℝ)
    dsimp only
    have hin : (∫ σ : Unit → α × (K_aux → ℝ),
        1 * (W_sh (π (σ ()).1) ⬝ᵥ α_sh (π (σ ()).1) +
            if () = () then W_aux (π (σ ()).1) ⬝ᵥ α_aux (π (σ ()).1) else 0) *
          ((deriv (deriv u) (S w (σ ())) + deriv u (S w (σ ())) * deriv u (S w (σ ()))) *
            ∏ r_u ∈ Finset.univ.erase (), deriv u (S w (σ r_u)))
        ∂(Measure.pi fun _ : Unit => (μ₀.prod γ_aux).tilted (fun y => u (S w y)))) = 0 := by
      refine (integral_congr_ae (g := fun _ => (0 : ℝ)) (ae_of_all _ fun σ => ?_)).trans
        (integral_zero _ ℝ)
      dsimp only
      simp only [↓reduceIte, hcov_diag (π (σ ()).1)]
      ring
    rw [hin, zero_mul]
  rw [hdiag_zero, zero_add]
  simp only [Fintype.card_unique, Nat.cast_one]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  dsimp only
  simp only [one_mul]
  rw [← mul_assoc, ← integral_const_mul]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun σ => ?_)
  dsimp only
  simp only [Finset.univ_unique, Finset.prod_singleton, hcov_sh]
  ring

/-! ### Section 2: Compact-interval bounds for shifted polynomial powers -/

/-- For `A₀, a : ℝ`, `L > 0`, and `m : ℕ`, the shifted power `t ↦ (A₀ + L⁻¹ * t - a) ^ m` is
differentiable with derivative `m * L⁻¹ * (A₀ + L⁻¹ * t - a) ^ (m - 1)` and satisfies uniform bounds
on every symmetric interval `[-B, B]` (`B ≥ 0`). -/
private lemma differentiable_and_abs_le_shift_pow_on_Icc
    (A₀ a L : ℝ) (hL : 0 < L) (m : ℕ) :
    let G (t : ℝ) : ℝ := (A₀ + L⁻¹ * t - a) ^ m
    Differentiable ℝ G ∧
      (∀ t, HasDerivAt G ((m : ℝ) * L⁻¹ * (A₀ + L⁻¹ * t - a) ^ (m - 1)) t) ∧
      (∀ {B : ℝ}, 0 ≤ B → ∀ t ∈ Icc (-B) B, |G t| ≤ (|A₀ - a| + L⁻¹ * B) ^ m) ∧
      (∀ {B : ℝ}, 0 ≤ B → ∀ t ∈ Icc (-B) B,
        |deriv G t| ≤ (m : ℝ) * L⁻¹ * (|A₀ - a| + L⁻¹ * B) ^ (m - 1)) := by
  intro G
  have hhd : ∀ t : ℝ, HasDerivAt G ((m : ℝ) * L⁻¹ * (A₀ + L⁻¹ * t - a) ^ (m - 1)) t := by
    intro t
    have hlin : HasDerivAt (fun x : ℝ => A₀ + L⁻¹ * x - a) L⁻¹ t := by
      simpa using (((hasDerivAt_id t).const_mul L⁻¹).const_add A₀).sub_const a
    exact ((hasDerivAt_pow m (A₀ + L⁻¹ * t - a)).comp t hlin).congr_deriv (by ring)
  have htri : ∀ {B t : ℝ}, t ∈ Icc (-B) B → |A₀ + L⁻¹ * t - a| ≤ |A₀ - a| + L⁻¹ * B := by
    intro B t ht
    have heq : A₀ + L⁻¹ * t - a = (A₀ - a) + L⁻¹ * t := by ring
    rw [heq]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul, abs_of_pos (inv_pos.2 hL)]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ht) (inv_nonneg.2 hL.le)
  refine ⟨fun t => (hhd t).differentiableAt, hhd, ?_, ?_⟩
  · intro B _ t ht
    dsimp only [G]
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (htri ht) m
  · intro B _ t ht
    rw [(hhd t).deriv, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg m),
      abs_of_pos (inv_pos.2 hL), abs_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (htri ht) (m - 1))
      (by positivity)

end SpinGlasses
