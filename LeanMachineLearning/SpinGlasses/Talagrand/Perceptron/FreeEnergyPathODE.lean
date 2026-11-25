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
public import LeanMachineLearning.ForMathlib.Probability.Moments.IidSumExpansion
public import LeanMachineLearning.ForMathlib.Analysis.Calculus.GronwallBackward
public import LeanMachineLearning.ForMathlib.Analysis.Convex.Integral
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IteratedHolder

/-!
# Log-weighted Stein identity and centered-moment ODE along `s`

Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 2.5, proof of Theorem
2.5.3, Eqs. (2.107)--(2.109).

For `N + 1` spins and `M` constraints with load `α = M / (N + 1)`, let
$$A(s, \omega) = \frac{1}{N + 1}\,\log \int_{\Sigma_{N+1} \times \mathbb{R}^M}
  \exp\bigl(E_s(s, \omega, x)\bigr)\,\mathrm{d}\mu_s(x),$$
$$\mathrm{RS}(s) = \mathrm{perceptronRSFunctional}(u, \alpha, r, q) +
  \frac{1 - s}{2}\,r(1 - q), \qquad V(s, \omega) = A(s, \omega) - \mathrm{RS}(s).$$

## Main declarations

* `SpinGlasses.stein_tilted_unit_replica_deriv_mul_comp_log`: model-free single-replica Stein
  identity multiplied by `G(log Z_w(w))` with zero diagonal covariance, derived from
  `stein_tilted_replica_ratio_mul_comp_log`.
* `SpinGlasses.hasDerivAt_interpolating_centered_moment_pow`: Eqs. (2.107)--(2.108), differentiating
  `s' ↦ 𝔼[(A(s', ω) - RS(s'))^k]` on `s ∈ (0, 1)` into `VII + VIII + IX` under free `(q, r)`
  (`q ∈ [0, 1]`, `r ≥ 0`, `SmartPathPotential₂`).
* `SpinGlasses.abs_interpolating_overlap_product_mul_pow_sub_one_le` and
  `SpinGlasses.abs_interpolating_overlap_product_mul_pow_sub_two_le`:
  Eq. (2.109), bounding `|VII|` and `|VIII|` uniformly in `s ∈ [0, 1]` via Hölder and
  Theorems 2.5.1--2.5.2.

The differential inequality Eq. (2.110) and the a priori Grönwall bound
`integral_interpolating_centered_abs_pow_le_uniform_in_moment_order` are in
`FreeEnergyGronwall.lean`.
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

/-! ### Section 3: Centered-moment ODE along the `s`-interpolation (Eqs. (2.107)--(2.108)) -/

private lemma memLp_abs_snd_interpDisorder (N M : ℕ) (i : Fin (N + 1)) (p : ℝ≥0) :
    MemLp (fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) => |ω.2 i|) p
      (((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)) :=
  (memLp_coord_pi_gaussianReal i p).norm.comp_measurePreserving
    (measurePreserving_snd
      (μ := (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin M => gaussianReal 0 1))
      (ν := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))

private lemma memLp_abs_fst_snd_interpDisorder (N M : ℕ) (k : Fin M) (p : ℝ≥0) :
    MemLp (fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) => |ω.1.2 k|) p
      (((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)) :=
  ((memLp_coord_pi_gaussianReal k p).norm.comp_measurePreserving
    (measurePreserving_snd
      (μ := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
      (ν := Measure.pi fun _ : Fin M => gaussianReal 0 1))).comp_measurePreserving
    (measurePreserving_fst
      (μ := (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin M => gaussianReal 0 1))
      (ν := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))

private lemma memLp_abs_fst_fst_interpDisorder (N M : ℕ) (k : Fin M) (i : Fin (N + 1)) (p : ℝ≥0) :
    MemLp (fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) => |ω.1.1 k i|) p
      (((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)) := by
  have hg0 : MemLp (fun g : Fin M → Fin (N + 1) → ℝ => |g k i|) p
      (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) :=
    (memLp_coord_pi_gaussianReal i p).norm.comp_measurePreserving
      (measurePreserving_eval
        (fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) k)
  exact (hg0.comp_measurePreserving
    (measurePreserving_fst
      (μ := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
      (ν := Measure.pi fun _ : Fin M => gaussianReal 0 1))).comp_measurePreserving
    (measurePreserving_fst
      (μ := (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin M => gaussianReal 0 1))
      (ν := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))

private lemma memLp_interp_log_partition_and_deriv
    {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) {B D₁ : ℝ} (hB : ∀ x, |u x| ≤ B)
    (q r a δ : ℝ) {s : ℝ} (hs0 : 0 ≤ s) (p : ℝ≥0) :
    let P := (((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod
      (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    let b_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      |D₁| * (1 / (2 * Real.sqrt δ)) *
        (∑ k : Fin M, ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.1 k i|) +
          Real.sqrt q * |ω.1.2 k|)) +
        (1 / (2 * Real.sqrt δ)) * ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r
    let dom_A (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ((N : ℝ) + 1)⁻¹ *
        (((N : ℝ) + 1) * Real.log 2 + M * B + ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r) + |a|
    MemLp b_ω p P ∧ MemLp dom_A p P ∧
      MemLp (fun ω => ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s ω x) ∂μ_s) - a) p P := by
  intro P μ_s E_s b_ω dom_A
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P]; infer_instance
  have hsum_z' : MemLp (fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) =>
      ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r) p P :=
    memLp_finsetSum Finset.univ fun i _ =>
      (memLp_abs_snd_interpDisorder N M i p).mul_const (Real.sqrt r)
  have hbω_mem : MemLp b_ω p P := by
    have h1 : MemLp (fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) =>
        ∑ k : Fin M, ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.1 k i|) +
          Real.sqrt q * |ω.1.2 k|)) p P :=
      memLp_finsetSum Finset.univ fun k _ =>
        ((memLp_finsetSum Finset.univ fun i _ =>
          memLp_abs_fst_fst_interpDisorder N M k i p).const_mul _).add
        ((memLp_abs_fst_snd_interpDisorder N M k p).const_mul _)
    exact (h1.const_mul _).add (hsum_z'.const_mul _)
  have hdomA_mem : MemLp dom_A p P :=
    (((memLp_const (((N : ℝ) + 1) * Real.log 2 + M * B)).add hsum_z').const_mul _).add
      (memLp_const |a|)
  obtain ⟨hm_log, hbd_log⟩ := measurable_and_abs_log_interpPartition_le (N := N) (M := M)
    hu hB q r hs0
  have hA_mem : MemLp
      (fun ω => ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s ω x) ∂μ_s) - a) p P := by
    refine MemLp.mono' hdomA_mem
      (((hm_log.const_mul _).sub_const a).aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
    rw [abs_mul, abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < (N : ℝ) + 1))]
    exact mul_le_mul_of_nonneg_left (hbd_log ω) (by positivity)
  exact ⟨hbω_mem, hdomA_mem, hA_mem⟩

private lemma integrable_pow_of_memLp
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {Y : Ω → ℝ} (m : ℕ) (hY : MemLp Y ((max m 1 : ℕ) : ℝ≥0) P) :
    Integrable (fun ω => Y ω ^ m) P ∧ Integrable (fun ω => |Y ω| ^ m) P := by
  have hm : MemLp Y (m : ℕ) P :=
    hY.mono_exponent (by exact_mod_cast Nat.le_max_left m 1)
  have hAbs : Integrable (fun ω => |Y ω| ^ m) P := by
    simpa only [Real.norm_eq_abs] using hm.integrable_norm_pow'
  refine ⟨?_, hAbs⟩
  exact hAbs.mono' (hm.aestronglyMeasurable.pow m) (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_pow])

private lemma integrable_mul_pow_of_memLp
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X Y : Ω → ℝ} (hX : MemLp X 2 P) (m : ℕ) (hY : MemLp Y (((2 * m : ℕ) : ℝ≥0)) P) :
    Integrable (fun ω => X ω * Y ω ^ m) P := by
  rcases m with _ | m
  · simpa using hX.integrable one_le_two
  · have hY' : MemLp Y (2 * ((m + 1 : ℕ) : ℝ≥0∞)) P := by simpa using hY
    have hpow := hY'.norm_rpow_div (m + 1 : ℕ)
    rw [ENNReal.mul_div_cancel_right (by simp) (by simp)] at hpow
    simp only [Real.norm_eq_abs, ENNReal.toReal_natCast, Real.rpow_natCast] at hpow
    have hYm : MemLp (fun ω => Y ω ^ (m + 1)) 2 P :=
      hpow.mono' (hY'.aestronglyMeasurable.pow _) (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_pow])
    exact hX.integrable_mul hYm

/-- Raw differentiation of `s' ↦ 𝔼[(A(s') - a)^m]` on `s ∈ (0, 1)` for a fixed center `a`. -/
private theorem hasDerivAt_interpolating_fixed_center_pow_raw
    {N M : ℕ} {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    {B D₁ : ℝ} (hB : ∀ x, |u x| ≤ B) (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (q r a : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (m : ℕ) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let S_fn (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (k : Fin M) : ℝ :=
      Real.sqrt s' * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s') * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k)
    let S'_fn (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (k : Fin M) : ℝ :=
      (1 / (2 * Real.sqrt s')) *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) -
        (1 / (2 * Real.sqrt (1 - s'))) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k)
    let E_s (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (S_fn s' ω x k)) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s') * ω.2 i * Real.sqrt r
    let A (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s s' ω x) ∂μ_s)
    HasDerivAt (fun s' => ∫ ω, (A s' ω - a) ^ m ∂P)
      ((m : ℝ) * ((N : ℝ) + 1)⁻¹ * ∫ ω,
        (∫ x, ((∑ k : Fin M, S'_fn s ω x k * deriv u (S_fn s ω x k)) -
          (1 / (2 * Real.sqrt (1 - s))) *
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
          ∂(μ_s.tilted (E_s s ω))) * (A s ω - a) ^ (m - 1) ∂P) s := by
  intro P_g P_z P_z' P μ_s S_fn S'_fn E_s A
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z']; infer_instance
  rcases m with _ | m
  · simp only [pow_zero, Nat.cast_zero, zero_mul, integral_const, probReal_univ, one_smul]
    exact hasDerivAt_const s 1
  obtain ⟨δ, hδ, hδ_bd⟩ := exists_Ioo_nhds_bound hs
  let U_nbhd : Set ℝ := Ioo (s - δ) (s + δ)
  have hU_nhds : U_nbhd ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
  have hs_mem : s ∈ U_nbhd := ⟨by linarith, by linarith⟩
  obtain ⟨hF'_m, hpt_δ⟩ := hasDerivAt_and_abs_le_log_interpPartition (N := N) (M := M)
    hu hB hD₁ q r hδ
  let γ₁ : Measure ℝ := gaussianReal 0 1
  let b_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    |D₁| * (1 / (2 * Real.sqrt δ)) *
      (∑ k : Fin M, ((Real.sqrt (N + 1 : ℕ))⁻¹ * (∑ i : Fin (N + 1), |ω.1.1 k i|) +
        Real.sqrt q * |ω.1.2 k|)) +
      (1 / (2 * Real.sqrt δ)) * ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r
  let b_ξ (ξ : Fin M → ℝ) : ℝ :=
    |D₁| * (1 / (2 * Real.sqrt δ)) * ∑ k : Fin M, Real.sqrt (1 - q) * |ξ k|
  let B_const : ℝ := Real.exp (2 * M * B) * ∫ ξ, b_ξ ξ ∂(Measure.pi fun _ : Fin M => γ₁)
  have hB_const0 : 0 ≤ B_const :=
    mul_nonneg (Real.exp_pos _).le (integral_nonneg fun _ => by dsimp only [b_ξ]; positivity)
  let dom_A (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    ((N : ℝ) + 1)⁻¹ *
      (((N : ℝ) + 1) * Real.log 2 + M * B + ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r) + |a|
  let dom_prod (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    ((m + 1 : ℕ) : ℝ) * ((N : ℝ) + 1)⁻¹ * ((b_ω ω + B_const) * dom_A ω ^ m)
  obtain ⟨hbω_2, -, -⟩ := memLp_interp_log_partition_and_deriv (N := N) (M := M)
    hu.continuous.measurable hB (D₁ := D₁) q r a δ hs.1.le 2
  obtain ⟨-, hdomA_2m, -⟩ := memLp_interp_log_partition_and_deriv (N := N) (M := M)
    hu.continuous.measurable hB (D₁ := D₁) q r a δ hs.1.le ((2 * m : ℕ) : ℝ≥0)
  have hdom_int : Integrable dom_prod P :=
    (integrable_mul_pow_of_memLp (hbω_2.add (memLp_const B_const)) m hdomA_2m).const_mul _
  have hF_int {s' : ℝ} (hs' : s' ∈ U_nbhd) :
      Integrable (fun ω => (A s' ω - a) ^ (m + 1)) P := by
    have hs'0 : 0 ≤ s' := (hδ.trans_le (hδ_bd s' hs').1).le
    obtain ⟨-, -, hAmem⟩ := memLp_interp_log_partition_and_deriv (N := N) (M := M)
      hu.continuous.measurable hB (D₁ := D₁) q r a δ hs'0 ((max (m + 1) 1 : ℕ) : ℝ≥0)
    exact (integrable_pow_of_memLp (m + 1) hAmem).1
  let F'_fn (t : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    ((m + 1 : ℕ) : ℝ) * ((N : ℝ) + 1)⁻¹ *
      ((∫ x, ((∑ k : Fin M, S'_fn t ω x k * deriv u (S_fn t ω x k)) -
          (1 / (2 * Real.sqrt (1 - t))) *
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        ∂(μ_s.tilted (E_s t ω))) * (A t ω - a) ^ m)
  have hF's_m : Measurable (F'_fn s) := by
    obtain ⟨hm_log, -⟩ := measurable_and_abs_log_interpPartition_le (N := N) (M := M)
      hu.continuous.measurable hB q r hs.1.le
    exact ((hF'_m s).mul (((hm_log.const_mul _).sub_const a).pow_const m)).const_mul _
  have hpt_deriv (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      {t : ℝ} (ht : t ∈ U_nbhd) :
      HasDerivAt (fun τ => (A τ ω - a) ^ (m + 1)) (F'_fn t ω) t ∧
        ‖F'_fn t ω‖ ≤ dom_prod ω := by
    obtain ⟨ht1, ht2⟩ := hδ_bd t ht
    have ht0 : 0 ≤ t := (hδ.trans_le ht1).le
    obtain ⟨hd_log, hbd_deriv⟩ := hpt_δ ω ht1 ht2
    obtain ⟨-, hbd_log⟩ := measurable_and_abs_log_interpPartition_le (N := N) (M := M)
      hu.continuous.measurable hB q r ht0
    have hd_A : HasDerivAt (fun τ => A τ ω - a)
        (((N : ℝ) + 1)⁻¹ * ∫ x, ((∑ k : Fin M, S'_fn t ω x k * deriv u (S_fn t ω x k)) -
          (1 / (2 * Real.sqrt (1 - t))) *
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
          ∂(μ_s.tilted (E_s t ω))) t :=
      (hd_log.const_mul (((N : ℝ) + 1)⁻¹)).sub_const a
    refine ⟨(hd_A.pow (m + 1)).congr_deriv
      (by dsimp only [F'_fn]; simp only [Nat.add_sub_cancel]; ring), ?_⟩
    rw [Real.norm_eq_abs]
    dsimp only [F'_fn, dom_prod]
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (m + 1)),
      abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < (N : ℝ) + 1)), abs_pow]
    refine mul_le_mul_of_nonneg_left (mul_le_mul hbd_deriv ?_ (by positivity)
      (add_nonneg (by dsimp only [b_ω]; positivity) hB_const0)) (by positivity)
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ m
    dsimp only [A, dom_A]
    refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
    rw [abs_mul, abs_of_pos (inv_pos.2 (by positivity : (0 : ℝ) < (N : ℝ) + 1))]
    exact mul_le_mul_of_nonneg_left (hbd_log ω) (by positivity)
  have hmain := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P)
    (F := fun t ω => (A t ω - a) ^ (m + 1)) (F' := F'_fn) (s := U_nbhd) (bound := dom_prod)
    hU_nhds
    (Filter.eventually_of_mem hU_nhds fun _ ht => (hF_int ht).aestronglyMeasurable)
    (hF_int hs_mem) hF's_m.aestronglyMeasurable
    (ae_of_all _ fun ω t ht => (hpt_deriv ω ht).2)
    hdom_int
    (ae_of_all _ fun ω t ht => (hpt_deriv ω ht).1)).2
  refine hmain.congr_deriv ?_
  dsimp only [F'_fn]
  simp only [Nat.add_sub_cancel]
  rw [integral_const_mul]

private lemma differentiable_and_exp_le_shift_pow
    (A₀ a L : ℝ) (hL : 0 < L) (m : ℕ) :
    let G (t : ℝ) : ℝ := (A₀ + L⁻¹ * t - a) ^ m
    Differentiable ℝ G ∧
      (∀ t, HasDerivAt G ((m : ℝ) * L⁻¹ * (A₀ + L⁻¹ * t - a) ^ (m - 1)) t) ∧
      (∀ t, |G t| ≤ (2 ^ m * (|A₀ - a| ^ m + (L⁻¹) ^ m * (Nat.factorial m : ℝ))) *
        Real.exp |t|) ∧
      (∀ t, |deriv G t| ≤ ((m : ℝ) * L⁻¹ *
          (2 ^ (m - 1) * (|A₀ - a| ^ (m - 1) + (L⁻¹) ^ (m - 1) * (Nat.factorial (m - 1) : ℝ)))) *
        Real.exp |t|) := by
  intro G
  have hhd : ∀ t : ℝ, HasDerivAt G ((m : ℝ) * L⁻¹ * (A₀ + L⁻¹ * t - a) ^ (m - 1)) t := by
    intro t
    have hlin : HasDerivAt (fun x : ℝ => A₀ + L⁻¹ * x - a) L⁻¹ t := by
      simpa using (((hasDerivAt_id t).const_mul L⁻¹).const_add A₀).sub_const a
    exact ((hasDerivAt_pow m (A₀ + L⁻¹ * t - a)).comp t hlin).congr_deriv (by ring)
  have hpow_exp : ∀ (p : ℕ) (t : ℝ), |A₀ + L⁻¹ * t - a| ^ p ≤
      (2 ^ p * (|A₀ - a| ^ p + (L⁻¹) ^ p * (Nat.factorial p : ℝ))) * Real.exp |t| := by
    intro p t
    have htri : |A₀ + L⁻¹ * t - a| ≤ |A₀ - a| + L⁻¹ * |t| := by
      rw [show A₀ + L⁻¹ * t - a = (A₀ - a) + L⁻¹ * t by ring]
      exact (abs_add_le _ _).trans (add_le_add le_rfl (by rw [abs_mul, abs_of_pos (inv_pos.2 hL)]))
    have h1 : |A₀ + L⁻¹ * t - a| ^ p ≤ 2 ^ p * (|A₀ - a| ^ p + (L⁻¹) ^ p * |t| ^ p) := by
      calc |A₀ + L⁻¹ * t - a| ^ p
          ≤ (|A₀ - a| + L⁻¹ * |t|) ^ p := pow_le_pow_left₀ (abs_nonneg _) htri p
        _ ≤ 2 ^ (p - 1) * (|A₀ - a| ^ p + (L⁻¹ * |t|) ^ p) :=
            add_pow_le (abs_nonneg _) (by positivity) p
        _ ≤ 2 ^ p * (|A₀ - a| ^ p + (L⁻¹ * |t|) ^ p) :=
            mul_le_mul_of_nonneg_right
              (pow_le_pow_right₀ one_le_two (Nat.sub_le p 1)) (by positivity)
        _ = 2 ^ p * (|A₀ - a| ^ p + (L⁻¹) ^ p * |t| ^ p) := by rw [mul_pow]
    calc |A₀ + L⁻¹ * t - a| ^ p
        ≤ 2 ^ p * (|A₀ - a| ^ p * 1 + (L⁻¹) ^ p * |t| ^ p) := by linarith
      _ ≤ 2 ^ p * (|A₀ - a| ^ p * Real.exp |t| +
            (L⁻¹) ^ p * ((Nat.factorial p : ℝ) * Real.exp |t|)) :=
          mul_le_mul_of_nonneg_left (add_le_add
            (mul_le_mul_of_nonneg_left (Real.one_le_exp (abs_nonneg t)) (by positivity))
            (mul_le_mul_of_nonneg_left (Real.pow_le_factorial_mul_exp (abs_nonneg t) p)
              (by positivity))) (by positivity)
      _ = (2 ^ p * (|A₀ - a| ^ p + (L⁻¹) ^ p * (Nat.factorial p : ℝ))) * Real.exp |t| := by ring
  refine ⟨fun t => (hhd t).differentiableAt, hhd,
    fun t => by dsimp only [G]; rw [abs_pow]; exact hpow_exp m t, fun t => ?_⟩
  rw [(hhd t).deriv, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg m),
    abs_of_pos (inv_pos.2 hL), abs_pow]
  exact (mul_le_mul_of_nonneg_left (hpow_exp (m - 1) t) (by positivity)).trans_eq (by ring)

private lemma interp_external_field_ibp_pow_coord
    {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    (q r s a : ℝ) (m : ℕ)
    (gz : (Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) (i : Fin (N + 1)) :
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let E_s (z' : Fin (N + 1) → ℝ) (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ j, gz.1 k j * ((x.1 j : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * gz.2 k + Real.sqrt (1 - q) * x.2 k))) +
      ∑ j : Fin (N + 1), ((x.1 j : ℤ) : ℝ) * Real.sqrt (1 - s) * z' j * Real.sqrt r
    let A_z' (z' : Fin (N + 1) → ℝ) : ℝ :=
      ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s z' x) ∂μ_s)
    ∫ z', z' i * ((∫ x, ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s z'))) * (A_z' z' - a) ^ m) ∂P_z' =
      (Real.sqrt (1 - s) * Real.sqrt r) *
        ∫ z', ((1 - ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
            (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)
            ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s z'))) * (A_z' z' - a) ^ m +
          (m : ℝ) * ((N : ℝ) + 1)⁻¹ *
            (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
              (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)
              ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s z'))) *
            (A_z' z' - a) ^ (m - 1)) ∂P_z' := by
  intro P_z' μ_s E_s A_z'
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  let c : ℝ := Real.sqrt (1 - s) * Real.sqrt r
  let D_gz (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    ∑ k : Fin M, u (Real.sqrt s *
        ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ j, gz.1 k j * ((x.1 j : ℤ) : ℝ)) +
      Real.sqrt (1 - s) * (Real.sqrt q * gz.2 k + Real.sqrt (1 - q) * x.2 k))
  let X_i (j : Fin (N + 1)) (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    c * ((x.1 j : ℤ) : ℝ)
  have hDm : Measurable D_gz := Finset.measurable_sum _ fun k _ => hu.comp (by fun_prop)
  have hDb (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : |D_gz x| ≤ M * |B| :=
    (Finset.abs_sum_le_card_mul_of_abs_le _ fun _ => (hB _).trans (le_abs_self B)).trans_eq
      (by simp)
  have hXm (j : Fin (N + 1)) : Measurable (X_i j) := by dsimp only [X_i]; fun_prop
  have hXb (j : Fin (N + 1)) (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : |X_i j x| ≤ c := by
    dsimp only [X_i, c]; rw [abs_mul, abs_of_nonneg (by positivity), abs_units_cast_eq_one, mul_one]
  have hE_eq (z' : Fin (N + 1) → ℝ) (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
      E_s z' x = D_gz x + ∑ j : Fin (N + 1), z' j * X_i j x := by
    dsimp only [E_s, D_gz, X_i, c]
    congr 1; exact Finset.sum_congr rfl fun _ _ => by ring
  have hZ_gauss : HasGaussianLaw (fun (z' : Fin (N + 1) → ℝ) (j : Fin (N + 1)) => z' j) P_z' := by
    let cId : Fin (N + 1) → Fin (N + 1) → ℝ := fun j l => if l = j then 1 else 0
    convert hasGaussianLaw_dotProduct_family cId using 1
    ext z' j; simp [cId, dotProduct]
  have hZ_mean (j : Fin (N + 1)) : ∫ z' : Fin (N + 1) → ℝ, z' j ∂P_z' = 0 := by
    refine (integral_congr_ae (ae_of_all _ fun z' => ?_)).trans
      (integral_dotProduct_pi_gaussianReal (Pi.single j (1 : ℝ)))
    simp [dotProduct, Pi.single_apply]
  have hZ_cov (j l : Fin (N + 1)) :
      ∫ z' : Fin (N + 1) → ℝ, z' j * z' l ∂P_z' = if j = l then 1 else 0 := by
    let ej : Fin (N + 1) → ℝ := Pi.single j 1
    let el : Fin (N + 1) → ℝ := Pi.single l 1
    have hpt (z' : Fin (N + 1) → ℝ) : z' j * z' l = (ej ⬝ᵥ z') * (el ⬝ᵥ z') := by
      simp [ej, el, dotProduct, Pi.single_apply]
    simp_rw [hpt]
    rw [integral_dotProduct_mul_dotProduct_pi_gaussianReal]
    simp [ej, el, dotProduct, Pi.single_apply, eq_comm]
  let R_gz (Y : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) → ℝ) (z' : Fin (N + 1) → ℝ) : ℝ :=
    (∫ x, Y x * Real.exp (D_gz x + ∑ k, z' k * X_i k x) ∂μ_s) /
      ∫ x, Real.exp (D_gz x + ∑ k, z' k * X_i k x) ∂μ_s
  let Z_part (z' : Fin (N + 1) → ℝ) : ℝ :=
    ∫ x, Real.exp (D_gz x + ∑ k, z' k * X_i k x) ∂μ_s
  have hR_tilted (Y : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) → ℝ) (z' : Fin (N + 1) → ℝ) :
      R_gz Y z' = ∫ x, Y x ∂(μ_s.tilted (E_s z')) := by
    rw [integral_tilted_eq_div]; simp_rw [hE_eq z']; rfl
  have hZ_part_eq (z' : Fin (N + 1) → ℝ) :
      ((N : ℝ) + 1)⁻¹ * Real.log (Z_part z') = A_z' z' := by
    dsimp only [Z_part, A_z']; simp_rw [hE_eq z']
  obtain ⟨hGd, hGder, hGb, hGdb⟩ :=
    differentiable_and_exp_le_shift_pow 0 a ((N : ℝ) + 1) (by positivity) m
  have hstein := integral_mul_gibbs_ratio_mul_comp_log_eq_sum (μ := μ_s) (P := P_z')
    R_gz (fun _ _ => rfl) Z_part (fun _ => rfl) hZ_gauss hZ_mean i hDm hXm
    (Y := fun x => ((x.1 i : ℤ) : ℝ)) (by fun_prop)
    hDb hXb (fun _ => (abs_units_cast_eq_one _).le)
    hGd (cG := 1) (cG' := 1)
    (fun t => by simpa only [one_mul] using hGb t)
    (fun t => by simpa only [one_mul] using hGdb t)
  simp only [zero_add, hZ_cov i, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, hR_tilted, hZ_part_eq] at hstein
  rw [hstein, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun z' => ?_)
  dsimp only
  have hprob : IsProbabilityMeasure (μ_s.tilted (E_s z')) :=
    isProbabilityMeasure_tilted_interpEnergy (L := N + 1) hu hB_le s q r (gz, z')
  have hsq_x : (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
      ((x.1 i : ℤ) : ℝ) * X_i i x ∂(μ_s.tilted (E_s z'))) = c := by
    have hpt_x (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        ((x.1 i : ℤ) : ℝ) * X_i i x = c := by
      dsimp only [X_i]
      have h1 : ((x.1 i : ℤ) : ℝ) ^ 2 = 1 := units_cast_sq _
      linear_combination c * h1
    simp_rw [hpt_x]; simp
  have hlin_x : (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
      X_i i x ∂(μ_s.tilted (E_s z'))) =
      c * ∫ x, ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s z')) :=
    integral_const_mul c _
  have htwo_rep :
      (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s z'))) ^ 2 =
      ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s z')) := by
    rw [sq]
    exact (integral_pi_fin_two_mul_fun (μ_s.tilted (E_s z'))
      (fun x => ((x.1 i : ℤ) : ℝ)) (fun x => ((x.1 i : ℤ) : ℝ))).symm
  have hdG := (hGder (Real.log (Z_part z'))).deriv
  simp only [zero_add, hZ_part_eq] at hdG
  rw [hdG, hsq_x, hlin_x]
  generalize (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
    ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s z'))) = m_i at htwo_rep ⊢
  rw [← htwo_rep]
  dsimp only [c]; ring

private theorem integral_interpolating_external_field_ibp_pow
    {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    (q : ℝ) {r : ℝ} (hr0 : 0 ≤ r) (a : ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (m : ℕ) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))) +
      ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    let A (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s ω x) ∂μ_s)
    ((N : ℝ) + 1)⁻¹ *
        ∫ ω, (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          (1 / (2 * Real.sqrt (1 - s))) *
            (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
          ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m ∂P =
      (r / 2) * ∫ ω,
        ((1 - ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
            (((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ))
            ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) * (A ω - a) ^ m +
          (m : ℝ) * ((N : ℝ) + 1)⁻¹ *
            (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
              (((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ))
              ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) *
            (A ω - a) ^ (m - 1)) ∂P := by
  intro P_g P_z P_z' P μ_s E_s A
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z']; infer_instance
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  let c : ℝ := Real.sqrt (1 - s) * Real.sqrt r
  have hEm_joint := measurable_interpEnergy_joint (L := N + 1) (M := M) hu s q r
  have hprob_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      IsProbabilityMeasure (μ_s.tilted (E_s ω)) :=
    isProbabilityMeasure_tilted_interpEnergy (L := N + 1) hu hB_le s q r ω
  obtain ⟨hm_log, -⟩ := measurable_and_abs_log_interpPartition_le (N := N) (M := M) hu hB q r hs0
  have hAm : Measurable A := hm_log.const_mul _
  have hA_mem (p : ℕ) : MemLp (fun ω => A ω - a) ((p : ℕ) : ℝ≥0) P :=
    (memLp_interp_log_partition_and_deriv (N := N) (M := M) hu hB (D₁ := 0)
      q r a 1 hs0 ((p : ℕ) : ℝ≥0)).2.2
  let L_i (i : Fin (N + 1))
      (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    ω.2 i * ((∫ x, ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m)
  have hLi_int (i : Fin (N + 1)) : Integrable (L_i i) P := by
    have hspin_p : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => ((p.2.1 i : ℤ) : ℝ) :=
      measurable_units_cast.comp ((measurable_pi_apply i).comp
        (measurable_fst.comp measurable_snd))
    have hLm : Measurable (L_i i) :=
      ((measurable_pi_apply i).comp measurable_snd).mul
        ((measurable_integral_tilted_dep hEm_joint hspin_p).mul ((hAm.sub_const a).pow_const m))
    have hdom_i : Integrable
        (fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) =>
          |ω.2 i| * (A ω - a) ^ m) P :=
      integrable_mul_pow_of_memLp (memLp_abs_snd_interpDisorder N M i 2) m (hA_mem (2 * m))
    have hdom_abs : Integrable
        (fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) =>
          |ω.2 i| * |A ω - a| ^ m) P :=
      hdom_i.abs.congr (ae_of_all _ fun _ => by simp only [abs_mul, abs_abs, abs_pow])
    refine hdom_abs.mono' hLm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    have := hprob_ω ω
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    calc |ω.2 i| * (|∫ x, ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s ω))| * |A ω - a| ^ m)
        ≤ |ω.2 i| * (1 * |A ω - a| ^ m) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (abs_integral_le_of_forall_abs_le _ fun _ => (abs_units_cast_eq_one _).le)
            (by positivity)) (abs_nonneg _)
      _ = |ω.2 i| * |A ω - a| ^ m := by ring
  let Q_i (i : Fin (N + 1))
      (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
      (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)
      ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))
  have hQi_m (i : Fin (N + 1)) : Measurable (Q_i i) := by
    let G_i (_ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)
    have hGm : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => G_i p.1 p.2 := by
      have h0 : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
          (((σ 0).1 i : ℤ) : ℝ) :=
        measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp (measurable_pi_apply 0)))
      have h1 : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
          (((σ 1).1 i : ℤ) : ℝ) :=
        measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp (measurable_pi_apply 1)))
      exact (h0.mul h1).comp measurable_snd
    exact measurable_integral_pi_tilted (μ := μ_s) hEm_joint hGm
  have hQi_bd (i : Fin (N + 1))
      (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      |Q_i i ω| ≤ 1 := by
    have := hprob_ω ω
    exact abs_integral_le_of_forall_abs_le _ fun _ => by
      rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one]
  let R_i (i : Fin (N + 1))
      (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    (1 - Q_i i ω) * (A ω - a) ^ m +
      (m : ℝ) * ((N : ℝ) + 1)⁻¹ * Q_i i ω * (A ω - a) ^ (m - 1)
  have hRi_int (i : Fin (N + 1)) : Integrable (R_i i) P := by
    have h1 : Integrable (fun ω => (1 - Q_i i ω) * (A ω - a) ^ m) P := by
      have hmem : MemLp (fun ω => 1 - Q_i i ω) 2 P :=
        MemLp.of_bound (measurable_const.sub (hQi_m i)).aestronglyMeasurable 2
          (ae_of_all _ fun ω => by
            rw [Real.norm_eq_abs]
            exact (abs_sub _ _).trans (by rw [abs_one]; linarith [hQi_bd i ω]))
      exact integrable_mul_pow_of_memLp hmem m (hA_mem (2 * m))
    have h2 : Integrable
        (fun ω => ((m : ℝ) * ((N : ℝ) + 1)⁻¹ * Q_i i ω) * (A ω - a) ^ (m - 1)) P := by
      have hmem : MemLp (fun ω => (m : ℝ) * ((N : ℝ) + 1)⁻¹ * Q_i i ω) 2 P :=
        (MemLp.of_bound (hQi_m i).aestronglyMeasurable 1
          (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hQi_bd i ω)).const_mul _
      exact integrable_mul_pow_of_memLp hmem (m - 1) (hA_mem (2 * (m - 1)))
    exact h1.add h2
  have hibp_full (i : Fin (N + 1)) :
      ∫ ω, L_i i ω ∂P = c * ∫ ω, R_i i ω ∂P := by
    dsimp only [P]
    rw [integral_prod _ (hLi_int i)]
    have heq_fub : ∀ᵐ gz ∂(P_g.prod P_z),
        ∫ z', L_i i (gz, z') ∂P_z' = c * ∫ z', R_i i (gz, z') ∂P_z' :=
      ae_of_all _ fun gz => interp_external_field_ibp_pow_coord hu hB q r s a m gz i
    rw [integral_congr_ae heq_fub, integral_const_mul, ← integral_prod (R_i i) (hRi_int i)]
  have hlhs_rw :
      (∫ ω, (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (1 / (2 * Real.sqrt (1 - s))) *
          (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m ∂P) =
      (Real.sqrt r / (2 * Real.sqrt (1 - s))) * ∑ i : Fin (N + 1), ∫ ω, L_i i ω ∂P := by
    have hpt_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
        (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          (1 / (2 * Real.sqrt (1 - s))) *
            (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
          ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m =
        (Real.sqrt r / (2 * Real.sqrt (1 - s))) * ∑ i : Fin (N + 1), L_i i ω := by
      have := hprob_ω ω
      rw [integral_const_mul]
      have h_in (i : Fin (N + 1)) :
          Integrable (fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
            ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r) (μ_s.tilted (E_s ω)) :=
        Integrable.of_bound (by fun_prop) (|ω.2 i| * Real.sqrt r) (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul,
            abs_of_nonneg (Real.sqrt_nonneg _)])
      rw [integral_finsetSum _ fun i _ => h_in i]
      have h_term (i : Fin (N + 1)) :
          (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
            ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r ∂(μ_s.tilted (E_s ω))) =
          Real.sqrt r * (ω.2 i * ∫ x, ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s ω))) := by
        have hpt_x (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
            ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r =
            (Real.sqrt r * ω.2 i) * ((x.1 i : ℤ) : ℝ) := by ring
        simp_rw [hpt_x]
        rw [integral_const_mul]; ring
      simp_rw [h_term, ← Finset.mul_sum]
      dsimp only [L_i]
      have hsum_eq : (∑ i : Fin (N + 1),
          ω.2 i * ((∫ x, ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m)) =
        (∑ i : Fin (N + 1),
          ω.2 i * ∫ x, ((x.1 i : ℤ) : ℝ) ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [hsum_eq]; ring
    simp_rw [hpt_ω]
    rw [integral_const_mul, integral_finsetSum _ fun i _ => hLi_int i]
  have hrhs_rw :
      ((N : ℝ) + 1)⁻¹ * (∑ i : Fin (N + 1), ∫ ω, R_i i ω ∂P) =
      ∫ ω,
        ((1 - ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
            (((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ))
            ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) * (A ω - a) ^ m +
          (m : ℝ) * ((N : ℝ) + 1)⁻¹ *
            (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
              (((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ))
              ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) *
            (A ω - a) ^ (m - 1)) ∂P := by
    rw [← integral_finsetSum _ fun i _ => hRi_int i, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    dsimp only [R_i]
    have hR_sum :
        (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          (((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ))
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) =
        ((N : ℝ) + 1)⁻¹ * ∑ i : Fin (N + 1), Q_i i ω := by
      have := hprob_ω ω
      have hin_i (i : Fin (N + 1)) :
          Integrable (fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
            (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ))
            (Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) := by
        have hm : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
            (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ) :=
          (measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp (measurable_pi_apply 0)))).mul
          (measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp (measurable_pi_apply 1))))
        exact Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun _ => by
          rw [Real.norm_eq_abs, abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one])
      rw [integral_const_mul, integral_finsetSum Finset.univ fun i _ => hin_i i]
    rw [hR_sum]
    have hL : ((N : ℝ) + 1) ≠ 0 := by positivity
    have hsum_sub : (∑ i : Fin (N + 1),
        ((1 - Q_i i ω) * (A ω - a) ^ m +
          (m : ℝ) * ((N : ℝ) + 1)⁻¹ * Q_i i ω * (A ω - a) ^ (m - 1))) =
      (((N : ℝ) + 1) - ∑ i : Fin (N + 1), Q_i i ω) * (A ω - a) ^ m +
        (m : ℝ) * ((N : ℝ) + 1)⁻¹ * (∑ i : Fin (N + 1), Q_i i ω) * (A ω - a) ^ (m - 1) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have h2 : (∑ i : Fin (N + 1), (m : ℝ) * ((N : ℝ) + 1)⁻¹ * Q_i i ω * (A ω - a) ^ (m - 1)) =
          (m : ℝ) * ((N : ℝ) + 1)⁻¹ * (∑ i : Fin (N + 1), Q_i i ω) * (A ω - a) ^ (m - 1) := by
        rw [Finset.mul_sum, Finset.sum_mul]
      rw [h2]; push_cast; ring
    rw [hsum_sub]
    generalize (∑ i : Fin (N + 1), Q_i i ω) = SQ
    field_simp
  rw [hlhs_rw]
  simp_rw [hibp_full, ← Finset.mul_sum]
  have h1s_ne : Real.sqrt (1 - s) ≠ 0 := (Real.sqrt_pos.2 (sub_pos.2 hs1)).ne'
  have hsr : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr0
  have hL : ((N : ℝ) + 1) ≠ 0 := by positivity
  rw [← hrhs_rw]
  dsimp only [c]
  generalize (∑ x : Fin (N + 1), ∫ ω, R_i x ω ∂P) = SR
  field_simp
  linear_combination SR * hsr

private lemma memLp_two_interp_field_deriv_gibbs
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    (q r s : ℝ) (k : Fin M) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let S_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (k' : Fin M) : ℝ :=
      Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k' i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k' + Real.sqrt (1 - q) * x.2 k')
    let S'_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (k' : Fin M) : ℝ :=
      (1 / (2 * Real.sqrt s)) *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k' i * ((x.1 i : ℤ) : ℝ)) -
        (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * ω.1.2 k' + Real.sqrt (1 - q) * x.2 k')
    let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k' : Fin M, u (S_fn ω x k')) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    MemLp (fun ω => ∫ x, S'_fn ω x k * deriv u (S_fn ω x k) ∂(μ_s.tilted (E_s ω))) 2 P := by
  intro P_g P_z P_z' P μ_s S_fn S'_fn E_s
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z']; infer_instance
  have hEm_joint := measurable_interpEnergy_joint (L := N + 1) (M := M) hu.measurable s q r
  let c1 : ℝ := |D₁| * ((1 / (2 * Real.sqrt (1 - s))) * Real.sqrt (1 - q))
  let dom_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    |D₁| * ((1 / (2 * Real.sqrt s)) *
        ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), |ω.1.1 k i|) +
      (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * |ω.1.2 k|)) +
    Real.exp (2 * M * |B|) *
      (c1 * ∫ ξ : Fin M → ℝ, |ξ k| ∂(Measure.pi fun _ => gaussianReal 0 1))
  have hdom_L2 : MemLp dom_ω 2 P := by
    refine MemLp.add (MemLp.const_mul ?_ |D₁|) (memLp_const _)
    exact ((memLp_finsetSum Finset.univ fun i _ =>
      memLp_abs_fst_fst_interpDisorder N M k i 2).const_mul _
      |>.const_mul _).add
      (((memLp_abs_fst_snd_interpDisorder N M k 2).const_mul _).const_mul _)
  have hm_k : Measurable fun ω =>
      ∫ x, S'_fn ω x k * deriv u (S_fn ω x k) ∂(μ_s.tilted (E_s ω)) :=
    measurable_integral_tilted_dep hEm_joint
      ((measurable_interpFieldDeriv_joint (L := N + 1) (M := M) s q k).mul
        ((measurable_deriv u).comp
          (measurable_interpField_joint (L := N + 1) (M := M) s q k)))
  refine hdom_L2.mono' hm_k.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  have hprob_ω : IsProbabilityMeasure (μ_s.tilted (E_s ω)) :=
    isProbabilityMeasure_tilted_interpEnergy (L := N + 1) hu.measurable (fun x => hu.le x) s q r ω
  rw [Real.norm_eq_abs]
  let c0_ω : ℝ := |D₁| * ((1 / (2 * Real.sqrt s)) *
      ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), |ω.1.1 k i|) +
    (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * |ω.1.2 k|))
  have hpt_x (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
      |S'_fn ω x k * deriv u (S_fn ω x k)| ≤ c0_ω + c1 * |x.2 k| := by
    rw [abs_mul, mul_comm _ |deriv u _|]
    have hd_b : |deriv u (S_fn ω x k)| ≤ |D₁| := hu.abs_deriv_le_abs _
    have hS'_b : |S'_fn ω x k| ≤
        (1 / (2 * Real.sqrt s)) *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), |ω.1.1 k i|) +
        (1 / (2 * Real.sqrt (1 - s))) *
          (Real.sqrt q * |ω.1.2 k| + Real.sqrt (1 - q) * |x.2 k|) := by
      dsimp only [S'_fn]
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul (1 / (2 * Real.sqrt s)), abs_of_nonneg (by positivity),
          abs_mul ((Real.sqrt (N + 1 : ℕ))⁻¹), abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
            rw [abs_mul, abs_units_cast_eq_one, mul_one])) (by positivity)) (by positivity)
      · rw [abs_mul (1 / (2 * Real.sqrt (1 - s))), abs_of_nonneg (by positivity)]
        refine mul_le_mul_of_nonneg_left
          ((abs_add_le _ _).trans (add_le_add ?_ ?_)) (by positivity)
        · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc |deriv u (S_fn ω x k)| * |S'_fn ω x k|
        ≤ |D₁| * ((1 / (2 * Real.sqrt s)) *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), |ω.1.1 k i|) +
          (1 / (2 * Real.sqrt (1 - s))) *
            (Real.sqrt q * |ω.1.2 k| + Real.sqrt (1 - q) * |x.2 k|)) :=
          mul_le_mul hd_b hS'_b (abs_nonneg _) (abs_nonneg D₁)
      _ = c0_ω + c1 * |x.2 k| := by dsimp only [c0_ω, c1]; ring
  have hξ_k : Integrable (fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => |x.2 k|) μ_s :=
    (integrable_comp_eval (μ := fun _ : Fin M => gaussianReal 0 1) (i := k)
      IsGaussian.integrable_id.abs).comp_snd _
  have hξ_t : Integrable (fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => |x.2 k|)
      (μ_s.tilted (E_s ω)) :=
    integrable_tilted_of_ae_le
      (Measurable.of_uncurry_left hEm_joint).aemeasurable
      (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r ω)) hξ_k
  have hS'_in_pt : Integrable (fun x => S'_fn ω x k * deriv u (S_fn ω x k))
      (μ_s.tilted (E_s ω)) := by
    have hm : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
        S'_fn ω x k * deriv u (S_fn ω x k) := by
      have h1 : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => S'_fn ω x k := by
        dsimp only [S'_fn]; fun_prop
      have h2 : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => S_fn ω x k := by
        dsimp only [S_fn]; fun_prop
      exact h1.mul ((measurable_deriv u).comp h2)
    exact integrable_tilted_of_abs_le_envelope
      (Measurable.of_uncurry_left hEm_joint).aemeasurable hm.aestronglyMeasurable
      ((integrable_const c0_ω).add (hξ_k.const_mul c1))
      (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r ω))
      (ae_of_all _ hpt_x)
  have h1 := (abs_integral_le_integral_abs).trans
    (integral_mono hS'_in_pt.abs
      (f := fun x => |S'_fn ω x k * deriv u (S_fn ω x k)|)
      (g := fun x => c0_ω + c1 * |x.2 k|)
      ((integrable_const c0_ω).add (hξ_t.const_mul c1)) hpt_x)
  rw [integral_add (integrable_const c0_ω) (hξ_t.const_mul c1), integral_const, probReal_univ,
    one_smul, integral_const_mul] at h1
  refine h1.trans (add_le_add le_rfl ?_)
  let E0_sp (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
  have hE0_m : Measurable E0_sp := by dsimp only [E0_sp]; fun_prop
  have hE0_b (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
      E0_sp x ≤ ∑ i : Fin (N + 1), |Real.sqrt (1 - s) * ω.2 i * Real.sqrt r| :=
    Finset.sum_le_sum fun i _ => (le_abs_self _).trans (by
      rw [abs_mul, abs_mul, abs_mul, abs_units_cast_eq_one, one_mul, abs_mul, abs_mul])
  have hi0 : Integrable (fun x => Real.exp (E0_sp x)) μ_s :=
    integrable_exp_of_ae_le hE0_m.aemeasurable (ae_of_all _ hE0_b)
  have : IsProbabilityMeasure (μ_s.tilted E0_sp) := isProbabilityMeasure_tilted hi0
  have hd_e := integral_pi_tilted_le_exp_mul_of_abs_sub_le (ι := Unit) (μ := μ_s)
    (E₀ := E0_sp) (E₁ := E_s ω) hi0
    ((Measurable.of_uncurry_left hEm_joint).sub hE0_m) (C := M * |B|)
    (fun x => by
      have heq_s : E_s ω x - E0_sp x = ∑ k', u (S_fn ω x k') := by
        dsimp only [E_s, E0_sp]; ring
      rw [heq_s]
      exact (Finset.abs_sum_le_card_mul_of_abs_le _ fun _ =>
        (hu.abs_le _).trans (le_abs_self B)).trans_eq (by simp))
    (Y := fun f_u : Unit → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => |(f_u ()).2 k|)
    (fun _ => abs_nonneg _)
    (integrable_comp_eval (μ := fun _ : Unit => μ_s.tilted E0_sp) (i := ())
      (integrable_tilted_of_ae_le hE0_m.aemeasurable (ae_of_all _ hE0_b) hξ_k))
  simp only [Fintype.card_unique, Nat.cast_one, mul_one] at hd_e
  have hu1 : (∫ σ : Unit → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), |(σ ()).2 k|
      ∂(Measure.pi fun _ : Unit => μ_s.tilted (E_s ω))) =
      ∫ y, |y.2 k| ∂(μ_s.tilted (E_s ω)) :=
    (measurePreserving_funUnique (μ_s.tilted (E_s ω))
      Unit).integral_comp_of_aestronglyMeasurable
      (g := fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => |x.2 k|)
      ((measurable_pi_apply k).comp measurable_snd).norm.aestronglyMeasurable
  have hu2 : (∫ σ : Unit → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), |(σ ()).2 k|
      ∂(Measure.pi fun _ : Unit => μ_s.tilted E0_sp)) =
      ∫ y, |y.2 k| ∂(μ_s.tilted E0_sp) :=
    (measurePreserving_funUnique (μ_s.tilted E0_sp)
      Unit).integral_comp_of_aestronglyMeasurable
      (g := fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => |x.2 k|)
      ((measurable_pi_apply k).comp measurable_snd).norm.aestronglyMeasurable
  rw [hu1, hu2] at hd_e
  have hE0_ind : ∫ x, |x.2 k| ∂(μ_s.tilted E0_sp) =
      ∫ ξ : Fin M → ℝ, |ξ k| ∂(Measure.pi fun _ => gaussianReal 0 1) := by
    rw [integral_tilted_eq_div]
    have hnum : (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        |x.2 k| * Real.exp (E0_sp x) ∂μ_s) =
        (∫ τ : Fin (N + 1) → ℤˣ,
          Real.exp (∑ i, ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r)
          ∂Measure.count) *
          ∫ ξ : Fin M → ℝ, |ξ k| ∂(Measure.pi fun _ => gaussianReal 0 1) := by
      dsimp only [μ_s, E0_sp]
      have hp := integral_prod_mul (μ := (Measure.count : Measure (Fin (N + 1) → ℤˣ)))
        (ν := Measure.pi fun _ : Fin M => gaussianReal 0 1)
        (fun τ => Real.exp (∑ i, ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r))
        (fun ξ => |ξ k|)
      exact (integral_congr_ae (ae_of_all _ fun _ => mul_comm _ _)).trans hp
    have hden : (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), Real.exp (E0_sp x) ∂μ_s) =
        ∫ τ : Fin (N + 1) → ℤˣ,
          Real.exp (∑ i, ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r)
          ∂Measure.count := by
      dsimp only [μ_s, E0_sp]
      have hp := integral_prod_mul (μ := (Measure.count : Measure (Fin (N + 1) → ℤˣ)))
        (ν := Measure.pi fun _ : Fin M => gaussianReal 0 1)
        (fun τ => Real.exp (∑ i, ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r))
        (fun _ => (1 : ℝ))
      simpa using hp
    have hden_pos : 0 < ∫ x, Real.exp (E0_sp x) ∂μ_s := integral_exp_pos hi0
    rw [hden] at hden_pos
    rw [hnum, hden, mul_div_cancel_left₀ _ hden_pos.ne']
  rw [hE0_ind, ← mul_assoc] at hd_e
  have hc1_0 : 0 ≤ c1 := by dsimp only [c1]; positivity
  calc c1 * ∫ x, |x.2 k| ∂(μ_s.tilted (E_s ω))
      ≤ c1 * (Real.exp (2 * M * |B|) *
          ∫ ξ : Fin M → ℝ, |ξ k| ∂(Measure.pi fun _ => gaussianReal 0 1)) :=
        mul_le_mul_of_nonneg_left hd_e hc1_0
    _ = Real.exp (2 * M * |B|) *
          (c1 * ∫ ξ : Fin M → ℝ, |ξ k| ∂(Measure.pi fun _ => gaussianReal 0 1)) := by ring

private lemma log_interpPartition_last_split_eq
    {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, u x ≤ B)
    (s q r : ℝ)
    (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1)
    let μ₀_base := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let γ_aux := Measure.pi fun _ : Unit => gaussianReal 0 1
    let ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) :=
      ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2)
    let w : (Fin (N + 1) ⊕ Unit) → ℝ :=
      Sum.elim (ω.1.1 (Fin.last M)) (fun _ => ω.1.2 (Fin.last M))
    let E₀ (x₀ : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k' : Fin M, u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω₀.1.1 k' i * ((x₀.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω₀.1.2 k' + Real.sqrt (1 - q) * x₀.2 k'))) +
      ∑ i : Fin (N + 1), ((x₀.1 i : ℤ) * Real.sqrt (1 - s) * ω₀.2 i * Real.sqrt r)
    let E_s (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      (∑ k' : Fin (M + 1), u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k' i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k' + Real.sqrt (1 - q) * x.2 k'))) +
      ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    let α_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
      Sum.elim (fun i => Real.sqrt s * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
        (fun _ => Real.sqrt (1 - s) * Real.sqrt q)
    let α_aux (_ : Fin (N + 1) → ℤˣ) : Unit → ℝ := fun _ => Real.sqrt (1 - s) * Real.sqrt (1 - q)
    Real.log (∫ x, Real.exp (E_s x) ∂μ_s) =
      Real.log (∫ x₀, Real.exp (E₀ x₀) ∂μ₀_base) +
        Real.log (∫ y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
          Real.exp (u (α_sh y.1.1 ⬝ᵥ w + α_aux y.1.1 ⬝ᵥ y.2))
            ∂((μ₀_base.tilted E₀).prod γ_aux)) := by
  intro μ_s μ₀_base γ_aux ω₀ w E₀ E_s α_sh α_aux
  let e_u : ℝ ≃ᵐ (Unit → ℝ) := (MeasurableEquiv.funUnique Unit ℝ).symm
  have hmp_u : MeasurePreserving ⇑e_u (gaussianReal 0 1) γ_aux :=
    (measurePreserving_funUnique (gaussianReal 0 1) Unit).symm
  let e_st : ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) ≃ᵐ
      ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) :=
    (interpStateLastSplit (N + 1) M).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) e_u)
  have hmp_st : MeasurePreserving ⇑e_st μ_s (μ₀_base.prod γ_aux) :=
    ((MeasurePreserving.id μ₀_base).prod hmp_u).comp
      (measurePreserving_interpStateLastSplit (N + 1) M)
  have he_st_apply (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      e_st x = ((x.1, Fin.init x.2), fun _ => x.2 (Fin.last M)) := by
    change (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) e_u
      (interpStateLastSplit (N + 1) M x)) = _
    rw [interpStateLastSplit_apply]; rfl
  let V_y (y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) : ℝ :=
    u (α_sh y.1.1 ⬝ᵥ w + α_aux y.1.1 ⬝ᵥ y.2)
  have hVy_m : Measurable V_y := by
    have ha1 : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
        α_sh y.1.1 ⬝ᵥ w :=
      Finset.measurable_sum _ fun idx _ =>
        ((measurable_of_finite fun τ => α_sh τ idx).comp
          (measurable_fst.comp measurable_fst)).mul_const _
    have ha2 : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
        α_aux y.1.1 ⬝ᵥ y.2 := by
      simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
      exact measurable_const.mul ((measurable_pi_apply ()).comp measurable_snd)
    exact hu.comp (ha1.add ha2)
  have hE₀_m := measurable_interpEnergy_slice (L := N + 1) (M := M) hu s q r ω₀
  have hE₀_int : Integrable (fun x₀ => Real.exp (E₀ x₀)) μ₀_base :=
    integrable_exp_of_ae_le hE₀_m.aemeasurable (ae_of_all _ (interpEnergy_le hB s q r ω₀))
  have hZ₀_pos : 0 < ∫ x₀, Real.exp (E₀ x₀) ∂μ₀_base := integral_exp_pos hE₀_int
  have hμ₀_prob : IsProbabilityMeasure (μ₀_base.tilted E₀) := isProbabilityMeasure_tilted hE₀_int
  have hZw_pos : 0 < ∫ y, Real.exp (V_y y) ∂((μ₀_base.tilted E₀).prod γ_aux) :=
    integral_exp_pos_of_ae_le hVy_m.aemeasurable (ae_of_all _ fun _ => hB _)
  have hE_split (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      E_s x = E₀ (e_st x).1 + V_y (e_st x) := by
    rw [he_st_apply]
    dsimp only [E_s, E₀, ω₀, V_y, α_sh, α_aux, w]
    rw [Fin.sum_univ_castSucc, sumElim_dotProduct_sumElim]
    simp only [Fin.init_def, dotProduct, Finset.univ_unique, Finset.sum_singleton, Finset.mul_sum]
    have h1 : (∑ i : Fin (N + 1),
        Real.sqrt s * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((x.1 i : ℤ) : ℝ) *
          ω.1.1 (Fin.last M) i) =
      ∑ i : Fin (N + 1),
        Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
          (ω.1.1 (Fin.last M) i * ((x.1 i : ℤ) : ℝ))) :=
      Finset.sum_congr rfl fun _ _ => by ring
    rw [h1]
    have hlast : (∑ i : Fin (N + 1),
          Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
            (ω.1.1 (Fin.last M) i * ((x.1 i : ℤ) : ℝ)))) +
        Real.sqrt (1 - s) *
          (Real.sqrt q * ω.1.2 (Fin.last M) + Real.sqrt (1 - q) * x.2 (Fin.last M)) =
      (∑ i : Fin (N + 1),
          Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
            (ω.1.1 (Fin.last M) i * ((x.1 i : ℤ) : ℝ))) +
        Real.sqrt (1 - s) * Real.sqrt q * ω.1.2 (Fin.last M)) +
        Real.sqrt (1 - s) * Real.sqrt (1 - q) * x.2 (Fin.last M) := by
      ring
    rw [hlast]; ring
  have hZ_prod : ∫ x, Real.exp (E_s x) ∂μ_s =
      (∫ x₀, Real.exp (E₀ x₀) ∂μ₀_base) *
        ∫ y, Real.exp (V_y y) ∂((μ₀_base.tilted E₀).prod γ_aux) := by
    have h_sum_m : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
        Real.exp (E₀ y.1 + V_y y) :=
      Real.measurable_exp.comp ((hE₀_m.comp measurable_fst).add hVy_m)
    have h1 : ∫ x, Real.exp (E_s x) ∂μ_s =
        ∫ y, Real.exp (E₀ y.1 + V_y y) ∂(μ₀_base.prod γ_aux) := by
      simp_rw [hE_split]
      exact hmp_st.integral_comp_of_aestronglyMeasurable h_sum_m.aestronglyMeasurable
    rw [h1]
    have hprod_i : Integrable (fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
        Real.exp (V_y y) * Real.exp (E₀ y.1)) (μ₀_base.prod γ_aux) := by
      refine (hE₀_int.comp_fst γ_aux |>.const_mul (Real.exp B)).mono'
        (Real.measurable_exp.comp hVy_m |>.mul
          (Real.measurable_exp.comp (hE₀_m.comp measurable_fst))).aestronglyMeasurable
        (ae_of_all _ fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (hB _)) (Real.exp_pos _).le
    have h_fub1 : ∫ y, Real.exp (E₀ y.1 + V_y y) ∂(μ₀_base.prod γ_aux) =
        ∫ x₀, (∫ η, Real.exp (V_y (x₀, η)) ∂γ_aux) * Real.exp (E₀ x₀) ∂μ₀_base := by
      have heq_y : (fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
          Real.exp (E₀ y.1 + V_y y)) =
          fun y => Real.exp (V_y y) * Real.exp (E₀ y.1) :=
        funext fun _ => by rw [add_comm, Real.exp_add]
      rw [heq_y, integral_prod _ hprod_i]
      exact integral_congr_ae (ae_of_all _ fun x₀ => by
        dsimp only
        exact integral_mul_const (Real.exp (E₀ x₀)) (fun η => Real.exp (V_y (x₀, η))))
    have hVy_int_t : Integrable (fun y => Real.exp (V_y y)) ((μ₀_base.tilted E₀).prod γ_aux) :=
      integrable_exp_of_ae_le hVy_m.aemeasurable (ae_of_all _ fun _ => hB _)
    rw [h_fub1, integral_prod _ hVy_int_t, integral_tilted_eq_div]
    exact (mul_div_cancel₀ _ hZ₀_pos.ne').symm
  rw [hZ_prod, Real.log_mul hZ₀_pos.ne' hZw_pos.ne']

private theorem interp_field_deriv_pow_stein_fixed_disorder
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (r a : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (m : ℕ)
    (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
    let μ₀_base := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let E₀ (x₀ : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k' : Fin M, u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω₀.1.1 k' i * ((x₀.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω₀.1.2 k' + Real.sqrt (1 - q) * x₀.2 k'))) +
      ∑ i : Fin (N + 1), ((x₀.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω₀.2 i * Real.sqrt r
    let μ₀ := μ₀_base.tilted E₀
    let A₀ : ℝ := ((N : ℝ) + 1)⁻¹ * Real.log (∫ x₀, Real.exp (E₀ x₀) ∂μ₀_base)
    let γ_sh := Measure.pi fun _ : Fin (N + 1) ⊕ Unit => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : Unit => gaussianReal 0 1
    let α_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
      Sum.elim (fun i => Real.sqrt s * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
        (fun _ => Real.sqrt (1 - s) * Real.sqrt q)
    let W_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
      Sum.elim (fun i => (1 / (2 * Real.sqrt s)) * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
        (fun _ => -(1 / (2 * Real.sqrt (1 - s))) * Real.sqrt q)
    let α_aux (_ : Fin (N + 1) → ℤˣ) : Unit → ℝ := fun _ => Real.sqrt (1 - s) * Real.sqrt (1 - q)
    let W_aux (_ : Fin (N + 1) → ℤˣ) : Unit → ℝ :=
      fun _ => -(1 / (2 * Real.sqrt (1 - s))) * Real.sqrt (1 - q)
    let Z_w (w : (Fin (N + 1) ⊕ Unit) → ℝ) : ℝ :=
      ∫ y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
        Real.exp (u (α_sh y.1.1 ⬝ᵥ w + α_aux y.1.1 ⬝ᵥ y.2)) ∂(μ₀.prod γ_aux)
    ∫ w, (∫ σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
        1 * (W_sh (σ ()).1.1 ⬝ᵥ w + W_aux (σ ()).1.1 ⬝ᵥ (σ ()).2) *
          (∏ r_u : Unit, deriv u (α_sh (σ r_u).1.1 ⬝ᵥ w + α_aux (σ r_u).1.1 ⬝ᵥ (σ r_u).2))
        ∂(Measure.pi fun _ : Unit => (μ₀.prod γ_aux).tilted
          (fun y => u (α_sh y.1.1 ⬝ᵥ w + α_aux y.1.1 ⬝ᵥ y.2)))) *
        (A₀ + ((N : ℝ) + 1)⁻¹ * Real.log (Z_w w) - a) ^ m ∂γ_sh =
      (1 / 2) * ∫ w, (∫ σ : Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
        ((((N : ℝ) + 1)⁻¹ * ∑ i,
            (((σ (some ())).1.1 i : ℤ) : ℝ) * (((σ none).1.1 i : ℤ) : ℝ)) - q) *
          deriv u (α_sh (σ (some ())).1.1 ⬝ᵥ w + α_aux (σ (some ())).1.1 ⬝ᵥ (σ (some ())).2) *
          deriv u (α_sh (σ none).1.1 ⬝ᵥ w + α_aux (σ none).1.1 ⬝ᵥ (σ none).2)
        ∂(Measure.pi fun _ : Option Unit => (μ₀.prod γ_aux).tilted
          (fun y => u (α_sh y.1.1 ⬝ᵥ w + α_aux y.1.1 ⬝ᵥ y.2)))) *
        ((m : ℝ) * ((N : ℝ) + 1)⁻¹ * (A₀ + ((N : ℝ) + 1)⁻¹ * Real.log (Z_w w) - a) ^ (m - 1) -
          (A₀ + ((N : ℝ) + 1)⁻¹ * Real.log (Z_w w) - a) ^ m) ∂γ_sh := by
  intro μ₀_base E₀ μ₀ A₀ γ_sh γ_aux α_sh W_sh α_aux W_aux Z_w
  have hμ₀_prob : IsProbabilityMeasure μ₀ :=
    isProbabilityMeasure_tilted_interpEnergy (L := N + 1) hu.measurable (fun x => hu.le x) s q r ω₀
  obtain ⟨hGd, hhd, hGb_Icc, hGd_Icc⟩ :=
    differentiable_and_abs_le_shift_pow_on_Icc A₀ a ((N : ℝ) + 1) (by positivity) m
  have hst := stein_tilted_unit_replica_deriv_mul_comp_log μ₀ Prod.fst measurable_fst
    α_sh W_sh α_aux W_aux hu
    (fun τ₁ τ₂ => (((N : ℝ) + 1)⁻¹ * ∑ i, ((τ₁ i : ℤ) : ℝ) * ((τ₂ i : ℤ) : ℝ)) - q)
    (interp_stein_cov_shared hs hq.1) (interp_stein_cov_diag hs hq)
    hGd (hGb_Icc (abs_nonneg B)) (hGd_Icc (abs_nonneg B))
  dsimp only at hst
  have hlhs_u :
      (∫ w, (∫ σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
          1 * (W_sh (σ ()).1.1 ⬝ᵥ w + W_aux (σ ()).1.1 ⬝ᵥ (σ ()).2) *
            (∏ r_u : Unit, deriv u (α_sh (σ r_u).1.1 ⬝ᵥ w + α_aux (σ r_u).1.1 ⬝ᵥ (σ r_u).2))
          ∂(Measure.pi fun _ : Unit => (μ₀.prod γ_aux).tilted
            (fun y => u (α_sh y.1.1 ⬝ᵥ w + α_aux y.1.1 ⬝ᵥ y.2)))) *
        (A₀ + ((N : ℝ) + 1)⁻¹ * Real.log (Z_w w) - a) ^ m ∂γ_sh) =
      ∫ w, (∫ y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
          (W_sh y.1.1 ⬝ᵥ w + W_aux y.1.1 ⬝ᵥ y.2) *
            deriv u (α_sh y.1.1 ⬝ᵥ w + α_aux y.1.1 ⬝ᵥ y.2)
          ∂((μ₀.prod γ_aux).tilted (fun y => u (α_sh y.1.1 ⬝ᵥ w + α_aux y.1.1 ⬝ᵥ y.2)))) *
        (A₀ + ((N : ℝ) + 1)⁻¹ * Real.log (Z_w w) - a) ^ m ∂γ_sh := by
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    dsimp only; congr 1
    let ν_w := (μ₀.prod γ_aux).tilted (fun y => u (α_sh y.1.1 ⬝ᵥ w + α_aux y.1.1 ⬝ᵥ y.2))
    have hVp_m : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
        u (α_sh y.1.1 ⬝ᵥ w + α_aux y.1.1 ⬝ᵥ y.2) := by
      have ha1 : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
          α_sh y.1.1 ⬝ᵥ w :=
        Finset.measurable_sum _ fun idx _ =>
          ((measurable_of_finite fun τ => α_sh τ idx).comp
            (measurable_fst.comp measurable_fst)).mul_const _
      have ha2 : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
          α_aux y.1.1 ⬝ᵥ y.2 := by
        simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
        exact measurable_const.mul ((measurable_pi_apply ()).comp measurable_snd)
      exact hu.measurable.comp (ha1.add ha2)
    have hprob_w : IsProbabilityMeasure ν_w :=
      isProbabilityMeasure_tilted_of_ae_le hVp_m.aemeasurable (ae_of_all _ fun _ => hu.le _)
    have hm_y : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
        (W_sh y.1.1 ⬝ᵥ w + W_aux y.1.1 ⬝ᵥ y.2) *
          deriv u (α_sh y.1.1 ⬝ᵥ w + α_aux y.1.1 ⬝ᵥ y.2) := by
      have hw1 : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
          W_sh y.1.1 ⬝ᵥ w :=
        Finset.measurable_sum _ fun idx _ =>
          ((measurable_of_finite fun τ => W_sh τ idx).comp
            (measurable_fst.comp measurable_fst)).mul_const _
      have hw2 : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
          W_aux y.1.1 ⬝ᵥ y.2 := by
        simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
        exact measurable_const.mul ((measurable_pi_apply ()).comp measurable_snd)
      have ha1 : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
          α_sh y.1.1 ⬝ᵥ w + α_aux y.1.1 ⬝ᵥ y.2 := by
        have ha_sh : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
            α_sh y.1.1 ⬝ᵥ w :=
          Finset.measurable_sum _ fun idx _ =>
            ((measurable_of_finite fun τ => α_sh τ idx).comp
              (measurable_fst.comp measurable_fst)).mul_const _
        have ha_aux : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
            α_aux y.1.1 ⬝ᵥ y.2 := by
          simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
          exact measurable_const.mul ((measurable_pi_apply ()).comp measurable_snd)
        exact ha_sh.add ha_aux
      exact (hw1.add hw2).mul ((measurable_deriv u).comp ha1)
    rw [← (measurePreserving_funUnique ν_w Unit).integral_comp_of_aestronglyMeasurable
      hm_y.aestronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ fun σ => by
      simp [Finset.univ_unique])
  rw [hlhs_u, hst]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun w => ?_)
  dsimp only
  congr 2
  exact (hhd (Real.log (Z_w w))).deriv

private lemma interp_stein_pow_split_identities
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    (q r s : ℝ)
    (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1)
    let μ₀_base := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let γ_aux := Measure.pi fun _ : Unit => gaussianReal 0 1
    let splitΩ : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) ⊕ Unit) → ℝ) :=
      (((Fin.init ω.1.1, Fin.init ω.1.2), ω.2),
        Sum.elim (ω.1.1 (Fin.last M)) (fun _ => ω.1.2 (Fin.last M)))
    let E₀ (x₀ : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k' : Fin M, u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, splitΩ.1.1.1 k' i * ((x₀.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * splitΩ.1.1.2 k' + Real.sqrt (1 - q) * x₀.2 k'))) +
      ∑ i : Fin (N + 1), ((x₀.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * splitΩ.1.2 i * Real.sqrt r
    let S_fn (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) (k' : Fin (M + 1)) : ℝ :=
      Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k' i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k' + Real.sqrt (1 - q) * x.2 k')
    let S'_fn (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) (k' : Fin (M + 1)) : ℝ :=
      (1 / (2 * Real.sqrt s)) *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k' i * ((x.1 i : ℤ) : ℝ)) -
        (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * ω.1.2 k' + Real.sqrt (1 - q) * x.2 k')
    let E_s (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      (∑ k' : Fin (M + 1), u (S_fn x k')) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    let α_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
      Sum.elim (fun i => Real.sqrt s * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
        (fun _ => Real.sqrt (1 - s) * Real.sqrt q)
    let W_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
      Sum.elim (fun i => (1 / (2 * Real.sqrt s)) * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
        (fun _ => -(1 / (2 * Real.sqrt (1 - s))) * Real.sqrt q)
    let α_aux (_ : Fin (N + 1) → ℤˣ) : Unit → ℝ := fun _ => Real.sqrt (1 - s) * Real.sqrt (1 - q)
    let W_aux (_ : Fin (N + 1) → ℤˣ) : Unit → ℝ :=
      fun _ => -(1 / (2 * Real.sqrt (1 - s))) * Real.sqrt (1 - q)
    (∫ σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
        1 * (W_sh (σ ()).1.1 ⬝ᵥ splitΩ.2 + W_aux (σ ()).1.1 ⬝ᵥ (σ ()).2) *
          (∏ r_u : Unit, deriv u (α_sh (σ r_u).1.1 ⬝ᵥ splitΩ.2 + α_aux (σ r_u).1.1 ⬝ᵥ (σ r_u).2))
        ∂(Measure.pi fun _ : Unit => ((μ₀_base.tilted E₀).prod γ_aux).tilted
          (fun y => u (α_sh y.1.1 ⬝ᵥ splitΩ.2 + α_aux y.1.1 ⬝ᵥ y.2))) =
      ∫ x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        S'_fn x (Fin.last M) * deriv u (S_fn x (Fin.last M)) ∂(μ_s.tilted E_s)) ∧
    (∫ σ : Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
        ((((N : ℝ) + 1)⁻¹ * ∑ i,
            (((σ (some ())).1.1 i : ℤ) : ℝ) * (((σ none).1.1 i : ℤ) : ℝ)) - q) *
          deriv u
            (α_sh (σ (some ())).1.1 ⬝ᵥ splitΩ.2 + α_aux (σ (some ())).1.1 ⬝ᵥ (σ (some ())).2) *
          deriv u (α_sh (σ none).1.1 ⬝ᵥ splitΩ.2 + α_aux (σ none).1.1 ⬝ᵥ (σ none).2)
        ∂(Measure.pi fun _ : Option Unit => ((μ₀_base.tilted E₀).prod γ_aux).tilted
          (fun y => u (α_sh y.1.1 ⬝ᵥ splitΩ.2 + α_aux y.1.1 ⬝ᵥ y.2))) =
      ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_fn (σ 0) (Fin.last M)) * deriv u (S_fn (σ 1) (Fin.last M))
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted E_s)) := by
  intro μ_s μ₀_base γ_aux splitΩ E₀ S_fn S'_fn E_s α_sh W_sh α_aux W_aux
  let e_opt2 : Option Unit ≃ Fin 2 :=
    { toFun := fun o => match o with | some () => 0 | none => 1
      invFun := fun i => if i = 0 then some () else none
      left_inv := fun o => by cases o <;> simp
      right_inv := fun i => by fin_cases i <;> simp }
  let e_u : ℝ ≃ᵐ (Unit → ℝ) := (MeasurableEquiv.funUnique Unit ℝ).symm
  have hmp_u : MeasurePreserving ⇑e_u (gaussianReal 0 1) γ_aux :=
    (measurePreserving_funUnique (gaussianReal 0 1) Unit).symm
  let e_st : ((Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) ≃ᵐ
      ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) :=
    (interpStateLastSplit (N + 1) M).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) e_u)
  have hmp_st : MeasurePreserving ⇑e_st μ_s (μ₀_base.prod γ_aux) :=
    ((MeasurePreserving.id μ₀_base).prod hmp_u).comp
      (measurePreserving_interpStateLastSplit (N + 1) M)
  have he_st_apply (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      e_st x = ((x.1, Fin.init x.2), fun _ => x.2 (Fin.last M)) := by
    change (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) e_u
      (interpStateLastSplit (N + 1) M x)) = _
    rw [interpStateLastSplit_apply]; rfl
  have hS_last_eq (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      α_sh (e_st x).1.1 ⬝ᵥ splitΩ.2 + α_aux (e_st x).1.1 ⬝ᵥ (e_st x).2 =
      S_fn x (Fin.last M) := by
    rw [he_st_apply]
    dsimp only [α_sh, α_aux, splitΩ, S_fn]
    rw [sumElim_dotProduct_sumElim]
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton, Finset.mul_sum]
    have h1 : (∑ i : Fin (N + 1),
        Real.sqrt s * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((x.1 i : ℤ) : ℝ) *
          ω.1.1 (Fin.last M) i) =
      ∑ i : Fin (N + 1),
        Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
          (ω.1.1 (Fin.last M) i * ((x.1 i : ℤ) : ℝ))) :=
      Finset.sum_congr rfl fun _ _ => by ring
    rw [h1]; ring
  have hS'_last_eq (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) :
      W_sh (e_st x).1.1 ⬝ᵥ splitΩ.2 + W_aux (e_st x).1.1 ⬝ᵥ (e_st x).2 =
      S'_fn x (Fin.last M) := by
    rw [he_st_apply]
    dsimp only [W_sh, W_aux, splitΩ, S'_fn]
    rw [sumElim_dotProduct_sumElim]
    simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton, Finset.mul_sum]
    have h1 : (∑ i : Fin (N + 1),
        (1 / (2 * Real.sqrt s)) * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((x.1 i : ℤ) : ℝ) *
          ω.1.1 (Fin.last M) i) =
      ∑ i : Fin (N + 1),
        (1 / (2 * Real.sqrt s)) * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
          (ω.1.1 (Fin.last M) i * ((x.1 i : ℤ) : ℝ))) :=
      Finset.sum_congr rfl fun _ _ => by ring
    rw [h1]; ring
  have htilted_st :
      (μ_s.tilted E_s).map e_st =
      ((μ₀_base.tilted E₀).prod γ_aux).tilted
        (fun y => u (α_sh y.1.1 ⬝ᵥ splitΩ.2 + α_aux y.1.1 ⬝ᵥ y.2)) := by
    rw [map_tilted_measurableEquiv e_st hmp_st
      (measurable_interpEnergy_slice (L := N + 1) (M := M + 1) hu.measurable s q r ω)]
    have hE₀_int : Integrable (fun x₀ => Real.exp (E₀ x₀)) μ₀_base :=
      integrable_exp_of_ae_le
        (measurable_interpEnergy_slice (L := N + 1) (M := M) hu.measurable s q r
          splitΩ.1).aemeasurable
        (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r splitΩ.1))
    have hcomb : ((μ₀_base.tilted E₀).prod γ_aux).tilted
        (fun y => u (α_sh y.1.1 ⬝ᵥ splitΩ.2 + α_aux y.1.1 ⬝ᵥ y.2)) =
        (μ₀_base.prod γ_aux).tilted
          (fun y => E₀ y.1 + u (α_sh y.1.1 ⬝ᵥ splitΩ.2 + α_aux y.1.1 ⬝ᵥ y.2)) := by
      rw [← tilted_prod_comp_fst, tilted_tilted (hE₀_int.comp_fst γ_aux)]
      rfl
    rw [hcomb]
    congr 1; funext y
    obtain ⟨x, rfl⟩ := e_st.surjective y
    dsimp only [Function.comp_apply]
    rw [MeasurableEquiv.symm_apply_apply, hS_last_eq x, he_st_apply]
    dsimp only [E_s, E₀, splitΩ, S_fn]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.init_def]
    ring
  have hprob_ω : IsProbabilityMeasure (μ_s.tilted E_s) :=
    isProbabilityMeasure_tilted_interpEnergy (L := N + 1) hu.measurable (fun x => hu.le x) s q r ω
  refine ⟨?_, ?_⟩
  · let g_L (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      S'_fn x (Fin.last M) * deriv u (S_fn x (Fin.last M))
    have hg_Lm : Measurable g_L := by
      have hS_x : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) =>
          S_fn x (Fin.last M) := by dsimp only [S_fn]; fun_prop
      have hS'_x : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) =>
          S'_fn x (Fin.last M) := by dsimp only [S'_fn]; fun_prop
      exact hS'_x.mul ((measurable_deriv u).comp hS_x)
    let F_split_L (σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) : ℝ :=
      1 * (W_sh (σ ()).1.1 ⬝ᵥ splitΩ.2 + W_aux (σ ()).1.1 ⬝ᵥ (σ ()).2) *
        (∏ r_u : Unit,
          deriv u (α_sh (σ r_u).1.1 ⬝ᵥ splitΩ.2 + α_aux (σ r_u).1.1 ⬝ᵥ (σ r_u).2))
    have ht2 : ∀ f_u : Unit → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        F_split_L (fun r_u => e_st (f_u r_u)) = g_L (f_u ()) := fun f_u => by
      dsimp only [F_split_L, g_L]
      simp only [Finset.univ_unique, Finset.prod_singleton, one_mul]
      rw [hS_last_eq (f_u ()), hS'_last_eq (f_u ())]
    have h_u :=
      (measurePreserving_funUnique (μ_s.tilted E_s) Unit).integral_comp_of_aestronglyMeasurable
        (g := g_L) hg_Lm.aestronglyMeasurable
    rw [← htilted_st, integral_pi_map_equiv (μ_s.tilted E_s) e_st F_split_L]
    exact (integral_congr_ae (ae_of_all _ ht2)).trans h_u
  · let G₂ (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
        deriv u (S_fn (σ 0) (Fin.last M)) * deriv u (S_fn (σ 1) (Fin.last M))
    have hG2_m : Measurable G₂ := by
      have hS_l (l : Fin 2) : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) =>
          S_fn (σ l) (Fin.last M) := by dsimp only [S_fn]; fun_prop
      have hR_2 : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ) =>
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) := by
        refine ((Finset.measurable_sum _ fun i _ => ?_).const_mul _).sub_const _
        exact (measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp (measurable_pi_apply 0)))).mul
          (measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp (measurable_pi_apply 1))))
      exact (hR_2.mul ((measurable_deriv u).comp (hS_l 0))).mul
        ((measurable_deriv u).comp (hS_l 1))
    let F_split_R (σ : Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ)) : ℝ :=
      ((((N : ℝ) + 1)⁻¹ * ∑ i,
          (((σ (some ())).1.1 i : ℤ) : ℝ) * (((σ none).1.1 i : ℤ) : ℝ)) - q) *
        deriv u
          (α_sh (σ (some ())).1.1 ⬝ᵥ splitΩ.2 + α_aux (σ (some ())).1.1 ⬝ᵥ (σ (some ())).2) *
        deriv u (α_sh (σ none).1.1 ⬝ᵥ splitΩ.2 + α_aux (σ none).1.1 ⬝ᵥ (σ none).2)
    let e_pi := MeasurableEquiv.piCongrLeft
      (fun _ : Fin 2 => (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) e_opt2
    have hmp_opt2 : MeasurePreserving ⇑e_pi
        (Measure.pi fun _ : Option Unit => μ_s.tilted E_s)
        (Measure.pi fun _ : Fin 2 => μ_s.tilted E_s) :=
      measurePreserving_piCongrLeft (fun _ : Fin 2 => μ_s.tilted E_s) e_opt2
    rw [← htilted_st, integral_pi_map_equiv (μ_s.tilted E_s) e_st F_split_R]
    refine (integral_congr_ae (ae_of_all _ fun τ_o => ?_)).trans
      (hmp_opt2.integral_comp_of_aestronglyMeasurable hG2_m.aestronglyMeasurable)
    have h0 : e_pi τ_o 0 = τ_o (some ()) := by
      change (Equiv.piCongrLeft (fun _ : Fin 2 => (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ))
        e_opt2 τ_o) 0 = _
      rw [Equiv.piCongrLeft_apply]; rfl
    have h1 : e_pi τ_o 1 = τ_o none := by
      change (Equiv.piCongrLeft (fun _ : Fin 2 => (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ))
        e_opt2 τ_o) 1 = _
      rw [Equiv.piCongrLeft_apply]; rfl
    dsimp only [F_split_R, G₂, Function.comp_apply]
    rw [h0, h1, hS_last_eq (τ_o (some ())), hS_last_eq (τ_o none),
      he_st_apply (τ_o (some ())), he_st_apply (τ_o none)]

private theorem integral_interpolating_field_deriv_ibp_pow_last
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (r a : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (m : ℕ) :
    let P_g := Measure.pi fun _ : Fin (M + 1) =>
      Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin (M + 1) => gaussianReal 0 1)
    let S_fn (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) (k' : Fin (M + 1)) : ℝ :=
      Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k' i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k' + Real.sqrt (1 - q) * x.2 k')
    let S'_fn (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) (k' : Fin (M + 1)) : ℝ :=
      (1 / (2 * Real.sqrt s)) *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k' i * ((x.1 i : ℤ) : ℝ)) -
        (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * ω.1.2 k' + Real.sqrt (1 - q) * x.2 k')
    let E_s (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
      (∑ k' : Fin (M + 1), u (S_fn ω x k')) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    let A (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s ω x) ∂μ_s)
    ∫ ω, (∫ x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        S'_fn ω x (Fin.last M) * deriv u (S_fn ω x (Fin.last M))
        ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m ∂P =
      (1 / 2) * ∫ ω,
        (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
            deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M))
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) *
        ((m : ℝ) * ((N : ℝ) + 1)⁻¹ * (A ω - a) ^ (m - 1) - (A ω - a) ^ m) ∂P := by
  intro P_g P_z P_z' P μ_s S_fn S'_fn E_s A
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z']; infer_instance
  let P₀ :=
    (((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
    (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod
    (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))
  let μ₀_base := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
    (Measure.pi fun _ : Fin M => gaussianReal 0 1)
  let E₀ (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (x₀ : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    (∑ k' : Fin M, u (Real.sqrt s *
        ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω₀.1.1 k' i * ((x₀.1 i : ℤ) : ℝ)) +
      Real.sqrt (1 - s) * (Real.sqrt q * ω₀.1.2 k' + Real.sqrt (1 - q) * x₀.2 k'))) +
    ∑ i : Fin (N + 1), ((x₀.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω₀.2 i * Real.sqrt r
  let μ₀ (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :=
    μ₀_base.tilted (E₀ ω₀)
  let A₀_fn (ω₀ : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    ((N : ℝ) + 1)⁻¹ * Real.log (∫ x₀, Real.exp (E₀ ω₀ x₀) ∂μ₀_base)
  let γ_sh := Measure.pi fun _ : Fin (N + 1) ⊕ Unit => gaussianReal 0 1
  let γ_aux := Measure.pi fun _ : Unit => gaussianReal 0 1
  let α_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
    Sum.elim (fun i => Real.sqrt s * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
      (fun _ => Real.sqrt (1 - s) * Real.sqrt q)
  let W_sh (τ : Fin (N + 1) → ℤˣ) : (Fin (N + 1) ⊕ Unit) → ℝ :=
    Sum.elim (fun i => (1 / (2 * Real.sqrt s)) * (Real.sqrt (N + 1 : ℕ))⁻¹ * ((τ i : ℤ) : ℝ))
      (fun _ => -(1 / (2 * Real.sqrt (1 - s))) * Real.sqrt q)
  let α_aux (_ : Fin (N + 1) → ℤˣ) : Unit → ℝ := fun _ => Real.sqrt (1 - s) * Real.sqrt (1 - q)
  let W_aux (_ : Fin (N + 1) → ℤˣ) : Unit → ℝ :=
    fun _ => -(1 / (2 * Real.sqrt (1 - s))) * Real.sqrt (1 - q)
  let Z_w (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      ((Fin (N + 1) ⊕ Unit) → ℝ)) : ℝ :=
    ∫ y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
      Real.exp (u (α_sh y.1.1 ⬝ᵥ p.2 + α_aux y.1.1 ⬝ᵥ y.2)) ∂((μ₀ p.1).prod γ_aux)
  let A_sp (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      ((Fin (N + 1) ⊕ Unit) → ℝ)) : ℝ :=
    A₀_fn p.1 + ((N : ℝ) + 1)⁻¹ * Real.log (Z_w p)
  obtain ⟨hIL_m, hIR_m⟩ :=
    measurable_interp_stein_split (N := N) (M := M) hu.measurable (fun x => hu.le x) q r s
  let I_L (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      ((Fin (N + 1) ⊕ Unit) → ℝ)) : ℝ :=
    ∫ σ : Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
      1 * (W_sh (σ ()).1.1 ⬝ᵥ p.2 + W_aux (σ ()).1.1 ⬝ᵥ (σ ()).2) *
        (∏ r_u : Unit, deriv u (α_sh (σ r_u).1.1 ⬝ᵥ p.2 + α_aux (σ r_u).1.1 ⬝ᵥ (σ r_u).2))
      ∂(Measure.pi fun _ : Unit => ((μ₀ p.1).prod γ_aux).tilted
        (fun y => u (α_sh y.1.1 ⬝ᵥ p.2 + α_aux y.1.1 ⬝ᵥ y.2)))
  let I_R (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      ((Fin (N + 1) ⊕ Unit) → ℝ)) : ℝ :=
    ∫ σ : Option Unit → ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ),
      ((((N : ℝ) + 1)⁻¹ * ∑ i,
          (((σ (some ())).1.1 i : ℤ) : ℝ) * (((σ none).1.1 i : ℤ) : ℝ)) - q) *
        deriv u (α_sh (σ (some ())).1.1 ⬝ᵥ p.2 + α_aux (σ (some ())).1.1 ⬝ᵥ (σ (some ())).2) *
        deriv u (α_sh (σ none).1.1 ⬝ᵥ p.2 + α_aux (σ none).1.1 ⬝ᵥ (σ none).2)
      ∂(Measure.pi fun _ : Option Unit => ((μ₀ p.1).prod γ_aux).tilted
        (fun y => u (α_sh y.1.1 ⬝ᵥ p.2 + α_aux y.1.1 ⬝ᵥ y.2)))
  let splitΩ (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) ⊕ Unit) → ℝ) :=
    (((Fin.init ω.1.1, Fin.init ω.1.2), ω.2),
      Sum.elim (ω.1.1 (Fin.last M)) (fun _ => ω.1.2 (Fin.last M)))
  have hmp_dis := measurePreserving_interpConstraintDisorder_lastSplit (N + 1) M
  have hA_split (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      A_sp (splitΩ ω) = A ω := by
    dsimp only [A_sp, A₀_fn, Z_w, A, splitΩ, μ₀]
    rw [log_interpPartition_last_split_eq hu.measurable (fun x => hu.le x) s q r ω, mul_add]
  let inv_splitΩ
      (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) ⊕ Unit) → ℝ)) :
      ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ) :=
    ((Fin.snoc p.1.1.1 (fun i => p.2 (Sum.inl i)), Fin.snoc p.1.1.2 (p.2 (Sum.inr ()))), p.1.2)
  have hinv_m : Measurable inv_splitΩ := by
    refine ((measurable_pi_iff.2 fun k => ?_).prodMk (measurable_pi_iff.2 fun k => ?_)).prodMk
      (measurable_snd.comp measurable_fst)
    · refine Fin.lastCases ?_ (fun k₀ => ?_) k
      · simp only [Fin.snoc_last]
        exact measurable_pi_iff.2 fun i => (measurable_pi_apply (Sum.inl i)).comp measurable_snd
      · simp only [Fin.snoc_castSucc]
        exact (measurable_pi_apply k₀).comp
          (measurable_fst.comp (measurable_fst.comp measurable_fst))
    · refine Fin.lastCases ?_ (fun k₀ => ?_) k
      · simp only [Fin.snoc_last]
        exact (measurable_pi_apply (Sum.inr ())).comp measurable_snd
      · simp only [Fin.snoc_castSucc]
        exact (measurable_pi_apply k₀).comp
          (measurable_snd.comp (measurable_fst.comp measurable_fst))
  have hsplit_inv (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      ((Fin (N + 1) ⊕ Unit) → ℝ)) : splitΩ (inv_splitΩ p) = p := by
    rcases p with ⟨⟨⟨g₀, z₀⟩, z'⟩, w⟩
    dsimp only [splitΩ, inv_splitΩ]
    refine Prod.ext (Prod.ext (Prod.ext ?_ ?_) rfl) ?_
    · exact @Fin.init_snoc M (fun _ => Fin (N + 1) → ℝ) (fun i => w (Sum.inl i)) g₀
    · exact @Fin.init_snoc M (fun _ => ℝ) (w (Sum.inr ())) z₀
    · ext idx; rcases idx with i | ⟨⟩ <;> simp
  have hAsp_m : Measurable A_sp := by
    obtain ⟨hm_log₁, -⟩ := measurable_and_abs_log_interpPartition_le (N := N) (M := M + 1)
      hu.measurable hu.abs_le q r hs.1.le
    have hAm : Measurable A := hm_log₁.const_mul _
    have heq_Asp : A_sp = A ∘ inv_splitΩ := by
      funext p; dsimp only [Function.comp_apply]; rw [← hA_split (inv_splitΩ p), hsplit_inv p]
    rw [heq_Asp]
    exact hAm.comp hinv_m
  let J_L (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      ((Fin (N + 1) ⊕ Unit) → ℝ)) : ℝ :=
    I_L p * (A_sp p - a) ^ m
  let J_R (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
      ((Fin (N + 1) ⊕ Unit) → ℝ)) : ℝ :=
    I_R p * ((m : ℝ) * ((N : ℝ) + 1)⁻¹ * (A_sp p - a) ^ (m - 1) - (A_sp p - a) ^ m)
  have hJL_m : Measurable J_L := hIL_m.mul ((hAsp_m.sub_const a).pow_const m)
  have hJR_m : Measurable J_R :=
    hIR_m.mul ((((hAsp_m.sub_const a).pow_const (m - 1)).const_mul _).sub
      ((hAsp_m.sub_const a).pow_const m))
  have hA_mem (p_exp : ℕ) : MemLp (fun ω => A ω - a) ((p_exp : ℕ) : ℝ≥0) P :=
    (memLp_interp_log_partition_and_deriv (N := N) (M := M + 1) hu.measurable hu.abs_le (D₁ := D₁)
      q r a 1 hs.1.le ((p_exp : ℕ) : ℝ≥0)).2.2
  have hJL_int : Integrable J_L (P₀.prod γ_sh) := by
    rw [← hmp_dis.integrable_comp hJL_m.aestronglyMeasurable]
    have hJL_pull : J_L ∘ splitΩ = fun ω =>
        (∫ x, S'_fn ω x (Fin.last M) * deriv u (S_fn ω x (Fin.last M))
          ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m := by
      funext ω
      obtain ⟨hid1, -⟩ := interp_stein_pow_split_identities hu q r s ω
      dsimp only [Function.comp_apply, J_L]
      rw [hA_split ω]
      exact congrArg (· * (A ω - a) ^ m) hid1
    rw [hJL_pull]
    exact integrable_mul_pow_of_memLp
      (memLp_two_interp_field_deriv_gibbs (N := N) (M := M + 1) hu q r s (Fin.last M))
      m (hA_mem (2 * m))
  have hJR_int : Integrable J_R (P₀.prod γ_sh) := by
    rw [← hmp_dis.integrable_comp hJR_m.aestronglyMeasurable]
    have hIR_bd (p : (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        ((Fin (N + 1) ⊕ Unit) → ℝ)) : |I_R p| ≤ 2 * |D₁| ^ 2 := by
      have hμ₀_p : IsProbabilityMeasure (μ₀ p.1) :=
        isProbabilityMeasure_tilted_interpEnergy (L := N + 1) hu.measurable
          (fun x => hu.le x) s q r p.1
      have hVp_m : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
          u (α_sh y.1.1 ⬝ᵥ p.2 + α_aux y.1.1 ⬝ᵥ y.2) := by
        have ha1 : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
            α_sh y.1.1 ⬝ᵥ p.2 :=
          Finset.measurable_sum _ fun idx _ =>
            ((measurable_of_finite fun τ => α_sh τ idx).comp
              (measurable_fst.comp measurable_fst)).mul_const _
        have ha2 : Measurable fun y : ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) × (Unit → ℝ) =>
            α_aux y.1.1 ⬝ᵥ y.2 := by
          simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
          exact measurable_const.mul ((measurable_pi_apply ()).comp measurable_snd)
        exact hu.measurable.comp (ha1.add ha2)
      have hprob_p : IsProbabilityMeasure
          (((μ₀ p.1).prod γ_aux).tilted
            fun y => u (α_sh y.1.1 ⬝ᵥ p.2 + α_aux y.1.1 ⬝ᵥ y.2)) :=
        isProbabilityMeasure_tilted_of_ae_le hVp_m.aemeasurable (ae_of_all _ fun _ => hu.le _)
      exact abs_integral_le_of_forall_abs_le _ fun σ => by
        rw [abs_mul, abs_mul, sq]
        have hd_ov := abs_spin_overlap_sub_le_two hq (σ (some ())).1.1 (σ none).1.1
        calc _ ≤ 2 * |D₁| * |D₁| :=
              mul_le_mul (mul_le_mul hd_ov (hu.abs_deriv_le_abs _)
                (abs_nonneg _) zero_le_two) (hu.abs_deriv_le_abs _)
                (abs_nonneg _) (by positivity)
          _ = 2 * (|D₁| * |D₁|) := by ring
    have hIR_pull_L2 : MemLp (fun ω => I_R (splitΩ ω)) 2 P :=
      (MemLp.of_bound hIR_m.aestronglyMeasurable (2 * |D₁| ^ 2)
        (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hIR_bd p)).comp_measurePreserving
        hmp_dis
    have hJR_pull : J_R ∘ splitΩ = fun ω =>
        (I_R (splitΩ ω) * ((m : ℝ) * ((N : ℝ) + 1)⁻¹)) * (A ω - a) ^ (m - 1) -
          I_R (splitΩ ω) * (A ω - a) ^ m := by
      funext ω; dsimp only [Function.comp_apply, J_R]; rw [hA_split ω]; ring
    rw [hJR_pull]
    exact (integrable_mul_pow_of_memLp (hIR_pull_L2.mul_const _) (m - 1)
      (hA_mem (2 * (m - 1)))).sub
      (integrable_mul_pow_of_memLp hIR_pull_L2 m (hA_mem (2 * m)))
  have hlhs_eq : (∫ ω, (∫ x : (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
      S'_fn ω x (Fin.last M) * deriv u (S_fn ω x (Fin.last M)) ∂(μ_s.tilted (E_s ω))) *
      (A ω - a) ^ m ∂P) = ∫ p, J_L p ∂(P₀.prod γ_sh) := by
    refine (integral_congr_ae (ae_of_all _ fun ω => ?_)).trans
      (hmp_dis.integral_comp_of_aestronglyMeasurable hJL_m.aestronglyMeasurable)
    obtain ⟨hid1, -⟩ := interp_stein_pow_split_identities hu q r s ω
    dsimp only [Function.comp_apply, J_L]
    rw [hA_split ω]
    exact congrArg (· * (A ω - a) ^ m) hid1.symm
  have hrhs_eq : (∫ ω, (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
      ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
        deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M))
      ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) *
      ((m : ℝ) * ((N : ℝ) + 1)⁻¹ * (A ω - a) ^ (m - 1) - (A ω - a) ^ m) ∂P) =
      ∫ p, J_R p ∂(P₀.prod γ_sh) := by
    refine (integral_congr_ae (ae_of_all _ fun ω => ?_)).trans
      (hmp_dis.integral_comp_of_aestronglyMeasurable hJR_m.aestronglyMeasurable)
    obtain ⟨-, hid2⟩ := interp_stein_pow_split_identities hu q r s ω
    dsimp only [Function.comp_apply, J_R]
    rw [hA_split ω]
    exact congrArg (· * ((m : ℝ) * ((N : ℝ) + 1)⁻¹ * (A ω - a) ^ (m - 1) - (A ω - a) ^ m))
      hid2.symm
  rw [hlhs_eq, hrhs_eq, integral_prod J_L hJL_int, integral_prod J_R hJR_int,
    ← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun ω₀ =>
    interp_field_deriv_pow_stein_fixed_disorder (N := N) (M := M) hu hq r a hs m ω₀)

private lemma interpPartition_constraintSwap_eq
    {N M : ℕ} {u : ℝ → ℝ} (hu : Measurable u)
    (q r s : ℝ) (k₁ k₂ : Fin M)
    (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let E_s (ω' : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k' : Fin M, u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω'.1.1 k' i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω'.1.2 k' + Real.sqrt (1 - q) * x.2 k'))) +
      ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω'.2 i * Real.sqrt r
    ∫ x, Real.exp (E_s (interpConstraintDisorderSwap k₁ k₂ ω) x) ∂μ_s =
      ∫ x, Real.exp (E_s ω x) ∂μ_s := by
  intro μ_s E_s
  have hEm := measurable_interpEnergy_slice (L := N + 1) (M := M) hu s q r ω
  have hmp := measurePreserving_interpConstraintStateSwap (L := N + 1) k₁ k₂
  have hcomp :
      (fun x => Real.exp (E_s (interpConstraintDisorderSwap k₁ k₂ ω) x)) =
      (fun x => Real.exp (E_s ω x)) ∘ ⇑(interpConstraintStateSwap k₁ k₂) := by
    funext x
    dsimp only [Function.comp_apply]
    congr 1
    rw [interpConstraintStateSwap_apply]
    dsimp only [E_s, interpConstraintDisorderSwap]
    congr 1
    rw [← Equiv.sum_comp (Equiv.swap k₁ k₂)]
    refine Finset.sum_congr rfl fun _ _ => ?_
    simp
  rw [hcomp]
  exact hmp.integral_comp_of_aestronglyMeasurable
    (Real.measurable_exp.comp hEm).aestronglyMeasurable

private theorem integral_interpolating_field_deriv_ibp_pow
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (r a : ℝ) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (m : ℕ) (k : Fin M) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let S_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (k' : Fin M) : ℝ :=
      Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k' i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k' + Real.sqrt (1 - q) * x.2 k')
    let S'_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (k' : Fin M) : ℝ :=
      (1 / (2 * Real.sqrt s)) *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k' i * ((x.1 i : ℤ) : ℝ)) -
        (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * ω.1.2 k' + Real.sqrt (1 - q) * x.2 k')
    let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k' : Fin M, u (S_fn ω x k')) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    let A (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s ω x) ∂μ_s)
    ∫ ω, (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        S'_fn ω x k * deriv u (S_fn ω x k) ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m ∂P =
      (1 / 2) * ∫ ω,
        (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
            deriv u (S_fn ω (σ 0) k) * deriv u (S_fn ω (σ 1) k)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) *
        ((m : ℝ) * ((N : ℝ) + 1)⁻¹ * (A ω - a) ^ (m - 1) - (A ω - a) ^ m) ∂P := by
  rcases M with _ | M
  · exact Fin.elim0 k
  intro P_g P_z P_z' P μ_s S_fn S'_fn E_s A
  have hEm_joint := measurable_interpEnergy_joint (L := N + 1) (M := M + 1) hu.measurable s q r
  obtain ⟨hm_log, -⟩ := measurable_and_abs_log_interpPartition_le (N := N) (M := M + 1)
    hu.measurable hu.abs_le q r hs.1.le
  have hAm : Measurable A := hm_log.const_mul _
  have hA_sw (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      A (interpConstraintDisorderSwap k (Fin.last M) ω) = A ω := by
    dsimp only [A]
    rw [interpPartition_constraintSwap_eq hu.measurable q r s k (Fin.last M) ω]
  have htilted_swap
      (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
      μ_s.tilted (E_s (interpConstraintDisorderSwap k (Fin.last M) ω)) =
      (μ_s.tilted (E_s ω)).map (interpConstraintStateSwap k (Fin.last M)) := by
    rw [map_tilted_measurableEquiv (interpConstraintStateSwap k (Fin.last M))
      (measurePreserving_interpConstraintStateSwap k (Fin.last M))
      (Measurable.of_uncurry_left hEm_joint)]
    congr 1; funext x
    dsimp only [Function.comp_apply]
    rw [interpConstraintStateSwap_symm_apply]
    dsimp only [E_s, S_fn, interpConstraintDisorderSwap]
    congr 1
    rw [← Equiv.sum_comp (Equiv.swap k (Fin.last M))]
    refine Finset.sum_congr rfl fun _ _ => ?_
    simp
  have hmp := measurePreserving_interpConstraintDisorderSwap (L := N + 1) k (Fin.last M)
  have hlhs_sw :
      ∫ ω, (∫ x, S'_fn ω x k * deriv u (S_fn ω x k) ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m ∂P =
      ∫ ω, (∫ x, S'_fn ω x (Fin.last M) * deriv u (S_fn ω x (Fin.last M))
        ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m ∂P := by
    let Φ_l (k' : Fin (M + 1))
        (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      (∫ x, S'_fn ω x k' * deriv u (S_fn ω x k') ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m
    have hΦ_m : Measurable (Φ_l (Fin.last M)) :=
      (measurable_integral_tilted_dep hEm_joint
        ((measurable_interpFieldDeriv_joint (L := N + 1) (M := M + 1) s q (Fin.last M)).mul
          ((measurable_deriv u).comp
            (measurable_interpField_joint (L := N + 1) (M := M + 1) s q (Fin.last M))))).mul
        ((hAm.sub_const a).pow_const m)
    have hpt_sw (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
        Φ_l (Fin.last M) (interpConstraintDisorderSwap k (Fin.last M) ω) = Φ_l k ω := by
      dsimp only [Φ_l]
      rw [hA_sw ω, htilted_swap ω, integral_map_equiv]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      dsimp only [Function.comp_apply, S_fn, S'_fn, interpConstraintDisorderSwap]
      simp [interpConstraintStateSwap_apply]
    exact (integral_congr_ae (ae_of_all _ fun ω => (hpt_sw ω).symm)).trans
      (hmp.integral_comp_of_aestronglyMeasurable hΦ_m.aestronglyMeasurable)
  have hrhs_sw :
      ∫ ω, (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_fn ω (σ 0) k) * deriv u (S_fn ω (σ 1) k)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) *
        ((m : ℝ) * ((N : ℝ) + 1)⁻¹ * (A ω - a) ^ (m - 1) - (A ω - a) ^ m) ∂P =
      ∫ ω, (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M))
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) *
        ((m : ℝ) * ((N : ℝ) + 1)⁻¹ * (A ω - a) ^ (m - 1) - (A ω - a) ^ m) ∂P := by
    let Ψ_r (k' : Fin (M + 1))
        (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ),
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_fn ω (σ 0) k') * deriv u (S_fn ω (σ 1) k')
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) *
      ((m : ℝ) * ((N : ℝ) + 1)⁻¹ * (A ω - a) ^ (m - 1) - (A ω - a) ^ m)
    have hΨ_m : Measurable (Ψ_r (Fin.last M)) := by
      have hS_l (l : Fin 2) : Measurable fun p :
          (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => S_fn p.1 (p.2 l) (Fin.last M) :=
        measurable_interpField_replica_joint (L := N + 1) (M := M + 1) s q (Fin.last M) l
      have hR_m : Measurable fun p :
          (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) =>
          (((N : ℝ) + 1)⁻¹ * ∑ i, ((((p.2 0).1 i : ℤ) : ℝ) * (((p.2 1).1 i : ℤ) : ℝ))) - q := by
        refine ((Finset.measurable_sum _ fun i _ => ?_).const_mul _).sub_const _
        exact (measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd)))).mul
          (measurable_units_cast.comp ((measurable_pi_apply i).comp
            (measurable_fst.comp ((measurable_pi_apply 1).comp measurable_snd))))
      let G_last
          (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ))
          (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) : ℝ :=
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          deriv u (S_fn ω (σ 0) (Fin.last M)) * deriv u (S_fn ω (σ 1) (Fin.last M))
      have hGm : Measurable fun p :
          (((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) ×
            (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin (M + 1) → ℝ)) => G_last p.1 p.2 :=
        (hR_m.mul ((measurable_deriv u).comp (hS_l 0))).mul
          ((measurable_deriv u).comp (hS_l 1))
      have h1 := measurable_integral_pi_tilted (μ := μ_s) (E := E_s) (G := G_last) hEm_joint hGm
      exact h1.mul ((((hAm.sub_const a).pow_const (m - 1)).const_mul _).sub
        ((hAm.sub_const a).pow_const m))
    have hpt_sw (ω : ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (M + 1) → ℝ)) × (Fin (N + 1) → ℝ)) :
        Ψ_r (Fin.last M) (interpConstraintDisorderSwap k (Fin.last M) ω) = Ψ_r k ω := by
      have hprob : IsProbabilityMeasure (μ_s.tilted (E_s ω)) :=
        isProbabilityMeasure_tilted_interpEnergy (L := N + 1) hu.measurable
          (fun x => hu.le x) s q r ω
      dsimp only [Ψ_r]
      rw [hA_sw ω, htilted_swap ω,
        integral_pi_map_equiv (μ_s.tilted (E_s ω)) (interpConstraintStateSwap k (Fin.last M))]
      congr 1
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      dsimp only [S_fn, interpConstraintDisorderSwap]
      simp [interpConstraintStateSwap_apply]
    exact (integral_congr_ae (ae_of_all _ fun ω => (hpt_sw ω).symm)).trans
      (hmp.integral_comp_of_aestronglyMeasurable hΨ_m.aestronglyMeasurable)
  rw [hlhs_sw, hrhs_sw]
  exact integral_interpolating_field_deriv_ibp_pow_last hu hq r a hs m

private theorem integral_interpolating_fixed_center_deriv_split
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    (q r a : ℝ) {s : ℝ} (hs0 : 0 ≤ s) (m : ℕ) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let S_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (k : Fin M) : ℝ :=
      Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k)
    let S'_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (k : Fin M) : ℝ :=
      (1 / (2 * Real.sqrt s)) *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) -
        (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k)
    let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (S_fn ω x k)) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    let A (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s ω x) ∂μ_s)
    ∫ ω, (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        ((∑ k : Fin M, S'_fn ω x k * deriv u (S_fn ω x k)) -
          (1 / (2 * Real.sqrt (1 - s))) *
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m ∂P =
      (∑ k : Fin M, ∫ ω,
        (∫ x, S'_fn ω x k * deriv u (S_fn ω x k) ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m ∂P) -
      ∫ ω, (∫ x, (1 / (2 * Real.sqrt (1 - s))) *
          (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
          ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m ∂P := by
  intro P_g P_z P_z' P μ_s S_fn S'_fn E_s A
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z']; infer_instance
  have hEm_joint := measurable_interpEnergy_joint (L := N + 1) (M := M) hu.measurable s q r
  have hprob_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      IsProbabilityMeasure (μ_s.tilted (E_s ω)) :=
    isProbabilityMeasure_tilted_interpEnergy (L := N + 1) hu.measurable (fun x => hu.le x) s q r ω
  have hA_mem (p : ℕ) : MemLp (fun ω => A ω - a) ((p : ℕ) : ℝ≥0) P :=
    (memLp_interp_log_partition_and_deriv (N := N) (M := M) hu.measurable hu.abs_le (D₁ := D₁)
      q r a 1 hs0 ((p : ℕ) : ℝ≥0)).2.2
  have hS'_in_pt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (k : Fin M) :
      Integrable (fun x => S'_fn ω x k * deriv u (S_fn ω x k)) (μ_s.tilted (E_s ω)) := by
    have hm : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
        S'_fn ω x k * deriv u (S_fn ω x k) := by
      have h1 : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => S'_fn ω x k := by
        dsimp only [S'_fn]; fun_prop
      have h2 : Measurable fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => S_fn ω x k := by
        dsimp only [S_fn]; fun_prop
      exact h1.mul ((measurable_deriv u).comp h2)
    let c0_ω : ℝ := |D₁| * ((1 / (2 * Real.sqrt s)) *
        ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), |ω.1.1 k i|) +
      (1 / (2 * Real.sqrt (1 - s))) * (Real.sqrt q * |ω.1.2 k|))
    let c1 : ℝ := |D₁| * ((1 / (2 * Real.sqrt (1 - s))) * Real.sqrt (1 - q))
    have hpt_x (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        |S'_fn ω x k * deriv u (S_fn ω x k)| ≤ c0_ω + c1 * |x.2 k| := by
      rw [abs_mul, mul_comm _ |deriv u _|]
      have hd_b : |deriv u (S_fn ω x k)| ≤ |D₁| := hu.abs_deriv_le_abs _
      have hS'_b : |S'_fn ω x k| ≤
          (1 / (2 * Real.sqrt s)) *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), |ω.1.1 k i|) +
          (1 / (2 * Real.sqrt (1 - s))) *
            (Real.sqrt q * |ω.1.2 k| + Real.sqrt (1 - q) * |x.2 k|) := by
        dsimp only [S'_fn]
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul (1 / (2 * Real.sqrt s)), abs_of_nonneg (by positivity),
            abs_mul ((Real.sqrt (N + 1 : ℕ))⁻¹), abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
              rw [abs_mul, abs_units_cast_eq_one, mul_one])) (by positivity)) (by positivity)
        · rw [abs_mul (1 / (2 * Real.sqrt (1 - s))), abs_of_nonneg (by positivity)]
          refine mul_le_mul_of_nonneg_left
            ((abs_add_le _ _).trans (add_le_add ?_ ?_)) (by positivity)
          · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      calc |deriv u (S_fn ω x k)| * |S'_fn ω x k|
          ≤ |D₁| * ((1 / (2 * Real.sqrt s)) *
              ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i : Fin (N + 1), |ω.1.1 k i|) +
            (1 / (2 * Real.sqrt (1 - s))) *
              (Real.sqrt q * |ω.1.2 k| + Real.sqrt (1 - q) * |x.2 k|)) :=
            mul_le_mul hd_b hS'_b (abs_nonneg _) (abs_nonneg D₁)
        _ = c0_ω + c1 * |x.2 k| := by dsimp only [c0_ω, c1]; ring
    have hξ_k : Integrable (fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) => |x.2 k|) μ_s :=
      (integrable_comp_eval (μ := fun _ : Fin M => gaussianReal 0 1) (i := k)
        IsGaussian.integrable_id.abs).comp_snd _
    exact integrable_tilted_of_abs_le_envelope
      (Measurable.of_uncurry_left hEm_joint).aemeasurable hm.aestronglyMeasurable
      ((integrable_const c0_ω).add (hξ_k.const_mul c1))
      (ae_of_all _ (interpEnergy_le (fun x => hu.le x) s q r ω))
      (ae_of_all _ hpt_x)
  have hext_in_pt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Integrable (fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
        (1 / (2 * Real.sqrt (1 - s))) *
          ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        (μ_s.tilted (E_s ω)) := by
    have := hprob_ω ω
    exact Integrable.of_bound (by fun_prop)
      ((1 / (2 * Real.sqrt (1 - s))) * ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_mul (1 / (2 * Real.sqrt (1 - s))),
          abs_of_nonneg (by positivity)]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_mul, abs_units_cast_eq_one, one_mul,
            abs_of_nonneg (Real.sqrt_nonneg _)]))
  have hS'_in_P (k : Fin M) :
      Integrable (fun ω =>
        (∫ x, S'_fn ω x k * deriv u (S_fn ω x k) ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m) P :=
    integrable_mul_pow_of_memLp
      (memLp_two_interp_field_deriv_gibbs (N := N) (M := M) hu q r s k)
      m (hA_mem (2 * m))
  have hext_in_P :
      Integrable (fun ω => (∫ x, (1 / (2 * Real.sqrt (1 - s))) *
        (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m) P := by
    have hg_e : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          ((Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) =>
        (1 / (2 * Real.sqrt (1 - s))) *
          ∑ i : Fin (N + 1), ((p.2.1 i : ℤ) : ℝ) * p.1.2 i * Real.sqrt r := by
      refine (Finset.measurable_sum _ fun i _ => ?_).const_mul _
      exact ((measurable_units_cast.comp ((measurable_pi_apply i).comp
          (measurable_fst.comp measurable_snd))).mul
        ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst))).mul_const _
    have hm_e : Measurable fun ω => ∫ x, (1 / (2 * Real.sqrt (1 - s))) *
        (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r) ∂(μ_s.tilted (E_s ω)) :=
      measurable_integral_tilted_dep hEm_joint hg_e
    have hdom_e : MemLp
        (fun ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ) =>
          (1 / (2 * Real.sqrt (1 - s))) * ∑ i : Fin (N + 1), |ω.2 i| * Real.sqrt r) 2 P :=
      (memLp_finsetSum Finset.univ fun i _ =>
        (memLp_abs_snd_interpDisorder N M i 2).mul_const _).const_mul _
    have hext_L2 : MemLp (fun ω => ∫ x, (1 / (2 * Real.sqrt (1 - s))) *
        (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        ∂(μ_s.tilted (E_s ω))) 2 P := by
      refine hdom_e.mono' hm_e.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
      have := hprob_ω ω
      rw [Real.norm_eq_abs]
      exact abs_integral_le_of_forall_abs_le _ fun x => by
        rw [abs_mul (1 / (2 * Real.sqrt (1 - s))), abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left
          ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
            rw [abs_mul, abs_mul, abs_units_cast_eq_one, one_mul,
              abs_of_nonneg (Real.sqrt_nonneg _)]))
          (by positivity)
    exact integrable_mul_pow_of_memLp hext_L2 m (hA_mem (2 * m))
  have hpt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      (∫ x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        ((∑ k : Fin M, S'_fn ω x k * deriv u (S_fn ω x k)) -
          (1 / (2 * Real.sqrt (1 - s))) *
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m =
      (∑ k : Fin M,
        (∫ x, S'_fn ω x k * deriv u (S_fn ω x k) ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m) -
      (∫ x, (1 / (2 * Real.sqrt (1 - s))) *
        (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * ω.2 i * Real.sqrt r)
        ∂(μ_s.tilted (E_s ω))) * (A ω - a) ^ m := by
    rw [integral_sub (integrable_finsetSum _ fun k _ => hS'_in_pt ω k) (hext_in_pt ω),
      integral_finsetSum _ fun k _ => hS'_in_pt ω k, sub_mul, Finset.sum_mul]
  simp_rw [hpt]
  rw [integral_sub (integrable_finsetSum _ fun k _ => hS'_in_P k) hext_in_P,
    integral_finsetSum _ fun k _ => hS'_in_P k]

private lemma regroup_fixed_center_ibp_terms
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (r a : ℝ) {s : ℝ} (hs0 : 0 ≤ s) (m : ℕ) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let S_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (j : Fin M) : ℝ :=
      Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j)
    let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ j : Fin M, u (S_fn ω x j)) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    let A (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s ω x) ∂μ_s)
    ((m + 1 : ℕ) : ℝ) *
      (((N : ℝ) + 1)⁻¹ *
        (∑ j : Fin M, (1 / 2) * ∫ ω,
          (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
            ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
              deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j)
            ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) *
          ((m : ℝ) * ((N : ℝ) + 1)⁻¹ * (A ω - a) ^ (m - 1) - (A ω - a) ^ m) ∂P) -
      (r / 2) * ∫ ω,
        ((1 - ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
            (((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ))
            ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) * (A ω - a) ^ m +
          (m : ℝ) * ((N : ℝ) + 1)⁻¹ *
            (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
              (((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ))
              ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) *
            (A ω - a) ^ (m - 1)) ∂P) =
    -(((m + 1 : ℕ) : ℝ) / 2) * ∫ ω,
        (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
            ((((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
              deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j)) - r)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) *
        (A ω - a) ^ m ∂P +
      (((m + 1 : ℕ) : ℝ) * (m : ℝ) / (2 * ((N : ℝ) + 1))) * ∫ ω,
        (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
            ((((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
              deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j)) - r)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) *
        (A ω - a) ^ (m - 1) ∂P -
      (((m + 1 : ℕ) : ℝ) * r * (1 - q) / 2) * ∫ ω, (A ω - a) ^ m ∂P -
      (r * q / (2 * ((N : ℝ) + 1)) * ((m + 1 : ℕ) : ℝ) * (m : ℝ)) *
        ∫ ω, (A ω - a) ^ (m - 1) ∂P := by
  intro P_g P_z P_z' P μ_s S_fn E_s A
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z']; infer_instance
  have hEm_joint := measurable_interpEnergy_joint (L := N + 1) (M := M) hu.measurable s q r
  have hprob_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      IsProbabilityMeasure (μ_s.tilted (E_s ω)) :=
    isProbabilityMeasure_tilted_interpEnergy (L := N + 1) hu.measurable (fun x => hu.le x) s q r ω
  have hA_mem (p : ℕ) : MemLp (fun ω => A ω - a) ((p : ℕ) : ℝ≥0) P :=
    (memLp_interp_log_partition_and_deriv (N := N) (M := M) hu.measurable hu.abs_le (D₁ := D₁)
      q r a 1 hs0 ((p : ℕ) : ℝ≥0)).2.2
  have hApow_int (p : ℕ) : Integrable (fun ω => (A ω - a) ^ p) P :=
    (integrable_pow_of_memLp p (hA_mem (max p 1))).1
  let R_obs (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
    ((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)
  have hR_obs_m : Measurable R_obs := by
    refine (Finset.measurable_sum _ fun i _ => ?_).const_mul _
    exact (measurable_units_cast.comp ((measurable_pi_apply i).comp
        (measurable_fst.comp (measurable_pi_apply 0)))).mul
      (measurable_units_cast.comp ((measurable_pi_apply i).comp
        (measurable_fst.comp (measurable_pi_apply 1))))
  have hR_obs_bd (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : |R_obs σ| ≤ 1 := by
    dsimp only [R_obs]
    rw [abs_mul, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    have hs_b : |∑ i : Fin (N + 1), (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)| ≤
        (N : ℝ) + 1 :=
      ((Finset.abs_sum_le_card_mul_of_abs_le _ (C := 1) fun i => by
        rw [abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, mul_one]).trans_eq (by simp))
    exact (inv_mul_le_iff₀ (by positivity)).2 (by linarith)
  let Q_j (j : Fin M) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
      (R_obs σ - q) * deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j)
      ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))
  have hQj_m (j : Fin M) : Measurable (Q_j j) := by
    let G_j (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (R_obs σ - q) * deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j)
    have hGm : Measurable fun p :
        (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
          (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => G_j p.1 p.2 :=
      (((hR_obs_m.comp measurable_snd).sub_const q).mul
        ((measurable_deriv u).comp
          (measurable_interpField_replica_joint (L := N + 1) (M := M) s q j 0))).mul
        ((measurable_deriv u).comp
          (measurable_interpField_replica_joint (L := N + 1) (M := M) s q j 1))
    exact measurable_integral_pi_tilted (μ := μ_s) (E := E_s) (G := G_j) hEm_joint hGm
  have hQj_bd (j : Fin M) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      |Q_j j ω| ≤ 2 * |D₁| ^ 2 := by
    have := hprob_ω ω
    exact abs_integral_le_of_forall_abs_le _ fun σ => by
      rw [abs_mul, abs_mul, sq]
      have hd_ov := abs_spin_overlap_sub_le_two hq (σ 0).1 (σ 1).1
      calc _ ≤ 2 * |D₁| * |D₁| :=
            mul_le_mul (mul_le_mul hd_ov (hu.abs_deriv_le_abs _)
              (abs_nonneg _) zero_le_two) (hu.abs_deriv_le_abs _)
              (abs_nonneg _) (by positivity)
        _ = 2 * (|D₁| * |D₁|) := by ring
  have hQj_L2 (j : Fin M) : MemLp (Q_j j) 2 P :=
    MemLp.of_bound (hQj_m j).aestronglyMeasurable (2 * |D₁| ^ 2)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hQj_bd j ω)
  let Q_ov (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
      R_obs σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))
  have hQov_m : Measurable Q_ov := by
    let G_ov (_ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ := R_obs σ
    exact measurable_integral_pi_tilted (μ := μ_s) (E := E_s) (G := G_ov) hEm_joint
      (hR_obs_m.comp measurable_snd)
  have hQov_bd (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      |Q_ov ω| ≤ 1 := by
    have := hprob_ω ω
    exact abs_integral_le_of_forall_abs_le _ hR_obs_bd
  have hQov_L2 : MemLp Q_ov 2 P :=
    MemLp.of_bound hQov_m.aestronglyMeasurable 1
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hQov_bd ω)
  let Q_ab (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
    ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
      (R_obs σ - q) *
        ((((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
          deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j)) - r)
      ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))
  have hQab_eq (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Q_ab ω = ((N : ℝ) + 1)⁻¹ * (∑ j : Fin M, Q_j j ω) - r * (Q_ov ω - q) := by
    have := hprob_ω ω
    have hj_in (j : Fin M) : Integrable
        (fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
          (R_obs σ - q) * deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j))
        (Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) := by
      have hS_l (l : Fin 2) : Measurable fun σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
          S_fn ω (σ l) j := by dsimp only [S_fn]; fun_prop
      exact Integrable.of_bound
        (((hR_obs_m.sub_const q).mul ((measurable_deriv u).comp (hS_l 0))).mul
          ((measurable_deriv u).comp (hS_l 1))).aestronglyMeasurable
        (2 * |D₁| ^ 2) (ae_of_all _ fun σ => by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, sq]
          have hd_ov := abs_spin_overlap_sub_le_two hq (σ 0).1 (σ 1).1
          calc _ ≤ 2 * |D₁| * |D₁| :=
                mul_le_mul (mul_le_mul hd_ov (hu.abs_deriv_le_abs _)
                  (abs_nonneg _) zero_le_two) (hu.abs_deriv_le_abs _)
                  (abs_nonneg _) (by positivity)
            _ = 2 * (|D₁| * |D₁|) := by ring)
    have hov_in : Integrable R_obs (Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) :=
      Integrable.of_bound hR_obs_m.aestronglyMeasurable 1
        (ae_of_all _ fun σ => by rw [Real.norm_eq_abs]; exact hR_obs_bd σ)
    have hpt (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        (R_obs σ - q) *
          ((((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
            deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j)) - r) =
        ((N : ℝ) + 1)⁻¹ *
          (∑ j : Fin M, (R_obs σ - q) * deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j)) -
        r * (R_obs σ - q) := by
      rw [mul_sub, ← mul_assoc, mul_comm (R_obs σ - q) (((N : ℝ) + 1)⁻¹), mul_assoc,
        Finset.mul_sum]
      refine congrArg₂ (· - ·)
        (congrArg _ (Finset.sum_congr rfl fun _ _ => by ring)) (mul_comm _ _)
    dsimp only [Q_ab]
    simp_rw [hpt]
    rw [integral_sub (f := fun σ => ((N : ℝ) + 1)⁻¹ *
          ∑ j : Fin M, (R_obs σ - q) * deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j))
        (g := fun σ => r * (R_obs σ - q))
        ((integrable_finsetSum _ fun j _ => hj_in j).const_mul _)
        ((hov_in.sub (integrable_const q)).const_mul r),
      integral_const_mul, integral_finsetSum _ fun j _ => hj_in j,
      integral_const_mul, integral_sub (f := R_obs) (g := fun _ => q) hov_in (integrable_const q),
      integral_const, probReal_univ, one_smul]
  have hQab_L2 : MemLp Q_ab 2 P := by
    rw [funext hQab_eq]
    exact ((memLp_finsetSum Finset.univ fun j _ => hQj_L2 j).const_mul _).sub
      ((hQov_L2.sub (memLp_const q)).const_mul r)
  have hint_Qj (j : Fin M) (p : ℕ) : Integrable (fun ω => Q_j j ω * (A ω - a) ^ p) P :=
    integrable_mul_pow_of_memLp (hQj_L2 j) p (hA_mem (2 * p))
  have hint_Qov (p : ℕ) : Integrable (fun ω => Q_ov ω * (A ω - a) ^ p) P :=
    integrable_mul_pow_of_memLp hQov_L2 p (hA_mem (2 * p))
  have hint_Qab (p : ℕ) : Integrable (fun ω => Q_ab ω * (A ω - a) ^ p) P :=
    integrable_mul_pow_of_memLp hQab_L2 p (hA_mem (2 * p))
  have hsum_j :
      (∑ j : Fin M, (1 / 2) * ∫ ω, Q_j j ω *
        ((m : ℝ) * ((N : ℝ) + 1)⁻¹ * (A ω - a) ^ (m - 1) - (A ω - a) ^ m) ∂P) =
      (1 / 2) * ((m : ℝ) * ((N : ℝ) + 1)⁻¹ *
        (∑ j : Fin M, ∫ ω, Q_j j ω * (A ω - a) ^ (m - 1) ∂P) -
        ∑ j : Fin M, ∫ ω, Q_j j ω * (A ω - a) ^ m ∂P) := by
    have hj (j : Fin M) :
        ∫ ω, Q_j j ω * ((m : ℝ) * ((N : ℝ) + 1)⁻¹ * (A ω - a) ^ (m - 1) - (A ω - a) ^ m) ∂P =
        (m : ℝ) * ((N : ℝ) + 1)⁻¹ * (∫ ω, Q_j j ω * (A ω - a) ^ (m - 1) ∂P) -
          ∫ ω, Q_j j ω * (A ω - a) ^ m ∂P := by
      have hpt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
          Q_j j ω * ((m : ℝ) * ((N : ℝ) + 1)⁻¹ * (A ω - a) ^ (m - 1) - (A ω - a) ^ m) =
          (m : ℝ) * ((N : ℝ) + 1)⁻¹ * (Q_j j ω * (A ω - a) ^ (m - 1)) -
            Q_j j ω * (A ω - a) ^ m := by ring
      simp_rw [hpt]
      rw [integral_sub ((hint_Qj j (m - 1)).const_mul _) (hint_Qj j m), integral_const_mul]
    simp_rw [hj, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hext_split :
      (∫ ω, ((1 - Q_ov ω) * (A ω - a) ^ m +
        (m : ℝ) * ((N : ℝ) + 1)⁻¹ * Q_ov ω * (A ω - a) ^ (m - 1)) ∂P) =
      (∫ ω, (A ω - a) ^ m ∂P) - (∫ ω, Q_ov ω * (A ω - a) ^ m ∂P) +
        (m : ℝ) * ((N : ℝ) + 1)⁻¹ * ∫ ω, Q_ov ω * (A ω - a) ^ (m - 1) ∂P := by
    have hpt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
        (1 - Q_ov ω) * (A ω - a) ^ m +
          (m : ℝ) * ((N : ℝ) + 1)⁻¹ * Q_ov ω * (A ω - a) ^ (m - 1) =
        ((A ω - a) ^ m - Q_ov ω * (A ω - a) ^ m) +
          (m : ℝ) * ((N : ℝ) + 1)⁻¹ * (Q_ov ω * (A ω - a) ^ (m - 1)) := by ring
    simp_rw [hpt]
    rw [integral_add (f := fun ω => (A ω - a) ^ m - Q_ov ω * (A ω - a) ^ m)
        (g := fun ω => (m : ℝ) * ((N : ℝ) + 1)⁻¹ * (Q_ov ω * (A ω - a) ^ (m - 1)))
        ((hApow_int m).sub (hint_Qov m)) ((hint_Qov (m - 1)).const_mul _),
      integral_sub (f := fun ω => (A ω - a) ^ m) (g := fun ω => Q_ov ω * (A ω - a) ^ m)
        (hApow_int m) (hint_Qov m),
      integral_const_mul]
  have hQab_int (p : ℕ) :
      ∫ ω, Q_ab ω * (A ω - a) ^ p ∂P =
        ((N : ℝ) + 1)⁻¹ * (∑ j : Fin M, ∫ ω, Q_j j ω * (A ω - a) ^ p ∂P) -
          r * ((∫ ω, Q_ov ω * (A ω - a) ^ p ∂P) - q * ∫ ω, (A ω - a) ^ p ∂P) := by
    have hpt (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
        Q_ab ω * (A ω - a) ^ p =
        ((N : ℝ) + 1)⁻¹ * (∑ j : Fin M, Q_j j ω * (A ω - a) ^ p) -
          r * (Q_ov ω * (A ω - a) ^ p - q * (A ω - a) ^ p) := by
      rw [hQab_eq ω, sub_mul, mul_assoc, Finset.sum_mul]
      congr 1; ring
    simp_rw [hpt]
    rw [integral_sub (f := fun ω => ((N : ℝ) + 1)⁻¹ * ∑ j : Fin M, Q_j j ω * (A ω - a) ^ p)
        (g := fun ω => r * (Q_ov ω * (A ω - a) ^ p - q * (A ω - a) ^ p))
        ((integrable_finsetSum _ fun j _ => hint_Qj j p).const_mul _)
        (((hint_Qov p).sub ((hApow_int p).const_mul q)).const_mul r),
      integral_const_mul, integral_finsetSum _ fun j _ => hint_Qj j p,
      integral_const_mul,
      integral_sub (f := fun ω => Q_ov ω * (A ω - a) ^ p)
        (g := fun ω => q * (A ω - a) ^ p) (hint_Qov p) ((hApow_int p).const_mul q),
      integral_const_mul]
  change ((m + 1 : ℕ) : ℝ) *
      (((N : ℝ) + 1)⁻¹ *
        (∑ j : Fin M, (1 / 2) * ∫ ω, Q_j j ω *
          ((m : ℝ) * ((N : ℝ) + 1)⁻¹ * (A ω - a) ^ (m - 1) - (A ω - a) ^ m) ∂P) -
      (r / 2) * ∫ ω, ((1 - Q_ov ω) * (A ω - a) ^ m +
        (m : ℝ) * ((N : ℝ) + 1)⁻¹ * Q_ov ω * (A ω - a) ^ (m - 1)) ∂P) =
    -(((m + 1 : ℕ) : ℝ) / 2) * (∫ ω, Q_ab ω * (A ω - a) ^ m ∂P) +
      (((m + 1 : ℕ) : ℝ) * (m : ℝ) / (2 * ((N : ℝ) + 1))) *
        (∫ ω, Q_ab ω * (A ω - a) ^ (m - 1) ∂P) -
      (((m + 1 : ℕ) : ℝ) * r * (1 - q) / 2) * (∫ ω, (A ω - a) ^ m ∂P) -
      (r * q / (2 * ((N : ℝ) + 1)) * ((m + 1 : ℕ) : ℝ) * (m : ℝ)) *
        ∫ ω, (A ω - a) ^ (m - 1) ∂P
  rw [hsum_j, hext_split, hQab_int m, hQab_int (m - 1)]
  have hL : ((N : ℝ) + 1) ≠ 0 := by positivity
  generalize (∑ j : Fin M, ∫ ω, Q_j j ω * (A ω - a) ^ m ∂P) = SJ_m
  generalize (∑ j : Fin M, ∫ ω, Q_j j ω * (A ω - a) ^ (m - 1) ∂P) = SJ_m1
  generalize (∫ ω, Q_ov ω * (A ω - a) ^ m ∂P) = SO_m
  generalize (∫ ω, Q_ov ω * (A ω - a) ^ (m - 1) ∂P) = SO_m1
  generalize (∫ ω, (A ω - a) ^ m ∂P) = SA_m
  generalize (∫ ω, (A ω - a) ^ (m - 1) ∂P) = SA_m1
  field_simp
  ring

private theorem hasDerivAt_interpolating_fixed_center_pow_regrouped
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) {r : ℝ} (hr0 : 0 ≤ r) (a : ℝ)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) (m : ℕ) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let S_fn (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (j : Fin M) : ℝ :=
      Real.sqrt s' * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s') * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j)
    let E_s (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ j : Fin M, u (S_fn s' ω x j)) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s') * ω.2 i * Real.sqrt r
    let A (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s s' ω x) ∂μ_s)
    HasDerivAt (fun s' => ∫ ω, (A s' ω - a) ^ m ∂P)
      (-((m : ℝ) / 2) * ∫ ω,
          (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
            ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
              ((((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
                deriv u (S_fn s ω (σ 0) j) * deriv u (S_fn s ω (σ 1) j)) - r)
            ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) *
          (A s ω - a) ^ (m - 1) ∂P +
        ((m : ℝ) * ((m : ℝ) - 1) / (2 * ((N : ℝ) + 1))) * ∫ ω,
          (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
            ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
              ((((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
                deriv u (S_fn s ω (σ 0) j) * deriv u (S_fn s ω (σ 1) j)) - r)
            ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) *
          (A s ω - a) ^ (m - 2) ∂P -
        ((m : ℝ) * r * (1 - q) / 2) * ∫ ω, (A s ω - a) ^ (m - 1) ∂P -
        (r * q / (2 * ((N : ℝ) + 1)) * (m : ℝ) * ((m : ℝ) - 1)) *
          ∫ ω, (A s ω - a) ^ (m - 2) ∂P) s := by
  intro P_g P_z P_z' P μ_s S_fn E_s A
  have hd_raw := hasDerivAt_interpolating_fixed_center_pow_raw (N := N) (M := M)
    hu.differentiable hu.abs_le hu.abs_deriv_le q r a hs m
  rcases m with _ | m
  · refine hd_raw.congr_deriv ?_
    simp
  refine hd_raw.congr_deriv ?_
  have hsplit := integral_interpolating_fixed_center_deriv_split (N := N) (M := M)
    hu q r a hs.1.le m
  have hext := integral_interpolating_external_field_ibp_pow (N := N) (M := M)
    hu.measurable hu.abs_le q hr0 a hs.1.le hs.2 m
  have hfield (j : Fin M) := integral_interpolating_field_deriv_ibp_pow (N := N) (M := M)
    hu hq r a hs m j
  have hcomb := regroup_fixed_center_ibp_terms (N := N) (M := M) hu hq r a hs.1.le m
  dsimp only [P, P_g, P_z, P_z', μ_s, S_fn, E_s, A] at *
  simp only [Nat.add_sub_cancel, show m + 1 - 2 = m - 1 by omega]
  rw [mul_assoc, hsplit, mul_sub, hext, Finset.sum_congr rfl fun j _ => hfield j, hcomb]
  push_cast
  ring

/-- **Talagrand Section 2.5, Eqs. (2.107)--(2.108): centered-moment ODE along `s`.**
Let `A(s', ω) = (N + 1)⁻¹ log ∫ exp(E_s(s', ω, x)) dμ_s` and
`RS(s') = perceptronRSFunctional u (M / (N + 1)) r q + ((1 - s') / 2) * r * (1 - q)`, with
`V(s', ω) = A(s', ω) - RS(s')`. Under `SmartPathPotential₂`, `q ∈ [0, 1]`, and `r ≥ 0` (with no
fixed-point or small-load hypotheses), for every `s ∈ (0, 1)` and `k : ℕ`,
`d/ds 𝔼[V(s)^k] = VII + VIII + IX`, where
- `VII = -(k / 2) 𝔼[⟨(R_{1,2} - q)((N + 1)⁻¹ ∑_j u'(S^1_{j,s}) u'(S^2_{j,s}) - r)⟩_s V(s)^{k-1}]`,
- `VIII = (k(k - 1) / (2(N + 1)))` times
  `𝔼[⟨(R_{1,2} - q)((N + 1)⁻¹ ∑_j u'(S^1_{j,s}) u'(S^2_{j,s}) - r)⟩_s V(s)^{k-2}]`,
- `IX = -(r q / (2(N + 1))) k(k - 1) 𝔼[V(s)^{k-2}]`. -/
theorem hasDerivAt_interpolating_centered_moment_pow
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) {r : ℝ} (hr0 : 0 ≤ r) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    (k : ℕ) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let S_fn (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (j : Fin M) : ℝ :=
      Real.sqrt s' * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s') * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j)
    let E_s (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ j : Fin M, u (S_fn s' ω x j)) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s') * ω.2 i * Real.sqrt r
    let A (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s s' ω x) ∂μ_s)
    let RS (s' : ℝ) : ℝ :=
      perceptronRSFunctional u ((M : ℝ) / ((N : ℝ) + 1)) r q + ((1 - s') / 2) * r * (1 - q)
    let V (s' : ℝ) (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
      A s' ω - RS s'
    HasDerivAt (fun s' => ∫ ω, V s' ω ^ k ∂P)
      ((-(k : ℝ) / 2 * ∫ ω,
          (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
            ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
              ((((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
                deriv u (S_fn s ω (σ 0) j) * deriv u (S_fn s ω (σ 1) j)) - r)
            ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) *
          V s ω ^ (k - 1) ∂P) +
        ((k : ℝ) * ((k : ℝ) - 1) / (2 * ((N : ℝ) + 1)) * ∫ ω,
          (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
            ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
              ((((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
                deriv u (S_fn s ω (σ 0) j) * deriv u (S_fn s ω (σ 1) j)) - r)
            ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) *
          V s ω ^ (k - 2) ∂P) +
        (-(r * q / (2 * ((N : ℝ) + 1))) * (k : ℝ) * ((k : ℝ) - 1) *
          ∫ ω, V s ω ^ (k - 2) ∂P)) s := by
  intro P_g P_z P_z' P μ_s S_fn E_s A RS V
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z']; infer_instance
  let a0 := RS s
  let φ (m : ℕ) (s' : ℝ) : ℝ := ∫ ω, (A s' ω - a0) ^ m ∂P
  let z (s' : ℝ) : ℝ := a0 - RS s'
  let D_m (m : ℕ) : ℝ :=
    -((m : ℝ) / 2) * ∫ ω,
        (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
            ((((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
              deriv u (S_fn s ω (σ 0) j) * deriv u (S_fn s ω (σ 1) j)) - r)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) *
        (A s ω - a0) ^ (m - 1) ∂P +
      ((m : ℝ) * ((m : ℝ) - 1) / (2 * ((N : ℝ) + 1))) * ∫ ω,
        (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
            ((((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
              deriv u (S_fn s ω (σ 0) j) * deriv u (S_fn s ω (σ 1) j)) - r)
          ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s s ω))) *
        (A s ω - a0) ^ (m - 2) ∂P -
      ((m : ℝ) * r * (1 - q) / 2) * ∫ ω, (A s ω - a0) ^ (m - 1) ∂P -
      (r * q / (2 * ((N : ℝ) + 1)) * (m : ℝ) * ((m : ℝ) - 1)) *
        ∫ ω, (A s ω - a0) ^ (m - 2) ∂P
  have hD (m : ℕ) : HasDerivAt (φ m) (D_m m) s :=
    hasDerivAt_interpolating_fixed_center_pow_regrouped (N := N) (M := M) hu hq hr0 a0 hs m
  have hz' : HasDerivAt z (r * (1 - q) / 2) s := by
    have hRS : HasDerivAt RS (-(r * (1 - q) / 2)) s := by
      have h1 : HasDerivAt (fun s' : ℝ => 1 - s') (-1) s := (hasDerivAt_id s).const_sub 1
      exact ((((h1.div_const 2).mul_const r).mul_const (1 - q)).const_add _).congr_deriv (by ring)
    exact (hRS.const_sub a0).congr_deriv (by ring)
  have hzs : z s = 0 := sub_self _
  have hint {s' : ℝ} (hs'0 : 0 ≤ s') (m : ℕ) : Integrable (fun ω => (A s' ω - a0) ^ m) P :=
    (integrable_pow_of_memLp m
      ((memLp_interp_log_partition_and_deriv (N := N) (M := M) hu.measurable hu.abs_le (D₁ := D₁)
        q r a0 1 hs'0 ((max m 1 : ℕ) : ℝ≥0)).2.2)).1
  have hsum_eq :
      (fun s' => ∫ ω, V s' ω ^ k ∂P) =ᶠ[𝓝 s]
      (fun s' => ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (z s' ^ i * φ (k - i) s')) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with s' hs'
    have e (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
        V s' ω ^ k =
          ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (z s' ^ i * (A s' ω - a0) ^ (k - i)) := by
      have hV : V s' ω = z s' + (A s' ω - a0) := by dsimp only [V, z]; ring
      rw [hV, add_pow]
      exact Finset.sum_congr rfl fun _ _ => by ring
    simp_rw [e]
    rw [integral_finsetSum _ fun i _ =>
      ((hint hs'.1.le (k - i)).const_mul (z s' ^ i)).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_const_mul]
  have hder : HasDerivAt
      (fun s' => ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (z s' ^ i * φ (k - i) s'))
      (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        (((i : ℝ) * z s ^ (i - 1) * (r * (1 - q) / 2)) * φ (k - i) s + z s ^ i * D_m (k - i))) s :=
    HasDerivAt.fun_sum fun i _ => ((hz'.pow i).mul (hD (k - i))).const_mul _
  refine (hder.congr_of_eventuallyEq hsum_eq).congr_deriv ?_
  simp only [hzs]
  rw [Finset.sum_choose_mul_deriv_pow_zero k (r * (1 - q) / 2) (fun m => φ m s) D_m]
  dsimp only [D_m, φ, a0, V]
  ring

/-! ### Section 4: A priori bounds on free-energy fluctuations via Grönwall (2.109)--(2.110) -/

private lemma rpow_inv_integral_abs_pow_gibbs_mul_le
    {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Ω → Measure Z} [∀ ω, IsProbabilityMeasure (ν ω)]
    {A B : Ω → Z → ℝ}
    {M_A M_B : ℝ} (hA_bd : ∀ ω z, |A ω z| ≤ M_A) (hB_bd : ∀ ω z, |B ω z| ≤ M_B)
    (hQ_m : AEStronglyMeasurable (fun ω => ∫ z, A ω z * B ω z ∂ν ω) P)
    {k : ℕ} (hk : 1 ≤ k)
    (hA_m : ∀ ω, AEStronglyMeasurable (A ω) (ν ω))
    (hB_m : ∀ ω, AEStronglyMeasurable (B ω) (ν ω))
    (hA2k_P : Integrable (fun ω => ∫ z, A ω z ^ (2 * k) ∂ν ω) P)
    (hB2k_P : Integrable (fun ω => ∫ z, B ω z ^ (2 * k) ∂ν ω) P) :
    (∫ ω, |∫ z, A ω z * B ω z ∂ν ω| ^ k ∂P) ^ (1 / (k : ℝ)) ≤
      (∫ ω, ∫ z, A ω z ^ (2 * k) ∂ν ω ∂P) ^ (1 / (2 * (k : ℝ))) *
        (∫ ω, ∫ z, B ω z ^ (2 * k) ∂ν ω ∂P) ^ (1 / (2 * (k : ℝ))) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  let MA := max M_A 0
  let MB := max M_B 0
  have hMA0 : 0 ≤ MA := le_max_right _ _
  have hMB0 : 0 ≤ MB := le_max_right _ _
  have hQ_bd (ω : Ω) : |∫ z, A ω z * B ω z ∂ν ω| ≤ MA * MB :=
    abs_integral_le_of_forall_abs_le _ fun z => by
      rw [abs_mul]
      exact mul_le_mul ((hA_bd ω z).trans (le_max_left _ _))
        ((hB_bd ω z).trans (le_max_left _ _)) (abs_nonneg _) hMA0
  have hQk_int : Integrable (fun ω => |∫ z, A ω z * B ω z ∂ν ω| ^ k) P :=
    Integrable.of_bound (hQ_m.norm.pow k) ((MA * MB) ^ k) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hQ_bd ω) k)
  have hpt_ω (ω : Ω) :
      |∫ z, A ω z * B ω z ∂ν ω| ^ k ≤
        (∫ z, A ω z ^ (2 * k) ∂ν ω) ^ (1 / (2 : ℝ)) *
          (∫ z, B ω z ^ (2 * k) ∂ν ω) ^ (1 / (2 : ℝ)) := by
    have hAB : MemLp (fun z => A ω z * B ω z) (k : ℕ) (ν ω) :=
      MemLp.of_bound ((hA_m ω).mul (hB_m ω)) (MA * MB) (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul ((hA_bd ω z).trans (le_max_left _ _))
          ((hB_bd ω z).trans (le_max_left _ _)) (abs_nonneg _) hMA0)
    have hJ : |∫ z, A ω z * B ω z ∂ν ω| ^ k ≤ ∫ z, |A ω z| ^ k * |B ω z| ^ k ∂ν ω := by
      simpa only [Real.norm_eq_abs, ENNReal.toReal_natCast, Real.rpow_natCast, abs_mul, mul_pow]
        using norm_integral_rpow_le_integral_norm_rpow (p := (k : ℕ))
          (by exact_mod_cast hk) (by simp) hAB
    have hLp {f : Z → ℝ} (hf : AEStronglyMeasurable f (ν ω))
        {C : ℝ} (hC : ∀ z, |f z| ≤ C) :
        MemLp (fun z => |f z| ^ k) (ENNReal.ofReal 2) (ν ω) :=
      MemLp.of_bound (hf.norm.pow k) (C ^ k) (ae_of_all _ fun z => by
        rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hC z) k)
    have hCS := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
      (hLp (C := MA) (hA_m ω) fun z => (hA_bd ω z).trans (le_max_left _ _))
      (hLp (C := MB) (hB_m ω) fun z => (hB_bd ω z).trans (le_max_left _ _))
    have habs (x : ℝ) : ‖|x| ^ k‖ = |x| ^ k := Real.norm_of_nonneg (by positivity)
    have hpow (x : ℝ) : (|x| ^ k) ^ (2 : ℝ) = x ^ (2 * k) := by
      rw [Real.rpow_two, ← pow_mul, Nat.mul_comm k 2, pow_mul, sq_abs, ← pow_mul]
    simp_rw [habs, hpow] at hCS
    exact hJ.trans hCS
  have hA2k_0 (ω : Ω) : 0 ≤ ∫ z, A ω z ^ (2 * k) ∂ν ω :=
    integral_nonneg fun _ => Even.pow_nonneg ⟨k, by ring⟩ _
  have hB2k_0 (ω : Ω) : 0 ≤ ∫ z, B ω z ^ (2 * k) ∂ν ω :=
    integral_nonneg fun _ => Even.pow_nonneg ⟨k, by ring⟩ _
  have hLA : MemLp (fun ω => (∫ z, A ω z ^ (2 * k) ∂ν ω) ^ (1 / (2 : ℝ))) (ENNReal.ofReal 2) P :=
    MeasureTheory.memLp_rpow_inv_of_integrable zero_lt_two hA2k_0 hA2k_P
  have hLB : MemLp (fun ω => (∫ z, B ω z ^ (2 * k) ∂ν ω) ^ (1 / (2 : ℝ))) (ENNReal.ofReal 2) P :=
    MeasureTheory.memLp_rpow_inv_of_integrable zero_lt_two hB2k_0 hB2k_P
  have hLP_prod : Integrable
      (fun ω => (∫ z, A ω z ^ (2 * k) ∂ν ω) ^ (1 / (2 : ℝ)) *
        (∫ z, B ω z ^ (2 * k) ∂ν ω) ^ (1 / (2 : ℝ))) P := by
    have hLA2 : MemLp (fun ω => (∫ z, A ω z ^ (2 * k) ∂ν ω) ^ (1 / (2 : ℝ))) 2 P := by
      simpa using hLA
    have hLB2 : MemLp (fun ω => (∫ z, B ω z ^ (2 * k) ∂ν ω) ^ (1 / (2 : ℝ))) 2 P := by
      simpa using hLB
    exact hLA2.integrable_mul hLB2
  have hP_cs : ∫ ω, |∫ z, A ω z * B ω z ∂ν ω| ^ k ∂P ≤
      (∫ ω, ∫ z, A ω z ^ (2 * k) ∂ν ω ∂P) ^ (1 / (2 : ℝ)) *
        (∫ ω, ∫ z, B ω z ^ (2 * k) ∂ν ω ∂P) ^ (1 / (2 : ℝ)) := by
    refine (integral_mono hQk_int hLP_prod hpt_ω).trans ?_
    refine (integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (ae_of_all _ fun ω => Real.rpow_nonneg (hA2k_0 ω) _)
      (ae_of_all _ fun ω => Real.rpow_nonneg (hB2k_0 ω) _) hLA hLB).trans_eq ?_
    congr 2 <;> refine integral_congr_ae (ae_of_all _ fun ω => ?_) <;> dsimp only
    · rw [← Real.rpow_mul (hA2k_0 ω), one_div_mul_cancel two_ne_zero, Real.rpow_one]
    · rw [← Real.rpow_mul (hB2k_0 ω), one_div_mul_cancel two_ne_zero, Real.rpow_one]
  have hIA0 : 0 ≤ ∫ ω, ∫ z, A ω z ^ (2 * k) ∂ν ω ∂P := integral_nonneg hA2k_0
  have hIB0 : 0 ≤ ∫ ω, ∫ z, B ω z ^ (2 * k) ∂ν ω ∂P := integral_nonneg hB2k_0
  calc (∫ ω, |∫ z, A ω z * B ω z ∂ν ω| ^ k ∂P) ^ (1 / (k : ℝ))
      ≤ ((∫ ω, ∫ z, A ω z ^ (2 * k) ∂ν ω ∂P) ^ (1 / (2 : ℝ)) *
          (∫ ω, ∫ z, B ω z ^ (2 * k) ∂ν ω ∂P) ^ (1 / (2 : ℝ))) ^ (1 / (k : ℝ)) :=
        Real.rpow_le_rpow (integral_nonneg fun _ => by positivity) hP_cs (by positivity)
    _ = (∫ ω, ∫ z, A ω z ^ (2 * k) ∂ν ω ∂P) ^ (1 / (2 * (k : ℝ))) *
          (∫ ω, ∫ z, B ω z ^ (2 * k) ∂ν ω ∂P) ^ (1 / (2 * (k : ℝ))) := by
        rw [Real.mul_rpow (Real.rpow_nonneg hIA0 _) (Real.rpow_nonneg hIB0 _),
          ← Real.rpow_mul hIA0, ← Real.rpow_mul hIB0]
        congr 2 <;> field_simp

private lemma abs_integral_mul_pow_le_rpow_inv_mul_rpow_div
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Q V : Ω → ℝ} {M_Q : ℝ} (hQ_bd : ∀ ω, |Q ω| ≤ M_Q)
    (hQ_m : AEStronglyMeasurable Q P) (hV_m : AEStronglyMeasurable V P)
    {k m : ℕ} (hmk : m < k)
    (hVk : Integrable (fun ω => |V ω| ^ k) P) :
    |∫ ω, Q ω * V ω ^ m ∂P| ≤
      (∫ ω, |Q ω| ^ k ∂P) ^ (1 / (k : ℝ)) *
        (∫ ω, |V ω| ^ k ∂P) ^ ((m : ℝ) / (k : ℝ)) := by
  have hk1 : 1 ≤ k := by omega
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.2 hk1
  let MQ := max M_Q 0
  have hMQ0 : 0 ≤ MQ := le_max_right _ _
  have hQ_le (ω : Ω) : |Q ω| ≤ MQ := (hQ_bd ω).trans (le_max_left _ _)
  have hQk_int : Integrable (fun ω => |Q ω| ^ k) P :=
    Integrable.of_bound (hQ_m.norm.pow k) (MQ ^ k) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hQ_le ω) k)
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · simp only [pow_zero, mul_one, Nat.cast_zero, zero_div, Real.rpow_zero, mul_one]
    have hQ1_int : Integrable (fun ω => |Q ω|) P :=
      Integrable.of_bound hQ_m.norm MQ (ae_of_all _ fun ω => by
        rw [Real.norm_of_nonneg (abs_nonneg _)]; exact hQ_le ω)
    have hjen : (∫ ω, |Q ω| ∂P) ^ k ≤ ∫ ω, |Q ω| ^ k ∂P :=
      (convexOn_pow k).map_integral_le (continuous_pow k).continuousOn isClosed_Ici
        (ae_of_all _ fun ω => (abs_nonneg (Q ω) : |Q ω| ∈ Ici (0 : ℝ))) hQ1_int hQk_int
    have hI0 : 0 ≤ ∫ ω, |Q ω| ∂P := integral_nonneg fun _ => abs_nonneg _
    calc |∫ ω, Q ω ∂P| ≤ ∫ ω, |Q ω| ∂P := abs_integral_le_integral_abs
      _ = ((∫ ω, |Q ω| ∂P) ^ k) ^ (1 / (k : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hI0, mul_one_div_cancel hk_pos.ne',
            Real.rpow_one]
      _ ≤ (∫ ω, |Q ω| ^ k ∂P) ^ (1 / (k : ℝ)) :=
          Real.rpow_le_rpow (pow_nonneg hI0 k) hjen (by positivity)
  · let r : ℕ := k - m
    have hr1 : 1 ≤ r := by omega
    have hr_pos : (0 : ℝ) < r := Nat.cast_pos.2 hr1
    have hm_pos_r : (0 : ℝ) < m := Nat.cast_pos.2 hm_pos
    have hr_eq : (r : ℝ) = (k : ℝ) - (m : ℝ) := Nat.cast_sub hmk.le
    let p : ℝ := (k : ℝ) / (r : ℝ)
    let q_exp : ℝ := (k : ℝ) / (m : ℝ)
    have hp1 : 1 < p := (one_lt_div hr_pos).2 (by rw [hr_eq]; linarith)
    have hpq : p.HolderConjugate q_exp := by
      rw [Real.holderConjugate_iff]
      refine ⟨hp1, ?_⟩
      dsimp only [p, q_exp]
      rw [inv_div, inv_div, hr_eq]
      field_simp; ring
    have hLQ : MemLp Q (ENNReal.ofReal p) P :=
      MemLp.of_bound hQ_m MQ (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hQ_le ω)
    have hLVm : MemLp (fun ω => |V ω| ^ m) (ENNReal.ofReal q_exp) P := by
      have hm_vm : AEStronglyMeasurable (fun ω => |V ω| ^ m) P := hV_m.norm.pow m
      refine (integrable_norm_rpow_iff hm_vm (by positivity) ENNReal.ofReal_ne_top).mp ?_
      rw [ENNReal.toReal_ofReal hpq.symm.pos.le]
      refine hVk.congr (ae_of_all _ fun ω => ?_)
      dsimp only
      rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_natCast (|V ω|) m,
        ← Real.rpow_mul (abs_nonneg _)]
      have hmq : (m : ℝ) * q_exp = (k : ℝ) := by dsimp only [q_exp]; field_simp
      rw [hmq, Real.rpow_natCast]
    have hhold := integral_mul_norm_le_Lp_mul_Lq hpq hLQ hLVm
    have h1 : |∫ ω, Q ω * V ω ^ m ∂P| ≤
        (∫ ω, |Q ω| ^ p ∂P) ^ (1 / p) * (∫ ω, |V ω| ^ k ∂P) ^ ((m : ℝ) / (k : ℝ)) := by
      refine abs_integral_le_integral_abs.trans ?_
      have heq : (fun ω => |Q ω * V ω ^ m|) = fun ω => ‖Q ω‖ * ‖|V ω| ^ m‖ :=
        funext fun ω => by
          rw [abs_mul, abs_pow, Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
      rw [heq]
      refine hhold.trans_eq ?_
      have heqQ : (fun ω => ‖Q ω‖ ^ p) = fun ω => |Q ω| ^ p :=
        funext fun _ => by rw [Real.norm_eq_abs]
      have heqV : (fun ω => ‖|V ω| ^ m‖ ^ q_exp) = fun ω => |V ω| ^ k :=
        funext fun ω => by
          rw [Real.norm_of_nonneg (by positivity), ← Real.rpow_natCast (|V ω|) m,
            ← Real.rpow_mul (abs_nonneg _)]
          have hmq : (m : ℝ) * q_exp = (k : ℝ) := by dsimp only [q_exp]; field_simp
          rw [hmq, Real.rpow_natCast]
      have h1q : 1 / q_exp = (m : ℝ) / (k : ℝ) := by dsimp only [q_exp]; field_simp
      simp_rw [heqQ, heqV, h1q]
    refine h1.trans (mul_le_mul_of_nonneg_right ?_
      (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _))
    have hQp_int : Integrable (fun ω => |Q ω| ^ p) P := by
      have h := hLQ.integrable_norm_rpow (by positivity) ENNReal.ofReal_ne_top
      rw [ENNReal.toReal_ofReal hpq.pos.le] at h
      simpa only [Real.norm_eq_abs] using h
    have hpr_eq (ω : Ω) : (|Q ω| ^ p) ^ r = |Q ω| ^ k := by
      rw [← Real.rpow_natCast (|Q ω| ^ p) r, ← Real.rpow_mul (abs_nonneg _)]
      have hpr : p * (r : ℝ) = (k : ℝ) := by dsimp only [p]; field_simp
      rw [hpr, Real.rpow_natCast]
    have hjen : (∫ ω, |Q ω| ^ p ∂P) ^ r ≤ ∫ ω, |Q ω| ^ k ∂P := by
      have hmap := (convexOn_pow r).map_integral_le (continuous_pow r).continuousOn isClosed_Ici
        (ae_of_all _ fun _ => Real.rpow_nonneg (abs_nonneg _) _) hQp_int
        (hQk_int.congr (ae_of_all _ fun ω => by
          dsimp only [Function.comp_apply]; exact (hpr_eq ω).symm))
      exact hmap.trans_eq (integral_congr_ae (ae_of_all _ fun ω => hpr_eq ω))
    have hIQp0 : 0 ≤ ∫ ω, |Q ω| ^ p ∂P :=
      integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
    calc (∫ ω, |Q ω| ^ p ∂P) ^ (1 / p)
        = ((∫ ω, |Q ω| ^ p ∂P) ^ r) ^ (1 / (k : ℝ)) := by
          rw [← Real.rpow_natCast _ r, ← Real.rpow_mul hIQp0]
          congr 1; dsimp only [p]; field_simp
      _ ≤ (∫ ω, |Q ω| ^ k ∂P) ^ (1 / (k : ℝ)) :=
          Real.rpow_le_rpow (pow_nonneg hIQp0 r) hjen (by positivity)

private lemma rpow_inv_two_mul_product_le
    {I_ov I_emp α L_emp L : ℝ} {k : ℕ} (hk : 1 ≤ k)
    (hL : 0 < L) (hL_emp : 0 ≤ L_emp) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hI_ov0 : 0 ≤ I_ov) (hI_emp0 : 0 ≤ I_emp)
    (h_ov : I_ov ≤ (64 * (k : ℝ) / L) ^ k)
    (h_emp : I_emp ≤ (α * (k : ℝ) * L_emp / L) ^ k) :
    I_ov ^ (1 / (2 * (k : ℝ))) * I_emp ^ (1 / (2 * (k : ℝ))) ≤
      Real.sqrt (64 * (k : ℝ) * ((k : ℝ) * L_emp)) / L := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have h1 : I_ov ^ (1 / (2 * (k : ℝ))) ≤ Real.sqrt (64 * (k : ℝ) / L) := by
    have hb0 : 0 ≤ 64 * (k : ℝ) / L := by positivity
    calc I_ov ^ (1 / (2 * (k : ℝ)))
        ≤ ((64 * (k : ℝ) / L) ^ k) ^ (1 / (2 * (k : ℝ))) :=
          Real.rpow_le_rpow hI_ov0 h_ov (by positivity)
      _ = (64 * (k : ℝ) / L) ^ (1 / (2 : ℝ)) := by
          rw [← Real.rpow_natCast _ k, ← Real.rpow_mul hb0]
          congr 1; field_simp
      _ = Real.sqrt (64 * (k : ℝ) / L) := (Real.sqrt_eq_rpow _).symm
  have h2 : I_emp ^ (1 / (2 * (k : ℝ))) ≤ Real.sqrt ((k : ℝ) * L_emp / L) := by
    have hα_le : α * (k : ℝ) * L_emp / L ≤ (k : ℝ) * L_emp / L := by
      refine div_le_div_of_nonneg_right ?_ hL.le
      calc α * (k : ℝ) * L_emp ≤ 1 * (k : ℝ) * L_emp :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hα1 hk_pos.le) hL_emp
        _ = (k : ℝ) * L_emp := by ring
    have hb0 : 0 ≤ (k : ℝ) * L_emp / L := by positivity
    calc I_emp ^ (1 / (2 * (k : ℝ)))
        ≤ (((k : ℝ) * L_emp / L) ^ k) ^ (1 / (2 * (k : ℝ))) :=
          Real.rpow_le_rpow hI_emp0
            (h_emp.trans (pow_le_pow_left₀ (by positivity) hα_le k)) (by positivity)
      _ = ((k : ℝ) * L_emp / L) ^ (1 / (2 : ℝ)) := by
          rw [← Real.rpow_natCast _ k, ← Real.rpow_mul hb0]
          congr 1; field_simp
      _ = Real.sqrt ((k : ℝ) * L_emp / L) := (Real.sqrt_eq_rpow _).symm
  calc I_ov ^ (1 / (2 * (k : ℝ))) * I_emp ^ (1 / (2 * (k : ℝ)))
      ≤ Real.sqrt (64 * (k : ℝ) / L) * Real.sqrt ((k : ℝ) * L_emp / L) :=
        mul_le_mul h1 h2 (Real.rpow_nonneg hI_emp0 _) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((64 * (k : ℝ) * ((k : ℝ) * L_emp)) / L ^ 2) := by
        rw [← Real.sqrt_mul (by positivity)]
        congr 1; ring
    _ = Real.sqrt (64 * (k : ℝ) * ((k : ℝ) * L_emp)) / L := by
        rw [Real.sqrt_div (by positivity), Real.sqrt_sq hL.le]

private lemma measurable_and_integrable_interp_pair_pow_moments
    {N M : ℕ} {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (r s : ℝ) (k : ℕ) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let S_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (j : Fin M) : ℝ :=
      Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j)
    let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ j : Fin M, u (S_fn ω x j)) +
        ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    let A_obs (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q
    let B_obs (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
        deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j)) - r
    (Measurable A_obs) ∧
    (∀ ω, Measurable (B_obs ω)) ∧
    (Measurable fun ω =>
      ∫ σ, A_obs σ * B_obs ω σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) ∧
    Integrable (fun ω =>
      ∫ σ, A_obs σ ^ (2 * k) ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) P ∧
    Integrable (fun ω =>
      ∫ σ, B_obs ω σ ^ (2 * k) ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) P := by
  intro P_g P_z P_z' P μ_s S_fn E_s A_obs B_obs
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z']; infer_instance
  have hEm_joint := measurable_interpEnergy_joint (L := N + 1) (M := M) hu.measurable s q r
  have hprob_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      IsProbabilityMeasure (μ_s.tilted (E_s ω)) :=
    isProbabilityMeasure_tilted_interpEnergy (L := N + 1) hu.measurable (fun x => hu.le x) s q r ω
  have hAm : Measurable A_obs := by
    refine ((Finset.measurable_sum _ fun i _ => ?_).const_mul _).sub_const q
    exact (measurable_units_cast.comp ((measurable_pi_apply i).comp
        (measurable_fst.comp (measurable_pi_apply 0)))).mul
      (measurable_units_cast.comp ((measurable_pi_apply i).comp
        (measurable_fst.comp (measurable_pi_apply 1))))
  have hBm_joint : Measurable fun p :
      (((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) ×
        (Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) => B_obs p.1 p.2 := by
    refine ((Finset.measurable_sum _ fun j _ => ?_).const_mul _).sub_const r
    exact ((measurable_deriv u).comp
      (measurable_interpField_replica_joint (L := N + 1) (M := M) s q j 0)).mul
      ((measurable_deriv u).comp
        (measurable_interpField_replica_joint (L := N + 1) (M := M) s q j 1))
  have hBm_slice (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      Measurable (B_obs ω) := Measurable.of_uncurry_left hBm_joint
  let G_AB (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ := A_obs σ * B_obs ω σ
  have hQ_m : Measurable fun ω =>
      ∫ σ, G_AB ω σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) :=
    measurable_integral_pi_tilted (μ := μ_s) (E := E_s) (G := G_AB) hEm_joint
      ((hAm.comp measurable_snd).mul hBm_joint)
  let G_A2k (_ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ := A_obs σ ^ (2 * k)
  have hA2k_int : Integrable (fun ω =>
      ∫ σ, G_A2k ω σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) P :=
    integrable_integral_pi_tilted (μ := μ_s) hEm_joint hprob_ω (G := G_A2k)
      ((hAm.comp measurable_snd).pow_const (2 * k)) (M := 2 ^ (2 * k))
      (fun _ σ => by
        dsimp only [G_A2k]; rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_spin_overlap_sub_le_two hq (σ 0).1 (σ 1).1) _)
  let G_B2k (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
      (σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ := B_obs ω σ ^ (2 * k)
  let MB : ℝ := ((M : ℝ) / ((N : ℝ) + 1)) * |D₁| ^ 2 + |r|
  have hB2k_int : Integrable (fun ω =>
      ∫ σ, G_B2k ω σ ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) P :=
    integrable_integral_pi_tilted (μ := μ_s) hEm_joint hprob_ω (G := G_B2k)
      (hBm_joint.pow_const (2 * k)) (M := MB ^ (2 * k))
      (fun ω σ => by
        dsimp only [G_B2k]; rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _)
          (abs_empVar_obs_le (N := N) hu.abs_deriv_le r (S_fn ω (σ 0)) (S_fn ω (σ 1))) _)
  exact ⟨hAm, hBm_slice, hQ_m, hA2k_int, hB2k_int⟩

/-- The common weighted overlap product in the moment ODE. The weight can be any lower
power of the centered free energy. -/
private theorem abs_integral_interpolating_overlap_product_mul_pow_le (D : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N M : ℕ) {s : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1)
        {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q)
        {m : ℕ} (_hm : m < k),
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
        let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P := (P_g.prod P_z).prod P_z'
        let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)
        let S_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (j : Fin M) : ℝ :=
          Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j)
        let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
          (∑ j : Fin M, u (S_fn ω x j)) +
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
        let A (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
          ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s ω x) ∂μ_s)
        let RS : ℝ :=
          perceptronRSFunctional u ((M : ℝ) / ((N : ℝ) + 1)) r q + ((1 - s) / 2) * r * (1 - q)
        |∫ ω,
            (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
              ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
                ((((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
                  deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j)) - r)
              ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) *
            (A ω - RS) ^ m ∂P| ≤
          C / ((N : ℝ) + 1) * (∫ ω, |A ω - RS| ^ k ∂P) ^ ((m : ℝ) / (k : ℝ)) := by
  obtain ⟨K_ov, hKov0, h_ov⟩ := integral_interpolating_overlap_pow_le D
  obtain ⟨K_emp, L_emp, hKemp0, hLemp0, h_emp⟩ := integral_interpolating_empirical_variance_pow_le D
  let K : ℝ := max (max K_ov K_emp) 1
  refine ⟨K, le_max_right _ _, ?_⟩
  intro k
  let C : ℝ := Real.sqrt (64 * (k : ℝ) * ((k : ℝ) * L_emp))
  refine ⟨C, by positivity, ?_⟩
  intro N M s hs u hd hb hα q r hq hr m hm P_g P_z P_z' P μ_s S_fn E_s A RS
  have hk_pos : 1 ≤ k := by omega
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z']; infer_instance
  let α : ℝ := (M : ℝ) / ((N : ℝ) + 1)
  have hα0 : 0 ≤ α := by dsimp only [α]; positivity
  have hα1 : α ≤ 1 := by
    have h1 : α * 1 ≤ α * K := mul_le_mul_of_nonneg_left (le_max_right _ 1) hα0
    linarith [hα]
  have hα_ov : α * K_ov ≤ 1 :=
    (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (le_max_left _ _)) hα0).trans hα
  have hα_emp : α * K_emp ≤ 1 :=
    (mul_le_mul_of_nonneg_left ((le_max_right _ _).trans (le_max_left _ _)) hα0).trans hα
  have hq_mem : q ∈ Icc (0 : ℝ) 1 := by rw [hq]; exact integral_tanh_sq_sqrt_mem_Icc r
  have hprob_ω (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      IsProbabilityMeasure (Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω)) := by
    have := isProbabilityMeasure_tilted_interpEnergy (L := N + 1) hu.measurable
      (fun x => hu.le x) s q r ω
    infer_instance
  obtain ⟨hAm_obs, hBm_obs, hQ_m, hA2k_P, hB2k_P⟩ :=
    measurable_and_integrable_interp_pair_pow_moments (N := N) (M := M) hu hq_mem r s k
  obtain ⟨hm_log, -⟩ := measurable_and_abs_log_interpPartition_le (N := N) (M := M)
    hu.measurable hu.abs_le q r hs.1
  have hVm : Measurable fun ω => A ω - RS := (hm_log.const_mul _).sub_const RS
  have hVk_int : Integrable (fun ω => |A ω - RS| ^ k) P :=
    (integrable_pow_of_memLp k
      ((memLp_interp_log_partition_and_deriv (N := N) (M := M) hu.measurable hu.abs_le (D₁ := D)
        q r RS 1 hs.1 ((max k 1 : ℕ) : ℝ≥0)).2.2)).2
  let MA : ℝ := 2
  let MB : ℝ := α * |D| ^ 2 + |r|
  have hQ_bd (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) :
      |∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
          ((((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
            deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j)) - r)
        ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))| ≤ MA * MB :=
    abs_integral_le_of_forall_abs_le _ fun σ => by
      rw [abs_mul]
      exact mul_le_mul (abs_spin_overlap_sub_le_two hq_mem (σ 0).1 (σ 1).1)
        (abs_empVar_obs_le (N := N) hu.abs_deriv_le r (S_fn ω (σ 0)) (S_fn ω (σ 1)))
        (abs_nonneg _) zero_le_two
  have hstep2 := abs_integral_mul_pow_le_rpow_inv_mul_rpow_div hQ_bd hQ_m.aestronglyMeasurable
    hVm.aestronglyMeasurable hm hVk_int
  have hstep1 := rpow_inv_integral_abs_pow_gibbs_mul_le (P := P)
    (ν := fun ω => Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))
    (A := fun _ σ => (((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q)
    (B := fun ω σ => (((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
      deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j)) - r)
    (fun _ σ => abs_spin_overlap_sub_le_two hq_mem (σ 0).1 (σ 1).1)
    (fun ω σ => abs_empVar_obs_le (N := N) hu.abs_deriv_le_abs r (S_fn ω (σ 0)) (S_fn ω (σ 1)))
    hQ_m.aestronglyMeasurable hk_pos
    (fun _ => hAm_obs.aestronglyMeasurable) (fun ω => (hBm_obs ω).aestronglyMeasurable)
    hA2k_P hB2k_P
  have h_ov_k := h_ov N M hs hd hb hα_ov hq hr k
  have h_emp_k := h_emp N M hs hd hb hα_emp hq hr k
  dsimp only at h_ov_k h_emp_k
  have hprod := rpow_inv_two_mul_product_le hk_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)
    hLemp0 hα0 hα1
    (integral_nonneg fun _ => integral_nonneg fun _ => Even.pow_nonneg ⟨k, by ring⟩ _)
    (integral_nonneg fun _ => integral_nonneg fun _ => Even.pow_nonneg ⟨k, by ring⟩ _)
    h_ov_k h_emp_k
  exact hstep2.trans (mul_le_mul_of_nonneg_right (hstep1.trans hprod)
    (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _))

/-- **Talagrand Section 2.5, Eq. (2.109), first inequality (`|VII|` bound):**
Given `D`, choose `K ≥ 1` before the order `k` and the bound constant `C`. Under (2.7),
`α K ≤ 1`, `(q, r)` solving (2.68), and `s ∈ [0, 1]`,
`|VII| ≤ (C / (N + 1)) * (𝔼|V(s)|^k)^{((k - 1 : ℕ) : ℝ) / k}`. -/
theorem abs_interpolating_overlap_product_mul_pow_sub_one_le (D : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N M : ℕ) {s : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1)
        {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q),
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
        let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P := (P_g.prod P_z).prod P_z'
        let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)
        let S_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (j : Fin M) : ℝ :=
          Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j)
        let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
          (∑ j : Fin M, u (S_fn ω x j)) +
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
        let A (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
          ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s ω x) ∂μ_s)
        let RS : ℝ :=
          perceptronRSFunctional u ((M : ℝ) / ((N : ℝ) + 1)) r q + ((1 - s) / 2) * r * (1 - q)
        |-(k : ℝ) / 2 * ∫ ω,
            (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
              ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
                ((((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
                  deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j)) - r)
              ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) *
            (A ω - RS) ^ (k - 1) ∂P| ≤
          C / ((N : ℝ) + 1) * (∫ ω, |A ω - RS| ^ k ∂P) ^ (((k - 1 : ℕ) : ℝ) / (k : ℝ)) := by
  obtain ⟨K, hK, h⟩ := abs_integral_interpolating_overlap_product_mul_pow_le D
  refine ⟨K, hK, ?_⟩
  intro k
  obtain ⟨C, hC, hbound⟩ := h k
  let C' : ℝ := ((k : ℝ) / 2) * C
  refine ⟨C', by dsimp only [C']; positivity, ?_⟩
  intro N M s hs u hd hb hα q r hq hr P_g P_z P_z' P μ_s S_fn E_s A RS
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [C']
  have hbnd := hbound N M hs hd hb hα hq hr (m := k - 1) (by omega)
  dsimp only at hbnd
  rw [abs_mul, abs_div, abs_neg, abs_of_nonneg (Nat.cast_nonneg k), abs_of_pos zero_lt_two]
  calc ((k : ℝ) / 2) * _ ≤ ((k : ℝ) / 2) *
      (C / ((N : ℝ) + 1) * (∫ ω, |A ω - RS| ^ k ∂P) ^ (((k - 1 : ℕ) : ℝ) / k)) :=
        mul_le_mul_of_nonneg_left hbnd (by positivity)
    _ = _ := by dsimp only [C']; ring

/-- The fixed-order form of `abs_interpolating_overlap_product_mul_pow_sub_one_le`. -/
theorem abs_interpolating_term_VII_le (D : ℝ) (k : ℕ) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
      ∀ (N M : ℕ) {s : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1)
        {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q),
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
        let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P := (P_g.prod P_z).prod P_z'
        let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)
        let S_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (j : Fin M) : ℝ :=
          Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j)
        let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
          (∑ j : Fin M, u (S_fn ω x j)) +
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
        let A (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
          ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s ω x) ∂μ_s)
        let RS : ℝ :=
          perceptronRSFunctional u ((M : ℝ) / ((N : ℝ) + 1)) r q + ((1 - s) / 2) * r * (1 - q)
        |-(k : ℝ) / 2 * ∫ ω,
            (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
              ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
                ((((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
                  deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j)) - r)
              ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) *
            (A ω - RS) ^ (k - 1) ∂P| ≤
          C / ((N : ℝ) + 1) * (∫ ω, |A ω - RS| ^ k ∂P) ^ (((k - 1 : ℕ) : ℝ) / (k : ℝ)) := by
  obtain ⟨K, hK, h⟩ := abs_interpolating_overlap_product_mul_pow_sub_one_le D
  obtain ⟨C, hC, hbound⟩ := h k
  exact ⟨K, C, zero_le_one.trans hK, hC, hbound⟩

/-- **Talagrand Section 2.5, Eq. (2.109), second inequality (`|VIII|` bound):**
Given `D`, choose `K ≥ 1` before the order `k` and the bound constant `C`. Under (2.7),
`α K ≤ 1`, `(q, r)` solving (2.68), and `s ∈ [0, 1]`,
`|VIII| ≤ (C / (N + 1)²) * (𝔼|V(s)|^k)^{((k - 2 : ℕ) : ℝ) / k}`. -/
theorem abs_interpolating_overlap_product_mul_pow_sub_two_le (D : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (N M : ℕ) {s : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1)
        {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q),
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
        let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P := (P_g.prod P_z).prod P_z'
        let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)
        let S_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (j : Fin M) : ℝ :=
          Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j)
        let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
          (∑ j : Fin M, u (S_fn ω x j)) +
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
        let A (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
          ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s ω x) ∂μ_s)
        let RS : ℝ :=
          perceptronRSFunctional u ((M : ℝ) / ((N : ℝ) + 1)) r q + ((1 - s) / 2) * r * (1 - q)
        |(k : ℝ) * ((k : ℝ) - 1) / (2 * ((N : ℝ) + 1)) * ∫ ω,
            (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
              ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
                ((((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
                  deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j)) - r)
              ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) *
            (A ω - RS) ^ (k - 2) ∂P| ≤
          C / ((N : ℝ) + 1) ^ 2 * (∫ ω, |A ω - RS| ^ k ∂P) ^ (((k - 2 : ℕ) : ℝ) / (k : ℝ)) := by
  obtain ⟨K, hK, h⟩ := abs_integral_interpolating_overlap_product_mul_pow_le D
  refine ⟨K, hK, ?_⟩
  intro k
  obtain ⟨C, hC, hbound⟩ := h k
  let C' : ℝ := ((k : ℝ) * ((k - 1 : ℕ) : ℝ) / 2) * C
  refine ⟨C', by dsimp only [C']; positivity, ?_⟩
  intro N M s hs u hd hb hα q r hq hr P_g P_z P_z' P μ_s S_fn E_s A RS
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have hcoeff : (k : ℝ) * ((k : ℝ) - 1) = 0 := by interval_cases k <;> norm_num
    rw [hcoeff, zero_div, zero_mul, abs_zero]
    dsimp only [C']
    positivity
  have hsub1 : (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hbnd := hbound N M hs hd hb hα hq hr (m := k - 2) (by omega)
  dsimp only at hbnd
  rw [hsub1, abs_mul, abs_div,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg (k - 1))),
    abs_of_pos (by positivity : (0 : ℝ) < 2 * ((N : ℝ) + 1))]
  calc ((k : ℝ) * ((k - 1 : ℕ) : ℝ) / (2 * ((N : ℝ) + 1))) * _
      ≤ ((k : ℝ) * ((k - 1 : ℕ) : ℝ) / (2 * ((N : ℝ) + 1))) *
        (C / ((N : ℝ) + 1) * (∫ ω, |A ω - RS| ^ k ∂P) ^ (((k - 2 : ℕ) : ℝ) / k)) :=
          mul_le_mul_of_nonneg_left hbnd (by positivity)
    _ = _ := by dsimp only [C']; field_simp

/-- The fixed-order form of `abs_interpolating_overlap_product_mul_pow_sub_two_le`. -/
theorem abs_interpolating_term_VIII_le (D : ℝ) (k : ℕ) :
    ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
      ∀ (N M : ℕ) {s : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1)
        {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        (_hα : (M : ℝ) / ((N : ℝ) + 1) * K ≤ 1)
        {q r : ℝ}
        (_hq : q = ∫ z : ℝ, Real.tanh (z * Real.sqrt r) ^ 2 ∂gaussianReal 0 1)
        (_hr : r = ((M : ℝ) / ((N : ℝ) + 1)) * perceptronRhat u q),
        let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
        let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
        let P := (P_g.prod P_z).prod P_z'
        let μ_s := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
          (Measure.pi fun _ : Fin M => gaussianReal 0 1)
        let S_fn (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) (j : Fin M) : ℝ :=
          Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 j i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 j + Real.sqrt (1 - q) * x.2 j)
        let E_s (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
            (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
          (∑ j : Fin M, u (S_fn ω x j)) +
            ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
        let A (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)) : ℝ :=
          ((N : ℝ) + 1)⁻¹ * Real.log (∫ x, Real.exp (E_s ω x) ∂μ_s)
        let RS : ℝ :=
          perceptronRSFunctional u ((M : ℝ) / ((N : ℝ) + 1)) r q + ((1 - s) / 2) * r * (1 - q)
        |(k : ℝ) * ((k : ℝ) - 1) / (2 * ((N : ℝ) + 1)) * ∫ ω,
            (∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
              ((((N : ℝ) + 1)⁻¹ * ∑ i, (((σ 0).1 i : ℤ) : ℝ) * (((σ 1).1 i : ℤ) : ℝ)) - q) *
                ((((N : ℝ) + 1)⁻¹ * ∑ j : Fin M,
                  deriv u (S_fn ω (σ 0) j) * deriv u (S_fn ω (σ 1) j)) - r)
              ∂(Measure.pi fun _ : Fin 2 => μ_s.tilted (E_s ω))) *
            (A ω - RS) ^ (k - 2) ∂P| ≤
          C / ((N : ℝ) + 1) ^ 2 * (∫ ω, |A ω - RS| ^ k ∂P) ^ (((k - 2 : ℕ) : ℝ) / (k : ℝ)) := by
  obtain ⟨K, hK, h⟩ := abs_interpolating_overlap_product_mul_pow_sub_two_le D
  obtain ⟨C, hC, hbound⟩ := h k
  exact ⟨K, C, zero_le_one.trans hK, hC, hbound⟩

end SpinGlasses
