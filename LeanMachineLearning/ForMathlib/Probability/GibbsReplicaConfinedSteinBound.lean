/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiExp
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FreshReplicas
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaConfinedStein

/-!
# A covariance bound for the square-root path of confined Gibbs states

The derivative along `v ↦ √v X + √(1 - v) Y` computed in `GibbsReplicaConfinedStein` is a sum of
six groups of replica averages, each against one covariance
`E[S'(σᵃ) S(σᵇ)] = (X(xᵃ) ⬝ᵥ X(xᵇ) - Y ⬝ᵥ Y - 1_{a = b} c²) / 2`.
Here the derivative is bounded by a constant, which depends only on the number of replicas and on
the bounds of `u'`, `u''` and `ψ`, times the sum of the averages of `|f| |covariance|` over two
fresh replicas. The constant does not depend on the dimension of the configuration space.

## Main statements

* `MeasureTheory.exists_hasDerivAt_integral_integral_pi_tilted_prod_gaussianReal_sqrt_abs_le`
* `MeasureTheory.continuousOn_integral_integral_pi_tilted_prod_gaussianReal_sqrt`
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function Set Filter Matrix
open scoped NNReal Topology

namespace MeasureTheory

universe u

variable {E K : Type*} {R : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The coefficients of the square-root path are bounded on the unit ball, uniformly in
`v ∈ [0, 1]`. -/
private theorem abs_sqrt_path_coeff_le_of_norm_le_one {E K : Type*} [SeminormedAddCommGroup E]
    [Fintype K] {X : E → K → ℝ} {L_X : ℝ} {n_X : ℕ} (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X)
    (Y : K → ℝ) {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (k : K) (x : E) (hx : ‖x‖ ≤ 1) :
    |Real.sqrt v * X x k + Real.sqrt (1 - v) * Y k| ≤ |L_X| * 2 ^ n_X + ∑ j, |Y j| := by
  have hs1 : Real.sqrt v ≤ 1 := Real.sqrt_le_one.2 hv1
  have hs2 : Real.sqrt (1 - v) ≤ 1 := Real.sqrt_le_one.2 (by linarith)
  have hX1 : |X x k| ≤ |L_X| * 2 ^ n_X :=
    (hXb k x).trans (mul_le_mul (le_abs_self _)
      (pow_le_pow_left₀ (by positivity) (by linarith : 1 + ‖x‖ ≤ 2) _)
      (by positivity) (abs_nonneg _))
  have hY1 : |Y k| ≤ ∑ j, |Y j| :=
    Finset.single_le_sum (f := fun j => |Y j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (add_le_add (mul_le_mul hs1 hX1 (abs_nonneg _) zero_le_one)
    (mul_le_mul hs2 hY1 (abs_nonneg _) zero_le_one)).trans_eq (by rw [one_mul, one_mul])

/-- **Covariance bound for the derivative along the square-root path** (the model-free form of
Talagrand's Eq. (3.96)). Under the hypotheses of
`hasDerivAt_integral_integral_pi_tilted_prod_gaussianReal_sqrt`, the quenched average of
`f(x) ∏_r ψ_r(S_v(σʳ))` has a derivative at `v₀ ∈ (0, 1)` whose absolute value is at most
`(n + 1)² B ^ (n + 2)` times `∑_{a, b} ν(|f| |X(xᵃ) ⬝ᵥ X(xᵇ) - Y ⬝ᵥ Y - 1_{a = b} c²|)`, where
`n = |R|`, the replicas `a, b` run over `R` and two fresh ones, and
`B = 1 + |M₀| + |M₁| + |M₂| + |D₁| + |D₂|`. -/
theorem exists_hasDerivAt_integral_integral_pi_tilted_prod_gaussianReal_sqrt_abs_le
    {Ω : Type*} [MeasurableSpace Ω] (P₀ : Measure Ω)
    [Fintype K] [Fintype R] [DecidableEq R]
    {κ : ℝ} (hκ : 0 < κ)
    {B₀ c₀ : Ω → ℝ} (hB₀ : ∀ ω, 0 ≤ B₀ ω)
    (hmom : ∀ deg : ℕ, Integrable (fun ω => (1 + B₀ ω + c₀ ω) ^ deg) P₀)
    {E₀ : Ω → E → ℝ} (hE₀m : Measurable fun p : Ω × E => E₀ p.1 p.2)
    (hE₀_conf : ∀ ω x, E₀ ω x ≤ B₀ ω * ‖x‖ - κ * ‖x‖ ^ 2)
    (hE₀_low : ∀ ω x, ‖x‖ ≤ 1 → -c₀ ω ≤ E₀ ω x)
    (X : E → K → ℝ) (Y : K → ℝ) (hXm : ∀ k, Measurable fun x => X x k)
    {L_X : ℝ} {n_X : ℕ} (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X)
    (horth : ∀ x, X x ⬝ᵥ Y = 0)
    (c_ξ : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu₂ : Differentiable ℝ (deriv u))
    (hu0 : ∀ x, u x ≤ 0) {D₁ D₂ : ℝ} (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    (hψ₂d : ∀ r, Differentiable ℝ (deriv (ψ r)))
    {M₀ M₁ M₂ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀)
    (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁)
    (hM₂ : ∀ r x, |deriv (deriv (ψ r)) x| ≤ M₂)
    {f : (R → E) → ℝ} (hf : Measurable f) {C_f : ℝ} {m_f : ℕ}
    (hfb : ∀ a, |f a| ≤ C_f * ∏ r, (1 + ‖a r‖) ^ m_f)
    {v₀ : ℝ} (hv₀ : v₀ ∈ Ioo (0 : ℝ) 1) :
    let γ_sh := Measure.pi fun _ : K => gaussianReal 0 1
    let S (v : ℝ) (w : K → ℝ) (p : E × ℝ) : ℝ :=
      Real.sqrt v * (X p.1 ⬝ᵥ w) + Real.sqrt (1 - v) * (Y ⬝ᵥ w + c_ξ * p.2)
    let ν (v : ℝ) (ω : Ω) (w : K → ℝ) : Measure (E × ℝ) :=
      (μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ ω p.1 + u (S v w p))
    let T (a b : Option (Option R)) : ℝ :=
      ∫ ω, ∫ w, ∫ σ : Option (Option R) → E × ℝ,
        |f (fun r => (σ (some (some r))).1)| *
          |X (σ a).1 ⬝ᵥ X (σ b).1 - (Y ⬝ᵥ Y + if a = b then c_ξ ^ 2 else 0)|
        ∂(Measure.pi fun _ : Option (Option R) => ν v₀ ω w) ∂γ_sh ∂P₀
    ∃ D : ℝ, HasDerivAt
        (fun v => ∫ ω, ∫ w, ∫ σ : R → E × ℝ, f (fun r => (σ r).1) * ∏ r, ψ r (S v w (σ r))
          ∂(Measure.pi fun _ : R => ν v ω w) ∂γ_sh ∂P₀) D v₀ ∧
      |D| ≤ ((Fintype.card R : ℝ) + 1) ^ 2 *
        (1 + |M₀| + |M₁| + |M₂| + |D₁| + |D₂|) ^ (Fintype.card R + 2) * ∑ a, ∑ b, T a b := by
  intro γ_sh S ν T
  obtain ⟨-, -, -, -, -, -, hd⟩ :=
    hasDerivAt_integral_integral_pi_tilted_prod_gaussianReal_sqrt μ P₀ hκ hB₀ hmom hE₀m
      hE₀_conf hE₀_low X Y hXm hXb horth c_ξ hu hu₂ hu0 hD₁ hD₂ ψ hψd hψ₂d hM₀ hM₁ hM₂ hf hfb hv₀
  refine ⟨_, hd, ?_⟩
  have hum : Measurable u := hu.continuous.measurable
  set B : ℝ := 1 + |M₀| + |M₁| + |M₂| + |D₁| + |D₂| with hB
  have hB1 : 1 ≤ B := by
    rw [hB]
    linarith [abs_nonneg M₀, abs_nonneg M₁, abs_nonneg M₂, abs_nonneg D₁, abs_nonneg D₂]
  have hB0 : 0 ≤ B := zero_le_one.trans hB1
  set n : ℕ := Fintype.card R with hn
  -- the square-root path is a linear form with `v`-dependent coefficients
  set A : E → K → ℝ := fun x => Real.sqrt v₀ • X x + Real.sqrt (1 - v₀) • Y
  set c : ℝ := Real.sqrt (1 - v₀) * c_ξ
  have hAm : ∀ k, Measurable fun x => A x k := fun k =>
    ((hXm k).const_mul (Real.sqrt v₀)).add_const _
  have hS : ∀ w p, S v₀ w p = A p.1 ⬝ᵥ w + c * p.2 := fun w p => by
    dsimp only [S, A, c]
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    ring
  have hSm : Measurable fun q : (K → ℝ) × (E × ℝ) => S v₀ q.1 q.2 := by
    simp only [hS]
    exact (Finset.measurable_sum _ fun k _ =>
      ((hAm k).comp (measurable_fst.comp measurable_snd)).mul
        ((measurable_pi_apply k).comp measurable_fst)).add
      ((measurable_snd.comp measurable_snd).const_mul c)
  -- the covariance observable of a pair of replicas
  set H : Option (Option R) → Option (Option R) → (Option (Option R) → E × ℝ) → ℝ :=
    fun a b σ => |f (fun r => (σ (some (some r))).1)| *
      |X (σ a).1 ⬝ᵥ X (σ b).1 - (Y ⬝ᵥ Y + if a = b then c_ξ ^ 2 else 0)|
  have hXXm : ∀ a b : Option (Option R),
      Measurable fun σ : Option (Option R) → E × ℝ => X (σ a).1 ⬝ᵥ X (σ b).1 := fun a b =>
    Finset.measurable_sum _ fun k _ =>
      ((hXm k).comp (measurable_fst.comp (measurable_pi_apply a))).mul
        ((hXm k).comp (measurable_fst.comp (measurable_pi_apply b)))
  have hFm : Measurable fun σ : Option (Option R) → E × ℝ => f fun r => (σ (some (some r))).1 :=
    hf.comp (measurable_pi_iff.2 fun r =>
      measurable_fst.comp (measurable_pi_apply (some (some r))))
  have hHm : ∀ a b, Measurable (H a b) := fun a b =>
    (continuous_abs.measurable.comp hFm).mul
      (continuous_abs.measurable.comp ((hXXm a b).sub_const _))
  set C_cov : ℝ := (∑ _k : K, |L_X| ^ 2) + (∑ k : K, Y k ^ 2) + c_ξ ^ 2 + c_ξ ^ 2
  have hC_cov : 0 ≤ C_cov := by
    have h1 : 0 ≤ ∑ _k : K, |L_X| ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h2 : 0 ≤ ∑ k : K, Y k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    dsimp only [C_cov]; linarith [sq_nonneg c_ξ]
  have hHb : ∀ a b σ, |H a b σ| ≤
      |C_f| * C_cov * ∏ o, (1 + ‖σ o‖) ^ (m_f + 2 * n_X) := fun a b σ => by
    have h1 : |f (fun r => (σ (some (some r))).1)| ≤
        |C_f| * ∏ o, (1 + ‖σ o‖) ^ m_f :=
      abs_comp_le_prod_of_injective hfb norm_fst_le
        ((Option.some_injective _).comp (Option.some_injective R)) σ
    have h2 : |X (σ a).1 ⬝ᵥ X (σ b).1 - (Y ⬝ᵥ Y + if a = b then c_ξ ^ 2 else 0)| ≤
        C_cov * ∏ o, (1 + ‖σ o‖) ^ (2 * n_X) := by
      have hcov := abs_dotProduct_sub_dotProduct_le_of_abs_le_pow (Y := Y) hXb c_ξ (σ a).1 (σ b).1
      have hpow : ∀ o : Option (Option R), (1 + ‖(σ o).1‖) ^ n_X ≤ (1 + ‖σ o‖) ^ n_X := fun o =>
        pow_le_pow_left₀ (by positivity) (add_le_add_right (norm_fst_le (σ o)) 1) _
      have hprod : (1 + ‖(σ a).1‖) ^ n_X * (1 + ‖(σ b).1‖) ^ n_X ≤
          ∏ o, (1 + ‖σ o‖) ^ (2 * n_X) := by
        rw [two_mul]
        simp only [pow_add, Finset.prod_mul_distrib]
        exact mul_le_mul ((hpow a).trans (one_add_norm_pow_le_prod σ n_X a))
          ((hpow b).trans (one_add_norm_pow_le_prod σ n_X b)) (by positivity)
          (Finset.prod_nonneg fun _ _ => by positivity)
      have hone : (1 : ℝ) ≤ ∏ o, (1 + ‖σ o‖) ^ (2 * n_X) :=
        Finset.one_le_prod₀ fun o _ => one_le_pow₀ (by linarith [norm_nonneg (σ o)])
      have hδ : |(if a = b then c_ξ ^ 2 else 0) - c_ξ ^ 0 * 0| ≤ c_ξ ^ 2 := by
        split <;> simp [sq_nonneg]
      have hδ' : |(if a = b then c_ξ ^ 2 else 0 : ℝ)| ≤ c_ξ ^ 2 := by simpa using hδ
      have hsplit : X (σ a).1 ⬝ᵥ X (σ b).1 - (Y ⬝ᵥ Y + if a = b then c_ξ ^ 2 else 0) =
          (X (σ a).1 ⬝ᵥ X (σ b).1 - Y ⬝ᵥ Y) - (if a = b then c_ξ ^ 2 else 0) := by ring
      rw [hsplit]
      refine (abs_sub _ _).trans ?_
      have hbase : 0 ≤ (∑ _k : K, |L_X| ^ 2) + (∑ k : K, Y k ^ 2) + c_ξ ^ 2 := by
        have h1 : 0 ≤ ∑ _k : K, |L_X| ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        have h2 : 0 ≤ ∑ k : K, Y k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        linarith [sq_nonneg c_ξ]
      refine (add_le_add (hcov.trans ((mul_assoc _ _ _).le.trans
        (mul_le_mul_of_nonneg_left hprod hbase)))
        (hδ'.trans (le_mul_of_one_le_right (sq_nonneg _) hone))).trans_eq ?_
      dsimp only [C_cov]; ring
    rw [abs_mul, abs_abs, abs_abs]
    refine (mul_le_mul h1 h2 (abs_nonneg _)
      (mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun _ _ => by positivity))).trans_eq ?_
    simp only [pow_add, Finset.prod_mul_distrib]
    ring
  -- every group is controlled by one of the pair averages
  have key : ∀ {ι : Type u} [Fintype ι] (e : ι → Option (Option R)) (_ : Function.Injective e)
      (a b : Option (Option R)) (G : (K → ℝ) → (ι → E × ℝ) → ℝ),
      (∀ w, Measurable (G w)) →
      (∀ w σ, |G w (fun i => σ (e i))| ≤ B ^ (n + 2) * H a b σ) →
      |∫ ω, ∫ w, ∫ σ : ι → E × ℝ, G w σ ∂(Measure.pi fun _ : ι => ν v₀ ω w) ∂γ_sh ∂P₀| ≤
        B ^ (n + 2) * T a b := by
    intro ι _ e he a b G hGm hGb
    obtain ⟨_, -, hJ⟩ := measurable_and_abs_le_integral_w_pi_tilted_prod_gaussianReal
      (ι := Option (Option R)) μ P₀ hκ hB₀
      (fun ω => nonneg_of_confining_of_neg_le (hE₀_conf ω) (hE₀_low ω)) hmom hE₀m hE₀_conf
      hE₀_low X Y hXm hXb c_ξ hu hu0 hD₁ (m_f + 2 * n_X)
    have hJint : Integrable (fun ω => ∫ w, ∫ σ : Option (Option R) → E × ℝ, H a b σ
        ∂(Measure.pi fun _ : Option (Option R) => ν v₀ ω w) ∂γ_sh) P₀ :=
      (hJ hv₀.1.le hv₀.2.le (G := fun _ σ => H a b σ) ((hHm a b).comp measurable_snd)
        (C_G := |C_f| * C_cov) (mul_nonneg (abs_nonneg _) hC_cov) fun _ σ => hHb a b σ).2.2
    rw [← Real.norm_eq_abs]
    dsimp only [T]
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hJint.const_mul _) (ae_of_all _ fun ω => ?_)
    have hEω : Measurable (E₀ ω) := hE₀m.comp (measurable_const.prodMk measurable_id)
    have hc₀ω : 0 ≤ c₀ ω := nonneg_of_confining_of_neg_le (hE₀_conf ω) (hE₀_low ω)
    have hwint : Integrable (fun w => ∫ σ : Option (Option R) → E × ℝ, H a b σ
        ∂(Measure.pi fun _ : Option (Option R) => ν v₀ ω w)) γ_sh := by
      obtain ⟨_, -, hI⟩ := exists_integrable_and_abs_le_integral_pi_tilted_prod_gaussianReal
        (K := K) (ι := Option (Option R)) μ hκ (m_f + 2 * n_X)
      have hs : ∀ k x, ‖x‖ ≤ 1 → |A x k| ≤
          Real.sqrt v₀ * (|L_X| * 2 ^ n_X) + Real.sqrt (1 - v₀) * ∑ j, |Y j| := fun k x hx => by
        have hXk : |X x k| ≤ |L_X| * 2 ^ n_X := (hXb k x).trans
          (mul_le_mul (le_abs_self _)
            (pow_le_pow_left₀ (by positivity) (by linarith : 1 + ‖x‖ ≤ 2) _)
            (by positivity) (abs_nonneg _))
        have hYk : |Y k| ≤ ∑ j, |Y j| :=
          Finset.single_le_sum (f := fun j => |Y j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
        dsimp only [A]
        rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          exact mul_le_mul_of_nonneg_left hXk (Real.sqrt_nonneg _)
        · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          exact mul_le_mul_of_nonneg_left hYk (Real.sqrt_nonneg _)
      have hsum : 0 ≤ ∑ j, |Y j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hres := (hI (hB₀ ω) hc₀ω hEω (hE₀_conf ω) (hE₀_low ω) A hAm
        (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by positivity))
          (mul_nonneg (Real.sqrt_nonneg _) hsum)) hs c hu hu0 hD₁
        (G := fun _ σ => H a b σ) ((hHm a b).comp measurable_snd)
        (C₀ := |C_f| * C_cov) (C₁ := 0) (mul_nonneg (abs_nonneg _) hC_cov) le_rfl
        fun w σ => by simpa only [zero_mul, add_zero] using hHb a b σ).2
      simpa only [ν, hS] using hres
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le (hwint.const_mul _) (ae_of_all _ fun w => ?_)
    have hprob : IsProbabilityMeasure (ν v₀ ω w) :=
      isProbabilityMeasure_tilted_prod_gaussianReal_of_confining μ hκ hEω (hE₀_conf ω) hum hu0
        (S := S v₀ w) (hSm.comp measurable_prodMk_left)
    have hHint : Integrable (H a b) (Measure.pi fun _ : Option (Option R) => ν v₀ ω w) := by
      have h := integrable_pi_tilted_prod_gaussianReal_of_poly (ι := Option (Option R)) μ hκ
        (hB₀ ω) hEω (hE₀_conf ω) A hAm c hu hu0 w (H a b) (hHm a b) (hHb a b)
      simpa only [ν, hS] using h
    rw [← integral_pi_comp_injective (ν v₀ ω w) he (G w) (hGm w).aestronglyMeasurable,
      ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hHint.const_mul _) (ae_of_all _ fun σ => hGb w σ)
  -- bounds for the potential factors
  have hD1B : ∀ x, |deriv u x| ≤ B := fun x =>
    (hD₁ x).trans ((le_abs_self _).trans (by
      rw [hB]; linarith [abs_nonneg M₀, abs_nonneg M₁, abs_nonneg M₂, abs_nonneg D₂]))
  have hψB : ∀ r x, |ψ r x| ≤ B := fun r x =>
    (hM₀ r x).trans ((le_abs_self _).trans (by
      rw [hB]; linarith [abs_nonneg M₁, abs_nonneg M₂, abs_nonneg D₁, abs_nonneg D₂]))
  have hM0 : ∀ r x, |ψ r x| ≤ |M₀| := fun r x => (hM₀ r x).trans (le_abs_self _)
  have hM1 : ∀ r x, |deriv (ψ r) x| ≤ |M₁| := fun r x => (hM₁ r x).trans (le_abs_self _)
  have hM2 : ∀ r x, |deriv (deriv (ψ r)) x| ≤ |M₂| := fun r x => (hM₂ r x).trans (le_abs_self _)
  have hE1 : ∀ x, |deriv u x| ≤ |D₁| := fun x => (hD₁ x).trans (le_abs_self _)
  have hE2 : ∀ x, |deriv (deriv u) x| ≤ |D₂| := fun x => (hD₂ x).trans (le_abs_self _)
  have h0M0 := abs_nonneg M₀
  have h0M1 := abs_nonneg M₁
  have h0M2 := abs_nonneg M₂
  have h0D1 := abs_nonneg D₁
  have h0D2 := abs_nonneg D₂
  have hW : ∀ x, |deriv (deriv u) x + deriv u x ^ 2| ≤ B ^ 2 := fun x => by
    refine (abs_add_le _ _).trans ?_
    rw [abs_pow]
    refine (add_le_add (hE2 x) (pow_le_pow_left₀ (abs_nonneg _) (hE1 x) 2)).trans ?_
    have h1 : 1 + |D₁| + |D₂| ≤ B := by rw [hB]; linarith
    refine le_trans ?_ (pow_le_pow_left₀ (by positivity) h1 2)
    nlinarith
  have hψd1 : ∀ r x, |deriv (ψ r) x + ψ r x * deriv u x| ≤ B ^ 2 := fun r x => by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    refine (add_le_add (hM1 r x) (mul_le_mul (hM0 r x) (hE1 x) (abs_nonneg _) h0M0)).trans ?_
    have h1 : 1 + |M₀| + |M₁| + |D₁| ≤ B := by rw [hB]; linarith
    refine le_trans ?_ (pow_le_pow_left₀ (by positivity) h1 2)
    nlinarith [mul_nonneg h0M0 h0D1]
  have hψd2 : ∀ r x, |deriv (deriv (ψ r)) x + 2 * deriv (ψ r) x * deriv u x +
      ψ r x * deriv (deriv u) x + ψ r x * deriv u x ^ 2| ≤ B ^ 3 := fun r x => by
    have h2 : |2 * deriv (ψ r) x * deriv u x| ≤ 2 * |M₁| * |D₁| := by
      rw [abs_mul, abs_mul, abs_two]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hM1 r x) zero_le_two) (hE1 x) (abs_nonneg _)
        (by positivity)
    have h3 : |ψ r x * deriv (deriv u) x| ≤ |M₀| * |D₂| := by
      rw [abs_mul]; exact mul_le_mul (hM0 r x) (hE2 x) (abs_nonneg _) h0M0
    have h4 : |ψ r x * deriv u x ^ 2| ≤ |M₀| * |D₁| ^ 2 := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul (hM0 r x) (pow_le_pow_left₀ (abs_nonneg _) (hE1 x) 2) (by positivity) h0M0
    refine (abs_add_le _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (hM2 r x) h2)) h3)) h4).trans ?_)
    set t : ℝ := |M₀| + |M₁| + |M₂| + |D₁| + |D₂| with ht
    have ht0 : 0 ≤ t := by positivity
    have hBt : B = 1 + t := by rw [hB, ht]; ring
    have hm0 : |M₀| ≤ t := by rw [ht]; linarith
    have hm1 : |M₁| ≤ t := by rw [ht]; linarith
    have hm2 : |M₂| ≤ t := by rw [ht]; linarith
    have hd1 : |D₁| ≤ t := by rw [ht]; linarith
    have hd2 : |D₂| ≤ t := by rw [ht]; linarith
    have e1 : |M₁| * |D₁| ≤ t * t := mul_le_mul hm1 hd1 h0D1 ht0
    have e2 : |M₀| * |D₂| ≤ t * t := mul_le_mul hm0 hd2 h0D2 ht0
    have e3 : |M₀| * |D₁| ^ 2 ≤ t * t ^ 2 :=
      mul_le_mul hm0 (pow_le_pow_left₀ h0D1 hd1 2) (sq_nonneg _) ht0
    have hexp : B ^ 3 = 1 + 3 * t + 3 * (t * t) + t * t ^ 2 := by rw [hBt]; ring
    rw [hexp]
    linarith [mul_nonneg ht0 ht0]
  have hprodB : ∀ (s : Finset R) (x : R → ℝ), |∏ r ∈ s, ψ r (x r)| ≤ B ^ s.card := fun s x =>
    s.abs_prod_le_pow_card fun r _ => hψB r _
  have hfin : ∀ (F C P : ℝ) (k : ℕ), |P| ≤ B ^ k → k ≤ n + 2 →
      |F * C * P| ≤ B ^ (n + 2) * (|F| * |C|) := fun F C P k hP hk => by
    rw [abs_mul, abs_mul, mul_comm (B ^ (n + 2))]
    exact mul_le_mul_of_nonneg_left (hP.trans (pow_le_pow_right₀ hB1 hk))
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  -- the product of a factor bounded by `B ^ a` and one bounded by `B ^ b`
  have hmul : ∀ (x y : ℝ) (a b : ℕ), |x| ≤ B ^ a → |y| ≤ B ^ b → |x * y| ≤ B ^ (a + b) :=
    fun x y a b hx hy => by
      rw [abs_mul, pow_add]; exact mul_le_mul hx hy (abs_nonneg _) (pow_nonneg hB0 _)
  have hSw : ∀ w, Measurable (S v₀ w) := fun w => hSm.comp measurable_prodMk_left
  have hfm : ∀ {ι : Type u} (g : R → ι), Measurable fun σ : ι → E × ℝ =>
      f (fun r => (σ (g r)).1) := fun g =>
    hf.comp (measurable_pi_iff.2 fun r => measurable_fst.comp (measurable_pi_apply (g r)))
  have hXX : ∀ {ι : Type u} (a b : ι), Measurable fun σ : ι → E × ℝ =>
      X (σ a).1 ⬝ᵥ X (σ b).1 := fun a b =>
    Finset.measurable_sum _ fun k _ =>
      ((hXm k).comp (measurable_fst.comp (measurable_pi_apply a))).mul
        ((hXm k).comp (measurable_fst.comp (measurable_pi_apply b)))
  have hcomp : ∀ {ι : Type u} (w : K → ℝ) (a : ι) (g : ℝ → ℝ), Measurable g →
      Measurable fun σ : ι → E × ℝ => g (S v₀ w (σ a)) := fun w a g hg =>
    hg.comp ((hSw w).comp (measurable_pi_apply a))
  have hu'm : Measurable (deriv u) := measurable_deriv u
  have hWm : Measurable fun x => deriv (deriv u) x + deriv u x ^ 2 :=
    (measurable_deriv (deriv u)).add (hu'm.pow_const 2)
  have hψm : ∀ r, Measurable (ψ r) := fun r => (hψd r).continuous.measurable
  have hψdm : ∀ r, Measurable fun x => deriv (ψ r) x + ψ r x * deriv u x := fun r =>
    (measurable_deriv (ψ r)).add ((hψm r).mul hu'm)
  have hψddm : ∀ r, Measurable fun x => deriv (deriv (ψ r)) x + 2 * deriv (ψ r) x * deriv u x +
      ψ r x * deriv (deriv u) x + ψ r x * deriv u x ^ 2 := fun r =>
    (((measurable_deriv (deriv (ψ r))).add (((measurable_deriv (ψ r)).const_mul 2).mul hu'm)).add
      ((hψm r).mul (measurable_deriv (deriv u)))).add ((hψm r).mul (hu'm.pow_const 2))
  have hss : Injective fun r : R => some (some r) :=
    (Option.some_injective _).comp (Option.some_injective R)
  have hos : Injective (Option.map (some : R → Option R)) :=
    Option.map_injective (Option.some_injective R)
  have h1 : ∀ i : R, |∫ ω, ∫ w, ∫ σ : R → E × ℝ,
      f (fun r => (σ r).1) * (X (σ i).1 ⬝ᵥ X (σ i).1 - (Y ⬝ᵥ Y + c_ξ ^ 2)) *
        ((deriv (deriv (ψ i)) (S v₀ w (σ i)) +
            2 * deriv (ψ i) (S v₀ w (σ i)) * deriv u (S v₀ w (σ i)) +
            ψ i (S v₀ w (σ i)) * deriv (deriv u) (S v₀ w (σ i)) +
            ψ i (S v₀ w (σ i)) * deriv u (S v₀ w (σ i)) ^ 2) *
          ∏ r ∈ Finset.univ.erase i, ψ r (S v₀ w (σ r)))
      ∂(Measure.pi fun _ : R => ν v₀ ω w) ∂γ_sh ∂P₀| ≤
      B ^ (n + 2) * T (some (some i)) (some (some i)) := fun i => by
    refine key _ hss _ _ _ (fun w => ?_) fun w σ => ?_
    · exact ((hfm id).mul ((hXX i i).sub_const _)).mul
        ((hcomp w i _ (hψddm i)).mul (Finset.measurable_prod _ fun r _ => hcomp w r _ (hψm r)))
    · have hk : 3 + (Finset.univ.erase i).card ≤ n + 2 := by
        have := Finset.card_pos.2 ⟨i, Finset.mem_univ i⟩
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), hn, ← Finset.card_univ]; omega
      simp only [H, reduceIte]
      exact hfin _ _ _ _ (hmul _ _ _ _ (hψd2 i _) (hprodB _ _)) hk
  have h2 : ∀ i : R, ∀ j ∈ Finset.univ.erase i, |∫ ω, ∫ w, ∫ σ : R → E × ℝ,
      f (fun r => (σ r).1) * (X (σ i).1 ⬝ᵥ X (σ j).1 - Y ⬝ᵥ Y) *
        ((deriv (ψ i) (S v₀ w (σ i)) + ψ i (S v₀ w (σ i)) * deriv u (S v₀ w (σ i))) *
          (deriv (ψ j) (S v₀ w (σ j)) + ψ j (S v₀ w (σ j)) * deriv u (S v₀ w (σ j))) *
          ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S v₀ w (σ r)))
      ∂(Measure.pi fun _ : R => ν v₀ ω w) ∂γ_sh ∂P₀| ≤
      B ^ (n + 2) * T (some (some i)) (some (some j)) := fun i j hj => by
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    refine key _ hss _ _ _ (fun w => ?_) fun w σ => ?_
    · exact ((hfm id).mul ((hXX i j).sub_const _)).mul
        (((hcomp w i _ (hψdm i)).mul (hcomp w j _ (hψdm j))).mul
          (Finset.measurable_prod _ fun r _ => hcomp w r _ (hψm r)))
    · have hk : 2 + 2 + ((Finset.univ.erase i).erase j).card ≤ n + 2 := by
        have h2 : 1 < (Finset.univ : Finset R).card :=
          Finset.one_lt_card.2 ⟨i, Finset.mem_univ i, j, Finset.mem_univ j, hij⟩
        rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ i), hn,
          ← Finset.card_univ]
        omega
      have hne : (some (some i) : Option (Option R)) ≠ some (some j) := fun h => hij (hss h)
      simp only [H, hne, reduceIte, add_zero]
      exact hfin _ _ _ _ (hmul _ _ _ _ (hmul _ _ _ _ (hψd1 i _) (hψd1 j _)) (hprodB _ _)) hk
  have hcard : ∀ i : R, 2 + (Finset.univ.erase i).card + 1 ≤ n + 2 := fun i => by
    have := Finset.card_pos.2 ⟨i, Finset.mem_univ i⟩
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), hn, ← Finset.card_univ]; omega
  have h3 : ∀ i : R, |∫ ω, ∫ w, ∫ σ : Option R → E × ℝ,
      f (fun r => (σ (some r)).1) * (X (σ (some i)).1 ⬝ᵥ X (σ none).1 - Y ⬝ᵥ Y) *
        ((deriv (ψ i) (S v₀ w (σ (some i))) +
            ψ i (S v₀ w (σ (some i))) * deriv u (S v₀ w (σ (some i)))) *
          ∏ r ∈ Finset.univ.erase i, ψ r (S v₀ w (σ (some r)))) *
        deriv u (S v₀ w (σ none))
      ∂(Measure.pi fun _ : Option R => ν v₀ ω w) ∂γ_sh ∂P₀| ≤
      B ^ (n + 2) * T (some (some i)) none := fun i => by
    refine key _ hos _ _ _ (fun w => ?_) fun w σ => ?_
    · exact (((hfm some).mul ((hXX (some i) none).sub_const _)).mul
        ((hcomp w (some i) _ (hψdm i)).mul
          (Finset.measurable_prod _ fun r _ => hcomp w (some r) _ (hψm r)))).mul
        (hcomp w none _ hu'm)
    · have hne : (some (some i) : Option (Option R)) ≠ none := Option.some_ne_none _
      simp only [H, hne, reduceIte, add_zero, Option.map_some, Option.map_none]
      rw [mul_assoc _ _ (deriv u _)]
      refine hfin _ _ _ _ (hmul _ _ _ 1 (hmul _ _ _ _ (hψd1 i _) (hprodB _ _)) ?_) (hcard i)
      rw [pow_one]; exact hD1B _
  have h4 : |∫ ω, ∫ w, ∫ σ : Option R → E × ℝ,
      f (fun r => (σ (some r)).1) * (X (σ none).1 ⬝ᵥ X (σ none).1 - (Y ⬝ᵥ Y + c_ξ ^ 2)) *
        (∏ r, ψ r (S v₀ w (σ (some r)))) *
        (deriv (deriv u) (S v₀ w (σ none)) + deriv u (S v₀ w (σ none)) ^ 2)
      ∂(Measure.pi fun _ : Option R => ν v₀ ω w) ∂γ_sh ∂P₀| ≤ B ^ (n + 2) * T none none := by
    refine key _ hos _ _ _ (fun w => ?_) fun w σ => ?_
    · exact (((hfm some).mul ((hXX none none).sub_const _)).mul
        (Finset.measurable_prod _ fun r _ => hcomp w (some r) _ (hψm r))).mul
        (hcomp w none _ hWm)
    · simp only [H, reduceIte, Option.map_some, Option.map_none]
      rw [mul_assoc _ _ (deriv (deriv u) _ + _)]
      exact hfin _ _ _ _ (hmul _ _ _ _ (hprodB _ _) (hW _)) (by rw [hn, Finset.card_univ])
  have h5 : ∀ j : R, |∫ ω, ∫ w, ∫ σ : Option R → E × ℝ,
      f (fun r => (σ (some r)).1) * (X (σ none).1 ⬝ᵥ X (σ (some j)).1 - Y ⬝ᵥ Y) *
        ((deriv (ψ j) (S v₀ w (σ (some j))) +
            ψ j (S v₀ w (σ (some j))) * deriv u (S v₀ w (σ (some j)))) *
          ∏ r ∈ Finset.univ.erase j, ψ r (S v₀ w (σ (some r)))) *
        deriv u (S v₀ w (σ none))
      ∂(Measure.pi fun _ : Option R => ν v₀ ω w) ∂γ_sh ∂P₀| ≤
      B ^ (n + 2) * T none (some (some j)) := fun j => by
    refine key _ hos _ _ _ (fun w => ?_) fun w σ => ?_
    · exact (((hfm some).mul ((hXX none (some j)).sub_const _)).mul
        ((hcomp w (some j) _ (hψdm j)).mul
          (Finset.measurable_prod _ fun r _ => hcomp w (some r) _ (hψm r)))).mul
        (hcomp w none _ hu'm)
    · have hne : (none : Option (Option R)) ≠ some (some j) := (Option.some_ne_none _).symm
      simp only [H, hne, reduceIte, add_zero, Option.map_some, Option.map_none]
      rw [mul_assoc _ _ (deriv u _)]
      refine hfin _ _ _ _ (hmul _ _ _ 1 (hmul _ _ _ _ (hψd1 j _) (hprodB _ _)) ?_) (hcard j)
      rw [pow_one]; exact hD1B _
  have h6 : |∫ ω, ∫ w, ∫ σ : Option (Option R) → E × ℝ,
      f (fun r => (σ (some (some r))).1) * (X (σ none).1 ⬝ᵥ X (σ (some none)).1 - Y ⬝ᵥ Y) *
        (∏ r, ψ r (S v₀ w (σ (some (some r))))) *
        deriv u (S v₀ w (σ none)) * deriv u (S v₀ w (σ (some none)))
      ∂(Measure.pi fun _ : Option (Option R) => ν v₀ ω w) ∂γ_sh ∂P₀| ≤
      B ^ (n + 2) * T none (some none) := by
    refine key id injective_id _ _ _ (fun w => ?_) fun w σ => ?_
    · exact ((((hfm fun r => some (some r)).mul ((hXX none (some none)).sub_const _)).mul
        (Finset.measurable_prod _ fun r _ => hcomp w (some (some r)) _ (hψm r))).mul
        (hcomp w none _ hu'm)).mul (hcomp w (some none) _ hu'm)
    · have hne : (none : Option (Option R)) ≠ some none := (Option.some_ne_none _).symm
      simp only [H, hne, reduceIte, add_zero, id_eq]
      rw [mul_assoc _ (deriv u _), mul_assoc _ _ (deriv u _ * _)]
      refine hfin _ _ _ _ (hmul _ _ _ (1 + 1) (hprodB _ _) (hmul _ _ 1 1 ?_ ?_))
        (by rw [hn, Finset.card_univ])
      · rw [pow_one]; exact hD1B _
      · rw [pow_one]; exact hD1B _
  -- collect the six groups
  have hT : ∀ a b, 0 ≤ T a b := fun a b =>
    integral_nonneg fun _ => integral_nonneg fun _ => integral_nonneg fun _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hBn : 0 ≤ B ^ (n + 2) := pow_nonneg hB0 _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpairs : (∑ i : R, T (some (some i)) (some (some i))) +
      (∑ i : R, ∑ j ∈ Finset.univ.erase i, T (some (some i)) (some (some j))) +
      (∑ i : R, T (some (some i)) none) + T none none + (∑ j : R, T none (some (some j))) +
      T none (some none) ≤ ∑ a, ∑ b, T a b := by
    have hrow : ∀ i : R, T (some (some i)) (some (some i)) +
        (∑ j ∈ Finset.univ.erase i, T (some (some i)) (some (some j))) +
        T (some (some i)) none ≤ ∑ b, T (some (some i)) b := fun i => by
      rw [Finset.add_sum_erase Finset.univ (fun j => T (some (some i)) (some (some j)))
        (Finset.mem_univ i), Fintype.sum_option, Fintype.sum_option]
      linarith [hT (some (some i)) (some none)]
    have hrows := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hrow i
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hrows
    have hmid : 0 ≤ ∑ b, T (some none) b := Finset.sum_nonneg fun b _ => hT _ _
    have hnone : T none none + (∑ j : R, T none (some (some j))) + T none (some none) =
        ∑ b, T none b := by
      rw [Fintype.sum_option, Fintype.sum_option]; ring
    rw [Fintype.sum_option (fun a => ∑ b, T a b),
      Fintype.sum_option (fun a => ∑ b, T (some a) b)]
    linarith
  have hscale : ∀ (c x t : ℝ), 0 ≤ c → c ≤ ((n : ℝ) + 1) ^ 2 → |x| ≤ B ^ (n + 2) * t → 0 ≤ t →
      |c * x| ≤ ((n : ℝ) + 1) ^ 2 * (B ^ (n + 2) * t) := fun c x t hc hcn hx ht => by
    rw [abs_mul, abs_of_nonneg hc]
    exact mul_le_mul hcn hx (abs_nonneg _) (by positivity)
  have hone : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith)
  have hnn : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hnn1 : (n : ℝ) * ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hsum : ∀ {ι : Type u} (s : Finset ι) (x t : ι → ℝ), (∀ i ∈ s, |x i| ≤ B ^ (n + 2) * t i) →
      |∑ i ∈ s, x i| ≤ B ^ (n + 2) * ∑ i ∈ s, t i := fun s x t h => by
    rw [Finset.mul_sum]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum h)
  have b1 := hscale 1 _ _ zero_le_one hone (hsum Finset.univ _ _ fun i _ => h1 i)
    (Finset.sum_nonneg fun _ _ => hT _ _)
  have b2 := hscale 1 _ _ zero_le_one hone
    (hsum Finset.univ _ _ fun i _ => hsum (Finset.univ.erase i) _ _ fun j hj => h2 i j hj)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hT _ _)
  have b3 := hscale n _ _ hn0 hnn (hsum Finset.univ _ _ fun i _ => h3 i)
    (Finset.sum_nonneg fun _ _ => hT _ _)
  have b4 := hscale n _ _ hn0 hnn h4 (hT _ _)
  have b5 := hscale n _ _ hn0 hnn (hsum Finset.univ _ _ fun j _ => h5 j)
    (Finset.sum_nonneg fun _ _ => hT _ _)
  have b6 := hscale (n * (n + 1)) _ _ (by positivity) hnn1 h6 (hT _ _)
  rw [one_mul] at b1 b2
  have htri : ∀ a b c d e g : ℝ, |(1 / 2) * (a + b - c - d - e + g)| ≤
      |a| + |b| + |c| + |d| + |e| + |g| := fun a b c d e g => by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    refine (mul_le_of_le_one_left (abs_nonneg _) (by norm_num)).trans ?_
    linarith [abs_add_le (a + b - c - d - e) g, abs_sub (a + b - c - d) e,
      abs_sub (a + b - c) d, abs_sub (a + b) c, abs_add_le a b]
  refine (htri _ _ _ _ _ _).trans ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hpairs
    (mul_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2) hBn))
  rw [mul_assoc (((n : ℝ) + 1) ^ 2)]
  refine (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add b1 b2) b3) b4) b5) b6).trans
    (le_of_eq ?_)
  ring

/-- **Continuity on `[0, 1]` of the disorder-averaged Gibbs expectation along the square-root
cavity path** (including the endpoints `v = 0` and `v = 1` where `√v` and `√(1 - v)` are continuous
but not differentiable). -/
theorem continuousOn_integral_integral_pi_tilted_prod_gaussianReal_sqrt
    {Ω : Type*} [MeasurableSpace Ω] (P₀ : Measure Ω) [Fintype K] [Fintype R]
    {κ : ℝ} (hκ : 0 < κ) {B₀ c₀ : Ω → ℝ} (hB₀ : ∀ ω, 0 ≤ B₀ ω)
    (hmom : ∀ deg : ℕ, Integrable (fun ω => (1 + B₀ ω + c₀ ω) ^ deg) P₀)
    {E₀ : Ω → E → ℝ} (hE₀m : Measurable fun p : Ω × E => E₀ p.1 p.2)
    (hE₀_conf : ∀ ω x, E₀ ω x ≤ B₀ ω * ‖x‖ - κ * ‖x‖ ^ 2)
    (hE₀_low : ∀ ω x, ‖x‖ ≤ 1 → -c₀ ω ≤ E₀ ω x)
    (X : E → K → ℝ) (Y : K → ℝ) (hXm : ∀ k, Measurable fun x => X x k)
    {L_X : ℝ} {n_X : ℕ} (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X)
    (c_ξ : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0)
    {D₁ : ℝ} (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (ψ : R → ℝ → ℝ) (hψc : ∀ r, Continuous (ψ r)) {M₀ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀)
    {f : (R → E) → ℝ} (hf : Measurable f) {C_f : ℝ} {m_f : ℕ}
    (hfb : ∀ a, |f a| ≤ C_f * ∏ r, (1 + ‖a r‖) ^ m_f) :
    let γ_sh := Measure.pi fun _ : K => gaussianReal 0 1
    let S (v : ℝ) (w : K → ℝ) (p : E × ℝ) : ℝ :=
      Real.sqrt v * (X p.1 ⬝ᵥ w) + Real.sqrt (1 - v) * (Y ⬝ᵥ w + c_ξ * p.2)
    let ν (v : ℝ) (ω : Ω) (w : K → ℝ) : Measure (E × ℝ) :=
      (μ.prod (gaussianReal 0 1)).tilted (fun p => E₀ ω p.1 + u (S v w p))
    ContinuousOn
      (fun v => ∫ ω, ∫ w, ∫ σ : R → E × ℝ, f (fun r => (σ r).1) * ∏ r, ψ r (S v w (σ r))
        ∂(Measure.pi fun _ : R => ν v ω w) ∂γ_sh ∂P₀)
      (Icc 0 1) := by
  intro γ_sh S ν v₀ _
  have hum : Measurable u := hu.continuous.measurable
  have huc : Continuous u := hu.continuous
  have hc₀ : ∀ ω, 0 ≤ c₀ ω := fun ω => nonneg_of_confining_of_neg_le (hE₀_conf ω) (hE₀_low ω)
  set C_tot : ℝ := |C_f| * |M₀| ^ Fintype.card R
  have hCtot0 : 0 ≤ C_tot := by positivity
  set G_v : ℝ → (K → ℝ) → (R → E × ℝ) → ℝ :=
    fun v w σ => f (fun r => (σ r).1) * ∏ r, ψ r (S v w (σ r))
  have hGvm : ∀ v, Measurable fun p : (K → ℝ) × (R → E × ℝ) => G_v v p.1 p.2 := fun v => by
    have h1 : Measurable fun p : (K → ℝ) × (R → E × ℝ) => f (fun r => (p.2 r).1) :=
      hf.comp (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
    have hS_m : ∀ r : R, Measurable fun p : (K → ℝ) × (R → E × ℝ) => S v p.1 (p.2 r) := fun r => by
      have hdot : Measurable fun p : (K → ℝ) × (R → E × ℝ) => X (p.2 r).1 ⬝ᵥ p.1 :=
        Finset.measurable_sum _ fun k _ =>
          ((hXm k).comp (measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))).mul
            ((measurable_pi_apply k).comp measurable_fst)
      have hYdot : Measurable fun p : (K → ℝ) × (R → E × ℝ) => Y ⬝ᵥ p.1 :=
        Finset.measurable_sum _ fun k _ =>
          measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)
      have h2 : Measurable fun p : (K → ℝ) × (R → E × ℝ) => Y ⬝ᵥ p.1 + c_ξ * (p.2 r).2 :=
        hYdot.add
          ((measurable_snd.comp ((measurable_pi_apply r).comp measurable_snd)).const_mul c_ξ)
      exact (hdot.const_mul _).add (h2.const_mul _)
    exact h1.mul (Finset.measurable_prod _ fun r _ => (hψc r).measurable.comp (hS_m r))
  have hGvb : ∀ v w σ, |G_v v w σ| ≤ C_tot * ∏ r, (1 + ‖σ r‖) ^ m_f := fun v w σ => by
    dsimp only [G_v, C_tot]
    rw [abs_mul]
    have h1 : |f (fun r => (σ r).1)| ≤ |C_f| * ∏ r, (1 + ‖σ r‖) ^ m_f :=
      abs_comp_le_prod_of_injective hfb norm_fst_le injective_id σ
    have h2 : |∏ r, ψ r (S v w (σ r))| ≤ |M₀| ^ Fintype.card R :=
      Finset.univ.abs_prod_le_pow_card fun r _ => (hM₀ r _).trans (le_abs_self _)
    exact (mul_le_mul h1 h2 (abs_nonneg _)
      (mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun _ _ => by positivity))).trans_eq (by ring)
  -- 1. Continuity at fixed `(ω, w)`
  have hpt_vw : ∀ ω (w : K → ℝ), ContinuousWithinAt
      (fun v => ∫ σ : R → E × ℝ, G_v v w σ ∂(Measure.pi fun _ : R => ν v ω w)) (Icc 0 1) v₀ := by
    intro ω w
    have hEω : Measurable (E₀ ω) := hE₀m.comp (measurable_const.prodMk measurable_id)
    set μ₁ := μ.prod (gaussianReal 0 1)
    set μ_R := Measure.pi fun _ : R => μ₁
    set e_vw : ℝ → E × ℝ → ℝ := fun v p => E₀ ω p.1 + u (S v w p)
    have hem : ∀ v, Measurable (e_vw v) := fun v => by
      have hSv : Measurable (S v w) := by
        have h1 : Measurable fun p : E × ℝ => X p.1 ⬝ᵥ w :=
          Finset.measurable_sum _ fun k _ => ((hXm k).comp measurable_fst).mul_const (w k)
        have h2 : Measurable fun p : E × ℝ => Y ⬝ᵥ w + c_ξ * p.2 :=
          measurable_const.add (measurable_snd.const_mul c_ξ)
        exact (h1.const_mul _).add (h2.const_mul _)
      exact (hEω.comp measurable_fst).add (hum.comp hSv)
    have hdom_1 : ∀ m : ℕ, Integrable (fun p : E × ℝ => (1 + ‖p‖) ^ m * Real.exp (E₀ ω p.1)) μ₁ :=
      fun m => by
        have h_x : Integrable (fun x : E => (1 + ‖x‖) ^ m *
            Real.exp (B₀ ω * ‖x‖ - κ * ‖x‖ ^ 2)) μ :=
          integrable_one_add_norm_pow_mul_exp (μ := μ) hκ (B₀ ω) m
        have h_ξ : Integrable (fun ξ : ℝ => (1 + |ξ|) ^ m) (gaussianReal 0 1) := by
          have hm1 : MemLp (fun ξ : ℝ => 1 + |ξ|) m (gaussianReal 0 1) :=
            (memLp_const 1).add (memLp_id_gaussianReal m).abs
          exact hm1.integrable_norm_pow'.congr (ae_of_all _ fun ξ => by
            change ‖1 + |ξ|‖ ^ m = (1 + |ξ|) ^ m
            rw [Real.norm_of_nonneg (by positivity)])
        have hprod := h_x.mul_prod h_ξ
        refine hprod.mono' (((measurable_const.add measurable_norm).pow_const m).mul
          (hEω.comp measurable_fst).exp).aestronglyMeasurable (ae_of_all _ fun p => ?_)
        rw [Real.norm_of_nonneg (by positivity)]
        have hp_norm : 1 + ‖p‖ ≤ (1 + ‖p.1‖) * (1 + |p.2|) := by
          have hmax : ‖p‖ ≤ ‖p.1‖ + |p.2| := by
            change max ‖p.1‖ ‖p.2‖ ≤ ‖p.1‖ + |p.2|
            rw [Real.norm_eq_abs]
            exact max_le (le_add_of_nonneg_right (abs_nonneg _))
              (le_add_of_nonneg_left (norm_nonneg _))
          nlinarith [norm_nonneg p.1, abs_nonneg p.2]
        have hpow := pow_le_pow_left₀ (by positivity) hp_norm m
        have hexp : Real.exp (E₀ ω p.1) ≤ Real.exp (B₀ ω * ‖p.1‖ - κ * ‖p.1‖ ^ 2) :=
          Real.exp_le_exp.2 (hE₀_conf ω p.1)
        calc (1 + ‖p‖) ^ m * Real.exp (E₀ ω p.1)
            ≤ ((1 + ‖p.1‖) * (1 + |p.2|)) ^ m * Real.exp (B₀ ω * ‖p.1‖ - κ * ‖p.1‖ ^ 2) :=
              mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
          _ = ((1 + ‖p.1‖) ^ m * Real.exp (B₀ ω * ‖p.1‖ - κ * ‖p.1‖ ^ 2)) * (1 + |p.2|) ^ m := by
              rw [mul_pow]; ring
    have hnum_c : ∀ {Φ : ℝ → (R → E × ℝ) → ℝ} {C_Φ : ℝ} {m : ℕ},
        (∀ v, Measurable (Φ v)) → (∀ σ, Continuous fun v => Φ v σ) →
        (∀ v σ, |Φ v σ| ≤ C_Φ * ∏ r, (1 + ‖σ r‖) ^ m) →
        ContinuousWithinAt
          (fun v => ∫ σ : R → E × ℝ, Φ v σ * Real.exp (∑ r, e_vw v (σ r)) ∂μ_R) (Icc 0 1) v₀ := by
      intro Φ C_Φ m hΦm hΦc hΦb
      set b_R : (R → E × ℝ) → ℝ := fun σ => |C_Φ| * ∏ r, (1 + ‖σ r‖) ^ m * Real.exp (E₀ ω (σ r).1)
      have hb_int : Integrable b_R μ_R :=
        (Integrable.fintype_prod (f := fun _ : R => fun p : E × ℝ =>
          (1 + ‖p‖) ^ m * Real.exp (E₀ ω p.1)) fun _ => hdom_1 m).const_mul |C_Φ|
      refine continuousWithinAt_of_dominated
        (F := fun v σ => Φ v σ * Real.exp (∑ r, e_vw v (σ r))) (bound := b_R)
        (Eventually.of_forall fun v =>
          ((hΦm v).mul (Finset.measurable_sum _ fun r _ =>
            (hem v).comp (measurable_pi_apply r)).exp).aestronglyMeasurable)
        (Eventually.of_forall fun v => ae_of_all _ fun σ => ?_) hb_int (ae_of_all _ fun σ => ?_)
      · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), Real.exp_sum]
        have h1 : |Φ v σ| ≤ |C_Φ| * ∏ r, (1 + ‖σ r‖) ^ m :=
          (hΦb v σ).trans (mul_le_mul_of_nonneg_right (le_abs_self _)
            (Finset.prod_nonneg fun _ _ => by positivity))
        have h2 : ∏ r, Real.exp (e_vw v (σ r)) ≤ ∏ r, Real.exp (E₀ ω (σ r).1) :=
          Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) fun r _ =>
            Real.exp_le_exp.2 (add_le_of_nonpos_right (hu0 _))
        refine (mul_le_mul h1 h2 (by positivity) (by positivity)).trans_eq ?_
        dsimp only [b_R]; rw [mul_assoc, Finset.prod_mul_distrib]
      · have hc_fn : Continuous fun v : ℝ => Φ v σ * Real.exp (∑ r, e_vw v (σ r)) := by
          refine (hΦc σ).mul ?_
          dsimp only [e_vw, S]; fun_prop
        exact hc_fn.continuousWithinAt
    have hc_num := hnum_c (Φ := fun v => G_v v w)
      (fun v => (hGvm v).comp (measurable_const.prodMk measurable_id))
      (fun σ => by
        dsimp only [G_v, S]
        fun_prop)
      (fun v => hGvb v w)
    have hc_den := hnum_c (Φ := fun _ _ => (1 : ℝ)) (C_Φ := 1) (m := 0)
      (fun _ => measurable_const) (fun _ => continuous_const) (fun _ _ => by simp)
    simp only [one_mul] at hc_den
    have hZ_pos : 0 < ∫ σ : R → E × ℝ, Real.exp (∑ r, e_vw v₀ (σ r)) ∂μ_R := by
      rw [integral_pi_exp_sum (μ := μ₁)]
      refine pow_pos (integral_exp_pos ?_) _
      refine (hdom_1 0).mono' (hem v₀).exp.aestronglyMeasurable (ae_of_all _ fun p => ?_)
      simp only [pow_zero, one_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.2 (add_le_of_nonpos_right (hu0 _))
    have heq : (fun v => ∫ σ : R → E × ℝ, G_v v w σ ∂(Measure.pi fun _ : R => ν v ω w)) =
        fun v => (∫ σ : R → E × ℝ, G_v v w σ * Real.exp (∑ r, e_vw v (σ r)) ∂μ_R) /
          ∫ σ : R → E × ℝ, Real.exp (∑ r, e_vw v (σ r)) ∂μ_R := by
      funext v; rw [pi_tilted_eq_tilted_pi, integral_tilted_eq_div]
    rw [heq]
    exact hc_num.div hc_den hZ_pos.ne'
  -- 2. Dominated convergence over `w` (`γ_sh`) for each `ω`
  obtain ⟨A_m, hAm0, hIm⟩ :=
    exists_integrable_and_abs_le_integral_pi_tilted_prod_gaussianReal (K := K) (ι := R) μ hκ m_f
  set s_Y : ℝ := ∑ k : K, |Y k|
  have hsY0 : 0 ≤ s_Y := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set s_A : ℝ := |L_X| * 2 ^ n_X + s_Y
  have hs_A : 0 ≤ s_A := by positivity
  set deg : ℕ := m_f * Fintype.card R
  set W_fac : (K → ℝ) → ℝ := fun w =>
    1 + |u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_ξ|) + 1 / 2
  have hWfac_int : Integrable (fun w => W_fac w ^ deg) γ_sh :=
    (integrable_const_add_mul_sum_abs_pow_pi_gaussianReal
      (1 + |u 0| + |D₁| * |c_ξ| + 1 / 2) (|D₁| * s_A) deg).congr
      (ae_of_all _ fun w => by dsimp only [W_fac]; ring)
  have hpt_ω : ∀ ω, ContinuousWithinAt
      (fun v => ∫ w, ∫ σ : R → E × ℝ, G_v v w σ ∂(Measure.pi fun _ : R => ν v ω w) ∂γ_sh)
      (Icc 0 1) v₀ := by
    intro ω
    have hEω_m : Measurable (E₀ ω) := hE₀m.comp (measurable_const.prodMk measurable_id)
    set b_w : (K → ℝ) → ℝ := fun w =>
      (C_tot * A_m ^ Fintype.card R * (1 + B₀ ω + c₀ ω) ^ deg) * W_fac w ^ deg
    have hbw_int : Integrable b_w γ_sh := hWfac_int.const_mul _
    have hw_meas_bd : ∀ v ∈ Icc (0 : ℝ) 1,
        AEStronglyMeasurable
          (fun w => ∫ σ : R → E × ℝ, G_v v w σ ∂(Measure.pi fun _ : R => ν v ω w)) γ_sh ∧
        ∀ w, |∫ σ : R → E × ℝ, G_v v w σ ∂(Measure.pi fun _ : R => ν v ω w)| ≤ b_w w := by
      rintro v ⟨hv0_l, hv1_u⟩
      set A_v : E → K → ℝ := fun x k => Real.sqrt v * X x k + Real.sqrt (1 - v) * Y k
      set c_v : ℝ := Real.sqrt (1 - v) * c_ξ
      have hS_Av : ∀ w p, S v w p = A_v p.1 ⬝ᵥ w + c_v * p.2 := fun w p => by
        dsimp only [S, A_v, c_v, dotProduct]
        simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
        ring
      have hAvm : ∀ k, Measurable fun x => A_v x k := fun k =>
        ((hXm k).const_mul _).add measurable_const
      have hAv_low : ∀ k x, ‖x‖ ≤ 1 → |A_v x k| ≤ s_A :=
        abs_sqrt_path_coeff_le_of_norm_le_one hXb Y hv0_l hv1_u
      have hcv_le : |c_v| ≤ |c_ξ| := by
        dsimp only [c_v]
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact mul_le_of_le_one_left (abs_nonneg _) (Real.sqrt_le_one.2 (by linarith))
      have hres := hIm (hB₀ ω) (hc₀ ω) hEω_m (hE₀_conf ω) (hE₀_low ω) A_v hAvm hs_A hAv_low c_v
        hu hu0 hD₁ (hGvm v) hCtot0 le_rfl
        (fun w σ => by simpa only [zero_mul, add_zero] using hGvb v w σ)
      have hν_Av : ∀ w, ν v ω w = (μ.prod (gaussianReal 0 1)).tilted
          (fun p => E₀ ω p.1 + u (A_v p.1 ⬝ᵥ w + c_v * p.2)) := by
        intro w; dsimp only [ν]; simp_rw [hS_Av]
      refine ⟨by simpa only [← hν_Av] using hres.2.aestronglyMeasurable, fun w => ?_⟩
      have hw1 := hres.1 w
      simp only [zero_mul, add_zero, ← hν_Av w] at hw1
      refine hw1.trans ?_
      have hbase_prod :
          1 + B₀ ω + (c₀ ω + (|u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_v|)) + 1 / 2) ≤
          (1 + B₀ ω + c₀ ω) * W_fac w := by
        dsimp only [W_fac]
        have hw_nn : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        have hBc : 0 ≤ B₀ ω + c₀ ω := add_nonneg (hB₀ ω) (hc₀ ω)
        have hU_nn : 0 ≤ |u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_ξ|) + 1 / 2 := by positivity
        have hcv_d := mul_le_mul_of_nonneg_left hcv_le (abs_nonneg D₁)
        nlinarith [mul_nonneg hBc hU_nn]
      have hpow_le := pow_le_pow_left₀ (by
        have : 0 ≤ ∑ k, |w k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        have := hB₀ ω; have := hc₀ ω; positivity) hbase_prod deg
      rw [mul_pow] at hpow_le
      calc C_tot * A_m ^ Fintype.card R *
              (1 + B₀ ω + (c₀ ω + (|u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_v|)) + 1 / 2)) ^ deg
          ≤ C_tot * A_m ^ Fintype.card R * ((1 + B₀ ω + c₀ ω) ^ deg * W_fac w ^ deg) :=
            mul_le_mul_of_nonneg_left hpow_le (by positivity)
        _ = b_w w := by dsimp only [b_w]; ring
    exact continuousWithinAt_of_dominated (bound := b_w)
      (eventually_nhdsWithin_of_forall fun v hv => (hw_meas_bd v hv).1)
      (eventually_nhdsWithin_of_forall fun v hv => ae_of_all _ fun w =>
        (Real.norm_eq_abs _).trans_le ((hw_meas_bd v hv).2 w))
      hbw_int (ae_of_all _ fun w => hpt_vw ω w)
  -- 3. Dominated convergence over `ω` (`P₀`)
  obtain ⟨C_dom, hCdom0, hJ⟩ := measurable_and_abs_le_integral_w_pi_tilted_prod_gaussianReal
    (ι := R) μ P₀ hκ hB₀ hc₀ hmom hE₀m hE₀_conf hE₀_low X Y hXm hXb c_ξ hu hu0 hD₁ m_f
  exact continuousWithinAt_of_dominated
    (bound := fun ω => C_tot * C_dom * (1 + B₀ ω + c₀ ω) ^ deg)
    (eventually_nhdsWithin_of_forall fun v hv =>
      (hJ hv.1 hv.2 (hGvm v) hCtot0 (hGvb v)).1.aestronglyMeasurable)
    (eventually_nhdsWithin_of_forall fun v hv => ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      exact (hJ hv.1 hv.2 (hGvm v) hCtot0 (hGvb v)).2.1 ω)
    ((hmom deg).const_mul _)
    (ae_of_all _ hpt_ω)

/-- **Joint integrability on `P₀.prod γ_sh`** of the quenched replica average at `v ∈ [0, 1]`, for
Fubini between `P₀` and `γ_sh`. -/
theorem integrable_prod_pi_tilted_prod_gaussianReal_sqrt
    {Ω ι : Type*} [MeasurableSpace Ω] (P₀ : Measure Ω) [Fintype K] [Fintype ι]
    {κ : ℝ} (hκ : 0 < κ) {B₀ c₀ : Ω → ℝ} (hB₀ : ∀ ω, 0 ≤ B₀ ω)
    (hmom : ∀ deg : ℕ, Integrable (fun ω => (1 + B₀ ω + c₀ ω) ^ deg) P₀)
    {E₀ : Ω → E → ℝ} (hE₀m : Measurable fun p : Ω × E => E₀ p.1 p.2)
    (hE₀_conf : ∀ ω x, E₀ ω x ≤ B₀ ω * ‖x‖ - κ * ‖x‖ ^ 2)
    (hE₀_low : ∀ ω x, ‖x‖ ≤ 1 → -c₀ ω ≤ E₀ ω x)
    (X : E → K → ℝ) (Y : K → ℝ) (hXm : ∀ k, Measurable fun x => X x k)
    {L_X : ℝ} {n_X : ℕ} (hXb : ∀ k x, |X x k| ≤ L_X * (1 + ‖x‖) ^ n_X)
    (c_ξ : ℝ) {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu0 : ∀ x, u x ≤ 0)
    {D₁ : ℝ} (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    {G : (K → ℝ) → (ι → E × ℝ) → ℝ}
    (hGm : Measurable fun p : (K → ℝ) × (ι → E × ℝ) => G p.1 p.2)
    {C_G : ℝ} {m : ℕ} (hGb : ∀ w σ, |G w σ| ≤ C_G * ∏ o, (1 + ‖σ o‖) ^ m) :
    let γ_sh := Measure.pi fun _ : K => gaussianReal 0 1
    let S (w : K → ℝ) (p : E × ℝ) : ℝ :=
      Real.sqrt v * (X p.1 ⬝ᵥ w) + Real.sqrt (1 - v) * (Y ⬝ᵥ w + c_ξ * p.2)
    Integrable
      (fun p : Ω × (K → ℝ) => ∫ σ : ι → E × ℝ, G p.2 σ
        ∂(Measure.pi fun _ : ι =>
          (μ.prod (gaussianReal 0 1)).tilted fun q => E₀ p.1 q.1 + u (S p.2 q)))
      (P₀.prod γ_sh) := by
  intro γ_sh S
  have hum : Measurable u := hu.continuous.measurable
  have hc₀ : ∀ ω, 0 ≤ c₀ ω := fun ω => nonneg_of_confining_of_neg_le (hE₀_conf ω) (hE₀_low ω)
  have hGb' : ∀ w σ, |G w σ| ≤ |C_G| * ∏ o, (1 + ‖σ o‖) ^ m := fun w σ =>
    (hGb w σ).trans (mul_le_mul_of_nonneg_right (le_abs_self _)
      (Finset.prod_nonneg fun _ _ => by positivity))
  set A_v : E → K → ℝ := fun x k => Real.sqrt v * X x k + Real.sqrt (1 - v) * Y k
  set c_v : ℝ := Real.sqrt (1 - v) * c_ξ
  have hS_Av : ∀ w p, S w p = A_v p.1 ⬝ᵥ w + c_v * p.2 := fun w p => by
    dsimp only [S, A_v, c_v, dotProduct]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  have hAvm : ∀ k, Measurable fun x => A_v x k := fun k =>
    ((hXm k).const_mul _).add measurable_const
  set s_Y : ℝ := ∑ k : K, |Y k|
  have hsY0 : 0 ≤ s_Y := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set s_A : ℝ := |L_X| * 2 ^ n_X + s_Y
  have hs_A : 0 ≤ s_A := by positivity
  have hAv_low : ∀ k x, ‖x‖ ≤ 1 → |A_v x k| ≤ s_A :=
    abs_sqrt_path_coeff_le_of_norm_le_one hXb Y hv0 hv1
  set H_fn : Ω × (K → ℝ) → ℝ := fun p => ∫ σ : ι → E × ℝ, G p.2 σ
    ∂(Measure.pi fun _ : ι =>
      (μ.prod (gaussianReal 0 1)).tilted fun q => E₀ p.1 q.1 + u (S p.2 q))
  have hHm : Measurable H_fn := by
    have hν_eq : ∀ ω w,
        (μ.prod (gaussianReal 0 1)).tilted (fun q : E × ℝ => E₀ ω q.1 + u (S w q)) =
        (μ.prod (volume : Measure ℝ)).tilted
          (fun q : E × ℝ => E₀ ω q.1 + u (S w q) - q.2 ^ 2 / 2) :=
      fun _ _ => tilted_prod_gaussianReal_zero_one μ _
    have he_joint : Measurable fun q : (Ω × (K → ℝ)) × (E × ℝ) =>
        E₀ q.1.1 q.2.1 + u (S q.1.2 q.2) - q.2.2 ^ 2 / 2 := by
      have hE1 : Measurable fun q : (Ω × (K → ℝ)) × (E × ℝ) => E₀ q.1.1 q.2.1 :=
        hE₀m.comp ((measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))
      have hS1 : Measurable fun q : (Ω × (K → ℝ)) × (E × ℝ) => S q.1.2 q.2 := by
        simp_rw [hS_Av]
        have hdot : Measurable fun q : (Ω × (K → ℝ)) × (E × ℝ) => A_v q.2.1 ⬝ᵥ q.1.2 :=
          Finset.measurable_sum _ fun k _ =>
            ((hAvm k).comp (measurable_fst.comp measurable_snd)).mul
              ((measurable_pi_apply k).comp (measurable_snd.comp measurable_fst))
        exact hdot.add ((measurable_snd.comp measurable_snd).const_mul c_v)
      exact (hE1.add (hum.comp hS1)).sub
        (((measurable_snd.comp measurable_snd).pow_const 2).div_const 2)
    have hH_eq : H_fn = fun p => ∫ σ : ι → E × ℝ, G p.2 σ
        ∂(Measure.pi fun _ : ι =>
          (μ.prod (volume : Measure ℝ)).tilted
            (fun q => E₀ p.1 q.1 + u (S p.2 q) - q.2 ^ 2 / 2)) := by
      funext p; dsimp only [H_fn]; simp_rw [hν_eq p.1 p.2]
    rw [hH_eq]
    exact measurable_integral_pi_tilted_of_sigmaFinite
      (μ' := μ.prod (volume : Measure ℝ)) he_joint
      (hGm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  obtain ⟨A_m, hAm0, hIm⟩ :=
    exists_integrable_and_abs_le_integral_pi_tilted_prod_gaussianReal (K := K) (ι := ι) μ hκ m
  set deg : ℕ := m * Fintype.card ι
  set W_fac : (K → ℝ) → ℝ := fun w =>
    1 + |u 0| + |D₁| * (s_A * (∑ k, |w k|) + |c_v|) + 1 / 2
  have hWfac_int : Integrable (fun w => W_fac w ^ deg) γ_sh :=
    (integrable_const_add_mul_sum_abs_pow_pi_gaussianReal
      (1 + |u 0| + |D₁| * |c_v| + 1 / 2) (|D₁| * s_A) deg).congr
      (ae_of_all _ fun w => by dsimp only [W_fac]; ring)
  have hdom_prod : Integrable
      (fun p : Ω × (K → ℝ) =>
        (|C_G| * A_m ^ Fintype.card ι) * ((1 + B₀ p.1 + c₀ p.1) ^ deg * W_fac p.2 ^ deg))
      (P₀.prod γ_sh) :=
    ((hmom deg).mul_prod hWfac_int).const_mul _
  refine hdom_prod.mono' hHm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs]
  have hEω_m : Measurable (E₀ p.1) := hE₀m.comp (measurable_const.prodMk measurable_id)
  have hw1 := (hIm (hB₀ p.1) (hc₀ p.1) hEω_m (hE₀_conf p.1) (hE₀_low p.1)
    A_v hAvm hs_A hAv_low c_v hu hu0 hD₁ hGm (abs_nonneg C_G) le_rfl
    (fun w σ => by simpa only [zero_mul, add_zero] using hGb' w σ)).1 p.2
  simp only [zero_mul, add_zero, ← hS_Av] at hw1
  refine hw1.trans ?_
  have hbase_prod :
      1 + B₀ p.1 + (c₀ p.1 + (|u 0| + |D₁| * (s_A * (∑ k, |p.2 k|) + |c_v|)) + 1 / 2) ≤
      (1 + B₀ p.1 + c₀ p.1) * W_fac p.2 := by
    dsimp only [W_fac]
    have hw_nn : 0 ≤ ∑ k, |p.2 k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hBc : 0 ≤ B₀ p.1 + c₀ p.1 := add_nonneg (hB₀ p.1) (hc₀ p.1)
    have hU_nn : 0 ≤ |u 0| + |D₁| * (s_A * (∑ k, |p.2 k|) + |c_v|) + 1 / 2 := by positivity
    nlinarith [mul_nonneg hBc hU_nn]
  have hpow_le := pow_le_pow_left₀ (by
    have : 0 ≤ ∑ k, |p.2 k| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have := hB₀ p.1; have := hc₀ p.1; positivity) hbase_prod deg
  rw [mul_pow] at hpow_le
  exact (mul_le_mul_of_nonneg_left hpow_le (by positivity)).trans_eq (by ring)

end MeasureTheory
