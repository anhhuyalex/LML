/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Gaussian.GaussianTiltedSteinRatio
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaComparison
public import LeanMachineLearning.ForMathlib.MeasureTheory.Function.AEStronglyMeasurableDeriv
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IteratedHolder
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Disorder-averaged rotation derivative and Hölder bounds for replica Gibbs states

Model-free tools averaging the Gaussian rotation derivative-and-integration-by-parts identity
`hasDerivAt_integral_gaussian_tilted_rotation_ibp` over an arbitrary outer probability space
`(Ω₀, P₀)` of old disorders, and bounding the resulting replica pair averages by Hölder's
inequality (both for interior conjugate exponents `Real.HolderConjugate p q` and for the endpoints
`(1, ∞)` and `(∞, 1)`).

No uniform deterministic bound is imposed on the random old-system observable `f`: only
`L¹`-integrability under the old Gibbs law is needed for differentiation under the outer integral,
and only the indicated `L^p` (or a.e. essential-supremum) moment is needed for the Hölder step.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace SpinGlasses

/-- **`A ^ (1 / p)` is in `L^p` when `A ≥ 0` is integrable.** -/
theorem memLp_rpow_inv_of_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : Ω → ℝ} {p : ℝ} (hp : 0 < p) (hA0 : ∀ ω, 0 ≤ A ω) (hA : Integrable A P) :
    MemLp (fun ω => A ω ^ (1 / p)) (ENNReal.ofReal p) P := by
  have hm : AEStronglyMeasurable (fun ω => A ω ^ (1 / p)) P :=
    (hA.aestronglyMeasurable.aemeasurable.pow_const _).aestronglyMeasurable
  refine (integrable_norm_rpow_iff hm (by positivity) ENNReal.ofReal_ne_top).mp ?_
  rw [ENNReal.toReal_ofReal hp.le]
  refine hA.congr (ae_of_all _ fun ω => ?_)
  dsimp only
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (hA0 ω) _), ← Real.rpow_mul (hA0 ω),
    one_div_mul_cancel hp.ne', Real.rpow_one]

/-- **The rotated field `cos s * X + sin s * Y` is measurable** in the old state and the auxiliary
Gaussian coordinates, when the old state enters only through a finite label `π`. -/
theorem measurable_rotation_field {α L K_sh K_aux : Type*} [MeasurableSpace α]
    [Finite L] [MeasurableSpace L] [MeasurableSingletonClass L] [Fintype K_sh] [Fintype K_aux]
    {π : α → L} (hπ : Measurable π) (X_sh Y_sh : L → K_sh → ℝ) (X_aux Y_aux : L → K_aux → ℝ)
    (s : ℝ) (w : K_sh → ℝ) :
    Measurable fun q : α × (K_aux → ℝ) =>
      Real.cos s * (X_sh (π q.1) ⬝ᵥ w + X_aux (π q.1) ⬝ᵥ q.2) +
        Real.sin s * (Y_sh (π q.1) ⬝ᵥ w + Y_aux (π q.1) ⬝ᵥ q.2) := by
  have h1 : ∀ (F : L → K_sh → ℝ) (k : K_sh),
      Measurable fun q : α × (K_aux → ℝ) => F (π q.1) k := fun F k =>
    (measurable_of_finite fun m => F m k).comp (hπ.comp measurable_fst)
  have h2 : ∀ (F : L → K_aux → ℝ) (k : K_aux),
      Measurable fun q : α × (K_aux → ℝ) => F (π q.1) k := fun F k =>
    (measurable_of_finite fun m => F m k).comp (hπ.comp measurable_fst)
  simp only [dotProduct]
  have := fun k => h1 X_sh k
  have := fun k => h1 Y_sh k
  have := fun k => h2 X_aux k
  have := fun k => h2 Y_aux k
  fun_prop

/-- Tilted replica integral of `f(σ ∘ e).1 * H σ` bounded by `M_H * exp(2 |ι| B)` times the
`L¹`-norm of `f` under the untitled product law `pi μ₀`. -/
theorem abs_integral_pi_tilted_prod_fst_mul_le
    {α β R ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [Fintype R] [Fintype ι]
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (γ : Measure β) [IsProbabilityMeasure γ]
    {V : α × β → ℝ} (hVm : Measurable V) {B : ℝ} (hVb : ∀ q, |V q| ≤ B)
    {e : R → ι} (he : Function.Injective e)
    {f : (R → α) → ℝ} (hfi : Integrable f (Measure.pi fun _ : R => μ₀))
    (H : (ι → α × β) → ℝ) {M_H : ℝ} (hMH0 : 0 ≤ M_H) (hHb : ∀ σ, |H σ| ≤ M_H) :
    |∫ σ : ι → α × β, f (fun r => (σ (e r)).1) * H σ
      ∂(Measure.pi fun _ : ι => (μ₀.prod γ).tilted V)| ≤
    M_H * Real.exp (2 * (Fintype.card ι : ℝ) * B) *
      ∫ a, |f a| ∂(Measure.pi fun _ : R => μ₀) := by
  have : IsProbabilityMeasure ((μ₀.prod γ).tilted V) :=
    isProbabilityMeasure_tilted_of_ae_le hVm.aemeasurable
      (ae_of_all _ fun q => le_of_abs_le (hVb q))
  have hmp_prod := measurePreserving_arrowProdEquivProdArrow α β ι (fun _ => μ₀) (fun _ => γ)
  have hmp_e := measurePreserving_pi_comp_injective μ₀ he
  have hf_a : Integrable (fun a : ι → α => |f (fun r => a (e r))|)
      (Measure.pi fun _ : ι => μ₀) :=
    hmp_e.integrable_comp_of_integrable hfi.abs
  have hf_prod : Integrable (fun p : (ι → α) × (ι → β) => |f (fun r => p.1 (e r))|)
      ((Measure.pi fun _ : ι => μ₀).prod (Measure.pi fun _ : ι => γ)) :=
    hf_a.comp_fst (Measure.pi fun _ : ι => γ)
  have hf_ι : Integrable (fun σ : ι → α × β => |f (fun r => (σ (e r)).1)|)
      (Measure.pi fun _ : ι => μ₀.prod γ) :=
    hmp_prod.integrable_comp_of_integrable
      (g := fun p : (ι → α) × (ι → β) => |f (fun r => p.1 (e r))|) hf_prod
  have hf_ι_int : ∫ σ : ι → α × β, |f (fun r => (σ (e r)).1)|
      ∂(Measure.pi fun _ : ι => μ₀.prod γ) =
      ∫ a, |f a| ∂(Measure.pi fun _ : R => μ₀) := by
    have h1 := integral_pi_prod_mul (ι := ι) μ₀ γ
      (fun a => |f (fun r => a (e r))|) (fun _ => 1)
    simp only [mul_one, integral_const, probReal_univ, one_smul] at h1
    exact h1.trans (integral_pi_comp_injective μ₀ he (fun a => |f a|) hfi.abs.aestronglyMeasurable)
  have hcomp := integral_pi_tilted_le_exp_mul_of_abs_sub_le (ι := ι) (μ := μ₀.prod γ)
    (E₀ := 0) (E₁ := V) (by simp) (by simpa using hVm)
    (C := B) (fun q => by simpa using hVb q)
    (Y := fun σ : ι → α × β => |f (fun r => (σ (e r)).1)|)
    (fun _ => abs_nonneg _) (by simpa [tilted_zero] using hf_ι)
  simp only [tilted_zero, hf_ι_int] at hcomp
  have hf_tilt : Integrable (fun σ : ι → α × β => |f (fun r => (σ (e r)).1)|)
      (Measure.pi fun _ : ι => (μ₀.prod γ).tilted V) := by
    have hE_sum_m : Measurable fun σ : ι → α × β => ∑ r, V (σ r) :=
      Finset.measurable_sum _ fun r _ => hVm.comp (measurable_pi_apply r)
    rw [pi_tilted_eq_tilted_pi]
    exact integrable_tilted_of_ae_le (C := (Fintype.card ι : ℝ) * B) hE_sum_m.aemeasurable
      (ae_of_all _ fun σ => (Finset.sum_le_sum fun r _ => le_of_abs_le (hVb _)).trans_eq (by simp))
      hf_ι
  calc |∫ σ : ι → α × β, f (fun r => (σ (e r)).1) * H σ
          ∂(Measure.pi fun _ : ι => (μ₀.prod γ).tilted V)|
      ≤ ∫ σ, |f (fun r => (σ (e r)).1) * H σ|
          ∂(Measure.pi fun _ : ι => (μ₀.prod γ).tilted V) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ σ, |f (fun r => (σ (e r)).1)| * M_H
          ∂(Measure.pi fun _ : ι => (μ₀.prod γ).tilted V) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
          (hf_tilt.mul_const M_H) (ae_of_all _ fun σ => ?_)
        dsimp only
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hHb σ) (abs_nonneg _)
    _ = M_H * ∫ σ, |f (fun r => (σ (e r)).1)|
          ∂(Measure.pi fun _ : ι => (μ₀.prod γ).tilted V) := by
        rw [integral_mul_const, mul_comm]
    _ ≤ M_H * (Real.exp (2 * (Fintype.card ι : ℝ) * B) *
          ∫ a, |f a| ∂(Measure.pi fun _ : R => μ₀)) :=
        mul_le_mul_of_nonneg_left hcomp hMH0
    _ = M_H * Real.exp (2 * (Fintype.card ι : ℝ) * B) *
          ∫ a, |f a| ∂(Measure.pi fun _ : R => μ₀) := by ring

/-- **Disorder-averaged Gaussian rotation derivative and integration by parts.** Averaging
`hasDerivAt_integral_gaussian_tilted_rotation_ibp` over an outer probability measure `P₀` requires
only `L¹`-integrability of `ω₀ ↦ ∫ a, |f ω₀ a| ∂pi(μ₀ ω₀)` and outer measurability of the quenched
expectation at each angle `s`. -/
theorem hasDerivAt_integral_integral_gaussian_tilted_rotation_ibp
    {Ω₀ α L K_sh K_aux R : Type*} [MeasurableSpace Ω₀] [MeasurableSpace α]
    [Finite L] [MeasurableSpace L] [MeasurableSingletonClass L]
    [Fintype K_sh] [Fintype K_aux] [Fintype R] [DecidableEq R]
    (P₀ : Measure Ω₀)
    (μ₀ : Ω₀ → Measure α) [∀ ω₀, IsProbabilityMeasure (μ₀ ω₀)]
    (π : α → L) (hπ : Measurable π)
    (X_sh Y_sh : L → K_sh → ℝ) (X_aux Y_aux : L → K_aux → ℝ)
    (horth_sh : ∀ m m', X_sh m ⬝ᵥ Y_sh m' = 0)
    (horth_aux : ∀ m m', X_aux m ⬝ᵥ Y_aux m' = 0)
    (hvar : ∀ m, X_sh m ⬝ᵥ X_sh m + X_aux m ⬝ᵥ X_aux m =
      Y_sh m ⬝ᵥ Y_sh m + Y_aux m ⬝ᵥ Y_aux m)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu₂ : Differentiable ℝ (deriv u))
    {B D₁ D₂ : ℝ} (hB : ∀ x, |u x| ≤ B) (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    (hψ₂d : ∀ r, Differentiable ℝ (deriv (ψ r)))
    {M₀ M₁ M₂ : R → ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀ r)
    (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁ r)
    (hM₂ : ∀ r x, |deriv (deriv (ψ r)) x| ≤ M₂ r)
    {f : Ω₀ → (R → α) → ℝ}
    (hf_mem : ∀ᵐ ω₀ ∂P₀, Integrable (f ω₀) (Measure.pi fun _ : R => μ₀ ω₀))
    (hf_int : Integrable (fun ω₀ => ∫ a, |f ω₀ a| ∂(Measure.pi fun _ : R => μ₀ ω₀)) P₀)
    (hGm : ∀ s, AEStronglyMeasurable
      (fun ω₀ => ∫ w : K_sh → ℝ, ∫ σ : R → α × (K_aux → ℝ),
        f ω₀ (fun r => (σ r).1) * ∏ r, ψ r
          (Real.cos s * (X_sh (π (σ r).1) ⬝ᵥ w + X_aux (π (σ r).1) ⬝ᵥ (σ r).2) +
            Real.sin s * (Y_sh (π (σ r).1) ⬝ᵥ w + Y_aux (π (σ r).1) ⬝ᵥ (σ r).2))
        ∂(Measure.pi fun _ : R =>
          ((μ₀ ω₀).prod (Measure.pi fun _ : K_aux => gaussianReal 0 1)).tilted
            (fun q => u (Real.cos s * (X_sh (π q.1) ⬝ᵥ w + X_aux (π q.1) ⬝ᵥ q.2) +
              Real.sin s * (Y_sh (π q.1) ⬝ᵥ w + Y_aux (π q.1) ⬝ᵥ q.2))))
        ∂(Measure.pi fun _ : K_sh => gaussianReal 0 1)) P₀)
    (s₀ : ℝ) :
    let γ_sh := Measure.pi fun _ : K_sh => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : K_aux => gaussianReal 0 1
    let S (s : ℝ) (w : K_sh → ℝ) (q : α × (K_aux → ℝ)) : ℝ :=
      Real.cos s * (X_sh (π q.1) ⬝ᵥ w + X_aux (π q.1) ⬝ᵥ q.2) +
        Real.sin s * (Y_sh (π q.1) ⬝ᵥ w + Y_aux (π q.1) ⬝ᵥ q.2)
    let C_cov (m m' : L) : ℝ := Y_sh m ⬝ᵥ Y_sh m' - X_sh m ⬝ᵥ X_sh m'
    let ψ_d (r : R) (x : ℝ) : ℝ := deriv (ψ r) x + ψ r x * deriv u x
    let D_ω (s : ℝ) (ω₀ : Ω₀) : ℝ :=
      (∑ i : R, ∑ j ∈ Finset.univ.erase i,
        ∫ w, ∫ σ : R → α × (K_aux → ℝ),
          f ω₀ (fun r => (σ r).1) * C_cov (π (σ i).1) (π (σ j).1) *
            (ψ_d i (S s w (σ i)) * ψ_d j (S s w (σ j)) *
              ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S s w (σ r)))
          ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh) -
      (Fintype.card R : ℝ) * ∑ i : R,
        ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
          f ω₀ (fun r => (σ (some r)).1) * C_cov (π (σ (some i)).1) (π (σ none).1) *
            (ψ_d i (S s w (σ (some i))) *
              ∏ r ∈ Finset.univ.erase i, ψ r (S s w (σ (some r)))) *
            deriv u (S s w (σ none))
          ∂(Measure.pi fun _ : Option R =>
            ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh -
      (Fintype.card R : ℝ) * ∑ j : R,
        ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
          f ω₀ (fun r => (σ (some r)).1) * C_cov (π (σ none).1) (π (σ (some j)).1) *
            (ψ_d j (S s w (σ (some j))) *
              ∏ r ∈ Finset.univ.erase j, ψ r (S s w (σ (some r)))) *
            deriv u (S s w (σ none))
          ∂(Measure.pi fun _ : Option R =>
            ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh +
      (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
        ∫ w, ∫ σ : Option (Option R) → α × (K_aux → ℝ),
          f ω₀ (fun r => (σ (some (some r))).1) * C_cov (π (σ (some none)).1) (π (σ none).1) *
            (∏ r : R, ψ r (S s w (σ (some (some r))))) *
            deriv u (S s w (σ (some none))) * deriv u (S s w (σ none))
          ∂(Measure.pi fun _ : Option (Option R) =>
            ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh
    HasDerivAt
      (fun s => ∫ ω₀, ∫ w, ∫ σ : R → α × (K_aux → ℝ),
          f ω₀ (fun r => (σ r).1) * ∏ r, ψ r (S s w (σ r))
          ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q)))
          ∂γ_sh ∂P₀)
      (Real.sin s₀ * Real.cos s₀ * ∫ ω₀, D_ω s₀ ω₀ ∂P₀)
      s₀ := by
  classical
  have := Fintype.ofFinite L
  intro γ_sh γ_aux S C_cov ψ_d D_ω
  have hum : Measurable u := hu.continuous.measurable
  have hSw_m : ∀ s w, Measurable fun q : α × (K_aux → ℝ) => S s w q := fun s w =>
    measurable_rotation_field hπ X_sh Y_sh X_aux Y_aux s w
  let M_cov : ℝ := ∑ m : L, ∑ m' : L, |C_cov m m'|
  have hMcov0 : 0 ≤ M_cov :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcov_le : ∀ m m', |C_cov m m'| ≤ M_cov := fun m m' =>
    (Finset.single_le_sum (f := fun m'' => |C_cov m m''|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ m')).trans
    (Finset.single_le_sum (f := fun m₁ => ∑ m₂, |C_cov m₁ m₂|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ m))
  let M_ψ : R → ℝ := fun r => |M₀ r| + |M₁ r| + |M₀ r| * |D₁|
  have hMψ0 : ∀ r, 0 ≤ M_ψ r := fun r => by positivity
  have hψ_le : ∀ r x, |ψ r x| ≤ M_ψ r := fun r x => by
    have h1 := (hM₀ r x).trans (le_abs_self _)
    have h2 : 0 ≤ |M₁ r| + |M₀ r| * |D₁| := by positivity
    dsimp only [M_ψ]
    linarith
  have hψd_le : ∀ r x, |ψ_d r x| ≤ M_ψ r := fun r x => by
    have h1 : |ψ_d r x| ≤ |M₁ r| + |M₀ r| * |D₁| := by
      refine (abs_add_le _ _).trans (add_le_add ((hM₁ r x).trans (le_abs_self _)) ?_)
      rw [abs_mul]
      exact mul_le_mul ((hM₀ r x).trans (le_abs_self _)) ((hD₁ x).trans (le_abs_self _))
        (abs_nonneg _) (abs_nonneg _)
    exact h1.trans (by dsimp only [M_ψ]; linarith [abs_nonneg (M₀ r)])
  let P_ψ : ℝ := ∏ r : R, M_ψ r
  have hPψ0 : 0 ≤ P_ψ := Finset.prod_nonneg fun r _ => hMψ0 r
  let K_dom : ℝ :=
    (Fintype.card R : ℝ) ^ 2 * (M_cov * P_ψ * Real.exp (2 * (Fintype.card R : ℝ) * B)) +
    2 * (Fintype.card R : ℝ) ^ 2 *
      (M_cov * P_ψ * |D₁| * Real.exp (2 * ((Fintype.card R : ℝ) + 1) * B)) +
    (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
      (M_cov * P_ψ * |D₁| ^ 2 * Real.exp (2 * ((Fintype.card R : ℝ) + 2) * B))
  have hDω_bd : ∀ ω₀, Integrable (f ω₀) (Measure.pi fun _ : R => μ₀ ω₀) →
      ∀ s, |D_ω s ω₀| ≤
      K_dom * ∫ a, |f ω₀ a| ∂(Measure.pi fun _ : R => μ₀ ω₀) := by
    intro ω₀ hfi s
    let I_f := ∫ a, |f ω₀ a| ∂(Measure.pi fun _ : R => μ₀ ω₀)
    have hIf0 : 0 ≤ I_f := integral_nonneg fun _ => abs_nonneg _
    have ht1 : ∀ i : R, ∀ j ∈ Finset.univ.erase i,
        |∫ w, ∫ σ : R → α × (K_aux → ℝ),
          f ω₀ (fun r => (σ r).1) * C_cov (π (σ i).1) (π (σ j).1) *
            (ψ_d i (S s w (σ i)) * ψ_d j (S s w (σ j)) *
              ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S s w (σ r)))
          ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh| ≤
        (M_cov * P_ψ * Real.exp (2 * (Fintype.card R : ℝ) * B)) * I_f := by
      intro i j hj
      refine abs_integral_le_of_forall_abs_le γ_sh fun w => ?_
      have hb_w := abs_integral_pi_tilted_prod_fst_mul_le (μ₀ ω₀) γ_aux
        (hum.comp (hSw_m s w)) (fun q => hB _) Function.injective_id hfi
        (fun σ => C_cov (π (σ i).1) (π (σ j).1) *
          (ψ_d i (S s w (σ i)) * ψ_d j (S s w (σ j)) *
            ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S s w (σ r))))
        (M_H := M_cov * P_ψ) (mul_nonneg hMcov0 hPψ0) fun σ => by
          rw [abs_mul, abs_mul, abs_mul, Finset.abs_prod]
          refine mul_le_mul (hcov_le _ _) ?_ (by positivity) hMcov0
          have hp_eq : P_ψ = M_ψ i * (M_ψ j * ∏ r ∈ (Finset.univ.erase i).erase j, M_ψ r) := by
            dsimp only [P_ψ]
            rw [← Finset.mul_prod_erase Finset.univ M_ψ (Finset.mem_univ i),
              ← Finset.mul_prod_erase (Finset.univ.erase i) M_ψ hj]
          rw [hp_eq, ← mul_assoc]
          exact mul_le_mul (mul_le_mul (hψd_le i _) (hψd_le j _) (abs_nonneg _) (hMψ0 i))
            (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hψ_le r _)
            (Finset.prod_nonneg fun _ _ => abs_nonneg _) (mul_nonneg (hMψ0 i) (hMψ0 j))
      have heq : (∫ σ : R → α × (K_aux → ℝ),
            f ω₀ (fun r => (σ r).1) * C_cov (π (σ i).1) (π (σ j).1) *
              (ψ_d i (S s w (σ i)) * ψ_d j (S s w (σ j)) *
                ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S s w (σ r)))
            ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q)))) =
          ∫ σ : R → α × (K_aux → ℝ),
            f ω₀ (fun r => (σ (id r)).1) *
              (C_cov (π (σ i).1) (π (σ j).1) *
                (ψ_d i (S s w (σ i)) * ψ_d j (S s w (σ j)) *
                  ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S s w (σ r))))
            ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (u ∘ fun q => S s w q)) :=
        integral_congr_ae (ae_of_all _ fun σ => mul_assoc _ _ _)
      rw [heq]
      exact hb_w
    have ht2 : ∀ (c_fn : L → L → ℝ), (∀ m m', |c_fn m m'| ≤ M_cov) → ∀ i : R,
        |∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
          f ω₀ (fun r => (σ (some r)).1) * c_fn (π (σ (some i)).1) (π (σ none).1) *
            (ψ_d i (S s w (σ (some i))) *
              ∏ r ∈ Finset.univ.erase i, ψ r (S s w (σ (some r)))) *
            deriv u (S s w (σ none))
          ∂(Measure.pi fun _ : Option R =>
            ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh| ≤
        (M_cov * P_ψ * |D₁| * Real.exp (2 * ((Fintype.card R : ℝ) + 1) * B)) * I_f := by
      intro c_fn hc_fn i
      refine abs_integral_le_of_forall_abs_le γ_sh fun w => ?_
      have hb_w := abs_integral_pi_tilted_prod_fst_mul_le (ι := Option R) (μ₀ ω₀) γ_aux
        (hum.comp (hSw_m s w)) (fun q => hB _) (Option.some_injective R) hfi
        (fun σ => c_fn (π (σ (some i)).1) (π (σ none).1) *
          (ψ_d i (S s w (σ (some i))) *
            ∏ r ∈ Finset.univ.erase i, ψ r (S s w (σ (some r)))) *
          deriv u (S s w (σ none)))
        (M_H := M_cov * P_ψ * |D₁|) (by positivity) fun σ => by
          rw [abs_mul, abs_mul, abs_mul, Finset.abs_prod]
          have hp_eq : P_ψ = M_ψ i * ∏ r ∈ Finset.univ.erase i, M_ψ r :=
            (Finset.mul_prod_erase Finset.univ M_ψ (Finset.mem_univ i)).symm
          have h_mid : |ψ_d i (S s w (σ (some i)))| *
              ∏ x ∈ Finset.univ.erase i, |ψ x (S s w (σ (some x)))| ≤ P_ψ := by
            rw [hp_eq]
            exact mul_le_mul (hψd_le i _)
              (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hψ_le r _)
              (Finset.prod_nonneg fun _ _ => abs_nonneg _) (hMψ0 i)
          exact mul_le_mul (mul_le_mul (hc_fn _ _) h_mid (by positivity) hMcov0)
            ((hD₁ _).trans (le_abs_self _)) (abs_nonneg _) (mul_nonneg hMcov0 hPψ0)
      have hcard_opt : (Fintype.card (Option R) : ℝ) = (Fintype.card R : ℝ) + 1 := by
        simp [Fintype.card_option]
      rw [hcard_opt] at hb_w
      have heq : (∫ σ : Option R → α × (K_aux → ℝ),
            f ω₀ (fun r => (σ (some r)).1) * c_fn (π (σ (some i)).1) (π (σ none).1) *
              (ψ_d i (S s w (σ (some i))) *
                ∏ r ∈ Finset.univ.erase i, ψ r (S s w (σ (some r)))) *
              deriv u (S s w (σ none))
            ∂(Measure.pi fun _ : Option R =>
              ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q)))) =
          ∫ σ : Option R → α × (K_aux → ℝ),
            f ω₀ (fun r => (σ (some r)).1) *
              (c_fn (π (σ (some i)).1) (π (σ none).1) *
                (ψ_d i (S s w (σ (some i))) *
                  ∏ r ∈ Finset.univ.erase i, ψ r (S s w (σ (some r)))) *
                deriv u (S s w (σ none)))
            ∂(Measure.pi fun _ : Option R =>
              ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q))) :=
        integral_congr_ae (ae_of_all _ fun σ => by ring)
      rw [heq]
      exact hb_w
    have ht4 :
        |∫ w, ∫ σ : Option (Option R) → α × (K_aux → ℝ),
          f ω₀ (fun r => (σ (some (some r))).1) * C_cov (π (σ (some none)).1) (π (σ none).1) *
            (∏ r : R, ψ r (S s w (σ (some (some r))))) *
            deriv u (S s w (σ (some none))) * deriv u (S s w (σ none))
          ∂(Measure.pi fun _ : Option (Option R) =>
            ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh| ≤
        (M_cov * P_ψ * |D₁| ^ 2 * Real.exp (2 * ((Fintype.card R : ℝ) + 2) * B)) * I_f := by
      refine abs_integral_le_of_forall_abs_le γ_sh fun w => ?_
      have hb_w := abs_integral_pi_tilted_prod_fst_mul_le (ι := Option (Option R)) (μ₀ ω₀) γ_aux
        (hum.comp (hSw_m s w)) (fun q => hB _)
        (fun a b hab => Option.some_injective _ (Option.some_injective _ hab)) hfi
        (fun σ => C_cov (π (σ (some none)).1) (π (σ none).1) *
          (∏ r : R, ψ r (S s w (σ (some (some r))))) *
          deriv u (S s w (σ (some none))) * deriv u (S s w (σ none)))
        (M_H := M_cov * P_ψ * |D₁| ^ 2) (by positivity) fun σ => by
          rw [abs_mul, abs_mul, abs_mul, Finset.abs_prod, sq]
          have h_mid : ∏ x : R, |ψ x (S s w (σ (some (some x))))| ≤ P_ψ :=
            Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hψ_le r _
          have h12 : |C_cov (π (σ (some none)).1) (π (σ none).1)| *
              (∏ x : R, |ψ x (S s w (σ (some (some x))))|) ≤ M_cov * P_ψ :=
            mul_le_mul (hcov_le _ _) h_mid (by positivity) hMcov0
          have h123 : (|C_cov (π (σ (some none)).1) (π (σ none).1)| *
              ∏ x : R, |ψ x (S s w (σ (some (some x))))|) *
              |deriv u (S s w (σ (some none)))| ≤ M_cov * P_ψ * |D₁| :=
            mul_le_mul h12 ((hD₁ _).trans (le_abs_self _)) (abs_nonneg _)
              (mul_nonneg hMcov0 hPψ0)
          calc _ ≤ (M_cov * P_ψ * |D₁|) * |D₁| :=
                mul_le_mul h123 ((hD₁ _).trans (le_abs_self _)) (abs_nonneg _) (by positivity)
            _ = _ := by ring
      have hcard_oo : (Fintype.card (Option (Option R)) : ℝ) = (Fintype.card R : ℝ) + 2 := by
        simp [Fintype.card_option]; ring
      rw [hcard_oo] at hb_w
      have heq : (∫ σ : Option (Option R) → α × (K_aux → ℝ),
            f ω₀ (fun r => (σ (some (some r))).1) * C_cov (π (σ (some none)).1) (π (σ none).1) *
              (∏ r : R, ψ r (S s w (σ (some (some r))))) *
              deriv u (S s w (σ (some none))) * deriv u (S s w (σ none))
            ∂(Measure.pi fun _ : Option (Option R) =>
              ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q)))) =
          ∫ σ : Option (Option R) → α × (K_aux → ℝ),
            f ω₀ (fun r => (σ (some (some r))).1) *
              (C_cov (π (σ (some none)).1) (π (σ none).1) *
                (∏ r : R, ψ r (S s w (σ (some (some r))))) *
                deriv u (S s w (σ (some none))) * deriv u (S s w (σ none)))
            ∂(Measure.pi fun _ : Option (Option R) =>
              ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q))) :=
        integral_congr_ae (ae_of_all _ fun σ => by ring)
      rw [heq]
      exact hb_w
    dsimp only [D_ω]
    have hsum1 : |∑ i : R, ∑ j ∈ Finset.univ.erase i,
        ∫ w, ∫ σ : R → α × (K_aux → ℝ),
          f ω₀ (fun r => (σ r).1) * C_cov (π (σ i).1) (π (σ j).1) *
            (ψ_d i (S s w (σ i)) * ψ_d j (S s w (σ j)) *
              ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S s w (σ r)))
          ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh| ≤
        (Fintype.card R : ℝ) ^ 2 *
          ((M_cov * P_ψ * Real.exp (2 * (Fintype.card R : ℝ) * B)) * I_f) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ i : R, (Fintype.card R : ℝ) *
            ((M_cov * P_ψ * Real.exp (2 * (Fintype.card R : ℝ) * B)) * I_f) := by
            refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
            calc _ ≤ ∑ _j ∈ Finset.univ.erase i,
                  ((M_cov * P_ψ * Real.exp (2 * (Fintype.card R : ℝ) * B)) * I_f) :=
                  Finset.sum_le_sum fun j hj => ht1 i j hj
              _ ≤ (Fintype.card R : ℝ) *
                  ((M_cov * P_ψ * Real.exp (2 * (Fintype.card R : ℝ) * B)) * I_f) := by
                  simp only [Finset.sum_const, nsmul_eq_mul]
                  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
                  exact_mod_cast Finset.card_le_univ _
        _ = _ := by simp [sq, mul_assoc]
    have hsum2 : |(Fintype.card R : ℝ) * ∑ i : R,
        ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
          f ω₀ (fun r => (σ (some r)).1) * C_cov (π (σ (some i)).1) (π (σ none).1) *
            (ψ_d i (S s w (σ (some i))) *
              ∏ r ∈ Finset.univ.erase i, ψ r (S s w (σ (some r)))) *
            deriv u (S s w (σ none))
          ∂(Measure.pi fun _ : Option R =>
            ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh| ≤
        (Fintype.card R : ℝ) ^ 2 *
          ((M_cov * P_ψ * |D₁| * Real.exp (2 * ((Fintype.card R : ℝ) + 1) * B)) * I_f) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      calc _ ≤ (Fintype.card R : ℝ) * ∑ _i : R,
            ((M_cov * P_ψ * |D₁| * Real.exp (2 * ((Fintype.card R : ℝ) + 1) * B)) * I_f) :=
            mul_le_mul_of_nonneg_left
              (Finset.abs_sum_le_sum_of_abs_le _ fun i _ => ht2 C_cov hcov_le i)
              (Nat.cast_nonneg _)
        _ = _ := by simp [sq, mul_assoc]
    have hsum3 : |(Fintype.card R : ℝ) * ∑ j : R,
        ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
          f ω₀ (fun r => (σ (some r)).1) * C_cov (π (σ none).1) (π (σ (some j)).1) *
            (ψ_d j (S s w (σ (some j))) *
              ∏ r ∈ Finset.univ.erase j, ψ r (S s w (σ (some r)))) *
            deriv u (S s w (σ none))
          ∂(Measure.pi fun _ : Option R =>
            ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh| ≤
        (Fintype.card R : ℝ) ^ 2 *
          ((M_cov * P_ψ * |D₁| * Real.exp (2 * ((Fintype.card R : ℝ) + 1) * B)) * I_f) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      calc _ ≤ (Fintype.card R : ℝ) * ∑ _j : R,
            ((M_cov * P_ψ * |D₁| * Real.exp (2 * ((Fintype.card R : ℝ) + 1) * B)) * I_f) :=
            mul_le_mul_of_nonneg_left
              (Finset.abs_sum_le_sum_of_abs_le _ fun j _ =>
                ht2 (fun m m' => C_cov m' m) (fun m m' => hcov_le m' m) j)
              (Nat.cast_nonneg _)
        _ = _ := by simp [sq, mul_assoc]
    have hsum4 : |(Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
        ∫ w, ∫ σ : Option (Option R) → α × (K_aux → ℝ),
          f ω₀ (fun r => (σ (some (some r))).1) * C_cov (π (σ (some none)).1) (π (σ none).1) *
            (∏ r : R, ψ r (S s w (σ (some (some r))))) *
            deriv u (S s w (σ (some none))) * deriv u (S s w (σ none))
          ∂(Measure.pi fun _ : Option (Option R) =>
            ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh| ≤
        (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
          ((M_cov * P_ψ * |D₁| ^ 2 * Real.exp (2 * ((Fintype.card R : ℝ) + 2) * B)) * I_f) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left ht4 (by positivity)
    have h_tri : ∀ a b c d : ℝ, |a - b - c + d| ≤ |a| + |b| + |c| + |d| := fun a b c d => by
      linarith [abs_add_le (a - b - c) d, abs_sub (a - b) c, abs_sub a b]
    calc _ ≤ _ := h_tri _ _ _ _
      _ ≤ _ := add_le_add (add_le_add (add_le_add hsum1 hsum2) hsum3) hsum4
      _ = K_dom * I_f := by dsimp only [K_dom]; ring
  let G_ω : ℝ → Ω₀ → ℝ := fun s ω₀ =>
    ∫ w, ∫ σ : R → α × (K_aux → ℝ),
      f ω₀ (fun r => (σ r).1) * ∏ r, ψ r (S s w (σ r))
      ∂(Measure.pi fun _ : R => ((μ₀ ω₀).prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh
  have hGω_int : ∀ s, Integrable (G_ω s) P₀ := fun s => by
    refine (hf_int.const_mul (P_ψ * Real.exp (2 * (Fintype.card R : ℝ) * B))).mono' (hGm s)
      (hf_mem.mono fun ω₀ hfi => ?_)
    rw [Real.norm_eq_abs]
    refine abs_integral_le_of_forall_abs_le γ_sh fun w => ?_
    exact abs_integral_pi_tilted_prod_fst_mul_le (μ₀ ω₀) γ_aux
      (hum.comp (hSw_m s w)) (fun q => hB _) Function.injective_id hfi
      (fun σ => ∏ r, ψ r (S s w (σ r))) hPψ0 fun σ => by
        rw [Finset.abs_prod]
        exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hψ_le r _
  have hGω_deriv : ∀ᵐ ω₀ ∂P₀, ∀ s, HasDerivAt (fun s' => G_ω s' ω₀)
      (Real.sin s * Real.cos s * D_ω s ω₀) s :=
    hf_mem.mono fun ω₀ hfi s =>
      hasDerivAt_integral_gaussian_tilted_rotation_ibp (μ₀ ω₀) π hπ X_sh Y_sh X_aux Y_aux
        horth_sh horth_aux hvar hu hu₂ hB hD₁ hD₂ ψ hψd hψ₂d hM₀ hM₁ hM₂ hfi s
  have hF'_m : AEStronglyMeasurable (fun ω₀ => Real.sin s₀ * Real.cos s₀ * D_ω s₀ ω₀) P₀ :=
    aestronglyMeasurable_of_hasDerivAt_param (hGω_deriv.mono fun _ hω => hω s₀) hGm
  have hdom := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P₀)
    (F := G_ω)
    (F' := fun s ω₀ => Real.sin s * Real.cos s * D_ω s ω₀)
    (x₀ := s₀) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall hGm) (hGω_int s₀) hF'_m
    (bound := fun ω₀ => K_dom * ∫ a, |f ω₀ a| ∂(Measure.pi fun _ : R => μ₀ ω₀))
    (hf_mem.mono fun ω₀ hfi s _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have hsc : |Real.sin s| * |Real.cos s| ≤ 1 :=
        (mul_le_mul (Real.abs_sin_le_one s) (Real.abs_cos_le_one s) (abs_nonneg _)
          zero_le_one).trans_eq (one_mul 1)
      calc |Real.sin s| * |Real.cos s| * |D_ω s ω₀|
          ≤ 1 * (K_dom * ∫ a, |f ω₀ a| ∂(Measure.pi fun _ : R => μ₀ ω₀)) :=
            mul_le_mul hsc (hDω_bd ω₀ hfi s) (abs_nonneg _) zero_le_one
        _ = _ := one_mul _)
    (hf_int.const_mul K_dom)
    (hGω_deriv.mono fun _ hω s _ => hω s)
  refine hdom.2.congr_deriv ?_
  rw [integral_const_mul]

/-- **Iterated Hölder for a random replica Gibbs law on an arbitrary state space.**
For interior conjugate exponents `Real.HolderConjugate p q`, if `f ω` is in `L^p` under `pi (ν ω)`
and `d` is in `L^q` for almost every two-replica law, with integrable conditional moments,
then the expected
pair average of `|f ω (σ ∘ e)| * d (σ r₁) (σ r₂)` (`r₁ ≠ r₂`) is bounded by the product of the
iterated `L^p` and `L^q` moments. -/
theorem integral_integral_pair_holder_prob
    {Ω α R ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [Fintype R] [Fintype ι]
    (P : Measure Ω)
    (ν : Ω → Measure α) [∀ ω, IsProbabilityMeasure (ν ω)]
    {e : R → ι} (he : Function.Injective e) {r₁ r₂ : ι} (hr : r₁ ≠ r₂)
    {f : Ω → (R → α) → ℝ}
    {d : α → α → ℝ} (hd0 : ∀ a b, 0 ≤ d a b)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (hfp_mem : ∀ᵐ ω ∂P, MemLp (f ω) (ENNReal.ofReal p) (Measure.pi fun _ : R => ν ω))
    (hfp_int : Integrable (fun ω => ∫ a, |f ω a| ^ p ∂(Measure.pi fun _ : R => ν ω)) P)
    (hdq_mem : ∀ᵐ ω ∂P, MemLp (fun τ : Fin 2 → α => d (τ 0) (τ 1)) (ENNReal.ofReal q)
      (Measure.pi fun _ : Fin 2 => ν ω))
    (hdq_int : Integrable
      (fun ω => ∫ τ : Fin 2 → α, d (τ 0) (τ 1) ^ q ∂(Measure.pi fun _ : Fin 2 => ν ω)) P) :
    ∫ ω, ∫ σ : ι → α, |f ω (fun r => σ (e r))| * d (σ r₁) (σ r₂)
        ∂(Measure.pi fun _ : ι => ν ω) ∂P ≤
      (∫ ω, ∫ a : R → α, |f ω a| ^ p ∂(Measure.pi fun _ : R => ν ω) ∂P) ^ (1 / p) *
      (∫ ω, ∫ τ : Fin 2 → α, d (τ 0) (τ 1) ^ q
        ∂(Measure.pi fun _ : Fin 2 => ν ω) ∂P) ^ (1 / q) := by
  have hp : 0 < p := hpq.pos
  have hq : 0 < q := hpq.symm.pos
  set A : Ω → ℝ := fun ω => ∫ a : R → α, |f ω a| ^ p ∂(Measure.pi fun _ : R => ν ω)
  set B : Ω → ℝ :=
    fun ω => ∫ τ : Fin 2 → α, d (τ 0) (τ 1) ^ q ∂(Measure.pi fun _ : Fin 2 => ν ω)
  have hA0 : ∀ ω, 0 ≤ A ω := fun ω => integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
  have hB0 : ∀ ω, 0 ≤ B ω := fun ω => integral_nonneg fun _ => Real.rpow_nonneg (hd0 _ _) _
  have hρ : Function.Injective (![r₁, r₂] : Fin 2 → ι) := Matrix.injective_pair_iff_ne.2 hr
  have hinner : ∀ᵐ ω ∂P, ∫ σ : ι → α, |f ω (fun r => σ (e r))| * d (σ r₁) (σ r₂)
        ∂(Measure.pi fun _ : ι => ν ω) ≤ A ω ^ (1 / p) * B ω ^ (1 / q) := by
    filter_upwards [hfp_mem, hdq_mem] with ω hf hd
    have hmp_e := measurePreserving_pi_comp_injective (ν ω) he
    have hf_ι : MemLp (fun σ : ι → α => |f ω (fun r => σ (e r))|) (ENNReal.ofReal p)
        (Measure.pi fun _ : ι => ν ω) :=
      hf.abs.comp_measurePreserving hmp_e
    have hd_ι : MemLp (fun σ : ι → α => d (σ r₁) (σ r₂)) (ENNReal.ofReal q)
        (Measure.pi fun _ : ι => ν ω) :=
      hd.comp_measurePreserving (measurePreserving_pi_comp_injective (ν ω) hρ)
    have hhold := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := Measure.pi fun _ : ι => ν ω) hpq
      (ae_of_all _ fun _ => abs_nonneg _) (ae_of_all _ fun _ => hd0 _ _) hf_ι hd_ι
    have he1 : ∫ σ : ι → α, |f ω (fun r => σ (e r))| ^ p ∂(Measure.pi fun _ : ι => ν ω) = A ω :=
      integral_pi_comp_injective (ν ω) he (fun a => |f ω a| ^ p)
        (hf.abs.aestronglyMeasurable.aemeasurable.pow_const p).aestronglyMeasurable
    have he2 : ∫ σ : ι → α, d (σ r₁) (σ r₂) ^ q ∂(Measure.pi fun _ : ι => ν ω) = B ω :=
      integral_pi_comp_injective (ν ω) hρ (fun τ : Fin 2 → α => d (τ 0) (τ 1) ^ q)
        (hd.aestronglyMeasurable.aemeasurable.pow_const q).aestronglyMeasurable
    simpa only [he1, he2] using hhold
  have hA_mem : MemLp (fun ω => A ω ^ (1 / p)) (ENNReal.ofReal p) P :=
    memLp_rpow_inv_of_integrable hp hA0 hfp_int
  have hB_mem : MemLp (fun ω => B ω ^ (1 / q)) (ENNReal.ofReal q) P :=
    memLp_rpow_inv_of_integrable hq hB0 hdq_int
  have hAB_int : Integrable (fun ω => A ω ^ (1 / p) * B ω ^ (1 / q)) P := by
    haveI := hpq.ennrealOfReal
    exact hA_mem.integrable_mul hB_mem
  calc ∫ ω, ∫ σ : ι → α, |f ω (fun r => σ (e r))| * d (σ r₁) (σ r₂)
          ∂(Measure.pi fun _ : ι => ν ω) ∂P
      ≤ ∫ ω, A ω ^ (1 / p) * B ω ^ (1 / q) ∂P :=
        integral_mono_of_nonneg
          (ae_of_all _ fun ω => integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (hd0 _ _))
          hAB_int hinner
    _ ≤ (∫ ω, (A ω ^ (1 / p)) ^ p ∂P) ^ (1 / p) * (∫ ω, (B ω ^ (1 / q)) ^ q ∂P) ^ (1 / q) :=
        integral_mul_le_Lp_mul_Lq_of_nonneg hpq
          (ae_of_all _ fun ω => Real.rpow_nonneg (hA0 ω) _)
          (ae_of_all _ fun ω => Real.rpow_nonneg (hB0 ω) _) hA_mem hB_mem
    _ = _ := by
        simp only [one_div, Real.rpow_inv_rpow (hA0 _) hp.ne', Real.rpow_inv_rpow (hB0 _) hq.ne']

/-- **Endpoint `(1, ∞)` of Hölder for a random replica Gibbs law:** if `d ≤ Md` almost everywhere
under `P`-a.e. two-replica law and `f` is `L¹`, the expected pair average is at most the `L¹`
moment of `f` times `Md`. -/
theorem integral_integral_pair_holder_one_top
    {Ω α R ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [Fintype R] [Fintype ι]
    (P : Measure Ω)
    (ν : Ω → Measure α) [∀ ω, IsProbabilityMeasure (ν ω)]
    {e : R → ι} (he : Function.Injective e) {r₁ r₂ : ι} (hr : r₁ ≠ r₂)
    {f : Ω → (R → α) → ℝ}
    {d : α → α → ℝ} (hd0 : ∀ a b, 0 ≤ d a b) (hdm : Measurable fun p : α × α => d p.1 p.2)
    {Md : ℝ}
    (hd_ae : ∀ᵐ ω ∂P, ∀ᵐ τ : Fin 2 → α ∂(Measure.pi fun _ : Fin 2 => ν ω), d (τ 0) (τ 1) ≤ Md)
    (hf1_mem : ∀ ω, Integrable (f ω) (Measure.pi fun _ : R => ν ω))
    (hf1_int : Integrable (fun ω => ∫ a, |f ω a| ∂(Measure.pi fun _ : R => ν ω)) P) :
    ∫ ω, ∫ σ : ι → α, |f ω (fun r => σ (e r))| * d (σ r₁) (σ r₂)
        ∂(Measure.pi fun _ : ι => ν ω) ∂P ≤
      (∫ ω, ∫ a : R → α, |f ω a| ∂(Measure.pi fun _ : R => ν ω) ∂P) * Md := by
  have hρ : Function.Injective (![r₁, r₂] : Fin 2 → ι) := Matrix.injective_pair_iff_ne.2 hr
  have hinner : ∀ᵐ ω ∂P,
      ∫ σ : ι → α, |f ω (fun r => σ (e r))| * d (σ r₁) (σ r₂) ∂(Measure.pi fun _ : ι => ν ω) ≤
        (∫ a : R → α, |f ω a| ∂(Measure.pi fun _ : R => ν ω)) * Md := by
    filter_upwards [hd_ae] with ω hω
    have hmp_ρ := measurePreserving_pi_comp_injective (ν ω) hρ
    have hd_ι_ae : ∀ᵐ σ : ι → α ∂(Measure.pi fun _ : ι => ν ω), d (σ r₁) (σ r₂) ≤ Md :=
      hmp_ρ.quasiMeasurePreserving.ae hω
    have hmp_e := measurePreserving_pi_comp_injective (ν ω) he
    have hf_ι : Integrable (fun σ : ι → α => |f ω (fun r => σ (e r))|)
        (Measure.pi fun _ : ι => ν ω) :=
      hmp_e.integrable_comp_of_integrable (hf1_mem ω).abs
    have hd_m : Measurable fun σ : ι → α => d (σ r₁) (σ r₂) :=
      hdm.comp (by fun_prop : Measurable fun σ : ι → α => (σ r₁, σ r₂))
    calc ∫ σ : ι → α, |f ω (fun r => σ (e r))| * d (σ r₁) (σ r₂) ∂(Measure.pi fun _ : ι => ν ω)
        ≤ ∫ σ : ι → α, |f ω (fun r => σ (e r))| * Md ∂(Measure.pi fun _ : ι => ν ω) := by
          refine integral_mono_ae
            ((hf_ι.bdd_mul_of_abs_le (C := Md) hd_m.aestronglyMeasurable
              (hd_ι_ae.mono fun σ hσ => by rw [abs_of_nonneg (hd0 _ _)]; exact hσ)).congr
              (ae_of_all _ fun σ => mul_comm _ _))
            (hf_ι.mul_const Md)
            (hd_ι_ae.mono fun σ hσ => mul_le_mul_of_nonneg_left hσ (abs_nonneg _))
      _ = (∫ a : R → α, |f ω a| ∂(Measure.pi fun _ : R => ν ω)) * Md := by
          rw [integral_mul_const, integral_pi_comp_injective (ν ω) he (fun a => |f ω a|)
            (hf1_mem ω).abs.aestronglyMeasurable]
  calc ∫ ω, ∫ σ : ι → α, |f ω (fun r => σ (e r))| * d (σ r₁) (σ r₂)
          ∂(Measure.pi fun _ : ι => ν ω) ∂P
      ≤ ∫ ω, (∫ a : R → α, |f ω a| ∂(Measure.pi fun _ : R => ν ω)) * Md ∂P :=
        integral_mono_of_nonneg
          (ae_of_all _ fun ω => integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (hd0 _ _))
          (hf1_int.mul_const Md) hinner
    _ = (∫ ω, ∫ a : R → α, |f ω a| ∂(Measure.pi fun _ : R => ν ω) ∂P) * Md :=
        integral_mul_const _ _

/-- **Endpoint `(∞, 1)` of Hölder for a random replica Gibbs law:** if `|f ω| ≤ Mf` almost
everywhere under `P`-a.e. replica law and `d` is bounded and measurable, the expected pair average
is at most `Mf` times the `L¹` moment of `d`. -/
theorem integral_integral_pair_holder_top_one
    {Ω α R ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [Fintype R] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Ω → Measure α) [∀ ω, IsProbabilityMeasure (ν ω)]
    {e : R → ι} (he : Function.Injective e) {r₁ r₂ : ι} (hr : r₁ ≠ r₂)
    {f : Ω → (R → α) → ℝ} (hf_m : ∀ ω, AEStronglyMeasurable (f ω) (Measure.pi fun _ : R => ν ω))
    {Mf : ℝ}
    (hf_ae : ∀ᵐ ω ∂P, ∀ᵐ a : R → α ∂(Measure.pi fun _ : R => ν ω), |f ω a| ≤ Mf)
    {d : α → α → ℝ} (hd0 : ∀ a b, 0 ≤ d a b) (hdm : Measurable fun p : α × α => d p.1 p.2)
    {Md : ℝ} (hdb : ∀ a b, d a b ≤ Md)
    (hd1_m : AEStronglyMeasurable
      (fun ω => ∫ τ : Fin 2 → α, d (τ 0) (τ 1) ∂(Measure.pi fun _ : Fin 2 => ν ω)) P) :
    ∫ ω, ∫ σ : ι → α, |f ω (fun r => σ (e r))| * d (σ r₁) (σ r₂)
        ∂(Measure.pi fun _ : ι => ν ω) ∂P ≤
      Mf * ∫ ω, ∫ τ : Fin 2 → α, d (τ 0) (τ 1) ∂(Measure.pi fun _ : Fin 2 => ν ω) ∂P := by
  have hρ : Function.Injective (![r₁, r₂] : Fin 2 → ι) := Matrix.injective_pair_iff_ne.2 hr
  have hd1_int : Integrable
      (fun ω => ∫ τ : Fin 2 → α, d (τ 0) (τ 1) ∂(Measure.pi fun _ : Fin 2 => ν ω)) P :=
    Integrable.of_bound hd1_m Md (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => hd0 _ _)]
      exact (le_abs_self _).trans (abs_integral_le_of_forall_abs_le _ fun τ => by
        rw [abs_of_nonneg (hd0 _ _)]
        exact hdb _ _))
  have hinner : ∀ᵐ ω ∂P,
      ∫ σ : ι → α, |f ω (fun r => σ (e r))| * d (σ r₁) (σ r₂) ∂(Measure.pi fun _ : ι => ν ω) ≤
        Mf * ∫ τ : Fin 2 → α, d (τ 0) (τ 1) ∂(Measure.pi fun _ : Fin 2 => ν ω) := by
    filter_upwards [hf_ae] with ω hω
    have hmp_e := measurePreserving_pi_comp_injective (ν ω) he
    have hf_ι_ae : ∀ᵐ σ : ι → α ∂(Measure.pi fun _ : ι => ν ω), |f ω (fun r => σ (e r))| ≤ Mf :=
      hmp_e.quasiMeasurePreserving.ae hω
    have hd_m : Measurable fun σ : ι → α => d (σ r₁) (σ r₂) :=
      hdm.comp (by fun_prop : Measurable fun σ : ι → α => (σ r₁, σ r₂))
    have hd_ι : Integrable (fun σ : ι → α => d (σ r₁) (σ r₂)) (Measure.pi fun _ : ι => ν ω) :=
      Integrable.of_bound hd_m.aestronglyMeasurable Md (ae_of_all _ fun σ => by
        rw [Real.norm_of_nonneg (hd0 _ _)]
        exact hdb _ _)
    calc ∫ σ : ι → α, |f ω (fun r => σ (e r))| * d (σ r₁) (σ r₂) ∂(Measure.pi fun _ : ι => ν ω)
        ≤ ∫ σ : ι → α, Mf * d (σ r₁) (σ r₂) ∂(Measure.pi fun _ : ι => ν ω) := by
          refine integral_mono_ae
            (hd_ι.bdd_mul_of_abs_le (C := Mf)
              (((hf_m ω).norm).comp_quasiMeasurePreserving hmp_e.quasiMeasurePreserving)
              (hf_ι_ae.mono fun σ hσ => by rw [abs_abs]; exact hσ))
            (hd_ι.const_mul Mf)
            (hf_ι_ae.mono fun σ hσ => mul_le_mul_of_nonneg_right hσ (hd0 _ _))
      _ = Mf * ∫ τ : Fin 2 → α, d (τ 0) (τ 1) ∂(Measure.pi fun _ : Fin 2 => ν ω) := by
          rw [integral_const_mul]
          congr 1
          exact integral_pi_comp_injective (ν ω) hρ (fun τ => d (τ 0) (τ 1))
            (hdm.comp ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1) :
              Measurable fun τ : Fin 2 → α => (τ 0, τ 1))).aestronglyMeasurable
  calc ∫ ω, ∫ σ : ι → α, |f ω (fun r => σ (e r))| * d (σ r₁) (σ r₂)
          ∂(Measure.pi fun _ : ι => ν ω) ∂P
      ≤ ∫ ω, Mf * ∫ τ : Fin 2 → α, d (τ 0) (τ 1) ∂(Measure.pi fun _ : Fin 2 => ν ω) ∂P :=
        integral_mono_of_nonneg
          (ae_of_all _ fun ω => integral_nonneg fun _ => mul_nonneg (abs_nonneg _) (hd0 _ _))
          (hd1_int.const_mul Mf) hinner
    _ = Mf * ∫ ω, ∫ τ : Fin 2 → α, d (τ 0) (τ 1) ∂(Measure.pi fun _ : Fin 2 => ν ω) ∂P :=
        integral_const_mul _ _

end SpinGlasses
