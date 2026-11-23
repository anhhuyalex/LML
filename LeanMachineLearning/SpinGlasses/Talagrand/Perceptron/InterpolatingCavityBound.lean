/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.OverlapConcentration

/-!
# Cavity-in-`M` bound for the `s`-interpolating constraint field (Talagrand Section 2.4)

Generalizes Proposition 2.3.5 (Eq. (2.62), used in both Eq. (2.80) and Lemma 2.4.3, Eq. (2.86))
from `s = 1` (`ConstraintCavityComparison.lean`) to the `s`-interpolating constraint field
`S_{M, t, s} = √s * S_{M, t} + √(1 - s) * (√q * z_M + √(1 - q) * ξ_M)` for arbitrary
`s, t, q ∈ [0, 1]` and an arbitrary old-state base measure `(Ω₀, P₀, μ_base, E₀)`.

Rotating the entire `s`-interpolating field `S_{M, t, s}` into an independent
`θ = √q * z + √(1 - q) * ξ` keeps unit total variance at every angle
(`interp_cavity_rotation_dotProducts`), scales the shared covariance difference by `s`
(`s * (q - R^t)`, bounded in absolute value by
`|R - q| + 1 / (N + 1)` since `0 ≤ s ≤ 1`), preserves the original potential `u`, and evaluates at
`ϑ = π / 2` to `r̂(q)`.

## Main declarations

* `SpinGlasses.interp_cavity_rotation_dotProducts`: orthogonality, unit variances, and covariance
  `s * (q - cavityCoef N t σ ⬝ᵥ cavityCoef N t τ)` for the `s`-interpolating cavity rotation.
* `SpinGlasses.abs_integral_interp_deriv_mul_sub_rhat_le_first_moment`: `(1, ∞)` endpoint of
  Proposition 2.3.5 for an arbitrary old-state base system with an `s`-interpolating new constraint.
* `SpinGlasses.abs_integral_interp_deriv_mul_sub_rhat_le_l2`: `L²` Cauchy-Schwarz (`p₁ = p₂ = 2`)
  case of Proposition 2.3.5 for an arbitrary old-state base system with an `s`-interpolating new
  constraint (used in both Eq. (2.80) and Lemma 2.4.3).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology

namespace SpinGlasses

universe uR uΩ uα

/-- **Covariance relations for the `s`-interpolating cavity rotation (`s, t, q ∈ [0, 1]`).** -/
theorem interp_cavity_rotation_dotProducts {N : ℕ} {s t q : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) :
    let X_sh : PerceptronSpin N → ((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit → ℝ :=
      fun σ => Sum.elim
        (Sum.elim (Real.sqrt s • cavityCoef N t σ) (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) 0
    let Y_sh : ((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit → ℝ :=
      Sum.elim 0 (fun _ => Real.sqrt q)
    let X_aux : Fin 2 ⊕ Unit → ℝ :=
      Sum.elim ![Real.sqrt s * Real.sqrt ((1 - t) / (N + 1)),
        Real.sqrt (1 - s) * Real.sqrt (1 - q)] 0
    let Y_aux : Fin 2 ⊕ Unit → ℝ :=
      Sum.elim 0 (fun _ => Real.sqrt (1 - q))
    (∀ σ, X_sh σ ⬝ᵥ Y_sh = 0) ∧
      X_aux ⬝ᵥ Y_aux = 0 ∧
      (∀ σ, X_sh σ ⬝ᵥ X_sh σ + X_aux ⬝ᵥ X_aux = 1) ∧
      Y_sh ⬝ᵥ Y_sh + Y_aux ⬝ᵥ Y_aux = 1 ∧
      (∀ σ τ, Y_sh ⬝ᵥ Y_sh - X_sh σ ⬝ᵥ X_sh τ =
        s * (q - cavityCoef N t σ ⬝ᵥ cavityCoef N t τ)) := by
  intro X_sh Y_sh X_aux Y_aux
  have hs1 : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.1
  have hs2 : Real.sqrt (1 - s) * Real.sqrt (1 - s) = 1 - s :=
    Real.mul_self_sqrt (sub_nonneg.2 hs.2)
  have hq1 : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq.1
  have hq2 : Real.sqrt (1 - q) * Real.sqrt (1 - q) = 1 - q :=
    Real.mul_self_sqrt (sub_nonneg.2 hq.2)
  have ht2 : Real.sqrt ((1 - t) / (N + 1)) * Real.sqrt ((1 - t) / (N + 1)) = (1 - t) / (N + 1) :=
    Real.mul_self_sqrt (div_nonneg (sub_nonneg.2 ht.2) (by positivity))
  have hY_sh : Y_sh ⬝ᵥ Y_sh = q := by
    dsimp only [Y_sh]
    rw [sumElim_dotProduct_sumElim, zero_dotProduct, zero_add]
    simp [dotProduct, hq1]
  have hX_sh (σ τ : PerceptronSpin N) :
      X_sh σ ⬝ᵥ X_sh τ = s * (cavityCoef N t σ ⬝ᵥ cavityCoef N t τ) + (1 - s) * q := by
    dsimp only [X_sh]
    rw [sumElim_dotProduct_sumElim, zero_dotProduct, add_zero,
      sumElim_dotProduct_sumElim, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have h2 : (fun _ : Unit => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ
        (fun _ : Unit => Real.sqrt (1 - s) * Real.sqrt q) = (1 - s) * q := by
      simp only [dotProduct, Finset.univ_unique, Finset.sum_singleton]
      linear_combination q * hs2 + (Real.sqrt (1 - s) ^ 2) * hq1
    rw [h2]
    linear_combination (cavityCoef N t σ ⬝ᵥ cavityCoef N t τ) * hs1
  refine ⟨fun σ => ?_, ?_, fun σ => ?_, ?_, fun σ τ => ?_⟩
  · dsimp only [X_sh, Y_sh]
    simp [sumElim_dotProduct_sumElim]
  · dsimp only [X_aux, Y_aux]
    simp [sumElim_dotProduct_sumElim]
  · rw [hX_sh σ σ]
    have hXa : X_aux ⬝ᵥ X_aux = s * ((1 - t) / (N + 1)) + (1 - s) * (1 - q) := by
      dsimp only [X_aux]
      rw [sumElim_dotProduct_sumElim, zero_dotProduct, add_zero]
      simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination ((1 - t) / (N + 1)) * hs1 + (Real.sqrt s ^ 2) * ht2 +
        (1 - q) * hs2 + (Real.sqrt (1 - s) ^ 2) * hq2
    rw [hXa]
    have hunit := cavityCoef_dotProduct_self_add ht σ
    rw [sq, ht2] at hunit
    linear_combination s * hunit
  · rw [hY_sh]
    have hYa : Y_aux ⬝ᵥ Y_aux = 1 - q := by
      dsimp only [Y_aux]
      rw [sumElim_dotProduct_sumElim, zero_dotProduct, zero_add]
      simp [dotProduct, hq2]
    linarith
  · rw [hY_sh, hX_sh σ τ]
    ring

/-- Boundedness-based domination between any two energies `V₁, V₂` on `((μ₀ p.1).prod γ)`. -/
private lemma integral_pi_tilted_prod_nonneg_le_exp_mul
    {Ω W α β R : Type*} [MeasurableSpace Ω] [MeasurableSpace W] [MeasurableSpace α]
    [MeasurableSpace β] [Fintype R]
    (P₀ : Measure Ω) [IsProbabilityMeasure P₀]
    (μ_base : Measure α) [IsFiniteMeasure μ_base] [NeZero μ_base]
    (γ_W : Measure W) [IsProbabilityMeasure γ_W]
    (γ : Measure β) [IsProbabilityMeasure γ]
    {E₀ : Ω → α → ℝ} (hE₀ : Measurable fun p : Ω × α => E₀ p.1 p.2)
    (hE₀i : ∀ ω, Integrable (fun a => Real.exp (E₀ ω a)) μ_base)
    {V₁ V₂ : W → α × β → ℝ}
    (hV₁ : Measurable fun p : W × (α × β) => V₁ p.1 p.2)
    (hV₂ : Measurable fun p : W × (α × β) => V₂ p.1 p.2)
    {B : ℝ} (hB₁ : ∀ w x, |V₁ w x| ≤ B) (hB₂ : ∀ w x, |V₂ w x| ≤ B)
    {g : Ω → (R → α) → ℝ}
    (hg : Measurable fun p : Ω × (R → α) => g p.1 p.2)
    (hg0 : ∀ ω a, 0 ≤ g ω a) {M_g : ℝ} (hgb : ∀ ω a, g ω a ≤ M_g) :
    ∫ p : Ω × W, ∫ σ : R → α × β, g p.1 (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => ((μ_base.tilted (E₀ p.1)).prod γ).tilted (V₁ p.2))
        ∂(P₀.prod γ_W) ≤
      Real.exp (4 * (Fintype.card R : ℝ) * B) *
      ∫ p : Ω × W, ∫ σ : R → α × β, g p.1 (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => ((μ_base.tilted (E₀ p.1)).prod γ).tilted (V₂ p.2))
        ∂(P₀.prod γ_W) := by
  have hB₁_le (w : W) (x : α × β) : V₁ w x ≤ B := le_of_abs_le (hB₁ w x)
  have hB₂_le (w : W) (x : α × β) : V₂ w x ≤ B := le_of_abs_le (hB₂ w x)
  have hμ₀ (ω : Ω) : IsProbabilityMeasure (μ_base.tilted (E₀ ω)) :=
    isProbabilityMeasure_tilted (hE₀i ω)
  have hV₁w (w : W) : Measurable (V₁ w) := hV₁.comp (measurable_const.prodMk measurable_id)
  have hV₂w (w : W) : Measurable (V₂ w) := hV₂.comp (measurable_const.prodMk measurable_id)
  have hdiff (w : W) (x : α × β) : |V₁ w x - V₂ w x| ≤ 2 * B := by
    refine (abs_sub _ _).trans ?_
    linarith [hB₁ w x, hB₂ w x]
  have hpt (p : Ω × W) :
      ∫ σ : R → α × β, g p.1 (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => ((μ_base.tilted (E₀ p.1)).prod γ).tilted (V₁ p.2)) ≤
      Real.exp (4 * (Fintype.card R : ℝ) * B) *
      ∫ σ : R → α × β, g p.1 (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => ((μ_base.tilted (E₀ p.1)).prod γ).tilted (V₂ p.2)) := by
    have hp2 : IsProbabilityMeasure (((μ_base.tilted (E₀ p.1)).prod γ).tilted (V₂ p.2)) :=
      isProbabilityMeasure_tilted_of_ae_le (hV₂w p.2).aemeasurable
        (ae_of_all _ fun x => hB₂_le p.2 x)
    have hgm_p : Measurable fun σ : R → α × β => g p.1 (fun r => (σ r).1) := by
      have hp_proj : Measurable fun σ : R → α × β => (p.1, fun r => (σ r).1) :=
        measurable_const.prodMk (measurable_pi_iff.2 fun r =>
          measurable_fst.comp (measurable_pi_apply r))
      exact hg.comp hp_proj
    have hgi_p : Integrable (fun σ : R → α × β => g p.1 (fun r => (σ r).1))
        (Measure.pi fun _ : R => ((μ_base.tilted (E₀ p.1)).prod γ).tilted (V₂ p.2)) :=
      Integrable.of_bound hgm_p.aestronglyMeasurable |M_g| (ae_of_all _ fun σ => by
        rw [Real.norm_of_nonneg (hg0 _ _)]
        exact (hgb _ _).trans (le_abs_self _))
    have hexp_V₂ : Integrable (fun x : α × β => Real.exp (V₂ p.2 x))
        ((μ_base.tilted (E₀ p.1)).prod γ) :=
      integrable_exp_of_ae_le (hV₂w p.2).aemeasurable (ae_of_all _ fun x => hB₂_le p.2 x)
    have hc := integral_pi_tilted_le_exp_mul_of_abs_sub_le (ι := R)
      (μ := (μ_base.tilted (E₀ p.1)).prod γ)
      (E₀ := V₂ p.2) (E₁ := V₁ p.2) hexp_V₂ ((hV₁w p.2).sub (hV₂w p.2))
      (C := 2 * B) (fun x => hdiff p.2 x)
      (Y := fun σ : R → α × β => g p.1 (fun r => (σ r).1))
      (fun _ => hg0 _ _) hgi_p
    have he : 2 * (Fintype.card R : ℝ) * (2 * B) = 4 * (Fintype.card R : ℝ) * B := by ring
    rwa [he] at hc
  let G_obs (p : Ω × W) (σ : R → α × β) : ℝ := g p.1 (fun r => (σ r).1)
  have hGm : Measurable fun q : (Ω × W) × (R → α × β) => G_obs q.1 q.2 := by
    have hp : Measurable fun q : (Ω × W) × (R → α × β) => (q.1.1, fun r => (q.2 r).1) :=
      (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun r =>
        measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
    exact hg.comp hp
  have hint (V : W → α × β → ℝ) (hV : Measurable fun p : W × (α × β) => V p.1 p.2)
      (hB : ∀ w x, V w x ≤ B) :
      Integrable (fun p : Ω × W => ∫ σ : R → α × β, g p.1 (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => ((μ_base.tilted (E₀ p.1)).prod γ).tilted (V p.2)))
        (P₀.prod γ_W) := by
    let V_obs (p : Ω × W) (x : α × β) : ℝ := V p.2 x
    have hVm : Measurable fun q : (Ω × W) × (α × β) => V_obs q.1 q.2 :=
      hV.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have hm := measurable_integral_pi_tilted_prod_tilted μ_base γ hE₀ hE₀i hVm hGm
    refine Integrable.of_bound hm.aestronglyMeasurable |M_g| (ae_of_all _ fun p => ?_)
    have hp_prob : IsProbabilityMeasure (((μ_base.tilted (E₀ p.1)).prod γ).tilted (V p.2)) :=
      isProbabilityMeasure_tilted_of_ae_le
        (hV.comp (measurable_const.prodMk measurable_id)).aemeasurable
        (ae_of_all _ fun x => hB p.2 x)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => hg0 _ _)]
    exact (le_abs_self _).trans (abs_integral_le_of_forall_abs_le _ fun _ => by
      rw [abs_of_nonneg (hg0 _ _)]
      exact (hgb _ _).trans (le_abs_self _))
  have hi1 := hint V₁ hV₁ hB₁_le
  have hi2 := (hint V₂ hV₂ hB₂_le).const_mul (Real.exp (4 * (Fintype.card R : ℝ) * B))
  exact (integral_mono hi1 hi2 hpt).trans_eq (integral_const_mul _ _)

/-- **Endpoint `ϑ = 0` of the model-free rotation.** -/
private lemma rotation_endpoint_zero_eq
    {Ω₀ : Type uΩ} {α : Type uα} {K₁ K₂ : Type} {R : Type uR}
    [MeasurableSpace Ω₀] [MeasurableSpace α] [Fintype K₁] [Fintype K₂] [Fintype R]
    (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (μ_base : Measure α) [IsFiniteMeasure μ_base] [NeZero μ_base]
    {E₀ : Ω₀ → α → ℝ} (hE₀ : Measurable fun p : Ω₀ × α => E₀ p.1 p.2)
    (hE₀i : ∀ ω, Integrable (fun a => Real.exp (E₀ ω a)) μ_base)
    {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    (X_fn : (K₁ → ℝ) → α × (K₂ → ℝ) → ℝ)
    (hXm : Measurable fun p : (K₁ → ℝ) × (α × (K₂ → ℝ)) => X_fn p.1 p.2)
    (ψ : R → ℝ → ℝ) (hψm : ∀ r, Measurable (ψ r)) {M₀ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀)
    {f : Ω₀ → (R → α) → ℝ} (hf : Measurable fun p : Ω₀ × (R → α) => f p.1 p.2)
    {M_f : ℝ} (hfb : ∀ ω a, |f ω a| ≤ M_f) :
    let γ₁ := Measure.pi fun _ : K₁ => gaussianReal 0 1
    let γ₂ := Measure.pi fun _ : K₂ => gaussianReal 0 1
    let γ_sh := Measure.pi fun _ : K₁ ⊕ Unit => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : K₂ ⊕ Unit => gaussianReal 0 1
    let μ₀ (ω : Ω₀) := μ_base.tilted (E₀ ω)
    ∫ ω, ∫ w : K₁ ⊕ Unit → ℝ, ∫ σ : R → α × (K₂ ⊕ Unit → ℝ),
        f ω (fun r => (σ r).1) * ∏ r, ψ r (X_fn (w ∘ Sum.inl) ((σ r).1, (σ r).2 ∘ Sum.inl))
        ∂(Measure.pi fun _ : R => ((μ₀ ω).prod γ_aux).tilted
          (fun q => u (X_fn (w ∘ Sum.inl) (q.1, q.2 ∘ Sum.inl))))
        ∂γ_sh ∂P₀ =
      ∫ p : Ω₀ × (K₁ → ℝ), ∫ a : R → α × (K₂ → ℝ),
        f p.1 (fun r => (a r).1) * ∏ r, ψ r (X_fn p.2 (a r))
        ∂(Measure.pi fun _ : R => ((μ₀ p.1).prod γ₂).tilted (fun x => u (X_fn p.2 x)))
        ∂(P₀.prod γ₁) := by
  intro γ₁ γ₂ γ_sh γ_aux μ₀
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  have hμ₀_prob (ω : Ω₀) : IsProbabilityMeasure (μ₀ ω) := isProbabilityMeasure_tilted (hE₀i ω)
  let e_sh : (K₁ ⊕ Unit → ℝ) ≃ᵐ (K₁ → ℝ) × (Unit → ℝ) :=
    MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ
  have hmp_sh :
      MeasurePreserving ⇑e_sh γ_sh (γ₁.prod (Measure.pi fun _ : Unit => gaussianReal 0 1)) :=
    measurePreserving_sumPiEquivProdPi fun _ => gaussianReal 0 1
  let e_aux : α × (K₂ ⊕ Unit → ℝ) ≃ᵐ (α × (K₂ → ℝ)) × (Unit → ℝ) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl α)
      (MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ)).trans
      MeasurableEquiv.prodAssoc.symm
  have he_aux_fst (q : α × (K₂ ⊕ Unit → ℝ)) : (e_aux q).1 = (q.1, q.2 ∘ Sum.inl) := rfl
  have hmp_aux (ω : Ω₀) : MeasurePreserving ⇑e_aux ((μ₀ ω).prod γ_aux)
      (((μ₀ ω).prod γ₂).prod (Measure.pi fun _ : Unit => gaussianReal 0 1)) := by
    have h1 := (MeasurePreserving.id (μ₀ ω)).prod
      (measurePreserving_sumPiEquivProdPi fun _ : K₂ ⊕ Unit => gaussianReal 0 1)
    exact (measurePreserving_prodAssoc _ _ _).symm.comp h1
  have hinner (ω : Ω₀) (w₁ : K₁ → ℝ) :
      ∫ σ : R → α × (K₂ ⊕ Unit → ℝ),
        f ω (fun r => (σ r).1) * ∏ r, ψ r (X_fn w₁ ((σ r).1, (σ r).2 ∘ Sum.inl))
        ∂(Measure.pi fun _ : R => ((μ₀ ω).prod γ_aux).tilted
          (fun q => u (X_fn w₁ (q.1, q.2 ∘ Sum.inl)))) =
      ∫ a : R → α × (K₂ → ℝ),
        f ω (fun r => (a r).1) * ∏ r, ψ r (X_fn w₁ (a r))
        ∂(Measure.pi fun _ : R => ((μ₀ ω).prod γ₂).tilted (fun x => u (X_fn w₁ x))) := by
    have hV_src_m : Measurable fun q : α × (K₂ ⊕ Unit → ℝ) =>
        u (X_fn w₁ (q.1, q.2 ∘ Sum.inl)) := by
      have hp : Measurable fun q : α × (K₂ ⊕ Unit → ℝ) => (w₁, (q.1, q.2 ∘ Sum.inl)) :=
        measurable_const.prodMk (measurable_fst.prodMk (measurable_pi_iff.2 fun k =>
          (measurable_pi_apply (Sum.inl k)).comp measurable_snd))
      exact hu.comp (hXm.comp hp)
    have hprob_src : IsProbabilityMeasure
        (((μ₀ ω).prod γ_aux).tilted (fun q => u (X_fn w₁ (q.1, q.2 ∘ Sum.inl)))) :=
      isProbabilityMeasure_tilted_of_ae_le hV_src_m.aemeasurable (ae_of_all _ fun _ => hB_le _)
    have hmap_tilt : (((μ₀ ω).prod γ_aux).tilted
        (fun q => u (X_fn w₁ (q.1, q.2 ∘ Sum.inl)))).map e_aux =
        ((((μ₀ ω).prod γ₂).prod (Measure.pi fun _ : Unit => gaussianReal 0 1)).tilted
          (fun y => u (X_fn w₁ y.1) + (0 : (Unit → ℝ) → ℝ) y.2)) := by
      rw [map_tilted_measurableEquiv e_aux (hmp_aux ω) hV_src_m]
      congr 1; ext y
      obtain ⟨q, rfl⟩ := e_aux.surjective y
      simp [MeasurableEquiv.symm_apply_apply, he_aux_fst]
    let G (a : R → α × (K₂ → ℝ)) : ℝ := f ω (fun r => (a r).1) * ∏ r, ψ r (X_fn w₁ (a r))
    have htrans := (integral_pi_map_equiv
      (((μ₀ ω).prod γ_aux).tilted (fun q => u (X_fn w₁ (q.1, q.2 ∘ Sum.inl)))) e_aux
      (fun τ => G (fun r => (τ r).1))).symm
    rw [hmap_tilt] at htrans
    have hprod := integral_pi_tilted_prod_add_mul (μ := (μ₀ ω).prod γ₂)
      (ν := Measure.pi fun _ : Unit => gaussianReal 0 1) (ι := R)
      (fun x => u (X_fn w₁ x)) (0 : (Unit → ℝ) → ℝ) G (fun _ => 1)
    simp only [tilted_zero, integral_const, probReal_univ, one_smul, mul_one] at hprod
    exact htrans.trans hprod
  simp_rw [hinner]
  let I_fn (p : Ω₀ × (K₁ → ℝ)) : ℝ :=
    ∫ a : R → α × (K₂ → ℝ),
      f p.1 (fun r => (a r).1) * ∏ r, ψ r (X_fn p.2 (a r))
      ∂(Measure.pi fun _ : R => ((μ₀ p.1).prod γ₂).tilted (fun x => u (X_fn p.2 x)))
  have hIm : Measurable I_fn := by
    have hVm : Measurable fun p : (Ω₀ × (K₁ → ℝ)) × (α × (K₂ → ℝ)) => u (X_fn p.1.2 p.2) :=
      hu.comp (hXm.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    have hFm : Measurable fun p : (Ω₀ × (K₁ → ℝ)) × (R → α × (K₂ → ℝ)) =>
        f p.1.1 (fun r => (p.2 r).1) * ∏ r, ψ r (X_fn p.1.2 (p.2 r)) := by
      have hp_f : Measurable fun p : (Ω₀ × (K₁ → ℝ)) × (R → α × (K₂ → ℝ)) =>
          (p.1.1, fun r => (p.2 r).1) :=
        (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun r =>
          measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
      have hpr : Measurable fun p : (Ω₀ × (K₁ → ℝ)) × (R → α × (K₂ → ℝ)) =>
          ∏ r, ψ r (X_fn p.1.2 (p.2 r)) :=
        Finset.measurable_prod _ fun r _ => (hψm r).comp (hXm.comp
          ((measurable_snd.comp measurable_fst).prodMk
            ((measurable_pi_apply r).comp measurable_snd)))
      exact (hf.comp hp_f).mul hpr
    exact measurable_integral_pi_tilted_prod_tilted μ_base γ₂ hE₀ hE₀i hVm hFm
  have hIb (p : Ω₀ × (K₁ → ℝ)) : |I_fn p| ≤ |M_f| * |M₀| ^ Fintype.card R := by
    have hVx : Measurable fun x : α × (K₂ → ℝ) => u (X_fn p.2 x) :=
      hu.comp (hXm.comp (measurable_const.prodMk measurable_id))
    have : IsProbabilityMeasure (((μ₀ p.1).prod γ₂).tilted (fun x => u (X_fn p.2 x))) :=
      isProbabilityMeasure_tilted_of_ae_le hVx.aemeasurable (ae_of_all _ fun _ => hB_le _)
    exact abs_integral_le_of_forall_abs_le _ fun a => by
      rw [abs_mul, Finset.abs_prod]
      exact mul_le_mul ((hfb _ _).trans (le_abs_self _))
        ((Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ =>
          (hM₀ r _).trans (le_abs_self _)).trans_eq (by simp))
        (Finset.prod_nonneg fun _ _ => abs_nonneg _) (abs_nonneg _)
  have hIi : Integrable I_fn (P₀.prod γ₁) :=
    Integrable.of_bound hIm.aestronglyMeasurable _
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hIb p)
  have hw_eq (ω : Ω₀) :
      ∫ w : K₁ ⊕ Unit → ℝ, I_fn (ω, w ∘ Sum.inl) ∂γ_sh = ∫ w₁ : K₁ → ℝ, I_fn (ω, w₁) ∂γ₁ := by
    have hm_ω : Measurable fun w₁ : K₁ → ℝ => I_fn (ω, w₁) :=
      hIm.comp (measurable_const.prodMk measurable_id)
    have h1 := hmp_sh.integral_comp_of_aestronglyMeasurable
      (g := fun p : (K₁ → ℝ) × (Unit → ℝ) => I_fn (ω, p.1))
      (hm_ω.comp measurable_fst).aestronglyMeasurable
    exact h1.trans (integral_prod_fun_fst_of_isProbabilityMeasure γ₁
      (Measure.pi fun _ : Unit => gaussianReal 0 1) (fun w₁ => I_fn (ω, w₁)))
  change (∫ ω, ∫ w, I_fn (ω, w ∘ Sum.inl) ∂γ_sh ∂P₀) = ∫ p, I_fn p ∂(P₀.prod γ₁)
  simp_rw [hw_eq]
  exact (integral_prod _ hIi).symm

/-- **Endpoint `ϑ = π / 2` of the model-free rotation (unweighted and weighted).** -/
private lemma rotation_endpoint_pi_div_two_eq
    {Ω₀ : Type uΩ} {α : Type uα} {K₁ K₂ : Type} {R : Type uR}
    [MeasurableSpace Ω₀] [MeasurableSpace α] [Fintype K₁] [Fintype K₂] [Fintype R]
    (P₀ : Measure Ω₀) (μ_base : Measure α) [NeZero μ_base]
    {E₀ : Ω₀ → α → ℝ}
    (hE₀i : ∀ ω, Integrable (fun a => Real.exp (E₀ ω a)) μ_base)
    {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    (q : ℝ) (f : Ω₀ → (R → α) → ℝ) :
    let γ_sh := Measure.pi fun _ : K₁ ⊕ Unit => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : K₂ ⊕ Unit => gaussianReal 0 1
    let μ₀ (ω : Ω₀) := μ_base.tilted (E₀ ω)
    let Y_fn (w : K₁ ⊕ Unit → ℝ) (y : α × (K₂ ⊕ Unit → ℝ)) : ℝ :=
      Real.sqrt q * w (Sum.inr ()) + Real.sqrt (1 - q) * y.2 (Sum.inr ())
    let rhat := perceptronRhat u q
    (∫ ω, ∫ w : K₁ ⊕ Unit → ℝ, ∫ σ : R → α × (K₂ ⊕ Unit → ℝ),
        f ω (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => ((μ₀ ω).prod γ_aux).tilted (fun y => u (Y_fn w y)))
        ∂γ_sh ∂P₀ =
      ∫ ω, ∫ a : R → α, f ω a ∂(Measure.pi fun _ : R => μ₀ ω) ∂P₀) ∧
    (∀ {r₁ r₂ : R}, r₁ ≠ r₂ →
      ∫ ω, ∫ w : K₁ ⊕ Unit → ℝ, ∫ σ : R → α × (K₂ ⊕ Unit → ℝ),
          f ω (fun r => (σ r).1) * (deriv u (Y_fn w (σ r₁)) * deriv u (Y_fn w (σ r₂)))
          ∂(Measure.pi fun _ : R => ((μ₀ ω).prod γ_aux).tilted (fun y => u (Y_fn w y)))
          ∂γ_sh ∂P₀ =
        rhat * ∫ ω, ∫ a : R → α, f ω a ∂(Measure.pi fun _ : R => μ₀ ω) ∂P₀) := by
  intro γ_sh γ_aux μ₀ Y_fn rhat
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hB x)
  have hμ₀_prob (ω : Ω₀) : IsProbabilityMeasure (μ₀ ω) := isProbabilityMeasure_tilted (hE₀i ω)
  let γ₁ := Measure.pi fun _ : K₁ => gaussianReal 0 1
  let γ₂ := Measure.pi fun _ : K₂ => gaussianReal 0 1
  let e_u : (Unit → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique Unit ℝ
  have hmp_u : MeasurePreserving ⇑e_u
      (Measure.pi fun _ : Unit => gaussianReal 0 1) (gaussianReal 0 1) :=
    measurePreserving_funUnique (gaussianReal 0 1) Unit
  let e_sh : (K₁ ⊕ Unit → ℝ) ≃ᵐ (K₁ → ℝ) × ℝ :=
    (MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) e_u)
  have hmp_sh : MeasurePreserving ⇑e_sh γ_sh (γ₁.prod (gaussianReal 0 1)) :=
    ((MeasurePreserving.id γ₁).prod hmp_u).comp
      (measurePreserving_sumPiEquivProdPi fun _ => gaussianReal 0 1)
  let e_aux : α × (K₂ ⊕ Unit → ℝ) ≃ᵐ (α × (K₂ → ℝ)) × ℝ :=
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl α)
      (MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ)).trans
      MeasurableEquiv.prodAssoc.symm).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) e_u)
  have he_aux_snd (y : α × (K₂ ⊕ Unit → ℝ)) : (e_aux y).2 = y.2 (Sum.inr ()) := rfl
  have hmp_aux (ω : Ω₀) : MeasurePreserving ⇑e_aux ((μ₀ ω).prod γ_aux)
      (((μ₀ ω).prod γ₂).prod (gaussianReal 0 1)) := by
    have h1 := (MeasurePreserving.id (μ₀ ω)).prod
      (measurePreserving_sumPiEquivProdPi fun _ : K₂ ⊕ Unit => gaussianReal 0 1)
    have h2 := (measurePreserving_prodAssoc _ _ _).symm.comp h1
    exact ((MeasurePreserving.id _).prod hmp_u).comp h2
  have hinner_fact (ω : Ω₀) (w : K₁ ⊕ Unit → ℝ) (H : (R → ℝ) → ℝ) :
      ∫ σ : R → α × (K₂ ⊕ Unit → ℝ),
        f ω (fun r => (σ r).1) * H (fun r => (σ r).2 (Sum.inr ()))
        ∂(Measure.pi fun _ : R => ((μ₀ ω).prod γ_aux).tilted (fun y => u (Y_fn w y))) =
      (∫ a : R → α, f ω a ∂(Measure.pi fun _ : R => μ₀ ω)) *
        ∫ τ : R → ℝ, H τ ∂(Measure.pi fun _ : R =>
          (gaussianReal 0 1).tilted fun ξ =>
            u (Real.sqrt q * w (Sum.inr ()) + Real.sqrt (1 - q) * ξ)) := by
    have hY_m : Measurable fun y : α × (K₂ ⊕ Unit → ℝ) => u (Y_fn w y) :=
      hu.comp (by dsimp only [Y_fn]; fun_prop)
    have hprob_src : IsProbabilityMeasure (((μ₀ ω).prod γ_aux).tilted (fun y => u (Y_fn w y))) :=
      isProbabilityMeasure_tilted_of_ae_le hY_m.aemeasurable (ae_of_all _ fun _ => hB_le _)
    have hprob_z : IsProbabilityMeasure
        ((gaussianReal 0 1).tilted fun ξ =>
          u (Real.sqrt q * w (Sum.inr ()) + Real.sqrt (1 - q) * ξ)) :=
      isProbabilityMeasure_tilted (integrable_exp_cavityPath_new hu hB_le q (w (Sum.inr ())))
    have hmap_tilt : (((μ₀ ω).prod γ_aux).tilted (fun y => u (Y_fn w y))).map e_aux =
        ((((μ₀ ω).prod γ₂).prod (gaussianReal 0 1)).tilted
          (fun p => (0 : α × (K₂ → ℝ) → ℝ) p.1 +
            u (Real.sqrt q * w (Sum.inr ()) + Real.sqrt (1 - q) * p.2))) := by
      rw [map_tilted_measurableEquiv e_aux (hmp_aux ω) hY_m]
      congr 1; ext p
      obtain ⟨y, rfl⟩ := e_aux.surjective p
      simp [MeasurableEquiv.symm_apply_apply, Y_fn, he_aux_snd]
    have htrans := (integral_pi_map_equiv
      (((μ₀ ω).prod γ_aux).tilted (fun y => u (Y_fn w y))) e_aux
      (fun σ => f ω (fun r => (σ r).1.1) * H (fun r => (σ r).2))).symm
    rw [hmap_tilt] at htrans
    have hprod := integral_pi_tilted_prod_add_mul (μ := (μ₀ ω).prod γ₂) (ν := gaussianReal 0 1)
      (ι := R) (0 : α × (K₂ → ℝ) → ℝ)
      (fun ξ => u (Real.sqrt q * w (Sum.inr ()) + Real.sqrt (1 - q) * ξ))
      (fun b => f ω (fun r => (b r).1)) H
    simp only [tilted_zero] at hprod
    have hb_eq : ∫ b : R → α × (K₂ → ℝ), f ω (fun r => (b r).1)
        ∂(Measure.pi fun _ : R => (μ₀ ω).prod γ₂) =
      ∫ a : R → α, f ω a ∂(Measure.pi fun _ : R => μ₀ ω) := by
      have hp1 := integral_pi_prod_mul (ι := R) (μ₀ ω) γ₂ (f ω) (fun _ => 1)
      simpa using hp1
    rw [hb_eq] at hprod
    exact htrans.trans hprod
  constructor
  · have hpt (ω : Ω₀) (w : K₁ ⊕ Unit → ℝ) :
        ∫ σ : R → α × (K₂ ⊕ Unit → ℝ), f ω (fun r => (σ r).1)
          ∂(Measure.pi fun _ : R => ((μ₀ ω).prod γ_aux).tilted (fun y => u (Y_fn w y))) =
        ∫ a : R → α, f ω a ∂(Measure.pi fun _ : R => μ₀ ω) := by
      have hprob_z : IsProbabilityMeasure
          ((gaussianReal 0 1).tilted fun ξ =>
            u (Real.sqrt q * w (Sum.inr ()) + Real.sqrt (1 - q) * ξ)) :=
        isProbabilityMeasure_tilted (integrable_exp_cavityPath_new hu hB_le q (w (Sum.inr ())))
      simpa using hinner_fact ω w (fun _ => 1)
    simp_rw [hpt]
    exact integral_congr_ae (ae_of_all _ fun _ => by simp)
  · intro r₁ r₂ hr
    let ρ_z (z : ℝ) : ℝ :=
      ((∫ ξ, deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ) *
          Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1) /
        ∫ ξ, Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1) ^ 2
    have hρ_m : Measurable ρ_z := by
      have hNm : Measurable fun z => ∫ ξ, deriv u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ) *
          Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1 := by
        have hj : Measurable fun p : ℝ × ℝ =>
            deriv u (Real.sqrt q * p.1 + Real.sqrt (1 - q) * p.2) *
              Real.exp (u (Real.sqrt q * p.1 + Real.sqrt (1 - q) * p.2)) :=
          ((measurable_deriv u).comp (by fun_prop)).mul
            (Real.measurable_exp.comp (hu.comp (by fun_prop)))
        exact (hj.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable
      have hZm : Measurable fun z =>
          ∫ ξ, Real.exp (u (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)) ∂gaussianReal 0 1 := by
        have hj : Measurable fun p : ℝ × ℝ =>
            Real.exp (u (Real.sqrt q * p.1 + Real.sqrt (1 - q) * p.2)) :=
          Real.measurable_exp.comp (hu.comp (by fun_prop))
        exact (hj.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable
      exact (hNm.div hZm).pow_const 2
    have hpt (ω : Ω₀) (w : K₁ ⊕ Unit → ℝ) :
        ∫ σ : R → α × (K₂ ⊕ Unit → ℝ),
          f ω (fun r => (σ r).1) * (deriv u (Y_fn w (σ r₁)) * deriv u (Y_fn w (σ r₂)))
          ∂(Measure.pi fun _ : R => ((μ₀ ω).prod γ_aux).tilted (fun y => u (Y_fn w y))) =
        (∫ a : R → α, f ω a ∂(Measure.pi fun _ : R => μ₀ ω)) * ρ_z (w (Sum.inr ())) := by
      have hprob_z : IsProbabilityMeasure
          ((gaussianReal 0 1).tilted fun ξ =>
            u (Real.sqrt q * w (Sum.inr ()) + Real.sqrt (1 - q) * ξ)) :=
        isProbabilityMeasure_tilted (integrable_exp_cavityPath_new hu hB_le q (w (Sum.inr ())))
      have h1 := hinner_fact ω w (fun τ =>
        deriv u (Real.sqrt q * w (Sum.inr ()) + Real.sqrt (1 - q) * τ r₁) *
          deriv u (Real.sqrt q * w (Sum.inr ()) + Real.sqrt (1 - q) * τ r₂))
      have hdu_m : Measurable fun ξ : ℝ =>
          deriv u (Real.sqrt q * w (Sum.inr ()) + Real.sqrt (1 - q) * ξ) :=
        (measurable_deriv u).comp (by fun_prop)
      rw [integral_pi_mul_of_ne _ hr hdu_m hdu_m, ← sq, integral_tilted_eq_div] at h1
      exact h1
    simp_rw [hpt, integral_const_mul]
    have hw_rhat : ∫ w : K₁ ⊕ Unit → ℝ, ρ_z (w (Sum.inr ())) ∂γ_sh = rhat := by
      have h1 := hmp_sh.integral_comp_of_aestronglyMeasurable
        (g := fun p : (K₁ → ℝ) × ℝ => ρ_z p.2)
        (hρ_m.comp measurable_snd).aestronglyMeasurable
      have h2 : ∫ p : (K₁ → ℝ) × ℝ, ρ_z p.2 ∂(γ₁.prod (gaussianReal 0 1)) = rhat := by
        have hp := integral_prod_mul (μ := γ₁) (ν := gaussianReal 0 1) (fun _ => (1 : ℝ)) ρ_z
        simpa using hp
      exact h1.trans h2
    simp_rw [hw_rhat, mul_comm _ rhat, integral_const_mul]

section RotationDerivative

/-- Measurability of the `s`-interpolating rotated field. -/
private lemma measurable_interp_rotation_field {N : ℕ} {α : Type uα} [MeasurableSpace α]
    {π : α → PerceptronSpin N} (hπ : Measurable π) (s t q ϑ : ℝ) :
    let K₁ := (Fin N ⊕ Unit) ⊕ Unit
    let K₂ := Fin 2
    let X_sh : PerceptronSpin N → K₁ ⊕ Unit → ℝ :=
      fun σ => Sum.elim
        (Sum.elim (Real.sqrt s • cavityCoef N t σ) (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) 0
    let Y_sh : K₁ ⊕ Unit → ℝ := Sum.elim 0 (fun _ => Real.sqrt q)
    let X_aux : K₂ ⊕ Unit → ℝ :=
      Sum.elim ![Real.sqrt s * Real.sqrt ((1 - t) / (N + 1)),
        Real.sqrt (1 - s) * Real.sqrt (1 - q)] 0
    let Y_aux : K₂ ⊕ Unit → ℝ := Sum.elim 0 (fun _ => Real.sqrt (1 - q))
    Measurable fun p : (K₁ ⊕ Unit → ℝ) × (α × (K₂ ⊕ Unit → ℝ)) =>
      Real.cos ϑ * (X_sh (π p.2.1) ⬝ᵥ p.1 + X_aux ⬝ᵥ p.2.2) +
        Real.sin ϑ * (Y_sh ⬝ᵥ p.1 + Y_aux ⬝ᵥ p.2.2) := by
  intro K₁ K₂ X_sh Y_sh X_aux Y_aux
  have hX (j : K₁ ⊕ Unit) :
      Measurable fun p : (K₁ ⊕ Unit → ℝ) × (α × (K₂ ⊕ Unit → ℝ)) => X_sh (π p.2.1) j :=
    (measurable_of_finite fun σ => X_sh σ j).comp (hπ.comp (measurable_fst.comp measurable_snd))
  have hdotX : Measurable fun p : (K₁ ⊕ Unit → ℝ) × (α × (K₂ ⊕ Unit → ℝ)) =>
      X_sh (π p.2.1) ⬝ᵥ p.1 := by
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun j _ =>
      (hX j).mul ((measurable_pi_apply j).comp measurable_fst)
  have hdotY : Measurable fun p : (K₁ ⊕ Unit → ℝ) × (α × (K₂ ⊕ Unit → ℝ)) =>
      Y_sh ⬝ᵥ p.1 := by
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun j _ =>
      measurable_const.mul ((measurable_pi_apply j).comp measurable_fst)
  have hdotXa : Measurable fun p : (K₁ ⊕ Unit → ℝ) × (α × (K₂ ⊕ Unit → ℝ)) =>
      X_aux ⬝ᵥ p.2.2 := by
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun j _ =>
      measurable_const.mul ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))
  have hdotYa : Measurable fun p : (K₁ ⊕ Unit → ℝ) × (α × (K₂ ⊕ Unit → ℝ)) =>
      Y_aux ⬝ᵥ p.2.2 := by
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun j _ =>
      measurable_const.mul ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))
  exact ((hdotX.add hdotXa).const_mul _).add ((hdotY.add hdotYa).const_mul _)

/-- **Angle derivative bound for the `s`-interpolating cavity rotation (`s, t, q ∈ [0, 1]`).** -/
private lemma exists_hasDerivAt_interp_rotation_abs_le_of_pair_bound
    {N : ℕ} {Ω₀ : Type uΩ} {α : Type uα} {R : Type uR}
    [MeasurableSpace Ω₀] [MeasurableSpace α] [Fintype R]
    (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (μ_base : Measure α) [IsFiniteMeasure μ_base] [NeZero μ_base]
    {E₀ : Ω₀ → α → ℝ} (hE₀ : Measurable fun p : Ω₀ × α => E₀ p.1 p.2)
    (hE₀i : ∀ ω, Integrable (fun a => Real.exp (E₀ ω a)) μ_base)
    (π : α → PerceptronSpin N) (hπ : Measurable π)
    {s t q : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1)
    {u : ℝ → ℝ} {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    (hψ₂d : ∀ r, Differentiable ℝ (deriv (ψ r)))
    {M₀ M₁ M₂ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀)
    (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁)
    (hM₂ : ∀ r x, |deriv (deriv (ψ r)) x| ≤ M₂)
    {f : Ω₀ → (R → α) → ℝ} (hf : Measurable fun p : Ω₀ × (R → α) => f p.1 p.2)
    {M_f : ℝ} (hfb : ∀ ω a, |f ω a| ≤ M_f)
    (ϑ : ℝ) {m : ℝ} (hm : 0 ≤ m) :
    let γ_sh := Measure.pi fun _ : (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : (Fin 2 ⊕ Unit) => gaussianReal 0 1
    let μ₀ (ω : Ω₀) := μ_base.tilted (E₀ ω)
    let X_sh : PerceptronSpin N → (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ :=
      fun σ => Sum.elim
        (Sum.elim (Real.sqrt s • cavityCoef N t σ) (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) 0
    let Y_sh : (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ := Sum.elim 0 (fun _ => Real.sqrt q)
    let X_aux : (Fin 2 ⊕ Unit) → ℝ :=
      Sum.elim ![Real.sqrt s * Real.sqrt ((1 - t) / (N + 1)),
        Real.sqrt (1 - s) * Real.sqrt (1 - q)] 0
    let Y_aux : (Fin 2 ⊕ Unit) → ℝ := Sum.elim 0 (fun _ => Real.sqrt (1 - q))
    let S (ϑ' : ℝ) (w : (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)
        (x : α × ((Fin 2 ⊕ Unit) → ℝ)) : ℝ :=
      Real.cos ϑ' * (X_sh (π x.1) ⬝ᵥ w + X_aux ⬝ᵥ x.2) +
        Real.sin ϑ' * (Y_sh ⬝ᵥ w + Y_aux ⬝ᵥ x.2)
    let ν (p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) :=
      ((μ₀ p.1).prod γ_aux).tilted fun x => u (S ϑ p.2 x)
    let F (p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ))
        (a : R → α × ((Fin 2 ⊕ Unit) → ℝ)) := f p.1 (fun r => (a r).1)
    let d_spin (σ τ : PerceptronSpin N) : ℝ :=
      |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
        ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
    let n : ℝ := Fintype.card R
    let L := 1 + |D| + |M₀| + |M₁| + |M₀| * |D|
    (∀ (ι : Type uR) [Fintype ι] (e : R → ι), Function.Injective e → ∀ i j, i ≠ j →
      ∫ p, ∫ a : ι → α × ((Fin 2 ⊕ Unit) → ℝ),
        |f p.1 (fun r => (a (e r)).1)| * d_spin (π (a i).1) (π (a j).1)
        ∂(Measure.pi fun _ : ι => ν p) ∂(P₀.prod γ_sh) ≤ m) →
    ∃ z,
      HasDerivAt
        (fun ϑ' => ∫ ω, ∫ w, ∫ σ : R → α × ((Fin 2 ⊕ Unit) → ℝ),
            f ω (fun r => (σ r).1) * ∏ r, ψ r (S ϑ' w (σ r))
            ∂(Measure.pi fun _ : R => ((μ₀ ω).prod γ_aux).tilted (fun x => u (S ϑ' w x)))
            ∂γ_sh ∂P₀)
        (Real.sin ϑ * Real.cos ϑ * z) ϑ ∧
      |z| ≤ (4 * n ^ 2 + n) * L ^ (Fintype.card R + 2) *
        (m + 1 / (N + 1) *
          ∫ p, ∫ a, |F p a| ∂(Measure.pi fun _ : R => ν p) ∂(P₀.prod γ_sh)) := by
  classical
  intro γ_sh γ_aux μ₀ X_sh Y_sh X_aux Y_aux S ν F d_spin n L hpair
  have hB_le : ∀ x, u x ≤ B := fun x => le_of_abs_le (hu.abs_le x)
  have hμ₀ (ω : Ω₀) : IsProbabilityMeasure (μ₀ ω) := isProbabilityMeasure_tilted (hE₀i ω)
  let W := (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ
  let T := α × ((Fin 2 ⊕ Unit) → ℝ)
  have hS_m (ϑ' : ℝ) : Measurable fun p : W × T => S ϑ' p.1 p.2 :=
    measurable_interp_rotation_field hπ s t q ϑ'
  have hV (p : Ω₀ × W) : Measurable fun x : T => u (S ϑ p.2 x) := by
    have hp : Measurable fun x : T => (p.2, x) := measurable_const.prodMk measurable_id
    have hsV := (hS_m ϑ).comp hp
    exact hu.measurable.comp hsV
  have hν_prob (p : Ω₀ × W) : IsProbabilityMeasure (ν p) :=
    isProbabilityMeasure_tilted_of_ae_le (hV p).aemeasurable (ae_of_all _ fun _ => hB_le _)
  have hmν {ι : Type uR} [Fintype ι] {G : Ω₀ × W → (ι → T) → ℝ}
      (hG : Measurable fun p : (Ω₀ × W) × (ι → T) => G p.1 p.2) :
      Measurable fun p => ∫ a, G p a ∂(Measure.pi fun _ : ι => ν p) := by
    let V_obs (p : Ω₀ × W) (x : T) : ℝ := u (S ϑ p.2 x)
    have hpV : Measurable fun p : (Ω₀ × W) × T => (p.1.2, p.2) :=
      (measurable_snd.comp measurable_fst).prodMk measurable_snd
    have hsV := (hS_m ϑ).comp hpV
    have hVm : Measurable fun p : (Ω₀ × W) × T => V_obs p.1 p.2 := hu.measurable.comp hsV
    exact measurable_integral_pi_tilted_prod_tilted μ_base γ_aux hE₀ hE₀i hVm hG
  have hfi (ω : Ω₀) : Integrable (f ω) (Measure.pi fun _ : R => μ₀ ω) := by
    have hp : Measurable fun a : R → α => (ω, a) := measurable_const.prodMk measurable_id
    have hm := hf.comp hp
    exact Integrable.of_bound hm.aestronglyMeasurable
      |M_f| (ae_of_all _ fun a => by rw [Real.norm_eq_abs]; exact (hfb ω a).trans (le_abs_self _))
  have hfi₁ : Integrable (fun ω => ∫ a, |f ω a| ∂(Measure.pi fun _ : R => μ₀ ω)) P₀ := by
    let f_abs (ω : Ω₀) (a : R → α) : ℝ := |f ω a|
    have hf_abs_m : Measurable fun p : Ω₀ × (R → α) => f_abs p.1 p.2 := by
      simpa only [f_abs, Real.norm_eq_abs] using hf.norm
    have hm1 := measurable_integral_pi_tilted (μ := μ_base) hE₀ hf_abs_m
    exact Integrable.of_bound hm1.aestronglyMeasurable |M_f| (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      exact abs_integral_le_of_forall_abs_le _ fun a => by
        rw [abs_abs]; exact (hfb ω a).trans (le_abs_self _))
  have hfm {ι : Type uR} (e : R → ι) :
      Measurable fun x : (Ω₀ × W) × (ι → T) => F x.1 (x.2 ∘ e) := by
    have hp : Measurable fun x : (Ω₀ × W) × (ι → T) =>
        ((x.1.1, fun r => (x.2 (e r)).1) : Ω₀ × (R → α)) :=
      (measurable_fst.comp measurable_fst).prodMk
        (measurable_pi_iff.2 fun r =>
          measurable_fst.comp ((measurable_pi_apply (e r)).comp measurable_snd))
    exact hf.comp hp
  have hfm_abs {ι : Type uR} (e : R → ι) :
      Measurable fun x : (Ω₀ × W) × (ι → T) => |F x.1 (x.2 ∘ e)| := by
    simpa only [Real.norm_eq_abs] using (hfm e).norm
  have hFI : ∀ᵐ p ∂P₀.prod γ_sh, Integrable (F p) (Measure.pi fun _ : R => ν p) :=
    ae_of_all _ fun p => by
      have hp : Measurable fun a : R → T => (p, a) := measurable_const.prodMk measurable_id
      have hm := (hfm id).comp hp
      exact Integrable.of_bound hm.aestronglyMeasurable |M_f|
        (ae_of_all _ fun a => by rw [Real.norm_eq_abs]; exact (hfb _ _).trans (le_abs_self _))
  have hF₁ : Integrable (fun p => ∫ a, |F p a| ∂(Measure.pi fun _ : R => ν p)) (P₀.prod γ_sh) := by
    let G_abs (p : Ω₀ × W) (a : R → T) : ℝ := |F p a|
    have hmG : Measurable fun x : (Ω₀ × W) × (R → T) => G_abs x.1 x.2 := hfm_abs id
    exact Integrable.of_bound (hmν hmG).aestronglyMeasurable |M_f| (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]
      exact abs_integral_le_of_forall_abs_le _ fun a => by
        rw [abs_abs]; exact (hfb _ _).trans (le_abs_self _))
  obtain ⟨horth_sh, horth_aux, hvar_X, hvar_Y, hcov⟩ := interp_cavity_rotation_dotProducts hs ht hq
  let C_cov (σ τ : PerceptronSpin N) := Y_sh ⬝ᵥ Y_sh - X_sh σ ⬝ᵥ X_sh τ
  let c (a b : T) := C_cov (π a.1) (π b.1)
  let d (a b : T) := d_spin (π a.1) (π b.1)
  let ε : ℝ := 1 / (N + 1)
  have hc (a b : T) : |c a b| ≤ d a b + ε := by
    change |C_cov (π a.1) (π b.1)| ≤ d a b + ε
    rw [show C_cov (π a.1) (π b.1) = s * (q - cavityCoef N t (π a.1) ⬝ᵥ cavityCoef N t (π b.1))
      from hcov _ _, abs_mul, abs_of_nonneg hs.1]
    calc s * |q - cavityCoef N t (π a.1) ⬝ᵥ cavityCoef N t (π b.1)|
        ≤ 1 * |q - cavityCoef N t (π a.1) ⬝ᵥ cavityCoef N t (π b.1)| :=
          mul_le_mul_of_nonneg_right hs.2 (abs_nonneg _)
      _ = |q - cavityCoef N t (π a.1) ⬝ᵥ cavityCoef N t (π b.1)| := one_mul _
      _ ≤ d a b + ε := abs_sub_cavityCoef_dotProduct_le ht q _ _
  have hd (a b : T) : d a b ≤ 2 := abs_perceptron_overlap_sub_le_two hq _ _
  have hdm : Measurable fun p : T × T => d p.1 p.2 := by
    let b : PerceptronSpin N × PerceptronSpin N → ℝ := fun p => d_spin p.1 p.2
    have hproj : Measurable fun p : T × T => (π p.1.1, π p.2.1) :=
      (hπ.comp (measurable_fst.comp measurable_fst)).prodMk
        (hπ.comp (measurable_fst.comp measurable_snd))
    have h := (measurable_of_finite b).comp hproj
    exact h
  have hcm : Measurable fun p : T × T => c p.1 p.2 := by
    let b : PerceptronSpin N × PerceptronSpin N → ℝ := fun p => C_cov p.1 p.2
    have hproj : Measurable fun p : T × T => (π p.1.1, π p.2.1) :=
      (hπ.comp (measurable_fst.comp measurable_fst)).prodMk
        (hπ.comp (measurable_fst.comp measurable_snd))
    have h := (measurable_of_finite b).comp hproj
    exact h
  let A₁ := ∫ p, ∫ a, |F p a| ∂(Measure.pi fun _ : R => ν p) ∂(P₀.prod γ_sh)
  let K := L ^ (Fintype.card R + 2)
  have hpos_MD : 0 ≤ |M₀| * |D| := mul_nonneg (abs_nonneg M₀) (abs_nonneg D)
  have hL : 1 ≤ L := by
    dsimp only [L]
    linarith [abs_nonneg M₀, abs_nonneg M₁, abs_nonneg D, hpos_MD]
  have hK : 0 ≤ K := pow_nonneg (zero_le_one.trans hL) _
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hA₁ : 0 ≤ A₁ := integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _
  have hTerm {ι : Type uR} [Fintype ι] (e : R → ι) (he : Function.Injective e)
      (i j : ι) (hij : i ≠ j) (H : Ω₀ × W → (ι → T) → ℝ)
      (hHm : Measurable fun x : (Ω₀ × W) × (ι → T) => H x.1 x.2)
      (hHb : ∀ p a, |H p a| ≤ K) :
      let J (ω : Ω₀) := ∫ w, ∫ a : ι → T, F (ω, w) (a ∘ e) * c (a i) (a j) * H (ω, w) a
        ∂(Measure.pi fun _ : ι => ν (ω, w)) ∂γ_sh
      Integrable J P₀ ∧ |∫ ω, J ω ∂P₀| ≤ K * (m + ε * A₁) := by
    have hp : Measurable fun x : (Ω₀ × W) × (ι → T) => (x.2 i, x.2 j) :=
      ((measurable_pi_apply i).comp measurable_snd).prodMk
        ((measurable_pi_apply j).comp measurable_snd)
    let M_obs (p : Ω₀ × W) (a : ι → T) : ℝ := |F p (a ∘ e)| * d (a i) (a j)
    let T_obs (p : Ω₀ × W) (a : ι → T) : ℝ := F p (a ∘ e) * c (a i) (a j) * H p a
    have hdp := hdm.comp hp
    have hcp := hcm.comp hp
    have hMm : Measurable fun x : (Ω₀ × W) × (ι → T) => M_obs x.1 x.2 :=
      (hfm_abs e).mul hdp
    have hTm : Measurable fun x : (Ω₀ × W) × (ι → T) => T_obs x.1 x.2 :=
      ((hfm e).mul hcp).mul hHm
    have hM := hmν hMm
    have hT := hmν hTm
    exact integrable_integral_pi_pair_mul_and_abs_le P₀ γ_sh ν he i j hFI hF₁ hdm
      (fun _ _ => abs_nonneg _) hd hε c hc H hK hHb
      hM.aestronglyMeasurable hT.aestronglyMeasurable
      (hpair ι e he i j hij)
  let ψ_d (r : R) (x : ℝ) := deriv (ψ r) x + ψ r x * deriv u x
  have hψm (r : R) : Measurable (ψ r) := (hψd r).continuous.measurable
  have hψdm (r : R) : Measurable (ψ_d r) :=
    (measurable_deriv _).add ((hψm r).mul (measurable_deriv _))
  have hψb (r : R) (x : ℝ) : |ψ r x| ≤ L :=
    (hM₀ r x).trans ((le_abs_self _).trans (by
      dsimp only [L]
      linarith [abs_nonneg M₀, abs_nonneg M₁, abs_nonneg D, hpos_MD]))
  have hbDu (x : ℝ) : |deriv u x| ≤ L :=
    (hu.abs_deriv_le x).trans ((le_abs_self _).trans (by
      dsimp only [L]
      linarith [abs_nonneg M₀, abs_nonneg M₁, abs_nonneg D, hpos_MD]))
  have hψdb (r : R) (x : ℝ) : |ψ_d r x| ≤ L := by
    have hh : |ψ r x * deriv u x| ≤ |M₀| * |D| := by
      rw [abs_mul]
      exact mul_le_mul ((hM₀ _ _).trans (le_abs_self _))
        ((hu.abs_deriv_le _).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)
    exact (abs_add_le _ _).trans ((add_le_add ((hM₁ _ _).trans (le_abs_self _)) hh).trans
      (by dsimp only [L]; linarith [abs_nonneg M₀, abs_nonneg M₁, abs_nonneg D]))
  have hfield {ι : Type uR} (i : ι) :
      Measurable fun x : (Ω₀ × W) × (ι → T) => S ϑ x.1.2 (x.2 i) := by
    have hp : Measurable fun x : (Ω₀ × W) × (ι → T) => (x.1.2, x.2 i) :=
      (measurable_snd.comp measurable_fst).prodMk ((measurable_pi_apply i).comp measurable_snd)
    have h := (hS_m ϑ).comp hp
    exact h
  have hprod {ι : Type uR} (e : R → ι) (U : Finset R) (p : Ω₀ × W) (a : ι → T) :
      |∏ r ∈ U, ψ r (S ϑ p.2 (a (e r)))| ≤ L ^ Fintype.card R := by
    rw [Finset.abs_prod]
    calc _ ≤ ∏ _r ∈ U, L := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hψb r _
      _ = L ^ U.card := Finset.prod_const _
      _ ≤ _ := pow_le_pow_right₀ hL (Finset.card_le_univ U)
  have hprod_m {ι : Type uR} (e : R → ι) (U : Finset R) :
      Measurable fun x : (Ω₀ × W) × (ι → T) => ∏ r ∈ U, ψ r (S ϑ x.1.2 (x.2 (e r))) := by
    refine Finset.measurable_prod _ fun r _ => ?_
    have h := (hψm r).comp (hfield (e r))
    exact h
  have hthree (a b g : ℝ) (ha : |a| ≤ L) (hb : |b| ≤ L)
      (hg : |g| ≤ L ^ Fintype.card R) : |a * b * g| ≤ K := by
    rw [abs_mul, abs_mul]
    calc _ ≤ L * L * L ^ Fintype.card R :=
          mul_le_mul (mul_le_mul ha hb (abs_nonneg _) (zero_le_one.trans hL)) hg
            (abs_nonneg _) (mul_nonneg (zero_le_one.trans hL) (zero_le_one.trans hL))
      _ = K := by dsimp only [K]; rw [pow_add, pow_two]; ring
  let e₁ : R → Option R := some
  let e₂ : R → Option (Option R) := fun i => some (some i)
  have he₁ : Function.Injective e₁ := Option.some_injective _
  have he₂ : Function.Injective e₂ := (Option.some_injective _).comp he₁
  let G₀ (i j : R) (p : Ω₀ × W) (a : R → T) :=
    ψ_d i (S ϑ p.2 (a i)) * ψ_d j (S ϑ p.2 (a j)) *
      ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S ϑ p.2 (a r))
  let G₁ (i : R) (p : Ω₀ × W) (a : Option R → T) :=
    (ψ_d i (S ϑ p.2 (a (some i))) *
      ∏ r ∈ Finset.univ.erase i, ψ r (S ϑ p.2 (a (some r)))) *
      deriv u (S ϑ p.2 (a none))
  let G₂ (p : Ω₀ × W) (a : Option (Option R) → T) :=
    (∏ r, ψ r (S ϑ p.2 (a (some (some r))))) *
      deriv u (S ϑ p.2 (a (some none))) * deriv u (S ϑ p.2 (a none))
  have hm₀ (i j : R) : Measurable fun x : (Ω₀ × W) × (R → T) => G₀ i j x.1 x.2 := by
    have hi := (hψdm i).comp (hfield i)
    have hj := (hψdm j).comp (hfield j)
    exact (hi.mul hj).mul (hprod_m id _)
  have hm₁ (i : R) : Measurable fun x : (Ω₀ × W) × (Option R → T) => G₁ i x.1 x.2 := by
    have hi := (hψdm i).comp (hfield (some i))
    have hnew := (measurable_deriv u).comp (hfield (none : Option R))
    exact (hi.mul (hprod_m e₁ _)).mul hnew
  have hm₂ : Measurable fun x : (Ω₀ × W) × (Option (Option R) → T) => G₂ x.1 x.2 := by
    have hi := (measurable_deriv u).comp (hfield (some (none : Option R)))
    have hj := (measurable_deriv u).comp (hfield (none : Option (Option R)))
    exact ((hprod_m e₂ Finset.univ).mul hi).mul hj
  have hb₀ (i j : R) (p : Ω₀ × W) (a : R → T) : |G₀ i j p a| ≤ K :=
    hthree _ _ _ (hψdb _ _) (hψdb _ _) (hprod id _ p a)
  have hb₁ (i : R) (p : Ω₀ × W) (a : Option R → T) : |G₁ i p a| ≤ K := by
    dsimp only [G₁]; rw [mul_right_comm]
    exact hthree _ _ _ (hψdb _ _) (hbDu _) (hprod e₁ _ p a)
  have hb₂ (p : Ω₀ × W) (a : Option (Option R) → T) : |G₂ p a| ≤ K := by
    let g := ∏ r, ψ r (S ϑ p.2 (a (some (some r))))
    let b := deriv u (S ϑ p.2 (a (some none)))
    let c' := deriv u (S ϑ p.2 (a none))
    change |g * b * c'| ≤ K
    rw [show g * b * c' = b * c' * g by ring]
    exact hthree _ _ _ (hbDu _) (hbDu _) (hprod e₂ Finset.univ p a)
  let J₀ (i j : R) (ω : Ω₀) :=
    ∫ w, ∫ a : R → T, F (ω, w) a * c (a i) (a j) * G₀ i j (ω, w) a
      ∂(Measure.pi fun _ : R => ν (ω, w)) ∂γ_sh
  let J₁ (i : R) (ω : Ω₀) :=
    ∫ w, ∫ a : Option R → T, F (ω, w) (a ∘ e₁) * c (a (some i)) (a none) * G₁ i (ω, w) a
      ∂(Measure.pi fun _ : Option R => ν (ω, w)) ∂γ_sh
  let J₁' (i : R) (ω : Ω₀) :=
    ∫ w, ∫ a : Option R → T, F (ω, w) (a ∘ e₁) * c (a none) (a (some i)) * G₁ i (ω, w) a
      ∂(Measure.pi fun _ : Option R => ν (ω, w)) ∂γ_sh
  let J₂ (ω : Ω₀) :=
    ∫ w, ∫ a : Option (Option R) → T,
      F (ω, w) (a ∘ e₂) * c (a (some none)) (a none) * G₂ (ω, w) a
      ∂(Measure.pi fun _ : Option (Option R) => ν (ω, w)) ∂γ_sh
  have hj₀ (i j : R) (h : i ≠ j) :
      Integrable (J₀ i j) P₀ ∧ |∫ ω, J₀ i j ω ∂P₀| ≤ K * (m + ε * A₁) :=
    hTerm id Function.injective_id i j h (G₀ i j) (hm₀ i j) (hb₀ i j)
  have hj₁ (i : R) : Integrable (J₁ i) P₀ ∧ |∫ ω, J₁ i ω ∂P₀| ≤ K * (m + ε * A₁) :=
    hTerm e₁ he₁ (some i) none (by simp) (G₁ i) (hm₁ i) (hb₁ i)
  have hj₁' (i : R) : Integrable (J₁' i) P₀ ∧ |∫ ω, J₁' i ω ∂P₀| ≤ K * (m + ε * A₁) :=
    hTerm e₁ he₁ none (some i) (by simp) (G₁ i) (hm₁ i) (hb₁ i)
  have hj₂ : Integrable J₂ P₀ ∧ |∫ ω, J₂ ω ∂P₀| ≤ K * (m + ε * A₁) :=
    hTerm e₂ he₂ (some none) none (by simp) G₂ hm₂ hb₂
  have hcomb := abs_integral_replica_groups_le P₀ J₀ J₁ J₁' J₂
    (fun i j h => (hj₀ i j h).1) (fun i => (hj₁ i).1) (fun i => (hj₁' i).1) hj₂.1
    (mul_nonneg hK (add_nonneg hm (mul_nonneg hε hA₁)))
    (fun i j h => (hj₀ i j h).2) (fun i => (hj₁ i).2) (fun i => (hj₁' i).2) hj₂.2
  have hGm (ϑ' : ℝ) : AEStronglyMeasurable
      (fun ω => ∫ w, ∫ σ : R → T, f ω (fun r => (σ r).1) * ∏ r, ψ r (S ϑ' w (σ r))
        ∂(Measure.pi fun _ : R => ((μ₀ ω).prod γ_aux).tilted (fun x => u (S ϑ' w x))) ∂γ_sh)
      P₀ := by
    let V_obs (p : Ω₀ × W) (x : T) : ℝ := u (S ϑ' p.2 x)
    let F_obs (p : Ω₀ × W) (σ : R → T) : ℝ :=
      f p.1 (fun r => (σ r).1) * ∏ r, ψ r (S ϑ' p.2 (σ r))
    have hpV : Measurable fun p : (Ω₀ × W) × T => (p.1.2, p.2) :=
      (measurable_snd.comp measurable_fst).prodMk measurable_snd
    have hsV := (hS_m ϑ').comp hpV
    have hVm : Measurable fun p : (Ω₀ × W) × T => V_obs p.1 p.2 := hu.measurable.comp hsV
    have hpr : Measurable fun p : (Ω₀ × W) × (R → T) => ∏ r, ψ r (S ϑ' p.1.2 (p.2 r)) := by
      refine Finset.measurable_prod _ fun r _ => ?_
      have hpr_r : Measurable fun p : (Ω₀ × W) × (R → T) => (p.1.2, p.2 r) :=
        (measurable_snd.comp measurable_fst).prodMk ((measurable_pi_apply r).comp measurable_snd)
      have hsr := (hS_m ϑ').comp hpr_r
      exact (hψm r).comp hsr
    have hFm : Measurable fun p : (Ω₀ × W) × (R → T) => F_obs p.1 p.2 := (hfm id).mul hpr
    have hm_int := measurable_integral_pi_tilted_prod_tilted μ_base γ_aux hE₀ hE₀i hVm hFm
    exact (hm_int.stronglyMeasurable.integral_prod_right' (ν := γ_sh)).aestronglyMeasurable
  have hvar_eq (m : PerceptronSpin N) :
      X_sh m ⬝ᵥ X_sh m + (fun _ : PerceptronSpin N => X_aux) m ⬝ᵥ
        (fun _ : PerceptronSpin N => X_aux) m =
      (fun _ : PerceptronSpin N => Y_sh) m ⬝ᵥ (fun _ : PerceptronSpin N => Y_sh) m +
        (fun _ : PerceptronSpin N => Y_aux) m ⬝ᵥ (fun _ : PerceptronSpin N => Y_aux) m :=
    (hvar_X m).trans hvar_Y.symm
  have hdRot := hasDerivAt_integral_integral_gaussian_tilted_rotation_ibp
    (Ω₀ := Ω₀) (α := α) (L := PerceptronSpin N)
    (K_sh := (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit)) (K_aux := (Fin 2 ⊕ Unit)) (R := R)
    P₀ μ₀ π hπ X_sh (fun _ => Y_sh) (fun _ => X_aux) (fun _ => Y_aux)
    (fun m _ => horth_sh m) (fun _ _ => horth_aux) hvar_eq
    hu.differentiable hu.differentiable_deriv hu.abs_le hu.abs_deriv_le hu.abs_deriv₂_le
    ψ hψd hψ₂d (M₀ := fun _ => M₀) (M₁ := fun _ => M₁) (M₂ := fun _ => M₂) hM₀ hM₁ hM₂
    (ae_of_all _ hfi) hfi₁ hGm ϑ
  have hbound := hcomb.trans_eq
    (show n ^ 2 * (K * (m + ε * A₁)) + n ^ 2 * (K * (m + ε * A₁)) +
      n ^ 2 * (K * (m + ε * A₁)) + n * (n + 1) * (K * (m + ε * A₁)) =
        (4 * n ^ 2 + n) * K * (m + ε * A₁) by ring)
  refine ⟨_, hdRot, ?_⟩
  have hrhs_eq : (4 * n ^ 2 + n) * K * (m + ε * A₁) =
      (4 * n ^ 2 + n) * L ^ (Fintype.card R + 2) *
        (m + 1 / (N + 1) *
          ∫ p, ∫ a, |F p a| ∂(Measure.pi fun _ : R => ν p) ∂(P₀.prod γ_sh)) := rfl
  rw [← hrhs_eq]
  have hJ₁_eq (i : R) (ω : Ω₀) :
      (∫ w, ∫ σ : Option R → T,
          (f ω fun r => (σ (some r)).1) * C_cov (π (σ (some i)).1) (π (σ none).1) *
            (ψ_d i (S ϑ w (σ (some i))) *
              ∏ r ∈ Finset.univ.erase i, ψ r (S ϑ w (σ (some r)))) *
            deriv u (S ϑ w (σ none))
          ∂(Measure.pi fun _ : Option R => ν (ω, w)) ∂γ_sh) = J₁ i ω :=
    integral_congr_ae (ae_of_all _ fun w => integral_congr_ae (ae_of_all _ fun σ => by
      dsimp only [F, c, G₁, e₁, Function.comp_apply]; ring))
  have hJ₁'_eq (j : R) (ω : Ω₀) :
      (∫ w, ∫ σ : Option R → T,
          (f ω fun r => (σ (some r)).1) * C_cov (π (σ none).1) (π (σ (some j)).1) *
            (ψ_d j (S ϑ w (σ (some j))) *
              ∏ r ∈ Finset.univ.erase j, ψ r (S ϑ w (σ (some r)))) *
            deriv u (S ϑ w (σ none))
          ∂(Measure.pi fun _ : Option R => ν (ω, w)) ∂γ_sh) = J₁' j ω :=
    integral_congr_ae (ae_of_all _ fun w => integral_congr_ae (ae_of_all _ fun σ => by
      dsimp only [F, c, G₁, e₁, Function.comp_apply]; ring))
  have hJ₂_eq (ω : Ω₀) :
      (∫ w, ∫ σ : Option (Option R) → T,
          (f ω fun r => (σ (some (some r))).1) * C_cov (π (σ (some none)).1) (π (σ none).1) *
            (∏ r, ψ r (S ϑ w (σ (some (some r))))) *
            deriv u (S ϑ w (σ (some none))) * deriv u (S ϑ w (σ none))
          ∂(Measure.pi fun _ : Option (Option R) => ν (ω, w)) ∂γ_sh) = J₂ ω :=
    integral_congr_ae (ae_of_all _ fun w => integral_congr_ae (ae_of_all _ fun σ => by
      dsimp only [F, c, G₂, e₂, Function.comp_apply]; ring))
  refine le_of_eq_of_le (congrArg abs (integral_congr_ae (ae_of_all _ fun ω => ?_))) hbound
  exact congrArg₂ (· + ·)
    (congrArg₂ (· - ·)
      (congrArg₂ (· - ·) rfl
        (congrArg _ (Finset.sum_congr rfl fun i _ => hJ₁_eq i ω)))
      (congrArg _ (Finset.sum_congr rfl fun j _ => hJ₁'_eq j ω)))
    (congrArg _ (hJ₂_eq ω))

end RotationDerivative

section MasterComparison

/-- **Master endpoint comparison for the `s`-interpolating cavity constraint (`s, t, q ∈ [0, 1]`).**
Generalizes `abs_integral_smartPath_deriv_mul_sub_rhat_le_of_split_pair_bound` to an arbitrary
old-state system `(Ω₀, P₀, μ_base, E₀)` and arbitrary interpolation parameter `s ∈ [0, 1]`. -/
private lemma abs_integral_interp_deriv_mul_sub_rhat_le_of_pair_bound
    {N : ℕ} {Ω₀ : Type uΩ} {α : Type uα} {R : Type uR}
    [MeasurableSpace Ω₀] [MeasurableSpace α] [Fintype R]
    (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (μ_base : Measure α) [IsFiniteMeasure μ_base] [NeZero μ_base]
    {E₀ : Ω₀ → α → ℝ} (hE₀ : Measurable fun p : Ω₀ × α => E₀ p.1 p.2)
    (hE₀i : ∀ ω, Integrable (fun a => Real.exp (E₀ ω a)) μ_base)
    (π : α → PerceptronSpin N) (hπ : Measurable π)
    {r₁ r₂ : R} (hr : r₁ ≠ r₂)
    {s t q : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1)
    {u : ℝ → ℝ} {D : ℝ}
    (hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
    (hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
    {f : Ω₀ → (R → α) → ℝ} (hf : Measurable fun p : Ω₀ × (R → α) => f p.1 p.2)
    {M_f : ℝ} (hfb : ∀ ω a, |f ω a| ≤ M_f)
    {m : ℝ} (hm0 : 0 ≤ m) :
    let γ₁ := Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => gaussianReal 0 1
    let γ₂ := Measure.pi fun _ : Fin 2 => gaussianReal 0 1
    let γ_sh := Measure.pi fun _ : (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : (Fin 2 ⊕ Unit) => gaussianReal 0 1
    let μ₀ (ω : Ω₀) := μ_base.tilted (E₀ ω)
    let X_fn (w₁ : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ) (x : α × (Fin 2 → ℝ)) : ℝ :=
      Sum.elim (Real.sqrt s • cavityCoef N t (π x.1))
        (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ w₁ +
      ![Real.sqrt s * Real.sqrt ((1 - t) / (N + 1)),
        Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ x.2
    let X_sh : PerceptronSpin N → (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ :=
      fun σ => Sum.elim
        (Sum.elim (Real.sqrt s • cavityCoef N t σ) (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) 0
    let Y_sh : (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ := Sum.elim 0 (fun _ => Real.sqrt q)
    let X_aux : (Fin 2 ⊕ Unit) → ℝ :=
      Sum.elim ![Real.sqrt s * Real.sqrt ((1 - t) / (N + 1)),
        Real.sqrt (1 - s) * Real.sqrt (1 - q)] 0
    let Y_aux : (Fin 2 ⊕ Unit) → ℝ := Sum.elim 0 (fun _ => Real.sqrt (1 - q))
    let S (ϑ : ℝ) (w : (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)
        (x : α × ((Fin 2 ⊕ Unit) → ℝ)) : ℝ :=
      Real.cos ϑ * (X_sh (π x.1) ⬝ᵥ w + X_aux ⬝ᵥ x.2) +
        Real.sin ϑ * (Y_sh ⬝ᵥ w + Y_aux ⬝ᵥ x.2)
    let ν_rot (ϑ : ℝ) (p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) :=
      ((μ₀ p.1).prod γ_aux).tilted fun x => u (S ϑ p.2 x)
    let ν_new (p : Ω₀ × (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) :=
      ((μ₀ p.1).prod γ₂).tilted fun x => u (X_fn p.2 x)
    let d_spin (σ τ : PerceptronSpin N) : ℝ :=
      |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
        ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
    let rhat := perceptronRhat u q
    let n : ℝ := Fintype.card R
    let M₀w : ℝ := 1 + |D|
    let M₁w : ℝ := |D|
    let L_u : ℝ := 1 + |D| + |(1 : ℝ)| + |(0 : ℝ)| + |(1 : ℝ)| * |D|
    let L_w : ℝ := 1 + |D| + |M₀w| + |M₁w| + |M₀w| * |D|
    let K_u : ℝ := (4 * n ^ 2 + n) * L_u ^ (Fintype.card R + 2)
    let K_w : ℝ := (4 * n ^ 2 + n) * L_w ^ (Fintype.card R + 2)
    (∀ (ϑ : ℝ) (ι : Type uR) [Fintype ι] (e : R → ι), Function.Injective e → ∀ i j, i ≠ j →
      ∫ p, ∫ a : ι → α × ((Fin 2 ⊕ Unit) → ℝ),
        |f p.1 (fun r => (a (e r)).1)| * d_spin (π (a i).1) (π (a j).1)
        ∂(Measure.pi fun _ : ι => ν_rot ϑ p) ∂(P₀.prod γ_sh) ≤ m) →
    |(∫ p, ∫ a : R → α × (Fin 2 → ℝ),
        f p.1 (fun r => (a r).1) * (deriv u (X_fn p.2 (a r₁)) * deriv u (X_fn p.2 (a r₂)))
        ∂(Measure.pi fun _ : R => ν_new p) ∂(P₀.prod γ₁)) -
      rhat * (∫ p, ∫ a : R → α × (Fin 2 → ℝ),
        f p.1 (fun r => (a r).1)
        ∂(Measure.pi fun _ : R => ν_new p) ∂(P₀.prod γ₁))| ≤
      (K_w / 2 + |D| ^ 2 * (K_u / 2)) *
        (m + 1 / (N + 1) * Real.exp (4 * n * |D|) *
          ∫ p, ∫ a : R → α × (Fin 2 → ℝ),
            |f p.1 (fun r => (a r).1)| ∂(Measure.pi fun _ : R => ν_new p) ∂(P₀.prod γ₁)) := by
  classical
  intro γ₁ γ₂ γ_sh γ_aux μ₀ X_fn X_sh Y_sh X_aux Y_aux S ν_rot ν_new d_spin rhat
    n M₀w M₁w L_u L_w K_u K_w hpair
  obtain ⟨hu, h2d, hb3⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hD_abs : ∀ x, |u x| ≤ |D| := fun x => (hu.abs_le x).trans (le_abs_self D)
  let f_abs (ω : Ω₀) (a : R → α) : ℝ := |f ω a|
  have hf_abs_m : Measurable fun p : Ω₀ × (R → α) => f_abs p.1 p.2 := by
    simpa only [f_abs, Real.norm_eq_abs] using hf.norm
  have hXm : Measurable fun p : (((Fin N ⊕ Unit) ⊕ Unit) → ℝ) × (α × (Fin 2 → ℝ)) =>
      X_fn p.1 p.2 := by
    have hX1 (j : (Fin N ⊕ Unit) ⊕ Unit) :
        Measurable fun p : (((Fin N ⊕ Unit) ⊕ Unit) → ℝ) × (α × (Fin 2 → ℝ)) =>
          (Sum.elim (Real.sqrt s • cavityCoef N t (π p.2.1))
            (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) j :=
      (measurable_of_finite fun σ =>
        (Sum.elim (Real.sqrt s • cavityCoef N t σ)
          (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) j).comp
        (hπ.comp (measurable_fst.comp measurable_snd))
    have hd1 : Measurable fun p : (((Fin N ⊕ Unit) ⊕ Unit) → ℝ) × (α × (Fin 2 → ℝ)) =>
        Sum.elim (Real.sqrt s • cavityCoef N t (π p.2.1))
          (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ p.1 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ =>
        (hX1 j).mul ((measurable_pi_apply j).comp measurable_fst)
    have hd2 : Measurable fun p : (((Fin N ⊕ Unit) ⊕ Unit) → ℝ) × (α × (Fin 2 → ℝ)) =>
        ![Real.sqrt s * Real.sqrt ((1 - t) / (N + 1)),
          Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ p.2.2 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))
    exact hd1.add hd2
  have hS0 (w : (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ) (x : α × ((Fin 2 ⊕ Unit) → ℝ)) :
      S 0 w x = X_fn (w ∘ Sum.inl) (x.1, x.2 ∘ Sum.inl) := by
    simp [S, X_sh, X_aux, X_fn, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  have hSpi (w : (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ) (x : α × ((Fin 2 ⊕ Unit) → ℝ)) :
      S (Real.pi / 2) w x =
        Real.sqrt q * w (Sum.inr ()) + Real.sqrt (1 - q) * x.2 (Sum.inr ()) := by
    simp [S, Y_sh, Y_aux, Real.cos_pi_div_two, Real.sin_pi_div_two, dotProduct,
      Fintype.sum_sum_type]
  let I₁ : ℝ := ∫ p, ∫ a : R → α × (Fin 2 → ℝ),
    |f p.1 (fun r => (a r).1)| ∂(Measure.pi fun _ : R => ν_new p) ∂(P₀.prod γ₁)
  have hI₁_0 : 0 ≤ I₁ := integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _
  have hm1_0 : ∫ p, ∫ a : R → α × ((Fin 2 ⊕ Unit) → ℝ),
      |f p.1 (fun r => (a r).1)| ∂(Measure.pi fun _ : R => ν_rot 0 p) ∂(P₀.prod γ_sh) = I₁ := by
    have h0 := rotation_endpoint_zero_eq P₀ μ_base hE₀ hE₀i hu.measurable hD_abs X_fn hXm
      (fun _ _ => 1) (fun _ => measurable_const) (M₀ := 1) (fun _ _ => by simp)
      hf_abs_m (M_f := |M_f|) (fun ω a => by
        dsimp only [f_abs]; rw [abs_abs]; exact (hfb ω a).trans (le_abs_self _))
    dsimp only [f_abs] at h0
    simp only [Finset.prod_const_one, mul_one] at h0
    let V_obs0 (p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ))
        (x : α × ((Fin 2 ⊕ Unit) → ℝ)) : ℝ := u (S 0 p.2 x)
    have hVm : Measurable fun p : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) ×
        (α × ((Fin 2 ⊕ Unit) → ℝ)) => V_obs0 p.1 p.2 := by
      have hp : Measurable fun p : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) ×
          (α × ((Fin 2 ⊕ Unit) → ℝ)) => (p.1.2, p.2) :=
        (measurable_snd.comp measurable_fst).prodMk measurable_snd
      have hs0 := (measurable_interp_rotation_field hπ s t q 0).comp hp
      exact hu.measurable.comp hs0
    let G_abs (p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ))
        (a : R → α × ((Fin 2 ⊕ Unit) → ℝ)) : ℝ := |f p.1 (fun r => (a r).1)|
    have hGm : Measurable fun q : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) ×
        (R → α × ((Fin 2 ⊕ Unit) → ℝ)) => G_abs q.1 q.2 := by
      have hp : Measurable fun q : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) ×
          (R → α × ((Fin 2 ⊕ Unit) → ℝ)) => (q.1.1, fun r => (q.2 r).1) :=
        (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun r =>
          measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
      exact hf_abs_m.comp hp
    have hIm := measurable_integral_pi_tilted_prod_tilted μ_base γ_aux hE₀ hE₀i hVm hGm
    have hμ₀ (ω : Ω₀) : IsProbabilityMeasure (μ₀ ω) := isProbabilityMeasure_tilted (hE₀i ω)
    have hIi : Integrable (fun p => ∫ a : R → α × ((Fin 2 ⊕ Unit) → ℝ),
        |f p.1 (fun r => (a r).1)| ∂(Measure.pi fun _ : R => ν_rot 0 p)) (P₀.prod γ_sh) := by
      refine Integrable.of_bound hIm.aestronglyMeasurable |M_f| (ae_of_all _ fun p => ?_)
      have hp0 : Measurable fun x : α × ((Fin 2 ⊕ Unit) → ℝ) => (p.2, x) :=
        measurable_const.prodMk measurable_id
      have hs0 := (measurable_interp_rotation_field hπ s t q 0).comp hp0
      have hVp : Measurable fun x : α × ((Fin 2 ⊕ Unit) → ℝ) => u (S 0 p.2 x) :=
        hu.measurable.comp hs0
      have : IsProbabilityMeasure (ν_rot 0 p) :=
        isProbabilityMeasure_tilted_of_ae_le hVp.aemeasurable
          (ae_of_all _ fun _ => le_of_abs_le (hD_abs _))
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
      exact (le_abs_self _).trans (abs_integral_le_of_forall_abs_le _ fun _ => by
        rw [abs_abs]; exact (hfb _ _).trans (le_abs_self _))
    rw [integral_prod (fun p => ∫ a : R → α × ((Fin 2 ⊕ Unit) → ℝ),
        |f p.1 (fun r => (a r).1)| ∂(Measure.pi fun _ : R => ν_rot 0 p)) hIi]
    refine (integral_congr_ae (ae_of_all _ fun ω =>
      integral_congr_ae (ae_of_all _ fun w => ?_))).trans h0
    dsimp only [ν_rot]
    simp_rw [hS0]; rfl
  have hm1_le (ϑ : ℝ) :
      ∫ p, ∫ a : R → α × ((Fin 2 ⊕ Unit) → ℝ),
        |f p.1 (fun r => (a r).1)| ∂(Measure.pi fun _ : R => ν_rot ϑ p) ∂(P₀.prod γ_sh) ≤
      Real.exp (4 * n * |D|) * I₁ := by
    let V_fn (ϑ' : ℝ) (w : (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)
        (x : α × ((Fin 2 ⊕ Unit) → ℝ)) : ℝ := u (S ϑ' w x)
    have hVm (ϑ' : ℝ) : Measurable fun p : ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ) ×
        (α × ((Fin 2 ⊕ Unit) → ℝ)) => V_fn ϑ' p.1 p.2 := by
      have hs_m := measurable_interp_rotation_field hπ s t q ϑ'
      exact hu.measurable.comp hs_m
    have hdom := integral_pi_tilted_prod_nonneg_le_exp_mul P₀ μ_base γ_sh γ_aux hE₀ hE₀i
      (hVm ϑ) (hVm 0) (fun _ _ => hD_abs _) (fun _ _ => hD_abs _) hf_abs_m
      (fun _ _ => abs_nonneg _) (M_g := |M_f|) (fun ω a => (hfb ω a).trans (le_abs_self _))
    rw [hm1_0] at hdom
    exact hdom
  let B_err : ℝ := m + 1 / (N + 1) * Real.exp (4 * n * |D|) * I₁
  let φ_u (ϑ : ℝ) : ℝ :=
    ∫ ω, ∫ w, ∫ σ : R → α × ((Fin 2 ⊕ Unit) → ℝ),
      f ω (fun r => (σ r).1)
      ∂(Measure.pi fun _ : R => ((μ₀ ω).prod γ_aux).tilted (fun x => u (S ϑ w x)))
      ∂γ_sh ∂P₀
  have hd_u (ϑ : ℝ) : ∃ z, HasDerivAt φ_u (Real.sin ϑ * Real.cos ϑ * z) ϑ ∧
      |z| ≤ K_u * B_err := by
    obtain ⟨z, hz, hzb⟩ := exists_hasDerivAt_interp_rotation_abs_le_of_pair_bound
      P₀ μ_base hE₀ hE₀i π hπ hs ht hq hu
      (fun _ _ => 1) (fun _ => differentiable_const 1) (fun _ => by simp)
      (M₀ := 1) (M₁ := 0) (M₂ := 0)
      (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp)
      hf hfb ϑ hm0 (hpair ϑ)
    have heq_φ : (fun ϑ' => ∫ ω, ∫ w, ∫ σ : R → α × ((Fin 2 ⊕ Unit) → ℝ),
        f ω (fun r => (σ r).1) * ∏ _r : R, (1 : ℝ)
        ∂(Measure.pi fun _ : R => ((μ₀ ω).prod γ_aux).tilted (fun x => u (S ϑ' w x)))
        ∂γ_sh ∂P₀) = φ_u := by
      funext ϑ'; simp [φ_u]
    rw [heq_φ] at hz
    refine ⟨z, hz, hzb.trans ?_⟩
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
    calc 1 / (N + 1 : ℝ) * _ ≤ 1 / (N + 1 : ℝ) * (Real.exp (4 * n * |D|) * I₁) :=
          mul_le_mul_of_nonneg_left (hm1_le ϑ) (by positivity)
      _ = 1 / (N + 1 : ℝ) * Real.exp (4 * n * |D|) * I₁ := by ring
  let ψ_w (r : R) (x : ℝ) : ℝ := if r = r₁ ∨ r = r₂ then deriv u x else 1
  obtain ⟨hψd, hψ2d, hM₀w, hM₁w, hM₂w⟩ :=
    differentiable_and_abs_deriv_le_ite_one (p := fun i : R => i = r₁ ∨ i = r₂)
      (B₀ := M₀w) (B₁ := M₁w) (B₂ := |D|) hu.differentiable_deriv h2d
      (fun x => by dsimp [M₀w]; linarith [hu.abs_deriv_le x, le_abs_self D])
      (fun x => (hu.abs_deriv₂_le x).trans (le_abs_self D))
      (fun x => (hb3 x).trans (le_abs_self D))
      (by dsimp [M₀w]; linarith only [abs_nonneg D]) (abs_nonneg _) (abs_nonneg _)
  let φ_w (ϑ : ℝ) : ℝ :=
    ∫ ω, ∫ w, ∫ σ : R → α × ((Fin 2 ⊕ Unit) → ℝ),
      f ω (fun r => (σ r).1) * ∏ r, ψ_w r (S ϑ w (σ r))
      ∂(Measure.pi fun _ : R => ((μ₀ ω).prod γ_aux).tilted (fun x => u (S ϑ w x)))
      ∂γ_sh ∂P₀
  have hd_w (ϑ : ℝ) : ∃ z, HasDerivAt φ_w (Real.sin ϑ * Real.cos ϑ * z) ϑ ∧
      |z| ≤ K_w * B_err := by
    obtain ⟨z, hz, hzb⟩ := exists_hasDerivAt_interp_rotation_abs_le_of_pair_bound
      P₀ μ_base hE₀ hE₀i π hπ hs ht hq hu
      ψ_w hψd hψ2d hM₀w hM₁w hM₂w
      hf hfb ϑ hm0 (hpair ϑ)
    refine ⟨z, hz, hzb.trans ?_⟩
    refine mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) (by positivity)
    calc 1 / (N + 1 : ℝ) * _ ≤ 1 / (N + 1 : ℝ) * (Real.exp (4 * n * |D|) * I₁) :=
          mul_le_mul_of_nonneg_left (hm1_le ϑ) (by positivity)
      _ = 1 / (N + 1 : ℝ) * Real.exp (4 * n * |D|) * I₁ := by ring
  have hprod_w (x : R → ℝ) :
      (∏ r : R, ψ_w r (x r)) = deriv u (x r₁) * deriv u (x r₂) := by
    simpa only [ψ_w, apply_ite, Finset.mem_insert, Finset.mem_singleton, Finset.prod_pair hr] using
      (Fintype.prod_ite_mem ({r₁, r₂} : Finset R) (fun r => deriv u (x r)))
  have hφ_u_0 : φ_u 0 = ∫ p, ∫ a : R → α × (Fin 2 → ℝ),
      f p.1 (fun r => (a r).1) ∂(Measure.pi fun _ : R => ν_new p) ∂(P₀.prod γ₁) := by
    have h0 := rotation_endpoint_zero_eq P₀ μ_base hE₀ hE₀i hu.measurable hD_abs X_fn hXm
      (fun _ _ => 1) (fun _ => measurable_const) (M₀ := 1) (fun _ _ => by simp) hf hfb
    dsimp only at h0
    simp only [Finset.prod_const_one, mul_one] at h0
    dsimp only [φ_u]
    refine (integral_congr_ae (ae_of_all _ fun ω =>
      integral_congr_ae (ae_of_all _ fun w => ?_))).trans h0
    simp_rw [hS0]; rfl
  have hφ_w_0 : φ_w 0 = ∫ p, ∫ a : R → α × (Fin 2 → ℝ),
      f p.1 (fun r => (a r).1) * (deriv u (X_fn p.2 (a r₁)) * deriv u (X_fn p.2 (a r₂)))
      ∂(Measure.pi fun _ : R => ν_new p) ∂(P₀.prod γ₁) := by
    have h0 := rotation_endpoint_zero_eq P₀ μ_base hE₀ hE₀i hu.measurable hD_abs X_fn hXm
      ψ_w (fun r => (hψd r).continuous.measurable) hM₀w hf hfb
    dsimp only at h0
    dsimp only [φ_w]
    have hl : (∫ ω, ∫ w, ∫ σ : R → α × ((Fin 2 ⊕ Unit) → ℝ),
        f ω (fun r => (σ r).1) * ∏ r, ψ_w r (S 0 w (σ r))
        ∂(Measure.pi fun _ : R => ((μ₀ ω).prod γ_aux).tilted (fun x => u (S 0 w x)))
        ∂γ_sh ∂P₀) =
      ∫ ω, ∫ w, ∫ σ : R → α × ((Fin 2 ⊕ Unit) → ℝ),
        f ω (fun r => (σ r).1) *
          ∏ r, ψ_w r (X_fn (w ∘ Sum.inl) ((σ r).1, (σ r).2 ∘ Sum.inl))
        ∂(Measure.pi fun _ : R => ((μ₀ ω).prod γ_aux).tilted
          (fun x => u (X_fn (w ∘ Sum.inl) (x.1, x.2 ∘ Sum.inl))))
        ∂γ_sh ∂P₀ :=
      integral_congr_ae (ae_of_all _ fun _ => integral_congr_ae (ae_of_all _ fun _ => by
        simp_rw [hS0]))
    rw [hl, h0]
    exact integral_congr_ae (ae_of_all _ fun _ => integral_congr_ae (ae_of_all _ fun a => by
      dsimp only; rw [hprod_w]))
  have hpi := rotation_endpoint_pi_div_two_eq (K₁ := (Fin N ⊕ Unit) ⊕ Unit) (K₂ := Fin 2)
    P₀ μ_base hE₀i hu.measurable hD_abs q f
  dsimp only at hpi
  have hφ_u_pi : φ_u (Real.pi / 2) =
      ∫ ω, ∫ a : R → α, f ω a ∂(Measure.pi fun _ : R => μ₀ ω) ∂P₀ := by
    dsimp only [φ_u]
    refine (integral_congr_ae (ae_of_all _ fun _ =>
      integral_congr_ae (ae_of_all _ fun _ => ?_))).trans hpi.1
    simp_rw [hSpi]; rfl
  have hφ_w_pi : φ_w (Real.pi / 2) = rhat * φ_u (Real.pi / 2) := by
    dsimp only [φ_w]
    have hl : (∫ ω, ∫ w, ∫ σ : R → α × ((Fin 2 ⊕ Unit) → ℝ),
        f ω (fun r => (σ r).1) * ∏ r, ψ_w r (S (Real.pi / 2) w (σ r))
        ∂(Measure.pi fun _ : R => ((μ₀ ω).prod γ_aux).tilted (fun x => u (S (Real.pi / 2) w x)))
        ∂γ_sh ∂P₀) =
      ∫ ω, ∫ w, ∫ σ : R → α × ((Fin 2 ⊕ Unit) → ℝ),
        f ω (fun r => (σ r).1) *
          (deriv u (Real.sqrt q * w (Sum.inr ()) + Real.sqrt (1 - q) * (σ r₁).2 (Sum.inr ())) *
            deriv u (Real.sqrt q * w (Sum.inr ()) + Real.sqrt (1 - q) * (σ r₂).2 (Sum.inr ())))
        ∂(Measure.pi fun _ : R => ((μ₀ ω).prod γ_aux).tilted
          (fun x => u (Real.sqrt q * w (Sum.inr ()) + Real.sqrt (1 - q) * x.2 (Sum.inr ()))))
        ∂γ_sh ∂P₀ :=
      integral_congr_ae (ae_of_all _ fun _ => integral_congr_ae (ae_of_all _ fun w => by
        simp_rw [hSpi]
        exact integral_congr_ae (ae_of_all _ fun σ => congrArg (_ * ·)
          (hprod_w fun r =>
            Real.sqrt q * w (Sum.inr ()) + Real.sqrt (1 - q) * (σ r).2 (Sum.inr ())))))
    rw [hl, hφ_u_pi]
    exact hpi.2 hr
  have hrhat_b := rhat_mem_Icc (u := u) (D' := |D|)
    (fun x => (hu.abs_deriv_le x).trans (le_abs_self D)) q
    (fun z => integrable_exp_cavityPath_new hu.measurable (fun x => hu.le x) q z)
  rw [← hφ_w_0, ← hφ_u_0]
  calc |φ_w 0 - rhat * φ_u 0| ≤ K_w * B_err / 2 + |D| ^ 2 * (K_u * B_err / 2) :=
        Real.abs_sub_mul_le_half_of_exists_hasDerivAt hφ_w_pi (by rwa [abs_of_nonneg hrhat_b.1])
          (fun s => let ⟨d, hd, hb⟩ := hd_w s; ⟨d, hd, fun _ => hb⟩)
          (fun s => let ⟨d, hd, hb⟩ := hd_u s; ⟨d, hd, fun _ => hb⟩)
    _ = (K_w / 2 + |D| ^ 2 * (K_u / 2)) * B_err := by ring

/-- **Proposition 2.3.5 for the `s`-interpolating constraint field, `(1, ∞)` endpoint.** -/
theorem abs_integral_interp_deriv_mul_sub_rhat_le_first_moment
    (R : Type uR) [Fintype R] (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N : ℕ) {Ω₀ : Type uΩ} {α : Type uα}
        [MeasurableSpace Ω₀] [MeasurableSpace α]
        (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
        (μ_base : Measure α) [IsFiniteMeasure μ_base] [NeZero μ_base]
        {E₀ : Ω₀ → α → ℝ} (_hE₀ : Measurable fun p : Ω₀ × α => E₀ p.1 p.2)
        (_hE₀i : ∀ ω, Integrable (fun a => Real.exp (E₀ ω a)) μ_base)
        (π : α → PerceptronSpin N) (_hπ : Measurable π)
        {r₁ r₂ : R} (_hr : r₁ ≠ r₂)
        {s t q : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1) (_ht : t ∈ Icc (0 : ℝ) 1) (_hq : q ∈ Icc (0 : ℝ) 1)
        {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        {f : Ω₀ → (R → α) → ℝ} (_hf : Measurable fun p : Ω₀ × (R → α) => f p.1 p.2)
        {M_f : ℝ} (_hfb : ∀ ω a, |f ω a| ≤ M_f),
        let γ₁ := Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => gaussianReal 0 1
        let γ₂ := Measure.pi fun _ : Fin 2 => gaussianReal 0 1
        let μ₀ (ω : Ω₀) := μ_base.tilted (E₀ ω)
        let X_fn (w₁ : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ) (x : α × (Fin 2 → ℝ)) : ℝ :=
          Sum.elim (Real.sqrt s • cavityCoef N t (π x.1))
            (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ w₁ +
          ![Real.sqrt s * Real.sqrt ((1 - t) / (N + 1)),
            Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ x.2
        let ν_new (p : Ω₀ × (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) :=
          ((μ₀ p.1).prod γ₂).tilted fun x => u (X_fn p.2 x)
        let rhat := perceptronRhat u q
        |(∫ p, ∫ a : R → α × (Fin 2 → ℝ),
            f p.1 (fun r => (a r).1) * (deriv u (X_fn p.2 (a r₁)) * deriv u (X_fn p.2 (a r₂)))
            ∂(Measure.pi fun _ : R => ν_new p) ∂(P₀.prod γ₁)) -
          rhat * (∫ p, ∫ a : R → α × (Fin 2 → ℝ),
            f p.1 (fun r => (a r).1)
            ∂(Measure.pi fun _ : R => ν_new p) ∂(P₀.prod γ₁))| ≤
          K * ((2 + 1 / (N + 1)) *
            ∫ p, ∫ a : R → α × (Fin 2 → ℝ),
              |f p.1 (fun r => (a r).1)| ∂(Measure.pi fun _ : R => ν_new p) ∂(P₀.prod γ₁)) := by
  let n : ℝ := Fintype.card R
  let M₀w : ℝ := 1 + |D|
  let M₁w : ℝ := |D|
  let L_u : ℝ := 1 + |D| + |(1 : ℝ)| + |(0 : ℝ)| + |(1 : ℝ)| * |D|
  let L_w : ℝ := 1 + |D| + |M₀w| + |M₁w| + |M₀w| * |D|
  let K_u : ℝ := (4 * n ^ 2 + n) * L_u ^ (Fintype.card R + 2)
  let K_w : ℝ := (4 * n ^ 2 + n) * L_w ^ (Fintype.card R + 2)
  let K : ℝ := (K_w / 2 + |D| ^ 2 * (K_u / 2)) * Real.exp (4 * n * |D|)
  refine ⟨K, by positivity, ?_⟩
  intro N Ω₀ α _ _ P₀ _ μ_base _ _ E₀ hE₀ hE₀i π hπ r₁ r₂ hr s t q hs ht hq u hd hb f hf M_f hfb
    γ₁ γ₂ μ₀ X_fn ν_new rhat
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hD_abs : ∀ x, |u x| ≤ |D| := fun x => (hu.abs_le x).trans (le_abs_self D)
  let f_abs (ω : Ω₀) (a : R → α) : ℝ := |f ω a|
  have hf_abs_m : Measurable fun p : Ω₀ × (R → α) => f_abs p.1 p.2 := by
    simpa only [f_abs, Real.norm_eq_abs] using hf.norm
  have hXm : Measurable fun p : (((Fin N ⊕ Unit) ⊕ Unit) → ℝ) × (α × (Fin 2 → ℝ)) =>
      X_fn p.1 p.2 := by
    have hX1 (j : (Fin N ⊕ Unit) ⊕ Unit) :
        Measurable fun p : (((Fin N ⊕ Unit) ⊕ Unit) → ℝ) × (α × (Fin 2 → ℝ)) =>
          (Sum.elim (Real.sqrt s • cavityCoef N t (π p.2.1))
            (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) j :=
      (measurable_of_finite fun σ =>
        (Sum.elim (Real.sqrt s • cavityCoef N t σ)
          (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) j).comp
        (hπ.comp (measurable_fst.comp measurable_snd))
    have hd1 : Measurable fun p : (((Fin N ⊕ Unit) ⊕ Unit) → ℝ) × (α × (Fin 2 → ℝ)) =>
        Sum.elim (Real.sqrt s • cavityCoef N t (π p.2.1))
          (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ p.1 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ =>
        (hX1 j).mul ((measurable_pi_apply j).comp measurable_fst)
    have hd2 : Measurable fun p : (((Fin N ⊕ Unit) ⊕ Unit) → ℝ) × (α × (Fin 2 → ℝ)) =>
        ![Real.sqrt s * Real.sqrt ((1 - t) / (N + 1)),
          Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ p.2.2 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))
    exact hd1.add hd2
  let I₁ : ℝ := ∫ p, ∫ a : R → α × (Fin 2 → ℝ),
    |f p.1 (fun r => (a r).1)| ∂(Measure.pi fun _ : R => ν_new p) ∂(P₀.prod γ₁)
  have hI₁_0 : 0 ≤ I₁ := integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _
  let m : ℝ := 2 * Real.exp (4 * n * |D|) * I₁
  have hm0 : 0 ≤ m := by positivity
  let γ_sh := Measure.pi fun _ : (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) => gaussianReal 0 1
  let γ_aux := Measure.pi fun _ : (Fin 2 ⊕ Unit) => gaussianReal 0 1
  let X_sh : PerceptronSpin N → (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ :=
    fun σ => Sum.elim
      (Sum.elim (Real.sqrt s • cavityCoef N t σ) (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) 0
  let Y_sh : (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ := Sum.elim 0 (fun _ => Real.sqrt q)
  let X_aux : (Fin 2 ⊕ Unit) → ℝ :=
    Sum.elim ![Real.sqrt s * Real.sqrt ((1 - t) / (N + 1)),
      Real.sqrt (1 - s) * Real.sqrt (1 - q)] 0
  let Y_aux : (Fin 2 ⊕ Unit) → ℝ := Sum.elim 0 (fun _ => Real.sqrt (1 - q))
  let S (ϑ : ℝ) (w : (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)
      (x : α × ((Fin 2 ⊕ Unit) → ℝ)) : ℝ :=
    Real.cos ϑ * (X_sh (π x.1) ⬝ᵥ w + X_aux ⬝ᵥ x.2) +
      Real.sin ϑ * (Y_sh ⬝ᵥ w + Y_aux ⬝ᵥ x.2)
  let ν_rot (ϑ : ℝ) (p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) :=
    ((μ₀ p.1).prod γ_aux).tilted fun x => u (S ϑ p.2 x)
  have hS0 (w : (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ) (x : α × ((Fin 2 ⊕ Unit) → ℝ)) :
      S 0 w x = X_fn (w ∘ Sum.inl) (x.1, x.2 ∘ Sum.inl) := by
    simp [S, X_sh, X_aux, X_fn, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  have hm1_0 : ∫ p, ∫ a : R → α × ((Fin 2 ⊕ Unit) → ℝ),
      |f p.1 (fun r => (a r).1)| ∂(Measure.pi fun _ : R => ν_rot 0 p) ∂(P₀.prod γ_sh) = I₁ := by
    have h0 := rotation_endpoint_zero_eq P₀ μ_base hE₀ hE₀i hu.measurable hD_abs X_fn hXm
      (fun _ _ => 1) (fun _ => measurable_const) (M₀ := 1) (fun _ _ => by simp)
      hf_abs_m (M_f := |M_f|) (fun ω a => by
        dsimp only [f_abs]; rw [abs_abs]; exact (hfb ω a).trans (le_abs_self _))
    dsimp only [f_abs] at h0
    simp only [Finset.prod_const_one, mul_one] at h0
    let V_obs0 (p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ))
        (x : α × ((Fin 2 ⊕ Unit) → ℝ)) : ℝ := u (S 0 p.2 x)
    have hVm0 : Measurable fun p : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) ×
        (α × ((Fin 2 ⊕ Unit) → ℝ)) => V_obs0 p.1 p.2 := by
      have hp : Measurable fun p : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) ×
          (α × ((Fin 2 ⊕ Unit) → ℝ)) => (p.1.2, p.2) :=
        (measurable_snd.comp measurable_fst).prodMk measurable_snd
      have hs0 := (measurable_interp_rotation_field hπ s t q 0).comp hp
      exact hu.measurable.comp hs0
    let G_abs (p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ))
        (a : R → α × ((Fin 2 ⊕ Unit) → ℝ)) : ℝ := |f p.1 (fun r => (a r).1)|
    have hGm : Measurable fun q : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) ×
        (R → α × ((Fin 2 ⊕ Unit) → ℝ)) => G_abs q.1 q.2 := by
      have hp : Measurable fun q : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) ×
          (R → α × ((Fin 2 ⊕ Unit) → ℝ)) => (q.1.1, fun r => (q.2 r).1) :=
        (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun r =>
          measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
      exact hf_abs_m.comp hp
    have hIm := measurable_integral_pi_tilted_prod_tilted μ_base γ_aux hE₀ hE₀i hVm0 hGm
    have hμ₀ (ω : Ω₀) : IsProbabilityMeasure (μ₀ ω) := isProbabilityMeasure_tilted (hE₀i ω)
    have hIi : Integrable (fun p => ∫ a : R → α × ((Fin 2 ⊕ Unit) → ℝ),
        |f p.1 (fun r => (a r).1)| ∂(Measure.pi fun _ : R => ν_rot 0 p)) (P₀.prod γ_sh) := by
      refine Integrable.of_bound hIm.aestronglyMeasurable |M_f| (ae_of_all _ fun p => ?_)
      have hp0 : Measurable fun x : α × ((Fin 2 ⊕ Unit) → ℝ) => (p.2, x) :=
        measurable_const.prodMk measurable_id
      have hs0 := (measurable_interp_rotation_field hπ s t q 0).comp hp0
      have hVp : Measurable fun x : α × ((Fin 2 ⊕ Unit) → ℝ) => u (S 0 p.2 x) :=
        hu.measurable.comp hs0
      have : IsProbabilityMeasure (ν_rot 0 p) :=
        isProbabilityMeasure_tilted_of_ae_le hVp.aemeasurable
          (ae_of_all _ fun _ => le_of_abs_le (hD_abs _))
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
      exact (le_abs_self _).trans (abs_integral_le_of_forall_abs_le _ fun _ => by
        rw [abs_abs]; exact (hfb _ _).trans (le_abs_self _))
    rw [integral_prod (fun p => ∫ a : R → α × ((Fin 2 ⊕ Unit) → ℝ),
        |f p.1 (fun r => (a r).1)| ∂(Measure.pi fun _ : R => ν_rot 0 p)) hIi]
    refine (integral_congr_ae (ae_of_all _ fun ω =>
      integral_congr_ae (ae_of_all _ fun w => ?_))).trans h0
    dsimp only [ν_rot]
    simp_rw [hS0]; rfl
  let d_spin (σ τ : PerceptronSpin N) : ℝ :=
    |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
      ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
  let T := α × ((Fin 2 ⊕ Unit) → ℝ)
  have hdm : Measurable fun p : T × T => d_spin (π p.1.1) (π p.2.1) := by
    let b : PerceptronSpin N × PerceptronSpin N → ℝ := fun p => d_spin p.1 p.2
    have hproj : Measurable fun p : T × T => (π p.1.1, π p.2.1) :=
      (hπ.comp (measurable_fst.comp measurable_fst)).prodMk
        (hπ.comp (measurable_fst.comp measurable_snd))
    have h := (measurable_of_finite b).comp hproj
    exact h
  have hpair (ϑ : ℝ) (ι : Type uR) [Fintype ι] (e : R → ι) (he : Function.Injective e)
      (i j : ι) (hij : i ≠ j) :
      ∫ p, ∫ a : ι → T, |f p.1 (fun r => (a (e r)).1)| * d_spin (π (a i).1) (π (a j).1)
        ∂(Measure.pi fun _ : ι => ν_rot ϑ p) ∂(P₀.prod γ_sh) ≤ m := by
    have hμ₀ (ω : Ω₀) : IsProbabilityMeasure (μ₀ ω) := isProbabilityMeasure_tilted (hE₀i ω)
    have hSϑ := measurable_interp_rotation_field hπ s t q ϑ
    have hprob_rot : ∀ p, IsProbabilityMeasure (ν_rot ϑ p) := fun p => by
      have hp : Measurable fun x : T => (p.2, x) := measurable_const.prodMk measurable_id
      have hsϑ := hSϑ.comp hp
      exact isProbabilityMeasure_tilted_of_ae_le (hu.measurable.comp hsϑ).aemeasurable
        (ae_of_all _ fun _ => hu.le _)
    let V_obsϑ (p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) (x : T) : ℝ := u (S ϑ p.2 x)
    have hVmϑ : Measurable fun p : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) × T =>
        V_obsϑ p.1 p.2 := by
      have hp : Measurable fun p : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) × T =>
          (p.1.2, p.2) :=
        (measurable_snd.comp measurable_fst).prodMk measurable_snd
      have hsϑ := hSϑ.comp hp
      exact hu.measurable.comp hsϑ
    let F_obs (p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) (a : R → T) : ℝ :=
      f p.1 (fun r => (a r).1)
    let G_abs (p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) (a : R → T) : ℝ :=
      |f p.1 (fun r => (a r).1)|
    have hFm : Measurable fun q : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) × (R → T) =>
        F_obs q.1 q.2 := by
      have hp : Measurable fun q : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) × (R → T) =>
          (q.1.1, fun r => (q.2 r).1) :=
        (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun r =>
          measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
      exact hf.comp hp
    have hGm : Measurable fun q : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) × (R → T) =>
        G_abs q.1 q.2 := by simpa only [G_abs, F_obs, Real.norm_eq_abs] using hFm.norm
    have hFI : ∀ᵐ p ∂P₀.prod γ_sh, Integrable (F_obs p) (Measure.pi fun _ : R => ν_rot ϑ p) :=
      ae_of_all _ fun p => by
        have hp : Measurable fun a : R → T => (p, a) := measurable_const.prodMk measurable_id
        have hm := hFm.comp hp
        exact Integrable.of_bound hm.aestronglyMeasurable |M_f|
          (ae_of_all _ fun a => by rw [Real.norm_eq_abs]; exact (hfb _ _).trans (le_abs_self _))
    have hIm := measurable_integral_pi_tilted_prod_tilted μ_base γ_aux hE₀ hE₀i hVmϑ hGm
    have hF₁ : Integrable (fun p => ∫ a, |F_obs p a| ∂(Measure.pi fun _ : R => ν_rot ϑ p))
        (P₀.prod γ_sh) :=
      Integrable.of_bound hIm.aestronglyMeasurable |M_f| (ae_of_all _ fun p => by
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
        exact (le_abs_self _).trans (abs_integral_le_of_forall_abs_le _ fun _ => by
          rw [abs_abs]; exact (hfb _ _).trans (le_abs_self _)))
    have hh := integral_integral_pair_holder_one_top (P₀.prod γ_sh) (ν_rot ϑ) he hij
      (f := F_obs) (d := fun a b => d_spin (π a.1) (π b.1))
      (fun _ _ => abs_nonneg _) hdm (Md := 2)
      (ae_of_all _ fun _ => ae_of_all _ fun _ => abs_perceptron_overlap_sub_le_two hq _ _)
      hFI hF₁
    let V_fn (ϑ' : ℝ) (w : (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ) (x : T) : ℝ := u (S ϑ' w x)
    have hVm_fn (ϑ' : ℝ) : Measurable fun p : ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ) × T =>
        V_fn ϑ' p.1 p.2 := by
      have hs_m := measurable_interp_rotation_field hπ s t q ϑ'
      exact hu.measurable.comp hs_m
    have hdom := integral_pi_tilted_prod_nonneg_le_exp_mul P₀ μ_base γ_sh γ_aux hE₀ hE₀i
      (hVm_fn ϑ) (hVm_fn 0) (fun _ _ => hD_abs _) (fun _ _ => hD_abs _) hf_abs_m
      (fun _ _ => abs_nonneg _) (M_g := |M_f|) (fun ω a => (hfb ω a).trans (le_abs_self _))
    rw [hm1_0] at hdom
    calc _ ≤ (∫ p, ∫ a : R → T, |F_obs p a| ∂(Measure.pi fun _ : R => ν_rot ϑ p)
            ∂(P₀.prod γ_sh)) * 2 := hh
      _ ≤ (Real.exp (4 * n * |D|) * I₁) * 2 := mul_le_mul_of_nonneg_right hdom zero_le_two
      _ = m := by dsimp only [m]; ring
  have hmain := abs_integral_interp_deriv_mul_sub_rhat_le_of_pair_bound
    P₀ μ_base hE₀ hE₀i π hπ hr hs ht hq hd hb hf hfb hm0 hpair
  refine hmain.trans_eq ?_
  dsimp only [K, m, I₁]
  ring

/-- **Proposition 2.3.5 for the `s`-interpolating constraint field, `L²` Cauchy-Schwarz
(`p₁ = p₂ = 2`).** -/
theorem abs_integral_interp_deriv_mul_sub_rhat_le_l2
    (R : Type uR) [Fintype R] (D : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (N : ℕ) {Ω₀ : Type uΩ} {α : Type uα}
        [MeasurableSpace Ω₀] [MeasurableSpace α]
        (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
        (μ_base : Measure α) [IsFiniteMeasure μ_base] [NeZero μ_base]
        {E₀ : Ω₀ → α → ℝ} (_hE₀ : Measurable fun p : Ω₀ × α => E₀ p.1 p.2)
        (_hE₀i : ∀ ω, Integrable (fun a => Real.exp (E₀ ω a)) μ_base)
        (π : α → PerceptronSpin N) (_hπ : Measurable π)
        {r₁ r₂ : R} (_hr : r₁ ≠ r₂)
        {s t q : ℝ} (_hs : s ∈ Icc (0 : ℝ) 1) (_ht : t ∈ Icc (0 : ℝ) 1) (_hq : q ∈ Icc (0 : ℝ) 1)
        {u : ℝ → ℝ}
        (_hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u))
        (_hb : ∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D)
        {f : Ω₀ → (R → α) → ℝ} (_hf : Measurable fun p : Ω₀ × (R → α) => f p.1 p.2)
        {M_f : ℝ} (_hfb : ∀ ω a, |f ω a| ≤ M_f),
        let γ₁ := Measure.pi fun _ : ((Fin N ⊕ Unit) ⊕ Unit) => gaussianReal 0 1
        let γ₂ := Measure.pi fun _ : Fin 2 => gaussianReal 0 1
        let μ₀ (ω : Ω₀) := μ_base.tilted (E₀ ω)
        let X_fn (w₁ : ((Fin N ⊕ Unit) ⊕ Unit) → ℝ) (x : α × (Fin 2 → ℝ)) : ℝ :=
          Sum.elim (Real.sqrt s • cavityCoef N t (π x.1))
            (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ w₁ +
          ![Real.sqrt s * Real.sqrt ((1 - t) / (N + 1)),
            Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ x.2
        let ν_new (p : Ω₀ × (((Fin N ⊕ Unit) ⊕ Unit) → ℝ)) :=
          ((μ₀ p.1).prod γ₂).tilted fun x => u (X_fn p.2 x)
        let d_spin (σ τ : PerceptronSpin N) : ℝ :=
          |((∑ i, ((σ.1 i : ℤ) : ℝ) * ((τ.1 i : ℤ) : ℝ)) +
            ((σ.2 : ℤ) : ℝ) * ((τ.2 : ℤ) : ℝ)) / (N + 1) - q|
        let rhat := perceptronRhat u q
        |(∫ p, ∫ a : R → α × (Fin 2 → ℝ),
            f p.1 (fun r => (a r).1) * (deriv u (X_fn p.2 (a r₁)) * deriv u (X_fn p.2 (a r₂)))
            ∂(Measure.pi fun _ : R => ν_new p) ∂(P₀.prod γ₁)) -
          rhat * (∫ p, ∫ a : R → α × (Fin 2 → ℝ),
            f p.1 (fun r => (a r).1)
            ∂(Measure.pi fun _ : R => ν_new p) ∂(P₀.prod γ₁))| ≤
          K * ((∫ p, ∫ a : R → α × (Fin 2 → ℝ),
                (f p.1 (fun r => (a r).1)) ^ 2
                ∂(Measure.pi fun _ : R => ν_new p) ∂(P₀.prod γ₁)) ^ (1 / (2 : ℝ)) *
              (∫ p, ∫ a : Fin 2 → α × (Fin 2 → ℝ),
                (d_spin (π (a 0).1) (π (a 1).1)) ^ 2
                ∂(Measure.pi fun _ : Fin 2 => ν_new p) ∂(P₀.prod γ₁)) ^ (1 / (2 : ℝ)) +
            1 / (N + 1) *
              ∫ p, ∫ a : R → α × (Fin 2 → ℝ),
                |f p.1 (fun r => (a r).1)| ∂(Measure.pi fun _ : R => ν_new p) ∂(P₀.prod γ₁)) := by
  let n : ℝ := Fintype.card R
  let M₀w : ℝ := 1 + |D|
  let M₁w : ℝ := |D|
  let L_u : ℝ := 1 + |D| + |(1 : ℝ)| + |(0 : ℝ)| + |(1 : ℝ)| * |D|
  let L_w : ℝ := 1 + |D| + |M₀w| + |M₁w| + |M₀w| * |D|
  let K_u : ℝ := (4 * n ^ 2 + n) * L_u ^ (Fintype.card R + 2)
  let K_w : ℝ := (4 * n ^ 2 + n) * L_w ^ (Fintype.card R + 2)
  let C_dom : ℝ := max (Real.exp ((2 * n + 4) * |D|)) (Real.exp (4 * n * |D|))
  let K : ℝ := (K_w / 2 + |D| ^ 2 * (K_u / 2)) * C_dom
  refine ⟨K, by positivity, ?_⟩
  intro N Ω₀ α _ _ P₀ _ μ_base _ _ E₀ hE₀ hE₀i π hπ r₁ r₂ hr s t q hs ht hq u hd hb f hf M_f hfb
    γ₁ γ₂ μ₀ X_fn ν_new d_spin rhat
  obtain ⟨hu, -, -⟩ := smartPathPotential_two_of_iteratedDeriv hd hb
  have hD_abs : ∀ x, |u x| ≤ |D| := fun x => (hu.abs_le x).trans (le_abs_self D)
  let f_sq (ω : Ω₀) (a : R → α) : ℝ := (f ω a) ^ 2
  have hf_sq_m : Measurable fun p : Ω₀ × (R → α) => f_sq p.1 p.2 := hf.pow_const 2
  let d_sq_old (_ω : Ω₀) (a : Fin 2 → α) : ℝ := (d_spin (π (a 0)) (π (a 1))) ^ 2
  have hd_sq_m : Measurable fun p : Ω₀ × (Fin 2 → α) => d_sq_old p.1 p.2 := by
    let b : PerceptronSpin N × PerceptronSpin N → ℝ := fun p => (d_spin p.1 p.2) ^ 2
    have hproj : Measurable fun p : Ω₀ × (Fin 2 → α) => (π (p.2 0), π (p.2 1)) :=
      (hπ.comp ((measurable_pi_apply 0).comp measurable_snd)).prodMk
        (hπ.comp ((measurable_pi_apply 1).comp measurable_snd))
    have h := (measurable_of_finite b).comp hproj
    exact h
  have hXm : Measurable fun p : (((Fin N ⊕ Unit) ⊕ Unit) → ℝ) × (α × (Fin 2 → ℝ)) =>
      X_fn p.1 p.2 := by
    have hX1 (j : (Fin N ⊕ Unit) ⊕ Unit) :
        Measurable fun p : (((Fin N ⊕ Unit) ⊕ Unit) → ℝ) × (α × (Fin 2 → ℝ)) =>
          (Sum.elim (Real.sqrt s • cavityCoef N t (π p.2.1))
            (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) j :=
      (measurable_of_finite fun σ =>
        (Sum.elim (Real.sqrt s • cavityCoef N t σ)
          (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) j).comp
        (hπ.comp (measurable_fst.comp measurable_snd))
    have hd1 : Measurable fun p : (((Fin N ⊕ Unit) ⊕ Unit) → ℝ) × (α × (Fin 2 → ℝ)) =>
        Sum.elim (Real.sqrt s • cavityCoef N t (π p.2.1))
          (fun _ => Real.sqrt (1 - s) * Real.sqrt q) ⬝ᵥ p.1 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ =>
        (hX1 j).mul ((measurable_pi_apply j).comp measurable_fst)
    have hd2 : Measurable fun p : (((Fin N ⊕ Unit) ⊕ Unit) → ℝ) × (α × (Fin 2 → ℝ)) =>
        ![Real.sqrt s * Real.sqrt ((1 - t) / (N + 1)),
          Real.sqrt (1 - s) * Real.sqrt (1 - q)] ⬝ᵥ p.2.2 := by
      simp only [dotProduct]
      exact Finset.measurable_sum _ fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))
    exact hd1.add hd2
  let A₀ : ℝ := ∫ p, ∫ a : R → α × (Fin 2 → ℝ),
    (f p.1 (fun r => (a r).1)) ^ 2 ∂(Measure.pi fun _ : R => ν_new p) ∂(P₀.prod γ₁)
  let B₀ : ℝ := ∫ p, ∫ a : Fin 2 → α × (Fin 2 → ℝ),
    (d_spin (π (a 0).1) (π (a 1).1)) ^ 2 ∂(Measure.pi fun _ : Fin 2 => ν_new p) ∂(P₀.prod γ₁)
  have hA₀_0 : 0 ≤ A₀ := integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  have hB₀_0 : 0 ≤ B₀ := integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
  let m : ℝ := Real.exp ((2 * n + 4) * |D|) * (A₀ ^ (1 / (2 : ℝ)) * B₀ ^ (1 / (2 : ℝ)))
  have hm0 : 0 ≤ m := by positivity
  let γ_sh := Measure.pi fun _ : (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) => gaussianReal 0 1
  let γ_aux := Measure.pi fun _ : (Fin 2 ⊕ Unit) => gaussianReal 0 1
  let X_sh : PerceptronSpin N → (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ :=
    fun σ => Sum.elim
      (Sum.elim (Real.sqrt s • cavityCoef N t σ) (fun _ => Real.sqrt (1 - s) * Real.sqrt q)) 0
  let Y_sh : (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ := Sum.elim 0 (fun _ => Real.sqrt q)
  let X_aux : (Fin 2 ⊕ Unit) → ℝ :=
    Sum.elim ![Real.sqrt s * Real.sqrt ((1 - t) / (N + 1)),
      Real.sqrt (1 - s) * Real.sqrt (1 - q)] 0
  let Y_aux : (Fin 2 ⊕ Unit) → ℝ := Sum.elim 0 (fun _ => Real.sqrt (1 - q))
  let S (ϑ : ℝ) (w : (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)
      (x : α × ((Fin 2 ⊕ Unit) → ℝ)) : ℝ :=
    Real.cos ϑ * (X_sh (π x.1) ⬝ᵥ w + X_aux ⬝ᵥ x.2) +
      Real.sin ϑ * (Y_sh ⬝ᵥ w + Y_aux ⬝ᵥ x.2)
  let ν_rot (ϑ : ℝ) (p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) :=
    ((μ₀ p.1).prod γ_aux).tilted fun x => u (S ϑ p.2 x)
  have hS0 (w : (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ) (x : α × ((Fin 2 ⊕ Unit) → ℝ)) :
      S 0 w x = X_fn (w ∘ Sum.inl) (x.1, x.2 ∘ Sum.inl) := by
    simp [S, X_sh, X_aux, X_fn, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  let V_obs0 (p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ))
      (x : α × ((Fin 2 ⊕ Unit) → ℝ)) : ℝ := u (S 0 p.2 x)
  have hVm0 : Measurable fun p : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) ×
      (α × ((Fin 2 ⊕ Unit) → ℝ)) => V_obs0 p.1 p.2 := by
    have hp : Measurable fun p : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) ×
        (α × ((Fin 2 ⊕ Unit) → ℝ)) => (p.1.2, p.2) :=
      (measurable_snd.comp measurable_fst).prodMk measurable_snd
    have hs0 := (measurable_interp_rotation_field hπ s t q 0).comp hp
    exact hu.measurable.comp hs0
  have hμ₀_p (ω : Ω₀) : IsProbabilityMeasure (μ₀ ω) := isProbabilityMeasure_tilted (hE₀i ω)
  have hprob_rot0 (p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) :
      IsProbabilityMeasure (ν_rot 0 p) := by
    have hp0 : Measurable fun x : α × ((Fin 2 ⊕ Unit) → ℝ) => (p.2, x) :=
      measurable_const.prodMk measurable_id
    have hs0 := (measurable_interp_rotation_field hπ s t q 0).comp hp0
    exact isProbabilityMeasure_tilted_of_ae_le (hu.measurable.comp hs0).aemeasurable
      (ae_of_all _ fun _ => le_of_abs_le (hD_abs _))
  have hA₀_eq : ∫ p, ∫ a : R → α × ((Fin 2 ⊕ Unit) → ℝ),
      (f p.1 (fun r => (a r).1)) ^ 2 ∂(Measure.pi fun _ : R => ν_rot 0 p) ∂(P₀.prod γ_sh) = A₀ := by
    have h0 := rotation_endpoint_zero_eq P₀ μ_base hE₀ hE₀i hu.measurable hD_abs X_fn hXm
      (fun _ _ => 1) (fun _ => measurable_const) (M₀ := 1) (fun _ _ => by simp) hf_sq_m
      (M_f := |M_f| ^ 2) fun ω a => by
        dsimp only [f_sq]; rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) ((hfb ω a).trans (le_abs_self _)) 2
    dsimp only [f_sq] at h0
    simp only [Finset.prod_const_one, mul_one] at h0
    let G_obs (p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ))
        (a : R → α × ((Fin 2 ⊕ Unit) → ℝ)) : ℝ := (f p.1 (fun r => (a r).1)) ^ 2
    have hGm : Measurable fun q : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) ×
        (R → α × ((Fin 2 ⊕ Unit) → ℝ)) => G_obs q.1 q.2 := by
      have hp : Measurable fun q : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) ×
          (R → α × ((Fin 2 ⊕ Unit) → ℝ)) => (q.1.1, fun r => (q.2 r).1) :=
        (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun r =>
          measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
      exact hf_sq_m.comp hp
    have hIm := measurable_integral_pi_tilted_prod_tilted μ_base γ_aux hE₀ hE₀i hVm0 hGm
    have hIi : Integrable (fun p => ∫ a : R → α × ((Fin 2 ⊕ Unit) → ℝ),
        (f p.1 (fun r => (a r).1)) ^ 2 ∂(Measure.pi fun _ : R => ν_rot 0 p)) (P₀.prod γ_sh) :=
      Integrable.of_bound hIm.aestronglyMeasurable (|M_f| ^ 2) (ae_of_all _ fun p => by
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
        exact (le_abs_self _).trans (abs_integral_le_of_forall_abs_le _ fun a => by
          rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) ((hfb _ _).trans (le_abs_self _)) 2))
    rw [integral_prod (fun p => ∫ a : R → α × ((Fin 2 ⊕ Unit) → ℝ),
        (f p.1 (fun r => (a r).1)) ^ 2 ∂(Measure.pi fun _ : R => ν_rot 0 p)) hIi]
    refine (integral_congr_ae (ae_of_all _ fun ω =>
      integral_congr_ae (ae_of_all _ fun w => ?_))).trans h0
    dsimp only [ν_rot]; simp_rw [hS0]; rfl
  have hB₀_eq : ∫ p, ∫ a : Fin 2 → α × ((Fin 2 ⊕ Unit) → ℝ),
      (d_spin (π (a 0).1) (π (a 1).1)) ^ 2
      ∂(Measure.pi fun _ : Fin 2 => ν_rot 0 p) ∂(P₀.prod γ_sh) = B₀ := by
    have h0 := rotation_endpoint_zero_eq P₀ μ_base hE₀ hE₀i hu.measurable hD_abs X_fn hXm
      (fun _ _ => 1) (fun _ => measurable_const) (M₀ := 1) (fun _ _ => by simp) hd_sq_m
      (M_f := 4) fun _ a => by
        dsimp only [d_sq_old]
        rw [abs_of_nonneg (sq_nonneg _), show (4 : ℝ) = 2 ^ 2 by norm_num]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_perceptron_overlap_sub_le_two hq _ _) 2
    dsimp only [d_sq_old] at h0
    simp only [Finset.prod_const_one, mul_one] at h0
    let G_obs (_p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ))
        (a : Fin 2 → α × ((Fin 2 ⊕ Unit) → ℝ)) : ℝ := (d_spin (π (a 0).1) (π (a 1).1)) ^ 2
    have hGm : Measurable fun q : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) ×
        (Fin 2 → α × ((Fin 2 ⊕ Unit) → ℝ)) => G_obs q.1 q.2 := by
      let b : PerceptronSpin N × PerceptronSpin N → ℝ := fun p => (d_spin p.1 p.2) ^ 2
      have hp : Measurable fun q : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) ×
          (Fin 2 → α × ((Fin 2 ⊕ Unit) → ℝ)) => (π (q.2 0).1, π (q.2 1).1) :=
        (hπ.comp (measurable_fst.comp ((measurable_pi_apply 0).comp measurable_snd))).prodMk
          (hπ.comp (measurable_fst.comp ((measurable_pi_apply 1).comp measurable_snd)))
      have hm_b := (measurable_of_finite b).comp hp
      exact hm_b
    have hIm := measurable_integral_pi_tilted_prod_tilted μ_base γ_aux hE₀ hE₀i hVm0 hGm
    have hIi : Integrable (fun p => ∫ a : Fin 2 → α × ((Fin 2 ⊕ Unit) → ℝ),
        (d_spin (π (a 0).1) (π (a 1).1)) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => ν_rot 0 p)) (P₀.prod γ_sh) :=
      Integrable.of_bound hIm.aestronglyMeasurable 4 (ae_of_all _ fun p => by
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
        exact (le_abs_self _).trans (abs_integral_le_of_forall_abs_le _ fun a => by
          rw [abs_of_nonneg (sq_nonneg _), show (4 : ℝ) = 2 ^ 2 by norm_num]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_perceptron_overlap_sub_le_two hq _ _) 2))
    rw [integral_prod (fun p => ∫ a : Fin 2 → α × ((Fin 2 ⊕ Unit) → ℝ),
        (d_spin (π (a 0).1) (π (a 1).1)) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => ν_rot 0 p)) hIi]
    refine (integral_congr_ae (ae_of_all _ fun ω =>
      integral_congr_ae (ae_of_all _ fun w => ?_))).trans h0
    dsimp only [ν_rot]; simp_rw [hS0]; rfl
  let T := α × ((Fin 2 ⊕ Unit) → ℝ)
  have hdm : Measurable fun p : T × T => d_spin (π p.1.1) (π p.2.1) := by
    let b : PerceptronSpin N × PerceptronSpin N → ℝ := fun p => d_spin p.1 p.2
    have hproj : Measurable fun p : T × T => (π p.1.1, π p.2.1) :=
      (hπ.comp (measurable_fst.comp measurable_fst)).prodMk
        (hπ.comp (measurable_fst.comp measurable_snd))
    have h := (measurable_of_finite b).comp hproj
    exact h
  have hp22 : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hpair (ϑ : ℝ) (ι : Type uR) [Fintype ι] (e : R → ι) (he : Function.Injective e)
      (i j : ι) (hij : i ≠ j) :
      ∫ p, ∫ a : ι → T, |f p.1 (fun r => (a (e r)).1)| * d_spin (π (a i).1) (π (a j).1)
        ∂(Measure.pi fun _ : ι => ν_rot ϑ p) ∂(P₀.prod γ_sh) ≤ m := by
    have hμ₀ (ω : Ω₀) : IsProbabilityMeasure (μ₀ ω) := isProbabilityMeasure_tilted (hE₀i ω)
    have hSϑ := measurable_interp_rotation_field hπ s t q ϑ
    have hprob_rot : ∀ p, IsProbabilityMeasure (ν_rot ϑ p) := fun p => by
      have hp : Measurable fun x : T => (p.2, x) := measurable_const.prodMk measurable_id
      have hsϑ := hSϑ.comp hp
      exact isProbabilityMeasure_tilted_of_ae_le (hu.measurable.comp hsϑ).aemeasurable
        (ae_of_all _ fun _ => hu.le _)
    let V_obsϑ (p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) (x : T) : ℝ := u (S ϑ p.2 x)
    have hVmϑ : Measurable fun p : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) × T =>
        V_obsϑ p.1 p.2 := by
      have hp : Measurable fun p : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) × T =>
          (p.1.2, p.2) :=
        (measurable_snd.comp measurable_fst).prodMk measurable_snd
      have hsϑ := hSϑ.comp hp
      exact hu.measurable.comp hsϑ
    let F_obs (p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) (a : R → T) : ℝ :=
      f p.1 (fun r => (a r).1)
    let F_rpow (p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) (a : R → T) : ℝ :=
      |f p.1 (fun r => (a r).1)| ^ (2 : ℝ)
    let D_rpow (_p : Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) (a : Fin 2 → T) : ℝ :=
      d_spin (π (a 0).1) (π (a 1).1) ^ (2 : ℝ)
    have hFm : Measurable fun q : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) × (R → T) =>
        F_obs q.1 q.2 := by
      have hp : Measurable fun q : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) × (R → T) =>
          (q.1.1, fun r => (q.2 r).1) :=
        (measurable_fst.comp measurable_fst).prodMk (measurable_pi_iff.2 fun r =>
          measurable_fst.comp ((measurable_pi_apply r).comp measurable_snd))
      exact hf.comp hp
    have hFr_m : Measurable fun q : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) × (R → T) =>
        F_rpow q.1 q.2 := by
      have habs : Measurable fun q : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) × (R → T) =>
          |F_obs q.1 q.2| := by simpa only [Real.norm_eq_abs] using hFm.norm
      exact habs.pow_const (2 : ℝ)
    have hDr_m : Measurable fun q : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) × (Fin 2 → T) =>
        D_rpow q.1 q.2 := by
      have hp2 : Measurable fun q : (Ω₀ × ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ)) × (Fin 2 → T) =>
          (q.2 0, q.2 1) :=
        ((measurable_pi_apply 0).comp measurable_snd).prodMk
          ((measurable_pi_apply 1).comp measurable_snd)
      have hd2 := hdm.comp hp2
      exact hd2.pow_const (2 : ℝ)
    have hFp_mem : ∀ᵐ p ∂P₀.prod γ_sh,
        MemLp (F_obs p) (ENNReal.ofReal 2) (Measure.pi fun _ : R => ν_rot ϑ p) :=
      ae_of_all _ fun p => by
        have hp : Measurable fun a : R → T => (p, a) := measurable_const.prodMk measurable_id
        have hm := hFm.comp hp
        exact MemLp.of_bound hm.aestronglyMeasurable |M_f|
          (ae_of_all _ fun a => by rw [Real.norm_eq_abs]; exact (hfb _ _).trans (le_abs_self _))
    have hDp_mem : ∀ᵐ p ∂P₀.prod γ_sh,
        MemLp (fun a : Fin 2 → T => d_spin (π (a 0).1) (π (a 1).1)) (ENNReal.ofReal 2)
          (Measure.pi fun _ : Fin 2 => ν_rot ϑ p) :=
      ae_of_all _ fun p => by
        have hp : Measurable fun a : Fin 2 → T => (a 0, a 1) :=
          (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
        have hm := hdm.comp hp
        exact MemLp.of_bound hm.aestronglyMeasurable 2
          (ae_of_all _ fun a => by
            rw [Real.norm_of_nonneg (abs_nonneg _)]
            exact abs_perceptron_overlap_sub_le_two hq _ _)
    have hIm_F := measurable_integral_pi_tilted_prod_tilted μ_base γ_aux hE₀ hE₀i hVmϑ hFr_m
    have hIm_D := measurable_integral_pi_tilted_prod_tilted (R := Fin 2)
      μ_base γ_aux hE₀ hE₀i hVmϑ hDr_m
    have hFp_int : Integrable (fun p => ∫ a : R → T, |F_obs p a| ^ (2 : ℝ)
        ∂(Measure.pi fun _ : R => ν_rot ϑ p)) (P₀.prod γ_sh) :=
      Integrable.of_bound hIm_F.aestronglyMeasurable (|M_f| ^ 2) (ae_of_all _ fun p => by
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _)]
        exact (le_abs_self _).trans (abs_integral_le_of_forall_abs_le _ fun a => by
          rw [Real.rpow_two, abs_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (abs_nonneg _) ((hfb _ _).trans (le_abs_self _)) 2))
    have hDp_int : Integrable (fun p => ∫ a : Fin 2 → T, d_spin (π (a 0).1) (π (a 1).1) ^ (2 : ℝ)
        ∂(Measure.pi fun _ : Fin 2 => ν_rot ϑ p)) (P₀.prod γ_sh) :=
      Integrable.of_bound hIm_D.aestronglyMeasurable 4 (ae_of_all _ fun p => by
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _)]
        exact (le_abs_self _).trans (abs_integral_le_of_forall_abs_le _ fun a => by
          rw [Real.rpow_two, abs_of_nonneg (sq_nonneg _), show (4 : ℝ) = 2 ^ 2 by norm_num]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_perceptron_overlap_sub_le_two hq _ _) 2))
    have hh := integral_integral_pair_holder_prob (P₀.prod γ_sh) (ν_rot ϑ) he hij
      (f := F_obs) (d := fun a b => d_spin (π a.1) (π b.1))
      (fun _ _ => abs_nonneg _) hp22 hFp_mem hFp_int hDp_mem hDp_int
    let V_fn (ϑ' : ℝ) (w : (((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ) (x : T) : ℝ := u (S ϑ' w x)
    have hVm_fn (ϑ' : ℝ) : Measurable fun p : ((((Fin N ⊕ Unit) ⊕ Unit) ⊕ Unit) → ℝ) × T =>
        V_fn ϑ' p.1 p.2 := by
      have hs_m := measurable_interp_rotation_field hπ s t q ϑ'
      exact hu.measurable.comp hs_m
    have hdom_A := integral_pi_tilted_prod_nonneg_le_exp_mul P₀ μ_base γ_sh γ_aux hE₀ hE₀i
      (hVm_fn ϑ) (hVm_fn 0) (fun _ _ => hD_abs _) (fun _ _ => hD_abs _) hf_sq_m
      (fun _ _ => sq_nonneg _) (M_g := |M_f| ^ 2)
      (fun ω a => by
        dsimp only [f_sq]; rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) ((hfb ω a).trans (le_abs_self _)) 2)
    have hdom_B := integral_pi_tilted_prod_nonneg_le_exp_mul P₀ μ_base γ_sh γ_aux hE₀ hE₀i
      (hVm_fn ϑ) (hVm_fn 0) (fun _ _ => hD_abs _) (fun _ _ => hD_abs _) hd_sq_m
      (fun _ _ => sq_nonneg _) (M_g := 4)
      (fun _ _ => by
        dsimp only [d_sq_old]
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_perceptron_overlap_sub_le_two hq _ _) 2)
    dsimp only [f_sq] at hdom_A
    dsimp only [d_sq_old] at hdom_B
    rw [hA₀_eq] at hdom_A
    rw [hB₀_eq] at hdom_B
    have hrpow_eq_A : (∫ p, ∫ a : R → T, |F_obs p a| ^ (2 : ℝ)
        ∂(Measure.pi fun _ : R => ν_rot ϑ p) ∂(P₀.prod γ_sh)) =
      ∫ p, ∫ a : R → T, (f p.1 (fun r => (a r).1)) ^ 2
        ∂(Measure.pi fun _ : R => ν_rot ϑ p) ∂(P₀.prod γ_sh) :=
      integral_congr_ae (ae_of_all _ fun _ => integral_congr_ae (ae_of_all _ fun _ => by
        dsimp only [F_obs]; rw [Real.rpow_two, sq_abs]))
    have hrpow_eq_B : (∫ p, ∫ a : Fin 2 → T, d_spin (π (a 0).1) (π (a 1).1) ^ (2 : ℝ)
        ∂(Measure.pi fun _ : Fin 2 => ν_rot ϑ p) ∂(P₀.prod γ_sh)) =
      ∫ p, ∫ a : Fin 2 → T, (d_spin (π (a 0).1) (π (a 1).1)) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => ν_rot ϑ p) ∂(P₀.prod γ_sh) :=
      integral_congr_ae (ae_of_all _ fun _ => integral_congr_ae (ae_of_all _ fun a =>
        Real.rpow_two (d_spin (π (a 0).1) (π (a 1).1))))
    rw [hrpow_eq_A, hrpow_eq_B] at hh
    have hA_rpow : (∫ p, ∫ a : R → T, (f p.1 (fun r => (a r).1)) ^ 2
        ∂(Measure.pi fun _ : R => ν_rot ϑ p) ∂(P₀.prod γ_sh)) ^ (1 / (2 : ℝ)) ≤
        Real.exp (2 * n * |D|) * A₀ ^ (1 / (2 : ℝ)) := by
      have h0 : 0 ≤ ∫ p, ∫ a : R → T, (f p.1 (fun r => (a r).1)) ^ 2
          ∂(Measure.pi fun _ : R => ν_rot ϑ p) ∂(P₀.prod γ_sh) :=
        integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
      calc _ ≤ (Real.exp (4 * n * |D|) * A₀) ^ (1 / (2 : ℝ)) :=
            Real.rpow_le_rpow h0 hdom_A (by positivity)
        _ = (Real.exp (4 * n * |D|)) ^ (1 / (2 : ℝ)) * A₀ ^ (1 / (2 : ℝ)) :=
            Real.mul_rpow (Real.exp_nonneg _) hA₀_0
        _ = Real.exp (2 * n * |D|) * A₀ ^ (1 / (2 : ℝ)) := by
            rw [← Real.exp_mul]; congr 2; ring
    have hB_rpow : (∫ p, ∫ a : Fin 2 → T, (d_spin (π (a 0).1) (π (a 1).1)) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => ν_rot ϑ p) ∂(P₀.prod γ_sh)) ^ (1 / (2 : ℝ)) ≤
        Real.exp (4 * |D|) * B₀ ^ (1 / (2 : ℝ)) := by
      have h0 : 0 ≤ ∫ p, ∫ a : Fin 2 → T, (d_spin (π (a 0).1) (π (a 1).1)) ^ 2
          ∂(Measure.pi fun _ : Fin 2 => ν_rot ϑ p) ∂(P₀.prod γ_sh) :=
        integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _
      have hc2 : (Fintype.card (Fin 2) : ℝ) = 2 := by simp
      rw [hc2] at hdom_B
      calc _ ≤ (Real.exp (4 * 2 * |D|) * B₀) ^ (1 / (2 : ℝ)) :=
            Real.rpow_le_rpow h0 hdom_B (by positivity)
        _ = (Real.exp (4 * 2 * |D|)) ^ (1 / (2 : ℝ)) * B₀ ^ (1 / (2 : ℝ)) :=
            Real.mul_rpow (Real.exp_nonneg _) hB₀_0
        _ = Real.exp (4 * |D|) * B₀ ^ (1 / (2 : ℝ)) := by
            rw [← Real.exp_mul]; congr 2; ring
    calc _ ≤ (Real.exp (2 * n * |D|) * A₀ ^ (1 / (2 : ℝ))) *
            (Real.exp (4 * |D|) * B₀ ^ (1 / (2 : ℝ))) :=
          hh.trans (mul_le_mul hA_rpow hB_rpow
            (Real.rpow_nonneg (integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _) _)
            (by positivity))
      _ = (Real.exp (2 * n * |D|) * Real.exp (4 * |D|)) *
            (A₀ ^ (1 / (2 : ℝ)) * B₀ ^ (1 / (2 : ℝ))) := by ring
      _ = m := by dsimp only [m]; rw [← Real.exp_add]; congr 2; ring
  have hmain := abs_integral_interp_deriv_mul_sub_rhat_le_of_pair_bound
    P₀ μ_base hE₀ hE₀i π hπ hr hs ht hq hd hb hf hfb hm0 hpair
  refine hmain.trans ?_
  have hC1 : Real.exp ((2 * n + 4) * |D|) ≤ C_dom := le_max_left _ _
  have hC2 : Real.exp (4 * n * |D|) ≤ C_dom := le_max_right _ _
  let I₁ : ℝ := ∫ p, ∫ a : R → α × (Fin 2 → ℝ),
    |f p.1 (fun r => (a r).1)| ∂(Measure.pi fun _ : R => ν_new p) ∂(P₀.prod γ₁)
  have hI₁_0 : 0 ≤ I₁ := integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _
  have hm_le : m ≤ C_dom * (A₀ ^ (1 / (2 : ℝ)) * B₀ ^ (1 / (2 : ℝ))) :=
    mul_le_mul_of_nonneg_right hC1 (by positivity)
  have herr_le : 1 / (N + 1 : ℝ) * Real.exp (4 * n * |D|) * I₁ ≤
      C_dom * (1 / (N + 1 : ℝ) * I₁) := by
    calc 1 / (N + 1 : ℝ) * Real.exp (4 * n * |D|) * I₁
        = Real.exp (4 * n * |D|) * (1 / (N + 1 : ℝ) * I₁) := by ring
      _ ≤ C_dom * (1 / (N + 1 : ℝ) * I₁) := mul_le_mul_of_nonneg_right hC2 (by positivity)
  calc (K_w / 2 + |D| ^ 2 * (K_u / 2)) * (m + 1 / (N + 1) * Real.exp (4 * n * |D|) * I₁)
      ≤ (K_w / 2 + |D| ^ 2 * (K_u / 2)) *
          (C_dom * (A₀ ^ (1 / (2 : ℝ)) * B₀ ^ (1 / (2 : ℝ))) + C_dom * (1 / (N + 1) * I₁)) :=
        mul_le_mul_of_nonneg_left (add_le_add hm_le herr_le) (by positivity)
    _ = K * (A₀ ^ (1 / (2 : ℝ)) * B₀ ^ (1 / (2 : ℝ)) + 1 / (N + 1) * I₁) := by
        dsimp only [K]; ring

end MasterComparison

end SpinGlasses
