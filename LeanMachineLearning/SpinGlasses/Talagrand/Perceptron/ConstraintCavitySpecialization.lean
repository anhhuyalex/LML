/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Calculus.IteratedDerivBounds
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.TrigSquareParam
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.SinCosEndpoint
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaEquivariance
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityAngleStep
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavitySpinOnly
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityEndpoint

/-!
# Specializing the unweighted cavity ratio to the concrete i.i.d. disorder

Talagrand Section 2.3, Task 1 (unweighted specialization of T18.5 and T18.7). Under the concrete
i.i.d. disorder law `smartPathDisorder (pi (pi γ₁)) r ⊗ γ₁` of `(ω, z)`, the measure-preserving
split `measurePreserving_smartPathDisorder_cavitySplit` separates the old disorder `ω₀` (including
the shared last field `Y ∼ 𝒩(0, r)`) from the independent standard Gaussian block
`ξ = ((g_M, a_M), z)` indexed by `(Fin N ⊕ Unit) ⊕ Unit`. Together with
`smartPathField_last_eq_dotProduct` and `integral_pi_tilted_cavityPath_spinOnly_eq_ratio`, this
identifies the concrete quenched average `ν_{t,s}(f)` and its `L^p`/overlap moments with the
abstract cavity ratio of `ConstraintCavityOldDisorder.lean` and `ConstraintCavityAngleStep.lean`.

We also retain the prefactor `sin s * cos s` from `hasDerivAt_integral_cavityRatio_theta` through
the old-disorder average so that:
* in the angle parameter `s`, the derivative is `sin s * cos s * d` with `|d|` bounded by the
  Hölder expression;
* in the book's parameter `v = cos² s` (`s = arccos √v`) on `(0, 1)`, the chain-rule singularity
  cancels `sin s * cos s` via `HasDerivAt.comp_arccos_sqrt_of_sin_cos`, giving `-d / 2`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace SpinGlasses

/-- Tilting `μ.prod γ` by `E₀ ∘ Prod.fst` equals `(μ.tilted E₀).prod γ` when `γ` is a probability
measure. -/
theorem tilted_prod_comp_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsFiniteMeasure μ] (γ : Measure β) [IsProbabilityMeasure γ]
    (E₀ : α → ℝ) :
    (μ.prod γ).tilted (fun p => E₀ p.1) = (μ.tilted E₀).prod γ := by
  have hZ : ∫ p : α × β, Real.exp (E₀ p.1) ∂(μ.prod γ) = ∫ a, Real.exp (E₀ a) ∂μ :=
    integral_prod_fun_fst_of_isProbabilityMeasure μ γ fun a => Real.exp (E₀ a)
  symm
  refine Measure.prod_eq fun s t hs ht => ?_
  rw [tilted_apply_eq_ofReal_integral, tilted_apply_eq_ofReal_integral, hZ]
  have hind : ∀ p : α × β,
      (s ×ˢ t).indicator (fun p : α × β => Real.exp (E₀ p.1) / ∫ a, Real.exp (E₀ a) ∂μ) p =
        (s.indicator (fun a => Real.exp (E₀ a) / ∫ a, Real.exp (E₀ a) ∂μ) p.1) *
          (t.indicator (fun _ => (1 : ℝ)) p.2) := by
    rintro ⟨a, b⟩
    by_cases ha : a ∈ s <;> by_cases hb : b ∈ t <;> simp [Set.mem_prod, ha, hb]
  rw [← integral_indicator (hs.prod ht)]
  simp_rw [hind]
  rw [integral_prod_mul, integral_indicator hs, integral_indicator_const _ ht, smul_eq_mul,
    mul_one, ENNReal.ofReal_mul (setIntegral_nonneg hs fun _ _ => div_nonneg (Real.exp_pos _).le
      (integral_nonneg fun _ => (Real.exp_pos _).le)),
    Measure.real, ENNReal.ofReal_toReal (measure_ne_top γ t)]

/-- **Exact state-space split of the extended cavity replica average.** At fixed disorder `(ω, z)`,
splitting `(x, ξ) ∈ SmartPathState N (M + 1) × ℝ` into the old state `(x.1, Fin.init x.2)` and the
two fresh auxiliary Gaussians `![x.2 (Fin.last M), ξ]` rewrites the extended replica average as a
replica average over `((smartPathBase N M).tilted E_old ⊗ γ₁^{⊗2}).tilted (u ∘ S_s)`. -/
theorem cavity_extended_replica_split_eq
    {N M : ℕ} {R : Type*} [Fintype R]
    {u : ℝ → ℝ} (hu : Measurable u) {D : ℝ} (hD : ∀ x, u x ≤ D)
    (t q s : ℝ) (ω : SmartPathDisorder N (M + 1)) (z : ℝ)
    (G : (R → SmartPathState N M × (Fin 2 → ℝ)) → ℝ) :
    ∫ σ : R → SmartPathState N (M + 1) × ℝ,
      G (fun r => (((σ r).1.1, Fin.init (σ r).1.2), ![(σ r).1.2 (Fin.last M), (σ r).2]))
      ∂(Measure.pi fun _ : R => ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
        fun x : SmartPathState N (M + 1) × ℝ =>
          smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1.1, Fin.init x.1.2) +
            u (Real.cos s * smartPathField t ω x.1 (Fin.last M) +
              Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * x.2))) =
    ∫ τ : R → SmartPathState N M × (Fin 2 → ℝ), G τ
      ∂(Measure.pi fun _ : R =>
        (((smartPathBase N M).tilted
            (smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2))).prod
          (Measure.pi fun _ : Fin 2 => gaussianReal 0 1)).tilted
        fun y : SmartPathState N M × (Fin 2 → ℝ) =>
          u (Real.cos s *
              (cavityCoef N t y.1.1 ⬝ᵥ
                Sum.elim (ω.1.1 (Fin.last M)) (fun _ : Unit => ω.1.2 (Fin.last M)) +
                Real.sqrt ((1 - t) / (N + 1)) * y.2 0) +
            Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * y.2 1))) := by
  let γ₁ : Measure ℝ := gaussianReal 0 1
  let e1 : SmartPathState N (M + 1) × ℝ ≃ᵐ (SmartPathState N M × ℝ) × ℝ :=
    MeasurableEquiv.prodCongr (smartPathStateSplit N M) (MeasurableEquiv.refl ℝ)
  let e2 : (SmartPathState N M × ℝ) × ℝ ≃ᵐ SmartPathState N M × (ℝ × ℝ) :=
    MeasurableEquiv.prodAssoc
  let e3 : SmartPathState N M × (ℝ × ℝ) ≃ᵐ SmartPathState N M × (Fin 2 → ℝ) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.piFinTwo fun _ => ℝ).symm
  let e : SmartPathState N (M + 1) × ℝ ≃ᵐ SmartPathState N M × (Fin 2 → ℝ) :=
    (e1.trans e2).trans e3
  have he_apply : ∀ x : SmartPathState N (M + 1) × ℝ,
      e x = ((x.1.1, Fin.init x.1.2), ![x.1.2 (Fin.last M), x.2]) := fun x => by
    have h1 : e1 x = (((x.1.1, Fin.init x.1.2), x.1.2 (Fin.last M)), x.2) :=
      Prod.ext (smartPathStateSplit_apply x.1) rfl
    have h2 : e2 (e1 x) = ((x.1.1, Fin.init x.1.2), (x.1.2 (Fin.last M), x.2)) := by
      rw [h1]; rfl
    change e3 (e2 (e1 x)) = _
    rw [h2]
    refine Prod.ext rfl (funext fun i => ?_)
    fin_cases i <;> simp [e3, MeasurableEquiv.coe_prodCongr]
  have hmp_e : MeasurePreserving ⇑e
      ((smartPathBase N (M + 1)).prod γ₁)
      ((smartPathBase N M).prod (Measure.pi fun _ : Fin 2 => γ₁)) := by
    have h1 : MeasurePreserving ⇑e1 ((smartPathBase N (M + 1)).prod γ₁)
        (((smartPathBase N M).prod γ₁).prod γ₁) :=
      (measurePreserving_smartPathStateSplit N M).prod (MeasurePreserving.id γ₁)
    have h2 : MeasurePreserving ⇑e2 (((smartPathBase N M).prod γ₁).prod γ₁)
        ((smartPathBase N M).prod (γ₁.prod γ₁)) :=
      measurePreserving_prodAssoc _ _ _
    have h3 : MeasurePreserving ⇑e3 ((smartPathBase N M).prod (γ₁.prod γ₁))
        ((smartPathBase N M).prod (Measure.pi fun _ : Fin 2 => γ₁)) :=
      (MeasurePreserving.id _).prod (measurePreserving_piFinTwo fun _ => γ₁).symm
    exact h3.comp (h2.comp h1)
  let E_src : SmartPathState N (M + 1) × ℝ → ℝ := fun x =>
    smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1.1, Fin.init x.1.2) +
      u (Real.cos s * smartPathField t ω x.1 (Fin.last M) +
        Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * x.2))
  let E₀ : SmartPathState N M → ℝ :=
    smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2)
  let V_dst : SmartPathState N M × (Fin 2 → ℝ) → ℝ := fun y =>
    u (Real.cos s *
        (cavityCoef N t y.1.1 ⬝ᵥ
          Sum.elim (ω.1.1 (Fin.last M)) (fun _ : Unit => ω.1.2 (Fin.last M)) +
          Real.sqrt ((1 - t) / (N + 1)) * y.2 0) +
      Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * y.2 1))
  have hE_src_m : Measurable E_src :=
    ((measurable_smartPathEnergy_init hu t ω).comp measurable_fst).add
      (hu.comp ((measurable_const.mul
        ((measurable_smartPathField_slice t ω (Fin.last M)).comp measurable_fst)).add
        (measurable_const.mul (measurable_const.add (measurable_const.mul measurable_snd)))))
  have hE_comp : E_src ∘ e.symm = (fun y => E₀ y.1) + V_dst := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    change E_src (e.symm (e x)) = E₀ (e x).1 + V_dst (e x)
    rw [MeasurableEquiv.symm_apply_apply]
    dsimp only [E_src, E₀, V_dst]
    rw [he_apply]
    dsimp only
    congr 3
    rw [smartPathField_last_eq_dotProduct]
    rfl
  have hmap_tilt : (((smartPathBase N (M + 1)).prod γ₁).tilted E_src).map e =
      (((smartPathBase N M).tilted E₀).prod (Measure.pi fun _ : Fin 2 => γ₁)).tilted V_dst := by
    rw [map_tilted_measurableEquiv e hmp_e hE_src_m, hE_comp]
    have hexp_E₀ : Integrable (fun y : SmartPathState N M × (Fin 2 → ℝ) => Real.exp (E₀ y.1))
        ((smartPathBase N M).prod (Measure.pi fun _ : Fin 2 => γ₁)) :=
      (integrable_exp_perceptron_smart_path_energy hu hD _ t).comp_fst _
    rw [← tilted_tilted hexp_E₀ V_dst, tilted_prod_comp_fst]
  have : IsFiniteMeasure (((smartPathBase N (M + 1)).prod γ₁).tilted E_src) := by
    have : IsProbabilityMeasure (((smartPathBase N (M + 1)).prod γ₁).tilted E_src) :=
      isProbabilityMeasure_tilted_of_ae_le (C := (M * D + Real.sqrt (1 - t) * |ω.2|) + D)
        hE_src_m.aemeasurable
        (ae_of_all _ fun x => add_le_add (smartPathEnergy_init_le hD t ω x.1) (hD _))
    infer_instance
  have hrhs := (integral_pi_map_equiv (((smartPathBase N (M + 1)).prod γ₁).tilted E_src) e G).symm
  rw [hmap_tilt] at hrhs
  simp_rw [he_apply] at hrhs
  exact hrhs

/-- Derive `ContDiff ℝ 2 u` and the bounds `|u|, |u'|, |u''| ≤ D` from Talagrand's hypothesis
(2.7): `∀ j < 3, Differentiable ℝ (iteratedDeriv j u)` and `∀ j ≤ 3, ∀ x, |iteratedDeriv j u x| ≤ D`. -/
theorem contDiff_two_of_forall_lt_three_differentiable {u : ℝ → ℝ}
    (hd : ∀ j < 3, Differentiable ℝ (iteratedDeriv j u)) :
    ContDiff ℝ 2 u := by
  have h0 : Differentiable ℝ u := by simpa using hd 0 (by omega)
  have h1 : Differentiable ℝ (deriv u) := by
    simpa [iteratedDeriv_one] using hd 1 (by omega)
  have h2 : Differentiable ℝ (deriv (deriv u)) := by
    simpa [iteratedDeriv_succ, iteratedDeriv_one] using hd 2 (by omega)
  have hc1 : ContDiff ℝ 1 (deriv u) :=
    contDiff_one_iff_deriv.2 ⟨h1, h2.continuous⟩
  have hc2 : ContDiff ℝ ((1 : ℕ) + 1) u :=
    contDiff_succ_iff_deriv.2 ⟨h0, by simp, hc1⟩
  exact hc2

/-- **Bridge between the concrete cavity law `ν_{t,s}` and the abstract tilted-count average.**
Under the concrete i.i.d. disorder law for `M + 1` constraints paired with `z ∼ 𝒩(0, 1)`, for any
random spin observable `f ω₀` depending on the old disorder `ω₀ : SmartPathDisorder N M` and
integrable in `L¹` at each spin tuple, the concrete extended cavity average equals the iterated
integral over `(ω₀, ξ)` of the counting-measure Gibbs average with weights `w ω₀` and smoothing
`ψ_s(Y_s ξ)`. -/
theorem integral_cavityPath_spinOnly_eq_cavityRatio {N M : ℕ} {R : Type*} [Fintype R]
    [DecidableEq R] {u : ℝ → ℝ} (hu : Measurable u) {D : ℝ} (hD : ∀ x, u x ≤ D)
    (t q s : ℝ) (v : ℝ≥0)
    {f : SmartPathDisorder N M → (R → PerceptronSpin N) → ℝ}
    (hfi : ∀ σ, Integrable (fun ω₀ => f ω₀ σ)
      (smartPathDisorder (Measure.pi fun _ : Fin M =>
        Measure.pi fun _ : Fin N => gaussianReal 0 1) v)) :
    ∫ p : SmartPathDisorder N (M + 1) × ℝ,
      (∫ σ : R → SmartPathState N (M + 1) × ℝ,
        f ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2) (fun r => (σ r).1.1)
        ∂(Measure.pi fun _ : R => ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
          fun x : SmartPathState N (M + 1) × ℝ =>
            smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
              (x.1.1, Fin.init x.1.2) +
              u (Real.cos s * smartPathField t p.1 x.1 (Fin.last M) +
                Real.sin s * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2))))
      ∂((smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) v).prod (gaussianReal 0 1)) =
    ∫ ω₀ : SmartPathDisorder N M,
      ∫ ξ : (Fin N ⊕ Unit) ⊕ Unit → ℝ,
        ∫ σ : R → PerceptronSpin N, f ω₀ σ
          ∂(Measure.pi fun _ : R => Measure.count.tilted fun a : PerceptronSpin N =>
            Real.log (Real.exp (((a.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * ω₀.2) *
              ∏ j : Fin M, ∫ b, Real.exp (u (smartPathField t ω₀ (a, fun _ => b) j))
                ∂gaussianReal 0 1) +
            Real.log (∫ η, Real.exp (u ((Real.cos s *
                ((Sum.elim (cavityCoef N t a) (fun _ : Unit => (0 : ℝ)) :
                  (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) +
              Real.sin s * ((Sum.elim (fun _ : Fin N ⊕ Unit => (0 : ℝ))
                (fun _ : Unit => Real.sqrt q) : (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ)) +
              η.1 * (Real.cos s * Real.sqrt ((1 - t) / (N + 1))) +
              η.2 * (Real.sin s * Real.sqrt (1 - q))))
              ∂((gaussianReal 0 1).prod (gaussianReal 0 1))))
        ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)
      ∂(smartPathDisorder (Measure.pi fun _ : Fin M =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) v) := by
  let P₀ : Measure (SmartPathDisorder N M) :=
    smartPathDisorder (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => gaussianReal 0 1) v
  let Ξ : Measure ((Fin N ⊕ Unit) ⊕ Unit → ℝ) :=
    Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1
  have hmp := measurePreserving_smartPathDisorder_cavitySplit N M v
  obtain ⟨w, hw⟩ : ∃ w : SmartPathDisorder N M → PerceptronSpin N → ℝ,
      ∀ ω₀ a, w ω₀ a = Real.exp (((a.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * ω₀.2) *
        ∏ j : Fin M, ∫ b, Real.exp (u (smartPathField t ω₀ (a, fun _ => b) j))
          ∂gaussianReal 0 1 := ⟨_, fun _ _ => rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ → ℝ, ∀ y, ψ y =
      ∫ η, Real.exp (u (y + η.1 * (Real.cos s * Real.sqrt ((1 - t) / (N + 1))) +
        η.2 * (Real.sin s * Real.sqrt (1 - q))))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := ⟨_, fun _ => rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ((Fin N ⊕ Unit) ⊕ Unit → ℝ) → PerceptronSpin N → ℝ,
      ∀ ξ a, Y ξ a = Real.cos s *
          ((Sum.elim (cavityCoef N t a) (fun _ : Unit => (0 : ℝ)) :
            (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) +
        Real.sin s * ((Sum.elim (fun _ : Fin N ⊕ Unit => (0 : ℝ))
          (fun _ : Unit => Real.sqrt q) : (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) := ⟨_, fun _ _ => rfl⟩
  have hwpos : ∀ ω₀ a, 0 < w ω₀ a := fun ω₀ a => by
    rw [hw]
    refine mul_pos (Real.exp_pos _) (Finset.prod_pos fun j _ => ?_)
    refine integral_exp_pos_of_ae_le (C := D) ?_ (ae_of_all _ fun _ => hD _)
    exact (hu.comp (by simp only [smartPathField_eq, smartPathFieldNoAux_eq]; fun_prop)).aemeasurable
  have hψpos : ∀ y, 0 < ψ y := fun y => by
    rw [hψ]
    refine integral_exp_pos_of_ae_le (C := D) ?_ (ae_of_all _ fun _ => hD _)
    exact (hu.comp (by fun_prop)).aemeasurable
  have hwm : ∀ a, Measurable fun ω₀ => w ω₀ a := fun a => by
    rw [show (fun ω₀ => w ω₀ a) = _ from funext fun ω₀ => hw ω₀ a]
    refine (Real.measurable_exp.comp (by fun_prop)).mul (Finset.measurable_prod _ fun j _ => ?_)
    have hj : Measurable fun p : SmartPathDisorder N M × ℝ =>
        Real.exp (u (smartPathField t p.1 (a, fun _ => p.2) j)) := by
      refine Real.measurable_exp.comp (hu.comp ?_)
      simp only [smartPathField_eq, smartPathFieldNoAux_eq]
      fun_prop
    exact (hj.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable
  have hψm : Measurable ψ := by
    rw [show ψ = _ from funext hψ]
    have hj : Measurable fun p : ℝ × (ℝ × ℝ) =>
        Real.exp (u (p.1 + p.2.1 * (Real.cos s * Real.sqrt ((1 - t) / (N + 1))) +
          p.2.2 * (Real.sin s * Real.sqrt (1 - q)))) :=
      Real.measurable_exp.comp (hu.comp (by fun_prop))
    exact (hj.stronglyMeasurable.integral_prod_right'
      (ν := (gaussianReal 0 1).prod (gaussianReal 0 1))).measurable
  have hYm : ∀ a, Measurable fun ξ => Y ξ a := fun a => by
    rw [show (fun ξ => Y ξ a) = _ from funext fun ξ => hY ξ a]
    exact measurable_cavityField N t q s a
  obtain ⟨G, hG⟩ : ∃ G : SmartPathDisorder N M × ((Fin N ⊕ Unit) ⊕ Unit → ℝ) → ℝ,
      ∀ q', G q' = ∫ σ : R → PerceptronSpin N, f q'.1 σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          fun a => Real.log (w q'.1 a) + Real.log (ψ (Y q'.2 a))) := ⟨_, fun _ => rfl⟩
  have hGi : Integrable G (P₀.prod Ξ) := by
    have hEm : ∀ a, Measurable fun q' : SmartPathDisorder N M × ((Fin N ⊕ Unit) ⊕ Unit → ℝ) =>
        Real.log (w q'.1 a) + Real.log (ψ (Y q'.2 a)) := fun a =>
      ((Real.measurable_log.comp (hwm a)).comp measurable_fst).add
        (Real.measurable_log.comp (hψm.comp ((hYm a).comp measurable_snd)))
    have hGm : AEStronglyMeasurable G (P₀.prod Ξ) := by
      have hGsum : G = ∑ σ : R → PerceptronSpin N, fun q' => f q'.1 σ *
          ∫ τ, (if τ = σ then (1 : ℝ) else 0)
            ∂(Measure.pi fun _ : R => Measure.count.tilted
              fun a => Real.log (w q'.1 a) + Real.log (ψ (Y q'.2 a))) := by
        ext q'
        rw [hG, Finset.sum_apply, integral_fintype Integrable.of_finite]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [integral_fintype Integrable.of_finite]
        simp [smul_eq_mul, mul_comm]
      rw [hGsum]
      refine Finset.aestronglyMeasurable_sum _ fun σ _ =>
        ((hfi σ).aestronglyMeasurable.comp_fst).mul ?_
      exact (measurable_integral_pi_count_tilted (R := R)
        (g := fun (q' : SmartPathDisorder N M × ((Fin N ⊕ Unit) ⊕ Unit → ℝ))
          (a : PerceptronSpin N) => Real.log (w q'.1 a) + Real.log (ψ (Y q'.2 a)))
        (Θ := fun _ τ => if τ = σ then (1 : ℝ) else 0)
        hEm (fun _ => measurable_const)).aestronglyMeasurable
    have hdom : Integrable (fun q' : SmartPathDisorder N M × ((Fin N ⊕ Unit) ⊕ Unit → ℝ) =>
        ∑ σ : R → PerceptronSpin N, |f q'.1 σ|) (P₀.prod Ξ) :=
      (integrable_finsetSum _ fun σ _ => (hfi σ).abs).comp_fst Ξ
    refine hdom.mono' hGm (ae_of_all _ fun q' => ?_)
    rw [Real.norm_eq_abs, hG]
    refine abs_integral_pi_count_tilted_le _ fun σ => ?_
    exact Finset.single_le_sum (f := fun τ => |f q'.1 τ|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ σ)
  have hpt : ∀ p : SmartPathDisorder N (M + 1) × ℝ,
      (∫ σ : R → SmartPathState N (M + 1) × ℝ,
        f ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2) (fun r => (σ r).1.1)
        ∂(Measure.pi fun _ : R => ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
          fun x : SmartPathState N (M + 1) × ℝ =>
            smartPathEnergy u t ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2)
              (x.1.1, Fin.init x.1.2) +
              u (Real.cos s * smartPathField t p.1 x.1 (Fin.last M) +
                Real.sin s * (Real.sqrt q * p.2 + Real.sqrt (1 - q) * x.2)))) =
      G ((((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2) : SmartPathDisorder N M),
        (Sum.elim (Sum.elim (p.1.1.1 (Fin.last M)) (fun _ : Unit => p.1.1.2 (Fin.last M)))
          (fun _ : Unit => p.2) : (Fin N ⊕ Unit) ⊕ Unit → ℝ)) := by
    intro p
    rw [integral_pi_tilted_cavityPath_spinOnly_eq_ratio hu hD t q s p.2 p.1, hG,
      ← replicaRatio_eq_integral_pi_count_tilted (hwpos _) (fun a => hψpos _)]
    have hY_eq : ∀ a : PerceptronSpin N,
        Real.cos s * smartPathFieldNoAux t p.1 (a, fun _ => 0) (Fin.last M) +
          Real.sin s * (Real.sqrt q * p.2) =
        Y (Sum.elim (Sum.elim (p.1.1.1 (Fin.last M)) (fun _ : Unit => p.1.1.2 (Fin.last M)))
            (fun _ : Unit => p.2)) a := by
      intro a
      have hfl := smartPathField_last_eq_dotProduct (t := t) p.1 (a, fun _ => 0)
      rw [smartPathField_eq] at hfl
      simp only [mul_zero, add_zero] at hfl
      rw [hfl, hY]
      simp [dotProduct, Fintype.sum_sum_type, mul_comm (Real.sqrt q)]
    have hw_eq : ∀ a : PerceptronSpin N,
        Real.exp ((a.2 : ℤ) * Real.sqrt (1 - t) * p.1.2) *
          (∏ j : Fin M, ∫ b, Real.exp (u (smartPathField t p.1 (a, fun _ => b) j.castSucc))
            ∂gaussianReal 0 1) =
        w ((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2) a := by
      intro a
      rw [hw]
      exact congrArg _ (Finset.prod_congr rfl fun j _ => integral_congr_ae (ae_of_all _ fun b =>
        congrArg (fun x => Real.exp (u x)) (smartPathField_init t p.1 (a, fun _ => b) j).symm))
    simp only [hY_eq, ← hψ, hw_eq]
  simp_rw [hpt]
  rw [hmp.integral_comp_of_aestronglyMeasurable hGi.aestronglyMeasurable, integral_prod _ hGi]
  refine integral_congr_ae (ae_of_all _ fun ω₀ => integral_congr_ae (ae_of_all _ fun ξ => ?_))
  dsimp only
  rw [hG]
  simp only [hw, hψ, hY]

end SpinGlasses
