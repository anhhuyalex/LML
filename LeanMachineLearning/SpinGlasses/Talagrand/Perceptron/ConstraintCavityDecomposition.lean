/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathBounds

/-!
# Removing the last constraint of the smart path

Talagrand Section 2.3, (2.30)--(2.32). The system has `M + 1` constraints and `N + 1` spins. The
removed constraint is `Fin.last M`, the old one is the restriction by `Fin.init` of the disorder
rows `(g, a)` and of the auxiliary vector `ξ`; the old energy is the smart-path energy with `M`
constraints (2.30). The old energy does not depend on `ξ_M`, but the auxiliary coordinate `ξ_M`
stays in the base measure, as in the book's definition (2.31) of `⟨·⟩_{t,∼}`.

* `smartPathEnergy_eq_init_add`: `-H_{N,M,t} = -H_{N,M-1,t} + u(S_{M,t})`;
* `integral_pi_tilted_smartPathEnergy_eq_div`: the identity (2.32) for the replica average of an
  arbitrary function, as a quotient of old-system averages (any finite base law);
* `integral_exp_smartPathEnergy_eq_mul`: the normalizer identity `Z = Z_∼ ⟨exp u(S_{M,t})⟩_{t,∼}`,
  and `integral_pi_mul_exp_smartPathEnergy_eq_mul` the numerator identity;
* positivity of the old normalizer and of `⟨exp u(S_{M,t})⟩_{t,∼}`.

Only measurability of `u` and an upper bound `u ≤ D` are used (the bounded potential makes the
Gibbs weight integrable at every fixed disorder, including when the last field is unbounded).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

variable {N M : ℕ}

/-- The field of the old system at constraint `k` is the field of the full system at
`k.castSucc`. -/
theorem smartPathField_init (t : ℝ) (ω : SmartPathDisorder N (M + 1))
    (x : SmartPathState N (M + 1)) (k : Fin M) :
    smartPathField t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2) k =
      smartPathField t ω x k.castSucc := rfl

/-- **The energy splits into the old energy and the last constraint** (2.30). The old energy
is the smart-path energy with `M` constraints at the restricted disorder and restricted state. -/
theorem smartPathEnergy_eq_init_add (u : ℝ → ℝ) (t : ℝ) (ω : SmartPathDisorder N (M + 1))
    (x : SmartPathState N (M + 1)) :
    smartPathEnergy u t ω x =
      smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2) +
        u (smartPathField t ω x (Fin.last M)) := by
  rw [smartPathEnergy_eq, smartPathEnergy_eq, Fin.sum_univ_castSucc]
  simp only [smartPathField_init]
  ring

/-- The restriction of the state to the old coordinates is measurable. -/
theorem measurable_smartPathState_init :
    Measurable fun x : SmartPathState N (M + 1) => ((x.1, Fin.init x.2) : SmartPathState N M) := by
  fun_prop

/-- The old energy (2.30) as a function of the full state is measurable. -/
theorem measurable_smartPathEnergy_init {u : ℝ → ℝ} (hu : Measurable u) (t : ℝ)
    (ω : SmartPathDisorder N (M + 1)) :
    Measurable fun x : SmartPathState N (M + 1) =>
      smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2) :=
  (measurable_smartPathEnergy_slice hu t _).comp measurable_smartPathState_init

/-- The old energy is bounded above for a potential bounded above. -/
theorem smartPathEnergy_init_le {u : ℝ → ℝ} {D : ℝ} (hD : ∀ x, u x ≤ D) (t : ℝ)
    (ω : SmartPathDisorder N (M + 1)) (x : SmartPathState N (M + 1)) :
    smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2) ≤
      M * D + Real.sqrt (1 - t) * |ω.2| :=
  perceptron_smart_path_energy_le hD t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) _

section Cavity

variable {μ : Measure (SmartPathState N (M + 1))} [IsFiniteMeasure μ] {u : ℝ → ℝ}
  {D : ℝ} (hu : Measurable u) (hD : ∀ x, u x ≤ D) (t : ℝ) (ω : SmartPathDisorder N (M + 1))

include hu hD in
/-- The Gibbs weight of the old system is integrable. -/
theorem integrable_exp_smartPathEnergy_init :
    Integrable (fun x : SmartPathState N (M + 1) => Real.exp
      (smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2))) μ :=
  integrable_exp_of_ae_le (C := M * D + Real.sqrt (1 - t) * |ω.2|)
    (measurable_smartPathEnergy_init hu t ω).aemeasurable
    (Filter.Eventually.of_forall (smartPathEnergy_init_le hD t ω))

include hu hD in
/-- The partition function `Z_∼` of the old system is positive. -/
theorem integral_exp_smartPathEnergy_init_pos [NeZero μ] :
    0 < ∫ x, Real.exp
      (smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2)) ∂μ :=
  integral_exp_pos_of_ae_le (C := M * D + Real.sqrt (1 - t) * |ω.2|)
    (measurable_smartPathEnergy_init hu t ω).aemeasurable
    (Filter.Eventually.of_forall (smartPathEnergy_init_le hD t ω))

include hu hD in
/-- The Gibbs law of the old system is a probability measure. -/
theorem isProbabilityMeasure_tilted_smartPathEnergy_init [NeZero μ] :
    IsProbabilityMeasure (μ.tilted fun x : SmartPathState N (M + 1) =>
      smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2)) :=
  isProbabilityMeasure_tilted_of_ae_le (C := M * D + Real.sqrt (1 - t) * |ω.2|)
    (measurable_smartPathEnergy_init hu t ω).aemeasurable
    (Filter.Eventually.of_forall (smartPathEnergy_init_le hD t ω))

include hu hD in
/-- **`⟨exp u(S_{M,t})⟩_{t,∼}` is positive.** -/
theorem integral_exp_lastField_tilted_pos [NeZero μ] :
    0 < ∫ x, Real.exp (u (smartPathField t ω x (Fin.last M))) ∂(μ.tilted fun x :
      SmartPathState N (M + 1) =>
        smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2)) := by
  have := isProbabilityMeasure_tilted_smartPathEnergy_init (μ := μ) hu hD t ω
  refine integral_exp_pos_of_ae_le (C := D) ?_ (Filter.Eventually.of_forall fun x => hD _)
  exact (hu.comp (Measurable.of_uncurry_left (f := fun ω x => smartPathField t ω x (Fin.last M))
    (measurable_smartPathField t (Fin.last M)))).aemeasurable

include hu hD in
/-- **Normalizer identity** `Z = Z_∼ ⟨exp u(S_{M,t})⟩_{t,∼}` (below (2.31)). -/
theorem integral_exp_smartPathEnergy_eq_mul [NeZero μ] :
    ∫ x, Real.exp (smartPathEnergy u t ω x) ∂μ =
      (∫ x, Real.exp
          (smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2)) ∂μ) *
        ∫ x, Real.exp (u (smartPathField t ω x (Fin.last M))) ∂(μ.tilted fun x :
          SmartPathState N (M + 1) =>
            smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2)) := by
  have hZ := (integral_exp_smartPathEnergy_init_pos (μ := μ) hu hD t ω).ne'
  rw [integral_tilted_eq_div, mul_div_cancel₀ _ hZ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smartPathEnergy_eq_init_add u t ω x, Real.exp_add, mul_comm]

include hu hD in
/-- **Replica numerator identity** below (2.32): the numerator of the `R`-replica average at
the full system is `Z_∼ ^ |R|` times the old-system average of `f exp ∑ u(S_{M,t}^ℓ)`. -/
theorem integral_pi_mul_exp_smartPathEnergy_eq_mul [NeZero μ] {R : Type*} [Fintype R]
    (Y : (R → SmartPathState N (M + 1)) → ℝ) :
    ∫ σ, Y σ * Real.exp (∑ r, smartPathEnergy u t ω (σ r)) ∂(Measure.pi fun _ : R => μ) =
      (∫ x, Real.exp
          (smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2)) ∂μ) ^
          Fintype.card R *
        ∫ σ, Y σ * Real.exp (∑ r, u (smartPathField t ω (σ r) (Fin.last M)))
          ∂(Measure.pi fun _ : R => μ.tilted fun x : SmartPathState N (M + 1) =>
            smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2)) := by
  have hZ := (integral_exp_smartPathEnergy_init_pos (μ := μ) hu hD t ω).ne'
  have := integral_pi_mul_exp_sum_add_eq (μ := μ) (ι := R)
    (E := fun x : SmartPathState N (M + 1) =>
      smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2))
    (V := fun x => u (smartPathField t ω x (Fin.last M))) hZ Y
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  simp only [smartPathEnergy_eq_init_add u t ω]

include hu hD in
/-- **The identity (2.32).** A replica average of an arbitrary function `Y` under the Gibbs law
of the full system is the old-system average of `Y exp ∑ u(S_{M,t}^ℓ)` divided by the `|R|`-th power
of `⟨exp u(S_{M,t})⟩_{t,∼}`. The denominator is positive. -/
theorem integral_pi_tilted_smartPathEnergy_eq_div {R : Type*} [Fintype R]
    (Y : (R → SmartPathState N (M + 1)) → ℝ) :
    ∫ σ, Y σ ∂(Measure.pi fun _ : R => μ.tilted (smartPathEnergy u t ω)) =
      (∫ σ, Y σ * Real.exp (∑ r, u (smartPathField t ω (σ r) (Fin.last M)))
          ∂(Measure.pi fun _ : R => μ.tilted fun x : SmartPathState N (M + 1) =>
            smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2))) /
        (∫ x, Real.exp (u (smartPathField t ω x (Fin.last M))) ∂(μ.tilted fun x :
          SmartPathState N (M + 1) =>
            smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2))) ^
          Fintype.card R := by
  have h := integral_pi_tilted_add_eq_div (μ := μ) (ι := R)
    (integrable_exp_smartPathEnergy_init (μ := μ) hu hD t ω)
    (V := fun x => u (smartPathField t ω x (Fin.last M))) Y
  have e : (fun x : SmartPathState N (M + 1) => smartPathEnergy u t
      ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2) +
        u (smartPathField t ω x (Fin.last M))) = smartPathEnergy u t ω :=
    funext fun x => (smartPathEnergy_eq_init_add u t ω x).symm
  rw [e] at h
  exact h

end Cavity

end SpinGlasses
