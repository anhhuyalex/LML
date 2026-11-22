/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.PiSnoc
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
open scoped NNReal

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

/-- The restriction of the disorder to the old constraints is measurable. -/
theorem measurable_smartPathDisorder_init :
    Measurable fun ω : SmartPathDisorder N (M + 1) =>
      ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) := by
  fun_prop

/-- The old energy (2.30) is jointly measurable in the disorder and the full state. -/
theorem measurable_smartPathEnergy_init_joint {u : ℝ → ℝ} (hu : Measurable u) (t : ℝ) :
    Measurable fun r : SmartPathDisorder N (M + 1) × SmartPathState N (M + 1) =>
      smartPathEnergy u t ((Fin.init r.1.1.1, Fin.init r.1.1.2), r.1.2)
        (r.2.1, Fin.init r.2.2) := by
  have h1 : Measurable fun r : SmartPathDisorder N (M + 1) × SmartPathState N (M + 1) =>
      (((Fin.init r.1.1.1, Fin.init r.1.1.2), r.1.2) : SmartPathDisorder N M) :=
    measurable_smartPathDisorder_init.comp measurable_fst
  have h2 : Measurable fun r : SmartPathDisorder N (M + 1) × SmartPathState N (M + 1) =>
      ((r.2.1, Fin.init r.2.2) : SmartPathState N M) :=
    measurable_smartPathState_init.comp measurable_snd
  have h3 := measurable_smartPathEnergy (N := N) (M := M) hu t
  exact (h3.comp (h1.prodMk h2) : _)

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
  integral_exp_pos (integrable_exp_smartPathEnergy_init (μ := μ) hu hD t ω)

include hu hD in
/-- The Gibbs law of the old system is a probability measure. -/
theorem isProbabilityMeasure_tilted_smartPathEnergy_init [NeZero μ] :
    IsProbabilityMeasure (μ.tilted fun x : SmartPathState N (M + 1) =>
      smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2)) :=
  isProbabilityMeasure_tilted (integrable_exp_smartPathEnergy_init (μ := μ) hu hD t ω)

include hu hD in
/-- **`⟨exp u(S_{M,t})⟩_{t,∼}` is positive.** -/
theorem integral_exp_lastField_tilted_pos [NeZero μ] :
    0 < ∫ x, Real.exp (u (smartPathField t ω x (Fin.last M))) ∂(μ.tilted fun x :
      SmartPathState N (M + 1) =>
        smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2)) := by
  have := isProbabilityMeasure_tilted_smartPathEnergy_init (μ := μ) hu hD t ω
  refine integral_exp_pos_of_ae_le (C := D) ?_ (Filter.Eventually.of_forall fun x => hD _)
  exact (hu.comp (measurable_smartPathField_slice t ω (Fin.last M))).aemeasurable

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
  rw [integral_exp_tilted, mul_div_cancel₀ _ hZ]
  simp only [Pi.add_apply, ← smartPathEnergy_eq_init_add u t ω]

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
  simpa only [← smartPathEnergy_eq_init_add u t ω] using this

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
  simpa only [← smartPathEnergy_eq_init_add u t ω] using h

end Cavity

section MeasureSplit

/-- Measurable equivalence splitting `SmartPathState N (M + 1)` into the old configuration
`SmartPathState N M` and the last auxiliary Gaussian `ξ_M`. -/
def smartPathStateSplit (N M : ℕ) : SmartPathState N (M + 1) ≃ᵐ SmartPathState N M × ℝ :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (PerceptronSpin N))
    (MeasurableEquiv.finSuccProd ℝ M)).trans (MeasurableEquiv.prodAssoc).symm

theorem smartPathStateSplit_apply (x : SmartPathState N (M + 1)) :
    smartPathStateSplit N M x = ((x.1, Fin.init x.2), x.2 (Fin.last M)) := by
  simp [smartPathStateSplit, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_prodCongr,
    MeasurableEquiv.coe_refl, Fin.init_def]

theorem smartPathStateSplit_symm_apply (q : SmartPathState N M × ℝ) :
    (smartPathStateSplit N M).symm q = (q.1.1, Fin.snoc q.1.2 q.2) := by
  apply (smartPathStateSplit N M).injective
  rw [MeasurableEquiv.apply_symm_apply, smartPathStateSplit_apply]
  simp [Fin.init_snoc, Fin.snoc_last]

/-- Splitting off the last auxiliary coordinate preserves the smart-path base measure. -/
theorem measurePreserving_smartPathStateSplit (N M : ℕ) :
    MeasurePreserving ⇑(smartPathStateSplit N M)
      (smartPathBase N (M + 1)) ((smartPathBase N M).prod (gaussianReal 0 1)) := by
  rw [smartPathBase_eq, smartPathBase_eq]
  exact (measurePreserving_prodAssoc _ _ _).symm.comp
    ((MeasurePreserving.id _).prod (measurePreserving_finSuccProd _ M))

/-- **Measure-preserving split of the concrete `(M + 1)`-constraint disorder.** Under the i.i.d.
Gaussian law of the old rows, the couplings `a` and the last field `Y ∼ 𝒩(0, v)`, splitting off the
removed row `(g_M, a_M)` maps `SmartPathDisorder N (M + 1)` to the product of the `M`-constraint
disorder law (including `Y`) and the independent standard Gaussian block `(g_M, a_M)` indexed by
`Fin N ⊕ Unit`. -/
theorem measurePreserving_smartPathDisorder_lastSplit (N M : ℕ) (v : ℝ≥0) :
    MeasurePreserving
      (fun ω : SmartPathDisorder N (M + 1) =>
        ((((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) : SmartPathDisorder N M),
          (Sum.elim (ω.1.1 (Fin.last M)) (fun _ : Unit => ω.1.2 (Fin.last M)) :
            Fin N ⊕ Unit → ℝ)))
      (smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) v)
      ((smartPathDisorder (Measure.pi fun _ : Fin M =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) v).prod
        (Measure.pi fun _ : Fin N ⊕ Unit => gaussianReal 0 1)) := by
  let γ : Measure ℝ := gaussianReal 0 1
  let G₀ : Measure (Fin M → Fin N → ℝ) := Measure.pi fun _ => Measure.pi fun _ => γ
  let gM : Measure (Fin N → ℝ) := Measure.pi fun _ => γ
  let A₀ : Measure (Fin M → ℝ) := Measure.pi fun _ => γ
  let Ym : Measure ℝ := gaussianReal 0 v
  have hg := measurePreserving_finSuccProd gM M
  have ha := measurePreserving_finSuccProd γ M
  have hunit := (measurePreserving_funUnique γ Unit).symm
  have hsum := (measurePreserving_sumPiEquivProdPi_symm (X := fun _ : Fin N ⊕ Unit => ℝ)
    (fun _ => γ)).comp ((MeasurePreserving.id gM).prod hunit)
  have step1 : MeasurePreserving
      (Prod.map (Prod.map (MeasurableEquiv.finSuccProd (Fin N → ℝ) M)
        (MeasurableEquiv.finSuccProd ℝ M)) id)
      (smartPathDisorder (Measure.pi fun _ : Fin (M + 1) => gM) v)
      (((G₀.prod gM).prod (A₀.prod γ)).prod Ym) := by
    rw [smartPathDisorder_eq]
    exact (hg.prod ha).prod (MeasurePreserving.id Ym)
  have step2 := (measurePreserving_prodProdProdComm G₀ gM A₀ γ).prod (MeasurePreserving.id Ym)
  have step3 := measurePreserving_prodAssoc (G₀.prod A₀) (gM.prod γ) Ym
  have step4 := (MeasurePreserving.id (G₀.prod A₀)).prod
    (Measure.measurePreserving_swap (μ := gM.prod γ) (ν := Ym))
  have step5 := (measurePreserving_prodAssoc (G₀.prod A₀) Ym (gM.prod γ)).symm
  have step6 := (MeasurePreserving.id ((G₀.prod A₀).prod Ym)).prod hsum
  have full := step6.comp (step5.comp (step4.comp (step3.comp (step2.comp step1))))
  rw [smartPathDisorder_eq (Measure.pi fun _ : Fin M => gM) v]
  convert full using 1
  ext ω : 1
  refine Prod.ext ?_ ?_
  · simp [MeasurableEquiv.prodAssoc, Fin.init_def]
  · ext x
    rcases x with i | _ <;>
      simp [MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
        Equiv.sumPiEquivProdPi_symm_apply]

/-- **Measure-preserving split of the cavity disorder `(ω, z)`.** Under the concrete i.i.d.
disorder law for `M + 1` constraints paired with the independent shared Gaussian `z ∼ 𝒩(0, 1)`,
splitting `(ω, z)` into the old system `ω_{<M}` (including `Y`) and the independent Gaussian block
`((g_M, a_M), z)` indexed by `(Fin N ⊕ Unit) ⊕ Unit` is measure-preserving. -/
theorem measurePreserving_smartPathDisorder_cavitySplit (N M : ℕ) (v : ℝ≥0) :
    MeasurePreserving
      (fun p : SmartPathDisorder N (M + 1) × ℝ =>
        ((((Fin.init p.1.1.1, Fin.init p.1.1.2), p.1.2) : SmartPathDisorder N M),
          (Sum.elim (Sum.elim (p.1.1.1 (Fin.last M)) (fun _ : Unit => p.1.1.2 (Fin.last M)))
            (fun _ : Unit => p.2) : (Fin N ⊕ Unit) ⊕ Unit → ℝ)))
      ((smartPathDisorder (Measure.pi fun _ : Fin (M + 1) =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) v).prod (gaussianReal 0 1))
      ((smartPathDisorder (Measure.pi fun _ : Fin M =>
          Measure.pi fun _ : Fin N => gaussianReal 0 1) v).prod
        (Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)) := by
  let γ : Measure ℝ := gaussianReal 0 1
  let P₀ : Measure (SmartPathDisorder N M) :=
    smartPathDisorder (Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin N => γ) v
  let K₀ : Measure (Fin N ⊕ Unit → ℝ) := Measure.pi fun _ => γ
  have h1 := (measurePreserving_smartPathDisorder_lastSplit N M v).prod (MeasurePreserving.id γ)
  have h2 := measurePreserving_prodAssoc P₀ K₀ γ
  have hunit := (measurePreserving_funUnique γ Unit).symm
  have hsum := (measurePreserving_sumPiEquivProdPi_symm
    (X := fun _ : (Fin N ⊕ Unit) ⊕ Unit => ℝ) (fun _ => γ)).comp
      ((MeasurePreserving.id K₀).prod hunit)
  have h3 := (MeasurePreserving.id P₀).prod hsum
  have full := h3.comp (h2.comp h1)
  convert full using 1
  ext p : 1
  refine Prod.ext rfl ?_
  ext x
  rcases x with (i | _) | _ <;>
    simp [MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
      Equiv.sumPiEquivProdPi_symm_apply]

end MeasureSplit

end SpinGlasses
