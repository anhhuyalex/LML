/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Initialization
public import LeanMachineLearning.Optimization.Renormalization.ParameterizedMLP

/-!
# Independent Gaussian initialization of a fixed MLP shape

This file upgrades the single-layer initialization law to an explicit joint law on
`MLPShape.Params`. It is the rigorous meaning of the Chapter 2 density `p(θ)`: parameters in
different layers, as well as scalar coordinates within each layer, are independent.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace NeuralNetwork

universe u v

namespace MLPShape

/-- One pair of Gaussian initialization hyperparameters for every affine layer of a fixed shape. -/
def Hyperparams {m n : ℕ} : MLPShape m n → Type
  | .output => InitHyperparams
  | .hidden tail => InitHyperparams × tail.Hyperparams

/-- The joint independent Gaussian law of every parameter in a fixed MLP.

The outer product at a hidden constructor makes the first layer independent of all later layers;
`layerGaussianInit` supplies the independent scalar coordinates inside that layer. -/
def gaussianInit {m n : ℕ} : (S : MLPShape m n) → S.Hyperparams → Measure S.Params
  | .output, p => layerGaussianInit p (Fin m) (Fin n)
  | .hidden (k := k) tail, p =>
      (layerGaussianInit p.1 (Fin m) (Fin k)).prod (tail.gaussianInit p.2)

-- The law at a hidden constructor is the product of the first-layer Gaussian law with the tail
-- law.  The first factor is a probability measure by `isProbabilityMeasure_layerGaussianInit`,
-- so the product is a probability measure exactly when the tail law is one; that hypothesis is
-- supplied by the induction hypothesis in `isProbabilityMeasure_gaussianInit`.
private lemma isProbabilityMeasure_gaussianInit_hidden {k n m : ℕ} (p₁ : InitHyperparams)
    (tail : MLPShape k n) (p₂ : tail.Hyperparams)
    (htail : IsProbabilityMeasure (tail.gaussianInit p₂)) :
    IsProbabilityMeasure ((layerGaussianInit p₁ (Fin m) (Fin k)).prod (tail.gaussianInit p₂)) :=
  inferInstance

/-- Every full-network Gaussian initialization is a probability measure.

Informal proof: induct on the architecture. The output case is
`isProbabilityMeasure_layerGaussianInit`. At a hidden constructor, the first-layer law and the
induction-hypothesis law for the tail are probability measures, and their product is again a
probability measure. See Mathlib's product-measure API:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/Prod/Basic.html>. -/
theorem isProbabilityMeasure_gaussianInit {m n : ℕ} (S : MLPShape m n)
    (p : S.Hyperparams) : IsProbabilityMeasure (S.gaussianInit p) := by
  induction S with
  | output => exact isProbabilityMeasure_layerGaussianInit p _ _
  | hidden tail ih => exact isProbabilityMeasure_gaussianInit_hidden p.1 tail p.2 (ih p.2)

noncomputable instance instIsProbabilityMeasureGaussianInit {m n : ℕ} (S : MLPShape m n)
    (p : S.Hyperparams) : IsProbabilityMeasure (S.gaussianInit p) :=
  S.isProbabilityMeasure_gaussianInit p

/-- A single index type for every scalar weight and bias in every layer of a fixed MLP. -/
def Coordinate {m n : ℕ} : MLPShape m n → Type
  | .output => LayerCoordinate (Fin m) (Fin n)
  | .hidden (k := k) tail => LayerCoordinate (Fin m) (Fin k) ⊕ tail.Coordinate

/-- The scalar-coordinate type of a finite MLP shape is finite. -/
private instance instFintypeCoordinate {m n : ℕ} (S : MLPShape m n) : Fintype S.Coordinate := by
  induction S with
  | output =>
      simp only [Coordinate]
      infer_instance
  | hidden tail ih =>
      simp only [Coordinate]
      letI : Fintype tail.Coordinate := ih
      infer_instance

/-- Read one scalar parameter from the structured parameter space of a fixed MLP. -/
def coordinate {m n : ℕ} (S : MLPShape m n) (c : S.Coordinate) (θ : S.Params) : ℝ :=
  match S with
  | .output => layerCoordinate c θ
  | .hidden tail =>
      match c with
      | Sum.inl c => layerCoordinate c θ.1
      | Sum.inr c => tail.coordinate c θ.2

/-- Variance assigned to a scalar coordinate by a full-network initialization. -/
def coordinateVariance {m n : ℕ} (S : MLPShape m n)
    (p : S.Hyperparams) (c : S.Coordinate) : ℝ≥0 :=
  match S with
  | .output =>
      match c with
      | Sum.inl _ => scaledWeightVariance p (Fin m)
      | Sum.inr _ => p.biasVariance
  | .hidden tail =>
      match c with
      | Sum.inl (Sum.inl _) => scaledWeightVariance p.1 (Fin m)
      | Sum.inl (Sum.inr _) => p.1.biasVariance
      | Sum.inr c => tail.coordinateVariance p.2 c

/-- A flattened scalar coordinate of one layer has the corresponding single-layer Gaussian law. -/
private theorem map_layerCoordinate_layerGaussianInit (p : InitHyperparams)
    (ι : Type u) (κ : Type v) [Fintype ι] [Fintype κ]
    (c : LayerCoordinate ι κ) :
    Measure.map (fun q : LayerParams ι κ => layerCoordinate c q) (layerGaussianInit p ι κ) =
      gaussianReal 0 (match c with
        | Sum.inl _ => scaledWeightVariance p ι
        | Sum.inr _ => p.biasVariance) := by
  cases c with
  | inl ji =>
      simpa [layerCoordinate] using map_weight_layerGaussianInit p ι κ ji.1 ji.2
  | inr j =>
      simpa [layerCoordinate] using map_bias_layerGaussianInit p ι κ j

/-- Layer-coordinate evaluation is measurable. -/
private theorem measurable_layerCoordinate' {ι : Type u} {κ : Type v}
    (c : LayerCoordinate ι κ) :
    Measurable (fun q : LayerParams ι κ => layerCoordinate c q) :=
  Sum.rec (fun ji => (measurable_pi_apply ji.2).comp ((measurable_pi_apply ji.1).comp measurable_fst))
    (fun j => (measurable_pi_apply j).comp measurable_snd) c

/-- Reading any scalar coordinate of an MLP parameter tuple is measurable. -/
private theorem measurable_coordinate {m n : ℕ} (S : MLPShape m n) (c : S.Coordinate) :
    Measurable (S.coordinate c) := by
  induction S with
  | output => exact measurable_layerCoordinate' c
  | hidden tail ih =>
      exact Sum.rec (fun c => (measurable_layerCoordinate' c).comp measurable_fst)
        (fun c => (ih c).comp measurable_snd) c

/-- Output-layer case of `map_coordinate_gaussianInit`.

Informal proof: after unfolding `coordinate`, `gaussianInit`, and `coordinateVariance`, this is
exactly the single-layer marginal lemmas `map_weight_layerGaussianInit` and
`map_bias_layerGaussianInit`. -/
private theorem map_coordinate_gaussianInit_output {m n : ℕ}
    (p : (MLPShape.output : MLPShape m n).Hyperparams)
    (c : (MLPShape.output : MLPShape m n).Coordinate) :
    Measure.map ((MLPShape.output : MLPShape m n).coordinate c)
        ((MLPShape.output : MLPShape m n).gaussianInit p) =
      gaussianReal 0 ((MLPShape.output : MLPShape m n).coordinateVariance p c) := by
  cases c with
  | inl ji =>
      simpa [coordinate, gaussianInit, coordinateVariance, layerCoordinate, Params] using
        map_weight_layerGaussianInit p (Fin m) (Fin n) ji.1 ji.2
  | inr j =>
      simpa [coordinate, gaussianInit, coordinateVariance, layerCoordinate, Params] using
        map_bias_layerGaussianInit p (Fin m) (Fin n) j

/-- Hidden-layer induction step for `map_coordinate_gaussianInit`.

Informal proof: split `c`. If `c` is in the first layer, rewrite the coordinate as a layer
coordinate composed with `Prod.fst`; `Measure.map_map` and `Measure.map_fst_prod` reduce the
marginal to the first-layer law because the tail law is a probability measure, then
`map_weight_layerGaussianInit`/`map_bias_layerGaussianInit` finish. If `c` is in the tail, use
`Prod.snd`, `Measure.map_snd_prod`, the probability-measure instance for the first-layer law, and
the induction hypothesis. This is the standard product-measure marginal argument documented at
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/Prod/Basic.html>. -/
private theorem map_coordinate_gaussianInit_hidden {m n k : ℕ} (tail : MLPShape k n)
    (ih : ∀ (p : tail.Hyperparams) (c : tail.Coordinate),
      Measure.map (tail.coordinate c) (tail.gaussianInit p) =
        gaussianReal 0 (tail.coordinateVariance p c))
    (p : (MLPShape.hidden tail : MLPShape m n).Hyperparams)
    (c : (MLPShape.hidden tail : MLPShape m n).Coordinate) :
    Measure.map ((MLPShape.hidden tail : MLPShape m n).coordinate c)
        ((MLPShape.hidden tail : MLPShape m n).gaussianInit p) =
      gaussianReal 0 ((MLPShape.hidden tail : MLPShape m n).coordinateVariance p c) := by
  cases c with
  | inl ji =>
      cases ji with
      | inl jiW =>
          simp only [coordinate, gaussianInit, coordinateVariance, layerCoordinate, Params]
          rw [show (fun q : LayerParams (Fin m) (Fin k) × tail.Params => q.1.1 jiW.1 jiW.2) =
              layerCoordinate (Sum.inl jiW) ∘ Prod.fst from rfl,
            ← Measure.map_map (measurable_layerCoordinate' (Sum.inl jiW)) measurable_fst]
          simpa [layerCoordinate, Measure.map_fst_prod, measure_univ, one_smul] using
            map_weight_layerGaussianInit p.1 (Fin m) (Fin k) jiW.1 jiW.2
      | inr jB =>
          simp only [coordinate, gaussianInit, coordinateVariance, layerCoordinate, Params]
          rw [show (fun q : LayerParams (Fin m) (Fin k) × tail.Params => q.1.2 jB) =
              layerCoordinate (Sum.inr jB) ∘ Prod.fst from rfl,
            ← Measure.map_map (measurable_layerCoordinate' (Sum.inr jB)) measurable_fst]
          simpa [layerCoordinate, Measure.map_fst_prod, measure_univ, one_smul] using
            map_bias_layerGaussianInit p.1 (Fin m) (Fin k) jB
  | inr c =>
      simp only [coordinate, gaussianInit, coordinateVariance, Params]
      rw [show (fun q : LayerParams (Fin m) (Fin k) × tail.Params => tail.coordinate c q.2) =
          tail.coordinate c ∘ Prod.snd from rfl,
        ← Measure.map_map (measurable_coordinate tail c) measurable_snd]
      simpa [Measure.map_snd_prod, measure_univ, one_smul] using ih p.2 c

/-- Every scalar parameter of a fixed MLP has its prescribed centered Gaussian marginal law.

Informal proof: induct on the shape and on whether the coordinate belongs to the first layer or
the tail. In the first case, project the first factor of the product and apply
`map_weight_layerGaussianInit` or `map_bias_layerGaussianInit`; in the second case, project the
tail factor and use the induction hypothesis. See Mathlib's product projection theorems:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/Prod/Basic.html>. -/
theorem map_coordinate_gaussianInit {m n : ℕ} (S : MLPShape m n)
    (p : S.Hyperparams) (c : S.Coordinate) :
    Measure.map (S.coordinate c) (S.gaussianInit p) =
      gaussianReal 0 (S.coordinateVariance p c) := by
  induction S with
  | output => exact map_coordinate_gaussianInit_output p c
  | hidden tail ih => exact map_coordinate_gaussianInit_hidden tail ih p c

-- The joint law of an independent family is the product of its marginals.  Used twice below to
-- compute the projected laws of the two families in `iIndepFun_sum_prod_real`.
private lemma iIndepFun_law_eq_pi {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (f : ι → Ω → ℝ) (hfmeas : ∀ i, Measurable (f i))
    (hf : iIndepFun f μ) :
    μ.map (fun x : Ω => fun i : ι => f i x) = Measure.pi (fun i : ι => μ.map (f i)) :=
  hf.map_fun_eq_pi_map (fun i => (hfmeas i).aemeasurable)

-- The first-factor marginal of a function depending only on the first coordinate is the law of
-- that function under the first factor (the second factor is a probability measure).
private lemma map_prod_fst_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure ν] (g : Ω → ℝ)
    (hg : Measurable g) :
    (μ.prod ν).map (fun ω : Ω × Ω' => g ω.1) = μ.map g := by
  rw [show (fun ω : Ω × Ω' => g ω.1) = g ∘ Prod.fst from rfl,
    ← Measure.map_map hg measurable_fst,
    measurePreserving_fst.map_eq]

-- The second-factor marginal of a function depending only on the second coordinate is the law of
-- that function under the second factor (the first factor is a probability measure).
private lemma map_prod_snd_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [SFinite ν] (g : Ω' → ℝ)
    (hg : Measurable g) :
    (μ.prod ν).map (fun ω : Ω × Ω' => g ω.2) = ν.map g := by
  rw [show (fun ω : Ω × Ω' => g ω.2) = g ∘ Prod.snd from rfl,
    ← Measure.map_map hg measurable_snd,
    measurePreserving_snd.map_eq]

-- The combined tuple law on `ι ⊕ κ`, transported through the sum-Pi equivalence, is the product
-- of the two projected laws.  This is the "left side" of the injectivity argument in
-- `iIndepFun_sum_prod_real`.
private lemma sumPi_tuple_map_prod_map {Ω Ω' ι κ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω')
    [SFinite μ] [SFinite ν] (f : ι → Ω → ℝ) (g : κ → Ω' → ℝ)
    (hfmeas : ∀ i, Measurable (f i)) (hgmeas : ∀ j, Measurable (g j)) :
    ((μ.prod ν).map (fun ω : Ω × Ω' => fun c : ι ⊕ κ =>
        Sum.elim (fun i => f i ω.1) (fun j => g j ω.2) c)).map
        (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ κ => ℝ)) =
      (μ.map (fun x : Ω => fun i : ι => f i x)).prod
        (ν.map (fun y : Ω' => fun j : κ => g j y)) := by
  have hF : Measurable (fun ω : Ω × Ω' => fun c : ι ⊕ κ =>
      Sum.elim (fun i => f i ω.1) (fun j => g j ω.2) c) :=
    measurable_pi_lambda _ (Sum.rec (fun i => (hfmeas i).comp measurable_fst)
      (fun j => (hgmeas j).comp measurable_snd))
  have hA : Measurable (fun x : Ω => fun i : ι => f i x) :=
    measurable_pi_lambda _ hfmeas
  have hB : Measurable (fun y : Ω' => fun j : κ => g j y) :=
    measurable_pi_lambda _ hgmeas
  rw [Measure.map_map (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ κ => ℝ)).measurable hF]
  exact (Measure.map_prod_map μ ν hA hB).symm

/-- Combine two independent finite families living on the two factors of a product probability
space into one independent family indexed by the disjoint union.

Informal proof: use `iIndepFun_iff_map_fun_eq_pi_map`. The tuple map indexed by `ι ⊕ κ`
becomes, under `MeasurableEquiv.sumPiEquivProdPi`, the pair of tuple maps indexed by `ι` and by
`κ`. The two tuple maps are independent by `indepFun_prod`, and their laws are finite product
measures by `hf.map_fun_eq_pi_map` and `hg.map_fun_eq_pi_map`; projection marginals are normalized
by `Measure.map_fst_prod` and `Measure.map_snd_prod`. This is the standard product-measure
factorization characterization of independence; see Mathlib's independence API:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html>. -/
private lemma iIndepFun_sum_prod_real {Ω Ω' ι κ : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [Finite ι] [Finite κ] (μ : Measure Ω) (ν : Measure Ω')
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (f : ι → Ω → ℝ) (g : κ → Ω' → ℝ)
    (hfmeas : ∀ i, Measurable (f i)) (hgmeas : ∀ j, Measurable (g j))
    (hf : iIndepFun f μ) (hg : iIndepFun g ν) :
    iIndepFun
      (fun c : ι ⊕ κ => fun ω : Ω × Ω' =>
        Sum.elim (fun i => f i ω.1) (fun j => g j ω.2) c)
      (μ.prod ν) := by
  have : Fintype ι := Fintype.ofFinite ι
  have : Fintype κ := Fintype.ofFinite κ
  let μπ : Measure (Ω × Ω') := μ.prod ν
  let F : Ω × Ω' → (ι ⊕ κ → ℝ) := fun ω c =>
    Sum.elim (fun i => f i ω.1) (fun j => g j ω.2) c
  let A : Ω → ι → ℝ := fun x i => f i x
  let B : Ω' → κ → ℝ := fun y j => g j y
  let ρ : ι ⊕ κ → Measure ℝ := fun c =>
    μπ.map (fun ω : Ω × Ω' =>
      Sum.elim (fun i => f i ω.1) (fun j => g j ω.2) c)
  let e : (ι ⊕ κ → ℝ) ≃ᵐ (ι → ℝ) × (κ → ℝ) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ κ => ℝ)
  -- The combined family must be ae-measurable coordinatewise for the factorization criterion
  have hFmeas : ∀ c : ι ⊕ κ,
      AEMeasurable (fun ω : Ω × Ω' =>
        Sum.elim (fun i => f i ω.1) (fun j => g j ω.2) c) μπ :=
    Sum.rec (fun i => ((hfmeas i).comp measurable_fst).aemeasurable)
      (fun j => ((hgmeas j).comp measurable_snd).aemeasurable)
  -- Each projected family has independent coordinates, so its law is the product of its marginals
  have hAπ : μ.map A = Measure.pi (fun i : ι => μ.map (f i)) :=
    iIndepFun_law_eq_pi μ f hfmeas hf
  have hBπ : ν.map B = Measure.pi (fun j : κ => ν.map (g j)) :=
    iIndepFun_law_eq_pi ν g hgmeas hg
  rw [iIndepFun_iff_map_fun_eq_pi_map (μ := μπ) hFmeas]
  apply MeasurableEquiv.map_measurableEquiv_injective e
  -- Transport the joint law through the sum-Pi equivalence: this is the pair of the two
  -- projected families, whose law is the product of the two laws
  have hLeft : (μπ.map F).map e = (μ.map A).prod (ν.map B) :=
    sumPi_tuple_map_prod_map μ ν f g hfmeas hgmeas
  -- A combined coordinate lives on one factor of the product, so its marginal law is the
  -- original single-family law
  have hρ_left : ∀ i : ι, ρ (Sum.inl i) = μ.map (f i) :=
    fun i => map_prod_fst_eq μ ν (f i) (hfmeas i)
  have hρ_right : ∀ j : κ, ρ (Sum.inr j) = ν.map (g j) :=
    fun j => map_prod_snd_eq μ ν (g j) (hgmeas j)
  -- Transport the pi-law through the sum-Pi equivalence: it is the product of the pi-laws of
  -- the two marginals, using the marginal laws computed above
  have hRight : (Measure.pi ρ).map e =
      (Measure.pi (fun i : ι => μ.map (f i))).prod
        (Measure.pi (fun j : κ => ν.map (g j))) := by
    simpa [hρ_left, hρ_right] using
      (measurePreserving_sumPiEquivProdPi (X := fun _ : ι ⊕ κ => ℝ) ρ).map_eq
  exact (hLeft.trans (hAπ ▸ hBπ ▸ rfl)).trans hRight.symm

/-- Hidden-constructor step for full-network coordinate independence.

Informal proof: unfold `Coordinate`, `coordinate`, and `gaussianInit`. The coordinate family is the
sum of the first-layer scalar coordinate family and the tail scalar coordinate family on the two
factors of the product measure. Apply `iIndepFun_sum_prod_real` with
`iIndepFun_layerCoordinate_layerGaussianInit` for the first layer and the induction hypothesis for
the tail. See the product-measure factorization characterization of independence in Mathlib:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html>. -/
private theorem iIndepFun_coordinate_gaussianInit_hidden {m n k : ℕ} (tail : MLPShape k n)
    (p : (MLPShape.hidden tail : MLPShape m n).Hyperparams)
    (ih : iIndepFun (fun c : tail.Coordinate => tail.coordinate c) (tail.gaussianInit p.2)) :
    iIndepFun
      (fun c : (MLPShape.hidden tail : MLPShape m n).Coordinate =>
        (MLPShape.hidden tail : MLPShape m n).coordinate c)
      ((MLPShape.hidden tail : MLPShape m n).gaussianInit p) := by
  have hfam : (fun c : (MLPShape.hidden tail : MLPShape m n).Coordinate =>
        (MLPShape.hidden tail : MLPShape m n).coordinate c) =
      (fun c : LayerCoordinate (Fin m) (Fin k) ⊕ tail.Coordinate =>
        fun θ : LayerParams (Fin m) (Fin k) × tail.Params =>
          Sum.elim (fun c₁ => layerCoordinate c₁ θ.1)
            (fun c₂ => tail.coordinate c₂ θ.2) c) := by
    ext c θ; cases c <;> rfl
  rw [hfam]
  exact iIndepFun_sum_prod_real
    (μ := layerGaussianInit p.1 (Fin m) (Fin k))
    (ν := tail.gaussianInit p.2)
    (f := layerCoordinate)
    (g := tail.coordinate)
    (hfmeas := measurable_layerCoordinate')
    (hgmeas := measurable_coordinate tail)
    (hf := iIndepFun_layerCoordinate_layerGaussianInit p.1 (Fin m) (Fin k))
    (hg := ih)

/-- All scalar weights and biases in all layers of a fixed MLP are jointly independent.

Informal proof: `iIndepFun_layerCoordinate_layerGaussianInit` gives joint independence in the first
layer, and the induction hypothesis gives it in the tail. The two families are independent because
the full law is their product; combining them along the sum index `S.Coordinate` proves the result.
See Mathlib's independence API:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html>. -/
theorem iIndepFun_coordinate_gaussianInit {m n : ℕ} (S : MLPShape m n)
    (p : S.Hyperparams) :
    iIndepFun (fun c : S.Coordinate => S.coordinate c) (S.gaussianInit p) := by
  induction S with
  | output => exact iIndepFun_layerCoordinate_layerGaussianInit p (Fin _) (Fin _)
  | hidden tail ih =>
      exact iIndepFun_coordinate_gaussianInit_hidden tail p (ih p.2)

end MLPShape

end NeuralNetwork

end

end
