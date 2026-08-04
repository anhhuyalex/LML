/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.Network
public import LeanMachineLearning.ForMathlib.Probability.Independence.IndepFun
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Covariance

/-!
# Independent Gaussian initialization of a dense layer

This file constructs the law, rather than merely postulating coordinate moments.  Its two nested
finite `Measure.pi` products encode independence of weight coordinates, and an outer product keeps
weights independent from biases.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace NeuralNetwork

universe u v

/-- Bias and unscaled weight variances.  Nonnegativity is represented in the type. -/
structure InitHyperparams where
  /-- Variance shared by the independent bias coordinates. -/
  biasVariance : ℝ≥0
  /-- Weight variance before division by the layer's fan-in. -/
  weightVariance : ℝ≥0

/-- Fan-in-scaled variance of one weight coordinate. -/
def scaledWeightVariance (p : InitHyperparams) (ι : Type u) [Fintype ι] : ℝ≥0 :=
  p.weightVariance / (Fintype.card ι : ℝ≥0)

/-- Independent centered Gaussian weight coordinates. -/
def gaussianWeightLaw (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] : Measure (κ → ι → ℝ) :=
  Measure.pi fun _ : κ => Measure.pi fun _ : ι => gaussianReal 0 (scaledWeightVariance p ι)

/-- Independent centered Gaussian bias coordinates. -/
def gaussianBiasLaw (p : InitHyperparams) (κ : Type v) [Fintype κ] : Measure (κ → ℝ) :=
  Measure.pi fun _ : κ => gaussianReal 0 p.biasVariance

/-- Product law of all weight and bias coordinates of a dense layer. -/
def layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] : Measure (LayerParams ι κ) :=
  (gaussianWeightLaw p ι κ).prod (gaussianBiasLaw p κ)

/-- A single index type for every scalar parameter of a dense layer.  Weight coordinates are on
the left and bias coordinates are on the right. -/
abbrev LayerCoordinate (ι : Type u) (κ : Type v) := (κ × ι) ⊕ κ

/-- Read a scalar layer parameter at a flattened coordinate. -/
def layerCoordinate {ι : Type u} {κ : Type v}
    (c : LayerCoordinate ι κ) (q : LayerParams ι κ) : ℝ :=
  match c with
  | .inl ji => q.1 ji.1 ji.2
  | .inr j => q.2 j

instance instIsProbabilityMeasureLayerGaussianInit (p : InitHyperparams)
    (ι : Type u) (κ : Type v) [Fintype ι] [Fintype κ] :
    IsProbabilityMeasure (layerGaussianInit p ι κ) := by
  unfold layerGaussianInit gaussianWeightLaw gaussianBiasLaw
  infer_instance

/-- Named theorem form of the probability-measure instance. -/
theorem isProbabilityMeasure_layerGaussianInit (p : InitHyperparams)
    (ι : Type u) (κ : Type v) [Fintype ι] [Fintype κ] :
    IsProbabilityMeasure (layerGaussianInit p ι κ) := by
  infer_instance

/-- A bias coordinate has the requested centered Gaussian law.

Informal proof: map the outer product by `Prod.snd`, then map the finite product by evaluation at
`j`.  `Measure.map_snd_prod` and `Measure.pi_map_eval` reduce the result to the corresponding
factor.  See Mathlib's finite product construction:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/Pi.html>. -/
theorem map_bias_layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] (j : κ) :
    Measure.map (fun q : LayerParams ι κ => q.2 j) (layerGaussianInit p ι κ) =
      gaussianReal 0 p.biasVariance := by
  classical
  have : IsProbabilityMeasure (gaussianWeightLaw p ι κ) := by
    unfold gaussianWeightLaw
    infer_instance
  rw [show (fun q : LayerParams ι κ => q.2 j) = Function.eval j ∘ Prod.snd from rfl,
    ← Measure.map_map (measurable_pi_apply j) measurable_snd]
  simp only [layerGaussianInit, Measure.map_snd_prod, measure_univ, one_smul, gaussianBiasLaw]
  rw [Measure.pi_map_eval]
  simp

/-- A weight coordinate has the fan-in-scaled centered Gaussian law.

Informal proof: map the outer product by `Prod.fst`, then apply `Measure.pi_map_eval` first at `j`
and then at `i`.  Probability normalization removes the scalar factors introduced by projection.
See <https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Constructions/Pi.html>. -/
theorem map_weight_layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] (j : κ) (i : ι) :
    Measure.map (fun q : LayerParams ι κ => q.1 j i) (layerGaussianInit p ι κ) =
      gaussianReal 0 (scaledWeightVariance p ι) := by
  classical
  have : IsProbabilityMeasure (gaussianBiasLaw p κ) := by
    unfold gaussianBiasLaw
    infer_instance
  rw [show (fun q : LayerParams ι κ => q.1 j i) =
      Function.eval i ∘ (fun q : LayerParams ι κ => q.1 j) from rfl,
    ← Measure.map_map (measurable_pi_apply i)
      ((measurable_pi_apply j).comp measurable_fst)]
  rw [show (fun q : LayerParams ι κ => q.1 j) = Function.eval j ∘ Prod.fst from rfl,
    ← Measure.map_map (measurable_pi_apply j) measurable_fst]
  simp only [layerGaussianInit, Measure.map_fst_prod, measure_univ, one_smul,
    gaussianWeightLaw]
  rw [Measure.pi_map_eval]
  simp only [measure_univ, Finset.prod_const_one, one_smul]
  rw [Measure.pi_map_eval]
  simp only [measure_univ, Finset.prod_const_one, one_smul]

/-- The bias marginal has exactly the normalized Gaussian density displayed in the source whenever
its variance is nonzero. -/
theorem map_bias_layerGaussianInit_eq_withDensity (p : InitHyperparams)
    (ι : Type u) (κ : Type v) [Fintype ι] [Fintype κ]
    (hp : p.biasVariance ≠ 0) (j : κ) :
    Measure.map (fun q : LayerParams ι κ => q.2 j) (layerGaussianInit p ι κ) =
      volume.withDensity (gaussianPDF 0 p.biasVariance) := by
  rw [map_bias_layerGaussianInit, gaussianReal_of_var_ne_zero _ hp]

/-- The weight marginal has the fan-in-normalized Gaussian density displayed in the source whenever
the scaled variance is nonzero. -/
theorem map_weight_layerGaussianInit_eq_withDensity (p : InitHyperparams)
    (ι : Type u) (κ : Type v) [Fintype ι] [Fintype κ]
    (hp : scaledWeightVariance p ι ≠ 0) (j : κ) (i : ι) :
    Measure.map (fun q : LayerParams ι κ => q.1 j i) (layerGaussianInit p ι κ) =
      volume.withDensity (gaussianPDF 0 (scaledWeightVariance p ι)) := by
  rw [map_weight_layerGaussianInit, gaussianReal_of_var_ne_zero _ hp]

/-- Pointwise expansion of the displayed centered bias density. -/
theorem gaussianPDFReal_bias_eq (p : InitHyperparams) (x : ℝ) :
    gaussianPDFReal 0 p.biasVariance x =
      (Real.sqrt (2 * Real.pi * (p.biasVariance : ℝ)))⁻¹ *
        Real.exp (-(x ^ 2) / (2 * (p.biasVariance : ℝ))) := by
  simp [gaussianPDFReal]

/-- Pointwise expansion of the displayed fan-in-scaled weight density. -/
theorem gaussianPDFReal_weight_eq (p : InitHyperparams) (ι : Type u)
    [Fintype ι] (x : ℝ) :
    gaussianPDFReal 0 (scaledWeightVariance p ι) x =
      (Real.sqrt (2 * Real.pi * (scaledWeightVariance p ι : ℝ)))⁻¹ *
        Real.exp (-(x ^ 2) / (2 * (scaledWeightVariance p ι : ℝ))) := by
  simp [gaussianPDFReal]

-- For positive `C` and `n`, moving the quotient `C / n` through the square root and inverting
-- gives the fan-in-scaled normalization factor: 1/√(2π·(C/n)) = √(n/(2π·C)).
-- Used by `gaussianPDFReal_weight_eq_source` to rewrite the weight density into the printed form.
private lemma gaussianNorm_scaled_eq (C n : ℝ) (hC : 0 < C) (hn : 0 < n) :
    (Real.sqrt (2 * Real.pi * (C / n)))⁻¹ =
      Real.sqrt (n / (2 * Real.pi * C)) := by
  rw [← Real.sqrt_inv]
  congr 1
  field_simp [ne_of_gt hC, ne_of_gt hn, Real.pi_ne_zero]

/-- The fan-in-scaled weight density in exactly the algebraic form printed in Chapter 2.

Informal proof: substitute `scaledWeightVariance = C_W / |ι|` into `gaussianPDFReal_weight_eq`.
Since both `C_W` and `|ι|` are positive, move the quotient through the square root and simplify the
exponent by field arithmetic.  See the normal-density scaling formula at
<https://en.wikipedia.org/wiki/Normal_distribution#General_normal_distribution>. -/
theorem gaussianPDFReal_weight_eq_source (p : InitHyperparams) (ι : Type u)
    [Fintype ι] [Nonempty ι] (hp : p.weightVariance ≠ 0) (x : ℝ) :
    gaussianPDFReal 0 (scaledWeightVariance p ι) x =
      Real.sqrt ((Fintype.card ι : ℝ) /
          (2 * Real.pi * (p.weightVariance : ℝ))) *
        Real.exp (-((Fintype.card ι : ℝ) * x ^ 2) /
          (2 * (p.weightVariance : ℝ))) := by
  rw [gaussianPDFReal_weight_eq]
  simp only [scaledWeightVariance, NNReal.coe_div, NNReal.coe_natCast]
  -- Positivity of the variance and of the fan-in, needed by the field simplifications below.
  have hCpos : 0 < (p.weightVariance : ℝ) := by
    exact_mod_cast pos_iff_ne_zero.mpr hp
  have hnpos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  -- Rewrite the square-root factor with the fan-in-scaled helper, then simplify the exponent.
  rw [gaussianNorm_scaled_eq (p.weightVariance : ℝ) (Fintype.card ι : ℝ) hCpos hnpos]
  congr 1
  congr 1
  field_simp [ne_of_gt hCpos, ne_of_gt hnpos]

/-- Bias coordinates are mutually independent.

Informal proof: `iIndepFun_pi` gives independence of evaluations under `gaussianBiasLaw`; composing
with the second projection preserves it under the independent outer product.  See Mathlib's
`ProbabilityTheory.iIndepFun_pi`:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html>. -/
theorem iIndepFun_bias_layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] :
    iIndepFun (fun j (q : LayerParams ι κ) => q.2 j) (layerGaussianInit p ι κ) := by
  classical
  have hWprob : IsProbabilityMeasure (gaussianWeightLaw p ι κ) := by
    unfold gaussianWeightLaw
    infer_instance
  have hBsfinite : SFinite (gaussianBiasLaw p κ) := by
    unfold gaussianBiasLaw
    infer_instance
  let X : κ → (κ → ℝ) → ℝ := fun j b => b j
  let f : LayerParams ι κ → κ → ℝ := Prod.snd
  have hf : AEMeasurable f (layerGaussianInit p ι κ) := measurable_snd.aemeasurable
  have hmap : Measure.map f (layerGaussianInit p ι κ) = gaussianBiasLaw p κ := by
    rw [show f = (Prod.snd : LayerParams ι κ → κ → ℝ) from rfl, layerGaussianInit]
    exact (@MeasureTheory.measurePreserving_snd (κ → ι → ℝ) (κ → ℝ) _ _
      (gaussianWeightLaw p ι κ) (gaussianBiasLaw p κ) hBsfinite hWprob).map_eq
  have hX : ∀ j, AEMeasurable (X j) (Measure.map f (layerGaussianInit p ι κ)) := by
    intro j
    exact (measurable_pi_apply j).aemeasurable
  have hBias : iIndepFun X (Measure.map f (layerGaussianInit p ι κ)) := by
    rw [hmap]
    change iIndepFun (fun j (b : κ → ℝ) => (id : ℝ → ℝ) (b j))
      (Measure.pi fun _ : κ => gaussianReal 0 p.biasVariance)
    exact iIndepFun_pi (mΩ := fun _ : κ => inferInstance)
      (mX := fun _ : κ => aemeasurable_id)
  have hPullback : iIndepFun (fun j => X j ∘ f) (layerGaussianInit p ι κ) :=
    (ProbabilityTheory.iIndepFun_map_iff hf hX).mp hBias
  simpa [X, f, Function.comp_def] using hPullback

/-- All flattened weight coordinates are mutually independent.

Informal proof: apply `iIndepFun_pi` at the outer weight-row product and within every row, or use
its `HasLaw` characterization to flatten the two finite products into a product indexed by
`κ × ι`.  See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html>. -/
theorem iIndepFun_weight_layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] :
    iIndepFun (fun ji : κ × ι => fun q : LayerParams ι κ => q.1 ji.1 ji.2)
      (layerGaussianInit p ι κ) := by
  classical
  -- 1. The flattened product measure, transported to `gaussianWeightLaw` by currying.
  let G : Measure ℝ := gaussianReal 0 (scaledWeightVariance p ι)
  let μ₀ : Measure (κ × ι → ℝ) := Measure.pi fun _ : κ × ι => G
  have hFlat : iIndepFun (fun ji (w : κ × ι → ℝ) => w ji) μ₀ := by
    exact iIndepFun_pi (mΩ := fun _ : κ × ι => inferInstance)
      (mX := fun _ : κ × ι => aemeasurable_id)
  have hCurry : μ₀.map (MeasurableEquiv.curry κ ι ℝ) = gaussianWeightLaw p ι κ := by
    unfold μ₀ gaussianWeightLaw
    rw [← Measure.infinitePi_eq_pi (μ := fun _ : κ × ι => G)]
    rw [Measure.infinitePi_map_curry (μ := fun (_ : κ) (_ : ι) => G)]
    rw [Measure.infinitePi_eq_pi (μ := fun _ : κ => Measure.infinitePi fun _ : ι => G)]
    congr 1
    funext j
    rw [Measure.infinitePi_eq_pi (μ := fun _ : ι => G)]
  let e : (κ × ι → ℝ) ≃ᵐ (κ → ι → ℝ) := MeasurableEquiv.curry κ ι ℝ
  have hCurrySymm : (gaussianWeightLaw p ι κ).map e.symm = μ₀ := by
    rw [← hCurry, MeasurableEquiv.map_symm_map e]
  have hWprob : IsProbabilityMeasure (gaussianWeightLaw p ι κ) := by
    unfold gaussianWeightLaw
    infer_instance
  have hX₀ : ∀ ji, AEMeasurable (fun w : κ × ι → ℝ => w ji)
      ((gaussianWeightLaw p ι κ).map e.symm) := by
    intro ji
    rw [hCurrySymm]
    exact (measurable_pi_apply ji).aemeasurable
  have hPull : iIndepFun (fun ji => (fun w : κ × ι → ℝ => w ji) ∘ e.symm)
      (gaussianWeightLaw p ι κ) :=
    (ProbabilityTheory.iIndepFun_map_iff (μ := gaussianWeightLaw p ι κ) (f := e.symm)
      e.symm.measurable.aemeasurable hX₀).mp (by simpa [hCurrySymm] using hFlat)
  have hW : iIndepFun (fun ji : κ × ι => fun w : κ → ι → ℝ => w ji.1 ji.2)
      (gaussianWeightLaw p ι κ) := by
    simpa [e, MeasurableEquiv.coe_curry_symm, Function.comp_def, Function.uncurry] using hPull
  -- 2. Pull back through `Prod.fst` from the outer product law.
  let f : LayerParams ι κ → κ → ι → ℝ := Prod.fst
  have hf : AEMeasurable f (layerGaussianInit p ι κ) := measurable_fst.aemeasurable
  have hBsfinite : SFinite (gaussianBiasLaw p κ) := by
    unfold gaussianBiasLaw
    infer_instance
  have hBprob : IsProbabilityMeasure (gaussianBiasLaw p κ) := by
    unfold gaussianBiasLaw
    infer_instance
  have hmap : Measure.map f (layerGaussianInit p ι κ) = gaussianWeightLaw p ι κ := by
    rw [show f = (Prod.fst : LayerParams ι κ → κ → ι → ℝ) from rfl, layerGaussianInit]
    exact (@MeasureTheory.measurePreserving_fst (κ → ι → ℝ) (κ → ℝ) _ _
      (gaussianWeightLaw p ι κ) (gaussianBiasLaw p κ) hBsfinite hBprob).map_eq
  let X : κ × ι → (κ → ι → ℝ) → ℝ := fun ji w => w ji.1 ji.2
  have hX : ∀ ji, AEMeasurable (X ji) (Measure.map f (layerGaussianInit p ι κ)) := by
    intro ji
    rw [hmap]
    exact ((measurable_pi_apply ji.2).comp (measurable_pi_apply ji.1)).aemeasurable
  have hFinal : iIndepFun (fun ji => X ji ∘ f) (layerGaussianInit p ι κ) :=
    (ProbabilityTheory.iIndepFun_map_iff hf hX).mp (by simpa [hmap, X] using hW)
  simpa [X, f, Function.comp_def] using hFinal

/-- The complete weight vector is independent of the complete bias vector.

Informal proof: these are the two coordinate projections of the product measure
`gaussianWeightLaw.prod gaussianBiasLaw`; independence of product projections is the defining
product-measure theorem.  See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html>. -/
theorem indepFun_weight_bias_layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] :
    IndepFun (fun q : LayerParams ι κ => q.1) (fun q => q.2) (layerGaussianInit p ι κ) := by
  classical
  have hWprob : IsProbabilityMeasure (gaussianWeightLaw p ι κ) := by
    unfold gaussianWeightLaw
    infer_instance
  have hBprob : IsProbabilityMeasure (gaussianBiasLaw p κ) := by
    unfold gaussianBiasLaw
    infer_instance
  rw [layerGaussianInit]
  simpa using
    (@ProbabilityTheory.indepFun_prod (κ → ι → ℝ) (κ → ℝ) _ _
      (gaussianWeightLaw p ι κ) (gaussianBiasLaw p κ) hWprob hBprob
      _ _ _ _ (fun w : κ → ι → ℝ => w) (fun b : κ → ℝ => b) measurable_id measurable_id)

-- Measurability of one flattened coordinate evaluation: `layerCoordinate` is a case split
-- between the weight coordinate `q.1 ji.1 ji.2` and the bias coordinate `q.2 j`.
private lemma measurable_layerCoordinate {ι : Type u} {κ : Type v}
    (c : LayerCoordinate ι κ) :
    Measurable (fun q : LayerParams ι κ => layerCoordinate c q) := by
  cases c with
  | inl ji =>
      exact (measurable_pi_apply ji.2).comp ((measurable_pi_apply ji.1).comp measurable_fst)
  | inr j =>
      exact (measurable_pi_apply j).comp measurable_snd

/-- All weights and biases are jointly independent, not merely pairwise independent.

Informal proof: the two nested `Measure.pi` constructions make all weight evaluations jointly
independent; the bias `Measure.pi` does the same for biases; and the outer product makes the two
complete vectors independent.  Combining independent indexed families on a sum index gives the
claim.  See Mathlib's product-independence API:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Independence/Basic.html>. -/
theorem iIndepFun_layerCoordinate_layerGaussianInit (p : InitHyperparams)
    (ι : Type u) (κ : Type v) [Fintype ι] [Fintype κ] :
    iIndepFun (fun c : LayerCoordinate ι κ => layerCoordinate c)
      (layerGaussianInit p ι κ) := by
  classical
  let μ : Measure (LayerParams ι κ) := layerGaussianInit p ι κ
  let W : LayerParams ι κ → (κ × ι → ℝ) := fun q ji => q.1 ji.1 ji.2
  let B : LayerParams ι κ → (κ → ℝ) := fun q j => q.2 j
  let F : LayerParams ι κ → (LayerCoordinate ι κ → ℝ) := fun q c => layerCoordinate c q
  let e : (LayerCoordinate ι κ → ℝ) ≃ᵐ ((κ × ι → ℝ) × (κ → ℝ)) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : LayerCoordinate ι κ => ℝ)
  let ρ : LayerCoordinate ι κ → Measure ℝ :=
    fun c => μ.map (fun q : LayerParams ι κ => layerCoordinate c q)
  -- Measurability of the flattened map `F` and of each coordinate evaluation.
  have hFmeas : Measurable F := by
    exact measurable_pi_lambda _ fun c => measurable_layerCoordinate c
  have hF : ∀ c : LayerCoordinate ι κ,
      AEMeasurable (fun q : LayerParams ι κ => layerCoordinate c q) μ := by
    intro c
    exact (measurable_layerCoordinate c).aemeasurable
  rw [iIndepFun_iff_map_fun_eq_pi_map (μ := μ) hF]
  apply MeasurableEquiv.map_measurableEquiv_injective e
  have hWmeas : Measurable W := by
    dsimp [W]
    exact measurable_pi_lambda _ fun ji : κ × ι => measurable_layerCoordinate (.inl ji)
  have hBmeas : Measurable B := by
    exact measurable_pi_lambda _ fun j => measurable_layerCoordinate (.inr j)
  have hWeightTuple :
      μ.map W =
        Measure.pi (fun ji : κ × ι => μ.map (fun q : LayerParams ι κ => q.1 ji.1 ji.2)) := by
    simpa [μ, W, layerCoordinate] using
      (iIndepFun_weight_layerGaussianInit p ι κ).map_fun_eq_pi_map (fun ji =>
        (measurable_layerCoordinate (.inl ji)).aemeasurable)
  have hBiasTuple :
      μ.map B = Measure.pi (fun j : κ => μ.map (fun q : LayerParams ι κ => q.2 j)) := by
    change
      μ.map B =
        Measure.pi (fun j : κ => μ.map (((fun b : κ → ℝ => b j) ∘ Prod.snd) : LayerParams ι κ → ℝ))
    simpa [μ, B, layerCoordinate] using
      (iIndepFun_bias_layerGaussianInit p ι κ).map_fun_eq_pi_map (fun j =>
        (measurable_layerCoordinate (.inr j)).aemeasurable)
  have hBlock : W ⟂ᵢ[μ] B := by
    have hWB := indepFun_weight_bias_layerGaussianInit p ι κ
    exact hWB.comp
      (measurable_pi_lambda _ fun ji : κ × ι =>
        (measurable_pi_apply ji.2).comp (measurable_pi_apply ji.1))
      measurable_id
  have hLeft : (μ.map F).map e = (μ.map W).prod (μ.map B) := by
    rw [Measure.map_map e.measurable hFmeas]
    change Measure.map (fun q : LayerParams ι κ => (W q, B q)) μ = (μ.map W).prod (μ.map B)
    rw [hBlock.map_prod_eq_prod_map_map hWmeas.aemeasurable hBmeas.aemeasurable]
  have hRight :
      (Measure.pi ρ).map e =
        (Measure.pi (fun ji : κ × ι => μ.map (fun q : LayerParams ι κ => q.1 ji.1 ji.2))).prod
          (Measure.pi (fun j : κ => μ.map (fun q : LayerParams ι κ => q.2 j))) := by
    simpa [e, LayerCoordinate, layerCoordinate, ρ] using
      (measurePreserving_sumPiEquivProdPi (X := fun _ : LayerCoordinate ι κ => ℝ) ρ).map_eq
  calc
    (μ.map F).map e = (μ.map W).prod (μ.map B) := hLeft
    _ = (Measure.pi fun ji : κ × ι => μ.map (fun q : LayerParams ι κ => q.1 ji.1 ji.2)).prod
        (Measure.pi fun j : κ => μ.map (fun q : LayerParams ι κ => q.2 j)) := by
          rw [hWeightTuple, hBiasTuple]
    _ = (Measure.pi ρ).map e := hRight.symm

/-- Every initialized bias is centered.

Informal proof: transfer the integral through `map_bias_layerGaussianInit` and use Mathlib's
`integral_id_gaussianReal`.  See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Gaussian/Real.html>. -/
theorem integral_bias_layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] (j : κ) :
    ∫ q, q.2 j ∂layerGaussianInit p ι κ = 0 := by
  let X : LayerParams ι κ → ℝ := fun q => q.2 j
  have hX : Measurable X := (measurable_pi_apply j).comp measurable_snd
  calc
    ∫ q, q.2 j ∂layerGaussianInit p ι κ =
        ∫ x, x ∂Measure.map X (layerGaussianInit p ι κ) := by
      symm
      exact integral_map hX.aemeasurable continuous_id.aestronglyMeasurable
    _ = ∫ x, x ∂gaussianReal 0 p.biasVariance := by rw [map_bias_layerGaussianInit]
    _ = 0 := integral_id_gaussianReal

/-- Every initialized weight is centered.

Informal proof: transfer the integral through `map_weight_layerGaussianInit` and apply
`integral_id_gaussianReal`.  See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Gaussian/Real.html>. -/
theorem integral_weight_layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] (j : κ) (i : ι) :
    ∫ q, q.1 j i ∂layerGaussianInit p ι κ = 0 := by
  let X : LayerParams ι κ → ℝ := fun q => q.1 j i
  have hX : Measurable X :=
    (measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_fst)
  calc
    ∫ q, q.1 j i ∂layerGaussianInit p ι κ =
        ∫ x, x ∂Measure.map X (layerGaussianInit p ι κ) := by
      symm
      exact integral_map hX.aemeasurable continuous_id.aestronglyMeasurable
    _ = ∫ x, x ∂gaussianReal 0 (scaledWeightVariance p ι) := by
      rw [map_weight_layerGaussianInit]
    _ = 0 := integral_id_gaussianReal

/-- Bias covariance is the expected Kronecker-delta formula.

Informal proof: for equal indices this is `variance_id_gaussianReal` transported through the
coordinate-law theorem; for unequal indices, mutual independence and centeredness give zero
covariance.  See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/Covariance.html>. -/
theorem covariance_bias_layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] [DecidableEq κ] (j j' : κ) :
    cov[fun q : LayerParams ι κ => q.2 j, fun q => q.2 j'; layerGaussianInit p ι κ] =
      if j = j' then p.biasVariance else 0 := by
  classical
  by_cases hjj : j = j'
  · subst j'
    let X : LayerParams ι κ → ℝ := fun q => q.2 j
    have hX : AEMeasurable X (layerGaussianInit p ι κ) :=
      ((measurable_pi_apply j).comp measurable_snd).aemeasurable
    have hmapX : Measure.map X (layerGaussianInit p ι κ) = gaussianReal 0 p.biasVariance :=
      map_bias_layerGaussianInit p ι κ j
    rw [covariance_self hX]
    rw [← variance_id_map hX]
    have hvar : Var[id; Measure.map X (layerGaussianInit p ι κ)] = (p.biasVariance : ℝ) := by
      rw [hmapX]
      exact variance_id_gaussianReal
    rw [hvar, if_pos rfl]
  · let X : LayerParams ι κ → ℝ := fun q => q.2 j
    let Y : LayerParams ι κ → ℝ := fun q => q.2 j'
    have hX : AEMeasurable X (layerGaussianInit p ι κ) :=
      ((measurable_pi_apply j).comp measurable_snd).aemeasurable
    have hY : AEMeasurable Y (layerGaussianInit p ι κ) :=
      ((measurable_pi_apply j').comp measurable_snd).aemeasurable
    have hIndep : X ⟂ᵢ[layerGaussianInit p ι κ] Y := by
      exact (iIndepFun_bias_layerGaussianInit p ι κ).indepFun hjj
    have hXlp : MemLp X 2 (layerGaussianInit p ι κ) := by
      have hmem : MemLp (id : ℝ → ℝ) 2 (Measure.map X (layerGaussianInit p ι κ)) := by
        rw [map_bias_layerGaussianInit p ι κ j]
        exact memLp_id_gaussianReal 2
      exact (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (p := 2) (f := X)
        (by exact measurable_id.aestronglyMeasurable) hX).1 hmem
    have hYlp : MemLp Y 2 (layerGaussianInit p ι κ) := by
      have hmem : MemLp (id : ℝ → ℝ) 2 (Measure.map Y (layerGaussianInit p ι κ)) := by
        rw [map_bias_layerGaussianInit p ι κ j']
        exact memLp_id_gaussianReal 2
      exact (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (p := 2) (f := Y)
        (by exact measurable_id.aestronglyMeasurable) hY).1 hmem
    have hXY : cov[X, Y; layerGaussianInit p ι κ] = 0 :=
      ProbabilityTheory.IndepFun.covariance_eq_zero hIndep hXlp hYlp
    simpa [X, Y, hjj] using hXY

/-- Weight covariance is diagonal in both neuron and input coordinates.

Informal proof: equality of the pairs reduces to the transported Gaussian variance theorem;
distinct pairs are independent by `iIndepFun_weight_layerGaussianInit`, hence have covariance zero.
See <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/Covariance.html>. -/
theorem covariance_weight_layerGaussianInit (p : InitHyperparams) (ι : Type u) (κ : Type v)
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (j j' : κ) (i i' : ι) :
    cov[fun q : LayerParams ι κ => q.1 j i, fun q => q.1 j' i'; layerGaussianInit p ι κ] =
      if j = j' ∧ i = i' then scaledWeightVariance p ι else 0 := by
  classical
  by_cases hjj : j = j' ∧ i = i'
  · rcases hjj with ⟨rfl, rfl⟩
    let X : LayerParams ι κ → ℝ := fun q => q.1 j i
    have hX : AEMeasurable X (layerGaussianInit p ι κ) :=
      ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_fst)).aemeasurable
    have hmapX :
        Measure.map X (layerGaussianInit p ι κ) = gaussianReal 0 (scaledWeightVariance p ι) :=
      map_weight_layerGaussianInit p ι κ j i
    rw [covariance_self hX]
    rw [← variance_id_map hX]
    have hvar : Var[id; Measure.map X (layerGaussianInit p ι κ)] =
        (scaledWeightVariance p ι : ℝ) := by
      rw [hmapX]
      exact variance_id_gaussianReal
    rw [hvar, if_pos ⟨rfl, rfl⟩]
  · let X : LayerParams ι κ → ℝ := fun q => q.1 j i
    let Y : LayerParams ι κ → ℝ := fun q => q.1 j' i'
    have hX : AEMeasurable X (layerGaussianInit p ι κ) :=
      ((measurable_pi_apply i).comp ((measurable_pi_apply j).comp measurable_fst)).aemeasurable
    have hY : AEMeasurable Y (layerGaussianInit p ι κ) :=
      ((measurable_pi_apply i').comp ((measurable_pi_apply j').comp measurable_fst)).aemeasurable
    have hji : (j, i) ≠ (j', i') := by
      intro hprod
      exact hjj (Prod.ext_iff.mp hprod)
    have hIndep : X ⟂ᵢ[layerGaussianInit p ι κ] Y := by
      exact (iIndepFun_weight_layerGaussianInit p ι κ).indepFun hji
    have hXlp : MemLp X 2 (layerGaussianInit p ι κ) := by
      have hmem : MemLp (id : ℝ → ℝ) 2 (Measure.map X (layerGaussianInit p ι κ)) := by
        rw [map_weight_layerGaussianInit p ι κ j i]
        exact memLp_id_gaussianReal 2
      exact (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (p := 2) (f := X)
        (by exact measurable_id.aestronglyMeasurable) hX).1 hmem
    have hYlp : MemLp Y 2 (layerGaussianInit p ι κ) := by
      have hmem : MemLp (id : ℝ → ℝ) 2 (Measure.map Y (layerGaussianInit p ι κ)) := by
        rw [map_weight_layerGaussianInit p ι κ j' i']
        exact memLp_id_gaussianReal 2
      exact (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (p := 2) (f := Y)
        (by exact measurable_id.aestronglyMeasurable) hY).1 hmem
    have hXY : cov[X, Y; layerGaussianInit p ι κ] = 0 :=
      ProbabilityTheory.IndepFun.covariance_eq_zero hIndep hXlp hYlp
    simpa [X, Y, hjj] using hXY

/-- Every bias coordinate is uncorrelated with every weight coordinate.

Informal proof: the complete weight and bias vectors are independent under the outer product law;
measurable coordinate projections preserve independence.  Both Gaussian coordinates are in
`L²`, so `IndepFun.covariance_eq_zero` applies.  See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Moments/Covariance.html>. -/
theorem covariance_weight_bias_layerGaussianInit (p : InitHyperparams)
    (ι : Type u) (κ : Type v) [Fintype ι] [Fintype κ]
    (jW : κ) (i : ι) (jB : κ) :
    cov[fun q : LayerParams ι κ => q.1 jW i,
      fun q => q.2 jB; layerGaussianInit p ι κ] = 0 := by
  classical
  let X : LayerParams ι κ → ℝ := fun q => q.1 jW i
  let Y : LayerParams ι κ → ℝ := fun q => q.2 jB
  have hX : AEMeasurable X (layerGaussianInit p ι κ) :=
    ((measurable_pi_apply i).comp
      ((measurable_pi_apply jW).comp measurable_fst)).aemeasurable
  have hY : AEMeasurable Y (layerGaussianInit p ι κ) :=
    ((measurable_pi_apply jB).comp measurable_snd).aemeasurable
  have hIndep : X ⟂ᵢ[layerGaussianInit p ι κ] Y := by
    exact (indepFun_weight_bias_layerGaussianInit p ι κ).comp
      ((measurable_pi_apply i).comp (measurable_pi_apply jW))
      (measurable_pi_apply jB)
  have hXlp : MemLp X 2 (layerGaussianInit p ι κ) := by
    have hmem : MemLp (id : ℝ → ℝ) 2 (Measure.map X (layerGaussianInit p ι κ)) := by
      rw [map_weight_layerGaussianInit p ι κ jW i]
      exact memLp_id_gaussianReal 2
    exact (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (p := 2) (f := X)
      (by exact measurable_id.aestronglyMeasurable) hX).1 hmem
  have hYlp : MemLp Y 2 (layerGaussianInit p ι κ) := by
    have hmem : MemLp (id : ℝ → ℝ) 2 (Measure.map Y (layerGaussianInit p ι κ)) := by
      rw [map_bias_layerGaussianInit p ι κ jB]
      exact memLp_id_gaussianReal 2
    exact (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (p := 2) (f := Y)
      (by exact measurable_id.aestronglyMeasurable) hY).1 hmem
  have hXY : cov[X, Y; layerGaussianInit p ι κ] = 0 :=
    ProbabilityTheory.IndepFun.covariance_eq_zero hIndep hXlp hYlp
  simpa [X, Y] using hXY

end NeuralNetwork

end

end
