/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.DeepLinear.GaussianLayer

/-!
# Exact finite-depth moments of deep linear networks

The main statements are shape-safe integral identities for LML's existing output law.  Scalar
amplitudes and Wick tensors are factored out as reusable deterministic definitions.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace NeuralNetwork.DeepLinear

universe uA uJ

/-- Product of all finite-width radial corrections before the observed output layer. -/
def hiddenWidthCorrection (m : ℕ) (widths : List ℕ) : ℝ :=
  (widths.map (widthMomentFactor m)).prod

/-- Scalar amplitude multiplying the output-index Wick tensor. -/
def correlatorAmplitude (Cw : ℝ≥0) (q : ℝ) (m : ℕ) (widths : List ℕ) : ℝ :=
  (((Cw : ℝ) ^ (widths.length + 1) * q) ^ m) * hiddenWidthCorrection m widths

@[simp] theorem hiddenWidthCorrection_nil (m : ℕ) : hiddenWidthCorrection m [] = 1 := by
  simp [hiddenWidthCorrection]

@[simp] theorem hiddenWidthCorrection_cons (m n : ℕ) (widths : List ℕ) :
    hiddenWidthCorrection m (n :: widths) =
      widthMomentFactor m n * hiddenWidthCorrection m widths := by
  simp [hiddenWidthCorrection]

/-- Wick's pairing sum for the Kronecker covariance on a list of output indices. -/
def pairingTensor {κ : Type uJ} [DecidableEq κ] {m : ℕ} (a : Fin (2 * m) → κ) : ℝ :=
  Renormalization.wick (fun r s => if a r = a s then 1 else 0) Finset.univ

/-- A product measure is invariant under pointwise negation when every marginal is. -/
private lemma pi_map_neg_invariant {ι : Type*} [Fintype ι] {α : Type*} [MeasurableSpace α]
    [Neg α] [MeasurableNeg α] (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, (μ i).map (fun x : α => -x) = μ i) :
    (Measure.pi μ).map (fun f : ι → α => -f) = Measure.pi μ := by
  have hIndep : iIndepFun (fun i : ι => fun f : ι → α => -f i) (Measure.pi μ) :=
    iIndepFun_pi (μ := μ) (X := fun _ : ι => fun x : α => -x)
      (mX := fun _ => (by fun_prop : Measurable fun x : α => -x).aemeasurable)
  have hmap := iIndepFun.map_fun_eq_pi_map
    (μ := Measure.pi μ)
    (f := fun (i : ι) (f : ι → α) => -f i)
    (hf := fun i => (by fun_prop : Measurable fun f : ι → α => -f i).aemeasurable)
    hIndep
  calc
    (Measure.pi μ).map (fun f : ι → α => -f)
        = Measure.pi (fun i : ι => (Measure.pi μ).map (fun f : ι → α => -f i)) := hmap
    _ = Measure.pi (fun i : ι => (μ i).map (fun x : α => -x)) := by
          congr 1
          funext i
          calc
            (Measure.pi μ).map (fun f : ι → α => -f i)
                = ((Measure.pi μ).map (fun f : ι → α => f i)).map (fun x : α => -x) :=
                  (Measure.map_map (g := fun x : α => -x) (f := fun f : ι → α => f i)
                    (by fun_prop : Measurable fun x : α => -x) (measurable_pi_apply i)).symm
            _ = (μ i).map (fun x : α => -x) :=
                  congrArg (fun ν : Measure α => ν.map (fun x : α => -x))
                    (measurePreserving_eval μ i).map_eq
    _ = Measure.pi μ := congrArg Measure.pi (funext hμ)

/-- Negate the weights and biases of the final affine layer of a structured parameter tuple. -/
noncomputable def negLastLayer {m n : ℕ} : (S : MLPShape m n) → S.Params → S.Params
  | .output, p => (fun j i => -p.1 j i, fun j => -p.2 j)
  | .hidden tail, p => (p.1, negLastLayer tail p.2)

/-- `negLastLayer` is measurable. -/
theorem measurable_negLastLayer {m n : ℕ} (S : MLPShape m n) : Measurable (negLastLayer S) := by
  induction S with
  | output =>
      dsimp [negLastLayer]
      fun_prop
  | hidden tail ih =>
      exact measurable_fst.prodMk (ih.comp measurable_snd)

/-- Negating the final layer's weights and biases negates the deep-linear output pointwise. -/
theorem eval_negLastLayer {m n : ℕ} (S : MLPShape m n) (θ : S.Params) (x : Fin m → ℝ) :
    S.eval (linear 1) (negLastLayer S θ) x = -S.eval (linear 1) θ x := by
  induction S with
  | output =>
      rename_i m₀ n₀
      change (DenseLayer.ofParams
          (negLastLayer (MLPShape.output : MLPShape m₀ n₀) θ)).preactivation x =
        -(DenseLayer.ofParams θ).preactivation x
      funext j
      simp only [negLastLayer, DenseLayer.ofParams, DenseLayer.preactivation_apply]
      have hsum : (∑ i : Fin m₀, (-θ.1 j i) * x i) = -(∑ i : Fin m₀, θ.1 j i * x i) := by
        simp [Finset.sum_neg_distrib]
      rw [hsum]
      simp [DenseLayer.preactivation_apply]
      ring
  | hidden tail ih =>
      exact ih θ.2 ((DenseLayer.ofParams θ.1).activate (linear 1) x)

/-- The Gaussian initialization law is invariant under `negLastLayer`. -/
theorem gaussianInit_negLastLayer {m n : ℕ} (S : MLPShape m n) (Cw : ℝ≥0) :
    Measure.map (negLastLayer S) (S.gaussianInit (S.deepLinearHyperparams Cw)) =
      S.gaussianInit (S.deepLinearHyperparams Cw) := by
  induction S with
  | output =>
      rename_i m₀ n₀
      let p : InitHyperparams := DeepLinear.hyperparams Cw
      have hgW : ∀ i : Fin m₀,
          (gaussianReal 0 (scaledWeightVariance p (Fin m₀))).map (fun x : ℝ => -x) =
            gaussianReal 0 (scaledWeightVariance p (Fin m₀)) :=
        fun _ => by
          simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := scaledWeightVariance p (Fin m₀))
      have hgB : ∀ j : Fin n₀,
          (gaussianReal 0 p.biasVariance).map (fun x : ℝ => -x) =
            gaussianReal 0 p.biasVariance :=
        fun _ => by simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := p.biasVariance)
      have hW : (gaussianWeightLaw p (Fin m₀) (Fin n₀)).map
          (fun W : Fin n₀ → Fin m₀ → ℝ => -W) = gaussianWeightLaw p (Fin m₀) (Fin n₀) :=
        pi_map_neg_invariant
          (μ := fun _ : Fin n₀ => Measure.pi fun _ : Fin m₀ =>
            gaussianReal 0 (scaledWeightVariance p (Fin m₀)))
          (fun _ => pi_map_neg_invariant
            (μ := fun _ : Fin m₀ => gaussianReal 0 (scaledWeightVariance p (Fin m₀))) hgW)
      have hB : (gaussianBiasLaw p (Fin n₀)).map (fun b : Fin n₀ → ℝ => -b) =
          gaussianBiasLaw p (Fin n₀) :=
        pi_map_neg_invariant (μ := fun _ : Fin n₀ => gaussianReal 0 p.biasVariance) hgB
      have : SFinite (gaussianWeightLaw p (Fin m₀) (Fin n₀)) := by
        unfold gaussianWeightLaw
        infer_instance
      have : SFinite (gaussianBiasLaw p (Fin n₀)) := by
        unfold gaussianBiasLaw
        infer_instance
      have hmap : Measure.map (negLastLayer (MLPShape.output : MLPShape m₀ n₀))
          (layerGaussianInit p (Fin m₀) (Fin n₀)) = layerGaussianInit p (Fin m₀) (Fin n₀) := by
        change Measure.map (Prod.map (fun W : Fin n₀ → Fin m₀ → ℝ => -W)
            (fun b : Fin n₀ → ℝ => -b))
            ((gaussianWeightLaw p (Fin m₀) (Fin n₀)).prod (gaussianBiasLaw p (Fin n₀))) =
          (gaussianWeightLaw p (Fin m₀) (Fin n₀)).prod (gaussianBiasLaw p (Fin n₀))
        rw [← Measure.map_prod_map (μa := gaussianWeightLaw p (Fin m₀) (Fin n₀))
          (μc := gaussianBiasLaw p (Fin n₀)) (hf := measurable_neg) (hg := measurable_neg),
          hW, hB]
      simpa [p, MLPShape.gaussianInit, MLPShape.deepLinearHyperparams] using hmap
  | hidden tail ih =>
      rename_i m₀ n₀ k
      let μ₁ := layerGaussianInit (DeepLinear.hyperparams Cw) (Fin m₀) (Fin k)
      let ν := tail.gaussianInit (tail.deepLinearHyperparams Cw)
      have hmap : Measure.map (negLastLayer (MLPShape.hidden tail : MLPShape m₀ n₀))
          (μ₁.prod ν) = μ₁.prod ν := by
        change Measure.map (Prod.map id (negLastLayer tail)) (μ₁.prod ν) = μ₁.prod ν
        rw [← Measure.map_prod_map (μa := μ₁) (μc := ν)
          (hf := measurable_id) (hg := measurable_negLastLayer tail), ih]
        simp [ν]
      simpa [μ₁, ν, MLPShape.gaussianInit, MLPShape.deepLinearHyperparams] using hmap

/-- The one-input deep-linear output law is invariant under the coordinatewise sign flip.

Informal proof: negate only the final affine layer's weights and biases.  This parameter-space
involution preserves the independent centered Gaussian initialization law (centered Gaussians, and
variance-zero Gaussian biases, are sign-invariant) and it sends the network output pointwise to its
negative.  Pushing the initialization law forward by evaluation therefore gives an output law
invariant under `z ↦ -z`.  This is the parity argument in `docs/Renormalization.md`, final
paragraphs of Section `sec:DLN`; equivalently see the standard symmetry proof of odd Gaussian
moments in <https://en.wikipedia.org/wiki/Isserlis%27s_theorem>.
-/
theorem deepLinearOutputLaw_isNegInvariant {dIn dOut : ℕ} (S : MLPShape dIn dOut)
    (Cw : ℝ≥0) (x : Fin dIn → ℝ) :
    Measure.IsNegInvariant (S.deepLinearOutputLaw Cw x) := ⟨by
  let μ₀ : Measure S.Params := S.gaussianInit (S.deepLinearHyperparams Cw)
  let F : S.Params → Fin dOut → ℝ := fun θ => S.eval (linear 1) θ x
  have hF_meas : Measurable F :=
    (S.measurable_eval (measurable_linear 1)).comp (measurable_id.prodMk measurable_const)
  have hJ_meas : Measurable (negLastLayer S) := measurable_negLastLayer S
  have hJ_inv : Measure.map (negLastLayer S) μ₀ = μ₀ := gaussianInit_negLastLayer S Cw
  calc
    (S.deepLinearOutputLaw Cw x).map (fun z : Fin dOut → ℝ => -z)
        = (μ₀.map F).map (fun z : Fin dOut → ℝ => -z) := rfl
    _ = μ₀.map (fun θ : S.Params => -F θ) :=
          Measure.map_map (g := fun z : Fin dOut → ℝ => -z) (f := F)
            (by fun_prop : Measurable fun z : Fin dOut → ℝ => -z) hF_meas
    _ = μ₀.map (fun θ : S.Params => F (negLastLayer S θ)) := by
          congr 1
          funext θ
          exact (eval_negLastLayer S θ x).symm
    _ = (μ₀.map (negLastLayer S)).map F := (Measure.map_map hF_meas hJ_meas).symm
    _ = μ₀.map F := by
          rw [hJ_inv]
    _ = S.deepLinearOutputLaw Cw x := rfl
  ⟩

-- The monomial `z ↦ ∏ r, z (a r)` in coordinate projections is measurable: each coordinate
-- projection is measurable and finite products of measurable functions are measurable.
private lemma measurable_monomial {κ : Type*} {n : ℕ} (a : Fin n → κ) :
    Measurable (fun z : κ → ℝ => ∏ r : Fin n, z (a r)) :=
  Finset.measurable_prod Finset.univ (fun r _ => measurable_pi_apply (a r))

-- A monomial of odd degree is an odd function of its arguments: negating the vector `z` negates
-- the whole product.  `Finset.prod_neg` factors out `(-1) ^ n`, and `Odd.neg_one_pow` collapses
-- that factor to `-1` because `n` is odd.
private lemma odd_monomial_neg {κ : Type*} {n : ℕ} (hn : Odd n) (a : Fin n → κ) (z : κ → ℝ) :
    (∏ r : Fin n, (-z) (a r)) = -∏ r : Fin n, z (a r) := by
  simpa [Fintype.card_fin, hn.neg_one_pow] using
    Finset.prod_neg (s := Finset.univ) (f := fun r : Fin n => z (a r))

/-- Every odd joint output moment vanishes.

Informal proof: condition on the penultimate layer.  The final output row is a centered Gaussian,
so its odd Wick moment is zero; integrating this zero conditional moment proves the claim.  The
base case is `Renormalization.integral_pow_gaussianReal_odd`.  Source:
`docs/Renormalization.md`, final paragraphs of Section `sec:DLN`.
-/
theorem jointMoment_outputLaw_odd {dIn dOut : ℕ} (S : MLPShape dIn dOut)
    (Cw : ℝ≥0) (x : Fin dIn → ℝ) (m : ℕ) (a : Fin (2 * m + 1) → Fin dOut)
    (_hIn : 0 < dIn) (_hWidths : ∀ n ∈ S.hiddenWidths, 0 < n) :
    ∫ z, (∏ r, z (a r)) ∂S.deepLinearOutputLaw Cw x = 0 := by
  let F : (Fin dOut → ℝ) → ℝ := fun z => ∏ r, z (a r)
  let : Measure.IsNegInvariant (S.deepLinearOutputLaw Cw x) :=
    deepLinearOutputLaw_isNegInvariant S Cw x
  have hF : AEStronglyMeasurable F (S.deepLinearOutputLaw Cw x) :=
    (measurable_monomial a).aestronglyMeasurable
  have hodd : ∀ z : Fin dOut → ℝ, F (-z) = -F z :=
    fun z => odd_monomial_neg (hn := odd_two_mul_add_one m) (a := a) (z := z)
  exact Renormalization.integral_eq_zero_of_odd_of_aestronglyMeasurable
    (S.deepLinearOutputLaw Cw x) hF hodd

/-- The law of one freshly initialized bias-free layer is a product of independent scalar
Gaussians with variance `Cw * normalizedEnergy x`.

Informal proof: specialize `map_batchPreactivation` to a singleton batch.  The singleton Gram
identity `NeuralNetwork.normalizedGram_singleton` identifies every output coordinate with a
centered Gaussian of variance `s = (Cw : ℝ) * normalizedEnergy x`, and different output
coordinates are independent because `map_batchPreactivation` gives a product measure over the
output type.  Projecting the singleton Euclidean coordinates back to `ℝ` via `PUnit.unit`
(`measurePreserving_eval_multivariateGaussian`) yields `gaussianReal 0 s` per coordinate.  This is
the product-form specialization of `oneLayerOutputLaw_eq_map_stdGaussian`; source:
`docs/Renormalization.md`, equation `eq:deep-linear-gaussian-first-layer`.
-/
private lemma oneLayerOutputLaw_eq_pi_gaussianReal {dIn dOut : ℕ} (Cw : ℝ≥0)
    (x : Fin dIn → ℝ) :
    oneLayerOutputLaw (ι := Fin dIn) (κ := Fin dOut) Cw x =
      Measure.pi (fun _ : Fin dOut =>
        gaussianReal 0 (Cw * NeuralNetwork.normalizedEnergyNNReal x)) := by
  classical
  let s : ℝ := (Cw : ℝ) * NeuralNetwork.normalizedEnergy x
  have hs : 0 ≤ s := by
    dsimp [s]
    exact mul_nonneg Cw.property (NeuralNetwork.normalizedEnergy_nonneg x)
  let ν : Measure (EuclideanSpace ℝ PUnit.{1}) :=
    multivariateGaussian 0 (fun _ _ : PUnit.{1} => s)
  let evalV : EuclideanSpace ℝ PUnit.{1} → ℝ := fun v => v PUnit.unit
  let g : (Fin dOut → EuclideanSpace ℝ PUnit) → Fin dOut → ℝ :=
    fun v j => (v j) PUnit.unit
  have hEval_meas : Measurable evalV := by
    dsimp [evalV]
    fun_prop
  have hT_meas : Measurable (fun y : ℝ =>
      (EuclideanSpace.equiv PUnit ℝ).symm (fun _ : PUnit => y)) := by
    have hcont : Continuous (fun y : ℝ =>
        (EuclideanSpace.equiv PUnit ℝ).symm (fun _ : PUnit => y)) := by
      exact (EuclideanSpace.equiv PUnit ℝ).symm.continuous.comp
        (continuous_pi fun _ : PUnit => continuous_id)
    exact hcont.measurable
  have hT_inv (y : ℝ) :
      ((EuclideanSpace.equiv PUnit ℝ).symm (fun _ : PUnit => y)) PUnit.unit = y := by
    simp [EuclideanSpace.equiv, WithLp.ofLp_toLp]
  -- Step 1: the singleton-batch Euclidean law is a product of one-dimensional
  -- multivariate Gaussians with constant covariance `s`.
  have hmat : (fun a b : PUnit.{1} =>
        (Cw : ℝ) * NeuralNetwork.normalizedGram (fun _ : PUnit.{1} => x) a b) =
      fun _ _ : PUnit.{1} => s := by
    funext a b
    cases a
    cases b
    simp [s, NeuralNetwork.normalizedGram_singleton]
  have hA : Measure.map (fun q : LayerParams (Fin dIn) (Fin dOut) =>
          fun j : Fin dOut => (EuclideanSpace.equiv PUnit ℝ).symm
            (fun _ : PUnit => (DenseLayer.ofParams q).preactivation x j))
        (layerGaussianInit (hyperparams Cw) (Fin dIn) (Fin dOut)) =
      Measure.pi (fun _ : Fin dOut => ν) := by
    calc
      Measure.map (fun q : LayerParams (Fin dIn) (Fin dOut) =>
          fun j : Fin dOut => (EuclideanSpace.equiv PUnit ℝ).symm
            (fun _ : PUnit => (DenseLayer.ofParams q).preactivation x j))
          (layerGaussianInit (hyperparams Cw) (Fin dIn) (Fin dOut))
          = Measure.pi (fun _ : Fin dOut =>
              multivariateGaussian 0 (fun a b : PUnit =>
                (Cw : ℝ) * NeuralNetwork.normalizedGram (fun _ : PUnit => x) a b)) := by
            simpa [batchToEuclidean, batchPreactivation] using
              map_batchPreactivation (A := PUnit.{1}) (κ := Fin dOut) (Cw := Cw)
                (x := fun _ : PUnit.{1} => x)
      _ = Measure.pi (fun _ : Fin dOut => ν) := by
            rw [hmat]
  -- Step 2: recover the real outputs from the Euclidean-embedded law.
  have hz_meas : Measurable (fun q : LayerParams (Fin dIn) (Fin dOut) =>
      fun j : Fin dOut => (DenseLayer.ofParams q).preactivation x j) := by
    dsimp [DenseLayer.preactivation, DenseLayer.ofParams, Matrix.mulVec]
    fun_prop
  have hf_meas : Measurable (fun q : LayerParams (Fin dIn) (Fin dOut) =>
      fun j : Fin dOut => (EuclideanSpace.equiv PUnit ℝ).symm
        (fun _ : PUnit => (DenseLayer.ofParams q).preactivation x j)) := by
    have h1 : Measurable (fun v : Fin dOut → ℝ =>
        fun j : Fin dOut => (EuclideanSpace.equiv PUnit ℝ).symm (fun _ : PUnit => v j)) := by
      refine measurable_pi_lambda _ (fun j => ?_)
      exact hT_meas.comp (measurable_pi_apply j)
    exact h1.comp hz_meas
  have hg_meas : Measurable g := by
    dsimp [g]
    refine measurable_pi_lambda _ (fun j => ?_)
    exact hEval_meas.comp (measurable_pi_apply j)
  have hcomp : g ∘
      (fun q : LayerParams (Fin dIn) (Fin dOut) => fun j : Fin dOut =>
        (EuclideanSpace.equiv PUnit ℝ).symm
          (fun _ : PUnit => (DenseLayer.ofParams q).preactivation x j)) =
    fun q : LayerParams (Fin dIn) (Fin dOut) => fun j : Fin dOut =>
      (DenseLayer.ofParams q).preactivation x j := by
    funext q j
    dsimp [g]
    exact hT_inv _
  have hLaw : oneLayerOutputLaw (ι := Fin dIn) (κ := Fin dOut) Cw x =
      Measure.map g (Measure.pi (fun _ : Fin dOut => ν)) := by
    calc
      oneLayerOutputLaw (ι := Fin dIn) (κ := Fin dOut) Cw x
          = Measure.map (fun q : LayerParams (Fin dIn) (Fin dOut) =>
              fun j : Fin dOut => (DenseLayer.ofParams q).preactivation x j)
              (layerGaussianInit (hyperparams Cw) (Fin dIn) (Fin dOut)) := rfl
      _ = Measure.map g
            (Measure.map (fun q : LayerParams (Fin dIn) (Fin dOut) =>
                fun j : Fin dOut => (EuclideanSpace.equiv PUnit ℝ).symm
                  (fun _ : PUnit => (DenseLayer.ofParams q).preactivation x j))
              (layerGaussianInit (hyperparams Cw) (Fin dIn) (Fin dOut))) := by
            rw [Measure.map_map hg_meas hf_meas, hcomp]
      _ = Measure.map g (Measure.pi (fun _ : Fin dOut => ν)) := by
            rw [hA]
  -- Step 3: project the product law coordinatewise.
  have hProj : Measure.map g (Measure.pi (fun _ : Fin dOut => ν)) =
    Measure.pi (fun _ : Fin dOut => ν.map evalV) := by
    have hgauss : ProbabilityTheory.IsGaussian ν :=
      ProbabilityTheory.isGaussian_multivariateGaussian
        (μ := (0 : EuclideanSpace ℝ PUnit.{1})) (S := (fun _ _ : PUnit.{1} => s))
    have hprob : MeasureTheory.IsProbabilityMeasure ν := by
      change MeasureTheory.IsProbabilityMeasure
        (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ PUnit.{1})
          (fun _ _ : PUnit.{1} => s))
      exact @ProbabilityTheory.IsGaussian.toIsProbabilityMeasure (EuclideanSpace ℝ PUnit.{1})
        _ _ _ _ _ hgauss
    have hIndep : iIndepFun
        (fun j : Fin dOut => fun v : Fin dOut → EuclideanSpace ℝ PUnit.{1} => (v j) PUnit.unit)
        (Measure.pi (fun _ : Fin dOut => ν)) := by
      simpa using
        (@iIndepFun_pi (Fin dOut) _ (fun _ : Fin dOut => EuclideanSpace ℝ PUnit.{1}) _
          (fun _ : Fin dOut => ν) (fun _ => hprob) (fun _ : Fin dOut => ℝ) _
          (fun _ : Fin dOut => evalV) (fun j => hEval_meas.aemeasurable))
    have hmap := @iIndepFun.map_fun_eq_pi_map
      (Fin dOut → EuclideanSpace ℝ PUnit.{1}) (Fin dOut) _
      (Measure.pi (fun _ : Fin dOut => ν)) _ (fun _ : Fin dOut => ℝ) _
      (fun (j : Fin dOut) (v : Fin dOut → EuclideanSpace ℝ PUnit.{1}) => (v j) PUnit.unit)
      (fun j => (hEval_meas.comp (measurable_pi_apply j)).aemeasurable) hIndep
    calc
      Measure.map g (Measure.pi (fun _ : Fin dOut => ν))
          = Measure.pi (fun j : Fin dOut => (Measure.pi (fun _ : Fin dOut => ν)).map
              (fun v : Fin dOut → EuclideanSpace ℝ PUnit => (v j) PUnit.unit)) := hmap
      _ = Measure.pi (fun _ : Fin dOut => ν.map evalV) := by
            congr 1
            funext j
            calc
              (Measure.pi (fun _ : Fin dOut => ν)).map
                  (fun v : Fin dOut → EuclideanSpace ℝ PUnit => (v j) PUnit.unit)
                  = (Measure.pi (fun _ : Fin dOut => ν)).map
                      (evalV ∘ (fun v : Fin dOut → EuclideanSpace ℝ PUnit => v j)) := rfl
              _ = ((Measure.pi (fun _ : Fin dOut => ν)).map
                    (fun v : Fin dOut → EuclideanSpace ℝ PUnit => v j)).map evalV := by
                    rw [Measure.map_map hEval_meas (measurable_pi_apply j)]
              _ = ν.map evalV := by
                    rw [(@measurePreserving_eval (Fin dOut)
                      (fun _ : Fin dOut => EuclideanSpace ℝ PUnit.{1}) _ _
                      (fun _ : Fin dOut => ν) (fun _ => hprob) j).map_eq]
  -- Step 4: each projected coordinate has law `gaussianReal 0 s`.
  have hν_proj : ν.map evalV = gaussianReal 0 ⟨s, hs⟩ := by
    let S₀ : Matrix PUnit.{1} PUnit.{1} ℝ := fun _ _ => s
    have hS₀ : S₀.PosSemidef := by
      have hdecomp : S₀ = Matrix.vecMulVec (fun _ : PUnit => Real.sqrt s)
          (star (fun _ : PUnit => Real.sqrt s)) := by
        ext a b
        change s = Real.sqrt s * star (Real.sqrt s)
        rw [star_trivial]
        exact (Real.mul_self_sqrt hs).symm
      rw [hdecomp]
      exact Matrix.posSemidef_vecMulVec_self_star (fun _ : PUnit => Real.sqrt s)
    have hEvalGauss := measurePreserving_eval_multivariateGaussian
      (μ := (0 : EuclideanSpace ℝ PUnit)) (S := S₀) hS₀ (i := PUnit.unit)
    have hstep1 : (multivariateGaussian 0 S₀).map evalV =
        gaussianReal ((0 : EuclideanSpace ℝ PUnit.{1}) PUnit.unit.{1})
          (S₀ PUnit.unit.{1} PUnit.unit.{1}).toNNReal :=
      hEvalGauss.map_eq
    have hstep2 : gaussianReal ((0 : EuclideanSpace ℝ PUnit.{1}) PUnit.unit.{1})
        (S₀ PUnit.unit.{1} PUnit.unit.{1}).toNNReal = gaussianReal 0 ⟨s, hs⟩ := by
      congr 1
      · dsimp [S₀]
        exact Real.toNNReal_of_nonneg hs
    calc
      ν.map evalV = (multivariateGaussian 0 S₀).map evalV := rfl
      _ = gaussianReal 0 ⟨s, hs⟩ := by
            rw [hstep1, hstep2]
  have hν : ν.map evalV = gaussianReal 0 (Cw * NeuralNetwork.normalizedEnergyNNReal x) := by
    have hNN : (⟨s, hs⟩ : ℝ≥0) = Cw * NeuralNetwork.normalizedEnergyNNReal x := by
      apply Subtype.ext
      change s = (Cw : ℝ) * NeuralNetwork.normalizedEnergy x
      dsimp [s]
    rw [hν_proj, hNN]
  calc
    oneLayerOutputLaw (ι := Fin dIn) (κ := Fin dOut) Cw x
        = Measure.map g (Measure.pi (fun _ : Fin dOut => ν)) := hLaw
    _ = Measure.pi (fun _ : Fin dOut => ν.map evalV) := hProj
    _ = Measure.pi (fun _ : Fin dOut =>
          gaussianReal 0 (Cw * NeuralNetwork.normalizedEnergyNNReal x)) := by
          congr 1
          funext j
          exact hν

/-- Scaling a centered real Gaussian by `Real.sqrt (v : ℝ)` produces variance `v`. -/
private lemma gaussianReal_scaling (v : ℝ≥0) :
    gaussianReal 0 v = (gaussianReal 0 1).map (fun y : ℝ => Real.sqrt (v : ℝ) * y) := by
  have h := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (c := Real.sqrt (v : ℝ))
  calc
    gaussianReal 0 v = gaussianReal (Real.sqrt (v : ℝ) * 0)
        (⟨(Real.sqrt (v : ℝ)) ^ 2, sq_nonneg (Real.sqrt (v : ℝ))⟩ * (1 : ℝ≥0)) := by
          congr 1
          · ring
          · apply Subtype.ext
            change (v : ℝ) = (Real.sqrt (v : ℝ) ^ 2) * 1
            calc
              (v : ℝ) = (Real.sqrt (v : ℝ)) ^ 2 := (Real.sq_sqrt v.property).symm
              _ = (Real.sqrt (v : ℝ)) ^ 2 * 1 := by ring
    _ = (gaussianReal 0 1).map (fun y : ℝ => Real.sqrt (v : ℝ) * y) := h.symm

/-- A monomial in the coordinates of the standard multivariate Gaussian is its Wick pairing sum.

Informal proof: apply the coordinate Wick theorem
`Renormalization.integral_prod_multivariateGaussian_centered_eq_wick` to the identity covariance
matrix; each coordinate projection has mean zero and covariance `if i = j then 1 else 0`. -/
private lemma integral_stdGaussian_monomial_eq_wick {κ : Type uJ} [Fintype κ] [DecidableEq κ]
    (m : ℕ) (a : Fin (2 * m) → κ) :
    ∫ x : EuclideanSpace ℝ κ, (∏ r : Fin (2 * m), x (a r)) ∂stdGaussian (EuclideanSpace ℝ κ) =
      pairingTensor a := by
  classical
  have hS : (1 : Matrix κ κ ℝ).PosSemidef := Matrix.PosSemidef.one
  have hWick := Renormalization.integral_prod_multivariateGaussian_centered_eq_wick
    (m := (0 : EuclideanSpace ℝ κ)) (S := (1 : Matrix κ κ ℝ)) (hS := hS) (index := a)
  have hInt : ∫ x : EuclideanSpace ℝ κ, (∏ r : Fin (2 * m), x (a r))
      ∂multivariateGaussian (0 : EuclideanSpace ℝ κ) (1 : Matrix κ κ ℝ) =
    Renormalization.wick (fun r q : Fin (2 * m) => (1 : Matrix κ κ ℝ) (a r) (a q)) Finset.univ := by
    -- unfold the joint moment and drop the zero mean
    simpa [Renormalization.jointMoment, Renormalization.blockMoment] using hWick
  calc
    ∫ x : EuclideanSpace ℝ κ, (∏ r : Fin (2 * m), x (a r)) ∂stdGaussian (EuclideanSpace ℝ κ)
        = ∫ x : EuclideanSpace ℝ κ, (∏ r : Fin (2 * m), x (a r))
            ∂multivariateGaussian (0 : EuclideanSpace ℝ κ) (1 : Matrix κ κ ℝ) := by
            rw [← multivariateGaussian_zero_one]
    _ = Renormalization.wick (fun r q : Fin (2 * m) => (1 : Matrix κ κ ℝ) (a r) (a q))
          Finset.univ := hInt
    _ = Renormalization.wick (fun r q : Fin (2 * m) => if a r = a q then 1 else 0)
          Finset.univ := by
          have hk : (fun r q : Fin (2 * m) => (1 : Matrix κ κ ℝ) (a r) (a q)) =
              (fun r q : Fin (2 * m) => if a r = a q then 1 else 0) := by
            funext r q
            rw [Matrix.one_apply]
          rw [hk]
    _ = pairingTensor a := rfl

/-- The monomial integral over the product of standard Gaussians is the Wick pairing sum. -/
private lemma integral_pi_stdGaussian_monomial_eq_pairingTensor {κ : Type uJ} [Fintype κ]
    [DecidableEq κ] (m : ℕ) (a : Fin (2 * m) → κ) :
    ∫ z, (∏ r, z (a r)) ∂Measure.pi (fun _ : κ => gaussianReal 0 1) =
      pairingTensor a := by
  classical
  have hφ_meas : AEMeasurable (fun u : κ → ℝ => WithLp.toLp 2 u)
      (Measure.pi (fun _ : κ => gaussianReal 0 1)) := by
    fun_prop
  have hG_meas : AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ κ => ∏ r : Fin (2 * m), x (a r))
      (Measure.map (fun u : κ → ℝ => WithLp.toLp 2 u)
        (Measure.pi (fun _ : κ => gaussianReal 0 1))) := by
    have hcont : Continuous (fun x : EuclideanSpace ℝ κ => ∏ r : Fin (2 * m), x (a r)) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  have hstep : ∫ x : EuclideanSpace ℝ κ, (∏ r : Fin (2 * m), x (a r))
        ∂stdGaussian (EuclideanSpace ℝ κ) =
      ∫ z, (∏ r : Fin (2 * m), z (a r)) ∂Measure.pi (fun _ : κ => gaussianReal 0 1) := by
    rw [← map_pi_eq_stdGaussian (ι := κ)]
    exact MeasureTheory.integral_map
      (φ := fun u : κ → ℝ => WithLp.toLp 2 u) hφ_meas
      (f := fun x : EuclideanSpace ℝ κ => ∏ r : Fin (2 * m), x (a r)) hG_meas
  exact (hstep.symm.trans (integral_stdGaussian_monomial_eq_wick m a))

/-- Wick/Isserlis theorem for a product of independent centered one-dimensional Gaussians with
common variance `v`.

Informal proof: identify the product law with the centered multivariate Gaussian whose covariance
matrix is `Matrix.diagonal (fun _ => (v : ℝ))`.  Then apply the coordinate Wick theorem
`Renormalization.integral_prod_multivariateGaussian_centered_eq_wick`.  Each covariance entry is
`(v : ℝ) * if i = j then 1 else 0`; every pairing has exactly `m` pairs, so the common factor
`(v : ℝ) ^ m` factors out, leaving exactly `pairingTensor a`.  This is Isserlis' theorem for
independent coordinates; see <https://en.wikipedia.org/wiki/Isserlis%27s_theorem>.
-/
private lemma integral_prod_pi_gaussianReal_eq_pairingTensor
    {κ : Type uJ} [Fintype κ] [DecidableEq κ] (v : ℝ≥0) (m : ℕ)
    (a : Fin (2 * m) → κ) :
    ∫ z, (∏ r, z (a r)) ∂Measure.pi (fun _ : κ => gaussianReal 0 v) =
      pairingTensor a * (v : ℝ) ^ m := by
  classical
  -- Step 1: reduce to the standard Gaussian (v = 1) by rescaling each coordinate.
  have hscale_pi : Measure.pi (fun _ : κ => gaussianReal 0 v) =
      (Measure.pi (fun _ : κ => gaussianReal 0 1)).map
        (fun z : κ → ℝ => fun i => Real.sqrt (v : ℝ) * z i) := by
    rw [MeasureTheory.Measure.pi_map_pi
      (μ := fun _ : κ => gaussianReal 0 1)
      (f := fun _ : κ => fun y : ℝ => Real.sqrt (v : ℝ) * y)
      (hf := fun i => (by fun_prop : AEMeasurable (fun y : ℝ => Real.sqrt (v : ℝ) * y)
        (gaussianReal 0 1)))]
    congr 1
    funext i
    exact gaussianReal_scaling v
  have hφ_meas : AEMeasurable (fun z : κ → ℝ => fun i : κ => Real.sqrt (v : ℝ) * z i)
      (Measure.pi (fun _ : κ => gaussianReal 0 1)) := by
    refine (measurable_pi_lambda _ (fun i => ?_)).aemeasurable
    fun_prop
  have hG_meas : AEStronglyMeasurable
      (fun z : κ → ℝ => ∏ r : Fin (2 * m), z (a r))
      (Measure.map (fun z : κ → ℝ => fun i : κ => Real.sqrt (v : ℝ) * z i)
        (Measure.pi (fun _ : κ => gaussianReal 0 1))) := by
    have hcont : Continuous (fun z : κ → ℝ => ∏ r : Fin (2 * m), z (a r)) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  have hprod : ∀ u : κ → ℝ,
      (∏ r : Fin (2 * m), Real.sqrt (v : ℝ) * u (a r)) =
        (Real.sqrt (v : ℝ)) ^ (2 * m) * (∏ r : Fin (2 * m), u (a r)) := by
    intro u
    calc
      (∏ r : Fin (2 * m), Real.sqrt (v : ℝ) * u (a r))
          = (∏ r : Fin (2 * m), Real.sqrt (v : ℝ)) * (∏ r : Fin (2 * m), u (a r)) := by
            rw [Finset.prod_mul_distrib]
      _ = (Real.sqrt (v : ℝ)) ^ (2 * m) * (∏ r : Fin (2 * m), u (a r)) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    ∫ z, (∏ r, z (a r)) ∂Measure.pi (fun _ : κ => gaussianReal 0 v)
        = ∫ z, (∏ r, z (a r))
            ∂(Measure.pi (fun _ : κ => gaussianReal 0 1)).map
              (fun z : κ → ℝ => fun i => Real.sqrt (v : ℝ) * z i) := by
            rw [hscale_pi]
    _ = ∫ u : κ → ℝ, (∏ r : Fin (2 * m), Real.sqrt (v : ℝ) * u (a r))
          ∂Measure.pi (fun _ : κ => gaussianReal 0 1) := by
          exact MeasureTheory.integral_map
            (φ := fun z : κ → ℝ => fun i : κ => Real.sqrt (v : ℝ) * z i) hφ_meas
            (f := fun z : κ → ℝ => ∏ r : Fin (2 * m), z (a r)) hG_meas
    _ = (Real.sqrt (v : ℝ)) ^ (2 * m) *
          ∫ u : κ → ℝ, (∏ r : Fin (2 * m), u (a r))
            ∂Measure.pi (fun _ : κ => gaussianReal 0 1) := by
          simp_rw [hprod]
          rw [MeasureTheory.integral_const_mul]
    _ = (Real.sqrt (v : ℝ)) ^ (2 * m) * pairingTensor a := by
          rw [integral_pi_stdGaussian_monomial_eq_pairingTensor m a]
    _ = pairingTensor a * (v : ℝ) ^ m := by
          have hpow2 : (Real.sqrt (v : ℝ)) ^ (2 * m) = (v : ℝ) ^ m := by
            calc
              (Real.sqrt (v : ℝ)) ^ (2 * m) = ((Real.sqrt (v : ℝ)) ^ 2) ^ m := by
                rw [pow_mul]
              _ = (v : ℝ) ^ m := by
                exact congrArg (fun t : ℝ => t ^ m) (Real.sq_sqrt v.property)
          rw [hpow2]
          ring

/-- Base case of `jointMoment_outputLaw_even`: a single bias-free Gaussian layer.

Informal proof: `deepLinearOutputLaw` for `MLPShape.output` is exactly `oneLayerOutputLaw`.
That law is a product of centered real Gaussians with variance
`(Cw : ℝ) * NeuralNetwork.normalizedEnergy x`; Wick/Isserlis then gives the Kronecker pairing sum
`pairingTensor a` and one variance factor for each of the `m` pairs.  The hidden-width list is
empty, so `correlatorAmplitude` reduces to `((Cw : ℝ) * normalizedEnergy x) ^ m`.
Source: Wick's theorem, <https://en.wikipedia.org/wiki/Isserlis%27s_theorem>, and the one-layer
law API in `GaussianLayer.lean`.
-/
private lemma jointMoment_outputLaw_output_even {dIn dOut : ℕ}
    (Cw : ℝ≥0) (x : Fin dIn → ℝ) (m : ℕ) (a : Fin (2 * m) → Fin dOut)
    (_hIn : 0 < dIn) :
    ∫ z, (∏ r, z (a r))
        ∂(MLPShape.output : MLPShape dIn dOut).deepLinearOutputLaw Cw x =
      pairingTensor a *
        correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy x) m
          (MLPShape.output : MLPShape dIn dOut).hiddenWidths := by
  -- Step 1: reduce the output law of one bias-free layer to a product of scalar Gaussians.
  -- This is exactly `firstLayerOutputLaw_eq_pi_gaussianReal`, which is declared later in this
  -- file; keeping it as a local explicit step avoids hiding the probabilistic reduction.
  have hLaw : (MLPShape.output : MLPShape dIn dOut).deepLinearOutputLaw Cw x =
      Measure.pi (fun _ : Fin dOut =>
        gaussianReal 0 (Cw * NeuralNetwork.normalizedEnergyNNReal x)) := by
    change oneLayerOutputLaw (ι := Fin dIn) (κ := Fin dOut) Cw x =
      Measure.pi (fun _ : Fin dOut =>
        gaussianReal 0 (Cw * NeuralNetwork.normalizedEnergyNNReal x))
    exact oneLayerOutputLaw_eq_pi_gaussianReal Cw x
  rw [hLaw]
  -- Step 2: apply the reusable product-Gaussian Wick theorem, then normalize the deterministic
  -- amplitude for the output shape (`hiddenWidths = []`).
  calc
    ∫ z, (∏ r, z (a r))
        ∂Measure.pi (fun _ : Fin dOut =>
          gaussianReal 0 (Cw * NeuralNetwork.normalizedEnergyNNReal x)) =
        pairingTensor a * ((Cw * NeuralNetwork.normalizedEnergyNNReal x : ℝ≥0) : ℝ) ^ m :=
      integral_prod_pi_gaussianReal_eq_pairingTensor
        (κ := Fin dOut) (v := Cw * NeuralNetwork.normalizedEnergyNNReal x) m a
    _ = pairingTensor a *
        correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy x) m
          (MLPShape.output : MLPShape dIn dOut).hiddenWidths := by
      have hAmp : ((Cw * NeuralNetwork.normalizedEnergyNNReal x : ℝ≥0) : ℝ) ^ m =
          correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy x) m
            (MLPShape.output : MLPShape dIn dOut).hiddenWidths := by
        simp only [normalizedEnergyNNReal, correlatorAmplitude, MLPShape.hiddenWidths,
          MLPShape.widths, List.tail_cons, List.dropLast_singleton, List.length_nil, zero_add,
          pow_one, hiddenWidthCorrection, List.map_nil, List.prod_nil, mul_one]
        change ((Cw : ℝ) * NeuralNetwork.normalizedEnergy x) ^ m =
          ((Cw : ℝ) * NeuralNetwork.normalizedEnergy x) ^ m
        rfl
      exact congrArg (fun t : ℝ => pairingTensor a * t) hAmp

/-- Monomials in the outputs of a single bias-free Gaussian layer are integrable.

Informal proof: the one-layer output law is a product of centered scalar Gaussians, so every
output coordinate lies in every `L^p`; the monomial is then bounded by a power-mean combination
of the coordinate `2m`-th powers, each of which is integrable by the finite Gaussian moments
(`ProbabilityTheory.memLp_id_gaussianReal'`). -/
private lemma integrable_monomial_outputLaw_even {dIn dOut : ℕ}
    (Cw : ℝ≥0) (x : Fin dIn → ℝ) (m : ℕ) (a : Fin (2 * m) → Fin dOut) :
    Integrable (fun z => ∏ r, z (a r))
      ((MLPShape.output : MLPShape dIn dOut).deepLinearOutputLaw Cw x) := by
  classical
  by_cases hm : m = 0
  · subst m
    have hIsProb : IsProbabilityMeasure
        ((MLPShape.output : MLPShape dIn dOut).deepLinearOutputLaw Cw x) := by
      unfold MLPShape.deepLinearOutputLaw
      exact Measure.isProbabilityMeasure_map
        (((MLPShape.output : MLPShape dIn dOut).measurable_eval (measurable_linear 1)).comp
          (measurable_id.prodMk measurable_const)).aemeasurable
    have hFin : IsFiniteMeasure
        ((MLPShape.output : MLPShape dIn dOut).deepLinearOutputLaw Cw x) :=
      ⟨by rw [hIsProb.measure_univ]; norm_num⟩
    have h1 : (fun z : Fin dOut → ℝ => ∏ r : Fin 0, z (a r)) = fun _ => (1 : ℝ) := by
      funext z
      simp
    rw [h1]
    exact @integrable_const (Fin dOut → ℝ) ℝ _ _
      (by infer_instance : NormedAddCommGroup ℝ)
      hFin (1 : ℝ)
  · have hmpos : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm)
    let v : ℝ≥0 := Cw * NeuralNetwork.normalizedEnergyNNReal x
    let π : Measure (Fin dOut → ℝ) := Measure.pi (fun _ : Fin dOut => gaussianReal 0 v)
    have hLaw : (MLPShape.output : MLPShape dIn dOut).deepLinearOutputLaw Cw x = π := by
      change oneLayerOutputLaw (ι := Fin dIn) (κ := Fin dOut) Cw x = π
      exact oneLayerOutputLaw_eq_pi_gaussianReal Cw x
    rw [hLaw]
    have hmemCoord (j : Fin dOut) :
        MemLp (fun z : Fin dOut → ℝ => z j) ((2 * m : ℕ) : ℝ≥0∞) π := by
      dsimp [π]
      simpa using (MemLp.comp_measurePreserving
        (memLp_id_gaussianReal' ((2 * m : ℕ) : ℝ≥0∞) (ENNReal.natCast_ne_top (2 * m)))
        (measurePreserving_eval (fun _ : Fin dOut => gaussianReal 0 v) j))
    have hIntCoord (j : Fin dOut) :
        Integrable (fun z : Fin dOut → ℝ => z j ^ (2 * m)) π := by
      have hint : Integrable (fun z : Fin dOut → ℝ => ‖z j‖ ^ (2 * m)) π := by
        exact (hmemCoord j).integrable_norm_pow'
      refine Integrable.mono' hint ?_ (Filter.Eventually.of_forall ?_)
      · exact (((measurable_pi_apply j).pow_const (2 * m))).aestronglyMeasurable
      · intro z
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
    have hsum : Integrable (fun z : Fin dOut → ℝ =>
        ∑ j : Fin dOut, z j ^ (2 * m)) π := by
      simpa using (integrable_finsetSum Finset.univ (μ := π)
        (f := fun (j : Fin dOut) (z : Fin dOut → ℝ) => z j ^ (2 * m)) (fun j _ => hIntCoord j))
    let C : ℝ := (Fintype.card (Fin dOut) : ℝ) ^ (m - 1)
    have hbound : ∀ z : Fin dOut → ℝ,
        ‖∏ r : Fin (2 * m), z (a r)‖ ≤ C * ∑ j : Fin dOut, z j ^ (2 * m) := by
      intro z
      have hprod : |∏ r : Fin (2 * m), z (a r)| ≤ (∑ j : Fin dOut, z j ^ 2) ^ m := by
        have hle (r : Fin (2 * m)) : |z (a r)| ≤ Real.sqrt (∑ j : Fin dOut, z j ^ 2) := by
          calc
            |z (a r)| = Real.sqrt (z (a r) ^ 2) := by rw [Real.sqrt_sq_eq_abs]
            _ ≤ Real.sqrt (∑ j : Fin dOut, z j ^ 2) := Real.sqrt_le_sqrt
              (Finset.single_le_sum (f := fun j : Fin dOut => z j ^ 2)
                (fun j _ => sq_nonneg (z j)) (Finset.mem_univ (a r)))
        calc
          |∏ r : Fin (2 * m), z (a r)| = ∏ r : Fin (2 * m), |z (a r)| := by
            rw [Finset.abs_prod]
          _ ≤ ∏ r : Fin (2 * m), Real.sqrt (∑ j : Fin dOut, z j ^ 2) := by
            exact Finset.prod_le_prod (fun r _ => abs_nonneg _) (fun r _ => hle r)
          _ = (Real.sqrt (∑ j : Fin dOut, z j ^ 2)) ^ (2 * m) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ = (∑ j : Fin dOut, z j ^ 2) ^ m := by
            rw [pow_mul, Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (z j)))]
      have hpm := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
        (s := (Finset.univ : Finset (Fin dOut)))
        (f := fun j : Fin dOut => z j ^ 2)
        (p := (m : ℝ)) (hp := by exact_mod_cast hmpos) (hf := fun j _ => sq_nonneg (z j))
      have hpm' : (∑ j : Fin dOut, z j ^ 2) ^ m ≤ C * ∑ j : Fin dOut, z j ^ (2 * m) := by
        have hpm2 : (∑ j : Fin dOut, z j ^ 2) ^ (m : ℝ) ≤
            (Fintype.card (Fin dOut) : ℝ) ^ ((m : ℝ) - 1) *
              ∑ j : Fin dOut, (z j ^ 2) ^ (m : ℝ) := by
          simpa [Finset.card_univ, Fintype.card_fin] using hpm
        calc
          (∑ j : Fin dOut, z j ^ 2) ^ m = (∑ j : Fin dOut, z j ^ 2) ^ (m : ℝ) := by
            rw [Real.rpow_natCast]
          _ ≤ (Fintype.card (Fin dOut) : ℝ) ^ ((m : ℝ) - 1) *
              ∑ j : Fin dOut, (z j ^ 2) ^ (m : ℝ) := hpm2
          _ = C * ∑ j : Fin dOut, z j ^ (2 * m) := by
            have hexp : ((m : ℝ) - 1) = ((m - 1 : ℕ) : ℝ) := by
              rw [Nat.cast_sub hmpos]
              norm_num
            rw [hexp, Real.rpow_natCast]
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            rw [Real.rpow_natCast]
            simp [← pow_mul]
      calc
        ‖∏ r : Fin (2 * m), z (a r)‖ = |∏ r : Fin (2 * m), z (a r)| := by
          rw [Real.norm_eq_abs]
        _ ≤ (∑ j : Fin dOut, z j ^ 2) ^ m := hprod
        _ ≤ C * ∑ j : Fin dOut, z j ^ (2 * m) := hpm'
    refine Integrable.mono' (hsum.const_mul C) ?_ (Filter.Eventually.of_forall ?_)
    · exact (measurable_monomial a).aestronglyMeasurable
    · intro z
      exact hbound z

/-- The linear activation is the identity, so activating equals preactivating. -/
private lemma activate_linear_eq_preactivation {ι κ : Type*} [Fintype ι]
    (q : LayerParams ι κ) (x : ι → ℝ) :
    (DenseLayer.ofParams q).activate (linear 1) x = (DenseLayer.ofParams q).preactivation x := by
  funext j
  simp [DenseLayer.activate, linear]

/-- A single weight coordinate of a freshly initialized bias-free layer is in every `L^p`. -/
private lemma integrable_pow_weight_coord {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Cw : ℝ≥0) (p : ℕ) (j : κ) (i : ι) :
    Integrable (fun q : LayerParams ι κ => |q.1 j i| ^ p)
      (layerGaussianInit (hyperparams Cw) ι κ) := by
  have hmem : MemLp (fun q : LayerParams ι κ => q.1 j i) (p : ℝ≥0∞)
      (layerGaussianInit (hyperparams Cw) ι κ) := by
    refine (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (p := (p : ℝ≥0∞))
      (f := fun q : LayerParams ι κ => q.1 j i)
      (by exact measurable_id.aestronglyMeasurable)
      (((measurable_pi_apply i).comp
          ((measurable_pi_apply j).comp measurable_fst)).aemeasurable)).1 ?_
    rw [map_weight_layerGaussianInit (hyperparams Cw) ι κ j i]
    exact memLp_id_gaussianReal (p : ℝ≥0)
  have hint : Integrable (fun q : LayerParams ι κ => ‖q.1 j i‖ ^ p)
      (layerGaussianInit (hyperparams Cw) ι κ) := by
    exact hmem.integrable_norm_pow'
  simpa [Real.norm_eq_abs] using hint

/-- A single bias coordinate of a freshly initialized bias-free layer is in every `L^p`. -/
private lemma integrable_pow_bias_coord {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Cw : ℝ≥0) (p : ℕ) (j : κ) :
    Integrable (fun q : LayerParams ι κ => |q.2 j| ^ p)
      (layerGaussianInit (hyperparams Cw) ι κ) := by
  have hmem : MemLp (fun q : LayerParams ι κ => q.2 j) (p : ℝ≥0∞)
      (layerGaussianInit (hyperparams Cw) ι κ) := by
    refine (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (p := (p : ℝ≥0∞))
      (f := fun q : LayerParams ι κ => q.2 j)
      (by exact measurable_id.aestronglyMeasurable)
      (((measurable_pi_apply j).comp measurable_snd).aemeasurable)).1 ?_
    rw [map_bias_layerGaussianInit (hyperparams Cw) ι κ j]
    exact memLp_id_gaussianReal (p : ℝ≥0)
  have hint : Integrable (fun q : LayerParams ι κ => ‖q.2 j‖ ^ p)
      (layerGaussianInit (hyperparams Cw) ι κ) := by
    exact hmem.integrable_norm_pow'
  simpa [Real.norm_eq_abs] using hint

/-- The `p`-th power of the absolute preactivation of one output coordinate is integrable under
the bias-free Gaussian initialization law.

Informal proof: bound the preactivation by the sum of absolute values of its Gaussian terms via
the triangle inequality, apply the power-mean inequality, and use the finite Gaussian moments of
the individual weight and bias coordinates. -/
private lemma integrable_pow_preactivation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Cw : ℝ≥0) (p : ℕ) (j : κ) (x : ι → ℝ) :
    Integrable (fun q : LayerParams ι κ => |(DenseLayer.ofParams q).preactivation x j| ^ p)
      (layerGaussianInit (hyperparams Cw) ι κ) := by
  classical
  by_cases hp0 : p = 0
  · subst p
    simp
  have hp : 1 ≤ p := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hp0)
  let μ : Measure (LayerParams ι κ) := layerGaussianInit (hyperparams Cw) ι κ
  have hb : Integrable (fun q : LayerParams ι κ => |q.2 j| ^ p) μ := by
    simpa [μ] using integrable_pow_bias_coord Cw p j
  have hw (t : ι) : Integrable (fun q : LayerParams ι κ => |x t| ^ p * |q.1 j t| ^ p) μ := by
    simpa [μ] using (integrable_pow_weight_coord Cw p j t).const_mul (|x t| ^ p)
  have hsum : Integrable (fun q : LayerParams ι κ => ∑ t : ι, |x t| ^ p * |q.1 j t| ^ p) μ := by
    simpa using (integrable_finsetSum Finset.univ (μ := μ)
      (f := fun (t : ι) q => |x t| ^ p * |q.1 j t| ^ p) (fun t _ => hw t))
  have hdom : Integrable (fun q : LayerParams ι κ =>
      ((Fintype.card ι + 1 : ℝ) ^ (p - 1)) *
        (|q.2 j| ^ p + ∑ t : ι, |x t| ^ p * |q.1 j t| ^ p)) μ := by
    exact (hb.add hsum).const_mul ((Fintype.card ι + 1 : ℝ) ^ (p - 1))
  refine Integrable.mono' hdom ?_ (Filter.Eventually.of_forall ?_)
  · have hmeas : Measurable
        (fun q : LayerParams ι κ => (DenseLayer.ofParams q).preactivation x j) := by
      change Measurable (fun q : LayerParams ι κ => (DenseLayer.preactivationFromParams (q, x)) j)
      exact (measurable_pi_apply j).comp (DenseLayer.measurable_preactivation.comp
        (measurable_id.prodMk measurable_const))
    simpa [Real.norm_eq_abs] using (hmeas.norm.pow_const p).aestronglyMeasurable
  · intro q
    have htri : |(DenseLayer.ofParams q).preactivation x j| ≤
        |q.2 j| + ∑ t : ι, |q.1 j t| * |x t| := by
      rw [DenseLayer.preactivation_apply]
      calc
        |q.2 j + ∑ t : ι, q.1 j t * x t|
            ≤ |q.2 j| + |∑ t : ι, q.1 j t * x t| := abs_add_le _ _
        _ ≤ |q.2 j| + ∑ t : ι, |q.1 j t * x t| := by
              have hsumabs : |∑ t : ι, q.1 j t * x t| ≤ ∑ t : ι, |q.1 j t * x t| := by
                simpa using Finset.abs_sum_le_sum_abs (fun t : ι => q.1 j t * x t) Finset.univ
              nlinarith
        _ = |q.2 j| + ∑ t : ι, |q.1 j t| * |x t| := by
              congr 1
              apply Finset.sum_congr rfl
              intro t _
              rw [abs_mul]
    have hnonneg : ∀ c : ι ⊕ PUnit.{1}, 0 ≤
        (match c with | Sum.inl t => |q.1 j t| * |x t| | Sum.inr _ => |q.2 j|) := by
      intro c
      cases c with
      | inl t => exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
      | inr _ => exact abs_nonneg _
    have hpm := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
      (s := (Finset.univ : Finset (ι ⊕ PUnit.{1})))
      (f := fun c : ι ⊕ PUnit.{1} =>
        match c with | Sum.inl t => |q.1 j t| * |x t| | Sum.inr _ => |q.2 j|)
      (p := (p : ℝ)) (hp := by exact_mod_cast hp) (hf := by intro c _; exact hnonneg c)
    have hpm' : (|q.2 j| + ∑ t : ι, |q.1 j t| * |x t|) ^ p ≤
        (Fintype.card ι + 1 : ℝ) ^ (p - 1) *
          (|q.2 j| ^ p + ∑ t : ι, (|q.1 j t| * |x t|) ^ p) := by
      calc
        (|q.2 j| + ∑ t : ι, |q.1 j t| * |x t|) ^ p
            = (∑ c : ι ⊕ PUnit.{1},
                match c with
                | Sum.inl t => |q.1 j t| * |x t|
                | Sum.inr _ => |q.2 j|) ^ (p : ℝ) := by
              rw [← Real.rpow_natCast]
              congr 1
              simp [Fintype.sum_sum_type, add_comm]
        _ ≤ (Fintype.card ι + 1 : ℝ) ^ ((p : ℝ) - 1) *
            ∑ c : ι ⊕ PUnit.{1},
              (match c with | Sum.inl t => |q.1 j t| * |x t| | Sum.inr _ => |q.2 j|) ^ (p : ℝ) := by
              simpa [Fintype.card_sum, Finset.card_univ] using hpm
        _ = (Fintype.card ι + 1 : ℝ) ^ (p - 1) *
            (|q.2 j| ^ p + ∑ t : ι, (|q.1 j t| * |x t|) ^ p) := by
              rw [← Nat.cast_one, ← Nat.cast_sub hp]
              simp_rw [Real.rpow_natCast]
              simp [Fintype.sum_sum_type, add_comm]
    have hpow2 : |(DenseLayer.ofParams q).preactivation x j| ^ p ≤
        (|q.2 j| + ∑ t : ι, |q.1 j t| * |x t|) ^ p := by
      exact pow_le_pow_left₀ (abs_nonneg _) htri p
    calc
      ‖|(DenseLayer.ofParams q).preactivation x j| ^ p‖
          = |(DenseLayer.ofParams q).preactivation x j| ^ p := by
            rw [Real.norm_eq_abs]
            exact abs_of_nonneg (pow_nonneg (abs_nonneg _) p)
      _ ≤ (|q.2 j| + ∑ t : ι, |q.1 j t| * |x t|) ^ p := hpow2
      _ ≤ (Fintype.card ι + 1 : ℝ) ^ (p - 1) *
            (|q.2 j| ^ p + ∑ t : ι, (|q.1 j t| * |x t|) ^ p) := hpm'
      _ ≤ (Fintype.card ι + 1 : ℝ) ^ (p - 1) *
            (|q.2 j| ^ p + ∑ t : ι, |x t| ^ p * |q.1 j t| ^ p) := by
            have hsumle : (∑ t : ι, (|q.1 j t| * |x t|) ^ p) ≤
                ∑ t : ι, |x t| ^ p * |q.1 j t| ^ p := by
              apply Finset.sum_le_sum
              intro t _
              rw [mul_pow, mul_comm]
            exact mul_le_mul_of_nonneg_left (by nlinarith [hsumle])
              (pow_nonneg (by positivity : 0 ≤ (Fintype.card ι + 1 : ℝ)) _)

/-- Pulling a measurable map out of the left side of a measure bind. -/
private lemma measure_bind_map_comp {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) {f : α → β} {g : β → Measure γ}
    (hf : Measurable f) (hg : Measurable g) :
    (μ.map f).bind g = μ.bind (fun x => g (f x)) := by
  rw [Measure.bind, Measure.bind, Measure.map_map hg hf]
  rfl

/-- Mapping a bind through a measurable function. -/
private lemma measure_map_bind {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (f : α → Measure β) {g : β → γ}
    (hf : Measurable f) (hg : Measurable g) :
    (μ.bind f).map g = μ.bind (fun x => (f x).map g) := by
  rw [Measure.bind, ← Measure.join_map_map hg]
  rw [Measure.bind, Measure.map_map (Measure.measurable_map g hg) hf]
  rfl

/-- The product-measure pushforward of a two-variable measurable function is the iterated bind
that first samples the left coordinate and then pushes the right measure forward.

This is the measure-level Fubini/Giry-monad calculation used in the hidden case of
`MLPEnsemble.outputKernel_apply_eq_outputLaw`. -/
private lemma map_prod_eq_bind_map {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) [SFinite ν] {G : α × β → γ}
    (hG : Measurable G) :
    (μ.prod ν).map G = μ.bind (fun a => ν.map (fun b => G (a, b))) := by
  rw [Measure.prod]
  calc
    (μ.bind (fun a : α => Measure.map (Prod.mk a) ν)).map G
        = μ.bind (fun a => (Measure.map (Prod.mk a) ν).map G) := by
          exact measure_map_bind μ (fun a : α => Measure.map (Prod.mk a) ν) (g := G)
            (by exact Measurable.map_prodMk_left) hG
    _ = μ.bind (fun a => ν.map (fun b => G (a, b))) := by
          congr
          funext a
          exact Measure.map_map hG (measurable_const.prodMk measurable_id)

/-- Measure-level tower decomposition for a deep-linear network with one hidden layer exposed.

Informal proof: specialize `MLPEnsemble.outputKernel_apply_eq_outputLaw` (or equivalently repeat
its hidden-case `hprod` calculation) to a singleton batch and to the linear activation.  The
initialization law of `MLPShape.hidden tail` is the product of the first-layer Gaussian law and the
independent tail-parameter law.  Mapping this product through `MLPShape.eval_hidden` and using
`activate_linear_eq_preactivation` identifies the first marginal pushforward with
`oneLayerOutputLaw Cw x`, leaving the conditional tail law `tail.deepLinearOutputLaw Cw y`.
-/
private lemma deepLinearOutputLaw_hidden_eq_bind {dIn k dOut : ℕ}
    (tail : MLPShape k dOut) (Cw : ℝ≥0) (x : Fin dIn → ℝ) :
    (MLPShape.hidden tail : MLPShape dIn dOut).deepLinearOutputLaw Cw x =
      (oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x).bind
        (fun y => tail.deepLinearOutputLaw Cw y) := by
  classical
  let μ : Measure (LayerParams (Fin dIn) (Fin k)) :=
    layerGaussianInit (hyperparams Cw) (Fin dIn) (Fin k)
  let ν : Measure tail.Params := tail.gaussianInit (tail.deepLinearHyperparams Cw)
  let f : LayerParams (Fin dIn) (Fin k) → Fin k → ℝ :=
    fun q => (DenseLayer.ofParams q).preactivation x
  let G : LayerParams (Fin dIn) (Fin k) × tail.Params → Fin dOut → ℝ :=
    fun p => tail.eval (linear 1) p.2 (f p.1)
  have hf_meas : Measurable f := by
    dsimp [f]
    exact DenseLayer.measurable_preactivation.comp
      (measurable_id.prodMk measurable_const)
  have hG_meas : Measurable G := by
    dsimp [G, f]
    exact (tail.measurable_eval (measurable_linear 1)).comp
      (measurable_snd.prodMk
        (DenseLayer.measurable_preactivation.comp
          (measurable_fst.prodMk measurable_const)))
  have htailLaw_meas : Measurable fun y : Fin k → ℝ => tail.deepLinearOutputLaw Cw y := by
    -- Joint measurability of `tail.eval` makes the parameter pushforward vary measurably in
    -- the deterministic input.  This is the one-input form of the kernel measurability packaged
    -- by `MLPEnsemble.outputKernel`; it follows by unfolding `deepLinearOutputLaw` and using
    -- `Measure.measurable_map` on the jointly measurable map `(θ, y) ↦ tail.eval (linear 1) θ y`.
    let μ₀ : Measure tail.Params := tail.gaussianInit (tail.deepLinearHyperparams Cw)
    change Measurable fun y : Fin k → ℝ =>
      μ₀.map (fun θ : tail.Params => tail.eval (linear 1) θ y)
    let G : tail.Params × (Fin k → ℝ) → Fin dOut → ℝ :=
      fun p => tail.eval (linear 1) p.1 p.2
    have hG_meas : Measurable G := by
      dsimp [G]
      exact (tail.measurable_eval (measurable_linear 1)).comp (measurable_fst.prodMk measurable_snd)
    have hEq : (fun y : Fin k → ℝ =>
          μ₀.map (fun θ : tail.Params => tail.eval (linear 1) θ y)) =
        fun y : Fin k → ℝ => (μ₀.map (fun θ : tail.Params => (θ, y))).map G := by
      funext y
      rw [Measure.map_map hG_meas measurable_prodMk_right]
      rfl
    rw [hEq]
    exact (Measure.measurable_map G hG_meas).comp (Measurable.map_prodMk_right (μ := μ₀))
  have hprod : (μ.prod ν).map G = μ.bind (fun q => ν.map (fun θ' => G (q, θ'))) := by
    exact map_prod_eq_bind_map μ ν hG_meas
  have hpull : (μ.map f).bind (fun y : Fin k → ℝ => tail.deepLinearOutputLaw Cw y) =
      μ.bind (fun q => tail.deepLinearOutputLaw Cw (f q)) := by
    exact measure_bind_map_comp μ hf_meas htailLaw_meas
  calc
    (MLPShape.hidden tail : MLPShape dIn dOut).deepLinearOutputLaw Cw x
        = (μ.prod ν).map G := by
          dsimp [MLPShape.deepLinearOutputLaw, MLPShape.gaussianInit,
            MLPShape.deepLinearHyperparams, μ, ν, G, f]
          congr
          funext θ
          rw [activate_linear_eq_preactivation]
    _ = μ.bind (fun q => ν.map (fun θ' => G (q, θ'))) := hprod
    _ = μ.bind (fun q => tail.deepLinearOutputLaw Cw (f q)) := by
          congr
    _ = (μ.map f).bind (fun y : Fin k → ℝ => tail.deepLinearOutputLaw Cw y) := hpull.symm
    _ = (oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x).bind
          (fun y => tail.deepLinearOutputLaw Cw y) := by
          dsimp [oneLayerOutputLaw, μ, f]

/-- Bochner integral form of the tower property for the monomial output observable.

Informal proof: apply Fubini/Tonelli to the bind measure in
`deepLinearOutputLaw_hidden_eq_bind`.  The integrand `z ↦ ∏ r, z (a r)` is measurable by
`measurable_monomial`; integrability follows because the output coordinates are polynomials in
finitely many independent Gaussian weights, hence have finite moments of all orders (the one-layer
case is `integrable_pow_preactivation`, and the general case follows by induction over `tail`).
This is the standard law of total expectation; see Mathlib's `Measure.lintegral_bind` / product
Fubini API and the discussion in `docs/Renormalization.md` on Gaussian moments.
-/
private lemma integral_monomial_deepLinearOutputLaw_bind {dIn k dOut : ℕ}
    (tail : MLPShape k dOut) (Cw : ℝ≥0) (x : Fin dIn → ℝ) (m : ℕ)
    (a : Fin (2 * m) → Fin dOut) :
    ∫ z, (∏ r, z (a r))
        ∂((oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x).bind
          (fun y => tail.deepLinearOutputLaw Cw y)) =
      ∫ y : Fin k → ℝ,
        (∫ z, (∏ r, z (a r)) ∂tail.deepLinearOutputLaw Cw y)
          ∂oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x := by
  classical
  -- The pinned Mathlib has only a lintegral bind theorem, so the real-valued Bochner version
  -- requires first proving the finite Gaussian moment/integrability side conditions.
  sorry

/-- Conditioning a `.hidden tail` deep-linear network on the output of its first random layer.

The first layer produces `y ∼ oneLayerOutputLaw Cw x`; conditional on this `y`, the remaining
parameters are independent and the output law is `tail.deepLinearOutputLaw Cw y`.  Thus moments of
any measurable integrand are computed by the corresponding iterated integral.  This is the
one-input specialization of the Markov/kernel composition theorem
`MLPEnsemble.outputKernel_apply_eq_outputLaw` from `InducedLaw.lean`, together with
`MLPShape.eval_hidden`.
-/
private lemma integral_monomial_deepLinearOutputLaw_hidden_bind {dIn k dOut : ℕ}
    (tail : MLPShape k dOut) (Cw : ℝ≥0) (x : Fin dIn → ℝ) (m : ℕ)
    (a : Fin (2 * m) → Fin dOut) :
    ∫ z, (∏ r, z (a r))
        ∂(MLPShape.hidden tail : MLPShape dIn dOut).deepLinearOutputLaw Cw x =
      ∫ y : Fin k → ℝ,
        (∫ z, (∏ r, z (a r)) ∂tail.deepLinearOutputLaw Cw y)
          ∂oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x := by
  rw [deepLinearOutputLaw_hidden_eq_bind tail Cw x]
  exact integral_monomial_deepLinearOutputLaw_bind tail Cw x m a

/-- The scalar part of the induction step after applying the tail moment formula.

Informally, expand `correlatorAmplitude Cw (normalizedEnergy y) m widths`, pull the constants
`pairingTensor a`, `(Cw : ℝ) ^ ((widths.length + 1) * m)`, and
`hiddenWidthCorrection m widths` outside the integral, and use
`integral_normalizedEnergy_pow_randomLayerKernel` to evaluate the remaining radial moment.  The
result is exactly the `correlatorAmplitude` recursion for the new width `k`.
-/
private lemma integral_pairingTensor_correlatorAmplitude_oneLayer {dIn k dOut : ℕ}
    (Cw : ℝ≥0) (x : Fin dIn → ℝ) (m : ℕ) (a : Fin (2 * m) → Fin dOut)
    (widths : List ℕ) (hk : 0 < k) :
    ∫ y : Fin k → ℝ,
        pairingTensor a * correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy y) m widths
          ∂oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x =
      pairingTensor a *
        correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy x) m (k :: widths) := by
  classical
  let c : ℝ :=
    pairingTensor a * hiddenWidthCorrection m widths * (Cw : ℝ) ^ ((widths.length + 1) * m)
  have hfactor : ∀ y : Fin k → ℝ,
      pairingTensor a * correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy y) m widths =
        c * NeuralNetwork.normalizedEnergy y ^ m := by
    intro y
    unfold correlatorAmplitude c
    rw [mul_pow, pow_mul]
    ring
  have hrad : ∫ y : Fin k → ℝ, NeuralNetwork.normalizedEnergy y ^ m
        ∂oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x =
      ((Cw : ℝ) * NeuralNetwork.normalizedEnergy x) ^ m * widthMomentFactor m k := by
    simpa [Fintype.card_fin] using
      integral_normalizedEnergy_pow_randomLayerKernel (ι := Fin dIn) (κ := Fin k) Cw x m
        (by simpa [Fintype.card_fin] using hk)
  calc
    ∫ y : Fin k → ℝ,
        pairingTensor a * correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy y) m widths
          ∂oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x
        = ∫ y : Fin k → ℝ, c * NeuralNetwork.normalizedEnergy y ^ m
            ∂oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with y
          exact hfactor y
    _ = c * ∫ y : Fin k → ℝ, NeuralNetwork.normalizedEnergy y ^ m
          ∂oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x := by
          rw [MeasureTheory.integral_const_mul]
    _ = c * (((Cw : ℝ) * NeuralNetwork.normalizedEnergy x) ^ m * widthMomentFactor m k) := by
          rw [hrad]
    _ = pairingTensor a *
        correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy x) m (k :: widths) := by
          dsimp [c]
          have hlen : widths.length + 1 + 1 = widths.length + 2 := by omega
          simp only [correlatorAmplitude, hiddenWidthCorrection_cons, List.length_cons]
          rw [hlen, mul_pow, mul_pow, pow_mul]
          ring_nf

/-- The width list of a shape is never empty: it always contains the input width. -/
private lemma widths_ne_nil {m n : ℕ} (S : MLPShape m n) : S.widths ≠ [] := by
  cases S <;> simp [MLPShape.widths]

/-- Adding a first hidden layer conses its output width onto the hidden-width list.

Informal proof: `tail.widths` always starts with its input width `k`.  Therefore
`(MLPShape.hidden tail).widths = dIn :: tail.widths`, and dropping the input and final output gives
`tail.widths.dropLast = k :: tail.widths.tail.dropLast`, i.e. `k :: tail.hiddenWidths`.
-/
private lemma hidden_hiddenWidths_cons {dIn k dOut : ℕ} (tail : MLPShape k dOut) :
    (MLPShape.hidden tail : MLPShape dIn dOut).hiddenWidths = k :: tail.hiddenWidths := by
  induction tail with
  | output =>
      simp [MLPShape.hiddenWidths, MLPShape.widths]
  | hidden tail' ih =>
      by_cases hnil : tail'.widths = []
      · exact (widths_ne_nil tail' hnil).elim
      · rcases List.exists_cons_of_ne_nil hnil with ⟨b, l, hw⟩
        simp [MLPShape.hiddenWidths, MLPShape.widths, hw, List.dropLast_cons_cons]

private lemma jointMoment_outputLaw_hidden_even_of_tail {dIn k dOut : ℕ}
    (tail : MLPShape k dOut) (Cw : ℝ≥0) (x : Fin dIn → ℝ) (m : ℕ)
    (a : Fin (2 * m) → Fin dOut)
    (_hIn : 0 < dIn)
    (hWidths : ∀ n ∈ (MLPShape.hidden tail : MLPShape dIn dOut).hiddenWidths, 0 < n)
    (ih : ∀ (y : Fin k → ℝ) (a : Fin (2 * m) → Fin dOut),
        0 < k → (∀ n ∈ tail.hiddenWidths, 0 < n) →
        ∫ z, (∏ r, z (a r)) ∂tail.deepLinearOutputLaw Cw y =
          pairingTensor a *
            correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy y) m tail.hiddenWidths) :
    ∫ z, (∏ r, z (a r))
        ∂(MLPShape.hidden tail : MLPShape dIn dOut).deepLinearOutputLaw Cw x =
      pairingTensor a *
        correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy x) m
          (MLPShape.hidden tail : MLPShape dIn dOut).hiddenWidths := by
  classical
  have hHiddenWidths :
      (MLPShape.hidden tail : MLPShape dIn dOut).hiddenWidths = k :: tail.hiddenWidths :=
    hidden_hiddenWidths_cons tail
  have hk : 0 < k := by
    apply hWidths k
    rw [hHiddenWidths]
    simp
  have hTailWidths : ∀ n ∈ tail.hiddenWidths, 0 < n := by
    intro n hn
    apply hWidths n
    rw [hHiddenWidths]
    exact List.mem_cons_of_mem k hn
  calc
    ∫ z, (∏ r, z (a r))
        ∂(MLPShape.hidden tail : MLPShape dIn dOut).deepLinearOutputLaw Cw x =
        ∫ y : Fin k → ℝ,
          (∫ z, (∏ r, z (a r)) ∂tail.deepLinearOutputLaw Cw y)
            ∂oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x := by
          exact integral_monomial_deepLinearOutputLaw_hidden_bind tail Cw x m a
    _ = ∫ y : Fin k → ℝ,
          pairingTensor a *
            correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy y) m tail.hiddenWidths
            ∂oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with y
          exact ih y a hk hTailWidths
    _ = pairingTensor a *
        correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy x) m (k :: tail.hiddenWidths) :=
          integral_pairingTensor_correlatorAmplitude_oneLayer Cw x m a tail.hiddenWidths hk
    _ = pairingTensor a *
        correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy x) m
          (MLPShape.hidden tail : MLPShape dIn dOut).hiddenWidths := by
          rw [hHiddenWidths]

/-- Exact even joint output moment at arbitrary finite positive widths.

Informal proof: condition on the penultimate activations and apply Wick's theorem to the centered
Gaussian final layer.  The index contractions give `pairingTensor`; the random variance gives the
`m`-th normalized-energy moment.  Iterating
`integral_normalizedEnergy_pow_randomLayerKernel` over the shape yields precisely the product
`hiddenWidthCorrection`.  Source: `docs/Renormalization.md`, equations
`eq:deep-linear-inductive-ansatz`, `eq:combinatorial-2m`, and `eq:2m-full-solution`.
-/
theorem jointMoment_outputLaw_even {dIn dOut : ℕ} (S : MLPShape dIn dOut)
    (Cw : ℝ≥0) (x : Fin dIn → ℝ) (m : ℕ) (a : Fin (2 * m) → Fin dOut)
    (hIn : 0 < dIn) (hWidths : ∀ n ∈ S.hiddenWidths, 0 < n) :
    ∫ z, (∏ r, z (a r)) ∂S.deepLinearOutputLaw Cw x =
      pairingTensor a *
        correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy x) m S.hiddenWidths := by
  induction S with
  | output =>
      exact jointMoment_outputLaw_output_even Cw x m a hIn
  | hidden tail ih =>
      exact jointMoment_outputLaw_hidden_even_of_tail tail Cw x m a hIn hWidths ih

/-- The Wick pairing sum for the constant output-index map is the even Gaussian coefficient. -/
private lemma pairingTensor_const {κ : Type uJ} [DecidableEq κ] (m : ℕ) (j : κ) :
    pairingTensor (fun _ : Fin (2 * m) => j) = gaussianEvenCoeff m := by
  classical
  have hWick := integral_prod_pi_gaussianReal_eq_pairingTensor
    (κ := Fin 1) (v := 1) m (fun _ : Fin (2 * m) => (0 : Fin 1))
  have hL : ∫ z, (∏ r : Fin (2 * m), z (0 : Fin 1))
        ∂Measure.pi (fun _ : Fin 1 => gaussianReal 0 1) = gaussianEvenCoeff m := by
    calc
      ∫ z, (∏ r : Fin (2 * m), z (0 : Fin 1))
          ∂Measure.pi (fun _ : Fin 1 => gaussianReal 0 1)
          = ∫ z, (z 0) ^ (2 * m) ∂Measure.pi (fun _ : Fin 1 => gaussianReal 0 1) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with z
            simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ∫ x : ℝ, x ^ (2 * m) ∂gaussianReal 0 1 := by
            let π₁ : Measure (Fin 1 → ℝ) := Measure.pi (fun _ : Fin 1 => gaussianReal 0 1)
            let e : (Fin 1 → ℝ) → ℝ := fun z => z 0
            have hmap := (measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) 0).map_eq
            calc
              ∫ z, (z 0) ^ (2 * m) ∂π₁
                  = ∫ x : ℝ, x ^ (2 * m) ∂π₁.map e := by
                    dsimp [π₁, e]
                    exact (MeasureTheory.integral_map (φ := fun z : Fin 1 → ℝ => z 0)
                      (measurable_pi_apply 0).aemeasurable
                      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ (2 * m))
                        (Measure.map (fun z : Fin 1 → ℝ => z 0)
                          (Measure.pi (fun _ : Fin 1 => gaussianReal 0 1))))).symm
              _ = ∫ x : ℝ, x ^ (2 * m) ∂gaussianReal 0 1 := by
                    rw [hmap]
      _ = gaussianEvenCoeff m := by
            simpa [gaussianEvenCoeff] using
              Renormalization.integral_pow_gaussianReal_even (v := (1 : ℝ≥0)) m
  have hcoef : pairingTensor (fun _ : Fin (2 * m) => (0 : Fin 1)) = gaussianEvenCoeff m := by
    have htmp : pairingTensor (fun _ : Fin (2 * m) => (0 : Fin 1)) * (1 : ℝ) ^ m =
        gaussianEvenCoeff m := hWick.symm.trans hL
    simpa using htmp
  have hsame : pairingTensor (fun _ : Fin (2 * m) => j) =
      pairingTensor (fun _ : Fin (2 * m) => (0 : Fin 1)) := by
    simp [pairingTensor]
  exact hsame.trans hcoef

/-- Exact even moment of one output coordinate.

Informal proof: specialize `jointMoment_outputLaw_even` to the constant output-index map.  Every
Kronecker factor is one and the number of pairings of `2m` points is
`(2m)!/(2^m m!) = gaussianEvenCoeff m`.  Source:
<https://en.wikipedia.org/wiki/Double_factorial#Applications>.
-/
theorem integral_coordinate_pow_outputLaw_even {dIn dOut : ℕ} (S : MLPShape dIn dOut)
    (Cw : ℝ≥0) (x : Fin dIn → ℝ) (m : ℕ) (j : Fin dOut)
    (hIn : 0 < dIn) (hWidths : ∀ n ∈ S.hiddenWidths, 0 < n) :
    ∫ z, z j ^ (2 * m) ∂S.deepLinearOutputLaw Cw x =
      gaussianEvenCoeff m *
        correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy x) m S.hiddenWidths := by
  calc
    ∫ z, z j ^ (2 * m) ∂S.deepLinearOutputLaw Cw x
        = ∫ z, (∏ r : Fin (2 * m), z ((fun _ : Fin (2 * m) => j) r))
            ∂S.deepLinearOutputLaw Cw x := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with z
            simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = pairingTensor (fun _ : Fin (2 * m) => j) *
          correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy x) m S.hiddenWidths :=
          jointMoment_outputLaw_even S Cw x m (fun _ => j) hIn hWidths
    _ = gaussianEvenCoeff m *
          correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy x) m S.hiddenWidths := by
          rw [pairingTensor_const m j]

/-- Covariance of two batch-output coordinates.  The theorem explicitly uses Mathlib's
`covariance`, not merely an uncentered second moment.

Informal proof: all outputs are centered by the odd-moment theorem.  Conditioning one layer gives
zero for different output rows and `Cw` times the previous normalized Gram entry for equal rows.
Induction over `S` gives the displayed closed form.  Source: `docs/Renormalization.md`, equations
`eq:two-point-function-deep-linear-layer-ell` and `eq:deep-linear-kernel-recursion`.
-/
theorem covariance_batchOutputLaw {A : Type uA}
    {dIn dOut : ℕ} (S : MLPShape dIn dOut) (Cw : ℝ≥0)
    (D : A → Fin dIn → ℝ) (a b : A) (i j : Fin dOut)
    (hIn : 0 < dIn) (hWidths : ∀ n ∈ S.hiddenWidths, 0 < n) :
    covariance (fun z => z a i) (fun z => z b j) (S.deepLinearBatchLaw Cw D) =
      if i = j then (Cw : ℝ) ^ S.depth * NeuralNetwork.normalizedGram D a b else 0 := by
  sorry

/-- Uncentered form of the exact finite-dataset covariance solution.

Informal proof: use `jointMoment_outputLaw_odd` to replace covariance by the second moment, then
apply `covariance_batchOutputLaw`.  This is the closed solution `G^(L)=Cw^L G^(0)` in
`docs/Renormalization.md`, equation `eq:deep-linear-exponential-solution`.
-/
theorem covariance_batchOutputLaw_closedForm {A : Type uA}
    {dIn dOut : ℕ} (S : MLPShape dIn dOut) (Cw : ℝ≥0)
    (D : A → Fin dIn → ℝ) (a b : A) (i j : Fin dOut)
    (hIn : 0 < dIn) (hWidths : ∀ n ∈ S.hiddenWidths, 0 < n) :
    ∫ z, z a i * z b j ∂S.deepLinearBatchLaw Cw D =
      if i = j then (Cw : ℝ) ^ S.depth * NeuralNetwork.normalizedGram D a b else 0 := by
  sorry

/-- Subcritical covariance amplitudes tend to zero. -/
theorem tendsto_covariance_of_weightVariance_lt_one (Cw q : ℝ)
    (hCw0 : 0 ≤ Cw) (hCw1 : Cw < 1) :
    Tendsto (fun L : ℕ => Cw ^ L * q) atTop (nhds 0) := by
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hCw0 hCw1).mul_const q

/-- At criticality the covariance amplitude is exactly constant. -/
@[simp, nolint simpNF] theorem covariance_eq_of_weightVariance_eq_one (q : ℝ) (L : ℕ) :
    (1 : ℝ) ^ L * q = q := by simp

/-- A positive supercritical covariance amplitude diverges to `+∞`.

Informal proof: `Cw^L → +∞` for `Cw>1`; multiplication by the fixed positive `q` preserves
divergence.  This is the geometric-sequence criterion; see
<https://en.wikipedia.org/wiki/Geometric_progression#Geometric_series>.
-/
theorem tendsto_covariance_atTop_of_one_lt_weightVariance (Cw q : ℝ)
    (hCw : 1 < Cw) (hq : 0 < q) :
    Tendsto (fun L : ℕ => Cw ^ L * q) atTop atTop :=
  Tendsto.atTop_mul_const hq (tendsto_pow_atTop_atTop_of_one_lt hCw)

/-- A negative supercritical off-diagonal covariance diverges in absolute value. -/
theorem tendsto_abs_covariance_atTop_of_one_lt_weightVariance (Cw q : ℝ)
    (hCw : 1 < Cw) (hq : q ≠ 0) :
    Tendsto (fun L : ℕ => |Cw ^ L * q|) atTop atTop := by
  simpa [abs_mul, abs_of_pos (lt_trans (by norm_num) hCw)] using
    tendsto_covariance_atTop_of_one_lt_weightVariance Cw |q| hCw (abs_pos.mpr hq)


/-- The first layer is exactly a product Gaussian law, not merely moment-equivalent to it.

Informal proof: specialize the one-layer conditional law to a singleton batch and transport along
the canonical equivalence between a singleton Euclidean vector and `ℝ`.  The resulting coordinate
variance is `Cw * normalizedEnergy x`.  Source: `docs/Renormalization.md`, equation
`eq:deep-linear-gaussian-first-layer`.
-/
theorem firstLayerOutputLaw_eq_pi_gaussianReal {dIn dOut : ℕ} (Cw : ℝ≥0)
    (x : Fin dIn → ℝ) (_hIn : 0 < dIn) :
    (MLPShape.output : MLPShape dIn dOut).deepLinearOutputLaw Cw x =
      Measure.pi (fun _ : Fin dOut =>
        gaussianReal 0 (Cw * NeuralNetwork.normalizedEnergyNNReal x)) := by
  change oneLayerOutputLaw (ι := Fin dIn) (κ := Fin dOut) Cw x =
    Measure.pi (fun _ : Fin dOut => gaussianReal 0 (Cw * NeuralNetwork.normalizedEnergyNNReal x))
  exact oneLayerOutputLaw_eq_pi_gaussianReal (dIn := dIn) (dOut := dOut) Cw x

-- temporary #check block
#check @Measurable.map_prodMk_right
#check @Measure.measurable_map
#check @Measure.map_map
#check @ProbabilityTheory.Kernel.integral_comp
#check @ProbabilityTheory.Kernel.aemeasurable
#check @ProbabilityTheory.Kernel.comp_apply
#check @MeasureTheory.Measure.comp_eq_comp_const_apply
#check @MeasureTheory.Measure.comp_assoc
#check @MeasureTheory.Measure.integrable_comp_iff
#check @MeasureTheory.Measure.lintegral_bind
#check @MeasureTheory.integral_eq_lintegral_pos_part_sub_lintegral_neg_part
#check @MeasureTheory.MemLp.mul
#check @ProbabilityTheory.memLp_id_gaussianReal
#check @ProbabilityTheory.memLp_id_gaussianReal'
#check @MeasureTheory.MemLp.comp_measurePreserving
#check @MeasureTheory.Integrable.mono'
#check @MeasureTheory.integrable_map_measure
#check @MeasureTheory.integrable_finsetSum
#check @MeasureTheory.Integrable.const_mul
#check @MeasureTheory.Integrable.norm
#check @MeasureTheory.MemLp.integrable_norm_pow'
#check @MeasureTheory.MemLp.integrable
#check @MeasureTheory.memLp_map_measure_iff
#check @MeasureTheory.Integrable.aestronglyMeasurable
#check @MeasureTheory.norm_integral_le_integral_norm
#check @MeasureTheory.integral_mono_ae
#check @MeasureTheory.integral_mono
#check @MeasureTheory.Integrable.congr
#check @MeasureTheory.Integrable.mono
#check @MeasureTheory.Integrable.congr'
#check @MeasureTheory.Integrable.mono_measure
#check @MeasureTheory.integral_eq_lintegral_of_nonneg_ae
#check @MeasureTheory.Measure.measurable_lintegral
#check @MeasureTheory.Measure.measurable_map
#check @MeasureTheory.measurePreserving_eval
#check @ProbabilityTheory.Kernel.const_apply
#check @ProbabilityTheory.Kernel.deterministic_apply
#check @MeasureTheory.Measure.dirac_bind
#check @MeasureTheory.Measure.bind_dirac_eq_map
#check @MeasureTheory.integral_map
#check @MeasureTheory.Measure.prod
#check @MeasureTheory.integral_prod
#check @MeasureTheory.Integrable.integral_prod_right
#check @MeasureTheory.integrable_const
#check @MeasureTheory.Measure.isProbabilityMeasure_map
#check @MLPShape.deepLinearOutputLaw
#check @MLPShape.measurable_eval
#check @MLPShape.gaussianInit
#check @MLPShape.deepLinearHyperparams
#check @MLPShape.eval
#check @measurable_linear
#check @LayerParams
#check @DenseLayer.preactivation
#check @DenseLayer.ofParams
#check @DenseLayer.preactivation_apply
#check @DenseLayer.measurable_preactivation
#check @Measure.map_map

end NeuralNetwork.DeepLinear

end

end
