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

/-- The batch deep-linear output law is invariant under the coordinatewise sign flip.

Informal proof: this is the same final-layer sign symmetry as
`deepLinearOutputLaw_isNegInvariant`, applied simultaneously to every input in the batch.  Negating
the last layer preserves the centered Gaussian initialization law and negates `S.eval` at each
batch entry, hence the pushforward batch law is fixed by `z ↦ -z`.
-/
theorem deepLinearBatchLaw_isNegInvariant {A : Type uA} {dIn dOut : ℕ}
    (S : MLPShape dIn dOut) (Cw : ℝ≥0) (D : A → Fin dIn → ℝ) :
    Measure.IsNegInvariant (S.deepLinearBatchLaw Cw D) := ⟨by
  let μ₀ : Measure S.Params := S.gaussianInit (S.deepLinearHyperparams Cw)
  let F : S.Params → A → Fin dOut → ℝ := fun θ a => S.eval (linear 1) θ (D a)
  have hF_meas : Measurable F :=
    (S.paramModel (linear 1) (measurable_linear 1)).measurable_evalBatch D
  have hJ_meas : Measurable (negLastLayer S) := measurable_negLastLayer S
  have hJ_inv : Measure.map (negLastLayer S) μ₀ = μ₀ := gaussianInit_negLastLayer S Cw
  calc
    (S.deepLinearBatchLaw Cw D).map (fun z : A → Fin dOut → ℝ => -z)
        = (μ₀.map F).map (fun z : A → Fin dOut → ℝ => -z) := rfl
    _ = μ₀.map (fun θ : S.Params => -F θ) :=
          Measure.map_map (g := fun z : A → Fin dOut → ℝ => -z) (f := F)
            (by fun_prop : Measurable fun z : A → Fin dOut → ℝ => -z) hF_meas
    _ = μ₀.map (fun θ : S.Params => F (negLastLayer S θ)) := by
          congr 1
          funext θ a
          exact (eval_negLastLayer S θ (D a)).symm
    _ = (μ₀.map (negLastLayer S)).map F := (Measure.map_map hF_meas hJ_meas).symm
    _ = μ₀.map F := by
          rw [hJ_inv]
    _ = S.deepLinearBatchLaw Cw D := rfl
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
      refine Measurable.of_eval (fun j => ?_)
      exact hT_meas.comp (measurable_pi_apply j)
    exact h1.comp hz_meas
  have hg_meas : Measurable g := by
    dsimp [g]
    refine Measurable.of_eval (fun j => ?_)
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
    refine (Measurable.of_eval (fun i => ?_)).aemeasurable
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
      exact (Measure.isProbabilityMeasure_map_iff
        (((MLPShape.output : MLPShape dIn dOut).measurable_eval (measurable_linear 1)).comp
          (measurable_id.prodMk measurable_const)).aemeasurable).mpr inferInstance
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
            exact Finset.prod_le_prod₀ (fun r _ => abs_nonneg _) (fun r _ => hle r)
          _ = (Real.sqrt (∑ j : Fin dOut, z j ^ 2)) ^ (2 * m) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ = (∑ j : Fin dOut, z j ^ 2) ^ m := by
            rw [pow_mul, Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (z j)))]
      have hpm' : (∑ j : Fin dOut, z j ^ 2) ^ m ≤ C * ∑ j : Fin dOut, z j ^ (2 * m) := by
        simpa [C, Fintype.card_fin, pow_mul] using
          (sum_pow_le_card_pow_mul_sum_pow_nat (fun j : Fin dOut => z j ^ 2) m hmpos
            (fun j => sq_nonneg (z j)))
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

/-- The tail output law varies measurably in the deterministic input.

Informal proof: unfold `deepLinearOutputLaw` and use `Measure.measurable_map` on the jointly
measurable map `(θ, y) ↦ tail.eval (linear 1) θ y`: the parameter pushforward is measurable in
the input (`Measurable.map_prodMk_right`) and `Measure.map` is measurable in the measure
argument (`Measure.measurable_map`). -/
private lemma measurable_deepLinearOutputLaw_kernel {k dOut : ℕ} (tail : MLPShape k dOut)
    (Cw : ℝ≥0) :
    Measurable fun y : Fin k → ℝ => tail.deepLinearOutputLaw Cw y := by
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
  have htailLaw_meas : Measurable fun y : Fin k → ℝ => tail.deepLinearOutputLaw Cw y :=
    measurable_deepLinearOutputLaw_kernel tail Cw
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

/-- Bochner tower property for a bind of a measurable kernel.

Informal proof: identify `κ ∘ₘ μ = μ.bind κ`, convert the measure composition into a kernel
composition with a constant kernel (`Measure.comp_eq_comp_const_apply`), and apply Mathlib's
kernel Fubini theorem `Kernel.integral_comp`.  The only side condition is integrability of the
integrand on the composed measure. -/
private lemma integral_bind_of_integrable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (κ : α → Measure β) (hκ : Measurable κ) {F : β → ℝ}
    (hF : Integrable F (μ.bind κ)) :
    ∫ z, F z ∂(μ.bind κ) = ∫ a, (∫ z, F z ∂(κ a)) ∂μ := by
  let η : Kernel α β := ⟨κ, hκ⟩
  have hF' : Integrable F (η ∘ₘ μ) := by
    dsimp [η]
    exact hF
  have htower := Kernel.integral_comp (η := η) (κ := Kernel.const Unit μ) (a := ()) (f := F)
    (by
      rw [Measure.comp_eq_comp_const_apply] at hF'
      exact hF')
  rw [Kernel.comp_apply, Kernel.const_apply] at htower
  change ∫ z, F z ∂(μ.bind κ) = ∫ a, (∫ z, F z ∂(κ a)) ∂μ
  simpa [η] using htower

/-- Bochner integral form of the tower property for the monomial output observable.

Informal proof: apply Fubini/Tonelli to the bind measure in
`deepLinearOutputLaw_hidden_eq_bind`, packaged as the kernel tower property
`integral_bind_of_integrable` (`Kernel.integral_comp`).  The integrand
`z ↦ ∏ r, z (a r)` is measurable by `measurable_monomial`; the integrability side condition is
carried explicitly because the output coordinates are polynomials in finitely many independent
Gaussian weights, hence have finite moments of all orders (proved together with the moment
formulas by induction over the shape).  This is the standard law of total expectation; see
Mathlib's `Measure.lintegral_bind` / kernel-composition Fubini API and the discussion in
`docs/Renormalization.md` on Gaussian moments.
-/
private lemma integral_monomial_deepLinearOutputLaw_bind {dIn k dOut : ℕ}
    (tail : MLPShape k dOut) (Cw : ℝ≥0) (x : Fin dIn → ℝ) (m : ℕ)
    (a : Fin (2 * m) → Fin dOut)
    (hInt : Integrable (fun z => ∏ r, z (a r))
      ((oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x).bind
        (fun y => tail.deepLinearOutputLaw Cw y))) :
    ∫ z, (∏ r, z (a r))
        ∂((oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x).bind
          (fun y => tail.deepLinearOutputLaw Cw y)) =
      ∫ y : Fin k → ℝ,
        (∫ z, (∏ r, z (a r)) ∂tail.deepLinearOutputLaw Cw y)
          ∂oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x := by
  classical
  let μ : Measure (Fin k → ℝ) := oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x
  have htower := integral_bind_of_integrable μ (fun y => tail.deepLinearOutputLaw Cw y)
    (measurable_deepLinearOutputLaw_kernel tail Cw) (F := fun z => ∏ r, z (a r)) hInt
  simpa [μ] using htower

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
    (a : Fin (2 * m) → Fin dOut)
    (hInt : Integrable (fun z => ∏ r, z (a r))
      ((MLPShape.hidden tail : MLPShape dIn dOut).deepLinearOutputLaw Cw x)) :
    ∫ z, (∏ r, z (a r))
        ∂(MLPShape.hidden tail : MLPShape dIn dOut).deepLinearOutputLaw Cw x =
      ∫ y : Fin k → ℝ,
        (∫ z, (∏ r, z (a r)) ∂tail.deepLinearOutputLaw Cw y)
          ∂oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x := by
  rw [deepLinearOutputLaw_hidden_eq_bind tail Cw x]
  exact integral_monomial_deepLinearOutputLaw_bind tail Cw x m a
    (by simpa [deepLinearOutputLaw_hidden_eq_bind tail Cw x] using hInt)

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

/-- Absolute-value bound for the deterministic correlator amplitude: it grows at most like a
constant times `|q|^m`. -/
private lemma correlatorAmplitude_abs_bound (Cw : ℝ≥0) (q : ℝ) (m : ℕ) (widths : List ℕ) :
    |correlatorAmplitude Cw q m widths| ≤
      |((Cw : ℝ) ^ (widths.length + 1)) ^ m| * |hiddenWidthCorrection m widths| * |q| ^ m := by
  unfold correlatorAmplitude
  calc
    |((Cw : ℝ) ^ (widths.length + 1) * q) ^ m * hiddenWidthCorrection m widths|
        = |((Cw : ℝ) ^ (widths.length + 1)) ^ m * q ^ m * hiddenWidthCorrection m widths| := by
          rw [mul_pow]
    _ = |((Cw : ℝ) ^ (widths.length + 1)) ^ m| * |q| ^ m * |hiddenWidthCorrection m widths| := by
          simp_rw [abs_mul, abs_pow]
    _ ≤ |((Cw : ℝ) ^ (widths.length + 1)) ^ m| * |hiddenWidthCorrection m widths| * |q| ^ m := by
          have hEq :
              |((Cw : ℝ) ^ (widths.length + 1)) ^ m| * |q| ^ m * |hiddenWidthCorrection m widths| =
                |((Cw : ℝ) ^ (widths.length + 1)) ^ m| *
                  |hiddenWidthCorrection m widths| * |q| ^ m := by
            ring
          exact le_of_eq hEq

private lemma jointMoment_outputLaw_hidden_even_of_tail {dIn k dOut : ℕ}
    (tail : MLPShape k dOut) (Cw : ℝ≥0) (x : Fin dIn → ℝ) (m : ℕ)
    (a : Fin (2 * m) → Fin dOut)
    (_hIn : 0 < dIn)
    (hWidths : ∀ n ∈ (MLPShape.hidden tail : MLPShape dIn dOut).hiddenWidths, 0 < n)
    (ih : ∀ (y : Fin k → ℝ) (a : Fin (2 * m) → Fin dOut),
        0 < k → (∀ n ∈ tail.hiddenWidths, 0 < n) →
        ∫ z, (∏ r, z (a r)) ∂tail.deepLinearOutputLaw Cw y =
          pairingTensor a *
            correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy y) m tail.hiddenWidths)
    (ihInt : ∀ (y : Fin k → ℝ) (a : Fin (2 * m) → Fin dOut),
        0 < k → (∀ n ∈ tail.hiddenWidths, 0 < n) →
        Integrable (fun z => ∏ r, z (a r)) (tail.deepLinearOutputLaw Cw y)) :
    (∫ z, (∏ r, z (a r))
        ∂(MLPShape.hidden tail : MLPShape dIn dOut).deepLinearOutputLaw Cw x =
      pairingTensor a *
        correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy x) m
          (MLPShape.hidden tail : MLPShape dIn dOut).hiddenWidths) ∧
    Integrable (fun z => ∏ r, z (a r))
      ((MLPShape.hidden tail : MLPShape dIn dOut).deepLinearOutputLaw Cw x) := by
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
  let F : (Fin dOut → ℝ) → ℝ := fun z => ∏ r, z (a r)
  let μ₁ : Measure (LayerParams (Fin dIn) (Fin k)) :=
    layerGaussianInit (hyperparams Cw) (Fin dIn) (Fin k)
  let f : LayerParams (Fin dIn) (Fin k) → Fin k → ℝ :=
    fun q => (DenseLayer.ofParams q).preactivation x
  have hf_meas : Measurable f := by
    dsimp [f]
    exact DenseLayer.measurable_preactivation.comp
      (measurable_id.prodMk measurable_const)
  -- pointwise power-mean bound `‖F z‖ ≤ dOut^(m-1) * ∑_j z j^(2m)` (also covers `m = 0`).
  have hFpoint (z : Fin dOut → ℝ) :
      ‖F z‖ ≤ (Fintype.card (Fin dOut) : ℝ) ^ (m - 1) *
        (1 + ∑ j : Fin dOut, z j ^ (2 * m)) := by
    by_cases hm : m = 0
    · subst m
      dsimp [F]
      simp
    · have hmpos : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm)
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
            exact Finset.prod_le_prod₀ (fun r _ => abs_nonneg _) (fun r _ => hle r)
          _ = (Real.sqrt (∑ j : Fin dOut, z j ^ 2)) ^ (2 * m) := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ = (∑ j : Fin dOut, z j ^ 2) ^ m := by
            rw [pow_mul, Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (z j)))]
      have hpm := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
        (s := (Finset.univ : Finset (Fin dOut)))
        (f := fun j : Fin dOut => z j ^ 2)
        (p := (m : ℝ)) (hp := by exact_mod_cast hmpos) (hf := fun j _ => sq_nonneg (z j))
      have hpm' : (∑ j : Fin dOut, z j ^ 2) ^ m ≤
          (Fintype.card (Fin dOut) : ℝ) ^ (m - 1) *
            (1 + ∑ j : Fin dOut, z j ^ (2 * m)) := by
        have hpm2 : (∑ j : Fin dOut, z j ^ 2) ^ (m : ℝ) ≤
            (Fintype.card (Fin dOut) : ℝ) ^ ((m : ℝ) - 1) *
              ∑ j : Fin dOut, (z j ^ 2) ^ (m : ℝ) := by
          simpa [Finset.card_univ, Fintype.card_fin] using hpm
        have hpowle : (∑ j : Fin dOut, z j ^ 2) ^ m ≤
            (Fintype.card (Fin dOut) : ℝ) ^ (m - 1) *
              ∑ j : Fin dOut, z j ^ (2 * m) := by
          calc
            (∑ j : Fin dOut, z j ^ 2) ^ m = (∑ j : Fin dOut, z j ^ 2) ^ (m : ℝ) := by
              rw [Real.rpow_natCast]
            _ ≤ (Fintype.card (Fin dOut) : ℝ) ^ ((m : ℝ) - 1) *
                ∑ j : Fin dOut, (z j ^ 2) ^ (m : ℝ) := hpm2
            _ = (Fintype.card (Fin dOut) : ℝ) ^ (m - 1) *
                ∑ j : Fin dOut, z j ^ (2 * m) := by
              have hexp : ((m : ℝ) - 1) = ((m - 1 : ℕ) : ℝ) := by
                rw [Nat.cast_sub hmpos]
                norm_num
              rw [hexp, Real.rpow_natCast]
              congr 1
              apply Finset.sum_congr rfl
              intro j _
              rw [Real.rpow_natCast]
              simp [← pow_mul]
        have hcard : 0 ≤ (Fintype.card (Fin dOut) : ℝ) ^ (m - 1) := by positivity
        have hsum : 0 ≤ ∑ j : Fin dOut, z j ^ (2 * m) := by
          exact Finset.sum_nonneg (fun j _ =>
            by simpa [← pow_mul] using pow_nonneg (sq_nonneg (z j)) m)
        calc
          (∑ j : Fin dOut, z j ^ 2) ^ m ≤
              (Fintype.card (Fin dOut) : ℝ) ^ (m - 1) * ∑ j : Fin dOut, z j ^ (2 * m) := hpowle
          _ ≤ (Fintype.card (Fin dOut) : ℝ) ^ (m - 1) * (1 + ∑ j : Fin dOut, z j ^ (2 * m)) := by
                exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by norm_num)) hcard
      calc
        ‖F z‖ = |∏ r : Fin (2 * m), z (a r)| := by
          simp [F, Real.norm_eq_abs, Finset.abs_prod]
        _ ≤ (∑ j : Fin dOut, z j ^ 2) ^ m := hprod
        _ ≤ (Fintype.card (Fin dOut) : ℝ) ^ (m - 1) * (1 + ∑ j : Fin dOut, z j ^ (2 * m)) := hpm'
  -- fibre norm-integral bound via the tail moment formulas
  have hFnorm (y : Fin k → ℝ) :
      ∫ z, ‖F z‖ ∂(tail.deepLinearOutputLaw Cw y) ≤
        (Fintype.card (Fin dOut) : ℝ) ^ (m - 1) *
          (1 + ∑ j : Fin dOut,
            (pairingTensor (fun _ : Fin (2 * m) => j) *
              correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy y) m tail.hiddenWidths)) := by
    -- the tail law is a probability measure, so constants are integrable
    have hprob : IsProbabilityMeasure (tail.deepLinearOutputLaw Cw y) := by
      unfold MLPShape.deepLinearOutputLaw
      exact (Measure.isProbabilityMeasure_map_iff
        (((tail.measurable_eval (measurable_linear 1)).comp
          (measurable_id.prodMk measurable_const)).aemeasurable)).mpr inferInstance
    have hfin : IsFiniteMeasure (tail.deepLinearOutputLaw Cw y) :=
      ⟨by rw [hprob.measure_univ]; norm_num⟩
    have hint (j : Fin dOut) :
        Integrable (fun z : Fin dOut → ℝ => z j ^ (2 * m)) (tail.deepLinearOutputLaw Cw y) := by
      simpa using ihInt y (fun _ : Fin (2 * m) => j) hk hTailWidths
    have hsum : Integrable (fun z : Fin dOut → ℝ =>
        ∑ j : Fin dOut, z j ^ (2 * m)) (tail.deepLinearOutputLaw Cw y) := by
      simpa using (integrable_finsetSum Finset.univ
        (f := fun (j : Fin dOut) (z : Fin dOut → ℝ) => z j ^ (2 * m)) (fun j _ => hint j))
    have hone : Integrable (fun z : Fin dOut → ℝ => (1 : ℝ))
        (tail.deepLinearOutputLaw Cw y) :=
      @integrable_const (Fin dOut → ℝ) ℝ _ _ (by infer_instance : NormedAddCommGroup ℝ)
        hfin (1 : ℝ)
    have hsumInt : Integrable (fun z : Fin dOut → ℝ =>
        1 + ∑ j : Fin dOut, z j ^ (2 * m)) (tail.deepLinearOutputLaw Cw y) := by
      simpa using hsum.add hone
    have hmono : ∫ z, ‖F z‖ ∂(tail.deepLinearOutputLaw Cw y) ≤
        (Fintype.card (Fin dOut) : ℝ) ^ (m - 1) *
          ∫ z, (1 + ∑ j : Fin dOut, z j ^ (2 * m)) ∂(tail.deepLinearOutputLaw Cw y) := by
      rw [← MeasureTheory.integral_const_mul]
      have hFint : Integrable (fun z : Fin dOut → ℝ => ‖F z‖) (tail.deepLinearOutputLaw Cw y) :=
        (ihInt y a hk hTailWidths).norm
      exact integral_mono_ae hFint
        (hsumInt.const_mul ((Fintype.card (Fin dOut) : ℝ) ^ (m - 1)))
        (Filter.Eventually.of_forall fun z => hFpoint z)
    calc
      ∫ z, ‖F z‖ ∂(tail.deepLinearOutputLaw Cw y) ≤
          (Fintype.card (Fin dOut) : ℝ) ^ (m - 1) *
            ∫ z, (1 + ∑ j : Fin dOut, z j ^ (2 * m)) ∂(tail.deepLinearOutputLaw Cw y) := hmono
      _ = (Fintype.card (Fin dOut) : ℝ) ^ (m - 1) *
            (1 + ∑ j : Fin dOut, ∫ z, z j ^ (2 * m) ∂(tail.deepLinearOutputLaw Cw y)) := by
            congr 1
            rw [MeasureTheory.integral_add hone hsum]
            rw [MeasureTheory.integral_finsetSum (s := Finset.univ)
              (f := fun (j : Fin dOut) (z : Fin dOut → ℝ) => z j ^ (2 * m)) (fun j _ => hint j)]
            simp [MeasureTheory.integral_const, Measure.real, hprob.measure_univ]
      _ = (Fintype.card (Fin dOut) : ℝ) ^ (m - 1) *
            (1 + ∑ j : Fin dOut,
              (pairingTensor (fun _ : Fin (2 * m) => j) *
                correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy y) m
                  tail.hiddenWidths)) := by
            congr 1
            congr 1
            apply Finset.sum_congr rfl
            intro j _
            simpa using ih y (fun _ : Fin (2 * m) => j) hk hTailWidths
  -- the fibre-norm integral is integrable under the Gaussian parameter law
  have hnorm : Integrable (fun q : LayerParams (Fin dIn) (Fin k) =>
      ∫ z, ‖F z‖ ∂(tail.deepLinearOutputLaw Cw (f q))) μ₁ := by
    let C₀ : ℝ := (Fintype.card (Fin dOut) : ℝ) ^ (m - 1)
    let C₁ : ℝ :=
      (∑ j : Fin dOut, |pairingTensor (fun _ : Fin (2 * m) => j)|) *
        |((Cw : ℝ) ^ (tail.hiddenWidths.length + 1)) ^ m| *
        |hiddenWidthCorrection m tail.hiddenWidths|
    let C₂ : ℝ := (Fintype.card (Fin k) : ℝ) ^ (m - 1)
    have hamp (y : Fin k → ℝ) :
        ∑ j : Fin dOut,
          (pairingTensor (fun _ : Fin (2 * m) => j) *
            correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy y) m tail.hiddenWidths) ≤
          C₁ * NeuralNetwork.normalizedEnergy y ^ m := by
      calc
        ∑ j : Fin dOut,
            (pairingTensor (fun _ : Fin (2 * m) => j) *
              correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy y) m tail.hiddenWidths)
            ≤ ∑ j : Fin dOut,
                |pairingTensor (fun _ : Fin (2 * m) => j) *
                  correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy y) m
                    tail.hiddenWidths| := by
              exact Finset.sum_le_sum (fun j _ => le_abs_self _)
        _ ≤ ∑ j : Fin dOut,
              (|pairingTensor (fun _ : Fin (2 * m) => j)| *
                |((Cw : ℝ) ^ (tail.hiddenWidths.length + 1)) ^ m| *
                |hiddenWidthCorrection m tail.hiddenWidths| *
                NeuralNetwork.normalizedEnergy y ^ m) := by
              apply Finset.sum_le_sum
              intro j _
              have h := correlatorAmplitude_abs_bound Cw (NeuralNetwork.normalizedEnergy y) m
                tail.hiddenWidths
              have hq : |NeuralNetwork.normalizedEnergy y| = NeuralNetwork.normalizedEnergy y :=
                abs_of_nonneg (NeuralNetwork.normalizedEnergy_nonneg y)
              rw [abs_mul]
              calc
                |pairingTensor (fun _ : Fin (2 * m) => j)| *
                      |correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy y) m
                        tail.hiddenWidths|
                    ≤ |pairingTensor (fun _ : Fin (2 * m) => j)| *
                        (|((Cw : ℝ) ^ (tail.hiddenWidths.length + 1)) ^ m| *
                          |hiddenWidthCorrection m tail.hiddenWidths| *
                          |NeuralNetwork.normalizedEnergy y| ^ m) := by
                      exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
                _ = |pairingTensor (fun _ : Fin (2 * m) => j)| *
                      |((Cw : ℝ) ^ (tail.hiddenWidths.length + 1)) ^ m| *
                      |hiddenWidthCorrection m tail.hiddenWidths| *
                      NeuralNetwork.normalizedEnergy y ^ m := by
                      rw [hq]
                      ring
        _ = C₁ * NeuralNetwork.normalizedEnergy y ^ m := by
              dsimp [C₁]
              simp only [← Finset.mul_sum, mul_comm, mul_left_comm]
    have hnormEnergy : Integrable (fun q : LayerParams (Fin dIn) (Fin k) =>
        NeuralNetwork.normalizedEnergy (f q) ^ m) μ₁ := by
      by_cases hm : m = 0
      · subst m
        simp
      · have hmpos : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm)
        have hpre (p : Fin k) : Integrable (fun q : LayerParams (Fin dIn) (Fin k) =>
            (DenseLayer.ofParams q).preactivation x p ^ (2 * m)) μ₁ := by
          have h := integrable_pow_preactivation Cw (2 * m) p x
          refine Integrable.congr' h ?_ (Filter.Eventually.of_forall ?_)
          · exact ((((measurable_pi_apply p).comp (DenseLayer.measurable_preactivation.comp
              (measurable_id.prodMk measurable_const))).pow_const (2 * m))).aestronglyMeasurable
          · intro q
            simp_rw [Real.norm_eq_abs, abs_pow, abs_abs]
        have hsum : Integrable (fun q : LayerParams (Fin dIn) (Fin k) =>
            ∑ p : Fin k, (DenseLayer.ofParams q).preactivation x p ^ (2 * m)) μ₁ := by
          simpa using (integrable_finsetSum Finset.univ
            (f := fun (p : Fin k) (q : LayerParams (Fin dIn) (Fin k)) =>
              (DenseLayer.ofParams q).preactivation x p ^ (2 * m)) (fun p _ => hpre p))
        have hmeasE : Measurable (fun q : LayerParams (Fin dIn) (Fin k) =>
            NeuralNetwork.normalizedEnergy (f q)) := by
          dsimp [f, NeuralNetwork.normalizedEnergy]
          have hsumm : Measurable (fun q : LayerParams (Fin dIn) (Fin k) =>
              ∑ p : Fin k, ((DenseLayer.ofParams q).preactivation x p) ^ 2) := by
            refine Finset.measurable_sum Finset.univ (fun p _ => ?_)
            exact ((((measurable_pi_apply p).comp (DenseLayer.measurable_preactivation.comp
              (measurable_id.prodMk measurable_const)))).pow_const 2)
          simpa [Fintype.card_fin] using hsumm.const_mul ((Fintype.card (Fin k) : ℝ)⁻¹)
        let hcoef : ℝ := (Fintype.card (Fin k) : ℝ) ^ (m - 1) * ((Fintype.card (Fin k) : ℝ)⁻¹) ^ m
        have hdom : Integrable (fun q : LayerParams (Fin dIn) (Fin k) =>
            hcoef * (1 + ∑ p : Fin k, (DenseLayer.ofParams q).preactivation x p ^ (2 * m))) μ₁ := by
          have hsum' : Integrable (fun q : LayerParams (Fin dIn) (Fin k) =>
              hcoef * ∑ p : Fin k,
                (DenseLayer.ofParams q).preactivation x p ^ (2 * m) + hcoef) μ₁ :=
            (hsum.const_mul hcoef).add (integrable_const hcoef)
          convert hsum' using 1
          funext q
          ring
        refine Integrable.mono' hdom ?_ (Filter.Eventually.of_forall ?_)
        · exact (hmeasE.pow_const m).aestronglyMeasurable
        · intro q
          have hpm' : (∑ p : Fin k, (DenseLayer.ofParams q).preactivation x p ^ 2) ^ m ≤
              (Fintype.card (Fin k) : ℝ) ^ (m - 1) *
                ∑ p : Fin k, (DenseLayer.ofParams q).preactivation x p ^ (2 * m) := by
            simpa [Fintype.card_fin, pow_mul] using
              (sum_pow_le_card_pow_mul_sum_pow_nat
                (fun p : Fin k => (DenseLayer.ofParams q).preactivation x p ^ 2) m hmpos
                (fun p => sq_nonneg _))
          have hnormE : NeuralNetwork.normalizedEnergy (f q) ^ m =
              ((Fintype.card (Fin k) : ℝ)⁻¹) ^ m * (∑ p : Fin k,
                (DenseLayer.ofParams q).preactivation x p ^ 2) ^ m := by
            dsimp [f]
            simp only [NeuralNetwork.normalizedEnergy, Fintype.card_fin]
            rw [mul_pow]
          calc
            ‖NeuralNetwork.normalizedEnergy (f q) ^ m‖
                = NeuralNetwork.normalizedEnergy (f q) ^ m := by
                  rw [Real.norm_eq_abs]
                  exact abs_of_nonneg (pow_nonneg (NeuralNetwork.normalizedEnergy_nonneg (f q)) m)
            _ = ((Fintype.card (Fin k) : ℝ)⁻¹) ^ m * (∑ p : Fin k,
                (DenseLayer.ofParams q).preactivation x p ^ 2) ^ m := hnormE
            _ ≤ ((Fintype.card (Fin k) : ℝ)⁻¹) ^ m *
                  ((Fintype.card (Fin k) : ℝ) ^ (m - 1) *
                    ∑ p : Fin k, (DenseLayer.ofParams q).preactivation x p ^ (2 * m)) := by
                  exact mul_le_mul_of_nonneg_left hpm' (pow_nonneg (inv_nonneg.mpr
                    (Nat.cast_nonneg _)) _)
            _ = ((Fintype.card (Fin k) : ℝ) ^ (m - 1) * ((Fintype.card (Fin k) : ℝ)⁻¹) ^ m) *
                  ∑ p : Fin k, (DenseLayer.ofParams q).preactivation x p ^ (2 * m) := by
                  ring
            _ ≤ ((Fintype.card (Fin k) : ℝ) ^ (m - 1) * ((Fintype.card (Fin k) : ℝ)⁻¹) ^ m) *
                  (1 + ∑ p : Fin k, (DenseLayer.ofParams q).preactivation x p ^ (2 * m)) := by
                  have hnon : 0 ≤ ∑ p : Fin k,
                      (DenseLayer.ofParams q).preactivation x p ^ (2 * m) := by
                    exact Finset.sum_nonneg (fun p _ =>
                      by simpa [pow_mul, mul_comm] using
                        sq_nonneg ((DenseLayer.ofParams q).preactivation x p ^ m))
                  have hcoef : 0 ≤ (Fintype.card (Fin k) : ℝ) ^ (m - 1) *
                      ((Fintype.card (Fin k) : ℝ)⁻¹) ^ m := by positivity
                  nlinarith
    -- assemble `hnorm` from `hFnorm ∘ f`, `hamp`, and `hnormEnergy`.
    have hdom : Integrable (fun q : LayerParams (Fin dIn) (Fin k) =>
        (C₀ * (1 + C₁)) * (1 + NeuralNetwork.normalizedEnergy (f q) ^ m)) μ₁ := by
      have hsum' : Integrable (fun q : LayerParams (Fin dIn) (Fin k) =>
          (C₀ * (1 + C₁)) * NeuralNetwork.normalizedEnergy (f q) ^ m + (C₀ * (1 + C₁))) μ₁ :=
        (hnormEnergy.const_mul (C₀ * (1 + C₁))).add (integrable_const (C₀ * (1 + C₁)))
      convert hsum' using 1
      funext q
      ring
    refine Integrable.mono' hdom ?_ (Filter.Eventually.of_forall ?_)
    · -- measurability of the fibre norm-integral `q ↦ ∫ z, ‖F z‖ ∂(tail law (f q))`
      have hg : Measurable (fun z : Fin dOut → ℝ => ENNReal.ofReal ‖F z‖) := by
        exact ENNReal.measurable_ofReal.comp (measurable_monomial a).norm
      have hlin : Measurable (fun q : LayerParams (Fin dIn) (Fin k) =>
          ∫⁻ z, ENNReal.ofReal ‖F z‖ ∂(tail.deepLinearOutputLaw Cw (f q))) := by
        exact (Measure.measurable_lintegral hg).comp
          ((measurable_deepLinearOutputLaw_kernel tail Cw).comp hf_meas)
      have hEq : (fun q : LayerParams (Fin dIn) (Fin k) =>
          ∫ z, ‖F z‖ ∂(tail.deepLinearOutputLaw Cw (f q))) =
        fun q => (∫⁻ z, ENNReal.ofReal ‖F z‖ ∂(tail.deepLinearOutputLaw Cw (f q))).toReal := by
        funext q
        exact integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall (fun z => norm_nonneg (F z)))
          ((measurable_monomial a).norm.aestronglyMeasurable)
      rw [hEq]
      exact (ENNReal.measurable_toReal.comp hlin).aestronglyMeasurable
    · intro q
      have hb := hFnorm (f q)
      have ha := hamp (f q)
      have hE : 0 ≤ NeuralNetwork.normalizedEnergy (f q) ^ m :=
        pow_nonneg (NeuralNetwork.normalizedEnergy_nonneg (f q)) m
      have hC₀ : 0 ≤ C₀ := by
        dsimp [C₀]
        positivity
      calc
        ‖∫ z, ‖F z‖ ∂(tail.deepLinearOutputLaw Cw (f q))‖
            = ∫ z, ‖F z‖ ∂(tail.deepLinearOutputLaw Cw (f q)) := by
              rw [Real.norm_eq_abs]
              exact abs_of_nonneg (MeasureTheory.integral_nonneg (fun z => norm_nonneg (F z)))
        _ ≤ C₀ * (1 + ∑ j : Fin dOut,
              (pairingTensor (fun _ : Fin (2 * m) => j) *
                correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy (f q)) m
                  tail.hiddenWidths)) := by
              dsimp [C₀]
              exact hb
        _ ≤ C₀ * (1 + C₁ * NeuralNetwork.normalizedEnergy (f q) ^ m) := by
              exact mul_le_mul_of_nonneg_left (by nlinarith [ha]) hC₀
        _ = C₀ + C₀ * C₁ * NeuralNetwork.normalizedEnergy (f q) ^ m := by ring
        _ ≤ C₀ * (1 + C₁) * (1 + NeuralNetwork.normalizedEnergy (f q) ^ m) := by
              have hC₁ : 0 ≤ C₁ := by
                dsimp [C₁]
                positivity
              nlinarith [mul_nonneg hC₀ hC₁, mul_nonneg hC₀ hE]
    -- integrability of the monomial under the hidden law
  have hInt : Integrable F
      ((MLPShape.hidden tail : MLPShape dIn dOut).deepLinearOutputLaw Cw x) := by
    rw [deepLinearOutputLaw_hidden_eq_bind tail Cw x]
    have hpull : (μ₁.map f).bind (fun y : Fin k → ℝ => tail.deepLinearOutputLaw Cw y) =
        μ₁.bind (fun q => tail.deepLinearOutputLaw Cw (f q)) := by
      exact measure_bind_map_comp μ₁ hf_meas (measurable_deepLinearOutputLaw_kernel tail Cw)
    let η' : Kernel (LayerParams (Fin dIn) (Fin k)) (Fin dOut → ℝ) :=
      ⟨fun q => tail.deepLinearOutputLaw Cw (f q),
        (measurable_deepLinearOutputLaw_kernel tail Cw).comp hf_meas⟩
    have hFmeas : AEStronglyMeasurable F (η' ∘ₘ μ₁) :=
      (measurable_monomial a).aestronglyMeasurable
    have hIntComp := (Measure.integrable_comp_iff (μ := μ₁) (κ := η') (f := F) hFmeas).2
    have hconj1 : ∀ᵐ q ∂μ₁, Integrable F (η' q) := by
      filter_upwards with q
      dsimp [η', F]
      exact ihInt (f q) a hk hTailWidths
    have hconj2 : Integrable (fun q => ∫ z, ‖F z‖ ∂η' q) μ₁ := by
      dsimp [η', F]
      exact hnorm
    have hIntBind : Integrable F (η' ∘ₘ μ₁) := (hIntComp ⟨hconj1, hconj2⟩)
    -- bridge the bind form back to the hidden-shape law
    have hbind : (oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x).bind
          (fun y => tail.deepLinearOutputLaw Cw y) = η' ∘ₘ μ₁ := by
      calc
        (oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x).bind
            (fun y => tail.deepLinearOutputLaw Cw y)
            = (μ₁.map f).bind (fun y : Fin k → ℝ => tail.deepLinearOutputLaw Cw y) := by
              dsimp [μ₁, f, oneLayerOutputLaw]
        _ = μ₁.bind (fun q => tail.deepLinearOutputLaw Cw (f q)) := hpull
        _ = η' ∘ₘ μ₁ := rfl
    rw [hbind]
    simpa [F] using hIntBind
  exact ⟨
    calc
      ∫ z, (∏ r, z (a r))
          ∂(MLPShape.hidden tail : MLPShape dIn dOut).deepLinearOutputLaw Cw x =
          ∫ y : Fin k → ℝ,
            (∫ z, (∏ r, z (a r)) ∂tail.deepLinearOutputLaw Cw y)
              ∂oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw x := by
            exact integral_monomial_deepLinearOutputLaw_hidden_bind tail Cw x m a hInt
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
            rw [hHiddenWidths],
    hInt
  ⟩

/-- Combined even-moment formula and monomial integrability for every finite-width shape.

Informal proof: induction over the shape.  The output case is the product-Gaussian Wick theorem
(`jointMoment_outputLaw_output_even`) and Gaussian `L^p` finiteness
(`integrable_monomial_outputLaw_even`).  In the hidden case the induction hypothesis supplies both
the tail moment formulas and the tail integrability; the latter makes the tower-property
integrability side condition available for `integral_monomial_deepLinearOutputLaw_hidden_bind`. -/
private theorem jointMoment_outputLaw_even_and_integrable {dIn dOut : ℕ} (S : MLPShape dIn dOut)
    (Cw : ℝ≥0) (hIn : 0 < dIn) (hWidths : ∀ n ∈ S.hiddenWidths, 0 < n) :
    (∀ (x : Fin dIn → ℝ) (m : ℕ) (a : Fin (2 * m) → Fin dOut),
      ∫ z, (∏ r, z (a r)) ∂S.deepLinearOutputLaw Cw x =
        pairingTensor a *
          correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy x) m S.hiddenWidths) ∧
    (∀ (x : Fin dIn → ℝ) (m : ℕ) (a : Fin (2 * m) → Fin dOut),
      Integrable (fun z => ∏ r, z (a r)) (S.deepLinearOutputLaw Cw x)) := by
  induction S with
  | output =>
      constructor
      · intro x m a
        exact jointMoment_outputLaw_output_even Cw x m a hIn
      · intro x m a
        exact integrable_monomial_outputLaw_even Cw x m a
  | hidden tail ih =>
      rename_i m n k
      have hHiddenWidths :
          (MLPShape.hidden tail : MLPShape m n).hiddenWidths = k :: tail.hiddenWidths :=
        hidden_hiddenWidths_cons (dIn := m) tail
      have hk : 0 < k := by
        apply hWidths k
        rw [hHiddenWidths]
        simp
      have hTailWidths : ∀ n ∈ tail.hiddenWidths, 0 < n := by
        intro n hn
        apply hWidths n
        rw [hHiddenWidths]
        exact List.mem_cons_of_mem k hn
      constructor
      · intro x m a
        have ihMoment : ∀ (y : Fin k → ℝ) (a : Fin (2 * m) → Fin n), 0 < k →
            (∀ n₁ ∈ tail.hiddenWidths, 0 < n₁) →
            ∫ z, (∏ r, z (a r)) ∂tail.deepLinearOutputLaw Cw y =
              pairingTensor a *
                correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy y) m tail.hiddenWidths :=
          fun y a' hk' hw => (ih hk' hw).1 y m a'
        have ihInt : ∀ (y : Fin k → ℝ) (a : Fin (2 * m) → Fin n), 0 < k →
            (∀ n₁ ∈ tail.hiddenWidths, 0 < n₁) →
            Integrable (fun z => ∏ r, z (a r)) (tail.deepLinearOutputLaw Cw y) :=
          fun y a' hk' hw => (ih hk' hw).2 y m a'
        exact (jointMoment_outputLaw_hidden_even_of_tail tail Cw x m a hIn hWidths ihMoment ihInt).1
      · intro x m a
        have ihMoment : ∀ (y : Fin k → ℝ) (a : Fin (2 * m) → Fin n), 0 < k →
            (∀ n₁ ∈ tail.hiddenWidths, 0 < n₁) →
            ∫ z, (∏ r, z (a r)) ∂tail.deepLinearOutputLaw Cw y =
              pairingTensor a *
                correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy y) m tail.hiddenWidths :=
          fun y a' hk' hw => (ih hk' hw).1 y m a'
        have ihInt : ∀ (y : Fin k → ℝ) (a : Fin (2 * m) → Fin n), 0 < k →
            (∀ n₁ ∈ tail.hiddenWidths, 0 < n₁) →
            Integrable (fun z => ∏ r, z (a r)) (tail.deepLinearOutputLaw Cw y) :=
          fun y a' hk' hw => (ih hk' hw).2 y m a'
        exact (jointMoment_outputLaw_hidden_even_of_tail tail Cw x m a hIn hWidths ihMoment ihInt).2

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
        correlatorAmplitude Cw (NeuralNetwork.normalizedEnergy x) m S.hiddenWidths :=
  (jointMoment_outputLaw_even_and_integrable S Cw hIn hWidths).1 x m a

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

/-- Centeredness reduction for two batch-output coordinates.

Informal proof: first prove `MemLp`/integrability for the two coordinate maps by the polynomial
Gaussian moment bounds already developed for the output law.  The law is invariant under negating
the final layer (the batch analogue of `deepLinearOutputLaw_isNegInvariant`), while each coordinate
is odd under this involution, so both expectations vanish.  Mathlib's covariance identity
`ProbabilityTheory.covariance_eq_sub` then reduces the covariance to the uncentered second moment.
This is the standard symmetry argument behind `jointMoment_outputLaw_odd` above.
-/
lemma covariance_batchOutputLaw_eq_integral_mul {A : Type uA}
    {dIn dOut : ℕ} (S : MLPShape dIn dOut) (Cw : ℝ≥0)
    (D : A → Fin dIn → ℝ) (a b : A) (i j : Fin dOut)
    (_hIn : 0 < dIn) (_hWidths : ∀ n ∈ S.hiddenWidths, 0 < n) :
    covariance (fun z => z a i) (fun z => z b j) (S.deepLinearBatchLaw Cw D) =
      ∫ z, z a i * z b j ∂S.deepLinearBatchLaw Cw D := by
  let μ : Measure (A → Fin dOut → ℝ) := S.deepLinearBatchLaw Cw D
  have hneg : Measure.IsNegInvariant μ := deepLinearBatchLaw_isNegInvariant S Cw D
  have hX_meas : Measurable (fun z : A → Fin dOut → ℝ => z a i) :=
    (measurable_pi_apply i).comp (measurable_pi_apply a)
  have hY_meas : Measurable (fun z : A → Fin dOut → ℝ => z b j) :=
    (measurable_pi_apply j).comp (measurable_pi_apply b)
  have hX0 : ∫ z, z a i ∂μ = 0 := by
    exact @Renormalization.integral_eq_zero_of_odd_of_aestronglyMeasurable
      (A → Fin dOut → ℝ) _ _ _ μ hneg (fun z => z a i)
      hX_meas.aestronglyMeasurable (fun z => by simp)
  have hY0 : ∫ z, z b j ∂μ = 0 := by
    exact @Renormalization.integral_eq_zero_of_odd_of_aestronglyMeasurable
      (A → Fin dOut → ℝ) _ _ _ μ hneg (fun z => z b j)
      hY_meas.aestronglyMeasurable (fun z => by simp)
  simp [covariance, μ, hX0, hY0]

/-- The batch law of a single bias-free initialized affine layer.

This is the batch analogue of `oneLayerOutputLaw`; it keeps the sample index `A` explicit rather
than bundling a finite batch into a Euclidean vector. -/
private def oneLayerBatchLaw {A : Type uA} {ι : Type uJ} {κ : Type*}
    [Fintype ι] [Fintype κ] (Cw : ℝ≥0) (D : A → ι → ℝ) :
    Measure (A → κ → ℝ) :=
  Measure.map (fun q : LayerParams ι κ =>
      fun a : A => (DenseLayer.ofParams q).preactivation (D a))
    (layerGaussianInit (hyperparams Cw) ι κ)

/-- For centered random variables, the mixed second moment equals the covariance. -/
private lemma integral_mul_eq_covariance_of_centered {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (X Y : α → ℝ)
    (hX0 : ∫ x, X x ∂μ = 0) (hY0 : ∫ x, Y x ∂μ = 0) :
    ∫ x, X x * Y x ∂μ = ProbabilityTheory.covariance X Y μ := by
  unfold ProbabilityTheory.covariance
  simp [hX0, hY0]

/-- Coordinate two-point function for the arbitrary-batch one-layer law.

This is the reusable analytic core behind `integral_mul_oneLayerBatchLaw`.  Informally, push the
integral through the defining `Measure.map`, unfold `DenseLayer.preactivation`, expand the two
finite sums over input coordinates, and use the product Gaussian initialization.  Biases vanish
because `hyperparams_biasVariance` makes their law `gaussianReal 0 0 = dirac 0`; weights have
centered independent coordinates, so Wick/Isserlis with two factors gives
`E[W i p * W j q] = if i = j then if p = q then (Cw / Fintype.card ι : ℝ≥0) else 0 else 0`.
Contracting the two finite sums leaves exactly
`(if i = j then (Cw : ℝ) * NeuralNetwork.normalizedGram D a b else 0)`, including the degenerate
empty-input case by Lean's zero-division convention.  This is the standard one-layer NNGP
covariance computation; see Isserlis' theorem
<https://en.wikipedia.org/wiki/Isserlis%27s_theorem> and Lee et al.,
"Deep Neural Networks as Gaussian Processes", Eq. (2), <https://arxiv.org/abs/1711.00165>.
-/
private lemma integral_mul_oneLayerBatchLaw_eq_sum_cov {A : Type uA} {ι : Type uJ} {κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ] (Cw : ℝ≥0) (D : A → ι → ℝ)
    (a b : A) (i j : κ) :
    ∫ y, y a i * y b j ∂oneLayerBatchLaw (ι := ι) (κ := κ) Cw D =
      if i = j then (Cw : ℝ) * NeuralNetwork.normalizedGram D a b else 0 := by
  classical
  let μ : Measure (LayerParams ι κ) := layerGaussianInit (hyperparams Cw) ι κ
  have hμ_prob : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  -- Coordinate means vanish and each coordinate lies in `L²`.
  have hw0 (j : κ) (p : ι) : ∫ q : LayerParams ι κ, q.1 j p ∂μ = 0 := by
    dsimp [μ]
    exact integral_weight_layerGaussianInit (hyperparams Cw) ι κ j p
  have hb0 (j : κ) : ∫ q : LayerParams ι κ, q.2 j ∂μ = 0 := by
    dsimp [μ]
    exact integral_bias_layerGaussianInit (hyperparams Cw) ι κ j
  have hwlp (j : κ) (p : ι) : MemLp (fun q : LayerParams ι κ => q.1 j p) 2 μ := by
    let X : LayerParams ι κ → ℝ := fun q => q.1 j p
    have hX : AEMeasurable X μ :=
      ((measurable_pi_apply p).comp ((measurable_pi_apply j).comp measurable_fst)).aemeasurable
    have hmem : MemLp (id : ℝ → ℝ) 2 (Measure.map X μ) := by
      dsimp [μ, X]
      rw [map_weight_layerGaussianInit (hyperparams Cw) ι κ j p]
      exact memLp_id_gaussianReal 2
    exact (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (p := 2) (f := X)
      (by exact measurable_id.aestronglyMeasurable) hX).1 hmem
  have hblp (j : κ) : MemLp (fun q : LayerParams ι κ => q.2 j) 2 μ := by
    let X : LayerParams ι κ → ℝ := fun q => q.2 j
    have hX : AEMeasurable X μ := ((measurable_pi_apply j).comp measurable_snd).aemeasurable
    have hmem : MemLp (id : ℝ → ℝ) 2 (Measure.map X μ) := by
      dsimp [μ, X]
      rw [map_bias_layerGaussianInit (hyperparams Cw) ι κ j]
      exact memLp_id_gaussianReal 2
    exact (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (p := 2) (f := X)
      (by exact measurable_id.aestronglyMeasurable) hX).1 hmem
  -- Second moments of the Gaussian coordinates.
  have hww (p p' : ι) :
      ∫ q : LayerParams ι κ, q.1 i p * q.1 j p' ∂μ =
        if i = j ∧ p = p' then (scaledWeightVariance (hyperparams Cw) ι : ℝ) else 0 := by
    calc
      ∫ q : LayerParams ι κ, q.1 i p * q.1 j p' ∂μ
          = ProbabilityTheory.covariance (fun q : LayerParams ι κ => q.1 i p)
              (fun q => q.1 j p') μ := by
            exact integral_mul_eq_covariance_of_centered μ
              (fun q : LayerParams ι κ => q.1 i p) (fun q => q.1 j p')
              (hw0 i p) (hw0 j p')
      _ = if i = j ∧ p = p' then (scaledWeightVariance (hyperparams Cw) ι : ℝ) else 0 := by
            have h := covariance_weight_layerGaussianInit (hyperparams Cw) ι κ i j p p'
            dsimp [μ] at h ⊢
            have hcast :
                (↑(if i = j ∧ p = p' then scaledWeightVariance (hyperparams Cw) ι else 0) : ℝ) =
                  if i = j ∧ p = p' then (scaledWeightVariance (hyperparams Cw) ι : ℝ) else 0 := by
              by_cases hijp : i = j ∧ p = p' <;> simp [hijp]
            exact h.trans hcast
  have hbb : ∫ q : LayerParams ι κ, q.2 i * q.2 j ∂μ = 0 := by
    calc
      ∫ q : LayerParams ι κ, q.2 i * q.2 j ∂μ
          = ProbabilityTheory.covariance (fun q : LayerParams ι κ => q.2 i)
              (fun q => q.2 j) μ := by
            exact integral_mul_eq_covariance_of_centered μ
              (fun q : LayerParams ι κ => q.2 i) (fun q => q.2 j)
              (hb0 i) (hb0 j)
      _ = 0 := by
            have h := covariance_bias_layerGaussianInit (hyperparams Cw) ι κ i j
            dsimp [μ] at h ⊢
            have hcast : (↑(if i = j then (0 : ℝ≥0) else 0) : ℝ) = 0 := by
              by_cases hij : i = j <;> simp [hij]
            rw [hcast] at h
            exact h
  have hwb (p : ι) : ∫ q : LayerParams ι κ, q.1 i p * q.2 j ∂μ = 0 := by
    calc
      ∫ q : LayerParams ι κ, q.1 i p * q.2 j ∂μ
          = ProbabilityTheory.covariance (fun q : LayerParams ι κ => q.1 i p)
              (fun q => q.2 j) μ := by
            exact integral_mul_eq_covariance_of_centered μ
              (fun q : LayerParams ι κ => q.1 i p) (fun q => q.2 j)
              (hw0 i p) (hb0 j)
      _ = 0 := by
            dsimp [μ]
            exact covariance_weight_bias_layerGaussianInit (hyperparams Cw) ι κ i p j
  have hbw (p' : ι) : ∫ q : LayerParams ι κ, q.2 i * q.1 j p' ∂μ = 0 := by
    calc
      ∫ q : LayerParams ι κ, q.2 i * q.1 j p' ∂μ
          = ProbabilityTheory.covariance (fun q : LayerParams ι κ => q.2 i)
              (fun q => q.1 j p') μ := by
            exact integral_mul_eq_covariance_of_centered μ
              (fun q : LayerParams ι κ => q.2 i) (fun q => q.1 j p')
              (hb0 i) (hw0 j p')
      _ = 0 := by
            rw [covariance_comm]
            dsimp [μ]
            exact covariance_weight_bias_layerGaussianInit (hyperparams Cw) ι κ j p' i
  -- Integrability of the coordinate products.
  have hww_int (p p' : ι) : Integrable (fun q : LayerParams ι κ => q.1 i p * q.1 j p') μ :=
    (hwlp i p).integrable_mul (hwlp j p')
  have hwb_int (p : ι) : Integrable (fun q : LayerParams ι κ => q.1 i p * q.2 j) μ :=
    (hwlp i p).integrable_mul (hblp j)
  have hbw_int (p' : ι) : Integrable (fun q : LayerParams ι κ => q.2 i * q.1 j p') μ :=
    (hblp i).integrable_mul (hwlp j p')
  -- Push the integral through the defining pushforward.
  have hmap :
      ∫ y, y a i * y b j ∂oneLayerBatchLaw (ι := ι) (κ := κ) Cw D =
        ∫ q : LayerParams ι κ,
          (DenseLayer.ofParams q).preactivation (D a) i *
            (DenseLayer.ofParams q).preactivation (D b) j ∂μ := by
    let φ : LayerParams ι κ → A → κ → ℝ :=
      fun q a => (DenseLayer.ofParams q).preactivation (D a)
    have hφ_meas : AEMeasurable φ μ := by
      dsimp [φ]
      exact (Measurable.of_eval (fun a : A =>
        (DenseLayer.measurable_preactivation.comp
          (measurable_id.prodMk measurable_const)))).aemeasurable
    have hG_meas : AEStronglyMeasurable (fun y : A → κ → ℝ => y a i * y b j) (μ.map φ) := by
      exact (by fun_prop : Measurable (fun y : A → κ → ℝ => y a i * y b j)).aestronglyMeasurable
    calc
      ∫ y, y a i * y b j ∂oneLayerBatchLaw (ι := ι) (κ := κ) Cw D
          = ∫ y, y a i * y b j ∂(μ.map φ) := by
            dsimp [oneLayerBatchLaw, μ, φ]
      _ = ∫ q : LayerParams ι κ,
            (DenseLayer.ofParams q).preactivation (D a) i *
              (DenseLayer.ofParams q).preactivation (D b) j ∂μ := by
            simpa [φ] using MeasureTheory.integral_map hφ_meas hG_meas
  -- Expand the two preactivations into bias plus input-sum and integrate term by term.
  have hpa (x : ι → ℝ) (k : κ) (q : LayerParams ι κ) :
      (DenseLayer.ofParams q).preactivation x k = q.2 k + ∑ p : ι, q.1 k p * x p := by
    simp [DenseLayer.ofParams]
  have hT1_int : Integrable (fun q : LayerParams ι κ => q.2 i * q.2 j) μ :=
    (hblp i).integrable_mul (hblp j)
  have hT2_int : Integrable (fun q : LayerParams ι κ =>
      q.2 i * (∑ p' : ι, q.1 j p' * D b p')) μ := by
    have hsum : Integrable (fun q : LayerParams ι κ =>
        ∑ p' : ι, q.2 i * q.1 j p' * D b p') μ := by
      refine integrable_finsetSum Finset.univ (μ := μ)
        (f := fun (p' : ι) (q : LayerParams ι κ) => q.2 i * q.1 j p' * D b p')
        (fun p' _ => ?_)
      simpa using (hbw_int p').mul_const (D b p')
    refine Integrable.congr' hsum ?_ (Filter.Eventually.of_forall ?_)
    · exact (by fun_prop : Measurable (fun q : LayerParams ι κ =>
        q.2 i * (∑ p' : ι, q.1 j p' * D b p'))).aestronglyMeasurable
    · intro q
      have hEq : q.2 i * (∑ p' : ι, q.1 j p' * D b p') =
          ∑ p' : ι, q.2 i * q.1 j p' * D b p' := by
        simp_rw [Finset.mul_sum, ← mul_assoc]
      rw [hEq]
  have hT3_int : Integrable (fun q : LayerParams ι κ =>
      (∑ p : ι, q.1 i p * D a p) * q.2 j) μ := by
    have hsum : Integrable (fun q : LayerParams ι κ =>
        ∑ p : ι, q.1 i p * q.2 j * D a p) μ := by
      refine integrable_finsetSum Finset.univ (μ := μ)
        (f := fun (p : ι) (q : LayerParams ι κ) => q.1 i p * q.2 j * D a p)
        (fun p _ => ?_)
      simpa using (hwb_int p).mul_const (D a p)
    refine Integrable.congr' hsum ?_ (Filter.Eventually.of_forall ?_)
    · exact (by fun_prop : Measurable (fun q : LayerParams ι κ =>
        (∑ p : ι, q.1 i p * D a p) * q.2 j)).aestronglyMeasurable
    · intro q
      have hEq : (∑ p : ι, q.1 i p * D a p) * q.2 j =
          ∑ p : ι, q.1 i p * q.2 j * D a p := by
        simp_rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro p _
        ring
      rw [hEq]
  have hT4_int : Integrable (fun q : LayerParams ι κ =>
      (∑ p : ι, q.1 i p * D a p) * (∑ p' : ι, q.1 j p' * D b p')) μ := by
    have hsum : Integrable (fun q : LayerParams ι κ =>
        ∑ p : ι, ∑ p' : ι, q.1 i p * q.1 j p' * (D a p * D b p')) μ := by
      refine integrable_finsetSum Finset.univ (μ := μ)
        (f := fun (p : ι) (q : LayerParams ι κ) =>
          ∑ p' : ι, q.1 i p * q.1 j p' * (D a p * D b p'))
        (fun p _ => ?_)
      refine integrable_finsetSum Finset.univ (μ := μ)
        (f := fun (p' : ι) (q : LayerParams ι κ) =>
          q.1 i p * q.1 j p' * (D a p * D b p'))
        (fun p' _ => ?_)
      simpa using (hww_int p p').mul_const (D a p * D b p')
    refine Integrable.congr' hsum ?_ (Filter.Eventually.of_forall ?_)
    · exact (by fun_prop : Measurable (fun q : LayerParams ι κ =>
        (∑ p : ι, q.1 i p * D a p) * (∑ p' : ι, q.1 j p' * D b p'))).aestronglyMeasurable
    · intro q
      have hEq : (∑ p : ι, q.1 i p * D a p) * (∑ p' : ι, q.1 j p' * D b p') =
          ∑ p : ι, ∑ p' : ι, q.1 i p * q.1 j p' * (D a p * D b p') := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro p' _
        ring
      rw [hEq]
  -- Values of the four summands.
  have hT1 : ∫ q : LayerParams ι κ, q.2 i * q.2 j ∂μ = 0 := hbb
  have hT2 : ∫ q : LayerParams ι κ, q.2 i * (∑ p' : ι, q.1 j p' * D b p') ∂μ = 0 := by
    calc
      ∫ q : LayerParams ι κ, q.2 i * (∑ p' : ι, q.1 j p' * D b p') ∂μ
          = ∑ p' : ι, ∫ q : LayerParams ι κ, q.2 i * q.1 j p' * D b p' ∂μ := by
            rw [show (fun q : LayerParams ι κ => q.2 i * (∑ p' : ι, q.1 j p' * D b p')) =
                fun q => ∑ p' : ι, q.2 i * q.1 j p' * D b p' from by
                  funext q
                  simp_rw [Finset.mul_sum, ← mul_assoc]]
            rw [MeasureTheory.integral_finsetSum Finset.univ
              (f := fun (p' : ι) (q : LayerParams ι κ) => q.2 i * q.1 j p' * D b p')
              (fun p' _ => by
                simpa using (hbw_int p').mul_const (D b p'))]
      _ = 0 := by
            have hinner : ∀ p' : ι, ∫ q : LayerParams ι κ, q.2 i * q.1 j p' * D b p' ∂μ = 0 := by
              intro p'
              calc
                ∫ q : LayerParams ι κ, q.2 i * q.1 j p' * D b p' ∂μ
                    = (∫ q : LayerParams ι κ, q.2 i * q.1 j p' ∂μ) * D b p' := by
                      exact integral_mul_const (D b p')
                        (fun q : LayerParams ι κ => q.2 i * q.1 j p')
                _ = 0 := by simp [hbw p']
            simp [hinner]
  have hT3 : ∫ q : LayerParams ι κ, (∑ p : ι, q.1 i p * D a p) * q.2 j ∂μ = 0 := by
    calc
      ∫ q : LayerParams ι κ, (∑ p : ι, q.1 i p * D a p) * q.2 j ∂μ
          = ∑ p : ι, ∫ q : LayerParams ι κ, q.1 i p * q.2 j * D a p ∂μ := by
            rw [show (fun q : LayerParams ι κ => (∑ p : ι, q.1 i p * D a p) * q.2 j) =
                fun q => ∑ p : ι, q.1 i p * q.2 j * D a p from by
                  funext q
                  simp_rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro p _
                  ring]
            rw [MeasureTheory.integral_finsetSum Finset.univ
              (f := fun (p : ι) (q : LayerParams ι κ) => q.1 i p * q.2 j * D a p)
              (fun p _ => by
                simpa using (hwb_int p).mul_const (D a p))]
      _ = 0 := by
            have hinner : ∀ p : ι, ∫ q : LayerParams ι κ, q.1 i p * q.2 j * D a p ∂μ = 0 := by
              intro p
              calc
                ∫ q : LayerParams ι κ, q.1 i p * q.2 j * D a p ∂μ
                    = (∫ q : LayerParams ι κ, q.1 i p * q.2 j ∂μ) * D a p := by
                      exact integral_mul_const (D a p) (fun q : LayerParams ι κ => q.1 i p * q.2 j)
                _ = 0 := by simp [hwb p]
            simp [hinner]
  have hT4 : ∫ q : LayerParams ι κ,
      (∑ p : ι, q.1 i p * D a p) * (∑ p' : ι, q.1 j p' * D b p') ∂μ =
        if i = j then (Cw : ℝ) * NeuralNetwork.normalizedGram D a b else 0 := by
    let sv : ℝ := (scaledWeightVariance (hyperparams Cw) ι : ℝ)
    have hsv : sv = (Cw : ℝ) / (Fintype.card ι : ℝ) := by
      dsimp [sv, scaledWeightVariance, hyperparams]
      push_cast
      rfl
    have hsvS : sv * (∑ p : ι, D a p * D b p) =
        (Cw : ℝ) * NeuralNetwork.normalizedGram D a b := by
      rw [hsv]
      unfold NeuralNetwork.normalizedGram
      ring
    calc
      ∫ q : LayerParams ι κ, (∑ p : ι, q.1 i p * D a p) * (∑ p' : ι, q.1 j p' * D b p') ∂μ
          = ∑ p : ι, ∑ p' : ι, (D a p * D b p') *
              ∫ q : LayerParams ι κ, q.1 i p * q.1 j p' ∂μ := by
            rw [show (fun q : LayerParams ι κ =>
                (∑ p : ι, q.1 i p * D a p) * (∑ p' : ι, q.1 j p' * D b p')) =
              fun q => ∑ p : ι, ∑ p' : ι, q.1 i p * q.1 j p' * (D a p * D b p') from by
                funext q
                simp_rw [Finset.sum_mul, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro p _
                apply Finset.sum_congr rfl
                intro p' _
                ring]
            rw [MeasureTheory.integral_finsetSum Finset.univ
              (f := fun (p : ι) (q : LayerParams ι κ) => ∑ p' : ι,
                q.1 i p * q.1 j p' * (D a p * D b p'))
              (fun p _ => by
                refine integrable_finsetSum Finset.univ (μ := μ)
                  (f := fun (p' : ι) (q : LayerParams ι κ) =>
                    q.1 i p * q.1 j p' * (D a p * D b p'))
                  (fun p' _ => ?_)
                simpa using (hww_int p p').mul_const (D a p * D b p'))]
            apply Finset.sum_congr rfl
            intro p _
            rw [MeasureTheory.integral_finsetSum Finset.univ
              (f := fun (p' : ι) (q : LayerParams ι κ) =>
                q.1 i p * q.1 j p' * (D a p * D b p'))
              (fun p' _ => by
                simpa using (hww_int p p').mul_const (D a p * D b p'))]
            apply Finset.sum_congr rfl
            intro p' _
            rw [integral_mul_const (D a p * D b p')
              (fun q : LayerParams ι κ => q.1 i p * q.1 j p')]
            ring
      _ = ∑ p : ι, ∑ p' : ι, (D a p * D b p') *
            (if i = j ∧ p = p' then sv else 0) := by
            apply Finset.sum_congr rfl
            intro p _
            apply Finset.sum_congr rfl
            intro p' _
            rw [hww p p']
      _ = if i = j then (Cw : ℝ) * NeuralNetwork.normalizedGram D a b else 0 := by
            by_cases hij : i = j
            · subst j
              rw [← hsvS]
              simp only [true_and, ite_true]
              have hdiag :
                  (∑ p : ι, ∑ p' : ι, (D a p * D b p') * (if p = p' then sv else 0)) =
                    sv * (∑ p : ι, D a p * D b p) := by
                calc
                  (∑ p : ι, ∑ p' : ι, (D a p * D b p') * (if p = p' then sv else 0))
                      = ∑ p : ι, (D a p * D b p) * sv := by
                        apply Finset.sum_congr rfl
                        intro p _
                        simp [mul_ite, Finset.sum_ite_eq]
                  _ = sv * (∑ p : ι, D a p * D b p) := by
                        rw [← Finset.sum_mul, mul_comm]
              exact hdiag
            · simp [hij]
  -- Assemble the four summands.
  have hT12_int : Integrable (fun q : LayerParams ι κ =>
      q.2 i * q.2 j + q.2 i * (∑ p' : ι, q.1 j p' * D b p')) μ :=
    hT1_int.add hT2_int
  have hT123_int : Integrable (fun q : LayerParams ι κ =>
      (q.2 i * q.2 j + q.2 i * (∑ p' : ι, q.1 j p' * D b p')) +
        (∑ p : ι, q.1 i p * D a p) * q.2 j) μ :=
    hT12_int.add hT3_int
  calc
    ∫ y, y a i * y b j ∂oneLayerBatchLaw (ι := ι) (κ := κ) Cw D
        = ∫ q : LayerParams ι κ,
            (DenseLayer.ofParams q).preactivation (D a) i *
              (DenseLayer.ofParams q).preactivation (D b) j ∂μ := hmap
    _ = ∫ q : LayerParams ι κ,
          (q.2 i * q.2 j + q.2 i * (∑ p' : ι, q.1 j p' * D b p') +
            (∑ p : ι, q.1 i p * D a p) * q.2 j +
              (∑ p : ι, q.1 i p * D a p) * (∑ p' : ι, q.1 j p' * D b p')) ∂μ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with q
          rw [hpa (D a) i q, hpa (D b) j q]
          ring
    _ = ∫ q : LayerParams ι κ, q.2 i * q.2 j ∂μ +
          ∫ q : LayerParams ι κ, q.2 i * (∑ p' : ι, q.1 j p' * D b p') ∂μ +
            ∫ q : LayerParams ι κ, (∑ p : ι, q.1 i p * D a p) * q.2 j ∂μ +
              ∫ q : LayerParams ι κ,
                (∑ p : ι, q.1 i p * D a p) * (∑ p' : ι, q.1 j p' * D b p') ∂μ := by
          rw [integral_add hT123_int hT4_int]
          rw [integral_add hT12_int hT3_int]
          rw [integral_add hT1_int hT2_int]
    _ = 0 + 0 + 0 + (if i = j then (Cw : ℝ) * NeuralNetwork.normalizedGram D a b else 0) := by
          rw [hT1, hT2, hT3, hT4]
    _ = if i = j then (Cw : ℝ) * NeuralNetwork.normalizedGram D a b else 0 := by
          ring

/-- Single-layer two-point function on an arbitrary indexed batch.

Informal proof: expand the preactivation
`y a i = ∑ p, W i p * D a p`.  The product initialization has centered independent Gaussian
weights with covariance
`E[W i p * W j q] = δᵢⱼ δₚq (Cw / Fintype.card ι)`.  Linearity of the integral over the two finite
sums gives exactly the Kronecker factor in output coordinates times `Cw * normalizedGram D a b`.
This is the two-point (`m = 1`) Wick/Isserlis computation; see
<https://en.wikipedia.org/wiki/Isserlis%27s_theorem>. -/
private lemma integral_mul_oneLayerBatchLaw {A : Type uA} {ι : Type uJ} {κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ] (Cw : ℝ≥0) (D : A → ι → ℝ)
    (a b : A) (i j : κ) :
    ∫ y, y a i * y b j ∂oneLayerBatchLaw (ι := ι) (κ := κ) Cw D =
      if i = j then (Cw : ℝ) * NeuralNetwork.normalizedGram D a b else 0 := by
  -- The hard work is isolated in `integral_mul_oneLayerBatchLaw_eq_sum_cov`; keeping this
  -- public-facing private lemma as a one-line wrapper makes the recursive proofs read cleanly.
  exact integral_mul_oneLayerBatchLaw_eq_sum_cov (ι := ι) (κ := κ) Cw D a b i j

/-- The output case of `integral_mul_batchOutputLaw` is the single-layer two-point function.

Informal proof: for `MLPShape.output`, `deepLinearBatchLaw` is precisely the pushforward of
`layerGaussianInit` by the batch preactivation map, i.e. `oneLayerBatchLaw`.  Then use
`integral_mul_oneLayerBatchLaw` and `MLPShape.depth .output = 1`. -/
private lemma integral_mul_batchOutputLaw_output {A : Type uA}
    {dIn dOut : ℕ} (Cw : ℝ≥0) (D : A → Fin dIn → ℝ) (a b : A) (i j : Fin dOut) :
    ∫ z, z a i * z b j ∂(MLPShape.output : MLPShape dIn dOut).deepLinearBatchLaw Cw D =
      if i = j then
        (Cw : ℝ) ^ (MLPShape.output : MLPShape dIn dOut).depth *
          NeuralNetwork.normalizedGram D a b
      else 0 := by
  calc
    ∫ z, z a i * z b j ∂(MLPShape.output : MLPShape dIn dOut).deepLinearBatchLaw Cw D
        = ∫ z, z a i * z b j ∂oneLayerBatchLaw (ι := Fin dIn) (κ := Fin dOut) Cw D := by
          rfl
    _ = if i = j then (Cw : ℝ) * NeuralNetwork.normalizedGram D a b else 0 :=
          integral_mul_oneLayerBatchLaw (ι := Fin dIn) (κ := Fin dOut) Cw D a b i j
    _ = if i = j then
          (Cw : ℝ) ^ (MLPShape.output : MLPShape dIn dOut).depth *
            NeuralNetwork.normalizedGram D a b
        else 0 := by
          by_cases hij : i = j
          · subst j
            simp [MLPShape.depth]
          · simp [hij]

/-- The `a`-th batch coordinate of the deep-linear batch law is the single-input output law at
`D a`. -/
private lemma deepLinearBatchLaw_map_coord {A : Type uA} {m n : ℕ} (S : MLPShape m n)
    (Cw : ℝ≥0) (D : A → Fin m → ℝ) (a : A) :
    (S.deepLinearBatchLaw Cw D).map (fun z : A → Fin n → ℝ => z a) =
      S.deepLinearOutputLaw Cw (D a) := by
  calc
    (S.deepLinearBatchLaw Cw D).map (fun z : A → Fin n → ℝ => z a)
        = ((S.gaussianInit (S.deepLinearHyperparams Cw)).map
            (fun θ b => S.eval (linear 1) θ (D b))).map (fun z : A → Fin n → ℝ => z a) := by
          rfl
    _ = (S.gaussianInit (S.deepLinearHyperparams Cw)).map
          (fun θ => S.eval (linear 1) θ (D a)) := by
          have hmm := Measure.map_map (μ := S.gaussianInit (S.deepLinearHyperparams Cw))
            (g := fun z : A → Fin n → ℝ => z a)
            (f := fun θ b => S.eval (linear 1) θ (D b))
            (by fun_prop : Measurable fun z : A → Fin n → ℝ => z a)
            ((S.paramModel (linear 1) (measurable_linear 1)).measurable_evalBatch D)
          have hcomp : (fun z : A → Fin n → ℝ => z a) ∘
              (fun θ b => S.eval (linear 1) θ (D b)) =
              (fun θ => S.eval (linear 1) θ (D a)) := by
            funext θ
            rfl
          rw [hcomp] at hmm
          exact hmm
    _ = S.deepLinearOutputLaw Cw (D a) := rfl

/-- Two batch coordinates of the deep-linear batch law have a finite mixed second moment.

Informal proof: the `a`-th marginal is the single-input output law (by
`deepLinearBatchLaw_map_coord`), under which monomials are integrable by
`jointMoment_outputLaw_even_and_integrable`; the product is bounded by the average of the two
coordinate squares. -/
private lemma integrable_coord_mul_deepBatchLaw {A : Type uA} {dIn dOut : ℕ}
    (S : MLPShape dIn dOut) (Cw : ℝ≥0) (D : A → Fin dIn → ℝ) (a b : A) (i j : Fin dOut)
    (hIn : 0 < dIn) (hWidths : ∀ n ∈ S.hiddenWidths, 0 < n) :
    Integrable (fun z : A → Fin dOut → ℝ => z a i * z b j) (S.deepLinearBatchLaw Cw D) := by
  let μ : Measure (A → Fin dOut → ℝ) := S.deepLinearBatchLaw Cw D
  have hIntSquare (a : A) (i : Fin dOut) :
      Integrable (fun z : A → Fin dOut → ℝ => z a i ^ 2) μ := by
    have hmarg : μ.map (fun z : A → Fin dOut → ℝ => z a) = S.deepLinearOutputLaw Cw (D a) := by
      dsimp [μ]
      exact deepLinearBatchLaw_map_coord S Cw D a
    have hz : AEMeasurable (fun z : A → Fin dOut → ℝ => z a) μ :=
      (measurable_pi_apply a).aemeasurable
    have hg : AEStronglyMeasurable (fun w : Fin dOut → ℝ => w i ^ 2)
        (μ.map (fun z : A → Fin dOut → ℝ => z a)) := by
      exact (by fun_prop : Measurable (fun w : Fin dOut → ℝ => w i ^ 2)).aestronglyMeasurable
    have hInt : Integrable (fun w : Fin dOut → ℝ => w i ^ 2) (S.deepLinearOutputLaw Cw (D a)) := by
      have hprod : (fun z : Fin dOut → ℝ =>
            ∏ r : Fin (2 * 1), z ((fun _ : Fin (2 * 1) => i) r)) =
          fun z : Fin dOut → ℝ => z i ^ 2 := by
        funext z
        change (∏ r : Fin 2, z i) = z i ^ 2
        simp [Finset.prod_const, pow_two]
      rw [← hprod]
      exact (jointMoment_outputLaw_even_and_integrable S Cw hIn hWidths).2 (D a) 1
        (fun _ : Fin (2 * 1) => i)
    have hg_mapped : Integrable (fun w : Fin dOut → ℝ => w i ^ 2)
        (μ.map (fun z : A → Fin dOut → ℝ => z a)) := by
      rw [hmarg]
      exact hInt
    exact (integrable_map_measure (g := fun w : Fin dOut → ℝ => w i ^ 2)
      (f := fun z : A → Fin dOut → ℝ => z a) hg hz).1 hg_mapped
  have hsum : Integrable (fun z : A → Fin dOut → ℝ => z a i ^ 2 + z b j ^ 2) μ :=
    (hIntSquare a i).add (hIntSquare b j)
  have hdom : Integrable (fun z : A → Fin dOut → ℝ => (z a i ^ 2 + z b j ^ 2) / 2) μ := by
    have h' : Integrable (fun z : A → Fin dOut → ℝ => (1 / 2 : ℝ) * (z a i ^ 2 + z b j ^ 2)) μ :=
      hsum.const_mul (1 / 2 : ℝ)
    convert h' using 1
    funext z
    ring
  refine Integrable.mono' hdom ?_ (Filter.Eventually.of_forall ?_)
  · exact (by fun_prop : Measurable (fun z : A → Fin dOut → ℝ =>
        z a i * z b j)).aestronglyMeasurable
  · intro z
    rw [Real.norm_eq_abs, abs_mul]
    have h₁ : |z a i| ^ 2 = z a i ^ 2 := sq_abs (z a i)
    have h₂ : |z b j| ^ 2 = z b j ^ 2 := sq_abs (z b j)
    nlinarith [sq_nonneg (|z a i| - |z b j|), h₁, h₂]

/-- Two batch coordinates of the one-layer batch law have a finite mixed second moment.

Informal proof: the `a`-th marginal is the one-layer output law, which is a product of centered
scalar Gaussians by `oneLayerOutputLaw_eq_pi_gaussianReal`; the product is bounded by the average
of the two coordinate squares. -/
private lemma integrable_coord_mul_oneLayerBatchLaw {A : Type uA} {dIn k : ℕ}
    (Cw : ℝ≥0) (D : A → Fin dIn → ℝ) (a b : A) (i j : Fin k) :
    Integrable (fun y : A → Fin k → ℝ => y a i * y b j)
      (oneLayerBatchLaw (ι := Fin dIn) (κ := Fin k) Cw D) := by
  let μ : Measure (A → Fin k → ℝ) := oneLayerBatchLaw (ι := Fin dIn) (κ := Fin k) Cw D
  have hIntSquare (a : A) (i : Fin k) : Integrable (fun y : A → Fin k → ℝ => y a i ^ 2) μ := by
    have hmarg : μ.map (fun y : A → Fin k → ℝ => y a) =
        oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw (D a) := by
      dsimp [μ, oneLayerBatchLaw]
      rw [Measure.map_map (measurable_pi_apply a)]
      · rfl
      · exact (Measurable.of_eval (fun a : A =>
            (DenseLayer.measurable_preactivation (ι := Fin dIn) (κ := Fin k)).comp
            (measurable_id.prodMk measurable_const)))
    have hz : AEMeasurable (fun y : A → Fin k → ℝ => y a) μ :=
      (measurable_pi_apply a).aemeasurable
    have hg : AEStronglyMeasurable (fun w : Fin k → ℝ => w i ^ 2)
        (μ.map (fun y : A → Fin k → ℝ => y a)) := by
      exact (by fun_prop : Measurable (fun w : Fin k → ℝ => w i ^ 2)).aestronglyMeasurable
    have hInt : Integrable (fun w : Fin k → ℝ => w i ^ 2)
        (oneLayerOutputLaw (ι := Fin dIn) (κ := Fin k) Cw (D a)) := by
      rw [oneLayerOutputLaw_eq_pi_gaussianReal Cw (D a)]
      let π : Measure (Fin k → ℝ) := Measure.pi (fun _ : Fin k =>
        gaussianReal 0 (Cw * NeuralNetwork.normalizedEnergyNNReal (D a)))
      have hmem : MemLp (fun w : Fin k → ℝ => w i) 2 π := by
        simpa [π] using (MemLp.comp_measurePreserving
          (memLp_id_gaussianReal' (2 : ℝ≥0∞) (by norm_num))
          (measurePreserving_eval
            (fun _ : Fin k => gaussianReal 0 (Cw * NeuralNetwork.normalizedEnergyNNReal (D a))) i))
      have hint_norm : Integrable (fun w : Fin k → ℝ => ‖w i‖ ^ 2) π :=
        hmem.integrable_norm_pow'
      convert hint_norm using 1
      funext w
      rw [Real.norm_eq_abs, sq_abs]
    have hg_mapped : Integrable (fun w : Fin k → ℝ => w i ^ 2)
        (μ.map (fun y : A → Fin k → ℝ => y a)) := by
      rw [hmarg]
      exact hInt
    exact (integrable_map_measure (g := fun w : Fin k → ℝ => w i ^ 2)
      (f := fun y : A → Fin k → ℝ => y a) hg hz).1 hg_mapped
  have hsum : Integrable (fun y : A → Fin k → ℝ => y a i ^ 2 + y b j ^ 2) μ :=
    (hIntSquare a i).add (hIntSquare b j)
  have hdom : Integrable (fun y : A → Fin k → ℝ => (y a i ^ 2 + y b j ^ 2) / 2) μ := by
    have h' : Integrable (fun y : A → Fin k → ℝ => (1 / 2 : ℝ) * (y a i ^ 2 + y b j ^ 2)) μ :=
      hsum.const_mul (1 / 2 : ℝ)
    convert h' using 1
    funext y
    ring
  refine Integrable.mono' hdom ?_ (Filter.Eventually.of_forall ?_)
  · exact (by fun_prop : Measurable (fun y : A → Fin k → ℝ => y a i * y b j)).aestronglyMeasurable
  · intro y
    rw [Real.norm_eq_abs, abs_mul]
    have h₁ : |y a i| ^ 2 = y a i ^ 2 := sq_abs (y a i)
    have h₂ : |y b j| ^ 2 = y b j ^ 2 := sq_abs (y b j)
    nlinarith [sq_nonneg (|y a i| - |y b j|), h₁, h₂]

/-- The deep-linear batch law varies measurably in the input batch. -/
private lemma measurable_deepLinearBatchLaw_kernel {A : Type uA} {k dOut : ℕ}
    (tail : MLPShape k dOut) (Cw : ℝ≥0) :
    Measurable fun y : A → Fin k → ℝ => tail.deepLinearBatchLaw Cw y := by
  let μ₀ : Measure tail.Params := tail.gaussianInit (tail.deepLinearHyperparams Cw)
  change Measurable fun y : A → Fin k → ℝ =>
    μ₀.map (fun θ : tail.Params => fun a : A => tail.eval (linear 1) θ (y a))
  let G : tail.Params × (A → Fin k → ℝ) → A → Fin dOut → ℝ :=
    fun p a => tail.eval (linear 1) p.1 (p.2 a)
  have hG_meas : Measurable G := by
    dsimp [G]
    refine Measurable.of_eval (fun a : A => ?_)
    exact (tail.measurable_eval (measurable_linear 1)).comp
      (measurable_fst.prodMk ((measurable_pi_apply a).comp measurable_snd))
  have hEq : (fun y : A → Fin k → ℝ =>
        μ₀.map (fun θ : tail.Params => fun a : A => tail.eval (linear 1) θ (y a))) =
      fun y : A → Fin k → ℝ => (μ₀.map (fun θ : tail.Params => (θ, y))).map G := by
    funext y
    rw [Measure.map_map hG_meas measurable_prodMk_right]
    rfl
  rw [hEq]
  exact (Measure.measurable_map G hG_meas).comp (Measurable.map_prodMk_right (μ := μ₀))

/-- Measure-level tower for the deep-linear batch law: conditioning on the first random layer
leaves the independent tail batch law. -/
private lemma deepLinearBatchLaw_hidden_eq_bind {A : Type uA} {dIn k dOut : ℕ}
    (tail : MLPShape k dOut) (Cw : ℝ≥0) (D : A → Fin dIn → ℝ) :
    (MLPShape.hidden tail : MLPShape dIn dOut).deepLinearBatchLaw Cw D =
      (oneLayerBatchLaw (ι := Fin dIn) (κ := Fin k) Cw D).bind
        (fun y => tail.deepLinearBatchLaw Cw y) := by
  classical
  let μ₁ : Measure (LayerParams (Fin dIn) (Fin k)) :=
    layerGaussianInit (hyperparams Cw) (Fin dIn) (Fin k)
  let ν : Measure tail.Params := tail.gaussianInit (tail.deepLinearHyperparams Cw)
  let f : LayerParams (Fin dIn) (Fin k) → A → Fin k → ℝ :=
    fun q a => (DenseLayer.ofParams q).preactivation (D a)
  let G : LayerParams (Fin dIn) (Fin k) × tail.Params → A → Fin dOut → ℝ :=
    fun p a => tail.eval (linear 1) p.2 (f p.1 a)
  have hf_meas : Measurable f := by
    dsimp [f]
    exact Measurable.of_eval (fun a : A =>
      (DenseLayer.measurable_preactivation.comp
        (measurable_id.prodMk measurable_const)))
  have hG_meas : Measurable G := by
    dsimp [G, f]
    refine Measurable.of_eval (fun a : A => ?_)
    exact (tail.measurable_eval (measurable_linear 1)).comp
      (measurable_snd.prodMk
        (DenseLayer.measurable_preactivation.comp
          (measurable_fst.prodMk measurable_const)))
  have htailLaw_meas : Measurable fun y : A → Fin k → ℝ => tail.deepLinearBatchLaw Cw y :=
    measurable_deepLinearBatchLaw_kernel tail Cw
  calc
    (MLPShape.hidden tail : MLPShape dIn dOut).deepLinearBatchLaw Cw D
        = (μ₁.prod ν).map G := by
          dsimp [MLPShape.deepLinearBatchLaw, ParamModel.outputLaw, ParamModel.evalBatch,
            MLPShape.paramModel, MLPShape.gaussianInit, MLPShape.deepLinearHyperparams,
            μ₁, ν, G, f]
          congr
          funext θ
          funext b
          change tail.hidden.eval (linear 1) θ (D b) =
            tail.eval (linear 1) θ.2 ((DenseLayer.ofParams θ.1).preactivation (D b))
          rw [MLPShape.eval_hidden]
          simp [activate_linear_eq_preactivation]
    _ = μ₁.bind (fun q => ν.map (fun θ' => G (q, θ'))) := by
          exact map_prod_eq_bind_map μ₁ ν hG_meas
    _ = μ₁.bind (fun q => tail.deepLinearBatchLaw Cw (f q)) := by
          congr
    _ = (μ₁.map f).bind (fun y : A → Fin k → ℝ => tail.deepLinearBatchLaw Cw y) :=
          (measure_bind_map_comp μ₁ hf_meas htailLaw_meas).symm
    _ = (oneLayerBatchLaw (ι := Fin dIn) (κ := Fin k) Cw D).bind
          (fun y => tail.deepLinearBatchLaw Cw y) := by
          rfl

/-- Tower property for a hidden deep-linear batch law, exposing the first random layer.

Informal proof: unfold `deepLinearBatchLaw` as a parameter-law pushforward.  The parameter law of
`.hidden tail` is the product of the first-layer Gaussian initialization and the independent tail
initialization.  Push this product through the evaluator, use
`MLPShape.eval_hidden` and `activate_linear_eq_preactivation`, and then apply the measure-level
identity `map_prod_eq_bind_map` / `measure_bind_map_comp`, exactly as in
`deepLinearOutputLaw_hidden_eq_bind`, but with `D : A → Fin dIn → ℝ` instead of a single input.
Finally apply `integral_bind_of_integrable` to the observable `z ↦ z a i * z b j`. -/
private lemma integral_mul_batchOutputLaw_hidden_tower {A : Type uA}
    {dIn k dOut : ℕ} (tail : MLPShape k dOut) (Cw : ℝ≥0)
    (D : A → Fin dIn → ℝ) (a b : A) (i j : Fin dOut)
    (hIn : 0 < dIn)
    (hWidths : ∀ n ∈ (MLPShape.hidden tail : MLPShape dIn dOut).hiddenWidths, 0 < n) :
    ∫ z, z a i * z b j
        ∂(MLPShape.hidden tail : MLPShape dIn dOut).deepLinearBatchLaw Cw D =
      ∫ y : A → Fin k → ℝ,
        (∫ z, z a i * z b j ∂tail.deepLinearBatchLaw Cw y)
          ∂oneLayerBatchLaw (ι := Fin dIn) (κ := Fin k) Cw D := by
  let μ : Measure (A → Fin k → ℝ) := oneLayerBatchLaw (ι := Fin dIn) (κ := Fin k) Cw D
  have hInt : Integrable (fun z : A → Fin dOut → ℝ => z a i * z b j)
      (μ.bind (fun y => tail.deepLinearBatchLaw Cw y)) := by
    rw [← deepLinearBatchLaw_hidden_eq_bind tail Cw D]
    exact integrable_coord_mul_deepBatchLaw (MLPShape.hidden tail) Cw D a b i j hIn hWidths
  have htower := integral_bind_of_integrable μ (fun y => tail.deepLinearBatchLaw Cw y)
    (measurable_deepLinearBatchLaw_kernel tail Cw) (F := fun z => z a i * z b j) hInt
  rw [deepLinearBatchLaw_hidden_eq_bind tail Cw D]
  simpa [μ] using htower

/-- The expected normalized Gram matrix after one random linear layer.

Informal proof: unfold `normalizedGram` and use linearity of the integral over the finite sum over
`p : Fin k`.  The previous single-layer two-point lemma with identical output coordinates gives
`E[y a p * y b p] = Cw * normalizedGram D a b` for each `p`; the positive-width hypothesis cancels
`(Fintype.card (Fin k) : ℝ)⁻¹ * Fintype.card (Fin k)`. -/
private lemma integral_normalizedGram_oneLayerBatchLaw {A : Type uA}
    {dIn k : ℕ} (Cw : ℝ≥0) (D : A → Fin dIn → ℝ) (a b : A) (hk : 0 < k) :
    ∫ y : A → Fin k → ℝ, NeuralNetwork.normalizedGram y a b
        ∂oneLayerBatchLaw (ι := Fin dIn) (κ := Fin k) Cw D =
      (Cw : ℝ) * NeuralNetwork.normalizedGram D a b := by
  calc
    ∫ y : A → Fin k → ℝ, NeuralNetwork.normalizedGram y a b
        ∂oneLayerBatchLaw (ι := Fin dIn) (κ := Fin k) Cw D
        = (Fintype.card (Fin k) : ℝ)⁻¹ * ∑ p : Fin k,
            ∫ y, y a p * y b p ∂oneLayerBatchLaw (ι := Fin dIn) (κ := Fin k) Cw D := by
          unfold NeuralNetwork.normalizedGram
          rw [MeasureTheory.integral_const_mul]
          congr 1
          rw [MeasureTheory.integral_finsetSum Finset.univ
            (f := fun (p : Fin k) (y : A → Fin k → ℝ) => y a p * y b p)
            (fun p _ => integrable_coord_mul_oneLayerBatchLaw Cw D a b p p)]
    _ = (Fintype.card (Fin k) : ℝ)⁻¹ * ∑ p : Fin k,
          (if p = p then (Cw : ℝ) * NeuralNetwork.normalizedGram D a b else 0) := by
          congr 1
          apply Finset.sum_congr rfl
          intro p _
          rw [integral_mul_oneLayerBatchLaw (ι := Fin dIn) (κ := Fin k) Cw D a b p p]
    _ = (Fintype.card (Fin k) : ℝ)⁻¹ * (Fintype.card (Fin k) : ℝ) *
          ((Cw : ℝ) * NeuralNetwork.normalizedGram D a b) := by
          have hsum :
              (∑ p : Fin k, (if p = p then (Cw : ℝ) * NeuralNetwork.normalizedGram D a b else 0)) =
                (Fintype.card (Fin k) : ℝ) * ((Cw : ℝ) * NeuralNetwork.normalizedGram D a b) := by
            calc
              (∑ p : Fin k, (if p = p then (Cw : ℝ) * NeuralNetwork.normalizedGram D a b else 0))
                  = ∑ p : Fin k, (Cw : ℝ) * NeuralNetwork.normalizedGram D a b := by
                    apply Finset.sum_congr rfl
                    intro p _
                    simp
              _ = (Fintype.card (Fin k) : ℝ) * ((Cw : ℝ) * NeuralNetwork.normalizedGram D a b) := by
                    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [hsum]
          ring
    _ = (Cw : ℝ) * NeuralNetwork.normalizedGram D a b := by
          have hkR : (Fintype.card (Fin k) : ℝ) ≠ 0 := by
            rw [Fintype.card_fin]
            exact_mod_cast (ne_of_gt hk)
          rw [← mul_assoc, inv_mul_cancel₀ hkR, one_mul]


/-- Uncentered second moment of two batch-output coordinates.

Informal proof: induct on `S`.  For `S = .output`, `map_batchPreactivation` identifies the law as a
product over output rows of centered multivariate Gaussians with covariance kernel
`Cw * normalizedGram D`, giving the displayed diagonal covariance.  For `S = .hidden tail`, use the
batch bind/tower decomposition: condition on the first-layer batch `y`, apply the induction
hypothesis to `tail` with input batch `y`, and average `normalizedGram y a b`.  The first-layer
calculation gives `E[y a p * y b p] = Cw * normalizedGram D a b`; summing over `p : Fin width` and
using the positive-width hypothesis cancels the `1 / width` in `normalizedGram`.
Sources: law of total covariance, <https://en.wikipedia.org/wiki/Law_of_total_covariance>, and
`docs/Renormalization.md`'s kernel recursion.
-/
lemma integral_mul_batchOutputLaw {A : Type uA}
    {dIn dOut : ℕ} (S : MLPShape dIn dOut) (Cw : ℝ≥0)
    (D : A → Fin dIn → ℝ) (a b : A) (i j : Fin dOut)
    (hIn : 0 < dIn) (hWidths : ∀ n ∈ S.hiddenWidths, 0 < n) :
    ∫ z, z a i * z b j ∂S.deepLinearBatchLaw Cw D =
      if i = j then (Cw : ℝ) ^ S.depth * NeuralNetwork.normalizedGram D a b else 0 := by
  induction S with
  | output =>
      exact integral_mul_batchOutputLaw_output Cw D a b i j
  | hidden tail ih =>
      rename_i dIn dOut k
      have hTower :
          ∫ z, z a i * z b j
              ∂(MLPShape.hidden tail : MLPShape dIn dOut).deepLinearBatchLaw Cw D =
            ∫ y : A → Fin k → ℝ,
              (∫ z, z a i * z b j ∂tail.deepLinearBatchLaw Cw y)
                ∂oneLayerBatchLaw (ι := Fin dIn) (κ := Fin k) Cw D :=
            integral_mul_batchOutputLaw_hidden_tower tail Cw D a b i j hIn hWidths
      have hk : 0 < k := by
        apply hWidths k
        rw [hidden_hiddenWidths_cons tail]
        simp
      have hTailWidths : ∀ n ∈ tail.hiddenWidths, 0 < n := by
        intro n hn
        apply hWidths n
        rw [hidden_hiddenWidths_cons tail]
        exact List.mem_cons_of_mem k hn
      calc
        ∫ z, z a i * z b j
            ∂(MLPShape.hidden tail : MLPShape dIn dOut).deepLinearBatchLaw Cw D
            = ∫ y : A → Fin k → ℝ,
                (∫ z, z a i * z b j ∂tail.deepLinearBatchLaw Cw y)
                  ∂oneLayerBatchLaw (ι := Fin dIn) (κ := Fin k) Cw D := hTower
        _ = ∫ y : A → Fin k → ℝ,
              (if i = j then
                (Cw : ℝ) ^ tail.depth * NeuralNetwork.normalizedGram y a b else 0)
                ∂oneLayerBatchLaw (ι := Fin dIn) (κ := Fin k) Cw D := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with y
              exact ih y i j hk hTailWidths
        _ = if i = j then (Cw : ℝ) ^ tail.depth * ∫ y : A → Fin k → ℝ,
              NeuralNetwork.normalizedGram y a b
                ∂oneLayerBatchLaw (ι := Fin dIn) (κ := Fin k) Cw D else 0 := by
              by_cases hij : i = j
              · subst j
                simp only [ite_true]
                rw [MeasureTheory.integral_const_mul]
              · simp [hij]
        _ = if i = j then (Cw : ℝ) ^ tail.depth * ((Cw : ℝ) * NeuralNetwork.normalizedGram D a b)
            else 0 := by
              by_cases hij : i = j
              · subst j
                simp only [ite_true]
                congr 1
                rw [integral_normalizedGram_oneLayerBatchLaw Cw D a b hk]
              · simp [hij]
        _ = if i = j then (Cw : ℝ) ^ (tail.depth + 1) * NeuralNetwork.normalizedGram D a b
            else 0 := by
              by_cases hij : i = j
              · subst j
                simp only [ite_true]
                rw [pow_succ]
                ring
              · simp [hij]
        _ = if i = j then (Cw : ℝ) ^ (MLPShape.hidden tail : MLPShape dIn dOut).depth *
              NeuralNetwork.normalizedGram D a b else 0 := by
              by_cases hij : i = j
              · subst j
                simp [MLPShape.depth]
              · simp [hij]

/-- Covariance of two batch-output coordinates.  The theorem explicitly uses Mathlib's
`covariance`, not merely an uncentered second moment.

Informal proof: all outputs are centered by final-layer sign symmetry, so covariance equals the
uncentered second moment.  The exact second moment is the finite-depth kernel recursion
`G^(L) = Cw^L G^(0)`, with a Kronecker delta in the output row indices.
-/
theorem covariance_batchOutputLaw {A : Type uA}
    {dIn dOut : ℕ} (S : MLPShape dIn dOut) (Cw : ℝ≥0)
    (D : A → Fin dIn → ℝ) (a b : A) (i j : Fin dOut)
    (hIn : 0 < dIn) (hWidths : ∀ n ∈ S.hiddenWidths, 0 < n) :
    covariance (fun z => z a i) (fun z => z b j) (S.deepLinearBatchLaw Cw D) =
      if i = j then (Cw : ℝ) ^ S.depth * NeuralNetwork.normalizedGram D a b else 0 := by
  calc
    covariance (fun z => z a i) (fun z => z b j) (S.deepLinearBatchLaw Cw D)
        = ∫ z, z a i * z b j ∂S.deepLinearBatchLaw Cw D :=
          covariance_batchOutputLaw_eq_integral_mul S Cw D a b i j hIn hWidths
    _ = if i = j then (Cw : ℝ) ^ S.depth * NeuralNetwork.normalizedGram D a b else 0 :=
          integral_mul_batchOutputLaw S Cw D a b i j hIn hWidths

/-- Uncentered form of the exact finite-dataset covariance solution.

Informal proof: this is the second-moment lemma `integral_mul_batchOutputLaw`, proved by the same
one-layer Gaussian covariance plus tower-property induction as the covariance theorem above.
-/
theorem covariance_batchOutputLaw_closedForm {A : Type uA}
    {dIn dOut : ℕ} (S : MLPShape dIn dOut) (Cw : ℝ≥0)
    (D : A → Fin dIn → ℝ) (a b : A) (i j : Fin dOut)
    (hIn : 0 < dIn) (hWidths : ∀ n ∈ S.hiddenWidths, 0 < n) :
    ∫ z, z a i * z b j ∂S.deepLinearBatchLaw Cw D =
      if i = j then (Cw : ℝ) ^ S.depth * NeuralNetwork.normalizedGram D a b else 0 :=
  integral_mul_batchOutputLaw S Cw D a b i j hIn hWidths

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

end NeuralNetwork.DeepLinear

end

end
