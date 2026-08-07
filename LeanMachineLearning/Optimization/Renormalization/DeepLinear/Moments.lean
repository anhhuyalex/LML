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
open scoped BigOperators NNReal Topology

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
  classical
  have hIndep : iIndepFun (fun i : ι => fun f : ι → α => -f i) (Measure.pi μ) := by
    simpa using
      (iIndepFun_pi (μ := μ) (X := fun _ : ι => fun x : α => -x)
        (mX := fun i => (by fun_prop : Measurable fun x : α => -x).aemeasurable))
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
                = ((Measure.pi μ).map (fun f : ι → α => f i)).map (fun x : α => -x) := by
                  rw [show (fun f : ι → α => -f i) =
                      (fun x : α => -x) ∘ (fun f : ι → α => f i) from rfl]
                  rw [Measure.map_map (by fun_prop : Measurable fun x : α => -x)
                    (measurable_pi_apply i)]
            _ = (μ i).map (fun x : α => -x) := by
                  rw [(measurePreserving_eval μ i).map_eq]
    _ = Measure.pi μ := by
          congr 1
          funext i
          exact hμ i

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
      dsimp [negLastLayer]
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
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
      rw [hsum]
      simp [DenseLayer.preactivation_apply]
      ring
  | hidden tail ih =>
      rename_i m₀ n₀ k
      simp only [MLPShape.eval_hidden, negLastLayer]
      calc
        MLPShape.eval tail (linear 1) (negLastLayer tail θ.2)
            ((DenseLayer.ofParams θ.1).activate (linear 1) x)
            = MLPShape.eval tail (linear 1) (negLastLayer tail θ.2)
                ((DenseLayer.ofParams θ.1).preactivation x) := by
              exact congrArg (MLPShape.eval tail (linear 1) (negLastLayer tail θ.2)) (by
                funext y
                simp [DenseLayer.activate, linear, one_mul])
        _ = -MLPShape.eval tail (linear 1) θ.2
              ((DenseLayer.ofParams θ.1).preactivation x) := by
              exact ih θ.2 ((DenseLayer.ofParams θ.1).preactivation x)
        _ = -MLPShape.eval tail (linear 1) θ.2
              ((DenseLayer.ofParams θ.1).activate (linear 1) x) := by
              exact congrArg Neg.neg (congrArg (MLPShape.eval tail (linear 1) θ.2) (by
                funext y
                simp [DenseLayer.activate, linear, one_mul]))

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
            gaussianReal 0 (scaledWeightVariance p (Fin m₀)) := by
        intro i
        simpa using
          (ProbabilityTheory.gaussianReal_map_neg (μ := (0 : ℝ))
            (v := scaledWeightVariance p (Fin m₀)))
      have hgB : ∀ j : Fin n₀,
          (gaussianReal 0 p.biasVariance).map (fun x : ℝ => -x) =
            gaussianReal 0 p.biasVariance := by
        intro j
        simpa using
          (ProbabilityTheory.gaussianReal_map_neg (μ := (0 : ℝ)) (v := p.biasVariance))
      have hW : (gaussianWeightLaw p (Fin m₀) (Fin n₀)).map
          (fun W : Fin n₀ → Fin m₀ → ℝ => -W) = gaussianWeightLaw p (Fin m₀) (Fin n₀) := by
        unfold gaussianWeightLaw
        exact pi_map_neg_invariant
          (μ := fun _ : Fin n₀ => Measure.pi fun _ : Fin m₀ =>
            gaussianReal 0 (scaledWeightVariance p (Fin m₀)))
          (fun _ => pi_map_neg_invariant
            (μ := fun _ : Fin m₀ => gaussianReal 0 (scaledWeightVariance p (Fin m₀))) hgW)
      have hB : (gaussianBiasLaw p (Fin n₀)).map (fun b : Fin n₀ → ℝ => -b) =
          gaussianBiasLaw p (Fin n₀) := by
        unfold gaussianBiasLaw
        exact pi_map_neg_invariant (μ := fun _ : Fin n₀ => gaussianReal 0 p.biasVariance) hgB
      have : SFinite (gaussianWeightLaw p (Fin m₀) (Fin n₀)) := by
        unfold gaussianWeightLaw
        infer_instance
      have : SFinite (gaussianBiasLaw p (Fin n₀)) := by
        unfold gaussianBiasLaw
        infer_instance
      have hmap : Measure.map (negLastLayer (MLPShape.output : MLPShape m₀ n₀))
          (layerGaussianInit p (Fin m₀) (Fin n₀)) = layerGaussianInit p (Fin m₀) (Fin n₀) := by
        dsimp [negLastLayer]
        rw [layerGaussianInit]
        calc
          Measure.map (fun q : LayerParams (Fin m₀) (Fin n₀) =>
              (fun j i => -q.1 j i, fun j => -q.2 j))
              ((gaussianWeightLaw p (Fin m₀) (Fin n₀)).prod (gaussianBiasLaw p (Fin n₀)))
              = ((gaussianWeightLaw p (Fin m₀) (Fin n₀)).map
                    (fun W : Fin n₀ → Fin m₀ → ℝ => -W)).prod
                  ((gaussianBiasLaw p (Fin n₀)).map (fun b : Fin n₀ → ℝ => -b)) := by
                exact (Measure.map_prod_map
                  (μa := gaussianWeightLaw p (Fin m₀) (Fin n₀))
                  (μc := gaussianBiasLaw p (Fin n₀))
                  (hf := measurable_neg) (hg := measurable_neg)).symm
          _ = (gaussianWeightLaw p (Fin m₀) (Fin n₀)).prod (gaussianBiasLaw p (Fin n₀)) := by
                rw [hW, hB]
      simpa [p, MLPShape.gaussianInit, MLPShape.deepLinearHyperparams] using hmap
  | hidden tail ih =>
      rename_i m₀ n₀ k
      let μ₁ : Measure (LayerParams (Fin m₀) (Fin k)) :=
        layerGaussianInit (DeepLinear.hyperparams Cw) (Fin m₀) (Fin k)
      let ν : Measure tail.Params := tail.gaussianInit (tail.deepLinearHyperparams Cw)
      have : IsProbabilityMeasure μ₁ := by
        dsimp [μ₁]
        exact isProbabilityMeasure_layerGaussianInit (DeepLinear.hyperparams Cw) (Fin m₀) (Fin k)
      have : IsProbabilityMeasure ν := by
        dsimp [ν]
        exact tail.isProbabilityMeasure_gaussianInit (tail.deepLinearHyperparams Cw)
      have : SFinite μ₁ := inferInstance
      have : SFinite ν := inferInstance
      have hmap : Measure.map (negLastLayer (MLPShape.hidden tail : MLPShape m₀ n₀))
          (μ₁.prod ν) = μ₁.prod ν := by
        dsimp [negLastLayer]
        calc
          Measure.map (fun q : LayerParams (Fin m₀) (Fin k) × tail.Params =>
              (q.1, negLastLayer tail q.2)) (μ₁.prod ν)
              = (μ₁.map id).prod (ν.map (negLastLayer tail)) := by
                exact (Measure.map_prod_map (μa := μ₁) (μc := ν)
                  (hf := measurable_id) (hg := measurable_negLastLayer tail)).symm
          _ = μ₁.prod ν := by
                dsimp [ν]
                rw [ih]
                simp
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
  rw [Measure.neg_def]
  let μ₀ : Measure S.Params := S.gaussianInit (S.deepLinearHyperparams Cw)
  let F : S.Params → Fin dOut → ℝ := fun θ => S.eval (linear 1) θ x
  have hF_meas : Measurable F := by
    dsimp [F]
    exact (S.measurable_eval (measurable_linear 1)).comp (measurable_id.prodMk measurable_const)
  have hJ_meas : Measurable (negLastLayer S) := measurable_negLastLayer S
  have hJ_inv : Measure.map (negLastLayer S) μ₀ = μ₀ := by
    dsimp [μ₀]
    exact gaussianInit_negLastLayer S Cw
  have hG : (fun θ : S.Params => -(S.eval (linear 1) θ x)) =
      (fun θ : S.Params => F (negLastLayer S θ)) := by
    funext θ
    dsimp [F]
    rw [eval_negLastLayer S θ x]
  calc
    (S.deepLinearOutputLaw Cw x).map (fun z : Fin dOut → ℝ => -z)
        = (μ₀.map F).map (fun z : Fin dOut → ℝ => -z) := by
          unfold MLPShape.deepLinearOutputLaw
          dsimp [μ₀, F]
    _ = μ₀.map (fun θ : S.Params => -F θ) := by
          rw [Measure.map_map (by fun_prop : Measurable fun z : Fin dOut → ℝ => -z) hF_meas]
          rfl
    _ = μ₀.map (fun θ : S.Params => F (negLastLayer S θ)) := by
          apply congrArg (fun G : S.Params → Fin dOut → ℝ => μ₀.map G)
          funext θ
          dsimp [F]
          rw [eval_negLastLayer S θ x]
    _ = (μ₀.map (negLastLayer S)).map F := by
          change μ₀.map (F ∘ negLastLayer S) = (μ₀.map (negLastLayer S)).map F
          exact (Measure.map_map hF_meas hJ_meas).symm
    _ = μ₀.map F := by
          rw [hJ_inv]
    _ = S.deepLinearOutputLaw Cw x := by
          unfold MLPShape.deepLinearOutputLaw
          dsimp [μ₀, F]
  ⟩

-- The monomial `z ↦ ∏ r, z (a r)` in coordinate projections is measurable: each coordinate
-- projection is measurable and finite products of measurable functions are measurable.
private lemma measurable_monomial {κ : Type*} {n : ℕ} (a : Fin n → κ) :
    Measurable (fun z : κ → ℝ => ∏ r : Fin n, z (a r)) := by
  exact Finset.measurable_prod Finset.univ (fun r _ => measurable_pi_apply (a r))

-- A monomial of odd degree is an odd function of its arguments: negating the vector `z` negates
-- the whole product.  `Finset.prod_neg` factors out `(-1) ^ n`, and `Odd.neg_one_pow` collapses
-- that factor to `-1` because `n` is odd.
private lemma odd_monomial_neg {κ : Type*} {n : ℕ} (hn : Odd n) (a : Fin n → κ) (z : κ → ℝ) :
    (∏ r : Fin n, (-z) (a r)) = -∏ r : Fin n, z (a r) := by
  calc
    (∏ r : Fin n, (-z) (a r)) = ∏ r : Fin n, -(z (a r)) := by
      simp
    _ = (-1 : ℝ) ^ Fintype.card (Fin n) * ∏ r : Fin n, z (a r) := by
      simpa using
        (Finset.prod_neg (s := Finset.univ) (f := fun r : Fin n => z (a r)))
    _ = -∏ r : Fin n, z (a r) := by
      simp [Fintype.card_fin, hn.neg_one_pow]

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
  classical
  -- The output law is invariant under the global sign flip `z ↦ -z`.
  have hneg : Measure.IsNegInvariant (S.deepLinearOutputLaw Cw x) :=
    deepLinearOutputLaw_isNegInvariant S Cw x
  -- `F` is the odd monomial `z ↦ ∏ r, z (a r)`: it is measurable, and it is odd because there
  -- are `2m + 1` (an odd number of) factors, so its integral against the sign-invariant law
  -- vanishes by `integral_eq_zero_of_odd_of_aestronglyMeasurable`.
  let F : (Fin dOut → ℝ) → ℝ := fun z => ∏ r, z (a r)
  have hF : AEStronglyMeasurable F (S.deepLinearOutputLaw Cw x) := by
    apply Measurable.aestronglyMeasurable
    dsimp [F]
    exact measurable_monomial a
  have hodd : ∀ z : Fin dOut → ℝ, F (-z) = -F z := by
    intro z
    dsimp [F]
    exact odd_monomial_neg (hn := odd_two_mul_add_one m) (a := a) (z := z)
  simpa [F] using
    @Renormalization.integral_eq_zero_of_odd_of_aestronglyMeasurable
      (Fin dOut → ℝ) _ _ _ (S.deepLinearOutputLaw Cw x) hneg F hF hodd

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
  sorry

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
  sorry

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
