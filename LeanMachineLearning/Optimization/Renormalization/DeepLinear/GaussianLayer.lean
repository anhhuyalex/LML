/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.StdGaussianRadial
public import LeanMachineLearning.Optimization.Renormalization.DeepLinear.Basic
public import LeanMachineLearning.Optimization.Renormalization.Gaussian

/-!
# One Gaussian layer of a deep linear network

The public API in this file isolates the radial calculation used by every finite-width moment
formula.  In particular, downstream files need not re-expand Gaussian coordinates or pairings.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace NeuralNetwork.DeepLinear

universe uA uI uJ

/-- The coefficient `(2m)! / (2^m m!)` in the `2m`-th centered Gaussian moment. -/
def gaussianEvenCoeff (m : ℕ) : ℝ :=
  ((2 * m).factorial : ℝ) / ((2 : ℝ) ^ m * (m.factorial : ℝ))

/-- The exact finite-width correction for the `m`-th moment of normalized Gaussian energy. -/
def widthMomentFactor (m n : ℕ) : ℝ :=
  ∏ s ∈ Finset.range m, (1 + (2 * s : ℝ) / (n : ℝ))

@[simp] theorem widthMomentFactor_zero (n : ℕ) : widthMomentFactor 0 n = 1 := by
  simp [widthMomentFactor]

@[simp] theorem widthMomentFactor_one (n : ℕ) : widthMomentFactor 1 n = 1 := by
  simp [widthMomentFactor]

theorem widthMomentFactor_two (n : ℕ) :
    widthMomentFactor 2 n = 1 + 2 / (n : ℝ) := by
  norm_num [widthMomentFactor, Finset.prod_range_succ]

theorem widthMomentFactor_three (n : ℕ) :
    widthMomentFactor 3 n = (1 + 2 / (n : ℝ)) * (1 + 4 / (n : ℝ)) := by
  norm_num [widthMomentFactor, Finset.prod_range_succ]

/-- The natural-power form of the finite power-mean bound.  This packages the recurring
conversion from Mathlib's real-exponent inequality to the integer exponents used for Gaussian
moment bounds. -/
theorem sum_pow_le_card_pow_mul_sum_pow_nat {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (m : ℕ) (hm : 1 ≤ m) (hf : ∀ i, 0 ≤ f i) :
    (∑ i, f i) ^ m ≤ (Fintype.card ι : ℝ) ^ (m - 1) * ∑ i, f i ^ m := by
  have hpm := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
    (s := (Finset.univ : Finset ι)) (f := f) (p := (m : ℝ))
    (hp := by exact_mod_cast hm) (hf := fun i _ => hf i)
  calc
    (∑ i, f i) ^ m = (∑ i, f i) ^ (m : ℝ) := by rw [Real.rpow_natCast]
    _ ≤ (Fintype.card ι : ℝ) ^ ((m : ℝ) - 1) * ∑ i, f i ^ (m : ℝ) := by
      simpa [Finset.card_univ] using hpm
    _ = (Fintype.card ι : ℝ) ^ (m - 1) * ∑ i, f i ^ m := by
      have hsub : (m : ℝ) - 1 = ((m - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hm]
        norm_num
      rw [hsub, Real.rpow_natCast]
      simp_rw [Real.rpow_natCast]

/-- Output law of one freshly initialized bias-free linear layer. -/
def oneLayerOutputLaw {ι : Type uI} {κ : Type uJ} [Fintype ι] [Fintype κ]
    (Cw : ℝ≥0) (x : ι → ℝ) : Measure (κ → ℝ) :=
  Measure.map (fun q : LayerParams ι κ => (DenseLayer.ofParams q).preactivation x)
    (layerGaussianInit (hyperparams Cw) ι κ)

/-- A bias-free initialized layer is a product of centered multivariate Gaussians across output
neurons.

Informal proof: specialize `map_evalBatch_layerGaussianInit`; the bias term vanishes and
`layerCovariance_eq_bias_add_weight_mul_normalizedGram` identifies its covariance with
`Cw • normalizedGram x`.  Independence of rows is already built into that theorem.  Source:
`docs/Renormalization.md`, equation `eq:two-point-function-deep-linear-layer-ell`, and Mathlib's
multivariate Gaussian API at
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Gaussian/Multivariate.html>.
-/
theorem map_batchPreactivation
    {A : Type uA} {ι : Type uI} {κ : Type uJ}
    [Fintype ι] [Fintype κ] [Fintype A] [DecidableEq A]
    (Cw : ℝ≥0) (x : A → ι → ℝ) :
    Measure.map
        (fun q : LayerParams ι κ => fun j => batchToEuclidean (batchPreactivation q x) j)
        (layerGaussianInit (hyperparams Cw) ι κ) =
      Measure.pi (fun _ : κ =>
        multivariateGaussian 0 (fun a b => (Cw : ℝ) * NeuralNetwork.normalizedGram x a b)) := by
  simpa only [NeuralNetwork.layerCovariance_eq_bias_add_weight_mul_normalizedGram,
    hyperparams_biasVariance, hyperparams_weightVariance, NNReal.coe_zero, zero_add] using
    map_evalBatch_layerGaussianInit (p := hyperparams Cw) x

/-- Unnormalized chi-square moments for the squared norm of a standard Gaussian vector:
`E (∑ᵢ gᵢ²)^m = ∏_{s<m} (n + 2 s)`, the moments of a `χ²_n` variable.

This is `ProbabilityTheory.integral_sumSq_pow_pi_gaussianReal` (radial moments of the standard
Gaussian, `ForMathlib/Probability/StdGaussianRadial.lean`); the case `n = 0` is the point mass at
`0`, where both sides are `0 ^ m` and `∏_{s<m} 2 s`. -/
theorem integral_sumSq_pow_stdGaussian (m n : ℕ) :
    ∫ g : Fin n → ℝ, ((∑ i, g i ^ 2) ^ m) ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      ∏ s ∈ Finset.range m, ((n : ℝ) + 2 * s) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [Finset.prod_eq_zero (Finset.mem_range.mpr hm) (by simp)]
      simp [zero_pow hm.ne']
  · have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    simpa using integral_sumSq_pow_pi_gaussianReal (ι := Fin n) m

private lemma normalized_chiSquare_product_algebra (m n : ℕ) (hn : 0 < n) :
    ((n : ℝ)⁻¹) ^ m * (∏ s ∈ Finset.range m, ((n : ℝ) + 2 * s)) =
      widthMomentFactor m n := by
  classical
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold widthMomentFactor
  calc
    ((n : ℝ)⁻¹) ^ m * (∏ s ∈ Finset.range m, ((n : ℝ) + 2 * s))
        = (∏ _s ∈ Finset.range m, (n : ℝ)⁻¹) *
            (∏ s ∈ Finset.range m, ((n : ℝ) + 2 * s)) := by
          simp [Finset.prod_const]
    _ = ∏ s ∈ Finset.range m, ((n : ℝ)⁻¹ * ((n : ℝ) + 2 * s)) := by
          rw [Finset.prod_mul_distrib]
    _ = ∏ s ∈ Finset.range m, (1 + (2 * s : ℝ) / (n : ℝ)) := by
          refine Finset.prod_congr rfl ?_
          intro s hs
          field_simp [hn_ne]

/-- Moment formula for the empirical mean of squares of an independent standard Gaussian vector.

This is the radial analytic core used by `integral_normalizedEnergy_pow_stdGaussian`.  In informal
terms, if `X g = ∑ i, g i ^ 2`, then the Gaussian integration-by-parts recurrence gives
`E[X^(m+1)] = ((n : ℝ) + 2 * m) * E[X^m]`; with `E[X^0] = 1`, this yields
`E[X^m] = ∏ s<m ((n : ℝ) + 2*s)`.  Multiplying by `(n : ℝ)⁻¹` inside the `m`-th power gives the
stated product `∏ s<m (1 + 2*s/n)`.  This is also the standard chi-square moment formula; see
<https://en.wikipedia.org/wiki/Chi-squared_distribution#Moments>.  A full Lean proof should derive
the recurrence using the local one-dimensional Stein identity
`Renormalization.integral_mul_pow_gaussianReal` and finite-product Fubini.
-/
theorem integral_normalizedSumSq_pow_stdGaussian (m n : ℕ) (hn : 0 < n) :
    ∫ g : Fin n → ℝ, (((n : ℝ)⁻¹ * ∑ i, g i ^ 2) ^ m)
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      widthMomentFactor m n := by
  calc
    ∫ g : Fin n → ℝ, (((n : ℝ)⁻¹ * ∑ i, g i ^ 2) ^ m)
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1)
        = ((n : ℝ)⁻¹) ^ m *
            ∫ g : Fin n → ℝ, ((∑ i, g i ^ 2) ^ m)
              ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
          simp_rw [mul_pow]
          rw [MeasureTheory.integral_const_mul]
    _ = ((n : ℝ)⁻¹) ^ m * (∏ s ∈ Finset.range m, ((n : ℝ) + 2 * s)) := by
          rw [integral_sumSq_pow_stdGaussian]
    _ = widthMomentFactor m n := normalized_chiSquare_product_algebra m n hn

/-- Exact moments of normalized energy under an independent standard Gaussian vector.

Informal proof: `n * normalizedEnergy g` has the chi-square distribution with `n` degrees of
freedom.  Its `m`-th moment is `∏ s<m (n+2s)`; division by `n^m` gives the stated product.  A Lean
proof can instead induct using Gaussian integration by parts and
`Renormalization.integral_pow_gaussianReal_even`.  Source:
<https://en.wikipedia.org/wiki/Chi-squared_distribution#Moments>.
-/
theorem integral_normalizedEnergy_pow_stdGaussian (m n : ℕ) (hn : 0 < n) :
    ∫ g, NeuralNetwork.normalizedEnergy g ^ m ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) =
      widthMomentFactor m n := by
  simpa [NeuralNetwork.normalizedEnergy, Fintype.card_fin] using
    integral_normalizedSumSq_pow_stdGaussian m n hn

/-- `normalizedEnergy` is homogeneous of degree two under coordinatewise scaling and relabelling:
`E[(c · g) ∘ e] = c² · E[g]`. -/
private lemma normalizedEnergy_comp_smul_equiv (c : ℝ) {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (g : ι → ℝ) :
    NeuralNetwork.normalizedEnergy (fun j : κ => c * g (e j)) =
      c ^ 2 * NeuralNetwork.normalizedEnergy g := by
  classical
  unfold NeuralNetwork.normalizedEnergy
  have hcard : (Fintype.card κ : ℝ) = (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_congr e
  have hsum : (∑ j : κ, (c * g (e j)) ^ 2) = c ^ 2 * ∑ i : ι, (g i) ^ 2 := by
    calc
      (∑ j : κ, (c * g (e j)) ^ 2) = ∑ j : κ, c ^ 2 * (g (e j)) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro j _
        ring
      _ = c ^ 2 * ∑ j : κ, (g (e j)) ^ 2 := by
        rw [Finset.mul_sum]
      _ = c ^ 2 * ∑ i : ι, (g i) ^ 2 := by
        rw [show (∑ j : κ, (g (e j)) ^ 2) = ∑ i : ι, (g i) ^ 2 by
          refine Finset.sum_bij (s := Finset.univ) (t := Finset.univ)
            (i := fun a _ => e a) (f := fun a => (g (e a)) ^ 2)
            (g := fun b => (g b) ^ 2) ?_ ?_ ?_ ?_
          · intro a _; simp
          · intro a _ b _ hab; exact e.injective hab
          · intro b _; exact ⟨e.symm b, by simp, e.apply_symm_apply b⟩
          · intro a _; rfl]
  rw [hsum, hcard]
  ring

/-- The law of one bias-free layer's output is a scaled, relabelled standard Gaussian vector.

This is the probabilistic assembly step of
`integral_normalizedEnergy_pow_oneLayerOutputLaw_eq_scaled_stdGaussian`.  Specialize
`map_batchPreactivation` to a singleton batch: the joint law of the Euclidean-embedded outputs is
a product over `κ` of centered multivariate Gaussians on `EuclideanSpace ℝ PUnit` whose single
entry is `(Cw : ℝ) * normalizedEnergy x`.  Projecting every coordinate back with
`ProbabilityTheory.measurePreserving_eval_multivariateGaussian`, identifying the scaled Gaussian
with the image of `gaussianReal 0 1` under multiplication by the square root of that variance
(`ProbabilityTheory.gaussianReal_map_const_mul`), and relabelling `κ` to `Fin (Fintype.card κ)`
(`MeasureTheory.measurePreserving_piCongrLeft`) yields the displayed pushforward of the
standard product Gaussian on `Fin (Fintype.card κ) → ℝ`. -/
private lemma oneLayerOutputLaw_eq_map_stdGaussian
    {ι : Type uI} {κ : Type uJ} [Fintype ι] [Fintype κ]
    (Cw : ℝ≥0) (x : ι → ℝ) :
    oneLayerOutputLaw (ι := ι) (κ := κ) Cw x =
      Measure.map
        (fun g : Fin (Fintype.card κ) → ℝ => fun j : κ =>
          Real.sqrt ((Cw : ℝ) * NeuralNetwork.normalizedEnergy x) * g (Fintype.equivFin κ j))
        ((Measure.pi fun _ : Fin (Fintype.card κ) => gaussianReal 0 1)) := by
  classical
  let s : ℝ := (Cw : ℝ) * NeuralNetwork.normalizedEnergy x
  have hs : 0 ≤ s := by
    dsimp [s]
    exact mul_nonneg Cw.property (NeuralNetwork.normalizedEnergy_nonneg x)
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let evalV : EuclideanSpace ℝ PUnit.{1} → ℝ := fun x => x PUnit.unit
  let ν : Measure (EuclideanSpace ℝ PUnit.{1}) :=
    multivariateGaussian 0 (fun _ _ : PUnit.{1} => s)
  have hEval_meas : Measurable evalV := by
    dsimp [evalV]
    fun_prop
  have hT_meas : Measurable (fun y : ℝ =>
      (EuclideanSpace.equiv PUnit ℝ).symm (fun _ : PUnit => y)) := by
    -- `EuclideanSpace.equiv PUnit ℝ` is a linear equivalence, hence continuous and measurable.
    have hcont : Continuous (fun y : ℝ =>
        (EuclideanSpace.equiv PUnit ℝ).symm (fun _ : PUnit => y)) := by
      exact (EuclideanSpace.equiv PUnit ℝ).symm.continuous.comp
        (continuous_pi fun _ : PUnit => continuous_id)
    exact hcont.measurable
  have hT_inv (y : ℝ) :
      ((EuclideanSpace.equiv PUnit ℝ).symm (fun _ : PUnit => y)) PUnit.unit = y := by
    simp [EuclideanSpace.equiv, WithLp.ofLp_toLp]
  -- Step 1: the singleton-batch Euclidean law.
  have hmat :
      (fun a b : PUnit.{1} =>
        (Cw : ℝ) * NeuralNetwork.normalizedGram (fun _ : PUnit.{1} => x) a b) =
        fun _ _ : PUnit.{1} => s := by
    funext a b
    cases a
    cases b
    simp [s, normalizedGram_singleton]
  have hA :
      Measure.map (fun q : LayerParams ι κ =>
          fun j : κ => (EuclideanSpace.equiv PUnit ℝ).symm
            (fun _ : PUnit => (DenseLayer.ofParams q).preactivation x j))
        (layerGaussianInit (hyperparams Cw) ι κ) =
      Measure.pi (fun _ : κ => ν) := by
    calc
      Measure.map (fun q : LayerParams ι κ =>
          fun j : κ => (EuclideanSpace.equiv PUnit ℝ).symm
            (fun _ : PUnit => (DenseLayer.ofParams q).preactivation x j))
          (layerGaussianInit (hyperparams Cw) ι κ)
          = Measure.pi (fun _ : κ =>
              multivariateGaussian 0 (fun a b : PUnit =>
                (Cw : ℝ) * NeuralNetwork.normalizedGram (fun _ : PUnit => x) a b)) := by
            simpa [batchToEuclidean, batchPreactivation] using
              map_batchPreactivation (A := PUnit.{1}) (κ := κ) (Cw := Cw)
                (x := fun _ : PUnit.{1} => x)
      _ = Measure.pi (fun _ : κ => ν) := by
            rw [hmat]
  -- Step 2: recover the law of the real outputs from the Euclidean-embedded law.
  have hz_meas : Measurable (fun q : LayerParams ι κ =>
      fun j : κ => (DenseLayer.ofParams q).preactivation x j) := by
    dsimp [DenseLayer.preactivation, DenseLayer.ofParams, Matrix.mulVec]
    fun_prop
  have hf_meas : Measurable (fun q : LayerParams ι κ =>
      fun j : κ => (EuclideanSpace.equiv PUnit ℝ).symm
        (fun _ : PUnit => (DenseLayer.ofParams q).preactivation x j)) := by
    have h1 : Measurable (fun v : κ → ℝ =>
        fun j : κ => (EuclideanSpace.equiv PUnit ℝ).symm (fun _ : PUnit => v j)) := by
      refine Measurable.of_eval (fun j => ?_)
      exact hT_meas.comp (measurable_pi_apply j)
    exact h1.comp hz_meas
  have hg_meas : Measurable (fun v : κ → EuclideanSpace ℝ PUnit =>
      fun j : κ => (v j) PUnit.unit) := by
    refine Measurable.of_eval (fun j => ?_)
    exact hEval_meas.comp (measurable_pi_apply j)
  have hcomp : (fun v : κ → EuclideanSpace ℝ PUnit => fun j : κ => (v j) PUnit.unit) ∘
      (fun q : LayerParams ι κ => fun j : κ => (EuclideanSpace.equiv PUnit ℝ).symm
        (fun _ : PUnit => (DenseLayer.ofParams q).preactivation x j)) =
    fun q : LayerParams ι κ => fun j : κ => (DenseLayer.ofParams q).preactivation x j := by
    funext q j
    exact hT_inv _
  have hLaw : oneLayerOutputLaw (ι := ι) (κ := κ) Cw x =
      Measure.map (fun v : κ → EuclideanSpace ℝ PUnit => fun j : κ => (v j) PUnit.unit)
        (Measure.pi (fun _ : κ => ν)) := by
    calc
      oneLayerOutputLaw (ι := ι) (κ := κ) Cw x
          = Measure.map (fun q : LayerParams ι κ =>
              fun j : κ => (DenseLayer.ofParams q).preactivation x j)
              (layerGaussianInit (hyperparams Cw) ι κ) := rfl
      _ = Measure.map (fun v : κ → EuclideanSpace ℝ PUnit => fun j : κ => (v j) PUnit.unit)
            (Measure.map (fun q : LayerParams ι κ =>
                fun j : κ => (EuclideanSpace.equiv PUnit ℝ).symm
                  (fun _ : PUnit => (DenseLayer.ofParams q).preactivation x j))
              (layerGaussianInit (hyperparams Cw) ι κ)) := by
            rw [Measure.map_map hg_meas hf_meas, hcomp]
      _ = Measure.map (fun v : κ → EuclideanSpace ℝ PUnit => fun j : κ => (v j) PUnit.unit)
            (Measure.pi (fun _ : κ => ν)) := by
            rw [hA]
  -- Step 3: project the product law coordinatewise.
  have hProj :
      Measure.map (fun v : κ → EuclideanSpace ℝ PUnit => fun j : κ => (v j) PUnit.unit)
          (Measure.pi (fun _ : κ => ν)) =
        Measure.pi (fun _ : κ => ν.map evalV) := by
    -- Typeclass search cannot apply the `IsGaussian` instance for `multivariateGaussian`
    -- (its conclusion head is a reducible `def`), so build the probability instances by hand
    -- and feed them to the product-measure API explicitly.
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
        (fun j : κ => fun v : κ → EuclideanSpace ℝ PUnit.{1} => (v j) PUnit.unit)
        (Measure.pi (fun _ : κ => ν)) := by
      simpa using
        (@iIndepFun_pi κ _ (fun _ : κ => EuclideanSpace ℝ PUnit.{1}) _ (fun _ : κ => ν)
          (fun _ => hprob) (fun _ : κ => ℝ) _ (fun _ : κ => evalV)
          (fun j => hEval_meas.aemeasurable))
    have hmap := @iIndepFun.map_fun_eq_pi_map (κ → EuclideanSpace ℝ PUnit.{1}) κ _
      (Measure.pi (fun _ : κ => ν)) _ (fun _ : κ => ℝ) _
      (fun (j : κ) (v : κ → EuclideanSpace ℝ PUnit.{1}) => (v j) PUnit.unit)
      (fun j => (hEval_meas.comp (measurable_pi_apply j)).aemeasurable) hIndep
    calc
      Measure.map (fun v : κ → EuclideanSpace ℝ PUnit => fun j : κ => (v j) PUnit.unit)
          (Measure.pi (fun _ : κ => ν))
          = Measure.pi (fun j : κ => (Measure.pi (fun _ : κ => ν)).map
              (fun v : κ → EuclideanSpace ℝ PUnit => (v j) PUnit.unit)) := hmap
      _ = Measure.pi (fun _ : κ => ν.map evalV) := by
            congr 1
            funext j
            calc
              (Measure.pi (fun _ : κ => ν)).map
                  (fun v : κ → EuclideanSpace ℝ PUnit => (v j) PUnit.unit)
                  = (Measure.pi (fun _ : κ => ν)).map
                      (evalV ∘ (fun v : κ → EuclideanSpace ℝ PUnit => v j)) := rfl
              _ = ((Measure.pi (fun _ : κ => ν)).map
                    (fun v : κ → EuclideanSpace ℝ PUnit => v j)).map evalV := by
                    rw [Measure.map_map hEval_meas (measurable_pi_apply j)]
              _ = ν.map evalV := by
                    rw [(@measurePreserving_eval κ (fun _ : κ => EuclideanSpace ℝ PUnit.{1}) _ _
                      (fun _ : κ => ν) (fun _ => hprob) j).map_eq]
  -- Step 4: each projected coordinate is the image of `gaussianReal 0 1` under `y ↦ √s * y`.
  have hν_proj : ν.map evalV = (gaussianReal 0 1).map (fun y : ℝ => Real.sqrt s * y) := by
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
    have hscale : (gaussianReal 0 1).map (fun y : ℝ => Real.sqrt s * y) =
        gaussianReal 0 ⟨s, hs⟩ := by
      have h := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (c := Real.sqrt s)
      calc
        (gaussianReal 0 1).map (fun y : ℝ => Real.sqrt s * y)
            = gaussianReal (Real.sqrt s * 0)
                (⟨(Real.sqrt s) ^ 2, sq_nonneg (Real.sqrt s)⟩ * (1 : ℝ≥0)) := h
        _ = gaussianReal 0 ⟨s, hs⟩ := by
              congr 1
              · ring
              · apply Subtype.ext
                change (Real.sqrt s ^ 2) * 1 = s
                rw [mul_one]
                exact Real.sq_sqrt hs
    calc
      ν.map evalV = (multivariateGaussian 0 S₀).map evalV := rfl
      _ = gaussianReal 0 ⟨s, hs⟩ := by
            rw [hstep1, hstep2]
      _ = (gaussianReal 0 1).map (fun y : ℝ => Real.sqrt s * y) := hscale.symm
  -- Step 5: relabel `κ` to `Fin (Fintype.card κ)` and pull the per-coordinate scale out.
  have hRelabel_scale :
      Measure.pi (fun _ : κ => (gaussianReal 0 1).map (fun y : ℝ => Real.sqrt s * y)) =
        (Measure.pi (fun _ : Fin (Fintype.card κ) => gaussianReal 0 1)).map
          (fun g : Fin (Fintype.card κ) → ℝ => fun j : κ => Real.sqrt s * g (e j)) := by
    let ν₁ : Measure ℝ := (gaussianReal 0 1).map (fun y : ℝ => Real.sqrt s * y)
    have hscale_pi : (Measure.pi (fun _ : Fin (Fintype.card κ) => gaussianReal 0 1)).map
          (fun g : Fin (Fintype.card κ) → ℝ => fun i : Fin (Fintype.card κ) => Real.sqrt s * g i) =
        Measure.pi (fun _ : Fin (Fintype.card κ) => ν₁) := by
      have hIndep : iIndepFun
          (fun i : Fin (Fintype.card κ) => fun g : Fin (Fintype.card κ) → ℝ => Real.sqrt s * g i)
          (Measure.pi (fun _ : Fin (Fintype.card κ) => gaussianReal 0 1)) := by
        simpa using
          (iIndepFun_pi (μ := fun _ : Fin (Fintype.card κ) => gaussianReal 0 1)
            (X := fun _ : Fin (Fintype.card κ) => fun y : ℝ => Real.sqrt s * y)
            (mX := fun i =>
              (by fun_prop : Measurable fun y : ℝ => Real.sqrt s * y).aemeasurable))
      have hmap := iIndepFun.map_fun_eq_pi_map
        (μ := Measure.pi (fun _ : Fin (Fintype.card κ) => gaussianReal 0 1))
        (f := fun (i : Fin (Fintype.card κ)) (g : Fin (Fintype.card κ) → ℝ) => Real.sqrt s * g i)
        (hf := fun i =>
          (by fun_prop : Measurable fun g : Fin (Fintype.card κ) → ℝ =>
            Real.sqrt s * g i).aemeasurable)
        hIndep
      calc
        (Measure.pi (fun _ : Fin (Fintype.card κ) => gaussianReal 0 1)).map
            (fun g : Fin (Fintype.card κ) → ℝ => fun i : Fin (Fintype.card κ) => Real.sqrt s * g i)
            = Measure.pi (fun i : Fin (Fintype.card κ) =>
                (Measure.pi (fun _ : Fin (Fintype.card κ) => gaussianReal 0 1)).map
                  (fun g : Fin (Fintype.card κ) → ℝ => Real.sqrt s * g i)) := hmap
        _ = Measure.pi (fun _ : Fin (Fintype.card κ) => ν₁) := by
              congr 1
              funext i
              calc
                (Measure.pi (fun _ : Fin (Fintype.card κ) => gaussianReal 0 1)).map
                    (fun g : Fin (Fintype.card κ) → ℝ => Real.sqrt s * g i)
                    = (Measure.pi (fun _ : Fin (Fintype.card κ) => gaussianReal 0 1)).map
                        ((fun y : ℝ => Real.sqrt s * y) ∘
                          (fun g : Fin (Fintype.card κ) → ℝ => g i)) := rfl
                _ = ((Measure.pi (fun _ : Fin (Fintype.card κ) => gaussianReal 0 1)).map
                      (fun g : Fin (Fintype.card κ) → ℝ => g i)).map
                      (fun y : ℝ => Real.sqrt s * y) := by
                      rw [Measure.map_map (by fun_prop : Measurable fun y : ℝ => Real.sqrt s * y)
                        (measurable_pi_apply i)]
                _ = ν₁ := by
                      dsimp [ν₁]
                      rw [(measurePreserving_eval (fun _ : Fin (Fintype.card κ) => gaussianReal 0 1)
                        i).map_eq]
    have hrelabel : Measure.pi (fun _ : κ => ν₁) =
        (Measure.pi (fun _ : Fin (Fintype.card κ) => ν₁)).map
          (fun h : Fin (Fintype.card κ) → ℝ => fun j : κ => h (e j)) := by
      have hp := measurePreserving_piCongrLeft (α := fun _ : κ => ℝ)
        (μ := fun _ : κ => ν₁) (f := e.symm)
      rw [← hp.map_eq]
      congr 1
      funext h j
      simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.symm_symm, e]
    calc
      Measure.pi (fun _ : κ => (gaussianReal 0 1).map (fun y : ℝ => Real.sqrt s * y))
          = Measure.pi (fun _ : κ => ν₁) := by rfl
      _ = (Measure.pi (fun _ : Fin (Fintype.card κ) => ν₁)).map
            (fun h : Fin (Fintype.card κ) → ℝ => fun j : κ => h (e j)) := hrelabel
      _ = ((Measure.pi (fun _ : Fin (Fintype.card κ) => gaussianReal 0 1)).map
            (fun g : Fin (Fintype.card κ) → ℝ => fun i : Fin (Fintype.card κ) =>
              Real.sqrt s * g i)).map
            (fun h : Fin (Fintype.card κ) → ℝ => fun j : κ => h (e j)) := by
            rw [hscale_pi]
      _ = (Measure.pi (fun _ : Fin (Fintype.card κ) => gaussianReal 0 1)).map
            (fun g : Fin (Fintype.card κ) → ℝ => fun j : κ => Real.sqrt s * g (e j)) := by
            rw [Measure.map_map (by fun_prop : Measurable fun h : Fin (Fintype.card κ) → ℝ =>
                fun j : κ => h (e j))
              (by fun_prop : Measurable fun g : Fin (Fintype.card κ) → ℝ =>
                fun i : Fin (Fintype.card κ) => Real.sqrt s * g i)]
            rfl
  calc
    oneLayerOutputLaw (ι := ι) (κ := κ) Cw x
        = Measure.map (fun v : κ → EuclideanSpace ℝ PUnit => fun j : κ => (v j) PUnit.unit)
            (Measure.pi (fun _ : κ => ν)) := hLaw
    _ = Measure.pi (fun _ : κ => ν.map evalV) := hProj
    _ = Measure.pi (fun _ : κ => (gaussianReal 0 1).map (fun y : ℝ => Real.sqrt s * y)) := by
          congr 1
          funext j
          exact hν_proj
    _ = (Measure.pi (fun _ : Fin (Fintype.card κ) => gaussianReal 0 1)).map
          (fun g : Fin (Fintype.card κ) → ℝ => fun j : κ => Real.sqrt s * g (e j)) := hRelabel_scale
    _ = Measure.map
          (fun g : Fin (Fintype.card κ) → ℝ => fun j : κ =>
            Real.sqrt ((Cw : ℝ) * NeuralNetwork.normalizedEnergy x) * g (Fintype.equivFin κ j))
          ((Measure.pi fun _ : Fin (Fintype.card κ) => gaussianReal 0 1)) := by
          dsimp [s, e]

/-- Transport-and-scaling form of the one-layer normalized-energy moment calculation.

This lemma isolates the probabilistic assembly step from the purely radial chi-square calculation:
the output of one bias-free Gaussian layer with deterministic input `x` has the same normalized
energy moments as a standard Gaussian vector, multiplied by the scale
`((Cw : ℝ) * normalizedEnergy x)^m`.

Informal proof.  Specialize `map_batchPreactivation` to a singleton batch.  The singleton Gram
identity `NeuralNetwork.normalizedGram_singleton` identifies every output coordinate with a
centered Gaussian of variance `(Cw : ℝ) * normalizedEnergy x`, and different output coordinates
are independent because `map_batchPreactivation` gives a product measure over `κ`.  Rewrite this
one-dimensional Gaussian as the image of `gaussianReal 0 1` under multiplication by
`Real.sqrt ((Cw : ℝ) * normalizedEnergy x)`, using
`ProbabilityTheory.gaussianReal_map_const_mul` and nonnegativity from `Cw.property` and
`NeuralNetwork.normalizedEnergy_nonneg x`.  Relabel the finite output type `κ` by
`Fintype.equivFin κ`; `MeasurableEquiv.piCongrLeft`/`measurePreserving_piCongrLeft` transports the
standard product Gaussian to `Measure.pi fun _ : Fin (Fintype.card κ) => gaussianReal 0 1`.
Finally, pointwise,
`normalizedEnergy (fun j => sqrt s * g j) = s * normalizedEnergy g`; raising to the `m`-th power
and factoring the constant out of the integral gives the stated identity.

This is the standard first-layer Gaussian law and radial rescaling step; see
`docs/Renormalization.md`, equations `eq:two-point-function-deep-linear-layer-ell` and
`eq:deep-linear-2m-point-function`, and Hanin's lecture notes §3.2.
-/
theorem integral_normalizedEnergy_pow_oneLayerOutputLaw_eq_scaled_stdGaussian
    {ι : Type uI} {κ : Type uJ} [Fintype ι] [Fintype κ]
    (Cw : ℝ≥0) (x : ι → ℝ) (m : ℕ) :
    ∫ z : κ → ℝ, NeuralNetwork.normalizedEnergy z ^ m
        ∂oneLayerOutputLaw (ι := ι) (κ := κ) Cw x =
      ((Cw : ℝ) * NeuralNetwork.normalizedEnergy x) ^ m *
        ∫ g : Fin (Fintype.card κ) → ℝ, NeuralNetwork.normalizedEnergy g ^ m
          ∂(Measure.pi fun _ : Fin (Fintype.card κ) => gaussianReal 0 1) := by
  classical
  let s : ℝ := (Cw : ℝ) * NeuralNetwork.normalizedEnergy x
  have hs : 0 ≤ s := by
    dsimp [s]
    exact mul_nonneg Cw.property (NeuralNetwork.normalizedEnergy_nonneg x)
  let φ : (Fin (Fintype.card κ) → ℝ) → κ → ℝ :=
    fun g j => Real.sqrt s * g (Fintype.equivFin κ j)
  have hLaw : oneLayerOutputLaw (ι := ι) (κ := κ) Cw x =
      Measure.map φ ((Measure.pi fun _ : Fin (Fintype.card κ) => gaussianReal 0 1)) := by
    simpa [φ, s] using oneLayerOutputLaw_eq_map_stdGaussian Cw x
  have hφ_meas : Measurable φ := by
    dsimp [φ]
    refine Measurable.of_eval (fun j => ?_)
    exact (by fun_prop : Measurable fun y : ℝ => Real.sqrt s * y).comp
      (measurable_pi_apply (Fintype.equivFin κ j))
  have hcont : Continuous (fun z : κ → ℝ => NeuralNetwork.normalizedEnergy z ^ m) := by
    dsimp [NeuralNetwork.normalizedEnergy]
    fun_prop
  have hpoint (g : Fin (Fintype.card κ) → ℝ) :
      (NeuralNetwork.normalizedEnergy (φ g)) ^ m = (s * NeuralNetwork.normalizedEnergy g) ^ m := by
    rw [normalizedEnergy_comp_smul_equiv (c := Real.sqrt s) (e := Fintype.equivFin κ) g]
    rw [Real.sq_sqrt hs]
  calc
    ∫ z : κ → ℝ, NeuralNetwork.normalizedEnergy z ^ m
        ∂oneLayerOutputLaw (ι := ι) (κ := κ) Cw x
        = ∫ z : κ → ℝ, NeuralNetwork.normalizedEnergy z ^ m
            ∂Measure.map φ ((Measure.pi fun _ : Fin (Fintype.card κ) => gaussianReal 0 1)) := by
          rw [hLaw]
    _ = ∫ g : Fin (Fintype.card κ) → ℝ,
          (NeuralNetwork.normalizedEnergy (φ g)) ^ m
          ∂(Measure.pi fun _ : Fin (Fintype.card κ) => gaussianReal 0 1) := by
          rw [MeasureTheory.integral_map]
          · exact hφ_meas.aemeasurable
          · exact hcont.aestronglyMeasurable
    _ = ∫ g : Fin (Fintype.card κ) → ℝ, (s * NeuralNetwork.normalizedEnergy g) ^ m
          ∂(Measure.pi fun _ : Fin (Fintype.card κ) => gaussianReal 0 1) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with g
          exact hpoint g
    _ = s ^ m *
          ∫ g : Fin (Fintype.card κ) → ℝ, NeuralNetwork.normalizedEnergy g ^ m
            ∂(Measure.pi fun _ : Fin (Fintype.card κ) => gaussianReal 0 1) := by
          simp_rw [mul_pow]
          rw [MeasureTheory.integral_const_mul]
    _ = ((Cw : ℝ) * NeuralNetwork.normalizedEnergy x) ^ m *
          ∫ g : Fin (Fintype.card κ) → ℝ, NeuralNetwork.normalizedEnergy g ^ m
            ∂(Measure.pi fun _ : Fin (Fintype.card κ) => gaussianReal 0 1) := by
          rfl

/-- One freshly initialized layer multiplies the `m`-th normalized-energy moment by
`(Cw * Q(x))^m c_{2m}(n)`.

Informal proof: conditional on `x`, every output is `sqrt(Cw * Q(x))` times an independent
standard Gaussian.  Pull this common scale through normalized energy and apply
`integral_normalizedEnergy_pow_stdGaussian`.  Source: `docs/Renormalization.md`, the radial
recursion leading to equation `eq:deep-linear-2m-point-function`.
-/
theorem integral_normalizedEnergy_pow_randomLayerKernel
    {ι : Type uI} {κ : Type uJ} [Fintype ι] [Fintype κ]
    (Cw : ℝ≥0) (x : ι → ℝ) (m : ℕ) (hκ : 0 < Fintype.card κ) :
    ∫ z : κ → ℝ, NeuralNetwork.normalizedEnergy z ^ m
        ∂oneLayerOutputLaw (ι := ι) (κ := κ) Cw x =
      ((Cw : ℝ) * NeuralNetwork.normalizedEnergy x) ^ m *
        widthMomentFactor m (Fintype.card κ) := by
  calc
    ∫ z : κ → ℝ, NeuralNetwork.normalizedEnergy z ^ m
        ∂oneLayerOutputLaw (ι := ι) (κ := κ) Cw x
        = ((Cw : ℝ) * NeuralNetwork.normalizedEnergy x) ^ m *
            ∫ g : Fin (Fintype.card κ) → ℝ, NeuralNetwork.normalizedEnergy g ^ m
              ∂(Measure.pi fun _ : Fin (Fintype.card κ) => gaussianReal 0 1) := by
          exact integral_normalizedEnergy_pow_oneLayerOutputLaw_eq_scaled_stdGaussian Cw x m
    _ = ((Cw : ℝ) * NeuralNetwork.normalizedEnergy x) ^ m *
          widthMomentFactor m (Fintype.card κ) := by
          rw [integral_normalizedEnergy_pow_stdGaussian m (Fintype.card κ) hκ]

end NeuralNetwork.DeepLinear

end

end
