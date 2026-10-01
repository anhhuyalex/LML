/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Basic
public import LeanMachineLearning.Optimization.NTK.Shallow.Kernel
public import LeanMachineLearning.Optimization.NTK.Shallow.Linearization
public import LeanMachineLearning.Optimization.NTK.ReLU.ArcCosine
public import LeanMachineLearning.Optimization.NTK.Foundations.SlutskyTightness
public import Mathlib.MeasureTheory.Measure.TightNormed
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.StrongLaw
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.CharacteristicFunction
public import Mathlib.Analysis.Matrix.Normed

/-!
# Two-layer initialization: network setup and independence structure

Network evaluation and the empirical covariance, the initialization probability space and its
independence structure, and entrywise (max) concentration for the readout weights.

## Main results and proof outline

* Readout weights: $a_i \stackrel{\text{i.i.d.}}{\sim} \mathcal{N}(0, 1) \quad \forall i$
  (`gaussianReadoutMeasure n`).
* Parameter space $\boldsymbol{\theta} = \{(a_i, \mathbf{w}_i)\}_{i=1}^n$ with joint measure
  `initMeasure n d`.
* Mutual Independence: $\{a_i\}_{i=1}^n$ is mutually independent of $\{\mathbf{w}_i\}_{i=1}^n$
  (`indepFun_input_readout`).
* Scalar network output:
  $f(\mathbf{x}; \boldsymbol{\theta}) =
    \frac{1}{\sqrt{n}} \sum_{i=1}^n a_i \varphi(\mathbf{w}_i^\top \mathbf{x})$
  (`evalSingle φ W a x`).
* Output vector $\mathbf{f}_m = (f(\mathbf{x}^1), \dots, f(\mathbf{x}^m))^\top$
  (`evalVector φ W a X`).
* Empirical covariance matrix $\boldsymbol{\Phi}^{(n)} \in \mathbb{R}^{m \times m}$:
  $\Phi^{(n), \alpha \beta} :=
    \frac{1}{n} \sum_{i=1}^n \varphi(\mathbf{w}_i^\top \mathbf{x}^\alpha)
    \varphi(\mathbf{w}_i^\top \mathbf{x}^\beta)$
  (`empiricalCovariance n φ W X`).
* `NTK.evalSingle` : scalar network output
  $f(\mathbf{x}; \mathbf{W}, a) =
    \frac{1}{\sqrt{n}} \sum_{i=1}^n a_i \varphi(\mathbf{w}_i^\top \mathbf{x})$.
* `NTK.evalSingle_eq_normalized_sum` : equation lemma for scalar network evaluation.
* `NTK.evalVector` : output vector $\mathbf{f}_m(\mathbf{W}, a) \in \mathbb{R}^m$.
* `NTK.empiricalCovariance` : empirical covariance matrix
  $\boldsymbol{\Phi}^{(n)} \in \mathbb{R}^{m \times m}$.
* `NTK.gaussianReadoutMeasure` : transparent product measure
  $\bigotimes_{i=1}^n \mathcal{N}(0, 1)$.
* `NTK.initMeasure` : joint parameter initialization measure
  $(\bigotimes_{i=1}^n \mathcal{N}(\mathbf{0}, \mathbf{I}_{n_0})) \otimes
    (\bigotimes_{i=1}^n \mathcal{N}(0, 1))$.
* `NTK.indepFun_input_readout` : mutual independence of input weights $\mathbf{W}$ and
  readout weights $a$.

See
`LeanMachineLearning.Optimization.NTK.Initialization`
for the overview of the whole development.
-/

@[expose] public section

set_option linter.style.longLine false

open Real MeasureTheory ProbabilityTheory Matrix Complex
open scoped BigOperators MatrixOrder RealInnerProductSpace Kronecker ENNReal

namespace NTK

variable {d n m : ℕ}

section Preliminaries

/-! ## Network Setup and Initialization Probability Space -/

/-! ### Network Evaluation and Empirical Covariance -/

/-- Single-output evaluation of a two-layer neural network with width `n`, activation `φ`,
input weights `W`, and readout weights `a`:
  `f(x; W, a) = (1/√n) ∑ i, a i * φ (W i ⬝ᵥ x)`. -/
noncomputable def evalSingle
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (x : Fin d → ℝ) : ℝ :=
  (n : ℝ)⁻¹.sqrt * ∑ i : Fin n, a i * φ (W i ⬝ᵥ x)

/-- The normalized-sum formula for a scalar network evaluation. This is the public
equation lemma for `evalSingle`, so proofs need not unfold its implementation. -/
lemma evalSingle_eq_normalized_sum
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (x : Fin d → ℝ) :
    evalSingle φ W a x = (n : ℝ)⁻¹.sqrt * ∑ i : Fin n, a i * φ (W i ⬝ᵥ x) := rfl

/-- The output vector `f_m(W, a) ∈ ℝᵐ` evaluated at `m` input points `X 0, …, X (m - 1)`:
  `f_m(W, a)_α = f(X α; W, a)`. -/
noncomputable def evalVector
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (X : Fin m → Fin d → ℝ) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun α => evalSingle φ W a (X α))

/-- The empirical covariance matrix `Φ^{(n)} ∈ ℝ^{m × m}`:
  `Φ^{(n), α β} = (1/n) ∑ i, φ (W i ⬝ᵥ X α) * φ (W i ⬝ᵥ X β)`. -/
noncomputable def empiricalCovariance
    (n : ℕ) (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun α β => (n : ℝ)⁻¹ * ∑ i : Fin n, φ (W i ⬝ᵥ X α) * φ (W i ⬝ᵥ X β)

/-! ### API for Network Evaluation -/

@[simp] lemma evalVector_ofLp
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (X : Fin m → Fin d → ℝ) (α : Fin m) :
    (evalVector φ W a X).ofLp α = evalSingle φ W a (X α) := rfl

lemma evalVector_inner
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (a : Fin n → ℝ) (t : EuclideanSpace ℝ (Fin m)) :
    ⟪t, evalVector φ W a X⟫ = ∑ α : Fin m, t.ofLp α * evalSingle φ W a (X α) := by
  simp only [evalVector, PiLp.inner_apply, RCLike.inner_apply', conj_trivial]

lemma evalVector_continuous
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ) :
    Continuous (fun a => evalVector φ W a X) := by
  change Continuous ((WithLp.toLp 2) ∘ (fun a α => evalSingle φ W a (X α)))
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun α => ?_)
  simp only [evalSingle_eq_normalized_sum]
  exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
    (continuous_apply i).mul continuous_const)

lemma evalVector_measurable
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ) :
    Measurable (fun a => evalVector φ W a X) :=
  (evalVector_continuous φ W X).measurable

lemma inner_evalVector_continuous
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    Continuous (fun a => ⟪t, evalVector φ W a X⟫) :=
  (innerSL ℝ t).continuous.comp (evalVector_continuous φ W X)

lemma inner_evalVector_measurable
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    Measurable (fun a => ⟪t, evalVector φ W a X⟫) :=
  (inner_evalVector_continuous φ W X t).measurable

/-! ### Initialization Probability Space and Independence Structure -/

/-- Transparent readout weight product measure on `Fin n → ℝ` with i.i.d. coordinates $\mathcal{N}(0, 1)$. -/
noncomputable abbrev gaussianReadoutMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 1)

/-- Instance: `gaussianInit n d` from `NTK.Basic` is a probability measure. -/
instance instIsProbabilityMeasureGaussianInit (n d : ℕ) :
    IsProbabilityMeasure (gaussianInit n d) := by
  dsimp [gaussianInit]
  infer_instance

/-- Transparent joint initialization measure on `(Fin n → Fin d → ℝ) × (Fin n → ℝ)`
using the existing `NTK.gaussianInit` from `NTK.Basic`. -/
noncomputable abbrev initMeasure (n d : ℕ) : Measure ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) :=
  (gaussianInit n d).prod (gaussianReadoutMeasure n)

/-- Readout weight coordinates `a_i` have marginal standard normal distribution
$\mathcal{N}(0, 1)$. -/
lemma map_gaussianReadoutMeasure_coord (i : Fin n) :
    Measure.map (fun a : Fin n → ℝ => a i) (gaussianReadoutMeasure n) = gaussianReal 0 1 :=
  (MeasureTheory.measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).map_eq

/-- The square function is integrable with respect to the standard real Gaussian measure. -/
lemma integrable_sq_gaussianReal : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := by
  apply (memLp_two_iff_integrable_sq
    (memLp_id_gaussianReal (2 : NNReal)).aestronglyMeasurable).1
  exact memLp_id_gaussianReal (2 : NNReal)

/-- The second moment of the standard real Gaussian measure is 1. -/
lemma integral_sq_gaussianReal : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := ProbabilityTheory.variance_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : NNReal))
  rw [variance_eq_integral (X := id) measurable_id'.aemeasurable] at h
  simpa [id] using h

/-- The fourth power is integrable with respect to the standard real Gaussian measure. -/
lemma integrable_pow_four_gaussianReal :
    Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) := by
  have h := memLp_id_gaussianReal (4 : NNReal) (μ := 0) (v := 1)
  have hint := h.integrable_norm_rpow (by norm_num) (by norm_num)
  have heq : (fun x : ℝ => ‖id x‖ ^ (4 : ℝ)) = (fun x : ℝ => x ^ 4) := by
    ext x
    simp only [id, Real.norm_eq_abs]
    have h1 : (4 : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
    rw [h1, Real.rpow_natCast]
    have h2 : |x| ^ 4 = (|x| ^ 2) ^ 2 := by ring
    have h3 : x ^ 4 = (x ^ 2) ^ 2 := by ring
    rw [h2, sq_abs, ← h3]
  have h_exp : ((4 : NNReal) : ENNReal).toReal = 4 := by rfl
  rw [h_exp] at hint
  rw [heq] at hint
  exact hint

/-- The square function is square-integrable (in `MemLp 2`) with respect to the standard
real Gaussian measure. -/
lemma memLp_sq_gaussianReal_two :
    MemLp (fun x : ℝ => x ^ 2) 2 (gaussianReal 0 1) := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  have heq : (fun x : ℝ => (x ^ 2) ^ 2) = (fun x : ℝ => x ^ 4) := by
    ext x; ring
  rw [heq]
  exact integrable_pow_four_gaussianReal

/-- The normalized squared Euclidean norm of a readout vector. -/
noncomputable def gaussianReadoutEnergy (n : ℕ) (a : Fin n → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i : Fin n, a i ^ 2

/-- Markov tail bound for the normalized squared readout energy. -/
lemma prob_gaussianReadout_sum_sq_le
    (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    (gaussianReadoutMeasure n).real {a | (n : ℝ)⁻¹ * ∑ i : Fin n, a i ^ 2 ≤ δ⁻¹} ≥
      1 - δ :=
  measureReal_pi_average_le_ge_one_sub (μ := gaussianReal 0 1) hn (g := fun a : ℝ => a ^ 2)
    (by fun_prop) integrable_sq_gaussianReal (fun _ => sq_nonneg _) (inv_pos.2 hδ)
    (by rw [integral_sq_gaussianReal, inv_mul_cancel₀ hδ.ne'])

/-- **Empirical activation energy concentration.** If `φ(w ⬝ᵥ x_α)` is square integrable under the
Gaussian row law and `∑_α E φ(w ⬝ᵥ x_α)² ≤ τ δ`, then the width-normalized activation energy
`n⁻¹ ∑_i ∑_α φ(W_i ⬝ᵥ x_α)²` of the hidden weights is at most `τ` with probability `≥ 1 - δ`. -/
lemma measureReal_gaussianInit_activationEnergy_le {n d m : ℕ} (hn : 0 < n) (φ : ℝ → ℝ)
    (hφ : Measurable φ) (X : Fin m → Fin d → ℝ)
    (hL2 : ∀ α, MemLp (fun w : Fin d → ℝ => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d))
    {τ δ : ℝ} (hτ : 0 < τ)
    (hv : ∑ α : Fin m, ∫ w, φ (w ⬝ᵥ X α) ^ 2 ∂(gaussianRowMeasure d) ≤ τ * δ) :
    (gaussianInit n d).real {W | (n : ℝ)⁻¹ * ∑ i : Fin n, ∑ α : Fin m,
      φ (W i ⬝ᵥ X α) ^ 2 ≤ τ} ≥ 1 - δ :=
  measureReal_pi_average_le_ge_one_sub (μ := gaussianRowMeasure d) hn
    (g := fun w => ∑ α : Fin m, φ (w ⬝ᵥ X α) ^ 2)
    (Finset.measurable_sum _ fun α _ =>
      (hφ.comp (measurable_dotProduct_left (X α))).pow_const 2)
    (integrable_finsetSum _ fun α _ => (hL2 α).integrable_sq) (fun w => by positivity) hτ
    (by rwa [integral_finsetSum _ fun α _ => (hL2 α).integrable_sq])

/-- A measurable activation with at most linear growth has all Gaussian moments along a row. -/
lemma memLp_gaussianRow_comp_of_linear_growth (φ : ℝ → ℝ) (hφ : Measurable φ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgrow : ∀ z, |φ z| ≤ A + B * |z|) (x : Fin d → ℝ) (p : NNReal) :
    MemLp (fun w : Fin d → ℝ => φ (w ⬝ᵥ x)) p (gaussianRowMeasure d) := by
  have hlin : Measurable (fun w : Fin d → ℝ => w ⬝ᵥ x) := measurable_dotProduct_left x
  change MemLp (φ ∘ fun w : Fin d → ℝ => w ⬝ᵥ x) p (gaussianRowMeasure d)
  rw [← memLp_map_measure_iff (hφ.aestronglyMeasurable) hlin.aemeasurable,
    map_gaussianRowMeasure_dotProduct]
  have hid := memLp_id_gaussianReal (μ := 0) (v := Real.toNNReal (x ⬝ᵥ x)) p
  refine MemLp.of_le (g := fun z => A + B * ‖z‖) ?_ hφ.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  · exact (memLp_const A).add (hid.norm.const_mul B)
  · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ A + B * ‖z‖)]
    simpa [Real.norm_eq_abs] using hgrow z

/-- Product of two such activations along rows is square integrable (Hölder with exponents
`4, 4 → 2`). -/
lemma memLp_two_gaussianRow_mul_comp_of_linear_growth (φ : ℝ → ℝ) (hφ : Measurable φ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgrow : ∀ z, |φ z| ≤ A + B * |z|) (x x' : Fin d → ℝ) :
    MemLp (fun w : Fin d → ℝ => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x')) 2 (gaussianRowMeasure d) := by
  have h4 : ∀ y : Fin d → ℝ, MemLp (fun w : Fin d → ℝ => φ (w ⬝ᵥ y)) (4 : ENNReal)
      (gaussianRowMeasure d) := fun y => by
    simpa using memLp_gaussianRow_comp_of_linear_growth φ hφ hA hB hgrow y (d := d) 4
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [← two_mul]
    have : (4 : ENNReal) = 2 * 2 := by norm_num
    rw [this, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by simp)), ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by simp), one_mul]⟩
  exact MemLp.mul (r := 2) (h4 x') (h4 x)
/-! ### Entrywise (max) concentration for readout weights

`prob_gaussianReadout_sum_sq_le` above bounds the readout *energy* `n⁻¹ ∑ᵢ aᵢ²` (an average),
via Markov's inequality, giving a tail bound whose natural scale is `O(√(n/δ))`. Gap 4
(`NTK.Training.TwoLayer.JacobianBounds`'s
`outputJacobian_netFromParams_frobenius_sub_le`) instead needs a uniform
bound on every *individual* `|aᵢ|`. Bounding this the same crude way (Markov on each `aᵢ²`
plus a union bound) would give `R = O(√(n/δ))` too - and since Gap 4's `L_J` is linear in `R`,
an `R` that grows like `√n` would make `L_J = Θ(1)`, silently breaking the "kernel freezes as
`n → ∞`" conclusion the whole plan is aimed at (see `docs/NTK_lazy_training_gap_closure_plan.md`
§3.1). The fix is to use the actual Gaussian tail (Chernoff/sub-Gaussian) instead of Markov,
which gives the much better `R = O(√(log(n/δ)))` - logarithmic, not polynomial, in the width. -/

/-- The standard Gaussian has a sub-Gaussian moment-generating function with parameter `1`. -/
lemma hasSubgaussianMGF_id_gaussianReal_zero_one :
    ProbabilityTheory.HasSubgaussianMGF id (1 : NNReal) (gaussianReal 0 1) where
  integrable_exp_mul := integrable_exp_mul_gaussianReal
  mgf_le t := by rw [mgf_id_gaussianReal]; simp

/-- Negating a standard Gaussian is still sub-Gaussian with the same parameter (used for the
two-sided/absolute-value tail bound below). -/
lemma hasSubgaussianMGF_neg_id_gaussianReal_zero_one :
    ProbabilityTheory.HasSubgaussianMGF (fun x => -x) (1 : NNReal) (gaussianReal 0 1) where
  integrable_exp_mul t := by
    have := integrable_exp_mul_gaussianReal (μ := (0:ℝ)) (v := (1:NNReal)) (-t)
    simpa [mul_comm, mul_neg] using this
  mgf_le t := by
    have h := hasSubgaussianMGF_id_gaussianReal_zero_one.mgf_le (-t)
    unfold mgf at *
    simp only [id] at h ⊢
    convert h using 2
    · ext x; ring_nf
    · ring

/-- Two-sided Chernoff tail bound for a standard Gaussian: `P(|X| ≥ ε) ≤ 2 exp(-ε²/2)`. -/
lemma prob_abs_gaussianReal_ge_le (ε : ℝ) (hε : 0 ≤ ε) :
    (gaussianReal 0 1).real {x : ℝ | ε ≤ |x|} ≤ 2 * Real.exp (-ε ^ 2 / 2) := by
  have hset : {x : ℝ | ε ≤ |x|} = {x : ℝ | ε ≤ x} ∪ {x : ℝ | ε ≤ -x} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  rw [hset]
  have h1 := hasSubgaussianMGF_id_gaussianReal_zero_one.measure_ge_le hε
  have h2 := hasSubgaussianMGF_neg_id_gaussianReal_zero_one.measure_ge_le hε
  simp only [id] at h1
  have hle := measureReal_union_le (μ := gaussianReal 0 1) {x : ℝ | ε ≤ x} {x : ℝ | ε ≤ -x}
  have hcalc : Real.exp (-ε ^ 2 / (2 * (1:NNReal))) = Real.exp (-ε ^ 2 / 2) := by norm_num
  rw [hcalc] at h1 h2
  calc
    (gaussianReal 0 1).real ({x : ℝ | ε ≤ x} ∪ {x : ℝ | ε ≤ -x}) ≤
        (gaussianReal 0 1).real {x : ℝ | ε ≤ x} + (gaussianReal 0 1).real {x : ℝ | ε ≤ -x} := hle
    _ ≤ Real.exp (-ε ^ 2 / 2) + Real.exp (-ε ^ 2 / 2) := add_le_add h1 h2
    _ = 2 * Real.exp (-ε ^ 2 / 2) := by ring

/-- Transport the two-sided tail bound to a single readout coordinate `a i`. -/
lemma prob_abs_gaussianReadout_coord_ge_le (n : ℕ) (i : Fin n) (ε : ℝ) (hε : 0 ≤ ε) :
    (gaussianReadoutMeasure n).real {a : Fin n → ℝ | ε ≤ |a i|} ≤ 2 * Real.exp (-ε ^ 2 / 2) := by
  have hmap : Measure.map (fun a : Fin n → ℝ => a i) (gaussianReadoutMeasure n) =
      gaussianReal 0 1 := map_gaussianReadoutMeasure_coord i
  have hpre : {a : Fin n → ℝ | ε ≤ |a i|} =
      (fun a : Fin n → ℝ => a i) ⁻¹' {x : ℝ | ε ≤ |x|} := rfl
  have hms : MeasurableSet {x : ℝ | ε ≤ |x|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hkey : (gaussianReadoutMeasure n).real
      ((fun a : Fin n → ℝ => a i) ⁻¹' {x : ℝ | ε ≤ |x|}) =
      (gaussianReal 0 1).real {x : ℝ | ε ≤ |x|} := by
    unfold MeasureTheory.Measure.real
    rw [← Measure.map_apply (measurable_pi_apply i) hms, hmap]
  rw [hpre, hkey]
  exact prob_abs_gaussianReal_ge_le ε hε

/-- Union bound over all `n` readout coordinates: the probability that *some* coordinate exceeds
`ε` in absolute value is at most `2n` times the single-coordinate tail bound. -/
theorem prob_max_abs_gaussianReadout_ge_le (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    (gaussianReadoutMeasure n).real {a : Fin n → ℝ | ∃ i, ε ≤ |a i|} ≤
      2 * (n : ℝ) * Real.exp (-ε ^ 2 / 2) := by
  have heq : {a : Fin n → ℝ | ∃ i, ε ≤ |a i|} = ⋃ i : Fin n, {a : Fin n → ℝ | ε ≤ |a i|} := by
    ext a; simp
  rw [heq]
  calc
    (gaussianReadoutMeasure n).real (⋃ i : Fin n, {a : Fin n → ℝ | ε ≤ |a i|}) ≤
        ∑ i : Fin n, (gaussianReadoutMeasure n).real {a : Fin n → ℝ | ε ≤ |a i|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin n, 2 * Real.exp (-ε ^ 2 / 2) :=
      Finset.sum_le_sum (fun i _ => prob_abs_gaussianReadout_coord_ge_le n i ε hε)
    _ = 2 * (n : ℝ) * Real.exp (-ε ^ 2 / 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- **Gap 4b deliverable.** With probability `≥ 1 - δ`, every readout weight `a i` has
`|a i| ≤ √(2 log(2n/δ))` - a bound that grows only **logarithmically** in the width `n`. -/
theorem prob_forall_abs_gaussianReadout_le (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    (gaussianReadoutMeasure n).real
      {a : Fin n → ℝ | ∀ i, |a i| ≤ Real.sqrt (2 * Real.log (2 * n / δ))} ≥ 1 - δ := by
  set ε : ℝ := Real.sqrt (2 * Real.log (2 * n / δ)) with hε_def
  have hnδ_pos : 0 < 2 * (n : ℝ) / δ := by positivity
  have hε_nonneg : 0 ≤ ε := Real.sqrt_nonneg _
  have hbad := prob_max_abs_gaussianReadout_ge_le n ε hε_nonneg
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.mpr hn
  have hlog_nonneg : 0 ≤ Real.log (2 * (n:ℝ) / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    nlinarith
  have hε_sq : ε ^ 2 = 2 * Real.log (2 * (n:ℝ) / δ) := by
    rw [hε_def, Real.sq_sqrt (by positivity)]
  have hexp : Real.exp (-ε ^ 2 / 2) = δ / (2 * n) := by
    rw [hε_sq]
    rw [show -(2 * Real.log (2 * (n:ℝ) / δ)) / 2 = -Real.log (2 * (n:ℝ) / δ) by ring]
    rw [Real.exp_neg, Real.exp_log hnδ_pos]
    rw [inv_div]
  rw [hexp] at hbad
  have hrhs : 2 * (n:ℝ) * (δ / (2 * (n:ℝ))) = δ := by field_simp
  rw [hrhs] at hbad
  have hcompl : {a : Fin n → ℝ | ∀ i, |a i| ≤ ε} = {a : Fin n → ℝ | ∃ i, ε < |a i|} ᶜ := by
    ext a
    simp [not_exists, not_lt]
  rw [hcompl]
  have hsub : {a : Fin n → ℝ | ∃ i, ε < |a i|} ⊆ {a : Fin n → ℝ | ∃ i, ε ≤ |a i|} :=
    fun a ⟨i, hi⟩ => ⟨i, hi.le⟩
  have hle := measureReal_mono (μ := gaussianReadoutMeasure n) hsub
  have hbad' : (gaussianReadoutMeasure n).real {a : Fin n → ℝ | ∃ i, ε < |a i|} ≤ δ :=
    hle.trans hbad
  have hcompl_ge : (gaussianReadoutMeasure n).real ({a : Fin n → ℝ | ∃ i, ε < |a i|} ᶜ) ≥
      1 - δ := by
    have hUn : {a : Fin n → ℝ | ∃ i, ε < |a i|} = ⋃ i : Fin n, {a : Fin n → ℝ | ε < |a i|} := by
      ext a; simp
    have hmeas : MeasurableSet {a : Fin n → ℝ | ∃ i, ε < |a i|} := by
      rw [hUn]
      exact MeasurableSet.iUnion (fun i => measurableSet_lt measurable_const
        (continuous_abs.measurable.comp (measurable_pi_apply i)))
    have := probReal_compl_eq_one_sub (μ := gaussianReadoutMeasure n)
      (s := {a : Fin n → ℝ | ∃ i, ε < |a i|}) hmeas
    rw [ge_iff_le, this]
    linarith
  exact hcompl_ge

/-- **Generic, reusable union-bound-for-complements.** Two events each of probability `≥ 1 - δ`
on the same probability measure intersect in an event of probability `≥ 1 - δ₁ - δ₂`. Used by
Phase 6 (`NTK.Training.TwoLayer.KernelFreeze`) to combine Gap 3's Jacobian-norm event with Gap 4b's
entrywise-readout event, but stated with no reference to the NTK setup so it can be reused for
any future combination of independent high-probability events. -/
theorem measureReal_inter_ge_of_ge {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {δ₁ δ₂ : ℝ} (hA' : μ.real A ≥ 1 - δ₁) (hB' : μ.real B ≥ 1 - δ₂) :
    μ.real (A ∩ B) ≥ 1 - δ₁ - δ₂ := by
  have hcompl : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := Set.compl_inter A B
  have h1 : μ.real ((A ∩ B)ᶜ) = 1 - μ.real (A ∩ B) := probReal_compl_eq_one_sub (hA.inter hB)
  have h2 : μ.real (Aᶜ ∪ Bᶜ) ≤ μ.real Aᶜ + μ.real Bᶜ := measureReal_union_le Aᶜ Bᶜ
  have h3 : μ.real Aᶜ = 1 - μ.real A := probReal_compl_eq_one_sub hA
  have h4 : μ.real Bᶜ = 1 - μ.real B := probReal_compl_eq_one_sub hB
  rw [hcompl] at h1
  linarith [h1, h2, h3, h4]

/-- The complement of an intersection has measure at most the sum of the complements' measures.
No measurability is needed. -/
theorem measureReal_compl_inter_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (A B : Set α) :
    μ.real (A ∩ B)ᶜ ≤ μ.real Aᶜ + μ.real Bᶜ := by
  rw [Set.compl_inter]
  exact measureReal_union_le _ _

/-- On a probability measure, `1 - μ Sᶜ ≤ μ S` for an arbitrary (possibly non-measurable) `S`. -/
theorem one_sub_le_measureReal_of_measureReal_compl_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {S : Set α} {c : ℝ} (h : μ.real Sᶜ ≤ c) :
    1 - c ≤ μ.real S := by
  have h1 := measureReal_union_le (μ := μ) S Sᶜ
  rw [Set.union_compl_self] at h1
  have h2 : μ.real Set.univ = 1 := by simp
  linarith

/-- Lift Gap 4b's readout-only event to the full initialization product measure
`initMeasure n d = (gaussianInit n d).prod (gaussianReadoutMeasure n)`. -/
lemma initMeasure_forall_abs_readout_ge (n d : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    (initMeasure n d).real
      {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
        ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ))} ≥ 1 - δ := by
  have hset : {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
      ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ))} =
      Set.univ ×ˢ {a : Fin n → ℝ | ∀ i, |a i| ≤ Real.sqrt (2 * Real.log (2 * n / δ))} := by
    ext p; simp
  rw [hset, initMeasure, MeasureTheory.measureReal_prod_prod]
  simpa using prob_forall_abs_gaussianReadout_le n hn hδ hδ1

/-- Readout weights `a_i` are mutually independent across hidden units `i ∈ Fin n`. -/
lemma iIndepFun_readoutWeights (n : ℕ) :
    iIndepFun (fun i : Fin n => fun a : Fin n → ℝ => a i) (gaussianReadoutMeasure n) :=
  iIndepFun_pi (fun _ => aemeasurable_id)

/-- Input weight rows `W_i` have marginal standard Gaussian row distribution `𝒩(0, Iᵈ)`. -/
lemma map_gaussianInit_row (i : Fin n) :
    Measure.map (fun W : Fin n → Fin d → ℝ => W i) (gaussianInit n d) = gaussianRowMeasure d :=
  (MeasureTheory.measurePreserving_eval (fun _ : Fin n => gaussianRowMeasure d) i).map_eq

/-- Input weight rows `W_i` are mutually independent across hidden unit indices `i ∈ Fin n`. -/
lemma iIndepFun_inputWeights (n d : ℕ) :
    iIndepFun (fun i : Fin n => fun W : Fin n → Fin d → ℝ => W i) (gaussianInit n d) :=
  iIndepFun_pi (fun _ => aemeasurable_id)

/-- Mutual Independence: the family of input weights `W` is independent of readout weights `a`. -/
lemma indepFun_input_readout (n d : ℕ) :
    IndepFun (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => p.1)
      (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => p.2)
      (initMeasure n d) :=
  indepFun_prod measurable_id measurable_id

end Preliminaries

end NTK

end
