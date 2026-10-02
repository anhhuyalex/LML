/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Initialization.CovariancePropagation

/-!
# Theorem 2.13 (deep NNGP recursion): construction and lemmas

The depth-`L` network construction, general convergence-in-probability lemmas, and the
continuity of the covariance-update map.

## Main results and proof outline

* `NTK.deepPreactivation` : the recursive pre-activation family $h_1, \dots, h_L$ of a depth-$L$
  MLP, built from a single infinite population of i.i.d. standard Gaussian weights.
* `NTK.indepFun_deepLayer_history` : Independence Across Depth for this population (the
  infinite-population analogue of `NTK.indepFun_layer_history`).
* `NTK.instPseudoEMetricSpaceMatrix` : the missing `PseudoEMetricSpace (Matrix (Fin m) (Fin m) ℝ)`
  glue instance (Mathlib deliberately does not register one directly, to avoid a diamond with
  other matrix norms), needed for the lemma below.
* `NTK.tendstoInMeasure_comp_of_continuousAt`,
  `NTK.tendsto_integral_of_tendstoInMeasure_of_bounded` : general-purpose
  convergence-in-probability lemmas (continuous mapping to a constant limit; bounded convergence)
  missing from Mathlib's `ConvergenceInMeasure` API, needed by the theorems below.
* `NTK.continuousWithinAt_covarianceMap` : continuity of the covariance-update map
  $\mathcal{C}_\varphi$ on the positive-semidefinite cone, including its singular boundary.

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

section DeepNNGPRecursion

/-! ## Theorem 2.13 (Deep NNGP Recursion)

This section assembles the single-layer-transition machinery above
(`layerCovarianceSeq`, `exact_conditional_normality_general_multivariate`,
`conditional_empiricalCovariance_tendstoInMeasure_layerCovarianceSeq`) into an actual depth-`L`
network with real weight matrices chained together at every layer, and proves that its empirical
covariance converges layer by layer (Part 1) and that its output converges in distribution to the
NNGP limit (Part 2).  The final theorem statements and full proof narratives are given in the
second `DeepNNGPRecursion` section later in this file; this section contains the network
construction and the supporting lemmas it needs.

Following the recursive pre-activation family `deepPreactivation` below, the per-layer empirical
covariance and the joint initialization measure are both written out inline at each point of use
(rather than named as separate definitions) to avoid adding more top-level declarations to an
already-large file: the empirical covariance of a width-`n` post-activation family
`H : Fin n → Fin m → ℝ` is `fun α β => (n:ℝ)⁻¹ * ∑ j, φ (H j α) * φ (H j β)` (the same formula
already inlined throughout `AsymptoticEmpiricalCovariancePropagation`, e.g. in
`conditional_preactivations_eq_pi`), and the joint initialization measure of a depth-`L` network is
`(Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
gaussianReal 0 1).prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)` (as in
`indepFun_deepLayer_history` below).

The covariance update is continuous relative to `PosSemidef`, including the singular boundary;
see `continuousWithinAt_covarianceMap` below.
-/

/-! ### Depth-`L` Network Construction -/

/-- The recursive pre-activation family `h_1, …, h_L` of a depth-`L` MLP with input dimension `d`,
uniform hidden width, activation `φ`, and evaluation inputs `X`.

`W : ℕ → ℕ → ℕ → ℝ` is a single infinite population of i.i.d. standard Gaussian weights, indexed by
`(layer, neuron, source-neuron)`: layer `0` (restricted to its first `d` "columns") plays the role
of the input weight matrix `W₀`, and layer `ℓ + 1` (restricted to its first `n` columns) plays the
role of the `(ℓ+1)`-th hidden-to-hidden weight matrix.  Folding the input layer into the *same*
uniform population as the hidden layers (rather than giving it a separate type/measure) is what
lets `indepFun_deepLayer_history` below supply independence for *every* layer transition, including
the first, via a single application of `iIndepFun_pi` — avoiding the need to separately combine
independence facts across two differently-shaped blocks.

`n` is the width cutoff used at every hidden layer; sending `n → ∞` over a single fixed probability
space (rather than building a different space per width) is the same device already used for
`Measure.infinitePi` throughout this file, e.g. in `empiricalCovariance_tendsto_limitingCovariance`.

Indexing starts at `0` so that `deepPreactivation … 0 = h_1` and, matching `layerCovarianceSeq`'s
own `0`-indexed recursion, the empirical covariance of `deepPreactivation … ℓ` is the quantity that
converges to `layerCovarianceSeq 1 0 φ m Φ0 (ℓ + 1)`. -/
noncomputable def deepPreactivation (d m n : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (W : ℕ → ℕ → ℕ → ℝ) : ℕ → Fin m → Fin n → ℝ
  | 0 => fun α j => (d : ℝ)⁻¹.sqrt * ((fun k : Fin d => W 0 j.val k.val) ⬝ᵥ X α)
  | ℓ + 1 => fun α j => (n : ℝ)⁻¹.sqrt * ∑ k : Fin n,
      W (ℓ + 1) j.val k.val * φ (deepPreactivation d m n φ X W ℓ α k)

/-- A preactivation at layer `ℓ` depends only on weight populations at indices at most `ℓ`.
This is the deterministic bridge from the finite earlier-layer history in
`indepFun_deepLayer_history` back to `deepPreactivation`. -/
lemma deepPreactivation_congr_of_eqOn (d m n : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (W W' : ℕ → ℕ → ℕ → ℝ) (ℓ : ℕ)
    (hW : ∀ k : ℕ, k ≤ ℓ → W k = W' k) :
    deepPreactivation d m n φ X W ℓ = deepPreactivation d m n φ X W' ℓ := by
  induction ℓ with
  | zero =>
      simp only [deepPreactivation]
      rw [hW 0 le_rfl]
  | succ ℓ ih =>
      simp only [deepPreactivation]
      rw [hW (ℓ + 1) le_rfl]
      apply funext
      intro α
      apply funext
      intro j
      apply congrArg (fun q : Fin n → ℝ => (n : ℝ)⁻¹.sqrt * ∑ k : Fin n,
        W' (ℓ + 1) j.val k.val * φ (q k))
      apply funext
      intro k
      exact congrFun (congrFun (ih fun r hr => hW r (Nat.le_succ_of_le hr)) α) k

/-- Truncating the weight population to its first `D` layers (zero afterwards) does not change the
preactivations at layers `ℓ < D`. This is the bridge from the `ℕ`-indexed tensor of
`DeepMLPParams.ofTensor` to the `Fin D`-indexed population. -/
lemma deepPreactivation_eq_prefix (d m n D : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (W : ℕ → ℕ → ℕ → ℝ) (ℓ : ℕ) (hℓ : ℓ < D) :
    deepPreactivation d m n φ X W ℓ =
      deepPreactivation d m n φ X (fun k => if _h : k < D then W k else 0) ℓ :=
  deepPreactivation_congr_of_eqOn d m n φ X _ _ ℓ fun r hr => by
    simp [show r < D by omega]

/-- The infinite input-weight population, evaluated at the fixed inputs and normalized by the
input dimension, is an i.i.d. family of centered Gaussians with the base Gram covariance. This
is the distributional bridge needed for the base case of the deep covariance induction. -/
lemma map_infinitePi_input_preactivations (d m : ℕ) (X : Fin m → Fin d → ℝ) :
    Measure.map
      (fun W : ℕ → ℕ → ℝ => fun j : ℕ => WithLp.toLp 2 fun α : Fin m =>
        (d : ℝ)⁻¹.sqrt * ∑ k : Fin d, W j k.val * X α k)
      (Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
      Measure.infinitePi fun _ : ℕ =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) := by
  let restrictRows : (ℕ → ℕ → ℝ) → (ℕ → Fin d → ℝ) :=
    fun W j k => W j k.val
  have hrestrictRows_meas : Measurable restrictRows := by
    refine measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun k => ?_
    exact (measurable_pi_apply k.val).comp (measurable_pi_apply j)
  have hrestrictRows :
      Measure.map restrictRows
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
      Measure.infinitePi fun _ : ℕ => gaussianReadoutMeasure d := by
    calc
      Measure.map restrictRows
          (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
        Measure.infinitePi fun _ : ℕ =>
          Measure.map (fun r : ℕ → ℝ => fun k : Fin d => r k.val)
            (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) := by
          simpa [restrictRows] using
            (Measure.infinitePi_map_pi
              (μ := fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
              (f := fun _ (r : ℕ → ℝ) (k : Fin d) => r k.val)
              (fun _ => measurable_pi_iff.2 fun k => measurable_pi_apply k.val))
      _ = Measure.infinitePi fun _ : ℕ => gaussianReadoutMeasure d := by
        congr 1
        funext j
        rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,
          Measure.infinitePi_eq_pi]
  let u : Fin m → Fin d → ℝ := fun α k => (d : ℝ)⁻¹.sqrt * X α k
  let projectRows : (ℕ → Fin d → ℝ) → (ℕ → EuclideanSpace ℝ (Fin m)) :=
    fun W j => WithLp.toLp 2 fun α => W j ⬝ᵥ u α
  have hprojectRows_meas : Measurable projectRows := by
    refine measurable_pi_iff.2 fun j => ?_
    apply (PiLp.continuous_toLp 2 _).measurable.comp
    refine measurable_pi_iff.2 fun α => ?_
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun k _ =>
      ((measurable_pi_apply k).comp (measurable_pi_apply j)).mul_const _
  have hprojectRows :
      Measure.map projectRows (Measure.infinitePi fun _ : ℕ => gaussianReadoutMeasure d) =
      Measure.infinitePi fun _ : ℕ =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) := by
    calc
      Measure.map projectRows (Measure.infinitePi fun _ : ℕ => gaussianReadoutMeasure d) =
        Measure.infinitePi fun _ : ℕ => Measure.map
          (fun r : Fin d → ℝ => WithLp.toLp 2 fun α => r ⬝ᵥ u α)
          (gaussianReadoutMeasure d) := by
          simpa [projectRows] using
            (Measure.infinitePi_map_pi
              (μ := fun _ : ℕ => gaussianReadoutMeasure d)
              (f := fun _ (r : Fin d → ℝ) => WithLp.toLp 2 fun α => r ⬝ᵥ u α)
              (fun _ => (PiLp.continuous_toLp 2 _).measurable.comp
                (continuous_pi fun α => by fun_prop).measurable))
      _ = Measure.infinitePi fun _ : ℕ =>
          multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
            (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) := by
        apply congrArg Measure.infinitePi
        funext j
        have hcov : (Matrix.of fun α β : Fin m => u α ⬝ᵥ u β) =
            (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) := by
          ext α β
          change (∑ k : Fin d, (d : ℝ)⁻¹.sqrt * X α k *
            ((d : ℝ)⁻¹.sqrt * X β k)) = (d : ℝ)⁻¹ * ∑ k : Fin d, X α k * X β k
          have hroot : (d : ℝ)⁻¹.sqrt * (d : ℝ)⁻¹.sqrt = (d : ℝ)⁻¹ :=
            Real.mul_self_sqrt (by positivity)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by
            rw [show (d : ℝ)⁻¹.sqrt * X α k * ((d : ℝ)⁻¹.sqrt * X β k) =
              ((d : ℝ)⁻¹.sqrt * (d : ℝ)⁻¹.sqrt) * (X α k * X β k) by ring, hroot]
        rw [stdGaussian_inner_family, hcov]
  have hcomp : projectRows ∘ restrictRows =
      fun W : ℕ → ℕ → ℝ => fun j : ℕ => WithLp.toLp 2 fun α : Fin m =>
        (d : ℝ)⁻¹.sqrt * ∑ k : Fin d, W j k.val * X α k := by
    funext W j
    simp only [Function.comp_apply, projectRows, restrictRows]
    congr 1
    funext α
    simp only [u, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [← hcomp, ← Measure.map_map hprojectRows_meas hrestrictRows_meas, hrestrictRows, hprojectRows]

/-- **Independence Across Depth**, for the uniform `Fin L → ℕ → ℕ → ℝ` layer population feeding
`deepPreactivation`.  This is the infinite-population analogue of `indepFun_layer_history`
(`NTK.Initialization.Peripheral`); the proof is identical (`iIndepFun_pi` is generic in the per-index
measurable space and measure), only the per-layer type changes from the finite-width
`Fin n → Fin d → ℝ` to the infinite-population `ℕ → ℕ → ℝ`. -/
theorem indepFun_deepLayer_history (L : ℕ) (ℓ : Fin L) :
    IndepFun (fun ω : Fin L → ℕ → ℕ → ℝ => ω ℓ)
      (fun ω : Fin L → ℕ → ℕ → ℝ => fun i : Finset.Iio ℓ => ω i)
      (Measure.pi (fun _ : Fin L =>
        Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) := by
  have h_indep : iIndepFun (fun ℓ : Fin L => fun ω : Fin L → ℕ → ℕ → ℝ => ω ℓ)
      (Measure.pi (fun _ : Fin L =>
        Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) :=
    iIndepFun_pi (fun _ => aemeasurable_id)
  have h_meas : ∀ i : Fin L, Measurable (fun ω : Fin L → ℕ → ℕ → ℝ => ω i) :=
    fun i => measurable_pi_apply i
  have h_disj : Disjoint ({ℓ} : Finset (Fin L)) (Finset.Iio ℓ) :=
    Finset.disjoint_singleton_left.2 (by simp)
  have h := h_indep.indepFun_finset {ℓ} (Finset.Iio ℓ) h_disj h_meas
  exact h.comp (measurable_pi_apply (⟨ℓ, Finset.mem_singleton_self ℓ⟩ :
    ({ℓ} : Finset (Fin L)))) measurable_id

/-- The current infinite weight population is independent of all earlier populations.  This
pushforward form is the measure-theoretic interface used by the deep covariance induction: it
separates the fresh layer weights from the history without introducing a second network state. -/
lemma map_deepLayer_history_eq_prod (L : ℕ) (ℓ : Fin L) :
    Measure.map
      (fun w : Fin L → ℕ → ℕ → ℝ => (w ℓ, fun i : Finset.Iio ℓ => w i))
      (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
        (Measure.map (fun w : Fin L → ℕ → ℕ → ℝ => fun i : Finset.Iio ℓ => w i)
          (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
            Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) := by
  have hhistory_meas : Measurable
      (fun w : Fin L → ℕ → ℕ → ℝ => fun i : Finset.Iio ℓ => w i) := by
    refine measurable_pi_iff.2 fun i => ?_
    exact measurable_pi_apply (i : Fin L)
  rw [(indepFun_deepLayer_history L ℓ).map_prod_eq_prod_map_map]
  · rw [(measurePreserving_eval (fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
      Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) ℓ).map_eq]
  · exact (measurable_pi_apply ℓ).aemeasurable
  · exact hhistory_meas.aemeasurable

/-- The total weight family reconstructed from the populations strictly before `r`.  Values at
and after `r` are irrelevant for preactivations before `r` and are set to zero. -/
noncomputable def deepHistoryWeight (L : ℕ) (r : Fin L)
    (h : Finset.Iio r → ℕ → ℕ → ℝ) : ℕ → ℕ → ℕ → ℝ := fun k =>
  if hk : k < r.val then
    h ⟨⟨k, lt_trans hk r.isLt⟩, Finset.mem_Iio.mpr (show (⟨k, lt_trans hk r.isLt⟩ : Fin L) < r
      from hk)⟩
  else 0

/-- A preactivation before `r` depends only on the `Iio r` history. -/
lemma deepPreactivation_eq_deepHistoryWeight
    (d m n L : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (r : Fin L) (ℓ : ℕ) (hℓ : ℓ < r.val)
    (w : Fin L → ℕ → ℕ → ℝ) :
    deepPreactivation d m n φ X
      (fun k => if hk : k < L then w ⟨k, hk⟩ else 0) ℓ =
    deepPreactivation d m n φ X (deepHistoryWeight L r (fun i : Finset.Iio r => w i)) ℓ := by
  apply deepPreactivation_congr_of_eqOn d m n φ X _ _ ℓ
  intro k hk
  have hkr : k < r.val := lt_of_le_of_lt hk hℓ
  simp [deepHistoryWeight, hkr, lt_trans hkr r.isLt]

/-! ### General-Purpose Convergence-in-Probability Lemmas

The two lemmas below are genuinely general (not NTK-specific): they are missing pieces of
`Mathlib.MeasureTheory.Function.ConvergenceInMeasure`'s API that the induction and the final
characteristic-function argument in the second `DeepNNGPRecursion` section both need. Neither is
hard to prove — they are direct consequences of tools already in this Mathlib checkout
(`EMetric.continuousAt_iff`, `TendstoInMeasure.exists_seq_tendsto_ae`,
`tendsto_of_subseq_tendsto`) — but Mathlib itself does not compose `TendstoInMeasure` with a
continuous map of the codomain, nor with dominated convergence of integrals, so both are proved
from scratch here.
-/

/-- `Matrix` inherits its `PseudoEMetricSpace` structure from the underlying Pi type. Mathlib does
not register this instance directly for `Matrix` (to avoid a diamond with other norms such as the
operator or Frobenius norm — `Matrix` is a `def`, not `abbrev`, over `m → n → α`, so instance
search does not unfold it automatically), so it is registered here. Needed so
`tendstoInMeasure_comp_of_continuousAt` below applies to the `Matrix`-valued sequences in Part 1
and Part 2. -/
instance instPseudoEMetricSpaceMatrix (m : ℕ) : PseudoEMetricSpace (Matrix (Fin m) (Fin m) ℝ) := by
  unfold Matrix; infer_instance

/-- The matching pseudo-metric instance is needed for the real-valued `dist` tail events used in
convergence-in-measure statements.  As above, it is inherited from the underlying finite Pi type. -/
instance instPseudoMetricSpaceMatrix (m : ℕ) : PseudoMetricSpace (Matrix (Fin m) (Fin m) ℝ) := by
  unfold Matrix; infer_instance

/-- **Continuous mapping theorem for convergence in probability to a constant.** If `f n → y` in
probability and `g` is continuous at `y`, then `g ∘ f n → g y` in probability. Used below to turn
the inductive hypothesis `Φ_ℓ^{(n)} → Φ_ℓ` into `𝒞_φ(Φ_ℓ^{(n)}) → 𝒞_φ(Φ_ℓ)`. -/
theorem tendstoInMeasure_comp_of_continuousAt
    {α E F : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [PseudoEMetricSpace E] [PseudoEMetricSpace F] {f : ℕ → α → E} {y : E} {g : E → F}
    (hfg : TendstoInMeasure μ f Filter.atTop (fun _ => y)) (hg : ContinuousAt g y) :
    TendstoInMeasure μ (fun n a => g (f n a)) Filter.atTop (fun _ => g y) := by
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := EMetric.continuousAt_iff.mp hg ε hε
  have hmono : ∀ n, μ {a | ε ≤ edist (g (f n a)) (g y)} ≤ μ {a | δ ≤ edist (f n a) y} := by
    intro n
    refine measure_mono fun a ha => ?_
    simp only [Set.mem_ofPred_eq] at ha ⊢
    by_contra hlt
    push Not at hlt
    exact absurd (hδg hlt) (not_lt.mpr ha)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hfg δ hδ)
    (fun _ => zero_le) hmono

/-- **Inverse of a convergent matrix sequence.** If `f n → M` in probability and `M` is invertible,
then `(f n)⁻¹ → M⁻¹` in probability: inversion is `det⁻¹ • adjugate`, continuous where `det ≠ 0`.
With the positive-definite limiting kernels of the deep NTK this yields
`‖Σ̂ₙ⁻¹‖ = O_ℙ(1)` for the empirical activation Gram. -/
theorem tendstoInMeasure_matrix_inv {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {m : ℕ}
    {f : ℕ → α → Matrix (Fin m) (Fin m) ℝ} {M : Matrix (Fin m) (Fin m) ℝ}
    (hf : TendstoInMeasure μ f Filter.atTop (fun _ => M)) (hM : IsUnit M.det) :
    TendstoInMeasure μ (fun n a => (f n a)⁻¹) Filter.atTop (fun _ => M⁻¹) := by
  refine tendstoInMeasure_comp_of_continuousAt
    (g := fun A : Matrix (Fin m) (Fin m) ℝ => A⁻¹) hf ?_
  refine continuousAt_matrix_inv M ?_
  simp only [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ hM.ne_zero

/-- Positive-definite version of `tendstoInMeasure_matrix_inv`. -/
theorem tendstoInMeasure_matrix_inv_of_posDef {α : Type*} {mα : MeasurableSpace α}
    {μ : Measure α} {m : ℕ} {f : ℕ → α → Matrix (Fin m) (Fin m) ℝ}
    {M : Matrix (Fin m) (Fin m) ℝ}
    (hf : TendstoInMeasure μ f Filter.atTop (fun _ => M)) (hM : M.PosDef) :
    TendstoInMeasure μ (fun n a => (f n a)⁻¹) Filter.atTop (fun _ => M⁻¹) :=
  tendstoInMeasure_matrix_inv hf (isUnit_iff_ne_zero.mpr hM.det_pos.ne')

/-- **Continuous mapping on an invariant set.** If `f n → y` in probability, all values of `f`
lie in `s`, and `g` is continuous at `y` relative to `s`, then `g ∘ f n → g y` in probability.
This is the form needed for covariance matrices: `multivariateGaussian` is naturally continuous in
its covariance only on the positive-semidefinite cone. -/
theorem tendstoInMeasure_comp_of_continuousWithinAt
    {α E F : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [PseudoEMetricSpace E] [PseudoEMetricSpace F] {f : ℕ → α → E} {y : E} {g : E → F}
    {s : Set E} (hfg : TendstoInMeasure μ f Filter.atTop (fun _ => y))
    (hf : ∀ n a, f n a ∈ s) (hg : ContinuousWithinAt g s y) :
    TendstoInMeasure μ (fun n a => g (f n a)) Filter.atTop (fun _ => g y) := by
  intro ε hε
  obtain ⟨δ, hδ, hδg⟩ := EMetric.continuousWithinAt_iff.mp hg ε hε
  have hmono : ∀ n, μ {a | ε ≤ edist (g (f n a)) (g y)} ≤ μ {a | δ ≤ edist (f n a) y} := by
    intro n
    refine measure_mono fun a ha => ?_
    simp only [Set.mem_ofPred_eq] at ha ⊢
    by_contra hlt
    push Not at hlt
    exact absurd (hδg (hf n a) hlt) (not_lt.mpr ha)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hfg δ hδ)
    (fun _ => zero_le) hmono

/-- A two-stage convergence-in-probability argument.  If `f n` is close in probability to a
possibly `n`-dependent intermediate approximation `g n`, and `g n` converges in probability to
`h`, then `f n` converges in probability to `h`.  The deep covariance induction uses this after
separating the fresh-layer empirical fluctuation from the deterministic covariance update. -/
theorem tendstoInMeasure_trans
    {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [PseudoMetricSpace E] {f g : ℕ → α → E} {h : α → E}
    (hfg : ∀ ε : ℝ, 0 < ε →
      Filter.Tendsto (fun n => μ {a | ε ≤ dist (f n a) (g n a)}) Filter.atTop (nhds 0))
    (hgh : TendstoInMeasure μ g Filter.atTop h) :
    TendstoInMeasure μ f Filter.atTop h := by
  rw [tendstoInMeasure_iff_dist] at hgh ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := by linarith
  have hsum := (hfg (ε / 2) hhalf).add (hgh (ε / 2) hhalf)
  have hmono : ∀ n, μ {a | ε ≤ dist (f n a) (h a)} ≤
      μ {a | ε / 2 ≤ dist (f n a) (g n a)} +
        μ {a | ε / 2 ≤ dist (g n a) (h a)} := by
    intro n
    calc
      μ {a | ε ≤ dist (f n a) (h a)} ≤
          μ ({a | ε / 2 ≤ dist (f n a) (g n a)} ∪
            {a | ε / 2 ≤ dist (g n a) (h a)}) := by
        apply measure_mono
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        by_cases hfg' : ε / 2 ≤ dist (f n a) (g n a)
        · exact Or.inl hfg'
        · right
          by_contra hgh'
          have hfg_lt : dist (f n a) (g n a) < ε / 2 := lt_of_not_ge hfg'
          have hgh_lt : dist (g n a) (h a) < ε / 2 := lt_of_not_ge hgh'
          have hlt : dist (f n a) (h a) < ε := by
            calc
              dist (f n a) (h a) ≤ dist (f n a) (g n a) + dist (g n a) (h a) :=
                dist_triangle _ _ _
              _ < ε / 2 + ε / 2 := add_lt_add hfg_lt hgh_lt
              _ = ε := by ring
          exact (not_lt_of_ge ha) hlt
      _ ≤ μ {a | ε / 2 ≤ dist (f n a) (g n a)} +
          μ {a | ε / 2 ≤ dist (g n a) (h a)} := measure_union_le _ _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using hsum)
    (fun _ => zero_le) hmono

/-- **Coordinatewise convergence in measure implies joint convergence** for a finite family. -/
theorem tendstoInMeasure_pi {Ω ι : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {E : ι → Type*} [∀ i, PseudoMetricSpace (E i)] {f : ℕ → Ω → ∀ i, E i} {c : ∀ i, E i}
    (h : ∀ i, TendstoInMeasure μ (fun n a => f n a i) Filter.atTop (fun _ => c i)) :
    TendstoInMeasure μ f Filter.atTop (fun _ => c) := by
  simp_rw [tendstoInMeasure_iff_dist] at h
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hsum : Filter.Tendsto (fun n => ∑ i, μ {a | ε ≤ dist (f n a i) (c i)}) Filter.atTop (nhds 0) := by
    simpa using tendsto_finsetSum (s := Finset.univ)
      (f := fun i n => μ {a | ε ≤ dist (f n a i) (c i)}) (a := fun _ => 0) fun i _ => h i ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le) ?_
  intro n
  calc μ {a | ε ≤ dist (f n a) c}
      ≤ μ (⋃ i, {a | ε ≤ dist (f n a i) (c i)}) := by
        apply measure_mono
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha
        by_contra hne
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hne
        push Not at hne
        exact (not_lt_of_ge ha) ((dist_pi_lt_iff hε).2 hne)
    _ ≤ ∑ i, μ {a | ε ≤ dist (f n a i) (c i)} := measure_iUnion_fintype_le _ _

/-- **Sums of products of convergent families.** If `a i n → a∞ i` and `b i n → b∞ i` in measure
for each index `i` of a finite set, then `∑ i, a i n * b i n → ∑ i, a∞ i * b∞ i` in measure. -/
theorem tendstoInMeasure_sum_mul {Ω ι : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {a b : ι → ℕ → Ω → ℝ} {a' b' : ι → ℝ}
    (ha : ∀ i, TendstoInMeasure μ (a i) Filter.atTop (fun _ => a' i))
    (hb : ∀ i, TendstoInMeasure μ (b i) Filter.atTop (fun _ => b' i)) :
    TendstoInMeasure μ (fun n ω => ∑ i, a i n ω * b i n ω) Filter.atTop
      (fun _ => ∑ i, a' i * b' i) := by
  have hpair : TendstoInMeasure μ (fun n ω => (Sum.elim (fun i => a i n ω) (fun i => b i n ω) :
      ι ⊕ ι → ℝ)) Filter.atTop (fun _ => Sum.elim a' b') := by
    refine tendstoInMeasure_pi fun i => ?_
    cases i with
    | inl i => exact ha i
    | inr i => exact hb i
  have hcont : Continuous (fun v : ι ⊕ ι → ℝ => ∑ i, v (Sum.inl i) * v (Sum.inr i)) := by
    fun_prop
  simpa using tendstoInMeasure_comp_of_continuousAt hpair hcont.continuousAt
/-- **Products of convergent sequences.** If `a n → a'` and `b n → b'` in measure then
`a n * b n → a' * b'` in measure (the one-term case of `tendstoInMeasure_sum_mul`). -/
theorem tendstoInMeasure_mul {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {a b : ℕ → Ω → ℝ} {a' b' : ℝ}
    (ha : TendstoInMeasure μ a Filter.atTop (fun _ => a'))
    (hb : TendstoInMeasure μ b Filter.atTop (fun _ => b')) :
    TendstoInMeasure μ (fun n ω => a n ω * b n ω) Filter.atTop (fun _ => a' * b') := by
  simpa using tendstoInMeasure_sum_mul (ι := Unit) (a := fun _ => a) (b := fun _ => b)
    (a' := fun _ => a') (b' := fun _ => b') (fun _ => ha) (fun _ => hb)

/-- To prove convergence in measure of a finite matrix-valued family, it suffices to prove the
corresponding tail estimate for every entry.  The proof uses the sup metric on Pi types and finite
subadditivity of measure.  This is the matrix reduction used by the conditional covariance
concentration argument. -/
theorem tendsto_matrixTail_of_tendsto_entrywise
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} (m : ℕ)
    {f g : ℕ → Ω → Matrix (Fin m) (Fin m) ℝ}
    (hentry : ∀ (α β : Fin m) (ε : ℝ), 0 < ε →
      Filter.Tendsto (fun n => μ {a | ε ≤ dist (f n a α β) (g n a α β)})
        Filter.atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε →
      Filter.Tendsto (fun n => μ {a | ε ≤ dist (f n a) (g n a)})
        Filter.atTop (nhds 0) := by
  intro ε hε
  have hsum : Filter.Tendsto
      (fun n => ∑ q : Fin m × Fin m,
        μ {a | ε ≤ dist (f n a q.1 q.2) (g n a q.1 q.2)})
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_finsetSum
      (f := fun q : Fin m × Fin m => fun n =>
        μ {a | ε ≤ dist (f n a q.1 q.2) (g n a q.1 q.2)})
      (a := fun _ => 0) (s := Finset.univ)
      (fun q _ => hentry q.1 q.2 ε hε))
  have hbound : ∀ n : ℕ,
      μ {a | ε ≤ dist (f n a) (g n a)} ≤
        ∑ q : Fin m × Fin m, μ {a | ε ≤ dist (f n a q.1 q.2) (g n a q.1 q.2)} := by
    intro n
    calc
      μ {a | ε ≤ dist (f n a) (g n a)} ≤
          μ (⋃ q : Fin m × Fin m, {a | ε ≤ dist (f n a q.1 q.2) (g n a q.1 q.2)}) := by
        apply measure_mono
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha
        by_contra h
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at h
        push Not at h
        exact (not_lt_of_ge ha) ((dist_pi_lt_iff hε).2 fun α =>
          (dist_pi_lt_iff hε).2 fun β => h ⟨α, β⟩)
      _ ≤ ∑ q : Fin m × Fin m,
          μ {a | ε ≤ dist (f n a q.1 q.2) (g n a q.1 q.2)} :=
        measure_iUnion_fintype_le _ _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) hbound

/-- Convergence in probability is preserved by precomposition with a measure-preserving map.
The explicit measurability hypotheses make the result applicable to the finite-dimensional
covariance maps used below without relying on an implicit completion of the source measure. -/
theorem tendstoInMeasure_comp_measurePreserving
    {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ : Measure α} {ν : Measure β} [PseudoEMetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] {T : α → β} {f : ℕ → β → E} {g : β → E}
    (hfg : TendstoInMeasure ν f Filter.atTop g) (hT : MeasurePreserving T μ ν)
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g) :
    TendstoInMeasure μ (fun n a => f n (T a)) Filter.atTop (fun a => g (T a)) := by
  intro ε hε
  have hset : ∀ n, MeasurableSet {b | ε ≤ edist (f n b) (g b)} := fun n =>
    ((hf n).edist hg) measurableSet_Ici
  have heq : (fun n => μ {a | ε ≤ edist (f n (T a)) (g (T a))}) =
      fun n => ν {b | ε ≤ edist (f n b) (g b)} := by
    funext n
    change μ (T ⁻¹' {b | ε ≤ edist (f n b) (g b)}) = _
    rw [← hT.map_eq, Measure.map_apply hT.measurable (hset n)]
  rw [heq]
  exact hfg ε hε

/-- **Bounded convergence for convergence in probability.** If `f n → g` in probability and the
`f n` are uniformly bounded in norm by a constant, then `∫ f n → ∫ g`. Proof: given any
subsequence, `TendstoInMeasure.exists_seq_tendsto_ae` extracts a further a.e.-convergent
subsequence, along which the ordinary dominated convergence theorem gives convergence of the
integrals; since every subsequence has such a further convergent subsequence,
`tendsto_of_subseq_tendsto` closes the full sequence. Used below in place of Theorem 3's dominated
convergence step (`tendsto_charFun_outputMeasure`), since Part 1 below only supplies convergence in
probability, not the almost-sure convergence Theorem 3 had from Kolmogorov's SLLN. -/
theorem tendsto_integral_of_tendstoInMeasure_of_bounded
    {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℕ → α → E} {g : α → E}
    (hfg : TendstoInMeasure μ f Filter.atTop g)
    (hf_meas : ∀ n, AEStronglyMeasurable (f n) μ) (C : ℝ)
    (hf_bound : ∀ n, ∀ᵐ a ∂μ, ‖f n a‖ ≤ C) [IsFiniteMeasure μ] :
    Filter.Tendsto (fun n => ∫ a, f n a ∂μ) Filter.atTop (nhds (∫ a, g a ∂μ)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, -, hms_ae⟩ := (hfg.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  simpa using tendsto_integral_of_dominated_convergence (bound := fun _ => C)
    (fun k => hf_meas (ns (ms k))) (integrable_const C)
    (fun k => hf_bound (ns (ms k))) hms_ae

/-! ### Continuity of the Covariance-Update Map -/

section CovarianceMapContinuity

open scoped Matrix.Norms.L2Operator

/-- A coordinate of `toEuclideanCLM K z` is controlled by the operator norm of `K`, uniformly in
the coordinate index. This is the linear-algebra fact behind the dominating function used by
`continuousWithinAt_covarianceMap`'s dominated-convergence argument. -/
lemma abs_toEuclideanCLM_ofLp_le {m : ℕ} (K : Matrix (Fin m) (Fin m) ℝ)
    (z : EuclideanSpace ℝ (Fin m)) (α : Fin m) :
    |(toEuclideanCLM (𝕜 := ℝ) K z).ofLp α| ≤ ‖K‖ * ‖z‖ := by
  rw [← Real.norm_eq_abs]
  change ‖(toEuclideanCLM (𝕜 := ℝ) K z) α‖ ≤ ‖K‖ * ‖z‖
  calc
    ‖(toEuclideanCLM (𝕜 := ℝ) K z) α‖ ≤ ‖toEuclideanCLM (𝕜 := ℝ) K z‖ :=
      PiLp.norm_apply_le _ _
    _ ≤ ‖toEuclideanCLM (𝕜 := ℝ) K‖ * ‖z‖ :=
      (toEuclideanCLM (𝕜 := ℝ) K).le_opNorm z
    _ = ‖K‖ * ‖z‖ := by rw [l2_opNorm_toEuclideanCLM]

-- Polynomial-growth bound on a product `φ a * φ b`, given a common bound `r` on `|a|` and `|b|`.
-- Pure real-analysis; no measure theory or matrices involved.
private lemma abs_mul_le_of_polynomial_growth (φ : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C) (p : ℕ)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (a b r : ℝ) (hr : 0 ≤ r) (ha : |a| ≤ r) (hb : |b| ≤ r) :
    |φ a * φ b| ≤ 2 * C ^ 2 * (1 + r ^ (2 * p)) := by
  have hpa : |a| ^ p ≤ r ^ p := pow_le_pow_left₀ (abs_nonneg a) ha p
  have hpb : |b| ^ p ≤ r ^ p := pow_le_pow_left₀ (abs_nonneg b) hb p
  have hφa : |φ a| ≤ C * (1 + r ^ p) := by
    calc
      |φ a| ≤ C * (1 + |a| ^ p) := hφ_growth a
      _ ≤ C * (1 + r ^ p) := by gcongr
  have hφb : |φ b| ≤ C * (1 + r ^ p) := by
    calc
      |φ b| ≤ C * (1 + |b| ^ p) := hφ_growth b
      _ ≤ C * (1 + r ^ p) := by gcongr
  have hsquare : (1 + r ^ p) ^ 2 ≤ 2 * (1 + r ^ (2 * p)) := by
    have hpow : r ^ (2 * p) = (r ^ p) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    rw [hpow]
    nlinarith [sq_nonneg (r ^ p - 1)]
  calc
    |φ a * φ b| = |φ a| * |φ b| := abs_mul _ _
    _ ≤ (C * (1 + r ^ p)) * (C * (1 + r ^ p)) := by gcongr
    _ = C ^ 2 * (1 + r ^ p) ^ 2 := by ring
    _ ≤ C ^ 2 * (2 * (1 + r ^ (2 * p))) :=
      mul_le_mul_of_nonneg_left hsquare (sq_nonneg C)
    _ = 2 * C ^ 2 * (1 + r ^ (2 * p)) := by ring

/-- Rewrites the covariance integral against `multivariateGaussian 0 K` as an integral against the
fixed reference measure `stdGaussian`, with all `K`-dependence isolated in `CFC.sqrt K`. This is
the measure-theoretic reduction step behind `continuousWithinAt_covarianceMap`: once the reference
measure no longer depends on `K`, continuity in `K` becomes an ordinary dominated-convergence
argument in the integrand. -/
private lemma integral_activationProduct_multivariateGaussian_eq_stdGaussian
    {m : ℕ} (φ : ℝ → ℝ) (hφ_cont : Continuous φ) (K : Matrix (Fin m) (Fin m) ℝ) (α β : Fin m) :
    ∫ z : EuclideanSpace ℝ (Fin m), φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K) =
      ∫ x : EuclideanSpace ℝ (Fin m),
        φ ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K) x).ofLp α) *
          φ ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K) x).ofLp β) ∂stdGaussian _ := by
  rw [multivariateGaussian, integral_map]
  · simp
  · exact (by fun_prop : AEMeasurable (fun x : EuclideanSpace ℝ (Fin m) =>
      0 + toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K) x) (stdGaussian _))
  · exact (hφ_cont.measurable.comp
      (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) α).measurable).mul
      (hφ_cont.measurable.comp
        (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) β).measurable) |>.aestronglyMeasurable

/-- **
The claim: `K ↦ 𝒞_φ(K) := fun α β => ∫ z, φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K)`
is continuous *within the positive-semidefinite cone* at every
`K0 : Matrix (Fin m) (Fin m) ℝ` in that cone — in particular at singular / rank-deficient `K0`,
not only at positive-definite ones. The relative formulation is essential: Mathlib deliberately
defines `multivariateGaussian 0 K` as a Dirac measure for non-PSD `K`, so ambient continuity at a
nonzero singular PSD matrix would be false. In the Part 1 induction this theorem turns
`Φ_ℓ^{(n)} → Φ_ℓ` into `𝒞_φ(Φ_ℓ^{(n)}) → 𝒞_φ(Φ_ℓ)` through
`tendstoInMeasure_comp_of_continuousWithinAt` and the PSD invariant.

**Why this should be true in general, not just for positive-definite `K`**: the underlying
mathematical fact is standard on the *whole* PSD cone. Mathlib's own
`multivariateGaussian μ S = (stdGaussian _).map (μ + toEuclideanCLM (CFC.sqrt S))`
(`Mathlib.Probability.Distributions.Gaussian.Multivariate`) rewrites the integral above as an
integral against a *fixed* reference measure `stdGaussian` with a `K`-dependent integrand built from
`CFC.sqrt K`, so continuity in `K` reduces to: (a) continuity of `K ↦ CFC.sqrt K` on all PSD
matrices — a soft continuous-functional-calculus fact about the whole operator, which survives
eigenvalue collisions/rank drops even though the individual eigenprojections are *not* continuous
there — composed with continuity of `φ`; plus (b) the Dominated Convergence Theorem, with
domination supplied by `φ`'s polynomial growth exactly as in
`memLp_activation_coordinate_of_polynomial_growth`. The measure-theoretic reduction is
`integral_activationProduct_multivariateGaussian_eq_stdGaussian`, the linear-algebra bound is
`abs_toEuclideanCLM_ofLp_le`, and the growth bound on the integrand is
`abs_mul_le_of_polynomial_growth`.
-/
theorem continuousWithinAt_covarianceMap (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p) (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (m : ℕ) (K0 : Matrix (Fin m) (Fin m) ℝ) (hK0 : K0.PosSemidef) :
    ContinuousWithinAt (fun K : Matrix (Fin m) (Fin m) ℝ => fun α β : Fin m =>
      ∫ z : EuclideanSpace ℝ (Fin m), φ (z.ofLp α) * φ (z.ofLp β) ∂(multivariateGaussian 0 K))
      {K | K.PosSemidef} K0 := by
  rw [continuousWithinAt_pi]
  intro α
  rw [continuousWithinAt_pi]
  intro β
  let : CompleteSpace (Matrix (Fin m) (Fin m) ℝ) := FiniteDimensional.complete ℝ _
  have hsqrt : ContinuousWithinAt (fun K : Matrix (Fin m) (Fin m) ℝ => CFC.sqrt K)
      {K | K.PosSemidef} K0 := by
    have hsqrt' : ContinuousOn (fun K : Matrix (Fin m) (Fin m) ℝ => CFC.sqrt K)
        {K | K.PosSemidef} := by
      simpa only [Matrix.nonneg_iff_posSemidef] using
        (@CFC.continuousOn_sqrt (Matrix (Fin m) (Fin m) ℝ) _ _ _ _ _ _ _ _ _ _)
    exact hsqrt' K0 hK0
  let R : ℝ := ‖CFC.sqrt K0‖ + 1
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hnorm : ∀ᶠ K : Matrix (Fin m) (Fin m) ℝ in nhdsWithin K0 {K | K.PosSemidef},
      ‖CFC.sqrt K‖ < R := by
    have hnorm_tendsto : Filter.Tendsto (fun K : Matrix (Fin m) (Fin m) ℝ => ‖CFC.sqrt K‖)
        (nhdsWithin K0 {K | K.PosSemidef}) (nhds ‖CFC.sqrt K0‖) := hsqrt.norm
    exact hnorm_tendsto.eventually (show ∀ᶠ x : ℝ in nhds ‖CFC.sqrt K0‖, x < R from by
      apply eventually_lt_nhds
      dsimp [R]
      linarith)
  have h_integrable : Integrable (fun z : EuclideanSpace ℝ (Fin m) =>
      2 * C ^ 2 * (1 + R ^ (2 * p) * ‖z‖ ^ (2 * p))) (stdGaussian _) := by
    have hmoment : Integrable (fun z : EuclideanSpace ℝ (Fin m) => ‖z‖ ^ (2 * p))
        (stdGaussian _) := by
      simpa only [id_eq] using
        (ProbabilityTheory.IsGaussian.memLp_id (stdGaussian (EuclideanSpace ℝ (Fin m)))
          ((2 * p : ℕ) : ℝ≥0∞) (ENNReal.natCast_ne_top (2 * p))).integrable_norm_pow
          (by omega)
    exact ((integrable_const (1 : ℝ)).add (hmoment.const_mul (R ^ (2 * p)))).const_mul
      (2 * C ^ 2)
  simp_rw [integral_activationProduct_multivariateGaussian_eq_stdGaussian φ hφ_cont]
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun z : EuclideanSpace ℝ (Fin m) =>
      2 * C ^ 2 * (1 + R ^ (2 * p) * ‖z‖ ^ (2 * p)))
  · filter_upwards with K
    exact ((hφ_cont.comp
      ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) α).comp
        (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K)).continuous)).mul
      (hφ_cont.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) β).comp
          (toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K)).continuous))).aestronglyMeasurable
  · filter_upwards [hnorm] with K hK
    filter_upwards with z
    rw [Real.norm_eq_abs]
    have hα : |(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K) z).ofLp α| ≤ R * ‖z‖ :=
      (abs_toEuclideanCLM_ofLp_le (CFC.sqrt K) z α).trans
        (mul_le_mul_of_nonneg_right (le_of_lt hK) (norm_nonneg z))
    have hβ : |(toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K) z).ofLp β| ≤ R * ‖z‖ :=
      (abs_toEuclideanCLM_ofLp_le (CFC.sqrt K) z β).trans
        (mul_le_mul_of_nonneg_right (le_of_lt hK) (norm_nonneg z))
    simpa [mul_pow] using
      (abs_mul_le_of_polynomial_growth φ C hC p hφ_growth _ _ (R * ‖z‖)
        (mul_nonneg hR (norm_nonneg z)) hα hβ)
  · exact h_integrable
  · filter_upwards with z
    have hlinear : ContinuousWithinAt (fun K : Matrix (Fin m) (Fin m) ℝ =>
        toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K) z) {K | K.PosSemidef} K0 := by
      have hpair : ContinuousWithinAt
          (fun K : Matrix (Fin m) (Fin m) ℝ => (CFC.sqrt K, z)) {K | K.PosSemidef} K0 :=
        hsqrt.prodMk continuousWithinAt_const
      change ContinuousWithinAt
        ((fun p : Matrix (Fin m) (Fin m) ℝ × EuclideanSpace ℝ (Fin m) =>
          toEuclideanCLM (𝕜 := ℝ) p.1 p.2) ∘ fun K => (CFC.sqrt K, z))
        {K | K.PosSemidef} K0
      exact continuous_uncurry_toEuclideanCLM.continuousAt.continuousWithinAt.comp hpair
        (Set.mapsTo_univ _ _)
    have hα : ContinuousWithinAt (fun K : Matrix (Fin m) (Fin m) ℝ =>
        φ ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K) z).ofLp α)) {K | K.PosSemidef} K0 := by
      exact hφ_cont.continuousAt.continuousWithinAt.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) α).continuousAt.continuousWithinAt.comp
          hlinear (Set.mapsTo_univ _ _)) (Set.mapsTo_univ _ _)
    have hβ : ContinuousWithinAt (fun K : Matrix (Fin m) (Fin m) ℝ =>
        φ ((toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt K) z).ofLp β)) {K | K.PosSemidef} K0 := by
      exact hφ_cont.continuousAt.continuousWithinAt.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) β).continuousAt.continuousWithinAt.comp
          hlinear (Set.mapsTo_univ _ _)) (Set.mapsTo_univ _ _)
    exact hα.mul hβ

/-- Polynomial growth is preserved by squaring: if `|φ x| ≤ C (1 + |x|^p)` then
`|φ x ^ 2| ≤ 2 C² (1 + |x|^(2p))`. -/
lemma polynomial_growth_sq (φ : ℝ → ℝ) (C : ℝ) (p : ℕ)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p)) :
    ∀ x : ℝ, |φ x ^ 2| ≤ (2 * C ^ 2) * (1 + |x| ^ (2 * p)) := by
  intro x
  have hpow : |x| ^ (2 * p) = (|x| ^ p) ^ 2 := by
    rw [← pow_mul]
    congr 1
    omega
  have hsq : (1 + |x| ^ p) ^ 2 ≤ 2 * (1 + |x| ^ (2 * p)) := by
    rw [hpow]
    nlinarith [sq_nonneg (|x| ^ p - 1)]
  calc
    |φ x ^ 2| = |φ x| ^ 2 := by rw [abs_pow]
    _ ≤ (C * (1 + |x| ^ p)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hφ_growth x) 2
    _ = C ^ 2 * (1 + |x| ^ p) ^ 2 := by ring
    _ ≤ C ^ 2 * (2 * (1 + |x| ^ (2 * p))) :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg C)
    _ = (2 * C ^ 2) * (1 + |x| ^ (2 * p)) := by ring

/-- The conditional second-moment matrix of activated Gaussian coordinates is continuous on the
positive-semidefinite cone.  This is `continuousWithinAt_covarianceMap` applied to `φ²`, with the
entries normalized back to the form used by the conditional Chebyshev estimate. -/
theorem continuousWithinAt_activationProductSq
    (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (_hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (m : ℕ) (K0 : Matrix (Fin m) (Fin m) ℝ) (hK0 : K0.PosSemidef) :
    ContinuousWithinAt (fun K : Matrix (Fin m) (Fin m) ℝ => fun α β : Fin m =>
      ∫ z : EuclideanSpace ℝ (Fin m),
        (φ (z.ofLp α) * φ (z.ofLp β)) ^ 2 ∂multivariateGaussian 0 K)
      {K | K.PosSemidef} K0 := by
  have hφsq_growth := polynomial_growth_sq φ C p hφ_growth
  have hcont := continuousWithinAt_covarianceMap (fun x : ℝ => φ x ^ 2)
    (hφ_cont.pow 2) (2 * C ^ 2) (by positivity) (2 * p) (by omega) hφsq_growth m K0 hK0
  simpa only [pow_two, mul_mul_mul_comm] using hcont

end CovarianceMapContinuity

end DeepNNGPRecursion

end NTK

end
