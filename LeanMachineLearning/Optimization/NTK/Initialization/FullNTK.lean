/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Initialization.DeepNNGPTheorems

/-!
# Full two-layer NTK initialization and infinite-width limit

The joint neuron law, the full NTK summand (measurability and moments), the strong law of large
numbers for the full NTK and its quantitative concentration.

## Main results and proof outline

* `NTK.singleNeuronMeasure` : product probability measure for a single hidden neuron `(w, a)`.
* `NTK.measurePreserving_arrowProd_singleNeuronMeasure` : measure preservation of the finite
  array rearrangement between `(Fin n → singleNeuronMeasure d)` and `initMeasure n d`.
* `NTK.measurePreserving_infiniteSeq_to_init` : measure preservation of the infinite sequence
  prefix truncation to `initMeasure n d`.
* `NTK.fullNTKSummandSecondMoment` : uncentered second moment of the full NTK summand.
* `NTK.measurable_fullNTK_summand` : measurability of full activation-derivative summand.
* `NTK.integrable_fullNTK_summand` : integrability under product Gaussian measure.
* `NTK.memLp_two_fullNTK_summand` : square-integrability (`MemLp 2`) of full summand.
* `NTK.integrable_sq_fullNTK_summand` : second-moment bound for quantitative concentration.
* `NTK.integral_fullNTK_summand` : expectation identity decomposing into NNGP plus
  derivative kernel.
* `NTK.fullNTKSummand_tendsto_integral` : entrywise almost-sure convergence of empirical sums.
* `NTK.fullNTKMatrix_tendsto_integral` : almost-sure matrix convergence on dataset `X`.
* `NTK.fullNTKMatrix_norm_sub_tendsto_zero` : matrix norm almost-sure convergence.
* `NTK.fullNTKMatrix_tendstoInMeasure` : matrix convergence in probability (`TendstoInMeasure`).
* `NTK.fullNTKMatrix_scaled_dataset_tendsto_integral` : almost-sure matrix convergence on
  the paper's scaled dataset `(1 / √d) * X`.
* `NTK.fullNTKMatrix_scaled_dataset_tendstoInMeasure` : convergence in probability on the
  paper's scaled dataset `(1 / √d) * X`.

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

/-! ## Full Two-Layer NTK Initialization and Infinite-Width Limit -/

section FullTwoLayerNTKInitialization

/-! ### Joint Neuron Law

The joint initialization law of a single hidden neuron `(w, a)` with input weights
`w ~ 𝒩(0, I_d)` and readout weight `a ~ 𝒩(0, 1)`. -/

/-- The single-neuron initialization probability measure on `(Fin d → ℝ) × ℝ`:
the product of the input row Gaussian measure and the scalar readout Gaussian measure. -/
noncomputable def singleNeuronMeasure (d : ℕ) : Measure ((Fin d → ℝ) × ℝ) :=
  (gaussianRowMeasure d).prod (gaussianReal 0 1)

/-- Instance: `singleNeuronMeasure d` is a probability measure. -/
instance instIsProbabilityMeasureSingleNeuronMeasure (d : ℕ) :
    IsProbabilityMeasure (singleNeuronMeasure d) := by
  dsimp [singleNeuronMeasure]
  infer_instance

/-- Measure-preserving rearrangement between a finite array of neuron pairs
and the repository's `(W, a)` initialization representation `initMeasure n d`. -/
theorem measurePreserving_arrowProd_singleNeuronMeasure (n d : ℕ) :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n))
      (Measure.pi fun _ : Fin n => singleNeuronMeasure d)
      (initMeasure n d) := by
  dsimp [singleNeuronMeasure, initMeasure, gaussianInit, gaussianReadoutMeasure]
  exact measurePreserving_arrowProdEquivProdArrow (Fin d → ℝ) ℝ (Fin n)
    (fun _ => gaussianRowMeasure d) (fun _ => gaussianReal 0 1)

/-- **Markov bound for neuron averages.** For a nonnegative measurable single-neuron observable
`g` that is integrable under `singleNeuronMeasure d`, the width-normalized empirical average
`n⁻¹ ∑ᵢ g (Wᵢ, aᵢ)` is at most `τ` with `initMeasure n d`-probability at least `1 - δ`, as soon as
`E g ≤ τ δ`. The threshold is independent of the width, in contrast with the maximum-readout bound
whose threshold grows like `√(log n)`. -/
theorem measureReal_initMeasure_neuronAverage_le {n d : ℕ} (hn : 0 < n)
    {g : (Fin d → ℝ) × ℝ → ℝ} (hg : Measurable g) (hint : Integrable g (singleNeuronMeasure d))
    (hnn : ∀ q, 0 ≤ g q) {τ δ : ℝ} (hτ : 0 < τ)
    (hv : ∫ q, g q ∂(singleNeuronMeasure d) ≤ τ * δ) :
    (initMeasure n d).real {p | (n : ℝ)⁻¹ * ∑ i : Fin n, g (p.1 i, p.2 i) ≤ τ} ≥ 1 - δ := by
  have hpi := measureReal_pi_average_le_ge_one_sub (μ := singleNeuronMeasure d) (n := n) hn hg hint
    hnn hτ hv
  have hmp := measurePreserving_arrowProd_singleNeuronMeasure n d
  have hpre := hmp.measure_preimage_equiv
    {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) | (n : ℝ)⁻¹ * ∑ i : Fin n, g (p.1 i, p.2 i) ≤ τ}
  rw [Measure.real, ← hpre]
  exact hpi

/-- Equivalence between `Fin n` and `{i : ℕ // i ∈ Finset.range n}`. -/
private def finEquivRange (n : ℕ) : Fin n ≃ ↑(Finset.range n) where
  toFun i := ⟨i.val, Finset.mem_range.2 i.isLt⟩
  invFun j := ⟨j.val, Finset.mem_range.1 j.2⟩
  left_inv i := by ext; rfl
  right_inv j := by ext; rfl

/-- Restricting an infinite sequence under `Measure.infinitePi` to `Finset.range n` preserves
measure with respect to the finite product measure on `↑(Finset.range n)`. -/
private theorem measurePreserving_restrict_range {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ) :
    MeasurePreserving (Finset.range n).restrict
      (Measure.infinitePi fun _ : ℕ => ν)
      (Measure.pi fun _ : ↑(Finset.range n) => ν) where
  measurable := measurable_pi_iff.2 fun i => measurable_pi_apply i.1
  map_eq := Measure.infinitePi_map_restrict (fun _ : ℕ => ν)

/-- Restricting an infinite sequence under `Measure.infinitePi` to its first `n` elements
indexed by `Fin n` is measure-preserving with respect to `Measure.pi (fun _ : Fin n => ν)`. -/
theorem measurePreserving_prefixMap {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (n : ℕ) :
    MeasurePreserving (fun (seq : ℕ → α) (i : Fin n) => seq i.val)
      (Measure.infinitePi fun _ : ℕ => ν)
      (Measure.pi fun _ : Fin n => ν) := by
  have h_restrict := measurePreserving_restrict_range ν n
  have h_congr := (measurePreserving_piCongrLeft (fun _ : Fin n => ν) (finEquivRange n).symm)
  have h_comp := h_congr.comp h_restrict
  have heq : (MeasurableEquiv.piCongrLeft (fun _ => α) (finEquivRange n).symm ∘
      (Finset.range n).restrict) =
      (fun (seq : ℕ → α) (i : Fin n) => seq i.val) := by
    ext seq i
    rfl
  rwa [heq] at h_comp

/-- The measure-preserving map from the infinite sequence space
`Measure.infinitePi (fun _ => singleNeuronMeasure d)` to the repository's finite-width
initialization representation `initMeasure n d`.
Composes the prefix restriction map with the finite array rearrangement
`measurePreserving_arrowProd_singleNeuronMeasure`. -/
theorem measurePreserving_infiniteSeq_to_init (n d : ℕ) :
    MeasurePreserving
      (fun (seq : ℕ → (Fin d → ℝ) × ℝ) =>
        (fun (i : Fin n) => (seq i.val).1, fun (i : Fin n) => (seq i.val).2))
      (Measure.infinitePi fun _ : ℕ => singleNeuronMeasure d)
      (initMeasure n d) := by
  have h_pref := measurePreserving_prefixMap (singleNeuronMeasure d) n
  have h_rearr := measurePreserving_arrowProd_singleNeuronMeasure n d
  exact h_rearr.comp h_pref

/-! ### Full NTK Summand Measurability and Moments -/

/-- Measurability of the full activation-plus-derivative single-neuron NTK summand.
We state measurability directly for the full expression without introducing a one-line wrapper. -/
lemma measurable_fullNTK_summand {d : ℕ}
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (hderiv_meas : Measurable (deriv φ))
    (x x' : Fin d → ℝ) :
    Measurable (fun p : (Fin d → ℝ) × ℝ =>
      φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x') +
        p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) := by
  have h_w : Measurable (fun p : (Fin d → ℝ) × ℝ => p.1) := measurable_fst
  have h_a : Measurable (fun p : (Fin d → ℝ) × ℝ => p.2) := measurable_snd
  have h_wx : Measurable (fun p : (Fin d → ℝ) × ℝ => p.1 ⬝ᵥ x) :=
    (measurable_dotProduct_left x).comp h_w
  have h_wx' : Measurable (fun p : (Fin d → ℝ) × ℝ => p.1 ⬝ᵥ x') :=
    (measurable_dotProduct_left x').comp h_w
  have h_φx : Measurable (fun p : (Fin d → ℝ) × ℝ => φ (p.1 ⬝ᵥ x)) :=
    hφ_meas.comp h_wx
  have h_φx' : Measurable (fun p : (Fin d → ℝ) × ℝ => φ (p.1 ⬝ᵥ x')) :=
    hφ_meas.comp h_wx'
  have h_dφx : Measurable (fun p : (Fin d → ℝ) × ℝ => deriv φ (p.1 ⬝ᵥ x)) :=
    hderiv_meas.comp h_wx
  have h_dφx' : Measurable (fun p : (Fin d → ℝ) × ℝ => deriv φ (p.1 ⬝ᵥ x')) :=
    hderiv_meas.comp h_wx'
  have h_a2 : Measurable (fun p : (Fin d → ℝ) × ℝ => p.2 ^ 2) :=
    (continuous_pow 2).measurable.comp h_a
  exact (h_φx.mul h_φx').add (((h_a2.mul h_dφx).mul h_dφx').mul_const (x ⬝ᵥ x'))

/-- Integrability of the full activation-plus-derivative single-neuron NTK summand
under `singleNeuronMeasure d`. Follows from product-measure Fubini and independence of
weights and readouts. -/
lemma integrable_fullNTK_summand {d : ℕ}
    (φ : ℝ → ℝ) (x x' : Fin d → ℝ)
    (hφ_int : Integrable (fun w => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x')) (gaussianRowMeasure d))
    (hdφ_int : Integrable (fun w => deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x')) (gaussianRowMeasure d)) :
    Integrable (fun p : (Fin d → ℝ) × ℝ =>
      φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x') +
        p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x'))
      (singleNeuronMeasure d) := by
  dsimp [singleNeuronMeasure]
  have h1 : Integrable (fun p : (Fin d → ℝ) × ℝ => φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x'))
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) :=
    hφ_int.comp_fst (gaussianReal 0 1)
  have h2_prod : Integrable (fun p : (Fin d → ℝ) × ℝ =>
      (deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) * p.2 ^ 2)
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) :=
    (hdφ_int.mul_const (x ⬝ᵥ x')).mul_prod integrable_sq_gaussianReal
  have h2 : Integrable (fun p : (Fin d → ℝ) × ℝ =>
      p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x'))
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) := by
    refine h2_prod.congr (ae_of_all _ (fun p => ?_))
    ring
  exact h1.add h2

/-- Integrability of the full NTK summand under `MemLp 2` hypotheses on `φ` and `deriv φ`. -/
lemma integrable_fullNTK_summand_of_memLp {d : ℕ}
    (φ : ℝ → ℝ) (x x' : Fin d → ℝ)
    (hφ : MemLp (fun w => φ (w ⬝ᵥ x)) 2 (gaussianRowMeasure d))
    (hφ' : MemLp (fun w => φ (w ⬝ᵥ x')) 2 (gaussianRowMeasure d))
    (hdφ : MemLp (fun w => deriv φ (w ⬝ᵥ x)) 2 (gaussianRowMeasure d))
    (hdφ' : MemLp (fun w => deriv φ (w ⬝ᵥ x')) 2 (gaussianRowMeasure d)) :
    Integrable (fun p : (Fin d → ℝ) × ℝ =>
      φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x') +
        p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x'))
      (singleNeuronMeasure d) :=
  integrable_fullNTK_summand φ x x' (hφ.integrable_mul hφ') (hdφ.integrable_mul hdφ')

/-- Square-integrability (`MemLp 2`) of the full single-neuron NTK summand under
`MemLp 2` hypotheses on the activation product and derivative product.
Uses the fourth-moment Gaussian readout bound `integrable_pow_four_gaussianReal`. -/
lemma memLp_two_fullNTK_summand {d : ℕ}
    (φ : ℝ → ℝ) (hdφ_meas : Measurable (deriv φ))
    (x x' : Fin d → ℝ)
    (hφ_L2 : MemLp (fun w => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x')) 2 (gaussianRowMeasure d))
    (hdφ_L2 : MemLp (fun w => deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x')) 2 (gaussianRowMeasure d)) :
    MemLp (fun p : (Fin d → ℝ) × ℝ =>
      φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x') +
        p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x'))
      2 (singleNeuronMeasure d) := by
  dsimp [singleNeuronMeasure]
  have h1 : MemLp (fun p : (Fin d → ℝ) × ℝ => φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x')) 2
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) :=
    hφ_L2.comp_fst (gaussianReal 0 1)
  have hd_scaled : MemLp (fun w => deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x') * (x ⬝ᵥ x')) 2
      (gaussianRowMeasure d) :=
    hdφ_L2.mul_const (x ⬝ᵥ x')
  have hd_sq : Integrable (fun w => (deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x') * (x ⬝ᵥ x')) ^ 2)
      (gaussianRowMeasure d) :=
    (memLp_two_iff_integrable_sq hd_scaled.aestronglyMeasurable).1 hd_scaled
  have ha4 : Integrable (fun a : ℝ => (a ^ 2) ^ 2) (gaussianReal 0 1) := by
    have heq : (fun a : ℝ => (a ^ 2) ^ 2) = (fun a => a ^ 4) := by ext a; ring
    rw [heq]
    exact integrable_pow_four_gaussianReal
  have h2_sq_prod : Integrable (fun p : (Fin d → ℝ) × ℝ =>
      (deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) ^ 2 * (p.2 ^ 2) ^ 2)
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) :=
    hd_sq.mul_prod ha4
  have h2_sq : Integrable (fun p : (Fin d → ℝ) × ℝ =>
      (p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) ^ 2)
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) := by
    refine h2_sq_prod.congr (ae_of_all _ (fun p => ?_))
    dsimp
    ring
  have h_w : Measurable (fun p : (Fin d → ℝ) × ℝ => p.1) := measurable_fst
  have h_a : Measurable (fun p : (Fin d → ℝ) × ℝ => p.2) := measurable_snd
  have h_wx : Measurable (fun p : (Fin d → ℝ) × ℝ => p.1 ⬝ᵥ x) :=
    (measurable_dotProduct_left x).comp h_w
  have h_wx' : Measurable (fun p : (Fin d → ℝ) × ℝ => p.1 ⬝ᵥ x') :=
    (measurable_dotProduct_left x').comp h_w
  have h_dφx : Measurable (fun p : (Fin d → ℝ) × ℝ => deriv φ (p.1 ⬝ᵥ x)) :=
    hdφ_meas.comp h_wx
  have h_dφx' : Measurable (fun p : (Fin d → ℝ) × ℝ => deriv φ (p.1 ⬝ᵥ x')) :=
    hdφ_meas.comp h_wx'
  have h_a2 : Measurable (fun p : (Fin d → ℝ) × ℝ => p.2 ^ 2) :=
    (continuous_pow 2).measurable.comp h_a
  have h2_meas : Measurable (fun p : (Fin d → ℝ) × ℝ =>
      p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) :=
    ((h_a2.mul h_dφx).mul h_dφx').mul_const (x ⬝ᵥ x')
  have h2 : MemLp (fun p : (Fin d → ℝ) × ℝ =>
      p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) 2
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) :=
    (memLp_two_iff_integrable_sq h2_meas.aestronglyMeasurable).2 h2_sq
  exact h1.add h2

/-- Integrability of the squared full NTK summand under `singleNeuronMeasure d`,
providing second-moment bounds needed for quantitative concentration and Chebyshev bounds. -/
lemma integrable_sq_fullNTK_summand {d : ℕ}
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (hdφ_meas : Measurable (deriv φ))
    (x x' : Fin d → ℝ)
    (hφ_L2 : MemLp (fun w => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x')) 2 (gaussianRowMeasure d))
    (hdφ_L2 : MemLp (fun w => deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x')) 2 (gaussianRowMeasure d)) :
    Integrable (fun p : (Fin d → ℝ) × ℝ =>
      (φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x') +
        p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) ^ 2)
      (singleNeuronMeasure d) := by
  have h_mem := memLp_two_fullNTK_summand φ hdφ_meas x x' hφ_L2 hdφ_L2
  have h_meas := measurable_fullNTK_summand φ hφ_meas hdφ_meas x x'
  exact (memLp_two_iff_integrable_sq h_meas.aestronglyMeasurable).1 h_mem

/-- The expectation of the full single-neuron NTK summand under `singleNeuronMeasure d`
equals the sum of the NNGP activation kernel entry and the derivative kernel entry
scaled by the input inner product `x ⬝ᵥ x'`. -/
lemma integral_fullNTK_summand {d : ℕ}
    (φ : ℝ → ℝ) (x x' : Fin d → ℝ)
    (hφ_int : Integrable (fun w => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x')) (gaussianRowMeasure d))
    (hdφ_int : Integrable (fun w => deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x')) (gaussianRowMeasure d)) :
    ∫ p : (Fin d → ℝ) × ℝ,
      (φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x') +
        p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x'))
      ∂(singleNeuronMeasure d) =
      (∫ w, φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x') ∂(gaussianRowMeasure d)) +
        (∫ w, deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x') ∂(gaussianRowMeasure d)) * (x ⬝ᵥ x') := by
  dsimp [singleNeuronMeasure]
  have h1 : Integrable (fun p : (Fin d → ℝ) × ℝ => φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x'))
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) :=
    hφ_int.comp_fst (gaussianReal 0 1)
  have h2_prod : Integrable (fun p : (Fin d → ℝ) × ℝ =>
      (deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) * p.2 ^ 2)
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) :=
    (hdφ_int.mul_const (x ⬝ᵥ x')).mul_prod integrable_sq_gaussianReal
  have h2 : Integrable (fun p : (Fin d → ℝ) × ℝ =>
      p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x'))
      ((gaussianRowMeasure d).prod (gaussianReal 0 1)) := by
    refine h2_prod.congr (ae_of_all _ (fun p => ?_))
    ring
  rw [integral_add h1 h2]
  have h_int1 : ∫ p : (Fin d → ℝ) × ℝ, φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x')
      ∂((gaussianRowMeasure d).prod (gaussianReal 0 1)) =
      ∫ w, φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x') ∂(gaussianRowMeasure d) := by
    have hfst := integral_fun_fst (fun w => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x'))
      (μ := gaussianRowMeasure d) (ν := gaussianReal 0 1)
    rw [hfst]
    simp
  have h_int2 : ∫ p : (Fin d → ℝ) × ℝ,
      p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')
      ∂((gaussianRowMeasure d).prod (gaussianReal 0 1)) =
      (∫ w, deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x') ∂(gaussianRowMeasure d)) * (x ⬝ᵥ x') := by
    have h_eq : (fun p : (Fin d → ℝ) × ℝ =>
        p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) =
        (fun p : (Fin d → ℝ) × ℝ =>
        (deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')) * p.2 ^ 2) := by
      ext p; ring
    rw [h_eq]
    rw [integral_prod_mul (fun w => deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x') * (x ⬝ᵥ x'))
      (fun a => a ^ 2)]
    rw [integral_sq_gaussianReal]
    rw [mul_one]
    exact integral_mul_const (x ⬝ᵥ x') (fun w => deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x'))
  rw [h_int1, h_int2]

/-! ### Strong Law of Large Numbers for the Full NTK -/

/-- Strong law of large numbers for empirical averages of the full NTK summand
over an i.i.d. neuron sequence drawn from `singleNeuronMeasure d`.
Reuses the generalized `iid_average_tendsto_integral` from `NTK.Foundations.IIDAverage`. -/
theorem fullNTKSummand_tendsto_integral {d : ℕ}
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (hdφ_meas : Measurable (deriv φ))
    (x x' : Fin d → ℝ)
    (hφ_int : Integrable (fun w => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x')) (gaussianRowMeasure d))
    (hdφ_int : Integrable (fun w => deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x')) (gaussianRowMeasure d)) :
    ∀ᵐ seq : ℕ → (Fin d → ℝ) × ℝ ∂(Measure.infinitePi fun _ => singleNeuronMeasure d),
      Filter.Tendsto
        (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j : Fin n,
          (φ ((seq j).1 ⬝ᵥ x) * φ ((seq j).1 ⬝ᵥ x') +
            (seq j).2 ^ 2 * deriv φ ((seq j).1 ⬝ᵥ x) * deriv φ ((seq j).1 ⬝ᵥ x') * (x ⬝ᵥ x')))
        Filter.atTop
        (nhds ((∫ w, φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x') ∂(gaussianRowMeasure d)) +
          (∫ w, deriv φ (w ⬝ᵥ x) * deriv φ (w ⬝ᵥ x') ∂(gaussianRowMeasure d)) * (x ⬝ᵥ x'))) := by
  set g := fun p : (Fin d → ℝ) × ℝ =>
    φ (p.1 ⬝ᵥ x) * φ (p.1 ⬝ᵥ x') +
      p.2 ^ 2 * deriv φ (p.1 ⬝ᵥ x) * deriv φ (p.1 ⬝ᵥ x') * (x ⬝ᵥ x')
  have hg_meas : Measurable g := measurable_fullNTK_summand φ hφ_meas hdφ_meas x x'
  have hg_int : Integrable g (singleNeuronMeasure d) :=
    integrable_fullNTK_summand φ x x' hφ_int hdφ_int
  have h_slln := iid_average_tendsto_integral (singleNeuronMeasure d) g hg_meas hg_int
  rw [integral_fullNTK_summand φ x x' hφ_int hdφ_int] at h_slln
  exact h_slln

/-- Full matrix almost-sure convergence of the empirical NTK Gram matrix on dataset `X`
to the deterministic limiting NTK Gram matrix. Assembles entrywise SLLN convergence
over the finite index space `Fin m × Fin m` using `tendsto_pi_nhds` and `ae_all_iff`. -/
theorem fullNTKMatrix_tendsto_integral {m d : ℕ}
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_int : ∀ α β : Fin m,
      Integrable (fun w => φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β)) (gaussianRowMeasure d))
    (hdφ_int : ∀ α β : Fin m,
      Integrable (fun w => deriv φ (w ⬝ᵥ X α) * deriv φ (w ⬝ᵥ X β)) (gaussianRowMeasure d)) :
    ∀ᵐ seq : ℕ → (Fin d → ℝ) × ℝ ∂(Measure.infinitePi fun _ => singleNeuronMeasure d),
      Filter.Tendsto
        (fun n : ℕ => ((fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
          (φ ((seq j).1 ⬝ᵥ X α) * φ ((seq j).1 ⬝ᵥ X β) +
            (seq j).2 ^ 2 * deriv φ ((seq j).1 ⬝ᵥ X α) * deriv φ ((seq j).1 ⬝ᵥ X β) *
              (X α ⬝ᵥ X β))) : Matrix (Fin m) (Fin m) ℝ))
        Filter.atTop
        (nhds ((fun α β =>
          (∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) +
            (∫ w, deriv φ (w ⬝ᵥ X α) * deriv φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) *
              (X α ⬝ᵥ X β)) : Matrix (Fin m) (Fin m) ℝ)) := by
  have h_entry : ∀ α β : Fin m,
      ∀ᵐ seq : ℕ → (Fin d → ℝ) × ℝ ∂(Measure.infinitePi fun _ => singleNeuronMeasure d),
        Filter.Tendsto
          (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j : Fin n,
            (φ ((seq j).1 ⬝ᵥ X α) * φ ((seq j).1 ⬝ᵥ X β) +
              (seq j).2 ^ 2 * deriv φ ((seq j).1 ⬝ᵥ X α) * deriv φ ((seq j).1 ⬝ᵥ X β) *
                (X α ⬝ᵥ X β)))
          Filter.atTop
          (nhds ((∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) +
            (∫ w, deriv φ (w ⬝ᵥ X α) * deriv φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) *
              (X α ⬝ᵥ X β))) :=
    fun α β => fullNTKSummand_tendsto_integral φ hφ_meas hdφ_meas (X α) (X β)
      (hφ_int α β) (hdφ_int α β)
  have h_all :
      ∀ᵐ seq : ℕ → (Fin d → ℝ) × ℝ ∂(Measure.infinitePi fun _ => singleNeuronMeasure d),
        ∀ α β : Fin m,
          Filter.Tendsto
            (fun n : ℕ => (n : ℝ)⁻¹ * ∑ j : Fin n,
              (φ ((seq j).1 ⬝ᵥ X α) * φ ((seq j).1 ⬝ᵥ X β) +
                (seq j).2 ^ 2 * deriv φ ((seq j).1 ⬝ᵥ X α) * deriv φ ((seq j).1 ⬝ᵥ X β) *
                  (X α ⬝ᵥ X β)))
            Filter.atTop
            (nhds ((∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) +
              (∫ w, deriv φ (w ⬝ᵥ X α) * deriv φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) *
                (X α ⬝ᵥ X β))) := by
    simp_rw [ae_all_iff]
    exact h_entry
  filter_upwards [h_all] with seq hseq
  exact tendsto_pi_nhds.2 fun α => tendsto_pi_nhds.2 fun β => hseq α β

/-- Full matrix almost-sure convergence of the empirical NTK on the paper's scaled dataset
`(1 / √d) * X`, with explicit scaling `1 / d` on the derivative covariance factor. -/
theorem fullNTKMatrix_scaled_dataset_tendsto_integral {m d : ℕ} (hd : 0 < d)
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_int : ∀ α β : Fin m,
      Integrable (fun w => φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) (gaussianRowMeasure d))
    (hdφ_int : ∀ α β : Fin m,
      Integrable (fun w => deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) (gaussianRowMeasure d)) :
    ∀ᵐ seq : ℕ → (Fin d → ℝ) × ℝ ∂(Measure.infinitePi fun _ => singleNeuronMeasure d),
      Filter.Tendsto
        (fun n : ℕ => ((fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
          (φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
             φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) +
            (seq j).2 ^ 2 *
              deriv φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
              deriv φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) *
              ((d : ℝ)⁻¹ * (X α ⬝ᵥ X β)))) : Matrix (Fin m) (Fin m) ℝ))
        Filter.atTop
        (nhds ((fun α β =>
          (∫ w, φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
            φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) ∂(gaussianRowMeasure d)) +
            (∫ w, deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
              deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) ∂(gaussianRowMeasure d)) *
                ((d : ℝ)⁻¹ * (X α ⬝ᵥ X β))) : Matrix (Fin m) (Fin m) ℝ)) := by
  have h_base := fullNTKMatrix_tendsto_integral φ hφ_meas hdφ_meas
    (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) hφ_int hdφ_int
  simp_rw [dotProduct_scaled_dataset d hd] at h_base
  exact h_base

/-- Matrix norm almost-sure convergence of the empirical NTK Gram matrix on dataset `X`
to the deterministic limiting NTK Gram matrix: `‖K_n(0) - K_∞‖ → 0` almost surely. -/
theorem fullNTKMatrix_norm_sub_tendsto_zero {m d : ℕ}
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_int : ∀ α β : Fin m,
      Integrable (fun w => φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β)) (gaussianRowMeasure d))
    (hdφ_int : ∀ α β : Fin m,
      Integrable (fun w => deriv φ (w ⬝ᵥ X α) * deriv φ (w ⬝ᵥ X β)) (gaussianRowMeasure d)) :
    ∀ᵐ seq : ℕ → (Fin d → ℝ) × ℝ ∂(Measure.infinitePi fun _ => singleNeuronMeasure d),
      Filter.Tendsto
        (fun n : ℕ =>
          ‖((fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
              (φ ((seq j).1 ⬝ᵥ X α) * φ ((seq j).1 ⬝ᵥ X β) +
                (seq j).2 ^ 2 * deriv φ ((seq j).1 ⬝ᵥ X α) * deriv φ ((seq j).1 ⬝ᵥ X β) *
                  (X α ⬝ᵥ X β))) : Matrix (Fin m) (Fin m) ℝ) -
            ((fun α β =>
              (∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) +
                (∫ w, deriv φ (w ⬝ᵥ X α) * deriv φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) *
                  (X α ⬝ᵥ X β)) : Matrix (Fin m) (Fin m) ℝ)‖)
        Filter.atTop
        (nhds 0) := by
  set L : Matrix (Fin m) (Fin m) ℝ := fun α β =>
    (∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) +
      (∫ w, deriv φ (w ⬝ᵥ X α) * deriv φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) * (X α ⬝ᵥ X β)
  have h := fullNTKMatrix_tendsto_integral φ hφ_meas hdφ_meas X hφ_int hdφ_int
  filter_upwards [h] with seq hseq
  have h_sub := hseq.sub (tendsto_const_nhds (x := L))
  rw [sub_self] at h_sub
  exact tendsto_zero_iff_norm_tendsto_zero.1 h_sub

/-- Convergence in probability (`TendstoInMeasure`) of the empirical NTK Gram matrix
to the deterministic limiting NTK Gram matrix on dataset `X`. -/
theorem fullNTKMatrix_tendstoInMeasure {m d : ℕ}
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_int : ∀ α β : Fin m,
      Integrable (fun w => φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β)) (gaussianRowMeasure d))
    (hdφ_int : ∀ α β : Fin m,
      Integrable (fun w => deriv φ (w ⬝ᵥ X α) * deriv φ (w ⬝ᵥ X β)) (gaussianRowMeasure d)) :
    TendstoInMeasure
      (Measure.infinitePi fun _ : ℕ => singleNeuronMeasure d)
      (fun n : ℕ => fun seq : ℕ → (Fin d → ℝ) × ℝ =>
        ((fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
          (φ ((seq j).1 ⬝ᵥ X α) * φ ((seq j).1 ⬝ᵥ X β) +
            (seq j).2 ^ 2 * deriv φ ((seq j).1 ⬝ᵥ X α) * deriv φ ((seq j).1 ⬝ᵥ X β) *
              (X α ⬝ᵥ X β))) : Matrix (Fin m) (Fin m) ℝ))
      Filter.atTop
      (fun _ => ((fun α β =>
        (∫ w, φ (w ⬝ᵥ X α) * φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) +
          (∫ w, deriv φ (w ⬝ᵥ X α) * deriv φ (w ⬝ᵥ X β) ∂(gaussianRowMeasure d)) *
            (X α ⬝ᵥ X β)) : Matrix (Fin m) (Fin m) ℝ)) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro n
    refine (measurable_pi_iff.2 fun α => measurable_pi_iff.2 fun β => ?_).aestronglyMeasurable
    refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
    have h_eval : Measurable (fun seq : ℕ → (Fin d → ℝ) × ℝ => seq j.val) :=
      measurable_pi_apply j.val
    have h_summand := measurable_fullNTK_summand φ hφ_meas hdφ_meas (X α) (X β)
    exact h_summand.comp h_eval
  · exact fullNTKMatrix_tendsto_integral φ hφ_meas hdφ_meas X hφ_int hdφ_int

/-- Convergence in probability (`TendstoInMeasure`) of the empirical NTK Gram matrix
on the paper's scaled dataset `(1 / √d) * X`. -/
theorem fullNTKMatrix_scaled_dataset_tendstoInMeasure {m d : ℕ} (hd : 0 < d)
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_int : ∀ α β : Fin m,
      Integrable (fun w => φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) (gaussianRowMeasure d))
    (hdφ_int : ∀ α β : Fin m,
      Integrable (fun w => deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) (gaussianRowMeasure d)) :
    TendstoInMeasure
      (Measure.infinitePi fun _ : ℕ => singleNeuronMeasure d)
      (fun n : ℕ => fun seq : ℕ → (Fin d → ℝ) × ℝ =>
        ((fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
          (φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
             φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) +
            (seq j).2 ^ 2 *
              deriv φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
              deriv φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) *
              ((d : ℝ)⁻¹ * (X α ⬝ᵥ X β)))) : Matrix (Fin m) (Fin m) ℝ))
      Filter.atTop
      (fun _ => ((fun α β =>
        (∫ w, φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
          φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) ∂(gaussianRowMeasure d)) +
          (∫ w, deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
            deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) ∂(gaussianRowMeasure d)) *
              ((d : ℝ)⁻¹ * (X α ⬝ᵥ X β))) : Matrix (Fin m) (Fin m) ℝ)) := by
  have h_base := fullNTKMatrix_tendstoInMeasure φ hφ_meas hdφ_meas
    (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) hφ_int hdφ_int
  simp_rw [dotProduct_scaled_dataset d hd] at h_base
  exact h_base

/-- The deterministic limiting full NTK Gram matrix on dataset `X` with input dimension `d`:
  `Θ_∞ = limitingCovariance φ scaledX + (d⁻¹ • (X Xᵀ)) ∘ limitingCovariance (deriv φ) scaledX`,
  where `∘` is the entrywise (Hadamard) product. -/
noncomputable def limitingFullNTKMatrix {m d : ℕ}
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun α β =>
    limitingCovariance φ (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) α β +
      limitingCovariance (deriv φ) (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) α β *
        ((d : ℝ)⁻¹ * (X α ⬝ᵥ X β))

/-- Equation lemma for `limitingFullNTKMatrix`. -/
lemma limitingFullNTKMatrix_apply {m d : ℕ}
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) (α β : Fin m) :
    limitingFullNTKMatrix φ X α β =
      limitingCovariance φ (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) α β +
        limitingCovariance (deriv φ) (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) α β *
          ((d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) := rfl

/-- The limiting full NTK Gram matrix is symmetric (Hermitian). -/
lemma limitingFullNTKMatrix_isHermitian {m d : ℕ}
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) :
    (limitingFullNTKMatrix φ X).IsHermitian := by
  ext α β
  simp only [limitingFullNTKMatrix_apply, conjTranspose_apply, star_trivial]
  have h1 : limitingCovariance φ (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) β α =
      limitingCovariance φ (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) α β := by
    rw [limitingCovariance_apply, limitingCovariance_apply]
    congr 1 with w
    ring
  have h2 : limitingCovariance (deriv φ) (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) β α =
      limitingCovariance (deriv φ) (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k) α β := by
    rw [limitingCovariance_apply, limitingCovariance_apply]
    congr 1 with w
    ring
  rw [h1, h2, dotProduct_comm]

/-- The limiting full NTK is the NNGP covariance of `φ` plus the Schur product of the covariance of
`φ'` with the input Gram matrix of the scaled dataset. -/
lemma limitingFullNTKMatrix_eq_add_hadamard {m d : ℕ}
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) :
    limitingFullNTKMatrix φ X =
      (limitingCovariance φ (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) +
        (limitingCovariance (deriv φ) (fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k)).hadamard
          ((Matrix.of fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k : Matrix (Fin m) (Fin d) ℝ) *
            (Matrix.of fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k :
              Matrix (Fin m) (Fin d) ℝ).conjTranspose) := by
  set scaledX : Matrix (Fin m) (Fin d) ℝ := fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k
  ext α β
  simp only [limitingFullNTKMatrix_apply, Matrix.add_apply, Matrix.hadamard_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
  dsimp [scaledX]
  have hsqrt : (Real.sqrt (d : ℝ))⁻¹ * (Real.sqrt (d : ℝ))⁻¹ = (d : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg d)]
  have hterm (k : Fin d) :
      ((Real.sqrt (d : ℝ))⁻¹ * X α k) * ((Real.sqrt (d : ℝ))⁻¹ * X β k) =
        (d : ℝ)⁻¹ * (X α k * X β k) := by
    rw [mul_mul_mul_comm, hsqrt]
  simp_rw [hterm, ← Finset.mul_sum]
  rfl

/-- The deterministic limiting full NTK matrix is positive semidefinite (`PosSemidef`),
established via Schur product theorem for the derivative covariance and input Gram matrix. -/
theorem limitingFullNTKMatrix_posSemidef {m d : ℕ}
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_meas : Measurable φ)
    (hdφ_meas : Measurable (deriv φ))
    (hφ_L2 : ∀ α : Fin m,
      MemLp (fun w => φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)))
        2 (gaussianRowMeasure d))
    (hdφ_L2 : ∀ α : Fin m,
      MemLp (fun w => deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)))
        2 (gaussianRowMeasure d)) :
    (limitingFullNTKMatrix φ X).PosSemidef := by
  set scaledX : Matrix (Fin m) (Fin d) ℝ := fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k
  have h_cov1 : (limitingCovariance φ scaledX).PosSemidef :=
    limitingCovariance_posSemidef φ scaledX hφ_meas hφ_L2
  have h_cov2 : (limitingCovariance (deriv φ) scaledX).PosSemidef :=
    limitingCovariance_posSemidef (deriv φ) scaledX hdφ_meas hdφ_L2
  have h_gram : (scaledX * scaledX.conjTranspose).PosSemidef :=
    Matrix.posSemidef_self_mul_conjTranspose scaledX
  have h_schur : ((limitingCovariance (deriv φ) scaledX).hadamard
      (scaledX * scaledX.conjTranspose)).PosSemidef :=
    h_cov2.hadamard h_gram
  have h_sum : ((limitingCovariance φ scaledX) +
      (limitingCovariance (deriv φ) scaledX).hadamard
        (scaledX * scaledX.conjTranspose)).PosSemidef :=
    h_cov1.add h_schur
  have heq := limitingFullNTKMatrix_eq_add_hadamard φ X
  rw [heq]
  exact h_sum

/-- **Strict positive definiteness of the NNGP covariance from feature independence.** If the
features `w ↦ φ(w ⬝ᵥ X α)` are linearly independent modulo Gaussian-null sets -- no nontrivial
combination `∑ α, u α * φ (w ⬝ᵥ X α)` vanishes `gaussianRowMeasure d`-almost everywhere -- then
`limitingCovariance φ X` is positive definite. The argument is the quadratic-form identity
`u ⬝ᵥ Φ u = 𝔼[(∑ α, u α φ(w ⬝ᵥ X α))²]`, which is positive as soon as the square is not
a.e. zero. -/
theorem limitingCovariance_posDef_of_ae_independent {m d : ℕ}
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_L2 : ∀ α : Fin m, MemLp (fun w => φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d))
    (hind : ∀ u : Fin m → ℝ,
      (∀ᵐ w ∂(gaussianRowMeasure d), ∑ α : Fin m, u α * φ (w ⬝ᵥ X α) = 0) → u = 0) :
    (limitingCovariance φ X).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.2 ⟨limitingCovariance_isHermitian φ X, ?_⟩
  intro c hc
  have hq : star c ⬝ᵥ (limitingCovariance φ X) *ᵥ c =
      ∫ w, (∑ α : Fin m, c α * φ (w ⬝ᵥ X α)) ^ 2 ∂(gaussianRowMeasure d) := by
    rw [← sum_sum_mul_limitingCovariance_eq_integral_sq φ X hφ_L2 c]
    simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring
  rw [hq]
  have hg : MemLp (fun w => ∑ α : Fin m, c α * φ (w ⬝ᵥ X α)) 2 (gaussianRowMeasure d) :=
    memLp_finsetSum _ fun α _ => (hφ_L2 α).const_mul (c α)
  rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun w => sq_nonneg _)
    hg.integrable_sq]
  refine pos_iff_ne_zero.2 fun h0 => hc (hind c ?_)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with w hw
  by_contra hne
  exact hw (pow_ne_zero 2 hne)

/-- **The limiting full NTK is positive definite under feature independence.**
`K_∞ = Φ_φ + Φ_{φ'} ⬝ᵥ (X Xᵀ / d)` with the second summand positive semidefinite (Schur product), so
`K_∞` is positive definite as soon as `Φ_φ` is
(`limitingCovariance_posDef_of_ae_independent`). Independence of the *values* `φ(w ⬝ᵥ X α)` is the
relevant hypothesis; the derivative term only helps. -/
theorem limitingFullNTKMatrix_posDef_of_ae_independent {m d : ℕ}
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ) (hdφ_meas : Measurable (deriv φ))
    (hφ_L2 : ∀ α : Fin m,
      MemLp (fun w => φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)))
        2 (gaussianRowMeasure d))
    (hdφ_L2 : ∀ α : Fin m,
      MemLp (fun w => deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)))
        2 (gaussianRowMeasure d))
    (hind : ∀ u : Fin m → ℝ,
      (∀ᵐ w ∂(gaussianRowMeasure d),
        ∑ α : Fin m, u α * φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) = 0) → u = 0) :
    (limitingFullNTKMatrix φ X).PosDef := by
  set scaledX : Matrix (Fin m) (Fin d) ℝ := fun α k => (Real.sqrt (d : ℝ))⁻¹ * X α k
  rw [limitingFullNTKMatrix_eq_add_hadamard]
  exact (limitingCovariance_posDef_of_ae_independent φ scaledX hφ_L2 hind).add_posSemidef
    ((limitingCovariance_posSemidef (deriv φ) scaledX hdφ_meas hdφ_L2).hadamard
      (Matrix.posSemidef_self_mul_conjTranspose scaledX))

/-- **Feature independence forces distinct inputs.** If the scaled features are linearly independent
modulo Gaussian-null sets, the inputs `X α` are pairwise distinct. This is the necessary half of the
source's informal condition "distinct inputs and an expressive activation": the hypothesis of
`limitingCovariance_posDef_of_ae_independent` cannot hold for a dataset with a repeated input, and
the remaining (sufficiency) content is exactly the independence hypothesis. -/
theorem injective_of_ae_independent {m d : ℕ} (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hind : ∀ u : Fin m → ℝ,
      (∀ᵐ w ∂(gaussianRowMeasure d),
        ∑ α : Fin m, u α * φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) = 0) → u = 0) :
    Function.Injective X := by
  intro α β hαβ
  by_contra hne
  have h := hind (Pi.single α 1 - Pi.single β 1) (Filter.Eventually.of_forall fun w => by
    simp [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply, ite_mul, hαβ])
  have := congrFun h α
  simp [hne] at this

/-- Matrix almost-sure convergence of the empirical NTK neuron-average matrix to the
deterministic `limitingFullNTKMatrix` on the paper's scaled dataset `(1 / √d) * X`. -/
theorem fullNTKMatrix_scaled_dataset_tendsto_limitingFullNTKMatrix {m d : ℕ} (hd : 0 < d)
    (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (hdφ_meas : Measurable (deriv φ))
    (X : Fin m → Fin d → ℝ)
    (hφ_int : ∀ α β : Fin m,
      Integrable (fun w => φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) (gaussianRowMeasure d))
    (hdφ_int : ∀ α β : Fin m,
      Integrable (fun w => deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) (gaussianRowMeasure d)) :
    ∀ᵐ seq : ℕ → (Fin d → ℝ) × ℝ ∂(Measure.infinitePi fun _ => singleNeuronMeasure d),
      Filter.Tendsto
        (fun n : ℕ =>
          ((fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
              (φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
                 φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) +
               (seq j).2 ^ 2 *
                 deriv φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
                 deriv φ ((seq j).1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) *
                 ((d : ℝ)⁻¹ * (X α ⬝ᵥ X β)))) : Matrix (Fin m) (Fin m) ℝ))
        Filter.atTop
        (nhds (limitingFullNTKMatrix φ X)) :=
  fullNTKMatrix_scaled_dataset_tendsto_integral hd φ hφ_meas hdφ_meas X hφ_int hdφ_int

/-! ### Quantitative Concentration for the Full NTK Initializer -/

section FullNTKConcentration

/-- Uncentered second moment of the full activation-plus-derivative NTK summand under
`singleNeuronMeasure d`. Hides the bivariate Gaussian integral over hidden weight and readout
parameters `(w, a)`.

This moment is the core quantitative constant in:
1. `chebyshev_entrywise_empiricalNTKMatrix`: entrywise Chebyshev concentration for each `(α, β)`.
2. `chebyshev_matrix_empiricalNTKMatrix`: Frobenius-norm matrix concentration via union bound.
3. Downstream initial spectral gap transfer and lazy-training bootstrap bounds. -/
noncomputable def fullNTKSummandSecondMoment (d : ℕ) (φ : ℝ → ℝ)
    {m : ℕ} (X : Fin m → Fin d → ℝ) (α β : Fin m) : ℝ :=
  ∫ u : (Fin d → ℝ) × ℝ,
    (φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
       φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) +
     u.2 ^ 2 * deriv φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
       deriv φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) *
       ((fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k) ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) ^ 2
    ∂(singleNeuronMeasure d)

lemma fullNTKSummandSecondMoment_nonneg (d : ℕ) (φ : ℝ → ℝ) {m : ℕ} (X : Fin m → Fin d → ℝ)
    (α β : Fin m) : 0 ≤ fullNTKSummandSecondMoment d φ X α β :=
  integral_nonneg fun _ => sq_nonneg _

/-- Expectation of the full NTK summand on the scaled dataset `(1 / √d) * X` equals
the limiting full NTK matrix entry `limitingFullNTKMatrix φ X α β`. -/
lemma integral_fullNTK_summand_scaled_dataset_eq_limiting {m d : ℕ} (hd : 0 < d)
    (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (hφ_int : ∀ α β : Fin m,
      Integrable (fun w => φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) (gaussianRowMeasure d))
    (hdφ_int : ∀ α β : Fin m,
      Integrable (fun w => deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
        deriv φ (w ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k))) (gaussianRowMeasure d))
    (α β : Fin m) :
    ∫ u : (Fin d → ℝ) × ℝ,
      (φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
         φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) +
       u.2 ^ 2 * deriv φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)) *
         deriv φ (u.1 ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)) *
         ((fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k) ⬝ᵥ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k)))
      ∂(singleNeuronMeasure d) =
      limitingFullNTKMatrix φ X α β := by
  have h := integral_fullNTK_summand φ (fun k => (Real.sqrt (d : ℝ))⁻¹ * X α k)
    (fun k => (Real.sqrt (d : ℝ))⁻¹ * X β k) (hφ_int α β) (hdφ_int α β)
  rw [h]
  rw [dotProduct_scaled_dataset d hd]
  rw [limitingFullNTKMatrix_apply, limitingCovariance_apply, limitingCovariance_apply]

end FullNTKConcentration

end FullTwoLayerNTKInitialization

end NTK

end
