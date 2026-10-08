/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.ReLU.ArcCosine
public import LeanMachineLearning.Optimization.NTK.Foundations.SlutskyTightness
public import LeanMachineLearning.Optimization.NTK.Foundations.Concentration
public import LeanMachineLearning.Optimization.NTK.Foundations.InfinitePiPrefix

/-!
# Two-layer initialization: network setup and independence structure

Network evaluation and the empirical covariance, the initialization probability space and its
independence structure, and entrywise (max) concentration for the readout weights.

## Main results and proof outline

* The initialization probability space is written out explicitly: readout weights
  $a_i \stackrel{\text{i.i.d.}}{\sim} \mathcal{N}(0, 1)$ have law
  `Measure.pi fun _ : Fin n => gaussianReal 0 1` (`𝒩(0, I_n)`), input weights
  $\mathbf{w}_i \stackrel{\text{i.i.d.}}{\sim} \mathcal{N}(\mathbf{0}, \mathbf{I}_{n_0})$ have law
  `Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1` (`𝒩(0,1)^{n×d}`),
  and the parameters $\boldsymbol{\theta} = \{(a_i, \mathbf{w}_i)\}_{i=1}^n$ have the `.prod` of the
  two.
* `NTK.indepFun_input_readout` : mutual independence of the input weights $\mathbf{W}$ and the
  readout weights $a$.
* `NTK.evalSingle` (defined in `NTK.Basic`) : scalar network output
  $f(\mathbf{x}; \mathbf{W}, a) =
    \frac{1}{\sqrt{n}} \sum_{i=1}^n a_i \varphi(\mathbf{w}_i^\top \mathbf{x})$, with the equation
    lemma
  `NTK.evalSingle_eq_normalized_sum`.
* `NTK.evalVector` : output vector
  $\mathbf{f}_m = (f(\mathbf{x}^1), \dots, f(\mathbf{x}^m))^\top \in \mathbb{R}^m$.
* `NTK.empiricalCovariance` : empirical covariance matrix
  $\Phi^{(n), \alpha \beta} := \frac{1}{n} \sum_{i=1}^n \varphi(\mathbf{w}_i^\top \mathbf{x}^\alpha)
    \varphi(\mathbf{w}_i^\top \mathbf{x}^\beta) \in \mathbb{R}^{m \times m}$.
* Entrywise (max) concentration of the readout weights
  (`prob_abs_gaussianReadout_coord_ge_le`, `prob_forall_abs_gaussianReadout_le`).

See
`LeanMachineLearning.Optimization.NTK.Initialization`
for the overview of the whole development.
-/

@[expose] public section

open Real MeasureTheory ProbabilityTheory Matrix Complex
open scoped BigOperators MatrixOrder RealInnerProductSpace Kronecker ENNReal

namespace NTK

variable {d n m : ℕ}

section Preliminaries

/-! ## Network Setup and Initialization Probability Space -/

/-! ### Network Evaluation and Empirical Covariance -/

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

/-- Coordinates of `evalVector` are the network outputs `evalSingle` at the corresponding inputs. -/
@[simp] lemma evalVector_ofLp
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (a : Fin n → ℝ) (X : Fin m → Fin d → ℝ) (α : Fin m) :
    (evalVector φ W a X).ofLp α = evalSingle φ W a (X α) := rfl

/-- The inner product `⟪t, f_m⟫` equals `∑ α, t α * f(X α)`. -/
lemma evalVector_inner
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (a : Fin n → ℝ) (t : EuclideanSpace ℝ (Fin m)) :
    ⟪t, evalVector φ W a X⟫ = ∑ α : Fin m, t.ofLp α * evalSingle φ W a (X α) := by
  simp only [evalVector, PiLp.inner_apply, RCLike.inner_apply', conj_trivial]

/-- `evalVector` is continuous in the readout weights `a`. -/
lemma evalVector_continuous
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ) :
    Continuous (fun a => evalVector φ W a X) := by
  change Continuous ((WithLp.toLp 2) ∘ (fun a α => evalSingle φ W a (X α)))
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun α => ?_)
  simp only [evalSingle_eq_normalized_sum]
  exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
    (continuous_apply i).mul continuous_const)

/-- `evalVector` is measurable in the readout weights `a`. -/
lemma evalVector_measurable
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ) :
    Measurable (fun a => evalVector φ W a X) :=
  (evalVector_continuous φ W X).measurable

/-- The map `a ↦ ⟪t, evalVector φ W a X⟫` is continuous. -/
lemma inner_evalVector_continuous
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    Continuous (fun a => ⟪t, evalVector φ W a X⟫) :=
  (innerSL ℝ t).continuous.comp (evalVector_continuous φ W X)

/-- The map `a ↦ ⟪t, evalVector φ W a X⟫` is measurable. -/
lemma inner_evalVector_measurable
    (φ : ℝ → ℝ) (W : Fin n → Fin d → ℝ) (X : Fin m → Fin d → ℝ)
    (t : EuclideanSpace ℝ (Fin m)) :
    Measurable (fun a => ⟪t, evalVector φ W a X⟫) :=
  (inner_evalVector_continuous φ W X t).measurable

/-! ### Initialization Probability Space and Independence Structure -/

/-- Readout weight coordinates `a_i` have marginal standard normal distribution
$\mathcal{N}(0, 1)$. -/
lemma map_gaussianReadoutMeasure_coord (i : Fin n) :
    Measure.map (fun a : Fin n → ℝ => a i) (Measure.pi fun _ : Fin n =>
        gaussianReal 0 1) = gaussianReal 0 1 :=
  (MeasureTheory.measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).map_eq

/-- Markov tail bound for the normalized squared readout energy. -/
lemma prob_gaussianReadout_sum_sq_le
    (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).real {a | (n :
        ℝ)⁻¹ * ∑ i : Fin n, a i ^ 2 ≤ δ⁻¹} ≥
      1 - δ :=
  measureReal_pi_average_le_ge_one_sub (μ := gaussianReal 0 1) hn (g := fun a : ℝ => a ^ 2)
    (by fun_prop) integrable_sq_gaussianReal (fun _ => sq_nonneg _) (inv_pos.2 hδ)
    (by rw [integral_sq_gaussianReal, inv_mul_cancel₀ hδ.ne'])

/-- **Empirical activation energy concentration.** If `φ(w ⬝ᵥ x_α)` is square integrable under the
Gaussian row law and `∑_α E φ(w ⬝ᵥ x_α)² ≤ τ δ`, then the width-normalized activation energy
`n⁻¹ ∑_i ∑_α φ(W_i ⬝ᵥ x_α)²` of the hidden weights is at most `τ` with probability `≥ 1 - δ`. -/
lemma measureReal_gaussianInit_activationEnergy_le {n d m : ℕ} (hn : 0 < n) (φ : ℝ → ℝ)
    (hφ : Measurable φ) (X : Fin m → Fin d → ℝ)
    (hL2 : ∀ α, MemLp (fun w : Fin d → ℝ => φ (w ⬝ᵥ X α)) 2 (Measure.pi fun _ : Fin d =>
        gaussianReal 0 1))
    {τ δ : ℝ} (hτ : 0 < τ)
    (hv : ∑ α : Fin m, ∫ w, φ (w ⬝ᵥ X α) ^ 2 ∂(Measure.pi fun _ : Fin d => gaussianReal 0 1) ≤ τ *
        δ) :
    (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).real {W | (n :
        ℝ)⁻¹ * ∑ i : Fin n, ∑ α : Fin m,
      φ (W i ⬝ᵥ X α) ^ 2 ≤ τ} ≥ 1 - δ :=
  measureReal_pi_average_le_ge_one_sub (μ := (Measure.pi fun _ : Fin d => gaussianReal 0 1)) hn
    (g := fun w => ∑ α : Fin m, φ (w ⬝ᵥ X α) ^ 2)
    (Finset.measurable_sum _ fun α _ =>
      (hφ.comp (measurable_dotProduct_left (X α))).pow_const 2)
    (integrable_finsetSum _ fun α _ => (hL2 α).integrable_sq) (fun w => by positivity) hτ
    (by rwa [integral_finsetSum _ fun α _ => (hL2 α).integrable_sq])

/-- A measurable activation with at most linear growth has all Gaussian moments along a row. -/
lemma memLp_gaussianRow_comp_of_linear_growth (φ : ℝ → ℝ) (hφ : Measurable φ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgrow : ∀ z, |φ z| ≤ A + B * |z|) (x : Fin d → ℝ) (p : NNReal) :
    MemLp (fun w : Fin d → ℝ => φ (w ⬝ᵥ x)) p (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
  have hlin : Measurable (fun w : Fin d → ℝ => w ⬝ᵥ x) := measurable_dotProduct_left x
  change MemLp (φ ∘ fun w : Fin d → ℝ => w ⬝ᵥ x) p (Measure.pi fun _ : Fin d => gaussianReal 0 1)
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
    MemLp (fun w : Fin d → ℝ => φ (w ⬝ᵥ x) * φ (w ⬝ᵥ x')) 2 (Measure.pi fun _ : Fin d =>
        gaussianReal 0 1) := by
  have h4 : ∀ y : Fin d → ℝ, MemLp (fun w : Fin d → ℝ => φ (w ⬝ᵥ y)) (4 : ENNReal)
      (Measure.pi fun _ : Fin d => gaussianReal 0 1) := fun y => by
    simpa using memLp_gaussianRow_comp_of_linear_growth φ hφ hA hB hgrow y (d := d) 4
  exact MemLp.mul (r := 2) (h4 x') (h4 x)

/-! ### Entrywise (max) concentration for readout weights

`prob_gaussianReadout_sum_sq_le` above bounds the readout *energy* `n⁻¹ ∑ᵢ aᵢ²` (an average),
via Markov's inequality, giving a tail bound whose natural scale is `O(√(n/δ))`. The Jacobian
Lipschitz bound
(`NTK.Training.TwoLayer.JacobianBounds`'s
`outputJacobian_netFromParams_frobenius_sub_le`) instead needs a uniform
bound on every *individual* `|aᵢ|`. Bounding this the same crude way (Markov on each `aᵢ²`
plus a union bound) would give `R = O(√(n/δ))` too - and since the Jacobian-Lipschitz constant
`L_J` is linear in `R`,
an `R` that grows like `√n` would make `L_J = Θ(1)`, silently breaking the "kernel freezes as
`n → ∞`" conclusion. The fix is to use the actual Gaussian tail (Chernoff/sub-Gaussian) instead of
Markov,
which gives the much better `R = O(√(log(n/δ)))` - logarithmic, not polynomial, in the width. -/

/-- Transport the two-sided tail bound to a single readout coordinate `a i`. -/
lemma prob_abs_gaussianReadout_coord_ge_le (n : ℕ) (i : Fin n) (ε : ℝ) (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin n =>
        gaussianReal 0 1).real {a : Fin n → ℝ | ε ≤ |a i|} ≤ 2 * Real.exp (-ε ^ 2 / 2) := by
  exact ((measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).measureReal_preimage
    (measurableSet_le measurable_const continuous_abs.measurable).nullMeasurableSet).trans_le
    (prob_abs_gaussianReal_ge_le ε hε)

/-- Union bound over all `n` readout coordinates: the probability that *some* coordinate exceeds
`ε` in absolute value is at most `2n` times the single-coordinate tail bound. -/
theorem prob_max_abs_gaussianReadout_ge_le (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).real {a : Fin n → ℝ | ∃ i, ε ≤ |a i|} ≤
      2 * (n : ℝ) * Real.exp (-ε ^ 2 / 2) := by
  have heq : {a : Fin n → ℝ | ∃ i, ε ≤ |a i|} = ⋃ i : Fin n, {a : Fin n → ℝ | ε ≤ |a i|} := by
    ext a; simp
  rw [heq]
  calc
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).real (⋃ i : Fin n, {a : Fin n → ℝ | ε ≤ |a i|}) ≤
        ∑ i : Fin n, (Measure.pi fun _ : Fin n =>
            gaussianReal 0 1).real {a : Fin n → ℝ | ε ≤ |a i|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin n, 2 * Real.exp (-ε ^ 2 / 2) :=
      Finset.sum_le_sum (fun i _ => prob_abs_gaussianReadout_coord_ge_le n i ε hε)
    _ = 2 * (n : ℝ) * Real.exp (-ε ^ 2 / 2) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- **Readout-weight concentration.** With probability `≥ 1 - δ`, every readout weight `a i` has
`|a i| ≤ √(2 log(2n/δ))` - a bound that grows only **logarithmically** in the width `n`. -/
theorem prob_forall_abs_gaussianReadout_le (n : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    (Measure.pi fun _ : Fin n => gaussianReal 0 1).real
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
  have hcompl : {a : Fin n → ℝ | ∀ i, |a i| ≤ ε}ᶜ ⊆ {a : Fin n → ℝ | ∃ i, ε ≤ |a i|} := by
    intro a ha
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at ha
    obtain ⟨i, hi⟩ := ha
    exact ⟨i, hi.le⟩
  exact one_sub_le_measureReal_of_measureReal_compl_le _ ((measureReal_mono hcompl).trans hbad)

/-- Lift the readout-weight concentration's readout-only event to the full initialization product
measure
the product `𝒩(0,1)^{n×d} ⊗ 𝒩(0, I_n)` of the input-weight and readout laws. -/
lemma initMeasure_forall_abs_readout_ge (n d : ℕ) (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi fun
        _ : Fin n => gaussianReal 0 1)).real
      {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
        ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ))} ≥ 1 - δ := by
  have hset : {p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) |
      ∀ i, |p.2 i| ≤ Real.sqrt (2 * Real.log (2 * n / δ))} =
      Set.univ ×ˢ {a : Fin n → ℝ | ∀ i, |a i| ≤ Real.sqrt (2 * Real.log (2 * n / δ))} := by
    ext p; simp
  rw [hset, MeasureTheory.measureReal_prod_prod]
  simpa using prob_forall_abs_gaussianReadout_le n hn hδ hδ1

/-- Readout weights `a_i` are mutually independent across hidden units `i ∈ Fin n`. -/
lemma iIndepFun_readoutWeights (n : ℕ) :
    iIndepFun (fun i : Fin n => fun a : Fin n → ℝ => a i) (Measure.pi fun _ : Fin n => gaussianReal
        0 1) :=
  iIndepFun_pi (fun _ => aemeasurable_id)

/-- Input weight rows `W_i` have marginal standard Gaussian row distribution `𝒩(0, Iᵈ)`. -/
lemma map_gaussianInit_row (i : Fin n) :
    Measure.map (fun W : Fin n → Fin d → ℝ => W i) (Measure.pi fun _ : Fin n => Measure.pi fun _ :
        Fin d => gaussianReal 0 1) = (Measure.pi fun _ : Fin d => gaussianReal 0 1) :=
  (MeasureTheory.measurePreserving_eval (fun _ : Fin n => (Measure.pi fun _ : Fin d => gaussianReal
      0 1)) i).map_eq

/-- Input weight rows `W_i` are mutually independent across hidden unit indices `i ∈ Fin n`. -/
lemma iIndepFun_inputWeights (n d : ℕ) :
    iIndepFun (fun i : Fin n => fun W : Fin n → Fin d → ℝ => W i) (Measure.pi fun _ : Fin n =>
        Measure.pi fun _ : Fin d => gaussianReal 0 1) :=
  iIndepFun_pi (fun _ => aemeasurable_id)

/-- Mutual Independence: the family of input weights `W` is independent of readout weights `a`. -/
lemma indepFun_input_readout (n d : ℕ) :
    IndepFun (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => p.1)
      (fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => p.2)
      ((Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin d => gaussianReal 0 1).prod (Measure.pi
          fun _ : Fin n => gaussianReal 0 1)) :=
  indepFun_prod measurable_id measurable_id

end Preliminaries

end NTK

end
