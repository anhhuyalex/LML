/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Initialization.DeepRecursion
public import LeanMachineLearning.Optimization.NTK.Initialization.ConditionalConcentration

/-!
# Theorem 2.13 (deep NNGP recursion): main theorems

Asymptotic propagation of the empirical covariance and the deep NNGP recursion theorems.

## Main results and proof outline

* `NTK.conditional_empiricalCovariance_tendstoInMeasure_layerCovarianceSeq` : the corresponding
  recursive forward-kernel statement for continuous polynomial-growth activations.
* `NTK.deepEmpiricalCovariance_tendstoInMeasure` : Part 1, layerwise covariance convergence in
  probability $\Phi_\ell^{(n)} \xrightarrow{\mathbb{P}} \Phi_\ell$. The successor step is
  `deepPreactivation_succ_deviation_tendsto` (conditional Chebyshev with a random covariance, from
  `Initialization/ConditionalConcentration.lean`).
* `NTK.measurable_deepEval`, `NTK.deepEval_covariance_posSemidef`,
  `NTK.map_deepEval_snd_eq_multivariateGaussian`, `NTK.charFun_map_deepEval`,
  `NTK.norm_charFun_deepEval_le_one`, `NTK.aestronglyMeasurable_charFun_deepEval`,
  `NTK.tendsto_charFun_map_deepEval` : supporting measurability, positive-semidefiniteness, exact
  conditional normality, and characteristic-function lemmas for the depth-$L$ network's output,
  assembled into Part 2 below.
* `NTK.tendstoInDistribution_deepEval` : Part 2, output convergence in distribution
  $\mathbf{f}_m(\boldsymbol{\theta}) \xrightarrow{d} \mathcal{N}(\mathbf{0}, \Phi_L)$. Fully
  proved (reuses `NTK.exact_conditional_normality_general_multivariate` verbatim for the exact
  conditional normality step, and Part 1 above).

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

section AsymptoticEmpiricalCovariancePropagation

/-- **Deterministic recursive forward kernel.**  At every fixed depth `ℓ`, an i.i.d. conditional
Gaussian layer with covariance `layerCovarianceSeq 1 0 φ m Φ0 ℓ` has empirical activated
covariance converging in probability to the next deterministic forward kernel. -/
theorem conditional_empiricalCovariance_tendstoInMeasure_layerCovarianceSeq
    (m ℓ : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (Φ0 : Matrix (Fin m) (Fin m) ℝ) :
    TendstoInMeasure
      (Measure.infinitePi fun _ : ℕ =>
        multivariateGaussian 0 (layerCovarianceSeq 1 0 φ m Φ0 ℓ))
      (fun n : ℕ => fun (Z : ℕ → EuclideanSpace ℝ (Fin m)) => fun α β : Fin m =>
        (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ ((Z j.val).ofLp α) * φ ((Z j.val).ofLp β))
      Filter.atTop
      (fun _ => layerCovarianceSeq 1 0 φ m Φ0 (ℓ + 1)) := by
  simpa [layerCovarianceSeq] using
    (conditional_empiricalCovariance_tendstoInMeasure_of_polynomial_growth
      m φ hφ_cont C hC p hp hφ_growth
        (layerCovarianceSeq 1 0 φ m Φ0 ℓ))

/-- The input layer is an exact transport of the reusable i.i.d.-Gaussian empirical-covariance
theorem.  Keeping this bridge separate makes the base case of the deep recursion independent of
the representation of the input weights. -/
lemma input_empiricalCovariance_tendstoInMeasure
    (d m : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p)) (X : Fin m → Fin d → ℝ) :
    TendstoInMeasure
      (Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      (fun n : ℕ => fun W : ℕ → ℕ → ℝ => fun α β : Fin m => (n : ℝ)⁻¹ * ∑ j : Fin n,
        φ ((d : ℝ)⁻¹.sqrt * ∑ k : Fin d, W j.val k.val * X α k) *
        φ ((d : ℝ)⁻¹.sqrt * ∑ k : Fin d, W j.val k.val * X β k))
      Filter.atTop
      (fun _ => layerCovarianceSeq 1 0 φ m
        (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) 1) := by
  let Z : (ℕ → ℕ → ℝ) → ℕ → EuclideanSpace ℝ (Fin m) :=
    fun W j => WithLp.toLp 2 fun α =>
      (d : ℝ)⁻¹.sqrt * ∑ k : Fin d, W j k.val * X α k
  have hZ_meas : Measurable Z := by
    refine measurable_pi_iff.2 fun j => ?_
    apply (PiLp.continuous_toLp 2 _).measurable.comp
    refine measurable_pi_iff.2 fun α => ?_
    refine measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)
    exact ((measurable_pi_apply k.val).comp (measurable_pi_apply j)).mul_const _
  have hZ_map : Measure.map Z
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
      Measure.infinitePi fun _ : ℕ =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) := by
    simpa [Z] using map_infinitePi_input_preactivations d m X
  let f : ℕ → (ℕ → EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ :=
    fun n z α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
      φ ((z j.val).ofLp α) * φ ((z j.val).ofLp β)
  let g : (ℕ → EuclideanSpace ℝ (Fin m)) → Matrix (Fin m) (Fin m) ℝ :=
    fun _ => layerCovarianceSeq 1 0 φ m
      (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) 1
  have hf_meas : ∀ n, Measurable (f n) := by
    intro n
    refine measurable_pi_iff.2 fun α => measurable_pi_iff.2 fun β => ?_
    refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
    exact
      (hφ_cont.measurable.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) α).measurable.comp
          (measurable_pi_apply j.val))).mul
      (hφ_cont.measurable.comp
        ((PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) β).measurable.comp
          (measurable_pi_apply j.val)))
  have hbase := conditional_empiricalCovariance_tendstoInMeasure_layerCovarianceSeq
    m 0 φ hφ_cont C hC p hp hφ_growth
      (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β))
  have htransport := tendstoInMeasure_comp_measurePreserving
    (E := Fin m → Fin m → ℝ) hbase
    ({ measurable := hZ_meas, map_eq := hZ_map } : MeasurePreserving Z
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      (Measure.infinitePi fun _ : ℕ => multivariateGaussian 0
        (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)))) hf_meas
      (measurable_const : Measurable g)
  simpa [f, g, Z] using htransport

/-- The layer-zero case of the deep covariance recursion.  This is the input empirical-covariance
transport composed with evaluation of the first independent layer population. -/
lemma deepEmpiricalCovariance_zero_tendstoInMeasure
    (d m L : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin d → ℝ) (hL : 0 < L) :
    TendstoInMeasure
      (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      (fun n : ℕ => fun w : Fin L → ℕ → ℕ → ℝ =>
        fun α β : Fin m => (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) 0 α j) *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) 0 β j))
      Filter.atTop
      (fun _ => layerCovarianceSeq 1 0 φ m
        (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) 1) := by
  let T : (Fin L → ℕ → ℕ → ℝ) → ℕ → ℕ → ℝ := fun w => w ⟨0, hL⟩
  have hT : MeasurePreserving T
      (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) := by
    simpa [T] using
      (measurePreserving_eval (fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) ⟨0, hL⟩)
  have hbase := input_empiricalCovariance_tendstoInMeasure d m φ hφ_cont C hC p hp hφ_growth X
  have hf : ∀ n : ℕ, Measurable (fun W : ℕ → ℕ → ℝ => fun α β : Fin m =>
      (n : ℝ)⁻¹ * ∑ j : Fin n,
        φ ((d : ℝ)⁻¹.sqrt * ∑ k : Fin d, W j.val k.val * X α k) *
        φ ((d : ℝ)⁻¹.sqrt * ∑ k : Fin d, W j.val k.val * X β k)) := by
    intro n
    refine measurable_pi_iff.2 fun α => measurable_pi_iff.2 fun β => ?_
    refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
    exact
      (hφ_cont.measurable.comp
        (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
          ((measurable_pi_apply k.val).comp (measurable_pi_apply j.val)).mul_const _))).mul
      (hφ_cont.measurable.comp
        (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
          ((measurable_pi_apply k.val).comp (measurable_pi_apply j.val)).mul_const _)))
  have htransport := tendstoInMeasure_comp_measurePreserving
    (E := Fin m → Fin m → ℝ) hbase hT hf
      (measurable_const : Measurable fun _ : ℕ → ℕ → ℝ =>
        layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) 1)
  simpa [T, deepPreactivation, hL, dotProduct] using htransport

/-- Restricting an infinite independent Gaussian weight population to its first `n` rows and
columns gives the finite conditional Gaussian layer law.  This is the raw-population counterpart
of `conditional_preactivations_eq_pi`; keeping it separate avoids rebuilding finite restrictions
inside the depth induction. -/
lemma conditional_preactivations_infinite_eq_pi (n m : ℕ) (φ : ℝ → ℝ)
    (H : Fin n → EuclideanSpace ℝ (Fin m)) :
    Measure.map
      (fun W : ℕ → ℕ → ℝ => fun j : Fin n => WithLp.toLp 2 fun α : Fin m =>
        (n : ℝ)⁻¹.sqrt * ∑ k : Fin n, W j.val k.val * φ ((H k).ofLp α))
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
      Measure.pi (fun _ : Fin n =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (fun α β : Fin m => (n : ℝ)⁻¹ * ∑ k : Fin n,
            φ ((H k).ofLp α) * φ ((H k).ofLp β))) := by
  let restrictColumns : (ℕ → ℕ → ℝ) → (ℕ → Fin n → ℝ) :=
    fun W j k => W j k.val
  have hrestrictColumns_meas : Measurable restrictColumns := by
    refine measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun k => ?_
    exact (measurable_pi_apply k.val).comp (measurable_pi_apply j)
  have hrestrictColumns : Measure.map restrictColumns
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
      Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin n => gaussianReal 0 1) :=
    map_prefixMap_infinitePi (gaussianReal 0 1) n
  let restrictRows : (ℕ → Fin n → ℝ) → (Fin n → Fin n → ℝ) :=
    fun W j k => W j.val k
  have hrestrictRows_meas : Measurable restrictRows := by
    refine measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun k => ?_
    exact (measurable_pi_apply k).comp (measurable_pi_apply j.val)
  have hrestrictRows : Measure.map restrictRows
      (Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin n => gaussianReal 0 1)) = (Measure.pi
          fun _ : Fin n => Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
    exact map_infinitePi_rows_eq_gaussianInit n n
  let F : (Fin n → Fin n → ℝ) → Fin n → EuclideanSpace ℝ (Fin m) :=
    fun W j => WithLp.toLp 2 fun α =>
      (n : ℝ)⁻¹.sqrt * ∑ k : Fin n, W j k * φ ((H k).ofLp α)
  have hF_meas : Measurable F := by
    refine measurable_pi_iff.2 fun j => ?_
    apply (PiLp.continuous_toLp 2 _).measurable.comp
    refine measurable_pi_iff.2 fun α => ?_
    refine measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)
    exact ((measurable_pi_apply k).comp (measurable_pi_apply j)).mul_const _
  have hcomp : F ∘ restrictRows ∘ restrictColumns =
      fun W : ℕ → ℕ → ℝ => fun j : Fin n => WithLp.toLp 2 fun α : Fin m =>
        (n : ℝ)⁻¹.sqrt * ∑ k : Fin n, W j.val k.val * φ ((H k).ofLp α) := rfl
  rw [← hcomp]
  calc
    Measure.map ((F ∘ restrictRows) ∘ restrictColumns)
        (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
      Measure.map (F ∘ restrictRows)
        (Measure.map restrictColumns
          (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)) := by
        rw [← Measure.map_map (hF_meas.comp hrestrictRows_meas) hrestrictColumns_meas]
    _ = Measure.map (F ∘ restrictRows) (Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin n =>
        gaussianReal 0 1)) := by
      rw [hrestrictColumns]
    _ = Measure.map F (Measure.map restrictRows
        (Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin n => gaussianReal 0 1))) := by
      rw [← Measure.map_map hF_meas hrestrictRows_meas]
    _ = Measure.map F (Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin n =>
        gaussianReal 0 1) := by rw [hrestrictRows]
    _ = Measure.pi (fun _ : Fin n =>
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (fun α β : Fin m => (n : ℝ)⁻¹ * ∑ k : Fin n,
            φ ((H k).ofLp α) * φ ((H k).ofLp β))) :=
      conditional_preactivations_eq_pi n n m φ H

/-- With all preceding populations fixed, a fresh infinite population produces an i.i.d. Gaussian
next preactivation layer.  This is the `deepPreactivation` specialization of
`conditional_preactivations_infinite_eq_pi`; it is the conditional-law bridge for the successor
step of the deep covariance induction. -/
lemma conditional_deepPreactivation_succ_infinite_eq_pi
    (d m n : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (W : ℕ → ℕ → ℕ → ℝ) (ℓ : ℕ) :
    Measure.map
      (fun V : ℕ → ℕ → ℝ => fun j : Fin n => WithLp.toLp 2 fun α : Fin m =>
        deepPreactivation d m n φ X
          (fun k => if _ : k ≤ ℓ then W k else if k = ℓ + 1 then V else 0) (ℓ + 1) α j)
      (Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) =
      Measure.pi (fun _ : Fin n => multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (fun α β : Fin m => (n : ℝ)⁻¹ * ∑ k : Fin n,
          φ (deepPreactivation d m n φ X W ℓ α k) *
          φ (deepPreactivation d m n φ X W ℓ β k))) := by
  let Wnext : (ℕ → ℕ → ℝ) → ℕ → ℕ → ℕ → ℝ :=
    fun V k => if _ : k ≤ ℓ then W k else if k = ℓ + 1 then V else 0
  have hprevious : ∀ V : ℕ → ℕ → ℝ,
      deepPreactivation d m n φ X (Wnext V) ℓ = deepPreactivation d m n φ X W ℓ := by
    intro V
    apply deepPreactivation_congr_of_eqOn d m n φ X (Wnext V) W ℓ
    intro k hk
    simp [Wnext, hk]
  let H : Fin n → EuclideanSpace ℝ (Fin m) := fun k => WithLp.toLp 2 fun α : Fin m =>
    deepPreactivation d m n φ X W ℓ α k
  have hmap :
      (fun V : ℕ → ℕ → ℝ => fun j : Fin n => WithLp.toLp 2 fun α : Fin m =>
        deepPreactivation d m n φ X (Wnext V) (ℓ + 1) α j) =
      (fun V : ℕ → ℕ → ℝ => fun j : Fin n => WithLp.toLp 2 fun α : Fin m =>
        (n : ℝ)⁻¹.sqrt * ∑ k : Fin n, V j.val k.val * φ ((H k).ofLp α)) := by
    funext V j
    congr 1
    funext α
    simp only [deepPreactivation]
    rw [show Wnext V (ℓ + 1) = V by simp [Wnext]]
    rw [hprevious V]
  rw [show (fun V : ℕ → ℕ → ℝ => fun j : Fin n => WithLp.toLp 2 fun α : Fin m =>
      deepPreactivation d m n φ X
        (fun k => if _ : k ≤ ℓ then W k else if k = ℓ + 1 then V else 0) (ℓ + 1) α j) =
      (fun V : ℕ → ℕ → ℝ => fun j : Fin n => WithLp.toLp 2 fun α : Fin m =>
        deepPreactivation d m n φ X (Wnext V) (ℓ + 1) α j) by rfl, hmap]
  simpa only [H, WithLp.ofLp_toLp] using
    conditional_preactivations_infinite_eq_pi n m φ H

end AsymptoticEmpiricalCovariancePropagation

/-- Measurability of `deepPreactivation` as a function of the layer-weight population, for fixed
width `n` and layer `ℓ`. -/
lemma measurable_deepPreactivation (d m n L : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (X : Fin m → Fin d → ℝ) (ℓ : ℕ) (α : Fin m) (j : Fin n) :
    Measurable (fun w : Fin L → ℕ → ℕ → ℝ =>
      deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ α j) := by
  have h_coord : ∀ ℓ0 : ℕ, Measurable
      (fun w : Fin L → ℕ → ℕ → ℝ => (if h : ℓ0 < L then w ⟨ℓ0, h⟩ else 0)) := by
    intro ℓ0
    by_cases hℓ0 : ℓ0 < L
    · simpa [hℓ0] using measurable_pi_apply (⟨ℓ0, hℓ0⟩ : Fin L)
    · simp [hℓ0]
  induction ℓ generalizing α j with
  | zero =>
    simp only [deepPreactivation]
    unfold dotProduct
    refine measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)
    exact ((measurable_pi_apply k.val).comp
      ((measurable_pi_apply j.val).comp (h_coord 0))).mul_const _
  | succ ℓ ih =>
    simp only [deepPreactivation]
    refine measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)
    exact (((measurable_pi_apply k.val).comp
      ((measurable_pi_apply j.val).comp (h_coord (ℓ + 1)))).mul (hφ_meas.comp (ih α k)))

/-- Measurability of the empirical feature average `n⁻¹ ∑ⱼ ψ(h_ℓ^α,ⱼ) ψ(h_ℓ^β,ⱼ)` as a function of
the layer-weight population (for a measurable feature map `ψ`; `ψ = φ` gives the activation Gram,
`ψ = φ'` the derivative Gram). -/
lemma measurable_deepFeatureAverage (d m n L : ℕ) (φ ψ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (hψ_meas : Measurable ψ) (X : Fin m → Fin d → ℝ) (ℓ : ℕ) (α β : Fin m) :
    Measurable (fun w : Fin L → ℕ → ℕ → ℝ => (n : ℝ)⁻¹ * ∑ j : Fin n,
      ψ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ α j) *
      ψ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ β j)) :=
  measurable_const.mul (Finset.measurable_sum _ fun j _ =>
    (hψ_meas.comp (measurable_deepPreactivation d m n L φ hφ_meas X ℓ α j)).mul
      (hψ_meas.comp (measurable_deepPreactivation d m n L φ hφ_meas X ℓ β j)))

/-- **Successor-layer deviation for the deep covariance recursion.** Conditionally on the first
`ℓ + 1` layer populations, layer `ℓ + 1` is i.i.d. `𝒩(0, Φ̂_ℓ^{(n)})` with the *random* empirical
covariance `Φ̂_ℓ^{(n)}` of layer `ℓ` (built from the activation `φ`). If `Φ̂_ℓ^{(n)} → Klim` in
measure, then for *any* continuous polynomial-growth `ψ` the empirical entry
`n⁻¹ ∑_j ψ(h_j^α) ψ(h_j^β)` of layer `ℓ + 1` is within `δ` of its conditional mean
`∫ ψ ψ d𝒩(0, Φ̂_ℓ^{(n)})` with probability tending to `1`. Taking `ψ = φ` gives the forward
covariance; `ψ = φ'` gives the derivative Gram matrix.

Proof: split the `Fin L`-indexed product at coordinate `ℓ + 1` (`measurePreserving_piFinSuccAbove`);
`Φ̂_ℓ^{(n)}` ignores that coordinate (`deepPreactivation_congr_of_eqOn`), the conditional-law bridge
`conditional_deepPreactivation_succ_infinite_eq_pi` identifies the fresh layer, and
`tendsto_measure_conditional_activationProduct` is the conditional Chebyshev estimate. -/
theorem deepPreactivation_succ_deviation_tendsto
    (d m L : ℕ) (φ ψ : ℝ → ℝ) (hφ_cont : Continuous φ) (hψ_cont : Continuous ψ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hψ_growth : ∀ x : ℝ, |ψ x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin d → ℝ) (ℓ : ℕ) (hℓ : ℓ + 1 < L)
    (Klim : Matrix (Fin m) (Fin m) ℝ) (hKlim : Klim.PosSemidef)
    (hprev : TendstoInMeasure
      (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      (fun n : ℕ => fun w : Fin L → ℕ → ℕ → ℝ => fun α β : Fin m =>
        (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ α j) *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ β j))
      Filter.atTop (fun _ => Klim))
    (α β : Fin m) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun n : ℕ =>
      (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      {w | δ ≤ |(n : ℝ)⁻¹ * ∑ j : Fin n,
          ψ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (ℓ + 1) α j) *
          ψ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (ℓ + 1) β j) -
        ∫ z : EuclideanSpace ℝ (Fin m), ψ (z.ofLp α) * ψ (z.ofLp β) ∂multivariateGaussian 0
          (fun α β : Fin m => (n : ℝ)⁻¹ * ∑ j : Fin n,
            φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ α j) *
            φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ β j))|})
      Filter.atTop (nhds 0) := by
  classical
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  set ν₀ : Measure (ℕ → ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ =>
    gaussianReal 0 1 with hν₀
  let i : Fin (L' + 1) := ⟨ℓ + 1, hℓ⟩
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (L' + 1) => ℕ → ℕ → ℝ) i
  have he : MeasurePreserving e (Measure.pi fun _ : Fin (L' + 1) => ν₀)
      (ν₀.prod (Measure.pi fun _ : Fin L' => ν₀)) :=
    measurePreserving_piFinSuccAbove (fun _ => ν₀) i
  have hes : MeasurePreserving e.symm (ν₀.prod (Measure.pi fun _ : Fin L' => ν₀))
      (Measure.pi fun _ : Fin (L' + 1) => ν₀) := he.symm e
  let tr : (Fin (L' + 1) → ℕ → ℕ → ℝ) → ℕ → ℕ → ℕ → ℝ :=
    fun w k => if h : k < L' + 1 then w ⟨k, h⟩ else 0
  have hcongr : ∀ (a a' : ℕ → ℕ → ℝ) (b : Fin L' → ℕ → ℕ → ℝ) (k : ℕ), k ≤ ℓ →
      tr (e.symm (a, b)) k = tr (e.symm (a', b)) k := by
    intro a a' b k hk
    have hk' : k < L' + 1 := by omega
    have hne : (⟨k, hk'⟩ : Fin (L' + 1)) ≠ i := by
      intro h; have := congrArg Fin.val h; simp [i] at this; omega
    obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hne
    simp only [tr, hk', dite_true, e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    rw [← hz]
    simp [Fin.insertNth_apply_succAbove]
  have hnew : ∀ (a : ℕ → ℕ → ℝ) (b : Fin L' → ℕ → ℕ → ℝ), tr (e.symm (a, b)) (ℓ + 1) = a := by
    intro a b
    simp only [tr, hℓ, dite_true, e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    exact Fin.insertNth_apply_same (α := fun _ => ℕ → ℕ → ℝ) i a b
  -- conditional covariance (random, depends only on the past)
  let Kfull : ∀ n : ℕ, (Fin (L' + 1) → ℕ → ℕ → ℝ) → Matrix (Fin m) (Fin m) ℝ :=
    fun n w α β => (n : ℝ)⁻¹ * ∑ k : Fin n,
      φ (deepPreactivation d m n φ X (tr w) ℓ α k) * φ (deepPreactivation d m n φ X (tr w) ℓ β k)
  have hKfull_meas : ∀ n, Measurable (Kfull n) := by
    intro n
    refine measurable_pi_iff.2 fun α' => measurable_pi_iff.2 fun β' => ?_
    refine measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)
    exact (hφ_cont.measurable.comp
        (measurable_deepPreactivation d m n (L' + 1) φ hφ_cont.measurable X ℓ α' k)).mul
      (hφ_cont.measurable.comp
        (measurable_deepPreactivation d m n (L' + 1) φ hφ_cont.measurable X ℓ β' k))
  have hKfull_psd : ∀ n w, (Kfull n w).PosSemidef := by
    intro n w
    simpa using empirical_layer_covariance_posSemidef_multivariate 1 0 n m
      (fun j α => φ (deepPreactivation d m n φ X (tr w) ℓ α j))
  have hKfull_tendsto : TendstoInMeasure (Measure.pi fun _ : Fin (L' + 1) => ν₀) Kfull
      Filter.atTop (fun _ => Klim) := hprev
  have hK_tendsto : TendstoInMeasure (ν₀.prod (Measure.pi fun _ : Fin L' => ν₀))
      (fun n q => Kfull n (e.symm q)) Filter.atTop (fun _ => Klim) := by
    have := tendstoInMeasure_comp_measurePreserving (E := Fin m → Fin m → ℝ)
      hKfull_tendsto hes (fun n => hKfull_meas n) (measurable_const : Measurable fun _ => Klim)
    exact this
  have hK_const : ∀ n a a' b, Kfull n (e.symm (a, b)) = Kfull n (e.symm (a', b)) := by
    intro n a a' b
    have h := deepPreactivation_congr_of_eqOn d m n φ X (tr (e.symm (a, b)))
      (tr (e.symm (a', b))) ℓ fun k hk => hcongr a a' b k hk
    simp only [Kfull, h]
    rfl
  let Z : ∀ n : ℕ, (ℕ → ℕ → ℝ) × (Fin L' → ℕ → ℕ → ℝ) → (Fin n → EuclideanSpace ℝ (Fin m)) :=
    fun n q j => WithLp.toLp 2 fun α' =>
      deepPreactivation d m n φ X (tr (e.symm q)) (ℓ + 1) α' j
  have hZ_meas : ∀ n, Measurable (Z n) := by
    intro n
    refine measurable_pi_iff.2 fun j => ?_
    apply (PiLp.continuous_toLp 2 _).measurable.comp
    refine measurable_pi_iff.2 fun α' => ?_
    exact (measurable_deepPreactivation d m n (L' + 1) φ hφ_cont.measurable X (ℓ + 1) α' j).comp
      e.symm.measurable
  have hZ_law : ∀ n a b, Measure.map (fun a' => Z n (a', b)) ν₀ =
      Measure.pi fun _ : Fin n => multivariateGaussian 0 (Kfull n (e.symm (a, b))) := by
    intro n a b
    have hfun : (fun a' => Z n (a', b)) =
        (fun V : ℕ → ℕ → ℝ => fun j : Fin n => WithLp.toLp 2 fun α' : Fin m =>
          deepPreactivation d m n φ X
            (fun k => if _ : k ≤ ℓ then tr (e.symm (a, b)) k else if k = ℓ + 1 then V else 0)
            (ℓ + 1) α' j) := by
      funext a' j
      simp only [Z]
      congr 1
      funext α'
      have := deepPreactivation_congr_of_eqOn d m n φ X (tr (e.symm (a', b)))
        (fun k => if _ : k ≤ ℓ then tr (e.symm (a, b)) k else if k = ℓ + 1 then a' else 0)
        (ℓ + 1) (by
          intro k hk
          by_cases hk1 : k ≤ ℓ
          · simp [hk1, hcongr a' a b k hk1]
          · have : k = ℓ + 1 := by omega
            subst this
            simp [hnew])
      rw [this]
    rw [hfun]
    exact conditional_deepPreactivation_succ_infinite_eq_pi d m n φ X (tr (e.symm (a, b))) ℓ
  have hmain := tendsto_measure_conditional_activationProduct
    (Measure.pi fun _ : Fin L' => ν₀) ν₀ m ψ hψ_cont C hC p hp hψ_growth
    (fun n q => Kfull n (e.symm q)) Klim hKlim
    (fun n => (hKfull_meas n).comp e.symm.measurable) (fun n q => hKfull_psd n _)
    (fun n a a' b => hK_const n a a' b) hK_tendsto Z hZ_meas hZ_law α β hδ
  refine hmain.congr fun n => ?_
  rw [← he.measure_preimage_equiv]
  congr 1
  ext w
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Z, Kfull, MeasurableEquiv.symm_apply_apply]
  rfl

section DeepNNGPRecursion

/-! ## Theorem 2.13 (Deep NNGP Recursion): Main Theorems

The ambient probability space throughout is the joint depth-`L` initialization measure built in
`Initialization/DeepRecursion.lean`: a `Fin L`-indexed family of mutually independent, i.i.d.
standard-Gaussian layer weight populations `q.1 : Fin L → ℕ → ℕ → ℝ` (layer `0` doubling as the
input weight matrix, restricted to its first `d` columns — see `deepPreactivation`), together with
a readout population. `deepPreactivation`'s `W : ℕ → ℕ → ℕ → ℝ` argument is recovered from
`q.1 : Fin L → ℕ → ℕ → ℝ` by extending with the junk value `0` past layer `L`
(`fun k => if h : k < L then q.1 ⟨k, h⟩ else 0`), written out at each site below rather than named,
per the same "no extra top-level definitions" preference as the network construction above. -/

-- The base Gram matrix `(d)⁻¹ * (X α ⬝ᵥ X β)` built from the evaluation points is positive
-- semidefinite: the `σw = 1, σb = 0` case of `empirical_layer_covariance_posSemidef_multivariate`,
-- applied to the input rows themselves rather than to activated preactivations.
private lemma inputGramMatrix_posSemidef (d m : ℕ) (X : Fin m → Fin d → ℝ) :
    (show Matrix (Fin m) (Fin m) ℝ from fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)).PosSemidef := by
  simpa [dotProduct] using
    empirical_layer_covariance_posSemidef_multivariate 1 0 d m (fun k α => X α k)

/-- Given that the seed matrix `Φ0` is positive semidefinite, every term of the recursive
covariance sequence `layerCovarianceSeq 1 0 φ m Φ0` is itself positive semidefinite, and the
corresponding Gaussian activation coordinates are square-integrable. Both facts are always needed
together (to invoke `continuousWithinAt_covarianceMap` at the next depth, and to bound the
characteristic-function integrand), so they are bundled here rather than re-derived at each of the
two sites below that need them. -/
private lemma memLp_and_posSemidef_layerCovarianceSeq_of_polynomial_growth
    (m : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p) (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (Φ0 : Matrix (Fin m) (Fin m) ℝ) (hΦ0 : Φ0.PosSemidef) :
    (∀ r : ℕ, ∀ α : Fin m, MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) 2
        (multivariateGaussian 0 (layerCovarianceSeq 1 0 φ m Φ0 r))) ∧
      ∀ r : ℕ, (layerCovarianceSeq 1 0 φ m Φ0 r).PosSemidef := by
  have hφ_L2 : ∀ r : ℕ, ∀ α : Fin m,
      MemLp (fun z : EuclideanSpace ℝ (Fin m) => φ (z.ofLp α)) 2
        (multivariateGaussian 0 (layerCovarianceSeq 1 0 φ m Φ0 r)) := fun r α =>
    memLp_activation_coordinate_of_polynomial_growth m (layerCovarianceSeq 1 0 φ m Φ0 r) φ
      hφ_cont.measurable C hC p hp hφ_growth α
  exact ⟨hφ_L2, layerCovarianceSeq_posSemidef 1 0 φ hφ_cont.measurable m Φ0 hΦ0 hφ_L2⟩

/-- **Successor step for feature covariances of layer `ℓ + 1`.** If the empirical activation
covariance of layer `ℓ` converges in measure to a PSD limit `Klim`, then for any continuous
polynomial-growth feature map `ψ` the empirical feature covariance
`n⁻¹ ∑_j ψ(h_{ℓ+1,j}^α) ψ(h_{ℓ+1,j}^β)` of layer `ℓ + 1` converges in measure to the Gaussian
covariance update `∫ ψ ψ d𝒩(0, Klim)`.

This is the conditional-Chebyshev fluctuation bound (`deepPreactivation_succ_deviation_tendsto`)
combined with continuity of the covariance-update map on the PSD cone. With `ψ = φ` it is the induction
step of `deepEmpiricalCovariance_tendstoInMeasure`; with `ψ = φ'` it gives the derivative Gram matrix. -/
theorem deepFeatureCovariance_succ_tendstoInMeasure
    (d m L : ℕ) (φ ψ : ℝ → ℝ) (hφ_cont : Continuous φ) (hψ_cont : Continuous ψ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hψ_growth : ∀ x : ℝ, |ψ x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin d → ℝ) (ℓ : ℕ) (hℓ : ℓ + 1 < L)
    (Klim : Matrix (Fin m) (Fin m) ℝ) (hKlim : Klim.PosSemidef)
    (hprev : TendstoInMeasure
      (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      (fun n : ℕ => fun w : Fin L → ℕ → ℕ → ℝ => fun α β : Fin m =>
        (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ α j) *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ β j))
      Filter.atTop (fun _ => Klim)) :
    TendstoInMeasure
      (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      (fun n : ℕ => fun w : Fin L → ℕ → ℕ → ℝ => fun α β : Fin m =>
        (n : ℝ)⁻¹ * ∑ j : Fin n,
          ψ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (ℓ + 1) α j) *
          ψ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (ℓ + 1) β j))
      Filter.atTop
      (fun _ => fun α β : Fin m =>
        ∫ z : EuclideanSpace ℝ (Fin m), ψ (z.ofLp α) * ψ (z.ofLp β) ∂multivariateGaussian 0 Klim) := by
  have hempirical_pos : ∀ (n : ℕ) (w : Fin L → ℕ → ℕ → ℝ),
      (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
        φ (deepPreactivation d m n φ X
          (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ α j) *
        φ (deepPreactivation d m n φ X
          (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ β j)).PosSemidef := by
    intro n w
    simpa using empirical_layer_covariance_posSemidef_multivariate 1 0 n m
      (fun j α => φ (deepPreactivation d m n φ X
        (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ α j))
  have hmean := tendstoInMeasure_comp_of_continuousWithinAt hprev hempirical_pos
    (continuousWithinAt_covarianceMap ψ hψ_cont C hC p hp hψ_growth m Klim hKlim)
  apply tendstoInMeasure_trans ?_ hmean
  intro ε hε
  refine tendsto_matrixTail_of_tendsto_entrywise m ?_ ε hε
  intro α β δ hδ
  simpa only [Real.dist_eq] using
    deepPreactivation_succ_deviation_tendsto d m L φ ψ hφ_cont hψ_cont C hC p hp hψ_growth
      X ℓ hℓ Klim hKlim hprev α β hδ

/-- **Theorem 2.13, Part 1 (Covariance Convergence in Probability).** As width `n → ∞`, the
empirical covariance of the depth-`L` network's layer-`(ℓ+1)` post-activations converges in
probability to the deterministic recursive kernel `layerCovarianceSeq 1 0 φ m Φ0 (ℓ + 1)`, where
`Φ0 α β := (d:ℝ)⁻¹ * (X α ⬝ᵥ X β)` is the base Gram matrix.

The base-layer transport is `input_empiricalCovariance_tendstoInMeasure`.  In the successor step
the conditional Gaussian product law of the fresh layer (random empirical covariance of the previous
layer) is combined with its conditional Chebyshev bound
(`deepPreactivation_succ_deviation_tendsto`) and the relative continuous-mapping theorem. -/
theorem deepEmpiricalCovariance_tendstoInMeasure
    (d m L : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p) (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin d → ℝ) (ℓ : ℕ) (hℓ : ℓ < L) :
    TendstoInMeasure
      (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      (fun n : ℕ => fun w : Fin L → ℕ → ℕ → ℝ =>
        fun α β : Fin m => (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ α j) *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ β j))
      Filter.atTop
      (fun _ => layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) (ℓ + 1)) := by
  induction ℓ with
  | zero =>
      exact deepEmpiricalCovariance_zero_tendstoInMeasure d m L φ hφ_cont C hC p hp
        hφ_growth X (Nat.zero_lt_of_lt hℓ)
  | succ ℓ ih =>
      have hℓ' : ℓ < L := by omega
      obtain ⟨hφ_L2, hlimit_pos⟩ := memLp_and_posSemidef_layerCovarianceSeq_of_polynomial_growth
        m φ hφ_cont C hC p hp hφ_growth
        (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) (inputGramMatrix_posSemidef d m X)
      simpa [layerCovarianceSeq, dotProduct] using
        deepFeatureCovariance_succ_tendstoInMeasure d m L φ φ hφ_cont hφ_cont C hC p hp
          hφ_growth X ℓ hℓ
          (layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) (ℓ + 1))
          (hlimit_pos (ℓ + 1)) (ih hℓ')

/-- **Feature-covariance convergence for an arbitrary feature map.** For the depth-`L` network built
from the activation `φ`, the empirical covariance of the features `ψ(h_ℓ)` of layer `ℓ` converges in
measure to the Gaussian expectation `∫ ψ ψ d𝒩(0, Σ^ℓ)` against the deterministic forward kernel
`Σ^ℓ = layerCovarianceSeq 1 0 φ m Φ0 ℓ`.

With `ψ = φ` this is `deepEmpiricalCovariance_tendstoInMeasure`; with `ψ = φ'` it is the convergence
of the derivative Gram matrix `Φ'^{(n)}_ℓ → Σ̇^ℓ` needed for the backward sensitivities. -/
theorem deepEmpiricalFeatureCovariance_tendstoInMeasure
    (d m L : ℕ) (φ ψ : ℝ → ℝ) (hφ_cont : Continuous φ) (hψ_cont : Continuous ψ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p)
    (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (Cψ : ℝ) (hCψ : 0 ≤ Cψ) (pψ : ℕ) (hpψ : 0 < pψ)
    (hψ_growth : ∀ x : ℝ, |ψ x| ≤ Cψ * (1 + |x| ^ pψ))
    (X : Fin m → Fin d → ℝ) (ℓ : ℕ) (hℓ : ℓ < L) :
    TendstoInMeasure
      (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      (fun n : ℕ => fun w : Fin L → ℕ → ℕ → ℝ =>
        fun α β : Fin m => (n : ℝ)⁻¹ * ∑ j : Fin n,
          ψ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ α j) *
          ψ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) ℓ β j))
      Filter.atTop
      (fun _ => fun α β : Fin m =>
        ∫ z : EuclideanSpace ℝ (Fin m), ψ (z.ofLp α) * ψ (z.ofLp β) ∂multivariateGaussian 0
          (layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) ℓ)) := by
  cases ℓ with
  | zero =>
      simpa [deepPreactivation, layerCovarianceSeq] using
        deepEmpiricalCovariance_zero_tendstoInMeasure d m L ψ hψ_cont Cψ hCψ pψ hpψ hψ_growth X hℓ
  | succ ℓ =>
      obtain ⟨hφ_L2, hlimit_pos⟩ := memLp_and_posSemidef_layerCovarianceSeq_of_polynomial_growth
        m φ hφ_cont C hC p hp hφ_growth
        (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) (inputGramMatrix_posSemidef d m X)
      exact deepFeatureCovariance_succ_tendstoInMeasure d m L φ ψ hφ_cont hψ_cont Cψ hCψ pψ hpψ
        hψ_growth X ℓ hℓ
        (layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) (ℓ + 1))
        (hlimit_pos (ℓ + 1))
        (deepEmpiricalCovariance_tendstoInMeasure d m L φ hφ_cont C hC p hp hφ_growth X ℓ
          (by omega))

/-- Bridge: pushforward of the infinite real population restricted to `Fin n` coordinates is
`𝒩(0, I_n)`. Special case of `measurePreserving_prefixMap`. -/
lemma map_infinitePi_real_eq_gaussianReadoutMeasure (n : ℕ) :
    Measure.map (fun (rows : ℕ → ℝ) (i : Fin n) => rows i.val)
      (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) = (Measure.pi fun _ : Fin n => gaussianReal
          0 1) := by
  exact (measurePreserving_prefixMap (gaussianReal 0 1) n).map_eq

/-- Measurability of the depth-`L` network's width-`n` output map (readout weights times the
final hidden layer's activations, summed and scaled), jointly in the hidden and readout weight
populations. -/
lemma measurable_deepEval (d m L : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ)
    (X : Fin m → Fin d → ℝ) (n : ℕ) :
    Measurable (fun (q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) =>
      WithLp.toLp 2 fun α : Fin m => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, q.2.1 j.val *
        φ (deepPreactivation d m n φ X
          (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j)) := by
  change Measurable ((WithLp.toLp 2) ∘
    (fun (q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) α => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n,
      q.2.1 j.val * φ (deepPreactivation d m n φ X
        (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j)))
  refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun α => ?_)
  refine measurable_const.mul (Finset.measurable_sum _ fun j _ => ?_)
  have h_a : Measurable (fun q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ) => q.2.1 j.val) :=
    (measurable_pi_apply j.val).comp (measurable_fst.comp measurable_snd)
  have h_φ : Measurable (fun q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ) =>
      φ (deepPreactivation d m n φ X (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j)) :=
    (hφ_meas.comp (measurable_deepPreactivation d m n L φ hφ_meas X (L - 1) α j)).comp measurable_fst
  exact h_a.mul h_φ

/-- Positive semidefiniteness of the depth-`L` network's width-`n` output covariance (the
`σw = 1`, `σb = 0` case of `empirical_layer_covariance_posSemidef_multivariate`, applied to the
final hidden layer's activations). -/
lemma deepEval_covariance_posSemidef (d m n L : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (w : Fin L → ℕ → ℕ → ℝ) :
    (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
      φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
      φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j)
      ).PosSemidef := by
  simpa using empirical_layer_covariance_posSemidef_multivariate 1 0 n m
    (fun j α => φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j))

/-- For a fixed realization `w` of the hidden weights, the pushforward of the readout population
(together with one unused throwaway real coordinate, see `tendstoInDistribution_deepEval`) under
the depth-`L` network's width-`n` output map is exactly the centered multivariate Gaussian with
the width-`n` output covariance — the exact conditional normality of the readout layer
(`exact_conditional_normality_general_multivariate`), transported along
`map_infinitePi_real_eq_gaussianReadoutMeasure` from the infinite readout population down to the
finite-width `𝒩(0, I_n)` it is built on. -/
lemma map_deepEval_snd_eq_multivariateGaussian (d m n L : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (w : Fin L → ℕ → ℕ → ℝ) :
    Measure.map
      (fun r : (ℕ → ℝ) × ℝ => WithLp.toLp 2 fun α : Fin m => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n,
        r.1 j.val * φ (deepPreactivation d m n φ X
          (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j))
      ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1)) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j)) := by
  set H : Fin n → Fin m → ℝ := fun j α =>
    φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j)
    with hH_def
  have h_split : (fun r : (ℕ → ℝ) × ℝ => WithLp.toLp 2 fun α : Fin m => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n,
        r.1 j.val * H j α) =
      (fun p : (Fin n → ℝ) × ℝ => WithLp.toLp 2 fun α : Fin m =>
        (0 : ℝ) * p.2 + (1 * (n : ℝ)⁻¹.sqrt) * ∑ j : Fin n, p.1 j * H j α) ∘
        (fun r : (ℕ → ℝ) × ℝ => ((fun j : Fin n => r.1 j.val), r.2)) := by
    funext r
    simp only [Function.comp_apply]
    congr 1
    funext α
    ring
  rw [h_split, ← Measure.map_map (by fun_prop) (by fun_prop),
    show (fun r : (ℕ → ℝ) × ℝ => ((fun j : Fin n => r.1 j.val), r.2)) =
      Prod.map (fun (rows : ℕ → ℝ) (j : Fin n) => rows j.val) id from rfl,
    ← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    map_infinitePi_real_eq_gaussianReadoutMeasure, Measure.map_id]
  simpa using exact_conditional_normality_general_multivariate 1 0 n m H

/-- **Law of Total Expectation for the depth-`L` network's characteristic function.** The
characteristic function of the width-`n` output distribution is the expectation, over the hidden
weights, of the conditional characteristic function `exp(-t·Φ_L^{(n)}(w)·t/2)` given by
`map_deepEval_snd_eq_multivariateGaussian` and `charFun_multivariateGaussian`. Mirrors
`charFun_outputMeasure`'s proof shape (Fubini on the product measure). -/
lemma charFun_map_deepEval (d m L : ℕ) (φ : ℝ → ℝ) (hφ_meas : Measurable φ) (X : Fin m → Fin d → ℝ)
    (n : ℕ) (t : EuclideanSpace ℝ (Fin m)) :
    charFun (Measure.map
      (fun (q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) => WithLp.toLp 2 fun α : Fin m =>
        (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, q.2.1 j.val * φ (deepPreactivation d m n φ X
          (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j))
      ((Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
        ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1)))) t =
      ∫ w : Fin L → ℕ → ℕ → ℝ, Complex.exp (-Complex.ofReal (t.ofLp ⬝ᵥ
        (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))
        *ᵥ t.ofLp) / 2)
      ∂(Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) := by
  have h_meas := measurable_deepEval d m L φ hφ_meas X n
  have h_inner : Measurable (fun q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ) =>
      ⟪(WithLp.toLp 2 fun α : Fin m => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, q.2.1 j.val *
        φ (deepPreactivation d m n φ X (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j)
        : EuclideanSpace ℝ (Fin m)), t⟫) :=
    (continuous_id.inner continuous_const).measurable.comp h_meas
  have h_exp_meas : AEStronglyMeasurable
      (fun q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ) =>
        Complex.exp (⟪(WithLp.toLp 2 fun α : Fin m => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, q.2.1 j.val *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j)
          : EuclideanSpace ℝ (Fin m)), t⟫ * Complex.I))
      ((Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
        ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1))) :=
    (Complex.continuous_exp.measurable.comp
      ((Complex.measurable_ofReal.comp h_inner).mul_const Complex.I)).aestronglyMeasurable
  rw [charFun_apply, integral_map h_meas.aemeasurable (by fun_prop),
    integral_prod _ (Integrable.of_bound h_exp_meas 1
      (ae_of_all _ fun p => (Complex.norm_exp_ofReal_mul_I _).le))]
  congr 1
  funext w
  have h_meas_w : Measurable (fun r : (ℕ → ℝ) × ℝ => WithLp.toLp 2 fun α : Fin m =>
      (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, r.1 j.val * φ (deepPreactivation d m n φ X
        (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j)) :=
    h_meas.comp (measurable_const.prodMk measurable_id)
  calc
    (∫ r : (ℕ → ℝ) × ℝ, Complex.exp (⟪(WithLp.toLp 2 fun α : Fin m => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n,
        r.1 j.val * φ (deepPreactivation d m n φ X
          (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) : EuclideanSpace ℝ (Fin m)), t⟫
        * Complex.I) ∂((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1))) =
        charFun (Measure.map (fun r : (ℕ → ℝ) × ℝ => WithLp.toLp 2 fun α : Fin m =>
          (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, r.1 j.val * φ (deepPreactivation d m n φ X
            (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j))
          ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1))) t := by
      rw [charFun_apply, integral_map h_meas_w.aemeasurable (by fun_prop)]
    _ = charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
            φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
            φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))) t := by
      rw [map_deepEval_snd_eq_multivariateGaussian d m n L φ X w]
    _ = Complex.exp (-Complex.ofReal (t.ofLp ⬝ᵥ (show Matrix (Fin m) (Fin m) ℝ from fun α β =>
          (n : ℝ)⁻¹ * ∑ j : Fin n,
            φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
            φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))
          *ᵥ t.ofLp) / 2) := by
      rw [charFun_multivariateGaussian (deepEval_covariance_posSemidef d m n L φ X w)]
      simp only [inner_zero_right, ofReal_zero, zero_mul, zero_sub]
      congr 1
      ring

/-- The characteristic integrand for the depth-`L` network's width-`n` output covariance is
bounded by `1` (since the covariance is positive semidefinite). -/
lemma norm_charFun_deepEval_le_one (d m n L : ℕ) (φ : ℝ → ℝ) (X : Fin m → Fin d → ℝ)
    (w : Fin L → ℕ → ℕ → ℝ) (t : EuclideanSpace ℝ (Fin m)) :
    ‖Complex.exp (-Complex.ofReal (t.ofLp ⬝ᵥ
      (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
        φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
        φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))
      *ᵥ t.ofLp) / 2)‖ ≤ 1 :=
  norm_exp_neg_ofReal_div_two_le_one (by
    simpa using empirical_layer_covariance_nonneg_multivariate 1 0 n m
      (fun j α => φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j))
      t)

/-- Measurability, in the hidden weights `w`, of the depth-`L` network's width-`n` characteristic
integrand. -/
lemma aestronglyMeasurable_charFun_deepEval (d m n L : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (X : Fin m → Fin d → ℝ) (t : EuclideanSpace ℝ (Fin m)) :
    AEStronglyMeasurable (fun w : Fin L → ℕ → ℕ → ℝ => Complex.exp (-Complex.ofReal (t.ofLp ⬝ᵥ
      (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
        φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
        φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))
      *ᵥ t.ofLp) / 2))
      (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) := by
  have h_quad : Measurable (fun w : Fin L → ℕ → ℕ → ℝ => t.ofLp ⬝ᵥ
      (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
        φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
        φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))
      *ᵥ t.ofLp) := by
    have h_eq : (fun w : Fin L → ℕ → ℕ → ℝ => t.ofLp ⬝ᵥ
        (show Matrix (Fin m) (Fin m) ℝ from fun α β => (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))
        *ᵥ t.ofLp) =
        fun w => ∑ α : Fin m, ∑ β : Fin m, t.ofLp α * ((n : ℝ)⁻¹ * ∑ j : Fin n,
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))
          * t.ofLp β := by
      funext w
      rw [Matrix.dot_mulVec_eq_sum_sum, Finset.sum_comm]
    rw [h_eq]
    refine Finset.measurable_sum _ fun α _ => Finset.measurable_sum _ fun β _ => ?_
    have h_cov := measurable_deepFeatureAverage d m n L φ φ hφ_cont.measurable
      hφ_cont.measurable X (L - 1) α β
    exact (measurable_const.mul h_cov).mul measurable_const
  exact (Complex.measurable_exp.comp
    (((Complex.measurable_ofReal.comp h_quad).neg).div_const 2)).aestronglyMeasurable

/-- Pointwise characteristic function convergence for the depth-`L` network's output under an
arbitrary sequence of empirical covariances converging in measure to the limiting forward kernel.
This decouples the Step 6 output-layer argument from the specific inductive proof of Part 1. -/
lemma tendsto_charFun_map_deepEval_of_covariance_tendsto
    (d m L : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p) (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin d → ℝ) (t : EuclideanSpace ℝ (Fin m))
    (hP : TendstoInMeasure
      (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      (fun n : ℕ => fun w : Fin L → ℕ → ℕ → ℝ =>
        fun α β : Fin m => (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))
      Filter.atTop
      (fun _ => layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) L)) :
    Filter.Tendsto (fun (n : ℕ) => charFun (Measure.map
        (fun (q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) => WithLp.toLp 2 fun α : Fin m =>
          (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, q.2.1 j.val * φ (deepPreactivation d m n φ X
            (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j))
        ((Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
            Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
          ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1)))) t)
      Filter.atTop
      (nhds (charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) L)) t)) := by
  obtain ⟨_, hΦr_pos⟩ := memLp_and_posSemidef_layerCovarianceSeq_of_polynomial_growth
    m φ hφ_cont C hC p hp hφ_growth
    (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) (inputGramMatrix_posSemidef d m X)
  simp_rw [charFun_map_deepEval d m L φ hφ_cont.measurable X _ t]
  have h_comp := tendstoInMeasure_comp_of_continuousAt hP
    (continuous_charFun_integrand t).continuousAt
    (g := fun M : Matrix (Fin m) (Fin m) ℝ =>
      Complex.exp (-Complex.ofReal (t.ofLp ⬝ᵥ M *ᵥ t.ofLp) / 2))
  have h_lim := tendsto_integral_of_tendstoInMeasure_of_bounded h_comp
    (fun n => aestronglyMeasurable_charFun_deepEval d m n L φ hφ_cont X t) 1
    (fun n => ae_of_all _ fun w => norm_charFun_deepEval_le_one d m n L φ X w t)
  rw [charFun_multivariateGaussian (hΦr_pos L)]
  simp only [inner_zero_right, ofReal_zero, zero_mul, zero_sub, neg_div]
  simpa [integral_const, neg_div] using h_lim

/-- **Pointwise characteristic function convergence for the depth-`L` network's output**
(Theorem 2.13 Part 2, Steps 2-5): combines the Law of Total Expectation
(`charFun_map_deepEval`) with Part 1 (`deepEmpiricalCovariance_tendstoInMeasure`) via the
continuous-mapping and bounded-convergence lemmas. -/
lemma tendsto_charFun_map_deepEval (d m L : ℕ) (hL : 0 < L) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p) (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin d → ℝ) (t : EuclideanSpace ℝ (Fin m)) :
    Filter.Tendsto (fun (n : ℕ) => charFun (Measure.map
        (fun (q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) => WithLp.toLp 2 fun α : Fin m =>
          (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, q.2.1 j.val * φ (deepPreactivation d m n φ X
            (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j))
        ((Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
            Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
          ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1)))) t)
      Filter.atTop
      (nhds (charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
        (layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) L)) t)) := by
  have hL1 : L - 1 + 1 = L := by omega
  have hP1 := deepEmpiricalCovariance_tendstoInMeasure d m L φ hφ_cont C hC p hp hφ_growth X
    (L - 1) (by omega)
  rw [hL1] at hP1
  exact tendsto_charFun_map_deepEval_of_covariance_tendsto d m L φ hφ_cont C hC p hp hφ_growth X t hP1

/-- **Theorem 2.13, Part 2 (Output Convergence in Distribution - Standalone Form).** Under any
probability space where the depth-`L` network's layer-`L` empirical covariance converges in
probability to `layerCovarianceSeq 1 0 φ m Φ0 L`, the output vector converges in distribution to
the centered multivariate Gaussian `𝒩(0, Φ_L)`.  This theorem is mathematically self-contained
and establishes Step 6 of the Deep NNGP Recursion. -/
theorem tendstoInDistribution_deepEval_of_covariance_tendsto
    (d m L : ℕ) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p) (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin d → ℝ)
    (hP : TendstoInMeasure
      (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)
      (fun n : ℕ => fun w : Fin L → ℕ → ℕ → ℝ =>
        fun α β : Fin m => (n : ℝ)⁻¹ * ∑ j : Fin n,
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) α j) *
          φ (deepPreactivation d m n φ X (fun k => if h : k < L then w ⟨k, h⟩ else 0) (L - 1) β j))
      Filter.atTop
      (fun _ => layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) L)) :
    TendstoInDistribution
      (fun (n : ℕ) (q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) =>
        WithLp.toLp 2 fun α : Fin m => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, q.2.1 j.val *
          φ (deepPreactivation d m n φ X
              (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j))
      Filter.atTop id
      (fun _ => (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
        ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1)))
      (multivariateGaussian 0
        (layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) L)) where
  forall_aemeasurable n := (measurable_deepEval d m L φ hφ_cont.measurable X n).aemeasurable
  aemeasurable_limit := measurable_id.aemeasurable
  tendsto := by
    have h_weak : Filter.Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ (Fin m)))
        (fun n : ℕ => ⟨Measure.map
            (fun (q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) => WithLp.toLp 2 fun α : Fin m =>
              (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, q.2.1 j.val * φ (deepPreactivation d m n φ X
                (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j))
            ((Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
                Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
              ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1))),
          (Measure.isProbabilityMeasure_map_iff
            (measurable_deepEval d m L φ hφ_cont.measurable X n).aemeasurable).mpr inferInstance⟩)
        Filter.atTop
        (nhds ⟨multivariateGaussian (0 : EuclideanSpace ℝ (Fin m))
          (layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) L),
          inferInstance⟩) := by
      apply ProbabilityMeasure.tendsto_of_tendsto_charFun
      intro t
      exact tendsto_charFun_map_deepEval_of_covariance_tendsto d m L φ hφ_cont C hC p hp hφ_growth X t hP
    convert! h_weak
    exact congrArg nhds (Subtype.ext Measure.map_id)

/-- **Theorem 2.13, Part 2 (Output Convergence in Distribution).** As width `n → ∞`, the depth-`L`
network's output vector `f_m(θ) = n⁻¹ᐟ² ∑ⱼ aⱼ φ(h_L(X^α)ⱼ)` converges in distribution to the
centered multivariate Gaussian `𝒩(0, Φ_L)`, `Φ_L := layerCovarianceSeq 1 0 φ m Φ0 L`.  (The ambient
sample space carries one extra, unused `ℝ`-valued coordinate `q.2.2` alongside the readout
population `q.2.1 : ℕ → ℝ`, purely so the proof can invoke
`exact_conditional_normality_general_multivariate` — whose general `σw, σb` signature includes a
bias-noise slot — with `σb := 0` at no extra cost, rather than adding a marginalization lemma.
The `hφ_L2` hypothesis, matching `layerCovarianceSeq_posSemidef`'s, is needed so the limit
`Φ_L` is positive semidefinite, which `charFun_multivariateGaussian` needs for its closed form.)

**Proof.**  Mirrors `tendstoInDistribution_evalVector` (Theorem 3) step for step, factored through
the helper lemmas above (`measurable_deepEval`, `map_deepEval_snd_eq_multivariateGaussian`,
`charFun_map_deepEval`, `tendsto_charFun_map_deepEval`):

1. *Exact conditional normality*: `exact_conditional_normality_general_multivariate 1 0 n m H`
   with `H j α := φ (deepPreactivation … (L - 1) α j)` gives, with **zero new proof**, that
   `f_m(θ) | (hidden weights) ~ 𝒩(0, Φ_L^{(n)})` exactly, where `Φ_L^{(n)}` is the width-`n`
   empirical covariance from Part 1 at `ℓ = L - 1` (`map_deepEval_snd_eq_multivariateGaussian`).
2. *Law of total expectation* for the characteristic function via Fubini on the product measure,
   mirroring `charFun_outputMeasure`'s proof shape (`charFun_map_deepEval`).
3. *Boundedness*: reuse `norm_exp_neg_ofReal_div_two_le_one` verbatim (PosSemidef of `Φ_L^{(n)}`,
   `norm_charFun_deepEval_le_one`).
4. *Continuity* of `M ↦ exp(-t·M·t/2)`: reuse `continuous_charFun_integrand` verbatim.
5. *Passing the limit*: `tendsto_integral_of_tendstoInMeasure_of_bounded` (already proved above)
   applied to Part 1 at `ℓ = L - 1`, in place of Theorem 3's dominated-convergence step (Part 1
   only supplies convergence in probability, not the a.s. convergence Theorem 3 had from
   Kolmogorov's SLLN) — assembled as `tendsto_charFun_map_deepEval`.
6. *Lévy continuity*: `ProbabilityMeasure.tendsto_of_tendsto_charFun`, reused directly.

The hypotheses otherwise match Part 1's exactly (continuity and polynomial growth, not just
measurability), since this theorem invokes Part 1 at `ℓ = L - 1`. -/
theorem tendstoInDistribution_deepEval
    (d m L : ℕ) (hL : 0 < L) (φ : ℝ → ℝ) (hφ_cont : Continuous φ)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ) (hp : 0 < p) (hφ_growth : ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ p))
    (X : Fin m → Fin d → ℝ) :
    TendstoInDistribution
      (fun (n : ℕ) (q : (Fin L → ℕ → ℕ → ℝ) × ((ℕ → ℝ) × ℝ)) =>
        WithLp.toLp 2 fun α : Fin m => (n : ℝ)⁻¹.sqrt * ∑ j : Fin n, q.2.1 j.val *
          φ (deepPreactivation d m n φ X
              (fun k => if h : k < L then q.1 ⟨k, h⟩ else 0) (L - 1) α j))
      Filter.atTop id
      (fun _ => (Measure.pi fun _ : Fin L => Measure.infinitePi fun _ : ℕ =>
          Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod
        ((Measure.infinitePi fun _ : ℕ => gaussianReal 0 1).prod (gaussianReal 0 1)))
      (multivariateGaussian 0
        (layerCovarianceSeq 1 0 φ m (fun α β => (d : ℝ)⁻¹ * (X α ⬝ᵥ X β)) L)) := by
  have hL1 : L - 1 + 1 = L := by omega
  have hP1 := deepEmpiricalCovariance_tendstoInMeasure d m L φ hφ_cont C hC p hp hφ_growth X
    (L - 1) (by omega)
  rw [hL1] at hP1
  exact tendstoInDistribution_deepEval_of_covariance_tendsto d m L φ hφ_cont C hC p hp hφ_growth X hP1

end DeepNNGPRecursion

end NTK

end
