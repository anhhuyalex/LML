/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.Renormalization.MLPInitialization
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Moments.Variance

/-!
# Induced laws and randomized neural-network layers

The primary semantics is a pushforward measure.  Kernel-valued randomized maps then make
independently initialized layers compositional without using formal products of Dirac deltas.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory ComplexConjugate

namespace NeuralNetwork

universe uΘ uX uY uA uB

variable {A : Type uA} {E S : Type uB} {ι : Type uX} {κ : Type uY}

/-- An architecture-independent model whose evaluator is jointly measurable in parameters and
input. -/
structure ParamModel (Θ : Type uΘ) (X : Type uX) (Y : Type uY)
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Y] where
  /-- Evaluate parameters `θ : Θ` at an input `x : X`. -/
  eval : Θ → X → Y
  /-- Joint measurability of evaluation in the parameter and input variables. -/
  measurable_eval : Measurable fun p : Θ × X => eval p.1 p.2

namespace ParamModel

variable {Θ : Type uΘ} {X : Type uX} {Y : Type uY}
  [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Y]

/-- Evaluate one parameter value on every entry of a dataset. -/
def evalBatch (F : ParamModel Θ X Y) (D : A → X) (θ : Θ) : A → Y :=
  fun a => F.eval θ (D a)

theorem measurable_eval_fixed (F : ParamModel Θ X Y) (x : X) :
    Measurable fun θ => F.eval θ x := by
  exact F.measurable_eval.comp (measurable_id.prodMk measurable_const)

theorem measurable_evalBatch (F : ParamModel Θ X Y) (D : A → X) :
    Measurable (F.evalBatch D) := by
  exact measurable_pi_lambda _ fun a => F.measurable_eval_fixed (D a)

/-- Distribution of the finite-dataset outputs induced by a parameter law. -/
def outputLaw (F : ParamModel Θ X Y) (D : A → X) (μ : Measure Θ) : Measure (A → Y) :=
  μ.map (F.evalBatch D)

/-- A measurable pushforward of a probability measure is a probability measure.

Informal proof: evaluate `μ.map (F.evalBatch D)` on the whole space; measurability of the batched
evaluator turns the preimage of `univ` into `univ`, whose mass is one. See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/Map.html>. -/
instance instIsProbabilityMeasureOutputLaw (F : ParamModel Θ X Y) (D : A → X)
    (μ : Measure Θ) [IsProbabilityMeasure μ] : IsProbabilityMeasure (F.outputLaw D μ) := by
  unfold outputLaw
  exact μ.isProbabilityMeasure_map (F.measurable_evalBatch D).aemeasurable

/-- Observable formula for the induced output law.

Informal proof: unfold `outputLaw` and apply `MeasureTheory.integral_map` using
`measurable_evalBatch`; the strong-measurability hypothesis is exactly the remaining premise.
See <https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Integral/Bochner/Basic.html>. -/
theorem integral_outputLaw [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ParamModel Θ X Y) (D : A → X) (μ : Measure Θ) (G : (A → Y) → E)
    (hG : AEStronglyMeasurable G (F.outputLaw D μ)) :
    ∫ y, G y ∂F.outputLaw D μ = ∫ θ, G (F.evalBatch D θ) ∂μ := by
  unfold outputLaw at hG ⊢
  exact integral_map (F.measurable_evalBatch D).aemeasurable hG

/-- Conditional output kernel at fixed parameters, with datasets as inputs. -/
def deterministicOutputKernel (F : ParamModel Θ X Y) (θ : Θ) : Kernel (A → X) (A → Y) :=
  Kernel.deterministic (fun D a => F.eval θ (D a)) <| by
    exact measurable_pi_lambda _ fun a =>
      F.measurable_eval.comp (measurable_const.prodMk (measurable_pi_apply a))

/-- Deterministic conditional-output kernel with the parameter as kernel input and the dataset
fixed.  This orientation is the one composed with a parameter measure. -/
def parameterOutputKernel (F : ParamModel Θ X Y) (D : A → X) : Kernel Θ (A → Y) :=
  Kernel.deterministic (F.evalBatch D) (F.measurable_evalBatch D)

/-- Integrating deterministic conditional outputs against the parameter law is the output
pushforward. -/
theorem parameterOutputKernel_comp_eq_outputLaw (F : ParamModel Θ X Y) (D : A → X)
    (μ : Measure Θ) : F.parameterOutputKernel D ∘ₘ μ = F.outputLaw D μ := by
  unfold parameterOutputKernel outputLaw
  exact Measure.deterministic_comp_eq_map (F.measurable_evalBatch D)

@[simp] theorem deterministicOutputKernel_apply (F : ParamModel Θ X Y) (θ : Θ)
    (D : A → X) : F.deterministicOutputKernel θ D = Measure.dirac (F.evalBatch D θ) := by
  rw [deterministicOutputKernel, Kernel.deterministic_apply]
  rfl

end ParamModel

namespace MLPShape

/-- A fixed MLP architecture as an architecture-independent measurable parameterized model. -/
def paramModel {m n : ℕ} (S : MLPShape m n) (σ : ℝ → ℝ) (hσ : Measurable σ) :
    ParamModel S.Params (Fin m → ℝ) (Fin n → ℝ) where
  eval := S.eval σ
  measurable_eval := S.measurable_eval hσ

@[simp] theorem paramModel_eval {m n : ℕ} (S : MLPShape m n) (σ : ℝ → ℝ)
    (hσ : Measurable σ) (θ : S.Params) (x : Fin m → ℝ) :
    (S.paramModel σ hσ).eval θ x = S.eval σ θ x := rfl

/-- The output law of `f(x; θ)` on a dataset is exactly the parameter-law pushforward, now
specialized to an MLP shape. -/
theorem outputLaw_eq_map_eval {m n : ℕ} (S : MLPShape m n) (σ : ℝ → ℝ)
    (hσ : Measurable σ) (D : A → Fin m → ℝ) (μ : Measure S.Params) :
    (S.paramModel σ hσ).outputLaw D μ =
      μ.map (fun θ a => S.eval σ θ (D a)) := rfl

/-- The Chapter 2 output ensemble is the pushforward of the explicit full-network Gaussian
parameter law. -/
theorem outputLaw_gaussianInit_eq_map {m n : ℕ} (S : MLPShape m n) (σ : ℝ → ℝ)
    (hσ : Measurable σ) (p : S.Hyperparams) (D : A → Fin m → ℝ) :
    (S.paramModel σ hσ).outputLaw D (S.gaussianInit p) =
      (S.gaussianInit p).map (fun θ a => S.eval σ θ (D a)) := rfl

end MLPShape

/-- Discoverability wrapper for Bochner integration against a Dirac measure. -/
theorem integral_dirac_apply [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace S] [MeasurableSingletonClass S] (f : S → E) (s : S) :
    ∫ x, f x ∂Measure.dirac s = f s := by
  exact integral_dirac f s

/-- The identity random variable has zero variance under a point mass. -/
theorem variance_id_dirac (s : ℝ) : Var[id; Measure.dirac s] = 0 := by
  exact variance_dirac s

/-- The source's Dirac mean equation. -/
theorem integral_id_dirac (s : ℝ) : ∫ z, z ∂Measure.dirac s = s := by
  exact integral_dirac _ _

/-- The source's Dirac second-moment equation. -/
theorem integral_sq_dirac (s : ℝ) : ∫ z, z ^ 2 ∂Measure.dirac s = s ^ 2 := by
  exact integral_dirac _ _

/-- The source's Dirac normalization equation. -/
theorem dirac_apply_univ (s : S) [MeasurableSpace S] :
    Measure.dirac s Set.univ = 1 := by
  simp

/-- A probability law is self-averaging at `s` when every bounded continuous observable has the
same expectation as under the point mass at `s`. -/
def SelfAveragingAt (μ : Measure ℝ) (s : ℝ) : Prop :=
  ∀ f : BoundedContinuousFunction ℝ ℝ, ∫ x, f x ∂μ = f s

theorem selfAveragingAt_dirac (s : ℝ) : SelfAveragingAt (Measure.dirac s) s := fun f =>
  integral_dirac f s

-- Agreement with the point mass at `s` on every bounded continuous observable forces the
-- measures to be equal: bounded continuous functions separate finite Borel measures on `ℝ`.
private lemma eq_dirac_of_selfAveragingAt (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : ℝ)
    (hμ : SelfAveragingAt μ s) : μ = Measure.dirac s :=
  MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure (μ := μ) (ν := Measure.dirac s)
    fun f => (hμ f).trans (integral_dirac f s).symm

/-- Self-averaging for every bounded continuous observable characterizes a Dirac law.

Informal proof: bounded continuous functions separate finite Borel measures on `ℝ`.  The defining
identity says that `μ` and `dirac s` integrate every such function equally, so the measures are
equal; the reverse direction is `integral_dirac`.  See the bounded-continuous characterization of
weak equality in Mathlib's finite-measure API:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/Measure/FiniteMeasure.html>. -/
theorem selfAveragingAt_iff_eq_dirac (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : ℝ) :
    SelfAveragingAt μ s ↔ μ = Measure.dirac s :=
  ⟨eq_dirac_of_selfAveragingAt μ s, fun hμ => hμ ▸ selfAveragingAt_dirac s⟩

/-- Characteristic function of a deterministic real law. -/
theorem charFun_dirac (s t : ℝ) :
    charFun (Measure.dirac s) t = Complex.exp ((t * s : ℂ) * Complex.I) := by
  rw [MeasureTheory.charFun_dirac]
  congr 2
  simp [mul_comm]

/-- A Gaussian law bundled with its probability certificate. -/
def gaussianProbabilityMeasure (m : ℝ) (v : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal m v, inferInstance⟩

/-- A Dirac law bundled as a probability measure. -/
def diracProbabilityMeasure (s : ℝ) : ProbabilityMeasure ℝ :=
  ⟨Measure.dirac s, inferInstance⟩

/-- The source's zero-variance Gaussian limit, stated rigorously as weak convergence of probability
measures.

Informal proof: write a Gaussian sample as `s + sqrt(v) Z` with `Z` standard normal.  As `v → 0`,
this converges to `s` in probability, hence in distribution.  Equivalently, dominated convergence
applied to every bounded continuous test function gives the weak limit.  See
<https://en.wikipedia.org/wiki/Convergence_of_random_variables#Convergence_in_distribution>. -/
theorem tendsto_gaussianProbabilityMeasure_zero_variance (s : ℝ) :
    Tendsto (gaussianProbabilityMeasure s) (nhds 0) (nhds (diracProbabilityMeasure s)) := by
  rw [tendsto_nhds_iff_seq_tendsto]
  intro u hu
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun ?_
  intro t
  have hlin : Tendsto (fun n : ℕ => ((u n : ℝ≥0) : ℂ) * (t : ℂ) ^ 2 / 2)
      atTop (nhds (((0 : ℝ≥0) : ℂ) * (t : ℂ) ^ 2 / 2)) := by
    exact (((continuous_subtype_val.tendsto 0).comp hu).ofReal.mul tendsto_const_nhds).div_const 2
  have hneg : Tendsto (fun n : ℕ => -(((u n : ℝ≥0) : ℂ) * (t : ℂ) ^ 2 / 2))
      atTop (nhds (-(((0 : ℝ≥0) : ℂ) * (t : ℂ) ^ 2 / 2))) := hlin.neg
  have hexp : Tendsto (fun n : ℕ => Complex.exp ((t : ℂ) * s * Complex.I -
        ((u n : ℝ≥0) : ℂ) * (t : ℂ) ^ 2 / 2))
      atTop (nhds (Complex.exp ((t : ℂ) * s * Complex.I -
        ((0 : ℝ≥0) : ℂ) * (t : ℂ) ^ 2 / 2))) := by
    have harg : Tendsto (fun n : ℕ => (t : ℂ) * s * Complex.I +
        -(((u n : ℝ≥0) : ℂ) * (t : ℂ) ^ 2 / 2))
        atTop (nhds ((t : ℂ) * s * Complex.I +
          -(((0 : ℝ≥0) : ℂ) * (t : ℂ) ^ 2 / 2))) :=
      tendsto_const_nhds.add hneg
    change Tendsto (Complex.exp ∘ fun n : ℕ => (t : ℂ) * s * Complex.I +
        -(((u n : ℝ≥0) : ℂ) * (t : ℂ) ^ 2 / 2)) atTop
      (nhds (Complex.exp ((t : ℂ) * s * Complex.I +
        -(((0 : ℝ≥0) : ℂ) * (t : ℂ) ^ 2 / 2))))
    exact (Complex.continuous_exp.tendsto _).comp harg
  have htarget : Complex.exp ((t : ℂ) * s * Complex.I - ((0 : ℝ≥0) : ℂ) * (t : ℂ) ^ 2 / 2) =
      charFun (diracProbabilityMeasure s) t := by
    simp [diracProbabilityMeasure]
  have hrew : (fun n : ℕ => charFun ((gaussianProbabilityMeasure s ∘ u) n) t) =
      fun n : ℕ => Complex.exp ((t : ℂ) * s * Complex.I -
        ((u n : ℝ≥0) : ℂ) * (t : ℂ) ^ 2 / 2) := by
    funext n
    simp [Function.comp, gaussianProbabilityMeasure, charFun_gaussianReal]
  rw [hrew, ← htarget]
  exact hexp

/-- The unregularized Fourier kernel in the source's formal delta representation is not Lebesgue
integrable.

Informal proof: the complex exponential has norm one for every real frequency, so its norm has
infinite integral over `ℝ`.  Thus the displayed Fourier integral cannot be a Bochner/Lebesgue
integral; it must be interpreted distributionally.  See
<https://en.wikipedia.org/wiki/Dirac_delta_function#Fourier_transform>. -/
theorem not_integrable_dirac_fourierKernel (z s : ℝ) :
    ¬ Integrable (fun Λ : ℝ => Complex.exp ((Λ * (z - s) : ℂ) * Complex.I)) := by
  intro h
  -- The integrand has norm one at every frequency, so integrability would force the constant
  -- function `1` to be integrable against Lebesgue measure, contradicting `volume univ = ∞`.
  have hrew : (fun Λ : ℝ => ‖Complex.exp ((Λ * (z - s) : ℂ) * Complex.I)‖ₑ) =
      fun _ : ℝ => (1 : ℝ≥0∞) := by
    funext Λ
    simpa [Complex.ofReal_mul, Complex.ofReal_sub] using
      Complex.enorm_exp_ofReal_mul_I (Λ * (z - s))
  have hln : ∫⁻ Λ : ℝ, (1 : ℝ≥0∞) ∂volume < ∞ := by
    rw [← hrew]
    exact h.2
  rw [lintegral_one] at hln
  rw [Real.volume_univ] at hln
  exact (lt_irrefl ∞) hln

/-- For positive variance, the regularized Fourier integral in the source is an ordinary integral
and equals the Gaussian density.

Informal proof: this is the Fourier transform of the centered Gaussian.  Complete the square (or
apply the already-formalized Gaussian Fourier transform), then translate by `s`; the factor
`1/(2π)` yields variance `K`.  See Mathlib's Gaussian Fourier transform development:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.html>. -/
theorem gaussianPDFReal_eq_regularizedFourierIntegral (s z : ℝ) (K : ℝ≥0) (hK : K ≠ 0) :
    (gaussianPDFReal s K z : ℂ) =
      (1 / (2 * Real.pi) : ℂ) *
        ∫ Λ : ℝ, Complex.exp
          (-(K : ℂ) / 2 * (Λ : ℂ) ^ 2 + Complex.I * (Λ : ℂ) * ((z - s : ℝ) : ℂ)) := by
  let b : ℂ := (K : ℂ) / 2
  let t : ℂ := ((z - s : ℝ) : ℂ)
  have hKpos : 0 < (K : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hK)
  have hK_ne : (K : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hKpos)
  have h2pi_pos : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have h2piK_pos : 0 < 2 * Real.pi * (K : ℝ) := mul_pos h2pi_pos hKpos
  have h2pi_over_K_pos : 0 < 2 * Real.pi / (K : ℝ) := div_pos h2pi_pos hKpos
  have hb : 0 < b.re := by
    dsimp [b]
    change 0 < ((K : ℂ) / ((2 : ℝ) : ℂ)).re
    rw [← Complex.ofReal_div]
    simp only [Complex.ofReal_re]
    exact div_pos hKpos (by norm_num : (0 : ℝ) < 2)
  -- The regularized Fourier integrand is exactly the Fourier integral of the Gaussian
  -- `cexp (I * t * Λ) * cexp (-b * Λ²)`, evaluated by `fourierIntegral_gaussian`.
  have hInt : (∫ Λ : ℝ, Complex.exp
        (-(K : ℂ) / 2 * (Λ : ℂ) ^ 2 + Complex.I * (Λ : ℂ) * ((z - s : ℝ) : ℂ))) =
      ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) * Complex.exp (-t ^ 2 / (4 * b)) := by
    calc
      (∫ Λ : ℝ, Complex.exp (-(K : ℂ) / 2 * (Λ : ℂ) ^ 2 +
            Complex.I * (Λ : ℂ) * ((z - s : ℝ) : ℂ))) =
          (∫ Λ : ℝ, Complex.exp (Complex.I * t * (Λ : ℂ)) *
            Complex.exp (-b * (Λ : ℂ) ^ 2)) := by
        congr 1
        funext Λ
        rw [← Complex.exp_add]
        congr 1
        dsimp [b, t]
        ring
      _ = ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) * Complex.exp (-t ^ 2 / (4 * b)) :=
        fourierIntegral_gaussian hb t
  -- The normalization constant `1/(2π)` times `(π/b)^(1/2)` is the inverse square root of
  -- `2πK`, and the translated exponent is `-(z - s)² / (2K)`.
  have hConst : (1 / (2 * Real.pi) : ℂ) * ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) =
      (Real.sqrt (2 * Real.pi * (K : ℝ)))⁻¹ := by
    have hbase : (Real.pi : ℂ) / b = ((2 * Real.pi / (K : ℝ) : ℝ) : ℂ) := by
      change (Real.pi : ℂ) / ((K : ℂ) / ((2 : ℝ) : ℂ)) = ((2 * Real.pi / (K : ℝ) : ℝ) : ℂ)
      rw [← Complex.ofReal_div]
      rw [← Complex.ofReal_div]
      exact_mod_cast (by
        field_simp [hKpos.ne', (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num)
    have hcpow : ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) =
        (Real.sqrt (2 * Real.pi / (K : ℝ)) : ℂ) := by
      calc
        ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) = ((2 * Real.pi / (K : ℝ) : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
          rw [hbase]
        _ = (Real.sqrt (2 * Real.pi / (K : ℝ)) : ℂ) := by
          have hE : (1 / 2 : ℂ) = (((1 / 2 : ℝ) : ℂ)) := by norm_num
          rw [hE]
          rw [← Complex.ofReal_cpow h2pi_over_K_pos.le (1 / 2 : ℝ)]
          congr 1
          rw [Real.sqrt_eq_rpow]
    rw [hcpow]
    have hReal : (1 / (2 * Real.pi)) * Real.sqrt (2 * Real.pi / (K : ℝ)) =
        (Real.sqrt (2 * Real.pi * (K : ℝ)))⁻¹ := by
      rw [Real.sqrt_div h2pi_pos.le (K : ℝ), Real.sqrt_mul h2pi_pos.le (K : ℝ)]
      field_simp [ne_of_gt (Real.sqrt_pos.2 h2pi_pos), ne_of_gt hKpos]
      nlinarith [Real.sq_sqrt h2pi_pos.le, Real.sq_sqrt hKpos.le]
    exact_mod_cast hReal
  have hExp : Complex.exp (-t ^ 2 / (4 * b)) =
      Complex.exp (-((z - s) ^ 2) / (2 * (K : ℝ))) := by
    congr 1
    dsimp [b, t]
    field_simp [hK_ne]
    push_cast
    ring
  calc
    (gaussianPDFReal s K z : ℂ) =
        (Real.sqrt (2 * Real.pi * (K : ℝ)))⁻¹ *
          Complex.exp (-((z - s) ^ 2) / (2 * (K : ℝ))) := by
      rw [gaussianPDFReal_def]
      simp [Complex.ofReal_exp, Complex.ofReal_inv]
    _ = (1 / (2 * Real.pi) : ℂ) * ((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) *
        Complex.exp (-t ^ 2 / (4 * b)) := by
      rw [← hConst, ← hExp]
    _ = (1 / (2 * Real.pi) : ℂ) * (((Real.pi : ℂ) / b) ^ (1 / 2 : ℂ) *
        Complex.exp (-t ^ 2 / (4 * b))) := by
      ring
    _ = (1 / (2 * Real.pi) : ℂ) *
        (∫ Λ : ℝ, Complex.exp (-(K : ℂ) / 2 * (Λ : ℂ) ^ 2 +
            Complex.I * (Λ : ℂ) * ((z - s : ℝ) : ℂ))) := by
      rw [← hInt]

/-- A randomized measurable map, represented as a Markov kernel.  The same random parameter is
used throughout one evaluation. -/
def randomMapKernel {Θ : Type uΘ} {X : Type uX} {Y : Type uY}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure Θ) (F : Θ → X → Y)
    (_hF : Measurable fun p : Θ × X => F p.1 p.2) : Kernel X Y :=
  (Kernel.id ×ₖ Kernel.const X ν).map fun p : X × Θ => F p.2 p.1

/-- Pointwise description of `randomMapKernel`.

Informal proof: `Kernel.prod_apply` turns `Kernel.id ×ₖ Kernel.const` into
`dirac x × ν`; mapping `(x,θ) ↦ F θ x` and integrating out the Dirac coordinate leaves
`ν.map (fun θ ↦ F θ x)`.  See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/Prod.html>. -/
theorem randomMapKernel_apply {Θ : Type uΘ} {X : Type uX} {Y : Type uY}
    [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure Θ) [IsProbabilityMeasure ν] (F : Θ → X → Y)
    (hF : Measurable fun p : Θ × X => F p.1 p.2) (x : X) :
    randomMapKernel ν F hF x = ν.map fun θ => F θ x := by
  have hswap : Measurable (fun p : X × Θ => F p.2 p.1) := hF.comp measurable_swap
  rw [randomMapKernel, Kernel.map_apply _ hswap, Kernel.prod_apply, Kernel.id_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map hswap measurable_prodMk_left]
  rfl

/-- Batched affine preactivation, with sample and neuron indices kept separate. -/
def batchPreactivation [Fintype ι] (q : LayerParams ι κ)
    (s : A → ι → ℝ) : A → κ → ℝ :=
  fun a => (DenseLayer.ofParams q).preactivation (s a)

/-- Batched affine evaluation is jointly measurable in parameters and inputs.

Informal proof: each output coordinate is a bias projection plus a finite sum of products of
measurable coordinate projections. Measurability of a function into a finite product is equivalent
to measurability of every coordinate. See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/MeasureTheory/MeasurableSpace/Constructions.html>. -/
theorem measurable_batchPreactivation [Fintype ι] [Finite κ] :
    Measurable (fun p : LayerParams ι κ × (A → ι → ℝ) =>
      batchPreactivation p.1 p.2) := by
  let _ := Fintype.ofFinite κ
  exact measurable_pi_lambda _ fun a => DenseLayer.measurable_preactivation.comp
    (measurable_fst.prodMk ((measurable_pi_apply a).comp measurable_snd))

/-- Apply an activation coordinatewise to every sample in a batch. -/
def batchActivate (σ : ℝ → ℝ) (z : A → ι → ℝ) : A → ι → ℝ :=
  fun a i => σ (z a i)

theorem measurable_batchActivate {σ : ℝ → ℝ} (hσ : Measurable σ) :
    Measurable (batchActivate σ : (A → ι → ℝ) → A → ι → ℝ) := by
  exact measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun i =>
    hσ.comp ((measurable_pi_apply i).comp (measurable_pi_apply a))

/-- Deterministic kernel applying an activation to a batch. -/
def batchActivationKernel (σ : ℝ → ℝ) (hσ : Measurable σ) :
    Kernel (A → ι → ℝ) (A → ι → ℝ) :=
  Kernel.deterministic (batchActivate σ) (measurable_batchActivate hσ)

@[simp] theorem batchActivationKernel_apply (σ : ℝ → ℝ) (hσ : Measurable σ)
    (z : A → ι → ℝ) : batchActivationKernel σ hσ z = Measure.dirac (batchActivate σ z) := by
  exact Kernel.deterministic_apply _ _

/-- Covariance across samples for one initialized output neuron. -/
def layerCovariance (p : InitHyperparams) (s : A → ι → ℝ) [Fintype ι] : Matrix A A ℝ :=
  fun a a' => p.biasVariance + scaledWeightVariance p ι * ∑ i, s a i * s a' i

/-- The layer covariance is positive semidefinite.

Informal proof: for a coefficient vector `v`, expand its quadratic form as
`C_b (∑ a, v a)^2 + (C_W / |ι|) ∑ i, (∑ a, v a * s a i)^2`.  Both coefficients are nonnegative
and every square is nonnegative.  The covariance is symmetric by commutativity.  This is the Gram
matrix argument described at <https://en.wikipedia.org/wiki/Gram_matrix#Positive-semidefiniteness>. -/
theorem layerCovariance_posSemidef [Fintype ι] [Finite A]
    (p : InitHyperparams) (s : A → ι → ℝ) : (layerCovariance p s).PosSemidef := by
  classical
  -- The covariance matrix is the all-ones matrix scaled by the bias variance plus the Gram
  -- matrix `S * Sᴴ` of the input vectors scaled by the fan-in-normalized weight variance.
  let _ : StarOrderedRing ℝ := RCLike.toStarOrderedRing (K := ℝ)
  let S : Matrix A ι ℝ := fun a i => s a i
  let J : Matrix A A ℝ := fun _ _ => (1 : ℝ)
  let G : Matrix A A ℝ := fun a a' => ∑ i, s a i * s a' i
  have hS : layerCovariance p s =
      (p.biasVariance : ℝ) • J + (scaledWeightVariance p ι : ℝ) • G := by
    ext a a'
    simp only [layerCovariance, Matrix.add_apply, J, G]
    change (p.biasVariance : ℝ) + (scaledWeightVariance p ι : ℝ) * (∑ i, s a i * s a' i) =
      (p.biasVariance : ℝ) * 1 + (scaledWeightVariance p ι : ℝ) * (∑ i, s a i * s a' i)
    simp
  have hJ : J.PosSemidef := by
    have hJ' : J = Matrix.vecMulVec (fun _ : A => (1 : ℝ)) (star (fun _ : A => (1 : ℝ))) := by
      ext a a'
      simp [J, Matrix.vecMulVec]
    rw [hJ']
    exact Matrix.posSemidef_vecMulVec_self_star (fun _ : A => (1 : ℝ))
  have hG : G.PosSemidef := by
    have hG' : G = S * Matrix.conjTranspose S := by
      ext a a'
      exact rfl
    rw [hG']
    exact Matrix.posSemidef_self_mul_conjTranspose S
  rw [hS]
  exact (Matrix.PosSemidef.smul hJ
      (show 0 ≤ (p.biasVariance : ℝ) from (p.biasVariance : ℝ≥0).property)).add
    (Matrix.PosSemidef.smul hG
      (show 0 ≤ (scaledWeightVariance p ι : ℝ) from (scaledWeightVariance p ι : ℝ≥0).property))

/-- Convert one neuron's raw sample vector to Mathlib's Euclidean representation. -/
def batchToEuclidean (z : A → κ → ℝ) (j : κ) : EuclideanSpace ℝ A :=
  (EuclideanSpace.equiv A ℝ).symm fun a => z a j

/-- Exact joint law of all batched preactivations in one initialized layer.

Informal proof: for fixed `j`, the batch is an affine linear image of the centered jointly Gaussian
bias and weight row.  Its mean is zero and its covariance is `layerCovariance p s` by the coordinate
moment lemmas.  Different `j` use disjoint independent parameter rows, so
`iIndepFun.map_fun_eq_pi_map` identifies the joint law with the finite product shown below.  See
Mathlib's multivariate Gaussian construction:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Gaussian/Multivariate.html>. -/
theorem map_evalBatch_layerGaussianInit [Fintype ι] [Fintype κ] [Fintype A] [DecidableEq A]
    (p : InitHyperparams) (s : A → ι → ℝ) :
    Measure.map (fun q : LayerParams ι κ => fun j => batchToEuclidean (batchPreactivation q s) j)
        (layerGaussianInit p ι κ) =
      Measure.pi (fun _ : κ => multivariateGaussian 0 (layerCovariance p s)) := by
  sorry

/-- Randomized dense-layer kernel under independent Gaussian initialization. -/
def randomLayerKernel [Fintype ι] [Fintype κ] (p : InitHyperparams) :
    Kernel (A → ι → ℝ) (A → κ → ℝ) :=
  randomMapKernel (layerGaussianInit p ι κ) batchPreactivation measurable_batchPreactivation

/-- The conditional law of a deeper affine layer is the pushforward of a fresh independent
parameter law, the rigorous measure-theoretic form of the source's product-of-Dirac display. -/
theorem randomLayerKernel_apply [Fintype ι] [Fintype κ] (p : InitHyperparams)
    (s : A → ι → ℝ) :
    randomLayerKernel p s =
      Measure.map (fun q : LayerParams ι κ => batchPreactivation q s)
        (layerGaussianInit p ι κ) := by
  exact randomMapKernel_apply _ _ _ _

/-- A shape-safe list of independently initialized layer laws. -/
inductive MLPEnsemble (σ : ℝ → ℝ) : ℕ → ℕ → Type where
  | output {m n : ℕ} : InitHyperparams → MLPEnsemble σ m n
  | hidden {m n k : ℕ} : InitHyperparams → MLPEnsemble σ k n → MLPEnsemble σ m n

namespace MLPEnsemble

/-- The fixed parameterized shape underlying an ensemble architecture. -/
def shape {σ : ℝ → ℝ} {m n : ℕ} : MLPEnsemble σ m n → MLPShape m n
  | .output _ => .output
  | .hidden _ N => .hidden N.shape

/-- The layerwise initialization hyperparameters, viewed as data for `shape.gaussianInit`. -/
def hyperparams {σ : ℝ → ℝ} {m n : ℕ} : (N : MLPEnsemble σ m n) → N.shape.Hyperparams
  | .output p => p
  | .hidden p N => (p, N.hyperparams)

/-- Depth of an ensemble architecture. -/
def depth {σ : ℝ → ℝ} {m n : ℕ} : MLPEnsemble σ m n → ℕ
  | .output _ => 1
  | .hidden _ N => N.depth + 1

/-- Input width followed by all layer widths of an ensemble architecture. -/
def widths {σ : ℝ → ℝ} {m n : ℕ} : MLPEnsemble σ m n → List ℕ
  | .output _ => [m, n]
  | .hidden _ N => m :: N.widths

/-- Kernel semantics of an independently initialized MLP on a shared finite batch.

Informal construction: an output node is `randomLayerKernel`.  At a hidden node, compose its
random affine kernel, the deterministic coordinatewise activation kernel, and the recursively
constructed tail.  Kernel composition integrates over the fresh parameter law at each layer,
which is exactly independent initialization.  See
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/Comp.html>. -/
def outputKernel {σ : ℝ → ℝ} (hσ : Measurable σ) {m n : ℕ} (N : MLPEnsemble σ m n)
    (A : Type uA) : Kernel (A → Fin m → ℝ) (A → Fin n → ℝ) :=
  match N with
  | .output p => randomLayerKernel p
  | .hidden p N => N.outputKernel hσ A ∘ₖ batchActivationKernel σ hσ ∘ₖ randomLayerKernel p

@[simp] theorem outputKernel_output {σ : ℝ → ℝ} (hσ : Measurable σ) {m n : ℕ}
    (p : InitHyperparams) (A : Type uA) :
    (MLPEnsemble.output p : MLPEnsemble σ m n).outputKernel hσ A = randomLayerKernel p := rfl

@[simp] theorem outputKernel_hidden {σ : ℝ → ℝ} (hσ : Measurable σ) {m n k : ℕ}
    (p : InitHyperparams) (N : MLPEnsemble σ k n) (A : Type uA) :
    (@MLPEnsemble.hidden σ m n k p N).outputKernel hσ A =
      N.outputKernel hσ A ∘ₖ batchActivationKernel σ hσ ∘ₖ
        (randomLayerKernel (A := A) (ι := Fin m) (κ := Fin k) p) := rfl

/-- `(μ.map f).bind g = μ.bind (g ∘ f)` for measurable maps, the measure-monad pullback rule. -/
private lemma bind_map {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) {f : α → β} {g : β → Measure γ}
    (hf : Measurable f) (hg : Measurable g) :
    (μ.map f).bind g = μ.bind (fun x => g (f x)) := by
  rw [Measure.bind, Measure.bind, Measure.map_map hg hf]
  rfl

/-- `(μ.bind f).map g = μ.bind (fun x => (f x).map g)` for a measurable map `g`. -/
private lemma map_bind {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (f : α → Measure β) {g : β → γ}
    (hf : Measurable f) (hg : Measurable g) :
    (μ.bind f).map g = μ.bind (fun x => (f x).map g) := by
  rw [Measure.bind, ← Measure.join_map_map hg]
  rw [Measure.bind, Measure.map_map (Measure.measurable_map g hg) hf]
  rfl

/-- Recursive integration of fresh layer parameters agrees with one global pushforward of the
joint independent parameter law.

Informal proof: induct on `N`. The output case is `randomLayerKernel_apply`. In the hidden case,
expand kernel composition, use Tonelli/Fubini for the product probability measure, and apply the
induction hypothesis. The evaluator recursion `MLPShape.eval_hidden` identifies the composed
integrand with full MLP evaluation. See Mathlib's kernel-composition API:
<https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/Composition/Comp.html>. -/
theorem outputKernel_apply_eq_outputLaw {σ : ℝ → ℝ} (hσ : Measurable σ)
    {m n : ℕ} (N : MLPEnsemble σ m n) (A : Type uA) (D : A → Fin m → ℝ) :
    N.outputKernel hσ A D =
      (N.shape.paramModel σ hσ).outputLaw D (N.shape.gaussianInit N.hyperparams) := by
  induction N with
  | output p =>
      simp only [ParamModel.outputLaw, outputKernel_output, MLPShape.paramModel]
      rw [randomLayerKernel_apply]
      rfl
  | hidden p N' ih =>
      rename_i m n k
      let μ : Measure (LayerParams (Fin m) (Fin k)) := layerGaussianInit p (Fin m) (Fin k)
      let ν : Measure N'.shape.Params := N'.shape.gaussianInit N'.hyperparams
      let f : LayerParams (Fin m) (Fin k) → A → Fin k → ℝ := fun q => batchPreactivation q D
      let act : (A → Fin k → ℝ) → A → Fin k → ℝ := batchActivate σ
      have hf_meas : Measurable f := by
        dsimp [f]
        exact measurable_pi_lambda _ fun a => DenseLayer.measurable_preactivation.comp
          (measurable_id.prodMk measurable_const)
      have hact_meas : Measurable act := measurable_batchActivate hσ
      have hcomp : (N'.outputKernel hσ A ∘ₖ batchActivationKernel σ hσ) =
          fun z => N'.outputKernel hσ A (act z) := by
        funext z
        rw [Kernel.comp_apply, batchActivationKernel_apply]
        exact Measure.dirac_bind (N'.outputKernel hσ A).measurable (batchActivate σ z)
      let G : (LayerParams (Fin m) (Fin k) × N'.shape.Params) → A → Fin n → ℝ :=
        fun p a => N'.shape.eval σ p.2 (act (f p.1) a)
      have hG_meas : Measurable G := by
        dsimp [G]
        refine measurable_pi_lambda _ fun a => ?_
        exact (N'.shape.measurable_eval hσ).comp
          (measurable_snd.prodMk
            (((measurable_pi_apply a).comp hact_meas).comp (hf_meas.comp measurable_fst)))
      have hprod :
          (μ.prod ν).map G =
          μ.bind (fun q => ν.map (fun θ' => G (q, θ'))) := by
        rw [Measure.prod]
        calc
          (μ.bind (fun q : LayerParams (Fin m) (Fin k) => Measure.map (Prod.mk q) ν)).map G
              = μ.bind (fun q => (Measure.map (Prod.mk q) ν).map G) := by
                exact map_bind μ (fun q => Measure.map (Prod.mk q) ν) (g := G)
                  (by exact Measurable.map_prodMk_left) hG_meas
          _ = μ.bind (fun q => ν.map (fun θ' => G (q, θ'))) := by
                congr
                funext q
                exact Measure.map_map hG_meas (measurable_const.prodMk measurable_id)
      calc
        (@MLPEnsemble.hidden σ m n k p N').outputKernel hσ A D
            = (N'.outputKernel hσ A ∘ₖ batchActivationKernel σ hσ ∘ₖ
                randomLayerKernel (A := A) (ι := Fin m) (κ := Fin k) p) D := by
          rw [outputKernel_hidden]
        _ = (randomLayerKernel (A := A) (ι := Fin m) (κ := Fin k) p D).bind
              (N'.outputKernel hσ A ∘ₖ batchActivationKernel σ hσ) := by
          rw [Kernel.comp_apply]
        _ = (layerGaussianInit p (Fin m) (Fin k)).bind
              (fun q => N'.outputKernel hσ A (act (f q))) := by
          rw [randomLayerKernel_apply]
          rw [hcomp]
          exact bind_map (layerGaussianInit p (Fin m) (Fin k)) (hf := hf_meas)
            (hg := (N'.outputKernel hσ A).measurable.comp hact_meas)
        _ = (layerGaussianInit p (Fin m) (Fin k)).bind
              (fun q => ν.map (fun θ' => fun a => N'.shape.eval σ θ' (act (f q) a))) := by
          apply congrArg (Measure.bind (layerGaussianInit p (Fin m) (Fin k)))
          funext q
          rw [ih (act (f q))]
          rfl
        _ = ((layerGaussianInit p (Fin m) (Fin k)).prod
              (N'.shape.gaussianInit N'.hyperparams)).map G := by
          exact hprod.symm
        _ = ((layerGaussianInit p (Fin m) (Fin k)).prod
              (N'.shape.gaussianInit N'.hyperparams)).map
              (fun p : (MLPShape.hidden N'.shape).Params =>
                fun a => (MLPShape.hidden N'.shape).eval σ p (D a)) := by
          congr 1
          funext p a
          dsimp [G, act, f]
        _ = ((MLPShape.hidden N'.shape).paramModel σ hσ).outputLaw D
              ((MLPShape.hidden N'.shape).gaussianInit (p, N'.hyperparams)) := by
          rfl

end MLPEnsemble

end NeuralNetwork

end

end
