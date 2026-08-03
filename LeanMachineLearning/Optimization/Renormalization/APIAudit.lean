/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.Tilted
public import LeanMachineLearning.Optimization.Renormalization.Convolution
public import LeanMachineLearning.Optimization.Renormalization.InducedLaw
public import LeanMachineLearning.Optimization.Renormalization.ParameterizedMLP

/-!
# Renormalization API audit

This scratch module verifies every external Mathlib declaration currently named in the
renormalization implementation and blueprint.  It intentionally uses direct imports and contains
only `#check` and `#synth` commands.
-/

/-! ## Finite partitions -/

#check Finpartition
#check Finpartition.parts
#check Finpartition.map
#check Finpartition.parts_map
#check Finpartition.bind
#check Finpartition.bind_parts
#check Finpartition.mem_bind
#check Finpartition.card_bind
#check Finpartition.part
#check Finpartition.sum_card_parts
#check Equiv.finsetCongr
#check Equiv.finsetCongr_apply
#check Finset.prod_biUnion
#check Finset.prod_sum
#check Fintype.prod_sum
#check IncidenceAlgebra.moebius_inversion_bot

#synth Fintype (Finpartition (Finset.univ : Finset (Fin 4)))

/-! ## Moments, cumulants, and independence -/

#check ProbabilityTheory.moment
#check ProbabilityTheory.mgf
#check ProbabilityTheory.cgf
#check ProbabilityTheory.integrableExpSet
#check ProbabilityTheory.iteratedDeriv_mgf_zero
#check ProbabilityTheory.covariance
#check ProbabilityTheory.covariance_eq_sub
#check ProbabilityTheory.IndepFun
#check ProbabilityTheory.iIndepFun
#check ProbabilityTheory.iIndepFun.indepFun_finset
#check ProbabilityTheory.iIndepFun.restrict

/-! ## Gaussian measures -/

#check ProbabilityTheory.gaussianReal
#check ProbabilityTheory.mgf_gaussianReal
#check ProbabilityTheory.mgf_fun_id_gaussianReal
#check ProbabilityTheory.cgf_gaussianReal
#check ProbabilityTheory.integrableExpSet_fun_id_gaussianReal
#check ProbabilityTheory.stdGaussian
#check ProbabilityTheory.multivariateGaussian
#check ProbabilityTheory.integral_id_multivariateGaussian
#check ProbabilityTheory.covariance_eval_multivariateGaussian
#check ProbabilityTheory.IsGaussian
#check ProbabilityTheory.IsGaussian.map_eq_gaussianReal
#check ProbabilityTheory.IsGaussian.memLp_dual
#check ProbabilityTheory.IsGaussian.integrable_dual

/-! ## Symmetry and exponential tilting -/

#check MeasureTheory.Measure.IsNegInvariant
#check MeasureTheory.Measure.measurePreserving_neg
#check MeasureTheory.Measure.tilted
#check MeasureTheory.tilted_zero
#check MeasureTheory.isProbabilityMeasure_tilted
#check MeasureTheory.integral_tilted
#check MeasureTheory.integral_exp_tilted
#check MeasureTheory.Integrable
#check MeasureTheory.AEStronglyMeasurable
#check HasDerivWithinAt
#check Asymptotics.IsBigO
#check nhdsWithin
#check Set.Ici
#check ProbabilityTheory.integral_tilted_mul_self
#check ProbabilityTheory.variance_tilted_mul

/-! ## Finite-dimensional quartic specialization -/

#check Matrix.PosSemidef
#check Equiv.Perm
#check Equiv.sumCongr
#check Sum.elim
#check Finset.univ
#check Finset.sum_mul

#synth MeasureTheory.IsProbabilityMeasure
  (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) 0)
#synth ProbabilityTheory.IsGaussian
  (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin 2)) 0)

/-! ## Chapter 2: products, induced laws, and kernels -/

#check MeasureTheory.Measure.pi
#check MeasureTheory.Measure.pi_map_eval
#check ProbabilityTheory.iIndepFun_pi
#check ProbabilityTheory.iIndepFun.map_fun_eq_pi_map
#check MeasureTheory.Measure.map_fst_prod
#check MeasureTheory.Measure.map_snd_prod
#check MeasureTheory.Measure.isProbabilityMeasure_map
#check MeasureTheory.integral_map
#check MeasureTheory.integral_dirac
#check ProbabilityTheory.variance_dirac
#check MeasureTheory.charFun_dirac
#check ProbabilityTheory.Kernel.deterministic
#check ProbabilityTheory.Kernel.deterministic_apply
#check ProbabilityTheory.Kernel.const
#check ProbabilityTheory.Kernel.id
#check ProbabilityTheory.Kernel.map
#check ProbabilityTheory.Kernel.map_apply
#check ProbabilityTheory.Kernel.prod_apply
#check MeasureTheory.Measure.deterministic_comp_eq_map
#check ProbabilityTheory.gaussianReal_zero_var
#check ProbabilityTheory.integral_id_gaussianReal
#check ProbabilityTheory.variance_id_gaussianReal

/-! ## Chapter 2 equation-by-equation coverage -/

-- `eq:exponential-Taylor-expansion`
#check NeuralNetwork.exp_eq_tsum_div_factorial

-- `eq:preactivation` and the firing criterion
#check NeuralNetwork.DenseLayer.preactivation_apply
#check NeuralNetwork.DenseLayer.activate_apply
#check NeuralNetwork.DenseLayer.activate_threshold_eq_one_iff

-- `eq:mlp-definition`, `f(x;θ) = z⁽ᴸ⁾(x)`, widths, depth, and parameter count
#check NeuralNetwork.MLP.eval_output
#check NeuralNetwork.MLP.eval_hidden
#check NeuralNetwork.MLP.depth
#check NeuralNetwork.MLP.widths
#check NeuralNetwork.MLP.paramCount_eq_paramCountFromWidths
#check NeuralNetwork.exampleMLP45551
#check NeuralNetwork.MLPShape.Params
#check NeuralNetwork.MLPShape.eval
#check NeuralNetwork.MLPShape.measurable_eval
#check NeuralNetwork.MLPShape.paramModel
#check NeuralNetwork.MLPShape.Hyperparams
#check NeuralNetwork.MLPShape.gaussianInit
#check NeuralNetwork.MLPShape.map_coordinate_gaussianInit
#check NeuralNetwork.MLPShape.iIndepFun_coordinate_gaussianInit

-- `eq:conv-layer` and its precise translation-equivariance statement
#check NeuralNetwork.Conv2DLayer.preactivation_apply
#check NeuralNetwork.Conv2DLayer.preactivation_ofOffsetTiedDense
#check NeuralNetwork.Conv2DLayer.preactivation_shift
#check NeuralNetwork.Conv2DLayer.preactivation_eq_toLocalDenseLayer
#check NeuralNetwork.Conv2DLayer.paramCount

-- Standard activation displays and exact qualitative claims
#check NeuralNetwork.threshold
#check NeuralNetwork.signedThreshold
#check NeuralNetwork.signedThreshold_eq_sign
#check NeuralNetwork.logistic
#check NeuralNetwork.logistic_pos
#check NeuralNetwork.logistic_lt_one
#check NeuralNetwork.relu
#check NeuralNetwork.linear
#check NeuralNetwork.leakyRelu
#check NeuralNetwork.logistic_eq_half_add_half_tanh
#check NeuralNetwork.tanh_eq_exp_div
#check NeuralNetwork.tanh_eq_exp_two_mul
#check Real.sin
#check NeuralNetwork.sinActivation_periodic
#check NeuralNetwork.hasDerivAt_tanh_zero
#check NeuralNetwork.PosHomogeneous
#check NeuralNetwork.posHomogeneous_iff_eq_piecewiseLinear
#check NeuralNetwork.differentiableAt_piecewiseLinear_zero_iff
#check NeuralNetwork.softplus
#check NeuralNetwork.swish
#check NeuralNetwork.gaussianErf
#check NeuralNetwork.gelu
#check NeuralNetwork.gelu_eq_erf
#check NeuralNetwork.smooth_activations
#check NeuralNetwork.activation_asymptotics
#check NeuralNetwork.nonhomogeneous_activations
#check NeuralNetwork.not_posHomogeneous_threshold
#check NeuralNetwork.not_posHomogeneous_logistic
#check NeuralNetwork.posHomogeneous_linear
#check NeuralNetwork.posHomogeneous_relu
#check NeuralNetwork.posHomogeneous_leakyRelu

-- `eq:bias-variance-def-naive`, `eq:weight-variance-def-naive`, and both densities
#check NeuralNetwork.layerGaussianInit
#check NeuralNetwork.iIndepFun_layerCoordinate_layerGaussianInit
#check NeuralNetwork.covariance_bias_layerGaussianInit
#check NeuralNetwork.covariance_weight_layerGaussianInit
#check NeuralNetwork.covariance_weight_bias_layerGaussianInit
#check NeuralNetwork.gaussianPDFReal_bias_eq
#check NeuralNetwork.gaussianPDFReal_weight_eq_source

-- `eq:gigantic-beast-that-we-tame` and its generic Dirac/pushforward form
#check NeuralNetwork.ParamModel.outputLaw
#check NeuralNetwork.ParamModel.integral_outputLaw
#check NeuralNetwork.ParamModel.parameterOutputKernel_comp_eq_outputLaw
#check NeuralNetwork.MLPShape.outputLaw_gaussianInit_eq_map

-- `eq:dirac-mean` through `eq:dirac-delta-normalization` and self-averaging
#check NeuralNetwork.integral_dirac_apply
#check NeuralNetwork.integral_id_dirac
#check NeuralNetwork.integral_sq_dirac
#check NeuralNetwork.variance_id_dirac
#check NeuralNetwork.dirac_apply_univ
#check NeuralNetwork.SelfAveragingAt
#check NeuralNetwork.selfAveragingAt_iff_eq_dirac

-- `eq:gaussian-limit-delta-function` and the corrected Fourier interpretation
#check NeuralNetwork.tendsto_gaussianProbabilityMeasure_zero_variance
#check NeuralNetwork.gaussianPDFReal_eq_regularizedFourierIntegral
#check NeuralNetwork.not_integrable_dirac_fourierKernel
#check NeuralNetwork.charFun_dirac

-- First-layer, deeper-layer, and general induced laws
#check NeuralNetwork.map_evalBatch_layerGaussianInit
#check NeuralNetwork.randomLayerKernel_apply
#check NeuralNetwork.MLPEnsemble.outputKernel
#check NeuralNetwork.MLPEnsemble.outputKernel_apply_eq_outputLaw
