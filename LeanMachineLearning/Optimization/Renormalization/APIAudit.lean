module

public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.Moments.Tilted

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
