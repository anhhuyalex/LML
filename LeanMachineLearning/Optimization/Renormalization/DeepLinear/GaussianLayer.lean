/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

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

/-- The product law of `n` independent standard real Gaussians. -/
def standardGaussianVectorLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => gaussianReal 0 1

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

/-- Even-moment recurrence for a standard one-dimensional Gaussian:
`∫ z, z ^ (2 * (a + 1)) = (2a + 1) * ∫ z, z ^ (2 * a)`.

This is the one-coordinate instance of the chi-square recursion used below in
`integral_sumSq_pow_stdGaussian_succ`.  It follows directly from
`Renormalization.integral_mul_pow_gaussianReal` (Stein's lemma for monomials). -/
private lemma integral_pow_two_mul_succ_stdGaussian (a : ℕ) :
    ∫ u : ℝ, u ^ (2 * (a + 1)) ∂gaussianReal 0 1 =
      (2 * (a : ℝ) + 1) * ∫ u : ℝ, u ^ (2 * a) ∂gaussianReal 0 1 := by
  calc
    ∫ u : ℝ, u ^ (2 * (a + 1)) ∂gaussianReal 0 1
        = ∫ u : ℝ, u * u ^ (2 * a + 1) ∂gaussianReal 0 1 := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with u
            rw [show 2 * (a + 1) = (2 * a + 1) + 1 by omega, pow_succ']
    _ = (2 * (a : ℝ) + 1) * ∫ u : ℝ, u ^ (2 * a) ∂gaussianReal 0 1 := by
            rw [Renormalization.integral_mul_pow_gaussianReal 1 (2 * a + 1)]
            norm_num [show 2 * a + 1 - 1 = 2 * a by omega]

/-- Monomials are integrable under the standard one-dimensional Gaussian. -/
private lemma integrable_pow_stdGaussian (n : ℕ) :
    Integrable (fun z : ℝ => z ^ n) (gaussianReal 0 1) := by
  -- The Gaussian has finite moments of every order (Fernique), so `‖z‖^(n+1)` is integrable.
  have hmem : MemLp (fun z : ℝ => z) ((n + 1 : ℕ) : ℝ≥0∞) (gaussianReal 0 1) :=
    memLp_id_gaussianReal' ((n + 1 : ℕ) : ℝ≥0∞) (by norm_num)
  have hint_dom : Integrable (fun z : ℝ => (1 : ℝ) + ‖z‖ ^ (n + 1)) (gaussianReal 0 1) :=
    (integrable_const _).add hmem.integrable_norm_pow'
  refine Integrable.mono' hint_dom ?_ (Filter.Eventually.of_forall ?_)
  · fun_prop
  · intro z
    rw [norm_pow]
    by_cases hz : ‖z‖ ≤ 1
    · have hzpow : ‖z‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
      nlinarith [hzpow, pow_nonneg (norm_nonneg z) (n + 1)]
    · have hz' : 1 ≤ ‖z‖ := le_of_not_ge hz
      have hzpow : ‖z‖ ^ n ≤ ‖z‖ ^ (n + 1) :=
        pow_le_pow_right₀ hz' (Nat.le_add_right n 1)
      nlinarith [hzpow]

/-- The `m`-th power of the sum of squares is integrable under the standard Gaussian vector law.

The proof bounds `(∑ i, g i ^ 2)^m` by the power-mean inequality in terms of the coordinate
monomials `g j ^ (2m)`, each of which is integrable because every coordinate is a standard
one-dimensional Gaussian. -/
private lemma integrable_sumSq_pow_stdGaussian (m : ℕ) (n : ℕ) :
    Integrable (fun g : Fin n → ℝ => (∑ i : Fin n, g i ^ 2) ^ m)
      (standardGaussianVectorLaw n) := by
  let μ : Measure (Fin n → ℝ) := standardGaussianVectorLaw n
  have : IsFiniteMeasure (standardGaussianVectorLaw n) := by
    unfold standardGaussianVectorLaw
    infer_instance
  by_cases hn : n = 0
  · subst n
    by_cases hm : m = 0
    · subst m
      simp [standardGaussianVectorLaw]
    · simp [standardGaussianVectorLaw, zero_pow hm]
  · by_cases hm : m = 0
    · subst m
      exact integrable_const (1 : ℝ)
    · have hmpos : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm)
      have hcoord : ∀ j : Fin n,
          Integrable (fun g : Fin n → ℝ => g j ^ (2 * m)) μ := by
        intro j
        have hmem : MemLp (fun g : Fin n → ℝ => g j) ((2 * m : ℕ) : ℝ≥0∞) μ := by
          simpa [μ, standardGaussianVectorLaw] using
            (MemLp.comp_measurePreserving
              (memLp_id_gaussianReal' ((2 * m : ℕ) : ℝ≥0∞) (ENNReal.natCast_ne_top (2 * m)))
              (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) j))
        have hint : Integrable (fun g : Fin n → ℝ => ‖g j‖ ^ (2 * m)) μ :=
          hmem.integrable_norm_pow'
        rw [← integrable_norm_iff ((measurable_pi_apply j).pow_const (2 * m)).aestronglyMeasurable]
        simpa [norm_pow] using hint
      have hsum : Integrable (fun g : Fin n → ℝ => ∑ j : Fin n, g j ^ (2 * m)) μ := by
        simpa using
          (integrable_finsetSum Finset.univ (μ := μ) (f := fun (j : Fin n) g => g j ^ (2 * m))
            (fun j _ => hcoord j))
      -- power-mean bound: `X^m ≤ n^(m-1) · ∑ g_j^(2m)`.
      have hbound : ∀ g : Fin n → ℝ,
          (∑ i : Fin n, g i ^ 2) ^ m ≤ (n : ℝ) ^ (m - 1) * ∑ j : Fin n, g j ^ (2 * m) := by
        intro g
        have hpm := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
          (s := Finset.univ) (f := fun i : Fin n => g i ^ 2) (p := (m : ℝ))
          (hp := by exact_mod_cast hmpos) (hf := fun i _ => sq_nonneg (g i))
        have hpm' : (∑ i : Fin n, g i ^ 2) ^ m ≤
            (n : ℝ) ^ (m - 1) * ∑ j : Fin n, (g j ^ 2) ^ m := by
          calc
            (∑ i : Fin n, g i ^ 2) ^ m = (∑ i : Fin n, g i ^ 2) ^ ((m : ℝ)) := by
              rw [← Real.rpow_natCast]
            _ ≤ (n : ℝ) ^ ((m : ℝ) - 1) * ∑ i : Fin n, (g i ^ 2) ^ ((m : ℝ)) := by
              simpa [Finset.card_univ, Fintype.card_fin] using hpm
            _ = (n : ℝ) ^ (m - 1) * ∑ j : Fin n, (g j ^ 2) ^ m := by
              rw [← Nat.cast_one, ← Nat.cast_sub hmpos]
              simp_rw [Real.rpow_natCast]
        simpa [← pow_mul] using hpm'
      refine Integrable.mono' (hsum.const_mul ((n : ℝ) ^ (m - 1))) ?_
        (Filter.Eventually.of_forall ?_)
      · exact ((Finset.measurable_sum Finset.univ (fun i _ =>
          (measurable_pi_apply i).pow_const 2)).pow_const m).aestronglyMeasurable
      · intro g
        rw [Real.norm_eq_abs,
          abs_of_nonneg (pow_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg (g i))) m)]
        exact hbound g

/-- `g i ^ 2 * (∑ j, g j ^ 2) ^ k` is integrable: it is dominated by `(∑ j, g j ^ 2) ^ (k+1)`. -/
private lemma integrable_sq_mul_sumSq_pow_stdGaussian (k : ℕ) (n : ℕ) (i : Fin n) :
    Integrable (fun g : Fin n → ℝ => g i ^ 2 * (∑ j : Fin n, g j ^ 2) ^ k)
      (standardGaussianVectorLaw n) := by
  refine Integrable.mono' (integrable_sumSq_pow_stdGaussian (k + 1) n) ?_
    (Filter.Eventually.of_forall ?_)
  · exact (((measurable_pi_apply i).pow_const 2).mul
      ((Finset.measurable_sum Finset.univ (fun j _ =>
        (measurable_pi_apply j).pow_const 2)).pow_const k)).aestronglyMeasurable
  · intro g
    have hpos : 0 ≤ g i ^ 2 * (∑ j : Fin n, g j ^ 2) ^ k :=
      mul_nonneg (sq_nonneg (g i))
        (pow_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg (g j))) k)
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    -- `g i ^ 2 ≤ ∑ j, g j ^ 2` and `(∑ g^2)^k ≥ 0`
    have hle : g i ^ 2 ≤ ∑ j : Fin n, g j ^ 2 :=
      Finset.single_le_sum (f := fun j : Fin n => g j ^ 2) (fun j _ => sq_nonneg (g j))
        (Finset.mem_univ i)
    have hXk : 0 ≤ (∑ j : Fin n, g j ^ 2) ^ k :=
      pow_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg (g j))) k
    have hmul : g i ^ 2 * (∑ j : Fin n, g j ^ 2) ^ k ≤
        (∑ j : Fin n, g j ^ 2) ^ (k + 1) := by
      simpa [pow_succ'] using (mul_le_mul_of_nonneg_right hle hXk)
    exact hmul

/-- The elementary binomial identity `(j+1) * (k choose (j+1)) = k * ((k-1) choose j)`
for `j < k`, used to reindex the coefficient sums in the chi-square moment recursion. -/
private lemma Nat_choose_mul_succ (j k : ℕ) (hj : j < k) :
    (j + 1) * (k.choose (j + 1)) = k * ((k - 1).choose j) := by
  have hk : k = (k - 1) + 1 := by omega
  calc
    (j + 1) * (k.choose (j + 1)) = (j + 1) * (((k - 1) + 1).choose (j + 1)) := by
      rw [← hk]
    _ = k * ((k - 1).choose j) := by
      rw [Nat.mul_comm, ← Nat.add_one_mul_choose_eq (k - 1) j, ← hk]

/-- The binomial coefficient identity behind the chi-square recursion: for any sequences `M`, `C`
with `M (a+1) = (2a+1) M a`, `∑ (k choose j) C(k-j) M(j+1)`
equals `∑ (k choose j) C(k-j) M j + 2k ∑ ((k-1) choose j) C(k-1-j) M(j+1)`. -/
private lemma momentRecurrence_coefficient (k : ℕ) (M C : ℕ → ℝ)
    (hM : ∀ a : ℕ, M (a + 1) = (2 * (a : ℝ) + 1) * M a) :
    (∑ j ∈ Finset.range (k + 1), ((k.choose j : ℝ) * C (k - j) * M (j + 1))) =
      (∑ j ∈ Finset.range (k + 1), ((k.choose j : ℝ) * C (k - j) * M j)) +
        (2 : ℝ) * k * (∑ j ∈ Finset.range (k - 1 + 1),
          (((k - 1).choose j : ℝ) * C (k - 1 - j) * M (j + 1))) := by
  classical
  let A : ℕ → ℝ := fun j => (k.choose j : ℝ) * C (k - j)
  let B : ℕ → ℝ := fun j => ((k - 1).choose j : ℝ) * C (k - 1 - j)
  have h_reindex :
      (∑ j ∈ Finset.range (k + 1), (j : ℝ) * A j * M j) =
        (k : ℝ) * ∑ j ∈ Finset.range (k - 1 + 1), (B j * M (j + 1)) := by
    by_cases hk0 : k = 0
    · subst k
      simp
    · have hkm : k - 1 + 1 = k := by omega
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, zero_mul, add_zero]
      rw [hkm]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hjlt : j < k := Finset.mem_range.mp hj
      have hchoose := Nat_choose_mul_succ j k hjlt
      have hpow : k - (j + 1) = k - 1 - j := by omega
      have hc : ((j : ℝ) + 1) * (k.choose (j + 1) : ℝ) = (k : ℝ) * ((k - 1).choose j : ℝ) := by
        have hc' : ((j + 1 : ℕ) : ℝ) * (k.choose (j + 1) : ℝ) =
            (k : ℝ) * ((k - 1).choose j : ℝ) := by
          exact_mod_cast hchoose
        rwa [show ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 by norm_num] at hc'
      dsimp [A, B]
      rw [hpow]
      rw [show ((j : ℝ) + 1) * (↑(k.choose (j + 1)) * C (k - 1 - j)) * M (j + 1) =
          (((j : ℝ) + 1) * ↑(k.choose (j + 1))) * C (k - 1 - j) * M (j + 1) by ring]
      rw [hc]
      ring
  calc
    (∑ j ∈ Finset.range (k + 1), ((k.choose j : ℝ) * C (k - j) * M (j + 1)))
        = ∑ j ∈ Finset.range (k + 1), (A j * ((2 * (j : ℝ) + 1) * M j)) := by
          dsimp [A]
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [hM]
    _ = ∑ j ∈ Finset.range (k + 1), (A j * M j) +
          2 * ∑ j ∈ Finset.range (k + 1), ((j : ℝ) * A j * M j) := by
          have hsummand : (∑ j ∈ Finset.range (k + 1), A j * ((2 * (j : ℝ) + 1) * M j)) =
              ∑ j ∈ Finset.range (k + 1), (A j * M j + 2 * (j : ℝ) * A j * M j) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            ring
          rw [hsummand, Finset.sum_add_distrib]
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _
          ring
    _ = ∑ j ∈ Finset.range (k + 1), (A j * M j) +
          (2 * (k : ℝ)) * ∑ j ∈ Finset.range (k - 1 + 1), (B j * M (j + 1)) := by
          rw [h_reindex]
          ring
    _ = (∑ j ∈ Finset.range (k + 1), ((k.choose j : ℝ) * C (k - j) * M j)) +
          (2 : ℝ) * k * (∑ j ∈ Finset.range (k - 1 + 1),
            (((k - 1).choose j : ℝ) * C (k - 1 - j) * M (j + 1))) := by
          dsimp [A, B]

/-- Stein's identity for `z^2 (z^2 + R)^k` under the standard Gaussian:
`E[z^2 (z^2+R)^k] = E[(z^2+R)^k] + 2k E[z^2 (z^2+R)^(k-1)]`.

The proof expands both sides by the binomial theorem, evaluates the resulting even moments with
`integral_pow_two_mul_succ_stdGaussian`, and reindexes the coefficient sums with
`Nat_choose_mul_succ`.  This is the one-coordinate engine behind the chi-square recursion. -/
private lemma integral_sq_mul_sq_add_pow_stdGaussian (k : ℕ) (R : ℝ) :
    ∫ z : ℝ, z ^ 2 * (z ^ 2 + R) ^ k ∂gaussianReal 0 1 =
      ∫ z : ℝ, (z ^ 2 + R) ^ k ∂gaussianReal 0 1 +
        (2 : ℝ) * k * ∫ z : ℝ, z ^ 2 * (z ^ 2 + R) ^ (k - 1) ∂gaussianReal 0 1 := by
  classical
  let M : ℕ → ℝ := fun a => ∫ z : ℝ, z ^ (2 * a) ∂gaussianReal 0 1
  have hM_succ : ∀ a : ℕ, M (a + 1) = (2 * (a : ℝ) + 1) * M a := by
    intro a
    simpa [M] using integral_pow_two_mul_succ_stdGaussian a
  let A : ℕ → ℝ := fun j => (k.choose j : ℝ) * R ^ (k - j)
  let B : ℕ → ℝ := fun j => ((k - 1).choose j : ℝ) * R ^ (k - 1 - j)
  have h_int_pow (a : ℕ) : Integrable (fun z : ℝ => z ^ a) (gaussianReal 0 1) :=
    integrable_pow_stdGaussian a
  have hbinom (z : ℝ) : (z ^ 2 + R) ^ k =
      ∑ j ∈ Finset.range (k + 1), (z ^ 2) ^ j * R ^ (k - j) * (k.choose j : ℝ) :=
    add_pow (z ^ 2) R k
  have hbinom' (z : ℝ) : (z ^ 2 + R) ^ (k - 1) =
      ∑ j ∈ Finset.range (k - 1 + 1), (z ^ 2) ^ j * R ^ (k - 1 - j) *
        ((k - 1).choose j : ℝ) :=
    add_pow (z ^ 2) R (k - 1)
  have hP : ∫ z : ℝ, z ^ 2 * (z ^ 2 + R) ^ k ∂gaussianReal 0 1 =
      ∑ j ∈ Finset.range (k + 1), (A j * M (j + 1)) := by
    calc
      ∫ z : ℝ, z ^ 2 * (z ^ 2 + R) ^ k ∂gaussianReal 0 1
          = ∫ z : ℝ, z ^ 2 * (∑ j ∈ Finset.range (k + 1),
              (z ^ 2) ^ j * R ^ (k - j) * (k.choose j : ℝ)) ∂gaussianReal 0 1 := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with z
              rw [hbinom]
      _ = ∫ z : ℝ, ∑ j ∈ Finset.range (k + 1),
              (z ^ 2 * (z ^ 2) ^ j * R ^ (k - j) * (k.choose j : ℝ)) ∂gaussianReal 0 1 := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with z
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
      _ = ∑ j ∈ Finset.range (k + 1),
            ∫ z : ℝ, z ^ 2 * (z ^ 2) ^ j * R ^ (k - j) * (k.choose j : ℝ) ∂gaussianReal 0 1 := by
            rw [integral_finsetSum]
            intro j _
            have hint : Integrable (fun z : ℝ => z ^ 2 * (z ^ 2) ^ j) (gaussianReal 0 1) := by
              simpa [pow_mul, pow_add, show 2 * (j + 1) = 2 + 2 * j by omega] using
                h_int_pow (2 * (j + 1))
            simpa [mul_assoc, mul_comm, mul_left_comm] using
              (hint.const_mul ((k.choose j : ℝ) * R ^ (k - j)))
      _ = ∑ j ∈ Finset.range (k + 1), (A j * M (j + 1)) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            dsimp [A, M]
            calc
              ∫ z : ℝ, z ^ 2 * (z ^ 2) ^ j * R ^ (k - j) * (k.choose j : ℝ) ∂gaussianReal 0 1
                  = ∫ z : ℝ, (k.choose j : ℝ) * (R ^ (k - j) * (z ^ 2 * (z ^ 2) ^ j))
                      ∂gaussianReal 0 1 := by
                      apply MeasureTheory.integral_congr_ae
                      filter_upwards with z
                      ring
              _ = (k.choose j : ℝ) *
                      ∫ z : ℝ, R ^ (k - j) * (z ^ 2 * (z ^ 2) ^ j) ∂gaussianReal 0 1 := by
                      rw [integral_const_mul]
              _ = (k.choose j : ℝ) * (R ^ (k - j) *
                      ∫ z : ℝ, z ^ 2 * (z ^ 2) ^ j ∂gaussianReal 0 1) := by
                      rw [integral_const_mul]
              _ = (k.choose j : ℝ) * R ^ (k - j) *
                      ∫ z : ℝ, z ^ 2 * (z ^ 2) ^ j ∂gaussianReal 0 1 := by
                      ring
              _ = (k.choose j : ℝ) * R ^ (k - j) *
                      ∫ z : ℝ, z ^ (2 * (j + 1)) ∂gaussianReal 0 1 := by
                      congr 1
                      apply MeasureTheory.integral_congr_ae
                      filter_upwards with z
                      rw [← pow_mul, ← pow_add, show 2 * (j + 1) = 2 + 2 * j by omega]
  have hQ : ∫ z : ℝ, (z ^ 2 + R) ^ k ∂gaussianReal 0 1 =
      ∑ j ∈ Finset.range (k + 1), (A j * M j) := by
    calc
      ∫ z : ℝ, (z ^ 2 + R) ^ k ∂gaussianReal 0 1
          = ∫ z : ℝ, ∑ j ∈ Finset.range (k + 1),
              ((z ^ 2) ^ j * R ^ (k - j) * (k.choose j : ℝ)) ∂gaussianReal 0 1 := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with z
              rw [hbinom]
      _ = ∑ j ∈ Finset.range (k + 1),
            ∫ z : ℝ, (z ^ 2) ^ j * R ^ (k - j) * (k.choose j : ℝ) ∂gaussianReal 0 1 := by
            rw [integral_finsetSum]
            intro j _
            have hint : Integrable (fun z : ℝ => (z ^ 2) ^ j) (gaussianReal 0 1) := by
              simpa [pow_mul] using h_int_pow (2 * j)
            simpa [mul_assoc, mul_comm, mul_left_comm] using
              (hint.const_mul ((k.choose j : ℝ) * R ^ (k - j)))
      _ = ∑ j ∈ Finset.range (k + 1), (A j * M j) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            dsimp [A, M]
            calc
              ∫ z : ℝ, (z ^ 2) ^ j * R ^ (k - j) * (k.choose j : ℝ) ∂gaussianReal 0 1
                  = ∫ z : ℝ, (k.choose j : ℝ) * (R ^ (k - j) * (z ^ 2) ^ j)
                      ∂gaussianReal 0 1 := by
                      apply MeasureTheory.integral_congr_ae
                      filter_upwards with z
                      ring
              _ = (k.choose j : ℝ) *
                      ∫ z : ℝ, R ^ (k - j) * (z ^ 2) ^ j ∂gaussianReal 0 1 := by
                      rw [integral_const_mul]
              _ = (k.choose j : ℝ) * (R ^ (k - j) *
                      ∫ z : ℝ, (z ^ 2) ^ j ∂gaussianReal 0 1) := by
                      rw [integral_const_mul]
              _ = (k.choose j : ℝ) * R ^ (k - j) *
                      ∫ z : ℝ, (z ^ 2) ^ j ∂gaussianReal 0 1 := by
                      ring
              _ = (k.choose j : ℝ) * R ^ (k - j) * M j := by
                      congr 1
                      apply MeasureTheory.integral_congr_ae
                      filter_upwards with z
                      rw [← pow_mul]
  have hP' : ∫ z : ℝ, z ^ 2 * (z ^ 2 + R) ^ (k - 1) ∂gaussianReal 0 1 =
      ∑ j ∈ Finset.range (k - 1 + 1), (B j * M (j + 1)) := by
    calc
      ∫ z : ℝ, z ^ 2 * (z ^ 2 + R) ^ (k - 1) ∂gaussianReal 0 1
          = ∫ z : ℝ, z ^ 2 * (∑ j ∈ Finset.range (k - 1 + 1),
              (z ^ 2) ^ j * R ^ (k - 1 - j) * ((k - 1).choose j : ℝ)) ∂gaussianReal 0 1 := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with z
              rw [hbinom']
      _ = ∫ z : ℝ, ∑ j ∈ Finset.range (k - 1 + 1),
              (z ^ 2 * (z ^ 2) ^ j * R ^ (k - 1 - j) * ((k - 1).choose j : ℝ))
                ∂gaussianReal 0 1 := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with z
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
      _ = ∑ j ∈ Finset.range (k - 1 + 1),
            ∫ z : ℝ, z ^ 2 * (z ^ 2) ^ j * R ^ (k - 1 - j) * ((k - 1).choose j : ℝ)
              ∂gaussianReal 0 1 := by
            rw [integral_finsetSum]
            intro j _
            have hint : Integrable (fun z : ℝ => z ^ 2 * (z ^ 2) ^ j) (gaussianReal 0 1) := by
              simpa [pow_mul, pow_add, show 2 * (j + 1) = 2 + 2 * j by omega] using
                h_int_pow (2 * (j + 1))
            simpa [mul_assoc, mul_comm, mul_left_comm] using
              (hint.const_mul (((k - 1).choose j : ℝ) * R ^ (k - 1 - j)))
      _ = ∑ j ∈ Finset.range (k - 1 + 1), (B j * M (j + 1)) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            dsimp [B, M]
            calc
              ∫ z : ℝ, z ^ 2 * (z ^ 2) ^ j * R ^ (k - 1 - j) * ((k - 1).choose j : ℝ)
                  ∂gaussianReal 0 1
                  = ∫ z : ℝ, ((k - 1).choose j : ℝ) *
                      (R ^ (k - 1 - j) * (z ^ 2 * (z ^ 2) ^ j)) ∂gaussianReal 0 1 := by
                      apply MeasureTheory.integral_congr_ae
                      filter_upwards with z
                      ring
              _ = ((k - 1).choose j : ℝ) *
                      ∫ z : ℝ, R ^ (k - 1 - j) * (z ^ 2 * (z ^ 2) ^ j) ∂gaussianReal 0 1 := by
                      rw [integral_const_mul]
              _ = ((k - 1).choose j : ℝ) * (R ^ (k - 1 - j) *
                      ∫ z : ℝ, z ^ 2 * (z ^ 2) ^ j ∂gaussianReal 0 1) := by
                      rw [integral_const_mul]
              _ = ((k - 1).choose j : ℝ) * R ^ (k - 1 - j) *
                      ∫ z : ℝ, z ^ 2 * (z ^ 2) ^ j ∂gaussianReal 0 1 := by
                      ring
              _ = ((k - 1).choose j : ℝ) * R ^ (k - 1 - j) *
                      ∫ z : ℝ, z ^ (2 * (j + 1)) ∂gaussianReal 0 1 := by
                      congr 1
                      apply MeasureTheory.integral_congr_ae
                      filter_upwards with z
                      rw [← pow_mul, ← pow_add, show 2 * (j + 1) = 2 + 2 * j by omega]
  calc
    ∫ z : ℝ, z ^ 2 * (z ^ 2 + R) ^ k ∂gaussianReal 0 1
        = ∑ j ∈ Finset.range (k + 1), (A j * M (j + 1)) := hP
    _ = (∑ j ∈ Finset.range (k + 1), (A j * M j)) +
          (2 : ℝ) * k * (∑ j ∈ Finset.range (k - 1 + 1), (B j * M (j + 1))) := by
          simpa [A, B] using momentRecurrence_coefficient k M (fun x : ℕ => R ^ x) hM_succ
    _ = ∫ z : ℝ, (z ^ 2 + R) ^ k ∂gaussianReal 0 1 +
          (2 : ℝ) * k * ∫ z : ℝ, z ^ 2 * (z ^ 2 + R) ^ (k - 1) ∂gaussianReal 0 1 := by
          rw [hQ, hP']

-- Fubini for the split `standardGaussianVectorLaw (m+1)`: splitting off coordinate `i` from
-- `Fin (m+1)` via `i.succAbove` (so the remaining coordinates are indexed by `Fin m`), an
-- integral over the product law equals the iterated integral in which the single coordinate is
-- integrated first.  That order is what lets the one-dimensional Stein identity
-- `integral_sq_mul_sq_add_pow_stdGaussian` apply inside the inner integral.
-- The integrability hypothesis is carried by the caller; it is the only side condition Fubini
-- requires.
private lemma integral_split_coord {m : ℕ} (i : Fin (m + 1))
    (F : ℝ × (Fin m → ℝ) → ℝ)
    (hF : Integrable F ((gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin m => gaussianReal 0 1))) :
    ∫ g : Fin (m + 1) → ℝ, F (g i, fun j : Fin m => g (i.succAbove j))
        ∂standardGaussianVectorLaw (m + 1) =
      ∫ y : Fin m → ℝ, ∫ t : ℝ, F (t, y) ∂gaussianReal 0 1
        ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
  classical
  let e : (Fin (m + 1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
  have hp : MeasurePreserving e (standardGaussianVectorLaw (m + 1))
      ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin m => gaussianReal 0 1)) := by
    simpa [e, standardGaussianVectorLaw] using
      (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => gaussianReal 0 1) i)
  calc
    ∫ g : Fin (m + 1) → ℝ, F (e g) ∂standardGaussianVectorLaw (m + 1)
        = ∫ ty : ℝ × (Fin m → ℝ), F ty
            ∂((gaussianReal 0 1).prod (Measure.pi fun _ : Fin m => gaussianReal 0 1)) :=
          hp.integral_comp' F
    _ = ∫ y : Fin m → ℝ, ∫ t : ℝ, F (t, y) ∂gaussianReal 0 1
          ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) :=
          MeasureTheory.integral_prod_symm F hF

-- Integrability transport across the split `piFinSuccAbove` equivalence: a function is
-- integrable on the split product law iff its pullback is integrable on the vector law.
-- This is the integrability half of `integral_split_coord`; the equivalence is a measurable
-- map, so `integrable_map_equiv` applies with no measurability side condition.
private lemma integrable_split_coord_iff {m : ℕ} (i : Fin (m + 1))
    (F : ℝ × (Fin m → ℝ) → ℝ) :
    Integrable F ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin m => gaussianReal 0 1)) ↔
      Integrable (fun g : Fin (m + 1) → ℝ => F (g i, fun j : Fin m => g (i.succAbove j)))
        (standardGaussianVectorLaw (m + 1)) := by
  classical
  let e : (Fin (m + 1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i
  have hp : MeasurePreserving e (standardGaussianVectorLaw (m + 1))
      ((gaussianReal 0 1).prod (Measure.pi fun _ : Fin m => gaussianReal 0 1)) := by
    simpa [e, standardGaussianVectorLaw] using
      (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => gaussianReal 0 1) i)
  rw [← hp.map_eq]
  exact integrable_map_equiv e F

-- Stein's identity for a single coordinate of the squared-norm vector:
-- `E[g_i ^ 2 · X ^ k] = E[X ^ k] + 2k · E[g_i ^ 2 · X ^ (k-1)]` with `X = ∑ j, g j ^ 2`.
-- Proof: split off coordinate `i` with `integral_split_coord`, apply the one-dimensional
-- Stein identity `integral_sq_mul_sq_add_pow_stdGaussian` to the inner integral, then
-- reassemble the two terms with the same split.
private lemma integral_coord_sq_mul_sumSq_pow_stdGaussian (k n : ℕ) (i : Fin n) :
    ∫ g : Fin n → ℝ, g i ^ 2 * ((∑ j : Fin n, g j ^ 2) ^ k) ∂standardGaussianVectorLaw n =
      ∫ g : Fin n → ℝ, ((∑ j : Fin n, g j ^ 2) ^ k) ∂standardGaussianVectorLaw n +
        (2 : ℝ) * k * ∫ g : Fin n → ℝ, g i ^ 2 * ((∑ j : Fin n, g j ^ 2) ^ (k - 1))
          ∂standardGaussianVectorLaw n := by
  classical
  by_cases hn : n = 0
  · subst n
    exact False.elim (Nat.not_lt_zero i.1 i.2)
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    -- split-space integrands: `t` is the coordinate value, `y` collects the remaining coordinates
    let R : (Fin m → ℝ) → ℝ := fun y => ∑ j : Fin m, y j ^ 2
    let Fs : ℝ × (Fin m → ℝ) → ℝ := fun ty => ty.1 ^ 2 * (ty.1 ^ 2 + R ty.2) ^ k
    let F0 : ℝ × (Fin m → ℝ) → ℝ := fun ty => (ty.1 ^ 2 + R ty.2) ^ k
    let Fp : ℝ × (Fin m → ℝ) → ℝ := fun ty => ty.1 ^ 2 * (ty.1 ^ 2 + R ty.2) ^ (k - 1)
    -- Under the split, `∑ g ^ 2 = g i ^ 2 + (rest sum)`, so each split integrand matches its
    -- unsplit counterpart pointwise.
    have hFs (g : Fin (m + 1) → ℝ) :
        Fs (g i, fun j : Fin m => g (i.succAbove j)) =
          g i ^ 2 * ((∑ j : Fin (m + 1), g j ^ 2) ^ k) := by
      dsimp [Fs, R]
      congr 1
      rw [Fin.sum_univ_succAbove (fun j : Fin (m + 1) => g j ^ 2) i]
    have hF0 (g : Fin (m + 1) → ℝ) :
        F0 (g i, fun j : Fin m => g (i.succAbove j)) =
          (∑ j : Fin (m + 1), g j ^ 2) ^ k := by
      dsimp [F0, R]
      rw [Fin.sum_univ_succAbove (fun j : Fin (m + 1) => g j ^ 2) i]
    have hFp (g : Fin (m + 1) → ℝ) :
        Fp (g i, fun j : Fin m => g (i.succAbove j)) =
          g i ^ 2 * ((∑ j : Fin (m + 1), g j ^ 2) ^ (k - 1)) := by
      dsimp [Fp, R]
      congr 1
      rw [Fin.sum_univ_succAbove (fun j : Fin (m + 1) => g j ^ 2) i]
    -- Integrability on the split measure, transported from the known vector-law integrability.
    have hFs_int : Integrable Fs ((gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin m => gaussianReal 0 1)) := by
      rw [integrable_split_coord_iff i Fs]
      simpa [hFs] using integrable_sq_mul_sumSq_pow_stdGaussian k (m + 1) i
    have hF0_int : Integrable F0 ((gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin m => gaussianReal 0 1)) := by
      rw [integrable_split_coord_iff i F0]
      simpa [hF0] using integrable_sumSq_pow_stdGaussian k (m + 1)
    have hFp_int : Integrable Fp ((gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin m => gaussianReal 0 1)) := by
      rw [integrable_split_coord_iff i Fp]
      simpa [hFp] using integrable_sq_mul_sumSq_pow_stdGaussian (k - 1) (m + 1) i
    -- The inner (single-coordinate) integrals are integrable as functions of the rest.
    have hA_int : Integrable (fun y : Fin m → ℝ => ∫ t : ℝ, F0 (t, y) ∂gaussianReal 0 1)
        (Measure.pi fun _ : Fin m => gaussianReal 0 1) :=
      hF0_int.integral_prod_right
    have hB_int : Integrable (fun y : Fin m → ℝ => ∫ t : ℝ, Fp (t, y) ∂gaussianReal 0 1)
        (Measure.pi fun _ : Fin m => gaussianReal 0 1) :=
      hFp_int.integral_prod_right
    calc
      ∫ g : Fin (m + 1) → ℝ, g i ^ 2 * ((∑ j : Fin (m + 1), g j ^ 2) ^ k)
            ∂standardGaussianVectorLaw (m + 1)
          = ∫ g : Fin (m + 1) → ℝ, Fs (g i, fun j : Fin m => g (i.succAbove j))
              ∂standardGaussianVectorLaw (m + 1) := by
              simp [hFs]
      _ = ∫ y : Fin m → ℝ, ∫ t : ℝ, Fs (t, y) ∂gaussianReal 0 1
            ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) :=
            integral_split_coord i Fs hFs_int
      _ = ∫ y : Fin m → ℝ,
            (∫ t : ℝ, F0 (t, y) ∂gaussianReal 0 1 +
              (2 : ℝ) * k * ∫ t : ℝ, Fp (t, y) ∂gaussianReal 0 1)
              ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with y
            -- the one-dimensional Stein identity with `R = ∑ y ^ 2`
            simpa [Fs, F0, Fp, R] using integral_sq_mul_sq_add_pow_stdGaussian k (R y)
      _ = ∫ y : Fin m → ℝ, ∫ t : ℝ, F0 (t, y) ∂gaussianReal 0 1
            ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) +
          (2 : ℝ) * k * ∫ y : Fin m → ℝ, ∫ t : ℝ, Fp (t, y) ∂gaussianReal 0 1
            ∂(Measure.pi fun _ : Fin m => gaussianReal 0 1) := by
            rw [integral_add hA_int (hB_int.const_mul ((2 : ℝ) * k)),
              MeasureTheory.integral_const_mul]
      _ = ∫ g : Fin (m + 1) → ℝ, ((∑ j : Fin (m + 1), g j ^ 2) ^ k)
            ∂standardGaussianVectorLaw (m + 1) +
          (2 : ℝ) * k * ∫ g : Fin (m + 1) → ℝ,
            g i ^ 2 * ((∑ j : Fin (m + 1), g j ^ 2) ^ (k - 1))
            ∂standardGaussianVectorLaw (m + 1) := by
            -- reassemble the two terms back on the vector law
            rw [← integral_split_coord i F0 hF0_int, ← integral_split_coord i Fp hFp_int]
            congr 1
            · simp [hF0]
            · congr 1
              simp [hFp]

private lemma integral_sumSq_pow_stdGaussian_succ (k n : ℕ) :
    ∫ g : Fin n → ℝ, ((∑ i, g i ^ 2) ^ (k + 1)) ∂standardGaussianVectorLaw n =
      ((n : ℝ) + 2 * k) *
        ∫ g : Fin n → ℝ, ((∑ i, g i ^ 2) ^ k) ∂standardGaussianVectorLaw n := by
  classical
  by_cases hk : k = 0
  · -- `k = 0`: `∫ X = n` (each `g i ^ 2` contributes `1`) and the right side is `n · ∫ 1 = n`.
    have hk0 : k = 0 := hk
    have hprob : (standardGaussianVectorLaw n).real Set.univ = 1 := by
      simp [standardGaussianVectorLaw]
    have hcoord (i : Fin n) :
        ∫ g : Fin n → ℝ, g i ^ 2 ∂standardGaussianVectorLaw n = 1 := by
      simpa [hprob] using integral_coord_sq_mul_sumSq_pow_stdGaussian 0 n i
    calc
      ∫ g : Fin n → ℝ, ((∑ i : Fin n, g i ^ 2) ^ (k + 1)) ∂standardGaussianVectorLaw n
          = ∫ g : Fin n → ℝ, ((∑ i : Fin n, g i ^ 2) ^ (0 + 1)) ∂standardGaussianVectorLaw n := by
            rw [hk0]
      _ = ∫ g : Fin n → ℝ, (∑ i : Fin n, g i ^ 2) ∂standardGaussianVectorLaw n := by
            simp [pow_succ]
      _ = ∑ i : Fin n, ∫ g : Fin n → ℝ, g i ^ 2 ∂standardGaussianVectorLaw n := by
            exact (integral_finsetSum Finset.univ
              (f := fun (i : Fin n) (g : Fin n → ℝ) => g i ^ 2)
              (fun i _ => by simpa using integrable_sq_mul_sumSq_pow_stdGaussian 0 n i))
      _ = ∑ _i : Fin n, (1 : ℝ) := by
            simp [hcoord]
      _ = (n : ℝ) := by simp [Finset.sum_const, Fintype.card_fin]
      _ = ((n : ℝ) + 2 * k) *
            ∫ g : Fin n → ℝ, ((∑ i : Fin n, g i ^ 2) ^ k) ∂standardGaussianVectorLaw n := by
            rw [hk0]
            rw [show ∫ g : Fin n → ℝ, ((∑ i : Fin n, g i ^ 2) ^ 0)
                ∂standardGaussianVectorLaw n = 1 by simp [hprob]]
            norm_num
  · -- `k = k' + 1`: factor `X ^ (k + 1) = X · X ^ k`, apply the coordinate Stein identity to
    -- each summand `g i ^ 2 · X ^ k`, and recombine `∑ g i ^ 2 · X ^ k' = X · X ^ k'`.
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    calc
      ∫ g : Fin n → ℝ, ((∑ i : Fin n, g i ^ 2) ^ (k' + 1 + 1)) ∂standardGaussianVectorLaw n
          = ∫ g : Fin n → ℝ, ((∑ i : Fin n, g i ^ 2) * (∑ i : Fin n, g i ^ 2) ^ (k' + 1))
              ∂standardGaussianVectorLaw n := by
            simp [pow_succ']
      _ = ∫ g : Fin n → ℝ,
            (∑ i : Fin n, g i ^ 2 * (∑ j : Fin n, g j ^ 2) ^ (k' + 1))
              ∂standardGaussianVectorLaw n := by
            simp [Finset.sum_mul]
      _ = ∑ i : Fin n,
            ∫ g : Fin n → ℝ, g i ^ 2 * (∑ j : Fin n, g j ^ 2) ^ (k' + 1)
              ∂standardGaussianVectorLaw n := by
            exact (integral_finsetSum Finset.univ
              (f := fun (i : Fin n) (g : Fin n → ℝ) => g i ^ 2 * (∑ j : Fin n, g j ^ 2) ^ (k' + 1))
              (fun i _ => integrable_sq_mul_sumSq_pow_stdGaussian (k' + 1) n i))
      _ = ∑ i : Fin n,
            (∫ g : Fin n → ℝ, ((∑ j : Fin n, g j ^ 2) ^ (k' + 1)) ∂standardGaussianVectorLaw n +
              (2 : ℝ) * (k' + 1) *
                ∫ g : Fin n → ℝ, g i ^ 2 * (∑ j : Fin n, g j ^ 2) ^ k'
                  ∂standardGaussianVectorLaw n) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            -- the coordinate Stein identity with `k = k' + 1`
            simpa using integral_coord_sq_mul_sumSq_pow_stdGaussian (k' + 1) n i
      _ = (n : ℝ) *
            ∫ g : Fin n → ℝ, ((∑ j : Fin n, g j ^ 2) ^ (k' + 1)) ∂standardGaussianVectorLaw n +
          (2 : ℝ) * (k' + 1) *
            ∑ i : Fin n,
              ∫ g : Fin n → ℝ, g i ^ 2 * (∑ j : Fin n, g j ^ 2) ^ k'
                ∂standardGaussianVectorLaw n := by
            rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum]
            simp [Fintype.card_fin]
      _ = (n : ℝ) *
            ∫ g : Fin n → ℝ, ((∑ j : Fin n, g j ^ 2) ^ (k' + 1)) ∂standardGaussianVectorLaw n +
          (2 : ℝ) * (k' + 1) *
            ∫ g : Fin n → ℝ, (∑ i : Fin n, g i ^ 2) * (∑ j : Fin n, g j ^ 2) ^ k'
              ∂standardGaussianVectorLaw n := by
            -- `∑ i, ∫ g i ^ 2 · X ^ k' = ∫ (∑ g i ^ 2) · X ^ k'`
            rw [(integral_finsetSum Finset.univ
              (f := fun (i : Fin n) (g : Fin n → ℝ) => g i ^ 2 * (∑ j : Fin n, g j ^ 2) ^ k')
              (fun i _ => integrable_sq_mul_sumSq_pow_stdGaussian k' n i)).symm]
            congr 2
            simp [← Finset.sum_mul]
      _ = (n : ℝ) *
            ∫ g : Fin n → ℝ, ((∑ j : Fin n, g j ^ 2) ^ (k' + 1)) ∂standardGaussianVectorLaw n +
          (2 : ℝ) * (k' + 1) *
            ∫ g : Fin n → ℝ, ((∑ j : Fin n, g j ^ 2) ^ (k' + 1)) ∂standardGaussianVectorLaw n := by
            -- `X · X ^ k' = X ^ (k' + 1)`
            congr 2
            simp [pow_succ']
      _ = ((n : ℝ) + 2 * k'.succ) *
            ∫ g : Fin n → ℝ, ((∑ j : Fin n, g j ^ 2) ^ k'.succ) ∂standardGaussianVectorLaw n := by
            -- the conclusion is stated with `k = k'.succ`; unfold the successor in the cast
            rw [show (↑k'.succ : ℝ) = ↑k' + 1 by norm_num]
            ring

/-- Unnormalized chi-square moments for the squared norm of a standard Gaussian vector.

Informal proof: write `X g = ∑ i, g i ^ 2`.  The Gaussian integration-by-parts/Stein identity
for one coordinate, applied to `z * (z^2 + R)^k` while holding the other coordinates fixed, gives
`∫ X^(k+1) = ((n : ℝ) + 2*k) * ∫ X^k`.  The base case is the integral of the constant `1` under a
probability measure.  Induction over `k` then gives the product formula below.  This is exactly the
standard moment formula for a chi-square random variable with `n` degrees of freedom; see
<https://en.wikipedia.org/wiki/Chi-squared_distribution#Moments>.  A complete formal proof should
combine `Renormalization.integral_mul_pow_gaussianReal` with finite-product Fubini for
`Measure.pi`.
-/
theorem integral_sumSq_pow_stdGaussian (m n : ℕ) :
    ∫ g : Fin n → ℝ, ((∑ i, g i ^ 2) ^ m) ∂standardGaussianVectorLaw n =
      ∏ s ∈ Finset.range m, ((n : ℝ) + 2 * s) := by
  induction m with
  | zero =>
      simp [standardGaussianVectorLaw]
  | succ k ih =>
      calc
        ∫ g : Fin n → ℝ, ((∑ i, g i ^ 2) ^ (k + 1)) ∂standardGaussianVectorLaw n
            = ((n : ℝ) + 2 * k) *
                ∫ g : Fin n → ℝ, ((∑ i, g i ^ 2) ^ k) ∂standardGaussianVectorLaw n :=
              integral_sumSq_pow_stdGaussian_succ k n
        _ = ((n : ℝ) + 2 * k) *
              (∏ s ∈ Finset.range k, ((n : ℝ) + 2 * s)) := by
              rw [ih]
        _ = ∏ s ∈ Finset.range (k + 1), ((n : ℝ) + 2 * s) := by
              rw [Finset.prod_range_succ]
              ring

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
    ∫ g : Fin n → ℝ, (((n : ℝ)⁻¹ * ∑ i, g i ^ 2) ^ m) ∂standardGaussianVectorLaw n =
      widthMomentFactor m n := by
  calc
    ∫ g : Fin n → ℝ, (((n : ℝ)⁻¹ * ∑ i, g i ^ 2) ^ m) ∂standardGaussianVectorLaw n
        = ((n : ℝ)⁻¹) ^ m *
            ∫ g : Fin n → ℝ, ((∑ i, g i ^ 2) ^ m) ∂standardGaussianVectorLaw n := by
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
    ∫ g, NeuralNetwork.normalizedEnergy g ^ m ∂standardGaussianVectorLaw n =
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
(`MeasureTheory.measurePreserving_piCongrLeft`) yields the displayed pushforward of
`standardGaussianVectorLaw`. -/
private lemma oneLayerOutputLaw_eq_map_stdGaussian
    {ι : Type uI} {κ : Type uJ} [Fintype ι] [Fintype κ]
    (Cw : ℝ≥0) (x : ι → ℝ) :
    oneLayerOutputLaw (ι := ι) (κ := κ) Cw x =
      Measure.map
        (fun g : Fin (Fintype.card κ) → ℝ => fun j : κ =>
          Real.sqrt ((Cw : ℝ) * NeuralNetwork.normalizedEnergy x) * g (Fintype.equivFin κ j))
        (standardGaussianVectorLaw (Fintype.card κ)) := by
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
      refine measurable_pi_lambda _ (fun j => ?_)
      exact hT_meas.comp (measurable_pi_apply j)
    exact h1.comp hz_meas
  have hg_meas : Measurable (fun v : κ → EuclideanSpace ℝ PUnit =>
      fun j : κ => (v j) PUnit.unit) := by
    refine measurable_pi_lambda _ (fun j => ?_)
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
          (standardGaussianVectorLaw (Fintype.card κ)) := by
          dsimp [standardGaussianVectorLaw, s, e]

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
standard product Gaussian to `standardGaussianVectorLaw (Fintype.card κ)`.  Finally, pointwise,
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
          ∂standardGaussianVectorLaw (Fintype.card κ) := by
  classical
  let s : ℝ := (Cw : ℝ) * NeuralNetwork.normalizedEnergy x
  have hs : 0 ≤ s := by
    dsimp [s]
    exact mul_nonneg Cw.property (NeuralNetwork.normalizedEnergy_nonneg x)
  let φ : (Fin (Fintype.card κ) → ℝ) → κ → ℝ :=
    fun g j => Real.sqrt s * g (Fintype.equivFin κ j)
  have hLaw : oneLayerOutputLaw (ι := ι) (κ := κ) Cw x =
      Measure.map φ (standardGaussianVectorLaw (Fintype.card κ)) := by
    simpa [φ, s] using oneLayerOutputLaw_eq_map_stdGaussian Cw x
  have hφ_meas : Measurable φ := by
    dsimp [φ]
    refine measurable_pi_lambda _ (fun j => ?_)
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
            ∂Measure.map φ (standardGaussianVectorLaw (Fintype.card κ)) := by
          rw [hLaw]
    _ = ∫ g : Fin (Fintype.card κ) → ℝ,
          (NeuralNetwork.normalizedEnergy (φ g)) ^ m
          ∂standardGaussianVectorLaw (Fintype.card κ) := by
          rw [MeasureTheory.integral_map]
          · exact hφ_meas.aemeasurable
          · exact hcont.aestronglyMeasurable
    _ = ∫ g : Fin (Fintype.card κ) → ℝ, (s * NeuralNetwork.normalizedEnergy g) ^ m
          ∂standardGaussianVectorLaw (Fintype.card κ) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with g
          exact hpoint g
    _ = s ^ m *
          ∫ g : Fin (Fintype.card κ) → ℝ, NeuralNetwork.normalizedEnergy g ^ m
            ∂standardGaussianVectorLaw (Fintype.card κ) := by
          simp_rw [mul_pow]
          rw [MeasureTheory.integral_const_mul]
    _ = ((Cw : ℝ) * NeuralNetwork.normalizedEnergy x) ^ m *
          ∫ g : Fin (Fintype.card κ) → ℝ, NeuralNetwork.normalizedEnergy g ^ m
            ∂standardGaussianVectorLaw (Fintype.card κ) := by
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
              ∂standardGaussianVectorLaw (Fintype.card κ) := by
          exact integral_normalizedEnergy_pow_oneLayerOutputLaw_eq_scaled_stdGaussian Cw x m
    _ = ((Cw : ℝ) * NeuralNetwork.normalizedEnergy x) ^ m *
          widthMomentFactor m (Fintype.card κ) := by
          rw [integral_normalizedEnergy_pow_stdGaussian m (Fintype.card κ) hκ]

end NeuralNetwork.DeepLinear

end

end
