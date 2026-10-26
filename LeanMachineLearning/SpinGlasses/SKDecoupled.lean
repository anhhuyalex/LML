/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.HypercubeProduct
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.Tanh
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.SqSub
public import LeanMachineLearning.SpinGlasses.Basic
public import LeanMachineLearning.SpinGlasses.GibbsMeasure
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Probability.IdentDistrib

/-!
# Decoupled Non-Interacting Spins in the Sherrington–Kirkpatrick Model

This file formalizes the decoupled, non-interacting spin reference system
(Michel Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, 2010, Section 1.2,
Eqs. (1.29)–(1.36) and (1.104)):
$$-H_0(\boldsymbol{\sigma}) = \sum_{i \in \iota} \sigma_i Y_i,
\qquad Y_i = \beta z_i \sqrt{q} + h_i.$$

Because there are no interactions between distinct sites, the partition function factors explicitly
via the hypercube product identity (`hypercube_sum_prod_eq_prod_add`), the Gibbs measure is an
exact product measure, and local single-spin magnetizations and replica overlaps evaluate
in closed form to hyperbolic functions.

## Main declarations

* `SpinGlasses.integrable_tanh_sq`: integrability of `tanh²(Y)` under any probability measure.
* `SpinGlasses.decoupled_partition_function_eq`:
  $Z_0 = 2^N \prod_{i \in \iota} \cosh(Y_i)$ (Eq. 1.32).
* `SpinGlasses.decoupled_sum_spin_mul_exp_eq`:
  single-spin weighted sum factors into $2 \sinh(Y_j) \prod_{i \ne j} (2 \cosh(Y_i))$.
* `SpinGlasses.decoupled_gibbs_spin_eq`:
  local marginal magnetization $\langle \sigma_j \rangle_0 = \tanh(Y_j)$ (Eq. 1.36).
* `SpinGlasses.decoupled_gibbs_replica_two_eq`:
  two-replica local correlation $\langle \sigma_j^1 \sigma_j^2 \rangle_0 = \tanh^2(Y_j)$.
* `SpinGlasses.decoupled_gibbs_overlap_eq`:
  average overlap of two independent replicas is $|\iota|^{-1} \sum_j \tanh^2(Y_j)$.
* `SpinGlasses.decoupled_replica_overlap_eq`:
  expected replica overlap under identically distributed fields equals
  $\mathbb{E} \tanh^2(\beta z \sqrt{q} + h)$ (Eq. 1.104).
* `SpinGlasses.decoupled_free_energy_eq`:
  expected free energy $p_N(0) = \log 2 + \mathbb{E} \log \cosh(Y)$ (Eq. 1.33).

## References

* [M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Springer, 2010], §1.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Real Matrix

namespace SpinGlasses

/-- Integrability of `tanh²(Y)` under any probability measure for an almost-everywhere
measurable random variable `Y`. -/
lemma integrable_tanh_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P) :
    Integrable (fun ω => Real.tanh (Y ω) ^ 2) P :=
  MeasureTheory.integrable_tanh_sq' Y hY

/-- For any random variable `Y` under a probability measure,
`∫ tanh⁴(Y) - 2 ∫ tanh²(Y) + 1 = ∫ (1 - tanh²(Y))² ∈ [0, 1]`. -/
theorem probability_tanh_fourth_sub_two_add_one_mem_Icc {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : AEMeasurable Y P) :
    (∫ ω, Real.tanh (Y ω) ^ 4 ∂P) - 2 * (∫ ω, Real.tanh (Y ω) ^ 2 ∂P) + 1 ∈ Set.Icc (0 : ℝ) 1 := by
  have h2 := integrable_tanh_sq Y hY
  have h4 := MeasureTheory.integrable_tanh_pow Y hY 4
  have key : (∫ ω, Real.tanh (Y ω) ^ 4 ∂P) - 2 * (∫ ω, Real.tanh (Y ω) ^ 2 ∂P) + 1 =
      ∫ ω, (1 - Real.tanh (Y ω) ^ 2) ^ 2 ∂P := by
    have e : ∀ ω, (1 - Real.tanh (Y ω) ^ 2) ^ 2 =
        (Real.tanh (Y ω) ^ 4 - 2 * Real.tanh (Y ω) ^ 2) + 1 := fun ω => by ring
    simp_rw [e]
    have hi : Integrable (fun ω => Real.tanh (Y ω) ^ 4 -
        2 * Real.tanh (Y ω) ^ 2) P := h4.sub (h2.const_mul 2)
    rw [integral_add hi (integrable_const _), integral_sub h4 (h2.const_mul 2),
      integral_const_mul]
    simp
  rw [key]
  have hb : ∀ ω, 0 ≤ (1 - Real.tanh (Y ω) ^ 2) ^ 2 ∧
      (1 - Real.tanh (Y ω) ^ 2) ^ 2 ≤ 1 := fun ω => by
    have h0 : 0 ≤ Real.tanh (Y ω) ^ 2 := sq_nonneg _
    have h1 : Real.tanh (Y ω) ^ 2 ≤ 1 := by
      have := Real.abs_tanh_lt_one (Y ω)
      nlinarith [abs_nonneg (Real.tanh (Y ω)), sq_abs (Real.tanh (Y ω))]
    exact ⟨sq_nonneg _, by nlinarith⟩
  refine ⟨integral_nonneg fun ω => (hb ω).1, ?_⟩
  calc _ ≤ ∫ ω, (1 : ℝ) ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => (hb ω).1) (integrable_const _)
          (ae_of_all _ fun ω => (hb ω).2)
    _ = 1 := by simp

variable {ι : Type*} [Fintype ι]

/-- **Decoupled Partition Function (Eq. 1.32):**
For non-interacting spins in fields `Y i`, the partition function factors
into `2^N ∏ cosh(Y i)`. -/
theorem decoupled_partition_function_eq [DecidableEq ι] (Y : ι → ℝ) :
    ∑ σ : ι → ℤˣ, Real.exp (∑ i, ((σ i : ℤ) : ℝ) * Y i) =
      (2 : ℝ) ^ Fintype.card ι * ∏ i, Real.cosh (Y i) := by
  have h_exp (σ : ι → ℤˣ) : Real.exp (∑ i, ((σ i : ℤ) : ℝ) * Y i) =
      ∏ i, Real.exp (((σ i : ℤ) : ℝ) * Y i) := by
    rw [Real.exp_sum]
  simp_rw [h_exp]
  rw [hypercube_sum_prod_eq_prod_add (fun i s => Real.exp (((s : ℤ) : ℝ) * Y i))]
  have h_cosh : (∏ i : ι, (Real.exp ((((1 : ℤˣ) : ℤ) : ℝ) * Y i) +
      Real.exp ((((-1 : ℤˣ) : ℤ) : ℝ) * Y i))) = ∏ i, (2 * Real.cosh (Y i)) := by
    congr 1
    ext i
    rw [Real.cosh_eq]
    simp
    ring
  rw [h_cosh, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-- Decoupled partition function expressed as a product over `univ.erase j` and coordinate `j`. -/
theorem decoupled_partition_function_eq_mul_erase [DecidableEq ι] (Y : ι → ℝ) (j : ι) :
    ∑ σ : ι → ℤˣ, Real.exp (∑ i, ((σ i : ℤ) : ℝ) * Y i) =
      (2 * Real.cosh (Y j)) * ∏ i ∈ Finset.univ.erase j, (2 * Real.cosh (Y i)) := by
  simp_rw [Real.exp_sum]
  rw [hypercube_sum_prod_erase_eq_prod_add (fun i s => Real.exp (((s : ℤ) : ℝ) * Y i)) j]
  simp only [Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, one_mul, neg_mul,
    Real.cosh_eq]
  congr 1 <;> [ring; exact Finset.prod_congr rfl fun i _ => by ring]

/-- **Decoupled Single-Spin Weighted Sum:**
`∑ σ, σ j * exp(∑ i, σ i * Y i) = 2 sinh(Y j) * ∏_{i ≠ j} (2 cosh(Y i))`. -/
theorem decoupled_sum_spin_mul_exp_eq [DecidableEq ι] (Y : ι → ℝ) (j : ι) :
    ∑ σ : ι → ℤˣ, ((σ j : ℤ) : ℝ) * Real.exp (∑ i, ((σ i : ℤ) : ℝ) * Y i) =
      (2 * Real.sinh (Y j)) * ∏ i ∈ Finset.univ.erase j, (2 * Real.cosh (Y i)) := by
  let a : ι → ℤˣ → ℝ := fun i s =>
    if i = j then ((s : ℤ) : ℝ) * Real.exp (((s : ℤ) : ℝ) * Y i)
    else Real.exp (((s : ℤ) : ℝ) * Y i)
  have h_prod (σ : ι → ℤˣ) : ((σ j : ℤ) : ℝ) * Real.exp (∑ i, ((σ i : ℤ) : ℝ) * Y i) =
      ∏ i, a i (σ i) := by
    rw [Real.exp_sum, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
      ← Finset.mul_prod_erase Finset.univ (fun i => a i (σ i)) (Finset.mem_univ j)]
    rw [← mul_assoc]
    congr 1
    · simp [a]
    · exact Finset.prod_congr rfl fun i hi => by simp [a, Finset.ne_of_mem_erase hi]
  simp_rw [h_prod]
  rw [hypercube_sum_prod_erase_eq_prod_add a j]
  congr 1
  · simp [a, Real.sinh_eq]
    ring
  · refine Finset.prod_congr rfl fun i hi => ?_
    simp [a, Finset.ne_of_mem_erase hi, Real.cosh_eq]
    ring

/-- **Decoupled Local Marginal Magnetization (Eq. 1.36):**
The Gibbs average of spin `σ j` in the decoupled model is `tanh(Y j)`. -/
theorem decoupled_gibbs_spin_eq (Y : ι → ℝ) (j : ι) :
    ∫ σ : ι → ℤˣ, ((σ j : ℤ) : ℝ)
      ∂(Measure.count.tilted fun σ => ∑ i, ((σ i : ℤ) : ℝ) * Y i) =
        Real.tanh (Y j) := by
  classical
  rw [integral_count_tilted]
  have h_num : (∑ a : ι → ℤˣ, Real.exp (∑ i, ((a i : ℤ) : ℝ) * Y i) * ((a j : ℤ) : ℝ)) =
      (2 * Real.sinh (Y j)) * ∏ i ∈ Finset.univ.erase j, (2 * Real.cosh (Y i)) := by
    have := decoupled_sum_spin_mul_exp_eq Y j
    simpa [mul_comm] using this
  have h_denom : (∑ b : ι → ℤˣ, Real.exp (∑ i, ((b i : ℤ) : ℝ) * Y i)) =
      (2 * Real.cosh (Y j)) * ∏ i ∈ Finset.univ.erase j, (2 * Real.cosh (Y i)) :=
    decoupled_partition_function_eq_mul_erase Y j
  have h_pos : 0 < ∏ i ∈ Finset.univ.erase j, (2 * Real.cosh (Y i)) := by
    apply Finset.prod_pos
    intro i _hi
    positivity
  have h_prod_ne : (∏ i ∈ Finset.univ.erase j, (2 * Real.cosh (Y i))) ≠ 0 :=
    ne_of_gt h_pos
  have h_sum_div : (∑ a : ι → ℤˣ, Real.exp (∑ i, ((a i : ℤ) : ℝ) * Y i) /
      (∑ b : ι → ℤˣ, Real.exp (∑ i, ((b i : ℤ) : ℝ) * Y i)) * ((a j : ℤ) : ℝ)) =
      (∑ a : ι → ℤˣ, Real.exp (∑ i, ((a i : ℤ) : ℝ) * Y i) * ((a j : ℤ) : ℝ)) /
        (∑ b : ι → ℤˣ, Real.exp (∑ i, ((b i : ℤ) : ℝ) * Y i)) := by
    simp_rw [div_mul_eq_mul_div]
    rw [Finset.sum_div]
  rw [h_sum_div, h_num, h_denom]
  have h_cancel : ((2 * Real.sinh (Y j)) * ∏ i ∈ Finset.univ.erase j, (2 * Real.cosh (Y i))) /
      ((2 * Real.cosh (Y j)) * ∏ i ∈ Finset.univ.erase j, (2 * Real.cosh (Y i))) =
      (2 * Real.sinh (Y j)) / (2 * Real.cosh (Y j)) := by
    rw [mul_div_mul_right _ _ h_prod_ne]
  rw [h_cancel, mul_div_mul_left (Real.sinh (Y j)) (Real.cosh (Y j)) (by norm_num)]
  exact (Real.tanh_eq_sinh_div_cosh (Y j)).symm

/-- **Decoupled Two-Replica Local Correlation:**
For two independent replicas under the decoupled Gibbs measure,
`⟨σ_j¹ σ_j²⟩₀ = tanh²(Y j)`. -/
theorem decoupled_gibbs_replica_two_eq (Y : ι → ℝ) (j : ι) :
    ∫ p : (ι → ℤˣ) × (ι → ℤˣ), ((p.1 j : ℤ) : ℝ) * ((p.2 j : ℤ) : ℝ)
      ∂((Measure.count.tilted fun σ => ∑ i, ((σ i : ℤ) : ℝ) * Y i).prod
        (Measure.count.tilted fun σ => ∑ i, ((σ i : ℤ) : ℝ) * Y i)) =
      Real.tanh (Y j) ^ 2 := by
  have := integral_prod_mul (μ := (Measure.count.tilted fun σ => ∑ i, ((σ i : ℤ) : ℝ) * Y i))
    (ν := (Measure.count.tilted fun σ => ∑ i, ((σ i : ℤ) : ℝ) * Y i))
    (fun σ : ι → ℤˣ => ((σ j : ℤ) : ℝ)) (fun τ : ι → ℤˣ => ((τ j : ℤ) : ℝ))
  rw [this, decoupled_gibbs_spin_eq Y j, sq]

/-- **Decoupled Gibbs Overlap Expectation:**
The expectation of the overlap `R(σ¹, σ²) = N⁻¹ ∑_j σ_j¹ σ_j²` under two independent replicas
equals `N⁻¹ ∑_j tanh²(Y j)`. -/
theorem decoupled_gibbs_overlap_eq (Y : ι → ℝ) :
    ∫ p : (ι → ℤˣ) × (ι → ℤˣ),
      ((Fintype.card ι : ℝ)⁻¹ * ∑ j, ((p.1 j : ℤ) : ℝ) * ((p.2 j : ℤ) : ℝ))
      ∂((Measure.count.tilted fun σ => ∑ i, ((σ i : ℤ) : ℝ) * Y i).prod
        (Measure.count.tilted fun σ => ∑ i, ((σ i : ℤ) : ℝ) * Y i)) =
      (Fintype.card ι : ℝ)⁻¹ * ∑ j, Real.tanh (Y j) ^ 2 := by
  rw [integral_const_mul]
  congr 1
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro j _hj
    exact decoupled_gibbs_replica_two_eq Y j
  · intro j _hj
    exact Integrable.of_finite

/-- **Decoupled Replica Overlap Expectation (Eq. 1.104):**
For identically distributed fields across sites, the expected overlap of two replicas
is `q = 𝔼 tanh²(β z √q + h)`. -/
theorem decoupled_replica_overlap_eq [Nonempty ι]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : ι → Ω → ℝ) (j₀ : ι)
    (h_law : ∀ j, IdentDistrib (Y j) (Y j₀) P P) :
    ∫ ω, (Fintype.card ι : ℝ)⁻¹ * ∑ j, Real.tanh (Y j ω) ^ 2 ∂P =
      ∫ ω, Real.tanh (Y j₀ ω) ^ 2 ∂P := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [integral_const_mul]
  rw [integral_finsetSum Finset.univ]
  · have h_each : ∀ j : ι, ∫ ω, Real.tanh (Y j ω) ^ 2 ∂P = ∫ ω, Real.tanh (Y j₀ ω) ^ 2 ∂P := by
      intro j
      have hid : IdentDistrib (fun ω => Real.tanh (Y j ω) ^ 2)
          (fun ω => Real.tanh (Y j₀ ω) ^ 2) P P := by
        exact (h_law j).comp ((continuous_pow 2).comp Real.continuous_tanh).measurable
      exact hid.integral_eq
    simp_rw [h_each, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  · intro j _hj
    exact integrable_tanh_sq (Y j) (h_law j).aemeasurable_fst

/-- **Decoupled Expected Free Energy (Eq. 1.33):**
The expected free energy of the non-interacting model equals `log 2 + 𝔼 log cosh(Y)`. -/
theorem decoupled_free_energy_eq [DecidableEq ι] [Nonempty ι]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : ι → Ω → ℝ) (j₀ : ι)
    (h_law : ∀ j, IdentDistrib (Y j) (Y j₀) P P)
    (h_int : Integrable (fun ω => Real.log (Real.cosh (Y j₀ ω))) P) :
    (Fintype.card ι : ℝ)⁻¹ *
        ∫ ω, Real.log (∑ σ : ι → ℤˣ, Real.exp (∑ i, ((σ i : ℤ) : ℝ) * Y i ω)) ∂P =
      Real.log 2 + ∫ ω, Real.log (Real.cosh (Y j₀ ω)) ∂P := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h_part (ω : Ω) : Real.log (∑ σ : ι → ℤˣ, Real.exp (∑ i, ((σ i : ℤ) : ℝ) * Y i ω)) =
      (Fintype.card ι : ℝ) * Real.log 2 + ∑ i, Real.log (Real.cosh (Y i ω)) := by
    rw [decoupled_partition_function_eq (fun i => Y i ω)]
    have h_prod_pos : 0 < ∏ i, Real.cosh (Y i ω) := by
      apply Finset.prod_pos
      intro i _hi
      exact Real.cosh_pos (Y i ω)
    rw [Real.log_mul (by positivity) (ne_of_gt h_prod_pos)]
    rw [Real.log_pow]
    congr 1
    exact Real.log_prod (fun i _hi => ne_of_gt (Real.cosh_pos _))
  simp_rw [h_part]
  have h_meas : Measurable (fun x : ℝ => Real.log (Real.cosh x)) :=
    (Real.continuous_cosh.log (fun x => ne_of_gt (Real.cosh_pos x))).measurable
  have h_int_all : ∀ j : ι, Integrable (fun ω => Real.log (Real.cosh (Y j ω))) P := by
    intro j
    have hid : IdentDistrib (fun ω => Real.log (Real.cosh (Y j ω)))
        (fun ω => Real.log (Real.cosh (Y j₀ ω))) P P := (h_law j).comp h_meas
    exact hid.integrable_iff.2 h_int
  have h_sum_int : Integrable (fun ω => ∑ i : ι, Real.log (Real.cosh (Y i ω))) P :=
    integrable_finsetSum Finset.univ (fun i _ => h_int_all i)
  rw [integral_add (integrable_const _) h_sum_int]
  rw [integral_const, probReal_univ, one_smul]
  rw [integral_finsetSum Finset.univ (fun i _ => h_int_all i)]
  have h_each : ∀ j : ι, ∫ ω, Real.log (Real.cosh (Y j ω)) ∂P =
      ∫ ω, Real.log (Real.cosh (Y j₀ ω)) ∂P := by
    intro j
    exact ((h_law j).comp h_meas).integral_eq
  simp_rw [h_each, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-- The cavity field `β √q ∑ᵢ zᵢ σᵢ + h ∑ᵢ σᵢ` as a sum over the sites of the local fields
`β √q zᵢ + h`. -/
theorem decoupled_field_eq {N : ℕ} (β h q : ℝ) (z : Fin N → ℝ) (a : Fin N → ℤˣ) :
    β * Real.sqrt q * (∑ i, z i * ((a i : ℤ) : ℝ)) + h * ∑ i, ((a i : ℤ) : ℝ) =
      ∑ i, ((a i : ℤ) : ℝ) * (β * Real.sqrt q * z i + h) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end SpinGlasses
