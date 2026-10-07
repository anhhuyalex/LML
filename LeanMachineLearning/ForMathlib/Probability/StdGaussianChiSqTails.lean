/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.StdGaussianRadial

/-!
# Chi-squared fourth moment and tail bounds for standard Gaussian vectors

For `x ~ stdGaussian E` with `dim E = k`, the variable `‖x‖²` is `χ²_k`. The radial moment formula
of `ForMathlib/Probability/StdGaussianRadial.lean` (`E ‖x‖^a = 2^(a/2) Γ ((k+a)/2) / Γ (k/2)`)
gives, in this file, the exact fourth central moment and the resulting tail bound used, in the
double-descent development, to concentrate `Tr ((Gᵀ G)⁻¹) = ∑ⱼ 1 / χ²_{p-q+1}` for a Gaussian
`G ∈ ℝ^{p × q}` without ever estimating covariances between the diagonal entries:

* `integral_norm_sq_sub_pow_four`: `E (‖x‖² - k)⁴ = 12 k² + 48 k`;
* `measureReal_norm_sq_sub_abs_ge_le`: `ℙ (|‖x‖² - k| ≥ t) ≤ (12 k² + 48 k) / t⁴`;
* `measureReal_norm_sq_sub_ge_le`: `ℙ (|‖x‖² - k| ≥ ε k) ≤ 60 / (ε⁴ k²)`;
* `measure_dev_le_of_map_norm_sq`: the same bound for any random variable *with the law* of `‖x‖²`,
  the form in which the tails are applied to `‖P g‖²`, `‖g‖²` and `1 / ((Wᵀ W)⁻¹)ⱼⱼ`.

The inverse moments `E 1/χ²_k = 1/(k-2)` and `E 1/χ⁴_k = 1/((k-2)(k-4))` are
`integral_inv_norm_sq_stdGaussian` and `integral_inv_norm_sq_sq_stdGaussian` in the radial file.
-/

@[expose]
public section

namespace ProbabilityTheory

open MeasureTheory ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

private lemma sub_pow_four_expand (y k : ℝ) :
    (y - k) ^ 4 = y ^ 4 + (-4 * k) * y ^ 3 + (6 * k ^ 2) * y ^ 2 + (-4 * k ^ 3) * y ^ 1 +
      (k ^ 4) * y ^ 0 := by ring

/-- The fourth central moment `(‖x‖² - c)⁴` is integrable under `stdGaussian E` for any centre
`c`. It is a polynomial of degree four in the `χ²_k` variable `‖x‖²`. -/
theorem integrable_norm_sq_sub_pow_four (c : ℝ) :
    Integrable (fun x : E => (‖x‖ ^ 2 - c) ^ 4) (stdGaussian E) := by
  simp_rw [sub_pow_four_expand]
  exact ((((integrable_norm_sq_pow_stdGaussian 4).add
    ((integrable_norm_sq_pow_stdGaussian 3).const_mul _)).add
    ((integrable_norm_sq_pow_stdGaussian 2).const_mul _)).add
    ((integrable_norm_sq_pow_stdGaussian 1).const_mul _)).add
    ((integrable_norm_sq_pow_stdGaussian 0).const_mul _)

/-- **Fourth central moment of `χ²_k`.** For `dim E = k`,
`E (‖x‖² - k)⁴ = 12 k² + 48 k`.

Proof: expand `(y - k)⁴` and insert the moments `E y^j = ∏_{i<j} (k + 2 i)` for `j ≤ 4`
(`integral_norm_sq_pow_stdGaussian`). -/
theorem integral_norm_sq_sub_pow_four :
    ∫ x : E, (‖x‖ ^ 2 - (Module.finrank ℝ E : ℝ)) ^ 4 ∂stdGaussian E =
      12 * (Module.finrank ℝ E : ℝ) ^ 2 + 48 * (Module.finrank ℝ E : ℝ) := by
  set k : ℝ := (Module.finrank ℝ E : ℝ) with hk
  have i0 := integrable_norm_sq_pow_stdGaussian (E := E) 0
  have i1 := integrable_norm_sq_pow_stdGaussian (E := E) 1
  have i2 := integrable_norm_sq_pow_stdGaussian (E := E) 2
  have i3 := integrable_norm_sq_pow_stdGaussian (E := E) 3
  have i4 := integrable_norm_sq_pow_stdGaussian (E := E) 4
  simp_rw [sub_pow_four_expand]
  have j1 : Integrable (fun x : E => (‖x‖ ^ 2) ^ 4 + (-4 * k) * (‖x‖ ^ 2) ^ 3)
      (stdGaussian E) := i4.add (i3.const_mul _)
  have j2 : Integrable (fun x : E => (‖x‖ ^ 2) ^ 4 + (-4 * k) * (‖x‖ ^ 2) ^ 3 +
      (6 * k ^ 2) * (‖x‖ ^ 2) ^ 2) (stdGaussian E) := j1.add (i2.const_mul _)
  have j3 : Integrable (fun x : E => (‖x‖ ^ 2) ^ 4 + (-4 * k) * (‖x‖ ^ 2) ^ 3 +
      (6 * k ^ 2) * (‖x‖ ^ 2) ^ 2 + (-4 * k ^ 3) * (‖x‖ ^ 2) ^ 1) (stdGaussian E) :=
    j2.add (i1.const_mul _)
  rw [integral_add j3 (i0.const_mul _), integral_add j2 (i1.const_mul _),
    integral_add j1 (i2.const_mul _), integral_add i4 (i3.const_mul _)]
  simp only [integral_const_mul, integral_norm_sq_pow_stdGaussian, Finset.prod_range_succ,
    Finset.prod_range_zero]
  push_cast
  ring

/-- **Absolute tail bound for `χ²_k`.** For `dim E = k` and `t > 0`,
`ℙ (|‖x‖² - k| ≥ t) ≤ (12 k² + 48 k) / t⁴`.

Proof: Markov's inequality for `(‖x‖² - k)⁴`, whose mean is `12 k² + 48 k`
(`integral_norm_sq_sub_pow_four`). -/
theorem measureReal_norm_sq_sub_abs_ge_le {t : ℝ} (ht : 0 < t) :
    (stdGaussian E).real {x : E | t ≤ |‖x‖ ^ 2 - Module.finrank ℝ E|} ≤
      (12 * (Module.finrank ℝ E : ℝ) ^ 2 + 48 * (Module.finrank ℝ E : ℝ)) / t ^ 4 := by
  set k : ℝ := (Module.finrank ℝ E : ℝ) with hkdef
  have ht4 : 0 < t ^ 4 := by positivity
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := stdGaussian E)
    (f := fun x : E => (‖x‖ ^ 2 - k) ^ 4)
    (Filter.Eventually.of_forall fun x => by positivity)
    (integrable_norm_sq_sub_pow_four k) (t ^ 4)
  rw [integral_norm_sq_sub_pow_four] at hM
  have hsub : {x : E | t ≤ |‖x‖ ^ 2 - k|} ⊆ {x : E | t ^ 4 ≤ (‖x‖ ^ 2 - k) ^ 4} := by
    intro x hx
    have : t ^ 4 ≤ |‖x‖ ^ 2 - k| ^ 4 := pow_le_pow_left₀ ht.le hx 4
    simpa [pow_abs, abs_pow, Even.pow_abs (by decide : Even 4)] using this
  calc (stdGaussian E).real {x : E | t ≤ |‖x‖ ^ 2 - k|}
      ≤ (stdGaussian E).real {x : E | t ^ 4 ≤ (‖x‖ ^ 2 - k) ^ 4} := measureReal_mono hsub
    _ ≤ (12 * k ^ 2 + 48 * k) / t ^ 4 := by rw [le_div_iff₀ ht4]; linarith

/-- **Relative tail bound for `χ²_k`.** For `dim E = k` and `ε > 0`,
`ℙ (|‖x‖² - k| ≥ ε k) ≤ 60 / (ε⁴ k²)`.

Summed over `q` entries by a union bound this is `60 q / (ε⁴ ν²) → 0` when `q ≍ ν`, which is what
concentrates `Tr ((Gᵀ G)⁻¹)`. -/
theorem measureReal_norm_sq_sub_ge_le {ε : ℝ} (hε : 0 < ε) :
    (stdGaussian E).real {x : E | ε * (Module.finrank ℝ E : ℝ) ≤
        |‖x‖ ^ 2 - Module.finrank ℝ E|} ≤ 60 / (ε ^ 4 * (Module.finrank ℝ E : ℝ) ^ 2) := by
  have hk : (1 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast Module.finrank_pos
  set k : ℝ := (Module.finrank ℝ E : ℝ) with hkdef
  have hεk : 0 < (ε * k) ^ 4 := by positivity
  refine (measureReal_norm_sq_sub_abs_ge_le (by positivity : 0 < ε * k)).trans ?_
  rw [div_le_div_iff₀ hεk (by positivity)]
  have : 0 < ε ^ 4 := by positivity
  nlinarith [mul_pos this (show 0 < k by linarith), sq_nonneg k,
    mul_pos this (mul_pos (show 0 < k by linarith) (show 0 < k by linarith))]

/-- **`χ²` tail bound for any variable with the law of `‖x‖²`.** If `f` has under `μ` the law of
`‖x‖²`, `x ~ stdGaussian (ℝ^k)` with `k ≥ 1`, then `μ (|f - k| ≥ ε k) ≤ 60 / (ε⁴ k²)`. -/
theorem measure_dev_le_of_map_norm_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Measurable f) {k : ℕ} (hk : 0 < k)
    (hlaw : μ.map f = (stdGaussian (EuclideanSpace ℝ (Fin k))).map (fun x => ‖x‖ ^ 2))
    {ε : ℝ} (hε : 0 < ε) :
    μ {a | ε * k ≤ |f a - k|} ≤ ENNReal.ofReal (60 / (ε ^ 4 * (k : ℝ) ^ 2)) := by
  have : NeZero k := ⟨hk.ne'⟩
  have hset : MeasurableSet {y : ℝ | ε * k ≤ |y - k|} :=
    measurableSet_le measurable_const (by fun_prop)
  have h1 := Measure.map_apply (μ := μ) hf hset
  rw [hlaw, Measure.map_apply (by fun_prop) hset] at h1
  have h2 := measureReal_norm_sq_sub_ge_le (E := EuclideanSpace ℝ (Fin k)) hε
  simp only [finrank_euclideanSpace, Fintype.card_fin] at h2
  have : {a | ε * k ≤ |f a - k|} = f ⁻¹' {y : ℝ | ε * k ≤ |y - k|} := rfl
  rw [this, ← h1, ← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal h2

end ProbabilityTheory

end
