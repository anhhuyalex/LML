/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Probability.Martingale.Convergence

/-!
# Nested conditional expectations in `L²`: Pythagoras and the equality case

For `m₁ ≤ m₂ ≤ m₀` and `f ∈ L²(μ)` the conditional expectations `μ[f | m₁]` and `μ[f | m₂]` are
orthogonal projections of `f` onto nested closed subspaces, so the smaller one is the projection of
the larger one and the Pythagorean theorem holds:
`‖μ[f | m₂] - μ[f | m₁]‖² = ‖μ[f | m₂]‖² - ‖μ[f | m₁]‖²`.
In particular the `L²` norm is monotone in the σ-algebra, and *equality of the norms forces equality
of the conditional expectations*.  This single fact is the engine of both Lemma 1.5
(exchangeable sequences) and Lemma 1.6 (weakly exchangeable arrays) of [Panchenko, 2013, §1.4].

Everything is proved with the function-level API (`condExp_condExp_of_le`, the pull-out property
and `integral_condExp`), not with `condExpL2`.

## Main declarations

* `MeasureTheory.integral_mul_condExp_of_stronglyMeasurable`: for `h` `m`-measurable,
  `∫ h * μ[g | m] = ∫ h * g`.
* `MeasureTheory.integral_condExp_mul_condExp_of_le`:
  `∫ μ[f | m₁] * μ[f | m₂] = ∫ (μ[f | m₁])²` for `m₁ ≤ m₂`.
* `MeasureTheory.integral_sq_condExp_sub_condExp_of_le`: the Pythagorean identity.
* `MeasureTheory.integral_sq_condExp_le_of_le`: monotonicity of the `L²` norm.
* `MeasureTheory.condExp_ae_eq_of_integral_sq_condExp_eq`: equal norms imply equal conditional
  expectations almost everywhere.
* `MeasureTheory.condExp_ae_eq_of_le_of_le`: if two conditional expectations agree, so does every
  one in between.
* `MeasureTheory.tendsto_integral_sq_condExp`: along an increasing sequence of σ-algebras the `L²`
  norms of `μ[f | 𝒢 n]` converge to that of `μ[f | ⨆ n, 𝒢 n]` (Lévy's upward theorem).  This lets
  one compute the norm for an infinite conditioning family from finite sub-families.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], proofs of Lemmas 1.5, 1.6.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace MeasureTheory

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {m m₁ m₂ : MeasurableSpace Ω} {f g h : Ω → ℝ}

/-- **Self-adjointness of the conditional expectation:** if `h` is `m`-measurable and the products
are integrable then `∫ h * μ[g | m] = ∫ h * g`. -/
theorem integral_mul_condExp_of_stronglyMeasurable (hm : m ≤ m₀) (hh : StronglyMeasurable[m] h)
    (hhg : Integrable (h * g) μ) (hg : Integrable g μ) :
    ∫ ω, h ω * μ[g | m] ω ∂μ = ∫ ω, h ω * g ω ∂μ := by
  have h1 : μ[h * g | m] =ᵐ[μ] h * μ[g | m] := condExp_mul_of_stronglyMeasurable_left hh hhg hg
  calc ∫ ω, h ω * μ[g | m] ω ∂μ = ∫ ω, μ[h * g | m] ω ∂μ :=
        integral_congr_ae (h1.mono fun ω hω => hω.symm)
    _ = ∫ ω, h ω * g ω ∂μ := integral_condExp hm

/-- For `m₁ ≤ m₂ ≤ m₀` and `f ∈ L²`: `∫ μ[f | m₁] * μ[f | m₂] = ∫ (μ[f | m₁])²`; the finer
projection has the same inner product with `μ[f | m₁]` as `μ[f | m₁]` itself. -/
theorem integral_condExp_mul_condExp_of_le (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀)
    (hf : MemLp f 2 μ) :
    ∫ ω, μ[f | m₁] ω * μ[f | m₂] ω ∂μ = ∫ ω, μ[f | m₁] ω ^ 2 ∂μ := by
  have h1 : MemLp (μ[f | m₁]) 2 μ := hf.condExp (by norm_num)
  have h2 : MemLp (μ[f | m₂]) 2 μ := hf.condExp (by norm_num)
  have h3 : ∀ᵐ ω ∂μ, μ[μ[f | m₂] | m₁] ω = μ[f | m₁] ω := condExp_condExp_of_le hm₁₂ hm₂
  calc ∫ ω, μ[f | m₁] ω * μ[f | m₂] ω ∂μ
      = ∫ ω, μ[f | m₁] ω * μ[μ[f | m₂] | m₁] ω ∂μ :=
        (integral_mul_condExp_of_stronglyMeasurable (hm₁₂.trans hm₂)
          stronglyMeasurable_condExp (h1.integrable_mul h2) (h2.integrable (by norm_num))).symm
    _ = ∫ ω, μ[f | m₁] ω ^ 2 ∂μ := by
        refine integral_congr_ae (h3.mono fun ω hω => ?_)
        simp only [hω, sq]

/-- **Pythagoras for nested conditional expectations:** for `m₁ ≤ m₂ ≤ m₀` and `f ∈ L²`,
`∫ (μ[f | m₂] - μ[f | m₁])² = ∫ (μ[f | m₂])² - ∫ (μ[f | m₁])²`. -/
theorem integral_sq_condExp_sub_condExp_of_le (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀)
    (hf : MemLp f 2 μ) :
    ∫ ω, (μ[f | m₂] ω - μ[f | m₁] ω) ^ 2 ∂μ =
      ∫ ω, μ[f | m₂] ω ^ 2 ∂μ - ∫ ω, μ[f | m₁] ω ^ 2 ∂μ := by
  have h1 : MemLp (μ[f | m₁]) 2 μ := hf.condExp (by norm_num)
  have h2 : MemLp (μ[f | m₂]) 2 μ := hf.condExp (by norm_num)
  have e : ∀ ω, (μ[f | m₂] ω - μ[f | m₁] ω) ^ 2 =
      μ[f | m₂] ω ^ 2 - 2 * (μ[f | m₁] ω * μ[f | m₂] ω) + μ[f | m₁] ω ^ 2 := fun ω => by ring
  have i2 : Integrable (fun ω => μ[f | m₂] ω ^ 2) μ := h2.integrable_sq
  have i1 : Integrable (fun ω => μ[f | m₁] ω ^ 2) μ := h1.integrable_sq
  have i12 : Integrable (fun ω => 2 * (μ[f | m₁] ω * μ[f | m₂] ω)) μ :=
    (h1.integrable_mul h2).const_mul 2
  have i3 : Integrable
      (fun ω => μ[f | m₂] ω ^ 2 - 2 * (μ[f | m₁] ω * μ[f | m₂] ω)) μ := i2.sub i12
  simp_rw [e]
  rw [integral_add i3 i1, integral_sub i2 i12, integral_const_mul,
    integral_condExp_mul_condExp_of_le hm₁₂ hm₂ hf]
  ring

/-- **Monotonicity of the `L²` norm of conditional expectations** in the σ-algebra. -/
theorem integral_sq_condExp_le_of_le (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀) (hf : MemLp f 2 μ) :
    ∫ ω, μ[f | m₁] ω ^ 2 ∂μ ≤ ∫ ω, μ[f | m₂] ω ^ 2 ∂μ := by
  have := integral_sq_condExp_sub_condExp_of_le hm₁₂ hm₂ hf
  have h0 : 0 ≤ ∫ ω, (μ[f | m₂] ω - μ[f | m₁] ω) ^ 2 ∂μ :=
    integral_nonneg fun ω => sq_nonneg _
  linarith

/-- **`L²` projection equality (Panchenko, proofs of Lemmas 1.5 and 1.6):** if `m₁ ≤ m₂ ≤ m₀`,
`f ∈ L²` and `μ[f | m₁]`, `μ[f | m₂]` have the same `L²` norm, they agree almost everywhere. -/
theorem condExp_ae_eq_of_integral_sq_condExp_eq (hm₁₂ : m₁ ≤ m₂) (hm₂ : m₂ ≤ m₀)
    (hf : MemLp f 2 μ)
    (hnorm : ∫ ω, μ[f | m₁] ω ^ 2 ∂μ = ∫ ω, μ[f | m₂] ω ^ 2 ∂μ) :
    μ[f | m₁] =ᵐ[μ] μ[f | m₂] := by
  have h1 : MemLp (μ[f | m₁]) 2 μ := hf.condExp (by norm_num)
  have h2 : MemLp (μ[f | m₂]) 2 μ := hf.condExp (by norm_num)
  have h0 : ∫ ω, (μ[f | m₂] ω - μ[f | m₁] ω) ^ 2 ∂μ = 0 := by
    rw [integral_sq_condExp_sub_condExp_of_le hm₁₂ hm₂ hf, hnorm, sub_self]
  have hint : Integrable (fun ω => (μ[f | m₂] ω - μ[f | m₁] ω) ^ 2) μ :=
    (h2.sub h1).integrable_sq
  have := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hint).1 h0
  filter_upwards [this] with ω hω
  have : μ[f | m₂] ω - μ[f | m₁] ω = 0 := by simpa using hω
  linarith

/-- **Sandwich:** if `m₁ ≤ m₂ ≤ m₃ ≤ m₀` and `μ[f | m₁]` and `μ[f | m₃]` agree almost everywhere
then so do `μ[f | m₂]` and `μ[f | m₃]`: the common value is `m₁`-measurable, hence `m₂`-measurable,
and is therefore unchanged by projecting onto `m₂`. -/
theorem condExp_ae_eq_of_le_of_le {m₃ : MeasurableSpace Ω} (hm₁₂ : m₁ ≤ m₂) (hm₂₃ : m₂ ≤ m₃)
    (hm₃ : m₃ ≤ m₀) (h : μ[f | m₁] =ᵐ[μ] μ[f | m₃]) : μ[f | m₂] =ᵐ[μ] μ[f | m₃] :=
  calc μ[f | m₂] =ᵐ[μ] μ[μ[f | m₃] | m₂] := (condExp_condExp_of_le hm₂₃ hm₃).symm
    _ =ᵐ[μ] μ[μ[f | m₁] | m₂] := condExp_congr_ae h.symm
    _ = μ[f | m₁] := condExp_of_stronglyMeasurable (hm₂₃.trans hm₃)
        (stronglyMeasurable_condExp.mono hm₁₂) integrable_condExp
    _ =ᵐ[μ] μ[f | m₃] := h

/-- **Convergence of `L²` norms along an increasing sequence of σ-algebras** (Lévy's upward
theorem plus bounded convergence): if `f` is bounded then
`∫ (μ[f | 𝒢 n])² → ∫ (μ[f | ⨆ n, 𝒢 n])²`. -/
theorem tendsto_integral_sq_condExp (𝒢 : ℕ → MeasurableSpace Ω) (hmono : Monotone 𝒢)
    (h𝒢 : ∀ n, 𝒢 n ≤ m₀) {C : ℝ} (hf : ∀ ω, |f ω| ≤ C) :
    Tendsto (fun n => ∫ ω, μ[f | 𝒢 n] ω ^ 2 ∂μ) atTop
      (𝓝 (∫ ω, μ[f | ⨆ n, 𝒢 n] ω ^ 2 ∂μ)) := by
  let ℱ : Filtration ℕ m₀ := ⟨𝒢, hmono, h𝒢⟩
  refine tendsto_integral_of_dominated_convergence (fun _ => C ^ 2) (fun n => ?_)
    (integrable_const _) (fun n => ?_) ?_
  · exact ((stronglyMeasurable_condExp (m := 𝒢 n)).mono (h𝒢 n)).aestronglyMeasurable.pow 2
  · filter_upwards [ae_bdd_abs_condExp_of_ae_bdd_abs (μ := μ) (m := 𝒢 n) (R := C)
      (Filter.Eventually.of_forall hf)] with ω hω
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hω 2
  · filter_upwards [tendsto_ae_condExp (μ := μ) (ℱ := ℱ) f] with ω hω
    exact hω.pow 2

end MeasureTheory
