/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKLatalaBase
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ExpMoment
public import LeanMachineLearning.SpinGlasses.SKLatalaCompensated

/-!
# Exponential concentration of the overlap (Talagrand, Theorem 1.4.1)

For `β < 1/2` the overlap `R₁,₂` of two replicas concentrates around the fixed point `q` of the
self-consistency equation `q = 𝔼 tanh² (β √q z + h)` at the sub-Gaussian scale `N^{-1/2}`.
The proof combines the compensated monotonicity along the smart path
(`sk_compensated_path_le_decoupled`) with the base case at the decoupled endpoint
(`integral_decoupled_exp_overlap_sq_le`).

## Main declarations

* `SpinGlasses.sk_overlap_concentration_exp`: `𝔼⟨exp (s N (R₁,₂ - q)²)⟩ ≤ (1 - 2 s - 4 β²)^{-1/2}`
  for the SK model (Theorem 1.4.1).
* `SpinGlasses.sk_path_expected_sq_overlap_le`: `𝔼⟨(R₁,₂ - q)²⟩_t ≤ K / N` uniformly along the
  smart path (Eqs. (1.89) and (1.103)).

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Theorem 1.4.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Exponential overlap concentration (Talagrand, Theorem 1.4.1).**  At the fixed point
`q = 𝔼 tanh² (β √q z + h)`, for `s ≥ 0` and `2 s + 4 β² < 1`, the SK model satisfies
`𝔼⟨exp (s N (R₁,₂ - q)²)⟩ ≤ (1 - 2 s - 4 β²)^{-1/2}`. -/
theorem sk_overlap_concentration_exp {N : ℕ} (hN : 0 < N) (β h q s : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hs : 0 ≤ s) (hβ : 2 * s + 4 * β ^ 2 < 1) :
    ∫ g : FinPairs N → ℝ, ∫ σ : Fin 2 → (Fin N → ℤˣ),
        Real.exp ((N * s) * (((N : ℝ)⁻¹ *
          ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
            (Real.sqrt N)⁻¹ * β *
              (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
              h * ∑ i, ((a i : ℤ) : ℝ))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
      (Real.sqrt (1 - 2 * s - 4 * β ^ 2))⁻¹ := by
  have hq : 0 ≤ q := hfix ▸ integral_nonneg fun x => sq_nonneg _
  refine (sk_compensated_le_decoupled hN β h q s hq hs).trans ?_
  have := integral_decoupled_exp_overlap_sq_le hN β h q (s + 2 * β ^ 2) hfix
    (by positivity) (by linarith)
  convert this using 3
  ring

/-- **Uniform second-moment bound along the smart path (Eqs. (1.89) and (1.103)).**  For
`β² < 1/4` and every `t ∈ [0, π/2]`, the expected squared overlap of two replicas under the
smart-path energy at time `t` is at most `K / N`, with
`K = ((1/2 - 2 β²)^{-1/2} - 1) / (1/4 - β²)`. -/
theorem sk_path_expected_sq_overlap_le {N : ℕ} (hN : 0 < N) (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : β ^ 2 < 1 / 4) {t : ℝ} (ht : t ∈ Set.Icc 0 (Real.pi / 2)) :
    ∫ ω : (FinPairs N → ℝ) × (Fin N → ℝ), ∫ σ : Fin 2 → (Fin N → ℤˣ),
        (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
            Real.cos t * ((Real.sqrt N)⁻¹ * β *
              ∑ p : FinPairs N, ω.1 p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
            Real.sin t * (β * Real.sqrt q * ∑ i, ω.2 i * ((a i : ℤ) : ℝ)) +
            h * ∑ i, ((a i : ℤ) : ℝ))
        ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)) ≤
      ((Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ - 1) / ((1 / 4 - β ^ 2) * N) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hq : 0 ≤ q := hfix ▸ integral_nonneg fun x => sq_nonneg _
  have hNpos : (0 : ℝ) < N := by positivity
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = 1 / 4 + β ^ 2 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = lam - 2 * β ^ 2 * Real.cos t ^ 2 := ⟨_, rfl⟩
  have hs0 : 0 < 1 / 4 - β ^ 2 := by linarith
  have ha0 : 1 / 4 - β ^ 2 ≤ a := by
    have := Real.cos_sq_le_one t
    rw [ha, hlam]
    nlinarith [sq_nonneg β]
  have hcomp := sk_compensated_path_le_decoupled hN β h q lam hq (by rw [hlam]; nlinarith) ht
  rw [← ha] at hcomp
  have hbase := integral_decoupled_exp_overlap_sq_le hN β h q lam hfix (by rw [hlam]; positivity)
    (by rw [hlam]; linarith)
  have hC : 1 - 2 * lam = 1 / 2 - 2 * β ^ 2 := by rw [hlam]; ring
  rw [hC] at hbase
  obtain ⟨Pg, hPg⟩ : ∃ Pg : Measure (FinPairs N → ℝ),
      Pg = Measure.pi fun _ : FinPairs N => gaussianReal 0 1 := ⟨_, rfl⟩
  obtain ⟨Pz, hPz⟩ : ∃ Pz : Measure (Fin N → ℝ),
      Pz = Measure.pi fun _ : Fin N => gaussianReal 0 1 := ⟨_, rfl⟩
  have : IsProbabilityMeasure Pg := by rw [hPg]; infer_instance
  have : IsProbabilityMeasure Pz := by rw [hPz]; infer_instance
  rw [← hPg, ← hPz] at hcomp ⊢
  obtain ⟨gf, hgf⟩ : ∃ gf : (Fin N → ℤˣ) → (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ, ∀ b ω,
      gf b ω = Real.cos t * ((Real.sqrt N)⁻¹ * β *
          ∑ p : FinPairs N, ω.1 p * ((b p.val.1 : ℤ) : ℝ) * ((b p.val.2 : ℤ) : ℝ)) +
        Real.sin t * (β * Real.sqrt q * ∑ i, ω.2 i * ((b i : ℤ) : ℝ)) +
        h * ∑ i, ((b i : ℤ) : ℝ) := ⟨_, fun _ _ => rfl⟩
  have hmeas : ∀ b : Fin N → ℤˣ, Measurable (gf b) := fun b => by
    rw [show gf b = _ from funext (hgf b)]
    fun_prop
  have hJe := integrable_integral_pi_count_tilted_det (R := Fin 2) (P := Pg.prod Pz)
    (g := gf) (fun b => (hmeas b).aemeasurable)
    (fun σ : Fin 2 → (Fin N → ℤˣ) => Real.exp ((N * a) * (((N : ℝ)⁻¹ *
      ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2))
  have hJx := integrable_integral_pi_count_tilted_det (R := Fin 2) (P := Pg.prod Pz)
    (g := gf) (fun b => (hmeas b).aemeasurable)
    (fun σ : Fin 2 → (Fin N → ℤˣ) => (((N : ℝ)⁻¹ *
      ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2)
  obtain ⟨X, hX⟩ : ∃ X : (Fin 2 → (Fin N → ℤˣ)) → ℝ, ∀ σ, X σ = (((N : ℝ)⁻¹ *
      ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨μt, hμt⟩ : ∃ μt : (FinPairs N → ℝ) × (Fin N → ℝ) → Measure (Fin 2 → (Fin N → ℤˣ)),
      ∀ ω, μt ω = Measure.pi fun _ : Fin 2 => Measure.count.tilted fun b => gf b ω :=
    ⟨_, fun _ => rfl⟩
  simp only [← hgf] at hcomp ⊢
  simp only [← hX, ← hμt] at hJe hJx hcomp ⊢
  simp only [← hX] at hbase
  rw [← hPz] at hbase
  have hprob : ∀ ω, IsProbabilityMeasure (μt ω) := fun ω => by rw [hμt]; infer_instance
  have hpt : ∀ ω, 1 + (N * a) * ∫ σ, X σ ∂μt ω ≤ ∫ σ, Real.exp ((N * a) * X σ) ∂μt ω :=
    fun ω => one_add_mul_integral_le_integral_exp (μ := μt ω) (N * a) Integrable.of_finite
      Integrable.of_finite
  have hint := one_add_mul_integral_le_integral (N * a) hJx hJe hpt
  have hnn : 0 ≤ ∫ ω, ∫ σ, X σ ∂μt ω ∂(Pg.prod Pz) :=
    integral_nonneg fun ω => integral_nonneg fun σ => by rw [hX]; exact sq_nonneg _
  have hle : 1 + (N * a) * ∫ ω, ∫ σ, X σ ∂μt ω ∂(Pg.prod Pz) ≤ (Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ :=
    hint.trans (hcomp.trans hbase)
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right ha0 (mul_nonneg hNpos.le hnn)]
end SpinGlasses
