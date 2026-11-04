/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapConcentration
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.AddPowEstimates

/-!
# Overlap moments along the whole smart path (Talagrand, Eqs. (1.103) and (1.88))

The proof of Theorem 1.4.11 needs the *fourth* moment of `R_{1,2} - q` along the smart path,
`ν_t ((R_{1,2} - q)^4) ≤ K / N²` uniformly in `t`.  The exponential bound
`ν_t (exp (N a_t (R_{1,2} - q)²)) ≤ (1/2 - 2β²)^{-1/2}` with
`a_t = 1/4 + β² - 2β² cos² t ≥ 1/4 - β²` holds along the whole path
(`sk_compensated_path_le_decoupled` and the decoupled base case), and `y^r ≤ r! exp y` turns it
into every even moment.

## Main declarations

* `SpinGlasses.sk_path_expected_exp_overlap_le`: the exponential bound along the path.
* `SpinGlasses.sk_path_expected_pow_overlap_le`: `ν_t ((R_{1,2} - q)^{2r}) ≤ K_r / N^r` for all
  `t ∈ [0, π/2]`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Eqs. (1.88), (1.103).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **The exponential overlap bound along the whole smart path (Talagrand, Eq. (1.103))** for
`β² < 1/4`: with `a_t = 1/4 + β² - 2 β² cos² t`,
`𝔼⟨exp (a_t N (R₁,₂ - q)²)⟩_t ≤ (1/2 - 2 β²)^{-1/2}`. -/
theorem sk_path_expected_exp_overlap_le {N : ℕ} (hN : 0 < N) (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : β ^ 2 < 1 / 4) {t : ℝ} (ht : t ∈ Set.Icc 0 (Real.pi / 2)) :
    ∫ ω : (FinPairs N → ℝ) × (Fin N → ℝ), ∫ σ : Fin 2 → (Fin N → ℤˣ),
        Real.exp ((N * (1 / 4 + β ^ 2 - 2 * β ^ 2 * Real.cos t ^ 2)) * (((N : ℝ)⁻¹ *
          ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
            Real.cos t * ((Real.sqrt N)⁻¹ * β *
              ∑ p : FinPairs N, ω.1 p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
            Real.sin t * (β * Real.sqrt q * ∑ i, ω.2 i * ((a i : ℤ) : ℝ)) +
            h * ∑ i, ((a i : ℤ) : ℝ))
        ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)) ≤
      (Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ := by
  have hq : 0 ≤ q := hfix ▸ integral_nonneg fun x => sq_nonneg _
  have hcomp := sk_compensated_path_le_decoupled hN β h q (1 / 4 + β ^ 2) hq
    (by nlinarith [sq_nonneg β]) ht
  have hbase := integral_decoupled_exp_overlap_sq_le hN β h q (1 / 4 + β ^ 2) hfix
    (by positivity) (by linarith)
  have hC : 1 - 2 * (1 / 4 + β ^ 2) = 1 / 2 - 2 * β ^ 2 := by ring
  rw [hC] at hbase
  exact hcomp.trans hbase

/-- **Even overlap moments along the whole smart path (Talagrand, Eq. (1.88) along the path).**
For `β² < 1/4`, a fixed point `q`, every `r` and every `t ∈ [0, π/2]`,
`𝔼⟨(R₁,₂ - q)^{2r}⟩_t ≤ r! (1/2 - 2β²)^{-1/2} / ((1/4 - β²)^r N^r)`. -/
theorem sk_path_expected_pow_overlap_le {N : ℕ} (hN : 0 < N) (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : β ^ 2 < 1 / 4) (r : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 (Real.pi / 2)) :
    ∫ ω : (FinPairs N → ℝ) × (Fin N → ℝ), ∫ σ : Fin 2 → (Fin N → ℤˣ),
        (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ (2 * r)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a =>
            Real.cos t * ((Real.sqrt N)⁻¹ * β *
              ∑ p : FinPairs N, ω.1 p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
            Real.sin t * (β * Real.sqrt q * ∑ i, ω.2 i * ((a i : ℤ) : ℝ)) +
            h * ∑ i, ((a i : ℤ) : ℝ))
        ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)) ≤
      (Nat.factorial r : ℝ) * (Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ /
        ((1 / 4 - β ^ 2) ^ r * (N : ℝ) ^ r) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hNpos : (0 : ℝ) < N := by positivity
  have hs0 : 0 < 1 / 4 - β ^ 2 := by linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / 4 + β ^ 2 - 2 * β ^ 2 * Real.cos t ^ 2 := ⟨_, rfl⟩
  have ha0 : 1 / 4 - β ^ 2 ≤ a := by
    have := Real.cos_sq_le_one t
    rw [ha]
    nlinarith [sq_nonneg β]
  have hexp := sk_path_expected_exp_overlap_le hN β h q hfix hβ ht
  rw [← ha] at hexp
  obtain ⟨Pg, hPg⟩ : ∃ Pg : Measure (FinPairs N → ℝ),
      Pg = Measure.pi fun _ : FinPairs N => gaussianReal 0 1 := ⟨_, rfl⟩
  obtain ⟨Pz, hPz⟩ : ∃ Pz : Measure (Fin N → ℝ),
      Pz = Measure.pi fun _ : Fin N => gaussianReal 0 1 := ⟨_, rfl⟩
  have : IsProbabilityMeasure Pg := by rw [hPg]; infer_instance
  have : IsProbabilityMeasure Pz := by rw [hPz]; infer_instance
  rw [← hPg, ← hPz] at hexp ⊢
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
      ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ (2 * r))
  obtain ⟨X, hX⟩ : ∃ X : (Fin 2 → (Fin N → ℤˣ)) → ℝ, ∀ σ, X σ = (((N : ℝ)⁻¹ *
      ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) - q) ^ 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨μt, hμt⟩ : ∃ μt : (FinPairs N → ℝ) × (Fin N → ℝ) → Measure (Fin 2 → (Fin N → ℤˣ)),
      ∀ ω, μt ω = Measure.pi fun _ : Fin 2 => Measure.count.tilted fun b => gf b ω :=
    ⟨_, fun _ => rfl⟩
  simp only [← hgf] at hexp hJe hJx ⊢
  have hXr : ∀ σ, (((N : ℝ)⁻¹ * ((fun i => ((σ 0 i : ℤ) : ℝ)) ⬝ᵥ fun i => ((σ 1 i : ℤ) : ℝ))) -
      q) ^ (2 * r) = X σ ^ r := fun σ => by rw [hX, ← pow_mul]
  simp only [hXr, ← hX, ← hμt] at hexp hJe hJx ⊢
  set C : ℝ := (Nat.factorial r : ℝ) / ((1 / 4 - β ^ 2) * N) ^ r with hC
  have hC0 : 0 ≤ C := by positivity
  have hpt : ∀ σ, X σ ^ r ≤ C * Real.exp ((N * a) * X σ) := fun σ => by
    have hX0 : 0 ≤ X σ := by rw [hX]; exact sq_nonneg _
    have h1 := Real.pow_le_factorial_mul_exp (mul_nonneg (mul_nonneg hNpos.le (hs0.le.trans ha0))
      hX0) r
    have h2 : (N * a * X σ) ^ r = (N * a) ^ r * X σ ^ r := by rw [mul_pow]
    have hpos : 0 < ((1 / 4 - β ^ 2) * N) ^ r := by positivity
    have h3 : ((1 / 4 - β ^ 2) * N) ^ r ≤ (N * a) ^ r :=
      pow_le_pow_left₀ (by positivity) (by nlinarith) r
    rw [h2] at h1
    have h4 : ((1 / 4 - β ^ 2) * N) ^ r * X σ ^ r ≤
        (Nat.factorial r : ℝ) * Real.exp (N * a * X σ) :=
      (mul_le_mul_of_nonneg_right h3 (pow_nonneg hX0 r)).trans h1
    rw [hC, div_mul_eq_mul_div, le_div_iff₀ hpos]
    calc X σ ^ r * ((1 / 4 - β ^ 2) * N) ^ r = ((1 / 4 - β ^ 2) * N) ^ r * X σ ^ r := by ring
      _ ≤ _ := h4
      _ = _ := by ring
  have hprob : ∀ ω, IsProbabilityMeasure (μt ω) := fun ω => by rw [hμt]; infer_instance
  have hin : ∀ ω, ∫ σ, X σ ^ r ∂μt ω ≤ C * ∫ σ, Real.exp ((N * a) * X σ) ∂μt ω := fun ω => by
    rw [← integral_const_mul]
    exact integral_mono Integrable.of_finite (Integrable.of_finite.const_mul _) hpt
  calc _ ≤ ∫ ω, C * ∫ σ, Real.exp ((N * a) * X σ) ∂μt ω ∂(Pg.prod Pz) :=
        integral_mono hJx (hJe.const_mul _) hin
    _ = C * ∫ ω, ∫ σ, Real.exp ((N * a) * X σ) ∂μt ω ∂(Pg.prod Pz) := integral_const_mul _ _
    _ ≤ C * (Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ := mul_le_mul_of_nonneg_left hexp hC0
    _ = _ := by
        rw [hC, mul_pow]
        field_simp

end SpinGlasses
