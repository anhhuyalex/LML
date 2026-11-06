/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenTheorem

/-!
# Hanen's theorem as a limit, and the moments of the limit law (Talagrand, Eq. (1.329)-(1.330))

`sk_hanen_theorem` gives the moments of `√N(⟨σ₁σ₂⟩ - ⟨σ₁⟩⟨σ₂⟩)` with an explicit error. Here
they are stated as limits, and the right-hand side is identified with the moments of the law
`β g ch⁻²Y₁ ch⁻²Y₂ / √(1 - β²α)` of Eq. (1.330) for independent standard Gaussians `g, z₁, z₂`.
Convergence in law is not claimed.

## Main declarations

* `SpinGlasses.sk_hanen_limit`: the limit form of Eq. (1.329).
* `SpinGlasses.hanen_law_moment`: the moments of the displayed law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators Real

namespace SpinGlasses

/-- **Talagrand's Theorem 1.11.1 as a limit (Eq. (1.329)).** For `4 β² < 1`, a root `q` of
`q = 𝔼 th²(β√q z + h)`, any `k`, and the sites `0, 1` of the system with `n + 2` spins,
`(√(n+2))^k 𝔼(⟨σ₀σ₁⟩ - ⟨σ₀⟩⟨σ₁⟩)^k` tends to `a_k (β²/(1 - β²α))^{k/2} (𝔼 ch^{-2k} Y)²`,
where `α = 1 - 2q + 𝔼 th⁴`. For odd `k` both sides vanish: `a_k = 0`. -/
theorem sk_hanen_limit (β h q : ℝ) (hβ : 4 * β ^ 2 < 1)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) (k : ℕ) :
    let α : ℝ := (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂gaussianReal 0 1) - 2 * q + 1
    let a_k : ℝ := ∫ x : ℝ, x ^ k ∂gaussianReal 0 1
    Tendsto (fun n : ℕ =>
      (Real.sqrt ((n : ℝ) + 2)) ^ k *
      ∫ g : FinPairs (n + 1 + 1) → ℝ,
        (∫ σ : Fin (n + 1 + 1) → ℤˣ, (σ 0 : ℝ) * (σ 1 : ℝ)
            ∂(Measure.count.tilted fun σ : Fin (n + 1 + 1) → ℤˣ =>
              (Real.sqrt ((n : ℝ) + 2))⁻¹ * β *
                (∑ p : FinPairs (n + 1 + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
                h * ∑ i : Fin (n + 1 + 1), (σ i : ℝ)) -
          (∫ σ : Fin (n + 1 + 1) → ℤˣ, (σ 0 : ℝ)
              ∂(Measure.count.tilted fun σ : Fin (n + 1 + 1) → ℤˣ =>
                (Real.sqrt ((n : ℝ) + 2))⁻¹ * β *
                  (∑ p : FinPairs (n + 1 + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
                  h * ∑ i : Fin (n + 1 + 1), (σ i : ℝ))) *
          (∫ σ : Fin (n + 1 + 1) → ℤˣ, (σ 1 : ℝ)
              ∂(Measure.count.tilted fun σ : Fin (n + 1 + 1) → ℤˣ =>
                (Real.sqrt ((n : ℝ) + 2))⁻¹ * β *
                  (∑ p : FinPairs (n + 1 + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
                  h * ∑ i : Fin (n + 1 + 1), (σ i : ℝ)))) ^ k
        ∂(Measure.pi fun _ : FinPairs (n + 1 + 1) => gaussianReal 0 1))
      atTop
      (𝓝 (a_k * (Real.sqrt (β ^ 2 / (1 - β ^ 2 * α))) ^ k *
        (∫ z : ℝ, (Real.cosh (β * z * Real.sqrt q + h) ^ (2 * k))⁻¹ ∂gaussianReal 0 1) ^ 2)) := by
  intro α a_k
  have hβ₀ : 4 * |β| ^ 2 < 1 := by rwa [sq_abs]
  obtain ⟨K, hKpos, hK⟩ := sk_hanen_theorem |β| hβ₀ k
  have hβ' : β ^ 2 ≤ |β| ^ 2 := (sq_abs β).ge
  have hα01 : α ∈ Set.Icc (0 : ℝ) 1 := by
    have := tanh_fourth_sub_two_add_one_mem_Icc (β * Real.sqrt q) h
    rwa [hfix] at this
  have hden : 0 < 1 - β ^ 2 * α := by
    have h2 : β ^ 2 * α ≤ β ^ 2 * 1 := mul_le_mul_of_nonneg_left hα01.2 (sq_nonneg _)
    linarith only [h2, hβ]
  set T : ℝ := ∫ z : ℝ, (Real.cosh (β * z * Real.sqrt q + h) ^ (2 * k))⁻¹ ∂gaussianReal 0 1
    with hT
  -- the main term, rescaled
  have hmain (M : ℝ) (hM : 0 < M) :
      (Real.sqrt M) ^ k * (a_k * (β ^ 2 / (M * (1 - β ^ 2 * α))) ^ (k / 2) * T ^ 2)
      = a_k * (Real.sqrt (β ^ 2 / (1 - β ^ 2 * α))) ^ k * T ^ 2 := by
    rcases Nat.even_or_odd k with ⟨p, hp⟩ | ⟨m, hm⟩
    · have hk2 : k / 2 = p := by omega
      have h1 : (Real.sqrt M) ^ k = M ^ p := by
        rw [hp, ← two_mul, pow_mul, Real.sq_sqrt hM.le]
      have h2 : (Real.sqrt (β ^ 2 / (1 - β ^ 2 * α))) ^ k = (β ^ 2 / (1 - β ^ 2 * α)) ^ p := by
        rw [hp, ← two_mul, pow_mul, Real.sq_sqrt (div_nonneg (sq_nonneg _) hden.le)]
      rw [hk2, h1, h2]
      have h3 : M ^ p * (β ^ 2 / (M * (1 - β ^ 2 * α))) ^ p = (β ^ 2 / (1 - β ^ 2 * α)) ^ p := by
        rw [← mul_pow]
        congr 1
        field_simp
      calc M ^ p * (a_k * (β ^ 2 / (M * (1 - β ^ 2 * α))) ^ p * T ^ 2)
          = a_k * (M ^ p * (β ^ 2 / (M * (1 - β ^ 2 * α))) ^ p) * T ^ 2 := by ring
        _ = _ := by rw [h3]
    · have ha : a_k = 0 := by
        simp only [a_k]
        rw [hm]
        exact gaussian_moment_odd m
      simp [ha]
  have hsqrt (M : ℝ) (hM : 0 < M) :
      (Real.sqrt M) ^ k * (K / M ^ (((k + 1 : ℕ) : ℝ) / 2)) = K / Real.sqrt M := by
    have h1 : M ^ (((k + 1 : ℕ) : ℝ) / 2) = (Real.sqrt M) ^ (k + 1) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hM.le]
      congr 1
      ring
    have hs : 0 < Real.sqrt M := Real.sqrt_pos.2 hM
    rw [h1, pow_succ]
    field_simp
  have hcast (n : ℕ) : (((n + 1 : ℕ) : ℝ) + 1) = (n : ℝ) + 2 := by push_cast; ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun n : ℕ => K / Real.sqrt ((n : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop))
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
  have hM : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hne : (0 : Fin (n + 1 + 1)) ≠ 1 := by simp
  have hb := hK β h q hfix hβ' (n + 1) 0 1 hne
  simp only [hcast] at hb
  rw [← hmain ((n : ℝ) + 2) hM, ← mul_sub, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) k), ← hsqrt ((n : ℝ) + 2) hM]
  exact mul_le_mul_of_nonneg_left hb (pow_nonneg (Real.sqrt_nonneg _) k)

/-- **The moments of the law (1.330).** For independent standard Gaussians `g, z₁, z₂` and
`Yᵢ = β zᵢ √q + h`, the `k`-th moment of `c g ch⁻²Y₁ ch⁻²Y₂` is
`a_k c^k (𝔼 ch^{-2k} Y)²`, where `a_k = 𝔼 g^k`. The constant `c` is arbitrary here; the law of
Eq. (1.330) has `c = β/√(1 - β²α)`, and `sk_hanen_limit` gives the matching limit of the moments
of the overlap fluctuation. -/
theorem hanen_law_moment (β h q c : ℝ) (k : ℕ) :
    ∫ w : ℝ × ℝ × ℝ,
      (c * w.1 * ((Real.cosh (β * w.2.1 * Real.sqrt q + h) ^ 2)⁻¹) *
        ((Real.cosh (β * w.2.2 * Real.sqrt q + h) ^ 2)⁻¹)) ^ k
      ∂((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1))) =
    (∫ x : ℝ, x ^ k ∂gaussianReal 0 1) * c ^ k *
      (∫ z : ℝ, (Real.cosh (β * z * Real.sqrt q + h) ^ (2 * k))⁻¹ ∂gaussianReal 0 1) ^ 2 := by
  let F : ℝ → ℝ := fun z => (Real.cosh (β * z * Real.sqrt q + h) ^ (2 * k))⁻¹
  have hint (w : ℝ × ℝ × ℝ) :
      (c * w.1 * ((Real.cosh (β * w.2.1 * Real.sqrt q + h) ^ 2)⁻¹) *
        ((Real.cosh (β * w.2.2 * Real.sqrt q + h) ^ 2)⁻¹)) ^ k =
      c ^ k * (w.1 ^ k * (F w.2.1 * F w.2.2)) := by
    simp only [F, mul_pow, inv_pow, ← pow_mul]
    ring
  simp_rw [hint]
  rw [integral_const_mul, integral_prod_mul (fun x : ℝ => x ^ k)
    (fun y : ℝ × ℝ => F y.1 * F y.2), integral_prod_mul F F]
  ring

end SpinGlasses
