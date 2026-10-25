/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GibbsGramMoments
public import LeanMachineLearning.SpinGlasses.SKOverlapConcentration
public import LeanMachineLearning.SpinGlasses.SKFixedPoint

/-!
# The general Gaussian fluctuation principle for the SK model (Talagrand, Theorem 1.7.11)

For `4 β² < 1`, `q = 𝔼 tanh²(β √q z + h)`, an exponentially tame `U` and `k ≥ 1`,
`𝔼 (⟨U(N^{-1/2} ∑ y_i (σ_i - ⟨σ_i⟩))⟩ - 𝔼_ξ U(ξ √(1-q)))^{2k} ≤ K / N^k`
(`SpinGlasses.sk_general_gaussian_fluctuation`).  The proof combines the Taylor step
`ExpTame.gibbs_fluctuation_abs_le` (a bound by the Gibbs average of products of Gram entries),
the arithmetic-geometric mean inequality, the moment bound `integral_projGram_pow_le` for the Gram
entries, and the moment bound `sk_overlap_moment_le_of_exp` for the overlap.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Theorem 1.7.11.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace SpinGlasses

/-! ### Products of Gram entries -/

theorem prod_abs_le_sum_pow {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) :
    ∏ j, |a j| ≤ ∑ j, |a j| ^ n := by
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) (fun j => |a j|)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  calc ∏ j, |a j| ≤ ∏ _j : Fin n, |a j₀| :=
        Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ => hj₀ j (Finset.mem_univ j)
    _ = |a j₀| ^ n := by simp
    _ ≤ ∑ j, |a j| ^ n :=
        Finset.single_le_sum (f := fun j => |a j| ^ n) (fun j _ => by positivity)
          (Finset.mem_univ j₀)

section Ising

attribute [local instance] Fintype.ofFinite

variable {α : Type*} [Finite α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
  {N : ℕ} (ξ : Fin N → α → ℝ) (hξ2 : ∀ i a, ξ i a ^ 2 = 1)

include hξ2 in
/-- The Gibbs average of the products of `2k` Gram entries is bounded by the overlap moment. -/
theorem sum_integral_abs_pairProd_le (hN : 0 < N) (f : α → ℝ) (q v : ℝ) (hv : v ^ 2 = 1 - q)
    {k : ℕ} (hk : 1 ≤ k) :
    ∑ p : Fin (2 * k) → Fin (2 * k) × Fin (2 * k), ∫ σ : Fin (2 * k) → α,
        |pairProd (projGram (centeredData ξ f σ) v) p|
          ∂(Measure.pi fun _ : Fin (2 * k) => Measure.count.tilted f) ≤
      ((2 * k) * (2 * k) : ℝ) ^ (2 * k) *
        ((2 * k : ℝ) * (4 ^ (2 * k) * overlapMoment ξ f q k)) := by
  have hn : 0 < 2 * k := by omega
  have hone : ∀ p : Fin (2 * k) → Fin (2 * k) × Fin (2 * k),
      ∫ σ : Fin (2 * k) → α, |pairProd (projGram (centeredData ξ f σ) v) p|
          ∂(Measure.pi fun _ : Fin (2 * k) => Measure.count.tilted f) ≤
        (2 * k : ℝ) * (4 ^ (2 * k) * overlapMoment ξ f q k) := fun p => by
    calc ∫ σ : Fin (2 * k) → α, |pairProd (projGram (centeredData ξ f σ) v) p|
          ∂(Measure.pi fun _ : Fin (2 * k) => Measure.count.tilted f)
        ≤ ∫ σ : Fin (2 * k) → α, ∑ j : Fin (2 * k),
            (projGram (centeredData ξ f σ) v (p j).1 (p j).2) ^ (2 * k)
            ∂(Measure.pi fun _ : Fin (2 * k) => Measure.count.tilted f) := by
          refine integral_mono Integrable.of_finite Integrable.of_finite fun σ => ?_
          unfold pairProd
          rw [Finset.abs_prod]
          refine (prod_abs_le_sum_pow hn (fun j => projGram (centeredData ξ f σ) v (p j).1
            (p j).2)).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun j _ => Even.pow_abs ⟨k, by ring⟩ _
      _ = ∑ j : Fin (2 * k), ∫ σ : Fin (2 * k) → α,
            (projGram (centeredData ξ f σ) v (p j).1 (p j).2) ^ (2 * k)
            ∂(Measure.pi fun _ : Fin (2 * k) => Measure.count.tilted f) :=
          integral_finsetSum _ fun j _ => Integrable.of_finite
      _ ≤ ∑ _j : Fin (2 * k), 4 ^ (2 * k) * overlapMoment ξ f q k :=
          Finset.sum_le_sum fun j _ => integral_projGram_pow_le ξ hξ2 hN f q v hv hk _ _
      _ = _ := by simp
  calc _ ≤ ∑ _p : Fin (2 * k) → Fin (2 * k) × Fin (2 * k),
        (2 * k : ℝ) * (4 ^ (2 * k) * overlapMoment ξ f q k) :=
        Finset.sum_le_sum fun p _ => hone p
    _ = _ := by simp [Finset.sum_const, Fintype.card_prod]

end Ising

/-! ### The SK model -/

/-- The Gibbs energy of the SK model with the pair disorder `g`. -/
noncomputable def skGibbsEnergy (N : ℕ) (β h : ℝ) (g : FinPairs N → ℝ) (a : Fin N → ℤˣ) : ℝ :=
  (Real.sqrt N)⁻¹ * β * (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
    h * ∑ i, ((a i : ℤ) : ℝ)


/-- **The general Gaussian fluctuation principle (Talagrand, Theorem 1.7.11).**  Let
`4 β² < 1`, let `q = 𝔼 tanh²(β √q z + h)` and let `U` be exponentially tame.  Then for every `k ≥ 1`
there is `K` such that for every `N ≥ 1`
`𝔼 (⟨U(N^{-1/2} ∑ y_i σ̇_i)⟩ - 𝔼_ξ U(ξ √(1-q)))^{2k} ≤ K / N^k`, where `σ̇_i = σ_i - ⟨σ_i⟩`, `y` is
a standard Gaussian vector independent of the disorder `g`, and `𝔼` is over `g` and `y`. -/
theorem sk_general_gaussian_fluctuation (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : 4 * β ^ 2 < 1) {U : ℝ → ℝ} (hU : ExpTame U) {k : ℕ} (hk : 1 ≤ k) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 0 < N →
      ∫ g : FinPairs N → ℝ, ∫ y : Fin N → ℝ,
        ((∫ a, U ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) -
              ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y)
            ∂(Measure.count.tilted (skGibbsEnergy N β h g))) -
          ∫ t, U (Real.sqrt (1 - q) * t) ∂(gaussianReal 0 1)) ^ (2 * k)
          ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤ K / (N : ℝ) ^ k := by
  have hq := fixedPoint_mem_Icc hfix
  set v : ℝ := Real.sqrt (1 - q) with hvdef
  have hv : v ^ 2 = 1 - q := Real.sq_sqrt (by linarith [hq.2])
  set c₀ : ℝ := ∫ s, U (v * s) ∂(gaussianReal 0 1) with hc₀
  have hV : ExpTame (fun x => U x - c₀) := hU.sub_const c₀
  have hV0 : ∫ t, (fun x => U x - c₀) (v * t) ∂(gaussianReal 0 1) = 0 :=
    hU.integral_sub_const_mul_gaussianReal v
  obtain ⟨C, hC0, hCb⟩ := hV.gibbs_fluctuation_abs_le (m := 2 * k) (by omega) v
    (by nlinarith [hq.1, hq.2]) hV0
  obtain ⟨K', hK'0, hK'⟩ := sk_overlap_moment_le_of_exp β h q hfix hβ k
  set C₂ : ℝ := C * (((2 * k) * (2 * k) : ℝ) ^ (2 * k) * ((2 * k : ℝ) * 4 ^ (2 * k))) with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  refine ⟨C₂ * K' + 1, by positivity, fun N hN => ?_⟩
  have hNk : (0 : ℝ) < (N : ℝ) ^ k := by positivity
  set ξ : Fin N → (Fin N → ℤˣ) → ℝ := fun i a => ((a i : ℤ) : ℝ) with hξ
  have hξ_abs : ∀ i a, |ξ i a| ≤ 1 := fun i a => abs_units_cast_le_one (a i)
  have hξ_sq : ∀ i a, ξ i a ^ 2 = 1 := fun i a => units_cast_sq (a i)
  set P : Measure (FinPairs N → ℝ) := Measure.pi fun _ : FinPairs N => gaussianReal 0 1 with hP
  set J : (FinPairs N → ℝ) → ℝ := fun g =>
    overlapMoment ξ (skGibbsEnergy N β h g) q k with hJ
  have hJint : Integrable J P := by
    refine integrable_integral_pi_count_tilted_det (R := Fin 2)
      (g := fun a g => skGibbsEnergy N β h g a) (fun a => ?_)
      (fun τ => (overlapGibbs ξ (τ 0) (τ 1) - q) ^ (2 * k))
    unfold skGibbsEnergy
    exact (by fun_prop : Measurable _).aemeasurable
  have hJmom : ∫ g, J g ∂P ≤ K' / (N : ℝ) ^ k := hK' N hN
  -- pointwise bound
  have hpt : ∀ g : FinPairs N → ℝ, ∫ y : Fin N → ℝ,
      ((∫ a, U ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) -
            ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y)
          ∂(Measure.count.tilted (skGibbsEnergy N β h g))) - c₀) ^ (2 * k)
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) ≤ C₂ * J g := fun g => by
    set f := skGibbsEnergy N β h g with hf
    have hrew : ∀ y : Fin N → ℝ, ((∫ a, U ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) -
            ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted f))) ⬝ᵥ y) ∂(Measure.count.tilted f)) -
          c₀) = ∫ a, (U ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) -
            ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted f))) ⬝ᵥ y) - c₀)
              ∂(Measure.count.tilted f) := fun y => by
      rw [integral_sub Integrable.of_finite (integrable_const _)]
      simp
    simp_rw [hrew]
    refine (le_abs_self _).trans ?_
    have h1 := hCb N (Fin N → ℤˣ) ξ hξ_abs f
    exact h1.trans (mul_le_mul_of_nonneg_left
      (sum_integral_abs_pairProd_le ξ hξ_sq hN f q v hv hk)
        hC0 |>.trans (le_of_eq (by simp only [hC₂, hJ]; ring)))
  have hnonneg : ∀ g : FinPairs N → ℝ, 0 ≤ ∫ y : Fin N → ℝ,
      ((∫ a, U ((fun i => (Real.sqrt N)⁻¹ * (((a i : ℤ) : ℝ) -
            ∫ b, ((b i : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy N β h g)))) ⬝ᵥ y)
          ∂(Measure.count.tilted (skGibbsEnergy N β h g))) - c₀) ^ (2 * k)
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) := fun g =>
    integral_nonneg fun y => Even.pow_nonneg ⟨k, by ring⟩ _
  calc _ ≤ ∫ g, C₂ * J g ∂P :=
        integral_mono_of_nonneg (ae_of_all _ hnonneg) (hJint.const_mul C₂) (ae_of_all _ hpt)
    _ = C₂ * ∫ g, J g ∂P := integral_const_mul _ _
    _ ≤ C₂ * (K' / (N : ℝ) ^ k) := mul_le_mul_of_nonneg_left hJmom hC₂0
    _ ≤ (C₂ * K' + 1) / (N : ℝ) ^ k := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by linarith) hNk.le

end SpinGlasses
