/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenIterStructure
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPathCalculus
public import LeanMachineLearning.SpinGlasses.Talagrand.GuerraReplicaSymmetric.SKFixedPoint
public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapCLT.HigherOrderCavity.SKCavityHigherOrder

/-!
# Lemma 1.11.3: size of the iterated cavity derivatives (Talagrand, Eq. (1.334))

For `β² ≤ β₀² < 1/4` the `m`-th derivative of the cavity path average `u ↦ ν_u(f)` is bounded,
uniformly in `u ∈ [0, 1]`, by `K (N+1)^{-m/2} ν(f²)^{1/2}`, where `ν` is the `(N+1)`-spin SK
average with `n` replicas.  The proof expands all `m` derivatives into signed sums of products of
`m` centered overlaps (`skCavityIterKernel_structure`), applies Cauchy-Schwarz once for each
term, compares the path average with the SK average (Lemma 1.6.4,
`sk_cavity_path_square_le_exp_mul`) and uses the moment bound `sk_cavity_prod_sq_le`.

## Main declarations

* `SpinGlasses.abs_skCavityPathMean_iterKernel_le`: the bound for `ν_u(skCavityIterKernel …)`.
* `SpinGlasses.abs_iteratedDerivWithin_skCavityPathMean_le`: Lemma 1.11.3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- Lemma 1.6.4 for the cavity-path average of `R` replicas. -/
theorem skCavityPathMean_le_exp_mul (N R : ℕ) (β q h : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (G : (Fin R → Fin (N + 1) → ℤˣ) → ℝ) (hG : ∀ σ, 0 ≤ G σ) (u : ℝ)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    skCavityPathMean N R β q h u G ≤ Real.exp (4 * (R : ℝ) ^ 2 * β ^ 2) *
      ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin R → Fin (N + 1) → ℤˣ, G σ
        ∂(Measure.pi fun _ : Fin R => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
  sk_cavity_path_square_le_exp_mul N R β q h hq G hG u hu

/-- The `(N+1)`-spin SK average of an observable of the replicas `ι r` only is its average over
the replicas `r` only. -/
theorem integral_sk_avg_comp_injective (N : ℕ) (β h : ℝ) {n R : ℕ} {ι : Fin n → Fin R}
    (hι : Function.Injective ι) (F : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin R → Fin (N + 1) → ℤˣ, F (fun r => σ (ι r))
        ∂(Measure.pi fun _ : Fin R => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
    ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, F σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
  integral_congr_ae (ae_of_all _ fun _ => integral_pi_count_tilted_comp_injective hι _ F)

theorem sqrt_pow_eq_rpow_half (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    Real.sqrt (x ^ m) = x ^ ((m : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1
  ring

/-- **Lemma 1.11.3 (Eq. (1.334)), kernel form.**  For `β² ≤ β₀² < 1/4` and the fixed point
`q`, the cavity-path average of the `m`-fold iterated kernel is at most
`K (N+1)^{-m/2} ν(f²)^{1/2}`, uniformly in `u ∈ [0, 1]`, with `K` chosen before
`β, h, q, N, f`. -/
theorem abs_skCavityPathMean_iterKernel_le (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (m n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) (u : ℝ),
      u ∈ Set.Icc (0 : ℝ) 1 →
      |skCavityPathMean N (skCavityIterReplicaCount m n) β q h u
          (skCavityIterKernel N β q m n f)| ≤
        K / ((N : ℝ) + 1) ^ ((m : ℝ) / 2) *
          Real.sqrt (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ ^ 2
            ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
                h * ∑ i : Fin (N + 1), (a i : ℝ))
            ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) := by
  set R := skCavityIterReplicaCount m n with hR
  obtain ⟨T, hT, w, ι, a, b, hι, hab, hw0, hwsum, hbound⟩ := abs_skCavityIterKernel_le m n
  obtain ⟨K1, hK1, hK1'⟩ := sk_cavity_prod_sq_le β₀ hβ₀ m 1
  have hBnd := skCavityIterWeightBound_nonneg m n
  set E : ℝ := Real.exp (4 * (R : ℝ) ^ 2 * β₀ ^ 2) with hE
  have hE1 : 0 < E := Real.exp_pos _
  refine ⟨(β₀ ^ 2) ^ m * skCavityIterWeightBound m n * E * Real.sqrt K1 + 1, by positivity, ?_⟩
  intro β h q hfix hβ N f u hu
  have hq := fixedPoint_mem_Icc hfix
  have hEβ : Real.exp (4 * (R : ℝ) ^ 2 * β ^ 2) ≤ E :=
    Real.exp_le_exp.2 (by nlinarith [sq_nonneg (R : ℝ)])
  let fι : (Fin R → Fin (N + 1) → ℤˣ) → ℝ := fun τ => f (fun r => τ (ι r))
  let P : T → (Fin R → Fin (N + 1) → ℤˣ) → ℝ := fun t τ => ∏ r : Fin m,
    ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (τ (a t r) i.castSucc : ℝ)) ⬝ᵥ
      fun i : Fin N => (τ (b t r) i.castSucc : ℝ)) - q)
  set s : ℝ := ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ ^ 2
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) with hs
  have hs0 : 0 ≤ s := integral_nonneg fun g => integral_nonneg fun σ => sq_nonneg _
  have hM : 0 < (N : ℝ) + 1 := by positivity
  set D : ℝ := ((N : ℝ) + 1) ^ ((m : ℝ) / 2) with hDdef
  have hD0 : 0 < D := Real.rpow_pos_of_pos hM _
  have hD2 : D ^ 2 = ((N : ℝ) + 1) ^ m := by
    rw [hDdef, ← sqrt_pow_eq_rpow_half _ hM.le, Real.sq_sqrt (by positivity)]
  have hprod : ∀ t τ, ∏ r, skCavityTruncDev N q (τ (a t r)) (τ (b t r)) = |P t τ| := by
    intro t τ
    simp only [skCavityTruncDev, P, Finset.abs_prod]
  -- the per-term bound
  have hpt : ∀ t, skCavityPathMean N R β q h u (fun τ => |fι τ| * |P t τ|) ≤
      E * Real.sqrt s * (Real.sqrt K1 / D) := by
    intro t
    have hcs := skCavityPathMean_mul_sq_le N R β q h u (fun τ => |fι τ|) (fun τ => |P t τ|)
    simp only [sq_abs] at hcs
    have hx0 : 0 ≤ skCavityPathMean N R β q h u (fun τ => |fι τ| * |P t τ|) := by
      have := skCavityPathMean_mono N R β q h u (f := fun _ => 0)
        (g := fun τ => |fι τ| * |P t τ|) fun τ => by positivity
      simpa [skCavityPathMean_eq] using this
    have hA0 := skCavityPathMean_le_exp_mul N R β q h hq (fun τ => fι τ ^ 2)
      (fun _ => sq_nonneg _) u hu
    have hm := integral_sk_avg_comp_injective N β h hι (fun σ => f σ ^ 2)
    have hA : skCavityPathMean N R β q h u (fun τ => fι τ ^ 2) ≤ E * s :=
      (hA0.trans_eq (congrArg (Real.exp (4 * (R : ℝ) ^ 2 * β ^ 2) * ·) hm)).trans
        (mul_le_mul_of_nonneg_right hEβ hs0)
    have hB0 := skCavityPathMean_le_exp_mul N R β q h hq (fun τ => P t τ ^ 2)
      (fun _ => sq_nonneg _) u hu
    have hK := hK1' β h q hfix hβ N R (a t) (b t) (hab t) (fun _ => 1) (fun _ => by simp)
    simp only [one_mul] at hK
    have hB : skCavityPathMean N R β q h u (fun τ => P t τ ^ 2) ≤
        E * (K1 / ((N : ℝ) + 1) ^ m) :=
      hB0.trans (mul_le_mul hEβ hK (integral_nonneg fun g => integral_nonneg fun σ =>
        sq_nonneg _) hE1.le)
    have hsq : (skCavityPathMean N R β q h u (fun τ => |fι τ| * |P t τ|)) ^ 2 ≤
        (E * Real.sqrt s * (Real.sqrt K1 / D)) ^ 2 := by
      have hY : (E * Real.sqrt s * (Real.sqrt K1 / D)) ^ 2 =
          (E * s) * (E * (K1 / ((N : ℝ) + 1) ^ m)) := by
        rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt hs0, Real.sq_sqrt hK1.le, hD2]
        ring
      rw [hY]
      refine hcs.trans (mul_le_mul hA hB ?_ (by positivity))
      exact (skCavityPathMean_mono N R β q h u (f := fun _ => 0)
        (g := fun τ => P t τ ^ 2) fun τ => sq_nonneg _).trans' (by simp [skCavityPathMean_eq])
    have hY0 : 0 ≤ E * Real.sqrt s * (Real.sqrt K1 / D) := by positivity
    by_contra hlt
    push Not at hlt
    exact absurd hsq (not_le.2 (pow_lt_pow_left₀ hlt hY0 two_ne_zero))
  -- domination of the kernel by the explicit positive combination
  have hdom : ∀ τ : Fin R → Fin (N + 1) → ℤˣ,
      |skCavityIterKernel N β q m n f τ| ≤
        ∑ t, ((β ^ 2) ^ m * w t) * (|fι τ| * |P t τ|) := fun τ => by
    refine (hbound N β q f τ).trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hprod]
    ring
  have h1 := abs_skCavityPathMean_le N R β q h u hdom
  rw [skCavityPathMean_finset_sum N R β q h u Finset.univ (fun t => (β ^ 2) ^ m * w t)
    (fun t τ => |fι τ| * |P t τ|)] at h1
  have h2 : ∑ t, ((β ^ 2) ^ m * w t) *
      skCavityPathMean N R β q h u (fun τ => |fι τ| * |P t τ|) ≤
      ∑ t, ((β ^ 2) ^ m * w t) * (E * Real.sqrt s * (Real.sqrt K1 / D)) :=
    Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hpt t)
      (mul_nonneg (pow_nonneg (sq_nonneg β) m) (hw0 t))
  rw [← Finset.sum_mul, ← Finset.mul_sum, hwsum] at h2
  have hβm : (β ^ 2) ^ m ≤ (β₀ ^ 2) ^ m := pow_le_pow_left₀ (sq_nonneg β) hβ m
  have hK0 : (β₀ ^ 2) ^ m * skCavityIterWeightBound m n * E * Real.sqrt K1 ≤
      (β₀ ^ 2) ^ m * skCavityIterWeightBound m n * E * Real.sqrt K1 + 1 := le_add_of_nonneg_right
    zero_le_one
  calc _ ≤ _ := h1.trans h2
    _ ≤ (β₀ ^ 2) ^ m * skCavityIterWeightBound m n * (E * Real.sqrt s * (Real.sqrt K1 / D)) := by
        gcongr
    _ = ((β₀ ^ 2) ^ m * skCavityIterWeightBound m n * E * Real.sqrt K1) / D * Real.sqrt s := by
        ring
    _ ≤ _ := by gcongr

/-- **Talagrand's Lemma 1.11.3 (Eq. (1.334)).** For `β² ≤ β₀² < 1/4` and the fixed point `q`,
every `m`-th derivative of the cavity path average `u ↦ ν_u(f)` of an `n`-replica observable is
bounded on `[0, 1]` by `K (N+1)^{-m/2} ν(f²)^{1/2}`, where `ν` is the `(N+1)`-spin SK average
and `K` is chosen before `β, h, q, N, f`. -/
theorem abs_iteratedDerivWithin_skCavityPathMean_le (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (m n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) (u : ℝ),
      u ∈ Set.Icc (0 : ℝ) 1 →
      |iteratedDerivWithin m (fun t => skCavityPathMean N n β q h t f) (Set.Icc 0 1) u| ≤
        K / ((N : ℝ) + 1) ^ ((m : ℝ) / 2) *
          Real.sqrt (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ ^ 2
            ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
                h * ∑ i : Fin (N + 1), (a i : ℝ))
            ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) := by
  obtain ⟨K, hK, hK'⟩ := abs_skCavityPathMean_iterKernel_le β₀ hβ₀ m n
  refine ⟨K, hK, fun β h q hfix hβ N f u hu => ?_⟩
  rw [iteratedDerivWithin_skCavityPathMean N m β q h (fixedPoint_mem_Icc hfix) n f u hu]
  exact hK' β h q hfix hβ N f u hu

end SpinGlasses
