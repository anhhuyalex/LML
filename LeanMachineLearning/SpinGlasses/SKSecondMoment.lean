/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKRectangularDerivative
public import LeanMachineLearning.SpinGlasses.SKOverlapContraction
public import LeanMachineLearning.SpinGlasses.SKOverlapConcentration

/-!
# The second moment of the rectangular overlap (Talagrand's Proposition 1.8.5)

For `β < 1/2`, with `q` the fixed point and `q̂ = 𝔼 tanh⁴ (β z √q + h)`,
`ν(((σ¹ - σ²)·(σ³ - σ⁴)/N)²) = 4 (1 - 2q + q̂) / (N (1 - β² (1 - 2q + q̂))) + O(N^{-3/2})`.
Here `N + 1` is the number of spins and the error is explicit, `K / (N+1)^{3/2}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Overlap moments of the `(N+1)`-spin system** (Eq. (1.88)), in the notation of the cavity
files: `𝔼⟨(R_{1,2} - q)^{2r}⟩ ≤ K / (N+1)^r` uniformly in `β² ≤ β₀² < 1/4`. -/
theorem sk_dev_moment_le (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (r : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
      ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ (2 * r)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤ K / ((N : ℝ) + 1) ^ r := by
  obtain ⟨K, hK0, hK⟩ := sk_overlap_moment_le_of_exp_unif β₀ hβ₀ r
  refine ⟨K, hK0, fun β h q hfix hb N => ?_⟩
  have := hK β h q hfix hb (N + 1) (Nat.succ_pos N)
  push_cast at this
  exact this

/-- **Site symmetry of the rectangular overlap** (Eq. (1.240)): with
`a_i = (σ¹_i - σ²_i)(σ³_i - σ⁴_i)` and `rect = (N+1)⁻¹ ∑_i a_i`, we have
`ν(rect²) = ν(a_N rect)`. -/
theorem sk_rect_sq_eq_last_site (N : ℕ) (β h : ℝ) :
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let rect : (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
      (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ) - (σ 1 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 2 i : ℝ) - (σ 3 i : ℝ))
    ∫ g, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, rect σ ^ 2
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) =
    ∫ g, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ,
        (((σ 0 (Fin.last N) : ℝ) - (σ 1 (Fin.last N) : ℝ)) *
          ((σ 2 (Fin.last N) : ℝ) - (σ 3 (Fin.last N) : ℝ))) * rect σ
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  intro Esk rect
  let a : Fin (N + 1) → (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun i σ =>
    ((σ 0 i : ℝ) - (σ 1 i : ℝ)) * ((σ 2 i : ℝ) - (σ 3 i : ℝ))
  let Θ : Fin (N + 1) → (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun i σ => a i σ * rect σ
  let ν : ((Fin 4 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun Φ =>
    ∫ g, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Φ σ
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  have hrect : ∀ σ, rect σ = (N + 1 : ℝ)⁻¹ * ∑ i, a i σ := fun σ => by
    simp only [rect, a, dotProduct]
  have hperm : ∀ (pm : Equiv.Perm (Fin (N + 1))) σ,
      rect (fun r i => σ r (pm i)) = rect σ := fun pm σ => by
    simp only [hrect, a]
    rw [Equiv.sum_comp pm fun i => ((σ 0 i : ℝ) - (σ 1 i : ℝ)) * ((σ 2 i : ℝ) - (σ 3 i : ℝ))]
  have hsite : ∀ i, ν (Θ i) = ν (Θ (Fin.last N)) := fun i => by
    have h1 := sk_replica_site_perm (R := Fin 4) N β h (Equiv.swap i (Fin.last N))
      (fun σ => Θ (Fin.last N) σ)
    have h2 : ∀ σ : Fin 4 → Fin (N + 1) → ℤˣ,
        Θ (Fin.last N) (fun r j => σ r (Equiv.swap i (Fin.last N) j)) = Θ i σ := fun σ => by
      simp only [Θ, hperm, a, Equiv.swap_apply_right]
    simp only [h2] at h1
    exact h1
  have hint : ∀ i, Integrable (fun g : FinPairs (N + 1) → ℝ => ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ,
      Θ i σ ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted (Esk g)))
      (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := fun i =>
    integrable_integral_sk_replica N 4 β h (Θ i)
  have hsum : ν (fun σ => ∑ i, Θ i σ) = ∑ i, ν (Θ i) := by
    simp only [ν]
    have e1 : ∀ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, ∑ i, Θ i σ
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted (Esk g)) =
        ∑ i, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Θ i σ
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted (Esk g)) := fun g =>
      integral_finsetSum _ fun i _ => Integrable.of_finite
    simp_rw [e1]
    exact integral_finsetSum _ fun i _ => hint i
  have hpt : ∀ σ, ∑ i, Θ i σ = ((N + 1 : ℕ) : ℝ) * rect σ ^ 2 := fun σ => by
    have hs : ∑ i, a i σ = ((N + 1 : ℕ) : ℝ) * rect σ := by
      rw [hrect]
      push_cast
      field_simp
    simp only [Θ, ← Finset.sum_mul]
    rw [hs]
    ring
  have hlin : ν (fun σ => ∑ i, Θ i σ) = ((N + 1 : ℕ) : ℝ) * ν (fun σ => rect σ ^ 2) := by
    simp only [ν, hpt]
    simp only [integral_const_mul]
  have hfin : ∑ i, ν (Θ i) = ((N + 1 : ℕ) : ℝ) * ν (Θ (Fin.last N)) := by
    simp only [hsite, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN : ((N + 1 : ℕ) : ℝ) ≠ 0 := by push_cast; exact Nat.cast_add_one_ne_zero N
  have h3 : ((N + 1 : ℕ) : ℝ) * ν (fun σ => rect σ ^ 2) =
      ((N + 1 : ℕ) : ℝ) * ν (Θ (Fin.last N)) := by rw [← hlin, hsum, hfin]
  exact mul_left_cancel₀ hN h3

/-- Four-term power estimate for the rectangular combination, even powers `2` and `4`. -/
theorem rect_sq_le (u₁ u₂ u₃ u₄ : ℝ) :
    (u₁ - u₂ - u₃ + u₄) ^ 2 ≤ 4 * (u₁ ^ 2 + u₂ ^ 2 + u₃ ^ 2 + u₄ ^ 2) := by
  nlinarith [sq_nonneg (u₁ + u₂), sq_nonneg (u₁ + u₃), sq_nonneg (u₁ - u₄), sq_nonneg (u₂ - u₃),
    sq_nonneg (u₂ + u₄), sq_nonneg (u₃ + u₄)]

theorem rect_pow_four_le (u₁ u₂ u₃ u₄ : ℝ) :
    (u₁ - u₂ - u₃ + u₄) ^ 4 ≤ 64 * (u₁ ^ 4 + u₂ ^ 4 + u₃ ^ 4 + u₄ ^ 4) := by
  have h1 := rect_sq_le u₁ u₂ u₃ u₄
  have h2 : (u₁ ^ 2 + u₂ ^ 2 + u₃ ^ 2 + u₄ ^ 2) ^ 2 ≤
      4 * (u₁ ^ 4 + u₂ ^ 4 + u₃ ^ 4 + u₄ ^ 4) := by
    nlinarith [sq_nonneg (u₁ ^ 2 - u₂ ^ 2), sq_nonneg (u₁ ^ 2 - u₃ ^ 2),
      sq_nonneg (u₁ ^ 2 - u₄ ^ 2), sq_nonneg (u₂ ^ 2 - u₃ ^ 2), sq_nonneg (u₂ ^ 2 - u₄ ^ 2),
      sq_nonneg (u₃ ^ 2 - u₄ ^ 2)]
  have h0 : 0 ≤ (u₁ - u₂ - u₃ + u₄) ^ 2 := sq_nonneg _
  calc (u₁ - u₂ - u₃ + u₄) ^ 4 = ((u₁ - u₂ - u₃ + u₄) ^ 2) ^ 2 := by ring
    _ ≤ (4 * (u₁ ^ 2 + u₂ ^ 2 + u₃ ^ 2 + u₄ ^ 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = 16 * (u₁ ^ 2 + u₂ ^ 2 + u₃ ^ 2 + u₄ ^ 2) ^ 2 := by ring
    _ ≤ 16 * (4 * (u₁ ^ 4 + u₂ ^ 4 + u₃ ^ 4 + u₄ ^ 4)) := by linarith
    _ = _ := by ring

/-- **Moments of the rectangular overlap from moments of one overlap.**  If
`(u₁ - u₂ - u₃ + u₄)^m ≤ C (u₁^m + u₂^m + u₃^m + u₄^m)` then
`ν(rect^m) ≤ 4 C ν((R_{1,2} - q)^m)`, since the four overlaps `R_{ab}`, `a ∈ {1,2}`, `b ∈ {3,4}`
are replicas pairs with the same average. -/
theorem sk_rect_moment_le (N : ℕ) (β h q : ℝ) (m : ℕ) (C : ℝ)
    (hC : ∀ u₁ u₂ u₃ u₄ : ℝ, (u₁ - u₂ - u₃ + u₄) ^ m ≤ C * (u₁ ^ m + u₂ ^ m + u₃ ^ m + u₄ ^ m)) :
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let rect : (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
      (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ) - (σ 1 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 2 i : ℝ) - (σ 3 i : ℝ))
    ∫ g, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, rect σ ^ m
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
    4 * C * ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ m
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  intro Esk rect
  let Rm : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun x y =>
    (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (x i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (y i : ℝ)) - q
  have hEg (c : Fin (N + 1) → ℤˣ) : Measurable (fun g : FinPairs (N + 1) → ℝ => Esk g c) := by
    dsimp [Esk]
    fun_prop
  let Iu : Bool → Fin 4 := fun u => if u then 0 else 1
  let Jv : Bool → Fin 4 := fun v => if v then 2 else 3
  have hrect : ∀ σ, rect σ = Rm (σ 0) (σ 2) - Rm (σ 0) (σ 3) - Rm (σ 1) (σ 2) + Rm (σ 1) (σ 3) :=
    fun σ => by
    simp only [rect, Rm, dotProduct, mul_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  let G : Bool × Bool → (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun j σ =>
    Rm (σ (Iu j.1)) (σ (Jv j.2)) ^ m
  have hle : ∀ σ, rect σ ^ m ≤ ∑ j : Bool × Bool, C * G j σ := fun σ => by
    rw [hrect]
    refine (hC _ _ _ _).trans (le_of_eq ?_)
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, G, Iu, Jv, ite_true, ite_false,
      Bool.false_eq_true]
    ring
  have hpair : ∀ (j : Bool × Bool), ∫ g, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, G j σ
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) =
      ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Rm (σ 0) (σ 1) ^ m
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := fun j => by
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    refine integral_pi_count_tilted_pair (a := Iu j.1) (b := Jv j.2) ?_ (Esk g)
      (fun x y => Rm x y ^ m)
    cases j.1 <;> cases j.2 <;> simp [Iu, Jv]
  have hmono : ∫ g, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, rect σ ^ m
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
      ∫ g, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, ∑ j : Bool × Bool, C * G j σ
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
    integral_integral_sk_replica_mono N 4 β h hle
  refine hmono.trans (le_of_eq ?_)
  rw [integral_gibbs_finset_sum (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    (R := Fin 4) Esk hEg Finset.univ (fun _ => C) G]
  simp only [hpair, Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
    nsmul_eq_mul]
  push_cast
  ring

/-- **The decoupled average of the rectangular sign polynomial vanishes** (Eq. (1.150) with
`𝔼 tanh² Y = q`): `ν₀(f⁻ (ε₁ - ε₂)(ε₃ - ε₄)) = 0` for every observable `f⁻` of the first `N`
spins. -/
theorem sk_cavity_decoupled_rect_zero (N : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (F : (Fin 4 → Fin N → ℤˣ) → ℝ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) →
        (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ,
          F (fun r i => σ r i.castSucc) *
            ((((σ 0 (Fin.last N) : ℤˣ) : ℝ) - ((σ 1 (Fin.last N) : ℤˣ) : ℝ)) *
              (((σ 2 (Fin.last N) : ℤˣ) : ℝ) - ((σ 3 (Fin.last N) : ℤˣ) : ℝ)))
          ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) = 0 := by
  intro B E
  have hEm (a : Fin (N + 1) → ℤˣ) :
      Measurable (fun x : (FinPairs N → ℝ) × ((Fin N → ℝ) × ℝ) => E (π / 2) x.1 x.2 a) := by
    dsimp [E, B]
    fun_prop
  let X : Bool → Fin 4 := fun u => if u then 0 else 1
  let Y : Bool → Fin 4 := fun v => if v then 2 else 3
  let sg : Bool → ℝ := fun u => if u then 1 else -1
  let Gj : Bool × Bool → (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun j σ =>
    F (fun r i => σ r i.castSucc) *
      (((σ (X j.1) (Fin.last N) : ℤˣ) : ℝ) * ((σ (Y j.2) (Fin.last N) : ℤˣ) : ℝ))
  have hpt : ∀ σ : Fin 4 → Fin (N + 1) → ℤˣ,
      F (fun r i => σ r i.castSucc) *
        ((((σ 0 (Fin.last N) : ℤˣ) : ℝ) - ((σ 1 (Fin.last N) : ℤˣ) : ℝ)) *
          (((σ 2 (Fin.last N) : ℤˣ) : ℝ) - ((σ 3 (Fin.last N) : ℤˣ) : ℝ))) =
      ∑ j, (sg j.1 * sg j.2) * Gj j σ := fun σ => by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, sg, Gj, X, Y, ite_true, ite_false,
      Bool.false_eq_true]
    ring
  simp_rw [hpt]
  rw [integral_nested_gibbs_finset_sum (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) (E (π / 2)) hEm
    Finset.univ (fun j => sg j.1 * sg j.2) Gj]
  have hend : ∀ (u v : Bool), ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ,
        Gj (u, v) σ ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) =
      q * ∫ g', ∫ ρ : Fin 4 → Fin N → ℤˣ, F ρ
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ))) ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) :=
    fun u v => by
    have hxy : X u ≠ Y v := by cases u <;> cases v <;> simp [X, Y]
    have := sk_cavity_decoupled_endpoint_replicas N β q h ({X u, Y v} : Finset (Fin 4)) F
    rw [Finset.card_pair hxy, hfix] at this
    simp only [Finset.prod_pair hxy] at this
    exact this
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, hend, sg, ite_true, ite_false, Bool.false_eq_true]
  ring

/-- **The decoupled second moment of the rectangular sign polynomial**:
`ν₀(((ε₁ - ε₂)(ε₃ - ε₄))²) = 4 (1 - 2 q + q̂)` (Eq. (1.242)). -/
theorem sk_cavity_decoupled_rect_sq (N : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) = q) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) →
        (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ,
          ((((σ 0 (Fin.last N) : ℤˣ) : ℝ) - ((σ 1 (Fin.last N) : ℤˣ) : ℝ)) *
              (((σ 2 (Fin.last N) : ℤˣ) : ℝ) - ((σ 3 (Fin.last N) : ℤˣ) : ℝ))) ^ 2
          ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    4 * ((∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ 4 ∂(gaussianReal 0 1)) - 2 * q + 1) := by
  intro B E
  have hEm (a : Fin (N + 1) → ℤˣ) :
      Measurable (fun x : (FinPairs N → ℝ) × ((Fin N → ℝ) × ℝ) => E (π / 2) x.1 x.2 a) := by
    dsimp [E, B]
    fun_prop
  let I : Fin 4 → Finset (Fin 4) := ![∅, {0, 1}, {2, 3}, Finset.univ]
  let c : Fin 4 → ℝ := ![4, -4, -4, 4]
  let Gj : Fin 4 → (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun k σ =>
    ∏ r ∈ I k, ((σ r (Fin.last N) : ℤˣ) : ℝ)
  have hpt : ∀ σ : Fin 4 → Fin (N + 1) → ℤˣ,
      ((((σ 0 (Fin.last N) : ℤˣ) : ℝ) - ((σ 1 (Fin.last N) : ℤˣ) : ℝ)) *
          (((σ 2 (Fin.last N) : ℤˣ) : ℝ) - ((σ 3 (Fin.last N) : ℤˣ) : ℝ))) ^ 2 =
      ∑ k, c k * Gj k σ := fun σ => by
    have h0 := units_cast_sq (σ 0 (Fin.last N))
    have h1 := units_cast_sq (σ 1 (Fin.last N))
    have h2 := units_cast_sq (σ 2 (Fin.last N))
    have h3 := units_cast_sq (σ 3 (Fin.last N))
    simp [Fin.sum_univ_four, c, Gj, I, Fin.prod_univ_four]
    generalize ((σ 0 (Fin.last N) : ℤˣ) : ℝ) = a0 at *
    generalize ((σ 1 (Fin.last N) : ℤˣ) : ℝ) = a1 at *
    generalize ((σ 2 (Fin.last N) : ℤˣ) : ℝ) = a2 at *
    generalize ((σ 3 (Fin.last N) : ℤˣ) : ℝ) = a3 at *
    linear_combination ((a2 - a3) ^ 2) * (h0 + h1) + (2 - 2 * a0 * a1) * (h2 + h3)
  simp_rw [hpt]
  rw [integral_nested_gibbs_finset_sum (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) (E (π / 2)) hEm
    Finset.univ c Gj]
  have hend : ∀ k : Fin 4, ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ,
        Gj k σ ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) =
      ∫ z, Real.tanh (β * z * Real.sqrt q + h) ^ (I k).card ∂(gaussianReal 0 1) := fun k => by
    have := sk_cavity_decoupled_endpoint_replicas N β q h (I k) (fun _ => 1)
    simp only [one_mul, mul_one, integral_const, probReal_univ, one_smul] at this
    exact this
  have hc2 : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
  have hc3 : ({2, 3} : Finset (Fin 4)).card = 2 := by decide
  have hc4 : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
  simp only [Fin.sum_univ_four, hend, c, I, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    Finset.card_empty, hc2, hc3, hc4, hfix]
  simp only [pow_zero, integral_const, probReal_univ, smul_eq_mul]
  ring

/-- **The linear system for the rectangular second moment** (the algebra at the end of the proof
of Proposition 1.8.5).  If `X = ν(rect²)`, `Pf = ν(f*)`, `Z₀ = ν₀(rect⁻²)`, `Z₁ = ν(rect⁻²)`,
`Pa = ν(a²)` satisfy `X = Pf + Pa/M`, `Pf ≈ λ Z₀`, `Z₀ ≈ Z₁`, `Z₁ = X - 2 X/M + Pa/M²` and
`Pa ≈ 4 c₂`, then `X ≈ 4 c₂ / (M (1 - λ))`, with the errors added up. -/
theorem second_moment_assembly {X Pa Pf Z0 Z1 M lam c2 e1 e2 e3 e4 : ℝ} (hM : 1 ≤ M)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1 / 4) (hPa : |Pa| ≤ 16)
    (h1 : X = Pf + Pa / M) (h2 : |Pf - lam * Z0| ≤ e1) (h3 : |Z0 - Z1| ≤ e2)
    (h4 : Z1 = X - 2 * X / M + Pa / M ^ 2) (h5 : |X| ≤ e3) (h6 : |Pa - 4 * c2| ≤ e4) :
    |X - 4 * c2 / (M * (1 - lam))| ≤
      4 / 3 * (e1 + e2 / 4 + e3 / (2 * M) + 4 / M ^ 2 + e4 / M) := by
  have hM0 : 0 < M := by linarith
  have hD : 0 < 1 - lam := by linarith
  have hX : (1 - lam) * X = (Pf - lam * Z0) + lam * (Z0 - Z1) - 2 * lam * X / M +
      lam * Pa / M ^ 2 + Pa / M := by
    rw [h1] at h4 ⊢
    linear_combination lam * h4
  have hkey : (1 - lam) * (X - 4 * c2 / (M * (1 - lam))) =
      (Pf - lam * Z0) + lam * (Z0 - Z1) - 2 * lam * X / M + lam * Pa / M ^ 2 +
        (Pa - 4 * c2) / M := by
    have : (1 - lam) * (4 * c2 / (M * (1 - lam))) = 4 * c2 / M := by
      field_simp
    rw [mul_sub, this, hX]
    ring
  have hb : |(1 - lam) * (X - 4 * c2 / (M * (1 - lam)))| ≤
      e1 + e2 / 4 + e3 / (2 * M) + 4 / M ^ 2 + e4 / M := by
    rw [hkey]
    have t2 : |lam * (Z0 - Z1)| ≤ e2 / 4 := by
      rw [abs_mul, abs_of_nonneg hlam0]
      have := abs_nonneg (Z0 - Z1)
      nlinarith
    have t3 : |2 * lam * X / M| ≤ e3 / (2 * M) := by
      have e : |2 * lam * X / M| = (2 * lam * |X|) / M := by
        rw [abs_div, abs_of_pos hM0, abs_mul, abs_mul, abs_two, abs_of_nonneg hlam0]
      rw [e]
      have : 2 * lam * |X| ≤ e3 / 2 := by nlinarith [abs_nonneg X]
      calc 2 * lam * |X| / M ≤ e3 / 2 / M := div_le_div_of_nonneg_right this hM0.le
        _ = e3 / (2 * M) := by field_simp
    have t4 : |lam * Pa / M ^ 2| ≤ 4 / M ^ 2 := by
      rw [abs_div, abs_of_pos (by positivity : 0 < M ^ 2), abs_mul, abs_of_nonneg hlam0]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [abs_nonneg Pa]
    have t5 : |(Pa - 4 * c2) / M| ≤ e4 / M := by
      rw [abs_div, abs_of_pos hM0]
      exact div_le_div_of_nonneg_right h6 hM0.le
    obtain ⟨a1, a2⟩ := abs_le.1 h2
    obtain ⟨b1, b2⟩ := abs_le.1 t2
    obtain ⟨c1, c2'⟩ := abs_le.1 t3
    obtain ⟨d1, d2⟩ := abs_le.1 t4
    obtain ⟨f1, f2⟩ := abs_le.1 t5
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hfin : |X - 4 * c2 / (M * (1 - lam))| * (1 - lam) ≤
      e1 + e2 / 4 + e3 / (2 * M) + 4 / M ^ 2 + e4 / M := by
    rw [abs_mul, abs_of_pos hD] at hb
    linarith
  have h34 : (3 : ℝ) / 4 ≤ 1 - lam := by linarith
  have : |X - 4 * c2 / (M * (1 - lam))| * (3 / 4) ≤
      e1 + e2 / 4 + e3 / (2 * M) + 4 / M ^ 2 + e4 / M :=
    le_trans (mul_le_mul_of_nonneg_left h34 (abs_nonneg _)) hfin
  linarith

/-- **Proposition 1.8.5, with explicit error terms (before choosing the constants).**  Let
`M = N + 1`, `c₂ = q̂ - 2q + 1` and `λ = β² c₂`.  If `𝔼⟨(R_{1,2} - q)²⟩ ≤ K₁ / M` and
`𝔼⟨(R_{1,2} - q)⁴⟩ ≤ K₂ / M²` then `ν(rect²)` differs from `4 c₂ / (M (1 - λ))` by at most
`4/3 (e₁ + e₂/4 + e₃/(2M) + 4/M² + e₄/M)`, where the `e_i` are the error terms of Eq. (1.216),
Eq. (1.215) for `rect⁻²`, the size of `ν(rect²)`, and Eq. (1.215) for `a_N²`. -/
theorem sk_rect_second_moment_aux (N : ℕ) (β q h K₁ K₂ : ℝ) (hβ : 4 * β ^ 2 < 1)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q) :
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    let c₂ : ℝ := (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1)) -
      2 * q + 1
    (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ≤ K₁ / ((N : ℝ) + 1) →
    (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 4
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ≤ K₂ / ((N : ℝ) + 1) ^ 2 →
    |(∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ) - (σ 1 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ) - (σ 3 i : ℝ))) ^ 2
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      4 * c₂ / (((N : ℝ) + 1) * (1 - β ^ 2 * c₂))| ≤
    4 / 3 * (2304 * β ^ 4 * Real.exp (256 * β ^ 2) *
        (Real.sqrt ((512 * K₁ + 512) / ((N : ℝ) + 1)) * Real.sqrt (K₂ / ((N : ℝ) + 1) ^ 2)) +
      32 * β ^ 2 * Real.exp (144 * β ^ 2) *
        (Real.sqrt ((2048 * K₂ + 2048) / ((N : ℝ) + 1) ^ 2) *
          Real.sqrt (K₁ / ((N : ℝ) + 1))) / 4 +
      16 * K₁ / ((N : ℝ) + 1) / (2 * ((N : ℝ) + 1)) + 4 / ((N : ℝ) + 1) ^ 2 +
      32 * β ^ 2 * Real.exp (144 * β ^ 2) * 16 *
        ((K₁ + 1) / (2 * Real.sqrt ((N : ℝ) + 1))) / ((N : ℝ) + 1)) := by
  intro Esk c₂
  sorry

end SpinGlasses
