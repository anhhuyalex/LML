/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKRectangularDerivative
public import LeanMachineLearning.SpinGlasses.SKOverlapContraction
public import LeanMachineLearning.SpinGlasses.SKOverlapConcentration
public import LeanMachineLearning.SpinGlasses.SKFixedPoint

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
    simp only [Fin.isValue, Fin.sum_univ_four, Matrix.cons_val_zero, Finset.prod_empty, mul_one,
      Matrix.cons_val_one, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
      Finset.prod_insert, Finset.prod_singleton, neg_mul, Matrix.cons_val, Fin.reduceEq,
      Fin.prod_univ_four, c, Gj, I]
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

/-- The Almeida-Thouless quantity `1 - 2 q + q̂ = 𝔼 (1 - tanh² Y)²` lies in `[0, 1]`. -/
theorem tanh_fourth_sub_two_add_one_mem_Icc (w h : ℝ) :
    (∫ z : ℝ, Real.tanh (w * z + h) ^ 4 ∂(gaussianReal 0 1)) -
      2 * (∫ z : ℝ, Real.tanh (w * z + h) ^ 2 ∂(gaussianReal 0 1)) + 1 ∈ Set.Icc (0 : ℝ) 1 :=
  probability_tanh_fourth_sub_two_add_one_mem_Icc (fun z => w * z + h) (by fun_prop)

/-- At a fixed point `q` of (1.74), the Almeida-Thouless quantity
`𝔼 tanh⁴ (β z √q + h) - 2 q + 1 = 1 - 2q + q̂` lies in `[0, 1]`. -/
theorem tanh_fourth_sub_two_mul_add_one_mem_Icc_of_fixedPoint {β q h : ℝ}
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q) :
    (∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 4 ∂(gaussianReal 0 1)) - 2 * q + 1 ∈
      Set.Icc (0 : ℝ) 1 := by
  have := tanh_fourth_sub_two_add_one_mem_Icc (β * Real.sqrt q) h
  rwa [hfix, ← integral_tanh_pow_mul_z_sqrt_eq β q h 4] at this

/-- Generic four-variable rectangle bound: `((x₀ - x₁)(x₂ - x₃))² ≤ 16` for `|x_i| ≤ 1`. -/
theorem sq_rect_le_of_abs_le_one {x₀ x₁ x₂ x₃ : ℝ}
    (h0 : |x₀| ≤ 1) (h1 : |x₁| ≤ 1) (h2 : |x₂| ≤ 1) (h3 : |x₃| ≤ 1) :
    ((x₀ - x₁) * (x₂ - x₃)) ^ 2 ≤ 16 := by
  have hd1 : |x₀ - x₁| ≤ 2 := (abs_sub x₀ x₁).trans (by linarith)
  have hd2 : |x₂ - x₃| ≤ 2 := (abs_sub x₂ x₃).trans (by linarith)
  have hp : |(x₀ - x₁) * (x₂ - x₃)| ≤ 4 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (x₀ - x₁), abs_nonneg (x₂ - x₃)]
  nlinarith [sq_abs ((x₀ - x₁) * (x₂ - x₃)), abs_nonneg ((x₀ - x₁) * (x₂ - x₃))]

/-- `((ε₁ - ε₂)(ε₃ - ε₄))² ≤ 16` for four signs. -/
theorem sq_sign_rect_le (u₀ u₁ u₂ u₃ : ℤˣ) :
    ((((u₀ : ℤ) : ℝ) - ((u₁ : ℤ) : ℝ)) * (((u₂ : ℤ) : ℝ) - ((u₃ : ℤ) : ℝ))) ^ 2 ≤ 16 :=
  sq_rect_le_of_abs_le_one (abs_units_cast_le_one u₀) (abs_units_cast_le_one u₁)
    (abs_units_cast_le_one u₂) (abs_units_cast_le_one u₃)

/-- An `n`-replica SK average is additive. -/
theorem sk_replica_avg_add (N n : ℕ) (β h : ℝ)
    (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (Φ Ψ : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    ν (fun σ => Φ σ + Ψ σ) = ν Φ + ν Ψ := by
  simp only [hν]
  have e1 : ∀ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, (Φ σ + Ψ σ)
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)) =
      (∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))) +
      ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Ψ σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ)) := fun g =>
    integral_add Integrable.of_finite Integrable.of_finite
  simp_rw [e1]
  exact integral_add (integrable_integral_sk_replica N n β h Φ)
    (integrable_integral_sk_replica N n β h Ψ)

/-- An `n`-replica SK average is homogeneous. -/
theorem sk_replica_avg_smul (N n : ℕ) (β h : ℝ)
    (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (c : ℝ) (Φ : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    ν (fun σ => c * Φ σ) = c * ν Φ := by
  simp only [hν, integral_const_mul]

/-- An `n`-replica SK average is monotone. -/
theorem sk_replica_avg_mono (N n : ℕ) (β h : ℝ)
    (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (Φ Ψ : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) (hΦΨ : ∀ σ, Φ σ ≤ Ψ σ) :
    ν Φ ≤ ν Ψ := by
  rw [hν, hν]
  exact integral_integral_sk_replica_mono N n β h hΦΨ

/-- An `n`-replica SK average is normalized. -/
theorem sk_replica_avg_const (N n : ℕ) (β h : ℝ)
    (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (c : ℝ) : ν (fun _ => c) = c := by
  simp [hν]

/-- Finite combinations commute with an `n`-replica SK average. -/
theorem sk_replica_avg_finset_sum (N n : ℕ) (β h : ℝ)
    (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (Φ : ι → (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    ν (fun σ => ∑ j ∈ s, c j * Φ j σ) = ∑ j ∈ s, c j * ν (Φ j) := by
  have hEg (a : Fin (N + 1) → ℤˣ) : Measurable (fun g : FinPairs (N + 1) → ℝ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)) := by fun_prop
  simp only [hν]
  exact integral_gibbs_finset_sum (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    (R := Fin n) _ hEg s c Φ

/-- **Calculus of an `n`-replica SK average.**  An average `ν` of observables of `n` replicas,
`ν Φ = 𝔼 ⟨Φ⟩`, is additive, homogeneous, monotone and normalized. -/
theorem sk_replica_avg_calculus (N n : ℕ) (β h : ℝ)
    (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) :
    (∀ Φ Ψ : (Fin n → Fin (N + 1) → ℤˣ) → ℝ, ν (fun σ => Φ σ + Ψ σ) = ν Φ + ν Ψ) ∧
    (∀ (c : ℝ) (Φ : (Fin n → Fin (N + 1) → ℤˣ) → ℝ), ν (fun σ => c * Φ σ) = c * ν Φ) ∧
    (∀ Φ Ψ : (Fin n → Fin (N + 1) → ℤˣ) → ℝ, (∀ σ, Φ σ ≤ Ψ σ) → ν Φ ≤ ν Ψ) ∧
    (∀ c : ℝ, ν (fun _ => c) = c) :=
  ⟨sk_replica_avg_add N n β h ν hν,
   sk_replica_avg_smul N n β h ν hν,
   sk_replica_avg_mono N n β h ν hν,
   sk_replica_avg_const N n β h ν hν⟩

/-- **The linear relations between the second moments** used in Proposition 1.8.5:
with `a = (ε₁ - ε₂)(ε₃ - ε₄)` the last-site factor, `rect = rect⁻ + a/M`, `f* = rect⁻ · a`,
one has `ν(rect²) = ν(a rect)`, `ν(a rect) = ν(f*) + ν(a²)/M` and
`ν((rect⁻)²) = ν(rect²) (1 - 2/M) + ν(a²)/M²`; moreover `0 ≤ ν(a²) ≤ 16`. -/
theorem sk_rect_nu_structure (N : ℕ) (β h : ℝ)
    (ν : ((Fin 4 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) :
    let aL : (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
      (((σ 0 (Fin.last N) : ℤˣ) : ℝ) - ((σ 1 (Fin.last N) : ℤˣ) : ℝ)) *
        (((σ 2 (Fin.last N) : ℤˣ) : ℝ) - ((σ 3 (Fin.last N) : ℤˣ) : ℝ))
    let rect : (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
      (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ) - (σ 1 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 2 i : ℝ) - (σ 3 i : ℝ))
    let Fo : (Fin 4 → Fin N → ℤˣ) → ℝ := fun ρ =>
      (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ 0 i : ℝ) - (ρ 1 i : ℝ)) ⬝ᵥ
        fun i : Fin N => (ρ 2 i : ℝ) - (ρ 3 i : ℝ))
    let rectm : (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun σ => Fo (fun r i => σ r i.castSucc)
    let fstar : (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
      Fo (fun r i => σ r i.castSucc) *
        ((((σ 0 (Fin.last N) : ℤˣ) : ℝ) - ((σ 1 (Fin.last N) : ℤˣ) : ℝ)) *
          (((σ 2 (Fin.last N) : ℤˣ) : ℝ) - ((σ 3 (Fin.last N) : ℤˣ) : ℝ)))
    ν (fun σ => rect σ ^ 2) = ν (fun σ => aL σ * rect σ) ∧
    ν (fun σ => aL σ * rect σ) = ν fstar + (1 / ((N : ℝ) + 1)) * ν (fun σ => aL σ ^ 2) ∧
    ν (fun σ => rectm σ ^ 2) = ν (fun σ => rect σ ^ 2) -
      2 / ((N : ℝ) + 1) * ν (fun σ => rect σ ^ 2) +
      1 / ((N : ℝ) + 1) ^ 2 * ν (fun σ => aL σ ^ 2) ∧
    0 ≤ ν (fun σ => rect σ ^ 2) ∧ 0 ≤ ν (fun σ => aL σ ^ 2) ∧ ν (fun σ => aL σ ^ 2) ≤ 16 := by
  intro aL rect Fo rectm fstar
  obtain ⟨hνadd, hνsmul, hνmono, hνconst⟩ := sk_replica_avg_calculus N 4 β h ν hν
  have hI1 : ∀ σ, rect σ = rectm σ + aL σ / ((N : ℝ) + 1) := fun σ => by
    simp only [rect, rectm, Fo, aL, dotProduct, Fin.sum_univ_castSucc]
    ring
  have hI2 : ∀ σ, aL σ * rect σ = fstar σ + (1 / ((N : ℝ) + 1)) * aL σ ^ 2 := fun σ => by
    rw [hI1]
    simp only [fstar, rectm, aL]
    ring
  have hI3 : ∀ σ, rectm σ ^ 2 = rect σ ^ 2 + (-(2 / ((N : ℝ) + 1))) * (aL σ * rect σ) +
      (1 / ((N : ℝ) + 1) ^ 2) * aL σ ^ 2 := fun σ => by
    have hM0 : (N : ℝ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero N
    have : rectm σ = rect σ - aL σ / ((N : ℝ) + 1) := by rw [hI1]; ring
    rw [this]
    field_simp
    ring
  have haL : ∀ σ, aL σ ^ 2 ≤ 16 := fun σ => sq_sign_rect_le _ _ _ _
  have hν0 : ∀ Φ : (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ, (∀ σ, 0 ≤ Φ σ) → 0 ≤ ν Φ := fun Φ hΦ => by
    have := hνmono (fun _ => 0) Φ (fun σ => by simpa using hΦ σ)
    rwa [hνconst] at this
  have hS1 : ν (fun σ => rect σ ^ 2) = ν (fun σ => aL σ * rect σ) := by
    rw [hν, hν]
    exact sk_rect_sq_eq_last_site N β h
  refine ⟨hS1, ?_, ?_, hν0 _ fun σ => sq_nonneg _, hν0 _ fun σ => sq_nonneg _, ?_⟩
  · rw [← hνsmul, ← hνadd]
    exact congrArg ν (funext hI2)
  · have : ν (fun σ => rectm σ ^ 2) = ν (fun σ => rect σ ^ 2) +
        (-(2 / ((N : ℝ) + 1))) * ν (fun σ => aL σ * rect σ) +
        (1 / ((N : ℝ) + 1) ^ 2) * ν (fun σ => aL σ ^ 2) := by
      rw [← hνsmul, ← hνsmul, ← hνadd, ← hνadd]
      exact congrArg ν (funext hI3)
    rw [this, ← hS1]
    ring
  · have := hνmono (fun σ => aL σ ^ 2) (fun _ => 16) haL
    rwa [hνconst] at this

/-- **Size of the second moments** (before Hölder): if `𝔼⟨(R_{1,2} - q)²⟩ ≤ K₁/M` and
`𝔼⟨(R_{1,2} - q)⁴⟩ ≤ K₂/M²` then `ν(rect²) ≤ 16 K₁/M`, `ν((rect⁻)²) ≤ (16 K₁ + 16)/M`,
`ν(f*²) ≤ (512 K₁ + 512)/M` and `ν((rect⁻)⁴) ≤ (2048 K₂ + 2048)/M²`. -/
theorem sk_rect_nu_bounds (N : ℕ) (β h q K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁)
    (ν : ((Fin 4 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (hD2 : (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ≤ K₁ / ((N : ℝ) + 1))
    (hD4 : (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 4
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ≤ K₂ / ((N : ℝ) + 1) ^ 2) :
    let rect : (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
      (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ) - (σ 1 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 2 i : ℝ) - (σ 3 i : ℝ))
    let Fo : (Fin 4 → Fin N → ℤˣ) → ℝ := fun ρ =>
      (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ 0 i : ℝ) - (ρ 1 i : ℝ)) ⬝ᵥ
        fun i : Fin N => (ρ 2 i : ℝ) - (ρ 3 i : ℝ))
    let rectm : (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun σ => Fo (fun r i => σ r i.castSucc)
    let fstar : (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
      Fo (fun r i => σ r i.castSucc) *
        ((((σ 0 (Fin.last N) : ℤˣ) : ℝ) - ((σ 1 (Fin.last N) : ℤˣ) : ℝ)) *
          (((σ 2 (Fin.last N) : ℤˣ) : ℝ) - ((σ 3 (Fin.last N) : ℤˣ) : ℝ)))
    ν (fun σ => rect σ ^ 2) ≤ 16 * K₁ / ((N : ℝ) + 1) ∧
    ν (fun σ => rectm σ ^ 2) ≤ (16 * K₁ + 16) / ((N : ℝ) + 1) ∧
    ν (fun σ => fstar σ ^ 2) ≤ (512 * K₁ + 512) / ((N : ℝ) + 1) ∧
    ν (fun σ => (rectm σ ^ 2) ^ 2) ≤ (2048 * K₂ + 2048) / ((N : ℝ) + 1) ^ 2 := by
  intro rect Fo rectm fstar
  let aL : (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
    (((σ 0 (Fin.last N) : ℤˣ) : ℝ) - ((σ 1 (Fin.last N) : ℤˣ) : ℝ)) *
      (((σ 2 (Fin.last N) : ℤˣ) : ℝ) - ((σ 3 (Fin.last N) : ℤˣ) : ℝ))
  obtain ⟨hνadd, hνsmul, hνmono, hνconst⟩ := sk_replica_avg_calculus N 4 β h ν hν
  obtain ⟨-, -, hS7, hXnn, hPa0, hPa16⟩ := sk_rect_nu_structure N β h ν hν
  have hM1 : 1 ≤ (N : ℝ) + 1 := by linarith only [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hM0 : 0 < (N : ℝ) + 1 := by linarith only [hM1]
  have hI1 : ∀ σ, rect σ = rectm σ + aL σ / ((N : ℝ) + 1) := fun σ => by
    simp only [rect, rectm, Fo, aL, dotProduct, Fin.sum_univ_castSucc]
    ring
  have haL : ∀ σ, aL σ ^ 2 ≤ 16 := fun σ => sq_sign_rect_le _ _ _ _
  have hX2 : ν (fun σ => rect σ ^ 2) ≤ 16 * K₁ / ((N : ℝ) + 1) := by
    have hm := sk_rect_moment_le N β h q 2 4 (fun u₁ u₂ u₃ u₄ => by
      have := rect_sq_le u₁ u₂ u₃ u₄
      linarith only [this])
    rw [hν]
    refine hm.trans ?_
    calc _ ≤ 4 * 4 * (K₁ / ((N : ℝ) + 1)) := mul_le_mul_of_nonneg_left hD2 (by norm_num)
      _ = _ := by ring
  have hX4 : ν (fun σ => rect σ ^ 4) ≤ 256 * K₂ / ((N : ℝ) + 1) ^ 2 := by
    have hm := sk_rect_moment_le N β h q 4 64 (fun u₁ u₂ u₃ u₄ => by
      have := rect_pow_four_le u₁ u₂ u₃ u₄
      linarith only [this])
    rw [hν]
    refine hm.trans ?_
    calc _ ≤ 4 * 64 * (K₂ / ((N : ℝ) + 1) ^ 2) := mul_le_mul_of_nonneg_left hD4 (by norm_num)
      _ = _ := by ring
  have hZ1 : ν (fun σ => rectm σ ^ 2) ≤ (16 * K₁ + 16) / ((N : ℝ) + 1) := by
    rw [hS7]
    have h1 : 1 / ((N : ℝ) + 1) ^ 2 * ν (fun σ => aL σ ^ 2) ≤ 16 / ((N : ℝ) + 1) := by
      have : 1 / ((N : ℝ) + 1) ^ 2 ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le hM0 (by nlinarith only [hM1])
      calc _ ≤ 1 / ((N : ℝ) + 1) ^ 2 * 16 := mul_le_mul_of_nonneg_left hPa16 (by positivity)
        _ ≤ 1 / ((N : ℝ) + 1) * 16 := mul_le_mul_of_nonneg_right this (by norm_num)
        _ = _ := by ring
    have h2 : 0 ≤ 2 / ((N : ℝ) + 1) * ν (fun σ => rect σ ^ 2) := by positivity
    calc _ ≤ ν (fun σ => rect σ ^ 2) + 16 / ((N : ℝ) + 1) := by linarith only [h1, h2]
      _ ≤ 16 * K₁ / ((N : ℝ) + 1) + 16 / ((N : ℝ) + 1) := by linarith only [hX2]
      _ = _ := by ring
  refine ⟨hX2, hZ1, ?_, ?_⟩
  · have hpt : ∀ σ, fstar σ ^ 2 ≤ 16 * rectm σ ^ 2 := fun σ => by
      have : fstar σ ^ 2 = rectm σ ^ 2 * aL σ ^ 2 := by simp only [fstar, rectm, aL]; ring
      rw [this]
      nlinarith only [haL σ, sq_nonneg (rectm σ)]
    calc _ ≤ ν (fun σ => 16 * rectm σ ^ 2) := hνmono _ _ hpt
      _ = 16 * ν (fun σ => rectm σ ^ 2) := hνsmul _ _
      _ ≤ 16 * ((16 * K₁ + 16) / ((N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hZ1 (by norm_num)
      _ ≤ _ := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by linarith only [hK₁]) hM0.le
  · have hpt : ∀ σ, (rectm σ ^ 2) ^ 2 ≤
        8 * rect σ ^ 4 + 2048 / ((N : ℝ) + 1) ^ 4 := fun σ => by
      have h1 : rectm σ = rect σ - aL σ / ((N : ℝ) + 1) := by rw [hI1]; ring
      have h2 : (aL σ / ((N : ℝ) + 1)) ^ 4 ≤ 256 / ((N : ℝ) + 1) ^ 4 := by
        rw [div_pow]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have := haL σ
        nlinarith only [this, sq_nonneg (aL σ)]
      have h3 : ∀ a b : ℝ, (a - b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := fun a b => by
        have hu : (a - b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith only [sq_nonneg (a + b)]
        have hv : (a ^ 2 + b ^ 2) ^ 2 ≤ 2 * (a ^ 4 + b ^ 4) := by
          nlinarith only [sq_nonneg (a ^ 2 - b ^ 2)]
        calc (a - b) ^ 4 = ((a - b) ^ 2) ^ 2 := by ring
          _ ≤ (2 * (a ^ 2 + b ^ 2)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hu 2
          _ = 4 * (a ^ 2 + b ^ 2) ^ 2 := by ring
          _ ≤ 8 * (a ^ 4 + b ^ 4) := by linarith only [hv]
      rw [h1]
      calc ((rect σ - aL σ / ((N : ℝ) + 1)) ^ 2) ^ 2 =
          (rect σ - aL σ / ((N : ℝ) + 1)) ^ 4 := by ring
        _ ≤ 8 * (rect σ ^ 4 + (aL σ / ((N : ℝ) + 1)) ^ 4) := h3 _ _
        _ ≤ 8 * (rect σ ^ 4 + 256 / ((N : ℝ) + 1) ^ 4) := by linarith only [h2]
        _ = _ := by ring
    calc _ ≤ ν (fun σ => 8 * rect σ ^ 4 + 2048 / ((N : ℝ) + 1) ^ 4) := hνmono _ _ hpt
      _ = 8 * ν (fun σ => rect σ ^ 4) + 2048 / ((N : ℝ) + 1) ^ 4 := by
        have e1 := hνsmul 8 (fun σ => rect σ ^ 4)
        have e2 := hνadd (fun σ => 8 * rect σ ^ 4) (fun _ => 2048 / ((N : ℝ) + 1) ^ 4)
        rw [hνconst] at e2
        beta_reduce at e1 e2
        rw [e2, e1]
      _ ≤ 8 * (256 * K₂ / ((N : ℝ) + 1) ^ 2) + 2048 / ((N : ℝ) + 1) ^ 4 := by
        linarith only [hX4]
      _ ≤ _ := by
        have : 2048 / ((N : ℝ) + 1) ^ 4 ≤ 2048 / ((N : ℝ) + 1) ^ 2 :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity)
            (pow_le_pow_right₀ hM1 (by norm_num))
        calc _ ≤ 8 * (256 * K₂ / ((N : ℝ) + 1) ^ 2) + 2048 / ((N : ℝ) + 1) ^ 2 := by
              linarith only [this]
          _ = _ := by ring

/-- **The decoupled comparisons for the rectangular overlap**: with `ν₀` the decoupled average,
`O` the old-system average, `c₂ = q̂ - 2q + 1` and `D_k = 𝔼⟨(R_{1,2} - q)^k⟩`,
`|ν(f*) - β² c₂ ν₀((rect⁻)²)| ≤ 2304 β⁴ e^{256 β²} ν(f*²)^{1/2} D₄^{1/2}` (Eq. (1.216) and (1.237)),
`|ν((rect⁻)²) - ν₀((rect⁻)²)| ≤ 32 β² e^{144 β²} ν((rect⁻)⁴)^{1/2} D₂^{1/2}` (Eq. (1.215)), and
`|ν(a²) - 4 c₂| ≤ 512 β² e^{144 β²} 𝔼⟨|R_{1,2} - q|⟩` (Eq. (1.215) with `τ₁ = ∞` and (1.242)). -/
theorem sk_rect_nu_decoupled (N : ℕ) (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (ν : ((Fin 4 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    :
    let aL : (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
      (((σ 0 (Fin.last N) : ℤˣ) : ℝ) - ((σ 1 (Fin.last N) : ℤˣ) : ℝ)) *
        (((σ 2 (Fin.last N) : ℤˣ) : ℝ) - ((σ 3 (Fin.last N) : ℤˣ) : ℝ))
    let Fo : (Fin 4 → Fin N → ℤˣ) → ℝ := fun ρ =>
      (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ 0 i : ℝ) - (ρ 1 i : ℝ)) ⬝ᵥ
        fun i : Fin N => (ρ 2 i : ℝ) - (ρ 3 i : ℝ))
    let rectm : (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun σ => Fo (fun r i => σ r i.castSucc)
    let fstar : (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
      Fo (fun r i => σ r i.castSucc) *
        ((((σ 0 (Fin.last N) : ℤˣ) : ℝ) - ((σ 1 (Fin.last N) : ℤˣ) : ℝ)) *
          (((σ 2 (Fin.last N) : ℤˣ) : ℝ) - ((σ 3 (Fin.last N) : ℤˣ) : ℝ)))
    let c₂ : ℝ := (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1)) -
      2 * q + 1
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    ∃ ν₀ : ((Fin 4 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ,
      |ν fstar - β ^ 2 * c₂ * ν₀ (fun σ => rectm σ ^ 2)| ≤
        2304 * β ^ 4 * Real.exp (256 * β ^ 2) *
          (Real.sqrt (ν (fun σ => fstar σ ^ 2)) *
            Real.sqrt (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
              ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
                fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 4
              ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
              ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))) ∧
      |ν (fun σ => rectm σ ^ 2) - ν₀ (fun σ => rectm σ ^ 2)| ≤
        32 * β ^ 2 * Real.exp (144 * β ^ 2) *
          (Real.sqrt (ν (fun σ => (rectm σ ^ 2) ^ 2)) *
            Real.sqrt (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
              ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
                fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2
              ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
              ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))) ∧
      |ν (fun σ => aL σ ^ 2) - 4 * c₂| ≤
        32 * β ^ 2 * Real.exp (144 * β ^ 2) * 16 *
          ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
            |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
              fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q|
            ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
            ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  intro aL Fo rectm fstar c₂ Esk
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := fixedPoint_mem_Icc hfix
  have hfixz : ∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) = q := by
    rw [integral_tanh_pow_mul_z_sqrt_eq, hfix]
  have hc₂z : (∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 4 ∂(gaussianReal 0 1)) -
      2 * q + 1 = c₂ := by
    rw [integral_tanh_pow_mul_z_sqrt_eq]
  let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
    (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs N, g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
  let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) → (Fin (N + 1) → ℤˣ) → ℝ :=
    fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
  obtain ⟨ν₀, hν₀⟩ : ∃ ν₀ : ((Fin 4 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ, ∀ Φ, ν₀ Φ =
      ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Φ σ
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := ⟨_, fun _ => rfl⟩
  obtain ⟨O, hO⟩ : ∃ O : ((Fin 4 → Fin N → ℤˣ) → ℝ) → ℝ, ∀ F, O F =
      ∫ g', ∫ ρ : Fin 4 → Fin N → ℤˣ, F ρ
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := ⟨_, fun _ => rfl⟩
  refine ⟨ν₀, ?_, ?_, ?_⟩
  · have hS4 : ν₀ fstar = 0 := by
      rw [hν₀]
      exact sk_cavity_decoupled_rect_zero N β q h hfixz Fo
    have hS7' : ν₀ (fun σ => rectm σ ^ 2) = O (fun ρ => Fo ρ ^ 2) := by
      rw [hν₀, hO]
      have := sk_cavity_decoupled_endpoint_replicas N β q h (∅ : Finset (Fin 4))
        (fun ρ => Fo ρ ^ 2)
      simp only [Finset.prod_empty, mul_one, Finset.card_empty, pow_zero, integral_const,
        probReal_univ, one_smul, one_mul] at this
      exact this
    have T := sk_cavity_nu_sub_nu_zero_sub_deriv_le_two N 4 β q h hq fstar
    have L := sk_cavity_deriv_zero_rect N 4 β q h hfixz (i₁ := 0) (i₂ := 1) (j₁ := 2)
      (j₂ := 3) (by decide) (by decide) (by decide) (by decide) Fo fstar (fun σ => rfl)
    simp only [] at T L
    have hcomb : ∀ ρ : Fin 4 → Fin N → ℤˣ, Fo ρ * (((((N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (ρ 0 i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ 2 i : ℝ))) -
          (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ 0 i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ 3 i : ℝ))) -
          (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ 1 i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ 2 i : ℝ))) +
          (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ 1 i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ 3 i : ℝ))) =
        Fo ρ ^ 2 := fun ρ => by
      have : Fo ρ = (((((N + 1 : ℝ)⁻¹ *
        ((fun i : Fin N => (ρ 0 i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ 2 i : ℝ))) -
          (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ 0 i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ 3 i : ℝ))) -
          (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ 1 i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ 2 i : ℝ))) +
          (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ 1 i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ 3 i : ℝ))) := by
        simp only [Fo, dotProduct, mul_sub, sub_mul, Finset.sum_sub_distrib]
        ring
      rw [← this]
      ring
    simp only [hcomb] at L
    rw [L] at T
    rw [← hν fstar, ← hν₀ fstar, ← hO, hc₂z, ← hν (fun σ => fstar σ ^ 2)] at T
    rw [hS4, ← hS7'] at T
    simp only [Nat.cast_ofNat, sub_zero] at T
    refine T.trans (le_of_eq ?_)
    have e2 : (4 : ℝ) * (4 + 4) ^ 2 * β ^ 2 = 256 * β ^ 2 := by ring
    rw [e2]
    ring
  · have T2 := sk_cavity_nu_sub_nu_zero_le_two N 4 β q h hq (fun σ => rectm σ ^ 2)
    simp only [] at T2
    rw [← hν (fun σ => rectm σ ^ 2), ← hν₀ (fun σ => rectm σ ^ 2),
      ← hν (fun σ => (rectm σ ^ 2) ^ 2)] at T2
    simp only [Nat.cast_ofNat] at T2
    refine T2.trans (le_of_eq ?_)
    have e2 : (4 : ℝ) * (4 + 2) ^ 2 * β ^ 2 = 144 * β ^ 2 := by ring
    rw [e2]
    ring
  · have hS9 : ν₀ (fun σ => aL σ ^ 2) = 4 * c₂ := by
      rw [hν₀, ← hc₂z]
      exact sk_cavity_decoupled_rect_sq N β q h hfixz
    have T3 := sk_cavity_nu_sub_nu_zero_le_of_abs_le N 4 β q h hq (fun σ => aL σ ^ 2) (M := 16)
      (fun σ => by
        rw [abs_of_nonneg (sq_nonneg _)]
        exact sq_sign_rect_le _ _ _ _)
    simp only [] at T3
    rw [← hν (fun σ => aL σ ^ 2), ← hν₀ (fun σ => aL σ ^ 2), hS9] at T3
    simp only [Nat.cast_ofNat] at T3
    refine T3.trans (le_of_eq ?_)
    have e2 : (4 : ℝ) * (4 + 2) ^ 2 * β ^ 2 = 144 * β ^ 2 := by ring
    rw [e2]
    ring

/-- `𝔼⟨|R_{1,2} - q|⟩ ≤ (K₁ + 1) / (2 √M)` if `𝔼⟨(R_{1,2} - q)²⟩ ≤ K₁ / M`, by
`|x| ≤ (√M x² + 1/√M) / 2`. -/
theorem sk_abs_dev_le (N : ℕ) (β h q K₁ : ℝ)
    (hD2 : (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ≤ K₁ / ((N : ℝ) + 1)) :
    (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q|
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ≤
      (K₁ + 1) / (2 * Real.sqrt ((N : ℝ) + 1)) := by
  have hM0 : 0 < (N : ℝ) + 1 := by positivity
  have hs0 : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.2 hM0
  have hs2 : Real.sqrt ((N : ℝ) + 1) ^ 2 = (N : ℝ) + 1 := Real.sq_sqrt hM0.le
  set s := Real.sqrt ((N : ℝ) + 1) with hs
  have hpt : ∀ x : ℝ, |x| ≤ s / 2 * x ^ 2 + 1 / (2 * s) := fun x => by
    have key : s / 2 * x ^ 2 + 1 / (2 * s) - |x| = (s * |x| - 1) ^ 2 / (2 * s) := by
      field_simp
      rw [← sq_abs x]
      ring
    have : 0 ≤ (s * |x| - 1) ^ 2 / (2 * s) := div_nonneg (sq_nonneg _) (by positivity)
    linarith only [key, this]
  calc _ ≤ ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        (s / 2 * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2 + 1 / (2 * s))
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
        integral_integral_sk_replica_mono N 2 β h
          (Φ := fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q|)
          (Ψ := fun σ => s / 2 * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2 + 1 / (2 * s)) fun σ => hpt _
    _ = s / 2 * (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) + 1 / (2 * s) :=
        integral_integral_sk_replica_affine N 2 β h (s / 2) (1 / (2 * s)) _
    _ ≤ s / 2 * (K₁ / ((N : ℝ) + 1)) + 1 / (2 * s) := by
        have := mul_le_mul_of_nonneg_left hD2 (by positivity : 0 ≤ s / 2)
        linarith only [this]
    _ = (K₁ + 1) / (2 * s) := by
        rw [← hs2]
        field_simp

/-- **Proposition 1.8.5, with explicit error terms (before choosing the constants).**  Let
`M = N + 1`, `c₂ = q̂ - 2q + 1` and `λ = β² c₂`.  If `𝔼⟨(R_{1,2} - q)²⟩ ≤ K₁ / M` and
`𝔼⟨(R_{1,2} - q)⁴⟩ ≤ K₂ / M²` then `ν(rect²)` differs from `4 c₂ / (M (1 - λ))` by at most
`4/3 (e₁ + e₂/4 + e₃/(2M) + 4/M² + e₄/M)`, where the `e_i` are the error terms of Eq. (1.216),
Eq. (1.215) for `rect⁻²`, the size of `ν(rect²)`, and Eq. (1.215) for `a_N²`. -/
theorem sk_rect_second_moment_aux (N : ℕ) (β q h K₁ K₂ : ℝ) (hβ : 4 * β ^ 2 < 1)
    (hK₁ : 0 ≤ K₁)
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
  intro Esk c₂ hD2 hD4
  have hc₂ : c₂ ∈ Set.Icc (0 : ℝ) 1 := by
    have := tanh_fourth_sub_two_add_one_mem_Icc (β * Real.sqrt q) h
    rwa [hfix] at this
  have hM1 : 1 ≤ (N : ℝ) + 1 := by linarith only [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hM0 : 0 < (N : ℝ) + 1 := by linarith only [hM1]
  have hlam0 : 0 ≤ β ^ 2 * c₂ := mul_nonneg (sq_nonneg _) hc₂.1
  have hlam1 : β ^ 2 * c₂ ≤ 1 / 4 := by nlinarith only [hc₂.2, sq_nonneg β, hβ]
  obtain ⟨ν, hν⟩ : ∃ ν : ((Fin 4 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ, ∀ Φ, ν Φ =
      ∫ g, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Φ σ
        ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := ⟨_, fun _ => rfl⟩
  let aL : (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
    (((σ 0 (Fin.last N) : ℤˣ) : ℝ) - ((σ 1 (Fin.last N) : ℤˣ) : ℝ)) *
      (((σ 2 (Fin.last N) : ℤˣ) : ℝ) - ((σ 3 (Fin.last N) : ℤˣ) : ℝ))
  let rect : (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
    (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ) - (σ 1 i : ℝ)) ⬝ᵥ
      fun i : Fin (N + 1) => (σ 2 i : ℝ) - (σ 3 i : ℝ))
  let Fo : (Fin 4 → Fin N → ℤˣ) → ℝ := fun ρ =>
    (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ 0 i : ℝ) - (ρ 1 i : ℝ)) ⬝ᵥ
      fun i : Fin N => (ρ 2 i : ℝ) - (ρ 3 i : ℝ))
  let rectm : (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun σ => Fo (fun r i => σ r i.castSucc)
  let fstar : (Fin 4 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
    Fo (fun r i => σ r i.castSucc) *
      ((((σ 0 (Fin.last N) : ℤˣ) : ℝ) - ((σ 1 (Fin.last N) : ℤˣ) : ℝ)) *
        (((σ 2 (Fin.last N) : ℤˣ) : ℝ) - ((σ 3 (Fin.last N) : ℤˣ) : ℝ)))
  obtain ⟨hS1, hS2, hS7, hXnn, hPa0, hPa16⟩ := sk_rect_nu_structure N β h ν hν
  obtain ⟨hX2, hZ1, hfs, hZ4⟩ := sk_rect_nu_bounds N β h q K₁ K₂ hK₁ ν hν hD2 hD4
  obtain ⟨ν₀, hC1, hC2, hC3⟩ := sk_rect_nu_decoupled N β h q hfix ν hν
  have hD1 := sk_abs_dev_le N β h q K₁ hD2
  have hs0 : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.2 hM0
  have hβ2 : 0 ≤ 32 * β ^ 2 * Real.exp (144 * β ^ 2) := by positivity
  have hβ4 : 0 ≤ 2304 * β ^ 4 * Real.exp (256 * β ^ 2) := by positivity
  have key := second_moment_assembly (X := ν (fun σ => rect σ ^ 2)) (Pa := ν (fun σ => aL σ ^ 2))
    (Pf := ν fstar) (Z0 := ν₀ (fun σ => rectm σ ^ 2)) (Z1 := ν (fun σ => rectm σ ^ 2))
    (M := (N : ℝ) + 1) (lam := β ^ 2 * c₂) (c2 := c₂)
    (e1 := 2304 * β ^ 4 * Real.exp (256 * β ^ 2) *
        (Real.sqrt ((512 * K₁ + 512) / ((N : ℝ) + 1)) * Real.sqrt (K₂ / ((N : ℝ) + 1) ^ 2)))
    (e2 := 32 * β ^ 2 * Real.exp (144 * β ^ 2) *
        (Real.sqrt ((2048 * K₂ + 2048) / ((N : ℝ) + 1) ^ 2) *
          Real.sqrt (K₁ / ((N : ℝ) + 1))))
    (e3 := 16 * K₁ / ((N : ℝ) + 1))
    (e4 := 32 * β ^ 2 * Real.exp (144 * β ^ 2) * 16 *
        ((K₁ + 1) / (2 * Real.sqrt ((N : ℝ) + 1))))
    hM1 hlam0 hlam1 (by rw [abs_of_nonneg hPa0]; exact hPa16)
    (by rw [hS1, hS2]; ring)
    (by
      refine hC1.trans ?_
      refine mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt hfs)
        (Real.sqrt_le_sqrt hD4) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hβ4)
    (by
      rw [abs_sub_comm]
      refine hC2.trans ?_
      refine mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt hZ4)
        (Real.sqrt_le_sqrt hD2) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hβ2)
    (by rw [hS7]; ring)
    (by rw [abs_of_nonneg hXnn]; exact hX2)
    (by
      refine hC3.trans ?_
      exact mul_le_mul_of_nonneg_left hD1 (by positivity))
  rw [hν (fun σ => rect σ ^ 2)] at key
  refine key.trans (le_of_eq ?_)
  ring

/-- The elementary estimate that turns the explicit error terms of
`sk_rect_second_moment_aux` into `K / s³`, `s = √(N+1)`. -/
theorem rect_error_arith {β β₀ K₁ K₂ s : ℝ} (hs : 1 ≤ s) (hβ : β ^ 2 ≤ β₀ ^ 2)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) :
    4 / 3 * (2304 * β ^ 4 * Real.exp (256 * β ^ 2) *
        (Real.sqrt ((512 * K₁ + 512) / s ^ 2) * Real.sqrt (K₂ / (s ^ 2) ^ 2)) +
      32 * β ^ 2 * Real.exp (144 * β ^ 2) *
        (Real.sqrt ((2048 * K₂ + 2048) / (s ^ 2) ^ 2) * Real.sqrt (K₁ / s ^ 2)) / 4 +
      16 * K₁ / s ^ 2 / (2 * s ^ 2) + 4 / (s ^ 2) ^ 2 +
      32 * β ^ 2 * Real.exp (144 * β ^ 2) * 16 * ((K₁ + 1) / (2 * s)) / s ^ 2) ≤
    (4 / 3 * (2304 * β₀ ^ 4 * Real.exp (256 * β₀ ^ 2) * Real.sqrt (512 * K₁ + 512) *
        Real.sqrt K₂ + 8 * β₀ ^ 2 * Real.exp (144 * β₀ ^ 2) * Real.sqrt (2048 * K₂ + 2048) *
        Real.sqrt K₁ + 8 * K₁ + 4 +
        256 * β₀ ^ 2 * Real.exp (144 * β₀ ^ 2) * (K₁ + 1))) / s ^ 3 := by
  have hs0 : 0 < s := by linarith
  have hb2 : 0 ≤ β ^ 2 := sq_nonneg _
  have hb4 : β ^ 4 ≤ β₀ ^ 4 := by
    have : β ^ 4 = (β ^ 2) ^ 2 := by ring
    have h2 : β₀ ^ 4 = (β₀ ^ 2) ^ 2 := by ring
    rw [this, h2]
    exact pow_le_pow_left₀ hb2 hβ 2
  have e1 : Real.exp (256 * β ^ 2) ≤ Real.exp (256 * β₀ ^ 2) :=
    Real.exp_le_exp.2 (by linarith)
  have e2 : Real.exp (144 * β ^ 2) ≤ Real.exp (144 * β₀ ^ 2) :=
    Real.exp_le_exp.2 (by linarith)
  have sq1 : Real.sqrt ((512 * K₁ + 512) / s ^ 2) = Real.sqrt (512 * K₁ + 512) / s := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq hs0.le]
  have sq2 : Real.sqrt (K₂ / (s ^ 2) ^ 2) = Real.sqrt K₂ / s ^ 2 := by
    rw [Real.sqrt_div hK₂, Real.sqrt_sq (by positivity)]
  have sq3 : Real.sqrt ((2048 * K₂ + 2048) / (s ^ 2) ^ 2) =
      Real.sqrt (2048 * K₂ + 2048) / s ^ 2 := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq (by positivity)]
  have sq4 : Real.sqrt (K₁ / s ^ 2) = Real.sqrt K₁ / s := by
    rw [Real.sqrt_div hK₁, Real.sqrt_sq hs0.le]
  rw [sq1, sq2, sq3, sq4]
  have s3 : 0 < s ^ 3 := by positivity
  have hs3 : s ^ 3 ≤ s ^ 4 := pow_le_pow_right₀ hs (by norm_num)
  have T1 : 2304 * β ^ 4 * Real.exp (256 * β ^ 2) *
      (Real.sqrt (512 * K₁ + 512) / s * (Real.sqrt K₂ / s ^ 2)) ≤
      2304 * β₀ ^ 4 * Real.exp (256 * β₀ ^ 2) * Real.sqrt (512 * K₁ + 512) *
        Real.sqrt K₂ / s ^ 3 := by
    have : Real.sqrt (512 * K₁ + 512) / s * (Real.sqrt K₂ / s ^ 2) =
        Real.sqrt (512 * K₁ + 512) * Real.sqrt K₂ / s ^ 3 := by field_simp
    rw [this, ← mul_div_assoc]
    refine div_le_div_of_nonneg_right ?_ s3.le
    have h0 : 0 ≤ Real.sqrt (512 * K₁ + 512) * Real.sqrt K₂ := by positivity
    calc _ ≤ 2304 * β₀ ^ 4 * Real.exp (256 * β₀ ^ 2) *
          (Real.sqrt (512 * K₁ + 512) * Real.sqrt K₂) := by
          apply mul_le_mul_of_nonneg_right _ h0
          exact mul_le_mul (mul_le_mul_of_nonneg_left hb4 (by norm_num)) e1 (by positivity)
            (by positivity)
      _ = _ := by ring
  have T2 : 32 * β ^ 2 * Real.exp (144 * β ^ 2) *
      (Real.sqrt (2048 * K₂ + 2048) / s ^ 2 * (Real.sqrt K₁ / s)) / 4 ≤
      8 * β₀ ^ 2 * Real.exp (144 * β₀ ^ 2) * Real.sqrt (2048 * K₂ + 2048) *
        Real.sqrt K₁ / s ^ 3 := by
    have : Real.sqrt (2048 * K₂ + 2048) / s ^ 2 * (Real.sqrt K₁ / s) =
        Real.sqrt (2048 * K₂ + 2048) * Real.sqrt K₁ / s ^ 3 := by field_simp
    rw [this]
    have h0 : 0 ≤ Real.sqrt (2048 * K₂ + 2048) * Real.sqrt K₁ := by positivity
    have h1 : 32 * β ^ 2 * Real.exp (144 * β ^ 2) ≤ 32 * β₀ ^ 2 * Real.exp (144 * β₀ ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hβ (by norm_num)) e2 (by positivity) (by positivity)
    calc _ = 32 * β ^ 2 * Real.exp (144 * β ^ 2) *
          (Real.sqrt (2048 * K₂ + 2048) * Real.sqrt K₁) / s ^ 3 / 4 := by ring
      _ ≤ 32 * β₀ ^ 2 * Real.exp (144 * β₀ ^ 2) *
          (Real.sqrt (2048 * K₂ + 2048) * Real.sqrt K₁) / s ^ 3 / 4 := by
          gcongr
      _ = _ := by ring
  have T3 : 16 * K₁ / s ^ 2 / (2 * s ^ 2) ≤ 8 * K₁ / s ^ 3 := by
    have : 16 * K₁ / s ^ 2 / (2 * s ^ 2) = 8 * K₁ / s ^ 4 := by field_simp; ring
    rw [this]
    exact div_le_div_of_nonneg_left (by positivity) s3 hs3
  have T4 : 4 / (s ^ 2) ^ 2 ≤ 4 / s ^ 3 := by
    have : (s ^ 2) ^ 2 = s ^ 4 := by ring
    rw [this]
    exact div_le_div_of_nonneg_left (by norm_num) s3 hs3
  have T5 : 32 * β ^ 2 * Real.exp (144 * β ^ 2) * 16 * ((K₁ + 1) / (2 * s)) / s ^ 2 ≤
      256 * β₀ ^ 2 * Real.exp (144 * β₀ ^ 2) * (K₁ + 1) / s ^ 3 := by
    have : 32 * β ^ 2 * Real.exp (144 * β ^ 2) * 16 * ((K₁ + 1) / (2 * s)) / s ^ 2 =
        256 * β ^ 2 * Real.exp (144 * β ^ 2) * (K₁ + 1) / s ^ 3 := by field_simp; ring
    rw [this]
    refine div_le_div_of_nonneg_right ?_ s3.le
    have h1 : 256 * β ^ 2 * Real.exp (144 * β ^ 2) ≤ 256 * β₀ ^ 2 * Real.exp (144 * β₀ ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hβ (by norm_num)) e2 (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right h1 (by linarith)
  have : (4 / 3 * (2304 * β₀ ^ 4 * Real.exp (256 * β₀ ^ 2) * Real.sqrt (512 * K₁ + 512) *
        Real.sqrt K₂ + 8 * β₀ ^ 2 * Real.exp (144 * β₀ ^ 2) * Real.sqrt (2048 * K₂ + 2048) *
        Real.sqrt K₁ + 8 * K₁ + 4 + 256 * β₀ ^ 2 * Real.exp (144 * β₀ ^ 2) * (K₁ + 1))) / s ^ 3 =
      4 / 3 * (2304 * β₀ ^ 4 * Real.exp (256 * β₀ ^ 2) * Real.sqrt (512 * K₁ + 512) *
        Real.sqrt K₂ / s ^ 3 + 8 * β₀ ^ 2 * Real.exp (144 * β₀ ^ 2) * Real.sqrt (2048 * K₂ + 2048) *
        Real.sqrt K₁ / s ^ 3 + 8 * K₁ / s ^ 3 + 4 / s ^ 3 +
        256 * β₀ ^ 2 * Real.exp (144 * β₀ ^ 2) * (K₁ + 1) / s ^ 3) := by ring
  rw [this]
  gcongr

/-- **Talagrand's Proposition 1.8.5 (Eq. (1.238))** for the `(N+1)`-spin system: for
`|β| ≤ β₀ < 1/2` and `q` the fixed point,
`ν(((σ¹ - σ²)·(σ³ - σ⁴)/(N+1))²) = 4 c₂ / ((N+1) (1 - β² c₂)) + O((N+1)^{-3/2})`,
where `c₂ = 1 - 2q + q̂ = 𝔼 ch⁻⁴ (β z √q + h)` and the error is bounded by `K / (N+1)^{3/2}`
with `K` independent of `N`, `β`, `q`. -/
theorem sk_rect_second_moment (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (h : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β q : ℝ), |β| ≤ β₀ →
      (∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q) →
      ∀ N : ℕ,
      |(∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ,
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ) - (σ 1 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 2 i : ℝ) - (σ 3 i : ℝ))) ^ 2
          ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
        4 * ((∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1)) - 2 * q + 1) /
          (((N : ℝ) + 1) * (1 - β ^ 2 * ((∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4
            ∂(gaussianReal 0 1)) - 2 * q + 1)))| ≤
      K / Real.sqrt ((N : ℝ) + 1) ^ 3 := by
  obtain ⟨K₁, hK₁, hM1⟩ := sk_dev_moment_le β₀ hβ₀ 1
  obtain ⟨K₂, hK₂, hM2⟩ := sk_dev_moment_le β₀ hβ₀ 2
  set C : ℝ := 4 / 3 * (2304 * β₀ ^ 4 * Real.exp (256 * β₀ ^ 2) * Real.sqrt (512 * K₁ + 512) *
        Real.sqrt K₂ + 8 * β₀ ^ 2 * Real.exp (144 * β₀ ^ 2) * Real.sqrt (2048 * K₂ + 2048) *
        Real.sqrt K₁ + 8 * K₁ + 4 + 256 * β₀ ^ 2 * Real.exp (144 * β₀ ^ 2) * (K₁ + 1)) with hC
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C + 1, by positivity, fun β q hβ hfix N => ?_⟩
  have hβ2 : β ^ 2 ≤ β₀ ^ 2 := by
    rw [← sq_abs β]
    exact pow_le_pow_left₀ (abs_nonneg _) hβ 2
  have hβ4 : 4 * β ^ 2 < 1 := by linarith
  have hD2 := hM1 β h q hfix hβ2 N
  have hD4 := hM2 β h q hfix hβ2 N
  simp only [mul_one, pow_one] at hD2
  have hD4' : (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 4
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ≤ K₂ / ((N : ℝ) + 1) ^ 2 :=
    hD4
  have haux := sk_rect_second_moment_aux N β q h K₁ K₂ hβ4 hK₁.le hfix hD2 hD4'
  have hM0 : 0 < (N : ℝ) + 1 := by positivity
  have hs1 : 1 ≤ Real.sqrt ((N : ℝ) + 1) := by
    rw [Real.one_le_sqrt]
    linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hs2 : Real.sqrt ((N : ℝ) + 1) ^ 2 = (N : ℝ) + 1 := Real.sq_sqrt hM0.le
  have harith := rect_error_arith (β := β) (β₀ := β₀) (K₁ := K₁) (K₂ := K₂) hs1 hβ2 hK₁.le hK₂.le
  rw [hs2] at harith
  refine haux.trans (harith.trans ?_)
  have hs3 : 0 < Real.sqrt ((N : ℝ) + 1) ^ 3 := by positivity
  exact div_le_div_of_nonneg_right (by linarith) hs3.le

end SpinGlasses
