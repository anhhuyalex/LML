/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapContraction
public import LeanMachineLearning.SpinGlasses.SKCavityDomination

/-!
# Higher moments of the overlap (Talagrand's Proposition 1.6.7)

Induction on `k` for `ν((R - q)^(2k)) ≤ (64 k / (N+1))^k`. The step reuses the contraction
argument of Proposition 1.6.6 (`sk_overlap_pow_le_two_odd_part`): the decoupled average of
`((D + x)^(2k+1) - (D - x)^(2k+1)) / 2`, with `D = R⁻ - q` and `x = 1/(N+1)`, is dominated by
`(2k+1) x (|R - q| + 2x)^(2k)` (a mean-value estimate), compared with `ν` through Lemma 1.6.4 and
split by a weighted Young inequality into the previous moment and a term of order `x^(2k)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- The numerical inequality closing the induction step of Proposition 1.6.7. -/
theorem sk_overlap_moment_arith {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : 0 < x)
    (hxk : 16 * ((k : ℝ) + 1) * x ≤ 1) :
    4 * (2 * (k : ℝ) + 1) * x *
        (2 * (64 * (k : ℝ) * x) ^ k + (1 + 4 * (k : ℝ)) ^ (2 * k - 1) * (2 * x) ^ (2 * k)) ≤
      (64 * ((k : ℝ) + 1) * x) ^ (k + 1) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha0 : 0 ≤ 10 * (k : ℝ) * x := by positivity
  have ha1 : 10 * (k : ℝ) * x ≤ 1 := by nlinarith
  have h2x : 2 * x ≤ 1 := by nlinarith
  have hsmall : (1 + 4 * (k : ℝ)) ^ (2 * k - 1) * (2 * x) ^ (2 * k) ≤ (64 * (k : ℝ) * x) ^ k := by
    have h5 : (1 + 4 * (k : ℝ)) ^ (2 * k - 1) ≤ (5 * (k : ℝ)) ^ (2 * k - 1) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have hsplit : (2 * x) ^ (2 * k) = (2 * x) ^ (2 * k - 1) * (2 * x) := by
      rw [← pow_succ]
      congr 1
      omega
    calc (1 + 4 * (k : ℝ)) ^ (2 * k - 1) * (2 * x) ^ (2 * k)
        ≤ (5 * (k : ℝ)) ^ (2 * k - 1) * ((2 * x) ^ (2 * k - 1) * (2 * x)) := by
          rw [hsplit]
          exact mul_le_mul_of_nonneg_right h5 (by positivity)
      _ = (10 * (k : ℝ) * x) ^ (2 * k - 1) * (2 * x) := by
          rw [← mul_assoc, ← mul_pow]
          ring_nf
      _ ≤ (10 * (k : ℝ) * x) ^ (2 * k - 1) * 1 :=
          mul_le_mul_of_nonneg_left h2x (by positivity)
      _ ≤ (10 * (k : ℝ) * x) ^ k := by
          rw [mul_one]
          exact pow_le_pow_of_le_one ha0 ha1 (by omega)
      _ ≤ (64 * (k : ℝ) * x) ^ k :=
          pow_le_pow_left₀ ha0 (by nlinarith) _
  have htw : (64 * (k : ℝ) * x) ^ k ≤ (64 * ((k : ℝ) + 1) * x) ^ k :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) _
  have hw0 : 0 ≤ (64 * ((k : ℝ) + 1) * x) ^ k := by positivity
  calc _ ≤ 4 * (2 * (k : ℝ) + 1) * x * (3 * (64 * ((k : ℝ) + 1) * x) ^ k) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
    _ ≤ (64 * ((k : ℝ) + 1) * x) ^ (k + 1) := by
        rw [pow_succ]
        have : 12 * (2 * (k : ℝ) + 1) * x ≤ 64 * ((k : ℝ) + 1) * x := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right this hw0]

/-- The overlap deviation `R - q` of two `(N+1)`-spin configurations has modulus at most `2`. -/
theorem abs_sk_overlap_sub_le_two (N : ℕ) (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (a b : Fin (N + 1) → ℤˣ) :
    |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (a i : ℝ)) ⬝ᵥ
      fun i : Fin (N + 1) => (b i : ℝ)) - q| ≤ 2 := by
  have hN : (0 : ℝ) < (N + 1 : ℝ) := by positivity
  have h1 : |(fun i : Fin (N + 1) => (a i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (b i : ℝ)| ≤
      (N + 1 : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    simp only [abs_mul, abs_units_cast_eq_one, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    exact le_rfl
  have h2 : |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (a i : ℝ)) ⬝ᵥ
      fun i : Fin (N + 1) => (b i : ℝ))| ≤ 1 := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hN)]
    calc _ ≤ (N + 1 : ℝ)⁻¹ * (N + 1 : ℝ) := mul_le_mul_of_nonneg_left h1 (inv_pos.2 hN).le
      _ = 1 := inv_mul_cancel₀ hN.ne'
  calc _ ≤ _ := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add h2 (by rw [abs_of_nonneg hq.1]; exact hq.2)
    _ = 2 := by norm_num

/-- **Induction step of Talagrand's Proposition 1.6.7.** If the `2k`-th moment of `R - q` is at
most `(64 k x)^k` (`x = 1/(N+1)`) and `16 (k+1) x ≤ 1`, then the `(2k+2)`-th moment is at most
`(64 (k+1) x)^(k+1)`. -/
theorem sk_overlap_moment_step (N : ℕ) (β q h : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hsmall : 16 * β ^ 2 * Real.exp (64 * β ^ 2) ≤ 1 / 2) {k : ℕ} (hk : 1 ≤ k)
    (hxk : 16 * ((k : ℝ) + 1) * (N + 1 : ℝ)⁻¹ ≤ 1) :
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    (∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ (2 * k)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
        (64 * (k : ℝ) * (N + 1 : ℝ)⁻¹) ^ k) →
    ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ (2 * k + 2)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
        (64 * ((k : ℝ) + 1) * (N + 1 : ℝ)⁻¹) ^ (k + 1) := by
  intro Esk hVk
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
  have hEm (a : Fin (N + 1) → ℤˣ) :
      Measurable (fun p : (FinPairs N → ℝ) × ((Fin N → ℝ) × ℝ) => E (π / 2) p.1 p.2 a) := by
    dsimp [E, B]
    fun_prop
  let ν : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun Φ =>
    ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
  let ν₀ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun Φ =>
    ∫ g', ∫ ω : (Fin N → ℝ) × ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E (π / 2) g' ω))
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
  let x : ℝ := (N + 1 : ℝ)⁻¹
  have hx : 0 < x := inv_pos.2 (by positivity)
  let Ab : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
    (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
      fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q
  let Dt : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
    (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ 0 i.castSucc : ℝ)) ⬝ᵥ
      fun i : Fin N => (σ 1 i.castSucc : ℝ)) - q
  let n : ℝ := 2 * (k : ℝ) + 1
  let Tf : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
    ((Dt σ + x) ^ (2 * k + 1) - (Dt σ - x) ^ (2 * k + 1)) / 2
  let Gf : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ := fun σ => n * x * (|Ab σ| + 2 * x) ^ (2 * k)
  have hn : 0 ≤ n := by positivity
  -- pointwise estimates
  have hDA : ∀ σ, |Dt σ| + x ≤ |Ab σ| + 2 * x := fun σ => by
    have hA : Ab σ = Dt σ + (σ 0 (Fin.last N) : ℝ) * (σ 1 (Fin.last N) : ℝ) * x := by
      simp only [Ab, Dt, x]
      rw [sk_overlap_succ_eq_cavity N (σ 0) (σ 1)]
      ring
    have he : |(σ 0 (Fin.last N) : ℝ) * (σ 1 (Fin.last N) : ℝ) * x| = x := by
      rw [abs_mul, abs_mul, abs_units_cast_eq_one, abs_units_cast_eq_one, one_mul, one_mul,
        abs_of_pos hx]
    have : |Dt σ| ≤ |Ab σ| + x := by
      calc |Dt σ| = |Ab σ - (σ 0 (Fin.last N) : ℝ) * (σ 1 (Fin.last N) : ℝ) * x| := by
            rw [hA]; ring_nf
        _ ≤ |Ab σ| + |(σ 0 (Fin.last N) : ℝ) * (σ 1 (Fin.last N) : ℝ) * x| := abs_sub _ _
        _ = |Ab σ| + x := by rw [he]
    linarith
  have hTnn : ∀ σ, 0 ≤ Tf σ := fun σ =>
    (pow_add_sub_pow_sub_le (n := 2 * k + 1) ⟨k, rfl⟩ (Dt σ) hx.le).1
  have hTG : ∀ σ, |Tf σ| ≤ Gf σ := fun σ => by
    rw [abs_of_nonneg (hTnn σ)]
    have h1 := (pow_add_sub_pow_sub_le (n := 2 * k + 1) ⟨k, rfl⟩ (Dt σ) hx.le).2
    refine h1.trans ?_
    have hnc : ((2 * k + 1 : ℕ) : ℝ) = n := by
      simp only [n]
      push_cast
      ring
    simp only [Nat.add_sub_cancel, Gf, hnc, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (hDA σ) _) hx.le) hn
  have hGnn : ∀ σ, 0 ≤ Gf σ := fun σ => by positivity
  have hA : ν₀ Tf ≤ ν₀ Gf :=
    (le_abs_self _).trans (abs_integral_nested_gibbs_le
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
      ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) (E (π / 2)) hEm hTG)
  have hG0 : 0 ≤ ν₀ Gf := integral_nonneg fun _ => integral_nonneg fun _ =>
    integral_nonneg hGnn
  have hB : ν₀ Gf ≤ Real.exp (4 * ((2 : ℕ) : ℝ) ^ 2 * β ^ 2) * ν Gf := by
    have := sk_cavity_path_square_le_exp_mul N 2 β q h hq Gf hGnn 0 ⟨le_rfl, zero_le_one⟩
    dsimp only at this
    rw [Real.sqrt_zero, Real.arccos_zero] at this
    exact this
  have hexp : Real.exp (4 * ((2 : ℕ) : ℝ) ^ 2 * β ^ 2) ≤ 2 := by
    have h16 : 16 * β ^ 2 ≤ 1 / 2 :=
      (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))).trans hsmall
    refine (Real.exp_le_exp.2 ?_).trans Real.exp_half_le_two
    norm_num
    linarith
  have hGY : ∀ σ, Gf σ ≤ (2 * n * x) * Ab σ ^ (2 * k) +
      n * x * ((1 + 4 * (k : ℝ)) ^ (2 * k - 1) * (2 * x) ^ (2 * k)) := fun σ => by
    have := abs_add_pow_two_mul_le hk (Ab σ) (b := 2 * x) (by positivity)
    have := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ n * x)
    simp only [Gf]
    linarith
  have hC : ν Gf ≤ (2 * n * x) * ν (fun σ => Ab σ ^ (2 * k)) +
      n * x * ((1 + 4 * (k : ℝ)) ^ (2 * k - 1) * (2 * x) ^ (2 * k)) :=
    (integral_integral_sk_replica_mono N 2 β h hGY).trans_eq
      (integral_integral_sk_replica_affine N 2 β h _ _ (fun σ => Ab σ ^ (2 * k)))
  have hGnu : 0 ≤ ν Gf := integral_nonneg fun _ => integral_nonneg hGnn
  have h1 := sk_overlap_pow_le_two_odd_part N β q h hq hfix hsmall k
  dsimp only at h1
  have h1' : ν (fun σ => Ab σ ^ (2 * k + 2)) ≤ 2 * ((1 - q ^ 2) * ν₀ Tf) := h1
  have hq2 : 0 ≤ 1 - q ^ 2 := by nlinarith [hq.1, hq.2]
  have hq3 : 1 - q ^ 2 ≤ 1 := by nlinarith [hq.1, hq.2]
  have h2 : (1 - q ^ 2) * ν₀ Tf ≤ 2 * ν Gf :=
    calc _ ≤ (1 - q ^ 2) * ν₀ Gf := mul_le_mul_of_nonneg_left hA hq2
      _ ≤ ν₀ Gf := mul_le_of_le_one_left hG0 hq3
      _ ≤ Real.exp (4 * ((2 : ℕ) : ℝ) ^ 2 * β ^ 2) * ν Gf := hB
      _ ≤ 2 * ν Gf := mul_le_mul_of_nonneg_right hexp hGnu
  have hVk' : ν (fun σ => Ab σ ^ (2 * k)) ≤ (64 * (k : ℝ) * x) ^ k := hVk
  have harith := sk_overlap_moment_arith hk hx hxk
  have hnx : 0 ≤ n * x := by positivity
  change ν (fun σ => Ab σ ^ (2 * k + 2)) ≤ _
  calc _ ≤ 2 * ((1 - q ^ 2) * ν₀ Tf) := h1'
    _ ≤ 2 * (2 * ν Gf) := by linarith
    _ ≤ 4 * ((2 * n * x) * (64 * (k : ℝ) * x) ^ k +
        n * x * ((1 + 4 * (k : ℝ)) ^ (2 * k - 1) * (2 * x) ^ (2 * k))) := by
        have := mul_le_mul_of_nonneg_left hVk' (by positivity : 0 ≤ 2 * n * x)
        linarith
    _ = 4 * (2 * (k : ℝ) + 1) * x * (2 * (64 * (k : ℝ) * x) ^ k +
        (1 + 4 * (k : ℝ)) ^ (2 * k - 1) * (2 * x) ^ (2 * k)) := by
        simp only [n]
        ring
    _ ≤ _ := harith

/-- **Talagrand's Proposition 1.6.7** (for the `(N+1)`-spin system). If
`16 β² exp (64 β²) ≤ 1/2` and `q` solves the fixed-point equation, then for every `k ≥ 1`,
`ν((R_{1,2} - q)^(2k)) ≤ (64 k / (N + 1))^k`. -/
theorem sk_overlap_moment_le (N : ℕ) (β q h : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hsmall : 16 * β ^ 2 * Real.exp (64 * β ^ 2) ≤ 1 / 2) (k : ℕ) (hk : 1 ≤ k) :
    let Esk : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g a =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
    ∫ g, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ (2 * k)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (Esk g))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
        (64 * (k : ℝ) / (N + 1 : ℝ)) ^ k := by
  intro Esk
  have hx : 0 < (N + 1 : ℝ)⁻¹ := inv_pos.2 (by positivity)
  have hdiv : ∀ c : ℝ, c / (N + 1 : ℝ) = c * (N + 1 : ℝ)⁻¹ := fun c => div_eq_mul_inv _ _
  simp only [hdiv]
  induction k, hk using Nat.le_induction with
  | base =>
    have h1 := sk_overlap_sq_le_two_div N β q h hq hfix hsmall
    dsimp only at h1 ⊢
    simp only [mul_one, Nat.cast_one, pow_one]
    refine h1.trans ?_
    rw [div_eq_mul_inv]
    nlinarith
  | succ k hk ih =>
    by_cases hxk : 16 * ((k : ℝ) + 1) * (N + 1 : ℝ)⁻¹ ≤ 1
    · have := sk_overlap_moment_step N β q h hq hfix hsmall hk hxk ih
      push_cast
      exact this
    · have hxk := not_le.1 hxk
      have hpt : ∀ σ : Fin 2 → Fin (N + 1) → ℤˣ,
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ (2 * (k + 1)) ≤
            0 * (fun _ : Fin 2 → Fin (N + 1) → ℤˣ => (1 : ℝ)) σ + 4 ^ (k + 1) := fun σ => by
        have h2 := abs_le.1 (abs_sk_overlap_sub_le_two N q hq (σ 0) (σ 1))
        rw [pow_mul, zero_mul, zero_add]
        exact pow_le_pow_left₀ (sq_nonneg _) (by nlinarith [h2.1, h2.2]) _
      have h3 := (integral_integral_sk_replica_mono N 2 β h hpt).trans_eq
        (integral_integral_sk_replica_affine N 2 β h 0 (4 ^ (k + 1))
          (fun _ : Fin 2 → Fin (N + 1) → ℤˣ => (1 : ℝ)))
      rw [zero_mul, zero_add] at h3
      refine h3.trans ?_
      push_cast
      exact pow_le_pow_left₀ (by norm_num) (by nlinarith) _

end SpinGlasses
