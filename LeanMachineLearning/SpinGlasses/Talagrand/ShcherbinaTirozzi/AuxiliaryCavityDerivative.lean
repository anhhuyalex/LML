/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaConfinedSteinBound
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.CavityDerivative

/-!
# The Shcherbina--Tirozzi model: the derivative along the auxiliary cavity path

For a system on `ℝ^(N+1)` with `M` old constraints and one isolated constraint, the auxiliary path
replaces the isolated field `S_{t}(σ)` by `S_v = √v S_t(σ) + √(1 - v) (√q z + √(ρ - q) ξ)`
(Talagrand, *Spin Glasses*, Vol. I, Eqs. (3.89)--(3.90)). The shared Gaussians are the row
`g_M = w ∘ Sum.inl` of the isolated constraint and `z = w (Sum.inr ())`; each replica carries its
own `ξ`.

This file proves Lemma 3.2.8: the derivative in `v` of
`ν_{t,v} (f(σ) ∏_r ψ_r (S_v^r))` is bounded by the averages of `|f|` times the deviations of the
overlaps `(N + 1)⁻¹ (∑_{i < N} σᵃ_i σᵇ_i + t σᵃ_N σᵇ_N)` from `ρ` (if `a = b`) or `q`
(if `a ≠ b`). The overlap carries the factor `t` on the last spin, which is what the covariance
of the field is; Eq. (3.96) is printed with the full overlap and an error `ν (|f|) / N`.

## Main declarations

* `SpinGlasses.exists_hasDerivAt_shcherbinaTirozziAuxCavity_abs_le`: Lemma 3.2.8.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function Set
open scoped NNReal Topology Matrix

namespace SpinGlasses

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

universe u

variable {N M : ℕ} {R : Type u} [Fintype R]

/-- **Talagrand, Lemma 3.2.8**: along the auxiliary cavity path, for any factors `ψ r` with two
bounded derivatives (for instance `1`, `u'`, `u'' + u'²`) and any observable `f` of the spins of
polynomial growth, `v ↦ ν_{t,v} (f ∏_r ψ_r (S_v^r))` is differentiable on `(0, 1)` and its
derivative is at most `(n + 1)² B ^ (n + 2)` times
`∑_{a, b} ν_{t,v} (|f| |R^t_{a,b} - (ρ if a = b, else q)|)`, where `n = |R|`, the replicas `a, b`
run over `R` and two fresh ones, and `B` is `1` plus the sum of the bounds on `ψ`, `ψ'`, `ψ''`,
`u'`, `u''`. The constant does not depend on `N`, `M`, `κ`, `h` or `t`. -/
theorem exists_hasDerivAt_shcherbinaTirozziAuxCavity_abs_le [DecidableEq R] {κ h : ℝ}
    (hκ : 0 < κ) (r : ℝ≥0) {rBar : ℝ} (hrr : rBar ≤ r) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {q ρ : ℝ} (hq : 0 ≤ q) (hqρ : q ≤ ρ) {u : ℝ → ℝ} (hu : Differentiable ℝ u)
    (hu₂ : Differentiable ℝ (deriv u)) (hu0 : ∀ x, u x ≤ 0) {D₁ D₂ : ℝ}
    (hD₁ : ∀ x, |deriv u x| ≤ D₁) (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    (hψ₂d : ∀ r, Differentiable ℝ (deriv (ψ r))) {M₀ M₁ M₂ : ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀)
    (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁) (hM₂ : ∀ r x, |deriv (deriv (ψ r)) x| ≤ M₂)
    {f : (R → ℝ^(N + 1)) → ℝ} (hf : Measurable f) {C : ℝ} {m : ℕ}
    (hfb : ∀ σ, |f σ| ≤ C * ∏ l, (1 + ‖σ l‖) ^ m) {v₀ : ℝ} (hv₀ : v₀ ∈ Ioo (0 : ℝ) 1) :
    let P := (gaussianReal 0 r).prod
      ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))
    let γ := Measure.pi fun _ : Fin (N + 1) ⊕ Unit => gaussianReal 0 1
    let S (v : ℝ) (w : Fin (N + 1) ⊕ Unit → ℝ) (p : ℝ^(N + 1) × ℝ) : ℝ :=
      Real.sqrt v * ((Real.sqrt (N + 1))⁻¹ *
          ((∑ i : Fin N, w (Sum.inl i.castSucc) * p.1 i.castSucc) +
            Real.sqrt t * (w (Sum.inl (Fin.last N)) * p.1 (Fin.last N)))) +
        Real.sqrt (1 - v) * (Real.sqrt q * w (Sum.inr ()) + Real.sqrt (ρ - q) * p.2)
    let G (v : ℝ) (d : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)))
        (w : Fin (N + 1) ⊕ Unit → ℝ) : Measure (ℝ^(N + 1) × ℝ) :=
      ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted fun p =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 p.1 + u (S v w p)
    let T (a b : Option (Option R)) : ℝ :=
      ∫ d, ∫ w, ∫ σ : Option (Option R) → ℝ^(N + 1) × ℝ,
        |f (fun l => (σ (some (some l))).1)| *
          |((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, (σ a).1 i.castSucc * (σ b).1 i.castSucc) +
              t * ((σ a).1 (Fin.last N) * (σ b).1 (Fin.last N))) - if a = b then ρ else q|
        ∂(Measure.pi fun _ : Option (Option R) => G v₀ d w) ∂γ ∂P
    ∃ D : ℝ, HasDerivAt
        (fun v => ∫ d, ∫ w, ∫ σ : R → ℝ^(N + 1) × ℝ,
          f (fun l => (σ l).1) * ∏ l, ψ l (S v w (σ l))
          ∂(Measure.pi fun _ : R => G v d w) ∂γ ∂P) D v₀ ∧
      |D| ≤ ((Fintype.card R : ℝ) + 1) ^ 2 *
        (1 + |M₀| + |M₁| + |M₂| + |D₁| + |D₂|) ^ (Fintype.card R + 2) * ∑ a, ∑ b, T a b := by
  intro P γ S G T
  have hum : Measurable u := hu.continuous.measurable
  have hD0 : 0 ≤ D₁ := (abs_nonneg _).trans (hD₁ 0)
  have hrr0 : 0 ≤ (r : ℝ) - rBar := sub_nonneg.2 hrr
  -- the field as a linear form in the shared Gaussians
  set X : ℝ^(N + 1) → Fin (N + 1) ⊕ Unit → ℝ := fun x =>
    Sum.elim (fun i => (Real.sqrt (N + 1))⁻¹ *
      ((if i = Fin.last N then Real.sqrt t else 1) * x i)) 0 with hX
  set Y : Fin (N + 1) ⊕ Unit → ℝ := Sum.elim 0 fun _ => Real.sqrt q with hY
  have hcast : ∀ i : Fin N, (i.castSucc : Fin (N + 1)) ≠ Fin.last N := fun i =>
    (Fin.castSucc_lt_last i).ne
  have hXdot : ∀ (x : ℝ^(N + 1)) (w : Fin (N + 1) ⊕ Unit → ℝ), X x ⬝ᵥ w =
      (Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, w (Sum.inl i.castSucc) * x i.castSucc) +
        Real.sqrt t * (w (Sum.inl (Fin.last N)) * x (Fin.last N))) := fun x w => by
    simp only [dotProduct, Fintype.sum_sum_type, hX, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, add_zero, Fin.sum_univ_castSucc (n := N), hcast,
      reduceIte, one_mul, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · ring
  have hYdot : ∀ w : Fin (N + 1) ⊕ Unit → ℝ, Y ⬝ᵥ w = Real.sqrt q * w (Sum.inr ()) := fun w => by
    simp [dotProduct, Fintype.sum_sum_type, hY]
  have horth : ∀ x, X x ⬝ᵥ Y = 0 := fun x => by
    simp [dotProduct, Fintype.sum_sum_type, hX, hY]
  have hYY : Y ⬝ᵥ Y = q := by
    rw [hYdot]
    simpa [hY] using Real.mul_self_sqrt hq
  have hXX : ∀ x y : ℝ^(N + 1), X x ⬝ᵥ X y =
      ((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, x i.castSucc * y i.castSucc) +
        t * (x (Fin.last N) * y (Fin.last N))) := fun x y => by
    have hs : (Real.sqrt (N + 1))⁻¹ * (Real.sqrt (N + 1))⁻¹ = ((N : ℝ) + 1)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
    have ht : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0
    rw [hXdot]
    simp only [hX, Sum.elim_inl, hcast, reduceIte, one_mul]
    rw [← hs, mul_add, mul_add]
    congr 1
    · rw [mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    · linear_combination (((Real.sqrt (N + 1))⁻¹ * (Real.sqrt (N + 1))⁻¹) *
        (x (Fin.last N) * y (Fin.last N))) * ht
  have hXm : ∀ k, Measurable fun x => X x k := fun k => by
    cases k with
    | inl i =>
      exact (((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) i).measurable).const_mul
        _).const_mul _
    | inr _ => exact measurable_const
  have hXb : ∀ k x, |X x k| ≤ 1 * (1 + ‖x‖) ^ 1 := fun k x => by
    rw [one_mul, pow_one]
    cases k with
    | inl i =>
      have hxi : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
      have hsN : |(Real.sqrt (N + 1))⁻¹| ≤ 1 := by
        rw [abs_of_nonneg (by positivity)]
        exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 (le_add_of_nonneg_left (Nat.cast_nonneg N)))
      have hst : |if i = Fin.last N then Real.sqrt t else 1| ≤ 1 := by
        split
        · rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact Real.sqrt_le_one.2 ht1
        · simp
      simp only [hX, Sum.elim_inl]
      rw [abs_mul, abs_mul]
      refine (mul_le_of_le_one_left (by positivity) hsN).trans ?_
      refine (mul_le_of_le_one_left (abs_nonneg _) hst).trans ?_
      linarith
    | inr _ =>
      simp only [hX, Sum.elim_inr, Pi.zero_apply, abs_zero]
      positivity
  -- confinement and moments in the old disorder
  set B₀ : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) → ℝ := fun d =>
    |h| * (∑ i, |d.2.2 i|) + |d.1|
  set c₀ : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) → ℝ := fun d =>
    |κ| + (|h| * (∑ i, |d.2.2 i|) + |d.1|) + ((r : ℝ) - rBar) / 2 +
      ∑ k, (|u 0| + D₁ * ∑ i, |d.2.1 k i|)
  have hB0 : ∀ d, 0 ≤ B₀ d := fun d => by
    have : 0 ≤ ∑ i, |d.2.2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    positivity
  have hc0 : ∀ d, 0 ≤ c₀ d := fun d => by
    have h1 : 0 ≤ ∑ i, |d.2.2 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have h2 : 0 ≤ ∑ k, (|u 0| + D₁ * ∑ i, |d.2.1 k i|) := Finset.sum_nonneg fun k _ =>
      add_nonneg (abs_nonneg _) (mul_nonneg hD0 (Finset.sum_nonneg fun _ _ => abs_nonneg _))
    exact add_nonneg (add_nonneg (add_nonneg (abs_nonneg _)
      (add_nonneg (mul_nonneg (abs_nonneg _) h1) (abs_nonneg _))) (div_nonneg hrr0 zero_le_two)) h2
  have hmom : ∀ deg : ℕ, Integrable (fun d => (1 + B₀ d + c₀ d) ^ deg) P := fun deg => by
    set A : ℝ := 1 + |κ| + (2 * |h| + 2) + ((r : ℝ) - rBar) / 2 + (M * |u 0| + D₁)
    have hm : Measurable fun d : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) =>
        (1 + B₀ d + c₀ d) ^ deg := by
      dsimp only [B₀, c₀]; fun_prop
    refine integrable_of_abs_le_cavity_disorder_pow r hm (K := A ^ deg) (d := deg) fun d => ?_
    obtain ⟨hs1, hsy, hsg, hsg0, -⟩ := cavity_disorder_size_bounds d
    rw [abs_of_nonneg (pow_nonneg (by linarith [hB0 d, hc0 d]) _), ← mul_pow]
    refine pow_le_pow_left₀ (by linarith [hB0 d, hc0 d]) ?_ deg
    set s : ℝ := 1 + |d.1| + (∑ k, ∑ i, |d.2.1 k i|) + ∑ i, |d.2.2 i|
    have hsum : ∑ k, (|u 0| + D₁ * ∑ i, |d.2.1 k i|) =
        M * |u 0| + D₁ * ∑ k, ∑ i, |d.2.1 k i| := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Finset.mul_sum]
    have h1 : |h| * (∑ i, |d.2.2 i|) ≤ |h| * s := mul_le_mul_of_nonneg_left hsg0 (abs_nonneg _)
    have h2 : D₁ * (∑ k, ∑ i, |d.2.1 k i|) ≤ D₁ * s := mul_le_mul_of_nonneg_left hsg hD0
    have h3 : ∀ c : ℝ, 0 ≤ c → c ≤ c * s := fun c hc => le_mul_of_one_le_right hc hs1
    have h4 := h3 1 zero_le_one
    have h5 := h3 |κ| (abs_nonneg _)
    have h6 := h3 (((r : ℝ) - rBar) / 2) (div_nonneg hrr0 zero_le_two)
    have h7 := h3 (M * |u 0|) (by positivity)
    dsimp only [B₀, c₀, A]
    rw [hsum]
    nlinarith
  have hE0m : Measurable fun p : (ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) ×
      ℝ^(N + 1) =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t p.1.1 u p.1.2.1 p.1.2.2 p.2 :=
    measurable_cavity_exponent hum t
  have hS : ∀ (v : ℝ) (w : Fin (N + 1) ⊕ Unit → ℝ) (p : ℝ^(N + 1) × ℝ), S v w p =
      Real.sqrt v * (X p.1 ⬝ᵥ w) +
        Real.sqrt (1 - v) * (Y ⬝ᵥ w + Real.sqrt (ρ - q) * p.2) := fun v w p => by
    rw [hXdot, hYdot]
  have hcov : ∀ (a b : Option (Option R)) (x y : ℝ^(N + 1)),
      X x ⬝ᵥ X y - (Y ⬝ᵥ Y + if a = b then Real.sqrt (ρ - q) ^ 2 else 0) =
        ((N : ℝ) + 1)⁻¹ * ((∑ i : Fin N, x i.castSucc * y i.castSucc) +
          t * (x (Fin.last N) * y (Fin.last N))) - if a = b then ρ else q := fun a b x y => by
    rw [hXX, hYY, Real.sq_sqrt (sub_nonneg.2 hqρ)]
    split <;> ring
  have hmain := exists_hasDerivAt_integral_integral_pi_tilted_prod_gaussianReal_sqrt_abs_le
    (volume : Measure (ℝ^(N + 1))) P hκ hB0 hmom hE0m
    (fun d σ => by
      simpa only [B₀] using neg_shcherbinaTirozziCavityHamiltonian_le κ h d.1 hrr ht0 ht1 hu0
        d.2.1 d.2.2 σ)
    (fun d σ hσ => by
      simpa only [c₀] using le_neg_shcherbinaTirozziCavityHamiltonian_of_norm_le_one κ h d.1 hrr
        ht0 ht1 hu hD₁ d.2.1 d.2.2 hσ)
    X Y hXm hXb horth (Real.sqrt (ρ - q)) hu hu₂ hu0 hD₁ hD₂ ψ hψd hψ₂d hM₀ hM₁ hM₂ hf hfb hv₀
  simp only [← hS, hcov] at hmain
  exact hmain

end SpinGlasses
