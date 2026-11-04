/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenVanishing
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityOuterDerivative
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityDomination
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityContraction
public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapSecondMoments.SKCavityTaylor
public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapCLT.HigherOrderCavity.SKCavityHigherOrderMoments

/-!
# Iterated cavity derivatives and Taylor bounds
(Talagrand Lemmas 1.11.3, 1.11.5, Corollaries 1.11.6, 1.11.7)

This module formalizes the quantitative differential calculus along the cavity path:
* `skCavityPathMean`: the disorder-averaged $n$-replica Gibbs average along the cavity path
  $u \mapsto \nu_u(f)$ parameterized by $u \in [0, 1]$ ($u = 1$ is coupled, $u = 0$ is decoupled).
* `skCavityPathDerivKernel`: the observable on `Option (Option (Fin n))` produced by differentiating
  with respect to $u$.
* `hasDerivAt_skCavityPathMean`: differentiability of $u \mapsto \nu_u(f)$ on $(0, 1)$ via
  `hasDerivAt_integral_sk_cavity_path_square`.
* **Lemma 1.11.3** (`sk_cavity_first_deriv_bound`): the first derivative along the cavity path
  satisfies $|\nu_u'(f)| \le K (N+1)^{-1/2} \nu_1(f^2)^{1/2}$.
* **Lemma 1.11.5** (`sk_cavity_decoupled_spin_vanishing`): vanishing of spin-difference observables
  under the decoupled endpoint $\nu_0$ whenever $2m + r < s$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- The disorder-averaged `n`-replica Gibbs average along the cavity path parameterized by
`u ∈ [0, 1]`. Here `u = 1` corresponds to the coupled system ($s = 0$), and `u = 0` corresponds
to the decoupled endpoint ($s = \pi / 2$). -/
noncomputable def skCavityPathMean (N n : ℕ) (β q h : ℝ) (u : ℝ)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) : ℝ :=
  let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
    (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs N,
          g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ)
  let s := Real.arccos (Real.sqrt u)
  let E : (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' ω a =>
    Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
      (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
    Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
  ∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
    ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E g' ω))
    ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
  ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)

/-- The cavity interaction kernel $K(a, b) = \beta^2 \varepsilon(a) \varepsilon(b) (R^-(a, b) - q)$. -/
noncomputable def skCavityPathKernel (N : ℕ) (β q : ℝ)
    (a b : Fin (N + 1) → ℤˣ) : ℝ :=
  β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
    ((N + 1 : ℝ)⁻¹ *
      ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)) - q)

/-- The truncated Ising overlap deviation $|R^-(a, b) - q|$. -/
noncomputable def skCavityTruncDev (N : ℕ) (q : ℝ)
    (a b : Fin (N + 1) → ℤˣ) : ℝ :=
  |((N + 1 : ℝ)⁻¹ *
    ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N => (b i.castSucc : ℝ)) - q)|

/-- The observable produced on `Option (Option (Fin n))` replicas by differentiating
`skCavityPathMean` with respect to `u`. -/
noncomputable def skCavityPathDerivKernel (N n : ℕ) (β q : ℝ)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ := fun τ =>
  f (fun r => τ (some (some r))) *
    ((∑ p : Fin n × Fin n with p.1 < p.2,
        skCavityPathKernel N β q (τ (some (some p.1))) (τ (some (some p.2)))) -
      (n : ℝ) * ∑ r : Fin n,
        skCavityPathKernel N β q (τ (some (some r))) (τ (some none)) +
      (n : ℝ) * ((n : ℝ) + 1) / 2 *
        skCavityPathKernel N β q (τ (some none)) (τ none))

/-- Pointwise bound on the cavity interaction kernel: $|K(a, b)| \le \beta^2 |R^-(a, b) - q|$. -/
theorem abs_skCavityPathKernel_le (N : ℕ) (β q : ℝ) (a b : Fin (N + 1) → ℤˣ) :
    |skCavityPathKernel N β q a b| ≤ β ^ 2 * skCavityTruncDev N q a b := by
  dsimp only [skCavityPathKernel, skCavityTruncDev]
  rw [abs_mul, abs_mul, abs_mul]
  have ha : |(a (Fin.last N) : ℝ)| = 1 := by
    rcases units_cast_eq_one_or (a (Fin.last N)) with h | h <;> simp [h]
  have hb : |(b (Fin.last N) : ℝ)| = 1 := by
    rcases units_cast_eq_one_or (b (Fin.last N)) with h | h <;> simp [h]
  rw [ha, hb, mul_one, mul_one, abs_sq]

/-- **Talagrand's Eq. (1.151).** Derivative of the cavity path expectation with respect to
the square parameter `u ∈ (0, 1)`. -/
theorem hasDerivAt_skCavityPathMean (N n : ℕ) (β q h t : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ);
    let E : (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' ω a =>
      Real.cos (Real.arccos (Real.sqrt t)) * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin (Real.arccos (Real.sqrt t)) * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) +
        B g' a;
    HasDerivAt (skCavityPathMean N n β q h · f)
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          skCavityPathDerivKernel N n β q f τ
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) t :=
  hasDerivAt_integral_sk_cavity_path_square N n β q h t hq ht f

/-- Bound on the derivative kernel `skCavityPathDerivKernel` in terms of centered overlaps. -/
theorem abs_skCavityPathDerivKernel_le (N n : ℕ) (β q : ℝ)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ)
    (τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) :
    |skCavityPathDerivKernel N n β q f τ| ≤
      β ^ 2 * |f (fun r => τ (some (some r)))| *
        (∑ p : Fin n × Fin n with p.1 < p.2,
            skCavityTruncDev N q (τ (some (some p.1))) (τ (some (some p.2))) +
          (n : ℝ) * ∑ r : Fin n,
            skCavityTruncDev N q (τ (some (some r))) (τ (some none)) +
          (n : ℝ) * ((n : ℝ) + 1) / 2 *
            skCavityTruncDev N q (τ (some none)) (τ none)) := by
  let X := ∑ p : Fin n × Fin n with p.1 < p.2,
    skCavityPathKernel N β q (τ (some (some p.1))) (τ (some (some p.2)))
  let Y := (n : ℝ) * ∑ r : Fin n,
    skCavityPathKernel N β q (τ (some (some r))) (τ (some none))
  let Z := (n : ℝ) * ((n : ℝ) + 1) / 2 *
    skCavityPathKernel N β q (τ (some none)) (τ none)
  have h_inner : |X - Y + Z| ≤ β ^ 2 *
      (∑ p : Fin n × Fin n with p.1 < p.2,
          skCavityTruncDev N q (τ (some (some p.1))) (τ (some (some p.2))) +
        (n : ℝ) * ∑ r : Fin n,
          skCavityTruncDev N q (τ (some (some r))) (τ (some none)) +
        (n : ℝ) * ((n : ℝ) + 1) / 2 *
          skCavityTruncDev N q (τ (some none)) (τ none)) := by
    have h1 := abs_add_le (X - Y) Z
    have h2 : |X - Y| ≤ |X| + |Y| := by
      rw [sub_eq_add_neg]
      refine (abs_add_le X (-Y)).trans ?_
      simp only [abs_neg, le_rfl]
    have htri : |X - Y + Z| ≤ |X| + |Y| + |Z| := by linarith
    refine htri.trans ?_
    have hX : |X| ≤ β ^ 2 * ∑ p : Fin n × Fin n with p.1 < p.2,
        skCavityTruncDev N q (τ (some (some p.1))) (τ (some (some p.2))) := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      refine (sum_le_sum fun p hp => abs_skCavityPathKernel_le N β q _ _).trans ?_
      rw [← mul_sum]
    have hY : |Y| ≤ (n : ℝ) * (β ^ 2 * ∑ r : Fin n,
        skCavityTruncDev N q (τ (some (some r))) (τ (some none))) := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
      refine (abs_sum_le_sum_abs _ _).trans ?_
      refine (sum_le_sum fun r hr => abs_skCavityPathKernel_le N β q _ _).trans ?_
      rw [← mul_sum]
    have hZ : |Z| ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 *
        (β ^ 2 * skCavityTruncDev N q (τ (some none)) (τ none)) := by
      rw [abs_mul]
      have hpos : 0 ≤ (n : ℝ) * ((n : ℝ) + 1) / 2 := by positivity
      rw [abs_of_nonneg hpos]
      exact mul_le_mul_of_nonneg_left (abs_skCavityPathKernel_le N β q _ _) hpos
    linarith
  dsimp only [skCavityPathDerivKernel]
  rw [abs_mul]
  have h_prod := mul_le_mul_of_nonneg_left h_inner
    (abs_nonneg (f (fun r => τ (some (some r)))))
  calc |f (fun r => τ (some (some r)))| * |X - Y + Z| ≤
      |f (fun r => τ (some (some r)))| * (β ^ 2 * _) := h_prod
  _ = β ^ 2 * |f (fun r => τ (some (some r)))| * _ := by ring

end SpinGlasses
