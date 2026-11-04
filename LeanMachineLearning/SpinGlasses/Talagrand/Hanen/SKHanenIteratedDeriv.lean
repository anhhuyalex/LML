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
public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapCLT.Contractions.SKOverlapCLTStep

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
* Bounds for coupled expectations of products of truncated centered overlaps.

The iterated derivative bounds and their connection to decoupled vanishing remain open.
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

/-- The cavity interaction kernel:
$K(a, b) = \beta^2 \varepsilon(a) \varepsilon(b) (R^-(a, b) - q)$. -/
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
    have htri : |X - Y + Z| ≤ |X| + |Y| + |Z| := by
      linarith [abs_add_le (X - Y) Z, abs_sub X Y]
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

/-- A coupled expectation containing `m` truncated overlap deviations and a uniformly
bounded observable is `O((N + 1)^(-m/2))`. This is not an iterated derivative bound. -/
theorem sk_cavity_iterated_deriv_bound (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    (n m : ℕ) (M : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ),
      (∀ σ, |f σ| ≤ M) →
      ∀ (p : Fin m → Fin n × Fin n),
      (∀ j, (p j).1 ≠ (p j).2) →
      let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (σ i : ℝ)
      let ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun F =>
        ∫ g, ∫ σ, F σ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E g))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
      |ν (fun σ => f σ * ∏ j : Fin m,
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (p j).1 i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (σ (p j).2 i.castSucc : ℝ)) - q))| ≤
        K / ((N : ℝ) + 1) ^ (((m : ℕ) : ℝ) / 2) := by
  obtain ⟨H, hH0, hH⟩ := sk_cavity_prod_sq_le β₀ hβ₀ m M
  refine ⟨Real.sqrt H + 1, by positivity, ?_⟩
  intro β h q hfix hb N f hf p hp E ν
  let F : (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
    f σ * ∏ j : Fin m,
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (p j).1 i.castSucc : ℝ)) ⬝ᵥ
        fun i : Fin N => (σ (p j).2 i.castSucc : ℝ)) - q)
  have h_sq := hH β h q hfix hb N n (fun j => (p j).1) (fun j => (p j).2) hp f hf
  change ν (fun σ => F σ ^ 2) ≤ H / ((N : ℝ) + 1) ^ m at h_sq
  have h_cs : (ν F) ^ 2 ≤ ν (fun σ => F σ ^ 2) := sk_nu_sq_le N n β h ν (fun _ => rfl) F
  have h_abs : |ν F| ≤ Real.sqrt (ν (fun σ => F σ ^ 2)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h_cs
  have h_trans := h_abs.trans (Real.sqrt_le_sqrt h_sq)
  refine h_trans.trans ?_
  have hN_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [Real.sqrt_div hH0.le]
  have h_pow : Real.sqrt (((N : ℝ) + 1) ^ m) = ((N : ℝ) + 1) ^ (((m : ℕ) : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]
    ring_nf
  rw [h_pow]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- Coupled expectation bound for a bounded observable and `a` truncated overlap deviations.
This does not yet establish the spin-difference Taylor estimate in Corollary 1.11.6. -/
theorem sk_eta_coupled_bound (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    (n a : ℕ) (M : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (W : (Fin n → Fin (N + 1) → ℤˣ) → ℝ),
      (∀ σ, |W σ| ≤ M) →
      ∀ (x y : Fin a → Fin n),
      (∀ j, x j ≠ y j) →
      let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (σ i : ℝ)
      let ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun F =>
        ∫ g, ∫ σ, F σ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E g))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
      |ν (fun σ => W σ * ∏ j : Fin a,
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (x j) i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (σ (y j) i.castSucc : ℝ)) - q))| ≤
        K / ((N : ℝ) + 1) ^ (((a : ℕ) : ℝ) / 2) := by
  obtain ⟨H, hH0, hH⟩ := sk_cavity_prod_sq_le β₀ hβ₀ a M
  refine ⟨Real.sqrt H + 1, by positivity, ?_⟩
  intro β h q hfix hb N W hW x y hxy E ν
  let F : (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
    W σ * ∏ j : Fin a,
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (x j) i.castSucc : ℝ)) ⬝ᵥ
        fun i : Fin N => (σ (y j) i.castSucc : ℝ)) - q)
  have h_sq := hH β h q hfix hb N n x y hxy W hW
  change ν (fun σ => F σ ^ 2) ≤ H / ((N : ℝ) + 1) ^ a at h_sq
  have h_cs : (ν F) ^ 2 ≤ ν (fun σ => F σ ^ 2) := sk_nu_sq_le N n β h ν (fun _ => rfl) F
  have h_abs : |ν F| ≤ Real.sqrt (ν (fun σ => F σ ^ 2)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt h_cs
  have h_trans := h_abs.trans (Real.sqrt_le_sqrt h_sq)
  refine h_trans.trans ?_
  have hN_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [Real.sqrt_div hH0.le]
  have h_pow : Real.sqrt (((N : ℝ) + 1) ^ a) = ((N : ℝ) + 1) ^ (((a : ℕ) : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]
    ring_nf
  rw [h_pow]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- The coupled overlap-product bound specialized to `2 * p + m` factors.
The spin-difference and shifted-overlap estimate of Corollary 1.11.7 remains open. -/
theorem sk_eta_overlap_shifted_bound (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    (n p m : ℕ) (M : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (W : (Fin n → Fin (N + 1) → ℤˣ) → ℝ),
      (∀ σ, |W σ| ≤ M) →
      ∀ (x y : Fin (2 * p + m) → Fin n),
      (∀ j, x j ≠ y j) →
      let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (σ i : ℝ)
      let ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ := fun F =>
        ∫ g, ∫ σ, F σ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E g))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
      |ν (fun σ => W σ * ∏ j : Fin (2 * p + m),
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (x j) i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (σ (y j) i.castSucc : ℝ)) - q))| ≤
        K / ((N : ℝ) + 1) ^ (((2 * p + m : ℕ) : ℝ) / 2) := by
  obtain ⟨K, hK0, hK⟩ := sk_eta_coupled_bound β₀ hβ₀ n (2 * p + m) M
  refine ⟨K, hK0, ?_⟩
  intro β h q hfix hb N W hW x y hxy E ν
  exact hK β h q hfix hb N W hW x y hxy

end SpinGlasses
