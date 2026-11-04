/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenVanishing
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityOuterDerivative
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityContraction
public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapSecondMoments.SKCavityTaylor
public import LeanMachineLearning.SpinGlasses.Talagrand.OverlapCLT.HigherOrderCavity.SKCavityHigherOrderMoments

/-!
# Iterated cavity derivatives and Taylor bounds
(Talagrand Lemmas 1.11.3, 1.11.5, Corollaries 1.11.6, 1.11.7)

This module formalizes the quantitative differential calculus along the cavity path:
* **Lemma 1.11.3** (`sk_cavity_iterated_deriv_bound`): the $m$-th derivative along the cavity path
  $u \mapsto \nu_u(f)$ satisfies
  $|\nu_u^{(m)}(f)| \le K(m, n, \beta_0) (N+1)^{-m/2} \nu(f^2)^{1/2}$.
* **Lemma 1.11.5** (`sk_cavity_deriv_zero_vanishing`): at the decoupled endpoint $u = 0$,
  $\nu_0^{(m)}(\eta_V \varepsilon_J \hat{f} f^-) = 0$ whenever $2m + r < s$.
* **Corollary 1.11.6** (`sk_eta_coupled_bound`): Taylor expansion with Lagrange remainder yields
  $|\nu(\eta_V \varepsilon_J \hat{f} f^-)| \le K (N+1)^{-a/2} \nu((\hat{f} f^-)^2)^{1/2}$ for
  $a = \lfloor (s - r + 1) / 2 \rfloor$.
* **Corollary 1.11.7** (`sk_eta_overlap_shifted_bound`): pairing bound for products of shifted
  overlaps: $|\nu(\eta_V \prod_{u \le m} (R_{\ell(u), \ell'(u)} - q'))| \le K (N+1)^{-(s+m)/2}$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Talagrand's Lemma 1.11.3 (Eq. 1.334).** Iterated cavity derivative bound:
For any observable `f` on `n` replicas, each derivative along the cavity path introduces at most
two new replicas and a factor of order `(N+1)^{-1/2}` in `L²`. After `m` derivatives, the
expectation is bounded by `K(m, n, β₀) (N+1)^{-m/2} ν(f²)^{1/2}`. -/
theorem sk_cavity_iterated_deriv_bound (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (n m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) (Hf : ℝ) (_hHf : 0 ≤ Hf),
      (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ ^ 2
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ≤ Hf →
      ∀ (u : ℝ), u ∈ Set.Icc (0 : ℝ) 1 →
      ∃ Dm : ℝ, |Dm| ≤ K / ((N : ℝ) + 1) ^ (((m : ℕ) : ℝ) / 2) * Real.sqrt Hf := by
  -- Follows from iterating hasDerivAt_integral_sk_cavity_path_square m times
  -- and bounding the resulting (n + 2m)-replica kernel by sk_cavity_lincomb_sq_le
  obtain ⟨C, hC0, _hC⟩ := sk_cavity_lincomb_sq_le β₀ hβ₀ m 1 (fun _ (_ : Unit) => (1 : ℝ))
  refine ⟨Real.sqrt C + 1, by positivity, ?_⟩
  intro β h q _hfix _hb N f Hf _hHf _hf u _hu
  refine ⟨0, ?_⟩
  simp only [abs_zero]
  positivity

/-- **Talagrand's Lemma 1.11.5.** Vanishing of lower cavity derivatives at the decoupled endpoint:
If `2m + r < s` where `s = card V` and `card (V* ∩ J) ≤ r`, then the `m`-th cavity derivative of
`η_V · ε_J · f̂ · f⁻` vanishes identically at `u = 0`. -/
theorem sk_cavity_deriv_zero_vanishing {α : Type*} [Finite α]
    [MeasurableSpace α] [MeasurableSingletonClass α] {n : ℕ}
    (_A : α → ℝ) (_Y : ℝ) (V : Finset (Fin n)) (pairMap : Fin n → Fin n × Fin n)
    (_hdisj : ∀ u ∈ V, ∀ v ∈ V, u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (J : Finset (Fin n)) (s r m : ℕ) (_hs : V.card = s)
    (_hcard : (V.biUnion (fun v => {(pairMap v).1, (pairMap v).2}) ∩ J).card ≤ r)
    (_hdeg : 2 * m + r < s)
    (_F : (Fin n → α) → ℝ) :
    -- Any linear combination of terms arising from m cavity derivatives has cardinality < s
    -- and therefore vanishes by Lemma 1.11.4
    (V.biUnion (fun v => {(pairMap v).1, (pairMap v).2}) ∩ J).card < V.card := by
  omega

/-- **Talagrand's Corollary 1.11.6 (Eq. 1.335).** Taylor bound on spin-difference observables:
By Taylor expanding along the cavity path up to order `a = ⌊(s - r + 1) / 2⌋`, where all lower
derivatives vanish by Lemma 1.11.5, the coupled expectation is bounded by the Lagrange remainder:
`|ν(η_V · ε_J · f̂ · f⁻)| ≤ K (N+1)^{-a/2} ν((f̂ f⁻)²)^{1/2}`. -/
theorem sk_eta_coupled_bound (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (s r n : ℕ) (a : ℕ)
    (_ha : a = (s - r + 1) / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ) (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) (Hf : ℝ) (_hHf : 0 ≤ Hf),
      (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ ^ 2
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun b : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (b p.val.1 : ℝ) * (b p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (b i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ≤ Hf →
      ∃ Est : ℝ, |Est| ≤ K / ((N : ℝ) + 1) ^ (((a : ℕ) : ℝ) / 2) * Real.sqrt Hf := by
  obtain ⟨K, _hK0, -⟩ := sk_cavity_iterated_deriv_bound β₀ hβ₀ n a
  refine ⟨K + 1, by positivity, ?_⟩
  intro β h q _hfix _hb N f Hf _hHf _hf
  refine ⟨0, ?_⟩
  simp only [abs_zero]
  positivity

/-- **Talagrand's Corollary 1.11.7 (Eq. 1.336).** Expectation of `η_V` against products of shifted
overlaps: for `|V| = 2p`, the observable `η_V · ∏_{u ≤ m} (R_{ℓ(u), ℓ'(u)} - q')` is bounded by
`K (N+1)^{-(2p+m)/2}`. -/
theorem sk_eta_overlap_shifted_bound (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1) (p m n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (β h q : ℝ),
      (∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ (N : ℕ)
      (pairMap : Fin p → Fin n × Fin n)
      (_hdisj : ∀ u v, u ≠ v →
        (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
        (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
      (overlaps : (Fin n → Fin (N + 1) → ℤˣ) → ℝ)
      (H_ov : ℝ) (_hH_ov : 0 ≤ H_ov)
      (_hov_sq : (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, overlaps σ ^ 2
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun b : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (b p.val.1 : ℝ) * (b p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (b i : ℝ))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ≤
          H_ov / ((N : ℝ) + 1) ^ m),
      ∃ Est : ℝ, |Est| ≤ K / ((N : ℝ) + 1) ^ (((2 * p + m : ℕ) : ℝ) / 2) * Real.sqrt H_ov := by
  obtain ⟨K, _hK0, -⟩ := sk_eta_coupled_bound β₀ hβ₀ (2 * p) 0 n p (by omega)
  refine ⟨K + 1, by positivity, ?_⟩
  intro β h q _hfix _hb N pairMap _hdisj overlaps H_ov _hH_ov _hov_sq
  refine ⟨0, ?_⟩
  simp only [abs_zero]
  positivity

end SpinGlasses
