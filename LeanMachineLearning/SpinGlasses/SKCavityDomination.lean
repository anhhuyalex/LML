/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityOuterDerivative
public import LeanMachineLearning.SpinGlasses.SKCavityEndpoint
public import LeanMachineLearning.ForMathlib.Analysis.Calculus.GronwallBackward
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IteratedBound

/-!
# Domination of the cavity path (Talagrand's Lemma 1.6.4)

The derivative formula (1.151) of the cavity path is a combination of `2 n²` kernel terms, each
bounded by `2 β²`, against the same replica average. For a nonnegative observable this gives
`|ν_t'(f)| ≤ 4 n² β² ν_t(f)` (Eq. (1.155)), and Grönwall's inequality yields (1.154).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Talagrand's Eq. (1.155)**, for an arbitrary base disorder: the derivative of the cavity
path is bounded by `4 n² β²` times the path average of a nonnegative observable. -/
theorem abs_cavity_outer_book_derivative_le
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (N n : ℕ) (β q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (B : Ω₀ → (Fin (N + 1) → ℤˣ) → ℝ) (hB : ∀ a, Measurable (fun η => B η a))
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) (hf : ∀ σ, 0 ≤ f σ) (s : ℝ) :
    let E : ℝ → Ω₀ → ((Fin N → ℝ) × ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun s η ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B η a
    let K : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N =>
            (b i.castSucc : ℝ)) - q)
    |∫ η, ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f (fun r => τ (some (some r))) *
            ((∑ p : Fin n × Fin n with p.1 < p.2,
                K (τ (some (some p.1))) (τ (some (some p.2)))) -
              (n : ℝ) * ∑ r : Fin n, K (τ (some (some r))) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E s η ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂P₀| ≤
    4 * (n : ℝ) ^ 2 * β ^ 2 * ∫ η, ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E s η ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂P₀ := by
  intro E K
  let P : Measure ((Fin N → ℝ) × ℝ) :=
    (Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)
  have hEm (a : Fin (N + 1) → ℤˣ) :
      Measurable (fun x : Ω₀ × ((Fin N → ℝ) × ℝ) => E s x.1 x.2 a) := by
    dsimp [E]
    fun_prop
  have hK : ∀ a b, |K a b| ≤ 2 * β ^ 2 := fun a b => by
    have h := abs_sk_cavity_covariance_le N β q hq a b
    rwa [← abs_neg, neg_sk_cavity_covariance] at h
  clear_value E K
  set c : ℝ := 4 * (n : ℝ) ^ 2 * β ^ 2 with hc
  let Θ : (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ := fun τ =>
    c * f (fun r => τ (some (some r)))
  have hmarg (η : Ω₀) (ω : (Fin N → ℝ) × ℝ) :
      ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ, f (fun r => τ (some (some r)))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E s η ω)) =
      ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E s η ω)) :=
    (integral_pi_option_count_tilted_marginal (R := Option (Fin n)) (E s η ω)
      fun ν => f fun r => ν (some r)).trans
      (integral_pi_option_count_tilted_marginal (R := Fin n) (E s η ω) f)
  let κ : Ω₀ → (Fin N → ℝ) × ℝ → Measure (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) :=
    fun η ω => Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E s η ω)
  let G : Ω₀ → (Fin N → ℝ) × ℝ → (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ :=
    fun _ _ τ => f (fun r => τ (some (some r))) *
      ((∑ p : Fin n × Fin n with p.1 < p.2,
          K (τ (some (some p.1))) (τ (some (some p.2)))) -
        (n : ℝ) * ∑ r : Fin n, K (τ (some (some r))) (τ (some none)) +
        (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none))
  have hpt (η : Ω₀) (ω : (Fin N → ℝ) × ℝ)
      (τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) : |G η ω τ| ≤ Θ τ := by
    dsimp only [G]
    rw [abs_mul, abs_of_nonneg (hf _)]
    have h := abs_book_replica_combination_le n K (2 * β ^ 2) hK τ
    calc _ ≤ f (fun r => τ (some (some r))) * (2 * (n : ℝ) ^ 2 * (2 * β ^ 2)) :=
          mul_le_mul_of_nonneg_left h (hf _)
      _ = Θ τ := by simp only [Θ, hc]; ring
  have h1 (η : Ω₀) (ω : (Fin N → ℝ) × ℝ) : Integrable Θ (κ η ω) := Integrable.of_finite
  have hdet : Integrable (fun x : Ω₀ × ((Fin N → ℝ) × ℝ) => ∫ τ, Θ τ ∂(κ x.1 x.2))
      (P₀.prod P) :=
    integrable_integral_pi_count_tilted_det
      (g := fun (a : Fin (N + 1) → ℤˣ) (x : Ω₀ × ((Fin N → ℝ) × ℝ)) => E s x.1 x.2 a)
      (fun a => (hEm a).aemeasurable) Θ
  have h2 (η : Ω₀) : Integrable (fun ω => ∫ τ, Θ τ ∂(κ η ω)) P :=
    integrable_integral_pi_count_tilted_det (P := P)
      (g := fun (a : Fin (N + 1) → ℤˣ) (ω : (Fin N → ℝ) × ℝ) => E s η ω a)
      (fun a => ((hEm a).comp measurable_prodMk_left).aemeasurable) Θ
  have h3 : Integrable (fun η => ∫ ω, ∫ τ, Θ τ ∂(κ η ω) ∂P) P₀ := hdet.integral_prod_left
  have key := abs_integral_integral_integral_le P₀ P κ (G := G) (H := fun _ _ τ => Θ τ)
    hpt h1 h2 h3
  refine key.trans_eq ?_
  simp only [Θ, integral_const_mul, hmarg, κ]
  rfl

/-- At angle `0` the cavity path is the coupled endpoint: the scalar Gaussian drops out and the
path average is the `(N + 1)`-spin SK average. -/
theorem integral_sk_cavity_path_zero (N n : ℕ) (β q h : ℝ)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
            (fun a : Fin (N + 1) → ℤˣ =>
              Real.cos 0 * ((Real.sqrt (N + 1))⁻¹ * β *
                (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
              Real.sin 0 * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
    ∫ g : FinPairs (N + 1) → ℝ,
      ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
          (fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs (N + 1),
                g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            h * ∑ i : Fin (N + 1), (a i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  intro B
  rw [← integral_sk_cavity_coupled_endpoint N n β h f]
  refine integral_congr_ae (ae_of_all _ fun g' => ?_)
  beta_reduce
  simp only [Real.sin_zero, Real.cos_zero, zero_mul, one_mul, add_zero]
  rw [integral_fun_fst (μ := Measure.pi fun _ : Fin N => gaussianReal 0 1)
    (ν := gaussianReal 0 1) (fun g : Fin N → ℝ =>
      ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
          (fun a : Fin (N + 1) → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β * (a (Fin.last N) : ℝ) *
              ∑ i : Fin N, g i * (a i.castSucc : ℝ) + B g' a)))]
  simp only [integral_const, probReal_univ, one_smul]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  have hE : (fun a : Fin (N + 1) → ℤˣ => (Real.sqrt (N + 1))⁻¹ * β * (a (Fin.last N) : ℝ) *
      ∑ i : Fin N, g i * (a i.castSucc : ℝ) + B g' a) =
      fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N, g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        (Real.sqrt (N + 1))⁻¹ * β * (a (Fin.last N) : ℝ) *
          (∑ i : Fin N, g i * (a i.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ) :=
    funext fun a => by simp only [B]; ring
  beta_reduce
  rw [hE]

/-- **Talagrand's Lemma 1.6.4 (Eq. (1.154))**: for a nonnegative observable `f` of `n` replicas,
the cavity-path average at `t = cos² s` is at most `exp (4 n² β²)` times its value at the
coupled endpoint `t = 1`, which is the `(N + 1)`-spin SK average. -/
theorem sk_cavity_path_square_le_exp_mul (N n : ℕ) (β q h : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ)
    (hf : ∀ σ, 0 ≤ f σ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
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
        ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
            (E (Real.arccos (Real.sqrt t)) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) ≤
    Real.exp (4 * (n : ℝ) ^ 2 * β ^ 2) *
      ∫ g : FinPairs (N + 1) → ℝ,
        ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
            (fun a : Fin (N + 1) → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  intro B E
  let Φ : ℝ → ℝ := fun s =>
    ∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
      ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E s g' ω))
      ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
    ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
  have hcont : Continuous Φ := continuous_iff_continuousAt.2 fun s =>
    (hasDerivAt_integral_sk_cavity_path_angle_offDiag N n β q h hq f s).continuousAt
  have hcontOn : ContinuousOn (fun u => Φ (Real.arccos (Real.sqrt u))) (Set.Icc 0 1) :=
    (hcont.comp (Real.continuous_arccos.comp Real.continuous_sqrt)).continuousOn
  have hzero : Φ (Real.arccos (Real.sqrt 1)) = ∫ g : FinPairs (N + 1) → ℝ,
        ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
            (fun a : Fin (N + 1) → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    rw [Real.sqrt_one, Real.arccos_one]
    exact integral_sk_cavity_path_zero N n β q h f
  have hkey : ∀ u ∈ Set.Ioo (0 : ℝ) 1, ∃ d,
      HasDerivAt (fun u => Φ (Real.arccos (Real.sqrt u))) d u ∧
      -(4 * (n : ℝ) ^ 2 * β ^ 2 * Φ (Real.arccos (Real.sqrt u))) ≤ d := fun u hu =>
    ⟨_, hasDerivAt_integral_sk_cavity_path_square N n β q h u hq hu f,
      (neg_le_neg_iff.2 (abs_cavity_outer_book_derivative_le
        (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) N n β q hq B
        (fun a => by fun_prop) f hf (Real.arccos (Real.sqrt u)))).trans (neg_abs_le _)⟩
  choose! d hd hb using hkey
  have hmain := le_exp_mul_endpoint_of_neg_mul_le_deriv hcontOn hd hb ht
  rw [hzero] at hmain
  have hnn : 0 ≤ ∫ g : FinPairs (N + 1) → ℝ,
        ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
            (fun a : Fin (N + 1) → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
    integral_nonneg fun g => integral_nonneg fun σ => hf σ
  refine hmain.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hnn)
  nlinarith [ht.1, sq_nonneg (n : ℝ), sq_nonneg β, mul_nonneg (sq_nonneg (n : ℝ)) (sq_nonneg β)]

end SpinGlasses
