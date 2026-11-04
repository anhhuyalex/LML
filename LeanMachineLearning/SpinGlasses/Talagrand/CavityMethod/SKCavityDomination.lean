/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityOuterDerivative
public import LeanMachineLearning.SpinGlasses.SKCavityEndpoint
public import LeanMachineLearning.SpinGlasses.GibbsReplicaMarginal
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

/-- **Domination of a nested replica average.** A pointwise bound `|G| ≤ H` on an observable of
`R` replicas passes through the Gibbs average of any measurable random energy, with an arbitrary
base disorder `P₀` and the cavity Gaussian disorder `ω`. -/
theorem abs_integral_nested_gibbs_le {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω]
    (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀] (P : Measure Ω) [IsProbabilityMeasure P]
    {R α : Type*} [Fintype R] [Finite α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (E : Ω₀ → Ω → α → ℝ)
    (hE : ∀ a, Measurable (fun x : Ω₀ × Ω => E x.1 x.2 a)) {G H : (R → α) → ℝ}
    (hGH : ∀ τ, |G τ| ≤ H τ) :
    |∫ η, ∫ ω, ∫ τ, G τ ∂(Measure.pi fun _ : R => Measure.count.tilted (E η ω)) ∂P ∂P₀| ≤
      ∫ η, ∫ ω, ∫ τ, H τ ∂(Measure.pi fun _ : R => Measure.count.tilted (E η ω)) ∂P ∂P₀ := by
  have hdet : Integrable (fun x : Ω₀ × Ω =>
      ∫ τ, H τ ∂(Measure.pi fun _ : R => Measure.count.tilted (E x.1 x.2))) (P₀.prod P) :=
    integrable_integral_pi_count_tilted_det (g := fun (a : α) (x : Ω₀ × Ω) => E x.1 x.2 a)
      (fun a => (hE a).aemeasurable) H
  exact abs_integral_integral_integral_le P₀ P
    (fun η ω => Measure.pi fun _ : R => Measure.count.tilted (E η ω))
    (G := fun _ _ τ => G τ) (H := fun _ _ τ => H τ) (fun _ _ τ => hGH τ)
    (fun _ _ => Integrable.of_finite)
    (fun η => integrable_integral_pi_count_tilted_det (P := P)
      (g := fun (a : α) (ω : Ω) => E η ω a)
      (fun a => ((hE a).comp measurable_prodMk_left).aemeasurable) H)
    hdet.integral_prod_left

/-- **Linearity of a nested replica average.** The three-level average of a finite combination of
observables is the combination of the averages. -/
theorem integral_nested_gibbs_finset_sum {Ω₀ Ω : Type*} [MeasurableSpace Ω₀] [MeasurableSpace Ω]
    (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀] (P : Measure Ω) [IsProbabilityMeasure P]
    {R α ι : Type*} [Fintype R] [Finite α] [Nonempty α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (E : Ω₀ → Ω → α → ℝ)
    (hE : ∀ a, Measurable (fun x : Ω₀ × Ω => E x.1 x.2 a)) (s : Finset ι) (c : ι → ℝ)
    (G : ι → (R → α) → ℝ) :
    ∫ η, ∫ ω, ∫ τ, ∑ j ∈ s, c j * G j τ ∂(Measure.pi fun _ : R => Measure.count.tilted (E η ω))
        ∂P ∂P₀ =
      ∑ j ∈ s, c j * ∫ η, ∫ ω, ∫ τ, G j τ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E η ω)) ∂P ∂P₀ := by
  have h2 (j : ι) (η : Ω₀) : Integrable (fun ω => ∫ τ, G j τ
      ∂(Measure.pi fun _ : R => Measure.count.tilted (E η ω))) P :=
    integrable_integral_pi_count_tilted_det (P := P) (g := fun (a : α) (ω : Ω) => E η ω a)
      (fun a => ((hE a).comp measurable_prodMk_left).aemeasurable) (G j)
  have h3 (j : ι) : Integrable (fun η => ∫ ω, ∫ τ, G j τ
      ∂(Measure.pi fun _ : R => Measure.count.tilted (E η ω)) ∂P) P₀ :=
    (integrable_integral_pi_count_tilted_det (P := P₀.prod P)
      (g := fun (a : α) (x : Ω₀ × Ω) => E x.1 x.2 a) (fun a => (hE a).aemeasurable)
      (G j)).integral_prod_left
  have e1 (η : Ω₀) (ω : Ω) : ∫ τ, ∑ j ∈ s, c j * G j τ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E η ω)) =
      ∑ j ∈ s, c j * ∫ τ, G j τ ∂(Measure.pi fun _ : R => Measure.count.tilted (E η ω)) := by
    rw [integral_finsetSum _ fun j _ => Integrable.of_finite.const_mul (c j)]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have e2 (η : Ω₀) : ∫ ω, ∑ j ∈ s, c j * ∫ τ, G j τ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E η ω)) ∂P =
      ∑ j ∈ s, c j * ∫ ω, ∫ τ, G j τ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E η ω)) ∂P := by
    rw [integral_finsetSum _ fun j _ => (h2 j η).const_mul (c j)]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  simp_rw [e1, e2]
  rw [integral_finsetSum _ fun j _ => (h3 j).const_mul (c j)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

/-- **Linearity of a two-level replica average.**  The disorder average of the Gibbs average of a
finite combination of observables is the combination of the averages. -/
theorem integral_gibbs_finset_sum {Ω₀ : Type*} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    [IsProbabilityMeasure P₀] {R α ι : Type*} [Fintype R] [Finite α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (E : Ω₀ → α → ℝ)
    (hE : ∀ a, Measurable (fun η => E η a)) (s : Finset ι) (c : ι → ℝ) (G : ι → (R → α) → ℝ) :
    ∫ η, ∫ τ, ∑ j ∈ s, c j * G j τ ∂(Measure.pi fun _ : R => Measure.count.tilted (E η)) ∂P₀ =
      ∑ j ∈ s, c j * ∫ η, ∫ τ, G j τ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E η)) ∂P₀ := by
  have h3 (j : ι) : Integrable (fun η => ∫ τ, G j τ
      ∂(Measure.pi fun _ : R => Measure.count.tilted (E η))) P₀ :=
    integrable_integral_pi_count_tilted_det (g := fun (a : α) (η : Ω₀) => E η a)
      (fun a => (hE a).aemeasurable) (G j)
  have e1 (η : Ω₀) : ∫ τ, ∑ j ∈ s, c j * G j τ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E η)) =
      ∑ j ∈ s, c j * ∫ τ, G j τ ∂(Measure.pi fun _ : R => Measure.count.tilted (E η)) := by
    rw [integral_finsetSum _ fun j _ => Integrable.of_finite.const_mul (c j)]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  simp_rw [e1]
  rw [integral_finsetSum _ fun j _ => (h3 j).const_mul (c j)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

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
  have hK : ∀ a b, |K a b| ≤ 2 * β ^ 2 := abs_sk_cavity_kernel_le N β q hq
  clear_value E K
  set c : ℝ := 4 * (n : ℝ) ^ 2 * β ^ 2 with hc
  let Θ : (Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) → ℝ := fun τ =>
    c * f (fun r => τ (some (some r)))
  have hmarg (η : Ω₀) (ω : (Fin N → ℝ) × ℝ) :
      ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ, f (fun r => τ (some (some r)))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted (E s η ω)) =
      ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (E s η ω)) :=
    integral_pi_option_option_count_tilted_marginal (E s η ω) f
  have hpt (τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ) :
      |f (fun r => τ (some (some r))) *
        ((∑ p : Fin n × Fin n with p.1 < p.2,
            K (τ (some (some p.1))) (τ (some (some p.2)))) -
          (n : ℝ) * ∑ r : Fin n, K (τ (some (some r))) (τ (some none)) +
          (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none))| ≤ Θ τ := by
    rw [abs_mul, abs_of_nonneg (hf _)]
    have h := abs_book_replica_combination_le n K (2 * β ^ 2) hK τ
    calc _ ≤ f (fun r => τ (some (some r))) * (2 * (n : ℝ) ^ 2 * (2 * β ^ 2)) :=
          mul_le_mul_of_nonneg_left h (hf _)
      _ = Θ τ := by simp only [Θ, hc]; ring
  refine (abs_integral_nested_gibbs_le P₀ P (E s) hEm hpt).trans_eq ?_
  simp only [Θ, integral_const_mul, hmarg]
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
  have hmain := le_exp_mul_endpoint_of_exists_hasDerivAt hcontOn hkey ht
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

/-- **Lemma 1.6.4 for an arbitrary finite set of replicas.** The replica index type enters only
through its cardinality `m`, so the comparison constant is `exp (4 m² β²)`. -/
theorem sk_cavity_path_square_le_exp_mul_replicas (N : ℕ) (β q h : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) {R : Type*} [Fintype R]
    (G : (R → Fin (N + 1) → ℤˣ) → ℝ) (hG : ∀ τ, 0 ≤ G τ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
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
        ∫ τ : R → Fin (N + 1) → ℤˣ, G τ
          ∂(Measure.pi fun _ : R => Measure.count.tilted
            (E (Real.arccos (Real.sqrt t)) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) ≤
    Real.exp (4 * (Fintype.card R : ℝ) ^ 2 * β ^ 2) *
      ∫ g : FinPairs (N + 1) → ℝ,
        ∫ τ : R → Fin (N + 1) → ℤˣ, G τ
          ∂(Measure.pi fun _ : R => Measure.count.tilted
            (fun a : Fin (N + 1) → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i : Fin (N + 1), (a i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  intro B E
  let e : R ≃ Fin (Fintype.card R) := Fintype.equivFin R
  have key := sk_cavity_path_square_le_exp_mul N (Fintype.card R) β q h hq
    (fun σ => G fun r => σ (e r)) (fun σ => hG _) t ht
  simpa only [integral_pi_count_tilted_reindex e] using key

end SpinGlasses
