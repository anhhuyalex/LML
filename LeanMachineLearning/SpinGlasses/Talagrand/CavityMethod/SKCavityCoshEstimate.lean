/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKCavityFreeEnergy

/-!
# The cavity `cosh` estimate (Talagrand Eq. 1.181)

The interpolation `s ↦ 𝔼 log ⟨cosh(cos s X + sin s Y + h)⟩` between the cavity field
(`s = 0`) and the decoupled Gaussian field (`s = π / 2`) has derivative `sin s cos s D(s)`
with `D(s)` uniformly within `K1 ν` of `-β² (1 - q)`.  Combined with the endpoint lemma
`sk_cavity_cosh_estimate_of_deriv_bound` this proves the hypothesis `h_cosh` of
`sk_cavity_free_energy_increment_le`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- The overlap deviation `R - q` of two `N`-spin configurations has modulus at most `2`. -/
theorem abs_sk_overlap_N_sub_le_two (N : ℕ) (hN : 0 < N) (q : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (a b : Fin N → ℤˣ) :
    |(N : ℝ)⁻¹ * ∑ i, (a i : ℝ) * (b i : ℝ) - q| ≤ 2 := by
  have _ : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  simpa only [Fintype.card_fin, dotProduct] using
    abs_card_inv_mul_dotProduct_sub_le_two
    (fun i : Fin N => (a i : ℝ)) (fun i : Fin N => (b i : ℝ))
    (fun i => abs_units_cast_le_one (a i)) (fun i => abs_units_cast_le_one (b i)) q hq

/-- The signed overlap term of the cavity bracket is bounded by `2 β²` for every base energy:
both the Ising signs and the normalized overlap are bounded, and all measures involved are
probability measures. -/
theorem abs_integral_integral_sk_cavity_signed_overlap_le_two_sq (N : ℕ) (β h q s : ℝ)
    (hN : 0 < N) (hq : q ∈ Set.Icc (0 : ℝ) 1) (A : (Fin N → ℤˣ) → ℝ) :
    let P := (Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)
    let L : (Fin N → ℤˣ) → (Fin N → ℝ) × ℝ → ℝ := fun ρ ω =>
      Real.cos s * ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, ω.1 i * (ρ i : ℝ)) +
      Real.sin s * (β * ω.2 * Real.sqrt q) + h
    |∫ ω, ∫ p : ((Fin N → ℤˣ) × ℤˣ) × ((Fin N → ℤˣ) × ℤˣ),
      (p.1.2 : ℝ) * (p.2.2 : ℝ) *
        (β ^ 2 * ((N : ℝ)⁻¹ * ∑ i, (p.1.1 i : ℝ) * (p.2.1 i : ℝ) - q))
      ∂((Measure.count.tilted fun x => A x.1 + (x.2 : ℝ) * L x.1 ω).prod
        (Measure.count.tilted fun x => A x.1 + (x.2 : ℝ) * L x.1 ω)) ∂P| ≤ 2 * β ^ 2 := by
  intro P L
  have hG : ∀ p : ((Fin N → ℤˣ) × ℤˣ) × ((Fin N → ℤˣ) × ℤˣ),
      |(p.1.2 : ℝ) * (p.2.2 : ℝ) *
        (β ^ 2 * ((N : ℝ)⁻¹ * ∑ i, (p.1.1 i : ℝ) * (p.2.1 i : ℝ) - q))| ≤ 2 * β ^ 2 := by
    intro p
    rw [abs_mul, abs_mul, abs_mul, abs_sq]
    have h1 := abs_units_cast_le_one p.1.2
    have h2 := abs_units_cast_le_one p.2.2
    have h3 := abs_sk_overlap_N_sub_le_two N hN q hq p.1.1 p.2.1
    have h4 : |((p.1.2 : ℤ) : ℝ)| * |((p.2.2 : ℤ) : ℝ)| ≤ 1 := by
      calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have h5 : 0 ≤ β ^ 2 := sq_nonneg β
    calc |((p.1.2 : ℤ) : ℝ)| * |((p.2.2 : ℤ) : ℝ)| *
          (β ^ 2 * |(N : ℝ)⁻¹ * ∑ i, (p.1.1 i : ℝ) * (p.2.1 i : ℝ) - q|)
        ≤ 1 * (β ^ 2 * 2) := mul_le_mul h4 (mul_le_mul_of_nonneg_left h3 h5)
          (by positivity) zero_le_one
      _ = 2 * β ^ 2 := by ring
  exact abs_integral_integral_le_of_forall_le P _ _ hG


/-- **Derivative of the cavity `cosh` interpolation (Talagrand Eqs. 1.178--1.181).**
For any measurable family of old-system energies `A η` over a probability space `P₀`, the path
`s ↦ 𝔼 log ⟨cosh(cos s X + sin s Y + h)⟩_{A η}` has derivative `sin t cos t D` at every `t`,
where `D` is within `β² cosh(2h) exp(2β²) ν` of `-β² (1 - q)`, `ν` the average of `|R - q|`. -/
theorem exists_hasDerivAt_sk_cavity_cosh_path
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (N : ℕ) (hN : 0 < N) (β h q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (A : Ω₀ → (Fin N → ℤˣ) → ℝ) (hA : ∀ ρ, Measurable fun η => A η ρ) (t : ℝ) :
    ∃ D : ℝ, HasDerivAt (fun s => ∫ η, ∫ ω : (Fin N → ℝ) × ℝ,
        Real.log (∫ ρ : Fin N → ℤˣ, Real.cosh (Real.cos s *
          ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, ω.1 i * (ρ i : ℝ)) +
          Real.sin s * (β * ω.2 * Real.sqrt q) + h) ∂Measure.count.tilted (A η))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) ∂P₀)
      (Real.sin t * Real.cos t * D) t ∧
      |D - (-β ^ 2 * (1 - q))| ≤
        β ^ 2 * (Real.cosh (2 * h) * Real.exp (2 * β ^ 2)) *
          ∫ η, ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ),
            |(N : ℝ)⁻¹ * ∑ i, (p.1 i : ℝ) * (p.2 i : ℝ) - q|
            ∂((Measure.count.tilted (A η)).prod (Measure.count.tilted (A η))) ∂P₀ := by
  have _ : Nonempty (Fin N → ℤˣ) := ⟨fun _ => 1⟩
  have hq0 : 0 ≤ q := hq.1
  let P : Measure ((Fin N → ℝ) × ℝ) :=
    (Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)
  let X : (Fin N → ℤˣ) → (Fin N → ℝ) × ℝ → ℝ := fun σ ω =>
    (Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, ω.1 i * (σ i : ℝ)
  let Y : (Fin N → ℤˣ) → (Fin N → ℝ) × ℝ → ℝ := fun _ ω => β * ω.2 * Real.sqrt q
  have hXm : ∀ σ, Measurable (X σ) := fun σ => by simp only [X]; fun_prop
  have hYm : ∀ σ, Measurable (Y σ) := fun σ => by simp only [Y]; fun_prop
  -- the bracket integral at fixed base disorder
  let G : ((Fin N → ℤˣ) × ℤˣ) × ((Fin N → ℤˣ) × ℤˣ) → ℝ := fun p =>
    (p.1.2 : ℝ) * (p.2.2 : ℝ) *
      (β ^ 2 * ((N : ℝ)⁻¹ * ∑ i, (p.1.1 i : ℝ) * (p.2.1 i : ℝ) - q))
  let J : Ω₀ → ℝ → ℝ := fun η s => ∫ ω, ∫ p, G p ∂((Measure.count.tilted fun x =>
      A η x.1 + (x.2 : ℝ) * (Real.cos s * X x.1 ω + Real.sin s * Y x.1 ω + h)).prod
      (Measure.count.tilted fun x =>
      A η x.1 + (x.2 : ℝ) * (Real.cos s * X x.1 ω + Real.sin s * Y x.1 ω + h))) ∂P
  have hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P := by
    convert hasGaussianLaw_sk_cavity_N_fields N β q using 1
    ext ω (σ | σ) <;> rfl
  have hX : ∀ σ, ∫ ω, X σ ω ∂P = 0 := fun σ => integral_sk_cavity_N_edge_field_eq_zero N β σ
  have hY : ∀ σ, ∫ ω, Y σ ω ∂P = 0 := fun σ => integral_sk_cavity_N_scalar_field_eq_zero N β q
  have h0 : ∀ σ τ, ∫ ω, X σ ω * Y τ ω ∂P = 0 := fun σ τ =>
    integral_sk_cavity_N_edge_mul_scalar_eq_zero N β q σ τ
  have hXi : ∀ σ, Integrable (X σ) P := fun σ => (hXY.eval (Sum.inl σ)).integrable
  have hYi : ∀ σ, Integrable (Y σ) P := fun σ => (hXY.eval (Sum.inr σ)).integrable
  let Lf : ℝ → (Fin N → ℝ) × ℝ → (Fin N → ℤˣ) → ℝ := fun s ω a =>
    Real.cos s * X a ω + Real.sin s * Y a ω + h
  have hLm : ∀ s a, Measurable fun ω => Lf s ω a := fun s a =>
    (((hXm a).const_mul _).add ((hYm a).const_mul _)).add_const _
  have hLi : ∀ s a, Integrable (fun ω => Lf s ω a) P := fun s a =>
    (((hXi a).const_mul _).add ((hYi a).const_mul _)).add (integrable_const _)
  -- the bracket identity at fixed base disorder
  have key : ∀ η s, (∫ ω, ∫ p : ((Fin N → ℤˣ) × ℤˣ) × ((Fin N → ℤˣ) × ℤˣ),
      Real.sin s * Real.cos s *
        ((∫ ω', (p.1.2 : ℝ) * Y p.1.1 ω' * ((p.1.2 : ℝ) * Y p.1.1 ω') ∂P -
            ∫ ω', (p.1.2 : ℝ) * X p.1.1 ω' * ((p.1.2 : ℝ) * X p.1.1 ω') ∂P) -
          (∫ ω', (p.1.2 : ℝ) * Y p.1.1 ω' * ((p.2.2 : ℝ) * Y p.2.1 ω') ∂P -
            ∫ ω', (p.1.2 : ℝ) * X p.1.1 ω' * ((p.2.2 : ℝ) * X p.2.1 ω') ∂P))
      ∂((Measure.count.tilted fun x : (Fin N → ℤˣ) × ℤˣ =>
          Real.cos s * ((x.2 : ℝ) * X x.1 ω) + Real.sin s * ((x.2 : ℝ) * Y x.1 ω) +
          A η x.1 + (x.2 : ℝ) * h).prod
        (Measure.count.tilted fun x : (Fin N → ℤˣ) × ℤˣ =>
          Real.cos s * ((x.2 : ℝ) * X x.1 ω) + Real.sin s * ((x.2 : ℝ) * Y x.1 ω) +
          A η x.1 + (x.2 : ℝ) * h)) ∂P) =
      Real.sin s * Real.cos s * (-β ^ 2 * (1 - q) + J η s) := by
    intro η s
    have hfun : ∀ ω : (Fin N → ℝ) × ℝ, (fun x : (Fin N → ℤˣ) × ℤˣ =>
        Real.cos s * ((x.2 : ℝ) * X x.1 ω) + Real.sin s * ((x.2 : ℝ) * Y x.1 ω) +
          A η x.1 + (x.2 : ℝ) * h) = fun x => A η x.1 +
        (x.2 : ℝ) * (Real.cos s * X x.1 ω + Real.sin s * Y x.1 ω + h) :=
      fun ω => funext fun x => by ring
    simp only [hfun]
    exact integral_integral_sk_cavity_covariance_bracket_eq N hN β h q s hq0 (A η)
  have hJm : ∀ s, AEStronglyMeasurable (fun η => J η s) P₀ := by
    intro s
    have hm := measurable_integral_prod_count_tilted_units_mul
      (W := Ω₀ × ((Fin N → ℝ) × ℝ)) (A := fun w a => A w.1 a)
      (L := fun w a => Lf s w.2 a) (fun a => (hA a).comp measurable_fst)
      (fun a => (hLm s a).comp measurable_snd)
      (fun σ τ => β ^ 2 * ((N : ℝ)⁻¹ * ∑ i, (σ i : ℝ) * (τ i : ℝ) - q))
    exact hm.aestronglyMeasurable.integral_prod_right'
  have hJb : ∀ η s, |J η s| ≤ 2 * β ^ 2 := fun η s =>
    abs_integral_integral_sk_cavity_signed_overlap_le_two_sq N β h q s hN hq (A η)
  have hJi : ∀ s, Integrable (fun η => J η s) P₀ := fun s =>
    Integrable.of_bound (hJm s) (2 * β ^ 2)
      (ae_of_all _ fun η => by simpa only [Real.norm_eq_abs] using hJb η s)
  have hC : |-β ^ 2 * (1 - q)| ≤ β ^ 2 := by
    rw [abs_le]
    have h1 := mul_nonneg (sq_nonneg β) (sub_nonneg.2 hq.2)
    have h2 := mul_nonneg (sq_nonneg β) hq0
    constructor <;> nlinarith [sq_nonneg β]
  have hder := hasDerivAt_integral_conditional_log_integral_cosh_trig P₀ (X := X) (Y := Y)
    hXm hYm hXY hX hY h0 A (fun _ => h) t
    (fun s => aestronglyMeasurable_integral_log_integral_cosh_count_tilted P₀ P hA
      (L := Lf s) (hLm s))
    (by
      exact (((hJm t).const_add (-β ^ 2 * (1 - q))).const_mul
        (Real.sin t * Real.cos t)).congr (ae_of_all _ fun η => (key η t).symm))
    (integrable_integral_log_integral_cosh_count_tilted P₀ P hA (L := Lf t) (hLm t) (hLi t))
    (3 * β ^ 2) (fun η s => by
      refine (le_of_eq_of_le (congrArg abs (key η s)) ?_)
      rw [abs_mul]
      have h1 := Real.abs_sin_mul_cos_le_half s
      have h2 := (abs_add_le _ _).trans (add_le_add hC (hJb η s))
      calc _ ≤ (1 / 2) * (3 * β ^ 2) := mul_le_mul h1 (by linarith) (abs_nonneg _) (by positivity)
        _ ≤ 3 * β ^ 2 := by nlinarith [sq_nonneg β])
  refine ⟨-β ^ 2 * (1 - q) + ∫ η, J η t ∂P₀, hder.congr_deriv ?_, ?_⟩
  · have hJint := hJi t
    calc _ = ∫ η, Real.sin t * Real.cos t * (-β ^ 2 * (1 - q) + J η t) ∂P₀ :=
          integral_congr_ae (ae_of_all _ fun η => key η t)
      _ = Real.sin t * Real.cos t * (-β ^ 2 * (1 - q) + ∫ η, J η t ∂P₀) := by
          rw [integral_const_mul, integral_const_add_of_isProbabilityMeasure P₀ _ _ hJint]
  · rw [add_sub_cancel_left]
    simpa only [J] using abs_integral_integral_sk_cavity_signed_overlap_le P₀ N β h q t hN hq A hA


/-- **Talagrand Eq. (1.181): the cavity `cosh` estimate.**  The expected log of the Gibbs
average of `cosh(N^{-1/2} β ∑ gᵢ ρᵢ + h)` over the cavity couplings and the old couplings is
within `β² cosh(2h) exp(2β²) ν` of `(β²/2)(1 - q) + 𝔼 log cosh(β z √q + h)`, where `ν` is the
old-system average of `|R_{1,2} - q|`.  This is the hypothesis `h_cosh` of
`sk_cavity_free_energy_increment_le`. -/
theorem sk_cavity_cosh_estimate (N : ℕ) (β h q : ℝ) (hN : 0 < N)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    |(∫ w : (FinPairs N → ℝ) × (Fin N → ℝ),
      Real.log (∫ ρ : Fin N → ℤˣ,
        Real.cosh ((Real.sqrt (N : ℝ))⁻¹ * β *
          ∑ i : Fin N, w.2 i * (ρ i : ℝ) + h)
        ∂Measure.count.tilted (fun ρ =>
          (Real.sqrt (N : ℝ))⁻¹ * β *
            (∑ p : FinPairs N, w.1 p * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) +
            h * ∑ i, (ρ i : ℝ)))
      ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1))) -
      (β ^ 2 / 2 * (1 - q) +
        ∫ z : ℝ, Real.log (Real.cosh (β * z * Real.sqrt q + h)) ∂gaussianReal 0 1)| ≤
    (β ^ 2 * Real.cosh (2 * h) * Real.exp (2 * β ^ 2)) *
      ∫ g' : FinPairs N → ℝ,
        ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ),
          |(N : ℝ)⁻¹ * ∑ i : Fin N, (p.1 i : ℝ) * (p.2 i : ℝ) - q|
          ∂((Measure.count.tilted (fun ρ =>
            (Real.sqrt (N : ℝ))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) +
              h * ∑ i, (ρ i : ℝ))).prod
            (Measure.count.tilted (fun ρ =>
              (Real.sqrt (N : ℝ))⁻¹ * β *
                (∑ p : FinPairs N, g' p * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) +
                h * ∑ i, (ρ i : ℝ))))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  have _ : Nonempty (Fin N → ℤˣ) := ⟨fun _ => 1⟩
  let A : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ := fun g' ρ =>
    (Real.sqrt (N : ℝ))⁻¹ * β *
      (∑ p : FinPairs N, g' p * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) + h * ∑ i, (ρ i : ℝ)
  have hA : ∀ ρ, Measurable fun η => A η ρ := fun ρ => by simp only [A]; fun_prop
  let ν : ℝ := ∫ g' : FinPairs N → ℝ,
    ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ),
      |(N : ℝ)⁻¹ * ∑ i : Fin N, (p.1 i : ℝ) * (p.2 i : ℝ) - q|
      ∂((Measure.count.tilted (A g')).prod (Measure.count.tilted (A g')))
    ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
  have hν : 0 ≤ ν := integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _
  have hK1 : 0 ≤ β ^ 2 * Real.cosh (2 * h) * Real.exp (2 * β ^ 2) := by positivity
  let φ : ℝ → ℝ := fun s => ∫ η, ∫ ω : (Fin N → ℝ) × ℝ,
    Real.log (∫ ρ : Fin N → ℤˣ, Real.cosh (Real.cos s *
      ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, ω.1 i * (ρ i : ℝ)) +
      Real.sin s * (β * ω.2 * Real.sqrt q) + h) ∂Measure.count.tilted (A η))
    ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
    ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
  have hd : ∀ s, ∃ D, HasDerivAt φ (Real.sin s * Real.cos s * D) s ∧
      (s ∈ Set.Icc 0 (Real.pi / 2) →
        |D - (-β ^ 2 * (1 - q))| ≤ 2 * (β ^ 2 * Real.cosh (2 * h) * Real.exp (2 * β ^ 2)) * ν) := by
    intro s
    obtain ⟨D, hD, hDb⟩ := exists_hasDerivAt_sk_cavity_cosh_path
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) N hN β h q hq A hA s
    refine ⟨D, hD, fun _ => hDb.trans ?_⟩
    have : 0 ≤ β ^ 2 * (Real.cosh (2 * h) * Real.exp (2 * β ^ 2)) * ν := by positivity
    nlinarith
  have hpi : φ (Real.pi / 2) =
      ∫ z : ℝ, Real.log (Real.cosh (β * z * Real.sqrt q + h)) ∂gaussianReal 0 1 := by
    simp only [φ, Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul, zero_add,
      integral_const, probReal_univ, one_smul]
    rw [integral_fun_snd (μ := Measure.pi fun _ : Fin N => gaussianReal 0 1)
      (ν := gaussianReal 0 1) fun z => Real.log (Real.cosh (β * z * Real.sqrt q + h))]
    simp
  have h0 : φ 0 = ∫ w : (FinPairs N → ℝ) × (Fin N → ℝ),
      Real.log (∫ ρ : Fin N → ℤˣ,
        Real.cosh ((Real.sqrt (N : ℝ))⁻¹ * β *
          ∑ i : Fin N, w.2 i * (ρ i : ℝ) + h)
        ∂Measure.count.tilted (A w.1))
      ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1)) := by
    have hid : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) :=
      (memLp_id_gaussianReal 1).integrable le_rfl
    have hu : ∀ ρ : Fin N → ℤˣ, Integrable (fun u : Fin N → ℝ =>
        (Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, u i * (ρ i : ℝ) + h)
        (Measure.pi fun _ : Fin N => gaussianReal 0 1) := fun ρ =>
      ((integrable_finsetSum _ fun i _ =>
        (integrable_eval (μ := fun _ : Fin N => gaussianReal 0 1) hid).mul_const _).const_mul
        _).add (integrable_const _)
    have hF : Integrable (fun w : (FinPairs N → ℝ) × (Fin N → ℝ) =>
        Real.log (∫ ρ : Fin N → ℤˣ, Real.cosh ((Real.sqrt (N : ℝ))⁻¹ * β *
          ∑ i : Fin N, w.2 i * (ρ i : ℝ) + h) ∂Measure.count.tilted (A w.1)))
        ((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin N => gaussianReal 0 1)) := by
      refine Integrable.mono' (integrable_finsetSum (Finset.univ : Finset (Fin N → ℤˣ))
        fun ρ _ => ((hu ρ).comp_snd (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)).abs)
        (measurable_log_integral_cosh_count_tilted (A := fun w a => A w.1 a)
          (L := fun (w : (FinPairs N → ℝ) × (Fin N → ℝ)) ρ =>
            (Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, w.2 i * (ρ i : ℝ) + h)
          (fun a => (hA a).comp measurable_fst)
          (fun a => by fun_prop)).aestronglyMeasurable (ae_of_all _ fun w => ?_)
      rw [Real.norm_eq_abs]
      exact abs_log_integral_cosh_count_tilted_le_sum_abs (A w.1) _
    simp only [φ, Real.cos_zero, Real.sin_zero, one_mul, zero_mul, add_zero]
    rw [integral_prod _ hF]
    refine integral_congr_ae (ae_of_all _ fun η => ?_)
    dsimp only
    rw [integral_fun_fst (μ := Measure.pi fun _ : Fin N => gaussianReal 0 1)
      (ν := gaussianReal 0 1) fun u => Real.log (∫ ρ : Fin N → ℤˣ,
        Real.cosh ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, u i * (ρ i : ℝ) + h)
        ∂Measure.count.tilted (A η))]
    simp
  exact sk_cavity_cosh_estimate_of_deriv_bound β q _ _ ν _ φ h0 hpi hd

end SpinGlasses
