/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GibbsMeasureNested
public import LeanMachineLearning.SpinGlasses.SKCavityGaussian
public import LeanMachineLearning.SpinGlasses.SKCavityInterpolation
public import LeanMachineLearning.SpinGlasses.SKCavityCoshEstimate
public import LeanMachineLearning.SpinGlasses.SKCavityFreeEnergy

/-!
# The last cavity step of the pair-perturbation estimate (Talagrand Eq. 1.182)

At the coupled endpoint the `(N+1)`-spin system at coefficient `β / √N` has the first `N` spins
distributed as an `N`-spin SK system perturbed by the cavity factor `cosh`; averaging the
cavity couplings bounds its overlap average by `cosh(2h) exp(2β²)` times the `N`-spin one.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Two-replica cavity identity on the last spin of `Fin (N+1) → ℤˣ`.**  For an observable
of the first `N` coordinates of two replicas, summing out the last spins gives the
`N`-spin two-replica average weighted by `cosh (L ρ) cosh (L ρ') / ⟨cosh L⟩²`. -/
theorem integral_prod_count_tilted_fin_snoc_cavity_units (N : ℕ)
    (A L : (Fin N → ℤˣ) → ℝ) (g : (Fin N → ℤˣ) → (Fin N → ℤˣ) → ℝ) :
    ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ),
        g (fun i => p.1 i.castSucc) (fun i => p.2 i.castSucc)
      ∂((Measure.count.tilted fun σ : Fin (N + 1) → ℤˣ =>
          A (fun i => σ i.castSucc) + (σ (Fin.last N) : ℝ) * L (fun i => σ i.castSucc)).prod
        (Measure.count.tilted fun σ : Fin (N + 1) → ℤˣ =>
          A (fun i => σ i.castSucc) + (σ (Fin.last N) : ℝ) * L (fun i => σ i.castSucc))) =
      (∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ),
          g p.1 p.2 * Real.cosh (L p.1) * Real.cosh (L p.2)
        ∂((Measure.count.tilted A).prod (Measure.count.tilted A))) /
        (∫ ρ, Real.cosh (L ρ) ∂Measure.count.tilted A) ^ 2 := by
  let e : ((Fin N → ℤˣ) × ℤˣ) ≃ (Fin (N + 1) → ℤˣ) :=
    (Equiv.prodComm (Fin N → ℤˣ) ℤˣ).trans (Fin.snocEquiv fun _ => ℤˣ)
  rw [integral_prod_count_tilted_equiv e _ (fun σ τ =>
    g (fun i => σ i.castSucc) (fun i => τ i.castSucc))]
  simp only [e, Equiv.trans_apply, Equiv.prodComm_apply, Fin.snocEquiv_apply,
    Fin.snoc_castSucc, Fin.snoc_last]
  exact integral_prod_count_tilted_units A L g

/-- The cavity average of a nonnegative observable is dominated by the `cosh`-weighted
`N`-spin average, since `⟨cosh L⟩ ≥ 1`. -/
theorem integral_prod_count_tilted_fin_snoc_cavity_units_le (N : ℕ)
    (A L : (Fin N → ℤˣ) → ℝ) (g : (Fin N → ℤˣ) → (Fin N → ℤˣ) → ℝ) (hg : ∀ a b, 0 ≤ g a b) :
    ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ),
        g (fun i => p.1 i.castSucc) (fun i => p.2 i.castSucc)
      ∂((Measure.count.tilted fun σ : Fin (N + 1) → ℤˣ =>
          A (fun i => σ i.castSucc) + (σ (Fin.last N) : ℝ) * L (fun i => σ i.castSucc)).prod
        (Measure.count.tilted fun σ : Fin (N + 1) → ℤˣ =>
          A (fun i => σ i.castSucc) + (σ (Fin.last N) : ℝ) * L (fun i => σ i.castSucc))) ≤
      ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ),
          g p.1 p.2 * Real.cosh (L p.1) * Real.cosh (L p.2)
        ∂((Measure.count.tilted A).prod (Measure.count.tilted A)) := by
  rw [integral_prod_count_tilted_fin_snoc_cavity_units]
  have hnum : 0 ≤ ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ),
      g p.1 p.2 * Real.cosh (L p.1) * Real.cosh (L p.2)
      ∂((Measure.count.tilted A).prod (Measure.count.tilted A)) :=
    integral_nonneg fun p => by
      have := Real.cosh_pos (L p.1); have := Real.cosh_pos (L p.2); have := hg p.1 p.2
      positivity
  have hcosh : 1 ≤ ∫ a, Real.cosh (L a) ∂Measure.count.tilted A := by
    have h1 : (1 : ℝ) = ∫ _ : Fin N → ℤˣ, (1 : ℝ) ∂Measure.count.tilted A := by
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
    rw [h1]
    exact integral_mono (integrable_const _) Integrable.of_finite fun a => Real.one_le_cosh (L a)
  exact div_le_self hnum (by nlinarith)

/-- Product formula for the two cavity `cosh` factors as a sum of two Gaussian `cosh` forms. -/
theorem cosh_mul_cosh_sk_cavity_eq (N : ℕ) (β h : ℝ) (σ τ : Fin N → ℤˣ) (w : Fin N → ℝ) :
    Real.cosh ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, w i * (σ i : ℝ) + h) *
        Real.cosh ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, w i * (τ i : ℝ) + h) =
      (Real.cosh (∑ i : Fin N, ((Real.sqrt (N : ℝ))⁻¹ * β * ((σ i : ℝ) + 1 * (τ i : ℝ))) * w i +
          2 * h) +
        Real.cosh (∑ i : Fin N, ((Real.sqrt (N : ℝ))⁻¹ * β * ((σ i : ℝ) + (-1) * (τ i : ℝ))) *
          w i + 0)) / 2 := by
  rw [Real.cosh_mul_cosh]
  have h1 : ∑ i : Fin N, ((Real.sqrt (N : ℝ))⁻¹ * β * ((σ i : ℝ) + 1 * (τ i : ℝ))) * w i =
      (Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, w i * (σ i : ℝ) +
        (Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, w i * (τ i : ℝ) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i : Fin N, ((Real.sqrt (N : ℝ))⁻¹ * β * ((σ i : ℝ) + (-1) * (τ i : ℝ))) * w i =
      (Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, w i * (σ i : ℝ) -
        (Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, w i * (τ i : ℝ) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h1, h2]
  congr 3 <;> ring_nf

/-- The two cavity `cosh` factors are Gaussian-integrable. -/
theorem integrable_cosh_mul_cosh_sk_cavity (N : ℕ) (β h : ℝ) (σ τ : Fin N → ℤˣ) :
    Integrable (fun w : Fin N → ℝ =>
        Real.cosh ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, w i * (σ i : ℝ) + h) *
        Real.cosh ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, w i * (τ i : ℝ) + h))
      (Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
  simp_rw [cosh_mul_cosh_sk_cavity_eq]
  exact ((integrable_cosh_sum_mul_gaussianReal _ _).add
    (integrable_cosh_sum_mul_gaussianReal _ _)).div_const 2

/-- Gaussian `cosh` product moment: `𝔼 cosh(x_σ + h) cosh(x_τ + h) ≤ cosh(2h) exp(2β²)` for
the N-spin cavity field `x_σ = β N^{-1/2} ∑ gᵢ σᵢ`. -/
theorem integral_cosh_mul_cosh_sk_cavity_le (N : ℕ) (hN : 0 < N) (β h : ℝ)
    (σ τ : Fin N → ℤˣ) :
    ∫ w : Fin N → ℝ,
        Real.cosh ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, w i * (σ i : ℝ) + h) *
        Real.cosh ((Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, w i * (τ i : ℝ) + h)
      ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) ≤
      Real.cosh (2 * h) * Real.exp (2 * β ^ 2) := by
  simp_rw [cosh_mul_cosh_sk_cavity_eq]
  rw [integral_div, integral_add (integrable_cosh_sum_mul_gaussianReal _ _)
    (integrable_cosh_sum_mul_gaussianReal _ _), integral_cosh_sum_mul_gaussianReal,
    integral_cosh_sum_mul_gaussianReal, Real.cosh_zero]
  have hq : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hv1 := sum_sq_sk_cavity_linear_combo_le N hN β 0 0 hq σ τ 1 (Or.inl rfl)
  have hv2 := sum_sq_sk_cavity_linear_combo_le N hN β 0 0 hq σ τ (-1) (Or.inr rfl)
  simp only [Real.cos_zero, Real.sin_zero, one_mul, zero_mul, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero] at hv1 hv2
  have e1 : Real.exp (∑ i : Fin N, ((Real.sqrt (N : ℝ))⁻¹ * β * ((σ i : ℝ) + 1 * (τ i : ℝ))) ^ 2 /
      2) ≤ Real.exp (2 * β ^ 2) := Real.exp_le_exp.2 (by
    rw [← Finset.sum_div]; simp only [one_mul]; linarith)
  have e2 : Real.exp (∑ i : Fin N, ((Real.sqrt (N : ℝ))⁻¹ * β *
      ((σ i : ℝ) + (-1) * (τ i : ℝ))) ^ 2 / 2) ≤ Real.exp (2 * β ^ 2) := Real.exp_le_exp.2 (by
    rw [← Finset.sum_div]; linarith)
  have hc := Real.one_le_cosh (2 * h)
  have hp := Real.cosh_pos (2 * h)
  nlinarith [mul_le_mul_of_nonneg_left e1 hp.le, mul_le_mul_of_nonneg_right hc (Real.exp_pos
    (2 * β ^ 2)).le, mul_le_mul_of_nonneg_left e2 (zero_le_one : (0:ℝ) ≤ 1)]

/-- **Final cavity step of Eq. (1.182).**  The overlap average of the first `N` coordinates of
the `(N+1)`-spin SK system at coefficient `β / √N` is at most `cosh(2h) exp(2β²)` times the
overlap average of the `N`-spin SK system at `β`. -/
theorem integral_sk_pair_perturb_cavity_le (N : ℕ) (hN : 0 < N) (β h q : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    (∫ g : FinPairs (N + 1) → ℝ, ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ),
        |(N : ℝ)⁻¹ * ∑ i : Fin N, (p.1 i.castSucc : ℝ) * (p.2 i.castSucc : ℝ) - q|
        ∂((Measure.count.tilted fun σ : Fin (N + 1) → ℤˣ => (Real.sqrt (N : ℝ))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
            h * ∑ i, (σ i : ℝ)).prod
          (Measure.count.tilted fun σ : Fin (N + 1) → ℤˣ => (Real.sqrt (N : ℝ))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
            h * ∑ i, (σ i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ≤
    Real.cosh (2 * h) * Real.exp (2 * β ^ 2) *
      ∫ g' : FinPairs N → ℝ, ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ),
        |(N : ℝ)⁻¹ * ∑ i : Fin N, (p.1 i : ℝ) * (p.2 i : ℝ) - q|
        ∂((Measure.count.tilted fun ρ : Fin N → ℤˣ => (Real.sqrt (N : ℝ))⁻¹ * β *
            (∑ p : FinPairs N, g' p * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) +
            h * ∑ i, (ρ i : ℝ)).prod
          (Measure.count.tilted fun ρ : Fin N → ℤˣ => (Real.sqrt (N : ℝ))⁻¹ * β *
            (∑ p : FinPairs N, g' p * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) +
            h * ∑ i, (ρ i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  have _ : Nonempty (Fin N → ℤˣ) := ⟨fun _ => 1⟩
  have _ : Nonempty (Fin (N + 1) → ℤˣ) := ⟨fun _ => 1⟩
  let A : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ := fun g' ρ => (Real.sqrt (N : ℝ))⁻¹ * β *
    (∑ p : FinPairs N, g' p * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) + h * ∑ i, (ρ i : ℝ)
  let L : (Fin N → ℝ) → (Fin N → ℤˣ) → ℝ := fun w ρ =>
    (Real.sqrt (N : ℝ))⁻¹ * β * ∑ i : Fin N, w i * (ρ i : ℝ) + h
  let Gm : (FinPairs N → ℝ) × (Fin N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun x σ =>
    A x.1 (fun i => σ i.castSucc) + (σ (Fin.last N) : ℝ) * L x.2 (fun i => σ i.castSucc)
  let fN : (Fin N → ℤˣ) → (Fin N → ℤˣ) → ℝ := fun a b =>
    |(N : ℝ)⁻¹ * ∑ i : Fin N, (a i : ℝ) * (b i : ℝ) - q|
  let Ff : (FinPairs N → ℝ) × (Fin N → ℝ) → ℝ := fun x =>
    ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ),
      fN (fun i => p.1 i.castSucc) (fun i => p.2 i.castSucc)
      ∂((Measure.count.tilted (Gm x)).prod (Measure.count.tilted (Gm x)))
  have hGm : ∀ a, Measurable fun x : (FinPairs N → ℝ) × (Fin N → ℝ) => Gm x a := fun a => by
    simp only [Gm, A, L]; fun_prop
  have hFm : Measurable Ff :=
    measurable_integral_prod_count_tilted (g := fun x a => Gm x a) hGm
      (Θ := fun _ a b => fN (fun i => a i.castSucc) (fun i => b i.castSucc))
      (fun _ _ => measurable_const)
  have hfN0 : ∀ a b, 0 ≤ fN a b := fun a b => abs_nonneg _
  have hfN2 : ∀ a b, fN a b ≤ 2 := fun a b => abs_sk_overlap_N_sub_le_two N hN q hq a b
  have hFb : ∀ x, |Ff x| ≤ 2 := fun x => by
    have h := norm_integral_le_of_norm_le_const
      (μ := (Measure.count.tilted (Gm x)).prod (Measure.count.tilted (Gm x)))
      (f := fun p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ) =>
        fN (fun i => p.1 i.castSucc) (fun i => p.2 i.castSucc)) (C := 2)
      (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hfN0 _ _)]; exact hfN2 _ _)
    simpa using h
  have hFint : Integrable Ff ((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin N => gaussianReal 0 1)) :=
    Integrable.of_bound hFm.aestronglyMeasurable 2 (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hFb x)
  have hsplit : ∀ g : FinPairs (N + 1) → ℝ,
      (fun σ : Fin (N + 1) → ℤˣ => (Real.sqrt (N : ℝ))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
        h * ∑ i, (σ i : ℝ)) =
      Gm (fun p => g (⟨(p.val.1.castSucc, p.val.2.castSucc),
          Fin.castSucc_lt_castSucc_iff.mpr p.property⟩ : FinPairs (N + 1)),
        fun i => g (⟨(i.castSucc, Fin.last N),
          Fin.castSucc_lt_last i⟩ : FinPairs (N + 1))) := fun g => by
    funext σ
    simp only [Gm, A, L]
    rw [sum_sk_pairs_succ_cavity, Fin.sum_univ_castSucc]
    ring
  have hstepB : (∫ g : FinPairs (N + 1) → ℝ,
      Ff (fun p => g (⟨(p.val.1.castSucc, p.val.2.castSucc),
          Fin.castSucc_lt_castSucc_iff.mpr p.property⟩ : FinPairs (N + 1)),
        fun i => g (⟨(i.castSucc, Fin.last N),
          Fin.castSucc_lt_last i⟩ : FinPairs (N + 1)))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      ∫ x, Ff x ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1)) := by
    exact integral_comp_sk_cavity_disorder N Ff
  calc _ = ∫ g : FinPairs (N + 1) → ℝ,
      Ff (fun p => g (⟨(p.val.1.castSucc, p.val.2.castSucc),
          Fin.castSucc_lt_castSucc_iff.mpr p.property⟩ : FinPairs (N + 1)),
        fun i => g (⟨(i.castSucc, Fin.last N),
          Fin.castSucc_lt_last i⟩ : FinPairs (N + 1)))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
        refine integral_congr_ae (ae_of_all _ fun g => ?_)
        simp only [Ff]
        rw [hsplit g]
    _ = ∫ x, Ff x ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin N => gaussianReal 0 1)) := hstepB
    _ = ∫ g', ∫ w, Ff (g', w) ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := integral_prod _ hFint
    _ ≤ ∫ g', (Real.cosh (2 * h) * Real.exp (2 * β ^ 2)) * ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ),
        fN p.1 p.2 ∂((Measure.count.tilted (A g')).prod (Measure.count.tilted (A g')))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
        have hA : ∀ ρ, Measurable fun g' : FinPairs N → ℝ => A g' ρ := fun ρ => by
          simp only [A]; fun_prop
        refine integral_mono hFint.integral_prod_left
          ((integrable_integral_prod_count_tilted_det (P := Measure.pi fun _ : FinPairs N =>
            gaussianReal 0 1) hA fun a b => fN a b).const_mul _) fun g' => ?_
        have hint : ∀ a b, Integrable (fun w : Fin N → ℝ =>
            Real.cosh (L w a) * Real.cosh (L w b))
            (Measure.pi fun _ : Fin N => gaussianReal 0 1) := fun a b =>
          integrable_cosh_mul_cosh_sk_cavity N β h a b
        have hle : ∀ a b, (∫ w : Fin N → ℝ, Real.cosh (L w a) * Real.cosh (L w b)
            ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)) ≤
            Real.cosh (2 * h) * Real.exp (2 * β ^ 2) := fun a b =>
          integral_cosh_mul_cosh_sk_cavity_le N hN β h a b
        have hm := integral_prod_count_tilted_mul_le (Measure.pi fun _ : Fin N => gaussianReal 0 1)
          (A g') fN (fun a b w => Real.cosh (L w a) * Real.cosh (L w b))
          (Real.cosh (2 * h) * Real.exp (2 * β ^ 2)) hint hle
        have hpt : ∀ w, Ff (g', w) ≤ ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ),
            |fN p.1 p.2| * (Real.cosh (L w p.1) * Real.cosh (L w p.2))
            ∂((Measure.count.tilted (A g')).prod (Measure.count.tilted (A g'))) := fun w => by
          have key := integral_prod_count_tilted_fin_snoc_cavity_units_le N (A g') (L w) fN hfN0
          have e : (fun p : (Fin N → ℤˣ) × (Fin N → ℤˣ) =>
              fN p.1 p.2 * Real.cosh (L w p.1) * Real.cosh (L w p.2)) = fun p =>
              |fN p.1 p.2| * (Real.cosh (L w p.1) * Real.cosh (L w p.2)) := by
            funext p
            rw [abs_of_nonneg (hfN0 _ _), mul_assoc]
          rw [e] at key
          exact key
        have heq : Real.cosh (2 * h) * Real.exp (2 * β ^ 2) *
            (∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ), |fN p.1 p.2|
              ∂((Measure.count.tilted (A g')).prod (Measure.count.tilted (A g')))) =
            Real.cosh (2 * h) * Real.exp (2 * β ^ 2) *
            ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ), fN p.1 p.2
              ∂((Measure.count.tilted (A g')).prod (Measure.count.tilted (A g'))) := by
          congr 1
          exact integral_congr_ae (ae_of_all _ fun p => abs_of_nonneg (hfN0 _ _))
        refine (integral_mono ?_ ?_ hpt).trans (hm.trans_eq heq)
        · exact Integrable.of_bound (hFm.comp measurable_prodMk_left).aestronglyMeasurable 2
            (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hFb _)
        · exact integrable_integral_prod_count_tilted (Measure.pi fun _ : Fin N => gaussianReal 0 1)
            (A g') (fun a b w => |fN a b| * (Real.cosh (L w a) * Real.cosh (L w b)))
            fun a b => (hint a b).const_mul _
    _ = _ := integral_const_mul _ _

/-- **Talagrand Eq. (1.174) for the overlap average.**  The two-block endpoint average at
`s = 0` of the pair-perturbation path (old pairs with coefficient `β / √(N+1)` and an independent
pair block with coefficient `β / √(N (N+1))`) equals the `(N+1)`-spin average at the single
coefficient `β / √N = β₊ / √(N+1)`. -/
theorem integral_sk_pair_perturb_endpoint_transport (N : ℕ) (hN : 0 < N) (β h q : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    (∫ η : FinPairs (N + 1) → ℝ, ∫ ω : (FinPairs (N + 1) → ℝ) × ℝ,
      ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ),
        |(N : ℝ)⁻¹ * ∑ i : Fin N, (p.1 i.castSucc : ℝ) * (p.2 i.castSucc : ℝ) - q|
        ∂((Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
              ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            ((Real.sqrt (N + 1 : ℝ))⁻¹ * β *
              (∑ p : FinPairs (N + 1), η p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i, (a i : ℝ))).prod
          (Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
            (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
              ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            ((Real.sqrt (N + 1 : ℝ))⁻¹ * β *
              (∑ p : FinPairs (N + 1), η p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
              h * ∑ i, (a i : ℝ))))
      ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
    ∫ g : FinPairs (N + 1) → ℝ, ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ),
        |(N : ℝ)⁻¹ * ∑ i : Fin N, (p.1 i.castSucc : ℝ) * (p.2 i.castSucc : ℝ) - q|
        ∂((Measure.count.tilted fun σ : Fin (N + 1) → ℤˣ => (Real.sqrt (N : ℝ))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
            h * ∑ i, (σ i : ℝ)).prod
          (Measure.count.tilted fun σ : Fin (N + 1) → ℤˣ => (Real.sqrt (N : ℝ))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
            h * ∑ i, (σ i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  have _ : Nonempty (Fin (N + 1) → ℤˣ) := ⟨fun _ => 1⟩
  let fR : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
    |(N : ℝ)⁻¹ * ∑ i : Fin N, (a i.castSucc : ℝ) * (b i.castSucc : ℝ) - q|
  let Eg : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun G σ =>
    (∑ p : FinPairs (N + 1), G p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ)
  let f : (FinPairs (N + 1) → ℝ) → ℝ := fun G =>
    ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ), fR p.1 p.2
      ∂((Measure.count.tilted (Eg G)).prod (Measure.count.tilted (Eg G)))
  have hEg : ∀ a, Measurable fun G : FinPairs (N + 1) → ℝ => Eg G a := fun a => by
    simp only [Eg]; fun_prop
  have hf : Measurable f := measurable_integral_prod_count_tilted (g := fun G a => Eg G a) hEg
    (Θ := fun _ a b => fR a b) (fun _ _ => measurable_const)
  have hfb : ∀ G, |f G| ≤ 2 := fun G => by
    have h := norm_integral_le_of_norm_le_const
      (μ := (Measure.count.tilted (Eg G)).prod (Measure.count.tilted (Eg G)))
      (f := fun p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ) => fR p.1 p.2) (C := 2)
      (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
        exact abs_sk_overlap_N_sub_le_two N hN q hq _ _)
    simpa using h
  have hvar := (sk_beta_plus_variance N β hN).symm
  have hRHS : (∫ g : FinPairs (N + 1) → ℝ, ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ),
        fR p.1 p.2
        ∂((Measure.count.tilted fun σ : Fin (N + 1) → ℤˣ => (Real.sqrt (N : ℝ))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
            h * ∑ i, (σ i : ℝ)).prod
          (Measure.count.tilted fun σ : Fin (N + 1) → ℤˣ => (Real.sqrt (N : ℝ))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
            h * ∑ i, (σ i : ℝ)))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      ∫ g : FinPairs (N + 1) → ℝ, f (fun p => (Real.sqrt (N : ℝ))⁻¹ * β * g p)
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    have : (fun σ : Fin (N + 1) → ℤˣ => (Real.sqrt (N : ℝ))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
            h * ∑ i, (σ i : ℝ)) =
        Eg (fun p => (Real.sqrt (N : ℝ))⁻¹ * β * g p) := funext fun σ => by
      simp only [Eg, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun p _ => by ring
    simp only [f, this]
  rw [hRHS, integral_pi_gaussianReal_scale_eq_prod_linear_combo
    ((Real.sqrt (N + 1 : ℝ))⁻¹ * β) (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹)
    ((Real.sqrt (N : ℝ))⁻¹ * β) hvar hf]
  have hfint : Integrable (fun q : (FinPairs (N + 1) → ℝ) × (FinPairs (N + 1) → ℝ) =>
      f (fun i => (Real.sqrt (N + 1 : ℝ))⁻¹ * β * q.1 i +
        β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ * q.2 i))
      ((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) := by
    refine Integrable.of_bound (hf.comp ?_).aestronglyMeasurable 2
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hfb _)
    exact measurable_pi_iff.2 fun i =>
      (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).add
        (measurable_const.mul ((measurable_pi_apply i).comp measurable_snd))
  rw [integral_prod _ hfint]
  refine integral_congr_ae (ae_of_all _ fun η => ?_)
  have hen : ∀ u : FinPairs (N + 1) → ℝ, (fun a : Fin (N + 1) → ℤˣ =>
      (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
        ∑ p : FinPairs (N + 1), u p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      ((Real.sqrt (N + 1 : ℝ))⁻¹ * β *
        (∑ p : FinPairs (N + 1), η p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i, (a i : ℝ))) =
      Eg (fun i => (Real.sqrt (N + 1 : ℝ))⁻¹ * β * η i +
        β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ * u i) := fun u => funext fun a => by
    simp only [Eg, Finset.mul_sum, add_mul, Finset.sum_add_distrib]
    ring_nf
  simp only [hen]
  exact integral_prod_fun_fst_of_isProbabilityMeasure (Measure.pi fun _ : FinPairs (N + 1) =>
    gaussianReal 0 1) (gaussianReal 0 1) (fun u => f (fun i =>
      (Real.sqrt (N + 1 : ℝ))⁻¹ * β * η i + β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ * u i))

end SpinGlasses
