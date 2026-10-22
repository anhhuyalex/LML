/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKPairPerturbGaussian
public import LeanMachineLearning.SpinGlasses.GibbsMeasureNested
public import LeanMachineLearning.SpinGlasses.GaussianInterpolationConditional
public import LeanMachineLearning.SpinGlasses.SKCavityFreeEnergy
public import LeanMachineLearning.SpinGlasses.SKCavityCoshEstimate
public import LeanMachineLearning.SpinGlasses.SKCavityBounds
public import LeanMachineLearning.SpinGlasses.SKCavityDomination
public import LeanMachineLearning.SpinGlasses.SKPairPerturbCavity

/-!
# The pair-perturbation estimate (Talagrand Eq. 1.182)

The path `s ↦ 𝔼 log ⟨exp(cos s u + sin s v)⟩` between the pair-perturbed `(N+1)`-spin system
(`s = 0`) and the decoupled scalar Gaussian (`s = π / 2`) has a derivative within
`β² 𝔼⟨|R_{1,2} - q|⟩_s + 2β² / (N+1)` of `-(β²/2)(1 - q²)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

/-- **Derivative of the pair-perturbation path (Talagrand Eqs. 1.178, 1.182).**  For any
measurable family of base energies `B η` with integrable coordinates, the path
`s ↦ 𝔼 log ∑ₐ exp(cos s u_a + sin s v + B η a)` has derivative `sin t cos t D` at every `t`,
where `D` is within `β² ν_t(|R - q|) + 2β²/(N+1)` of `-(β²/2)(1 - q²)`, `ν_t` the average of the
two-replica tilted measure at time `t`. -/
theorem exists_hasDerivAt_sk_pair_perturb_path
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (N : ℕ) (hN : 0 < N) (β q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (B : Ω₀ → (Fin (N + 1) → ℤˣ) → ℝ) (hB : ∀ a, Measurable fun η => B η a)
    (hBi : ∀ a, Integrable (fun η => B η a) P₀) (t : ℝ) :
    ∃ D : ℝ, HasDerivAt (fun s => ∫ η, ∫ ω : (FinPairs (N + 1) → ℝ) × ℝ,
        Real.log (∑ a : Fin (N + 1) → ℤˣ, Real.exp (Real.cos s *
          (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
            ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          Real.sin s * (β * (Real.sqrt 2)⁻¹ * q * ω.2) + B η a))
        ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod (gaussianReal 0 1))
        ∂P₀) (Real.sin t * Real.cos t * D) t ∧
      |D - (-(β ^ 2 / 2) * (1 - q ^ 2))| ≤
        β ^ 2 * (∫ η, ∫ ω : (FinPairs (N + 1) → ℝ) × ℝ,
          ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ),
            |(N : ℝ)⁻¹ * ∑ i : Fin N, (p.1 i.castSucc : ℝ) * (p.2 i.castSucc : ℝ) - q|
            ∂((Measure.count.tilted fun a => Real.cos t *
                (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
                  ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
                Real.sin t * (β * (Real.sqrt 2)⁻¹ * q * ω.2) + B η a).prod
              (Measure.count.tilted fun a => Real.cos t *
                (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
                  ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
                Real.sin t * (β * (Real.sqrt 2)⁻¹ * q * ω.2) + B η a))
          ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod (gaussianReal 0 1))
          ∂P₀) + 2 * β ^ 2 / ((N : ℝ) + 1) := by
  have _ : Nonempty (Fin (N + 1) → ℤˣ) := ⟨fun _ => 1⟩
  set P : Measure ((FinPairs (N + 1) → ℝ) × ℝ) :=
    (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod (gaussianReal 0 1) with hPdef
  set X : (Fin (N + 1) → ℤˣ) → (FinPairs (N + 1) → ℝ) × ℝ → ℝ := fun a ω =>
    β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
      ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ) with hXdef
  set Y : (Fin (N + 1) → ℤˣ) → (FinPairs (N + 1) → ℝ) × ℝ → ℝ := fun _ ω =>
    β * (Real.sqrt 2)⁻¹ * q * ω.2 with hYdef
  have hXm : ∀ a, Measurable (X a) := fun a => by simp only [hXdef]; fun_prop
  have hYm : ∀ a, Measurable (Y a) := fun a => by simp only [hYdef]; fun_prop
  have hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P := by
    convert hasGaussianLaw_sk_pair_perturb_fields N β q using 1
    ext ω (σ | σ) <;> rfl
  have hX : ∀ a, ∫ ω, X a ω ∂P = 0 := fun a => integral_sk_pair_perturb_edge_field_eq_zero N β a
  have hY : ∀ a, ∫ ω, Y a ω ∂P = 0 := fun a =>
    integral_sk_pair_perturb_scalar_field_eq_zero N β q
  have h0 : ∀ a b, ∫ ω, X a ω * Y b ω ∂P = 0 := fun a b =>
    integral_sk_pair_perturb_edge_mul_scalar_eq_zero N β q a
  have hXi : ∀ a, Integrable (X a) P := fun a => (hXY.eval (Sum.inl a)).integrable
  have hYi : ∀ a, Integrable (Y a) P := fun a => (hXY.eval (Sum.inr a)).integrable
  let Zf : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
    ((∑ i, (a i : ℝ) * (b i : ℝ)) ^ 2 - (N + 1 : ℝ)) / ((N : ℝ) * (N + 1))
  let Rf : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
    (N : ℝ)⁻¹ * ∑ i : Fin N, (a i.castSucc : ℝ) * (b i.castSucc : ℝ)
  let C : ℝ := -(β ^ 2 / 2) * (1 - q ^ 2)
  let E : ℝ → Ω₀ → (FinPairs (N + 1) → ℝ) × ℝ → (Fin (N + 1) → ℤˣ) → ℝ := fun s η ω a =>
    Real.cos s * X a ω + Real.sin s * Y a ω + B η a
  have hEm : ∀ s a, Measurable (fun x : Ω₀ × ((FinPairs (N + 1) → ℝ) × ℝ) => E s x.1 x.2 a) :=
    fun s a => (((hXm a).comp measurable_snd).const_mul _ |>.add
      (((hYm a).comp measurable_snd).const_mul _)).add ((hB a).comp measurable_fst)
  have hbr : ∀ a b,
      ((∫ ω', Y a ω' * Y a ω' ∂P - ∫ ω', X a ω' * X a ω' ∂P) -
        (∫ ω', Y a ω' * Y b ω' ∂P - ∫ ω', X a ω' * X b ω' ∂P)) =
      C + β ^ 2 / 2 * (Zf a b - q ^ 2) := fun a b => by
    have := sk_pair_perturb_bracket_eq N hN β q a b
    simpa only [C, Zf, neg_mul] using this
  have hZ : ∀ a b, |Zf a b - q ^ 2| ≤ 2 * |Rf a b - q| + 4 / ((N : ℝ) + 1) := fun a b =>
    abs_sk_pair_perturb_Z_sub_le N hN q hq a b
  have hR2 : ∀ a b, |Rf a b - q| ≤ 2 := fun a b =>
    abs_sk_overlap_N_sub_le_two N hN q hq (fun i => a i.castSucc) (fun i => b i.castSucc)
  have hN1 : 4 / ((N : ℝ) + 1) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hZ6 : ∀ a b, |Zf a b - q ^ 2| ≤ 6 := fun a b => by
    have := hZ a b
    have := hR2 a b
    linarith
  have hsc := abs_sin_mul_cos_le_half
  have hpt : ∀ s a b, |Real.sin s * Real.cos s * (C + β ^ 2 / 2 * (Zf a b - q ^ 2))| ≤
      2 * β ^ 2 := fun s a b => by
    have h1 := hsc s
    have h2 : |C| ≤ β ^ 2 / 2 := by
      have : 0 ≤ 1 - q ^ 2 := by nlinarith [hq.1, hq.2]
      have : 1 - q ^ 2 ≤ 1 := by nlinarith [hq.1, hq.2]
      simp only [C]
      rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ β ^ 2 / 2), abs_of_nonneg ‹0 ≤ 1 - q ^ 2›]
      nlinarith [sq_nonneg β]
    have h3 : |C + β ^ 2 / 2 * (Zf a b - q ^ 2)| ≤ β ^ 2 / 2 + β ^ 2 / 2 * 6 := by
      refine (abs_add_le _ _).trans (add_le_add h2 ?_)
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ β ^ 2 / 2)]
      exact mul_le_mul_of_nonneg_left (hZ6 a b) (by positivity)
    rw [abs_mul]
    calc _ ≤ (1 / 2) * (β ^ 2 / 2 + β ^ 2 / 2 * 6) :=
          mul_le_mul h1 h3 (abs_nonneg _) (by norm_num)
      _ ≤ 2 * β ^ 2 := by nlinarith [sq_nonneg β]
  have hFm : ∀ s, AEStronglyMeasurable (fun η => ∫ ω,
      Real.log (∑ a, Real.exp (Real.cos s * X a ω + Real.sin s * Y a ω + B η a)) ∂P) P₀ := by
    intro s
    have hm : Measurable fun x : Ω₀ × ((FinPairs (N + 1) → ℝ) × ℝ) =>
        Real.log (∑ a, Real.exp (E s x.1 x.2 a)) :=
      (Finset.measurable_sum _ fun a _ => (hEm s a).exp).log
    exact hm.aestronglyMeasurable.integral_prod_right'
  have hF : Integrable (fun η => ∫ ω,
      Real.log (∑ a, Real.exp (Real.cos t * X a ω + Real.sin t * Y a ω + B η a)) ∂P) P₀ := by
    have hint := integrable_log_sum_exp (μ := P₀.prod P) (β := 1)
      (H := fun (x : Ω₀ × ((FinPairs (N + 1) → ℝ) × ℝ)) a => E t x.1 x.2 a) (by norm_num)
      (hEm t) (fun a => ((((hXi a).comp_snd P₀).const_mul _).add
        (((hYi a).comp_snd P₀).const_mul _)).add ((hBi a).comp_fst P))
    simp only [one_mul] at hint
    exact hint.integral_prod_left
  have hDm : AEStronglyMeasurable (fun η => ∫ ω, ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ),
      Real.sin t * Real.cos t *
        ((∫ ω', Y p.1 ω' * Y p.1 ω' ∂P - ∫ ω', X p.1 ω' * X p.1 ω' ∂P) -
          (∫ ω', Y p.1 ω' * Y p.2 ω' ∂P - ∫ ω', X p.1 ω' * X p.2 ω' ∂P))
        ∂((Measure.count.tilted fun a => Real.cos t * X a ω + Real.sin t * Y a ω + B η a).prod
          (Measure.count.tilted fun a => Real.cos t * X a ω + Real.sin t * Y a ω + B η a))
        ∂P) P₀ := by
    simp only [hbr]
    have hm := measurable_integral_prod_count_tilted
      (g := fun (x : Ω₀ × ((FinPairs (N + 1) → ℝ) × ℝ)) a => E t x.1 x.2 a)
      (Θ := fun _ (a b : Fin (N + 1) → ℤˣ) =>
        Real.sin t * Real.cos t * (C + β ^ 2 / 2 * (Zf a b - q ^ 2))) (hEm t)
      (fun _ _ => measurable_const)
    exact hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
  have hder := hasDerivAt_integral_conditional_log_sum_exp_trig P₀ (X := X) (Y := Y)
    hXm hYm hXY hX hY h0 B t hFm hDm hF (2 * β ^ 2) (fun η s => by
      simp only [hbr]
      exact abs_integral_integral_le_of_forall_le P _
        (fun p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ) =>
          Real.sin s * Real.cos s * (C + β ^ 2 / 2 * (Zf p.1 p.2 - q ^ 2)))
        (fun p => hpt s p.1 p.2))
  let V : ℝ := ∫ η, ∫ ω, ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ), (Zf p.1 p.2 - q ^ 2)
    ∂((Measure.count.tilted (E t η ω)).prod (Measure.count.tilted (E t η ω))) ∂P ∂P₀
  let Ψ : ℝ := ∫ η, ∫ ω, ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ), |Rf p.1 p.2 - q|
    ∂((Measure.count.tilted (E t η ω)).prod (Measure.count.tilted (E t η ω))) ∂P ∂P₀
  refine ⟨C + β ^ 2 / 2 * V, hder.congr_deriv ?_, ?_⟩
  · have hrw : ∀ a b, Real.sin t * Real.cos t * (C + β ^ 2 / 2 * (Zf a b - q ^ 2)) =
        (Real.sin t * Real.cos t * (β ^ 2 / 2)) * (Zf a b - q ^ 2) +
          Real.sin t * Real.cos t * C := fun a b => by ring
    have key := integral_nested_prod_gibbs_affine P₀ P (E t) (hEm t)
      (fun a b => Zf a b - q ^ 2) (Real.sin t * Real.cos t * (β ^ 2 / 2))
      (Real.sin t * Real.cos t * C)
    simp only [hbr, hrw]
    refine key.trans ?_
    simp only [V]
    ring
  · have h1 := abs_integral_nested_prod_gibbs_le P₀ P (E t) (hEm t)
      (G := fun a b => Zf a b - q ^ 2) (H := fun a b => 2 * |Rf a b - q| + 4 / ((N : ℝ) + 1))
      hZ
    have h2 := integral_nested_prod_gibbs_affine P₀ P (E t) (hEm t)
      (fun a b => |Rf a b - q|) 2 (4 / ((N : ℝ) + 1))
    have hV : |V| ≤ 2 * Ψ + 4 / ((N : ℝ) + 1) := h1.trans h2.le
    show |C + β ^ 2 / 2 * V - C| ≤ β ^ 2 * Ψ + 2 * β ^ 2 / ((N : ℝ) + 1)
    have : |C + β ^ 2 / 2 * V - C| = β ^ 2 / 2 * |V| := by
      rw [add_sub_cancel_left, abs_mul, abs_of_nonneg (by positivity : 0 ≤ β ^ 2 / 2)]
    rw [this]
    calc β ^ 2 / 2 * |V| ≤ β ^ 2 / 2 * (2 * Ψ + 4 / ((N : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hV (by positivity)
      _ = β ^ 2 * Ψ + 2 * β ^ 2 / ((N : ℝ) + 1) := by ring

/-- **Comparison of the overlap average along the pair-perturbation path (Talagrand,
Eq. 1.182 and the bound `|ψ'| ≤ K ψ`).**  The path average of `|R_{1,2} - q|` at any angle is
at most `exp (10 β²)` times its value at the coupled endpoint `s = 0`. -/
theorem sk_pair_perturb_overlap_path_le
    {Ω₀ : Type*} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    (N : ℕ) (hN : 0 < N) (β q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (B : Ω₀ → (Fin (N + 1) → ℤˣ) → ℝ) (hB : ∀ a, Measurable fun η => B η a)
    {s : ℝ} (hs : s ∈ Set.Icc 0 (Real.pi / 2)) :
    (∫ η, ∫ ω : (FinPairs (N + 1) → ℝ) × ℝ,
      ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ),
        |(N : ℝ)⁻¹ * ∑ i : Fin N, (p.1 i.castSucc : ℝ) * (p.2 i.castSucc : ℝ) - q|
        ∂((Measure.count.tilted fun a => Real.cos s *
            (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
              ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            Real.sin s * (β * (Real.sqrt 2)⁻¹ * q * ω.2) + B η a).prod
          (Measure.count.tilted fun a => Real.cos s *
            (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
              ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
            Real.sin s * (β * (Real.sqrt 2)⁻¹ * q * ω.2) + B η a))
      ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂P₀) ≤
    Real.exp (10 * β ^ 2) * ∫ η, ∫ ω : (FinPairs (N + 1) → ℝ) × ℝ,
      ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ),
        |(N : ℝ)⁻¹ * ∑ i : Fin N, (p.1 i.castSucc : ℝ) * (p.2 i.castSucc : ℝ) - q|
        ∂((Measure.count.tilted fun a => (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
              ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) + B η a).prod
          (Measure.count.tilted fun a => (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
              ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) + B η a))
      ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂P₀ := by
  have _ : Nonempty (Fin (N + 1) → ℤˣ) := ⟨fun _ => 1⟩
  set P : Measure ((FinPairs (N + 1) → ℝ) × ℝ) :=
    (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod (gaussianReal 0 1) with hPdef
  set X : (Fin (N + 1) → ℤˣ) → (FinPairs (N + 1) → ℝ) × ℝ → ℝ := fun a ω =>
    β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
      ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ) with hXdef
  set Y : (Fin (N + 1) → ℤˣ) → (FinPairs (N + 1) → ℝ) × ℝ → ℝ := fun _ ω =>
    β * (Real.sqrt 2)⁻¹ * q * ω.2 with hYdef
  have hXm : ∀ a, Measurable (X a) := fun a => by simp only [hXdef]; fun_prop
  have hYm : ∀ a, Measurable (Y a) := fun a => by simp only [hYdef]; fun_prop
  have hXY : HasGaussianLaw (fun ω s => Sum.elim X Y s ω) P := by
    convert hasGaussianLaw_sk_pair_perturb_fields N β q using 1
    ext ω (σ | σ) <;> rfl
  have hX : ∀ a, ∫ ω, X a ω ∂P = 0 := fun a => integral_sk_pair_perturb_edge_field_eq_zero N β a
  have hY : ∀ a, ∫ ω, Y a ω ∂P = 0 := fun a =>
    integral_sk_pair_perturb_scalar_field_eq_zero N β q
  have h0 : ∀ a b, ∫ ω, X a ω * Y b ω ∂P = 0 := fun a b =>
    integral_sk_pair_perturb_edge_mul_scalar_eq_zero N β q a
  let Zf : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
    ((∑ i, (a i : ℝ) * (b i : ℝ)) ^ 2 - (N + 1 : ℝ)) / ((N : ℝ) * (N + 1))
  let Rf : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
    (N : ℝ)⁻¹ * ∑ i : Fin N, (a i.castSucc : ℝ) * (b i.castSucc : ℝ)
  let U : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
    β ^ 2 / 2 * (q ^ 2 - Zf a b)
  have hU : ∀ a b, U a b = ∫ ω, Y a ω * Y b ω ∂P - ∫ ω, X a ω * X b ω ∂P := fun a b =>
    sk_pair_perturb_covariance_difference N hN β q a b
  have hUb : ∀ a b, |U a b| ≤ β ^ 2 := fun a b => by
    have hz := abs_sk_pair_perturb_Z_le_one N hN a b
    have hq2 : q ^ 2 ≤ 1 := by nlinarith [hq.1, hq.2]
    have hq0 : 0 ≤ q ^ 2 := sq_nonneg q
    have h1 : |q ^ 2 - Zf a b| ≤ 2 := by
      rw [abs_le] at hz ⊢
      constructor <;> linarith [hz.1, hz.2]
    simp only [U]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ β ^ 2 / 2)]
    nlinarith [sq_nonneg β]
  let Φ : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ := fun σ => |Rf (σ 0) (σ 1) - q|
  have hΦ0 : ∀ σ, 0 ≤ Φ σ := fun σ => abs_nonneg _
  have hΦ2 : ∀ σ, |Φ σ| ≤ 2 := fun σ => by
    rw [abs_of_nonneg (hΦ0 σ)]
    exact abs_sk_overlap_N_sub_le_two N hN q hq (fun i => σ 0 i.castSucc) (fun i => σ 1 i.castSucc)
  let E : ℝ → Ω₀ → (FinPairs (N + 1) → ℝ) × ℝ → (Fin (N + 1) → ℤˣ) → ℝ := fun s η ω a =>
    Real.cos s * X a ω + Real.sin s * Y a ω + B η a
  have hEm : ∀ s a, Measurable (fun x : Ω₀ × ((FinPairs (N + 1) → ℝ) × ℝ) => E s x.1 x.2 a) :=
    fun s a => (((hXm a).comp measurable_snd).const_mul _ |>.add
      (((hYm a).comp measurable_snd).const_mul _)).add ((hB a).comp measurable_fst)
  let Gf : (Option (Option (Fin 2)) → Fin (N + 1) → ℤˣ) → ℝ := fun τ =>
    Φ (fun r => τ (some (some r))) *
      ((∑ r, ∑ r', U (τ (some (some r))) (τ (some (some r')))) -
        2 * Fintype.card (Fin 2) * ∑ r, U (τ (some (some r))) (τ (some none)) -
        Fintype.card (Fin 2) * U (τ (some none)) (τ (some none)) +
        Fintype.card (Fin 2) * (Fintype.card (Fin 2) + 1) * U (τ (some none)) (τ none))
  have hGf : ∀ τ, |Gf τ| ≤ Φ (fun r => τ (some (some r))) * (20 * β ^ 2) := fun τ => by
    have h := abs_replica_covariance_combination_le (R := Fin 2) U (β ^ 2) hUb τ
    simp only [Fintype.card_fin] at h
    simp only [Gf]
    rw [abs_mul, abs_of_nonneg (hΦ0 (fun r => τ (some (some r))))]
    refine mul_le_mul_of_nonneg_left ?_ (hΦ0 (fun r => τ (some (some r))))
    simp only [Fintype.card_fin]
    norm_num at h ⊢
    linarith
  have hGf40 : ∀ τ, |Gf τ| ≤ 40 * β ^ 2 := fun τ => by
    refine (hGf τ).trans ?_
    have := hΦ2 (fun r => τ (some (some r)))
    have h0' := hΦ0 (fun r => τ (some (some r)))
    rw [abs_of_nonneg h0'] at this
    nlinarith [sq_nonneg β]
  let φ : ℝ → ℝ := fun s' => ∫ η, ∫ ω, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
    ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E s' η ω)) ∂P ∂P₀
  have hd : ∀ s', ∃ d, HasDerivAt φ d s' ∧ (s' ∈ Set.Icc 0 (Real.pi / 2) →
      d ≤ 20 * β ^ 2 * (Real.sin s' * Real.cos s') * φ s') := by
    intro s'
    have hder := hasDerivAt_integral_conditional_replica_trig (R := Fin 2) P₀ (X := X) (Y := Y)
      hXm hYm hXY hX hY h0 U hU B hB Φ 2 hΦ2 s' (20 * β ^ 2) (fun η s'' => by
        have hI := abs_integral_integral_le_of_forall_le P
          (fun ω => Measure.pi fun _ : Option (Option (Fin 2)) =>
            Measure.count.tilted (E s'' η ω)) Gf hGf40
        rw [abs_mul]
        calc _ ≤ (1 / 2) * (40 * β ^ 2) :=
              mul_le_mul (abs_sin_mul_cos_le_half s'') hI (abs_nonneg _) (by norm_num)
          _ = 20 * β ^ 2 := by ring)
    refine ⟨_, hder, fun hs' => ?_⟩
    have hsc0 : 0 ≤ Real.sin s' * Real.cos s' :=
      mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hs'.1 (by linarith [hs'.2, Real.pi_pos]))
        (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hs'.1, Real.pi_pos], hs'.2⟩)
    rw [integral_const_mul]
    have hnest := abs_integral_nested_gibbs_le P₀ P (E s') (hEm s') (R := Option (Option (Fin 2)))
      (G := Gf) (H := fun τ => Φ (fun r => τ (some (some r))) * (20 * β ^ 2)) hGf
    have hmarg : ∀ η ω, ∫ τ : Option (Option (Fin 2)) → Fin (N + 1) → ℤˣ,
        Φ (fun r => τ (some (some r))) * (20 * β ^ 2)
          ∂(Measure.pi fun _ : Option (Option (Fin 2)) => Measure.count.tilted (E s' η ω)) =
        (∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E s' η ω))) * (20 * β ^ 2) :=
      fun η ω => by
        rw [integral_mul_const, integral_pi_option_option_count_tilted_marginal (E s' η ω) Φ]
    simp_rw [hmarg, integral_mul_const] at hnest
    calc _ ≤ Real.sin s' * Real.cos s' * |∫ η, ∫ ω, ∫ τ, Gf τ
          ∂(Measure.pi fun _ : Option (Option (Fin 2)) =>
            Measure.count.tilted (E s' η ω)) ∂P ∂P₀| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hsc0
      _ ≤ Real.sin s' * Real.cos s' * (φ s' * (20 * β ^ 2)) :=
          mul_le_mul_of_nonneg_left hnest hsc0
      _ = _ := by ring
  have hgr := Real.le_exp_mul_sin_sq_of_exists_hasDerivAt (φ := φ) (K := 20 * β ^ 2) hd hs
  have hφ0 : 0 ≤ φ 0 :=
    integral_nonneg fun η => integral_nonneg fun ω => integral_nonneg fun σ => hΦ0 σ
  have hexp : Real.exp (20 * β ^ 2 * Real.sin s ^ 2 / 2) ≤ Real.exp (10 * β ^ 2) :=
    Real.exp_le_exp.2 (by nlinarith [Real.sin_sq_le_one s, sq_nonneg β])
  have hconv : ∀ s' η ω, (∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E s' η ω))) =
      ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ), |Rf p.1 p.2 - q|
        ∂((Measure.count.tilted (E s' η ω)).prod (Measure.count.tilted (E s' η ω))) :=
    fun s' η ω => (integral_pi_fin_two_count_tilted (E s' η ω) (fun a b => |Rf a b - q|)).trans
      (integral_prod_count_tilted (E s' η ω) (fun a b => |Rf a b - q|)).symm
  have hE0 : ∀ η ω, E 0 η ω = fun a => X a ω + B η a := fun η ω =>
    funext fun a => by simp [E]
  have hφ : ∀ s', φ s' = ∫ η, ∫ ω, ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ),
      |Rf p.1 p.2 - q|
      ∂((Measure.count.tilted (E s' η ω)).prod (Measure.count.tilted (E s' η ω))) ∂P ∂P₀ :=
    fun s' => by simp only [φ, hconv]
  have hφ0' : φ 0 = ∫ η, ∫ ω, ∫ p : (Fin (N + 1) → ℤˣ) × (Fin (N + 1) → ℤˣ),
      |Rf p.1 p.2 - q|
      ∂((Measure.count.tilted fun a => X a ω + B η a).prod
        (Measure.count.tilted fun a => X a ω + B η a)) ∂P ∂P₀ := by
    rw [hφ]
    simp only [hE0]
  calc _ = φ s := (hφ s).symm
    _ ≤ Real.exp (20 * β ^ 2 * Real.sin s ^ 2 / 2) * φ 0 := hgr
    _ ≤ Real.exp (10 * β ^ 2) * φ 0 := mul_le_mul_of_nonneg_right hexp hφ0
    _ = _ := by rw [hφ0']

/-- **Talagrand's Eq. (1.182), with explicit constants.**  The expected log Gibbs average of the
independent pair perturbation `exp(β (N(N+1))^{-1/2} ∑ g''_{ij} σᵢσⱼ)` in the `(N+1)`-spin system
at coefficient `β / √(N+1)` is within `β² / N + β² cosh(2h) exp(12β²) ν` of
`(β²/4)(1 - q²)`, where `ν` is the `N`-spin two-replica average of `|R_{1,2} - q|`.  This is the
hypothesis `h_perturb` of `sk_cavity_free_energy_increment_le`, with the constants that the
interpolation actually gives. -/
theorem sk_pair_perturb_estimate (N : ℕ) (hN : 0 < N) (β h q : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    |(∫ qdis : (FinPairs (N + 1) → ℝ) × (FinPairs (N + 1) → ℝ),
      Real.log (∫ σ : Fin (N + 1) → ℤˣ,
        Real.exp (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
          ∑ p : FinPairs (N + 1), qdis.2 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ))
        ∂Measure.count.tilted (fun σ =>
          (Real.sqrt (N + 1 : ℝ))⁻¹ * β *
            (∑ p : FinPairs (N + 1), qdis.1 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
            h * ∑ i, (σ i : ℝ)))
      ∂((Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))) -
      β ^ 2 / 4 * (1 - q ^ 2)| ≤
    β ^ 2 / (N : ℝ) +
      (β ^ 2 * Real.cosh (2 * h) * Real.exp (12 * β ^ 2)) *
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
  have _ : Nonempty (Fin (N + 1) → ℤˣ) := ⟨fun _ => 1⟩
  have _ : Nonempty (Fin N → ℤˣ) := ⟨fun _ => 1⟩
  set P₀ : Measure (FinPairs (N + 1) → ℝ) := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1
    with hP₀
  set P : Measure ((FinPairs (N + 1) → ℝ) × ℝ) := P₀.prod (gaussianReal 0 1) with hPdef
  set a₁ : ℝ := (Real.sqrt (N + 1 : ℝ))⁻¹ * β with ha₁
  set b₁ : ℝ := β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ with hb₁
  let B : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun η a =>
    (Real.sqrt (N + 1 : ℝ))⁻¹ * β *
      (∑ p : FinPairs (N + 1), η p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) + h * ∑ i, (a i : ℝ)
  have hB : ∀ a, Measurable fun η => B η a := fun a => by simp only [B]; fun_prop
  have hid : Integrable (id : ℝ → ℝ) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  have hBi : ∀ a, Integrable (fun η => B η a) P₀ := fun a =>
    ((integrable_finsetSum _ fun p _ =>
      ((integrable_eval (μ := fun _ : FinPairs (N + 1) => gaussianReal 0 1) hid).mul_const
        _).mul_const _).const_mul _).add (integrable_const _)
  let Fp : ℝ → ℝ := fun s => ∫ η, ∫ ω : (FinPairs (N + 1) → ℝ) × ℝ,
    Real.log (∑ a : Fin (N + 1) → ℤˣ, Real.exp (Real.cos s *
      (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
        ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      Real.sin s * (β * (Real.sqrt 2)⁻¹ * q * ω.2) + B η a)) ∂P ∂P₀
  let Zb : ℝ := ∫ η, Real.log (∑ a : Fin (N + 1) → ℤˣ, Real.exp (B η a)) ∂P₀
  let ψ : ℝ → ℝ := fun s => Fp s - Zb
  let ν : ℝ := ∫ g' : FinPairs N → ℝ,
    ∫ p : (Fin N → ℤˣ) × (Fin N → ℤˣ),
      |(N : ℝ)⁻¹ * ∑ i : Fin N, (p.1 i : ℝ) * (p.2 i : ℝ) - q|
      ∂((Measure.count.tilted (fun ρ => (Real.sqrt (N : ℝ))⁻¹ * β *
          (∑ p : FinPairs N, g' p * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) +
          h * ∑ i, (ρ i : ℝ))).prod
        (Measure.count.tilted (fun ρ => (Real.sqrt (N : ℝ))⁻¹ * β *
          (∑ p : FinPairs N, g' p * (ρ p.val.1 : ℝ) * (ρ p.val.2 : ℝ)) +
          h * ∑ i, (ρ i : ℝ))))
    ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
  have hν : 0 ≤ ν := integral_nonneg fun _ => integral_nonneg fun _ => abs_nonneg _
  have hK3 : 0 ≤ β ^ 2 * Real.cosh (2 * h) * Real.exp (12 * β ^ 2) := by positivity
  have hd : ∀ s, ∃ D, HasDerivAt ψ (Real.sin s * Real.cos s * D) s ∧
      (s ∈ Set.Icc 0 (Real.pi / 2) → |D - (-β ^ 2 / 2 * (1 - q ^ 2))| ≤
        2 * (β ^ 2 / (N : ℝ) + (β ^ 2 * Real.cosh (2 * h) * Real.exp (12 * β ^ 2)) * ν)) := by
    intro s
    obtain ⟨D, hD, hDb⟩ := exists_hasDerivAt_sk_pair_perturb_path P₀ N hN β q hq B hB hBi s
    refine ⟨D, hD.sub_const Zb, fun hs => ?_⟩
    have h1 := sk_pair_perturb_overlap_path_le P₀ N hN β q hq B hB hs
    have h2 := integral_sk_pair_perturb_endpoint_transport N hN β h q hq
    have h3 := integral_sk_pair_perturb_cavity_le N hN β h q hq
    have h4 : (2 * β ^ 2 / ((N : ℝ) + 1)) ≤ 2 * β ^ 2 / (N : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hN) (by linarith)
    have hnu : 0 ≤ (β ^ 2 * Real.cosh (2 * h) * Real.exp (12 * β ^ 2)) * ν := mul_nonneg hK3 hν
    have e : β ^ 2 * (Real.exp (10 * β ^ 2) * (Real.cosh (2 * h) * Real.exp (2 * β ^ 2) * ν)) =
        (β ^ 2 * Real.cosh (2 * h) * Real.exp (12 * β ^ 2)) * ν := by
      rw [show 12 * β ^ 2 = 10 * β ^ 2 + 2 * β ^ 2 by ring, Real.exp_add]
      ring
    have key := h1.trans (mul_le_mul_of_nonneg_left (h2.le.trans h3) (Real.exp_nonneg _))
    calc |D - (-β ^ 2 / 2 * (1 - q ^ 2))| = |D - (-(β ^ 2 / 2) * (1 - q ^ 2))| := by ring_nf
      _ ≤ _ := hDb
      _ ≤ β ^ 2 * (Real.exp (10 * β ^ 2) * (Real.cosh (2 * h) * Real.exp (2 * β ^ 2) * ν)) +
            2 * β ^ 2 / ((N : ℝ) + 1) := by gcongr
      _ ≤ _ := by
        have h5 : 2 * β ^ 2 / (N : ℝ) = 2 * (β ^ 2 / (N : ℝ)) := by ring
        rw [e]; linarith
  have h0 : ψ 0 = ∫ qdis : (FinPairs (N + 1) → ℝ) × (FinPairs (N + 1) → ℝ),
      Real.log (∫ σ : Fin (N + 1) → ℤˣ,
        Real.exp (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
          ∑ p : FinPairs (N + 1), qdis.2 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ))
        ∂Measure.count.tilted (fun σ =>
          (Real.sqrt (N + 1 : ℝ))⁻¹ * β *
            (∑ p : FinPairs (N + 1), qdis.1 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
            h * ∑ i, (σ i : ℝ)))
      ∂(P₀.prod P₀) := by
    have hsplit := integral_log_partition_sk_pair_perturb N a₁ b₁ h
    have hint := integrable_log_partition_sk_pair N a₁ b₁ h
    have harg : ∀ (η u : FinPairs (N + 1) → ℝ) (σ : Fin (N + 1) → ℤˣ) (z : ℝ),
        Real.cos 0 * (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
          ∑ p : FinPairs (N + 1), u p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          Real.sin 0 * (β * (Real.sqrt 2)⁻¹ * q * z) + B η σ =
        a₁ * (∑ p : FinPairs (N + 1), η p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
          h * ∑ i, (σ i : ℝ) +
        b₁ * (∑ p : FinPairs (N + 1), u p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) :=
      fun η u σ z => by
        simp only [B, a₁, b₁, Real.cos_zero, Real.sin_zero]
        ring
    have hF0 : Fp 0 = ∫ q : (FinPairs (N + 1) → ℝ) × (FinPairs (N + 1) → ℝ),
        Real.log (∑ σ : Fin (N + 1) → ℤˣ,
          Real.exp (a₁ * (∑ p : FinPairs (N + 1),
            q.1 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ) +
            b₁ * (∑ p : FinPairs (N + 1),
              q.2 p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)))) ∂(P₀.prod P₀) := by
      rw [integral_prod _ hint]
      refine integral_congr_ae (ae_of_all _ fun η => ?_)
      simp only [harg]
      exact integral_prod_fun_fst_of_isProbabilityMeasure P₀ (gaussianReal 0 1)
        (fun u => Real.log (∑ σ : Fin (N + 1) → ℤˣ,
          Real.exp (a₁ * (∑ p : FinPairs (N + 1),
            η p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ) +
            b₁ * (∑ p : FinPairs (N + 1), u p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)))))
    have hZb : Zb = ∫ g : FinPairs (N + 1) → ℝ,
        Real.log (∑ σ : Fin (N + 1) → ℤˣ,
          Real.exp (a₁ * (∑ p : FinPairs (N + 1),
            g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) + h * ∑ i, (σ i : ℝ))) ∂P₀ := rfl
    simp only [ψ]
    rw [hF0, hZb]
    linarith
  have hpi : ψ (Real.pi / 2) = 0 := by
    have hYi : Integrable (fun ω : (FinPairs (N + 1) → ℝ) × ℝ => β * (Real.sqrt 2)⁻¹ * q * ω.2)
        P := (hid.comp_snd P₀).const_mul _
    have hY0 : ∫ ω : (FinPairs (N + 1) → ℝ) × ℝ, β * (Real.sqrt 2)⁻¹ * q * ω.2 ∂P = 0 :=
      integral_sk_pair_perturb_scalar_field_eq_zero N β q
    have hcalc : ∀ (η : FinPairs (N + 1) → ℝ) (ω : (FinPairs (N + 1) → ℝ) × ℝ),
        Real.log (∑ a : Fin (N + 1) → ℤˣ, Real.exp (Real.cos (Real.pi / 2) *
          (β * (Real.sqrt ((N : ℝ) * (N + 1)))⁻¹ *
            ∑ p : FinPairs (N + 1), ω.1 p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          Real.sin (Real.pi / 2) * (β * (Real.sqrt 2)⁻¹ * q * ω.2) + B η a)) =
        β * (Real.sqrt 2)⁻¹ * q * ω.2 + Real.log (∑ a : Fin (N + 1) → ℤˣ, Real.exp (B η a)) := by
      intro η ω
      simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_mul, one_mul, zero_add]
      simp_rw [Real.exp_add]
      rw [← Finset.mul_sum, Real.log_mul (Real.exp_pos _).ne', Real.log_exp]
      exact (Finset.sum_pos (fun a _ => Real.exp_pos _) Finset.univ_nonempty).ne'
    simp only [ψ, Fp, hcalc, Zb]
    have : ∀ η : FinPairs (N + 1) → ℝ,
        (∫ ω : (FinPairs (N + 1) → ℝ) × ℝ, β * (Real.sqrt 2)⁻¹ * q * ω.2 +
          Real.log (∑ a : Fin (N + 1) → ℤˣ, Real.exp (B η a)) ∂P) =
        Real.log (∑ a : Fin (N + 1) → ℤˣ, Real.exp (B η a)) := fun η => by
      rw [integral_add hYi (integrable_const _), hY0]
      simp
    simp_rw [this]
    simp
  exact sk_pair_perturb_estimate_of_deriv_bound β q N _ ν (β ^ 2)
    (β ^ 2 * Real.cosh (2 * h) * Real.exp (12 * β ^ 2)) ψ h0 hpi hd

end SpinGlasses
