/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletGhirlandaGuerraTransfer

/-!
# Marginalizing the extra Poisson-Dirichlet replica

The independent `none` coordinate of the Gaussian IBP correction disappears from
terms involving only the original replicas. The remaining term measures coincidence
with the fresh replica.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SpinGlasses

/-- Pointwise extra-replica algebra for normalized Gibbs weights. This separates
the overlap correction from all Poisson and Gaussian probability arguments. -/
theorem gaussian_ibp_overlap_correction_marginal
    {J α : Type*} [Fintype J] [DecidableEq α]
    {w : α → ℝ} (hw0 : ∀ a, 0 ≤ w a) (hws : Summable w)
    (hw : ∑' a, w a = 1) (r₀ : J)
    (Φ : (J → α) → ℝ) {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M) (t : ℝ) :
    (∑' τ : Option J → α, (∏ o, w (τ o)) *
      (Φ (fun j => τ (some j)) *
        ((∑ j, t * (if τ (some r₀) = τ (some j) then 1 else 0)) -
          (Fintype.card J : ℝ) * t *
            (if τ (some r₀) = τ none then 1 else 0)))) =
      t * ((∑' σ : J → α, (∏ j, w (σ j)) *
        (Φ σ * ∑ j, if σ r₀ = σ j then 1 else 0)) -
        (Fintype.card J : ℝ) *
          (∑' τ : Option J → α, (∏ o, w (τ o)) *
            (Φ (fun j => τ (some j)) *
              (if τ (some r₀) = τ none then 1 else 0)))) := by
  let A : (Option J → α) → ℝ := fun τ =>
    (∏ o, w (τ o)) *
      (Φ (fun j => τ (some j)) *
        (∑ j, if τ (some r₀) = τ (some j) then (1 : ℝ) else 0))
  let C : (Option J → α) → ℝ := fun τ =>
    (∏ o, w (τ o)) *
      (Φ (fun j => τ (some j)) *
        (if τ (some r₀) = τ none then (1 : ℝ) else 0))
  have hA : Summable A := by
    apply (summable_prod_pi (J := Option J) (f := fun _ => w)
      (fun _ a => hw0 a) (fun _ => hws)).mul_right (M * Fintype.card J) |>.of_norm_bounded
    intro τ
    dsimp [A]
    rw [abs_mul,
      abs_of_nonneg (Finset.prod_nonneg fun o _ => hw0 (τ o)), abs_mul]
    have hsum : |∑ j, if τ (some r₀) = τ (some j) then (1 : ℝ) else 0| ≤
        Fintype.card J := by
      rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num)]
      simpa using Finset.sum_le_card_nsmul Finset.univ
        (fun j => if τ (some r₀) = τ (some j) then (1 : ℝ) else 0) 1
        (fun j _ => by split_ifs <;> norm_num)
    have hM : 0 ≤ M := (abs_nonneg _).trans (hΦ (fun j => τ (some j)))
    exact (mul_le_mul_of_nonneg_left
      ((mul_le_mul (hΦ _) hsum (by positivity) hM).trans_eq (by ring))
      (Finset.prod_nonneg fun o _ => hw0 (τ o)))
  have hC : Summable C := by
    apply (summable_prod_pi (J := Option J) (f := fun _ => w)
      (fun _ a => hw0 a) (fun _ => hws)).mul_right M |>.of_norm_bounded
    intro τ
    dsimp [C]
    rw [abs_mul,
      abs_of_nonneg (Finset.prod_nonneg fun o _ => hw0 (τ o)), abs_mul]
    have hi : |(if τ (some r₀) = τ none then (1 : ℝ) else 0)| ≤ 1 := by
      split_ifs <;> norm_num
    have hM : 0 ≤ M := (abs_nonneg _).trans (hΦ (fun j => τ (some j)))
    exact mul_le_mul_of_nonneg_left
      ((mul_le_mul (hΦ _) hi (by positivity) hM).trans_eq (by ring))
      (Finset.prod_nonneg fun o _ => hw0 (τ o))
  have heq (τ : Option J → α) :
      (∏ o, w (τ o)) *
        (Φ (fun j => τ (some j)) *
          ((∑ j, t * (if τ (some r₀) = τ (some j) then 1 else 0)) -
            (Fintype.card J : ℝ) * t *
              (if τ (some r₀) = τ none then 1 else 0))) = t * A τ -
        (Fintype.card J : ℝ) * t * C τ := by
    rw [gaussian_ibp_overlap_correction_factor]
    dsimp [A, C]
    ring
  simp_rw [heq]
  rw [hA.mul_left t |>.tsum_sub (hC.mul_left ((Fintype.card J : ℝ) * t)),
    tsum_mul_left, tsum_mul_left]
  rw [gaussian_ibp_option_overlap_marginal hw0 hws hw r₀ Φ hΦ]
  ring

/-- Positive summable tilted masses give a normalized Gibbs distribution, and
the extra-replica Gaussian correction reduces to two overlap averages. -/
theorem gaussian_ibp_overlap_correction_active
    {J α : Type*} [Fintype J] [Nonempty α] [DecidableEq α]
    (u : α → ℝ) (hu : ∀ a, 0 < u a) (g : α → ℝ) (t : ℝ)
    (hs : Summable fun a => u a * Real.exp (t * g a))
    (r₀ : J) (Φ : (J → α) → ℝ)
    {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M) :
    let w : α → ℝ := fun a =>
      u a * Real.exp (t * g a) /
        ∑' b, u b * Real.exp (t * g b)
    (∑' τ : Option J → α, (∏ o, w (τ o)) *
      (Φ (fun j => τ (some j)) *
        ((∑ j, t * (if τ (some r₀) = τ (some j) then 1 else 0)) -
          (Fintype.card J : ℝ) * t *
            (if τ (some r₀) = τ none then 1 else 0)))) =
      t * ((∑' σ : J → α, (∏ j, w (σ j)) *
        (Φ σ * ∑ j, if σ r₀ = σ j then 1 else 0)) -
        (Fintype.card J : ℝ) *
          (∑' τ : Option J → α, (∏ o, w (τ o)) *
            (Φ (fun j => τ (some j)) *
              (if τ (some r₀) = τ none then 1 else 0)))) := by
  let v : α → ℝ := fun a => u a * Real.exp (t * g a)
  have hv (a : α) : 0 < v a := mul_pos (hu a) (Real.exp_pos _)
  have hV : 0 < ∑' a, v a :=
    hs.tsum_pos (fun a => (hv a).le) (Classical.choice inferInstance) (hv _)
  let w : α → ℝ := fun a => v a / ∑' b, v b
  have hw0 (a : α) : 0 ≤ w a := div_nonneg (hv a).le hV.le
  have hws : Summable w := hs.div_const _
  have hw : ∑' a, w a = 1 := tsum_div_tsum_eq_one hV
  exact gaussian_ibp_overlap_correction_marginal hw0 hws hw r₀ Φ hΦ t

/-- Transfer any jointly integrable observable from split Poisson blocks to the
independent product of their mass environment and standard Gaussian marks. -/
theorem integral_split_poissonBlocks_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ν : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (ν n)] (r : ℕ → ℝ≥0)
    {B : ℕ → Ω → ℕ × (ℕ → ℝ × ℝ)}
    (hBm : ∀ n, Measurable (B n)) (hB : iIndepFun B P)
    (hlaw : ∀ n, HasLaw (B n)
      (Po(r n).prod (Measure.infinitePi fun _ : ℕ =>
        (ν n).prod (gaussianReal 0 1))) P)
    {H : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → ℕ → ℝ) → ℝ}
    (hH : Integrable H ((P.map fun ω n =>
      ((B n ω).1, fun l => ((B n ω).2 l).1)).prod
      (Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1))) :
    (∫ ω, H ((fun n => ((B n ω).1, fun l => ((B n ω).2 l).1)),
      (fun n l => ((B n ω).2 l).2)) ∂P) =
    ∫ zg, H zg ∂(P.map fun ω n =>
      ((B n ω).1, fun l => ((B n ω).2 l).1)).prod
      (Measure.infinitePi fun _ : ℕ =>
        Measure.infinitePi fun _ : ℕ => gaussianReal 0 1) := by
  let Z : Ω → ℕ → ℕ × (ℕ → ℝ) :=
    fun ω n => ((B n ω).1, fun l => ((B n ω).2 l).1)
  let G : Ω → ℕ → ℕ → ℝ := fun ω n l => ((B n ω).2 l).2
  let μ : Measure (ℕ → ℕ → ℝ) :=
    Measure.infinitePi fun _ : ℕ => Measure.infinitePi fun _ : ℕ => gaussianReal 0 1
  have hsplit := indepFun_poissonBlocks_snd_marks ν
    (fun _ => gaussianReal 0 1) r hBm hB hlaw
  have hZm : Measurable Z := measurable_poissonBlocks_counts_fst hBm
  have hGm : Measurable G := measurable_poissonBlocks_snd hBm
  have hG : P.map G = μ := hsplit.2.1.map_eq
  change (∫ ω, H (Z ω, G ω) ∂P) = ∫ zg, H zg ∂(P.map Z).prod μ
  rw [IndepFun.integral_comp_prod hsplit.1 hZm hGm (hG.symm ▸ hH)]
  rw [hG, integral_prod H hH]

end SpinGlasses
