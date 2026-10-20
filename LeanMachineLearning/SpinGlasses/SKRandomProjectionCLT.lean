/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.GaussianCovarianceInterpolation
public import LeanMachineLearning.SpinGlasses.SKCorrelationDecay
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ParametrizedL2

/-!
# A kind of central limit theorem (Talagrand, Section 1.5)

Let `μ` be a probability measure on `ℝ^N` whose overlaps concentrate, `𝔼 (x¹ ⬝ x² / N - q)² ≃ 0`
and `‖x‖² / N ≃ ρ`.  For a standard Gaussian vector `g` the image of `μ` under `x ↦ g ⬝ x / √N` is
nearly the Gaussian of mean `g ⬝ b / √N` (`b` the barycenter of `μ`) and variance `ρ - q`: for a
`C²` function `f` with bounded derivatives,
`U = ∫ f (g ⬝ x / √N) dμ(x)` and `V = 𝔼_ξ f (g ⬝ b / √N + ξ √(ρ - q))` satisfy `𝔼_g (U - V)² ≃ 0`.

This file proves a quantitative form for a finite Gibbs state: with weights `w` on a finite set of
configurations `x_a ∈ ℝ^N` (`SpinGlasses.expected_sq_sub_le`),
`𝔼_g (U - V)² ≤ 2 (2 M₁² + M₀ M₂) (ν |R₁,₂ - q| + ⟨|‖x‖² / N - ρ|⟩)`,
where `M₀, M₁, M₂` bound `|f|, |f'|, |f''|`.  The proof expands the square and compares each of the
three terms with the same reference Gaussian integral through the covariance comparison
`SpinGlasses.abs_integral_mul_sub_le`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 1.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped Matrix

namespace SpinGlasses

section Block

variable {N : ℕ}

/-- **One expectation of the product `f (u ⬝ ξ) f (v ⬝ ξ)` against the reference.**  For `0 ≤ q ≤ ρ`
let `T` be the Gaussian integral `𝔼 f (u₀ ⬝ ζ) f (v₀ ⬝ ζ)` for the vectors
`u₀ = (√q, √(ρ - q), 0)`, `v₀ = (√q, 0, √(ρ - q))` of Gram matrix `[[ρ, q], [q, ρ]]`.  Then for a
Gaussian block `g` of dimension `N` and an independent Gaussian block `ξ` of dimension two,
`|𝔼 f (u₁ ⬝ g + u₂ ⬝ ξ) f (v₁ ⬝ g + v₂ ⬝ ξ) - T| ≤
  M₁² |u ⬝ v - q| + ½ M₀ M₂ (|u ⬝ u - ρ| + |v ⬝ v - ρ|)`
with the combined vectors `u = (u₁, u₂)`, `v = (v₁, v₂)`. -/
theorem abs_integral_block_sub_le {q ρ : ℝ} (hq : 0 ≤ q) (hqρ : q ≤ ρ) (u₁ v₁ : Fin N → ℝ)
    (u₂ v₂ : Fin 2 → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {M0 M1 M2 : ℝ}
    (h0 : ∀ x, |f x| ≤ M0) (h1 : ∀ x, |deriv f x| ≤ M1) (h2 : ∀ x, |deriv (deriv f) x| ≤ M2) :
    |∫ g, ∫ ξ, f (u₁ ⬝ᵥ g + u₂ ⬝ᵥ ξ) * f (v₁ ⬝ᵥ g + v₂ ⬝ᵥ ξ)
          ∂(Measure.pi fun _ : Fin 2 => gaussianReal 0 1) ∂(Measure.pi fun _ : Fin N =>
            gaussianReal 0 1) -
        ∫ ζ, f (![Real.sqrt q, Real.sqrt (ρ - q), 0] ⬝ᵥ ζ) *
          f (![Real.sqrt q, 0, Real.sqrt (ρ - q)] ⬝ᵥ ζ)
          ∂(Measure.pi fun _ : Fin 3 => gaussianReal 0 1)| ≤
      M1 ^ 2 * |u₁ ⬝ᵥ v₁ + u₂ ⬝ᵥ v₂ - q| +
        M0 * M2 / 2 * (|u₁ ⬝ᵥ u₁ + u₂ ⬝ᵥ u₂ - ρ| + |v₁ ⬝ᵥ v₁ + v₂ ⬝ᵥ v₂ - ρ|) := by
  have hFm : Measurable fun y : Fin 2 → ℝ => f (y 0) * f (y 1) :=
    (contDiff_pair_mul hf hf).continuous.measurable
  have hM0 : 0 ≤ M0 := (abs_nonneg _).trans (h0 0)
  have hbridge := integral_integral_dotProduct_add (κ := Fin 2) ![u₁, v₁] ![u₂, v₂]
    (F := fun y : Fin 2 → ℝ => f (y 0) * f (y 1)) hFm (B := M0 * M0) (fun y => by
      rw [abs_mul]; exact mul_le_mul (h0 _) (h0 _) (abs_nonneg _) hM0)
  have hcomp := abs_integral_mul_sub_le (u := Sum.elim u₁ u₂) (v := Sum.elim v₁ v₂)
    (u' := ![Real.sqrt q, Real.sqrt (ρ - q), 0]) (v' := ![Real.sqrt q, 0, Real.sqrt (ρ - q)])
    hf h0 h1 h2
  have e1 : ![Real.sqrt q, Real.sqrt (ρ - q), 0] ⬝ᵥ ![Real.sqrt q, 0, Real.sqrt (ρ - q)] = q := by
    simp [dotProduct, Fin.sum_univ_three, Real.mul_self_sqrt hq]
  have e2 : ![Real.sqrt q, Real.sqrt (ρ - q), 0] ⬝ᵥ ![Real.sqrt q, Real.sqrt (ρ - q), 0] = ρ := by
    simp [dotProduct, Fin.sum_univ_three, Real.mul_self_sqrt hq,
      Real.mul_self_sqrt (sub_nonneg.2 hqρ)]
  have e3 : ![Real.sqrt q, 0, Real.sqrt (ρ - q)] ⬝ᵥ ![Real.sqrt q, 0, Real.sqrt (ρ - q)] = ρ := by
    simp [dotProduct, Fin.sum_univ_three, Real.mul_self_sqrt hq,
      Real.mul_self_sqrt (sub_nonneg.2 hqρ)]
  have e4 : ∀ x y : Fin N → ℝ, ∀ x' y' : Fin 2 → ℝ,
      Sum.elim x x' ⬝ᵥ Sum.elim y y' = x ⬝ᵥ y + x' ⬝ᵥ y' := fun x y x' y' => by
    simp [dotProduct, Fintype.sum_sum_type]
  rw [e1, e2, e3, e4, e4, e4] at hcomp
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hbridge
  rw [hbridge, abs_sub_comm]
  refine hcomp.trans (le_of_eq ?_)
  simp only [abs_sub_comm q, abs_sub_comm ρ]

/-- **Fubini for two i.i.d. Gaussian coordinates:** a bounded measurable function of the two
coordinates of a point of `ℝ^{Fin 2}` integrates against the product Gaussian measure as an
iterated integral. -/
theorem integral_pi_fin_two_gaussianReal {G : ℝ → ℝ → ℝ} (hG : Measurable (Function.uncurry G))
    {B : ℝ} (hB : ∀ x y, |G x y| ≤ B) :
    ∫ σ : Fin 2 → ℝ, G (σ 0) (σ 1) ∂(Measure.pi fun _ : Fin 2 => gaussianReal 0 1) =
      ∫ x, ∫ y, G x y ∂(gaussianReal 0 1) ∂(gaussianReal 0 1) :=
  integral_pi_fin_two_of_integrable _ (Integrable.of_bound
    (hG.comp measurable_id).aestronglyMeasurable B
    (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hB _ _))

/-- A bounded measurable function of the first of two i.i.d. Gaussian coordinates integrates as
a function of one Gaussian. -/
theorem integral_pi_fin_two_fst {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, |φ x| ≤ B) :
    ∫ σ : Fin 2 → ℝ, φ (σ 0) ∂(Measure.pi fun _ : Fin 2 => gaussianReal 0 1) =
      ∫ x, φ x ∂(gaussianReal 0 1) := by
  rw [integral_pi_fin_two_gaussianReal (G := fun x _ => φ x) (hφ.comp measurable_fst)
    fun x _ => hB x]
  simp

/-- The product of a bounded measurable function of the two i.i.d. Gaussian coordinates is the
square of its Gaussian mean. -/
theorem integral_pi_fin_two_mul {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, |φ x| ≤ B) :
    ∫ σ : Fin 2 → ℝ, φ (σ 0) * φ (σ 1) ∂(Measure.pi fun _ : Fin 2 => gaussianReal 0 1) =
      (∫ x, φ x ∂(gaussianReal 0 1)) ^ 2 := by
  have hbd : ∀ x y, |φ x * φ y| ≤ B * B := fun x y => by
    rw [abs_mul]; exact mul_le_mul (hB x) (hB y) (abs_nonneg _) ((abs_nonneg _).trans (hB 0))
  rw [integral_pi_fin_two_gaussianReal (G := fun x y => φ x * φ y)
    ((hφ.comp measurable_fst).mul (hφ.comp measurable_snd)) hbd]
  simp [integral_mul_const, integral_const_mul, sq]

/-- The Gaussian smoothing `c ↦ 𝔼 f (c + s ξ)` of a bounded continuous function is continuous. -/
theorem continuous_integral_comp_add_mul {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) (s : ℝ) :
    Continuous fun c : ℝ => ∫ ξ, f (c + s * ξ) ∂(gaussianReal 0 1) :=
  continuous_of_dominated (bound := fun _ => M)
    (fun c => (hf.comp (by fun_prop : Continuous fun ξ : ℝ => c + s * ξ)).aestronglyMeasurable)
    (fun c => ae_of_all _ fun ξ => by rw [Real.norm_eq_abs]; exact hM _) (integrable_const _)
    (ae_of_all _ fun ξ => hf.comp (by fun_prop))

end Block

section Gibbs

variable {N : ℕ} {α : Type*} [Fintype α]

theorem integral_sq_sub_le (hN : 0 < N) (x : α → Fin N → ℝ) {w : α → ℝ} (hw : ∀ a, 0 ≤ w a)
    (hw1 : ∑ a, w a = 1) {q ρ : ℝ} (hq : 0 ≤ q) (hqρ : q ≤ ρ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    {M0 M1 M2 : ℝ} (h0 : ∀ x, |f x| ≤ M0) (h1 : ∀ x, |deriv f x| ≤ M1)
    (h2 : ∀ x, |deriv (deriv f) x| ≤ M2) :
    ∫ g, (∑ a, w a * f ((Real.sqrt N)⁻¹ * (x a ⬝ᵥ g)) -
        ∫ ξ, f ((Real.sqrt N)⁻¹ * ((∑ a, w a • x a) ⬝ᵥ g) + Real.sqrt (ρ - q) * ξ)
          ∂(gaussianReal 0 1)) ^ 2 ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) ≤
      2 * (2 * M1 ^ 2 + M0 * M2) * (∑ a, ∑ a', w a * w a' *
          |(N : ℝ)⁻¹ * (x a ⬝ᵥ x a') - q| + ∑ a, w a * |(N : ℝ)⁻¹ * (x a ⬝ᵥ x a) - ρ|) := by
  classical
  have hfc : Continuous f := hf.continuous
  have hM0 : 0 ≤ M0 := (abs_nonneg _).trans (h0 0)
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  obtain ⟨u, hu⟩ : ∃ u : α → Fin N → ℝ, ∀ a, u a = (Real.sqrt N)⁻¹ • x a := ⟨_, fun _ => rfl⟩
  obtain ⟨bb, hbb⟩ : ∃ bb : Fin N → ℝ, bb = ∑ a, w a • u a := ⟨_, rfl⟩
  have hua : ∀ a g, (Real.sqrt N)⁻¹ * (x a ⬝ᵥ g) = u a ⬝ᵥ g := fun a g => by
    simp [hu, smul_dotProduct]
  have hb : ∀ g, (Real.sqrt N)⁻¹ * ((∑ a, w a • x a) ⬝ᵥ g) = bb ⬝ᵥ g := fun g => by
    simp [hbb, hu, sum_dotProduct, smul_dotProduct, Finset.mul_sum, mul_left_comm]
  have hR : ∀ a a', u a ⬝ᵥ u a' = (N : ℝ)⁻¹ * (x a ⬝ᵥ x a') := fun a a' => by
    simp only [hu, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hNpos.le]
  simp only [hua, hb, ← hR]
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt (ρ - q) := ⟨_, rfl⟩
  have hss : s * s = ρ - q := by rw [hs]; exact Real.mul_self_sqrt (sub_nonneg.2 hqρ)
  rw [← hs]
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∫ ζ, f (![Real.sqrt q, Real.sqrt (ρ - q), 0] ⬝ᵥ ζ) *
      f (![Real.sqrt q, 0, Real.sqrt (ρ - q)] ⬝ᵥ ζ)
      ∂(Measure.pi fun _ : Fin 3 => gaussianReal 0 1) := ⟨_, rfl⟩
  obtain ⟨blk, hblk⟩ : ∃ blk : (Fin N → ℝ) → (Fin N → ℝ) → (Fin 2 → ℝ) → (Fin 2 → ℝ) → ℝ,
      ∀ u₁ v₁ u₂ v₂, blk u₁ v₁ u₂ v₂ = ∫ g, ∫ ξ, f (u₁ ⬝ᵥ g + u₂ ⬝ᵥ ξ) * f (v₁ ⬝ᵥ g + v₂ ⬝ᵥ ξ)
        ∂(Measure.pi fun _ : Fin 2 => gaussianReal 0 1)
        ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) := ⟨_, fun _ _ _ _ => rfl⟩
  have hblkT : ∀ u₁ v₁ u₂ v₂, |blk u₁ v₁ u₂ v₂ - T| ≤ M1 ^ 2 * |u₁ ⬝ᵥ v₁ + u₂ ⬝ᵥ v₂ - q| +
      M0 * M2 / 2 * (|u₁ ⬝ᵥ u₁ + u₂ ⬝ᵥ u₂ - ρ| + |v₁ ⬝ᵥ v₁ + v₂ ⬝ᵥ v₂ - ρ|) :=
    fun u₁ v₁ u₂ v₂ => by
      rw [hblk, hT]; exact abs_integral_block_sub_le hq hqρ u₁ v₁ u₂ v₂ hf h0 h1 h2
  obtain ⟨Vf, hVf⟩ : ∃ Vf : ℝ → ℝ, ∀ c, Vf c = ∫ ξ, f (c + s * ξ) ∂(gaussianReal 0 1) :=
    ⟨_, fun _ => rfl⟩
  have hVfc : Continuous Vf := by
    have := continuous_integral_comp_add_mul hfc h0 s
    rwa [show Vf = fun c => ∫ ξ, f (c + s * ξ) ∂(gaussianReal 0 1) from funext hVf]
  have hVfb : ∀ c, |Vf c| ≤ M0 := fun c => by
    rw [hVf]
    have := norm_integral_le_of_norm_le_const (μ := gaussianReal 0 1)
      (f := fun ξ => f (c + s * ξ)) (C := M0) (ae_of_all _ fun ξ => by
        rw [Real.norm_eq_abs]; exact h0 _)
    simpa using this
  simp only [← hVf]
  have hint : ∀ φ : (Fin N → ℝ) → ℝ, Continuous φ → ∀ C : ℝ, (∀ g, |φ g| ≤ C) →
      Integrable φ (Measure.pi fun _ : Fin N => gaussianReal 0 1) := fun φ hφ C hC =>
    Integrable.of_bound hφ.aestronglyMeasurable C (ae_of_all _ fun g => by
      rw [Real.norm_eq_abs]; exact hC g)
  have hdotc : ∀ v : Fin N → ℝ, Continuous fun g : Fin N → ℝ => v ⬝ᵥ g := fun v => by
    simp only [dotProduct]; fun_prop
  obtain ⟨U, hU⟩ : ∃ U : (Fin N → ℝ) → ℝ, ∀ g, U g = ∑ a, w a * f (u a ⬝ᵥ g) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : (Fin N → ℝ) → ℝ, ∀ g, V g = Vf (bb ⬝ᵥ g) := ⟨_, fun _ => rfl⟩
  simp only [← hU, ← hV]
  have hUc : Continuous U := by
    rw [show U = fun g => ∑ a, w a * f (u a ⬝ᵥ g) from funext hU]
    exact continuous_finsetSum _ fun a _ => continuous_const.mul (hfc.comp (hdotc _))
  have hVc : Continuous V := by
    rw [show V = fun g => Vf (bb ⬝ᵥ g) from funext hV]
    exact hVfc.comp (hdotc _)
  have hUb : ∀ g, |U g| ≤ M0 := fun g => by
    rw [hU]; exact abs_sum_mul_le hw hw1 fun a => h0 _
  have hVb : ∀ g, |V g| ≤ M0 := fun g => by rw [hV]; exact hVfb _
  have hUV : ∀ g, |U g * V g| ≤ M0 * M0 := fun g => by
    rw [abs_mul]; exact mul_le_mul (hUb g) (hVb g) (abs_nonneg _) hM0
  have hexp : ∫ g, (U g - V g) ^ 2 ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      ∫ g, U g ^ 2 ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) -
        2 * ∫ g, U g * V g ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) +
        ∫ g, V g ^ 2 ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) := by
    have hi1 : Integrable (fun g => U g ^ 2) (Measure.pi fun _ : Fin N => gaussianReal 0 1) :=
      hint _ (hUc.pow 2) (M0 * M0) fun g => by
        rw [abs_pow, sq]; exact mul_le_mul (hUb g) (hUb g) (abs_nonneg _) hM0
    have hi2 : Integrable (fun g => U g * V g) (Measure.pi fun _ : Fin N => gaussianReal 0 1) :=
      hint _ (hUc.mul hVc) _ hUV
    have hi3 : Integrable (fun g => V g ^ 2) (Measure.pi fun _ : Fin N => gaussianReal 0 1) :=
      hint _ (hVc.pow 2) (M0 * M0) fun g => by
        rw [abs_pow, sq]; exact mul_le_mul (hVb g) (hVb g) (abs_nonneg _) hM0
    have hi12 : Integrable (fun g => U g ^ 2 - 2 * (U g * V g))
        (Measure.pi fun _ : Fin N => gaussianReal 0 1) := hi1.sub (hi2.const_mul 2)
    rw [show (fun g => (U g - V g) ^ 2) = fun g => (U g ^ 2 - 2 * (U g * V g)) + V g ^ 2 from
      funext fun g => by ring, integral_add hi12 hi3, integral_sub hi1 (hi2.const_mul 2),
      integral_const_mul]
  rw [hexp]
  have hdot0 : ∀ ξ : Fin 2 → ℝ, ![s, 0] ⬝ᵥ ξ = s * ξ 0 := fun ξ => by
    simp [dotProduct, Fin.sum_univ_two]
  have hdot1 : ∀ ξ : Fin 2 → ℝ, ![0, s] ⬝ᵥ ξ = s * ξ 1 := fun ξ => by
    simp [dotProduct, Fin.sum_univ_two]
  have hE1 : ∫ g, U g ^ 2 ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      ∑ a, ∑ a', w a * w a' * blk (u a) (u a') 0 0 := by
    have hz : ∀ a a', blk (u a) (u a') 0 0 =
        ∫ g, f (u a ⬝ᵥ g) * f (u a' ⬝ᵥ g) ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) :=
      fun a a' => by rw [hblk]; simp
    have hterm : ∀ a a', Integrable (fun g => w a * w a' * (f (u a ⬝ᵥ g) * f (u a' ⬝ᵥ g)))
        (Measure.pi fun _ : Fin N => gaussianReal 0 1) := fun a a' =>
      hint _ (continuous_const.mul ((hfc.comp (hdotc _)).mul (hfc.comp (hdotc _))))
        (w a * w a' * (M0 * M0)) fun g => by
          rw [abs_mul, abs_of_nonneg (mul_nonneg (hw a) (hw a')), abs_mul]
          exact mul_le_mul_of_nonneg_left (mul_le_mul (h0 _) (h0 _) (abs_nonneg _) hM0)
            (mul_nonneg (hw a) (hw a'))
    simp_rw [hU, sq_sum_mul_eq]
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun a' _ => hterm a a')]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun a' _ => hterm a a']
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [integral_const_mul, hz]
  have hmeasφ : ∀ c : ℝ, Measurable fun x : ℝ => f (c + s * x) := fun c =>
    (hfc.comp (by fun_prop : Continuous fun x : ℝ => c + s * x)).measurable
  have hE2 : ∫ g, U g * V g ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      ∑ a, w a * blk (u a) bb 0 ![s, 0] := by
    have hz : ∀ a, blk (u a) bb 0 ![s, 0] =
        ∫ g, f (u a ⬝ᵥ g) * V g ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) := fun a => by
      rw [hblk]
      refine integral_congr_ae (ae_of_all _ fun g => ?_)
      simp only [zero_dotProduct, add_zero, hdot0]
      rw [integral_const_mul, hV, hVf]
      congr 1
      exact integral_pi_fin_two_fst (φ := fun x => f (bb ⬝ᵥ g + s * x)) (hmeasφ _) fun x => h0 _
    have hterm : ∀ a, Integrable (fun g => w a * (f (u a ⬝ᵥ g) * V g))
        (Measure.pi fun _ : Fin N => gaussianReal 0 1) := fun a =>
      hint _ (continuous_const.mul ((hfc.comp (hdotc _)).mul hVc)) (w a * (M0 * M0)) fun g => by
        rw [abs_mul, abs_of_nonneg (hw a), abs_mul]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (h0 _) (hVb g) (abs_nonneg _) hM0) (hw a)
    simp_rw [hU, Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum _ fun a _ => hterm a]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_const_mul, hz]
  have hE3 : ∫ g, V g ^ 2 ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) =
      blk bb bb ![s, 0] ![0, s] := by
    rw [hblk]
    refine integral_congr_ae (ae_of_all _ fun g => ?_)
    simp only [hdot0, hdot1]
    rw [integral_pi_fin_two_mul (φ := fun x => f (bb ⬝ᵥ g + s * x)) (hmeasφ _) fun x => h0 _,
      hV, hVf]
  rw [hE1, hE2, hE3]
  have hww : ∀ c : ℝ, ∑ a, ∑ a', w a * w a' * c = c := fun c => by
    simp_rw [sum_mul_mul_const hw1, sum_mul_const_of_sum_eq_one hw1]
  have hub : ∀ a, u a ⬝ᵥ bb = ∑ a', w a' * (u a ⬝ᵥ u a') := fun a => by
    simp [hbb, dotProduct_sum, dotProduct_smul]
  have hbb2 : bb ⬝ᵥ bb = ∑ a, ∑ a', w a * w a' * (u a ⬝ᵥ u a') := by
    calc bb ⬝ᵥ bb = (∑ a, w a • u a) ⬝ᵥ bb := by rw [← hbb]
      _ = ∑ a, w a * (u a ⬝ᵥ bb) := by simp [sum_dotProduct, smul_dotProduct]
      _ = _ := by simp_rw [hub, Finset.mul_sum, mul_assoc]
  obtain ⟨ε1, hε1⟩ : ∃ ε1 : ℝ, ε1 = ∑ a, ∑ a', w a * w a' * |u a ⬝ᵥ u a' - q| := ⟨_, rfl⟩
  obtain ⟨ε2, hε2⟩ : ∃ ε2 : ℝ, ε2 = ∑ a, w a * |u a ⬝ᵥ u a - ρ| := ⟨_, rfl⟩
  rw [← hε1, ← hε2]
  have hε1nn : 0 ≤ ε1 := by
    rw [hε1]
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun a' _ =>
      mul_nonneg (mul_nonneg (hw a) (hw a')) (abs_nonneg _)
  have hε2nn : 0 ≤ ε2 := by
    rw [hε2]; exact Finset.sum_nonneg fun a _ => mul_nonneg (hw a) (abs_nonneg _)
  have hβ : |bb ⬝ᵥ bb - q| ≤ ε1 := by
    have : bb ⬝ᵥ bb - q = ∑ a, ∑ a', w a * w a' * (u a ⬝ᵥ u a' - q) := by
      rw [hbb2]; simp [mul_sub, Finset.sum_sub_distrib, hww]
    rw [this, hε1]; exact abs_sum_sum_mul_le hw _
  have hua_q : ∀ a, |u a ⬝ᵥ bb - q| ≤ ∑ a', w a' * |u a ⬝ᵥ u a' - q| := fun a => by
    have : u a ⬝ᵥ bb - q = ∑ a', w a' * (u a ⬝ᵥ u a' - q) := by
      rw [hub]; simp [mul_sub, Finset.sum_sub_distrib, sum_mul_const_of_sum_eq_one hw1]
    rw [this]; exact abs_sum_mul_le_sum_mul_abs hw
  have he00 : (![s, 0] : Fin 2 → ℝ) ⬝ᵥ ![s, 0] = s * s := by simp [dotProduct, Fin.sum_univ_two]
  have he11 : (![0, s] : Fin 2 → ℝ) ⬝ᵥ ![0, s] = s * s := by simp [dotProduct, Fin.sum_univ_two]
  have he01 : (![s, 0] : Fin 2 → ℝ) ⬝ᵥ ![0, s] = 0 := by simp [dotProduct, Fin.sum_univ_two]
  have hB1 : |∑ a, ∑ a', w a * w a' * blk (u a) (u a') 0 0 - T| ≤
      M1 ^ 2 * ε1 + M0 * M2 * ε2 := by
    have e1 : ∑ a, ∑ a', w a * w a' * blk (u a) (u a') 0 0 - T =
        ∑ a, ∑ a', w a * w a' * (blk (u a) (u a') 0 0 - T) := by
      simp [mul_sub, Finset.sum_sub_distrib, hww]
    rw [e1]
    refine (abs_sum_sum_mul_le hw _).trans ?_
    have hB_a : ∑ a, ∑ a', w a * w a' * |u a ⬝ᵥ u a - ρ| = ε2 := by
      rw [hε2]; exact Finset.sum_congr rfl fun a _ => sum_mul_mul_const hw1 (w a) _
    have hB_a' : ∑ a, ∑ a', w a * w a' * |u a' ⬝ᵥ u a' - ρ| = ε2 := by
      rw [Finset.sum_comm, hε2]
      exact Finset.sum_congr rfl fun a' _ => sum_mul_mul_const_left hw1 (w a') _
    calc ∑ a, ∑ a', w a * w a' * |blk (u a) (u a') 0 0 - T| ≤ ∑ a, ∑ a', w a * w a' *
          (M1 ^ 2 * |u a ⬝ᵥ u a' - q| + M0 * M2 / 2 * (|u a ⬝ᵥ u a - ρ| + |u a' ⬝ᵥ u a' - ρ|)) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun a' _ =>
            mul_le_mul_of_nonneg_left (by simpa using hblkT (u a) (u a') 0 0)
              (mul_nonneg (hw a) (hw a'))
      _ = M1 ^ 2 * ε1 + M0 * M2 * ε2 := by
          have hexp : ∀ a a' : α, w a * w a' * (M1 ^ 2 * |u a ⬝ᵥ u a' - q| + M0 * M2 / 2 *
              (|u a ⬝ᵥ u a - ρ| + |u a' ⬝ᵥ u a' - ρ|)) = M1 ^ 2 * (w a * w a' *
              |u a ⬝ᵥ u a' - q|) + M0 * M2 / 2 * (w a * w a' * |u a ⬝ᵥ u a - ρ|) +
              M0 * M2 / 2 * (w a * w a' * |u a' ⬝ᵥ u a' - ρ|) := fun a a' => by ring
          simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, hB_a, hB_a', ← hε1]
          ring
  have hM1 : 0 ≤ M1 := (abs_nonneg _).trans (h1 0)
  have hM2 : 0 ≤ M2 := (abs_nonneg _).trans (h2 0)
  have hB2pt : ∀ a, |blk (u a) bb 0 ![s, 0] - T| ≤ M1 ^ 2 * (∑ a', w a' * |u a ⬝ᵥ u a' - q|) +
      M0 * M2 / 2 * (|u a ⬝ᵥ u a - ρ| + ε1) := fun a => by
    have h := hblkT (u a) bb 0 ![s, 0]
    have e : bb ⬝ᵥ bb + ![s, 0] ⬝ᵥ ![s, 0] - ρ = bb ⬝ᵥ bb - q := by rw [he00, hss]; ring
    simp only [zero_dotProduct, add_zero] at h
    rw [e] at h
    refine h.trans (add_le_add (mul_le_mul_of_nonneg_left (hua_q a) (sq_nonneg _))
      (mul_le_mul_of_nonneg_left (add_le_add_right hβ _) (by positivity)))
  have hB2 : |∑ a, w a * blk (u a) bb 0 ![s, 0] - T| ≤
      M1 ^ 2 * ε1 + M0 * M2 / 2 * (ε2 + ε1) := by
    have e2 : ∑ a, w a * blk (u a) bb 0 ![s, 0] - T =
        ∑ a, w a * (blk (u a) bb 0 ![s, 0] - T) := by
      simp [mul_sub, Finset.sum_sub_distrib, sum_mul_const_of_sum_eq_one hw1]
    rw [e2]
    refine (abs_sum_mul_le_sum_mul_abs hw).trans ?_
    have hS : ∑ a, w a * (∑ a', w a' * |u a ⬝ᵥ u a' - q|) = ε1 := by
      rw [hε1]; simp_rw [Finset.mul_sum, ← mul_assoc]
    have hsumε : ∑ a, w a * ε1 = ε1 := sum_mul_const_of_sum_eq_one hw1 ε1
    calc ∑ a, w a * |blk (u a) bb 0 ![s, 0] - T| ≤ ∑ a, w a * (M1 ^ 2 *
          (∑ a', w a' * |u a ⬝ᵥ u a' - q|) + M0 * M2 / 2 * (|u a ⬝ᵥ u a - ρ| + ε1)) :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hB2pt a) (hw a)
      _ = M1 ^ 2 * ε1 + M0 * M2 / 2 * (ε2 + ε1) := by
          have hexp : ∀ a : α, w a * (M1 ^ 2 * (∑ a', w a' * |u a ⬝ᵥ u a' - q|) + M0 * M2 / 2 *
              (|u a ⬝ᵥ u a - ρ| + ε1)) = M1 ^ 2 * (w a * (∑ a', w a' * |u a ⬝ᵥ u a' - q|)) +
              M0 * M2 / 2 * (w a * |u a ⬝ᵥ u a - ρ|) + M0 * M2 / 2 * (w a * ε1) := fun a => by
            ring
          simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, hS, ← hε2, hsumε]
          ring
  have hB3 : |blk bb bb ![s, 0] ![0, s] - T| ≤ (M1 ^ 2 + M0 * M2) * ε1 := by
    have h := hblkT bb bb ![s, 0] ![0, s]
    rw [he01, he00, he11, hss, add_zero] at h
    have e : bb ⬝ᵥ bb + (ρ - q) - ρ = bb ⬝ᵥ bb - q := by ring
    rw [e] at h
    refine h.trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hβ (sq_nonneg M1),
      mul_le_mul_of_nonneg_left hβ (mul_nonneg hM0 hM2)]
  have hM1sq : 0 ≤ M1 ^ 2 * ε2 := mul_nonneg (sq_nonneg _) hε2nn
  have hM02 : 0 ≤ M0 * M2 := mul_nonneg hM0 hM2
  have hlo1 := abs_le.1 hB1
  have hlo2 := abs_le.1 hB2
  have hlo3 := abs_le.1 hB3
  nlinarith [hlo1.1, hlo1.2, hlo2.1, hlo2.2, hlo3.1, hlo3.2, hM1sq, mul_nonneg hM02 hε1nn,
    mul_nonneg hM02 hε2nn]

end Gibbs

section SK

/-- **A kind of central limit theorem for the SK Gibbs measure (Talagrand, Section 1.5).**  For
`β² < 1/4` at the fixed point `q`, a standard Gaussian vector `z` of projection directions and a
`C²` function `f` with `|f| ≤ M₀`, `|f'| ≤ M₁`, `|f''| ≤ M₂`, the Gibbs average
`U = ⟨f (σ ⬝ z / √N)⟩` is close in mean square, over `z` and the disorder, to the Gaussian
average `V = 𝔼_ξ f (⟨σ⟩ ⬝ z / √N + ξ √(1 - q))`, where `⟨σ⟩` is the vector of magnetizations:
`𝔼 (U - V)² ≤ 2 (2 M₁² + M₀ M₂) √(K / N)` with the overlap constant `K` of
`sk_expected_sq_overlap_le`. -/
theorem sk_random_projection_le {N : ℕ} (hN : 0 < N) (β h q : ℝ)
    (hfix : ∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (hβ : β ^ 2 < 1 / 4) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {M0 M1 M2 : ℝ}
    (h0 : ∀ x, |f x| ≤ M0) (h1 : ∀ x, |deriv f x| ≤ M1) (h2 : ∀ x, |deriv (deriv f) x| ≤ M2) :
    ∫ g : FinPairs N → ℝ, ∫ z : Fin N → ℝ,
        (∫ σ : Fin N → ℤˣ, f ((Real.sqrt N)⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ z))
            ∂(Measure.count.tilted fun a => (Real.sqrt N)⁻¹ * β *
              (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
              h * ∑ i, ((a i : ℤ) : ℝ)) -
          ∫ ξ, f ((Real.sqrt N)⁻¹ * ((fun i => ∫ σ : Fin N → ℤˣ, ((σ i : ℤ) : ℝ)
              ∂(Measure.count.tilted fun a => (Real.sqrt N)⁻¹ * β *
                (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
                h * ∑ i, ((a i : ℤ) : ℝ))) ⬝ᵥ z) + Real.sqrt (1 - q) * ξ)
            ∂(gaussianReal 0 1)) ^ 2 ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
      2 * (2 * M1 ^ 2 + M0 * M2) *
        Real.sqrt (((Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ - 1) / ((1 / 4 - β ^ 2) * N)) := by
  have hq01 : q ∈ Set.Icc (0 : ℝ) 1 := hfix ▸ fixedPointMap_mem_Icc β h q
  obtain ⟨E, hE⟩ : ∃ E : (FinPairs N → ℝ) → (Fin N → ℤˣ) → ℝ, ∀ g a, E g a =
      (Real.sqrt N)⁻¹ * β *
        (∑ p : FinPairs N, g p * ((a p.val.1 : ℤ) : ℝ) * ((a p.val.2 : ℤ) : ℝ)) +
        h * ∑ i, ((a i : ℤ) : ℝ) := ⟨_, fun _ _ => rfl⟩
  simp only [← hE]
  obtain ⟨hw0, hw1, hwm, -⟩ := sk_gibbsWeight_siteSymmetric β h E hE
  obtain ⟨xv, hxv⟩ : ∃ xv : (Fin N → ℤˣ) → Fin N → ℝ, ∀ σ, xv σ = fun i => ((σ i : ℤ) : ℝ) :=
    ⟨_, fun _ => rfl⟩
  have hxx : ∀ σ, (N : ℝ)⁻¹ * (xv σ ⬝ᵥ xv σ) = 1 := fun σ => by
    have : xv σ ⬝ᵥ xv σ = N := by
      simp only [hxv, dotProduct]
      rw [Finset.sum_congr rfl fun i _ => (by rcases Int.units_eq_one_or (σ i) with h1 | h1 <;>
        simp [h1] : ((σ i : ℤ) : ℝ) * ((σ i : ℤ) : ℝ) = 1)]
      simp
    rw [this, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hN.ne')]
  have hZ : ∀ g, 0 < ∑ b, Real.exp (E g b) := fun g =>
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  obtain ⟨ε, hε⟩ : ∃ ε : (FinPairs N → ℝ) → ℝ, ∀ g, ε g = ∑ a, ∑ a',
      Real.exp (E g a) / (∑ b, Real.exp (E g b)) * (Real.exp (E g a') / ∑ b, Real.exp (E g b)) *
        |(N : ℝ)⁻¹ * (xv a ⬝ᵥ xv a') - q| := ⟨_, fun _ => rfl⟩
  have hpt : ∀ g, ∫ z : Fin N → ℝ,
      (∫ σ : Fin N → ℤˣ, f ((Real.sqrt N)⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ z))
          ∂(Measure.count.tilted (E g)) -
        ∫ ξ, f ((Real.sqrt N)⁻¹ * ((fun i => ∫ σ : Fin N → ℤˣ, ((σ i : ℤ) : ℝ)
            ∂(Measure.count.tilted (E g))) ⬝ᵥ z) + Real.sqrt (1 - q) * ξ)
          ∂(gaussianReal 0 1)) ^ 2 ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1) ≤
      2 * (2 * M1 ^ 2 + M0 * M2) * ε g := fun g => by
    have h := integral_sq_sub_le hN xv (w := fun σ => Real.exp (E g σ) / ∑ b, Real.exp (E g b))
      (hw0 g) (hw1 g) hq01.1 (ρ := 1) hq01.2 hf h0 h1 h2
    simp only [hxx, sub_self, abs_zero, mul_zero, Finset.sum_const_zero, add_zero] at h
    have hb : (∑ a, (Real.exp (E g a) / ∑ b, Real.exp (E g b)) • xv a) =
        fun i => ∑ a, Real.exp (E g a) / (∑ b, Real.exp (E g b)) * ((a i : ℤ) : ℝ) := by
      funext i
      simp [hxv, Finset.sum_apply]
    rw [hb] at h
    simp only [hxv] at h
    simp only [integral_count_tilted]
    rw [hε]
    simp only [hxv]
    exact h
  -- the weighted average `ε` of `|R - q|` and its square
  have hεint : Integrable ε (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
    have : ε = fun g => (fun v : (Fin N → ℤˣ) → ℝ => ∑ a, ∑ a', v a * v a' *
        |(N : ℝ)⁻¹ * (xv a ⬝ᵥ xv a') - q|)
        (fun σ => Real.exp (E g σ) / ∑ b, Real.exp (E g b)) := funext hε
    rw [this]
    exact integrable_comp_weights hw0 hw1 hwm (Ψ := fun v : (Fin N → ℤˣ) → ℝ =>
      ∑ a, ∑ a', v a * v a' * |(N : ℝ)⁻¹ * (xv a ⬝ᵥ xv a') - q|) (by fun_prop)
  have hεm : Measurable ε := by
    have : ε = fun g => (fun v : (Fin N → ℤˣ) → ℝ => ∑ a, ∑ a', v a * v a' *
        |(N : ℝ)⁻¹ * (xv a ⬝ᵥ xv a') - q|)
        (fun σ => Real.exp (E g σ) / ∑ b, Real.exp (E g b)) := funext hε
    rw [this]
    exact (by fun_prop : Continuous fun v : (Fin N → ℤˣ) → ℝ => ∑ a, ∑ a', v a * v a' *
      |(N : ℝ)⁻¹ * (xv a ⬝ᵥ xv a') - q|).measurable.comp (measurable_pi_iff.2 hwm)
  have hεsq : Integrable (fun g => ε g ^ 2)
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
    have : (fun g => ε g ^ 2) = fun g => (fun v : (Fin N → ℤˣ) → ℝ => (∑ a, ∑ a', v a * v a' *
        |(N : ℝ)⁻¹ * (xv a ⬝ᵥ xv a') - q|) ^ 2)
        (fun σ => Real.exp (E g σ) / ∑ b, Real.exp (E g b)) := by
      funext g; rw [hε]
    rw [this]
    exact integrable_comp_weights hw0 hw1 hwm (Ψ := fun v : (Fin N → ℤˣ) → ℝ =>
      (∑ a, ∑ a', v a * v a' * |(N : ℝ)⁻¹ * (xv a ⬝ᵥ xv a') - q|) ^ 2) (by fun_prop)
  have hov := sk_expected_sq_overlap_le_weights hN β h q hfix hβ E hE
  have hAint : Integrable (fun g => ∑ a, ∑ a', Real.exp (E g a) / (∑ b, Real.exp (E g b)) *
      (Real.exp (E g a') / ∑ b, Real.exp (E g b)) * ((N : ℝ)⁻¹ * (xv a ⬝ᵥ xv a') - q) ^ 2)
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) :=
    integrable_comp_weights hw0 hw1 hwm (Ψ := fun v : (Fin N → ℤˣ) → ℝ => ∑ a, ∑ a',
      v a * v a' * ((N : ℝ)⁻¹ * (xv a ⬝ᵥ xv a') - q) ^ 2) (by fun_prop)
  have hεA : ∀ g, ε g ^ 2 ≤ ∑ a, ∑ a', Real.exp (E g a) / (∑ b, Real.exp (E g b)) *
      (Real.exp (E g a') / ∑ b, Real.exp (E g b)) * ((N : ℝ)⁻¹ * (xv a ⬝ᵥ xv a') - q) ^ 2 :=
    fun g => by
    rw [hε]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    calc _ ≤ ∑ a, Real.exp (E g a) / (∑ b, Real.exp (E g b)) *
          (∑ a', Real.exp (E g a') / (∑ b, Real.exp (E g b)) *
            |(N : ℝ)⁻¹ * (xv a ⬝ᵥ xv a') - q|) ^ 2 :=
          sq_sum_mul_le_sum_mul_sq (hw0 g) (hw1 g)
      _ ≤ _ := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
          ((sq_sum_mul_le_sum_mul_sq (hw0 g) (hw1 g)).trans (le_of_eq
            (Finset.sum_congr rfl fun a' _ => by rw [sq_abs]))) (hw0 g a)
  have hεint2 : (∫ g, ε g ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) ^ 2 ≤
      ((Real.sqrt (1 / 2 - 2 * β ^ 2))⁻¹ - 1) / ((1 / 4 - β ^ 2) * N) :=
    (sq_integral_le_integral_sq hεm hεsq).trans ((integral_mono hεsq hAint hεA).trans (by
      simp only [hxv]; exact hov))
  have hεnn : ∀ g, 0 ≤ ε g := fun g => by
    rw [hε]
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun a' _ =>
      mul_nonneg (mul_nonneg (div_nonneg (Real.exp_pos _).le (hZ g).le)
        (div_nonneg (Real.exp_pos _).le (hZ g).le)) (abs_nonneg _)
  have hmain : ∫ g, ∫ z : Fin N → ℝ,
      (∫ σ : Fin N → ℤˣ, f ((Real.sqrt N)⁻¹ * ((fun i => ((σ i : ℤ) : ℝ)) ⬝ᵥ z))
          ∂(Measure.count.tilted (E g)) -
        ∫ ξ, f ((Real.sqrt N)⁻¹ * ((fun i => ∫ σ : Fin N → ℤˣ, ((σ i : ℤ) : ℝ)
            ∂(Measure.count.tilted (E g))) ⬝ᵥ z) + Real.sqrt (1 - q) * ξ)
          ∂(gaussianReal 0 1)) ^ 2 ∂(Measure.pi fun _ : Fin N => gaussianReal 0 1)
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) ≤
      ∫ g, 2 * (2 * M1 ^ 2 + M0 * M2) * ε g ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) :=
    integral_mono_of_nonneg (ae_of_all _ fun g => integral_nonneg fun z => sq_nonneg _)
      (hεint.const_mul _) (ae_of_all _ hpt)
  rw [integral_const_mul] at hmain
  have hM0 : 0 ≤ M0 := (abs_nonneg _).trans (h0 0)
  have hM2 : 0 ≤ M2 := (abs_nonneg _).trans (h2 0)
  refine hmain.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg zero_le_two
    (add_nonneg (by positivity) (mul_nonneg hM0 hM2))))
  exact Real.le_sqrt_of_sq_le hεint2

end SK

end SpinGlasses
