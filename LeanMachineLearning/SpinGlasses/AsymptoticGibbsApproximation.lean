/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianContinuity
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianGram
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianExp
public import LeanMachineLearning.ForMathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Gram-matrix approximation of Gibbs averages (Panchenko, Theorem 1.3)

Let `Γ = ∑ᵢ wᵢ δ_{ρⁱ}` be a finitely supported probability measure on the unit sphere of a Hilbert
space, `z`, `y` centered Gaussian processes with `𝔼 z(ρ¹) z(ρ²) = Cz (ρ¹ ⬝ ρ²)` and
`𝔼 y(ρ¹) y(ρ²) = Cy (ρ¹ ⬝ ρ²)`, and
`Φ(Γ) = 𝔼 log ⟨2 cosh z⟩ - 𝔼 log ⟨exp y⟩`, `⟨f⟩ = ∑ᵢ wᵢ f(ρⁱ)`
([Panchenko, 2013, Eqs. (1.61)–(1.64)]).  **Theorem 1.3**: `Φ(Γ)` is, up to an arbitrary `ε`,
the `Γ`-average of a continuous bounded function of the Gram matrix of finitely many i.i.d.
replicas `ρ¹, …, ρᵐ ~ Γ`, uniformly in `Γ`.

## Proof

1. *Truncation* (`abs_integral_log_sub_integral_log_clamp_le`, Eqs. (1.65), (1.68)–(1.72)).  With
   `X = ⟨φ(g)⟩ > 0` and `ℓ_a x = log (max (min x e^a) e^{-a})`, the error of replacing `log X` by
   `ℓ_a (⟨φ(clamp_a g)⟩)` is `≤ C e^{-a}`, `C` depending only on the sub-Gaussian parameter, not on
   the number of atoms.  It is the sum of `𝔼 (|log X| - a)₊ ≤ e^{-a} 𝔼 (X + X⁻¹)` (using
   `𝔼 ⟨φ(g)⟩`, `𝔼 ⟨φ(g)⁻¹⟩ ≤ C'` by Jensen) and of `e^a 𝔼 |X - ⟨φ(clamp_a g)⟩|`, the latter bounded
   by the exponential moments `𝔼 e^{3|gᵢ|}` through the pointwise bound
   `|φ x - φ (clamp_a x)| ≤ 2 A e^{-2a} e^{3|x|}`.  For `φ = 2 cosh` the truncated observable
   `φ (clamp_a x) = 2 min (cosh x, cosh a)` is exactly the book's `ch_a`.
2. *Polynomial approximation* (`exists_polynomial_integral_log_approx`, Eq. (1.66)): `ℓ_a` is
   approximated uniformly on `[0, A e^a]` by a polynomial (Weierstrass,
   `exists_polynomial_near_of_continuousOn`).
3. *Moment expansion* (`integral_pow_sum_mul_comp_eq`, Eq. (1.67)): `⟨ψ(g)⟩^k` expands over `k`
   replicas, and `𝔼 ∏ₗ ψ(g_{jₗ})` is a Gaussian integral
   `∫ ∏ₗ ψ(xₗ) d𝒩(0, (𝔼 g_{jₗ} g_{jₗ'}))`, a function of the covariance matrix of the replicas
   only (`ForMathlib/Probability/Moments/GaussianGram.lean`).  It is continuous and bounded in the
   Gram matrix (`continuousOn_integral_prod_multivariateGaussian`, by Lévy's continuity theorem,
   `ForMathlib/Probability/Moments/GaussianContinuity.lean`).
4. *Theorem 1.3* (`exists_gram_approx_free_energy`, `exists_continuousOn_gram_approx`): the two
   terms of `Φ` are treated separately (`φ = 2 cosh` and `φ = exp`) and the finitely many
   replica-numbers `k ≤ deg` are merged into a single function of `m` replicas
   (`sum_prod_mul_comp_castLE`).

## Deviations from the book

* No Hilbert space appears: `Φ` depends on `Γ` only through the weights `w` and the Gram data
  `q i j = ρⁱ ⬝ ρʲ`, so the theorem is stated for an arbitrary finite family and arbitrary
  covariance functions.  Only finitely supported `Γ` are treated (the Gibbs measures `G'_N` of the
  SK model are such); the extension to countably many atoms is a limiting argument.
* The truncation error is controlled by first moments of `X` and `X⁻¹` and by exponential
  moments of the coordinates, instead of the Gaussian concentration of `log ⟨cosh z⟩`
  (Eq. (1.69)): only the expectation of the error is needed, and the moment bounds
  are uniform in the number of atoms.
* The constants (`a`, the polynomials) depend only on `ε` and on bounds `vz`, `vy` for the
  variances, not on the covariance functions; `F` depends on the covariance functions only through
  the Gaussian integrals.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped NNReal Matrix

namespace SpinGlasses

section Clamp

/-- The truncated logarithm `log (max (min x e^a) e^{-a})` moves `log x` by at most
`e^{-a} (x + x⁻¹)`. -/
theorem abs_log_sub_log_clamp_le {a x : ℝ} (ha : 0 ≤ a) (hx : 0 < x) :
    |Real.log x - Real.log (max (min x (Real.exp a)) (Real.exp (-a)))| ≤
      Real.exp (-a) * (x + x⁻¹) := by
  have hle : Real.exp (-a) ≤ Real.exp a := Real.exp_le_exp.2 (by linarith)
  have hxi : 0 < x⁻¹ := inv_pos.2 hx
  have key : ∀ u : ℝ, u ≤ Real.exp u := fun u => by linarith [Real.add_one_le_exp u]
  rcases le_total (Real.exp a) x with h1 | h1
  · rw [min_eq_right h1, max_eq_left hle, Real.log_exp, abs_of_nonneg
      (by rw [sub_nonneg]; exact (Real.le_log_iff_exp_le hx).2 h1)]
    have := key (Real.log x - a)
    rw [Real.exp_sub, Real.exp_log hx, div_eq_mul_inv, ← Real.exp_neg] at this
    nlinarith [Real.exp_pos (-a)]
  rcases le_total x (Real.exp (-a)) with h2 | h2
  · rw [min_eq_left (h2.trans hle), max_eq_right h2, Real.log_exp,
      abs_of_nonpos (by rw [sub_nonpos]; linarith [(Real.log_le_iff_le_exp hx).2 h2])]
    have := key (-Real.log x - a)
    rw [Real.exp_sub, Real.exp_neg, Real.exp_log hx, div_eq_mul_inv, ← Real.exp_neg] at this
    nlinarith [Real.exp_pos (-a)]
  · rw [min_eq_left h1, max_eq_left h2, sub_self, abs_zero]
    positivity

/-- The map `x ↦ max (min x e^a) e^{-a}` is `1`-Lipschitz. -/
theorem abs_clamp_sub_clamp_le (c₁ c₂ x y : ℝ) :
    |max (min x c₁) c₂ - max (min y c₁) c₂| ≤ |x - y| := by
  refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
  refine max_le ((abs_min_sub_min_le_max _ _ _ _).trans ?_) (by simp)
  simp

/-- `log` is `e^a`-Lipschitz on `[e^{-a}, ∞)`. -/
theorem abs_log_sub_log_le {a s t : ℝ} (hs : Real.exp (-a) ≤ s) (ht : Real.exp (-a) ≤ t) :
    |Real.log s - Real.log t| ≤ Real.exp a * |s - t| := by
  have hs0 : 0 < s := (Real.exp_pos _).trans_le hs
  have ht0 : 0 < t := (Real.exp_pos _).trans_le ht
  have hinv : ∀ r, Real.exp (-a) ≤ r → r⁻¹ ≤ Real.exp a := fun r hr => by
    rw [inv_le_comm₀ ((Real.exp_pos _).trans_le hr) (Real.exp_pos _), ← Real.exp_neg]
    exact hr
  have h1 : Real.log s - Real.log t ≤ Real.exp a * |s - t| := by
    rw [← Real.log_div hs0.ne' ht0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hs0 ht0)
    calc _ ≤ s / t - 1 := this
      _ = (s - t) * t⁻¹ := by field_simp
      _ ≤ |s - t| * Real.exp a :=
        mul_le_mul (le_abs_self _) (hinv t ht) (inv_nonneg.2 ht0.le) (abs_nonneg _)
      _ = _ := mul_comm _ _
  have h2 : Real.log t - Real.log s ≤ Real.exp a * |s - t| := by
    rw [← Real.log_div ht0.ne' hs0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos ht0 hs0)
    calc _ ≤ t / s - 1 := this
      _ = (t - s) * s⁻¹ := by field_simp
      _ ≤ |s - t| * Real.exp a :=
        mul_le_mul (by rw [abs_sub_comm]; exact le_abs_self _) (hinv s hs)
          (inv_nonneg.2 hs0.le) (abs_nonneg _)
      _ = _ := mul_comm _ _
  rw [abs_le]
  constructor <;> linarith

/-- The truncated logarithm is `e^a`-Lipschitz on `[0, ∞)` in the argument. -/
theorem abs_log_clamp_sub_le (a x y : ℝ) :
    |Real.log (max (min x (Real.exp a)) (Real.exp (-a))) -
        Real.log (max (min y (Real.exp a)) (Real.exp (-a)))| ≤ Real.exp a * |x - y| :=
  (abs_log_sub_log_le (le_max_right _ _) (le_max_right _ _)).trans
    (mul_le_mul_of_nonneg_left (abs_clamp_sub_clamp_le _ _ _ _) (Real.exp_pos _).le)

/-- `|log x| ≤ x + x⁻¹` for `x > 0`. -/
theorem abs_log_le_add_inv {x : ℝ} (hx : 0 < x) : |Real.log x| ≤ x + x⁻¹ := by
  have h1 := Real.log_le_sub_one_of_pos hx
  have h2 := Real.log_le_sub_one_of_pos (inv_pos.2 hx)
  rw [Real.log_inv] at h2
  have := inv_pos.2 hx
  rw [abs_le]
  constructor <;> linarith

/-- A function with `φ x ≤ A e^{|x|}` moves by at most `2 A e^{-2a} e^{3|x|}` when its argument
is clamped to `[-a, a]`. -/
theorem abs_sub_comp_clamp_le {φ : ℝ → ℝ} {A : ℝ} (hφ : ∀ x, 0 < φ x)
    (hA : ∀ x, φ x ≤ A * Real.exp |x|) {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    |φ x - φ (max (-a) (min x a))| ≤ 2 * A * Real.exp (-(2 * a)) * Real.exp (3 * |x|) := by
  have hA0 : 0 < A := by simpa using (hφ 0).trans_le (hA 0)
  rcases le_total |x| a with h | h
  · obtain ⟨h1, h2⟩ := abs_le.1 h
    rw [min_eq_left h2, max_eq_right h1, sub_self, abs_zero]
    positivity
  · have hc : |max (-a) (min x a)| ≤ a := by
      rw [abs_le]
      exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
    have hq := (hA (max (-a) (min x a))).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hc.trans h)) hA0.le)
    have hp := hA x
    have hbound : A * Real.exp |x| ≤ A * (Real.exp (-(2 * a)) * Real.exp (3 * |x|)) := by
      refine mul_le_mul_of_nonneg_left ?_ hA0.le
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    rw [abs_le]
    constructor <;> nlinarith [hφ x, hφ (max (-a) (min x a)), Real.exp_pos (-(2 * a)),
      Real.exp_pos (3 * |x|), mul_pos (Real.exp_pos (-(2 * a))) (Real.exp_pos (3 * |x|))]

end Clamp

section Gibbs

variable {ι : Type*} [Fintype ι] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {w : ι → ℝ} {g : ι → Ω → ℝ} {v : ℝ≥0}

/-- A weighted average of `exp (s |g i|)` over sub-Gaussian `g i` is integrable with expectation at
most `2 exp (v s² / 2)`, whatever the number of terms. -/
theorem integral_sum_mul_exp_abs_le (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hm : ∀ i, Measurable (g i)) (hsub : ∀ i, HasSubgaussianMGF (g i) v P) (s : ℝ) :
    Integrable (fun ω => ∑ i, w i * Real.exp (s * |g i ω|)) P ∧
      ∫ ω, ∑ i, w i * Real.exp (s * |g i ω|) ∂P ≤ 2 * Real.exp (v * s ^ 2 / 2) := by
  have hi : ∀ i, Integrable (fun ω => w i * Real.exp (s * |g i ω|)) P := fun i =>
    ((hsub i).integral_exp_abs_mul_le (hm i) s).1.const_mul _
  refine ⟨integrable_finsetSum _ fun i _ => hi i, ?_⟩
  rw [integral_finsetSum _ fun i _ => hi i]
  calc ∑ i, ∫ ω, w i * Real.exp (s * |g i ω|) ∂P
      ≤ ∑ i, w i * (2 * Real.exp (v * s ^ 2 / 2)) := Finset.sum_le_sum fun i _ => by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left ((hsub i).integral_exp_abs_mul_le (hm i) s).2 (hw0 i)
    _ = 2 * Real.exp (v * s ^ 2 / 2) := by rw [← Finset.sum_mul, hw1, one_mul]

/-- **Domination by a Gibbs average of `exp (s |g i|)`.** -/
theorem integrable_integral_le_of_le_sum_exp_abs (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hm : ∀ i, Measurable (g i)) (hsub : ∀ i, HasSubgaussianMGF (g i) v P) {F : Ω → ℝ}
    (hF : Measurable F) (hF0 : ∀ ω, 0 ≤ F ω) {K : ℝ} (hK : 0 ≤ K) (s : ℝ)
    (hFle : ∀ ω, F ω ≤ K * ∑ i, w i * Real.exp (s * |g i ω|)) :
    Integrable F P ∧ ∫ ω, F ω ∂P ≤ 2 * K * Real.exp (v * s ^ 2 / 2) := by
  obtain ⟨hi, hint⟩ := integral_sum_mul_exp_abs_le hw0 hw1 hm hsub s
  refine ⟨(hi.const_mul K).mono' hF.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_),
    ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ω)]
    exact hFle ω
  · calc ∫ ω, F ω ∂P ≤ ∫ ω, K * ∑ i, w i * Real.exp (s * |g i ω|) ∂P :=
          integral_mono ((hi.const_mul K).mono' hF.aestronglyMeasurable
            (Filter.Eventually.of_forall fun ω => by
              rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ω)]; exact hFle ω)) (hi.const_mul K) hFle
      _ = K * ∫ ω, ∑ i, w i * Real.exp (s * |g i ω|) ∂P := integral_const_mul _ _
      _ ≤ K * (2 * Real.exp (v * s ^ 2 / 2)) := mul_le_mul_of_nonneg_left hint hK
      _ = _ := by ring

/-- **Jensen for the inverse:** `(∑ wᵢ xᵢ)⁻¹ ≤ ∑ wᵢ xᵢ⁻¹` for a probability vector `w`, `x > 0`. -/
theorem inv_sum_mul_le (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {x : ι → ℝ}
    (hx : ∀ i, 0 < x i) : (∑ i, w i * x i)⁻¹ ≤ ∑ i, w i * (x i)⁻¹ := by
  have := (convexOn_zpow (𝕜 := ℝ) (-1)).map_sum_le (t := Finset.univ) (w := w) (p := x)
    (fun i _ => hw0 i) hw1 (fun i _ => hx i)
  simpa [smul_eq_mul] using this

/-- A probability vector has a positive sum against a positive function. -/
theorem sum_mul_pos (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {x : ι → ℝ}
    (hx : ∀ i, 0 < x i) : 0 < ∑ i, w i * x i := by
  obtain ⟨i, hi⟩ : ∃ i, 0 < w i := by
    by_contra h
    push Not at h
    have : ∑ i, w i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (h i) (hw0 i)
    linarith
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hw0 j) (hx j).le)
    ⟨i, mem_univ _, mul_pos hi (hx i)⟩

end Gibbs

section Truncation

variable {ι : Type*} [Fintype ι] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {w : ι → ℝ} {g : ι → Ω → ℝ} {v : ℝ≥0} {φ : ℝ → ℝ} {A B : ℝ}

/-- **Integrability and size of a Gibbs average of a positive function of sub-Gaussian
variables and of its inverse:** with `X = ∑ wᵢ φ (gᵢ)`, `𝔼 X ≤ 2 A e^{v/2}` and
`𝔼 X⁻¹ ≤ 2 B e^{v/2}`. -/
theorem integrable_sum_mul_comp
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hm : ∀ i, Measurable (g i))
    (hsub : ∀ i, HasSubgaussianMGF (g i) v P) (hφc : Continuous φ) (hφ : ∀ x, 0 < φ x)
    (hA : ∀ x, φ x ≤ A * Real.exp |x|) (hB : ∀ x, (φ x)⁻¹ ≤ B * Real.exp |x|) :
    (Integrable (fun ω => ∑ i, w i * φ (g i ω)) P ∧
        ∫ ω, ∑ i, w i * φ (g i ω) ∂P ≤ 2 * A * Real.exp (v * 1 ^ 2 / 2)) ∧
      (Integrable (fun ω => (∑ i, w i * φ (g i ω))⁻¹) P ∧
        ∫ ω, (∑ i, w i * φ (g i ω))⁻¹ ∂P ≤ 2 * B * Real.exp (v * 1 ^ 2 / 2)) := by
  have hA0 : 0 ≤ A := by simpa using (hφ 0).le.trans (hA 0)
  have hB0 : 0 ≤ B := by simpa using (inv_pos.2 (hφ 0)).le.trans (hB 0)
  have hXpos : ∀ ω, 0 < ∑ i, w i * φ (g i ω) := fun ω => sum_mul_pos hw0 hw1 fun i => hφ _
  have hXm : Measurable fun ω => ∑ i, w i * φ (g i ω) :=
    Finset.measurable_sum _ fun i _ => (hφc.measurable.comp (hm i)).const_mul _
  refine ⟨integrable_integral_le_of_le_sum_exp_abs hw0 hw1 hm hsub hXm
    (fun ω => (hXpos ω).le) hA0 1 fun ω => ?_,
    integrable_integral_le_of_le_sum_exp_abs hw0 hw1 hm hsub hXm.inv
    (fun ω => (inv_pos.2 (hXpos ω)).le) hB0 1 fun ω => ?_⟩
  · calc _ ≤ ∑ i, w i * (A * Real.exp (1 * |g i ω|)) := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (by simpa using hA (g i ω)) (hw0 i)
      _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  · calc _ ≤ ∑ i, w i * (φ (g i ω))⁻¹ := inv_sum_mul_le hw0 hw1 fun i => hφ _
      _ ≤ ∑ i, w i * (B * Real.exp (1 * |g i ω|)) := Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (by simpa using hB (g i ω)) (hw0 i)
      _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

/-- The logarithm of a Gibbs average of a sub-Gaussian field is integrable. -/
theorem integrable_log_sum_mul_comp
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hm : ∀ i, Measurable (g i))
    (hsub : ∀ i, HasSubgaussianMGF (g i) v P) (hφc : Continuous φ) (hφ : ∀ x, 0 < φ x)
    (hA : ∀ x, φ x ≤ A * Real.exp |x|) (hB : ∀ x, (φ x)⁻¹ ≤ B * Real.exp |x|) :
    Integrable (fun ω => Real.log (∑ i, w i * φ (g i ω))) P := by
  obtain ⟨⟨hXi, -⟩, ⟨hXii, -⟩⟩ := integrable_sum_mul_comp hw0 hw1 hm hsub hφc hφ hA hB
  exact (hXi.add hXii).mono' (Real.measurable_log.comp
    (Finset.measurable_sum _ fun i _ =>
      (hφc.measurable.comp (hm i)).const_mul _)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs] using
        abs_log_le_add_inv (sum_mul_pos hw0 hw1 fun i => hφ (g i ω)))

/-- The truncated logarithm is bounded by `a`. -/
theorem abs_log_clamp_le {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    |Real.log (max (min x (Real.exp a)) (Real.exp (-a)))| ≤ a := by
  have hle : Real.exp (-a) ≤ Real.exp a := Real.exp_le_exp.2 (by linarith)
  rw [abs_le]
  constructor
  · calc -a = Real.log (Real.exp (-a)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
  · calc _ ≤ Real.log (Real.exp a) := Real.log_le_log
          ((Real.exp_pos _).trans_le (le_max_right _ _))
          (max_le (min_le_right _ _) hle)
      _ = a := Real.log_exp _

/-- **Truncation error for a Gibbs average of a sub-Gaussian field** (the estimates behind
Panchenko Eqs. (1.65), (1.68)–(1.72)).  Let `φ > 0` be continuous with `φ x ≤ A e^{|x|}` and
`φ x⁻¹ ≤ B e^{|x|}`, and let `g i` be sub-Gaussian with parameter `v`.  Then replacing
`log ⟨φ (g)⟩` by `log` truncated to `[-a, a]` of `⟨φ (clamp g)⟩`, with `clamp` the projection to
`[-a, a]`, changes the expectation by at most `C e^{-a}`, with `C` independent of the number of
terms. -/
theorem abs_integral_log_sub_integral_log_clamp_le [IsProbabilityMeasure P]
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hm : ∀ i, Measurable (g i))
    (hsub : ∀ i, HasSubgaussianMGF (g i) v P) (hφc : Continuous φ) (hφ : ∀ x, 0 < φ x)
    (hA : ∀ x, φ x ≤ A * Real.exp |x|) (hB : ∀ x, (φ x)⁻¹ ≤ B * Real.exp |x|) {a : ℝ}
    (ha : 0 ≤ a) :
    |∫ ω, Real.log (∑ i, w i * φ (g i ω)) ∂P -
        ∫ ω, Real.log (max (min (∑ i, w i * φ (max (-a) (min (g i ω) a))) (Real.exp a))
          (Real.exp (-a))) ∂P| ≤
      ((2 * A + 2 * B) * Real.exp (v / 2) + 4 * A * Real.exp (9 * v / 2)) * Real.exp (-a) := by
  have hA0 : 0 ≤ A := by simpa using (hφ 0).le.trans (hA 0)
  have hB0 : 0 ≤ B := by simpa using (inv_pos.2 (hφ 0)).le.trans (hB 0)
  have hφm : Measurable φ := hφc.measurable
  set X : Ω → ℝ := fun ω => ∑ i, w i * φ (g i ω) with hX
  set Xa : Ω → ℝ := fun ω => ∑ i, w i * φ (max (-a) (min (g i ω) a)) with hXa
  set D : Ω → ℝ := fun ω => ∑ i, w i * |φ (g i ω) - φ (max (-a) (min (g i ω) a))| with hD
  have hXpos : ∀ ω, 0 < X ω := fun ω => sum_mul_pos hw0 hw1 fun i => hφ _
  have hXm : Measurable X :=
    Finset.measurable_sum _ fun i _ => (hφm.comp (hm i)).const_mul _
  have hXam : Measurable Xa :=
    Finset.measurable_sum _ fun i _ =>
      (hφm.comp ((measurable_const.max ((hm i).min measurable_const)))).const_mul _
  have hDm : Measurable D := Finset.measurable_sum _ fun i _ =>
    (continuous_abs.measurable.comp ((hφm.comp (hm i)).sub (hφm.comp ((measurable_const.max
      ((hm i).min measurable_const)))))).const_mul _
  -- integrability and size of `X`, `X⁻¹` and `D`
  obtain ⟨⟨hXi, hXint⟩, ⟨hXii, hXiint⟩⟩ := integrable_sum_mul_comp hw0 hw1 hm hsub hφc hφ hA hB
  obtain ⟨hDi, hDint⟩ := integrable_integral_le_of_le_sum_exp_abs hw0 hw1 hm hsub hDm
    (fun ω => Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (abs_nonneg _))
    (K := 2 * A * Real.exp (-(2 * a))) (by positivity) 3 fun ω => by
      calc D ω ≤ ∑ i, w i * (2 * A * Real.exp (-(2 * a)) * Real.exp (3 * |g i ω|)) :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
              (abs_sub_comp_clamp_le hφ hA ha _) (hw0 i)
        _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have hlogX : Integrable (fun ω => Real.log (X ω)) P :=
    integrable_log_sum_mul_comp hw0 hw1 hm hsub hφc hφ hA hB
  have hlogT :
      Integrable (fun ω => Real.log (max (min (Xa ω) (Real.exp a)) (Real.exp (-a)))) P :=
    Integrable.of_bound (C := a)
      (Real.measurable_log.comp
        ((hXam.min measurable_const).max measurable_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact abs_log_clamp_le ha _)
  have hU : Integrable (fun ω => Real.exp (-a) * (X ω + (X ω)⁻¹) + Real.exp a * D ω) P :=
    ((hXi.add hXii).const_mul _).add (hDi.const_mul _)
  have hpt : ∀ ω, ‖Real.log (X ω) -
      Real.log (max (min (Xa ω) (Real.exp a)) (Real.exp (-a)))‖ ≤
        Real.exp (-a) * (X ω + (X ω)⁻¹) + Real.exp a * D ω := fun ω => by
    have h1 := abs_log_sub_log_clamp_le ha (hXpos ω)
    have h2 := abs_log_clamp_sub_le a (X ω) (Xa ω)
    have h3 : |X ω - Xa ω| ≤ D ω := by
      simp only [hX, hXa, hD, ← Finset.sum_sub_distrib, ← mul_sub]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_of_nonneg (hw0 i)]
    rw [Real.norm_eq_abs]
    calc _ = |(Real.log (X ω) - Real.log (max (min (X ω) (Real.exp a)) (Real.exp (-a)))) +
          (Real.log (max (min (X ω) (Real.exp a)) (Real.exp (-a))) -
            Real.log (max (min (Xa ω) (Real.exp a)) (Real.exp (-a))))| := by ring_nf
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1
          (h2.trans (mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le)))
  rw [← integral_sub hlogX hlogT, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hU (Filter.Eventually.of_forall hpt)).trans ?_
  have hXX : Integrable (fun ω => X ω + (X ω)⁻¹) P := hXi.add hXii
  have hI1 : Integrable (fun ω => Real.exp (-a) * (X ω + (X ω)⁻¹)) P := hXX.const_mul _
  have hI2 : Integrable (fun ω => Real.exp a * D ω) P := hDi.const_mul _
  rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul,
    show ∫ ω, (X ω + (X ω)⁻¹) ∂P = (∫ ω, X ω ∂P) + ∫ ω, (X ω)⁻¹ ∂P from integral_add hXi hXii]
  have e1 : (v : ℝ) * 1 ^ 2 / 2 = v / 2 := by ring
  have e3 : (v : ℝ) * 3 ^ 2 / 2 = 9 * v / 2 := by ring
  rw [e1] at hXint hXiint
  rw [e3] at hDint
  have hexp : Real.exp a * Real.exp (-(2 * a)) = Real.exp (-a) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 := mul_le_mul_of_nonneg_left (add_le_add hXint hXiint) (Real.exp_pos (-a)).le
  have h2 := mul_le_mul_of_nonneg_left hDint (Real.exp_pos a).le
  calc _ ≤ Real.exp (-a) * (2 * A * Real.exp (v / 2) + 2 * B * Real.exp (v / 2)) +
        Real.exp a * (2 * (2 * A * Real.exp (-(2 * a))) * Real.exp (9 * v / 2)) := add_le_add h1 h2
    _ = _ := by rw [← hexp]; ring

universe u u'

/-- **Polynomial approximation of the Gibbs free energy of a sub-Gaussian field**
(Panchenko Eqs. (1.65)–(1.66)).  Given `ε > 0` there are a truncation level `a ≥ 0` and a
polynomial `p`, depending only on `ε`, `v`, `φ`, `A`, `B`, such that for every finite family of
sub-Gaussian variables `g i` (parameter `v`) and every probability vector `w`,
`|𝔼 log ∑ wᵢ φ (gᵢ) - 𝔼 p (∑ wᵢ φ (clamp_a gᵢ))| ≤ ε`. -/
theorem exists_polynomial_integral_log_approx (v : ℝ≥0) (hφc : Continuous φ)
    (hφ : ∀ x, 0 < φ x) (hA : ∀ x, φ x ≤ A * Real.exp |x|)
    (hB : ∀ x, (φ x)⁻¹ ≤ B * Real.exp |x|) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ p : Polynomial ℝ,
      ∀ (ι : Type u) [Fintype ι] (Ω : Type u') [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (w : ι → ℝ) (g : ι → Ω → ℝ), (∀ i, 0 ≤ w i) → ∑ i, w i = 1 →
        (∀ i, Measurable (g i)) → (∀ i, HasSubgaussianMGF (g i) v P) →
        |∫ ω, Real.log (∑ i, w i * φ (g i ω)) ∂P -
          ∫ ω, p.eval (∑ i, w i * φ (max (-a) (min (g i ω) a))) ∂P| ≤ ε := by
  have hA0 : 0 ≤ A := by simpa using (hφ 0).le.trans (hA 0)
  set C : ℝ := (2 * A + 2 * B) * Real.exp (v / 2) + 4 * A * Real.exp (9 * v / 2) with hC
  have hC0 : 0 ≤ C := by
    have hB0 : 0 ≤ B := by simpa using (inv_pos.2 (hφ 0)).le.trans (hB 0)
    positivity
  set a : ℝ := max 0 (Real.log (2 * (C + 1) / ε)) with ha
  have ha0 : 0 ≤ a := le_max_left _ _
  have hCa : C * Real.exp (-a) ≤ ε / 2 := by
    have h1 : Real.exp (-a) ≤ ε / (2 * (C + 1)) := by
      have : Real.exp (-a) ≤ Real.exp (-Real.log (2 * (C + 1) / ε)) :=
        Real.exp_le_exp.2 (neg_le_neg (le_max_right _ _))
      rwa [Real.exp_neg (Real.log _), Real.exp_log (by positivity), inv_div] at this
    calc C * Real.exp (-a) ≤ (C + 1) * (ε / (2 * (C + 1))) :=
          mul_le_mul (by linarith) h1 (Real.exp_pos _).le (by linarith)
      _ = ε / 2 := by field_simp
  have hcont : ContinuousOn (fun x => Real.log (max (min x (Real.exp a)) (Real.exp (-a))))
      (Set.Icc 0 (A * Real.exp a)) :=
    ((continuous_id.min continuous_const).max continuous_const).continuousOn.log fun x _ =>
      (Real.exp_pos _).trans_le (le_max_right _ _) |>.ne'
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 (A * Real.exp a) _ hcont
    (ε / 2) (half_pos hε)
  refine ⟨a, ha0, p, fun ι _ Ω _ P _ w g hw0 hw1 hm hsub => ?_⟩
  have hφm : Measurable φ := hφc.measurable
  set Xa : Ω → ℝ := fun ω => ∑ i, w i * φ (max (-a) (min (g i ω) a)) with hXa
  have hXam : Measurable Xa :=
    Finset.measurable_sum _ fun i _ =>
      (hφm.comp ((measurable_const.max ((hm i).min measurable_const)))).const_mul _
  have hmem : ∀ ω, Xa ω ∈ Set.Icc 0 (A * Real.exp a) := fun ω => by
    refine ⟨Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (hφ _).le, ?_⟩
    calc Xa ω ≤ ∑ i, w i * (A * Real.exp a) := Finset.sum_le_sum fun i _ => by
          refine mul_le_mul_of_nonneg_left ((hA _).trans (mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.2 ?_) hA0)) (hw0 i)
          rw [abs_le]
          exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
      _ = A * Real.exp a := by rw [← Finset.sum_mul, hw1, one_mul]
  set ℓ : ℝ → ℝ := fun x => Real.log (max (min x (Real.exp a)) (Real.exp (-a))) with hℓ
  have hℓm : Measurable (fun ω => ℓ (Xa ω)) :=
    Real.measurable_log.comp ((hXam.min measurable_const).max measurable_const)
  have hℓi : Integrable (fun ω => ℓ (Xa ω)) P :=
    Integrable.of_bound (C := a) hℓm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]; exact abs_log_clamp_le ha0 _)
  have hpi : Integrable (fun ω => p.eval (Xa ω)) P :=
    Integrable.of_bound (C := a + ε / 2) (p.continuous.measurable.comp hXam).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        have h1 := hp _ (hmem ω)
        have h2 := abs_log_clamp_le ha0 (Xa ω)
        rw [Real.norm_eq_abs]
        calc |p.eval (Xa ω)| = |(p.eval (Xa ω) - ℓ (Xa ω)) + ℓ (Xa ω)| := by ring_nf
          _ ≤ |p.eval (Xa ω) - ℓ (Xa ω)| + |ℓ (Xa ω)| := abs_add_le _ _
          _ ≤ a + ε / 2 := by linarith)
  have h2 : |∫ ω, ℓ (Xa ω) ∂P - ∫ ω, p.eval (Xa ω) ∂P| ≤ ε / 2 := by
    rw [← integral_sub hℓi hpi, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := ε / 2)
      (Filter.Eventually.of_forall fun ω => ?_)).trans (by simp)
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact (hp _ (hmem ω)).le
  have h1 := abs_integral_log_sub_integral_log_clamp_le hw0 hw1 hm hsub hφc hφ hA hB ha0
  exact (abs_sub_le _ (∫ ω, ℓ (Xa ω) ∂P) _).trans (by linarith)

end Truncation

section Moments

variable {ι : Type*} [Fintype ι] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {w : ι → ℝ} {g : ι → Ω → ℝ} {ψ : ℝ → ℝ}

/-- **Replica expansion (Panchenko Eq. (1.67)).**  For a centered Gaussian family `g`, a bounded
measurable `ψ` and a probability vector `w`,
`𝔼 (∑ wᵢ ψ (gᵢ))^k = ∑_{j : Fin k → ι} (∏ₗ w_{jₗ}) ∫ ∏ₗ ψ (xₗ) d𝒩(0, (𝔼 g_{jₗ} g_{jₗ'})ₗₗ')`:
the `k`-th moment of a Gibbs average is the Gibbs average of a Gaussian integral that depends only
on the covariance matrix of `k` replicas. -/
theorem integral_pow_sum_mul_comp_eq [IsProbabilityMeasure P]
    (hg : HasGaussianLaw (fun ω i => g i ω) P) (h0 : ∀ i, ∫ ω, g i ω ∂P = 0)
    (hm : ∀ i, Measurable (g i)) (hψm : Measurable ψ) {M : ℝ} (hψ : ∀ x, |ψ x| ≤ M) (k : ℕ) :
    ∫ ω, (∑ i, w i * ψ (g i ω)) ^ k ∂P =
      ∑ j : Fin k → ι, (∏ l, w (j l)) *
        ∫ x : EuclideanSpace ℝ (Fin k), ∏ l, ψ (x.ofLp l) ∂(multivariateGaussian 0
          (Matrix.of fun l l' => ∫ ω, g (j l) ω * g (j l') ω ∂P)) := by
  classical
  have hM : 0 ≤ M := (abs_nonneg _).trans (hψ 0)
  have hprod : ∀ y : Fin k → ℝ, |∏ l, ψ (y l)| ≤ M ^ k := fun y => by
    rw [Finset.abs_prod]
    calc ∏ l, |ψ (y l)| ≤ ∏ _l : Fin k, M := by
          gcongr with l
          exact hψ _
      _ = M ^ k := by simp
  simp_rw [Fintype.sum_pow, Finset.prod_mul_distrib]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul,
      integral_comp_comp_eq_integral_multivariateGaussian hg h0 j (f := fun y => ∏ l, ψ (y l))
        (Finset.measurable_prod _ fun l _ => hψm.comp (measurable_pi_apply l))]
  · intro j _
    refine Integrable.of_bound (C := (∏ l, |w (j l)|) * M ^ k) ?_
      (Filter.Eventually.of_forall fun ω => ?_)
    · exact (measurable_const.mul (Finset.measurable_prod _ fun l _ =>
        hψm.comp (hm (j l)))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, Finset.abs_prod]
      exact mul_le_mul_of_nonneg_left (hprod (fun l => g (j l) ω))
        (Finset.prod_nonneg fun l _ => abs_nonneg _)

/-- **Moment expansion of a polynomial of a Gibbs average.**  Summing `integral_pow_sum_mul_comp_eq`
against the coefficients of `p`. -/
theorem integral_eval_sum_mul_comp_eq [IsProbabilityMeasure P] (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hg : HasGaussianLaw (fun ω i => g i ω) P)
    (h0 : ∀ i, ∫ ω, g i ω ∂P = 0) (hm : ∀ i, Measurable (g i)) (hψm : Measurable ψ) {M : ℝ}
    (hψ : ∀ x, |ψ x| ≤ M) (p : Polynomial ℝ) :
    ∫ ω, p.eval (∑ i, w i * ψ (g i ω)) ∂P =
      ∑ k ∈ range (p.natDegree + 1), p.coeff k * ∑ j : Fin k → ι, (∏ l, w (j l)) *
        ∫ x : EuclideanSpace ℝ (Fin k), ∏ l, ψ (x.ofLp l) ∂(multivariateGaussian 0
          (Matrix.of fun l l' => ∫ ω, g (j l) ω * g (j l') ω ∂P)) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hψ 0)
  have hX : ∀ ω, |∑ i, w i * ψ (g i ω)| ≤ M := fun ω => by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |w i * ψ (g i ω)| ≤ ∑ i, w i * M := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, abs_of_nonneg (hw0 i)]
          exact mul_le_mul_of_nonneg_left (hψ _) (hw0 i)
      _ = M := by rw [← Finset.sum_mul, hw1, one_mul]
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_pow_sum_mul_comp_eq hg h0 hm hψm hψ k]
  · intro k _
    refine Integrable.const_mul (Integrable.of_bound (C := M ^ k) ?_
      (Filter.Eventually.of_forall fun ω => ?_)) _
    · exact ((Finset.measurable_sum _ fun i _ => (hψm.comp (hm i)).const_mul _).pow_const
        k).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hX ω) k

end Moments

section Jensen

variable {ι : Type*} [Fintype ι] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {w : ι → ℝ} {g : ι → Ω → ℝ} {v : ℝ≥0}

/-- **Jensen's inequality for the logarithm**, in the elementary form `log x ≤ x / c - 1 + log c`:
`𝔼 log X ≤ log 𝔼 X` for a positive integrable `X` with integrable logarithm. -/
theorem integral_log_le_log_integral [IsProbabilityMeasure P] {X : Ω → ℝ} (hpos : ∀ ω, 0 < X ω)
    (hX : Integrable X P) (hlog : Integrable (fun ω => Real.log (X ω)) P) :
    ∫ ω, Real.log (X ω) ∂P ≤ Real.log (∫ ω, X ω ∂P) := by
  have hc : 0 < ∫ ω, X ω ∂P := by
    refine (integral_pos_iff_support_of_nonneg (fun ω => (hpos ω).le) hX).2 ?_
    rw [Set.eq_univ_of_forall (s := Function.support X) fun ω => (hpos ω).ne']
    simp
  set c := ∫ ω, X ω ∂P with hcdef
  have hpt : ∀ ω, Real.log (X ω) ≤ X ω / c - 1 + Real.log c := fun ω => by
    have := Real.log_le_sub_one_of_pos (div_pos (hpos ω) hc)
    rw [Real.log_div (hpos ω).ne' hc.ne'] at this
    linarith
  have h1 : Integrable (fun ω => X ω / c - 1) P := (hX.div_const c).sub (integrable_const _)
  have hi : Integrable (fun ω => X ω / c - 1 + Real.log c) P := h1.add (integrable_const _)
  calc ∫ ω, Real.log (X ω) ∂P ≤ ∫ ω, (X ω / c - 1 + Real.log c) ∂P := integral_mono hlog hi hpt
    _ = Real.log c := by
      rw [integral_add h1 (integrable_const _), integral_sub (hX.div_const c) (integrable_const _),
        integral_div]
      have : (∫ ω, X ω ∂P) / c = 1 := by rw [← hcdef]; exact div_self hc.ne'
      simp [this]

theorem exp_le_exp_abs_mul (x : ℝ) : Real.exp x ≤ 1 * Real.exp |x| := by
  rw [one_mul]; exact Real.exp_le_exp.2 (le_abs_self x)

theorem inv_exp_le_exp_abs_mul (x : ℝ) : (Real.exp x)⁻¹ ≤ 1 * Real.exp |x| := by
  rw [one_mul, ← Real.exp_neg]; exact Real.exp_le_exp.2 (neg_le_abs x)

theorem two_cosh_le_exp_abs_mul (x : ℝ) : 2 * Real.cosh x ≤ 2 * Real.exp |x| := by
  rw [Real.cosh_eq]
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
    nlinarith [Real.exp_pos (-x), Real.exp_le_exp.2 (show -x ≤ x by linarith)]
  · rw [abs_of_nonpos h]
    nlinarith [Real.exp_pos x, Real.exp_le_exp.2 (show x ≤ -x by linarith)]

theorem inv_two_cosh_le_exp_abs_mul (x : ℝ) : (2 * Real.cosh x)⁻¹ ≤ 1 * Real.exp |x| := by
  have h1 : 1 ≤ Real.cosh x := Real.one_le_cosh x
  have h2 : 1 ≤ Real.exp |x| := Real.one_le_exp (abs_nonneg x)
  rw [one_mul]
  calc (2 * Real.cosh x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    _ ≤ _ := h2

/-- The Gibbs average of expectations is bounded by the common bound of the expectations. -/
theorem integral_sum_mul_le (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) {f : ι → Ω → ℝ}
    (hf : ∀ i, Integrable (f i) P) {K : ℝ} (hK : ∀ i, ∫ ω, f i ω ∂P ≤ K) :
    ∫ ω, ∑ i, w i * f i ω ∂P ≤ K := by
  rw [integral_finsetSum _ fun i _ => (hf i).const_mul _]
  calc ∑ i, ∫ ω, w i * f i ω ∂P ≤ ∑ i, w i * K := Finset.sum_le_sum fun i _ => by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hK i) (hw0 i)
    _ = K := by rw [← Finset.sum_mul, hw1, one_mul]

/-- **`log 2 ≤ 𝔼 log ⟨2 cosh g⟩`.** -/
theorem log_two_le_integral_log_sum_mul_two_cosh [IsProbabilityMeasure P]
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hm : ∀ i, Measurable (g i))
    (hsub : ∀ i, HasSubgaussianMGF (g i) v P) :
    Real.log 2 ≤ ∫ ω, Real.log (∑ i, w i * (2 * Real.cosh (g i ω))) ∂P := by
  have hlog := integrable_log_sum_mul_comp (φ := fun x => 2 * Real.cosh x) (A := 2) (B := 1)
    hw0 hw1 hm hsub (by fun_prop) (fun x => by positivity) (fun x => two_cosh_le_exp_abs_mul x)
    (fun x => inv_two_cosh_le_exp_abs_mul x)
  have := integral_mono (integrable_const (Real.log 2)) hlog fun ω => by
    refine Real.log_le_log (by norm_num) ?_
    calc (2 : ℝ) = ∑ i, w i * 2 := by rw [← Finset.sum_mul, hw1, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (by nlinarith [Real.one_le_cosh (g i ω)]) (hw0 i)
  simpa using this

/-- **`𝔼 log ⟨2 cosh g⟩ ≤ log 2 + v / 2`** for sub-Gaussian `g i` with parameter `v`, by Jensen. -/
theorem integral_log_sum_mul_two_cosh_le [IsProbabilityMeasure P]
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hm : ∀ i, Measurable (g i))
    (hsub : ∀ i, HasSubgaussianMGF (g i) v P) :
    ∫ ω, Real.log (∑ i, w i * (2 * Real.cosh (g i ω))) ∂P ≤ Real.log 2 + v / 2 := by
  have hlog := integrable_log_sum_mul_comp (φ := fun x => 2 * Real.cosh x) (A := 2) (B := 1)
    hw0 hw1 hm hsub (by fun_prop) (fun x => by positivity) (fun x => two_cosh_le_exp_abs_mul x)
    (fun x => inv_two_cosh_le_exp_abs_mul x)
  have hpos : ∀ ω, 0 < ∑ i, w i * (2 * Real.cosh (g i ω)) := fun ω =>
    sum_mul_pos hw0 hw1 fun i => by positivity
  have hint : Integrable (fun ω => ∑ i, w i * (2 * Real.cosh (g i ω))) P :=
    integrable_finsetSum _ fun i _ => ((hsub i).integrable_two_cosh).const_mul _
  refine (integral_log_le_log_integral hpos hint hlog).trans ?_
  have hle := integral_sum_mul_le hw0 hw1 (fun i => (hsub i).integrable_two_cosh)
    fun i => (hsub i).integral_two_cosh_le
  calc _ ≤ Real.log (2 * Real.exp (v / 2)) := Real.log_le_log
        (integral_pos_iff_support_of_nonneg (fun ω => (hpos ω).le) hint |>.2 (by
          rw [Set.eq_univ_of_forall (s := Function.support _) fun ω => (hpos ω).ne']
          simp)) hle
    _ = _ := by rw [Real.log_mul two_ne_zero (Real.exp_pos _).ne', Real.log_exp]

/-- **`0 ≤ 𝔼 log ⟨exp g⟩`** for centered `g i`, by Jensen: `log ⟨exp g⟩ ≥ ⟨g⟩`. -/
theorem zero_le_integral_log_sum_mul_exp
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hm : ∀ i, Measurable (g i))
    (hsub : ∀ i, HasSubgaussianMGF (g i) v P) (h0 : ∀ i, ∫ ω, g i ω ∂P = 0) :
    0 ≤ ∫ ω, Real.log (∑ i, w i * Real.exp (g i ω)) ∂P := by
  have hlog := integrable_log_sum_mul_comp (φ := Real.exp) (A := 1) (B := 1)
    hw0 hw1 hm hsub Real.continuous_exp Real.exp_pos exp_le_exp_abs_mul inv_exp_le_exp_abs_mul
  have hgi : ∀ i, Integrable (g i) P := fun i => (hsub i).integrable_of_measurable (hm i)
  have hlin : Integrable (fun ω => ∑ i, w i * g i ω) P :=
    integrable_finsetSum _ fun i _ => (hgi i).const_mul _
  have hmono := integral_mono hlin hlog fun ω => by
    have h := convexOn_exp.map_sum_le (t := Finset.univ) (w := w) (p := fun i => g i ω)
      (fun i _ => hw0 i) hw1 (fun i _ => Set.mem_univ _)
    simp only [smul_eq_mul] at h
    calc ∑ i, w i * g i ω = Real.log (Real.exp (∑ i, w i * g i ω)) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) h
  rw [integral_finsetSum _ fun i _ => (hgi i).const_mul _] at hmono
  simpa [integral_const_mul, h0] using hmono

/-- **`𝔼 log ⟨exp g⟩ ≤ v / 2`** for sub-Gaussian `g i` with parameter `v`, by Jensen. -/
theorem integral_log_sum_mul_exp_le [IsProbabilityMeasure P]
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hm : ∀ i, Measurable (g i))
    (hsub : ∀ i, HasSubgaussianMGF (g i) v P) :
    ∫ ω, Real.log (∑ i, w i * Real.exp (g i ω)) ∂P ≤ v / 2 := by
  have hlog := integrable_log_sum_mul_comp (φ := Real.exp) (A := 1) (B := 1)
    hw0 hw1 hm hsub Real.continuous_exp Real.exp_pos exp_le_exp_abs_mul inv_exp_le_exp_abs_mul
  have hpos : ∀ ω, 0 < ∑ i, w i * Real.exp (g i ω) := fun ω =>
    sum_mul_pos hw0 hw1 fun i => Real.exp_pos _
  have hint : Integrable (fun ω => ∑ i, w i * Real.exp (g i ω)) P :=
    integrable_finsetSum _ fun i _ => ((hsub i).integrable_exp_mul 1 |>.congr
      (Filter.Eventually.of_forall fun ω => by simp)).const_mul _
  refine (integral_log_le_log_integral hpos hint hlog).trans ?_
  have hle := integral_sum_mul_le hw0 hw1 (f := fun i ω => Real.exp (g i ω))
    (fun i => (hsub i).integrable_exp_mul 1 |>.congr (Filter.Eventually.of_forall fun ω => by simp))
    fun i => (hsub i).integral_exp_le
  calc _ ≤ Real.log (Real.exp (v / 2)) := Real.log_le_log
        (integral_pos_iff_support_of_nonneg (fun ω => (hpos ω).le) hint |>.2 (by
          rw [Set.eq_univ_of_forall (s := Function.support _) fun ω => (hpos ω).ne']
          simp)) hle
    _ = _ := Real.log_exp _


theorem abs_clamp_le {a : ℝ} (ha : 0 ≤ a) (x : ℝ) : |max (-a) (min x a)| ≤ a := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem abs_two_cosh_clamp_le {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    |2 * Real.cosh (max (-a) (min x a))| ≤ 2 * Real.exp a := by
  rw [abs_of_pos (by positivity)]
  exact (two_cosh_le_exp_abs_mul _).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (abs_clamp_le ha x)) two_pos.le)

theorem abs_exp_clamp_le {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    |Real.exp (max (-a) (min x a))| ≤ Real.exp a := by
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 ((le_abs_self _).trans (abs_clamp_le ha x))

end Jensen

section Marginal

variable {ι : Type*} [Fintype ι] {w : ι → ℝ}

/-- **Marginalization of i.i.d. replicas:** under the product weight `∏ₗ w_{jₗ}` on `m` replicas, a
function of the first `k ≤ m` replicas has the same average as under the product weight on `k`
replicas. -/
theorem sum_prod_mul_comp_castLE (hw1 : ∑ i, w i = 1) {k m : ℕ} (hkm : k ≤ m)
    (h : (Fin k → ι) → ℝ) :
    ∑ j : Fin m → ι, (∏ l, w (j l)) * h (fun l => j (Fin.castLE hkm l)) =
      ∑ j : Fin k → ι, (∏ l, w (j l)) * h j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hkm
  rw [← (Fin.appendEquiv k n).sum_comp, Fintype.sum_prod_type]
  have hb : ∑ b : Fin n → ι, ∏ l, w (b l) = 1 := by
    rw [← Fintype.sum_pow, hw1, one_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  calc ∑ b : Fin n → ι, (∏ l, w ((Fin.appendEquiv k n) (a, b) l)) *
        h (fun l => (Fin.appendEquiv k n) (a, b) (Fin.castLE (Nat.le_add_right k n) l)) =
      ∑ b : Fin n → ι, (∏ l, w (a l)) * h a * ∏ l, w (b l) := Finset.sum_congr rfl fun b _ => by
        rw [Fin.prod_univ_add]
        have e1 : ∀ l : Fin k, (Fin.appendEquiv k n) (a, b) (Fin.castAdd n l) = a l := fun l => by
          simp [Fin.appendEquiv]
        have e2 : ∀ l : Fin n, (Fin.appendEquiv k n) (a, b) (Fin.natAdd k l) = b l := fun l => by
          simp [Fin.appendEquiv]
        simp only [e1, e2]
        rw [show (fun l : Fin k => (Fin.appendEquiv k n) (a, b)
          (Fin.castLE (Nat.le_add_right k n) l)) = a from funext e1]
        ring
    _ = (∏ l, w (a l)) * h a := by rw [← Finset.mul_sum, hb, mul_one]

theorem sum_mul_sum_comm {J K : Type*} [Fintype J] [Fintype K] (c : J → ℝ) (a : K → ℝ)
    (Z : K → J → ℝ) :
    ∑ j, c j * ∑ k, a k * Z k j = ∑ k, a k * ∑ j, c j * Z k j := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

end Marginal

section Approx

universe u u'

variable {φ : ℝ → ℝ} {A B : ℝ}

/-- **Gram-matrix approximation of a Gibbs free energy, one Gaussian family.**  Let `φ > 0` be
continuous with `φ x ≤ A e^{|x|}` and `(φ x)⁻¹ ≤ B e^{|x|}`.  For every `ε > 0` and `v` there are a
truncation level `a ≥ 0` and a polynomial `p` such that, for every finite centered Gaussian family
`g` with `𝔼 gᵢ² ≤ v` and every probability vector `w`,
`|𝔼 log ∑ wᵢ φ (gᵢ) - ∑_{k ≤ deg p} p_k ∑_{j : Fin k → ι} (∏ₗ w_{jₗ})
 F_k((𝔼 g_{jₗ} g_{jₗ'})ₗₗ')| ≤ ε`
with `F_k(S) = ∫ ∏ₗ φ (clamp_a xₗ) d𝒩(0, S)`.  Only the covariance matrices of at most `deg p`
replicas enter (Panchenko Eqs. (1.64)–(1.67)). -/
theorem exists_gram_approx (v : ℝ≥0) (hφc : Continuous φ) (hφ : ∀ x, 0 < φ x)
    (hA : ∀ x, φ x ≤ A * Real.exp |x|) (hB : ∀ x, (φ x)⁻¹ ≤ B * Real.exp |x|) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ a : ℝ, 0 ≤ a ∧ ∃ p : Polynomial ℝ,
      ∀ (ι : Type u) [Fintype ι] (Ω : Type u') [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (w : ι → ℝ) (g : ι → Ω → ℝ), (∀ i, 0 ≤ w i) → ∑ i, w i = 1 →
        (∀ i, Measurable (g i)) → HasGaussianLaw (fun ω i => g i ω) P →
        (∀ i, ∫ ω, g i ω ∂P = 0) → (∀ i, ∫ ω, g i ω ^ 2 ∂P ≤ v) →
        |∫ ω, Real.log (∑ i, w i * φ (g i ω)) ∂P -
          ∑ k ∈ range (p.natDegree + 1), p.coeff k * ∑ j : Fin k → ι, (∏ l, w (j l)) *
            ∫ x : EuclideanSpace ℝ (Fin k), ∏ l, φ (max (-a) (min (x.ofLp l) a)) ∂(
              multivariateGaussian 0
                (Matrix.of fun l l' => ∫ ω, g (j l) ω * g (j l') ω ∂P))| ≤ ε := by
  have hA0 : 0 ≤ A := by simpa using (hφ 0).le.trans (hA 0)
  obtain ⟨a, ha, p, hp⟩ := exists_polynomial_integral_log_approx v hφc hφ hA hB hε
  refine ⟨a, ha, p, fun ι _ Ω _ P _ w g hw0 hw1 hm hg h0 hv => ?_⟩
  have hsub : ∀ i, HasSubgaussianMGF (g i) v P := fun i => by
    simpa using (hg.eval i).hasSubgaussianMGF_of_integral_sq_le (h0 i) (hv i)
  have hψm : Measurable fun x : ℝ => φ (max (-a) (min x a)) :=
    hφc.measurable.comp (measurable_const.max (measurable_id.min measurable_const))
  have hψ : ∀ x : ℝ, |φ (max (-a) (min x a))| ≤ A * Real.exp a := fun x => by
    rw [abs_of_pos (hφ _)]
    refine (hA _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hA0)
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  have := hp ι Ω P w g hw0 hw1 hm hsub
  rwa [integral_eval_sum_mul_comp_eq (ψ := fun x => φ (max (-a) (min x a))) hw0 hw1 hg h0 hm
    hψm hψ p] at this

/-- **Continuity and boundedness of the replica functionals `F_k` (Panchenko Eq. (1.67)).**  For a
continuous bounded `ψ` and a continuous covariance function `C`, the Gaussian moment
`Q ↦ ∫ ∏ₗ ψ (xₗ) d𝒩(0, (C (Q l l'))ₗₗ')` of `k` replicas is bounded by `M^k` and continuous on the
set of overlap matrices `Q` for which `(C (Q l l'))` is positive semidefinite (the only ones that
occur). -/
theorem continuousOn_integral_prod_multivariateGaussian {C ψ : ℝ → ℝ} (hC : Continuous C)
    (hψ : Continuous ψ) {M : ℝ} (hM : ∀ x, ‖ψ x‖ ≤ M) (k : ℕ) :
    ContinuousOn (fun Q : Fin k → Fin k → ℝ =>
      ∫ x : EuclideanSpace ℝ (Fin k), ∏ l, ψ (x.ofLp l)
        ∂(multivariateGaussian 0 (Matrix.of fun l l' => C (Q l l'))))
      {Q | (Matrix.of fun l l' => C (Q l l')).PosSemidef} := by
  have hf : Continuous fun x : EuclideanSpace ℝ (Fin k) => ∏ l, ψ (x.ofLp l) :=
    continuous_finsetProd _ fun l _ =>
      hψ.comp ((continuous_apply l).comp (PiLp.continuous_ofLp 2 _))
  have hbd : ∀ x : EuclideanSpace ℝ (Fin k), ‖∏ l, ψ (x.ofLp l)‖ ≤ M ^ k := fun x => by
    rw [norm_prod]
    calc ∏ l, ‖ψ (x.ofLp l)‖ ≤ ∏ _l : Fin k, M := by
          gcongr with l
          exact hM _
      _ = M ^ k := by simp
  have hmat : Continuous fun Q : Fin k → Fin k → ℝ => (Matrix.of fun l l' => C (Q l l')) :=
    continuous_pi fun l => continuous_pi fun l' =>
      hC.comp ((continuous_apply l').comp (continuous_apply l))
  exact (continuousOn_integral_multivariateGaussian hf hbd).comp hmat.continuousOn
    fun Q hQ => hQ

/-- The replica functionals are bounded: `|F_k(Q)| ≤ M^k`. -/
theorem abs_integral_prod_multivariateGaussian_le {ψ : ℝ → ℝ} {M : ℝ} (hM : ∀ x, |ψ x| ≤ M)
    {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) :
    |∫ x : EuclideanSpace ℝ (Fin k), ∏ l, ψ (x.ofLp l) ∂(multivariateGaussian 0 S)| ≤ M ^ k := by
  have := norm_integral_le_of_norm_le_const (μ := multivariateGaussian 0 S) (C := M ^ k)
    (f := fun x : EuclideanSpace ℝ (Fin k) => ∏ l, ψ (x.ofLp l))
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, Finset.abs_prod]
      calc ∏ l, |ψ (x.ofLp l)| ≤ ∏ _l : Fin k, M := by
            gcongr with l
            exact hM _
        _ = M ^ k := by simp)
  simpa [Real.norm_eq_abs] using this

/-- **Theorem 1.3 (Gram-matrix approximation of the Gibbs functional, Panchenko Eq. (1.64)).**
Let `Φ = 𝔼 log ⟨2 cosh z⟩ - 𝔼 log ⟨exp y⟩` where `⟨·⟩` is the average under a probability vector
`w` on a finite set and `z`, `y` are centered Gaussian families with second moments at most `vz`,
`vy`.  For every `ε > 0` there are truncation levels `az`, `ay` and polynomials `pz`, `py`,
depending only on `ε`, `vz`, `vy` (not on `w`, on the number of atoms, or on the covariances),
such that `Φ` is within `ε` of
`∑_k pz_k ∑_j (∏ₗ w_{jₗ}) Fz_k(Cz_j) - ∑_k py_k ∑_j (∏ₗ w_{jₗ}) Fy_k(Cy_j)`, where `C*_j` is the
covariance matrix of the `k` replicas `j : Fin k → ι` and `F*_k` the (continuous bounded) Gaussian
replica functional of `continuousOn_integral_prod_multivariateGaussian`: the right side is the
`w`-average of a continuous bounded function of the overlaps of finitely many replicas. -/
theorem exists_gram_approx_free_energy (vz vy : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (az ay : ℝ) (pz py : Polynomial ℝ), 0 ≤ az ∧ 0 ≤ ay ∧
      ∀ (ι : Type u) [Fintype ι] (w : ι → ℝ), (∀ i, 0 ≤ w i) → ∑ i, w i = 1 →
        ∀ (Ω : Type u') [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (z : ι → Ω → ℝ) (Ω' : Type u') [MeasurableSpace Ω'] (P' : Measure Ω')
          [IsProbabilityMeasure P'] (y : ι → Ω' → ℝ),
        (∀ i, Measurable (z i)) → HasGaussianLaw (fun ω i => z i ω) P →
        (∀ i, ∫ ω, z i ω ∂P = 0) → (∀ i, ∫ ω, z i ω ^ 2 ∂P ≤ vz) →
        (∀ i, Measurable (y i)) → HasGaussianLaw (fun ω i => y i ω) P' →
        (∀ i, ∫ ω, y i ω ∂P' = 0) → (∀ i, ∫ ω, y i ω ^ 2 ∂P' ≤ vy) →
        |((∫ ω, Real.log (∑ i, w i * (2 * Real.cosh (z i ω))) ∂P) -
            ∫ ω, Real.log (∑ i, w i * Real.exp (y i ω)) ∂P') -
          ((∑ k ∈ range (pz.natDegree + 1), pz.coeff k * ∑ j : Fin k → ι, (∏ l, w (j l)) *
            ∫ x : EuclideanSpace ℝ (Fin k),
              ∏ l, 2 * Real.cosh (max (-az) (min (x.ofLp l) az)) ∂(multivariateGaussian 0
                (Matrix.of fun l l' => ∫ ω, z (j l) ω * z (j l') ω ∂P))) -
          ∑ k ∈ range (py.natDegree + 1), py.coeff k * ∑ j : Fin k → ι, (∏ l, w (j l)) *
            ∫ x : EuclideanSpace ℝ (Fin k),
              ∏ l, Real.exp (max (-ay) (min (x.ofLp l) ay)) ∂(multivariateGaussian 0
                (Matrix.of fun l l' => ∫ ω, y (j l) ω * y (j l') ω ∂P')))| ≤ ε := by
  obtain ⟨az, haz, pz, hpz⟩ := exists_gram_approx (φ := fun x => 2 * Real.cosh x) (A := 2) (B := 1)
    vz (by fun_prop) (fun x => by positivity) two_cosh_le_exp_abs_mul inv_two_cosh_le_exp_abs_mul
    (half_pos hε)
  obtain ⟨ay, hay, py, hpy⟩ := exists_gram_approx (φ := Real.exp) (A := 1) (B := 1) vy
    Real.continuous_exp Real.exp_pos exp_le_exp_abs_mul inv_exp_le_exp_abs_mul (half_pos hε)
  refine ⟨az, ay, pz, py, haz, hay, fun ι _ w hw0 hw1 Ω _ P _ z Ω' _ P' _ y hzm hzg hz0 hzv hym hyg
    hy0 hyv => ?_⟩
  have h1 := hpz ι Ω P w z hw0 hw1 hzm hzg hz0 hzv
  have h2 := hpy ι Ω' P' w y hw0 hw1 hym hyg hy0 hyv
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Theorem 1.3, in the form of a single Gram-matrix functional (Panchenko Eq. (1.64)).**
Let `Cz`, `Cy` be continuous covariance functions.  For every `ε > 0` there are `m` and a bounded
function `F` of the `m × m` Gram matrix of `m` replicas, continuous on the set of Gram matrices `Q`
for which `(Cz (Q l l'))` and `(Cy (Q l l'))` are positive semidefinite (the only ones that occur),
such that for every finite probability vector `w`, every Gram array `q` and all centered Gaussian
families `z`, `y` with `𝔼 zᵢ zⱼ = Cz (q i j)`, `𝔼 yᵢ yⱼ = Cy (q i j)` and second moments at most
`vz`, `vy`,
`|𝔼 log ⟨2 cosh z⟩ - 𝔼 log ⟨exp y⟩ - ∑_{j : Fin m → ι} (∏ₗ w_{jₗ}) F((q_{jₗ jₗ'})ₗₗ')| ≤ ε`:
the left side is within `ε` of the Gibbs average of the continuous bounded function `F` of the
overlap matrix of `m` i.i.d. replicas, uniformly over `w`, `ι`, `q`. -/
theorem exists_continuousOn_gram_approx {Cz Cy : ℝ → ℝ} (hCz : Continuous Cz)
    (hCy : Continuous Cy) (vz vy : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (F : (Fin m → Fin m → ℝ) → ℝ),
      ContinuousOn F {Q | (Matrix.of fun l l' => Cz (Q l l')).PosSemidef ∧
        (Matrix.of fun l l' => Cy (Q l l')).PosSemidef} ∧ (∃ M, ∀ Q, |F Q| ≤ M) ∧
      ∀ (ι : Type u) [Fintype ι] (w : ι → ℝ) (q : ι → ι → ℝ), (∀ i, 0 ≤ w i) → ∑ i, w i = 1 →
        ∀ (Ω : Type u') [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (z : ι → Ω → ℝ) (Ω' : Type u') [MeasurableSpace Ω'] (P' : Measure Ω')
          [IsProbabilityMeasure P'] (y : ι → Ω' → ℝ),
        (∀ i, Measurable (z i)) → HasGaussianLaw (fun ω i => z i ω) P →
        (∀ i, ∫ ω, z i ω ∂P = 0) → (∀ i, ∫ ω, z i ω ^ 2 ∂P ≤ vz) →
        (∀ i j, ∫ ω, z i ω * z j ω ∂P = Cz (q i j)) →
        (∀ i, Measurable (y i)) → HasGaussianLaw (fun ω i => y i ω) P' →
        (∀ i, ∫ ω, y i ω ∂P' = 0) → (∀ i, ∫ ω, y i ω ^ 2 ∂P' ≤ vy) →
        (∀ i j, ∫ ω, y i ω * y j ω ∂P' = Cy (q i j)) →
        |((∫ ω, Real.log (∑ i, w i * (2 * Real.cosh (z i ω))) ∂P) -
            ∫ ω, Real.log (∑ i, w i * Real.exp (y i ω)) ∂P') -
          ∑ j : Fin m → ι, (∏ l, w (j l)) * F (fun l l' => q (j l) (j l'))| ≤ ε := by
  obtain ⟨az, ay, pz, py, haz, hay, h13⟩ := exists_gram_approx_free_energy.{u, u'} vz vy hε
  have hzk : ∀ k : Fin (pz.natDegree + 1), (k : ℕ) ≤ max pz.natDegree py.natDegree := fun k =>
    (Nat.lt_succ_iff.1 k.2).trans (le_max_left _ _)
  have hyk : ∀ k : Fin (py.natDegree + 1), (k : ℕ) ≤ max pz.natDegree py.natDegree := fun k =>
    (Nat.lt_succ_iff.1 k.2).trans (le_max_right _ _)
  refine ⟨max pz.natDegree py.natDegree, fun Q =>
    (∑ k : Fin (pz.natDegree + 1), pz.coeff k * ∫ x : EuclideanSpace ℝ (Fin k),
      ∏ l, 2 * Real.cosh (max (-az) (min (x.ofLp l) az)) ∂(multivariateGaussian 0
        (Matrix.of fun l l' => Cz (Q (Fin.castLE (hzk k) l) (Fin.castLE (hzk k) l'))))) -
    ∑ k : Fin (py.natDegree + 1), py.coeff k * ∫ x : EuclideanSpace ℝ (Fin k),
      ∏ l, Real.exp (max (-ay) (min (x.ofLp l) ay)) ∂(multivariateGaussian 0
        (Matrix.of fun l l' => Cy (Q (Fin.castLE (hyk k) l) (Fin.castLE (hyk k) l')))),
    ?_, ?_, ?_⟩
  · refine ContinuousOn.sub (continuousOn_finsetSum _ fun k _ => continuousOn_const.mul ?_)
      (continuousOn_finsetSum _ fun k _ => continuousOn_const.mul ?_)
    · have hr : Continuous fun Q : Fin (max pz.natDegree py.natDegree) →
          Fin (max pz.natDegree py.natDegree) → ℝ =>
          fun l l' : Fin k => Q (Fin.castLE (hzk k) l) (Fin.castLE (hzk k) l') := by fun_prop
      exact (continuousOn_integral_prod_multivariateGaussian hCz (by fun_prop)
        (fun x => abs_two_cosh_clamp_le haz x) k).comp hr.continuousOn fun Q hQ =>
          hQ.1.submatrix (Fin.castLE (hzk k))
    · have hr : Continuous fun Q : Fin (max pz.natDegree py.natDegree) →
          Fin (max pz.natDegree py.natDegree) → ℝ =>
          fun l l' : Fin k => Q (Fin.castLE (hyk k) l) (Fin.castLE (hyk k) l') := by fun_prop
      exact (continuousOn_integral_prod_multivariateGaussian hCy (by fun_prop)
        (fun x => abs_exp_clamp_le hay x) k).comp hr.continuousOn fun Q hQ =>
          hQ.2.submatrix (Fin.castLE (hyk k))
  · refine ⟨(∑ k : Fin (pz.natDegree + 1), |pz.coeff k| * (2 * Real.exp az) ^ (k : ℕ)) +
      ∑ k : Fin (py.natDegree + 1), |py.coeff k| * Real.exp ay ^ (k : ℕ), fun Q => ?_⟩
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_integral_prod_multivariateGaussian_le
        (fun x => abs_two_cosh_clamp_le haz x) _) (abs_nonneg _)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_integral_prod_multivariateGaussian_le
        (fun x => abs_exp_clamp_le hay x) _) (abs_nonneg _)
  · intro ι _ w q hw0 hw1 Ω _ P _ z Ω' _ P' _ y hzm hzg hz0 hzv hzc hym hyg hy0 hyv hyc
    have h := h13 ι w hw0 hw1 Ω P z Ω' P' y hzm hzg hz0 hzv hym hyg hy0 hyv
    simp only [hzc, hyc, Finset.sum_range] at h
    have e1 : ∀ k : Fin (pz.natDegree + 1), ∑ j : Fin (max pz.natDegree py.natDegree) → ι,
        (∏ l, w (j l)) * ∫ x : EuclideanSpace ℝ (Fin k),
          ∏ l, 2 * Real.cosh (max (-az) (min (x.ofLp l) az)) ∂(multivariateGaussian 0
            (Matrix.of fun l l' => Cz (q (j (Fin.castLE (hzk k) l)) (j (Fin.castLE (hzk k) l'))))) =
        ∑ j : Fin k → ι, (∏ l, w (j l)) * ∫ x : EuclideanSpace ℝ (Fin k),
          ∏ l, 2 * Real.cosh (max (-az) (min (x.ofLp l) az)) ∂(multivariateGaussian 0
            (Matrix.of fun l l' => Cz (q (j l) (j l')))) := fun k =>
      sum_prod_mul_comp_castLE hw1 (hzk k) fun j => ∫ x : EuclideanSpace ℝ (Fin k),
        ∏ l, 2 * Real.cosh (max (-az) (min (x.ofLp l) az)) ∂(multivariateGaussian 0
          (Matrix.of fun l l' => Cz (q (j l) (j l'))))
    have e2 : ∀ k : Fin (py.natDegree + 1), ∑ j : Fin (max pz.natDegree py.natDegree) → ι,
        (∏ l, w (j l)) * ∫ x : EuclideanSpace ℝ (Fin k),
          ∏ l, Real.exp (max (-ay) (min (x.ofLp l) ay)) ∂(multivariateGaussian 0
            (Matrix.of fun l l' => Cy (q (j (Fin.castLE (hyk k) l)) (j (Fin.castLE (hyk k) l'))))) =
        ∑ j : Fin k → ι, (∏ l, w (j l)) * ∫ x : EuclideanSpace ℝ (Fin k),
          ∏ l, Real.exp (max (-ay) (min (x.ofLp l) ay)) ∂(multivariateGaussian 0
            (Matrix.of fun l l' => Cy (q (j l) (j l')))) := fun k =>
      sum_prod_mul_comp_castLE hw1 (hyk k) fun j => ∫ x : EuclideanSpace ℝ (Fin k),
        ∏ l, Real.exp (max (-ay) (min (x.ofLp l) ay)) ∂(multivariateGaussian 0
          (Matrix.of fun l l' => Cy (q (j l) (j l'))))
    simp only [mul_sub, Finset.sum_sub_distrib, sum_mul_sum_comm, e1, e2]
    exact h

end Approx

end SpinGlasses
