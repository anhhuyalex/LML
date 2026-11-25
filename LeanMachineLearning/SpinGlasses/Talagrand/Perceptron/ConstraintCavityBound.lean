/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityRegularity
public import LeanMachineLearning.SpinGlasses.Gaussian.GaussianReplicaTheta

/-!
# The bound (2.40) at a fixed angle and fixed old system

Talagrand Section 2.3, Lemma 2.3.2 for `B_v ≡ 1`. The pathwise derivative
(`hasDerivAt_integral_cavityRatio_theta`) is `sin t cos t 𝔼_ξ ⟨f Θ⟩`; with `|u| ≤ D'` and
`|q - C| ≤ |q - R| + 1/(N+1)` the kernel of `Θ` is bounded by `α d + β` with `d = |R - q|`, so
the model-free estimate `abs_integral_integral_theta_le` gives the Hölder bound of (2.40).

* `SpinGlasses.abs_cavity_theta_le`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

variable {N : ℕ} {R : Type*} [Fintype R] [DecidableEq R]

omit [DecidableEq R] in
/-- **The bound (2.40) at a fixed angle for a spin-only observable.** Let `Y ξ σ` be the spin
fields of the Gaussian block `ξ`, `ψ` the smoothing with `|ψ₁/ψ| ≤ D'`, and `Θint ξ` the replica
expression of `hasDerivAt_integral_cavityRatio_theta`. Then
`|𝔼_ξ Θint| ≤ (4n² + n) D'² ((𝔼⟨|f|^p⟩)^{1/p} (𝔼⟨|R_{12} - q|^r⟩)^{1/r} + 𝔼⟨|f|⟩/(N+1))`,
where `R(σ,τ) = (∑_i σ_i τ_i + ε ε')/(N+1)` is the overlap and `⟨·⟩` the Gibbs average at the site
energies `log w + log ψ (Y ξ)`. -/
theorem abs_cavity_theta_le {w : PerceptronSpin N → ℝ} {ψ ψ₁ : ℝ → ℝ} (hψm : Measurable ψ)
    {q p D' : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (hD' : ∀ x, |ψ₁ x / ψ x| ≤ D')
    (Y : ((Fin N ⊕ Unit) ⊕ Unit → ℝ) → PerceptronSpin N → ℝ)
    (hY : ∀ l, Measurable fun ξ => Y ξ l) (f : (R → PerceptronSpin N) → ℝ) {pp rr : ℝ}
    (hpr : pp.HolderConjugate rr) :
    |∫ ξ, (∑ l, ∑ k, (q - cavityCoef N p l ⬝ᵥ cavityCoef N p k) *
          (ψ₁ (Y ξ l) / ψ (Y ξ l)) * (ψ₁ (Y ξ k) / ψ (Y ξ k)) *
          ∫ σ, (((∑ r, if σ r = l then (1 : ℝ) else 0) -
            Fintype.card R * (Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {l}) *
            ((∑ r, if σ r = k then (1 : ℝ) else 0) -
            Fintype.card R * (Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {k}) -
            Fintype.card R * (Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {l} *
            ((if l = k then 1 else 0) - (Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {k})) * f σ
            ∂(Measure.pi fun _ : R => Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))) -
        ∑ l, (q - cavityCoef N p l ⬝ᵥ cavityCoef N p l) * (ψ₁ (Y ξ l) / ψ (Y ξ l)) ^ 2 *
          ∫ σ, ((∑ r, if σ r = l then (1 : ℝ) else 0) -
            Fintype.card R * (Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {l}) * f σ
            ∂(Measure.pi fun _ : R => Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))))
        ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)| ≤
    (4 * (Fintype.card R : ℝ) ^ 2 + Fintype.card R) *
      (D' ^ 2 * ((∫ ξ, ∫ σ : R → PerceptronSpin N, |f σ| ^ pp ∂(Measure.pi fun _ : R =>
          Measure.count.tilted (fun a => Real.log (w a) + Real.log (ψ (Y ξ a))))
          ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)) ^ (1 / pp) *
        (∫ ξ, ∫ τ : Fin 2 → PerceptronSpin N,
          |q - ((∑ i, (((τ 0).1 i : ℤ) : ℝ) * (((τ 1).1 i : ℤ) : ℝ)) +
            (((τ 0).2 : ℤ) : ℝ) * (((τ 1).2 : ℤ) : ℝ)) / (N + 1)| ^ rr
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted
            (fun a => Real.log (w a) + Real.log (ψ (Y ξ a))))
          ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)) ^ (1 / rr)) +
      D' ^ 2 / (N + 1) * ∫ ξ, ∫ σ : R → PerceptronSpin N, |f σ| ∂(Measure.pi fun _ : R =>
          Measure.count.tilted (fun a => Real.log (w a) + Real.log (ψ (Y ξ a))))
          ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)) := by
  have hD0 : 0 ≤ D' := (abs_nonneg _).trans (hD' 0)
  have hE : ∀ a, Measurable fun ξ => Real.log (w a) + Real.log (ψ (Y ξ a)) := fun a =>
    measurable_const.add (Real.measurable_log.comp (hψm.comp (hY a)))
  have hcm : ∀ (ξ : (Fin N ⊕ Unit) ⊕ Unit → ℝ) (a b : PerceptronSpin N),
      |(q - cavityCoef N p a ⬝ᵥ cavityCoef N p b) * (ψ₁ (Y ξ a) / ψ (Y ξ a)) *
        (ψ₁ (Y ξ b) / ψ (Y ξ b))| ≤
      D' ^ 2 * |q - ((∑ i, (((a.1 i : ℤ) : ℝ) * ((b.1 i : ℤ) : ℝ))) +
        ((a.2 : ℤ) : ℝ) * ((b.2 : ℤ) : ℝ)) / (N + 1)| + D' ^ 2 / (N + 1) := fun ξ a b => by
    have h1 := abs_cavityCoef_dotProduct_sub_overlap_le (N := N) hp a b
    have h2 : |q - cavityCoef N p a ⬝ᵥ cavityCoef N p b| ≤
        |q - ((∑ i, (((a.1 i : ℤ) : ℝ) * ((b.1 i : ℤ) : ℝ))) +
          ((a.2 : ℤ) : ℝ) * ((b.2 : ℤ) : ℝ)) / (N + 1)| + 1 / (N + 1) := by
      refine (abs_sub_le q (((∑ i, (((a.1 i : ℤ) : ℝ) * ((b.1 i : ℤ) : ℝ))) +
        ((a.2 : ℤ) : ℝ) * ((b.2 : ℤ) : ℝ)) / (N + 1)) (cavityCoef N p a ⬝ᵥ cavityCoef N p b)).trans
        (add_le_add le_rfl ?_)
      rw [abs_sub_comm]
      exact h1
    rw [abs_mul, abs_mul]
    have hu : |ψ₁ (Y ξ a) / ψ (Y ξ a)| * |ψ₁ (Y ξ b) / ψ (Y ξ b)| ≤ D' ^ 2 := by
      rw [sq]; exact mul_le_mul (hD' _) (hD' _) (abs_nonneg _) hD0
    calc _ = |q - cavityCoef N p a ⬝ᵥ cavityCoef N p b| *
          (|ψ₁ (Y ξ a) / ψ (Y ξ a)| * |ψ₁ (Y ξ b) / ψ (Y ξ b)|) := by ring
      _ ≤ (|q - ((∑ i, (((a.1 i : ℤ) : ℝ) * ((b.1 i : ℤ) : ℝ))) +
          ((a.2 : ℤ) : ℝ) * ((b.2 : ℤ) : ℝ)) / (N + 1)| + 1 / (N + 1)) * D' ^ 2 :=
        mul_le_mul h2 hu (by positivity) (by positivity)
      _ = _ := by ring
  classical
  have key := abs_integral_integral_theta_le (R := R)
    (μ := Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)
    (fun ξ a => Real.log (w a) + Real.log (ψ (Y ξ a))) hE
    (fun ξ a b => (q - cavityCoef N p a ⬝ᵥ cavityCoef N p b) * (ψ₁ (Y ξ a) / ψ (Y ξ a)) *
      (ψ₁ (Y ξ b) / ψ (Y ξ b)))
    (fun a b => |q - ((∑ i, (((a.1 i : ℤ) : ℝ) * ((b.1 i : ℤ) : ℝ))) +
        ((a.2 : ℤ) : ℝ) * ((b.2 : ℤ) : ℝ)) / (N + 1)|) (fun a b => abs_nonneg _)
    (sq_nonneg D') (by positivity) hcm f hpr
  refine le_trans (le_of_eq ?_) key
  congr 2
  funext ξ
  rw [← sum_mul_integral_eq_integral_sum (R := R)
    (Measure.pi fun _ : R => Measure.count.tilted
      (fun a => Real.log (w a) + Real.log (ψ (Y ξ a))))
    (fun l k => (q - cavityCoef N p l ⬝ᵥ cavityCoef N p k) * (ψ₁ (Y ξ l) / ψ (Y ξ l)) *
      (ψ₁ (Y ξ k) / ψ (Y ξ k)))
    (fun l k σ => ((∑ r, if σ r = l then (1 : ℝ) else 0) -
            Fintype.card R * (Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {l}) *
            ((∑ r, if σ r = k then (1 : ℝ) else 0) -
            Fintype.card R * (Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {k}) -
            Fintype.card R * (Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {l} *
            ((if l = k then 1 else 0) - (Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {k}))
    (fun l σ => ((∑ r, if σ r = l then (1 : ℝ) else 0) -
            Fintype.card R * (Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a)))).real {l})) f]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by ring

/-- **The derivative of the quenched spin-only average at an angle, with its bound (2.40).** Under
the hypotheses of `hasDerivAt_integral_cavityRatio_theta`, the derivative of
`s ↦ 𝔼_ξ F(τ s, cos s X + sin s Y)` at the angle `t` exists, and is bounded by
`(1/2)(4n² + n) D'² ((𝔼⟨|f|^p⟩)^{1/p} (𝔼⟨|R₁₂ - q|^r⟩)^{1/r} + 𝔼⟨|f|⟩/(N+1))` with
`D' = e^{D+B} D₁`, the Gibbs averages taken at the angle `t`. -/
theorem exists_hasDerivAt_abs_le_cavityRatio {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    {B D D₁ D₂ : ℝ} (hB : ∀ x, -B ≤ u x) (hD : ∀ x, u x ≤ D) (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    {w : PerceptronSpin N → ℝ} (hw : ∀ a, 0 < w a) (f : (R → PerceptronSpin N) → ℝ)
    (a₀ t p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (ha₀ : a₀ ^ 2 = (1 - p) / (N + 1))
    (F : (ℝ × ℝ) × (PerceptronSpin N → ℝ) → ℝ)
    (hF : ∀ x, F x = (∑ σ : R → PerceptronSpin N, f σ * ∏ r, (w (σ r) *
        ∫ η, Real.exp (u (x.2 (σ r) + η.1 * x.1.1 + η.2 * x.1.2))
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))) /
      (∑ a, w a * ∫ η, Real.exp (u (x.2 a + η.1 * x.1.1 + η.2 * x.1.2))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) ^ Fintype.card R)
    (ψ ψ₁ ψ₂ : ℝ → ℝ)
    (hψ : ∀ x, ψ x = ∫ η, Real.exp (u (x + η.1 * (Real.cos t * a₀) +
      η.2 * (Real.sin t * Real.sqrt (1 - q)))) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))
    (hψ₁ : ∀ x, ψ₁ x = ∫ η, deriv (fun x => Real.exp (u x)) (x + η.1 * (Real.cos t * a₀) +
      η.2 * (Real.sin t * Real.sqrt (1 - q))) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))
    (hψ₂ : ∀ x, ψ₂ x = ∫ η, deriv (deriv fun x => Real.exp (u x)) (x + η.1 * (Real.cos t * a₀) +
      η.2 * (Real.sin t * Real.sqrt (1 - q))) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))
    (Y : ((Fin N ⊕ Unit) ⊕ Unit → ℝ) → PerceptronSpin N → ℝ)
    (hYd : ∀ ξ l, Y ξ l = Real.cos t * ((Sum.elim (cavityCoef N p l) (fun _ : Unit => (0 : ℝ)) :
        (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) + Real.sin t * ((Sum.elim
        (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
        (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ)) {pp rr : ℝ} (hpr : pp.HolderConjugate rr) :
    ∃ g' : ℝ, HasDerivAt (fun s => ∫ ξ, F ((Real.cos s * a₀, Real.sin s * Real.sqrt (1 - q)),
        fun σ => Real.cos s * ((Sum.elim (cavityCoef N p σ) (fun _ : Unit => (0 : ℝ)) :
          (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) + Real.sin s * ((Sum.elim
          (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
          (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ))
        ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)) g' t ∧
      |g'| ≤ 1 / 2 * ((4 * (Fintype.card R : ℝ) ^ 2 + Fintype.card R) *
        ((Real.exp (D + B) * D₁) ^ 2 * ((∫ ξ, ∫ σ : R → PerceptronSpin N, |f σ| ^ pp
            ∂(Measure.pi fun _ : R => Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a))))
            ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)) ^ (1 / pp) *
          (∫ ξ, ∫ τ : Fin 2 → PerceptronSpin N,
            |q - ((∑ i, (((τ 0).1 i : ℤ) : ℝ) * (((τ 1).1 i : ℤ) : ℝ)) +
              (((τ 0).2 : ℤ) : ℝ) * (((τ 1).2 : ℤ) : ℝ)) / (N + 1)| ^ rr
            ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a))))
            ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)) ^ (1 / rr)) +
        (Real.exp (D + B) * D₁) ^ 2 / (N + 1) * ∫ ξ, ∫ σ : R → PerceptronSpin N, |f σ|
            ∂(Measure.pi fun _ : R => Measure.count.tilted
              (fun a => Real.log (w a) + Real.log (ψ (Y ξ a))))
            ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1))) := by
  have hdt := hasDerivAt_integral_cavityRatio_theta hu hB hD hD₁ hD₂ hq hw f a₀ t p hp ha₀ F hF
    ψ ψ₁ ψ₂ hψ hψ₁ hψ₂ Y hYd
  refine ⟨_, hdt, ?_⟩
  have hpos : ∀ x, 0 < ψ x := fun x => by
    rw [hψ]
    exact integral_exp_comp_gaussian_pos hu.continuous hB hD x _ _
  have hD' : ∀ x, |ψ₁ x / ψ x| ≤ Real.exp (D + B) * D₁ := fun x => by
    rw [abs_div, abs_of_pos (hpos x), hψ₁ x, hψ x]
    exact abs_integral_deriv_exp_comp_div_le hu hB hD hD₁ x _ _
  have hψm : Measurable ψ := by
    rw [show ψ = _ from funext hψ]
    exact measurable_integral_exp_comp_gaussian hu hD hD₁ hD₂ _ _
  have hYm : ∀ l, Measurable fun ξ => Y ξ l := fun l => by
    rw [show (fun ξ => Y ξ l) = _ from funext fun ξ => hYd ξ l]
    exact measurable_cavityField N p q t l
  have hbd := abs_cavity_theta_le (R := R) (w := w) (q := q) hψm hp hD' Y hYm f hpr
  have hsc : |Real.sin t * Real.cos t| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (Real.sin t + Real.cos t),
      sq_nonneg (Real.sin t - Real.cos t), Real.sin_sq_add_cos_sq t]
  rw [abs_mul]
  exact mul_le_mul hsc hbd (abs_nonneg _) (by norm_num)

end SpinGlasses
