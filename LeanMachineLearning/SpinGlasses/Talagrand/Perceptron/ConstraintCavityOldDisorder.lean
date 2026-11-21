/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityBound
public import LeanMachineLearning.ForMathlib.MeasureTheory.Function.AEStronglyMeasurableDeriv

/-!
# The bound (2.40) after averaging the old disorder

Talagrand Section 2.3, Lemma 2.3.2 for `B_v ≡ 1`. At every old disorder `ω` the quenched
spin-only average `G_ω(s)` is differentiable in the angle `s` and
`|G_ω'(s)| ≤ ½ (4n² + n) D'² (A_ω B_ω + C_ω / (N+1))` is bounded uniformly in `ω` and `s` (the
spin set is finite). Differentiating under the integral over `ω` is then dominated convergence,
and Hölder over `ω` gives the bound of (2.40) for the averaged quantity.

* `SpinGlasses.exists_hasDerivAt_integral_abs_le_cavityRatio`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

variable {N : ℕ} {R : Type*} [Fintype R] [DecidableEq R]

/-- **The bound (2.40) after averaging the old disorder.** Under the hypotheses of
`exists_hasDerivAt_abs_le_cavityRatio`, with weights `w ω` and a bounded observable `f ω` depending
measurably on a probability space `Ω₀` of old disorders and old auxiliary coordinates, the
derivative at every angle `t` of `s ↦ 𝔼_ω 𝔼_ξ F_ω(τ s, cos s X + sin s Y)` exists and is bounded by
`(1/2)(4n² + n) D'² ((𝔼⟨|f|^p⟩)^{1/p} (𝔼⟨|R₁₂ - q|^r⟩)^{1/r} + 𝔼⟨|f|⟩/(N+1))` with all averages
over `(ω, ξ)` and the Gibbs average at the angle `t`. The families `ψ s`, `Y s` are the smoothing
and the spin fields at the angle `s`. -/
theorem exists_hasDerivAt_integral_abs_le_cavityRatio {Ω₀ : Type*} [MeasurableSpace Ω₀]
    (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀] {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    {B D D₁ D₂ : ℝ} (hB : ∀ x, -B ≤ u x) (hD : ∀ x, u x ≤ D) (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂) {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    {w : Ω₀ → PerceptronSpin N → ℝ} (hw : ∀ ω a, 0 < w ω a)
    (hwm : ∀ a, Measurable fun ω => w ω a) (f : Ω₀ → (R → PerceptronSpin N) → ℝ)
    (hfm : ∀ σ, Measurable fun ω => f ω σ) {Fm : ℝ} (hfb : ∀ ω σ, |f ω σ| ≤ Fm)
    (a₀ p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) (ha₀ : a₀ ^ 2 = (1 - p) / (N + 1))
    (F : Ω₀ → (ℝ × ℝ) × (PerceptronSpin N → ℝ) → ℝ)
    (hF : ∀ ω x, F ω x = (∑ σ : R → PerceptronSpin N, f ω σ * ∏ r, (w ω (σ r) *
        ∫ η, Real.exp (u (x.2 (σ r) + η.1 * x.1.1 + η.2 * x.1.2))
          ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))) /
      (∑ a, w ω a * ∫ η, Real.exp (u (x.2 a + η.1 * x.1.1 + η.2 * x.1.2))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) ^ Fintype.card R)
    (ψ : ℝ → ℝ → ℝ)
    (hψ : ∀ s x, ψ s x = ∫ η, Real.exp (u (x + η.1 * (Real.cos s * a₀) +
      η.2 * (Real.sin s * Real.sqrt (1 - q)))) ∂((gaussianReal 0 1).prod (gaussianReal 0 1)))
    (Y : ℝ → ((Fin N ⊕ Unit) ⊕ Unit → ℝ) → PerceptronSpin N → ℝ)
    (hYd : ∀ s ξ l, Y s ξ l = Real.cos s * ((Sum.elim (cavityCoef N p l)
        (fun _ : Unit => (0 : ℝ)) : (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) + Real.sin s * ((Sum.elim
        (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
        (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ)) {pp rr : ℝ} (hpr : pp.HolderConjugate rr) (t : ℝ) :
    ∃ g' : ℝ, HasDerivAt (fun s => ∫ ω, ∫ ξ, F ω ((Real.cos s * a₀, Real.sin s * Real.sqrt (1 - q)),
        fun σ => Real.cos s * ((Sum.elim (cavityCoef N p σ) (fun _ : Unit => (0 : ℝ)) :
          (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) + Real.sin s * ((Sum.elim
          (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
          (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ))
        ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) ∂P₀) g' t ∧
      |g'| ≤ 1 / 2 * ((4 * (Fintype.card R : ℝ) ^ 2 + Fintype.card R) *
        ((Real.exp (D + B) * D₁) ^ 2 * ((∫ ω, ∫ ξ, ∫ σ : R → PerceptronSpin N, |f ω σ| ^ pp
            ∂(Measure.pi fun _ : R => Measure.count.tilted
              (fun a => Real.log (w ω a) + Real.log (ψ t (Y t ξ a))))
            ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) ∂P₀) ^ (1 / pp) *
          (∫ ω, ∫ ξ, ∫ τ : Fin 2 → PerceptronSpin N,
            |q - ((∑ i, (((τ 0).1 i : ℤ) : ℝ) * (((τ 1).1 i : ℤ) : ℝ)) +
              (((τ 0).2 : ℤ) : ℝ) * (((τ 1).2 : ℤ) : ℝ)) / (N + 1)| ^ rr
            ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted
              (fun a => Real.log (w ω a) + Real.log (ψ t (Y t ξ a))))
            ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) ∂P₀) ^ (1 / rr)) +
        (Real.exp (D + B) * D₁) ^ 2 / (N + 1) * ∫ ω, ∫ ξ, ∫ σ : R → PerceptronSpin N, |f ω σ|
            ∂(Measure.pi fun _ : R => Measure.count.tilted
              (fun a => Real.log (w ω a) + Real.log (ψ t (Y t ξ a))))
            ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) ∂P₀)) := by
  classical
  have hq0 : 0 ≤ q := hq.1
  obtain ⟨ψ₁s, hψ₁s⟩ : ∃ ψ₁s : ℝ → ℝ → ℝ, ∀ s x, ψ₁s s x = ∫ η, deriv (fun x => Real.exp (u x))
      (x + η.1 * (Real.cos s * a₀) + η.2 * (Real.sin s * Real.sqrt (1 - q)))
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨ψ₂s, hψ₂s⟩ : ∃ ψ₂s : ℝ → ℝ → ℝ, ∀ s x, ψ₂s s x = ∫ η,
      deriv (deriv fun x => Real.exp (u x))
      (x + η.1 * (Real.cos s * a₀) + η.2 * (Real.sin s * Real.sqrt (1 - q)))
      ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Gm, hGm⟩ : ∃ Gm : Ω₀ → ℝ → ℝ, ∀ ω s, Gm ω s = ∫ ξ, F ω
      ((Real.cos s * a₀, Real.sin s * Real.sqrt (1 - q)),
        fun σ => Real.cos s * ((Sum.elim (cavityCoef N p σ) (fun _ : Unit => (0 : ℝ)) :
          (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) + Real.sin s * ((Sum.elim
          (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
          (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ))
      ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) := ⟨_, fun _ _ => rfl⟩
  have hψpos : ∀ s x, 0 < ψ s x := fun s x => by
    rw [hψ]
    exact integral_exp_comp_gaussian_pos hu.continuous hB hD x _ _
  have hψm : ∀ s, Measurable (ψ s) := fun s => by
    rw [show ψ s = _ from funext (hψ s)]
    exact measurable_integral_exp_comp_gaussian hu hD hD₁ hD₂ _ _
  have hYm : ∀ s l, Measurable fun ξ => Y s ξ l := fun s l => by
    rw [show (fun ξ => Y s ξ l) = _ from funext fun ξ => hYd s ξ l]
    exact measurable_cavityField N p q s l
  have hEm : ∀ s a, Measurable fun z : Ω₀ × ((Fin N ⊕ Unit) ⊕ Unit → ℝ) =>
      Real.log (w z.1 a) + Real.log (ψ s (Y s z.2 a)) := fun s a =>
    ((Real.measurable_log.comp (hwm a)).comp measurable_fst).add
      (Real.measurable_log.comp ((hψm s).comp ((hYm s a).comp measurable_snd)))
  have hFG : ∀ ω s ξ, F ω ((Real.cos s * a₀, Real.sin s * Real.sqrt (1 - q)),
      fun σ => Real.cos s * ((Sum.elim (cavityCoef N p σ) (fun _ : Unit => (0 : ℝ)) :
          (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) + Real.sin s * ((Sum.elim
          (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
          (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ)) =
      ∫ σ, f ω σ ∂(Measure.pi fun _ : R => Measure.count.tilted
        (fun a => Real.log (w ω a) + Real.log (ψ s (Y s ξ a)))) := fun ω s ξ => by
    rw [hF ω]
    have h1 : ∀ a, (∫ η, Real.exp (u (Real.cos s * ((Sum.elim (cavityCoef N p a)
        (fun _ : Unit => (0 : ℝ)) : (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) + Real.sin s *
        ((Sum.elim (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
          (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) + η.1 * (Real.cos s * a₀) +
        η.2 * (Real.sin s * Real.sqrt (1 - q))))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) = ψ s (Y s ξ a) := fun a => by
      rw [hψ, hYd]
    simp only [h1]
    exact replicaRatio_eq_integral_pi_count_tilted (fun a => hw ω a) (fun a => hψpos s _) (f ω)
  have hGint : ∀ s, Integrable (fun ω => Gm ω s) P₀ := fun s => by
    have := integrable_integral_integral_count_tilted P₀
      (Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)
      (fun ω ξ a => Real.log (w ω a) + Real.log (ψ s (Y s ξ a))) (hEm s) f hfm hfb
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp only [hGm, hFG]
  obtain ⟨Aa, hAa⟩ : ∃ Aa : Ω₀ → ℝ → ℝ, ∀ ω s, Aa ω s = (∫ ξ, ∫ σ : R → PerceptronSpin N,
      |f ω σ| ^ pp ∂(Measure.pi fun _ : R => Measure.count.tilted
        (fun a => Real.log (w ω a) + Real.log (ψ s (Y s ξ a))))
      ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)) ^ (1 / pp) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨Bb, hBb⟩ : ∃ Bb : Ω₀ → ℝ → ℝ, ∀ ω s, Bb ω s = (∫ ξ, ∫ τ : Fin 2 → PerceptronSpin N,
      |q - ((∑ i, (((τ 0).1 i : ℤ) : ℝ) * (((τ 1).1 i : ℤ) : ℝ)) +
        (((τ 0).2 : ℤ) : ℝ) * (((τ 1).2 : ℤ) : ℝ)) / (N + 1)| ^ rr
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted
        (fun a => Real.log (w ω a) + Real.log (ψ s (Y s ξ a))))
      ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)) ^ (1 / rr) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨Cc, hCc⟩ : ∃ Cc : Ω₀ → ℝ → ℝ, ∀ ω s, Cc ω s = ∫ ξ, ∫ σ : R → PerceptronSpin N, |f ω σ|
      ∂(Measure.pi fun _ : R => Measure.count.tilted
        (fun a => Real.log (w ω a) + Real.log (ψ s (Y s ξ a))))
      ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) := ⟨_, fun _ _ => rfl⟩
  have hang : ∀ ω s, ∃ g', HasDerivAt (Gm ω) g' s ∧ |g'| ≤ 1 / 2 *
      ((4 * (Fintype.card R : ℝ) ^ 2 + Fintype.card R) *
        ((Real.exp (D + B) * D₁) ^ 2 * (Aa ω s * Bb ω s) +
          (Real.exp (D + B) * D₁) ^ 2 / (N + 1) * Cc ω s)) := fun ω s => by
    obtain ⟨g', hg', hb⟩ := exists_hasDerivAt_abs_le_cavityRatio (R := R) hu hB hD hD₁ hD₂ hq
      (hw ω) (f ω) a₀ s p hp ha₀ (F ω) (hF ω) (ψ s) (ψ₁s s) (ψ₂s s) (hψ s) (hψ₁s s) (hψ₂s s)
      (Y s) (hYd s) hpr
    refine ⟨g', ?_, ?_⟩
    · have : Gm ω = fun s' => ∫ ξ, F ω ((Real.cos s' * a₀, Real.sin s' * Real.sqrt (1 - q)),
        fun σ => Real.cos s' * ((Sum.elim (cavityCoef N p σ) (fun _ : Unit => (0 : ℝ)) :
          (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) + Real.sin s' * ((Sum.elim
          (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
          (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ))
        ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) := funext (hGm ω)
      rw [this]
      exact hg'
    · rw [hAa, hBb, hCc]
      exact hb
  have hpp : 0 < pp := hpr.pos
  have hrr : 0 < rr := hpr.symm.pos
  -- uniform constants: the spin set is finite
  obtain ⟨ω₀⟩ : Nonempty Ω₀ := MeasureTheory.Measure.nonempty_of_neZero P₀
  have hFm0 : 0 ≤ Fm := (abs_nonneg _).trans (hfb ω₀ (Classical.arbitrary _))
  obtain ⟨Dm, hDm⟩ : ∃ Dm : ℝ, Dm = ∑ τ : Fin 2 → PerceptronSpin N,
      |q - ((∑ i, (((τ 0).1 i : ℤ) : ℝ) * (((τ 1).1 i : ℤ) : ℝ)) +
        (((τ 0).2 : ℤ) : ℝ) * (((τ 1).2 : ℤ) : ℝ)) / (N + 1)| := ⟨_, rfl⟩
  have hDm0 : 0 ≤ Dm := hDm ▸ Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hdle : ∀ τ : Fin 2 → PerceptronSpin N,
      |q - ((∑ i, (((τ 0).1 i : ℤ) : ℝ) * (((τ 1).1 i : ℤ) : ℝ)) +
        (((τ 0).2 : ℤ) : ℝ) * (((τ 1).2 : ℤ) : ℝ)) / (N + 1)| ≤ Dm := fun τ => hDm ▸
    Finset.single_le_sum (f := fun τ : Fin 2 → PerceptronSpin N =>
      |q - ((∑ i, (((τ 0).1 i : ℤ) : ℝ) * (((τ 1).1 i : ℤ) : ℝ)) +
        (((τ 0).2 : ℤ) : ℝ) * (((τ 1).2 : ℤ) : ℝ)) / (N + 1)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ τ)
  have hroot : ∀ {x M e : ℝ}, 0 < e → 0 ≤ x → 0 ≤ M → x ≤ M ^ e → x ^ (1 / e) ≤ M := by
    intro x M e he hx hM hxM
    calc x ^ (1 / e) ≤ (M ^ e) ^ (1 / e) := Real.rpow_le_rpow hx hxM (by positivity)
      _ = M := by rw [← Real.rpow_mul hM, mul_one_div_cancel he.ne', Real.rpow_one]
  have hA0 : ∀ ω s, 0 ≤ Aa ω s := fun ω s => by
    rw [hAa]
    exact Real.rpow_nonneg (integral_nonneg fun ξ => integral_nonneg fun σ =>
      Real.rpow_nonneg (abs_nonneg _) _) _
  have hB0 : ∀ ω s, 0 ≤ Bb ω s := fun ω s => by
    rw [hBb]
    exact Real.rpow_nonneg (integral_nonneg fun ξ => integral_nonneg fun σ =>
      Real.rpow_nonneg (abs_nonneg _) _) _
  have hC0 : ∀ ω s, 0 ≤ Cc ω s := fun ω s => by
    rw [hCc]
    exact integral_nonneg fun ξ => integral_nonneg fun σ => abs_nonneg _
  have hAle : ∀ ω s, Aa ω s ≤ Fm := fun ω s => by
    rw [hAa]
    exact hroot hpp (integral_nonneg fun ξ => integral_nonneg fun σ =>
      Real.rpow_nonneg (abs_nonneg _) _) hFm0
      (integral_integral_rpow_count_tilted_le
        (Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)
        (fun ξ a => Real.log (w ω a) + Real.log (ψ s (Y s ξ a))) (fun σ => |f ω σ|) hpp.le
        (fun _ => abs_nonneg _) (hfb ω))
  have hBle : ∀ ω s, Bb ω s ≤ Dm := fun ω s => by
    rw [hBb]
    exact hroot hrr (integral_nonneg fun ξ => integral_nonneg fun σ =>
      Real.rpow_nonneg (abs_nonneg _) _) hDm0
      (integral_integral_rpow_count_tilted_le
        (Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)
        (fun ξ a => Real.log (w ω a) + Real.log (ψ s (Y s ξ a)))
        (fun τ : Fin 2 → PerceptronSpin N => |q - ((∑ i, (((τ 0).1 i : ℤ) : ℝ) *
          (((τ 1).1 i : ℤ) : ℝ)) + (((τ 0).2 : ℤ) : ℝ) * (((τ 1).2 : ℤ) : ℝ)) / (N + 1)|)
        hrr.le (fun _ => abs_nonneg _) hdle)
  have hCle : ∀ ω s, Cc ω s ≤ Fm := fun ω s => by
    have := integral_integral_rpow_count_tilted_le
      (Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)
      (fun ξ a => Real.log (w ω a) + Real.log (ψ s (Y s ξ a))) (fun σ => |f ω σ|)
      (p := 1) zero_le_one (fun _ => abs_nonneg _) (hfb ω)
    simpa [hCc] using this
  have hderiv : ∀ ω s, HasDerivAt (Gm ω) (deriv (Gm ω) s) s := fun ω s => by
    obtain ⟨g', hg', _⟩ := hang ω s
    rw [hg'.deriv]
    exact hg'
  have hdb : ∀ ω s, |deriv (Gm ω) s| ≤ 1 / 2 *
      ((4 * (Fintype.card R : ℝ) ^ 2 + Fintype.card R) *
        ((Real.exp (D + B) * D₁) ^ 2 * (Aa ω s * Bb ω s) +
          (Real.exp (D + B) * D₁) ^ 2 / (N + 1) * Cc ω s)) := fun ω s => by
    obtain ⟨g', hg', hb⟩ := hang ω s
    rw [hg'.deriv]
    exact hb
  have hdM : ∀ ω s, |deriv (Gm ω) s| ≤ 1 / 2 *
      ((4 * (Fintype.card R : ℝ) ^ 2 + Fintype.card R) *
        ((Real.exp (D + B) * D₁) ^ 2 * (Fm * Dm) +
          (Real.exp (D + B) * D₁) ^ 2 / (N + 1) * Fm)) := fun ω s => by
    refine (hdb ω s).trans ?_
    have := hA0 ω s
    have := hB0 ω s
    have := hC0 ω s
    have := hAle ω s
    have := hBle ω s
    have := hCle ω s
    gcongr
  have hdom := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := P₀)
    (F := fun s ω => Gm ω s) (x₀ := t) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun s => (hGint s).aestronglyMeasurable) (hGint t)
    (F' := fun s ω => deriv (Gm ω) s)
    (aestronglyMeasurable_of_hasDerivAt_param (fun ω => hderiv ω t)
      fun s => (hGint s).aestronglyMeasurable)
    (bound := fun _ => 1 / 2 * ((4 * (Fintype.card R : ℝ) ^ 2 + Fintype.card R) *
        ((Real.exp (D + B) * D₁) ^ 2 * (Fm * Dm) +
          (Real.exp (D + B) * D₁) ^ 2 / (N + 1) * Fm)))
    (ae_of_all _ fun ω s _ => by simpa using hdM ω s) (integrable_const _)
    (ae_of_all _ fun ω s _ => hderiv ω s)
  refine ⟨∫ ω, deriv (Gm ω) t ∂P₀, ?_, ?_⟩
  · have : (fun s => ∫ ω, ∫ ξ, F ω ((Real.cos s * a₀, Real.sin s * Real.sqrt (1 - q)),
        fun σ => Real.cos s * ((Sum.elim (cavityCoef N p σ) (fun _ : Unit => (0 : ℝ)) :
          (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) + Real.sin s * ((Sum.elim
          (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
          (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ))
        ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) ∂P₀) =
        fun s => ∫ ω, Gm ω s ∂P₀ :=
      funext fun s => integral_congr_ae (ae_of_all _ fun ω => (hGm ω s).symm)
    rw [this]
    exact hdom.2
  have hEmt := hEm t
  have hIa : ∀ ω, Aa ω t ^ pp = ∫ ξ, ∫ σ : R → PerceptronSpin N, |f ω σ| ^ pp
      ∂(Measure.pi fun _ : R => Measure.count.tilted
        (fun a => Real.log (w ω a) + Real.log (ψ t (Y t ξ a))))
      ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) := fun ω => by
    rw [hAa, ← Real.rpow_mul (integral_nonneg fun ξ => integral_nonneg fun σ =>
      Real.rpow_nonneg (abs_nonneg _) _), one_div_mul_cancel hpp.ne', Real.rpow_one]
  have hIb : ∀ ω, Bb ω t ^ rr = ∫ ξ, ∫ τ : Fin 2 → PerceptronSpin N,
      |q - ((∑ i, (((τ 0).1 i : ℤ) : ℝ) * (((τ 1).1 i : ℤ) : ℝ)) +
        (((τ 0).2 : ℤ) : ℝ) * (((τ 1).2 : ℤ) : ℝ)) / (N + 1)| ^ rr
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted
        (fun a => Real.log (w ω a) + Real.log (ψ t (Y t ξ a))))
      ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) := fun ω => by
    rw [hBb, ← Real.rpow_mul (integral_nonneg fun ξ => integral_nonneg fun σ =>
      Real.rpow_nonneg (abs_nonneg _) _), one_div_mul_cancel hrr.ne', Real.rpow_one]
  have hIam := (integrable_integral_integral_count_tilted P₀
    (Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)
    (fun ω ξ a => Real.log (w ω a) + Real.log (ψ t (Y t ξ a))) hEmt
    (fun ω σ => |f ω σ| ^ pp)
    (fun σ => (continuous_abs.measurable.comp (hfm σ)).pow_const pp) (C := Fm ^ pp)
    (fun ω σ => by
      rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact Real.rpow_le_rpow (abs_nonneg _) (hfb ω σ) hpp.le)).aestronglyMeasurable
  have hIbm := (integrable_integral_integral_count_tilted P₀
    (Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)
    (fun ω ξ a => Real.log (w ω a) + Real.log (ψ t (Y t ξ a))) hEmt
    (fun (_ : Ω₀) (τ : Fin 2 → PerceptronSpin N) => |q - ((∑ i, (((τ 0).1 i : ℤ) : ℝ) *
      (((τ 1).1 i : ℤ) : ℝ)) + (((τ 0).2 : ℤ) : ℝ) * (((τ 1).2 : ℤ) : ℝ)) / (N + 1)| ^ rr)
    (fun _ => measurable_const) (C := Dm ^ rr) (fun _ τ => by
      rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      exact Real.rpow_le_rpow (abs_nonneg _) (hdle τ) hrr.le)).aestronglyMeasurable
  have hCint : Integrable (fun ω => Cc ω t) P₀ := by
    have := integrable_integral_integral_count_tilted P₀
      (Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)
      (fun ω ξ a => Real.log (w ω a) + Real.log (ψ t (Y t ξ a))) hEmt
      (fun ω σ => |f ω σ|) (fun σ => continuous_abs.measurable.comp (hfm σ)) (C := Fm)
      fun ω σ => by rw [abs_abs]; exact hfb ω σ
    exact this.congr (ae_of_all _ fun ω => by simp only [hCc])
  have hAm : AEStronglyMeasurable (fun ω => Aa ω t) P₀ := by
    simp only [hAa]
    exact (hIam.aemeasurable.pow_const _).aestronglyMeasurable
  have hBm : AEStronglyMeasurable (fun ω => Bb ω t) P₀ := by
    simp only [hBb]
    exact (hIbm.aemeasurable.pow_const _).aestronglyMeasurable
  have hABint : Integrable (fun ω => Aa ω t * Bb ω t) P₀ :=
    Integrable.of_bound (C := Fm * Dm) (hAm.mul hBm) (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (mul_nonneg (hA0 ω t) (hB0 ω t))]
      exact mul_le_mul (hAle ω t) (hBle ω t) (hB0 ω t) hFm0)
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := P₀) hpr (f := fun ω => Aa ω t)
    (g := fun ω => Bb ω t) (ae_of_all _ fun ω => hA0 ω t) (ae_of_all _ fun ω => hB0 ω t)
    (MemLp.of_bound hAm Fm (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (hA0 ω t)]; exact hAle ω t))
    (MemLp.of_bound hBm Dm (ae_of_all _ fun ω => by
      rw [Real.norm_of_nonneg (hB0 ω t)]; exact hBle ω t))
  simp only [hIa, hIb] at hH
  have hCeq : ∫ ω, Cc ω t ∂P₀ = ∫ ω, ∫ ξ, ∫ σ : R → PerceptronSpin N, |f ω σ|
      ∂(Measure.pi fun _ : R => Measure.count.tilted
        (fun a => Real.log (w ω a) + Real.log (ψ t (Y t ξ a))))
      ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) ∂P₀ :=
    integral_congr_ae (ae_of_all _ fun ω => by simp only [hCc])
  rw [← hCeq]
  calc |∫ ω, deriv (Gm ω) t ∂P₀| ≤ ∫ ω, |deriv (Gm ω) t| ∂P₀ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, 1 / 2 * ((4 * (Fintype.card R : ℝ) ^ 2 + Fintype.card R) *
        ((Real.exp (D + B) * D₁) ^ 2 * (Aa ω t * Bb ω t) +
          (Real.exp (D + B) * D₁) ^ 2 / (N + 1) * Cc ω t)) ∂P₀ :=
        integral_mono hdom.1.abs (((hABint.const_mul _).add (hCint.const_mul _)).const_mul _
          |>.const_mul _) fun ω => hdb ω t
    _ = 1 / 2 * ((4 * (Fintype.card R : ℝ) ^ 2 + Fintype.card R) *
        ((Real.exp (D + B) * D₁) ^ 2 * ∫ ω, Aa ω t * Bb ω t ∂P₀ +
          (Real.exp (D + B) * D₁) ^ 2 / (N + 1) * ∫ ω, Cc ω t ∂P₀)) := by
        rw [integral_const_mul, integral_const_mul,
          integral_add (hABint.const_mul _) (hCint.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ _ := by
        have : 0 ≤ (4 * (Fintype.card R : ℝ) ^ 2 + Fintype.card R) := by positivity
        gcongr

end SpinGlasses
