/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityOldDisorder

/-!
# Increments of the averaged cavity system across angles

Talagrand Section 2.3, the mean-value step (2.63) of Proposition 2.3.5 for `B_v ≡ 1`. The
derivative bound (2.40) holds at every angle with the Gibbs averages taken at that angle; two
angles differ in the site energies by at most `B + D`, so (2.61) (the comparison
`integral_integral_integral_count_tilted_le_exp_mul`) replaces every average by the one at a fixed
reference angle `s₀` at the price of a constant depending on `n`, `B`, `D` only. The mean value
theorem then bounds the increment of `s ↦ 𝔼_ω 𝔼_ξ ⟨f⟩_{p,s}` between any two angles.

* `SpinGlasses.abs_integral_integral_cavityRatio_sub_le`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

variable {N : ℕ} {R : Type*} [Fintype R] [DecidableEq R]

/-- **Increments of the averaged cavity system across angles.** Under the hypotheses of
`exists_hasDerivAt_integral_abs_le_cavityRatio`, for every reference angle `s₀` and all angles
`s₁, s₂`, the increment `|Φ s₂ - Φ s₁|` of `Φ s = 𝔼_ω 𝔼_ξ F_ω(τ s, cos s X + sin s Y)` is at most
`|s₂ - s₁|` times
`(1/2)(4n² + n) D'² (e^{2n(B+D)/p + 4(B+D)/r} (𝔼⟨|f|^p⟩)^{1/p} (𝔼⟨|R₁₂ - q|^r⟩)^{1/r} +
e^{2n(B+D)} 𝔼⟨|f|⟩/(N+1))`, all averages at the angle `s₀`. -/
theorem abs_integral_integral_cavityRatio_sub_le {Ω₀ : Type*} [MeasurableSpace Ω₀]
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
        (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ)) {pp rr : ℝ} (hpr : pp.HolderConjugate rr)
    (Φ : ℝ → ℝ)
    (hΦ : ∀ s, Φ s = ∫ ω, ∫ ξ, F ω ((Real.cos s * a₀, Real.sin s * Real.sqrt (1 - q)),
        fun σ => Real.cos s * ((Sum.elim (cavityCoef N p σ) (fun _ : Unit => (0 : ℝ)) :
          (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) + Real.sin s * ((Sum.elim
          (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
          (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ))
        ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) ∂P₀)
    (s₀ s₁ s₂ : ℝ) :
    |Φ s₂ - Φ s₁| ≤ |s₂ - s₁| * (1 / 2 * ((4 * (Fintype.card R : ℝ) ^ 2 + Fintype.card R) *
        ((Real.exp (D + B) * D₁) ^ 2 * (Real.exp (2 * Fintype.card R * (B + D) / pp +
            4 * (B + D) / rr) *
          ((∫ ω, ∫ ξ, ∫ σ : R → PerceptronSpin N, |f ω σ| ^ pp
            ∂(Measure.pi fun _ : R => Measure.count.tilted
              (fun a => Real.log (w ω a) + Real.log (ψ s₀ (Y s₀ ξ a))))
            ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) ∂P₀) ^ (1 / pp) *
          (∫ ω, ∫ ξ, ∫ τ : Fin 2 → PerceptronSpin N,
            |q - ((∑ i, (((τ 0).1 i : ℤ) : ℝ) * (((τ 1).1 i : ℤ) : ℝ)) +
              (((τ 0).2 : ℤ) : ℝ) * (((τ 1).2 : ℤ) : ℝ)) / (N + 1)| ^ rr
            ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted
              (fun a => Real.log (w ω a) + Real.log (ψ s₀ (Y s₀ ξ a))))
            ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) ∂P₀) ^ (1 / rr))) +
        (Real.exp (D + B) * D₁) ^ 2 / (N + 1) * (Real.exp (2 * Fintype.card R * (B + D)) *
          ∫ ω, ∫ ξ, ∫ σ : R → PerceptronSpin N, |f ω σ|
            ∂(Measure.pi fun _ : R => Measure.count.tilted
              (fun a => Real.log (w ω a) + Real.log (ψ s₀ (Y s₀ ξ a))))
            ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) ∂P₀)))) := by
  classical
  have hpp : 0 < pp := hpr.pos
  have hrr : 0 < rr := hpr.symm.pos
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
  have hEdiff : ∀ s ω ξ a, |(Real.log (w ω a) + Real.log (ψ s (Y s ξ a))) -
      (Real.log (w ω a) + Real.log (ψ s₀ (Y s₀ ξ a)))| ≤ B + D := fun s ω ξ a => by
    rw [add_sub_add_left_eq_sub, hψ s, hψ s₀]
    exact abs_log_integral_exp_comp_gaussian_sub_le hu.continuous hB hD _ _ _ _ _ _
  obtain ⟨IA, hIA⟩ : ∃ IA : ℝ → ℝ, ∀ s, IA s = ∫ ω, ∫ ξ, ∫ σ : R → PerceptronSpin N,
      |f ω σ| ^ pp ∂(Measure.pi fun _ : R => Measure.count.tilted
        (fun a => Real.log (w ω a) + Real.log (ψ s (Y s ξ a))))
      ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) ∂P₀ := ⟨_, fun _ => rfl⟩
  obtain ⟨IB, hIB⟩ : ∃ IB : ℝ → ℝ, ∀ s, IB s = ∫ ω, ∫ ξ, ∫ τ : Fin 2 → PerceptronSpin N,
      |q - ((∑ i, (((τ 0).1 i : ℤ) : ℝ) * (((τ 1).1 i : ℤ) : ℝ)) +
        (((τ 0).2 : ℤ) : ℝ) * (((τ 1).2 : ℤ) : ℝ)) / (N + 1)| ^ rr
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted
        (fun a => Real.log (w ω a) + Real.log (ψ s (Y s ξ a))))
      ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) ∂P₀ := ⟨_, fun _ => rfl⟩
  obtain ⟨IC, hIC⟩ : ∃ IC : ℝ → ℝ, ∀ s, IC s = ∫ ω, ∫ ξ, ∫ σ : R → PerceptronSpin N, |f ω σ|
      ∂(Measure.pi fun _ : R => Measure.count.tilted
        (fun a => Real.log (w ω a) + Real.log (ψ s (Y s ξ a))))
      ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) ∂P₀ := ⟨_, fun _ => rfl⟩
  have hIA0 : ∀ s, 0 ≤ IA s := fun s => by
    rw [hIA]
    exact integral_nonneg fun ω => integral_nonneg fun ξ => integral_nonneg fun σ =>
      Real.rpow_nonneg (abs_nonneg _) _
  have hIB0 : ∀ s, 0 ≤ IB s := fun s => by
    rw [hIB]
    exact integral_nonneg fun ω => integral_nonneg fun ξ => integral_nonneg fun σ =>
      Real.rpow_nonneg (abs_nonneg _) _
  have hIC0 : ∀ s, 0 ≤ IC s := fun s => by
    rw [hIC]
    exact integral_nonneg fun ω => integral_nonneg fun ξ => integral_nonneg fun σ => abs_nonneg _
  have hIAle : ∀ s, IA s ≤ Real.exp (2 * Fintype.card R * (B + D)) * IA s₀ := fun s => by
    rw [hIA, hIA]
    exact integral_integral_integral_count_tilted_le_exp_mul P₀
      (Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)
      (fun ω ξ a => Real.log (w ω a) + Real.log (ψ s₀ (Y s₀ ξ a)))
      (fun ω ξ a => Real.log (w ω a) + Real.log (ψ s (Y s ξ a))) (hEm s₀) (hEm s)
      (hEdiff s) (fun ω σ => |f ω σ| ^ pp)
      (fun σ => (continuous_abs.measurable.comp (hfm σ)).pow_const pp)
      (fun ω σ => Real.rpow_nonneg (abs_nonneg _) _) (M := Fm ^ pp)
      (fun ω σ => Real.rpow_le_rpow (abs_nonneg _) (hfb ω σ) hpp.le)
  have hIBle : ∀ s, IB s ≤ Real.exp (4 * (B + D)) * IB s₀ := fun s => by
    have := integral_integral_integral_count_tilted_le_exp_mul (R := Fin 2) P₀
      (Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)
      (fun ω ξ a => Real.log (w ω a) + Real.log (ψ s₀ (Y s₀ ξ a)))
      (fun ω ξ a => Real.log (w ω a) + Real.log (ψ s (Y s ξ a))) (hEm s₀) (hEm s)
      (hEdiff s) (fun (_ : Ω₀) (τ : Fin 2 → PerceptronSpin N) => |q - ((∑ i,
        (((τ 0).1 i : ℤ) : ℝ) * (((τ 1).1 i : ℤ) : ℝ)) + (((τ 0).2 : ℤ) : ℝ) *
        (((τ 1).2 : ℤ) : ℝ)) / (N + 1)| ^ rr) (fun _ => measurable_const)
      (fun ω σ => Real.rpow_nonneg (abs_nonneg _) _) (M := Dm ^ rr)
      (fun ω τ => Real.rpow_le_rpow (abs_nonneg _) (hdle τ) hrr.le)
    have e : Real.exp (2 * (Fintype.card (Fin 2) : ℝ) * (B + D)) = Real.exp (4 * (B + D)) := by
      congr 1
      simp only [Fintype.card_fin]
      push_cast
      ring
    rw [hIB, hIB, ← e]
    exact this
  have hIClex : ∀ s, IC s ≤ Real.exp (2 * Fintype.card R * (B + D)) * IC s₀ := fun s => by
    rw [hIC, hIC]
    exact integral_integral_integral_count_tilted_le_exp_mul P₀
      (Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1)
      (fun ω ξ a => Real.log (w ω a) + Real.log (ψ s₀ (Y s₀ ξ a)))
      (fun ω ξ a => Real.log (w ω a) + Real.log (ψ s (Y s ξ a))) (hEm s₀) (hEm s)
      (hEdiff s) (fun ω σ => |f ω σ|)
      (fun σ => continuous_abs.measurable.comp (hfm σ)) (fun ω σ => abs_nonneg _)
      (M := Fm) (fun ω σ => hfb ω σ)
  have hd : ∀ s, ∃ g', HasDerivAt Φ g' s ∧ |g'| ≤ 1 / 2 *
      ((4 * (Fintype.card R : ℝ) ^ 2 + Fintype.card R) *
        ((Real.exp (D + B) * D₁) ^ 2 * (IA s ^ (1 / pp) * IB s ^ (1 / rr)) +
          (Real.exp (D + B) * D₁) ^ 2 / (N + 1) * IC s)) := fun s => by
    obtain ⟨g', hg', hb⟩ := exists_hasDerivAt_integral_abs_le_cavityRatio P₀ hu hB hD hD₁ hD₂ hq
      hw hwm f hfm hfb a₀ p hp ha₀ F hF ψ hψ Y hYd hpr s
    refine ⟨g', ?_, ?_⟩
    · have : Φ = fun s => ∫ ω, ∫ ξ, F ω ((Real.cos s * a₀, Real.sin s * Real.sqrt (1 - q)),
          fun σ => Real.cos s * ((Sum.elim (cavityCoef N p σ) (fun _ : Unit => (0 : ℝ)) :
            (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ) + Real.sin s * ((Sum.elim
            (fun _ : Fin N ⊕ Unit => (0 : ℝ)) (fun _ : Unit => Real.sqrt q) :
            (Fin N ⊕ Unit) ⊕ Unit → ℝ) ⬝ᵥ ξ))
          ∂(Measure.pi fun _ : (Fin N ⊕ Unit) ⊕ Unit => gaussianReal 0 1) ∂P₀ := funext hΦ
      rw [this]
      exact hg'
    · rw [hIA, hIB, hIC]
      exact hb
  have hderiv : ∀ s, HasDerivAt Φ (deriv Φ s) s := fun s => by
    obtain ⟨g', hg', _⟩ := hd s
    rw [hg'.deriv]
    exact hg'
  have hroot : ∀ {x y e c : ℝ}, 0 < e → 0 ≤ x → x ≤ Real.exp c * y →
      x ^ (1 / e) ≤ Real.exp (c / e) * y ^ (1 / e) := by
    intro x y e c he hx hxy
    have hy : 0 ≤ y := by
      by_contra hneg
      have : Real.exp c * y < 0 := mul_neg_of_pos_of_neg (Real.exp_pos _) (not_le.1 hneg)
      linarith
    calc x ^ (1 / e) ≤ (Real.exp c * y) ^ (1 / e) := Real.rpow_le_rpow hx hxy (by positivity)
      _ = Real.exp (c / e) * y ^ (1 / e) := by
        rw [Real.mul_rpow (Real.exp_pos _).le hy, ← Real.exp_mul]
        congr 2
        ring
  have hAle : ∀ s, IA s ^ (1 / pp) ≤ Real.exp (2 * Fintype.card R * (B + D) / pp) *
      IA s₀ ^ (1 / pp) := fun s => hroot hpp (hIA0 s) (hIAle s)
  have hBle : ∀ s, IB s ^ (1 / rr) ≤ Real.exp (4 * (B + D) / rr) * IB s₀ ^ (1 / rr) :=
    fun s => hroot hrr (hIB0 s) (hIBle s)
  have hbd : ∀ s, |deriv Φ s| ≤ 1 / 2 * ((4 * (Fintype.card R : ℝ) ^ 2 + Fintype.card R) *
        ((Real.exp (D + B) * D₁) ^ 2 * (Real.exp (2 * Fintype.card R * (B + D) / pp +
            4 * (B + D) / rr) * (IA s₀ ^ (1 / pp) * IB s₀ ^ (1 / rr))) +
        (Real.exp (D + B) * D₁) ^ 2 / (N + 1) *
          (Real.exp (2 * Fintype.card R * (B + D)) * IC s₀))) := fun s => by
    obtain ⟨g', hg', hb⟩ := hd s
    rw [hg'.deriv]
    refine hb.trans ?_
    have h1 := hAle s
    have h2 := hBle s
    have h3 := hIClex s
    have h4 : 0 ≤ IA s ^ (1 / pp) := Real.rpow_nonneg (hIA0 s) _
    have h5 : 0 ≤ IB s ^ (1 / rr) := Real.rpow_nonneg (hIB0 s) _
    have h6 : 0 ≤ Real.exp (2 * Fintype.card R * (B + D) / pp) * IA s₀ ^ (1 / pp) := by
      have := Real.rpow_nonneg (hIA0 s₀) (1 / pp)
      positivity
    have e : Real.exp (2 * Fintype.card R * (B + D) / pp + 4 * (B + D) / rr) *
        (IA s₀ ^ (1 / pp) * IB s₀ ^ (1 / rr)) =
        (Real.exp (2 * Fintype.card R * (B + D) / pp) * IA s₀ ^ (1 / pp)) *
          (Real.exp (4 * (B + D) / rr) * IB s₀ ^ (1 / rr)) := by
      rw [Real.exp_add]
      ring
    rw [e]
    have : 0 ≤ (4 * (Fintype.card R : ℝ) ^ 2 + Fintype.card R) := by positivity
    gcongr
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Φ) (f' := deriv Φ)
    (s := Set.univ) (x := s₁) (y := s₂)
    (fun x _ => (hderiv x).hasDerivWithinAt) (fun x _ => by simpa using hbd x) convex_univ
    (Set.mem_univ _) (Set.mem_univ _)
  rw [hIA, hIB, hIC] at hmv
  simpa [Real.norm_eq_abs, mul_comm] using hmv

end SpinGlasses
