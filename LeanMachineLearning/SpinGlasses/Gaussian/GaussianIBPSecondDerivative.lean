/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Gaussian.GaussianInterpolationReplica

/-!
# Second derivative of a finite replica average in the energy

For a finite spin set `α` and `n = |R|` replicas, the derivative of
`⟨Ψ⟩ = ∫ Ψ d(count.tilted f)^{⊗R}` in the energy direction `e_ρ` is `⟨(N_ρ - n G_ρ) Ψ⟩` with
`N_ρ = ∑_r 1[σ_r = ρ]` and `G_ρ` the Gibbs weight of `ρ` (`fderiv_integral_pi_count_tilted`).
Differentiating once more in the direction `e_{ρ'}` gives
`⟨Ψ [(N_ρ - n G_ρ)(N_{ρ'} - n G_{ρ'}) - n G_ρ (1[ρ = ρ'] - G_{ρ'})]⟩`. In Talagrand's cavity in
`M` (Section 2.3) these are the replica sums with the two extra replicas `n + 1, n + 2` of
(2.55)--(2.58).

* `SpinGlasses.hasDerivAt_integral_pi_count_tilted_single_path`: along any smooth energy path;
* `SpinGlasses.hasDerivAt_integral_pi_count_tilted_single_single`: the straight path `f + ε e_{ρ'}`;
* `SpinGlasses.hasDerivAt_integral_pi_count_tilted_site`,
  `SpinGlasses.hasDerivAt_integral_pi_count_tilted_site_site`: the first and second derivative in a
  single site variable `y_c` of the replica average with site energies `h a + L (y a)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

variable {α R : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **Derivative of the energy-derivative along a smooth energy path.** If `f s a` has derivative
`f' a` at `0`, the first derivative `⟨(N_ρ - n G_ρ) Ψ⟩_{f s}` has derivative
`⟨Ψ [(N_ρ - n G_ρ)(∑_r f'(σ_r) - n ⟨f'⟩) - n G_ρ (f'(ρ) - ⟨f'⟩)]⟩` at `s = 0`, where
`⟨f'⟩ = ∑_a G_a f'(a)` is the Gibbs average of `f'`. -/
theorem hasDerivAt_integral_pi_count_tilted_single_path [Finite α] [Nonempty α]
    [DecidableEq α] [Fintype R] (Ψ : (R → α) → ℝ) (f : ℝ → α → ℝ) (f' : α → ℝ)
    (hf : ∀ a, HasDerivAt (fun s => f s a) (f' a) 0) (ρ : α) :
    HasDerivAt (fun s : ℝ => ∫ σ, ((∑ r, if σ r = ρ then (1 : ℝ) else 0) -
        Fintype.card R * (Measure.count.tilted (f s)).real {ρ}) * Ψ σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (f s)))
      (∫ σ, (((∑ r, if σ r = ρ then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted (f 0)).real {ρ}) *
        (∑ r, f' (σ r) - Fintype.card R * ∫ τ, f' τ ∂(Measure.count.tilted (f 0))) -
        Fintype.card R * (Measure.count.tilted (f 0)).real {ρ} *
          (f' ρ - ∫ τ, f' τ ∂(Measure.count.tilted (f 0)))) * Ψ σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (f 0))) 0 := by
  have := Fintype.ofFinite α
  have hW : ∀ g : α → ℝ, (Measure.count.tilted g).real {ρ} =
      Real.exp (g ρ) / ∑ b, Real.exp (g b) := fun g => real_count_tilted_singleton g ρ
  have hZ : 0 < ∑ b, Real.exp (f 0 b) := Finset.sum_pos (fun _ _ => Real.exp_pos _)
    Finset.univ_nonempty
  have hnum : HasDerivAt (fun s : ℝ => Real.exp (f s ρ))
      (Real.exp (f 0 ρ) * f' ρ) 0 := (hf ρ).exp
  have hden : HasDerivAt (fun s : ℝ => ∑ b, Real.exp (f s b))
      (∑ b, Real.exp (f 0 b) * f' b) 0 :=
    HasDerivAt.fun_sum fun b _ => (hf b).exp
  have hmean : ∫ τ, f' τ ∂(Measure.count.tilted (f 0)) =
      (∑ b, Real.exp (f 0 b) * f' b) / ∑ b, Real.exp (f 0 b) := by
    rw [integral_count_tilted, Finset.sum_div]
    exact Finset.sum_congr rfl fun b _ => by ring
  have hG : HasDerivAt (fun s : ℝ => Real.exp (f s ρ) / ∑ b, Real.exp (f s b))
      ((Real.exp (f 0 ρ) / ∑ b, Real.exp (f 0 b)) *
        (f' ρ - ∫ τ, f' τ ∂(Measure.count.tilted (f 0)))) 0 := by
    refine (hnum.div hden hZ.ne').congr_deriv ?_
    rw [hmean]
    field_simp
  have key := hasDerivAt_integral_pi_count_tilted_path_moving (R := R)
    (fun s σ => ((∑ r, if σ r = ρ then (1 : ℝ) else 0) -
      Fintype.card R * (Real.exp (f s ρ) / ∑ b, Real.exp (f s b))) * Ψ σ)
    (fun σ => -(Fintype.card R * ((Real.exp (f 0 ρ) / ∑ b, Real.exp (f 0 b)) *
      (f' ρ - ∫ τ, f' τ ∂(Measure.count.tilted (f 0))))) * Ψ σ)
    f f' 0 (fun σ => by
      have := ((hG.const_mul (Fintype.card R : ℝ)).const_sub
        (∑ r, if σ r = ρ then (1 : ℝ) else 0)).mul_const (Ψ σ)
      simpa [neg_mul] using this) hf
  simp only [hW]
  refine key.congr_deriv ?_
  rw [← integral_add Integrable.of_finite Integrable.of_finite]
  refine integral_congr_ae (ae_of_all _ fun σ => ?_)
  simp only
  ring

/-- **Hessian of a finite replica average in the energy.** Along `f + ε e_{ρ'}` the first
derivative `⟨(N_ρ - n G_ρ) Ψ⟩` has derivative
`⟨Ψ [(N_ρ - n G_ρ)(N_{ρ'} - n G_{ρ'}) - n G_ρ (1[ρ = ρ'] - G_{ρ'})]⟩` at `ε = 0`. -/
theorem hasDerivAt_integral_pi_count_tilted_single_single [Finite α] [Nonempty α]
    [DecidableEq α] [Fintype R] (Ψ : (R → α) → ℝ) (f : α → ℝ) (ρ ρ' : α) :
    HasDerivAt (fun ε : ℝ => ∫ σ, ((∑ r, if σ r = ρ then (1 : ℝ) else 0) -
        Fintype.card R * (Measure.count.tilted (fun a => f a + ε * if a = ρ' then 1 else 0)).real
          {ρ}) * Ψ σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun a => f a + ε * if a = ρ' then 1 else 0)))
      (∫ σ, (((∑ r, if σ r = ρ then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted f).real {ρ}) *
        ((∑ r, if σ r = ρ' then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted f).real {ρ'}) -
        Fintype.card R * (Measure.count.tilted f).real {ρ} *
          ((if ρ = ρ' then 1 else 0) - (Measure.count.tilted f).real {ρ'})) * Ψ σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted f)) 0 := by
  have hfd : ∀ a, HasDerivAt (fun s : ℝ => f a + s * if a = ρ' then (1 : ℝ) else 0)
      (if a = ρ' then (1 : ℝ) else 0) 0 := fun a => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (if a = ρ' then (1 : ℝ) else 0)).const_add (f a)
  have hind : ∫ τ, (if τ = ρ' then (1 : ℝ) else 0) ∂(Measure.count.tilted f) =
      (Measure.count.tilted f).real {ρ'} := by
    simpa [Set.indicator] using integral_indicator_one (μ := Measure.count.tilted f)
      (measurableSet_singleton ρ')
  have key := hasDerivAt_integral_pi_count_tilted_single_path Ψ
    (fun s a => f a + s * if a = ρ' then (1 : ℝ) else 0) (fun a => if a = ρ' then 1 else 0)
    hfd ρ
  simpa only [zero_mul, add_zero, hind] using key

/-- **First derivative in a site variable.** For the site energies `E a = h a + L (y a)`, moving
the single coordinate `y_c` has derivative `L'(y_c) ⟨(N_c - n G_c) Ψ⟩` at `0`. -/
theorem hasDerivAt_integral_pi_count_tilted_site [Finite α] [Nonempty α]
    [DecidableEq α] [Fintype R] (Ψ : (R → α) → ℝ) (h : α → ℝ) {L L' : ℝ → ℝ}
    (hL : ∀ x, HasDerivAt L (L' x) x) (y : α → ℝ) (c : α) :
    HasDerivAt (fun ε : ℝ => ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted
        (fun a => h a + L (y a + ε * if a = c then 1 else 0))))
      (L' (y c) * ∫ σ, ((∑ r, if σ r = c then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted (fun a => h a + L (y a))).real {c}) * Ψ σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (fun a => h a + L (y a)))) 0 := by
  have := Fintype.ofFinite α
  have hf : ∀ a, HasDerivAt (fun ε : ℝ => h a + L (y a + ε * if a = c then 1 else 0))
      (if a = c then L' (y c) else 0) 0 := fun a => by
    by_cases hac : a = c
    · subst hac
      have := (hL (y a + 0 * 1)).comp (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).mul_const (1 : ℝ)).const_add
        (y a))
      simpa using this.const_add (h a)
    · simpa [hac] using hasDerivAt_const (0 : ℝ) (h a + L (y a))
  have key := hasDerivAt_integral_pi_count_tilted_path (R := R) Ψ
    (fun ε a => h a + L (y a + ε * if a = c then 1 else 0)) (fun a => if a = c then L' (y c) else 0)
    0 hf
  refine key.congr_deriv ?_
  have hite : ∀ τ : α, (if τ = c then L' (y c) else 0) = L' (y c) * if τ = c then (1 : ℝ) else 0 :=
    fun τ => by split_ifs <;> simp
  have hmean : ∫ τ, (if τ = c then L' (y c) else 0) ∂(Measure.count.tilted
      (fun a => h a + L (y a + (0 : ℝ) * if a = c then 1 else 0))) =
      L' (y c) * (Measure.count.tilted (fun a => h a + L (y a))).real {c} := by
    simp only [zero_mul, add_zero, hite]
    rw [integral_const_mul]
    congr 1
    simpa [Set.indicator] using integral_indicator_one
      (μ := Measure.count.tilted (fun a => h a + L (y a))) (measurableSet_singleton c)
  simp only [zero_mul, add_zero] at hmean ⊢
  rw [hmean, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun σ => ?_)
  simp only [hite, ← Finset.mul_sum]
  ring

/-- **Second derivative in two site variables.** For the site energies `E a = h a + L (y a)`, the
derivative `L'(y_b) ⟨(N_b - n G_b) Ψ⟩` in the site `b`, differentiated by moving `y_c`, is
`1[b = c] L''(y_b) ⟨(N_b - n G_b) Ψ⟩
  + L'(y_b) L'(y_c) ⟨Ψ [(N_b - n G_b)(N_c - n G_c) - n G_b (1[b = c] - G_c)]⟩`. -/
theorem hasDerivAt_integral_pi_count_tilted_site_site [Finite α] [Nonempty α]
    [DecidableEq α] [Fintype R] (Ψ : (R → α) → ℝ) (h : α → ℝ) {L L' L'' : ℝ → ℝ}
    (hL : ∀ x, HasDerivAt L (L' x) x) (hL' : ∀ x, HasDerivAt L' (L'' x) x) (y : α → ℝ)
    (b c : α) :
    HasDerivAt (fun ε : ℝ => L' (y b + ε * if b = c then 1 else 0) *
        ∫ σ, ((∑ r, if σ r = b then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted
            (fun a => h a + L (y a + ε * if a = c then 1 else 0))).real {b}) * Ψ σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun a => h a + L (y a + ε * if a = c then 1 else 0))))
      ((if b = c then L'' (y b) else 0) * ∫ σ, ((∑ r, if σ r = b then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted (fun a => h a + L (y a))).real {b}) * Ψ σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (fun a => h a + L (y a))) +
        L' (y b) * L' (y c) * ∫ σ, (((∑ r, if σ r = b then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted (fun a => h a + L (y a))).real {b}) *
        ((∑ r, if σ r = c then (1 : ℝ) else 0) -
          Fintype.card R * (Measure.count.tilted (fun a => h a + L (y a))).real {c}) -
        Fintype.card R * (Measure.count.tilted (fun a => h a + L (y a))).real {b} *
          ((if b = c then 1 else 0) -
            (Measure.count.tilted (fun a => h a + L (y a))).real {c})) * Ψ σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (fun a => h a + L (y a)))) 0 := by
  have := Fintype.ofFinite α
  have hf : ∀ a, HasDerivAt (fun ε : ℝ => h a + L (y a + ε * if a = c then 1 else 0))
      (if a = c then L' (y c) else 0) 0 := fun a => by
    by_cases hac : a = c
    · subst hac
      have := (hL (y a + 0 * 1)).comp (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).mul_const (1 : ℝ)).const_add
        (y a))
      simpa using this.const_add (h a)
    · simpa [hac] using hasDerivAt_const (0 : ℝ) (h a + L (y a))
  have key := hasDerivAt_integral_pi_count_tilted_single_path Ψ
    (fun ε a => h a + L (y a + ε * if a = c then 1 else 0)) (fun a => if a = c then L' (y c) else 0)
    hf b
  have hl : HasDerivAt (fun ε : ℝ => L' (y b + ε * if b = c then 1 else 0))
      (if b = c then L'' (y b) else 0) 0 := by
    by_cases hbc : b = c
    · subst hbc
      simpa [Function.comp_def] using (hL' (y b + 0 * 1)).comp (0 : ℝ)
        (((hasDerivAt_id (0 : ℝ)).mul_const (1 : ℝ)).const_add (y b))
    · simpa [hbc] using hasDerivAt_const (0 : ℝ) (L' (y b))
  refine (hl.mul key).congr_deriv ?_
  have hite : ∀ τ : α, (if τ = c then L' (y c) else 0) = L' (y c) * if τ = c then (1 : ℝ) else 0 :=
    fun τ => by split_ifs <;> simp
  have hmean : ∫ τ, (if τ = c then L' (y c) else 0) ∂(Measure.count.tilted
      (fun a => h a + L (y a + (0 : ℝ) * if a = c then 1 else 0))) =
      L' (y c) * (Measure.count.tilted (fun a => h a + L (y a))).real {c} := by
    simp only [zero_mul, add_zero, hite]
    rw [integral_const_mul]
    congr 1
    simpa [Set.indicator] using integral_indicator_one
      (μ := Measure.count.tilted (fun a => h a + L (y a))) (measurableSet_singleton c)
  simp only [zero_mul, add_zero] at hmean ⊢
  rw [hmean]
  simp only [hite, ← Finset.mul_sum]
  refine (add_right_inj _).2 ?_
  rw [mul_assoc (L' (y b)) (L' (y c)), ← integral_const_mul (L' (y c))]
  refine congrArg _ (integral_congr_ae (ae_of_all _ fun σ => ?_))
  ring

end SpinGlasses
