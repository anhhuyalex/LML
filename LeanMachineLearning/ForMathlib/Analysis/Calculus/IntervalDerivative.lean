/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.Deriv

/-!
# Derivatives on closed intervals: extension, Taylor remainder and Lipschitz bounds

* `hasDerivWithinAt_Icc_of_continuous_derivative`: extends an interior derivative formula with a
  continuous derivative to `[a, b]`.
* `abs_sub_sub_deriv_zero_le_half_of_Ioo`: second-order Taylor remainder
  `|φ 1 - φ 0 - φ' 0| ≤ C / 2` from continuity of `φ, φ'` on `[0, 1]` and an interior bound
  `|φ''| ≤ C` on `(0, 1)`.
* `abs_sub_le_of_continuousOn_Icc_of_hasDerivAt_Ioo`: mean-value Lipschitz bound on `[a, b]` from
  continuity on `[a, b]` and a bounded derivative on `(a, b)`.
* `ConcaveOn.deriv_nonneg_of_forall_ge_eq`: a concave function which is constant on a half-line
  `[τ, ∞)` has a nonnegative derivative.
-/

@[expose] public section

open Filter Set
open scoped Topology

/-- A continuous interior derivative formula extends to both ends of a closed interval. -/
theorem hasDerivWithinAt_Icc_of_continuous_derivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (hab : a < b) (F G : ℝ → E)
    (hF : Continuous F) (hG : Continuous G)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt F (G x) x) :
    ∀ x ∈ Icc a b, HasDerivWithinAt F (G x) (Icc a b) x := by
  have hdiff : DifferentiableOn ℝ F (Ioo a b) :=
    fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  intro x hx
  rcases hx.1.eq_or_lt with rfl | hax
  · have heq : deriv F =ᶠ[𝓝[>] a] G := by
      filter_upwards [Ioo_mem_nhdsGT hab] with t ht
      exact (hd t ht).deriv
    have hlim : Tendsto (deriv F) (𝓝[>] a) (𝓝 (G a)) :=
      (hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm
    exact (hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hF.continuousAt.continuousWithinAt
      (Ioo_mem_nhdsGT hab) hlim).mono Icc_subset_Ici_self
  · rcases hx.2.eq_or_lt with rfl | hxb
    · have heq : deriv F =ᶠ[𝓝[<] x] G := by
        filter_upwards [Ioo_mem_nhdsLT hab] with t ht
        exact (hd t ht).deriv
      have hlim : Tendsto (deriv F) (𝓝[<] x) (𝓝 (G x)) :=
        (hG.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm
      exact (hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hF.continuousAt.continuousWithinAt
        (Ioo_mem_nhdsLT hab) hlim).mono Icc_subset_Iic_self
    · exact (hd x ⟨hax, hxb⟩).hasDerivWithinAt

/-- **Second-order Taylor remainder on `[0, 1]` from an interior second-derivative bound:**
if `φ` and `φ'` are continuous on `[0, 1]`, `HasDerivAt φ (φ' v) v` on `(0, 1)`, and `φ'` has
derivative bounded in modulus by `C` at every `v ∈ (0, 1)`, then
`|φ 1 - φ 0 - φ' 0| ≤ C / 2`. -/
theorem abs_sub_sub_deriv_zero_le_half_of_Ioo
    {φ φ' : ℝ → ℝ} {C : ℝ}
    (hφ_cont : ContinuousOn φ (Icc 0 1))
    (hφ'_cont : ContinuousOn φ' (Icc 0 1))
    (hφ_der : ∀ v ∈ Ioo (0 : ℝ) 1, HasDerivAt φ (φ' v) v)
    (hφ'_der : ∀ v ∈ Ioo (0 : ℝ) 1, ∃ d, HasDerivAt φ' d v ∧ |d| ≤ C) :
    |φ 1 - φ 0 - φ' 0| ≤ C / 2 := by
  let g (v : ℝ) : ℝ := φ v - φ 0 - v * φ' 0
  have hg_cont : ContinuousOn g (Icc 0 1) :=
    (hφ_cont.sub continuousOn_const).sub (continuousOn_id.mul continuousOn_const)
  have hg_der_oo : ∀ v ∈ Ioo (0 : ℝ) 1, HasDerivAt g (φ' v - φ' 0) v := fun v hv => by
    have h1 := (hφ_der v hv).sub_const (φ 0)
    have h2 := h1.sub ((hasDerivAt_id v).mul_const (φ' 0))
    exact h2.congr_deriv (by ring)
  have hg_right : ∀ v ∈ Ico (0 : ℝ) 1, HasDerivWithinAt g (φ' v - φ' 0) (Ici v) v := by
    intro v hv
    rcases hv.1.eq_or_lt with rfl | hv_pos
    · have hg_diff_oo : DifferentiableOn ℝ g (Ioo 0 1) :=
        fun x hx => (hg_der_oo x hx).differentiableAt.differentiableWithinAt
      have hg_cwa : ContinuousWithinAt g (Ioo 0 1) 0 :=
        (hg_cont 0 ⟨le_rfl, zero_le_one⟩).mono Ioo_subset_Icc_self
      have hderiv_eq : deriv g =ᶠ[𝓝[>] (0 : ℝ)] fun x => φ' x - φ' 0 := by
        filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
        exact (hg_der_oo x hx).deriv
      have hφ'_lim : Tendsto (fun x => φ' x - φ' 0) (𝓝[>] (0 : ℝ)) (𝓝 (φ' 0 - φ' 0)) := by
        have hc0 : ContinuousWithinAt (fun x => φ' x - φ' 0) (Icc 0 1) 0 :=
          (hφ'_cont.sub continuousOn_const) 0 ⟨le_rfl, zero_le_one⟩
        exact hc0.mono_of_mem_nhdsWithin (Icc_mem_nhdsGT zero_lt_one)
      exact hasDerivWithinAt_Ici_of_tendsto_deriv hg_diff_oo hg_cwa
        (Ioo_mem_nhdsGT zero_lt_one) (hφ'_lim.congr' hderiv_eq.symm)
    · exact (hg_der_oo v ⟨hv_pos, hv.2⟩).hasDerivWithinAt
  choose! φ'' hφ''_d hφ''_b using hφ'_der
  have hlip_φ' : ∀ v ∈ Ico (0 : ℝ) 1, ‖φ' v - φ' 0‖ ≤ C * v := by
    intro v hv
    rw [Real.norm_eq_abs]
    rcases hv.1.eq_or_lt with rfl | hv_pos
    · simp
    · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope φ' φ'' hv_pos
        (hφ'_cont.mono (Icc_subset_Icc le_rfl hv.2.le))
        (fun t ht => hφ''_d t ⟨ht.1, ht.2.trans_le hv.2.le⟩)
      have heq : φ' v - φ' 0 = φ'' c * v := by
        rw [sub_zero] at hslope
        exact ((eq_div_iff hv_pos.ne').1 hslope).symm
      rw [heq, abs_mul, abs_of_pos hv_pos]
      exact mul_le_mul_of_nonneg_right (hφ''_b c ⟨hc.1, hc.2.trans_le hv.2.le⟩) hv_pos.le
  have hbound := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := g) (a := 0) (b := 1)
    (B := fun v => C * v ^ 2 / 2)
    (B' := fun v => C * v)
    hg_cont hg_right (by simp [g])
    (fun v => by
      have h := ((hasDerivAt_pow 2 v).const_mul C).div_const 2
      exact h.congr_deriv (by push_cast; ring))
    hlip_φ' (x := 1) ⟨zero_le_one, le_rfl⟩
  rw [Real.norm_eq_abs] at hbound
  dsimp only [g] at hbound
  simpa using hbound

/-- If `f : ℝ → ℝ` is continuous on `[a, b]` and has derivative bounded by `C` on `(a, b)`,
then `|f y - f x| ≤ C * |y - x|` for all `x, y ∈ [a, b]`. -/
theorem abs_sub_le_of_continuousOn_Icc_of_hasDerivAt_Ioo
    {f : ℝ → ℝ} {a b C : ℝ} (hfc : ContinuousOn f (Icc a b))
    (hfd : ∀ x ∈ Ioo a b, ∃ d, HasDerivAt f d x ∧ |d| ≤ C)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |f y - f x| ≤ C * |y - x| := by
  wlog hxy : x ≤ y generalizing x y
  · rw [abs_sub_comm (f y) (f x), abs_sub_comm y x]
    exact this hy hx (le_of_not_ge hxy)
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · simp
  have hsub : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1 hy.2
  have hsub_oo : Ioo x y ⊆ Ioo a b := Ioo_subset_Ioo hx.1 hy.2
  choose! f' hf' hfb using hfd
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope f f' hlt (hfc.mono hsub)
    (fun t ht => hf' t (hsub_oo ht))
  have hpos : 0 < y - x := sub_pos.2 hlt
  have heq : f y - f x = f' c * (y - x) := ((eq_div_iff hpos.ne').1 hslope).symm
  rw [heq, abs_mul, abs_of_pos hpos]
  exact mul_le_mul_of_nonneg_right (hfb c (hsub_oo hc)) hpos.le

/-- A differentiable concave function on `ℝ` which is constant on a half-line `[τ, ∞)` has a
nonnegative derivative. -/
theorem ConcaveOn.deriv_nonneg_of_forall_ge_eq {u : ℝ → ℝ} (huc : ConcaveOn ℝ univ u)
    (hu : Differentiable ℝ u) {τ b : ℝ} (h : ∀ x, τ ≤ x → u x = b) (x : ℝ) : 0 ≤ deriv u x := by
  have hτ : τ < max x τ + 1 := (le_max_right x τ).trans_lt (lt_add_one _)
  have h0 : deriv u (max x τ + 1) = 0 := by
    have : u =ᶠ[𝓝 (max x τ + 1)] fun _ => b := by
      filter_upwards [Ioi_mem_nhds hτ] with t ht using h t (le_of_lt ht)
    rw [this.deriv_eq, deriv_const]
  exact h0 ▸ huc.antitoneOn_deriv (fun z _ => hu z) (mem_univ x) (mem_univ _)
    ((le_max_left x τ).trans (le_add_of_nonneg_right zero_le_one))
