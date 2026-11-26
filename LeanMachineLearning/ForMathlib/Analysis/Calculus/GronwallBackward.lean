/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Foundations.ODE

/-!
# Grönwall's inequality run backwards from the right endpoint

Interpolation arguments compare a quantity at time `t` with its value at the endpoint `1`.
This is the time reversal of `NTK.gronwall_exponential_decay_Icc`.
-/

@[expose] public section

open Set

/-- If `g` is continuous on `[0, 1]`, differentiable on `(0, 1)` and `g' ≥ -K g` there, then
`g t ≤ exp (K (1 - t)) g 1` for every `t ∈ [0, 1]`. -/
theorem le_exp_mul_endpoint_of_neg_mul_le_deriv {g g' : ℝ → ℝ} {K : ℝ}
    (hc : ContinuousOn g (Icc 0 1)) (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g (g' t) t)
    (hb : ∀ t ∈ Ioo (0 : ℝ) 1, -(K * g t) ≤ g' t) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    g t ≤ Real.exp (K * (1 - t)) * g 1 := by
  have hmaps : MapsTo (fun u : ℝ => 1 - u) (Icc 0 1) (Icc 0 1) := fun u hu =>
    ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have h := NTK.gronwall_exponential_decay_Icc (E := fun u => g (1 - u))
    (E' := fun u => -g' (1 - u)) (c := -K) zero_le_one
    (hc.comp (by fun_prop) hmaps)
    (fun u hu => (hd (1 - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩).comp_const_sub 1 u)
    (fun u hu => by
      have := hb (1 - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
      linarith)
    (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  simpa [mul_comm, neg_mul] using h

/-- The same comparison with the derivative bound stated pointwise, so callers need not choose a
global derivative function. -/
theorem le_exp_mul_endpoint_of_exists_hasDerivAt {g : ℝ → ℝ} {K : ℝ}
    (hc : ContinuousOn g (Icc 0 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, ∃ d, HasDerivAt g d t ∧ -(K * g t) ≤ d) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : g t ≤ Real.exp (K * (1 - t)) * g 1 := by
  choose! g' hd' hb using hd
  exact le_exp_mul_endpoint_of_neg_mul_le_deriv hc hd' hb ht

/-- **Forward affine Grönwall comparison on `[0, 1]`:** if `ψ ≥ 0` is continuous on `[0, 1]` and
satisfies `ψ'(t) ≤ K * ψ(t) + ε` (`K, ε ≥ 0`) on the interior `(0, 1)`, then
`ψ(s) ≤ exp(K + 1) * (ψ(0) + ε)` for every `s ∈ [0, 1]`. -/
theorem le_exp_mul_add_of_exists_hasDerivAt_Ioo {ψ : ℝ → ℝ} {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hc : ContinuousOn ψ (Icc (0 : ℝ) 1)) (hψ0 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ ψ s)
    (hd : ∀ s ∈ Ioo (0 : ℝ) 1, ∃ d, HasDerivAt ψ d s ∧ d ≤ K * ψ s + ε)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ψ s ≤ Real.exp (K + 1) * (ψ 0 + ε) := by
  let K' : ℝ := K + 1
  have hK' : 1 ≤ K' := by dsimp only [K']; linarith
  have hK'_pos : 0 < K' := zero_lt_one.trans_le hK'
  let g (t : ℝ) : ℝ := (ψ t + ε / K') * Real.exp (-K' * t)
  have hg_cont : ContinuousOn g (Icc 0 1) := (hc.add continuousOn_const).mul (by fun_prop)
  choose! ψ' hψ'_d hψ'_le using hd
  have hg_deriv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt g ((ψ' t - K' * ψ t - ε) * Real.exp (-K' * t)) t := by
    intro t ht
    have h1 : HasDerivAt (fun u => ψ u + ε / K') (ψ' t) t := (hψ'_d t ht).add_const _
    have h2 : HasDerivAt (fun u => Real.exp (-K' * u)) (Real.exp (-K' * t) * (-K')) t := by
      have hc1 : HasDerivAt (fun u => -K' * u) (-K' * 1) t := (hasDerivAt_id t).const_mul (-K')
      rw [mul_one] at hc1
      exact hc1.exp
    refine (h1.mul h2).congr_deriv ?_
    field_simp; ring
  have hg_within : ∀ t ∈ interior (Icc (0 : ℝ) 1),
      HasDerivWithinAt g ((ψ' t - K' * ψ t - ε) * Real.exp (-K' * t)) (interior (Icc 0 1)) t :=
    fun t ht => (hg_deriv t (by rwa [interior_Icc] at ht)).hasDerivWithinAt
  have hg_nonpos : ∀ t ∈ interior (Icc (0 : ℝ) 1),
      (ψ' t - K' * ψ t - ε) * Real.exp (-K' * t) ≤ 0 := by
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by rwa [interior_Icc] at ht
    have hle : ψ' t - K' * ψ t - ε ≤ 0 := by
      have h1 := hψ'_le t ht'
      have h2 := hψ0 t ⟨ht'.1.le, ht'.2.le⟩
      dsimp only [K']; nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg hle (Real.exp_pos _).le
  have h_anti : AntitoneOn g (Icc 0 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1) hg_cont hg_within hg_nonpos
  have h_le := h_anti ⟨le_rfl, zero_le_one⟩ hs hs.1
  dsimp only [g] at h_le
  rw [mul_zero, Real.exp_zero, mul_one] at h_le
  have h_mul := mul_le_mul_of_nonneg_right h_le (Real.exp_pos (K' * s)).le
  have hcancel : (ψ s + ε / K') * Real.exp (-K' * s) * Real.exp (K' * s) = ψ s + ε / K' := by
    rw [mul_assoc, ← Real.exp_add, show -K' * s + K' * s = 0 by ring, Real.exp_zero, mul_one]
  rw [hcancel] at h_mul
  have hdiv_le : ε / K' ≤ ε := div_le_self hε hK'
  have h0_nn : 0 ≤ ψ 0 + ε / K' := add_nonneg (hψ0 0 ⟨le_rfl, zero_le_one⟩) (by positivity)
  have hexp_le : Real.exp (K' * s) ≤ Real.exp (K + 1) :=
    Real.exp_le_exp.2 (by dsimp only [K']; nlinarith [hs.2])
  calc ψ s ≤ ψ s + ε / K' := le_add_of_nonneg_right (by positivity)
    _ ≤ (ψ 0 + ε / K') * Real.exp (K' * s) := h_mul
    _ ≤ (ψ 0 + ε) * Real.exp (K + 1) :=
        mul_le_mul (add_le_add le_rfl hdiv_le) hexp_le (Real.exp_pos _).le (by linarith)
    _ = Real.exp (K + 1) * (ψ 0 + ε) := mul_comm _ _

/-- **Backward affine Grönwall comparison on `[0, 1]` (Talagrand, Lemma A.13.1):** if `ψ ≥ 0` is
continuous on `[0, 1]` and satisfies `-(K * ψ t + ε) ≤ ψ' t` (`K, ε ≥ 0`) on `(0, 1)`, then
`ψ s ≤ exp (K + 1) * (ψ 1 + ε)` for every `s ∈ [0, 1]`. -/
theorem le_exp_mul_add_endpoint_of_exists_hasDerivAt_Ioo {ψ : ℝ → ℝ} {K ε : ℝ} (hK : 0 ≤ K)
    (hε : 0 ≤ ε) (hc : ContinuousOn ψ (Icc (0 : ℝ) 1)) (hψ0 : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ ψ s)
    (hd : ∀ s ∈ Ioo (0 : ℝ) 1, ∃ d, HasDerivAt ψ d s ∧ -(K * ψ s + ε) ≤ d)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ψ s ≤ Real.exp (K + 1) * (ψ 1 + ε) := by
  have hmaps : MapsTo (fun u : ℝ => 1 - u) (Icc 0 1) (Icc 0 1) := fun u hu =>
    ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have h := le_exp_mul_add_of_exists_hasDerivAt_Ioo (ψ := fun u => ψ (1 - u)) hK hε
    (hc.comp (by fun_prop) hmaps) (fun u hu => hψ0 (1 - u) (hmaps hu))
    (fun u hu => by
      obtain ⟨d, hdu, hdb⟩ := hd (1 - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
      exact ⟨-d, hdu.comp_const_sub 1 u, by linarith⟩)
    (s := 1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
  simpa only [sub_sub_cancel, sub_zero] using h
