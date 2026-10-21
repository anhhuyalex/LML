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
