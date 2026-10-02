/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Deep.BackwardTop

/-!
# The Joint Downward Induction on `DeepSpace`

The backward Gram convergence `C(ℓ)` (`G_ℓ^{ab} → Π^ℓ_{ab}` for all pairs) and the
gradient-independence invariant `I(ℓ)` (`n⁻¹ ⟨h_ℓ^b, g_ℓ^a⟩ → 0` for all pairs) are proved together
by downward induction on `ℓ = d - 1, …, 0`:

* base `ℓ = d - 1`: `sensitivityGram_top_tendsto`, `gradIndep_top_tendsto`
  (`Deep/BackwardTop.lean`);
* step `ℓ + 1 → ℓ`: `gradIndep_step_tendsto` gives `I(ℓ)`, and the decoupling approximation
  `decoupling_tendsto` together with `G_{ℓ+1} → Π^{ℓ+1}` and `Φ'_ℓ → Σ̇^ℓ` gives `C(ℓ)` (the limit
  recursion `Π^ℓ = Σ̇^ℓ ⊙ Π^{ℓ+1}` is `deepLimitingSensitivityKernel_step`).

The result `deepSpace_sensitivity_induction` is stated on `DeepSpace d` and transported to the
`(W, w_out)` product space in `Deep/BackwardConcentration.lean`.
-/

@[expose]
public section

open MeasureTheory ProbabilityTheory Filter Matrix
open scoped Matrix

namespace NTK

variable {d n0 m : ℕ} {φ φ' : ℝ → ℝ} (A : ActivationData φ φ') (X : Fin m → Fin n0 → ℝ)

/-- Reading the parameters from a prefix of a tensor population is the same as `ofTensor`. -/
lemma deepParams_prefix (hd : 0 < d) (n : ℕ) (q : (ℕ → ℕ → ℕ → ℝ) × (ℕ → ℝ)) :
    deepParams d n0 n ((fun i : Fin d => q.1 i.val), q.2) =
      DeepMLPParams.ofTensor d n0 n q.1 q.2 := by
  simp only [deepParams, DeepMLPParams.ofTensor, DeepMLPParams.mk.injEq, and_true]
  refine ⟨?_, ?_⟩
  · simp [hd]
  · funext ℓ
    have : ℓ.val + 1 < d := by have := ℓ.2; omega
    simp [this]

/-- The backward Gram entries are measurable functions of the point of `DeepSpace`. -/
lemma measurable_sensitivityGram_entry (hφ : Measurable φ) (hφ' : Measurable φ') (n k : ℕ)
    (hk : k < d) (a b : Fin m) :
    Measurable fun ω : DeepSpace d =>
      deepSensitivityGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ a b := by
  have : ∀ ω : DeepSpace d, deepSensitivityGram d n0 n m φ φ' X (deepParams d n0 n ω)
      ⟨k, by omega⟩ a b = (n : ℝ)⁻¹ * ∑ j : Fin n,
        backwardSensitivity d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k, hk⟩ a j *
        backwardSensitivity d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k, hk⟩ b j := by
    intro ω
    rw [deepSensitivityGram_hidden d n0 n m φ φ' X _ k hk, Matrix.of_apply]
    rfl
  simp only [this]
  exact measurable_const.mul (Finset.measurable_sum _ fun j _ =>
    (measurable_backwardSensitivity (paramsMeasurable_deepParams d n0 n) hφ hφ' X ⟨k, hk⟩ a j).mul
      (measurable_backwardSensitivity (paramsMeasurable_deepParams d n0 n) hφ hφ' X ⟨k, hk⟩ b j))

/-- The derivative Gram entries are measurable functions of the point of `DeepSpace`. -/
lemma measurable_derivativeGram_entry (hφ : Measurable φ) (hφ' : Measurable φ') (n k : ℕ)
    (hk : k < d) (a b : Fin m) :
    Measurable fun ω : DeepSpace d =>
      deepDerivativeGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k, hk⟩ a b := by
  simp only [deepDerivativeGram, Matrix.of_apply, dotProduct]
  exact measurable_const.mul (Finset.measurable_sum _ fun j _ =>
    (hφ'.comp (measurable_netPre hφ X n ⟨k, hk⟩ a j)).mul
      (hφ'.comp (measurable_netPre hφ X n ⟨k, hk⟩ b j)))

include A in
/-- `Φ'_k → Σ̇^k` entrywise on `DeepSpace`. -/
lemma derivGram_tendsto (k : ℕ) (hk : k < d) (a b : Fin m) :
    TendstoInMeasure (deepMeasure d)
      (fun (n : ℕ) (ω : DeepSpace d) =>
        deepDerivativeGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k, hk⟩ a b) atTop
      (fun _ => ∫ z : EuclideanSpace ℝ (Fin m), φ' (z.ofLp a) * φ' (z.ofLp b)
        ∂multivariateGaussian 0
        (layerCovarianceSeq 1 0 φ m (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) k)) :=
  (deepSpace_featureCov_tendsto φ φ' A.cont A.cont' A.C A.hC A.p A.hp A.growth A.C A.hC A.p A.hp
    A.growth' X k hk a b).congr_left fun n => Eventually.of_forall fun ω => by
      simp [deepDerivativeGram, dotProduct]

include A in
/-- **The joint downward induction on `DeepSpace`**: for every layer `k < d`, the backward Gram
entries converge to the limiting backward kernel `Π^k`, and gradient independence holds. -/
theorem deepSpace_sensitivity_induction (hd : 0 < d)
    (hnd : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < d →
      (layerCovarianceSeq 1 0 φ m (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) ℓ).PosDef)
    (k : ℕ) (hk : k < d) :
    (∀ a b : Fin m, TendstoInMeasure (deepMeasure d)
      (fun (n : ℕ) (ω : DeepSpace d) =>
        deepSensitivityGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ a b) atTop
      (fun _ => deepLimitingSensitivityKernel d m φ φ'
        (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) ⟨k, by omega⟩ a b)) ∧
    (∀ a b : Fin m, TendstoInMeasure (deepMeasure d)
      (fun (n : ℕ) (ω : DeepSpace d) =>
        gradIndep φ φ' X (deepParams d n0 n ω) ⟨k, hk⟩ a b) atTop (fun _ => 0)) := by
  suffices key : ∀ j : ℕ, ∀ k : ℕ, ∀ hk : k < d, k + j = d - 1 →
      (∀ a b : Fin m, TendstoInMeasure (deepMeasure d)
        (fun (n : ℕ) (ω : DeepSpace d) =>
          deepSensitivityGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k, by omega⟩ a b) atTop
        (fun _ => deepLimitingSensitivityKernel d m φ φ'
          (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) ⟨k, by omega⟩ a b)) ∧
      (∀ a b : Fin m, TendstoInMeasure (deepMeasure d)
        (fun (n : ℕ) (ω : DeepSpace d) =>
          gradIndep φ φ' X (deepParams d n0 n ω) ⟨k, hk⟩ a b) atTop (fun _ => 0)) from
    key (d - 1 - k) k hk (by omega)
  intro j
  induction j with
  | zero =>
    intro k hk hkj
    obtain rfl : k = d - 1 := by omega
    refine ⟨fun a b => ?_, fun a b => gradIndep_top_tendsto A X hd a b⟩
    have h := sensitivityGram_top_tendsto A X hd a b
    have hterm : deepLimitingSensitivityKernel d m φ φ'
        (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) ⟨d - 1 + 1, by omega⟩ =
        Matrix.of fun _ _ => 1 := by
      have : (⟨d - 1 + 1, by omega⟩ : Fin (d + 1)) = ⟨d, by omega⟩ :=
        Fin.ext (Nat.sub_add_cancel (by omega))
      rw [this]
      exact deepLimitingSensitivityKernel_terminal d m φ φ' _
    have hlim := congrFun (congrFun
      (deepLimitingSensitivityKernel_step d m φ φ'
        (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) ⟨d - 1, by omega⟩
        (by simp; omega)) a) b
    simp only [Matrix.hadamard_apply, hterm, Matrix.of_apply, mul_one] at hlim
    rw [hlim]
    exact h
  | succ j ih =>
    intro k hk hkj
    have hk1 : k + 1 < d := by omega
    obtain ⟨hC, hI⟩ := ih (k + 1) hk1 (by omega)
    have hpd := hnd (k + 1) (by omega) hk1
    have hG : ∀ c c' : Fin m, ∃ c0 : ℝ, TendstoInMeasure (deepMeasure d)
        (fun (n : ℕ) (ω : DeepSpace d) =>
          deepSensitivityGram d n0 n m φ φ' X (deepParams d n0 n ω) ⟨k + 1, by omega⟩ c c')
        atTop (fun _ => c0) := fun c c' => ⟨_, hC c c'⟩
    refine ⟨fun a b => ?_, fun a b => gradIndep_step_tendsto A X k hk1 hpd hG hI a b⟩
    have hdec := decoupling_tendsto A X k hk1 hpd hG hI a b
    have hD := derivGram_tendsto (n0 := n0) A X k hk a b
    have hprod := tendstoInMeasure_mul (hC a b) hD
    have hsum := tendstoInMeasure_add hdec hprod
    have hlim := congrFun (congrFun
      (deepLimitingSensitivityKernel_step d m φ φ'
        (Matrix.of fun i j => (n0 : ℝ)⁻¹ * (X i ⬝ᵥ X j)) ⟨k, by omega⟩ hk) a) b
    simp only [Matrix.hadamard_apply, Matrix.of_apply] at hlim
    rw [hlim, mul_comm]
    rw [zero_add] at hsum
    refine hsum.congr_left fun n => Eventually.of_forall fun ω => ?_
    ring

end NTK

end
