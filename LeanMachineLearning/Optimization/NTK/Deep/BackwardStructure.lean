/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Deep.LayerSplit
public import LeanMachineLearning.Optimization.NTK.Foundations.MatrixMeasurability

/-!
# Structure of the Forward and Backward Passes under a Layer Substitution

Facts about `deepMLPPreactivation` and `backwardSensitivity` used to condition on one weight layer
`W_{k+1} = Wh k`:

* `DeepMLPParams.updateWh`: replace one hidden weight matrix.
* **Prefix congruence** (`deepMLPPreactivation_congr_prefix`): `h_ℓ` reads only `W0` and `Wh j`,
  `j < ℓ`; so `h_k` does not change when `Wh k` is substituted.
* **Suffix congruence** (`deepMLPPreactivation_congr_suffix`,
  `backwardSensitivity_updateWh_congr`): `g_{k+1}` sees `Wh k` only through `Wh k · φ(h_k^α)`,
  i.e. through `Wh k Φ`.
* **Measurability** (`ParamsMeasurable`, `measurable_deepMLPPreactivation`,
  `measurable_backwardSensitivity`): the passes are measurable functions of the weight entries.
-/

@[expose]
public section

open MeasureTheory Matrix
open scoped Matrix

namespace NTK

variable {d n0 n m : ℕ}

/-- Replace the hidden weight matrix `Wh k` of a parameter record. -/
def DeepMLPParams.updateWh (θ : DeepMLPParams d n0 n) (k : Fin (d - 1))
    (X : Matrix (Fin n) (Fin n) ℝ) : DeepMLPParams d n0 n :=
  { θ with Wh := Function.update θ.Wh k X }

/-- Substituting a hidden weight matrix and reading it back gives the substituted matrix. -/
@[simp] lemma DeepMLPParams.updateWh_Wh_self (θ : DeepMLPParams d n0 n) (k : Fin (d - 1))
    (X : Matrix (Fin n) (Fin n) ℝ) : (θ.updateWh k X).Wh k = X := by
  simp [DeepMLPParams.updateWh]

/-- Substituting the hidden matrix at layer `k` leaves every other hidden matrix `j ≠ k` unchanged.
-/
lemma DeepMLPParams.updateWh_Wh_of_ne (θ : DeepMLPParams d n0 n) {k j : Fin (d - 1)}
    (X : Matrix (Fin n) (Fin n) ℝ) (h : j ≠ k) : (θ.updateWh k X).Wh j = θ.Wh j := by
  simp [DeepMLPParams.updateWh, Function.update_of_ne h]

/-- Substituting a hidden matrix leaves the input weights `W0` unchanged. -/
@[simp] lemma DeepMLPParams.updateWh_W0 (θ : DeepMLPParams d n0 n) (k : Fin (d - 1))
    (X : Matrix (Fin n) (Fin n) ℝ) : (θ.updateWh k X).W0 = θ.W0 := rfl

/-- Substituting a hidden matrix leaves the readout weights `Wd` unchanged. -/
@[simp] lemma DeepMLPParams.updateWh_Wd (θ : DeepMLPParams d n0 n) (k : Fin (d - 1))
    (X : Matrix (Fin n) (Fin n) ℝ) : (θ.updateWh k X).Wd = θ.Wd := rfl

/-- **Prefix congruence for the forward pass.** `h_ℓ` reads only `W0` and the `Wh j` with
`j < ℓ`. -/
lemma deepMLPPreactivation_congr_prefix (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ θ' : DeepMLPParams d n0 n) (ℓ : Fin d) (hW0 : θ.W0 = θ'.W0)
    (hWh : ∀ j : Fin (d - 1), j.val < ℓ.val → θ.Wh j = θ'.Wh j) :
    deepMLPPreactivation d n0 n m φ X θ ℓ = deepMLPPreactivation d n0 n m φ X θ' ℓ := by
  obtain ⟨ℓ, hℓ⟩ := ℓ
  induction ℓ with
  | zero =>
    funext α j
    rw [deepMLPPreactivation_zero _ _ _ _ _ _ _ hℓ, deepMLPPreactivation_zero _ _ _ _ _ _ _ hℓ,
      hW0]
  | succ ℓ ih =>
    funext α j
    rw [deepMLPPreactivation_succ _ _ _ _ _ _ _ ℓ hℓ, deepMLPPreactivation_succ _ _ _ _ _ _ _ ℓ hℓ,
      hWh ⟨ℓ, by omega⟩ (by simp only; omega)]
    have := ih (by omega) (fun j hj => hWh j (Nat.lt_succ_of_lt hj))
    simp only [this]

/-- **Suffix congruence for the forward pass.** If `h_{ℓ₀}` and the weights `Wh j`, `j ≥ ℓ₀`,
agree, then so do all `h_ℓ`, `ℓ ≥ ℓ₀`. -/
lemma deepMLPPreactivation_congr_suffix (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ θ' : DeepMLPParams d n0 n) (ℓ₀ : Fin d)
    (h₀ : deepMLPPreactivation d n0 n m φ X θ ℓ₀ = deepMLPPreactivation d n0 n m φ X θ' ℓ₀)
    (hWh : ∀ j : Fin (d - 1), ℓ₀.val ≤ j.val → θ.Wh j = θ'.Wh j) (ℓ : Fin d)
    (hℓ : ℓ₀.val ≤ ℓ.val) :
    deepMLPPreactivation d n0 n m φ X θ ℓ = deepMLPPreactivation d n0 n m φ X θ' ℓ := by
  obtain ⟨ℓ, hℓd⟩ := ℓ
  induction ℓ with
  | zero =>
    have : ℓ₀ = ⟨0, hℓd⟩ := Fin.ext (by simp only at hℓ ⊢; omega)
    subst this; exact h₀
  | succ ℓ ih =>
    by_cases hle : ℓ₀.val ≤ ℓ
    · funext α j
      rw [deepMLPPreactivation_succ _ _ _ _ _ _ _ ℓ hℓd,
        deepMLPPreactivation_succ _ _ _ _ _ _ _ ℓ hℓd,
        hWh ⟨ℓ, by omega⟩ (by simp only; omega)]
      have := ih (by omega) hle
      simp only [this]
    · have : ℓ₀ = ⟨ℓ + 1, hℓd⟩ := Fin.ext (by simp only at hℓ hle ⊢; omega)
      subst this; exact h₀

/-- A hidden weight matrix `Wh k` affects the forward pass only from layer `k + 1` on:
`h_ℓ` is unchanged for `ℓ ≤ k`. -/
lemma deepMLPPreactivation_updateWh_of_le (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (k : Fin (d - 1)) (Y : Matrix (Fin n) (Fin n) ℝ) (ℓ : Fin d)
    (hℓ : ℓ.val ≤ k.val) :
    deepMLPPreactivation d n0 n m φ X (θ.updateWh k Y) ℓ =
      deepMLPPreactivation d n0 n m φ X θ ℓ :=
  deepMLPPreactivation_congr_prefix φ X _ _ ℓ rfl fun j hj =>
    DeepMLPParams.updateWh_Wh_of_ne θ Y (by intro h; subst h; omega)

/-- `h_{k+1}^α = n^{-1/2} Wh k φ(h_k^α)`, in matrix form. -/
lemma deepMLPPreactivation_succ_mulVec (φ : ℝ → ℝ) (X : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (k : ℕ) (hk : k + 1 < d) (α : Fin m) :
    deepMLPPreactivation d n0 n m φ X θ ⟨k + 1, hk⟩ α =
      Real.sqrt ((n : ℝ)⁻¹) • (θ.Wh ⟨k, by omega⟩ *ᵥ fun i =>
        φ (deepMLPPreactivation d n0 n m φ X θ ⟨k, by omega⟩ α i)) := by
  funext j
  rw [deepMLPPreactivation_succ]
  simp [Matrix.mulVec, dotProduct]

/-- **`g_{k+1}` depends on `Wh k` only through `Wh k Φ`.** If two substitutions `X, X'` for
`Wh k` agree on the forward features `φ(h_k^α)`, the backward sensitivities `g_{k+1}` agree. -/
lemma backwardSensitivity_updateWh_congr (φ φ' : ℝ → ℝ) (X₀ : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (k : ℕ) (hk : k + 1 < d) (X X' : Matrix (Fin n) (Fin n) ℝ)
    (hXX' : ∀ α : Fin m, X *ᵥ (fun i =>
        φ (deepMLPPreactivation d n0 n m φ X₀ θ ⟨k, by omega⟩ α i)) =
      X' *ᵥ (fun i => φ (deepMLPPreactivation d n0 n m φ X₀ θ ⟨k, by omega⟩ α i))) :
    backwardSensitivity d n0 n m φ φ' X₀ (θ.updateWh ⟨k, by omega⟩ X) ⟨k + 1, hk⟩ =
      backwardSensitivity d n0 n m φ φ' X₀ (θ.updateWh ⟨k, by omega⟩ X') ⟨k + 1, hk⟩ := by
  have hk' : k < d - 1 := by omega
  have hprev : ∀ Y : Matrix (Fin n) (Fin n) ℝ,
      deepMLPPreactivation d n0 n m φ X₀ (θ.updateWh ⟨k, hk'⟩ Y) ⟨k, by omega⟩ =
        deepMLPPreactivation d n0 n m φ X₀ θ ⟨k, by omega⟩ := fun Y =>
    deepMLPPreactivation_updateWh_of_le φ X₀ θ ⟨k, hk'⟩ Y ⟨k, by omega⟩ le_rfl
  have hone : deepMLPPreactivation d n0 n m φ X₀ (θ.updateWh ⟨k, hk'⟩ X) ⟨k + 1, hk⟩ =
      deepMLPPreactivation d n0 n m φ X₀ (θ.updateWh ⟨k, hk'⟩ X') ⟨k + 1, hk⟩ := by
    funext α
    rw [deepMLPPreactivation_succ_mulVec, deepMLPPreactivation_succ_mulVec]
    simp only [DeepMLPParams.updateWh_Wh_self, hprev]
    rw [hXX' α]
  refine backwardSensitivity_congr_of_eqOn d n0 n m φ φ' X₀ _ _ ⟨k + 1, hk⟩ rfl ?_ ?_
  · intro j hj
    rw [DeepMLPParams.updateWh_Wh_of_ne θ X (by intro h; subst h; simp at hj),
      DeepMLPParams.updateWh_Wh_of_ne θ X' (by intro h; subst h; simp at hj)]
  · intro j hj
    exact deepMLPPreactivation_congr_suffix φ X₀ _ _ ⟨k + 1, hk⟩ hone
      (fun i hi => by
        rw [DeepMLPParams.updateWh_Wh_of_ne θ X (by intro h; subst h; simp at hi),
          DeepMLPParams.updateWh_Wh_of_ne θ X' (by intro h; subst h; simp at hi)]) j hj

/-- `g_k^α = φ'(h_k^α) ⊙ (n^{-1/2} Wh kᵀ g_{k+1}^α)`, in matrix form. -/
lemma backwardSensitivity_succ_mulVec (φ φ' : ℝ → ℝ) (X₀ : Fin m → Fin n0 → ℝ)
    (θ : DeepMLPParams d n0 n) (k : ℕ) (hk : k + 1 < d) (α : Fin m) :
    backwardSensitivity d n0 n m φ φ' X₀ θ ⟨k, by omega⟩ α =
      fun j => φ' (deepMLPPreactivation d n0 n m φ X₀ θ ⟨k, by omega⟩ α j) *
        (Real.sqrt ((n : ℝ)⁻¹) •
          ((θ.Wh ⟨k, by omega⟩)ᵀ *ᵥ backwardSensitivity d n0 n m φ φ' X₀ θ ⟨k + 1, hk⟩ α)) j := by
  funext j
  rw [backwardSensitivity_step d n0 n m φ φ' X₀ θ ⟨k, by omega⟩ (by simp only; omega)]
  simp [Matrix.mulVec, dotProduct]

/-! ### Measurability of the passes in the weight entries -/

section measurability

variable {Z : Type*} [MeasurableSpace Z]

/-- A family of parameter records is measurable if every weight entry is. -/
structure ParamsMeasurable (θ : Z → DeepMLPParams d n0 n) : Prop where
  W0 : ∀ j i, Measurable fun z => (θ z).W0 j i
  Wh : ∀ ℓ j i, Measurable fun z => (θ z).Wh ℓ j i
  Wd : ∀ j, Measurable fun z => (θ z).Wd j

/-- Preactivations are measurable functions of `z` whenever the parameter family `θ` is measurable
(`ParamsMeasurable`). -/
lemma measurable_deepMLPPreactivation {θ : Z → DeepMLPParams d n0 n} (hθ : ParamsMeasurable θ)
    {φ : ℝ → ℝ} (hφ : Measurable φ) (X : Fin m → Fin n0 → ℝ) (ℓ : Fin d) (α : Fin m)
    (j : Fin n) : Measurable fun z => deepMLPPreactivation d n0 n m φ X (θ z) ℓ α j := by
  obtain ⟨ℓ, hℓ⟩ := ℓ
  induction ℓ generalizing j with
  | zero =>
    simp only [deepMLPPreactivation_zero _ _ _ _ _ _ _ hℓ]
    refine measurable_const.mul ?_
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun i _ => (hθ.W0 j i).mul_const _
  | succ ℓ ih =>
    simp only [deepMLPPreactivation_succ _ _ _ _ _ _ _ ℓ hℓ]
    refine measurable_const.mul (Finset.measurable_sum _ fun i _ => (hθ.Wh _ j i).mul ?_)
    exact hφ.comp (ih i (by omega))

/-- Backward sensitivities are measurable functions of `z` whenever the parameter family `θ` is
measurable (`ParamsMeasurable`). -/
lemma measurable_backwardSensitivity {θ : Z → DeepMLPParams d n0 n} (hθ : ParamsMeasurable θ)
    {φ φ' : ℝ → ℝ} (hφ : Measurable φ) (hφ' : Measurable φ') (X : Fin m → Fin n0 → ℝ)
    (ℓ : Fin d) (α : Fin m) (j : Fin n) :
    Measurable fun z => backwardSensitivity d n0 n m φ φ' X (θ z) ℓ α j := by
  induction ℓ using backwardInduction generalizing j with
  | top ℓ hℓ =>
    have hd : 0 < d := by have := ℓ.2; omega
    have heq : ℓ = ⟨d - 1, by omega⟩ := Fin.ext (by simp only; omega)
    rw [heq]
    simp only [backwardSensitivity_top d n0 n m φ φ' X _ hd]
    exact (hθ.Wd j).mul (hφ'.comp (measurable_deepMLPPreactivation hθ hφ X _ α j))
  | step ℓ hℓ ih =>
    have hne : ℓ.val < d - 1 := by omega
    simp only [backwardSensitivity_step d n0 n m φ φ' X _ ℓ hne]
    refine (hφ'.comp (measurable_deepMLPPreactivation hθ hφ X ℓ α j)).mul
      (measurable_const.mul (Finset.measurable_sum _ fun i _ => (hθ.Wh _ i j).mul ?_))
    exact ih i

end measurability

/-! ### The parameters read from `population/readout product`, and the layer substitution -/

section deepSpace

variable (d n0 n)

/-- Entries of the zero-padded prefix weight tensor of a `population/readout product` point are measurable. -/
lemma measurable_prefixTensor_entry (k j i : ℕ) :
    Measurable fun ω : ((Fin d → ℕ → ℕ → ℝ) × (ℕ → ℝ)) => (if h : k < d then ω.1 ⟨k, h⟩ else 0) j i := by
  by_cases h : k < d
  · simp only [h, dite_true]
    exact (measurable_pi_apply i).comp ((measurable_pi_apply j).comp
      ((measurable_pi_apply (⟨k, h⟩ : Fin d)).comp measurable_fst))
  · simp only [h, dite_false]; exact measurable_const

/-- `deepParams d n0 n` is a measurable family of parameter records on `population/readout product`. -/
lemma paramsMeasurable_deepParams : ParamsMeasurable (deepParams d n0 n) where
  W0 j i := measurable_prefixTensor_entry d 0 j.val i.val
  Wh ℓ j i := measurable_prefixTensor_entry d (ℓ.val + 1) j.val i.val
  Wd j := (measurable_pi_apply j.val).comp measurable_snd

variable {d n0 n}

/-- **The parameters of `ω` are the substitution of its `Wh k` block into those of the network
with that population zeroed.**
With `i₀ = k + 1` the weight population feeding `Wh k`: the network at `ω` is the network at
`(Function.update ω.1 i₀ 0, ω.2)` with `Wh k` replaced by the `n × n` block of `ω.1 i₀`. -/
lemma deepParams_eq_updateWh (k : Fin (d - 1)) (ω : ((Fin d → ℕ → ℕ → ℝ) × (ℕ → ℝ))) :
    deepParams d n0 n ω =
      (deepParams d n0 n (Function.update ω.1 (⟨k.val + 1, by omega⟩ : Fin d) 0, ω.2)).updateWh k
        (Matrix.of (fun j i => (ω.1 ⟨k.val + 1, by omega⟩) j.val i.val)) := by
  have hk := k.2
  simp only [deepParams, DeepMLPParams.ofTensor, DeepMLPParams.updateWh,
    DeepMLPParams.mk.injEq]
  refine ⟨?_, ?_, trivial⟩
  · have h0 : 0 < d := by omega
    have : (⟨0, h0⟩ : Fin d) ≠ ⟨k.val + 1, by omega⟩ := by
      intro h; simp [Fin.ext_iff] at h
    simp only [h0, dite_true, Function.update_of_ne this]
  · funext ℓ
    have hk1 : k.val + 1 < d := by omega
    by_cases h : ℓ = k
    · subst h
      simp only [Function.update_self, hk1, dite_true]
      rfl
    · have hℓ1 : ℓ.val + 1 < d := by have := ℓ.2; omega
      have : (⟨ℓ.val + 1, hℓ1⟩ : Fin d) ≠ ⟨k.val + 1, hk1⟩ := by
        intro h'; apply h; exact Fin.ext (by simpa [Fin.ext_iff] using h')
      simp only [Function.update_of_ne h, hℓ1, dite_true, Function.update_of_ne this]

end deepSpace

end NTK

end
