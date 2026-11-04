/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.CascadeData
public import LeanMachineLearning.SpinGlasses.CascadeParisiStep

/-!
# The marked partition sum of a Ruelle cascade

For the vertex data `d (p, γ) = (blocks, labels)`, the weights `w_α` are the branch products of the
ranked atoms of the blocks, the label of the child `γ n` of `γ` is `(d (p, γ)).2 n`, and
`cascadeMarkedSum r X g d = ∑_α w_α g(d (r, α)) exp (X (labels along α))` is the partition sum
of Section 2.4 with the final-level mark `g`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace SpinGlasses

variable {Ξ : Type*}

/-- The partition sum `∑_α w_α g(d (r, α)) exp (X (Ω_α))` of the Ruelle cascade with vertex data
`d (p, γ) = (blocks, labels)`, where `Ω_α` is the vector of labels along the path to `α`. -/
noncomputable def cascadeMarkedSum (r : ℕ) (X : (Fin r → Ξ) → ℝ)
    (g : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) → ℝ≥0∞)
    (d : (Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) : ℝ≥0∞ :=
  ∑' α : Fin r → ℕ, cascadeBranchWeight (fun p γ m => nthLargestAtom m (poissonCountingMeasure
      (fun k => ((d ⟨p, γ⟩).1 k).1) (fun k l => ((d ⟨p, γ⟩).1 k).2 l))) α * g (d ⟨r, α⟩) *
    ENNReal.ofReal (Real.exp (X fun i : Fin r => (d ⟨i, Fin.take i i.isLt.le α⟩).2 (α i)))

/-- Peeling the first level of the cascade. -/
theorem cascadeMarkedSum_succ (r : ℕ) (X : (Fin (r + 1) → Ξ) → ℝ)
    (g : (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ) → ℝ≥0∞)
    (d : (Σ p : ℕ, Fin p → ℕ) → (ℕ → ℕ × (ℕ → ℝ)) × (ℕ → Ξ)) :
    cascadeMarkedSum (r + 1) X g d =
      ∑' n, nthLargestAtom n (poissonCountingMeasure
          (fun k => ((d ⟨0, fun i => i.elim0⟩).1 k).1)
          (fun k l => ((d ⟨0, fun i => i.elim0⟩).1 k).2 l)) *
        cascadeMarkedSum r (fun θ => X (Fin.cons ((d ⟨0, fun i => i.elim0⟩).2 n) θ)) g
          (fun v => d ⟨v.1 + 1, Fin.cons n v.2⟩) := by
  unfold cascadeMarkedSum
  rw [← (Fin.consEquiv (fun _ : Fin (r + 1) => ℕ)).tsum_eq]
  change (∑' c : ℕ × (Fin r → ℕ), _) = _
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun n => ?_
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun β => ?_
  have hce : ∀ (n : ℕ) (β : Fin r → ℕ),
      (Fin.consEquiv (fun _ : Fin (r + 1) => ℕ)) (n, β) = Fin.cons n β := fun _ _ => rfl
  simp only [hce]
  rw [cascadeBranchWeight_cons]
  have hpath : (fun i : Fin (r + 1) =>
      (d ⟨i, Fin.take i i.isLt.le (Fin.cons n β : Fin (r + 1) → ℕ)⟩).2
        ((Fin.cons n β : Fin (r + 1) → ℕ) i)) =
      Fin.cons ((d ⟨0, fun i => i.elim0⟩).2 n)
        (fun i : Fin r => (d ⟨i.val + 1, Fin.cons n (Fin.take i i.isLt.le β)⟩).2 (β i)) := by
    funext i
    cases i using Fin.cases with
    | zero =>
      have h0 : ∀ (h : 0 ≤ r + 1) (c : Fin (r + 1) → ℕ),
          Fin.take 0 h c = fun i : Fin 0 => i.elim0 := fun _ _ => funext fun i => Fin.elim0 i
      simp only [Fin.cons_zero, Fin.val_zero]
      rw [h0 (Nat.zero_le _)]
    | succ k =>
      simp only [Fin.cons_succ, Fin.val_succ]
      rw [take_succ_cons n β k _ k.isLt.le]
  simp only [hpath]
  ring

end SpinGlasses
