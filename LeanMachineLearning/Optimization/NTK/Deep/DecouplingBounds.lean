/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.Optimization.NTK.Deep.BackwardAlgebra
public import LeanMachineLearning.Optimization.NTK.Initialization.ResidualConcentration

/-!
# Convergence-in-Measure Consequences of the Backward Algebra

Probabilistic (but network-free) corollaries of `Deep/BackwardAlgebra.lean`. Throughout, a
"tight" ingredient is one that converges in measure to *some* constant.

* `tendstoInMeasure_wsq_mulVec`: if `w n → 0` coordinatewise and the fourth-moment averages of `f`
  and of the columns of `Φ` converge, then `N_f(Φ w) = n⁻¹ ∑ⱼ fⱼ² (Φ w)ⱼ² → 0`. This is the
  projected part of the back-propagated vector.
* `tendstoInMeasure_inv_nat_mul_trace`: `n⁻¹ ∑_{ab} S_{ab} M(f,g)_{ba} → 0` if the entries of `S`
  converge and the fourth-moment averages converge. This is `n⁻¹ tr(D P) → 0`.
-/

@[expose]
public section

open MeasureTheory Filter Matrix
open scoped Matrix BigOperators

namespace NTK

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m : ℕ}

/-- Finite sums of sequences tending to `0` in measure tend to `0` in measure. -/
lemma tendstoInMeasure_sum_zero {ι : Type*} [Fintype ι] {f : ι → ℕ → Ω → ℝ}
    (h : ∀ i, TendstoInMeasure μ (f i) atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω => ∑ i, f i n ω) atTop (fun _ => 0) := by
  have := tendstoInMeasure_sum_mul (μ := μ) (a := f) (b := fun _ _ _ => (1 : ℝ))
    (a' := fun _ => 0) (b' := fun _ => 1) h (fun _ => tendstoInMeasure_const 1)
  simpa using this

/-- Absolute values of sequences tending to `0` in measure tend to `0` in measure. -/
lemma tendstoInMeasure_abs_zero {f : ℕ → Ω → ℝ}
    (h : TendstoInMeasure μ f atTop (fun _ => 0)) :
    TendstoInMeasure μ (fun n ω => |f n ω|) atTop (fun _ => 0) :=
  tendstoInMeasure_zero_of_abs_le (fun n ω => by simp) (g := fun n ω => |f n ω|) (by
    simpa using tendstoInMeasure_comp_of_continuousAt (g := fun x : ℝ => |x|) h
      continuous_abs.continuousAt)

/-- Absolute values of convergent sequences converge. -/
lemma tendstoInMeasure_abs {f : ℕ → Ω → ℝ} {c : ℝ}
    (h : TendstoInMeasure μ f atTop (fun _ => c)) :
    TendstoInMeasure μ (fun n ω => |f n ω|) atTop (fun _ => |c|) :=
  tendstoInMeasure_comp_of_continuousAt (g := fun x : ℝ => |x|) h continuous_abs.continuousAt

/-- Entrywise convergence in measure of a matrix sequence is convergence in measure. -/
lemma tendstoInMeasure_matrix_of_entries {F : ℕ → Ω → Matrix (Fin m) (Fin m) ℝ}
    {M : Matrix (Fin m) (Fin m) ℝ}
    (h : ∀ a b, TendstoInMeasure μ (fun (n : ℕ) (ω : Ω) => F n ω a b) atTop (fun _ => M a b)) :
    TendstoInMeasure μ F atTop (fun _ => M) :=
  tendstoInMeasure_pi (E := fun _ : Fin m => Fin m → ℝ) (f := fun n ω a => F n ω a)
    (c := fun a => M a) fun a => tendstoInMeasure_pi fun b => h a b

/-- The Cauchy–Schwarz bound `3 (xa xb + xa yb + ya xb)` tends to `0` when `xa, xb → 0` and
`ya, yb` converge. -/
lemma tendstoInMeasure_three_terms {xa xb ya yb : ℕ → Ω → ℝ} {cya cyb : ℝ}
    (hxa : TendstoInMeasure μ xa atTop (fun _ => 0))
    (hxb : TendstoInMeasure μ xb atTop (fun _ => 0))
    (hya : TendstoInMeasure μ ya atTop (fun _ => cya))
    (hyb : TendstoInMeasure μ yb atTop (fun _ => cyb)) :
    TendstoInMeasure μ (fun n ω => 3 * (xa n ω * xb n ω + xa n ω * yb n ω + ya n ω * xb n ω))
      atTop (fun _ => 0) := by
  have h1 := tendstoInMeasure_mul hxa hxb
  have h2 := tendstoInMeasure_mul hxa hyb
  have h3 := tendstoInMeasure_mul hya hxb
  have h := tendstoInMeasure_mul (tendstoInMeasure_const (μ := μ) (3 : ℝ))
    (tendstoInMeasure_add (tendstoInMeasure_add h1 h2) h3)
  simpa using h

/-- A product of two sequences tending to `0` and one convergent sequence tends to `0`. -/
lemma tendstoInMeasure_mul_mul_zero {a b c : ℕ → Ω → ℝ} {γ : ℝ}
    (ha : TendstoInMeasure μ a atTop (fun _ => 0)) (hb : TendstoInMeasure μ b atTop (fun _ => 0))
    (hc : TendstoInMeasure μ c atTop (fun _ => γ)) :
    TendstoInMeasure μ (fun n ω => a n ω * b n ω * c n ω) atTop (fun _ => 0) := by
  have := tendstoInMeasure_mul (tendstoInMeasure_mul ha hb) hc
  simpa using this

/-- Half-sums of convergent sequences converge. -/
lemma tendstoInMeasure_half_sum {A₁ A₂ : ℕ → Ω → ℝ} {c₁ c₂ : ℝ}
    (h₁ : TendstoInMeasure μ A₁ atTop (fun _ => c₁))
    (h₂ : TendstoInMeasure μ A₂ atTop (fun _ => c₂)) :
    TendstoInMeasure μ (fun n ω => (A₁ n ω + A₂ n ω) / 2) atTop (fun _ => (c₁ + c₂) / 2) := by
  have h := tendstoInMeasure_mul (tendstoInMeasure_const (μ := μ) ((2 : ℝ)⁻¹))
    (tendstoInMeasure_add h₁ h₂)
  have e : (fun (n : ℕ) (ω : Ω) => (A₁ n ω + A₂ n ω) / 2) =
      fun n ω => (2 : ℝ)⁻¹ * (A₁ n ω + A₂ n ω) := by
    funext n ω; ring
  rw [e]
  convert h using 2
  ring

/-- The normalized fourth-moment bound `(avg4 f + avg4 g + avg4 a + avg4 b) / 4` of a weighted Gram
entry converges when its four ingredients do. -/
lemma tendstoInMeasure_quarter_sum {A₁ A₂ A₃ A₄ : ℕ → Ω → ℝ} {c₁ c₂ c₃ c₄ : ℝ}
    (h₁ : TendstoInMeasure μ A₁ atTop (fun _ => c₁))
    (h₂ : TendstoInMeasure μ A₂ atTop (fun _ => c₂))
    (h₃ : TendstoInMeasure μ A₃ atTop (fun _ => c₃))
    (h₄ : TendstoInMeasure μ A₄ atTop (fun _ => c₄)) :
    TendstoInMeasure μ (fun n ω => (A₁ n ω + A₂ n ω + A₃ n ω + A₄ n ω) / 4) atTop
      (fun _ => (c₁ + c₂ + c₃ + c₄) / 4) := by
  have h := tendstoInMeasure_mul (tendstoInMeasure_const (μ := μ) ((4 : ℝ)⁻¹))
    (tendstoInMeasure_add (tendstoInMeasure_add (tendstoInMeasure_add h₁ h₂) h₃) h₄)
  have e : (fun (n : ℕ) (ω : Ω) => (A₁ n ω + A₂ n ω + A₃ n ω + A₄ n ω) / 4) =
      fun n ω => (4 : ℝ)⁻¹ * (A₁ n ω + A₂ n ω + A₃ n ω + A₄ n ω) := by
    funext n ω; ring
  rw [e]
  convert h using 2
  ring

/-- **`N_f(Φ w) → 0`.** -/
theorem tendstoInMeasure_wsq_mulVec
    (f : ∀ n : ℕ, Ω → Fin n → ℝ) (Φ : ∀ n : ℕ, Ω → Matrix (Fin n) (Fin m) ℝ)
    (w : ℕ → Ω → Fin m → ℝ)
    (hw : ∀ a, TendstoInMeasure μ (fun (n : ℕ) (ω : Ω) => w n ω a) atTop (fun _ => 0))
    (hf : ∃ c : ℝ, TendstoInMeasure μ (fun (n : ℕ) (ω : Ω) => avg4 (f n ω)) atTop (fun _ => c))
    (hΦ : ∀ a, ∃ c : ℝ, TendstoInMeasure μ
      (fun (n : ℕ) (ω : Ω) => avg4 (fun j => Φ n ω j a)) atTop (fun _ => c)) :
    TendstoInMeasure μ (fun (n : ℕ) (ω : Ω) => wsq (f n ω) (Φ n ω *ᵥ w n ω)) atTop
      (fun _ => 0) := by
  obtain ⟨cf, hcf⟩ := hf
  choose cΦ hcΦ using hΦ
  obtain ⟨T, hT⟩ : ∃ T : Fin m × Fin m → ℕ → Ω → ℝ, ∀ ab n ω, T ab n ω =
      |w n ω ab.1| * |w n ω ab.2| *
        ((avg4 (f n ω) + avg4 (f n ω) + avg4 (fun j => Φ n ω j ab.1) +
          avg4 (fun j => Φ n ω j ab.2)) / 4) := ⟨_, fun _ _ _ => rfl⟩
  have hT0 : ∀ ab, TendstoInMeasure μ (T ab) atTop (fun _ => 0) := by
    intro ab
    have e : T ab = fun n ω => |w n ω ab.1| * |w n ω ab.2| *
        ((avg4 (f n ω) + avg4 (f n ω) + avg4 (fun j => Φ n ω j ab.1) +
          avg4 (fun j => Φ n ω j ab.2)) / 4) := funext fun n => funext fun ω => hT ab n ω
    rw [e]
    exact tendstoInMeasure_mul_mul_zero (tendstoInMeasure_abs_zero (hw ab.1))
      (tendstoInMeasure_abs_zero (hw ab.2))
      (tendstoInMeasure_quarter_sum hcf hcf (hcΦ ab.1) (hcΦ ab.2))
  have hsum := tendstoInMeasure_sum_zero hT0
  refine tendstoInMeasure_zero_of_abs_le (fun n ω => ?_) hsum
  rw [wsq_mulVec_eq, Fintype.sum_prod_type]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [hT]
  simp only [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_wmat_le _ _ _ a b) (by positivity)

/-- **`n⁻¹ tr(D P) → 0`.** If the entries of `S n` converge and the fourth-moment averages of
`f, g` and of the columns of `Φ` converge, then `n⁻¹ ∑_{ab} S_{ab} M(f,g)_{ba} → 0`. -/
theorem tendstoInMeasure_inv_nat_mul_trace
    (f g : ∀ n : ℕ, Ω → Fin n → ℝ) (Φ : ∀ n : ℕ, Ω → Matrix (Fin n) (Fin m) ℝ)
    (S : ℕ → Ω → Matrix (Fin m) (Fin m) ℝ)
    (hS : ∀ a b, ∃ c : ℝ, TendstoInMeasure μ
      (fun (n : ℕ) (ω : Ω) => S n ω a b) atTop (fun _ => c))
    (hf : ∃ c : ℝ, TendstoInMeasure μ (fun (n : ℕ) (ω : Ω) => avg4 (f n ω)) atTop (fun _ => c))
    (hg : ∃ c : ℝ, TendstoInMeasure μ (fun (n : ℕ) (ω : Ω) => avg4 (g n ω)) atTop (fun _ => c))
    (hΦ : ∀ a, ∃ c : ℝ, TendstoInMeasure μ
      (fun (n : ℕ) (ω : Ω) => avg4 (fun j => Φ n ω j a)) atTop (fun _ => c)) :
    TendstoInMeasure μ (fun (n : ℕ) (ω : Ω) =>
      (n : ℝ)⁻¹ * ∑ a, ∑ b, S n ω a b * (𝔼 j, (f n ω) j * (g n ω) j * (Φ n ω) j b *
          (Φ n ω) j a)) atTop
      (fun _ => 0) := by
  obtain ⟨cf, hcf⟩ := hf
  obtain ⟨cg, hcg⟩ := hg
  choose cΦ hcΦ using hΦ
  choose cS hcS using hS
  obtain ⟨U, hU⟩ : ∃ U : Fin m × Fin m → ℕ → Ω → ℝ, ∀ ab n ω, U ab n ω =
      |S n ω ab.1 ab.2| * ((avg4 (f n ω) + avg4 (g n ω) + avg4 (fun j => Φ n ω j ab.2) +
        avg4 (fun j => Φ n ω j ab.1)) / 4) := ⟨_, fun _ _ _ => rfl⟩
  have hU0 : ∀ ab, ∃ c : ℝ, TendstoInMeasure μ (U ab) atTop (fun _ => c) := by
    intro ab
    have e : U ab = fun n ω => |S n ω ab.1 ab.2| * ((avg4 (f n ω) + avg4 (g n ω) +
        avg4 (fun j => Φ n ω j ab.2) + avg4 (fun j => Φ n ω j ab.1)) / 4) :=
      funext fun n => funext fun ω => hU ab n ω
    rw [e]
    exact ⟨_, tendstoInMeasure_mul (tendstoInMeasure_abs (hcS ab.1 ab.2))
      (tendstoInMeasure_quarter_sum hcf hcg (hcΦ ab.2) (hcΦ ab.1))⟩
  choose cU hcU using hU0
  have hsum := tendstoInMeasure_sum_mul (μ := μ) (a := U) (b := fun _ _ _ => (1 : ℝ))
    (a' := cU) (b' := fun _ => 1) hcU (fun _ => tendstoInMeasure_const 1)
  have hscaled := tendstoInMeasure_inv_nat_mul hsum
  refine tendstoInMeasure_zero_of_abs_le (fun n ω => ?_) hscaled
  have hn : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg n)
  rw [abs_mul, abs_of_nonneg hn]
  refine mul_le_mul_of_nonneg_left ?_ hn
  rw [Fintype.sum_prod_type]
  simp only [mul_one]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [abs_mul, hU]
  exact mul_le_mul_of_nonneg_left (abs_wmat_le _ _ _ b a) (abs_nonneg _)

end NTK

end
