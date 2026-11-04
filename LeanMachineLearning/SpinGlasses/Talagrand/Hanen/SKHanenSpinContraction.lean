/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenVanishing
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.CoordinatePair

/-!
# Exact spin contractions for surviving Hanen terms

A spin-difference pair with one selected endpoint contracts to a signed inverse cosh square.
The remaining observable may be arbitrary provided it is invariant under updates at that pair.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real
namespace SpinGlasses

/-- The mean of a single spin with energy `s*Y` is `tanh Y`. -/
theorem integral_count_tilted_spin_eq_tanh (Y : ℝ) :
    (∫ s : ℤˣ, (s : ℝ) ∂Measure.count.tilted (fun s : ℤˣ => (s : ℝ) * Y)) =
      Real.tanh Y := by
  rw [integral_count_tilted, sum_units_int, sum_units_int]
  simp only [Units.val_one, Units.val_neg, Int.cast_neg, Int.cast_one, one_mul, neg_one_mul,
    mul_one, mul_neg_one]
  rw [Real.tanh_eq]
  ring

/-- A spin difference times its first endpoint contracts to the spin variance. -/
theorem integral_spin_diff_mul_left_of_invariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : ℝ) (x y : ι) (hxy : x ≠ y) (G : (ι → ℤˣ) → ℝ)
    (hx : ∀ ε t, G (Function.update ε x t) = G ε)
    (hy : ∀ ε t, G (Function.update ε y t) = G ε) :
    (∫ ε : ι → ℤˣ, ((ε x : ℝ) - (ε y : ℝ)) * (ε x : ℝ) * G ε
      ∂(Measure.pi fun _ : ι => Measure.count.tilted fun s : ℤˣ => (s : ℝ) * Y)) =
      ((Real.cosh Y)⁻¹) ^ 2 *
        ∫ ε : ι → ℤˣ, G ε
          ∂(Measure.pi fun _ : ι => Measure.count.tilted fun s : ℤˣ => (s : ℝ) * Y) := by
  rw [integral_pi_mul_pair_of_invariant _ x y hxy
    (fun a b : ℤˣ => ((a : ℝ) - (b : ℝ)) * (a : ℝ)) G hx hy]
  congr 1
  have hin (a : ℤˣ) :
      (∫ b : ℤˣ, ((a : ℝ) - (b : ℝ)) * (a : ℝ)
        ∂Measure.count.tilted (fun s : ℤˣ => (s : ℝ) * Y)) =
      1 - Real.tanh Y * (a : ℝ) := by
    simp_rw [sub_mul, ← pow_two, units_cast_sq,
      integral_sub Integrable.of_finite Integrable.of_finite,
      integral_const, probReal_univ, one_smul, integral_mul_const,
      integral_count_tilted_spin_eq_tanh]
  simp_rw [hin]
  rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_const,
    probReal_univ, one_smul, integral_const_mul, integral_count_tilted_spin_eq_tanh,
    ← pow_two, Real.one_sub_tanh_sq_eq_inv_cosh_sq]

/-- Selecting the second endpoint reverses the sign of the contraction. -/
theorem integral_spin_diff_mul_selected_of_invariant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : ℝ) (x y : ι) (hxy : x ≠ y) (b : Bool) (G : (ι → ℤˣ) → ℝ)
    (hx : ∀ ε t, G (Function.update ε x t) = G ε)
    (hy : ∀ ε t, G (Function.update ε y t) = G ε) :
    (∫ ε : ι → ℤˣ, ((ε x : ℝ) - (ε y : ℝ)) *
        (ε (if b then x else y) : ℝ) * G ε
      ∂(Measure.pi fun _ : ι => Measure.count.tilted fun s : ℤˣ => (s : ℝ) * Y)) =
      (if b then (1 : ℝ) else -1) * ((Real.cosh Y)⁻¹) ^ 2 *
        ∫ ε : ι → ℤˣ, G ε
          ∂(Measure.pi fun _ : ι => Measure.count.tilted fun s : ℤˣ => (s : ℝ) * Y) := by
  cases b with
  | true => simpa using integral_spin_diff_mul_left_of_invariant Y x y hxy G hx hy
  | false =>
    simp only [Bool.false_eq_true, ite_false, neg_one_mul]
    have he (ε : ι → ℤˣ) : ((ε x : ℝ) - (ε y : ℝ)) * (ε y : ℝ) * G ε =
        -(((ε y : ℝ) - (ε x : ℝ)) * (ε y : ℝ) * G ε) := by ring
    simp_rw [he, integral_neg]
    rw [integral_spin_diff_mul_left_of_invariant Y y x hxy.symm G hy hx]
    ring

/-- A product of disjoint spin-difference pairs, each hit at one selected endpoint,
contracts to the product of its orientation signs times `cosh(Y)^(-2*card V)`.
The untouched factor may be any function of the remaining replicas. -/
theorem integral_spin_diff_prod_selected {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (Y : ℝ) (V : Finset κ) (pairMap : κ → ι × ι)
    (hxy : ∀ v ∈ V, (pairMap v).1 ≠ (pairMap v).2)
    (hdisj : ∀ u ∈ V, ∀ v ∈ V, u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (b : κ → Bool) (fhat : (ι → ℤˣ) → ℝ)
    (hfhat : ∀ (ε : ι → ℤˣ) (i : ι) (t : ℤˣ),
      i ∈ V.biUnion (fun v => {(pairMap v).1, (pairMap v).2}) →
      fhat (Function.update ε i t) = fhat ε) :
    (∫ ε : ι → ℤˣ, (∏ v ∈ V,
        (((ε (pairMap v).1 : ℝ) - (ε (pairMap v).2 : ℝ)) *
          (ε (if b v then (pairMap v).1 else (pairMap v).2) : ℝ))) * fhat ε
      ∂(Measure.pi fun _ : ι => Measure.count.tilted fun s : ℤˣ => (s : ℝ) * Y)) =
      (∏ v ∈ V, if b v then (1 : ℝ) else -1) * ((Real.cosh Y)⁻¹) ^ (2 * V.card) *
        ∫ ε : ι → ℤˣ, fhat ε
          ∂(Measure.pi fun _ : ι => Measure.count.tilted fun s : ℤˣ => (s : ℝ) * Y) := by
  revert hxy hdisj hfhat
  induction V using Finset.cons_induction with
  | empty => intros; simp
  | cons v V hv ih =>
    intro hxy hdisj hfhat
    let G : (ι → ℤˣ) → ℝ := fun ε => (∏ w ∈ V,
      (((ε (pairMap w).1 : ℝ) - (ε (pairMap w).2 : ℝ)) *
        (ε (if b w then (pairMap w).1 else (pairMap w).2) : ℝ))) * fhat ε
    have hG (i : ι) (hi : i = (pairMap v).1 ∨ i = (pairMap v).2)
        (ε : ι → ℤˣ) (t : ℤˣ) : G (Function.update ε i t) = G ε := by
      dsimp only [G]
      rw [hfhat ε i t (mem_biUnion.mpr ⟨v, mem_cons_self _ _, by simpa using hi⟩)]
      congr 1
      apply prod_congr rfl
      intro w hw
      have hvw : v ≠ w := by
        intro heq
        subst w
        exact hv hw
      obtain ⟨h1, h2, h3, h4⟩ := hdisj v (mem_cons_self _ _) w (mem_cons_of_mem hw) hvw
      have hn1 : (pairMap w).1 ≠ i := by
        rcases hi with rfl | rfl
        · exact h1.symm
        · exact h3.symm
      have hn2 : (pairMap w).2 ≠ i := by
        rcases hi with rfl | rfl
        · exact h2.symm
        · exact h4.symm
      cases b w <;> simp only [Bool.false_eq_true, ite_false, ite_true,
        Function.update_of_ne hn1, Function.update_of_ne hn2]
    have he (ε : ι → ℤˣ) : (∏ w ∈ cons v V hv,
        (((ε (pairMap w).1 : ℝ) - (ε (pairMap w).2 : ℝ)) *
          (ε (if b w then (pairMap w).1 else (pairMap w).2) : ℝ))) * fhat ε =
        ((ε (pairMap v).1 : ℝ) - (ε (pairMap v).2 : ℝ)) *
          (ε (if b v then (pairMap v).1 else (pairMap v).2) : ℝ) * G ε := by
      rw [prod_cons]
      dsimp only [G]
      ring
    simp_rw [he]
    rw [integral_spin_diff_mul_selected_of_invariant Y _ _
      (hxy v (mem_cons_self _ _)) (b v) G (hG _ (Or.inl rfl)) (hG _ (Or.inr rfl))]
    have hrest := ih (fun w hw => hxy w (mem_cons_of_mem hw))
      (fun u hu w hw huw => hdisj u (mem_cons_of_mem hu) w (mem_cons_of_mem hw) huw)
      (fun ε i t hi => hfhat ε i t (by
        obtain ⟨w, hw, hi⟩ := mem_biUnion.mp hi
        exact mem_biUnion.mpr ⟨w, mem_cons_of_mem hw, hi⟩))
    change (if b v then (1 : ℝ) else -1) * (Real.cosh Y)⁻¹ ^ 2 *
      (∫ ε : ι → ℤˣ, G ε ∂(Measure.pi fun _ : ι =>
        Measure.count.tilted fun s : ℤˣ => (s : ℝ) * Y)) = _
    rw [hrest]
    simp only [prod_cons, card_cons, Nat.mul_add, Nat.mul_one, pow_add]
    ring

/-- Evaluate the spin factor of a surviving derivative tuple, after its endpoint bijection
and orientations have been identified. The bijection is the one provided by critical survival. -/
theorem integral_spin_diff_prod_endpoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Y : ℝ) (m : ℕ) (pairMap : Fin (2 * m) → ι × ι)
    (hxy : ∀ v, (pairMap v).1 ≠ (pairMap v).2)
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (p : Fin m → ι × ι) (e : Fin (2 * m) ≃ Fin m × Bool) (b : Fin (2 * m) → Bool)
    (he : ∀ v, (if (e v).2 then (p (e v).1).1 else (p (e v).1).2) =
      if b v then (pairMap v).1 else (pairMap v).2)
    (fhat : (ι → ℤˣ) → ℝ)
    (hfhat : ∀ (ε : ι → ℤˣ) (i : ι) (t : ℤˣ),
      i ∈ (univ : Finset (Fin (2 * m))).biUnion
        (fun v => {(pairMap v).1, (pairMap v).2}) →
      fhat (Function.update ε i t) = fhat ε) :
    (∫ ε : ι → ℤˣ,
        (∏ v : Fin (2 * m), ((ε (pairMap v).1 : ℝ) - (ε (pairMap v).2 : ℝ))) *
        (∏ j : Fin m, (ε (p j).1 : ℝ) * (ε (p j).2 : ℝ)) * fhat ε
      ∂(Measure.pi fun _ : ι => Measure.count.tilted fun s : ℤˣ => (s : ℝ) * Y)) =
      (∏ v : Fin (2 * m), if b v then (1 : ℝ) else -1) *
        ((Real.cosh Y)⁻¹) ^ (4 * m) *
        ∫ ε : ι → ℤˣ, fhat ε
          ∂(Measure.pi fun _ : ι => Measure.count.tilted fun s : ℤˣ => (s : ℝ) * Y) := by
  have hprod (ε : ι → ℤˣ) : (∏ j : Fin m, (ε (p j).1 : ℝ) * (ε (p j).2 : ℝ)) =
      ∏ v : Fin (2 * m), (ε (if b v then (pairMap v).1 else (pairMap v).2) : ℝ) := by
    calc
      _ = ∏ j : Fin m × Bool,
          (ε (if j.2 then (p j.1).1 else (p j.1).2) : ℝ) := by
        simp [Fintype.prod_prod_type]
      _ = ∏ v : Fin (2 * m),
          (ε (if (e v).2 then (p (e v).1).1 else (p (e v).1).2) : ℝ) :=
        (e.prod_comp _).symm
      _ = _ := prod_congr rfl fun v _ => congrArg (fun i => (ε i : ℝ)) (he v)
  simp_rw [hprod, ← prod_mul_distrib]
  simpa only [card_univ, Fintype.card_fin, ← Nat.mul_assoc, Nat.reduceMul] using
    integral_spin_diff_prod_selected Y univ pairMap (fun v _ => hxy v)
      (fun u _ v _ huv => hdisj u v huv) b fhat hfhat

end SpinGlasses
