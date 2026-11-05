/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPairingFibers

/-!
# Signed evaluation of a term in an ordered-pairing class

The previously proved endpoint contraction applies to every tuple in a class, including
tuples whose integrals vanish. The sign is written directly in terms of the selected replica
endpoints and factors over the matching blocks. No new sign or measure definition is needed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

/-- Evaluate a term in an ordered-pairing class, with its sign already factored over blocks.
The old observable may include the tuple-dependent product of truncated overlaps. -/
theorem skCavityPathMean_zero_fiber_term_eval (N m n : ℕ) (β q h : ℝ)
    (pairMap : Fin (2 * m) → Fin n × Fin n)
    (hxy : ∀ v, (pairMap v).1 ≠ (pairMap v).2)
    (hdisj : ∀ u v : Fin (2 * m), u ≠ v →
      (pairMap u).1 ≠ (pairMap v).1 ∧ (pairMap u).1 ≠ (pairMap v).2 ∧
      (pairMap u).2 ≠ (pairMap v).1 ∧ (pairMap u).2 ≠ (pairMap v).2)
    (Pe : Σ P : Finpartition.Pairing (univ : Finset (Fin (2 * m))), Fin m ≃ P.val.parts)
    (p : Fin m → FinPairs n)
    (hp : ∀ i v, v ∈ (Pe.2 i).val ↔
      (p i).val.1 ∈ ({(pairMap v).1, (pairMap v).2} : Finset (Fin n)) ∨
      (p i).val.2 ∈ ({(pairMap v).1, (pairMap v).2} : Finset (Fin n)))
    (F : (Fin n → Fin N → ℤˣ) → ℝ) (fhat : (Fin n → ℤˣ) → ℝ)
    (hfhat : ∀ ε i t,
      i ∈ (univ : Finset (Fin (2 * m))).biUnion
        (fun v => {(pairMap v).1, (pairMap v).2}) →
      fhat (Function.update ε i t) = fhat ε) :
    skCavityPathMean N n β q h 0 (fun σ => F (fun r i => σ r i.castSucc) *
      (∏ v : Fin (2 * m), ((σ (pairMap v).1 (Fin.last N) : ℝ) -
        (σ (pairMap v).2 (Fin.last N) : ℝ))) *
      (∏ r : Fin m, (σ (p r).val.1 (Fin.last N) : ℝ) *
        (σ (p r).val.2 (Fin.last N) : ℝ)) * fhat (fun r => σ r (Fin.last N)) *
      ∏ r : Fin m, ((N + 1 : ℝ)⁻¹ *
        (∑ i : Fin N, (σ (p r).val.1 i.castSucc : ℝ) *
          (σ (p r).val.2 i.castSucc : ℝ)) - q)) =
      (∫ z : ℝ, (∫ ε : Fin n → ℤˣ, fhat ε
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
            fun s : ℤˣ => (s : ℝ) * (β * z * Real.sqrt q + h))) *
        ((Real.cosh (β * z * Real.sqrt q + h))⁻¹) ^ (4 * m) ∂gaussianReal 0 1) *
      (∫ g' : FinPairs N → ℝ, ∫ ρ : Fin n → Fin N → ℤˣ,
        F ρ * ∏ i : Fin m,
          (∏ v ∈ (Pe.2 i).val,
            if (pairMap v).1 ∈ ({(p i).val.1, (p i).val.2} : Finset (Fin n)) then
              (1 : ℝ) else -1) *
          ((N + 1 : ℝ)⁻¹ * (∑ j : Fin N, (ρ (p i).val.1 j : ℝ) *
            (ρ (p i).val.2 j : ℝ)) - q)
        ∂(Measure.pi fun _ : Fin n => Measure.count.tilted (skCavityOldEnergy N β h g'))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) := by
  obtain ⟨e, b, he, _, hb⟩ := Finpartition.exists_endpoint_choices_of_pairing_fiber
    pairMap hxy hdisj Pe (fun i => (p i).val) hp
  have hs : (∏ v : Fin (2 * m), if b v then (1 : ℝ) else -1) =
      ∏ i : Fin m, ∏ v ∈ (Pe.2 i).val,
        if (pairMap v).1 ∈ ({(p i).val.1, (p i).val.2} : Finset (Fin n)) then
          (1 : ℝ) else -1 := by
    calc
      _ = ∏ B ∈ Pe.1.val.parts, ∏ v ∈ B, if b v then (1 : ℝ) else -1 :=
        (Finpartition.prod_parts Pe.1.val _).symm
      _ = ∏ B : Pe.1.val.parts, ∏ v ∈ B.val, if b v then (1 : ℝ) else -1 :=
        (prod_coe_sort _ _).symm
      _ = ∏ i : Fin m, ∏ v ∈ (Pe.2 i).val, if b v then (1 : ℝ) else -1 :=
        (Pe.2.prod_comp _).symm
      _ = _ := by
        apply prod_congr rfl
        intro i _
        apply prod_congr rfl
        intro v hv
        simp only [hb i v hv]
  let Fp : (Fin n → Fin N → ℤˣ) → ℝ := fun ρ => F ρ *
    ∏ r : Fin m, ((N + 1 : ℝ)⁻¹ *
      (∑ i : Fin N, (ρ (p r).val.1 i : ℝ) * (ρ (p r).val.2 i : ℝ)) - q)
  have hfun : (fun σ : Fin n → Fin (N + 1) → ℤˣ => F (fun r i => σ r i.castSucc) *
      (∏ v : Fin (2 * m), ((σ (pairMap v).1 (Fin.last N) : ℝ) -
        (σ (pairMap v).2 (Fin.last N) : ℝ))) *
      (∏ r : Fin m, (σ (p r).val.1 (Fin.last N) : ℝ) *
        (σ (p r).val.2 (Fin.last N) : ℝ)) * fhat (fun r => σ r (Fin.last N)) *
      ∏ r : Fin m, ((N + 1 : ℝ)⁻¹ *
        (∑ i : Fin N, (σ (p r).val.1 i.castSucc : ℝ) *
          (σ (p r).val.2 i.castSucc : ℝ)) - q)) =
      fun σ => Fp (fun r i => σ r i.castSucc) *
        (∏ v : Fin (2 * m), ((σ (pairMap v).1 (Fin.last N) : ℝ) -
          (σ (pairMap v).2 (Fin.last N) : ℝ))) *
        (∏ r : Fin m, (σ (p r).val.1 (Fin.last N) : ℝ) *
          (σ (p r).val.2 (Fin.last N) : ℝ)) * fhat (fun r => σ r (Fin.last N)) := by
    funext σ
    dsimp only [Fp]
    ring
  rw [hfun, skCavityPathMean_zero_tuple_eval N m n β q h pairMap hxy hdisj
    (fun i => (p i).val) e b he Fp fhat hfhat, hs]
  let c : ℝ := ∏ i : Fin m, ∏ v ∈ (Pe.2 i).val,
    if (pairMap v).1 ∈ ({(p i).val.1, (p i).val.2} : Finset (Fin n)) then 1 else -1
  have hR (ρ : Fin n → Fin N → ℤˣ) :
      F ρ * ∏ i : Fin m,
        (∏ v ∈ (Pe.2 i).val,
          if (pairMap v).1 ∈ ({(p i).val.1, (p i).val.2} : Finset (Fin n)) then
            (1 : ℝ) else -1) *
        ((N + 1 : ℝ)⁻¹ * (∑ j : Fin N, (ρ (p i).val.1 j : ℝ) *
          (ρ (p i).val.2 j : ℝ)) - q) = c * Fp ρ := by
    rw [prod_mul_distrib]
    dsimp only [c, Fp]
    ring
  simp_rw [hR, integral_const_mul]
  ring

end SpinGlasses
