/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenRectangular

public import LeanMachineLearning.Optimization.Renormalization.PairingInvolution
public import LeanMachineLearning.Optimization.Renormalization.PairingCardinality
public import LeanMachineLearning.Optimization.Renormalization.PairingWick

/-!
# Hanen pairings and rectangular products

The public involution representation is linked to the generic finite-partition pairing
library. Analytic derivative arguments are kept in `SKHanenPairing.lean`.
-/

@[expose] public section

open Finset
open scoped BigOperators Real Matrix
namespace SpinGlasses

/-- A pairing on `Fin (2 * m)` is a fixed-point-free involution. -/
@[ext, nolint docBlame] structure HanenPairing (m : ℕ) where
  /-- The partner involution matching each replica to its paired replica. -/
  partner : Fin (2 * m) → Fin (2 * m)
  /-- The partner map is an involution ($P^2 = \mathrm{id}$). -/
  involutive : ∀ i, partner (partner i) = i
  /-- No replica is paired with itself. -/
  no_fixed_point : ∀ i, partner i ≠ i

attribute [nolint docBlame] HanenPairing.partner

noncomputable instance (m : ℕ) : Fintype (HanenPairing m) := by
  refine Fintype.ofInjective (fun P => P.partner) fun P Q h => ?_
  cases P; cases Q; congr

/-- The unique empty pairing on `Fin 0`. -/
def hanenPairingZero : HanenPairing 0 where
  partner := fun x => x.elim0
  involutive := fun x => x.elim0
  no_fixed_point := fun x => x.elim0

instance : Unique (HanenPairing 0) where
  default := hanenPairingZero
  uniq := fun P => by
    ext x
    exact x.elim0

/-- Transport Hanen's partner involutions to the existing finite-partition pairing API.
This preserves the public Hanen representation while sharing the weighted pairing recursion. -/
noncomputable def HanenPairing.equivFinpartition (m : ℕ) :
    HanenPairing m ≃ Finpartition.Pairing (univ : Finset (Fin (2 * m))) :=
  (show HanenPairing m ≃ {f : Fin (2 * m) → Fin (2 * m) //
      Function.Involutive f ∧ ∀ i, f i ≠ i} from
    { toFun := fun P => ⟨P.partner, P.involutive, P.no_fixed_point⟩
      invFun := fun f => ⟨f.val, f.property.1, f.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans Finpartition.Pairing.equivInvolution.symm

/-- The transported partition has exactly the blocks specified by the Hanen partner map. -/
@[simp] theorem HanenPairing.part_equivFinpartition {m : ℕ} (P : HanenPairing m)
    (i : Fin (2 * m)) :
    ((HanenPairing.equivFinpartition m) P).val.part i = {i, P.partner i} :=
  Finpartition.Pairing.part_ofInvolution P.partner P.involutive P.no_fixed_point i

/-- Block weights on Hanen's pairings have the same product as in the generic partition API.
The codomain is any commutative monoid; there are no spin or probability assumptions. -/
theorem HanenPairing.blockProduct_equivFinpartition {R : Type*} [CommMonoid R]
    {m : ℕ} (P : HanenPairing m) (w : Finset (Fin (2 * m)) → R) :
    ((HanenPairing.equivFinpartition m) P).blockProduct w =
      ∏ i ∈ univ.filter (fun i => i < P.partner i), w {i, P.partner i} :=
  Finpartition.Pairing.blockProduct_ofInvolution P.partner P.involutive P.no_fixed_point w

/-- The number of Hanen pairings is the standard even Gaussian moment coefficient.
The proof transports the count for arbitrary finite-set pairings. -/
theorem HanenPairing.card (m : ℕ) :
    (Fintype.card (HanenPairing m) : ℝ) =
      ((2 * m).factorial : ℝ) / (2 ^ m * (m.factorial : ℝ)) := by
  apply (eq_div_iff (by positivity : (2 : ℝ) ^ m * (m.factorial : ℝ) ≠ 0)).mpr
  have hc := Finpartition.Pairing.card_mul_two_pow_mul_factorial m
    (univ : Finset (Fin (2 * m))) (by simp)
  rw [← Fintype.card_congr (HanenPairing.equivFinpartition m)] at hc
  exact_mod_cast hc

/-- Truncated rectangular difference $U_J^-$ for two replica pairs. -/
noncomputable def skCavityRectTrunc (N n m : ℕ) (q : ℝ)
    (pairMap : Fin (2 * m) → Fin n × Fin n) (u v : Fin (2 * m))
    (ρ : Fin n → Fin N → ℤˣ) : ℝ :=
  let x1 := (pairMap u).1
  let x2 := (pairMap u).2
  let y1 := (pairMap v).1
  let y2 := (pairMap v).2
  ((N + 1 : ℝ)⁻¹ * ((fun i => (ρ x1 i : ℝ)) ⬝ᵥ (fun i => (ρ y1 i : ℝ))) - q) -
  ((N + 1 : ℝ)⁻¹ * ((fun i => (ρ x2 i : ℝ)) ⬝ᵥ (fun i => (ρ y1 i : ℝ))) - q) -
  ((N + 1 : ℝ)⁻¹ * ((fun i => (ρ x1 i : ℝ)) ⬝ᵥ (fun i => (ρ y2 i : ℝ))) - q) +
  ((N + 1 : ℝ)⁻¹ * ((fun i => (ρ x2 i : ℝ)) ⬝ᵥ (fun i => (ρ y2 i : ℝ))) - q)

/-- Symmetry of $U_{\{u, v\}}^-$ under swapping $u$ and $v$. -/
theorem skCavityRectTrunc_comm (N n m : ℕ) (q : ℝ)
    (pairMap : Fin (2 * m) → Fin n × Fin n) (u v : Fin (2 * m))
    (ρ : Fin n → Fin N → ℤˣ) :
    skCavityRectTrunc N n m q pairMap u v ρ = skCavityRectTrunc N n m q pairMap v u ρ := by
  dsimp only [skCavityRectTrunc]
  have hdot (a b : Fin n) :
      ((fun i => (ρ a i : ℝ)) ⬝ᵥ (fun i => (ρ b i : ℝ))) =
      ((fun i => (ρ b i : ℝ)) ⬝ᵥ (fun i => (ρ a i : ℝ))) := dotProduct_comm _ _
  rw [hdot (pairMap u).1 (pairMap v).1, hdot (pairMap u).2 (pairMap v).1,
      hdot (pairMap u).1 (pairMap v).2, hdot (pairMap u).2 (pairMap v).2]
  ring

/-- The product of truncated rectangular differences over the pairs of a pairing $P$. -/
noncomputable def skCavityPairingRectProd (N n m : ℕ) (q : ℝ)
    (pairMap : Fin (2 * m) → Fin n × Fin n) (P : HanenPairing m)
    (ρ : Fin n → Fin N → ℤˣ) : ℝ :=
  ∏ i ∈ (Finset.univ : Finset (Fin (2 * m))).filter (fun i => i < P.partner i),
    skCavityRectTrunc N n m q pairMap i (P.partner i) ρ

/-- At $m = 0$, the rectangular product is the empty product, which equals 1. -/
@[simp] theorem skCavityPairingRectProd_zero (N n : ℕ) (q : ℝ)
    (pairMap : Fin 0 → Fin n × Fin n) (P : HanenPairing 0)
    (ρ : Fin n → Fin N → ℤˣ) :
    skCavityPairingRectProd N n 0 q pairMap P ρ = 1 := by
  simp [skCavityPairingRectProd]

/-- Rectangular products use the same unordered block weights as the generic Wick library. -/
theorem skCavityPairingRectProd_eq_blockProduct (N n m : ℕ) (q : ℝ)
    (pairMap : Fin (2 * m) → Fin n × Fin n) (P : HanenPairing m)
    (ρ : Fin n → Fin N → ℤˣ) :
    skCavityPairingRectProd N n m q pairMap P ρ =
      ((HanenPairing.equivFinpartition m) P).blockProduct
        (Renormalization.pairWeight fun u v => skCavityRectTrunc N n m q pairMap u v ρ) := by
  rw [HanenPairing.blockProduct_equivFinpartition]
  apply prod_congr rfl
  intro i _
  exact (Renormalization.pairWeight_pair _
    (fun u v => skCavityRectTrunc_comm N n m q pairMap u v ρ)
    (P.no_fixed_point i).symm).symm

/-- The sum of Hanen's rectangular products is the existing Wick sum of the rectangular kernel.
This identifies the whole weighted sum, rather than only the number of pairings. -/
theorem sum_skCavityPairingRectProd_eq_wick (N n m : ℕ) (q : ℝ)
    (pairMap : Fin (2 * m) → Fin n × Fin n) (ρ : Fin n → Fin N → ℤˣ) :
    (∑ P : HanenPairing m, skCavityPairingRectProd N n m q pairMap P ρ) =
      Renormalization.wick (fun u v => skCavityRectTrunc N n m q pairMap u v ρ) univ := by
  simp_rw [skCavityPairingRectProd_eq_blockProduct]
  exact (HanenPairing.equivFinpartition m).sum_comp
    (fun P => P.blockProduct (Renormalization.pairWeight
      fun u v => skCavityRectTrunc N n m q pairMap u v ρ))

end SpinGlasses
