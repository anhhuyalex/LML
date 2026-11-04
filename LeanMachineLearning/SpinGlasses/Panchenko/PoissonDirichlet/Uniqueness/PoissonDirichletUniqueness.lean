/-
Copyright (c) 2026 LML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML contributors
-/
module

public import LeanMachineLearning.SpinGlasses.PoissonDirichletRanked
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# The compact decreasing subprobability simplex

Theorem 2.8 compares probability laws on the compact space of decreasing
nonnegative sequences of total mass at most one. The first-power sum is not
continuous in the product topology. The higher power sums are continuous,
separate points, and generate a dense subalgebra by Stone--Weierstrass.
-/

@[expose] public section

open Set

namespace SpinGlasses

set_option quotPrecheck false in
/-- Panchenko's compact simplex `V` of decreasing subprobability sequences, as notation
for an explicit set (no definition is introduced). The sum is bounded by one, not required
to equal one: mass may escape to zero in the product topology. -/
scoped notation "𝕍" =>
  {x : ℕ → ℝ | (∀ j, 0 ≤ x j) ∧ Antitone x ∧ (∑' j, ENNReal.ofReal (x j)) ≤ 1}

/-- The zero sequence belongs to the simplex. -/
theorem zero_mem_poissonDirichletSimplex : (fun _ : ℕ => (0 : ℝ)) ∈ 𝕍 :=
  ⟨fun _ => le_rfl, fun _ _ _ => le_rfl, by simp⟩

/-- Every coordinate of the decreasing subprobability simplex lies in `[0,1]`. -/
theorem poissonDirichletSimplex_coordinate_mem {x : ℕ → ℝ}
    (hx : x ∈ 𝕍) (j : ℕ) : x j ∈ Set.Icc 0 1 := by
  obtain ⟨hpos, _, hsum⟩ := hx
  refine ⟨hpos j, ?_⟩
  have hle : ENNReal.ofReal (x j) ≤ 1 :=
    (ENNReal.le_tsum j).trans hsum
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1)).mp
    (by simpa only [ENNReal.ofReal_one] using hle)

/-- The simplex is closed in the product topology. The ENNReal summability
bound is the intersection of the closed finite-partial-sum constraints. -/
theorem isClosed_poissonDirichletSimplex : IsClosed 𝕍 := by
  have hpos : IsClosed {x : ℕ → ℝ | ∀ j, 0 ≤ x j} := by
    simp only [show {x : ℕ → ℝ | ∀ j, 0 ≤ x j} =
      ⋂ j, {x | 0 ≤ x j} from Set.ext fun x => by simp]
    exact isClosed_iInter (fun j => isClosed_le continuous_const (continuous_apply j))
  have hanti : IsClosed {x : ℕ → ℝ | Antitone x} := by
    have heq : {x : ℕ → ℝ | Antitone x} =
        ⋂ i : ℕ, ⋂ j : ℕ, if i ≤ j then {x | x j ≤ x i} else Set.univ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      constructor
      · intro hx i j
        split_ifs with hij
        · exact hx hij
        · trivial
      · intro hx i j hij
        simpa [hij] using hx i j
    rw [heq]
    exact isClosed_iInter fun i => isClosed_iInter fun j => by
      split_ifs
      · exact isClosed_le (continuous_apply j) (continuous_apply i)
      · exact isClosed_univ
  have hsum : IsClosed {x : ℕ → ℝ |
      (∑' j, ENNReal.ofReal (x j)) ≤ 1} := by
    have hlim (x : ℕ → ℝ) :
        (∑' j, ENNReal.ofReal (x j)) ≤ 1 ↔
        ∀ s : Finset ℕ, (∑ j ∈ s, ENNReal.ofReal (x j)) ≤ 1 := by
      constructor
      · intro h s
        exact (ENNReal.sum_le_tsum s).trans h
      · intro h
        exact ENNReal.tsum_le_of_sum_range_le fun n => by
          simpa using h (Finset.range n)
    have heq : {x : ℕ → ℝ | (∑' j, ENNReal.ofReal (x j)) ≤ 1} =
        ⋂ s : Finset ℕ, {x | (∑ j ∈ s, ENNReal.ofReal (x j)) ≤ 1} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, hlim]
    rw [heq]
    apply isClosed_iInter
    intro s
    exact isClosed_le (continuous_finsetSum _ fun j hj =>
      ENNReal.continuous_ofReal.comp (continuous_apply j)) continuous_const
  convert (hpos.inter hanti).inter hsum using 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  tauto

/-- The decreasing subprobability simplex is compact. -/
theorem isCompact_poissonDirichletSimplex : IsCompact 𝕍 := by
  have hc : IsCompact {x : ℕ → ℝ | ∀ j, x j ∈ Set.Icc (0 : ℝ) 1} := by
    convert isCompact_univ_pi (fun _ : ℕ =>
      (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))) using 1
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const,
      Set.mem_Icc]
  apply hc.of_isClosed_subset isClosed_poissonDirichletSimplex
  intro x hx j
  exact poissonDirichletSimplex_coordinate_mem hx j

/-- Higher power sums are well-defined on the compact simplex. -/
theorem poissonDirichletSimplex_summable_pow (x : 𝕍)
    (s : ℕ) (hs : 1 ≤ s) : Summable (fun j => (x.1 j) ^ s) := by
  have hbase : Summable (fun j => x.1 j) :=
    summable_of_tsum_ofReal_lt_top x.2.1
      (lt_of_le_of_lt x.2.2.2 ENNReal.one_lt_top)
  apply Summable.of_nonneg_of_le (fun j => pow_nonneg (x.2.1 j) _)
    (fun j => ?_) hbase
  have hbound := poissonDirichletSimplex_coordinate_mem x.2 j
  exact pow_le_of_le_one hbound.1 hbound.2 (by omega)

/-- The real-valued total mass on the simplex is at most one. -/
theorem poissonDirichletSimplex_tsum_le_one (x : 𝕍) :
    (∑' j, x.1 j) ≤ 1 := by
  have hs : Summable (fun j => x.1 j) := by
    simpa only [pow_one] using poissonDirichletSimplex_summable_pow x 1 le_rfl
  rw [← ENNReal.toReal_ofReal (tsum_nonneg x.2.1),
    ENNReal.ofReal_tsum_of_nonneg x.2.1 hs]
  exact ENNReal.toReal_mono ENNReal.one_ne_top x.2.2.2

/-- The simplex condition gives the uniform coordinate decay `x_j ≤ 1/(j+1)`.
This is the key quantitative input for uniform convergence of power sums
of degree at least two. -/
theorem poissonDirichletSimplex_coordinate_le_inv (x : 𝕍)
    (j : ℕ) : x.1 j ≤ 1 / ((j : ℝ) + 1) := by
  have hsum := poissonDirichletSimplex_tsum_le_one x
  have hprefix : ∑ k ∈ Finset.range (j + 1), x.1 k ≤ 1 :=
    (Summable.sum_le_tsum (Finset.range (j + 1))
      (fun k _ => x.2.1 k)
      (by simpa only [pow_one] using
        poissonDirichletSimplex_summable_pow x 1 (by omega))).trans hsum
  have hanti : ∀ k ∈ Finset.range (j + 1), x.1 j ≤ x.1 k := by
    intro k hk
    exact x.2.2.1 (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hle : ((j : ℝ) + 1) * x.1 j ≤ 1 := by
    have h := Finset.sum_le_sum hanti
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one] using h.trans hprefix
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)).2
    (by simpa only [mul_comm] using hle)

/-- Power sums of degree at least two are continuous on the compact simplex
in the product topology: the uniform envelope is `(j+1)⁻²`. -/
theorem continuousOn_poissonDirichletSimplex_powerSum (s : ℕ) (hs : 2 ≤ s) :
    ContinuousOn (fun x : ℕ → ℝ => ∑' j, (x j) ^ s)
      𝕍 := by
  have hmajor : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
    convert (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num) using 1
    ext j
    simp only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1)]
    norm_num [Real.rpow_natCast]
  apply continuousOn_tsum
    (fun j => ((continuous_apply j).pow s).continuousOn) hmajor
  intro j x hx
  change ‖x j ^ s‖ ≤ 1 / ((j : ℝ) + 1) ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hx.1 j) _)]
  have hbound : 0 ≤ 1 / ((j : ℝ) + 1) ∧ 1 / ((j : ℝ) + 1) ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)).2
        (by nlinarith [Nat.cast_nonneg (α := ℝ) j])
  calc
    x j ^ s ≤ (1 / ((j : ℝ) + 1)) ^ s :=
      pow_le_pow_left₀ (hx.1 j)
        (poissonDirichletSimplex_coordinate_le_inv ⟨x, hx⟩ j) _
    _ ≤ 1 / ((j : ℝ) + 1) ^ 2 := by
      simpa only [one_div_pow] using pow_le_pow_of_le_one hbound.1 hbound.2 hs

/-- A power sum is at least the power of the largest coordinate. -/
theorem poissonDirichletSimplex_first_pow_le_powerSum
    (x : 𝕍) (s : ℕ) (hs : 1 ≤ s) :
    x.1 0 ^ s ≤ ∑' j, x.1 j ^ s := by
  simpa using (poissonDirichletSimplex_summable_pow x s hs).sum_le_tsum
    {0} (fun j hj => pow_nonneg (x.2.1 j) _)

/-- The total-mass constraint controls all higher moments by the first
coordinate: `p_(s+1)(x) ≤ x₀^s`. -/
theorem poissonDirichletSimplex_powerSum_le_first_pow
    (x : 𝕍) (s : ℕ) :
    (∑' j, x.1 j ^ (s + 1)) ≤ x.1 0 ^ s := by
  have hs := poissonDirichletSimplex_summable_pow x (s + 1) (by omega)
  have hbase := poissonDirichletSimplex_summable_pow x 1 (by omega)
  have hmass := poissonDirichletSimplex_tsum_le_one x
  calc
    (∑' j, x.1 j ^ (s + 1)) ≤ ∑' j, x.1 0 ^ s * x.1 j := by
      apply hs.tsum_le_tsum (fun j => by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (x.2.1 j) (x.2.2.1 (Nat.zero_le j)) s)
          (x.2.1 j))
      simpa only [pow_one] using hbase.mul_left (x.1 0 ^ s)
    _ = x.1 0 ^ s * ∑' j, x.1 j := by rw [tsum_mul_left]
    _ ≤ x.1 0 ^ s := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hmass (pow_nonneg (x.2.1 0) _)

/-- A strict inequality between the largest coordinates is incompatible
with equality of all higher power sums. -/
private theorem poissonDirichletSimplex_first_not_lt_of_powerSums_eq
    (x y : 𝕍)
    (h : ∀ s : ℕ, 2 ≤ s →
      (∑' j, x.1 j ^ s) = ∑' j, y.1 j ^ s) :
    ¬ y.1 0 < x.1 0 := by
  intro hlt
  have hypos : 0 < x.1 0 := lt_of_le_of_lt (y.2.1 0) hlt
  have hr : 0 ≤ y.1 0 / x.1 0 := div_nonneg (y.2.1 0) hypos.le
  have hrlt : y.1 0 / x.1 0 < 1 := (div_lt_one hypos).2 hlt
  have hbound (s : ℕ) :
      x.1 0 ^ (s + 2) ≤ y.1 0 ^ (s + 1) := by
    calc
      x.1 0 ^ (s + 2) ≤ ∑' j, x.1 j ^ (s + 2) :=
        poissonDirichletSimplex_first_pow_le_powerSum x _ (by omega)
      _ = ∑' j, y.1 j ^ (s + 2) := h _ (by omega)
      _ ≤ y.1 0 ^ (s + 1) :=
        poissonDirichletSimplex_powerSum_le_first_pow y _
  have hratio (s : ℕ) : x.1 0 ≤ (y.1 0 / x.1 0) ^ s := by
    have hb := hbound s
    have hs : 0 < x.1 0 ^ (s + 1) := pow_pos hypos _
    have hd : x.1 0 ≤ (y.1 0 ^ (s + 1)) / (x.1 0 ^ (s + 1)) := by
      apply (le_div_iff₀ hs).2
      nlinarith [pow_succ (x.1 0) (s + 1)]
    calc
      x.1 0 ≤ (y.1 0 / x.1 0) ^ (s + 1) := by
        simpa only [div_pow] using hd
      _ ≤ (y.1 0 / x.1 0) ^ s := by
        rw [pow_succ]
        exact mul_le_of_le_one_right (pow_nonneg hr _) hrlt.le
  have hz := ge_of_tendsto (tendsto_pow_atTop_nhds_zero_of_lt_one hr hrlt)
    (Filter.Eventually.of_forall hratio)
  exact (not_le_of_gt hypos) hz

/-- Equality of all higher power sums identifies the largest coordinate.
Together with tail subtraction, this is an alternative to the atomic-measure
moment argument for separating points of the simplex. -/
theorem poissonDirichletSimplex_first_eq_of_powerSums_eq
    (x y : 𝕍)
    (h : ∀ s : ℕ, 2 ≤ s →
      (∑' j, x.1 j ^ s) = ∑' j, y.1 j ^ s) :
    x.1 0 = y.1 0 := by
  apply le_antisymm
  · exact le_of_not_gt (poissonDirichletSimplex_first_not_lt_of_powerSums_eq x y h)
  · exact le_of_not_gt (poissonDirichletSimplex_first_not_lt_of_powerSums_eq
      y x (fun s hs => (h s hs).symm))

/-- Removing the first coordinate preserves the decreasing subprobability simplex. -/
theorem poissonDirichletSimplex_tail (x : 𝕍) :
    (fun j => x.1 (j + 1)) ∈ 𝕍 := by
  refine ⟨(fun j => x.2.1 (j + 1)), ?_, ?_⟩
  · intro i j hij
    exact x.2.2.1 (Nat.add_le_add_right hij 1)
  · have hsum : (∑' j, ENNReal.ofReal (x.1 (j + 1))) ≤
        ∑' j, ENNReal.ofReal (x.1 j) :=
      (ENNReal.summable
        (f := fun j : ℕ => ENNReal.ofReal (x.1 (j + 1)))).tsum_le_tsum_of_inj
        (fun j : ℕ => j + 1) (fun i j hij => Nat.add_right_cancel hij)
        (fun _ _ => zero_le) (fun _ => le_rfl) ENNReal.summable
    exact hsum.trans x.2.2.2

/-- Equal higher power sums and equal first coordinates pass to the tails. -/
theorem poissonDirichletSimplex_tail_powerSums_eq
    (x y : 𝕍) (hfirst : x.1 0 = y.1 0)
    (h : ∀ s : ℕ, 2 ≤ s →
      (∑' j, x.1 j ^ s) = ∑' j, y.1 j ^ s) :
    ∀ s : ℕ, 2 ≤ s →
      (∑' j, x.1 (j + 1) ^ s) = ∑' j, y.1 (j + 1) ^ s := by
  intro s hs
  have hx := (poissonDirichletSimplex_summable_pow x s (by omega)).tsum_eq_zero_add
  have hy := (poissonDirichletSimplex_summable_pow y s (by omega)).tsum_eq_zero_add
  have heq := h s hs
  rw [hx, hy, hfirst] at heq
  exact add_left_cancel heq

/-- All higher power sums separate points of the decreasing simplex.
The proof successively recovers the maximum and removes it; it does not need
any moment-determinacy theorem for an auxiliary atomic measure. -/
theorem poissonDirichletSimplex_eq_of_powerSums_eq
    (x y : 𝕍)
    (h : ∀ s : ℕ, 2 ≤ s →
      (∑' j, x.1 j ^ s) = ∑' j, y.1 j ^ s) : x = y := by
  have hcoord (k : ℕ) : x.1 k = y.1 k := by
    induction k generalizing x y with
    | zero => exact poissonDirichletSimplex_first_eq_of_powerSums_eq x y h
    | succ k ih =>
      let xt : 𝕍 := ⟨_, poissonDirichletSimplex_tail x⟩
      let yt : 𝕍 := ⟨_, poissonDirichletSimplex_tail y⟩
      exact ih xt yt (poissonDirichletSimplex_tail_powerSums_eq x y
        (poissonDirichletSimplex_first_eq_of_powerSums_eq x y h) h)
  exact Subtype.ext (funext hcoord)

/-- The continuous higher power-sum observable on the compact simplex. -/
noncomputable def poissonDirichletPowerSum (s : ℕ) (hs : 2 ≤ s) :
    C(𝕍, ℝ) :=
  ⟨fun x => ∑' j, x.1 j ^ s,
    continuousOn_iff_continuous_domRestrict.mp
      (continuousOn_poissonDirichletSimplex_powerSum s hs)⟩

/-- The subtype inherits compactness from the closed simplex. This instance
allows Mathlib's Stone--Weierstrass theorem to apply to its continuous maps. -/
instance : CompactSpace 𝕍 :=
  isCompact_iff_compactSpace.mp isCompact_poissonDirichletSimplex

/-- The subalgebra of continuous functions generated by higher power sums;
its point separation is proved below rather than assumed in the definition. -/
noncomputable def poissonDirichletPowerSumAlgebra :
    Subalgebra ℝ C(𝕍, ℝ) :=
  Algebra.adjoin ℝ {f | ∃ s : ℕ, ∃ hs : 2 ≤ s, f = poissonDirichletPowerSum s hs}

/-- The algebra generated by higher power sums separates the decreasing
simplex: equality of every generator forces equality of all coordinates. -/
theorem poissonDirichletPowerSumAlgebra_separatesPoints :
    poissonDirichletPowerSumAlgebra.SeparatesPoints := by
  intro x y hxy
  by_contra hnot
  have heq : ∀ s : ℕ, 2 ≤ s →
      (∑' j, x.1 j ^ s) = ∑' j, y.1 j ^ s := by
    intro s hs
    by_contra hne
    apply hnot
    refine ⟨poissonDirichletPowerSum s hs, ?_, hne⟩
    refine ⟨poissonDirichletPowerSum s hs, ?_, rfl⟩
    exact Algebra.subset_adjoin (R := ℝ) (show poissonDirichletPowerSum s hs ∈
      {f : C(𝕍, ℝ) |
        ∃ t : ℕ, ∃ ht : 2 ≤ t, f = poissonDirichletPowerSum t ht} from
      ⟨s, hs, rfl⟩)
  exact hxy (poissonDirichletSimplex_eq_of_powerSums_eq x y heq)

/-- Stone--Weierstrass for an arbitrary point-separating algebra on `V`. -/
theorem poissonDirichlet_stoneWeierstrass
    (A : Subalgebra ℝ C(𝕍, ℝ))
    (hsep : A.SeparatesPoints) : A.topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep

/-- Polynomial expressions in higher power sums are uniformly dense in
continuous functions on the compact decreasing subprobability simplex. -/
theorem poissonDirichletPowerSumAlgebra_dense :
    poissonDirichletPowerSumAlgebra.topologicalClosure = ⊤ :=
  poissonDirichlet_stoneWeierstrass poissonDirichletPowerSumAlgebra
    poissonDirichletPowerSumAlgebra_separatesPoints

end SpinGlasses
