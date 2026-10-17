/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Series over a finite power of a countable set

For a finite index type `J` and a family of summable nonnegative functions `f j : α → ℝ`, the
product `σ ↦ ∏ j, f j (σ j)` is summable over `J → α` (`summable_prod_pi`).  Combined with
Tannery's theorem this gives dominated convergence for averages of an observable `Ψ` against the
`J`-fold product of weights `w i : α → ℝ` that converge pointwise and are dominated by a summable
function (`tendsto_tsum_prod_pi`).  This is how a Gibbs average over `J` replicas of a countable
configuration space is approximated by finite truncations.
-/

@[expose] public section

open Filter Topology

variable {α J : Type*} [Fintype J]

/-- A finite product of summable nonnegative functions is summable over the product space:
`∑_{σ : J → α} ∏ⱼ f j (σ j) < ∞`. -/
theorem summable_prod_pi {f : J → α → ℝ} (hf0 : ∀ j a, 0 ≤ f j a) (hf : ∀ j, Summable (f j)) :
    Summable fun σ : J → α => ∏ j, f j (σ j) := by
  classical
  refine summable_of_sum_le (c := ∏ j, ∑' a, f j a)
    (fun σ => Finset.prod_nonneg fun j _ => hf0 j (σ j)) fun T => ?_
  have hT : T ⊆ Fintype.piFinset fun j => T.image fun σ => σ j := by
    intro σ hσ
    rw [Fintype.mem_piFinset]
    exact fun j => Finset.mem_image_of_mem _ hσ
  calc ∑ σ ∈ T, ∏ j, f j (σ j)
      ≤ ∑ σ ∈ Fintype.piFinset fun j => T.image fun σ => σ j, ∏ j, f j (σ j) :=
        Finset.sum_le_sum_of_subset_of_nonneg hT fun σ _ _ =>
          Finset.prod_nonneg fun j _ => hf0 j (σ j)
    _ = ∏ j, ∑ a ∈ T.image fun σ => σ j, f j a := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ j, ∑' a, f j a :=
        Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun a _ => hf0 j a)
          (fun j _ => (hf j).sum_le_tsum _ fun a _ => hf0 j a)

/-- A countable product of nonnegative summable series over a finite coordinate set.
This is the infinite-series counterpart of `Finset.prod_univ_sum`. -/
theorem tsum_prod_pi {f : J → α → ℝ} (hf0 : ∀ j a, 0 ≤ f j a)
    (hf : ∀ j, Summable (f j)) :
    (∑' σ : J → α, ∏ j, f j (σ j)) = ∏ j, ∑' a, f j a := by
  classical
  have hs := summable_prod_pi hf0 hf
  have hnet : Tendsto
      (fun s : Finset α => ∑ σ ∈ Fintype.piFinset (fun _ : J => s), ∏ j, f j (σ j))
      atTop (𝓝 (∑' σ : J → α, ∏ j, f j (σ j))) := by
    apply hs.hasSum.comp
    apply tendsto_atTop.2
    intro T
    refine Filter.eventually_atTop.2 ⟨Finset.univ.biUnion (fun j : J => T.image (· j)), ?_⟩
    intro s hs
    have hs' : Finset.univ.biUnion (fun j : J => T.image (· j)) ⊆ s := hs
    intro σ hσ
    apply Fintype.mem_piFinset.mpr
    intro j
    exact hs' (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j,
      Finset.mem_image.mpr ⟨σ, hσ, rfl⟩⟩)
  have hright : Tendsto (fun s : Finset α => ∏ j, ∑ a ∈ s, f j a)
      atTop (𝓝 (∏ j, ∑' a, f j a)) :=
    tendsto_finsetProd _ fun j _ => (hf j).hasSum
  apply tendsto_nhds_unique hnet
  convert hright using 1
  ext s
  exact (Finset.prod_univ_sum (fun _ : J => s) (fun j a => f j a)).symm

/-- Replacing the factor at one coordinate `j₀` of a product `∏ⱼ a (σ j)` by `a (σ j₀) * b (σ j₀)`
multiplies the product by `b (σ j₀)`. -/
theorem prod_ite_mul_eval [DecidableEq J] (a b : α → ℝ) (σ : J → α) (j₀ : J) :
    ∏ j, (if j = j₀ then a (σ j) * b (σ j) else a (σ j)) = (∏ j, a (σ j)) * b (σ j₀) := by
  have h : ∀ j, (if j = j₀ then a (σ j) * b (σ j) else a (σ j)) =
      a (σ j) * (if j = j₀ then b (σ j) else 1) := fun j => by split_ifs <;> simp
  rw [Finset.prod_congr rfl fun j _ => h j, Finset.prod_mul_distrib,
    Finset.prod_ite_eq' Finset.univ j₀ (fun j => b (σ j))]
  simp

/-- A normalized product weight has the expected one-coordinate marginal at the replica
`j₀` (so the replica set is nonempty). -/
theorem tsum_prod_pi_mul_eval {w χ : α → ℝ}
    (hw0 : ∀ a, 0 ≤ w a) (hws : Summable w) (hw : ∑' a, w a = 1)
    (hχ0 : ∀ a, 0 ≤ χ a) (hχ : Summable fun a => w a * χ a) (j₀ : J) :
    (∑' σ : J → α, (∏ j, w (σ j)) * χ (σ j₀)) = ∑' a, w a * χ a := by
  classical
  have hprod := tsum_prod_pi (J := J)
    (f := fun j a => if j = j₀ then w a * χ a else w a)
  have hf0 : ∀ j a, 0 ≤ (if j = j₀ then w a * χ a else w a) := by
    intro j a
    split_ifs <;> [exact mul_nonneg (hw0 a) (hχ0 a); exact hw0 a]
  have hf : ∀ j, Summable (fun a => if j = j₀ then w a * χ a else w a) := by
    intro j
    split_ifs <;> assumption
  have hp := hprod hf0 hf
  convert hp using 1
  · exact tsum_congr fun σ => (prod_ite_mul_eval w χ σ j₀).symm
  · simp_rw [show ∀ j, (∑' a, if j = j₀ then w a * χ a else w a) =
        if j = j₀ then (∑' a, w a * χ a) else 1 from fun j => by
          split_ifs <;> simp [hw]]
    simp

/-- **Tannery's theorem for replica averages:** if the weights `w i` are dominated by a summable
`B` and converge pointwise, then the `J`-fold product averages of an observable `Ψ` with
`∑_σ ∏ⱼ B(σ j) |Ψ σ| < ∞` converge. -/
theorem tendsto_tsum_prod_pi {ι : Type*} {𝓕 : Filter ι} {w : ι → α → ℝ} {w₀ : α → ℝ}
    {B : α → ℝ} (hw0 : ∀ᶠ i in 𝓕, ∀ a, 0 ≤ w i a ∧ w i a ≤ B a)
    (hw : ∀ a, Tendsto (fun i => w i a) 𝓕 (𝓝 (w₀ a))) {Ψ : (J → α) → ℝ}
    (hΨ : Summable fun σ : J → α => (∏ j, B (σ j)) * |Ψ σ|) :
    Tendsto (fun i => ∑' σ : J → α, (∏ j, w i (σ j)) * Ψ σ) 𝓕
      (𝓝 (∑' σ : J → α, (∏ j, w₀ (σ j)) * Ψ σ)) := by
  refine tendsto_tsum_of_dominated_convergence hΨ (fun σ => ?_) ?_
  · exact (tendsto_finsetProd _ fun j _ => hw (σ j)).mul_const _
  · filter_upwards [hw0] with i hi σ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg
      (Finset.prod_nonneg fun j _ => (hi (σ j)).1)]
    exact mul_le_mul_of_nonneg_right
      (Finset.prod_le_prod₀ (fun j _ => (hi (σ j)).1) fun j _ => (hi (σ j)).2) (abs_nonneg _)

/-- Summability of `∏ⱼ B(σ j) |Φ σ| |χ(σ j₀)|` for bounded `Φ`, summable `B` and `B |χ|`. -/
theorem summable_prod_pi_mul_abs_eval {B χ : α → ℝ}
    (hB0 : ∀ a, 0 ≤ B a) (hB : Summable B) (hχ : Summable fun a => B a * |χ a|) (j₀ : J)
    {Φ : (J → α) → ℝ} {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M) :
    Summable fun σ : J → α => (∏ j, B (σ j)) * |Φ σ * χ (σ j₀)| := by
  classical
  have h := summable_prod_pi (J := J) (f := fun j a => if j = j₀ then B a * |χ a| else B a)
    (fun j a => by split_ifs <;> [exact mul_nonneg (hB0 a) (abs_nonneg _); exact hB0 a])
    (fun j => by split_ifs <;> assumption)
  refine (h.mul_left M).of_nonneg_of_le (fun σ => ?_) fun σ => ?_
  · exact mul_nonneg (Finset.prod_nonneg fun j _ => hB0 _) (abs_nonneg _)
  · have hprod := prod_ite_mul_eval B (fun a => |χ a|) σ j₀
    rw [hprod, abs_mul]
    calc (∏ j, B (σ j)) * (|Φ σ| * |χ (σ j₀)|)
        ≤ (∏ j, B (σ j)) * (M * |χ (σ j₀)|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hΦ σ) (abs_nonneg _))
            (Finset.prod_nonneg fun j _ => hB0 _)
      _ = M * ((∏ j, B (σ j)) * |χ (σ j₀)|) := by ring

/-- A product-weighted series is bounded in absolute value by the series of the absolute values.
This is the triangle inequality for a summable family of real terms. -/
theorem abs_tsum_prod_pi_mul_le {w : α → ℝ} (hw0 : ∀ a, 0 ≤ w a) {Ψ : (J → α) → ℝ}
    (hΨ : Summable fun σ : J → α => (∏ j, w (σ j)) * |Ψ σ|) :
    |∑' σ : J → α, (∏ j, w (σ j)) * Ψ σ| ≤ ∑' σ : J → α, (∏ j, w (σ j)) * |Ψ σ| := by
  have habs : ∀ σ : J → α, ‖(∏ j, w (σ j)) * Ψ σ‖ = (∏ j, w (σ j)) * |Ψ σ| := fun σ => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Finset.prod_nonneg fun j _ => hw0 _)]
  have hs : Summable fun σ : J → α => ‖(∏ j, w (σ j)) * Ψ σ‖ :=
    hΨ.congr fun σ => (habs σ).symm
  calc |∑' σ : J → α, (∏ j, w (σ j)) * Ψ σ|
      = ‖∑' σ : J → α, (∏ j, w (σ j)) * Ψ σ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' σ : J → α, ‖(∏ j, w (σ j)) * Ψ σ‖ := norm_tsum_le_tsum_norm hs
    _ = _ := tsum_congr habs

/-- For normalized nonnegative weights, the weighted absolute value of an observable
at one replica is bounded by its one-coordinate marginal. -/
theorem abs_tsum_prod_pi_mul_eval_le
    {w χ : α → ℝ} (hw0 : ∀ a, 0 ≤ w a) (hws : Summable w)
    (hw : ∑' a, w a = 1) (hχ : Summable fun a => w a * |χ a|)
    {Φ : (J → α) → ℝ} {M : ℝ}
    (hΦ : ∀ σ, |Φ σ| ≤ M) (j₀ : J) :
    |∑' σ : J → α, (∏ j, w (σ j)) * (Φ σ * χ (σ j₀))| ≤
      M * ∑' a, w a * |χ a| := by
  classical
  have hs := summable_prod_pi_mul_abs_eval hw0 hws hχ j₀ hΦ
  have hs0 : Summable fun σ : J → α => (∏ j, w (σ j)) * |χ (σ j₀)| := by
    simpa using summable_prod_pi_mul_abs_eval hw0 hws hχ j₀ (Φ := fun _ => (1 : ℝ)) (M := 1)
      fun _ => by simp
  have hbase := tsum_prod_pi_mul_eval hw0 hws hw (fun a => abs_nonneg _) hχ j₀
  have hle : ∑' σ : J → α, (∏ j, w (σ j)) * |Φ σ * χ (σ j₀)| ≤
      ∑' σ : J → α, M * ((∏ j, w (σ j)) * |χ (σ j₀)|) := by
    refine hs.tsum_le_tsum (fun σ => ?_) (hs0.mul_left M)
    rw [abs_mul]
    calc (∏ j, w (σ j)) * (|Φ σ| * |χ (σ j₀)|)
        ≤ (∏ j, w (σ j)) * (M * |χ (σ j₀)|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hΦ σ) (abs_nonneg _))
            (Finset.prod_nonneg fun j _ => hw0 _)
      _ = M * ((∏ j, w (σ j)) * |χ (σ j₀)|) := by ring
  calc _ ≤ ∑' σ : J → α, (∏ j, w (σ j)) * |Φ σ * χ (σ j₀)| :=
        abs_tsum_prod_pi_mul_le hw0 hs
    _ ≤ _ := hle
    _ = M * ∑' σ : J → α, (∏ j, w (σ j)) * |χ (σ j₀)| := tsum_mul_left
    _ = _ := by rw [hbase]
