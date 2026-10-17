/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
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

/-- Normalizing a family by its (positive) total gives a family with total `1`. -/
theorem tsum_div_tsum_eq_one {β : Type*} {v : β → ℝ} (hV : 0 < ∑' a, v a) :
    ∑' a, v a / ∑' b, v b = 1 := by
  rw [tsum_div_const, div_self hV.ne']

/-- Summability of a function over the subtype cut out by a predicate is summability of the
guarded function `if p x then f x else 0` over the ambient type. -/
theorem summable_subtype_guard_iff {β : Type*} (p : β → Prop) [DecidablePred p] (f : β → ℝ) :
    Summable (fun a : {x : β // p x} => f a.1) ↔
      Summable (fun x : β => if p x then f x else 0) := by
  have heq : Set.indicator {x | p x} f = fun x => if p x then f x else 0 := by
    funext x
    by_cases hx : p x <;> simp [Set.indicator, hx]
  rw [← heq]
  exact summable_subtype_iff_indicator (s := {x | p x}) (f := f)

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

/-- For a normalized nonnegative weight family, the higher power series
is summable by comparison with the first power. -/
theorem summable_pow_of_normalized {w : α → ℝ} (hw0 : ∀ a, 0 ≤ w a)
    (hws : Summable w) (hw : ∑' a, w a = 1) {n : ℕ} (hn : 0 < n) :
    Summable (fun a => w a ^ n) := by
  have hbound (a : α) : w a ≤ 1 := by
    rw [← hw]
    simpa using hws.sum_le_tsum {a} (fun _ _ => hw0 _)
  apply Summable.of_nonneg_of_le (fun a => pow_nonneg (hw0 a) _)
    (fun a => ?_) hws
  exact pow_le_of_le_one (hw0 a) (hbound a) hn.ne'

/-- For a nonempty finite replica block, imposing equality of all sampled
indices turns its Gibbs series into a power sum. -/
theorem tsum_prod_pi_all_eq {I : Type*} [Fintype I] [Nonempty I]
    [DecidableEq α] {w : α → ℝ} (hw0 : ∀ a, 0 ≤ w a) (hws : Summable w) :
    (∑' σ : I → α, (∏ i, w (σ i)) *
      (if (∀ i j, σ i = σ j) then (1 : ℝ) else 0)) =
      ∑' a, w a ^ Fintype.card I := by
  classical
  let i₀ : I := Classical.choice inferInstance
  have hp : Summable (fun σ : I → α => ∏ i, w (σ i)) :=
    summable_prod_pi (fun _ => hw0) (fun _ => hws)
  have hguard : Summable (fun σ : I → α =>
      (∏ i, w (σ i)) * (if ∀ i j, σ i = σ j then 1 else 0)) := by
    apply hp.of_norm_bounded
    intro σ
    have hpos : 0 ≤ ∏ i, w (σ i) :=
      Finset.prod_nonneg fun i _ => hw0 (σ i)
    by_cases h : ∀ i j, σ i = σ j
    · simp only [ite_eq_left h, mul_one, Real.norm_eq_abs, abs_of_nonneg hpos, le_refl]
    · simpa [h] using hpos
  have heq (σ : I → α) : (∀ i j, σ i = σ j) ↔ σ = Function.const I (σ i₀) := by
    constructor
    · intro h
      funext i
      exact h i i₀
    · intro h i j
      exact congrArg (fun f : I → α => f i) h |>.trans
        (congrArg (fun f : I → α => f j) h).symm
  have hinj : Function.Injective (Function.const I : α → I → α) := by
    intro a b h
    exact congrArg (fun f : I → α => f i₀) h
  have hsupport (σ : I → α) (h : ∀ i j, σ i = σ j) :
      σ = Function.const I (σ i₀) := (heq σ).mp h
  have hzero (σ : I → α)
      (hσ : σ ∉ Set.range (Function.const I : α → I → α)) :
      (∏ i, w (σ i)) * (if ∀ i j, σ i = σ j then 1 else 0) = 0 := by
    have hn : ¬ ∀ i j, σ i = σ j := by
      intro h
      exact hσ ⟨σ i₀, (hsupport σ h).symm⟩
    simp [hn]
  have hreindex : (∑' σ : I → α,
      (∏ i, w (σ i)) * (if ∀ i j, σ i = σ j then 1 else 0)) =
      ∑' a : α, (∏ i, w ((Function.const I a) i)) *
        (if ∀ i j, (Function.const I a) i = (Function.const I a) j
          then 1 else 0) := by
    rw [← tsum_subtype_eq_of_support_subset
      (s := Set.range (Function.const I : α → I → α))
      (fun σ hσ => by
        by_contra hn
        exact hσ (hzero σ hn))]
    let e : α ≃ Set.range (Function.const I : α → I → α) :=
      Equiv.ofBijective (fun a => ⟨Function.const I a, ⟨a, rfl⟩⟩)
        ⟨fun a b h => hinj (congrArg Subtype.val h),
          fun ⟨σ, a, ha⟩ => ⟨a, Subtype.ext ha⟩⟩
    exact (e.tsum_eq (fun σ : Set.range (Function.const I : α → I → α) =>
      (∏ i, w (σ.1 i)) * (if ∀ i j, σ.1 i = σ.1 j then 1 else 0))).symm
  rw [hreindex]
  apply tsum_congr
  intro a
  simp only [Function.const_apply, forall_const, ite_true, mul_one,
    Finset.prod_const, Finset.card_univ]

/-- Replica assignments constant on the fibers of a surjective block map are precisely
assignments of one label per block. The resulting series is a product of power sums. -/
theorem tsum_prod_pi_fiber_eq {I K : Type*} [Fintype I] [Fintype K]
    (b : I → K) (hb : Function.Surjective b) [DecidableEq K]
    [∀ σ : I → α, Decidable (∀ i j, b i = b j → σ i = σ j)]
    {w : α → ℝ} (hw0 : ∀ a, 0 ≤ w a) (hws : Summable w)
    (hw : ∑' a, w a = 1) :
    (∑' σ : I → α, (∏ i, w (σ i)) *
      (if ∀ i j, b i = b j → σ i = σ j then 1 else 0)) =
      ∏ m : K, ∑' a, w a ^ Fintype.card {i : I // b i = m} := by
  let _ : DecidableEq (I → α) := Classical.decEq _
  let e : (K → α) ≃ {σ : I → α // ∀ i j, b i = b j → σ i = σ j} :=
    { toFun := fun τ => ⟨τ ∘ b, fun i j h => congrArg τ h⟩
      invFun := fun σ m => σ.1 (Classical.choose (hb m))
      left_inv := by
        intro τ
        funext m
        exact congrArg τ (Classical.choose_spec (hb m))
      right_inv := by
        intro σ
        apply Subtype.ext
        funext i
        exact (σ.2 i (Classical.choose (hb (b i)))
          (Classical.choose_spec (hb (b i))).symm).symm }
  have hguard : (∑' σ : I → α, (∏ i, w (σ i)) *
      (if ∀ i j, b i = b j → σ i = σ j then 1 else 0)) =
      ∑' σ : {σ : I → α // ∀ i j, b i = b j → σ i = σ j},
        ∏ i, w (σ.1 i) := by
    let F : (I → α) → ℝ := fun σ => (∏ i, w (σ i)) *
      (if ∀ i j, b i = b j → σ i = σ j then 1 else 0)
    calc
      (∑' σ : I → α, F σ) = ∑' σ : {σ : I → α // ∀ i j,
          b i = b j → σ i = σ j}, F σ.1 := by
        symm
        apply tsum_subtype_eq_of_support_subset
        intro σ hσ
        by_contra hn
        have h : ¬ ∀ i j, b i = b j → σ i = σ j := hn
        exact hσ (by simp [F, h])
      _ = _ := tsum_congr fun σ => by
        change (∏ i, w (σ.1 i)) *
          (if ∀ i j, b i = b j → σ.1 i = σ.1 j then 1 else 0) = _
        rw [ite_eq_left σ.property, mul_one]
  rw [hguard, ← e.tsum_eq (fun σ : {σ : I → α // ∀ i j,
    b i = b j → σ i = σ j} => ∏ i, w (σ.1 i))]
  have hf (m : K) : Summable (fun a => w a ^ Fintype.card {i : I // b i = m}) :=
    summable_pow_of_normalized hw0 hws hw
      (Fintype.card_pos_iff.mpr (let ⟨i, hi⟩ := hb m; ⟨⟨i, hi⟩⟩))
  calc
    (∑' τ : K → α, ∏ i, w ((e τ).1 i)) =
        ∑' τ : K → α, ∏ m, w (τ m) ^ Fintype.card {i : I // b i = m} := by
      apply tsum_congr
      intro τ
      change (∏ i, w (τ (b i))) = _
      rw [← Fintype.prod_fiberwise' b (fun m => w (τ m))]
      congr 1
      funext m
      simp only [Finset.prod_const, Finset.card_univ]
    _ = _ := tsum_prod_pi (fun m a => pow_nonneg (hw0 a) _) hf

/-- Reindex a finite tuple of elements of a subset as a tuple of elements of the ambient
set satisfying the coordinatewise membership guard. This also applies to `Option J` for the
extra replica in Gaussian integration by parts. -/
theorem tsum_pi_subtype_eq_tsum_ite {s : Set α} [DecidablePred (· ∈ s)]
    (f : (J → s) → ℝ) :
    (∑' σ : J → s, f σ) =
      ∑' σ : J → α, if h : ∀ j, σ j ∈ s then f (fun j => ⟨σ j, h j⟩) else 0 := by
  classical
  let t : Set (J → α) := {σ | ∀ j, σ j ∈ s}
  let e : (J → s) ≃ t :=
    { toFun := fun σ => ⟨(fun j => (σ j).1), fun j => (σ j).2⟩
      invFun := fun σ j => ⟨σ.1 j, σ.2 j⟩
      left_inv := fun σ => by funext j; exact Subtype.ext rfl
      right_inv := fun σ => by apply Subtype.ext; rfl }
  calc
    (∑' σ : J → s, f σ) = ∑' σ : t, f (e.symm σ) :=
      (e.tsum_eq (fun σ : t => f (e.symm σ))) |>.trans (by
        apply tsum_congr
        intro σ
        rfl)
    _ = ∑' σ : J → α,
        if h : σ ∈ t then f (e.symm ⟨σ, h⟩) else 0 := by
      let F : (J → α) → ℝ := fun σ =>
        if h : σ ∈ t then f (e.symm ⟨σ, h⟩) else 0
      have h := tsum_subtype t F
      calc
        _ = ∑' σ : t, F σ := by
          apply tsum_congr
          intro σ
          simp [F, σ.property]
        _ = ∑' σ : J → α, t.indicator F σ := h
        _ = _ := by
          apply tsum_congr
          intro σ
          by_cases hs : σ ∈ t <;> simp [F, Set.indicator, hs]
    _ = _ := by
      apply tsum_congr
      intro σ
      have hmem : σ ∈ t ↔ ∀ j, σ j ∈ s := Iff.rfl
      by_cases h : ∀ j, σ j ∈ s
      · simp only [dite_eq_left (hmem.mpr h), dite_eq_left h]
        rfl
      · simp only [dite_eq_right (fun ht => h (hmem.mp ht)), dite_eq_right h]

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

/-- Summing out a fresh independent replica leaves a normalized replica average unchanged.
The extra coordinate is indexed by `none`, while the existing replicas use `some`. -/
theorem tsum_prod_option_some {w : α → ℝ} (hw0 : ∀ a, 0 ≤ w a)
    (hws : Summable w) (hw : ∑' a, w a = 1)
    (Φ : (J → α) → ℝ)
    (hΦ : Summable fun σ : J → α => (∏ j, w (σ j)) * Φ σ) :
    (∑' τ : Option J → α, (∏ o, w (τ o)) * Φ (fun j => τ (some j))) =
      ∑' σ : J → α, (∏ j, w (σ j)) * Φ σ := by
  let e : (Option J → α) ≃ α × (J → α) := Equiv.piOptionEquivProd
  let F : (J → α) → ℝ := fun σ => (∏ j, w (σ j)) * Φ σ
  have hFnorm : Summable fun σ => ‖F σ‖ := by
    exact hΦ.abs.congr (fun σ => (Real.norm_eq_abs _).symm)
  have hs : Summable (fun p : α × (J → α) => w p.1 * F p.2) :=
    summable_mul_of_summable_norm
      (by simpa only [Real.norm_eq_abs, abs_of_nonneg (hw0 _)] using hws) hFnorm
  have hfactor : ∀ τ : Option J → α,
      (∏ o, w (τ o)) * Φ (fun j => τ (some j)) =
        w (τ none) * ((∏ j, w (τ (some j))) * Φ (fun j => τ (some j))) := by
    intro τ
    rw [Fintype.prod_option]
    ring
  calc
    _ = ∑' p : α × (J → α), w p.1 * ((∏ j, w (p.2 j)) * Φ p.2) := by
      calc
        _ = ∑' τ : Option J → α, w (e τ).1 * F (e τ).2 := by
          apply tsum_congr
          intro τ
          exact hfactor τ
        _ = _ := e.tsum_eq (fun p : α × (J → α) => w p.1 * F p.2)
    _ = ∑' a : α, ∑' σ : J → α, w a * F σ := hs.tsum_prod
    _ = (∑' a : α, w a) * (∑' σ : J → α, F σ) := by
      simp only [tsum_mul_left, tsum_mul_right]
    _ = _ := by rw [hw, one_mul]

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

/-- A bounded function of finitely many independent samples has its original bound
when averaged against normalized nonnegative, summable weights. -/
theorem abs_tsum_prod_pi_mul_le_bound
    {w : α → ℝ} (hw0 : ∀ a, 0 ≤ w a) (hws : Summable w)
    (hw : ∑' a, w a = 1) {Ψ : (J → α) → ℝ} {M : ℝ}
    (hΨ : ∀ σ, |Ψ σ| ≤ M) :
    |∑' σ : J → α, (∏ j, w (σ j)) * Ψ σ| ≤ M := by
  have hs : Summable (fun σ : J → α => (∏ j, w (σ j)) * |Ψ σ|) := by
    have hbase := summable_prod_pi (J := J) (f := fun _ => w)
      (fun _ a => hw0 a) (fun _ => hws)
    exact (hbase.mul_right M).of_nonneg_of_le
      (fun σ => mul_nonneg (Finset.prod_nonneg fun j _ => hw0 _) (abs_nonneg _))
      (fun σ => mul_le_mul_of_nonneg_left (hΨ σ)
        (Finset.prod_nonneg fun j _ => hw0 _))
  calc
    |∑' σ : J → α, (∏ j, w (σ j)) * Ψ σ|
        ≤ ∑' σ : J → α, (∏ j, w (σ j)) * |Ψ σ| :=
          abs_tsum_prod_pi_mul_le hw0 hs
    _ ≤ ∑' σ : J → α, M * (∏ j, w (σ j)) :=
      hs.tsum_le_tsum (fun σ => by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hΨ σ)
          (Finset.prod_nonneg fun j _ => hw0 _))
        ((summable_prod_pi (J := J) (f := fun _ => w)
          (fun _ a => hw0 a) (fun _ => hws)).mul_left M)
    _ = M := by
      rw [tsum_mul_left, tsum_prod_pi (J := J) (f := fun _ => w)
        (fun _ a => hw0 a) (fun _ => hws)]
      simp [hw]

/-- For normalized nonnegative weights, the weighted absolute value of an observable
at one replica is bounded by its one-coordinate marginal. -/
theorem abs_tsum_prod_pi_mul_eval_le
    {w χ : α → ℝ} (hw0 : ∀ a, 0 ≤ w a) (hws : Summable w)
    (hw : ∑' a, w a = 1) (hχ : Summable fun a => w a * |χ a|)
    {Φ : (J → α) → ℝ} {M : ℝ}
    (hΦ : ∀ σ, |Φ σ| ≤ M) (j₀ : J) :
    |∑' σ : J → α, (∏ j, w (σ j)) * (Φ σ * χ (σ j₀))| ≤
      M * ∑' a, w a * |χ a| := by
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
