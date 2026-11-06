/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenPairingBasic
public import LeanMachineLearning.Optimization.Renormalization.PairingRestrict
public import LeanMachineLearning.SpinGlasses.Talagrand.Hanen.SKHanenSpinContraction
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.PiDisjointSupports

/-!
# Full rectangles: truncation plus spin correction (Talagrand, Eq. (1.347)-(1.348))

Spin-level ingredients for Proposition 1.11.11. The full rectangle of two difference labels
on `N + 1` sites is the truncated rectangle of the first `N` sites plus `(N+1)^{-1}` times the
product of the two last-site spin differences.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Matrix
namespace SpinGlasses

/-- **Eq. (1.348), one block.** The full rectangle on `N + 1` sites equals the truncated rectangle
plus `(N+1)^{-1}` times the product of the last-site spin differences of the two labels. -/
theorem hanen_full_rect_eq_trunc_add_spin (N n m : ℕ) (q : ℝ)
    (pairMap : Fin (2 * m) → Fin n × Fin n) (σ : Fin n → Fin (N + 1) → ℤˣ)
    (a b : Fin (2 * m)) :
    (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap a).1 i : ℝ) * (σ (pairMap b).1 i : ℝ)) -
      (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap a).2 i : ℝ) * (σ (pairMap b).1 i : ℝ)) -
      (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap a).1 i : ℝ) * (σ (pairMap b).2 i : ℝ)) +
      (N + 1 : ℝ)⁻¹ * (∑ i : Fin (N + 1), (σ (pairMap a).2 i : ℝ) * (σ (pairMap b).2 i : ℝ)) =
    skCavityRectTrunc N n m q pairMap a b (fun r i => σ r i.castSucc) +
      (N + 1 : ℝ)⁻¹ * (((σ (pairMap a).1 (Fin.last N) : ℝ) - (σ (pairMap a).2 (Fin.last N) : ℝ)) *
        ((σ (pairMap b).1 (Fin.last N) : ℝ) - (σ (pairMap b).2 (Fin.last N) : ℝ))) := by
  simp only [skCavityRectTrunc, Fin.sum_univ_castSucc, dotProduct]
  ring

/-- **One spin difference squared.** For two distinct replicas the mean of the squared spin
difference under independent tilted spins is `2 (cosh Y)^{-2} = 2 - 2 tanh² Y`. -/
theorem integral_spin_diff_sq {ι : Type*} [Fintype ι] (Y : ℝ) (x y : ι)
    (hxy : x ≠ y) :
    (∫ ε : ι → ℤˣ, ((ε x : ℝ) - (ε y : ℝ)) ^ 2
      ∂(Measure.pi fun _ : ι => Measure.count.tilted fun s : ℤˣ => (s : ℝ) * Y)) =
      2 * ((Real.cosh Y)⁻¹) ^ 2 := by
  classical
  have h := integral_pi_mul_pair_of_invariant
    (fun _ : ι => Measure.count.tilted fun s : ℤˣ => (s : ℝ) * Y) x y hxy
    (fun a b : ℤˣ => ((a : ℝ) - (b : ℝ)) ^ 2) (fun _ => 1) (fun _ _ => rfl) (fun _ _ => rfl)
  simp only [mul_one, integral_const, probReal_univ, smul_eq_mul] at h
  rw [h]
  have hin (a : ℤˣ) :
      (∫ b : ℤˣ, ((a : ℝ) - (b : ℝ)) ^ 2
        ∂Measure.count.tilted (fun s : ℤˣ => (s : ℝ) * Y)) =
      2 - 2 * (a : ℝ) * Real.tanh Y := by
    have hsq (b : ℤˣ) : ((a : ℝ) - (b : ℝ)) ^ 2 = 2 - 2 * (a : ℝ) * (b : ℝ) := by
      have ha := units_cast_sq a
      have hb := units_cast_sq b
      nlinarith [ha, hb]
    simp_rw [hsq]
    rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_const,
      probReal_univ, smul_eq_mul, one_mul, integral_const_mul,
      integral_count_tilted_spin_eq_tanh]
  simp_rw [hin]
  rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_const, probReal_univ,
    smul_eq_mul, one_mul]
  have hm : (∫ a : ℤˣ, 2 * (a : ℝ) * Real.tanh Y
      ∂Measure.count.tilted (fun s : ℤˣ => (s : ℝ) * Y)) = 2 * Real.tanh Y ^ 2 := by
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_mul_const, integral_count_tilted_spin_eq_tanh]
    ring
  rw [hm]
  have := Real.one_sub_tanh_sq_eq_inv_cosh_sq Y
  nlinarith [this]

/-- **A product of squared spin differences of disjoint replica pairs.** The mean under
independent tilted spins of `∏_{v ∈ Λ} (ε_{x v} - ε_{y v})²` is `(2 (cosh Y)^{-2})^{|Λ|}`. -/
theorem integral_prod_spin_diff_sq {ι κ : Type*} [Fintype κ]
    (Y : ℝ) (x y : ι → κ) (hxy : ∀ v, x v ≠ y v)
    (hdisj : ∀ u v : ι, u ≠ v → x u ≠ x v ∧ x u ≠ y v ∧ y u ≠ x v ∧ y u ≠ y v)
    (Λ : Finset ι) :
    (∫ ε : κ → ℤˣ, ∏ v ∈ Λ, ((ε (x v) : ℝ) - (ε (y v) : ℝ)) ^ 2
      ∂(Measure.pi fun _ : κ => Measure.count.tilted fun s : ℤˣ => (s : ℝ) * Y)) =
      (2 * ((Real.cosh Y)⁻¹) ^ 2) ^ Λ.card := by
  classical
  have : Inhabited ℤˣ := ⟨1⟩
  have h := integral_pi_prod_of_disjoint_supports
    (Measure.count.tilted fun s : ℤˣ => (s : ℝ) * Y) (D := κ) (V := ι)
    (fun v => ({x v, y v} : Finset κ))
    (fun u v huv => by
      have := hdisj u v huv
      rw [Finset.disjoint_left]
      intro a ha hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with h | h
      · exact this.1 h
      · exact this.2.1 h
      · exact this.2.2.1 h
      · exact this.2.2.2 h)
    (fun v ε => ((ε (x v) : ℝ) - (ε (y v) : ℝ)) ^ 2)
    (fun v => measurable_of_finite _)
    (fun v ε ε' h => by
      simp only [h (x v) (by simp), h (y v) (by simp)])
    Λ
  rw [h]
  rw [Finset.prod_congr rfl (fun v _ => integral_spin_diff_sq Y (x v) (y v) (hxy v)),
    Finset.prod_const]

/-- **Expansion over subsets of the blocks (Eq. (1.347)).** For block weights `η B`, `u B` and a
constant `c`, the product of all `η B` with `∏ (u B + c η B)` is the sum over subsets `S` of the
blocks of `c^{|blocks| - |S|}` times `∏_{S} η u` times `∏_{blocks \ S} η²`. -/
theorem hanen_block_expansion {L : Type*} [DecidableEq L] (parts : Finset (Finset L))
    (u η : Finset L → ℝ) (c : ℝ) :
    (∏ B ∈ parts, η B) * ∏ B ∈ parts, (u B + c * η B) =
      ∑ S ∈ parts.powerset, c ^ (parts.card - S.card) *
        ((∏ B ∈ S, (η B * u B)) * ∏ B ∈ parts \ S, η B ^ 2) := by
  rw [Finset.prod_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hsub : S ⊆ parts := Finset.mem_powerset.1 hS
  have h1 : ∏ B ∈ parts, η B = (∏ B ∈ S, η B) * ∏ B ∈ parts \ S, η B := by
    rw [mul_comm, Finset.prod_sdiff hsub]
  have h2 : ∏ B ∈ parts \ S, (c * η B) = c ^ (parts.card - S.card) * ∏ B ∈ parts \ S, η B := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_sdiff_of_subset hsub]
  rw [h1, h2, Finset.prod_mul_distrib]
  simp only [sq, Finset.prod_mul_distrib]
  ring

/-- The labels covered by a set of blocks of a pairing, as a product: a product over the
relabelled elements `w k` is a product over the covered labels, which is the double product over
the blocks (they are pairwise disjoint). -/
theorem hanen_prod_relabel_eq_prod_blocks {L : Type*} {m' : ℕ}
    (parts S : Finset (Finset L)) (hdisj : (parts : Set (Finset L)).PairwiseDisjoint id)
    (hS : S ⊆ parts) (w : Fin m' → L) (hwinj : Function.Injective w)
    (hwrange : ∀ a, a ∈ Set.range w ↔ ∃ B ∈ S, a ∈ B) (g : L → ℝ) :
    ∏ k, g (w k) = ∏ B ∈ S, ∏ v ∈ B, g v := by
  classical
  have himg : (Finset.univ : Finset (Fin m')).image w = S.biUnion id := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_biUnion, id_eq]
    exact hwrange a
  rw [← Finset.prod_image (f := g) (fun a _ b _ h => hwinj h), himg,
    Finset.prod_biUnion (hdisj.subset (Finset.coe_subset.2 hS))]
  rfl

/-- The labels not covered by a set of blocks: the squared double product. -/
theorem hanen_prod_sq_blocks {L : Type*} [DecidableEq L] (parts S : Finset (Finset L))
    (hdisj : (parts : Set (Finset L)).PairwiseDisjoint id) (g : L → ℝ) :
    ∏ v ∈ (parts \ S).biUnion id, g v ^ 2 = ∏ B ∈ parts \ S, (∏ v ∈ B, g v) ^ 2 := by
  rw [Finset.prod_biUnion (hdisj.subset (by simp))]
  exact Finset.prod_congr rfl fun B _ => by rw [Finset.prod_pow]; rfl

/-- The number of labels outside a subset of the blocks of a pairing of a `2p`-element set. -/
theorem hanen_card_biUnion_sdiff {L : Type*} [DecidableEq L] {p : ℕ}
    (parts S : Finset (Finset L)) (hdisj : (parts : Set (Finset L)).PairwiseDisjoint id)
    (hcard : ∀ B ∈ parts, B.card = 2) (hS : S ⊆ parts) (hp : parts.card = p) :
    ((parts \ S).biUnion id).card = 2 * (p - S.card) := by
  rw [Finset.card_biUnion (hdisj.subset (by simp))]
  have h2 : ∑ u ∈ parts \ S, (id u).card = ∑ _u ∈ parts \ S, 2 :=
    Finset.sum_congr rfl (fun B hB => hcard B (Finset.mem_sdiff.1 hB).1)
  rw [h2]
  simp [Finset.card_sdiff_of_subset hS, hp, mul_comm]

end SpinGlasses
