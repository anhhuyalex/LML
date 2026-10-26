/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.MeasurePreservingSymmetry
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.SupMoment
public import LeanMachineLearning.SpinGlasses.SKLocalMagnetizations
public import LeanMachineLearning.SpinGlasses.SKTAPEquation

/-!
# The TAP equations hold at all sites simultaneously (Talagrand, Corollary 1.7.8)

Let `Δ_i = ⟨σ_i⟩ - tanh (β M^{-1/2} ∑_{j ≠ i} g_{ij} ⟨σ_j⟩ + h - β² (1-q) ⟨σ_i⟩)` for the `M`-spin
system, `M = N+1`, where `g_{ij} = g_{ji}` is the symmetric extension of the couplings
`g : FinPairs M → ℝ` (stored for `i < j` only; `g_{ii} = 0`).  The proof is the book's:

1. a relabelling `π` of the sites acts on the couplings by `g ∘ (pairPerm π).symm`, and
   `Δ_i (g ∘ (pairPerm π).symm) = Δ_{π⁻¹ i} g` (`tap_defect_comp_pairPerm`), so all `Δ_i` have the
   same `2k`-th moment (`integral_comp_eq_of_perm_equivariant`);
2. for the last site `Δ_last` is exactly the quantity of Theorem 1.7.7 (`sk_tap_equation`);
3. `𝔼 max_i |Δ_i| ≤ (1 + K) M^{-(k-1)/(2k)}` from `𝔼 Δ_i^{2k} ≤ K / M^k`
   (`integral_sup'_abs_le_rpow`), and `k` is chosen with `2k ≥ 1/ε`.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Corollary 1.7.8.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

variable {M : ℕ}

/-- **The symmetric coupling field under a relabelling of the sites.**  If `G g i j` is the
symmetric extension of the couplings (`g_{ij}` for `i < j`, `g_{ji}` for `j < i`, `0` on the
diagonal), then `G (g ∘ (pairPerm π).symm) i j = G g (π⁻¹ i) (π⁻¹ j)`. -/
theorem symCoupling_comp_pairPerm (G : (FinPairs M → ℝ) → Fin M → Fin M → ℝ)
    (hG : ∀ g i j, G g i j = if hij : i < j then g ⟨(i, j), hij⟩
      else if hji : j < i then g ⟨(j, i), hji⟩ else 0)
    (π : Equiv.Perm (Fin M)) (g : FinPairs M → ℝ) (i j : Fin M) :
    G (g ∘ (pairPerm π).symm) i j = G g (π.symm i) (π.symm j) := by
  rw [hG, hG]
  rcases lt_trichotomy i j with hij | rfl | hji
  · have hne : π.symm i ≠ π.symm j := π.symm.injective.ne hij.ne
    simp only [hij, ↓reduceDIte]
    rcases lt_or_gt_of_ne hne with h | h
    · simp only [h, ↓reduceDIte]
      simp [pairPerm, min_eq_left h.le, max_eq_right h.le]
    · simp only [not_lt.mpr h.le, h, ↓reduceDIte]
      simp [pairPerm, min_eq_right h.le, max_eq_left h.le]
  · simp
  · have hne : π.symm j ≠ π.symm i := π.symm.injective.ne hji.ne
    simp only [not_lt.mpr hji.le, hji, ↓reduceDIte]
    rcases lt_or_gt_of_ne hne with h | h
    · simp only [not_lt.mpr h.le, h, ↓reduceDIte]
      simp [pairPerm, min_eq_left h.le, max_eq_right h.le]
    · simp only [h, ↓reduceDIte]
      simp [pairPerm, min_eq_right h.le, max_eq_left h.le]

/-- **The TAP defect is equivariant under the relabelling of the sites.**  For the symmetric
coupling field `G` (see `symCoupling_comp_pairPerm`),
`Δ_i (g ∘ (pairPerm π).symm) = Δ_{π⁻¹ i} g`, where
`Δ_i g = ⟨σ_i⟩ - tanh (c ∑_j G g i j ⟨σ_j⟩ + h - b ⟨σ_i⟩)` and `⟨·⟩` is the Gibbs mean of the
`M`-spin system with couplings `g`. -/
theorem tap_defect_comp_pairPerm (β h c b : ℝ) (G : (FinPairs M → ℝ) → Fin M → Fin M → ℝ)
    (hG : ∀ g i j, G g i j = if hij : i < j then g ⟨(i, j), hij⟩
      else if hji : j < i then g ⟨(j, i), hji⟩ else 0)
    (π : Equiv.Perm (Fin M)) (g : FinPairs M → ℝ) (i : Fin M) :
    ∫ σ : Fin M → ℤˣ, ((σ i : ℤ) : ℝ)
          ∂(Measure.count.tilted (skGibbsEnergy M β h (g ∘ (pairPerm π).symm))) -
        Real.tanh (c * ∑ j, G (g ∘ (pairPerm π).symm) i j *
            (∫ σ : Fin M → ℤˣ, ((σ j : ℤ) : ℝ)
              ∂(Measure.count.tilted (skGibbsEnergy M β h (g ∘ (pairPerm π).symm)))) + h -
          b * ∫ σ : Fin M → ℤˣ, ((σ i : ℤ) : ℝ)
            ∂(Measure.count.tilted (skGibbsEnergy M β h (g ∘ (pairPerm π).symm)))) =
      ∫ σ : Fin M → ℤˣ, ((σ (π.symm i) : ℤ) : ℝ)
          ∂(Measure.count.tilted (skGibbsEnergy M β h g)) -
        Real.tanh (c * ∑ j, G g (π.symm i) j *
            (∫ σ : Fin M → ℤˣ, ((σ j : ℤ) : ℝ)
              ∂(Measure.count.tilted (skGibbsEnergy M β h g))) + h -
          b * ∫ σ : Fin M → ℤˣ, ((σ (π.symm i) : ℤ) : ℝ)
            ∂(Measure.count.tilted (skGibbsEnergy M β h g))) := by
  simp only [integral_spin_comp_pairPerm M β h π g, symCoupling_comp_pairPerm G hG π g]
  rw [Equiv.sum_comp π.symm (fun j => G g (π.symm i) j *
    ∫ σ : Fin M → ℤˣ, ((σ j : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy M β h g)))]

/-- **The symmetric field at the last site** is the field of the last-spin couplings
`y_i = (skCavityDisorderEquiv N g).2 i`. -/
theorem sum_symCoupling_last {N : ℕ}
    (G : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → Fin (N + 1) → ℝ)
    (hG : ∀ g i j, G g i j = if hij : i < j then g ⟨(i, j), hij⟩
      else if hji : j < i then g ⟨(j, i), hji⟩ else 0)
    (m : Fin (N + 1) → ℝ) (g : FinPairs (N + 1) → ℝ) :
    ∑ j, G g (Fin.last N) j * m j =
      ∑ i : Fin N, (skCavityDisorderEquiv N g).2 i * m i.castSucc := by
  rw [Fin.sum_univ_castSucc, hG g (Fin.last N) (Fin.last N)]
  simp only [lt_irrefl, ↓reduceDIte, zero_mul, add_zero, skCavityDisorderEquiv_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hG]
  simp only [not_lt.mpr (Fin.castSucc_lt_last i).le, Fin.castSucc_lt_last i, ↓reduceDIte]

/-- **Talagrand, Corollary 1.7.8, Eq. (1.194): the TAP equations hold at all sites.**  For
`4 β₀² < 1`, `h` and `ε > 0` there is `K = K(β₀, h, ε)` such that for all `0 ≤ β ≤ β₀`, every fixed
point `q` and `N ≥ 1`, in the `(N+1)`-spin SK system with the symmetric couplings `g_{ij}` (`g_{ij}`
for `i < j`, `g_{ji}` for `j < i`, `0` on the diagonal) and Gibbs mean `⟨·⟩`,
`𝔼 max_i |⟨σ_i⟩ - tanh (β (N+1)^{-1/2} ∑_j g_{ij} ⟨σ_j⟩ + h - β² (1-q) ⟨σ_i⟩)|
  ≤ K / (N+1)^{1/2-ε}`. -/
theorem sk_tap_uniform (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (hβ₀' : 4 * β₀ ^ 2 < 1) (h : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ β : ℝ, 0 ≤ β → β ≤ β₀ → ∀ q : ℝ,
      (∫ x : ℝ, Real.tanh (β * Real.sqrt q * x + h) ^ 2 ∂(gaussianReal 0 1) = q) →
      ∀ N : ℕ, 0 < N →
      ∫ g : FinPairs (N + 1) → ℝ, Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (N + 1) =>
        |∫ σ : Fin (N + 1) → ℤˣ, ((σ i : ℤ) : ℝ)
            ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g)) -
          Real.tanh ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β * ∑ j : Fin (N + 1),
            (if hij : i < j then g ⟨(i, j), hij⟩
              else if hji : j < i then g ⟨(j, i), hji⟩ else 0) *
            (∫ σ : Fin (N + 1) → ℤˣ, ((σ j : ℤ) : ℝ)
              ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g))) + h -
            β ^ 2 * (1 - q) * ∫ σ : Fin (N + 1) → ℤˣ, ((σ i : ℤ) : ℝ)
              ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g)))|)
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ≤
        K / ((N : ℝ) + 1) ^ (1 / 2 - ε) := by
  obtain ⟨k, hk, hεk⟩ : ∃ k : ℕ, 1 ≤ k ∧ 1 / (2 * (k : ℝ)) ≤ ε := by
    refine ⟨⌈1 / (2 * ε)⌉₊ + 1, by omega, ?_⟩
    have h1 : 1 / (2 * ε) ≤ ((⌈1 / (2 * ε)⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil (1 / (2 * ε))]
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at h1
    nlinarith
  obtain ⟨K, hK0, hK⟩ := sk_tap_equation β₀ hβ₀ hβ₀' h hk
  refine ⟨1 + K, by positivity, fun β hβ0 hββ₀ q hq N hN => ?_⟩
  set P : Measure (FinPairs (N + 1) → ℝ) := Measure.pi fun _ => gaussianReal 0 1 with hP
  let G : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → Fin (N + 1) → ℝ := fun g i j =>
    if hij : i < j then g ⟨(i, j), hij⟩ else if hji : j < i then g ⟨(j, i), hji⟩ else 0
  have hG : ∀ g i j, G g i j = if hij : i < j then g ⟨(i, j), hij⟩
      else if hji : j < i then g ⟨(j, i), hji⟩ else 0 := fun _ _ _ => rfl
  let m : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g j =>
    ∫ σ : Fin (N + 1) → ℤˣ, ((σ j : ℤ) : ℝ) ∂(Measure.count.tilted (skGibbsEnergy (N + 1) β h g))
  let Δ : Fin (N + 1) → (FinPairs (N + 1) → ℝ) → ℝ := fun i g =>
    m g i - Real.tanh ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β * ∑ j, G g i j * m g j + h -
      β ^ 2 * (1 - q) * m g i)
  have hm_meas : ∀ j, Measurable fun g => m g j := fun j =>
    measurable_integral_spin_skGibbsEnergy (N + 1) β h j
  have hG_meas : ∀ i j, Measurable fun g => G g i j := fun i j => by
    simp only [G]
    split_ifs
    exacts [measurable_pi_apply _, measurable_pi_apply _, measurable_const]
  have hmeas : ∀ i, Measurable (Δ i) := fun i =>
    (hm_meas i).sub (Real.continuous_tanh.measurable.comp (((measurable_const.mul
      (Finset.measurable_sum _ fun j _ => (hG_meas i j).mul (hm_meas j))).add_const h).sub
      (measurable_const.mul (hm_meas i))))
  have hbdd : ∀ i g, |Δ i g| ≤ 2 := fun i g => by
    have h1 : |m g i| ≤ 1 := abs_integral_spin_count_tilted_le _ i
    have h2 := (Real.abs_tanh_lt_one ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β * ∑ j, G g i j * m g j + h -
      β ^ 2 * (1 - q) * m g i)).le
    exact (abs_sub _ _).trans (by linarith)
  have hint : ∀ i, Integrable (fun g => Δ i g ^ (2 * k)) P := fun i =>
    Integrable.of_bound ((hmeas i).pow_const _).aestronglyMeasurable (2 ^ (2 * k))
      (ae_of_all _ fun g => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hbdd i g) _)
  have hsymm : ∀ π : Equiv.Perm (Fin (N + 1)), ∃ φ : (FinPairs (N + 1) → ℝ) → _,
      MeasurePreserving φ P P ∧ ∀ i g, Δ i (φ g) = Δ (π i) g := fun π =>
    ⟨fun g => g ∘ (pairPerm π.symm).symm, measurePreserving_comp_pairPerm (gaussianReal 0 1) π.symm,
      fun i g => tap_defect_comp_pairPerm β h ((Real.sqrt ((N : ℝ) + 1))⁻¹ * β)
        (β ^ 2 * (1 - q)) G hG π.symm g i⟩
  have hlast : ∫ g, Δ (Fin.last N) g ^ (2 * k) ∂P ≤ K / ((N : ℝ) + 1) ^ k := by
    refine le_trans (le_of_eq (integral_congr_ae (ae_of_all _ fun g => ?_)))
      (hK β hβ0 hββ₀ q hq N hN)
    change (m g (Fin.last N) -
      Real.tanh (_ * ∑ j, G g (Fin.last N) j * m g j + h - _)) ^ (2 * k) = _
    rw [sum_symCoupling_last G hG (m g) g]
  have hmom : ∀ i, ∫ g, Δ i g ^ (2 * k) ∂P ≤ K / (Fintype.card (Fin (N + 1)) : ℝ) ^ k :=
    fun i => by
      rw [integral_comp_eq_of_perm_equivariant Δ hmeas (G := fun x => x ^ (2 * k))
        (measurable_id.pow_const _) hsymm i (Fin.last N)]
      simpa using hlast
  have hmax := integral_sup'_abs_le_rpow (P := P) Δ hk hint hmom
  refine hmax.trans ?_
  have hM1 : (1 : ℝ) ≤ (Fintype.card (Fin (N + 1)) : ℝ) := by
    simp only [Fintype.card_fin]; push_cast; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have h2 := rpow_neg_div_le_of_inv_le hM1 hk hεk
  rw [Fintype.card_fin, Nat.cast_succ] at h2 ⊢
  calc _ ≤ (1 + K) * ((N : ℝ) + 1) ^ (-(1 / 2 - ε)) := by gcongr
    _ = _ := by
        rw [Real.rpow_neg (by positivity)]
        exact (div_eq_mul_inv _ _).symm

end SpinGlasses
