/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKOverlapCLTGlobalMoments

/-!
# The overlap against a product of blocks (Theorem 1.10.1, the computation after Eq. (1.328))

For pairwise disjoint blocks `{ca u, da u}` of replicas, the averages
`𝔼 ⟨(R_{xy} - q) ∏_u (R_{ca u, da u} - q)⟩` are classified by how `x` and `y` meet the blocks. The
exact integration of the replicas that are touched by no other factor
(`SKOverlapCLTGlobalIntegrate.lean`) and the moments of `SKOverlapCLTGlobalMoments.lean` give,
with `ν_j = 𝔼 T^j`, `m` the number of blocks, and `t` the number of members of `{x, y}` that lie in
a block and `e = 1` if `{x, y}` is itself a block,
`ν_{m+1} + (t B² + e A²) ν_{m-1} / (N+1) + O(m+2)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real

namespace SpinGlasses

/-- The integral of a sum of four integrable functions. -/
theorem integral_add_four {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b c d : α → ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ) (hc : Integrable c μ) (hd : Integrable d μ) :
    ∫ x, (a x + b x + c x + d x) ∂μ = (∫ x, a x ∂μ) + (∫ x, b x ∂μ) + (∫ x, c x ∂μ) +
      ∫ x, d x ∂μ := by
  rw [integral_add (f := fun x => a x + b x + c x) (g := d) ((ha.add hb).add hc) hd,
    integral_add (f := fun x => a x + b x) (g := c) (ha.add hb) hc,
    integral_add (f := a) (g := b) ha hb]

/-- **Integrability of the disorder averages.** A bounded replica average that is measurable in the
disorder, multiplied by a power of the global variable `T`, is integrable in the disorder. -/
theorem sk_global_integrable (N : ℕ) (β h q : ℝ)
    {R : Type*} [Fintype R]
    (F : (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ)
    (hF : ∀ ρ, Measurable fun g => F g ρ) (M : ℝ) (hM : ∀ g ρ, |F g ρ| ≤ M) (j : ℕ) :
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tg : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
      ((N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i) - q
    Integrable (fun g => Tg g ^ j * ∫ ρ : R → Fin (N + 1) → ℤˣ, F g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)))
      (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  classical
  intro E bmean Tg
  have hmeasE : ∀ σ, Measurable fun g : FinPairs (N + 1) → ℝ => E g σ := fun σ => by
    dsimp only [E]
    fun_prop
  have hbm : ∀ i, Measurable fun g : FinPairs (N + 1) → ℝ => bmean g i := fun i =>
    measurable_integral_count_tilted (fun g σ => E g σ) hmeasE (fun σ => (σ i : ℝ))
  have hb1 : ∀ g i, |bmean g i| ≤ 1 := fun g i => abs_integral_spin_le_one (E g) i
  have hTm : Measurable Tg := by
    refine Measurable.sub (measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_))
      measurable_const
    exact (hbm i).mul (hbm i)
  have hTb : ∀ g, |Tg g| ≤ 1 + |q| := fun g => by
    refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N + 1 : ℝ)⁻¹)]
    have : |∑ i, bmean g i * bmean g i| ≤ ∑ _i : Fin (N + 1), (1 : ℝ) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact (mul_le_mul (hb1 g i) (hb1 g i) (abs_nonneg _) zero_le_one).trans
          (by norm_num))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at this
    calc (N + 1 : ℝ)⁻¹ * _ ≤ (N + 1 : ℝ)⁻¹ * ((N + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 := by
        push_cast
        field_simp
  have hint := integrable_integral_pi_count_tilted_of_bound (μ := Measure.pi fun _ :
      FinPairs (N + 1) => gaussianReal 0 1) (fun g σ => E g σ) hmeasE F hF M hM
  refine Integrable.bdd_mul (c := (1 + |q|) ^ j) hint
    ((hTm.pow_const j).aestronglyMeasurable) (Filter.Eventually.of_forall fun g => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hTb g) j

/-- **Integrability of the monomials in `T`, `T_x`, `T_{xy}`.** For every `j` the functions
`g ↦ T^j`, `g ↦ T^j 𝔼 T_x²`, `g ↦ T^j 𝔼 T_{xy}²` and `g ↦ T^j 𝔼 T_{xy} T_x T_y` are integrable. -/
theorem sk_global_integrable_monomials (N : ℕ) (β h q : ℝ)
    {R : Type*} [Fintype R] (x y : R) (j : ℕ) :
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tg : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
      ((N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i) - q
    let A : R → (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ := fun z g ρ =>
      (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ z i : ℝ) - bmean g i) * bmean g i
    let P : R → R → (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ := fun z z' g ρ =>
      (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ z i : ℝ) - bmean g i) * ((ρ z' i : ℝ) - bmean g i)
    Integrable (fun g => Tg g ^ j) (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ∧
    Integrable (fun g => Tg g ^ j * ∫ ρ : R → Fin (N + 1) → ℤˣ, A x g ρ ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)))
      (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ∧
    Integrable (fun g => Tg g ^ j * ∫ ρ : R → Fin (N + 1) → ℤˣ, P x y g ρ ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)))
      (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) ∧
    Integrable (fun g => Tg g ^ j * ∫ ρ : R → Fin (N + 1) → ℤˣ, P x y g ρ * A x g ρ * A y g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)))
      (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  classical
  intro E bmean Tg A P
  have hmeasE : ∀ σ, Measurable fun g : FinPairs (N + 1) → ℝ => E g σ := fun σ => by
    dsimp only [E]
    fun_prop
  have hbm : ∀ i, Measurable fun g : FinPairs (N + 1) → ℝ => bmean g i := fun i =>
    measurable_integral_count_tilted (fun g σ => E g σ) hmeasE (fun σ => (σ i : ℝ))
  have hb1 : ∀ g i, |bmean g i| ≤ 1 := fun g i => abs_integral_spin_le_one (E g) i
  have hside : ∀ (ρ : R → Fin (N + 1) → ℤˣ) g z i, |(ρ z i : ℝ) - bmean g i| ≤ 2 :=
    fun ρ g z i => (abs_sub _ _).trans (add_le_add (abs_units_cast_le_one _) (hb1 g i)) |>.trans
      (by norm_num)
  have hsum : ∀ (w : Fin (N + 1) → ℝ) (c : ℝ), (∀ i, |w i| ≤ c) →
      |(N + 1 : ℝ)⁻¹ * ∑ i, w i| ≤ c := fun w c hw => by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N + 1 : ℝ)⁻¹)]
    have : |∑ i, w i| ≤ ∑ _i : Fin (N + 1), c :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hw i)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    calc (N + 1 : ℝ)⁻¹ * _ ≤ (N + 1 : ℝ)⁻¹ * (((N + 1 : ℕ) : ℝ) * c) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = c := by
        push_cast
        field_simp
  have hAm : ∀ z ρ, Measurable fun g => A z g ρ := fun z ρ => by
    refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
    exact (measurable_const.sub (hbm i)).mul (hbm i)
  have hPm : ∀ z z' ρ, Measurable fun g => P z z' g ρ := fun z z' ρ => by
    refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
    exact (measurable_const.sub (hbm i)).mul (measurable_const.sub (hbm i))
  have hAb : ∀ z g ρ, |A z g ρ| ≤ 2 := fun z g ρ =>
    hsum _ 2 fun i => by
      rw [abs_mul]
      exact (mul_le_mul (hside ρ g z i) (hb1 g i) (abs_nonneg _) (by norm_num)).trans
        (by norm_num)
  have hPb : ∀ z z' g ρ, |P z z' g ρ| ≤ 4 := fun z z' g ρ =>
    hsum _ 4 fun i => by
      rw [abs_mul]
      exact (mul_le_mul (hside ρ g z i) (hside ρ g z' i) (abs_nonneg _) (by norm_num)).trans
        (by norm_num)
  have h1 := sk_global_integrable N β h q (R := R) (fun _ _ => 1) (fun _ => measurable_const) 1
    (fun _ _ => by simp) j
  refine ⟨by simpa using h1, ?_, ?_, ?_⟩
  · exact sk_global_integrable N β h q (R := R) (fun g ρ => A x g ρ ^ 2)
      (fun ρ => (hAm x ρ).pow_const 2) 4 (fun g ρ => by
        rw [abs_pow]
        nlinarith [abs_nonneg (A x g ρ), hAb x g ρ]) j
  · exact sk_global_integrable N β h q (R := R) (fun g ρ => P x y g ρ ^ 2)
      (fun ρ => (hPm x y ρ).pow_const 2) 16 (fun g ρ => by
        rw [abs_pow]
        nlinarith [abs_nonneg (P x y g ρ), hPb x y g ρ]) j
  · exact sk_global_integrable N β h q (R := R) (fun g ρ => P x y g ρ * A x g ρ * A y g ρ)
      (fun ρ => ((hPm x y ρ).mul (hAm x ρ)).mul (hAm y ρ)) 32 (fun g ρ => by
        rw [abs_mul, abs_mul]
        have := hPb x y g ρ
        have := hAb x g ρ
        have := hAb y g ρ
        have h0 := abs_nonneg (P x y g ρ)
        have h0' := abs_nonneg (A x g ρ)
        have h0'' := abs_nonneg (A y g ρ)
        nlinarith [mul_le_mul ‹|P x y g ρ| ≤ 4› ‹|A x g ρ| ≤ 2› h0' (by norm_num : (0:ℝ) ≤ 4)]) j


/-- **One replica of the pair lies in a block, the other in none.** -/
theorem sk_overlap_blocks_one_touched_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R V : Type*} [Fintype R] [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R)) {x y : R}
    (u0 : V) (x' : R) (hx0 : (ca u0 = x ∧ da u0 = x') ∨ (ca u0 = x' ∧ da u0 = x))
    (hy : ∀ u, y ≠ ca u ∧ y ≠ da u) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tg : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
      ((N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i) - q
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let ν : ℕ → ℝ := fun j =>
      ∫ g, Tg g ^ j ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let B2 : ℝ := (q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) /
      (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) / (N + 1 : ℝ)
    let Φ : R → R → ℝ := fun x y => ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, (ρ x i : ℝ) * (ρ y i : ℝ)) - q) *
          ∏ u, (((N + 1 : ℝ)⁻¹ * ∑ i, (ρ (ca u) i : ℝ) * (ρ (da u) i : ℝ)) - q)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    |Φ x y - (ν (Fintype.card V + 1) + B2 * ν (Fintype.card V - 1))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card V + 2 : ℕ) : ℝ) / 2) := by
  classical
  have hxy : x ≠ y := by
    rcases hx0 with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact fun h => (hy u0).1 (h1 ▸ h.symm)
    · exact fun h => (hy u0).2 (h2 ▸ h.symm)
  have hm : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨u0⟩
  obtain ⟨C, hC0, hC⟩ := sk_T_single_square_moment_uniform β₀ hβ₀ x (Fintype.card V - 1)
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro E bmean Tg qh α ν B2 Φ
  have h1 := hC β h q hfix hb N
  have hint := sk_global_integrable_monomials N β h q x y (Fintype.card V + 1)
  have hint' := sk_global_integrable_monomials N β h q x y (Fintype.card V - 1)
  have hg : ∀ g, (∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, (ρ x i : ℝ) * (ρ y i : ℝ)) - q) *
          ∏ u, (((N + 1 : ℝ)⁻¹ * ∑ i, (ρ (ca u) i : ℝ) * (ρ (da u) i : ℝ)) - q)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))) =
      Tg g ^ (Fintype.card V + 1) + Tg g ^ (Fintype.card V - 1) *
        ∫ ρ : R → Fin (N + 1) → ℤˣ, (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) *
          bmean g i)) ^ 2 ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)) := fun g => by
    have := integral_pi_overlap_blocks_one_touched (Measure.count.tilted (E g))
      (fun σ i => (σ i : ℝ)) (bmean g) (fun i => rfl) ((N + 1 : ℝ)⁻¹) q
      (fun ρ a a' => ((N + 1 : ℝ)⁻¹ * ∑ i, (ρ a i : ℝ) * (ρ a' i : ℝ)) - q) (fun _ _ _ => rfl)
      (Tg g) rfl (fun z ρ => (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ z i : ℝ) - bmean g i) * bmean g i)
      (fun _ _ => rfl)
      (fun a a' ρ => (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ a i : ℝ) - bmean g i) * ((ρ a' i : ℝ) - bmean g i))
      (fun _ _ _ => rfl) ca da hinj hxy u0 x' hx0 hy
    rw [this]
    have hp : Tg g ^ (Fintype.card V + 1) = Tg g ^ 2 * Tg g ^ (Fintype.card V - 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hp]
    ring
  have e1 : Φ x y = ν (Fintype.card V + 1) +
      ∫ g, Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * bmean g i)) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    change _ = (∫ g, Tg g ^ (Fintype.card V + 1) ∂(Measure.pi fun _ : FinPairs (N + 1) =>
      gaussianReal 0 1)) + _
    rw [← integral_add hint.1 hint'.2.1]
    exact integral_congr_ae (Filter.Eventually.of_forall hg)
  have h1' : |(∫ g, Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * bmean g i)) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      B2 * ν (Fintype.card V - 1)| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card V - 1 + 3 : ℕ) : ℝ) / 2) := h1
  have hexp : Fintype.card V - 1 + 3 = Fintype.card V + 2 := by omega
  rw [hexp] at h1'
  rw [e1]
  convert h1' using 2
  ring

/-- **The pair `{x, y}` is itself a block.** -/
theorem sk_overlap_blocks_same_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R V : Type*} [Fintype R] [LinearOrder R] [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R)) {x y : R}
    (u0 : V) (hx0 : (ca u0 = x ∧ da u0 = y) ∨ (ca u0 = y ∧ da u0 = x)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tg : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
      ((N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i) - q
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let ν : ℕ → ℝ := fun j =>
      ∫ g, Tg g ^ j ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let B2 : ℝ := (q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) /
      (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) / (N + 1 : ℝ)
    let A2 : ℝ := α / (1 - β ^ 2 * α) / (N + 1 : ℝ)
    let Φ : R → R → ℝ := fun x y => ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, (ρ x i : ℝ) * (ρ y i : ℝ)) - q) *
          ∏ u, (((N + 1 : ℝ)⁻¹ * ∑ i, (ρ (ca u) i : ℝ) * (ρ (da u) i : ℝ)) - q)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    |Φ x y - (ν (Fintype.card V + 1) + (A2 + 2 * B2) * ν (Fintype.card V - 1))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card V + 2 : ℕ) : ℝ) / 2) := by
  classical
  have hxy : x ≠ y := by
    rcases hx0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h1 ▸ h2 ▸ (sum_elim_injective_facts hinj).2.2 u0 u0
    · exact h1 ▸ h2 ▸ ((sum_elim_injective_facts hinj).2.2 u0 u0).symm
  have hm : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨u0⟩
  obtain ⟨C₁, hC₁0, hC₁⟩ := sk_T_single_square_moment_uniform β₀ hβ₀ x (Fintype.card V - 1)
  obtain ⟨C₂, hC₂0, hC₂⟩ := sk_T_single_square_moment_uniform β₀ hβ₀ y (Fintype.card V - 1)
  obtain ⟨C₃, hC₃0, hC₃⟩ := sk_T_pair_square_moment_uniform β₀ hβ₀ hxy (Fintype.card V - 1)
  refine ⟨C₁ + C₂ + C₃, by positivity, fun β h q hfix hb N => ?_⟩
  intro E bmean Tg qh α ν B2 A2 Φ
  have h1 := hC₁ β h q hfix hb N
  have h2 := hC₂ β h q hfix hb N
  have h3 := hC₃ β h q hfix hb N
  have hint := sk_global_integrable_monomials N β h q x y (Fintype.card V + 1)
  have hint' := sk_global_integrable_monomials N β h q x y (Fintype.card V - 1)
  have hint'' := sk_global_integrable_monomials N β h q y x (Fintype.card V - 1)
  have hg : ∀ g, (∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, (ρ x i : ℝ) * (ρ y i : ℝ)) - q) *
          ∏ u, (((N + 1 : ℝ)⁻¹ * ∑ i, (ρ (ca u) i : ℝ) * (ρ (da u) i : ℝ)) - q)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))) =
      Tg g ^ (Fintype.card V + 1) +
      Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * ((ρ y i : ℝ) - bmean g i))) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)) +
      Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * bmean g i)) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)) +
      Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ y i : ℝ) - bmean g i) * bmean g i)) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)) := fun g => by
    have := integral_pi_overlap_blocks_same (Measure.count.tilted (E g))
      (fun σ i => (σ i : ℝ)) (bmean g) (fun i => rfl) ((N + 1 : ℝ)⁻¹) q
      (fun ρ a a' => ((N + 1 : ℝ)⁻¹ * ∑ i, (ρ a i : ℝ) * (ρ a' i : ℝ)) - q) (fun _ _ _ => rfl)
      (Tg g) rfl (fun z ρ => (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ z i : ℝ) - bmean g i) * bmean g i)
      (fun _ _ => rfl)
      (fun a a' ρ => (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ a i : ℝ) - bmean g i) * ((ρ a' i : ℝ) - bmean g i))
      (fun _ _ _ => rfl) ca da hinj hxy u0 hx0
    rw [this]
    have hp : Tg g ^ (Fintype.card V + 1) = Tg g ^ 2 * Tg g ^ (Fintype.card V - 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hp]
    ring
  have e1 : Φ x y = ν (Fintype.card V + 1) +
      (∫ g, Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * ((ρ y i : ℝ) - bmean g i))) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) +
      (∫ g, Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * bmean g i)) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) +
      (∫ g, Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ y i : ℝ) - bmean g i) * bmean g i)) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) := by
    exact (integral_congr_ae (Filter.Eventually.of_forall hg)).trans
      (integral_add_four hint.1 hint'.2.2.1 hint'.2.1 hint''.2.1)
  have hexp : Fintype.card V - 1 + 3 = Fintype.card V + 2 := by omega
  have h1' : |(∫ g, Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * bmean g i)) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      B2 * ν (Fintype.card V - 1)| ≤
      C₁ / ((N : ℝ) + 1) ^ (((Fintype.card V + 2 : ℕ) : ℝ) / 2) := by
    rw [← hexp]; exact h1
  have h2' : |(∫ g, Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ y i : ℝ) - bmean g i) * bmean g i)) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      B2 * ν (Fintype.card V - 1)| ≤
      C₂ / ((N : ℝ) + 1) ^ (((Fintype.card V + 2 : ℕ) : ℝ) / 2) := by
    rw [← hexp]; exact h2
  have h3' : |(∫ g, Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * ((ρ y i : ℝ) - bmean g i))) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      A2 * ν (Fintype.card V - 1)| ≤
      C₃ / ((N : ℝ) + 1) ^ (((Fintype.card V + 2 : ℕ) : ℝ) / 2) := by
    rw [← hexp]; exact h3
  rw [e1]
  generalize (∫ g, Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * ((ρ y i : ℝ) - bmean g i))) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) = IP at h3' ⊢
  generalize (∫ g, Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * bmean g i)) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) = IX at h1' ⊢
  generalize (∫ g, Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ y i : ℝ) - bmean g i) * bmean g i)) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) = IY at h2' ⊢
  have hsplit : ν (Fintype.card V + 1) + IP + IX + IY -
      (ν (Fintype.card V + 1) + (A2 + 2 * B2) * ν (Fintype.card V - 1)) =
      (IP - A2 * ν (Fintype.card V - 1)) + (IX - B2 * ν (Fintype.card V - 1)) +
        (IY - B2 * ν (Fintype.card V - 1)) := by ring
  rw [hsplit]
  refine (abs_add_three _ _ _).trans ?_
  have : (C₁ + C₂ + C₃) / ((N : ℝ) + 1) ^ (((Fintype.card V + 2 : ℕ) : ℝ) / 2) =
      C₃ / ((N : ℝ) + 1) ^ (((Fintype.card V + 2 : ℕ) : ℝ) / 2) +
      C₁ / ((N : ℝ) + 1) ^ (((Fintype.card V + 2 : ℕ) : ℝ) / 2) +
      C₂ / ((N : ℝ) + 1) ^ (((Fintype.card V + 2 : ℕ) : ℝ) / 2) := by ring
  rw [this]
  exact add_le_add (add_le_add h3' h1') h2'

/-- **The two replicas lie in different blocks.** -/
theorem sk_overlap_blocks_two_touched_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R V : Type*} [Fintype R] [LinearOrder R] [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R)) {x y : R}
    (u0 u1 : V) (hu01 : u0 ≠ u1) (x' y' : R)
    (hx0 : (ca u0 = x ∧ da u0 = x') ∨ (ca u0 = x' ∧ da u0 = x))
    (hy0 : (ca u1 = y ∧ da u1 = y') ∨ (ca u1 = y' ∧ da u1 = y)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tg : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
      ((N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i) - q
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let ν : ℕ → ℝ := fun j =>
      ∫ g, Tg g ^ j ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let B2 : ℝ := (q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) /
      (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) / (N + 1 : ℝ)
    let Φ : R → R → ℝ := fun x y => ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, (ρ x i : ℝ) * (ρ y i : ℝ)) - q) *
          ∏ u, (((N + 1 : ℝ)⁻¹ * ∑ i, (ρ (ca u) i : ℝ) * (ρ (da u) i : ℝ)) - q)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    |Φ x y - (ν (Fintype.card V + 1) + (2 * B2) * ν (Fintype.card V - 1))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card V + 2 : ℕ) : ℝ) / 2) := by
  classical
  obtain ⟨hxx', hfx⟩ := block_facts hinj hx0
  have hxy : x ≠ y := by
    obtain ⟨h1, h2, h3, h4⟩ := hfx u1 hu01.symm
    rcases hy0 with ⟨h5, -⟩ | ⟨-, h5⟩
    · exact fun h => h1 (h5.trans h.symm)
    · exact fun h => h3 (h5.trans h.symm)
  have hm : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff.mpr ⟨u0, u1, hu01⟩
  obtain ⟨C₁, hC₁0, hC₁⟩ := sk_T_single_square_moment_uniform β₀ hβ₀ x (Fintype.card V - 1)
  obtain ⟨C₂, hC₂0, hC₂⟩ := sk_T_single_square_moment_uniform β₀ hβ₀ y (Fintype.card V - 1)
  obtain ⟨C₃, hC₃0, hC₃⟩ := sk_T_pair_two_singles_moment_uniform β₀ hβ₀ hxy (Fintype.card V - 2)
  refine ⟨C₁ + C₂ + C₃, by positivity, fun β h q hfix hb N => ?_⟩
  intro E bmean Tg qh α ν B2 Φ
  have h1 := hC₁ β h q hfix hb N
  have h2 := hC₂ β h q hfix hb N
  have h3 := hC₃ β h q hfix hb N
  have hint := sk_global_integrable_monomials N β h q x y (Fintype.card V + 1)
  have hint' := sk_global_integrable_monomials N β h q x y (Fintype.card V - 1)
  have hint'' := sk_global_integrable_monomials N β h q y x (Fintype.card V - 1)
  have hint3 := sk_global_integrable_monomials N β h q x y (Fintype.card V - 2)
  have hg : ∀ g, (∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, (ρ x i : ℝ) * (ρ y i : ℝ)) - q) *
          ∏ u, (((N + 1 : ℝ)⁻¹ * ∑ i, (ρ (ca u) i : ℝ) * (ρ (da u) i : ℝ)) - q)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))) =
      Tg g ^ (Fintype.card V + 1) +
      Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * bmean g i)) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)) +
      Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ y i : ℝ) - bmean g i) * bmean g i)) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)) +
      Tg g ^ (Fintype.card V - 2) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * ((ρ y i : ℝ) - bmean g i)) *
        ((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * bmean g i) *
        ((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ y i : ℝ) - bmean g i) * bmean g i)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)) := fun g => by
    have := integral_pi_overlap_blocks_two_touched (Measure.count.tilted (E g))
      (fun σ i => (σ i : ℝ)) (bmean g) (fun i => rfl) ((N + 1 : ℝ)⁻¹) q
      (fun ρ a a' => ((N + 1 : ℝ)⁻¹ * ∑ i, (ρ a i : ℝ) * (ρ a' i : ℝ)) - q) (fun _ _ _ => rfl)
      (Tg g) rfl (fun z ρ => (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ z i : ℝ) - bmean g i) * bmean g i)
      (fun _ _ => rfl)
      (fun a a' ρ => (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ a i : ℝ) - bmean g i) * ((ρ a' i : ℝ) - bmean g i))
      (fun _ _ _ => rfl) ca da hinj hxy u0 u1 hu01 x' y' hx0 hy0
    rw [this]
    have hp : Tg g ^ (Fintype.card V + 1) = Tg g ^ 3 * Tg g ^ (Fintype.card V - 2) := by
      rw [← pow_add]
      congr 1
      omega
    have hp' : Tg g ^ (Fintype.card V - 1) = Tg g * Tg g ^ (Fintype.card V - 2) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hp, hp']
    ring
  have e1 : Φ x y = ν (Fintype.card V + 1) +
      (∫ g, Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * bmean g i)) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) +
      (∫ g, Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ y i : ℝ) - bmean g i) * bmean g i)) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) +
      (∫ g, Tg g ^ (Fintype.card V - 2) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * ((ρ y i : ℝ) - bmean g i)) *
        ((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * bmean g i) *
        ((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ y i : ℝ) - bmean g i) * bmean g i)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) := by
    exact (integral_congr_ae (Filter.Eventually.of_forall hg)).trans
      (integral_add_four hint.1 hint'.2.1 hint''.2.1 hint3.2.2.2)
  have hexp : Fintype.card V - 1 + 3 = Fintype.card V + 2 := by omega
  have hexp3 : Fintype.card V - 2 + 4 = Fintype.card V + 2 := by omega
  have h1' : |(∫ g, Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * bmean g i)) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      B2 * ν (Fintype.card V - 1)| ≤
      C₁ / ((N : ℝ) + 1) ^ (((Fintype.card V + 2 : ℕ) : ℝ) / 2) := by
    rw [← hexp]; exact h1
  have h2' : |(∫ g, Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ y i : ℝ) - bmean g i) * bmean g i)) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      B2 * ν (Fintype.card V - 1)| ≤
      C₂ / ((N : ℝ) + 1) ^ (((Fintype.card V + 2 : ℕ) : ℝ) / 2) := by
    rw [← hexp]; exact h2
  have h3' : |(∫ g, Tg g ^ (Fintype.card V - 2) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * ((ρ y i : ℝ) - bmean g i)) *
        ((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * bmean g i) *
        ((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ y i : ℝ) - bmean g i) * bmean g i)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))| ≤
      C₃ / ((N : ℝ) + 1) ^ (((Fintype.card V + 2 : ℕ) : ℝ) / 2) := by
    rw [← hexp3]; exact h3
  rw [e1]
  generalize (∫ g, Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * bmean g i)) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) = IX at h1' ⊢
  generalize (∫ g, Tg g ^ (Fintype.card V - 1) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ y i : ℝ) - bmean g i) * bmean g i)) ^ 2
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) = IY at h2' ⊢
  generalize (∫ g, Tg g ^ (Fintype.card V - 2) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * ((ρ y i : ℝ) - bmean g i)) *
        ((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - bmean g i) * bmean g i) *
        ((N + 1 : ℝ)⁻¹ * ∑ i, ((ρ y i : ℝ) - bmean g i) * bmean g i)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) = IZ at h3' ⊢
  have hsplit : ν (Fintype.card V + 1) + IX + IY + IZ -
      (ν (Fintype.card V + 1) + (2 * B2) * ν (Fintype.card V - 1)) =
      (IX - B2 * ν (Fintype.card V - 1)) + (IY - B2 * ν (Fintype.card V - 1)) + (IZ - 0) := by
    ring
  rw [hsplit]
  refine (abs_add_three _ _ _).trans ?_
  have : (C₁ + C₂ + C₃) / ((N : ℝ) + 1) ^ (((Fintype.card V + 2 : ℕ) : ℝ) / 2) =
      C₁ / ((N : ℝ) + 1) ^ (((Fintype.card V + 2 : ℕ) : ℝ) / 2) +
      C₂ / ((N : ℝ) + 1) ^ (((Fintype.card V + 2 : ℕ) : ℝ) / 2) +
      C₃ / ((N : ℝ) + 1) ^ (((Fintype.card V + 2 : ℕ) : ℝ) / 2) := by ring
  rw [this]
  exact add_le_add (add_le_add h1' h2') (by simpa using h3')

/-- **No replica of the pair lies in a block.** -/
theorem sk_overlap_blocks_untouched_exact (N : ℕ) (β h q : ℝ)
    {R V : Type*} [Fintype R] [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R)) {x y : R} (hxy : x ≠ y)
    (hx : ∀ u, x ≠ ca u ∧ x ≠ da u) (hy : ∀ u, y ≠ ca u ∧ y ≠ da u) :
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tg : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
      ((N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i) - q
    let ν : ℕ → ℝ := fun j =>
      ∫ g, Tg g ^ j ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let Φ : R → R → ℝ := fun x y => ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, (ρ x i : ℝ) * (ρ y i : ℝ)) - q) *
          ∏ u, (((N + 1 : ℝ)⁻¹ * ∑ i, (ρ (ca u) i : ℝ) * (ρ (da u) i : ℝ)) - q)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    Φ x y = ν (Fintype.card V + 1) := by
  classical
  intro E bmean Tg ν Φ
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  have := integral_pi_overlap_blocks_untouched (Measure.count.tilted (E g))
      (fun σ i => (σ i : ℝ)) (bmean g) (fun i => rfl) ((N + 1 : ℝ)⁻¹) q
      (fun ρ a a' => ((N + 1 : ℝ)⁻¹ * ∑ i, (ρ a i : ℝ) * (ρ a' i : ℝ)) - q) (fun _ _ _ => rfl)
      (Tg g) rfl (fun z ρ => (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ z i : ℝ) - bmean g i) * bmean g i)
      (fun _ _ => rfl)
      (fun a a' ρ => (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ a i : ℝ) - bmean g i) * ((ρ a' i : ℝ) - bmean g i))
      (fun _ _ _ => rfl) ca da hinj hxy hx hy
  exact this

/-- A member of a block has a partner in that block. -/
theorem exists_block_partner {V R : Type*} (ca da : V → R) {x : R} {u : V}
    (hu : x = ca u ∨ x = da u) :
    ∃ x', (ca u = x ∧ da u = x') ∨ (ca u = x' ∧ da u = x) := by
  rcases hu with h | h
  · exact ⟨da u, Or.inl ⟨h.symm, rfl⟩⟩
  · exact ⟨ca u, Or.inr ⟨rfl, h.symm⟩⟩

/-- **The classification of `𝔼 (R_{xy} - q) ∏_u (R_{ca u, da u} - q)`.** With `t` the number of
members of `{x, y}` lying in a block and `e = 1` if `{x, y}` is a block, the average is
`ν_{m+1} + (t B² + e A²) ν_{m-1} / (N+1) + O(m+2)` where `m` is the number of blocks. -/
theorem sk_overlap_blocks_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R V : Type*} [Fintype R] [LinearOrder R] [Fintype V] (ca da : V → R)
    (hinj : Function.Injective (Sum.elim ca da : V ⊕ V → R)) {x y : R} (hxy : x ≠ y) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tg : (FinPairs (N + 1) → ℝ) → ℝ := fun g =>
      ((N + 1 : ℝ)⁻¹ * ∑ i, bmean g i * bmean g i) - q
    let qh : ℝ := ∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1
    let α : ℝ := qh - 2 * q + 1
    let ν : ℕ → ℝ := fun j =>
      ∫ g, Tg g ^ j ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let B2 : ℝ := (q - qh) * (1 + β ^ 2 * (α / (1 - β ^ 2 * α))) /
      (1 - β ^ 2 * (1 - 4 * q + 3 * qh)) / (N + 1 : ℝ)
    let A2 : ℝ := α / (1 - β ^ 2 * α) / (N + 1 : ℝ)
    let Φ : R → R → ℝ := fun x y => ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (((N + 1 : ℝ)⁻¹ * ∑ i, (ρ x i : ℝ) * (ρ y i : ℝ)) - q) *
          ∏ u, (((N + 1 : ℝ)⁻¹ * ∑ i, (ρ (ca u) i : ℝ) * (ρ (da u) i : ℝ)) - q)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)
    let tch : R → ℝ := fun z => if ∃ u, z = ca u ∨ z = da u then 1 else 0
    let blk : ℝ := if ∃ u, (x = ca u ∧ y = da u) ∨ (x = da u ∧ y = ca u) then 1 else 0
    |Φ x y - (ν (Fintype.card V + 1) +
        ((tch x + tch y) * B2 + blk * A2) * ν (Fintype.card V - 1))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card V + 2 : ℕ) : ℝ) / 2) := by
  classical
  by_cases htx : ∃ u, x = ca u ∨ x = da u
  · obtain ⟨u0, hu0⟩ := htx
    obtain ⟨x', hx'⟩ := exists_block_partner ca da hu0
    by_cases hty : ∃ u, y = ca u ∨ y = da u
    · obtain ⟨u1, hu1⟩ := hty
      obtain ⟨y', hy'⟩ := exists_block_partner ca da hu1
      by_cases hs : ∃ u, (x = ca u ∧ y = da u) ∨ (x = da u ∧ y = ca u)
      · obtain ⟨u2, hu2⟩ := hs
        obtain ⟨C, hC0, hC⟩ := sk_overlap_blocks_same_uniform β₀ hβ₀ ca da hinj (x := x) (y := y)
          u2 (by rcases hu2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
                 · exact Or.inl ⟨h1.symm, h2.symm⟩
                 · exact Or.inr ⟨h2.symm, h1.symm⟩)
        refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
        intro E bmean Tg qh α ν B2 A2 Φ tch blk
        have key := hC β h q hfix hb N
        have e1 : tch x = 1 := ite_eq_left ⟨u0, hu0⟩
        have e2 : tch y = 1 := ite_eq_left ⟨u1, hu1⟩
        have e3 : blk = 1 := ite_eq_left ⟨u2, hu2⟩
        rw [e1, e2, e3]
        convert key using 4
        ring
      · have hu01 : u0 ≠ u1 := by
          rintro rfl
          apply hs
          refine ⟨u0, ?_⟩
          rcases hu0 with h0 | h0 <;> rcases hu1 with h1 | h1
          · exact absurd (h0.trans h1.symm) hxy
          · exact Or.inl ⟨h0, h1⟩
          · exact Or.inr ⟨h0, h1⟩
          · exact absurd (h0.trans h1.symm) hxy
        obtain ⟨C, hC0, hC⟩ := sk_overlap_blocks_two_touched_uniform β₀ hβ₀ ca da hinj
          u0 u1 hu01 x' y' hx' hy'
        refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
        intro E bmean Tg qh α ν B2 A2 Φ tch blk
        have key := hC β h q hfix hb N
        have e1 : tch x = 1 := ite_eq_left ⟨u0, hu0⟩
        have e2 : tch y = 1 := ite_eq_left ⟨u1, hu1⟩
        have e3 : blk = 0 := ite_eq_right hs
        rw [e1, e2, e3]
        convert key using 4
        ring
    · have hy : ∀ u, y ≠ ca u ∧ y ≠ da u := fun u =>
        ⟨fun h => hty ⟨u, Or.inl h⟩, fun h => hty ⟨u, Or.inr h⟩⟩
      obtain ⟨C, hC0, hC⟩ := sk_overlap_blocks_one_touched_uniform β₀ hβ₀ ca da hinj
        u0 x' hx' hy
      refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
      intro E bmean Tg qh α ν B2 A2 Φ tch blk
      have key := hC β h q hfix hb N
      have e1 : tch x = 1 := ite_eq_left ⟨u0, hu0⟩
      have e2 : tch y = 0 := ite_eq_right hty
      have e3 : blk = 0 := ite_eq_right fun ⟨u, hu⟩ => hty ⟨u, by
        rcases hu with ⟨-, h⟩ | ⟨-, h⟩
        · exact Or.inr h
        · exact Or.inl h⟩
      rw [e1, e2, e3]
      convert key using 4
      ring
  · by_cases hty : ∃ u, y = ca u ∨ y = da u
    · obtain ⟨u1, hu1⟩ := hty
      obtain ⟨y', hy'⟩ := exists_block_partner ca da hu1
      have hx : ∀ u, x ≠ ca u ∧ x ≠ da u := fun u =>
        ⟨fun h => htx ⟨u, Or.inl h⟩, fun h => htx ⟨u, Or.inr h⟩⟩
      obtain ⟨C, hC0, hC⟩ := sk_overlap_blocks_one_touched_uniform β₀ hβ₀ ca da hinj
        u1 y' hy' hx
      refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
      intro E bmean Tg qh α ν B2 A2 Φ tch blk
      have key := hC β h q hfix hb N
      have e1 : tch y = 1 := ite_eq_left ⟨u1, hu1⟩
      have e2 : tch x = 0 := ite_eq_right htx
      have e3 : blk = 0 := ite_eq_right fun ⟨u, hu⟩ => htx ⟨u, by
        rcases hu with ⟨h, -⟩ | ⟨h, -⟩
        · exact Or.inl h
        · exact Or.inr h⟩
      have hcomm : Φ x y = Φ y x := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        refine integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
        beta_reduce
        simp only [mul_comm (ρ x _ : ℝ)]
      rw [e1, e2, e3, hcomm]
      convert key using 4
      ring
    · refine ⟨1, one_pos, fun β h q hfix hb N => ?_⟩
      intro E bmean Tg qh α ν B2 A2 Φ tch blk
      have hx : ∀ u, x ≠ ca u ∧ x ≠ da u := fun u =>
        ⟨fun h => htx ⟨u, Or.inl h⟩, fun h => htx ⟨u, Or.inr h⟩⟩
      have hy : ∀ u, y ≠ ca u ∧ y ≠ da u := fun u =>
        ⟨fun h => hty ⟨u, Or.inl h⟩, fun h => hty ⟨u, Or.inr h⟩⟩
      have key := sk_overlap_blocks_untouched_exact N β h q ca da hinj hxy hx hy
      have e1 : tch x = 0 := ite_eq_right htx
      have e2 : tch y = 0 := ite_eq_right hty
      have e3 : blk = 0 := ite_eq_right fun ⟨u, hu⟩ => htx ⟨u, by
        rcases hu with ⟨h, -⟩ | ⟨h, -⟩
        · exact Or.inl h
        · exact Or.inr h⟩
      rw [e1, e2, e3]
      have : Φ x y = ν (Fintype.card V + 1) := key
      rw [this]
      simp only [add_zero, zero_mul, sub_self, abs_zero]
      positivity

end SpinGlasses
