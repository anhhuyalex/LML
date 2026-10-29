/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FiniteReplicaTilted
public import LeanMachineLearning.SpinGlasses.SKOverlapCLTPairGaussian

/-!
# Live-replica T-moments: integrability and linearity in the disorder

The mixed T-moments of Talagrand, Section 1.10, integrate a product of Gibbs-mean dependent
factors over the replicas and then over the disorder. To expand a product of sums of such factors
into monomials one needs to interchange the disorder integral with a finite sum. The generic
finite-tilted integration calculus supplies this step; the model-specific measurable bounds
are proved once and reused by the exact expansion and later conditional moments.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real

namespace SpinGlasses

/-- **Measurability and boundedness of a product of `T`-sums.** For every choice of data, the
integrand `∏_k ∑_m γ k m T(l,s;x,y)` is measurable in the disorder and uniformly bounded. -/
theorem sk_live_T_family_meas_bound (N : ℕ) (β h q : ℝ)
    {R : Type*} {K M : Type*} [Fintype K] [Fintype M]
    (l s : K → M → Bool) (x y : K → M → R) (γ : K → M → ℝ) :
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tp : Bool → Bool → R → R → (FinPairs (N + 1) → ℝ) →
        (R → Fin (N + 1) → ℤˣ) → ℝ := fun l s x y g ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if l then (ρ x i : ℝ) - bmean g i else bmean g i) *
        (if s then (ρ y i : ℝ) - bmean g i else bmean g i)) - (if l || s then 0 else q)
    (∀ ρ : R → Fin (N + 1) → ℤˣ, Measurable fun g : FinPairs (N + 1) → ℝ =>
      ∏ k, ∑ m, γ k m * Tp (l k m) (s k m) (x k m) (y k m) g ρ) ∧
    ∃ Mb : ℝ, ∀ g (ρ : R → Fin (N + 1) → ℤˣ),
      |∏ k, ∑ m, γ k m * Tp (l k m) (s k m) (x k m) (y k m) g ρ| ≤ Mb := by
  intro E bmean Tp
  have hmeasE : ∀ σ, Measurable fun g : FinPairs (N + 1) → ℝ => E g σ := fun σ => by
    dsimp only [E]
    fun_prop
  have hbm : ∀ i, Measurable fun g : FinPairs (N + 1) → ℝ => bmean g i := fun i =>
    measurable_integral_count_tilted (fun g σ => E g σ) hmeasE (fun σ => (σ i : ℝ))
  have hTp_meas : ∀ l s x y (ρ : R → Fin (N + 1) → ℤˣ),
      Measurable fun g : FinPairs (N + 1) → ℝ => Tp l s x y g ρ := fun l s x y ρ => by
    dsimp only [Tp]
    refine Measurable.sub ?_ measurable_const
    refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
    refine Measurable.mul ?_ ?_
    · cases l
      · simpa using hbm i
      · simp only [ite_true]
        exact measurable_const.sub (hbm i)
    · cases s
      · simpa using hbm i
      · simp only [ite_true]
        exact measurable_const.sub (hbm i)
  have hb1 : ∀ g i, |bmean g i| ≤ 1 := fun g i => abs_integral_spin_le_one (E g) i
  have hTp_bound : ∀ l s x y g (ρ : R → Fin (N + 1) → ℤˣ), |Tp l s x y g ρ| ≤ 4 + |q| :=
    fun l s x y g ρ => by
    have hside : ∀ (c : Bool) (z : R) i, |(if c then (ρ z i : ℝ) - bmean g i else bmean g i)| ≤ 2 :=
      fun c z i => by
      cases c
      · exact (hb1 g i).trans (by norm_num)
      · exact (abs_sub _ _).trans (add_le_add (abs_units_cast_le_one _) (hb1 g i)) |>.trans
          (by norm_num)
    have hsum : |(N + 1 : ℝ)⁻¹ * ∑ i,
        (if l then (ρ x i : ℝ) - bmean g i else bmean g i) *
        (if s then (ρ y i : ℝ) - bmean g i else bmean g i)| ≤ 4 := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N + 1 : ℝ)⁻¹)]
      have : |∑ i, (if l then (ρ x i : ℝ) - bmean g i else bmean g i) *
          (if s then (ρ y i : ℝ) - bmean g i else bmean g i)| ≤ ∑ _i : Fin (N + 1), (4 : ℝ) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact (mul_le_mul (hside l x i) (hside s y i) (abs_nonneg _) (by norm_num)).trans
            (by norm_num))
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      calc (N + 1 : ℝ)⁻¹ * _ ≤ (N + 1 : ℝ)⁻¹ * (((N + 1 : ℕ) : ℝ) * 4) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = 4 := by
          push_cast
          field_simp
    dsimp only [Tp]
    refine (abs_sub _ _).trans (add_le_add hsum ?_)
    split_ifs <;> simp
  refine ⟨fun ρ => Finset.measurable_prod _ fun k _ => Finset.measurable_sum _ fun m _ =>
    measurable_const.mul (hTp_meas _ _ _ _ ρ),
    ∏ k, ∑ m, |γ k m| * (4 + |q|), fun g ρ => ?_⟩
  rw [Finset.abs_prod]
  refine Finset.prod_le_prod₀ (fun k _ => abs_nonneg _) fun k _ => ?_
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hTp_bound _ _ _ _ g ρ) (abs_nonneg _))

/-- **Exact monomial expansion.** A product over factors `k` of finite sums of T-terms with
live replica labels is the sum over monomials `f : K → M` of `∏ γ` times the monomial's
disorder- and replica-averaged product. No hypothesis on the parameters is needed. -/
theorem sk_live_T_expansion_exact (N : ℕ) (β h q : ℝ)
    {R : Type*} [Fintype R] {K M : Type*} [Fintype K] [DecidableEq K] [Fintype M]
    (l s : K → M → Bool) (x y : K → M → R) (γ : K → M → ℝ) :
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tp : Bool → Bool → R → R → (FinPairs (N + 1) → ℝ) →
        (R → Fin (N + 1) → ℤˣ) → ℝ := fun l s x y g ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if l then (ρ x i : ℝ) - bmean g i else bmean g i) *
        (if s then (ρ y i : ℝ) - bmean g i else bmean g i)) - (if l || s then 0 else q)
    (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, ∑ m, γ k m * Tp (l k m) (s k m) (x k m) (y k m) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      ∑ f : K → M, (∏ k, γ k (f k)) * ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, Tp (l k (f k)) (s k (f k)) (x k (f k)) (y k (f k)) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
  intro E bmean Tp
  have hE : ∀ σ, Measurable fun g : FinPairs (N + 1) → ℝ => E g σ := fun σ => by
    dsimp only [E]
    fun_prop
  have hmono (f : K → M) : Integrable (fun g =>
      ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, Tp (l k (f k)) (s k (f k)) (x k (f k)) (y k (f k)) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)))
      (Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    have hg := sk_live_T_family_meas_bound N β h q (R := R) (K := K) (M := Unit)
      (fun k _ => l k (f k)) (fun k _ => s k (f k))
      (fun k _ => x k (f k)) (fun k _ => y k (f k)) (fun _ _ => 1)
    have hg' :
        (∀ ρ : R → Fin (N + 1) → ℤˣ, Measurable fun g =>
          ∏ k, Tp (l k (f k)) (s k (f k)) (x k (f k)) (y k (f k)) g ρ) ∧
        ∃ B : ℝ, ∀ g (ρ : R → Fin (N + 1) → ℤˣ),
          |∏ k, Tp (l k (f k)) (s k (f k)) (x k (f k)) (y k (f k)) g ρ| ≤ B := by
      simpa only [Fintype.sum_unique, one_mul] using hg
    obtain ⟨hm, B, hB⟩ := hg'
    exact integrable_integral_pi_count_tilted_of_bound E hE _ hm B hB
  have hexp (g : FinPairs (N + 1) → ℝ) (ρ : R → Fin (N + 1) → ℤˣ) :
      (∏ k, ∑ m, γ k m * Tp (l k m) (s k m) (x k m) (y k m) g ρ) =
        ∑ f : K → M, (∏ k, γ k (f k)) *
          ∏ k, Tp (l k (f k)) (s k (f k)) (x k (f k)) (y k (f k)) g ρ := by
    rw [Finset.prod_univ_sum (fun _ => Finset.univ), Fintype.piFinset_univ]
    exact Finset.sum_congr rfl fun _ _ => Finset.prod_mul_distrib
  have hinner (g : FinPairs (N + 1) → ℝ) :
      (∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, ∑ m, γ k m * Tp (l k m) (s k m) (x k m) (y k m) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))) =
      ∑ f : K → M, (∏ k, γ k (f k)) * ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, Tp (l k (f k)) (s k (f k)) (x k (f k)) (y k (f k)) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g)) := by
    simp_rw [hexp]
    rw [integral_finsetSum _ fun _ _ => Integrable.of_finite]
    simp_rw [integral_const_mul]
  simp_rw [hinner]
  rw [integral_finsetSum _ fun f _ => (hmono f).const_mul _]
  simp_rw [integral_const_mul]

/-- **The T-reduction.** A product over factors `k` of finite sums `∑_m γ k m * T(l,s;x,y)` of
T-terms with live replica labels is, up to `O(k+1)`, the sum over monomials `f : K → M` of
`∏ γ` times the Gaussian reference of Proposition 1.10.4 for the monomial. The constant is chosen
before the model parameters and the site count; the factor data are fixed. -/
theorem sk_live_T_expansion_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R : Type*} [Fintype R] [LinearOrder R]
    {K M : Type*} [Fintype K] [DecidableEq K] [Fintype M]
    (l s : K → M → Bool) (x y : K → M → R)
    (hxy : ∀ k m, l k m = true → s k m = true → x k m ≠ y k m) (γ : K → M → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tp : Bool → Bool → R → R → (FinPairs (N + 1) → ℝ) →
        (R → Fin (N + 1) → ℤˣ) → ℝ := fun l s x y g ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if l then (ρ x i : ℝ) - bmean g i else bmean g i) *
        (if s then (ρ y i : ℝ) - bmean g i else bmean g i)) - (if l || s then 0 else q)
    let α : ℝ := (∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4
      ∂gaussianReal 0 1) - 2 * q + 1
    |(∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, ∑ m, γ k m * Tp (l k m) (s k m) (x k m) (y k m) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      ∑ f : K → M, (∏ k, γ k (f k)) *
        ((∏ κ : R × R, ∫ z : ℝ,
          (Real.sqrt (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) * z) ^
            (Finset.univ.filter fun k => (l k (f k) = true ∧ s k (f k) = true) ∧
              (min (x k (f k)) (y k (f k)), max (x k (f k)) (y k (f k))) = κ).card
            ∂gaussianReal 0 1) *
          ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
            ∏ k ∈ Finset.univ.filter (fun k => ¬(l k (f k) = true ∧ s k (f k) = true)),
              Tp (l k (f k)) (s k (f k)) (x k (f k)) (y k (f k)) g ρ
            ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
            ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card K + 1 : ℕ) : ℝ) / 2) := by
  classical
  choose C hC0 hC using fun f : K → M => sk_T_pair_gaussian_moment_uniform β₀ hβ₀ (R := R)
    (J := K) (fun k => l k (f k)) (fun k => s k (f k))
    (fun k => if l k (f k) = true ∧ s k (f k) = true then min (x k (f k)) (y k (f k))
      else x k (f k))
    (fun k => if l k (f k) = true ∧ s k (f k) = true then max (x k (f k)) (y k (f k))
      else y k (f k))
    (fun k hl hs => by
      simp only [hl, hs, and_self, ite_true]
      exact min_lt_max.mpr (hxy k (f k) hl hs)) Finset.univ
  refine ⟨∑ f : K → M, |∏ k, γ k (f k)| * C f + 1, by
    have := Finset.sum_nonneg (fun f (_ : f ∈ (Finset.univ : Finset (K → M))) =>
      mul_nonneg (abs_nonneg (∏ k, γ k (f k))) (hC0 f).le)
    linarith, ?_⟩
  intro β h q hfix hb N E bmean Tp α
  have hmono : ∀ f : K → M, |(∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, Tp (l k (f k)) (s k (f k)) (x k (f k)) (y k (f k)) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
        ((∏ κ : R × R, ∫ z : ℝ,
          (Real.sqrt (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) * z) ^
            (Finset.univ.filter fun k => (l k (f k) = true ∧ s k (f k) = true) ∧
              (min (x k (f k)) (y k (f k)), max (x k (f k)) (y k (f k))) = κ).card
            ∂gaussianReal 0 1) *
          ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
            ∏ k ∈ Finset.univ.filter (fun k => ¬(l k (f k) = true ∧ s k (f k) = true)),
              Tp (l k (f k)) (s k (f k)) (x k (f k)) (y k (f k)) g ρ
            ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
            ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))| ≤
      C f / ((N : ℝ) + 1) ^ (((Fintype.card K + 1 : ℕ) : ℝ) / 2) := fun f => by
    let aa : K → R := fun k =>
      if l k (f k) = true ∧ s k (f k) = true then min (x k (f k)) (y k (f k)) else x k (f k)
    let bb : K → R := fun k =>
      if l k (f k) = true ∧ s k (f k) = true then max (x k (f k)) (y k (f k)) else y k (f k)
    let T' : K → (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ := fun j g ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if l j (f j) then (ρ (aa j) i : ℝ) - bmean g i else bmean g i) *
        (if s j (f j) then (ρ (bb j) i : ℝ) - bmean g i else bmean g i)) -
          (if l j (f j) || s j (f j) then 0 else q)
    have h1 : |(∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, ∏ j ∈ (Finset.univ : Finset K), T' j g ρ
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
        ((∏ κ : R × R, ∫ z : ℝ,
          (Real.sqrt (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) * z) ^
            ((Finset.univ : Finset K).filter fun j =>
              (l j (f j) = true ∧ s j (f j) = true) ∧ (aa j, bb j) = κ).card
            ∂gaussianReal 0 1) *
          ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
            ∏ j ∈ (Finset.univ : Finset K).filter
              (fun j => ¬(l j (f j) = true ∧ s j (f j) = true)), T' j g ρ
            ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
            ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))| ≤
        C f / ((N : ℝ) + 1) ^ ((((Finset.univ : Finset K).card + 1 : ℕ) : ℝ) / 2) :=
      hC f β h q hfix hb N
    have hTeq : ∀ j g ρ, T' j g ρ =
        Tp (l j (f j)) (s j (f j)) (x j (f j)) (y j (f j)) g ρ := fun j g ρ => by
      by_cases hp : l j (f j) = true ∧ s j (f j) = true
      · simp only [T', Tp, aa, bb, hp, and_self, ite_true, Bool.true_or]
        congr 2
        refine Finset.sum_congr rfl fun i _ => ?_
        rcases le_total (x j (f j)) (y j (f j)) with hle | hle
        · simp only [min_eq_left hle, max_eq_right hle]
        · simp only [min_eq_right hle, max_eq_left hle]
          ring
      · simp only [T', Tp, aa, bb, hp, ite_false]
    have hlab : ∀ κ : R × R, ((Finset.univ : Finset K).filter fun j =>
        (l j (f j) = true ∧ s j (f j) = true) ∧ (aa j, bb j) = κ) =
        (Finset.univ : Finset K).filter fun k => (l k (f k) = true ∧ s k (f k) = true) ∧
          (min (x k (f k)) (y k (f k)), max (x k (f k)) (y k (f k))) = κ := fun κ =>
      Finset.filter_congr fun j _ => by
        by_cases hp : l j (f j) = true ∧ s j (f j) = true
        · simp only [aa, bb, hp, and_self, ite_true]
        · simp [hp]
    simp_rw [hTeq, hlab] at h1
    rw [Finset.card_univ] at h1
    exact h1
  have hLHS := sk_live_T_expansion_exact N β h q l s x y γ
  rw [hLHS, ← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  have hd : 0 < ((N : ℝ) + 1) ^ (((Fintype.card K + 1 : ℕ) : ℝ) / 2) := by positivity
  calc _ ≤ ∑ f : K → M, |(∏ k, γ k (f k)) * _| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ f : K → M, |∏ k, γ k (f k)| *
        (C f / ((N : ℝ) + 1) ^ (((Fintype.card K + 1 : ℕ) : ℝ) / 2)) :=
      Finset.sum_le_sum fun f _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hmono f) (abs_nonneg _)
    _ = (∑ f : K → M, |∏ k, γ k (f k)| * C f) /
        ((N : ℝ) + 1) ^ (((Fintype.card K + 1 : ℕ) : ℝ) / 2) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun f _ => by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hd.le

/-- **Dropping pair terms.** If the pair labels of different factors are pairwise distinct, every
monomial containing a pair term has an odd (size one) pair class, so the pair terms of all factors
can be deleted at the cost of `O(k+1)`. -/
theorem sk_live_T_drop_pair_terms_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R : Type*} [Fintype R] [LinearOrder R]
    {K M : Type*} [Fintype K] [DecidableEq K] [Fintype M]
    (l s : K → M → Bool) (x y : K → M → R)
    (hxy : ∀ k m, l k m = true → s k m = true → x k m ≠ y k m) (γ : K → M → ℝ)
    (hinj : ∀ k k' m m', k ≠ k' → (l k m = true ∧ s k m = true) →
      (l k' m' = true ∧ s k' m' = true) → γ k m ≠ 0 → γ k' m' ≠ 0 →
      (min (x k m) (y k m), max (x k m) (y k m)) ≠
        (min (x k' m') (y k' m'), max (x k' m') (y k' m'))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tp : Bool → Bool → R → R → (FinPairs (N + 1) → ℝ) →
        (R → Fin (N + 1) → ℤˣ) → ℝ := fun l s x y g ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if l then (ρ x i : ℝ) - bmean g i else bmean g i) *
        (if s then (ρ y i : ℝ) - bmean g i else bmean g i)) - (if l || s then 0 else q)
    |(∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, ∑ m, γ k m * Tp (l k m) (s k m) (x k m) (y k m) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, ∑ m, (if l k m = true ∧ s k m = true then 0 else γ k m) *
          Tp (l k m) (s k m) (x k m) (y k m) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card K + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := sk_live_T_expansion_uniform β₀ hβ₀ l s x y hxy γ
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro E bmean Tp
  have h1 := hC β h q hfix hb N
  have h2 := sk_live_T_expansion_exact N β h q l s x y
    (fun k m => if l k m = true ∧ s k m = true then 0 else γ k m)
  rw [h2]
  convert h1 using 3
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases hγ : ∀ k, γ k (f k) ≠ 0
  swap
  · push Not at hγ
    obtain ⟨k1, hk1⟩ := hγ
    have hk1' : (if l k1 (f k1) = true ∧ s k1 (f k1) = true then (0 : ℝ) else γ k1 (f k1)) = 0 := by
      by_cases hp : l k1 (f k1) = true ∧ s k1 (f k1) = true
      · simp [hp]
      · simp [hp, hk1]
    have hz1 : (∏ k, if l k (f k) = true ∧ s k (f k) = true then (0 : ℝ) else γ k (f k)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k1) hk1'
    have hz2 : (∏ k, γ k (f k)) = 0 := Finset.prod_eq_zero (Finset.mem_univ k1) hk1
    simp only [hz1, hz2, zero_mul]
  by_cases hpf : ∃ k, l k (f k) = true ∧ s k (f k) = true
  · obtain ⟨k0, hk0⟩ := hpf
    have hz1 : (∏ k, if l k (f k) = true ∧ s k (f k) = true then (0 : ℝ) else γ k (f k)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k0) (by simp [hk0])
    have hcard : ((Finset.univ : Finset K).filter fun k =>
        (l k (f k) = true ∧ s k (f k) = true) ∧
          (min (x k (f k)) (y k (f k)), max (x k (f k)) (y k (f k))) =
          (min (x k0 (f k0)) (y k0 (f k0)), max (x k0 (f k0)) (y k0 (f k0)))) = {k0} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hk, heq⟩
        by_contra hne
        exact hinj k k0 (f k) (f k0) hne hk hk0 (hγ k) (hγ k0) heq
      · rintro rfl
        exact ⟨hk0, rfl⟩
    have hz2 : (∏ κ : R × R, ∫ z : ℝ,
        (Real.sqrt ((∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4 ∂gaussianReal 0 1 -
          2 * q + 1) / (1 - β ^ 2 * (∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4
            ∂gaussianReal 0 1 - 2 * q + 1)) / (N + 1 : ℝ)) * z) ^
          ((Finset.univ : Finset K).filter fun k =>
            (l k (f k) = true ∧ s k (f k) = true) ∧
              (min (x k (f k)) (y k (f k)), max (x k (f k)) (y k (f k))) = κ).card
          ∂gaussianReal 0 1) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ
        (min (x k0 (f k0)) (y k0 (f k0)), max (x k0 (f k0)) (y k0 (f k0)))) ?_
      rw [hcard, Finset.card_singleton]
      exact integral_pow_scaled_gaussianReal_of_odd _ odd_one
    simp only [hz1, hz2, zero_mul, mul_zero]
  · push Not at hpf
    have hz1 : (∏ k, if l k (f k) = true ∧ s k (f k) = true then (0 : ℝ) else γ k (f k)) =
        ∏ k, γ k (f k) :=
      Finset.prod_congr rfl fun k _ =>
        ite_eq_right_iff.mpr fun hk => (hpf k hk.1 hk.2).elim
    have hz2 : ∀ κ : R × R, ((Finset.univ : Finset K).filter fun k =>
        (l k (f k) = true ∧ s k (f k) = true) ∧
          (min (x k (f k)) (y k (f k)), max (x k (f k)) (y k (f k))) = κ) = ∅ := fun κ => by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨hk, -⟩
      exact hpf k hk.1 hk.2
    have hz3 : ((Finset.univ : Finset K).filter fun k =>
        ¬(l k (f k) = true ∧ s k (f k) = true)) = Finset.univ :=
      Finset.filter_true_of_mem fun k _ h => hpf k h.1 h.2
    simp only [hz1, hz2, hz3, Finset.card_empty, pow_zero, integral_const, probReal_univ,
      smul_eq_mul, mul_one, Finset.prod_const_one, one_mul]

/-- **A squared pair factor.** Let `T(1,1;u,v)²` multiply a product over factors whose pair labels
are pairwise distinct and different from `{u,v}`. Then, up to `O(k+1)`, the pair terms of the
other factors can be dropped and the square contributes the Gaussian second moment
`α/(1-β²α)/(N+1)` of Proposition 1.10.4. -/
theorem sk_live_T_square_factor_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R : Type*} [Fintype R] [LinearOrder R]
    {K M : Type*} [Fintype K] [DecidableEq K] [Fintype M] [DecidableEq M] [Nonempty M]
    (l s : K → M → Bool) (x y : K → M → R)
    (hxy : ∀ k m, l k m = true → s k m = true → x k m ≠ y k m) (γ : K → M → ℝ)
    (u v : R) (huv : u < v)
    (hinj : ∀ k k' m m', k ≠ k' → (l k m = true ∧ s k m = true) →
      (l k' m' = true ∧ s k' m' = true) → γ k m ≠ 0 → γ k' m' ≠ 0 →
      (min (x k m) (y k m), max (x k m) (y k m)) ≠
        (min (x k' m') (y k' m'), max (x k' m') (y k' m')))
    (hdup : ∀ k m, (l k m = true ∧ s k m = true) → γ k m ≠ 0 →
      (min (x k m) (y k m), max (x k m) (y k m)) ≠ (u, v)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tp : Bool → Bool → R → R → (FinPairs (N + 1) → ℝ) →
        (R → Fin (N + 1) → ℤˣ) → ℝ := fun l s x y g ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if l then (ρ x i : ℝ) - bmean g i else bmean g i) *
        (if s then (ρ y i : ℝ) - bmean g i else bmean g i)) - (if l || s then 0 else q)
    let α : ℝ := (∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4
      ∂gaussianReal 0 1) - 2 * q + 1
    |(∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        Tp true true u v g ρ * Tp true true u v g ρ *
          ∏ k, ∑ m, γ k m * Tp (l k m) (s k m) (x k m) (y k m) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      α / (1 - β ^ 2 * α) / (N + 1 : ℝ) *
      (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, ∑ m, (if l k m = true ∧ s k m = true then 0 else γ k m) *
          Tp (l k m) (s k m) (x k m) (y k m) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card K + 2 + 1 : ℕ) : ℝ) / 2) := by
  classical
  obtain ⟨m₀⟩ := (inferInstance : Nonempty M)
  let l' : Bool ⊕ K → M → Bool := fun k' m => Sum.elim (fun _ => true) (fun k => l k m) k'
  let s' : Bool ⊕ K → M → Bool := fun k' m => Sum.elim (fun _ => true) (fun k => s k m) k'
  let x' : Bool ⊕ K → M → R := fun k' m => Sum.elim (fun _ => u) (fun k => x k m) k'
  let y' : Bool ⊕ K → M → R := fun k' m => Sum.elim (fun _ => v) (fun k => y k m) k'
  let γ' : Bool ⊕ K → M → ℝ := fun k' m =>
    Sum.elim (fun _ => if m = m₀ then 1 else 0) (fun k => γ k m) k'
  have hxy' : ∀ k m, l' k m = true → s' k m = true → x' k m ≠ y' k m := fun k' m => by
    cases k' with
    | inl b => intro _ _; exact huv.ne
    | inr k => exact hxy k m
  obtain ⟨C, hC0, hC⟩ := sk_live_T_expansion_uniform β₀ hβ₀ l' s' x' y' hxy' γ'
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro E bmean Tp α
  have h1 : |(∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k', ∑ m, γ' k' m * Tp (l' k' m) (s' k' m) (x' k' m) (y' k' m) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      ∑ f : Bool ⊕ K → M, (∏ k', γ' k' (f k')) *
        ((∏ κ : R × R, ∫ z : ℝ,
          (Real.sqrt (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) * z) ^
            (Finset.univ.filter fun k' => (l' k' (f k') = true ∧ s' k' (f k') = true) ∧
              (min (x' k' (f k')) (y' k' (f k')), max (x' k' (f k')) (y' k' (f k'))) = κ).card
            ∂gaussianReal 0 1) *
          ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
            ∏ k' ∈ Finset.univ.filter
                (fun k' => ¬(l' k' (f k') = true ∧ s' k' (f k') = true)),
              Tp (l' k' (f k')) (s' k' (f k')) (x' k' (f k')) (y' k' (f k')) g ρ
            ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
            ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card (Bool ⊕ K) + 1 : ℕ) : ℝ) / 2) :=
    hC β h q hfix hb N
  have hcard : Fintype.card (Bool ⊕ K) = Fintype.card K + 2 := by
    rw [Fintype.card_sum, Fintype.card_bool]; ring
  rw [hcard] at h1
  have hpt : ∀ g ρ, ∏ k', ∑ m, γ' k' m *
      Tp (l' k' m) (s' k' m) (x' k' m) (y' k' m) g ρ =
      Tp true true u v g ρ * Tp true true u v g ρ *
        ∏ k, ∑ m, γ k m * Tp (l k m) (s k m) (x k m) (y k m) g ρ := fun g ρ => by
    rw [Fintype.prod_sum_type]
    simp only [γ', l', s', x', y', Sum.elim_inl, Sum.elim_inr, Fintype.prod_bool, ite_mul,
      one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp_rw [hpt] at h1
  have hexx : (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, ∑ m, (if l k m = true ∧ s k m = true then 0 else γ k m) *
          Tp (l k m) (s k m) (x k m) (y k m) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      ∑ f : K → M, (∏ k, if l k (f k) = true ∧ s k (f k) = true then 0 else γ k (f k)) *
        ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
          ∏ k, Tp (l k (f k)) (s k (f k)) (x k (f k)) (y k (f k)) g ρ
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
          ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
    sk_live_T_expansion_exact N β h q l s x y
      (fun k m => if l k m = true ∧ s k m = true then 0 else γ k m)
  rw [hexx]
  convert h1 using 3
  have hα01 := tanh_fourth_sub_two_mul_add_one_mem_Icc_of_fixedPoint hfix
  have hden : 0 < 1 - β ^ 2 * α := by
    have h2 : β ^ 2 * α ≤ β ^ 2 * 1 := mul_le_mul_of_nonneg_left hα01.2 (sq_nonneg _)
    linarith only [h2, hb, hβ₀]
  have hc0 : 0 ≤ α / (1 - β ^ 2 * α) / (N + 1 : ℝ) :=
    div_nonneg (div_nonneg hα01.1 hden.le) (by positivity)
  have hsq : ∫ z : ℝ, (Real.sqrt (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) * z) ^ 2 ∂gaussianReal 0 1 =
      α / (1 - β ^ 2 * α) / (N + 1 : ℝ) := by
    have := integral_pow_add_two_scaled_gaussianReal
      (Real.sqrt (α / (1 - β ^ 2 * α) / (N + 1 : ℝ))) 0
    simp only [zero_add, pow_zero, integral_const, probReal_univ, smul_eq_mul, mul_one,
      Nat.cast_zero] at this
    rw [this, Real.sq_sqrt hc0]
    ring
  have hsumF : ∀ F : (Bool ⊕ K → M) → ℝ, ∑ f, F f = ∑ fb : Bool → M, ∑ fr : K → M,
      F (Sum.elim fb fr) := fun F => by
    rw [← (Equiv.sumArrowEquivProdArrow Bool K M).symm.sum_comp F, Fintype.sum_prod_type]
    rfl
  rw [hsumF]
  rw [Finset.sum_eq_single (fun _ : Bool => m₀)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun fr _ => ?_
    have hprod : (∏ k', γ' k' (Sum.elim (fun _ => m₀) fr k')) = ∏ k, γ k (fr k) := by
      rw [Fintype.prod_sum_type]
      simp [γ']
    have hpairs : ∀ κ : R × R, ((Finset.univ : Finset (Bool ⊕ K)).filter fun k' =>
        (l' k' (Sum.elim (fun _ => m₀) fr k') = true ∧
          s' k' (Sum.elim (fun _ => m₀) fr k') = true) ∧
        (min (x' k' (Sum.elim (fun _ => m₀) fr k')) (y' k' (Sum.elim (fun _ => m₀) fr k')),
          max (x' k' (Sum.elim (fun _ => m₀) fr k')) (y' k' (Sum.elim (fun _ => m₀) fr k'))) =
          κ).card = (if κ = (u, v) then 2 else 0) +
        ((Finset.univ : Finset K).filter fun k => (l k (fr k) = true ∧ s k (fr k) = true) ∧
          (min (x k (fr k)) (y k (fr k)), max (x k (fr k)) (y k (fr k))) = κ).card :=
      fun κ => by
      rw [Finset.card_filter, Fintype.sum_sum_type, Finset.card_filter]
      congr 1
      simp only [l', s', x', y', Sum.elim_inl, min_eq_left huv.le,
        max_eq_right huv.le, and_self, true_and, Finset.sum_const, Finset.card_univ,
        Fintype.card_bool, smul_eq_mul]
      by_cases hκ : (u, v) = κ
      · simp [hκ]
      · simp [hκ, Ne.symm hκ]
    rw [hprod]
    simp_rw [hpairs]
    by_cases hγ : ∀ k, γ k (fr k) ≠ 0
    swap
    · push Not at hγ
      obtain ⟨k1, hk1⟩ := hγ
      have hk1' : (if l k1 (fr k1) = true ∧ s k1 (fr k1) = true then (0 : ℝ)
          else γ k1 (fr k1)) = 0 := by
        by_cases hp : l k1 (fr k1) = true ∧ s k1 (fr k1) = true
        · simp [hp]
        · simp [hp, hk1]
      have hz1 : (∏ k, if l k (fr k) = true ∧ s k (fr k) = true then (0 : ℝ) else γ k (fr k)) =
          0 := Finset.prod_eq_zero (Finset.mem_univ k1) hk1'
      have hz2 : (∏ k, γ k (fr k)) = 0 := Finset.prod_eq_zero (Finset.mem_univ k1) hk1
      simp only [hz1, hz2, zero_mul, mul_zero]
    by_cases hp : ∃ k, l k (fr k) = true ∧ s k (fr k) = true
    · obtain ⟨k0, hk0⟩ := hp
      have hz1 : (∏ k, if l k (fr k) = true ∧ s k (fr k) = true then (0 : ℝ) else γ k (fr k)) =
          0 := Finset.prod_eq_zero (Finset.mem_univ k0) (by simp [hk0])
      have hcard : ((Finset.univ : Finset K).filter fun k =>
          (l k (fr k) = true ∧ s k (fr k) = true) ∧
            (min (x k (fr k)) (y k (fr k)), max (x k (fr k)) (y k (fr k))) =
            (min (x k0 (fr k0)) (y k0 (fr k0)), max (x k0 (fr k0)) (y k0 (fr k0)))) = {k0} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨hk, heq⟩
          by_contra hne
          exact hinj k k0 (fr k) (fr k0) hne hk hk0 (hγ k) (hγ k0) heq
        · rintro rfl
          exact ⟨hk0, rfl⟩
      have hz2 : (∏ κ : R × R, ∫ z : ℝ, (Real.sqrt (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) * z) ^
          ((if κ = (u, v) then 2 else 0) + ((Finset.univ : Finset K).filter fun k =>
            (l k (fr k) = true ∧ s k (fr k) = true) ∧
            (min (x k (fr k)) (y k (fr k)), max (x k (fr k)) (y k (fr k))) = κ).card)
          ∂gaussianReal 0 1) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ
          (min (x k0 (fr k0)) (y k0 (fr k0)), max (x k0 (fr k0)) (y k0 (fr k0)))) ?_
        rw [hcard, Finset.card_singleton]
        have hne := hdup k0 (fr k0) hk0 (hγ k0)
        simp only [hne, ite_false, zero_add]
        exact integral_pow_scaled_gaussianReal_of_odd _ odd_one
      simp only [hz1, hz2, zero_mul, mul_zero]
    · push Not at hp
      have hz1 : (∏ k, if l k (fr k) = true ∧ s k (fr k) = true then (0 : ℝ) else γ k (fr k)) =
          ∏ k, γ k (fr k) :=
        Finset.prod_congr rfl fun k _ => ite_eq_right_iff.mpr fun hk => (hp k hk.1 hk.2).elim
      have hz2 : ∀ κ : R × R, ((Finset.univ : Finset K).filter fun k =>
          (l k (fr k) = true ∧ s k (fr k) = true) ∧
            (min (x k (fr k)) (y k (fr k)), max (x k (fr k)) (y k (fr k))) = κ) = ∅ :=
        fun κ => by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rintro ⟨hk, -⟩
        exact hp k hk.1 hk.2
      simp_rw [hz2, Finset.card_empty, add_zero]
      have hG : (∏ κ : R × R, ∫ z : ℝ, (Real.sqrt (α / (1 - β ^ 2 * α) / (N + 1 : ℝ)) * z) ^
          (if κ = (u, v) then 2 else 0) ∂gaussianReal 0 1) =
          α / (1 - β ^ 2 * α) / (N + 1 : ℝ) := by
        rw [Finset.prod_eq_single (u, v)]
        · simpa using hsq
        · intro κ _ hκ
          simp [hκ]
        · intro hcon
          exact absurd (Finset.mem_univ _) hcon
      rw [hG, hz1]
      have hν : ∀ g ρ, (∏ k' ∈ (Finset.univ : Finset (Bool ⊕ K)).filter (fun k' =>
          ¬(l' k' (Sum.elim (fun _ => m₀) fr k') = true ∧
            s' k' (Sum.elim (fun _ => m₀) fr k') = true)),
          Tp (l' k' (Sum.elim (fun _ => m₀) fr k')) (s' k' (Sum.elim (fun _ => m₀) fr k'))
            (x' k' (Sum.elim (fun _ => m₀) fr k')) (y' k' (Sum.elim (fun _ => m₀) fr k')) g ρ) =
          ∏ k, Tp (l k (fr k)) (s k (fr k)) (x k (fr k)) (y k (fr k)) g ρ := fun g ρ => by
        rw [Finset.prod_filter, Fintype.prod_sum_type]
        simp only [l', s', x', y', Sum.elim_inl, Sum.elim_inr, and_self, not_true_eq_false,
          ite_false, Finset.prod_const_one, one_mul]
        refine Finset.prod_congr rfl fun k _ => ?_
        have : ¬(l k (fr k) = true ∧ s k (fr k) = true) := fun hh => hp k hh.1 hh.2
        simp [this]
      simp_rw [hν]
      ring
  · intro fb _ hfb
    refine Finset.sum_eq_zero fun fr _ => ?_
    have : (∏ k', γ' k' ((Sum.elim fb fr : Bool ⊕ K → M) k')) = 0 := by
      rw [Fintype.prod_sum_type]
      have hb0 : ∃ b, fb b ≠ m₀ := by
        by_contra hcon
        push Not at hcon
        exact hfb (funext hcon)
      obtain ⟨b0, hb0⟩ := hb0
      have : (∏ b : Bool, γ' (Sum.inl b) ((Sum.elim fb fr : Bool ⊕ K → M) (Sum.inl b))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ b0) (by simp [γ', hb0])
      rw [this, zero_mul]
    rw [this, zero_mul]
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

/-- **A product with a pair-only factor is of lower order.** If one factor consists only of pair
terms (nonzero coefficients only for pair terms) and the pair labels of different factors are
distinct, the whole average is `O(k+1)`. -/
theorem sk_live_T_pair_only_factor_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R : Type*} [Fintype R] [LinearOrder R]
    {K M : Type*} [Fintype K] [DecidableEq K] [Fintype M]
    (l s : K → M → Bool) (x y : K → M → R)
    (hxy : ∀ k m, l k m = true → s k m = true → x k m ≠ y k m) (γ : K → M → ℝ)
    (hinj : ∀ k k' m m', k ≠ k' → (l k m = true ∧ s k m = true) →
      (l k' m' = true ∧ s k' m' = true) → γ k m ≠ 0 → γ k' m' ≠ 0 →
      (min (x k m) (y k m), max (x k m) (y k m)) ≠
        (min (x k' m') (y k' m'), max (x k' m') (y k' m')))
    (k0 : K) (hk0 : ∀ m, γ k0 m ≠ 0 → l k0 m = true ∧ s k0 m = true) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tp : Bool → Bool → R → R → (FinPairs (N + 1) → ℝ) →
        (R → Fin (N + 1) → ℤˣ) → ℝ := fun l s x y g ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if l then (ρ x i : ℝ) - bmean g i else bmean g i) *
        (if s then (ρ y i : ℝ) - bmean g i else bmean g i)) - (if l || s then 0 else q)
    |∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, ∑ m, γ k m * Tp (l k m) (s k m) (x k m) (y k m) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card K + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := sk_live_T_drop_pair_terms_uniform β₀ hβ₀ l s x y hxy γ hinj
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro E bmean Tp
  have h1 : |(∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, ∑ m, γ k m * Tp (l k m) (s k m) (x k m) (y k m) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, ∑ m, (if l k m = true ∧ s k m = true then 0 else γ k m) *
          Tp (l k m) (s k m) (x k m) (y k m) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card K + 1 : ℕ) : ℝ) / 2) := hC β h q hfix hb N
  have hz : (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, ∑ m, (if l k m = true ∧ s k m = true then 0 else γ k m) *
          Tp (l k m) (s k m) (x k m) (y k m) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) = 0 := by
    have : ∀ g (ρ : R → Fin (N + 1) → ℤˣ), (∏ k, ∑ m, (if l k m = true ∧ s k m = true then 0
        else γ k m) * Tp (l k m) (s k m) (x k m) (y k m) g ρ) = 0 := fun g ρ => by
      refine Finset.prod_eq_zero (Finset.mem_univ k0) (Finset.sum_eq_zero fun m _ => ?_)
      by_cases hp : l k0 m = true ∧ s k0 m = true
      · simp [hp]
      · have : γ k0 m = 0 := by
          by_contra hne
          exact hp (hk0 m hne)
        simp [this]
    have hz2 : ∀ g, (∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, ∑ m, (if l k m = true ∧ s k m = true then 0 else γ k m) *
          Tp (l k m) (s k m) (x k m) (y k m) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))) = 0 := fun g => by
      simp_rw [this g]
      simp
    simp_rw [hz2]
    simp
  rw [hz, sub_zero] at h1
  exact h1

/-- **Pointwise T-expansion of an overlap.** For every real vector `b` (the Gibbs mean in the
applications) the centered overlap of two replicas is the sum of the four `T`-factors with all
flag choices (Talagrand, Eq. (1.246)). -/
theorem sum_flag_T_factor_eq_overlap {R : Type*} (N : ℕ) (q : ℝ) (b : Fin (N + 1) → ℝ)
    (ρ : R → Fin (N + 1) → ℤˣ) (x y : R) :
    (∑ ls : Bool × Bool, (((N + 1 : ℝ)⁻¹ * ∑ i,
        (if ls.1 then (ρ x i : ℝ) - b i else b i) *
        (if ls.2 then (ρ y i : ℝ) - b i else b i)) - (if ls.1 || ls.2 then 0 else q))) =
      (N + 1 : ℝ)⁻¹ * ∑ i, (ρ x i : ℝ) * (ρ y i : ℝ) - q := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false,
    Bool.true_or, Bool.false_or, Bool.or_self, sub_zero]
  have : ∀ i : Fin (N + 1), ((ρ x i : ℝ) - b i) * ((ρ y i : ℝ) - b i) +
      ((ρ x i : ℝ) - b i) * b i + (b i * ((ρ y i : ℝ) - b i) + b i * b i) =
      (ρ x i : ℝ) * (ρ y i : ℝ) := fun i => by ring
  have hsum : (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - b i) * ((ρ y i : ℝ) - b i) +
      (N + 1 : ℝ)⁻¹ * ∑ i, ((ρ x i : ℝ) - b i) * b i +
      ((N + 1 : ℝ)⁻¹ * ∑ i, b i * ((ρ y i : ℝ) - b i) + (N + 1 : ℝ)⁻¹ * ∑ i, b i * b i) =
      (N + 1 : ℝ)⁻¹ * ∑ i, (ρ x i : ℝ) * (ρ y i : ℝ) := by
    rw [← mul_add, ← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    congr 2
    funext i
    exact this i
  linarith only [hsum]

/-- **The increment in pair form.** For signs `sg₁(i₁) sg₂(i₂)` with `∑ sg = 0` on each factor,
the combination of centered overlaps `∑ sg₁ sg₂ (R_{X i₁,Y i₂} - q)` equals the corresponding
combination of pair `T`-factors `T(1,1;X i₁,Y i₂)`: all single and global terms cancel. -/
theorem sum_sign_overlap_eq_pair_T {R : Type*} (N : ℕ) (q : ℝ) (b : Fin (N + 1) → ℝ)
    (ρ : R → Fin (N + 1) → ℤˣ) (X Y : Bool → R) :
    (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
      ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (X i.1) v : ℝ) * (ρ (Y i.2) v : ℝ) - q)) =
    ∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
      (((N + 1 : ℝ)⁻¹ * ∑ v, ((ρ (X i.1) v : ℝ) - b v) * ((ρ (Y i.2) v : ℝ) - b v))) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  have hv : ∀ v : Fin (N + 1), ∀ x y : R, (ρ x v : ℝ) * (ρ y v : ℝ) =
      ((ρ x v : ℝ) - b v) * ((ρ y v : ℝ) - b v) + ((ρ x v : ℝ) - b v) * b v +
        (b v * ((ρ y v : ℝ) - b v) + b v * b v) := fun v x y => by ring
  have hsum : ∀ x y : R, (N + 1 : ℝ)⁻¹ * ∑ v, (ρ x v : ℝ) * (ρ y v : ℝ) =
      (N + 1 : ℝ)⁻¹ * ∑ v, ((ρ x v : ℝ) - b v) * ((ρ y v : ℝ) - b v) +
      (N + 1 : ℝ)⁻¹ * ∑ v, ((ρ x v : ℝ) - b v) * b v +
      ((N + 1 : ℝ)⁻¹ * ∑ v, b v * ((ρ y v : ℝ) - b v) + (N + 1 : ℝ)⁻¹ * ∑ v, b v * b v) :=
    fun x y => by
    rw [← mul_add, ← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    congr 2
    funext v
    exact hv v x y
  simp only [hsum]
  ring

/-- **Increment against a product, all pair labels distinct.** The increment
`∑ sg₁ sg₂ (R_{X i₁,Y i₂} - q)` multiplying a product of overlap polynomials
`∑_i c_{b,i} (R_{A b i,B b i} - q)` has average `O(k+1)` when no pair label of the increment
equals a pair label of a factor and the pair labels of different factors are distinct. -/
theorem sk_live_inc_unmatched_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R : Type*} [Fintype R] [LinearOrder R] {B : Type*} [Fintype B] [DecidableEq B]
    (c : B → Bool × Bool → ℝ) (A Bb : B → Bool × Bool → R) (X Y : Bool → R)
    (hAB : ∀ b i, A b i ≠ Bb b i) (hXY : ∀ i₁ i₂, X i₁ ≠ Y i₂)
    (hrest : ∀ b b' i i', b ≠ b' → c b i ≠ 0 → c b' i' ≠ 0 →
      (min (A b i) (Bb b i), max (A b i) (Bb b i)) ≠
        (min (A b' i') (Bb b' i'), max (A b' i') (Bb b' i')))
    (hinc : ∀ i₁ i₂ b i, c b i ≠ 0 →
      (min (X i₁) (Y i₂), max (X i₁) (Y i₂)) ≠ (min (A b i) (Bb b i), max (A b i) (Bb b i))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    |∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (X i.1) v : ℝ) * (ρ (Y i.2) v : ℝ) - q)) *
        ∏ b, ∑ i, c b i * ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (A b i) v : ℝ) * (ρ (Bb b i) v : ℝ) - q)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card B + 2 : ℕ) : ℝ) / 2) := by
  let sg : Bool × Bool → ℝ := fun i => (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1)
  let γ : Option B → (Bool × Bool) × (Bool × Bool) → ℝ := fun k m =>
    Option.elim k (if m.2 = (true, true) then sg m.1 else 0) (fun b => c b m.1)
  let l : Option B → (Bool × Bool) × (Bool × Bool) → Bool := fun _ m => m.2.1
  let s : Option B → (Bool × Bool) × (Bool × Bool) → Bool := fun _ m => m.2.2
  let x : Option B → (Bool × Bool) × (Bool × Bool) → R := fun k m =>
    Option.elim k (X m.1.1) (fun b => A b m.1)
  let y : Option B → (Bool × Bool) × (Bool × Bool) → R := fun k m =>
    Option.elim k (Y m.1.2) (fun b => Bb b m.1)
  have hxy : ∀ k m, l k m = true → s k m = true → x k m ≠ y k m := fun k m _ _ => by
    cases k with
    | none => exact hXY _ _
    | some b => exact hAB b m.1
  have hinj : ∀ k k' m m', k ≠ k' → (l k m = true ∧ s k m = true) →
      (l k' m' = true ∧ s k' m' = true) → γ k m ≠ 0 → γ k' m' ≠ 0 →
      (min (x k m) (y k m), max (x k m) (y k m)) ≠
        (min (x k' m') (y k' m'), max (x k' m') (y k' m')) := by
    intro k k' m m' hkk _ _ hγ hγ'
    cases k with
    | none =>
      cases k' with
      | none => exact absurd rfl hkk
      | some b' => exact hinc _ _ b' m'.1 hγ'
    | some b =>
      cases k' with
      | none => exact (hinc _ _ b m.1 hγ).symm
      | some b' => exact hrest b b' m.1 m'.1 (fun h => hkk (by rw [h])) hγ hγ'
  have hk0 : ∀ m, γ none m ≠ 0 → l none m = true ∧ s none m = true := fun m hm => by
    by_cases hls : m.2 = (true, true)
    · exact ⟨by rw [show l none m = m.2.1 from rfl, hls],
        by rw [show s none m = m.2.2 from rfl, hls]⟩
    · exact absurd (by simp [γ, hls]) hm
  obtain ⟨C, hC0, hC⟩ := sk_live_T_pair_only_factor_uniform β₀ hβ₀ l s x y hxy γ hinj none hk0
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro E
  let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
    ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
  let Tp : Bool → Bool → R → R → (FinPairs (N + 1) → ℝ) →
      (R → Fin (N + 1) → ℤˣ) → ℝ := fun l s x y g ρ =>
    ((N + 1 : ℝ)⁻¹ * ∑ i,
      (if l then (ρ x i : ℝ) - bmean g i else bmean g i) *
      (if s then (ρ y i : ℝ) - bmean g i else bmean g i)) - (if l || s then 0 else q)
  have h1 : |∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, ∑ m, γ k m * Tp (l k m) (s k m) (x k m) (y k m) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card (Option B) + 1 : ℕ) : ℝ) / 2) :=
    hC β h q hfix hb N
  have hpt : ∀ g (ρ : R → Fin (N + 1) → ℤˣ), (∏ k, ∑ m, γ k m *
      Tp (l k m) (s k m) (x k m) (y k m) g ρ) =
      (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (X i.1) v : ℝ) * (ρ (Y i.2) v : ℝ) - q)) *
        ∏ b, ∑ i, c b i * ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (A b i) v : ℝ) * (ρ (Bb b i) v : ℝ) - q) :=
    fun g ρ => by
    rw [Fintype.prod_option]
    congr 1
    · rw [sum_sign_overlap_eq_pair_T N q (bmean g) ρ X Y, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [γ, l, s, x, y, Option.elim, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, sg]
      simp only [Tp, Bool.or_self, ite_true, sub_zero]
    · refine Finset.prod_congr rfl fun b _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [γ, l, s, x, y, Option.elim]
      rw [← Finset.mul_sum]
      congr 1
      rw [← sum_flag_T_factor_eq_overlap N q (bmean g) ρ (A b i) (Bb b i)]
  simp_rw [hpt] at h1
  rw [Fintype.card_option] at h1
  exact h1

/-- **Pair-only spec factor (uniform shape).** Factors are `T`-sums `∑_{(i,ls)} γ k (i,ls)
T(ls; x k i, y k i)`. If one factor is pair-only and the pair labels of different factors with
nonzero coefficients are distinct, the average is `O(k+1)`. -/
theorem sk_live_sp_pair_only_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R : Type*} [Fintype R] [LinearOrder R] {K : Type*} [Fintype K] [DecidableEq K]
    (γ : K → (Bool × Bool) × (Bool × Bool) → ℝ) (x y : K → Bool × Bool → R)
    (hxy : ∀ k i, x k i ≠ y k i)
    (hinj : ∀ k k' m m', k ≠ k' → m.2 = (true, true) → m'.2 = (true, true) →
      γ k m ≠ 0 → γ k' m' ≠ 0 →
      (min (x k m.1) (y k m.1), max (x k m.1) (y k m.1)) ≠
        (min (x k' m'.1) (y k' m'.1), max (x k' m'.1) (y k' m'.1)))
    (k0 : K) (hk0 : ∀ m, γ k0 m ≠ 0 → m.2 = (true, true)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tp : Bool → Bool → R → R → (FinPairs (N + 1) → ℝ) →
        (R → Fin (N + 1) → ℤˣ) → ℝ := fun l s x y g ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if l then (ρ x i : ℝ) - bmean g i else bmean g i) *
        (if s then (ρ y i : ℝ) - bmean g i else bmean g i)) - (if l || s then 0 else q)
    |∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, ∑ m, γ k m * Tp m.2.1 m.2.2 (x k m.1) (y k m.1) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card K + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := sk_live_T_pair_only_factor_uniform β₀ hβ₀
    (fun _ m => m.2.1) (fun _ m => m.2.2) (fun k m => x k m.1) (fun k m => y k m.1)
    (fun k m _ _ => hxy k m.1) γ
    (fun k k' m m' hkk hm hm' h1 h2 => hinj k k' m m' hkk
      (Prod.ext hm.1 hm.2) (Prod.ext hm'.1 hm'.2) h1 h2)
    k0 (fun m hm => by
      have := hk0 m hm
      exact ⟨by rw [this], by rw [this]⟩)
  exact ⟨C, hC0, hC⟩

/-- **Dropping pair terms (uniform shape).** -/
theorem sk_live_sp_drop_pair_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R : Type*} [Fintype R] [LinearOrder R] {K : Type*} [Fintype K] [DecidableEq K]
    (γ : K → (Bool × Bool) × (Bool × Bool) → ℝ) (x y : K → Bool × Bool → R)
    (hxy : ∀ k i, x k i ≠ y k i)
    (hinj : ∀ k k' m m', k ≠ k' → m.2 = (true, true) → m'.2 = (true, true) →
      γ k m ≠ 0 → γ k' m' ≠ 0 →
      (min (x k m.1) (y k m.1), max (x k m.1) (y k m.1)) ≠
        (min (x k' m'.1) (y k' m'.1), max (x k' m'.1) (y k' m'.1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tp : Bool → Bool → R → R → (FinPairs (N + 1) → ℝ) →
        (R → Fin (N + 1) → ℤˣ) → ℝ := fun l s x y g ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if l then (ρ x i : ℝ) - bmean g i else bmean g i) *
        (if s then (ρ y i : ℝ) - bmean g i else bmean g i)) - (if l || s then 0 else q)
    |(∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, ∑ m, γ k m * Tp m.2.1 m.2.2 (x k m.1) (y k m.1) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, ∑ m, (if m.2.1 = true ∧ m.2.2 = true then 0 else γ k m) *
          Tp m.2.1 m.2.2 (x k m.1) (y k m.1) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card K + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := sk_live_T_drop_pair_terms_uniform β₀ hβ₀
    (fun _ m => m.2.1) (fun _ m => m.2.2) (fun k m => x k m.1) (fun k m => y k m.1)
    (fun k m _ _ => hxy k m.1) γ
    (fun k k' m m' hkk hm hm' h1 h2 => hinj k k' m m' hkk
      (Prod.ext hm.1 hm.2) (Prod.ext hm'.1 hm'.2) h1 h2)
  exact ⟨C, hC0, hC⟩

/-- **Squared pair factor (uniform shape).** -/
theorem sk_live_sp_square_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R : Type*} [Fintype R] [LinearOrder R] {K : Type*} [Fintype K] [DecidableEq K]
    (γ : K → (Bool × Bool) × (Bool × Bool) → ℝ) (x y : K → Bool × Bool → R)
    (hxy : ∀ k i, x k i ≠ y k i)
    (hinj : ∀ k k' m m', k ≠ k' → m.2 = (true, true) → m'.2 = (true, true) →
      γ k m ≠ 0 → γ k' m' ≠ 0 →
      (min (x k m.1) (y k m.1), max (x k m.1) (y k m.1)) ≠
        (min (x k' m'.1) (y k' m'.1), max (x k' m'.1) (y k' m'.1)))
    (u v : R) (huv : u < v)
    (hdup : ∀ k m, m.2 = (true, true) → γ k m ≠ 0 →
      (min (x k m.1) (y k m.1), max (x k m.1) (y k m.1)) ≠ (u, v)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tp : Bool → Bool → R → R → (FinPairs (N + 1) → ℝ) →
        (R → Fin (N + 1) → ℤˣ) → ℝ := fun l s x y g ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if l then (ρ x i : ℝ) - bmean g i else bmean g i) *
        (if s then (ρ y i : ℝ) - bmean g i else bmean g i)) - (if l || s then 0 else q)
    let α : ℝ := (∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4
      ∂gaussianReal 0 1) - 2 * q + 1
    |(∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        Tp true true u v g ρ * Tp true true u v g ρ *
          ∏ k, ∑ m, γ k m * Tp m.2.1 m.2.2 (x k m.1) (y k m.1) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      α / (1 - β ^ 2 * α) / (N + 1 : ℝ) *
      (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k, ∑ m, (if m.2.1 = true ∧ m.2.2 = true then 0 else γ k m) *
          Tp m.2.1 m.2.2 (x k m.1) (y k m.1) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card K + 2 + 1 : ℕ) : ℝ) / 2) := by
  obtain ⟨C, hC0, hC⟩ := sk_live_T_square_factor_uniform β₀ hβ₀
    (fun _ m => m.2.1) (fun _ m => m.2.2) (fun k m => x k m.1) (fun k m => y k m.1)
    (fun k m _ _ => hxy k m.1) γ u v huv
    (fun k k' m m' hkk hm hm' h1 h2 => hinj k k' m m' hkk
      (Prod.ext hm.1 hm.2) (Prod.ext hm'.1 hm'.2) h1 h2)
    (fun k m hm h1 => hdup k m (Prod.ext hm.1 hm.2) h1)
  exact ⟨C, hC0, hC⟩

/-- **A centered overlap polynomial as a sum of `T`-terms.** For every real vector `b`,
`∑_i c i (R_{A i,B i} - q)` is the `T`-sum with coefficient `c i` on all four flag choices. -/
theorem sum_spec_eq_overlap_poly {R : Type*} (N : ℕ) (q : ℝ) (b : Fin (N + 1) → ℝ)
    (ρ : R → Fin (N + 1) → ℤˣ) (c : Bool × Bool → ℝ) (A B : Bool × Bool → R) :
    (∑ m : (Bool × Bool) × (Bool × Bool), c m.1 *
      (((N + 1 : ℝ)⁻¹ * ∑ i,
        (if m.2.1 then (ρ (A m.1) i : ℝ) - b i else b i) *
        (if m.2.2 then (ρ (B m.1) i : ℝ) - b i else b i)) - (if m.2.1 || m.2.2 then 0 else q))) =
    ∑ i : Bool × Bool, c i * ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (A i) v : ℝ) * (ρ (B i) v : ℝ) - q) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [← Finset.mul_sum]
  congr 1
  exact sum_flag_T_factor_eq_overlap N q b ρ (A i) (B i)

/-- **The increment as a pair-only `T`-sum.** -/
theorem sum_spec_eq_sign_overlap {R : Type*} (N : ℕ) (q : ℝ) (b : Fin (N + 1) → ℝ)
    (ρ : R → Fin (N + 1) → ℤˣ) (X Y : Bool → R) :
    (∑ m : (Bool × Bool) × (Bool × Bool),
      (if m.2 = (true, true) then (if m.1.1 then (1 : ℝ) else -1) * (if m.1.2 then 1 else -1)
        else 0) *
      (((N + 1 : ℝ)⁻¹ * ∑ i,
        (if m.2.1 then (ρ (X m.1.1) i : ℝ) - b i else b i) *
        (if m.2.2 then (ρ (Y m.1.2) i : ℝ) - b i else b i)) - (if m.2.1 || m.2.2 then 0 else q))) =
    ∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
      ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (X i.1) v : ℝ) * (ρ (Y i.2) v : ℝ) - q) := by
  rw [sum_sign_overlap_eq_pair_T N q b ρ X Y, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Bool.or_self,
    sub_zero]

/-- **Two special `T`-sum factors times a product of ordinary ones.** The first special factor
is pair-only; the pair labels of the special factors and of the rest are pairwise distinct
(for nonzero coefficients). The average of the product is `O(k+1)`. This is the pair-only lemma
for the index set `Bool ⊕ B`, with the sum-type bookkeeping done once. -/
theorem sk_live_sp_two_special_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R : Type*} [Fintype R] [LinearOrder R] {B : Type*} [Fintype B] [DecidableEq B]
    (c : B → Bool × Bool → ℝ) (A Bb : B → Bool × Bool → R)
    (γ0 γ1 : (Bool × Bool) × (Bool × Bool) → ℝ) (x0 y0 x1 y1 : Bool × Bool → R)
    (hAB : ∀ b i, A b i ≠ Bb b i) (hxy0 : ∀ i, x0 i ≠ y0 i) (hxy1 : ∀ i, x1 i ≠ y1 i)
    (hpo : ∀ m, γ0 m ≠ 0 → m.2 = (true, true))
    (h01 : ∀ m m', m.2 = (true, true) → m'.2 = (true, true) → γ0 m ≠ 0 → γ1 m' ≠ 0 →
      (min (x0 m.1) (y0 m.1), max (x0 m.1) (y0 m.1)) ≠
        (min (x1 m'.1) (y1 m'.1), max (x1 m'.1) (y1 m'.1)))
    (h0r : ∀ m b i, γ0 m ≠ 0 → c b i ≠ 0 →
      (min (x0 m.1) (y0 m.1), max (x0 m.1) (y0 m.1)) ≠ (min (A b i) (Bb b i), max (A b i) (Bb b i)))
    (h1r : ∀ m b i, m.2 = (true, true) → γ1 m ≠ 0 → c b i ≠ 0 →
      (min (x1 m.1) (y1 m.1), max (x1 m.1) (y1 m.1)) ≠ (min (A b i) (Bb b i), max (A b i) (Bb b i)))
    (hrest : ∀ b b' i i', b ≠ b' → c b i ≠ 0 → c b' i' ≠ 0 →
      (min (A b i) (Bb b i), max (A b i) (Bb b i)) ≠
        (min (A b' i') (Bb b' i'), max (A b' i') (Bb b' i'))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tp : Bool → Bool → R → R → (FinPairs (N + 1) → ℝ) →
        (R → Fin (N + 1) → ℤˣ) → ℝ := fun l s x y g ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if l then (ρ x i : ℝ) - bmean g i else bmean g i) *
        (if s then (ρ y i : ℝ) - bmean g i else bmean g i)) - (if l || s then 0 else q)
    |∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (∑ m : (Bool × Bool) × (Bool × Bool), γ0 m * Tp m.2.1 m.2.2 (x0 m.1) (y0 m.1) g ρ) *
        (∑ m : (Bool × Bool) × (Bool × Bool), γ1 m * Tp m.2.1 m.2.2 (x1 m.1) (y1 m.1) g ρ) *
        ∏ b, ∑ m : (Bool × Bool) × (Bool × Bool), c b m.1 *
          Tp m.2.1 m.2.2 (A b m.1) (Bb b m.1) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card B + 3 : ℕ) : ℝ) / 2) := by
  let G2 : Bool ⊕ B → (Bool × Bool) × (Bool × Bool) → ℝ :=
    Sum.elim (fun j => if j then γ1 else γ0) (fun b m => c b m.1)
  let X2 : Bool ⊕ B → Bool × Bool → R := Sum.elim (fun j => if j then x1 else x0) A
  let Y2 : Bool ⊕ B → Bool × Bool → R := Sum.elim (fun j => if j then y1 else y0) Bb
  obtain ⟨C, hC0, hC⟩ := sk_live_sp_pair_only_uniform β₀ hβ₀ G2 X2 Y2
    (fun k i => by
      cases k with
      | inl j => cases j <;> simp [X2, Y2, hxy0 i, hxy1 i]
      | inr b => exact hAB b i)
    (by
      intro k k' m m' hkk hm hm' hγ hγ'
      cases k with
      | inl j =>
        cases k' with
        | inl j' =>
          cases j <;> cases j' <;> simp only [G2, X2, Y2, Sum.elim_inl, Bool.false_eq_true,
            ite_false, ite_true] at hγ hγ' ⊢
          · exact absurd rfl hkk
          · exact h01 m m' hm hm' hγ hγ'
          · exact (h01 m' m hm' hm hγ' hγ).symm
          · exact absurd rfl hkk
        | inr b' =>
          cases j <;> simp only [G2, X2, Y2, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true,
            ite_false, ite_true] at hγ hγ' ⊢
          · exact h0r m b' m'.1 hγ hγ'
          · exact h1r m b' m'.1 hm hγ hγ'
      | inr b =>
        cases k' with
        | inl j' =>
          cases j' <;> simp only [G2, X2, Y2, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true,
            ite_false, ite_true] at hγ hγ' ⊢
          · exact (h0r m' b m.1 hγ' hγ).symm
          · exact (h1r m' b m.1 hm' hγ' hγ).symm
        | inr b' =>
          simp only [G2, X2, Y2, Sum.elim_inr] at hγ hγ' ⊢
          exact hrest b b' m.1 m'.1 (fun h => hkk (by rw [h])) hγ hγ')
    (Sum.inl false) (fun m hm => by simpa [G2] using hpo m hm)
  refine ⟨C, hC0, fun β h q hfix hb N => ?_⟩
  intro E bmean Tp
  have hfam : ∀ gg (ρ : R → Fin (N + 1) → ℤˣ),
      (∏ k : Bool ⊕ B, ∑ m, G2 k m * Tp m.2.1 m.2.2 (X2 k m.1) (Y2 k m.1) gg ρ) =
      (∑ m : (Bool × Bool) × (Bool × Bool), γ0 m * Tp m.2.1 m.2.2 (x0 m.1) (y0 m.1) gg ρ) *
        (∑ m : (Bool × Bool) × (Bool × Bool), γ1 m * Tp m.2.1 m.2.2 (x1 m.1) (y1 m.1) gg ρ) *
        ∏ b, ∑ m : (Bool × Bool) × (Bool × Bool), c b m.1 *
          Tp m.2.1 m.2.2 (A b m.1) (Bb b m.1) gg ρ := fun gg ρ => by
    rw [Fintype.prod_sum_type, Fintype.prod_bool]
    simp only [G2, X2, Y2, Sum.elim_inl, Sum.elim_inr, ite_true, Bool.false_eq_true, ite_false]
    ring
  have h1 : |∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ k : Bool ⊕ B, ∑ m, G2 k m * Tp m.2.1 m.2.2 (X2 k m.1) (Y2 k m.1) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card (Bool ⊕ B) + 1 : ℕ) : ℝ) / 2) := hC β h q hfix hb N
  simp_rw [hfam] at h1
  rw [Fintype.card_sum, Fintype.card_bool] at h1
  have hc : 2 + Fintype.card B + 1 = Fintype.card B + 3 := by ring
  rw [hc] at h1
  exact h1

/-- **Measurability and boundedness of a product of two special sums and the rest.** -/
theorem sk_live_sp_two_meas_bound (N : ℕ) (β h q : ℝ)
    {R : Type*} {B : Type*} [Fintype B]
    (c : B → Bool × Bool → ℝ) (A Bb : B → Bool × Bool → R)
    (γ0 γ1 : (Bool × Bool) × (Bool × Bool) → ℝ) (x0 y0 x1 y1 : Bool × Bool → R) :
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
      ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
    let Tp : Bool → Bool → R → R → (FinPairs (N + 1) → ℝ) →
        (R → Fin (N + 1) → ℤˣ) → ℝ := fun l s x y g ρ =>
      ((N + 1 : ℝ)⁻¹ * ∑ i,
        (if l then (ρ x i : ℝ) - bmean g i else bmean g i) *
        (if s then (ρ y i : ℝ) - bmean g i else bmean g i)) - (if l || s then 0 else q)
    (∀ ρ : R → Fin (N + 1) → ℤˣ, Measurable fun g : FinPairs (N + 1) → ℝ =>
      (∑ m : (Bool × Bool) × (Bool × Bool), γ0 m * Tp m.2.1 m.2.2 (x0 m.1) (y0 m.1) g ρ) *
        (∑ m : (Bool × Bool) × (Bool × Bool), γ1 m * Tp m.2.1 m.2.2 (x1 m.1) (y1 m.1) g ρ) *
        ∏ b, ∑ m : (Bool × Bool) × (Bool × Bool), c b m.1 *
          Tp m.2.1 m.2.2 (A b m.1) (Bb b m.1) g ρ) ∧
    ∃ Mb : ℝ, ∀ g (ρ : R → Fin (N + 1) → ℤˣ),
      |(∑ m : (Bool × Bool) × (Bool × Bool), γ0 m * Tp m.2.1 m.2.2 (x0 m.1) (y0 m.1) g ρ) *
        (∑ m : (Bool × Bool) × (Bool × Bool), γ1 m * Tp m.2.1 m.2.2 (x1 m.1) (y1 m.1) g ρ) *
        ∏ b, ∑ m : (Bool × Bool) × (Bool × Bool), c b m.1 *
          Tp m.2.1 m.2.2 (A b m.1) (Bb b m.1) g ρ| ≤ Mb := by
  intro E bmean Tp
  let G2 : Bool ⊕ B → (Bool × Bool) × (Bool × Bool) → ℝ :=
    Sum.elim (fun j => if j then γ1 else γ0) (fun b m => c b m.1)
  let X2 : Bool ⊕ B → Bool × Bool → R := Sum.elim (fun j => if j then x1 else x0) A
  let Y2 : Bool ⊕ B → Bool × Bool → R := Sum.elim (fun j => if j then y1 else y0) Bb
  obtain ⟨hm, Mb, hMb⟩ := sk_live_T_family_meas_bound N β h q
    (fun (_ : Bool ⊕ B) (m : (Bool × Bool) × (Bool × Bool)) => m.2.1)
    (fun (_ : Bool ⊕ B) (m : (Bool × Bool) × (Bool × Bool)) => m.2.2)
    (fun k m => X2 k m.1) (fun k m => Y2 k m.1) G2
  have hfam : ∀ gg (ρ : R → Fin (N + 1) → ℤˣ),
      (∏ k : Bool ⊕ B, ∑ m, G2 k m * Tp m.2.1 m.2.2 (X2 k m.1) (Y2 k m.1) gg ρ) =
      (∑ m : (Bool × Bool) × (Bool × Bool), γ0 m * Tp m.2.1 m.2.2 (x0 m.1) (y0 m.1) gg ρ) *
        (∑ m : (Bool × Bool) × (Bool × Bool), γ1 m * Tp m.2.1 m.2.2 (x1 m.1) (y1 m.1) gg ρ) *
        ∏ b, ∑ m : (Bool × Bool) × (Bool × Bool), c b m.1 *
          Tp m.2.1 m.2.2 (A b m.1) (Bb b m.1) gg ρ := fun gg ρ => by
    rw [Fintype.prod_sum_type, Fintype.prod_bool]
    simp only [G2, X2, Y2, Sum.elim_inl, Sum.elim_inr, ite_true, Bool.false_eq_true, ite_false]
    ring
  refine ⟨fun ρ => ?_, Mb, fun g ρ => ?_⟩
  · have e : (fun g : FinPairs (N + 1) → ℝ =>
        (∑ m : (Bool × Bool) × (Bool × Bool), γ0 m * Tp m.2.1 m.2.2 (x0 m.1) (y0 m.1) g ρ) *
        (∑ m : (Bool × Bool) × (Bool × Bool), γ1 m * Tp m.2.1 m.2.2 (x1 m.1) (y1 m.1) g ρ) *
        ∏ b, ∑ m : (Bool × Bool) × (Bool × Bool), c b m.1 *
          Tp m.2.1 m.2.2 (A b m.1) (Bb b m.1) g ρ) = fun g =>
        ∏ k : Bool ⊕ B, ∑ m, G2 k m * Tp m.2.1 m.2.2 (X2 k m.1) (Y2 k m.1) g ρ :=
      funext fun g => (hfam g ρ).symm
    rw [e]
    exact hm ρ
  · have := hMb g ρ
    rw [← hfam] at *
    exact this

/-- **Increment against a matched factor.** The increment `Inc = ∑ sg₁ sg₂ (R_{X i₁,Y i₂} - q)`
and the overlap polynomial `U_u = ∑_i cu i (R_{Au i,Bu i} - q)` share exactly one pair label,
that of the term `i = (true,true)` (with `cu (true,true) = 1`, `X true = Au (true,true)`,
`Y true = Bu (true,true)`); all other pair labels are distinct from each other and from those of
the remaining factors. Then `ν(Inc · U_u · ∏_b U_b)` equals `α/(1-β²α)/(N+1)` times
`ν(∏_b U_b)` up to `O(k+1)`. -/
theorem sk_live_inc_matched_uniform (β₀ : ℝ) (hβ₀ : 4 * β₀ ^ 2 < 1)
    {R : Type*} [Fintype R] [LinearOrder R] {B : Type*} [Fintype B] [DecidableEq B]
    (c : B → Bool × Bool → ℝ) (A Bb : B → Bool × Bool → R) (X Y : Bool → R)
    (cu : Bool × Bool → ℝ) (Au Bu : Bool × Bool → R)
    (hAB : ∀ b i, A b i ≠ Bb b i) (hXY : ∀ i₁ i₂, X i₁ ≠ Y i₂) (hABu : ∀ i, Au i ≠ Bu i)
    (hu1 : cu (true, true) = 1) (hX : X true = Au (true, true)) (hY : Y true = Bu (true, true))
    (hrest : ∀ b b' i i', b ≠ b' → c b i ≠ 0 → c b' i' ≠ 0 →
      (min (A b i) (Bb b i), max (A b i) (Bb b i)) ≠
        (min (A b' i') (Bb b' i'), max (A b' i') (Bb b' i')))
    (hinc_rest : ∀ i₁ i₂ b i, c b i ≠ 0 →
      (min (X i₁) (Y i₂), max (X i₁) (Y i₂)) ≠ (min (A b i) (Bb b i), max (A b i) (Bb b i)))
    (hu_rest : ∀ i b i', cu i ≠ 0 → c b i' ≠ 0 →
      (min (Au i) (Bu i), max (Au i) (Bu i)) ≠ (min (A b i') (Bb b i'), max (A b i') (Bb b i')))
    (hinc_u : ∀ i₁ i₂ i, (i₁, i₂) ≠ (true, true) → cu i ≠ 0 →
      (min (X i₁) (Y i₂), max (X i₁) (Y i₂)) ≠ (min (Au i) (Bu i), max (Au i) (Bu i)))
    (hT1_u : ∀ i, i ≠ (true, true) → cu i ≠ 0 →
      (min (X true) (Y true), max (X true) (Y true)) ≠ (min (Au i) (Bu i), max (Au i) (Bu i))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β h q : ℝ),
      (∫ t : ℝ, Real.tanh (β * Real.sqrt q * t + h) ^ 2 ∂gaussianReal 0 1 = q) →
      β ^ 2 ≤ β₀ ^ 2 → ∀ N : ℕ,
    let E : (FinPairs (N + 1) → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g σ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (σ p.val.1 : ℝ) * (σ p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (σ i : ℝ)
    let α : ℝ := (∫ t : ℝ, Real.tanh (β * t * Real.sqrt q + h) ^ 4
      ∂gaussianReal 0 1) - 2 * q + 1
    |(∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (X i.1) v : ℝ) * (ρ (Y i.2) v : ℝ) - q)) *
        (∑ i, cu i * ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (Au i) v : ℝ) * (ρ (Bu i) v : ℝ) - q)) *
        ∏ b, ∑ i, c b i * ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (A b i) v : ℝ) * (ρ (Bb b i) v : ℝ) - q)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      α / (1 - β ^ 2 * α) / (N + 1 : ℝ) *
      (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ b, ∑ i, c b i * ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (A b i) v : ℝ) * (ρ (Bb b i) v : ℝ) - q)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))| ≤
      C / ((N : ℝ) + 1) ^ (((Fintype.card B + 3 : ℕ) : ℝ) / 2) := by
  let sg : Bool × Bool → ℝ := fun i => (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1)
  let ms : (Bool × Bool) × (Bool × Bool) := ((true, true), (true, true))
  let δ : (Bool × Bool) × (Bool × Bool) → ℝ := fun m => if m = ms then 1 else 0
  let γinc : (Bool × Bool) × (Bool × Bool) → ℝ := fun m =>
    if m.2 = (true, true) then sg m.1 else 0
  let γu : (Bool × Bool) × (Bool × Bool) → ℝ := fun m => cu m.1
  let xI : Bool × Bool → R := fun i => X i.1
  let yI : Bool × Bool → R := fun i => Y i.2
  have hsg : sg (true, true) = 1 := by simp [sg]
  have hδ0 : ∀ m, δ m ≠ 0 → m = ms := fun m hm => by
    by_contra h; exact hm (by simp [δ, h])
  have hinc0 : ∀ m, (γinc m - δ m) ≠ 0 → m.2 = (true, true) ∧ m.1 ≠ (true, true) := by
    intro m hm
    by_cases h2 : m.2 = (true, true)
    · refine ⟨h2, fun h1 => hm ?_⟩
      have : m = ms := Prod.ext h1 h2
      simp [γinc, δ, this, ms, hsg]
    · exact absurd (by
        have : m ≠ ms := fun h => h2 (by rw [h])
        simp [γinc, δ, h2, this]) hm
  have hQ0 : ∀ m, m.2 = (true, true) → (γu m - δ m) ≠ 0 → m.1 ≠ (true, true) ∧ cu m.1 ≠ 0 := by
    intro m h2 hm
    have h1 : m.1 ≠ (true, true) := fun h1 => hm (by
      have : m = ms := Prod.ext h1 h2
      simp [γu, δ, this, ms, hu1])
    refine ⟨h1, fun hc => hm ?_⟩
    have : m ≠ ms := fun h => h1 (by rw [h])
    simp [γu, δ, this, hc]
  have hxyI : ∀ i, xI i ≠ yI i := fun i => hXY _ _
  obtain ⟨C₃, hC₃0, hC₃⟩ := sk_live_sp_two_special_uniform β₀ hβ₀ c A Bb
    (fun m => γinc m - δ m) γu xI yI Au Bu hAB hxyI hABu (fun m hm => (hinc0 m hm).1)
    (fun m m' _ _ hγ hγ' => hinc_u m.1.1 m.1.2 m'.1 (fun h => (hinc0 m hγ).2 h) hγ')
    (fun m b i _ hc => hinc_rest m.1.1 m.1.2 b i hc)
    (fun m b i _ hγ hc => hu_rest m.1 b i hγ hc) hrest
  obtain ⟨C₄, hC₄0, hC₄⟩ := sk_live_sp_two_special_uniform β₀ hβ₀ c A Bb
    δ (fun m => γu m - δ m) xI yI Au Bu hAB hxyI hABu (fun m hm => by rw [hδ0 m hm])
    (fun m m' _ hm' hγ hγ' => by
      have hm0 := hδ0 m hγ
      have hQ := hQ0 m' hm' hγ'
      rw [hm0]
      exact hT1_u m'.1 hQ.1 hQ.2)
    (fun m b i hγ hc => hinc_rest m.1.1 m.1.2 b i hc)
    (fun m b i hm hγ hc => hu_rest m.1 b i (hQ0 m hm hγ).2 hc) hrest
  have hrestinj : ∀ (b b' : B) (m m' : (Bool × Bool) × (Bool × Bool)), b ≠ b' →
      m.2 = (true, true) → m'.2 = (true, true) → c b m.1 ≠ 0 → c b' m'.1 ≠ 0 →
      (min (A b m.1) (Bb b m.1), max (A b m.1) (Bb b m.1)) ≠
        (min (A b' m'.1) (Bb b' m'.1), max (A b' m'.1) (Bb b' m'.1)) :=
    fun b b' m m' hkk _ _ h h' => hrest b b' m.1 m'.1 hkk h h'
  obtain ⟨C₁, hC₁0, hC₁⟩ := sk_live_sp_square_uniform β₀ hβ₀
    (fun (b : B) (m : (Bool × Bool) × (Bool × Bool)) => c b m.1) A Bb hAB hrestinj
    (min (X true) (Y true)) (max (X true) (Y true)) (min_lt_max.mpr (hXY true true))
    (fun b m _ hc => (hinc_rest true true b m.1 hc).symm)
  obtain ⟨C₂, hC₂0, hC₂⟩ := sk_live_sp_drop_pair_uniform β₀ hβ₀
    (fun (b : B) (m : (Bool × Bool) × (Bool × Bool)) => c b m.1) A Bb hAB hrestinj
  refine ⟨C₁ + 2 * C₂ + C₃ + C₄ + 1, by positivity, fun β h q hfix hb N => ?_⟩
  intro E α
  let bmean : (FinPairs (N + 1) → ℝ) → Fin (N + 1) → ℝ := fun g i =>
    ∫ σ : Fin (N + 1) → ℤˣ, (σ i : ℝ) ∂(Measure.count.tilted (E g))
  let Tp : Bool → Bool → R → R → (FinPairs (N + 1) → ℝ) →
      (R → Fin (N + 1) → ℤˣ) → ℝ := fun l s x y g ρ =>
    ((N + 1 : ℝ)⁻¹ * ∑ i,
      (if l then (ρ x i : ℝ) - bmean g i else bmean g i) *
      (if s then (ρ y i : ℝ) - bmean g i else bmean g i)) - (if l || s then 0 else q)
  let Sg : ((Bool × Bool) × (Bool × Bool) → ℝ) → (Bool × Bool → R) → (Bool × Bool → R) →
      (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ := fun g0 x0 y0 gg ρ =>
    ∑ m, g0 m * Tp m.2.1 m.2.2 (x0 m.1) (y0 m.1) gg ρ
  have hSadd : ∀ g0 g1 x0 y0 gg ρ, Sg (fun m => g0 m + g1 m) x0 y0 gg ρ =
      Sg g0 x0 y0 gg ρ + Sg g1 x0 y0 gg ρ := fun g0 g1 x0 y0 gg ρ => by
    simp only [Sg, add_mul, Finset.sum_add_distrib]
  have hSδ : ∀ x0 y0 gg ρ,
      Sg δ x0 y0 gg ρ = Tp true true (x0 (true, true)) (y0 (true, true)) gg ρ :=
    fun x0 y0 gg ρ => by
    simp only [Sg]
    rw [Finset.sum_eq_single ms]
    · simp [δ, ms]
    · intro m _ hm
      simp [δ, hm]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  have hInc : ∀ gg ρ, Sg γinc xI yI gg ρ =
      ∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
        ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (X i.1) v : ℝ) * (ρ (Y i.2) v : ℝ) - q) :=
    fun gg ρ => sum_spec_eq_sign_overlap N q (bmean gg) ρ X Y
  have hUu : ∀ gg ρ, Sg γu Au Bu gg ρ =
      ∑ i, cu i * ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (Au i) v : ℝ) * (ρ (Bu i) v : ℝ) - q) :=
    fun gg ρ => sum_spec_eq_overlap_poly N q (bmean gg) ρ cu Au Bu
  have hUb : ∀ b gg ρ, Sg (fun m => c b m.1) (A b) (Bb b) gg ρ =
      ∑ i, c b i * ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (A b i) v : ℝ) * (ρ (Bb b i) v : ℝ) - q) :=
    fun b gg ρ => sum_spec_eq_overlap_poly N q (bmean gg) ρ (c b) (A b) (Bb b)
  have hT : ∀ gg ρ, Sg δ Au Bu gg ρ = Sg δ xI yI gg ρ := fun gg ρ => by
    rw [hSδ, hSδ]
    simp only [xI, yI, hX, hY]
  let Rf : (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ := fun gg ρ =>
    ∏ b, Sg (fun m => c b m.1) (A b) (Bb b) gg ρ
  have hpt : ∀ gg ρ,
      ((∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (X i.1) v : ℝ) * (ρ (Y i.2) v : ℝ) - q)) *
        (∑ i, cu i * ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (Au i) v : ℝ) * (ρ (Bu i) v : ℝ) - q)) *
        ∏ b, ∑ i, c b i * ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (A b i) v : ℝ) * (ρ (Bb b i) v : ℝ) - q)) =
      Sg δ xI yI gg ρ * Sg δ xI yI gg ρ * Rf gg ρ +
      Sg (fun m => γinc m - δ m) xI yI gg ρ * Sg γu Au Bu gg ρ * Rf gg ρ +
      Sg δ xI yI gg ρ * Sg (fun m => γu m - δ m) Au Bu gg ρ * Rf gg ρ := fun gg ρ => by
    have hR : (∏ b, ∑ i, c b i * ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (A b i) v : ℝ) *
        (ρ (Bb b i) v : ℝ) - q)) = Rf gg ρ := Finset.prod_congr rfl fun b _ => (hUb b gg ρ).symm
    rw [hR, ← hInc, ← hUu]
    have e1 : Sg γinc xI yI gg ρ = Sg (fun m => γinc m - δ m) xI yI gg ρ + Sg δ xI yI gg ρ := by
      rw [← hSadd]
      congr 1
      funext m
      ring
    have e2 : Sg γu Au Bu gg ρ = Sg (fun m => γu m - δ m) Au Bu gg ρ + Sg δ Au Bu gg ρ := by
      rw [← hSadd]
      congr 1
      funext m
      ring
    rw [e1, e2, hT]
    ring
  have hmeasE : ∀ σ, Measurable fun g : FinPairs (N + 1) → ℝ => E g σ := fun σ => by
    dsimp only [E]
    fun_prop
  obtain ⟨hm1, M1, hM1⟩ := sk_live_sp_two_meas_bound N β h q c A Bb δ δ xI yI xI yI
  obtain ⟨hm2, M2, hM2⟩ := sk_live_sp_two_meas_bound N β h q c A Bb
    (fun m => γinc m - δ m) γu xI yI Au Bu
  obtain ⟨hm3, M3, hM3⟩ := sk_live_sp_two_meas_bound N β h q c A Bb
    δ (fun m => γu m - δ m) xI yI Au Bu
  let P1 : (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ := fun gg ρ =>
    Sg δ xI yI gg ρ * Sg δ xI yI gg ρ * Rf gg ρ
  let P2 : (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ := fun gg ρ =>
    Sg (fun m => γinc m - δ m) xI yI gg ρ * Sg γu Au Bu gg ρ * Rf gg ρ
  let P3 : (FinPairs (N + 1) → ℝ) → (R → Fin (N + 1) → ℤˣ) → ℝ := fun gg ρ =>
    Sg δ xI yI gg ρ * Sg (fun m => γu m - δ m) Au Bu gg ρ * Rf gg ρ
  have hMx : ∀ gg ρ, |P1 gg ρ| ≤ |M1| + |M2| + |M3| ∧ |P2 gg ρ| ≤ |M1| + |M2| + |M3| ∧
      |P3 gg ρ| ≤ |M1| + |M2| + |M3| := fun gg ρ => by
    refine ⟨?_, ?_, ?_⟩
    · exact (hM1 gg ρ).trans ((le_abs_self M1).trans (by linarith [abs_nonneg M2, abs_nonneg M3]))
    · exact (hM2 gg ρ).trans ((le_abs_self M2).trans (by linarith [abs_nonneg M1, abs_nonneg M3]))
    · exact (hM3 gg ρ).trans ((le_abs_self M3).trans (by linarith [abs_nonneg M1, abs_nonneg M2]))
  have hsplit : (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, (P1 g ρ + P2 g ρ + P3 g ρ)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, P1 g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) +
      (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, P2 g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) +
      (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, P3 g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) := by
    have e12 := integral_integral_pi_count_tilted_add
      (μ := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) (R := R)
      (fun g σ => E g σ) hmeasE (fun g ρ => P1 g ρ + P2 g ρ) P3
      (fun ρ => (hm1 ρ).add (hm2 ρ)) hm3 (2 * (|M1| + |M2| + |M3|))
      (fun gg ρ => by
        refine (abs_add_le _ _).trans ?_
        have := hMx gg ρ
        linarith [this.1, this.2.1])
      (fun gg ρ => by
        have := (hMx gg ρ).2.2
        linarith [abs_nonneg M1, abs_nonneg M2, abs_nonneg M3])
    have e1 := integral_integral_pi_count_tilted_add
      (μ := Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) (R := R)
      (fun g σ => E g σ) hmeasE P1 P2 hm1 hm2 (|M1| + |M2| + |M3|)
      (fun gg ρ => (hMx gg ρ).1) (fun gg ρ => (hMx gg ρ).2.1)
    rw [e12, e1]
  have hα01 := tanh_fourth_sub_two_mul_add_one_mem_Icc_of_fixedPoint hfix
  have hα : 0 ≤ α ∧ α ≤ 1 := hα01
  have hden : 3 / 4 ≤ 1 - β ^ 2 * α := by
    have h2 : β ^ 2 * α ≤ β ^ 2 * 1 := mul_le_mul_of_nonneg_left hα.2 (sq_nonneg _)
    linarith only [h2, hb, hβ₀]
  have hDpos : 0 < 1 - β ^ 2 * α := by linarith only [hden]
  have hc2 : 0 ≤ α / (1 - β ^ 2 * α) / (N + 1 : ℝ) ∧
      α / (1 - β ^ 2 * α) / (N + 1 : ℝ) ≤ 4 / 3 / (N + 1 : ℝ) := by
    refine ⟨div_nonneg (div_nonneg hα.1 hDpos.le) (by positivity),
      div_le_div_of_nonneg_right ?_ (by positivity)⟩
    rw [div_le_iff₀ hDpos]
    nlinarith only [hden, hα.2]
  have hTmm : ∀ (a b : R) gg ρ, Tp true true (min a b) (max a b) gg ρ = Tp true true a b gg ρ :=
    fun a b gg ρ => by
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab, max_eq_right hab]
    · rw [min_eq_right hab, max_eq_left hab]
      simp only [Tp, mul_comm]
  have hP1 : ∀ gg ρ, P1 gg ρ =
      Tp true true (min (X true) (Y true)) (max (X true) (Y true)) gg ρ *
      Tp true true (min (X true) (Y true)) (max (X true) (Y true)) gg ρ * Rf gg ρ :=
    fun gg ρ => by
    simp only [P1, hSδ, hTmm, xI, yI]
  have h1' : |(∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, P1 g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      α / (1 - β ^ 2 * α) / (N + 1 : ℝ) *
      (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ b, ∑ m : (Bool × Bool) × (Bool × Bool),
          (if m.2.1 = true ∧ m.2.2 = true then 0 else c b m.1) *
          Tp m.2.1 m.2.2 (A b m.1) (Bb b m.1) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))| ≤
      C₁ / ((N : ℝ) + 1) ^ (((Fintype.card B + 2 + 1 : ℕ) : ℝ) / 2) := by
    simp_rw [hP1]
    exact hC₁ β h q hfix hb N
  have h2' : |(∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, Rf g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) -
      (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ b, ∑ m : (Bool × Bool) × (Bool × Bool),
          (if m.2.1 = true ∧ m.2.2 = true then 0 else c b m.1) *
          Tp m.2.1 m.2.2 (A b m.1) (Bb b m.1) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))| ≤
      C₂ / ((N : ℝ) + 1) ^ (((Fintype.card B + 1 : ℕ) : ℝ) / 2) := hC₂ β h q hfix hb N
  have h3' : |∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, P2 g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      C₃ / ((N : ℝ) + 1) ^ (((Fintype.card B + 3 : ℕ) : ℝ) / 2) := hC₃ β h q hfix hb N
  have h4' : |∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, P3 g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)| ≤
      C₄ / ((N : ℝ) + 1) ^ (((Fintype.card B + 3 : ℕ) : ℝ) / 2) := hC₄ β h q hfix hb N
  have hRpure : ∀ gg (ρ : R → Fin (N + 1) → ℤˣ),
      (∏ b, ∑ i, c b i * ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (A b i) v : ℝ) * (ρ (Bb b i) v : ℝ) - q)) =
        Rf gg ρ := fun gg ρ => Finset.prod_congr rfl fun b _ => (hUb b gg ρ).symm
  have hI : (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        (∑ i : Bool × Bool, (if i.1 then (1 : ℝ) else -1) * (if i.2 then 1 else -1) *
          ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (X i.1) v : ℝ) * (ρ (Y i.2) v : ℝ) - q)) *
        (∑ i, cu i * ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (Au i) v : ℝ) * (ρ (Bu i) v : ℝ) - q)) *
        ∏ b, ∑ i, c b i * ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (A b i) v : ℝ) * (ρ (Bb b i) v : ℝ) - q)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, (P1 g ρ + P2 g ρ + P3 g ρ)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
    integral_congr_ae (ae_of_all _ fun g =>
      integral_congr_ae (ae_of_all _ fun ρ => hpt g ρ))
  have hIR : (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ b, ∑ i, c b i * ((N + 1 : ℝ)⁻¹ * ∑ v, (ρ (A b i) v : ℝ) * (ρ (Bb b i) v : ℝ) - q)
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) =
      ∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, Rf g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) :=
    integral_congr_ae (ae_of_all _ fun g =>
      integral_congr_ae (ae_of_all _ fun ρ => hRpure g ρ))
  rw [hI, hIR, hsplit]
  have e3 : ((Fintype.card B + 2 + 1 : ℕ) : ℝ) = ((Fintype.card B + 3 : ℕ) : ℝ) := by
    push_cast; ring
  rw [e3] at h1'
  generalize hI1 : (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, P1 g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) = I1 at h1' ⊢
  generalize hI2 : (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, P2 g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) = I2 at h3' ⊢
  generalize hI3 : (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, P3 g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) = I3 at h4' ⊢
  generalize hIR : (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ, Rf g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) = IR at h2' ⊢
  generalize hInp : (∫ g, ∫ ρ : R → Fin (N + 1) → ℤˣ,
        ∏ b, ∑ m : (Bool × Bool) × (Bool × Bool),
          (if m.2.1 = true ∧ m.2.2 = true then 0 else c b m.1) *
          Tp m.2.1 m.2.2 (A b m.1) (Bb b m.1) g ρ
        ∂(Measure.pi fun _ : R => Measure.count.tilted (E g))
        ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) = Inp at h1' h2'
  set c₂ : ℝ := α / (1 - β ^ 2 * α) / (N + 1 : ℝ) with hc₂
  have hD : ((N : ℝ) + 1) ^ (((Fintype.card B + 3 : ℕ) : ℝ) / 2) =
      ((N : ℝ) + 1) * ((N : ℝ) + 1) ^ (((Fintype.card B + 1 : ℕ) : ℝ) / 2) := by
    have hexp : ((Fintype.card B + 3 : ℕ) : ℝ) / 2 = 1 + ((Fintype.card B + 1 : ℕ) : ℝ) / 2 := by
      push_cast; ring
    rw [hexp, Real.rpow_add (by positivity), Real.rpow_one]
  have hDp : 0 < ((N : ℝ) + 1) ^ (((Fintype.card B + 1 : ℕ) : ℝ) / 2) := by positivity
  have hDq : 0 < ((N : ℝ) + 1) ^ (((Fintype.card B + 3 : ℕ) : ℝ) / 2) := by positivity
  have hcross : |c₂ * (Inp - IR)| ≤ 4 / 3 * C₂ /
      ((N : ℝ) + 1) ^ (((Fintype.card B + 3 : ℕ) : ℝ) / 2) := by
    rw [abs_mul, abs_of_nonneg hc2.1, abs_sub_comm]
    calc c₂ * |IR - Inp| ≤ 4 / 3 / (N + 1 : ℝ) * (C₂ / ((N : ℝ) + 1) ^
          (((Fintype.card B + 1 : ℕ) : ℝ) / 2)) :=
          mul_le_mul hc2.2 h2' (abs_nonneg _) (by positivity)
      _ = _ := by
        rw [hD]
        field_simp
  calc |I1 + I2 + I3 - c₂ * IR|
      = |(I1 - c₂ * Inp) + I2 + I3 + c₂ * (Inp - IR)| := congrArg abs (by ring)
    _ ≤ |I1 - c₂ * Inp| + |I2| + |I3| + |c₂ * (Inp - IR)| := by
      have a1 := abs_add_le ((I1 - c₂ * Inp) + I2 + I3) (c₂ * (Inp - IR))
      have a2 := abs_add_le ((I1 - c₂ * Inp) + I2) I3
      have a3 := abs_add_le (I1 - c₂ * Inp) I2
      linarith only [a1, a2, a3]
    _ ≤ C₁ / ((N : ℝ) + 1) ^ (((Fintype.card B + 3 : ℕ) : ℝ) / 2) +
        C₃ / ((N : ℝ) + 1) ^ (((Fintype.card B + 3 : ℕ) : ℝ) / 2) +
        C₄ / ((N : ℝ) + 1) ^ (((Fintype.card B + 3 : ℕ) : ℝ) / 2) +
        4 / 3 * C₂ / ((N : ℝ) + 1) ^ (((Fintype.card B + 3 : ℕ) : ℝ) / 2) := by
      gcongr
    _ ≤ _ := by
      rw [← add_div, ← add_div, ← add_div]
      exact div_le_div_of_nonneg_right (by linarith [hC₂0]) hDq.le

end SpinGlasses
