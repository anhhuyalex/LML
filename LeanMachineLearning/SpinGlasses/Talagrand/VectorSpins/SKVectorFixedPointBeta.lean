/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.SKVectorFixedPointPath
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.SKVectorFixedPointExistence
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.SKVectorConcreteModel

/-!
# Dependence of the fixed-point map on the inverse temperature

Writing the Gaussian field as `Y = b X` with `X` of covariance `q`, the field model has energy
`∑ b Xᵤ ξᵤ + (b²/2) ∑ ξᵤ ξᵥ (ρ - q)ᵤᵥ`.  The replica derivative theorem bounds the derivative of
`b ↦ 𝔼 ⟨F⟩` by `4 b D M (n+1)² d³`, which gives the Lipschitz dependence in `b` needed to show
that the fixed point of (1.372)--(1.373) is Lipschitz in `β` (Theorem 1.12.3).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

variable {α : Type*} [MeasurableSpace α]

omit [MeasurableSpace α] in
/-- The energy along the `β`-path is the field exponent of the scaled field. -/
theorem skVectorBetaEnergy_eq {d : ℕ} (ξ : α → Fin d → ℝ) (ρ q : Fin d → Fin d → ℝ)
    (x : Fin d → ℝ) (b : ℝ) (a : α) :
    0 + ∑ k : Fin d, b * x k * ξ a k +
      ∑ j : Fin d × Fin d, (b ^ 2 / 2 * (ρ j.1 j.2 - q j.1 j.2)) * (ξ a j.1 * ξ a j.2) =
      skVectorFieldExponent ξ b ρ q (fun k => b * x k) a := by
  unfold skVectorFieldExponent
  rw [Fintype.sum_prod_type, zero_add]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun u _ => by ring) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun v _ => by ring

/-- **Derivative of the replica Gibbs average in the inverse temperature.**  With `Z` a centered
Gaussian field of covariance `q` and the energy `∑ b Zₖ ξₖ + (b²/2) ∑ ξᵤ ξᵥ (ρ - q)ᵤᵥ`, the
expected `n`-replica Gibbs average of `F` is differentiable at `b > 0` with derivative of absolute
value at most `4 b (n+1)² M d³ (D_q + D_{ρ-q})`, where `D_q`, `D_{ρ-q}` bound the entries. -/
theorem skVectorField_beta_hasDerivAt {d : ℕ} {Ω R : Type*} [MeasurableSpace Ω] [Fintype R]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d)
    (ρ q : Fin d → Fin d → ℝ) {Dq DA : ℝ} (hq : ∀ u v, |q u v| ≤ Dq)
    (hA : ∀ u v, |ρ u v - q u v| ≤ DA)
    (F : (R → α) → ℝ) (hF : Measurable F) {M : ℝ} (hM : 0 ≤ M) (hFb : ∀ σ, |F σ| ≤ M)
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Fin d → Ω → ℝ}
    (hZ : HasGaussianLaw (fun ω k => Z k ω) P) (hZm : ∀ k, Measurable (Z k))
    (hmean : ∀ k, ∫ ω, Z k ω ∂P = 0) (hcov : ∀ x y, ∫ ω, Z x ω * Z y ω ∂P = q x y)
    {b : ℝ} (hb : 0 < b) :
    ∃ V : ℝ, HasDerivAt (fun r => ∫ ω, ∫ σ : R → α, F σ ∂(Measure.pi fun _ : R => μ.tilted
        fun a => 0 + ∑ k : Fin d, r * Z k ω * ξ a k +
          ∑ j : Fin d × Fin d, (r ^ 2 / 2 * (ρ j.1 j.2 - q j.1 j.2)) * (ξ a j.1 * ξ a j.2)) ∂P)
      V b ∧
      |V| ≤ b * ((d : ℝ) * d * Dq * (4 * (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) * M * d)
          +
        (d : ℝ) * d * DA * (2 * ((Fintype.card R : ℝ) + 1) * M * d)) := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hxb : ∀ a u, |ξ a u| ≤ Real.sqrt d := abs_spin_le ξ hbound
  have hxs : ∀ a u v, |ξ a u * ξ a v| ≤ d := fun a u v =>
    abs_spin_mul_le ξ (Nat.cast_nonneg d) hbound a a u v
  have hsd : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  set CA : ℝ := ∑ j : Fin d × Fin d, |(b + 1) * (ρ j.1 j.2 - q j.1 j.2)| with hCA
  have hCA0 : 0 ≤ CA := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hd := hasDerivAt_integral_gibbs_replica_cavity_path (μ := μ) (R := R) (P := P)
    (D := fun _ => (0 : ℝ)) (X := fun (k : Fin d) a => ξ a k)
    (Xs := fun (j : Fin d × Fin d) a => ξ a j.1 * ξ a j.2) (F := F) (Eb := 0)
    (B := Real.sqrt d + d) (M := M) measurable_const hξ (fun j => (hξ j.1).mul (hξ j.2)) hF
    (by positivity) hM (fun _ => by simp)
    (fun k a => (hxb a k).trans (by linarith)) (fun j a => (hxs a j.1 j.2).trans (by linarith))
    hFb hZ hZm hmean
    (s := fun k r => r) (c := fun j r => r ^ 2 / 2 * (ρ j.1 j.2 - q j.1 j.2))
    (s' := fun k _ => 1) (c' := fun j r => r * (ρ j.1 j.2 - q j.1 j.2))
    (t := b) (δ := 1) (C := 1 + CA) one_pos
    (fun k r _ => hasDerivAt_id r)
    (fun j r _ => by
      have := ((hasDerivAt_id r).pow 2).div_const 2 |>.mul_const (ρ j.1 j.2 - q j.1 j.2)
      refine this.congr_deriv ?_
      simp only [Nat.cast_ofNat, id_eq]
      ring)
    (fun k r _ => by
      rw [abs_one]
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _))
    (fun j r hr' => by
      rw [Metric.mem_ball, Real.dist_eq] at hr'
      have h1 : |r| ≤ b + 1 := by
        have := (abs_lt.1 hr')
        rw [abs_le]; constructor <;> linarith [this.1, this.2]
      have : |r * (ρ j.1 j.2 - q j.1 j.2)| ≤ |(b + 1) * (ρ j.1 j.2 - q j.1 j.2)| := by
        rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < b + 1)]
        exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      have h2 := Finset.single_le_sum (f := fun j : Fin d × Fin d =>
        |(b + 1) * (ρ j.1 j.2 - q j.1 j.2)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      linarith [hCA0])
    (fun k => Or.inr hb.ne')
  refine ⟨_, hd, ?_⟩
  obtain ⟨en, hen⟩ : ∃ en : Ω → α → ℝ, ∀ ω, en ω = fun a => 0 + ∑ k' : Fin d,
      b * Z k' ω * ξ a k' + ∑ j' : Fin d × Fin d,
        (b ^ 2 / 2 * (ρ j'.1 j'.2 - q j'.1 j'.2)) * (ξ a j'.1 * ξ a j'.2) := ⟨_, fun _ => rfl⟩
  simp only [← hen]
  obtain ⟨E1, hE1⟩ : ∃ E1 : Fin d → Fin d → ℝ, ∀ k l, E1 k l =
      ∫ ω, ∫ σ : Option (Option R) → α, (F fun a => σ (some (some a))) *
        (∑ a, ξ (σ (some (some a))) k - (Fintype.card R : ℝ) * ξ (σ (some none)) k) *
        (∑ o, ξ (σ (some o)) l - ((Fintype.card R : ℝ) + 1) * ξ (σ none) l)
        ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (en ω)) ∂P := ⟨_, fun _ _ => rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ E2 : Fin d × Fin d → ℝ, ∀ j, E2 j =
      ∫ ω, ∫ σ : Option (Option R) → α, (F fun a => σ (some (some a))) *
        (∑ o, ξ (σ (some o)) j.1 * ξ (σ (some o)) j.2 -
          ((Fintype.card R : ℝ) + 1) * (ξ (σ none) j.1 * ξ (σ none) j.2))
        ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (en ω)) ∂P := ⟨_, fun _ => rfl⟩
  simp only [← hE1, ← hE2]
  have hen' : ∀ ω, en ω = skVectorFieldExponent ξ b ρ q (fun k => b * Z k ω) := fun ω =>
    funext fun a => by rw [hen]; exact skVectorBetaEnergy_eq ξ ρ q (fun k => Z k ω) b a
  have hprob : ∀ ω, IsProbabilityMeasure (μ.tilted (en ω)) := fun ω => by
    rw [hen']
    exact isProbabilityMeasure_tilted (skVectorFieldExponent_integrable μ ξ hξ hr hbound b _ _ _)
  have hint : ∀ (G : (Option (Option R) → α) → ℝ) (C : ℝ), (∀ σ, |G σ| ≤ C) →
      |∫ ω, ∫ σ, G σ ∂(Measure.pi fun _ : Option (Option R) => μ.tilted (en ω)) ∂P| ≤ C := by
    intro G C hG
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := C) (Filter.Eventually.of_forall fun ω =>
        ?_)).trans
      (by simp)
    have := hprob ω
    have := norm_integral_le_of_norm_le_const
      (μ := Measure.pi fun _ : Option (Option R) => μ.tilted (en ω)) (f := G) (C := C)
      (Filter.Eventually.of_forall fun σ => by simpa using hG σ)
    simpa using this
  set n : ℝ := (Fintype.card R : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hcardo : (Fintype.card (Option R) : ℝ) = n + 1 := by simp [hn]
  have hE1b : ∀ k l, |E1 k l| ≤ M * (2 * n * Real.sqrt d) * (2 * (n + 1) * Real.sqrt d) := by
    intro k l
    rw [hE1]
    refine hint _ _ fun σ => ?_
    rw [abs_mul, abs_mul]
    have h1 := abs_replica_combination_le (fun a : R => ξ (σ (some (some a))) k)
      (ξ (σ (some none)) k) (Real.sqrt d) (fun a => hxb _ _) (hxb _ _) (c := n) rfl
    have h2 := abs_replica_combination_le (fun o : Option R => ξ (σ (some o)) l)
      (ξ (σ none) l) (Real.sqrt d) (fun a => hxb _ _) (hxb _ _) hcardo
    exact mul_le_mul (mul_le_mul (hFb _) h1 (abs_nonneg _) hM) h2 (abs_nonneg _)
      (by positivity)
  have hE2b : ∀ j, |E2 j| ≤ M * (2 * (n + 1) * d) := by
    intro j
    rw [hE2]
    refine hint _ _ fun σ => ?_
    rw [abs_mul]
    have h2 := abs_replica_combination_le (fun o : Option R => ξ (σ (some o)) j.1 * ξ (σ (some o))
        j.2)
      (ξ (σ none) j.1 * ξ (σ none) j.2) (d : ℝ) (fun a => hxs _ _ _) (hxs _ _ _) hcardo
    exact mul_le_mul (hFb _) h2 (abs_nonneg _) hM
  have hsqd : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hr
  have hE1b' : ∀ k l, |E1 k l| ≤ 4 * n * (n + 1) * M * d := fun k l => by
    refine (hE1b k l).trans (le_of_eq ?_)
    calc M * (2 * n * Real.sqrt d) * (2 * (n + 1) * Real.sqrt d) =
        4 * n * (n + 1) * M * (Real.sqrt d * Real.sqrt d) := by ring
      _ = _ := by rw [hsqd]
  simp only [hcov]
  have hb0 : 0 ≤ b := hb.le
  have hA1 : |∑ k, ∑ l, (1 * b * q k l) * E1 k l| ≤
      (d : ℝ) * d * ((b * Dq) * (4 * n * (n + 1) * M * d)) := by
    have hterm : ∀ k l, |(1 * b * q k l) * E1 k l| ≤ (b * Dq) * (4 * n * (n + 1) * M * d) :=
      fun k l => by
        rw [abs_mul, abs_mul, one_mul, abs_of_nonneg hb0]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hq k l) hb0) (hE1b' k l) (abs_nonneg _)
          (mul_nonneg hb0 ((abs_nonneg _).trans (hq k l)))
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun k _ =>
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => hterm k l)).trans ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring_nf
    exact le_rfl
  have hA2 : |∑ j : Fin d × Fin d, (b * (ρ j.1 j.2 - q j.1 j.2)) * E2 j| ≤
      (d : ℝ) * d * ((b * DA) * (2 * (n + 1) * M * d)) := by
    have hterm : ∀ j : Fin d × Fin d, |(b * (ρ j.1 j.2 - q j.1 j.2)) * E2 j| ≤
        (b * DA) * (2 * (n + 1) * M * d) := fun j => by
      rw [abs_mul, abs_mul, abs_of_nonneg hb0]
      refine mul_le_mul (mul_le_mul_of_nonneg_left (hA j.1 j.2) hb0) ?_ (abs_nonneg _)
        (mul_nonneg hb0 ((abs_nonneg _).trans (hA j.1 j.2)))
      refine (hE2b j).trans (le_of_eq ?_)
      ring
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun j _ => hterm j).trans ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_mul]
    exact le_rfl
  refine (abs_add_le _ _).trans ((add_le_add hA1 hA2).trans (le_of_eq ?_))
  ring

/-- The `β`-dependence of the expected Gibbs average: for `0 < b₁ ≤ b₂` the average over the field
of
covariance `b² q` changes by at most `b₂ K₀ (b₂ - b₁)`. -/
theorem skVectorFieldAvg_beta_lipschitz {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (ρ q : Fin d → Fin d → ℝ)
    (hqpsd : (Matrix.of q).PosSemidef) {Dq DA : ℝ} (hDq : 0 ≤ Dq) (hDA : 0 ≤ DA)
    (hq : ∀ u v, |q u v| ≤ Dq) (hA : ∀ u v, |ρ u v - q u v| ≤ DA) (F : (Fin 2 → α) → ℝ) (hF :
        Measurable F) {M : ℝ}
    (hM : 0 ≤ M) (hFb : ∀ σ, |F σ| ≤ M) {b₁ b₂ : ℝ} (hb₁ : 0 < b₁) (hb₁₂ : b₁ ≤ b₂) :
    |(∫ y, skVectorFieldAvg μ ξ b₂ ρ q F y ∂(skVectorGaussLaw b₂ q)) -
        ∫ y, skVectorFieldAvg μ ξ b₁ ρ q F y ∂(skVectorGaussLaw b₁ q)| ≤
      b₂ * ((d : ℝ) * d * Dq * (4 * 2 * (2 + 1) * M * d) +
        (d : ℝ) * d * DA * (2 * (2 + 1) * M * d)) * (b₂ - b₁) := by
  classical
  have := isGaussian_skVectorGaussLaw 1 q
  set P := skVectorGaussLaw 1 q with hP
  have hZ : HasGaussianLaw (fun (y : Fin d → ℝ) (k : Fin d) => y k) P :=
    IsGaussian.hasGaussianLaw_id
  have hZm : ∀ k : Fin d, Measurable fun y : Fin d → ℝ => y k := fun k => measurable_pi_apply k
  have hmean : ∀ k : Fin d, ∫ y : Fin d → ℝ, y k ∂P = 0 := fun k =>
    integral_skVectorGaussLaw_coord 1 q k
  have hcov : ∀ x y : Fin d, ∫ ω : Fin d → ℝ, ω x * ω y ∂P = q x y := fun x y => by
    have := integral_skVectorGaussLaw_mul 1 q hqpsd x y
    simpa using this
  have hlaw : ∀ b : ℝ, P.map (fun (ω : Fin d → ℝ) (u : Fin d) => b * ω u) = skVectorGaussLaw b q :=
    fun b => map_eq_skVectorGaussLaw b q (hZ.mul (fun _ => b)) (fun u => by
      rw [integral_const_mul, hmean, mul_zero]) (fun u v => by
      have : ∫ ω : Fin d → ℝ, b * ω u * (b * ω v) ∂P = b ^ 2 * ∫ ω, ω u * ω v ∂P := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
      rw [this, hcov])
  set φ : ℝ → ℝ := fun r => ∫ ω : Fin d → ℝ, ∫ σ : Fin 2 → α, F σ ∂(Measure.pi fun _ : Fin 2 =>
      μ.tilted fun a => 0 + ∑ k : Fin d, r * ω k * ξ a k +
        ∑ j : Fin d × Fin d, (r ^ 2 / 2 * (ρ j.1 j.2 - q j.1 j.2)) * (ξ a j.1 * ξ a j.2)) ∂P
    with hφ
  have hφ_eq : ∀ b : ℝ, ∫ y, skVectorFieldAvg μ ξ b ρ q F y ∂(skVectorGaussLaw b q) = φ b := by
    intro b
    rw [← integral_skVectorFieldAvg_realization μ ξ hξ b ρ q F hF
      (Y := fun (u : Fin d) (ω : Fin d → ℝ) => b * ω u)
      (fun u => (measurable_const.mul (measurable_pi_apply u) : Measurable fun ω : Fin d → ℝ => b *
          ω u))
      (hlaw b)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    unfold skVectorFieldAvg
    simp only [skVectorBetaEnergy_eq]
  rw [hφ_eq, hφ_eq]
  have hder : ∀ r : ℝ, 0 < r → ∃ V, HasDerivAt φ V r ∧ |V| ≤ r * ((d : ℝ) * d * Dq *
      (4 * 2 * (2 + 1) * M * d) + (d : ℝ) * d * DA * (2 * (2 + 1) * M * d)) := fun r hr => by
    obtain ⟨V, hV, hVb⟩ := skVectorField_beta_hasDerivAt (R := Fin 2) μ ξ hξ hbound ρ q hq hA F hF
      hM hFb hZ hZm hmean hcov hr
    refine ⟨V, hV, ?_⟩
    simpa [Fintype.card_fin] using hVb
  rcases hb₁₂.eq_or_lt with h | h
  · subst h; simp
  have hcont : ContinuousOn φ (Set.Icc b₁ b₂) := fun r hr =>
    (hder r (lt_of_lt_of_le hb₁ hr.1)).choose_spec.1.continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ φ (Set.Ioo b₁ b₂) := fun r hr =>
    (hder r (lt_trans hb₁ hr.1)).choose_spec.1.differentiableAt.differentiableWithinAt
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope φ h hcont hdiff
  obtain ⟨V, hV, hVb⟩ := hder c (lt_trans hb₁ hc.1)
  rw [hV.deriv] at hcd
  have hsl : φ b₂ - φ b₁ = V * (b₂ - b₁) := by
    rw [hcd]; field_simp
  rw [hsl, abs_mul, abs_of_nonneg (sub_nonneg.2 hb₁₂)]
  refine mul_le_mul_of_nonneg_right (hVb.trans ?_) (sub_nonneg.2 hb₁₂)
  refine mul_le_mul_of_nonneg_right hc.2.le ?_
  positivity

/-- **`β`-Lipschitz dependence of the fixed-point map.**  For `w` in the cone with entries bounded
by `Dq`, `DA` and `0 < b₁ ≤ b₂`, `T_{b₁} w` and `T_{b₂} w` are at sup-distance at most
`b₂ K₀ (b₂ - b₁)`. -/
theorem skVectorFixedMap_beta_dist_le {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) {w : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)}
    (hw : (Matrix.of w.1).PosSemidef) {Dq DA : ℝ} (hDq : 0 ≤ Dq) (hDA : 0 ≤ DA)
    (hq : ∀ u v, |w.1 u v| ≤ Dq) (hA : ∀ u v, |w.2 u v - w.1 u v| ≤ DA) {b₁ b₂ : ℝ}
    (hb₁ : 0 < b₁) (hb₁₂ : b₁ ≤ b₂) :
    dist (skVectorFixedMap μ ξ b₁ w) (skVectorFixedMap μ ξ b₂ w) ≤
      b₂ * ((d : ℝ) * d * Dq * (4 * 2 * (2 + 1) * d * d) +
        (d : ℝ) * d * DA * (2 * (2 + 1) * d * d)) * (b₂ - b₁) := by
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hxb : ∀ a u, |ξ a u| ≤ Real.sqrt d := abs_spin_le ξ hbound
  have hxs : ∀ a b u v, |ξ a u * ξ b v| ≤ d := abs_spin_mul_le ξ (Nat.cast_nonneg d) hbound
  set K : ℝ := b₂ * ((d : ℝ) * d * Dq * (4 * 2 * (2 + 1) * d * d) +
        (d : ℝ) * d * DA * (2 * (2 + 1) * d * d)) * (b₂ - b₁) with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ b₂ := hb₁.le.trans hb₁₂
    have : 0 ≤ b₂ - b₁ := sub_nonneg.2 hb₁₂
    positivity
  have key : ∀ F : (Fin 2 → α) → ℝ, Measurable F → (∀ σ, |F σ| ≤ d) →
      |(∫ y, skVectorFieldAvg μ ξ b₂ w.2 w.1 F y ∂(skVectorGaussLaw b₂ w.1)) -
        ∫ y, skVectorFieldAvg μ ξ b₁ w.2 w.1 F y ∂(skVectorGaussLaw b₁ w.1)| ≤ K :=
    fun F hF hFb => skVectorFieldAvg_beta_lipschitz μ ξ hξ hbound w.2 w.1 hw hDq hDA hq hA F hF hr
      hFb hb₁ hb₁₂
  have hF1 : ∀ u v, Measurable fun σ : Fin 2 → α => ξ (σ 0) u * ξ (σ 1) v := fun u v =>
    ((hξ u).comp (measurable_pi_apply 0)).mul ((hξ v).comp (measurable_pi_apply 1))
  have hF2 : ∀ u v, Measurable fun σ : Fin 2 → α => ξ (σ 0) u * ξ (σ 0) v := fun u v =>
    ((hξ u).comp (measurable_pi_apply 0)).mul ((hξ v).comp (measurable_pi_apply 0))
  rw [Prod.dist_eq]
  refine max_le ?_ ?_
  · refine (dist_pi_le_iff hK0).2 fun u => (dist_pi_le_iff hK0).2 fun v => ?_
    rw [Real.dist_eq, abs_sub_comm]
    exact key _ (hF1 u v) fun σ => hxs _ _ u v
  · refine (dist_pi_le_iff hK0).2 fun u => (dist_pi_le_iff hK0).2 fun v => ?_
    rw [Real.dist_eq, abs_sub_comm]
    exact key _ (hF2 u v) fun σ => hxs _ _ u v

/-- **The fixed point of (1.372)--(1.373) is Lipschitz in `β`** (for `18 β² d² < 1`):
if `z₁`, `z₂` are fixed points of `T_{b₁}`, `T_{b₂}` in the cone with `0 < b₁ ≤ b₂`, then
`dist z₁ z₂ ≤ d b₂ K₀ (b₂ - b₁)/(1 - 18 b₁² d²)`. -/
theorem skVectorFixedPoint_beta_dist_le {d : ℕ} (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → Fin d → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) {b₁ b₂ : ℝ} (hb₁ : 0 < b₁) (hb₁₂ : b₁ ≤ b₂)
    (hκ : 18 * b₁ ^ 2 * (d : ℝ) ^ 2 < 1)
    {z₁ z₂ : (Fin d → Fin d → ℝ) × (Fin d → Fin d → ℝ)} (hz₁ : z₁ ∈ skVectorFixedCone d)
    (hz₂ : z₂ ∈ skVectorFixedCone d) (hf₁ : skVectorFixedMap μ ξ b₁ z₁ = z₁)
    (hf₂ : skVectorFixedMap μ ξ b₂ z₂ = z₂) :
    dist z₁ z₂ ≤ d * (b₂ * ((d : ℝ) * d * d * (4 * 2 * (2 + 1) * d * d) +
        (d : ℝ) * d * (2 * d) * (2 * (2 + 1) * d * d)) * (b₂ - b₁)) /
      (1 - 18 * b₁ ^ 2 * (d : ℝ) ^ 2) := by
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  obtain ⟨hq2, hρ2⟩ := skVectorFixedPoint_sum_sq_le μ ξ hξ hbound b₂ hz₂ hf₂
  have hqb : ∀ u v, |z₂.1 u v| ≤ d := abs_entry_le_of_sum_sq_le z₂.1 hq2
  have hρb : ∀ u v, |z₂.2 u v| ≤ d := abs_entry_le_of_sum_sq_le z₂.2 hρ2
  have hAb : ∀ u v, |z₂.2 u v - z₂.1 u v| ≤ 2 * d := fun u v =>
    (abs_sub _ _).trans (by linarith [hqb u v, hρb u v])
  have h1 := skVectorFixedMap_frobDist_le μ ξ hξ hbound b₁ hz₁ hz₂
  have h2 := skVectorFixedMap_beta_dist_le μ ξ hξ hbound hz₂.1 (Dq := d) (DA := 2 * d) hr
    (by positivity) hqb hAb hb₁ hb₁₂
  rw [hf₁] at h1
  rw [hf₂] at h2
  have h2' := (skVectorFrobDist_le_mul_dist _ _).trans (mul_le_mul_of_nonneg_left h2 hr)
  set B : ℝ := d * (b₂ * ((d : ℝ) * d * d * (4 * 2 * (2 + 1) * d * d) +
      (d : ℝ) * d * (2 * d) * (2 * (2 + 1) * d * d)) * (b₂ - b₁)) with hB
  have h3 : skVectorFrobDist z₁ z₂ ≤ 18 * b₁ ^ 2 * (d : ℝ) ^ 2 * skVectorFrobDist z₁ z₂ + B := by
    calc skVectorFrobDist z₁ z₂ ≤ skVectorFrobDist z₁ (skVectorFixedMap μ ξ b₁ z₂) +
          skVectorFrobDist (skVectorFixedMap μ ξ b₁ z₂) z₂ := skVectorFrobDist_triangle _ _ _
      _ ≤ _ := add_le_add h1 h2'
  rw [le_div_iff₀ (by linarith)]
  have h4 : dist z₁ z₂ ≤ skVectorFrobDist z₁ z₂ := dist_le_skVectorFrobDist _ _
  nlinarith

end SpinGlasses
