/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsCavityPath
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.BoundedTilted

/-!
# The cavity derivative for a replica Gibbs average

`GibbsCavityPath.lean` differentiates the expected Gibbs average of one observable `f` on a
single base space. Here the observable is a function `F` of `|R|` replicas, and the replica
bookkeeping of Eq. (1.376) is carried out: the base space is `Option (Option R) → α` (the old
replicas `some (some a)` and two fresh ones `some none` and `none`), the energy is summed over
all replicas, and the covariance `⟨Y_k X_l⟩ - ⟨Y_k⟩⟨X_l⟩` is rewritten by
`integral_replica_cov_identity` as a combination of averages over `|R| + 1` replicas.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Finset
open scoped BigOperators

namespace MeasureTheory

theorem neZero_measure_pi {α J : Type*} [MeasurableSpace α] [Fintype J] (μ : Measure α)
    [IsFiniteMeasure μ] [NeZero μ] : NeZero (Measure.pi fun _ : J => μ) :=
  ⟨fun h => by
    have := congrArg (fun m : Measure (J → α) => m Set.univ) h
    simp only [Measure.pi_univ, FunLike.coe_zero, Pi.zero_apply] at this
    rw [Finset.prod_eq_zero_iff] at this
    obtain ⟨i, -, hi⟩ := this
    exact (NeZero.ne μ) (Measure.measure_univ_eq_zero.mp hi)⟩

/-- The Gibbs measure `μ.tilted g` is a probability measure when the energy `g` is bounded and
measurable. -/
theorem isProbabilityMeasure_tilted_of_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] [NeZero μ] {g : α → ℝ} (hg : Measurable g) {Eb : ℝ}
    (hb : ∀ a, |g a| ≤ Eb) : IsProbabilityMeasure (μ.tilted g) :=
  isProbabilityMeasure_tilted_of_ae_le hg.aemeasurable
    (Filter.Eventually.of_forall fun a => (le_abs_self _).trans (hb a))

variable {α K Ks R : Type*} [MeasurableSpace α] [Fintype K] [Fintype Ks] [Fintype R]
  {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ]

/-- **The cavity derivative of a replica Gibbs average** (Proposition 1.12.4, before the
overlap algebra). For `F` a bounded measurable function of the replicas `R` and the Gibbs measure
`ν_{r,ω} = μ.tilted (D + ∑ₖ sₖ(r) Zₖ(ω) Xₖ + ∑ⱼ cⱼ(r) X'ⱼ)` of the energy, the derivative of
`r ↦ 𝔼 ⟨F⟩_{r}` is the Gaussian covariance sum of the single-replica statement, with `Yₖ` the
replica combination `F · (∑ₐ Xₖ(σᵃ) - |R| Xₖ(σ^{n+1}))`, and covariances rewritten over the
replicas `Option R`. -/
theorem hasDerivAt_integral_gibbs_replica_cavity_path {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : α → ℝ} {X : K → α → ℝ} {Xs : Ks → α → ℝ}
    {F : (R → α) → ℝ} {Eb B M : ℝ}
    (hD : Measurable D) (hX : ∀ k, Measurable (X k)) (hXs : ∀ j, Measurable (Xs j))
    (hF : Measurable F) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hDb : ∀ a, |D a| ≤ Eb) (hXb : ∀ k a, |X k a| ≤ B) (hXsb : ∀ j a, |Xs j a| ≤ B)
    (hFb : ∀ σ, |F σ| ≤ M)
    {Z : K → Ω → ℝ} (hZ : HasGaussianLaw (fun ω k => Z k ω) P) (hZm : ∀ k, Measurable (Z k))
    (hmean : ∀ k, ∫ ω, Z k ω ∂P = 0)
    {s s' : K → ℝ → ℝ} {c c' : Ks → ℝ → ℝ} {t δ C : ℝ} (hδ : 0 < δ)
    (hs : ∀ k, ∀ r ∈ Metric.ball t δ, HasDerivAt (s k) (s' k r) r)
    (hc : ∀ j, ∀ r ∈ Metric.ball t δ, HasDerivAt (c j) (c' j r) r)
    (hsC : ∀ k, ∀ r ∈ Metric.ball t δ, |s' k r| ≤ C)
    (hcC : ∀ j, ∀ r ∈ Metric.ball t δ, |c' j r| ≤ C)
    (hsz : ∀ k, s' k t = 0 ∨ s k t ≠ 0) :
    HasDerivAt (fun r => ∫ ω, ∫ σ : R → α, F σ ∂(Measure.pi fun _ : R => μ.tilted
        fun a => D a + ∑ k, s k r * Z k ω * X k a + ∑ j, c j r * Xs j a) ∂P)
      (∑ k, ∑ l, s' k t * s l t * (∫ ω, Z k ω * Z l ω ∂P) * ∫ ω,
          ∫ σ : Option (Option R) → α, (F fun a => σ (some (some a))) *
              (∑ a, X k (σ (some (some a))) - Fintype.card R * X k (σ (some none))) *
            (∑ o : Option R, X l (σ (some o)) - (Fintype.card R + 1) * X l (σ none))
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted
              fun a => D a + ∑ k', s k' t * Z k' ω * X k' a + ∑ j', c j' t * Xs j' a) ∂P +
        ∑ j, c' j t * ∫ ω,
          ∫ σ : Option (Option R) → α, (F fun a => σ (some (some a))) *
              (∑ o : Option R, Xs j (σ (some o)) - (Fintype.card R + 1) * Xs j (σ none))
            ∂(Measure.pi fun _ : Option (Option R) => μ.tilted
              fun a => D a + ∑ k', s k' t * Z k' ω * X k' a + ∑ j', c j' t * Xs j' a) ∂P) t := by
  classical
  set μB : Measure (Option (Option R) → α) := Measure.pi fun _ => μ with hμB
  have : NeZero μB := neZero_measure_pi μ
  set cJ : ℝ := (Fintype.card (Option (Option R)) : ℝ) with hcJ
  set DB : (Option (Option R) → α) → ℝ := fun σ => ∑ i, D (σ i) with hDB
  set XB : K → (Option (Option R) → α) → ℝ := fun k σ => ∑ i, X k (σ i) with hXB
  set XsB : Ks → (Option (Option R) → α) → ℝ := fun j σ => ∑ i, Xs j (σ i) with hXsB
  set fB : (Option (Option R) → α) → ℝ := fun σ => F fun a => σ (some (some a)) with hfB
  set Yk : K → (Option (Option R) → α) → ℝ := fun k σ =>
    fB σ * (∑ a, X k (σ (some (some a))) - Fintype.card R * X k (σ (some none))) with hYk
  set Rr : ((Option (Option R) → α) → ℝ) → (K ⊕ Ks → ℝ) → ℝ := fun Y' z =>
    (∫ σ, Y' σ * Real.exp (DB σ + ∑ l, z l * Sum.elim XB XsB l σ) ∂μB) /
      ∫ σ, Real.exp (DB σ + ∑ l, z l * Sum.elim XB XsB l σ) ∂μB with hRr
  set gz : (K ⊕ Ks → ℝ) → α → ℝ := fun z a => D a + ∑ l, z l * Sum.elim X Xs l a with hgz
  have hsumb : ∀ (g : α → ℝ) (b : ℝ), (∀ a, |g a| ≤ b) → ∀ σ : Option (Option R) → α,
      |∑ i, g (σ i)| ≤ cJ * b := by
    intro g b hg σ
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |g (σ i)| ≤ ∑ _i : Option (Option R), b := Finset.sum_le_sum fun i _ => hg _
      _ = cJ * b := by simp [hcJ]
  have hmeassum : ∀ g : α → ℝ, Measurable g → Measurable fun σ : Option (Option R) → α =>
      ∑ i, g (σ i) := fun g hg =>
    Finset.measurable_sum _ fun i _ => hg.comp (measurable_pi_apply i)
  have hXall : ∀ l, Measurable (Sum.elim X Xs l) := by
    intro l; rcases l with k | j
    · exact hX k
    · exact hXs j
  have hXallb : ∀ l a, |Sum.elim X Xs l a| ≤ B := by
    intro l a; rcases l with k | j
    · exact hXb k a
    · exact hXsb j a
  have hgzm : ∀ z, Measurable (gz z) := fun z =>
    hD.add (Finset.measurable_sum _ fun l _ => (hXall l).const_mul _)
  have hgzb : ∀ z, ∀ a, |gz z a| ≤ Eb + ∑ l, |z l| * B := by
    intro z a
    refine (abs_add_le _ _).trans (add_le_add (hDb a) ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hXallb l a) (abs_nonneg _)
  have hprob : ∀ z, IsProbabilityMeasure (μ.tilted (gz z)) := fun z =>
    isProbabilityMeasure_tilted_of_bound (hgzm z) (hgzb z)
  have hXallB : ∀ (l : K ⊕ Ks) (σ : Option (Option R) → α),
      Sum.elim XB XsB l σ = ∑ i, Sum.elim X Xs l (σ i) := by
    intro l σ; rcases l with k | j <;> rfl
  have hexp : ∀ z σ, DB σ + ∑ l, z l * Sum.elim XB XsB l σ = ∑ i, gz z (σ i) := by
    intro z σ
    simp only [hXallB, hDB, hgz, Finset.mul_sum, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
  have hRint : ∀ z Y', Rr Y' z = ∫ σ, Y' σ ∂(Measure.pi fun _ : Option (Option R) =>
      μ.tilted (gz z)) := by
    intro z Y'
    rw [integral_pi_tilted_eq_div]
    simp only [hRr, hexp]
    rfl
  have hfBm : Measurable fB := hF.comp (by fun_prop)
  have hXcomp : ∀ (k : K) (i : Option (Option R)), Measurable fun σ : Option (Option R) → α =>
      X k (σ i) := fun k i => (hX k).comp (measurable_pi_apply i)
  have hHm : ∀ k, Measurable fun τ : Option R → α => (F fun a => τ (some a)) *
      (∑ a, X k (τ (some a)) - Fintype.card R * X k (τ none)) := fun k =>
    (hF.comp (by fun_prop)).mul ((Finset.measurable_sum _ fun a _ =>
      (hX k).comp (measurable_pi_apply _)).sub (((hX k).comp (measurable_pi_apply _)).const_mul _))
  have hHb : ∀ (k : K) (τ : Option R → α), |(F fun a => τ (some a)) *
      (∑ a, X k (τ (some a)) - Fintype.card R * X k (τ none))| ≤
        M * (Fintype.card R * B + Fintype.card R * B) := by
    intro k τ
    rw [abs_mul]
    refine mul_le_mul (hFb _) ?_ (abs_nonneg _) hM
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ a, |X k (τ (some a))| ≤ ∑ _a : R, B := Finset.sum_le_sum fun a _ => hXb _ _
        _ = Fintype.card R * B := by simp
    · rw [abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (hXb _ _) (Nat.cast_nonneg _)
  have hYm : ∀ k, Measurable (Yk k) := fun k =>
    (hHm k).comp (show Measurable
      (fun (σ : Option (Option R) → α) (o : Option R) => σ (some o)) from
      measurable_pi_iff.2 fun o => measurable_pi_apply (some o))
  have hYb : ∀ k σ, |Yk k σ| ≤ M * (Fintype.card R * B + Fintype.card R * B) :=
    fun k σ => hHb k fun o => σ (some o)
  have hYk' : ∀ k z, Rr (Yk k) z = Rr (fun σ => fB σ * XB k σ) z - Rr fB z * Rr (XB k) z := by
    intro k z
    have := hprob z
    rw [hRint, hRint, hRint, hRint]
    exact integral_replica_combination_eq_cov (μ.tilted (gz z)) F (X k) hF hFb (hX k) (hXb k)
  have hmain := hasDerivAt_integral_gibbs_cavity_path (μ := μB) (D := DB) (X := XB) (Xs := XsB)
    (f := fB) (Y := Yk) (Eb := cJ * Eb) (B := cJ * B) (M := M)
    (M' := M * (Fintype.card R * B + Fintype.card R * B)) Rr (fun Y' z => rfl)
    (hmeassum D hD) (fun k => hmeassum _ (hX k)) (fun j => hmeassum _ (hXs j)) hfBm hYm
    (mul_nonneg (Nat.cast_nonneg _) hB) hM (by positivity)
    (fun σ => hsumb D Eb hDb σ) (fun k σ => hsumb _ B (hXb k) σ)
    (fun j σ => hsumb _ B (hXsb j) σ) (fun σ => hFb _) hYb hYk' hZ hZm hmean hδ hs hc hsC hcC hsz
  set zp : ℝ → Ω → K ⊕ Ks → ℝ := fun r ω => Sum.elim (fun k => s k r * Z k ω) (fun j => c j r)
    with hzp
  have hgeq : ∀ r ω, gz (zp r ω) =
      fun a => D a + ∑ k, s k r * Z k ω * X k a + ∑ j, c j r * Xs j a := by
    intro r ω
    funext a
    simp only [hgz, hzp, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, add_assoc]
  have hFR : ∀ (ν : Measure α) [IsProbabilityMeasure ν],
      ∫ σ : Option (Option R) → α, fB σ ∂(Measure.pi fun _ => ν) =
        ∫ ρ : R → α, F ρ ∂(Measure.pi fun _ => ν) := fun ν _ =>
    integral_pi_comp_injective ν (ρ := fun a : R => some (some a))
      (fun a b hab => Option.some_injective _ (Option.some_injective _ hab)) F
      hF.aestronglyMeasurable
  have hfun : (fun r => ∫ ω, ∫ σ : R → α, F σ ∂(Measure.pi fun _ : R => μ.tilted
        fun a => D a + ∑ k, s k r * Z k ω * X k a + ∑ j, c j r * Xs j a) ∂P) =
      fun r => ∫ ω, Rr fB (zp r ω) ∂P := by
    funext r
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have := hprob (zp r ω)
    simp only
    rw [hRint, hFR, hgeq]
  rw [hfun]
  refine hmain.congr_deriv ?_
  congr 1
  · refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have hpr := hprob (zp t ω)
    beta_reduce
    rw [hRint, hRint, hRint, hgeq]
    rw [hgeq] at hpr
    have := hpr
    exact integral_replica_cov_identity' (μ.tilted _) _ (X l) (hHm k) (hHb k) (hX l) (hXb l)
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have hpr := hprob (zp t ω)
    beta_reduce
    rw [hRint, hRint, hRint, hgeq]
    rw [hgeq] at hpr
    have := hpr
    exact integral_replica_cov_identity'
      (μ.tilted fun a => D a + ∑ k', s k' t * Z k' ω * X k' a + ∑ j', c j' t * Xs j' a)
      (fun τ : Option R → α => F fun a => τ (some a)) (Xs j)
      (hF.comp (measurable_pi_iff.2 fun a => measurable_pi_apply (some a))) (M := M)
      (fun τ => hFb _) (hXs j) (hXsb j)

/-- **Continuity of the expected replica Gibbs average along an interpolation.**  If the
coefficients `sₖ`, `cⱼ` are continuous then
`r ↦ 𝔼 ⟨F⟩_r` is continuous (no differentiability of the coefficients is needed, so this covers the
endpoints of the cavity path where `√t` and `√(1 - t)` are not differentiable). -/
theorem continuous_integral_gibbs_replica_path {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {D : α → ℝ} {X : K → α → ℝ} {Xs : Ks → α → ℝ}
    {F : (R → α) → ℝ} {Eb B M : ℝ}
    (hD : Measurable D) (hX : ∀ k, Measurable (X k)) (hXs : ∀ j, Measurable (Xs j))
    (hF : Measurable F) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hDb : ∀ a, |D a| ≤ Eb) (hXb : ∀ k a, |X k a| ≤ B) (hXsb : ∀ j a, |Xs j a| ≤ B)
    (hFb : ∀ σ, |F σ| ≤ M) {Z : K → Ω → ℝ} (hZm : ∀ k, Measurable (Z k))
    {s : K → ℝ → ℝ} {c : Ks → ℝ → ℝ} (hs : ∀ k, Continuous (s k)) (hc : ∀ j, Continuous (c j)) :
    Continuous (fun r => ∫ ω, ∫ σ : R → α, F σ ∂(Measure.pi fun _ : R => μ.tilted
        fun a => D a + ∑ k, s k r * Z k ω * X k a + ∑ j, c j r * Xs j a) ∂P) := by
  classical
  set cR : ℝ := (Fintype.card R : ℝ) with hcR
  set μB : Measure (R → α) := Measure.pi fun _ => μ with hμB
  have : NeZero μB := neZero_measure_pi μ
  set DB : (R → α) → ℝ := fun σ => ∑ i, D (σ i) with hDB
  set XB : K → (R → α) → ℝ := fun k σ => ∑ i, X k (σ i) with hXB
  set XsB : Ks → (R → α) → ℝ := fun j σ => ∑ i, Xs j (σ i) with hXsB
  set gz : (K ⊕ Ks → ℝ) → α → ℝ := fun z a => D a + ∑ l, z l * Sum.elim X Xs l a with hgz
  have hsumb : ∀ (g : α → ℝ) (b : ℝ), (∀ a, |g a| ≤ b) → ∀ σ : R → α,
      |∑ i, g (σ i)| ≤ cR * b := by
    intro g b hg σ
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |g (σ i)| ≤ ∑ _i : R, b := Finset.sum_le_sum fun i _ => hg _
      _ = cR * b := by simp [hcR]
  have hmeassum : ∀ g : α → ℝ, Measurable g → Measurable fun σ : R → α => ∑ i, g (σ i) :=
    fun g hg => Finset.measurable_sum _ fun i _ => hg.comp (measurable_pi_apply i)
  have hXall : ∀ l, Measurable (Sum.elim X Xs l) := by
    intro l; rcases l with k | j
    · exact hX k
    · exact hXs j
  have hXallb : ∀ l a, |Sum.elim X Xs l a| ≤ B := by
    intro l a; rcases l with k | j
    · exact hXb k a
    · exact hXsb j a
  have hgzm : ∀ z, Measurable (gz z) := fun z =>
    hD.add (Finset.measurable_sum _ fun l _ => (hXall l).const_mul _)
  have hgzb : ∀ z, ∀ a, |gz z a| ≤ Eb + ∑ l, |z l| * B := by
    intro z a
    refine (abs_add_le _ _).trans (add_le_add (hDb a) ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hXallb l a) (abs_nonneg _)
  have hXallB : ∀ (l : K ⊕ Ks) (σ : R → α),
      Sum.elim XB XsB l σ = ∑ i, Sum.elim X Xs l (σ i) := by
    intro l σ; rcases l with k | j <;> rfl
  have hexp : ∀ z σ, DB σ + ∑ l, z l * Sum.elim XB XsB l σ = ∑ i, gz z (σ i) := by
    intro z σ
    simp only [hXallB, hDB, hgz, Finset.mul_sum, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
  set Rr : ((R → α) → ℝ) → (K ⊕ Ks → ℝ) → ℝ := fun Y' z =>
    (∫ σ, Y' σ * Real.exp (DB σ + ∑ l, z l * Sum.elim XB XsB l σ) ∂μB) /
      ∫ σ, Real.exp (DB σ + ∑ l, z l * Sum.elim XB XsB l σ) ∂μB with hRr
  have hRint : ∀ z, Rr F z = ∫ σ, F σ ∂(Measure.pi fun _ : R => μ.tilted (gz z)) := by
    intro z
    rw [integral_pi_tilted_eq_div]
    simp only [hRr, hexp]
    rfl
  have hBB : 0 ≤ cR * B := mul_nonneg (Nat.cast_nonneg _) hB
  have hcont : Continuous (Rr F) :=
    continuous_gibbs_ratio_linear (μ := μB) (K := K ⊕ Ks) (X := Sum.elim XB XsB) (D := DB)
      (Eb := cR * Eb) (B := cR * B) (M := M) Rr (fun _ _ => rfl) (hmeassum D hD)
      (by rintro (k | j)
          · exact hmeassum _ (hX k)
          · exact hmeassum _ (hXs j)) hF hBB hM
      (fun σ => hsumb D Eb hDb σ)
      (by rintro (k | j) σ
          · exact hsumb _ B (hXb k) σ
          · exact hsumb _ B (hXsb j) σ) hFb
  set zp : ℝ → Ω → K ⊕ Ks → ℝ := fun r ω => Sum.elim (fun k => s k r * Z k ω) (fun j => c j r)
    with hzp
  have hgeq : ∀ r ω, gz (zp r ω) =
      fun a => D a + ∑ k, s k r * Z k ω * X k a + ∑ j, c j r * Xs j a := by
    intro r ω
    funext a
    simp only [hgz, hzp, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, add_assoc]
  have hprob : ∀ z, IsProbabilityMeasure (μ.tilted (gz z)) := fun z =>
    isProbabilityMeasure_tilted_of_bound (hgzm z) (hgzb z)
  have hzm : ∀ r, Measurable (zp r) := by
    intro r
    refine measurable_pi_iff.2 fun l => ?_
    rcases l with k | j
    · simpa [hzp] using (hZm k).const_mul (s k r)
    · simp [hzp]
  have hfun : (fun r => ∫ ω, ∫ σ : R → α, F σ ∂(Measure.pi fun _ : R => μ.tilted
        fun a => D a + ∑ k, s k r * Z k ω * X k a + ∑ j, c j r * Xs j a) ∂P) =
      fun r => ∫ ω, Rr F (zp r ω) ∂P := by
    funext r
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    beta_reduce
    rw [hRint, hgeq]
  rw [hfun]
  refine continuous_of_dominated (bound := fun _ => M) (fun r => ?_) (fun r => ?_)
    (integrable_const M) (Filter.Eventually.of_forall fun ω => ?_)
  · exact (hcont.measurable.comp (hzm r)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs]
    have := abs_gibbs_ratio_le (μ := μB) (K := K ⊕ Ks) (X := Sum.elim XB XsB) (D := DB)
      (Eb := cR * Eb) (B := cR * B) (Y := F) (M := M) (hmeassum D hD) (by
        rintro (k | j)
        · exact hmeassum _ (hX k)
        · exact hmeassum _ (hXs j)) (fun σ => hsumb D Eb hDb σ) (by
        rintro (k | j) σ
        · exact hsumb _ B (hXb k) σ
        · exact hsumb _ B (hXsb j) σ) hFb (zp r ω)
    simpa [hRr] using this
  · refine hcont.comp ?_
    refine continuous_pi fun l => ?_
    rcases l with k | j
    · exact (hs k).mul continuous_const
    · exact hc j

end MeasureTheory
