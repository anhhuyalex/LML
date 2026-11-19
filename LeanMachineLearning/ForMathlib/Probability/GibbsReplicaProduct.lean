/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IteratedBound
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Tilted
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FreshReplicas
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FiniteTilted
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.BoundedTilted

/-!
# Replica Gibbs measures on an arbitrary base space

For a finite measure `μ` and a bounded energy `E`, the `ι`-fold product of the Gibbs measure
`μ.tilted E` is the Gibbs measure of the product base law with the energy summed over replicas.
This is the base-space-free analogue of the counting-measure replica API in
`SpinGlasses/Gibbs/GibbsReplicaMarginal.lean`.
-/

@[expose] public section

open MeasureTheory Finset
open scoped Topology

namespace MeasureTheory

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] {μ : Measure α} [IsFiniteMeasure μ]

/-- The finite replica base measure is nonzero whenever its common finite base measure is. -/
theorem neZero_measure_pi {α J : Type*} [MeasurableSpace α] [Fintype J] (μ : Measure α)
    [IsFiniteMeasure μ] [NeZero μ] : NeZero (Measure.pi fun _ : J => μ) :=
  ⟨fun h => by
    have := congrArg (fun m : Measure (J → α) => m Set.univ) h
    simp only [Measure.pi_univ, FunLike.coe_zero, Pi.zero_apply] at this
    rw [Finset.prod_eq_zero_iff] at this
    obtain ⟨i, -, hi⟩ := this
    exact (NeZero.ne μ) (Measure.measure_univ_eq_zero.mp hi)⟩

/-- The partition function of a product of replicas is the product of partition functions. -/
theorem integral_pi_exp_sum (E : α → ℝ) :
    ∫ σ : ι → α, Real.exp (∑ i, E (σ i)) ∂(Measure.pi fun _ => μ) =
      (∫ a, Real.exp (E a) ∂μ) ^ Fintype.card ι := by
  simp_rw [Real.exp_sum]
  exact integral_fintype_prod_eq_pow (fun a => Real.exp (E a))

/-- **Replica product of Gibbs measures.** The `ι`-fold product of `μ.tilted E` is the tilt of the
product base law by the energy summed over the replicas. -/
theorem pi_tilted_eq_tilted_pi {E : α → ℝ} :
    Measure.pi (fun _ : ι => μ.tilted E) =
      (Measure.pi fun _ : ι => μ).tilted (fun σ => ∑ i, E (σ i)) := by
  refine Measure.pi_eq (μ := fun _ : ι => μ.tilted E) fun s hs => ?_
  have hR : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hZ := integral_pi_exp_sum (μ := μ) (ι := ι) E
  set Z := ∫ b, Real.exp (E b) ∂μ with hZdef
  have hpt : ∀ σ : ι → α, Real.exp (∑ i, E (σ i)) / (Z ^ Fintype.card ι) =
      ∏ i, Real.exp (E (σ i)) / Z := by
    intro σ
    rw [Real.exp_sum, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
  rw [tilted_apply_eq_ofReal_integral, hZ]
  simp_rw [hpt]
  have hind : ∀ σ : ι → α, (Set.univ.pi s).indicator (fun σ => ∏ i, Real.exp (E (σ i)) / Z) σ =
      ∏ i, (s i).indicator (fun a => Real.exp (E a) / Z) (σ i) := by
    intro σ
    by_cases h : σ ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem h]
      exact Finset.prod_congr rfl fun i _ =>
        (Set.indicator_of_mem (h i (Set.mem_univ i)) (fun a => Real.exp (E a) / Z)).symm
    · rw [Set.indicator_of_notMem h]
      obtain ⟨i, hi⟩ : ∃ i, σ i ∉ s i := by
        by_contra hcon
        push Not at hcon
        exact h fun i _ => hcon i
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [← integral_indicator hR]
  simp_rw [hind]
  rw [integral_fintype_prod_eq_prod (fun i a => (s i).indicator (fun a => Real.exp (E a) / Z) a),
    ENNReal.ofReal_prod_of_nonneg]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [tilted_apply_eq_ofReal_integral, integral_indicator (hs i)]
  · intro i _
    refine integral_nonneg fun a => ?_
    by_cases ha : a ∈ s i
    · rw [Set.indicator_of_mem ha]
      exact div_nonneg (Real.exp_pos _).le (integral_nonneg fun b => (Real.exp_pos _).le)
    · rw [Set.indicator_of_notMem ha]
      exact le_rfl

/-- Adding an interaction to independent finite Gibbs laws gives the Gibbs law of the sum
of the one-site energies and the interaction, relative to counting measure. -/
theorem tilted_pi_count_tilted {A I : Type*} [Finite A] [Fintype I]
    [MeasurableSpace A] [MeasurableSingletonClass A] (f : A → ℝ) (E : (I → A) → ℝ) :
    (Measure.pi fun _ : I => Measure.count.tilted f).tilted E =
      Measure.count.tilted (fun σ => (∑ i, f (σ i)) + E σ) := by
  rw [pi_tilted_eq_tilted_pi, Measure.pi_count, tilted_tilted Integrable.of_finite]
  rfl

section Counting

variable {A I : Type*} [Fintype A] [Fintype I] [MeasurableSpace A]
  [MeasurableSingletonClass A]

/-- The partition integral relative to independent normalized Gibbs laws is a counting sum
divided by the product of the one-site normalizing sums. Empty site types are allowed. -/
theorem integral_exp_pi_count_tilted_eq_div [DecidableEq I] (f : A → ℝ) (E : (I → A) → ℝ) :
    (∫ σ, Real.exp (E σ) ∂(Measure.pi fun _ : I => Measure.count.tilted f)) =
      (∑ σ : I → A, Real.exp ((∑ i, f (σ i)) + E σ)) /
        (∑ a, Real.exp (f a)) ^ Fintype.card I := by
  rw [pi_tilted_eq_tilted_pi, Measure.pi_count, integral_exp_tilted,
    integral_count_eq_sum]
  congr 1
  rw [← Measure.pi_count]
  simpa only [integral_count_eq_sum] using
    integral_pi_exp_sum (μ := Measure.count) (ι := I) f

/-- Logarithmic form of the product-law partition normalization. The one-site normalizing
sum contributes once per site, without a restriction on the interaction or its sign. -/
theorem log_integral_exp_pi_count_tilted [DecidableEq I] [Nonempty A]
    (f : A → ℝ) (E : (I → A) → ℝ) :
    Real.log (∫ σ, Real.exp (E σ) ∂(Measure.pi fun _ : I => Measure.count.tilted f)) =
      Real.log (∑ σ : I → A, Real.exp ((∑ i, f (σ i)) + E σ)) -
        (Fintype.card I : ℝ) * Real.log (∑ a, Real.exp (f a)) := by
  rw [integral_exp_pi_count_tilted_eq_div,
    Real.log_div (by positivity) (by positivity), Real.log_pow]

end Counting

/-- The `ι`-replica Gibbs average of `Y` as a ratio of integrals against the product base law. -/
theorem integral_pi_tilted_eq_div (E : α → ℝ) (Y : (ι → α) → ℝ) :
    ∫ σ, Y σ ∂(Measure.pi fun _ : ι => μ.tilted E) =
      (∫ σ, Y σ * Real.exp (∑ i, E (σ i)) ∂(Measure.pi fun _ : ι => μ)) /
        ∫ σ, Real.exp (∑ i, E (σ i)) ∂(Measure.pi fun _ : ι => μ) := by
  rw [pi_tilted_eq_tilted_pi, integral_tilted_eq_div]

/-- Differentiate a bounded replica observable along a smooth energy path. A uniform upper
energy bound and an integrable bound on the energy derivative justify the exchange with all
replica integrals, including for a continuous base space and an empty replica index type.
The derivative is the covariance with the sum of the replica energy derivatives. -/
theorem hasDerivAt_integral_pi_tilted_of_dominated {α R : Type*} [MeasurableSpace α] [Fintype R]
    {μ : Measure α} [IsFiniteMeasure μ] [NeZero μ]
    {E E' : ℝ → α → ℝ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t)
    (hE : ∀ r ∈ s, Measurable (E r)) (hE' : Measurable (E' t))
    {B : ℝ} (hEb : ∀ r ∈ s, ∀ a, E r a ≤ B)
    {b : α → ℝ} (hb : Integrable b μ) (hdb : ∀ r ∈ s, ∀ a, |E' r a| ≤ b a)
    (hd : ∀ a, ∀ r ∈ s, HasDerivAt (fun q => E q a) (E' r a) r)
    {F : (R → α) → ℝ} (hF : Measurable F) {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) :
    HasDerivAt (fun r => ∫ σ, F σ ∂(Measure.pi fun _ : R => μ.tilted (E r)))
      ((∫ σ, F σ * (∑ i, E' t (σ i)) ∂(Measure.pi fun _ : R => μ.tilted (E t))) -
        (∫ σ, F σ ∂(Measure.pi fun _ : R => μ.tilted (E t))) *
          ∫ σ, (∑ i, E' t (σ i)) ∂(Measure.pi fun _ : R => μ.tilted (E t))) t := by
  let J := fun (r : ℝ) (σ : R → α) => ∑ i, E r (σ i)
  let J' := fun (r : ℝ) (σ : R → α) => ∑ i, E' r (σ i)
  have ht : t ∈ s := mem_of_mem_nhds hs
  have hJ (r : ℝ) (hr : r ∈ s) : Measurable (J r) := by
    dsimp only [J]
    fun_prop
  have hJ' : Measurable (J' t) := by
    dsimp only [J']
    fun_prop
  have hJb (r : ℝ) (hr : r ∈ s) (σ : R → α) : J r σ ≤ (Fintype.card R : ℝ) * B := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun i _ => hEb r hr (σ i))
  have hib : Integrable (fun σ : R → α => ∑ i, b (σ i)) (Measure.pi fun _ : R => μ) :=
    integrable_finsetSum _ fun i _ => integrable_comp_eval hb
  have hderb (r : ℝ) (hr : r ∈ s) (σ : R → α) : |J' r σ| ≤ ∑ i, b (σ i) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hdb r hr (σ i))
  have : NeZero (Measure.pi fun _ : R => μ) := neZero_measure_pi μ
  have hres := hasDerivAt_integral_tilted_of_bounded
    (μ := Measure.pi fun _ : R => μ) (E := J) (E' := J') hs hJ hJ' hJb hib
    hderb (fun σ r hr => HasDerivAt.fun_sum fun i _ => hd (σ i) r hr) hF hFb
  simpa only [J, J', ← pi_tilted_eq_tilted_pi] using hres

/-- **Fresh replicas factorize.** A function of the replicas `e i` (`e` injective) times a function
of one further replica `r` has the product of the two averages. -/
theorem integral_pi_fresh_replica_mul {I J : Type*} [Fintype I] [Fintype J] (ν : Measure α)
    [IsProbabilityMeasure ν] {e : I → J} (he : Function.Injective e) {r : J}
    (hr : ∀ i, e i ≠ r) (H : (I → α) → ℝ) (h : α → ℝ)
    (hH : AEStronglyMeasurable H (Measure.pi fun _ : I => ν)) (hh : AEStronglyMeasurable h ν) :
    ∫ σ : J → α, H (fun i => σ (e i)) * h (σ r) ∂(Measure.pi fun _ : J => ν) =
      (∫ ρ : I → α, H ρ ∂(Measure.pi fun _ : I => ν)) * ∫ a, h a ∂ν := by
  let ρ : I ⊕ Unit → J := Sum.elim e fun _ => r
  have hρ : Function.Injective ρ := by
    rintro (i | ⟨⟩) (j | ⟨⟩) hij
    · exact congrArg Sum.inl (he hij)
    · exact absurd hij (hr i)
    · exact absurd hij.symm (hr j)
    · rfl
  have hG : AEStronglyMeasurable (fun τ : I ⊕ Unit → α => H (fun i => τ (Sum.inl i)) *
      h (τ (Sum.inr ()))) (Measure.pi fun _ : I ⊕ Unit => ν) := by
    have hl := measurePreserving_pi_comp_injective ν (Sum.inl_injective (α := I) (β := Unit))
    exact (hH.comp_quasiMeasurePreserving hl.quasiMeasurePreserving).mul
      (hh.comp_quasiMeasurePreserving
        (measurePreserving_eval (fun _ : I ⊕ Unit => ν) (Sum.inr ())).quasiMeasurePreserving)
  have h1 := integral_pi_comp_injective ν hρ _ hG
  simp only [ρ, Sum.elim_inl, Sum.elim_inr] at h1
  rw [h1, integral_pi_sum_mul ν H (fun τ : Unit → α => h (τ ())) hH ?_]
  · congr 1
    have := integral_fintype_prod_eq_prod (ι := Unit) (fun _ => h) (μ := fun _ => ν)
    simpa using this
  · exact hh.comp_quasiMeasurePreserving
      (measurePreserving_eval (fun _ : Unit => ν) ()).quasiMeasurePreserving

/-- **One-replica marginal.** A function of a single replica of the product law has the average
of the replica law. -/
theorem integral_pi_eval (ν : Measure α) [IsProbabilityMeasure ν] {J : Type*} [Fintype J]
    (i : J) (h : α → ℝ) (hh : AEStronglyMeasurable h ν) :
    ∫ σ : J → α, h (σ i) ∂(Measure.pi fun _ : J => ν) = ∫ a, h a ∂ν :=
  integral_comp_eval hh

/-- The mean of a sum of copies of an integrable observable is the number of copies times
its one-state mean. No boundedness of the observable is required. -/
theorem integral_pi_sum_eval (ν : Measure α) [IsProbabilityMeasure ν] {J : Type*} [Fintype J]
    (h : α → ℝ) (hh : Integrable h ν) :
    ∫ σ : J → α, (∑ i, h (σ i)) ∂(Measure.pi fun _ : J => ν) =
      (Fintype.card J : ℝ) * ∫ a, h a ∂ν := by
  rw [integral_finsetSum _ fun i _ => integrable_comp_eval hh]
  simp_rw [integral_pi_eval ν _ h hh.aestronglyMeasurable]
  simp

/-- The replica difference operator `∑_i ⟨F h(σ_i)⟩ - |R| ⟨F h(σ_*)⟩`. -/
noncomputable def replicaDiff {α R : Type*} [MeasurableSpace α] [Fintype R] (ν : Measure α)
    (F : (R → α) → ℝ) (h : α → ℝ) : ℝ :=
  (∑ i, ∫ σ : Option R → α, F (fun j => σ (some j)) * h (σ (some i))
      ∂(Measure.pi fun _ : Option R => ν)) -
    (Fintype.card R : ℝ) * ∫ σ : Option R → α, F (fun j => σ (some j)) * h (σ none)
      ∂(Measure.pi fun _ : Option R => ν)

/-- The zero observable has zero replica difference. -/
theorem replicaDiff_zero {α R : Type*} [MeasurableSpace α] [Fintype R] (ν : Measure α)
    (F : (R → α) → ℝ) :
    replicaDiff ν F 0 = 0 := by
  dsimp only [replicaDiff]
  simp only [Pi.zero_apply, mul_zero, integral_zero, Finset.sum_const_zero, sub_zero, mul_zero]

/-- A covariance with a sum over the observed replicas is a sum of observed-replica terms
minus the cardinality times one fresh-replica term. The one-state observable only needs to be
integrable, so this also applies to energy derivatives containing Gaussian coordinates. -/
theorem integral_pi_cov_sum_eq_sum_sub_fresh {α R : Type*} [MeasurableSpace α] [Fintype R]
    (ν : Measure α)
    [IsProbabilityMeasure ν] (F : (R → α) → ℝ)
    (hF : AEStronglyMeasurable F (Measure.pi fun _ : R => ν))
    {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) (h : α → ℝ) (hh : Integrable h ν) :
    (∫ σ, F σ * (∑ i, h (σ i)) ∂(Measure.pi fun _ : R => ν)) -
      (∫ σ, F σ ∂(Measure.pi fun _ : R => ν)) *
        (∫ σ, (∑ i, h (σ i)) ∂(Measure.pi fun _ : R => ν)) =
    replicaDiff ν F h := by
  have hI (i : R) : Integrable (fun σ : R → α => h (σ i)) (Measure.pi fun _ : R => ν) :=
    integrable_comp_eval hh
  have hFI (i : R) := (hI i).bdd_mul hF (ae_of_all _ fun σ => by
    simpa only [Real.norm_eq_abs] using hFb σ)
  have hnum : (∫ σ, F σ * (∑ i, h (σ i)) ∂(Measure.pi fun _ : R => ν)) =
      ∑ i, ∫ σ : Option R → α, F (fun j => σ (some j)) * h (σ (some i))
        ∂(Measure.pi fun _ : Option R => ν) := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ fun i _ => hFI i]
    apply Finset.sum_congr rfl
    intro i _
    exact (integral_pi_comp_injective ν (Option.some_injective _)
      (fun σ : R → α => F σ * h (σ i)) (hFI i).aestronglyMeasurable).symm
  have hfresh := integral_pi_fresh_replica_mul ν (e := some) (Option.some_injective R)
    (r := none) (fun i => Option.some_ne_none i) F h hF hh.aestronglyMeasurable
  dsimp only [replicaDiff]
  rw [hnum, integral_pi_sum_eval ν h hh, hfresh]
  ring

/-- Additivity needs only one-state integrability of `h₁, h₂`, no product integrability. -/
theorem replicaDiff_add {α R : Type*} [MeasurableSpace α] [Fintype R] (ν : Measure α)
    [IsProbabilityMeasure ν] (F : (R → α) → ℝ)
    (hF : AEStronglyMeasurable F (Measure.pi fun _ : R => ν))
    {C : ℝ} (hFb : ∀ σ, |F σ| ≤ C) {h₁ h₂ : α → ℝ}
    (hh₁ : Integrable h₁ ν) (hh₂ : Integrable h₂ ν) :
    replicaDiff ν F (fun x => h₁ x + h₂ x) = replicaDiff ν F h₁ + replicaDiff ν F h₂ := by
  have hcov (h : α → ℝ) (hh : Integrable h ν) : replicaDiff ν F h =
      (∫ σ, F σ * (∑ i, h (σ i)) ∂(Measure.pi fun _ : R => ν)) -
      (∫ σ, F σ ∂(Measure.pi fun _ : R => ν)) *
        (∫ σ, (∑ i, h (σ i)) ∂(Measure.pi fun _ : R => ν)) :=
    (integral_pi_cov_sum_eq_sum_sub_fresh ν F hF hFb h hh).symm
  have hS (h : α → ℝ) (hh : Integrable h ν) : Integrable (fun σ : R → α => ∑ i, h (σ i))
      (Measure.pi fun _ : R => ν) := integrable_finsetSum _ fun i _ => integrable_comp_eval hh
  have hFS (h : α → ℝ) (hh : Integrable h ν) :
      Integrable (fun σ : R → α => F σ * ∑ i, h (σ i)) (Measure.pi fun _ : R => ν) := by
    simpa only [mul_comm] using (hS h hh).bdd_mul hF (ae_of_all _ fun σ => by
      simpa only [Real.norm_eq_abs] using hFb σ)
  rw [hcov (fun x => h₁ x + h₂ x) (hh₁.add hh₂), hcov _ hh₁, hcov _ hh₂]
  simp only [Finset.sum_add_distrib, mul_add]
  rw [integral_add (hFS h₁ hh₁) (hFS h₂ hh₂), integral_add (hS h₁ hh₁) (hS h₂ hh₂)]
  ring

/-- **The replica covariance identity.** For `Y` a function of the replicas `some o`
(`o : Option R`) and `h` a function of one spin, the covariance of `Y` with the sum of `h` over all
`|R| + 2` replicas is the sum over the replicas `some o` of `⟨Y h(σ_{some o})⟩`, minus
`(|R| + 1) ⟨Y⟩⟨h⟩`: the last replica is fresh. -/
theorem integral_replica_cov_identity {R : Type*} [Fintype R] (ν : Measure α)
    [IsProbabilityMeasure ν] (H : (Option R → α) → ℝ) (h : α → ℝ) (hH : Measurable H)
    {M B : ℝ} (hHb : ∀ τ, |H τ| ≤ M) (hh : Measurable h) (hhb : ∀ a, |h a| ≤ B) :
    (∫ σ : Option (Option R) → α, H (fun o => σ (some o)) * ∑ i, h (σ i)
        ∂(Measure.pi fun _ => ν)) -
      (∫ σ : Option (Option R) → α, H (fun o => σ (some o)) ∂(Measure.pi fun _ => ν)) *
        ∫ σ : Option (Option R) → α, ∑ i, h (σ i) ∂(Measure.pi fun _ => ν) =
    (∑ o : Option R, ∫ σ : Option (Option R) → α, H (fun o => σ (some o)) * h (σ (some o))
        ∂(Measure.pi fun _ => ν)) -
      (Fintype.card R + 1) * ((∫ τ : Option R → α, H τ ∂(Measure.pi fun _ => ν)) *
        ∫ a, h a ∂ν) := by
  set Y : (Option (Option R) → α) → ℝ := fun σ => H (fun o => σ (some o)) with hY
  have hYm : Measurable Y := hH.comp (by fun_prop)
  have hYb : ∀ σ, |Y σ| ≤ M := fun σ => hHb _
  have hhm : ∀ i : Option (Option R), Measurable fun σ : Option (Option R) → α => h (σ i) :=
    fun i => hh.comp (measurable_pi_apply i)
  have hbd : ∀ i (σ : Option (Option R) → α), |h (σ i)| ≤ B := fun i σ => hhb _
  have hI1 : ∀ i, Integrable (fun σ : Option (Option R) → α => Y σ * h (σ i))
      (Measure.pi fun _ => ν) := fun i =>
    integrable_of_measurable_bound (hYm.mul (hhm i)) (M := M * B) fun σ => by
      rw [abs_mul]
      exact mul_le_mul (hYb σ) (hhb _) (abs_nonneg _) ((abs_nonneg _).trans (hYb σ))
  have hfresh : ∫ σ : Option (Option R) → α, Y σ * h (σ none) ∂(Measure.pi fun _ => ν) =
      (∫ τ : Option R → α, H τ ∂(Measure.pi fun _ => ν)) * ∫ a, h a ∂ν :=
    integral_pi_fresh_replica_mul ν (e := fun o : Option R => some o) (Option.some_injective _)
      (fun _ => Option.some_ne_none _) H h hH.aestronglyMeasurable hh.aestronglyMeasurable
  have hY0 : ∫ σ : Option (Option R) → α, Y σ ∂(Measure.pi fun _ => ν) =
      ∫ τ : Option R → α, H τ ∂(Measure.pi fun _ => ν) :=
    integral_pi_comp_injective ν (Option.some_injective (Option R)) H hH.aestronglyMeasurable
  have hsum : ∫ σ : Option (Option R) → α, ∑ i, h (σ i) ∂(Measure.pi fun _ => ν) =
      (Fintype.card R + 2) * ∫ a, h a ∂ν := by
    rw [integral_pi_sum_eval ν h (integrable_of_measurable_bound hh hhb)]
    simp only [Fintype.card_option]
    push_cast
    ring
  have hexp : ∫ σ : Option (Option R) → α, Y σ * ∑ i, h (σ i) ∂(Measure.pi fun _ => ν) =
      (∫ σ : Option (Option R) → α, Y σ * h (σ none) ∂(Measure.pi fun _ => ν)) +
        ∑ o : Option R, ∫ σ : Option (Option R) → α, Y σ * h (σ (some o))
          ∂(Measure.pi fun _ => ν) := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ fun i _ => hI1 i, Fintype.sum_option]
  rw [hexp, hfresh, hY0, hsum]
  ring

/-- **The replica correction term.** The replica combination
`F · (∑ₐ h(σᵃ) - |R| h(σ^{n+1}))` has the average of `F ⟨h⟩`-centered products: the sum over the
replicas `some o` of `⟨F h(σ_{some o})⟩`, minus `(|R| + 1) ⟨F⟩⟨h⟩`. -/
theorem integral_replica_combination {R : Type*} [Fintype R] (ν : Measure α)
    [IsProbabilityMeasure ν] (F : (R → α) → ℝ) (h : α → ℝ) (hF : Measurable F)
    {M B : ℝ} (hFb : ∀ ρ, |F ρ| ≤ M) (hh : Measurable h) (hhb : ∀ a, |h a| ≤ B) :
    ∫ σ : Option (Option R) → α, (F fun a => σ (some (some a))) *
        (∑ a, h (σ (some (some a))) - Fintype.card R * h (σ (some none)))
        ∂(Measure.pi fun _ => ν) =
      (∑ o : Option R, ∫ σ : Option (Option R) → α, (F fun a => σ (some (some a))) *
          h (σ (some o)) ∂(Measure.pi fun _ => ν)) -
        (Fintype.card R + 1) * ((∫ ρ : R → α, F ρ ∂(Measure.pi fun _ => ν)) * ∫ a, h a ∂ν) := by
  set f : (Option (Option R) → α) → ℝ := fun σ => F fun a => σ (some (some a)) with hf
  have hfm : Measurable f := hF.comp (by fun_prop)
  have hhm : ∀ i : Option (Option R), Measurable fun σ : Option (Option R) → α => h (σ i) :=
    fun i => hh.comp (measurable_pi_apply i)
  have hfb : ∀ σ, |f σ| ≤ M := fun σ => hFb _
  have hI : ∀ i, Integrable (fun σ : Option (Option R) → α => f σ * h (σ i))
      (Measure.pi fun _ => ν) := fun i =>
    integrable_of_measurable_bound (hfm.mul (hhm i)) (M := M * B) fun σ => by
      rw [abs_mul]
      exact mul_le_mul (hfb σ) (hhb _) (abs_nonneg _) ((abs_nonneg _).trans (hfb σ))
  have hfresh : ∀ r : Option (Option R), (∀ a : R, some (some a) ≠ r) →
      ∫ σ : Option (Option R) → α, f σ * h (σ r) ∂(Measure.pi fun _ => ν) =
        (∫ ρ : R → α, F ρ ∂(Measure.pi fun _ => ν)) * ∫ a, h a ∂ν := fun r hr =>
    integral_pi_fresh_replica_mul ν (e := fun a : R => some (some a))
      (fun a b hab => Option.some_injective _ (Option.some_injective _ hab)) hr F h
      hF.aestronglyMeasurable hh.aestronglyMeasurable
  have h1 := hfresh (some none) fun a => by simp
  have hL : ∫ σ : Option (Option R) → α, f σ *
      (∑ a, h (σ (some (some a))) - Fintype.card R * h (σ (some none)))
        ∂(Measure.pi fun _ => ν) =
      (∑ a : R, ∫ σ : Option (Option R) → α, f σ * h (σ (some (some a)))
        ∂(Measure.pi fun _ => ν)) -
        Fintype.card R * ((∫ ρ : R → α, F ρ ∂(Measure.pi fun _ => ν)) * ∫ a, h a ∂ν) := by
    simp_rw [mul_sub, Finset.mul_sum]
    rw [integral_sub (integrable_finsetSum _ fun a _ => hI _),
      integral_finsetSum _ fun a _ => hI _]
    · congr 1
      rw [← h1, ← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun σ => by ring)
    · simpa only [mul_left_comm] using (hI (some none)).const_mul (Fintype.card R : ℝ)
  have hR : (∑ o : Option R, ∫ σ : Option (Option R) → α, f σ * h (σ (some o))
        ∂(Measure.pi fun _ => ν)) =
      (∫ ρ : R → α, F ρ ∂(Measure.pi fun _ => ν)) * (∫ a, h a ∂ν) +
        ∑ a : R, ∫ σ : Option (Option R) → α, f σ * h (σ (some (some a)))
          ∂(Measure.pi fun _ => ν) := by
    rw [Fintype.sum_option, h1]
  rw [hL, hR]
  ring

/-- The replica combination `F · (∑ₐ h(σᵃ) - |R| h(σ^{n+1}))` has the average of the covariance
of `F` with the sum of `h` over all replicas. -/
theorem integral_replica_combination_eq_cov {R : Type*} [Fintype R] (ν : Measure α)
    [IsProbabilityMeasure ν] (F : (R → α) → ℝ) (h : α → ℝ) (hF : Measurable F)
    {M B : ℝ} (hFb : ∀ ρ, |F ρ| ≤ M) (hh : Measurable h) (hhb : ∀ a, |h a| ≤ B) :
    ∫ σ : Option (Option R) → α, (F fun a => σ (some (some a))) *
        (∑ a, h (σ (some (some a))) - Fintype.card R * h (σ (some none)))
        ∂(Measure.pi fun _ => ν) =
      (∫ σ : Option (Option R) → α, (F fun a => σ (some (some a))) * ∑ i, h (σ i)
          ∂(Measure.pi fun _ => ν)) -
        (∫ σ : Option (Option R) → α, (F fun a => σ (some (some a))) ∂(Measure.pi fun _ => ν)) *
          ∫ σ : Option (Option R) → α, ∑ i, h (σ i) ∂(Measure.pi fun _ => ν) := by
  rw [integral_replica_combination ν F h hF hFb hh hhb,
    integral_replica_cov_identity ν (fun τ : Option R → α => F fun a => τ (some a)) h
      (hF.comp (by fun_prop)) (M := M) (fun τ => hFb _) hh hhb]
  have : ∫ ρ : R → α, F ρ ∂(Measure.pi fun _ : R => ν) =
      ∫ τ : Option R → α, F (fun a => τ (some a)) ∂(Measure.pi fun _ : Option R => ν) :=
    (integral_pi_comp_injective ν (Option.some_injective R) F hF.aestronglyMeasurable).symm
  rw [this]

/-- **The replica covariance identity in one integral.** The covariance of `Y = H(σ_{some ·})` with
the sum of `h` over all `|R| + 2` replicas is the average of `Y` times
`∑_{o} h(σ_{some o}) - (|R| + 1) h(σ_none)`. -/
theorem integral_replica_cov_identity' {R : Type*} [Fintype R] (ν : Measure α)
    [IsProbabilityMeasure ν] (H : (Option R → α) → ℝ) (h : α → ℝ) (hH : Measurable H)
    {M B : ℝ} (hHb : ∀ τ, |H τ| ≤ M) (hh : Measurable h) (hhb : ∀ a, |h a| ≤ B) :
    (∫ σ : Option (Option R) → α, H (fun o => σ (some o)) * ∑ i, h (σ i)
        ∂(Measure.pi fun _ => ν)) -
      (∫ σ : Option (Option R) → α, H (fun o => σ (some o)) ∂(Measure.pi fun _ => ν)) *
        ∫ σ : Option (Option R) → α, ∑ i, h (σ i) ∂(Measure.pi fun _ => ν) =
    ∫ σ : Option (Option R) → α, H (fun o => σ (some o)) *
      (∑ o : Option R, h (σ (some o)) - (Fintype.card R + 1) * h (σ none))
        ∂(Measure.pi fun _ => ν) := by
  rw [integral_replica_cov_identity ν H h hH hHb hh hhb]
  have hHm : Measurable fun σ : Option (Option R) → α => H (fun o => σ (some o)) :=
    hH.comp (measurable_pi_iff.2 fun o => measurable_pi_apply (some o))
  have hhm : ∀ i : Option (Option R), Measurable fun σ : Option (Option R) → α => h (σ i) :=
    fun i => hh.comp (measurable_pi_apply i)
  have hI : ∀ i, Integrable (fun σ : Option (Option R) → α => H (fun o => σ (some o)) * h (σ i))
      (Measure.pi fun _ => ν) := fun i =>
    integrable_of_measurable_bound (hHm.mul (hhm i)) (M := M * B) fun σ => by
      rw [abs_mul]
      exact mul_le_mul (hHb _) (hhb _) (abs_nonneg _)
        ((abs_nonneg _).trans (hHb fun o => σ (some o)))
  have hfresh : ∫ σ : Option (Option R) → α, H (fun o => σ (some o)) * h (σ none)
      ∂(Measure.pi fun _ => ν) =
      (∫ τ : Option R → α, H τ ∂(Measure.pi fun _ => ν)) * ∫ a, h a ∂ν :=
    integral_pi_fresh_replica_mul ν (e := fun o : Option R => some o) (Option.some_injective _)
      (fun _ => Option.some_ne_none _) H h hH.aestronglyMeasurable hh.aestronglyMeasurable
  simp_rw [mul_sub, Finset.mul_sum]
  rw [integral_sub (integrable_finsetSum _ fun o _ => hI _), integral_finsetSum _ fun o _ => hI _]
  · rw [show (∫ σ : Option (Option R) → α, H (fun o => σ (some o)) *
        ((Fintype.card R + 1) * h (σ none)) ∂(Measure.pi fun _ => ν)) =
        (Fintype.card R + 1) * ∫ σ : Option (Option R) → α, H (fun o => σ (some o)) * h (σ none)
          ∂(Measure.pi fun _ => ν) from by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun σ => by ring), hfresh]
  · simpa only [mul_left_comm] using (hI none).const_mul ((Fintype.card R : ℝ) + 1)

/-- The two-replica difference combination appearing in the cavity and smart-path derivatives
(Talagrand (2.24)--(2.25)):
`∑_{r < r'} U(σ^r, σ^{r'}) - n ∑_r U(σ^r, σ^{n+1}) + n(n+1)/2 U(σ^{n+1}, σ^{n+2})`. -/
noncomputable def replicaPairDiff {R α : Type*} [Fintype R] [LinearOrder R]
    (U : α → α → ℝ) (τ : Option (Option R) → α) : ℝ :=
  (∑ p : R × R with p.1 < p.2, U (τ (some (some p.1))) (τ (some (some p.2)))) -
    (Fintype.card R : ℝ) * (∑ r : R, U (τ (some (some r))) (τ (some none))) +
    (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) / 2 * U (τ (some none)) (τ none)

theorem replicaPairDiff_const_mul {R α : Type*} [Fintype R] [LinearOrder R]
    (c : ℝ) (U : α → α → ℝ) (τ : Option (Option R) → α) :
    replicaPairDiff (fun a b => c * U a b) τ = c * replicaPairDiff U τ := by
  simp only [replicaPairDiff, mul_sub, mul_add, ← Finset.mul_sum]
  ring

theorem replicaPairDiff_add {R α : Type*} [Fintype R] [LinearOrder R]
    (U₁ U₂ : α → α → ℝ) (τ : Option (Option R) → α) :
    replicaPairDiff (fun a b => U₁ a b + U₂ a b) τ =
      replicaPairDiff U₁ τ + replicaPairDiff U₂ τ := by
  simp only [replicaPairDiff, Finset.sum_add_distrib]
  ring

theorem replicaPairDiff_sum {R α ι : Type*} [Fintype R] [LinearOrder R] [Fintype ι]
    (U : ι → α → α → ℝ) (τ : Option (Option R) → α) :
    replicaPairDiff (fun a b => ∑ k, U k a b) τ =
      ∑ k, replicaPairDiff (U k) τ := by
  dsimp only [replicaPairDiff]
  simp only [Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_comm
    (s := Finset.filter (fun p : R × R => p.1 < p.2) Finset.univ) (t := Finset.univ)]
  congr 1
  congr 1
  rw [Finset.sum_comm (s := (Finset.univ : Finset R)) (t := Finset.univ)]

/-- The replica average of `F` against the pair combination of the kernel `U`; the two-fresh-replica
analogue of `replicaDiff`. -/
noncomputable def replicaPairAverage {R α : Type*} [MeasurableSpace α] [Fintype R]
    [LinearOrder R] (ν : Measure α) (F : (R → α) → ℝ) (U : α → α → ℝ) : ℝ :=
  ∫ τ : Option (Option R) → α, F (fun r => τ (some (some r))) * replicaPairDiff U τ
    ∂(Measure.pi fun _ => ν)

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Measurability of a replica Gibbs average in the random environment.** The energy and
observable may both depend jointly measurably on the environment. -/
theorem measurable_integral_pi_tilted {E : Ω → α → ℝ} (hE : Measurable fun p : Ω × α => E p.1 p.2)
    {G : Ω → (ι → α) → ℝ} (hG : Measurable fun p : Ω × (ι → α) => G p.1 p.2) :
    Measurable fun ω => ∫ σ, G ω σ ∂(Measure.pi fun _ : ι => μ.tilted (E ω)) := by
  simp_rw [pi_tilted_eq_tilted_pi]
  have hJ : Measurable fun p : Ω × (ι → α) => ∑ i, E p.1 (p.2 i) :=
    Finset.measurable_sum _ fun i _ => hE.comp (measurable_fst.prodMk
      ((measurable_pi_apply i).comp measurable_snd))
  exact measurable_integral_tilted_dep hJ hG

/-- A uniformly bounded, jointly measurable replica observable has an integrable Gibbs average
in the environment. Its dependence on the environment may be shared with the energy. -/
theorem integrable_integral_pi_tilted {E : Ω → α → ℝ}
    (hE : Measurable fun p : Ω × α => E p.1 p.2)
    (hprob : ∀ ω, IsProbabilityMeasure (μ.tilted (E ω))) {P : Measure Ω} [IsFiniteMeasure P]
    {G : Ω → (ι → α) → ℝ} (hG : Measurable fun p : Ω × (ι → α) => G p.1 p.2)
    {M : ℝ} (hGb : ∀ ω σ, |G ω σ| ≤ M) :
    Integrable (fun ω => ∫ σ, G ω σ ∂(Measure.pi fun _ : ι => μ.tilted (E ω))) P := by
  refine (integrable_const M).mono' (measurable_integral_pi_tilted hE hG).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have := hprob ω
  have := norm_integral_le_of_norm_le_const (μ := Measure.pi fun _ : ι => μ.tilted (E ω))
    (f := G ω) (C := M) (Filter.Eventually.of_forall fun σ => by simpa using hGb ω σ)
  simpa using this

omit [IsFiniteMeasure μ] in
/-- A uniform bound on a function of the disorder and replicas bounds its disorder-averaged
Gibbs average. The observable may depend on the same disorder as the energy. -/
theorem abs_integral_integral_pi_tilted_le {E : Ω → α → ℝ}
    (hprob : ∀ ω, IsProbabilityMeasure (μ.tilted (E ω))) {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Ω → (ι → α) → ℝ} {C : ℝ} (hG : ∀ ω σ, |G ω σ| ≤ C) :
    |∫ ω, ∫ σ, G ω σ ∂(Measure.pi fun _ : ι => μ.tilted (E ω)) ∂P| ≤ C := by
  have := hprob
  exact abs_integral_integral_le_of_forall_abs_le P
    (fun ω => Measure.pi fun _ : ι => μ.tilted (E ω)) G hG

end Measurability

/-- Integral of a nine-term linear combination of integrable functions. -/
theorem integral_nine_combination {β : Type*} [MeasurableSpace β] {m : Measure β}
    {g₁ g₂ g₃ g₄ g₅ g₆ g₇ g₈ g₉ : β → ℝ} (h₁ : Integrable g₁ m) (h₂ : Integrable g₂ m)
    (h₃ : Integrable g₃ m) (h₄ : Integrable g₄ m) (h₅ : Integrable g₅ m) (h₆ : Integrable g₆ m)
    (h₇ : Integrable g₇ m) (h₈ : Integrable g₈ m) (h₉ : Integrable g₉ m) (c₃ c₄ c₅ c₆ c₉ : ℝ) :
    ∫ x, (g₁ x + g₂ x - c₃ * g₃ x - c₄ * g₄ x - c₅ * g₅ x + c₆ * g₆ x - g₇ x - g₈ x +
        c₉ * g₉ x) ∂m =
      (∫ x, g₁ x ∂m) + (∫ x, g₂ x ∂m) - c₃ * ∫ x, g₃ x ∂m - c₄ * ∫ x, g₄ x ∂m -
        c₅ * ∫ x, g₅ x ∂m + c₆ * ∫ x, g₆ x ∂m - (∫ x, g₇ x ∂m) - (∫ x, g₈ x ∂m) +
        c₉ * ∫ x, g₉ x ∂m := by
  have e3 := h₃.const_mul c₃
  have e4 := h₄.const_mul c₄
  have e5 := h₅.const_mul c₅
  have e6 := h₆.const_mul c₆
  have e9 := h₉.const_mul c₉
  have hfun : (fun x => g₁ x + g₂ x - c₃ * g₃ x - c₄ * g₄ x - c₅ * g₅ x + c₆ * g₆ x - g₇ x -
      g₈ x + c₉ * g₉ x) = g₁ + g₂ - (fun x => c₃ * g₃ x) - (fun x => c₄ * g₄ x) -
        (fun x => c₅ * g₅ x) + (fun x => c₆ * g₆ x) - g₇ - g₈ + (fun x => c₉ * g₉ x) := by
    ext x; simp
  rw [hfun, integral_add' (((((((h₁.add h₂).sub e3).sub e4).sub e5).add e6).sub h₇).sub h₈) e9,
    integral_sub' ((((((h₁.add h₂).sub e3).sub e4).sub e5).add e6).sub h₇) h₈,
    integral_sub' (((((h₁.add h₂).sub e3).sub e4).sub e5).add e6) h₇,
    integral_add' ((((h₁.add h₂).sub e3).sub e4).sub e5) e6,
    integral_sub' (((h₁.add h₂).sub e3).sub e4) e5,
    integral_sub' ((h₁.add h₂).sub e3) e4, integral_sub' (h₁.add h₂) e3, integral_add' h₁ h₂,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul]

/-- Integral of a four-term linear combination of integrable functions. -/
theorem integral_four_combination {β : Type*} [MeasurableSpace β] {m : Measure β}
    {g₁ g₂ g₃ g₄ : β → ℝ} (h₁ : Integrable g₁ m) (h₂ : Integrable g₂ m) (h₃ : Integrable g₃ m)
    (h₄ : Integrable g₄ m) :
    ∫ x, (g₁ x - g₂ x - g₃ x + g₄ x) ∂m =
      (∫ x, g₁ x ∂m) - (∫ x, g₂ x ∂m) - (∫ x, g₃ x ∂m) + ∫ x, g₄ x ∂m := by
  have hfun : (fun x => g₁ x - g₂ x - g₃ x + g₄ x) = g₁ - g₂ - g₃ + g₄ := by ext x; simp
  rw [hfun, integral_add' ((h₁.sub h₂).sub h₃) h₄, integral_sub' (h₁.sub h₂) h₃,
    integral_sub' h₁ h₂]

section Exchangeability

variable {J : Type*} [Fintype J] (ν : Measure α) [IsProbabilityMeasure ν]

/-- **Exchangeability of pairs of replicas.** A function of two distinct replicas of an i.i.d.
family has the same average for every choice of the two replicas. -/
theorem integral_pi_pair_eq {x y x' y' : J} (hxy : x ≠ y) (hxy' : x' ≠ y') (φ : α → α → ℝ)
    (hφ : Measurable fun p : α × α => φ p.1 p.2) :
    ∫ σ : J → α, φ (σ x) (σ y) ∂(Measure.pi fun _ : J => ν) =
      ∫ σ : J → α, φ (σ x') (σ y') ∂(Measure.pi fun _ : J => ν) := by
  have hm : Measurable fun τ : Fin 2 → α => φ (τ 0) (τ 1) :=
    Measurable.comp (g := fun p : α × α => φ p.1 p.2) (f := fun τ : Fin 2 → α => (τ 0, τ 1)) hφ
      ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1))
  have key : ∀ {a b : J}, a ≠ b → ∫ σ : J → α, φ (σ a) (σ b) ∂(Measure.pi fun _ : J => ν) =
      ∫ τ : Fin 2 → α, φ (τ 0) (τ 1) ∂(Measure.pi fun _ : Fin 2 => ν) := by
    intro a b hab
    have hρ : Function.Injective (![a, b] : Fin 2 → J) := by
      intro u v huv
      fin_cases u <;> fin_cases v <;> simp_all [Ne.symm hab]
    simpa using integral_pi_comp_injective ν hρ (fun τ : Fin 2 → α => φ (τ 0) (τ 1))
      hm.aestronglyMeasurable
  rw [key hxy, key hxy']

/-- **Exchangeability of single replicas.** -/
theorem integral_pi_diag_eq {x x' : J} (φ : α → α → ℝ)
    (hφ : Measurable fun p : α × α => φ p.1 p.2) :
    ∫ σ : J → α, φ (σ x) (σ x) ∂(Measure.pi fun _ : J => ν) =
      ∫ σ : J → α, φ (σ x') (σ x') ∂(Measure.pi fun _ : J => ν) := by
  have hm : Measurable fun a : α => φ a a :=
    Measurable.comp (g := fun p : α × α => φ p.1 p.2) (f := fun a : α => (a, a)) hφ
      (measurable_id.prodMk measurable_id)
  rw [integral_pi_eval ν x (fun a => φ a a) hm.aestronglyMeasurable,
    integral_pi_eval ν x' (fun a => φ a a) hm.aestronglyMeasurable]

end Exchangeability

section ReplicaSymmetry

variable {R : Type*} [Fintype R] [DecidableEq R] (ν : Measure α) [IsProbabilityMeasure ν]
  (F : (R → α) → ℝ)

omit [DecidableEq R] in
/-- **Exchanging the two fresh replicas.** For `F` a function of the old replicas, a kernel
`K(σ_a, σ_{n+1})` can be moved to `K(σ_a, σ_{n+2})`; this is the replica symmetry used to
reach the form (1.376). -/
theorem integral_replica_swap_fresh (hF : Measurable F) {K : α → α → ℝ}
    (hK : Measurable fun p : α × α => K p.1 p.2) (a : R) :
    ∫ σ : Option (Option R) → α, (F fun c => σ (some (some c))) * K (σ (some (some a))) (σ none)
        ∂(Measure.pi fun _ => ν) =
      ∫ σ : Option (Option R) → α, (F fun c => σ (some (some c))) *
        K (σ (some (some a))) (σ (some none)) ∂(Measure.pi fun _ => ν) := by
  classical
  let e : Option R → Option (Option R) := fun o => Option.elim o none fun c => some (some c)
  have he : Function.Injective e := by
    rintro (_ | a) (_ | b) h <;> simp_all [e]
  have hx₀ : ∀ o, e o ≠ some none := by
    rintro (_ | a) <;> simp [e]
  have hFm : Measurable fun τ : Option R → α => F fun c => τ (some c) :=
    hF.comp (measurable_pi_iff.2 fun c => measurable_pi_apply (some c))
  have hm : AEStronglyMeasurable (fun σ : Option R → α => (F fun c => σ (some c)) *
      K (σ (some a)) (σ none)) (Measure.pi fun _ : Option R => ν) :=
    (hFm.mul (hK.comp ((measurable_pi_apply (some a)).prodMk
      (measurable_pi_apply none)))).aestronglyMeasurable
  exact integral_pi_replace_replica ν (e := e) (i := some a) (k := none) he hx₀
    (Option.some_ne_none a) (fun τ => F fun c => τ (some c))
    (fun σ x => by simp [Function.update_of_ne]) K hm

/-- **The replica pattern of Eq. (1.376).** For a symmetric bounded kernel `H` and a bounded
function `C`, the average of `F` times the bilinear replica combination of `H` minus the
`C`-combination is the combination of averages appearing in Proposition 1.12.4 (with the diagonal
`C` merged into the old-old terms). -/
theorem integral_replica_pattern (hF : Measurable F) {M : ℝ} (hFb : ∀ ρ, |F ρ| ≤ M)
    {H : α → α → ℝ} (hH : Measurable fun p : α × α => H p.1 p.2) {BH : ℝ}
    (hHb : ∀ x y, |H x y| ≤ BH) (hHs : ∀ x y, H x y = H y x)
    {C : α → ℝ} (hC : Measurable C) {BC : ℝ} (hCb : ∀ x, |C x| ≤ BC) :
    ∫ σ : Option (Option R) → α, (F fun c => σ (some (some c))) *
        (((∑ a, ∑ o : Option R, H (σ (some (some a))) (σ (some o))) -
          (Fintype.card R + 1) * ∑ a, H (σ (some (some a))) (σ none) -
          Fintype.card R * ∑ o : Option R, H (σ (some none)) (σ (some o)) +
          Fintype.card R * (Fintype.card R + 1) * H (σ (some none)) (σ none)) -
        (∑ o : Option R, C (σ (some o)) - (Fintype.card R + 1) * C (σ none)))
        ∂(Measure.pi fun _ => ν) =
      (∑ a, ∑ b, ∫ σ : Option (Option R) → α, (F fun c => σ (some (some c))) *
          (H (σ (some (some a))) (σ (some (some b))) -
            if a = b then C (σ (some (some a))) else 0) ∂(Measure.pi fun _ => ν)) -
        2 * Fintype.card R * ∑ a, ∫ σ : Option (Option R) → α,
          (F fun c => σ (some (some c))) * H (σ (some (some a))) (σ (some none))
            ∂(Measure.pi fun _ => ν) -
        Fintype.card R * ∫ σ : Option (Option R) → α, (F fun c => σ (some (some c))) *
          (H (σ (some none)) (σ (some none)) - C (σ (some none))) ∂(Measure.pi fun _ => ν) +
        Fintype.card R * (Fintype.card R + 1) * ∫ σ : Option (Option R) → α,
          (F fun c => σ (some (some c))) * H (σ (some none)) (σ none)
            ∂(Measure.pi fun _ => ν) := by
  set f : (Option (Option R) → α) → ℝ := fun σ => F fun c => σ (some (some c)) with hf
  have hfm : Measurable f := hF.comp (measurable_pi_iff.2 fun c => measurable_pi_apply _)
  have hfb : ∀ σ, |f σ| ≤ M := fun σ => hFb _
  have hHm : ∀ x y : Option (Option R), Measurable fun σ : Option (Option R) → α =>
      H (σ x) (σ y) := fun x y =>
    Measurable.comp (g := fun p : α × α => H p.1 p.2)
      (f := fun σ : Option (Option R) → α => (σ x, σ y)) hH
      ((measurable_pi_apply x).prodMk (measurable_pi_apply y))
  have hI2 : ∀ x y : Option (Option R), Integrable (fun σ : Option (Option R) → α =>
      f σ * H (σ x) (σ y)) (Measure.pi fun _ => ν) := fun x y =>
    integrable_of_measurable_bound (hfm.mul (hHm x y)) (M := M * BH) fun σ => by
      rw [abs_mul]
      exact mul_le_mul (hfb σ) (hHb _ _) (abs_nonneg _) ((abs_nonneg _).trans (hfb σ))
  have hI1 : ∀ x : Option (Option R), Integrable (fun σ : Option (Option R) → α =>
      f σ * C (σ x)) (Measure.pi fun _ => ν) := fun x =>
    integrable_of_measurable_bound (hfm.mul (hC.comp (measurable_pi_apply x)))
      (M := M * BC) fun σ => by
      rw [abs_mul]
      exact mul_le_mul (hfb σ) (hCb _) (abs_nonneg _) ((abs_nonneg _).trans (hfb σ))
  have hdec : ∀ σ : Option (Option R) → α, f σ * (((∑ a, ∑ o : Option R,
        H (σ (some (some a))) (σ (some o))) -
          (Fintype.card R + 1) * ∑ a, H (σ (some (some a))) (σ none) -
          Fintype.card R * ∑ o : Option R, H (σ (some none)) (σ (some o)) +
          Fintype.card R * (Fintype.card R + 1) * H (σ (some none)) (σ none)) -
        (∑ o : Option R, C (σ (some o)) - (Fintype.card R + 1) * C (σ none))) =
      (∑ a, ∑ b, f σ * H (σ (some (some a))) (σ (some (some b)))) +
        (∑ a, f σ * H (σ (some (some a))) (σ (some none))) -
        (Fintype.card R + 1) * ∑ a, f σ * H (σ (some (some a))) (σ none) -
        Fintype.card R * ∑ b, f σ * H (σ (some none)) (σ (some (some b))) -
        Fintype.card R * (f σ * H (σ (some none)) (σ (some none))) +
        Fintype.card R * (Fintype.card R + 1) * (f σ * H (σ (some none)) (σ none)) -
        (∑ b, f σ * C (σ (some (some b)))) - f σ * C (σ (some none)) +
        (Fintype.card R + 1) * (f σ * C (σ none)) := by
    intro σ
    simp only [Fintype.sum_option, Finset.sum_add_distrib, mul_sub, mul_add, Finset.mul_sum,
      mul_left_comm (f σ)]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hdec)]
  have hsum2 : ∀ (a : R) (y : Option (Option R)), ∀ g : R → Option (Option R),
      Integrable (fun σ : Option (Option R) → α => ∑ b, f σ * H (σ (g b)) (σ y))
        (Measure.pi fun _ => ν) := fun a y g => integrable_finsetSum _ fun b _ => hI2 _ _
  rw [integral_nine_combination
    (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hI2 _ _)
    (integrable_finsetSum _ fun a _ => hI2 _ _) (integrable_finsetSum _ fun a _ => hI2 _ _)
    (integrable_finsetSum _ fun a _ => hI2 _ _) (hI2 _ _) (hI2 _ _)
    (integrable_finsetSum _ fun a _ => hI1 _) (hI1 _) (hI1 _)]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hI2 _ _]
  simp_rw [integral_finsetSum _ fun a _ => hI2 _ _, integral_finsetSum _ fun a _ => hI1 _]
  -- the two exchanges of fresh replicas and the symmetry of the kernel
  have hswap : ∀ a : R, ∫ σ : Option (Option R) → α, f σ * H (σ (some (some a))) (σ none)
      ∂(Measure.pi fun _ => ν) = ∫ σ : Option (Option R) → α,
        f σ * H (σ (some (some a))) (σ (some none)) ∂(Measure.pi fun _ => ν) := fun a =>
    integral_replica_swap_fresh ν F hF hH a
  have hsymm : ∀ b : R, ∫ σ : Option (Option R) → α, f σ * H (σ (some none)) (σ (some (some b)))
      ∂(Measure.pi fun _ => ν) = ∫ σ : Option (Option R) → α,
        f σ * H (σ (some (some b))) (σ (some none)) ∂(Measure.pi fun _ => ν) := fun b =>
    integral_congr_ae (Filter.Eventually.of_forall fun σ => by simp only [hHs (σ (some none))])
  have hfresh : ∀ r : Option (Option R), (∀ c : R, some (some c) ≠ r) →
      ∫ σ : Option (Option R) → α, f σ * C (σ r) ∂(Measure.pi fun _ => ν) =
        (∫ ρ : R → α, F ρ ∂(Measure.pi fun _ => ν)) * ∫ a, C a ∂ν := fun r hr =>
    integral_pi_fresh_replica_mul ν (e := fun c : R => some (some c))
      (fun a b hab => Option.some_injective _ (Option.some_injective _ hab)) hr F C
      hF.aestronglyMeasurable hC.aestronglyMeasurable
  have hC1 : ∫ σ : Option (Option R) → α, f σ * C (σ none) ∂(Measure.pi fun _ => ν) =
      ∫ σ : Option (Option R) → α, f σ * C (σ (some none)) ∂(Measure.pi fun _ => ν) := by
    rw [hfresh none (fun c => by simp), hfresh (some none) (fun c => by simp)]
  have hdiag : ∀ a : R, ∑ b, ∫ σ : Option (Option R) → α, f σ *
        (H (σ (some (some a))) (σ (some (some b))) - if a = b then C (σ (some (some a))) else 0)
        ∂(Measure.pi fun _ => ν) = (∑ b, ∫ σ : Option (Option R) → α,
          f σ * H (σ (some (some a))) (σ (some (some b))) ∂(Measure.pi fun _ => ν)) -
          ∫ σ : Option (Option R) → α, f σ * C (σ (some (some a))) ∂(Measure.pi fun _ => ν) := by
    intro a
    have hite : ∀ b : R, ∫ σ : Option (Option R) → α, f σ *
        (H (σ (some (some a))) (σ (some (some b))) - if a = b then C (σ (some (some a))) else 0)
        ∂(Measure.pi fun _ => ν) = (∫ σ : Option (Option R) → α,
          f σ * H (σ (some (some a))) (σ (some (some b))) ∂(Measure.pi fun _ => ν)) -
          if a = b then ∫ σ : Option (Option R) → α, f σ * C (σ (some (some a)))
            ∂(Measure.pi fun _ => ν) else 0 := by
      intro b
      by_cases hab : a = b
      · simp only [hab, ite_true, mul_sub]
        rw [integral_sub (hI2 _ _) (hI1 _)]
      · simp [hab]
    simp only [hite, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have h00 : ∫ σ : Option (Option R) → α, f σ * (H (σ (some none)) (σ (some none)) -
      C (σ (some none))) ∂(Measure.pi fun _ => ν) =
      (∫ σ : Option (Option R) → α, f σ * H (σ (some none)) (σ (some none))
        ∂(Measure.pi fun _ => ν)) -
        ∫ σ : Option (Option R) → α, f σ * C (σ (some none)) ∂(Measure.pi fun _ => ν) := by
    simp only [mul_sub]
    exact integral_sub (hI2 _ _) (hI1 _)
  simp only [hf] at hswap hsymm hC1 hdiag h00 ⊢
  simp only [hdiag, hswap, hsymm, hC1, h00, Finset.sum_sub_distrib]
  ring

end ReplicaSymmetry

section Bounded

variable {β : Type*}

/-- The class of uniformly bounded functions is closed under the operations used to build
observables (sums, differences, products, constants); a bound is only claimed to exist. -/
theorem exists_abs_le_add {f g : β → ℝ} (hf : ∃ B, ∀ x, |f x| ≤ B) (hg : ∃ B, ∀ x, |g x| ≤ B) :
    ∃ B, ∀ x, |f x + g x| ≤ B := by
  obtain ⟨B₁, h₁⟩ := hf
  obtain ⟨B₂, h₂⟩ := hg
  exact ⟨B₁ + B₂, fun x => (abs_add_le _ _).trans (add_le_add (h₁ x) (h₂ x))⟩

theorem exists_abs_le_sub {f g : β → ℝ} (hf : ∃ B, ∀ x, |f x| ≤ B) (hg : ∃ B, ∀ x, |g x| ≤ B) :
    ∃ B, ∀ x, |f x - g x| ≤ B := by
  obtain ⟨B₁, h₁⟩ := hf
  obtain ⟨B₂, h₂⟩ := hg
  exact ⟨B₁ + B₂, fun x => (abs_sub _ _).trans (add_le_add (h₁ x) (h₂ x))⟩

theorem exists_abs_le_mul {f g : β → ℝ} (hf : ∃ B, ∀ x, |f x| ≤ B) (hg : ∃ B, ∀ x, |g x| ≤ B) :
    ∃ B, ∀ x, |f x * g x| ≤ B := by
  obtain ⟨B₁, h₁⟩ := hf
  obtain ⟨B₂, h₂⟩ := hg
  exact ⟨B₁ * B₂, fun x => by
    rw [abs_mul]
    exact mul_le_mul (h₁ x) (h₂ x) (abs_nonneg _) ((abs_nonneg _).trans (h₁ x))⟩

theorem exists_abs_le_const (c : ℝ) : ∃ B, ∀ _ : β, |c| ≤ B := ⟨|c|, fun _ => le_rfl⟩

theorem exists_abs_le_sum {ι : Type*} (s : Finset ι) {f : ι → β → ℝ}
    (hf : ∀ i ∈ s, ∃ B, ∀ x, |f i x| ≤ B) : ∃ B, ∀ x, |∑ i ∈ s, f i x| ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun x => by simp⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact exists_abs_le_add (hf a (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end Bounded

end MeasureTheory
