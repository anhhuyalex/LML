/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianSteinRatio
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianGram
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProdFactorization
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.BoundedTilted

/-!
# Gaussian integration by parts for replica averages with potential energy

Model-free Gaussian integration by parts (Stein's identity) for a replica Gibbs average whose
energy is `u` applied to a Gaussian field `S(q) = α_sh(π a) ⬝ᵥ w + α_aux(π a) ⬝ᵥ η` with a shared
standard Gaussian vector `w` and per-replica auxiliary standard Gaussian vectors `η`. This is the
shared analytical engine behind:

1. Talagrand Section 2.3, Lemma 2.3.2 (the fixed-angle integration by parts (2.52)--(2.58),
   requiring only bounded `u, u', u'', u'''` without continuity of `u'''`);
2. Talagrand Section 2.3, Exercise 2.3.3 (the one-step time-derivative formula from (2.60)).

## Main declarations

* `SpinGlasses.stein_ratio_fixed_spins`: first-order Stein ratio identity at fixed spin labels;
* `SpinGlasses.stein_tilted_replica_ratio`: first-order Stein identity integrated over an
  arbitrary old-state probability law `μ₀` and an integrable `R`-replica observable `f`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SpinGlasses

private lemma hasFDerivAt_Z_sum {L K_aux : Type*} [Fintype L] [DecidableEq L] [Fintype K_aux]
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) {B D₁ : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (p : L → ℝ) (hp : ∀ m, 0 ≤ p m) (hp1 : ∑ m, p m = 1) (c : L → K_aux → ℝ) :
    let γ_aux := Measure.pi fun _ : K_aux => gaussianReal 0 1
    let Z : (L → ℝ) → ℝ := fun y =>
      ∑ m : L, p m * ∫ η, Real.exp (u (y m + c m ⬝ᵥ η)) ∂γ_aux
    Differentiable ℝ Z ∧
      (∀ y, Real.exp (-B) ≤ Z y) ∧
      (∀ m y, fderiv ℝ Z y (Pi.single m 1) =
        p m * ∫ η, deriv u (y m + c m ⬝ᵥ η) * Real.exp (u (y m + c m ⬝ᵥ η)) ∂γ_aux) ∧
      (∀ m y, |fderiv ℝ Z y (Pi.single m 1)| ≤ p m * (|D₁| * Real.exp B)) := by
  intro γ_aux Z
  have hum : Measurable u := hu.continuous.measurable
  have hdum : Measurable (deriv u) := measurable_deriv u
  have hlinm : ∀ (m : L) (t : ℝ), Measurable fun η : K_aux → ℝ => t + c m ⬝ᵥ η := fun m t => by
    simp only [dotProduct]; fun_prop
  have hexpi : ∀ (m : L) (t : ℝ), Integrable (fun η => Real.exp (u (t + c m ⬝ᵥ η))) γ_aux :=
    fun m t => Integrable.of_bound (C := Real.exp B)
      (Real.measurable_exp.comp (hum.comp (hlinm m t))).aestronglyMeasurable
      (ae_of_all _ fun η => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (le_of_abs_le (hB _)))
  have hterm : ∀ (m : L) (y : L → ℝ),
      HasFDerivAt (fun y' : L → ℝ => ∫ η, Real.exp (u (y' m + c m ⬝ᵥ η)) ∂γ_aux)
        ((∫ η, deriv u (y m + c m ⬝ᵥ η) * Real.exp (u (y m + c m ⬝ᵥ η)) ∂γ_aux) •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : L => ℝ) m) y := by
    intro m y
    have hscalar : HasDerivAt (fun t : ℝ => ∫ η, Real.exp (u (t + c m ⬝ᵥ η)) ∂γ_aux)
        (∫ η, deriv u (y m + c m ⬝ᵥ η) * Real.exp (u (y m + c m ⬝ᵥ η)) ∂γ_aux) (y m) := by
      refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ_aux)
        (F := fun t η => Real.exp (u (t + c m ⬝ᵥ η)))
        (F' := fun t η => deriv u (t + c m ⬝ᵥ η) * Real.exp (u (t + c m ⬝ᵥ η)))
        (s := Set.univ) Filter.univ_mem
        (Filter.Eventually.of_forall fun t =>
          (Real.measurable_exp.comp (hum.comp (hlinm m t))).aestronglyMeasurable)
        (hexpi m (y m))
        ((hdum.comp (hlinm m (y m))).mul
          (Real.measurable_exp.comp (hum.comp (hlinm m (y m))))).aestronglyMeasurable
        (bound := fun _ => |D₁| * Real.exp B)
        (ae_of_all _ fun η t _ => by
          rw [Real.norm_eq_abs]
          exact abs_mul_exp_le ((hD₁ _).trans (le_abs_self _)) (le_of_abs_le (hB _)))
        (integrable_const _)
        (ae_of_all _ fun η t _ => by
          have h1 : HasDerivAt (fun t : ℝ => t + c m ⬝ᵥ η) 1 t :=
            (hasDerivAt_id t).add_const _
          have h2 := ((hu _).hasDerivAt.comp t h1).exp
          simpa [mul_comm] using h2)).2
    exact hscalar.comp_hasFDerivAt y
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : L => ℝ) m).hasFDerivAt
  have hZd : ∀ y : L → ℝ, HasFDerivAt Z
      (∑ m : L, p m • ((∫ η, deriv u (y m + c m ⬝ᵥ η) * Real.exp (u (y m + c m ⬝ᵥ η)) ∂γ_aux) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : L => ℝ) m)) y := fun y =>
    HasFDerivAt.fun_sum fun m _ => (hterm m y).const_smul (p m)
  refine ⟨fun y => (hZd y).differentiableAt, ?_, ?_, ?_⟩
  · intro y
    have hlow : ∀ m : L, Real.exp (-B) ≤ ∫ η, Real.exp (u (y m + c m ⬝ᵥ η)) ∂γ_aux := fun m => by
      have hm := integral_mono (integrable_const (Real.exp (-B))) (hexpi m (y m))
        fun η => Real.exp_le_exp.2 (neg_le_of_abs_le (hB _))
      simpa [γ_aux] using hm
    calc Real.exp (-B) = (∑ m : L, p m) * Real.exp (-B) := by rw [hp1, one_mul]
      _ = ∑ m : L, p m * Real.exp (-B) := Finset.sum_mul _ _ _
      _ ≤ ∑ m : L, p m * ∫ η, Real.exp (u (y m + c m ⬝ᵥ η)) ∂γ_aux :=
          Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hlow m) (hp m)
  · intro m y
    rw [(hZd y).fderiv]
    simp [Pi.single_apply, mul_comm (p m)]
  · intro m y
    rw [(hZd y).fderiv]
    simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, abs_mul, abs_of_nonneg (hp m)]
    refine mul_le_mul_of_nonneg_left ?_ (hp m)
    have hb := norm_integral_le_of_norm_le_const (μ := γ_aux)
      (f := fun η => deriv u (y m + c m ⬝ᵥ η) * Real.exp (u (y m + c m ⬝ᵥ η)))
      (C := |D₁| * Real.exp B) (ae_of_all _ fun η => by
        rw [Real.norm_eq_abs]
        exact abs_mul_exp_le ((hD₁ _).trans (le_abs_self _)) (le_of_abs_le (hB _)))
    simpa [γ_aux] using hb

private lemma hasFDerivAt_prod_ϕ {R : Type*} [Fintype R] [DecidableEq R]
    (ϕ : R → ℝ → ℝ) (hϕ : ∀ r, Differentiable ℝ (ϕ r))
    {M M' : R → ℝ} (hM : ∀ r x, |ϕ r x| ≤ M r) (hM' : ∀ r x, |deriv (ϕ r) x| ≤ M' r) :
    let F : (R → ℝ) → ℝ := fun x => ∏ r, ϕ r (x r)
    Differentiable ℝ F ∧
      (∀ x, |F x| ≤ ∏ r, |M r|) ∧
      (∀ j x, fderiv ℝ F x (Pi.single j 1) =
        deriv (ϕ j) (x j) * ∏ r ∈ Finset.univ.erase j, ϕ r (x r)) ∧
      (∀ j x, |fderiv ℝ F x (Pi.single j 1)| ≤
        |M' j| * ∏ r ∈ Finset.univ.erase j, |M r|) := by
  intro F
  have hterm : ∀ (r : R) (x : R → ℝ),
      HasFDerivAt (fun x' : R → ℝ => ϕ r (x' r))
        (deriv (ϕ r) (x r) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : R => ℝ) r) x :=
    fun r x => (hϕ r (x r)).hasDerivAt.comp_hasFDerivAt x
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : R => ℝ) r).hasFDerivAt
  have hFd : ∀ x : R → ℝ, HasFDerivAt F
      (∑ j : R, (∏ r ∈ Finset.univ.erase j, ϕ r (x r)) •
        (deriv (ϕ j) (x j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : R => ℝ) j)) x :=
    fun x => HasFDerivAt.finsetProd fun r _ => hterm r x
  refine ⟨fun x => (hFd x).differentiableAt, ?_, ?_, ?_⟩
  · intro x
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => (hM r _).trans (le_abs_self _)
  · intro j x
    rw [(hFd x).fderiv]
    simp [Pi.single_apply, mul_comm]
  · intro j x
    rw [(hFd x).fderiv]
    simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, abs_mul, Finset.abs_prod]
    rw [mul_comm]
    exact mul_le_mul ((hM' j _).trans (le_abs_self _))
      (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => (hM r _).trans (le_abs_self _))
      (Finset.prod_nonneg fun _ _ => abs_nonneg _) (abs_nonneg _)

/-- **First-order Gaussian integration by parts of a normalized replica ratio at fixed spin
labels.** -/
theorem stein_ratio_fixed_spins
    {L K_sh K_aux R : Type*} [Fintype L] [Nonempty L]
    [Fintype K_sh] [Fintype K_aux] [Fintype R] [DecidableEq R]
    (p : L → ℝ) (hp : ∀ m, 0 ≤ p m) (hp1 : ∑ m, p m = 1)
    (α_sh W_sh : L → K_sh → ℝ) (α_aux W_aux : L → K_aux → ℝ)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) {B D₁ : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (ϕ : R → ℝ → ℝ) (hϕ : ∀ r, Differentiable ℝ (ϕ r))
    {M M' : R → ℝ} (hM : ∀ r x, |ϕ r x| ≤ M r) (hM' : ∀ r x, |deriv (ϕ r) x| ≤ M' r)
    (i₀ : R) (s : R → L) :
    let γ_sh := Measure.pi fun _ : K_sh => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : K_aux => gaussianReal 0 1
    let Z (w : K_sh → ℝ) : ℝ :=
      ∑ m : L, p m * ∫ η, Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η)) ∂γ_aux
    ∫ w, (∫ η : R → K_aux → ℝ,
        (W_sh (s i₀) ⬝ᵥ w + W_aux (s i₀) ⬝ᵥ η i₀) *
          (∏ r, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r))
        ∂(Measure.pi fun _ : R => γ_aux)) / Z w ^ Fintype.card R ∂γ_sh =
      ∑ j : R, (W_sh (s i₀) ⬝ᵥ α_sh (s j) +
          if i₀ = j then W_aux (s i₀) ⬝ᵥ α_aux (s j) else 0) *
        ∫ w, (∫ η : R → K_aux → ℝ,
          deriv (ϕ j) (α_sh (s j) ⬝ᵥ w + α_aux (s j) ⬝ᵥ η j) *
            ∏ r ∈ Finset.univ.erase j, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r)
          ∂(Measure.pi fun _ : R => γ_aux)) / Z w ^ Fintype.card R ∂γ_sh -
      (Fintype.card R : ℝ) *
        ∑ m : L, p m * (W_sh (s i₀) ⬝ᵥ α_sh m) *
          ∫ w, ((∫ η : R → K_aux → ℝ,
              ∏ r, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r)
              ∂(Measure.pi fun _ : R => γ_aux)) *
            ∫ η₀ : K_aux → ℝ,
              deriv u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) *
                Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀))
              ∂γ_aux) / Z w ^ (Fintype.card R + 1) ∂γ_sh := by
  classical
  intro γ_sh γ_aux Z
  let K_tot := K_sh ⊕ (R × K_aux)
  let γ_tot := Measure.pi fun _ : K_tot => gaussianReal 0 1
  have hmp_aux : MeasurePreserving ⇑(MeasurableEquiv.curry R K_aux ℝ)
      (Measure.pi fun _ : R × K_aux => gaussianReal 0 1)
      (Measure.pi fun _ : R => γ_aux) :=
    (measurePreserving_curry_symm (ι := R) (κ := K_aux) (gaussianReal 0 1)).symm
  let e_tot : (K_tot → ℝ) ≃ᵐ (K_sh → ℝ) × (R → K_aux → ℝ) :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : K_tot => ℝ)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.curry R K_aux ℝ))
  have he_fst : ∀ ξ, (e_tot ξ).1 = fun k => ξ (Sum.inl k) := fun _ => rfl
  have he_snd : ∀ ξ r k, (e_tot ξ).2 r k = ξ (Sum.inr (r, k)) := fun _ _ _ => rfl
  have hmp_tot : MeasurePreserving ⇑e_tot γ_tot (γ_sh.prod (Measure.pi fun _ : R => γ_aux)) :=
    ((MeasurePreserving.id γ_sh).prod hmp_aux).comp
      (measurePreserving_sumPiEquivProdPi (fun _ : K_tot => gaussianReal 0 1))
  let cW : Unit → K_tot → ℝ := fun _ =>
    Sum.elim (W_sh (s i₀)) (fun rk => if rk.1 = i₀ then W_aux (s i₀) rk.2 else 0)
  let cX : R → K_tot → ℝ := fun r =>
    Sum.elim (α_sh (s r)) (fun rk => if rk.1 = r then α_aux (s r) rk.2 else 0)
  let cY : L → K_tot → ℝ := fun m =>
    Sum.elim (α_sh m) (fun _ => 0)
  let cAll : Unit ⊕ (R ⊕ L) → K_tot → ℝ := Sum.elim cW (Sum.elim cX cY)
  have hgauss : HasGaussianLaw (fun (ξ : K_tot → ℝ) idx =>
      Sum.elim (fun k (ξ : K_tot → ℝ) => cW k ⬝ᵥ ξ)
        (Sum.elim (fun r (ξ : K_tot → ℝ) => cX r ⬝ᵥ ξ)
          (fun m (ξ : K_tot → ℝ) => cY m ⬝ᵥ ξ)) idx ξ)
      γ_tot := by
    convert hasGaussianLaw_dotProduct_family cAll using 1
    ext ξ idx
    rcases idx with k | (r | m) <;> rfl
  obtain ⟨hFd, hFb, hFder, hFdb⟩ := hasFDerivAt_prod_ϕ ϕ hϕ hM hM'
  obtain ⟨hZd, hZb, hZder, hZdb⟩ := hasFDerivAt_Z_sum hu hB hD₁ p hp hp1 α_aux
  have hstein := integral_mul_div_pow_eq_sum (P := γ_tot)
    (W := fun k ξ => cW k ⬝ᵥ ξ) (X := fun r ξ => cX r ⬝ᵥ ξ) (Y := fun m ξ => cY m ⬝ᵥ ξ)
    hgauss
    (fun k => integral_dotProduct_pi_gaussianReal _)
    (fun r => integral_dotProduct_pi_gaussianReal _)
    (fun m => integral_dotProduct_pi_gaussianReal _)
    ()
    hFd hFb hFdb
    hZd (Real.exp_pos (-B)) hZb hZdb
    (Fintype.card R)
  have hcovX : ∀ j : R, ∫ ξ, cW () ⬝ᵥ ξ * (cX j ⬝ᵥ ξ) ∂γ_tot =
      W_sh (s i₀) ⬝ᵥ α_sh (s j) + if i₀ = j then W_aux (s i₀) ⬝ᵥ α_aux (s j) else 0 := by
    intro j
    rw [integral_dotProduct_mul_dotProduct_pi_gaussianReal]
    change (∑ x : K_sh ⊕ (R × K_aux), cW () x * cX j x) = _
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [cW, cX, dotProduct, Sum.elim_inl, Sum.elim_inr]
    congr 1
    by_cases hij : i₀ = j
    · subst hij
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro r _ hr; simp [hr]
      · simp
    · simp only [hij, ↓reduceIte]
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : r = i₀
      · subst hr; simp [hij]
      · simp [hr]
  have hcovY : ∀ m : L, ∫ ξ, cW () ⬝ᵥ ξ * (cY m ⬝ᵥ ξ) ∂γ_tot = W_sh (s i₀) ⬝ᵥ α_sh m := by
    intro m
    rw [integral_dotProduct_mul_dotProduct_pi_gaussianReal]
    change (∑ x : K_sh ⊕ (R × K_aux), cW () x * cY m x) = _
    rw [Fintype.sum_sum_type]
    simp [cW, cY, dotProduct]
  have hW_e : ∀ ξ, cW () ⬝ᵥ ξ =
      W_sh (s i₀) ⬝ᵥ (e_tot ξ).1 + W_aux (s i₀) ⬝ᵥ (e_tot ξ).2 i₀ := by
    intro ξ
    change (∑ x : K_sh ⊕ (R × K_aux), cW () x * ξ x) = _
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, he_fst]
    simp only [cW, dotProduct, Sum.elim_inl, Sum.elim_inr, he_snd]
    congr 1
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro r _ hr; simp [hr]
    · simp
  have hX_e : ∀ (r : R) ξ, cX r ⬝ᵥ ξ =
      α_sh (s r) ⬝ᵥ (e_tot ξ).1 + α_aux (s r) ⬝ᵥ (e_tot ξ).2 r := by
    intro r ξ
    change (∑ x : K_sh ⊕ (R × K_aux), cX r x * ξ x) = _
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, he_fst]
    simp only [cX, dotProduct, Sum.elim_inl, Sum.elim_inr, he_snd]
    congr 1
    rw [Finset.sum_eq_single r]
    · simp
    · intro r' _ hr'; simp [hr']
    · simp
  have hY_e : ∀ (m : L) ξ, cY m ⬝ᵥ ξ = α_sh m ⬝ᵥ (e_tot ξ).1 := by
    intro m ξ
    change (∑ x : K_sh ⊕ (R × K_aux), cY m x * ξ x) = _
    rw [Fintype.sum_sum_type, he_fst]
    simp [cY, dotProduct]
  have h_push : ∀ (G : (K_sh → ℝ) × (R → K_aux → ℝ) → ℝ),
      Measurable G → Integrable (fun ξ => G (e_tot ξ)) γ_tot →
      ∫ ξ, G (e_tot ξ) ∂γ_tot =
        ∫ w, ∫ η, G (w, η) ∂(Measure.pi fun _ : R => γ_aux) ∂γ_sh := by
    intro G hGm hGi
    have hGi' : Integrable G (γ_sh.prod (Measure.pi fun _ : R => γ_aux)) := by
      rw [← hmp_tot.map_eq, integrable_map_measure hGm.aestronglyMeasurable
        e_tot.measurable.aemeasurable]
      exact hGi
    rw [hmp_tot.integral_comp_of_aestronglyMeasurable hGi'.aestronglyMeasurable,
      integral_prod _ hGi']
  have hZm : Measurable Z := by
    have hm_lin : Measurable fun (w : K_sh → ℝ) (m : L) => α_sh m ⬝ᵥ w :=
      measurable_pi_iff.2 fun m => by simp only [dotProduct]; fun_prop
    exact hZd.continuous.measurable.comp hm_lin
  have hZ_tot : ∀ ξ : K_tot → ℝ,
      (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux) = Z (e_tot ξ).1 :=
    fun ξ => Finset.sum_congr rfl fun m _ => by rw [hY_e]
  obtain ⟨lhsFun, hlhsFun⟩ : ∃ lhsFun : (K_sh → ℝ) × (R → K_aux → ℝ) → ℝ, ∀ q, lhsFun q =
      (W_sh (s i₀) ⬝ᵥ q.1 + W_aux (s i₀) ⬝ᵥ q.2 i₀) *
        ((∏ r, ϕ r (α_sh (s r) ⬝ᵥ q.1 + α_aux (s r) ⬝ᵥ q.2 r)) / Z q.1 ^ Fintype.card R) :=
    ⟨_, fun _ => rfl⟩
  have hlhs_m : Measurable lhsFun := by
    rw [show lhsFun = _ from funext hlhsFun]
    have h1 : Measurable fun q : (K_sh → ℝ) × (R → K_aux → ℝ) =>
        W_sh (s i₀) ⬝ᵥ q.1 + W_aux (s i₀) ⬝ᵥ q.2 i₀ := by
      simp only [dotProduct]; fun_prop
    have h2 : Measurable fun q : (K_sh → ℝ) × (R → K_aux → ℝ) =>
        ∏ r, ϕ r (α_sh (s r) ⬝ᵥ q.1 + α_aux (s r) ⬝ᵥ q.2 r) := by
      refine Finset.measurable_prod _ fun r _ => (hϕ r).continuous.measurable.comp ?_
      simp only [dotProduct]; fun_prop
    exact h1.mul (h2.div ((hZm.comp measurable_fst).pow_const _))
  have hlhs_eq : ∀ ξ, cW () ⬝ᵥ ξ * ((∏ r, ϕ r (cX r ⬝ᵥ ξ)) /
      (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux) ^ Fintype.card R) =
      lhsFun (e_tot ξ) := fun ξ => by
    rw [hlhsFun, hW_e, hZ_tot]
    congr 2
    exact Finset.prod_congr rfl fun r _ => by rw [hX_e]
  have hlhs_i : Integrable (fun ξ => lhsFun (e_tot ξ)) γ_tot := by
    have hw_int : Integrable (fun ξ : K_tot → ℝ => cW () ⬝ᵥ ξ) γ_tot :=
      ((hasGaussianLaw_dotProduct_family cW).eval ()).integrable
    have hrm : Measurable fun ξ : K_tot → ℝ => (∏ r, ϕ r (cX r ⬝ᵥ ξ)) /
        (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux) ^
          Fintype.card R := by
      have h1 : Measurable fun ξ : K_tot → ℝ => ∏ r, ϕ r (cX r ⬝ᵥ ξ) :=
        Finset.measurable_prod _ fun r _ =>
          (hϕ r).continuous.measurable.comp
            (by refine Finset.measurable_sum _ fun x _ => ?_; fun_prop)
      have h2 : Measurable fun ξ : K_tot → ℝ => Z (e_tot ξ).1 ^ Fintype.card R :=
        (hZm.comp (measurable_fst.comp e_tot.measurable)).pow_const _
      simp_rw [hZ_tot]
      exact h1.div h2
    have hrb : ∀ ξ : K_tot → ℝ, |(∏ r, ϕ r (cX r ⬝ᵥ ξ)) /
        (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux) ^
          Fintype.card R| ≤
        (∏ r, |M r|) / Real.exp (-B) ^ Fintype.card R := fun ξ => by
      rw [abs_div, abs_of_pos (pow_pos (Real.exp_pos (-B) |>.trans_le (hZb _)) _)]
      exact div_le_div₀ (Finset.prod_nonneg fun _ _ => abs_nonneg _) (hFb _)
        (pow_pos (Real.exp_pos _) _) (pow_le_pow_left₀ (Real.exp_pos _).le (hZb _) _)
    have := hw_int.bdd_mul_of_abs_le hrm.aestronglyMeasurable (ae_of_all _ hrb)
    exact this.congr (ae_of_all _ fun ξ => by dsimp; rw [mul_comm, hlhs_eq])
  have hLHS : ∫ ξ, cW () ⬝ᵥ ξ * ((∏ r, ϕ r (cX r ⬝ᵥ ξ)) /
      (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux) ^ Fintype.card R)
      ∂γ_tot =
    ∫ w, (∫ η : R → K_aux → ℝ,
        (W_sh (s i₀) ⬝ᵥ w + W_aux (s i₀) ⬝ᵥ η i₀) *
          (∏ r, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r))
        ∂(Measure.pi fun _ : R => γ_aux)) / Z w ^ Fintype.card R ∂γ_sh := by
    simp_rw [hlhs_eq]
    rw [h_push lhsFun hlhs_m hlhs_i]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp_rw [hlhsFun, ← mul_div_assoc]
    rw [integral_div]
  have hRHS1 : ∀ j : R, ∫ ξ,
      (fderiv ℝ (fun x => ∏ r, ϕ r (x r)) (fun k => cX k ⬝ᵥ ξ)) (Pi.single j 1) /
      (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux) ^ Fintype.card R
      ∂γ_tot =
    ∫ w, (∫ η : R → K_aux → ℝ,
        deriv (ϕ j) (α_sh (s j) ⬝ᵥ w + α_aux (s j) ⬝ᵥ η j) *
          ∏ r ∈ Finset.univ.erase j, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r)
        ∂(Measure.pi fun _ : R => γ_aux)) / Z w ^ Fintype.card R ∂γ_sh := by
    intro j
    obtain ⟨rhs1Fun, hrhs1Fun⟩ : ∃ rhs1Fun : (K_sh → ℝ) × (R → K_aux → ℝ) → ℝ, ∀ q, rhs1Fun q =
        (deriv (ϕ j) (α_sh (s j) ⬝ᵥ q.1 + α_aux (s j) ⬝ᵥ q.2 j) *
          ∏ r ∈ Finset.univ.erase j, ϕ r (α_sh (s r) ⬝ᵥ q.1 + α_aux (s r) ⬝ᵥ q.2 r)) /
          Z q.1 ^ Fintype.card R := ⟨_, fun _ => rfl⟩
    have hr1_m : Measurable rhs1Fun := by
      rw [show rhs1Fun = _ from funext hrhs1Fun]
      have h1 : Measurable fun q : (K_sh → ℝ) × (R → K_aux → ℝ) =>
          deriv (ϕ j) (α_sh (s j) ⬝ᵥ q.1 + α_aux (s j) ⬝ᵥ q.2 j) :=
        (measurable_deriv _).comp (by simp only [dotProduct]; fun_prop)
      have h2 : Measurable fun q : (K_sh → ℝ) × (R → K_aux → ℝ) =>
          ∏ r ∈ Finset.univ.erase j, ϕ r (α_sh (s r) ⬝ᵥ q.1 + α_aux (s r) ⬝ᵥ q.2 r) :=
        Finset.measurable_prod _ fun r _ =>
          (hϕ r).continuous.measurable.comp (by simp only [dotProduct]; fun_prop)
      exact (h1.mul h2).div ((hZm.comp measurable_fst).pow_const _)
    have hr1_eq : ∀ ξ,
        (fderiv ℝ (fun x => ∏ r, ϕ r (x r)) (fun k => cX k ⬝ᵥ ξ)) (Pi.single j 1) /
          (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux) ^
            Fintype.card R =
        rhs1Fun (e_tot ξ) := fun ξ => by
      rw [hFder, hrhs1Fun]
      simp only [hX_e, hY_e]
      rfl
    have hr1_i : Integrable (fun ξ => rhs1Fun (e_tot ξ)) γ_tot := by
      refine Integrable.of_bound (C := (|M' j| * ∏ r ∈ Finset.univ.erase j, |M r|) /
          Real.exp (-B) ^ Fintype.card R)
        (hr1_m.comp e_tot.measurable).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
      rw [Real.norm_eq_abs, ← hr1_eq, abs_div,
        abs_of_pos (pow_pos (Real.exp_pos (-B) |>.trans_le (hZb _)) _)]
      exact div_le_div₀ (by positivity) (hFdb j _) (pow_pos (Real.exp_pos _) _)
        (pow_le_pow_left₀ (Real.exp_pos _).le (hZb _) _)
    simp_rw [hr1_eq]
    rw [h_push rhs1Fun hr1_m hr1_i]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp_rw [hrhs1Fun]
    rw [integral_div]
  have hRHS2 : ∀ m : L, ∫ ξ,
      (∏ r, ϕ r (cX r ⬝ᵥ ξ)) *
        (fderiv ℝ (fun y => ∑ m' : L, p m' * ∫ η, Real.exp (u (y m' + α_aux m' ⬝ᵥ η)) ∂γ_aux)
          (fun k => cY k ⬝ᵥ ξ)) (Pi.single m 1) /
      (∑ m' : L, p m' * ∫ η, Real.exp (u (cY m' ⬝ᵥ ξ + α_aux m' ⬝ᵥ η)) ∂γ_aux) ^
        (Fintype.card R + 1) ∂γ_tot =
    p m * ∫ w, ((∫ η : R → K_aux → ℝ,
          ∏ r, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r) ∂(Measure.pi fun _ : R => γ_aux)) *
        ∫ η₀ : K_aux → ℝ,
          deriv u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) *
            Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀))
          ∂γ_aux) / Z w ^ (Fintype.card R + 1) ∂γ_sh := by
    intro m
    obtain ⟨rhs2Fun, hrhs2Fun⟩ : ∃ rhs2Fun : (K_sh → ℝ) × (R → K_aux → ℝ) → ℝ, ∀ q, rhs2Fun q =
        p m * ((∏ r, ϕ r (α_sh (s r) ⬝ᵥ q.1 + α_aux (s r) ⬝ᵥ q.2 r)) *
          (∫ η₀ : K_aux → ℝ,
            deriv u (α_sh m ⬝ᵥ q.1 + α_aux m ⬝ᵥ η₀) *
              Real.exp (u (α_sh m ⬝ᵥ q.1 + α_aux m ⬝ᵥ η₀))
            ∂γ_aux) / Z q.1 ^ (Fintype.card R + 1)) := ⟨_, fun _ => rfl⟩
    have hr2_m : Measurable rhs2Fun := by
      rw [show rhs2Fun = _ from funext hrhs2Fun]
      have h1 : Measurable fun q : (K_sh → ℝ) × (R → K_aux → ℝ) =>
          ∏ r, ϕ r (α_sh (s r) ⬝ᵥ q.1 + α_aux (s r) ⬝ᵥ q.2 r) :=
        Finset.measurable_prod _ fun r _ =>
          (hϕ r).continuous.measurable.comp (by simp only [dotProduct]; fun_prop)
      have h2 : Measurable fun q : (K_sh → ℝ) × (R → K_aux → ℝ) =>
          ∫ η₀ : K_aux → ℝ,
            deriv u (α_sh m ⬝ᵥ q.1 + α_aux m ⬝ᵥ η₀) *
              Real.exp (u (α_sh m ⬝ᵥ q.1 + α_aux m ⬝ᵥ η₀))
            ∂γ_aux := by
        have hj : Measurable fun p' : ((K_sh → ℝ) × (R → K_aux → ℝ)) × (K_aux → ℝ) =>
            deriv u (α_sh m ⬝ᵥ p'.1.1 + α_aux m ⬝ᵥ p'.2) *
              Real.exp (u (α_sh m ⬝ᵥ p'.1.1 + α_aux m ⬝ᵥ p'.2)) := by
          have hl : Measurable fun p' : ((K_sh → ℝ) × (R → K_aux → ℝ)) × (K_aux → ℝ) =>
              α_sh m ⬝ᵥ p'.1.1 + α_aux m ⬝ᵥ p'.2 := by simp only [dotProduct]; fun_prop
          exact ((measurable_deriv u).comp hl).mul
            (Real.measurable_exp.comp (hu.continuous.measurable.comp hl))
        exact (hj.stronglyMeasurable.integral_prod_right' (ν := γ_aux)).measurable
      exact ((h1.mul h2).div ((hZm.comp measurable_fst).pow_const _)).const_mul _
    have hr2_eq : ∀ ξ, (∏ r, ϕ r (cX r ⬝ᵥ ξ)) *
        (fderiv ℝ (fun y => ∑ m' : L, p m' * ∫ η, Real.exp (u (y m' + α_aux m' ⬝ᵥ η)) ∂γ_aux)
          (fun k => cY k ⬝ᵥ ξ)) (Pi.single m 1) /
        (∑ m' : L, p m' * ∫ η, Real.exp (u (cY m' ⬝ᵥ ξ + α_aux m' ⬝ᵥ η)) ∂γ_aux) ^
          (Fintype.card R + 1) = rhs2Fun (e_tot ξ) := fun ξ => by
      rw [hZder, hrhs2Fun]
      simp only [hX_e, hY_e]
      change _ / Z (e_tot ξ).1 ^ (Fintype.card R + 1) = _
      ring
    have hr2_i : Integrable (fun ξ => rhs2Fun (e_tot ξ)) γ_tot := by
      refine Integrable.of_bound (C := (∏ r, |M r|) * (p m * (|D₁| * Real.exp B)) /
          Real.exp (-B) ^ (Fintype.card R + 1))
        (hr2_m.comp e_tot.measurable).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
      rw [Real.norm_eq_abs, ← hr2_eq, abs_div, abs_mul,
        abs_of_pos (pow_pos (Real.exp_pos (-B) |>.trans_le (hZb _)) _)]
      exact div_le_div₀ (mul_nonneg (Finset.prod_nonneg fun _ _ => abs_nonneg _)
          (mul_nonneg (hp m) (by positivity)))
        (mul_le_mul (hFb _) (hZdb m _) (abs_nonneg _)
          (Finset.prod_nonneg fun _ _ => abs_nonneg _))
        (pow_pos (Real.exp_pos _) _)
        (pow_le_pow_left₀ (Real.exp_pos _).le (hZb _) _)
    simp_rw [hr2_eq]
    rw [h_push rhs2Fun hr2_m hr2_i]
    simp_rw [hrhs2Fun, integral_const_mul]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    dsimp only
    rw [integral_div, integral_mul_const]
  rw [← hLHS, hstein]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcovX j, hRHS1 j]
  · congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hcovY m, hRHS2 m]
    ring

private lemma integral_Z_eq_sum_fiber {α L K_aux : Type*} [MeasurableSpace α]
    [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L] [Fintype K_aux]
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀] (π : α → L) (hπ : Measurable π)
    {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    (c : L → K_aux → ℝ) (y : L → ℝ) :
    let γ_aux := Measure.pi fun _ : K_aux => gaussianReal 0 1
    ∫ q : α × (K_aux → ℝ), Real.exp (u (y (π q.1) + c (π q.1) ⬝ᵥ q.2)) ∂(μ₀.prod γ_aux) =
      ∑ m : L, (μ₀.map π).real {m} * ∫ η, Real.exp (u (y m + c m ⬝ᵥ η)) ∂γ_aux := by
  intro γ_aux
  have hexp : Integrable (fun q : α × (K_aux → ℝ) =>
      Real.exp (u (y (π q.1) + c (π q.1) ⬝ᵥ q.2))) (μ₀.prod γ_aux) := by
    have hm1 : Measurable fun q : α × (K_aux → ℝ) => y (π q.1) :=
      (measurable_of_finite y).comp (hπ.comp measurable_fst)
    have hm2 : Measurable fun q : α × (K_aux → ℝ) => c (π q.1) ⬝ᵥ q.2 := by
      simp only [dotProduct]
      refine Finset.measurable_sum _ fun k _ => ?_
      exact ((measurable_of_finite fun m => c m k).comp (hπ.comp measurable_fst)).mul
        ((measurable_pi_apply k).comp measurable_snd)
    exact Integrable.of_bound (C := Real.exp B)
      (Real.measurable_exp.comp (hu.comp (hm1.add hm2))).aestronglyMeasurable
      (ae_of_all _ fun q => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (le_of_abs_le (hB _)))
  rw [integral_prod _ hexp]
  set g : L → ℝ := fun m => ∫ η, Real.exp (u (y m + c m ⬝ᵥ η)) ∂γ_aux
  change ∫ a, g (π a) ∂μ₀ = ∑ m : L, (μ₀.map π).real {m} * g m
  rw [← integral_map hπ.aemeasurable (measurable_of_finite g).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  simp [smul_eq_mul]

private lemma integral_tilted_replica_fubini
    {α L K_sh K_aux ι : Type*} [MeasurableSpace α]
    [Fintype L] [MeasurableSpace L] [MeasurableSingletonClass L]
    [Fintype K_sh] [Fintype K_aux] [Fintype ι]
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (π : α → L) (hπ : Measurable π)
    (α_sh : L → K_sh → ℝ) (α_aux : L → K_aux → ℝ)
    {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, |u x| ≤ B)
    {F : (ι → α) → ℝ} (hFi : Integrable F (Measure.pi fun _ : ι => μ₀))
    (H : (K_sh → ℝ) → (ι → α × (K_aux → ℝ)) → ℝ)
    (K : (ι → L) → (K_sh → ℝ) → (ι → K_aux → ℝ) → ℝ)
    (hHK : ∀ w σ,
      H w σ * Real.exp (∑ r, u (α_sh (π (σ r).1) ⬝ᵥ w + α_aux (π (σ r).1) ⬝ᵥ (σ r).2)) =
        K (fun r => π (σ r).1) w (fun r => (σ r).2))
    (hKm : ∀ s, Measurable fun q : (K_sh → ℝ) × (ι → K_aux → ℝ) => K s q.1 q.2)
    {bw : (K_sh → ℝ) → ℝ} (hbwi : Integrable bw (Measure.pi fun _ : K_sh => gaussianReal 0 1))
    {bη : (ι → K_aux → ℝ) → ℝ}
    (hbηi : Integrable bη (Measure.pi fun _ : ι => Measure.pi fun _ : K_aux => gaussianReal 0 1))
    (hKb : ∀ s w η, |K s w η| ≤ bw w + bη η) :
    let γ_sh := Measure.pi fun _ : K_sh => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : K_aux => gaussianReal 0 1
    let Z (w : K_sh → ℝ) : ℝ :=
      ∑ m : L, (μ₀.map π).real {m} * ∫ η, Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η)) ∂γ_aux
    ∫ w, ∫ σ : ι → α × (K_aux → ℝ), F (fun r => (σ r).1) * H w σ
        ∂(Measure.pi fun _ : ι => (μ₀.prod γ_aux).tilted
          (fun q => u (α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2))) ∂γ_sh =
      ∫ a : ι → α, F a *
        ∫ w, (∫ η : ι → K_aux → ℝ, K (fun r => π (a r)) w η ∂(Measure.pi fun _ : ι => γ_aux)) /
          Z w ^ Fintype.card ι ∂γ_sh ∂(Measure.pi fun _ : ι => μ₀) := by
  classical
  intro γ_sh γ_aux Z
  have hZ_eq : ∀ w, ∫ q : α × (K_aux → ℝ),
      Real.exp (u (α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2)) ∂(μ₀.prod γ_aux) = Z w :=
    fun w => integral_Z_eq_sum_fiber μ₀ π hπ hu hB α_aux (fun m => α_sh m ⬝ᵥ w)
  have hp1 : ∑ m : L, (μ₀.map π).real {m} = 1 := by
    have : IsProbabilityMeasure (μ₀.map π) :=
      (Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).2 inferInstance
    have hsum := integral_fintype (μ := μ₀.map π) (f := fun _ : L => (1 : ℝ)) Integrable.of_finite
    simp only [smul_eq_mul, mul_one, integral_const, probReal_univ] at hsum
    exact hsum.symm
  have hZ_ge : ∀ w, Real.exp (-B) ≤ Z w := by
    intro w
    have hlow : ∀ m : L, Real.exp (-B) ≤
        ∫ η, Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η)) ∂γ_aux :=
      fun m => by
        have hm1 : Measurable fun η : K_aux → ℝ => α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η :=
          measurable_const.add (Finset.measurable_sum _ fun k _ => by fun_prop)
        have hint : Integrable (fun η => Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η))) γ_aux :=
          Integrable.of_bound (C := Real.exp B)
            (Real.measurable_exp.comp (hu.comp hm1)).aestronglyMeasurable
            (ae_of_all _ fun η => by
              rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
              exact Real.exp_le_exp.2 (le_of_abs_le (hB _)))
        have hm := integral_mono (integrable_const (Real.exp (-B))) hint
          fun η => Real.exp_le_exp.2 (neg_le_of_abs_le (hB _))
        simpa [γ_aux] using hm
    calc Real.exp (-B) = (∑ m : L, (μ₀.map π).real {m}) * Real.exp (-B) := by rw [hp1, one_mul]
      _ = ∑ m : L, (μ₀.map π).real {m} * Real.exp (-B) := Finset.sum_mul _ _ _
      _ ≤ Z w := Finset.sum_le_sum fun m _ =>
          mul_le_mul_of_nonneg_left (hlow m) ENNReal.toReal_nonneg
  have hZm : Measurable Z := by
    refine Finset.measurable_sum _ fun m _ => ?_
    have hj : Measurable fun p' : (K_sh → ℝ) × (K_aux → ℝ) =>
        Real.exp (u (α_sh m ⬝ᵥ p'.1 + α_aux m ⬝ᵥ p'.2)) := by
      have hl : Measurable fun p' : (K_sh → ℝ) × (K_aux → ℝ) =>
          α_sh m ⬝ᵥ p'.1 + α_aux m ⬝ᵥ p'.2 :=
        (Finset.measurable_sum _ fun k _ => by fun_prop).add
          (Finset.measurable_sum _ fun k _ => by fun_prop)
      exact Real.measurable_exp.comp (hu.comp hl)
    exact (hj.stronglyMeasurable.integral_prod_right' (ν := γ_aux)).measurable.const_mul _
  have hπa_m : Measurable fun a : ι → α => (fun r => π (a r)) :=
    measurable_pi_iff.2 fun r => hπ.comp (measurable_pi_apply r)
  have hK_sum : ∀ (a : ι → α) w η, K (fun r => π (a r)) w η =
      ∑ s : ι → L, (if (fun r => π (a r)) = s then (1 : ℝ) else 0) * K s w η :=
    fun a w η => by simp
  have hw_step : ∀ w : K_sh → ℝ,
      ∫ σ : ι → α × (K_aux → ℝ), F (fun r => (σ r).1) * H w σ
          ∂(Measure.pi fun _ : ι => (μ₀.prod γ_aux).tilted
            (fun q => u (α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2))) =
        ∫ a : ι → α, F a *
          ((∫ η : ι → K_aux → ℝ, K (fun r => π (a r)) w η ∂(Measure.pi fun _ : ι => γ_aux)) /
            Z w ^ Fintype.card ι) ∂(Measure.pi fun _ : ι => μ₀) := by
    intro w
    have : IsFiniteMeasure (μ₀.prod γ_aux) := inferInstance
    rw [integral_pi_tilted_eq_div,
      integral_pi_exp_sum (fun q : α × (K_aux → ℝ) =>
        u (α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2)),
      hZ_eq w]
    have hmp := measurePreserving_arrowProdEquivProdArrow α (K_aux → ℝ) ι
      (fun _ => μ₀) (fun _ => γ_aux)
    have hK_meas_w : Measurable fun p' : (ι → α) × (ι → K_aux → ℝ) =>
        K (fun r => π (p'.1 r)) w p'.2 := by
      have : (fun p' : (ι → α) × (ι → K_aux → ℝ) => K (fun r => π (p'.1 r)) w p'.2) =
          fun p' => ∑ s : ι → L, (if (fun r => π (p'.1 r)) = s then (1 : ℝ) else 0) *
            K s w p'.2 := funext fun p' => hK_sum p'.1 w p'.2
      rw [this]
      refine Finset.measurable_sum _ fun s _ => ?_
      have hs1 : Measurable fun p' : (ι → α) × (ι → K_aux → ℝ) =>
          (if (fun r => π (p'.1 r)) = s then (1 : ℝ) else 0) :=
        (measurable_of_finite fun t : ι → L => if t = s then (1 : ℝ) else 0).comp
          (hπa_m.comp measurable_fst)
      exact hs1.mul ((hKm s).comp (measurable_const.prodMk measurable_snd))
    have hnum_int : Integrable (fun p' : (ι → α) × (ι → K_aux → ℝ) =>
        F p'.1 * K (fun r => π (p'.1 r)) w p'.2)
        ((Measure.pi fun _ : ι => μ₀).prod (Measure.pi fun _ : ι => γ_aux)) := by
      have hdom : Integrable (fun p' : (ι → α) × (ι → K_aux → ℝ) =>
          |F p'.1| * (|bw w| + |bη p'.2|))
          ((Measure.pi fun _ : ι => μ₀).prod (Measure.pi fun _ : ι => γ_aux)) :=
        hFi.abs.mul_prod ((integrable_const |bw w|).add hbηi.abs)
      refine hdom.mono' (hFi.aestronglyMeasurable.comp_fst.mul hK_meas_w.aestronglyMeasurable)
        (ae_of_all _ fun p' => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact (hKb _ w p'.2).trans (add_le_add (le_abs_self _) (le_abs_self _))
    have heq1 : ∫ σ : ι → α × (K_aux → ℝ),
        F (fun r => (σ r).1) * H w σ *
          Real.exp (∑ r, u (α_sh (π (σ r).1) ⬝ᵥ w + α_aux (π (σ r).1) ⬝ᵥ (σ r).2))
        ∂(Measure.pi fun _ : ι => μ₀.prod γ_aux) =
      ∫ p' : (ι → α) × (ι → K_aux → ℝ),
        F p'.1 * K (fun r => π (p'.1 r)) w p'.2
        ∂((Measure.pi fun _ : ι => μ₀).prod (Measure.pi fun _ : ι => γ_aux)) := by
      rw [← hmp.integral_comp_of_aestronglyMeasurable hnum_int.aestronglyMeasurable]
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      dsimp only [Function.comp_apply]
      rw [mul_assoc, hHK w σ]
      rfl
    rw [heq1, integral_prod _ hnum_int, ← integral_div]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    dsimp only
    rw [integral_const_mul, mul_div_assoc]
  simp_rw [hw_step]
  let G_wa : (K_sh → ℝ) → (ι → α) → ℝ := fun w a =>
    F a * ((∫ η : ι → K_aux → ℝ, K (fun r => π (a r)) w η ∂(Measure.pi fun _ : ι => γ_aux)) /
      Z w ^ Fintype.card ι)
  have hG_wa_int : Integrable (Function.uncurry G_wa)
      (γ_sh.prod (Measure.pi fun _ : ι => μ₀)) := by
    let C_η : ℝ := ∫ η, |bη η| ∂(Measure.pi fun _ : ι => γ_aux)
    let C_Z : ℝ := Real.exp (-B) ^ Fintype.card ι
    have hCZ_pos : 0 < C_Z := pow_pos (Real.exp_pos _) _
    have hdom_wa : Integrable (fun q : (K_sh → ℝ) × (ι → α) =>
        ((|bw q.1| + C_η) / C_Z) * |F q.2|)
        (γ_sh.prod (Measure.pi fun _ : ι => μ₀)) :=
      (((hbwi.abs.add (integrable_const C_η)).div_const C_Z)).mul_prod hFi.abs
    have hK_int_m : ∀ s : ι → L, Measurable fun w : K_sh → ℝ =>
        ∫ η : ι → K_aux → ℝ, K s w η ∂(Measure.pi fun _ : ι => γ_aux) :=
      fun s => ((hKm s).stronglyMeasurable.integral_prod_right'
        (ν := Measure.pi fun _ : ι => γ_aux)).measurable
    have hmeas_wa : AEStronglyMeasurable (Function.uncurry G_wa)
        (γ_sh.prod (Measure.pi fun _ : ι => μ₀)) := by
      refine (hFi.aestronglyMeasurable.comp_snd).mul ?_
      refine Measurable.aestronglyMeasurable ?_
      have h_inner_eq : (fun q : (K_sh → ℝ) × (ι → α) =>
          ∫ η : ι → K_aux → ℝ, K (fun r => π (q.2 r)) q.1 η
            ∂(Measure.pi fun _ : ι => γ_aux)) =
          fun q => ∑ s : ι → L, (if (fun r => π (q.2 r)) = s then (1 : ℝ) else 0) *
            ∫ η : ι → K_aux → ℝ, K s q.1 η ∂(Measure.pi fun _ : ι => γ_aux) := by
        ext q
        rw [Finset.sum_eq_single (fun r => π (q.2 r))
          (fun s' _ hs' => by simp [Ne.symm hs']) (by simp)]
        simp
      rw [show (fun q : (K_sh → ℝ) × (ι → α) =>
          (∫ η : ι → K_aux → ℝ, K (fun r => π (q.2 r)) q.1 η
              ∂(Measure.pi fun _ : ι => γ_aux)) /
            Z q.1 ^ Fintype.card ι) =
          fun q => (∑ s : ι → L, (if (fun r => π (q.2 r)) = s then (1 : ℝ) else 0) *
            ∫ η : ι → K_aux → ℝ, K s q.1 η ∂(Measure.pi fun _ : ι => γ_aux)) /
            Z q.1 ^ Fintype.card ι from funext fun q => by rw [← congrFun h_inner_eq q]]
      refine (Finset.measurable_sum _ fun s _ => ?_).div
        ((hZm.comp measurable_fst).pow_const _)
      exact ((measurable_of_finite fun t : ι → L => if t = s then (1 : ℝ) else 0).comp
        (hπa_m.comp measurable_snd)).mul ((hK_int_m s).comp measurable_fst)
    refine hdom_wa.mono' hmeas_wa (ae_of_all _ fun q => ?_)
    dsimp only [Function.uncurry, G_wa]
    rw [Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_pos (pow_pos ((Real.exp_pos (-B)).trans_le (hZ_ge q.1)) _)]
    have hK_eta_int : Integrable (fun η => |bw q.1| + |bη η|) (Measure.pi fun _ : ι => γ_aux) :=
      (integrable_const _).add hbηi.abs
    have hK_bd : |∫ η : ι → K_aux → ℝ, K (fun r => π (q.2 r)) q.1 η
          ∂(Measure.pi fun _ : ι => γ_aux)| ≤
        |bw q.1| + C_η := by
      calc _ ≤ ∫ η, |K (fun r => π (q.2 r)) q.1 η| ∂(Measure.pi fun _ : ι => γ_aux) :=
            abs_integral_le_integral_abs
        _ ≤ ∫ η, (|bw q.1| + |bη η|) ∂(Measure.pi fun _ : ι => γ_aux) := by
            refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) hK_eta_int
              (ae_of_all _ fun η =>
                (hKb _ q.1 η).trans (add_le_add (le_abs_self _) (le_abs_self _)))
        _ = |bw q.1| + C_η := by
            rw [integral_add (integrable_const _) hbηi.abs, integral_const, probReal_univ, one_smul]
    calc |F q.2| * (|∫ η, K (fun r => π (q.2 r)) q.1 η ∂(Measure.pi fun _ : ι => γ_aux)| /
            Z q.1 ^ Fintype.card ι)
        ≤ |F q.2| * ((|bw q.1| + C_η) / C_Z) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact div_le_div₀ (add_nonneg (abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _))
            hK_bd hCZ_pos (pow_le_pow_left₀ (Real.exp_pos _).le (hZ_ge q.1) _)
      _ = ((|bw q.1| + C_η) / C_Z) * |F q.2| := mul_comm _ _
  change ∫ w, ∫ a, G_wa w a ∂(Measure.pi fun _ : ι => μ₀) ∂γ_sh = _
  rw [integral_integral_swap hG_wa_int]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  dsimp only [G_wa]
  rw [integral_const_mul]

/-- **Model-free Gaussian integration by parts for a tilted replica average.** Let `μ₀` be a
probability measure on an old-state space `α` with a measurable projection `π : α → L` onto a
finite spin-label set `L`. With shared Gaussian vector `w` and per-replica auxiliary Gaussian
vectors `η`, field `S w q = α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2`, multiplier
`Wt w q = W_sh (π q.1) ⬝ᵥ w + W_aux (π q.1) ⬝ᵥ q.2`, and per-replica factors `ψ r` such that
`(ψ r * exp ∘ u)' = ψ' r * exp ∘ u` is bounded (requiring no continuity of `ψ' r`), the quenched
expectation of `⟨f · Wt(σ_{i₀}) · ∏_r ψ_r(S(σ_r))⟩` expands into `R` replica terms plus the fresh
replica term created by differentiating the normalizer. Only `Integrable f (pi μ₀)` is required of
`f`. -/
theorem stein_tilted_replica_ratio
    {α L K_sh K_aux R : Type*} [MeasurableSpace α]
    [Finite L] [Nonempty L] [MeasurableSpace L] [MeasurableSingletonClass L]
    [Fintype K_sh] [Fintype K_aux] [Fintype R] [DecidableEq R]
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (π : α → L) (hπ : Measurable π)
    (α_sh W_sh : L → K_sh → ℝ) (α_aux W_aux : L → K_aux → ℝ)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) {B D₁ : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (ψ : R → ℝ → ℝ)
    (hψd : ∀ r, Differentiable ℝ fun x => ψ r x * Real.exp (u x))
    {M₀ M' : R → ℝ}
    (hM₀ : ∀ r x, |ψ r x| ≤ M₀ r)
    (hM' : ∀ r x, |deriv (fun x => ψ r x * Real.exp (u x)) x| ≤ M' r)
    (ψ' : R → ℝ → ℝ)
    (hψ' : ∀ r x, deriv (fun x => ψ r x * Real.exp (u x)) x = ψ' r x * Real.exp (u x))
    (i₀ : R)
    {f : (R → α) → ℝ} (hfi : Integrable f (Measure.pi fun _ : R => μ₀)) :
    let γ_sh := Measure.pi fun _ : K_sh => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : K_aux => gaussianReal 0 1
    let S (w : K_sh → ℝ) (q : α × (K_aux → ℝ)) : ℝ :=
      α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2
    let Wt (w : K_sh → ℝ) (q : α × (K_aux → ℝ)) : ℝ :=
      W_sh (π q.1) ⬝ᵥ w + W_aux (π q.1) ⬝ᵥ q.2
    ∫ w, ∫ σ : R → α × (K_aux → ℝ),
        f (fun r => (σ r).1) * Wt w (σ i₀) * (∏ r, ψ r (S w (σ r)))
        ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S w q))) ∂γ_sh =
      ∑ j : R, ∫ w, ∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) *
            (W_sh (π (σ i₀).1) ⬝ᵥ α_sh (π (σ j).1) +
              if i₀ = j then W_aux (π (σ i₀).1) ⬝ᵥ α_aux (π (σ j).1) else 0) *
            (ψ' j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S w q))) ∂γ_sh -
      (Fintype.card R : ℝ) * ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
          f (fun r => (σ (some r)).1) *
            (W_sh (π (σ (some i₀)).1) ⬝ᵥ α_sh (π (σ none).1)) *
            (∏ r : R, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))
          ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted (fun q => u (S w q))) ∂γ_sh := by
  classical
  have := Fintype.ofFinite L
  intro γ_sh γ_aux S Wt
  have hum : Measurable u := hu.continuous.measurable
  let p : L → ℝ := fun m => (μ₀.map π).real {m}
  have hp0 : ∀ m, 0 ≤ p m := fun m => ENNReal.toReal_nonneg
  have hp1 : ∑ m : L, p m = 1 := by
    have : IsProbabilityMeasure (μ₀.map π) :=
      (Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).2 inferInstance
    have hsum := integral_fintype (μ := μ₀.map π) (f := fun _ : L => (1 : ℝ)) Integrable.of_finite
    simp only [smul_eq_mul, mul_one, integral_const, probReal_univ] at hsum
    exact hsum.symm
  let Z : (K_sh → ℝ) → ℝ := fun w =>
    ∑ m : L, p m * ∫ η, Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η)) ∂γ_aux
  obtain ⟨hZd, hZb, -, -⟩ := hasFDerivAt_Z_sum hu hB hD₁ p hp0 hp1 α_aux
  have hZ_ge : ∀ w, Real.exp (-B) ≤ Z w := fun w => hZb (fun m => α_sh m ⬝ᵥ w)
  let ϕ : R → ℝ → ℝ := fun r x => ψ r x * Real.exp (u x)
  have hM : ∀ r x, |ϕ r x| ≤ |M₀ r| * Real.exp B := fun r x =>
    abs_mul_exp_le ((hM₀ r x).trans (le_abs_self _)) (le_of_abs_le (hB x))
  let C_ϕ : ℝ := ∏ r, (|M₀ r| * Real.exp B)
  have hCϕ0 : 0 ≤ C_ϕ := Finset.prod_nonneg fun _ _ => by positivity
  have hLHS := integral_tilted_replica_fubini μ₀ π hπ α_sh α_aux hum hB hfi
    (fun w σ => Wt w (σ i₀) * ∏ r, ψ r (S w (σ r)))
    (fun s w η => (W_sh (s i₀) ⬝ᵥ w + W_aux (s i₀) ⬝ᵥ η i₀) *
      ∏ r, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r))
    (fun w σ => by
      simp only [Wt, S, ϕ, mul_assoc, Real.exp_sum, ← Finset.prod_mul_distrib])
    (fun s => by
      have h1 : Measurable fun q : (K_sh → ℝ) × (R → K_aux → ℝ) =>
          W_sh (s i₀) ⬝ᵥ q.1 + W_aux (s i₀) ⬝ᵥ q.2 i₀ :=
        (Finset.measurable_sum _ fun k _ =>
          measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
          (Finset.measurable_sum _ fun k _ =>
            measurable_const.mul
              ((measurable_pi_apply k).comp ((measurable_pi_apply i₀).comp measurable_snd)))
      have h2 : Measurable fun q : (K_sh → ℝ) × (R → K_aux → ℝ) =>
          ∏ r, ϕ r (α_sh (s r) ⬝ᵥ q.1 + α_aux (s r) ⬝ᵥ q.2 r) :=
        Finset.measurable_prod _ fun r _ => (hψd r).continuous.measurable.comp
          ((Finset.measurable_sum _ fun k _ =>
            measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
            (Finset.measurable_sum _ fun k _ =>
              measurable_const.mul
                ((measurable_pi_apply k).comp ((measurable_pi_apply r).comp measurable_snd))))
      exact h1.mul h2)
    (bw := fun w : K_sh → ℝ => C_ϕ * ∑ m : L, ∑ k : K_sh, |W_sh m k| * |w k|)
    (by
      have hsum_i : Integrable (fun w : K_sh → ℝ =>
          ∑ m : L, ∑ k : K_sh, |W_sh m k| * |w k|) γ_sh :=
        integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun k _ =>
          (integrable_comp_eval (μ := fun _ : K_sh => gaussianReal 0 1) (i := k)
            (integrable_abs_id_gaussianReal (m := 0) (v := 1))).const_mul |W_sh m k|
      exact hsum_i.const_mul C_ϕ)
    (bη := fun η : R → K_aux → ℝ => C_ϕ * ∑ m : L, ∑ k : K_aux, |W_aux m k| * |η i₀ k|)
    (by
      have hsum_i : Integrable (fun η : R → K_aux → ℝ =>
          ∑ m : L, ∑ k : K_aux, |W_aux m k| * |η i₀ k|) (Measure.pi fun _ : R => γ_aux) := by
        refine integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun k _ => ?_
        have hk : Integrable (fun x : K_aux → ℝ => |x k|) γ_aux :=
          integrable_comp_eval (μ := fun _ : K_aux => gaussianReal 0 1) (i := k)
            (integrable_abs_id_gaussianReal (m := 0) (v := 1))
        exact (integrable_comp_eval (μ := fun _ : R => γ_aux) (i := i₀) hk).const_mul |W_aux m k|
      exact hsum_i.const_mul C_ϕ)
    (fun s w η => by
      rw [abs_mul]
      have hp_bd : |∏ r, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r)| ≤ C_ϕ := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hM r _
      have hw_bd : |W_sh (s i₀) ⬝ᵥ w + W_aux (s i₀) ⬝ᵥ η i₀| ≤
          (∑ m : L, ∑ k : K_sh, |W_sh m k| * |w k|) +
            (∑ m : L, ∑ k : K_aux, |W_aux m k| * |η i₀ k|) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          simp_rw [abs_mul]
          exact Finset.single_le_sum (f := fun m : L => ∑ k : K_sh, |W_sh m k| * |w k|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ (s i₀))
        · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          simp_rw [abs_mul]
          exact Finset.single_le_sum (f := fun m : L => ∑ k : K_aux, |W_aux m k| * |η i₀ k|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ (s i₀))
      calc _ ≤ ((∑ m : L, ∑ k : K_sh, |W_sh m k| * |w k|) +
                (∑ m : L, ∑ k : K_aux, |W_aux m k| * |η i₀ k|)) * C_ϕ :=
            mul_le_mul hw_bd hp_bd (abs_nonneg _) (by positivity)
        _ = _ := by ring)
  have hRHS1 : ∀ j : R,
      ∫ w, ∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) *
            (W_sh (π (σ i₀).1) ⬝ᵥ α_sh (π (σ j).1) +
              if i₀ = j then W_aux (π (σ i₀).1) ⬝ᵥ α_aux (π (σ j).1) else 0) *
            (ψ' j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S w q))) ∂γ_sh =
        ∫ a : R → α, f a *
          ((W_sh (π (a i₀)) ⬝ᵥ α_sh (π (a j)) +
              if i₀ = j then W_aux (π (a i₀)) ⬝ᵥ α_aux (π (a j)) else 0) *
            ∫ w, (∫ η : R → K_aux → ℝ,
                deriv (ϕ j) (α_sh (π (a j)) ⬝ᵥ w + α_aux (π (a j)) ⬝ᵥ η j) *
                  ∏ r ∈ Finset.univ.erase j,
                    ϕ r (α_sh (π (a r)) ⬝ᵥ w + α_aux (π (a r)) ⬝ᵥ η r)
                ∂(Measure.pi fun _ : R => γ_aux)) / Z w ^ Fintype.card R ∂γ_sh)
          ∂(Measure.pi fun _ : R => μ₀) := by
    intro j
    let C_j : ℝ := (∑ m : L, ∑ m' : L,
        (|W_sh m ⬝ᵥ α_sh m'| + |W_aux m ⬝ᵥ α_aux m'|)) *
      (|M' j| * ∏ r ∈ Finset.univ.erase j, (|M₀ r| * Real.exp B))
    have hj_fub := integral_tilted_replica_fubini μ₀ π hπ α_sh α_aux hum hB hfi
      (fun w σ => (W_sh (π (σ i₀).1) ⬝ᵥ α_sh (π (σ j).1) +
          if i₀ = j then W_aux (π (σ i₀).1) ⬝ᵥ α_aux (π (σ j).1) else 0) *
        (ψ' j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r))))
      (fun s w η => (W_sh (s i₀) ⬝ᵥ α_sh (s j) +
          if i₀ = j then W_aux (s i₀) ⬝ᵥ α_aux (s j) else 0) *
        (deriv (ϕ j) (α_sh (s j) ⬝ᵥ w + α_aux (s j) ⬝ᵥ η j) *
          ∏ r ∈ Finset.univ.erase j, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r)))
      (fun w σ => by
        rw [Real.exp_sum, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        have hd_eq : deriv (ϕ j) (S w (σ j)) = ψ' j (S w (σ j)) * Real.exp (u (S w (σ j))) :=
          hψ' j _
        have hprod_eq : (∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r))) *
            (∏ r ∈ Finset.univ.erase j, Real.exp (u (S w (σ r)))) =
            ∏ r ∈ Finset.univ.erase j, ϕ r (S w (σ r)) := by
          rw [← Finset.prod_mul_distrib]
        dsimp only [S] at hd_eq hprod_eq ⊢
        rw [hd_eq, ← hprod_eq]
        ring)
      (fun s => by
        refine measurable_const.mul ?_
        have hlin : ∀ r : R, Measurable fun q : (K_sh → ℝ) × (R → K_aux → ℝ) =>
            α_sh (s r) ⬝ᵥ q.1 + α_aux (s r) ⬝ᵥ q.2 r := fun r =>
          (Finset.measurable_sum _ fun k _ =>
            measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
            (Finset.measurable_sum _ fun k _ =>
              measurable_const.mul
                ((measurable_pi_apply k).comp ((measurable_pi_apply r).comp measurable_snd)))
        exact ((measurable_deriv _).comp (hlin j)).mul
          (Finset.measurable_prod _ fun r _ => (hψd r).continuous.measurable.comp (hlin r)))
      (bw := fun _ => C_j) (integrable_const _)
      (bη := fun _ => 0) (integrable_const _)
      (fun s w η => by
        rw [add_zero, abs_mul, abs_mul]
        have hc1 : |W_sh (s i₀) ⬝ᵥ α_sh (s j) +
            if i₀ = j then W_aux (s i₀) ⬝ᵥ α_aux (s j) else 0| ≤
            ∑ m : L, ∑ m' : L, (|W_sh m ⬝ᵥ α_sh m'| + |W_aux m ⬝ᵥ α_aux m'|) := by
          have hpair : |W_sh (s i₀) ⬝ᵥ α_sh (s j) +
              if i₀ = j then W_aux (s i₀) ⬝ᵥ α_aux (s j) else 0| ≤
              |W_sh (s i₀) ⬝ᵥ α_sh (s j)| + |W_aux (s i₀) ⬝ᵥ α_aux (s j)| := by
            refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
            split_ifs <;> simp [abs_nonneg]
          refine hpair.trans ?_
          have h1 := Finset.single_le_sum (f := fun m' : L =>
              |W_sh (s i₀) ⬝ᵥ α_sh m'| + |W_aux (s i₀) ⬝ᵥ α_aux m'|)
            (fun _ _ => by positivity) (Finset.mem_univ (s j))
          exact h1.trans (Finset.single_le_sum
            (f := fun m : L => ∑ m' : L, (|W_sh m ⬝ᵥ α_sh m'| + |W_aux m ⬝ᵥ α_aux m'|))
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ (s i₀)))
        have hc2 : |deriv (ϕ j) (α_sh (s j) ⬝ᵥ w + α_aux (s j) ⬝ᵥ η j)| *
            |∏ r ∈ Finset.univ.erase j, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r)| ≤
            |M' j| * ∏ r ∈ Finset.univ.erase j, (|M₀ r| * Real.exp B) := by
          rw [Finset.abs_prod]
          exact mul_le_mul ((hM' j _).trans (le_abs_self _))
            (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hM r _)
            (Finset.prod_nonneg fun _ _ => abs_nonneg _) (abs_nonneg _)
        rw [← mul_assoc]
        simpa only [mul_assoc] using mul_le_mul hc1 hc2 (by positivity)
          (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity))
    dsimp only at hj_fub
    have heq_lhs : (fun w => ∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) *
            (W_sh (π (σ i₀).1) ⬝ᵥ α_sh (π (σ j).1) +
              if i₀ = j then W_aux (π (σ i₀).1) ⬝ᵥ α_aux (π (σ j).1) else 0) *
            (ψ' j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S w q)))) =
        fun w => ∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) *
            ((W_sh (π (σ i₀).1) ⬝ᵥ α_sh (π (σ j).1) +
              if i₀ = j then W_aux (π (σ i₀).1) ⬝ᵥ α_aux (π (σ j).1) else 0) *
            (ψ' j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r))))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S w q))) :=
      funext fun w => integral_congr_ae (ae_of_all _ fun σ => by ring)
    rw [heq_lhs, hj_fub]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    dsimp only
    simp_rw [integral_const_mul, mul_div_assoc]
    rw [integral_const_mul]
  have hf_opt : Integrable (fun a : Option R → α => f (fun r => a (some r)))
      (Measure.pi fun _ : Option R => μ₀) :=
    (measurePreserving_pi_comp_injective μ₀
      (Option.some_injective R)).integrable_comp_of_integrable hfi
  have hRHS2 :
      ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
          f (fun r => (σ (some r)).1) *
            (W_sh (π (σ (some i₀)).1) ⬝ᵥ α_sh (π (σ none).1)) *
            (∏ r : R, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))
          ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted (fun q => u (S w q))) ∂γ_sh =
        ∫ a : R → α, f a *
          (∑ m : L, p m * (W_sh (π (a i₀)) ⬝ᵥ α_sh m) *
            ∫ w, ((∫ η : R → K_aux → ℝ,
                  ∏ r, ϕ r (α_sh (π (a r)) ⬝ᵥ w + α_aux (π (a r)) ⬝ᵥ η r)
                  ∂(Measure.pi fun _ : R => γ_aux)) *
                ∫ η₀ : K_aux → ℝ,
                  deriv u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) *
                    Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀))
                  ∂γ_aux) / Z w ^ (Fintype.card R + 1) ∂γ_sh)
          ∂(Measure.pi fun _ : R => μ₀) := by
    let C_opt : ℝ := (∑ m : L, ∑ m' : L, |W_sh m ⬝ᵥ α_sh m'|) * (C_ϕ * (|D₁| * Real.exp B))
    have hopt_fub :=
      integral_tilted_replica_fubini (ι := Option R) μ₀ π hπ α_sh α_aux hum hB hf_opt
      (fun w σ => (W_sh (π (σ (some i₀)).1) ⬝ᵥ α_sh (π (σ none).1)) *
        (∏ r : R, ψ r (S w (σ (some r)))) * deriv u (S w (σ none)))
      (fun s w η => (W_sh (s (some i₀)) ⬝ᵥ α_sh (s none)) *
        (∏ r : R, ϕ r (α_sh (s (some r)) ⬝ᵥ w + α_aux (s (some r)) ⬝ᵥ η (some r))) *
        (deriv u (α_sh (s none) ⬝ᵥ w + α_aux (s none) ⬝ᵥ η none) *
          Real.exp (u (α_sh (s none) ⬝ᵥ w + α_aux (s none) ⬝ᵥ η none))))
      (fun w σ => by
        rw [Fintype.sum_option, Real.exp_add, Real.exp_sum]
        have hprod_eq : (∏ r : R, ψ r (S w (σ (some r)))) *
            (∏ r : R, Real.exp (u (S w (σ (some r))))) =
            ∏ r : R, ϕ r (S w (σ (some r))) := by
          rw [← Finset.prod_mul_distrib]
        dsimp only [S] at hprod_eq ⊢
        rw [← hprod_eq]
        ring)
      (fun s => by
        have hlin : ∀ r : Option R, Measurable fun q : (K_sh → ℝ) × (Option R → K_aux → ℝ) =>
            α_sh (s r) ⬝ᵥ q.1 + α_aux (s r) ⬝ᵥ q.2 r := fun r =>
          (Finset.measurable_sum _ fun k _ =>
            measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
            (Finset.measurable_sum _ fun k _ =>
              measurable_const.mul
                ((measurable_pi_apply k).comp ((measurable_pi_apply r).comp measurable_snd)))
        exact (measurable_const.mul
          (Finset.measurable_prod _ fun r _ =>
            (hψd r).continuous.measurable.comp (hlin (some r)))).mul
          (((measurable_deriv u).comp (hlin none)).mul
            (Real.measurable_exp.comp (hum.comp (hlin none)))))
      (bw := fun _ => C_opt) (integrable_const _)
      (bη := fun _ => 0) (integrable_const _)
      (fun s w η => by
        rw [add_zero, abs_mul, abs_mul]
        have hc1 : |W_sh (s (some i₀)) ⬝ᵥ α_sh (s none)| ≤
            ∑ m : L, ∑ m' : L, |W_sh m ⬝ᵥ α_sh m'| := by
          have h1 := Finset.single_le_sum (f := fun m' : L => |W_sh (s (some i₀)) ⬝ᵥ α_sh m'|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ (s none))
          exact h1.trans (Finset.single_le_sum
            (f := fun m : L => ∑ m' : L, |W_sh m ⬝ᵥ α_sh m'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ (s (some i₀))))
        have hc2 : |∏ r : R,
            ϕ r (α_sh (s (some r)) ⬝ᵥ w + α_aux (s (some r)) ⬝ᵥ η (some r))| ≤ C_ϕ := by
          rw [Finset.abs_prod]
          exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hM r _
        have hc3 : |deriv u (α_sh (s none) ⬝ᵥ w + α_aux (s none) ⬝ᵥ η none) *
            Real.exp (u (α_sh (s none) ⬝ᵥ w + α_aux (s none) ⬝ᵥ η none))| ≤ |D₁| * Real.exp B :=
          abs_mul_exp_le ((hD₁ _).trans (le_abs_self _)) (le_of_abs_le (hB _))
        calc _ ≤ (∑ m : L, ∑ m' : L, |W_sh m ⬝ᵥ α_sh m'|) * C_ϕ * (|D₁| * Real.exp B) := by
              refine mul_le_mul (mul_le_mul hc1 hc2 (abs_nonneg _)
                (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _))
                hc3 (abs_nonneg _) (by positivity)
          _ = C_opt := by ring)
    dsimp only at hopt_fub
    have heq_lhs : (fun w => ∫ σ : Option R → α × (K_aux → ℝ),
          f (fun r => (σ (some r)).1) *
            (W_sh (π (σ (some i₀)).1) ⬝ᵥ α_sh (π (σ none).1)) *
            (∏ r : R, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))
          ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted (fun q => u (S w q)))) =
        fun w => ∫ σ : Option R → α × (K_aux → ℝ),
          f (fun r => (σ (some r)).1) *
            ((W_sh (π (σ (some i₀)).1) ⬝ᵥ α_sh (π (σ none).1)) *
              (∏ r : R, ψ r (S w (σ (some r)))) * deriv u (S w (σ none)))
          ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted (fun q => u (S w q))) :=
      funext fun w => integral_congr_ae (ae_of_all _ fun σ => by ring)
    rw [heq_lhs, hopt_fub]
    have h_eta_split : ∀ (a : Option R → α) (w : K_sh → ℝ),
        ∫ η : Option R → K_aux → ℝ,
          (W_sh (π (a (some i₀))) ⬝ᵥ α_sh (π (a none))) *
            (∏ r : R,
              ϕ r (α_sh (π (a (some r))) ⬝ᵥ w + α_aux (π (a (some r))) ⬝ᵥ η (some r))) *
            (deriv u (α_sh (π (a none)) ⬝ᵥ w + α_aux (π (a none)) ⬝ᵥ η none) *
              Real.exp (u (α_sh (π (a none)) ⬝ᵥ w + α_aux (π (a none)) ⬝ᵥ η none)))
          ∂(Measure.pi fun _ : Option R => γ_aux) =
        (W_sh (π (a (some i₀))) ⬝ᵥ α_sh (π (a none))) *
          ((∫ η : R → K_aux → ℝ,
              ∏ r : R, ϕ r (α_sh (π (a (some r))) ⬝ᵥ w + α_aux (π (a (some r))) ⬝ᵥ η r)
              ∂(Measure.pi fun _ : R => γ_aux)) *
            ∫ η₀ : K_aux → ℝ,
              deriv u (α_sh (π (a none)) ⬝ᵥ w + α_aux (π (a none)) ⬝ᵥ η₀) *
                Real.exp (u (α_sh (π (a none)) ⬝ᵥ w + α_aux (π (a none)) ⬝ᵥ η₀))
              ∂γ_aux) := by
      intro a w
      simp_rw [mul_assoc]
      rw [integral_const_mul]
      congr 1
      refine integral_pi_fresh_replica_mul γ_aux (Option.some_injective R)
        (fun r => Option.some_ne_none r)
        (fun η : R → K_aux → ℝ =>
          ∏ r : R, ϕ r (α_sh (π (a (some r))) ⬝ᵥ w + α_aux (π (a (some r))) ⬝ᵥ η r))
        (fun η₀ : K_aux → ℝ =>
          deriv u (α_sh (π (a none)) ⬝ᵥ w + α_aux (π (a none)) ⬝ᵥ η₀) *
            Real.exp (u (α_sh (π (a none)) ⬝ᵥ w + α_aux (π (a none)) ⬝ᵥ η₀)))
        ?_ ?_
      · refine Measurable.aestronglyMeasurable (Finset.measurable_prod _ fun r _ => ?_)
        exact (hψd r).continuous.measurable.comp
          (measurable_const.add (Finset.measurable_sum _ fun k _ => by fun_prop))
      · have hl : Measurable fun η₀ : K_aux → ℝ =>
            α_sh (π (a none)) ⬝ᵥ w + α_aux (π (a none)) ⬝ᵥ η₀ :=
          measurable_const.add (Finset.measurable_sum _ fun k _ => by fun_prop)
        exact (((measurable_deriv u).comp hl).mul
          (Real.measurable_exp.comp (hum.comp hl))).aestronglyMeasurable
    let I_m : (R → L) → L → ℝ := fun s m =>
      (W_sh (s i₀) ⬝ᵥ α_sh m) *
        ∫ w, ((∫ η : R → K_aux → ℝ,
              ∏ r : R, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r)
              ∂(Measure.pi fun _ : R => γ_aux)) *
            ∫ η₀ : K_aux → ℝ,
              deriv u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) *
                Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀))
              ∂γ_aux) / Z w ^ (Fintype.card R + 1) ∂γ_sh
    have h_a_eq : ∀ a : Option R → α,
        f (fun r => a (some r)) *
          ∫ w, (∫ η : Option R → K_aux → ℝ,
              (W_sh (π (a (some i₀))) ⬝ᵥ α_sh (π (a none))) *
                (∏ r : R,
                  ϕ r (α_sh (π (a (some r))) ⬝ᵥ w + α_aux (π (a (some r))) ⬝ᵥ η (some r))) *
                (deriv u (α_sh (π (a none)) ⬝ᵥ w + α_aux (π (a none)) ⬝ᵥ η none) *
                  Real.exp (u (α_sh (π (a none)) ⬝ᵥ w + α_aux (π (a none)) ⬝ᵥ η none)))
              ∂(Measure.pi fun _ : Option R => γ_aux)) /
            Z w ^ Fintype.card (Option R) ∂γ_sh =
        f (fun r => a (some r)) * I_m (fun r => π (a (some r))) (π (a none)) := by
      intro a
      congr 1
      dsimp only [I_m]
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      dsimp only
      rw [h_eta_split a w, Fintype.card_option, mul_div_assoc]
    have h_a_congr : ∫ a : Option R → α,
          f (fun r => a (some r)) *
            ∫ w, (∫ η : Option R → K_aux → ℝ,
                (W_sh (π (a (some i₀))) ⬝ᵥ α_sh (π (a none))) *
                  (∏ r : R,
                    ϕ r (α_sh (π (a (some r))) ⬝ᵥ w + α_aux (π (a (some r))) ⬝ᵥ η (some r))) *
                  (deriv u (α_sh (π (a none)) ⬝ᵥ w + α_aux (π (a none)) ⬝ᵥ η none) *
                    Real.exp (u (α_sh (π (a none)) ⬝ᵥ w + α_aux (π (a none)) ⬝ᵥ η none)))
                ∂(Measure.pi fun _ : Option R => γ_aux)) /
              Z w ^ Fintype.card (Option R) ∂γ_sh
          ∂(Measure.pi fun _ : Option R => μ₀) =
        ∫ a : Option R → α,
          ∑ m : L, (f (fun r => a (some r)) * I_m (fun r => π (a (some r))) m) *
            (if π (a none) = m then (1 : ℝ) else 0)
          ∂(Measure.pi fun _ : Option R => μ₀) :=
      integral_congr_ae (ae_of_all _ fun a => by
        dsimp only
        rw [h_a_eq a]
        simp)
    rw [h_a_congr]
    have h_term_int : ∀ m : L, Integrable (fun a : Option R → α =>
        (f (fun r => a (some r)) * I_m (fun r => π (a (some r))) m) *
          (if π (a none) = m then (1 : ℝ) else 0)) (Measure.pi fun _ : Option R => μ₀) := by
      intro m
      let B_Im : ℝ := ∑ s : R → L, |I_m s m|
      have hπ_opt : Measurable fun a : Option R → α => (fun r : R => π (a (some r))) :=
        measurable_pi_iff.2 fun r => hπ.comp (measurable_pi_apply (some r))
      refine (hf_opt.abs.mul_const B_Im).mono' ?_ (ae_of_all _ fun a => ?_)
      · refine (hf_opt.aestronglyMeasurable.mul ?_).mul ?_
        · exact ((measurable_of_finite fun s => I_m s m).comp hπ_opt).aestronglyMeasurable
        · exact ((measurable_of_finite fun m' : L => if m' = m then (1 : ℝ) else 0).comp
            (hπ.comp (measurable_pi_apply none))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have h1 : |if π (a none) = m then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
        have h2 : |I_m (fun r => π (a (some r))) m| ≤ B_Im :=
          Finset.single_le_sum (f := fun s => |I_m s m|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ (fun r => π (a (some r))))
        calc |f (fun r => a (some r))| * |I_m (fun r => π (a (some r))) m| *
                |if π (a none) = m then (1 : ℝ) else 0|
            ≤ |f (fun r => a (some r))| * B_Im * 1 := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) h1
                (abs_nonneg _) (mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans h2))
          _ = |f (fun r => a (some r))| * B_Im := mul_one _
    rw [integral_finsetSum _ fun m _ => h_term_int m]
    have h_each_m : ∀ m : L,
        ∫ a : Option R → α,
          (f (fun r => a (some r)) * I_m (fun r => π (a (some r))) m) *
            (if π (a none) = m then (1 : ℝ) else 0)
          ∂(Measure.pi fun _ : Option R => μ₀) =
        ∫ a : R → α, f a * (p m * I_m (fun r => π (a r)) m) ∂(Measure.pi fun _ : R => μ₀) := by
      intro m
      rw [integral_pi_fresh_replica_mul μ₀ (Option.some_injective R)
        (fun r => Option.some_ne_none r)
        (fun a : R → α => f a * I_m (fun r => π (a r)) m)
        (fun x : α => if π x = m then (1 : ℝ) else 0)
        (hfi.aestronglyMeasurable.mul
          ((measurable_of_finite fun s => I_m s m).comp
            (measurable_pi_iff.2 fun r => hπ.comp (measurable_pi_apply r))).aestronglyMeasurable)
        (((measurable_of_finite fun m' : L => if m' = m then (1 : ℝ) else 0).comp
          hπ).aestronglyMeasurable)]
      have hprob_m : ∫ x : α, (if π x = m then (1 : ℝ) else 0) ∂μ₀ = p m := by
        rw [← integral_map hπ.aemeasurable
          (measurable_of_finite fun m' : L => if m' = m then (1 : ℝ) else 0).aestronglyMeasurable,
          integral_fintype Integrable.of_finite]
        simp [p, smul_eq_mul]
      rw [hprob_m, ← integral_mul_const]
      exact integral_congr_ae (ae_of_all _ fun a => by ring)
    simp_rw [h_each_m]
    have h_a_int : ∀ m : L, Integrable (fun a : R → α => f a * (p m * I_m (fun r => π (a r)) m))
        (Measure.pi fun _ : R => μ₀) := by
      intro m
      have hπ_r : Measurable fun a : R → α => (fun r : R => π (a r)) :=
        measurable_pi_iff.2 fun r => hπ.comp (measurable_pi_apply r)
      exact (hfi.bdd_mul_of_abs_le
        ((measurable_of_finite fun s : R → L => p m * I_m s m).comp hπ_r).aestronglyMeasurable
        (ae_of_all _ fun a => Finset.single_le_sum (f := fun s => |p m * I_m s m|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ (fun r => π (a r))))).congr
        (ae_of_all _ fun a => mul_comm _ _)
    rw [← integral_finsetSum _ fun m _ => h_a_int m]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    dsimp only
    rw [← Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun m _ => by dsimp only [I_m]; ring
  dsimp only at hLHS
  have hLHS' : ∫ w, ∫ σ : R → α × (K_aux → ℝ),
        f (fun r => (σ r).1) * Wt w (σ i₀) * (∏ r, ψ r (S w (σ r)))
        ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S w q))) ∂γ_sh =
      ∫ a : R → α, f a *
        ∫ w, (∫ η : R → K_aux → ℝ,
            (W_sh (π (a i₀)) ⬝ᵥ w + W_aux (π (a i₀)) ⬝ᵥ η i₀) *
              (∏ r, ϕ r (α_sh (π (a r)) ⬝ᵥ w + α_aux (π (a r)) ⬝ᵥ η r))
            ∂(Measure.pi fun _ : R => γ_aux)) / Z w ^ Fintype.card R ∂γ_sh
        ∂(Measure.pi fun _ : R => μ₀) :=
    (integral_congr_ae (ae_of_all _ fun w =>
      integral_congr_ae (ae_of_all _ fun σ => mul_assoc _ _ _))).trans hLHS
  rw [hLHS', Finset.sum_congr rfl fun j _ => hRHS1 j, hRHS2]
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : R → (R → L) → ℝ, ∀ j s, g₁ j s =
      (W_sh (s i₀) ⬝ᵥ α_sh (s j) + if i₀ = j then W_aux (s i₀) ⬝ᵥ α_aux (s j) else 0) *
        ∫ w, (∫ η : R → K_aux → ℝ,
            deriv (ϕ j) (α_sh (s j) ⬝ᵥ w + α_aux (s j) ⬝ᵥ η j) *
              ∏ r ∈ Finset.univ.erase j, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r)
            ∂(Measure.pi fun _ : R => γ_aux)) / Z w ^ Fintype.card R ∂γ_sh :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨g₂, hg₂⟩ : ∃ g₂ : (R → L) → ℝ, ∀ s, g₂ s =
      ∑ m : L, p m * (W_sh (s i₀) ⬝ᵥ α_sh m) *
        ∫ w, ((∫ η : R → K_aux → ℝ,
              ∏ r, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r)
              ∂(Measure.pi fun _ : R => γ_aux)) *
            ∫ η₀ : K_aux → ℝ,
              deriv u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) *
                Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀))
              ∂γ_aux) / Z w ^ (Fintype.card R + 1) ∂γ_sh :=
    ⟨_, fun _ => rfl⟩
  have hR1_fold : ∀ j : R,
      (∫ a : R → α, f a *
        ((W_sh (π (a i₀)) ⬝ᵥ α_sh (π (a j)) +
            if i₀ = j then W_aux (π (a i₀)) ⬝ᵥ α_aux (π (a j)) else 0) *
          ∫ w, (∫ η : R → K_aux → ℝ,
              deriv (ϕ j) (α_sh (π (a j)) ⬝ᵥ w + α_aux (π (a j)) ⬝ᵥ η j) *
                ∏ r ∈ Finset.univ.erase j, ϕ r (α_sh (π (a r)) ⬝ᵥ w + α_aux (π (a r)) ⬝ᵥ η r)
              ∂(Measure.pi fun _ : R => γ_aux)) / Z w ^ Fintype.card R ∂γ_sh)
        ∂(Measure.pi fun _ : R => μ₀)) =
      ∫ a : R → α, f a * g₁ j (fun r => π (a r)) ∂(Measure.pi fun _ : R => μ₀) :=
    fun j => integral_congr_ae (ae_of_all _ fun a => by dsimp only; rw [hg₁])
  have hR2_fold :
      (∫ a : R → α, f a *
        (∑ m : L, p m * (W_sh (π (a i₀)) ⬝ᵥ α_sh m) *
          ∫ w, ((∫ η : R → K_aux → ℝ,
                ∏ r, ϕ r (α_sh (π (a r)) ⬝ᵥ w + α_aux (π (a r)) ⬝ᵥ η r)
                ∂(Measure.pi fun _ : R => γ_aux)) *
              ∫ η₀ : K_aux → ℝ,
                deriv u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) *
                  Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀))
                ∂γ_aux) / Z w ^ (Fintype.card R + 1) ∂γ_sh)
        ∂(Measure.pi fun _ : R => μ₀)) =
      ∫ a : R → α, f a * g₂ (fun r => π (a r)) ∂(Measure.pi fun _ : R => μ₀) :=
    integral_congr_ae (ae_of_all _ fun a => by dsimp only; rw [hg₂])
  rw [Finset.sum_congr rfl fun j _ => hR1_fold j, hR2_fold]
  have hπ_vec : Measurable fun a : R → α => (fun r => π (a r)) :=
    measurable_pi_iff.2 fun r => hπ.comp (measurable_pi_apply r)
  have h_bdd_int : ∀ g : (R → L) → ℝ, Integrable (fun a : R → α => f a * g (fun r => π (a r)))
      (Measure.pi fun _ : R => μ₀) := fun g =>
    (hfi.bdd_mul_of_abs_le ((measurable_of_finite g).comp hπ_vec).aestronglyMeasurable
      (ae_of_all _ fun a => Finset.single_le_sum (f := fun s => |g s|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ _))).congr
      (ae_of_all _ fun a => mul_comm _ _)
  rw [← integral_finsetSum _ fun j _ => h_bdd_int (g₁ j), ← integral_const_mul,
    ← integral_sub (integrable_finsetSum _ fun j _ => h_bdd_int (g₁ j))
      ((h_bdd_int g₂).const_mul _)]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  dsimp only
  rw [← Finset.mul_sum, mul_left_comm (Fintype.card R : ℝ) (f a), ← mul_sub]
  congr 1
  simp_rw [hg₁, hg₂]
  exact stein_ratio_fixed_spins p hp0 hp1 α_sh W_sh α_aux W_aux hu hB hD₁ ϕ hψd hM hM' i₀
    (fun r => π (a r))

end SpinGlasses
