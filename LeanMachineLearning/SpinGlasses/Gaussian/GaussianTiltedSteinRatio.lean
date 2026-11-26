/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Data.Finset.SumBound
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

* `SpinGlasses.stein_tilted_replica_ratio`: first-order Stein identity integrated over an
  arbitrary old-state probability law `μ₀` and an integrable `R`-replica observable `f`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace SpinGlasses

/-- **Lower bound for a mixture of Gaussian exponential moments.** If `|G m η| ≤ B` and the weights
`p` form a probability vector, then `∑ m, p m * ∫ exp (G m η) dγ ≥ exp (-B)`. -/
lemma exp_neg_le_sum_mul_integral_exp {L K : Type*} [Fintype L] [Fintype K]
    (p : L → ℝ) (hp : ∀ m, 0 ≤ p m) (hp1 : ∑ m, p m = 1) {B : ℝ}
    (G : L → (K → ℝ) → ℝ) (hB : ∀ m η, |G m η| ≤ B)
    (hint : ∀ m, Integrable (fun η => Real.exp (G m η))
      (Measure.pi fun _ : K => gaussianReal 0 1)) :
    Real.exp (-B) ≤
      ∑ m, p m * ∫ η, Real.exp (G m η) ∂(Measure.pi fun _ : K => gaussianReal 0 1) := by
  have hlow : ∀ m, Real.exp (-B) ≤
      ∫ η, Real.exp (G m η) ∂(Measure.pi fun _ : K => gaussianReal 0 1) := fun m => by
    have hm := integral_mono (integrable_const (Real.exp (-B))) (hint m)
      fun η => Real.exp_le_exp.2 (neg_le_of_abs_le (hB m η))
    simpa using hm
  calc Real.exp (-B) = (∑ m, p m) * Real.exp (-B) := by rw [hp1, one_mul]
    _ = ∑ m, p m * Real.exp (-B) := Finset.sum_mul _ _ _
    _ ≤ _ := Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hlow m) (hp m)

/-- **Upper bound for a mixture of Gaussian exponential moments.** If `|G m η| ≤ B` and the weights
`p` form a probability vector, then `∑ m, p m * ∫ exp (G m η) dγ ≤ exp B`. -/
lemma sum_mul_integral_exp_le_exp {L K : Type*} [Fintype L] [Fintype K]
    (p : L → ℝ) (hp : ∀ m, 0 ≤ p m) (hp1 : ∑ m, p m = 1) {B : ℝ}
    (G : L → (K → ℝ) → ℝ) (hB : ∀ m η, |G m η| ≤ B)
    (hint : ∀ m, Integrable (fun η => Real.exp (G m η))
      (Measure.pi fun _ : K => gaussianReal 0 1)) :
    (∑ m, p m * ∫ η, Real.exp (G m η) ∂(Measure.pi fun _ : K => gaussianReal 0 1)) ≤
      Real.exp B := by
  have hup : ∀ m,
      ∫ η, Real.exp (G m η) ∂(Measure.pi fun _ : K => gaussianReal 0 1) ≤ Real.exp B := fun m => by
    have hm := integral_mono (hint m) (integrable_const (Real.exp B))
      fun η => Real.exp_le_exp.2 (le_of_abs_le (hB m η))
    simpa using hm
  calc (∑ m, p m * ∫ η, Real.exp (G m η) ∂(Measure.pi fun _ : K => gaussianReal 0 1))
      ≤ ∑ m, p m * Real.exp B := Finset.sum_le_sum fun m _ =>
          mul_le_mul_of_nonneg_left (hup m) (hp m)
    _ = (∑ m, p m) * Real.exp B := (Finset.sum_mul _ _ _).symm
    _ = Real.exp B := by rw [hp1, one_mul]

lemma hasFDerivAt_Z_sum {L K_aux : Type*} [Fintype L] [DecidableEq L] [Fintype K_aux]
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) {B D₁ : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (p : L → ℝ) (hp : ∀ m, 0 ≤ p m) (hp1 : ∑ m, p m = 1) (c : L → K_aux → ℝ) :
    let γ_aux := Measure.pi fun _ : K_aux => gaussianReal 0 1
    let Z : (L → ℝ) → ℝ := fun y =>
      ∑ m : L, p m * ∫ η, Real.exp (u (y m + c m ⬝ᵥ η)) ∂γ_aux
    Differentiable ℝ Z ∧
      (∀ y, Real.exp (-B) ≤ Z y) ∧
      (∀ y, Z y ≤ Real.exp B) ∧
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
  refine ⟨fun y => (hZd y).differentiableAt, ?_, ?_, ?_, ?_⟩
  · intro y
    exact exp_neg_le_sum_mul_integral_exp p hp hp1 (fun m η => u (y m + c m ⬝ᵥ η))
      (fun _ _ => hB _) fun m => hexpi m (y m)
  · intro y
    exact sum_mul_integral_exp_le_exp p hp hp1 (fun m η => u (y m + c m ⬝ᵥ η))
      (fun _ _ => hB _) fun m => hexpi m (y m)
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

/-- **First-order Gaussian integration by parts of a normalized replica ratio multiplied by
`G(log Z(w))` at fixed spin labels.** The reusable interface is
`stein_tilted_replica_ratio_mul_comp_log` (and `stein_tilted_replica_ratio` for `G = 1`). -/
theorem stein_ratio_comp_log_fixed_spins
    {L K_sh K_aux R : Type*} [Fintype L]
    [Fintype K_sh] [Fintype K_aux] [Fintype R] [DecidableEq R]
    (p : L → ℝ) (hp : ∀ m, 0 ≤ p m) (hp1 : ∑ m, p m = 1)
    (α_sh W_sh : L → K_sh → ℝ) (α_aux W_aux : L → K_aux → ℝ)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) {B D₁ : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (ϕ : R → ℝ → ℝ) (hϕ : ∀ r, Differentiable ℝ (ϕ r))
    {M M' : R → ℝ} (hM : ∀ r x, |ϕ r x| ≤ M r) (hM' : ∀ r x, |deriv (ϕ r) x| ≤ M' r)
    {G : ℝ → ℝ} (hG : Differentiable ℝ G) {CG CG' : ℝ}
    (hGb : ∀ t ∈ Set.Icc (-B) B, |G t| ≤ CG)
    (hGd : ∀ t ∈ Set.Icc (-B) B, |deriv G t| ≤ CG')
    (i₀ : R) (s : R → L) :
    let γ_sh := Measure.pi fun _ : K_sh => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : K_aux => gaussianReal 0 1
    let Z (w : K_sh → ℝ) : ℝ :=
      ∑ m : L, p m * ∫ η, Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η)) ∂γ_aux
    ∫ w, ((∫ η : R → K_aux → ℝ,
        (W_sh (s i₀) ⬝ᵥ w + W_aux (s i₀) ⬝ᵥ η i₀) *
          (∏ r, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r))
        ∂(Measure.pi fun _ : R => γ_aux)) / Z w ^ Fintype.card R) *
        G (Real.log (Z w)) ∂γ_sh =
      ∑ j : R, (W_sh (s i₀) ⬝ᵥ α_sh (s j) +
          if i₀ = j then W_aux (s i₀) ⬝ᵥ α_aux (s j) else 0) *
        ∫ w, ((∫ η : R → K_aux → ℝ,
          deriv (ϕ j) (α_sh (s j) ⬝ᵥ w + α_aux (s j) ⬝ᵥ η j) *
            ∏ r ∈ Finset.univ.erase j, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r)
          ∂(Measure.pi fun _ : R => γ_aux)) / Z w ^ Fintype.card R) *
          G (Real.log (Z w)) ∂γ_sh +
      ∑ m : L, p m * (W_sh (s i₀) ⬝ᵥ α_sh m) *
        ∫ w, (((∫ η : R → K_aux → ℝ,
              ∏ r, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r)
              ∂(Measure.pi fun _ : R => γ_aux)) *
            ∫ η₀ : K_aux → ℝ,
              deriv u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) *
                Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀))
              ∂γ_aux) / Z w ^ (Fintype.card R + 1)) *
          (deriv G (Real.log (Z w)) - (Fintype.card R : ℝ) * G (Real.log (Z w))) ∂γ_sh := by
  classical
  intro γ_sh γ_aux Z
  let K_tot := K_sh ⊕ (R × K_aux)
  let γ_tot := Measure.pi fun _ : K_tot => gaussianReal 0 1
  have hmp_aux : MeasurePreserving ⇑(MeasurableEquiv.curry R K_aux ℝ)
      (Measure.pi fun _ : R × K_aux => gaussianReal 0 1)
      (Measure.pi fun _ : R => γ_aux) :=
    (measurePreserving_curry_symm (ι := R) (κ := K_aux) fun _ _ => gaussianReal 0 1).symm
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
  obtain ⟨hZd, hZb, hZu, hZder, hZdb⟩ := hasFDerivAt_Z_sum hu hB hD₁ p hp hp1 α_aux
  have hGb' : ∀ t ∈ Set.Icc (Real.log (Real.exp (-B))) (Real.log (Real.exp B)), |G t| ≤ CG := by
    simpa only [Real.log_exp] using hGb
  have hGd' : ∀ t ∈ Set.Icc (Real.log (Real.exp (-B))) (Real.log (Real.exp B)),
      |deriv G t| ≤ CG' := by
    simpa only [Real.log_exp] using hGd
  have hstein := integral_mul_div_pow_mul_comp_log_eq_sum (P := γ_tot)
    (W := fun k ξ => cW k ⬝ᵥ ξ) (X := fun r ξ => cX r ⬝ᵥ ξ) (Y := fun m ξ => cY m ⬝ᵥ ξ)
    hgauss (i := ())
    (integral_dotProduct_pi_gaussianReal _)
    (fun r => integral_dotProduct_pi_gaussianReal _)
    (fun m => integral_dotProduct_pi_gaussianReal _)
    hFd hFb hFdb
    hZd (Real.exp_pos (-B)) hZb hZu hZdb
    (fun t _ => hG t) hGb' hGd'
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
  have h_push : ∀ (H : (K_sh → ℝ) × (R → K_aux → ℝ) → ℝ),
      Measurable H → Integrable (fun ξ => H (e_tot ξ)) γ_tot →
      ∫ ξ, H (e_tot ξ) ∂γ_tot =
        ∫ w, ∫ η, H (w, η) ∂(Measure.pi fun _ : R => γ_aux) ∂γ_sh := by
    intro H hHm hHi
    have hHi' : Integrable H (γ_sh.prod (Measure.pi fun _ : R => γ_aux)) := by
      rw [← hmp_tot.map_eq, integrable_map_measure hHm.aestronglyMeasurable
        e_tot.measurable.aemeasurable]
      exact hHi
    rw [hmp_tot.integral_comp_of_aestronglyMeasurable hHi'.aestronglyMeasurable,
      integral_prod _ hHi']
  have hZm : Measurable Z := by
    have hm_lin : Measurable fun (w : K_sh → ℝ) (m : L) => α_sh m ⬝ᵥ w :=
      measurable_pi_iff.2 fun m => by simp only [dotProduct]; fun_prop
    exact hZd.continuous.measurable.comp hm_lin
  have hZ_tot : ∀ ξ : K_tot → ℝ,
      (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux) = Z (e_tot ξ).1 :=
    fun ξ => Finset.sum_congr rfl fun m _ => by rw [hY_e]
  have hZ_pos : ∀ w, 0 < Z w := fun w => (Real.exp_pos (-B)).trans_le (hZb (fun m => α_sh m ⬝ᵥ w))
  have hZ_mem : ∀ w, Real.log (Z w) ∈ Set.Icc (-B) B := fun w =>
    ⟨by simpa using Real.log_le_log (Real.exp_pos (-B)) (hZb (fun m => α_sh m ⬝ᵥ w)),
     by simpa using Real.log_le_log (hZ_pos w) (hZu (fun m => α_sh m ⬝ᵥ w))⟩
  have hCG0 : 0 ≤ CG := (abs_nonneg _).trans (hGb _ (hZ_mem 0))
  have hCG'0 : 0 ≤ CG' := (abs_nonneg _).trans (hGd _ (hZ_mem 0))
  obtain ⟨lhsFun, hlhsFun⟩ : ∃ lhsFun : (K_sh → ℝ) × (R → K_aux → ℝ) → ℝ, ∀ q, lhsFun q =
      (W_sh (s i₀) ⬝ᵥ q.1 + W_aux (s i₀) ⬝ᵥ q.2 i₀) *
        (((∏ r, ϕ r (α_sh (s r) ⬝ᵥ q.1 + α_aux (s r) ⬝ᵥ q.2 r)) / Z q.1 ^ Fintype.card R) *
          G (Real.log (Z q.1))) :=
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
    have hZ1 : Measurable fun q : (K_sh → ℝ) × (R → K_aux → ℝ) => Z q.1 := hZm.comp measurable_fst
    exact h1.mul ((h2.div (hZ1.pow_const _)).mul
      (hG.continuous.measurable.comp (Real.measurable_log.comp hZ1)))
  have hlhs_eq : ∀ ξ, cW () ⬝ᵥ ξ * (((∏ r, ϕ r (cX r ⬝ᵥ ξ)) /
      (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux) ^ Fintype.card R) *
      G (Real.log (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux))) =
      lhsFun (e_tot ξ) := fun ξ => by
    rw [hlhsFun, hW_e, hZ_tot]
    congr 3
    exact Finset.prod_congr rfl fun r _ => by rw [hX_e]
  have hlhs_i : Integrable (fun ξ => lhsFun (e_tot ξ)) γ_tot := by
    have hw_int : Integrable (fun ξ : K_tot → ℝ => cW () ⬝ᵥ ξ) γ_tot :=
      ((hasGaussianLaw_dotProduct_family cW).eval ()).integrable
    have hrm : Measurable fun ξ : K_tot → ℝ => ((∏ r, ϕ r (cX r ⬝ᵥ ξ)) /
        (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux) ^
          Fintype.card R) *
        G (Real.log (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux)) := by
      have h1 : Measurable fun ξ : K_tot → ℝ => ∏ r, ϕ r (cX r ⬝ᵥ ξ) :=
        Finset.measurable_prod _ fun r _ =>
          (hϕ r).continuous.measurable.comp
            (by refine Finset.measurable_sum _ fun x _ => ?_; fun_prop)
      have h2 : Measurable fun ξ : K_tot → ℝ => Z (e_tot ξ).1 :=
        hZm.comp (measurable_fst.comp e_tot.measurable)
      simp_rw [hZ_tot]
      exact (h1.div (h2.pow_const _)).mul
        (hG.continuous.measurable.comp (Real.measurable_log.comp h2))
    have hrb : ∀ ξ : K_tot → ℝ, |((∏ r, ϕ r (cX r ⬝ᵥ ξ)) /
        (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux) ^
          Fintype.card R) *
        G (Real.log (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux))| ≤
        ((∏ r, |M r|) / Real.exp (-B) ^ Fintype.card R) * CG := fun ξ => by
      simp_rw [hZ_tot]
      rw [abs_mul, abs_div, abs_of_pos (pow_pos (hZ_pos _) _)]
      exact mul_le_mul
        (div_le_div₀ (Finset.prod_nonneg fun _ _ => abs_nonneg _) (hFb _)
          (pow_pos (Real.exp_pos _) _) (pow_le_pow_left₀ (Real.exp_pos _).le (hZb _) _))
        (hGb _ (hZ_mem _)) (abs_nonneg _) (by positivity)
    have := hw_int.bdd_mul_of_abs_le hrm.aestronglyMeasurable (ae_of_all _ hrb)
    exact this.congr (ae_of_all _ fun ξ => by dsimp; rw [mul_comm, hlhs_eq])
  have hLHS : ∫ ξ, cW () ⬝ᵥ ξ * (((∏ r, ϕ r (cX r ⬝ᵥ ξ)) /
      (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux) ^ Fintype.card R) *
      G (Real.log (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux)))
      ∂γ_tot =
    ∫ w, ((∫ η : R → K_aux → ℝ,
        (W_sh (s i₀) ⬝ᵥ w + W_aux (s i₀) ⬝ᵥ η i₀) *
          (∏ r, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r))
        ∂(Measure.pi fun _ : R => γ_aux)) / Z w ^ Fintype.card R) *
      G (Real.log (Z w)) ∂γ_sh := by
    simp_rw [hlhs_eq]
    rw [h_push lhsFun hlhs_m hlhs_i]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    have hpt : ∀ η, lhsFun (w, η) =
        (((W_sh (s i₀) ⬝ᵥ w + W_aux (s i₀) ⬝ᵥ η i₀) *
          ∏ r, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r)) / Z w ^ Fintype.card R) *
          G (Real.log (Z w)) := fun η => by rw [hlhsFun]; ring
    simp_rw [hpt]
    rw [integral_mul_const, integral_div]
  have hRHS1 : ∀ j : R, ∫ ξ,
      ((fderiv ℝ (fun x => ∏ r, ϕ r (x r)) (fun k => cX k ⬝ᵥ ξ)) (Pi.single j 1) /
        (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux) ^ Fintype.card R) *
      G (Real.log (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux))
      ∂γ_tot =
    ∫ w, ((∫ η : R → K_aux → ℝ,
        deriv (ϕ j) (α_sh (s j) ⬝ᵥ w + α_aux (s j) ⬝ᵥ η j) *
          ∏ r ∈ Finset.univ.erase j, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r)
        ∂(Measure.pi fun _ : R => γ_aux)) / Z w ^ Fintype.card R) *
      G (Real.log (Z w)) ∂γ_sh := by
    intro j
    obtain ⟨rhs1Fun, hrhs1Fun⟩ : ∃ rhs1Fun : (K_sh → ℝ) × (R → K_aux → ℝ) → ℝ, ∀ q, rhs1Fun q =
        ((deriv (ϕ j) (α_sh (s j) ⬝ᵥ q.1 + α_aux (s j) ⬝ᵥ q.2 j) *
          ∏ r ∈ Finset.univ.erase j, ϕ r (α_sh (s r) ⬝ᵥ q.1 + α_aux (s r) ⬝ᵥ q.2 r)) /
          Z q.1 ^ Fintype.card R) * G (Real.log (Z q.1)) := ⟨_, fun _ => rfl⟩
    have hr1_m : Measurable rhs1Fun := by
      rw [show rhs1Fun = _ from funext hrhs1Fun]
      have h1 : Measurable fun q : (K_sh → ℝ) × (R → K_aux → ℝ) =>
          deriv (ϕ j) (α_sh (s j) ⬝ᵥ q.1 + α_aux (s j) ⬝ᵥ q.2 j) :=
        (measurable_deriv _).comp (by simp only [dotProduct]; fun_prop)
      have h2 : Measurable fun q : (K_sh → ℝ) × (R → K_aux → ℝ) =>
          ∏ r ∈ Finset.univ.erase j, ϕ r (α_sh (s r) ⬝ᵥ q.1 + α_aux (s r) ⬝ᵥ q.2 r) :=
        Finset.measurable_prod _ fun r _ =>
          (hϕ r).continuous.measurable.comp (by simp only [dotProduct]; fun_prop)
      have hZ1 : Measurable fun q : (K_sh → ℝ) × (R → K_aux → ℝ) => Z q.1 := hZm.comp measurable_fst
      exact ((h1.mul h2).div (hZ1.pow_const _)).mul
        (hG.continuous.measurable.comp (Real.measurable_log.comp hZ1))
    have hr1_eq : ∀ ξ,
        ((fderiv ℝ (fun x => ∏ r, ϕ r (x r)) (fun k => cX k ⬝ᵥ ξ)) (Pi.single j 1) /
          (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux) ^
            Fintype.card R) *
        G (Real.log (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux)) =
        rhs1Fun (e_tot ξ) := fun ξ => by
      rw [hFder, hrhs1Fun, hZ_tot]
      simp only [hX_e]
    have hr1_i : Integrable (fun ξ => rhs1Fun (e_tot ξ)) γ_tot := by
      refine Integrable.of_bound (C := ((|M' j| * ∏ r ∈ Finset.univ.erase j, |M r|) /
          Real.exp (-B) ^ Fintype.card R) * CG)
        (hr1_m.comp e_tot.measurable).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
      rw [Real.norm_eq_abs, ← hr1_eq, abs_mul, abs_div,
        abs_of_pos (pow_pos (Real.exp_pos (-B) |>.trans_le (hZb _)) _)]
      simp_rw [hZ_tot]
      exact mul_le_mul
        (div_le_div₀ (by positivity) (hFdb j _) (pow_pos (Real.exp_pos _) _)
          (pow_le_pow_left₀ (Real.exp_pos _).le (hZb _) _))
        (hGb _ (hZ_mem _)) (abs_nonneg _) (by positivity)
    simp_rw [hr1_eq]
    rw [h_push rhs1Fun hr1_m hr1_i]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp_rw [hrhs1Fun]
    rw [integral_mul_const, integral_div]
  have hRHS2 : ∀ m : L, ∫ ξ,
      ((∏ r, ϕ r (cX r ⬝ᵥ ξ)) *
        (fderiv ℝ (fun y => ∑ m' : L, p m' * ∫ η, Real.exp (u (y m' + α_aux m' ⬝ᵥ η)) ∂γ_aux)
          (fun k => cY k ⬝ᵥ ξ)) (Pi.single m 1) /
      (∑ m' : L, p m' * ∫ η, Real.exp (u (cY m' ⬝ᵥ ξ + α_aux m' ⬝ᵥ η)) ∂γ_aux) ^
        (Fintype.card R + 1)) *
      (deriv G (Real.log (∑ m' : L, p m' * ∫ η,
          Real.exp (u (cY m' ⬝ᵥ ξ + α_aux m' ⬝ᵥ η)) ∂γ_aux)) -
        (Fintype.card R : ℝ) * G (Real.log (∑ m' : L, p m' * ∫ η,
          Real.exp (u (cY m' ⬝ᵥ ξ + α_aux m' ⬝ᵥ η)) ∂γ_aux))) ∂γ_tot =
    p m * ∫ w, (((∫ η : R → K_aux → ℝ,
          ∏ r, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r) ∂(Measure.pi fun _ : R => γ_aux)) *
        ∫ η₀ : K_aux → ℝ,
          deriv u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) *
            Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀))
          ∂γ_aux) / Z w ^ (Fintype.card R + 1)) *
      (deriv G (Real.log (Z w)) - (Fintype.card R : ℝ) * G (Real.log (Z w))) ∂γ_sh := by
    intro m
    obtain ⟨rhs2Fun, hrhs2Fun⟩ : ∃ rhs2Fun : (K_sh → ℝ) × (R → K_aux → ℝ) → ℝ, ∀ q, rhs2Fun q =
        p m * ((((∏ r, ϕ r (α_sh (s r) ⬝ᵥ q.1 + α_aux (s r) ⬝ᵥ q.2 r)) *
          (∫ η₀ : K_aux → ℝ,
            deriv u (α_sh m ⬝ᵥ q.1 + α_aux m ⬝ᵥ η₀) *
              Real.exp (u (α_sh m ⬝ᵥ q.1 + α_aux m ⬝ᵥ η₀))
            ∂γ_aux)) / Z q.1 ^ (Fintype.card R + 1)) *
          (deriv G (Real.log (Z q.1)) - (Fintype.card R : ℝ) * G (Real.log (Z q.1)))) :=
      ⟨_, fun _ => rfl⟩
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
      have hZ1 : Measurable fun q : (K_sh → ℝ) × (R → K_aux → ℝ) => Z q.1 := hZm.comp measurable_fst
      have hGsub : Measurable fun q : (K_sh → ℝ) × (R → K_aux → ℝ) =>
          deriv G (Real.log (Z q.1)) - (Fintype.card R : ℝ) * G (Real.log (Z q.1)) :=
        ((measurable_deriv G).comp (Real.measurable_log.comp hZ1)).sub
          ((hG.continuous.measurable.comp (Real.measurable_log.comp hZ1)).const_mul _)
      exact (((h1.mul h2).div (hZ1.pow_const _)).mul hGsub).const_mul _
    have hr2_eq : ∀ ξ, ((∏ r, ϕ r (cX r ⬝ᵥ ξ)) *
        (fderiv ℝ (fun y => ∑ m' : L, p m' * ∫ η, Real.exp (u (y m' + α_aux m' ⬝ᵥ η)) ∂γ_aux)
          (fun k => cY k ⬝ᵥ ξ)) (Pi.single m 1) /
        (∑ m' : L, p m' * ∫ η, Real.exp (u (cY m' ⬝ᵥ ξ + α_aux m' ⬝ᵥ η)) ∂γ_aux) ^
          (Fintype.card R + 1)) *
        (deriv G (Real.log (∑ m' : L, p m' * ∫ η,
            Real.exp (u (cY m' ⬝ᵥ ξ + α_aux m' ⬝ᵥ η)) ∂γ_aux)) -
          (Fintype.card R : ℝ) * G (Real.log (∑ m' : L, p m' * ∫ η,
            Real.exp (u (cY m' ⬝ᵥ ξ + α_aux m' ⬝ᵥ η)) ∂γ_aux))) =
        rhs2Fun (e_tot ξ) := fun ξ => by
      rw [hZder, hrhs2Fun, hZ_tot]
      simp only [hX_e, hY_e]
      ring
    have hr2_i : Integrable (fun ξ => rhs2Fun (e_tot ξ)) γ_tot := by
      refine Integrable.of_bound (C := ((∏ r, |M r|) * (p m * (|D₁| * Real.exp B)) /
          Real.exp (-B) ^ (Fintype.card R + 1)) * (CG' + (Fintype.card R : ℝ) * CG))
        (hr2_m.comp e_tot.measurable).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
      rw [Real.norm_eq_abs, ← hr2_eq]
      simp_rw [hZ_tot]
      rw [abs_mul, abs_div, abs_mul, abs_of_pos (pow_pos (hZ_pos _) _)]
      have hfrac : |(∏ r, ϕ r (cX r ⬝ᵥ ξ))| *
          |(fderiv ℝ (fun y => ∑ m' : L, p m' * ∫ η, Real.exp (u (y m' + α_aux m' ⬝ᵥ η)) ∂γ_aux)
            (fun k => cY k ⬝ᵥ ξ)) (Pi.single m 1)| /
          Z (e_tot ξ).1 ^ (Fintype.card R + 1) ≤
          (∏ r, |M r|) * (p m * (|D₁| * Real.exp B)) / Real.exp (-B) ^ (Fintype.card R + 1) :=
        div_le_div₀ (mul_nonneg (Finset.prod_nonneg fun _ _ => abs_nonneg _)
            (mul_nonneg (hp m) (by positivity)))
          (mul_le_mul (hFb _) (hZdb m _) (abs_nonneg _)
            (Finset.prod_nonneg fun _ _ => abs_nonneg _))
          (pow_pos (Real.exp_pos _) _)
          (pow_le_pow_left₀ (Real.exp_pos _).le (hZb _) _)
      have hdG_sub : |deriv G (Real.log (Z (e_tot ξ).1)) -
          (Fintype.card R : ℝ) * G (Real.log (Z (e_tot ξ).1))| ≤
          CG' + (Fintype.card R : ℝ) * CG := by
        refine (abs_sub _ _).trans (add_le_add (hGd _ (hZ_mem _)) ?_)
        rw [abs_mul, Nat.abs_cast]
        exact mul_le_mul_of_nonneg_left (hGb _ (hZ_mem _)) (Nat.cast_nonneg _)
      have hnum_nn : 0 ≤ (∏ r, |M r|) * (p m * (|D₁| * Real.exp B)) /
          Real.exp (-B) ^ (Fintype.card R + 1) :=
        div_nonneg (mul_nonneg (Finset.prod_nonneg fun _ _ => abs_nonneg _)
          (mul_nonneg (hp m) (by positivity))) (pow_nonneg (Real.exp_pos _).le _)
      exact mul_le_mul hfrac hdG_sub (abs_nonneg _) hnum_nn
    simp_rw [hr2_eq]
    rw [h_push rhs2Fun hr2_m hr2_i]
    simp_rw [hrhs2Fun, integral_const_mul]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    dsimp only
    rw [integral_mul_const, integral_div, integral_mul_const]
  rw [← hLHS, hstein]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcovX j, hRHS1 j]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [hcovY m, hRHS2 m]
    ring

/-- **First-order Gaussian integration by parts of a normalized replica ratio at fixed spin
labels** (`G = 1` specialization). -/
private theorem stein_ratio_fixed_spins
    {L K_sh K_aux R : Type*} [Fintype L]
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
  intro γ_sh γ_aux Z
  have h := stein_ratio_comp_log_fixed_spins p hp hp1 α_sh W_sh α_aux W_aux hu hB hD₁ ϕ hϕ hM hM'
    (G := fun _ => (1 : ℝ)) (differentiable_const 1)
    (CG := 1) (CG' := 0) (fun _ _ => by simp) (fun _ _ => by simp) i₀ s
  dsimp only at h
  simp only [deriv_const', mul_one, zero_sub, mul_neg, integral_neg, Finset.sum_neg_distrib] at h
  rw [h, sub_eq_add_neg, Finset.mul_sum]
  congr 2
  refine Finset.sum_congr rfl fun m _ => ?_
  have heq : (∫ w, (((∫ η : R → K_aux → ℝ,
        ∏ r, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r) ∂(Measure.pi fun _ : R => γ_aux)) *
      ∫ η₀ : K_aux → ℝ,
        deriv u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) *
          Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀)) ∂γ_aux) /
      Z w ^ (Fintype.card R + 1)) * (Fintype.card R : ℝ) ∂γ_sh) =
    (Fintype.card R : ℝ) * ∫ w, ((∫ η : R → K_aux → ℝ,
        ∏ r, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r) ∂(Measure.pi fun _ : R => γ_aux)) *
      ∫ η₀ : K_aux → ℝ,
        deriv u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) *
          Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀)) ∂γ_aux) /
      Z w ^ (Fintype.card R + 1) ∂γ_sh := by
    rw [integral_mul_const]; ring
  rw [heq]; ring

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

/-- **Fubini reduction of a quenched tilted replica average to fixed spin labels.** -/
theorem integral_tilted_replica_fubini
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
  have hZ_ge (w : K_sh → ℝ) : Real.exp (-B) ≤ Z w := by
    let E (q : α × (K_aux → ℝ)) :=
      u (α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2)
    have hj : Measurable (fun q : L × (K_aux → ℝ) =>
        u (α_sh q.1 ⬝ᵥ w + α_aux q.1 ⬝ᵥ q.2)) := by
      apply measurable_from_prod_countable_right
      intro l
      apply hu.comp
      simp only [dotProduct]
      fun_prop
    have hm : Measurable E :=
      hj.comp ((hπ.comp measurable_fst).prodMk measurable_snd)
    have hz := integral_exp_pos_of_ae_le (μ := μ₀.prod γ_aux)
      hm.aemeasurable (ae_of_all _ fun q => le_of_abs_le (hB _))
    have hl := abs_log_integral_exp_le_of_ae_abs_le (μ := μ₀.prod γ_aux)
      hm.aemeasurable (ae_of_all _ fun q => hB (α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2))
    rw [← hZ_eq w]
    exact (Real.le_log_iff_exp_le hz).mp (neg_le_of_abs_le hl)
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
  have hK_joint : Measurable (fun p : (ι → L) × ((K_sh → ℝ) × (ι → K_aux → ℝ)) =>
      K p.1 p.2.1 p.2.2) :=
    measurable_from_prod_countable_right hKm
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
        K (fun r => π (p'.1 r)) w p'.2 :=
      hK_joint.comp ((hπa_m.comp measurable_fst).prodMk
        (measurable_const.prodMk measurable_snd))
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
      have hKi : Measurable (fun q : (ι → L) × (K_sh → ℝ) =>
          ∫ η : ι → K_aux → ℝ, K q.1 q.2 η ∂(Measure.pi fun _ : ι => γ_aux)) :=
        measurable_from_prod_countable_right hK_int_m
      exact (hKi.comp ((hπa_m.comp measurable_snd).prodMk measurable_fst)).div
        ((hZm.comp measurable_fst).pow_const _)
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

/-- **Model-free Gaussian integration by parts for a tilted replica average multiplied by
`G(log Z_w(w))`.** Generalizes `stein_tilted_replica_ratio` (recovered at `G = 1`) by allowing an
arbitrary differentiable disorder-normalizer weight `G(log Z_w(w))` with bounded value and
derivative on `[-B, B]`. -/
theorem stein_tilted_replica_ratio_mul_comp_log
    {α L K_sh K_aux R : Type*} [MeasurableSpace α]
    [Finite L] [MeasurableSpace L] [MeasurableSingletonClass L]
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
    {G : ℝ → ℝ} (hG : Differentiable ℝ G) {CG CG' : ℝ}
    (hGb : ∀ t ∈ Set.Icc (-B) B, |G t| ≤ CG)
    (hGd : ∀ t ∈ Set.Icc (-B) B, |deriv G t| ≤ CG')
    (i₀ : R)
    {f : (R → α) → ℝ} (hfi : Integrable f (Measure.pi fun _ : R => μ₀)) :
    let γ_sh := Measure.pi fun _ : K_sh => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : K_aux => gaussianReal 0 1
    let S (w : K_sh → ℝ) (q : α × (K_aux → ℝ)) : ℝ :=
      α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2
    let Wt (w : K_sh → ℝ) (q : α × (K_aux → ℝ)) : ℝ :=
      W_sh (π q.1) ⬝ᵥ w + W_aux (π q.1) ⬝ᵥ q.2
    let Z_w (w : K_sh → ℝ) : ℝ := ∫ q, Real.exp (u (S w q)) ∂(μ₀.prod γ_aux)
    ∫ w, (∫ σ : R → α × (K_aux → ℝ),
        f (fun r => (σ r).1) * Wt w (σ i₀) * (∏ r, ψ r (S w (σ r)))
        ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S w q)))) *
        G (Real.log (Z_w w)) ∂γ_sh =
      ∑ j : R, ∫ w, (∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) *
            (W_sh (π (σ i₀).1) ⬝ᵥ α_sh (π (σ j).1) +
              if i₀ = j then W_aux (π (σ i₀).1) ⬝ᵥ α_aux (π (σ j).1) else 0) *
            (ψ' j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S w q)))) *
          G (Real.log (Z_w w)) ∂γ_sh +
      ∫ w, (∫ σ : Option R → α × (K_aux → ℝ),
          f (fun r => (σ (some r)).1) *
            (W_sh (π (σ (some i₀)).1) ⬝ᵥ α_sh (π (σ none).1)) *
            (∏ r : R, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))
          ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted (fun q => u (S w q)))) *
          (deriv G (Real.log (Z_w w)) - (Fintype.card R : ℝ) * G (Real.log (Z_w w))) ∂γ_sh := by
  classical
  have := Fintype.ofFinite L
  intro γ_sh γ_aux S Wt Z_w
  have hum : Measurable u := hu.continuous.measurable
  let p : L → ℝ := fun m => (μ₀.map π).real {m}
  have hp0 : ∀ m, 0 ≤ p m := fun m => ENNReal.toReal_nonneg
  have hp1 : ∑ m : L, p m = 1 := by
    have : IsProbabilityMeasure (μ₀.map π) :=
      (Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).2 inferInstance
    simp [p]
  let Z : (K_sh → ℝ) → ℝ := fun w =>
    ∑ m : L, p m * ∫ η, Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η)) ∂γ_aux
  have hZ_eq : ∀ w, Z_w w = Z w :=
    fun w => integral_Z_eq_sum_fiber μ₀ π hπ hum hB α_aux (fun m => α_sh m ⬝ᵥ w)
  obtain ⟨hZd, hZb, hZu, -, -⟩ := hasFDerivAt_Z_sum hu hB hD₁ p hp0 hp1 α_aux
  have hZm : Measurable Z := by
    have hm_lin : Measurable fun (w : K_sh → ℝ) (m : L) => α_sh m ⬝ᵥ w :=
      measurable_pi_iff.2 fun m => by simp only [dotProduct]; fun_prop
    exact hZd.continuous.measurable.comp hm_lin
  have hZ_pos : ∀ w, 0 < Z w := fun w => (Real.exp_pos (-B)).trans_le (hZb (fun m => α_sh m ⬝ᵥ w))
  have hZ_mem : ∀ w, Real.log (Z w) ∈ Set.Icc (-B) B := fun w =>
    ⟨by simpa using Real.log_le_log (Real.exp_pos (-B)) (hZb (fun m => α_sh m ⬝ᵥ w)),
     by simpa using Real.log_le_log (hZ_pos w) (hZu (fun m => α_sh m ⬝ᵥ w))⟩
  have hCG0 : 0 ≤ CG := (abs_nonneg _).trans (hGb _ (hZ_mem 0))
  have hCG'0 : 0 ≤ CG' := (abs_nonneg _).trans (hGd _ (hZ_mem 0))
  have hGm : Measurable fun w => G (Real.log (Z w)) :=
    hG.continuous.measurable.comp (Real.measurable_log.comp hZm)
  have hGsub_m : Measurable fun w =>
      deriv G (Real.log (Z w)) - (Fintype.card R : ℝ) * G (Real.log (Z w)) :=
    ((measurable_deriv G).comp (Real.measurable_log.comp hZm)).sub (hGm.const_mul _)
  have hG_bd : ∀ w, |G (Real.log (Z w))| ≤ CG := fun w => hGb _ (hZ_mem w)
  have hGsub_bd : ∀ w,
      |deriv G (Real.log (Z w)) - (Fintype.card R : ℝ) * G (Real.log (Z w))| ≤
        CG' + (Fintype.card R : ℝ) * CG := fun w => by
    refine (abs_sub _ _).trans (add_le_add (hGd _ (hZ_mem w)) ?_)
    rw [abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left (hGb _ (hZ_mem w)) (Nat.cast_nonneg _)
  let ϕ : R → ℝ → ℝ := fun r x => ψ r x * Real.exp (u x)
  have hM : ∀ r x, |ϕ r x| ≤ |M₀ r| * Real.exp B := fun r x =>
    abs_mul_exp_le ((hM₀ r x).trans (le_abs_self _)) (le_of_abs_le (hB x))
  let C_ϕ : ℝ := ∏ r, (|M₀ r| * Real.exp B)
  have hCϕ0 : 0 ≤ C_ϕ := Finset.prod_nonneg fun _ _ => by positivity
  have hLHS := integral_tilted_replica_fubini μ₀ π hπ α_sh α_aux hum hB hfi
    (fun w σ => (Wt w (σ i₀) * ∏ r, ψ r (S w (σ r))) * G (Real.log (Z w)))
    (fun s w η => ((W_sh (s i₀) ⬝ᵥ w + W_aux (s i₀) ⬝ᵥ η i₀) *
      ∏ r, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r)) * G (Real.log (Z w)))
    (fun w σ => by
      have hp : (∏ r, ψ r (S w (σ r))) * Real.exp (∑ r, u (S w (σ r))) =
          ∏ r, ϕ r (S w (σ r)) := by
        rw [Real.exp_sum, ← Finset.prod_mul_distrib]
      dsimp only [Wt, S, ϕ] at hp ⊢
      calc _ = ((W_sh (π (σ i₀).1) ⬝ᵥ w + W_aux (π (σ i₀).1) ⬝ᵥ (σ i₀).2) *
                ((∏ r, ψ r (α_sh (π (σ r).1) ⬝ᵥ w + α_aux (π (σ r).1) ⬝ᵥ (σ r).2)) *
                  Real.exp (∑ r, u (α_sh (π (σ r).1) ⬝ᵥ w + α_aux (π (σ r).1) ⬝ᵥ (σ r).2)))) *
                G (Real.log (Z w)) := by ring
        _ = _ := by rw [hp])
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
      exact (h1.mul h2).mul (hGm.comp measurable_fst))
    (bw := fun w : K_sh → ℝ => (C_ϕ * CG) * ∑ m : L, ∑ k : K_sh, |W_sh m k| * |w k|)
    (by
      have hsum_i : Integrable (fun w : K_sh → ℝ =>
          ∑ m : L, ∑ k : K_sh, |W_sh m k| * |w k|) γ_sh :=
        integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun k _ =>
          (integrable_comp_eval (μ := fun _ : K_sh => gaussianReal 0 1) (i := k)
            (integrable_abs_id_gaussianReal (m := 0) (v := 1))).const_mul |W_sh m k|
      exact hsum_i.const_mul (C_ϕ * CG))
    (bη := fun η : R → K_aux → ℝ => (C_ϕ * CG) * ∑ m : L, ∑ k : K_aux, |W_aux m k| * |η i₀ k|)
    (by
      have hsum_i : Integrable (fun η : R → K_aux → ℝ =>
          ∑ m : L, ∑ k : K_aux, |W_aux m k| * |η i₀ k|) (Measure.pi fun _ : R => γ_aux) := by
        refine integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun k _ => ?_
        have hk : Integrable (fun x : K_aux → ℝ => |x k|) γ_aux :=
          integrable_comp_eval (μ := fun _ : K_aux => gaussianReal 0 1) (i := k)
            (integrable_abs_id_gaussianReal (m := 0) (v := 1))
        exact (integrable_comp_eval (μ := fun _ : R => γ_aux) (i := i₀) hk).const_mul |W_aux m k|
      exact hsum_i.const_mul (C_ϕ * CG))
    (fun s w η => by
      rw [abs_mul, abs_mul]
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
                (∑ m : L, ∑ k : K_aux, |W_aux m k| * |η i₀ k|)) * C_ϕ * CG :=
            mul_le_mul (mul_le_mul hw_bd hp_bd (abs_nonneg _) (by positivity))
              (hG_bd w) (abs_nonneg _) (by positivity)
        _ = _ := by ring)
  have hRHS1 : ∀ j : R,
      ∫ w, (∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) *
            (W_sh (π (σ i₀).1) ⬝ᵥ α_sh (π (σ j).1) +
              if i₀ = j then W_aux (π (σ i₀).1) ⬝ᵥ α_aux (π (σ j).1) else 0) *
            (ψ' j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S w q)))) *
          G (Real.log (Z_w w)) ∂γ_sh =
        ∫ a : R → α, f a *
          ((W_sh (π (a i₀)) ⬝ᵥ α_sh (π (a j)) +
              if i₀ = j then W_aux (π (a i₀)) ⬝ᵥ α_aux (π (a j)) else 0) *
            ∫ w, ((∫ η : R → K_aux → ℝ,
                deriv (ϕ j) (α_sh (π (a j)) ⬝ᵥ w + α_aux (π (a j)) ⬝ᵥ η j) *
                  ∏ r ∈ Finset.univ.erase j,
                    ϕ r (α_sh (π (a r)) ⬝ᵥ w + α_aux (π (a r)) ⬝ᵥ η r)
                ∂(Measure.pi fun _ : R => γ_aux)) / Z w ^ Fintype.card R) *
              G (Real.log (Z w)) ∂γ_sh)
          ∂(Measure.pi fun _ : R => μ₀) := by
    intro j
    let C_j : ℝ := (∑ m : L, ∑ m' : L,
        (|W_sh m ⬝ᵥ α_sh m'| + |W_aux m ⬝ᵥ α_aux m'|)) *
      (|M' j| * ∏ r ∈ Finset.univ.erase j, (|M₀ r| * Real.exp B)) * CG
    have hj_fub := integral_tilted_replica_fubini μ₀ π hπ α_sh α_aux hum hB hfi
      (fun w σ => ((W_sh (π (σ i₀).1) ⬝ᵥ α_sh (π (σ j).1) +
          if i₀ = j then W_aux (π (σ i₀).1) ⬝ᵥ α_aux (π (σ j).1) else 0) *
        (ψ' j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))) *
        G (Real.log (Z w)))
      (fun s w η => ((W_sh (s i₀) ⬝ᵥ α_sh (s j) +
          if i₀ = j then W_aux (s i₀) ⬝ᵥ α_aux (s j) else 0) *
        (deriv (ϕ j) (α_sh (s j) ⬝ᵥ w + α_aux (s j) ⬝ᵥ η j) *
          ∏ r ∈ Finset.univ.erase j, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r))) *
        G (Real.log (Z w)))
      (fun w σ => by
        rw [Real.exp_sum, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
        have hd_eq : deriv (ϕ j) (S w (σ j)) = ψ' j (S w (σ j)) * Real.exp (u (S w (σ j))) :=
          hψ' j _
        have hprod_eq : (∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r))) *
            (∏ r ∈ Finset.univ.erase j, Real.exp (u (S w (σ r)))) =
            ∏ r ∈ Finset.univ.erase j, ϕ r (S w (σ r)) := by
          rw [← Finset.prod_mul_distrib]
        dsimp only [S] at hd_eq hprod_eq ⊢
        calc _ = (W_sh (π (σ i₀).1) ⬝ᵥ α_sh (π (σ j).1) +
                    if i₀ = j then W_aux (π (σ i₀).1) ⬝ᵥ α_aux (π (σ j).1) else 0) *
                  (ψ' j (α_sh (π (σ j).1) ⬝ᵥ w + α_aux (π (σ j).1) ⬝ᵥ (σ j).2) *
                    Real.exp (u (α_sh (π (σ j).1) ⬝ᵥ w + α_aux (π (σ j).1) ⬝ᵥ (σ j).2))) *
                  ((∏ r ∈ Finset.univ.erase j,
                      ψ r (α_sh (π (σ r).1) ⬝ᵥ w + α_aux (π (σ r).1) ⬝ᵥ (σ r).2)) *
                    ∏ r ∈ Finset.univ.erase j,
                      Real.exp (u (α_sh (π (σ r).1) ⬝ᵥ w + α_aux (π (σ r).1) ⬝ᵥ (σ r).2))) *
                  G (Real.log (Z w)) := by ring
          _ = _ := by rw [← hd_eq, hprod_eq]; ring)
      (fun s => by
        have hlin : ∀ r : R, Measurable fun q : (K_sh → ℝ) × (R → K_aux → ℝ) =>
            α_sh (s r) ⬝ᵥ q.1 + α_aux (s r) ⬝ᵥ q.2 r := fun r =>
          (Finset.measurable_sum _ fun k _ =>
            measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
            (Finset.measurable_sum _ fun k _ =>
              measurable_const.mul
                ((measurable_pi_apply k).comp ((measurable_pi_apply r).comp measurable_snd)))
        exact (measurable_const.mul (((measurable_deriv _).comp (hlin j)).mul
          (Finset.measurable_prod _ fun r _ =>
            (hψd r).continuous.measurable.comp (hlin r)))).mul (hGm.comp measurable_fst))
      (bw := fun _ => C_j) (integrable_const _)
      (bη := fun _ => 0) (integrable_const _)
      (fun s w η => by
        rw [add_zero, abs_mul, abs_mul, abs_mul]
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
        exact mul_le_mul
          (mul_le_mul hc1 hc2 (by positivity)
            (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity))
          (hG_bd w) (abs_nonneg _) (by positivity))
    dsimp only at hj_fub
    have heq_lhs : (fun w => (∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) *
            (W_sh (π (σ i₀).1) ⬝ᵥ α_sh (π (σ j).1) +
              if i₀ = j then W_aux (π (σ i₀).1) ⬝ᵥ α_aux (π (σ j).1) else 0) *
            (ψ' j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S w q)))) *
          G (Real.log (Z_w w))) =
        fun w => ∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) *
            (((W_sh (π (σ i₀).1) ⬝ᵥ α_sh (π (σ j).1) +
              if i₀ = j then W_aux (π (σ i₀).1) ⬝ᵥ α_aux (π (σ j).1) else 0) *
            (ψ' j (S w (σ j)) * ∏ r ∈ Finset.univ.erase j, ψ r (S w (σ r)))) *
            G (Real.log (Z w)))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S w q))) := by
      funext w
      rw [hZ_eq w, ← integral_mul_const]
      exact integral_congr_ae (ae_of_all _ fun σ => by ring)
    rw [heq_lhs, hj_fub]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    dsimp only
    congr 1
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    dsimp only
    rw [integral_mul_const, integral_const_mul]
    change (_ * _) * G (Real.log (Z w)) / Z w ^ Fintype.card R = _
    ring
  have hf_opt : Integrable (fun a : Option R → α => f (fun r => a (some r)))
      (Measure.pi fun _ : Option R => μ₀) :=
    (measurePreserving_pi_comp_injective μ₀
      (Option.some_injective R)).integrable_comp_of_integrable hfi
  have hRHS2 :
      ∫ w, (∫ σ : Option R → α × (K_aux → ℝ),
          f (fun r => (σ (some r)).1) *
            (W_sh (π (σ (some i₀)).1) ⬝ᵥ α_sh (π (σ none).1)) *
            (∏ r : R, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))
          ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted (fun q => u (S w q)))) *
          (deriv G (Real.log (Z_w w)) - (Fintype.card R : ℝ) * G (Real.log (Z_w w))) ∂γ_sh =
        ∫ a : R → α, f a *
          (∑ m : L, p m * (W_sh (π (a i₀)) ⬝ᵥ α_sh m) *
            ∫ w, (((∫ η : R → K_aux → ℝ,
                  ∏ r, ϕ r (α_sh (π (a r)) ⬝ᵥ w + α_aux (π (a r)) ⬝ᵥ η r)
                  ∂(Measure.pi fun _ : R => γ_aux)) *
                ∫ η₀ : K_aux → ℝ,
                  deriv u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) *
                    Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀))
                  ∂γ_aux) / Z w ^ (Fintype.card R + 1)) *
              (deriv G (Real.log (Z w)) - (Fintype.card R : ℝ) * G (Real.log (Z w))) ∂γ_sh)
          ∂(Measure.pi fun _ : R => μ₀) := by
    let C_opt : ℝ := (∑ m : L, ∑ m' : L, |W_sh m ⬝ᵥ α_sh m'|) * (C_ϕ * (|D₁| * Real.exp B)) *
      (CG' + (Fintype.card R : ℝ) * CG)
    have hopt_fub :=
      integral_tilted_replica_fubini (ι := Option R) μ₀ π hπ α_sh α_aux hum hB hf_opt
      (fun w σ => ((W_sh (π (σ (some i₀)).1) ⬝ᵥ α_sh (π (σ none).1)) *
        (∏ r : R, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))) *
        (deriv G (Real.log (Z w)) - (Fintype.card R : ℝ) * G (Real.log (Z w))))
      (fun s w η => ((W_sh (s (some i₀)) ⬝ᵥ α_sh (s none)) *
        (∏ r : R, ϕ r (α_sh (s (some r)) ⬝ᵥ w + α_aux (s (some r)) ⬝ᵥ η (some r))) *
        (deriv u (α_sh (s none) ⬝ᵥ w + α_aux (s none) ⬝ᵥ η none) *
          Real.exp (u (α_sh (s none) ⬝ᵥ w + α_aux (s none) ⬝ᵥ η none)))) *
        (deriv G (Real.log (Z w)) - (Fintype.card R : ℝ) * G (Real.log (Z w))))
      (fun w σ => by
        rw [Fintype.sum_option, Real.exp_add, Real.exp_sum]
        have hprod_eq : (∏ r : R, ψ r (S w (σ (some r)))) *
            (∏ r : R, Real.exp (u (S w (σ (some r))))) =
            ∏ r : R, ϕ r (S w (σ (some r))) := by
          rw [← Finset.prod_mul_distrib]
        dsimp only [S] at hprod_eq ⊢
        calc _ = (W_sh (π (σ (some i₀)).1) ⬝ᵥ α_sh (π (σ none).1)) *
                  ((∏ r : R, ψ r (α_sh (π (σ (some r)).1) ⬝ᵥ w +
                      α_aux (π (σ (some r)).1) ⬝ᵥ (σ (some r)).2)) *
                    ∏ r : R, Real.exp (u (α_sh (π (σ (some r)).1) ⬝ᵥ w +
                      α_aux (π (σ (some r)).1) ⬝ᵥ (σ (some r)).2))) *
                  (deriv u (α_sh (π (σ none).1) ⬝ᵥ w + α_aux (π (σ none).1) ⬝ᵥ (σ none).2) *
                    Real.exp (u (α_sh (π (σ none).1) ⬝ᵥ w + α_aux (π (σ none).1) ⬝ᵥ (σ none).2))) *
                  (deriv G (Real.log (Z w)) - (Fintype.card R : ℝ) * G (Real.log (Z w))) := by ring
          _ = _ := by rw [hprod_eq])
      (fun s => by
        have hlin : ∀ r : Option R, Measurable fun q : (K_sh → ℝ) × (Option R → K_aux → ℝ) =>
            α_sh (s r) ⬝ᵥ q.1 + α_aux (s r) ⬝ᵥ q.2 r := fun r =>
          (Finset.measurable_sum _ fun k _ =>
            measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
            (Finset.measurable_sum _ fun k _ =>
              measurable_const.mul
                ((measurable_pi_apply k).comp ((measurable_pi_apply r).comp measurable_snd)))
        exact ((measurable_const.mul
          (Finset.measurable_prod _ fun r _ =>
            (hψd r).continuous.measurable.comp (hlin (some r)))).mul
          (((measurable_deriv u).comp (hlin none)).mul
            (Real.measurable_exp.comp (hum.comp (hlin none))))).mul (hGsub_m.comp measurable_fst))
      (bw := fun _ => C_opt) (integrable_const _)
      (bη := fun _ => 0) (integrable_const _)
      (fun s w η => by
        rw [add_zero, abs_mul, abs_mul, abs_mul]
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
        calc _ ≤ (∑ m : L, ∑ m' : L, |W_sh m ⬝ᵥ α_sh m'|) * C_ϕ * (|D₁| * Real.exp B) *
                  (CG' + (Fintype.card R : ℝ) * CG) :=
              mul_le_mul
                (mul_le_mul (mul_le_mul hc1 hc2 (abs_nonneg _)
                  (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _))
                  hc3 (abs_nonneg _) (by positivity))
                (hGsub_bd w) (abs_nonneg _) (by positivity)
          _ = C_opt := by dsimp only [C_opt]; ring)
    dsimp only at hopt_fub
    have heq_lhs : (fun w => (∫ σ : Option R → α × (K_aux → ℝ),
          f (fun r => (σ (some r)).1) *
            (W_sh (π (σ (some i₀)).1) ⬝ᵥ α_sh (π (σ none).1)) *
            (∏ r : R, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))
          ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted (fun q => u (S w q)))) *
          (deriv G (Real.log (Z_w w)) - (Fintype.card R : ℝ) * G (Real.log (Z_w w)))) =
        fun w => ∫ σ : Option R → α × (K_aux → ℝ),
          f (fun r => (σ (some r)).1) *
            (((W_sh (π (σ (some i₀)).1) ⬝ᵥ α_sh (π (σ none).1)) *
              (∏ r : R, ψ r (S w (σ (some r)))) * deriv u (S w (σ none))) *
            (deriv G (Real.log (Z w)) - (Fintype.card R : ℝ) * G (Real.log (Z w))))
          ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted (fun q => u (S w q))) := by
      funext w
      rw [hZ_eq w, ← integral_mul_const]
      exact integral_congr_ae (ae_of_all _ fun σ => by ring)
    rw [heq_lhs, hopt_fub]
    have h_eta_split : ∀ (a : Option R → α) (w : K_sh → ℝ),
        ∫ η : Option R → K_aux → ℝ,
          ((W_sh (π (a (some i₀))) ⬝ᵥ α_sh (π (a none))) *
            (∏ r : R,
              ϕ r (α_sh (π (a (some r))) ⬝ᵥ w + α_aux (π (a (some r))) ⬝ᵥ η (some r))) *
            (deriv u (α_sh (π (a none)) ⬝ᵥ w + α_aux (π (a none)) ⬝ᵥ η none) *
              Real.exp (u (α_sh (π (a none)) ⬝ᵥ w + α_aux (π (a none)) ⬝ᵥ η none)))) *
          (deriv G (Real.log (Z w)) - (Fintype.card R : ℝ) * G (Real.log (Z w)))
          ∂(Measure.pi fun _ : Option R => γ_aux) =
        (W_sh (π (a (some i₀))) ⬝ᵥ α_sh (π (a none))) *
          ((∫ η : R → K_aux → ℝ,
              ∏ r : R, ϕ r (α_sh (π (a (some r))) ⬝ᵥ w + α_aux (π (a (some r))) ⬝ᵥ η r)
              ∂(Measure.pi fun _ : R => γ_aux)) *
            ∫ η₀ : K_aux → ℝ,
              deriv u (α_sh (π (a none)) ⬝ᵥ w + α_aux (π (a none)) ⬝ᵥ η₀) *
                Real.exp (u (α_sh (π (a none)) ⬝ᵥ w + α_aux (π (a none)) ⬝ᵥ η₀))
              ∂γ_aux) *
          (deriv G (Real.log (Z w)) - (Fintype.card R : ℝ) * G (Real.log (Z w))) := by
      intro a w
      rw [integral_mul_const]
      congr 1
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
        ∫ w, (((∫ η : R → K_aux → ℝ,
              ∏ r : R, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r)
              ∂(Measure.pi fun _ : R => γ_aux)) *
            ∫ η₀ : K_aux → ℝ,
              deriv u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) *
                Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀))
              ∂γ_aux) / Z w ^ (Fintype.card R + 1)) *
          (deriv G (Real.log (Z w)) - (Fintype.card R : ℝ) * G (Real.log (Z w))) ∂γ_sh
    have h_a_eq : ∀ a : Option R → α,
        f (fun r => a (some r)) *
          ∫ w, (∫ η : Option R → K_aux → ℝ,
              ((W_sh (π (a (some i₀))) ⬝ᵥ α_sh (π (a none))) *
                (∏ r : R,
                  ϕ r (α_sh (π (a (some r))) ⬝ᵥ w + α_aux (π (a (some r))) ⬝ᵥ η (some r))) *
                (deriv u (α_sh (π (a none)) ⬝ᵥ w + α_aux (π (a none)) ⬝ᵥ η none) *
                  Real.exp (u (α_sh (π (a none)) ⬝ᵥ w + α_aux (π (a none)) ⬝ᵥ η none)))) *
              (deriv G (Real.log (Z w)) - (Fintype.card R : ℝ) * G (Real.log (Z w)))
              ∂(Measure.pi fun _ : Option R => γ_aux)) /
            Z w ^ Fintype.card (Option R) ∂γ_sh =
        f (fun r => a (some r)) * I_m (fun r => π (a (some r))) (π (a none)) := by
      intro a
      congr 1
      dsimp only [I_m]
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      dsimp only
      rw [h_eta_split a w, Fintype.card_option]
      ring
    have h_a_congr : ∫ a : Option R → α,
          f (fun r => a (some r)) *
            ∫ w, (∫ η : Option R → K_aux → ℝ,
                ((W_sh (π (a (some i₀))) ⬝ᵥ α_sh (π (a none))) *
                  (∏ r : R,
                    ϕ r (α_sh (π (a (some r))) ⬝ᵥ w + α_aux (π (a (some r))) ⬝ᵥ η (some r))) *
                  (deriv u (α_sh (π (a none)) ⬝ᵥ w + α_aux (π (a none)) ⬝ᵥ η none) *
                    Real.exp (u (α_sh (π (a none)) ⬝ᵥ w + α_aux (π (a none)) ⬝ᵥ η none)))) *
                (deriv G (Real.log (Z w)) - (Fintype.card R : ℝ) * G (Real.log (Z w)))
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
  have hLHS' : ∫ w, (∫ σ : R → α × (K_aux → ℝ),
        f (fun r => (σ r).1) * Wt w (σ i₀) * (∏ r, ψ r (S w (σ r)))
        ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S w q)))) *
        G (Real.log (Z_w w)) ∂γ_sh =
      ∫ a : R → α, f a *
        ∫ w, ((∫ η : R → K_aux → ℝ,
            (W_sh (π (a i₀)) ⬝ᵥ w + W_aux (π (a i₀)) ⬝ᵥ η i₀) *
              (∏ r, ϕ r (α_sh (π (a r)) ⬝ᵥ w + α_aux (π (a r)) ⬝ᵥ η r))
            ∂(Measure.pi fun _ : R => γ_aux)) / Z w ^ Fintype.card R) *
          G (Real.log (Z w)) ∂γ_sh
        ∂(Measure.pi fun _ : R => μ₀) := by
    have heq : (fun w => (∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) * Wt w (σ i₀) * (∏ r, ψ r (S w (σ r)))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S w q)))) *
          G (Real.log (Z_w w))) =
        fun w => ∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) * ((Wt w (σ i₀) * ∏ r, ψ r (S w (σ r))) * G (Real.log (Z w)))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S w q))) := by
      funext w
      rw [hZ_eq w, ← integral_mul_const]
      exact integral_congr_ae (ae_of_all _ fun σ => by ring)
    rw [heq, hLHS]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    dsimp only
    congr 1
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    dsimp only
    rw [integral_mul_const]
    change _ / Z w ^ Fintype.card R = _
    ring
  rw [hLHS', Finset.sum_congr rfl fun j _ => hRHS1 j, hRHS2]
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : R → (R → L) → ℝ, ∀ j s, g₁ j s =
      (W_sh (s i₀) ⬝ᵥ α_sh (s j) + if i₀ = j then W_aux (s i₀) ⬝ᵥ α_aux (s j) else 0) *
        ∫ w, ((∫ η : R → K_aux → ℝ,
            deriv (ϕ j) (α_sh (s j) ⬝ᵥ w + α_aux (s j) ⬝ᵥ η j) *
              ∏ r ∈ Finset.univ.erase j, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r)
            ∂(Measure.pi fun _ : R => γ_aux)) / Z w ^ Fintype.card R) *
          G (Real.log (Z w)) ∂γ_sh :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨g₂, hg₂⟩ : ∃ g₂ : (R → L) → ℝ, ∀ s, g₂ s =
      ∑ m : L, p m * (W_sh (s i₀) ⬝ᵥ α_sh m) *
        ∫ w, (((∫ η : R → K_aux → ℝ,
              ∏ r, ϕ r (α_sh (s r) ⬝ᵥ w + α_aux (s r) ⬝ᵥ η r)
              ∂(Measure.pi fun _ : R => γ_aux)) *
            ∫ η₀ : K_aux → ℝ,
              deriv u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) *
                Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀))
              ∂γ_aux) / Z w ^ (Fintype.card R + 1)) *
          (deriv G (Real.log (Z w)) - (Fintype.card R : ℝ) * G (Real.log (Z w))) ∂γ_sh :=
    ⟨_, fun _ => rfl⟩
  have hR1_fold : ∀ j : R,
      (∫ a : R → α, f a *
        ((W_sh (π (a i₀)) ⬝ᵥ α_sh (π (a j)) +
            if i₀ = j then W_aux (π (a i₀)) ⬝ᵥ α_aux (π (a j)) else 0) *
          ∫ w, ((∫ η : R → K_aux → ℝ,
              deriv (ϕ j) (α_sh (π (a j)) ⬝ᵥ w + α_aux (π (a j)) ⬝ᵥ η j) *
                ∏ r ∈ Finset.univ.erase j, ϕ r (α_sh (π (a r)) ⬝ᵥ w + α_aux (π (a r)) ⬝ᵥ η r)
              ∂(Measure.pi fun _ : R => γ_aux)) / Z w ^ Fintype.card R) *
            G (Real.log (Z w)) ∂γ_sh)
        ∂(Measure.pi fun _ : R => μ₀)) =
      ∫ a : R → α, f a * g₁ j (fun r => π (a r)) ∂(Measure.pi fun _ : R => μ₀) :=
    fun j => integral_congr_ae (ae_of_all _ fun a => by dsimp only; rw [hg₁])
  have hR2_fold :
      (∫ a : R → α, f a *
        (∑ m : L, p m * (W_sh (π (a i₀)) ⬝ᵥ α_sh m) *
          ∫ w, (((∫ η : R → K_aux → ℝ,
                ∏ r, ϕ r (α_sh (π (a r)) ⬝ᵥ w + α_aux (π (a r)) ⬝ᵥ η r)
                ∂(Measure.pi fun _ : R => γ_aux)) *
              ∫ η₀ : K_aux → ℝ,
                deriv u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) *
                  Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀))
                ∂γ_aux) / Z w ^ (Fintype.card R + 1)) *
            (deriv G (Real.log (Z w)) - (Fintype.card R : ℝ) * G (Real.log (Z w))) ∂γ_sh)
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
  rw [← integral_finsetSum _ fun j _ => h_bdd_int (g₁ j),
    ← integral_add (integrable_finsetSum _ fun j _ => h_bdd_int (g₁ j)) (h_bdd_int g₂)]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  dsimp only
  rw [← Finset.mul_sum, ← mul_add]
  congr 1
  simp_rw [hg₁, hg₂]
  exact stein_ratio_comp_log_fixed_spins p hp0 hp1 α_sh W_sh α_aux W_aux hu hB hD₁ ϕ hψd hM hM'
    hG hGb hGd i₀ (fun r => π (a r))

/-- **Model-free Gaussian integration by parts for a tilted replica average.** Let `μ₀` be a
probability measure on an old-state space `α` with a measurable projection `π : α → L` onto a
finite spin-label set `L`. With shared Gaussian vector `w` and per-replica auxiliary Gaussian
vectors `η`, field `S w q = α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2`, multiplier
`Wt w q = W_sh (π q.1) ⬝ᵥ w + W_aux (π q.1) ⬝ᵥ q.2`, and per-replica factors `ψ r` such that
`(ψ r * exp ∘ u)' = ψ' r * exp ∘ u` is bounded (requiring no continuity of `ψ' r`), the quenched
expectation of `⟨f · Wt(σ_{i₀}) · ∏_r ψ_r(S(σ_r))⟩` expands into `R` replica terms plus the fresh
replica term created by differentiating the normalizer. Only `Integrable f (pi μ₀)` is required of
`f` (`G = 1` specialization of `stein_tilted_replica_ratio_mul_comp_log`). -/
theorem stein_tilted_replica_ratio
    {α L K_sh K_aux R : Type*} [MeasurableSpace α]
    [Finite L] [MeasurableSpace L] [MeasurableSingletonClass L]
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
  intro γ_sh γ_aux S Wt
  have h := stein_tilted_replica_ratio_mul_comp_log μ₀ π hπ α_sh W_sh α_aux W_aux hu hB hD₁
    ψ hψd hM₀ hM' ψ' hψ' (G := fun _ => (1 : ℝ)) (differentiable_const 1)
    (CG := 1) (CG' := 0) (fun _ _ => by simp) (fun _ _ => by simp) i₀ hfi
  dsimp only at h
  simp only [deriv_const', mul_one, zero_sub, mul_neg, integral_neg] at h
  rw [h, sub_eq_add_neg]
  congr 2
  rw [integral_mul_const]; ring

/-- Differentiating `s ↦ (∫ η : R → K_aux → ℝ, ∏_r ϕ_r(S_s(w, st_r, η_r))) / Z_s(w)^|R|`
at fixed spin labels `st : R → L` and fixed `w : K_sh → ℝ`. -/
private lemma hasDerivAt_ratio_fixed_spins_w
    {L K_sh K_aux R : Type*} [Fintype L]
    [Fintype K_sh] [Fintype K_aux] [Fintype R] [DecidableEq R]
    (p : L → ℝ) (hp0 : ∀ m, 0 ≤ p m) (hp1 : ∑ m, p m = 1)
    (X_sh Y_sh : L → K_sh → ℝ) (X_aux Y_aux : L → K_aux → ℝ)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) {B D₁ : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    {M₀ M₁ : R → ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀ r) (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁ r)
    (st : R → L) (w : K_sh → ℝ) (s₀ : ℝ) :
    let γ_aux := Measure.pi fun _ : K_aux => gaussianReal 0 1
    let S (s : ℝ) (m : L) (η : K_aux → ℝ) : ℝ :=
      Real.cos s * (X_sh m ⬝ᵥ w + X_aux m ⬝ᵥ η) + Real.sin s * (Y_sh m ⬝ᵥ w + Y_aux m ⬝ᵥ η)
    let S' (s : ℝ) (m : L) (η : K_aux → ℝ) : ℝ :=
      -Real.sin s * (X_sh m ⬝ᵥ w + X_aux m ⬝ᵥ η) + Real.cos s * (Y_sh m ⬝ᵥ w + Y_aux m ⬝ᵥ η)
    let ϕ (r : R) (x : ℝ) : ℝ := ψ r x * Real.exp (u x)
    let ϕ' (r : R) (x : ℝ) : ℝ := (deriv (ψ r) x + ψ r x * deriv u x) * Real.exp (u x)
    let Z (s : ℝ) : ℝ := ∑ m : L, p m * ∫ η, Real.exp (u (S s m η)) ∂γ_aux
    HasDerivAt
      (fun s =>
        (∫ η : R → K_aux → ℝ, ∏ r, ϕ r (S s (st r) (η r)) ∂(Measure.pi fun _ : R => γ_aux)) /
          Z s ^ Fintype.card R)
      ((∑ i : R, (∫ η : R → K_aux → ℝ, S' s₀ (st i) (η i) *
            (ϕ' i (S s₀ (st i) (η i)) * ∏ r ∈ Finset.univ.erase i, ϕ r (S s₀ (st r) (η r)))
            ∂(Measure.pi fun _ : R => γ_aux)) / Z s₀ ^ Fintype.card R) -
        (Fintype.card R : ℝ) * ∑ m : L, p m *
          (((∫ η : R → K_aux → ℝ, ∏ r, ϕ r (S s₀ (st r) (η r))
              ∂(Measure.pi fun _ : R => γ_aux)) *
            ∫ η₀, S' s₀ m η₀ * deriv u (S s₀ m η₀) * Real.exp (u (S s₀ m η₀)) ∂γ_aux) /
            Z s₀ ^ (Fintype.card R + 1)))
      s₀ := by
  intro γ_aux S S' ϕ ϕ' Z
  have h1_m : ∀ (g : ℝ → ℝ), Measurable g → ∀ s m,
      Measurable fun η : K_aux → ℝ => g (S s m η) :=
    fun g hg s m => hg.comp (((measurable_const.add
      (Finset.measurable_sum _ fun k _ => by fun_prop)).const_mul _).add
      ((measurable_const.add (Finset.measurable_sum _ fun k _ => by fun_prop)).const_mul _))
  have hum : Measurable u := hu.continuous.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  have hϕm : ∀ r, Measurable (ϕ r) := fun r =>
    (hψd r).continuous.measurable.mul (Real.measurable_exp.comp hum)
  have hϕ'm : ∀ r, Measurable (ϕ' r) := fun r =>
    ((measurable_deriv _).add ((hψd r).continuous.measurable.mul hdu)).mul
      (Real.measurable_exp.comp hum)
  let b_m : L → (K_aux → ℝ) → ℝ := fun m η =>
    (|X_sh m ⬝ᵥ w| + ∑ k, |X_aux m k| * |η k|) + (|Y_sh m ⬝ᵥ w| + ∑ k, |Y_aux m k| * |η k|)
  have hbm_0 : ∀ m η, 0 ≤ b_m m η := fun m η =>
    add_nonneg (add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => by positivity))
      (add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => by positivity))
  have hbm_i : ∀ m, Integrable (b_m m) γ_aux := fun m =>
    ((integrable_const _).add (integrable_finsetSum _ fun k _ =>
      (integrable_comp_eval (μ := fun _ : K_aux => gaussianReal 0 1) (i := k)
        (integrable_abs_id_gaussianReal (m := 0) (v := 1))).const_mul _)).add
    ((integrable_const _).add (integrable_finsetSum _ fun k _ =>
      (integrable_comp_eval (μ := fun _ : K_aux => gaussianReal 0 1) (i := k)
        (integrable_abs_id_gaussianReal (m := 0) (v := 1))).const_mul _))
  have hS'_le : ∀ s m η, |S' s m η| ≤ b_m m η := fun s m η => by
    have h1 : |S' s m η| ≤ |X_sh m ⬝ᵥ w + X_aux m ⬝ᵥ η| + |Y_sh m ⬝ᵥ w + Y_aux m ⬝ᵥ η| := by
      calc |S' s m η| ≤ |-Real.sin s * (X_sh m ⬝ᵥ w + X_aux m ⬝ᵥ η)| +
            |Real.cos s * (Y_sh m ⬝ᵥ w + Y_aux m ⬝ᵥ η)| := abs_add_le _ _
        _ = |Real.sin s| * |X_sh m ⬝ᵥ w + X_aux m ⬝ᵥ η| +
            |Real.cos s| * |Y_sh m ⬝ᵥ w + Y_aux m ⬝ᵥ η| := by rw [abs_mul, abs_mul, abs_neg]
        _ ≤ 1 * |X_sh m ⬝ᵥ w + X_aux m ⬝ᵥ η| + 1 * |Y_sh m ⬝ᵥ w + Y_aux m ⬝ᵥ η| :=
            add_le_add (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one s) (abs_nonneg _))
              (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one s) (abs_nonneg _))
        _ = _ := by ring
    refine h1.trans (add_le_add ?_ ?_)
    · refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      simp_rw [abs_mul]
    · refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      simp_rw [abs_mul]
  have hS_d : ∀ m η s, HasDerivAt (fun s' => S s' m η) (S' s m η) s := fun m η s =>
    ((Real.hasDerivAt_cos s).mul_const _).add ((Real.hasDerivAt_sin s).mul_const _)
  have h_one : ∀ (m : L) (g g' : ℝ → ℝ) (hg : Measurable g) (hg' : Measurable g')
      (hgd : ∀ x, HasDerivAt g (g' x) x) {C0 C1 : ℝ} (h0 : ∀ x, |g x| ≤ C0)
      (h1 : ∀ x, |g' x| ≤ C1) (s : ℝ),
      HasDerivAt (fun s' => ∫ η, g (S s' m η) ∂γ_aux)
        (∫ η, S' s m η * g' (S s m η) ∂γ_aux) s := by
    intro m g g' hg hg' hgd C0 C1 h0 h1 s
    have hS'_m : Measurable fun η : K_aux → ℝ => S' s m η :=
      ((measurable_const.add (Finset.measurable_sum _ fun k _ => by fun_prop)).const_mul _).add
        ((measurable_const.add (Finset.measurable_sum _ fun k _ => by fun_prop)).const_mul _)
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ_aux)
      (F := fun s' η => g (S s' m η))
      (F' := fun s' η => S' s' m η * g' (S s' m η))
      (s := Set.univ) Filter.univ_mem
      (Filter.Eventually.of_forall fun s' => (h1_m g hg s' m).aestronglyMeasurable)
      (Integrable.of_bound (C := |C0|) (h1_m g hg s m).aestronglyMeasurable
        (ae_of_all _ fun η => (Real.norm_eq_abs _).trans_le ((h0 _).trans (le_abs_self _))))
      (hS'_m.mul (h1_m g' hg' s m)).aestronglyMeasurable
      (bound := fun η => b_m m η * |C1|)
      (ae_of_all _ fun η s' _ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hS'_le s' m η) ((h1 _).trans (le_abs_self _)) (abs_nonneg _)
          (hbm_0 m η))
      ((hbm_i m).mul_const |C1|)
      (ae_of_all _ fun η s' _ =>
        ((hgd _).comp s' (hS_d m η s')).congr_deriv (mul_comm _ _))).2
  have hZd : HasDerivAt Z
      (∑ m : L, p m *
        ∫ η₀, S' s₀ m η₀ * deriv u (S s₀ m η₀) * Real.exp (u (S s₀ m η₀)) ∂γ_aux) s₀ := by
    refine HasDerivAt.fun_sum fun m _ => ?_
    have h1 := (h_one m (fun x => Real.exp (u x)) (fun x => deriv u x * Real.exp (u x))
      (Real.measurable_exp.comp hum) (hdu.mul (Real.measurable_exp.comp hum))
      (fun x => ((hu x).hasDerivAt.exp).congr_deriv (mul_comm _ _))
      (fun x => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.2 (le_of_abs_le (hB x)))
      (fun x => abs_mul_exp_le ((hD₁ x).trans (le_abs_self _)) (le_of_abs_le (hB x))) s₀).const_mul
      (p m)
    exact h1.congr_deriv (congrArg (p m * ·)
      (integral_congr_ae (ae_of_all _ fun η₀ => by ring)))
  have hϕb : ∀ r x, |ϕ r x| ≤ |M₀ r| * Real.exp B := fun r x =>
    abs_mul_exp_le ((hM₀ r x).trans (le_abs_self _)) (le_of_abs_le (hB x))
  have hϕ'b : ∀ r x, |ϕ' r x| ≤ (|M₁ r| + |M₀ r| * |D₁|) * Real.exp B := fun r x => by
    refine abs_mul_exp_le ?_ (le_of_abs_le (hB x))
    refine (abs_add_le _ _).trans (add_le_add ((hM₁ r x).trans (le_abs_self _)) ?_)
    rw [abs_mul]
    exact mul_le_mul ((hM₀ r x).trans (le_abs_self _)) ((hD₁ x).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  have hϕ_one : ∀ r s, HasDerivAt (fun s' => ∫ η, ϕ r (S s' (st r) η) ∂γ_aux)
      (∫ η, S' s (st r) η * ϕ' r (S s (st r) η) ∂γ_aux) s := fun r s =>
    h_one (st r) (ϕ r) (ϕ' r) (hϕm r) (hϕ'm r)
      (fun x => (((hψd r x).hasDerivAt).mul ((hu x).hasDerivAt.exp)).congr_deriv
        (by dsimp only [ϕ']; ring))
      (hϕb r) (hϕ'b r) s
  have hNum_prod_eq : ∀ s,
      (∫ η : R → K_aux → ℝ, ∏ r, ϕ r (S s (st r) (η r)) ∂(Measure.pi fun _ : R => γ_aux)) =
        ∏ r, ∫ η, ϕ r (S s (st r) η) ∂γ_aux := fun s =>
    integral_fintype_prod_eq_prod (fun r η => ϕ r (S s (st r) η))
  have hNum'_prod_eq : ∀ i : R,
      (∫ η : R → K_aux → ℝ, S' s₀ (st i) (η i) *
          (ϕ' i (S s₀ (st i) (η i)) * ∏ r ∈ Finset.univ.erase i, ϕ r (S s₀ (st r) (η r)))
        ∂(Measure.pi fun _ : R => γ_aux)) =
      (∫ η, S' s₀ (st i) η * ϕ' i (S s₀ (st i) η) ∂γ_aux) *
        ∏ r ∈ Finset.univ.erase i, ∫ η, ϕ r (S s₀ (st r) η) ∂γ_aux := by
    intro i
    let g_r : R → (K_aux → ℝ) → ℝ := fun r η =>
      if r = i then S' s₀ (st i) η * ϕ' i (S s₀ (st i) η) else ϕ r (S s₀ (st r) η)
    have hprod_g : ∀ η : R → K_aux → ℝ,
        S' s₀ (st i) (η i) *
          (ϕ' i (S s₀ (st i) (η i)) * ∏ r ∈ Finset.univ.erase i, ϕ r (S s₀ (st r) (η r))) =
        ∏ r : R, g_r r (η r) := fun η => by
      rw [← Finset.mul_prod_erase Finset.univ (fun r => g_r r (η r)) (Finset.mem_univ i)]
      simp only [g_r, ↓reduceIte, mul_assoc]
      congr 2
      exact Finset.prod_congr rfl fun r hr => by simp [Finset.ne_of_mem_erase hr]
    simp_rw [hprod_g]
    rw [integral_fintype_prod_eq_prod g_r,
      ← Finset.mul_prod_erase Finset.univ (fun r => ∫ η, g_r r η ∂γ_aux) (Finset.mem_univ i)]
    simp only [g_r, ↓reduceIte]
    congr 1
    exact Finset.prod_congr rfl fun r hr => by simp [Finset.ne_of_mem_erase hr]
  have hZ_pos : 0 < Z s₀ :=
    (Real.exp_pos (-B)).trans_le <|
      exp_neg_le_sum_mul_integral_exp p hp0 hp1 (fun m η => u (S s₀ m η)) (fun _ _ => hB _)
        fun m => Integrable.of_bound (C := Real.exp B)
          (h1_m (fun x => Real.exp (u x)) (Real.measurable_exp.comp hum) s₀ m).aestronglyMeasurable
          (ae_of_all _ fun η => by
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact Real.exp_le_exp.2 (le_of_abs_le (hB _)))
  simp_rw [hNum_prod_eq]
  have hNum_d : HasDerivAt (fun s => ∏ r : R, ∫ η, ϕ r (S s (st r) η) ∂γ_aux)
      (∑ i : R, (∏ j ∈ Finset.univ.erase i, ∫ η, ϕ j (S s₀ (st j) η) ∂γ_aux) *
        ∫ η, S' s₀ (st i) η * ϕ' i (S s₀ (st i) η) ∂γ_aux) s₀ := by
    have hp := HasDerivAt.finsetProd (u := Finset.univ)
      (f := fun r s' => ∫ η, ϕ r (S s' (st r) η) ∂γ_aux)
      (f' := fun r => ∫ η, S' s₀ (st r) η * ϕ' r (S s₀ (st r) η) ∂γ_aux)
      fun r _ => hϕ_one r s₀
    have hfun : (∏ i : R, fun s' => ∫ η, ϕ i (S s' (st i) η) ∂γ_aux) =
        fun s => ∏ r : R, ∫ η, ϕ r (S s (st r) η) ∂γ_aux :=
      funext fun s => Finset.prod_apply s Finset.univ _
    rw [hfun] at hp
    exact hp.congr_deriv (Finset.sum_congr rfl fun _ _ => rfl)
  have hZ_ne : Z s₀ ≠ 0 := hZ_pos.ne'
  have hZpow_d : HasDerivAt (fun s => Z s ^ Fintype.card R)
      ((Fintype.card R : ℝ) * Z s₀ ^ (Fintype.card R - 1) *
        ∑ m : L, p m *
          ∫ η₀, S' s₀ m η₀ * deriv u (S s₀ m η₀) * Real.exp (u (S s₀ m η₀)) ∂γ_aux) s₀ := by
    have hp := hZd.pow (Fintype.card R)
    have hfun : Z ^ Fintype.card R = fun s => Z s ^ Fintype.card R := rfl
    rw [hfun] at hp
    exact hp
  have hdiv_d := hNum_d.div hZpow_d (pow_ne_zero _ hZ_ne)
  change HasDerivAt (fun s => (∏ r, ∫ η, ϕ r (S s (st r) η) ∂γ_aux) / Z s ^ Fintype.card R) _ s₀
    at hdiv_d
  refine hdiv_d.congr_deriv ?_
  simp_rw [hNum'_prod_eq]
  have hrhs_sum : (∑ m : L, p m *
      (((∏ r, ∫ η, ϕ r (S s₀ (st r) η) ∂γ_aux) *
          ∫ η₀, S' s₀ m η₀ * deriv u (S s₀ m η₀) * Real.exp (u (S s₀ m η₀)) ∂γ_aux) /
        Z s₀ ^ (Fintype.card R + 1))) =
      (∏ r, ∫ η, ϕ r (S s₀ (st r) η) ∂γ_aux) *
        (∑ m : L, p m *
          ∫ η₀, S' s₀ m η₀ * deriv u (S s₀ m η₀) * Real.exp (u (S s₀ m η₀)) ∂γ_aux) /
        Z s₀ ^ (Fintype.card R + 1) := by
    simp_rw [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [hrhs_sum]
  have heq_sum : ∑ i : R, ((∫ η, S' s₀ (st i) η * ϕ' i (S s₀ (st i) η) ∂γ_aux) *
      ∏ r ∈ Finset.univ.erase i, ∫ η, ϕ r (S s₀ (st r) η) ∂γ_aux) / Z s₀ ^ Fintype.card R =
      (∑ i : R, (∏ j ∈ Finset.univ.erase i, ∫ η, ϕ j (S s₀ (st j) η) ∂γ_aux) *
        ∫ η, S' s₀ (st i) η * ϕ' i (S s₀ (st i) η) ∂γ_aux) / Z s₀ ^ Fintype.card R := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  rw [heq_sum]
  generalize (∑ m : L, p m *
    ∫ η₀, S' s₀ m η₀ * deriv u (S s₀ m η₀) * Real.exp (u (S s₀ m η₀)) ∂γ_aux) = D_Z
  generalize (∏ r, ∫ η, ϕ r (S s₀ (st r) η) ∂γ_aux) = P_num
  generalize (∑ i : R, (∏ j ∈ Finset.univ.erase i, ∫ η, ϕ j (S s₀ (st j) η) ∂γ_aux) *
    ∫ η, S' s₀ (st i) η * ϕ' i (S s₀ (st i) η) ∂γ_aux) = S_num
  rcases Nat.eq_zero_or_pos (Fintype.card R) with h0 | hpos
  · simp [h0]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    rw [hk]
    have hsub : k.succ - 1 = k := rfl
    rw [hsub, Nat.succ_eq_add_one]
    have hZk : Z s₀ ^ (k + 1) ≠ 0 := pow_ne_zero _ hZ_ne
    field_simp [hZ_ne]
    ring

/-- Integrating `hasDerivAt_ratio_fixed_spins_w` over `w ∼ γ_sh` at fixed `st : R → L`. -/
private lemma hasDerivAt_integral_w_ratio_fixed_spins
    {L K_sh K_aux R : Type*} [Fintype L]
    [Fintype K_sh] [Fintype K_aux] [Fintype R] [DecidableEq R]
    (p : L → ℝ) (hp0 : ∀ m, 0 ≤ p m) (hp1 : ∑ m, p m = 1)
    (X_sh Y_sh : L → K_sh → ℝ) (X_aux Y_aux : L → K_aux → ℝ)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) {B D₁ : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    {M₀ M₁ : R → ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀ r) (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁ r)
    (st : R → L) (s₀ : ℝ) :
    let γ_sh := Measure.pi fun _ : K_sh => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : K_aux => gaussianReal 0 1
    let S (s : ℝ) (w : K_sh → ℝ) (m : L) (η : K_aux → ℝ) : ℝ :=
      Real.cos s * (X_sh m ⬝ᵥ w + X_aux m ⬝ᵥ η) + Real.sin s * (Y_sh m ⬝ᵥ w + Y_aux m ⬝ᵥ η)
    let S' (s : ℝ) (w : K_sh → ℝ) (m : L) (η : K_aux → ℝ) : ℝ :=
      -Real.sin s * (X_sh m ⬝ᵥ w + X_aux m ⬝ᵥ η) + Real.cos s * (Y_sh m ⬝ᵥ w + Y_aux m ⬝ᵥ η)
    let ϕ (r : R) (x : ℝ) : ℝ := ψ r x * Real.exp (u x)
    let ϕ' (r : R) (x : ℝ) : ℝ := (deriv (ψ r) x + ψ r x * deriv u x) * Real.exp (u x)
    let Z (s : ℝ) (w : K_sh → ℝ) : ℝ := ∑ m : L, p m * ∫ η, Real.exp (u (S s w m η)) ∂γ_aux
    HasDerivAt
      (fun s => ∫ w, (∫ η : R → K_aux → ℝ, ∏ r, ϕ r (S s w (st r) (η r))
          ∂(Measure.pi fun _ : R => γ_aux)) / Z s w ^ Fintype.card R ∂γ_sh)
      ((∑ i : R, ∫ w, (∫ η : R → K_aux → ℝ, S' s₀ w (st i) (η i) *
            (ϕ' i (S s₀ w (st i) (η i)) *
              ∏ r ∈ Finset.univ.erase i, ϕ r (S s₀ w (st r) (η r)))
            ∂(Measure.pi fun _ : R => γ_aux)) / Z s₀ w ^ Fintype.card R ∂γ_sh) -
        (Fintype.card R : ℝ) * ∑ m : L, p m *
          ∫ w, ((∫ η : R → K_aux → ℝ, ∏ r, ϕ r (S s₀ w (st r) (η r))
              ∂(Measure.pi fun _ : R => γ_aux)) *
            ∫ η₀, S' s₀ w m η₀ * deriv u (S s₀ w m η₀) *
              Real.exp (u (S s₀ w m η₀)) ∂γ_aux) /
            Z s₀ w ^ (Fintype.card R + 1) ∂γ_sh)
      s₀ := by
  intro γ_sh γ_aux S S' ϕ ϕ' Z
  have hum : Measurable u := hu.continuous.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  have hϕm : ∀ r, Measurable (ϕ r) := fun r =>
    (hψd r).continuous.measurable.mul (Real.measurable_exp.comp hum)
  have hϕ'm : ∀ r, Measurable (ϕ' r) := fun r =>
    ((measurable_deriv _).add ((hψd r).continuous.measurable.mul hdu)).mul
      (Real.measurable_exp.comp hum)
  have hSw_m : ∀ s m, Measurable fun q : (K_sh → ℝ) × (K_aux → ℝ) => S s q.1 m q.2 := fun s m =>
    (((Finset.measurable_sum _ fun k _ =>
        measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
      (Finset.measurable_sum _ fun k _ =>
        measurable_const.mul ((measurable_pi_apply k).comp measurable_snd))).const_mul _).add
    (((Finset.measurable_sum _ fun k _ =>
        measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
      (Finset.measurable_sum _ fun k _ =>
        measurable_const.mul ((measurable_pi_apply k).comp measurable_snd))).const_mul _)
  have hS'w_m : ∀ s m, Measurable fun q : (K_sh → ℝ) × (K_aux → ℝ) => S' s q.1 m q.2 :=
    fun s m =>
      (((Finset.measurable_sum _ fun k _ =>
          measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
        (Finset.measurable_sum _ fun k _ =>
          measurable_const.mul ((measurable_pi_apply k).comp measurable_snd))).const_mul _).add
      (((Finset.measurable_sum _ fun k _ =>
          measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
        (Finset.measurable_sum _ fun k _ =>
          measurable_const.mul ((measurable_pi_apply k).comp measurable_snd))).const_mul _)
  have h1_w_m : ∀ (g : (K_sh → ℝ) × (K_aux → ℝ) → ℝ),
      Measurable g → Measurable fun w : K_sh → ℝ => ∫ η, g (w, η) ∂γ_aux := fun _ hg => by
    dsimp only [γ_aux]
    exact (hg.stronglyMeasurable.integral_prod_right'
      (ν := Measure.pi fun _ : K_aux => gaussianReal 0 1)).measurable
  have hZm : ∀ s, Measurable (Z s) := fun s =>
    Finset.measurable_sum _ fun m _ =>
      (h1_w_m _ (Real.measurable_exp.comp (hum.comp (hSw_m s m)))).const_mul _
  have hZ_ge : ∀ s w, Real.exp (-B) ≤ Z s w := fun s w => by
    have hlow : ∀ m : L, Real.exp (-B) ≤ ∫ η, Real.exp (u (S s w m η)) ∂γ_aux := fun m => by
      have hlin : Measurable fun η : K_aux → ℝ => S s w m η :=
        (((measurable_const.add (Finset.measurable_sum _ fun k _ =>
          measurable_const.mul (measurable_pi_apply k)))).const_mul _).add
        (((measurable_const.add (Finset.measurable_sum _ fun k _ =>
          measurable_const.mul (measurable_pi_apply k)))).const_mul _)
      have hint : Integrable (fun η : K_aux → ℝ => Real.exp (u (S s w m η))) γ_aux :=
        Integrable.of_bound (C := Real.exp B)
          (Real.measurable_exp.comp (hum.comp hlin)).aestronglyMeasurable
          (ae_of_all _ fun η => by
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact Real.exp_le_exp.2 (le_of_abs_le (hB _)))
      have hm := integral_mono (μ := γ_aux) (integrable_const (Real.exp (-B))) hint
        fun η => Real.exp_le_exp.2 (neg_le_of_abs_le (hB _))
      simpa [γ_aux] using hm
    calc Real.exp (-B) = (∑ m : L, p m) * Real.exp (-B) := by rw [hp1, one_mul]
      _ = ∑ m : L, p m * Real.exp (-B) := Finset.sum_mul _ _ _
      _ ≤ Z s w := Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hlow m) (hp0 m)
  let b_sh : (K_sh → ℝ) → ℝ := fun w =>
    ∑ m : L, ∑ k : K_sh, (|X_sh m k| + |Y_sh m k|) * |w k|
  let b_aux : (K_aux → ℝ) → ℝ := fun η =>
    ∑ m : L, ∑ k : K_aux, (|X_aux m k| + |Y_aux m k|) * |η k|
  have hb_sh_0 : ∀ w, 0 ≤ b_sh w := fun w =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hb_aux_0 : ∀ η, 0 ≤ b_aux η := fun η =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hb_sh_i : Integrable b_sh γ_sh :=
    integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun k _ =>
      (integrable_comp_eval (μ := fun _ : K_sh => gaussianReal 0 1) (i := k)
        (integrable_abs_id_gaussianReal (m := 0) (v := 1))).const_mul _
  have hb_aux_i : Integrable b_aux γ_aux :=
    integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun k _ =>
      (integrable_comp_eval (μ := fun _ : K_aux => gaussianReal 0 1) (i := k)
        (integrable_abs_id_gaussianReal (m := 0) (v := 1))).const_mul _
  have hS'_le : ∀ s w m η, |S' s w m η| ≤ b_sh w + b_aux η := fun s w m η => by
    have h1 : |S' s w m η| ≤ |X_sh m ⬝ᵥ w + X_aux m ⬝ᵥ η| + |Y_sh m ⬝ᵥ w + Y_aux m ⬝ᵥ η| := by
      calc |S' s w m η| ≤ |-Real.sin s * (X_sh m ⬝ᵥ w + X_aux m ⬝ᵥ η)| +
            |Real.cos s * (Y_sh m ⬝ᵥ w + Y_aux m ⬝ᵥ η)| := abs_add_le _ _
        _ = |Real.sin s| * |X_sh m ⬝ᵥ w + X_aux m ⬝ᵥ η| +
            |Real.cos s| * |Y_sh m ⬝ᵥ w + Y_aux m ⬝ᵥ η| := by rw [abs_mul, abs_mul, abs_neg]
        _ ≤ 1 * |X_sh m ⬝ᵥ w + X_aux m ⬝ᵥ η| + 1 * |Y_sh m ⬝ᵥ w + Y_aux m ⬝ᵥ η| :=
            add_le_add (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one s) (abs_nonneg _))
              (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one s) (abs_nonneg _))
        _ = _ := by ring
    have h2 : |X_sh m ⬝ᵥ w + X_aux m ⬝ᵥ η| + |Y_sh m ⬝ᵥ w + Y_aux m ⬝ᵥ η| ≤
        (|X_sh m ⬝ᵥ w| + |Y_sh m ⬝ᵥ w|) + (|X_aux m ⬝ᵥ η| + |Y_aux m ⬝ᵥ η|) := by
      linarith [abs_add_le (X_sh m ⬝ᵥ w) (X_aux m ⬝ᵥ η),
        abs_add_le (Y_sh m ⬝ᵥ w) (Y_aux m ⬝ᵥ η)]
    refine (h1.trans h2).trans (add_le_add ?_ ?_)
    · have hx : |X_sh m ⬝ᵥ w| + |Y_sh m ⬝ᵥ w| ≤
          ∑ k : K_sh, (|X_sh m k| + |Y_sh m k|) * |w k| := by
        calc _ ≤ (∑ k, |X_sh m k * w k|) + ∑ k, |Y_sh m k * w k| :=
              add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
          _ = _ := by simp_rw [← Finset.sum_add_distrib, abs_mul, add_mul]
      exact hx.trans (Finset.single_le_sum
        (f := fun m' : L => ∑ k : K_sh, (|X_sh m' k| + |Y_sh m' k|) * |w k|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ m))
    · have hy : |X_aux m ⬝ᵥ η| + |Y_aux m ⬝ᵥ η| ≤
          ∑ k : K_aux, (|X_aux m k| + |Y_aux m k|) * |η k| := by
        calc _ ≤ (∑ k, |X_aux m k * η k|) + ∑ k, |Y_aux m k * η k| :=
              add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
          _ = _ := by simp_rw [← Finset.sum_add_distrib, abs_mul, add_mul]
      exact hy.trans (Finset.single_le_sum
        (f := fun m' : L => ∑ k : K_aux, (|X_aux m' k| + |Y_aux m' k|) * |η k|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ m))
  have hϕb : ∀ r x, |ϕ r x| ≤ |M₀ r| * Real.exp B := fun r x =>
    abs_mul_exp_le ((hM₀ r x).trans (le_abs_self _)) (le_of_abs_le (hB x))
  have hϕ'b : ∀ r x, |ϕ' r x| ≤ (|M₁ r| + |M₀ r| * |D₁|) * Real.exp B := fun r x => by
    refine abs_mul_exp_le ?_ (le_of_abs_le (hB x))
    refine (abs_add_le _ _).trans (add_le_add ((hM₁ r x).trans (le_abs_self _)) ?_)
    rw [abs_mul]
    exact mul_le_mul ((hM₀ r x).trans (le_abs_self _)) ((hD₁ x).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  let C_ϕ : ℝ := ∏ r, (|M₀ r| * Real.exp B)
  let C_i : R → ℝ := fun i => ((|M₁ i| + |M₀ i| * |D₁|) * Real.exp B) *
    ∏ r ∈ Finset.univ.erase i, (|M₀ r| * Real.exp B)
  let C_η : ℝ := ∫ η, b_aux η ∂γ_aux
  have hCη0 : 0 ≤ C_η := integral_nonneg hb_aux_0
  obtain ⟨F_w, hF_w⟩ : ∃ F_w : ℝ → (K_sh → ℝ) → ℝ, ∀ s w, F_w s w =
      (∫ η : R → K_aux → ℝ, ∏ r, ϕ r (S s w (st r) (η r)) ∂(Measure.pi fun _ : R => γ_aux)) /
        Z s w ^ Fintype.card R := ⟨_, fun _ _ => rfl⟩
  obtain ⟨D1_w, hD1_w⟩ : ∃ D1_w : R → ℝ → (K_sh → ℝ) → ℝ, ∀ i s w, D1_w i s w =
      (∫ η : R → K_aux → ℝ, S' s w (st i) (η i) *
        (ϕ' i (S s w (st i) (η i)) * ∏ r ∈ Finset.univ.erase i, ϕ r (S s w (st r) (η r)))
        ∂(Measure.pi fun _ : R => γ_aux)) / Z s w ^ Fintype.card R := ⟨_, fun _ _ _ => rfl⟩
  obtain ⟨D2_w, hD2_w⟩ : ∃ D2_w : L → ℝ → (K_sh → ℝ) → ℝ, ∀ m s w, D2_w m s w =
      ((∫ η : R → K_aux → ℝ, ∏ r, ϕ r (S s w (st r) (η r)) ∂(Measure.pi fun _ : R => γ_aux)) *
        ∫ η₀, S' s w m η₀ * deriv u (S s w m η₀) * Real.exp (u (S s w m η₀)) ∂γ_aux) /
        Z s w ^ (Fintype.card R + 1) := ⟨_, fun _ _ _ => rfl⟩
  have hprod_w_eq : ∀ s w,
      (∫ η : R → K_aux → ℝ, ∏ r, ϕ r (S s w (st r) (η r)) ∂(Measure.pi fun _ : R => γ_aux)) =
        ∏ r, ∫ η, ϕ r (S s w (st r) η) ∂γ_aux := fun s w =>
    integral_fintype_prod_eq_prod (μ := fun _ : R => Measure.pi fun _ : K_aux => gaussianReal 0 1)
      (fun r η => ϕ r (S s w (st r) η))
  have hD1_num_eq : ∀ i s w,
      (∫ η : R → K_aux → ℝ, S' s w (st i) (η i) *
          (ϕ' i (S s w (st i) (η i)) * ∏ r ∈ Finset.univ.erase i, ϕ r (S s w (st r) (η r)))
        ∂(Measure.pi fun _ : R => γ_aux)) =
      (∫ η, S' s w (st i) η * ϕ' i (S s w (st i) η) ∂γ_aux) *
        ∏ r ∈ Finset.univ.erase i, ∫ η, ϕ r (S s w (st r) η) ∂γ_aux := by
    intro i s w
    let g_r : R → (K_aux → ℝ) → ℝ := fun r η =>
      if r = i then S' s w (st i) η * ϕ' i (S s w (st i) η) else ϕ r (S s w (st r) η)
    have hprod_g : ∀ η : R → K_aux → ℝ,
        S' s w (st i) (η i) *
          (ϕ' i (S s w (st i) (η i)) * ∏ r ∈ Finset.univ.erase i, ϕ r (S s w (st r) (η r))) =
        ∏ r : R, g_r r (η r) := fun η => by
      rw [← Finset.mul_prod_erase Finset.univ (fun r => g_r r (η r)) (Finset.mem_univ i)]
      simp only [g_r, ↓reduceIte, mul_assoc]
      congr 2
      exact Finset.prod_congr rfl fun r hr => by simp [Finset.ne_of_mem_erase hr]
    simp_rw [hprod_g]
    rw [integral_fintype_prod_eq_prod
        (μ := fun _ : R => Measure.pi fun _ : K_aux => gaussianReal 0 1) g_r,
      ← Finset.mul_prod_erase Finset.univ (fun r => ∫ η, g_r r η ∂γ_aux) (Finset.mem_univ i)]
    simp only [g_r, ↓reduceIte]
    congr 1
    exact Finset.prod_congr rfl fun r hr => by simp [Finset.ne_of_mem_erase hr]
  have hprod_w_m : ∀ s, Measurable fun w : K_sh → ℝ =>
      ∫ η : R → K_aux → ℝ, ∏ r, ϕ r (S s w (st r) (η r)) ∂(Measure.pi fun _ : R => γ_aux) := by
    intro s
    have heq : (fun w : K_sh → ℝ => ∫ η : R → K_aux → ℝ, ∏ r, ϕ r (S s w (st r) (η r))
          ∂(Measure.pi fun _ : R => γ_aux)) =
        fun w => ∏ r, ∫ η, ϕ r (S s w (st r) η) ∂γ_aux := funext (hprod_w_eq s)
    rw [heq]
    exact Finset.measurable_prod _ fun r _ =>
      h1_w_m (fun q => ϕ r (S s q.1 (st r) q.2)) ((hϕm r).comp (hSw_m s (st r)))
  have hFw_m : ∀ s, Measurable (F_w s) := fun s => by
    rw [show F_w s = _ from funext (hF_w s)]
    exact (hprod_w_m s).div ((hZm s).pow_const _)
  have hD1w_m : ∀ i s, Measurable (D1_w i s) := fun i s => by
    have heq : D1_w i s = fun w =>
        ((∫ η, S' s w (st i) η * ϕ' i (S s w (st i) η) ∂γ_aux) *
          ∏ r ∈ Finset.univ.erase i, ∫ η, ϕ r (S s w (st r) η) ∂γ_aux) /
          Z s w ^ Fintype.card R :=
      funext fun w =>
        (hD1_w i s w).trans (congrArg (· / Z s w ^ Fintype.card R) (hD1_num_eq i s w))
    rw [heq]
    have h_head := h1_w_m (fun q => S' s q.1 (st i) q.2 * ϕ' i (S s q.1 (st i) q.2))
      ((hS'w_m s (st i)).mul ((hϕ'm i).comp (hSw_m s (st i))))
    have h_tail : Measurable fun w : K_sh → ℝ =>
        ∏ r ∈ Finset.univ.erase i, ∫ η, ϕ r (S s w (st r) η) ∂γ_aux :=
      Finset.measurable_prod _ fun r _ =>
        h1_w_m (fun q => ϕ r (S s q.1 (st r) q.2)) ((hϕm r).comp (hSw_m s (st r)))
    exact (h_head.mul h_tail).div ((hZm s).pow_const _)
  have hD2w_m : ∀ m s, Measurable (D2_w m s) := fun m s => by
    rw [show D2_w m s = _ from funext (hD2_w m s)]
    have hj2 : Measurable fun q : (K_sh → ℝ) × (K_aux → ℝ) =>
        S' s q.1 m q.2 * deriv u (S s q.1 m q.2) * Real.exp (u (S s q.1 m q.2)) :=
      (((hS'w_m s m).mul (hdu.comp (hSw_m s m))).mul
        (Real.measurable_exp.comp (hum.comp (hSw_m s m))))
    exact ((hprod_w_m s).mul (h1_w_m _ hj2)).div ((hZm s).pow_const _)
  have hprod_bd : ∀ s w, |∫ η : R → K_aux → ℝ, ∏ r, ϕ r (S s w (st r) (η r))
      ∂(Measure.pi fun _ : R => γ_aux)| ≤ C_ϕ := fun s w =>
    abs_integral_le_of_forall_abs_le
      (Measure.pi fun _ : R => Measure.pi fun _ : K_aux => gaussianReal 0 1)
      (f := fun η : R → K_aux → ℝ => ∏ r, ϕ r (S s w (st r) (η r))) (M := C_ϕ) fun η => by
        rw [Finset.abs_prod]
        exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hϕb r _
  have hFw_bd : ∀ s w, |F_w s w| ≤ C_ϕ / Real.exp (-B) ^ Fintype.card R := fun s w => by
    rw [hF_w, abs_div, abs_of_pos (pow_pos ((Real.exp_pos _).trans_le (hZ_ge s w)) _)]
    exact div_le_div₀ (Finset.prod_nonneg fun _ _ => by positivity) (hprod_bd s w)
      (pow_pos (Real.exp_pos _) _) (pow_le_pow_left₀ (Real.exp_pos _).le (hZ_ge s w) _)
  have hD1w_bd : ∀ i s w, |D1_w i s w| ≤
      (C_i i * (b_sh w + C_η)) / Real.exp (-B) ^ Fintype.card R := fun i s w => by
    rw [hD1_w, abs_div, abs_of_pos (pow_pos ((Real.exp_pos _).trans_le (hZ_ge s w)) _)]
    refine div_le_div₀ (mul_nonneg (mul_nonneg (by positivity)
        (Finset.prod_nonneg fun _ _ => by positivity)) (add_nonneg (hb_sh_0 w) hCη0)) ?_
      (pow_pos (Real.exp_pos _) _) (pow_le_pow_left₀ (Real.exp_pos _).le (hZ_ge s w) _)
    have hb_eta : Integrable (fun η : R → K_aux → ℝ => C_i i * (b_sh w + b_aux (η i)))
        (Measure.pi fun _ : R => γ_aux) :=
      ((integrable_const (b_sh w)).add
        (integrable_comp_eval (μ := fun _ : R => γ_aux) (i := i) hb_aux_i)).const_mul (C_i i)
    calc |∫ η : R → K_aux → ℝ, S' s w (st i) (η i) *
            (ϕ' i (S s w (st i) (η i)) * ∏ r ∈ Finset.univ.erase i, ϕ r (S s w (st r) (η r)))
            ∂(Measure.pi fun _ : R => γ_aux)|
        ≤ ∫ η : R → K_aux → ℝ, C_i i * (b_sh w + b_aux (η i))
            ∂(Measure.pi fun _ : R => γ_aux) := by
          refine abs_integral_le_integral_abs.trans
            (integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) hb_eta
              (ae_of_all _ fun η => ?_))
          dsimp only
          rw [abs_mul, abs_mul, Finset.abs_prod, mul_comm (C_i i)]
          exact mul_le_mul (hS'_le s w (st i) (η i))
            (mul_le_mul (hϕ'b i _)
              (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hϕb r _)
              (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity))
            (by positivity) (add_nonneg (hb_sh_0 w) (hb_aux_0 (η i)))
      _ = C_i i * (b_sh w + C_η) := by
          rw [integral_const_mul, integral_add (integrable_const _)
            (integrable_comp_eval (μ := fun _ : R => γ_aux) (i := i) hb_aux_i),
            integral_const, probReal_univ, one_smul,
            integral_pi_eval γ_aux i b_aux hb_aux_i.aestronglyMeasurable]
  have hD2w_bd : ∀ m s w, |D2_w m s w| ≤
      (C_ϕ * (|D₁| * Real.exp B) * (b_sh w + C_η)) / Real.exp (-B) ^ (Fintype.card R + 1) := by
    intro m s w
    rw [hD2_w, abs_div, abs_mul, abs_of_pos (pow_pos ((Real.exp_pos _).trans_le (hZ_ge s w)) _)]
    refine div_le_div₀ (mul_nonneg (mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity)
        (by positivity)) (add_nonneg (hb_sh_0 w) hCη0)) ?_
      (pow_pos (Real.exp_pos _) _) (pow_le_pow_left₀ (Real.exp_pos _).le (hZ_ge s w) _)
    have hb1 := hprod_bd s w
    have hb2 : |∫ η₀, S' s w m η₀ * deriv u (S s w m η₀) * Real.exp (u (S s w m η₀)) ∂γ_aux| ≤
        (|D₁| * Real.exp B) * (b_sh w + C_η) := by
      calc _ ≤ ∫ η₀, (b_sh w + b_aux η₀) * (|D₁| * Real.exp B) ∂γ_aux := by
            refine abs_integral_le_integral_abs.trans
              (integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
                (((integrable_const (b_sh w)).add hb_aux_i).mul_const _)
                (ae_of_all _ fun η₀ => ?_))
            dsimp only
            rw [mul_assoc, abs_mul]
            exact mul_le_mul (hS'_le s w m η₀)
              (abs_mul_exp_le ((hD₁ _).trans (le_abs_self _)) (le_of_abs_le (hB _)))
              (abs_nonneg _) (add_nonneg (hb_sh_0 w) (hb_aux_0 η₀))
        _ = (|D₁| * Real.exp B) * (b_sh w + C_η) := by
            rw [integral_mul_const, integral_add (integrable_const _) hb_aux_i,
              integral_const, probReal_univ, one_smul, mul_comm]
    calc _ ≤ C_ϕ * ((|D₁| * Real.exp B) * (b_sh w + C_η)) :=
          mul_le_mul hb1 hb2 (abs_nonneg _) (Finset.prod_nonneg fun _ _ => by positivity)
      _ = _ := by ring
  have hD1w_int : ∀ i, Integrable (D1_w i s₀) γ_sh := fun i =>
    ((((hb_sh_i.add (integrable_const C_η)).const_mul (C_i i)).div_const _)).mono'
      (hD1w_m i s₀).aestronglyMeasurable
      (ae_of_all _ fun w => (Real.norm_eq_abs _).trans_le (hD1w_bd i s₀ w))
  have hD2w_int : ∀ m, Integrable (D2_w m s₀) γ_sh := fun m =>
    ((((hb_sh_i.add (integrable_const C_η)).const_mul
        (C_ϕ * (|D₁| * Real.exp B))).div_const _)).mono'
      (hD2w_m m s₀).aestronglyMeasurable
      (ae_of_all _ fun w => (Real.norm_eq_abs _).trans_le (hD2w_bd m s₀ w))
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := γ_sh)
    (F := F_w)
    (F' := fun s w => (∑ i : R, D1_w i s w) - (Fintype.card R : ℝ) * ∑ m : L, p m * D2_w m s w)
    (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun s => (hFw_m s).aestronglyMeasurable)
    (Integrable.of_bound (C := C_ϕ / Real.exp (-B) ^ Fintype.card R)
      (hFw_m s₀).aestronglyMeasurable
      (ae_of_all _ fun w => (Real.norm_eq_abs _).trans_le (hFw_bd s₀ w)))
    ((Finset.measurable_sum _ fun i _ => hD1w_m i s₀).sub
      ((Finset.measurable_sum _ fun m _ =>
        (hD2w_m m s₀).const_mul _).const_mul _)).aestronglyMeasurable
    (bound := fun w => (∑ i : R, (C_i i * (b_sh w + C_η)) / Real.exp (-B) ^ Fintype.card R) +
      (Fintype.card R : ℝ) * ∑ m : L, p m *
        ((C_ϕ * (|D₁| * Real.exp B) * (b_sh w + C_η)) / Real.exp (-B) ^ (Fintype.card R + 1)))
    (ae_of_all _ fun w s _ => by
      rw [Real.norm_eq_abs]
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · exact Finset.abs_sum_le_sum_of_abs_le _ fun i _ => hD1w_bd i s w
      · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        refine Finset.abs_sum_le_sum_of_abs_le _ fun m _ => ?_
        rw [abs_mul, abs_of_nonneg (hp0 m)]
        exact mul_le_mul_of_nonneg_left (hD2w_bd m s w) (hp0 m))
    ((integrable_finsetSum _ fun i _ =>
        ((hb_sh_i.add (integrable_const C_η)).const_mul (C_i i)).div_const _).add
      ((integrable_finsetSum _ fun m _ =>
        (((hb_sh_i.add (integrable_const C_η)).const_mul
          (C_ϕ * (|D₁| * Real.exp B))).div_const _).const_mul (p m)).const_mul _))
    (ae_of_all _ fun w s _ => by
      simp_rw [hF_w, hD1_w, hD2_w]
      exact hasDerivAt_ratio_fixed_spins_w p hp0 hp1 X_sh Y_sh X_aux Y_aux hu hB hD₁ ψ hψd
        hM₀ hM₁ st w s)).2
  have hfun : (fun s => ∫ w, F_w s w ∂γ_sh) =
      fun s => ∫ w, (∫ η : R → K_aux → ℝ, ∏ r, ϕ r (S s w (st r) (η r))
        ∂(Measure.pi fun _ : R => γ_aux)) / Z s w ^ Fintype.card R ∂γ_sh :=
    funext fun s => integral_congr_ae (ae_of_all _ fun w => hF_w s w)
  rw [← hfun]
  refine hd.congr_deriv ?_
  rw [integral_sub (integrable_finsetSum _ fun i _ => hD1w_int i)
      ((integrable_finsetSum _ fun m _ => (hD2w_int m).const_mul (p m)).const_mul _),
    integral_finsetSum _ fun i _ => hD1w_int i,
    integral_const_mul,
    integral_finsetSum _ fun m _ => (hD2w_int m).const_mul (p m)]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => integral_congr_ae (ae_of_all _ fun w => hD1_w i s₀ w)
  · congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_const_mul]
    congr 1
    exact integral_congr_ae (ae_of_all _ fun w => hD2_w m s₀ w)

/-- **Pathwise derivative of a quenched tilted replica average along a Gaussian rotation, with
only `L¹`-integrability of `f`.** Under an old-state probability measure `μ₀` with finite spin
projection `π : α → L`, shared standard Gaussian `w` and per-replica auxiliary standard Gaussian
`η`, the quenched expectation of `⟨f(σ.1) * ∏_r ψ_r(S_s(σ_r))⟩_{u(S_s)}` has derivative at `s₀`
given by the `R` replica terms plus the fresh-replica normalizer term. Only `Integrable f (pi μ₀)`
is assumed of `f`. -/
theorem hasDerivAt_integral_gaussian_tilted_rotation
    {α L K_sh K_aux R : Type*} [MeasurableSpace α]
    [Finite L] [MeasurableSpace L] [MeasurableSingletonClass L]
    [Fintype K_sh] [Fintype K_aux] [Fintype R] [DecidableEq R]
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (π : α → L) (hπ : Measurable π)
    (X_sh Y_sh : L → K_sh → ℝ) (X_aux Y_aux : L → K_aux → ℝ)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) {B D₁ : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    {M₀ M₁ : R → ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀ r) (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁ r)
    {f : (R → α) → ℝ} (hfi : Integrable f (Measure.pi fun _ : R => μ₀))
    (s₀ : ℝ) :
    let γ_sh := Measure.pi fun _ : K_sh => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : K_aux => gaussianReal 0 1
    let S (s : ℝ) (w : K_sh → ℝ) (q : α × (K_aux → ℝ)) : ℝ :=
      Real.cos s * (X_sh (π q.1) ⬝ᵥ w + X_aux (π q.1) ⬝ᵥ q.2) +
        Real.sin s * (Y_sh (π q.1) ⬝ᵥ w + Y_aux (π q.1) ⬝ᵥ q.2)
    let S' (s : ℝ) (w : K_sh → ℝ) (q : α × (K_aux → ℝ)) : ℝ :=
      -Real.sin s * (X_sh (π q.1) ⬝ᵥ w + X_aux (π q.1) ⬝ᵥ q.2) +
        Real.cos s * (Y_sh (π q.1) ⬝ᵥ w + Y_aux (π q.1) ⬝ᵥ q.2)
    HasDerivAt
      (fun s => ∫ w, ∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) * ∏ r, ψ r (S s w (σ r))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh)
      ((∑ i : R, ∫ w, ∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) * S' s₀ w (σ i) *
            ((deriv (ψ i) (S s₀ w (σ i)) + ψ i (S s₀ w (σ i)) * deriv u (S s₀ w (σ i))) *
              ∏ r ∈ Finset.univ.erase i, ψ r (S s₀ w (σ r)))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh) -
        (Fintype.card R : ℝ) * ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
          f (fun r => (σ (some r)).1) * S' s₀ w (σ none) *
            (∏ r : R, ψ r (S s₀ w (σ (some r)))) * deriv u (S s₀ w (σ none))
          ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh)
      s₀ := by
  classical
  have := Fintype.ofFinite L
  intro γ_sh γ_aux S S'
  have hum : Measurable u := hu.continuous.measurable
  have hdu : Measurable (deriv u) := measurable_deriv u
  let p : L → ℝ := fun m => (μ₀.map π).real {m}
  have hp0 : ∀ m, 0 ≤ p m := fun m => ENNReal.toReal_nonneg
  have hp1 : ∑ m : L, p m = 1 := by
    have : IsProbabilityMeasure (μ₀.map π) :=
      (Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).2 inferInstance
    have hsum := integral_fintype (μ := μ₀.map π) (f := fun _ : L => (1 : ℝ)) Integrable.of_finite
    simp only [smul_eq_mul, mul_one, integral_const, probReal_univ] at hsum
    exact hsum.symm
  let α_sh : ℝ → L → K_sh → ℝ := fun s m k => Real.cos s * X_sh m k + Real.sin s * Y_sh m k
  let α_aux : ℝ → L → K_aux → ℝ := fun s m k => Real.cos s * X_aux m k + Real.sin s * Y_aux m k
  let W_sh : ℝ → L → K_sh → ℝ := fun s m k => -Real.sin s * X_sh m k + Real.cos s * Y_sh m k
  let W_aux : ℝ → L → K_aux → ℝ := fun s m k => -Real.sin s * X_aux m k + Real.cos s * Y_aux m k
  let S_m : ℝ → (K_sh → ℝ) → L → (K_aux → ℝ) → ℝ := fun s w m η =>
    Real.cos s * (X_sh m ⬝ᵥ w + X_aux m ⬝ᵥ η) + Real.sin s * (Y_sh m ⬝ᵥ w + Y_aux m ⬝ᵥ η)
  let S'_m : ℝ → (K_sh → ℝ) → L → (K_aux → ℝ) → ℝ := fun s w m η =>
    -Real.sin s * (X_sh m ⬝ᵥ w + X_aux m ⬝ᵥ η) + Real.cos s * (Y_sh m ⬝ᵥ w + Y_aux m ⬝ᵥ η)
  have hSm_lin : ∀ s w m η, α_sh s m ⬝ᵥ w + α_aux s m ⬝ᵥ η = S_m s w m η := fun s w m η => by
    dsimp only [S_m, α_sh, α_aux, dotProduct]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  have hS'm_lin : ∀ s w m η, W_sh s m ⬝ᵥ w + W_aux s m ⬝ᵥ η = S'_m s w m η := fun s w m η => by
    dsimp only [S'_m, W_sh, W_aux, dotProduct]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  have hS_lin : ∀ s w (q : α × (K_aux → ℝ)),
      S s w q = α_sh s (π q.1) ⬝ᵥ w + α_aux s (π q.1) ⬝ᵥ q.2 :=
    fun s w q => (hSm_lin s w (π q.1) q.2).symm
  have hS'_lin : ∀ s w (q : α × (K_aux → ℝ)),
      S' s w q = W_sh s (π q.1) ⬝ᵥ w + W_aux s (π q.1) ⬝ᵥ q.2 :=
    fun s w q => (hS'm_lin s w (π q.1) q.2).symm
  let ϕ : R → ℝ → ℝ := fun r x => ψ r x * Real.exp (u x)
  let ϕ' : R → ℝ → ℝ := fun r x => (deriv (ψ r) x + ψ r x * deriv u x) * Real.exp (u x)
  have hϕb : ∀ r x, |ϕ r x| ≤ |M₀ r| * Real.exp B := fun r x =>
    abs_mul_exp_le ((hM₀ r x).trans (le_abs_self _)) (le_of_abs_le (hB x))
  have hϕ'b : ∀ r x, |ϕ' r x| ≤ (|M₁ r| + |M₀ r| * |D₁|) * Real.exp B := fun r x => by
    refine abs_mul_exp_le ?_ (le_of_abs_le (hB x))
    refine (abs_add_le _ _).trans (add_le_add ((hM₁ r x).trans (le_abs_self _)) ?_)
    rw [abs_mul]
    exact mul_le_mul ((hM₀ r x).trans (le_abs_self _)) ((hD₁ x).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  let C_ϕ : ℝ := ∏ r, (|M₀ r| * Real.exp B)
  let Z : ℝ → (K_sh → ℝ) → ℝ := fun s w =>
    ∑ m : L, p m * ∫ η, Real.exp (u (S_m s w m η)) ∂γ_aux
  obtain ⟨I_st, hI_st⟩ : ∃ I_st : ℝ → (R → L) → ℝ, ∀ s st, I_st s st =
      ∫ w, (∫ η : R → K_aux → ℝ, ∏ r, ϕ r (S_m s w (st r) (η r))
        ∂(Measure.pi fun _ : R => γ_aux)) / Z s w ^ Fintype.card R ∂γ_sh :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨I'_st, hI'_st⟩ : ∃ I'_st : (R → L) → ℝ, ∀ st, I'_st st =
      (∑ i : R, ∫ w, (∫ η : R → K_aux → ℝ, S'_m s₀ w (st i) (η i) *
            (ϕ' i (S_m s₀ w (st i) (η i)) *
              ∏ r ∈ Finset.univ.erase i, ϕ r (S_m s₀ w (st r) (η r)))
            ∂(Measure.pi fun _ : R => γ_aux)) / Z s₀ w ^ Fintype.card R ∂γ_sh) -
        (Fintype.card R : ℝ) * ∑ m : L, p m *
          ∫ w, ((∫ η : R → K_aux → ℝ, ∏ r, ϕ r (S_m s₀ w (st r) (η r))
              ∂(Measure.pi fun _ : R => γ_aux)) *
            ∫ η₀, S'_m s₀ w m η₀ * deriv u (S_m s₀ w m η₀) *
              Real.exp (u (S_m s₀ w m η₀)) ∂γ_aux) /
            Z s₀ w ^ (Fintype.card R + 1) ∂γ_sh :=
    ⟨_, fun _ => rfl⟩
  have hIst_d : ∀ st, HasDerivAt (fun s => I_st s st) (I'_st st) s₀ := fun st => by
    rw [show (fun s => I_st s st) = _ from funext fun s => hI_st s st, hI'_st]
    exact hasDerivAt_integral_w_ratio_fixed_spins p hp0 hp1 X_sh Y_sh X_aux Y_aux hu hB hD₁
      ψ hψd hM₀ hM₁ st s₀
  have hLHS_fub : ∀ s,
      ∫ w, ∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) * ∏ r, ψ r (S s w (σ r))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh =
        ∫ a : R → α, f a * I_st s (fun r => π (a r)) ∂(Measure.pi fun _ : R => μ₀) := by
    intro s
    simp_rw [hS_lin s]
    have hfub := integral_tilted_replica_fubini μ₀ π hπ (α_sh s) (α_aux s) hum hB hfi
      (fun w σ => ∏ r, ψ r (α_sh s (π (σ r).1) ⬝ᵥ w + α_aux s (π (σ r).1) ⬝ᵥ (σ r).2))
      (fun st w η => ∏ r, ϕ r (S_m s w (st r) (η r)))
      (fun w σ => by
        rw [Real.exp_sum, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun r _ => by rw [hSm_lin])
      (fun st => Finset.measurable_prod _ fun r _ =>
        ((hψd r).continuous.measurable.mul (Real.measurable_exp.comp hum)).comp
          ((((Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
            (Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp
                ((measurable_pi_apply r).comp measurable_snd)))).const_mul _).add
          ((((Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
            (Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp
                ((measurable_pi_apply r).comp measurable_snd)))).const_mul _))))
      (bw := fun _ => C_ϕ) (integrable_const _)
      (bη := fun _ => 0) (integrable_const _)
      (fun st w η => by
        rw [add_zero, Finset.abs_prod]
        exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hϕb r _)
    dsimp only at hfub
    have hZ_eq_s : ∀ w,
        (∑ m : L, (μ₀.map π).real {m} *
          ∫ η, Real.exp (u (α_sh s m ⬝ᵥ w + α_aux s m ⬝ᵥ η)) ∂γ_aux) = Z s w :=
      fun w => Finset.sum_congr rfl fun m _ => congrArg (p m * ·)
        (integral_congr_ae (ae_of_all _ fun η => by dsimp only; rw [hSm_lin]))
    have hI_eq_s : ∀ a : R → α,
        (∫ w, (∫ η : R → K_aux → ℝ, ∏ r, ϕ r (S_m s w (π (a r)) (η r))
            ∂(Measure.pi fun _ : R => γ_aux)) /
          (∑ m : L, (μ₀.map π).real {m} *
            ∫ η, Real.exp (u (α_sh s m ⬝ᵥ w + α_aux s m ⬝ᵥ η)) ∂γ_aux) ^
              Fintype.card R ∂γ_sh) =
        I_st s (fun r => π (a r)) := fun a => by
      rw [hI_st]
      exact integral_congr_ae (ae_of_all _ fun w => by dsimp only; rw [hZ_eq_s w])
    exact hfub.trans (integral_congr_ae (ae_of_all _ fun a => by dsimp only; rw [hI_eq_s a]))
  have h_finite_sum : ∀ (g : (R → L) → ℝ),
      ∫ a : R → α, f a * g (fun r => π (a r)) ∂(Measure.pi fun _ : R => μ₀) =
        ∑ st : R → L, (∫ a : R → α, (if (fun r => π (a r)) = st then f a else 0)
          ∂(Measure.pi fun _ : R => μ₀)) * g st := by
    intro g
    have hπa : Measurable fun a : R → α => (fun r => π (a r)) :=
      measurable_pi_iff.2 fun r => hπ.comp (measurable_pi_apply r)
    have hsum_pt : ∀ a : R → α, f a * g (fun r => π (a r)) =
        ∑ st : R → L, (if (fun r => π (a r)) = st then f a else 0) * g st := fun a => by
      rw [Finset.sum_eq_single (fun r => π (a r))
        (fun st' _ hne => by simp [Ne.symm hne]) (by simp)]
      simp
    simp_rw [hsum_pt]
    have hint_st : ∀ st : R → L, Integrable (fun a : R → α =>
        (if (fun r => π (a r)) = st then f a else 0) * g st) (Measure.pi fun _ : R => μ₀) := by
      intro st
      have h1 : Integrable (fun a : R → α => if (fun r => π (a r)) = st then f a else 0)
          (Measure.pi fun _ : R => μ₀) := by
        have heq : (fun a : R → α => if (fun r => π (a r)) = st then f a else 0) =
            fun a => (if (fun r => π (a r)) = st then (1 : ℝ) else 0) * f a := by
          ext a; split_ifs <;> simp
        rw [heq]
        exact hfi.bdd_mul_of_abs_le (C := 1)
          ((measurable_of_finite fun t =>
            if t = st then (1 : ℝ) else 0).comp hπa).aestronglyMeasurable
          (ae_of_all _ fun a => by split_ifs <;> norm_num)
      exact h1.mul_const (g st)
    rw [integral_finsetSum _ fun st _ => hint_st st]
    exact Finset.sum_congr rfl fun st _ => integral_mul_const _ _
  have hLHS_d : HasDerivAt
      (fun s => ∫ w, ∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) * ∏ r, ψ r (S s w (σ r))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh)
      (∫ a : R → α, f a * I'_st (fun r => π (a r)) ∂(Measure.pi fun _ : R => μ₀)) s₀ := by
    simp_rw [hLHS_fub, h_finite_sum]
    exact HasDerivAt.fun_sum fun st _ => (hIst_d st).const_mul _
  refine hLHS_d.congr_deriv ?_
  let C_i : R → ℝ := fun i => ((|M₁ i| + |M₀ i| * |D₁|) * Real.exp B) *
    ∏ r ∈ Finset.univ.erase i, (|M₀ r| * Real.exp B)
  have hZ_eq_s0 : ∀ w,
      (∑ m : L, (μ₀.map π).real {m} *
        ∫ η, Real.exp (u (α_sh s₀ m ⬝ᵥ w + α_aux s₀ m ⬝ᵥ η)) ∂γ_aux) = Z s₀ w :=
    fun w => Finset.sum_congr rfl fun m _ => congrArg (p m * ·)
      (integral_congr_ae (ae_of_all _ fun η => by dsimp only; rw [hSm_lin]))
  have hRHS1 : ∀ i : R,
      ∫ w, ∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) * S' s₀ w (σ i) *
            ((deriv (ψ i) (S s₀ w (σ i)) + ψ i (S s₀ w (σ i)) * deriv u (S s₀ w (σ i))) *
              ∏ r ∈ Finset.univ.erase i, ψ r (S s₀ w (σ r)))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh =
        ∫ a : R → α, f a *
          ∫ w, (∫ η : R → K_aux → ℝ, S'_m s₀ w (π (a i)) (η i) *
              (ϕ' i (S_m s₀ w (π (a i)) (η i)) *
                ∏ r ∈ Finset.univ.erase i, ϕ r (S_m s₀ w (π (a r)) (η r)))
              ∂(Measure.pi fun _ : R => γ_aux)) / Z s₀ w ^ Fintype.card R ∂γ_sh
          ∂(Measure.pi fun _ : R => μ₀) := by
    intro i
    have heq_in : (fun w => ∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) * S' s₀ w (σ i) *
            ((deriv (ψ i) (S s₀ w (σ i)) + ψ i (S s₀ w (σ i)) * deriv u (S s₀ w (σ i))) *
              ∏ r ∈ Finset.univ.erase i, ψ r (S s₀ w (σ r)))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q)))) =
        fun w => ∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) *
            (S' s₀ w (σ i) *
              ((deriv (ψ i) (S s₀ w (σ i)) + ψ i (S s₀ w (σ i)) * deriv u (S s₀ w (σ i))) *
                ∏ r ∈ Finset.univ.erase i, ψ r (S s₀ w (σ r))))
          ∂(Measure.pi fun _ : R =>
            (μ₀.prod γ_aux).tilted
              (fun q => u (α_sh s₀ (π q.1) ⬝ᵥ w + α_aux s₀ (π q.1) ⬝ᵥ q.2))) :=
      funext fun w => by
        simp_rw [← hS_lin s₀ w]
        exact integral_congr_ae (ae_of_all _ fun σ => mul_assoc _ _ _)
    rw [heq_in]
    have hfub := integral_tilted_replica_fubini μ₀ π hπ (α_sh s₀) (α_aux s₀) hum hB hfi
      (fun w σ => S' s₀ w (σ i) *
        ((deriv (ψ i) (S s₀ w (σ i)) + ψ i (S s₀ w (σ i)) * deriv u (S s₀ w (σ i))) *
          ∏ r ∈ Finset.univ.erase i, ψ r (S s₀ w (σ r))))
      (fun st w η => S'_m s₀ w (st i) (η i) *
        (ϕ' i (S_m s₀ w (st i) (η i)) *
          ∏ r ∈ Finset.univ.erase i, ϕ r (S_m s₀ w (st r) (η r))))
      (fun w σ => by
        rw [Real.exp_sum, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
        simp only [hS_lin, hS'_lin, hSm_lin, hS'm_lin]
        have hprod_eq : (∏ r ∈ Finset.univ.erase i, ψ r (S_m s₀ w (π (σ r).1) (σ r).2)) *
            (∏ r ∈ Finset.univ.erase i, Real.exp (u (S_m s₀ w (π (σ r).1) (σ r).2))) =
            ∏ r ∈ Finset.univ.erase i, ϕ r (S_m s₀ w (π (σ r).1) (σ r).2) := by
          rw [← Finset.prod_mul_distrib]
        dsimp only [ϕ']
        rw [← hprod_eq]
        ring)
      (fun st => by
        have hlinS : ∀ r : R, Measurable fun q : (K_sh → ℝ) × (R → K_aux → ℝ) =>
            S_m s₀ q.1 (st r) (q.2 r) := fun r =>
          ((((Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
            (Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp
                ((measurable_pi_apply r).comp measurable_snd)))).const_mul _).add
          ((((Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
            (Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp
                ((measurable_pi_apply r).comp measurable_snd)))).const_mul _)))
        have hlinS' : Measurable fun q : (K_sh → ℝ) × (R → K_aux → ℝ) =>
            S'_m s₀ q.1 (st i) (q.2 i) :=
          ((((Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
            (Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp
                ((measurable_pi_apply i).comp measurable_snd)))).const_mul _).add
          ((((Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
            (Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp
                ((measurable_pi_apply i).comp measurable_snd)))).const_mul _)))
        exact hlinS'.mul (((((measurable_deriv _).add
            ((hψd i).continuous.measurable.mul hdu)).mul
            (Real.measurable_exp.comp hum)).comp (hlinS i)).mul
          (Finset.measurable_prod _ fun r _ =>
            ((hψd r).continuous.measurable.mul (Real.measurable_exp.comp hum)).comp (hlinS r))))
      (bw := fun w : K_sh → ℝ => C_i i * ∑ m : L, ∑ k : K_sh, (|X_sh m k| + |Y_sh m k|) * |w k|)
      ((integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun k _ =>
        (integrable_comp_eval (μ := fun _ : K_sh => gaussianReal 0 1) (i := k)
          (integrable_abs_id_gaussianReal (m := 0) (v := 1))).const_mul _).const_mul _)
      (bη := fun η : R → K_aux → ℝ =>
        C_i i * ∑ m : L, ∑ k : K_aux, (|X_aux m k| + |Y_aux m k|) * |η i k|)
      ((integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun k _ =>
        (integrable_comp_eval (μ := fun _ : R => γ_aux) (i := i)
          (integrable_comp_eval (μ := fun _ : K_aux => gaussianReal 0 1) (i := k)
            (integrable_abs_id_gaussianReal (m := 0) (v := 1)))).const_mul _).const_mul _)
      (fun st w η => by
        rw [abs_mul, abs_mul, Finset.abs_prod]
        have hc2 : |ϕ' i (S_m s₀ w (st i) (η i))| *
            ∏ x ∈ Finset.univ.erase i, |ϕ x (S_m s₀ w (st x) (η x))| ≤ C_i i :=
          mul_le_mul (hϕ'b i _)
            (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hϕb r _)
            (Finset.prod_nonneg fun _ _ => abs_nonneg _) (by positivity)
        have hc1 : |S'_m s₀ w (st i) (η i)| ≤
            (∑ m : L, ∑ k : K_sh, (|X_sh m k| + |Y_sh m k|) * |w k|) +
            (∑ m : L, ∑ k : K_aux, (|X_aux m k| + |Y_aux m k|) * |η i k|) := by
          have h1 : |S'_m s₀ w (st i) (η i)| ≤
              |X_sh (st i) ⬝ᵥ w + X_aux (st i) ⬝ᵥ η i| +
              |Y_sh (st i) ⬝ᵥ w + Y_aux (st i) ⬝ᵥ η i| := by
            calc _ ≤ |-Real.sin s₀ * (X_sh (st i) ⬝ᵥ w + X_aux (st i) ⬝ᵥ η i)| +
                  |Real.cos s₀ * (Y_sh (st i) ⬝ᵥ w + Y_aux (st i) ⬝ᵥ η i)| := abs_add_le _ _
              _ = |Real.sin s₀| * |X_sh (st i) ⬝ᵥ w + X_aux (st i) ⬝ᵥ η i| +
                  |Real.cos s₀| * |Y_sh (st i) ⬝ᵥ w + Y_aux (st i) ⬝ᵥ η i| := by
                  rw [abs_mul, abs_mul, abs_neg]
              _ ≤ 1 * |X_sh (st i) ⬝ᵥ w + X_aux (st i) ⬝ᵥ η i| +
                  1 * |Y_sh (st i) ⬝ᵥ w + Y_aux (st i) ⬝ᵥ η i| :=
                  add_le_add (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _))
                    (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _))
              _ = _ := by ring
          have h2 : |X_sh (st i) ⬝ᵥ w + X_aux (st i) ⬝ᵥ η i| +
              |Y_sh (st i) ⬝ᵥ w + Y_aux (st i) ⬝ᵥ η i| ≤
              (|X_sh (st i) ⬝ᵥ w| + |Y_sh (st i) ⬝ᵥ w|) +
              (|X_aux (st i) ⬝ᵥ η i| + |Y_aux (st i) ⬝ᵥ η i|) := by
            linarith [abs_add_le (X_sh (st i) ⬝ᵥ w) (X_aux (st i) ⬝ᵥ η i),
              abs_add_le (Y_sh (st i) ⬝ᵥ w) (Y_aux (st i) ⬝ᵥ η i)]
          refine (h1.trans h2).trans (add_le_add ?_ ?_)
          · have hx : |X_sh (st i) ⬝ᵥ w| + |Y_sh (st i) ⬝ᵥ w| ≤
                ∑ k : K_sh, (|X_sh (st i) k| + |Y_sh (st i) k|) * |w k| := by
              calc _ ≤ (∑ k, |X_sh (st i) k * w k|) + ∑ k, |Y_sh (st i) k * w k| :=
                    add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
                _ = _ := by simp_rw [← Finset.sum_add_distrib, abs_mul, add_mul]
            exact hx.trans (Finset.single_le_sum
              (f := fun m : L => ∑ k : K_sh, (|X_sh m k| + |Y_sh m k|) * |w k|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ (st i)))
          · have hy : |X_aux (st i) ⬝ᵥ η i| + |Y_aux (st i) ⬝ᵥ η i| ≤
                ∑ k : K_aux, (|X_aux (st i) k| + |Y_aux (st i) k|) * |η i k| := by
              calc _ ≤ (∑ k, |X_aux (st i) k * η i k|) + ∑ k, |Y_aux (st i) k * η i k| :=
                    add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
                _ = _ := by simp_rw [← Finset.sum_add_distrib, abs_mul, add_mul]
            exact hy.trans (Finset.single_le_sum
              (f := fun m : L => ∑ k : K_aux, (|X_aux m k| + |Y_aux m k|) * |η i k|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ (st i)))
        calc _ ≤ (_ + _) * C_i i := mul_le_mul hc1 hc2 (by positivity) (by positivity)
          _ = _ := by ring)
    dsimp only at hfub
    have hI1_eq : ∀ a : R → α,
        (∫ w, (∫ η : R → K_aux → ℝ, S'_m s₀ w (π (a i)) (η i) *
            (ϕ' i (S_m s₀ w (π (a i)) (η i)) *
              ∏ r ∈ Finset.univ.erase i, ϕ r (S_m s₀ w (π (a r)) (η r)))
            ∂(Measure.pi fun _ : R => γ_aux)) /
          (∑ m : L, (μ₀.map π).real {m} *
            ∫ η, Real.exp (u (α_sh s₀ m ⬝ᵥ w + α_aux s₀ m ⬝ᵥ η)) ∂γ_aux) ^
              Fintype.card R ∂γ_sh) =
        (∫ w, (∫ η : R → K_aux → ℝ, S'_m s₀ w (π (a i)) (η i) *
            (ϕ' i (S_m s₀ w (π (a i)) (η i)) *
              ∏ r ∈ Finset.univ.erase i, ϕ r (S_m s₀ w (π (a r)) (η r)))
            ∂(Measure.pi fun _ : R => γ_aux)) / Z s₀ w ^ Fintype.card R ∂γ_sh) :=
      fun a => integral_congr_ae (ae_of_all _ fun w => by dsimp only; rw [hZ_eq_s0 w])
    exact hfub.trans (integral_congr_ae (ae_of_all _ fun a => by dsimp only; rw [hI1_eq a]))
  have hf_opt : Integrable (fun a : Option R → α => f (fun r => a (some r)))
      (Measure.pi fun _ : Option R => μ₀) :=
    (measurePreserving_pi_comp_injective μ₀
      (Option.some_injective R)).integrable_comp_of_integrable hfi
  have hRHS2 :
      ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
          f (fun r => (σ (some r)).1) * S' s₀ w (σ none) *
            (∏ r : R, ψ r (S s₀ w (σ (some r)))) * deriv u (S s₀ w (σ none))
          ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh =
        ∫ a : R → α, f a *
          (∑ m : L, p m *
            ∫ w, ((∫ η : R → K_aux → ℝ, ∏ r, ϕ r (S_m s₀ w (π (a r)) (η r))
                ∂(Measure.pi fun _ : R => γ_aux)) *
              ∫ η₀, S'_m s₀ w m η₀ * deriv u (S_m s₀ w m η₀) *
                Real.exp (u (S_m s₀ w m η₀)) ∂γ_aux) /
              Z s₀ w ^ (Fintype.card R + 1) ∂γ_sh)
          ∂(Measure.pi fun _ : R => μ₀) := by
    have heq_in : (fun w => ∫ σ : Option R → α × (K_aux → ℝ),
          f (fun r => (σ (some r)).1) * S' s₀ w (σ none) *
            (∏ r : R, ψ r (S s₀ w (σ (some r)))) * deriv u (S s₀ w (σ none))
          ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q)))) =
        fun w => ∫ σ : Option R → α × (K_aux → ℝ),
          f (fun r => (σ (some r)).1) *
            (S' s₀ w (σ none) *
              (∏ r : R, ψ r (S s₀ w (σ (some r)))) * deriv u (S s₀ w (σ none)))
          ∂(Measure.pi fun _ : Option R =>
            (μ₀.prod γ_aux).tilted
              (fun q => u (α_sh s₀ (π q.1) ⬝ᵥ w + α_aux s₀ (π q.1) ⬝ᵥ q.2))) :=
      funext fun w => by
        simp_rw [← hS_lin s₀ w]
        exact integral_congr_ae (ae_of_all _ fun σ => by ring)
    rw [heq_in]
    let C_opt : ℝ := C_ϕ * (|D₁| * Real.exp B)
    have hopt_fub := integral_tilted_replica_fubini (ι := Option R) μ₀ π hπ
      (α_sh s₀) (α_aux s₀) hum hB hf_opt
      (fun w σ => S' s₀ w (σ none) *
        (∏ r : R, ψ r (S s₀ w (σ (some r)))) * deriv u (S s₀ w (σ none)))
      (fun st w η => (∏ r : R, ϕ r (S_m s₀ w (st (some r)) (η (some r)))) *
        (S'_m s₀ w (st none) (η none) * deriv u (S_m s₀ w (st none) (η none)) *
          Real.exp (u (S_m s₀ w (st none) (η none)))))
      (fun w σ => by
        rw [Fintype.sum_option, Real.exp_add, Real.exp_sum]
        simp only [hS_lin, hS'_lin, hSm_lin, hS'm_lin]
        have hprod_eq : (∏ r : R, ψ r (S_m s₀ w (π (σ (some r)).1) (σ (some r)).2)) *
            (∏ r : R, Real.exp (u (S_m s₀ w (π (σ (some r)).1) (σ (some r)).2))) =
            ∏ r : R, ϕ r (S_m s₀ w (π (σ (some r)).1) (σ (some r)).2) := by
          rw [← Finset.prod_mul_distrib]
        rw [← hprod_eq]
        ring)
      (fun st => by
        have hlinS : ∀ r : Option R, Measurable fun q : (K_sh → ℝ) × (Option R → K_aux → ℝ) =>
            S_m s₀ q.1 (st r) (q.2 r) := fun r =>
          ((((Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
            (Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp
                ((measurable_pi_apply r).comp measurable_snd)))).const_mul _).add
          ((((Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
            (Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp
                ((measurable_pi_apply r).comp measurable_snd)))).const_mul _)))
        have hlinS' : Measurable fun q : (K_sh → ℝ) × (Option R → K_aux → ℝ) =>
            S'_m s₀ q.1 (st none) (q.2 none) :=
          ((((Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
            (Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp
                ((measurable_pi_apply none).comp measurable_snd)))).const_mul _).add
          ((((Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp measurable_fst)).add
            (Finset.measurable_sum _ fun k _ =>
              measurable_const.mul ((measurable_pi_apply k).comp
                ((measurable_pi_apply none).comp measurable_snd)))).const_mul _)))
        exact (Finset.measurable_prod _ fun r _ =>
          ((hψd r).continuous.measurable.mul (Real.measurable_exp.comp hum)).comp
            (hlinS (some r))).mul
          ((hlinS'.mul (hdu.comp (hlinS none))).mul
            (Real.measurable_exp.comp (hum.comp (hlinS none)))))
      (bw := fun w : K_sh → ℝ => C_opt * ∑ m : L, ∑ k : K_sh, (|X_sh m k| + |Y_sh m k|) * |w k|)
      ((integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun k _ =>
        (integrable_comp_eval (μ := fun _ : K_sh => gaussianReal 0 1) (i := k)
          (integrable_abs_id_gaussianReal (m := 0) (v := 1))).const_mul _).const_mul _)
      (bη := fun η : Option R → K_aux → ℝ =>
        C_opt * ∑ m : L, ∑ k : K_aux, (|X_aux m k| + |Y_aux m k|) * |η none k|)
      ((integrable_finsetSum _ fun m _ => integrable_finsetSum _ fun k _ =>
        (integrable_comp_eval (μ := fun _ : Option R => γ_aux) (i := none)
          (integrable_comp_eval (μ := fun _ : K_aux => gaussianReal 0 1) (i := k)
            (integrable_abs_id_gaussianReal (m := 0) (v := 1)))).const_mul _).const_mul _)
      (fun st w η => by
        rw [abs_mul, mul_assoc (S'_m _ _ _ _), abs_mul, Finset.abs_prod]
        have hc2 : |deriv u (S_m s₀ w (st none) (η none)) *
            Real.exp (u (S_m s₀ w (st none) (η none)))| ≤ |D₁| * Real.exp B :=
          abs_mul_exp_le ((hD₁ _).trans (le_abs_self _)) (le_of_abs_le (hB _))
        have hc3 : |S'_m s₀ w (st none) (η none)| ≤
            (∑ m : L, ∑ k : K_sh, (|X_sh m k| + |Y_sh m k|) * |w k|) +
            (∑ m : L, ∑ k : K_aux, (|X_aux m k| + |Y_aux m k|) * |η none k|) := by
          have h1 : |S'_m s₀ w (st none) (η none)| ≤
              |X_sh (st none) ⬝ᵥ w + X_aux (st none) ⬝ᵥ η none| +
              |Y_sh (st none) ⬝ᵥ w + Y_aux (st none) ⬝ᵥ η none| := by
            calc _ ≤ |-Real.sin s₀ * (X_sh (st none) ⬝ᵥ w + X_aux (st none) ⬝ᵥ η none)| +
                  |Real.cos s₀ * (Y_sh (st none) ⬝ᵥ w + Y_aux (st none) ⬝ᵥ η none)| :=
                  abs_add_le _ _
              _ = |Real.sin s₀| * |X_sh (st none) ⬝ᵥ w + X_aux (st none) ⬝ᵥ η none| +
                  |Real.cos s₀| * |Y_sh (st none) ⬝ᵥ w + Y_aux (st none) ⬝ᵥ η none| := by
                  rw [abs_mul, abs_mul, abs_neg]
              _ ≤ 1 * |X_sh (st none) ⬝ᵥ w + X_aux (st none) ⬝ᵥ η none| +
                  1 * |Y_sh (st none) ⬝ᵥ w + Y_aux (st none) ⬝ᵥ η none| :=
                  add_le_add (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _))
                    (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _))
              _ = _ := by ring
          have h2 : |X_sh (st none) ⬝ᵥ w + X_aux (st none) ⬝ᵥ η none| +
              |Y_sh (st none) ⬝ᵥ w + Y_aux (st none) ⬝ᵥ η none| ≤
              (|X_sh (st none) ⬝ᵥ w| + |Y_sh (st none) ⬝ᵥ w|) +
              (|X_aux (st none) ⬝ᵥ η none| + |Y_aux (st none) ⬝ᵥ η none|) := by
            linarith [abs_add_le (X_sh (st none) ⬝ᵥ w) (X_aux (st none) ⬝ᵥ η none),
              abs_add_le (Y_sh (st none) ⬝ᵥ w) (Y_aux (st none) ⬝ᵥ η none)]
          refine (h1.trans h2).trans (add_le_add ?_ ?_)
          · have hx : |X_sh (st none) ⬝ᵥ w| + |Y_sh (st none) ⬝ᵥ w| ≤
                ∑ k : K_sh, (|X_sh (st none) k| + |Y_sh (st none) k|) * |w k| := by
              calc _ ≤ (∑ k, |X_sh (st none) k * w k|) + ∑ k, |Y_sh (st none) k * w k| :=
                    add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
                _ = _ := by simp_rw [← Finset.sum_add_distrib, abs_mul, add_mul]
            exact hx.trans (Finset.single_le_sum
              (f := fun m : L => ∑ k : K_sh, (|X_sh m k| + |Y_sh m k|) * |w k|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ (st none)))
          · have hy : |X_aux (st none) ⬝ᵥ η none| + |Y_aux (st none) ⬝ᵥ η none| ≤
                ∑ k : K_aux, (|X_aux (st none) k| + |Y_aux (st none) k|) * |η none k| := by
              calc _ ≤ (∑ k, |X_aux (st none) k * η none k|) +
                      ∑ k, |Y_aux (st none) k * η none k| :=
                    add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
                _ = _ := by simp_rw [← Finset.sum_add_distrib, abs_mul, add_mul]
            exact hy.trans (Finset.single_le_sum
              (f := fun m : L => ∑ k : K_aux, (|X_aux m k| + |Y_aux m k|) * |η none k|)
              (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ (st none)))
        have hc1' : ∏ x : R, |ϕ x (S_m s₀ w (st (some x)) (η (some x)))| ≤ C_ϕ :=
          Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun r _ => hϕb r _
        calc _ ≤ C_ϕ * ((_ + _) * (|D₁| * Real.exp B)) :=
              mul_le_mul hc1' (mul_le_mul hc3 hc2 (abs_nonneg _) (by positivity))
                (by positivity) (Finset.prod_nonneg fun _ _ => by positivity)
          _ = _ := by dsimp only [C_opt]; ring)
    dsimp only at hopt_fub
    rw [hopt_fub]
    obtain ⟨I_m, hI_m⟩ : ∃ I_m : (R → L) → L → ℝ, ∀ st m, I_m st m =
        ∫ w, ((∫ η : R → K_aux → ℝ, ∏ r, ϕ r (S_m s₀ w (st r) (η r))
            ∂(Measure.pi fun _ : R => γ_aux)) *
          ∫ η₀, S'_m s₀ w m η₀ * deriv u (S_m s₀ w m η₀) *
            Real.exp (u (S_m s₀ w m η₀)) ∂γ_aux) /
          Z s₀ w ^ (Fintype.card R + 1) ∂γ_sh := ⟨_, fun _ _ => rfl⟩
    have h_eta_split : ∀ (a : Option R → α) (w : K_sh → ℝ),
        ∫ η : Option R → K_aux → ℝ,
          (∏ r : R, ϕ r (S_m s₀ w (π (a (some r))) (η (some r)))) *
            (S'_m s₀ w (π (a none)) (η none) * deriv u (S_m s₀ w (π (a none)) (η none)) *
              Real.exp (u (S_m s₀ w (π (a none)) (η none))))
          ∂(Measure.pi fun _ : Option R => γ_aux) =
        (∫ η : R → K_aux → ℝ, ∏ r, ϕ r (S_m s₀ w (π (a (some r))) (η r))
            ∂(Measure.pi fun _ : R => γ_aux)) *
          ∫ η₀, S'_m s₀ w (π (a none)) η₀ * deriv u (S_m s₀ w (π (a none)) η₀) *
            Real.exp (u (S_m s₀ w (π (a none)) η₀)) ∂γ_aux := by
      intro a w
      have hlin_eta : ∀ m : L, Measurable fun η₀ : K_aux → ℝ => S_m s₀ w m η₀ := fun m =>
        (((measurable_const.add (Finset.measurable_sum _ fun k _ =>
            measurable_const.mul (measurable_pi_apply k))).const_mul _).add
        (((measurable_const.add (Finset.measurable_sum _ fun k _ =>
            measurable_const.mul (measurable_pi_apply k))).const_mul _)))
      have hlin_eta' : ∀ m : L, Measurable fun η₀ : K_aux → ℝ => S'_m s₀ w m η₀ := fun m =>
        (((measurable_const.add (Finset.measurable_sum _ fun k _ =>
            measurable_const.mul (measurable_pi_apply k))).const_mul _).add
        (((measurable_const.add (Finset.measurable_sum _ fun k _ =>
            measurable_const.mul (measurable_pi_apply k))).const_mul _)))
      exact integral_pi_fresh_replica_mul γ_aux (Option.some_injective R)
        (fun r => Option.some_ne_none r)
        (fun η : R → K_aux → ℝ => ∏ r : R, ϕ r (S_m s₀ w (π (a (some r))) (η r)))
        (fun η₀ : K_aux → ℝ => S'_m s₀ w (π (a none)) η₀ *
          deriv u (S_m s₀ w (π (a none)) η₀) * Real.exp (u (S_m s₀ w (π (a none)) η₀)))
        (Finset.measurable_prod _ fun r _ =>
          ((hψd r).continuous.measurable.mul (Real.measurable_exp.comp hum)).comp
            ((hlin_eta (π (a (some r)))).comp (measurable_pi_apply r))).aestronglyMeasurable
        (((hlin_eta' (π (a none))).mul (hdu.comp (hlin_eta (π (a none))))).mul
          (Real.measurable_exp.comp (hum.comp (hlin_eta (π (a none)))))).aestronglyMeasurable
    have h_a_congr : ∫ a : Option R → α,
          f (fun r => a (some r)) *
            ∫ w, (∫ η : Option R → K_aux → ℝ,
                (∏ r : R, ϕ r (S_m s₀ w (π (a (some r))) (η (some r)))) *
                  (S'_m s₀ w (π (a none)) (η none) * deriv u (S_m s₀ w (π (a none)) (η none)) *
                    Real.exp (u (S_m s₀ w (π (a none)) (η none))))
                ∂(Measure.pi fun _ : Option R => γ_aux)) /
              (∑ m : L, (μ₀.map π).real {m} *
                ∫ η, Real.exp (u (α_sh s₀ m ⬝ᵥ w + α_aux s₀ m ⬝ᵥ η)) ∂γ_aux) ^
                  Fintype.card (Option R) ∂γ_sh
          ∂(Measure.pi fun _ : Option R => μ₀) =
        ∫ a : Option R → α,
          ∑ m : L, (f (fun r => a (some r)) * I_m (fun r => π (a (some r))) m) *
            (if π (a none) = m then (1 : ℝ) else 0)
          ∂(Measure.pi fun _ : Option R => μ₀) := by
      refine integral_congr_ae (ae_of_all _ fun a => ?_)
      dsimp only
      have hw_eq : (∫ w, (∫ η : Option R → K_aux → ℝ,
              (∏ r : R, ϕ r (S_m s₀ w (π (a (some r))) (η (some r)))) *
                (S'_m s₀ w (π (a none)) (η none) * deriv u (S_m s₀ w (π (a none)) (η none)) *
                  Real.exp (u (S_m s₀ w (π (a none)) (η none))))
              ∂(Measure.pi fun _ : Option R => γ_aux)) /
            (∑ m : L, (μ₀.map π).real {m} *
              ∫ η, Real.exp (u (α_sh s₀ m ⬝ᵥ w + α_aux s₀ m ⬝ᵥ η)) ∂γ_aux) ^
                Fintype.card (Option R) ∂γ_sh) =
          I_m (fun r => π (a (some r))) (π (a none)) := by
        rw [hI_m]
        exact integral_congr_ae (ae_of_all _ fun w => by
          dsimp only
          rw [h_eta_split a w, hZ_eq_s0 w, Fintype.card_option])
      rw [hw_eq]
      simp
    rw [h_a_congr]
    have hπ_opt : Measurable fun a : Option R → α => (fun r : R => π (a (some r))) :=
      measurable_pi_iff.2 fun r => hπ.comp (measurable_pi_apply (some r))
    have h_term_int : ∀ m : L, Integrable (fun a : Option R → α =>
        (f (fun r => a (some r)) * I_m (fun r => π (a (some r))) m) *
          (if π (a none) = m then (1 : ℝ) else 0)) (Measure.pi fun _ : Option R => μ₀) := by
      intro m
      let B_Im : ℝ := ∑ st : R → L, |I_m st m|
      refine (hf_opt.abs.mul_const B_Im).mono' ?_ (ae_of_all _ fun a => ?_)
      · refine (hf_opt.aestronglyMeasurable.mul
          ((measurable_of_finite fun st => I_m st m).comp hπ_opt).aestronglyMeasurable).mul
          ((measurable_of_finite fun m' : L => if m' = m then (1 : ℝ) else 0).comp
            (hπ.comp (measurable_pi_apply none))).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have h1 : |if π (a none) = m then (1 : ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
        have h2 : |I_m (fun r => π (a (some r))) m| ≤ B_Im :=
          Finset.single_le_sum (f := fun st => |I_m st m|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ _)
        calc |f (fun r => a (some r))| * |I_m (fun r => π (a (some r))) m| *
                |if π (a none) = m then (1 : ℝ) else 0|
            ≤ |f (fun r => a (some r))| * B_Im * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) h1
                (abs_nonneg _) (mul_nonneg (abs_nonneg _) ((abs_nonneg _).trans h2))
          _ = |f (fun r => a (some r))| * B_Im := mul_one _
    rw [integral_finsetSum _ fun m _ => h_term_int m]
    have hπ_r : Measurable fun a : R → α => (fun r : R => π (a r)) :=
      measurable_pi_iff.2 fun r => hπ.comp (measurable_pi_apply r)
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
          ((measurable_of_finite fun st => I_m st m).comp hπ_r).aestronglyMeasurable)
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
        (Measure.pi fun _ : R => μ₀) := fun m =>
      (hfi.bdd_mul_of_abs_le
        ((measurable_of_finite fun st : R → L => p m * I_m st m).comp hπ_r).aestronglyMeasurable
        (ae_of_all _ fun a => Finset.single_le_sum (f := fun st => |p m * I_m st m|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ _))).congr
        (ae_of_all _ fun a => mul_comm _ _)
    rw [← integral_finsetSum _ fun m _ => h_a_int m]
    exact integral_congr_ae (ae_of_all _ fun a => by
      dsimp only
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun m _ => by rw [hI_m])
  obtain ⟨g₁, hg₁⟩ : ∃ g₁ : R → (R → L) → ℝ, ∀ i st, g₁ i st =
      ∫ w, (∫ η : R → K_aux → ℝ, S'_m s₀ w (st i) (η i) *
          (ϕ' i (S_m s₀ w (st i) (η i)) *
            ∏ r ∈ Finset.univ.erase i, ϕ r (S_m s₀ w (st r) (η r)))
          ∂(Measure.pi fun _ : R => γ_aux)) / Z s₀ w ^ Fintype.card R ∂γ_sh :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨g₂, hg₂⟩ : ∃ g₂ : (R → L) → ℝ, ∀ st, g₂ st =
      ∑ m : L, p m *
        ∫ w, ((∫ η : R → K_aux → ℝ, ∏ r, ϕ r (S_m s₀ w (st r) (η r))
            ∂(Measure.pi fun _ : R => γ_aux)) *
          ∫ η₀, S'_m s₀ w m η₀ * deriv u (S_m s₀ w m η₀) *
            Real.exp (u (S_m s₀ w m η₀)) ∂γ_aux) /
          Z s₀ w ^ (Fintype.card R + 1) ∂γ_sh :=
    ⟨_, fun _ => rfl⟩
  have hR1_fold : ∀ i : R,
      ∫ w, ∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) * S' s₀ w (σ i) *
            ((deriv (ψ i) (S s₀ w (σ i)) + ψ i (S s₀ w (σ i)) * deriv u (S s₀ w (σ i))) *
              ∏ r ∈ Finset.univ.erase i, ψ r (S s₀ w (σ r)))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh =
        ∫ a : R → α, f a * g₁ i (fun r => π (a r)) ∂(Measure.pi fun _ : R => μ₀) :=
    fun i => (hRHS1 i).trans (integral_congr_ae (ae_of_all _ fun a => by dsimp only; rw [hg₁]))
  have hR2_fold :
      ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
          f (fun r => (σ (some r)).1) * S' s₀ w (σ none) *
            (∏ r : R, ψ r (S s₀ w (σ (some r)))) * deriv u (S s₀ w (σ none))
          ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh =
        ∫ a : R → α, f a * g₂ (fun r => π (a r)) ∂(Measure.pi fun _ : R => μ₀) :=
    hRHS2.trans (integral_congr_ae (ae_of_all _ fun a => by dsimp only; rw [hg₂]))
  rw [Finset.sum_congr rfl fun i _ => hR1_fold i, hR2_fold]
  have hπ_r : Measurable fun a : R → α => (fun r : R => π (a r)) :=
    measurable_pi_iff.2 fun r => hπ.comp (measurable_pi_apply r)
  have h_bdd_int : ∀ g : (R → L) → ℝ, Integrable (fun a : R → α => f a * g (fun r => π (a r)))
      (Measure.pi fun _ : R => μ₀) := fun g =>
    (hfi.bdd_mul_of_abs_le ((measurable_of_finite g).comp hπ_r).aestronglyMeasurable
      (ae_of_all _ fun a => Finset.single_le_sum (f := fun st => |g st|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ _))).congr
      (ae_of_all _ fun a => mul_comm _ _)
  rw [← integral_finsetSum _ fun i _ => h_bdd_int (g₁ i), ← integral_const_mul,
    ← integral_sub (integrable_finsetSum _ fun i _ => h_bdd_int (g₁ i))
      ((h_bdd_int g₂).const_mul _)]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  dsimp only
  rw [hI'_st, ← Finset.mul_sum, mul_left_comm (Fintype.card R : ℝ) (f a), ← mul_sub]
  congr 1
  simp_rw [hg₁, hg₂]

/-- **Full rotation derivative and Gaussian integration by parts at fixed old-state probability
measure `μ₀`.** Under orthogonality `X_sh m ⬝ᵥ Y_sh m' = 0`, `X_aux m ⬝ᵥ Y_aux m' = 0` and equal
total variance `X_sh m ⬝ᵥ X_sh m + X_aux m ⬝ᵥ X_aux m = Y_sh m ⬝ᵥ Y_sh m + Y_aux m ⬝ᵥ Y_aux m`,
the same-replica covariance vanishes identically, and the angle derivative of
`s ↦ ∫ w, ⟨f(σ.1) * ∏_r ψ_r(S_s(w, σ_r))⟩_{u(S_s)} ∂γ_sh` at `s₀` expands into the four-group
off-diagonal covariance formula over `R`, `Option R` and `Option (Option R)` with prefactor
`sin s₀ * cos s₀`. Neither `deriv (deriv u)` nor `deriv (deriv (ψ r))` needs to be continuous. -/
theorem hasDerivAt_integral_gaussian_tilted_rotation_ibp
    {α L K_sh K_aux R : Type*} [MeasurableSpace α]
    [Finite L] [MeasurableSpace L] [MeasurableSingletonClass L]
    [Fintype K_sh] [Fintype K_aux] [Fintype R] [DecidableEq R]
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (π : α → L) (hπ : Measurable π)
    (X_sh Y_sh : L → K_sh → ℝ) (X_aux Y_aux : L → K_aux → ℝ)
    (horth_sh : ∀ m m', X_sh m ⬝ᵥ Y_sh m' = 0)
    (horth_aux : ∀ m m', X_aux m ⬝ᵥ Y_aux m' = 0)
    (hvar : ∀ m, X_sh m ⬝ᵥ X_sh m + X_aux m ⬝ᵥ X_aux m =
      Y_sh m ⬝ᵥ Y_sh m + Y_aux m ⬝ᵥ Y_aux m)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) (hu₂ : Differentiable ℝ (deriv u))
    {B D₁ D₂ : ℝ} (hB : ∀ x, |u x| ≤ B) (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (hD₂ : ∀ x, |deriv (deriv u) x| ≤ D₂)
    (ψ : R → ℝ → ℝ) (hψd : ∀ r, Differentiable ℝ (ψ r))
    (hψ₂d : ∀ r, Differentiable ℝ (deriv (ψ r)))
    {M₀ M₁ M₂ : R → ℝ} (hM₀ : ∀ r x, |ψ r x| ≤ M₀ r)
    (hM₁ : ∀ r x, |deriv (ψ r) x| ≤ M₁ r)
    (hM₂ : ∀ r x, |deriv (deriv (ψ r)) x| ≤ M₂ r)
    {f : (R → α) → ℝ} (hfi : Integrable f (Measure.pi fun _ : R => μ₀))
    (s₀ : ℝ) :
    let γ_sh := Measure.pi fun _ : K_sh => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : K_aux => gaussianReal 0 1
    let S (s : ℝ) (w : K_sh → ℝ) (q : α × (K_aux → ℝ)) : ℝ :=
      Real.cos s * (X_sh (π q.1) ⬝ᵥ w + X_aux (π q.1) ⬝ᵥ q.2) +
        Real.sin s * (Y_sh (π q.1) ⬝ᵥ w + Y_aux (π q.1) ⬝ᵥ q.2)
    let C_cov (m m' : L) : ℝ := Y_sh m ⬝ᵥ Y_sh m' - X_sh m ⬝ᵥ X_sh m'
    let ψ_d (r : R) (x : ℝ) : ℝ := deriv (ψ r) x + ψ r x * deriv u x
    HasDerivAt
      (fun s => ∫ w, ∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) * ∏ r, ψ r (S s w (σ r))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S s w q))) ∂γ_sh)
      (Real.sin s₀ * Real.cos s₀ * (
        (∑ i : R, ∑ j ∈ Finset.univ.erase i,
          ∫ w, ∫ σ : R → α × (K_aux → ℝ),
            f (fun r => (σ r).1) * C_cov (π (σ i).1) (π (σ j).1) *
              (ψ_d i (S s₀ w (σ i)) * ψ_d j (S s₀ w (σ j)) *
                ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S s₀ w (σ r)))
            ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh) -
        (Fintype.card R : ℝ) * ∑ i : R,
          ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
            f (fun r => (σ (some r)).1) * C_cov (π (σ (some i)).1) (π (σ none).1) *
              (ψ_d i (S s₀ w (σ (some i))) *
                ∏ r ∈ Finset.univ.erase i, ψ r (S s₀ w (σ (some r)))) *
              deriv u (S s₀ w (σ none))
            ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh -
        (Fintype.card R : ℝ) * ∑ j : R,
          ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
            f (fun r => (σ (some r)).1) * C_cov (π (σ none).1) (π (σ (some j)).1) *
              (ψ_d j (S s₀ w (σ (some j))) *
                ∏ r ∈ Finset.univ.erase j, ψ r (S s₀ w (σ (some r)))) *
              deriv u (S s₀ w (σ none))
            ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh +
        (Fintype.card R : ℝ) * ((Fintype.card R : ℝ) + 1) *
          ∫ w, ∫ σ : Option (Option R) → α × (K_aux → ℝ),
            f (fun r => (σ (some (some r))).1) * C_cov (π (σ (some none)).1) (π (σ none).1) *
              (∏ r : R, ψ r (S s₀ w (σ (some (some r))))) *
              deriv u (S s₀ w (σ (some none))) * deriv u (S s₀ w (σ none))
            ∂(Measure.pi fun _ : Option (Option R) =>
              (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh))
      s₀ := by
  classical
  have := Fintype.ofFinite L
  intro γ_sh γ_aux S C_cov ψ_d
  have hrot := hasDerivAt_integral_gaussian_tilted_rotation μ₀ π hπ X_sh Y_sh X_aux Y_aux
    hu hB hD₁ ψ hψd hM₀ hM₁ hfi s₀
  refine hrot.congr_deriv ?_
  let α_sh : L → K_sh → ℝ := fun m k => Real.cos s₀ * X_sh m k + Real.sin s₀ * Y_sh m k
  let W_sh : L → K_sh → ℝ := fun m k => -Real.sin s₀ * X_sh m k + Real.cos s₀ * Y_sh m k
  let α_aux : L → K_aux → ℝ := fun m k => Real.cos s₀ * X_aux m k + Real.sin s₀ * Y_aux m k
  let W_aux : L → K_aux → ℝ := fun m k => -Real.sin s₀ * X_aux m k + Real.cos s₀ * Y_aux m k
  have hS_eq : ∀ w (q : α × (K_aux → ℝ)),
      S s₀ w q = α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2 := fun w q => by
    dsimp only [S, α_sh, α_aux, dotProduct]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  have hS'_eq : ∀ w (q : α × (K_aux → ℝ)),
      -Real.sin s₀ * (X_sh (π q.1) ⬝ᵥ w + X_aux (π q.1) ⬝ᵥ q.2) +
        Real.cos s₀ * (Y_sh (π q.1) ⬝ᵥ w + Y_aux (π q.1) ⬝ᵥ q.2) =
      W_sh (π q.1) ⬝ᵥ w + W_aux (π q.1) ⬝ᵥ q.2 := fun w q => by
    dsimp only [W_sh, W_aux, dotProduct]
    simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    ring
  have hdot_sh : ∀ m m' : L, W_sh m ⬝ᵥ α_sh m' = Real.sin s₀ * Real.cos s₀ * C_cov m m' := by
    intro m m'
    have hxy := horth_sh m m'
    have hyx : Y_sh m ⬝ᵥ X_sh m' = 0 := by rw [dotProduct_comm, horth_sh m' m]
    have hexp : W_sh m ⬝ᵥ α_sh m' =
        (-Real.sin s₀ * Real.cos s₀) * (X_sh m ⬝ᵥ X_sh m') +
        (-Real.sin s₀ * Real.sin s₀) * (X_sh m ⬝ᵥ Y_sh m') +
        (Real.cos s₀ * Real.cos s₀) * (Y_sh m ⬝ᵥ X_sh m') +
        (Real.cos s₀ * Real.sin s₀) * (Y_sh m ⬝ᵥ Y_sh m') := by
      simp only [W_sh, α_sh, dotProduct, Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hexp, hxy, hyx]
    dsimp only [C_cov]
    ring
  have hdot_same : ∀ m : L, W_sh m ⬝ᵥ α_sh m + W_aux m ⬝ᵥ α_aux m = 0 := by
    intro m
    have hxy_a := horth_aux m m
    have hyx_a : Y_aux m ⬝ᵥ X_aux m = 0 := by rw [dotProduct_comm, hxy_a]
    have hexp_a : W_aux m ⬝ᵥ α_aux m =
        (-Real.sin s₀ * Real.cos s₀) * (X_aux m ⬝ᵥ X_aux m) +
        (-Real.sin s₀ * Real.sin s₀) * (X_aux m ⬝ᵥ Y_aux m) +
        (Real.cos s₀ * Real.cos s₀) * (Y_aux m ⬝ᵥ X_aux m) +
        (Real.cos s₀ * Real.sin s₀) * (Y_aux m ⬝ᵥ Y_aux m) := by
      simp only [W_aux, α_aux, dotProduct, Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hdot_sh m m, hexp_a, hxy_a, hyx_a]
    dsimp only [C_cov]
    linear_combination (-Real.sin s₀ * Real.cos s₀) * hvar m
  let ψ_dd : R → ℝ → ℝ := fun r x =>
    deriv (deriv (ψ r)) x + 2 * deriv (ψ r) x * deriv u x +
      ψ r x * deriv (deriv u) x + ψ r x * deriv u x ^ 2
  have hψ_d_b0 : ∀ r x, |ψ_d r x| ≤ |M₁ r| + |M₀ r| * |D₁| := fun r x => by
    refine (abs_add_le _ _).trans (add_le_add ((hM₁ r x).trans (le_abs_self _)) ?_)
    rw [abs_mul]
    exact mul_le_mul ((hM₀ r x).trans (le_abs_self _)) ((hD₁ x).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  have hψ_exp_d : ∀ r x, HasDerivAt (fun x => ψ r x * Real.exp (u x))
      (ψ_d r x * Real.exp (u x)) x := fun r x =>
    (((hψd r x).hasDerivAt).mul ((hu x).hasDerivAt.exp)).congr_deriv (by dsimp only [ψ_d]; ring)
  have hψ_d_exp_d : ∀ r x, HasDerivAt (fun x => ψ_d r x * Real.exp (u x))
      (ψ_dd r x * Real.exp (u x)) x := fun r x => by
    have hd1 : HasDerivAt (ψ_d r)
        (deriv (deriv (ψ r)) x + (deriv (ψ r) x * deriv u x + ψ r x * deriv (deriv u) x)) x :=
      (hψ₂d r x).hasDerivAt.add (((hψd r x).hasDerivAt).mul (hu₂ x).hasDerivAt)
    exact (hd1.mul ((hu x).hasDerivAt.exp)).congr_deriv (by dsimp only [ψ_d, ψ_dd]; ring)
  have hψ_dd_b : ∀ r x, |ψ_dd r x| ≤
      |M₂ r| + 2 * |M₁ r| * |D₁| + |M₀ r| * |D₂| + |M₀ r| * |D₁| ^ 2 := fun r x => by
    dsimp only [ψ_dd]
    have h1 := (hM₂ r x).trans (le_abs_self _)
    have h2 : |2 * deriv (ψ r) x * deriv u x| ≤ 2 * |M₁ r| * |D₁| := by
      rw [abs_mul, abs_mul, abs_two, mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul ((hM₁ r x).trans (le_abs_self _)) ((hD₁ x).trans (le_abs_self _))
          (abs_nonneg _) (abs_nonneg _)) zero_le_two
    have h3 : |ψ r x * deriv (deriv u) x| ≤ |M₀ r| * |D₂| := by
      rw [abs_mul]
      exact mul_le_mul ((hM₀ r x).trans (le_abs_self _)) ((hD₂ x).trans (le_abs_self _))
        (abs_nonneg _) (abs_nonneg _)
    have h4 : |ψ r x * deriv u x ^ 2| ≤ |M₀ r| * |D₁| ^ 2 := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul ((hM₀ r x).trans (le_abs_self _))
        (pow_le_pow_left₀ (abs_nonneg _) ((hD₁ x).trans (le_abs_self _)) 2)
        (by positivity) (abs_nonneg _)
    linarith [abs_add_le (deriv (deriv (ψ r)) x + 2 * deriv (ψ r) x * deriv u x +
        ψ r x * deriv (deriv u) x) (ψ r x * deriv u x ^ 2),
      abs_add_le (deriv (deriv (ψ r)) x + 2 * deriv (ψ r) x * deriv u x)
        (ψ r x * deriv (deriv u) x),
      abs_add_le (deriv (deriv (ψ r)) x) (2 * deriv (ψ r) x * deriv u x)]
  have h_term1 : ∀ i : R,
      ∫ w, ∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) *
            (-Real.sin s₀ * (X_sh (π (σ i).1) ⬝ᵥ w + X_aux (π (σ i).1) ⬝ᵥ (σ i).2) +
              Real.cos s₀ * (Y_sh (π (σ i).1) ⬝ᵥ w + Y_aux (π (σ i).1) ⬝ᵥ (σ i).2)) *
            (ψ_d i (S s₀ w (σ i)) * ∏ r ∈ Finset.univ.erase i, ψ r (S s₀ w (σ r)))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh =
        Real.sin s₀ * Real.cos s₀ * (
          (∑ j ∈ Finset.univ.erase i,
            ∫ w, ∫ σ : R → α × (K_aux → ℝ),
              f (fun r => (σ r).1) * C_cov (π (σ i).1) (π (σ j).1) *
                (ψ_d i (S s₀ w (σ i)) * ψ_d j (S s₀ w (σ j)) *
                  ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S s₀ w (σ r)))
              ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh) -
          (Fintype.card R : ℝ) *
            ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
              f (fun r => (σ (some r)).1) * C_cov (π (σ (some i)).1) (π (σ none).1) *
                (ψ_d i (S s₀ w (σ (some i))) *
                  ∏ r ∈ Finset.univ.erase i, ψ r (S s₀ w (σ (some r)))) *
                deriv u (S s₀ w (σ none))
              ∂(Measure.pi fun _ : Option R =>
                (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh) := by
    intro i
    let ψ_i : R → ℝ → ℝ := fun r => if r = i then ψ_d i else ψ r
    let ψ_i' : R → ℝ → ℝ := fun r => if r = i then ψ_dd i else ψ_d r
    have hstein_i := stein_tilted_replica_ratio μ₀ π hπ α_sh W_sh α_aux W_aux hu hB hD₁
      ψ_i
      (fun r x => by
        dsimp only [ψ_i]
        split_ifs with h
        · exact (hψ_d_exp_d i x).differentiableAt
        · exact (hψ_exp_d r x).differentiableAt)
      (M₀ := fun r => if r = i then |M₁ i| + |M₀ i| * |D₁| else M₀ r)
      (fun r x => by
        dsimp only [ψ_i]
        split_ifs with h
        · exact hψ_d_b0 i x
        · exact hM₀ r x)
      (M' := fun r => (if r = i then
          |M₂ i| + 2 * |M₁ i| * |D₁| + |M₀ i| * |D₂| + |M₀ i| * |D₁| ^ 2
        else |M₁ r| + |M₀ r| * |D₁|) * Real.exp B)
      (fun r x => by
        dsimp only [ψ_i]
        split_ifs with h
        · rw [(hψ_d_exp_d i x).deriv]
          exact abs_mul_exp_le (hψ_dd_b i x) (le_of_abs_le (hB x))
        · rw [(hψ_exp_d r x).deriv]
          exact abs_mul_exp_le (hψ_d_b0 r x) (le_of_abs_le (hB x)))
      ψ_i'
      (fun r x => by
        dsimp only [ψ_i, ψ_i']
        split_ifs with h
        · exact (hψ_d_exp_d i x).deriv
        · exact (hψ_exp_d r x).deriv)
      i hfi
    dsimp only at hstein_i
    have hprod_ψi : ∀ (w : K_sh → ℝ) (τ : R → α × (K_aux → ℝ)),
        ∏ r : R, ψ_i r (α_sh (π (τ r).1) ⬝ᵥ w + α_aux (π (τ r).1) ⬝ᵥ (τ r).2) =
        ψ_d i (S s₀ w (τ i)) * ∏ r ∈ Finset.univ.erase i, ψ r (S s₀ w (τ r)) := by
      intro w τ
      simp_rw [← hS_eq w]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
      simp only [ψ_i, ↓reduceIte]
      congr 1
      exact Finset.prod_congr rfl fun r hr => by simp [Finset.ne_of_mem_erase hr]
    have hlhs_eq : ∫ w, ∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) *
            (-Real.sin s₀ * (X_sh (π (σ i).1) ⬝ᵥ w + X_aux (π (σ i).1) ⬝ᵥ (σ i).2) +
              Real.cos s₀ * (Y_sh (π (σ i).1) ⬝ᵥ w + Y_aux (π (σ i).1) ⬝ᵥ (σ i).2)) *
            (ψ_d i (S s₀ w (σ i)) * ∏ r ∈ Finset.univ.erase i, ψ r (S s₀ w (σ r)))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh =
        ∫ w, ∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) *
            (W_sh (π (σ i).1) ⬝ᵥ w + W_aux (π (σ i).1) ⬝ᵥ (σ i).2) *
            ∏ r, ψ_i r (α_sh (π (σ r).1) ⬝ᵥ w + α_aux (π (σ r).1) ⬝ᵥ (σ r).2)
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted
            (fun q => u (α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2))) ∂γ_sh := by
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      dsimp only
      simp_rw [← hS_eq w, hS'_eq w]
      exact integral_congr_ae (ae_of_all _ fun σ => by
        dsimp only
        rw [← hprod_ψi w σ]
        simp_rw [← hS_eq w])
    rw [hlhs_eq, hstein_i, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    have hdiag_zero : ∫ w, ∫ σ : R → α × (K_aux → ℝ),
        f (fun r => (σ r).1) *
          (W_sh (π (σ i).1) ⬝ᵥ α_sh (π (σ i).1) +
            if i = i then W_aux (π (σ i).1) ⬝ᵥ α_aux (π (σ i).1) else 0) *
          (ψ_i' i (α_sh (π (σ i).1) ⬝ᵥ w + α_aux (π (σ i).1) ⬝ᵥ (σ i).2) *
            ∏ r ∈ Finset.univ.erase i,
              ψ_i r (α_sh (π (σ r).1) ⬝ᵥ w + α_aux (π (σ r).1) ⬝ᵥ (σ r).2))
        ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted
          (fun q => u (α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2))) ∂γ_sh = 0 := by
      simp only [↓reduceIte, hdot_same, mul_zero, zero_mul, integral_zero]
    rw [hdiag_zero, zero_add]
    have hoff_eq : ∀ j ∈ Finset.univ.erase i,
        ∫ w, ∫ σ : R → α × (K_aux → ℝ),
          f (fun r => (σ r).1) *
            (W_sh (π (σ i).1) ⬝ᵥ α_sh (π (σ j).1) +
              if i = j then W_aux (π (σ i).1) ⬝ᵥ α_aux (π (σ j).1) else 0) *
            (ψ_i' j (α_sh (π (σ j).1) ⬝ᵥ w + α_aux (π (σ j).1) ⬝ᵥ (σ j).2) *
              ∏ r ∈ Finset.univ.erase j,
                ψ_i r (α_sh (π (σ r).1) ⬝ᵥ w + α_aux (π (σ r).1) ⬝ᵥ (σ r).2))
          ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted
            (fun q => u (α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2))) ∂γ_sh =
        Real.sin s₀ * Real.cos s₀ *
          ∫ w, ∫ σ : R → α × (K_aux → ℝ),
            f (fun r => (σ r).1) * C_cov (π (σ i).1) (π (σ j).1) *
              (ψ_d i (S s₀ w (σ i)) * ψ_d j (S s₀ w (σ j)) *
                ∏ r ∈ (Finset.univ.erase i).erase j, ψ r (S s₀ w (σ r)))
            ∂(Measure.pi fun _ : R => (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh := by
      intro j hj
      have hji : j ≠ i := Finset.ne_of_mem_erase hj
      have hij : i ≠ j := hji.symm
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      dsimp only
      rw [← integral_const_mul]
      simp_rw [← hS_eq w]
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      dsimp only
      simp only [hij, ↓reduceIte, add_zero, hdot_sh]
      have hij_mem : i ∈ Finset.univ.erase j := Finset.mem_erase.2 ⟨hij, Finset.mem_univ i⟩
      rw [← Finset.mul_prod_erase (Finset.univ.erase j) _ hij_mem, Finset.erase_right_comm]
      simp only [ψ_i, ψ_i', hji, ↓reduceIte]
      have hp_rest : ∏ x ∈ (Finset.univ.erase i).erase j,
          (if x = i then ψ_d i else ψ x) (S s₀ w (σ x)) =
          ∏ x ∈ (Finset.univ.erase i).erase j, ψ x (S s₀ w (σ x)) :=
        Finset.prod_congr rfl fun x hx => by
          have hxi : x ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hx)
          simp [hxi]
      rw [hp_rest]
      ring
    have hfresh_eq :
        ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
          f (fun r => (σ (some r)).1) *
            (W_sh (π (σ (some i)).1) ⬝ᵥ α_sh (π (σ none).1)) *
            (∏ r : R, ψ_i r
              (α_sh (π (σ (some r)).1) ⬝ᵥ w + α_aux (π (σ (some r)).1) ⬝ᵥ (σ (some r)).2)) *
            deriv u (α_sh (π (σ none).1) ⬝ᵥ w + α_aux (π (σ none).1) ⬝ᵥ (σ none).2)
          ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted
            (fun q => u (α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2))) ∂γ_sh =
        Real.sin s₀ * Real.cos s₀ *
          ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
            f (fun r => (σ (some r)).1) * C_cov (π (σ (some i)).1) (π (σ none).1) *
              (ψ_d i (S s₀ w (σ (some i))) *
                ∏ r ∈ Finset.univ.erase i, ψ r (S s₀ w (σ (some r)))) *
              deriv u (S s₀ w (σ none))
            ∂(Measure.pi fun _ : Option R =>
              (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      dsimp only
      have hmeas_eq : (Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted
          (fun q => u (α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2))) =
          Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q)) := by
        simp_rw [← hS_eq w]
      rw [hmeas_eq, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      dsimp only
      rw [hdot_sh, hprod_ψi w (fun r => σ (some r)), ← hS_eq w (σ none)]
      ring
    rw [Finset.sum_congr rfl hoff_eq, hfresh_eq, ← Finset.mul_sum]
    ring
  have hf_opt : Integrable (fun a : Option R → α => f (fun r => a (some r)))
      (Measure.pi fun _ : Option R => μ₀) :=
    (measurePreserving_pi_comp_injective μ₀
      (Option.some_injective R)).integrable_comp_of_integrable hfi
  have hdu_exp_d : ∀ x, HasDerivAt (fun x => deriv u x * Real.exp (u x))
      ((deriv (deriv u) x + deriv u x ^ 2) * Real.exp (u x)) x := fun x =>
    ((hu₂ x).hasDerivAt.mul ((hu x).hasDerivAt.exp)).congr_deriv (by ring)
  have h_term2 :
      ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
          f (fun r => (σ (some r)).1) *
            (-Real.sin s₀ * (X_sh (π (σ none).1) ⬝ᵥ w + X_aux (π (σ none).1) ⬝ᵥ (σ none).2) +
              Real.cos s₀ * (Y_sh (π (σ none).1) ⬝ᵥ w + Y_aux (π (σ none).1) ⬝ᵥ (σ none).2)) *
            (∏ r : R, ψ r (S s₀ w (σ (some r)))) * deriv u (S s₀ w (σ none))
          ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh =
        Real.sin s₀ * Real.cos s₀ * (
          (∑ j : R,
            ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
              f (fun r => (σ (some r)).1) * C_cov (π (σ none).1) (π (σ (some j)).1) *
                (ψ_d j (S s₀ w (σ (some j))) *
                  ∏ r ∈ Finset.univ.erase j, ψ r (S s₀ w (σ (some r)))) *
                deriv u (S s₀ w (σ none))
              ∂(Measure.pi fun _ : Option R =>
                (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh) -
          ((Fintype.card R : ℝ) + 1) *
            ∫ w, ∫ σ : Option (Option R) → α × (K_aux → ℝ),
              f (fun r => (σ (some (some r))).1) * C_cov (π (σ (some none)).1) (π (σ none).1) *
                (∏ r : R, ψ r (S s₀ w (σ (some (some r))))) *
                deriv u (S s₀ w (σ (some none))) * deriv u (S s₀ w (σ none))
              ∂(Measure.pi fun _ : Option (Option R) =>
                (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh) := by
    let ψ_opt : Option R → ℝ → ℝ := fun o => Option.casesOn o (deriv u) ψ
    let ψ_opt' : Option R → ℝ → ℝ := fun o =>
      Option.casesOn o (fun x => deriv (deriv u) x + deriv u x ^ 2) ψ_d
    have hstein_opt := stein_tilted_replica_ratio (R := Option R) μ₀ π hπ
      α_sh W_sh α_aux W_aux hu hB hD₁
      ψ_opt
      (fun o x => by cases o with
        | none => exact (hdu_exp_d x).differentiableAt
        | some r => exact (hψ_exp_d r x).differentiableAt)
      (M₀ := fun o => Option.casesOn o D₁ M₀)
      (fun o x => by cases o with
        | none => exact hD₁ x
        | some r => exact hM₀ r x)
      (M' := fun o => Option.casesOn o ((|D₂| + |D₁| ^ 2) * Real.exp B)
        (fun r => (|M₁ r| + |M₀ r| * |D₁|) * Real.exp B))
      (fun o x => by cases o with
        | none =>
          dsimp only [ψ_opt]
          rw [(hdu_exp_d x).deriv]
          refine abs_mul_exp_le ((abs_add_le _ _).trans (add_le_add
            ((hD₂ x).trans (le_abs_self _)) ?_)) (le_of_abs_le (hB x))
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) ((hD₁ x).trans (le_abs_self _)) 2
        | some r =>
          dsimp only [ψ_opt]
          rw [(hψ_exp_d r x).deriv]
          exact abs_mul_exp_le (hψ_d_b0 r x) (le_of_abs_le (hB x)))
      ψ_opt'
      (fun o x => by cases o with
        | none => exact (hdu_exp_d x).deriv
        | some r => exact (hψ_exp_d r x).deriv)
      none hf_opt
    dsimp only at hstein_opt
    have hprod_opt : ∀ (w : K_sh → ℝ) (τ : Option R → α × (K_aux → ℝ)),
        ∏ o : Option R, ψ_opt o (α_sh (π (τ o).1) ⬝ᵥ w + α_aux (π (τ o).1) ⬝ᵥ (τ o).2) =
        (∏ r : R, ψ r (S s₀ w (τ (some r)))) * deriv u (S s₀ w (τ none)) := by
      intro w τ
      simp_rw [← hS_eq w]
      rw [Fintype.prod_option]
      dsimp only [ψ_opt]
      ring
    have hlhs_opt : ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
          f (fun r => (σ (some r)).1) *
            (-Real.sin s₀ * (X_sh (π (σ none).1) ⬝ᵥ w + X_aux (π (σ none).1) ⬝ᵥ (σ none).2) +
              Real.cos s₀ * (Y_sh (π (σ none).1) ⬝ᵥ w + Y_aux (π (σ none).1) ⬝ᵥ (σ none).2)) *
            (∏ r : R, ψ r (S s₀ w (σ (some r)))) * deriv u (S s₀ w (σ none))
          ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh =
        ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
          f (fun r => (σ (some r)).1) *
            (W_sh (π (σ none).1) ⬝ᵥ w + W_aux (π (σ none).1) ⬝ᵥ (σ none).2) *
            ∏ o : Option R, ψ_opt o (α_sh (π (σ o).1) ⬝ᵥ w + α_aux (π (σ o).1) ⬝ᵥ (σ o).2)
          ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted
            (fun q => u (α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2))) ∂γ_sh := by
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      dsimp only
      have hmeas_eq : (Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted
          (fun q => u (S s₀ w q))) =
          Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted
            (fun q => u (α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2)) := by
        simp_rw [← hS_eq w]
      rw [hmeas_eq]
      exact integral_congr_ae (ae_of_all _ fun σ => by
        dsimp only
        rw [hS'_eq w (σ none), hprod_opt w σ]
        ring)
    rw [hlhs_opt, hstein_opt, Fintype.sum_option]
    have hnone_zero : ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
        f (fun r => (σ (some r)).1) *
          (W_sh (π (σ none).1) ⬝ᵥ α_sh (π (σ none).1) +
            if (none : Option R) = none then W_aux (π (σ none).1) ⬝ᵥ α_aux (π (σ none).1) else 0) *
          (ψ_opt' none (α_sh (π (σ none).1) ⬝ᵥ w + α_aux (π (σ none).1) ⬝ᵥ (σ none).2) *
            ∏ o ∈ Finset.univ.erase none,
              ψ_opt o (α_sh (π (σ o).1) ⬝ᵥ w + α_aux (π (σ o).1) ⬝ᵥ (σ o).2))
        ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted
          (fun q => u (α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2))) ∂γ_sh = 0 := by
      simp only [↓reduceIte, hdot_same, mul_zero, zero_mul, integral_zero]
    rw [hnone_zero, zero_add]
    have hsome_eq : ∀ j : R,
        ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
          f (fun r => (σ (some r)).1) *
            (W_sh (π (σ none).1) ⬝ᵥ α_sh (π (σ (some j)).1) +
              if (none : Option R) = some j then
                W_aux (π (σ none).1) ⬝ᵥ α_aux (π (σ (some j)).1)
              else 0) *
            (ψ_opt' (some j)
                (α_sh (π (σ (some j)).1) ⬝ᵥ w + α_aux (π (σ (some j)).1) ⬝ᵥ (σ (some j)).2) *
              ∏ o ∈ Finset.univ.erase (some j),
                ψ_opt o (α_sh (π (σ o).1) ⬝ᵥ w + α_aux (π (σ o).1) ⬝ᵥ (σ o).2))
          ∂(Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted
            (fun q => u (α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2))) ∂γ_sh =
        Real.sin s₀ * Real.cos s₀ *
          ∫ w, ∫ σ : Option R → α × (K_aux → ℝ),
            f (fun r => (σ (some r)).1) * C_cov (π (σ none).1) (π (σ (some j)).1) *
              (ψ_d j (S s₀ w (σ (some j))) *
                ∏ r ∈ Finset.univ.erase j, ψ r (S s₀ w (σ (some r)))) *
              deriv u (S s₀ w (σ none))
            ∂(Measure.pi fun _ : Option R =>
              (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh := by
      intro j
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      dsimp only
      have hmeas_eq : (Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted
          (fun q => u (α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2))) =
          Measure.pi fun _ : Option R => (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q)) := by
        simp_rw [← hS_eq w]
      rw [hmeas_eq, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      dsimp only
      simp_rw [← hS_eq w]
      simp only [reduceCtorEq, ↓reduceIte, add_zero, hdot_sh]
      have hnone_mem : (none : Option R) ∈ Finset.univ.erase (some j) :=
        Finset.mem_erase.2 ⟨(Option.some_ne_none j).symm, Finset.mem_univ _⟩
      rw [← Finset.mul_prod_erase (Finset.univ.erase (some j)) _ hnone_mem]
      have herase_opt : ((Finset.univ.erase (some j)).erase none : Finset (Option R)) =
          (Finset.univ.erase j).map ⟨Option.some, Option.some_injective R⟩ := by
        ext o
        cases o with
        | none => simp
        | some r => simp [and_comm]
      rw [herase_opt, Finset.prod_map]
      dsimp only [ψ_opt, ψ_opt', Function.Embedding.coeFn_mk]
      ring
    have hfresh_opt :
        ∫ w, ∫ σ : Option (Option R) → α × (K_aux → ℝ),
          f (fun r => (σ (some (some r))).1) *
            (W_sh (π (σ (some none)).1) ⬝ᵥ α_sh (π (σ none).1)) *
            (∏ o : Option R, ψ_opt o
              (α_sh (π (σ (some o)).1) ⬝ᵥ w + α_aux (π (σ (some o)).1) ⬝ᵥ (σ (some o)).2)) *
            deriv u (α_sh (π (σ none).1) ⬝ᵥ w + α_aux (π (σ none).1) ⬝ᵥ (σ none).2)
          ∂(Measure.pi fun _ : Option (Option R) => (μ₀.prod γ_aux).tilted
            (fun q => u (α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2))) ∂γ_sh =
        Real.sin s₀ * Real.cos s₀ *
          ∫ w, ∫ σ : Option (Option R) → α × (K_aux → ℝ),
            f (fun r => (σ (some (some r))).1) * C_cov (π (σ (some none)).1) (π (σ none).1) *
              (∏ r : R, ψ r (S s₀ w (σ (some (some r))))) *
              deriv u (S s₀ w (σ (some none))) * deriv u (S s₀ w (σ none))
            ∂(Measure.pi fun _ : Option (Option R) =>
              (μ₀.prod γ_aux).tilted (fun q => u (S s₀ w q))) ∂γ_sh := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun w => ?_)
      dsimp only
      have hmeas_eq : (Measure.pi fun _ : Option (Option R) => (μ₀.prod γ_aux).tilted
          (fun q => u (α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2))) =
          Measure.pi fun _ : Option (Option R) => (μ₀.prod γ_aux).tilted
            (fun q => u (S s₀ w q)) := by
        simp_rw [← hS_eq w]
      rw [hmeas_eq, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun σ => ?_)
      dsimp only
      rw [hdot_sh, hprod_opt w (fun o => σ (some o)), ← hS_eq w (σ none)]
      ring
    rw [Finset.sum_congr rfl fun j _ => hsome_eq j, hfresh_opt, Fintype.card_option,
      ← Finset.mul_sum]
    push_cast
    ring
  dsimp only at h_term1 h_term2 ⊢
  rw [Finset.sum_congr rfl fun i _ => h_term1 i, h_term2]
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

end SpinGlasses
