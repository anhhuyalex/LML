/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianSteinRatio
public import LeanMachineLearning.SpinGlasses.Gaussian.GaussianTiltedSteinRatio
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ReplicaSymmetricFreeEnergy
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.OverlapHighMoments
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.EmpiricalVarianceHighMoments
public import LeanMachineLearning.ForMathlib.Algebra.BigOperators.Binomial
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.SqSub
public import LeanMachineLearning.ForMathlib.Probability.Moments.IidSumMoments
public import LeanMachineLearning.Optimization.NTK.Foundations.ODE

/-!
# Centered-moment ODE and Grönwall bounds along the `s`-interpolation (Talagrand Section 2.5)

Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 2.5, proof of Theorem
2.5.3, Eqs. (2.107)--(2.110).

For `N + 1` spins and `M` constraints with load `α = M / (N + 1)`, let
$$A(s, \omega) = \frac{1}{N + 1}\,\log \int_{\Sigma_{N+1} \times \mathbb{R}^M}
  \exp\bigl(E_s(s, \omega, x)\bigr)\,\mathrm{d}\mu_s(x),$$
$$\mathrm{RS}(s) = \mathrm{perceptronRSFunctional}(u, \alpha, r, q) +
  \frac{1 - s}{2}\,r(1 - q), \qquad V(s, \omega) = A(s, \omega) - \mathrm{RS}(s).$$

## Main declarations

* `SpinGlasses.stein_tilted_unit_replica_deriv_mul_comp_log`: model-free single-replica Stein
  identity multiplied by `G(log Z_w(w))` with zero diagonal covariance.
* `SpinGlasses.hasDerivAt_interpolating_centered_moment_pow`: Eq. (2.108), differentiating
  `ψ(s) = 𝔼[V(s)^k]` on `s ∈ (0, 1)` into `VII + VIII + IX`.
* `SpinGlasses.abs_interpolating_term_VII_le`, `SpinGlasses.abs_interpolating_term_VIII_le`:
  Hölder bounds (2.109) from Theorems 2.5.1 and 2.5.2.
* `SpinGlasses.integral_interpolating_centered_abs_pow_le`: a priori Grönwall bound
  `𝔼[|V(s)|^k] ≤ C * ((√(N + 1))⁻¹)^k` uniformly in `s ∈ [0, 1]` for all `k : ℕ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology

namespace SpinGlasses

/-! ### Section 1: Log-weighted single-replica Stein identity -/

private lemma exp_le_sum_mul_integral_exp {L K : Type*} [Fintype L] [Fintype K]
    (p : L → ℝ) (hp : ∀ m, 0 ≤ p m) (hp1 : ∑ m, p m = 1) {B : ℝ}
    (G : L → (K → ℝ) → ℝ) (hB : ∀ m η, |G m η| ≤ B)
    (hint : ∀ m, Integrable (fun η => Real.exp (G m η))
      (Measure.pi fun _ : K => gaussianReal 0 1)) :
    (∑ m, p m * ∫ η, Real.exp (G m η) ∂(Measure.pi fun _ : K => gaussianReal 0 1)) ≤
      Real.exp B := by
  have hup : ∀ m, ∫ η, Real.exp (G m η) ∂(Measure.pi fun _ : K => gaussianReal 0 1) ≤ Real.exp B :=
    fun m => by
      have hm := integral_mono (hint m) (integrable_const (Real.exp B))
        fun η => Real.exp_le_exp.2 (le_of_abs_le (hB m η))
      simpa using hm
  calc (∑ m, p m * ∫ η, Real.exp (G m η) ∂(Measure.pi fun _ : K => gaussianReal 0 1))
      ≤ ∑ m, p m * Real.exp B := Finset.sum_le_sum fun m _ =>
          mul_le_mul_of_nonneg_left (hup m) (hp m)
    _ = (∑ m, p m) * Real.exp B := (Finset.sum_mul _ _ _).symm
    _ = Real.exp B := by rw [hp1, one_mul]

private lemma hasFDerivAt_Z_sum_bounds {L K_aux : Type*} [Fintype L] [DecidableEq L] [Fintype K_aux]
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
    have hlow : ∀ m, Real.exp (-B) ≤ ∫ η, Real.exp (u (y m + c m ⬝ᵥ η)) ∂γ_aux := fun m => by
      have hm := integral_mono (integrable_const (Real.exp (-B))) (hexpi m (y m))
        fun η => Real.exp_le_exp.2 (neg_le_of_abs_le (hB _))
      simpa using hm
    calc Real.exp (-B) = (∑ m, p m) * Real.exp (-B) := by rw [hp1, one_mul]
      _ = ∑ m, p m * Real.exp (-B) := Finset.sum_mul _ _ _
      _ ≤ _ := Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hlow m) (hp m)
  · intro y
    exact exp_le_sum_mul_integral_exp p hp hp1 (fun m η => u (y m + c m ⬝ᵥ η))
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

/-- **Single-replica Stein identity multiplied by `G(log Z(w))` at fixed spin label.** -/
private theorem stein_ratio_comp_log_fixed_spin
    {L K_sh K_aux : Type*} [Fintype L] [Fintype K_sh] [Fintype K_aux]
    (p : L → ℝ) (hp : ∀ m, 0 ≤ p m) (hp1 : ∑ m, p m = 1)
    (α_sh W_sh : L → K_sh → ℝ) (α_aux W_aux : L → K_aux → ℝ)
    {u : ℝ → ℝ} (hu : Differentiable ℝ u) {B D₁ : ℝ} (hB : ∀ x, |u x| ≤ B)
    (hD₁ : ∀ x, |deriv u x| ≤ D₁)
    (ϕ : ℝ → ℝ) (hϕ : Differentiable ℝ ϕ) {M M' : ℝ}
    (hM : ∀ x, |ϕ x| ≤ M) (hM' : ∀ x, |deriv ϕ x| ≤ M')
    {G : ℝ → ℝ} (hG : Differentiable ℝ G) {CG CG' : ℝ}
    (hGb : ∀ t ∈ Set.Icc (-B) B, |G t| ≤ CG)
    (hGd : ∀ t ∈ Set.Icc (-B) B, |deriv G t| ≤ CG')
    (s₀ : L) :
    let γ_sh := Measure.pi fun _ : K_sh => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : K_aux => gaussianReal 0 1
    let Z (w : K_sh → ℝ) : ℝ :=
      ∑ m : L, p m * ∫ η, Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η)) ∂γ_aux
    ∫ w, ((∫ η : K_aux → ℝ,
        (W_sh s₀ ⬝ᵥ w + W_aux s₀ ⬝ᵥ η) * ϕ (α_sh s₀ ⬝ᵥ w + α_aux s₀ ⬝ᵥ η) ∂γ_aux) / Z w) *
        G (Real.log (Z w)) ∂γ_sh =
      (W_sh s₀ ⬝ᵥ α_sh s₀ + W_aux s₀ ⬝ᵥ α_aux s₀) *
        ∫ w, ((∫ η : K_aux → ℝ, deriv ϕ (α_sh s₀ ⬝ᵥ w + α_aux s₀ ⬝ᵥ η) ∂γ_aux) / Z w) *
          G (Real.log (Z w)) ∂γ_sh +
      ∑ m : L, p m * (W_sh s₀ ⬝ᵥ α_sh m) *
        ∫ w, (((∫ η : K_aux → ℝ, ϕ (α_sh s₀ ⬝ᵥ w + α_aux s₀ ⬝ᵥ η) ∂γ_aux) *
            ∫ η₀ : K_aux → ℝ,
              deriv u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) *
                Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀)) ∂γ_aux) / Z w ^ 2) *
          (deriv G (Real.log (Z w)) - G (Real.log (Z w))) ∂γ_sh := by
  classical
  intro γ_sh γ_aux Z
  let K_tot := K_sh ⊕ K_aux
  let γ_tot := Measure.pi fun _ : K_tot => gaussianReal 0 1
  let e_tot : (K_tot → ℝ) ≃ᵐ (K_sh → ℝ) × (K_aux → ℝ) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : K_tot => ℝ)
  have he_fst : ∀ ξ, (e_tot ξ).1 = fun k => ξ (Sum.inl k) := fun _ => rfl
  have he_snd : ∀ ξ k, (e_tot ξ).2 k = ξ (Sum.inr k) := fun _ _ => rfl
  have hmp_tot : MeasurePreserving ⇑e_tot γ_tot (γ_sh.prod γ_aux) :=
    measurePreserving_sumPiEquivProdPi (fun _ : K_tot => gaussianReal 0 1)
  let cW : Unit → K_tot → ℝ := fun _ => Sum.elim (W_sh s₀) (W_aux s₀)
  let cX : Unit → K_tot → ℝ := fun _ => Sum.elim (α_sh s₀) (α_aux s₀)
  let cY : L → K_tot → ℝ := fun m => Sum.elim (α_sh m) 0
  let cAll : Unit ⊕ (Unit ⊕ L) → K_tot → ℝ := Sum.elim cW (Sum.elim cX cY)
  have hgauss : HasGaussianLaw (fun (ξ : K_tot → ℝ) idx =>
      Sum.elim (fun k (ξ : K_tot → ℝ) => cW k ⬝ᵥ ξ)
        (Sum.elim (fun r (ξ : K_tot → ℝ) => cX r ⬝ᵥ ξ)
          (fun m (ξ : K_tot → ℝ) => cY m ⬝ᵥ ξ)) idx ξ)
      γ_tot := by
    convert hasGaussianLaw_dotProduct_family cAll using 1
    ext ξ idx
    rcases idx with k | (r | m) <;> rfl
  let F_u : (Unit → ℝ) → ℝ := fun x => ϕ (x ())
  have hFu_d : Differentiable ℝ F_u := fun x =>
    (hϕ (x ())).comp x (differentiableAt_pi.1 differentiableAt_id ())
  have hFu_der : ∀ x : Unit → ℝ, fderiv ℝ F_u x (Pi.single () 1) = deriv ϕ (x ()) := fun x => by
    have hd : HasFDerivAt F_u
        (deriv ϕ (x ()) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Unit => ℝ) ()) x :=
      (hϕ (x ())).hasDerivAt.comp_hasFDerivAt x
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Unit => ℝ) ()).hasFDerivAt
    rw [hd.fderiv]
    simp
  have hFu_b : ∀ x : Unit → ℝ, |F_u x| ≤ |M| := fun x => (hM (x ())).trans (le_abs_self _)
  have hFu_db : ∀ (l : Unit) (x : Unit → ℝ), |fderiv ℝ F_u x (Pi.single l 1)| ≤ |M'| := by
    intro l x
    have hl : l = () := Subsingleton.elim _ _
    rw [hl, hFu_der]
    exact (hM' _).trans (le_abs_self _)
  obtain ⟨hZd, hZb, hZu, hZder, hZdb⟩ := hasFDerivAt_Z_sum_bounds hu hB hD₁ p hp hp1 α_aux
  have hGb' : ∀ t ∈ Set.Icc (Real.log (Real.exp (-B))) (Real.log (Real.exp B)), |G t| ≤ CG := by
    simpa only [Real.log_exp] using hGb
  have hGd' : ∀ t ∈ Set.Icc (Real.log (Real.exp (-B))) (Real.log (Real.exp B)),
      |deriv G t| ≤ CG' := by
    simpa only [Real.log_exp] using hGd
  have hstein := integral_mul_div_mul_comp_log_eq_sum (P := γ_tot)
    (W := fun k ξ => cW k ⬝ᵥ ξ) (X := fun r ξ => cX r ⬝ᵥ ξ) (Y := fun m ξ => cY m ⬝ᵥ ξ)
    hgauss
    (fun k => integral_dotProduct_pi_gaussianReal _)
    (fun r => integral_dotProduct_pi_gaussianReal _)
    (fun m => integral_dotProduct_pi_gaussianReal _)
    ()
    hFu_d hFu_b hFu_db
    hZd (Real.exp_pos (-B)) hZb hZu hZdb
    hG hGb' hGd'
  have hcovX : ∫ ξ, cW () ⬝ᵥ ξ * (cX () ⬝ᵥ ξ) ∂γ_tot =
      W_sh s₀ ⬝ᵥ α_sh s₀ + W_aux s₀ ⬝ᵥ α_aux s₀ := by
    rw [integral_dotProduct_mul_dotProduct_pi_gaussianReal]
    change (∑ x : K_sh ⊕ K_aux, cW () x * cX () x) = _
    rw [Fintype.sum_sum_type]
    simp [cW, cX, dotProduct]
  have hcovY : ∀ m : L, ∫ ξ, cW () ⬝ᵥ ξ * (cY m ⬝ᵥ ξ) ∂γ_tot = W_sh s₀ ⬝ᵥ α_sh m := by
    intro m
    rw [integral_dotProduct_mul_dotProduct_pi_gaussianReal]
    change (∑ x : K_sh ⊕ K_aux, cW () x * cY m x) = _
    rw [Fintype.sum_sum_type]
    simp [cW, cY, dotProduct]
  have hW_e : ∀ ξ, cW () ⬝ᵥ ξ = W_sh s₀ ⬝ᵥ (e_tot ξ).1 + W_aux s₀ ⬝ᵥ (e_tot ξ).2 := by
    intro ξ
    change (∑ x : K_sh ⊕ K_aux, cW () x * ξ x) = _
    rw [Fintype.sum_sum_type, he_fst]
    simp [cW, dotProduct, he_snd]
  have hX_e : ∀ ξ, cX () ⬝ᵥ ξ = α_sh s₀ ⬝ᵥ (e_tot ξ).1 + α_aux s₀ ⬝ᵥ (e_tot ξ).2 := by
    intro ξ
    change (∑ x : K_sh ⊕ K_aux, cX () x * ξ x) = _
    rw [Fintype.sum_sum_type, he_fst]
    simp [cX, dotProduct, he_snd]
  have hY_e : ∀ (m : L) ξ, cY m ⬝ᵥ ξ = α_sh m ⬝ᵥ (e_tot ξ).1 := by
    intro m ξ
    change (∑ x : K_sh ⊕ K_aux, cY m x * ξ x) = _
    rw [Fintype.sum_sum_type, he_fst]
    simp [cY, dotProduct]
  have h_push : ∀ (H : (K_sh → ℝ) × (K_aux → ℝ) → ℝ),
      Measurable H → Integrable (fun ξ => H (e_tot ξ)) γ_tot →
      ∫ ξ, H (e_tot ξ) ∂γ_tot = ∫ w, ∫ η, H (w, η) ∂γ_aux ∂γ_sh := by
    intro H hHm hHi
    have hHi' : Integrable H (γ_sh.prod γ_aux) := by
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
  obtain ⟨lhsFun, hlhsFun⟩ : ∃ lhsFun : (K_sh → ℝ) × (K_aux → ℝ) → ℝ, ∀ q, lhsFun q =
      (W_sh s₀ ⬝ᵥ q.1 + W_aux s₀ ⬝ᵥ q.2) *
        ((ϕ (α_sh s₀ ⬝ᵥ q.1 + α_aux s₀ ⬝ᵥ q.2) / Z q.1) * G (Real.log (Z q.1))) :=
    ⟨_, fun _ => rfl⟩
  have hlhs_m : Measurable lhsFun := by
    rw [show lhsFun = _ from funext hlhsFun]
    have h1 : Measurable fun q : (K_sh → ℝ) × (K_aux → ℝ) =>
        W_sh s₀ ⬝ᵥ q.1 + W_aux s₀ ⬝ᵥ q.2 := by simp only [dotProduct]; fun_prop
    have h2 : Measurable fun q : (K_sh → ℝ) × (K_aux → ℝ) =>
        ϕ (α_sh s₀ ⬝ᵥ q.1 + α_aux s₀ ⬝ᵥ q.2) :=
      hϕ.continuous.measurable.comp (by simp only [dotProduct]; fun_prop)
    have hZ1 : Measurable fun q : (K_sh → ℝ) × (K_aux → ℝ) => Z q.1 := hZm.comp measurable_fst
    exact h1.mul ((h2.div hZ1).mul (hG.continuous.measurable.comp (Real.measurable_log.comp hZ1)))
  have hlhs_eq : ∀ ξ, cW () ⬝ᵥ ξ *
      ((F_u (fun _ => cX () ⬝ᵥ ξ) /
        (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux)) *
      G (Real.log (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux))) =
      lhsFun (e_tot ξ) := fun ξ => by
    rw [hlhsFun, hW_e, hZ_tot]; dsimp only [F_u]; rw [hX_e]
  have hlhs_i : Integrable (fun ξ => lhsFun (e_tot ξ)) γ_tot := by
    have hw_int : Integrable (fun ξ : K_tot → ℝ => cW () ⬝ᵥ ξ) γ_tot :=
      ((hasGaussianLaw_dotProduct_family cW).eval ()).integrable
    have hrm : Measurable fun ξ : K_tot → ℝ =>
        (ϕ (cX () ⬝ᵥ ξ) / Z (e_tot ξ).1) * G (Real.log (Z (e_tot ξ).1)) := by
      have h1 : Measurable fun ξ : K_tot → ℝ => ϕ (cX () ⬝ᵥ ξ) :=
        hϕ.continuous.measurable.comp
          (Finset.measurable_sum _ fun x _ => measurable_const.mul (measurable_pi_apply x))
      have h2 : Measurable fun ξ : K_tot → ℝ => Z (e_tot ξ).1 :=
        hZm.comp (measurable_fst.comp e_tot.measurable)
      exact (h1.div h2).mul (hG.continuous.measurable.comp (Real.measurable_log.comp h2))
    have hrb : ∀ ξ : K_tot → ℝ,
        |(ϕ (cX () ⬝ᵥ ξ) / Z (e_tot ξ).1) * G (Real.log (Z (e_tot ξ).1))| ≤
          (|M| / Real.exp (-B)) * CG := fun ξ => by
      rw [abs_mul, abs_div, abs_of_pos (hZ_pos _)]
      exact mul_le_mul
        (div_le_div₀ (abs_nonneg M) ((hM _).trans (le_abs_self _)) (Real.exp_pos _)
          (hZb (fun m => α_sh m ⬝ᵥ (e_tot ξ).1)))
        (hGb _ (hZ_mem _)) (abs_nonneg _) (by positivity)
    have := hw_int.bdd_mul_of_abs_le hrm.aestronglyMeasurable (ae_of_all _ hrb)
    exact this.congr (ae_of_all _ fun ξ => by
      dsimp only
      rw [mul_comm, hlhsFun, hX_e, hW_e])
  have hLHS : ∫ ξ, cW () ⬝ᵥ ξ *
      ((F_u (fun _ => cX () ⬝ᵥ ξ) /
        (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux)) *
      G (Real.log (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux))) ∂γ_tot =
    ∫ w, ((∫ η : K_aux → ℝ,
        (W_sh s₀ ⬝ᵥ w + W_aux s₀ ⬝ᵥ η) * ϕ (α_sh s₀ ⬝ᵥ w + α_aux s₀ ⬝ᵥ η) ∂γ_aux) / Z w) *
      G (Real.log (Z w)) ∂γ_sh := by
    simp_rw [hlhs_eq]
    rw [h_push lhsFun hlhs_m hlhs_i]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    dsimp only
    have hpt : ∀ η, lhsFun (w, η) =
        ((W_sh s₀ ⬝ᵥ w + W_aux s₀ ⬝ᵥ η) * ϕ (α_sh s₀ ⬝ᵥ w + α_aux s₀ ⬝ᵥ η) / Z w) *
          G (Real.log (Z w)) := fun η => by rw [hlhsFun]; ring
    simp_rw [hpt]
    rw [integral_mul_const, integral_div]
  obtain ⟨rhs1Fun, hrhs1Fun⟩ : ∃ rhs1Fun : (K_sh → ℝ) × (K_aux → ℝ) → ℝ, ∀ q, rhs1Fun q =
      (deriv ϕ (α_sh s₀ ⬝ᵥ q.1 + α_aux s₀ ⬝ᵥ q.2) / Z q.1) * G (Real.log (Z q.1)) :=
    ⟨_, fun _ => rfl⟩
  have hr1_m : Measurable rhs1Fun := by
    rw [show rhs1Fun = _ from funext hrhs1Fun]
    have h1 : Measurable fun q : (K_sh → ℝ) × (K_aux → ℝ) =>
        deriv ϕ (α_sh s₀ ⬝ᵥ q.1 + α_aux s₀ ⬝ᵥ q.2) :=
      (measurable_deriv _).comp (by simp only [dotProduct]; fun_prop)
    have hZ1 : Measurable fun q : (K_sh → ℝ) × (K_aux → ℝ) => Z q.1 := hZm.comp measurable_fst
    exact (h1.div hZ1).mul (hG.continuous.measurable.comp (Real.measurable_log.comp hZ1))
  have hr1_eq : ∀ ξ,
      (fderiv ℝ F_u (fun _ => cX () ⬝ᵥ ξ) (Pi.single () 1) /
        (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux)) *
      G (Real.log (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux)) =
      rhs1Fun (e_tot ξ) := fun ξ => by
    rw [hFu_der, hrhs1Fun, hX_e, hZ_tot]
  have hr1_i : Integrable (fun ξ => rhs1Fun (e_tot ξ)) γ_tot := by
    refine Integrable.of_bound (C := (|M'| / Real.exp (-B)) * CG)
      (hr1_m.comp e_tot.measurable).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
    rw [Real.norm_eq_abs, hrhs1Fun, abs_mul, abs_div, abs_of_pos (hZ_pos _)]
    exact mul_le_mul
      (div_le_div₀ (abs_nonneg M') ((hM' _).trans (le_abs_self _)) (Real.exp_pos _)
        (hZb (fun m => α_sh m ⬝ᵥ (e_tot ξ).1)))
      (hGb _ (hZ_mem _)) (abs_nonneg _) (by positivity)
  have hRHS1 : ∫ ξ,
      (fderiv ℝ F_u (fun _ => cX () ⬝ᵥ ξ) (Pi.single () 1) /
        (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux)) *
      G (Real.log (∑ m : L, p m * ∫ η, Real.exp (u (cY m ⬝ᵥ ξ + α_aux m ⬝ᵥ η)) ∂γ_aux)) ∂γ_tot =
    ∫ w, ((∫ η : K_aux → ℝ, deriv ϕ (α_sh s₀ ⬝ᵥ w + α_aux s₀ ⬝ᵥ η) ∂γ_aux) / Z w) *
      G (Real.log (Z w)) ∂γ_sh := by
    simp_rw [hr1_eq]
    rw [h_push rhs1Fun hr1_m hr1_i]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp_rw [hrhs1Fun]
    rw [integral_mul_const, integral_div]
  have hRHS2 : ∀ m : L, ∫ ξ,
      (F_u (fun _ => cX () ⬝ᵥ ξ) *
        (fderiv ℝ (fun y => ∑ m' : L, p m' * ∫ η, Real.exp (u (y m' + α_aux m' ⬝ᵥ η)) ∂γ_aux)
          (fun k => cY k ⬝ᵥ ξ)) (Pi.single m 1) /
        (∑ m' : L, p m' * ∫ η, Real.exp (u (cY m' ⬝ᵥ ξ + α_aux m' ⬝ᵥ η)) ∂γ_aux) ^ 2) *
      (deriv G (Real.log (∑ m' : L, p m' * ∫ η,
          Real.exp (u (cY m' ⬝ᵥ ξ + α_aux m' ⬝ᵥ η)) ∂γ_aux)) -
        G (Real.log (∑ m' : L, p m' * ∫ η,
          Real.exp (u (cY m' ⬝ᵥ ξ + α_aux m' ⬝ᵥ η)) ∂γ_aux)))
      ∂γ_tot =
    p m * ∫ w, (((∫ η : K_aux → ℝ, ϕ (α_sh s₀ ⬝ᵥ w + α_aux s₀ ⬝ᵥ η) ∂γ_aux) *
        ∫ η₀ : K_aux → ℝ,
          deriv u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) *
            Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀)) ∂γ_aux) / Z w ^ 2) *
      (deriv G (Real.log (Z w)) - G (Real.log (Z w))) ∂γ_sh := by
    intro m
    obtain ⟨rhs2Fun, hrhs2Fun⟩ : ∃ rhs2Fun : (K_sh → ℝ) × (K_aux → ℝ) → ℝ, ∀ q, rhs2Fun q =
        p m * (((ϕ (α_sh s₀ ⬝ᵥ q.1 + α_aux s₀ ⬝ᵥ q.2) *
          (∫ η₀ : K_aux → ℝ,
            deriv u (α_sh m ⬝ᵥ q.1 + α_aux m ⬝ᵥ η₀) *
              Real.exp (u (α_sh m ⬝ᵥ q.1 + α_aux m ⬝ᵥ η₀)) ∂γ_aux)) / Z q.1 ^ 2) *
        (deriv G (Real.log (Z q.1)) - G (Real.log (Z q.1)))) := ⟨_, fun _ => rfl⟩
    have hr2_m : Measurable rhs2Fun := by
      rw [show rhs2Fun = _ from funext hrhs2Fun]
      have h1 : Measurable fun q : (K_sh → ℝ) × (K_aux → ℝ) =>
          ϕ (α_sh s₀ ⬝ᵥ q.1 + α_aux s₀ ⬝ᵥ q.2) :=
        hϕ.continuous.measurable.comp (by simp only [dotProduct]; fun_prop)
      have h2 : Measurable fun q : (K_sh → ℝ) × (K_aux → ℝ) =>
          ∫ η₀ : K_aux → ℝ,
            deriv u (α_sh m ⬝ᵥ q.1 + α_aux m ⬝ᵥ η₀) *
              Real.exp (u (α_sh m ⬝ᵥ q.1 + α_aux m ⬝ᵥ η₀)) ∂γ_aux := by
        have hj : Measurable fun p' : ((K_sh → ℝ) × (K_aux → ℝ)) × (K_aux → ℝ) =>
            deriv u (α_sh m ⬝ᵥ p'.1.1 + α_aux m ⬝ᵥ p'.2) *
              Real.exp (u (α_sh m ⬝ᵥ p'.1.1 + α_aux m ⬝ᵥ p'.2)) := by
          have hl : Measurable fun p' : ((K_sh → ℝ) × (K_aux → ℝ)) × (K_aux → ℝ) =>
              α_sh m ⬝ᵥ p'.1.1 + α_aux m ⬝ᵥ p'.2 := by simp only [dotProduct]; fun_prop
          exact ((measurable_deriv u).comp hl).mul
            (Real.measurable_exp.comp (hu.continuous.measurable.comp hl))
        exact (hj.stronglyMeasurable.integral_prod_right' (ν := γ_aux)).measurable
      have hZ1 : Measurable fun q : (K_sh → ℝ) × (K_aux → ℝ) => Z q.1 := hZm.comp measurable_fst
      have hGsub : Measurable fun q : (K_sh → ℝ) × (K_aux → ℝ) =>
          deriv G (Real.log (Z q.1)) - G (Real.log (Z q.1)) :=
        ((measurable_deriv G).comp (Real.measurable_log.comp hZ1)).sub
          (hG.continuous.measurable.comp (Real.measurable_log.comp hZ1))
      exact (((h1.mul h2).div (hZ1.pow_const 2)).mul hGsub).const_mul (p m)
    have hr2_eq : ∀ ξ,
        (F_u (fun _ => cX () ⬝ᵥ ξ) *
          (fderiv ℝ (fun y => ∑ m' : L, p m' * ∫ η, Real.exp (u (y m' + α_aux m' ⬝ᵥ η)) ∂γ_aux)
            (fun k => cY k ⬝ᵥ ξ)) (Pi.single m 1) /
          (∑ m' : L, p m' * ∫ η, Real.exp (u (cY m' ⬝ᵥ ξ + α_aux m' ⬝ᵥ η)) ∂γ_aux) ^ 2) *
        (deriv G (Real.log (∑ m' : L, p m' * ∫ η,
            Real.exp (u (cY m' ⬝ᵥ ξ + α_aux m' ⬝ᵥ η)) ∂γ_aux)) -
          G (Real.log (∑ m' : L, p m' * ∫ η,
            Real.exp (u (cY m' ⬝ᵥ ξ + α_aux m' ⬝ᵥ η)) ∂γ_aux))) =
        rhs2Fun (e_tot ξ) := fun ξ => by
      rw [hZder, hrhs2Fun, hZ_tot]
      dsimp only [F_u]
      rw [hX_e, hY_e]
      ring
    have hr2_i : Integrable (fun ξ => rhs2Fun (e_tot ξ)) γ_tot := by
      refine Integrable.of_bound
        (C := p m * ((|M| * (|D₁| * Real.exp B) / Real.exp (-B) ^ 2) * (CG + CG')))
        (hr2_m.comp e_tot.measurable).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
      rw [Real.norm_eq_abs, hrhs2Fun, abs_mul, abs_of_nonneg (hp m), abs_mul, abs_div,
        abs_of_pos (sq_pos_of_pos (hZ_pos _)), abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (hp m)
      have hb_int : |∫ η₀ : K_aux → ℝ,
          deriv u (α_sh m ⬝ᵥ (e_tot ξ).1 + α_aux m ⬝ᵥ η₀) *
            Real.exp (u (α_sh m ⬝ᵥ (e_tot ξ).1 + α_aux m ⬝ᵥ η₀)) ∂γ_aux| ≤
          |D₁| * Real.exp B := by
        have hb := norm_integral_le_of_norm_le_const (μ := γ_aux)
          (f := fun η₀ => deriv u (α_sh m ⬝ᵥ (e_tot ξ).1 + α_aux m ⬝ᵥ η₀) *
            Real.exp (u (α_sh m ⬝ᵥ (e_tot ξ).1 + α_aux m ⬝ᵥ η₀)))
          (C := |D₁| * Real.exp B) (ae_of_all _ fun η₀ => by
            rw [Real.norm_eq_abs]
            exact abs_mul_exp_le ((hD₁ _).trans (le_abs_self _)) (le_of_abs_le (hB _)))
        simpa [γ_aux] using hb
      have hfrac : |ϕ (α_sh s₀ ⬝ᵥ (e_tot ξ).1 + α_aux s₀ ⬝ᵥ (e_tot ξ).2)| *
          |∫ η₀, deriv u (α_sh m ⬝ᵥ (e_tot ξ).1 + α_aux m ⬝ᵥ η₀) *
            Real.exp (u (α_sh m ⬝ᵥ (e_tot ξ).1 + α_aux m ⬝ᵥ η₀)) ∂γ_aux| /
          Z (e_tot ξ).1 ^ 2 ≤ |M| * (|D₁| * Real.exp B) / Real.exp (-B) ^ 2 :=
        div_le_div₀ (by positivity)
          (mul_le_mul ((hM _).trans (le_abs_self _)) hb_int (abs_nonneg _) (abs_nonneg _))
          (sq_pos_of_pos (Real.exp_pos _))
          (pow_le_pow_left₀ (Real.exp_pos _).le (hZb (fun m' => α_sh m' ⬝ᵥ (e_tot ξ).1)) 2)
      have hdG_sub : |deriv G (Real.log (Z (e_tot ξ).1)) - G (Real.log (Z (e_tot ξ).1))| ≤
          CG + CG' := by
        have h := abs_sub (deriv G (Real.log (Z (e_tot ξ).1))) (G (Real.log (Z (e_tot ξ).1)))
        linarith [hGb _ (hZ_mem (e_tot ξ).1), hGd _ (hZ_mem (e_tot ξ).1)]
      exact mul_le_mul hfrac hdG_sub (abs_nonneg _) (by positivity)
    simp_rw [hr2_eq]
    rw [h_push rhs2Fun hr2_m hr2_i]
    simp_rw [hrhs2Fun, integral_const_mul]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    dsimp only
    rw [integral_mul_const, integral_div, integral_mul_const]
  rw [← hLHS, hstein]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [hcovX, hRHS1]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hcovY m, hRHS2 m]
  ring

/-- **Log-weighted marked-replica Stein identity for `deriv u` with zero diagonal covariance.**
Let `μ₀` be a probability measure on `α` with measurable projection `π : α → L` onto a finite set
`L`, and let `Z_w w = ∫ q, exp(u(S(w, q))) d(μ₀ × γ_aux)`. Under `SmartPathPotential₂`,
`W_sh τ₁ ⬝ᵥ α_sh τ₂ = (1 / 2) * c τ₁ τ₂`, `W_sh τ ⬝ᵥ α_sh τ + W_aux τ ⬝ᵥ α_aux τ = 0`, and `G`
differentiable with bounded value and derivative on `[-|B|, |B|]`:
`𝔼_w[⟨Wt(y) u'(S(w, y))⟩_{ν_w} * G(log Z_w(w))] =
  (1 / 2) * 𝔼_w[⟨c(π σ_0, π σ_1) u'(S(w, σ_0)) u'(S(w, σ_1))⟩_{ν_w^{⊗2}} *
    (G'(log Z_w(w)) - G(log Z_w(w)))]`. -/
theorem stein_tilted_unit_replica_deriv_mul_comp_log
    {α L K_sh K_aux : Type*} [MeasurableSpace α]
    [Finite L] [MeasurableSpace L] [MeasurableSingletonClass L]
    [Fintype K_sh] [Fintype K_aux]
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (π : α → L) (hπ : Measurable π)
    (α_sh W_sh : L → K_sh → ℝ) (α_aux W_aux : L → K_aux → ℝ)
    {u : ℝ → ℝ} {B D₁ D₂ : ℝ} (hu : SmartPathPotential₂ u B D₁ D₂)
    (c : L → L → ℝ)
    (hcov_sh : ∀ τ₁ τ₂, W_sh τ₁ ⬝ᵥ α_sh τ₂ = (1 / 2) * c τ₁ τ₂)
    (hcov_diag : ∀ τ, W_sh τ ⬝ᵥ α_sh τ + W_aux τ ⬝ᵥ α_aux τ = 0)
    {G : ℝ → ℝ} (hG : Differentiable ℝ G) {CG CG' : ℝ}
    (hGb : ∀ t ∈ Set.Icc (-|B|) |B|, |G t| ≤ CG)
    (hGd : ∀ t ∈ Set.Icc (-|B|) |B|, |deriv G t| ≤ CG') :
    let γ_sh := Measure.pi fun _ : K_sh => gaussianReal 0 1
    let γ_aux := Measure.pi fun _ : K_aux => gaussianReal 0 1
    let S (w : K_sh → ℝ) (y : α × (K_aux → ℝ)) : ℝ :=
      α_sh (π y.1) ⬝ᵥ w + α_aux (π y.1) ⬝ᵥ y.2
    let Wt (w : K_sh → ℝ) (y : α × (K_aux → ℝ)) : ℝ :=
      W_sh (π y.1) ⬝ᵥ w + W_aux (π y.1) ⬝ᵥ y.2
    let Z_w (w : K_sh → ℝ) : ℝ := ∫ y, Real.exp (u (S w y)) ∂(μ₀.prod γ_aux)
    ∫ w, (∫ y : α × (K_aux → ℝ), Wt w y * deriv u (S w y)
        ∂((μ₀.prod γ_aux).tilted (fun y => u (S w y)))) * G (Real.log (Z_w w)) ∂γ_sh =
      (1 / 2) * ∫ w, (∫ σ : Option Unit → α × (K_aux → ℝ),
        c (π (σ (some ())).1) (π (σ none).1) *
          deriv u (S w (σ (some ()))) * deriv u (S w (σ none))
        ∂(Measure.pi fun _ : Option Unit => (μ₀.prod γ_aux).tilted (fun y => u (S w y)))) *
        (deriv G (Real.log (Z_w w)) - G (Real.log (Z_w w))) ∂γ_sh := by
  classical
  have := Fintype.ofFinite L
  intro γ_sh γ_aux S Wt Z_w
  have hum : Measurable u := hu.measurable
  have hB_abs : ∀ x, |u x| ≤ |B| := fun x => (hu.abs_le x).trans (le_abs_self B)
  let p : L → ℝ := fun m => (μ₀.map π).real {m}
  have hp0 : ∀ m, 0 ≤ p m := fun m => ENNReal.toReal_nonneg
  have hp1 : ∑ m : L, p m = 1 := by
    have : IsProbabilityMeasure (μ₀.map π) :=
      (Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).2 inferInstance
    simp [p]
  let Z (w : K_sh → ℝ) : ℝ :=
    ∑ m : L, p m * ∫ η, Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η)) ∂γ_aux
  have hZ_eq : ∀ w : K_sh → ℝ, Z_w w = Z w := by
    intro w
    dsimp only [Z_w, Z, S]
    have hexp : Integrable (fun q : α × (K_aux → ℝ) =>
        Real.exp (u (α_sh (π q.1) ⬝ᵥ w + α_aux (π q.1) ⬝ᵥ q.2))) (μ₀.prod γ_aux) := by
      have hm1 : Measurable fun q : α × (K_aux → ℝ) => α_sh (π q.1) ⬝ᵥ w :=
        (measurable_of_finite fun m => α_sh m ⬝ᵥ w).comp (hπ.comp measurable_fst)
      have hm2 : Measurable fun q : α × (K_aux → ℝ) => α_aux (π q.1) ⬝ᵥ q.2 := by
        simp only [dotProduct]
        exact Finset.measurable_sum _ fun k _ =>
          ((measurable_of_finite fun m => α_aux m k).comp (hπ.comp measurable_fst)).mul
            ((measurable_pi_apply k).comp measurable_snd)
      exact Integrable.of_bound (C := Real.exp |B|)
        (Real.measurable_exp.comp (hum.comp (hm1.add hm2))).aestronglyMeasurable
        (ae_of_all _ fun q => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact Real.exp_le_exp.2 (le_of_abs_le (hB_abs _)))
    rw [integral_prod _ hexp]
    set g_m : L → ℝ := fun m => ∫ η, Real.exp (u (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η)) ∂γ_aux
    change ∫ a, g_m (π a) ∂μ₀ = ∑ m : L, p m * g_m m
    rw [← integral_map hπ.aemeasurable (measurable_of_finite g_m).aestronglyMeasurable,
      integral_fintype Integrable.of_finite]
    simp [p, smul_eq_mul]
  obtain ⟨hZd, hZb, hZu, -, -⟩ :=
    hasFDerivAt_Z_sum_bounds hu.differentiable hB_abs hu.abs_deriv_le p hp0 hp1 α_aux
  have hZm : Measurable Z := by
    have hm_lin : Measurable fun (w : K_sh → ℝ) (m : L) => α_sh m ⬝ᵥ w :=
      measurable_pi_iff.2 fun m => by simp only [dotProduct]; fun_prop
    exact hZd.continuous.measurable.comp hm_lin
  have hZ_pos : ∀ w, 0 < Z w := fun w =>
    (Real.exp_pos (-|B|)).trans_le (hZb (fun m => α_sh m ⬝ᵥ w))
  have hZ_mem : ∀ w, Real.log (Z w) ∈ Set.Icc (-|B|) |B| := fun w =>
    ⟨by simpa using Real.log_le_log (Real.exp_pos (-|B|)) (hZb (fun m => α_sh m ⬝ᵥ w)),
     by simpa using Real.log_le_log (hZ_pos w) (hZu (fun m => α_sh m ⬝ᵥ w))⟩
  let ϕ (x : ℝ) : ℝ := deriv u x * Real.exp (u x)
  have hψ_deriv := hu.hasDerivAt_deriv_mul_exp
  have hϕ_d : Differentiable ℝ ϕ := fun x => (hψ_deriv x).differentiableAt
  have hM : ∀ x, |ϕ x| ≤ |D₁| * Real.exp |B| := fun x =>
    abs_mul_exp_le (hu.abs_deriv_le_abs x) (hu.le_abs x)
  have hM' : ∀ x, |deriv ϕ x| ≤ (|D₂| + |D₁| ^ 2) * Real.exp |B| := fun x => by
    dsimp only [ϕ]
    rw [(hψ_deriv x).deriv, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul ?_ (Real.exp_le_exp.2 (hu.le_abs x)) (Real.exp_pos _).le (by positivity)
    refine (abs_add_le _ _).trans (add_le_add ((hu.abs_deriv₂_le x).trans (le_abs_self D₂)) ?_)
    rw [abs_mul, sq]
    exact mul_le_mul (hu.abs_deriv_le_abs x) (hu.abs_deriv_le_abs x)
      (abs_nonneg _) (abs_nonneg _)
  have hLHS_w : ∀ w : K_sh → ℝ,
      (∫ y : α × (K_aux → ℝ), Wt w y * deriv u (S w y)
          ∂((μ₀.prod γ_aux).tilted (fun y => u (S w y)))) * G (Real.log (Z_w w)) =
      ∑ s₀ : L, p s₀ *
        (((∫ η : K_aux → ℝ, (W_sh s₀ ⬝ᵥ w + W_aux s₀ ⬝ᵥ η) *
            ϕ (α_sh s₀ ⬝ᵥ w + α_aux s₀ ⬝ᵥ η) ∂γ_aux) / Z w) * G (Real.log (Z w))) := by
    intro w
    rw [integral_tilted_eq_div, hZ_eq w]
    change ((∫ y, Wt w y * deriv u (S w y) * Real.exp (u (S w y)) ∂(μ₀.prod γ_aux)) / Z_w w) *
      G (Real.log (Z w)) = _
    rw [hZ_eq w]
    have hnum_i : Integrable (fun y : α × (K_aux → ℝ) =>
        Wt w y * ϕ (S w y)) (μ₀.prod γ_aux) := by
      have hmS : Measurable (S w) := by
        refine ((measurable_of_finite fun m => α_sh m ⬝ᵥ w).comp (hπ.comp measurable_fst)).add ?_
        simp only [dotProduct]
        exact Finset.measurable_sum _ fun k _ =>
          ((measurable_of_finite fun m => α_aux m k).comp (hπ.comp measurable_fst)).mul
            ((measurable_pi_apply k).comp measurable_snd)
      have hmWt : Measurable (Wt w) := by
        refine ((measurable_of_finite fun m => W_sh m ⬝ᵥ w).comp (hπ.comp measurable_fst)).add ?_
        simp only [dotProduct]
        exact Finset.measurable_sum _ fun k _ =>
          ((measurable_of_finite fun m => W_aux m k).comp (hπ.comp measurable_fst)).mul
            ((measurable_pi_apply k).comp measurable_snd)
      let C_sh : ℝ := ∑ m : L, |W_sh m ⬝ᵥ w|
      let C_aux : ℝ := ∑ m : L, ∑ k : K_aux, |W_aux m k|
      have hdom : Integrable (fun y : α × (K_aux → ℝ) =>
          (C_sh + C_aux * ∑ k : K_aux, |y.2 k|) * (|D₁| * Real.exp |B|)) (μ₀.prod γ_aux) := by
        refine ((integrable_const C_sh).add ?_).mul_const _
        refine (integrable_finsetSum _ fun k _ => ?_).const_mul C_aux
        exact (integrable_comp_eval (μ := fun _ : K_aux => gaussianReal 0 1) (i := k)
          IsGaussian.integrable_id.abs).comp_snd _
      refine hdom.mono' (hmWt.mul (hϕ_d.continuous.measurable.comp hmS)).aestronglyMeasurable
        (ae_of_all _ fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul ?_ (hM _) (abs_nonneg _) (by positivity)
      dsimp only [Wt]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · exact Finset.single_le_sum (f := fun m : L => |W_sh m ⬝ᵥ w|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ (π y.1))
      · rw [Finset.mul_sum]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        have h1 := Finset.single_le_sum (f := fun k' : K_aux => |W_aux (π y.1) k'|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
        exact h1.trans (Finset.single_le_sum (f := fun m : L => ∑ k' : K_aux, |W_aux m k'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ (π y.1)))
    have hnum_eq : (∫ y : α × (K_aux → ℝ),
        Wt w y * deriv u (S w y) * Real.exp (u (S w y)) ∂(μ₀.prod γ_aux)) =
        ∑ s₀ : L, p s₀ * ∫ η : K_aux → ℝ,
          (W_sh s₀ ⬝ᵥ w + W_aux s₀ ⬝ᵥ η) * ϕ (α_sh s₀ ⬝ᵥ w + α_aux s₀ ⬝ᵥ η) ∂γ_aux := by
      have hcongr : (∫ y : α × (K_aux → ℝ),
          Wt w y * deriv u (S w y) * Real.exp (u (S w y)) ∂(μ₀.prod γ_aux)) =
          ∫ y : α × (K_aux → ℝ), Wt w y * ϕ (S w y) ∂(μ₀.prod γ_aux) :=
        integral_congr_ae (ae_of_all _ fun y => by dsimp only [ϕ]; ring)
      rw [hcongr, integral_prod _ hnum_i]
      set h_m : L → ℝ := fun m => ∫ η, (W_sh m ⬝ᵥ w + W_aux m ⬝ᵥ η) *
        ϕ (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η) ∂γ_aux
      change ∫ a, h_m (π a) ∂μ₀ = ∑ s₀ : L, p s₀ * h_m s₀
      rw [← integral_map hπ.aemeasurable (measurable_of_finite h_m).aestronglyMeasurable,
        integral_fintype Integrable.of_finite]
      simp [p, smul_eq_mul]
    rw [hnum_eq, Finset.sum_div, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s₀ _ => by ring
  have hRHS_w : ∀ w : K_sh → ℝ,
      (∫ σ : Option Unit → α × (K_aux → ℝ),
          c (π (σ (some ())).1) (π (σ none).1) *
            deriv u (S w (σ (some ()))) * deriv u (S w (σ none))
          ∂(Measure.pi fun _ : Option Unit => (μ₀.prod γ_aux).tilted (fun y => u (S w y)))) *
        (deriv G (Real.log (Z_w w)) - G (Real.log (Z_w w))) =
      ∑ s₀ : L, ∑ m : L, p s₀ * p m * c s₀ m *
        ((((∫ η : K_aux → ℝ, ϕ (α_sh s₀ ⬝ᵥ w + α_aux s₀ ⬝ᵥ η) ∂γ_aux) *
            ∫ η₀ : K_aux → ℝ, ϕ (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) ∂γ_aux) / Z w ^ 2) *
          (deriv G (Real.log (Z w)) - G (Real.log (Z w)))) := by
    intro w
    have : IsFiniteMeasure (μ₀.prod γ_aux) := inferInstance
    rw [integral_pi_tilted_eq_div,
      integral_pi_exp_sum (fun y : α × (K_aux → ℝ) => u (S w y)),
      Fintype.card_option, Fintype.card_unique]
    have hZ_def : (∫ a : α × (K_aux → ℝ), Real.exp (u (S w a)) ∂μ₀.prod γ_aux) = Z w := hZ_eq w
    rw [hZ_def, hZ_eq w]
    let J_1 : L → ℝ := fun m => ∫ η : K_aux → ℝ, ϕ (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η) ∂γ_aux
    have h_f1 : ∀ (g : L → ℝ),
        ∫ y : α × (K_aux → ℝ), g (π y.1) * ϕ (S w y) ∂(μ₀.prod γ_aux) =
          ∑ m : L, p m * g m * J_1 m := by
      intro g
      have hi : Integrable (fun y : α × (K_aux → ℝ) => g (π y.1) * ϕ (S w y)) (μ₀.prod γ_aux) := by
        have hmS : Measurable (S w) := by
          refine ((measurable_of_finite fun m => α_sh m ⬝ᵥ w).comp (hπ.comp measurable_fst)).add ?_
          simp only [dotProduct]
          exact Finset.measurable_sum _ fun k _ =>
            ((measurable_of_finite fun m => α_aux m k).comp (hπ.comp measurable_fst)).mul
              ((measurable_pi_apply k).comp measurable_snd)
        let Bg : ℝ := ∑ m : L, |g m|
        exact Integrable.of_bound
          (((measurable_of_finite g).comp (hπ.comp measurable_fst)).mul
            (hϕ_d.continuous.measurable.comp hmS)).aestronglyMeasurable
          (Bg * (|D₁| * Real.exp |B|)) (ae_of_all _ fun y => by
            rw [Real.norm_eq_abs, abs_mul]
            exact mul_le_mul
              (Finset.single_le_sum (f := fun m => |g m|) (fun _ _ => abs_nonneg _)
                (Finset.mem_univ _))
              (hM _) (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _))
      rw [integral_prod _ hi]
      set k_m : L → ℝ := fun m => g m * J_1 m
      have h_inner : ∀ a : α, ∫ η : K_aux → ℝ, g (π a) * ϕ (S w (a, η)) ∂γ_aux = k_m (π a) :=
        fun a => by dsimp only [S, k_m, J_1]; rw [integral_const_mul]
      simp_rw [h_inner]
      rw [← integral_map hπ.aemeasurable (measurable_of_finite k_m).aestronglyMeasurable,
        integral_fintype Integrable.of_finite]
      simp only [p, k_m, smul_eq_mul]
      exact Finset.sum_congr rfl fun m _ => by ring
    have hnum_2 :
        (∫ σ : Option Unit → α × (K_aux → ℝ),
          c (π (σ (some ())).1) (π (σ none).1) *
            deriv u (S w (σ (some ()))) * deriv u (S w (σ none)) *
            Real.exp (∑ r : Option Unit, u (S w (σ r)))
          ∂(Measure.pi fun _ : Option Unit => μ₀.prod γ_aux)) =
        ∑ s₀ : L, ∑ m : L, p s₀ * p m * c s₀ m * (J_1 s₀ * J_1 m) := by
      have h_alg : ∀ σ : Option Unit → α × (K_aux → ℝ),
          c (π (σ (some ())).1) (π (σ none).1) *
            deriv u (S w (σ (some ()))) * deriv u (S w (σ none)) *
            Real.exp (∑ r : Option Unit, u (S w (σ r))) =
          ∑ s₀ : L, (c s₀ (π (σ none).1) * ϕ (S w (σ none))) *
            ((if π (σ (some ())).1 = s₀ then (1 : ℝ) else 0) * ϕ (S w (σ (some ())))) := by
        intro σ
        rw [Fintype.sum_option, Finset.univ_unique, Finset.sum_singleton, Real.exp_add]
        have hsum_s : ∑ s₀ : L, (c s₀ (π (σ none).1) * ϕ (S w (σ none))) *
            ((if π (σ (some ())).1 = s₀ then (1 : ℝ) else 0) * ϕ (S w (σ (some ())))) =
            (c (π (σ (some ())).1) (π (σ none).1) * ϕ (S w (σ none))) *
              (1 * ϕ (S w (σ (some ())))) := by
          rw [Finset.sum_eq_single (π (σ (some ())).1)]
          · simp
          · intro s₀ _ hs; simp [hs.symm]
          · simp
        rw [hsum_s]
        dsimp only [ϕ]; ring
      simp_rw [h_alg]
      have hmS : Measurable (S w) := by
        refine ((measurable_of_finite fun m => α_sh m ⬝ᵥ w).comp (hπ.comp measurable_fst)).add ?_
        simp only [dotProduct]
        exact Finset.measurable_sum _ fun k _ =>
          ((measurable_of_finite fun m => α_aux m k).comp (hπ.comp measurable_fst)).mul
            ((measurable_pi_apply k).comp measurable_snd)
      have h_term_i : ∀ s₀ : L, Integrable (fun σ : Option Unit → α × (K_aux → ℝ) =>
          (c s₀ (π (σ none).1) * ϕ (S w (σ none))) *
            ((if π (σ (some ())).1 = s₀ then (1 : ℝ) else 0) * ϕ (S w (σ (some ())))))
          (Measure.pi fun _ : Option Unit => μ₀.prod γ_aux) := by
        intro s₀
        let Bc : ℝ := ∑ m : L, |c s₀ m|
        refine Integrable.of_bound ?_
          ((Bc * (|D₁| * Real.exp |B|)) * (|D₁| * Real.exp |B|))
          (ae_of_all _ fun σ => ?_)
        · have hm_none : Measurable fun σ : Option Unit → α × (K_aux → ℝ) =>
              c s₀ (π (σ none).1) * ϕ (S w (σ none)) :=
            (((measurable_of_finite fun m => c s₀ m).comp
              (hπ.comp (measurable_fst.comp (measurable_pi_apply none)))).mul
              ((hϕ_d.continuous.measurable.comp hmS).comp (measurable_pi_apply none)))
          have hm_some : Measurable fun σ : Option Unit → α × (K_aux → ℝ) =>
              (if π (σ (some ())).1 = s₀ then (1 : ℝ) else 0) * ϕ (S w (σ (some ()))) :=
            (((measurable_of_finite fun m => if m = s₀ then (1 : ℝ) else 0).comp
              (hπ.comp (measurable_fst.comp (measurable_pi_apply (some ()))))).mul
              ((hϕ_d.continuous.measurable.comp hmS).comp (measurable_pi_apply (some ()))))
          exact (hm_none.mul hm_some).aestronglyMeasurable
        · rw [Real.norm_eq_abs, abs_mul,
            abs_mul (c s₀ (π (σ none).1)) (ϕ (S w (σ none))),
            abs_mul (if π (σ (some ())).1 = s₀ then (1 : ℝ) else 0) (ϕ (S w (σ (some ()))))]
          have h1 : |c s₀ (π (σ none).1)| ≤ Bc :=
            Finset.single_le_sum (f := fun m => |c s₀ m|) (fun _ _ => abs_nonneg _)
              (Finset.mem_univ _)
          have h2 : |if π (σ (some ())).1 = s₀ then (1 : ℝ) else 0| ≤ 1 := by
            split_ifs <;> norm_num
          have hb1 : |c s₀ (π (σ none).1)| * |ϕ (S w (σ none))| ≤
              Bc * (|D₁| * Real.exp |B|) :=
            mul_le_mul h1 (hM _) (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
          have hb2 : |if π (σ (some ())).1 = s₀ then (1 : ℝ) else 0| * |ϕ (S w (σ (some ())))| ≤
              |D₁| * Real.exp |B| := by
            simpa only [one_mul] using mul_le_mul h2 (hM _) (abs_nonneg _) zero_le_one
          exact mul_le_mul hb1 hb2 (by positivity) (by positivity)
      rw [integral_finsetSum _ fun s₀ _ => h_term_i s₀]
      refine Finset.sum_congr rfl fun s₀ _ => ?_
      have hm_some_1 : Measurable fun f_u : Unit → α × (K_aux → ℝ) =>
          (if π (f_u ()).1 = s₀ then (1 : ℝ) else 0) * ϕ (S w (f_u ())) :=
        (((measurable_of_finite fun m => if m = s₀ then (1 : ℝ) else 0).comp
          (hπ.comp (measurable_fst.comp (measurable_pi_apply ())))).mul
          ((hϕ_d.continuous.measurable.comp hmS).comp (measurable_pi_apply ())))
      have hm_none_1 : Measurable fun y : α × (K_aux → ℝ) => c s₀ (π y.1) * ϕ (S w y) :=
        ((measurable_of_finite fun m => c s₀ m).comp (hπ.comp measurable_fst)).mul
          (hϕ_d.continuous.measurable.comp hmS)
      have hfresh := integral_pi_fresh_replica_mul (μ₀.prod γ_aux) (Option.some_injective Unit)
        (fun r => Option.some_ne_none r)
        (fun f_u : Unit → α × (K_aux → ℝ) =>
          (if π (f_u ()).1 = s₀ then (1 : ℝ) else 0) * ϕ (S w (f_u ())))
        (fun y : α × (K_aux → ℝ) => c s₀ (π y.1) * ϕ (S w y))
        hm_some_1.aestronglyMeasurable hm_none_1.aestronglyMeasurable
      have hcomm : (∫ σ : Option Unit → α × (K_aux → ℝ),
          (c s₀ (π (σ none).1) * ϕ (S w (σ none))) *
            ((if π (σ (some ())).1 = s₀ then (1 : ℝ) else 0) * ϕ (S w (σ (some ()))))
          ∂(Measure.pi fun _ : Option Unit => μ₀.prod γ_aux)) =
          ∫ σ : Option Unit → α × (K_aux → ℝ),
            ((if π (σ (some ())).1 = s₀ then (1 : ℝ) else 0) * ϕ (S w (σ (some ())))) *
              (c s₀ (π (σ none).1) * ϕ (S w (σ none)))
            ∂(Measure.pi fun _ : Option Unit => μ₀.prod γ_aux) :=
        integral_congr_ae (ae_of_all _ fun _ => mul_comm _ _)
      rw [hcomm, hfresh]
      have h_u : (∫ f_u : Unit → α × (K_aux → ℝ),
          (if π (f_u ()).1 = s₀ then (1 : ℝ) else 0) * ϕ (S w (f_u ()))
          ∂(Measure.pi fun _ : Unit => μ₀.prod γ_aux)) =
          ∫ y : α × (K_aux → ℝ),
            (if π y.1 = s₀ then (1 : ℝ) else 0) * ϕ (S w y) ∂(μ₀.prod γ_aux) :=
        (measurePreserving_funUnique (μ₀.prod γ_aux) Unit).integral_comp_of_aestronglyMeasurable
          (g := fun y : α × (K_aux → ℝ) => (if π y.1 = s₀ then (1 : ℝ) else 0) * ϕ (S w y))
          (((measurable_of_finite fun m => if m = s₀ then (1 : ℝ) else 0).comp
            (hπ.comp measurable_fst)).mul
            (hϕ_d.continuous.measurable.comp hmS)).aestronglyMeasurable
      rw [h_u, h_f1 (fun m => if m = s₀ then 1 else 0), h_f1 (fun m => c s₀ m)]
      have h_s0 : ∑ m : L, p m * (if m = s₀ then (1 : ℝ) else 0) * J_1 m = p s₀ * J_1 s₀ := by
        rw [Finset.sum_eq_single s₀]
        · simp
        · intro m _ hm; simp [hm]
        · simp
      rw [h_s0, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [hnum_2, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s₀ _ => ?_
    rw [Finset.sum_div, Finset.sum_mul]
    exact Finset.sum_congr rfl fun m _ => by dsimp only [J_1]; ring
  simp_rw [hLHS_w, hRHS_w]
  have hL_sum_i : ∀ s₀ : L, Integrable (fun w : K_sh → ℝ =>
      p s₀ * (((∫ η : K_aux → ℝ, (W_sh s₀ ⬝ᵥ w + W_aux s₀ ⬝ᵥ η) *
        ϕ (α_sh s₀ ⬝ᵥ w + α_aux s₀ ⬝ᵥ η) ∂γ_aux) / Z w) * G (Real.log (Z w)))) γ_sh := by
    intro s₀
    have hCG0 : 0 ≤ CG := (abs_nonneg _).trans (hGb _ (hZ_mem 0))
    let C_aux : ℝ := ∫ η : K_aux → ℝ, |W_aux s₀ ⬝ᵥ η| ∂γ_aux
    let dom_w (w : K_sh → ℝ) : ℝ :=
      p s₀ * (((|W_sh s₀ ⬝ᵥ w| + C_aux) * (|D₁| * Real.exp |B|) / Real.exp (-|B|)) * CG)
    have hdom_i : Integrable dom_w γ_sh := by
      refine (((?_) : Integrable (fun w : K_sh → ℝ => |W_sh s₀ ⬝ᵥ w| + C_aux) γ_sh).mul_const
        (|D₁| * Real.exp |B|) |>.div_const _ |>.mul_const CG).const_mul (p s₀)
      refine Integrable.add ?_ (integrable_const C_aux)
      have hcW : HasGaussianLaw (fun (w : K_sh → ℝ) (_ : Unit) => W_sh s₀ ⬝ᵥ w) γ_sh :=
        hasGaussianLaw_dotProduct_family (fun _ => W_sh s₀)
      exact (hcW.eval ()).integrable.abs
    have hm_w : Measurable fun w : K_sh → ℝ =>
        p s₀ * (((∫ η : K_aux → ℝ, (W_sh s₀ ⬝ᵥ w + W_aux s₀ ⬝ᵥ η) *
          ϕ (α_sh s₀ ⬝ᵥ w + α_aux s₀ ⬝ᵥ η) ∂γ_aux) / Z w) * G (Real.log (Z w))) := by
      have hj : Measurable fun q : (K_sh → ℝ) × (K_aux → ℝ) =>
          (W_sh s₀ ⬝ᵥ q.1 + W_aux s₀ ⬝ᵥ q.2) * ϕ (α_sh s₀ ⬝ᵥ q.1 + α_aux s₀ ⬝ᵥ q.2) :=
        ((by simp only [dotProduct]; fun_prop : Measurable fun q : (K_sh → ℝ) × (K_aux → ℝ) =>
          W_sh s₀ ⬝ᵥ q.1 + W_aux s₀ ⬝ᵥ q.2)).mul
          (hϕ_d.continuous.measurable.comp (by simp only [dotProduct]; fun_prop))
      exact ((((hj.stronglyMeasurable.integral_prod_right' (ν := γ_aux)).measurable).div hZm).mul
        (hG.continuous.measurable.comp (Real.measurable_log.comp hZm))).const_mul _
    refine hdom_i.mono' hm_w.aestronglyMeasurable (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 s₀), abs_mul, abs_div,
      abs_of_pos (hZ_pos w)]
    refine mul_le_mul_of_nonneg_left ?_ (hp0 s₀)
    have hη_i : Integrable (fun η : K_aux → ℝ => |W_aux s₀ ⬝ᵥ η|) γ_aux :=
      ((hasGaussianLaw_dotProduct_family (fun _ : Unit => W_aux s₀)).eval ()).integrable.abs
    have hint_num : |∫ η : K_aux → ℝ, (W_sh s₀ ⬝ᵥ w + W_aux s₀ ⬝ᵥ η) *
        ϕ (α_sh s₀ ⬝ᵥ w + α_aux s₀ ⬝ᵥ η) ∂γ_aux| ≤
        (|W_sh s₀ ⬝ᵥ w| + C_aux) * (|D₁| * Real.exp |B|) := by
      calc _ ≤ ∫ η, |(W_sh s₀ ⬝ᵥ w + W_aux s₀ ⬝ᵥ η) *
              ϕ (α_sh s₀ ⬝ᵥ w + α_aux s₀ ⬝ᵥ η)| ∂γ_aux := abs_integral_le_integral_abs
        _ ≤ ∫ η, (|W_sh s₀ ⬝ᵥ w| + |W_aux s₀ ⬝ᵥ η|) * (|D₁| * Real.exp |B|) ∂γ_aux := by
            refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
              (((integrable_const _).add hη_i).mul_const _) (ae_of_all _ fun η => ?_)
            dsimp only
            rw [abs_mul]
            exact mul_le_mul (abs_add_le _ _) (hM _) (abs_nonneg _) (by positivity)
        _ = (|W_sh s₀ ⬝ᵥ w| + C_aux) * (|D₁| * Real.exp |B|) := by
            rw [integral_mul_const, integral_add (integrable_const _) hη_i, integral_const,
              probReal_univ, one_smul]
    exact mul_le_mul
      (div_le_div₀ (by positivity) hint_num (Real.exp_pos _)
        (hZb (fun m => α_sh m ⬝ᵥ w)))
      (hGb _ (hZ_mem w)) (abs_nonneg _) (by positivity)
  have hR_pair_i : ∀ (s₀ m : L), Integrable (fun w : K_sh → ℝ =>
      ((((∫ η : K_aux → ℝ, ϕ (α_sh s₀ ⬝ᵥ w + α_aux s₀ ⬝ᵥ η) ∂γ_aux) *
          ∫ η₀ : K_aux → ℝ, ϕ (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) ∂γ_aux) / Z w ^ 2) *
        (deriv G (Real.log (Z w)) - G (Real.log (Z w))))) γ_sh := by
    intro s₀ m
    have hCG0 : 0 ≤ CG := (abs_nonneg _).trans (hGb _ (hZ_mem 0))
    have hCG'0 : 0 ≤ CG' := (abs_nonneg _).trans (hGd _ (hZ_mem 0))
    have hmJ : ∀ l : L, Measurable fun w : K_sh → ℝ =>
        ∫ η : K_aux → ℝ, ϕ (α_sh l ⬝ᵥ w + α_aux l ⬝ᵥ η) ∂γ_aux := fun l => by
      have hj : Measurable fun q : (K_sh → ℝ) × (K_aux → ℝ) =>
          ϕ (α_sh l ⬝ᵥ q.1 + α_aux l ⬝ᵥ q.2) :=
        hϕ_d.continuous.measurable.comp (by simp only [dotProduct]; fun_prop)
      exact (hj.stronglyMeasurable.integral_prod_right' (ν := γ_aux)).measurable
    have hm_tot : Measurable fun w : K_sh → ℝ =>
        ((((∫ η : K_aux → ℝ, ϕ (α_sh s₀ ⬝ᵥ w + α_aux s₀ ⬝ᵥ η) ∂γ_aux) *
            ∫ η₀ : K_aux → ℝ, ϕ (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) ∂γ_aux) / Z w ^ 2) *
          (deriv G (Real.log (Z w)) - G (Real.log (Z w)))) :=
      ((((hmJ s₀).mul (hmJ m)).div (hZm.pow_const 2)).mul
        (((measurable_deriv G).comp (Real.measurable_log.comp hZm)).sub
          (hG.continuous.measurable.comp (Real.measurable_log.comp hZm))))
    refine Integrable.of_bound hm_tot.aestronglyMeasurable
      (((|D₁| * Real.exp |B|) * (|D₁| * Real.exp |B|) / Real.exp (-|B|) ^ 2) * (CG + CG'))
      (ae_of_all _ fun w => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos (sq_pos_of_pos (hZ_pos w)), abs_mul]
    have hbJ : ∀ l : L, |∫ η : K_aux → ℝ, ϕ (α_sh l ⬝ᵥ w + α_aux l ⬝ᵥ η) ∂γ_aux| ≤
        |D₁| * Real.exp |B| := fun l => by
      have hb := norm_integral_le_of_norm_le_const (μ := γ_aux)
        (f := fun η => ϕ (α_sh l ⬝ᵥ w + α_aux l ⬝ᵥ η)) (C := |D₁| * Real.exp |B|)
        (ae_of_all _ fun η => by rw [Real.norm_eq_abs]; exact hM _)
      simpa [γ_aux] using hb
    have hfrac := div_le_div₀ (by positivity)
      (mul_le_mul (hbJ s₀) (hbJ m) (abs_nonneg _) (by positivity))
      (sq_pos_of_pos (Real.exp_pos _))
      (pow_le_pow_left₀ (Real.exp_pos _).le (hZb (fun m' => α_sh m' ⬝ᵥ w)) 2)
    have hdG_sub : |deriv G (Real.log (Z w)) - G (Real.log (Z w))| ≤ CG + CG' := by
      have h := abs_sub (deriv G (Real.log (Z w))) (G (Real.log (Z w)))
      linarith [hGb _ (hZ_mem w), hGd _ (hZ_mem w)]
    exact mul_le_mul hfrac hdG_sub (abs_nonneg _) (by positivity)
  rw [integral_finsetSum _ fun s₀ _ => hL_sum_i s₀]
  have hR_sum_eq :
      (∫ w, (∑ s₀ : L, ∑ m : L, p s₀ * p m * c s₀ m *
        ((((∫ η : K_aux → ℝ, ϕ (α_sh s₀ ⬝ᵥ w + α_aux s₀ ⬝ᵥ η) ∂γ_aux) *
            ∫ η₀ : K_aux → ℝ, ϕ (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) ∂γ_aux) / Z w ^ 2) *
          (deriv G (Real.log (Z w)) - G (Real.log (Z w))))) ∂γ_sh) =
      ∑ s₀ : L, ∑ m : L, p s₀ * p m * c s₀ m *
        ∫ w, ((((∫ η : K_aux → ℝ, ϕ (α_sh s₀ ⬝ᵥ w + α_aux s₀ ⬝ᵥ η) ∂γ_aux) *
            ∫ η₀ : K_aux → ℝ, ϕ (α_sh m ⬝ᵥ w + α_aux m ⬝ᵥ η₀) ∂γ_aux) / Z w ^ 2) *
          (deriv G (Real.log (Z w)) - G (Real.log (Z w)))) ∂γ_sh := by
    rw [integral_finsetSum _ fun s₀ _ =>
      integrable_finsetSum _ fun m _ => (hR_pair_i s₀ m).const_mul _]
    refine Finset.sum_congr rfl fun s₀ _ => ?_
    rw [integral_finsetSum _ fun m _ => (hR_pair_i s₀ m).const_mul _]
    exact Finset.sum_congr rfl fun m _ => integral_const_mul _ _
  rw [hR_sum_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s₀ _ => ?_
  rw [integral_const_mul]
  have hst := stein_ratio_comp_log_fixed_spin p hp0 hp1 α_sh W_sh α_aux W_aux
    hu.differentiable hB_abs hu.abs_deriv_le ϕ hϕ_d hM hM' hG hGb hGd s₀
  dsimp only at hst
  rw [hst, hcov_diag s₀, zero_mul, zero_add, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hcov_sh s₀ m]
  dsimp only [ϕ]
  ring

/-! ### Section 2: Regularity and integrability of powers of `A(s, ω)` -/

/-- Auxiliary: `|t|^m ≤ m! * exp(|t|)` for all `t : ℝ` and `m : ℕ`. -/
private lemma abs_pow_le_factorial_mul_exp_abs (m : ℕ) (t : ℝ) :
    |t| ^ m ≤ (Nat.factorial m : ℝ) * Real.exp |t| :=
  Real.pow_le_factorial_mul_exp (abs_nonneg t) m

/-- Auxiliary: for `A_0 : ℝ`, `a : ℝ`, `L > 0`, and `m : ℕ`, the polynomial
`G(t) = ((A_0 + L⁻¹ * t) - a)^m` is differentiable with exponential growth on `ℝ` and uniform bounds
on any compact interval `[-B, B]`. -/
private lemma polynomial_power_shift_bounds (A₀ a L : ℝ) (hL : 0 < L) (m : ℕ) :
    let G (t : ℝ) : ℝ := (A₀ + L⁻¹ * t - a) ^ m
    Differentiable ℝ G ∧
      (∀ t, HasDerivAt G ((m : ℝ) * L⁻¹ * (A₀ + L⁻¹ * t - a) ^ (m - 1)) t) ∧
      (∀ t, |G t| ≤ (2 ^ m * (|A₀ - a| ^ m + (L⁻¹) ^ m * (Nat.factorial m : ℝ))) *
        Real.exp |t|) ∧
      (∀ t, |deriv G t| ≤ ((m : ℝ) * L⁻¹ *
          (2 ^ (m - 1) * (|A₀ - a| ^ (m - 1) + (L⁻¹) ^ (m - 1) * (Nat.factorial (m - 1) : ℝ)))) *
        Real.exp |t|) ∧
      (∀ {B : ℝ}, 0 ≤ B → ∀ t ∈ Icc (-B) B, |G t| ≤ (|A₀ - a| + L⁻¹ * B) ^ m) ∧
      (∀ {B : ℝ}, 0 ≤ B → ∀ t ∈ Icc (-B) B,
        |deriv G t| ≤ (m : ℝ) * L⁻¹ * (|A₀ - a| + L⁻¹ * B) ^ (m - 1)) := by
  intro G
  have hhd : ∀ t : ℝ, HasDerivAt G ((m : ℝ) * L⁻¹ * (A₀ + L⁻¹ * t - a) ^ (m - 1)) t := by
    intro t
    have hlin : HasDerivAt (fun x : ℝ => A₀ + L⁻¹ * x - a) L⁻¹ t := by
      simpa using (((hasDerivAt_id t).const_mul L⁻¹).const_add A₀).sub_const a
    have hp := (hasDerivAt_pow m (A₀ + L⁻¹ * t - a)).comp t hlin
    exact hp.congr_deriv (by ring)
  have hdiff : Differentiable ℝ G := fun t => (hhd t).differentiableAt
  have hpow_exp : ∀ (p : ℕ) (t : ℝ), |A₀ + L⁻¹ * t - a| ^ p ≤
      (2 ^ p * (|A₀ - a| ^ p + (L⁻¹) ^ p * (Nat.factorial p : ℝ))) * Real.exp |t| := by
    intro p t
    have htri : |A₀ + L⁻¹ * t - a| ≤ |A₀ - a| + L⁻¹ * |t| := by
      have heq : A₀ + L⁻¹ * t - a = (A₀ - a) + L⁻¹ * t := by ring
      rw [heq]
      exact (abs_add_le _ _).trans (add_le_add le_rfl
        (by rw [abs_mul, abs_of_pos (inv_pos.2 hL)]))
    have h1 : |A₀ + L⁻¹ * t - a| ^ p ≤ 2 ^ p * (|A₀ - a| ^ p + (L⁻¹ * |t|) ^ p) := by
      calc |A₀ + L⁻¹ * t - a| ^ p
          ≤ (|A₀ - a| + L⁻¹ * |t|) ^ p := pow_le_pow_left₀ (abs_nonneg _) htri p
        _ ≤ 2 ^ (p - 1) * (|A₀ - a| ^ p + (L⁻¹ * |t|) ^ p) :=
            add_pow_le (abs_nonneg _) (by positivity) p
        _ ≤ 2 ^ p * (|A₀ - a| ^ p + (L⁻¹ * |t|) ^ p) :=
            mul_le_mul_of_nonneg_right
              (pow_le_pow_right₀ one_le_two (Nat.sub_le p 1)) (by positivity)
    have hexp_ge1 : 1 ≤ Real.exp |t| := Real.one_le_exp (abs_nonneg t)
    have hfac := abs_pow_le_factorial_mul_exp_abs p t
    rw [mul_pow] at h1
    calc |A₀ + L⁻¹ * t - a| ^ p
        ≤ 2 ^ p * (|A₀ - a| ^ p * 1 + (L⁻¹) ^ p * |t| ^ p) := by linarith
      _ ≤ 2 ^ p * (|A₀ - a| ^ p * Real.exp |t| +
            (L⁻¹) ^ p * ((Nat.factorial p : ℝ) * Real.exp |t|)) := by
          refine mul_le_mul_of_nonneg_left (add_le_add
            (mul_le_mul_of_nonneg_left hexp_ge1 (by positivity))
            (mul_le_mul_of_nonneg_left hfac (by positivity))) (by positivity)
      _ = (2 ^ p * (|A₀ - a| ^ p + (L⁻¹) ^ p * (Nat.factorial p : ℝ))) * Real.exp |t| := by ring
  refine ⟨hdiff, hhd, hpow_exp m, ?_, ?_, ?_⟩
  · intro t
    rw [(hhd t).deriv, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg m),
      abs_of_pos (inv_pos.2 hL), abs_pow]
    calc (m : ℝ) * L⁻¹ * |A₀ + L⁻¹ * t - a| ^ (m - 1)
        ≤ (m : ℝ) * L⁻¹ *
            ((2 ^ (m - 1) * (|A₀ - a| ^ (m - 1) +
              (L⁻¹) ^ (m - 1) * (Nat.factorial (m - 1) : ℝ))) * Real.exp |t|) :=
          mul_le_mul_of_nonneg_left (hpow_exp (m - 1) t) (by positivity)
      _ = _ := by ring
  · intro B hB t ht
    dsimp only [G]
    rw [abs_pow]
    have ht_abs : |t| ≤ B := abs_le.2 ht
    have htri : |A₀ + L⁻¹ * t - a| ≤ |A₀ - a| + L⁻¹ * B := by
      have heq : A₀ + L⁻¹ * t - a = (A₀ - a) + L⁻¹ * t := by ring
      rw [heq]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul, abs_of_pos (inv_pos.2 hL)]
      exact mul_le_mul_of_nonneg_left ht_abs (inv_nonneg.2 hL.le)
    exact pow_le_pow_left₀ (abs_nonneg _) htri m
  · intro B hB t ht
    rw [(hhd t).deriv, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg m),
      abs_of_pos (inv_pos.2 hL), abs_pow]
    have ht_abs : |t| ≤ B := abs_le.2 ht
    have htri : |A₀ + L⁻¹ * t - a| ≤ |A₀ - a| + L⁻¹ * B := by
      have heq : A₀ + L⁻¹ * t - a = (A₀ - a) + L⁻¹ * t := by ring
      rw [heq]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul, abs_of_pos (inv_pos.2 hL)]
      exact mul_le_mul_of_nonneg_left ht_abs (inv_nonneg.2 hL.le)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) htri (m - 1)) (by positivity)

end SpinGlasses
