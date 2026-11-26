/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.QuadraticTilt
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct

/-!
# Replica averages under a confined energy on a Euclidean space

The energies are bounded by `A + B ‖x‖ - κ ‖x‖²` with `κ > 0`, so the Gibbs densities relative to
the volume measure have Gaussian tails. Observables and energy derivatives may grow polynomially
in each replica, which covers the unbounded spins of continuous spin glass models.

## Main statements

* `MeasureTheory.integrable_pi_mul_exp_of_confining`: integrability of replica observables of
  polynomial growth against the product weight.
* `MeasureTheory.hasDerivAt_integral_pi_tilted_of_confining`: the derivative of a replica average
  whose energy and observable depend on a parameter, and its replica-difference form
  `MeasureTheory.hasDerivAt_integral_pi_tilted_of_confining_replicaDiff`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace MeasureTheory

section ReplicaSum

variable {E : Type*} [SeminormedAddCommGroup E] {R : Type*} [Fintype R]

/-- The product weight of confined energies is bounded replica by replica. -/
theorem exp_sum_le_prod_of_confining {κ A B : ℝ} {e : E → ℝ}
    (hconf : ∀ x, e x ≤ A + B * ‖x‖ - κ * ‖x‖ ^ 2) (σ : R → E) :
    Real.exp (∑ i, e (σ i)) ≤ ∏ i, Real.exp A * Real.exp (B * ‖σ i‖ - κ * ‖σ i‖ ^ 2) := by
  rw [Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) fun i _ => ?_
  rw [← Real.exp_add, Real.exp_le_exp, ← add_sub_assoc]
  exact hconf _

/-- The polynomial weight of one replica is at most the product of the weights of all replicas. -/
theorem one_add_norm_pow_le_prod (σ : R → E) (n : ℕ) (i : R) :
    (1 + ‖σ i‖) ^ n ≤ ∏ j, (1 + ‖σ j‖) ^ n := by
  have h1le : ∀ j, (1 : ℝ) ≤ (1 + ‖σ j‖) ^ n := fun j =>
    one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _))
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact le_mul_of_one_le_right (zero_le_one.trans (h1le i))
    (Finset.one_le_prod₀ (s := Finset.univ.erase i) fun j _ => h1le j)

/-- A sum over replicas of terms of polynomial growth grows at most polynomially in each
replica. -/
theorem abs_sum_le_mul_prod_one_add_norm_pow {f : E → ℝ} {L : ℝ} {n : ℕ}
    (hf : ∀ x, |f x| ≤ L * (1 + ‖x‖) ^ n) (σ : R → E) :
    |∑ i, f (σ i)| ≤ L * Fintype.card R * ∏ i, (1 + ‖σ i‖) ^ n := by
  have hL : 0 ≤ L := by simpa using (abs_nonneg _).trans (hf 0)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => (hf (σ i)).trans
    (mul_le_mul_of_nonneg_left (one_add_norm_pow_le_prod σ n i) hL)).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end ReplicaSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {R : Type*} [Fintype R]

/-- Replica observables of polynomial growth are integrable against the confined product
weight. -/
theorem integrable_pi_mul_exp_of_confining {κ : ℝ} (hκ : 0 < κ) {e : E → ℝ} (he : Measurable e)
    {A B : ℝ} (hconf : ∀ x, e x ≤ A + B * ‖x‖ - κ * ‖x‖ ^ 2) {Ψ : (R → E) → ℝ}
    (hΨ : Measurable Ψ) {C : ℝ} {m : ℕ} (hΨb : ∀ σ, |Ψ σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m) :
    Integrable (fun σ => Ψ σ * Real.exp (∑ i, e (σ i))) (Measure.pi fun _ : R => volume) := by
  have hprod : Integrable (fun σ : R → E => ∏ i,
      Real.exp A * ((1 + ‖σ i‖) ^ m * Real.exp (B * ‖σ i‖ - κ * ‖σ i‖ ^ 2)))
      (Measure.pi fun _ : R => volume) :=
    Integrable.fintype_prod (f := fun _ : R => fun x : E =>
      Real.exp A * ((1 + ‖x‖) ^ m * Real.exp (B * ‖x‖ - κ * ‖x‖ ^ 2)))
      fun _ => (integrable_one_add_norm_pow_mul_exp hκ B m).const_mul _
  refine (hprod.const_mul C).mono' (hΨ.mul (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun σ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine (mul_le_mul (hΨb σ) (exp_sum_le_prod_of_confining hconf σ) (Real.exp_pos _).le
    ((abs_nonneg _).trans (hΨb σ))).trans_eq ?_
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl fun i _ => by ring

/-- The Gibbs weight of a confined energy is integrable. -/
theorem integrable_exp_of_confining {κ : ℝ} (hκ : 0 < κ) {e : E → ℝ} (he : Measurable e)
    {A B : ℝ} (hconf : ∀ x, e x ≤ A + B * ‖x‖ - κ * ‖x‖ ^ 2) :
    Integrable fun x => Real.exp (e x) := by
  refine ((integrable_one_add_norm_pow_mul_exp (E := E) hκ B 0).const_mul
    (Real.exp A)).mono' he.exp.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, pow_zero, one_mul, ← Real.exp_add,
    Real.exp_le_exp, ← add_sub_assoc]
  exact hconf x

/-- Replica observables of polynomial growth are integrable for the replicated Gibbs measure of a
confined energy. -/
theorem integrable_pi_tilted_of_confining {κ : ℝ} (hκ : 0 < κ) {e : E → ℝ} (he : Measurable e)
    {A B : ℝ} (hconf : ∀ x, e x ≤ A + B * ‖x‖ - κ * ‖x‖ ^ 2) {Ψ : (R → E) → ℝ}
    (hΨ : Measurable Ψ) {C : ℝ} {m : ℕ} (hΨb : ∀ σ, |Ψ σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m) :
    Integrable Ψ (Measure.pi fun _ : R => volume.tilted e) := by
  have hi : Integrable (fun σ : R → E => Real.exp (∑ i, e (σ i)))
      (Measure.pi fun _ : R => volume) := by
    simp_rw [Real.exp_sum]
    exact Integrable.fintype_prod (f := fun _ : R => fun x : E => Real.exp (e x))
      fun _ => integrable_exp_of_confining hκ he hconf
  rw [pi_tilted_eq_tilted_pi, integrable_tilted_iff hi]
  simpa only [smul_eq_mul, mul_comm] using
    integrable_pi_mul_exp_of_confining hκ he hconf hΨ hΨb

/-- **Differentiation of a replica average under a confined energy.** Let the energies `e r` be
bounded by `A + B ‖x‖ - κ ‖x‖²` with `κ > 0`, uniformly for `r` near `t`, with derivative of
polynomial growth. For a replica observable `Ψ r` which, together with its derivative, grows at
most polynomially in each replica, the derivative of `r ↦ ⟨Ψ r⟩` is
`⟨∂ Ψ⟩ + ⟨Ψ X⟩ - ⟨Ψ⟩ ⟨X⟩`, where `X σ = ∑ i, ∂ e (σ i)`. -/
theorem hasDerivAt_integral_pi_tilted_of_confining {κ : ℝ} (hκ : 0 < κ) {e e' : ℝ → E → ℝ}
    {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t) (he : ∀ r ∈ s, Measurable (e r))
    (he' : Measurable (e' t)) {A B L : ℝ} {n : ℕ}
    (hconf : ∀ r ∈ s, ∀ x, e r x ≤ A + B * ‖x‖ - κ * ‖x‖ ^ 2)
    (he'b : ∀ r ∈ s, ∀ x, |e' r x| ≤ L * (1 + ‖x‖) ^ n)
    (hd : ∀ x, ∀ r ∈ s, HasDerivAt (fun q => e q x) (e' r x) r)
    {Ψ Ψ' : ℝ → (R → E) → ℝ} (hΨ : ∀ r ∈ s, Measurable (Ψ r)) (hΨ' : Measurable (Ψ' t))
    {C : ℝ} {m : ℕ} (hΨb : ∀ r ∈ s, ∀ σ, |Ψ r σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m)
    (hΨ'b : ∀ r ∈ s, ∀ σ, |Ψ' r σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m)
    (hΨd : ∀ σ, ∀ r ∈ s, HasDerivAt (fun q => Ψ q σ) (Ψ' r σ) r) :
    HasDerivAt (fun r => ∫ σ, Ψ r σ ∂(Measure.pi fun _ : R => volume.tilted (e r)))
      ((∫ σ, Ψ' t σ ∂(Measure.pi fun _ : R => volume.tilted (e t))) +
        ((∫ σ, Ψ t σ * (∑ i, e' t (σ i)) ∂(Measure.pi fun _ : R => volume.tilted (e t))) -
          (∫ σ, Ψ t σ ∂(Measure.pi fun _ : R => volume.tilted (e t))) *
            ∫ σ, (∑ i, e' t (σ i)) ∂(Measure.pi fun _ : R => volume.tilted (e t)))) t := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  -- it suffices to treat a nonnegative constant
  obtain ⟨C, hC, hΨb, hΨ'b⟩ : ∃ C : ℝ, 1 ≤ C ∧
      (∀ r ∈ s, ∀ σ, |Ψ r σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m) ∧
      ∀ r ∈ s, ∀ σ, |Ψ' r σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m :=
    ⟨max C 1, le_max_right _ _,
      fun r hr σ => (hΨb r hr σ).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)),
      fun r hr σ => (hΨ'b r hr σ).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hL : 0 ≤ L := by simpa using (abs_nonneg _).trans (he'b t ht 0)
  have hem : ∀ r ∈ s, Measurable fun σ : R → E => Real.exp (∑ i, e r (σ i)) :=
    fun r hr => (Finset.measurable_sum _ fun i _ =>
      (he r hr).comp (measurable_pi_apply i)).exp
  have hXm : Measurable fun σ : R → E => ∑ i, e' t (σ i) :=
    Finset.measurable_sum _ fun i _ => he'.comp (measurable_pi_apply i)
  -- the product of an observable with the replica sum of the energy derivatives
  have hPX : ∀ r ∈ s, ∀ Φ : (R → E) → ℝ, (∀ σ, |Φ σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m) → ∀ σ,
      |Φ σ * ∑ i, e' r (σ i)| ≤
        C * (L * Fintype.card R) * ∏ i, (1 + ‖σ i‖) ^ (m + n) := fun r hr Φ hΦ σ => by
    have hQ : (∏ i, (1 + ‖σ i‖) ^ m) * ∏ i, (1 + ‖σ i‖) ^ n =
        ∏ i, (1 + ‖σ i‖) ^ (m + n) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => (pow_add _ _ _).symm
    rw [abs_mul, ← hQ]
    refine (mul_le_mul (hΦ σ) (abs_sum_le_mul_prod_one_add_norm_pow (he'b r hr) σ)
      (abs_nonneg _) ((abs_nonneg _).trans (hΦ σ))).trans_eq ?_
    ring
  -- differentiate an unnormalized integral
  have hnum : ∀ (Φ Φ' : ℝ → (R → E) → ℝ), (∀ r ∈ s, Measurable (Φ r)) → Measurable (Φ' t) →
      (∀ r ∈ s, ∀ σ, |Φ r σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m) →
      (∀ r ∈ s, ∀ σ, |Φ' r σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m) →
      (∀ σ, ∀ r ∈ s, HasDerivAt (fun q => Φ q σ) (Φ' r σ) r) →
      HasDerivAt (fun r => ∫ σ, Φ r σ * Real.exp (∑ i, e r (σ i))
          ∂(Measure.pi fun _ : R => volume))
        (∫ σ, (Φ' t σ + Φ t σ * ∑ i, e' t (σ i)) * Real.exp (∑ i, e t (σ i))
          ∂(Measure.pi fun _ : R => volume)) t := by
    intro Φ Φ' hΦ hΦ' hΦb hΦ'b hΦd
    set K : ℝ := C * (1 + L * Fintype.card R) with hK
    have hbd : ∀ r ∈ s, ∀ σ : R → E, |Φ' r σ + Φ r σ * ∑ i, e' r (σ i)| ≤
        K * ∏ i, (1 + ‖σ i‖) ^ (m + n) := fun r hr σ => by
      have hP : ∏ i, (1 + ‖σ i‖) ^ m ≤ ∏ i, (1 + ‖σ i‖) ^ (m + n) :=
        Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i _ =>
          pow_le_pow_right₀ (le_add_of_nonneg_right (norm_nonneg _)) (Nat.le_add_right _ _)
      refine (abs_add_le _ _).trans ((add_le_add
        ((hΦ'b r hr σ).trans (mul_le_mul_of_nonneg_left hP hC0))
        (hPX r hr _ (hΦb r hr) σ)).trans_eq ?_)
      rw [hK]
      ring
    have hbi : Integrable (fun σ : R → E => ∏ i, Real.exp A *
        ((1 + ‖σ i‖) ^ (m + n) * Real.exp (B * ‖σ i‖ - κ * ‖σ i‖ ^ 2)))
        (Measure.pi fun _ : R => volume) :=
      Integrable.fintype_prod (f := fun _ : R => fun x : E =>
        Real.exp A * ((1 + ‖x‖) ^ (m + n) * Real.exp (B * ‖x‖ - κ * ‖x‖ ^ 2)))
        fun _ => (integrable_one_add_norm_pow_mul_exp hκ B (m + n)).const_mul _
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun r σ => Φ r σ * Real.exp (∑ i, e r (σ i)))
      (F' := fun r σ => (Φ' r σ + Φ r σ * ∑ i, e' r (σ i)) * Real.exp (∑ i, e r (σ i)))
      (bound := fun σ => K * ∏ i, Real.exp A *
        ((1 + ‖σ i‖) ^ (m + n) * Real.exp (B * ‖σ i‖ - κ * ‖σ i‖ ^ 2))) hs
      (Filter.mem_of_superset hs fun r hr => ((hΦ r hr).mul (hem r hr)).aestronglyMeasurable)
      (integrable_pi_mul_exp_of_confining hκ (he t ht) (hconf t ht) (hΦ t ht) (hΦb t ht))
      ((hΦ'.add ((hΦ t ht).mul hXm)).mul (hem t ht)).aestronglyMeasurable
      (ae_of_all _ fun σ r hr => ?_) (hbi.const_mul K)
      (ae_of_all _ fun σ r hr => ?_)).2
    · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      refine (mul_le_mul (hbd r hr σ) (exp_sum_le_prod_of_confining (hconf r hr) σ)
        (Real.exp_pos _).le ((abs_nonneg _).trans (hbd r hr σ))).trans_eq ?_
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      exact Finset.prod_congr rfl fun i _ => by ring
    · have h1 : HasDerivAt (fun q => ∑ i, e q (σ i)) (∑ i, e' r (σ i)) r :=
        HasDerivAt.fun_sum fun i _ => hd (σ i) r hr
      exact ((hΦd σ r hr).mul h1.exp).congr_deriv (by ring)
  have h1b : ∀ σ : R → E, |(1 : ℝ)| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m := fun σ => by
    rw [abs_one]
    exact one_le_mul_of_one_le_of_one_le hC (Finset.one_le_prod₀ (s := Finset.univ) fun i _ =>
      one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _)))
  have hN := hnum Ψ Ψ' hΨ hΨ' hΨb hΨ'b hΨd
  have hD := hnum (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => measurable_const) measurable_const
    (fun _ _ => h1b) (fun _ _ σ => by
      rw [abs_zero]
      exact mul_nonneg hC0 (by positivity))
    (fun σ r _ => hasDerivAt_const r 1)
  simp only [one_mul, zero_add] at hD
  have hZ : (0 : ℝ) < ∫ σ, Real.exp (∑ i, e t (σ i)) ∂(Measure.pi fun _ : R => volume) := by
    rw [integral_pi_exp_sum (μ := (volume : Measure E))]
    exact pow_pos (integral_exp_pos
      (integrable_exp_of_confining hκ (he t ht) (hconf t ht))) _
  have hI1 : Integrable (fun σ => Ψ' t σ * Real.exp (∑ i, e t (σ i)))
      (Measure.pi fun _ : R => volume) :=
    integrable_pi_mul_exp_of_confining hκ (he t ht) (hconf t ht) hΨ' (hΨ'b t ht)
  have hI2 : Integrable (fun σ => (Ψ t σ * ∑ i, e' t (σ i)) * Real.exp (∑ i, e t (σ i)))
      (Measure.pi fun _ : R => volume) :=
    integrable_pi_mul_exp_of_confining hκ (he t ht) (hconf t ht) ((hΨ t ht).mul hXm)
      (hPX t ht _ (hΨb t ht))
  have hsplit := integral_add hI1 hI2
  simp only [← add_mul] at hsplit
  rw [hsplit] at hN
  simp_rw [pi_tilted_eq_tilted_pi, integral_tilted_eq_div]
  refine (hN.div hD hZ.ne').congr_deriv ?_
  have := hZ.ne'
  field_simp
  ring

/-- The derivative of `hasDerivAt_integral_pi_tilted_of_confining` written with the replica
difference: `⟨∂ Ψ⟩ + ∑ i, ⟨Ψ ∂ e (σ i)⟩ - |R| ⟨Ψ ∂ e (σ_*)⟩`, with one fresh replica `σ_*`. -/
theorem hasDerivAt_integral_pi_tilted_of_confining_replicaDiff {κ : ℝ} (hκ : 0 < κ)
    {e e' : ℝ → E → ℝ} {t : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t) (he : ∀ r ∈ s, Measurable (e r))
    (he' : Measurable (e' t)) {A B L : ℝ} {n : ℕ}
    (hconf : ∀ r ∈ s, ∀ x, e r x ≤ A + B * ‖x‖ - κ * ‖x‖ ^ 2)
    (he'b : ∀ r ∈ s, ∀ x, |e' r x| ≤ L * (1 + ‖x‖) ^ n)
    (hd : ∀ x, ∀ r ∈ s, HasDerivAt (fun q => e q x) (e' r x) r)
    {Ψ Ψ' : ℝ → (R → E) → ℝ} (hΨ : ∀ r ∈ s, Measurable (Ψ r)) (hΨ' : Measurable (Ψ' t))
    {C : ℝ} {m : ℕ} (hΨb : ∀ r ∈ s, ∀ σ, |Ψ r σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m)
    (hΨ'b : ∀ r ∈ s, ∀ σ, |Ψ' r σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m)
    (hΨd : ∀ σ, ∀ r ∈ s, HasDerivAt (fun q => Ψ q σ) (Ψ' r σ) r) :
    HasDerivAt (fun r => ∫ σ, Ψ r σ ∂(Measure.pi fun _ : R => volume.tilted (e r)))
      ((∫ σ, Ψ' t σ ∂(Measure.pi fun _ : R => volume.tilted (e t))) +
        replicaDiff (volume.tilted (e t)) (Ψ t) (e' t)) t := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  refine (hasDerivAt_integral_pi_tilted_of_confining hκ hs he he' hconf he'b hd hΨ hΨ' hΨb
    hΨ'b hΨd).congr_deriv ?_
  have : IsProbabilityMeasure (volume.tilted (e t)) :=
    isProbabilityMeasure_tilted (integrable_exp_of_confining hκ (he t ht) (hconf t ht))
  have hh : Integrable (e' t) (volume.tilted (e t)) := by
    have h := integrable_pi_tilted_of_confining (R := Unit) hκ (he t ht) (hconf t ht)
      (Ψ := fun σ => e' t (σ ())) (he'.comp (measurable_pi_apply _)) (C := L) (m := n)
      fun σ => by simpa using he'b t ht (σ ())
    exact (measurePreserving_eval (fun _ : Unit => volume.tilted (e t)) ()).integrable_comp
      he'.aestronglyMeasurable |>.1 h
  have hFI : ∀ i : R, Integrable (fun σ => Ψ t σ * e' t (σ i))
      (Measure.pi fun _ : R => volume.tilted (e t)) := fun i => by
    refine integrable_pi_tilted_of_confining hκ (he t ht) (hconf t ht)
      (C := C * L) (m := m + n) ((hΨ t ht).mul (he'.comp (measurable_pi_apply i))) fun σ => ?_
    have hL : 0 ≤ L := by simpa using (abs_nonneg _).trans (he'b t ht 0)
    rw [abs_mul]
    refine (mul_le_mul (hΨb t ht σ) ((he'b t ht (σ i)).trans
      (mul_le_mul_of_nonneg_left (one_add_norm_pow_le_prod σ n i) hL)) (abs_nonneg _)
      ((abs_nonneg _).trans (hΨb t ht σ))).trans_eq ?_
    have hQ : ∏ j, (1 + ‖σ j‖) ^ (m + n) =
        (∏ j, (1 + ‖σ j‖) ^ m) * ∏ j, (1 + ‖σ j‖) ^ n := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ => pow_add _ _ _
    rw [hQ]
    ring
  rw [integral_pi_cov_sum_eq_sum_sub_fresh_of_integrable _ _
    (hΨ t ht).aestronglyMeasurable _ hh hFI]

end MeasureTheory
