/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaConfined
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaPairBridge

/-!
# Replica differences under a confined energy

For energies bounded by `A + B ‖x‖ - κ ‖x‖²` on a finite-dimensional real normed space with an
additive Haar measure `μ`, and observables of polynomial growth, this file controls the replica
difference and the two-fresh-replica average, and differentiates a replica difference along a
parameter of the energy.

## Main statements

* `MeasureTheory.replicaDiff_finsetSum_of_confining`: additivity in the one-replica observable.
* `MeasureTheory.abs_replicaDiff_le_of_confining`,
  `MeasureTheory.abs_replicaPairAverage_le_of_confining`: bounds by one moment of the Gibbs
  measure.
* `MeasureTheory.hasDerivAt_replicaDiff_tilted_of_confining`: the derivative of a replica
  difference whose energy and observable move together.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {R : Type*} [Fintype R]

/-- The products entering the replica difference of polynomially growing observables are
integrable for a confined energy. -/
theorem integrable_replicaDiff_term_of_confining {κ : ℝ} (hκ : 0 < κ) {e : E → ℝ}
    (he : Measurable e) {A B : ℝ} (hconf : ∀ x, e x ≤ A + B * ‖x‖ - κ * ‖x‖ ^ 2)
    {F : (R → E) → ℝ} (hF : Measurable F) {C : ℝ} {m : ℕ}
    (hFb : ∀ σ, |F σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m) {f : E → ℝ} (hf : Measurable f) {L : ℝ}
    {n : ℕ} (hfb : ∀ x, |f x| ≤ L * (1 + ‖x‖) ^ n) (o : Option R) :
    Integrable (fun σ : Option R → E => F (fun j => σ (some j)) * f (σ o))
      (Measure.pi fun _ : Option R => μ.tilted e) :=
  integrable_pi_tilted_of_confining hκ he hconf
    ((hF.comp (measurable_pi_iff.2 fun j => measurable_pi_apply (some j))).mul
      (hf.comp (measurable_pi_apply o))).aestronglyMeasurable
    (fun σ => abs_mul_le_mul_prod_one_add_norm_pow (abs_comp_some_le_prod hFb σ)
      (abs_comp_eval_le_prod hfb σ o))

/-- The replica difference is additive in the one-replica observable, for polynomial growth and
a confined energy. -/
theorem replicaDiff_add_of_confining {κ : ℝ} (hκ : 0 < κ) {e : E → ℝ} (he : Measurable e)
    {A B : ℝ} (hconf : ∀ x, e x ≤ A + B * ‖x‖ - κ * ‖x‖ ^ 2) {F : (R → E) → ℝ}
    (hF : Measurable F) {C : ℝ} {m : ℕ} (hFb : ∀ σ, |F σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m)
    {f g : E → ℝ} (hf : Measurable f) (hg : Measurable g) {L L' : ℝ} {n n' : ℕ}
    (hfb : ∀ x, |f x| ≤ L * (1 + ‖x‖) ^ n) (hgb : ∀ x, |g x| ≤ L' * (1 + ‖x‖) ^ n') :
    replicaDiff (μ.tilted e) F (fun x => f x + g x) =
      replicaDiff (μ.tilted e) F f + replicaDiff (μ.tilted e) F g := by
  have hfi := integrable_replicaDiff_term_of_confining (μ := μ) hκ he hconf hF hFb hf hfb
  have hgi := integrable_replicaDiff_term_of_confining (μ := μ) hκ he hconf hF hFb hg hgb
  simp only [replicaDiff_eq, mul_add]
  simp only [fun o => integral_add (hfi o) (hgi o), Finset.sum_add_distrib]
  ring

/-- The replica difference is additive over a finite sum of one-replica observables, for
polynomial growth and a confined energy. -/
theorem replicaDiff_finsetSum_of_confining {κ : ℝ} (hκ : 0 < κ) {e : E → ℝ} (he : Measurable e)
    {A B : ℝ} (hconf : ∀ x, e x ≤ A + B * ‖x‖ - κ * ‖x‖ ^ 2) {F : (R → E) → ℝ}
    (hF : Measurable F) {C : ℝ} {m : ℕ} (hFb : ∀ σ, |F σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m)
    {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} (hf : ∀ k, Measurable (f k)) {L : ι → ℝ} {n : ℕ}
    (hfb : ∀ k x, |f k x| ≤ L k * (1 + ‖x‖) ^ n) :
    replicaDiff (μ.tilted e) F (fun x => ∑ k ∈ s, f k x) =
      ∑ k ∈ s, replicaDiff (μ.tilted e) F (f k) := by
  have hi := fun k => integrable_replicaDiff_term_of_confining (μ := μ) hκ he hconf hF hFb (hf k)
    (hfb k)
  simp only [replicaDiff_eq, Finset.mul_sum, fun o => integral_finsetSum s fun k _ => hi k o,
    Finset.sum_sub_distrib]
  rw [Finset.sum_comm]

/-- A replica observable of polynomial growth is bounded in mean by a power of the corresponding
one-replica moment. No measurability of the observable is needed. -/
theorem abs_integral_pi_tilted_le_of_confining {κ : ℝ} (hκ : 0 < κ) {e : E → ℝ}
    (he : Measurable e) {A B : ℝ} (hconf : ∀ x, e x ≤ A + B * ‖x‖ - κ * ‖x‖ ^ 2)
    {Ψ : (R → E) → ℝ} {C : ℝ} {m : ℕ} (hΨb : ∀ σ, |Ψ σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m) :
    |∫ σ, Ψ σ ∂(Measure.pi fun _ : R => μ.tilted e)| ≤
      C * (∫ x, (1 + ‖x‖) ^ m ∂(μ.tilted e)) ^ Fintype.card R := by
  have : IsProbabilityMeasure (μ.tilted e) :=
    isProbabilityMeasure_tilted (integrable_exp_of_confining (μ := μ) hκ he hconf)
  have hprod : Integrable (fun σ : R → E => ∏ i, (1 + ‖σ i‖) ^ m)
      (Measure.pi fun _ : R => μ.tilted e) :=
    integrable_pi_tilted_of_confining hκ he hconf
      (Finset.measurable_prod _ fun i _ =>
        ((measurable_pi_apply i).norm.const_add 1).pow_const m).aestronglyMeasurable
      (C := 1) (m := m) fun σ => by
      rw [one_mul, Real.norm_of_nonneg (Finset.prod_nonneg fun _ _ => by positivity)]
  have hpow := integral_fintype_prod_eq_pow (ι := R) (μ := μ.tilted e)
    (fun x : E => (1 + ‖x‖) ^ m)
  rw [← hpow, ← integral_const_mul, ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le (hprod.const_mul C) (ae_of_all _ fun σ => by
    rw [Real.norm_eq_abs]
    exact hΨb σ)

/-- The replica difference of polynomially growing observables is controlled by one moment of
the Gibbs measure. -/
theorem abs_replicaDiff_le_of_confining {κ : ℝ} (hκ : 0 < κ) {e : E → ℝ}
    (he : Measurable e) {A B : ℝ} (hconf : ∀ x, e x ≤ A + B * ‖x‖ - κ * ‖x‖ ^ 2)
    {F : (R → E) → ℝ} {C : ℝ} {m : ℕ} (hFb : ∀ σ, |F σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m)
    {f : E → ℝ} {L : ℝ} {n : ℕ} (hfb : ∀ x, |f x| ≤ L * (1 + ‖x‖) ^ n) :
    |replicaDiff (μ.tilted e) F f| ≤ 2 * Fintype.card R * (C * L *
      (∫ x, (1 + ‖x‖) ^ (m + n) ∂(μ.tilted e)) ^ (Fintype.card R + 1)) := by
  set M : ℝ := C * L * (∫ x, (1 + ‖x‖) ^ (m + n) ∂(μ.tilted e)) ^ (Fintype.card R + 1)
    with hM
  have hterm : ∀ o : Option R, |∫ σ, F (fun j => σ (some j)) * f (σ o)
      ∂(Measure.pi fun _ : Option R => μ.tilted e)| ≤ M := fun o => by
    have h := abs_integral_pi_tilted_le_of_confining (μ := μ) (R := Option R) hκ he hconf
      (Ψ := fun σ => F (fun j => σ (some j)) * f (σ o))
      (fun σ => abs_mul_le_mul_prod_one_add_norm_pow (abs_comp_some_le_prod hFb σ)
        (abs_comp_eval_le_prod hfb σ o))
    rwa [Fintype.card_option] at h
  rw [replicaDiff_eq]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, Nat.abs_cast, mul_comm 2, mul_assoc, two_mul]
  rw [mul_add]
  refine add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans ?_)
    (mul_le_mul_of_nonneg_left (hterm none) (Nat.cast_nonneg _))
  exact (Finset.sum_le_sum fun i _ => hterm (some i)).trans_eq (by simp)

/-- The two-fresh-replica average of a product kernel of polynomially growing observables is
controlled by one moment of the Gibbs measure. -/
theorem abs_replicaPairAverage_le_of_confining [LinearOrder R] {κ : ℝ} (hκ : 0 < κ)
    {e : E → ℝ} (he : Measurable e) {A B : ℝ}
    (hconf : ∀ x, e x ≤ A + B * ‖x‖ - κ * ‖x‖ ^ 2) {F : (R → E) → ℝ}
    {C : ℝ} {m : ℕ} (hFb : ∀ σ, |F σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m) {f : E → ℝ}
    {L : ℝ} {n : ℕ} (hfb : ∀ x, |f x| ≤ L * (1 + ‖x‖) ^ n) :
    |replicaPairAverage (μ.tilted e) F (fun a b => f a * f b)| ≤
      3 * (Fintype.card R + 1) ^ 2 * (C * L ^ 2 *
        (∫ x, (1 + ‖x‖) ^ (m + (n + n)) ∂(μ.tilted e)) ^ (Fintype.card R + 2)) := by
  have hL : 0 ≤ L := by simpa using (abs_nonneg _).trans (hfb 0)
  set k : ℝ := (Fintype.card R : ℝ) with hk
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  set G : (Option (Option R) → E) → ℝ := fun τ => F fun r => τ (some (some r)) with hG
  have hGb : ∀ τ, |G τ| ≤ C * ∏ o, (1 + ‖τ o‖) ^ m := fun τ =>
    abs_comp_some_le_prod (R := R) (F := F) hFb (fun o => τ (some o)) |>.trans (by
      have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hFb 0))
        (Finset.prod_pos fun _ _ => by positivity)
      refine mul_le_mul_of_nonneg_left ?_ hC
      rw [Fintype.prod_option (fun o : Option (Option R) => (1 + ‖τ o‖) ^ m)]
      exact le_mul_of_one_le_left (Finset.prod_nonneg fun _ _ => by positivity)
        (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _))))
  -- each value of the kernel grows polynomially
  have hff : ∀ (τ : Option (Option R) → E) (a b : Option (Option R)),
      |f (τ a) * f (τ b)| ≤ L ^ 2 * ∏ o, (1 + ‖τ o‖) ^ (n + n) := fun τ a b => by
    refine (abs_mul_le_mul_prod_one_add_norm_pow (abs_comp_eval_le_prod hfb τ a)
      (abs_comp_eval_le_prod hfb τ b)).trans_eq ?_
    rw [sq]
  set W : ℝ := L ^ 2 with hW
  have hcomb : ∀ τ : Option (Option R) → E,
      |replicaPairCombination (fun a b => f a * f b) τ| ≤
        3 * (k + 1) ^ 2 * (W * ∏ o, (1 + ‖τ o‖) ^ (n + n)) := fun τ => by
    set P : ℝ := W * ∏ o, (1 + ‖τ o‖) ^ (n + n) with hP
    have hP0 : 0 ≤ P := (abs_nonneg _).trans (hff τ none none)
    have h1 : |∑ p : R × R with p.1 < p.2,
        f (τ (some (some p.1))) * f (τ (some (some p.2)))| ≤ k ^ 2 * P := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans
        ((Finset.sum_le_sum fun p _ => hff τ _ _).trans ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ hP0
      rw [hk, sq, ← Nat.cast_mul, ← Fintype.card_prod]
      exact_mod_cast Finset.card_filter_le _ _
    have h2 : |k * ∑ r : R, f (τ (some (some r))) * f (τ (some none))| ≤ k ^ 2 * P := by
      rw [abs_mul, abs_of_nonneg hk0, sq, mul_assoc]
      refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
        ((Finset.sum_le_sum fun r _ => hff τ _ _).trans_eq ?_)) hk0
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have h3 : |k * (k + 1) / 2 * (f (τ (some none)) * f (τ none))| ≤ (k + 1) ^ 2 * P := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul (by nlinarith) (hff τ _ _) (abs_nonneg _) (by positivity)
    have h4 : k ^ 2 * P ≤ (k + 1) ^ 2 * P :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hk0 (by linarith) 2) hP0
    rw [replicaPairCombination_eq]
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add ((abs_sub _ _).trans (add_le_add h1 h2)) h3).trans ?_
    linarith
  have hmain := abs_integral_pi_tilted_le_of_confining (μ := μ) (R := Option (Option R)) hκ he hconf
    (Ψ := fun τ => G τ * replicaPairCombination (fun a b => f a * f b) τ)
    (C := 3 * (k + 1) ^ 2 * (C * W)) (m := m + (n + n)) fun τ => by
      refine (abs_mul_le_mul_prod_one_add_norm_pow (hGb τ)
        ((hcomb τ).trans_eq (mul_assoc _ _ _).symm)).trans_eq ?_
      ring
  rw [Fintype.card_option, Fintype.card_option] at hmain
  rw [replicaPairAverage_eq]
  refine hmain.trans_eq ?_
  ring

/-- **Derivative of a replica difference along a confined energy.** Suppose the energy and the
one-replica observable move with `∂ e = c h` and `∂ h = c h₂`, everything growing polynomially.
Then `∂ replicaDiff F h = c (replicaDiff F (h₂ + h²) + 2 replicaPairAverage F (h ⊗ h))`. -/
theorem hasDerivAt_replicaDiff_tilted_of_confining [LinearOrder R] {κ : ℝ} (hκ : 0 < κ)
    {e h h₂ : ℝ → E → ℝ} {t c : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 t) (he : ∀ r ∈ s, Measurable (e r))
    (hh : ∀ r ∈ s, Measurable (h r)) (hh₂ : Measurable (h₂ t)) {A B L : ℝ} {n : ℕ}
    (hconf : ∀ r ∈ s, ∀ x, e r x ≤ A + B * ‖x‖ - κ * ‖x‖ ^ 2)
    (hhb : ∀ r ∈ s, ∀ x, |h r x| ≤ L * (1 + ‖x‖) ^ n)
    (hh₂b : ∀ r ∈ s, ∀ x, |h₂ r x| ≤ L * (1 + ‖x‖) ^ n)
    (hed : ∀ x, ∀ r ∈ s, HasDerivAt (fun q => e q x) (c * h r x) r)
    (hhd : ∀ x, ∀ r ∈ s, HasDerivAt (fun q => h q x) (c * h₂ r x) r)
    {F : (R → E) → ℝ} (hF : Measurable F) {C : ℝ} {m : ℕ}
    (hFb : ∀ σ, |F σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m) :
    HasDerivAt (fun r => replicaDiff (μ.tilted (e r)) F (h r))
      (c * (replicaDiff (μ.tilted (e t)) F (fun x => h₂ t x + h t x ^ 2) +
        2 * replicaPairAverage (μ.tilted (e t)) F (fun a b => h t a * h t b))) t := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  set ν := μ.tilted (e t) with hν
  have : IsProbabilityMeasure ν :=
    isProbabilityMeasure_tilted (integrable_exp_of_confining (μ := μ) hκ (he t ht) (hconf t ht))
  have hL : 0 ≤ L := by simpa using (abs_nonneg _).trans (hhb t ht 0)
  set G : (Option R → E) → ℝ := fun σ => F fun j => σ (some j) with hG
  have hGm : Measurable G := hF.comp (measurable_pi_iff.2 fun j => measurable_pi_apply (some j))
  -- each of the `|R| + 1` terms is a moving replica observable
  have hterm : ∀ o : Option R, HasDerivAt
      (fun r => ∫ σ, G σ * h r (σ o) ∂(Measure.pi fun _ : Option R => μ.tilted (e r)))
      (c * (∫ σ, G σ * h₂ t (σ o) ∂(Measure.pi fun _ : Option R => ν)) +
        c * replicaDiff ν (fun σ => G σ * h t (σ o)) (h t)) t := fun o => by
    have hmain := hasDerivAt_integral_pi_tilted_of_confining_replicaDiff (μ := μ)
      (R := Option R) hκ hs
      (e := e) (e' := fun r x => c * h r x) he ((hh t ht).const_mul c) hconf
      (L := |c| * L) (n := n) (fun r hr x => by
        rw [abs_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hhb r hr x) (abs_nonneg c))
      hed (Ψ := fun r σ => G σ * h r (σ o)) (Ψ' := fun r σ => G σ * (c * h₂ r (σ o)))
      (fun r hr => hGm.mul ((hh r hr).comp (measurable_pi_apply o)))
      (hGm.mul ((hh₂.comp (measurable_pi_apply o)).const_mul c))
      (C := max (C * L) (C * (|c| * L))) (m := m + n)
      (fun r hr σ => (abs_mul_le_mul_prod_one_add_norm_pow (abs_comp_some_le_prod hFb σ)
        (abs_comp_eval_le_prod (hhb r hr) σ o)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
      (fun r hr σ => (abs_mul_le_mul_prod_one_add_norm_pow (abs_comp_some_le_prod hFb σ)
        (abs_comp_eval_le_prod (f := fun x => c * h₂ r x) (L := |c| * L) (fun x => by
          rw [abs_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_left (hh₂b r hr x) (abs_nonneg c)) σ o)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
      (fun σ r hr => (hhd (σ o) r hr).const_mul (G σ))
    refine hmain.congr_deriv ?_
    rw [← hν, replicaDiff_const_mul]
    congr 1
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun σ => by ring)
  have hsum : HasDerivAt (fun r => replicaDiff (μ.tilted (e r)) F (h r))
      ((∑ i : R, (c * (∫ σ, G σ * h₂ t (σ (some i)) ∂(Measure.pi fun _ : Option R => ν)) +
          c * replicaDiff ν (fun σ => G σ * h t (σ (some i))) (h t))) -
        (Fintype.card R : ℝ) * (c * (∫ σ, G σ * h₂ t (σ none)
            ∂(Measure.pi fun _ : Option R => ν)) +
          c * replicaDiff ν (fun σ => G σ * h t (σ none)) (h t))) t :=
    (HasDerivAt.fun_sum fun i _ => hterm (some i)).sub ((hterm none).const_mul _)
  refine hsum.congr_deriv ?_
  -- recognise the two replica differences
  have hpair := replicaDiffWith_replicaDiff_eq_of_memLp ν F hF (fun p =>
      memLp_pi_tilted_of_confining hκ (he t ht) (hconf t ht) hF.aestronglyMeasurable hFb p)
    (h t) (hh t ht) (fun p => memLp_of_poly_bound_of_confining hκ (he t ht) (hconf t ht)
      (hh t ht).aestronglyMeasurable (hhb t ht) p) 1
  simp only [one_mul, mul_one] at hpair
  have hh2sq : ∀ x, |h t x ^ 2| ≤ L ^ 2 * (1 + ‖x‖) ^ (n * 2) := fun x => by
    rw [abs_pow, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hhb t ht x) 2
  rw [replicaDiff_add_of_confining hκ (he t ht) (hconf t ht) hF hFb (f := h₂ t)
    (g := fun x => h t x ^ 2) hh₂ ((hh t ht).pow_const 2) (hh₂b t ht) hh2sq]
  have hsq : replicaDiff ν F (fun x => h t x ^ 2) = replicaDiff ν F (fun a => h t a * h t a) := by
    simp only [sq]
  rw [← hν, hsq]
  have hD2 : replicaDiff ν F (h₂ t) =
      (∑ i : R, ∫ σ, G σ * h₂ t (σ (some i)) ∂(Measure.pi fun _ : Option R => ν)) -
        (Fintype.card R : ℝ) * ∫ σ, G σ * h₂ t (σ none)
          ∂(Measure.pi fun _ : Option R => ν) := replicaDiff_eq ν F (h₂ t)
  have hW : replicaDiffWith (fun G => replicaDiff ν G (h t)) F (h t) =
      (∑ i : R, replicaDiff ν (fun σ => G σ * h t (σ (some i))) (h t)) -
        (Fintype.card R : ℝ) * replicaDiff ν (fun σ => G σ * h t (σ none)) (h t) := rfl
  rw [hW] at hpair
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  linear_combination c * hpair - c * hD2

end MeasureTheory
