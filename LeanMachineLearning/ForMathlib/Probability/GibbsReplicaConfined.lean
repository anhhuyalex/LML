/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Distributions.Gaussian.QuadraticTilt
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct

/-!
# Replica averages under a confined energy

The space is a finite-dimensional real normed space with an additive Haar measure `μ`. The energies
are bounded by `A + B ‖x‖ - κ ‖x‖²` with `κ > 0`, so the Gibbs densities relative to `μ` have
Gaussian tails. Observables and energy derivatives may grow polynomially
in each replica, which covers the unbounded spins of continuous spin glass models.

## Main statements

* `MeasureTheory.memLp_of_poly_bound_of_confining`,
  `MeasureTheory.memLp_pi_tilted_of_confining`: observables of polynomial growth have finite
  moments of every order, for one replica and for finitely many.
* `MeasureTheory.exists_integral_one_add_norm_pow_tilted_le`: a moment bound which is polynomial
  in the linear growth of the energy and in its lower bound on the unit ball.
* `MeasureTheory.integrable_pi_mul_exp_of_confining`: integrability of replica observables of
  polynomial growth against the product weight.
* `MeasureTheory.hasDerivAt_integral_pi_tilted_of_confining`: the derivative of a replica average
  whose energy and observable depend on a parameter, and its replica-difference form
  `MeasureTheory.hasDerivAt_integral_pi_tilted_of_confining_replicaDiff`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

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

/-- A one-replica observable of polynomial growth, evaluated at one replica, grows polynomially
in the replicas. -/
theorem abs_comp_eval_le_prod {f : E → ℝ} {L : ℝ} {n : ℕ}
    (hf : ∀ x, |f x| ≤ L * (1 + ‖x‖) ^ n) (σ : R → E) (i : R) :
    |f (σ i)| ≤ L * ∏ j, (1 + ‖σ j‖) ^ n := by
  have hL : 0 ≤ L := by simpa using (abs_nonneg _).trans (hf 0)
  exact (hf (σ i)).trans (mul_le_mul_of_nonneg_left (one_add_norm_pow_le_prod σ n i) hL)

/-- The growth bounds of two replica observables multiply. -/
theorem abs_mul_le_mul_prod_one_add_norm_pow {σ : R → E} {a b C D : ℝ} {m n : ℕ}
    (ha : |a| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m) (hb : |b| ≤ D * ∏ i, (1 + ‖σ i‖) ^ n) :
    |a * b| ≤ C * D * ∏ i, (1 + ‖σ i‖) ^ (m + n) := by
  simp only [pow_add, Finset.prod_mul_distrib]
  rw [abs_mul, mul_mul_mul_comm]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- A replica observable of polynomial growth times the product weight of confined energies is
dominated by a product of one-replica functions. -/
theorem abs_mul_exp_sum_le_of_confining {κ A B : ℝ} {e : E → ℝ}
    (hconf : ∀ x, e x ≤ A + B * ‖x‖ - κ * ‖x‖ ^ 2) {σ : R → E} {a C : ℝ} {m : ℕ}
    (ha : |a| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m) :
    |a * Real.exp (∑ i, e (σ i))| ≤
      C * ∏ i, Real.exp A * ((1 + ‖σ i‖) ^ m * Real.exp (B * ‖σ i‖ - κ * ‖σ i‖ ^ 2)) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  refine (mul_le_mul ha (exp_sum_le_prod_of_confining hconf σ) (Real.exp_pos _).le
    ((abs_nonneg _).trans ha)).trans_eq ?_
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  exact congrArg _ (Finset.prod_congr rfl fun i _ => by ring)

/-- A replica observable of polynomial growth, read on distinct replicas of a larger system
through a norm-nonincreasing map, keeps its growth bound. -/
theorem abs_comp_le_prod_of_injective {E' R' : Type*} [SeminormedAddCommGroup E'] [Fintype R']
    {F : (R → E) → ℝ} {C : ℝ} {m : ℕ} (hF : ∀ σ, |F σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m)
    {g : E' → E} (hg : ∀ y, ‖g y‖ ≤ ‖y‖) {e : R → R'} (he : Function.Injective e) (σ : R' → E') :
    |F fun i => g (σ (e i))| ≤ |C| * ∏ j, (1 + ‖σ j‖) ^ m := by
  classical
  refine (hF _).trans (mul_le_mul (le_abs_self C) ?_
    (Finset.prod_nonneg fun _ _ => by positivity) (abs_nonneg C))
  exact Finset.prod_le_prod_of_injOn₀ e he.injOn (Finset.subset_univ _)
    (fun i _ => pow_le_pow_left₀ (by positivity) (add_le_add_right (hg _) 1) _)
    (fun _ _ => by positivity) fun _ _ _ => one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _))

/-- A replica observable pulled back along `some` to `|R| + 1` replicas keeps its growth bound. -/
theorem abs_comp_some_le_prod {F : (R → E) → ℝ} {C : ℝ} {m : ℕ}
    (hF : ∀ σ, |F σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m) (σ : Option R → E) :
    |F fun j => σ (some j)| ≤ C * ∏ o, (1 + ‖σ o‖) ^ m := by
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hF 0))
    (Finset.prod_pos fun _ _ => by positivity)
  simpa only [abs_of_nonneg hC, id] using
    abs_comp_le_prod_of_injective hF (g := id) (fun _ => le_rfl) (Option.some_injective R) σ

end ReplicaSum

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {R : Type*} [Fintype R]

/-- Replica observables of polynomial growth are integrable against the confined product
weight. -/
theorem integrable_pi_mul_exp_of_confining {κ : ℝ} (hκ : 0 < κ) {e : E → ℝ} (he : Measurable e)
    {A B : ℝ} (hconf : ∀ x, e x ≤ A + B * ‖x‖ - κ * ‖x‖ ^ 2) {Ψ : (R → E) → ℝ}
    (hΨ : Measurable Ψ) {C : ℝ} {m : ℕ} (hΨb : ∀ σ, |Ψ σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m) :
    Integrable (fun σ => Ψ σ * Real.exp (∑ i, e (σ i))) (Measure.pi fun _ : R => μ) := by
  have hprod : Integrable (fun σ : R → E => ∏ i,
      Real.exp A * ((1 + ‖σ i‖) ^ m * Real.exp (B * ‖σ i‖ - κ * ‖σ i‖ ^ 2)))
      (Measure.pi fun _ : R => μ) :=
    Integrable.fintype_prod (f := fun _ : R => fun x : E =>
      Real.exp A * ((1 + ‖x‖) ^ m * Real.exp (B * ‖x‖ - κ * ‖x‖ ^ 2)))
      fun _ => (integrable_one_add_norm_pow_mul_exp (μ := μ) hκ B m).const_mul _
  exact (hprod.const_mul C).mono' (hΨ.mul (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun σ => abs_mul_exp_sum_le_of_confining hconf (hΨb σ))

/-- The Gibbs weight of a confined energy is integrable. -/
theorem integrable_exp_of_confining {κ : ℝ} (hκ : 0 < κ) {e : E → ℝ} (he : Measurable e)
    {A B : ℝ} (hconf : ∀ x, e x ≤ A + B * ‖x‖ - κ * ‖x‖ ^ 2) :
    Integrable (fun x => Real.exp (e x)) μ := by
  refine ((integrable_one_add_norm_pow_mul_exp (μ := μ) hκ B 0).const_mul
    (Real.exp A)).mono' he.exp.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, pow_zero, one_mul, ← Real.exp_add,
    Real.exp_le_exp, ← add_sub_assoc]
  exact hconf x

/-- Under the Gibbs measure of a confined energy, observables of polynomial growth have finite
moments of every order. -/
theorem memLp_of_poly_bound_of_confining {F : Type*} [NormedAddCommGroup F] {κ : ℝ} (hκ : 0 < κ)
    {e : E → ℝ} (he : Measurable e) {A B : ℝ}
    (hconf : ∀ x, e x ≤ A + B * ‖x‖ - κ * ‖x‖ ^ 2) {f : E → F}
    (hf : AEStronglyMeasurable f μ) {C : ℝ} {m : ℕ} (hfb : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ m)
    (p : ℝ≥0) : MemLp f p (μ.tilted e) := by
  have hexp := integrable_exp_of_confining (μ := μ) hκ he hconf
  have : IsProbabilityMeasure (μ.tilted e) := isProbabilityMeasure_tilted hexp
  have hfm : AEStronglyMeasurable f (μ.tilted e) :=
    hf.mono_ac (tilted_absolutelyContinuous _ _)
  obtain ⟨k, hk⟩ := exists_nat_ge p
  have hpk : (p : ℝ≥0∞) ≤ ((k + 1 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hk.trans (Nat.cast_le.2 k.le_succ)
  refine MemLp.mono_exponent ?_ hpk
  refine (integrable_norm_rpow_iff hfm (by simp) (ENNReal.natCast_ne_top _)).1 ?_
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast]
  rw [integrable_tilted_iff hexp]
  refine ((integrable_one_add_norm_pow_mul_exp (μ := μ) hκ B (m * (k + 1))).const_mul
    (Real.exp A * C ^ (k + 1))).mono' (he.exp.aestronglyMeasurable.smul (hf.norm.pow _))
    (ae_of_all _ fun x => ?_)
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, norm_pow, norm_norm]
  have h1 : Real.exp (e x) ≤ Real.exp A * Real.exp (B * ‖x‖ - κ * ‖x‖ ^ 2) := by
    rw [← Real.exp_add, Real.exp_le_exp, ← add_sub_assoc]
    exact hconf x
  refine (mul_le_mul h1 (pow_le_pow_left₀ (norm_nonneg _) (hfb x) (k + 1)) (by positivity)
    (by positivity)).trans_eq ?_
  rw [mul_pow, ← pow_mul]
  ring

/-- **Polynomial moments of a confined Gibbs measure.** For `κ > 0` and `k : ℕ` there is a
constant `K` such that, for every energy with `e x ≤ B ‖x‖ - κ ‖x‖²` everywhere and `-c ≤ e x`
on the unit ball, the Gibbs measure of `e` satisfies `⟨(1 + ‖x‖)^k⟩ ≤ K (1 + B + c)^k`. The
bound is polynomial in `B` and `c`, which keeps it integrable against Gaussian disorder. -/
theorem exists_integral_one_add_norm_pow_tilted_le (μ : Measure E) [μ.IsAddHaarMeasure] {κ : ℝ}
    (hκ : 0 < κ) (k : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (e : E → ℝ), Measurable e → ∀ B c : ℝ, 0 ≤ B → 0 ≤ c →
      (∀ x, e x ≤ B * ‖x‖ - κ * ‖x‖ ^ 2) → (∀ x, ‖x‖ ≤ 1 → -c ≤ e x) →
      ∫ x, (1 + ‖x‖) ^ k ∂(μ.tilted e) ≤ K * (1 + B + c) ^ k := by
  set V : ℝ := μ.real (Metric.closedBall (0 : E) 1) with hV
  have hV0 : 0 < V := ENNReal.toReal_pos
    (Metric.measure_closedBall_pos μ (0 : E) one_pos).ne' measure_closedBall_lt_top.ne
  set I : ℝ := ∫ x : E, (1 + ‖x‖) ^ k * Real.exp (0 * ‖x‖ - κ / 4 * ‖x‖ ^ 2) ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => by positivity
  set M : ℝ := 3 + 3 / κ with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨M ^ k + I / V, by positivity, fun e he B c hB hc hup hlow => ?_⟩
  have hconf : ∀ x, e x ≤ 0 + B * ‖x‖ - κ * ‖x‖ ^ 2 := by simpa using hup
  have hZi := integrable_exp_of_confining (μ := μ) hκ he hconf
  set Z : ℝ := ∫ x, Real.exp (e x) ∂μ with hZ
  have hZ0 : 0 < Z := integral_exp_pos hZi
  -- the normalizer is bounded below on the unit ball
  have hZlow : V * Real.exp (-c) ≤ Z := by
    refine le_trans ?_ (setIntegral_le_integral (s := Metric.closedBall (0 : E) 1) hZi
      (ae_of_all _ fun _ => (Real.exp_pos _).le))
    rw [mul_comm]
    refine setIntegral_ge_of_const_le_real measurableSet_closedBall measure_closedBall_lt_top.ne
      (fun x hx => ?_) hZi.integrableOn
    exact Real.exp_le_exp.2 (hlow x (by simpa using hx))
  set T : ℝ := 2 + 2 * B / κ + c / κ with hT
  have hT0 : 0 ≤ T := by positivity
  -- outside the ball of radius `T` the weight is small compared with the normalizer
  have hpt : ∀ x : E, (1 + ‖x‖) ^ k * Real.exp (e x) ≤ (1 + T) ^ k * Real.exp (e x) +
      Real.exp (-c) * ((1 + ‖x‖) ^ k * Real.exp (0 * ‖x‖ - κ / 4 * ‖x‖ ^ 2)) := fun x => by
    rcases le_or_gt ‖x‖ T with hx | hx
    · refine le_add_of_le_of_nonneg (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by linarith) k) (Real.exp_pos _).le) (by positivity)
    refine le_add_of_nonneg_of_le (by positivity) ?_
    rw [mul_left_comm, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ((hup x).trans ?_)) (by positivity)
    have h1 : 2 * B ≤ κ * ‖x‖ := by
      have : 2 * B / κ ≤ ‖x‖ := by
        have := div_nonneg hc hκ.le
        linarith
      rwa [div_le_iff₀' hκ] at this
    have h2 : 4 * c ≤ κ * ‖x‖ ^ 2 := by
      have h3 : 1 + c / κ ≤ ‖x‖ := by
        have := div_nonneg (mul_nonneg zero_le_two hB) hκ.le
        linarith
      have h4 : 4 * (c / κ) ≤ ‖x‖ ^ 2 :=
        le_trans (by nlinarith [sq_nonneg (c / κ - 1)])
          (pow_le_pow_left₀ (by positivity) h3 2)
      rwa [mul_div_assoc', div_le_iff₀' hκ] at h4
    have h5 := mul_le_mul_of_nonneg_right h1 (norm_nonneg x)
    nlinarith
  have hIi : Integrable (fun x : E => (1 + ‖x‖) ^ k * Real.exp (0 * ‖x‖ - κ / 4 * ‖x‖ ^ 2)) μ :=
    integrable_one_add_norm_pow_mul_exp (by positivity) 0 k
  have hNi : Integrable (fun x : E => (1 + ‖x‖) ^ k * Real.exp (e x)) μ := by
    refine (integrable_one_add_norm_pow_mul_exp (μ := μ) hκ B k).mono'
      ((by fun_prop : Measurable fun x : E => (1 + ‖x‖) ^ k).mul he.exp).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hup x)) (by positivity)
  have hnum : ∫ x, (1 + ‖x‖) ^ k * Real.exp (e x) ∂μ ≤ (1 + T) ^ k * Z + Real.exp (-c) * I := by
    refine (integral_mono hNi ((hZi.const_mul _).add (hIi.const_mul _)) hpt).trans_eq ?_
    simp only [Pi.add_apply]
    rw [integral_add (hZi.const_mul _) (hIi.const_mul _), integral_const_mul,
      integral_const_mul]
  have htail : Real.exp (-c) * I ≤ I / V * Z := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hV0]
    calc Real.exp (-c) * I * V = I * (V * Real.exp (-c)) := by ring
      _ ≤ I * Z := mul_le_mul_of_nonneg_left hZlow hI0
  have hTM : 1 + T ≤ M * (1 + B + c) := by
    have h1 : 2 * B / κ + c / κ ≤ 3 / κ * (1 + B + c) := by
      rw [← add_div, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (by linarith) hκ.le
    rw [hM, add_mul, hT]
    linarith
  have h1 : (1 : ℝ) ≤ (1 + B + c) ^ k := one_le_pow₀ (by linarith)
  rw [integral_tilted_eq_div e fun x => (1 + ‖x‖) ^ k, ← hZ, div_le_iff₀ hZ0]
  refine hnum.trans ?_
  have h2 : (1 + T) ^ k ≤ M ^ k * (1 + B + c) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hTM k
  have h3 : I / V ≤ I / V * (1 + B + c) ^ k :=
    le_mul_of_one_le_right (div_nonneg hI0 hV0.le) h1
  calc (1 + T) ^ k * Z + Real.exp (-c) * I
      ≤ (M ^ k * (1 + B + c) ^ k) * Z + (I / V * (1 + B + c) ^ k) * Z :=
        add_le_add (mul_le_mul_of_nonneg_right h2 hZ0.le)
          (htail.trans (mul_le_mul_of_nonneg_right h3 hZ0.le))
    _ = (M ^ k + I / V) * (1 + B + c) ^ k * Z := by ring

/-- Replica observables of polynomial growth, with values in a normed space, are integrable for
the replicated Gibbs measure of a confined energy. -/
theorem integrable_pi_tilted_of_confining {F : Type*} [NormedAddCommGroup F] {κ : ℝ}
    (hκ : 0 < κ) {e : E → ℝ} (he : Measurable e) {A B : ℝ}
    (hconf : ∀ x, e x ≤ A + B * ‖x‖ - κ * ‖x‖ ^ 2) {Ψ : (R → E) → F}
    (hΨ : AEStronglyMeasurable Ψ (Measure.pi fun _ : R => μ)) {C : ℝ} {m : ℕ}
    (hΨb : ∀ σ, ‖Ψ σ‖ ≤ C * ∏ i, (1 + ‖σ i‖) ^ m) :
    Integrable Ψ (Measure.pi fun _ : R => μ.tilted e) := by
  have : IsProbabilityMeasure (μ.tilted e) :=
    isProbabilityMeasure_tilted (integrable_exp_of_confining (μ := μ) hκ he hconf)
  have h1 : Integrable (fun x : E => (1 + ‖x‖) ^ m) (μ.tilted e) :=
    (memLp_of_poly_bound_of_confining hκ he hconf (f := fun x : E => (1 + ‖x‖) ^ m)
      (by fun_prop) (C := 1) (m := m)
      (fun x => by rw [Real.norm_of_nonneg (by positivity), one_mul]) 1).integrable (by simp)
  have hΨ' : AEStronglyMeasurable Ψ (Measure.pi fun _ : R => μ.tilted e) := by
    rw [pi_tilted_eq_tilted_pi]
    exact hΨ.mono_ac (tilted_absolutelyContinuous _ _)
  exact ((Integrable.fintype_prod (f := fun _ : R => fun x : E => (1 + ‖x‖) ^ m)
    fun _ => h1).const_mul C).mono' hΨ' (ae_of_all _ hΨb)

/-- Replica observables of polynomial growth have finite moments of every order for the
replicated Gibbs measure of a confined energy. -/
theorem memLp_pi_tilted_of_confining {F : Type*} [NormedAddCommGroup F] {κ : ℝ} (hκ : 0 < κ)
    {e : E → ℝ} (he : Measurable e) {A B : ℝ}
    (hconf : ∀ x, e x ≤ A + B * ‖x‖ - κ * ‖x‖ ^ 2) {Ψ : (R → E) → F}
    (hΨ : AEStronglyMeasurable Ψ (Measure.pi fun _ : R => μ)) {C : ℝ} {m : ℕ}
    (hΨb : ∀ σ, ‖Ψ σ‖ ≤ C * ∏ i, (1 + ‖σ i‖) ^ m) (p : ℝ≥0) :
    MemLp Ψ p (Measure.pi fun _ : R => μ.tilted e) := by
  have : IsProbabilityMeasure (μ.tilted e) :=
    isProbabilityMeasure_tilted (integrable_exp_of_confining (μ := μ) hκ he hconf)
  have hΨ' : AEStronglyMeasurable Ψ (Measure.pi fun _ : R => μ.tilted e) := by
    rw [pi_tilted_eq_tilted_pi]
    exact hΨ.mono_ac (tilted_absolutelyContinuous _ _)
  obtain ⟨k, hk⟩ := exists_nat_ge p
  have hpk : (p : ℝ≥0∞) ≤ ((k + 1 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hk.trans (Nat.cast_le.2 k.le_succ)
  refine MemLp.mono_exponent ?_ hpk
  refine (integrable_norm_rpow_iff hΨ' (by simp) (ENNReal.natCast_ne_top _)).1 ?_
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast]
  refine integrable_pi_tilted_of_confining hκ he hconf (hΨ.norm.pow _) (C := C ^ (k + 1))
    (m := m * (k + 1)) fun σ => ?_
  rw [norm_pow, norm_norm]
  refine (pow_le_pow_left₀ (norm_nonneg _) (hΨb σ) _).trans_eq ?_
  rw [mul_pow, ← Finset.prod_pow]
  exact congrArg _ (Finset.prod_congr rfl fun i _ => (pow_mul _ _ _).symm)

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
    HasDerivAt (fun r => ∫ σ, Ψ r σ ∂(Measure.pi fun _ : R => μ.tilted (e r)))
      ((∫ σ, Ψ' t σ ∂(Measure.pi fun _ : R => μ.tilted (e t))) +
        ((∫ σ, Ψ t σ * (∑ i, e' t (σ i)) ∂(Measure.pi fun _ : R => μ.tilted (e t))) -
          (∫ σ, Ψ t σ ∂(Measure.pi fun _ : R => μ.tilted (e t))) *
            ∫ σ, (∑ i, e' t (σ i)) ∂(Measure.pi fun _ : R => μ.tilted (e t)))) t := by
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
        C * (L * Fintype.card R) * ∏ i, (1 + ‖σ i‖) ^ (m + n) := fun r hr Φ hΦ σ =>
    abs_mul_le_mul_prod_one_add_norm_pow (hΦ σ)
      (abs_sum_le_mul_prod_one_add_norm_pow (he'b r hr) σ)
  -- differentiate an unnormalized integral
  have hnum : ∀ (Φ Φ' : ℝ → (R → E) → ℝ), (∀ r ∈ s, Measurable (Φ r)) → Measurable (Φ' t) →
      (∀ r ∈ s, ∀ σ, |Φ r σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m) →
      (∀ r ∈ s, ∀ σ, |Φ' r σ| ≤ C * ∏ i, (1 + ‖σ i‖) ^ m) →
      (∀ σ, ∀ r ∈ s, HasDerivAt (fun q => Φ q σ) (Φ' r σ) r) →
      HasDerivAt (fun r => ∫ σ, Φ r σ * Real.exp (∑ i, e r (σ i))
          ∂(Measure.pi fun _ : R => μ))
        (∫ σ, (Φ' t σ + Φ t σ * ∑ i, e' t (σ i)) * Real.exp (∑ i, e t (σ i))
          ∂(Measure.pi fun _ : R => μ)) t := by
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
        (Measure.pi fun _ : R => μ) :=
      Integrable.fintype_prod (f := fun _ : R => fun x : E =>
        Real.exp A * ((1 + ‖x‖) ^ (m + n) * Real.exp (B * ‖x‖ - κ * ‖x‖ ^ 2)))
        fun _ => (integrable_one_add_norm_pow_mul_exp (μ := μ) hκ B (m + n)).const_mul _
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
    · exact abs_mul_exp_sum_le_of_confining (hconf r hr) (hbd r hr σ)
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
  have hZ : (0 : ℝ) < ∫ σ, Real.exp (∑ i, e t (σ i)) ∂(Measure.pi fun _ : R => μ) := by
    rw [integral_pi_exp_sum (μ := μ)]
    exact pow_pos (integral_exp_pos
      (integrable_exp_of_confining (μ := μ) hκ (he t ht) (hconf t ht))) _
  have hI1 : Integrable (fun σ => Ψ' t σ * Real.exp (∑ i, e t (σ i)))
      (Measure.pi fun _ : R => μ) :=
    integrable_pi_mul_exp_of_confining hκ (he t ht) (hconf t ht) hΨ' (hΨ'b t ht)
  have hI2 : Integrable (fun σ => (Ψ t σ * ∑ i, e' t (σ i)) * Real.exp (∑ i, e t (σ i)))
      (Measure.pi fun _ : R => μ) :=
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
    HasDerivAt (fun r => ∫ σ, Ψ r σ ∂(Measure.pi fun _ : R => μ.tilted (e r)))
      ((∫ σ, Ψ' t σ ∂(Measure.pi fun _ : R => μ.tilted (e t))) +
        replicaDiff (μ.tilted (e t)) (Ψ t) (e' t)) t := by
  have ht : t ∈ s := mem_of_mem_nhds hs
  refine (hasDerivAt_integral_pi_tilted_of_confining hκ hs he he' hconf he'b hd hΨ hΨ' hΨb
    hΨ'b hΨd).congr_deriv ?_
  have : IsProbabilityMeasure (μ.tilted (e t)) :=
    isProbabilityMeasure_tilted (integrable_exp_of_confining (μ := μ) hκ (he t ht) (hconf t ht))
  have hh : Integrable (e' t) (μ.tilted (e t)) :=
    (memLp_of_poly_bound_of_confining hκ (he t ht) (hconf t ht) he'.aestronglyMeasurable
      (he'b t ht) 1).integrable (by simp)
  have hFI : ∀ i : R, Integrable (fun σ => Ψ t σ * e' t (σ i))
      (Measure.pi fun _ : R => μ.tilted (e t)) := fun i =>
    integrable_pi_tilted_of_confining hκ (he t ht) (hconf t ht)
      ((hΨ t ht).mul (he'.comp (measurable_pi_apply i))).aestronglyMeasurable fun σ =>
        abs_mul_le_mul_prod_one_add_norm_pow (hΨb t ht σ) (abs_comp_eval_le_prod (he'b t ht) σ i)
  rw [integral_pi_cov_sum_eq_sum_sub_fresh_of_integrable _ _
    (hΨ t ht).aestronglyMeasurable _ hh hFI]

end MeasureTheory
