/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianVector
public import LeanMachineLearning.SpinGlasses.GibbsMeasure

/-!
# Gaussian integration by parts for the Gibbs measure

Let `(x, y)` be a centered jointly Gaussian field on a finite set `α`, with
`C(a, b) = 𝔼 x(a) y(b)`, and let `⟨·⟩ = Measure.count.tilted (y + h)` be the Gibbs measure of the
random energy `y` with a deterministic bias `h` (`h = log G` for a reference weight `G`; compare
[Panchenko, 2013, Eq. (1.27)]).  No definitions are introduced: Gibbs averages are integrals
against `Measure.count.tilted`, replicas are the `Measure.pi` of copies of it, and the Gaussian
input is Mathlib's `HasGaussianLaw` for the vector `(x, y)`.

## Main declarations

* `SpinGlasses.integral_pi_count_tilted`: the `R`-replica average as an explicit finite sum.
* `SpinGlasses.fderiv_integral_pi_count_tilted_add`: the derivative of a replica average with
  respect to the energy `y(ρ)`, `∂_ρ ⟨Ψ⟩ = ⟨(∑ᵣ 1[σʳ = ρ] - n G(ρ)) Ψ⟩`.
* `SpinGlasses.integral_gibbs_replica_average_gaussian`: the replica covariance formula
  [Panchenko, 2013, Exercise 1.1, Eq. (1.29)], for an arbitrary finite replica index set `R` and
  an arbitrary observable `Φ` of the replicas; the extra replica is integrated out.
* `SpinGlasses.integral_gibbs_replica_average_gaussian_option`: the same with the `(n+1)`-st
  replica written as an `Option R`-indexed replica.
* `SpinGlasses.integral_gibbs_average_gaussian`: Lemma 1.1, Eq. (1.28),
  `𝔼⟨x(σ)⟩ = 𝔼⟨C(σ¹, σ¹) - C(σ¹, σ²)⟩`, the case of one replica and `Φ ≡ 1`.

The proof is Gaussian integration by parts
(`ProbabilityTheory.integral_mul_comp_eq_sum_integral_mul_of_sum`) applied to the smooth function
`y ↦ ⟨1[σ^{r₀} = a] Φ⟩_y` for each `a`, followed by the finite recombination
`SpinGlasses.sum_sum_mul_integral_eq`.

## References

* [D. Panchenko, *The Sherrington-Kirkpatrick Model*, Springer, 2013], §1.2.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Function
open scoped Matrix Topology

namespace SpinGlasses

variable {α R : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]

/-- **Replica average as an explicit sum:** under the `R`-fold product of the Gibbs measure
`count.tilted f`, `∫ Ψ = ∑_σ (∏_r exp (f (σ r)) / Z) Ψ(σ)`. -/
theorem integral_pi_count_tilted [Fintype α] [Fintype R] [DecidableEq R] (f : α → ℝ)
    (Ψ : (R → α) → ℝ) :
    ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted f) =
      ∑ σ : R → α, (∏ r, Real.exp (f (σ r)) / ∑ b, Real.exp (f b)) * Ψ σ := by
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Measure.real, Measure.pi_singleton, ENNReal.toReal_prod, smul_eq_mul]
  congr 1
  exact Finset.prod_congr rfl fun r _ => real_count_tilted_singleton f (σ r)

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The Gibbs weight vector `a ↦ exp (f a) / ∑ b, exp (f b)` depends smoothly on `f`. -/
theorem differentiable_gibbsWeight [Fintype α] [Nonempty α] (a : α) :
    Differentiable ℝ fun f : α → ℝ => Real.exp (f a) / ∑ b, Real.exp (f b) := by
  have hZ : ∀ f : α → ℝ, ∑ b, Real.exp (f b) ≠ 0 := fun f =>
    (Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty).ne'
  have h : ∀ b : α, Differentiable ℝ fun f : α → ℝ => Real.exp (f b) := fun b =>
    Real.differentiable_exp.comp (differentiable_apply b)
  have hs : Differentiable ℝ fun f : α → ℝ => ∑ b, Real.exp (f b) :=
    Differentiable.fun_sum fun b _ => h b
  have := (h a).mul (hs.inv hZ)
  convert this using 1
  ext f
  simp [div_eq_mul_inv]

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The replica average of `Ψ` is a smooth function of the energy `f`. -/
theorem differentiable_replicaAverage [Fintype α] [Nonempty α] [Fintype R] [DecidableEq R]
    (Ψ : (R → α) → ℝ) :
    Differentiable ℝ fun f : α → ℝ =>
      ∑ σ : R → α, (∏ r, Real.exp (f (σ r)) / ∑ b, Real.exp (f b)) * Ψ σ := by
  refine Differentiable.fun_sum fun σ _ => ?_
  refine Differentiable.mul ?_ (differentiable_const _)
  exact by
    have := fun r : R => differentiable_gibbsWeight (σ r)
    fun_prop

omit [MeasurableSpace α] [MeasurableSingletonClass α] in
/-- The product of `n` Gibbs weights along the line `f + t e_ρ` has derivative
`(∏ w) (∑ᵣ 1[σ r = ρ] - n w_ρ)` at `t = 0`. -/
theorem hasDerivAt_prod_gibbsWeight [Fintype α] [Nonempty α] [DecidableEq α] [Fintype R]
    (f : α → ℝ) (ρ : α) (σ : R → α) :
    HasDerivAt (fun t : ℝ => ∏ r, Real.exp (f (σ r) + t * if σ r = ρ then (1 : ℝ) else 0) /
        ∑ b, Real.exp (f b + t * if b = ρ then (1 : ℝ) else 0))
      ((∏ r, Real.exp (f (σ r)) / ∑ b, Real.exp (f b)) *
        ((∑ r, if σ r = ρ then (1 : ℝ) else 0) -
          Fintype.card R * (Real.exp (f ρ) / ∑ b, Real.exp (f b)))) 0 := by
  set Z := ∑ b, Real.exp (f b) with hZdef
  have hZ : 0 < Z := Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have e : ∀ t : ℝ, (∏ r, Real.exp (f (σ r) + t * if σ r = ρ then (1 : ℝ) else 0) /
        ∑ b, Real.exp (f b + t * if b = ρ then (1 : ℝ) else 0)) =
      Real.exp (∑ r, (f (σ r) + t * if σ r = ρ then (1 : ℝ) else 0)) /
        (∑ b, Real.exp (f b + t * if b = ρ then (1 : ℝ) else 0)) ^ Fintype.card R := by
    intro t
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Real.exp_sum]
  simp_rw [e]
  have hN : HasDerivAt (fun t : ℝ => Real.exp (∑ r, (f (σ r) + t * if σ r = ρ then (1 : ℝ) else 0)))
      (Real.exp (∑ r, f (σ r)) * ∑ r, if σ r = ρ then (1 : ℝ) else 0) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => ∑ r, (f (σ r) + t * if σ r = ρ then (1 : ℝ) else 0))
        (∑ r, if σ r = ρ then (1 : ℝ) else 0) 0 := by
      refine HasDerivAt.fun_sum fun r _ => ?_
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (if σ r = ρ then (1 : ℝ) else 0)).const_add
        (f (σ r))
    simpa [Real.exp_sum] using h1.exp
  have hZ' : HasDerivAt (fun t : ℝ => ∑ b, Real.exp (f b + t * if b = ρ then (1 : ℝ) else 0))
      (Real.exp (f ρ)) 0 := by
    have : HasDerivAt (fun t : ℝ => ∑ b, Real.exp (f b + t * if b = ρ then (1 : ℝ) else 0))
        (∑ b, Real.exp (f b) * if b = ρ then (1 : ℝ) else 0) 0 := by
      refine HasDerivAt.fun_sum fun b _ => ?_
      have := ((hasDerivAt_id (0 : ℝ)).mul_const (if b = ρ then (1 : ℝ) else 0)).const_add (f b)
      simpa using this.exp
    simpa using this
  have hpow := hZ'.pow (Fintype.card R)
  have hne : (∑ b, Real.exp (f b + (0 : ℝ) * if b = ρ then (1 : ℝ) else 0)) ^
      Fintype.card R ≠ 0 := by
    simp only [zero_mul, add_zero]; exact pow_ne_zero _ hZ.ne'
  convert hN.div hpow hne using 1
  simp only [zero_mul, add_zero, ← hZdef, Real.exp_sum, Pi.pow_apply, Finset.prod_div_distrib,
    Finset.prod_const, Finset.card_univ]
  generalize Fintype.card R = n
  rcases n with _ | m
  · simp
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp

/-- **Derivative of a replica average with respect to the energy.**  For
`F(f) = ∫ Ψ ∂(count.tilted f)^{⊗R}`, the derivative in the direction `e_ρ` is
`∫ (∑ᵣ 1[σ r = ρ] - |R| G_f(ρ)) Ψ(σ) ∂(count.tilted f)^{⊗R}`, where `G_f(ρ)` is the Gibbs
weight of `ρ`. -/
theorem fderiv_integral_pi_count_tilted [Finite α] [Nonempty α] [DecidableEq α] [Fintype R]
    (Ψ : (R → α) → ℝ) (f : α → ℝ) (ρ : α) :
    fderiv ℝ (fun f : α → ℝ => ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted f)) f
        (Pi.single ρ 1) =
      ∫ σ, ((∑ r, if σ r = ρ then (1 : ℝ) else 0) -
        Fintype.card R * (Measure.count.tilted f).real {ρ}) * Ψ σ
          ∂(Measure.pi fun _ : R => Measure.count.tilted f) := by
  have := Fintype.ofFinite α
  classical
  have hfun : (fun f : α → ℝ => ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted f)) =
      fun f => ∑ σ : R → α, (∏ r, Real.exp (f (σ r)) / ∑ b, Real.exp (f b)) * Ψ σ :=
    funext fun f => integral_pi_count_tilted f Ψ
  have hdiff := differentiable_replicaAverage (R := R) Ψ
  rw [hfun, integral_pi_count_tilted]
  have hline : HasDerivAt (fun t : ℝ => f + t • (Pi.single ρ (1 : ℝ) : α → ℝ))
      (Pi.single ρ (1 : ℝ) : α → ℝ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single ρ (1 : ℝ) : α → ℝ)).const_add f
  have h1 := (hdiff (f + (0 : ℝ) • (Pi.single ρ (1 : ℝ) : α → ℝ))).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) hline
  have h2 : HasDerivAt (fun t : ℝ => ∑ σ : R → α, (∏ r, Real.exp (f (σ r) +
        t * if σ r = ρ then (1 : ℝ) else 0) /
          ∑ b, Real.exp (f b + t * if b = ρ then (1 : ℝ) else 0)) * Ψ σ)
      (∑ σ : R → α, ((∏ r, Real.exp (f (σ r)) / ∑ b, Real.exp (f b)) *
        ((∑ r, if σ r = ρ then (1 : ℝ) else 0) -
          Fintype.card R * (Real.exp (f ρ) / ∑ b, Real.exp (f b)))) * Ψ σ) 0 :=
    HasDerivAt.fun_sum fun σ _ => (hasDerivAt_prod_gibbsWeight f ρ σ).mul_const _
  have h3 : (fun t : ℝ => ∑ σ : R → α, (∏ r, Real.exp (f (σ r) +
        t * if σ r = ρ then (1 : ℝ) else 0) /
          ∑ b, Real.exp (f b + t * if b = ρ then (1 : ℝ) else 0)) * Ψ σ) =
      fun t => (fun f : α → ℝ => ∑ σ : R → α,
        (∏ r, Real.exp (f (σ r)) / ∑ b, Real.exp (f b)) * Ψ σ)
          (f + t • (Pi.single ρ (1 : ℝ) : α → ℝ)) := by
    funext t
    simp [Pi.single_apply]
  rw [h3] at h2
  simp only [zero_smul, add_zero] at h1
  rw [h1.unique h2, real_count_tilted_singleton]
  simp [mul_assoc]

/-- Recombination of the covariance terms in the replica Gaussian integration by parts. -/
theorem sum_sum_mul_integral_eq [Fintype α] [DecidableEq α] [Fintype R]
    (f : α → ℝ) (c : α → α → ℝ) (Φ : (R → α) → ℝ) (r₀ : R) :
    ∑ a, ∑ b, c a b * ∫ σ, ((∑ r, if σ r = b then (1 : ℝ) else 0) -
        Fintype.card R * (Measure.count.tilted f).real {b}) * (if σ r₀ = a then Φ σ else 0)
          ∂(Measure.pi fun _ : R => Measure.count.tilted f) =
      ∫ σ, Φ σ * (∑ r, c (σ r₀) (σ r) - Fintype.card R * ∫ τ, c (σ r₀) τ ∂(Measure.count.tilted f))
        ∂(Measure.pi fun _ : R => Measure.count.tilted f) := by
  classical
  simp only [integral_pi_count_tilted, integral_count_tilted, real_count_tilted_singleton]
  set w : α → ℝ := fun b => Real.exp (f b) / ∑ b, Real.exp (f b) with hw
  set W : (R → α) → ℝ := fun σ => ∏ r, w (σ r) with hW
  have hT : ∀ σ : R → α, ∑ a, ∑ b, c a b * (W σ * (((∑ r, if σ r = b then (1 : ℝ) else 0) -
      Fintype.card R * w b) * if σ r₀ = a then Φ σ else 0)) =
      W σ * (Φ σ * (∑ r, c (σ r₀) (σ r) - Fintype.card R * ∑ τ, w τ * c (σ r₀) τ)) := by
    intro σ
    rw [Finset.sum_eq_single (σ r₀)]
    · simp only [ite_true]
      have h1 : ∑ b, c (σ r₀) b * (∑ r, if σ r = b then (1 : ℝ) else 0) = ∑ r, c (σ r₀) (σ r) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        simp
      have h2 : ∑ b, c (σ r₀) b * w b = ∑ τ, w τ * c (σ r₀) τ := by
        simp_rw [mul_comm]
      calc _ = W σ * Φ σ * (∑ b, c (σ r₀) b * (∑ r, if σ r = b then (1 : ℝ) else 0) -
              Fintype.card R * ∑ b, c (σ r₀) b * w b) := by
            rw [Finset.mul_sum Finset.univ (fun b => c (σ r₀) b * w b) (Fintype.card R : ℝ),
              ← Finset.sum_sub_distrib, Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => by ring
        _ = _ := by rw [h1, h2]; ring
    · intro a _ ha
      refine Finset.sum_eq_zero fun b _ => ?_
      simp [Ne.symm ha]
    · simp
  calc _ = ∑ a, ∑ σ, ∑ b, c a b * (W σ * (((∑ r, if σ r = b then (1 : ℝ) else 0) -
            Fintype.card R * w b) * if σ r₀ = a then Φ σ else 0)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
    _ = ∑ σ, ∑ a, ∑ b, c a b * (W σ * (((∑ r, if σ r = b then (1 : ℝ) else 0) -
            Fintype.card R * w b) * if σ r₀ = a then Φ σ else 0)) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun σ _ => hT σ

/-- A replica average is bounded by any bound on the observable. -/
theorem abs_integral_pi_count_tilted_le [Finite α] [Nonempty α] [Fintype R] (f : α → ℝ)
    {Ψ : (R → α) → ℝ} {C : ℝ}
    (hΨ : ∀ σ, |Ψ σ| ≤ C) : |∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted f)| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := Measure.pi fun _ : R => Measure.count.tilted f)
    (f := Ψ) (C := C) (ae_of_all _ hΨ)
  simpa using h

/-- A replica average of `Φ χ(σ^{j₀})` with `Φ` bounded by `M` is at most `M ⟨|χ|⟩`. -/
theorem abs_integral_pi_count_tilted_mul_eval_le [Finite α] [Nonempty α] [Fintype R]
    (f χ : α → ℝ) (j₀ : R) {Φ : (R → α) → ℝ} {M : ℝ} (hΦ : ∀ σ, |Φ σ| ≤ M) :
    |∫ σ, Φ σ * χ (σ j₀) ∂(Measure.pi fun _ : R => Measure.count.tilted f)| ≤
      M * ∫ b, |χ b| ∂(Measure.count.tilted f) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hΦ (fun _ => Classical.arbitrary α))
  calc |∫ σ, Φ σ * χ (σ j₀) ∂(Measure.pi fun _ : R => Measure.count.tilted f)|
      ≤ ∫ σ, |Φ σ * χ (σ j₀)| ∂(Measure.pi fun _ : R => Measure.count.tilted f) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ σ, M * |χ (σ j₀)| ∂(Measure.pi fun _ : R => Measure.count.tilted f) := by
        refine integral_mono Integrable.of_finite Integrable.of_finite fun σ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hΦ σ) (abs_nonneg _)
    _ = M * ∫ b, |χ b| ∂(Measure.count.tilted f) := by
        rw [integral_const_mul]
        congr 1
        exact integral_comp_eval (μ := fun _ : R => Measure.count.tilted f) (i := j₀)
          (f := fun b => |χ b|) (measurable_of_finite _).aestronglyMeasurable

/-- The replica average with a deterministic shift `h` is smooth in the field `v`. -/
theorem differentiable_integral_pi_count_tilted_add [Finite α] [Nonempty α] [Fintype R]
    (Ψ : (R → α) → ℝ) (h : α → ℝ) :
    Differentiable ℝ fun v : α → ℝ =>
      ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted fun b => v b + h b) := by
  have := Fintype.ofFinite α
  classical
  have hfun : (fun v : α → ℝ => ∫ σ, Ψ σ ∂(Measure.pi fun _ : R =>
      Measure.count.tilted fun b => v b + h b)) = (fun f : α → ℝ => ∑ σ : R → α,
        (∏ r, Real.exp (f (σ r)) / ∑ b, Real.exp (f b)) * Ψ σ) ∘ fun v => v + h :=
    funext fun v => integral_pi_count_tilted (fun b => v b + h b) Ψ
  rw [hfun]
  exact (differentiable_replicaAverage Ψ).comp (differentiable_id.add_const h)

/-- Derivative of the shifted replica average in the direction `e_ρ`. -/
theorem fderiv_integral_pi_count_tilted_add [Finite α] [Nonempty α] [DecidableEq α] [Fintype R]
    (Ψ : (R → α) → ℝ) (h : α → ℝ) (v : α → ℝ) (ρ : α) :
    fderiv ℝ (fun v : α → ℝ =>
        ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted fun b => v b + h b)) v
        (Pi.single ρ 1) =
      ∫ σ, ((∑ r, if σ r = ρ then (1 : ℝ) else 0) -
        Fintype.card R * (Measure.count.tilted fun b => v b + h b).real {ρ}) * Ψ σ
          ∂(Measure.pi fun _ : R => Measure.count.tilted fun b => v b + h b) := by
  have := Fintype.ofFinite α
  have hfun : (fun v : α → ℝ => ∫ σ, Ψ σ ∂(Measure.pi fun _ : R =>
      Measure.count.tilted fun b => v b + h b)) = fun v => (fun f : α → ℝ =>
        ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted f)) (v + h) :=
    rfl
  rw [hfun, fderiv_comp_add_right (f := fun f : α → ℝ =>
    ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted f)) h]
  exact fderiv_integral_pi_count_tilted Ψ (v + h) ρ

section Gaussian

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Gaussian integration by parts for replica averages of the Gibbs measure**
(Panchenko Exercise 1.1, Eq. (1.29)).  Let `(x, y)` be a centered jointly Gaussian field on a
finite set `α`, `C a b = 𝔼 x(a) y(b)`, and let `⟨·⟩` be the `R`-fold product of the Gibbs measure
of the energy `y + h`.  For every observable `Φ` of the `|R|` replicas,
`𝔼⟨Φ x(σ^{r₀})⟩ = 𝔼⟨Φ (∑ᵣ C(σ^{r₀}, σʳ) - |R| 𝔼_τ C(σ^{r₀}, τ))⟩`,
where `τ` is drawn from the Gibbs measure itself (the extra replica `σ^{n+1}`). -/
theorem integral_gibbs_replica_average_gaussian [Finite α] [Nonempty α] [Fintype R]
    (x y : α → Ω → ℝ)
    (hxy : HasGaussianLaw (fun ω s => Sum.elim x y s ω) P)
    (hx : ∀ a, ∫ ω, x a ω ∂P = 0) (hy : ∀ a, ∫ ω, y a ω ∂P = 0)
    (C : α → α → ℝ) (hC : ∀ a b, C a b = ∫ ω, x a ω * y b ω ∂P) (h : α → ℝ) (r₀ : R)
    (Φ : (R → α) → ℝ) :
    ∫ ω, ∫ σ, Φ σ * x (σ r₀) ω
        ∂(Measure.pi fun _ : R => Measure.count.tilted fun a => y a ω + h a) ∂P =
      ∫ ω, ∫ σ, Φ σ * (∑ r, C (σ r₀) (σ r) - Fintype.card R *
          ∫ τ, C (σ r₀) τ ∂(Measure.count.tilted fun a => y a ω + h a))
        ∂(Measure.pi fun _ : R => Measure.count.tilted fun a => y a ω + h a) ∂P := by
  have := Fintype.ofFinite α
  classical
  have hP := hxy.isProbabilityMeasure
  set F : α → (α → ℝ) → ℝ := fun a v => ∫ σ, (if σ r₀ = a then Φ σ else 0)
    ∂(Measure.pi fun _ : R => Measure.count.tilted fun b => v b + h b) with hF
  have hFd : ∀ a, Differentiable ℝ (F a) := fun a =>
    differentiable_integral_pi_count_tilted_add _ h
  have hYm : AEMeasurable (fun ω => fun b => y b ω) P :=
    (measurable_pi_iff.2 fun b => measurable_pi_apply (Sum.inr b)).comp_aemeasurable
      hxy.aemeasurable
  -- uniform bounds on `F a` and its partial derivatives
  set K : α → ℝ := fun a => ∑ σ : R → α, |if σ r₀ = a then Φ σ else 0| with hK
  have hite : ∀ a σ, |if σ r₀ = a then Φ σ else 0| ≤ K a := fun a σ =>
    Finset.single_le_sum (f := fun σ : R → α => |if σ r₀ = a then Φ σ else 0|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)
  have hFg : ∀ a v, |F a v| ≤ K a * Real.exp (0 * ∑ l, |v l|) := fun a v => by
    simpa using abs_integral_pi_count_tilted_le _ (hite a)
  have hFg' : ∀ a b v, |fderiv ℝ (F a) v (Pi.single b 1)| ≤
      (Fintype.card R * K a) * Real.exp (0 * ∑ l, |v l|) := by
    intro a b v
    rw [hF, fderiv_integral_pi_count_tilted_add]
    simp only [zero_mul, Real.exp_zero, mul_one]
    refine abs_integral_pi_count_tilted_le _ fun σ => ?_
    have hw0 := measureReal_nonneg (μ := Measure.count.tilted fun b => v b + h b) (s := {b})
    have hw1 : (Measure.count.tilted fun b => v b + h b).real {b} ≤ 1 := measureReal_le_one
    have hS0 : 0 ≤ ∑ r, if σ r = b then (1 : ℝ) else 0 :=
      Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    have hSn : (∑ r, if σ r = b then (1 : ℝ) else 0) ≤ Fintype.card R := by
      calc _ ≤ ∑ _r : R, (1 : ℝ) := Finset.sum_le_sum fun _ _ => by split_ifs <;> norm_num
        _ = _ := by simp
    have hn : (0 : ℝ) ≤ Fintype.card R := Nat.cast_nonneg _
    rw [abs_mul]
    refine mul_le_mul ?_ (hite a σ) (abs_nonneg _) hn
    rw [abs_le]
    constructor <;> nlinarith
  -- integrability of the building blocks
  have hxi : ∀ a, Integrable (x a) P := fun a => by
    simpa using (hxy.eval (X := Sum.elim x y) (Sum.inl a)).integrable
  have hint1 : ∀ a, Integrable (fun ω => x a ω * F a (fun b => y b ω)) P := fun a =>
    (hxi a).mul_bdd (c := K a)
      (((hFd a).continuous.measurable.comp_aemeasurable hYm).aestronglyMeasurable)
      (ae_of_all _ fun ω => by simpa using hFg a (fun b => y b ω))
  have hint2 : ∀ a b, Integrable (fun ω => fderiv ℝ (F a) (fun k => y k ω) (Pi.single b 1)) P :=
    fun a b => Integrable.of_bound (C := Fintype.card R * K a)
      (((measurable_fderiv_apply_const ℝ (F a) _).comp_aemeasurable hYm).aestronglyMeasurable)
      (ae_of_all _ fun ω => by simpa using hFg' a b (fun k => y k ω))
  -- pointwise expansion of the left-hand side in the first replica
  have hlhs : ∀ ω, ∫ σ, Φ σ * x (σ r₀) ω
        ∂(Measure.pi fun _ : R => Measure.count.tilted fun a => y a ω + h a) =
      ∑ a, x a ω * F a (fun b => y b ω) := by
    intro ω
    simp only [hF]
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ fun a _ => Integrable.of_finite]
    refine integral_congr_ae (ae_of_all _ fun σ => ?_)
    simp [mul_comm, Finset.sum_ite_eq]
  simp_rw [hlhs]
  rw [integral_finsetSum _ fun a _ => hint1 a]
  have hst := fun a => integral_mul_comp_eq_sum_integral_mul_of_sum hxy hx hy a (hFd a)
    (hFg a) (hFg' a)
  rw [Finset.sum_congr rfl fun a _ => hst a]
  simp_rw [← hC]
  have e : ∀ a b, C a b * ∫ ω, fderiv ℝ (F a) (fun k => y k ω) (Pi.single b 1) ∂P =
      ∫ ω, C a b * fderiv ℝ (F a) (fun k => y k ω) (Pi.single b 1) ∂P := fun a b =>
    (integral_const_mul _ _).symm
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => e a b,
    Finset.sum_congr rfl fun a _ =>
      (integral_finsetSum _ fun b _ => (hint2 a b).const_mul (C a b)).symm,
    ← integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint2 a b).const_mul _]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only [hF, fderiv_integral_pi_count_tilted_add]
  exact sum_sum_mul_integral_eq (fun a => y a ω + h a) C Φ r₀

/-- **The extra replica of Eq. (1.29).**  Integrating a function of `n + 1` replicas that depends
on the last one only through a deterministic function is the same as integrating the `n`-replica
function against the Gibbs average of the last one. -/
theorem integral_pi_option_count_tilted [Finite α] [Fintype R] (f : α → ℝ)
    (g : (R → α) → α → ℝ) :
    ∫ τ, g (fun r => τ (some r)) (τ none) ∂(Measure.pi fun _ : Option R => Measure.count.tilted f) =
      ∫ σ, ∫ a, g σ a ∂(Measure.count.tilted f)
        ∂(Measure.pi fun _ : R => Measure.count.tilted f) := by
  have := Fintype.ofFinite α
  classical
  have hmp := Measure.pi_map_piOptionEquivProd (β := fun _ : Option R => α)
    (fun _ : Option R => Measure.count.tilted f)
  rw [← hmp, integral_map (MeasurableEquiv.measurable _).aemeasurable
    (measurable_of_finite _).aestronglyMeasurable, integral_prod _ Integrable.of_finite]
  rfl

/-- **Replica covariance formula with the extra replica (Panchenko Eq. (1.29)).**
`𝔼⟨Φ x(σ^{r₀})⟩ = 𝔼⟨Φ (∑ᵣ C(σ^{r₀}, σʳ) - n C(σ^{r₀}, σ^{n+1}))⟩`, where the right-hand side is a
Gibbs average over `n + 1` replicas indexed by `Option R`, the new replica being `none`. -/
theorem integral_gibbs_replica_average_gaussian_option [Finite α] [Nonempty α] [Fintype R]
    (x y : α → Ω → ℝ)
    (hxy : HasGaussianLaw (fun ω s => Sum.elim x y s ω) P)
    (hx : ∀ a, ∫ ω, x a ω ∂P = 0) (hy : ∀ a, ∫ ω, y a ω ∂P = 0)
    (C : α → α → ℝ) (hC : ∀ a b, C a b = ∫ ω, x a ω * y b ω ∂P) (h : α → ℝ) (r₀ : R)
    (Φ : (R → α) → ℝ) :
    ∫ ω, ∫ σ, Φ σ * x (σ r₀) ω
        ∂(Measure.pi fun _ : R => Measure.count.tilted fun a => y a ω + h a) ∂P =
      ∫ ω, ∫ τ, Φ (fun r => τ (some r)) * (∑ r, C (τ (some r₀)) (τ (some r)) -
          Fintype.card R * C (τ (some r₀)) (τ none))
        ∂(Measure.pi fun _ : Option R => Measure.count.tilted fun a => y a ω + h a) ∂P := by
  have := Fintype.ofFinite α
  classical
  rw [integral_gibbs_replica_average_gaussian x y hxy hx hy C hC h r₀ Φ]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  symm
  refine (integral_pi_option_count_tilted (fun a => y a ω + h a) (fun σ a => Φ σ *
    (∑ r, C (σ r₀) (σ r) - Fintype.card R * C (σ r₀) a))).trans ?_
  refine integral_congr_ae (ae_of_all _ fun σ => ?_)
  simp only
  rw [integral_const_mul, integral_sub Integrable.of_finite Integrable.of_finite,
    integral_const, integral_const_mul]
  simp

/-- **Gaussian integration by parts for the Gibbs measure (Panchenko Lemma 1.1, Eq. (1.28)):**
`𝔼⟨x(σ)⟩ = 𝔼⟨C(σ¹, σ¹) - C(σ¹, σ²)⟩`, the case of one replica and `Φ ≡ 1`. -/
theorem integral_gibbs_average_gaussian [Finite α] [Nonempty α] (x y : α → Ω → ℝ)
    (hxy : HasGaussianLaw (fun ω s => Sum.elim x y s ω) P)
    (hx : ∀ a, ∫ ω, x a ω ∂P = 0) (hy : ∀ a, ∫ ω, y a ω ∂P = 0)
    (C : α → α → ℝ) (hC : ∀ a b, C a b = ∫ ω, x a ω * y b ω ∂P) (h : α → ℝ) :
    ∫ ω, ∫ a, x a ω ∂(Measure.count.tilted fun a => y a ω + h a) ∂P =
      ∫ ω, ∫ p : α × α, (C p.1 p.1 - C p.1 p.2)
        ∂((Measure.count.tilted fun a => y a ω + h a).prod
          (Measure.count.tilted fun a => y a ω + h a)) ∂P := by
  have := Fintype.ofFinite α
  classical
  have h1 := integral_gibbs_replica_average_gaussian (R := Unit) x y hxy hx hy C hC h ()
    (fun _ => 1)
  have e1 : ∀ ω, ∫ σ : Unit → α, (1 : ℝ) * x (σ ()) ω
      ∂(Measure.pi fun _ : Unit => Measure.count.tilted fun a => y a ω + h a) =
      ∫ a, x a ω ∂(Measure.count.tilted fun a => y a ω + h a) := fun ω => by
    simpa using integral_comp_eval (μ := fun _ : Unit => Measure.count.tilted fun a => y a ω + h a)
      (i := ()) (f := fun a => x a ω) (measurable_of_finite _).aestronglyMeasurable
  have e2 : ∀ ω, ∫ σ : Unit → α, (1 : ℝ) * (∑ r : Unit, C (σ ()) (σ r) - Fintype.card Unit *
        ∫ τ, C (σ ()) τ ∂(Measure.count.tilted fun a => y a ω + h a))
      ∂(Measure.pi fun _ : Unit => Measure.count.tilted fun a => y a ω + h a) =
      ∫ p : α × α, (C p.1 p.1 - C p.1 p.2)
        ∂((Measure.count.tilted fun a => y a ω + h a).prod
          (Measure.count.tilted fun a => y a ω + h a)) := fun ω => by
    rw [integral_prod _ Integrable.of_finite]
    simp only [one_mul, Finset.univ_unique, Finset.sum_singleton, Fintype.card_unique, Nat.cast_one]
    rw [integral_comp_eval (μ := fun _ : Unit => Measure.count.tilted fun a => y a ω + h a)
      (i := ()) (f := fun a => C a a - ∫ τ, C a τ ∂(Measure.count.tilted fun a => y a ω + h a))
      (measurable_of_finite _).aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    simp only
    rw [integral_sub Integrable.of_finite Integrable.of_finite, integral_const]
    simp
  simpa only [e1, e2] using h1

end Gaussian

end SpinGlasses
