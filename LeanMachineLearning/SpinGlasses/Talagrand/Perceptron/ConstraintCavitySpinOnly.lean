/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.ProductTiltedMarginal
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.ConstraintCavityPath

/-!
# The spin-only reduction of the interpolating cavity system

Talagrand Section 2.3. For a spin-only observable the auxiliary coordinates `ξ_{<M}, ξ_M` of the
base and the new coordinate `ξ` of the extended system can be integrated out: the replica average
under the extended Gibbs law equals a replica average on the spin set under a counting Gibbs
measure whose energy is `D + ∑_{k<M} log ∫ e^{v_k} + log ∫∫ e^{w}`.

* `integral_pi_tilted_cavityPath_spinOnly`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace SpinGlasses

variable {N M : ℕ}

variable {u : ℝ → ℝ} {D : ℝ} (hu : Measurable u) (hD : ∀ x, u x ≤ D) (t q s z : ℝ)
  (ω : SmartPathDisorder N (M + 1))

include hu hD in
/-- **The new coordinate drops out of the energy by integration.** Marginalizing `ξ` replaces the
cavity energy by `E_∼ + log ∫ e^{u(S_s)} dγ(ξ)`, a function of the old configuration only. -/
theorem integral_pi_tilted_cavityPath_marginal_xi {R : Type*} [Fintype R]
    {f : (R → SmartPathState N (M + 1)) → ℝ} (hf : Measurable f) :
    ∫ σ : R → SmartPathState N (M + 1) × ℝ, f (fun r => (σ r).1)
      ∂(Measure.pi fun _ : R => ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
        fun p : SmartPathState N (M + 1) × ℝ =>
          smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
            u (Real.cos s * smartPathField t ω p.1 (Fin.last M) +
              Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2))) =
      ∫ x, f x ∂(Measure.pi fun _ : R => (smartPathBase N (M + 1)).tilted
        fun x : SmartPathState N (M + 1) =>
          smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2) +
            Real.log (∫ ξ, Real.exp (u (Real.cos s * smartPathField t ω x (Fin.last M) +
              Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * ξ))) ∂gaussianReal 0 1)) := by
  have hmeasE : Measurable fun p : SmartPathState N (M + 1) × ℝ =>
      smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
        u (Real.cos s * smartPathField t ω p.1 (Fin.last M) +
          Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2)) :=
    ((measurable_smartPathEnergy_init hu t ω).comp measurable_fst).add
      (hu.comp ((measurable_const.mul ((measurable_smartPathField_slice t ω (Fin.last M)).comp
        measurable_fst)).add (measurable_const.mul (by fun_prop))))
  have hbd : ∀ p : SmartPathState N (M + 1) × ℝ,
      smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
        u (Real.cos s * smartPathField t ω p.1 (Fin.last M) +
          Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2)) ≤
        (M * D + Real.sqrt (1 - t) * |ω.2|) + D := fun p =>
    add_le_add (smartPathEnergy_init_le hD t ω p.1) (hD _)
  have hi := integrable_exp_of_ae_le (μ := (smartPathBase N (M + 1)).prod (gaussianReal 0 1))
    hmeasE.aemeasurable (ae_of_all _ hbd)
  rw [integral_pi_tilted_prod_fst hi hf]
  have hlog : ∀ x : SmartPathState N (M + 1),
      Real.log (∫ b, Real.exp (smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2)
          (x.1, Fin.init x.2) +
        u (Real.cos s * smartPathField t ω x (Fin.last M) +
          Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * b))) ∂gaussianReal 0 1) =
      smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2) +
        Real.log (∫ ξ, Real.exp (u (Real.cos s * smartPathField t ω x (Fin.last M) +
          Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * ξ))) ∂gaussianReal 0 1) := by
    intro x
    have hpos : 0 < ∫ ξ, Real.exp (u (Real.cos s * smartPathField t ω x (Fin.last M) +
        Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * ξ))) ∂gaussianReal 0 1 :=
      integral_exp_pos_of_ae_le (C := D)
        (hu.comp (measurable_const.add (measurable_const.mul
          (measurable_const.add (measurable_const.mul measurable_id))))).aemeasurable
        (ae_of_all _ fun _ => hD _)
    simp_rw [Real.exp_add]
    rw [integral_const_mul, Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp]
  simp_rw [hlog]

include hu hD in
/-- **The spin-only reduction.** For an observable `f` of the spins only, the replica average of the
extended cavity system is the replica average on the spin set (a finite set with counting
measure) of the Gibbs law with energy
`ε √(1-t) y + ∑_{k<M} log ∫ e^{u(S_k)} dγ + log ∫∫ e^{u(S_s)} dγ dγ`,
where every auxiliary coordinate has been integrated out. -/
theorem integral_pi_tilted_cavityPath_spinOnly {R : Type*} [Fintype R]
    (f : (R → PerceptronSpin N) → ℝ) :
    ∫ σ : R → SmartPathState N (M + 1) × ℝ, f (fun r => (σ r).1.1)
      ∂(Measure.pi fun _ : R => ((smartPathBase N (M + 1)).prod (gaussianReal 0 1)).tilted
        fun p : SmartPathState N (M + 1) × ℝ =>
          smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (p.1.1, Fin.init p.1.2) +
            u (Real.cos s * smartPathField t ω p.1 (Fin.last M) +
              Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2))) =
      ∫ a, f a ∂(Measure.pi fun _ : R => Measure.count.tilted fun a : PerceptronSpin N =>
        ((a.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * ω.2 +
          (∑ j : Fin M, Real.log (∫ b, Real.exp (u (smartPathField t ω (a, fun _ => b)
              j.castSucc)) ∂gaussianReal 0 1) +
            Real.log (∫ b, ∫ ξ, Real.exp (u (Real.cos s *
              smartPathField t ω (a, fun _ => b) (Fin.last M) +
              Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)))
              ∂gaussianReal 0 1 ∂gaussianReal 0 1))) := by
  -- the auxiliary potentials of the `M + 1` coordinates
  let Vt : PerceptronSpin N → ℝ → ℝ := fun a b => Real.log (∫ ξ, Real.exp (u (Real.cos s *
    smartPathField t ω (a, fun _ => b) (Fin.last M) +
    Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * ξ))) ∂gaussianReal 0 1)
  let V : PerceptronSpin N → Fin (M + 1) → ℝ → ℝ := fun a k b =>
    if k = Fin.last M then Vt a b else u (smartPathField t ω (a, fun _ => b) k)
  have hfb : ∀ a k, Measurable fun b : ℝ => smartPathField t ω (a, fun _ => b) k := fun a k => by
    simp only [smartPathField_eq, smartPathFieldNoAux_eq]
    fun_prop
  have hVt_meas : ∀ a, Measurable (Vt a) := fun a => by
    have hj : Measurable fun p : ℝ × ℝ => Real.exp (u (Real.cos s *
        smartPathField t ω (a, fun _ => p.1) (Fin.last M) +
        Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * p.2))) :=
      (hu.comp ((measurable_const.mul ((hfb a (Fin.last M)).comp measurable_fst)).add
        (measurable_const.mul (measurable_const.add (measurable_const.mul measurable_snd))))).exp
    exact Real.measurable_log.comp
      (hj.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable
  have hV_meas : ∀ a k, Measurable (V a k) := fun a k => by
    by_cases hk : k = Fin.last M
    · simpa [V, hk] using hVt_meas a
    · simp only [V, hk, ite_false]
      exact hu.comp (hfb a k)
  have hIpos : ∀ a b, 0 < ∫ ξ, Real.exp (u (Real.cos s * smartPathField t ω (a, fun _ => b)
        (Fin.last M) + Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)))
        ∂gaussianReal 0 1 := fun a b =>
      integral_exp_pos_of_ae_le (C := D)
        (hu.comp (measurable_const.add (measurable_const.mul
          (measurable_const.add (measurable_const.mul measurable_id))))).aemeasurable
        (ae_of_all _ fun _ => hD _)
  have hVt_le : ∀ a b, Vt a b ≤ D := fun a b => by
    have hpos := hIpos a b
    have hle : ∫ ξ, Real.exp (u (Real.cos s * smartPathField t ω (a, fun _ => b)
        (Fin.last M) + Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)))
        ∂gaussianReal 0 1 ≤ Real.exp D := by
      refine (le_abs_self _).trans (abs_integral_le_of_forall_abs_le (gaussianReal 0 1)
        (M := Real.exp D) fun ξ => ?_)
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (hD _)
    exact (Real.log_le_log hpos hle).trans_eq (Real.log_exp D)
  have hV_le : ∀ a k b, V a k b ≤ D := fun a k b => by
    by_cases hk : k = Fin.last M
    · simpa [V, hk] using hVt_le a b
    · simpa [V, hk] using hD _
  have hfx : Measurable fun τ : R → SmartPathState N (M + 1) => f (fun r => (τ r).1) :=
    (measurable_of_finite f).comp (by fun_prop)
  refine (integral_pi_tilted_cavityPath_marginal_xi hu hD t q s z ω
    (f := fun τ => f (fun r => (τ r).1)) hfx).trans ?_
  -- the marginalized energy is a sum over the `M + 1` auxiliary coordinates
  have hE : ∀ x : SmartPathState N (M + 1),
      smartPathEnergy u t ((Fin.init ω.1.1, Fin.init ω.1.2), ω.2) (x.1, Fin.init x.2) +
        Real.log (∫ ξ, Real.exp (u (Real.cos s * smartPathField t ω x (Fin.last M) +
          Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * ξ))) ∂gaussianReal 0 1) =
      ((x.1.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * ω.2 + ∑ k, V x.1 k (x.2 k) := fun x => by
    have hfld : ∀ k, smartPathField t ω x k = smartPathField t ω (x.1, fun _ => x.2 k) k :=
      fun k => by simp [smartPathField_eq, smartPathFieldNoAux_eq]
    rw [smartPathEnergy_eq, Fin.sum_univ_castSucc]
    simp only [V, Vt, smartPathField_init, hfld (Fin.last M),
      (Fin.castSucc_lt_last _).ne, ite_false, ite_true, hfld]
    ring
  simp_rw [hE, smartPathBase_eq]
  have key := integral_pi_tilted_count_prod_sum (A := PerceptronSpin N) (B := ℝ)
    (K := Fin (M + 1)) (fun _ => gaussianReal 0 1)
    (fun a => ((a.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * ω.2) V hV_meas (fun _ => D) hV_le f
  have hRfun : (fun a : PerceptronSpin N => ((a.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * ω.2 +
      ∑ k, Real.log (∫ b, Real.exp (V a k b) ∂gaussianReal 0 1)) =
      fun a : PerceptronSpin N => ((a.2 : ℤ) : ℝ) * Real.sqrt (1 - t) * ω.2 +
        (∑ j : Fin M, Real.log (∫ b, Real.exp (u (smartPathField t ω (a, fun _ => b)
              j.castSucc)) ∂gaussianReal 0 1) +
          Real.log (∫ b, ∫ ξ, Real.exp (u (Real.cos s *
            smartPathField t ω (a, fun _ => b) (Fin.last M) +
            Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)))
            ∂gaussianReal 0 1 ∂gaussianReal 0 1)) := by
    funext a
    rw [Fin.sum_univ_castSucc]
    have hlast : ∫ b, Real.exp (V a (Fin.last M) b) ∂gaussianReal 0 1 =
        ∫ b, ∫ ξ, Real.exp (u (Real.cos s * smartPathField t ω (a, fun _ => b) (Fin.last M) +
          Real.sin s * (Real.sqrt q * z + Real.sqrt (1 - q) * ξ)))
          ∂gaussianReal 0 1 ∂gaussianReal 0 1 :=
      integral_congr_ae (ae_of_all _ fun b => by
        simp only [V, Vt, ite_true]
        exact Real.exp_log (hIpos a b))
    have hcast : ∀ j : Fin M, ∫ b, Real.exp (V a j.castSucc b) ∂gaussianReal 0 1 =
        ∫ b, Real.exp (u (smartPathField t ω (a, fun _ => b) j.castSucc)) ∂gaussianReal 0 1 :=
      fun j => by
        simp only [V, (Fin.castSucc_lt_last j).ne, ite_false]
    simp only [hlast, hcast]
  rw [hRfun] at key
  exact key

end SpinGlasses
