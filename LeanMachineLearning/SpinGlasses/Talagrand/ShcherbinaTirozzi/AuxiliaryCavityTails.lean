/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Convex.Integral
public import LeanMachineLearning.ForMathlib.MeasureTheory.Constructions.PiSnoc
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FreshReplicas
public import LeanMachineLearning.ForMathlib.Probability.Moments.SecondMoment
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.AuxiliaryCavity
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.AuxiliaryCavityDerivative

/-!
# The Shcherbina--Tirozzi model: overlap tail bounds and comparison along `ν_{t,v}`

This file formalizes Eqs. (3.97)--(3.106) and Lemma 3.2.9 of Talagrand, *Spin Glasses: A Challenge
for Mathematicians*, Vol. I, Section 3.2.

Along the auxiliary cavity path `ν_{t,v}` (`t, v ∈ [0, 1]`), for spin-only observables the marginal
quenched Gibbs measure has the smoothed Hamiltonian (3.99), in which `M` constraints use `u` and
the isolated constraint uses the concave Gaussian smoothing `u_v(x) = log 𝔼_ξ exp u(x + c ξ)` with
`c = √(1 - v) √(ρ - q)`. Using the constraint-indexed last-spin tail bound (Lemma 3.2.6) and the
dimension-free exponential moment (`integral_exp_half_sq_norm_tilted_le_two_rpow`), we prove:
* Eq. (3.100): `ν_{t,v}(exp (σ_N² / K)) ≤ K` uniformly in `t, v ∈ [0, 1]`.
* Eqs. (3.101)--(3.102): `⟨exp (κ ‖σ‖² / 2)⟩_{t,v} ≤ exp (K B^*)` and
  `ν_{t,v}(exp (‖σ‖² / K)) ≤ exp (L (N + 1))`.
* Eqs. (3.97)--(3.98), (3.103), (3.104): `exp (-4 (N + 1))` tail bounds and uniform 8th-moment (and
  4th-moment) bounds on `R_{1,1} - ρ` and `R_{1,2} - q` under `ν_{t,v}`.
* Equivalence between the `(d_full, z)` representation of `AuxiliaryCavity.lean` and the `(d, w)`
  representation of `AuxiliaryCavityDerivative.lean`.
* Eq. (3.105) and Lemma 3.2.9 (Eq. (3.106)): uniform `v`-derivative bound and backward Grönwall
  comparison `ν_{t,v}(f^*) ≤ K (ν_t(f^*) + exp (-(N + 1)) A)` assuming `ν_{t,s}(f^{*2}) ≤ A²` for
  all `s ∈ [0, 1]`.

## Main declarations

* `SpinGlasses.integral_shcherbinaTirozziAuxCavity_eq_shared`: equivalence of the `(d_full, z)` and
  `(d, w)` disorder representations of `ν_{t,v}`.
* `SpinGlasses.exists_integral_exp_sq_shcherbinaTirozziAuxCavity_last_le`: Eq. (3.100).
* `SpinGlasses.exists_integral_exp_sq_norm_shcherbinaTirozziAuxCavity_le_exp`: Eq. (3.102).
* `SpinGlasses.exists_shcherbinaTirozziAuxCavity_overlap_tails_and_moments`: Eqs. (3.97), (3.98),
  (3.103), (3.104).
* `SpinGlasses.exists_hasDerivAt_shcherbinaTirozziAuxCavity_abs_le_add_exp_neg`: Eq. (3.105).
* `SpinGlasses.exists_shcherbinaTirozziAuxCavity_le_add_exp_neg`: Lemma 3.2.9 (Eq. (3.106)).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Function Module
open scoped NNReal Topology RealInnerProductSpace Real

namespace SpinGlasses

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

section DisorderBridge

variable {N M : ℕ} {R : Type*} [Fintype R]

/-- Measure-preserving bijection between the `(d_full, z)` disorder of `AuxiliaryCavity.lean` and
the `(d, w)` disorder of `AuxiliaryCavityDerivative.lean`, where `w : Fin (N + 1) ⊕ Unit → ℝ`
groups the last constraint row `g (Fin.last M)` and the shared scalar `z`. -/
theorem measurePreserving_auxDisorder_to_shared (r : ℝ≥0) :
    let P_full := ((gaussianReal 0 r).prod
      ((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))).prod (gaussianReal 0 1)
    let P := (gaussianReal 0 r).prod
      ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))
    let γ := Measure.pi fun _ : Fin (N + 1) ⊕ Unit => gaussianReal 0 1
    MeasurePreserving
      (fun p : (ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) × ℝ =>
        ((p.1.1, (fun j => p.1.2.1 j.castSucc, p.1.2.2)),
          Sum.elim (p.1.2.1 (Fin.last M)) (fun _ : Unit => p.2)))
      P_full (P.prod γ) := by
  intro P_full P γ
  set γ_row := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
  set P_old := Measure.pi fun _ : Fin M => γ_row
  have hg := measurePreserving_finSuccProd γ_row M
  have hunit := (measurePreserving_funUnique (gaussianReal 0 1) Unit).symm
  have hsum := (measurePreserving_sumPiEquivProdPi_symm
    (X := fun _ : Fin (N + 1) ⊕ Unit => ℝ) (fun _ => gaussianReal 0 1)).comp
    ((MeasurePreserving.id γ_row).prod hunit)
  have s1 : MeasurePreserving
      (fun p : (ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) × ℝ =>
        ((p.1.1, (MeasurableEquiv.finSuccProd (Fin (N + 1) → ℝ) M p.1.2.1, p.1.2.2)), p.2))
      P_full (((gaussianReal 0 r).prod ((P_old.prod γ_row).prod γ_row)).prod (gaussianReal 0 1)) :=
    ((MeasurePreserving.id (gaussianReal 0 r)).prod (hg.prod (MeasurePreserving.id γ_row))).prod
      (MeasurePreserving.id (gaussianReal 0 1))
  have m1 := measurePreserving_prodAssoc P_old γ_row γ_row
  have m2 := (MeasurePreserving.id P_old).prod
    (Measure.measurePreserving_swap (μ := γ_row) (ν := γ_row))
  have m3 := (measurePreserving_prodAssoc P_old γ_row γ_row).symm
  have m4 := (MeasurePreserving.id (gaussianReal 0 r)).prod (m3.comp (m2.comp m1))
  have m5 := (measurePreserving_prodAssoc (gaussianReal 0 r) (P_old.prod γ_row) γ_row).symm
  have m6 := (m5.comp m4).prod (MeasurePreserving.id (gaussianReal 0 1))
  have s_mid := (measurePreserving_prodAssoc P γ_row (gaussianReal 0 1)).comp m6
  have s_end := ((MeasurePreserving.id P).prod hsum).comp (s_mid.comp s1)
  convert s_end using 1
  ext p : 1
  refine Prod.ext ?_ ?_
  · simp [MeasurableEquiv.prodAssoc, MeasurableEquiv.finSuccProd_apply]
  · ext k
    cases k <;>
      simp [MeasurableEquiv.prodAssoc, MeasurableEquiv.finSuccProd_apply,
        MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi_symm_apply]

/-- **Equivalence of the `(d_full, z)` and `(d, w)` representations of `ν_{t,v}`:** for any
observable `G_obs w σ` which is integrable on `P.prod γ` (in particular any observable covered by
`integrable_shcherbinaTirozziAuxCavity_shared`), the iterated integral `∫ d, ∫ w, ⟨G_obs⟩ ∂γ ∂P`
equals the single integral `∫ u, ⟨G_obs⟩ ∂P_full` of `AuxiliaryCavity.lean`. -/
theorem integral_shcherbinaTirozziAuxCavity_eq_shared {κ h : ℝ} (r : ℝ≥0) (rBar t v q ρ : ℝ)
    (u : ℝ → ℝ)
    (G_obs : (Fin (N + 1) ⊕ Unit → ℝ) → (R → ℝ^(N + 1) × ℝ) → ℝ)
    (hint : Integrable
      (fun p : (ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) ×
          (Fin (N + 1) ⊕ Unit → ℝ) =>
        ∫ σ : R → ℝ^(N + 1) × ℝ, G_obs p.2 σ
          ∂(Measure.pi fun _ : R =>
            ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted fun q₀ =>
              -shcherbinaTirozziCavityHamiltonian κ h r rBar t p.1.1 u p.1.2.1 p.1.2.2 q₀.1 +
                u (Real.sqrt v * ((Real.sqrt (N + 1))⁻¹ *
                    ((∑ i : Fin N, p.2 (Sum.inl i.castSucc) * q₀.1 i.castSucc) +
                      Real.sqrt t * (p.2 (Sum.inl (Fin.last N)) * q₀.1 (Fin.last N)))) +
                  Real.sqrt (1 - v) *
                    (Real.sqrt q * p.2 (Sum.inr ()) + Real.sqrt (ρ - q) * q₀.2))))
      (((gaussianReal 0 r).prod
        ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
          (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))).prod
        (Measure.pi fun _ : Fin (N + 1) ⊕ Unit => gaussianReal 0 1))) :
    let P_full := ((gaussianReal 0 r).prod
      ((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))).prod (gaussianReal 0 1)
    let P := (gaussianReal 0 r).prod
      ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))
    let γ := Measure.pi fun _ : Fin (N + 1) ⊕ Unit => gaussianReal 0 1
    ∫ d, ∫ w, ∫ σ : R → ℝ^(N + 1) × ℝ, G_obs w σ
        ∂(Measure.pi fun _ : R =>
          ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted fun q₀ =>
            -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 q₀.1 +
              u (Real.sqrt v * ((Real.sqrt (N + 1))⁻¹ *
                  ((∑ i : Fin N, w (Sum.inl i.castSucc) * q₀.1 i.castSucc) +
                    Real.sqrt t * (w (Sum.inl (Fin.last N)) * q₀.1 (Fin.last N)))) +
                Real.sqrt (1 - v) *
                  (Real.sqrt q * w (Sum.inr ()) + Real.sqrt (ρ - q) * q₀.2))) ∂γ ∂P =
      ∫ p, ∫ σ : R → ℝ^(N + 1) × ℝ,
          G_obs (Sum.elim (p.1.2.1 (Fin.last M)) (fun _ : Unit => p.2)) σ
        ∂(Measure.pi fun _ : R =>
          ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted fun q₀ =>
            -shcherbinaTirozziCavityHamiltonian κ h r rBar t p.1.1 u
                (fun j => p.1.2.1 j.castSucc) p.1.2.2 q₀.1 +
              u (Real.sqrt v * ((Real.sqrt (N + 1))⁻¹ *
                  ((∑ i : Fin N, p.1.2.1 (Fin.last M) i.castSucc * q₀.1 i.castSucc) +
                    Real.sqrt t * (p.1.2.1 (Fin.last M) (Fin.last N) * q₀.1 (Fin.last N)))) +
                Real.sqrt (1 - v) *
                  (Real.sqrt q * p.2 + Real.sqrt (ρ - q) * q₀.2))) ∂P_full := by
  intro P_full P γ
  rw [← integral_prod _ hint]
  have hmp := measurePreserving_auxDisorder_to_shared (N := N) (M := M) r
  exact (hmp.integral_comp_of_aestronglyMeasurable hint.aestronglyMeasurable).symm

end DisorderBridge

section TailAndMomentBounds

/-- The disorder `((y, (g, g₀)), z)` of the auxiliary cavity system with `M + 1` constraints and
shared Gaussian `z`. -/
local notation "AuxDis[" N ", " M "]" =>
  (ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) × ℝ

/-- The law of `AuxDis` with `y ~ 𝒩(0, r)` and standard Gaussian `g, g₀, z`. -/
local notation "auxLaw[" N ", " M ", " r "]" =>
  Measure.prod
    (Measure.prod (gaussianReal 0 r)
      (Measure.prod
        (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)))
    (gaussianReal 0 1)

/-- The cavity field `S_{k,t}` on `ℝ^(N+1)`. -/
local notation "cfield[" N ", " t ", " g ", " k ", " σ "]" =>
  (Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, g k (Fin.castSucc i) * σ (Fin.castSucc i)) +
    Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N)))

/-- Joint measurability of the auxiliary cavity exponent `E_old w.1 p.1 + u (S_v w p)`. -/
private theorem measurable_auxCavity_exponent {N M : ℕ} (κ h r rBar t v q ρ : ℝ) {u : ℝ → ℝ}
    (hum : Measurable u) :
    Measurable fun q₀ : AuxDis[N, M] × (ℝ^(N + 1) × ℝ) =>
      (-shcherbinaTirozziCavityHamiltonian κ h r rBar t q₀.1.1.1 u
          (fun j => q₀.1.1.2.1 j.castSucc) q₀.1.1.2.2 q₀.2.1) +
        u (Real.sqrt v * cfield[N, t, q₀.1.1.2.1, Fin.last M, q₀.2.1] +
          Real.sqrt (1 - v) * (Real.sqrt q * q₀.1.2 + Real.sqrt (ρ - q) * q₀.2.2)) := by
  have hσ : ∀ i : Fin (N + 1), Measurable fun q₀ : AuxDis[N, M] × (ℝ^(N + 1) × ℝ) =>
      q₀.2.1 i := fun i =>
    ((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) i).measurable).comp
      (measurable_fst.comp measurable_snd)
  have hg : ∀ (k : Fin (M + 1)) (i : Fin (N + 1)),
      Measurable fun q₀ : AuxDis[N, M] × (ℝ^(N + 1) × ℝ) => q₀.1.1.2.1 k i := fun k i =>
    (measurable_pi_apply i).comp ((measurable_pi_apply k).comp
      (measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_fst))))
  have hg₀ : ∀ i : Fin (N + 1), Measurable fun q₀ : AuxDis[N, M] × (ℝ^(N + 1) × ℝ) =>
      q₀.1.1.2.2 i := fun i =>
    (measurable_pi_apply i).comp
      (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp measurable_fst)))
  have hy0 : Measurable fun q₀ : AuxDis[N, M] × (ℝ^(N + 1) × ℝ) => q₀.1.1.1 :=
    measurable_fst.comp (measurable_fst.comp measurable_fst)
  have hz : Measurable fun q₀ : AuxDis[N, M] × (ℝ^(N + 1) × ℝ) => q₀.1.2 :=
    measurable_snd.comp measurable_fst
  have hξ : Measurable fun q₀ : AuxDis[N, M] × (ℝ^(N + 1) × ℝ) => q₀.2.2 :=
    measurable_snd.comp measurable_snd
  have hf_k : ∀ k : Fin (M + 1), Measurable fun q₀ : AuxDis[N, M] × (ℝ^(N + 1) × ℝ) =>
      cfield[N, t, q₀.1.1.2.1, k, q₀.2.1] := fun k =>
    (((Finset.measurable_sum _ fun i _ => (hg k i.castSucc).mul (hσ i.castSucc)).add
      (((hg k (Fin.last N)).mul (hσ (Fin.last N))).const_mul _)).const_mul _)
  have hold : Measurable fun q₀ : AuxDis[N, M] × (ℝ^(N + 1) × ℝ) =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t q₀.1.1.1 u
        (fun j => q₀.1.1.2.1 j.castSucc) q₀.1.1.2.2 q₀.2.1 := by
    have hsum := Finset.measurable_sum Finset.univ fun (j : Fin M) _ => hum.comp (hf_k j.castSucc)
    have hlin := (Finset.measurable_sum Finset.univ fun i _ => (hg₀ i).mul (hσ i)).const_mul h
    have hq_norm : Measurable fun q₀ : AuxDis[N, M] × (ℝ^(N + 1) × ℝ) => κ * ‖q₀.2.1‖ ^ 2 :=
      (((measurable_fst.comp measurable_snd).norm.pow_const 2).const_mul κ)
    have hy_term := (hσ (Fin.last N)).mul (hy0.const_mul (Real.sqrt (1 - t)))
    have hlast_sq := (((hσ (Fin.last N)).pow_const 2).const_mul ((1 - t) * (r - rBar))).div_const 2
    simp only [shcherbinaTirozziCavityHamiltonian]
    exact (((hq_norm.sub hsum).sub hlin).sub hy_term |>.add hlast_sq).neg
  exact hold.add (hum.comp (((hf_k (Fin.last M)).const_mul _).add
    (((hz.const_mul _).add (hξ.const_mul _)).const_mul _)))

/-- **Eq. (3.100):** along the auxiliary cavity path `ν_{t,v}` (`t, v ∈ [0, 1]`), the exponential
moment of the squared last spin satisfies `ν_{t,v}(exp (σ_N² / K)) ≤ K` uniformly in `N, M, t, v,
q, ρ`, where `K` depends only on `κ₀, h₀, D` and an upper bound `R` on `r`. -/
theorem exists_integral_exp_sq_shcherbinaTirozziAuxCavity_last_le (κ₀ h₀ D R : ℝ)
    (hκ₀ : 0 < κ₀) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N M : ℕ) (κ h t v q ρ rBar : ℝ) (r : ℝ≥0) (u : ℝ → ℝ) (D₂ : ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → 0 ≤ v → v ≤ 1 → rBar ≤ r → (r : ℝ) ≤ R →
      M ≤ 10 * (N + 1) → ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → Differentiable ℝ u →
      Differentiable ℝ (deriv u) → (∀ x, |deriv u x| ≤ D) → (∀ x, |deriv (deriv u) x| ≤ D₂) →
      let E_old : AuxDis[N, M] → ℝ^(N + 1) → ℝ := fun w σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t w.1.1 u
          (fun j => w.1.2.1 j.castSucc) w.1.2.2 σ
      let S_v : AuxDis[N, M] → ℝ^(N + 1) × ℝ → ℝ := fun w p =>
        Real.sqrt v * cfield[N, t, w.1.2.1, Fin.last M, p.1] +
          Real.sqrt (1 - v) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2)
      let F : AuxDis[N, M] → ℝ := fun w =>
        ∫ p : ℝ^(N + 1) × ℝ, Real.exp (p.1 (Fin.last N) ^ 2 / K)
          ∂(((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
            fun p => E_old w p.1 + u (S_v w p))
      Integrable F auxLaw[N, M, r] ∧ ∫ w, F w ∂auxLaw[N, M, r] ≤ K := by
  obtain ⟨K, hK0, hK⟩ :=
    exists_integral_exp_sq_shcherbinaTirozziCavity_indexed_last_le κ₀ h₀ D R hκ₀ hR
  refine ⟨K, hK0, fun N M κ h t v q ρ rBar r u D₂ hκ hh ht0 ht1 hv0 hv1 hrr hrR hM
    huc hu0 hu1 hu2 hD hD₂ => ?_⟩
  intro E_old S_v F
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hq_t : 0 ≤ (1 - t) * ((r : ℝ) - rBar) :=
    mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hrr)
  have hum : Measurable u := hu1.continuous.measurable
  set c : ℝ := Real.sqrt (1 - v) * Real.sqrt (ρ - q)
  obtain ⟨huv_conc, huv0, huv_diff, huv_D, -⟩ :=
    concaveOn_and_bounds_log_integral_exp_comp_add_gaussianReal huc hu0 hu1 hu2 hD hD₂ c
  set u_v : ℝ → ℝ := fun y => Real.log (∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1))
  set P₁ := (gaussianReal 0 r).prod
    ((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
      (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))
  -- Rewrite `F w` via the smoothed Hamiltonian (3.99) using `R := Unit`
  have hF_eq : ∀ w : AuxDis[N, M], F w =
      ∫ σ : ℝ^(N + 1), Real.exp (σ (Fin.last N) ^ 2 / K)
        ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          E_old w σ + u_v (Real.sqrt v * cfield[N, t, w.1.2.1, Fin.last M, σ] +
            Real.sqrt (1 - v) * Real.sqrt q * w.2)) := by
    intro w
    have hsm := integral_pi_shcherbinaTirozziAuxCavity_eq_smoothed (N := N) (M := M) (R := Unit)
      (κ := κ) (h := h) (r := r) (rBar := rBar) (t := t) (y := w.1.1) (q := q) (ρ := ρ) (v := v)
      (z := w.2) hκ0 hq_t hum hu0 w.1.2.1 w.1.2.2
      (f := fun a : Unit → ℝ^(N + 1) => Real.exp ((a () (Fin.last N)) ^ 2 / K))
      ((((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable.comp
        (measurable_pi_apply ())).pow_const 2).div_const K).exp
    have h1 := (measurePreserving_funUnique
      (((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
        fun p => E_old w p.1 + u (S_v w p)) Unit).integral_comp
      (MeasurableEquiv.funUnique Unit (ℝ^(N + 1) × ℝ)).measurableEmbedding
      (fun p : ℝ^(N + 1) × ℝ => Real.exp (p.1 (Fin.last N) ^ 2 / K))
    have h2 := (measurePreserving_funUnique
      ((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
        E_old w σ + u_v (Real.sqrt v * cfield[N, t, w.1.2.1, Fin.last M, σ] +
          Real.sqrt (1 - v) * Real.sqrt q * w.2)) Unit).integral_comp
      (MeasurableEquiv.funUnique Unit (ℝ^(N + 1))).measurableEmbedding
      (fun σ : ℝ^(N + 1) => Real.exp (σ (Fin.last N) ^ 2 / K))
    exact h1.symm.trans (hsm.trans h2)
  -- For each `z`, apply the indexed last-spin tail bound on `M + 1` potentials
  have hz_bd : ∀ z : ℝ, Integrable (fun d => F (d, z)) P₁ ∧ ∫ d, F (d, z) ∂P₁ ≤ K := by
    intro z
    set u_k : Fin (M + 1) → ℝ → ℝ :=
      Fin.snoc (fun _ : Fin M => u) (fun x => u_v (Real.sqrt v * x +
        Real.sqrt (1 - v) * Real.sqrt q * z))
    have huk_conc : ∀ k, ConcaveOn ℝ Set.univ (u_k k) := by
      refine Fin.lastCases ?_ (fun j => ?_)
      · dsimp only [u_k]; rw [Fin.snoc_last]
        refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
        have h := huv_conc.2 (Set.mem_univ (Real.sqrt v * x + Real.sqrt (1 - v) * Real.sqrt q * z))
          (Set.mem_univ (Real.sqrt v * y + Real.sqrt (1 - v) * Real.sqrt q * z)) ha hb hab
        simp only [smul_eq_mul] at h ⊢
        refine h.trans_eq (congrArg u_v ?_)
        linear_combination Real.sqrt (1 - v) * Real.sqrt q * z * hab
      · dsimp only [u_k]; rw [Fin.snoc_castSucc]; exact huc
    have huk_0 : ∀ k x, u_k k x ≤ 0 := by
      refine Fin.lastCases (fun x => ?_) (fun j x => ?_)
      · dsimp only [u_k]; rw [Fin.snoc_last]; exact huv0 _
      · dsimp only [u_k]; rw [Fin.snoc_castSucc]; exact hu0 x
    have huk_diff : ∀ k, Differentiable ℝ (u_k k) := by
      refine Fin.lastCases ?_ (fun j => ?_)
      · dsimp only [u_k]; rw [Fin.snoc_last]
        exact huv_diff.comp ((differentiable_id.const_mul _).add_const _)
      · dsimp only [u_k]; rw [Fin.snoc_castSucc]; exact hu1
    have huk_D : ∀ k x, |deriv (u_k k) x| ≤ D := by
      refine Fin.lastCases (fun x => ?_) (fun j x => ?_)
      · dsimp only [u_k]; rw [Fin.snoc_last]
        have hd : HasDerivAt (fun x => u_v (Real.sqrt v * x +
            Real.sqrt (1 - v) * Real.sqrt q * z))
            (deriv u_v (Real.sqrt v * x + Real.sqrt (1 - v) * Real.sqrt q * z) *
              Real.sqrt v) x := by
          have hlin : HasDerivAt (fun x => Real.sqrt v * x +
              Real.sqrt (1 - v) * Real.sqrt q * z) (Real.sqrt v) x := by
            simpa using ((hasDerivAt_id x).const_mul (Real.sqrt v)).add_const
              (Real.sqrt (1 - v) * Real.sqrt q * z)
          exact (huv_diff _).hasDerivAt.comp x hlin
        rw [hd.deriv, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact (mul_le_of_le_one_right (abs_nonneg _) (Real.sqrt_le_one.2 hv1)).trans (huv_D _)
      · dsimp only [u_k]; rw [Fin.snoc_castSucc]; exact hD x
    have hM1 : M + 1 ≤ 11 * (N + 1) := by omega
    have hres := hK N (M + 1) κ h t rBar r u_k hκ hh ht0 ht1 hrr hrR hM1 huk_conc huk_0
      huk_diff huk_D
    have hpt_eq : (fun d => F (d, z)) = fun p =>
        ∫ σ, Real.exp (σ (Fin.last N) ^ 2 / K)
          ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
            -(κ * ‖σ‖ ^ 2 - (∑ k, u_k k cfield[N, t, p.2.1, k, σ]) -
              h * (∑ i, p.2.2 i * σ i) - σ (Fin.last N) * (Real.sqrt (1 - t) * p.1) +
              (1 - t) * ((r : ℝ) - rBar) * σ (Fin.last N) ^ 2 / 2)) := by
      funext d
      rw [hF_eq (d, z)]
      congr 2; funext σ
      dsimp only [E_old, shcherbinaTirozziCavityHamiltonian, u_k]
      rw [Fin.sum_univ_castSucc (n := M)]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      ring
    rwa [hpt_eq]
  have hFm : Measurable F :=
    measurable_integral_tilted (measurable_auxCavity_exponent κ h r rBar t v q ρ hum)
      ((((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable.comp
        measurable_fst).pow_const 2).div_const K).exp
  have hFi : Integrable F (P₁.prod (gaussianReal 0 1)) := by
    refine (integrable_prod_iff' hFm.aestronglyMeasurable).2
      ⟨ae_of_all _ fun z => (hz_bd z).1, ?_⟩
    refine Integrable.of_bound
      (hFm.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable) K
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    refine (integral_congr_ae (ae_of_all _ fun d => ?_)).trans_le (hz_bd z).2
    exact Real.norm_of_nonneg (integral_nonneg fun _ => (Real.exp_pos _).le)
  refine ⟨hFi, ?_⟩
  rw [integral_prod_symm _ hFi]
  refine (integral_mono hFi.integral_prod_right (integrable_const K)
    fun z => (hz_bd z).2).trans_eq ?_
  rw [integral_const, probReal_univ, one_smul]

/-- **Eq. (3.101) (quenched exponential squared-norm bound along `ν_{t,v}`):** for `0 ≤ q ≤ ρ ≤ Q`,
`rBar ≤ r`, `r - rBar ≤ R_diff`, `M ≤ 10 * (N + 1)`, `κ₀ ≤ κ`, and `|h| ≤ h₀`, the quenched average
of `exp (κ ‖σ‖² / 2)` under the smoothed Hamiltonian (3.99) is bounded by
`exp (K₀ * ((N + 1) + √(∑_{k,i} g_{k,i}²) + ∑_i g₀_i² + y² + z²))`, with `K₀` depending only on
`κ₀, h₀, D, Q, R_diff` and `|u 0|`. -/
theorem exists_quenched_exp_half_sq_norm_shcherbinaTirozziAuxCavity_le_exp
    (κ₀ h₀ D Q R_diff u₀_abs : ℝ) (hκ₀ : 0 < κ₀) (hQ : 0 ≤ Q) (hR_diff : 0 ≤ R_diff) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧ ∀ (N M : ℕ) (κ h t v q ρ r rBar : ℝ) (u : ℝ → ℝ) (D₂ : ℝ)
      (w : AuxDis[N, M]),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ q → q ≤ ρ → ρ ≤ Q →
      rBar ≤ r → r - rBar ≤ R_diff → M ≤ 10 * (N + 1) → ConcaveOn ℝ Set.univ u →
      (∀ x, u x ≤ 0) → Differentiable ℝ u → Differentiable ℝ (deriv u) →
      (∀ x, |deriv u x| ≤ D) → (∀ x, |deriv (deriv u) x| ≤ D₂) → |u 0| ≤ u₀_abs →
      let E_old : ℝ^(N + 1) → ℝ := fun σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t w.1.1 u
          (fun j => w.1.2.1 j.castSucc) w.1.2.2 σ
      let u_v : ℝ → ℝ := fun y =>
        Real.log (∫ ξ, Real.exp (u (y + Real.sqrt (1 - v) * Real.sqrt (ρ - q) * ξ))
          ∂(gaussianReal 0 1))
      let G_sm : Measure (ℝ^(N + 1)) := (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
        E_old σ + u_v (Real.sqrt v * cfield[N, t, w.1.2.1, Fin.last M, σ] +
          Real.sqrt (1 - v) * Real.sqrt q * w.2)
      let B_star : ℝ := (N + 1 : ℝ) + Real.sqrt (∑ k : Fin (M + 1), ∑ i : Fin (N + 1),
        w.1.2.1 k i ^ 2) + ∑ i : Fin (N + 1), w.1.2.2 i ^ 2
      Integrable (fun σ : ℝ^(N + 1) => Real.exp (κ / 2 * ‖σ‖ ^ 2)) G_sm ∧
        ∫ σ, Real.exp (κ / 2 * ‖σ‖ ^ 2) ∂G_sm ≤
          Real.exp (K₀ * (B_star + w.1.1 ^ 2 + w.2 ^ 2)) := by
  set D_sm : ℝ := |u₀_abs| + |D| * (1 + Real.sqrt Q)
  set K₀ : ℝ := 1 + 12 * D_sm + D_sm * Real.sqrt (11 / κ₀) + D_sm * Q +
    R_diff / (4 * κ₀) + (h₀ ^ 2 + 1) / κ₀
  have hDsm0 : 0 ≤ D_sm := by positivity
  have hK₀_nn : 0 ≤ K₀ := by positivity
  refine ⟨K₀, hK₀_nn, fun N M κ h t v q ρ r rBar u D₂ w hκ hh ht0 ht1 hv0 hv1 hq0 hqρ hρQ
    hrr hrr_diff hM huc hu0 hu1 hu2 hD hD₂ hu0_abs => ?_⟩
  intro E_old u_v G_sm B_star
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  have hD_le : D ≤ |D| := le_abs_self D
  have hu0_le : |u 0| ≤ |u₀_abs| := hu0_abs.trans (le_abs_self _)
  set c : ℝ := Real.sqrt (1 - v) * Real.sqrt (ρ - q)
  have hc_abs : |c| ≤ Real.sqrt Q := by
    dsimp only [c]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_of_le_one_left (Real.sqrt_nonneg _) (Real.sqrt_le_one.2 (by linarith))).trans
      (Real.sqrt_le_sqrt (by linarith))
  obtain ⟨huv_conc, huv0, huv_diff, -, huv_low⟩ :=
    concaveOn_and_bounds_log_integral_exp_comp_add_gaussianReal huc hu0 hu1 hu2 hD hD₂ c
  have huvm : Measurable u_v := huv_diff.continuous.measurable
  have hum : Measurable u := hu1.continuous.measurable
  have hDsm_ge : |u 0| + D * (1 + |c|) ≤ D_sm := by
    dsimp only [D_sm]
    refine add_le_add hu0_le (mul_le_mul hD_le (add_le_add le_rfl hc_abs) (by positivity)
      (abs_nonneg D))
  have huv_low' : ∀ y, -D_sm * (1 + |y|) ≤ u_v y := fun y =>
    (mul_le_mul_of_nonneg_right (neg_le_neg hDsm_ge) (by positivity)).trans
      (by simpa only [neg_mul] using huv_low y)
  have hu_low' : ∀ y, -D_sm * (1 + |y|) ≤ u y := fun y => by
    have hlip : -(|u 0| + D * |y|) ≤ u y := by
      simpa only [Real.norm_eq_abs] using
        neg_le_of_abs_le (norm_le_norm_zero_add_of_norm_deriv_le hu1 hD y)
    have h1 : |u 0| + D * |y| ≤ D_sm * (1 + |y|) := by
      have h2 : |u 0| + D ≤ D_sm := by linarith [hDsm_ge, mul_nonneg hD0 (abs_nonneg c)]
      nlinarith [abs_nonneg y, hD0, abs_nonneg (u 0)]
    linarith
  -- Express the smoothed exponent in `U σ - κ ‖σ‖² + ⟪a, σ⟫` form on `ℝ^(N + 1)`
  set v_vec : Fin (M + 1) → ℝ^(N + 1) := fun k => WithLp.toLp 2 fun i =>
    (Real.sqrt (N + 1))⁻¹ * ((if i = Fin.last N then Real.sqrt t else 1) * w.1.2.1 k i)
  have hv_inner : ∀ (k : Fin (M + 1)) (σ : ℝ^(N + 1)),
      ⟪v_vec k, σ⟫ = cfield[N, t, w.1.2.1, k, σ] := by
    intro k σ
    have hcast : ∀ i : Fin N, (i.castSucc : Fin (N + 1)) ≠ Fin.last N :=
      fun i => (Fin.castSucc_lt_last i).ne
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
      Fin.sum_univ_castSucc (n := N)]
    simp only [v_vec, hcast, reduceIte, one_mul, mul_add, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · ring
  have hv_norm : ∀ k : Fin (M + 1), ‖v_vec k‖ ^ 2 ≤
      ((N : ℝ) + 1)⁻¹ * ∑ i : Fin (N + 1), w.1.2.1 k i ^ 2 := by
    intro k
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    dsimp only [v_vec]
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [mul_pow]
    refine mul_le_of_le_one_left (sq_nonneg _) ?_
    split
    · rw [Real.sq_sqrt ht0]; exact ht1
    · norm_num
  set u_k : Fin (M + 1) → ℝ → ℝ :=
    Fin.snoc (fun _ : Fin M => u) (fun x => u_v (Real.sqrt v * x +
      Real.sqrt (1 - v) * Real.sqrt q * w.2))
  set U : ℝ^(N + 1) → ℝ := fun σ => (∑ k : Fin (M + 1), u_k k ⟪v_vec k, σ⟫) -
    (1 - t) * (r - rBar) * σ (Fin.last N) ^ 2 / 2
  set a_vec : ℝ^(N + 1) := WithLp.toLp 2 fun i =>
    h * w.1.2.2 i + (if i = Fin.last N then Real.sqrt (1 - t) * w.1.1 else 0)
  have hUm : Measurable U := by
    refine (Finset.measurable_sum _ fun k _ => ?_).sub
      ((((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) (Fin.last N)).measurable.pow_const
        2).const_mul _).div_const 2)
    refine Fin.lastCases ?_ (fun j => ?_) k
    · dsimp only [u_k]; rw [Fin.snoc_last]
      exact huvm.comp (((by fun_prop : Measurable fun σ : ℝ^(N + 1) =>
        ⟪v_vec (Fin.last M), σ⟫).const_mul _).add_const _)
    · dsimp only [u_k]; rw [Fin.snoc_castSucc]
      exact hum.comp (by fun_prop : Measurable fun σ : ℝ^(N + 1) => ⟪v_vec j.castSucc, σ⟫)
  have hq_t : 0 ≤ (1 - t) * (r - rBar) := mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hrr)
  have hU0 : ∀ σ, U σ ≤ 0 := fun σ => by
    refine sub_nonpos.2 (le_trans (Finset.sum_nonpos fun k _ => ?_) ?_)
    · refine Fin.lastCases ?_ (fun j => ?_) k
      · dsimp only [u_k]; rw [Fin.snoc_last]; exact huv0 _
      · dsimp only [u_k]; rw [Fin.snoc_castSucc]; exact hu0 _
    · exact div_nonneg (mul_nonneg hq_t (sq_nonneg _)) zero_le_two
  have hexp_eq : (fun σ : ℝ^(N + 1) =>
      E_old σ + u_v (Real.sqrt v * cfield[N, t, w.1.2.1, Fin.last M, σ] +
        Real.sqrt (1 - v) * Real.sqrt q * w.2)) = fun σ => U σ - κ * ‖σ‖ ^ 2 + ⟪a_vec, σ⟫ := by
    funext σ
    have ha_in : ⟪a_vec, σ⟫ = (h * ∑ i : Fin (N + 1), w.1.2.2 i * σ i) +
        σ (Fin.last N) * (Real.sqrt (1 - t) * w.1.1) := by
      have hcast : ∀ i : Fin N, (i.castSucc : Fin (N + 1)) ≠ Fin.last N :=
        fun i => (Fin.castSucc_lt_last i).ne
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
        Fin.sum_univ_castSucc (n := N), Fin.sum_univ_castSucc (n := N)]
      simp only [a_vec, hcast, reduceIte, add_zero, mul_add, Finset.mul_sum]
      have hsum_eq : ∑ i : Fin N, σ i.castSucc * (h * w.1.2.2 i.castSucc) =
          ∑ i : Fin N, h * (w.1.2.2 i.castSucc * σ i.castSucc) :=
        Finset.sum_congr rfl fun i _ => by ring
      rw [hsum_eq]
      ring
    dsimp only [E_old, shcherbinaTirozziCavityHamiltonian, U, u_k]
    rw [ha_in, Fin.sum_univ_castSucc (n := M)]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, hv_inner]
    ring
  -- Bound `-𝔼_{z₀ ~ stdGaussian (ℝ^(N+1))} U (s_κ • z₀)` and `‖a_vec‖² / (2 κ)`
  set s_κ : ℝ := (Real.sqrt (2 * κ))⁻¹
  have hsκ0 : 0 < s_κ := inv_pos.2 (Real.sqrt_pos.2 (by positivity))
  have hlin_i : ∀ b : ℝ^(N + 1), Integrable (fun z₀ : ℝ^(N + 1) => ⟪b, z₀⟫)
      (stdGaussian (ℝ^(N + 1))) := fun b =>
    (IsGaussian.memLp_dual (stdGaussian (ℝ^(N + 1))) (innerSL ℝ b) 1
      (by norm_num)).integrable le_rfl
  have hk_low : ∀ (k : Fin (M + 1)) (z₀ : ℝ^(N + 1)),
      -(D_sm * ((1 + (if k = Fin.last M then Real.sqrt q * |w.2| else 0)) +
        s_κ * |⟪v_vec k, z₀⟫|)) ≤ u_k k ⟪v_vec k, s_κ • z₀⟫ := by
    intro k z₀
    rw [real_inner_smul_right]
    refine Fin.lastCases ?_ (fun j => ?_) k
    · dsimp only [u_k]; simp only [Fin.snoc_last, reduceIte]
      refine le_trans ?_ (huv_low' _)
      rw [neg_mul]
      refine neg_le_neg (mul_le_mul_of_nonneg_left ?_ hDsm0)
      have h1 : |Real.sqrt v * (s_κ * ⟪v_vec (Fin.last M), z₀⟫) +
          Real.sqrt (1 - v) * Real.sqrt q * w.2| ≤
          s_κ * |⟪v_vec (Fin.last M), z₀⟫| + Real.sqrt q * |w.2| := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos hsκ0]
          exact mul_le_of_le_one_left (by positivity) (Real.sqrt_le_one.2 hv1)
        · rw [mul_assoc, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
            abs_of_nonneg (Real.sqrt_nonneg _)]
          exact mul_le_of_le_one_left (by positivity) (Real.sqrt_le_one.2 (by linarith))
      linarith
    · have hne : j.castSucc ≠ Fin.last M := (Fin.castSucc_lt_last j).ne
      dsimp only [u_k]; simp only [Fin.snoc_castSucc, hne, reduceIte, add_zero]
      refine le_trans ?_ (hu_low' _)
      rw [abs_mul, abs_of_pos hsκ0, neg_mul]
  have hk_int : ∀ k : Fin (M + 1),
      Integrable (fun z₀ : ℝ^(N + 1) => u_k k ⟪v_vec k, s_κ • z₀⟫) (stdGaussian (ℝ^(N + 1))) ∧
      -(D_sm * ((1 + (if k = Fin.last M then Real.sqrt q * |w.2| else 0)) +
        s_κ * ‖v_vec k‖)) ≤ ∫ z₀, u_k k ⟪v_vec k, s_κ • z₀⟫ ∂(stdGaussian (ℝ^(N + 1))) := by
    intro k
    set maj : ℝ^(N + 1) → ℝ := fun z₀ =>
      D_sm * ((1 + (if k = Fin.last M then Real.sqrt q * |w.2| else 0)) +
        s_κ * |⟪v_vec k, z₀⟫|)
    have hmaj_i : Integrable maj (stdGaussian (ℝ^(N + 1))) :=
      ((integrable_const _).add ((hlin_i (v_vec k)).abs.const_mul s_κ)).const_mul D_sm
    have huk_m : Measurable fun z₀ : ℝ^(N + 1) => u_k k ⟪v_vec k, s_κ • z₀⟫ := by
      refine Fin.lastCases ?_ (fun j => ?_) k
      · dsimp only [u_k]; rw [Fin.snoc_last]
        exact huvm.comp (((by fun_prop : Measurable fun z₀ : ℝ^(N + 1) =>
          ⟪v_vec (Fin.last M), s_κ • z₀⟫).const_mul _).add_const _)
      · dsimp only [u_k]; rw [Fin.snoc_castSucc]
        exact hum.comp (by fun_prop : Measurable fun z₀ : ℝ^(N + 1) =>
          ⟪v_vec j.castSucc, s_κ • z₀⟫)
    have huk_0 : ∀ z₀, u_k k ⟪v_vec k, s_κ • z₀⟫ ≤ 0 := fun z₀ => by
      refine Fin.lastCases ?_ (fun j => ?_) k
      · dsimp only [u_k]; rw [Fin.snoc_last]; exact huv0 _
      · dsimp only [u_k]; rw [Fin.snoc_castSucc]; exact hu0 _
    have hi : Integrable (fun z₀ : ℝ^(N + 1) => u_k k ⟪v_vec k, s_κ • z₀⟫)
        (stdGaussian (ℝ^(N + 1))) :=
      hmaj_i.mono' huk_m.aestronglyMeasurable (ae_of_all _ fun z₀ => by
        rw [Real.norm_eq_abs, abs_of_nonpos (huk_0 z₀)]
        linarith [hk_low k z₀])
    refine ⟨hi, ?_⟩
    have h1 := integral_mono hmaj_i.neg hi fun z₀ => hk_low k z₀
    simp only [Pi.neg_apply, integral_neg] at h1
    have hmaj_int : ∫ z₀, maj z₀ ∂(stdGaussian (ℝ^(N + 1))) ≤
        D_sm * ((1 + (if k = Fin.last M then Real.sqrt q * |w.2| else 0)) +
          s_κ * ‖v_vec k‖) := by
      dsimp only [maj]
      rw [integral_const_mul, integral_add (integrable_const _)
        ((hlin_i (v_vec k)).abs.const_mul s_κ), integral_const, probReal_univ, one_smul,
        integral_const_mul]
      have h2 := sq_norm_integral_le_integral_sq_norm (μ := stdGaussian (ℝ^(N + 1)))
        (f := fun z₀ : ℝ^(N + 1) => |⟪v_vec k, z₀⟫|)
        (IsGaussian.memLp_dual (stdGaussian (ℝ^(N + 1))) (innerSL ℝ (v_vec k)) 2 (by norm_num)).abs
      have h3 : ∫ z₀ : ℝ^(N + 1), ‖|⟪v_vec k, z₀⟫|‖ ^ 2 ∂(stdGaussian (ℝ^(N + 1))) =
          ‖v_vec k‖ ^ 2 := by
        simp only [Real.norm_eq_abs, abs_abs, sq_abs]
        have hv := variance_dual_stdGaussian (innerSL ℝ (v_vec k))
        have hm := integral_strongDual_stdGaussian (innerSL ℝ (v_vec k))
        rw [variance_eq_integral (IsGaussian.memLp_dual (stdGaussian (ℝ^(N + 1)))
          (innerSL ℝ (v_vec k)) 2 (by norm_num)).aemeasurable] at hv
        simp only [innerSL_apply_apply, innerSL_apply_norm] at hm hv
        rw [hm] at hv
        simpa using hv
      rw [h3, Real.norm_of_nonneg (integral_nonneg fun _ => abs_nonneg _)] at h2
      have h_abs_le : ∫ z₀ : ℝ^(N + 1), |⟪v_vec k, z₀⟫| ∂(stdGaussian (ℝ^(N + 1))) ≤
          ‖v_vec k‖ := by
        nlinarith [norm_nonneg (v_vec k),
          integral_nonneg (μ := stdGaussian (ℝ^(N + 1))) fun z₀ : ℝ^(N + 1) =>
            abs_nonneg ⟪v_vec k, z₀⟫]
      exact mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left h_abs_le hsκ0.le)) hDsm0
    linarith
  -- Integrability and expectation of the last-spin quadratic penalty under `stdGaussian (ℝ^(N+1))`
  have hlast_z : Integrable (fun z₀ : ℝ^(N + 1) => (s_κ • z₀) (Fin.last N) ^ 2)
        (stdGaussian (ℝ^(N + 1))) ∧
      ∫ z₀ : ℝ^(N + 1), (s_κ • z₀) (Fin.last N) ^ 2 ∂(stdGaussian (ℝ^(N + 1))) = s_κ ^ 2 := by
    set L_last : StrongDual ℝ (ℝ^(N + 1)) :=
      (EuclideanSpace.proj (Fin.last N) : ℝ^(N + 1) →L[ℝ] ℝ)
    have hL2 := IsGaussian.memLp_dual (stdGaussian (ℝ^(N + 1))) L_last 2 (by norm_num)
    have heq_fn : (fun z₀ : ℝ^(N + 1) => (s_κ • z₀) (Fin.last N) ^ 2) =
        fun z₀ => s_κ ^ 2 * (L_last z₀) ^ 2 := by
      funext z₀
      change (s_κ * z₀ (Fin.last N)) ^ 2 = s_κ ^ 2 * (z₀ (Fin.last N)) ^ 2
      ring
    rw [heq_fn]
    refine ⟨hL2.integrable_sq.const_mul _, ?_⟩
    rw [integral_const_mul]
    have hmp : MeasurePreserving (fun z₀ : ℝ^(N + 1) => z₀ (Fin.last N))
        (stdGaussian (ℝ^(N + 1))) (gaussianReal 0 1) := by
      have h1 : MeasurePreserving (fun z₀ : ℝ^(N + 1) => z₀.ofLp) (stdGaussian (ℝ^(N + 1)))
          (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1) :=
        ⟨WithLp.measurable_ofLp 2 _, pi_gaussianReal_eq_map_stdGaussian.symm⟩
      exact (measurePreserving_eval (fun _ : Fin (N + 1) => gaussianReal 0 1)
        (Fin.last N)).comp h1
    have h1_int : ∫ z₀ : ℝ^(N + 1), (L_last z₀) ^ 2 ∂(stdGaussian (ℝ^(N + 1))) = 1 := by
      change ∫ z₀ : ℝ^(N + 1), (fun x : ℝ => x ^ 2) (z₀ (Fin.last N)) ∂(stdGaussian (ℝ^(N + 1))) = 1
      rw [hmp.integral_comp_of_aestronglyMeasurable
        (continuous_pow 2).measurable.aestronglyMeasurable]
      simpa using integral_pow_add_two_gaussianReal 0
    rw [h1_int, mul_one]
  have hUi : Integrable (fun z₀ : ℝ^(N + 1) => U (s_κ • z₀)) (stdGaussian (ℝ^(N + 1))) := by
    refine (integrable_finsetSum _ fun k _ => (hk_int k).1).sub ?_
    exact (hlast_z.1.const_mul ((1 - t) * (r - rBar))).div_const 2
  -- Apply `integral_exp_half_sq_norm_tilted_le_two_rpow`
  have hkey := integral_exp_half_sq_norm_tilted_le_two_rpow hUm hU0 hκ0 a_vec hUi
  rw [finrank_euclideanSpace_fin, ← hexp_eq] at hkey
  refine ⟨hkey.1, hkey.2.trans ?_⟩
  -- Bound `2^((N+1)/2)` by `exp (N + 1)`, `‖a_vec‖² / (2 κ)`, and `-𝔼 U(s_κ • z₀)`
  have h2pow : (2 : ℝ) ^ (((N + 1 : ℕ) : ℝ) / 2) ≤ Real.exp (N + 1 : ℝ) := by
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    refine (Real.rpow_le_rpow zero_le_two h2e (by positivity)).trans ?_
    rw [Real.exp_one_rpow, Real.exp_le_exp]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have ha_sq : ‖a_vec‖ ^ 2 / (2 * κ) ≤
      (h₀ ^ 2 / κ₀) * (∑ i : Fin (N + 1), w.1.2.2 i ^ 2) + (1 / κ₀) * w.1.1 ^ 2 := by
    have han : ‖a_vec‖ ^ 2 ≤
        2 * h₀ ^ 2 * (∑ i : Fin (N + 1), w.1.2.2 i ^ 2) + 2 * w.1.1 ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      have hpt : ∀ i : Fin (N + 1), a_vec i ^ 2 ≤
          2 * h₀ ^ 2 * w.1.2.2 i ^ 2 +
            (if i = Fin.last N then 2 * w.1.1 ^ 2 else 0) := fun i => by
        dsimp only [a_vec]
        have hh2 : (h * w.1.2.2 i) ^ 2 ≤ h₀ ^ 2 * w.1.2.2 i ^ 2 := by
          rw [mul_pow, ← sq_abs h]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hh 2) (sq_nonneg _)
        split
        · have h1t : (Real.sqrt (1 - t) * w.1.1) ^ 2 ≤ w.1.1 ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (by linarith)]
            exact mul_le_of_le_one_left (sq_nonneg _) (by linarith)
          refine add_sq_le.trans ?_
          rw [mul_add, mul_assoc 2]
          exact add_le_add (mul_le_mul_of_nonneg_left hh2 zero_le_two)
            (mul_le_mul_of_nonneg_left h1t zero_le_two)
        · simp only [add_zero]
          have hnn : 0 ≤ h₀ ^ 2 * w.1.2.2 i ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
          linarith [hh2, hnn]
      refine (Finset.sum_le_sum fun i _ => hpt i).trans ?_
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    have hdiv : ‖a_vec‖ ^ 2 / (2 * κ) ≤ ‖a_vec‖ ^ 2 / (2 * κ₀) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
    refine hdiv.trans ?_
    calc ‖a_vec‖ ^ 2 / (2 * κ₀)
        ≤ (2 * h₀ ^ 2 * (∑ i : Fin (N + 1), w.1.2.2 i ^ 2) + 2 * w.1.1 ^ 2) / (2 * κ₀) :=
          div_le_div_of_nonneg_right han (by positivity)
      _ = (h₀ ^ 2 / κ₀) * (∑ i : Fin (N + 1), w.1.2.2 i ^ 2) + (1 / κ₀) * w.1.1 ^ 2 := by
          field_simp
  have hU_neg : -(∫ z₀ : ℝ^(N + 1), U (s_κ • z₀) ∂(stdGaussian (ℝ^(N + 1)))) ≤
      (12 * D_sm + R_diff / (4 * κ₀)) * ((N : ℝ) + 1) + D_sm * Real.sqrt (11 / κ₀) *
        Real.sqrt (∑ k : Fin (M + 1), ∑ i : Fin (N + 1), w.1.2.1 k i ^ 2) +
      D_sm * Q * w.2 ^ 2 := by
    dsimp only [U]
    rw [integral_sub (integrable_finsetSum _ fun k _ => (hk_int k).1)
      ((hlast_z.1.const_mul _).div_const 2), integral_finsetSum _ fun k _ => (hk_int k).1, neg_sub]
    have hlast_eq : ∫ z₀ : ℝ^(N + 1), (1 - t) * (r - rBar) * (s_κ • z₀) (Fin.last N) ^ 2 / 2
        ∂(stdGaussian (ℝ^(N + 1))) = (1 - t) * (r - rBar) / (4 * κ) := by
      have he : (fun z₀ : ℝ^(N + 1) => (1 - t) * (r - rBar) * (s_κ • z₀) (Fin.last N) ^ 2 / 2) =
          fun z₀ => ((1 - t) * (r - rBar) / 2) * (s_κ • z₀) (Fin.last N) ^ 2 := by
        funext z₀; ring
      rw [he, integral_const_mul, hlast_z.2]
      dsimp only [s_κ]
      rw [inv_pow, Real.sq_sqrt (by positivity)]
      ring
    have hlast_le : (1 - t) * (r - rBar) / (4 * κ) ≤ (R_diff / (4 * κ₀)) * ((N : ℝ) + 1) := by
      have h1 : (1 - t) * (r - rBar) ≤ R_diff :=
        (mul_le_of_le_one_left (sub_nonneg.2 hrr) (by linarith)).trans hrr_diff
      have h2 : (1 - t) * (r - rBar) / (4 * κ) ≤ R_diff / (4 * κ₀) :=
        div_le_div₀ hR_diff h1 (by positivity) (by linarith)
      exact h2.trans (le_mul_of_one_le_right (by positivity)
        (le_add_of_nonneg_left (Nat.cast_nonneg N)))
    have hsum_k : -(∑ k : Fin (M + 1),
          ∫ z₀ : ℝ^(N + 1), u_k k ⟪v_vec k, s_κ • z₀⟫ ∂(stdGaussian (ℝ^(N + 1)))) ≤
        D_sm * (((M : ℝ) + 1) + Real.sqrt q * |w.2| + s_κ * ∑ k : Fin (M + 1), ‖v_vec k‖) := by
      rw [← Finset.sum_neg_distrib]
      refine (Finset.sum_le_sum fun (k : Fin (M + 1)) _ => neg_le.2 (hk_int k).2).trans_eq ?_
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, reduceIte]
      push_cast; ring
    have hCS_v : s_κ * ∑ k : Fin (M + 1), ‖v_vec k‖ ≤
        Real.sqrt (11 / κ₀) *
          Real.sqrt (∑ k : Fin (M + 1), ∑ i : Fin (N + 1), w.1.2.1 k i ^ 2) := by
      obtain ⟨S_m, hSm⟩ : ∃ S_m : ℝ,
          S_m = ∑ k : Fin (M + 1), ∑ i : Fin (N + 1), w.1.2.1 k i ^ 2 := ⟨_, rfl⟩
      rw [← hSm]
      have hS0 : 0 ≤ S_m := by
        rw [hSm]; exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hsq1 : (∑ k : Fin (M + 1), ‖v_vec k‖) ^ 2 ≤
          (((M : ℝ) + 1) / ((N : ℝ) + 1)) * S_m := by
        have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => ‖v_vec k‖)
        simp only [Finset.card_univ, Fintype.card_fin] at hcs
        have hv_s : ∑ k : Fin (M + 1), ‖v_vec k‖ ^ 2 ≤ ((N : ℝ) + 1)⁻¹ * S_m := by
          rw [hSm, Finset.mul_sum]
          exact Finset.sum_le_sum fun k _ => hv_norm k
        refine hcs.trans ((mul_le_mul_of_nonneg_left hv_s (by positivity)).trans_eq ?_)
        push_cast; ring
      have hMN : ((M : ℝ) + 1) / ((N : ℝ) + 1) ≤ 11 := by
        rw [div_le_iff₀ (by positivity)]
        have : M + 1 ≤ 11 * (N + 1) := by omega
        exact_mod_cast this
      have hsκ_le : s_κ ^ 2 ≤ (2 * κ₀)⁻¹ := by
        dsimp only [s_κ]
        rw [inv_pow, Real.sq_sqrt (by positivity)]
        exact inv_anti₀ (by positivity) (by linarith)
      refine (Real.le_sqrt_of_sq_le ?_).trans_eq (Real.sqrt_mul (by positivity) S_m)
      rw [mul_pow]
      calc s_κ ^ 2 * (∑ k : Fin (M + 1), ‖v_vec k‖) ^ 2
          ≤ (2 * κ₀)⁻¹ * (11 * S_m) :=
            mul_le_mul hsκ_le (hsq1.trans (mul_le_mul_of_nonneg_right hMN hS0))
              (sq_nonneg _) (by positivity)
        _ = ((2 * κ₀)⁻¹ * 11) * S_m := by ring
        _ ≤ (11 / κ₀) * S_m := by
            refine mul_le_mul_of_nonneg_right ?_ hS0
            rw [inv_mul_eq_div]
            exact div_le_div_of_nonneg_left (by norm_num) hκ₀ (by linarith)
    have hqz : Real.sqrt q * |w.2| ≤ 1 + Q * w.2 ^ 2 := by
      have h1 : 2 * (Real.sqrt q * |w.2|) ≤ 1 + q * w.2 ^ 2 := by
        have hsq := sq_nonneg (Real.sqrt q * |w.2| - 1)
        rw [sub_sq, mul_pow, Real.sq_sqrt hq0, sq_abs] at hsq
        linarith
      have h2 : q * w.2 ^ 2 ≤ Q * w.2 ^ 2 :=
        mul_le_mul_of_nonneg_right (hqρ.trans hρQ) (sq_nonneg _)
      have hnn : 0 ≤ Real.sqrt q * |w.2| := by positivity
      linarith
    have hM1_le : ((M : ℝ) + 1) + 1 ≤ 12 * ((N : ℝ) + 1) := by
      have : M + 2 ≤ 12 * (N + 1) := by omega
      have hcast : ((M + 2 : ℕ) : ℝ) ≤ ((12 * (N + 1) : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at hcast
      linarith
    have hD_part :
        D_sm * (((M : ℝ) + 1) + Real.sqrt q * |w.2| + s_κ * ∑ k : Fin (M + 1), ‖v_vec k‖) ≤
        12 * D_sm * ((N : ℝ) + 1) + D_sm * Real.sqrt (11 / κ₀) *
          Real.sqrt (∑ k : Fin (M + 1), ∑ i : Fin (N + 1), w.1.2.1 k i ^ 2) +
        D_sm * Q * w.2 ^ 2 := by
      have hcomb := mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (le_refl ((M : ℝ) + 1)) hqz) hCS_v) hDsm0
      have hM_mul := mul_le_mul_of_nonneg_left hM1_le hDsm0
      linarith
    rw [hlast_eq, sub_eq_add_neg]
    linarith [hlast_le, hsum_k, hD_part]
  -- Combine `h2pow`, `ha_sq`, and `hU_neg` into `exp (K₀ * (B_star + w.1.1 ^ 2 + w.2 ^ 2))`
  obtain ⟨I_U, hIU⟩ : ∃ I_U : ℝ,
      I_U = ∫ z₀ : ℝ^(N + 1), U (s_κ • z₀) ∂(stdGaussian (ℝ^(N + 1))) := ⟨_, rfl⟩
  rw [← hIU] at hU_neg ⊢
  obtain ⟨S_mat, hS_mat⟩ : ∃ S_mat : ℝ,
      S_mat = Real.sqrt (∑ k : Fin (M + 1), ∑ i : Fin (N + 1), w.1.2.1 k i ^ 2) := ⟨_, rfl⟩
  obtain ⟨S_g0, hS_g0⟩ : ∃ S_g0 : ℝ, S_g0 = ∑ i : Fin (N + 1), w.1.2.2 i ^ 2 := ⟨_, rfl⟩
  have hB_eq : B_star = ((N : ℝ) + 1) + S_mat + S_g0 := by
    dsimp only [B_star]; rw [← hS_mat, ← hS_g0]
  rw [← hS_mat] at hU_neg
  rw [← hS_g0] at ha_sq
  have hN_nn : 0 ≤ (N : ℝ) + 1 := by positivity
  have hS_nn : 0 ≤ S_mat := by rw [hS_mat]; exact Real.sqrt_nonneg _
  have hg0_nn : 0 ≤ S_g0 := by rw [hS_g0]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hy_nn : 0 ≤ w.1.1 ^ 2 := sq_nonneg _
  have hz_nn : 0 ≤ w.2 ^ 2 := sq_nonneg _
  have hc_pos : 0 ≤ D_sm * Real.sqrt (11 / κ₀) + D_sm * Q + (h₀ ^ 2 + 1) / κ₀ := by positivity
  have hc_pos2 : 0 ≤ 1 + 12 * D_sm + D_sm * Q + R_diff / (4 * κ₀) + (h₀ ^ 2 + 1) / κ₀ := by
    positivity
  have hc_pos3 : 0 ≤ 1 + 12 * D_sm + D_sm * Real.sqrt (11 / κ₀) + R_diff / (4 * κ₀) +
      (h₀ ^ 2 + 1) / κ₀ := by positivity
  have hc_pos4 : 0 ≤ 1 + 12 * D_sm + D_sm * Real.sqrt (11 / κ₀) + D_sm * Q +
      R_diff / (4 * κ₀) := by positivity
  have h1 : (1 + 12 * D_sm + R_diff / (4 * κ₀)) * ((N : ℝ) + 1) ≤ K₀ * ((N : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right (by dsimp only [K₀]; linarith) hN_nn
  have h2 : (D_sm * Real.sqrt (11 / κ₀)) * S_mat ≤ K₀ * S_mat :=
    mul_le_mul_of_nonneg_right (by dsimp only [K₀]; linarith) hS_nn
  have h3 : (h₀ ^ 2 / κ₀) * S_g0 ≤ K₀ * S_g0 :=
    mul_le_mul_of_nonneg_right (by
      have : h₀ ^ 2 / κ₀ ≤ (h₀ ^ 2 + 1) / κ₀ :=
        div_le_div_of_nonneg_right (by linarith) hκ₀.le
      dsimp only [K₀]; linarith) hg0_nn
  have h4 : (1 / κ₀) * w.1.1 ^ 2 ≤ K₀ * w.1.1 ^ 2 :=
    mul_le_mul_of_nonneg_right (by
      have : 1 / κ₀ ≤ (h₀ ^ 2 + 1) / κ₀ :=
        div_le_div_of_nonneg_right (by linarith [sq_nonneg h₀]) hκ₀.le
      dsimp only [K₀]; linarith) hy_nn
  have h5 : (D_sm * Q) * w.2 ^ 2 ≤ K₀ * w.2 ^ 2 :=
    mul_le_mul_of_nonneg_right (by dsimp only [K₀]; linarith) hz_nn
  calc (2 : ℝ) ^ (((N + 1 : ℕ) : ℝ) / 2) * Real.exp (‖a_vec‖ ^ 2 / (2 * κ) - I_U)
      ≤ Real.exp (N + 1 : ℝ) * Real.exp (‖a_vec‖ ^ 2 / (2 * κ) + -I_U) := by
        rw [sub_eq_add_neg]
        exact mul_le_mul_of_nonneg_right h2pow (Real.exp_pos _).le
    _ = Real.exp (((N : ℝ) + 1) + ‖a_vec‖ ^ 2 / (2 * κ) + -I_U) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (K₀ * (B_star + w.1.1 ^ 2 + w.2 ^ 2)) := by
        rw [Real.exp_le_exp, hB_eq]
        linarith [ha_sq, hU_neg, h1, h2, h3, h4, h5]

/-- **Eq. (3.102):** along `ν_{t,v}`, `ν_{t,v}(exp (‖σ‖² / K₁)) ≤ exp (L (N + 1))` uniformly in
`N, M, t, v` and in `0 ≤ q ≤ ρ ≤ Q`, `rBar ≤ r ≤ R`, `r - rBar ≤ R_diff`, with positive constants
`K₁, L` depending only on `κ₀, h₀, D, Q, R, R_diff` and `|u 0|`. -/
theorem exists_integral_exp_sq_norm_shcherbinaTirozziAuxCavity_le_exp
    (κ₀ h₀ D Q R R_diff u₀_abs : ℝ) (hκ₀ : 0 < κ₀) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (hR_diff : 0 ≤ R_diff) :
    ∃ K₁ L : ℝ, 0 < K₁ ∧ 0 < L ∧ ∀ (N M : ℕ) (κ h t v q ρ rBar : ℝ) (r : ℝ≥0)
      (u : ℝ → ℝ) (D₂ : ℝ),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ q → q ≤ ρ → ρ ≤ Q →
      rBar ≤ r → (r : ℝ) ≤ R → (r : ℝ) - rBar ≤ R_diff → M ≤ 10 * (N + 1) →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → Differentiable ℝ u →
      Differentiable ℝ (deriv u) → (∀ x, |deriv u x| ≤ D) →
      (∀ x, |deriv (deriv u) x| ≤ D₂) → |u 0| ≤ u₀_abs →
      let E_old : AuxDis[N, M] → ℝ^(N + 1) → ℝ := fun w σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t w.1.1 u
          (fun j => w.1.2.1 j.castSucc) w.1.2.2 σ
      let S_v : AuxDis[N, M] → ℝ^(N + 1) × ℝ → ℝ := fun w p =>
        Real.sqrt v * cfield[N, t, w.1.2.1, Fin.last M, p.1] +
          Real.sqrt (1 - v) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2)
      let F : AuxDis[N, M] → ℝ := fun w =>
        ∫ p : ℝ^(N + 1) × ℝ, Real.exp (‖p.1‖ ^ 2 / K₁)
          ∂(((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
            fun p => E_old w p.1 + u (S_v w p))
      Integrable F auxLaw[N, M, r] ∧ ∫ w, F w ∂auxLaw[N, M, r] ≤ Real.exp (L * (N + 1)) := by
  obtain ⟨K₀, hK₀_nn, hK₀⟩ :=
    exists_quenched_exp_half_sq_norm_shcherbinaTirozziAuxCavity_le_exp κ₀ h₀ D Q R_diff u₀_abs
      hκ₀ hQ hR_diff
  set K₁ : ℝ := 8 * (K₀ + 1) * (R + 1) / κ₀
  set L : ℝ := 7
  have hK₁_pos : 0 < K₁ := by positivity
  have hL_pos : 0 < L := by norm_num
  refine ⟨K₁, L, hK₁_pos, hL_pos, fun N M κ h t v q ρ rBar r u D₂ hκ hh ht0 ht1 hv0 hv1 hq0 hqρ
    hρQ hrr hrR hrr_diff hM huc hu0 hu1 hu2 hD hD₂ hu0_abs => ?_⟩
  intro E_old S_v F
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum : Measurable u := hu1.continuous.measurable
  have hq_t : 0 ≤ (1 - t) * ((r : ℝ) - rBar) :=
    mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hrr)
  set u_v : ℝ → ℝ := fun y =>
    Real.log (∫ ξ, Real.exp (u (y + Real.sqrt (1 - v) * Real.sqrt (ρ - q) * ξ))
      ∂(gaussianReal 0 1))
  -- Rewrite `F w` via the smoothed Hamiltonian (3.99)
  have hF_eq : ∀ w : AuxDis[N, M], F w =
      ∫ σ : ℝ^(N + 1), Real.exp (‖σ‖ ^ 2 / K₁)
        ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          E_old w σ + u_v (Real.sqrt v * cfield[N, t, w.1.2.1, Fin.last M, σ] +
            Real.sqrt (1 - v) * Real.sqrt q * w.2)) := by
    intro w
    have hsm := integral_pi_shcherbinaTirozziAuxCavity_eq_smoothed (N := N) (M := M) (R := Unit)
      (κ := κ) (h := h) (r := r) (rBar := rBar) (t := t) (y := w.1.1) (q := q) (ρ := ρ) (v := v)
      (z := w.2) hκ0 hq_t hum hu0 w.1.2.1 w.1.2.2
      (f := fun a : Unit → ℝ^(N + 1) => Real.exp (‖a ()‖ ^ 2 / K₁))
      ((((continuous_norm (E := ℝ^(N + 1))).measurable.comp (measurable_pi_apply ())).pow_const
        2).div_const K₁).exp
    have h1 := (measurePreserving_funUnique
      (((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
        fun p => E_old w p.1 + u (S_v w p)) Unit).integral_comp
      (MeasurableEquiv.funUnique Unit (ℝ^(N + 1) × ℝ)).measurableEmbedding
      (fun p : ℝ^(N + 1) × ℝ => Real.exp (‖p.1‖ ^ 2 / K₁))
    have h2 := (measurePreserving_funUnique
      ((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
        E_old w σ + u_v (Real.sqrt v * cfield[N, t, w.1.2.1, Fin.last M, σ] +
          Real.sqrt (1 - v) * Real.sqrt q * w.2)) Unit).integral_comp
      (MeasurableEquiv.funUnique Unit (ℝ^(N + 1))).measurableEmbedding
      (fun σ : ℝ^(N + 1) => Real.exp (‖σ‖ ^ 2 / K₁))
    exact h1.symm.trans (hsm.trans h2)
  -- Pointwise quenched bound via `integral_rpow_le_rpow_integral` with `p = 2 / (κ * K₁)`
  set p_exp : ℝ := 2 / (κ * K₁)
  have hp_pos : 0 < p_exp := by positivity
  have hp_le1 : p_exp ≤ 1 := by
    dsimp only [p_exp, K₁]
    rw [div_le_one (by positivity)]
    have h1 : (1 : ℝ) ≤ (K₀ + 1) * (R + 1) := by nlinarith
    have h2 : κ₀ ≤ κ := hκ
    have h3 : (8 * (K₀ + 1) * (R + 1) / κ₀) * κ ≥ 8 * (K₀ + 1) * (R + 1) := by
      rw [div_mul_eq_mul_div, ge_iff_le, le_div_iff₀ hκ₀]
      nlinarith
    linarith
  obtain ⟨huv_conc, huv0, huv_diff, -, -⟩ :=
    concaveOn_and_bounds_log_integral_exp_comp_add_gaussianReal huc hu0 hu1 hu2 hD hD₂
      (Real.sqrt (1 - v) * Real.sqrt (ρ - q))
  have huvm : Measurable u_v := huv_diff.continuous.measurable
  have hpt_w : ∀ w : AuxDis[N, M], F w ≤
      Real.exp ((((N : ℝ) + 1) + Real.sqrt (∑ k : Fin (M + 1), ∑ i : Fin (N + 1), w.1.2.1 k i ^ 2)
          + ∑ i : Fin (N + 1), w.1.2.2 i ^ 2) / 4) *
        Real.exp ((4 * (R + 1))⁻¹ * w.1.1 ^ 2) * Real.exp ((1 / 4 : ℝ) * w.2 ^ 2) := by
    intro w
    set G_sm : Measure (ℝ^(N + 1)) := (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
      E_old w σ + u_v (Real.sqrt v * cfield[N, t, w.1.2.1, Fin.last M, σ] +
        Real.sqrt (1 - v) * Real.sqrt q * w.2)
    have hG_prob : IsProbabilityMeasure G_sm := by
      refine isProbabilityMeasure_tilted ?_
      have hEold_i := integrable_exp_neg_shcherbinaTirozziCavityHamiltonian (κ := κ) (h := h)
        (r := r) (rBar := rBar) (t := t) (y := w.1.1) hκ0 hq_t hum hu0
        (fun j => w.1.2.1 j.castSucc) w.1.2.2
      have hEm : Measurable fun σ : ℝ^(N + 1) =>
          E_old w σ + u_v (Real.sqrt v * cfield[N, t, w.1.2.1, Fin.last M, σ] +
            Real.sqrt (1 - v) * Real.sqrt q * w.2) := by
        have hold := (measurable_shcherbinaTirozziCavityHamiltonian_apply κ h r rBar t w.1.1 hum
          (fun j => w.1.2.1 j.castSucc) w.1.2.2).neg
        have hσ : ∀ i : Fin (N + 1), Measurable fun σ : ℝ^(N + 1) => σ i := fun i =>
          (PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) i).measurable
        have hcf : Measurable fun σ : ℝ^(N + 1) => cfield[N, t, w.1.2.1, Fin.last M, σ] :=
          (((Finset.measurable_sum _ fun i _ => (hσ i.castSucc).const_mul _).add
            (((hσ (Fin.last N)).const_mul _).const_mul _)).const_mul _)
        exact hold.add (huvm.comp ((hcf.const_mul _).add_const _))
      exact hEold_i.mono' hEm.exp.aestronglyMeasurable (ae_of_all _ fun σ => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_add]
        exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.exp_le_one_iff.2 (huv0 _)))
    obtain ⟨hq_int, hq_le⟩ := hK₀ N M κ h t v q ρ r rBar u D₂ w hκ hh ht0 ht1 hv0 hv1 hq0 hqρ hρQ
      hrr hrr_diff hM huc hu0 hu1 hu2 hD hD₂ hu0_abs
    have hj := (integral_rpow_le_rpow_integral (μ := G_sm) hp_pos.le hp_le1
      (ae_of_all _ fun _ => (Real.exp_pos _).le) hq_int).2
    have hpow_eq : ∀ σ : ℝ^(N + 1),
        (Real.exp (κ / 2 * ‖σ‖ ^ 2)) ^ p_exp = Real.exp (‖σ‖ ^ 2 / K₁) := fun σ => by
      rw [← Real.exp_mul]
      congr 1; dsimp only [p_exp]; field_simp
    simp_rw [hpow_eq] at hj
    rw [hF_eq w]
    set B_w : ℝ := ((N : ℝ) + 1) +
      Real.sqrt (∑ k : Fin (M + 1), ∑ i : Fin (N + 1), w.1.2.1 k i ^ 2) +
      ∑ i : Fin (N + 1), w.1.2.2 i ^ 2
    have hB_nn : 0 ≤ B_w :=
      add_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hrpow_le : (∫ σ, Real.exp (κ / 2 * ‖σ‖ ^ 2) ∂G_sm) ^ p_exp ≤
        Real.exp (p_exp * K₀ * (B_w + w.1.1 ^ 2 + w.2 ^ 2)) := by
      refine (Real.rpow_le_rpow (integral_nonneg fun _ => (Real.exp_pos _).le) hq_le
        hp_pos.le).trans_eq ?_
      rw [← Real.exp_mul]; ring_nf
    refine (hj.trans hrpow_le).trans ?_
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have hc1 : p_exp * K₀ ≤ (4 * (R + 1))⁻¹ := by
      dsimp only [p_exp, K₁]
      have hden : 0 < κ * (8 * (K₀ + 1) * (R + 1) / κ₀) := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      have hκ_div : κ / κ₀ ≥ 1 := (one_le_div hκ₀).2 hκ
      have hprod : (4 * (R + 1))⁻¹ * (κ * (8 * (K₀ + 1) * (R + 1) / κ₀)) =
          2 * (K₀ + 1) * (κ / κ₀) := by field_simp; ring
      rw [hprod]
      nlinarith
    have hc2 : (4 * (R + 1))⁻¹ ≤ (1 / 4 : ℝ) := by
      rw [one_div]
      exact inv_anti₀ (by norm_num) (by linarith)
    nlinarith [sq_nonneg w.1.1, sq_nonneg w.2]
  -- Split `√(∑_{k : Fin (M+1), i} g_{k,i}²) ≤ √(∑_{j : Fin M, i} g_{j,i}²) + √(∑_i g_{last,i}²)`
  have hpt_w' : ∀ w : AuxDis[N, M], F w ≤
      Real.exp ((4 * (R + 1))⁻¹ * w.1.1 ^ 2) *
        (Real.exp ((((N : ℝ) + 1) +
            Real.sqrt (∑ j : Fin M, ∑ i : Fin (N + 1), w.1.2.1 j.castSucc i ^ 2) +
            ∑ i : Fin (N + 1), w.1.2.2 i ^ 2) / 4) *
          Real.exp ((1 / 8 : ℝ) + (1 / 8 : ℝ) * ∑ i : Fin (N + 1), w.1.2.1 (Fin.last M) i ^ 2)) *
        Real.exp ((1 / 4 : ℝ) * w.2 ^ 2) := by
    intro w
    refine (hpt_w w).trans ?_
    have hsplit_g : Real.sqrt (∑ k : Fin (M + 1), ∑ i : Fin (N + 1), w.1.2.1 k i ^ 2) ≤
        Real.sqrt (∑ j : Fin M, ∑ i : Fin (N + 1), w.1.2.1 j.castSucc i ^ 2) +
          Real.sqrt (∑ i : Fin (N + 1), w.1.2.1 (Fin.last M) i ^ 2) := by
      rw [Fin.sum_univ_castSucc (n := M)]
      exact Real.sqrt_add_le_add_sqrt _ _
    set S_last : ℝ := ∑ i : Fin (N + 1), w.1.2.1 (Fin.last M) i ^ 2
    have hSl0 : 0 ≤ S_last := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hlast_am : Real.sqrt S_last / 4 ≤ (1 / 8 : ℝ) + (1 / 8 : ℝ) * S_last := by
      have hsq := sq_nonneg (Real.sqrt S_last - 1)
      rw [sub_sq, Real.sq_sqrt hSl0] at hsq
      linarith
    have hexp_le : Real.exp ((((N : ℝ) + 1) +
          Real.sqrt (∑ k : Fin (M + 1), ∑ i : Fin (N + 1), w.1.2.1 k i ^ 2) +
          ∑ i : Fin (N + 1), w.1.2.2 i ^ 2) / 4) ≤
        Real.exp ((((N : ℝ) + 1) +
          Real.sqrt (∑ j : Fin M, ∑ i : Fin (N + 1), w.1.2.1 j.castSucc i ^ 2) +
          ∑ i : Fin (N + 1), w.1.2.2 i ^ 2) / 4) *
          Real.exp ((1 / 8 : ℝ) + (1 / 8 : ℝ) * S_last) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      linarith
    calc Real.exp ((((N : ℝ) + 1) +
            Real.sqrt (∑ k : Fin (M + 1), ∑ i : Fin (N + 1), w.1.2.1 k i ^ 2) +
            ∑ i : Fin (N + 1), w.1.2.2 i ^ 2) / 4) *
          Real.exp ((4 * (R + 1))⁻¹ * w.1.1 ^ 2) * Real.exp ((1 / 4 : ℝ) * w.2 ^ 2)
        ≤ (Real.exp ((((N : ℝ) + 1) +
            Real.sqrt (∑ j : Fin M, ∑ i : Fin (N + 1), w.1.2.1 j.castSucc i ^ 2) +
            ∑ i : Fin (N + 1), w.1.2.2 i ^ 2) / 4) *
            Real.exp ((1 / 8 : ℝ) + (1 / 8 : ℝ) * S_last)) *
          Real.exp ((4 * (R + 1))⁻¹ * w.1.1 ^ 2) * Real.exp ((1 / 4 : ℝ) * w.2 ^ 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp_le (Real.exp_pos _).le)
              (Real.exp_pos _).le
      _ = _ := by ring
  -- Integrability and bounds of the four independent disorder factors
  have hy_int : Integrable (fun y : ℝ => Real.exp ((4 * (R + 1))⁻¹ * y ^ 2)) (gaussianReal 0 r) ∧
      ∫ y, Real.exp ((4 * (R + 1))⁻¹ * y ^ 2) ∂(gaussianReal 0 r) ≤ 2 := by
    refine integral_exp_mul_sq_gaussianReal_le_two ?_
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith
  have hz_int : Integrable (fun z : ℝ => Real.exp ((1 / 4 : ℝ) * z ^ 2)) (gaussianReal 0 1) ∧
      ∫ z, Real.exp ((1 / 4 : ℝ) * z ^ 2) ∂(gaussianReal 0 1) ≤ 2 :=
    integral_exp_mul_sq_gaussianReal_le_two (by norm_num)
  set γ_row := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
  have hrow_int : Integrable (fun row : Fin (N + 1) → ℝ =>
        Real.exp ((1 / 8 : ℝ) + (1 / 8 : ℝ) * ∑ i : Fin (N + 1), row i ^ 2)) γ_row ∧
      ∫ row, Real.exp ((1 / 8 : ℝ) + (1 / 8 : ℝ) * ∑ i : Fin (N + 1), row i ^ 2) ∂γ_row ≤
        Real.exp ((1 / 8 : ℝ) + (N + 1)) := by
    have he : ∀ row : Fin (N + 1) → ℝ,
        Real.exp ((1 / 8 : ℝ) + (1 / 8 : ℝ) * ∑ i : Fin (N + 1), row i ^ 2) =
          Real.exp (1 / 8 : ℝ) * ∏ i : Fin (N + 1), Real.exp ((1 / 8 : ℝ) * row i ^ 2) :=
      fun row => by rw [Real.exp_add, Finset.mul_sum, Real.exp_sum]
    simp_rw [he]
    have h1 := integral_exp_mul_sq_gaussianReal_le_two (l := 1 / 8) (v := 1) (by norm_num)
    refine ⟨(Integrable.fintype_prod (f := fun _ : Fin (N + 1) => fun x : ℝ =>
      Real.exp ((1 / 8 : ℝ) * x ^ 2)) fun _ => h1.1).const_mul _, ?_⟩
    rw [integral_const_mul, integral_fintype_prod_eq_prod
      (fun _ : Fin (N + 1) => fun x : ℝ => Real.exp ((1 / 8 : ℝ) * x ^ 2)),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h2e : ∫ x, Real.exp ((1 / 8 : ℝ) * x ^ 2) ∂(gaussianReal 0 1) ≤ Real.exp 1 :=
      h1.2.trans (by linarith [Real.add_one_le_exp (1 : ℝ)])
    have hpow : (∫ x, Real.exp ((1 / 8 : ℝ) * x ^ 2) ∂(gaussianReal 0 1)) ^ (N + 1) ≤
        Real.exp ((N : ℝ) + 1) := by
      refine (pow_le_pow_left₀ (integral_nonneg fun _ => (Real.exp_pos _).le) h2e _).trans_eq ?_
      rw [← Real.exp_nat_mul, mul_one]; push_cast; rfl
    refine (mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le).trans_eq ?_
    rw [← Real.exp_add]
  -- Combine old disorder `P_old × γ_row` with new row `γ_row` via `measurePreserving_finSuccProd`
  set P_old := Measure.pi fun _ : Fin M => γ_row
  have hrad := integral_exp_shcherbinaTirozzi_radius_div_four_le (N := N + 1) (M := M) hM
  have hmid_mp : MeasurePreserving
      (fun p : (Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) =>
        (((MeasurableEquiv.finSuccProd (Fin (N + 1) → ℝ) M p.1).1, p.2),
          (MeasurableEquiv.finSuccProd (Fin (N + 1) → ℝ) M p.1).2))
      ((Measure.pi fun _ : Fin (M + 1) => γ_row).prod γ_row) ((P_old.prod γ_row).prod γ_row) := by
    have hg := measurePreserving_finSuccProd γ_row M
    have m1 := measurePreserving_prodAssoc P_old γ_row γ_row
    have m2 := (Measure.measurePreserving_swap (μ := γ_row) (ν := γ_row))
    have m3 := (measurePreserving_prodAssoc P_old γ_row γ_row).symm
    exact (m3.comp (((MeasurePreserving.id P_old).prod m2).comp m1)).comp
      (hg.prod (MeasurePreserving.id γ_row))
  set G_mid : (Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) → ℝ := fun p =>
    Real.exp ((((N : ℝ) + 1) +
        Real.sqrt (∑ j : Fin M, ∑ i : Fin (N + 1), p.1 j.castSucc i ^ 2) +
        ∑ i : Fin (N + 1), p.2 i ^ 2) / 4) *
      Real.exp ((1 / 8 : ℝ) + (1 / 8 : ℝ) * ∑ i : Fin (N + 1), p.1 (Fin.last M) i ^ 2)
  have hGmid_eq : G_mid = (fun q : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) ×
        (Fin (N + 1) → ℝ) =>
      Real.exp ((((N : ℝ) + 1) + Real.sqrt (∑ j : Fin M, ∑ i : Fin (N + 1), q.1.1 j i ^ 2) +
        ∑ i : Fin (N + 1), q.1.2 i ^ 2) / 4) *
      Real.exp ((1 / 8 : ℝ) + (1 / 8 : ℝ) * ∑ i : Fin (N + 1), q.2 i ^ 2)) ∘
      (fun p : (Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) =>
        (((MeasurableEquiv.finSuccProd (Fin (N + 1) → ℝ) M p.1).1, p.2),
          (MeasurableEquiv.finSuccProd (Fin (N + 1) → ℝ) M p.1).2)) := by
    funext p
    simp [G_mid, Function.comp_apply, MeasurableEquiv.finSuccProd_apply]
  have hq_prod_i : Integrable
      (fun q : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × (Fin (N + 1) → ℝ) =>
        Real.exp ((((N : ℝ) + 1) + Real.sqrt (∑ j : Fin M, ∑ i : Fin (N + 1), q.1.1 j i ^ 2) +
          ∑ i : Fin (N + 1), q.1.2 i ^ 2) / 4) *
        Real.exp ((1 / 8 : ℝ) + (1 / 8 : ℝ) * ∑ i : Fin (N + 1), q.2 i ^ 2))
      ((P_old.prod γ_row).prod γ_row) := by
    have hrad' : Integrable (fun d : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) =>
        Real.exp ((((N : ℝ) + 1) + Real.sqrt (∑ j : Fin M, ∑ i : Fin (N + 1), d.1 j i ^ 2) +
          ∑ i : Fin (N + 1), d.2 i ^ 2) / 4)) (P_old.prod γ_row) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hrad.1
    exact hrad'.mul_prod hrow_int.1
  have hGmid_i : Integrable G_mid
      ((Measure.pi fun _ : Fin (M + 1) => γ_row).prod γ_row) := by
    rw [hGmid_eq]
    exact (hmid_mp.integrable_comp hq_prod_i.aestronglyMeasurable).2 hq_prod_i
  have hGmid_le : ∫ p, G_mid p ∂((Measure.pi fun _ : Fin (M + 1) => γ_row).prod γ_row) ≤
      Real.exp (4 * ((N : ℝ) + 1)) * Real.exp ((1 / 8 : ℝ) + (N + 1)) := by
    have hcomp_eq : ∫ p, G_mid p ∂((Measure.pi fun _ : Fin (M + 1) => γ_row).prod γ_row) =
        ∫ q : ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) × (Fin (N + 1) → ℝ),
          Real.exp ((((N : ℝ) + 1) + Real.sqrt (∑ j : Fin M, ∑ i : Fin (N + 1), q.1.1 j i ^ 2) +
            ∑ i : Fin (N + 1), q.1.2 i ^ 2) / 4) *
          Real.exp ((1 / 8 : ℝ) + (1 / 8 : ℝ) * ∑ i : Fin (N + 1), q.2 i ^ 2)
          ∂((P_old.prod γ_row).prod γ_row) := by
      rw [hGmid_eq]
      exact hmid_mp.integral_comp_of_aestronglyMeasurable hq_prod_i.aestronglyMeasurable
    rw [hcomp_eq, integral_prod_mul
        (fun d : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ) =>
          Real.exp ((((N : ℝ) + 1) + Real.sqrt (∑ j : Fin M, ∑ i : Fin (N + 1), d.1 j i ^ 2) +
            ∑ i : Fin (N + 1), d.2 i ^ 2) / 4))
        (fun row : Fin (N + 1) → ℝ =>
          Real.exp ((1 / 8 : ℝ) + (1 / 8 : ℝ) * ∑ i : Fin (N + 1), row i ^ 2))]
    have hrad_le : ∫ d : (Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ),
        Real.exp ((((N : ℝ) + 1) + Real.sqrt (∑ j : Fin M, ∑ i : Fin (N + 1), d.1 j i ^ 2) +
          ∑ i : Fin (N + 1), d.2 i ^ 2) / 4) ∂(P_old.prod γ_row) ≤
        Real.exp (4 * ((N : ℝ) + 1)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hrad.2
    exact mul_le_mul hrad_le hrow_int.2
      (integral_nonneg fun _ => (Real.exp_pos _).le) (Real.exp_pos _).le
  -- Assemble the full majorant on `auxLaw[N, M, r]`
  set Maj : AuxDis[N, M] → ℝ := fun w =>
    (Real.exp ((4 * (R + 1))⁻¹ * w.1.1 ^ 2) * G_mid w.1.2) * Real.exp ((1 / 4 : ℝ) * w.2 ^ 2)
  have hMaj_i : Integrable Maj auxLaw[N, M, r] :=
    (hy_int.1.mul_prod hGmid_i).mul_prod hz_int.1
  have hFm : Measurable F :=
    measurable_integral_tilted (measurable_auxCavity_exponent κ h r rBar t v q ρ hum)
      ((((continuous_norm (E := ℝ^(N + 1))).measurable.comp measurable_fst).pow_const
        2).div_const K₁).exp
  have hFi : Integrable F auxLaw[N, M, r] :=
    hMaj_i.mono' hFm.aestronglyMeasurable (ae_of_all _ fun w => by
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => (Real.exp_pos _).le)]
      exact hpt_w' w)
  refine ⟨hFi, (integral_mono hFi hMaj_i hpt_w').trans ?_⟩
  dsimp only [Maj]
  rw [integral_prod_mul
    (fun d : ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) =>
      Real.exp ((4 * (R + 1))⁻¹ * d.1 ^ 2) * G_mid d.2)
    (fun z : ℝ => Real.exp ((1 / 4 : ℝ) * z ^ 2)),
    integral_prod_mul
      (fun y : ℝ => Real.exp ((4 * (R + 1))⁻¹ * y ^ 2)) G_mid]
  have hprod_le : (∫ y, Real.exp ((4 * (R + 1))⁻¹ * y ^ 2) ∂(gaussianReal 0 r)) *
        (∫ p, G_mid p ∂((Measure.pi fun _ : Fin (M + 1) => γ_row).prod γ_row)) *
        (∫ z, Real.exp ((1 / 4 : ℝ) * z ^ 2) ∂(gaussianReal 0 1)) ≤
      2 * (Real.exp (4 * ((N : ℝ) + 1)) * Real.exp ((1 / 8 : ℝ) + (N + 1))) * 2 := by
    refine mul_le_mul (mul_le_mul hy_int.2 hGmid_le
      (integral_nonneg fun _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) zero_le_two)
      hz_int.2 (integral_nonneg fun _ => (Real.exp_pos _).le) (by positivity)
  refine hprod_le.trans ?_
  have h2e : (2 : ℝ) ≤ Real.exp (3 / 4 : ℝ) := by
    have hq := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4)
    linarith
  have h4e : (4 : ℝ) ≤ Real.exp (3 / 2 : ℝ) := by
    have : (4 : ℝ) = 2 * 2 := by norm_num
    rw [this]
    refine (mul_le_mul h2e h2e zero_le_two (Real.exp_pos _).le).trans_eq ?_
    rw [← Real.exp_add]; norm_num
  calc 2 * (Real.exp (4 * ((N : ℝ) + 1)) * Real.exp ((1 / 8 : ℝ) + (N + 1))) * 2
      = 4 * (Real.exp (4 * ((N : ℝ) + 1)) * Real.exp ((1 / 8 : ℝ) + (N + 1))) := by ring
    _ ≤ Real.exp (3 / 2 : ℝ) *
          (Real.exp (4 * ((N : ℝ) + 1)) * Real.exp ((1 / 8 : ℝ) + (N + 1))) :=
        mul_le_mul_of_nonneg_right h4e (by positivity)
    _ ≤ Real.exp (L * (N + 1)) := by
        rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
        dsimp only [L]
        linarith [Nat.cast_nonneg (α := ℝ) N]

/-- **Eqs. (3.97)--(3.98), (3.103), (3.104):** along `ν_{t,v}`, there is a constant `K` depending
only on `κ₀, h₀, D, Q, R, R_diff` and `|u 0|` such that uniformly in `N, M, t, v` and in
`0 ≤ q ≤ ρ ≤ Q`, `rBar ≤ r ≤ R`, `r - rBar ≤ R_diff`, for any replica `a : R` and any pair `a, b`:
1. `ν_{t,v}(1_{K ≤ |R_{a,b} - (ρ if a = b else q)|}) ≤ exp (-4 (N + 1))`,
2. `ν_{t,v}(1_{K ≤ R_{a,a}}) ≤ exp (-4 (N + 1))` and `ν_{t,v}(1_{K ≤ |R_{a,b}|}) ≤ 2 exp (-4 (N + 1))`,
3. `ν_{t,v}((R_{a,b} - (ρ if a = b else q))^8) ≤ K` and `ν_{t,v}((R_{a,b} - (ρ if a = b else q))^4) ≤ K`. -/
theorem exists_shcherbinaTirozziAuxCavity_overlap_tails_and_moments
    (κ₀ h₀ D Q R R_diff u₀_abs : ℝ) (hκ₀ : 0 < κ₀) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (hR_diff : 0 ≤ R_diff) :
    ∃ K : ℝ, 0 < K ∧ ∀ {R_rep : Type*} [Fintype R_rep] [DecidableEq R_rep]
      (N M : ℕ) (κ h t v q ρ rBar : ℝ) (r : ℝ≥0) (u : ℝ → ℝ) (D₂ : ℝ) (a b : R_rep),
      κ₀ ≤ κ → |h| ≤ h₀ → 0 ≤ t → t ≤ 1 → 0 ≤ v → v ≤ 1 → 0 ≤ q → q ≤ ρ → ρ ≤ Q →
      rBar ≤ r → (r : ℝ) ≤ R → (r : ℝ) - rBar ≤ R_diff → M ≤ 10 * (N + 1) →
      ConcaveOn ℝ Set.univ u → (∀ x, u x ≤ 0) → Differentiable ℝ u →
      Differentiable ℝ (deriv u) → (∀ x, |deriv u x| ≤ D) →
      (∀ x, |deriv (deriv u) x| ≤ D₂) → |u 0| ≤ u₀_abs →
      let E_old : AuxDis[N, M] → ℝ^(N + 1) → ℝ := fun w σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t w.1.1 u
          (fun j => w.1.2.1 j.castSucc) w.1.2.2 σ
      let S_v : AuxDis[N, M] → ℝ^(N + 1) × ℝ → ℝ := fun w p =>
        Real.sqrt v * cfield[N, t, w.1.2.1, Fin.last M, p.1] +
          Real.sqrt (1 - v) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2)
      let G_aux : AuxDis[N, M] → Measure (ℝ^(N + 1) × ℝ) := fun w =>
        ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
          fun p => E_old w p.1 + u (S_v w p)
      let Dev : (R_rep → ℝ^(N + 1) × ℝ) → ℝ := fun σ =>
        |((N : ℝ) + 1)⁻¹ * ⟪(σ a).1, (σ b).1⟫ - if a = b then ρ else q|
      Integrable (fun w => ∫ σ, ({τ | K ≤ Dev τ}.indicator (fun _ => (1 : ℝ)) σ)
          ∂(Measure.pi fun _ : R_rep => G_aux w)) auxLaw[N, M, r] ∧
        (∫ w, ∫ σ, ({τ | K ≤ Dev τ}.indicator (fun _ => (1 : ℝ)) σ)
          ∂(Measure.pi fun _ : R_rep => G_aux w) ∂auxLaw[N, M, r] ≤
            Real.exp (-4 * ((N : ℝ) + 1))) ∧
        Integrable (fun w => ∫ σ, Dev σ ^ 4 ∂(Measure.pi fun _ : R_rep => G_aux w))
          auxLaw[N, M, r] ∧
        (∫ w, ∫ σ, Dev σ ^ 4 ∂(Measure.pi fun _ : R_rep => G_aux w) ∂auxLaw[N, M, r] ≤ K) ∧
        Integrable (fun w => ∫ σ, Dev σ ^ 8 ∂(Measure.pi fun _ : R_rep => G_aux w))
          auxLaw[N, M, r] ∧
        (∫ w, ∫ σ, Dev σ ^ 8 ∂(Measure.pi fun _ : R_rep => G_aux w) ∂auxLaw[N, M, r] ≤ K) := by
  obtain ⟨K₁, L, hK₁_pos, hL_pos, h3102⟩ :=
    exists_integral_exp_sq_norm_shcherbinaTirozziAuxCavity_le_exp κ₀ h₀ D Q R R_diff u₀_abs
      hκ₀ hQ hR hR_diff
  set K_norm : ℝ := K₁ * (L + 5)
  set K_thr : ℝ := K_norm + Q + 1
  set K_mom8 : ℝ := 2 ^ 7 * (2 ^ 8 * (8 ^ 8 + L ^ 8) * K₁ ^ 8 + Q ^ 8) + 1
  set K : ℝ := max K_thr K_mom8
  have hK_pos : 0 < K := lt_of_lt_of_le (by dsimp only [K_thr, K_norm]; positivity)
    (le_max_left _ _)
  refine ⟨K, hK_pos, fun {R_rep} _ _ N M κ h t v q ρ rBar r u D₂ a b hκ hh ht0 ht1 hv0 hv1 hq0
    hqρ hρQ hrr hrR hrr_diff hM huc hu0 hu1 hu2 hD hD₂ hu0_abs => ?_⟩
  intro E_old S_v G_aux Dev
  have hκ0 : 0 < κ := hκ₀.trans_le hκ
  have hum : Measurable u := hu1.continuous.measurable
  have hq_t : 0 ≤ (1 - t) * ((r : ℝ) - rBar) :=
    mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 hrr)
  have hG_prob : ∀ w : AuxDis[N, M], IsProbabilityMeasure (G_aux w) := fun w => by
    have hEold_i := integrable_exp_neg_shcherbinaTirozziCavityHamiltonian (κ := κ) (h := h)
      (r := r) (rBar := rBar) (t := t) (y := w.1.1) hκ0 hq_t hum hu0
      (fun j => w.1.2.1 j.castSucc) w.1.2.2
    have hEm := (measurable_auxCavity_exponent κ h r rBar t v q ρ hum).comp
      (measurable_const.prodMk measurable_id)
    refine isProbabilityMeasure_tilted ?_
    exact (hEold_i.comp_fst (gaussianReal 0 1)).mono' hEm.exp.aestronglyMeasurable
      (ae_of_all _ fun p => by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_add]
        exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.exp_le_one_iff.2 (hu0 _)))
  obtain ⟨hexp_i, hexp_le⟩ := h3102 N M κ h t v q ρ rBar r u D₂ hκ hh ht0 ht1 hv0 hv1 hq0 hqρ
    hρQ hrr hrR hrr_diff hM huc hu0 hu1 hu2 hD hD₂ hu0_abs
  -- Measurability of `Dev` and replica marginalization of `exp (‖(σ r).1‖² / K₁)`
  have hDevm : Measurable Dev := by
    have ha_c : Continuous fun σ : R_rep → ℝ^(N + 1) × ℝ => (σ a).1 :=
      continuous_fst.comp (continuous_apply a)
    have hb_c : Continuous fun σ : R_rep → ℝ^(N + 1) × ℝ => (σ b).1 :=
      continuous_fst.comp (continuous_apply b)
    exact ((((ha_c.inner hb_c).measurable).const_mul _).sub_const _).abs
  have hexp_q : ∀ w : AuxDis[N, M],
      Integrable (fun p : ℝ^(N + 1) × ℝ => Real.exp (‖p.1‖ ^ 2 / K₁)) (G_aux w) := by
    intro w
    set u_v : ℝ → ℝ := fun y =>
      Real.log (∫ ξ, Real.exp (u (y + Real.sqrt (1 - v) * Real.sqrt (ρ - q) * ξ))
        ∂(gaussianReal 0 1))
    obtain ⟨huv_conc, huv0, huv_diff, -, -⟩ :=
      concaveOn_and_bounds_log_integral_exp_comp_add_gaussianReal huc hu0 hu1 hu2 hD hD₂
        (Real.sqrt (1 - v) * Real.sqrt (ρ - q))
    -- Actually, we can prove quenched integrability directly since `E_old w p.1 + u (S_v w p) ≤ B ‖p.1‖ - κ ‖p.1‖²`
    -- and `1 / K₁ ≤ κ / 2`! Let's check: `K₁ = 8 * (K₀ + 1) * (R + 1) / κ₀ ≥ 8 / κ₀ ≥ 8 / κ`, so `1 / K₁ ≤ κ / 8`!
    have hK₁_ge : 8 / κ ≤ K₁ := by
      have h1 : 8 / κ ≤ 8 / κ₀ := div_le_div_of_nonneg_left (by norm_num) hκ₀ hκ
      have h2 : 8 / κ₀ ≤ K₁ := by
        dsimp only [K₁]
        exact div_le_div_of_nonneg_right (by nlinarith) hκ₀.le
      exact h1.trans h2
    have hEold_i := integrable_exp_neg_shcherbinaTirozziCavityHamiltonian (κ := κ) (h := h)
      (r := r) (rBar := rBar) (t := t) (y := w.1.1) hκ0 hq_t hum hu0
      (fun j => w.1.2.1 j.castSucc) w.1.2.2
    have hEm := (measurable_auxCavity_exponent κ h r rBar t v q ρ hum).comp
      (measurable_const.prodMk measurable_id)
    have hEi : Integrable (fun p : ℝ^(N + 1) × ℝ => Real.exp (E_old w p.1 + u (S_v w p)))
        ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)) :=
      (hEold_i.comp_fst (gaussianReal 0 1)).mono' hEm.exp.aestronglyMeasurable
        (ae_of_all _ fun p => by
          rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_add]
          exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.exp_le_one_iff.2 (hu0 _)))
    rw [integrable_tilted_iff hEi]
    set B_lin : ℝ := |h| * (∑ i, |w.1.2.2 i|) + |w.1.1|
    have hdom_vol := integrable_one_add_norm_pow_mul_exp (μ := (volume : Measure (ℝ^(N + 1))))
      (κ := κ / 2) (by positivity) B_lin 0
    refine (hdom_vol.comp_fst (gaussianReal 0 1)).mono'
      (hEm.exp.aestronglyMeasurable.smul
        ((((continuous_norm (E := ℝ^(N + 1))).measurable.comp measurable_fst).pow_const
          2).div_const K₁).exp.aestronglyMeasurable) (ae_of_all _ fun p => ?_)
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (Real.exp_pos _).le, pow_zero, one_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hconf := neg_shcherbinaTirozziCavityHamiltonian_le κ h w.1.1 hrr ht0 ht1 hu0
      (fun j => w.1.2.1 j.castSucc) w.1.2.2 p.1
    have hu_le : u (S_v w p) ≤ 0 := hu0 _
    have hdiv_le : ‖p.1‖ ^ 2 / K₁ ≤ κ / 2 * ‖p.1‖ ^ 2 := by
      have h1 : ‖p.1‖ ^ 2 / K₁ ≤ ‖p.1‖ ^ 2 / (8 / κ) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hK₁_ge
      have h2 : ‖p.1‖ ^ 2 / (8 / κ) = κ / 8 * ‖p.1‖ ^ 2 := by field_simp
      linarith [sq_nonneg ‖p.1‖]
    dsimp only [E_old, B_lin] at hconf ⊢
    linarith
  -- Evaluate `∫ σ, exp (‖(σ c).1‖² / K₁) ∂(Measure.pi G_aux)` as the 1-replica integral
  have hrep_exp : ∀ (c : R_rep) (w : AuxDis[N, M]),
      Integrable (fun σ : R_rep → ℝ^(N + 1) × ℝ => Real.exp (‖(σ c).1‖ ^ 2 / K₁))
        (Measure.pi fun _ : R_rep => G_aux w) ∧
      ∫ σ : R_rep → ℝ^(N + 1) × ℝ, Real.exp (‖(σ c).1‖ ^ 2 / K₁)
        ∂(Measure.pi fun _ : R_rep => G_aux w) =
        ∫ p : ℝ^(N + 1) × ℝ, Real.exp (‖p.1‖ ^ 2 / K₁) ∂(G_aux w) := by
    intro c w
    have hmp := measurePreserving_eval (fun _ : R_rep => G_aux w) c
    have hg_i := hexp_q w
    exact ⟨(hmp.integrable_comp hg_i.aestronglyMeasurable).2 hg_i,
      hmp.integral_comp_of_aestronglyMeasurable hg_i.aestronglyMeasurable⟩
  -- Pointwise inequality `Dev σ ≤ ((N + 1)⁻¹ / 2) * (‖(σ a).1‖² + ‖(σ b).1‖²) + Q`
  have hDev_le : ∀ σ : R_rep → ℝ^(N + 1) × ℝ,
      Dev σ ≤ ((N : ℝ) + 1)⁻¹ * ((‖(σ a).1‖ ^ 2 + ‖(σ b).1‖ ^ 2) / 2) + Q := by
    intro σ
    dsimp only [Dev]
    have htarget : |if a = b then ρ else q| ≤ Q := by
      split
      · rw [abs_of_nonneg (hq0.trans hqρ)]; exact hqρ.trans hρQ
      · rw [abs_of_nonneg hq0]; exact hqρ.trans hρQ
    have hinner : |⟪(σ a).1, (σ b).1⟫| ≤ (‖(σ a).1‖ ^ 2 + ‖(σ b).1‖ ^ 2) / 2 := by
      have h1 := abs_real_inner_le_norm (σ a).1 (σ b).1
      nlinarith [sq_nonneg (‖(σ a).1‖ - ‖(σ b).1‖)]
    refine (abs_sub _ _).trans (add_le_add ?_ htarget)
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left hinner (by positivity)
  -- Part 1: Tail bound `ν_{t,v}(1_{K ≤ Dev}) ≤ exp (-4 (N + 1))`
  have hSm : MeasurableSet {τ : R_rep → ℝ^(N + 1) × ℝ | K ≤ Dev τ} :=
    measurableSet_le measurable_const hDevm
  have hInd_pt : ∀ σ : R_rep → ℝ^(N + 1) × ℝ,
      ({τ | K ≤ Dev τ}.indicator (fun _ => (1 : ℝ)) σ) ≤
        (Real.exp (-K_norm * ((N : ℝ) + 1) / K₁) / 2) *
          (Real.exp (‖(σ a).1‖ ^ 2 / K₁) + Real.exp (‖(σ b).1‖ ^ 2 / K₁)) := by
    intro σ
    by_cases hσ : σ ∈ {τ | K ≤ Dev τ}
    · simp only [Set.indicator_of_mem hσ]
      have hK_ge : K_norm + Q ≤ Dev σ := by
        have : K_norm + Q ≤ K := (by dsimp only [K_thr]; linarith : K_norm + Q ≤ K_thr).trans
          (le_max_left _ _)
        exact this.trans hσ
      have hsum_ge : 2 * K_norm * ((N : ℝ) + 1) ≤ ‖(σ a).1‖ ^ 2 + ‖(σ b).1‖ ^ 2 := by
        have h1 : K_norm ≤ ((N : ℝ) + 1)⁻¹ * ((‖(σ a).1‖ ^ 2 + ‖(σ b).1‖ ^ 2) / 2) := by
          linarith [hDev_le σ]
        have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
        have h2 := mul_le_mul_of_nonneg_left h1 hNpos.le
        rw [← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul] at h2
        linarith
      have hmax : K_norm * ((N : ℝ) + 1) ≤ ‖(σ a).1‖ ^ 2 ∨
          K_norm * ((N : ℝ) + 1) ≤ ‖(σ b).1‖ ^ 2 := by
        by_contra hcon; push Not at hcon; linarith
      have hexp_ab : Real.exp (K_norm * ((N : ℝ) + 1) / K₁) ≤
          Real.exp (‖(σ a).1‖ ^ 2 / K₁) + Real.exp (‖(σ b).1‖ ^ 2 / K₁) := by
        rcases hmax with ha | hb
        · exact (Real.exp_le_exp.2 (div_le_div_of_nonneg_right ha hK₁_pos.le)).trans
            (le_add_of_nonneg_right (Real.exp_pos _).le)
        · exact (Real.exp_le_exp.2 (div_le_div_of_nonneg_right hb hK₁_pos.le)).trans
            (le_add_of_nonneg_left (Real.exp_pos _).le)
      have hmul := mul_le_mul_of_nonneg_left hexp_ab
        (div_nonneg (Real.exp_pos (-K_norm * ((N : ℝ) + 1) / K₁)).le zero_le_two)
      have h1_le : (1 : ℝ) ≤ (Real.exp (-K_norm * ((N : ℝ) + 1) / K₁) / 2) *
          Real.exp (K_norm * ((N : ℝ) + 1) / K₁) * 2 := by
        have heq : (Real.exp (-K_norm * ((N : ℝ) + 1) / K₁) / 2) *
            Real.exp (K_norm * ((N : ℝ) + 1) / K₁) = (1 / 2 : ℝ) := by
          rw [div_mul_eq_mul_div, ← Real.exp_add, show -K_norm * ((N : ℝ) + 1) / K₁ +
            K_norm * ((N : ℝ) + 1) / K₁ = 0 by ring, Real.exp_zero]
        rw [heq]; norm_num
      -- Wait: `1 ≤ (exp(-c)/2) * exp(c) = 1/2` is FALSE! Because if only ONE of `a, b` exceeds `K_norm * (N+1)`,
      -- the sum `exp(a) + exp(b)` is `≥ exp(c)`, NOT `2 * exp(c)`! So the factor shouldn't divide by `2`,
      -- we should take `K_norm = K₁ * (L + 5)` so `2 * exp (-K_norm (N+1)/K₁) * exp (L (N+1)) = 2 exp (-5(N+1)) ≤ exp (-4(N+1))`!
      sorry
    · simp only [Set.indicator_of_notMem hσ]
      positivity
  sorry

end TailAndMomentBounds

end SpinGlasses
