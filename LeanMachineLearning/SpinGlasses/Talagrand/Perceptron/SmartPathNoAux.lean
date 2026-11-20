/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.SmartPathExchangeable
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaPointMass

/-!
# The perceptron path without auxiliary spins (Talagrand, Exercise 2.2.4)

The path of (2.14) has the field `S⁰_{k,t}` without the auxiliary Gaussian term. Its Gibbs measure
is the spin Gibbs measure of `smartPathEnergyNoAux`; it is the smart-path energy for the base law
`count × δ₀` (`smartPathBaseNoAux`), where the auxiliary coordinates vanish almost surely. All
fixed-disorder and disorder-averaged integrations by parts of `SmartPathIBP.lean` and
`SmartPathAssembly.lean` hold for an arbitrary finite base law, and the auxiliary-spin term of the
energy derivative is zero for this base, so no auxiliary cancellation takes place: the derivative
is `I + II` plus the surviving diagonal term `VI`.

* `smartPathBaseNoAux`: the base law `count × δ₀`;
* `hasDerivAt_integral_integral_pi_perceptron_smart_path_noAux_base`: `ν'_t(f) = I + VI + II`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Function
open scoped NNReal

namespace SpinGlasses

variable {N M : ℕ}

/-- The base law of the path without auxiliary spins: spin counting measure times a point mass at
`ξ = 0`. The Gibbs measure of the smart-path energy for this base is the spin Gibbs measure of
the field `S⁰` of Talagrand (2.14), with a vanishing auxiliary part. -/
noncomputable def smartPathBaseNoAux (N M : ℕ) : Measure (SmartPathState N M) :=
  (Measure.count : Measure (PerceptronSpin N)).prod (Measure.dirac (0 : Fin M → ℝ))

instance : IsFiniteMeasure (smartPathBaseNoAux N M) := by
  unfold smartPathBaseNoAux; infer_instance

instance : NeZero (smartPathBaseNoAux N M) := by
  unfold smartPathBaseNoAux; infer_instance

/-- The auxiliary coordinates vanish almost surely for the auxiliary-free base law. -/
theorem ae_snd_eq_zero_smartPathBaseNoAux :
    ∀ᵐ x ∂(smartPathBaseNoAux N M), x.2 = (0 : Fin M → ℝ) := by
  unfold smartPathBaseNoAux
  have h : ∀ᵐ ξ ∂(Measure.dirac (0 : Fin M → ℝ)), ξ = 0 := by simp
  exact Measure.quasiMeasurePreserving_snd.ae h

/-- `exp (∑ |ξ_k|)` is integrable for the auxiliary-free base law (it equals `1` almost surely). -/
theorem integrable_exp_sum_abs_smartPathBaseNoAux :
    Integrable (fun x : SmartPathState N M => Real.exp (∑ k, |x.2 k|))
      (smartPathBaseNoAux N M) := by
  refine (integrable_const (1 : ℝ)).congr ?_
  filter_upwards [ae_snd_eq_zero_smartPathBaseNoAux (N := N) (M := M)] with x hx
  simp [hx]

/-- The auxiliary-spin term of the energy derivative vanishes where `ξ = 0`. -/
theorem smartPathEnergyDerivXi_of_snd_eq_zero (u : ℝ → ℝ) (t : ℝ) (ω : SmartPathDisorder N M)
    (x : SmartPathState N M) (hx : x.2 = 0) : smartPathEnergyDerivXi u t ω x = 0 := by
  simp [smartPathEnergyDerivXi, hx]

/-- **Exercise 2.2.4 at the level of the auxiliary-free base law.** For the base `count × δ₀` the
auxiliary part of the energy derivative vanishes, and the derivative of the quenched replica
average is `I + VI + II`: the pair terms `(1/(N+1)) ∑_k 𝔼⟨f pd(U_k)⟩`, the surviving diagonal
`1/(2(N+1)) ∑_k 𝔼 diff(u'' + u'^2)(S⁰_k)` and `−v 𝔼⟨f pd(ε ε')⟩`. -/
theorem hasDerivAt_integral_integral_pi_perceptron_smart_path_noAux_base {R : Type*}
    [Fintype R] [LinearOrder R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) {u : ℝ → ℝ}
    {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂) (v : ℝ≥0)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (f : (R → PerceptronSpin N) → ℝ) :
    HasDerivAt (fun s => ∫ ω, ∫ σ : R → SmartPathState N M, f (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => (smartPathBaseNoAux N M).tilted (smartPathEnergy u s ω))
        ∂smartPathDisorder Pold v)
      (1 / ((N : ℝ) + 1) * ∑ k : Fin M, ∫ ω, replicaPairAverage
          ((smartPathBaseNoAux N M).tilted (smartPathEnergy u t ω))
          (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
          (smartPathPotentialKernel u t ω k) ∂(smartPathDisorder Pold v) +
        1 / (2 * ((N : ℝ) + 1)) * ∑ k : Fin M, ∫ ω, replicaDiff
          ((smartPathBaseNoAux N M).tilted (smartPathEnergy u t ω))
          (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
          (fun x => deriv (deriv u) (smartPathField t ω x k) +
            deriv u (smartPathField t ω x k) ^ 2) ∂(smartPathDisorder Pold v) -
        (v : ℝ) * ∫ ω, replicaPairAverage
          ((smartPathBaseNoAux N M).tilted (smartPathEnergy u t ω))
          (fun σ : R → SmartPathState N M => f (fun r => (σ r).1)) lastSpinKernel
          ∂(smartPathDisorder Pold v)) t := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_finite f
  have hFm := measurable_spin_only (N := N) (M := M) f
  have hFb : ∀ σ : R → SmartPathState N M, |f (fun r => (σ r).1)| ≤ C := fun σ => hC _
  refine (hasDerivAt_integral_integral_pi_perceptron_smart_path_three_terms
    (integrable_exp_sum_abs_smartPathBaseNoAux (N := N) (M := M)) ht hu.differentiable
    hu.abs_le hu.abs_deriv_le v (Pold := Pold)
    (fun σ => f (fun r => (σ r).1)) hFm hFb).congr_deriv ?_
  have hprob (ω : SmartPathDisorder N M) : IsProbabilityMeasure
      ((smartPathBaseNoAux N M).tilted (smartPathEnergy u t ω)) :=
    isProbabilityMeasure_tilted_perceptron_smart_path_energy hu.measurable
      (fun x => hu.le x) ω t
  have hξ0 (ω : SmartPathDisorder N M) : replicaDiff
      ((smartPathBaseNoAux N M).tilted (smartPathEnergy u t ω))
      (fun σ : R → SmartPathState N M => f (fun r => (σ r).1)) (smartPathEnergyDerivXi u t ω) =
      0 := by
    have := hprob ω
    refine replicaDiff_eq_zero_of_ae _ _ ?_
    have h0 : ∀ᵐ x ∂(smartPathBaseNoAux N M), smartPathEnergyDerivXi u t ω x = 0 := by
      filter_upwards [ae_snd_eq_zero_smartPathBaseNoAux (N := N) (M := M)] with x hx
      exact smartPathEnergyDerivXi_of_snd_eq_zero u t ω x hx
    exact (tilted_absolutelyContinuous _ _).ae_le h0
  have hA := integrable_replicaDiff_smartPathEnergyDerivA (μ := smartPathBaseNoAux N M) (t := t)
    hu.toSmartPathPotential v (Pold := Pold) _ hFm hFb
  have hY := integrable_replicaDiff_smartPathEnergyDerivY (μ := smartPathBaseNoAux N M) (t := t)
    hu.toSmartPathPotential v (Pold := Pold) _ hFm hFb
  simp only [hξ0, add_zero]
  rw [integral_add hA hY,
    integral_replicaDiff_smartPathEnergyDerivA_disorder (μ := smartPathBaseNoAux N M) ht hu v
      _ hFm hFb,
    integral_replicaDiff_smartPathEnergyDerivY_disorder (μ := smartPathBaseNoAux N M) ht
      hu.toSmartPathPotential v _ hFm hFb]
  simp only [integral_smartPathConstraintTerm hu _ hFm hFb, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- At `ξ = 0` the smart-path field is the field `S⁰` of the path without auxiliary spins. -/
theorem smartPathField_zero_aux (t : ℝ) (ω : SmartPathDisorder N M) (a : PerceptronSpin N)
    (k : Fin M) : smartPathField t ω (a, 0) k = smartPathFieldNoAux t ω (a, 0) k := by
  simp [smartPathField]

/-- At `ξ = 0` the smart-path energy is the energy of the path without auxiliary spins. -/
theorem smartPathEnergy_zero_aux (u : ℝ → ℝ) (t : ℝ) (ω : SmartPathDisorder N M)
    (a : PerceptronSpin N) : smartPathEnergy u t ω (a, 0) = smartPathEnergyNoAux u t ω (a, 0) := by
  simp [smartPathEnergy, smartPathEnergyNoAux, smartPathField_zero_aux]

/-- The potential kernel (2.24) of the path without auxiliary spins, on the spin space. -/
noncomputable def smartPathPotentialKernelNoAux (u : ℝ → ℝ) (t : ℝ) (ω : SmartPathDisorder N M)
    (k : Fin M) (a b : PerceptronSpin N) : ℝ :=
  ((a.2 : ℤ) : ℝ) * ((b.2 : ℤ) : ℝ) * deriv u (smartPathFieldNoAux t ω (a, 0) k) *
    deriv u (smartPathFieldNoAux t ω (b, 0) k)

/-- The Gibbs weight of the smart-path energy is integrable for the auxiliary-free base law. -/
theorem integrable_exp_smartPathEnergy_noAux {u : ℝ → ℝ} (hu : Measurable u) {D : ℝ}
    (hD : ∀ x, u x ≤ D) (s : ℝ) (ω : SmartPathDisorder N M) :
    Integrable (fun x : PerceptronSpin N × (Fin M → ℝ) => Real.exp (smartPathEnergy u s ω x))
      ((Measure.count : Measure (PerceptronSpin N)).prod (Measure.dirac (0 : Fin M → ℝ))) :=
  integrable_exp_perceptron_smart_path_energy (μ := smartPathBaseNoAux N M) hu hD ω s

/-- **Spin transfer for the quenched average.** -/
theorem integral_pi_noAux_eq_spin {R : Type*} [Fintype R] {u : ℝ → ℝ} {D : ℝ}
    (hu : Measurable u) (hD : ∀ x, u x ≤ D) (s : ℝ) (ω : SmartPathDisorder N M)
    (f : (R → PerceptronSpin N) → ℝ) :
    ∫ σ : R → SmartPathState N M, f (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => (smartPathBaseNoAux N M).tilted (smartPathEnergy u s ω)) =
      ∫ σ : R → PerceptronSpin N, f σ ∂(Measure.pi fun _ : R => Measure.count.tilted
        (fun a => smartPathEnergyNoAux u s ω (a, 0))) := by
  have := integral_pi_tilted_prod_dirac (μ := (Measure.count : Measure (PerceptronSpin N)))
    (0 : Fin M → ℝ) (integrable_exp_smartPathEnergy_noAux hu hD s ω)
    (G := fun τ : R → PerceptronSpin N × (Fin M → ℝ) => f (fun r => (τ r).1)) (g := f)
    (measurable_of_finite f) (fun τ _ => rfl)
  simp only [smartPathEnergy_zero_aux] at this
  exact this

/-- **Spin transfer for a pair average.** -/
theorem replicaPairAverage_noAux_eq_spin {R : Type*} [Fintype R] [LinearOrder R] {u : ℝ → ℝ}
    {D : ℝ} (hu : Measurable u) (hD : ∀ x, u x ≤ D) (t : ℝ) (ω : SmartPathDisorder N M)
    (f : (R → PerceptronSpin N) → ℝ) (U : SmartPathState N M → SmartPathState N M → ℝ)
    (U0 : PerceptronSpin N → PerceptronSpin N → ℝ) (hU : ∀ a b, U (a, 0) (b, 0) = U0 a b) :
    replicaPairAverage ((smartPathBaseNoAux N M).tilted (smartPathEnergy u t ω))
        (fun σ : R → SmartPathState N M => f (fun r => (σ r).1)) U =
      replicaPairAverage (Measure.count.tilted (fun a => smartPathEnergyNoAux u t ω (a, 0))) f
        U0 := by
  have := replicaPairAverage_tilted_prod_dirac (μ := (Measure.count : Measure (PerceptronSpin N)))
    (0 : Fin M → ℝ) (integrable_exp_smartPathEnergy_noAux hu hD t ω) f U
  simp only [smartPathEnergy_zero_aux, hU] at this
  exact this

/-- **Spin transfer for the diagonal term.** -/
theorem replicaDiff_diag_noAux_eq_spin {R : Type*} [Fintype R] {u : ℝ → ℝ} {D : ℝ}
    (hu : Measurable u) (hD : ∀ x, u x ≤ D) (t : ℝ) (ω : SmartPathDisorder N M)
    (f : (R → PerceptronSpin N) → ℝ) (k : Fin M) :
    replicaDiff ((smartPathBaseNoAux N M).tilted (smartPathEnergy u t ω))
        (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
        (fun x => deriv (deriv u) (smartPathField t ω x k) +
          deriv u (smartPathField t ω x k) ^ 2) =
      replicaDiff (Measure.count.tilted (fun a => smartPathEnergyNoAux u t ω (a, 0))) f
        (fun a => deriv (deriv u) (smartPathFieldNoAux t ω (a, 0) k) +
          deriv u (smartPathFieldNoAux t ω (a, 0) k) ^ 2) := by
  have := replicaDiff_tilted_prod_dirac (μ := (Measure.count : Measure (PerceptronSpin N)))
    (0 : Fin M → ℝ) (integrable_exp_smartPathEnergy_noAux hu hD t ω) f
    (fun x => deriv (deriv u) (smartPathField t ω x k) + deriv u (smartPathField t ω x k) ^ 2)
  simp only [smartPathEnergy_zero_aux, smartPathField_zero_aux] at this
  exact this

/-- The swap of the auxiliary coordinates preserves the auxiliary-free base law. -/
theorem measurePreserving_smartPathStateSwap_noAux (i j : Fin M) :
    MeasurePreserving (smartPathStateSwap (N := N) i j) (smartPathBaseNoAux N M)
      (smartPathBaseNoAux N M) := by
  have hm : Measurable (fun ξ : Fin M → ℝ => fun l => ξ (Equiv.swap i j l)) :=
    measurable_pi_iff.2 fun l => measurable_pi_apply _
  have h : MeasurePreserving (fun ξ : Fin M → ℝ => fun l => ξ (Equiv.swap i j l))
      (Measure.dirac (0 : Fin M → ℝ)) (Measure.dirac (0 : Fin M → ℝ)) :=
    ⟨hm, Measure.map_dirac (f := fun ξ : Fin M → ℝ => fun l => ξ (Equiv.swap i j l))
      (0 : Fin M → ℝ)⟩
  exact (MeasurePreserving.id (Measure.count : Measure (PerceptronSpin N))).prod h

/-- **Spin transfer for the `k`-th potential-kernel pair average.** -/
theorem replicaPairAverage_potentialKernel_noAux_eq_spin {R : Type*} [Fintype R] [LinearOrder R]
    {u : ℝ → ℝ} {D : ℝ} (hu : Measurable u) (hD : ∀ x, u x ≤ D) (t : ℝ)
    (ω : SmartPathDisorder N M) (f : (R → PerceptronSpin N) → ℝ) (k : Fin M) :
    replicaPairAverage ((smartPathBaseNoAux N M).tilted (smartPathEnergy u t ω))
        (fun σ : R → SmartPathState N M => f (fun r => (σ r).1))
        (smartPathPotentialKernel u t ω k) =
      replicaPairAverage (Measure.count.tilted (fun a => smartPathEnergyNoAux u t ω (a, 0))) f
        (smartPathPotentialKernelNoAux u t ω k) :=
  replicaPairAverage_noAux_eq_spin hu hD t ω f _ _ fun a b => by
    simp [smartPathPotentialKernel, smartPathPotentialKernelNoAux, smartPathField_zero_aux]

/-- **Spin transfer for the last-spin pair average.** -/
theorem replicaPairAverage_lastSpin_noAux_eq_spin {R : Type*} [Fintype R] [LinearOrder R]
    {u : ℝ → ℝ} {D : ℝ} (hu : Measurable u) (hD : ∀ x, u x ≤ D) (t : ℝ)
    (ω : SmartPathDisorder N M) (f : (R → PerceptronSpin N) → ℝ) :
    replicaPairAverage ((smartPathBaseNoAux N M).tilted (smartPathEnergy u t ω))
        (fun σ : R → SmartPathState N M => f (fun r => (σ r).1)) lastSpinKernel =
      replicaPairAverage (Measure.count.tilted (fun a => smartPathEnergyNoAux u t ω (a, 0))) f
        (fun a b => ((a.2 : ℤ) : ℝ) * ((b.2 : ℤ) : ℝ)) :=
  replicaPairAverage_noAux_eq_spin hu hD t ω f _ _ fun _ _ => rfl

/-- **Talagrand, Exercise 2.2.4.** For the path without auxiliary spins, the Gibbs measure is the
counting measure on the spins tilted by `smartPathEnergyNoAux`, and for `0 < t < 1`, a potential
with `|u| ≤ B`, `|u'| ≤ D`, `|u''| ≤ D₂`, any finite law of the old couplings and any `v ≥ 0`, the
derivative of the quenched replica average of any observable `f` of `n` replicas is
`I + VI + II`: `I = (1/(N+1)) ∑_k 𝔼⟨f pd(U⁰_k)⟩`, `II = −v 𝔼⟨f pd(ε ε')⟩` as for the smart path,
and the extra term `VI = 1/(2(N+1)) ∑_k 𝔼 diff(u'' + u'^2)(S⁰_k)` that nothing cancels. -/
theorem hasDerivAt_integral_integral_pi_perceptron_smart_path_noAux {R : Type*}
    [Fintype R] [LinearOrder R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) {u : ℝ → ℝ}
    {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂) (v : ℝ≥0)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold]
    (f : (R → PerceptronSpin N) → ℝ) :
    HasDerivAt (fun s => ∫ ω, ∫ σ : R → PerceptronSpin N, f σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun a => smartPathEnergyNoAux u s ω (a, 0)))
        ∂smartPathDisorder Pold v)
      (1 / ((N : ℝ) + 1) * ∑ k : Fin M, ∫ ω, replicaPairAverage
          (Measure.count.tilted (fun a => smartPathEnergyNoAux u t ω (a, 0))) f
          (smartPathPotentialKernelNoAux u t ω k) ∂(smartPathDisorder Pold v) +
        1 / (2 * ((N : ℝ) + 1)) * ∑ k : Fin M, ∫ ω, replicaDiff
          (Measure.count.tilted (fun a => smartPathEnergyNoAux u t ω (a, 0))) f
          (fun a => deriv (deriv u) (smartPathFieldNoAux t ω (a, 0) k) +
            deriv u (smartPathFieldNoAux t ω (a, 0) k) ^ 2) ∂(smartPathDisorder Pold v) -
        (v : ℝ) * ∫ ω, replicaPairAverage
          (Measure.count.tilted (fun a => smartPathEnergyNoAux u t ω (a, 0))) f
          (fun a b => ((a.2 : ℤ) : ℝ) * ((b.2 : ℤ) : ℝ)) ∂(smartPathDisorder Pold v)) t := by
  have hbase := hasDerivAt_integral_integral_pi_perceptron_smart_path_noAux_base (N := N) (M := M)
    ht hu v (Pold := Pold) f
  have hfun : (fun s => ∫ ω, ∫ σ : R → PerceptronSpin N, f σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun a => smartPathEnergyNoAux u s ω (a, 0))) ∂smartPathDisorder Pold v) =
      fun s => ∫ ω, ∫ σ : R → SmartPathState N M, f (fun r => (σ r).1)
        ∂(Measure.pi fun _ : R => (smartPathBaseNoAux N M).tilted (smartPathEnergy u s ω))
        ∂smartPathDisorder Pold v :=
    funext fun s => integral_congr_ae
      (ae_of_all _ fun ω => (integral_pi_noAux_eq_spin hu.measurable (fun x => hu.le x) s ω f).symm)
  rw [hfun]
  refine hbase.congr_deriv ?_
  simp only [replicaPairAverage_potentialKernel_noAux_eq_spin hu.measurable (fun x => hu.le x) t,
    replicaPairAverage_lastSpin_noAux_eq_spin hu.measurable (fun x => hu.le x) t,
    replicaDiff_diag_noAux_eq_spin hu.measurable (fun x => hu.le x) t _ f]

/-- **Exercise 2.2.4, exchangeable form.** If the old rows are exchangeable, the sums over the
constraints in `I` and in `VI` are `M` times the term of a fixed constraint `j₀`:
the derivative is `(M/(N+1)) 𝔼⟨f pd(U⁰_{j₀})⟩ + (M/(2(N+1))) 𝔼 diff(u'' + u'^2)(S⁰_{j₀}) −
v 𝔼⟨f pd(ε ε')⟩`. -/
theorem hasDerivAt_integral_integral_pi_perceptron_smart_path_noAux_exchangeable {R : Type*}
    [Fintype R] [LinearOrder R] {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) {u : ℝ → ℝ}
    {B D D₂ : ℝ} (hu : SmartPathPotential₂ u B D D₂) (v : ℝ≥0)
    {Pold : Measure (Fin M → Fin N → ℝ)} [IsFiniteMeasure Pold] (j₀ : Fin M)
    (hPold : ∀ k : Fin M,
      Pold.map (fun g : Fin M → Fin N → ℝ => fun l => g (Equiv.swap k j₀ l)) = Pold)
    (f : (R → PerceptronSpin N) → ℝ) :
    HasDerivAt (fun s => ∫ ω, ∫ σ : R → PerceptronSpin N, f σ
        ∂(Measure.pi fun _ : R => Measure.count.tilted
          (fun a => smartPathEnergyNoAux u s ω (a, 0)))
        ∂smartPathDisorder Pold v)
      ((M : ℝ) / ((N : ℝ) + 1) * ∫ ω, replicaPairAverage
          (Measure.count.tilted (fun a => smartPathEnergyNoAux u t ω (a, 0))) f
          (smartPathPotentialKernelNoAux u t ω j₀) ∂(smartPathDisorder Pold v) +
        (M : ℝ) / (2 * ((N : ℝ) + 1)) * ∫ ω, replicaDiff
          (Measure.count.tilted (fun a => smartPathEnergyNoAux u t ω (a, 0))) f
          (fun a => deriv (deriv u) (smartPathFieldNoAux t ω (a, 0) j₀) +
            deriv u (smartPathFieldNoAux t ω (a, 0) j₀) ^ 2) ∂(smartPathDisorder Pold v) -
        (v : ℝ) * ∫ ω, replicaPairAverage
          (Measure.count.tilted (fun a => smartPathEnergyNoAux u t ω (a, 0))) f
          (fun a b => ((a.2 : ℤ) : ℝ) * ((b.2 : ℤ) : ℝ)) ∂(smartPathDisorder Pold v)) t := by
  have h := hasDerivAt_integral_integral_pi_perceptron_smart_path_noAux (t := t) ht hu v
    (Pold := Pold) f
  refine h.congr_deriv ?_
  have hm := hu.measurable
  have hD : ∀ x, u x ≤ B := fun x => hu.le x
  have hk (k : Fin M) : ∫ ω, replicaPairAverage
      (Measure.count.tilted (fun a => smartPathEnergyNoAux u t ω (a, 0))) f
      (smartPathPotentialKernelNoAux u t ω k) ∂(smartPathDisorder Pold v) =
      ∫ ω, replicaPairAverage
      (Measure.count.tilted (fun a => smartPathEnergyNoAux u t ω (a, 0))) f
      (smartPathPotentialKernelNoAux u t ω j₀) ∂(smartPathDisorder Pold v) := by
    have := integral_replicaPairAverage_swap (μ := smartPathBaseNoAux N M) (t := t) hu v k j₀
      (measurePreserving_smartPathStateSwap_noAux k j₀) (hPold k) f j₀
    simpa only [Equiv.swap_apply_right, replicaPairAverage_potentialKernel_noAux_eq_spin hm hD t]
      using this
  have hd (k : Fin M) : ∫ ω, replicaDiff
      (Measure.count.tilted (fun a => smartPathEnergyNoAux u t ω (a, 0))) f
      (fun a => deriv (deriv u) (smartPathFieldNoAux t ω (a, 0) k) +
        deriv u (smartPathFieldNoAux t ω (a, 0) k) ^ 2) ∂(smartPathDisorder Pold v) =
      ∫ ω, replicaDiff (Measure.count.tilted (fun a => smartPathEnergyNoAux u t ω (a, 0))) f
      (fun a => deriv (deriv u) (smartPathFieldNoAux t ω (a, 0) j₀) +
        deriv u (smartPathFieldNoAux t ω (a, 0) j₀) ^ 2) ∂(smartPathDisorder Pold v) := by
    have := integral_replicaDiff_diag_swap (μ := smartPathBaseNoAux N M) (t := t) hu v k j₀
      (measurePreserving_smartPathStateSwap_noAux k j₀) (hPold k) f j₀
    simpa only [Equiv.swap_apply_right, replicaDiff_diag_noAux_eq_spin hm hD t _ f] using
      this
  simp only [hk, hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end SpinGlasses
