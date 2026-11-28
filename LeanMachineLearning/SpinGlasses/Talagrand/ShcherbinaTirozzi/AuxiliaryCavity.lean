/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.Analysis.Calculus.GronwallBackward
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProdFactorization
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.CavityDerivative
public import LeanMachineLearning.SpinGlasses.Talagrand.ShcherbinaTirozzi.RSEquations

/-!
# The Shcherbina--Tirozzi model: the auxiliary cavity path `ν_{t,v}` (Talagrand Section 3.2)

For a system on `ℝ^(N+1)` with `M` old constraints and one isolated constraint (so `M + 1` total
constraints, corresponding to Talagrand's `M - 1` and `M`), write `⟨·⟩_{t,∼}` for the cavity Gibbs
measure of the `M` old constraints (Eq. (3.88)). Attach an independent standard Gaussian `z` to the
quenched disorder and independent standard Gaussians `(ξ^ℓ)` to the replicas, and set
`θ^ℓ = √q z + √(ρ - q) ξ^ℓ` (Eq. (3.89)), `S_v^ℓ = √v S_{last,t}(σ^ℓ) + √(1 - v) θ^ℓ` (Eq. (3.90)).

Rather than introducing a separate definition for `ν_{t,v}` (Eq. (3.91)), we realize the quenched
measure at fixed disorder and `z` as the replica product of the tilted measure
`((G_{t,∼} × 𝒩(0,1)).tilted (fun p => u (S_v p)))` (whose equivalence with the ratio (3.91) is
`MeasureTheory.integral_pi_tilted_add_eq_div`), and for spin-only observables of one replica as the
Gibbs measure of the smoothed Hamiltonian (3.99).

## Main declarations

* `SpinGlasses.integral_pi_shcherbinaTirozziAuxCavity_one`: `ν_{t,1}(f) = ν_t(f)`.
* `SpinGlasses.integral_pi_shcherbinaTirozziAuxCavity_eq_div`: equivalence with the ratio (3.91).
* `SpinGlasses.integral_shcherbinaTirozziAuxCavity_zero`,
  `SpinGlasses.integral_shcherbinaTirozziAuxCavity_zero_deriv_mul`,
  `SpinGlasses.integral_shcherbinaTirozziAuxCavity_zero_deriv_two`: Lemma 3.2.7
  (Eqs. (3.92)--(3.94)),
  proved first for an arbitrary σ-finite old measure and specialized to `ν_{t,0}`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology RealInnerProductSpace

namespace SpinGlasses

local notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)

section GeneralEndpoint

variable {Ω α R : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [Fintype R]

/-- **General `v = 0` decoupling (model-free core of Lemma 3.2.7, Eq. (3.92)):** for any σ-finite
old measure `μ`, when the perturbation `u (√q z + c ξ)` depends only on `z` and the replica's
fresh Gaussian `ξ`, the extended replica average of an old-configuration observable `f` equals its
`μ`-Gibbs average. -/
theorem integral_pi_tilted_prod_gaussian_zero_observable {μ : Measure α} [SigmaFinite μ]
    {E : α → ℝ} {u : ℝ → ℝ} (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0) (q c z : ℝ)
    (f : (R → α) → ℝ) :
    ∫ σ : R → α × ℝ, f (fun l => (σ l).1)
        ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted
          fun p : α × ℝ => E p.1 + u (Real.sqrt q * z + c * p.2)) =
      ∫ a : R → α, f a ∂(Measure.pi fun _ : R => μ.tilted E) := by
  have hZ : Integrable (fun ξ : ℝ => Real.exp (u (Real.sqrt q * z + c * ξ))) (gaussianReal 0 1) :=
    integrable_exp_comp_add_gaussianReal hu hu0 (Real.sqrt q * z) c
  have : IsProbabilityMeasure ((gaussianReal 0 1).tilted
      fun ξ : ℝ => u (Real.sqrt q * z + c * ξ)) := isProbabilityMeasure_tilted hZ
  have h := integral_pi_tilted_prod_add_mul (μ := μ) (ν := gaussianReal 0 1) (ι := R)
    E (fun ξ : ℝ => u (Real.sqrt q * z + c * ξ)) f (fun _ => 1)
  simpa using h

/-- **Integrating out the fresh Gaussians (model-free core of the smoothed Hamiltonian (3.99)):**
if the perturbation is `u (s x + c ξ)` with `u ≤ 0` and `ξ ~ 𝒩(0, 1)` fresh for each replica, the
replica average of an observable of the old configurations is its average under the energy
`E x + log 𝔼_ξ exp u (s x + c ξ)`. -/
theorem integral_pi_tilted_prod_gaussianReal_eq_smoothed {μ : Measure α} [SigmaFinite μ]
    {E s : α → ℝ} {u : ℝ → ℝ} (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0) (hs : Measurable s)
    (hE : Integrable (fun x => Real.exp (E x)) μ) (c : ℝ) {f : (R → α) → ℝ} (hf : Measurable f) :
    ∫ σ : R → α × ℝ, f (fun l => (σ l).1)
        ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted
          fun p : α × ℝ => E p.1 + u (s p.1 + c * p.2)) =
      ∫ a : R → α, f a ∂(Measure.pi fun _ : R => μ.tilted fun x =>
        E x + Real.log (∫ ξ, Real.exp (u (s x + c * ξ)) ∂(gaussianReal 0 1))) := by
  have hum : Measurable fun p : α × ℝ => Real.exp (u (s p.1 + c * p.2)) :=
    (hu.comp ((hs.comp measurable_fst).add (measurable_snd.const_mul c))).exp
  have hEi : Integrable (fun p : α × ℝ => Real.exp (E p.1 + u (s p.1 + c * p.2)))
      (μ.prod (gaussianReal 0 1)) := by
    have h1 := hE.comp_fst (gaussianReal 0 1)
    simp_rw [Real.exp_add]
    refine h1.mono' (h1.aestronglyMeasurable.mul hum.aestronglyMeasurable)
      (ae_of_all _ fun p => ?_)
    rw [Real.norm_of_nonneg (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.exp_le_one_iff.2 (hu0 _))
  have hfib : ∀ x : α,
      Real.log (∫ ξ, Real.exp (E x + u (s x + c * ξ)) ∂(gaussianReal 0 1)) =
        E x + Real.log (∫ ξ, Real.exp (u (s x + c * ξ)) ∂(gaussianReal 0 1)) := fun x => by
    simp_rw [Real.exp_add]
    rw [integral_const_mul, Real.log_mul (Real.exp_pos _).ne'
      (integral_exp_comp_add_gaussianReal_pos hu hu0 _ _).ne', Real.log_exp]
  rw [integral_pi_tilted_prod_fst hEi hf]
  simp_rw [hfib]

/-- **General `v = 0` decoupling for a pair of derivatives (model-free core of Eq. (3.93)):** for
distinct replicas `l₁ ≠ l₂`, the extended replica average of `u'(θ^{l₁}) u'(θ^{l₂}) f` at `v = 0`
is `⟨f⟩_E` times `(𝔼_ξ [u'(θ) e^{u(θ)}] / 𝔼_ξ [e^{u(θ)}])²`. -/
theorem integral_pi_tilted_prod_gaussian_zero_deriv_mul {μ : Measure α} [SigmaFinite μ]
    {E : α → ℝ} {u : ℝ → ℝ} (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0) (q c z : ℝ)
    {l₁ l₂ : R} (hne : l₁ ≠ l₂) (f : (R → α) → ℝ) :
    ∫ σ : R → α × ℝ,
        (deriv u (Real.sqrt q * z + c * (σ l₁).2) * deriv u (Real.sqrt q * z + c * (σ l₂).2)) *
          f (fun l => (σ l).1)
        ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted
          fun p : α × ℝ => E p.1 + u (Real.sqrt q * z + c * p.2)) =
      ((∫ ξ, deriv u (Real.sqrt q * z + c * ξ) * Real.exp (u (Real.sqrt q * z + c * ξ))
          ∂(gaussianReal 0 1)) /
        ∫ ξ, Real.exp (u (Real.sqrt q * z + c * ξ)) ∂(gaussianReal 0 1)) ^ 2 *
      ∫ a : R → α, f a ∂(Measure.pi fun _ : R => μ.tilted E) := by
  have hZ : Integrable (fun ξ : ℝ => Real.exp (u (Real.sqrt q * z + c * ξ))) (gaussianReal 0 1) :=
    integrable_exp_comp_add_gaussianReal hu hu0 (Real.sqrt q * z) c
  have : IsProbabilityMeasure ((gaussianReal 0 1).tilted
      fun ξ : ℝ => u (Real.sqrt q * z + c * ξ)) := isProbabilityMeasure_tilted hZ
  have hθ : Measurable fun ξ : ℝ => deriv u (Real.sqrt q * z + c * ξ) :=
    (measurable_deriv u).comp (measurable_const.add (measurable_const.mul measurable_id))
  have h := integral_pi_tilted_prod_add_mul (μ := μ) (ν := gaussianReal 0 1) (ι := R)
    E (fun ξ : ℝ => u (Real.sqrt q * z + c * ξ)) f
    (fun τ => deriv u (Real.sqrt q * z + c * τ l₁) * deriv u (Real.sqrt q * z + c * τ l₂))
  have hcomm : (∫ σ : R → α × ℝ,
        (deriv u (Real.sqrt q * z + c * (σ l₁).2) * deriv u (Real.sqrt q * z + c * (σ l₂).2)) *
          f (fun l => (σ l).1)
        ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted
          fun p : α × ℝ => E p.1 + u (Real.sqrt q * z + c * p.2))) =
      ∫ σ : R → α × ℝ, f (fun l => (σ l).1) *
        (deriv u (Real.sqrt q * z + c * (σ l₁).2) * deriv u (Real.sqrt q * z + c * (σ l₂).2))
        ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted
          fun p : α × ℝ => E p.1 + u (Real.sqrt q * z + c * p.2)) :=
    integral_congr_ae (ae_of_all _ fun _ => mul_comm _ _)
  rw [hcomm, h, integral_pi_mul_of_ne _ hne hθ hθ, integral_tilted_eq_div, ← sq, mul_comm]

/-- **General `v = 0` decoupling for `u'' + u'²` (model-free core of Eq. (3.94)):** for any replica
`l₁ : R`, the extended replica average of `(u''(θ^{l₁}) + u'(θ^{l₁})²) f` at `v = 0` is `⟨f⟩_E`
times `𝔼_ξ [(u''(θ) + u'(θ)²) e^{u(θ)}] / 𝔼_ξ [e^{u(θ)}]`. -/
theorem integral_pi_tilted_prod_gaussian_zero_deriv_two {μ : Measure α} [SigmaFinite μ]
    {E : α → ℝ} {u : ℝ → ℝ} (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0) (q c z : ℝ)
    (l₁ : R) (f : (R → α) → ℝ) :
    ∫ σ : R → α × ℝ,
        (deriv (deriv u) (Real.sqrt q * z + c * (σ l₁).2) +
          deriv u (Real.sqrt q * z + c * (σ l₁).2) ^ 2) * f (fun l => (σ l).1)
        ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted
          fun p : α × ℝ => E p.1 + u (Real.sqrt q * z + c * p.2)) =
      ((∫ ξ, (deriv (deriv u) (Real.sqrt q * z + c * ξ) +
          deriv u (Real.sqrt q * z + c * ξ) ^ 2) * Real.exp (u (Real.sqrt q * z + c * ξ))
          ∂(gaussianReal 0 1)) /
        ∫ ξ, Real.exp (u (Real.sqrt q * z + c * ξ)) ∂(gaussianReal 0 1)) *
      ∫ a : R → α, f a ∂(Measure.pi fun _ : R => μ.tilted E) := by
  have hZ : Integrable (fun ξ : ℝ => Real.exp (u (Real.sqrt q * z + c * ξ))) (gaussianReal 0 1) :=
    integrable_exp_comp_add_gaussianReal hu hu0 (Real.sqrt q * z) c
  set γ_z := (gaussianReal 0 1).tilted fun ξ : ℝ => u (Real.sqrt q * z + c * ξ)
  have : IsProbabilityMeasure γ_z := isProbabilityMeasure_tilted hZ
  set ψ : ℝ → ℝ := fun x => deriv (deriv u) x + deriv u x ^ 2
  have hψm : Measurable fun ξ : ℝ => ψ (Real.sqrt q * z + c * ξ) :=
    ((measurable_deriv (deriv u)).add ((measurable_deriv u).pow_const 2)).comp
      (measurable_const.add (measurable_const.mul measurable_id))
  have h := integral_pi_tilted_prod_add_mul (μ := μ) (ν := gaussianReal 0 1) (ι := R)
    E (fun ξ : ℝ => u (Real.sqrt q * z + c * ξ)) f
    (fun τ => ψ (Real.sqrt q * z + c * τ l₁))
  have h1 : ∫ τ : R → ℝ, ψ (Real.sqrt q * z + c * τ l₁) ∂(Measure.pi fun _ : R => γ_z) =
      ∫ ξ : ℝ, ψ (Real.sqrt q * z + c * ξ) ∂γ_z :=
    integral_comp_eval (μ := fun _ : R => γ_z) (i := l₁)
      (f := fun ξ => ψ (Real.sqrt q * z + c * ξ)) hψm.aestronglyMeasurable
  have hcomm : (∫ σ : R → α × ℝ, ψ (Real.sqrt q * z + c * (σ l₁).2) * f (fun l => (σ l).1)
        ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted
          fun p : α × ℝ => E p.1 + u (Real.sqrt q * z + c * p.2))) =
      ∫ σ : R → α × ℝ, f (fun l => (σ l).1) * ψ (Real.sqrt q * z + c * (σ l₁).2)
        ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted
          fun p : α × ℝ => E p.1 + u (Real.sqrt q * z + c * p.2)) :=
    integral_congr_ae (ae_of_all _ fun _ => mul_comm _ _)
  change ∫ σ : R → α × ℝ, ψ (Real.sqrt q * z + c * (σ l₁).2) * f (fun l => (σ l).1)
      ∂(Measure.pi fun _ : R => (μ.prod (gaussianReal 0 1)).tilted
        fun p : α × ℝ => E p.1 + u (Real.sqrt q * z + c * p.2)) = _
  rw [hcomm, h, h1, integral_tilted_eq_div, mul_comm]

end GeneralEndpoint

section ModelEndpoint

variable {N M : ℕ} {R : Type*} [Fintype R]

/-- The disorder `((y, (g, g₀)), z)` of the auxiliary cavity system with `M + 1` constraints and
shared Gaussian `z`. -/
local notation "AuxDis" =>
  (ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) × ℝ

/-- The law of `AuxDis` with `y ~ 𝒩(0, r)` and standard Gaussian `g, g₀, z`. -/
local notation "auxLaw " r:arg =>
  Measure.prod
    (Measure.prod (gaussianReal 0 r)
      (Measure.prod
        (Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)))
    (gaussianReal 0 1)

/-- The cavity field `S_{k,t}` on `ℝ^(N+1)`. -/
local notation "cfield⟨" t ", " g ", " k ", " σ "⟩" =>
  (Real.sqrt (N + 1))⁻¹ * ((∑ i : Fin N, g k (Fin.castSucc i) * σ (Fin.castSucc i)) +
    Real.sqrt t * (g k (Fin.last N) * σ (Fin.last N)))

/-- Dropping the last constraint: integrating a function of the old disorder against the law with
`M + 1` constraints gives its integral against the law with `M` constraints (no measurability is
needed). -/
private theorem integral_comp_castSucc_disorder (r : ℝ≥0)
    (G : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) → ℝ) :
    ∫ d : ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)),
        G (d.1, (fun j => d.2.1 j.castSucc, d.2.2))
        ∂((gaussianReal 0 r).prod
          ((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0
              1).prod
            (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))) =
      ∫ d₀, G d₀
        ∂((gaussianReal 0 r).prod
          ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))) := by
  set γ : Measure (Fin (N + 1) → ℝ) := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
  set Pold : Measure (Fin M → Fin (N + 1) → ℝ) := Measure.pi fun _ : Fin M => γ
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => Fin (N + 1) → ℝ) (Fin.last M)
  have he : MeasurePreserving e (Measure.pi fun _ : Fin (M + 1) => γ) (γ.prod Pold) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => γ) (Fin.last M)
  -- move the last row to the front
  have h1 := (measurePreserving_prodAssoc γ Pold γ).comp (he.prod (MeasurePreserving.id γ))
  have h2 := (MeasurePreserving.id (gaussianReal 0 r)).prod h1
  have h3 := (measurePreserving_prodAssoc (gaussianReal 0 r) γ (Pold.prod γ)).symm
    MeasurableEquiv.prodAssoc
  have h4 := (Measure.measurePreserving_swap (μ := gaussianReal 0 r) (ν := γ)).prod
    (MeasurePreserving.id (Pold.prod γ))
  have h5 := measurePreserving_prodAssoc γ (gaussianReal 0 r) (Pold.prod γ)
  have h := (h5.comp (h4.comp (h3.comp h2)))
  have hemb : MeasurableEmbedding fun d : ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) ×
      (Fin (N + 1) → ℝ)) => ((e d.2.1).1, (d.1, ((e d.2.1).2, d.2.2))) :=
    (((MeasurableEquiv.refl ℝ).prodCongr ((e.prodCongr (MeasurableEquiv.refl _)).trans
      MeasurableEquiv.prodAssoc)).trans (MeasurableEquiv.prodAssoc.symm.trans
        ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl _)).trans
          MeasurableEquiv.prodAssoc))).measurableEmbedding
  have h' : MeasurePreserving (fun d : ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) ×
      (Fin (N + 1) → ℝ)) => ((e d.2.1).1, (d.1, ((e d.2.1).2, d.2.2))))
      ((gaussianReal 0 r).prod ((Measure.pi fun _ : Fin (M + 1) => γ).prod γ))
      (γ.prod ((gaussianReal 0 r).prod (Pold.prod γ))) := h
  have hint := h'.integral_comp hemb fun q => G q.2
  rw [integral_fun_snd, probReal_univ, one_smul] at hint
  refine Eq.trans (integral_congr_ae (ae_of_all _ fun d => ?_)) hint
  have hrows : (e d.2.1).2 = fun j => d.2.1 j.castSucc := by
    funext j
    change d.2.1 ((Fin.last M).succAbove j) = _
    rw [Fin.succAbove_last]
  simp only [hrows]

/-- Splitting the cavity Hamiltonian with `M + 1` constraints into the `M` old constraints
`Fin.castSucc j` and the last constraint `Fin.last M`. -/
theorem neg_shcherbinaTirozziCavityHamiltonian_succ (κ h r rBar t y : ℝ) (u : ℝ → ℝ)
    (g : Fin (M + 1) → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ) (σ : ℝ^(N + 1)) :
    -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u g g₀ σ =
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u (fun j => g j.castSucc) g₀ σ +
        u cfield⟨t, g, Fin.last M, σ⟩ := by
  simp only [shcherbinaTirozziCavityHamiltonian, Fin.sum_univ_castSucc (f := fun k => u _)]
  ring

/-- **Equivalence with the ratio formula (3.91):** for `κ > 0`, `u ≤ 0` measurable, and
`(1 - t) (r - r̄) ≥ 0`, the replica average under the tilted product measure
`((volume × 𝒩(0,1)).tilted (-H_{M,t} + u(S_v)))` equals the ratio
`⟨Y exp (∑_ℓ u(S_v^ℓ))⟩_{t,∼} / ⟨𝔼_ξ exp u(S_v^1)⟩_{t,∼}^{|R|}` of Eq. (3.91). -/
theorem integral_pi_shcherbinaTirozziAuxCavity_eq_div {κ h r rBar t y q ρ v z : ℝ} (hκ : 0 < κ)
    (hq_t : 0 ≤ (1 - t) * (r - rBar)) {u : ℝ → ℝ} (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0)
    (g : Fin (M + 1) → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ)
    (Y : (R → ℝ^(N + 1) × ℝ) → ℝ) :
    let E_old : ℝ^(N + 1) → ℝ := fun σ =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u (fun j => g j.castSucc) g₀ σ
    let S_v : ℝ^(N + 1) × ℝ → ℝ := fun p =>
      Real.sqrt v * cfield⟨t, g, Fin.last M, p.1⟩ +
        Real.sqrt (1 - v) * (Real.sqrt q * z + Real.sqrt (ρ - q) * p.2)
    let G_old : Measure (ℝ^(N + 1)) := (volume : Measure (ℝ^(N + 1))).tilted E_old
    ∫ σ : R → ℝ^(N + 1) × ℝ, Y σ
        ∂(Measure.pi fun _ : R =>
          ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
            fun p => E_old p.1 + u (S_v p)) =
      (∫ σ : R → ℝ^(N + 1) × ℝ, Y σ * Real.exp (∑ l, u (S_v (σ l)))
          ∂(Measure.pi fun _ : R => G_old.prod (gaussianReal 0 1))) /
        (∫ σ : ℝ^(N + 1), (∫ ξ, Real.exp (u (S_v (σ, ξ))) ∂(gaussianReal 0 1)) ∂G_old) ^
          Fintype.card R := by
  intro E_old S_v G_old
  have hEi : Integrable (fun σ : ℝ^(N + 1) => Real.exp (E_old σ)) volume :=
    integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ hq_t hu hu0 _ g₀
  have hprod_eq : ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
      (fun p : ℝ^(N + 1) × ℝ => E_old p.1) = G_old.prod (gaussianReal 0 1) :=
    tilted_prod_comp_fst (volume : Measure (ℝ^(N + 1))) (gaussianReal 0 1) E_old
  have hdiv := integral_pi_tilted_add_eq_div
    (μ := (volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)) (ι := R)
    (E := fun p : ℝ^(N + 1) × ℝ => E_old p.1) (V := fun p => u (S_v p))
    (hEi.comp_fst (gaussianReal 0 1)) Y
  rw [hprod_eq] at hdiv
  rw [hdiv]
  congr 2
  have hSvm : Measurable S_v := by
    have hσ : ∀ i : Fin (N + 1), Measurable fun p : ℝ^(N + 1) × ℝ => p.1 i := fun i =>
      ((PiLp.continuous_apply 2 (fun _ : Fin (N + 1) => ℝ) i).measurable).comp measurable_fst
    have hf1 : Measurable fun p : ℝ^(N + 1) × ℝ => cfield⟨t, g, Fin.last M, p.1⟩ :=
      (((Finset.measurable_sum _ fun i _ => (hσ i.castSucc).const_mul _).add
        (((hσ (Fin.last N)).const_mul _).const_mul _)).const_mul _)
    exact (hf1.const_mul _).add ((measurable_const.add (measurable_snd.const_mul _)).const_mul _)
  have : IsProbabilityMeasure G_old := isProbabilityMeasure_tilted hEi
  have hVi : Integrable (fun p : ℝ^(N + 1) × ℝ => Real.exp (u (S_v p)))
      (G_old.prod (gaussianReal 0 1)) :=
    Integrable.of_bound (hu.comp hSvm).exp.aestronglyMeasurable 1 (ae_of_all _ fun p => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.2 (hu0 _))
  rw [integral_prod _ hVi]

/-- **At `v = 1`, `ν_{t,1}(f) = ν_t(f)`:** for an observable `f` of the spins only, at `v = 1` the
auxiliary coordinates `(z, ξ^ℓ)` drop out and the expectation equals the full cavity average with
`M + 1` constraints. -/
theorem integral_pi_shcherbinaTirozziAuxCavity_one (κ h : ℝ) (r : ℝ≥0) (rBar t q ρ : ℝ)
    (u : ℝ → ℝ) (f : (R → ℝ^(N + 1)) → ℝ) :
    let E_old : (ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) → ℝ^(N + 1) → ℝ :=
      fun d σ => -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u
        (fun j => d.2.1 j.castSucc) d.2.2 σ
    let S_one : AuxDis → ℝ^(N + 1) × ℝ → ℝ := fun w p =>
      Real.sqrt 1 * cfield⟨t, w.1.2.1, Fin.last M, p.1⟩ +
        Real.sqrt (1 - 1) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2)
    ∫ w : AuxDis, ∫ σ : R → ℝ^(N + 1) × ℝ, f (fun l => (σ l).1)
        ∂(Measure.pi fun _ : R =>
          ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
            fun p => E_old w.1 p.1 + u (S_one w p)) ∂(auxLaw r) =
      ∫ d, ∫ a : R → ℝ^(N + 1), f a
        ∂(Measure.pi fun _ : R => (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 σ)
        ∂((gaussianReal 0 r).prod
          (((Measure.pi fun _ : Fin (M + 1) => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0
              1).prod
            (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)))) := by
  intro E_old S_one
  obtain ⟨G, hG⟩ : ∃ G : ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) → ℝ,
      G = fun d => ∫ a : R → ℝ^(N + 1), f a
        ∂(Measure.pi fun _ : R => (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 σ) := ⟨_, rfl⟩
  have hpt : ∀ w : AuxDis,
      ∫ σ : R → ℝ^(N + 1) × ℝ, f (fun l => (σ l).1)
          ∂(Measure.pi fun _ : R =>
            ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
              fun p => E_old w.1 p.1 + u (S_one w p)) = G w.1 := by
    intro w
    have heq : (fun p : ℝ^(N + 1) × ℝ => E_old w.1 p.1 + u (S_one w p)) =
        fun p => (-shcherbinaTirozziCavityHamiltonian κ h r rBar t w.1.1 u w.1.2.1 w.1.2.2 p.1) +
          (0 : ℝ → ℝ) p.2 := by
      funext p
      dsimp only [E_old, S_one]
      rw [neg_shcherbinaTirozziCavityHamiltonian_succ]
      simp
    rw [heq, hG]
    have h := integral_pi_tilted_prod_add_mul (μ := (volume : Measure (ℝ^(N + 1))))
      (ν := gaussianReal 0 1) (ι := R)
      (fun σ => -shcherbinaTirozziCavityHamiltonian κ h r rBar t w.1.1 u w.1.2.1 w.1.2.2 σ)
      (0 : ℝ → ℝ) f (fun _ => 1)
    simpa using h
  refine Eq.trans (integral_congr_ae (ae_of_all _ hpt)) ?_
  refine Eq.trans (integral_fun_fst (ν := gaussianReal 0 1) G) ?_
  rw [probReal_univ, one_smul]
  subst hG
  rfl

/-- **Talagrand, Lemma 3.2.7, Eq. (3.92):** at `v = 0`, `ν_{t,0}(f) = 𝔼 ⟨f⟩_{t,∼}` for any spin
observable `f` (integrability is not even needed: the `z` and `ξ` integrals factor out with mass
`1`). -/
theorem integral_shcherbinaTirozziAuxCavity_zero (κ h : ℝ) (r : ℝ≥0) (rBar t q ρ : ℝ)
    {u : ℝ → ℝ} (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0) (f : (R → ℝ^(N + 1)) → ℝ) :
    let P_old := (gaussianReal 0 r).prod
      ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))
    let E_old : (ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) → ℝ^(N + 1) → ℝ :=
      fun d σ => -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u
        (fun j => d.2.1 j.castSucc) d.2.2 σ
    let S_zero : AuxDis → ℝ^(N + 1) × ℝ → ℝ := fun w p =>
      Real.sqrt 0 * cfield⟨t, w.1.2.1, Fin.last M, p.1⟩ +
        Real.sqrt (1 - 0) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2)
    ∫ w : AuxDis, ∫ σ : R → ℝ^(N + 1) × ℝ, f (fun l => (σ l).1)
        ∂(Measure.pi fun _ : R =>
          ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
            fun p => E_old w.1 p.1 + u (S_zero w p)) ∂(auxLaw r) =
      ∫ d₀, ∫ a : R → ℝ^(N + 1), f a
        ∂(Measure.pi fun _ : R => (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar t d₀.1 u d₀.2.1 d₀.2.2 σ) ∂P_old := by
  intro P_old E_old S_zero
  obtain ⟨G, hG⟩ : ∃ G : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) → ℝ,
      G = fun d₀ => ∫ a : R → ℝ^(N + 1), f a
        ∂(Measure.pi fun _ : R => (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          -shcherbinaTirozziCavityHamiltonian κ h r rBar t d₀.1 u d₀.2.1 d₀.2.2 σ) := ⟨_, rfl⟩
  have hpt : ∀ w : AuxDis, ∫ σ : R → ℝ^(N + 1) × ℝ, f (fun l => (σ l).1)
        ∂(Measure.pi fun _ : R =>
          ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
            fun p => E_old w.1 p.1 + u (S_zero w p)) =
      G (w.1.1, (fun j => w.1.2.1 j.castSucc, w.1.2.2)) := fun w => by
    have hS0 : (fun p : ℝ^(N + 1) × ℝ => E_old w.1 p.1 + u (S_zero w p)) =
        fun p => E_old w.1 p.1 + u (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2) := by
      funext p
      dsimp only [S_zero]
      simp
    rw [hS0, integral_pi_tilted_prod_gaussian_zero_observable hu hu0 q (Real.sqrt (ρ - q)) w.2 f,
      hG]
  refine Eq.trans (integral_congr_ae (ae_of_all _ hpt)) ?_
  refine Eq.trans (integral_fun_fst (ν := gaussianReal 0 1)
    (fun d : ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) =>
      G (d.1, (fun j => d.2.1 j.castSucc, d.2.2)))) ?_
  rw [probReal_univ, one_smul]
  refine Eq.trans (integral_comp_castSucc_disorder (N := N) (M := M) r G) ?_
  subst hG
  rfl

/-- At `v = 0`, a weight of the auxiliary coordinates whose one-disorder average factors as
`⟨f⟩ * k z` contributes the factor `∫ k` to `ν_{t,0}`. -/
private theorem integral_aux_zero_of_factor (r : ℝ≥0)
    (G : ℝ × ((Fin M → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) → ℝ) (k : ℝ → ℝ)
    (J : ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) → ℝ → ℝ)
    (hJ : ∀ d z, J d z = G (d.1, (fun j => d.2.1 j.castSucc, d.2.2)) * k z) :
    ∫ w : AuxDis, J w.1 w.2 ∂(auxLaw r) =
      (∫ z, k z ∂(gaussianReal 0 1)) *
        ∫ d₀, G d₀
          ∂((gaussianReal 0 r).prod
            ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
              (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))) := by
  simp_rw [hJ]
  rw [integral_prod_mul (fun d : ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ)) =>
      G (d.1, (fun j => d.2.1 j.castSucc, d.2.2))) k,
    integral_comp_castSucc_disorder (N := N) (M := M) r G, mul_comm]

/-- **Talagrand, Lemma 3.2.7, Eq. (3.93):** for distinct replicas `l₁ ≠ l₂`, at `v = 0`,
`α ν_{t,0}(u'(S_0^{l₁}) u'(S_0^{l₂}) f) = r 𝔼 ⟨f⟩_{t,∼}` where
`r = α 𝔼_z [(𝔼_ξ u'(θ) e^{u(θ)} / 𝔼_ξ e^{u(θ)})²]`. -/
theorem integral_shcherbinaTirozziAuxCavity_zero_deriv_mul (α κ h : ℝ) (r : ℝ≥0)
    (rBar t q ρ : ℝ) {u : ℝ → ℝ} (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0)
    {l₁ l₂ : R} (hne : l₁ ≠ l₂) (f : (R → ℝ^(N + 1)) → ℝ) :
    let P_old := (gaussianReal 0 r).prod
      ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))
    let E_old : (ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) → ℝ^(N + 1) → ℝ :=
      fun d σ => -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u
        (fun j => d.2.1 j.castSucc) d.2.2 σ
    let S_zero : AuxDis → ℝ^(N + 1) × ℝ → ℝ := fun w p =>
      Real.sqrt 0 * cfield⟨t, w.1.2.1, Fin.last M, p.1⟩ +
        Real.sqrt (1 - 0) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2)
    let c : ℝ := Real.sqrt (ρ - q)
    let V : ℝ → ℝ := fun y =>
      (∫ ξ, deriv u (y + c * ξ) * Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) /
        ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)
    α * (∫ w : AuxDis, ∫ σ : R → ℝ^(N + 1) × ℝ,
          (deriv u (S_zero w (σ l₁)) * deriv u (S_zero w (σ l₂))) * f (fun l => (σ l).1)
          ∂(Measure.pi fun _ : R =>
            ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
              fun p => E_old w.1 p.1 + u (S_zero w p)) ∂(auxLaw r)) =
      (α * ∫ z, V (Real.sqrt q * z) ^ 2 ∂(gaussianReal 0 1)) *
        ∫ d₀, ∫ a : R → ℝ^(N + 1), f a
          ∂(Measure.pi fun _ : R => (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
            -shcherbinaTirozziCavityHamiltonian κ h r rBar t d₀.1 u d₀.2.1 d₀.2.2 σ) ∂P_old := by
  intro P_old E_old S_zero c V
  have hS0 : ∀ w p, S_zero w p = Real.sqrt q * w.2 + c * p.2 := fun w p => by
    dsimp only [S_zero, c]; simp
  simp_rw [hS0]
  rw [mul_assoc]
  congr 1
  refine integral_aux_zero_of_factor (N := N) (M := M) r
    (fun d => ∫ a : R → ℝ^(N + 1), f a ∂(Measure.pi fun _ : R =>
      (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 σ))
    (fun z => V (Real.sqrt q * z) ^ 2) (fun d z => ∫ σ : R → ℝ^(N + 1) × ℝ,
      (deriv u (Real.sqrt q * z + c * (σ l₁).2) * deriv u (Real.sqrt q * z + c * (σ l₂).2)) *
        f (fun l => (σ l).1)
      ∂(Measure.pi fun _ : R => ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
        fun p => E_old d p.1 + u (Real.sqrt q * z + c * p.2))) fun d z => ?_
  rw [integral_pi_tilted_prod_gaussian_zero_deriv_mul hu hu0 q c z hne f, mul_comm]

/-- **Talagrand, Lemma 3.2.7, Eq. (3.94):** for any replica `l₁`, at `v = 0`,
`α ν_{t,0}((u''(S_0^{l₁}) + u'(S_0^{l₁})²) f) = r̄ 𝔼 ⟨f⟩_{t,∼}` where
`r̄ = α 𝔼_z [𝔼_ξ (u''(θ) + u'(θ)²) e^{u(θ)} / 𝔼_ξ e^{u(θ)}]`. -/
theorem integral_shcherbinaTirozziAuxCavity_zero_deriv_two (α κ h : ℝ) (r : ℝ≥0)
    (rBar t q ρ : ℝ) {u : ℝ → ℝ} (hu : Measurable u) (hu0 : ∀ x, u x ≤ 0)
    (l₁ : R) (f : (R → ℝ^(N + 1)) → ℝ) :
    let P_old := (gaussianReal 0 r).prod
      ((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1))
    let E_old : (ℝ × ((Fin (M + 1) → Fin (N + 1) → ℝ) × (Fin (N + 1) → ℝ))) → ℝ^(N + 1) → ℝ :=
      fun d σ => -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u
        (fun j => d.2.1 j.castSucc) d.2.2 σ
    let S_zero : AuxDis → ℝ^(N + 1) × ℝ → ℝ := fun w p =>
      Real.sqrt 0 * cfield⟨t, w.1.2.1, Fin.last M, p.1⟩ +
        Real.sqrt (1 - 0) * (Real.sqrt q * w.2 + Real.sqrt (ρ - q) * p.2)
    let c : ℝ := Real.sqrt (ρ - q)
    let W : ℝ → ℝ := fun y =>
      (∫ ξ, (deriv (deriv u) (y + c * ξ) + deriv u (y + c * ξ) ^ 2) *
        Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)) /
        ∫ ξ, Real.exp (u (y + c * ξ)) ∂(gaussianReal 0 1)
    α * (∫ w : AuxDis, ∫ σ : R → ℝ^(N + 1) × ℝ,
          (deriv (deriv u) (S_zero w (σ l₁)) + deriv u (S_zero w (σ l₁)) ^ 2) *
            f (fun l => (σ l).1)
          ∂(Measure.pi fun _ : R =>
            ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
              fun p => E_old w.1 p.1 + u (S_zero w p)) ∂(auxLaw r)) =
      (α * ∫ z, W (Real.sqrt q * z) ∂(gaussianReal 0 1)) *
        ∫ d₀, ∫ a : R → ℝ^(N + 1), f a
          ∂(Measure.pi fun _ : R => (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
            -shcherbinaTirozziCavityHamiltonian κ h r rBar t d₀.1 u d₀.2.1 d₀.2.2 σ) ∂P_old := by
  intro P_old E_old S_zero c W
  have hS0 : ∀ w p, S_zero w p = Real.sqrt q * w.2 + c * p.2 := fun w p => by
    dsimp only [S_zero, c]; simp
  simp_rw [hS0]
  rw [mul_assoc]
  congr 1
  refine integral_aux_zero_of_factor (N := N) (M := M) r
    (fun d => ∫ a : R → ℝ^(N + 1), f a ∂(Measure.pi fun _ : R =>
      (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
        -shcherbinaTirozziCavityHamiltonian κ h r rBar t d.1 u d.2.1 d.2.2 σ))
    (fun z => W (Real.sqrt q * z)) (fun d z => ∫ σ : R → ℝ^(N + 1) × ℝ,
      (deriv (deriv u) (Real.sqrt q * z + c * (σ l₁).2) +
          deriv u (Real.sqrt q * z + c * (σ l₁).2) ^ 2) * f (fun l => (σ l).1)
      ∂(Measure.pi fun _ : R => ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
        fun p => E_old d p.1 + u (Real.sqrt q * z + c * p.2))) fun d z => ?_
  rw [integral_pi_tilted_prod_gaussian_zero_deriv_two hu hu0 q c z l₁ f, mul_comm]

/-- **Smoothed marginal representation (Eq. (3.99)):** for a measurable spin-only observable `f` of
`R` replicas, the `R`-replica average under `((volume × 𝒩(0,1)).tilted (E_old + u ∘ S_v))` equals
the `R`-replica average under `volume.tilted (E_old + u_v(√v S_last + √(1 - v) √q z))`, where
`u_v(x) = log 𝔼_ξ exp u(x + √(1 - v) √(ρ - q) ξ)`. -/
theorem integral_pi_shcherbinaTirozziAuxCavity_eq_smoothed {κ h r rBar t y q ρ v z : ℝ}
    (hκ : 0 < κ) (hq_t : 0 ≤ (1 - t) * (r - rBar)) {u : ℝ → ℝ} (hu : Measurable u)
    (hu0 : ∀ x, u x ≤ 0) (g : Fin (M + 1) → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ)
    {f : (R → ℝ^(N + 1)) → ℝ} (hf : Measurable f) :
    let E_old : ℝ^(N + 1) → ℝ := fun σ =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u (fun j => g j.castSucc) g₀ σ
    let S_v : ℝ^(N + 1) × ℝ → ℝ := fun p =>
      Real.sqrt v * cfield⟨t, g, Fin.last M, p.1⟩ +
        Real.sqrt (1 - v) * (Real.sqrt q * z + Real.sqrt (ρ - q) * p.2)
    let u_v : ℝ → ℝ := fun x =>
      Real.log (∫ ξ, Real.exp (u (x + Real.sqrt (1 - v) * Real.sqrt (ρ - q) * ξ))
        ∂(gaussianReal 0 1))
    ∫ σ : R → ℝ^(N + 1) × ℝ, f (fun l => (σ l).1)
        ∂(Measure.pi fun _ : R =>
          ((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
            fun p => E_old p.1 + u (S_v p)) =
      ∫ a : R → ℝ^(N + 1), f a
        ∂(Measure.pi fun _ : R => (volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          E_old σ + u_v (Real.sqrt v * cfield⟨t, g, Fin.last M, σ⟩ +
            Real.sqrt (1 - v) * Real.sqrt q * z)) := by
  intro E_old S_v u_v
  have hs : Measurable fun σ : ℝ^(N + 1) => Real.sqrt v * cfield⟨t, g, Fin.last M, σ⟩ +
      Real.sqrt (1 - v) * Real.sqrt q * z := Continuous.measurable (by fun_prop)
  have hS : ∀ p : ℝ^(N + 1) × ℝ, S_v p =
      (Real.sqrt v * cfield⟨t, g, Fin.last M, p.1⟩ + Real.sqrt (1 - v) * Real.sqrt q * z) +
        (Real.sqrt (1 - v) * Real.sqrt (ρ - q)) * p.2 := fun p => by
    dsimp only [S_v]; ring
  simp only [hS]
  exact integral_pi_tilted_prod_gaussianReal_eq_smoothed hu hu0 hs
    (integrable_exp_neg_shcherbinaTirozziCavityHamiltonian hκ hq_t hu hu0 _ g₀) _ hf

/-- **One-replica form of `integral_pi_shcherbinaTirozziAuxCavity_eq_smoothed`:** the average of an
old-configuration observable under the one-replica auxiliary cavity state is its average under the
smoothed Hamiltonian (3.99). -/
theorem integral_shcherbinaTirozziAuxCavity_eq_smoothed {κ h r rBar t y q ρ v z : ℝ}
    (hκ : 0 < κ) (hq_t : 0 ≤ (1 - t) * (r - rBar)) {u : ℝ → ℝ} (hu : Measurable u)
    (hu0 : ∀ x, u x ≤ 0) (g : Fin (M + 1) → Fin (N + 1) → ℝ) (g₀ : Fin (N + 1) → ℝ)
    {f : ℝ^(N + 1) → ℝ} (hf : Measurable f) :
    let E_old : ℝ^(N + 1) → ℝ := fun σ =>
      -shcherbinaTirozziCavityHamiltonian κ h r rBar t y u (fun j => g j.castSucc) g₀ σ
    let S_v : ℝ^(N + 1) × ℝ → ℝ := fun p =>
      Real.sqrt v * cfield⟨t, g, Fin.last M, p.1⟩ +
        Real.sqrt (1 - v) * (Real.sqrt q * z + Real.sqrt (ρ - q) * p.2)
    let u_v : ℝ → ℝ := fun x =>
      Real.log (∫ ξ, Real.exp (u (x + Real.sqrt (1 - v) * Real.sqrt (ρ - q) * ξ))
        ∂(gaussianReal 0 1))
    ∫ p : ℝ^(N + 1) × ℝ, f p.1
        ∂(((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
          fun p => E_old p.1 + u (S_v p)) =
      ∫ σ : ℝ^(N + 1), f σ
        ∂((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
          E_old σ + u_v (Real.sqrt v * cfield⟨t, g, Fin.last M, σ⟩ +
            Real.sqrt (1 - v) * Real.sqrt q * z)) := by
  intro E_old S_v u_v
  have hsm := integral_pi_shcherbinaTirozziAuxCavity_eq_smoothed (R := Unit) (κ := κ) (h := h)
    (r := r) (rBar := rBar) (t := t) (y := y) (q := q) (ρ := ρ) (v := v) (z := z) hκ hq_t hu hu0
    g g₀ (f := fun a => f (a ())) (hf.comp (measurable_pi_apply ()))
  have h1 := (measurePreserving_funUnique
    (((volume : Measure (ℝ^(N + 1))).prod (gaussianReal 0 1)).tilted
      fun p => E_old p.1 + u (S_v p)) Unit).integral_comp
    (MeasurableEquiv.funUnique Unit (ℝ^(N + 1) × ℝ)).measurableEmbedding
    (fun p : ℝ^(N + 1) × ℝ => f p.1)
  have h2 := (measurePreserving_funUnique
    ((volume : Measure (ℝ^(N + 1))).tilted fun σ =>
      E_old σ + u_v (Real.sqrt v * cfield⟨t, g, Fin.last M, σ⟩ +
        Real.sqrt (1 - v) * Real.sqrt q * z)) Unit).integral_comp
    (MeasurableEquiv.funUnique Unit (ℝ^(N + 1))).measurableEmbedding f
  exact h1.symm.trans (hsm.trans h2)

end ModelEndpoint

end SpinGlasses
