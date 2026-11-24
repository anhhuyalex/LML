/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IntegrableOfBound
public import LeanMachineLearning.SpinGlasses.Talagrand.Perceptron.InterpolatingCavityBound

/-!
# Overlap concentration along the `s`-interpolating Hamiltonian (Talagrand Section 2.4, Eq. (2.80))

Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 2.4, Eqs. (2.76)--(2.80).

For `s ∈ [0, 1]`, the `s`-interpolating Hamiltonian on `N + 1` spins and `M` constraints is
$$-H_{M, N+1, s}(\sigma, \xi) =
  \sum_{k < M} u\!\left(\sqrt{s}\,S_k(\sigma) +
    \sqrt{1 - s}\,(\sqrt{q}\,z_k + \sqrt{1 - q}\,\xi_k)\right) +
  \sum_{i < N + 1} \sigma_i \sqrt{1 - s}\,z'_i \sqrt{r},$$
where $g_{k,i}, z_k, z'_i \sim \mathcal{N}(0, 1)$ are independent quenched standard Gaussians and
$\xi_k \sim \mathcal{N}(0, 1)$ are auxiliary standard Gaussians ("new spins") integrated per
replica.

We prove site-permutation symmetry Eq. (2.70) for all `s`, decoupling at `t = 0` via two-block
Gaussian rotation (`integral_pi_gaussianReal_scale_eq_prod_linear_combo`), the `(s, t)` smart-path
derivative and endpoint domination, and conclude uniform overlap concentration Eq. (2.80):
$$\forall s \in [0, 1], \quad \nu_s((R_{1,2} - q)^2) \le \frac{L}{N + 1}$$
whenever $\alpha K(D) \le 1$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology

namespace SpinGlasses

universe uR

/-! ### Site-permutation symmetry on `Fin L` for the `s`-interpolating Gibbs average -/

/-- **Site permutation symmetry of the `s`-interpolating perceptron Gibbs average.**
Relabelling spin sites by `pm : Equiv.Perm (Fin L)` leaves the disorder-averaged `R`-replica Gibbs
expectation of the `s`-interpolating Hamiltonian (2.76) invariant, for any `s, q, r ∈ ℝ`. -/
theorem interpolating_replica_site_perm {L M : ℕ} {R : Type uR} [Fintype R]
    {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, u x ≤ B)
    (s q r : ℝ) (pm : Equiv.Perm (Fin L)) (Θ : (R → Fin L → ℤˣ) → ℝ) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin L => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin L => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_base := (Measure.count : Measure (Fin L → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let E (ω : ((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ))
        (x : (Fin L → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (Real.sqrt s * ((Real.sqrt (L : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))) +
      ∑ i : Fin L, ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    ∫ ω, ∫ σ : R → (Fin L → ℤˣ) × (Fin M → ℝ), Θ (fun l i => (σ l).1 (pm i))
        ∂(Measure.pi fun _ : R => μ_base.tilted (E ω)) ∂P =
      ∫ ω, ∫ σ : R → (Fin L → ℤˣ) × (Fin M → ℝ), Θ (fun l => (σ l).1)
        ∂(Measure.pi fun _ : R => μ_base.tilted (E ω)) ∂P := by
  intro P_g P_z P_z' P μ_base E
  let e_spin : (Fin L → ℤˣ) ≃ (Fin L → ℤˣ) := Equiv.arrowCongr pm (Equiv.refl ℤˣ)
  have he_spin (τ : Fin L → ℤˣ) : (fun i => (e_spin τ) (pm i)) = τ :=
    funext fun i => by simp [e_spin]
  let e_col : (Fin L → ℝ) ≃ᵐ (Fin L → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ => ℝ) pm.symm
  have hmp_col : MeasurePreserving ⇑e_col P_z' P_z' :=
    measurePreserving_piCongrLeft (fun _ => gaussianReal 0 1) pm.symm
  let e_mat : (Fin M → Fin L → ℝ) ≃ᵐ (Fin M → Fin L → ℝ) :=
    MeasurableEquiv.piCongrRight fun _ => e_col
  have hmp_mat : MeasurePreserving ⇑e_mat P_g P_g :=
    measurePreserving_pi _ _ fun _ => hmp_col
  let e_dis : ((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ) ≃ᵐ
      ((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ) :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.prodCongr e_mat (MeasurableEquiv.refl _)) e_col
  have hmp_dis : MeasurePreserving ⇑e_dis P P :=
    (hmp_mat.prod (MeasurePreserving.id P_z)).prod hmp_col
  let E_eff (ω : ((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) (τ : Fin L → ℤˣ) : ℝ :=
    (∑ i : Fin L, ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r) +
    ∑ k : Fin M, Real.log (∫ ξ, Real.exp (u (Real.sqrt s *
      ((Real.sqrt (L : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
      Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ))) ∂gaussianReal 0 1)
  have haux (ω : ((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ))
      (Φ : (R → Fin L → ℤˣ) → ℝ) :
      ∫ σ : R → (Fin L → ℤˣ) × (Fin M → ℝ), Φ (fun l => (σ l).1)
        ∂(Measure.pi fun _ : R => μ_base.tilted (E ω)) =
      ∫ τ : R → Fin L → ℤˣ, Φ τ ∂(Measure.pi fun _ : R => Measure.count.tilted (E_eff ω)) := by
    have hE_swap (x : (Fin L → ℤˣ) × (Fin M → ℝ)) :
        E ω x = (∑ i : Fin L, ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r) +
          ∑ k : Fin M, u (Real.sqrt s * ((Real.sqrt (L : ℕ))⁻¹ *
            ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k)) := add_comm _ _
    simp_rw [show E ω = _ from funext hE_swap]
    exact integral_pi_tilted_count_prod_sum (fun _ : Fin M => gaussianReal 0 1)
      (fun τ : Fin L → ℤˣ => ∑ i : Fin L, ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r)
      (fun τ k ξ => u (Real.sqrt s * ((Real.sqrt (L : ℕ))⁻¹ *
        ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ)))
      (fun τ k => hu.comp (by fun_prop)) (fun _ => B) (fun _ _ _ => hB _) Φ
  have hE_eff_eq (ω : ((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) (τ : Fin L → ℤˣ) :
      E_eff ω (e_spin τ) = E_eff (e_dis ω) τ := by
    dsimp only [E_eff]
    congr 1
    · rw [← Equiv.sum_comp pm]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hz'_i : (e_dis ω).2 i = ω.2 (pm i) := by
        change (Equiv.piCongrLeft (fun _ : Fin L => ℝ) pm.symm ω.2) i = ω.2 (pm i)
        rw [Equiv.piCongrLeft_apply]; simp
      have hτ_i : (e_spin τ) (pm i) = τ i := congrFun (he_spin τ) i
      rw [hz'_i, hτ_i]
    · refine Finset.sum_congr rfl fun k _ => congrArg Real.log ?_
      refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
      dsimp only
      have hsum_eq : ∑ i : Fin L, ω.1.1 k i * (((e_spin τ) i : ℤ) : ℝ) =
          ∑ i : Fin L, (e_dis ω).1.1 k i * ((τ i : ℤ) : ℝ) := by
        rw [← Equiv.sum_comp pm]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hg_i : (e_dis ω).1.1 k i = ω.1.1 k (pm i) := by
          change (Equiv.piCongrLeft (fun _ : Fin L => ℝ) pm.symm (ω.1.1 k)) i = ω.1.1 k (pm i)
          rw [Equiv.piCongrLeft_apply]; simp
        have hτ_i : (e_spin τ) (pm i) = τ i := congrFun (he_spin τ) i
        rw [hg_i, hτ_i]
      have hz_k : (e_dis ω).1.2 k = ω.1.2 k := rfl
      rw [hsum_eq, hz_k]
  have hpt (ω : ((Fin M → Fin L → ℝ) × (Fin M → ℝ)) × (Fin L → ℝ)) :
      ∫ σ : R → (Fin L → ℤˣ) × (Fin M → ℝ), Θ (fun l i => (σ l).1 (pm i))
        ∂(Measure.pi fun _ : R => μ_base.tilted (E ω)) =
      ∫ σ : R → (Fin L → ℤˣ) × (Fin M → ℝ), Θ (fun l => (σ l).1)
        ∂(Measure.pi fun _ : R => μ_base.tilted (E (e_dis ω))) := by
    rw [haux ω (fun τ => Θ (fun l i => τ l (pm i))), haux (e_dis ω) Θ,
      integral_pi_count_tilted_equiv e_spin (E_eff ω) (fun τ => Θ (fun l i => τ l (pm i)))]
    have h_obs (τ : R → Fin L → ℤˣ) : (fun l i => (e_spin (τ l)) (pm i)) = τ :=
      funext fun l => he_spin (τ l)
    have h_en : (fun b => E_eff ω (e_spin b)) = E_eff (e_dis ω) := funext (hE_eff_eq ω)
    simp_rw [h_obs, h_en]
  simp_rw [hpt]
  exact hmp_dis.integral_comp'
    (fun ω => ∫ σ : R → (Fin L → ℤˣ) × (Fin M → ℝ), Θ (fun l => (σ l).1)
      ∂(Measure.pi fun _ : R => μ_base.tilted (E ω)))

/-- **Site-swap invariance for a two-replica spin observable under the `s`-interpolating Gibbs
measure.** If `Θ (Fin.last N)` conjugated on both replicas by `Equiv.swap i (Fin.last N)` equals
`Θ i`, then `ν_s(Θ i) = ν_s(Θ (Fin.last N))`. -/
theorem integral_interpolating_two_replica_site_swap {N M : ℕ}
    {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, u x ≤ B)
    (s q r : ℝ) (Θ : Fin (N + 1) → (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ)
    (i : Fin (N + 1))
    (hΘ : ∀ x y : Fin (N + 1) → ℤˣ,
      Θ (Fin.last N) (fun j => x (Equiv.swap i (Fin.last N) j))
        (fun j => y (Equiv.swap i (Fin.last N) j)) = Θ i x y) :
    ∫ ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ),
      ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        Θ i (σ 0).1 (σ 1).1
        ∂(Measure.pi fun _ : Fin 2 =>
          ((Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
            (Measure.pi fun _ : Fin M => gaussianReal 0 1)).tilted
            fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
              (∑ k : Fin M, u (Real.sqrt s *
                  ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ j, ω.1.1 k j * ((x.1 j : ℤ) : ℝ)) +
                Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))) +
              ∑ j : Fin (N + 1), ((x.1 j : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 j * Real.sqrt r)
        ∂(((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod
          (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)) =
      ∫ ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ),
        ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          Θ (Fin.last N) (σ 0).1 (σ 1).1
          ∂(Measure.pi fun _ : Fin 2 =>
            ((Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
              (Measure.pi fun _ : Fin M => gaussianReal 0 1)).tilted
              fun x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ) =>
                (∑ k : Fin M, u (Real.sqrt s *
                    ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ j, ω.1.1 k j * ((x.1 j : ℤ) : ℝ)) +
                  Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))) +
                ∑ j : Fin (N + 1), ((x.1 j : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 j * Real.sqrt r)
          ∂(((Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1).prod
              (Measure.pi fun _ : Fin M => gaussianReal 0 1)).prod
            (Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1)) := by
  have h1 := interpolating_replica_site_perm (L := N + 1) (M := M) (R := Fin 2) hu hB s q r
    (Equiv.swap i (Fin.last N)) (fun σ => Θ (Fin.last N) (σ 0) (σ 1))
  dsimp only at h1
  rw [← h1]
  exact integral_congr_ae (ae_of_all _ fun _ =>
    integral_congr_ae (ae_of_all _ fun σ => (hΘ (σ 0).1 (σ 1).1).symm))

/-- **Eq. (2.70) for the `s`-interpolating Gibbs measure:**
`ν_s((R_{1,2} - q) φ(R_{1,2} - q)) = ν_s((ε₁ ε₂ - q) φ(R_{1,2} - q))` where `ε_l = σ_l(Fin.last N)`
is the last spin. -/
theorem integral_interpolating_overlap_mul_eq_last_site {N M : ℕ}
    {u : ℝ → ℝ} (hu : Measurable u) {B : ℝ} (hB : ∀ x, u x ≤ B)
    (s q r : ℝ) (φ : ℝ → ℝ) :
    let P_g := Measure.pi fun _ : Fin M => Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P_z := Measure.pi fun _ : Fin M => gaussianReal 0 1
    let P_z' := Measure.pi fun _ : Fin (N + 1) => gaussianReal 0 1
    let P := (P_g.prod P_z).prod P_z'
    let μ_base := (Measure.count : Measure (Fin (N + 1) → ℤˣ)).prod
      (Measure.pi fun _ : Fin M => gaussianReal 0 1)
    let E (ω : ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ))
        (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) : ℝ :=
      (∑ k : Fin M, u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k))) +
      ∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r
    let Rf (x y : Fin (N + 1) → ℤˣ) : ℝ :=
      ((N : ℝ) + 1)⁻¹ * ∑ i, ((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)
    ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        (Rf (σ 0).1 (σ 1).1 - q) * φ (Rf (σ 0).1 (σ 1).1 - q)
        ∂(Measure.pi fun _ : Fin 2 => μ_base.tilted (E ω)) ∂P =
      ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
        ((((((σ 0).1 (Fin.last N) : ℤ) : ℝ) * (((σ 1).1 (Fin.last N) : ℤ) : ℝ) - q) *
          φ (Rf (σ 0).1 (σ 1).1 - q)))
        ∂(Measure.pi fun _ : Fin 2 => μ_base.tilted (E ω)) ∂P := by
  intro P_g P_z P_z' P μ_base E Rf
  let Θ (i : Fin (N + 1)) (x y : Fin (N + 1) → ℤˣ) : ℝ :=
    (((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ) - q) * φ (Rf x y - q)
  let ν (Φ : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ) : ℝ :=
    ∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), Φ (σ 0).1 (σ 1).1
      ∂(Measure.pi fun _ : Fin 2 => μ_base.tilted (E ω)) ∂P
  have hRperm (pm : Equiv.Perm (Fin (N + 1))) (x y : Fin (N + 1) → ℤˣ) :
      Rf (fun i => x (pm i)) (fun i => y (pm i)) = Rf x y := by
    dsimp only [Rf]
    rw [Equiv.sum_comp pm fun i => ((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)]
  have hsite (i : Fin (N + 1)) : ν (Θ i) = ν (Θ (Fin.last N)) :=
    integral_interpolating_two_replica_site_swap hu hB s q r Θ i fun x y => by
      simp only [Θ, hRperm, Equiv.swap_apply_right]
  let Ω := ((Fin M → Fin (N + 1) → ℝ) × (Fin M → ℝ)) × (Fin (N + 1) → ℝ)
  let E_eff (ω : Ω) (τ : Fin (N + 1) → ℤˣ) : ℝ :=
    (∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r) +
    ∑ k : Fin M, Real.log (∫ ξ, Real.exp (u (Real.sqrt s *
      ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
      Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ))) ∂gaussianReal 0 1)
  have haux (ω : Ω) (Φ : (Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) :
      ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ), Φ (fun l => (σ l).1)
        ∂(Measure.pi fun _ : Fin 2 => μ_base.tilted (E ω)) =
      ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, Φ τ
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_eff ω)) := by
    have hE_swap (x : (Fin (N + 1) → ℤˣ) × (Fin M → ℝ)) :
        E ω x = (∑ i : Fin (N + 1), ((x.1 i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r) +
          ∑ k : Fin M, u (Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
            ∑ i, ω.1.1 k i * ((x.1 i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * x.2 k)) := add_comm _ _
    simp_rw [show E ω = _ from funext hE_swap]
    exact integral_pi_tilted_count_prod_sum (fun _ : Fin M => gaussianReal 0 1)
      (fun τ : Fin (N + 1) → ℤˣ =>
        ∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r)
      (fun τ k ξ => u (Real.sqrt s * ((Real.sqrt (N + 1 : ℕ))⁻¹ *
        ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
        Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ)))
      (fun τ k => hu.comp (by fun_prop)) (fun _ => B) (fun _ _ _ => hB _) Φ
  have hE_eff_m (τ : Fin (N + 1) → ℤˣ) : Measurable fun ω : Ω => E_eff ω τ := by
    dsimp only [E_eff]
    have hm1 : Measurable fun ω : Ω =>
        ∑ i : Fin (N + 1), ((τ i : ℤ) : ℝ) * Real.sqrt (1 - s) * ω.2 i * Real.sqrt r :=
      Finset.measurable_sum _ fun i _ =>
        (measurable_const.mul ((measurable_pi_apply i).comp measurable_snd)).mul measurable_const
    have hm2 : Measurable fun ω : Ω =>
        ∑ k : Fin M, Real.log (∫ ξ, Real.exp (u (Real.sqrt s *
          ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, ω.1.1 k i * ((τ i : ℤ) : ℝ)) +
          Real.sqrt (1 - s) * (Real.sqrt q * ω.1.2 k + Real.sqrt (1 - q) * ξ)))
          ∂gaussianReal 0 1) := by
      refine Finset.measurable_sum _ fun k _ => Real.measurable_log.comp ?_
      have hj : Measurable fun p : Ω × ℝ =>
          Real.exp (u (Real.sqrt s *
            ((Real.sqrt (N + 1 : ℕ))⁻¹ * ∑ i, p.1.1.1 k i * ((τ i : ℤ) : ℝ)) +
            Real.sqrt (1 - s) * (Real.sqrt q * p.1.1.2 k + Real.sqrt (1 - q) * p.2))) := by
        have hs1 : Measurable fun p : Ω × ℝ =>
            ∑ i : Fin (N + 1), p.1.1.1 k i * ((τ i : ℤ) : ℝ) := by
          refine Finset.measurable_sum _ fun i _ => ?_
          have mg : Measurable fun p : Ω × ℝ => p.1.1.1 k i :=
            (measurable_pi_apply i).comp ((measurable_pi_apply k).comp
              (measurable_fst.comp (measurable_fst.comp measurable_fst)))
          exact mg.mul_const _
        have hz1 : Measurable fun p : Ω × ℝ => p.1.1.2 k :=
          (measurable_pi_apply k).comp (measurable_snd.comp (measurable_fst.comp measurable_fst))
        exact Real.measurable_exp.comp (hu.comp
          (((hs1.const_mul _).const_mul _).add
            (((hz1.const_mul _).add (measurable_snd.const_mul _)).const_mul _)))
      exact (hj.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).measurable
    exact hm1.add hm2
  have hP_prob : IsProbabilityMeasure P := by dsimp only [P, P_g, P_z, P_z']; infer_instance
  have hint (i : Fin (N + 1)) :
      Integrable (fun ω : Ω => ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, Θ i (τ 0) (τ 1)
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_eff ω))) P := by
    obtain ⟨C, hC⟩ := exists_abs_le_of_finite
      (fun τ : Fin 2 → Fin (N + 1) → ℤˣ => Θ i (τ 0) (τ 1))
    exact integrable_integral_pi_count_tilted_of_bound E_eff hE_eff_m
      (fun _ τ => Θ i (τ 0) (τ 1)) (fun _ => measurable_const) C (fun _ τ => hC τ)
  have hsum : ν (fun x y => ∑ i, Θ i x y) = ∑ i, ν (Θ i) := by
    dsimp only [ν]
    have hlhs : (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          ∑ i, Θ i (σ 0).1 (σ 1).1 ∂(Measure.pi fun _ : Fin 2 => μ_base.tilted (E ω)) ∂P) =
        ∫ ω, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, ∑ i, Θ i (τ 0) (τ 1)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_eff ω)) ∂P :=
      integral_congr_ae (ae_of_all _ fun ω => haux ω (fun τ => ∑ i, Θ i (τ 0) (τ 1)))
    have hrhs (i : Fin (N + 1)) : (∫ ω, ∫ σ : Fin 2 → (Fin (N + 1) → ℤˣ) × (Fin M → ℝ),
          Θ i (σ 0).1 (σ 1).1 ∂(Measure.pi fun _ : Fin 2 => μ_base.tilted (E ω)) ∂P) =
        ∫ ω, ∫ τ : Fin 2 → Fin (N + 1) → ℤˣ, Θ i (τ 0) (τ 1)
          ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_eff ω)) ∂P :=
      integral_congr_ae (ae_of_all _ fun ω => haux ω (fun τ => Θ i (τ 0) (τ 1)))
    rw [hlhs]
    simp_rw [hrhs]
    exact integral_integral_finset_sum P
      (fun ω => Measure.pi fun _ : Fin 2 => Measure.count.tilted (E_eff ω))
      Finset.univ (fun i (τ : Fin 2 → Fin (N + 1) → ℤˣ) => Θ i (τ 0) (τ 1))
      (fun _ _ _ => Integrable.of_finite) (fun i _ => hint i)
  have hpt (x y : Fin (N + 1) → ℤˣ) :
      ∑ i, Θ i x y = ((N : ℝ) + 1) * ((Rf x y - q) * φ (Rf x y - q)) := by
    have hL : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    dsimp only [Θ, Rf]
    rw [← Finset.sum_mul]
    have hsum_i : (∑ i : Fin (N + 1), (((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ) - q)) =
        (∑ i : Fin (N + 1), ((x i : ℤ) : ℝ) * ((y i : ℤ) : ℝ)) - ((N : ℝ) + 1) * q := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast; ring
    rw [hsum_i]
    field_simp
  have hν_lhs : ν (fun x y => ∑ i, Θ i x y) =
      ((N : ℝ) + 1) * ν (fun x y => (Rf x y - q) * φ (Rf x y - q)) := by
    dsimp only [ν]
    simp_rw [hpt, integral_const_mul]
  have hν_rhs : ∑ i : Fin (N + 1), ν (Θ i) = ((N : ℝ) + 1) * ν (Θ (Fin.last N)) := by
    simp_rw [hsite, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [hν_lhs, hν_rhs] at hsum
  exact mul_left_cancel₀ (by positivity : ((N : ℝ) + 1) ≠ 0) hsum

end SpinGlasses
