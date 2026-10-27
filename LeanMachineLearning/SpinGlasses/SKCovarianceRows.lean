/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.SKSecondMoment
public import LeanMachineLearning.SpinGlasses.SKCavityCovariance
public import LeanMachineLearning.SpinGlasses.GibbsOverlapCovariances

/-!
# One row of the cavity covariance system (Talagrand, Eqs. (1.231)-(1.233))

Site symmetry and the exact split `R_{ab} = R⁻_{ab} + ε_aε_b/M` for products of overlaps of
the `(N+1)`-spin system.

## References

* M. Talagrand, *Spin Glasses: A Challenge for Mathematicians*, Vol. I, Section 1.8.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Real Matrix

namespace SpinGlasses

section SiteSymmetry

variable (N n : ℕ) (β h q : ℝ)
  (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
  (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
    ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ))
    ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))

include hν in
/-- **Site symmetry for a product of an overlap with a site-symmetric observable** (Eq. (1.240)
in its general form): if `Ψ` is invariant under permutations of the sites, then
`ν((R_{xy} - q) Ψ) = ν((ε_xε_y - q) Ψ)` where `ε` is the last spin. -/
theorem sk_overlap_mul_eq_last_site_of_perm (x y : Fin n)
    (Ψ : (Fin n → Fin (N + 1) → ℤˣ) → ℝ)
    (hΨ : ∀ (pm : Equiv.Perm (Fin (N + 1))) σ, Ψ (fun r i => σ r (pm i)) = Ψ σ) :
    ν (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ x i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ y i : ℝ)) - q) * Ψ σ) =
      ν (fun σ => (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q) * Ψ σ) := by
  let Θ : Fin (N + 1) → (Fin n → Fin (N + 1) → ℤˣ) → ℝ := fun i σ =>
    (((σ x i : ℤˣ) : ℝ) * ((σ y i : ℤˣ) : ℝ) - q) * Ψ σ
  have hsite : ∀ i, ν (Θ i) = ν (Θ (Fin.last N)) := fun i => by
    have h1 := sk_replica_site_perm (R := Fin n) N β h (Equiv.swap i (Fin.last N))
      (fun σ => Θ (Fin.last N) σ)
    have h2 : ∀ σ : Fin n → Fin (N + 1) → ℤˣ,
        Θ (Fin.last N) (fun r j => σ r (Equiv.swap i (Fin.last N) j)) = Θ i σ := fun σ => by
      simp only [Θ, hΨ, Equiv.swap_apply_right]
    simp only [h2] at h1
    rw [hν, hν]
    exact h1
  have hpt : ∀ σ, ∑ i, Θ i σ = ((N + 1 : ℕ) : ℝ) *
      (((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ x i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ y i : ℝ)) - q) * Ψ σ) := fun σ => by
    have hM : ((N + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero N)
    simp only [Θ, ← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, dotProduct]
    push_cast
    field_simp
  have hlin : ν (fun σ => ∑ i ∈ Finset.univ, (1 : ℝ) * Θ i σ) =
      ∑ i ∈ Finset.univ, 1 * ν (Θ i) := sk_replica_avg_finset_sum N n β h ν hν _ _ _
  have hlin2 : ν (fun σ => ∑ i, Θ i σ) = ∑ i, ν (Θ i) := by
    simpa using hlin
  have hlin3 : ν (fun σ => ∑ i, Θ i σ) = ((N + 1 : ℕ) : ℝ) *
      ν (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ x i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ y i : ℝ)) - q) * Ψ σ) := by
    simp only [hpt]
    exact sk_replica_avg_smul N n β h ν hν _ _
  have hfin : ∑ i, ν (Θ i) = ((N + 1 : ℕ) : ℝ) * ν (Θ (Fin.last N)) := by
    simp only [hsite, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN : ((N + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero N)
  exact mul_left_cancel₀ hN (hlin3.symm.trans (hlin2.trans hfin))

end SiteSymmetry

/-- **The decoupled average of a centered pair monomial vanishes:** for `x ≠ y`,
`ν₀(F (ε_xε_y - q)) = 0` when `𝔼 tanh² Y = q` (the first term of Eq. (1.216)). -/
theorem sk_cavity_decoupled_pair_zero (N : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) = q)
    {R : Type*} [Fintype R] {x y : R} (hxy : x ≠ y)
    (F : (R → Fin N → ℤˣ) → ℝ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) →
        (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ σ : R → Fin (N + 1) → ℤˣ,
          F (fun r i => σ r i.castSucc) *
            (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q)
          ∂(Measure.pi fun _ : R => Measure.count.tilted (E (π / 2) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) = 0 := by
  classical
  intro B E
  have hEm (a : Fin (N + 1) → ℤˣ) :
      Measurable (fun x : (FinPairs N → ℝ) × ((Fin N → ℝ) × ℝ) => E (π / 2) x.1 x.2 a) := by
    dsimp [E, B]
    fun_prop
  let Gj : Bool → (R → Fin (N + 1) → ℤˣ) → ℝ := fun u σ =>
    if u then F (fun r i => σ r i.castSucc) *
        (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ))
    else F (fun r i => σ r i.castSucc)
  let cw : Bool → ℝ := fun u => if u then 1 else -q
  have hpt : ∀ σ : R → Fin (N + 1) → ℤˣ,
      F (fun r i => σ r i.castSucc) *
        (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q) =
      ∑ u ∈ Finset.univ, cw u * Gj u σ := fun σ => by
    simp only [Fintype.sum_bool, cw, Gj, ite_true, ite_false, Bool.false_eq_true]
    ring
  simp_rw [hpt]
  rw [integral_nested_gibbs_finset_sum (Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)) (E (π / 2)) hEm
    Finset.univ cw Gj]
  have h1 := sk_cavity_decoupled_endpoint_replicas N β q h ({x, y} : Finset R) F
  have h0 := sk_cavity_decoupled_endpoint_replicas N β q h (∅ : Finset R) F
  rw [Finset.card_pair hxy, hfix] at h1
  simp only [Finset.prod_pair hxy] at h1
  simp only [Finset.prod_empty, mul_one, Finset.card_empty, pow_zero, integral_const,
    probReal_univ, one_smul, one_mul] at h0
  simp only [Fintype.sum_bool, cw, Gj, ite_true, ite_false, Bool.false_eq_true]
  rw [h1, h0]
  ring

/-- **The Taylor step for a pair covariance** (Eq. (1.216) with Lemma 1.8.2): for `x ≠ y`, an
observable `F` of the old spins and `f = F (ε_xε_y - q)`,
`ν(f)` differs from `∑_j w_j b(c_j) 𝔼⟨F (R⁻_j - q)⟩_{old}` by at most
`4 n² (n+2)² β⁴ exp (4 (n+4)² β²) ν(f²)^{1/2} ν((R_{1,2} - q)⁴)^{1/2}`. -/
theorem sk_pair_taylor (N n : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (qhat : ℝ)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    {x y : Fin n} (hxy : x ≠ y) (F : (Fin n → Fin N → ℤˣ) → ℝ)
    (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) (Dfour : ℝ)
    (hDfour : Dfour = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 4
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) :
    |ν (fun σ => F (fun r i => σ r i.castSucc) *
        (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q)) -
      ∑ j : SKCavityReplicaPair n,
        skCavityReplicaPairWeight n j *
          (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences x y j) *
            ∫ g', ∫ ρ : Option (Option (Fin n)) → Fin N → ℤˣ,
              F (fun r => ρ (some (some r))) *
                ((N + 1 : ℝ)⁻¹ *
                  ((fun i : Fin N => (ρ (skCavityReplicaPairMap j).1 i : ℝ)) ⬝ᵥ
                    fun i : Fin N => (ρ (skCavityReplicaPairMap j).2 i : ℝ)) - q)
              ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
                (fun r : Fin N → ℤˣ =>
                  (Real.sqrt (N + 1))⁻¹ * β *
                    (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
                  h * ∑ i : Fin N, (r i : ℝ)))
              ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))| ≤
    4 * (n : ℝ) ^ 2 * ((n : ℝ) + 2) ^ 2 * β ^ 4 * Real.exp (4 * ((n : ℝ) + 4) ^ 2 * β ^ 2) *
      (Real.sqrt (ν (fun σ => (F (fun r i => σ r i.castSucc) *
        (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q)) ^ 2)) *
        Real.sqrt Dfour) := by
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := fixedPoint_mem_Icc hfix
  have hfixz : ∫ z : ℝ, Real.tanh (β * z * Real.sqrt q + h) ^ 2 ∂(gaussianReal 0 1) = q := by
    rw [integral_tanh_pow_mul_z_sqrt_eq, hfix]
  have T := sk_cavity_nu_sub_nu_zero_sub_deriv_le_two N n β q h hq
    (fun σ => F (fun r i => σ r i.castSucc) *
      (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q))
  have L := sk_cavity_deriv_zero_pair N n β q h hfix qhat hqhat hxy F
  have Z := sk_cavity_decoupled_pair_zero N β q h hfixz hxy F
  simp only [] at T L Z
  rw [Z, L] at T
  rw [← hν, ← hDfour, ← hν] at T
  simpa using T

section Structure

variable (N n : ℕ) (β h q : ℝ)
  (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
  (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
    ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
      (Real.sqrt (N + 1))⁻¹ * β *
        (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
      h * ∑ i : Fin (N + 1), (a i : ℝ))
    ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))

include hν in
/-- **Structure of one row of the covariance system** (Talagrand's Eq. (1.217)-(1.218) in the
cavity notation): for replicas `x ≠ y` and `a ≠ b` of the `(N+1)`-spin system, with
`M = N + 1`, `R⁻_{ab} = M⁻¹ ∑_{i<N} σ^a_iσ^b_i` and `ε = ` the last spin,
`ν((R_{xy} - q)(R_{ab} - q)) = ν((R⁻_{ab} - q)(ε_xε_y - q)) + M⁻¹ ν((ε_xε_y - q) ε_aε_b)`. -/
theorem sk_row_structure (x y a b : Fin n) :
    ν (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ x i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ y i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ a i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ b i : ℝ)) - q)) =
      ν (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ a i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ b i.castSucc : ℝ)) - q) *
        (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q)) +
      (N + 1 : ℝ)⁻¹ * ν (fun σ =>
        (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q) *
          (((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ))) := by
  have hperm : ∀ (pm : Equiv.Perm (Fin (N + 1))) (σ : Fin n → Fin (N + 1) → ℤˣ),
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (fun r i => σ r (pm i) : Fin n → Fin (N + 1) → ℤˣ)
        a i |> fun v => (v : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => ((σ b (pm i) : ℤˣ) : ℝ)) - q) =
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ a i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ b i : ℝ)) - q) := fun pm σ => by
    simp only [dotProduct]
    rw [Equiv.sum_comp pm fun i => ((σ a i : ℤˣ) : ℝ) * ((σ b i : ℤˣ) : ℝ)]
  rw [sk_overlap_mul_eq_last_site_of_perm N n β h q ν hν x y
    (fun σ => (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ a i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ b i : ℝ)) - q) (fun pm σ => hperm pm σ)]
  have hsplit : ∀ σ : Fin n → Fin (N + 1) → ℤˣ,
      (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ a i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ b i : ℝ)) - q) =
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ a i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ b i.castSucc : ℝ)) - q) *
        (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q) +
      (N + 1 : ℝ)⁻¹ * ((((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q) *
          (((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ))) := fun σ => by
    simp only [dotProduct, Fin.sum_univ_castSucc]
    ring
  obtain ⟨hadd, hsmul, -, -⟩ := sk_replica_avg_calculus N n β h ν hν
  rw [show (fun σ : Fin n → Fin (N + 1) → ℤˣ => _) = _ from funext hsplit, hadd, hsmul]

end Structure

/-- **Passing from the `(N+1)`-spin average to the old-spin average** (Eq. (1.215) with
`τ₁ = τ₂ = 2`): for an observable `G` of the first `N` spins of `m` replicas,
`|ν(G) - 𝔼⟨G⟩_{old}| ≤ 2 m² β² exp (4 (m+2)² β²) ν(G²)^{1/2} ν((R_{1,2} - q)²)^{1/2}`. -/
theorem sk_old_spin_compare (N m : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (G : (Fin m → Fin N → ℤˣ) → ℝ)
    (ν : ((Fin m → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin m → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) (Dtwo : ℝ)
    (hDtwo : Dtwo = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) :
    |ν (fun σ => G (fun r i => σ r i.castSucc)) -
      ∫ g', ∫ ρ : Fin m → Fin N → ℤˣ, G ρ
        ∂(Measure.pi fun _ : Fin m => Measure.count.tilted
          (fun r : Fin N → ℤˣ =>
            (Real.sqrt (N + 1))⁻¹ * β *
              (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
            h * ∑ i : Fin N, (r i : ℝ)))
        ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)| ≤
    2 * (m : ℝ) ^ 2 * β ^ 2 * Real.exp (4 * ((m : ℝ) + 2) ^ 2 * β ^ 2) *
      (Real.sqrt (ν (fun σ => G (fun r i => σ r i.castSucc) ^ 2)) * Real.sqrt Dtwo) := by
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := fixedPoint_mem_Icc hfix
  have T := sk_cavity_nu_sub_nu_zero_le_two N m β q h hq (fun σ => G (fun r i => σ r i.castSucc))
  have h0 := sk_cavity_decoupled_endpoint_replicas N β q h (∅ : Finset (Fin m)) G
  simp only [Finset.prod_empty, mul_one, Finset.card_empty, pow_zero, integral_const,
    probReal_univ, one_smul, one_mul] at h0
  simp only [] at T
  rw [h0] at T
  rw [← hν, ← hDtwo, ← hν] at T
  exact T

/-- **The last-spin term of a row:** for `x ≠ y`, `a ≠ b`,
`|ν((ε_xε_y - q) ε_aε_b) - b(c)| ≤ 4 n² β² exp (4 (n+2)² β²) ν(|R_{1,2} - q|)`, where `c` is the
number of coincidences of `{x, y}` and `{a, b}` and `b(c) = 𝔼 tanh^{4-2c} - q²` (the unscaled
coefficient of Lemma 1.8.2). -/
theorem sk_row_last_site (N n : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (qhat : ℝ)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    {x y a b : Fin n} (hxy : x ≠ y) (hab : a ≠ b)
    (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) (Dabs : ℝ)
    (hDabs : Dabs = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q|
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) :
    |ν (fun σ => (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q) *
        (((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ))) -
      skCavityBUnscaled q qhat (skCavityCoincidences x y a b)| ≤
    4 * (n : ℝ) ^ 2 * β ^ 2 * Real.exp (4 * ((n : ℝ) + 2) ^ 2 * β ^ 2) * Dabs := by
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := fixedPoint_mem_Icc hfix
  have hbd : ∀ σ : Fin n → Fin (N + 1) → ℤˣ,
      |(((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q) *
        (((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ))| ≤ 2 := fun σ => by
    have hx := abs_units_cast_le_one (σ x (Fin.last N))
    have hy := abs_units_cast_le_one (σ y (Fin.last N))
    have ha := abs_units_cast_le_one (σ a (Fin.last N))
    have hb := abs_units_cast_le_one (σ b (Fin.last N))
    have hq0 := hq.1
    have hq1 := hq.2
    rw [abs_mul]
    have h1 : |((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q| ≤ 2 := by
      have : |((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ)| ≤ 1 := by
        rw [abs_mul]; nlinarith [abs_nonneg ((σ x (Fin.last N) : ℤˣ) : ℝ)]
      calc _ ≤ |((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ)| + |q| :=
            abs_sub _ _
        _ ≤ 2 := by rw [abs_of_nonneg hq0]; linarith
    have h2 : |((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ)| ≤ 1 := by
      rw [abs_mul]; nlinarith [abs_nonneg ((σ a (Fin.last N) : ℤˣ) : ℝ)]
    nlinarith [abs_nonneg (((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ))]
  have T := sk_cavity_nu_sub_nu_zero_le_of_abs_le N n β q h hq
    (fun σ => (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q) *
        (((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ))) (M := 2) hbd
  have P := sk_cavity_decoupled_endpoint_pair_cov N β q h hfix qhat hqhat hxy hab
    (fun _ => (1 : ℝ))
  simp only [] at T P
  simp only [one_mul, integral_const, probReal_univ, one_smul, mul_one] at P
  rw [P] at T
  rw [← hν, ← hDabs] at T
  refine T.trans (le_of_eq ?_)
  ring

section Moments

variable (N : ℕ) (β h q : ℝ)

/-- **Marginal of an `m`-replica SK average along an injection of the replicas.** -/
theorem sk_nu_marginal_inj {k m : ℕ}
    (νk : ((Fin k → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hνk : ∀ Φ, νk Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin k → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin k => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (νm : ((Fin m → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hνm : ∀ Φ, νm Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin m → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    {ρ : Fin k → Fin m} (hρ : Function.Injective ρ)
    (Φ : (Fin k → Fin (N + 1) → ℤˣ) → ℝ) :
    νm (fun σ => Φ (fun r => σ (ρ r))) = νk Φ := by
  rw [hνm, hνk]
  refine integral_congr_ae (ae_of_all _ fun g => ?_)
  exact integral_pi_count_tilted_comp_injective hρ _ Φ

/-- **Two-replica marginal of an `m`-replica SK average:** a function of two distinct replicas
`x ≠ y` has the same average as under two replicas. -/
theorem sk_nu_pair_marginal (m : ℕ)
    (ν : ((Fin m → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin m → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₂ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    {x y : Fin m} (hxy : x ≠ y) (H : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ) :
    ν (fun σ => H (σ x) (σ y)) = ν₂ (fun σ => H (σ 0) (σ 1)) := by
  have hρ : Function.Injective (![x, y] : Fin 2 → Fin m) := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all [Ne.symm hxy]
  simpa using sk_nu_marginal_inj N β h ν₂ hν₂ ν hν hρ
    (fun σ : Fin 2 → Fin (N + 1) → ℤˣ => H (σ 0) (σ 1))

/-- `|ν(Z)| ≤ ν(|Z|)` for an `m`-replica SK average. -/
theorem sk_nu_abs_le (m : ℕ)
    (ν : ((Fin m → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin m → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (Z : (Fin m → Fin (N + 1) → ℤˣ) → ℝ) : |ν Z| ≤ ν (fun σ => |Z σ|) := by
  obtain ⟨-, hsmul, hmono, -⟩ := sk_replica_avg_calculus N m β h ν hν
  rw [abs_le]
  refine ⟨?_, hmono Z _ fun σ => le_abs_self _ |> fun h' => by simpa using h'⟩
  have h1 := hmono (fun σ => (-1 : ℝ) * Z σ) (fun σ => |Z σ|) fun σ => by
    rw [neg_one_mul]; exact neg_le_abs _
  rw [hsmul] at h1
  linarith

/-- Perturbing both factors of a product by at most `c` costs `c |X| + c |Y| + c²`. -/
theorem abs_mul_sub_sub_le (X Y d₁ d₂ c : ℝ) (h₁ : |d₁| ≤ c) (h₂ : |d₂| ≤ c) :
    |(X - d₁) * (Y - d₂) - X * Y| ≤ c * |X| + c * |Y| + c * c := by
  have e : (X - d₁) * (Y - d₂) - X * Y = -(d₁ * Y) - d₂ * X + d₁ * d₂ := by ring
  have hc : 0 ≤ c := (abs_nonneg _).trans h₁
  rw [e]
  calc |-(d₁ * Y) - d₂ * X + d₁ * d₂| ≤ |-(d₁ * Y) - d₂ * X| + |d₁ * d₂| := abs_add_le _ _
    _ ≤ (|d₁ * Y| + |d₂ * X|) + |d₁ * d₂| := by
        gcongr
        exact (abs_sub _ _).trans (by rw [abs_neg])
    _ ≤ c * |Y| + c * |X| + c * c := by
        rw [abs_mul, abs_mul, abs_mul]
        gcongr
    _ = _ := by ring

/-- `|M⁻¹ (u v)| ≤ M⁻¹` for two signs (in fact an equality). -/
theorem abs_inv_mul_sign_le (M : ℝ) (hM : 0 < M) (u v : ℤˣ) :
    |M⁻¹ * (((u : ℤ) : ℝ) * ((v : ℤ) : ℝ))| ≤ M⁻¹ := by
  simp only [abs_mul, abs_units_cast_eq_one, mul_one, abs_of_pos (inv_pos.2 hM), le_refl]

/-- **From `R⁻` to `R` in a product of two overlaps** (Eq. (1.219)-(1.223)): since
`R_{pq} = R⁻_{pq} + ε_pε_q/M`, replacing `R⁻` by `R` in `ν((R_{pq} - q)(R_{rs} - q))` costs at most
`2 ν(|R_{1,2} - q|)/M + 1/M²`. -/
theorem sk_row_conv (m : ℕ)
    (ν : ((Fin m → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin m → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₂ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    {p₁ p₂ r₁ r₂ : Fin m} (hp : p₁ ≠ p₂) (hr : r₁ ≠ r₂) :
    |ν (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ p₁ i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (σ p₂ i.castSucc : ℝ)) - q) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ r₁ i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (σ r₂ i.castSucc : ℝ)) - q)) -
      ν (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ p₁ i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ p₂ i : ℝ)) - q) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ r₁ i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ r₂ i : ℝ)) - q))| ≤
    2 * ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q|) / (N + 1) + 1 / (N + 1) ^ 2 := by
  obtain ⟨hadd, hsmul, hmono, hconst⟩ := sk_replica_avg_calculus N m β h ν hν
  have hM0 : (0 : ℝ) < N + 1 := by positivity
  set c : ℝ := (N + 1 : ℝ)⁻¹ with hc
  let X : (Fin m → Fin (N + 1) → ℤˣ) → ℝ := fun σ => (N + 1 : ℝ)⁻¹ *
    ((fun i : Fin (N + 1) => (σ p₁ i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ p₂ i : ℝ)) - q
  let Y : (Fin m → Fin (N + 1) → ℤˣ) → ℝ := fun σ => (N + 1 : ℝ)⁻¹ *
    ((fun i : Fin (N + 1) => (σ r₁ i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ r₂ i : ℝ)) - q
  have hpt : ∀ σ : Fin m → Fin (N + 1) → ℤˣ,
      |((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ p₁ i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (σ p₂ i.castSucc : ℝ)) - q) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ r₁ i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (σ r₂ i.castSucc : ℝ)) - q) +
        (-1 : ℝ) * (X σ * Y σ)| ≤ c * |X σ| + c * |Y σ| + c * c := fun σ => by
    have e1 : ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ p₁ i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (σ p₂ i.castSucc : ℝ)) - q) =
        X σ - (N + 1 : ℝ)⁻¹ *
          (((σ p₁ (Fin.last N) : ℤˣ) : ℝ) * ((σ p₂ (Fin.last N) : ℤˣ) : ℝ)) := by
      simp only [X, dotProduct, Fin.sum_univ_castSucc]; ring
    have e2 : ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ r₁ i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (σ r₂ i.castSucc : ℝ)) - q) =
        Y σ - (N + 1 : ℝ)⁻¹ *
          (((σ r₁ (Fin.last N) : ℤˣ) : ℝ) * ((σ r₂ (Fin.last N) : ℤˣ) : ℝ)) := by
      simp only [Y, dotProduct, Fin.sum_univ_castSucc]; ring
    rw [e1, e2, neg_one_mul, ← sub_eq_add_neg]
    exact abs_mul_sub_sub_le _ _ _ _ c (abs_inv_mul_sign_le _ hM0 _ _)
      (abs_inv_mul_sign_le _ hM0 _ _)
  let A : (Fin m → Fin (N + 1) → ℤˣ) → ℝ := fun σ =>
    ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ p₁ i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (σ p₂ i.castSucc : ℝ)) - q) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ r₁ i.castSucc : ℝ)) ⬝ᵥ
            fun i : Fin N => (σ r₂ i.castSucc : ℝ)) - q)
  have hdiff : ν A - ν (fun σ => X σ * Y σ) = ν (fun σ => A σ + (-1 : ℝ) * (X σ * Y σ)) := by
    rw [hadd, hsmul]; ring
  have hX : ν (fun σ => |X σ|) = ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ *
      ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q|) :=
    sk_nu_pair_marginal N β h m ν hν ν₂ hν₂ hp
      (fun a b => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (a i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (b i : ℝ)) - q|)
  have hY : ν (fun σ => |Y σ|) = ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ *
      ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q|) :=
    sk_nu_pair_marginal N β h m ν hν ν₂ hν₂ hr
      (fun a b => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (a i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (b i : ℝ)) - q|)
  have hlin : ν (fun σ => c * |X σ| + c * |Y σ| + c * c) =
      c * ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q|) +
      c * ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q|) + c * c := by
    rw [hadd (fun σ => c * |X σ| + c * |Y σ|) (fun _ => c * c), hadd (fun σ => c * |X σ|)
      (fun σ => c * |Y σ|), hsmul, hsmul, hconst, hX, hY]
  have hle : |ν (fun σ => A σ + (-1 : ℝ) * (X σ * Y σ))| ≤
      c * ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q|) +
      c * ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q|) + c * c := by
    rw [← hlin]
    exact (sk_nu_abs_le N β h m ν hν _).trans (hmono _ _ hpt)
  calc |ν A - ν (fun σ => X σ * Y σ)| = |ν (fun σ => A σ + (-1 : ℝ) * (X σ * Y σ))| := by
        rw [hdiff]
    _ ≤ _ := hle
    _ = _ := by
        rw [hc]
        field_simp
        ring

end Moments

/-- The unscaled coefficients `b(c)` of Lemma 1.8.2 are bounded by `1` when `q, q̂ ∈ [0, 1]`. -/
theorem abs_skCavityBUnscaled_le {q qhat : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hqhat : qhat ∈ Set.Icc (0 : ℝ) 1) (c : ℕ) : |skCavityBUnscaled q qhat c| ≤ 1 := by
  obtain ⟨hq0, hq1⟩ := hq
  obtain ⟨hh0, hh1⟩ := hqhat
  unfold skCavityBUnscaled
  split_ifs
  · rw [abs_le]; constructor <;> nlinarith
  · rw [abs_le]; constructor <;> nlinarith
  · rw [abs_le]; constructor <;> nlinarith

/-- Triangle inequality for the three pieces of a row. -/
theorem abs_row_combine {W κ SV fab SOO kν bu c E₁ E₂ E₃ : ℝ} (hW : W = fab + c * kν)
    (hκ : κ = c * bu) (hc : 0 ≤ c) (h₁ : |fab - SOO| ≤ E₁) (h₂ : |SOO - SV| ≤ E₂)
    (h₃ : |kν - bu| ≤ E₃) : |W - κ - SV| ≤ E₁ + E₂ + c * E₃ := by
  have a1 := abs_le.1 h₁
  have a2 := abs_le.1 h₂
  have a3 := abs_le.1 h₃
  have b1 := mul_le_mul_of_nonneg_left a3.1 hc
  have b2 := mul_le_mul_of_nonneg_left a3.2 hc
  rw [abs_le]
  constructor <;> subst hW hκ <;> nlinarith only [a1.1, a1.2, a2.1, a2.2, b1, b2]

section Row

/-- **One row of the cavity covariance system (explicit error).**  Let `x ≠ y`, `a ≠ b` be
replicas of `n` replicas and `e` a numbering of the `n + 2` replicas of the cavity formula.  Then
`ν((R_{xy} - q)(R_{ab} - q))` differs from
`M⁻¹ b(c) + ∑_j w_j β² b(c_j) ν_{n+2}((R_{ab} - q)(R_{j} - q))`, `M = N + 1`, by at most the sum of
the Taylor error (Eq. (1.216)), the `ν₀ → ν` error (Eq. (1.215)) for the `∑_j`, the cost of
`R⁻ → R`, and the last-site error (Eq. (1.215) again).  The quantities `Vf`, `Gb`, `Dtwo`, `Dfour`,
`Dabs` are bounds for the second moments that enter. -/
theorem sk_row_equation (N n : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (qhat : ℝ)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    (hqhat01 : qhat ∈ Set.Icc (0 : ℝ) 1)
    {x y a b : Fin n} (hxy : x ≠ y) (hab : a ≠ b)
    (e : Option (Option (Fin n)) ≃ Fin (n + 2))
    (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (νm : ((Fin (n + 2) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hνm : ∀ Φ, νm Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin (n + 2) → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin (n + 2) => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₂ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (Vf Gb Dtwo Dfour Dabs : ℝ)
    (hVf : ν (fun σ => (((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ a i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ b i.castSucc : ℝ)) - q) *
        (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q)) ^ 2) ≤ Vf)
    (hGb : ∀ j : SKCavityReplicaPair n, νm (fun σ =>
      (((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (e (some (some a))) i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ (e (some (some b))) i.castSucc : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (e (skCavityReplicaPairMap j).1) i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ (e (skCavityReplicaPairMap j).2) i.castSucc : ℝ)) - q)) ^ 2) ≤ Gb)
    (hDtwo : Dtwo = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (hDfour : Dfour = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 4
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (hDabs : Dabs = ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q|)) :
    |ν (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ x i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ y i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ a i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ b i : ℝ)) - q)) -
      (N + 1 : ℝ)⁻¹ * skCavityBUnscaled q qhat (skCavityCoincidences x y a b) -
      ∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
        (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences x y j) *
          νm (fun τ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (τ (e (some (some a))) i : ℝ)) ⬝ᵥ
              fun i : Fin (N + 1) => (τ (e (some (some b))) i : ℝ)) - q) *
            ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (τ (e (skCavityReplicaPairMap j).1) i : ℝ)) ⬝ᵥ
              fun i : Fin (N + 1) => (τ (e (skCavityReplicaPairMap j).2) i : ℝ)) - q)))| ≤
    4 * (n : ℝ) ^ 2 * ((n : ℝ) + 2) ^ 2 * β ^ 4 * Real.exp (4 * ((n : ℝ) + 4) ^ 2 * β ^ 2) *
        (Real.sqrt Vf * Real.sqrt Dfour) +
      (∑ j : SKCavityReplicaPair n, |skCavityReplicaPairWeight n j|) * β ^ 2 *
        (2 * ((n : ℝ) + 2) ^ 2 * β ^ 2 * Real.exp (4 * (((n + 2 : ℕ) : ℝ) + 2) ^ 2 * β ^ 2) *
            (Real.sqrt Gb * Real.sqrt Dtwo) +
          (2 * Dabs / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) ^ 2)) +
      (N + 1 : ℝ)⁻¹ * (4 * (n : ℝ) ^ 2 * β ^ 2 * Real.exp (4 * ((n : ℝ) + 2) ^ 2 * β ^ 2) * Dabs)
        := by
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := fixedPoint_mem_Icc hfix
  have hM0 : (0 : ℝ) < N + 1 := by positivity
  let Fab : (Fin n → Fin N → ℤˣ) → ℝ := fun ρ => (N + 1 : ℝ)⁻¹ *
    ((fun i : Fin N => (ρ a i : ℝ)) ⬝ᵥ fun i : Fin N => (ρ b i : ℝ)) - q
  have S1 := sk_row_structure N n β h q ν hν x y a b
  have T := sk_pair_taylor N n β q h hfix qhat hqhat hxy Fab ν hν Dfour hDfour
  have hDabs' : Dabs = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
      |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
        fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q|
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1) := by
    rw [hDabs, hν₂]
  have K := sk_row_last_site N n β q h hfix qhat hqhat hxy hab ν hν Dabs hDabs'
  have hso : ∀ r r' : Fin n, r ≠ r' → e (some (some r)) ≠ e (some (some r')) :=
    fun r r' hr he => hr (Option.some.inj (Option.some.inj (e.injective he)))
  have hj : ∀ j : SKCavityReplicaPair n,
      |(∫ g', ∫ ρ : Option (Option (Fin n)) → Fin N → ℤˣ,
              Fab (fun r => ρ (some (some r))) *
                ((N + 1 : ℝ)⁻¹ *
                  ((fun i : Fin N => (ρ (skCavityReplicaPairMap j).1 i : ℝ)) ⬝ᵥ
                    fun i : Fin N => (ρ (skCavityReplicaPairMap j).2 i : ℝ)) - q)
              ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
                (fun r : Fin N → ℤˣ =>
                  (Real.sqrt (N + 1))⁻¹ * β *
                    (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
                  h * ∑ i : Fin N, (r i : ℝ)))
              ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) -
        νm (fun τ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (τ (e (some (some a))) i : ℝ)) ⬝ᵥ
              fun i : Fin (N + 1) => (τ (e (some (some b))) i : ℝ)) - q) *
            ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (τ (e (skCavityReplicaPairMap j).1) i : ℝ)) ⬝ᵥ
              fun i : Fin (N + 1) => (τ (e (skCavityReplicaPairMap j).2) i : ℝ)) - q))| ≤
      2 * ((n : ℝ) + 2) ^ 2 * β ^ 2 * Real.exp (4 * (((n + 2 : ℕ) : ℝ) + 2) ^ 2 * β ^ 2) *
            (Real.sqrt Gb * Real.sqrt Dtwo) +
          (2 * Dabs / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) ^ 2) := fun j => by
    let G6 : (Fin (n + 2) → Fin N → ℤˣ) → ℝ := fun ρ' =>
      Fab (fun r => ρ' (e (some (some r)))) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ' (e (skCavityReplicaPairMap j).1) i : ℝ)) ⬝ᵥ
          fun i : Fin N => (ρ' (e (skCavityReplicaPairMap j).2) i : ℝ)) - q)
    have hre : (∫ g', ∫ ρ : Option (Option (Fin n)) → Fin N → ℤˣ,
              Fab (fun r => ρ (some (some r))) *
                ((N + 1 : ℝ)⁻¹ *
                  ((fun i : Fin N => (ρ (skCavityReplicaPairMap j).1 i : ℝ)) ⬝ᵥ
                    fun i : Fin N => (ρ (skCavityReplicaPairMap j).2 i : ℝ)) - q)
              ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
                (fun r : Fin N → ℤˣ =>
                  (Real.sqrt (N + 1))⁻¹ * β *
                    (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
                  h * ∑ i : Fin N, (r i : ℝ)))
              ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =
        ∫ g', ∫ ρ' : Fin (n + 2) → Fin N → ℤˣ, G6 ρ'
          ∂(Measure.pi fun _ : Fin (n + 2) => Measure.count.tilted
            (fun r : Fin N → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
              h * ∑ i : Fin N, (r i : ℝ)))
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
      refine integral_congr_ae (ae_of_all _ fun g' => ?_)
      exact integral_pi_count_tilted_reindex e _ (fun ρ : Option (Option (Fin n)) → Fin N → ℤˣ =>
        Fab (fun r => ρ (some (some r))) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (ρ (skCavityReplicaPairMap j).1 i : ℝ)) ⬝ᵥ
            fun i : Fin N => (ρ (skCavityReplicaPairMap j).2 i : ℝ)) - q))
    have H := sk_old_spin_compare N (n + 2) β q h hfix G6 νm hνm Dtwo hDtwo
    have Cv := sk_row_conv N β h q (n + 2) νm hνm ν₂ hν₂ (hso a b hab)
      (fun he => skCavityReplicaPair_ne j (e.injective he))
    rw [← hDabs] at Cv
    rw [hre]
    have hsq : Real.sqrt (νm (fun σ => G6 (fun r i => σ r i.castSucc) ^ 2)) ≤ Real.sqrt Gb :=
      Real.sqrt_le_sqrt (hGb j)
    have hCH : 0 ≤ 2 * ((n + 2 : ℕ) : ℝ) ^ 2 * β ^ 2 *
        Real.exp (4 * (((n + 2 : ℕ) : ℝ) + 2) ^ 2 * β ^ 2) := by positivity
    have H2 : |νm (fun σ => G6 (fun r i => σ r i.castSucc)) - ∫ g', ∫ ρ' : Fin (n + 2) → Fin N → ℤˣ,
        G6 ρ' ∂(Measure.pi fun _ : Fin (n + 2) => Measure.count.tilted
            (fun r : Fin N → ℤˣ =>
              (Real.sqrt (N + 1))⁻¹ * β *
                (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
              h * ∑ i : Fin N, (r i : ℝ)))
          ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)| ≤
        2 * ((n : ℝ) + 2) ^ 2 * β ^ 2 * Real.exp (4 * (((n + 2 : ℕ) : ℝ) + 2) ^ 2 * β ^ 2) *
            (Real.sqrt Gb * Real.sqrt Dtwo) := by
      refine H.trans ?_
      push_cast
      gcongr
    rw [abs_sub_comm] at H2
    refine (abs_sub_le _ (νm (fun σ => G6 (fun r i => σ r i.castSucc))) _).trans ?_
    gcongr
  have hbu : ∀ c : ℕ, |skCavityBCoef β q qhat c| ≤ β ^ 2 := fun c => by
    unfold skCavityBCoef
    rw [abs_mul, abs_of_nonneg (sq_nonneg β)]
    exact mul_le_of_le_one_right (sq_nonneg β) (abs_skCavityBUnscaled_le hq hqhat01 c)
  set Eb : ℝ := 2 * ((n : ℝ) + 2) ^ 2 * β ^ 2 * Real.exp (4 * (((n + 2 : ℕ) : ℝ) + 2) ^ 2 * β ^ 2) *
            (Real.sqrt Gb * Real.sqrt Dtwo) +
          (2 * Dabs / ((N : ℝ) + 1) + 1 / ((N : ℝ) + 1) ^ 2) with hEb
  set OO : SKCavityReplicaPair n → ℝ := fun j =>
    ∫ g', ∫ ρ : Option (Option (Fin n)) → Fin N → ℤˣ,
              Fab (fun r => ρ (some (some r))) *
                ((N + 1 : ℝ)⁻¹ *
                  ((fun i : Fin N => (ρ (skCavityReplicaPairMap j).1 i : ℝ)) ⬝ᵥ
                    fun i : Fin N => (ρ (skCavityReplicaPairMap j).2 i : ℝ)) - q)
              ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
                (fun r : Fin N → ℤˣ =>
                  (Real.sqrt (N + 1))⁻¹ * β *
                    (∑ p : FinPairs N, g' p * (r p.val.1 : ℝ) * (r p.val.2 : ℝ)) +
                  h * ∑ i : Fin N, (r i : ℝ))) ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)
    with hOO
  set Vj : SKCavityReplicaPair n → ℝ := fun j =>
    νm (fun τ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (τ (e (some (some a))) i : ℝ)) ⬝ᵥ
              fun i : Fin (N + 1) => (τ (e (some (some b))) i : ℝ)) - q) *
            ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (τ (e (skCavityReplicaPairMap j).1) i : ℝ)) ⬝ᵥ
              fun i : Fin (N + 1) => (τ (e (skCavityReplicaPairMap j).2) i : ℝ)) - q)) with hVj
  have hmid : |∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
        (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences x y j) * (OO j - Vj j))| ≤
      (∑ j : SKCavityReplicaPair n, |skCavityReplicaPairWeight n j|) * β ^ 2 * Eb := by
    rw [mul_assoc]
    refine Weights.abs_weighted_sum_le _ _ fun j => ?_
    rw [abs_mul]
    exact mul_le_mul (hbu _) (hj j) (abs_nonneg _) (sq_nonneg β)
  have hT' : |ν (fun σ => Fab (fun r i => σ r i.castSucc) *
        (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q)) -
      ∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
        (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences x y j) * OO j)| ≤
      4 * (n : ℝ) ^ 2 * ((n : ℝ) + 2) ^ 2 * β ^ 4 * Real.exp (4 * ((n : ℝ) + 4) ^ 2 * β ^ 2) *
        (Real.sqrt Vf * Real.sqrt Dfour) := by
    refine T.trans ?_
    gcongr
  have hsplit : ∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
        (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences x y j) * OO j) -
      ∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
        (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences x y j) * Vj j) =
      ∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
        (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences x y j) * (OO j - Vj j)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hK : |ν (fun σ => (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q) *
        (((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ))) -
      skCavityBUnscaled q qhat (skCavityCoincidences x y a b)| ≤
      4 * (n : ℝ) ^ 2 * β ^ 2 * Real.exp (4 * ((n : ℝ) + 2) ^ 2 * β ^ 2) * Dabs := K
  rw [S1]
  have hmid' : |(∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
        (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences x y j) * OO j)) -
      ∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
        (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences x y j) * Vj j)| ≤
      (∑ j : SKCavityReplicaPair n, |skCavityReplicaPairWeight n j|) * β ^ 2 * Eb := by
    rw [hsplit]; exact hmid
  exact abs_row_combine rfl rfl (inv_nonneg.2 hM0.le) hT' hmid' hK

end Row

section Classes

variable (N : ℕ) (β h q : ℝ)

/-- **Classes of products of two overlaps (one shared replica).** -/
theorem sk_nu_class_one {m : ℕ}
    (ν₃ : ((Fin 3 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₃ : ∀ Φ, ν₃ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 3 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 3 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (νm : ((Fin m → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hνm : ∀ Φ, νm Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin m → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    {s t t' : Fin m} (hst : s ≠ t) (hst' : s ≠ t') (htt' : t ≠ t') :
    νm (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ s i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ t i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ s i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ t' i : ℝ)) - q)) =
      ν₃ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q)) := by
  have hρ : Function.Injective (![s, t, t'] : Fin 3 → Fin m) := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp_all [Ne.symm hst, Ne.symm hst', Ne.symm htt']
  have := sk_nu_marginal_inj N β h ν₃ hν₃ νm hνm hρ
    (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q))
  simpa using this

/-- **Classes of products of two overlaps (four distinct replicas).** -/
theorem sk_nu_class_zero {m : ℕ}
    (ν₄ : ((Fin 4 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₄ : ∀ Φ, ν₄ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (νm : ((Fin m → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hνm : ∀ Φ, νm Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin m → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    {x y x' y' : Fin m} (hxy : x ≠ y) (hxx' : x ≠ x') (hxy' : x ≠ y') (hyx' : y ≠ x')
    (hyy' : y ≠ y') (hx'y' : x' ≠ y') :
    νm (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ x i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ y i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ x' i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ y' i : ℝ)) - q)) =
      ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q)) := by
  have hρ : Function.Injective (![x, y, x', y'] : Fin 4 → Fin m) := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      simp_all [Ne.symm hxy, Ne.symm hxx', Ne.symm hxy', Ne.symm hyx', Ne.symm hyy',
        Ne.symm hx'y']
  have := sk_nu_marginal_inj N β h ν₄ hν₄ νm hνm hρ
    (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q))
  simpa using this

/-- **Classes of products of two overlaps, indexed through an injection.**  For an injective
numbering `e` of the replicas and pairs `p₁ ≠ p₂`, `r₁ ≠ r₂`, the average
`ν_m((R_{e p₁, e p₂} - q)(R_{e r₁, e r₂} - q))` is `U` if the pairs coincide, `V` if they share
exactly one replica and `W` if they are disjoint, where `U, V, W` are the averages of
`(R₀₁ - q)²`, `(R₀₁ - q)(R₀₂ - q)`, `(R₀₁ - q)(R₂₃ - q)`. -/
theorem sk_nu_overlap_class {m : ℕ} {R : Type*} [DecidableEq R]
    (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₂ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₃ : ((Fin 3 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₃ : ∀ Φ, ν₃ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 3 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 3 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₄ : ((Fin 4 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₄ : ∀ Φ, ν₄ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (νm : ((Fin m → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hνm : ∀ Φ, νm Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin m → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (e : R → Fin m) (he : Function.Injective e) {p₁ p₂ r₁ r₂ : R} (hp : p₁ ≠ p₂) (hr : r₁ ≠ r₂) :
    νm (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ (e p₁) i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ (e p₂) i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ (e r₁) i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ (e r₂) i : ℝ)) - q)) =
      if (p₁ = r₁ ∧ p₂ = r₂) ∨ (p₁ = r₂ ∧ p₂ = r₁) then
        ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q))
      else if p₁ = r₁ ∨ p₁ = r₂ ∨ p₂ = r₁ ∨ p₂ = r₂ then
        ν₃ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q))
      else
        ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q)) := by
  have hne : ∀ u v : R, u ≠ v → e u ≠ e v := fun u v huv h' => huv (he h')
  have two : ∀ u v : R, u ≠ v →
      νm (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ (e u) i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ (e v) i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ (e u) i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ (e v) i : ℝ)) - q)) =
      ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)) := fun u v huv =>
    sk_nu_pair_marginal N β h m νm hνm ν₂ hν₂ (hne u v huv)
      (fun a b => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (a i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (b i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (a i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (b i : ℝ)) - q))
  have one : ∀ s t t' : R, s ≠ t → s ≠ t' → t ≠ t' →
      νm (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ (e s) i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ (e t) i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ (e s) i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ (e t') i : ℝ)) - q)) =
      ν₃ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q)) := fun s t t' h1 h2 h3 =>
    sk_nu_class_one N β h q ν₃ hν₃ νm hνm (hne s t h1) (hne s t' h2) (hne t t' h3)
  have zero : ∀ u v u' v' : R, u ≠ v → u ≠ u' → u ≠ v' → v ≠ u' → v ≠ v' → u' ≠ v' →
      νm (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ (e u) i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ (e v) i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ (e u') i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ (e v') i : ℝ)) - q)) =
      ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2 i : ℝ)) ⬝ᵥ
            fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q)) := fun u v u' v' h1 h2 h3 h4 h5 h6 =>
    sk_nu_class_zero N β h q ν₄ hν₄ νm hνm (hne u v h1) (hne u u' h2) (hne u v' h3)
      (hne v u' h4) (hne v v' h5) (hne u' v' h6)
  have comm : ∀ (u v : R) (σ : Fin m → Fin (N + 1) → ℤˣ),
      (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ (e u) i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ (e v) i : ℝ)) =
      (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ (e v) i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ (e u) i : ℝ)) := fun u v σ => by rw [dotProduct_comm]
  split_ifs with c1 c2
  · rcases c1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact two p₁ p₂ hp
    · simp only [comm p₁ p₂]
      exact two p₂ p₁ hp.symm
  · have hA : ¬(p₁ = r₁ ∧ p₂ = r₂) := fun h' => c1 (Or.inl h')
    have hB : ¬(p₁ = r₂ ∧ p₂ = r₁) := fun h' => c1 (Or.inr h')
    rcases c2 with h1 | h2 | h3 | h4
    · subst h1
      have : p₂ ≠ r₂ := fun h' => hA ⟨rfl, h'⟩
      exact one p₁ p₂ r₂ hp hr this
    · subst h2
      have : p₂ ≠ r₁ := fun h' => hB ⟨rfl, h'⟩
      simp only [comm r₁ p₁]
      exact one p₁ p₂ r₁ hp hr.symm this
    · subst h3
      have : p₁ ≠ r₂ := fun h' => hB ⟨h', rfl⟩
      simp only [comm p₁ p₂]
      exact one p₂ p₁ r₂ hp.symm hr this
    · subst h4
      have : p₁ ≠ r₁ := fun h' => hA ⟨h', rfl⟩
      simp only [comm p₁ p₂, comm r₁ p₂]
      exact one p₂ p₁ r₁ hp.symm hr.symm this
  · simp only [not_or] at c2
    exact zero p₁ p₂ r₁ r₂ hp c2.1 c2.2.1 c2.2.2.1 c2.2.2.2 hr

end Classes

section Bounds

/-- `(x y)² ≤ (x⁴ + y⁴)/2`. -/
theorem mul_sq_le_half_pow_four (x y : ℝ) : (x * y) ^ 2 ≤ (x ^ 4 + y ^ 4) / 2 := by
  nlinarith only [sq_nonneg (x ^ 2 - y ^ 2)]

variable (N : ℕ) (β h q : ℝ)

/-- **The `L²` size of `f = (R⁻_{ab} - q)(ε_xε_y - q)`:**
`ν(f²) ≤ 8 ν((R_{1,2} - q)²) + 8/M²`. -/
theorem sk_row_Vf_bound (n : ℕ)
    (ν : ((Fin n → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin n => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₂ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (hq : q ∈ Set.Icc (0 : ℝ) 1) {x y a b : Fin n} (hab : a ≠ b) :
    ν (fun σ => (((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ a i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ b i.castSucc : ℝ)) - q) *
        (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q)) ^ 2) ≤
      8 * ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2) + 8 / (N + 1) ^ 2 := by
  obtain ⟨hadd, hsmul, hmono, hconst⟩ := sk_replica_avg_calculus N n β h ν hν
  have hM0 : (0 : ℝ) < N + 1 := by positivity
  have hmarg : ν (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ a i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ b i : ℝ)) - q) ^ 2) =
      ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2) :=
    sk_nu_pair_marginal N β h n ν hν ν₂ hν₂ hab
      (fun u v => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (u i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (v i : ℝ)) - q) ^ 2)
  have hpt : ∀ σ : Fin n → Fin (N + 1) → ℤˣ,
      (((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ a i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ b i.castSucc : ℝ)) - q) *
        (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q)) ^ 2 ≤
      8 * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ a i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ b i : ℝ)) - q) ^ 2 + 8 / (N + 1) ^ 2 := fun σ => by
    set X : ℝ := (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ a i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ b i : ℝ)) - q with hX
    set δ : ℝ := (N + 1 : ℝ)⁻¹ * (((σ a (Fin.last N) : ℤˣ) : ℝ) * ((σ b (Fin.last N) : ℤˣ) : ℝ))
      with hδ
    have e1 : (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ a i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ b i.castSucc : ℝ)) - q = X - δ := by
      simp only [hX, hδ, dotProduct, Fin.sum_univ_castSucc]; ring
    have hδ1 : δ ^ 2 = 1 / (N + 1) ^ 2 := by
      simp only [hδ, mul_pow, units_cast_sq, mul_one, inv_pow, one_div]
    have hs : (((σ x (Fin.last N) : ℤˣ) : ℝ) * ((σ y (Fin.last N) : ℤˣ) : ℝ) - q) ^ 2 ≤ 4 := by
      simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using
        pow_le_pow_left₀ (abs_nonneg _) (abs_units_cast_mul_sub_le_two _ _ hq) 2
    rw [e1, mul_pow]
    have := sub_pow_two_mul_le (k := 1) le_rfl X δ
    norm_num at this
    have hp := mul_le_mul_of_nonneg_left hs (sq_nonneg (X - δ))
    have e8 : 8 / ((N : ℝ) + 1) ^ 2 = 8 * (1 / ((N : ℝ) + 1) ^ 2) := by ring
    linarith only [hp, this, hδ1, e8]
  have h1 := hmono _ _ hpt
  rw [hadd, hsmul, hconst, hmarg] at h1
  exact h1

/-- **The `L²` size of a product of two truncated overlaps:**
`ν(((R⁻_P - q)(R⁻_Q - q))²) ≤ 8 ν((R_{1,2} - q)⁴) + 8/M⁴`. -/
theorem sk_row_Gb_bound (m : ℕ)
    (ν : ((Fin m → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν : ∀ Φ, ν Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin m → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin m => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₂ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    {p₁ p₂ r₁ r₂ : Fin m} (hp : p₁ ≠ p₂) (hr : r₁ ≠ r₂) :
    ν (fun σ => (((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ p₁ i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ p₂ i.castSucc : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ r₁ i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ r₂ i.castSucc : ℝ)) - q)) ^ 2) ≤
      8 * ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 4) + 8 / (N + 1) ^ 4 := by
  obtain ⟨hadd, hsmul, hmono, hconst⟩ := sk_replica_avg_calculus N m β h ν hν
  have hM0 : (0 : ℝ) < N + 1 := by positivity
  have hmarg : ∀ {u v : Fin m}, u ≠ v →
      ν (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ u i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ v i : ℝ)) - q) ^ 4) =
      ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 4) := fun {u v} huv =>
    sk_nu_pair_marginal N β h m ν hν ν₂ hν₂ huv
      (fun u v => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (u i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (v i : ℝ)) - q) ^ 4)
  have hdelta : ∀ (σ : Fin m → Fin (N + 1) → ℤˣ) (u v : Fin m),
      ((N + 1 : ℝ)⁻¹ * (((σ u (Fin.last N) : ℤˣ) : ℝ) * ((σ v (Fin.last N) : ℤˣ) : ℝ))) ^ 4 =
        1 / (N + 1) ^ 4 := fun σ u v => by
    have h4 : ∀ w : ℤˣ, ((w : ℤ) : ℝ) ^ 4 = 1 := fun w => by
      rw [show 4 = 2 * 2 from rfl, pow_mul, units_cast_sq, one_pow]
    simp only [mul_pow, h4, mul_one, inv_pow, one_div]
  have hpt : ∀ σ : Fin m → Fin (N + 1) → ℤˣ,
      (((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ p₁ i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ p₂ i.castSucc : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ r₁ i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ r₂ i.castSucc : ℝ)) - q)) ^ 2 ≤
      4 * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ p₁ i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ p₂ i : ℝ)) - q) ^ 4 +
        4 * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ r₁ i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ r₂ i : ℝ)) - q) ^ 4 + 8 / (N + 1) ^ 4 := fun σ => by
    set X : ℝ := (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ p₁ i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ p₂ i : ℝ)) - q with hX
    set Y : ℝ := (N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ r₁ i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ r₂ i : ℝ)) - q with hY
    set δ : ℝ := (N + 1 : ℝ)⁻¹ * (((σ p₁ (Fin.last N) : ℤˣ) : ℝ) * ((σ p₂ (Fin.last N) : ℤˣ) : ℝ))
      with hδ
    set δ' : ℝ := (N + 1 : ℝ)⁻¹ * (((σ r₁ (Fin.last N) : ℤˣ) : ℝ) * ((σ r₂ (Fin.last N) : ℤˣ) : ℝ))
      with hδ'
    have e1 : (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ p₁ i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ p₂ i.castSucc : ℝ)) - q = X - δ := by
      simp only [hX, hδ, dotProduct, Fin.sum_univ_castSucc]; ring
    have e2 : (N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ r₁ i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ r₂ i.castSucc : ℝ)) - q = Y - δ' := by
      simp only [hY, hδ', dotProduct, Fin.sum_univ_castSucc]; ring
    rw [e1, e2]
    have h1 := mul_sq_le_half_pow_four (X - δ) (Y - δ')
    have h2 := sub_pow_two_mul_le (k := 2) (by norm_num) X δ
    have h3 := sub_pow_two_mul_le (k := 2) (by norm_num) Y δ'
    norm_num at h2 h3
    have h4 := hdelta σ p₁ p₂
    have h5 := hdelta σ r₁ r₂
    have e8 : 8 / ((N : ℝ) + 1) ^ 4 = 8 * (1 / ((N : ℝ) + 1) ^ 4) := by ring
    linarith only [h1, h2, h3, h4, h5, e8]
  have h1 := hmono _ _ hpt
  rw [hadd, hadd, hsmul, hsmul, hconst, hmarg hp, hmarg hr] at h1
  linarith only [h1]

end Bounds

section RowSums

/-- The three-family signed sum of a class-valued kernel, in the filter form. -/
theorem sk_row_sum_aux (n : ℕ) (b : ℕ → ℝ) (x y a c : Fin n) (U V W : ℝ) :
    ∑ j : SKCavityReplicaPair n, skCavityReplicaPairWeight n j *
      (b (skCavityReplicaPairCoincidences x y j) *
        (if (some (some a) = (skCavityReplicaPairMap j).1 ∧
              some (some c) = (skCavityReplicaPairMap j).2) ∨
            (some (some a) = (skCavityReplicaPairMap j).2 ∧
              some (some c) = (skCavityReplicaPairMap j).1) then U
          else if some (some a) = (skCavityReplicaPairMap j).1 ∨
              some (some a) = (skCavityReplicaPairMap j).2 ∨
              some (some c) = (skCavityReplicaPairMap j).1 ∨
              some (some c) = (skCavityReplicaPairMap j).2 then V else W)) =
    ∑ p : Fin n × Fin n with p.1 < p.2,
      (b (skCavityCoincidences (some (some x)) (some (some y)) (some (some p.1)) (some (some p.2)))
        *
        (if (some (some a) = some (some p.1) ∧ some (some c) = some (some p.2)) ∨
            (some (some a) = some (some p.2) ∧ some (some c) = some (some p.1)) then U
          else if some (some a) = some (some p.1) ∨ some (some a) = some (some p.2) ∨
              some (some c) = some (some p.1) ∨ some (some c) = some (some p.2) then V else W))
    - n * ∑ r : Fin n, (b (skCavityCoincidences (some (some x)) (some (some y)) (some (some r))
      (some none)) *
        (if (some (some a) = some (some r) ∧ some (some c) = some none) ∨
            (some (some a) = some none ∧ some (some c) = some (some r)) then U
          else if some (some a) = some (some r) ∨ some (some a) = some none ∨
              some (some c) = some (some r) ∨ some (some c) = some none then V else W))
    + n * (n + 1) / 2 * (b (skCavityCoincidences (some (some x)) (some (some y)) (some none) none) *
        (if (some (some a) = some none ∧ some (some c) = none) ∨
            (some (some a) = none ∧ some (some c) = some none) then U
          else if some (some a) = some none ∨ some (some a) = none ∨
              some (some c) = some none ∨ some (some c) = none then V else W)) := by
  have := sk_cavity_signed_pair_sum (n := n) (fun α β : Option (Option (Fin n)) =>
    b (skCavityCoincidences (some (some x)) (some (some y)) α β) *
      (if (some (some a) = α ∧ some (some c) = β) ∨ (some (some a) = β ∧ some (some c) = α) then U
        else if some (some a) = α ∨ some (some a) = β ∨ some (some c) = α ∨ some (some c) = β
          then V else W)) id
  simp only [id] at this
  unfold skCavityReplicaPairCoincidences
  exact this.symm

/-- First row of the AT matrix: the signed three-family sum for the pair `(1,2)` against `(1,2)`. -/
theorem sk_row_sum_zero (b : ℕ → ℝ) (U V W : ℝ) :
    ∑ p : Fin 4 × Fin 4 with p.1 < p.2,
      (b (skCavityCoincidences (some (some (0:Fin 4))) (some (some 1)) (some (some p.1)) (some
        (some p.2))) *
        (if (some (some (0:Fin 4)) = some (some p.1) ∧ some (some (1:Fin 4)) = some (some p.2)) ∨
            (some (some (0:Fin 4)) = some (some p.2) ∧ some (some (1:Fin 4)) = some (some p.1))
              then U
          else if some (some (0:Fin 4)) = some (some p.1) ∨ some (some (0:Fin 4)) = some (some p.2)
            ∨
              some (some (1:Fin 4)) = some (some p.1) ∨ some (some (1:Fin 4)) = some (some p.2)
                then V else W))
    - (4:ℕ) * ∑ r : Fin 4, (b (skCavityCoincidences (some (some (0:Fin 4))) (some (some 1)) (some
      (some r)) (some none)) *
        (if (some (some (0:Fin 4)) = some (some r) ∧ some (some (1:Fin 4)) = some none) ∨
            (some (some (0:Fin 4)) = some none ∧ some (some (1:Fin 4)) = some (some r)) then U
          else if some (some (0:Fin 4)) = some (some r) ∨ some (some (0:Fin 4)) = some none ∨
              some (some (1:Fin 4)) = some (some r) ∨ some (some (1:Fin 4)) = some none then V else
                W))
    + (4:ℕ) * ((4:ℕ) + 1) / 2 * (b (skCavityCoincidences (some (some (0:Fin 4))) (some (some 1))
      (some none) none) *
        (if (some (some (0:Fin 4)) = some none ∧ some (some (1:Fin 4)) = none) ∨
            (some (some (0:Fin 4)) = none ∧ some (some (1:Fin 4)) = some none) then U
          else if some (some (0:Fin 4)) = some none ∨ some (some (0:Fin 4)) = none ∨
              some (some (1:Fin 4)) = some none ∨ some (some (1:Fin 4)) = none then V else W))
   = b 2 * U - 4 * b 1 * V + 3 * b 0 * W := by
  simp [Fin.sum_univ_four, Finset.sum_filter, Fintype.sum_prod_type, skCavityCoincidences]
  ring

/-- Second row of the AT matrix: pair `(1,2)` against `(1,3)`. -/
theorem sk_row_sum_one (b : ℕ → ℝ) (U V W : ℝ) :
    ∑ p : Fin 4 × Fin 4 with p.1 < p.2,
      (b (skCavityCoincidences (some (some (0:Fin 4))) (some (some 1)) (some (some p.1)) (some
        (some p.2))) *
        (if (some (some (0:Fin 4)) = some (some p.1) ∧ some (some (2:Fin 4)) = some (some p.2)) ∨
            (some (some (0:Fin 4)) = some (some p.2) ∧ some (some (2:Fin 4)) = some (some p.1))
              then U
          else if some (some (0:Fin 4)) = some (some p.1) ∨ some (some (0:Fin 4)) = some (some p.2)
            ∨
              some (some (2:Fin 4)) = some (some p.1) ∨ some (some (2:Fin 4)) = some (some p.2)
                then V else W))
    - (4:ℕ) * ∑ r : Fin 4, (b (skCavityCoincidences (some (some (0:Fin 4))) (some (some 1)) (some
      (some r)) (some none)) *
        (if (some (some (0:Fin 4)) = some (some r) ∧ some (some (2:Fin 4)) = some none) ∨
            (some (some (0:Fin 4)) = some none ∧ some (some (2:Fin 4)) = some (some r)) then U
          else if some (some (0:Fin 4)) = some (some r) ∨ some (some (0:Fin 4)) = some none ∨
              some (some (2:Fin 4)) = some (some r) ∨ some (some (2:Fin 4)) = some none then V else
                W))
    + (4:ℕ) * ((4:ℕ) + 1) / 2 * (b (skCavityCoincidences (some (some (0:Fin 4))) (some (some 1))
      (some none) none) *
        (if (some (some (0:Fin 4)) = some none ∧ some (some (2:Fin 4)) = none) ∨
            (some (some (0:Fin 4)) = none ∧ some (some (2:Fin 4)) = some none) then U
          else if some (some (0:Fin 4)) = some none ∨ some (some (0:Fin 4)) = none ∨
              some (some (2:Fin 4)) = some none ∨ some (some (2:Fin 4)) = none then V else W))
   = b 1 * U + (b 2 - 2 * b 1 - 3 * b 0) * V + (6 * b 0 - 3 * b 1) * W := by
  simp [Fin.sum_univ_four, Finset.sum_filter, Fintype.sum_prod_type, skCavityCoincidences]
  ring

/-- Third row of the AT matrix: pair `(1,2)` against `(3,4)`. -/
theorem sk_row_sum_two (b : ℕ → ℝ) (U V W : ℝ) :
    ∑ p : Fin 4 × Fin 4 with p.1 < p.2,
      (b (skCavityCoincidences (some (some (0:Fin 4))) (some (some 1)) (some (some p.1)) (some
        (some p.2))) *
        (if (some (some (2:Fin 4)) = some (some p.1) ∧ some (some (3:Fin 4)) = some (some p.2)) ∨
            (some (some (2:Fin 4)) = some (some p.2) ∧ some (some (3:Fin 4)) = some (some p.1))
              then U
          else if some (some (2:Fin 4)) = some (some p.1) ∨ some (some (2:Fin 4)) = some (some p.2)
            ∨
              some (some (3:Fin 4)) = some (some p.1) ∨ some (some (3:Fin 4)) = some (some p.2)
                then V else W))
    - (4:ℕ) * ∑ r : Fin 4, (b (skCavityCoincidences (some (some (0:Fin 4))) (some (some 1)) (some
      (some r)) (some none)) *
        (if (some (some (2:Fin 4)) = some (some r) ∧ some (some (3:Fin 4)) = some none) ∨
            (some (some (2:Fin 4)) = some none ∧ some (some (3:Fin 4)) = some (some r)) then U
          else if some (some (2:Fin 4)) = some (some r) ∨ some (some (2:Fin 4)) = some none ∨
              some (some (3:Fin 4)) = some (some r) ∨ some (some (3:Fin 4)) = some none then V else
                W))
    + (4:ℕ) * ((4:ℕ) + 1) / 2 * (b (skCavityCoincidences (some (some (0:Fin 4))) (some (some 1))
      (some none) none) *
        (if (some (some (2:Fin 4)) = some none ∧ some (some (3:Fin 4)) = none) ∨
            (some (some (2:Fin 4)) = none ∧ some (some (3:Fin 4)) = some none) then U
          else if some (some (2:Fin 4)) = some none ∨ some (some (2:Fin 4)) = none ∨
              some (some (3:Fin 4)) = some none ∨ some (some (3:Fin 4)) = none then V else W))
   = b 0 * U + (4 * b 1 - 8 * b 0) * V + (b 2 - 8 * b 1 + 10 * b 0) * W := by
  simp [Fin.sum_univ_four, Finset.sum_filter, Fintype.sum_prod_type, skCavityCoincidences]
  ring

/-- The first row of the AT matrix as a sum over the replica families `j`. -/
theorem sk_row_sum_zero_j (b : ℕ → ℝ) (U V W : ℝ) :
    ∑ j : SKCavityReplicaPair 4, skCavityReplicaPairWeight 4 j *
      (b (skCavityReplicaPairCoincidences (0 : Fin 4) 1 j) *
        (if (some (some (0 : Fin 4)) = (skCavityReplicaPairMap j).1 ∧ some (some (1 : Fin 4)) =
          (skCavityReplicaPairMap j).2) ∨ (some (some (0 : Fin 4)) = (skCavityReplicaPairMap j).2 ∧
          some (some (1 : Fin 4)) = (skCavityReplicaPairMap j).1) then U
          else if some (some (0 : Fin 4)) = (skCavityReplicaPairMap j).1 ∨ some (some (0 : Fin 4))
            = (skCavityReplicaPairMap j).2 ∨ some (some (1 : Fin 4)) = (skCavityReplicaPairMap j).1
            ∨ some (some (1 : Fin 4)) = (skCavityReplicaPairMap j).2 then V else W)) =
      b 2 * U - 4 * b 1 * V + 3 * b 0 * W := by
  rw [sk_row_sum_aux 4 b 0 1 0 1 U V W]
  exact sk_row_sum_zero b U V W

/-- The second row of the AT matrix as a sum over the replica families `j`. -/
theorem sk_row_sum_one_j (b : ℕ → ℝ) (U V W : ℝ) :
    ∑ j : SKCavityReplicaPair 4, skCavityReplicaPairWeight 4 j *
      (b (skCavityReplicaPairCoincidences (0 : Fin 4) 1 j) *
        (if (some (some (0 : Fin 4)) = (skCavityReplicaPairMap j).1 ∧ some (some (2 : Fin 4)) =
          (skCavityReplicaPairMap j).2) ∨ (some (some (0 : Fin 4)) = (skCavityReplicaPairMap j).2 ∧
          some (some (2 : Fin 4)) = (skCavityReplicaPairMap j).1) then U
          else if some (some (0 : Fin 4)) = (skCavityReplicaPairMap j).1 ∨ some (some (0 : Fin 4))
            = (skCavityReplicaPairMap j).2 ∨ some (some (2 : Fin 4)) = (skCavityReplicaPairMap j).1
            ∨ some (some (2 : Fin 4)) = (skCavityReplicaPairMap j).2 then V else W)) =
      b 1 * U + (b 2 - 2 * b 1 - 3 * b 0) * V + (6 * b 0 - 3 * b 1) * W := by
  rw [sk_row_sum_aux 4 b 0 1 0 2 U V W]
  exact sk_row_sum_one b U V W

/-- The third row of the AT matrix as a sum over the replica families `j`. -/
theorem sk_row_sum_two_j (b : ℕ → ℝ) (U V W : ℝ) :
    ∑ j : SKCavityReplicaPair 4, skCavityReplicaPairWeight 4 j *
      (b (skCavityReplicaPairCoincidences (0 : Fin 4) 1 j) *
        (if (some (some (2 : Fin 4)) = (skCavityReplicaPairMap j).1 ∧ some (some (3 : Fin 4)) =
          (skCavityReplicaPairMap j).2) ∨ (some (some (2 : Fin 4)) = (skCavityReplicaPairMap j).2 ∧
          some (some (3 : Fin 4)) = (skCavityReplicaPairMap j).1) then U
          else if some (some (2 : Fin 4)) = (skCavityReplicaPairMap j).1 ∨ some (some (2 : Fin 4))
            = (skCavityReplicaPairMap j).2 ∨ some (some (3 : Fin 4)) = (skCavityReplicaPairMap j).1
            ∨ some (some (3 : Fin 4)) = (skCavityReplicaPairMap j).2 then V else W)) =
      b 0 * U + (4 * b 1 - 8 * b 0) * V + (b 2 - 8 * b 1 + 10 * b 0) * W := by
  rw [sk_row_sum_aux 4 b 0 1 2 3 U V W]
  exact sk_row_sum_two b U V W

end RowSums

/-- The vector equation `v = S + A v + R` holds for the remainder defined by the three scalar
equations. -/
theorem sk_at_vec_eq (U V W q qhat M b2 b1 b0 : ℝ) :
    ![U, V, W] = skAtSource q qhat M + skAtMatrix b2 b1 b0 *ᵥ ![U, V, W] +
      ![U - (1 - q ^ 2) / M - skAtRowZero b2 b1 b0 U V W,
        V - (q - q ^ 2) / M - skAtRowOne b2 b1 b0 U V W,
        W - (qhat - q ^ 2) / M - skAtRowTwo b2 b1 b0 U V W] := by
  rw [sk_at_covariance_equations_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  exact ⟨by ring, by ring, by ring⟩

section RowBound

/-- **One row with explicit error bounds in terms of the overlap moments.**  Let
`𝔼⟨(R_{1,2} - q)²⟩ ≤ K₁/M` and `𝔼⟨(R_{1,2} - q)⁴⟩ ≤ K₂/M²`.  For `x = 0`, `y = 1` and any
`a ≠ c` among `4` replicas, `ν((R₀₁ - q)(R_{ac} - q))` differs from `M⁻¹ b(c) +
∑_j w_j b(c_j) ν₆((R_{ac} - q)(R_j - q))` by at most `E`. -/
theorem sk_cov_row_bound (N : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (qhat : ℝ)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    (hqhat01 : qhat ∈ Set.Icc (0 : ℝ) 1) (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (e : Option (Option (Fin 4)) ≃ Fin (4 + 2))
    (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₂ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₄ : ((Fin 4 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₄ : ∀ Φ, ν₄ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₆ : ((Fin (4 + 2) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₆ : ∀ Φ, ν₆ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin (4 + 2) → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin (4 + 2) => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (hD2 : ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2) ≤ K₁ / ((N : ℝ) + 1))
    (hD4 : ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 4) ≤ K₂ / ((N : ℝ) + 1) ^ 2)
    {a c : Fin 4} (hac : a ≠ c) (E : ℝ)
    (hE : E = 2304 * β ^ 4 * Real.exp (256 * β ^ 2) *
        (Real.sqrt ((8 * K₁ + 8) / ((N : ℝ) + 1)) * Real.sqrt (K₂ / ((N : ℝ) + 1) ^ 2)) +
      32 * β ^ 2 * (72 * β ^ 2 * Real.exp (256 * β ^ 2) *
          (Real.sqrt ((8 * K₂ + 8) / ((N : ℝ) + 1) ^ 2) * Real.sqrt (K₁ / ((N : ℝ) + 1))) +
        (2 * ((K₁ + 1) / (2 * Real.sqrt ((N : ℝ) + 1))) / ((N : ℝ) + 1) +
          1 / ((N : ℝ) + 1) ^ 2)) +
      (N + 1 : ℝ)⁻¹ * (64 * β ^ 2 * Real.exp (144 * β ^ 2) *
        ((K₁ + 1) / (2 * Real.sqrt ((N : ℝ) + 1))))) :
    |ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ a i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ c i : ℝ)) - q)) -
      (N + 1 : ℝ)⁻¹ * skCavityBUnscaled q qhat (skCavityCoincidences (0 : Fin 4) 1 a c) -
      ∑ j : SKCavityReplicaPair 4, skCavityReplicaPairWeight 4 j *
        (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences (0 : Fin 4) 1 j) *
          ν₆ (fun τ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (τ (e (some (some a))) i : ℝ)) ⬝ᵥ
              fun i : Fin (N + 1) => (τ (e (some (some c))) i : ℝ)) - q) *
            ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (τ (e (skCavityReplicaPairMap j).1) i : ℝ)) ⬝ᵥ
              fun i : Fin (N + 1) => (τ (e (skCavityReplicaPairMap j).2) i : ℝ)) - q)))| ≤ E := by
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := fixedPoint_mem_Icc hfix
  have hM0 : (0 : ℝ) < N + 1 := by positivity
  have hM1 : (1 : ℝ) ≤ N + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hD2' : (∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ,
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2
        ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
          (Real.sqrt (N + 1))⁻¹ * β *
            (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
          h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1)) ≤ K₁ / ((N : ℝ) + 1) := by
    rw [← hν₂]; exact hD2
  have hDabs := sk_abs_dev_le N β h q K₁ hD2'
  rw [← hν₂] at hDabs
  have hVf := sk_row_Vf_bound N β h q 4 ν₄ hν₄ ν₂ hν₂ hq (x := 0) (y := 1) hac
  have hso : ∀ r r' : Fin 4, r ≠ r' → e (some (some r)) ≠ e (some (some r')) :=
    fun r r' hr he' => hr (Option.some.inj (Option.some.inj (e.injective he')))
  have hGb : ∀ j : SKCavityReplicaPair 4, ν₆ (fun σ =>
      (((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (e (some (some a))) i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ (e (some (some c))) i.castSucc : ℝ)) - q) *
        ((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ (e (skCavityReplicaPairMap j).1) i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ (e (skCavityReplicaPairMap j).2) i.castSucc : ℝ)) - q)) ^ 2) ≤
      (8 * K₂ + 8) / ((N : ℝ) + 1) ^ 2 := fun j => by
    have := sk_row_Gb_bound N β h q (4 + 2) ν₆ hν₆ ν₂ hν₂ (hso a c hac)
      (fun he' => skCavityReplicaPair_ne j (e.injective he'))
    refine this.trans ?_
    have h8 : 8 / ((N : ℝ) + 1) ^ 4 ≤ 8 / ((N : ℝ) + 1) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_right₀ hM1 (by norm_num))
    have e8 : (8 * K₂ + 8) / ((N : ℝ) + 1) ^ 2 = 8 * (K₂ / ((N : ℝ) + 1) ^ 2) +
        8 / ((N : ℝ) + 1) ^ 2 := by ring
    rw [e8]
    nlinarith only [hD4, h8]
  have hVf' : ν₄ (fun σ => (((N + 1 : ℝ)⁻¹ * ((fun i : Fin N => (σ a i.castSucc : ℝ)) ⬝ᵥ
          fun i : Fin N => (σ c i.castSucc : ℝ)) - q) *
        (((σ 0 (Fin.last N) : ℤˣ) : ℝ) * ((σ 1 (Fin.last N) : ℤˣ) : ℝ) - q)) ^ 2) ≤
      (8 * K₁ + 8) / ((N : ℝ) + 1) := by
    refine hVf.trans ?_
    have h8 : 8 / ((N : ℝ) + 1) ^ 2 ≤ 8 / ((N : ℝ) + 1) :=
      div_le_div_of_nonneg_left (by norm_num) hM0 (by nlinarith only [hM1])
    have e8 : (8 * K₁ + 8) / ((N : ℝ) + 1) = 8 * (K₁ / ((N : ℝ) + 1)) + 8 / ((N : ℝ) + 1) := by
      ring
    rw [e8]
    nlinarith only [hD2, h8]
  have key := sk_row_equation N 4 β q h hfix qhat hqhat hqhat01 (x := 0) (y := 1) (a := a)
    (b := c) (by decide) hac e ν₄ hν₄ ν₆ hν₆ ν₂ hν₂ ((8 * K₁ + 8) / ((N : ℝ) + 1))
    ((8 * K₂ + 8) / ((N : ℝ) + 1) ^ 2)
    (ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2))
    (ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 4))
    (ν₂ (fun σ => |(N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q|)) hVf' hGb (hν₂ _) (hν₂ _) rfl
  refine key.trans ?_
  rw [hE]
  have hs : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.2 hM0
  have hsum32 : ∑ j : SKCavityReplicaPair 4, |skCavityReplicaPairWeight 4 j| = 32 := by
    have hc : Fintype.card (FinPairs 4) = 6 := by
      unfold FinPairs; decide
    simp [Fintype.sum_sum_type, skCavityReplicaPairWeight, hc]
    norm_num
  rw [hsum32]
  have e6 : (((4 + 2 : ℕ) : ℝ) + 2) = 8 := by norm_num
  simp only [e6, Nat.cast_ofNat]
  norm_num
  gcongr

/-- **The covariance system (Talagrand Eqs. (1.231)-(1.233)) with explicit errors.**  Let
`U = 𝔼⟨(R₁₂ - q)²⟩`, `V = 𝔼⟨(R₁₂ - q)(R₁₃ - q)⟩`, `W = 𝔼⟨(R₁₂ - q)(R₃₄ - q)⟩` for the
`(N+1)`-spin system. If `𝔼⟨(R₁₂ - q)²⟩ ≤ K₁/M` and `𝔼⟨(R₁₂ - q)⁴⟩ ≤ K₂/M²`, there is a
remainder `R` with `|R_i| ≤ E` such that `(U, V, W) = S + A (U, V, W) + R`, where `S` is the source
`skAtSource` and `A` the AT matrix `skAtMatrix`. -/
theorem sk_cov_system (N : ℕ) (β q h : ℝ)
    (hfix : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 2 ∂(gaussianReal 0 1) = q)
    (qhat : ℝ)
    (hqhat : ∫ z : ℝ, Real.tanh (β * Real.sqrt q * z + h) ^ 4 ∂(gaussianReal 0 1) = qhat)
    (hqhat01 : qhat ∈ Set.Icc (0 : ℝ) 1) (K₁ K₂ : ℝ) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (e : Option (Option (Fin 4)) ≃ Fin (4 + 2))
    (ν₂ : ((Fin 2 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₂ : ∀ Φ, ν₂ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 2 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 2 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₃ : ((Fin 3 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₃ : ∀ Φ, ν₃ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 3 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 3 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₄ : ((Fin 4 → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₄ : ∀ Φ, ν₄ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin 4 → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin 4 => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (ν₆ : ((Fin (4 + 2) → Fin (N + 1) → ℤˣ) → ℝ) → ℝ)
    (hν₆ : ∀ Φ, ν₆ Φ = ∫ g : FinPairs (N + 1) → ℝ, ∫ σ : Fin (4 + 2) → Fin (N + 1) → ℤˣ, Φ σ
      ∂(Measure.pi fun _ : Fin (4 + 2) => Measure.count.tilted fun a : Fin (N + 1) → ℤˣ =>
        (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs (N + 1), g p * (a p.val.1 : ℝ) * (a p.val.2 : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ))
      ∂(Measure.pi fun _ : FinPairs (N + 1) => gaussianReal 0 1))
    (hD2 : ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 2) ≤ K₁ / ((N : ℝ) + 1))
    (hD4 : ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) ^ 4) ≤ K₂ / ((N : ℝ) + 1) ^ 2)
    (E : ℝ)
    (hE : E = 2304 * β ^ 4 * Real.exp (256 * β ^ 2) *
        (Real.sqrt ((8 * K₁ + 8) / ((N : ℝ) + 1)) * Real.sqrt (K₂ / ((N : ℝ) + 1) ^ 2)) +
      32 * β ^ 2 * (72 * β ^ 2 * Real.exp (256 * β ^ 2) *
          (Real.sqrt ((8 * K₂ + 8) / ((N : ℝ) + 1) ^ 2) * Real.sqrt (K₁ / ((N : ℝ) + 1))) +
        (2 * ((K₁ + 1) / (2 * Real.sqrt ((N : ℝ) + 1))) / ((N : ℝ) + 1) +
          1 / ((N : ℝ) + 1) ^ 2)) +
      (N + 1 : ℝ)⁻¹ * (64 * β ^ 2 * Real.exp (144 * β ^ 2) *
        ((K₁ + 1) / (2 * Real.sqrt ((N : ℝ) + 1))))) :
    ∃ R : Fin 3 → ℝ,
      (![ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)),
         ν₃ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q)),
         ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q))] =
        skAtSource q qhat ((N : ℝ) + 1) +
          skAtMatrix (skCavityBCoef β q qhat 2) (skCavityBCoef β q qhat 1)
            (skCavityBCoef β q qhat 0) *ᵥ
          ![ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)),
            ν₃ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q)),
            ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q))] + R) ∧
      ∀ i, |R i| ≤ E := by
  have hsoR : Function.Injective (e : Option (Option (Fin 4)) → Fin (4 + 2)) := e.injective
  have hidinj : Function.Injective (fun r : Fin 4 => r) := fun _ _ h' => h'
  -- the value of the left side of a row: a class of the pair `(0, 1)` against `(a, c)`
  have hLHS : ∀ {a c : Fin 4}, a ≠ c →
      ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) *
          ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ a i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ c i : ℝ)) - q)) =
        if ((0 : Fin 4) = a ∧ (1 : Fin 4) = c) ∨ ((0 : Fin 4) = c ∧ (1 : Fin 4) = a) then
          ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q))
        else if (0 : Fin 4) = a ∨ (0 : Fin 4) = c ∨ (1 : Fin 4) = a ∨ (1 : Fin 4) = c then
          ν₃ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q))
        else
          ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q)) := fun {a c} hac => by
    have := sk_nu_overlap_class N β h q ν₂ hν₂ ν₃ hν₃ ν₄ hν₄ ν₄ hν₄ (fun r : Fin 4 => r) hidinj
      (p₁ := 0) (p₂ := 1) (r₁ := a) (r₂ := c) (by decide) hac
    exact this
  -- the sum over the replica families
  have hSum : ∀ {a c : Fin 4}, a ≠ c →
      ∑ j : SKCavityReplicaPair 4, skCavityReplicaPairWeight 4 j *
        (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences (0 : Fin 4) 1 j) *
          ν₆ (fun τ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (τ (e (some (some a))) i : ℝ)) ⬝ᵥ
              fun i : Fin (N + 1) => (τ (e (some (some c))) i : ℝ)) - q) *
            ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (τ (e (skCavityReplicaPairMap j).1) i : ℝ)) ⬝ᵥ
              fun i : Fin (N + 1) => (τ (e (skCavityReplicaPairMap j).2) i : ℝ)) - q))) =
      ∑ j : SKCavityReplicaPair 4, skCavityReplicaPairWeight 4 j *
        (skCavityBCoef β q qhat (skCavityReplicaPairCoincidences (0 : Fin 4) 1 j) *
          (if (some (some a) = (skCavityReplicaPairMap j).1 ∧
                some (some c) = (skCavityReplicaPairMap j).2) ∨
              (some (some a) = (skCavityReplicaPairMap j).2 ∧
                some (some c) = (skCavityReplicaPairMap j).1) then
            ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q))
          else if some (some a) = (skCavityReplicaPairMap j).1 ∨
              some (some a) = (skCavityReplicaPairMap j).2 ∨
              some (some c) = (skCavityReplicaPairMap j).1 ∨
              some (some c) = (skCavityReplicaPairMap j).2 then
            ν₃ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q))
          else
            ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q)))) := fun {a c} hac => by
    refine Finset.sum_congr rfl fun j _ => ?_
    have := sk_nu_overlap_class N β h q ν₂ hν₂ ν₃ hν₃ ν₄ hν₄ ν₆ hν₆
      (e : Option (Option (Fin 4)) → Fin (4 + 2))
      hsoR (p₁ := some (some a)) (p₂ := some (some c)) (r₁ := (skCavityReplicaPairMap j).1)
      (r₂ := (skCavityReplicaPairMap j).2)
      (fun h' => hac (Option.some.inj (Option.some.inj h'))) (skCavityReplicaPair_ne j)
    rw [this]
  have hrow : ∀ {a c : Fin 4}, a ≠ c → _ := fun {a c} hac =>
    sk_cov_row_bound N β q h hfix qhat hqhat hqhat01 K₁ K₂ hK₁ hK₂ e ν₂ hν₂ ν₄ hν₄ ν₆ hν₆
      hD2 hD4 hac E hE
  have r0 := hrow (a := 0) (c := 1) (by decide)
  have r1 := hrow (a := 0) (c := 2) (by decide)
  have r2 := hrow (a := 2) (c := 3) (by decide)
  rw [hLHS (by decide), hSum (by decide)] at r0 r1 r2
  have c0 : ((0 : Fin 4) = 0 ∧ (1 : Fin 4) = 1) ∨ ((0 : Fin 4) = 1 ∧ (1 : Fin 4) = 0) := by decide
  have c1 : ¬(((0 : Fin 4) = 0 ∧ (1 : Fin 4) = 2) ∨ ((0 : Fin 4) = 2 ∧ (1 : Fin 4) = 0)) := by
    decide
  have c1' : (0 : Fin 4) = 0 ∨ (0 : Fin 4) = 2 ∨ (1 : Fin 4) = 0 ∨ (1 : Fin 4) = 2 := by decide
  have c2 : ¬(((0 : Fin 4) = 2 ∧ (1 : Fin 4) = 3) ∨ ((0 : Fin 4) = 3 ∧ (1 : Fin 4) = 2)) := by
    decide
  have c2' : ¬((0 : Fin 4) = 2 ∨ (0 : Fin 4) = 3 ∨ (1 : Fin 4) = 2 ∨ (1 : Fin 4) = 3) := by
    decide
  rw [sk_row_sum_zero_j] at r0
  rw [sk_row_sum_one_j] at r1
  rw [sk_row_sum_two_j] at r2
  have k0 : skCavityBUnscaled q qhat (skCavityCoincidences (0 : Fin 4) 1 0 1) = 1 - q ^ 2 := by
    simp [skCavityBUnscaled, skCavityCoincidences]
  have k1 : skCavityBUnscaled q qhat (skCavityCoincidences (0 : Fin 4) 1 0 2) = q - q ^ 2 := by
    simp [skCavityBUnscaled, skCavityCoincidences]
  have k2 : skCavityBUnscaled q qhat (skCavityCoincidences (0 : Fin 4) 1 2 3) = qhat - q ^ 2 := by
    simp [skCavityBUnscaled, skCavityCoincidences]
  rw [k0] at r0
  rw [k1] at r1
  rw [k2] at r2
  refine ⟨![ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q)) - (1 - q ^ 2) / ((N : ℝ) + 1) -
        skAtRowZero (skCavityBCoef β q qhat 2) (skCavityBCoef β q qhat 1)
          (skCavityBCoef β q qhat 0) (ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i
            : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q))) (ν₃ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin
            (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q))) (ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin
            (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q))),
      ν₃ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q)) - (q - q ^ 2) / ((N : ℝ) + 1) -
        skAtRowOne (skCavityBCoef β q qhat 2) (skCavityBCoef β q qhat 1)
          (skCavityBCoef β q qhat 0) (ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i
            : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q))) (ν₃ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin
            (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q))) (ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin
            (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q))),
      ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q)) - (qhat - q ^ 2) / ((N : ℝ) + 1) -
        skAtRowTwo (skCavityBCoef β q qhat 2) (skCavityBCoef β q qhat 1)
          (skCavityBCoef β q qhat 0) (ν₂ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0 i
            : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q))) (ν₃ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin
            (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 0
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 2 i : ℝ)) - q))) (ν₄ (fun σ => ((N + 1 : ℝ)⁻¹ * ((fun i : Fin
            (N + 1) => (σ 0 i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 1 i : ℝ)) - q) * ((N + 1 : ℝ)⁻¹ * ((fun i : Fin (N + 1) => (σ 2
            i : ℝ)) ⬝ᵥ
          fun i : Fin (N + 1) => (σ 3 i : ℝ)) - q)))], ?_, ?_⟩
  · exact sk_at_vec_eq _ _ _ q qhat _ _ _ _
  · intro i
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, skAtRowZero]
      rw [inv_mul_eq_div] at r0
      exact r0
    · simp only [Fin.mk_one, Matrix.cons_val_one, skAtRowOne]
      rw [inv_mul_eq_div] at r1
      exact r1
    · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
        skAtRowTwo]
      rw [inv_mul_eq_div] at r2
      exact r2

end RowBound

section Solve

/-- Algebra of the difference of two resolvent-type fractions. -/
theorem frac_sub_half (c₂ d D₁ D₂ M n : ℝ) (hM : M ≠ 0) (hD₁ : D₁ ≠ 0) (hD₂ : D₂ ≠ 0)
    (hnum : c₂ * D₂ - d * D₁ = n) :
    (c₂ / (M * D₁) - d / (M * D₂)) / 2 = n / (2 * (M * D₁ * D₂)) := by
  rw [← hnum]
  field_simp


/-- `|x / D| ≤ b / δ` if `|x| ≤ b` and `0 < δ ≤ |D|`; the denominator may be negative. -/
theorem abs_div_le_div_of_le_abs {x D b δ : ℝ} (hδ : 0 < δ) (hD : δ ≤ |D|) (hx : |x| ≤ b) :
    |x / D| ≤ b / δ := by
  rw [abs_div]
  exact div_le_div₀ ((abs_nonneg _).trans hx) hx hδ hD

/-- `|x / D| ≤ (4/3) b` if `D ≥ 3/4` and `|x| ≤ b`. -/
theorem abs_div_le_four_thirds {x D b : ℝ} (hD : 3 / 4 ≤ D) (hx : |x| ≤ b) :
    |x / D| ≤ 4 / 3 * b :=
  (abs_div_le_div_of_le_abs (by norm_num) (hD.trans (le_abs_self D)) hx).trans_eq (by ring)

/-- The error bookkeeping of the covariance system: with `a = ρ₁/D₁`, `b' = (ρ₁/D₁ - ρ₂/D₂)/2`
and `w = (b₀ a + g b' + R₂)/D₂`, `D_i ≥ 3/4`, `|R_i| ≤ E`, `|b₀| ≤ 1/4`, `|g| ≤ 3/2`, one has
`|a| ≤ 16E/3`, `|b'| ≤ 8E` and `|w| ≤ 20E`. -/
theorem at_error_bound {a b' w D₁ D₂ b₀ g R₀ R₁ R₂ E : ℝ} (hD₁ : 3 / 4 ≤ D₁) (hD₂ : 3 / 4 ≤ D₂)
    (hR₀ : |R₀| ≤ E) (hR₁ : |R₁| ≤ E) (hR₂ : |R₂| ≤ E) (hb₀ : |b₀| ≤ 1 / 4) (hg : |g| ≤ 3 / 2)
    (ha : a = (R₀ - 2 * R₁ + R₂) / D₁)
    (hb : b' = ((R₀ - 2 * R₁ + R₂) / D₁ - (R₀ - 4 * R₁ + 3 * R₂) / D₂) / 2)
    (hw : w = (b₀ * a + g * b' + R₂) / D₂) :
    |a| ≤ 16 / 3 * E ∧ |b'| ≤ 8 * E ∧ |w| ≤ 20 * E := by
  have hE : 0 ≤ E := (abs_nonneg _).trans hR₀
  have hR : ∀ i : Fin 3, |![R₀, R₁, R₂] i| ≤ E := fun i => by fin_cases i <;> assumption
  have hρ1 : |R₀ - 2 * R₁ + R₂| ≤ 4 * E := by
    have h := Weights.abs_weighted_sum_le ![1, -2, 1] _ hR
    simp only [Fin.sum_univ_three] at h
    norm_num at h
    convert h using 2
  have hρ2 : |R₀ - 4 * R₁ + 3 * R₂| ≤ 8 * E := by
    have h := Weights.abs_weighted_sum_le ![1, -4, 3] _ hR
    simp only [Fin.sum_univ_three] at h
    norm_num at h
    convert h using 2
  have hα' : |a| ≤ 16 / 3 * E := by
    rw [ha]; exact (abs_div_le_four_thirds hD₁ hρ1).trans (by linarith)
  have hB' : |b'| ≤ 8 * E := by
    rw [hb]
    have a1 := abs_le.1 (abs_div_le_four_thirds hD₁ hρ1)
    have a2 := abs_le.1 (abs_div_le_four_thirds hD₂ hρ2)
    rw [abs_le]; constructor <;> linarith
  have hnumW : |b₀ * a + g * b' + R₂| ≤ 43 / 3 * E := by
    have t1 : |b₀ * a| ≤ 1 / 4 * (16 / 3 * E) := by
      rw [abs_mul]; exact mul_le_mul hb₀ hα' (abs_nonneg _) (by norm_num)
    have t2 : |g * b'| ≤ 3 / 2 * (8 * E) := by
      rw [abs_mul]; exact mul_le_mul hg hB' (abs_nonneg _) (by norm_num)
    have a1 := abs_le.1 t1; have a2 := abs_le.1 t2; have a3 := abs_le.1 hR₂
    rw [abs_le]; constructor <;> linarith
  refine ⟨hα', hB', ?_⟩
  rw [hw]; exact (abs_div_le_four_thirds hD₂ hnumW).trans (by linarith)


/-- **Solving the covariance system (the algebra of Theorem 1.8.12).**  Let
`U = (1 - q²)/M + b(2) U - 4 b(1) V + 3 b(0) W + R₀`, ... be the three covariance equations with
`b(c) = β² (𝔼 tanh^{4-2c} - q²)`, `|R_i| ≤ E`, `4 β² < 1`, `0 ≤ q̂ ≤ q ≤ 1`.
Put `c₂ = 1 - 2q + q̂`,
`d = 1 - 4q + 3q̂`, `D₁ = 1 - β² c₂`, `D₂ = 1 - β² d`, and
`A² = c₂/(M D₁)`, `B² = (q - q̂)/(M D₁ D₂)`,
`C² = ((q̂ - q²)/M + β²(q̂ - q²) A² + 2β²(2q + q² - 3q̂) B²)/D₂`.  Then
`|U - (A² + 2B² + C²)|`, `|V - (B² + C²)|`, `|W - C²|` are all at most `44 E`. -/
theorem sk_at_scalar_solution (β q qhat M U V W R₀ R₁ R₂ E : ℝ) (hM : 0 < M)
    (hβ : 4 * β ^ 2 < 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hqh0 : 0 ≤ qhat) (hqhq : qhat ≤ q)
    (hR₀ : |R₀| ≤ E) (hR₁ : |R₁| ≤ E) (hR₂ : |R₂| ≤ E)
    (h₀ : U = (1 - q ^ 2) / M + (β ^ 2 * (1 - q ^ 2) * U - 4 * (β ^ 2 * (q - q ^ 2)) * V +
      3 * (β ^ 2 * (qhat - q ^ 2)) * W) + R₀)
    (h₁ : V = (q - q ^ 2) / M + (β ^ 2 * (q - q ^ 2) * U +
      (β ^ 2 * (1 - q ^ 2) - 2 * (β ^ 2 * (q - q ^ 2)) - 3 * (β ^ 2 * (qhat - q ^ 2))) * V +
      (6 * (β ^ 2 * (qhat - q ^ 2)) - 3 * (β ^ 2 * (q - q ^ 2))) * W) + R₁)
    (h₂ : W = (qhat - q ^ 2) / M + (β ^ 2 * (qhat - q ^ 2) * U +
      (4 * (β ^ 2 * (q - q ^ 2)) - 8 * (β ^ 2 * (qhat - q ^ 2))) * V +
      (β ^ 2 * (1 - q ^ 2) - 8 * (β ^ 2 * (q - q ^ 2)) + 10 * (β ^ 2 * (qhat - q ^ 2))) * W) +
      R₂) :
    let c₂ := 1 - 2 * q + qhat
    let d := 1 - 4 * q + 3 * qhat
    let D₁ := 1 - β ^ 2 * c₂
    let D₂ := 1 - β ^ 2 * d
    let A2 := c₂ / (M * D₁)
    let B2 := (q - qhat) / (M * D₁ * D₂)
    let C2 := ((qhat - q ^ 2) / M + β ^ 2 * (qhat - q ^ 2) * A2 +
      2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qhat) * B2) / D₂
    |U - (A2 + 2 * B2 + C2)| ≤ 44 * E ∧ |V - (B2 + C2)| ≤ 44 * E ∧ |W - C2| ≤ 44 * E := by
  intro c₂ d D₁ D₂ A2 B2 C2
  have hE : 0 ≤ E := (abs_nonneg _).trans hR₀
  have hb2 : β ^ 2 ≤ 1 / 4 := by linarith
  have hb0 : 0 ≤ β ^ 2 := sq_nonneg β
  have hD₁ : 3 / 4 ≤ D₁ := by
    change 3 / 4 ≤ 1 - β ^ 2 * (1 - 2 * q + qhat)
    nlinarith only [hb2, hb0, hq0, hq1, hqh0, hqhq]
  have hD₂ : 3 / 4 ≤ D₂ := by
    change 3 / 4 ≤ 1 - β ^ 2 * (1 - 4 * q + 3 * qhat)
    nlinarith only [hb2, hb0, hq0, hq1, hqh0, hqhq]
  have hD₁0 : 0 < D₁ := by linarith
  have hD₂0 : 0 < D₂ := by linarith
  have div_sol : ∀ {D x y ρ : ℝ}, D ≠ 0 → D * x = y + ρ → x - y / D = ρ / D :=
    fun {D x y ρ} hD h' => by field_simp; linarith
  set α : ℝ := U - 2 * V + W with hα
  set γ : ℝ := U - 4 * V + 3 * W with hγ
  set B : ℝ := V - W with hB
  have e1 : D₁ * α = c₂ / M + (R₀ - 2 * R₁ + R₂) := by
    change (1 - β ^ 2 * (1 - 2 * q + qhat)) * (U - 2 * V + W) = (1 - 2 * q + qhat) / M +
      (R₀ - 2 * R₁ + R₂)
    linear_combination h₀ - 2 * h₁ + h₂
  have e2 : D₂ * γ = d / M + (R₀ - 4 * R₁ + 3 * R₂) := by
    change (1 - β ^ 2 * (1 - 4 * q + 3 * qhat)) * (U - 4 * V + 3 * W) = (1 - 4 * q + 3 * qhat) / M +
      (R₀ - 4 * R₁ + 3 * R₂)
    linear_combination h₀ - 4 * h₁ + 3 * h₂
  set b0 : ℝ := β ^ 2 * (qhat - q ^ 2) with hb0def
  set g : ℝ := 2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qhat) with hg
  have e3 : D₂ * W = (qhat - q ^ 2) / M + b0 * α + g * B + R₂ := by
    change (1 - β ^ 2 * (1 - 4 * q + 3 * qhat)) * W = (qhat - q ^ 2) / M +
      β ^ 2 * (qhat - q ^ 2) * (U - 2 * V + W) +
      2 * β ^ 2 * (2 * q + q ^ 2 - 3 * qhat) * (V - W) + R₂
    linear_combination h₂
  have hαA : α - A2 = (R₀ - 2 * R₁ + R₂) / D₁ := by
    have := div_sol hD₁0.ne' e1
    simpa [A2, div_div] using this
  have hγA : γ - d / (M * D₂) = (R₀ - 4 * R₁ + 3 * R₂) / D₂ := by
    have := div_sol hD₂0.ne' e2
    simpa [div_div] using this
  have hαγ : α - γ = 2 * B := by simp only [hα, hγ, hB]; ring
  have hB2 : (A2 - d / (M * D₂)) / 2 = B2 := by
    have hnum : c₂ * D₂ - d * D₁ = 2 * (q - qhat) := by
      simp only [D₁, D₂, c₂, d]; ring
    have := frac_sub_half c₂ d D₁ D₂ M (2 * (q - qhat)) hM.ne' hD₁0.ne' hD₂0.ne' hnum
    rw [show A2 = c₂ / (M * D₁) from rfl, this]
    simp only [B2]
    field_simp
  have hBB : B - B2 = ((R₀ - 2 * R₁ + R₂) / D₁ - (R₀ - 4 * R₁ + 3 * R₂) / D₂) / 2 := by
    rw [← hB2]
    linarith only [hαγ, hαA, hγA]
  have hWC : W - C2 = (b0 * (α - A2) + g * (B - B2) + R₂) / D₂ := by
    have := div_sol (D := D₂) (x := W) (y := (qhat - q ^ 2) / M + b0 * A2 + g * B2)
      (ρ := b0 * (α - A2) + g * (B - B2) + R₂) hD₂0.ne' (by linear_combination e3)
    simpa [C2, hb0def, hg] using this
  have hb0' : |b0| ≤ 1 / 4 := by
    rw [hb0def, abs_mul, abs_of_nonneg hb0]
    have : |qhat - q ^ 2| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith only [hq0, hq1, hqh0, hqhq]
    nlinarith only [this, hb2, hb0, abs_nonneg (qhat - q ^ 2)]
  have hg' : |g| ≤ 3 / 2 := by
    rw [hg, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hb0]
    have : |2 * q + q ^ 2 - 3 * qhat| ≤ 3 := by
      rw [abs_le]; constructor <;> nlinarith only [hq0, hq1, hqh0, hqhq]
    nlinarith only [this, hb2, hb0, abs_nonneg (2 * q + q ^ 2 - 3 * qhat)]
  obtain ⟨hα', hB', hW'⟩ := at_error_bound (a := α - A2) (b' := B - B2) (w := W - C2)
    hD₁ hD₂ hR₀ hR₁ hR₂ hb0' hg' hαA hBB hWC
  have hV : V - (B2 + C2) = (B - B2) + (W - C2) := by simp only [hB]; ring
  have hU : U - (A2 + 2 * B2 + C2) = (α - A2) + 2 * (B - B2) + (W - C2) := by
    simp only [hα, hB]; ring
  refine ⟨?_, ?_, hW'.trans (by linarith only [hE])⟩
  · rw [hU]
    have a1 := abs_le.1 hα'; have a2 := abs_le.1 hB'; have a3 := abs_le.1 hW'
    rw [abs_le]; constructor <;> linarith only [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, hE]
  · rw [hV]
    have a2 := abs_le.1 hB'; have a3 := abs_le.1 hW'
    rw [abs_le]; constructor <;> linarith only [a2.1, a2.2, a3.1, a3.2, hE]

end Solve

end SpinGlasses
