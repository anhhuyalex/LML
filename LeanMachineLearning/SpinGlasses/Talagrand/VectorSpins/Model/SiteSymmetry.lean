/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Cavity.DecoupledOverlap
public import LeanMachineLearning.SpinGlasses.Talagrand.SpinDecorrelation.SKSiteSymmetry
public import LeanMachineLearning.ForMathlib.Probability.GibbsSiteSymmetry
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.IntegrableOfBound

/-!
# Symmetry between sites for vector spins (Talagrand, proof of Theorem 1.12.1)

* At `t = 1` the cavity Hamiltonian (1.375) is the vector SK energy of the `N + 1` site system
  whose couplings are `g` (old pairs) and `g'` (pairs with the cavity site).
* Relabelling the sites relabels the couplings through `pairPerm`, so if the law of the couplings
  is invariant under `pairPerm`, the disorder-averaged `R`-replica Gibbs average of a functional
  `Θ` is unchanged when the sites of all replicas are permuted.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

variable {α D : Type*} [MeasurableSpace α] [Fintype D]

/-- Relabelling the sites of the vector SK energy: the energy with couplings `g ∘ (pairPerm π).symm`
at the configuration `σ` is the energy with couplings `g` at the relabelled configuration
`σ ∘ π`. -/
theorem skVectorEnergy_comp_pairPerm {M : ℕ} (β : ℝ) (π : Equiv.Perm (Fin M))
    (g : FinPairs M → ℝ) (σ : Fin M → D → ℝ) :
    skVectorEnergy M β (g ∘ (pairPerm π).symm) σ = skVectorEnergy M β g (fun i => σ (π i)) := by
  rw [skVectorEnergy_eq_sum_components, skVectorEnergy_eq_sum_components]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  have := sum_pairs_pairPerm π g (fun i => σ i u)
  simp only [Function.comp_apply]
  exact this.symm

omit [MeasurableSpace α] in
/-- **The cavity Hamiltonian at `t = 1` is the `(N+1)`-site vector SK energy** of the couplings
`g`, `g'` assembled into one coupling family on pairs of `N + 1` sites. -/
theorem skVectorCavityEnergy_one {N : ℕ} (ξ : α → D → ℝ) (β : ℝ) (ρ q : D → D → ℝ)
    (gt : FinPairs (N + 1) → ℝ) (Y : D → ℝ) (σ : Fin (N + 1) → α) :
    skVectorCavityEnergy ξ N β ρ q
      (fun p => gt ⟨(p.val.1.castSucc, p.val.2.castSucc),
        Fin.castSucc_lt_castSucc_iff.mpr p.property⟩)
      (fun i => gt ⟨(i.castSucc, Fin.last N), Fin.castSucc_lt_last i⟩) Y 1 σ =
      skVectorEnergy (N + 1) β gt (fun i => ξ (σ i)) := by
  rw [skVectorEnergy_succ_cavity]
  unfold skVectorCavityEnergy
  simp only [Real.sqrt_one, one_mul, sub_self, Real.sqrt_zero, zero_mul, add_zero, mul_zero]
  rw [mul_add]
  congr 1
  · congr 1
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun p _ => by ring
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring

/-- The vector SK energy is jointly measurable in the couplings and the configuration. -/
theorem measurable_skVectorEnergy_joint {M : ℕ} (ξ : α → D → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (β : ℝ) :
    Measurable fun p : (FinPairs M → ℝ) × (Fin M → α) =>
      skVectorEnergy M β p.1 (fun i => ξ (p.2 i)) := by
  unfold skVectorEnergy
  refine measurable_const.mul (Finset.measurable_sum _ fun p _ => ?_)
  refine ((measurable_pi_apply p).comp measurable_fst).mul (Finset.measurable_sum _ fun u _ => ?_)
  exact ((hξ u).comp ((measurable_pi_apply _).comp measurable_snd)).mul
    ((hξ u).comp ((measurable_pi_apply _).comp measurable_snd))

/-- **Symmetry between sites for the disorder average of a replica Gibbs average.**  If the law of
the couplings is invariant under the relabelling `g ↦ g ∘ (pairPerm π).symm`, permuting the sites
of all replicas does not change `𝔼 ⟨Θ⟩`. -/
theorem integral_skVector_replica_perm {M : ℕ} {Ω R : Type*} [MeasurableSpace Ω] [Fintype R]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → D → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (β : ℝ) {P : Measure Ω} {gt : Ω → FinPairs M → ℝ}
    (hgt : Measurable gt)
    (hsym : ∀ π : Equiv.Perm (Fin M),
      Measure.map (fun ω => gt ω ∘ (pairPerm π).symm) P = Measure.map gt P)
    (π : Equiv.Perm (Fin M)) (Θ : (R → Fin M → α) → ℝ) (hΘ : Measurable Θ) :
    ∫ ω, ∫ σ : R → Fin M → α, Θ (fun r i => σ r (π i)) ∂(Measure.pi fun _ : R =>
        (Measure.pi fun _ : Fin M => μ).tilted (fun a => skVectorEnergy M β (gt ω)
          (fun i => ξ (a i)))) ∂P =
      ∫ ω, ∫ σ : R → Fin M → α, Θ σ ∂(Measure.pi fun _ : R =>
        (Measure.pi fun _ : Fin M => μ).tilted (fun a => skVectorEnergy M β (gt ω)
          (fun i => ξ (a i)))) ∂P := by
  set Φ : (FinPairs M → ℝ) → ℝ := fun g => ∫ σ : R → Fin M → α, Θ σ ∂(Measure.pi fun _ : R =>
    (Measure.pi fun _ : Fin M => μ).tilted (fun a => skVectorEnergy M β g
      (fun i => ξ (a i)))) with hΦ
  have hΦm : Measurable Φ :=
    measurable_integral_pi_tilted (μ := Measure.pi fun _ : Fin M => μ) (ι := R)
      (E := fun g a => skVectorEnergy M β g (fun i => ξ (a i)))
      (measurable_skVectorEnergy_joint ξ hξ β) hΘ
  have hinner : ∀ ω, ∫ σ : R → Fin M → α, Θ (fun r i => σ r (π i)) ∂(Measure.pi fun _ : R =>
      (Measure.pi fun _ : Fin M => μ).tilted (fun a => skVectorEnergy M β (gt ω)
        (fun i => ξ (a i)))) = Φ (gt ω ∘ (pairPerm π.symm).symm) := by
    intro ω
    rw [integral_pi_tilted_comp_perm]
    simp only [hΦ, skVectorEnergy_comp_pairPerm]
  have hφ : AEMeasurable (fun ω => gt ω ∘ (pairPerm π.symm).symm) P :=
    (measurable_pi_iff.2 fun p => (measurable_pi_apply _).comp hgt).aemeasurable
  simp_rw [hinner]
  rw [← integral_map hφ hΦm.aestronglyMeasurable, hsym π.symm,
    integral_map hgt.aemeasurable hΦm.aestronglyMeasurable]

/-- The Gibbs measure of the `(N+1)`-site vector SK energy is a probability measure. -/
theorem isProbabilityMeasure_tilted_skVectorEnergy (μ : Measure α) [IsProbabilityMeasure μ]
    (ξ : α → D → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u)) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r) (N : ℕ) (β : ℝ) (g : FinPairs (N + 1) → ℝ) :
    IsProbabilityMeasure ((Measure.pi fun _ : Fin (N + 1) => μ).tilted
      (fun a => skVectorEnergy (N + 1) β g (fun i => ξ (a i)))) :=
  isProbabilityMeasure_tilted_skVectorEnergy_of_sum_sq_le μ ξ hξ r hr hbound (N + 1) β g

/-- The disorder average of a bounded measurable function of the replicas has an integrable Gibbs
average for the `(N+1)`-site vector SK energy. -/
theorem integrable_integral_skVectorEnergy {N d : ℕ} {Ω R : Type*} [MeasurableSpace Ω] [Fintype R]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    {P : Measure Ω} [IsProbabilityMeasure P] {gt : Ω → FinPairs (N + 1) → ℝ} (hgt : Measurable gt)
    (G : (R → Fin (N + 1) → α) → ℝ) (hG : Measurable G) (hGb : ∃ M, ∀ x, |G x| ≤ M) :
    Integrable (fun ω => ∫ x, G x ∂(Measure.pi fun _ : R =>
      (Measure.pi fun _ : Fin (N + 1) => μ).tilted
        (fun x => skVectorEnergy (N + 1) β (gt ω) (fun i => ξ (x i))))) P :=
  integrable_integral_pi_tilted (ι := R) (P := P) (μ := Measure.pi fun _ : Fin (N + 1) => μ)
    (E := fun ω x => skVectorEnergy (N + 1) β (gt ω) (fun i => ξ (x i)))
    ((measurable_skVectorEnergy_joint ξ hξ β).comp (hgt.comp measurable_fst |>.prodMk
      measurable_snd))
    (fun ω => isProbabilityMeasure_tilted_skVectorEnergy μ ξ hξ (Nat.cast_nonneg d) hbound N β
      (gt ω)) hG hGb.choose_spec

/-- **Symmetry between sites** (Eq. (1.383)): for two replicas, `ν((R - T) (R - T)) =
ν(ε_last (R - T))` where `R - T = (N+1)⁻¹ ∑_i e_i` is the centered overlap and `e_i` the centered
product of the replica spins `a`, `b` at the site `i`. -/
theorem skVector_overlap_variance_eq_last_spin {N d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    {P : Measure Ω} [IsProbabilityMeasure P] {gt : Ω → FinPairs (N + 1) → ℝ}
    (hgt : Measurable gt)
    (hsym : ∀ π : Equiv.Perm (Fin (N + 1)),
      Measure.map (fun ω => gt ω ∘ (pairPerm π).symm) P = Measure.map gt P)
    (a b : Fin 2) (u v : Fin d) (T : ℝ) (hTb : |T| ≤ d) :
    ∫ ω, ∫ σ : Fin 2 → Fin (N + 1) → α,
        (((N : ℝ) + 1)⁻¹ * ∑ i, ξ (σ a i) u * ξ (σ b i) v - T) *
          (((N : ℝ) + 1)⁻¹ * ∑ i, ξ (σ a i) u * ξ (σ b i) v - T)
        ∂(Measure.pi fun _ : Fin 2 => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
          (fun x => skVectorEnergy (N + 1) β (gt ω) (fun i => ξ (x i)))) ∂P =
      ∫ ω, ∫ σ : Fin 2 → Fin (N + 1) → α,
        (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v - T) *
          (((N : ℝ) + 1)⁻¹ * ∑ i, ξ (σ a i) u * ξ (σ b i) v - T)
        ∂(Measure.pi fun _ : Fin 2 => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
          (fun x => skVectorEnergy (N + 1) β (gt ω) (fun i => ξ (x i)))) ∂P := by
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hM0 : ((N : ℝ) + 1) ≠ 0 := by positivity
  have hsp := abs_spin_mul_le ξ hr hbound
  -- the family of Gibbs measures
  set Q : Ω → Measure (Fin 2 → Fin (N + 1) → α) := fun ω => Measure.pi fun _ : Fin 2 =>
    (Measure.pi fun _ : Fin (N + 1) => μ).tilted
      (fun x => skVectorEnergy (N + 1) β (gt ω) (fun i => ξ (x i))) with hQ
  have : ∀ ω, IsProbabilityMeasure (Q ω) := fun ω => by
    have := isProbabilityMeasure_tilted_skVectorEnergy μ ξ hξ hr hbound N β (gt ω)
    exact inferInstance
  have hI : ∀ G : (Fin 2 → Fin (N + 1) → α) → ℝ, Measurable G → (∃ M, ∀ x, |G x| ≤ M) →
      Integrable (fun ω => ∫ x, G x ∂(Q ω)) P := fun G hG hGb =>
    integrable_integral_skVectorEnergy μ ξ hξ hbound β hgt G hG hGb
  -- the centered site products and the centered overlap
  have heM : ∀ s : Fin (N + 1), Measurable fun σ : Fin 2 → Fin (N + 1) → α =>
      ξ (σ a s) u * ξ (σ b s) v - T := fun s =>
    (((hξ u).comp ((measurable_pi_apply s).comp (measurable_pi_apply a))).mul
      ((hξ v).comp ((measurable_pi_apply s).comp (measurable_pi_apply b)))).sub measurable_const
  have heb : ∀ (s : Fin (N + 1)) (σ : Fin 2 → Fin (N + 1) → α),
      |ξ (σ a s) u * ξ (σ b s) v - T| ≤ d + d := fun s σ =>
    (abs_sub _ _).trans (add_le_add (hsp _ _ u v) hTb)
  have hHm : Measurable fun σ : Fin 2 → Fin (N + 1) → α =>
      ((N : ℝ) + 1)⁻¹ * ∑ i, ξ (σ a i) u * ξ (σ b i) v - T :=
    (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      ((hξ u).comp ((measurable_pi_apply i).comp (measurable_pi_apply a))).mul
        ((hξ v).comp ((measurable_pi_apply i).comp (measurable_pi_apply b))))).sub
      measurable_const
  have hHb : ∀ σ : Fin 2 → Fin (N + 1) → α,
      |((N : ℝ) + 1)⁻¹ * ∑ i, ξ (σ a i) u * ξ (σ b i) v - T| ≤ d + d := fun σ => by
    refine (abs_sub _ _).trans (add_le_add ?_ hTb)
    rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1))]
    calc ((N : ℝ) + 1)⁻¹ * |∑ i, ξ (σ a i) u * ξ (σ b i) v| ≤
          ((N : ℝ) + 1)⁻¹ * (((N : ℝ) + 1) * d) := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (by positivity))
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          refine (Finset.sum_le_sum fun i _ => hsp _ _ u v).trans ?_
          simp
      _ = d := by field_simp
  -- each site has the same average as the last one
  have hsite : ∀ s : Fin (N + 1),
      ∫ ω, ∫ σ, (((N : ℝ) + 1)⁻¹ * ∑ i, ξ (σ a i) u * ξ (σ b i) v - T) *
        (ξ (σ a s) u * ξ (σ b s) v - T) ∂(Q ω) ∂P =
      ∫ ω, ∫ σ, (((N : ℝ) + 1)⁻¹ * ∑ i, ξ (σ a i) u * ξ (σ b i) v - T) *
        (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v - T) ∂(Q ω) ∂P := by
    intro s
    have key := integral_skVector_replica_perm (R := Fin 2) μ ξ hξ β hgt hsym
      (Equiv.swap s (Fin.last N))
      (fun σ => (((N : ℝ) + 1)⁻¹ * ∑ i, ξ (σ a i) u * ξ (σ b i) v - T) *
        (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v - T))
      (hHm.mul (heM (Fin.last N)))
    have hpt : ∀ σ : Fin 2 → Fin (N + 1) → α,
        (((N : ℝ) + 1)⁻¹ * ∑ i, ξ (σ a (Equiv.swap s (Fin.last N) i)) u *
          ξ (σ b (Equiv.swap s (Fin.last N) i)) v - T) *
        (ξ (σ a (Equiv.swap s (Fin.last N) (Fin.last N))) u *
          ξ (σ b (Equiv.swap s (Fin.last N) (Fin.last N))) v - T) =
        (((N : ℝ) + 1)⁻¹ * ∑ i, ξ (σ a i) u * ξ (σ b i) v - T) *
          (ξ (σ a s) u * ξ (σ b s) v - T) := fun σ => by
      rw [Equiv.swap_apply_right]
      congr 3
      exact Equiv.sum_comp (Equiv.swap s (Fin.last N)) fun i => ξ (σ a i) u * ξ (σ b i) v
    simp only [hpt] at key
    exact key
  -- the centered overlap is the average of the centered site products
  have hH : ∀ σ : Fin 2 → Fin (N + 1) → α,
      (((N : ℝ) + 1)⁻¹ * ∑ i, ξ (σ a i) u * ξ (σ b i) v - T) *
        (((N : ℝ) + 1)⁻¹ * ∑ i, ξ (σ a i) u * ξ (σ b i) v - T) =
      ((N : ℝ) + 1)⁻¹ * ∑ s : Fin (N + 1), (((N : ℝ) + 1)⁻¹ * ∑ i, ξ (σ a i) u * ξ (σ b i) v - T) *
        (ξ (σ a s) u * ξ (σ b s) v - T) := fun σ => by
    have hsum : ∑ s : Fin (N + 1), (ξ (σ a s) u * ξ (σ b s) v - T) =
        ∑ i, ξ (σ a i) u * ξ (σ b i) v - ((N : ℝ) + 1) * T := by
      rw [Finset.sum_sub_distrib]
      simp
    rw [← Finset.mul_sum, hsum]
    field_simp
  simp_rw [hH]
  have hlin := integral_integral_finset_sum P Q Finset.univ
    (fun s σ => (((N : ℝ) + 1)⁻¹ * ∑ i, ξ (σ a i) u * ξ (σ b i) v - T) *
      (ξ (σ a s) u * ξ (σ b s) v - T))
    (fun s _ ω => integrable_of_measurable_bound (hHm.mul (heM s))
      (fun σ => by
        rw [abs_mul]
        exact mul_le_mul (hHb σ) (heb s σ) (abs_nonneg _) (add_nonneg hr hr)))
    (fun s _ => hI _ (hHm.mul (heM s))
      ⟨(d + d) * (d + d), fun σ => by
        rw [abs_mul]; exact mul_le_mul (hHb σ) (heb s σ) (abs_nonneg _) (add_nonneg hr hr)⟩)
  simp_rw [integral_const_mul]
  rw [hlin]
  simp_rw [hsite]
  have hcomm : ∫ ω, ∫ σ, (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v - T) *
        (((N : ℝ) + 1)⁻¹ * ∑ i, ξ (σ a i) u * ξ (σ b i) v - T) ∂(Q ω) ∂P =
      ∫ ω, ∫ σ, (((N : ℝ) + 1)⁻¹ * ∑ i, ξ (σ a i) u * ξ (σ b i) v - T) *
        (ξ (σ a (Fin.last N)) u * ξ (σ b (Fin.last N)) v - T) ∂(Q ω) ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
    exact mul_comm _ _
  rw [hcomm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

end SpinGlasses
