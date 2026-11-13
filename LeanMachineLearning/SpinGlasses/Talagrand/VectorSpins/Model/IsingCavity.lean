/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Model.Ising
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Cavity.Derivative
public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Cavity.Comparison
public import LeanMachineLearning.SpinGlasses.Talagrand.CavityMethod.SKCavityOuterDerivative
public import LeanMachineLearning.SpinGlasses.Talagrand.GaussianFluctuation.SKLastSpinGaussian
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.FiniteReplicaTiltedShift
public import LeanMachineLearning.ForMathlib.MeasureTheory.Integral.TripleProductMul
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianVector
public import LeanMachineLearning.ForMathlib.Probability.Moments.GaussianPiLinearForm
public import LeanMachineLearning.ForMathlib.Probability.GibbsReplicaProduct
public import LeanMachineLearning.ForMathlib.Analysis.SpecialFunctions.TrigSquareParam

/-!
# Derivative-level bridge from vector cavity to scalar cavity

This file formalizes the bridge between the vector cavity derivative of Section 1.12
(`hasDerivAt_skVectorCavityAverage`) and the scalar SK cavity derivative of Section 1.6
(`hasDerivAt_integral_sk_cavity_path_square`).

For one-component spins ($d = 1$), spin map $\xi_1(\varepsilon) = \varepsilon \in \mathbb{R}$,
$\rho = 1$, and tilted base measure $\mu_h = \text{count}.\text{tilted}(h \cdot \varepsilon)$:
1. The vector Hamiltonian plus the one-site field equals the scalar cavity energy $E(s)$
   (for $s = \arccos \sqrt{t}$) plus the configuration-independent constant
   $(1 - t) \frac{\beta^2}{2}(1 - q)$ (`skVectorCavityEnergy_ising_eq`).
2. At the replica integral level, this constant cancels exactly, identifying the vector and
   scalar Gibbs averages for every fixed disorder realization (`skVectorCavityGibbs_ising_eq`).
3. Gaussian noise on the scalar disorder space satisfies the hypotheses of Proposition 1.12.4
   (`skVectorCavityGaussianData_disorderLaw_ising`).
4. By Fubini, the disorder expectation functions coincide on $(0, 1)$
   (`skVectorCavityAverage_ising_eq`).
5. Transferring the derivative along `HasDerivAt.congr_of_eventuallyEq` establishes the
   derivative of the scalar cavity path from the vector engine
   (`hasDerivAt_ising_cavity_path_of_vector`), and `HasDerivAt.unique` confirms that the
   vector derivative value equals the scalar derivative value.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Topology

namespace SpinGlasses

local notation "ξ₁" => fun (ε : ℤˣ) (_ : Fin 1) => ((ε : ℤ) : ℝ)

/-! ### S1. Spin dictionary -/

theorem measurable_ising_spin (u : Fin 1) : Measurable (fun ε : ℤˣ => ξ₁ ε u) :=
  measurable_of_finite _

theorem ising_spin_sq_sum_le_one (ε : ℤˣ) : ∑ u : Fin 1, (ξ₁ ε u) ^ 2 ≤ 1 := by
  simp only [Fin.sum_univ_one, units_cast_sq, le_refl]

/-! ### S2. Energy dictionary -/

/-- **The cavity energy dictionary**: for one-component spins and `s = arccos √t`,
the vector cavity Hamiltonian plus the one-site field matches the scalar cavity energy
up to the configuration-independent constant `(1 - t) * (β² / 2 * (1 - q))`. -/
theorem skVectorCavityEnergy_ising_eq (N : ℕ) (β q h t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (g' : FinPairs N → ℝ) (ω : (Fin N → ℝ) × ℝ) (σ : Fin (N + 1) → ℤˣ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    skVectorCavityEnergy ξ₁ N β (fun _ _ => 1) (fun _ _ => q) g' ω.1
        (fun _ => β * Real.sqrt q * ω.2) t σ +
      ∑ i : Fin (N + 1), h * ((σ i : ℤ) : ℝ) =
    E (Real.arccos (Real.sqrt t)) g' ω σ + (1 - t) * (β ^ 2 / 2 * (1 - q)) := by
  intro B E
  have hcos : Real.cos (Real.arccos (Real.sqrt t)) = Real.sqrt t := by
    have h1 : Real.sqrt t ≤ 1 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt ht1
    have h2 : -1 ≤ Real.sqrt t := by
      linarith [Real.sqrt_nonneg t]
    exact Real.cos_arccos h2 h1
  have hsin : Real.sin (Real.arccos (Real.sqrt t)) = Real.sqrt (1 - t) := by
    rw [Real.sin_arccos, Real.sq_sqrt ht0]
  unfold skVectorCavityEnergy
  simp only [Fin.sum_univ_one]
  dsimp [E, B]
  rw [hcos, hsin]
  have hsq : ((σ (Fin.last N) : ℤ) : ℝ) * ((σ (Fin.last N) : ℤ) : ℝ) = 1 := by
    rw [← sq, units_cast_sq]
  rw [hsq]
  have hfield : (∑ i : Fin (N + 1), h * ((σ i : ℤ) : ℝ)) =
      h * ∑ i : Fin (N + 1), ((σ i : ℤ) : ℝ) := by
    rw [Finset.mul_sum]
  rw [hfield]
  simp only [mul_assoc]
  set Sp : ℝ := ∑ p : FinPairs N, g' p * (((σ p.val.1.castSucc : ℤ) : ℝ) *
    ((σ p.val.2.castSucc : ℤ) : ℝ))
  set Si : ℝ := ∑ i : Fin N, ω.1 i * ((σ i.castSucc : ℤ) : ℝ)
  set Sh : ℝ := ∑ i : Fin (N + 1), ((σ i : ℤ) : ℝ)
  ring

/-! ### S3. Gibbs-average dictionary -/

/-- **Pointwise equality of replica Gibbs averages**: for every fixed disorder configuration,
the vector replica average under `μ_h` equals the scalar replica average under counting
measure. -/
theorem skVectorCavityGibbs_ising_eq {R : Type*} [Fintype R] (N : ℕ) (β q h t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (g' : FinPairs N → ℝ) (ω : (Fin N → ℝ) × ℝ)
    (Ψ : (R → Fin (N + 1) → ℤˣ) → ℝ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    ∫ σ, Ψ σ ∂(Measure.pi fun _ : R =>
      (Measure.pi fun _ : Fin (N + 1) =>
        Measure.count.tilted (fun ε : ℤˣ => h * ((ε : ℤ) : ℝ))).tilted
          (skVectorCavityEnergy ξ₁ N β (fun _ _ => 1) (fun _ _ => q) g' ω.1
            (fun _ => β * Real.sqrt q * ω.2) t)) =
      ∫ σ, Ψ σ ∂(Measure.pi fun _ : R => Measure.count.tilted
        (E (Real.arccos (Real.sqrt t)) g' ω)) := by
  intro B E
  have htilt : (Measure.pi fun _ : Fin (N + 1) =>
        Measure.count.tilted (fun ε : ℤˣ => h * ((ε : ℤ) : ℝ))).tilted
          (skVectorCavityEnergy ξ₁ N β (fun _ _ => 1) (fun _ _ => q) g' ω.1
            (fun _ => β * Real.sqrt q * ω.2) t) =
      Measure.count.tilted (fun σ => E (Real.arccos (Real.sqrt t)) g' ω σ +
        (1 - t) * (β ^ 2 / 2 * (1 - q))) := by
    rw [tilted_pi_count_tilted]
    congr 1
    funext σ
    rw [add_comm]
    exact skVectorCavityEnergy_ising_eq N β q h t ht0 ht1 g' ω σ
  simp_rw [htilt]
  exact integral_pi_count_tilted_add_const _ _ Ψ


/-! ### S4. Gaussian disorder data -/

/-- **Gaussian disorder data on the scalar space**: the product Gaussian measure on
`(FinPairs N → ℝ) × ((Fin N → ℝ) × ℝ)` satisfies the joint Gaussianity and covariance
hypotheses of `SKVectorCavityGaussianData` with `d = 1` and `Y_u = β √q ω₂.2`. -/
theorem skVectorCavityGaussianData_disorderLaw_ising (N : ℕ) (β q : ℝ) (hq : 0 ≤ q) :
    SKVectorCavityGaussianData
      ((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
        ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)))
      N 1 β (fun _ _ => q)
      (fun p ω => ω.1 p)
      (fun i ω => ω.2.1 i)
      (fun _ ω => β * Real.sqrt q * ω.2.2) := by
  have h1 : HasGaussianLaw (fun x : FinPairs N → ℝ => x)
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1) :=
    isGaussian_pi_gaussianReal.hasGaussianLaw_id
  have h2a : HasGaussianLaw (fun x : Fin N → ℝ => x)
      (Measure.pi fun _ : Fin N => gaussianReal 0 1) :=
    isGaussian_pi_gaussianReal.hasGaussianLaw_id
  have h2b_real : HasGaussianLaw (fun z : ℝ => z) (gaussianReal 0 1) :=
    isGaussian_gaussianReal 0 1 |>.hasGaussianLaw_id
  let L : ℝ →L[ℝ] (Fin 1 → ℝ) := ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℝ ℝ
  have h2b : HasGaussianLaw (fun z (_ : Fin 1) => z) (gaussianReal 0 1) :=
    h2b_real.map_fun L
  have h2_joint := HasGaussianLaw.sumElim_prod_of_independent h2a h2b
    measurable_id (Measurable.of_eval fun _ => measurable_id)
  let c : Fin N ⊕ Fin 1 → ℝ := Sum.elim (fun _ => 1) (fun _ => β * Real.sqrt q)
  have h2_scaled := h2_joint.reindex_mul id c
  have h2_m : Measurable (fun z : (Fin N → ℝ) × ℝ => fun s : Fin N ⊕ Fin 1 =>
      c s * Sum.elim (fun a => z.1 a) (fun b => z.2) (id s)) := by
    refine Measurable.of_eval fun s => ?_
    rcases s with i | u
    · simp only [c, Sum.elim_inl, id_eq, one_mul]
      exact (measurable_pi_apply i).comp measurable_fst
    · simp only [c, Sum.elim_inr, id_eq]
      exact measurable_const.mul measurable_snd
  have h_all := HasGaussianLaw.sumElim_prod_of_independent h1 h2_scaled measurable_id h2_m
  let e : (FinPairs N ⊕ Fin N) ⊕ Fin 1 → FinPairs N ⊕ (Fin N ⊕ Fin 1) := fun k =>
    match k with
    | .inl (.inl p) => .inl p
    | .inl (.inr i) => .inr (.inl i)
    | .inr u => .inr (.inr u)
  have h_final := h_all.reindex e
  have hG : HasGaussianLaw (fun ω : (FinPairs N → ℝ) × ((Fin N → ℝ) × ℝ) =>
      fun k : (FinPairs N ⊕ Fin N) ⊕ Fin 1 =>
        Sum.elim (Sum.elim (fun p => ω.1 p) fun i => ω.2.1 i)
          (fun _ => β * Real.sqrt q * ω.2.2) k)
      ((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
        ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) := by
    convert h_final using 1
    ext ω k
    rcases k with (p | i) | u <;> simp [c, e]
  refine ⟨hG, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun p => (measurable_pi_apply p).comp measurable_fst
  · exact fun i => ((measurable_pi_apply i).comp measurable_fst).comp measurable_snd
  · exact fun u => measurable_const.mul (measurable_snd.comp measurable_snd)
  · intro k l
    rcases k with p | i <;> rcases l with p' | i' <;> dsimp only [Sum.elim_inl, Sum.elim_inr]
    · refine (integral_prod_prod_eq_mul _ (fun g => g p * g p') (fun _ => 1) (fun _ => 1)
        fun ω => by ring).trans ?_
      simp [integral_pi_gaussianReal_coord_mul]
    · refine (integral_prod_prod_eq_mul _ (fun g => g p) (fun g' => g' i') (fun _ => 1)
        fun ω => by ring).trans ?_
      simp [integral_pi_gaussianReal_coord]
    · refine (integral_prod_prod_eq_mul _ (fun g => g p') (fun g' => g' i) (fun _ => 1)
        fun ω => by ring).trans ?_
      simp [integral_pi_gaussianReal_coord]
    · refine (integral_prod_prod_eq_mul _ (fun _ => 1) (fun g' => g' i * g' i') (fun _ => 1)
        fun ω => by ring).trans ?_
      simp [integral_pi_gaussianReal_coord_mul]
  · intro u v
    refine (integral_prod_prod_eq_mul _ (fun _ => 1) (fun _ => 1)
      (fun z => (β * Real.sqrt q * z) * (β * Real.sqrt q * z)) fun ω => by ring).trans ?_
    have hsq : (β * Real.sqrt q) ^ 2 = β ^ 2 * q := by rw [mul_pow, Real.sq_sqrt hq]
    have hz : ∫ z, (β * Real.sqrt q * z) * (β * Real.sqrt q * z) ∂(gaussianReal 0 1) =
        β ^ 2 * q := by
      have : (fun z : ℝ => (β * Real.sqrt q * z) * (β * Real.sqrt q * z)) =
          fun z => (β * Real.sqrt q) ^ 2 * z ^ 2 := funext fun z => by ring
      rw [this, integral_const_mul, integral_sq_gaussianReal_zero_one, mul_one, hsq]
    simp [hz]
  · intro k u
    rcases k with p | i <;> dsimp only [Sum.elim_inl, Sum.elim_inr]
    · refine (integral_prod_prod_eq_mul _ (fun g => g p) (fun _ => 1)
        (fun z => β * Real.sqrt q * z) fun ω => by ring).trans ?_
      simp [integral_pi_gaussianReal_coord]
    · refine (integral_prod_prod_eq_mul _ (fun _ => 1) (fun g' => g' i)
        (fun z => β * Real.sqrt q * z) fun ω => by ring).trans ?_
      simp [integral_pi_gaussianReal_coord]
  · intro p
    refine (integral_prod_prod_eq_mul _ (fun g => g p) (fun _ => 1) (fun _ => 1)
      fun ω => by ring).trans ?_
    simp [integral_pi_gaussianReal_coord]
  · intro i
    refine (integral_prod_prod_eq_mul _ (fun _ => 1) (fun g' => g' i) (fun _ => 1)
      fun ω => by ring).trans ?_
    simp [integral_pi_gaussianReal_coord]
  · intro u
    refine (integral_prod_prod_eq_mul _ (fun _ => 1) (fun _ => 1)
      (fun z => β * Real.sqrt q * z) fun ω => by ring).trans ?_
    have hz : ∫ z, β * Real.sqrt q * z ∂(gaussianReal 0 1) = 0 := by
      rw [integral_const_mul, integral_id_gaussianReal, mul_zero]
    simp [hz]

/-! ### S5. Integrability of replica Gibbs averages -/

/-- Integrability of vector cavity replica Gibbs averages under finite disorder measures. -/
theorem integrable_skVectorCavityGibbs {Ω R α : Type*} [MeasurableSpace Ω] [Fintype R]
    [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {D : Type*} [Fintype D] (ξ : α → D → ℝ) (hξ : ∀ u, Measurable (fun a => ξ a u))
    {r : ℝ} (hr : 0 ≤ r) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r)
    (N : ℕ) (β : ℝ) (ρ q : D → D → ℝ)
    {P : Measure Ω} [IsFiniteMeasure P]
    (g : FinPairs N → Ω → ℝ) (g' : Fin N → Ω → ℝ) (Y : D → Ω → ℝ)
    (hgm : ∀ p, Measurable (g p)) (hg'm : ∀ i, Measurable (g' i)) (hYm : ∀ u, Measurable (Y u))
    (t : ℝ) (G : (R → Fin (N + 1) → α) → ℝ) (hG : Measurable G)
    {M : ℝ} (hGb : ∀ σ, |G σ| ≤ M) :
    Integrable (fun ω => ∫ σ, G σ ∂(Measure.pi fun _ : R =>
      (Measure.pi fun _ : Fin (N + 1) => μ).tilted (skVectorCavityEnergy ξ N β ρ q
        (fun p => g p ω) (fun i => g' i ω) (fun u => Y u ω) t))) P :=
  integrable_integral_pi_tilted (μ := Measure.pi fun _ : Fin (N + 1) => μ)
    (measurable_skVectorCavityEnergy_joint ξ hξ N β ρ q hgm hg'm hYm t)
    (fun _ => isProbabilityMeasure_tilted_skVectorCavityEnergy μ ξ hξ hr hbound N β ρ q _ _ _ t)
    hG hGb

/-! ### S6. Disorder average equality (Milestone A1) -/

/-- **Equality of cavity expectation functions (Milestone A1)**: for one-component spins,
the disorder expectation of the vector cavity Gibbs average equals the scalar cavity path
integral on `[0, 1]`. -/
theorem skVectorCavityAverage_ising_eq (N n : ℕ) (β q h t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    (∫ ω : (FinPairs N → ℝ) × ((Fin N → ℝ) × ℝ),
        ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ ∂(Measure.pi fun _ : Fin n =>
          (Measure.pi fun _ : Fin (N + 1) =>
            Measure.count.tilted (fun ε : ℤˣ => h * ((ε : ℤ) : ℝ))).tilted
              (skVectorCavityEnergy ξ₁ N β (fun _ _ => 1) (fun _ _ => q)
                (fun p => ω.1 p) (fun i => ω.2.1 i) (fun _ => β * Real.sqrt q * ω.2.2) t))
        ∂((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
          ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)))) =
      ∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
            (E (Real.arccos (Real.sqrt t)) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  intro B E
  have h_gibbs : ∀ ω : (FinPairs N → ℝ) × (Fin N → ℝ) × ℝ,
      (∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ ∂(Measure.pi fun _ : Fin n =>
        (Measure.pi fun _ : Fin (N + 1) =>
          Measure.count.tilted (fun ε : ℤˣ => h * ((ε : ℤ) : ℝ))).tilted
            (skVectorCavityEnergy ξ₁ N β (fun _ _ => 1) (fun _ _ => q)
              (fun p => ω.1 p) (fun i => ω.2.1 i) (fun _ => β * Real.sqrt q * ω.2.2) t))) =
      ∫ σ, f σ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        (E (Real.arccos (Real.sqrt t)) ω.1 ω.2)) :=
    fun ω => skVectorCavityGibbs_ising_eq N β q h t ht0 ht1 ω.1 ω.2 f
  have hYm : ∀ u : Fin 1, Measurable (fun ω : (FinPairs N → ℝ) × (Fin N → ℝ) × ℝ =>
      β * Real.sqrt q * ω.2.2) :=
    fun _ => measurable_const.mul (measurable_snd.comp measurable_snd)
  have h_int_vec : Integrable (fun ω : (FinPairs N → ℝ) × (Fin N → ℝ) × ℝ =>
      ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ ∂(Measure.pi fun _ : Fin n =>
        (Measure.pi fun _ : Fin (N + 1) =>
          Measure.count.tilted (fun ε : ℤˣ => h * ((ε : ℤ) : ℝ))).tilted
            (skVectorCavityEnergy ξ₁ N β (fun _ _ => 1) (fun _ _ => q)
              (fun p => ω.1 p) (fun i => ω.2.1 i) (fun _ => β * Real.sqrt q * ω.2.2) t)))
      ((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
        ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) :=
    integrable_skVectorCavityGibbs
      (μ := Measure.count.tilted (fun ε : ℤˣ => h * ((ε : ℤ) : ℝ)))
      ξ₁ (fun u => measurable_of_finite _) zero_le_one
      (fun a => ising_spin_sq_sum_le_one a) N β (fun _ _ => 1) (fun _ _ => q)
      (P := (Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
        ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1)))
      (fun p ω => ω.1 p) (fun i ω => ω.2.1 i) (fun _ ω => β * Real.sqrt q * ω.2.2)
      (fun p => (measurable_pi_apply p).comp measurable_fst)
      (fun i => ((measurable_pi_apply i).comp measurable_fst).comp measurable_snd)
      hYm
      t f (measurable_of_finite _) (M := ∑ σ, |f σ|)
      (fun σ => Finset.single_le_sum (f := fun x => |f x|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ σ))
  have h_int_scal : Integrable (fun ω : (FinPairs N → ℝ) × (Fin N → ℝ) × ℝ =>
      ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
        (E (Real.arccos (Real.sqrt t)) ω.1 ω.2)))
      ((Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
        ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))) :=
    h_int_vec.congr (ae_of_all _ h_gibbs)
  rw [integral_congr_ae (ae_of_all _ h_gibbs)]
  exact MeasureTheory.integral_prod (fun ω => ∫ σ, f σ ∂(Measure.pi fun _ : Fin n =>
    Measure.count.tilted (E (Real.arccos (Real.sqrt t)) ω.1 ω.2))) h_int_scal

/-! ### S7. Derivative transfer (Milestones A2 and A3) -/

/-- **Milestone A2: Scalar cavity path derivative transferred from the vector engine.** -/
theorem hasDerivAt_ising_cavity_path_of_vector (N n : ℕ) (β q h t : ℝ)
    (hq0 : 0 ≤ q) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    let P : Measure ((FinPairs N → ℝ) × (Fin N → ℝ) × ℝ) :=
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
        ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
    let μ_h : Measure ℤˣ := Measure.count.tilted (fun ε : ℤˣ => h * ((ε : ℤ) : ℝ))
    HasDerivAt (fun u =>
      ∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
            (E (Real.arccos (Real.sqrt u)) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))
      (β ^ 2 / 2 * ∑ a : Fin n, ∑ b : Fin n, ∑ u : Fin 1, ∑ v : Fin 1,
          skVectorCavityAverage μ_h ξ₁ N β (fun _ _ => 1) (fun _ _ => q) P
            (fun p ω => ω.1 p) (fun i ω => ω.2.1 i) (fun _ ω => β * Real.sqrt q * ω.2.2) t (fun σ =>
            f (fun c => σ (some (some c))) * ξ₁ (σ (some (some a)) (Fin.last N)) u *
              ξ₁ (σ (some (some b)) (Fin.last N)) v *
              (skVectorCavityOverlap ξ₁ N (σ (some (some a))) (σ (some (some b))) u v -
                if a = b then 1 else q)) -
        (n : ℝ) * β ^ 2 * ∑ a : Fin n, ∑ u : Fin 1, ∑ v : Fin 1,
          skVectorCavityAverage μ_h ξ₁ N β (fun _ _ => 1) (fun _ _ => q) P
            (fun p ω => ω.1 p) (fun i ω => ω.2.1 i) (fun _ ω => β * Real.sqrt q * ω.2.2) t (fun σ =>
            f (fun c => σ (some (some c))) * ξ₁ (σ (some (some a)) (Fin.last N)) u *
              ξ₁ (σ (some none) (Fin.last N)) v *
              (skVectorCavityOverlap ξ₁ N (σ (some (some a))) (σ (some none)) u v - q)) -
        (n : ℝ) * (β ^ 2 / 2) * ∑ u : Fin 1, ∑ v : Fin 1,
          skVectorCavityAverage μ_h ξ₁ N β (fun _ _ => 1) (fun _ _ => q) P
            (fun p ω => ω.1 p) (fun i ω => ω.2.1 i) (fun _ ω => β * Real.sqrt q * ω.2.2) t (fun σ =>
            f (fun c => σ (some (some c))) * ξ₁ (σ (some none) (Fin.last N)) u *
              ξ₁ (σ (some none) (Fin.last N)) v *
              (skVectorCavityOverlap ξ₁ N (σ (some none)) (σ (some none)) u v - 1)) +
        (n : ℝ) * ((n : ℝ) + 1) / 2 * β ^ 2 * ∑ u : Fin 1, ∑ v : Fin 1,
          skVectorCavityAverage μ_h ξ₁ N β (fun _ _ => 1) (fun _ _ => q) P
            (fun p ω => ω.1 p) (fun i ω => ω.2.1 i) (fun _ ω => β * Real.sqrt q * ω.2.2) t (fun σ =>
            f (fun c => σ (some (some c))) * ξ₁ (σ (some none) (Fin.last N)) u *
              ξ₁ (σ none (Fin.last N)) v *
              (skVectorCavityOverlap ξ₁ N (σ (some none)) (σ none) u v - q))) t := by
  intro B E P μ_h
  have hG := skVectorCavityGaussianData_disorderLaw_ising N β q hq0
  have hM0 : 0 ≤ ∑ σ, |f σ| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hd_vec := hasDerivAt_skVectorCavityAverage μ_h ξ₁
    (fun u => measurable_of_finite _) zero_le_one
    (fun a => ising_spin_sq_sum_le_one a) N β (fun _ _ => 1) (fun _ _ => q)
    (fun _ _ => rfl) f (measurable_of_finite _) hM0
    (fun σ => Finset.single_le_sum (f := fun x => |f x|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ σ))
    hG.hasGaussianLaw hG.measurable_old_coupling hG.measurable_new_coupling hG.measurable_field
    hG.integral_coupling_mul_coupling hG.integral_field_mul_field hG.integral_coupling_mul_field
    hG.integral_old_coupling hG.integral_new_coupling hG.integral_field ht.1 ht.2
  have heq : (fun u =>
      ∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
            (E (Real.arccos (Real.sqrt u)) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) =ᶠ[𝓝 t]
      (fun s => ∫ ω, ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ ∂(Measure.pi fun _ : Fin n =>
        (Measure.pi fun _ : Fin (N + 1) => μ_h).tilted (skVectorCavityEnergy ξ₁ N β
          (fun _ _ => 1) (fun _ _ => q) (fun p => ω.1 p) (fun i => ω.2.1 i)
          (fun _ => β * Real.sqrt q * ω.2.2) s)) ∂P) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact (skVectorCavityAverage_ising_eq N n β q h u hu.1.le hu.2.le f).symm
  have hd := hd_vec.congr_of_eventuallyEq heq
  simpa only [Fintype.card_fin] using hd

/-- **Milestone A3: The vector derivative value equals the scalar derivative value.** -/
theorem ising_cavity_path_deriv_eq_scalar (N n : ℕ) (β q h t : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
    let B : (FinPairs N → ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun g' a =>
      (Real.sqrt (N + 1))⁻¹ * β *
          (∑ p : FinPairs N,
            g' p * (a p.val.1.castSucc : ℝ) * (a p.val.2.castSucc : ℝ)) +
        h * ∑ i : Fin (N + 1), (a i : ℝ)
    let E : ℝ → (FinPairs N → ℝ) → ((Fin N → ℝ) × ℝ) → (Fin (N + 1) → ℤˣ) → ℝ := fun s g' ω a =>
      Real.cos s * ((Real.sqrt (N + 1))⁻¹ * β *
        (a (Fin.last N) : ℝ) * ∑ i : Fin N, ω.1 i * (a i.castSucc : ℝ)) +
      Real.sin s * (β * (a (Fin.last N) : ℝ) * ω.2 * Real.sqrt q) + B g' a
    let K : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N =>
            (b i.castSucc : ℝ)) - q)
    let P : Measure ((FinPairs N → ℝ) × (Fin N → ℝ) × ℝ) :=
      (Measure.pi fun _ : FinPairs N => gaussianReal 0 1).prod
        ((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
    let μ_h : Measure ℤˣ := Measure.count.tilted (fun ε : ℤˣ => h * ((ε : ℤ) : ℝ))
    (β ^ 2 / 2 * ∑ a : Fin n, ∑ b : Fin n, ∑ u : Fin 1, ∑ v : Fin 1,
        skVectorCavityAverage μ_h ξ₁ N β (fun _ _ => 1) (fun _ _ => q) P
          (fun p ω => ω.1 p) (fun i ω => ω.2.1 i) (fun _ ω => β * Real.sqrt q * ω.2.2) t (fun σ =>
          f (fun c => σ (some (some c))) * ξ₁ (σ (some (some a)) (Fin.last N)) u *
            ξ₁ (σ (some (some b)) (Fin.last N)) v *
            (skVectorCavityOverlap ξ₁ N (σ (some (some a))) (σ (some (some b))) u v -
              if a = b then 1 else q)) -
      (n : ℝ) * β ^ 2 * ∑ a : Fin n, ∑ u : Fin 1, ∑ v : Fin 1,
        skVectorCavityAverage μ_h ξ₁ N β (fun _ _ => 1) (fun _ _ => q) P
          (fun p ω => ω.1 p) (fun i ω => ω.2.1 i) (fun _ ω => β * Real.sqrt q * ω.2.2) t (fun σ =>
          f (fun c => σ (some (some c))) * ξ₁ (σ (some (some a)) (Fin.last N)) u *
            ξ₁ (σ (some none) (Fin.last N)) v *
            (skVectorCavityOverlap ξ₁ N (σ (some (some a))) (σ (some none)) u v - q)) -
      (n : ℝ) * (β ^ 2 / 2) * ∑ u : Fin 1, ∑ v : Fin 1,
        skVectorCavityAverage μ_h ξ₁ N β (fun _ _ => 1) (fun _ _ => q) P
          (fun p ω => ω.1 p) (fun i ω => ω.2.1 i) (fun _ ω => β * Real.sqrt q * ω.2.2) t (fun σ =>
          f (fun c => σ (some (some c))) * ξ₁ (σ (some none) (Fin.last N)) u *
            ξ₁ (σ (some none) (Fin.last N)) v *
            (skVectorCavityOverlap ξ₁ N (σ (some none)) (σ (some none)) u v - 1)) +
      (n : ℝ) * ((n : ℝ) + 1) / 2 * β ^ 2 * ∑ u : Fin 1, ∑ v : Fin 1,
        skVectorCavityAverage μ_h ξ₁ N β (fun _ _ => 1) (fun _ _ => q) P
          (fun p ω => ω.1 p) (fun i ω => ω.2.1 i) (fun _ ω => β * Real.sqrt q * ω.2.2) t (fun σ =>
          f (fun c => σ (some (some c))) * ξ₁ (σ (some none) (Fin.last N)) u *
            ξ₁ (σ none (Fin.last N)) v *
            (skVectorCavityOverlap ξ₁ N (σ (some none)) (σ none) u v - q))) =
      ∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f (fun r => τ (some (some r))) *
            ((∑ p : Fin n × Fin n with p.1 < p.2,
                K (τ (some (some p.1))) (τ (some (some p.2)))) -
              (n : ℝ) * ∑ r : Fin n, K (τ (some (some r))) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (Real.arccos (Real.sqrt t)) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1) := by
  intro B E K P μ_h
  have hd_vec := hasDerivAt_ising_cavity_path_of_vector N n β q h t hq0 ht f
  have hd_scal := hasDerivAt_integral_sk_cavity_path_square N n β q h t ⟨hq0, hq1⟩ ht f
  exact hd_vec.unique hd_scal

/-! ### S8/S9. Integrand specialization (Milestone B) -/

/-- **Talagrand's Eq. (1.151) derived from the vector cavity derivative.**
By specializing Proposition 1.12.4 to one-component spins (`d = 1`), `ξ₁ ε = ε`, `ρ = 1`,
and tilted measure `μ_h = count.tilted (h · ε)`, the vector cavity path derivative
coincides with the scalar SK cavity derivative. -/
theorem hasDerivAt_integral_sk_cavity_path_square_of_vector (N n : ℕ) (β q h t : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (f : (Fin n → Fin (N + 1) → ℤˣ) → ℝ) :
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
    let K : (Fin (N + 1) → ℤˣ) → (Fin (N + 1) → ℤˣ) → ℝ := fun a b =>
      β ^ 2 * (a (Fin.last N) : ℝ) * (b (Fin.last N) : ℝ) *
        ((N + 1 : ℝ)⁻¹ *
          ((fun i : Fin N => (a i.castSucc : ℝ)) ⬝ᵥ fun i : Fin N =>
            (b i.castSucc : ℝ)) - q)
    HasDerivAt (fun u =>
      ∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ σ : Fin n → Fin (N + 1) → ℤˣ, f σ
          ∂(Measure.pi fun _ : Fin n => Measure.count.tilted
            (E (Real.arccos (Real.sqrt u)) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1))
      (∫ g', ∫ ω : (Fin N → ℝ) × ℝ,
        ∫ τ : Option (Option (Fin n)) → Fin (N + 1) → ℤˣ,
          f (fun r => τ (some (some r))) *
            ((∑ p : Fin n × Fin n with p.1 < p.2,
                K (τ (some (some p.1))) (τ (some (some p.2)))) -
              (n : ℝ) * ∑ r : Fin n, K (τ (some (some r))) (τ (some none)) +
              (n : ℝ) * ((n : ℝ) + 1) / 2 * K (τ (some none)) (τ none))
        ∂(Measure.pi fun _ : Option (Option (Fin n)) => Measure.count.tilted
          (E (Real.arccos (Real.sqrt t)) g' ω))
        ∂((Measure.pi fun _ : Fin N => gaussianReal 0 1).prod (gaussianReal 0 1))
      ∂(Measure.pi fun _ : FinPairs N => gaussianReal 0 1)) t := by
  intro B E K
  have hd := hasDerivAt_ising_cavity_path_of_vector N n β q h t hq.1 ht f
  have heq := ising_cavity_path_deriv_eq_scalar N n β q h t hq.1 hq.2 ht f
  exact heq ▸ hd

end SpinGlasses
