/-
Copyright (c) 2026 LML Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LML Contributors
-/
module

public import LeanMachineLearning.SpinGlasses.Talagrand.VectorSpins.Cavity.Comparison
public import LeanMachineLearning.ForMathlib.Probability.GibbsProductSplit

/-!
# The decoupled system at `t = 0` (Talagrand, proof of Theorem 1.12.1)

At `t = 0` the cavity Hamiltonian (1.375) splits as `E_old(σ₁, …, σ_N) + E_new(σ_{N+1})`: the last
spin only sees the Gaussian field `Y` and the compensation.  Its Gibbs measure is therefore the
product of the Gibbs measures of the two parts, and Eq. (1.372) gives
`ν₀((ε¹ᵤ ε²ᵥ - qᵤᵥ) h) = 0` for every function `h` of the first `N` sites of the replicas.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators
namespace SpinGlasses

variable {α D : Type*} [MeasurableSpace α] [Fintype D]

/-- The part of the cavity Hamiltonian (1.375) that involves only the first `N` spins
(the old couplings). -/
noncomputable def skVectorOldEnergy (ξ : α → D → ℝ) (N : ℕ) (β : ℝ) (g : FinPairs N → ℝ)
    (τ : Fin N → α) : ℝ :=
  (Real.sqrt (N + 1))⁻¹ * β * ∑ p : FinPairs N, g p *
      ∑ u, ξ (τ p.val.1) u * ξ (τ p.val.2) u

omit [MeasurableSpace α] in
/-- At `t = 0` the cavity Hamiltonian is the old energy plus the energy of the decoupled last
spin. -/
theorem skVectorCavityEnergy_zero (ξ : α → D → ℝ) (N : ℕ) (β : ℝ) (ρ q : D → D → ℝ)
    (g : FinPairs N → ℝ) (g' : Fin N → ℝ) (Y : D → ℝ) (σ : Fin (N + 1) → α) :
    skVectorCavityEnergy ξ N β ρ q g g' Y 0 σ =
      skVectorOldEnergy ξ N β g (fun j => σ j.castSucc) +
        skVectorFieldExponent ξ β ρ q Y (σ (Fin.last N)) := by
  unfold skVectorCavityEnergy skVectorOldEnergy skVectorFieldExponent
  simp only [Real.sqrt_zero, zero_mul, zero_add, sub_zero, Real.sqrt_one, one_mul]
  have h : ∑ u, ξ (σ (Fin.last N)) u * Y u = ∑ u, Y u * ξ (σ (Fin.last N)) u :=
    Finset.sum_congr rfl fun u _ => mul_comm _ _
  rw [h]
  ring

section Bounds

variable {r : ℝ} (ξ : α → D → ℝ) (hr : 0 ≤ r) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ r)
include hr hbound

omit [MeasurableSpace α] in
/-- A uniform bound for the old energy, for fixed couplings. -/
theorem abs_skVectorOldEnergy_le (N : ℕ) (β : ℝ) (g : FinPairs N → ℝ)
    (τ : Fin N → α) :
    |skVectorOldEnergy ξ N β g τ| ≤ |β| * ∑ p : FinPairs N, |g p| * (Fintype.card D * r) := by
  have hc : |(Real.sqrt ((N : ℝ) + 1))⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
    exact inv_le_one_of_one_le₀
      (Real.one_le_sqrt.2 (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]))
  unfold skVectorOldEnergy
  rw [abs_mul, abs_mul]
  calc |(Real.sqrt ((N : ℝ) + 1))⁻¹| * |β| * |∑ p : FinPairs N, g p *
        ∑ u, ξ (τ p.val.1) u * ξ (τ p.val.2) u|
      ≤ 1 * |β| * ∑ p : FinPairs N, |g p| * (Fintype.card D * r) := by
        refine mul_le_mul (mul_le_mul hc le_rfl (abs_nonneg _) zero_le_one) ?_ (abs_nonneg _)
          (by positivity)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ u, |ξ (τ p.val.1) u * ξ (τ p.val.2) u| ≤ ∑ _u : D, r :=
              Finset.sum_le_sum fun u _ => abs_spin_mul_le ξ hr hbound _ _ u u
          _ = Fintype.card D * r := by simp
    _ = _ := by ring

omit [MeasurableSpace α] in
/-- A uniform bound for the energy of the decoupled last spin. -/
theorem abs_skVectorFieldExponent_le (β : ℝ) (ρ q : D → D → ℝ) (y : D → ℝ)
    (a : α) : |skVectorFieldExponent ξ β ρ q y a| ≤
      ∑ u, |y u| * Real.sqrt r + β ^ 2 / 2 * ∑ u, ∑ v, r * |ρ u v - q u v| := by
  have hξb : ∀ a u, |ξ a u| ≤ Real.sqrt r := abs_spin_le ξ hbound
  unfold skVectorFieldExponent
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hξb a u) (abs_nonneg _)
  · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ β ^ 2 / 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_spin_mul_le ξ hr hbound a a u v) (abs_nonneg _)

end Bounds

/-- **Decoupling at `t = 0`, abstract form.**  If `Y` is independent of the old couplings and the
two-replica observable `Ψ₂` of the last spin has zero average against the Gibbs measure of the
field `Y`, then `ν₀(Ψ(old sites) Ψ₂(last site)) = 0`. -/
theorem skVectorCavityAverage_zero_centered_mul_eq_zero {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    (ρ q : Fin d → Fin d → ℝ) {P : Measure Ω}
    {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : Fin d → Ω → ℝ}
    (hgm : ∀ p, Measurable (g p)) (hYm : ∀ u, Measurable (Y u))
    (hind : IndepFun (fun ω p => g p ω) (fun ω u => Y u ω) P)
    (Ψ : (Fin 2 → Fin N → α) → ℝ) (hΨ : Measurable Ψ) (Ψ₂ : (Fin 2 → α) → ℝ)
    (hΨ₂m : Measurable Ψ₂)
    (hzero : ∫ ω, ∫ a, Ψ₂ a ∂(Measure.pi fun _ : Fin 2 =>
      μ.tilted (skVectorFieldExponent ξ β ρ q (fun w => Y w ω))) ∂P = 0) :
    ∫ ω, ∫ σ : Fin 2 → Fin (N + 1) → α, Ψ (fun i j => σ i j.castSucc) *
        Ψ₂ (fun i => σ i (Fin.last N))
        ∂(Measure.pi fun _ : Fin 2 => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
          (skVectorCavityEnergy ξ N β ρ q (fun p => g p ω) (fun i => g' i ω)
            (fun w => Y w ω) 0)) ∂P = 0 := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set A : (FinPairs N → ℝ) → ℝ := fun x => ∫ τ, Ψ τ ∂(Measure.pi fun _ : Fin 2 =>
    (Measure.pi fun _ : Fin N => μ).tilted (skVectorOldEnergy ξ N β x)) with hA
  set B : (Fin d → ℝ) → ℝ := fun y => ∫ a, Ψ₂ a ∂(Measure.pi fun _ : Fin 2 =>
    μ.tilted (skVectorFieldExponent ξ β ρ q y)) with hB
  have hE₁m : ∀ x, Measurable (skVectorOldEnergy ξ N β x) := fun x => by
    unfold skVectorOldEnergy
    refine measurable_const.mul (Finset.measurable_sum _ fun p _ => measurable_const.mul
      (Finset.measurable_sum _ fun w _ => ?_))
    exact ((hξ w).comp (measurable_pi_apply _)).mul ((hξ w).comp (measurable_pi_apply _))
  have hE₂m : ∀ y, Measurable (skVectorFieldExponent ξ β ρ q y) := fun y => by
    unfold skVectorFieldExponent
    exact (Finset.measurable_sum _ fun w _ => measurable_const.mul (hξ w)).add
      (measurable_const.mul (Finset.measurable_sum _ fun w _ => Finset.measurable_sum _
        fun w' _ => ((hξ w).mul (hξ w')).mul measurable_const))
  -- step 1: the inner integral factorizes at every `ω`
  have hstep : ∀ ω, ∫ σ : Fin 2 → Fin (N + 1) → α, Ψ (fun i j => σ i j.castSucc) *
        Ψ₂ (fun i => σ i (Fin.last N))
        ∂(Measure.pi fun _ : Fin 2 => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
          (skVectorCavityEnergy ξ N β ρ q (fun p => g p ω) (fun i => g' i ω)
            (fun w => Y w ω) 0)) = A (fun p => g p ω) * B (fun w => Y w ω) := by
    intro ω
    have hfun : skVectorCavityEnergy ξ N β ρ q (fun p => g p ω) (fun i => g' i ω)
        (fun w => Y w ω) 0 = fun σ => skVectorOldEnergy ξ N β (fun p => g p ω)
          (fun j => σ j.castSucc) +
          skVectorFieldExponent ξ β ρ q (fun w => Y w ω) (σ (Fin.last N)) :=
      funext fun σ => skVectorCavityEnergy_zero ξ N β ρ q _ _ _ σ
    rw [hfun]
    exact integral_pi_tilted_split μ (skVectorOldEnergy ξ N β (fun p => g p ω))
      (skVectorFieldExponent ξ β ρ q (fun w => Y w ω)) (hE₁m _) (hE₂m _)
      (abs_skVectorOldEnergy_le ξ hr hbound N β _)
      (abs_skVectorFieldExponent_le ξ hr hbound β ρ q _)
      Ψ Ψ₂ hΨ hΨ₂m
  -- step 2: measurability of `A` and `B`
  have hEj₁ : Measurable fun p : (FinPairs N → ℝ) × (Fin N → α) =>
      skVectorOldEnergy ξ N β p.1 p.2 := by
    unfold skVectorOldEnergy
    refine measurable_const.mul (Finset.measurable_sum _ fun p _ => ?_)
    refine ((measurable_pi_apply p).comp measurable_fst).mul (Finset.measurable_sum _ fun w _ => ?_)
    exact ((hξ w).comp ((measurable_pi_apply _).comp measurable_snd)).mul
      ((hξ w).comp ((measurable_pi_apply _).comp measurable_snd))
  have hEj₂ : Measurable fun p : (Fin d → ℝ) × α => skVectorFieldExponent ξ β ρ q p.1 p.2 := by
    unfold skVectorFieldExponent
    exact (Finset.measurable_sum _ fun w _ => ((measurable_pi_apply w).comp measurable_fst).mul
      ((hξ w).comp measurable_snd)).add (measurable_const.mul (Finset.measurable_sum _
        fun w _ => Finset.measurable_sum _ fun w' _ =>
          (((hξ w).comp measurable_snd).mul ((hξ w').comp measurable_snd)).mul measurable_const))
  have hAm : Measurable A := measurable_integral_pi_tilted
    (μ := Measure.pi fun _ : Fin N => μ) (ι := Fin 2)
    (E := fun x τ => skVectorOldEnergy ξ N β x τ) hEj₁ hΨ
  have hBm : Measurable B := measurable_integral_pi_tilted (μ := μ) (ι := Fin 2)
    (E := fun y a => skVectorFieldExponent ξ β ρ q y a) hEj₂ hΨ₂m
  -- step 3: independence of the old couplings and the field
  have hGm : Measurable fun ω p => g p ω := measurable_pi_iff.2 hgm
  have hHm : Measurable fun ω u => Y u ω := measurable_pi_iff.2 hYm
  rw [integral_congr_ae (Filter.Eventually.of_forall hstep)]
  rw [hind.integral_fun_comp_mul_comp hGm.aemeasurable hHm.aemeasurable
    hAm.aestronglyMeasurable hBm.aestronglyMeasurable]
  rw [show ∫ ω, B (fun w => Y w ω) ∂P = 0 from hzero, mul_zero]

/-- **Decoupling at `t = 0`** (Eq. (1.372)): with `Y` independent of the old couplings,
`ν₀((ε¹ᵤ ε²ᵥ - qᵤᵥ) h) = 0` for every bounded measurable function `h` of the first `N`
sites of the two replicas. -/
theorem skVectorCavityAverage_zero_pair_mul_eq_zero {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    (ρ q : Fin d → Fin d → ℝ) {P : Measure Ω} [IsProbabilityMeasure P]
    {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : Fin d → Ω → ℝ}
    (hgm : ∀ p, Measurable (g p)) (hYm : ∀ u, Measurable (Y u))
    (hind : IndepFun (fun ω p => g p ω) (fun ω u => Y u ω) P)
    (hq : ∀ u v, q u v = ∫ ω, skVectorGibbs μ (skVectorFieldExponent ξ β ρ q (fun w => Y w ω))
      (fun a => ξ a u) * skVectorGibbs μ (skVectorFieldExponent ξ β ρ q (fun w => Y w ω))
      (fun a => ξ a v) ∂P)
    (Ψ : (Fin 2 → Fin N → α) → ℝ) (hΨ : Measurable Ψ) (u v : Fin d) :
    ∫ ω, ∫ σ : Fin 2 → Fin (N + 1) → α, Ψ (fun i j => σ i j.castSucc) *
        (ξ (σ 0 (Fin.last N)) u * ξ (σ 1 (Fin.last N)) v - q u v)
        ∂(Measure.pi fun _ : Fin 2 => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
          (skVectorCavityEnergy ξ N β ρ q (fun p => g p ω) (fun i => g' i ω)
            (fun w => Y w ω) 0)) ∂P = 0 := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set Ψ₂ : (Fin 2 → α) → ℝ := fun a => ξ (a 0) u * ξ (a 1) v - q u v with hΨ₂
  have hΨ₂m : Measurable Ψ₂ :=
    (((hξ u).comp (measurable_pi_apply 0)).mul ((hξ v).comp (measurable_pi_apply 1))).sub
      measurable_const
  set B : (Fin d → ℝ) → ℝ := fun y => ∫ a, Ψ₂ a ∂(Measure.pi fun _ : Fin 2 =>
    μ.tilted (skVectorFieldExponent ξ β ρ q y)) with hB
  have hEj₂ : Measurable fun p : (Fin d → ℝ) × α => skVectorFieldExponent ξ β ρ q p.1 p.2 := by
    unfold skVectorFieldExponent
    exact (Finset.measurable_sum _ fun w _ => ((measurable_pi_apply w).comp measurable_fst).mul
      ((hξ w).comp measurable_snd)).add (measurable_const.mul (Finset.measurable_sum _
        fun w _ => Finset.measurable_sum _ fun w' _ =>
          (((hξ w).comp measurable_snd).mul ((hξ w').comp measurable_snd)).mul measurable_const))
  have hHm : Measurable fun ω u => Y u ω := measurable_pi_iff.2 hYm
  -- step 4: the field average vanishes by Eq. (1.372)
  have hBy : ∀ y, B y = skVectorGibbs μ (skVectorFieldExponent ξ β ρ q y) (fun a => ξ a u) *
      skVectorGibbs μ (skVectorFieldExponent ξ β ρ q y) (fun a => ξ a v) - q u v := by
    intro y
    have hexpi := integrable_exp_skVectorFieldExponent μ ξ hξ hr hbound β ρ q y
    have : IsProbabilityMeasure (μ.tilted (skVectorFieldExponent ξ β ρ q y)) :=
      isProbabilityMeasure_tilted hexpi
    have hξu := abs_spin_mul_le ξ hr hbound
    have hint : ∀ w, Integrable (fun a => ξ a w) (μ.tilted (skVectorFieldExponent ξ β ρ q y)) :=
      fun w => integrable_of_measurable_bound (hξ w) (M := Real.sqrt d) fun a => by
        refine Real.abs_le_sqrt ?_
        exact (Finset.single_le_sum (f := fun u => ξ a u ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ w)).trans (hbound a)
    have hprod : ∫ a : Fin 2 → α, ξ (a 0) u * ξ (a 1) v ∂(Measure.pi fun _ : Fin 2 =>
        μ.tilted (skVectorFieldExponent ξ β ρ q y)) =
        (∫ a, ξ a u ∂(μ.tilted (skVectorFieldExponent ξ β ρ q y))) *
          ∫ a, ξ a v ∂(μ.tilted (skVectorFieldExponent ξ β ρ q y)) := by
      have := integral_fintype_prod_eq_prod (ι := Fin 2) (E := fun _ => α)
        (fun i => ![fun a => ξ a u, fun a => ξ a v] i)
        (μ := fun _ => μ.tilted (skVectorFieldExponent ξ β ρ q y))
      simpa [Fin.prod_univ_two] using this
    have hΨ₂i : Integrable (fun a : Fin 2 → α => ξ (a 0) u * ξ (a 1) v)
        (Measure.pi fun _ : Fin 2 => μ.tilted (skVectorFieldExponent ξ β ρ q y)) :=
      integrable_of_measurable_bound (((hξ u).comp (measurable_pi_apply 0)).mul
        ((hξ v).comp (measurable_pi_apply 1))) (M := d) fun a => by
          simpa [Real.norm_eq_abs] using abs_spin_mul_le ξ hr hbound (a 0) (a 1) u v
    simp only [hB, hΨ₂]
    rw [integral_sub hΨ₂i (integrable_const _), hprod, integral_const]
    simp [skVectorGibbs_eq_integral_tilted]
  have hGm' : ∀ w, Measurable fun ω => skVectorGibbs μ
      (skVectorFieldExponent ξ β ρ q (fun w' => Y w' ω)) (fun a => ξ a w) := fun w =>
    measurable_skVectorGibbs (e := fun ω a => skVectorFieldExponent ξ β ρ q (fun w' => Y w' ω) a)
      (hEj₂.comp ((hHm.comp measurable_fst).prodMk measurable_snd)) (hξ w)
  have hB0 : ∫ ω, B (fun w => Y w ω) ∂P = 0 := by
    simp_rw [hBy]
    have hi : Integrable (fun ω => skVectorGibbs μ
        (skVectorFieldExponent ξ β ρ q (fun w' => Y w' ω)) (fun a => ξ a u) *
        skVectorGibbs μ (skVectorFieldExponent ξ β ρ q (fun w' => Y w' ω))
        (fun a => ξ a v)) P := by
      refine integrable_of_measurable_bound ((hGm' u).mul (hGm' v)) (M := d) fun ω => ?_
      have hexpi := integrable_exp_skVectorFieldExponent μ ξ hξ hr hbound β ρ q (fun w' => Y w' ω)
      have hb : ∀ a w, |ξ a w| ≤ Real.sqrt d := abs_spin_le ξ hbound
      rw [abs_mul]
      calc _ ≤ Real.sqrt d * Real.sqrt d :=
            mul_le_mul (abs_skVectorGibbs_le hexpi fun a => hb a u)
              (abs_skVectorGibbs_le hexpi fun a => hb a v) (abs_nonneg _) (Real.sqrt_nonneg _)
        _ = d := Real.mul_self_sqrt hr
    rw [integral_sub hi (integrable_const _), ← hq u v]
    simp
  exact skVectorCavityAverage_zero_centered_mul_eq_zero μ ξ hξ hbound β ρ q hgm hYm hind Ψ hΨ Ψ₂
    hΨ₂m hB0

/-- **Decoupling at `t = 0` for the diagonal overlap** (Eq. (1.373)): with `Y` independent of the
old couplings, `ν₀((ε¹ᵤ ε¹ᵥ - ρᵤᵥ) h) = 0` for every bounded measurable function `h` of the first
`N` sites of the two replicas. -/
theorem skVectorCavityAverage_zero_diag_mul_eq_zero {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure α) [IsProbabilityMeasure μ] (ξ : α → Fin d → ℝ)
    (hξ : ∀ u, Measurable (fun a => ξ a u)) (hbound : ∀ a, ∑ u, ξ a u ^ 2 ≤ d) (β : ℝ)
    (ρ q : Fin d → Fin d → ℝ) {P : Measure Ω} [IsProbabilityMeasure P]
    {g : FinPairs N → Ω → ℝ} {g' : Fin N → Ω → ℝ} {Y : Fin d → Ω → ℝ}
    (hgm : ∀ p, Measurable (g p)) (hYm : ∀ u, Measurable (Y u))
    (hind : IndepFun (fun ω p => g p ω) (fun ω u => Y u ω) P)
    (hρ : ∀ u v, ρ u v = ∫ ω, skVectorGibbs μ
      (skVectorFieldExponent ξ β ρ q (fun w => Y w ω)) (fun a => ξ a u * ξ a v) ∂P)
    (Ψ : (Fin 2 → Fin N → α) → ℝ) (hΨ : Measurable Ψ) (u v : Fin d) :
    ∫ ω, ∫ σ : Fin 2 → Fin (N + 1) → α, Ψ (fun i j => σ i j.castSucc) *
        (ξ (σ 0 (Fin.last N)) u * ξ (σ 0 (Fin.last N)) v - ρ u v)
        ∂(Measure.pi fun _ : Fin 2 => (Measure.pi fun _ : Fin (N + 1) => μ).tilted
          (skVectorCavityEnergy ξ N β ρ q (fun p => g p ω) (fun i => g' i ω)
            (fun w => Y w ω) 0)) ∂P = 0 := by
  classical
  have hr : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hΨ₂m : Measurable fun a : Fin 2 → α => ξ (a 0) u * ξ (a 0) v - ρ u v :=
    (((hξ u).comp (measurable_pi_apply 0)).mul ((hξ v).comp (measurable_pi_apply 0))).sub
      measurable_const
  have hEj₂ : Measurable fun p : (Fin d → ℝ) × α => skVectorFieldExponent ξ β ρ q p.1 p.2 := by
    unfold skVectorFieldExponent
    exact (Finset.measurable_sum _ fun w _ => ((measurable_pi_apply w).comp measurable_fst).mul
      ((hξ w).comp measurable_snd)).add (measurable_const.mul (Finset.measurable_sum _
        fun w _ => Finset.measurable_sum _ fun w' _ =>
          (((hξ w).comp measurable_snd).mul ((hξ w').comp measurable_snd)).mul measurable_const))
  have hHm : Measurable fun ω u => Y u ω := measurable_pi_iff.2 hYm
  have hBy : ∀ y, ∫ a, (ξ (a 0) u * ξ (a 0) v - ρ u v) ∂(Measure.pi fun _ : Fin 2 =>
      μ.tilted (skVectorFieldExponent ξ β ρ q y)) =
      skVectorGibbs μ (skVectorFieldExponent ξ β ρ q y) (fun a => ξ a u * ξ a v) - ρ u v := by
    intro y
    have hexpi := integrable_exp_skVectorFieldExponent μ ξ hξ hr hbound β ρ q y
    have : IsProbabilityMeasure (μ.tilted (skVectorFieldExponent ξ β ρ q y)) :=
      isProbabilityMeasure_tilted hexpi
    have hmeas : AEStronglyMeasurable (fun a => ξ a u * ξ a v - ρ u v)
        (μ.tilted (skVectorFieldExponent ξ β ρ q y)) :=
      (((hξ u).mul (hξ v)).sub measurable_const).aestronglyMeasurable
    have hint : Integrable (fun a => ξ a u * ξ a v)
        (μ.tilted (skVectorFieldExponent ξ β ρ q y)) :=
      integrable_of_measurable_bound ((hξ u).mul (hξ v)) (M := d)
        fun a => abs_spin_mul_le ξ hr hbound a a u v
    rw [integral_pi_eval (μ.tilted (skVectorFieldExponent ξ β ρ q y)) (J := Fin 2) 0
      (fun a => ξ a u * ξ a v - ρ u v) hmeas, integral_sub hint (integrable_const _),
      ← skVectorGibbs_eq_integral_tilted]
    simp
  have hG : Measurable fun ω => skVectorGibbs μ
      (skVectorFieldExponent ξ β ρ q (fun w' => Y w' ω)) (fun a => ξ a u * ξ a v) :=
    measurable_skVectorGibbs (e := fun ω a => skVectorFieldExponent ξ β ρ q (fun w' => Y w' ω) a)
      (hEj₂.comp ((hHm.comp measurable_fst).prodMk measurable_snd)) ((hξ u).mul (hξ v))
  have hB0 : ∫ ω, ∫ a, (ξ (a 0) u * ξ (a 0) v - ρ u v) ∂(Measure.pi fun _ : Fin 2 =>
      μ.tilted (skVectorFieldExponent ξ β ρ q (fun w => Y w ω))) ∂P = 0 := by
    simp_rw [hBy]
    have hi : Integrable (fun ω => skVectorGibbs μ
        (skVectorFieldExponent ξ β ρ q (fun w' => Y w' ω)) (fun a => ξ a u * ξ a v)) P :=
      integrable_of_measurable_bound hG (M := d) fun ω =>
        abs_skVectorGibbs_le (integrable_exp_skVectorFieldExponent μ ξ hξ hr hbound β ρ q _)
          fun a => abs_spin_mul_le ξ hr hbound a a u v
    rw [integral_sub hi (integrable_const _), ← hρ u v]
    simp
  exact skVectorCavityAverage_zero_centered_mul_eq_zero μ ξ hξ hbound β ρ q hgm hYm hind Ψ hΨ
    (fun a => ξ (a 0) u * ξ (a 0) v - ρ u v) hΨ₂m hB0

end SpinGlasses
